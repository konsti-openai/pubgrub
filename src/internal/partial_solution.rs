// SPDX-License-Identifier: MPL-2.0

//! Package decisions and the derivations that constrain them.

use std::borrow::Cow;
use std::cmp::Reverse;
use std::collections::hash_map::Entry;
use std::fmt::{Debug, Display};
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;

use log::debug;
use priority_queue::PriorityQueue;
use rustc_hash::FxHasher;

use crate::internal::{Arena, HashArena, Id, IncompDpId, IncompId, Incompatibility, Relation};
use crate::{DependencyProvider, Map, Package, Term, VersionSet, term};

type FnvIndexSet<T> = indexmap::IndexSet<T, BuildHasherDefault<FxHasher>>;

/// The number of decisions that have been made at some point in solving.
///
/// The logical level is zero-based, but it is stored as `level + 1` in a
/// `NonZeroU32` so that `Option<DecisionLevel>` fits in the same 4 bytes as a
/// bare `u32`, with `None` occupying the all-zero niche.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub(crate) struct DecisionLevel(NonZeroU32);

impl DecisionLevel {
    /// Decision level zero: no decisions have been made yet.
    pub(crate) const ZERO: DecisionLevel = DecisionLevel(NonZeroU32::MIN);
    /// Sentinel greater than any decision level the solver can reach.
    pub(crate) const MAX: DecisionLevel = DecisionLevel(NonZeroU32::MAX);

    /// Build a `DecisionLevel` from its zero-based logical value.
    pub(crate) fn new(level: u32) -> Self {
        // `level + 1` is always >= 1; the only overflow would be `u32::MAX`
        // decisions, which the solver cannot reach.
        Self(NonZeroU32::new(level + 1).expect("decision level overflow"))
    }

    /// The zero-based logical decision level.
    pub(crate) fn get(self) -> u32 {
        self.0.get() - 1
    }

    /// Advances to the next decision level, panicking if the representation is exhausted.
    pub(crate) fn increment(self) -> Self {
        Self(self.0.checked_add(1).expect("decision level overflow"))
    }
}

impl Debug for DecisionLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DecisionLevel({})", self.get())
    }
}

// Preserve the niche so `Option<DecisionLevel>` stays as small as a bare `u32`.
const _: () = assert!(std::mem::size_of::<Option<DecisionLevel>>() == std::mem::size_of::<u32>());

/// The partial solution contains all package assignments,
/// organized by package and historically ordered.
#[derive(Clone, Debug)]
pub struct PartialSolution<DP: DependencyProvider> {
    next_global_index: u32,
    /// Current decisions and derivation histories, indexed by package.
    #[allow(clippy::type_complexity)]
    package_assignments: Map<Id<DP::P>, PackageAssignments<DP::P, DP::VS, DP::M>>,
    /// Packages in decision order; a backtrack truncates this list.
    decided_packages: Vec<Id<DP::P>>,
    /// The undecided packages order by their `Priority`.
    ///
    /// The max heap allows quickly `pop`ing the highest priority package.
    ///
    /// The `Reverse<u32>` is the discovery order of packages used as tiebreaker. Its order is that
    /// of a breadth-first search.
    #[allow(clippy::type_complexity)]
    prioritized_potential_packages:
        PriorityQueue<Id<DP::P>, (DP::Priority, Reverse<u32>), BuildHasherDefault<FxHasher>>,
    /// Packages whose derivations changed since the last time `prioritize` was called and need
    /// their priorities to be updated.
    outdated_priorities: FnvIndexSet<Id<DP::P>>,
    /// For each completed backtrack generation, the highest decision level that remains valid.
    /// The active generation is represented by the missing entry after the end of this vector.
    last_valid_decision_levels: Vec<DecisionLevel>,
}

/// The derivation history for a package and its optional selected version.
#[derive(Clone, Debug)]
struct PackageAssignments<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    /// The selected version, if a decision has been made.
    decision: Option<Decision<VS::V>>,
    /// All constraints on the package version from previous decisions, accumulated by decision
    /// level.
    dated_derivations: Vec<DatedDerivation<P, VS, M>>,
    /// Smallest [`DecisionLevel`] in `dated_derivations`.
    smallest_decision_level: DecisionLevel,
    /// Level of the latest assignment, including a decision when present.
    highest_decision_level: DecisionLevel,
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> Display
    for PackageAssignments<P, VS, M>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let derivations: Vec<_> = self
            .dated_derivations
            .iter()
            .map(|dd| dd.to_string())
            .collect();
        write!(
            f,
            "decision range: {:?}..{:?}\nderivations:\n  {}\n,decision: {:?}",
            self.smallest_decision_level,
            self.highest_decision_level,
            derivations.join("\n  "),
            self.decision
        )
    }
}

#[derive(Clone, Debug)]
struct DatedDerivation<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    global_index: u32,
    /// Only decisions up this level has been used to compute the accumulated term.
    decision_level: DecisionLevel,
    cause: IncompId<P, VS, M>,
    /// The intersection of all terms up to `decision_level`.
    ///
    /// It may not contain all terms of this `decision_level`, there may be more than one
    /// `DatedDerivation` per decision level.
    accumulated_intersection: Term<VS>,
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> Display
    for DatedDerivation<P, VS, M>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}, cause: {:?}", self.decision_level, self.cause)
    }
}

#[derive(Clone, Debug)]
struct Decision<V> {
    global_index: u32,
    version: V,
}

#[derive(Clone, Debug)]
pub(crate) enum SatisfierSearch<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    DifferentDecisionLevels {
        previous_satisfier_level: DecisionLevel,
    },
    SameDecisionLevels {
        satisfier_cause: IncompId<P, VS, M>,
        /// The union of the incompatibility and cause terms for the satisfier package.
        resolved_term: Term<VS>,
    },
}

struct Satisfier<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    cause: Option<IncompId<P, VS, M>>,
    global_index: u32,
    decision_level: DecisionLevel,
}

impl<DP: DependencyProvider> PartialSolution<DP> {
    /// Initialize an empty PartialSolution.
    pub(crate) fn empty() -> Self {
        Self {
            next_global_index: 0,
            package_assignments: Map::default(),
            decided_packages: Vec::new(),
            prioritized_potential_packages: PriorityQueue::default(),
            outdated_priorities: FnvIndexSet::default(),
            last_valid_decision_levels: vec![DecisionLevel::ZERO],
        }
    }

    pub(crate) fn is_contradicted(
        &self,
        incompatibility: &Incompatibility<DP::P, DP::VS, DP::M>,
    ) -> bool {
        incompatibility.is_contradicted(&self.last_valid_decision_levels)
    }

    pub(crate) fn mark_contradicted(
        &self,
        incompatibility: &mut Incompatibility<DP::P, DP::VS, DP::M>,
    ) {
        incompatibility.mark_contradicted(
            self.current_decision_level(),
            self.last_valid_decision_levels.len() as u32,
        );
    }

    /// Returns whether at least one backtrack generation has completed.
    pub(crate) fn has_backtracked(&self) -> bool {
        self.last_valid_decision_levels.len() > 1
    }

    pub(crate) fn display<'a>(&'a self, package_store: &'a HashArena<DP::P>) -> impl Display + 'a {
        struct PSDisplay<'a, DP: DependencyProvider>(&'a PartialSolution<DP>, &'a HashArena<DP::P>);

        impl<DP: DependencyProvider> Display for PSDisplay<'_, DP> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let mut assignments: Vec<_> = self
                    .0
                    .package_assignments
                    .iter()
                    .map(|(p, pa)| format!("{:?} = '{}': {}", p, self.1[*p], pa))
                    .collect();
                assignments.sort();
                write!(
                    f,
                    "next_global_index: {}\ncurrent_decision_level: {:?}\npackage_assignments:\n{}",
                    self.0.next_global_index,
                    self.0.current_decision_level(),
                    assignments.join("\t\n")
                )
            }
        }

        PSDisplay(self, package_store)
    }

    /// Add a decision.
    pub fn add_decision(&mut self, package: Id<DP::P>, version: DP::V) {
        let decision_level = self.current_decision_level().increment();
        let pa = self
            .package_assignments
            .get_mut(&package)
            .expect("Derivations must already exist");
        debug_assert!(pa.decision.is_none(), "Already existing decision");
        debug_assert!(
            pa.derivations().contains(&version),
            "{package:?}: {version} was expected to be contained in {}",
            pa.derivations(),
        );
        pa.highest_decision_level = decision_level;
        pa.decision = Some(Decision {
            global_index: self.next_global_index,
            version,
        });
        self.decided_packages.push(package);
        self.next_global_index += 1;
    }

    /// The list of package that have not been selected after the last prioritization.
    ///
    /// This list gets updated by [`Self::pick_highest_priority_pkg`] and cleared by backtracking.
    #[allow(clippy::type_complexity)]
    pub fn undecided_packages(
        &self,
    ) -> impl Iterator<
        Item = (
            &Id<DP::P>,
            &(<DP as DependencyProvider>::Priority, Reverse<u32>),
        ),
    > {
        self.prioritized_potential_packages.iter()
    }

    /// Add a derivation.
    pub(crate) fn add_derivation(
        &mut self,
        package: Id<DP::P>,
        cause: IncompDpId<DP>,
        store: &Arena<Incompatibility<DP::P, DP::VS, DP::M>>,
    ) {
        let term = store[cause].get(package).unwrap();
        let global_index = self.next_global_index;
        let decision_level = self.current_decision_level();
        self.next_global_index += 1;
        let dated_derivation = |accumulated_intersection| DatedDerivation {
            global_index,
            decision_level,
            cause,
            accumulated_intersection,
        };
        match self.package_assignments.entry(package) {
            Entry::Occupied(mut entry) => {
                let pa = entry.get_mut();
                pa.highest_decision_level = decision_level;
                assert!(
                    pa.decision.is_none(),
                    "add_derivation should not be called after a decision"
                );
                let accumulated_intersection = pa.derivations().difference(term);
                if accumulated_intersection.is_positive() {
                    self.outdated_priorities.insert(package);
                }
                pa.dated_derivations
                    .push(dated_derivation(accumulated_intersection));
            }
            Entry::Vacant(entry) => {
                let term = term.negate();
                if term.is_positive() {
                    self.outdated_priorities.insert(package);
                }
                entry.insert(PackageAssignments {
                    smallest_decision_level: decision_level,
                    highest_decision_level: decision_level,
                    dated_derivations: vec![dated_derivation(term)],
                    decision: None,
                });
            }
        }
    }

    #[cold]
    pub fn prioritized_packages(&self) -> impl Iterator<Item = (Id<DP::P>, &DP::VS)> {
        // TODO(konsti): Should we use `self.outdated_priorities` instead?
        let current_decision_level = self.current_decision_level();
        self.package_assignments
            .iter()
            .filter(move |(_, pa)| pa.highest_decision_level == current_decision_level)
            .filter_map(|(p, pa)| Some((*p, pa.potential_package_filter()?)))
    }

    #[cold]
    pub fn pick_highest_priority_pkg(
        &mut self,
        mut prioritizer: impl FnMut(Id<DP::P>, &DP::VS) -> DP::Priority,
    ) -> Option<(Id<DP::P>, &DP::VS)> {
        let package_assignments = &self.package_assignments;
        let prioritized_potential_packages = &mut self.prioritized_potential_packages;
        while let Some(p) = self.outdated_priorities.pop() {
            let Some(pa) = package_assignments.get(&p) else {
                continue;
            };
            let Some(r) = pa.potential_package_filter() else {
                continue;
            };
            let priority = prioritizer(p, r);
            prioritized_potential_packages.push(p, (priority, Reverse(p.into_raw() as u32)));
        }
        while let Some(p) = self.prioritized_potential_packages.pop().map(|(p, _)| p) {
            let Some(pa) = package_assignments.get(&p) else {
                continue;
            };
            if let Some(r) = pa.potential_package_filter() {
                return Some((p, r));
            }
        }
        None
    }

    /// If a partial solution has, for every derivation that requires a package,
    /// a corresponding decision that satisfies that assignment,
    /// it's a total solution and version solving has succeeded.
    pub fn extract_solution(&self) -> impl Iterator<Item = (Id<DP::P>, DP::V)> + '_ {
        self.decided_packages.iter().map(|&package| {
            let decision = self
                .assignments(package)
                .and_then(|pa| pa.decision.as_ref())
                .expect("Every decided package has a version");
            (package, decision.version.clone())
        })
    }

    /// Backtrack the partial solution to a given decision level.
    pub(crate) fn backtrack(&mut self, decision_level: DecisionLevel) {
        self.decided_packages
            .truncate(decision_level.get() as usize);
        self.package_assignments.retain(|p, pa| {
            if pa.smallest_decision_level > decision_level {
                // Remove all entries that have a smallest decision level higher than the backtrack target.
                false
            } else if pa.highest_decision_level <= decision_level {
                // Do not change entries older than the backtrack decision level target.
                if pa.potential_package_filter().is_some()
                    && self.prioritized_potential_packages.get(p).is_none()
                {
                    self.outdated_priorities.insert(*p);
                }
                true
            } else {
                // smallest_decision_level <= decision_level < highest_decision_level
                //
                // Since decision_level < highest_decision_level,
                // We can be certain that there will be no decision in this package assignments
                // after backtracking, because such decision would have been the last
                // assignment and it would have the "highest_decision_level".

                // Truncate the history.
                while pa.dated_derivations.last().map(|dd| dd.decision_level) > Some(decision_level)
                {
                    pa.dated_derivations.pop();
                }
                debug_assert!(!pa.dated_derivations.is_empty());

                let last = pa.dated_derivations.last().unwrap();

                // Update highest_decision_level.
                pa.highest_decision_level = last.decision_level;

                pa.decision = None;

                self.prioritized_potential_packages.remove(p);
                if pa.derivations().is_positive() {
                    self.outdated_priorities.insert(*p);
                }
                true
            }
        });

        // Close the active generation, then lower every generation invalidated by this backtrack
        // to the new highest valid decision level.
        self.last_valid_decision_levels.push(DecisionLevel::MAX);
        let index = self
            .last_valid_decision_levels
            .partition_point(|&level| level <= decision_level);
        self.last_valid_decision_levels[index..].fill(decision_level);
    }

    /// Backtrack the partial solution before a particular package was selected.
    ///
    /// This can be used to switch the order of packages if the previous prioritization was bad.
    ///
    /// Returns the new decision level on success and an error if the package was not decided on
    /// yet.
    pub(crate) fn backtrack_package(&mut self, package: Id<DP::P>) -> Result<DecisionLevel, ()> {
        let pa = self.assignments(package).ok_or(())?;
        pa.decision.as_ref().ok_or(())?;
        let decision_level = DecisionLevel::new(pa.highest_decision_level.get() - 1);
        debug!(
            "Package backtracking ot decision level {}",
            decision_level.get()
        );
        self.backtrack(decision_level);
        Ok(decision_level)
    }

    /// Add a package version as decision if none of its dependencies conflicts with the partial
    /// solution.
    ///
    /// If the resolution never backtracked before, a fast path adds the package version directly
    /// without checking dependencies.
    ///
    /// Returns the incompatibility that caused the current version to be rejected, if a conflict
    /// in the dependencies was found.
    pub(crate) fn add_package_version_incompatibilities(
        &mut self,
        package: Id<DP::P>,
        version: DP::V,
        new_incompatibilities: std::ops::Range<IncompId<DP::P, DP::VS, DP::M>>,
        store: &Arena<Incompatibility<DP::P, DP::VS, DP::M>>,
    ) -> Option<IncompId<DP::P, DP::VS, DP::M>> {
        if !self.has_backtracked() {
            // Fast path: Nothing has yet gone wrong during this resolution. This call is unlikely to be the first problem.
            // So let's live with a little bit of risk and add the decision without checking the dependencies.
            // The worst that can happen is we will have to do a full backtrack which only removes this one decision.
            log::info!("add_decision: {package:?} @ {version} without checking dependencies");
            self.add_decision(package, version);
            return None;
        }

        // Check if any of the dependencies preclude deciding on this crate version.
        let relation = |incompat: IncompId<DP::P, DP::VS, DP::M>| {
            store[incompat].relation(|p, term| {
                // The current package isn't part of the package assignments yet.
                if p == package {
                    Some(term.relation_with_version(&version))
                } else {
                    self.assignments(p).map(|pa| pa.relation(term))
                }
            })
        };
        if let Some(satisfied) = Id::range_to_iter(new_incompatibilities)
            .find(|incompat| relation(*incompat) == Relation::Satisfied)
        {
            log::info!(
                "rejecting decision {package:?} @ {version} because its dependencies conflict"
            );
            Some(satisfied)
        } else {
            log::info!("adding decision: {package:?} @ {version}");
            self.add_decision(package, version);
            None
        }
    }

    /// Check if the terms in the partial solution satisfy the incompatibility.
    pub(crate) fn relation(
        &self,
        incompat: &Incompatibility<DP::P, DP::VS, DP::M>,
    ) -> Relation<DP::P> {
        incompat.relation(|package, term| self.assignments(package).map(|pa| pa.relation(term)))
    }

    /// The allowed versions when an undecided package is required by the partial solution.
    pub fn required_versions_for_package(&self, package: Id<DP::P>) -> Option<&DP::VS> {
        self.assignments(package)?.potential_package_filter()
    }

    /// Figure out if the satisfier and previous satisfier are of different decision levels.
    #[allow(clippy::type_complexity)]
    pub(crate) fn satisfier_search(
        &self,
        incompat: &Incompatibility<DP::P, DP::VS, DP::M>,
        store: &Arena<Incompatibility<DP::P, DP::VS, DP::M>>,
    ) -> (Id<DP::P>, SatisfierSearch<DP::P, DP::VS, DP::M>) {
        let (satisfier_package, satisfier, previous_satisfier_level) =
            self.find_satisfier(incompat);
        let satisfier_pa = self
            .assignments(satisfier_package)
            .expect("Satisfier must exist");
        let incompat_term = incompat
            .get(satisfier_package)
            .expect("Satisfier must belong to incompatibility");

        let Some(satisfier_cause) = satisfier.cause else {
            // A decision satisfies this term on its own. Its first derivation bounds how
            // far back the package can remain in the partial solution.
            debug_assert!(
                satisfier_pa
                    .decision
                    .as_ref()
                    .is_some_and(|decision| { incompat_term.contains(&decision.version) })
            );
            let previous_satisfier_level =
                previous_satisfier_level.max(satisfier_pa.dated_derivations[0].decision_level);
            debug_assert!(previous_satisfier_level < satisfier.decision_level);
            return (
                satisfier_package,
                SatisfierSearch::DifferentDecisionLevels {
                    previous_satisfier_level,
                },
            );
        };

        // If the satisfier derives `not cause`, earlier assignments must satisfy
        // `incompat or cause`: (earlier and not cause) implies incompat.
        // The rule of resolution needs the same union.
        let resolved_term = incompat_term.union(
            store[satisfier_cause]
                .get(satisfier_package)
                .expect("Cause must constrain the satisfier"),
        );
        let previous_satisfier_level = if previous_satisfier_level >= satisfier.decision_level {
            // Another package already prevents backtracking below the satisfier's level.
            // Searching this package's history cannot change that outcome.
            previous_satisfier_level
        } else {
            let level = if resolved_term == Term::any() {
                // No earlier restriction on this package is needed. Keep its first derivation
                // as the historical lower bound without comparing version sets.
                satisfier_pa.dated_derivations[0].decision_level
            } else {
                satisfier_pa.satisfier(&resolved_term).decision_level
            };
            previous_satisfier_level.max(level)
        };
        let search_result = if previous_satisfier_level >= satisfier.decision_level {
            SatisfierSearch::SameDecisionLevels {
                satisfier_cause,
                resolved_term,
            }
        } else {
            SatisfierSearch::DifferentDecisionLevels {
                previous_satisfier_level,
            }
        };
        (satisfier_package, search_result)
    }

    /// Find the latest package satisfier and the highest decision level among the others.
    #[expect(clippy::type_complexity)]
    fn find_satisfier(
        &self,
        incompat: &Incompatibility<DP::P, DP::VS, DP::M>,
    ) -> (Id<DP::P>, Satisfier<DP::P, DP::VS, DP::M>, DecisionLevel) {
        let mut satisfiers = incompat.iter().map(|(package, term)| {
            let assignments = self.assignments(package).expect("Must exist");
            (package, assignments.satisfier(term))
        });
        let (mut package, mut satisfier) = satisfiers
            .next()
            .expect("Terminal incompatibilities are handled before satisfier search");
        let mut previous_level = DecisionLevel::new(1);
        for (candidate_package, candidate) in satisfiers {
            if candidate.global_index >= satisfier.global_index {
                previous_level = previous_level.max(satisfier.decision_level);
                package = candidate_package;
                satisfier = candidate;
            } else {
                previous_level = previous_level.max(candidate.decision_level);
            }
        }
        (package, satisfier, previous_level)
    }

    fn assignments(&self, package: Id<DP::P>) -> Option<&PackageAssignments<DP::P, DP::VS, DP::M>> {
        self.package_assignments.get(&package)
    }

    pub(crate) fn current_decision_level(&self) -> DecisionLevel {
        DecisionLevel::new(self.decided_packages.len() as u32)
    }

    /// The allowed versions that will not change through backtracking.
    ///
    /// This does not imply the package must be selected. It bounds candidate
    /// prefetching even when the package may still be absent.
    pub fn unchanging_versions_for_package(&self, package: Id<DP::P>) -> Option<Cow<'_, DP::VS>> {
        let pa = self.assignments(package)?;

        let idx_newer = pa
            .dated_derivations
            .as_slice()
            .partition_point(|dd| dd.decision_level <= DecisionLevel::new(1));
        let idx = idx_newer.checked_sub(1)?;
        let term = &pa.dated_derivations[idx].accumulated_intersection;
        Some(if term.negative {
            Cow::Owned(term.set.complement())
        } else {
            Cow::Borrowed(&term.set)
        })
    }
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> PackageAssignments<P, VS, M> {
    fn satisfier(&self, term: &Term<VS>) -> Satisfier<P, VS, M> {
        // Indicate if we found a satisfier in the list of derivations, otherwise it will be the decision.
        let idx = self
            .dated_derivations
            .as_slice()
            .partition_point(|dd| !dd.accumulated_intersection.subset_of(term));
        if let Some(dd) = self.dated_derivations.get(idx) {
            debug_assert_eq!(
                dd.accumulated_intersection.intersection(term),
                dd.accumulated_intersection
            );
            return Satisfier {
                cause: Some(dd.cause),
                global_index: dd.global_index,
                decision_level: dd.decision_level,
            };
        }
        // If it wasn't found in the derivations,
        // it must be the decision which is last (if called in the right context).
        let decision = self
            .decision
            .as_ref()
            .expect("The last assignment must satisfy the term");
        debug_assert!(term.contains(&decision.version));
        Satisfier {
            cause: None,
            global_index: decision.global_index,
            decision_level: self.highest_decision_level,
        }
    }

    /// The last history entry owns the intersection of all derivations.
    fn derivations(&self) -> &Term<VS> {
        &self
            .dated_derivations
            .last()
            .expect("Derivations must exist")
            .accumulated_intersection
    }

    fn relation(&self, term: &Term<VS>) -> term::Relation {
        if let Some(decision) = &self.decision {
            term.relation_with_version(&decision.version)
        } else {
            term.relation_with(self.derivations())
        }
    }

    /// An undecided package is a potential pick when its derivations require it.
    fn potential_package_filter(&self) -> Option<&VS> {
        if self.decision.is_some() {
            None
        } else {
            let term = self.derivations();
            term.is_positive().then_some(&term.set)
        }
    }
}
