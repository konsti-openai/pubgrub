// SPDX-License-Identifier: MPL-2.0

//! Package decisions and the derivations that constrain them.

use std::borrow::Cow;
use std::cmp::Reverse;
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
}

impl Debug for DecisionLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DecisionLevel({})", self.get())
    }
}

// Preserve the niche so `Option<DecisionLevel>` stays as small as a bare `u32`.
const _: () = assert!(std::mem::size_of::<Option<DecisionLevel>>() == std::mem::size_of::<u32>());

/// Assignments in chronological order, with package histories indexing that same log.
///
/// Decision indices divide the log into levels. Backtracking removes a suffix and
/// restores each affected package to its preceding assignment.
#[derive(Clone, Debug)]
pub struct PartialSolution<DP: DependencyProvider> {
    #[expect(clippy::type_complexity)]
    trail: Vec<(Id<DP::P>, Assignment<DP::P, DP::VS, DP::M>)>,
    /// Increasing trail indices for each package; the last is its current assignment.
    histories: Map<Id<DP::P>, Vec<usize>>,
    /// The trail index of each decision, in decision order.
    decisions: Vec<usize>,
    #[allow(clippy::type_complexity)]
    prioritized_potential_packages:
        PriorityQueue<Id<DP::P>, (DP::Priority, Reverse<u32>), BuildHasherDefault<FxHasher>>,
    /// Packages whose constraints changed since their priority was computed.
    outdated_priorities: FnvIndexSet<Id<DP::P>>,
    /// The highest level that survived each completed backtrack generation.
    last_valid_decision_levels: Vec<DecisionLevel>,
}

#[derive(Clone, Debug)]
enum Assignment<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    Decision(VS::V),
    Derivation {
        cause: IncompId<P, VS, M>,
        /// The intersection of this package's derivations through this assignment.
        term: Term<VS>,
    },
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

impl<DP: DependencyProvider> PartialSolution<DP> {
    pub(crate) fn empty() -> Self {
        Self {
            trail: Vec::new(),
            histories: Map::default(),
            decisions: Vec::new(),
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
                for (index, (package, assignment)) in self.0.trail.iter().enumerate() {
                    writeln!(
                        f,
                        "{index}: {:?} {} {assignment:?}",
                        self.0.decision_level(index),
                        self.1[*package]
                    )?;
                }
                Ok(())
            }
        }

        PSDisplay(self, package_store)
    }

    fn push(&mut self, package: Id<DP::P>, assignment: Assignment<DP::P, DP::VS, DP::M>) {
        self.histories
            .entry(package)
            .or_default()
            .push(self.trail.len());
        self.trail.push((package, assignment));
    }

    /// Record a selected version. Its trail position starts the next decision level.
    pub fn add_decision(&mut self, package: Id<DP::P>, version: DP::V) {
        let term = self
            .assignment(package)
            .and_then(Assignment::derivation)
            .expect("Derivations must already exist");
        debug_assert!(term.contains(&version));
        self.decisions.push(self.trail.len());
        self.push(package, Assignment::Decision(version));
        self.prioritized_potential_packages.remove(&package);
    }

    /// Packages in the priority queue, with their most recently computed priorities.
    #[allow(clippy::type_complexity)]
    pub fn undecided_packages(
        &self,
    ) -> impl Iterator<Item = (&Id<DP::P>, &(DP::Priority, Reverse<u32>))> {
        self.prioritized_potential_packages.iter()
    }

    pub(crate) fn add_derivation(
        &mut self,
        package: Id<DP::P>,
        cause: IncompDpId<DP>,
        store: &Arena<Incompatibility<DP::P, DP::VS, DP::M>>,
    ) {
        let excluded = store[cause]
            .get(package)
            .expect("The cause constrains the package");
        let term = match self.assignment(package) {
            Some(assignment) => assignment
                .derivation()
                .expect("Cannot derive a constraint after a decision")
                .difference(excluded),
            None => excluded.negate(),
        };
        if term.is_positive() {
            self.outdated_priorities.insert(package);
        }
        self.push(package, Assignment::Derivation { cause, term });
    }

    /// Undecided packages whose current constraints were derived at this decision level.
    #[cold]
    pub fn prioritized_packages(&self) -> impl Iterator<Item = (Id<DP::P>, &DP::VS)> {
        let start = self.decisions.last().copied().unwrap_or(0);
        self.trail[start..]
            .iter()
            .enumerate()
            .filter_map(move |(offset, (package, assignment))| {
                if self.histories[package].last() == Some(&(start + offset)) {
                    Some((*package, assignment.required_versions()?))
                } else {
                    None
                }
            })
    }

    /// Refresh changed priorities and inspect the best undecided package.
    /// The package remains queued until a decision is recorded or its constraints exclude it.
    #[cold]
    pub fn pick_highest_priority_pkg(
        &mut self,
        mut prioritizer: impl FnMut(Id<DP::P>, &DP::VS) -> DP::Priority,
    ) -> Option<(Id<DP::P>, &DP::VS)> {
        while let Some(package) = self.outdated_priorities.pop() {
            if let Some(versions) = self.required_versions_for_package(package) {
                let priority = prioritizer(package, versions);
                self.prioritized_potential_packages
                    .push(package, (priority, Reverse(package.into_raw() as u32)));
            }
        }
        // Keep the chosen package queued until it is decided. If a proposed version
        // conflicts before a decision is recorded, no trail entry exists to restore it.
        while let Some((&package, _)) = self.prioritized_potential_packages.peek() {
            if let Some(&index) = self
                .histories
                .get(&package)
                .and_then(|history| history.last())
                && let Some(versions) = self.trail[index].1.required_versions()
            {
                return Some((package, versions));
            }
            self.prioritized_potential_packages.pop();
        }
        None
    }

    /// Selected versions in decision order.
    pub fn extract_solution(&self) -> impl Iterator<Item = (Id<DP::P>, DP::V)> + '_ {
        self.decisions.iter().map(|&index| {
            let (package, assignment) = &self.trail[index];
            let version = assignment
                .decision()
                .expect("A decision index points to a decision");
            (*package, version.clone())
        })
    }

    pub(crate) fn backtrack(&mut self, decision_level: DecisionLevel) {
        let end = self
            .decisions
            .get(decision_level.get() as usize)
            .copied()
            .unwrap_or(self.trail.len());
        while self.trail.len() > end {
            let (package, _) = self
                .trail
                .pop()
                .expect("The trail extends past the target level");
            let history = self
                .histories
                .get_mut(&package)
                .expect("Every assignment has a package history");
            history.pop();
            if history.is_empty() {
                self.histories.remove(&package);
            }
            self.prioritized_potential_packages.remove(&package);
            self.outdated_priorities.insert(package);
        }
        self.decisions.truncate(decision_level.get() as usize);

        // Invalidate cached contradictions whose supporting decisions were undone.
        self.last_valid_decision_levels.push(DecisionLevel::MAX);
        let index = self
            .last_valid_decision_levels
            .partition_point(|&level| level <= decision_level);
        self.last_valid_decision_levels[index..].fill(decision_level);
    }

    /// Undo the decision for a package and all subsequent assignments.
    pub(crate) fn backtrack_package(&mut self, package: Id<DP::P>) -> Result<DecisionLevel, ()> {
        let &index = self
            .histories
            .get(&package)
            .and_then(|history| history.last())
            .ok_or(())?;
        let Assignment::Decision(_) = self.trail[index].1 else {
            return Err(());
        };
        let decision_level = DecisionLevel::new(self.decision_level(index).get() - 1);
        debug!(
            "Package backtracking to decision level {}",
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
                    self.assignment(p)
                        .map(|assignment| assignment.relation(term))
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
        incompat.relation(|package, term| {
            self.assignment(package)
                .map(|assignment| assignment.relation(term))
        })
    }

    /// The allowed versions when an undecided package is required by the partial solution.
    pub fn required_versions_for_package(&self, package: Id<DP::P>) -> Option<&DP::VS> {
        self.assignment(package)?.required_versions()
    }

    /// Find the assignment that completes an incompatibility and the level to undo to.
    #[allow(clippy::type_complexity)]
    pub(crate) fn satisfier_search(
        &self,
        incompat: &Incompatibility<DP::P, DP::VS, DP::M>,
        store: &Arena<Incompatibility<DP::P, DP::VS, DP::M>>,
    ) -> (Id<DP::P>, SatisfierSearch<DP::P, DP::VS, DP::M>) {
        let (package, index, previous_level) = self.find_satisfier(incompat);
        let level = self.decision_level(index);
        let first_level = self.decision_level(self.histories[&package][0]);
        let Assignment::Derivation { cause, .. } = &self.trail[index].1 else {
            return (
                package,
                SatisfierSearch::DifferentDecisionLevels {
                    previous_satisfier_level: previous_level.max(first_level),
                },
            );
        };

        // Earlier assignments must satisfy `incompat or cause`: combined with
        // the derived `not cause`, that implies the incompatibility's term.
        let resolved_term = incompat
            .get(package)
            .expect("The satisfier belongs to the incompatibility")
            .union(
                store[*cause]
                    .get(package)
                    .expect("The cause constrains the satisfier"),
            );
        let previous_level = if previous_level >= level {
            previous_level
        } else if resolved_term == Term::any() {
            previous_level.max(first_level)
        } else {
            previous_level.max(self.decision_level(self.satisfier(package, &resolved_term)))
        };
        let result = if previous_level >= level {
            SatisfierSearch::SameDecisionLevels {
                satisfier_cause: *cause,
                resolved_term,
            }
        } else {
            SatisfierSearch::DifferentDecisionLevels {
                previous_satisfier_level: previous_level,
            }
        };
        (package, result)
    }

    /// Latest satisfier position and the highest decision level among the other terms.
    fn find_satisfier(
        &self,
        incompat: &Incompatibility<DP::P, DP::VS, DP::M>,
    ) -> (Id<DP::P>, usize, DecisionLevel) {
        let mut satisfiers = incompat
            .iter()
            .map(|(package, term)| (package, self.satisfier(package, term)));
        let (mut package, mut latest) = satisfiers
            .next()
            .expect("Terminal incompatibilities are handled first");
        let mut previous = 0;
        for (candidate_package, candidate) in satisfiers {
            if candidate >= latest {
                previous = previous.max(latest);
                package = candidate_package;
                latest = candidate;
            } else {
                previous = previous.max(candidate);
            }
        }
        (
            package,
            latest,
            self.decision_level(previous).max(DecisionLevel::new(1)),
        )
    }

    /// The first assignment for this package that implies the term.
    fn satisfier(&self, package: Id<DP::P>, term: &Term<DP::VS>) -> usize {
        let history = &self.histories[&package];
        let position = history.partition_point(|&index| !self.trail[index].1.satisfies(term));
        *history
            .get(position)
            .expect("The current assignment satisfies the term")
    }

    fn assignment(&self, package: Id<DP::P>) -> Option<&Assignment<DP::P, DP::VS, DP::M>> {
        let &index = self.histories.get(&package)?.last()?;
        Some(&self.trail[index].1)
    }

    fn decision_level(&self, index: usize) -> DecisionLevel {
        DecisionLevel::new(
            self.decisions
                .partition_point(|&decision| decision <= index) as u32,
        )
    }

    pub(crate) fn current_decision_level(&self) -> DecisionLevel {
        DecisionLevel::new(self.decisions.len() as u32)
    }

    /// Allowed versions that remain valid through backtracking, whether required or optional.
    pub fn unchanging_versions_for_package(&self, package: Id<DP::P>) -> Option<Cow<'_, DP::VS>> {
        let history = self.histories.get(&package)?;
        let end = self.decisions.get(1).copied().unwrap_or(self.trail.len());
        let stable = history.partition_point(|&index| index < end);
        let term = history[..stable]
            .iter()
            .rev()
            .find_map(|&index| self.trail[index].1.derivation())?;
        Some(if term.negative {
            Cow::Owned(term.set.complement())
        } else {
            Cow::Borrowed(&term.set)
        })
    }
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> Assignment<P, VS, M> {
    fn relation(&self, term: &Term<VS>) -> term::Relation {
        match self {
            Self::Decision(version) => term.relation_with_version(version),
            Self::Derivation {
                term: intersection, ..
            } => term.relation_with(intersection),
        }
    }

    fn satisfies(&self, term: &Term<VS>) -> bool {
        match self {
            Self::Decision(version) => term.contains(version),
            Self::Derivation {
                term: intersection, ..
            } => intersection.subset_of(term),
        }
    }

    fn decision(&self) -> Option<&VS::V> {
        match self {
            Self::Decision(version) => Some(version),
            Self::Derivation { .. } => None,
        }
    }

    fn derivation(&self) -> Option<&Term<VS>> {
        match self {
            Self::Derivation { term, .. } => Some(term),
            Self::Decision(_) => None,
        }
    }

    fn required_versions(&self) -> Option<&VS> {
        let term = self.derivation()?;
        term.is_positive().then_some(&term.set)
    }
}
