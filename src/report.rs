// SPDX-License-Identifier: MPL-2.0

//! Build a report as clear as possible as to why
//! dependency solving failed.

use std::fmt::{self, Debug, Display};
use std::ops::Deref;
use std::sync::Arc;

use crate::{Map, Package, Set, Term, VersionSet};

/// Reporter trait.
pub trait Reporter<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    /// Output type of the report.
    type Output;

    /// Generate a report from the derivation tree
    /// describing the resolution failure using the default formatter.
    fn report(derivation_tree: &DerivationTree<P, VS, M>) -> Self::Output;

    /// Generate a report from the derivation tree
    /// describing the resolution failure using a custom formatter.
    fn report_with_formatter(
        derivation_tree: &DerivationTree<P, VS, M>,
        formatter: &impl ReportFormatter<P, VS, M, Output = Self::Output>,
    ) -> Self::Output;
}

/// Derivation tree resulting in the impossibility to solve the dependencies of our root package.
#[derive(Clone)]
pub enum DerivationTree<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    /// External incompatibility.
    External(External<P, VS, M>),
    /// Incompatibility derived from two others.
    Derived(Derived<P, VS, M>),
}

/// Incompatibility that is not derived from other incompatibilities.
#[derive(Debug, Clone)]
pub enum External<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    /// Initial incompatibility aiming at picking the root package for the first decision.
    NotRoot(P, VS::V),
    /// There are no versions in the given set for this package.
    NoVersions(P, VS),
    /// Incompatibility coming from the dependencies of a given package.
    FromDependencyOf(P, VS, P, VS),
    /// The package is unusable for reasons outside pubgrub.
    Custom(P, VS, M),
}

/// Incompatibility derived from two others.
#[derive(Clone)]
pub struct Derived<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    /// Terms of the incompatibility.
    pub terms: Map<P, Term<VS>>,
    /// Indicate if the incompatibility is present multiple times in the derivation tree.
    ///
    /// If that is the case, the number is a unique id. This can be used to only explain this
    /// incompatibility once, then refer to the explanation for the other times.
    pub shared_id: Option<usize>,
    /// First cause.
    pub cause1: Arc<DerivationTree<P, VS, M>>,
    /// Second cause.
    pub cause2: Arc<DerivationTree<P, VS, M>>,
}

enum CompactDebugFrame<'a, P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    Tree(&'a DerivationTree<P, VS, M>),
    Derived(&'a Derived<P, VS, M>),
    Text(&'static str),
}

enum PrettyDebugFrame<'a, P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    Tree(&'a DerivationTree<P, VS, M>, usize),
    Derived(&'a Derived<P, VS, M>, usize),
    External(&'a External<P, VS, M>, usize),
    Value(&'a dyn Debug, usize),
    Indent(usize),
    Text(&'static str),
}

fn debug_derivation_tree_compact<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display>(
    frame: CompactDebugFrame<'_, P, VS, M>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let mut frames = vec![frame];
    while let Some(frame) = frames.pop() {
        match frame {
            CompactDebugFrame::Tree(DerivationTree::External(external)) => {
                f.write_str("External(")?;
                Debug::fmt(external, f)?;
                f.write_str(")")?;
            }
            CompactDebugFrame::Tree(DerivationTree::Derived(derived)) => {
                f.write_str("Derived(")?;
                frames.push(CompactDebugFrame::Text(")"));
                frames.push(CompactDebugFrame::Derived(derived));
            }
            CompactDebugFrame::Derived(derived) => {
                f.write_str("Derived { terms: ")?;
                derived.terms.fmt(f)?;
                f.write_str(", shared_id: ")?;
                derived.shared_id.fmt(f)?;
                f.write_str(", cause1: ")?;
                frames.push(CompactDebugFrame::Text(" }"));
                frames.push(CompactDebugFrame::Tree(&derived.cause2));
                frames.push(CompactDebugFrame::Text(", cause2: "));
                frames.push(CompactDebugFrame::Tree(&derived.cause1));
            }
            CompactDebugFrame::Text(text) => f.write_str(text)?,
        }
    }
    Ok(())
}

fn debug_value_pretty(value: &dyn Debug, indent: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let output = format!("{value:#?}");
    for (line_number, line) in output.lines().enumerate() {
        if line_number > 0 {
            f.write_str("\n")?;
            for _ in 0..indent {
                f.write_str(" ")?;
            }
        }
        f.write_str(line)?;
    }
    Ok(())
}

fn push_pretty_tuple_field<'a, P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display>(
    frames: &mut Vec<PrettyDebugFrame<'a, P, VS, M>>,
    value: &'a dyn Debug,
    indent: usize,
) {
    frames.push(PrettyDebugFrame::Text(",\n"));
    frames.push(PrettyDebugFrame::Value(value, indent));
    frames.push(PrettyDebugFrame::Indent(indent));
}

fn debug_derivation_tree_pretty<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display>(
    frame: PrettyDebugFrame<'_, P, VS, M>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let mut frames = vec![frame];
    while let Some(frame) = frames.pop() {
        match frame {
            PrettyDebugFrame::Tree(DerivationTree::External(external), indent) => {
                f.write_str("External(\n")?;
                frames.push(PrettyDebugFrame::Text(")"));
                frames.push(PrettyDebugFrame::Indent(indent));
                frames.push(PrettyDebugFrame::Text(",\n"));
                frames.push(PrettyDebugFrame::External(external, indent + 4));
                frames.push(PrettyDebugFrame::Indent(indent + 4));
            }
            PrettyDebugFrame::Tree(DerivationTree::Derived(derived), indent) => {
                f.write_str("Derived(\n")?;
                frames.push(PrettyDebugFrame::Text(")"));
                frames.push(PrettyDebugFrame::Indent(indent));
                frames.push(PrettyDebugFrame::Text(",\n"));
                frames.push(PrettyDebugFrame::Derived(derived, indent + 4));
                frames.push(PrettyDebugFrame::Indent(indent + 4));
            }
            PrettyDebugFrame::Derived(derived, indent) => {
                f.write_str("Derived {\n")?;
                frames.push(PrettyDebugFrame::Text("}"));
                frames.push(PrettyDebugFrame::Indent(indent));
                frames.push(PrettyDebugFrame::Text(",\n"));
                frames.push(PrettyDebugFrame::Tree(&derived.cause2, indent + 4));
                frames.push(PrettyDebugFrame::Text("cause2: "));
                frames.push(PrettyDebugFrame::Indent(indent + 4));
                frames.push(PrettyDebugFrame::Text(",\n"));
                frames.push(PrettyDebugFrame::Tree(&derived.cause1, indent + 4));
                frames.push(PrettyDebugFrame::Text("cause1: "));
                frames.push(PrettyDebugFrame::Indent(indent + 4));
                frames.push(PrettyDebugFrame::Text(",\n"));
                frames.push(PrettyDebugFrame::Value(&derived.shared_id, indent + 4));
                frames.push(PrettyDebugFrame::Text("shared_id: "));
                frames.push(PrettyDebugFrame::Indent(indent + 4));
                frames.push(PrettyDebugFrame::Text(",\n"));
                frames.push(PrettyDebugFrame::Value(&derived.terms, indent + 4));
                frames.push(PrettyDebugFrame::Text("terms: "));
                frames.push(PrettyDebugFrame::Indent(indent + 4));
            }
            PrettyDebugFrame::External(external, indent) => match external {
                External::NotRoot(package, version) => {
                    f.write_str("NotRoot(\n")?;
                    frames.push(PrettyDebugFrame::Text(")"));
                    frames.push(PrettyDebugFrame::Indent(indent));
                    push_pretty_tuple_field(&mut frames, version, indent + 4);
                    push_pretty_tuple_field(&mut frames, package, indent + 4);
                }
                External::NoVersions(package, set) => {
                    f.write_str("NoVersions(\n")?;
                    frames.push(PrettyDebugFrame::Text(")"));
                    frames.push(PrettyDebugFrame::Indent(indent));
                    push_pretty_tuple_field(&mut frames, set, indent + 4);
                    push_pretty_tuple_field(&mut frames, package, indent + 4);
                }
                External::FromDependencyOf(package, set, dependency, dependency_set) => {
                    f.write_str("FromDependencyOf(\n")?;
                    frames.push(PrettyDebugFrame::Text(")"));
                    frames.push(PrettyDebugFrame::Indent(indent));
                    push_pretty_tuple_field(&mut frames, dependency_set, indent + 4);
                    push_pretty_tuple_field(&mut frames, dependency, indent + 4);
                    push_pretty_tuple_field(&mut frames, set, indent + 4);
                    push_pretty_tuple_field(&mut frames, package, indent + 4);
                }
                External::Custom(package, set, metadata) => {
                    f.write_str("Custom(\n")?;
                    frames.push(PrettyDebugFrame::Text(")"));
                    frames.push(PrettyDebugFrame::Indent(indent));
                    push_pretty_tuple_field(&mut frames, metadata, indent + 4);
                    push_pretty_tuple_field(&mut frames, set, indent + 4);
                    push_pretty_tuple_field(&mut frames, package, indent + 4);
                }
            },
            PrettyDebugFrame::Value(value, indent) => debug_value_pretty(value, indent, f)?,
            PrettyDebugFrame::Indent(indent) => {
                for _ in 0..indent {
                    f.write_str(" ")?;
                }
            }
            PrettyDebugFrame::Text(text) => f.write_str(text)?,
        }
    }
    Ok(())
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> Debug
    for DerivationTree<P, VS, M>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            debug_derivation_tree_pretty(PrettyDebugFrame::Tree(self, 0), f)
        } else {
            debug_derivation_tree_compact(CompactDebugFrame::Tree(self), f)
        }
    }
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> Debug for Derived<P, VS, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            debug_derivation_tree_pretty(PrettyDebugFrame::Derived(self, 0), f)
        } else {
            debug_derivation_tree_compact(CompactDebugFrame::Derived(self), f)
        }
    }
}

struct PendingNoVersions<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    terms: Map<P, Term<VS>>,
    shared_id: Option<usize>,
    no_versions: Arc<DerivationTree<P, VS, M>>,
    no_versions_first: bool,
    package: P,
    set: VS,
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> PendingNoVersions<P, VS, M> {
    fn wrap(self, other: DerivationTree<P, VS, M>) -> DerivationTree<P, VS, M> {
        let other = Arc::new(other);
        let (cause1, cause2) = if self.no_versions_first {
            (self.no_versions, other)
        } else {
            (other, self.no_versions)
        };
        DerivationTree::Derived(Derived {
            terms: self.terms,
            shared_id: self.shared_id,
            cause1,
            cause2,
        })
    }
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> DerivationTree<P, VS, M> {
    /// Get all packages referred to in the derivation tree.
    pub fn packages(&self) -> Set<&P> {
        let mut packages = Set::default();
        let mut trees = vec![self];
        while let Some(tree) = trees.pop() {
            match tree {
                Self::External(external) => match external {
                    External::FromDependencyOf(p, _, p2, _) => {
                        packages.insert(p);
                        packages.insert(p2);
                    }
                    External::NoVersions(p, _)
                    | External::NotRoot(p, _)
                    | External::Custom(p, _, _) => {
                        packages.insert(p);
                    }
                },
                Self::Derived(derived) => {
                    packages.extend(derived.terms.keys());
                    trees.push(&derived.cause1);
                    trees.push(&derived.cause2);
                }
            }
        }
        packages
    }

    /// Merge the [NoVersions](External::NoVersions) external incompatibilities
    /// with the other one they are matched with
    /// in a derived incompatibility.
    /// This cleans up quite nicely the generated report.
    /// You might want to do this if you know that the
    /// [DependencyProvider](crate::solver::DependencyProvider)
    /// was not run in some kind of offline mode that may not
    /// have access to all versions existing.
    pub fn collapse_no_versions(&mut self) {
        self.assert_no_versions_not_root();
        let mut trees = vec![self];
        while let Some(tree) = trees.pop() {
            let mut pending: Vec<PendingNoVersions<P, VS, M>> = Vec::new();
            loop {
                let DerivationTree::Derived(derived) = tree else {
                    while let Some(frame) = pending.pop() {
                        if let Some(replacement) = tree
                            .clone()
                            .merge_no_versions(frame.package.clone(), frame.set.clone())
                        {
                            *tree = replacement;
                        } else {
                            *tree = frame.wrap(tree.clone());
                            pending.clear();
                            break;
                        }
                    }
                    break;
                };

                let derived_replacement = match (derived.cause1.deref(), derived.cause2.deref()) {
                    (
                        DerivationTree::External(External::NoVersions(package, set)),
                        other @ DerivationTree::Derived(_),
                    ) => Some((true, package.clone(), set.clone(), other.clone())),
                    (
                        other @ DerivationTree::Derived(_),
                        DerivationTree::External(External::NoVersions(package, set)),
                    ) => Some((false, package.clone(), set.clone(), other.clone())),
                    _ => None,
                };

                if let Some((no_versions_first, package, set, replacement)) = derived_replacement {
                    let frame = PendingNoVersions {
                        terms: std::mem::take(&mut derived.terms),
                        shared_id: derived.shared_id,
                        no_versions: if no_versions_first {
                            Arc::clone(&derived.cause1)
                        } else {
                            Arc::clone(&derived.cause2)
                        },
                        no_versions_first,
                        package,
                        set,
                    };
                    *tree = replacement;
                    pending.push(frame);
                    continue;
                }

                let external_merge = match (derived.cause1.deref(), derived.cause2.deref()) {
                    (
                        DerivationTree::External(External::NoVersions(package, set)),
                        other @ DerivationTree::External(_),
                    ) => Some(
                        other
                            .clone()
                            .merge_no_versions(package.clone(), set.clone()),
                    ),
                    (
                        other @ DerivationTree::External(_),
                        DerivationTree::External(External::NoVersions(package, set)),
                    ) => Some(
                        other
                            .clone()
                            .merge_no_versions(package.clone(), set.clone()),
                    ),
                    _ => None,
                };

                match external_merge {
                    Some(Some(replacement)) => {
                        *tree = replacement;
                    }
                    Some(None) => break,
                    None => {
                        pending.clear();
                        let DerivationTree::Derived(derived) = tree else {
                            unreachable!();
                        };
                        let cause1 = Arc::make_mut(&mut derived.cause1);
                        let cause2 = Arc::make_mut(&mut derived.cause2);
                        trees.push(cause2);
                        trees.push(cause1);
                        break;
                    }
                }
            }
        }
    }

    fn assert_no_versions_not_root(&self) {
        let mut trees = vec![self];
        while let Some(tree) = trees.pop() {
            if let DerivationTree::Derived(derived) = tree {
                if matches!(
                    (derived.cause1.deref(), derived.cause2.deref()),
                    (
                        DerivationTree::External(External::NoVersions(_, _)),
                        DerivationTree::External(External::NotRoot(_, _)),
                    ) | (
                        DerivationTree::External(External::NotRoot(_, _)),
                        DerivationTree::External(External::NoVersions(_, _)),
                    )
                ) {
                    panic!("How did we end up with a NoVersions merged with a NotRoot?");
                }
                trees.push(&derived.cause2);
                trees.push(&derived.cause1);
            }
        }
    }

    fn merge_no_versions(self, package: P, set: VS) -> Option<Self> {
        match self {
            // TODO: take care of the Derived case.
            // Once done, we can remove the Option.
            DerivationTree::Derived(_) => Some(self),
            DerivationTree::External(External::NotRoot(_, _)) => {
                panic!("How did we end up with a NoVersions merged with a NotRoot?")
            }
            //
            // Cannot be merged because the reason may not match
            DerivationTree::External(External::NoVersions(_, _)) => None,
            DerivationTree::External(External::FromDependencyOf(p1, r1, p2, r2)) => {
                if p1 == package {
                    Some(DerivationTree::External(External::FromDependencyOf(
                        p1,
                        r1.union(&set),
                        p2,
                        r2,
                    )))
                } else {
                    Some(DerivationTree::External(External::FromDependencyOf(
                        p1,
                        r1,
                        p2,
                        r2.union(&set),
                    )))
                }
            }
            // Cannot be merged because the reason may not match
            DerivationTree::External(External::Custom(_, _, _)) => None,
        }
    }
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> Display for External<P, VS, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotRoot(package, version) => {
                write!(f, "we are solving dependencies of {package} {version}")
            }
            Self::NoVersions(package, set) => {
                if set == &VS::full() {
                    write!(f, "there is no available version for {package}")
                } else {
                    write!(f, "there is no version of {package} in {set}")
                }
            }
            Self::Custom(package, set, metadata) => {
                if set == &VS::full() {
                    write!(f, "dependencies of {package} are unavailable {metadata}")
                } else {
                    write!(
                        f,
                        "dependencies of {package} at version {set} are unavailable {metadata}"
                    )
                }
            }
            Self::FromDependencyOf(p, set_p, dep, set_dep) => {
                if set_p == &VS::full() && set_dep == &VS::full() {
                    write!(f, "{p} depends on {dep}")
                } else if set_p == &VS::full() {
                    write!(f, "{p} depends on {dep} {set_dep}")
                } else if set_dep == &VS::full() {
                    write!(f, "{p} {set_p} depends on {dep}")
                } else {
                    write!(f, "{p} {set_p} depends on {dep} {set_dep}")
                }
            }
        }
    }
}

/// Trait for formatting outputs in the reporter.
pub trait ReportFormatter<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    /// Output type of the report.
    type Output;

    /// Format an [External] incompatibility.
    fn format_external(&self, external: &External<P, VS, M>) -> Self::Output;

    /// Format terms of an incompatibility.
    fn format_terms(&self, terms: &Map<P, Term<VS>>) -> Self::Output;

    /// Simplest case, we just combine two external incompatibilities.
    fn explain_both_external(
        &self,
        external1: &External<P, VS, M>,
        external2: &External<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> Self::Output;

    /// Both causes have already been explained so we use their refs.
    fn explain_both_ref(
        &self,
        ref_id1: usize,
        derived1: &Derived<P, VS, M>,
        ref_id2: usize,
        derived2: &Derived<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> Self::Output;

    /// One cause is derived (already explained so one-line),
    /// the other is a one-line external cause,
    /// and finally we conclude with the current incompatibility.
    fn explain_ref_and_external(
        &self,
        ref_id: usize,
        derived: &Derived<P, VS, M>,
        external: &External<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> Self::Output;

    /// Add an external cause to the chain of explanations.
    fn and_explain_external(
        &self,
        external: &External<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> Self::Output;

    /// Add an already explained incompat to the chain of explanations.
    fn and_explain_ref(
        &self,
        ref_id: usize,
        derived: &Derived<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> Self::Output;

    /// Add an already explained incompat to the chain of explanations.
    fn and_explain_prior_and_external(
        &self,
        prior_external: &External<P, VS, M>,
        external: &External<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> Self::Output;
}

/// Default formatter for the default reporter.
#[derive(Default, Debug)]
pub struct DefaultStringReportFormatter;

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> ReportFormatter<P, VS, M>
    for DefaultStringReportFormatter
{
    type Output = String;

    fn format_external(&self, external: &External<P, VS, M>) -> String {
        external.to_string()
    }

    fn format_terms(&self, terms: &Map<P, Term<VS>>) -> Self::Output {
        let terms_vec: Vec<_> = terms.iter().collect();
        match terms_vec.as_slice() {
            [] => "version solving failed".into(),
            // TODO: special case when that unique package is root.
            [(package, Term::Positive(range))] => format!("{package} {range} is forbidden"),
            [(package, Term::Negative(range))] => format!("{package} {range} is mandatory"),
            [(p1, Term::Positive(r1)), (p2, Term::Negative(r2))] => self.format_external(
                &External::<_, _, M>::FromDependencyOf(p1, r1.clone(), p2, r2.clone()),
            ),
            [(p1, Term::Negative(r1)), (p2, Term::Positive(r2))] => self.format_external(
                &External::<_, _, M>::FromDependencyOf(p2, r2.clone(), p1, r1.clone()),
            ),
            slice => {
                let str_terms: Vec<_> = slice.iter().map(|(p, t)| format!("{p} {t}")).collect();
                str_terms.join(", ") + " are incompatible"
            }
        }
    }

    /// Simplest case, we just combine two external incompatibilities.
    fn explain_both_external(
        &self,
        external1: &External<P, VS, M>,
        external2: &External<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> String {
        // TODO: order should be chosen to make it more logical.
        format!(
            "Because {} and {}, {}.",
            self.format_external(external1),
            self.format_external(external2),
            ReportFormatter::<P, VS, M>::format_terms(self, current_terms)
        )
    }

    /// Both causes have already been explained so we use their refs.
    fn explain_both_ref(
        &self,
        ref_id1: usize,
        derived1: &Derived<P, VS, M>,
        ref_id2: usize,
        derived2: &Derived<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> String {
        // TODO: order should be chosen to make it more logical.
        format!(
            "Because {} ({}) and {} ({}), {}.",
            ReportFormatter::<P, VS, M>::format_terms(self, &derived1.terms),
            ref_id1,
            ReportFormatter::<P, VS, M>::format_terms(self, &derived2.terms),
            ref_id2,
            ReportFormatter::<P, VS, M>::format_terms(self, current_terms)
        )
    }

    /// One cause is derived (already explained so one-line),
    /// the other is a one-line external cause,
    /// and finally we conclude with the current incompatibility.
    fn explain_ref_and_external(
        &self,
        ref_id: usize,
        derived: &Derived<P, VS, M>,
        external: &External<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> String {
        // TODO: order should be chosen to make it more logical.
        format!(
            "Because {} ({}) and {}, {}.",
            ReportFormatter::<P, VS, M>::format_terms(self, &derived.terms),
            ref_id,
            self.format_external(external),
            ReportFormatter::<P, VS, M>::format_terms(self, current_terms)
        )
    }

    /// Add an external cause to the chain of explanations.
    fn and_explain_external(
        &self,
        external: &External<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> String {
        format!(
            "And because {}, {}.",
            self.format_external(external),
            ReportFormatter::<P, VS, M>::format_terms(self, current_terms)
        )
    }

    /// Add an already explained incompat to the chain of explanations.
    fn and_explain_ref(
        &self,
        ref_id: usize,
        derived: &Derived<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> String {
        format!(
            "And because {} ({}), {}.",
            ReportFormatter::<P, VS, M>::format_terms(self, &derived.terms),
            ref_id,
            ReportFormatter::<P, VS, M>::format_terms(self, current_terms)
        )
    }

    /// Add an already explained incompat to the chain of explanations.
    fn and_explain_prior_and_external(
        &self,
        prior_external: &External<P, VS, M>,
        external: &External<P, VS, M>,
        current_terms: &Map<P, Term<VS>>,
    ) -> String {
        format!(
            "And because {} and {}, {}.",
            self.format_external(prior_external),
            self.format_external(external),
            ReportFormatter::<P, VS, M>::format_terms(self, current_terms)
        )
    }
}

/// Default reporter able to generate an explanation as a [String].
pub struct DefaultStringReporter {
    /// Number of explanations already with a line reference.
    ref_count: usize,
    /// Shared nodes that have already been marked with a line reference.
    /// The incompatibility ids are the keys, and the line references are the values.
    shared_with_ref: Map<usize, usize>,
    /// Accumulated lines of the report already generated.
    lines: Vec<String>,
}

enum ReportFrame<'a, P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    Build(&'a Derived<P, VS, M>),
    FinishShared(Option<usize>),
    PushBlank,
    PushAndExplainRef {
        ref_id: usize,
        derived: &'a Derived<P, VS, M>,
        current_terms: &'a Map<P, Term<VS>>,
    },
    PushAndExplainExternal {
        external: &'a External<P, VS, M>,
        current_terms: &'a Map<P, Term<VS>>,
    },
    PushAndExplainPriorAndExternal {
        prior_external: &'a External<P, VS, M>,
        external: &'a External<P, VS, M>,
        current_terms: &'a Map<P, Term<VS>>,
    },
    ContinueBothUnreferenced {
        derived1: &'a Derived<P, VS, M>,
        derived2: &'a Derived<P, VS, M>,
        current_terms: &'a Map<P, Term<VS>>,
    },
}

impl DefaultStringReporter {
    /// Initialize the reporter.
    fn new() -> Self {
        Self {
            ref_count: 0,
            shared_with_ref: Map::default(),
            lines: Vec::new(),
        }
    }

    fn build<
        P: Package,
        VS: VersionSet,
        M: Eq + Clone + Debug + Display,
        F: ReportFormatter<P, VS, M, Output = String>,
    >(
        &mut self,
        derived: &Derived<P, VS, M>,
        formatter: &F,
    ) {
        let mut frames = vec![ReportFrame::Build(derived)];
        while let Some(frame) = frames.pop() {
            match frame {
                ReportFrame::Build(current) => {
                    frames.push(ReportFrame::FinishShared(current.shared_id));
                    match (current.cause1.deref(), current.cause2.deref()) {
                        (
                            DerivationTree::External(external1),
                            DerivationTree::External(external2),
                        ) => self.lines.push(formatter.explain_both_external(
                            external1,
                            external2,
                            &current.terms,
                        )),
                        (DerivationTree::Derived(derived), DerivationTree::External(external))
                        | (DerivationTree::External(external), DerivationTree::Derived(derived)) => {
                            match self.line_ref_of(derived.shared_id) {
                                Some(ref_id) => {
                                    self.lines.push(formatter.explain_ref_and_external(
                                        ref_id,
                                        derived,
                                        external,
                                        &current.terms,
                                    ));
                                }
                                None => match (derived.cause1.deref(), derived.cause2.deref()) {
                                    (
                                        DerivationTree::Derived(prior_derived),
                                        DerivationTree::External(prior_external),
                                    )
                                    | (
                                        DerivationTree::External(prior_external),
                                        DerivationTree::Derived(prior_derived),
                                    ) => {
                                        frames.push(ReportFrame::PushAndExplainPriorAndExternal {
                                            prior_external,
                                            external,
                                            current_terms: &current.terms,
                                        });
                                        frames.push(ReportFrame::Build(prior_derived));
                                    }
                                    _ => {
                                        frames.push(ReportFrame::PushAndExplainExternal {
                                            external,
                                            current_terms: &current.terms,
                                        });
                                        frames.push(ReportFrame::Build(derived));
                                    }
                                },
                            }
                        }
                        (DerivationTree::Derived(derived1), DerivationTree::Derived(derived2)) => {
                            match (
                                self.line_ref_of(derived1.shared_id),
                                self.line_ref_of(derived2.shared_id),
                            ) {
                                (Some(ref1), Some(ref2)) => {
                                    self.lines.push(formatter.explain_both_ref(
                                        ref1,
                                        derived1,
                                        ref2,
                                        derived2,
                                        &current.terms,
                                    ));
                                }
                                (Some(ref1), None) => {
                                    frames.push(ReportFrame::PushAndExplainRef {
                                        ref_id: ref1,
                                        derived: derived1,
                                        current_terms: &current.terms,
                                    });
                                    frames.push(ReportFrame::Build(derived2));
                                }
                                (None, Some(ref2)) => {
                                    frames.push(ReportFrame::PushAndExplainRef {
                                        ref_id: ref2,
                                        derived: derived2,
                                        current_terms: &current.terms,
                                    });
                                    frames.push(ReportFrame::Build(derived1));
                                }
                                (None, None) if derived1.shared_id.is_some() => {
                                    frames.push(ReportFrame::Build(current));
                                    frames.push(ReportFrame::PushBlank);
                                    frames.push(ReportFrame::Build(derived1));
                                }
                                (None, None) => {
                                    frames.push(ReportFrame::ContinueBothUnreferenced {
                                        derived1,
                                        derived2,
                                        current_terms: &current.terms,
                                    });
                                    frames.push(ReportFrame::Build(derived1));
                                }
                            }
                        }
                    }
                }
                ReportFrame::FinishShared(shared_id) => {
                    if let Some(id) = shared_id {
                        #[allow(clippy::map_entry)] // `add_line_ref` needs mutable `self`.
                        if !self.shared_with_ref.contains_key(&id) {
                            self.add_line_ref();
                            self.shared_with_ref.insert(id, self.ref_count);
                        }
                    }
                }
                ReportFrame::PushBlank => self.lines.push(String::new()),
                ReportFrame::PushAndExplainRef {
                    ref_id,
                    derived,
                    current_terms,
                } => self
                    .lines
                    .push(formatter.and_explain_ref(ref_id, derived, current_terms)),
                ReportFrame::PushAndExplainExternal {
                    external,
                    current_terms,
                } => self
                    .lines
                    .push(formatter.and_explain_external(external, current_terms)),
                ReportFrame::PushAndExplainPriorAndExternal {
                    prior_external,
                    external,
                    current_terms,
                } => self.lines.push(formatter.and_explain_prior_and_external(
                    prior_external,
                    external,
                    current_terms,
                )),
                ReportFrame::ContinueBothUnreferenced {
                    derived1,
                    derived2,
                    current_terms,
                } => {
                    self.add_line_ref();
                    let ref1 = self.ref_count;
                    self.lines.push(String::new());
                    frames.push(ReportFrame::PushAndExplainRef {
                        ref_id: ref1,
                        derived: derived1,
                        current_terms,
                    });
                    frames.push(ReportFrame::Build(derived2));
                }
            }
        }
    }

    // Helper functions ########################################################

    fn add_line_ref(&mut self) {
        let new_count = self.ref_count + 1;
        self.ref_count = new_count;
        if let Some(line) = self.lines.last_mut() {
            *line = format!("{line} ({new_count})");
        }
    }

    fn line_ref_of(&self, shared_id: Option<usize>) -> Option<usize> {
        shared_id.and_then(|id| self.shared_with_ref.get(&id).cloned())
    }
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> Reporter<P, VS, M>
    for DefaultStringReporter
{
    type Output = String;

    fn report(derivation_tree: &DerivationTree<P, VS, M>) -> Self::Output {
        let formatter = DefaultStringReportFormatter;
        match derivation_tree {
            DerivationTree::External(external) => formatter.format_external(external),
            DerivationTree::Derived(derived) => {
                let mut reporter = Self::new();
                reporter.build(derived, &formatter);
                reporter.lines.join("\n")
            }
        }
    }

    fn report_with_formatter(
        derivation_tree: &DerivationTree<P, VS, M>,
        formatter: &impl ReportFormatter<P, VS, M, Output = Self::Output>,
    ) -> Self::Output {
        match derivation_tree {
            DerivationTree::External(external) => formatter.format_external(external),
            DerivationTree::Derived(derived) => {
                let mut reporter = Self::new();
                reporter.build(derived, formatter);
                reporter.lines.join("\n")
            }
        }
    }
}
