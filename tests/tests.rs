// SPDX-License-Identifier: MPL-2.0

use pubgrub::{
    DefaultStringReporter, Dependencies, DependencyProvider, DerivationTree, Derived, External,
    Map, OfflineDependencyProvider, Package, PackageResolutionStatistics, PubGrubError, Ranges,
    Reporter, VersionSet, resolve,
};
use std::convert::Infallible;
use std::mem::ManuallyDrop;
use std::sync::Arc;

type NumVS = Ranges<u32>;

#[test]
fn same_result_on_repeated_runs() {
    let mut dependency_provider = OfflineDependencyProvider::<_, NumVS>::new();

    dependency_provider.add_dependencies("c", 0u32, []);
    dependency_provider.add_dependencies("c", 2u32, []);
    dependency_provider.add_dependencies("b", 0u32, []);
    dependency_provider.add_dependencies("b", 1u32, [("c", Ranges::between(0u32, 1u32))]);

    dependency_provider.add_dependencies("a", 0u32, [("b", Ranges::full()), ("c", Ranges::full())]);

    let name = "a";
    let ver: u32 = 0;
    let one = resolve(&dependency_provider, name, ver);
    for _ in 0..10 {
        match (&one, &resolve(&dependency_provider, name, ver)) {
            (Ok(l), Ok(r)) => assert_eq!(l, r),
            _ => panic!("not the same result"),
        }
    }
}

#[test]
fn should_always_find_a_satisfier() {
    let mut dependency_provider = OfflineDependencyProvider::<_, NumVS>::new();
    dependency_provider.add_dependencies("a", 0u32, [("b", Ranges::empty())]);
    assert!(matches!(
        resolve(&dependency_provider, "a", 0u32),
        Err(PubGrubError::NoSolution { .. })
    ));

    dependency_provider.add_dependencies("c", 0u32, [("a", Ranges::full())]);
    assert!(matches!(
        resolve(&dependency_provider, "c", 0u32),
        Err(PubGrubError::NoSolution { .. })
    ));
}

#[test]
fn depend_on_self() {
    let mut dependency_provider = OfflineDependencyProvider::<_, NumVS>::new();
    dependency_provider.add_dependencies("a", 0u32, [("a", Ranges::full())]);
    assert!(resolve(&dependency_provider, "a", 0u32).is_ok());
    dependency_provider.add_dependencies("a", 66u32, [("a", Ranges::singleton(111u32))]);
    assert!(resolve(&dependency_provider, "a", 66u32).is_err());
}

/// Test the prioritization is stable across platforms.
///
/// https://github.com/pubgrub-rs/pubgrub/issues/373#issuecomment-3384608891
#[test]
fn same_result_across_platforms() {
    struct UnprioritizingDependencyProvider<P: Package, VS: VersionSet> {
        dependency_provider: OfflineDependencyProvider<P, VS>,
    }

    impl<P: Package, VS: VersionSet> UnprioritizingDependencyProvider<P, VS> {
        fn new() -> Self {
            Self {
                dependency_provider: OfflineDependencyProvider::new(),
            }
        }

        pub fn add_dependencies<I: IntoIterator<Item = (P, VS)>>(
            &mut self,
            package: P,
            version: impl Into<VS::V>,
            dependencies: I,
        ) {
            self.dependency_provider
                .add_dependencies(package, version, dependencies);
        }
    }

    impl<P: Package, VS: VersionSet> DependencyProvider for UnprioritizingDependencyProvider<P, VS> {
        type P = P;
        type V = VS::V;
        type VS = VS;
        type M = String;
        type Priority = u32;
        type Err = Infallible;

        fn choose_version(&self, package: &P, range: &VS) -> Result<Option<VS::V>, Infallible> {
            self.dependency_provider.choose_version(package, range)
        }

        fn prioritize(
            &self,
            _package: &Self::P,
            _range: &Self::VS,
            _package_statistics: &PackageResolutionStatistics,
        ) -> Self::Priority {
            0
        }

        fn get_dependencies(
            &self,
            package: &P,
            version: &VS::V,
        ) -> Result<Dependencies<P, VS, Self::M>, Infallible> {
            self.dependency_provider.get_dependencies(package, version)
        }
    }

    let mut dependency_provider = UnprioritizingDependencyProvider::<_, NumVS>::new();

    let x = (0..1000)
        .map(|i| (i.to_string(), Ranges::full()))
        .collect::<Vec<_>>();
    dependency_provider.add_dependencies("root".to_string(), 1u32, x);

    for i in 0..1000 {
        let x = (0..1000)
            .filter(|j| *j != i)
            .map(|i| (i.to_string(), Ranges::<u32>::singleton(1u32)))
            .collect::<Vec<_>>();
        dependency_provider.add_dependencies(i.to_string(), 2u32, x);
        dependency_provider.add_dependencies(i.to_string(), 1u32, []);
    }

    let name = "root".to_string();
    let ver: u32 = 1;
    let resolution = resolve(&dependency_provider, name, ver).unwrap();
    let (p, _v) = resolution.into_iter().find(|(_p, v)| *v == 2).unwrap();
    assert_eq!(p, "0".to_string());
}

fn deep_derivation_tree(depth: usize) -> DerivationTree<String, Ranges<u32>, Infallible> {
    let mut tree = DerivationTree::External(External::NoVersions("leaf".into(), Ranges::empty()));
    for index in 0..depth {
        tree = DerivationTree::Derived(Derived {
            terms: Map::default(),
            shared_id: None,
            cause1: Arc::new(tree),
            cause2: Arc::new(DerivationTree::External(External::NoVersions(
                format!("external-{index}"),
                Ranges::empty(),
            ))),
        });
    }
    tree
}

fn on_small_stack(
    f: impl FnOnce(&DerivationTree<String, Ranges<u32>, Infallible>) + Send + 'static,
) {
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let tree = ManuallyDrop::new(deep_derivation_tree(1_000));
            f(&tree);
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Regression test for <https://github.com/pubgrub-rs/pubgrub/issues/293>.
#[test]
fn debug_deep_derivation_tree_without_stack_overflow() {
    on_small_stack(|tree| {
        let _ = format!("{tree:?}");
        let _ = format!("{tree:#?}");
    });
}

#[test]
fn pretty_debug_derivation_tree() {
    let tree = DerivationTree::<String, Ranges<u32>, Infallible>::External(External::NotRoot(
        "root".into(),
        1,
    ));
    assert_eq!(
        format!("{tree:#?}"),
        "External(\n    NotRoot(\n        \"root\",\n        1,\n    ),\n)"
    );
}

#[test]
fn debug_derived_tree_format() {
    let external = |package, version| {
        Arc::new(DerivationTree::External(External::NotRoot(
            package, version,
        )))
    };
    let tree = DerivationTree::<String, Ranges<u32>, Infallible>::Derived(Derived {
        terms: Map::default(),
        shared_id: None,
        cause1: external("a".into(), 1),
        cause2: external("b".into(), 2),
    });
    assert_eq!(
        format!("{tree:?}"),
        "Derived(Derived { terms: {}, shared_id: None, cause1: External(NotRoot(\"a\", 1)), cause2: External(NotRoot(\"b\", 2)) })"
    );
    assert_eq!(
        format!("{tree:#?}"),
        "Derived(\n    Derived {\n        terms: {},\n        shared_id: None,\n        cause1: External(\n            NotRoot(\n                \"a\",\n                1,\n            ),\n        ),\n        cause2: External(\n            NotRoot(\n                \"b\",\n                2,\n            ),\n        ),\n    },\n)"
    );
}

/// Regression test for <https://github.com/pubgrub-rs/pubgrub/issues/293>.
#[test]
fn report_deep_derivation_tree_without_stack_overflow() {
    on_small_stack(|tree| {
        let _ = DefaultStringReporter::report(tree);
    });
}

#[test]
fn collect_packages_from_deep_derivation_tree_without_stack_overflow() {
    on_small_stack(|tree| {
        assert_eq!(tree.packages().len(), 1_001);
    });
}

#[test]
fn collapse_deep_derivation_tree_without_stack_overflow() {
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut tree = ManuallyDrop::new(deep_derivation_tree(1_000));
            tree.collapse_no_versions();
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn collapse_no_versions_preserves_pending_merges() {
    let no_versions = |set| {
        Arc::new(DerivationTree::External(External::NoVersions(
            "foo".into(),
            set,
        )))
    };
    let inner = DerivationTree::Derived(Derived {
        terms: Map::default(),
        shared_id: None,
        cause1: no_versions(Ranges::singleton(1u32)),
        cause2: Arc::new(DerivationTree::External(External::FromDependencyOf(
            "foo".into(),
            Ranges::singleton(2u32),
            "bar".into(),
            Ranges::full(),
        ))),
    });
    let mut tree = DerivationTree::<String, Ranges<u32>, Infallible>::Derived(Derived {
        terms: Map::default(),
        shared_id: None,
        cause1: no_versions(Ranges::singleton(3u32)),
        cause2: Arc::new(inner),
    });

    tree.collapse_no_versions();

    let DerivationTree::External(External::FromDependencyOf(
        package,
        set,
        dependency,
        dependency_set,
    )) = tree
    else {
        panic!("expected a collapsed dependency");
    };
    assert_eq!(package, "foo");
    assert_eq!(dependency, "bar");
    assert_eq!(dependency_set, Ranges::full());
    assert!(set.contains(&1));
    assert!(set.contains(&2));
    assert!(set.contains(&3));
    assert!(!set.contains(&4));
}

#[test]
fn collapse_no_versions_reconstructs_failed_inner_merge() {
    let no_versions = |package| {
        Arc::new(DerivationTree::External(External::NoVersions(
            package,
            Ranges::empty(),
        )))
    };
    let inner = DerivationTree::Derived(Derived {
        terms: Map::default(),
        shared_id: Some(1),
        cause1: no_versions("inner".into()),
        cause2: Arc::new(DerivationTree::External(External::Custom(
            "custom".into(),
            Ranges::full(),
            "offline".to_string(),
        ))),
    });
    let mut tree = DerivationTree::<String, Ranges<u32>, String>::Derived(Derived {
        terms: Map::default(),
        shared_id: Some(2),
        cause1: no_versions("outer".into()),
        cause2: Arc::new(inner),
    });

    tree.collapse_no_versions();

    let DerivationTree::Derived(derived) = tree else {
        panic!("expected the failed inner merge to remain derived");
    };
    assert_eq!(derived.shared_id, Some(1));
    assert!(matches!(
        derived.cause1.as_ref(),
        DerivationTree::External(External::NoVersions(package, _)) if package == "inner"
    ));
    assert!(matches!(
        derived.cause2.as_ref(),
        DerivationTree::External(External::Custom(package, _, metadata))
            if package == "custom" && metadata == "offline"
    ));
}

#[test]
fn collapse_no_versions_panics_before_rewriting_parent() {
    let no_versions = || {
        Arc::new(DerivationTree::External(External::NoVersions(
            "missing".to_string(),
            Ranges::empty(),
        )))
    };
    let inner = DerivationTree::Derived(Derived {
        terms: Map::default(),
        shared_id: Some(1),
        cause1: no_versions(),
        cause2: Arc::new(DerivationTree::External(External::NotRoot(
            "root".into(),
            1,
        ))),
    });
    let branch = DerivationTree::Derived(Derived {
        terms: Map::default(),
        shared_id: Some(3),
        cause1: Arc::new(inner),
        cause2: Arc::new(DerivationTree::External(External::FromDependencyOf(
            "package".into(),
            Ranges::full(),
            "dependency".into(),
            Ranges::full(),
        ))),
    });
    let mut tree = DerivationTree::<String, Ranges<u32>, Infallible>::Derived(Derived {
        terms: Map::default(),
        shared_id: Some(2),
        cause1: no_versions(),
        cause2: Arc::new(branch),
    });
    let before = format!("{tree:?}");

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tree.collapse_no_versions();
    }));

    assert!(result.is_err());
    assert_eq!(format!("{tree:?}"), before);
}
