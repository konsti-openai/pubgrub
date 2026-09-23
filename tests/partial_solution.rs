// SPDX-License-Identifier: MPL-2.0

use std::cmp::Reverse;
use std::collections::BTreeMap;

use pubgrub::{OfflineDependencyProvider, Ranges, State};

type Provider = OfflineDependencyProvider<&'static str, Ranges<u32>>;

fn root_state() -> State<Provider> {
    let mut state = State::<Provider>::init("root", 1);
    let root = state.root_package;
    state.unit_propagation(root).expect("root is available");
    state.add_package_version_dependencies(
        root,
        1,
        Ranges::singleton(1u32),
        [
            ("a", Ranges::full()),
            ("b", Ranges::full()),
            ("c", Ranges::full()),
        ],
    );
    state
        .unit_propagation(root)
        .expect("root dependencies are compatible");
    state
}

#[test]
fn backtracking_restores_constraints_and_an_uncommitted_choice() {
    let mut state = root_state();
    let package_a = state.package_store.alloc("a");
    let package_b = state.package_store.alloc("b");
    let package_c = state.package_store.alloc("c");
    state.add_package_version_dependencies(
        package_a,
        1,
        Ranges::singleton(1u32),
        [("b", Ranges::higher_than(2u32))],
    );
    state
        .unit_propagation(package_a)
        .expect("b can satisfy the dependency");
    state.partial_solution.add_decision(package_b, 2);

    let chosen = state
        .partial_solution
        .pick_highest_priority_pkg(|_, _| (0, Reverse(0)))
        .map(|(package, _)| package);
    assert_eq!(chosen, Some(package_c));
    assert_eq!(state.backtrack_package(package_b), Some(1));
    assert_eq!(
        state
            .partial_solution
            .required_versions_for_package(package_b),
        Some(&Ranges::higher_than(2u32))
    );
    let chosen = state
        .partial_solution
        .pick_highest_priority_pkg(|_, _| (0, Reverse(0)))
        .map(|(package, _)| package);
    assert_eq!(chosen, Some(package_b));
    state.partial_solution.add_decision(package_b, 2);
    // The choice for c had no decision to undo, and must still be available.
    let chosen = state
        .partial_solution
        .pick_highest_priority_pkg(|_, _| (0, Reverse(0)))
        .map(|(package, _)| package);
    assert_eq!(chosen, Some(package_c));

    assert_eq!(state.backtrack_package(package_a), Some(2));
    assert_eq!(
        state
            .partial_solution
            .required_versions_for_package(package_b),
        Some(&Ranges::full())
    );
    state.partial_solution.add_decision(package_a, 3);
    state.partial_solution.add_decision(package_b, 1);
    state.partial_solution.add_decision(package_c, 1);
    assert_eq!(
        state
            .partial_solution
            .extract_solution()
            .map(|(package, version)| (state.package_store[package], version))
            .collect::<BTreeMap<_, _>>(),
        BTreeMap::from([("root", 1), ("a", 3), ("b", 1), ("c", 1)]),
    );
}

#[test]
fn current_and_stable_ranges_follow_rollback_and_reused_positions() {
    let mut state = root_state();
    let package_a = state.package_store.alloc("a");
    let package_b = state.package_store.alloc("b");
    let package_c = state.package_store.alloc("c");
    state.add_package_version_dependencies(
        package_a,
        1,
        Ranges::singleton(1u32),
        [
            ("b", Ranges::higher_than(2u32)),
            ("c", Ranges::higher_than(3u32)),
        ],
    );
    state
        .unit_propagation(package_a)
        .expect("dependencies are compatible");
    state.add_dependency(
        package_a,
        Ranges::singleton(1u32),
        (package_b, Ranges::strictly_lower_than(5u32)),
    );
    state
        .unit_propagation(package_a)
        .expect("b has compatible versions");
    let candidates = state
        .partial_solution
        .prioritized_packages()
        .map(|(package, range)| (state.package_store[package], range.clone()))
        .collect::<Vec<_>>();
    assert_eq!(candidates.len(), 2);
    assert_eq!(
        candidates.into_iter().collect::<BTreeMap<_, _>>(),
        BTreeMap::from([
            ("b", Ranges::between(2u32, 5u32)),
            ("c", Ranges::higher_than(3u32))
        ])
    );
    assert_eq!(
        state
            .partial_solution
            .unchanging_versions_for_package(package_b)
            .as_deref(),
        Some(&Ranges::full())
    );
    assert_eq!(
        state
            .partial_solution
            .unchanging_versions_for_package(package_a)
            .as_deref(),
        Some(&Ranges::full())
    );

    assert_eq!(state.backtrack_package(package_a), Some(1));
    state.add_package_version_dependencies(
        package_a,
        3,
        Ranges::singleton(3u32),
        [("b", Ranges::singleton(1u32))],
    );
    state
        .unit_propagation(package_a)
        .expect("the alternative dependency is compatible");
    let candidates = state
        .partial_solution
        .prioritized_packages()
        .map(|(package, range)| (state.package_store[package], range.clone()))
        .collect::<Vec<_>>();
    assert_eq!(candidates, vec![("b", Ranges::singleton(1u32))]);
    assert_eq!(
        state
            .partial_solution
            .required_versions_for_package(package_c),
        Some(&Ranges::full())
    );
    assert_eq!(
        state
            .partial_solution
            .unchanging_versions_for_package(package_b)
            .as_deref(),
        Some(&Ranges::full())
    );
}

#[test]
fn an_optional_package_can_be_selected_and_undone() {
    let mut state = State::<Provider>::init("root", 1);
    let root = state.root_package;
    state.unit_propagation(root).expect("root is available");
    state.partial_solution.add_decision(root, 1);
    let optional = state.package_store.alloc("optional");
    state.add_dependency(
        optional,
        Ranges::singleton(2u32),
        (root, Ranges::singleton(2u32)),
    );
    state
        .unit_propagation(root)
        .expect("optional can be absent or use a different version");
    assert_eq!(
        state
            .partial_solution
            .required_versions_for_package(optional),
        None
    );
    assert_eq!(
        state
            .partial_solution
            .unchanging_versions_for_package(optional)
            .as_deref(),
        Some(&Ranges::singleton(2u32).complement())
    );

    state.partial_solution.add_decision(optional, 1);
    assert_eq!(
        state
            .partial_solution
            .extract_solution()
            .map(|(package, version)| (state.package_store[package], version))
            .collect::<BTreeMap<_, _>>(),
        BTreeMap::from([("root", 1), ("optional", 1)])
    );
    assert_eq!(state.backtrack_package(optional), Some(1));
    assert_eq!(
        state
            .partial_solution
            .required_versions_for_package(optional),
        None
    );
    assert_eq!(
        state
            .partial_solution
            .unchanging_versions_for_package(optional)
            .as_deref(),
        Some(&Ranges::singleton(2u32).complement())
    );
}
