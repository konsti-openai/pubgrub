// SPDX-License-Identifier: MPL-2.0

use std::cmp::Reverse;

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
        [("a", Ranges::full()), ("b", Ranges::full())],
    );
    state
        .unit_propagation(root)
        .expect("root dependencies are compatible");
    state
}

#[test]
fn backtracking_retains_an_uncommitted_choice() {
    let mut state = root_state();
    let package_a = state.package_store.alloc("a");
    let package_b = state.package_store.alloc("b");
    state.partial_solution.add_decision(package_a, 1);
    assert_eq!(
        state
            .partial_solution
            .pick_highest_priority_pkg(|_, _| (0, Reverse(0)))
            .map(|(package, _)| package),
        Some(package_b)
    );

    assert_eq!(state.backtrack_package(package_a), Some(1));
    state.partial_solution.add_decision(package_a, 2);
    // No decision for b was undone, but its pending choice must still be available.
    assert_eq!(
        state
            .partial_solution
            .pick_highest_priority_pkg(|_, _| (0, Reverse(0)))
            .map(|(package, _)| package),
        Some(package_b)
    );
}

#[test]
fn current_and_stable_ranges_follow_rollback() {
    let mut state = root_state();
    let package_a = state.package_store.alloc("a");
    let package_b = state.package_store.alloc("b");
    state.add_package_version_dependencies(
        package_a,
        1,
        Ranges::singleton(1u32),
        [("b", Ranges::higher_than(2u32))],
    );
    state.unit_propagation(package_a).expect("b is compatible");
    state.add_dependency(
        package_a,
        Ranges::singleton(1u32),
        (package_b, Ranges::strictly_lower_than(5u32)),
    );
    state.unit_propagation(package_a).expect("b is compatible");
    assert_eq!(
        state
            .partial_solution
            .prioritized_packages()
            .collect::<Vec<_>>(),
        vec![(package_b, &Ranges::between(2u32, 5u32))]
    );
    assert_eq!(
        state
            .partial_solution
            .unchanging_versions_for_package(package_b)
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
    state.unit_propagation(package_a).expect("b is compatible");
    assert_eq!(
        state
            .partial_solution
            .prioritized_packages()
            .collect::<Vec<_>>(),
        vec![(package_b, &Ranges::singleton(1u32))]
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

    state.partial_solution.add_decision(optional, 1);
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
