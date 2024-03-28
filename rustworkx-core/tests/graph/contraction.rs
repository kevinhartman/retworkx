// use petgraph::graph::IndexType;
// use petgraph::graph::NodeIndex;
use hashbrown::HashSet;
use petgraph::data::Build;
use petgraph::visit::{
    Data, EdgeRef, GraphBase, IntoEdgeReferences, IntoEdgesDirected, IntoNodeIdentifiers,
};
use rustworkx_core::err::ContractError;
use rustworkx_core::graph::directed::*;
use rustworkx_core::graph::NodeRemovable;
use std::fmt::Debug;
use std::hash::Hash;

mod graph {
    use petgraph::prelude::*;
    type G = DiGraph<char, usize>;

    common_test!(test_cycle_check_enabled, G);
    common_test!(test_cycle_check_disabled, G);
    common_test!(test_empty_nodes, G);
    common_test!(test_unknown_nodes, G);
    common_test!(test_cycle_path_len_gt_1, G);
    common_test!(test_multiple_paths_would_cycle, G);
}

mod graph_map {
    use petgraph::prelude::*;
    type G = DiGraphMap<char, usize>;

    common_test!(test_cycle_check_enabled, G);
    common_test!(test_cycle_check_disabled, G);
    common_test!(test_empty_nodes, G);
    common_test!(test_unknown_nodes, G);
    common_test!(test_cycle_path_len_gt_1, G);
    common_test!(test_multiple_paths_would_cycle, G);
}

mod matrix_graph {
    use petgraph::matrix_graph::DiMatrix;
    type G = DiMatrix<char, usize>;

    common_test!(test_cycle_check_enabled, G);
    common_test!(test_cycle_check_disabled, G);
    common_test!(test_empty_nodes, G);
    common_test!(test_unknown_nodes, G);
    common_test!(test_cycle_path_len_gt_1, G);
    common_test!(test_multiple_paths_would_cycle, G);
}

mod stable_graph {
    // mod directed {
    //
    // }
    use petgraph::prelude::*;
    type G = StableDiGraph<char, usize>;

    common_test!(test_cycle_check_enabled, G);
    common_test!(test_cycle_check_disabled, G);
    common_test!(test_empty_nodes, G);
    common_test!(test_unknown_nodes, G);
    common_test!(test_cycle_path_len_gt_1, G);
    common_test!(test_multiple_paths_would_cycle, G);
}

///          ┌─┐                         ┌─┐
///        ┌─┤a│               ┌─────────┤m│
///        │ └─┘               │         └▲┘
///       ┌▼┐                 ┌▼┐         │
///       │b│          ───►   │b├─────────┘
///       └┬┘                 └─┘
///        │  ┌─┐
///        └─►┤c│
///           └─┘
pub fn test_cycle_check_enabled<G>()
where
    G: Default
        + Data<NodeWeight = char, EdgeWeight = usize>
        + Build
        + ContractNodesDirected<Error = ContractError>,
    G::NodeId: Debug,
{
    let mut dag = G::default();
    let a = dag.add_node('a');
    let b = dag.add_node('b');
    let c = dag.add_node('c');
    dag.add_edge(a, b, 1);
    dag.add_edge(b, c, 2);
    let result = dag.contract_nodes([a, c], 'm', true);
    match result.expect_err("Cycle should cause return error.") {
        ContractError::DAGWouldCycle => (),
    }
}

fn test_cycle_check_disabled<G>()
where
    G: Default
        + Data<NodeWeight = char, EdgeWeight = usize>
        + Build
        + ContractNodesDirected<Error = ContractError>,
    G::NodeId: Debug,
{
    let mut dag = G::default();
    let a = dag.add_node('a');
    let b = dag.add_node('b');
    let c = dag.add_node('c');
    dag.add_edge(a, b, 1);
    dag.add_edge(b, c, 2);
    let result = dag.contract_nodes([a, c], 'm', false);
    result.expect("No error should be raised for a cycle when cycle check is disabled.");
}

fn test_empty_nodes<G>()
where
    G: Default
        + Data<NodeWeight = char, EdgeWeight = usize>
        + Build
        + ContractNodesDirected<Error = ContractError>,
    G::NodeId: Debug,
{
    let mut dag = G::default();
    dag.contract_nodes([], 'm', false).unwrap();
    assert_eq!(dag.node_count(), 1);
}

fn test_unknown_nodes<G>()
where
    G: Default
        + Data<NodeWeight = char, EdgeWeight = usize>
        + Build
        + ContractNodesDirected<Error = ContractError>
        + NodeRemovable,
    G::NodeId: Debug + Copy,
{
    let mut dag = G::default();

    // A -> B -> C
    let a = dag.add_node('a');
    let b = dag.add_node('b');
    let c = dag.add_node('c');

    dag.add_edge(a, b, 1);
    dag.add_edge(b, c, 2);

    // Leave just A.
    dag.remove_node(b);
    dag.remove_node(c);

    // Replacement should ignore the unknown nodes, making
    // the behavior equivalent to adding a new node in
    // this case.
    dag.contract_nodes([b, c], 'm', false).unwrap();
    assert_eq!(dag.node_count(), 2);
}

///           ┌─┐              ┌─┐
///        ┌4─┤a├─1┐           │m├──1───┐
///        │  └─┘  │           └▲┘      │
///       ┌▼┐     ┌▼┐           │      ┌▼┐
///       │d│     │b│   ───►    │      │b│
///       └▲┘     └┬┘           │      └┬┘
///        │  ┌─┐  2            │  ┌─┐  2
///        └3─┤c│◄─┘            └3─┤c│◄─┘
///           └─┘                  └─┘
fn test_cycle_path_len_gt_1<G>()
where
    G: Default
        + Data<NodeWeight = char, EdgeWeight = usize>
        + Build
        + ContractNodesDirected<Error = ContractError>
        + NodeRemovable,
    G::NodeId: Debug + Copy,
{
    let mut dag = G::default();
    let a = dag.add_node('a');
    let b = dag.add_node('b');
    let c = dag.add_node('c');
    let d = dag.add_node('d');
    dag.add_edge(a, b, 1);
    dag.add_edge(b, c, 2);
    dag.add_edge(c, d, 3);
    dag.add_edge(a, d, 4);

    dag.contract_nodes([a, d], 'm', true)
        .expect_err("Cycle should be detected.");
}

///           ┌─┐     ┌─┐                  ┌─┐     ┌─┐
///        ┌3─┤c│     │e├─5┐            ┌──┤c│     │e├──┐
///        │  └▲┘     └▲┘  │            │  └▲┘     └▲┘  │
///       ┌▼┐  2  ┌─┐  4  ┌▼┐           │   2  ┌─┐  4   │
///       │d│  └──┤b├──┘  │f│   ───►    │   └──┤b├──┘   │
///       └─┘     └▲┘     └─┘           3      └▲┘      5
///                1                    │       1       │
///               ┌┴┐                   │      ┌┴┐      │
///               │a│                   └─────►│m│◄─────┘
///               └─┘                          └─┘
fn test_multiple_paths_would_cycle<G>()
where
    G: Default
        + Data<NodeWeight = char, EdgeWeight = usize>
        + Build
        + ContractNodesDirected<Error = ContractError>,
    for<'b> &'b G: GraphBase<NodeId = G::NodeId>
        + Data<EdgeWeight = G::EdgeWeight>
        + IntoEdgeReferences
        + IntoNodeIdentifiers,
    G::NodeId: Eq + Hash + Debug + Copy,
{
    let mut dag = G::default();
    let a = dag.add_node('a');
    let b = dag.add_node('b');
    let c = dag.add_node('c');
    let d = dag.add_node('d');
    let e = dag.add_node('e');
    let f = dag.add_node('f');

    dag.add_edge(a, b, 1);
    dag.add_edge(b, c, 2);
    dag.add_edge(c, d, 3);
    dag.add_edge(b, e, 4);
    dag.add_edge(e, f, 5);

    let result = dag.contract_nodes([a, d, f], 'm', true);
    match result.expect_err("Cycle should cause return error.") {
        ContractError::DAGWouldCycle => (),
    }

    // Proceed, ignoring cycles.
    let m = dag
        .contract_nodes([a, d, f], 'm', false)
        .expect("Contraction should be allowed without cycle check.");

    assert_eq!(
        HashSet::from([b, c, e, m]),
        dag.node_identifiers().collect::<HashSet<_>>()
    );

    let expected_edges = HashSet::from([(b, c, 2), (c, m, 3), (e, m, 5), (b, e, 4), (m, b, 1)]);

    assert_eq!(
        expected_edges,
        dag.edge_references()
            .map(|e| (e.source(), e.target(), *e.weight()))
            .collect::<HashSet<_>>()
    );
}

//       self.assertEqual(
//           {
//               (node_b, node_c),
//               (node_c, node_m),
//               (node_e, node_m),
//               (node_b, node_e),
//               (node_m, node_b),
//           },
//           set(dag.edge_list()),
//       )
//
//   def test_replace_node_no_neighbors(self):
//       dag = rustworkx.PyDAG()
//       node_a = dag.add_node("a")
//       node_m = dag.contract_nodes([node_a], "m", check_cycle=True)
//       self.assertEqual([node_m], dag.node_indexes())
//       self.assertEqual(set(), set(dag.edge_list()))
//
//   def test_keep_edges_multigraph(self):
//       """
//          ┌─┐            ┌─┐
//        ┌─┤a│◄┐        ┌─┤a│◄┐
//        │ └─┘ │        │ └─┘ │
//        1     2   ──►  1     2
//       ┌▼┐   ┌┴┐       │ ┌─┐ │
//       │b│   │c│       └►│m├─┘
//       └─┘   └─┘         └─┘
//       """
//       dag = rustworkx.PyDiGraph()
//       node_a = dag.add_node("a")
//       node_b = dag.add_node("b")
//       node_c = dag.add_node("c")
//
//       dag.add_edge(node_a, node_b, 1)
//       dag.add_edge(node_c, node_a, 2)
//
//       with self.assertRaises(rustworkx.DAGWouldCycle):
//           dag.contract_nodes([node_b, node_c], "m", check_cycle=True)
//
//       # Proceed, ignoring cycles.
//       node_m = dag.contract_nodes([node_b, node_c], "m")
//       self.assertEqual([node_a, node_m], dag.node_indexes())
//       self.assertEqual(
//           {(node_a, node_m, 1), (node_m, node_a, 2)},
//           set(dag.weighted_edge_list()),
//       )
//
//
//lass TestContractNodesSimpleGraph(unittest.TestCase):
//   def setUp(self):
//       super().setUp()
//       self.dag = rustworkx.PyDAG(multigraph=False)
//       self.node_a = self.dag.add_node("a")
//       self.node_b = self.dag.add_child(self.node_a, "b", 1)
//       self.node_c = self.dag.add_child(self.node_a, "c", 2)
//       self.node_d = self.dag.add_child(self.node_a, "d", 3)
//       self.node_e = self.dag.add_node("e")
//       self.dag.add_edge(self.node_b, self.node_e, 4)
//       self.dag.add_edge(self.node_c, self.node_e, 5)
//       self.dag.add_edge(self.node_d, self.node_e, 6)
//
//   def test_collapse_parallel_edges_no_combo_fn(self):
//       """
//       Parallel edges are collapsed arbitrarily when weight_combo_fn is None.
//           ┌─┐               ┌─┐
//           │a│               │a│
//        ┌──┴┬┴──┐            └┬┘
//        1   2   3        1 or 2 or 3
//       ┌▼┐ ┌▼┐ ┌▼┐           ┌▼┐
//       │b│ │c│ │d│   ──►     │m│
//       └┬┘ └┬┘ └┬┘           └┬┘
//        4   5   6        4 or 5 or 6
//        └──►▼◄──┘            ┌▼┐
//           │e│               │e│
//           └─┘               └─┘
//       """
//       self.dag.contract_nodes([self.node_b, self.node_c, self.node_d], "m")
//
//       self.assertEqual(set(self.dag.nodes()), {"a", "e", "m"})
//       self.assertEqual(len(self.dag.edges()), 2)
//
//       # Should have one incoming edge, one outgoing
//       self.assertTrue(any(e in self.dag.edges() for e in {1, 2, 3}))
//       self.assertTrue(any(e in self.dag.edges() for e in {4, 5, 6}))
//
//   def test_collapse_parallel_edges(self):
//       """
//       Parallel edges are collapsed using weight_combo_fn.
//           ┌─┐               ┌─┐
//           │a│               │a│
//        ┌──┴┬┴──┐            └┬┘
//        1   2   3             6
//       ┌▼┐ ┌▼┐ ┌▼┐           ┌▼┐
//       │b│ │c│ │d│   ──►     │m│
//       └┬┘ └┬┘ └┬┘           └┬┘
//        4   5   6             15
//        └──►▼◄──┘            ┌▼┐
//           │e│               │e│
//           └─┘               └─┘
//       """
//       self.dag.contract_nodes(
//           [self.node_b, self.node_c, self.node_d],
//           "m",
//           weight_combo_fn=lambda w1, w2: w1 + w2,
//       )
//
//       self.assertEqual(set(self.dag.nodes()), {"a", "e", "m"})
//       self.assertEqual(len(self.dag.edges()), 2)
//
//       # Should have one incoming edge, one outgoing
//       self.assertEqual(set(self.dag.edges()), {6, 15})
//
//   def test_replace_all_nodes(self):
//       self.dag.contract_nodes(self.dag.node_indexes(), "m")
//       self.assertEqual(set(self.dag.nodes()), {"m"})
//       self.assertFalse(self.dag.edges())
