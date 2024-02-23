// Licensed under the Apache License, Version 2.0 (the "License"); you may
// not use this file except in compliance with the License. You may obtain
// a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.

//! This module defines graph traits for node contraction.

use crate::dictmap::{DictMap, InitWithHasher};
use crate::graph::NodeRemovable;
use crate::RxError;
use indexmap::map::Entry::{Occupied, Vacant};
use indexmap::IndexSet;
use petgraph::data::Build;
use petgraph::visit::{
    Data, Dfs, EdgeRef, GraphBase, GraphProp, IntoEdges, IntoEdgesDirected, Visitable,
};
use petgraph::{Directed, Direction, Undirected};
use std::hash::Hash;
use std::ops::Deref;

fn merge_duplicates<K, V, F, E>(xs: Vec<(K, V)>, mut merge_fn: F) -> Result<Vec<(K, V)>, E>
where
    K: Hash + Eq,
    F: FnMut(&V, &V) -> Result<V, E>,
{
    let mut kvs = DictMap::with_capacity(xs.len());
    for (k, v) in xs {
        match kvs.entry(k) {
            Occupied(entry) => {
                *entry.into_mut() = merge_fn(&v, entry.get())?;
            }
            Vacant(entry) => {
                entry.insert(v);
            }
        }
    }
    Ok(kvs.into_iter().collect::<Vec<_>>())
}

pub trait ContractNodesDirected: Data {
    /// Substitute a set of nodes with a single new node.
    ///
    /// The specified `nodes` are removed and replaced with a new node
    /// with the given `weight`. Any nodes not in the graph are ignored.
    /// It is valid for `nodes` to be empty, in which case the new node
    /// is added to the graph without edges.
    ///
    /// By default, contraction will *attempt* to introduce parallel edges
    /// when more than one edge exists between the same node external to
    /// `nodes` and more than one node inside of it.
    /// If this is not desired (e.g. the graph is not a multi-graph),
    /// specify `weight_combo_fn` to merge the would-be parallel edges.
    ///
    /// If `check_cycle` is enabled and the contraction would introduce
    /// a cycle, an error is returned and the graph is not modified.
    ///
    /// The `NodeId` of the newly created node is returned.
    ///
    /// # Example
    /// ```
    /// todo!()
    /// ```
    fn contract_nodes<I, F, E>(
        &mut self,
        nodes: I,
        weight: Self::NodeWeight,
        check_cycle: bool,
        weight_combo_fn: Option<F>,
    ) -> Result<Self::NodeId, RxError<E>>
    where
        I: IntoIterator<Item = Self::NodeId>,
        F: FnMut(&Self::EdgeWeight, &Self::EdgeWeight) -> Result<Self::EdgeWeight, E>;
}

impl<G> ContractNodesDirected for G
where
    G: GraphProp<EdgeType = Directed> + NodeRemovable + Build + Visitable,
    for<'b> &'b G:
        GraphBase<NodeId = G::NodeId> + Data<EdgeWeight = G::EdgeWeight> + IntoEdgesDirected,
    G::NodeId: Eq + Hash,
    G::EdgeWeight: Clone,
{
    fn contract_nodes<I, F, E>(
        &mut self,
        nodes: I,
        obj: Self::NodeWeight,
        check_cycle: bool,
        weight_combo_fn: Option<F>,
    ) -> Result<Self::NodeId, RxError<E>>
    where
        I: IntoIterator<Item = Self::NodeId>,
        F: FnMut(&Self::EdgeWeight, &Self::EdgeWeight) -> Result<Self::EdgeWeight, E>,
    {
        let can_contract = |nodes: &IndexSet<G::NodeId, ahash::RandomState>| {
            // Start with successors of `nodes` that aren't in `nodes` itself.
            let visit_next: Vec<G::NodeId> = nodes
                .iter()
                .flat_map(|n| self.edges(*n))
                .filter_map(|edge| {
                    let target_node = edge.target();
                    if !nodes.contains(&target_node) {
                        Some(target_node)
                    } else {
                        None
                    }
                })
                .collect();

            // Now, if we can reach any of `nodes`, there exists a path from `nodes`
            // back to `nodes` of length > 1, meaning contraction is disallowed.
            let mut dfs = Dfs::from_parts(visit_next, self.visit_map());
            while let Some(node) = dfs.next(self.deref()) {
                if nodes.contains(&node) {
                    // we found a path back to `nodes`
                    return false;
                }
            }
            true
        };

        let mut indices_to_remove: IndexSet<G::NodeId, ahash::RandomState> =
            IndexSet::from_iter(nodes);

        if check_cycle && !can_contract(&indices_to_remove) {
            return Err(RxError::DAGWouldCycle);
        }

        // Create new node.
        let node_index = self.add_node(obj);

        // Sanitize new node index from user input.
        indices_to_remove.swap_remove(&node_index);

        // Determine edges for new node.
        let mut incoming_edges: Vec<(Self::NodeId, Self::EdgeWeight)> = indices_to_remove
            .iter()
            .flat_map(|i| self.edges_directed(*i, Direction::Incoming))
            .filter_map(|edge| {
                let pred = edge.source();
                if !indices_to_remove.contains(&pred) {
                    Some((pred, edge.weight().clone()))
                } else {
                    None
                }
            })
            .collect();

        let mut outgoing_edges: Vec<(Self::NodeId, Self::EdgeWeight)> = indices_to_remove
            .iter()
            .flat_map(|&i| self.edges_directed(i, Direction::Outgoing))
            .filter_map(|edge| {
                let succ = edge.target();
                if !indices_to_remove.contains(&succ) {
                    Some((succ, edge.weight().clone()))
                } else {
                    None
                }
            })
            .collect();

        // Remove nodes that will be replaced.
        for index in indices_to_remove {
            self.remove_node(index);
        }

        // If `weight_combo_fn` was specified, merge edges according
        // to that function. If unspecified, defer parallel edge handling
        // to `add_edge`.
        if let Some(mut merge_fn) = weight_combo_fn {
            incoming_edges = merge_duplicates(incoming_edges, &mut merge_fn)?;
            outgoing_edges = merge_duplicates(outgoing_edges, &mut merge_fn)?;
        }

        for (source, weight) in incoming_edges.into_iter() {
            self.add_edge(source, node_index, weight);
        }

        for (target, weight) in outgoing_edges.into_iter() {
            self.add_edge(node_index, target, weight);
        }

        Ok(node_index)
    }
}

pub trait ContractNodesUndirected: Data {
    /// Substitute a set of nodes with a single new node.
    ///
    /// The specified `nodes` are removed and replaced with a new node
    /// with the given `weight`. Any nodes not in the graph are ignored.
    /// It is valid for `nodes` to be empty, in which case the new node
    /// is added to the graph without edges.
    ///
    /// By default, contraction will *attempt* to introduce parallel edges
    /// when more than one edge exists between the same node external to
    /// `nodes` and more than one node inside of it.
    /// If this is not desired (e.g. the graph is not a multi-graph),
    /// specify `weight_combo_fn` to merge the would-be parallel edges.
    ///
    /// The `NodeId` of the newly created node is returned.
    ///
    /// # Example
    /// ```
    /// todo!()
    /// ```
    fn contract_nodes<I, F, E>(
        &mut self,
        nodes: I,
        weight: Self::NodeWeight,
        weight_combo_fn: Option<F>,
    ) -> Result<Self::NodeId, RxError<E>>
    where
        I: IntoIterator<Item = Self::NodeId>,
        F: FnMut(&Self::EdgeWeight, &Self::EdgeWeight) -> Result<Self::EdgeWeight, E>;
}

impl<G> ContractNodesUndirected for G
where
    G: GraphProp<EdgeType = Undirected> + NodeRemovable + Build + Visitable,
    for<'b> &'b G:
        GraphBase<NodeId = G::NodeId> + Data<EdgeWeight = G::EdgeWeight> + IntoEdgesDirected,
    G::NodeId: Eq + Hash,
    G::EdgeWeight: Clone,
{
    fn contract_nodes<I, F, E>(
        &mut self,
        nodes: I,
        obj: Self::NodeWeight,
        weight_combo_fn: Option<F>,
    ) -> Result<Self::NodeId, RxError<E>>
    where
        I: IntoIterator<Item = Self::NodeId>,
        F: FnMut(&Self::EdgeWeight, &Self::EdgeWeight) -> Result<Self::EdgeWeight, E>,
    {
        let mut indices_to_remove: IndexSet<G::NodeId, ahash::RandomState> =
            IndexSet::from_iter(nodes);

        // Create new node.
        let node_index = self.add_node(obj);

        // Sanitize new node index from user input.
        indices_to_remove.swap_remove(&node_index);

        // Determine edges for new node.
        // note: `edges_directed` returns all edges with `i` as
        // an endpoint. `Direction::Incoming` configures `edge.target()`
        // to return `i` and `edge.source()` to return the other node.
        let mut edges: Vec<(Self::NodeId, Self::EdgeWeight)> = indices_to_remove
            .iter()
            .flat_map(|i| self.edges_directed(*i, Direction::Incoming))
            .filter_map(|edge| {
                let pred = edge.source();
                if !indices_to_remove.contains(&pred) {
                    Some((pred, edge.weight().clone()))
                } else {
                    None
                }
            })
            .collect();

        // Remove nodes that will be replaced.
        for index in indices_to_remove {
            self.remove_node(index);
        }

        // If `weight_combo_fn` was specified, merge edges according
        // to that function, even if this is a multigraph. If unspecified,
        // defer parallel edge handling to `add_edge`.
        if let Some(mut merge_fn) = weight_combo_fn {
            edges = merge_duplicates(edges, &mut merge_fn)?;
        }

        for (source, weight) in edges {
            self.add_edge(source, node_index, weight);
        }

        Ok(node_index)
    }
}
