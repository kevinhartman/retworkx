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

//! # rustworkx-core
//!
//! rustworkx-core is a graph algorithm crate built on top of [`petgraph`]. It offers
//! a set of functions that are used in the larger rustworkx project but
//! implemented in a generic manner for use by downstream rust projects.
//!
//! ## Usage
//!
//! First add this crate to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rustworkx-core = "0.11"
//! ```
//!
//! Then in your code, it may be used something like this:
//!
//! ```rust
//! use rustworkx_core::petgraph;
//! use rustworkx_core::centrality::betweenness_centrality;
//!
//! let g = petgraph::graph::UnGraph::<i32, ()>::from_edges(&[
//!     (1, 2), (2, 3), (3, 4), (1, 4)
//! ]);
//! // Calculate the betweenness centrality
//! let output = betweenness_centrality(&g, false, false, 200);
//! assert_eq!(
//!     vec![Some(0.0), Some(0.5), Some(0.5), Some(0.5), Some(0.5)],
//!     output
//! );
//! ```
//!
//! ## Algorithm Modules
//!
//! The crate is organized into
//!
//! * [`centrality`](./centrality/index.html)
//! * [`connectivity`](./connectivity/index.html)
//! * [`max_weight_matching`](./max_weight_matching/index.html)
//! * [`shortest_path`](./shortest_path/index.html)
//! * [`token_swapper`](./token_swapper/index.html)
//! * [`traversal`](./traversal/index.html)
//! * [`generators`](./generators/index.html)
//!
//! ## Release Notes
//!
//! The release notes for rustworkx-core are included as part of the rustworkx
//! documentation which is hosted at:
//!
//! <https://www.rustworkx.org/release_notes.html>

use std::convert::Infallible;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};

use petgraph::graph::IndexType;
use petgraph::stable_graph::StableGraph;
use petgraph::visit::Data;
use petgraph::{EdgeType, Graph};

/// A convenient type alias that by default assumes no error can happen.
///
/// It can be used to avoid type annotations when the function you want
/// to use needs a callback that returns [`Result`] but in your case no
/// error can happen.
pub type Result<T, E = Infallible> = core::result::Result<T, E>;

pub mod bipartite_coloring;
/// Module for centrality algorithms.
pub mod centrality;
/// Module for coloring algorithms.
pub mod coloring;
pub mod connectivity;
pub mod generators;
pub mod line_graph;

/// Module for maximum weight matching algorithms.
pub mod max_weight_matching;
pub mod planar;
pub mod shortest_path;
pub mod traversal;
// These modules define additional data structures
pub mod dictmap;
pub mod distancemap;
pub mod graph_ext;
mod min_scored;
/// Module for swapping tokens
pub mod token_swapper;
pub mod utils;

// re-export petgraph so there is a consistent version available to users and
// then only need to require rustworkx-core in their dependencies
pub use petgraph;
use petgraph::graphmap::{GraphMap, NodeTrait};
use petgraph::matrix_graph::{MatrixGraph, Nullable};

/// The error type returned by Rustworkx core.
#[derive(Debug)]
pub enum RxError<E> {
    InvalidArgument(String),
    CallbackFailure { error: E },
}

impl<E: Display> Display for RxError<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match *self {
            RxError::InvalidArgument(ref reason) => write!(f, "Invalid argument: {}", reason),
            RxError::CallbackFailure { ref error } => write!(f, "Callback error: {}", error),
        }
    }
}

impl<E: Debug + Display> Error for RxError<E> {}

impl<E> From<E> for RxError<E> {
    fn from(err: E) -> RxError<E> {
        RxError::CallbackFailure { error: err }
    }
}

/// A graph whose nodes may be removed.
pub trait NodeRemovable: Data {
    type ReturnType;
    fn remove_node(&mut self, node: Self::NodeId) -> Self::ReturnType;
}

impl<N, E, Ty, Ix> NodeRemovable for StableGraph<N, E, Ty, Ix>
where
    Ty: EdgeType,
    Ix: IndexType,
{
    type ReturnType = Option<Self::NodeWeight>;
    fn remove_node(&mut self, node: Self::NodeId) -> Option<Self::NodeWeight> {
        self.remove_node(node)
    }
}

impl<N, E, Ty, Ix> NodeRemovable for Graph<N, E, Ty, Ix>
where
    Ty: EdgeType,
    Ix: IndexType,
{
    type ReturnType = Option<Self::NodeWeight>;
    fn remove_node(&mut self, node: Self::NodeId) -> Option<Self::NodeWeight> {
        self.remove_node(node)
    }
}

impl<N, E, Ty> NodeRemovable for GraphMap<N, E, Ty>
where
    N: NodeTrait,
    Ty: EdgeType,
{
    type ReturnType = bool;
    fn remove_node(&mut self, node: Self::NodeId) -> Self::ReturnType {
        self.remove_node(node)
    }
}

impl<N, E, Ty: EdgeType, Null: Nullable<Wrapped = E>, Ix: IndexType> NodeRemovable
    for MatrixGraph<N, E, Ty, Null, Ix>
{
    type ReturnType = Self::NodeWeight;

    fn remove_node(&mut self, node: Self::NodeId) -> Self::ReturnType {
        self.remove_node(node)
    }
}
