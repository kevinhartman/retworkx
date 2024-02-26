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

//! This module defines the common error type.

use std::error::Error;
use std::fmt::{Debug, Display, Formatter};

/// The common error type.
#[derive(Debug)]
pub enum RxError<N, E, C> {
    NodeId(N),
    EdgeId(E),
    Callback(C),
    DAGWouldCycle,
}

impl<N, E, C> From<C> for RxError<N, E, C> {
    fn from(value: C) -> Self {
        RxError::Callback(value)
    }
}

impl<N: Debug, E: Debug, C: Debug> Display for RxError<N, E, C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match *self {
            RxError::NodeId(ref n) => write!(f, "Node index not found in graph: {:?}", n),
            RxError::EdgeId(ref n) => write!(f, "Node edge not found in graph: {:?}", n),
            RxError::Callback(ref error) => write!(f, "Callback error: {:?}", error),
            RxError::DAGWouldCycle => write!(f, "The operation would introduce a cycle."),
        }
    }
}

impl<N: Debug, E: Debug, C: Debug> Error for RxError<N, E, C> {}
