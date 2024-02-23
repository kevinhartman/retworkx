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
pub enum RxError<E> {
    BadArgument(String),
    CallbackFailure { error: E },
    DAGWouldCycle,
}

impl<E: Display> Display for RxError<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match *self {
            RxError::BadArgument(ref reason) => write!(f, "Invalid argument: {}", reason),
            RxError::CallbackFailure { ref error } => write!(f, "Callback error: {}", error),
            RxError::DAGWouldCycle => write!(f, "The operation would introduce a cycle."),
        }
    }
}

impl<E: Debug + Display> Error for RxError<E> {}

impl<E> From<E> for RxError<E> {
    fn from(err: E) -> RxError<E> {
        RxError::CallbackFailure { error: err }
    }
}
