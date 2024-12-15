//! Configuration for swc

pub mod config_types;
pub mod merge;
mod module;
#[cfg(feature = "sourcemap")]
mod source_map;

pub use swc_cached::{Error, regex::CachedRegex};

pub use crate::module::IsModule;
#[cfg(feature = "sourcemap")]
pub use crate::source_map::*;
