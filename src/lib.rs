#![doc = include_str!("../README.md")]
pub mod data;

#[cfg(feature = "cli")]
mod cli;

pub(crate) mod log_stub;
mod actions;

pub use actions::BackupManager;