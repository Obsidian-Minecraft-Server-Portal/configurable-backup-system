#![doc = include_str!("../README.md")]
pub mod data;

#[cfg(feature = "cli")]
mod cli;
pub mod backup_manager;

pub(crate) mod log_stub;