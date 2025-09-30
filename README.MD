# Obsidian Backup System

A Git-based backup library for Rust applications. Originally designed for the Obsidian Minecraft Server Panel, but generic enough to be used in any project requiring file backup management.

This library uses Git under the hood to provide efficient, version-controlled backups with diff capabilities.

## Features

- 🔄 **Create backups** - Snapshot your files and directories using Git commits
- 📋 **List backups** - View all available backup points with timestamps and descriptions
- ⏮️ **Restore backups** - Roll back to any previous backup state
- 🔍 **Diff backups** - See exactly what changed between backup points
- 📦 **Export backups** - Create compressed archives (7z) from any backup (requires `zip` feature)
- 🏷️ **Backup descriptions** - Add meaningful descriptions to track what each backup represents
- ⚡ **Efficient storage** - Leverages Git's delta compression for space-efficient storage
- 🔧 **Optional features** - Enable only the functionality you need

## Installation

This crate is not yet published on crates.io. To use it, add the following to your `Cargo.toml`:

```toml
[dependencies]
obsidian_backup_system = { git = "https://github.com/Obsidian-Minecraft-Server-Portal/obsidian-backup-system.git" }
```

### With Optional Features

```toml
[dependencies]
obsidian_backup_system = { git = "https://github.com/Obsidian-Minecraft-Server-Portal/obsidian-backup-system.git", features = ["serde", "logging", "zip"] }
```

## Available Features

| Feature   | Description                                                    | Dependencies                              |
|-----------|----------------------------------------------------------------|-------------------------------------------|
| `serde`   | Enables serialization/deserialization support for backup items | `serde`                                   |
| `logging` | Enables internal logging using the `log` crate                 | `log`                                     |
| `zip`     | Enables exporting backups as 7z compressed archives            | `sevenz-rust2`                            |
| `cli`     | Builds the command-line interface application                  | `clap`, `serde_json`, `pretty_env_logger` |

## Basic Usage

### Initialize BackupManager

```rust
use obsidian_backup_system::BackupManager;

// Create a backup manager
// store_directory: where backup metadata is stored (.git repository)
// working_directory: the directory you want to back up
let manager = BackupManager::new("./backups", "./my_data")
.expect("Failed to initialize BackupManager");
```

### Create a Backup

```rust
// Create a backup without description
let backup_id = manager.backup(None)
.expect("Failed to create backup");
println!("Created backup with ID: {}", backup_id);

// Create a backup with description
let backup_id = manager.backup(Some("Before major update".to_string()))
.expect("Failed to create backup");
```

### List All Backups

```rust
let backups = manager.list()
.expect("Failed to list backups");

for backup in backups {
    println!("ID: {}", backup.id);
    println!("Timestamp: {}", backup.timestamp);
    println!("Description: {}", backup.description);
    println!("---");
}
```

### Get Most Recent Backup

```rust
if let Some(last_backup) = manager.last().expect("Failed to get last backup") {
    println!("Last backup: {}", last_backup.description);
    println!("Created at: {}", last_backup.timestamp);
} else {
    println!("No backups found");
}
```

### Restore a Backup

```rust
// Restore using backup ID
manager.restore( & backup_id)
.expect("Failed to restore backup");
```

### View Changes (Diff)

```rust
// Get differences between a backup and its parent
let modified_files = manager.diff( & backup_id)
.expect("Failed to get diff");

for file in modified_files {
    println!("File: {}", file.path);
    
    match ( &file.content_before, &file.content_after) {
        (Some(_), Some(_)) => println ! ("  Modified"),
        (None, Some(_)) => println ! ("  Added"),
        (Some(_), None) => println ! ("  Deleted"),
        _ => {}
    }
}
```

### Export Backup as Archive (requires `zip` feature)

```rust
#[cfg(feature = "zip")]
{
    // Export a backup as a 7z archive
    // compression_level: 0-9 (0 = no compression, 9 = maximum compression)
    manager.export( & backup_id, "./backup.7z", 5)
    .expect("Failed to export backup");
}
```

## Complete Example

```rust
use obsidian_backup_system::BackupManager;
use std::fs;

fn main() -> anyhow::Result<()> {
	// Initialize directories
	fs::create_dir_all("./backups")?;
	fs::create_dir_all("./my_data")?;

	// Create some content
	fs::write("./my_data/file.txt", "Initial content")?;

	// Initialize backup manager
	let manager = BackupManager::new("./backups", "./my_data")?;

	// Create first backup
	let backup1 = manager.backup(Some("Initial state".to_string()))?;
	println!("Created backup: {}", backup1);

	// Modify content
	fs::write("./my_data/file.txt", "Modified content")?;

	// Create second backup
	let backup2 = manager.backup(Some("After modifications".to_string()))?;

	// View changes
	let diffs = manager.diff(&backup2)?;
	println!("\nChanges in last backup:");
	for diff in diffs {
		println!("  {}: modified", diff.path);
	}

	// List all backups
	println!("\nAll backups:");
	for backup in manager.list()? {
		println!("  {}: {}", backup.timestamp, backup.description);
	}

	// Restore first backup
	manager.restore(&backup1)?;
	println!("\nRestored to initial state");

	Ok(())
}
```

## With Logging (requires `logging` feature)

```rust
#[cfg(feature = "logging")]
use log::{info, LevelFilter};

#[cfg(feature = "logging")]
fn main() {
	// Initialize logger
	pretty_env_logger::env_logger::builder()
		.filter_level(LevelFilter::Debug)
		.init();

	let manager = BackupManager::new("./backups", "./my_data")
		.expect("Failed to create BackupManager");

	info!("Creating backup...");
	let backup_id = manager.backup(Some("Logged backup".to_string()))
	                       .expect("Failed to create backup");
	info!("Backup created: {}", backup_id);
}
```

## API Reference

### `BackupManager`

The main struct for managing backups.

#### Methods

- `new(store_directory, working_directory) -> Result<Self>` - Initialize a new backup manager
- `backup(description: Option<String>) -> Result<String>` - Create a new backup, returns backup ID
- `list() -> Result<Vec<BackupItem>>` - List all available backups
- `last() -> Result<Option<BackupItem>>` - Get the most recent backup
- `restore(backup_id: impl AsRef<str>) -> Result<()>` - Restore a specific backup
- `diff(backup_id: impl AsRef<str>) -> Result<Vec<ModifiedFile>>` - Get changes in a backup
- `export(backup_id, output_path, level: u8) -> Result<()>` - Export backup as 7z archive (requires `zip` feature)

### `BackupItem`

Represents a backup point with metadata.

```rust
pub struct BackupItem {
	pub id: String,                    // Git commit ID
	pub timestamp: DateTime<Utc>,      // When the backup was created
	pub description: String,           // User-provided description
}
```

### `ModifiedFile`

Represents a file that changed in a backup.

```rust
pub struct ModifiedFile {
	pub path: String,                  // Path to the file
	pub content_before: Option<Vec<u8>>, // Content before change (None if added)
	pub content_after: Option<Vec<u8>>,  // Content after change (None if deleted)
}
```

## Contributing

Contributions are welcome! Please feel free to submit issues or pull requests.