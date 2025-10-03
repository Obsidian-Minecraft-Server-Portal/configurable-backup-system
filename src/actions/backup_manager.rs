//! `BackupManager` is responsible for managing backup operations within a Git-based
//! storage mechanism. It provides functionality to initialize a backup repository,
//! create new backups, list existing backups, restore backups, and export backups
//! as compressed archives.
//!
//! # Examples
//!
//! ```rust
//! use obsidian_backup_system::BackupManager;
//!
//! let store_dir = "./backup_store";
//! let working_dir = "./my_data";
//! let backup_manager = BackupManager::new(store_dir, working_dir)
//!     .expect("Failed to initialize BackupManager");
//! ```
//!
//! # Fields
//!
//! * `repository` - The Git repository used for managing backups.
use crate::data::backup_item::BackupItem;
use crate::data::modified_file::ModifiedFile;
use crate::log_stub::*;
use anyhow::{anyhow, Result};
use git2::{Oid, Repository, RepositoryInitOptions};
use ignore::gitignore::{Gitignore, GitignoreBuilder};
#[cfg(feature = "zip")]
use sevenz_rust2::{encoder_options, ArchiveWriter};
use std::fs;
use std::path::Path;

/// `BackupManager` is a struct responsible for managing backup operations.
///
/// This struct serves as a core component for creating, storing, and retrieving backups
/// in the system. It encapsulates the `Repository` where backup data is managed,
/// providing an interface to interact with the underlying repository for backup-related tasks.
///
/// # Fields
/// - `repository`: The repository where backup data is stored and managed.
///
/// # Example
/// ```rust
/// use obsidian_backup_system::BackupManager;
///
/// let backup_manager = BackupManager::new("./backup_store", "./my_data")
///     .expect("Failed to create BackupManager");
/// ```
pub struct BackupManager {
    repository: Repository,
    ignore_matcher: Option<Gitignore>,
}

impl BackupManager {
    /// Helper function to check if a path should be excluded from backups using ignore patterns in `exclude.obak`
    fn should_exclude(&self, path: &Path, is_dir: bool) -> bool {
        // Always skip the Git metadata directory and common junk files
        if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
            if name == ".git"
                || matches!(
                    name,
                    ".DS_Store"
                        | "Thumbs.db"
                        | "desktop.ini"
                        | ".Spotlight-V100"
                        | ".Trashes"
                        | "ehthumbs.db"
                        | "ehthumbs_vista.db"
                        | "$RECYCLE.BIN"
                )
                || name.starts_with("~$")
                || name.ends_with(".tmp")
                || name.ends_with(".swp")
                || name.ends_with("~")
                || name == "__pycache__"
            {
                return true;
            }
        }

        if let Some(matcher) = &self.ignore_matcher {
            let m = matcher.matched(path, is_dir);
            if m.is_ignore() {
                return true;
            }
        }
        false
    }

    /// Helper function to recursively add files from a directory to the git index
    #[allow(clippy::only_used_in_recursion)]
    fn add_directory_to_index(
        &self,
        index: &mut git2::Index,
        dir_path: &Path,
        base_path: &Path,
    ) -> Result<()> {
        for entry in fs::read_dir(dir_path)? {
            let entry = entry?;
            let path = entry.path();

            let file_type = entry.file_type()?;

            // Skip excluded files and directories
            if self.should_exclude(&path, file_type.is_dir()) {
                debug!("Skipping excluded path: {:?}", path);
                continue;
            }

            if file_type.is_dir() {
                // Recursively add subdirectory
                self.add_directory_to_index(index, &path, base_path)?;
            } else if file_type.is_file() {
                // Calculate relative path from base_path
                let relative_path = path.strip_prefix(base_path)?;
                debug!("Adding file to index: {:?}", relative_path);
                index.add_path(relative_path)?;
            }
        }
        Ok(())
    }

    /// Creates a new instance of `BackupManager`.
    ///
    /// This function initializes a `BackupManager` by setting up a new Git repository
    /// in the specified `store_directory` with the specified `working_directory` as
    /// the working directory for the repository.
    ///
    /// # Arguments
    ///
    /// * `store_directory` - A reference to a path where the repository data will be stored.
    /// * `working_directory` - A reference to a path that will serve as the working directory for the repository.
    ///
    /// Both arguments accept types that can be converted into a `PathBuf`.
    ///
    /// # Returns
    ///
    /// Returns `Ok(Self)` with the initialized `BackupManager` if successful, or an error
    /// if the Git repository initialization fails.
    ///
    /// # Logging
    ///
    /// * Logs an informational message when starting and successfully completing the initialization process.
    /// * Logs debug messages showing the resolved paths and steps during initialization.
    ///
    /// # Errors
    ///
    /// Returns an error if repository initialization fails. This typically occurs
    /// due to invalid paths, insufficient permissions, or issues with the Git backend.
    ///
    /// # Example
    ///
    /// ```
    /// use obsidian_backup_system::BackupManager;
    ///
    /// let manager = BackupManager::new("./backup_store", "./my_data")
    ///     .expect("Failed to initialize BackupManager");
    /// ```
    ///
    /// Note: Ensure that the provided paths are valid and writable for the process.
    pub fn new(
        store_directory: impl AsRef<Path>,
        working_directory: impl AsRef<Path>,
    ) -> Result<Self> {
        info!("Initializing BackupManager");

        // Convert to absolute paths to avoid path resolution issues
        let store_directory = if store_directory.as_ref().is_absolute() {
            store_directory.as_ref().to_path_buf()
        } else {
            std::env::current_dir()?.join(store_directory.as_ref())
        };

        let working_directory = if working_directory.as_ref().is_absolute() {
            working_directory.as_ref().to_path_buf()
        } else {
            std::env::current_dir()?.join(working_directory.as_ref())
        };

        debug!("Store directory (absolute): {:?}", store_directory);
        debug!("Working directory (absolute): {:?}", working_directory);

        let mut opts = RepositoryInitOptions::new();
        opts.workdir_path(&working_directory);

        debug!("Initializing git repository with options");
        let repository = Repository::init_opts(&store_directory, &opts)?;

        info!("BackupManager initialized successfully");
        Ok(Self {
            repository,
            ignore_matcher: None,
        })
    }

    /// Sets up a `.gitignore`-style ignore file for the repository using the provided file path.
    /// This function configures an ignore matcher to exclude specified paths or patterns.
    ///
    /// # Arguments
    /// * `ignore_file` - A path-like object referencing the ignore file to process. The file should follow `.gitignore` syntax.
    ///
    /// # Returns
    /// * `Result<()>` - Returns `Ok(())` if the ignore matcher is successfully built and configured.
    ///                  Returns an error if the ignore matcher cannot be built or if the ignore file causes an issue.
    ///
    /// # Behavior
    /// 1. Locates the working directory of the repository. Defaults to `./` if the repository has no working directory.
    /// 2. Initializes a `GitignoreBuilder` using the repository's working directory.
    /// 3. Checks whether the provided ignore file exists:
    ///    - If the file exists, attempts to add it to the builder. Logs a warning if there's an issue while adding the file.
    /// 4. Attempts to construct the ignore matcher from the builder:
    ///    - If successful, stores the ignore matcher in `self.ignore_matcher`.
    ///    - If unsuccessful, logs an error message and returns an error.
    ///
    /// # Errors
    /// * Returns an error if:
    ///   - The ignore file could not be properly parsed or added.
    ///   - The ignore matcher fails to build successfully.
    ///
    /// # Logging
    /// - Logs a warning message if the function fails to add the ignore file to the builder.
    /// - Logs an error message if the function fails to build the ignore matcher.
    ///
    /// # Example Usage
    /// ```rust
    /// use std::path::Path;
    /// use obsidian_backup_system::BackupManager;
    ///
    /// let mut backup_manager = BackupManager::new("./backup_store", "./my_data")?;
    /// backup_manager.setup_ignore_file(".my_ignore_file")?;
    /// ```
    pub fn setup_ignore_file(&mut self, ignore_file: impl AsRef<Path>) -> Result<()> {
        let working_directory = self.repository.workdir().unwrap_or(Path::new("./"));
        let mut builder = GitignoreBuilder::new(working_directory);

        let ignore_file = ignore_file.as_ref();

        if ignore_file.exists() {
            if let Some(e) = builder.add(ignore_file) {
                warn!("Failed to add ignore file {ignore_file:?}: {e}");
            }
        }
        match builder.build() {
            Ok(ignore_matcher) => {
                self.ignore_matcher = Some(ignore_matcher);
                Ok(())
            }
            Err(e) => {
                error!("Failed to build ignore matcher: {e}");
                Err(anyhow!("Failed to build ignore matcher: {e}"))
            }
        }
    }

    /// Lists all backup items available in the repository.
    ///
    /// The method traverses the commit history of the repository, collects metadata
    /// for each commit, and returns a list of items representing the backup points. Each
    /// item includes the commit ID, timestamp, and commit message.
    ///
    /// # Process
    /// - Logs an informational message indicating the start of the operation.
    /// - Initializes a revision walk over the repository to retrieve commit objects.
    /// - Iterates through each commit, retrieves its metadata, and constructs a `BackupItem` instance.
    /// - Each created `BackupItem` is logged at the trace level, and the total count is logged at the end.
    ///
    /// # Returns
    /// A `Result` containing a vector of `BackupItem` instances if the operation succeeds, or an error
    /// if any repository operation fails.
    ///
    /// # Errors
    /// Returns an error if:
    /// - The revision walk initialization fails.
    /// - Retrieving an individual commit in the history fails.
    /// - Any other repository-related operation encounters an error.
    ///
    /// # Logging
    /// - Logs informational messages about the start and result of the operation.
    /// - Logs debug messages about processing individual commits.
    /// - Logs trace messages with details of each created `BackupItem`.
    ///
    /// # Example
    /// ```
    /// use obsidian_backup_system::BackupManager;
    ///
    /// let manager = BackupManager::new("./backup_store", "./my_data")
    ///     .expect("Failed to initialize BackupManager");
    ///
    /// match manager.list() {
    ///     Ok(backup_items) => {
    ///         for item in backup_items {
    ///             println!("Backup ID: {}, Timestamp: {}, Description: {}",
    ///                      item.id, item.timestamp, item.description);
    ///         }
    ///     },
    ///     Err(e) => eprintln!("Error listing backup items: {}", e),
    /// }
    /// ```
    ///
    /// # Note
    /// The method assumes that commit messages are UTF-8 encoded. If a commit has
    /// no message, an empty string is used as the description.
    ///
    /// # Dependencies
    /// - Requires the repository to be properly initialized and accessible.
    /// - Relies on the `BackupItem` struct to hold commit metadata.
    pub fn list(&self) -> Result<Vec<BackupItem>> {
        info!("Listing backup items");
        debug!("Starting revision walk");
        let mut items = Vec::new();
        let ids = self.list_ids()?;
        debug!("Found {} commit IDs", ids.len());

        for commit_id in ids {
            debug!("Processing commit: {}", commit_id);
            let commit = self.repository.find_commit(Oid::from_str(&commit_id)?)?;
            let item = BackupItem {
                id: commit_id,
                timestamp: chrono::DateTime::from_timestamp_secs(commit.time().seconds())
                    .unwrap_or(chrono::DateTime::<chrono::Utc>::MIN_UTC),
                description: commit
                    .message()
                    .unwrap_or("No description was provided")
                    .to_string(),
            };
            trace!(
                "Created backup item: id={}, timestamp={}, description={:?}",
                item.id, item.timestamp, item.description
            );
            items.push(item);
        }

        info!("Found {} backup items", items.len());
        Ok(items)
    }

    fn list_ids(&self) -> Result<Vec<String>> {
        let mut rev_walk = self.repository.revwalk()?;
        rev_walk.push_head()?;
        let mut ids = Vec::new();
        for oid in rev_walk {
            let oid = oid?;
            ids.push(oid.to_string());
        }
        Ok(ids)
    }

    /// Creates a backup by committing the current state of the repository.
    ///
    /// This method stages all changes, creates a commit with the given description, and returns the ID
    /// of the newly created commit. If no description is provided, a default description of "No description
    /// provided" is used. It also ensures proper handling for creating an initial commit if the repository
    /// does not have an existing HEAD.
    ///
    /// # Arguments
    ///
    /// * `description` - An optional string containing a description for the backup commit.
    ///
    /// # Returns
    ///
    /// Returns a `Result<String>` which contains:
    /// * On success: The ID of the newly created commit as a string.
    /// * On failure: An error indicating the cause of the failure.
    ///
    /// # Errors
    ///
    /// This function will return an error if:
    /// * There is an issue accessing or writing the repository index.
    /// * There is an issue creating a new tree or finding the tree object in the repository.
    /// * The repository signature (user name and email) is invalid or not set.
    /// * The commit operation fails due to any Git-related error.
    ///
    /// # Logging
    ///
    /// This method emits the following log messages:
    /// * `info` logs for the overall operation (`Creating backup`, `Backup created successfully`).
    /// * `debug` logs for intermediate steps, such as getting the index, adding files, writing the tree, finding
    ///   parents, creating signatures, and creating the commit.
    ///
    /// # Example
    ///
    /// ```rust
    /// use obsidian_backup_system::BackupManager;
    ///
    /// let manager = BackupManager::new("./backup_store", "./my_data")
    ///     .expect("Failed to initialize BackupManager");
    ///
    /// let description = Some("Backup before deployment".to_string());
    /// match manager.backup(description) {
    ///     Ok(commit_id) => println!("Backup created with ID: {}", commit_id),
    ///     Err(e) => eprintln!("Failed to create backup: {}", e),
    /// }
    /// ```
    ///
    /// # Notes
    ///
    /// * This method assumes that the caller has already initialized the repository (`self.repository`) and has
    ///   proper permissions to write to it.
    /// * If no HEAD exists (e.g., for an empty repository), it creates an initial commit without parent commits.
    pub fn backup(&self, description: Option<String>) -> Result<String> {
        info!("Creating backup with description: {:?}", description);

        debug!("Getting repository index");
        let mut index = self.repository.index()?;

        // Get the working directory
        let workdir = self
            .repository
            .workdir()
            .ok_or_else(|| anyhow::anyhow!("Repository has no working directory"))?;

        debug!("Working directory: {:?}", workdir);

        // Clear the index first to handle deleted files
        debug!("Clearing index");
        index.clear()?;

        debug!("Adding all files from working directory to index");
        self.add_directory_to_index(&mut index, workdir, workdir)?;

        debug!("Writing index");
        index.write()?;

        debug!("Creating tree from index");
        let tree_id = index.write_tree()?;
        debug!("Tree created with ID: {}", tree_id);

        let tree = self.repository.find_tree(tree_id)?;
        let head = self.repository.head();

        // Create and own the parent_commit outside the if scope
        let parent_commit = if let Ok(head) = head {
            debug!("Found existing HEAD, using as parent commit");
            Some(head.peel_to_commit()?)
        } else {
            debug!("No existing HEAD found, creating initial commit");
            None
        };

        // Build the parent's vector using references to the owned commit
        let parents = match &parent_commit {
            Some(commit) => {
                debug!("Using parent commit: {}", commit.id());
                vec![commit]
            }
            None => {
                debug!("No parent commits");
                vec![]
            }
        };

        debug!("Getting repository signature");
        let sig = self.repository.signature()?;
        debug!(
            "Signature: {} <{}>",
            sig.name().unwrap_or("unknown"),
            sig.email().unwrap_or("unknown")
        );

        debug!("Creating commit");
        let commit_id = self.repository.commit(
            Some("HEAD"),
            &sig,
            &sig,
            description
                .unwrap_or("No description provided".to_string())
                .as_ref(),
            &tree,
            &parents,
        )?;

        info!("Backup created successfully with ID: {}", commit_id);
        Ok(commit_id.to_string())
    }

    /// Restores a backup by its ID and checks out the associated commit.
    ///
    /// # Arguments
    ///
    /// * `backup_id` - A reference to a string that uniquely identifies the backup.
    ///                 This ID is parsed as a git object ID.
    ///
    /// # Returns
    ///
    /// * `Result<()>` - Returns `Ok(())` if the backup was successfully restored,
    ///                  or an error if the operation fails at any stage.
    ///
    /// # Process
    ///
    /// 1. The backup ID is parsed as a git object ID (OID).
    /// 2. The associated git commit is retrieved using the OID.
    /// 3. The commit's tree is accessed, and its contents are checked out in the repository.
    /// 4. If the repository is configured with a working directory:
    ///    * The contents of the current working directory are removed.
    ///    * A new working directory is created.
    ///    * HEAD is checked out into the working directory.
    /// 5. Logs are generated at various points to provide insights into the restoration process.
    ///
    /// # Logs
    ///
    /// * **Info** logs are used to indicate the start and successful completion of the restore operation.
    /// * **Debug** logs provide detailed information about each step of the process, such as parsing the backup ID,
    ///   working with git objects, and modifying the working directory.
    /// * **Warning** logs occur if no working directory is configured for the repository.
    ///
    /// # Errors
    ///
    /// Returns an error if any of the following occurs:
    ///
    /// * The backup ID cannot be parsed as a valid git OID.
    /// * The associated commit cannot be found in the repository.
    /// * The commit's tree cannot be accessed.
    /// * Checking out the tree in the repository fails.
    /// * File system operations, such as removing or creating the working directory, encounter errors.
    ///
    /// # Example Usage
    ///
    /// ```no_run
    /// use obsidian_backup_system::BackupManager;
    ///
    /// let manager = BackupManager::new("./backup_store", "./my_data")
    ///     .expect("Failed to initialize BackupManager");
    ///
    /// let backup_id = "abcdef1234567890";
    /// if let Err(err) = manager.restore(backup_id) {
    ///     eprintln!("Failed to restore backup: {}", err);
    /// } else {
    ///     println!("Backup restored successfully!");
    /// }
    /// ```
    pub fn restore(&self, backup_id: impl AsRef<str>) -> Result<()> {
        let backup_id = backup_id.as_ref();
        info!("Restoring backup with ID: {}", backup_id);

        debug!("Parsing backup ID as git OID");
        let oid = Oid::from_str(backup_id)?;

        debug!("Finding commit for OID: {}", oid);
        let commit = self.repository.find_commit(oid)?;

        debug!("Getting tree from commit");
        let tree = commit.tree()?;
        debug!("Tree ID: {}", tree.id());

        if let Some(ref workdir) = self.repository.workdir() {
            debug!("Working directory found: {:?}", workdir);

            // Use safer restore approach with temporary directory
            let temp_dir = workdir
                .parent()
                .ok_or_else(|| {
                    anyhow::anyhow!("Cannot determine parent directory for working directory")
                })?
                .join(format!(
                    "{}_restore_tmp",
                    workdir
                        .file_name()
                        .and_then(|n| n.to_str())
                        .unwrap_or("workdir")
                ));

            debug!("Using temporary directory: {:?}", temp_dir);

            // Clean up temp directory if it exists from a previous failed restore
            if temp_dir.exists() {
                debug!("Cleaning up existing temporary directory");
                fs::remove_dir_all(&temp_dir)?;
            }

            // Create temp directory
            debug!("Creating temporary directory");
            fs::create_dir_all(&temp_dir)?;

            // Checkout to temp location
            debug!("Checking out tree to temporary directory");
            let mut checkout_opts = git2::build::CheckoutBuilder::new();
            checkout_opts.target_dir(&temp_dir);
            checkout_opts.force();
            checkout_opts.remove_untracked(true);
            self.repository
                .checkout_tree(tree.as_object(), Some(&mut checkout_opts))?;

            // At this point, the checkout succeeded. Now perform the swap.
            debug!("Checkout successful, swapping directories");

            // Create a backup of the old working directory
            let backup_dir = workdir
                .parent()
                .ok_or_else(|| {
                    anyhow::anyhow!("Cannot determine parent directory for working directory")
                })?
                .join(format!(
                    "{}_old_backup",
                    workdir
                        .file_name()
                        .and_then(|n| n.to_str())
                        .unwrap_or("workdir")
                ));

            // Clean up old backup if it exists
            if backup_dir.exists() {
                debug!("Cleaning up old backup directory");
                fs::remove_dir_all(&backup_dir)?;
            }

            // Move current workdir to backup location
            debug!("Moving current working directory to backup location");
            fs::rename(workdir, &backup_dir)?;

            // Move temp directory to workdir location
            debug!("Moving temporary directory to working directory location");
            match fs::rename(&temp_dir, workdir) {
                Ok(_) => {
                    debug!("Restore completed successfully, cleaning up old backup");
                    // Only remove the old backup if the restore succeeded
                    let _ = fs::remove_dir_all(&backup_dir);
                }
                Err(e) => {
                    // If rename fails, try to restore the original
                    error!("Failed to move temp directory: {}", e);
                    debug!("Attempting to restore original working directory");
                    if let Err(_restore_err) = fs::rename(&backup_dir, workdir) {
                        error!("Failed to restore original directory: {}", _restore_err);
                        return Err(anyhow::anyhow!(
                            "Restore failed and could not recover original directory. Original backed up at: {:?}",
                            backup_dir
                        ));
                    }
                    return Err(anyhow::anyhow!("Failed to complete restore: {}", e));
                }
            }
        } else {
            warn!("No working directory configured for repository");
            // For bare repositories, just update HEAD
            debug!("Checking out tree in bare repository");
            self.repository.checkout_tree(tree.as_object(), None)?;
        }

        info!("Backup restored successfully");
        Ok(())
    }

    /// Exports a backup identified by its ID into a compressed archive.
    ///
    /// This function retrieves a backup commit from the Git repository using the provided `backup_id`,
    /// packages its content into a compressed archive, and writes the result to the specified `output_path`.
    ///
    /// # Parameters
    ///
    /// * `backup_id` - A string-like identifier of the backup to export. This must correspond to a valid Git object ID (OID) in the repository.
    /// * `output_path` - The destination path for the created archive. This must be a valid filesystem path.
    /// * `level` - Compression level (0-9, clamped to this range). The value determines the trade-off between compression size and speed.
    ///
    /// # Returns
    ///
    /// * `Result<()>` - Returns `Ok(())` if the archive is successfully created, or an error if any step in the process fails.
    ///
    /// # Errors
    ///
    /// This function can fail for several reasons, including (but not limited to):
    ///
    /// 1. The provided `backup_id` is not a valid Git OID.
    /// 2. The backup commit or its associated tree cannot be found within the repository.
    /// 3. Issues encountered while creating the archive writer or writing to the output path.
    /// 4. Any errors arising from compression settings or file operations during the archive creation process.
    ///
    /// # Logging
    ///
    /// - Logs the progress of the backup export process at `info` and `debug` levels.
    /// - Logs errors if any step in the process fails.
    ///
    /// # Example
    ///
    /// ```rust
    /// use obsidian_backup_system::BackupManager;
    ///
    /// let manager = BackupManager::new("./backup_store", "./my_data")
    ///     .expect("Failed to initialize BackupManager");
    ///
    /// let last_backup = manager
    ///     .last()
    ///     .expect("Failed to get last backup")
    ///     .expect("No backups found");
    ///
    /// manager.export(&last_backup.id, "backup.7z", 5)
    ///     .expect("Failed to export backup");
    /// ```
    ///
    /// In this example, the specified backup ID is packed into a `.7z` archive
    /// with medium compression level (5) and saved to the given output path.
    #[cfg(feature = "zip")]
    pub fn export(
        &self,
        backup_id: impl AsRef<str>,
        output_path: impl AsRef<Path>,
        level: u8,
    ) -> Result<()> {
        // Validate and clamp compression level to 0-9 range
        let level = level.clamp(0, 9);

        let mut writer = ArchiveWriter::create(output_path)?;
        writer.set_content_methods(vec![
            encoder_options::Lzma2Options::from_level(level as u32).into(),
        ]);

        let backup_id = backup_id.as_ref();
        info!("Exporting backup with ID: {} to archive", backup_id);
        let oid = Oid::from_str(backup_id)?;
        let commit = self.repository.find_commit(oid)?;
        let tree = commit.tree()?;

        // Walk the tree recursively and add files to the archive
        self.add_tree_to_archive(&mut writer, &tree, "")?;

        debug!("Finalizing archive");
        writer.finish()?;

        info!("Archive created successfully");
        Ok(())
    }

    /// Computes the list of files that were modified (added, updated, or deleted)
    /// in the specified backup/commit within the repository.
    ///
    /// # Arguments
    ///
    /// * `backup_id` - A string-like identifier for the backup or commit to compute
    ///                 the modified files against its parent commit. The function
    ///                 expects this to be in the format of a valid Git object ID.
    ///
    /// # Returns
    ///
    /// A `Result` containing:
    /// * `Ok(Vec<ModifiedFile>)` - A vector of `ModifiedFile` objects, each representing
    ///                             a file that was added, updated, or deleted. Each `ModifiedFile`
    ///                             includes:
    ///   - `path`: The path of the file.
    ///   - `content_before`: The file's content before modification (if applicable, `Some` if the file existed, otherwise `None`).
    ///   - `content_after`: The file's content after modification (if applicable, `Some` if the file exists, otherwise `None` for deletions).
    /// * `Err(git2::Error)` - In case of any error during Git repository or commit/tree operations.
    ///
    /// # Details
    ///
    /// * The function computes the difference between the specified commit/tree and its
    ///   immediate parent (if available). If there is no parent commit (e.g., for the first commit),
    ///   only the newly added files will appear in the output list.
    /// * For each file in the current tree:
    ///     - If a corresponding file exists in the parent tree, the function checks for modifications.
    ///     - If the file does not exist in the parent tree, it is marked as newly added.
    /// * For files that existed in the parent tree but are absent in the current tree,
    ///   the function marks them as deleted.
    ///
    /// # Errors
    ///
    /// This function can return an `Err` in the following situations:
    /// * If the provided `backup_id` is not a valid Git commit or tree object ID.
    /// * If the repository cannot find the commit or tree corresponding to `backup_id`.
    /// * If there are errors while retrieving or processing blobs within the trees.
    ///
    /// # Example
    ///
    /// ```rust
    /// use obsidian_backup_system::BackupManager;
    ///
    /// let manager = BackupManager::new("./backup_store", "./my_data")
    ///     .expect("Failed to initialize BackupManager");
    ///
    /// let backup_id = "abcd1234";
    /// let modified_files = manager.diff(backup_id)
    ///     .expect("Failed to get diff");
    ///
    /// for file in modified_files {
    ///     println!("Path: {}", file.path);
    ///     match (&file.content_before, &file.content_after) {
    ///         (Some(before), Some(after)) => {
    ///             println!("File was modified. Before size: {}, After size: {}", before.len(), after.len());
    ///         }
    ///         (None, Some(after)) => {
    ///             println!("File was added. Size: {}", after.len());
    ///         }
    ///         (Some(before), None) => {
    ///             println!("File was deleted. Previous size: {}", before.len());
    ///         }
    ///         _ => {}
    ///     }
    /// }
    /// ```
    ///
    /// # Structs Used
    ///
    /// * `ModifiedFile`: A struct representing a modified file, with the following fields:
    ///     - `path`: The file's path as a `String`.
    ///     - `content_before`: An optional `Vec<u8>` containing the file's content in the parent revision (if it existed).
    ///     - `content_after`: An optional `Vec<u8>` containing the file's content in the current revision (if it exists).
    ///
    /// # Note
    ///
    /// * This function assumes text or binary files are stored as blobs in the Git repository.
    /// * Files that are not blobs (e.g., submodules or symlinks) are ignored.
    pub fn diff(&self, backup_id: impl AsRef<str>) -> Result<Vec<ModifiedFile>> {
        let backup_id = backup_id.as_ref();
        let mut files = Vec::new();
        let oid = Oid::from_str(backup_id)?;
        let commit = self.repository.find_commit(oid)?;
        let tree = commit.tree()?;

        // Get the parent commit tree (if exists) to compare against
        let parent_tree = if commit.parent_count() > 0 {
            Some(commit.parent(0)?.tree()?)
        } else {
            None
        };

        // Recursively diff trees
        self.diff_trees_recursive(&tree, parent_tree.as_ref(), "", &mut files)?;

        Ok(files)
    }

    /// Helper method to recursively diff two trees
    fn diff_trees_recursive(
        &self,
        tree: &git2::Tree,
        parent_tree: Option<&git2::Tree>,
        path_prefix: &str,
        files: &mut Vec<ModifiedFile>,
    ) -> Result<()> {
        // Check files in current tree (for added/modified files)
        for entry in tree.iter() {
            let name = entry.name().unwrap_or("");
            let full_path = if path_prefix.is_empty() {
                name.to_string()
            } else {
                format!("{}/{}", path_prefix, name)
            };

            match entry.kind() {
                Some(git2::ObjectType::Blob) => {
                    // It's a file
                    let blob = self.repository.find_blob(entry.id())?;
                    let content_after = blob.content().to_vec();

                    // Try to get the content before from parent commit
                    let content_before = if let Some(parent_tree) = parent_tree {
                        parent_tree
                            .get_name(name)
                            .and_then(|parent_entry| {
                                if let Some(git2::ObjectType::Blob) = parent_entry.kind() {
                                    self.repository.find_blob(parent_entry.id()).ok()
                                } else {
                                    None
                                }
                            })
                            .map(|parent_blob| parent_blob.content().to_vec())
                    } else {
                        None
                    };

                    // Only add if file was added or modified
                    if let Some(before_content) = content_before {
                        // File existed before - check if it was modified
                        if before_content != content_after {
                            files.push(ModifiedFile {
                                path: full_path,
                                content_before: Some(before_content),
                                content_after: Some(content_after),
                            });
                        }
                        // If content is the same, don't add to results
                    } else {
                        // File was added
                        files.push(ModifiedFile {
                            path: full_path,
                            content_before: None,
                            content_after: Some(content_after),
                        });
                    }
                }
                Some(git2::ObjectType::Tree) => {
                    // It's a directory, recurse into it
                    let subtree = self.repository.find_tree(entry.id())?;
                    let parent_subtree =
                        parent_tree.and_then(|pt| pt.get_name(name)).and_then(|e| {
                            if let Some(git2::ObjectType::Tree) = e.kind() {
                                self.repository.find_tree(e.id()).ok()
                            } else {
                                None
                            }
                        });
                    self.diff_trees_recursive(
                        &subtree,
                        parent_subtree.as_ref(),
                        &full_path,
                        files,
                    )?;
                }
                _ => {
                    // Skip other object types
                }
            }
        }

        // Check for files/directories that were deleted (existed in parent but not in current)
        if let Some(parent_tree) = parent_tree {
            for parent_entry in parent_tree.iter() {
                let name = parent_entry.name().unwrap_or("");
                let full_path = if path_prefix.is_empty() {
                    name.to_string()
                } else {
                    format!("{}/{}", path_prefix, name)
                };

                // If this entry doesn't exist in the current tree, it was deleted
                if tree.get_name(name).is_none() {
                    match parent_entry.kind() {
                        Some(git2::ObjectType::Blob) => {
                            // File was deleted
                            let parent_blob = self.repository.find_blob(parent_entry.id())?;
                            let content_before = parent_blob.content().to_vec();

                            files.push(ModifiedFile {
                                path: full_path,
                                content_before: Some(content_before),
                                content_after: None,
                            });
                        }
                        Some(git2::ObjectType::Tree) => {
                            // Directory was deleted - recursively add all files as deleted
                            let parent_subtree = self.repository.find_tree(parent_entry.id())?;
                            self.diff_trees_recursive(
                                &parent_subtree,
                                Some(&parent_subtree),
                                &full_path,
                                &mut Vec::new(),
                            )?;
                            // Mark all files in the deleted directory
                            self.mark_tree_as_deleted(&parent_subtree, &full_path, files)?;
                        }
                        _ => {}
                    }
                }
            }
        }

        Ok(())
    }

    /// Helper method to mark all files in a tree as deleted
    fn mark_tree_as_deleted(
        &self,
        tree: &git2::Tree,
        path_prefix: &str,
        files: &mut Vec<ModifiedFile>,
    ) -> Result<()> {
        for entry in tree.iter() {
            let name = entry.name().unwrap_or("");
            let full_path = if path_prefix.is_empty() {
                name.to_string()
            } else {
                format!("{}/{}", path_prefix, name)
            };

            match entry.kind() {
                Some(git2::ObjectType::Blob) => {
                    let blob = self.repository.find_blob(entry.id())?;
                    files.push(ModifiedFile {
                        path: full_path,
                        content_before: Some(blob.content().to_vec()),
                        content_after: None,
                    });
                }
                Some(git2::ObjectType::Tree) => {
                    let subtree = self.repository.find_tree(entry.id())?;
                    self.mark_tree_as_deleted(&subtree, &full_path, files)?;
                }
                _ => {}
            }
        }
        Ok(())
    }
    pub fn last(&self) -> Result<Option<BackupItem>> {
        // Check if HEAD exists first
        if self.repository.head().is_err() {
            return Ok(None); // No backups yet
        }

        let mut rev_walk = self.repository.revwalk()?;
        rev_walk.push_head()?;
        if let Some(oid) = rev_walk.next() {
            let oid = oid?;
            let commit = self.repository.find_commit(oid)?;
            let item = BackupItem {
                id: oid.to_string(),
                timestamp: chrono::DateTime::from_timestamp_secs(commit.time().seconds())
                    .unwrap_or(chrono::DateTime::<chrono::Utc>::MIN_UTC),
                description: commit
                    .message()
                    .unwrap_or("No description was provided")
                    .to_string(),
            };
            Ok(Some(item))
        } else {
            Ok(None)
        }
    }

    #[cfg(feature = "zip")]
    fn add_tree_to_archive(
        &self,
        writer: &mut ArchiveWriter<fs::File>,
        tree: &git2::Tree,
        path_prefix: &str,
    ) -> Result<()> {
        for entry in tree.iter() {
            let name = entry.name().unwrap_or("");
            let full_path = if path_prefix.is_empty() {
                name.to_string()
            } else {
                format!("{}/{}", path_prefix, name)
            };

            match entry.kind() {
                Some(git2::ObjectType::Blob) => {
                    // It's a file
                    debug!("Adding file to archive: {}", full_path);
                    let blob = self.repository.find_blob(entry.id())?;
                    let content = blob.content();

                    writer.push_archive_entry(
                        sevenz_rust2::ArchiveEntry::new_file(&full_path),
                        Some(content),
                    )?;
                }
                Some(git2::ObjectType::Tree) => {
                    // It's a directory, recurse into it
                    debug!("Entering directory: {}", full_path);
                    let subtree = self.repository.find_tree(entry.id())?;
                    self.add_tree_to_archive(writer, &subtree, &full_path)?;
                }
                _ => {
                    // Skip other object types (commits, tags, etc.)
                    debug!("Skipping object type: {:?} for {}", entry.kind(), full_path);
                }
            }
        }
        Ok(())
    }

    pub fn purge_backups_over_count(&self, count: usize) -> Result<()> {
        info!("Purging backups over count: {}", count);

        // Get all commit IDs
        let ids = self.list_ids()?;

        if ids.len() <= count {
            info!(
                "Number of backups ({}) is within limit ({})",
                ids.len(),
                count
            );
            return Ok(());
        }

        // Keep the most recent 'count' commits
        let commits_to_keep = &ids[..count];
        let oldest_commit_to_keep = &ids[count - 1];

        debug!("Keeping {} most recent commits", count);
        debug!("Oldest commit to keep: {}", oldest_commit_to_keep);

        // Get the tree of the oldest commit we want to keep
        let oldest_oid = Oid::from_str(oldest_commit_to_keep)?;
        let oldest_commit = self.repository.find_commit(oldest_oid)?;
        let oldest_tree = oldest_commit.tree()?;

        // Create a new initial commit with this tree
        let sig = self.repository.signature()?;
        let new_base_oid = self.repository.commit(
            None, // Don't update any reference yet
            &sig,
            &sig,
            &format!(
                "Consolidated backup prior to {}",
                oldest_commit.time().seconds()
            ),
            &oldest_tree,
            &[], // No parents - this becomes the new root
        )?;

        debug!("Created new base commit: {}", new_base_oid);

        // Now we need to rewrite the remaining commits to use this new base
        self.rewrite_commit_chain(&commits_to_keep[..commits_to_keep.len() - 1], new_base_oid)?;

        // Force garbage collection to remove unreferenced objects
        self.cleanup_orphaned_commits()?;

        info!("Successfully purged {} old backups", ids.len() - count);
        Ok(())
    }

    pub fn purge_backups_older_than(&self, period: chrono::Duration) -> Result<()> {
        info!("Purging backups older than {:?}", period);

        let now = chrono::Utc::now();
        let cutoff_time = now - period;
        let cutoff_timestamp = cutoff_time.timestamp();

        debug!("Cutoff timestamp: {}", cutoff_timestamp);

        // Get all commits
        let ids = self.list_ids()?;
        let mut commits_to_keep = Vec::new();
        let mut oldest_commit_to_delete = None;

        for commit_id in &ids {
            let oid = Oid::from_str(commit_id)?;
            let commit = self.repository.find_commit(oid)?;
            let commit_time = commit.time().seconds();

            if commit_time >= cutoff_timestamp {
                commits_to_keep.push(commit_id.clone());
            } else {
                // Track the oldest commit we're deleting (youngest of the ones to delete)
                if oldest_commit_to_delete.is_none() {
                    oldest_commit_to_delete = Some((commit_id.clone(), commit));
                }
            }
        }

        if commits_to_keep.len() == ids.len() {
            info!("No backups to purge");
            return Ok(());
        }

        if commits_to_keep.is_empty() {
            return Err(anyhow::anyhow!("Cannot purge all backups"));
        }

        // Create a consolidated base commit from the oldest commit to keep
        let oldest_to_keep = &commits_to_keep[commits_to_keep.len() - 1];
        let oldest_oid = Oid::from_str(oldest_to_keep)?;
        let oldest_commit = self.repository.find_commit(oldest_oid)?;
        let oldest_tree = oldest_commit.tree()?;

        let sig = self.repository.signature()?;
        let new_base_oid = self.repository.commit(
            None,
            &sig,
            &sig,
            &format!(
                "Consolidated backup prior to {}",
                chrono::DateTime::from_timestamp_secs(oldest_commit.time().seconds()).unwrap()
            ),
            &oldest_tree,
            &[],
        )?;

        debug!("Created new base commit: {}", new_base_oid);

        // Rewrite remaining commits
        if commits_to_keep.len() > 1 {
            self.rewrite_commit_chain(&commits_to_keep[..commits_to_keep.len() - 1], new_base_oid)?;
        } else {
            // Only one commit to keep, just update HEAD to the new base
            self.repository.reference(
                "refs/heads/master",
                new_base_oid,
                true,
                "Purged old backups",
            )?;
            self.repository.set_head("refs/heads/master")?;
        }

        self.cleanup_orphaned_commits()?;

        info!("Successfully purged backups older than {:?}", period);
        Ok(())
    }

    pub fn purge_backups_over_size(&self, size: usize) -> Result<()> {
        info!(
            "Purging backups to reduce repository size below {} bytes",
            size
        );

        // Get current repository size
        let repo_path = self.repository.path();
        let current_size = self.calculate_repo_size(repo_path)?;

        debug!("Current repository size: {} bytes", current_size);

        if current_size <= size {
            info!("Repository size is within limit");
            return Ok(());
        }

        // Strategy: Remove oldest commits one by one until size is acceptable
        let ids = self.list_ids()?;

        if ids.len() <= 1 {
            return Err(anyhow::anyhow!(
                "Cannot reduce size further without removing all backups"
            ));
        }

        // Binary search for the right number of commits to keep
        let mut keep_count = ids.len();

        while keep_count > 1 {
            keep_count /= 2;

            // Estimate if this would be enough by checking
            // We'll need to actually try purging to get accurate size
            debug!("Trying to keep {} commits", keep_count);

            // For now, just use purge_backups_over_count approach
            // In production, you might want a more sophisticated size estimation
            self.purge_backups_over_count(keep_count)?;

            let new_size = self.calculate_repo_size(repo_path)?;
            debug!("New repository size: {} bytes", new_size);

            if new_size <= size {
                info!("Successfully reduced repository size to {} bytes", new_size);
                return Ok(());
            }
        }

        Err(anyhow::anyhow!(
            "Could not reduce repository size below {} bytes",
            size
        ))
    }

    /// Helper function to rewrite a chain of commits with a new parent
    fn rewrite_commit_chain(&self, commit_ids: &[String], new_parent_oid: Oid) -> Result<()> {
        debug!("Rewriting commit chain with {} commits", commit_ids.len());

        let mut current_parent = new_parent_oid;
        let mut new_head = None;

        // Iterate through commits from oldest to newest (reverse order)
        for commit_id in commit_ids.iter().rev() {
            let old_oid = Oid::from_str(commit_id)?;
            let old_commit = self.repository.find_commit(old_oid)?;

            debug!("Rewriting commit: {}", commit_id);

            let parent_commit = self.repository.find_commit(current_parent)?;

            // Create new commit with same tree but new parent
            let new_oid = self.repository.commit(
                None,
                &old_commit.author(),
                &old_commit.committer(),
                old_commit.message().unwrap_or("No description provided"),
                &old_commit.tree()?,
                &[&parent_commit],
            )?;

            debug!("Created new commit: {} (was: {})", new_oid, old_oid);

            current_parent = new_oid;
            new_head = Some(new_oid);
        }

        // Update HEAD to point to the new chain
        if let Some(head_oid) = new_head {
            debug!("Updating HEAD to: {}", head_oid);
            self.repository.reference(
                "refs/heads/master",
                head_oid,
                true,
                "Restructured commit history",
            )?;
            self.repository.set_head("refs/heads/master")?;
        }

        Ok(())
    }

    /// Clean up orphaned commits and run garbage collection
    ///
    /// This implements a standalone garbage collection mechanism that:
    /// 1. Expires reflog entries
    /// 2. Identifies all reachable objects from refs
    /// 3. Removes unreachable loose objects
    /// 4. Packs remaining loose objects into packfiles
    fn cleanup_orphaned_commits(&self) -> Result<()> {
        info!("Starting comprehensive garbage collection");

        // Step 1: Expire reflog entries immediately
        debug!("Expiring reflog entries");
        self.expire_reflogs()?;

        // Step 2: Collect all reachable objects
        debug!("Identifying reachable objects");
        let reachable_oids = self.find_reachable_objects()?;
        info!("Found {} reachable objects", reachable_oids.len());

        // Step 3: Remove unreachable loose objects
        debug!("Pruning unreachable objects");
        let _pruned_count = self.prune_unreachable_objects(&reachable_oids)?;
        info!("Pruned {} unreachable objects", _pruned_count);

        // Step 4: Pack loose objects
        debug!("Packing loose objects");
        let _packed_count = self.pack_loose_objects()?;
        info!("Packed {} loose objects", _packed_count);

        // Step 5: Pack references
        debug!("Packing references");
        self.pack_references()?;

        info!("Garbage collection completed successfully");
        Ok(())
    }

    /// Expire all reflog entries
    fn expire_reflogs(&self) -> Result<()> {
        let reflog_refs = vec!["HEAD", "refs/heads/master"];

        for ref_name in reflog_refs {
            if let Ok(mut reflog) = self.repository.reflog(ref_name) {
                // Clear all reflog entries
                while !reflog.is_empty() {
                    reflog.remove(0, false)?;
                }
                reflog.write()?;
            }
        }

        Ok(())
    }

    /// Find all objects reachable from current refs
    fn find_reachable_objects(&self) -> Result<std::collections::HashSet<Oid>> {
        use std::collections::{HashSet, VecDeque};

        let mut reachable = HashSet::new();
        let mut to_visit = VecDeque::new();

        // Start from all references
        for reference in self.repository.references()? {
            let reference = reference?;
            if let Some(oid) = reference.target() {
                to_visit.push_back(oid);
                reachable.insert(oid);
            }
        }

        // Also include HEAD if it exists
        if let Ok(head) = self.repository.head() {
            if let Some(oid) = head.target() {
                to_visit.push_back(oid);
                reachable.insert(oid);
            }
        }

        // Traverse the object graph
        while let Some(oid) = to_visit.pop_front() {
            // Try to read the object and find its dependencies
            if let Ok(obj) = self.repository.find_object(oid, None) {
                match obj.kind() {
                    Some(git2::ObjectType::Commit) => {
                        if let Some(commit) = obj.as_commit() {
                            // Add the tree
                            let tree_oid = commit.tree_id();
                            if reachable.insert(tree_oid) {
                                to_visit.push_back(tree_oid);
                            }

                            // Add all parents
                            for parent in commit.parents() {
                                let parent_oid = parent.id();
                                if reachable.insert(parent_oid) {
                                    to_visit.push_back(parent_oid);
                                }
                            }
                        }
                    }
                    Some(git2::ObjectType::Tree) => {
                        if let Some(tree) = obj.as_tree() {
                            for entry in tree.iter() {
                                let entry_oid = entry.id();
                                if reachable.insert(entry_oid) {
                                    to_visit.push_back(entry_oid);
                                }
                            }
                        }
                    }
                    Some(git2::ObjectType::Tag) => {
                        if let Some(tag) = obj.as_tag() {
                            let target_id = tag.target_id();
                            if reachable.insert(target_id) {
                                to_visit.push_back(target_id);
                            }
                        }
                    }
                    _ => {
                        // Blobs have no dependencies
                    }
                }
            }
        }

        Ok(reachable)
    }

    /// Remove unreachable loose objects from the object database
    fn prune_unreachable_objects(
        &self,
        reachable_oids: &std::collections::HashSet<Oid>,
    ) -> Result<usize> {
        let objects_dir = self.repository.path().join("objects");
        let mut pruned_count = 0;

        // Iterate through loose object directories (00-ff)
        for i in 0..256 {
            let dir_name = format!("{:02x}", i);
            let dir_path = objects_dir.join(&dir_name);

            if !dir_path.exists() {
                continue;
            }

            for entry in fs::read_dir(&dir_path)? {
                let entry = entry?;
                let file_name = entry.file_name();
                let file_name_str = file_name.to_string_lossy();

                // Skip pack and idx files
                if file_name_str == "pack" || file_name_str == "info" {
                    continue;
                }

                // Construct the full OID from directory and filename
                let oid_str = format!("{}{}", dir_name, file_name_str);

                if let Ok(oid) = Oid::from_str(&oid_str) {
                    // If this object is not reachable, delete it
                    if !reachable_oids.contains(&oid) {
                        let file_path = entry.path();
                        debug!("Pruning unreachable object: {}", oid);
                        fs::remove_file(&file_path)?;
                        pruned_count += 1;

                        // Remove directory if it's now empty
                        if let Ok(mut entries) = fs::read_dir(&dir_path) {
                            if entries.next().is_none() {
                                let _ = fs::remove_dir(&dir_path);
                            }
                        }
                    }
                }
            }
        }

        Ok(pruned_count)
    }

    /// Pack loose objects into packfiles
    fn pack_loose_objects(&self) -> Result<usize> {
        let objects_dir = self.repository.path().join("objects");
        let mut loose_oids = Vec::new();

        // Collect all loose object OIDs
        for i in 0..256 {
            let dir_name = format!("{:02x}", i);
            let dir_path = objects_dir.join(&dir_name);

            if !dir_path.exists() {
                continue;
            }

            for entry in fs::read_dir(&dir_path)? {
                let entry = entry?;
                let file_name = entry.file_name();
                let file_name_str = file_name.to_string_lossy();

                // Skip pack and idx files
                if file_name_str == "pack" || file_name_str == "info" {
                    continue;
                }

                // Construct the full OID
                let oid_str = format!("{}{}", dir_name, file_name_str);
                if let Ok(oid) = Oid::from_str(&oid_str) {
                    loose_oids.push(oid);
                }
            }
        }

        let loose_count = loose_oids.len();

        if loose_oids.is_empty() {
            debug!("No loose objects to pack");
            return Ok(0);
        }

        debug!("Packing {} loose objects", loose_count);

        // Create a packbuilder
        let mut packbuilder = self.repository.packbuilder()?;

        // Add all loose objects to the pack
        for oid in &loose_oids {
            if let Err(_e) = packbuilder.insert_object(*oid, None) {
                debug!("Failed to insert object {} into pack: {}", oid, _e);
                // Continue with other objects
            }
        }

        // Write the packfile
        let pack_dir = objects_dir.join("pack");
        fs::create_dir_all(&pack_dir)?;

        // Generate a unique pack name based on timestamp
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_secs();
        let pack_path = pack_dir.join(format!("pack-{:x}.pack", timestamp));

        debug!("Writing packfile to: {:?}", pack_path);
        let mut buf = git2::Buf::new();
        packbuilder.write_buf(&mut buf)?;
        fs::write::<&std::path::PathBuf, &[u8]>(&pack_path, buf.as_ref())?;

        // After successful packing, remove the loose objects
        for oid in &loose_oids {
            let oid_str = oid.to_string();
            let dir_name = &oid_str[..2];
            let file_name = &oid_str[2..];
            let file_path = objects_dir.join(dir_name).join(file_name);

            if file_path.exists() {
                let _ = fs::remove_file(&file_path);
            }
        }

        // Clean up empty directories
        for i in 0..256 {
            let dir_name = format!("{:02x}", i);
            let dir_path = objects_dir.join(&dir_name);

            if dir_path.exists() {
                if let Ok(mut entries) = fs::read_dir(&dir_path) {
                    if entries.next().is_none() {
                        let _ = fs::remove_dir(&dir_path);
                    }
                }
            }
        }

        Ok(loose_count)
    }

    /// Pack references into packed-refs file
    fn pack_references(&self) -> Result<()> {
        // Get all references
        let mut refs_to_pack = Vec::new();

        for reference in self.repository.references()? {
            let reference = reference?;
            let name = reference.name().unwrap_or("");

            // Only pack refs under refs/ (not HEAD or other special refs)
            if name.starts_with("refs/") {
                if let Some(target) = reference.target() {
                    refs_to_pack.push((name.to_string(), target));
                }
            }
        }

        if refs_to_pack.is_empty() {
            debug!("No references to pack");
            return Ok(());
        }

        // Write packed-refs file
        let packed_refs_path = self.repository.path().join("packed-refs");
        let mut content = String::from("# pack-refs with: peeled fully-peeled sorted\n");

        for (name, oid) in &refs_to_pack {
            content.push_str(&format!("{} {}\n", oid, name));
        }

        fs::write(&packed_refs_path, content)?;

        // Remove individual ref files
        for (name, _) in &refs_to_pack {
            let ref_path = self.repository.path().join(name);
            if ref_path.exists() {
                let _ = fs::remove_file(&ref_path);
            }
        }

        debug!("Packed {} references", refs_to_pack.len());
        Ok(())
    }

    /// Calculate the total size of the repository
    fn calculate_repo_size(&self, repo_path: &Path) -> Result<usize> {
        let mut total_size = 0;

        fn visit_dirs(dir: &Path, total: &mut usize) -> Result<()> {
            if dir.is_dir() {
                for entry in fs::read_dir(dir)? {
                    let entry = entry?;
                    let path = entry.path();
                    if path.is_dir() {
                        visit_dirs(&path, total)?;
                    } else {
                        *total += fs::metadata(&path)?.len() as usize;
                    }
                }
            }
            Ok(())
        }

        visit_dirs(repo_path, &mut total_size)?;
        Ok(total_size)
    }
}
