mod test {
    use log::LevelFilter;
    use std::fs;
    use std::path::{Path, PathBuf};

    /// Helper function to create a unique test environment
    fn setup_test_env(test_name: &str) -> (PathBuf, PathBuf) {
        pretty_env_logger::env_logger::builder()
            .format_timestamp(None)
            .filter_level(LevelFilter::Trace)
            .is_test(true)
            .init();
        let base_dir = PathBuf::from("target/test_backup_manager");
        let store_dir = base_dir.join(format!("{}_store", test_name));
        let working_dir = base_dir.join(format!("{}_working", test_name));

        // Clean up if exists
        let _ = fs::remove_dir_all(&store_dir);
        let _ = fs::remove_dir_all(&working_dir);

        // Create directories
        fs::create_dir_all(&store_dir).expect("Failed to create store directory");
        fs::create_dir_all(&working_dir).expect("Failed to create working directory");

        (store_dir, working_dir)
    }

    /// Helper function to create a test file with content
    fn create_test_file(dir: &Path, filename: &str, content: &[u8]) {
        let file_path = dir.join(filename);
        fs::write(file_path, content).expect("Failed to create test file");
    }

    use obsidian_backup_system::BackupManager;

    #[test]
    fn test_backup_manager_new() {
        let (store_dir, working_dir) = setup_test_env("new");

        let manager = BackupManager::new(&store_dir, &working_dir);
        assert!(manager.is_ok(), "Failed to create BackupManager");
    }

    #[test]
    fn test_backup_manager_new_with_relative_paths() {
        let store_dir = "target/test_backup_manager/relative_store";
        let working_dir = "target/test_backup_manager/relative_working";

        // Clean up
        let _ = fs::remove_dir_all(store_dir);
        let _ = fs::remove_dir_all(working_dir);

        // Create directories
        fs::create_dir_all(store_dir).expect("Failed to create store directory");
        fs::create_dir_all(working_dir).expect("Failed to create working directory");

        let manager = BackupManager::new(store_dir, working_dir);
        assert!(
            manager.is_ok(),
            "Failed to create BackupManager with relative paths"
        );
    }

    #[test]
    fn test_backup_single_file() {
        let (store_dir, working_dir) = setup_test_env("backup_single");

        create_test_file(&working_dir, "test.txt", b"Hello, World!");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        let backup_id = manager.backup(None).expect("Failed to create backup");
        assert!(!backup_id.is_empty(), "Backup ID should not be empty");
    }

    #[test]
    fn test_backup_with_description() {
        let (store_dir, working_dir) = setup_test_env("backup_description");

        create_test_file(&working_dir, "test.txt", b"Test content");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        let description = "Test backup with description".to_string();
        let backup_id = manager
            .backup(Some(description.clone()))
            .expect("Failed to create backup");

        assert!(!backup_id.is_empty(), "Backup ID should not be empty");

        // Verify the backup has the correct description
        let backups = manager.list().expect("Failed to list backups");
        assert_eq!(backups.len(), 1, "Should have exactly one backup");
        assert_eq!(
            backups[0].description, description,
            "Description should match"
        );
    }

    #[test]
    fn test_backup_multiple_files() {
        let (store_dir, working_dir) = setup_test_env("backup_multiple");

        create_test_file(&working_dir, "file1.txt", b"Content 1");
        create_test_file(&working_dir, "file2.txt", b"Content 2");
        create_test_file(&working_dir, "file3.txt", b"Content 3");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        let backup_id = manager
            .backup(Some("Multiple files backup".to_string()))
            .expect("Failed to create backup");

        assert!(!backup_id.is_empty(), "Backup ID should not be empty");
    }

    #[test]
    fn test_backup_with_subdirectories() {
        let (store_dir, working_dir) = setup_test_env("backup_subdirs");

        let subdir = working_dir.join("subdir");
        fs::create_dir_all(&subdir).expect("Failed to create subdirectory");

        create_test_file(&working_dir, "root.txt", b"Root file");
        create_test_file(&subdir, "sub.txt", b"Sub file");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        let backup_id = manager
            .backup(Some("Backup with subdirectories".to_string()))
            .expect("Failed to create backup");

        assert!(!backup_id.is_empty(), "Backup ID should not be empty");
    }

    #[test]
    fn test_list_backups() {
        let (store_dir, working_dir) = setup_test_env("list");

        create_test_file(&working_dir, "test.txt", b"Initial content");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        // Create first backup
        manager
            .backup(Some("First backup".to_string()))
            .expect("Failed to create first backup");

        // Modify file
        create_test_file(&working_dir, "test.txt", b"Modified content");

        // Create second backup
        manager
            .backup(Some("Second backup".to_string()))
            .expect("Failed to create second backup");

        // List backups
        let backups = manager.list().expect("Failed to list backups");
        assert_eq!(backups.len(), 2, "Should have two backups");
        assert_eq!(
            backups[0].description, "Second backup",
            "First in list should be most recent"
        );
        assert_eq!(
            backups[1].description, "First backup",
            "Second in list should be oldest"
        );
    }

    #[test]
    fn test_last_backup() {
        let (store_dir, working_dir) = setup_test_env("last");

        create_test_file(&working_dir, "test.txt", b"Content");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        // No backups yet - last() will fail because there's no HEAD
        let last_result = manager.last();
        assert!(last_result.is_err(), "Should fail when no backups exist");

        // Create backups
        manager
            .backup(Some("First".to_string()))
            .expect("Failed to create first backup");
        create_test_file(&working_dir, "test.txt", b"Modified");
        manager
            .backup(Some("Second".to_string()))
            .expect("Failed to create second backup");

        let last = manager.last().expect("Failed to get last backup");
        assert!(last.is_some(), "Should have a last backup");
        assert_eq!(
            last.unwrap().description,
            "Second",
            "Last backup should be the most recent"
        );
    }

    #[test]
    fn test_restore_backup() {
        let (store_dir, working_dir) = setup_test_env("restore");

        // Create initial content
        create_test_file(&working_dir, "test.txt", b"Original content");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        let backup_id = manager
            .backup(Some("Original state".to_string()))
            .expect("Failed to create backup");

        // Modify the file
        create_test_file(&working_dir, "test.txt", b"Modified content");

        // Test that restore completes without error
        let result = manager.restore(&backup_id);
        assert!(result.is_ok(), "Restore should complete without error");

        // Verify the working directory exists after restore
        assert!(
            working_dir.exists(),
            "Working directory should exist after restore"
        );
    }

    #[test]
    fn test_restore_with_multiple_files() {
        let (store_dir, working_dir) = setup_test_env("restore_multiple");

        // Create initial files
        create_test_file(&working_dir, "file1.txt", b"Content 1");
        create_test_file(&working_dir, "file2.txt", b"Content 2");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        let backup_id = manager
            .backup(Some("Two files".to_string()))
            .expect("Failed to create backup");

        // Modify and add files
        create_test_file(&working_dir, "file1.txt", b"Modified 1");
        create_test_file(&working_dir, "file3.txt", b"New file");
        fs::remove_file(working_dir.join("file2.txt")).expect("Failed to delete file2");

        // Test that restore completes without error
        let result = manager.restore(&backup_id);
        assert!(result.is_ok(), "Restore should complete without error");

        // Verify the working directory exists after restore
        assert!(
            working_dir.exists(),
            "Working directory should exist after restore"
        );
    }

    #[test]
    fn test_diff_no_changes() {
        let (store_dir, working_dir) = setup_test_env("diff_no_changes");

        create_test_file(&working_dir, "test.txt", b"Content");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        // Create first backup
        manager.backup(None).expect("Failed to create first backup");

        // Create second backup without any changes
        let backup_id = manager
            .backup(None)
            .expect("Failed to create second backup");

        // diff() compares the second backup with its parent (first backup)
        // Since there are no changes, should return empty
        let diffs = manager.diff(&backup_id).expect("Failed to get diff");
        assert_eq!(
            diffs.len(),
            0,
            "Should have no differences between identical backups"
        );
    }

    #[test]
    fn test_diff_modified_file() {
        let (store_dir, working_dir) = setup_test_env("diff_modified");

        create_test_file(&working_dir, "test.txt", b"Original content");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        // Create first backup
        manager.backup(None).expect("Failed to create first backup");

        // Modify the file
        create_test_file(&working_dir, "test.txt", b"Modified content");

        // Create second backup with modified file
        let backup_id = manager
            .backup(None)
            .expect("Failed to create second backup");

        // diff() compares second backup with its parent (first backup)
        let diffs = manager.diff(&backup_id).expect("Failed to get diff");
        assert_eq!(diffs.len(), 1, "Should have one modified file");
        assert_eq!(diffs[0].path, "test.txt", "Path should match");
        assert_eq!(
            diffs[0].content_before,
            Some(b"Original content".to_vec()),
            "Before content should match"
        );
        assert_eq!(
            diffs[0].content_after,
            Some(b"Modified content".to_vec()),
            "After content should match"
        );
    }

    #[test]
    fn test_diff_added_file() {
        let (store_dir, working_dir) = setup_test_env("diff_added");

        create_test_file(&working_dir, "existing.txt", b"Existing");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        // Create first backup
        manager.backup(None).expect("Failed to create first backup");

        // Add new file
        create_test_file(&working_dir, "new.txt", b"New content");

        // Create second backup with new file
        let backup_id = manager
            .backup(None)
            .expect("Failed to create second backup");

        // diff() compares second backup with its parent (first backup)
        let diffs = manager.diff(&backup_id).expect("Failed to get diff");
        assert_eq!(diffs.len(), 1, "Should have one added file");

        let added_file = diffs.iter().find(|d| d.path == "new.txt");
        assert!(added_file.is_some(), "Should find new.txt in diffs");
        assert_eq!(
            added_file.unwrap().content_before,
            None,
            "Before content should be None for added file"
        );
        assert_eq!(
            added_file.unwrap().content_after,
            Some(b"New content".to_vec()),
            "After content should match"
        );
    }

    #[test]
    fn test_diff_deleted_file() {
        let (store_dir, working_dir) = setup_test_env("diff_deleted");

        create_test_file(&working_dir, "to_delete.txt", b"Will be deleted");
        create_test_file(&working_dir, "to_keep.txt", b"Will be kept");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        // Create first backup with both files
        manager.backup(None).expect("Failed to create first backup");

        // Delete file
        fs::remove_file(working_dir.join("to_delete.txt")).expect("Failed to delete file");

        // Create second backup with file deleted
        let backup_id = manager
            .backup(None)
            .expect("Failed to create second backup");

        // diff() compares second backup with its parent (first backup)
        let diffs = manager.diff(&backup_id).expect("Failed to get diff");
        assert_eq!(diffs.len(), 1, "Should have one deleted file");

        let deleted_file = diffs.iter().find(|d| d.path == "to_delete.txt");
        assert!(deleted_file.is_some(), "Should find to_delete.txt in diffs");
        assert_eq!(
            deleted_file.unwrap().content_before,
            Some(b"Will be deleted".to_vec()),
            "Before content should match"
        );
        assert_eq!(
            deleted_file.unwrap().content_after,
            None,
            "After content should be None for deleted file"
        );
    }

    #[test]
    fn test_diff_multiple_changes() {
        let (store_dir, working_dir) = setup_test_env("diff_multiple");

        create_test_file(&working_dir, "modified.txt", b"Original");
        create_test_file(&working_dir, "deleted.txt", b"To delete");
        create_test_file(&working_dir, "unchanged.txt", b"Unchanged");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        // Create first backup
        manager.backup(None).expect("Failed to create first backup");

        // Make various changes
        create_test_file(&working_dir, "modified.txt", b"Modified");
        fs::remove_file(working_dir.join("deleted.txt")).expect("Failed to delete file");
        create_test_file(&working_dir, "added.txt", b"New file");

        // Create second backup with multiple changes
        let backup_id = manager
            .backup(None)
            .expect("Failed to create second backup");

        // diff() compares second backup with its parent (first backup)
        let diffs = manager.diff(&backup_id).expect("Failed to get diff");
        assert_eq!(
            diffs.len(),
            3,
            "Should have three changes (1 modified, 1 deleted, 1 added)"
        );
    }

    #[test]
    fn test_restore_invalid_backup_id() {
        let (store_dir, working_dir) = setup_test_env("restore_invalid");

        create_test_file(&working_dir, "test.txt", b"Content");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        manager.backup(None).expect("Failed to create backup");

        // Try to restore with invalid ID
        let result = manager.restore("invalid_backup_id_123");
        assert!(result.is_err(), "Should fail to restore invalid backup ID");
    }

    #[test]
    fn test_diff_invalid_backup_id() {
        let (store_dir, working_dir) = setup_test_env("diff_invalid");

        create_test_file(&working_dir, "test.txt", b"Content");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        manager.backup(None).expect("Failed to create backup");

        // Try to diff with invalid ID
        let result = manager.diff("invalid_backup_id_123");
        assert!(
            result.is_err(),
            "Should fail to diff with invalid backup ID"
        );
    }

    #[test]
    fn test_backup_empty_directory() {
        let (store_dir, working_dir) = setup_test_env("backup_empty");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        // Create backup of empty directory
        let backup_id = manager
            .backup(Some("Empty directory".to_string()))
            .expect("Failed to create backup of empty directory");

        assert!(
            !backup_id.is_empty(),
            "Should create backup even for empty directory"
        );
    }

    #[test]
    fn test_multiple_sequential_backups() {
        let (store_dir, working_dir) = setup_test_env("sequential");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        // Create multiple backups with changes
        for i in 1..=5 {
            create_test_file(
                &working_dir,
                "test.txt",
                format!("Content {}", i).as_bytes(),
            );
            let backup_id = manager
                .backup(Some(format!("Backup {}", i)))
                .expect(&format!("Failed to create backup {}", i));
            assert!(!backup_id.is_empty(), "Backup ID should not be empty");
        }

        let backups = manager.list().expect("Failed to list backups");
        assert_eq!(backups.len(), 5, "Should have 5 backups");
    }

    #[test]
    #[cfg(feature = "zip")]
    fn test_export_backup() {
        let (store_dir, working_dir) = setup_test_env("export");

        create_test_file(&working_dir, "test.txt", b"Content to export");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        let backup_id = manager
            .backup(Some("Export test".to_string()))
            .expect("Failed to create backup");

        let export_path = PathBuf::from("target/test_backup_manager/export_test.7z");
        let _ = fs::remove_file(&export_path); // Clean up if exists

        let result = manager.export(&backup_id, &export_path, 5);
        assert!(result.is_ok(), "Failed to export backup");
        assert!(export_path.exists(), "Export file should exist");
    }

    #[test]
    #[cfg(feature = "zip")]
    fn test_export_invalid_backup_id() {
        let (store_dir, working_dir) = setup_test_env("export_invalid");

        let manager =
            BackupManager::new(&store_dir, &working_dir).expect("Failed to create BackupManager");

        let export_path = PathBuf::from("target/test_backup_manager/export_invalid.7z");

        let result = manager.export("invalid_id_123", &export_path, 5);
        assert!(
            result.is_err(),
            "Should fail to export with invalid backup ID"
        );
    }
}
