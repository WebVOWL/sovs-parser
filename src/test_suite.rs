use std::path::PathBuf;

use crate::Specification;
use include_dir::{Dir, DirEntry, include_dir};

static TEST_SUITE_DIR: Dir<'_> = include_dir!("$CARGO_MANIFEST_DIR/test-suite");

#[derive(Clone, Debug)]
pub struct TestCase {
    pub specification: Specification,
    pub text: &'static str,
    pub name: &'static str,
}

pub fn test_cases() -> impl Iterator<Item = TestCase> {
    TEST_SUITE_DIR
        .find("**/*")
        .expect("glob pattern should be valid")
        .filter_map(|case| {
            let DirEntry::File(file) = case else {
                return None;
            };
            let name = file
                .path()
                .file_name()
                .expect("test case should have file name")
                .to_str()
                .expect("file name should be valid utf-8");

            if file
                .path()
                .extension()
                .expect("test case should have extension")
                == "sovs"
            {
                return None;
            }

            let case_name = case.path().file_stem().expect("test case should have stem");
            let sovs_file_name = PathBuf::from(case_name).with_extension("sovs");
            let sovs_path = PathBuf::from("sovs").join(sovs_file_name);
            let sovs_file = TEST_SUITE_DIR.get_file(&sovs_path)?;

            let specification = Specification::parse(
                sovs_file
                    .contents_utf8()
                    .expect("sovs file should be valid utf-8"),
            )
            .unwrap_or_else(|e| {
                panic!(
                    "sovs specification in {} should be valid: {e}",
                    sovs_path.display()
                )
            });

            let text = file
                .contents_utf8()
                .expect("test file should be valid utf-8");
            Some(TestCase {
                specification,
                text,
                name,
            })
        })
}
