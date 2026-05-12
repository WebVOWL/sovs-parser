//! Suite of tests based on the [VOWL](https://web.archive.org/web/20160120220406/http://vowl.visualdataweb.org/v2/) specification.
use std::path::PathBuf;

use crate::Specification;
use include_dir::{Dir, DirEntry, include_dir};

static TEST_SUITE_DIR: Dir<'_> = include_dir!("$CARGO_MANIFEST_DIR/test-suite");

/// A single test case
#[derive(Clone, Debug)]
pub struct TestCase {
    /// The expected SOVS graph for this test case.
    pub specification: Specification,
    /// The source code of the ontology of this test case.
    /// This may be in OFN, OWL-RDF, TTL, or OWL-XML format.
    /// The format of this text corresponds to the file extension of [`Self::name`]
    pub text: &'static str,
    /// The file name of this test case.
    pub name: &'static str,
}

/// An iterator of each test case in the test suite.
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

#[cfg(test)]
mod test {
    use crate::test_cases;

    #[test]
    fn all_test_cases_compile() {
        for x in test_cases() {
            std::hint::black_box(x);
        }
    }
}
