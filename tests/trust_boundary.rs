//! What the Verus proofs take on trust lives in one file.
//!
//! `src/port.rs` holds the storage port's contract: wrappers whose bodies
//! Verus does not check and whose specs it takes as given. Nowhere else may
//! the source ask Verus to take anything on faith — no unchecked body, no
//! assumed fact, no admitted goal — so reviewing that one file is reviewing
//! everything the proofs rest on.

use std::path::Path;

const TRUST: &[&str] = &[
    "external_body",
    "assume_specification",
    "external_fn_specification",
    "assume(",
    "admit(",
];

fn visit(dir: &Path, found: &mut Vec<String>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            visit(&path, found);
        } else if path.extension().is_some_and(|e| e == "rs") && !path.ends_with("src/port.rs") {
            let text = std::fs::read_to_string(&path).unwrap();
            for (n, line) in text.lines().enumerate() {
                if TRUST.iter().any(|t| line.contains(t)) {
                    found.push(format!("{}:{}: {}", path.display(), n + 1, line.trim()));
                }
            }
        }
    }
}

#[test]
fn only_the_port_is_trusted() {
    let mut found = Vec::new();
    visit(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("src"),
        &mut found,
    );
    assert!(
        found.is_empty(),
        "trust outside src/port.rs:\n{}",
        found.join("\n")
    );
}
