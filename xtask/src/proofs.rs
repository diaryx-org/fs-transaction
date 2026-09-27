//! `cargo xtask proofs`: Verus over the library, as it is.
//!
//! The proofs sit on the code that runs. A function that is proved carries
//! its specification in a `verus_spec` attribute, its proof sits beside it in
//! a module only Verus compiles, and all of it is behind `verus_keep_ghost`,
//! a cfg nothing but Verus sets — so an ordinary build compiles the same
//! function with none of it, and gains no dependency.
//!
//! Verus is a compiler driver, so it is run the way cargo runs any compiler:
//! `cargo check` builds every dependency with the Rust release Verus was built
//! against — none, with the default features — and hands the one compile that
//! is the library to `verus` instead of `rustc`, with the edition and the cfgs
//! cargo would give `rustc`. The hand-off is this program:
//! cargo calls it as `RUSTC_WORKSPACE_WRAPPER`, and [`wrap`] passes the
//! library to Verus and everything else through. Verus brings its own
//! verified standard library, so the manifest names nothing it needs.
//!
//! Verus writes no metadata for the library, so cargo never counts the
//! verification as done and runs it every time: a green run is a run.
//!
//! The prover is a release bundle — the driver, Z3, and `vstd`, built against
//! one Rust toolchain — pinned in [`VERUS`] and fetched once per release into
//! a cache outside the checkout.

use std::env;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use crate::{Result, Sh};

/// The Verus release the library is verified with.
///
/// Moved by hand, with the proofs re-run in the same commit: a proof that
/// verifies under one release can be refused by the next, when the prover's
/// triggers or its standard library change underneath it.
const VERUS: &str = "0.2026.09.20.aef82ed";

/// Set by [`proofs`] for the `cargo check` it runs, naming the `verus` driver.
/// Its presence is what tells this program it was called as the wrapper.
pub(crate) const WRAPPER: &str = "FS_TRANSACTION_XTASK_VERUS";

pub(crate) fn proofs(sh: &Sh) -> Result<()> {
    let verus = verus(sh)?;
    let bundle = verus
        .parent()
        .ok_or_else(|| format!("{} is not inside a Verus bundle", verus.display()))?;
    let toolchain = toolchain(bundle)?;
    // Idempotent: rustup reports an already-installed toolchain and returns 0.
    sh.run(
        "rustup",
        &[
            "toolchain",
            "install",
            &toolchain,
            "--profile",
            "minimal",
            "--no-self-update",
        ],
    )
    .map_err(|e| {
        format!("{e}\n\nVerus {VERUS} is built against Rust {toolchain}, which rustup installs")
    })?;

    let wrapper = env::current_exe()
        .map_err(|e| format!("could not find this program to hand cargo: {e}"))?;
    // Beside the ordinary build rather than in it, because every dependency
    // here is compiled by another Rust release; and per Verus release, so a
    // new one never meets what the last one left.
    let target = sh.root.join("target").join("verus").join(VERUS);
    sh.run_with(
        &[
            ("RUSTC_WORKSPACE_WRAPPER", &wrapper.to_string_lossy()),
            (WRAPPER, &verus.to_string_lossy()),
            ("CARGO_TARGET_DIR", &target.to_string_lossy()),
        ],
        "rustup",
        // `rustup run`, for `msrv`'s reason: `cargo +toolchain` is a proxy
        // feature, and $CARGO may point past the proxy.
        &[
            "run",
            &toolchain,
            "cargo",
            "check",
            "--package",
            "fs-transaction",
            "--lib",
        ],
    )
}

/// This program as cargo's `RUSTC_WORKSPACE_WRAPPER`: called as `<rustc>
/// <arguments>` for each workspace crate cargo compiles, it compiles the
/// library with `verus` and anything else with the `rustc` it was given.
///
/// Verus takes rustc's arguments — cargo's `--extern`s for the dependencies
/// it built, its `--cfg`s for the features, the edition — and verifies as it
/// compiles.
pub(crate) fn wrap(verus: OsString) -> ExitCode {
    let mut arguments = env::args_os().skip(1);
    let Some(rustc) = arguments.next() else {
        eprintln!("xtask: called as a compiler wrapper with no compiler");
        return ExitCode::FAILURE;
    };
    let arguments: Vec<OsString> = arguments.collect();
    let program = if is_the_library(&arguments) {
        verus
    } else {
        rustc
    };
    match Command::new(&program).args(&arguments).status() {
        Ok(status) => match status.code() {
            Some(0) => ExitCode::SUCCESS,
            Some(code) => ExitCode::from(u8::try_from(code).unwrap_or(1)),
            None => ExitCode::FAILURE,
        },
        Err(error) => {
            eprintln!(
                "xtask: could not run {}: {error}",
                Path::new(&program).display()
            );
            ExitCode::FAILURE
        }
    }
}

/// Whether a compile is the library's: `--crate-name fs_transaction` and
/// `--crate-type lib`. The test harness compiles the same crate name as a
/// binary, and `xtask` is a crate of its own.
fn is_the_library(arguments: &[OsString]) -> bool {
    let value = |flag: &str| {
        arguments
            .windows(2)
            .find(|pair| pair[0] == flag)
            .map(|pair| pair[1].clone())
    };
    value("--crate-name").is_some_and(|name| name == "fs_transaction")
        && value("--crate-type").is_some_and(|kind| kind == "lib")
}

// ---------------------------------------------------------------------------
// The prover
// ---------------------------------------------------------------------------

/// The `verus` driver: `$VERUS` if it is set, otherwise the pinned release,
/// fetched on first use.
fn verus(sh: &Sh) -> Result<PathBuf> {
    match env::var_os("VERUS") {
        Some(given) => Ok(PathBuf::from(given)),
        None => fetched(sh),
    }
}

/// The pinned release, from the cache or from GitHub.
///
/// The cache is per user rather than per checkout — the bundle is 1.4 GB
/// unpacked, and every worktree of this repository wants the same one — and
/// is keyed by release, so moving [`VERUS`] fetches the new one beside the
/// old. It is unpacked under a temporary name and renamed into place, so an
/// interrupted fetch leaves nothing a later run would mistake for a bundle.
fn fetched(sh: &Sh) -> Result<PathBuf> {
    let platform = platform()?;
    let cache = cache_directory(sh).join("verus").join(VERUS);
    let bundle = cache.join(format!("verus-{platform}"));
    let driver = bundle.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    if driver.exists() {
        return Ok(driver);
    }

    let archive = format!("verus-{VERUS}-{platform}.zip");
    let url =
        format!("https://github.com/verus-lang/verus/releases/download/release/{VERUS}/{archive}");
    let partial = cache.join("partial");
    let _ = std::fs::remove_dir_all(&partial);
    std::fs::create_dir_all(&partial)
        .map_err(|e| format!("could not create {}: {e}", partial.display()))?;
    let zip = partial.join(&archive);
    println!(
        "fetching Verus {VERUS} for {platform}, once, into {}",
        cache.display()
    );
    sh.run(
        "curl",
        &[
            "--fail",
            "--location",
            "--silent",
            "--show-error",
            "--output",
            &zip.to_string_lossy(),
            &url,
        ],
    )?;
    sh.run(
        "unzip",
        &[
            "-q",
            &zip.to_string_lossy(),
            "-d",
            &partial.to_string_lossy(),
        ],
    )?;
    std::fs::rename(partial.join(format!("verus-{platform}")), &bundle).map_err(|e| {
        format!(
            "could not move the unpacked bundle into {}: {e}",
            bundle.display()
        )
    })?;
    let _ = std::fs::remove_dir_all(&partial);
    Ok(driver)
}

/// Where a fetched bundle is kept: the platform's per-user cache, or the
/// workspace's `target/` on a machine that names neither.
fn cache_directory(sh: &Sh) -> PathBuf {
    if let Some(cache) = env::var_os("XDG_CACHE_HOME") {
        return PathBuf::from(cache);
    }
    if let Some(local) = env::var_os("LOCALAPPDATA") {
        return PathBuf::from(local);
    }
    match env::var_os("HOME") {
        Some(home) => PathBuf::from(home).join(".cache"),
        None => sh.root.join("target"),
    }
}

/// The platform half of a release's archive name.
fn platform() -> Result<&'static str> {
    match (env::consts::OS, env::consts::ARCH) {
        ("macos", "aarch64") => Ok("arm64-macos"),
        ("macos", "x86_64") => Ok("x86-macos"),
        ("linux", "x86_64") => Ok("x86-linux"),
        ("windows", "x86_64") => Ok("x86-win"),
        (os, arch) => Err(format!(
            "Verus publishes no release for {arch} {os}; build it and set VERUS to its `verus`"
        )),
    }
}

/// The Rust release a bundle was built against, from its `version.json`:
/// `"toolchain": "1.98.1-aarch64-apple-darwin …"` is `1.98.1`.
fn toolchain(bundle: &Path) -> Result<String> {
    let path = bundle.join("version.json");
    let text = std::fs::read_to_string(&path)
        .map_err(|e| format!("could not read {}: {e}", path.display()))?;
    text.split("\"toolchain\": \"")
        .nth(1)
        .and_then(|rest| rest.split(['-', '"']).next())
        .filter(|version| !version.is_empty())
        .map(str::to_owned)
        .ok_or_else(|| format!("no toolchain named in {}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn arguments(line: &str) -> Vec<OsString> {
        line.split_whitespace().map(OsString::from).collect()
    }

    /// cargo compiles `fs_transaction` more than one way in a workspace test
    /// run; only the library is Verus's.
    #[test]
    fn only_the_library_goes_to_verus() {
        assert!(is_the_library(&arguments(
            "--crate-name fs_transaction --edition=2024 src/lib.rs --crate-type lib --emit=dep-info,metadata"
        )));
        assert!(!is_the_library(&arguments(
            "--crate-name fs_transaction --edition=2024 src/lib.rs --test"
        )));
        assert!(!is_the_library(&arguments(
            "--crate-name xtask --edition=2024 xtask/src/main.rs --crate-type bin"
        )));
        assert!(!is_the_library(&arguments("-vV")));
    }

    #[test]
    fn a_toolchain_is_read_off_the_bundle() {
        let bundle = env::temp_dir().join(format!("fs-transaction-xtask-{}", std::process::id()));
        std::fs::create_dir_all(&bundle).unwrap();
        std::fs::write(
            bundle.join("version.json"),
            r#"{ "verus": { "toolchain": "1.98.1-aarch64-apple-darwin (overridden)" } }"#,
        )
        .unwrap();
        let found = toolchain(&bundle);
        std::fs::remove_dir_all(&bundle).unwrap();
        assert_eq!(found.unwrap(), "1.98.1");
    }
}
