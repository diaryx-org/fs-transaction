//! fs-transaction's CI, as one program.
//!
//! Every job the CI workflow runs is one entry in [`JOBS`] and one
//! `cargo xtask <id>` invocation. The workflow itself holds no build knowledge:
//! it asks `cargo xtask ci-matrix` what the jobs are, then runs each one by id.
//! Adding, renaming, reordering, or retiring a job is an edit to this file and
//! nothing else — the YAML does not change.
//!
//! Locally, `cargo xtask ci` runs the same jobs in the same order against the
//! same commands, so a green run here is a green run there.
//!
//! Cutting a release does not live here. It is `dx <command>`, the shared
//! tooling configured by `.config/release.toml`.
//!
//! There are no dependencies on purpose. Every CI job builds this crate before
//! it can start, so its build time is paid several times over per push.

mod proofs;

use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

/// Anything that goes wrong here is a message for whoever is reading the log;
/// there is nothing for a CI runner to recover from.
type Result<T> = std::result::Result<T, String>;

/// One CI job: what to call it, where it runs, what the runner must install
/// for it, and the work itself.
struct Job {
    /// `cargo xtask <id>`, and the key the workflow dispatches on.
    id: &'static str,
    /// The name GitHub shows in the checks list. Renaming it renames the
    /// required status check, so branch protection has to be updated to match.
    name: &'static str,
    /// The GitHub runner the job asks for.
    runner: &'static str,
    /// rustup components the job needs, comma-joined for
    /// `dtolnay/rust-toolchain`. Empty means the default toolchain is enough.
    components: &'static str,
    /// Does this job *compile* the crate? If so, restoring the cargo cache is
    /// worth its cost. `fmt` only ever parses, and `proofs` builds into a
    /// target directory of its own.
    builds: bool,
    /// One line of explanation, printed by `cargo xtask` with no arguments.
    about: &'static str,
    run: fn(&Sh) -> Result<()>,
}

/// The whole of CI, in the order `cargo xtask ci` runs it: cheapest and most
/// likely to fail first.
const JOBS: &[Job] = &[
    Job {
        id: "fmt",
        name: "Format",
        runner: "ubuntu-latest",
        components: "rustfmt",
        builds: false,
        about: "rustfmt, in check mode",
        run: fmt,
    },
    Job {
        id: "clippy",
        name: "Clippy",
        runner: "ubuntu-latest",
        components: "clippy",
        builds: true,
        about: "clippy over every target and feature, warnings denied",
        run: clippy,
    },
    Job {
        id: "doc",
        name: "Doc",
        runner: "ubuntu-latest",
        components: "",
        builds: true,
        about: "rustdoc over every feature, warnings denied",
        run: doc,
    },
    Job {
        id: "test",
        name: "Test",
        runner: "ubuntu-latest",
        components: "",
        builds: true,
        about: "the workspace test suite",
        run: test,
    },
    Job {
        id: "apple",
        name: "Apple",
        runner: "macos-latest",
        components: "clippy",
        builds: true,
        about: "clippy and the tests with `barrier-fsync`, which only Apple compiles",
        run: apple,
    },
    Job {
        id: "msrv",
        name: "MSRV",
        runner: "ubuntu-latest",
        components: "",
        builds: true,
        about: "build on the minimum supported Rust version",
        run: msrv,
    },
    Job {
        id: "proofs",
        name: "Proofs",
        runner: "ubuntu-latest",
        components: "",
        builds: false,
        about: "Verus over the library, fetching the pinned release once",
        run: proofs::proofs,
    },
];

// ---------------------------------------------------------------------------
// The jobs
// ---------------------------------------------------------------------------

fn fmt(sh: &Sh) -> Result<()> {
    sh.cargo(&["fmt", "--all", "--check"])
}

/// Warnings are errors in CI, so they are errors here too — a lint that only
/// fires on the runner is a lint found too late.
fn clippy(sh: &Sh) -> Result<()> {
    sh.cargo(&[
        "clippy",
        "--workspace",
        "--all-targets",
        "--all-features",
        "--",
        "-D",
        "warnings",
    ])
}

/// rustdoc, held to the same standard as the compiler: a link to an item that
/// was renamed still compiles, and renders as plain text on docs.rs.
fn doc(sh: &Sh) -> Result<()> {
    sh.cargo_with(
        &[("RUSTDOCFLAGS", "-D warnings")],
        &["doc", "--workspace", "--all-features", "--no-deps"],
    )
}

fn test(sh: &Sh) -> Result<()> {
    sh.cargo(&["test", "--workspace"])
}

/// `barrier-fsync` answers an ordered sync with `F_BARRIERFSYNC`, and the code
/// that does is compiled on Apple platforms alone. Anywhere else the feature
/// builds nothing, so `clippy` and `test` cannot see it; this job asks for a
/// Mac. Run locally off a Mac it checks nothing the others do not.
fn apple(sh: &Sh) -> Result<()> {
    sh.cargo(&[
        "clippy",
        "--all-targets",
        "--features",
        "barrier-fsync",
        "--",
        "-D",
        "warnings",
    ])?;
    sh.cargo(&["test", "--features", "barrier-fsync"])
}

/// Build on the crate's declared minimum supported Rust version. A build, not a
/// test run: MSRV is a promise about who can *compile* fs-transaction, and the
/// test tooling need not hold to it.
///
/// The version is read from `rust-version` in Cargo.toml, so the pin can never
/// drift from the declared floor — bump it there and this follows.
fn msrv(sh: &Sh) -> Result<()> {
    let version = sh.rust_version()?;
    println!("MSRV from Cargo.toml: {version}");
    // Idempotent: rustup reports an already-installed toolchain and returns 0.
    sh.run(
        "rustup",
        &[
            "toolchain",
            "install",
            &version,
            "--profile",
            "minimal",
            "--no-self-update",
        ],
    )
    .map_err(|e| format!("{e}\n\nthe MSRV job needs rustup on PATH to pin Rust {version}"))?;
    // `rustup run`, not `cargo +{version}`: the `+toolchain` shorthand is a
    // rustup-proxy feature, and $CARGO may well point past the proxy at a real
    // toolchain binary that does not understand it.
    sh.run(
        "rustup",
        &[
            "run",
            &version,
            "cargo",
            "build",
            "--package",
            "fs-transaction",
            "--all-features",
        ],
    )
}

// ---------------------------------------------------------------------------
// Driving them
// ---------------------------------------------------------------------------

fn main() -> ExitCode {
    // Called by cargo as the compiler wrapper the `proofs` job sets up, not by
    // a person — and before `env::args`, which would refuse a path cargo
    // passed that is not UTF-8.
    if let Some(verus) = env::var_os(proofs::WRAPPER) {
        return proofs::wrap(verus);
    }

    let args: Vec<String> = env::args().skip(1).collect();
    let sh = Sh::new();

    let outcome = match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        [] | ["-h" | "--help" | "help"] => {
            print!("{}", usage());
            return ExitCode::SUCCESS;
        }
        ["ci"] => ci(&sh),
        ["ci-matrix"] => {
            println!("{}", ci_matrix());
            Ok(())
        }
        [id] => match JOBS.iter().find(|job| job.id == id) {
            Some(job) => (job.run)(&sh),
            None => Err(format!("unknown job `{id}`\n\n{}", usage())),
        },
        [id, ..] => Err(format!("`{id}` takes no arguments\n\n{}", usage())),
    };

    match outcome {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("\nxtask: {message}");
            ExitCode::FAILURE
        }
    }
}

/// Every job, in order — what CI does, on one machine. Stops at the first
/// failure, on the theory that a red build is worth reading before the next one
/// buries it.
fn ci(sh: &Sh) -> Result<()> {
    for job in JOBS {
        println!("\n\x1b[1m━━ {} ━━\x1b[0m", job.name);
        (job.run)(sh)?;
    }
    println!("\n\x1b[32mall {} jobs passed\x1b[0m", JOBS.len());
    Ok(())
}

/// The job table as a single line of JSON, for the workflow's `strategy.matrix`.
///
/// Hand-rolled rather than serde-derived: the crate has no dependencies, and
/// every value here is a `&'static str` literal from [`JOBS`] with nothing in it
/// that JSON would need escaped — which the test below checks.
fn ci_matrix() -> String {
    let entries: Vec<String> = JOBS
        .iter()
        .map(|job| {
            format!(
                r#"{{"id":"{}","name":"{}","runner":"{}","components":"{}","builds":{}}}"#,
                job.id, job.name, job.runner, job.components, job.builds
            )
        })
        .collect();
    format!("[{}]", entries.join(","))
}

fn usage() -> String {
    let mut out = String::from(
        "fs-transaction's CI. Each job below is exactly what the CI workflow runs.\n\n\
         usage: cargo xtask <command>\n\njobs:\n\n",
    );
    for job in JOBS {
        out.push_str(&format!("  {:<20}{}\n", job.id, job.about));
    }
    out.push_str(&format!("  {:<20}{}\n", "ci", "every job above, in order"));
    out.push_str(&format!(
        "  {:<20}{}\n",
        "ci-matrix", "the job table as JSON, for the workflow matrix"
    ));
    out.push_str("\nreleasing:  dx <command>   (the shared tooling; see .config/release.toml)\n");
    out
}

// ---------------------------------------------------------------------------
// Running things
// ---------------------------------------------------------------------------

/// A shell rooted at the workspace, so a job never has to think about where it
/// was invoked from.
struct Sh {
    root: PathBuf,
    /// Cargo tells its subprocesses which cargo it is; prefer that over
    /// whichever one happens to be first on PATH.
    cargo: String,
}

impl Sh {
    fn new() -> Self {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask/ always has a parent")
            .to_path_buf();
        let cargo = env::var("CARGO").unwrap_or_else(|_| "cargo".into());
        Sh { root, cargo }
    }

    fn cargo(&self, args: &[&str]) -> Result<()> {
        let cargo = self.cargo.clone();
        self.run(&cargo, args)
    }

    /// The same, with environment the job wants the command to see.
    fn cargo_with(&self, environment: &[(&str, &str)], args: &[&str]) -> Result<()> {
        let cargo = self.cargo.clone();
        self.run_with(environment, &cargo, args)
    }

    /// Run a command at the workspace root, echoing it first so a CI log reads
    /// as a transcript of commands anyone can paste back.
    fn run(&self, program: &str, args: &[&str]) -> Result<()> {
        self.run_with(&[], program, args)
    }

    /// The same, with environment — echoed in front of the command, since a
    /// transcript that leaves out what the command was told is not one.
    fn run_with(&self, environment: &[(&str, &str)], program: &str, args: &[&str]) -> Result<()> {
        let shown = if program == self.cargo {
            "cargo"
        } else {
            program
        };
        let prefix: String = environment
            .iter()
            .map(|(name, value)| format!("{name}={value} "))
            .collect();
        println!("\x1b[2m$ {prefix}{} {}\x1b[0m", shown, args.join(" "));

        let status = Command::new(program)
            .args(args)
            .envs(environment.iter().copied())
            .current_dir(&self.root)
            .status()
            .map_err(|e| format!("could not run `{shown}`: {e}"))?;

        if status.success() {
            Ok(())
        } else {
            Err(format!(
                "`{prefix}{shown} {}` failed ({status})",
                args.join(" ")
            ))
        }
    }

    /// `rust-version` in the root manifest, the single source of truth for the
    /// MSRV.
    fn rust_version(&self) -> Result<String> {
        let manifest = self.root.join("Cargo.toml");
        let text = std::fs::read_to_string(&manifest)
            .map_err(|e| format!("could not read {}: {e}", manifest.display()))?;
        text.lines()
            .find_map(|line| line.trim().strip_prefix("rust-version")?.split('"').nth(1))
            .map(str::to_owned)
            .ok_or_else(|| format!("no `rust-version` in {}", manifest.display()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The workflow's `fromJSON` is the only thing that parses `ci-matrix`, and
    /// it fails at a point where the fix costs a push. Check the shape here
    /// instead: one object per job, every field present, nothing needing an
    /// escape.
    #[test]
    fn ci_matrix_is_well_formed_json() {
        let json = ci_matrix();
        assert!(json.starts_with('[') && json.ends_with(']'));
        assert_eq!(json.matches("\"id\":").count(), JOBS.len());
        assert_eq!(json.lines().count(), 1, "the workflow reads it as one line");

        for job in JOBS {
            for field in [job.id, job.name, job.runner, job.components] {
                assert!(
                    !field.contains(['"', '\\']),
                    "`{field}` would need JSON escaping, which ci_matrix does not do",
                );
            }
            assert!(json.contains(&format!("\"id\":\"{}\"", job.id)));
        }
    }

    /// `ci` and `ci-matrix` are handled before the table is consulted, so a job
    /// by either name would be unreachable.
    #[test]
    fn job_ids_are_distinct_and_dispatchable() {
        let mut ids: Vec<&str> = JOBS.iter().map(|job| job.id).collect();
        let count = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), count, "duplicate job id");
        assert!(!ids.contains(&"ci") && !ids.contains(&"ci-matrix"));
    }

    /// The MSRV job reads this; if the parse breaks, the job silently pins the
    /// wrong compiler or fails far from the cause.
    #[test]
    fn msrv_is_readable_from_the_manifest() {
        let version = Sh::new().rust_version().unwrap();
        assert!(
            version.split('.').all(|part| part.parse::<u32>().is_ok()),
            "`{version}` does not look like a Rust version",
        );
    }
}
