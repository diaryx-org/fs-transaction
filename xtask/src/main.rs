//! The one CI job too big to be a command: `cargo xtask proofs`.
//!
//! CI itself is the `job` list in `.config/ship.figl`, run by `ship ci` here
//! and on the runners. Every job there is a plain command except `proofs`,
//! which fetches a pinned prover and drives cargo through it — real logic,
//! so it is a program, and the job runs it.
//!
//! Cutting a release does not live here either. It is `ship`, configured by
//! the same file.
//!
//! There are no dependencies on purpose. The `proofs` job builds this crate
//! before it can start.

mod proofs;

use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

/// Anything that goes wrong here is a message for whoever is reading the log;
/// there is nothing for a CI runner to recover from.
type Result<T> = std::result::Result<T, String>;

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
        ["proofs"] => proofs::proofs(&sh),
        // CI and releases moved to ship; say where rather than "unknown".
        ["ci" | "ci-matrix", ..] => Err(String::from(
            "CI is the `job` list in .config/ship.figl now: `ship ci` runs every job, \
             `ship ci <id>` one, and `ship ci --list` names them",
        )),
        [id] => Err(format!("unknown task `{id}`\n\n{}", usage())),
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

fn usage() -> String {
    String::from(
        "fs-transaction's xtask.\n\n\
         usage: cargo xtask <task>\n\n\
         \x20 proofs              Verus over the library, fetching the pinned release once\n\n\
         CI:         ship ci [<job>]   (the jobs are in .config/ship.figl)\n\
         releasing:  ship <command>    (see `ship help`)\n",
    )
}

// ---------------------------------------------------------------------------
// Running things
// ---------------------------------------------------------------------------

/// A shell rooted at the workspace, so a task never has to think about where it
/// was invoked from.
struct Sh {
    root: PathBuf,
}

impl Sh {
    fn new() -> Self {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("xtask/ always has a parent")
            .to_path_buf();
        Sh { root }
    }

    /// Run a command at the workspace root, echoing it first so a CI log reads
    /// as a transcript of commands anyone can paste back.
    fn run(&self, program: &str, args: &[&str]) -> Result<()> {
        self.run_with(&[], program, args)
    }

    /// The same, with environment — echoed in front of the command, since a
    /// transcript that leaves out what the command was told is not one.
    fn run_with(&self, environment: &[(&str, &str)], program: &str, args: &[&str]) -> Result<()> {
        let prefix: String = environment
            .iter()
            .map(|(name, value)| format!("{name}={value} "))
            .collect();
        println!("\x1b[2m$ {prefix}{} {}\x1b[0m", program, args.join(" "));

        let status = Command::new(program)
            .args(args)
            .envs(environment.iter().copied())
            .current_dir(&self.root)
            .status()
            .map_err(|e| format!("could not run `{program}`: {e}"))?;

        if status.success() {
            Ok(())
        } else {
            Err(format!(
                "`{prefix}{program} {}` failed ({status})",
                args.join(" ")
            ))
        }
    }
}
