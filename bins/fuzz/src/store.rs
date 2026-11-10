//! The campaign directory, shared by the supervisor and its workers through the file system only:
//!
//! ```text
//! <out>/campaign.txt                          the campaign's base seed and command line, appended per start
//! <out>/stats.txt                             the supervisor's latest per-target table
//! <out>/findings/<severity>/<target>/<key hash>/
//!     finding.txt                             key, first detail, how to reproduce, hit count
//!     case-<n>.bin                            up to MAX_CASES inputs that hit it (`repro --input`)
//! <out>/corpus/<target>/<hash>.bin            inputs that reached a new note, replayed with zeros after them; libFuzzer
//!                                             (`fuzz/campaign.sh`) reads and writes the same directory
//! <out>/corpus/<target>/notes.log             every note any worker reached, one per line
//! <out>/cache/                                targets' fixtures (`Ctx::dir`)
//! <out>/workers/<id>.case, <id>.stderr        the case a worker is running, and its stderr
//! ```

use fuzz::{Finding, Severity};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

const MAX_CASES: usize = 8;
const MAGIC: &[u8; 5] = b"LVFZ1";

/// A case: the prefix it reads first and the seed of the tail after it, if any.
#[derive(Clone, Debug)]
pub struct CaseInput {
    pub prefix: Vec<u8>,
    pub tail_seed: Option<u64>,
}

impl CaseInput {
    pub fn encode(&self) -> Vec<u8> {
        let mut out = MAGIC.to_vec();
        out.push(u8::from(self.tail_seed.is_some()));
        out.extend(self.tail_seed.unwrap_or(0).to_le_bytes());
        out.extend(&self.prefix);
        out
    }

    /// A case file, or raw bytes (a corpus entry, a libFuzzer artifact) read with zeros after them.
    pub fn decode(bytes: &[u8]) -> Self {
        match bytes.strip_prefix(MAGIC.as_slice()) {
            Some(rest) if rest.len() >= 9 => Self {
                tail_seed: (rest[0] == 1).then(|| u64::from_le_bytes(rest[1..9].try_into().unwrap())),
                prefix: rest[9..].to_vec(),
            },
            _ => Self {
                prefix: bytes.to_vec(),
                tail_seed: None,
            },
        }
    }

    pub fn source(&self) -> fuzz::Source {
        fuzz::Source::new(self.prefix.clone(), self.tail_seed)
    }
}

/// Whether `text` starts with `pattern`, where each `*` in the pattern stands for any run of characters.
fn glob_prefix(pattern: &str, text: &str) -> bool {
    let mut parts = pattern.split('*');
    let Some(first) = parts.next() else { return true };
    let Some(mut rest) = text.strip_prefix(first) else {
        return false;
    };
    for part in parts {
        match rest.find(part) {
            Some(i) => rest = &rest[i + part.len()..],
            None => return false,
        }
    }
    true
}

/// FNV-1a, for file names: stable across builds and platforms.
pub fn hash(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, &b| {
        (h ^ b as u64).wrapping_mul(0x0100_0000_01b3)
    })
}

pub struct Store {
    pub out: PathBuf,
    suppressions: Vec<String>,
}

impl Store {
    pub fn new(out: &Path) -> Self {
        for dir in ["findings", "corpus", "cache", "workers"] {
            let _ = fs::create_dir_all(out.join(dir));
        }
        let repo = include_str!("../../../crates/fuzz/suppressions.txt");
        let campaign = fs::read_to_string(out.join("suppressions.txt")).unwrap_or_default();
        let suppressions = repo
            .lines()
            .chain(campaign.lines())
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(str::to_string)
            .collect();
        Self {
            out: out.to_path_buf(),
            suppressions,
        }
    }

    pub fn cache_dir(&self) -> PathBuf {
        self.out.join("cache")
    }

    pub fn worker_file(&self, id: &str, ext: &str) -> PathBuf {
        self.out.join("workers").join(format!("{id}.{ext}"))
    }

    /// Record a finding. Returns whether its key is new to the campaign.
    pub fn record(&self, target: &str, finding: &Finding, case: &CaseInput) -> bool {
        let suppressed = self.suppressed(target, &finding.key);
        let dir = self
            .out
            .join("findings")
            .join(if suppressed {
                "suppressed"
            } else {
                finding.severity.as_str()
            })
            .join(target)
            .join(format!("{:016x}", hash(finding.key.as_bytes())));
        // Creating the directory is the lock: exactly one recorder writes the first report.
        let new = fs::create_dir_all(dir.parent().unwrap()).is_ok() && fs::create_dir(&dir).is_ok();
        let cases = fs::read_dir(&dir).map_or(0, |d| d.count());
        if cases <= MAX_CASES {
            let _ = fs::write(dir.join(format!("case-{}.bin", hash(&case.encode()))), case.encode());
        }
        let hits = dir.join("hits");
        let _ = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&hits)
            .and_then(|mut f| f.write_all(b"."));
        if new {
            let case_file = dir.join(format!("case-{}.bin", hash(&case.encode())));
            let report = format!(
                "target:   {target}\nseverity: {}\nkey:      {}\n\nreproduce:\n  cargo leanvm-fuzz repro {target} --input {}\n\n{}\n",
                finding.severity.as_str(),
                finding.key,
                case_file.display(),
                finding.detail,
            );
            let _ = fs::write(dir.join("finding.txt"), report);
        }
        new && !suppressed
    }

    pub fn suppressed(&self, target: &str, key: &str) -> bool {
        let full = format!("{target} {key}");
        self.suppressions.iter().any(|pattern| glob_prefix(pattern, &full))
    }

    pub fn corpus_dir(&self, target: &str) -> PathBuf {
        let dir = self.out.join("corpus").join(target);
        let _ = fs::create_dir_all(&dir);
        dir
    }

    pub fn corpus(&self, target: &str) -> Vec<Vec<u8>> {
        let Ok(entries) = fs::read_dir(self.corpus_dir(target)) else {
            return Vec::new();
        };
        entries
            .filter_map(Result::ok)
            .map(|e| e.path())
            // libFuzzer shares the directory and names its entries by hash, without an extension.
            .filter(|p| {
                p.is_file()
                    && p.file_name()
                        .is_some_and(|n| n != "notes.log" && !n.to_string_lossy().starts_with('.'))
            })
            .filter_map(|p| fs::read(p).ok())
            .collect()
    }

    pub fn known_notes(&self, target: &str) -> std::collections::BTreeSet<String> {
        fs::read_to_string(self.corpus_dir(target).join("notes.log"))
            .unwrap_or_default()
            .lines()
            .map(str::to_string)
            .collect()
    }

    /// Keep an input that reached `notes`, which no earlier case of the target reached.
    pub fn add_to_corpus(&self, target: &str, input: &[u8], notes: &[String]) {
        let dir = self.corpus_dir(target);
        let _ = fs::write(dir.join(format!("{:016x}.bin", hash(input))), input);
        if let Ok(mut log) = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(dir.join("notes.log"))
        {
            let _ = log.write_all(
                notes
                    .iter()
                    .map(|n| format!("{}\n", n.replace('\n', " ")))
                    .collect::<String>()
                    .as_bytes(),
            );
        }
    }

    /// Every recorded finding: severity, target, key, hits, directory.
    pub fn findings(&self) -> Vec<(Severity, String, String, usize, PathBuf)> {
        let mut out = Vec::new();
        let root = self.out.join("findings");
        for severity in [Severity::Critical, Severity::High, Severity::Medium, Severity::Low] {
            let Ok(targets) = fs::read_dir(root.join(severity.as_str())) else {
                continue;
            };
            for target in targets.filter_map(Result::ok) {
                let Ok(keys) = fs::read_dir(target.path()) else {
                    continue;
                };
                for key in keys.filter_map(Result::ok) {
                    let report = fs::read_to_string(key.path().join("finding.txt")).unwrap_or_default();
                    let key_line = report
                        .lines()
                        .find_map(|l| l.strip_prefix("key:"))
                        .unwrap_or("?")
                        .trim()
                        .to_string();
                    let hits = fs::metadata(key.path().join("hits")).map_or(0, |m| m.len() as usize);
                    out.push((
                        severity,
                        target.file_name().to_string_lossy().into_owned(),
                        key_line,
                        hits,
                        key.path(),
                    ));
                }
            }
        }
        out
    }
}
