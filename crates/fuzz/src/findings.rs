//! What a failed oracle reports.

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Severity {
    /// Something false is accepted.
    Critical,
    /// Something true is refused, or computed wrong.
    High,
    /// A crash, hang or unbounded allocation where the input deserves an error.
    Medium,
    /// A panic on a path documented to panic, or a behaviour worth a look.
    Low,
}

impl Severity {
    pub fn as_str(self) -> &'static str {
        match self {
            Severity::Critical => "critical",
            Severity::High => "high",
            Severity::Medium => "medium",
            Severity::Low => "low",
        }
    }

    pub fn parse(s: &str) -> Option<Self> {
        [Severity::Critical, Severity::High, Severity::Medium, Severity::Low]
            .into_iter()
            .find(|v| v.as_str() == s)
    }
}

/// A failed oracle. `key` is what findings are deduplicated by, so it names the bug and nothing about the case: a
/// panic's location, an error variant, a mutated field, never a seed, an offset or a value.
#[derive(Clone, Debug)]
pub struct Finding {
    pub severity: Severity,
    pub key: String,
    pub detail: String,
}

impl Finding {
    pub fn new(severity: Severity, key: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            severity,
            key: key.into(),
            detail: detail.into(),
        }
    }

    pub fn critical(key: impl Into<String>, detail: impl Into<String>) -> Self {
        Self::new(Severity::Critical, key, detail)
    }

    pub fn high(key: impl Into<String>, detail: impl Into<String>) -> Self {
        Self::new(Severity::High, key, detail)
    }

    pub fn medium(key: impl Into<String>, detail: impl Into<String>) -> Self {
        Self::new(Severity::Medium, key, detail)
    }

    pub fn low(key: impl Into<String>, detail: impl Into<String>) -> Self {
        Self::new(Severity::Low, key, detail)
    }

    /// A caught panic, keyed by its location and its message with the numbers taken out.
    pub fn panic(message: &str, location: &str) -> Self {
        Self::medium(
            format!("panic at {location}: {}", normalize(message)),
            format!("panicked at {location}:\n{message}"),
        )
    }

    /// The same finding at another severity: a target that knows a panic on its path is documented re-ranks it.
    pub fn with_severity(mut self, severity: Severity) -> Self {
        self.severity = severity;
        self
    }

    /// Prefix the key, so one target's findings do not merge with another's.
    pub fn in_context(mut self, context: &str) -> Self {
        self.key = format!("{context}: {}", self.key);
        self
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}\n{}", self.severity.as_str(), self.key, self.detail)
    }
}

/// Collapse runs of digits and hex words to `#`, and cap the length: what keeps one bug at one key across cases.
pub fn normalize(message: &str) -> String {
    let mut out = String::with_capacity(message.len().min(200));
    let mut in_number = false;
    for c in message.chars().take(400) {
        if c.is_ascii_hexdigit() && (c.is_ascii_digit() || in_number) {
            if !in_number {
                out.push('#');
                in_number = true;
            }
        } else {
            in_number = false;
            out.push(c);
        }
    }
    out.truncate(200);
    out
}

/// `ensure!(cond, Severity::X, "key", "detail {}", args)`: return the finding when `cond` fails.
#[macro_export]
macro_rules! ensure {
    ($cond:expr, $severity:expr, $key:expr, $($detail:tt)+) => {
        if !$cond {
            return Err($crate::Finding::new($severity, $key, format!($($detail)+)));
        }
    };
}
