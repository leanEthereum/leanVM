//! The EthLib test vectors' format, shared by leanXMSS's and leanSPHINCS's tests: each case is a
//! `data.yaml` under `tests/<crate>/ethlib/<handler>/<case>/`.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// One value of a case, as EthLib writes it.
#[derive(Debug, PartialEq)]
pub(crate) enum Value {
    /// `'0x…'`: a byte string.
    Bytes(Vec<u8>),
    /// A decimal integer.
    Int(u64),
    /// `true` or `false`.
    Bool(bool),
    /// `null`: the input is rejected.
    Null,
}

/// One case: its name, its named inputs and its output.
pub(crate) struct Case {
    pub(crate) name: String,
    pub(crate) input: BTreeMap<String, Value>,
    pub(crate) output: Value,
}

impl Case {
    /// The byte string input `key`.
    pub(crate) fn bytes(&self, key: &str) -> &[u8] {
        match self.input.get(key) {
            Some(Value::Bytes(bytes)) => bytes,
            other => panic!("{}: input {key} is {other:?}, not bytes", self.name),
        }
    }
}

/// Decode `0x`-prefixed hex.
pub(crate) fn hex(s: &str) -> Vec<u8> {
    let digits = s.strip_prefix("0x").expect("hex starts with 0x");
    assert!(digits.len().is_multiple_of(2), "odd hex length");
    (0..digits.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&digits[i..i + 2], 16).expect("hex digit"))
        .collect()
}

/// One scalar, in the subset of YAML EthLib's cases use.
pub(crate) fn value(s: &str) -> Value {
    match s {
        "null" => Value::Null,
        "true" => Value::Bool(true),
        "false" => Value::Bool(false),
        _ => match s.strip_prefix('\'').and_then(|s| s.strip_suffix('\'')) {
            Some(quoted) => Value::Bytes(hex(quoted)),
            None => Value::Int(s.parse().unwrap_or_else(|_| panic!("unknown value {s}"))),
        },
    }
}

/// Read one `data.yaml`, rejecting any line outside its fixed shape:
///
/// ```text
/// input:
///   <key>: <value>
///   ...
/// output: <value>
/// ```
pub(crate) fn parse(name: String, text: &str) -> Case {
    let mut lines = text.lines();
    assert_eq!(lines.next(), Some("input:"), "{name}: no input");
    let mut input = BTreeMap::new();
    for line in lines.by_ref() {
        // The indented lines are the inputs, and the first unindented one the output.
        let Some(field) = line.strip_prefix("  ") else {
            let output = line
                .strip_prefix("output: ")
                .unwrap_or_else(|| panic!("{name}: bad line {line}"));
            assert!(lines.next().is_none(), "{name}: text after the output");
            return Case {
                name,
                input,
                output: value(output),
            };
        };
        let (key, raw) = field
            .split_once(": ")
            .unwrap_or_else(|| panic!("{name}: bad input {field}"));
        input.insert(key.to_owned(), value(raw));
    }
    panic!("{name}: no output")
}

/// Every case of one handler, in name order.
pub(crate) fn cases(handler: &str) -> Vec<Case> {
    let dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join(env!("CARGO_CRATE_NAME"))
        .join("ethlib")
        .join(handler);
    let mut names: Vec<String> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|entry| entry.unwrap())
        .filter(|entry| entry.file_type().unwrap().is_dir())
        .map(|entry| entry.file_name().into_string().unwrap())
        .collect();
    names.sort();
    assert!(!names.is_empty(), "no {handler} cases");
    names
        .into_iter()
        .map(|name| {
            let text = fs::read_to_string(dir.join(&name).join("data.yaml")).unwrap();
            parse(name, &text)
        })
        .collect()
}

/// The fixed-size array a byte string must fill, or `None` for any other length.
pub(crate) fn exact<const L: usize>(bytes: &[u8]) -> Option<[u8; L]> {
    bytes.try_into().ok()
}
