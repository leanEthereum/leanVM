//! The cases of `run/check.sh`: leanXMSS and leanSPHINCS inputs laid out as the native verifiers (x86-64 and AArch64,
//! one context layout) read them, each with what the crate's `verify` returns.
//!
//! `reference DIR` writes `DIR/<scheme>_<name>.case` for every case, and `DIR/cases.list`, their file stems in order.
//! A case is text: the lines `scheme xmss` (or `sphincs`), `expect 0` (or `1`), `words N`, then the `N` input words,
//! 16 hex digits each, one per line. The words are `X86/Xmss/Layout.lean`'s 309 or `X86/Sphincs/Layout.lean`'s 977
//! (`encode`): a 16-byte digest as two little-endian words, low first; the message as four; XMSS's leaf index and each
//! SPHINCS counter as one word holding its value. Every other field keeps its place in the crate's `to_bytes`.
//!
//! The cases, for each scheme: EthLib's `verify` vectors whose input has the right lengths (`ethlib_*`, the crate's
//! `verify` checked against EthLib's output), fresh keys and signatures (`valid_*`), and one signature changed in one
//! place (`wrong_*`, `flip_*`: a flipped bit in the first and in the last byte of a field, so in its low and its high
//! word).

use std::path::Path;
use std::{env, fs, process};

use lean_sphincs::internals::{COUNTER_LEN, FORS_HEIGHT, FORS_TREES, LAYER_HEIGHTS};
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_xmss::internals::{LAYER_HEIGHT, RANDOMIZER_LEN, V};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};

/// A digest's bytes, in both schemes.
const N: usize = 16;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Scheme {
    Xmss,
    Sphincs,
}

impl Scheme {
    fn name(self) -> &'static str {
        match self {
            Scheme::Xmss => "xmss",
            Scheme::Sphincs => "sphincs",
        }
    }
}

/// A public key, a message and a signature, as the crate's `to_bytes` lays them out.
#[derive(Clone)]
struct Input {
    scheme: Scheme,
    pk: Vec<u8>,
    message: Vec<u8>,
    sig: Vec<u8>,
}

fn array<const L: usize>(bytes: &[u8]) -> &[u8; L] {
    bytes.try_into().expect("a field of the right length")
}

/// Little-endian 64-bit words of whole 8-byte chunks.
fn le_words(bytes: &[u8]) -> impl Iterator<Item = u64> + '_ {
    let (chunks, rest) = bytes.as_chunks::<8>();
    assert!(rest.is_empty());
    chunks.iter().map(|chunk| u64::from_le_bytes(*chunk))
}

/// Where layer `l`'s signature starts in a leanSPHINCS signature: after `R` and the FORS openings.
fn sphincs_layer_offset(layer: usize) -> usize {
    let fors = N + FORS_TREES * (N + FORS_HEIGHT * N);
    fors + LAYER_HEIGHTS[..layer]
        .iter()
        .map(|h| COUNTER_LEN + lean_sphincs::internals::V * N + h * N)
        .sum::<usize>()
}

/// Where layer `l`'s signature starts in a leanXMSS signature: after the leaf index and the layers below.
fn xmss_layer_offset(layer: usize) -> usize {
    4 + layer * (RANDOMIZER_LEN + V * N + LAYER_HEIGHT * N)
}

impl Input {
    fn verify(&self) -> bool {
        match self.scheme {
            Scheme::Xmss => lean_xmss::verify(
                &LeanXmssPublicKey::from_bytes(array(&self.pk)),
                array(&self.message),
                &LeanXmssSignature::from_bytes(array(&self.sig)),
            ),
            Scheme::Sphincs => lean_sphincs::verify(
                &LeanSphincsPublicKey::from_bytes(array(&self.pk)),
                array(&self.message),
                &LeanSphincsSignature::from_bytes(array(&self.sig)),
            ),
        }
    }

    /// The input words, `encode` of the scheme's `Layout.lean`.
    fn words(&self) -> Vec<u64> {
        let mut words: Vec<u64> = le_words(&self.pk).chain(le_words(&self.message)).collect();
        match self.scheme {
            Scheme::Xmss => {
                words.push(u32::from_le_bytes(self.sig[..4].try_into().unwrap()).into());
                words.extend(le_words(&self.sig[4..]));
                assert_eq!(words.len(), 309);
            }
            Scheme::Sphincs => {
                let mut at = sphincs_layer_offset(0);
                words.extend(le_words(&self.sig[..at]));
                for h in LAYER_HEIGHTS {
                    words.push(u32::from_be_bytes(self.sig[at..at + COUNTER_LEN].try_into().unwrap()).into());
                    at += COUNTER_LEN;
                    let len = (lean_sphincs::internals::V + h) * N;
                    words.extend(le_words(&self.sig[at..at + len]));
                    at += len;
                }
                assert_eq!(at, self.sig.len());
                assert_eq!(words.len(), 977);
            }
        }
        words
    }

    fn with_pk(&self, pk: &[u8]) -> Input {
        Input {
            pk: pk.to_vec(),
            ..self.clone()
        }
    }
}

fn flip(bytes: &[u8], at: usize, bit: u32) -> Vec<u8> {
    let mut out = bytes.to_vec();
    out[at] ^= 1 << bit;
    out
}

struct Case {
    stem: String,
    expect: bool,
    words: Vec<u64>,
}

#[derive(Default)]
struct Cases(Vec<Case>);

impl Cases {
    /// A case expecting what the crate's `verify` returns, which it returns.
    fn add(&mut self, name: &str, input: &Input) -> bool {
        let stem = format!("{}_{name}", input.scheme.name());
        assert!(self.0.iter().all(|c| c.stem != stem), "{stem} twice");
        let expect = input.verify();
        self.0.push(Case {
            stem,
            expect,
            words: input.words(),
        });
        expect
    }

    fn valid(&mut self, name: &str, input: &Input) {
        assert!(self.add(name, input), "{name}: a fresh signature does not verify");
    }

    fn invalid(&mut self, name: &str, input: &Input) {
        assert!(!self.add(name, input), "{name}: a changed signature still verifies");
    }

    /// The signature with a bit flipped in the first byte and in the last of the `len` bytes at `at`.
    fn flip_sig(&mut self, name: &str, input: &Input, at: usize, len: usize) {
        for (suffix, byte, bit) in [("lo", at, 0), ("hi", at + len - 1, 7)] {
            let sig = flip(&input.sig, byte, bit);
            self.invalid(&format!("flip_{name}_{suffix}"), &Input { sig, ..input.clone() });
        }
    }

    /// Changed public keys and messages: each 16-byte half of the key and the message flipped.
    fn wrong_pk_and_message(&mut self, input: &Input, halves: [&str; 2]) {
        for (k, half) in halves.iter().enumerate() {
            self.flip_pk(&format!("wrong_{half}"), input, N * k);
        }
        for (suffix, byte, bit) in [("lo", 0, 0), ("hi", 31, 7)] {
            let message = flip(&input.message, byte, bit);
            self.invalid(
                &format!("wrong_message_{suffix}"),
                &Input {
                    message,
                    ..input.clone()
                },
            );
        }
    }

    fn flip_pk(&mut self, name: &str, input: &Input, at: usize) {
        for (suffix, byte, bit) in [("lo", at, 0), ("hi", at + N - 1, 7)] {
            self.invalid(&format!("{name}_{suffix}"), &input.with_pk(&flip(&input.pk, byte, bit)));
        }
    }
}

/// EthLib's verify cases of one crate whose inputs fit the fixed-size arrays (the others have no layout), checked
/// against EthLib's output. Returns each case's name and input.
fn ethlib_verify(scheme: Scheme) -> Vec<(String, Input)> {
    let crate_name = format!("lean_{}", scheme.name());
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../../crates")
        .join(&crate_name)
        .join("tests")
        .join(&crate_name)
        .join("ethlib/verify");
    let mut names: Vec<String> = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|entry| entry.unwrap())
        .filter(|entry| entry.file_type().unwrap().is_dir())
        .map(|entry| entry.file_name().into_string().unwrap())
        .collect();
    names.sort();
    let (pk_len, sig_len) = match scheme {
        Scheme::Xmss => (lean_xmss::PUB_KEY_SIZE, lean_xmss::SIG_SIZE),
        Scheme::Sphincs => (lean_sphincs::PUB_KEY_SIZE, lean_sphincs::SIG_SIZE),
    };
    let mut out = Vec::new();
    for name in names {
        let text = fs::read_to_string(dir.join(&name).join("data.yaml")).unwrap();
        let field = |key: &str| -> Vec<u8> {
            let prefix = format!("  {key}: '0x");
            let line = text
                .lines()
                .find_map(|l| l.strip_prefix(prefix.as_str()))
                .unwrap_or_else(|| panic!("{name}: no {key}"));
            let digits = line.strip_suffix('\'').expect("a quoted hex string");
            (0..digits.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&digits[i..i + 2], 16).expect("hex"))
                .collect()
        };
        let output = text
            .lines()
            .find_map(|l| l.strip_prefix("output: "))
            .unwrap_or_else(|| panic!("{name}: no output"));
        let input = Input {
            scheme,
            pk: field("public_key"),
            message: field("message"),
            sig: field("signature"),
        };
        if input.pk.len() != pk_len || input.message.len() != 32 || input.sig.len() != sig_len {
            assert_eq!(output, "null", "{name}: a wrong length that verifies");
            continue;
        }
        let expect = match output {
            "true" => true,
            "false" => false,
            _ => panic!("{name}: output {output} for inputs of the right lengths"),
        };
        assert_eq!(input.verify(), expect, "{name}: the crate disagrees with EthLib");
        out.push((name, input));
    }
    assert!(!out.is_empty(), "no EthLib cases in {}", dir.display());
    out
}

fn xmss_cases(cases: &mut Cases) {
    let ethlib = ethlib_verify(Scheme::Xmss);
    for (name, input) in &ethlib {
        cases.add(&format!("ethlib_{name}"), input);
    }
    let known_answer_pk = &ethlib
        .iter()
        .find(|(name, _)| name == "verify_valid_known_answer")
        .expect("EthLib's known answer")
        .1
        .pk;

    let (sk, pk) = lean_xmss::key_gen(&[1; lean_xmss::SECRET_KEY_LEN]);
    // Leaf indices across three bottom trees, so the top layer signs at three keys.
    let signed: [(&str, u32, [u8; 32]); 5] = [
        ("first_leaf", 0, [0; 32]),
        ("second_leaf", 1, [0xff; 32]),
        ("last_leaf_of_tree_0", 0xffff, std::array::from_fn(|i| i as u8)),
        (
            "tree_7",
            (7 << LAYER_HEIGHT) + 3,
            std::array::from_fn(|i| (i * 3 + 7) as u8),
        ),
        ("last_leaf", u32::MAX, std::array::from_fn(|i| 0xa5 ^ (i as u8))),
    ];
    std::thread::scope(|s| {
        for (_, leaf, _) in &signed {
            s.spawn(|| sk.prepare(*leaf));
        }
    });
    let mut base = None;
    for (name, leaf, message) in &signed {
        let input = Input {
            scheme: Scheme::Xmss,
            pk: pk.to_bytes().to_vec(),
            message: message.to_vec(),
            sig: lean_xmss::sign(&sk, message, *leaf).to_bytes().to_vec(),
        };
        cases.valid(&format!("valid_{name}"), &input);
        if *leaf == (7 << LAYER_HEIGHT) + 3 {
            base = Some(input);
        }
    }

    // One signature, at a leaf whose two layer indices are both nonzero, changed in one place.
    let base = base.unwrap();
    cases.wrong_pk_and_message(&base, ["root", "public_param"]);
    cases.invalid("wrong_key", &base.with_pk(known_answer_pk));
    for (name, byte, bit) in [
        ("leaf_index_bit_0", 0, 0),
        ("leaf_index_bit_16", 2, 0),
        ("leaf_index_bit_31", 3, 7),
    ] {
        cases.invalid(
            &format!("flip_{name}"),
            &Input {
                sig: flip(&base.sig, byte, bit),
                ..base.clone()
            },
        );
    }
    for (layer, layer_name) in ["bottom", "top"].iter().enumerate() {
        let at = xmss_layer_offset(layer);
        let chains = at + RANDOMIZER_LEN;
        let path = chains + V * N;
        cases.flip_sig(&format!("{layer_name}_randomizer"), &base, at, RANDOMIZER_LEN);
        cases.flip_sig(&format!("{layer_name}_chain_0"), &base, chains, N);
        cases.flip_sig(&format!("{layer_name}_chain_{}", V - 1), &base, chains + (V - 1) * N, N);
        cases.flip_sig(&format!("{layer_name}_path_0"), &base, path, N);
        cases.flip_sig(
            &format!("{layer_name}_path_{}", LAYER_HEIGHT - 1),
            &base,
            path + (LAYER_HEIGHT - 1) * N,
            N,
        );
    }
}

fn sphincs_cases(cases: &mut Cases) {
    for (name, input) in ethlib_verify(Scheme::Sphincs) {
        cases.add(&format!("ethlib_{name}"), &input);
    }

    let sign = |seed: [u8; 32], message: [u8; 32]| Input {
        scheme: Scheme::Sphincs,
        pk: lean_sphincs::key_gen(&seed).to_bytes().to_vec(),
        message: message.to_vec(),
        sig: lean_sphincs::sign(&seed, &message).to_bytes().to_vec(),
    };
    // The crate's known answer (`known_answer.hex`), regenerated from its seed and message.
    let known = sign(
        std::array::from_fn(|i| (37 * i + 11) as u8),
        std::array::from_fn(|i| (7 * i + 3) as u8),
    );
    let hex = include_str!("../../../../../crates/lean_sphincs/tests/lean_sphincs/known_answer.hex");
    let unhex = |s: &str| -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    };
    let mut lines = hex.lines();
    assert_eq!(known.pk, unhex(lines.next().unwrap()), "the known answer's public key");
    assert_eq!(known.sig, unhex(lines.next().unwrap()), "the known answer's signature");
    cases.valid("valid_known_answer", &known);
    let zero = sign([0; 32], [0; 32]);
    cases.valid("valid_zero_seed_zero_message", &zero);
    cases.valid("valid_ones_seed_ones_message", &sign([0xff; 32], [0xff; 32]));
    cases.valid(
        "valid_counting_seed",
        &sign(std::array::from_fn(|i| i as u8), std::array::from_fn(|i| 255 - i as u8)),
    );

    // The known answer changed in one place.
    cases.wrong_pk_and_message(&known, ["pk_seed", "root"]);
    cases.invalid("wrong_key", &known.with_pk(&zero.pk));
    cases.flip_sig("randomizer", &known, 0, N);
    for tree in [0, FORS_TREES - 1] {
        let at = N + tree * (N + FORS_HEIGHT * N);
        cases.flip_sig(&format!("fors_{tree}_secret"), &known, at, N);
        cases.flip_sig(&format!("fors_{tree}_path_0"), &known, at + N, N);
        let last = FORS_HEIGHT - 1;
        cases.flip_sig(&format!("fors_{tree}_path_{last}"), &known, at + N + last * N, N);
    }
    let v = lean_sphincs::internals::V;
    for (layer, h) in LAYER_HEIGHTS.iter().enumerate() {
        let at = sphincs_layer_offset(layer);
        let chains = at + COUNTER_LEN;
        let path = chains + v * N;
        cases.flip_sig(&format!("layer_{layer}_counter"), &known, at, COUNTER_LEN);
        cases.flip_sig(&format!("layer_{layer}_chain_0"), &known, chains, N);
        cases.flip_sig(
            &format!("layer_{layer}_chain_{}", v - 1),
            &known,
            chains + (v - 1) * N,
            N,
        );
        cases.flip_sig(&format!("layer_{layer}_path_0"), &known, path, N);
        cases.flip_sig(&format!("layer_{layer}_path_{}", h - 1), &known, path + (h - 1) * N, N);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let [_, dir] = args.as_slice() else {
        eprintln!("usage: reference DIR");
        process::exit(2);
    };
    let dir = Path::new(dir);
    fs::create_dir_all(dir).unwrap();
    let mut cases = Cases::default();
    xmss_cases(&mut cases);
    sphincs_cases(&mut cases);

    let mut list = String::new();
    for case in &cases.0 {
        let mut text = format!(
            "scheme {}\nexpect {}\nwords {}\n",
            case.stem.split('_').next().unwrap(),
            u8::from(case.expect),
            case.words.len()
        );
        for w in &case.words {
            text.push_str(&format!("{w:016x}\n"));
        }
        fs::write(dir.join(format!("{}.case", case.stem)), text).unwrap();
        list.push_str(&case.stem);
        list.push('\n');
    }
    fs::write(dir.join("cases.list"), list).unwrap();
    for scheme in [Scheme::Xmss, Scheme::Sphincs] {
        let of = |expect: bool| {
            cases
                .0
                .iter()
                .filter(|c| c.stem.starts_with(scheme.name()) && c.expect == expect)
                .count()
        };
        println!("{}: {} cases verify, {} do not", scheme.name(), of(true), of(false));
    }
}
