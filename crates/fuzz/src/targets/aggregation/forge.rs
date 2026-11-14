//! `guest-forge`: a malicious host's witness. A node is built over random inputs (raw signatures of both schemes,
//! fixture children, blobs, a `declare`), then its hint streams are edited before the guest runs.
//!
//! Two modes. A witness forgery keeps the honest statement and edits one thing (a cell, an entry, a count, a slot):
//! the guest must refuse, unless the edit only touches what the guest provably never reads or reads up to an
//! equivalence (each such case is named in [`benign`] and reported Low, never dropped). A statement forgery edits
//! the claim lists coherently (counts, splits, slots) so the node claims something its inputs do not back, then runs
//! against that statement: acceptance is Critical.

use super::common::{Inputs, bytes_of, count, count_inv, edge_count, log_g, outcome};
use super::fixtures::{Fixtures, N_SPHINCS, N_XMSS, fixtures, root_of};
use crate::mutate_proof::{perturb, stream_position};
use crate::{Ctx, Finding, Outcome, Source};
use fiat_shamir::merkle::{hash_pair, hash_to_scalars, hash_words};
use primitives::field::{F64, F128};
use rec_aggregation::EthereumClaims;
use rec_aggregation::fuzzing::{Hints, arm_forgery, disarm_forgery, prepare_node, run_guest, statement_of};
use signatures::lean_sphincs::LeanSphincsPublicKey;
use signatures::lean_xmss::LeanXmssPublicKey;
use std::cell::RefCell;
use std::rc::Rc;

pub(super) use super::common::Streams;

/// Streams that carry the node's own bookkeeping, drawn more often than a child's proof or a signature's path.
const SEMANTIC: &[&str] = &[
    "meta",
    "fs_seed",
    "claims",
    "dup_claims",
    "signers_split",
    "raw_index",
    "sp_raw_index",
    "child_meta",
    "child_mono",
    "child_claim_gap",
    "child_claim_index",
    "child_defer",
    "child_da",
    "da_pick",
    "leaf_defer",
    "bc_sumcheck_msgs",
    "bc_star_hint",
    "da_shape",
    "da_challenge",
];

/// The streams that only say which slot each writer covers.
const COVERAGE: &[&str] = &[
    "raw_index",
    "sp_raw_index",
    "child_mono",
    "child_claim_gap",
    "child_claim_index",
    "dup_claims",
];

/// Pairs of streams whose entries share a shape, so one's entry in the other's place still parses.
const CROSS: &[(&str, &str)] = &[
    ("raw_index", "sp_raw_index"),
    ("claims", "dup_claims"),
    ("sp_fors_nodes", "siblings"),
    ("child_claim_index", "child_claim_gap"),
    ("child_claim_index", "raw_index"),
    ("randomizer", "sp_rand"),
    ("digits", "lx_digits"),
    ("chain_starts", "lx_path"),
];

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let f = fixtures(ctx)?;
    let inputs = random_inputs(src, f);
    if src.chance(1, 8) {
        honest(&inputs, ctx)?;
    }
    if src.chance(1, 4) {
        statement_forgery(src, &inputs, ctx)
    } else {
        witness_forgery(src, &inputs, ctx)
    }
}

/// A random valid node: every input honest, so the unforged run must succeed.
pub fn random_inputs(src: &mut Source, f: &Fixtures) -> Inputs {
    let s = &f.signers;
    let mut inp = Inputs::default();
    let nx = src.weighted(&[2, 3, 2, 1]);
    let start = src.below(N_XMSS);
    for k in 0..nx {
        inp.lean_xmss.push(s.lean_xmss[(start + k) % N_XMSS].clone());
    }
    if src.chance(1, 4) {
        inp.lean_xmss.push(s.xmss_two[src.below(3)].clone());
        if src.bool() {
            inp.lean_xmss.push(s.xmss_two[src.below(3)].clone());
        }
    }
    let ns = src.weighted(&[3, 3, 1]);
    let start = src.below(N_SPHINCS);
    for k in 0..ns {
        inp.sphincs.push(s.sphincs[(start + k) % N_SPHINCS].clone());
    }
    if src.chance(1, 6) {
        inp.sphincs.push(s.sphincs_two[src.below(2)].clone());
    }
    for _ in 0..src.weighted(&[3, 4, 2, 1]) {
        inp.child(f, src.below(f.children.len()));
    }
    if src.chance(1, 5) {
        inp.blobs = f.blobs[src.below(3)].clone();
        if src.chance(1, 4) {
            inp.blobs.extend(&f.blobs[src.below(3)]);
        }
    }
    if src.chance(1, 4) {
        let mut d = inp.expected_claims();
        let n = d.num_signature_claims();
        if n > 1 && src.bool() {
            let k = src.below(n);
            if k < d.lean_xmss.len() {
                d.lean_xmss.remove(k);
            } else {
                d.lean_sphincs.remove(k - d.lean_xmss.len());
            }
        }
        if inp.blobs.is_empty() {
            let roots: Vec<_> = inp.children.iter().filter_map(|c| c.claims().da_commitment).collect();
            d.da_commitment = if roots.is_empty() || src.chance(1, 3) {
                None
            } else {
                Some(*src.pick(&roots))
            };
        }
        if d.num_signature_claims() > 0 || d.da_commitment.is_some() {
            inp.declare = Some(d);
        }
    }
    if inp.lean_xmss.is_empty() && inp.sphincs.is_empty() && inp.children.is_empty() && inp.blobs.is_empty() {
        inp.lean_xmss.push(s.lean_xmss[0].clone());
    }
    inp
}

/// The unforged node runs, and publishes what `aggregate`'s rules say.
fn honest(inputs: &Inputs, ctx: &Ctx) -> Outcome {
    let result = inputs.execute();
    super::common::note_kill(ctx, &result);
    match outcome(&result) {
        Ok(()) => {
            let run = result.unwrap();
            let want = inputs.expected_claims();
            if run.claims != want {
                return Err(Finding::high(
                    "guest-forge: an honest node publishes other claims than aggregate's rules",
                    format!(
                        "published {}\nexpected {}\ninputs: {}",
                        super::common::describe_claims(&run.claims),
                        super::common::describe_claims(&want),
                        inputs.describe()
                    ),
                ));
            }
            ctx.note("honest ok");
            Ok(())
        }
        Err(kind) => Err(Finding::high(
            format!("guest-forge: an honest node is refused ({kind})"),
            format!(
                "{}\ninputs: {}",
                super::common::describe_outcome(&result),
                inputs.describe()
            ),
        )),
    }
}

/// What a forgery did, recorded inside the hook.
struct Edit {
    stream: String,
    kind: &'static str,
    detail: String,
}

struct Logged {
    edit: Edit,
    effective: bool,
    benign: Option<String>,
}

fn witness_forgery(src: &mut Source, inputs: &Inputs, ctx: &Ctx) -> Outcome {
    let choice = src.bytes(64);
    let lens: Vec<usize> = inputs.children.iter().map(|c| c.vm_proof().stream.len()).collect();
    let log: Rc<RefCell<Option<Logged>>> = Rc::default();
    let sink = log.clone();
    arm_forgery(Box::new(move |hints: &mut Hints| {
        let streams = hints.streams_mut();
        let honest = streams.clone();
        let mut s = Source::from_bytes(&choice);
        let edit = edit_witness(streams, &mut s, &lens);
        let effective = changes_reads(&honest, streams);
        let benign = if effective {
            benign(&honest, streams, &lens)
        } else {
            None
        };
        *sink.borrow_mut() = Some(Logged {
            edit,
            effective,
            benign,
        });
    }));
    let result = inputs.execute();
    disarm_forgery();
    let Some(logged) = log.take() else {
        ctx.note(format!("built nothing: {:?}", outcome(&result).err()));
        return Ok(());
    };
    let Edit { stream, kind, detail } = logged.edit;
    ctx.note(format!("edit {stream} {kind}"));
    if !logged.effective {
        ctx.note("edit reads nothing new");
        return Ok(());
    }
    super::common::note_kill(ctx, &result);
    match outcome(&result) {
        Err(why) => {
            ctx.note(format!("refused {stream} {why}"));
            Ok(())
        }
        Ok(()) => {
            let detail = format!("{detail}\ninputs: {}", inputs.describe());
            match logged.benign {
                Some(reason) => Err(Finding::low(
                    format!("guest-forge {stream}: accepted an edit the guest does not read ({reason})"),
                    format!("a benign multiplicity: the edited cells are not bound, by design ({reason})\n{detail}"),
                )),
                None => Err(Finding::critical(
                    format!("guest-forge {stream}: a forged witness is accepted ({kind})"),
                    format!(
                        "the guest accepted a witness the honest host would not produce, for the honest statement\n{detail}"
                    ),
                )),
            }
        }
    }
}

fn pick_stream(streams: &Streams, s: &mut Source) -> Option<usize> {
    let weights: Vec<u32> = streams
        .iter()
        .map(|(name, e)| {
            if e.is_empty() {
                0
            } else if SEMANTIC.contains(&name.as_str()) {
                3
            } else {
                2
            }
        })
        .collect();
    if weights.iter().all(|&w| w == 0) {
        return None;
    }
    Some(s.weighted(&weights))
}

pub(super) fn index_of(streams: &Streams, name: &str) -> Option<usize> {
    streams.iter().position(|(n, _)| n == name)
}

/// One cell of a stream entry, never past a child proof's real stream, whose padding is documented as unread.
fn pick_cell(name: &str, entry: &[F128], i: usize, s: &mut Source, lens: &[usize]) -> usize {
    match name {
        "stream" => stream_position(lens.get(i).copied().unwrap_or(entry.len()).min(entry.len()), s),
        // Mostly the cap nodes the openings bind; the rest are opaque by design.
        "merkle_caps" if s.chance(3, 4) => {
            let bound: Vec<usize> = (0..entry.len()).filter(|&k| entry[k] != F128::ZERO).collect();
            if bound.is_empty() {
                s.below(entry.len())
            } else {
                *s.pick(&bound)
            }
        }
        _ => s.below(entry.len()),
    }
}

fn edit_witness(streams: &mut Streams, s: &mut Source, lens: &[usize]) -> Edit {
    if s.chance(1, 6) {
        return structured(streams, s);
    }
    let Some(si) = pick_stream(streams, s) else {
        return Edit {
            stream: "none".into(),
            kind: "none",
            detail: String::new(),
        };
    };
    let (name, entries) = &mut streams[si];
    let stream = name.clone();
    let n = entries.len();
    let i = match s.below(4) {
        0 => 0,
        1 => n - 1,
        _ => s.below(n),
    };
    let other = |s: &mut Source| if n > 1 && s.bool() { (i + 1) % n } else { s.below(n) };
    let cell_edit = |entries: &mut Vec<Vec<F128>>, s: &mut Source, how: u8| -> (&'static str, String) {
        if entries[i].is_empty() {
            entries[i].push(s.f128());
            return ("entry-grow", format!("entry {i} was empty"));
        }
        let k = pick_cell(&stream, &entries[i], i, s, lens);
        let before = entries[i][k];
        let (kind, after) = match how {
            0 => ("cell-perturb", perturb(before, s)),
            1 => {
                let shift = s.range(1, 3);
                (
                    "cell-shift",
                    if s.bool() {
                        before * count(shift)
                    } else {
                        before * count_inv(shift)
                    },
                )
            }
            2 => ("cell-edge", edge_count(s, n)),
            _ => {
                let j = s.below(n);
                let from = &entries[j];
                if from.is_empty() {
                    ("cell-perturb", perturb(before, s))
                } else {
                    ("cell-copy", from[s.below(from.len())])
                }
            }
        };
        entries[i][k] = after;
        (
            kind,
            format!("entry {i}/{n}, cell {k}/{}: {before:?} -> {after:?}", entries[i].len()),
        )
    };
    let (kind, detail) = match s.below(14) {
        0..=3 => cell_edit(entries, s, 0),
        4 | 5 => cell_edit(entries, s, 1),
        6 => cell_edit(entries, s, 2),
        7 => cell_edit(entries, s, 3),
        8 => {
            let j = other(s);
            entries.swap(i, j);
            ("entry-swap", format!("entries {i} and {j} of {n}"))
        }
        9 => {
            let j = other(s);
            entries[i] = entries[j].clone();
            ("entry-copy", format!("entry {j} over entry {i} of {n}"))
        }
        10 => {
            let e = entries[i].clone();
            entries.insert(i, e);
            ("entry-dup", format!("entry {i} of {n} twice"))
        }
        11 => {
            entries.remove(i);
            ("entry-drop", format!("entry {i} of {n} dropped"))
        }
        12 if entries[i].len() > 1 => {
            let len = entries[i].len();
            let (a, b) = (s.below(len), s.below(len));
            entries[i].swap(a, b);
            ("cell-swap", format!("entry {i}/{n}, cells {a} and {b}"))
        }
        _ => {
            if s.bool() || entries[i].is_empty() {
                let x = s.f128();
                entries[i].push(x);
                ("entry-grow", format!("entry {i}/{n} one cell longer"))
            } else {
                entries[i].pop();
                ("entry-shrink", format!("entry {i}/{n} one cell shorter"))
            }
        }
    };
    Edit {
        detail: format!("{kind} on `{stream}`: {detail}"),
        stream,
        kind,
    }
}

/// Edits across streams: counts moved between the two schemes' regions, an entry of one stream in another's place,
/// a whole stream gone.
fn structured(streams: &mut Streams, s: &mut Source) -> Edit {
    let edit = |stream: &str, kind: &'static str, detail: String| Edit {
        stream: stream.into(),
        kind,
        detail: format!("{kind}: {detail}"),
    };
    match s.below(4) {
        0 => {
            let Some(m) = index_of(streams, "meta") else {
                return edit("meta", "none", String::new());
            };
            let pairs = [
                (0, 3),
                (3, 0),
                (1, 4),
                (4, 1),
                (2, 5),
                (5, 2),
                (0, 1),
                (1, 0),
                (3, 4),
                (4, 3),
            ];
            let (a, b) = *s.pick(&pairs);
            let meta = &mut streams[m].1[0];
            meta[a] *= count_inv(1);
            meta[b] *= count(1);
            edit("meta", "meta-move", format!("one count from meta[{a}] to meta[{b}]"))
        }
        1 => {
            let present: Vec<(usize, usize)> = CROSS
                .iter()
                .filter_map(|(a, b)| Some((index_of(streams, a)?, index_of(streams, b)?)))
                .filter(|&(a, b)| !streams[a].1.is_empty() && !streams[b].1.is_empty())
                .collect();
            let Some(&(a, b)) = present.get(s.below(present.len().max(1))) else {
                return edit("cross", "none", String::new());
            };
            let (a, b) = if s.bool() { (a, b) } else { (b, a) };
            let j = s.below(streams[b].1.len());
            let i = s.below(streams[a].1.len());
            let from = streams[b].1[j].clone();
            let detail = format!("`{}` entry {j} over `{}` entry {i}", streams[b].0, streams[a].0);
            streams[a].1[i] = from;
            let name = streams[a].0.clone();
            edit(&name, "cross-copy", detail)
        }
        2 => {
            let Some(si) = pick_stream(streams, s) else {
                return edit("none", "none", String::new());
            };
            let (name, _) = streams.remove(si);
            edit(&name, "stream-drop", format!("`{name}` removed"))
        }
        _ => {
            let Some(m) = index_of(streams, "meta") else {
                return edit("meta", "none", String::new());
            };
            let k = s.below(8);
            let near = streams[m].1[0].get(k).copied().and_then(log_g).unwrap_or(0);
            let v = edge_count(s, near);
            streams[m].1[0][k] = v;
            edit("meta", "meta-edge", format!("meta[{k}] = {v:?}"))
        }
    }
}

/// Whether the guest reads anything else: it pops each stream in order, as many entries as the honest witness has,
/// so an edit past them (a trailing copy) changes nothing it reads.
fn changes_reads(honest: &Streams, forged: &Streams) -> bool {
    honest
        .iter()
        .any(|(name, h)| match forged.iter().find(|(n, _)| n == name) {
            None => true,
            Some((_, f)) => f.len() < h.len() || f[..h.len()] != h[..],
        })
}

/// Why an effective edit is still no attack, if it is one the guest provably does not read, or reads up to an
/// equivalence. Each reason names the guest code that makes it so.
fn benign(honest: &Streams, forged: &Streams, lens: &[usize]) -> Option<String> {
    if let Some(reason) = benign_cells(honest, forged, lens) {
        return Some(reason);
    }
    let changed: Vec<&str> = honest
        .iter()
        .filter(|(name, h)| forged.iter().find(|(n, _)| n == name).is_none_or(|(_, f)| f != h))
        .map(|(name, _)| name.as_str())
        .collect();
    if forged.len() == honest.len()
        && changed.iter().all(|name| COVERAGE.contains(name))
        && let (Some(h), Some(f)) = (coverage(honest), coverage(forged))
        && h == f
    {
        // Two slots holding the same claim, their writers exchanged: every writer still reads its own claim.
        return Some("coverage slots exchanged between equal claims".into());
    }
    None
}

/// Every edited cell one the guest does not read, or reads up to an equivalence, with the edits' shapes unchanged.
fn benign_cells(honest: &Streams, forged: &Streams, lens: &[usize]) -> Option<String> {
    let mut reasons: Vec<&'static str> = Vec::new();
    for (name, h) in honest {
        let f = &forged.iter().find(|(n, _)| n == name)?.1;
        if f.len() != h.len() {
            return None;
        }
        for (e, (he, fe)) in h.iter().zip(f).enumerate() {
            if he.len() != fe.len() {
                return None;
            }
            for (k, (&hv, &fv)) in he.iter().zip(fe).enumerate() {
                if hv == fv {
                    continue;
                }
                let reason = match name.as_str() {
                    // `verify_sub`: "the unused suffix is outside the recursively verified proof".
                    "stream" if k >= lens.get(e).copied().unwrap_or(usize::MAX) => "stream padding",
                    // `gen_verify`: "unknown, unused subtrees stay opaque"; a node no active parent hashes.
                    "merkle_caps" if hv == F128::ZERO => "opaque cap node",
                    // `verify_merkle_cap` reads an internal node's flag only as `!= 0`.
                    "merkle_cap_active" if hv != F128::ZERO && fv != F128::ZERO => "cap flag nonzero either way",
                    // A zero flag no walk sets and no hash depends on: node 0 of a cap level, which has no node.
                    "merkle_cap_active" if hv == F128::ZERO => "unread cap flag",
                    // `walk_window` hashes the running node with the sibling half of the pair, never the other half.
                    "merkle_children" if own_half(honest, e, k) => "running node's copy in a Merkle pair",
                    "da_pick" if same_da(honest, forged) => "DA pick of an equal digest",
                    // `verify_tables` certifies the push and count sides' group orders only: "pull's blocks mirror
                    // push's", so the pull side's ranks are hinted and never read.
                    "block_group_order" if pull_ranks().contains(&k) => "pull side's block group order",
                    // `child_claim_list_digest` reads `child_mono` only as `== GEN`: every other value is the any-walk.
                    "child_mono" if hv != count(1) && fv != count(1) => "child_mono other than g",
                    _ => return None,
                };
                if !reasons.contains(&reason) {
                    reasons.push(reason);
                }
            }
        }
    }
    if forged.len() != honest.len() || reasons.is_empty() {
        return None;
    }
    Some(reasons.join(", "))
}

/// The ranks of `block_group_order` that order the pull side's groups: `SIDE_GROUP_START[1]..SIDE_GROUP_START[2]`.
fn pull_ranks() -> std::ops::Range<usize> {
    static RANKS: std::sync::OnceLock<std::ops::Range<usize>> = std::sync::OnceLock::new();
    RANKS
        .get_or_init(|| {
            let (_, placeholders) = rec_aggregation::fuzzing::guest_source();
            let starts: Vec<usize> = placeholders
                .get("SIDE_GROUP_START_PLACEHOLDER")
                .map(|v| {
                    v.trim_matches(|c| c == '[' || c == ']')
                        .split(',')
                        .filter_map(|x| x.trim().parse().ok())
                        .collect()
                })
                .unwrap_or_default();
            match starts[..] {
                [_, pull, count, ..] => pull..count,
                _ => 0..0,
            }
        })
        .clone()
}

fn stream<'a>(streams: &'a Streams, name: &str) -> Option<&'a Vec<Vec<F128>>> {
    streams.iter().find(|(n, _)| n == name).map(|(_, e)| e)
}

/// Whether cell `k` of `merkle_children` entry `e` lies in the half of its level's pair that holds the running
/// node: the leaf's hash at level 0, the hash of the pair below above it.
fn own_half(honest: &Streams, e: usize, k: usize) -> bool {
    let (Some(children), Some(rows)) = (stream(honest, "merkle_children"), stream(honest, "merkle_leaf_rows")) else {
        return false;
    };
    let (Some(path), Some(row)) = (children.get(e), rows.get(e)) else {
        return false;
    };
    let level = k / 4;
    let node = if level == 0 {
        let leaf: Vec<F64> = row.iter().map(|c| F64(c.c0)).collect();
        hash_words(&leaf)
    } else {
        let (Some(l), Some(r)) = (
            bytes_of(&path[4 * level - 4..4 * level - 2]),
            bytes_of(&path[4 * level - 2..4 * level]),
        ) else {
            return false;
        };
        hash_pair(&l, &r)
    };
    let own = hash_to_scalars(&node);
    let half = 4 * level + 2 * ((k % 4) / 2);
    path.get(half..half + 2) == Some(&own[..])
}

/// Whether the forged `da_pick` names a digest equal to the honest pick's.
fn same_da(honest: &Streams, forged: &Streams) -> bool {
    let digest = |streams: &Streams| -> Option<Vec<F128>> {
        let meta = stream(streams, "meta")?.first()?;
        let n_children = log_g(meta[6])?;
        let own_blobs = log_g(meta[7])? == 1;
        let pick = log_g(stream(streams, "da_pick")?.first()?[0])?;
        if pick < n_children {
            stream(honest, "child_da")?.get(pick).cloned()
        } else if pick == n_children && !own_blobs {
            Some(vec![F128::ZERO; 2])
        } else {
            None
        }
    };
    digest(honest).is_some() && digest(honest) == digest(forged)
}

/// The claim every coverage writer reads, in the order the guest walks them: each raw leanXMSS signature, each raw
/// leanSPHINCS signature, then each child's two lists. `None` when the hints do not parse.
fn coverage(streams: &Streams) -> Option<Vec<Vec<F128>>> {
    let meta = stream(streams, "meta")?.first()?;
    let n: Vec<usize> = meta.iter().map(|&x| log_g(x)).collect::<Option<_>>()?;
    let (n_lx, n_xdup, n_raw_x, n_s, n_sdup, n_raw_s, n_children) = (n[0], n[1], n[2], n[3], n[4], n[5], n[6]);
    let empty = Vec::new();
    let claims = stream(streams, "claims").unwrap_or(&empty);
    let dups = stream(streams, "dup_claims").unwrap_or(&empty);
    if claims.len() < n_lx + n_s || dups.len() < n_xdup + n_sdup {
        return None;
    }
    let x_table: Vec<&Vec<F128>> = claims[..n_lx].iter().chain(&dups[..n_xdup]).collect();
    let s_table: Vec<&Vec<F128>> = claims[n_lx..n_lx + n_s]
        .iter()
        .chain(&dups[n_xdup..n_xdup + n_sdup])
        .collect();
    let mut cursor = std::collections::HashMap::<&str, usize>::new();
    let mut next = |name: &'static str| -> Option<F128> {
        let at = cursor.entry(name).or_default();
        let v = *stream(streams, name)?.get(*at)?.first()?;
        *at += 1;
        Some(v)
    };
    let mut out = Vec::new();
    for _ in 0..n_raw_x {
        out.push(x_table.get(log_g(next("raw_index")?)?)?.to_vec());
    }
    for _ in 0..n_raw_s {
        out.push(s_table.get(log_g(next("sp_raw_index")?)?)?.to_vec());
    }
    let child_meta = stream(streams, "child_meta")?;
    for c in 0..n_children {
        let lengths = child_meta.get(c)?;
        for (list, table) in [&x_table, &s_table].into_iter().enumerate() {
            let len = log_g(*lengths.get(list)?)?;
            if len == 0 {
                continue;
            }
            if next("child_mono")? == count(1) {
                let mut at = 0;
                for _ in 0..len {
                    let slot = at + log_g(next("child_claim_gap")?)?;
                    out.push(table.get(slot)?.to_vec());
                    at = slot + 1;
                }
            } else {
                for _ in 0..len {
                    out.push(table.get(log_g(next("child_claim_index")?)?)?.to_vec());
                }
            }
        }
    }
    Some(out)
}

/// `list_split` in the guest and in `statement.rs`.
pub(super) fn list_split(n: usize) -> Vec<F128> {
    const GROUP: usize = 17;
    const BIG: usize = GROUP * 8;
    vec![count(n / BIG), count(n % BIG / GROUP), count(n % BIG % GROUP)]
}

/// What a statement forgery made of the claim lists, as cells, and the DA root it publishes instead, if any.
struct Claimed {
    kind: &'static str,
    lean_xmss: Vec<Vec<F128>>,
    sphincs: Vec<Vec<F128>>,
    da: Option<Option<[u8; 32]>>,
    detail: String,
}

fn statement_forgery(src: &mut Source, inputs: &Inputs, ctx: &Ctx) -> Outcome {
    let choice = src.bytes(32);
    let foreign_root = match src.below(3) {
        0 => [0xEE; 32],
        1 => root_of(&blob_of_seed(src.u64())),
        _ => {
            let mut r = [0; 32];
            src.rng().fill(&mut r);
            r
        }
    };
    let log: Rc<RefCell<Option<Claimed>>> = Rc::default();
    let sink = log.clone();
    arm_forgery(Box::new(move |hints: &mut Hints| {
        let mut s = Source::from_bytes(&choice);
        *sink.borrow_mut() = forge_claims(hints.streams_mut(), &mut s, foreign_root);
    }));
    let prepared = prepare_node(
        &inputs.children,
        inputs.lean_xmss.clone(),
        inputs.sphincs.clone(),
        &inputs.blobs,
        inputs.declare.as_ref(),
    );
    disarm_forgery();
    let prepared = match prepared {
        Ok(p) => p,
        Err(e) => {
            ctx.note(format!("built nothing: {}", super::common::error_kind(&e)));
            return Ok(());
        }
    };
    let Some(claimed) = log.take() else {
        ctx.note("statement forgery inapplicable");
        return Ok(());
    };
    ctx.note(format!("statement {}", claimed.kind));
    let to_claim =
        |cells: &Vec<F128>| -> Option<([u8; 32], [u8; 32])> { Some((bytes_of(&cells[..2])?, bytes_of(&cells[2..])?)) };
    let lean_xmss: Option<Vec<_>> = claimed
        .lean_xmss
        .iter()
        .map(|c| to_claim(c).map(|(pk, m)| (LeanXmssPublicKey::from_bytes(&pk), m)))
        .collect();
    let sphincs: Option<Vec<_>> = claimed
        .sphincs
        .iter()
        .map(|c| to_claim(c).map(|(pk, m)| (LeanSphincsPublicKey::from_bytes(&pk), m)))
        .collect();
    let (Some(lean_xmss), Some(lean_sphincs)) = (lean_xmss, sphincs) else {
        ctx.note("statement forgery: a non-canonical claim");
        return Ok(());
    };
    let forged = EthereumClaims {
        lean_xmss,
        lean_sphincs,
        da_commitment: claimed.da.unwrap_or(prepared.claims.da_commitment),
    };
    let pi = statement_of(&forged, &prepared.defer_point, prepared.defer_value);
    match run_guest(&prepared.program, pi) {
        Err(e) => {
            ctx.note(format!(
                "statement {} refused {}",
                claimed.kind,
                super::common::refusal_kind(&e)
            ));
            Ok(())
        }
        Ok(_) => match inputs.backing().unbacked(&forged) {
            Some(why) => Err(Finding::critical(
                format!(
                    "guest-forge: a node claiming what nothing backs is accepted ({})",
                    claimed.kind
                ),
                format!(
                    "{why}\n{}\nclaimed {}\nhonest {}\ninputs: {}",
                    claimed.detail,
                    super::common::describe_claims(&forged),
                    super::common::describe_claims(&prepared.claims),
                    inputs.describe()
                ),
            )),
            None => {
                ctx.note(format!("statement {} accepted, backed", claimed.kind));
                Ok(())
            }
        },
    }
}

fn blob_of_seed(seed: u64) -> Vec<u64> {
    super::fixtures::blob_row(seed)
}

/// Edit the declared lists coherently (counts, splits, the tables), so the guest's run decides the new statement.
fn forge_claims(streams: &mut Streams, s: &mut Source, foreign_root: [u8; 32]) -> Option<Claimed> {
    let m = index_of(streams, "meta")?;
    let meta = streams[m].1.first()?.clone();
    let n: Vec<usize> = meta.iter().map(|&x| log_g(x)).collect::<Option<_>>()?;
    let (n_lx, n_xdup, n_s, n_sdup) = (n[0], n[1], n[3], n[4]);
    let c = index_of(streams, "claims");
    let claims: Vec<Vec<F128>> = c.map(|c| streams[c].1.clone()).unwrap_or_default();
    if claims.len() < n_lx + n_s {
        return None;
    }
    let mut lean_xmss = claims[..n_lx].to_vec();
    let mut sphincs = claims[n_lx..n_lx + n_s].to_vec();
    let foreign = |s: &mut Source, like: Option<&Vec<F128>>| -> Vec<F128> {
        let mut claim = like.cloned().unwrap_or_else(|| vec![F128::new(7, 7); 4]);
        let k = s.below(4);
        claim[k].c0 ^= 1 << s.below(64);
        claim
    };
    let kind = match s.below(4) {
        0 if n_lx + n_s > 0 => {
            // One declared claim, one bit of its pubkey or message flipped: a claim nobody signed.
            let j = s.below(n_lx + n_s);
            let forged = foreign(s, Some(&claims[j]));
            if j < n_lx {
                lean_xmss[j] = forged.clone()
            } else {
                sphincs[j - n_lx] = forged.clone()
            }
            streams[c?].1[j] = forged;
            "substitute"
        }
        1 if n_lx + n_s > 0 => {
            // The boundary between the lists moved by one: a claim verified under one scheme published as the other's.
            let to_sphincs = n_lx > 0 && (n_s == 0 || s.bool());
            if to_sphincs {
                sphincs.insert(0, lean_xmss.pop()?);
                streams[m].1[0][0] *= count_inv(1);
                streams[m].1[0][3] *= count(1);
            } else {
                lean_xmss.push(sphincs.remove(0));
                streams[m].1[0][0] *= count(1);
                streams[m].1[0][3] *= count_inv(1);
            }
            resplit(streams, n_lx, n_s, lean_xmss.len(), sphincs.len());
            "scheme-move"
        }
        2 if n_xdup + n_sdup > 0 => {
            // A duplicate slot turned into a declared claim nobody signed: its writer now covers the new claim.
            let x = n_xdup > 0 && (n_sdup == 0 || s.bool());
            let d = index_of(streams, "dup_claims")?;
            let like = claims.get(s.below(claims.len().max(1)));
            let forged = foreign(s, like);
            if x {
                streams[d].1.remove(0);
                lean_xmss.push(forged.clone());
                streams[c?].1.insert(n_lx, forged);
                streams[m].1[0][0] *= count(1);
                streams[m].1[0][1] *= count_inv(1);
            } else {
                streams[d].1.remove(n_xdup);
                sphincs.push(forged.clone());
                streams[c?].1.insert(n_lx + n_s, forged);
                streams[m].1[0][3] *= count(1);
                streams[m].1[0][4] *= count_inv(1);
            }
            resplit(streams, n_lx, n_s, lean_xmss.len(), sphincs.len());
            "promote-dup"
        }
        _ => {
            return Some(Claimed {
                kind: "da-root",
                lean_xmss,
                sphincs,
                da: Some(Some(foreign_root)),
                detail: "a DA root no input has".into(),
            });
        }
    };
    Some(Claimed {
        kind,
        detail: format!(
            "{kind}: lists of {n_lx} and {n_s} claims become {} and {}",
            lean_xmss.len(),
            sphincs.len()
        ),
        lean_xmss,
        sphincs,
        da: None,
    })
}

/// Replace the declared lists' splits, the first entries of `signers_split`, with those of the new lengths.
pub(super) fn resplit(streams: &mut Streams, old_x: usize, old_s: usize, new_x: usize, new_s: usize) {
    let mut fresh = Vec::new();
    for n in [new_x, new_s] {
        if n > 0 {
            fresh.push(list_split(n));
        }
    }
    let old = usize::from(old_x > 0) + usize::from(old_s > 0);
    match index_of(streams, "signers_split") {
        Some(i) => {
            let entries = &mut streams[i].1;
            entries.splice(..old.min(entries.len()), fresh);
        }
        None => streams.push(("signers_split".into(), fresh)),
    }
}
