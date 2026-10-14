//! The tree's circuits, and their heights.
//!
//! - A first-level node verifies leaves of the tree's one family, and reduces every claim they leave. RISC-V proofs of the program leave program claims, which become point claims on the bytecode table and the image; proofs of the leaf circuit leave hinted evaluations of that circuit's fixed columns, which become claims on the leaves' fixed polynomial.
//! - A node verifies tree proofs of the tree's kinds, and reduces their fresh claims with the claims they carry, each on a polynomial a first-level node does not fix weighed by whether its child is a node.
//!
//! A tree of outputs has one circuit of each; a claim-set tree has a node circuit for every arity up to its largest.
//! The circuits of one tier have the same heights, so a node verifies a child of any of the tier's kinds with one set of
//! rows, its kind's bits selecting its circuit's block of the tier's fixed polynomial.
//!
//! A claim-set tree may have two tiers, each at heights of its own. The small tier holds the first level, nodes of a few
//! children within a small capacity, and a wrap; the large tier holds one node of the tree's arity within the tree's
//! capacity. Every node, of either tier, verifies children of the small tier, and a wrap verifies one proof of the
//! large tier and states its set: so a small proof never pays the large tier's heights, and a large one is combined
//! once wrapped. A claim-set node's places past its children are absent, their sets read as the empty set.

use super::multiset::Capacity;
use super::reduce::{Bits, DenseClaim, DensePoly, DenseTables, DenseTerm, DenseVars, MatrixClaim, NodeClaims};
use super::statement::{Items, StatementLayout, TreeStatement};
use super::union::{UnionFill, UnionShape};
use super::{ClaimShape, LeafCircuit, TreeError, TreeShape, reduce};
use crate::bus::N_TUPLE_BITS;
use crate::commitment::Rate;
use crate::cpu::{Claim, Lookup, ProgramPoint};
use crate::rec::circuit::{Builder, Dw, Ew, Finished, Kw, Limbs};
use crate::rec::fixed::{FixedColumns, FixedLayout};
use crate::rec::hash;
use crate::rec::table::Heights;
use crate::rec::transcript::{ProofSource, Transcript};
use crate::rec::verifier::{FixedHint, ProofShape, RecShape, Rows, infallible};
use crate::tables::CircuitId;
use fiat_shamir::arith::Arith;
use fiat_shamir::{ProofTranscript, SessionId};
use pcs::merkle::Openings;

use pcs::ring_switch::inverse_frobenius_ladder;
use primitives::field::{F64, F192};
use primitives::multilinear::mle_eval_par;
use std::ops::Range;

/// The protocol half of every recursion proof's session tag.
const DOMAIN: &[u8] = b"leanvm-tree-17";

/// The tier of a tree of one tier, or of a claim-set tree's small tier: the first level's.
pub(crate) const SMALL: usize = 0;

/// A claim-set tree's large tier.
pub(crate) const LARGE: usize = 1;

/// What one of a tree's circuits verifies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Level {
    /// The tree's leaves: a first-level node.
    First,
    /// This many proofs of the first level's tier: a node above the first level.
    Node(usize),
    /// One proof of the large tier, whose set it states.
    Wrap,
}

/// One of a tree's circuits: its tier, and what it verifies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Place {
    /// Its tier.
    pub(crate) tier: usize,
    /// What it verifies.
    pub(crate) level: Level,
}

/// The circuits of one tier: their heights, and what verifying one of their proofs takes.
pub(crate) struct TierDesign {
    /// The heights its circuits share: a table is absent from them only if all its circuits lack it.
    pub(crate) taus: Heights,
    /// The shape of one of its proofs, as a node verifies it.
    child: RecShape,
    /// Where each fixed column sits in one of its circuits' stack.
    pub(crate) fixed: FixedLayout,
    /// Its circuits' places in the tree's list.
    pub(crate) places: Range<usize>,
    /// The bits of a kind's index within the tier, which select its circuit's block of the tier's fixed polynomial.
    kind_bits: usize,
    /// In a claim-set tree, the capacity of its circuits' unions.
    capacity: Option<Capacity>,
}

/// The tree's leaf family, as its circuits verify it.
pub(crate) enum Family<'p> {
    /// RISC-V proofs of one program, of one shape: the program, its tables' heights, its rate.
    Runs(ProofShape<'p>),
    /// Proofs of one recursion circuit.
    Circuit(CircuitFamily<'p>),
}

/// Proofs of one recursion circuit, as a first-level node verifies them.
pub(crate) struct CircuitFamily<'p> {
    /// The circuit, its fixed columns, its session and its proofs' rate.
    pub(crate) leaf: LeafCircuit<'p>,
    /// The shape of its proofs, at its own heights.
    shape: RecShape,
    /// Where each of its fixed columns sits in its stack, `W_leaf`.
    fixed: FixedLayout,
}

/// What fixes a tree's circuits: the leaf family, the arities, the rate, the semantics, and each tier's heights.
pub(crate) struct Design<'p> {
    /// The leaf family, which the first-level circuit verifies.
    pub(crate) family: Family<'p>,
    /// The leaves a first-level node verifies.
    pub(crate) arity_0: usize,
    /// The children a node verifies: the only arity of a tree of outputs, the largest of a claim-set tree.
    pub(crate) arity: usize,
    /// Every tree proof's rate.
    pub(crate) rate: Rate,
    /// A claim-set tree's capacities, none for a tree of outputs.
    pub(crate) claims: Option<ClaimShape>,
    /// Each circuit's place, by its position: the first level's first, the small tier's before the large tier's.
    pub(crate) places: Vec<Place>,
    /// Each tier.
    pub(crate) tiers: Vec<TierDesign>,
    /// The bits of a kind's index within its tier, above which the kind states its tier.
    tier_shift: usize,
    /// Each dense polynomial's variables.
    pub(crate) vars: DenseVars,
    /// Which dense polynomials the tree has.
    pub(crate) present: [bool; DensePoly::COUNT],
    /// Where each part of a statement sits.
    pub(crate) statement: StatementLayout,
}

/// A child's kind, as its node's rows read it.
struct KindBits {
    /// The bits that select its circuit's block of its tier's fixed polynomial, lowest first.
    top: Vec<Ew>,
    /// One if it is a node above the first level, zero if it is a first-level node.
    is_node: Ew,
}

/// A leaf as a first-level node's prover holds it: its proof, which the native verifier accepted, and its output.
pub(crate) struct LeafWitness<'a> {
    /// The proof.
    pub(crate) proof: &'a ProofTranscript,
    /// Every opening its native verifier authenticated, phase by phase.
    pub(crate) openings: Vec<Openings>,
    /// The output it proves.
    pub(crate) output: [u64; 4],
    /// In a claim-set tree, the digest of its claim set, whose hash is its output.
    pub(crate) set: [u64; 4],
}

/// A leaf of a recursion circuit as a first-level node's prover holds it: its statement, its proof, which the native verifier accepted, and its circuit's fixed columns.
pub(crate) struct CircuitWitness<'a> {
    /// What it states, word by word.
    pub(crate) statement: Vec<Limbs>,
    /// The proof.
    pub(crate) proof: &'a ProofTranscript,
    /// Every opening its native verifier authenticated, phase by phase.
    pub(crate) openings: Vec<Openings>,
    /// The fixed columns of its circuit.
    pub(crate) columns: &'a FixedColumns,
}

/// A child as a node's prover holds it: its statement, its proof, and its circuit's fixed columns.
pub(crate) struct ChildWitness<'a> {
    /// What it states.
    pub(crate) statement: &'a TreeStatement,
    /// The proof, which the native verifier accepted.
    pub(crate) proof: &'a ProofTranscript,
    /// Every opening its native verifier authenticated, phase by phase.
    pub(crate) openings: Vec<Openings>,
    /// The fixed columns of its circuit.
    pub(crate) columns: &'a FixedColumns,
}

/// What a circuit is built from: the shapes alone, or what a prover holds.
pub(crate) enum NodeInputs<'a, T> {
    /// No values: every proof read is zeros, and the rows are the circuit's.
    Shape,
    /// The verified proofs, and the dense polynomials the hints are evaluations of.
    Prove {
        /// The proofs, in order.
        items: &'a [T],
        /// The dense polynomials.
        tables: &'a DenseTables,
        /// In a claim-set tree, the union's values.
        union: Option<&'a UnionFill>,
    },
}

/// A circuit's rows up to its reduction: they verify its proofs, and leave the claims the reduction takes.
pub(crate) struct NodeRows {
    /// The circuit so far, and its values.
    b: Builder,
    /// The circuit's position in the tree's list.
    position: usize,
    /// The digest it states: of what the leaves under it state, or of its claim set.
    digest: Dw,
    /// The claims its rows leave.
    claims: NodeClaims<Ew>,
}

impl<'p> CircuitFamily<'p> {
    /// The family of a leaf circuit's proofs.
    ///
    /// # Errors
    ///
    /// A circuit whose heights admit no recursion proof.
    pub(crate) fn new(leaf: LeafCircuit<'p>) -> Result<Self, TreeError> {
        let taus = leaf.circuit().heights();
        Ok(Self {
            shape: RecShape::new(taus, leaf.rate).map_err(|_| TreeError::TooLarge)?,
            fixed: FixedLayout::new(&taus),
            leaf,
        })
    }

    /// The leaves' fixed polynomial `W_leaf` of the leaf circuit's fixed columns: its stack.
    pub(crate) fn leaf_polynomial(&self, columns: &FixedColumns) -> Vec<F64> {
        self.fixed.polynomial(&[columns])
    }
}

impl<T> NodeInputs<'_, T> {
    /// Proof `i`, when a prover holds it.
    const fn item(&self, i: usize) -> Option<&T> {
        match self {
            Self::Shape => None,
            Self::Prove { items, .. } => Some(&items[i]),
        }
    }

    /// A dense polynomial's value at a point, as a hint: only the prover's tables give it, zero from the shapes.
    fn hint(&self, b: &mut Builder, poly: DensePoly, point: &[Ew]) -> Ew {
        let value = match self {
            Self::Shape => F192::ZERO,
            Self::Prove { tables, .. } => {
                let at: Vec<F192> = point.iter().map(|&w| b.e(w)).collect();
                mle_eval_par(&tables.0[poly as usize], &at)
            }
        };
        b.free_e(value)
    }

    /// The union's values, when a prover of a claim-set tree holds them.
    const fn union(&self) -> Option<&UnionFill> {
        match self {
            Self::Shape => None,
            Self::Prove { union, .. } => *union,
        }
    }
}

impl Place {
    /// The circuits of a tree, in order: the first level's, the nodes of each arity, then in a tree of two tiers the
    /// wrap and the large tier's one node.
    ///
    /// A tree of outputs has one node, of its arity; a claim-set tree of one tier one of each arity up to its largest.
    /// A claim-set node takes from one child to its arity, the rest absent (in rows, any place may be), so the large
    /// tier needs one node and its fixed polynomial, which every proof above a wrap reduces, is of one circuit.
    pub(crate) fn all(arity: usize, claims: Option<ClaimShape>) -> Vec<Self> {
        let place = |tier, level| Self { tier, level };
        let nodes = |tier, arities: std::ops::RangeInclusive<usize>| arities.map(move |a| place(tier, Level::Node(a)));
        let first = std::iter::once(place(SMALL, Level::First));
        match claims {
            None => first.chain(nodes(SMALL, arity..=arity)).collect(),
            Some(ClaimShape { small: None, .. }) => first.chain(nodes(SMALL, 2..=arity)).collect(),
            Some(ClaimShape { small: Some(s), .. }) => (first.chain(nodes(SMALL, 2..=s.arity)))
                .chain([place(SMALL, Level::Wrap)])
                .chain(nodes(LARGE, arity..=arity))
                .collect(),
        }
    }
}

impl<'p> Design<'p> {
    /// The design of a tree over proofs of a program, at the given heights of each tier's circuits.
    ///
    /// # Errors
    ///
    /// Returns an error if the heights admit no recursion proof.
    pub(crate) fn new(family: Family<'p>, shape: &TreeShape, taus: &[Heights]) -> Result<Self, TreeError> {
        let TreeShape {
            arity_0,
            arity,
            rate,
            claims,
        } = *shape;
        let places = Place::all(arity, claims);
        let tiers = (0..taus.len())
            .map(|tier| {
                let start = places.iter().position(|p| p.tier == tier).expect("a tier has circuits");
                let end = start + places[start..].iter().take_while(|p| p.tier == tier).count();
                Ok(TierDesign {
                    taus: taus[tier],
                    child: RecShape::new(taus[tier], rate).map_err(|_| TreeError::TooLarge)?,
                    fixed: FixedLayout::new(&taus[tier]),
                    places: start..end,
                    kind_bits: crate::log2_ceil_usize(end - start),
                    capacity: claims.map(|c| c.tier_capacity(tier)),
                })
            })
            .collect::<Result<Vec<_>, TreeError>>()?;
        assert_eq!(
            tiers.last().map(|t| t.places.end),
            Some(places.len()),
            "a height for each tier"
        );
        let tier_shift = tiers.iter().map(|t| t.kind_bits).max().unwrap_or(0);
        let fixed_vars = |tier: usize| tiers.get(tier).map_or(0, |t| t.fixed.kappa() + t.kind_bits);
        let fixed = fixed_vars(SMALL);
        let wide = fixed_vars(LARGE);
        let large = tiers.len() > 1;
        let (present, vars) = match &family {
            Family::Runs(shape) => {
                let rv = shape.program().rv();
                let bytecode = crate::log2_strict_usize(rv.entries().len()) + N_TUPLE_BITS;
                let image = crate::log2_ceil_usize(rv.image().len().max(1));
                (
                    [true, true, false, true, large],
                    DenseVars([bytecode, image, 0, fixed, wide]),
                )
            }
            Family::Circuit(c) => (
                [false, false, true, true, large],
                DenseVars([0, 0, c.fixed.kappa(), fixed, wide]),
            ),
        };
        let n_dense = (vars.0.iter().zip(present))
            .filter_map(|(&n, p)| p.then_some(n))
            .max()
            .unwrap_or(0);
        Ok(Self {
            family,
            arity_0,
            arity,
            rate,
            claims,
            places,
            tiers,
            tier_shift,
            vars,
            present,
            statement: StatementLayout::new(n_dense, present),
        })
    }

    /// The transcript's session: everything that fixes the circuits, as one tag.
    ///
    /// Every kind shares it.
    /// The kind is the statement's first word, and the statement is the transcript's instance.
    /// A tree of outputs and a claim-set tree differ in it, so a proof of one is never one of the other.
    ///
    /// It names the leaf family: the program's digest, the leaves' heights, rate and kind, or the leaf circuit's session, statement length, heights and rate. So a tree proof verifies only under a tree of its own leaf family.
    pub(crate) fn session(&self) -> SessionId {
        self.session_under(DOMAIN)
    }

    /// The session under a protocol version's tag.
    pub(super) fn session_under(&self, domain: &[u8]) -> SessionId {
        let mut tag = domain.to_vec();
        let word = |tag: &mut Vec<u8>, x: usize| tag.extend_from_slice(&(x as u64).to_le_bytes());
        // An absent table's height is a word no height is.
        let height = |tag: &mut Vec<u8>, tau: Option<usize>| word(tag, tau.unwrap_or(usize::MAX));
        match &self.family {
            Family::Runs(proofs) => {
                let leaf = proofs.shape();
                tag.extend_from_slice(b"runs....");
                tag.extend_from_slice(proofs.program().digest());
                leaf.taus().values().for_each(|&t| word(&mut tag, t));
                tag.push(leaf.rate().log_inv_rate());
                tag.push(u8::from(leaf.is_zero_knowledge()));
            }
            Family::Circuit(c) => {
                tag.extend_from_slice(b"circuit.");
                tag.extend_from_slice(&c.leaf.session.0);
                word(&mut tag, c.leaf.circuit().statement_len);
                for t in c.leaf.circuit().heights().into_values() {
                    height(&mut tag, t);
                }
                tag.push(c.leaf.rate.log_inv_rate());
                // A claim-set tree's first level reads the leaves' sets by the circuit's layout.
                if self.claims.is_some() {
                    c.leaf
                        .claims
                        .tag()
                        .for_each(|w| tag.extend_from_slice(&w.to_le_bytes()));
                }
            }
        }
        let large = self.claims.map(|c| c.capacity);
        let semantics = large.map_or([0; 3], |c| [1, c.claims, c.groups]);
        let small = (self.claims.and_then(|c| c.small)).map(|s| [s.arity, s.capacity.claims, s.capacity.groups]);
        let sizes = [self.arity_0, self.arity, self.statement.len()]
            .into_iter()
            .chain(semantics)
            .chain(small.into_iter().flatten());
        for x in sizes {
            word(&mut tag, x);
        }
        for t in self.tiers.iter().flat_map(|t| t.taus.into_values()) {
            height(&mut tag, t);
        }
        tag.push(self.rate.log_inv_rate());
        SessionId::new(&tag)
    }

    /// The kind a circuit's proofs state: its index within its tier, the tier above it.
    pub(crate) fn code(&self, position: usize) -> usize {
        let tier = self.places[position].tier;
        (tier << self.tier_shift) | (position - self.tiers[tier].places.start)
    }

    /// The position of the circuit whose proofs state this kind, if the tree has one.
    pub(crate) fn position(&self, code: usize) -> Option<usize> {
        let tier = code >> self.tier_shift;
        let t = self.tiers.get(tier)?;
        let position = t.places.start + (code & ((1 << self.tier_shift) - 1));
        t.places.contains(&position).then_some(position)
    }

    /// The union a circuit runs, in a claim-set tree: none for a wrap, which states its child's set.
    ///
    /// A node's places past its children are absent; a first-level node verifies all its leaves.
    pub(crate) fn union_shape(&self, position: usize) -> Option<UnionShape> {
        let Place { tier, level } = self.places[position];
        let capacity = self.tiers[tier].capacity?;
        match level {
            Level::First => Some(UnionShape::new(capacity, self.arity_0)),
            Level::Node(arity) => Some(UnionShape::optional(capacity, arity)),
            Level::Wrap => None,
        }
    }

    /// The position of the circuit of this place, if the tree has one.
    pub(crate) fn place(&self, tier: usize, level: Level) -> Option<usize> {
        self.places.iter().position(|&p| p == Place { tier, level })
    }

    /// Whether the leaves fix the polynomial, so a first-level node's statement carries a claim on it: the bytecode
    /// table and the image under RISC-V proofs, the leaves' fixed polynomial under a leaf circuit's proofs. Every other
    /// proof carries a claim on every polynomial the tree has.
    pub(crate) fn leaves_fix(&self, poly: DensePoly) -> bool {
        self.present[poly as usize]
            && match self.family {
                Family::Runs(_) => matches!(poly, DensePoly::Bytecode | DensePoly::Image),
                Family::Circuit(_) => poly == DensePoly::Leaf,
            }
    }

    /// The dense polynomials, of the circuits' fixed columns by position: a polynomial the tree lacks is the zero table
    /// of no variables.
    pub(crate) fn tables(&self, columns: &[&FixedColumns]) -> DenseTables {
        let none = || vec![F64::ZERO];
        let [bytecode, image, leaf] = match &self.family {
            Family::Runs(proofs) => {
                let rv = proofs.program().rv();
                let mut image: Vec<F64> = rv.image().iter().map(|&w| F64(w)).collect();
                image.resize(1 << self.vars.0[DensePoly::Image as usize], F64::ZERO);
                [Lookup::Bytecode.table(rv), image, none()]
            }
            Family::Circuit(c) => [none(), none(), c.leaf_polynomial(c.leaf.columns())],
        };
        // Each tier's fixed polynomial stacks its circuits' columns; a tree of one tier has no wide one.
        let fixed = |tier: usize| {
            self.tiers
                .get(tier)
                .map_or_else(none, |t| t.fixed.polynomial(&columns[t.places.clone()]))
        };
        DenseTables([bytecode, image, leaf, fixed(SMALL), fixed(LARGE)])
    }

    /// The first level's rows over RISC-V proofs, verifying its leaves.
    pub(crate) fn first_runs_rows(&self, leaf: &ProofShape<'_>, inputs: &NodeInputs<'_, LeafWitness<'_>>) -> NodeRows {
        let mut b = Builder::new();
        let mut claims = NodeClaims::default();
        let mut outputs = Vec::with_capacity(self.arity_0);
        let mut sets = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let item = inputs.item(i);
            // A claim-set leaf's output is the hash of its set's digest, which the union reads.
            let output = if self.claims.is_some() {
                let set = b.free_d(item.map_or([0; 4], |l| l.set));
                sets.push(set);
                let words = b.d_to_k(set);
                let output = b.chain(&words);
                b.d_to_k(output)
            } else {
                item.map_or([0; 4], |l| l.output).map(|o| b.free_k(o))
            };
            let source = item.map_or(ProofSource::Shape, |l| ProofSource::Proof(l.proof, &l.openings));
            let core = b.scope(format!("leaf {i}"), |b| leaf.verify_core(b, output, source));
            claims.bind_state(&mut b, core.state);
            b.scope(format!("leaf {i} program"), |b| {
                self.program_claims(b, &core.claims.program, inputs, &mut claims);
            });
            let fresh = CircuitId::ALL.into_iter().zip(&core.claims.circuits);
            claims.matrices.extend(fresh.map(|(f, c)| MatrixClaim::fresh(f, c)));
            outputs.push(output);
        }
        let digest = match self.union_shape(0) {
            Some(shape) => shape.rows(&mut b, &self.session(), &sets, inputs.union()),
            None => Items::Runs.digest_rows(&mut b, &outputs),
        };
        NodeRows {
            b,
            position: 0,
            digest,
            claims,
        }
    }

    /// The first level's rows over proofs of a recursion circuit, verifying its leaves at the circuit's own heights, rate and session.
    ///
    /// Each leaf's statement is free wires, which its verifier's rows absorb as its transcript's instance. In a tree of outputs the digest is over each transcript's digest of its instance (`instance_digest`); in a claim-set tree each leaf's set is read from its statement's wires (`leaf_set`), and the union reads the sets at their digests.
    pub(crate) fn first_circuit_rows(
        &self,
        family: &CircuitFamily<'_>,
        inputs: &NodeInputs<'_, CircuitWitness<'_>>,
    ) -> NodeRows {
        let leaf = &family.leaf;
        let mut b = Builder::new();
        let zeros = matches!(inputs, NodeInputs::Shape).then(|| FixedColumns::zeros(&leaf.circuit().heights()));
        let zero = b.k_const(0);
        let mut claims = NodeClaims::default();
        let mut instances = Vec::with_capacity(self.arity_0);
        let mut sets = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let item = inputs.item(i);
            let limbs: Vec<[Kw; 4]> = (0..leaf.circuit().statement_len)
                .map(|z| {
                    let [l0, l1, l2, _] = item.map_or([0; 4], |l| l.statement[z]);
                    [b.free_k(l0), b.free_k(l1), b.free_k(l2), zero]
                })
                .collect();
            let columns = item.map_or_else(|| zeros.as_ref().expect("zero columns from a shape"), |l| l.columns);
            let source = item.map_or(ProofSource::Shape, |l| ProofSource::Proof(l.proof, &l.openings));
            let (instance, rows) = b.scope(format!("leaf {i}"), |b| {
                let t = RecShape::transcript(b, &leaf.session, &limbs, source);
                let instance = self.claims.is_none().then(|| t.digest_so_far(b));
                (instance, family.shape.verify_from(b, t, &limbs, columns))
            });
            claims.bind_state(&mut b, rows.state);
            claims.bound.extend(rows.hints.iter().map(|h| h.value));
            claims
                .dense
                .push(fixed_claim(DensePoly::Leaf, &family.fixed, &rows.hints, &[]));
            claims.matrices.push(MatrixClaim::fresh(hash::CIRCUIT, &rows.matrix));
            match instance {
                Some(instance) => instances.push(b.d_to_k(instance)),
                None => sets.push(b.scope(format!("leaf {i} claims"), |b| leaf.claims.digest_rows(b, &limbs))),
            }
        }
        let digest = match self.union_shape(0) {
            Some(shape) => shape.rows(&mut b, &self.session(), &sets, inputs.union()),
            None => Items::Circuit(leaf.seed()).digest_rows(&mut b, &instances),
        };
        NodeRows {
            b,
            position: 0,
            digest,
            claims,
        }
    }

    /// The rows of the node circuit or wrap at `position`, verifying its children of any of their tier's kinds.
    pub(crate) fn node_rows(&self, inputs: &NodeInputs<'_, ChildWitness<'_>>, position: usize) -> NodeRows {
        let (arity, child_tier) = match self.places[position].level {
            Level::Node(arity) => (arity, SMALL),
            Level::Wrap => (1, LARGE),
            Level::First => panic!("circuit {position} is a first-level node"),
        };
        let tier = &self.tiers[child_tier];
        let session = self.session();
        let mut b = Builder::new();
        let zeros = matches!(inputs, NodeInputs::Shape).then(|| FixedColumns::zeros(&tier.taus));
        let mut claims = NodeClaims::default();
        let mut words = Vec::with_capacity(arity);
        let mut digests = Vec::with_capacity(arity);
        for i in 0..arity {
            let child = inputs.item(i);
            let statement = match child {
                Some(c) => c.statement.map(|&w| b.free_e(w)),
                None => TreeStatement::filled(self.statement, F192::ZERO).map(|&w| b.free_e(w)),
            };
            let kind = b.scope(format!("child {i} kind"), |b| {
                self.kind_bits(b, statement.kind(), child_tier)
            });
            let zero = b.k_const(0);
            let limbs: Vec<[Kw; 4]> = (statement.words().iter())
                .map(|&w| {
                    let [c0, c1, c2] = b.e_to_k(w);
                    [c0, c1, c2, zero]
                })
                .collect();
            let columns = child.map_or_else(|| zeros.as_ref().expect("zero columns from a shape"), |c| c.columns);
            let source = child.map_or(ProofSource::Shape, |c| ProofSource::Proof(c.proof, &c.openings));
            let rows = b.scope(format!("child {i}"), |b| {
                tier.child.verify(b, &session, &limbs, columns, source)
            });

            claims.bind_state(&mut b, rows.state);
            claims.bound.extend(rows.hints.iter().map(|h| h.value));
            let poly = if child_tier == SMALL {
                DensePoly::Fixed
            } else {
                DensePoly::Wide
            };
            claims
                .dense
                .push(fixed_claim(poly, &tier.fixed, &rows.hints, &kind.top));
            claims.matrices.push(MatrixClaim::fresh(hash::CIRCUIT, &rows.matrix));
            self.carried(&statement, kind.is_node, &mut claims);
            let digest = statement.digest_wire(&mut b);
            if self.claims.is_some() {
                digests.push(digest);
            } else {
                words.push(b.d_to_k(digest));
            }
        }
        let digest = match (self.places[position].level, self.union_shape(position)) {
            // A wrap states its child's set.
            (Level::Wrap, _) => digests[0],
            (_, Some(shape)) => shape.rows(&mut b, &session, &digests, inputs.union()),
            (_, None) => Items::Node.digest_rows(&mut b, &words),
        };
        NodeRows {
            b,
            position,
            digest,
            claims,
        }
    }

    /// A child's kind as the bits that select its circuit's block of its tier's fixed polynomial, and whether it is a
    /// node.
    ///
    /// With two kinds the kind is that bit; with more it is held to a kind of the tier's circuits, then split.
    fn kind_bits(&self, b: &mut Builder, kind: Ew, tier: usize) -> KindBits {
        if self.places.len() == 2 {
            let square = b.square(kind);
            b.eq(square, kind);
            return KindBits {
                top: vec![kind],
                is_node: kind,
            };
        }
        let t = &self.tiers[tier];
        let (zero, one) = (b.zero(), b.one());
        let vanishing = t.places.clone().fold(one, |acc, position| {
            let code = b.e_const(F192::new(self.code(position) as u64, 0, 0));
            let factor = b.add(kind, code);
            b.mul(acc, factor)
        });
        b.eq(vanishing, zero);
        // A kind is its first limb: its index's bits, then the tier's.
        let [word, ..] = b.e_to_k(kind);
        let bits = b.split(word);
        let above = (tier << self.tier_shift) >> t.kind_bits;
        for (j, &bit) in bits[t.kind_bits..].iter().enumerate() {
            b.eq_k_const(bit, (above >> j & 1) as u64);
        }
        let top: Vec<Ew> = bits[..t.kind_bits].iter().map(|&bit| b.k_to_e1(bit)).collect();
        // Only the small tier has a first level, at its index zero.
        if tier != SMALL {
            return KindBits { top, is_node: one };
        }
        let is_first = top.iter().fold(one, |acc, &t| {
            let not = b.add(t, one);
            b.mul(acc, not)
        });
        let is_node = b.add(is_first, one);
        KindBits { top, is_node }
    }

    /// A circuit built from the shapes alone.
    pub(crate) fn shape(&self, position: usize) -> Finished {
        let rows = match (self.places[position].level, &self.family) {
            (Level::First, Family::Runs(leaf)) => self.first_runs_rows(leaf, &NodeInputs::Shape),
            (Level::First, Family::Circuit(family)) => self.first_circuit_rows(family, &NodeInputs::Shape),
            (Level::Node(_) | Level::Wrap, _) => self.node_rows(&NodeInputs::Shape, position),
        };
        rows.reduce(self, ProofSource::Shape)
    }

    /// A leaf's program claim as point claims on the bytecode table and RAM's image.
    ///
    /// - Bit `i`'s share is `phi^i(T(phi^(-i)(chi), alpha))`, by its hinted value `D_i` at the point `(phi^(-i)(chi), alpha)`.
    /// - The image's share is its value at the point's low coordinates, the image being zero above them.
    fn program_claims(
        &self,
        b: &mut Builder,
        program: &Claim<ProgramPoint<Ew>, Ew>,
        inputs: &NodeInputs<'_, LeafWitness<'_>>,
        claims: &mut NodeClaims<Ew>,
    ) {
        let p = &program.point;
        let kbc = self.vars.0[DensePoly::Bytecode as usize] - N_TUPLE_BITS;
        let (chi, alpha) = p.bytecode.split_at(kbc);
        let ladders: Vec<Vec<Ew>> = chi.iter().map(|&x| inverse_frobenius_ladder(b, x, 1)).collect();
        let mut total = b.zero();
        for (i, &mu) in p.twist.iter().enumerate() {
            let point: Vec<Ew> = ladders.iter().map(|l| l[i]).chain(alpha.iter().copied()).collect();
            let d = inputs.hint(b, DensePoly::Bytecode, &point);
            let twisted = (0..i).fold(d, |x, _| b.square(x));
            total = b.mul_add(mu, twisted, total);
            claims.bound.push(d);
            claims.dense.push(DenseClaim::at(DensePoly::Bytecode, point, None, d));
        }
        let m = self.vars.0[DensePoly::Image as usize];
        let low = p.image_point[..m].to_vec();
        let image = inputs.hint(b, DensePoly::Image, &low);
        let above = (p.image_point[m..].iter()).fold(p.image_weight, |acc, &x| b.times_one_plus(acc, x));
        total = b.mul_add(above, image, total);
        b.eq(total, program.value);
        claims.bound.push(image);
        claims.dense.push(DenseClaim::at(DensePoly::Image, low, None, image));
    }

    /// The claims a child's statement carries, each on a polynomial the leaves do not fix scaled by `is_node`.
    ///
    /// A first-level node's statement is zero on such a polynomial, and `is_node`, the scale, is zero.
    fn carried(&self, statement: &TreeStatement<Ew>, is_node: Ew, claims: &mut NodeClaims<Ew>) {
        let point = statement.dense_point();
        for poly in self.statement.polys() {
            let n = self.vars.0[poly as usize];
            let scale = (!self.leaves_fix(poly)).then_some(is_node);
            claims.dense.push(DenseClaim::at(
                poly,
                point[..n].to_vec(),
                scale,
                statement.dense_value(poly),
            ));
        }
        for f in CircuitId::ALL {
            claims.matrices.extend(MatrixClaim::carried(
                f,
                f.k_log(),
                statement.rows(),
                statement.cols(),
                statement.matrices(f),
            ));
        }
    }
}

/// A circuit's hinted fixed-column evaluations as claims on a fixed polynomial whose stack of that circuit has this
/// layout.
///
/// Column `c` at the bus point's prefix `p` is the polynomial at `(p, block_c, top)`: `top` the kind's bits, if the
/// polynomial holds several circuits' stacks.
fn fixed_claim(poly: DensePoly, layout: &FixedLayout, hints: &[FixedHint], top: &[Ew]) -> DenseClaim<Ew> {
    let low = hints
        .iter()
        .map(|h| &h.point)
        .max_by_key(|p| p.len())
        .cloned()
        .unwrap_or_default();
    let terms = (hints.iter())
        .map(|h| {
            let n_low = h.point.len();
            assert!(
                n_low == layout.tau(h.column) && h.point[..] == low[..n_low],
                "a fixed column is read at its prefix of the bus point"
            );
            DenseTerm {
                n_low,
                bits: Bits {
                    value: layout.block(h.column),
                    len: layout.kappa() - n_low,
                },
                top: top.to_vec(),
                scale: None,
                value: h.value,
            }
        })
        .collect();
    DenseClaim { poly, low, terms }
}
impl NodeRows {
    /// The position of its circuit in the tree.
    pub(crate) const fn position(&self) -> usize {
        self.position
    }

    /// The claims' values, which the prover's reduction takes.
    pub(crate) fn claim_values(&self) -> NodeClaims<F192> {
        self.claims.map(|w| self.b.e(w))
    }

    /// Verify the reduction the given source holds, then expose the statement: the kind, the digest, the reduced claims.
    pub(crate) fn reduce(mut self, design: &Design<'_>, source: ProofSource<'_>) -> Finished {
        let b = &mut self.b;
        let claims = &self.claims;

        // The instance is every value the claims rest on, their count first.
        let count = b.k_const(claims.bound.len() as u64);
        let mut instance = vec![count];
        for &x in &claims.bound {
            instance.extend(b.e_to_k(x));
        }
        let session = SessionId::tagged(reduce::SESSION_TAG, &design.session().0);
        let mut t = Transcript::new(b, &session, &instance, source);
        let reduced = b.scope("reduction", |b| {
            infallible(claims.verify(&mut Rows::new(b, &mut t), &design.vars))
        });
        if !t.finished() {
            b.scope("reduction", |b| {
                b.fail("the reduction has data the verifier never reads");
            });
        }
        let kind = design.code(self.position);
        let statement = TreeStatement::from_reduced(b, design.statement, kind, self.digest, &reduced);
        for &w in statement.words() {
            b.expose(w);
        }
        self.b.finish()
    }
}
