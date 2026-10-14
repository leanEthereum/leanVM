//! The tree's circuits, and their heights.
//!
//! - A first-level node verifies RISC-V proofs of the program, and of the proofs each assumes, turns their program claims into point claims, and reduces every claim.
//! - A node verifies recursion proofs of the tree's kinds, and reduces their fresh claims with the claims they carry.
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
use super::shape::TreeShape;
use super::statement::{Kind, StatementLayout, TreeStatement};
use super::union::{UnionFill, UnionShape};
use super::{AssumedProofs, ClaimShape, TreeError, reduce};
use crate::bus::N_TUPLE_BITS;
use crate::commitment::Rate;
use crate::cpu::{Claim, Lookup, Program, ProgramPoint};
use crate::rec::circuit::{ASSUMING_IV, Builder, Dw, Ew, Finished, Kw};
use crate::rec::fixed::{FixedColumns, FixedLayout};
use crate::rec::hash;
use crate::rec::table::PerRecTable;
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

/// Where one program's tables sit in the dense polynomials: alone, or as one half of a stack of two.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Slot {
    /// The bytecode table's entry variables.
    kbc: usize,
    /// The image's variables.
    m: usize,
    /// The half it fills when the leaves' program and the assumed one share the polynomials: their top variable.
    half: Option<usize>,
}

/// The proofs each leaf of a tree assumes: their shape, how many, and where their program sits.
pub(crate) struct Assumed<'p> {
    /// Their shape: the program, its tables' heights, its rate.
    pub(crate) shape: ProofShape<'p>,
    /// How many each leaf assumes.
    pub(crate) count: usize,
    /// Where their program sits in the dense polynomials.
    slot: Slot,
}

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
    /// The heights its circuits share.
    pub(crate) taus: PerRecTable<usize>,
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

/// What fixes a tree's circuits: the leaves' shape, the proofs they assume, the arities, the rate, the semantics, and
/// each tier's heights.
pub(crate) struct Design<'p> {
    /// The leaves' shape: the program, its tables' heights, its rate.
    pub(crate) leaf: ProofShape<'p>,
    /// Where the leaves' program sits in the dense polynomials.
    slot: Slot,
    /// The proofs each leaf assumes, if any.
    pub(crate) assumed: Option<Assumed<'p>>,
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

/// A leaf as a first-level node's prover holds it: its proof, which the native verifier accepted, and what it states.
pub(crate) struct LeafWitness<'a> {
    /// The proof.
    pub(crate) proof: &'a ProofTranscript,
    /// Every opening its native verifier authenticated, phase by phase.
    pub(crate) openings: Vec<Openings>,
    /// The output it proves, its run's exit output.
    pub(crate) output: [u64; 4],
    /// The digest of its run's committed values: its output when it assumes nothing.
    pub(crate) committed: [u64; 4],
    /// The proofs it assumes, in order, each assuming nothing.
    pub(crate) assumed: Vec<Self>,
    /// In a claim-set tree, the digest of its claim set, whose hash is its output.
    pub(crate) set: [u64; 4],
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
    /// The digest it states: of the leaves' outputs under it, or of its claim set.
    digest: Dw,
    /// The claims its rows leave.
    claims: NodeClaims<Ew>,
}

impl<T> NodeInputs<'_, T> {
    /// Proof `i`, when a prover holds it.
    const fn item(&self, i: usize) -> Option<&T> {
        match self {
            Self::Shape => None,
            Self::Prove { items, .. } => Some(&items[i]),
        }
    }

    /// A dense polynomial's value at a point then public bits, as a hint: only the prover's tables give it, zero from
    /// the shapes.
    fn hint(&self, b: &mut Builder, poly: DensePoly, point: &[Ew], bits: Bits) -> Ew {
        let value = match self {
            Self::Shape => F192::ZERO,
            Self::Prove { tables, .. } => {
                let bit = |i: usize| F192::new((bits.value >> i & 1) as u64, 0, 0);
                let at: Vec<F192> = (point.iter().map(|&w| b.e(w))).chain((0..bits.len).map(bit)).collect();
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

impl Slot {
    /// The slot of a program's tables, in the given half of a stack of two if any.
    fn of(program: &Program, half: Option<usize>) -> Self {
        let rv = program.rv();
        Self {
            kbc: crate::log2_strict_usize(rv.entries().len()),
            m: crate::log2_ceil_usize(rv.image().len().max(1)),
            half,
        }
    }

    /// The public coordinates that place a point of `n` coordinates on this program's tables in a polynomial of `vars`:
    /// zeros past the program's own variables, then its half.
    fn bits(self, n: usize, vars: usize) -> Bits {
        self.half.map_or_else(
            || {
                assert_eq!(n, vars, "a program alone fills its polynomial");
                Bits::NONE
            },
            |half| Bits {
                value: half << (vars - 1 - n),
                len: vars - n,
            },
        )
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
    /// The design of a tree over proofs of a program, each assuming `assumed`'s proofs if any, at the given heights of
    /// each tier's circuits.
    ///
    /// # Errors
    ///
    /// Returns an error if no proof of the program, or of the assumed one, has the leaves' or the assumed proofs' shape,
    /// or the heights admit no recursion proof.
    pub(crate) fn new(
        program: &'p Program,
        shape: &TreeShape,
        assumed: Option<AssumedProofs<'p>>,
        taus: &[PerRecTable<usize>],
    ) -> Result<Self, TreeError> {
        let TreeShape {
            leaf,
            arity_0,
            arity,
            rate,
            claims,
        } = *shape;
        let of = |program, s| ProofShape::new(program, s).map_err(|e| TreeError::LeafShape(e.into()));
        let leaf = of(program, leaf)?;
        let assumed = assumed.map(|a| Ok((of(a.program, a.leaf)?, a.count))).transpose()?;
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
        let slot = Slot::of(leaf.program(), assumed.as_ref().map(|_| 0));
        let assumed = assumed.map(|(shape, count)| Assumed {
            slot: Slot::of(shape.program(), Some(1)),
            shape,
            count,
        });
        // Two programs stack their tables, each padded to the larger, under one more variable.
        let slots = [Some(slot), assumed.as_ref().map(|a| a.slot)];
        let most = |f: fn(&Slot) -> usize| slots.iter().flatten().map(f).max().unwrap_or(0);
        let halves = usize::from(assumed.is_some());
        let vars = DenseVars([
            most(|s| s.kbc) + N_TUPLE_BITS + halves,
            most(|s| s.m) + halves,
            fixed_vars(SMALL),
            fixed_vars(LARGE),
        ]);
        // A tree of one tier has no wide polynomial, the last.
        let n_polys = DensePoly::COUNT - usize::from(tiers.len() == 1);
        let statement = StatementLayout::new(vars.0.into_iter().max().unwrap_or(0), n_polys);
        Ok(Self {
            leaf,
            slot,
            assumed,
            arity_0,
            arity,
            rate,
            claims,
            places,
            tiers,
            tier_shift,
            vars,
            statement,
        })
    }

    /// The transcript's session: everything that fixes the circuits, as one tag.
    ///
    /// Every kind shares it.
    /// The kind is the statement's first word, and the statement is the transcript's instance.
    /// A tree of outputs and a claim-set tree differ in it, so a proof of one is never one of the other.
    pub(crate) fn session(&self) -> SessionId {
        self.session_under(DOMAIN)
    }

    /// The session under a protocol version's tag.
    pub(super) fn session_under(&self, domain: &[u8]) -> SessionId {
        let mut tag = domain.to_vec();
        tag.extend_from_slice(self.leaf.program().digest());
        let large = self.claims.map(|c| c.capacity);
        let semantics = large.map_or([0; 3], |c| [1, c.claims, c.groups]);
        let small = (self.claims.and_then(|c| c.small)).map(|s| [s.arity, s.capacity.claims, s.capacity.groups]);
        let leaf = self.leaf.shape();
        let sizes = (leaf.taus().values().copied())
            .chain([self.arity_0, self.arity, self.statement.len()])
            .chain(semantics)
            .chain(small.into_iter().flatten())
            .chain(self.tiers.iter().flat_map(|t| t.taus.into_values()));
        for x in sizes {
            tag.extend_from_slice(&(x as u64).to_le_bytes());
        }
        tag.extend_from_slice(&[leaf.rate().log_inv_rate(), self.rate.log_inv_rate()]);
        // A tree resolving assumptions also names the assumed proofs: their program, how many, their shape.
        if let Some(a) = &self.assumed {
            let assumed = a.shape.shape();
            tag.extend_from_slice(a.shape.program().digest());
            for x in std::iter::once(a.count).chain(assumed.taus().values().copied()) {
                tag.extend_from_slice(&(x as u64).to_le_bytes());
            }
            tag.push(assumed.rate().log_inv_rate());
        }
        SessionId::new(&tag)
    }

    /// The dense polynomials the root's claims are settled against: the bytecode tables, the images, each tier's fixed
    /// polynomial.
    ///
    /// With assumed proofs, the leaves' program's table is the lower half of each of the first two, the assumed
    /// program's the upper.
    pub(crate) fn tables(&self, [small, large]: [Vec<F64>; 2]) -> DenseTables {
        let programs: Vec<&Program> = [
            Some(self.leaf.program()),
            self.assumed.as_ref().map(|a| a.shape.program()),
        ]
        .into_iter()
        .flatten()
        .collect();
        let stack = |poly: DensePoly, table: fn(&Program) -> Vec<F64>| -> Vec<F64> {
            let half = (1 << self.vars.0[poly as usize]) / programs.len();
            (programs.iter())
                .flat_map(|&p| {
                    let mut t = table(p);
                    t.resize(half, F64::ZERO);
                    t
                })
                .collect()
        };
        DenseTables([
            stack(DensePoly::Bytecode, |p| Lookup::Bytecode.table(p.rv())),
            stack(DensePoly::Image, |p| p.rv().image().iter().map(|&w| F64(w)).collect()),
            small,
            large,
        ])
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

    /// The first level's rows, verifying its leaves and the proofs they assume.
    ///
    /// A leaf that assumes proofs states its committed values' digest: the rows verify each assumed proof, fold the
    /// assumed program's digest and each one's output with that digest as the leaf's guest did, and verify the leaf's
    /// proof against the fold.
    pub(crate) fn first_rows(&self, inputs: &NodeInputs<'_, LeafWitness<'_>>) -> NodeRows {
        let mut b = Builder::new();
        let mut claims = NodeClaims::default();
        let mut outputs = Vec::with_capacity(self.arity_0);
        let mut sets = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let leaf = inputs.item(i);
            // What the leaf states, its committed values' digest: in a claim-set tree, the hash of its set's digest,
            // which the union reads.
            let committed = if self.claims.is_some() {
                let set = b.free_d(leaf.map_or([0; 4], |l| l.set));
                sets.push(set);
                let words = b.d_to_k(set);
                let committed = b.chain(&words);
                b.d_to_k(committed)
            } else {
                leaf.map_or([0; 4], |l| l.committed).map(|w| b.free_k(w))
            };
            // The output its run exits with: the digest itself, or folded with the assumed proofs' outputs.
            let output = self.assumed.as_ref().map_or(committed, |a| {
                let assumed: Vec<[Kw; 4]> = (0..a.count)
                    .map(|j| {
                        let proof = leaf.map(|l| &l.assumed[j]);
                        let output = proof.map_or([0; 4], |l| l.output).map(|o| b.free_k(o));
                        b.scope(format!("leaf {i} assumption {j}"), |b| {
                            self.verified(b, (&a.shape, a.slot), output, proof, inputs, &mut claims);
                        });
                        output
                    })
                    .collect();
                b.scope(format!("leaf {i} assumptions"), |b| {
                    let program = a.shape.program().digest_words().map(|w| b.k_const(w));
                    let folded = assuming_rows(b, committed, program, &assumed);
                    b.d_to_k(folded)
                })
            });
            b.scope(format!("leaf {i}"), |b| {
                self.verified(b, (&self.leaf, self.slot), output, leaf, inputs, &mut claims);
            });
            outputs.push(committed);
        }
        let digest = match self.union_shape(0) {
            Some(shape) => shape.rows(&mut b, &self.session(), &sets, inputs.union()),
            None => Kind::First.digest_rows(&mut b, &outputs),
        };
        NodeRows {
            b,
            position: 0,
            digest,
            claims,
        }
    }

    /// One RISC-V proof's core in rows, of a program of this shape and slot, against the output on `output`, its claims
    /// added to the node's.
    fn verified(
        &self,
        b: &mut Builder,
        (shape, slot): (&ProofShape<'_>, Slot),
        output: [Kw; 4],
        proof: Option<&LeafWitness<'_>>,
        inputs: &NodeInputs<'_, LeafWitness<'_>>,
        claims: &mut NodeClaims<Ew>,
    ) {
        let source = proof.map_or(ProofSource::Shape, |l| ProofSource::Proof(l.proof, &l.openings));
        let core = shape.verify_core(b, output, source);
        claims.bind_state(b, core.state);
        b.scope("program", |b| {
            self.program_claims(b, &core.claims.program, slot, inputs, claims);
        });
        let fresh = CircuitId::ALL.into_iter().zip(&core.claims.circuits);
        claims.matrices.extend(fresh.map(|(f, c)| MatrixClaim::fresh(f, c)));
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
            claims.dense.push(self.fixed_claim(&rows.hints, &kind.top, child_tier));
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
            (_, None) => Kind::Node.digest_rows(&mut b, &words),
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
        let rows = match self.places[position].level {
            Level::First => self.first_rows(&NodeInputs::Shape),
            Level::Node(_) | Level::Wrap => self.node_rows(&NodeInputs::Shape, position),
        };
        rows.reduce(self, ProofSource::Shape)
    }

    /// A proof's program claim as point claims on the bytecode table and RAM's image, in its program's slot.
    ///
    /// - Bit `i`'s share is `phi^i(T(phi^(-i)(chi), alpha))`, by its hinted value `D_i` at the point `(phi^(-i)(chi), alpha)`.
    /// - The image's share is its value at the point's low coordinates, the image being zero above them.
    fn program_claims(
        &self,
        b: &mut Builder,
        program: &Claim<ProgramPoint<Ew>, Ew>,
        slot: Slot,
        inputs: &NodeInputs<'_, LeafWitness<'_>>,
        claims: &mut NodeClaims<Ew>,
    ) {
        let p = &program.point;
        let (chi, alpha) = p.bytecode.split_at(slot.kbc);
        let ladders: Vec<Vec<Ew>> = chi.iter().map(|&x| inverse_frobenius_ladder(b, x, 1)).collect();
        let mut total = b.zero();
        let vars = self.vars.0[DensePoly::Bytecode as usize];
        for (i, &mu) in p.twist.iter().enumerate() {
            let point: Vec<Ew> = ladders.iter().map(|l| l[i]).chain(alpha.iter().copied()).collect();
            let bits = slot.bits(point.len(), vars);
            let d = inputs.hint(b, DensePoly::Bytecode, &point, bits);
            let twisted = (0..i).fold(d, |x, _| b.square(x));
            total = b.mul_add(mu, twisted, total);
            claims.bound.push(d);
            claims
                .dense
                .push(DenseClaim::at_bits(DensePoly::Bytecode, point, bits, d));
        }
        let low = p.image_point[..slot.m].to_vec();
        let bits = slot.bits(slot.m, self.vars.0[DensePoly::Image as usize]);
        let image = inputs.hint(b, DensePoly::Image, &low, bits);
        let above = (p.image_point[slot.m..].iter()).fold(p.image_weight, |acc, &x| b.times_one_plus(acc, x));
        total = b.mul_add(above, image, total);
        b.eq(total, program.value);
        claims.bound.push(image);
        claims
            .dense
            .push(DenseClaim::at_bits(DensePoly::Image, low, bits, image));
    }

    /// A child's hinted fixed-column evaluations as claims on its tier's fixed polynomial, in its circuit's block.
    ///
    /// Column `c` at the bus point's prefix `p` is the fixed polynomial at `(p, block_c, kind's bits)`.
    fn fixed_claim(&self, hints: &[FixedHint], top: &[Ew], tier: usize) -> DenseClaim<Ew> {
        let fixed = &self.tiers[tier].fixed;
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
                    n_low == fixed.tau(h.column) && h.point[..] == low[..n_low],
                    "a fixed column is read at its prefix of the bus point"
                );
                DenseTerm {
                    n_low,
                    bits: Bits {
                        value: fixed.block(h.column),
                        len: fixed.kappa() - n_low,
                    },
                    top: top.to_vec(),
                    scale: None,
                    value: h.value,
                }
            })
            .collect();
        DenseClaim {
            poly: if tier == SMALL {
                DensePoly::Fixed
            } else {
                DensePoly::Wide
            },
            low,
            terms,
        }
    }

    /// The claims a child's statement carries.
    ///
    /// A first-level node reduces no claim on a fixed polynomial, so its carried ones are scaled by `is_node`, zero.
    fn carried(&self, statement: &TreeStatement<Ew>, is_node: Ew, claims: &mut NodeClaims<Ew>) {
        let point = statement.dense_point();
        for &poly in self.statement.polys() {
            let n = self.vars.0[poly as usize];
            let scale = poly.is_fixed().then_some(is_node);
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

/// The output a run committing values of digest `committed` exits with, having assumed runs of the program of digest
/// `program` exiting with `outputs`, in order: `Output::assuming`, in rows, one hash row per assumption and one more.
pub(crate) fn assuming_rows(b: &mut Builder, committed: [Kw; 4], program: [Kw; 4], outputs: &[[Kw; 4]]) -> Dw {
    let words: Vec<Kw> = (outputs.iter())
        .flat_map(|o| program.into_iter().chain(*o))
        .chain(committed)
        .collect();
    b.chain_from(ASSUMING_IV, &words)
}
