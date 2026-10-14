//! The tree's circuits, and their heights.
//!
//! - A first-level node verifies RISC-V proofs of the program, turns their program claims into point claims, and reduces every claim.
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
use super::{ClaimShape, TreeError, reduce};
use crate::bus::N_TUPLE_BITS;
use crate::commitment::Rate;
use crate::cpu::{Claim, Program, ProgramPoint};
use crate::rec::circuit::{Builder, Dw, Ew, Finished, Kw};
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
use primitives::field::F192;
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

/// What fixes a tree's circuits: the leaves' shape, the arities, the rate, the semantics, and each tier's heights.
pub(crate) struct Design<'p> {
    /// The leaves' shape: the program, its tables' heights, its rate.
    pub(crate) leaf: ProofShape<'p>,
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
    /// Returns an error if no proof of the program has the leaves' shape, or the heights admit no recursion proof.
    pub(crate) fn new(program: &'p Program, shape: &TreeShape, taus: &[PerRecTable<usize>]) -> Result<Self, TreeError> {
        let TreeShape {
            leaf,
            arity_0,
            arity,
            rate,
            claims,
        } = *shape;
        let leaf = ProofShape::new(program, leaf).map_err(|e| TreeError::LeafShape(e.into()))?;
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
        let rv = leaf.program().rv();
        let vars = DenseVars([
            crate::log2_strict_usize(rv.entries().len()) + N_TUPLE_BITS,
            crate::log2_ceil_usize(rv.image().len().max(1)),
            fixed_vars(SMALL),
            fixed_vars(LARGE),
        ]);
        // A tree of one tier has no wide polynomial, the last.
        let n_polys = DensePoly::COUNT - usize::from(tiers.len() == 1);
        let statement = StatementLayout::new(vars.0.into_iter().max().unwrap_or(0), n_polys);
        Ok(Self {
            leaf,
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

    /// The first level's rows, verifying its leaves.
    pub(crate) fn first_rows(&self, inputs: &NodeInputs<'_, LeafWitness<'_>>) -> NodeRows {
        let mut b = Builder::new();
        let mut claims = NodeClaims::default();
        let mut outputs = Vec::with_capacity(self.arity_0);
        let mut sets = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let leaf = inputs.item(i);
            // A claim-set leaf's output is the hash of its set's digest, which the union reads.
            let output = if self.claims.is_some() {
                let set = b.free_d(leaf.map_or([0; 4], |l| l.set));
                sets.push(set);
                let words = b.d_to_k(set);
                let output = b.chain(&words);
                b.d_to_k(output)
            } else {
                leaf.map_or([0; 4], |l| l.output).map(|o| b.free_k(o))
            };
            let source = leaf.map_or(ProofSource::Shape, |l| ProofSource::Proof(l.proof, &l.openings));
            let core = b.scope(format!("leaf {i}"), |b| self.leaf.verify_core(b, output, source));
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
            None => Kind::First.digest_rows(&mut b, &outputs),
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
