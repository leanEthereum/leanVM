//! The tree's two circuits, and the heights they share.
//!
//! - A first-level node verifies RISC-V proofs of the program, turns their program claims into point claims, and reduces every claim.
//! - A node verifies recursion proofs of either kind, and reduces their fresh claims with the claims they carry.
//!
//! Both circuits have the same heights, so a node verifies a child of either kind with one set of rows.

use super::claims::{Bits, DenseClaim, DensePoly, DenseTerm, MatrixClaim, NodeClaims};
use super::fixed::FixedLayout;
use super::reduce::{DenseTables, DenseVars, Reduced};
use super::statement::{Kind, Section, StatementLayout, TreeStatement, digest_halves_rows};
use super::{TreeError, reduce};
use crate::class_flock::FlockId;
use crate::cpu::{Claim, ProgramPoint};
use crate::leaf::N_TUPLE_BITS;
use crate::pcs::Rate;
use crate::rec::circuit::{Builder, Dw, Ew, Finished, Kw};
use crate::rec::fixed::FixedColumns;
use crate::rec::table::{HashFlock, PerRecTable};
use crate::rec::transcript::{ProofSource, Transcript};
use crate::rec::verifier::{FixedHint, ProofShape, RecShape, Rows, infallible};
use fiat_shamir::arith::Arith;
use fiat_shamir::transcript::RawProof;
use pcs::ring_switch::inverse_frobenius_ladder;
use primitives::field::{F64, F192};
use primitives::hash::Hasher;
use primitives::multilinear::mle_eval_par;

/// The domain of every tree proof's transcript.
const DOMAIN: &[u8] = b"leanvm-tree-6";

/// What fixes a tree's circuits: the leaves' shape, the arities, the rate, and the nodes' heights.
pub(crate) struct Design<'p> {
    /// The leaves' shape: the program, its tables' heights, its rate.
    pub(crate) leaf: ProofShape<'p>,
    /// The leaves a first-level node verifies.
    pub(crate) arity_0: usize,
    /// The children a node verifies.
    pub(crate) arity: usize,
    /// Every tree proof's rate.
    pub(crate) rate: Rate,
    /// The nodes' heights, which both circuits share.
    pub(crate) taus: PerRecTable<usize>,
    /// The shape of a child recursion proof.
    child: RecShape,
    /// Where each fixed column sits in one circuit's stack.
    pub(crate) fixed: FixedLayout,
    /// Each dense polynomial's variables.
    pub(crate) vars: DenseVars,
    /// Where each part of a statement sits.
    pub(crate) statement: StatementLayout,
    /// The transcript's seed for every proof of the tree.
    pub(crate) iv: [F64; 4],
}

/// A leaf as a first-level node's prover holds it: its proof as its verifier read it, and its output.
pub(crate) struct LeafWitness {
    /// The proof, its Merkle paths written out.
    pub(crate) raw: RawProof,
    /// The output it proves.
    pub(crate) output: [u64; 4],
}

/// A child as a node's prover holds it: its statement, its proof as its verifier read it, and its circuit's fixed columns.
pub(crate) struct ChildWitness<'a> {
    /// What it states.
    pub(crate) statement: &'a TreeStatement,
    /// The proof, its Merkle paths written out.
    pub(crate) raw: RawProof,
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
    },
}

/// A circuit's rows up to its reduction: they verify its proofs, and leave the claims the reduction takes.
pub(crate) struct NodeRows {
    /// The circuit so far, and its values.
    b: Builder,
    /// The circuit's kind.
    kind: Kind,
    /// The digest of the leaves' outputs under it.
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
}

impl NodeClaims<Ew> {
    /// Bind a verified proof's final transcript state, as two scalars: its first three words, then its fourth.
    fn bind_state(&mut self, b: &mut Builder, state: Dw) {
        let [w0, w1, w2, w3] = b.d_to_k(state);
        self.bound.extend([b.k_to_e([w0, w1, w2]), b.k_to_e1(w3)]);
    }
}

impl<'p> Design<'p> {
    /// The design at the given heights of both circuits.
    ///
    /// # Errors
    ///
    /// Returns an error if the heights admit no recursion proof.
    pub(crate) fn new(
        leaf: ProofShape<'p>,
        arity_0: usize,
        arity: usize,
        rate: Rate,
        taus: PerRecTable<usize>,
    ) -> Result<Self, TreeError> {
        let child = RecShape::new(taus, rate).map_err(|_| TreeError::TooLarge)?;
        let fixed = FixedLayout::new(&taus);
        let rv = leaf.program().rv();
        let vars = DenseVars([
            crate::log2_strict_usize(rv.entries().len()) + N_TUPLE_BITS,
            crate::log2_ceil_usize(rv.image().len().max(1)),
            fixed.kappa() + 1,
        ]);
        let statement = StatementLayout::new(vars.0.into_iter().max().unwrap_or(0));
        let mut design = Self {
            leaf,
            arity_0,
            arity,
            rate,
            taus,
            child,
            fixed,
            vars,
            statement,
            iv: [F64::ZERO; 4],
        };
        design.iv = design.seed();
        Ok(design)
    }

    /// The transcript's seed: everything that fixes the circuits.
    ///
    /// Both kinds share it.
    /// The kind is the statement's first word, and the statement's hash is the transcript's first block.
    fn seed(&self) -> [F64; 4] {
        let mut h = Hasher::new();
        h.update(DOMAIN);
        h.update(self.leaf.program().digest());
        let sizes = (self.leaf.taus().values().copied())
            .chain([self.arity_0, self.arity, self.statement.len()])
            .chain(self.taus.into_values());
        for x in sizes {
            h.update(&(x as u64).to_le_bytes());
        }
        h.update(&[self.leaf.rate().log_inv_rate(), self.rate.log_inv_rate()]);
        fiat_shamir::digest_words(&h.finalize())
    }

    /// The first level's rows, verifying its leaves.
    pub(crate) fn first(&self, inputs: &NodeInputs<'_, LeafWitness>) -> NodeRows {
        let mut b = Builder::new();
        let mut claims = NodeClaims::default();
        let mut outputs = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let leaf = inputs.item(i);
            let output = leaf.map_or([0; 4], |l| l.output).map(|o| b.free_k(o));
            let source = leaf.map_or(ProofSource::Shape, |l| ProofSource::Proof(&l.raw));
            let core = b.scope(format!("leaf {i}"), |b| self.leaf.verify_core(b, output, source));
            claims.bind_state(&mut b, core.state);
            b.scope(format!("leaf {i} program"), |b| {
                self.program_claims(b, &core.claims.program, inputs, &mut claims);
            });
            let fresh = FlockId::ALL.into_iter().zip(&core.claims.circuits);
            claims.matrices.extend(fresh.map(|(f, c)| MatrixClaim::fresh(f, c)));
            outputs.push(output);
        }
        let digest = Kind::First.digest_rows(&mut b, &outputs);
        NodeRows {
            b,
            kind: Kind::First,
            digest,
            claims,
        }
    }

    /// The node's rows, verifying its children, of either kind.
    pub(crate) fn node(&self, inputs: &NodeInputs<'_, ChildWitness<'_>>) -> NodeRows {
        let mut b = Builder::new();
        let iv = b.d_const(self.iv.map(|w| w.0));
        let zeros = matches!(inputs, NodeInputs::Shape).then(|| FixedColumns::zeros(&self.taus));
        let mut claims = NodeClaims::default();
        let mut digests = Vec::with_capacity(self.arity);
        for i in 0..self.arity {
            let child = inputs.item(i);
            let statement = match child {
                Some(c) => c.statement.map(|&w| b.free_e(w)),
                None => TreeStatement::filled(self.statement, F192::ZERO).map(|&w| b.free_e(w)),
            };
            // The kind is a bit: it selects the child's circuit's half of the fixed polynomial.
            let kind = statement.kind();
            b.scope(format!("child {i} kind"), |b| {
                let square = b.square(kind);
                b.eq_e(square, kind);
            });
            let zero = b.k_const(0);
            let limbs: Vec<[Kw; 4]> = (statement.words().iter())
                .map(|&w| {
                    let [c0, c1, c2] = b.e_to_k(w);
                    [c0, c1, c2, zero]
                })
                .collect();
            let columns = child.map_or_else(|| zeros.as_ref().expect("zero columns from a shape"), |c| c.columns);
            let source = child.map_or(ProofSource::Shape, |c| ProofSource::Proof(&c.raw));
            let rows = b.scope(format!("child {i}"), |b| {
                self.child.verify(b, iv, &limbs, columns, source)
            });

            claims.bind_state(&mut b, rows.state);
            claims.bound.extend(rows.hints.iter().map(|h| h.value));
            claims.dense.push(self.fixed_claim(&rows.hints, kind));
            claims.matrices.push(MatrixClaim::fresh(HashFlock::FLOCK, &rows.matrix));
            self.carried(&statement, kind, &mut claims);
            let digest = statement.digest_wire(&mut b);
            digests.push(b.d_to_k(digest));
        }
        let digest = Kind::Node.digest_rows(&mut b, &digests);
        NodeRows {
            b,
            kind: Kind::Node,
            digest,
            claims,
        }
    }

    /// A circuit built from the shapes alone.
    pub(crate) fn shape(&self, kind: Kind) -> Finished {
        let rows = match kind {
            Kind::First => self.first(&NodeInputs::Shape),
            Kind::Node => self.node(&NodeInputs::Shape),
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
        inputs: &NodeInputs<'_, LeafWitness>,
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
        b.eq_e(total, program.value);
        claims.bound.push(image);
        claims.dense.push(DenseClaim::at(DensePoly::Image, low, None, image));
    }

    /// A child's hinted fixed-column evaluations as claims on the fixed polynomial, in its circuit's half.
    ///
    /// Column `c` at the bus point's prefix `p` is the fixed polynomial at `(p, block_c, kind)`.
    fn fixed_claim(&self, hints: &[FixedHint], kind: Ew) -> DenseClaim<Ew> {
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
                    n_low == self.fixed.tau(h.column) && h.point[..] == low[..n_low],
                    "a fixed column is read at its prefix of the bus point"
                );
                DenseTerm {
                    n_low,
                    bits: Bits {
                        value: self.fixed.block(h.column),
                        len: self.fixed.kappa() - n_low,
                    },
                    top: Some(kind),
                    scale: None,
                    value: h.value,
                }
            })
            .collect();
        DenseClaim {
            poly: DensePoly::Fixed,
            low,
            terms,
        }
    }

    /// The claims a child's statement carries.
    ///
    /// A first-level node reduces no claim on the fixed polynomial, so its carried one is scaled by its kind, zero.
    fn carried(&self, statement: &TreeStatement<Ew>, kind: Ew, claims: &mut NodeClaims<Ew>) {
        let point = statement.dense_point();
        for poly in DensePoly::ALL {
            let n = self.vars.0[poly as usize];
            let scale = (poly == DensePoly::Fixed).then_some(kind);
            claims.dense.push(DenseClaim::at(
                poly,
                point[..n].to_vec(),
                scale,
                statement.dense_value(poly),
            ));
        }
        for f in FlockId::ALL {
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

impl Reduced<Ew> {
    /// The statement of a circuit of this kind and digest whose reduction left these claims.
    ///
    /// A polynomial left unreduced has a zero value, and the point is zero past the reduction's rounds.
    fn statement(&self, b: &mut Builder, layout: StatementLayout, kind: Kind, digest: Dw) -> TreeStatement<Ew> {
        let zero = b.zero();
        let mut s = TreeStatement::filled(layout, zero);
        s.section_mut(Section::Kind)[0] = b.e_const(F192::new(kind.bit(), 0, 0));
        s.section_mut(Section::Digest)
            .copy_from_slice(&digest_halves_rows(b, digest));
        s.section_mut(Section::DensePoint)[..self.dense.point.len()].copy_from_slice(&self.dense.point);
        let values = self.dense.values.map(|v| v.unwrap_or(zero));
        s.section_mut(Section::DenseValues).copy_from_slice(&values);
        s.section_mut(Section::Rows).copy_from_slice(&self.matrices.rows);
        s.section_mut(Section::Cols).copy_from_slice(&self.matrices.cols);
        s.section_mut(Section::Matrices)
            .copy_from_slice(self.matrices.values.as_flattened());
        s
    }
}

impl NodeRows {
    /// The claims' values, which the prover's reduction takes.
    pub(crate) fn claim_values(&self) -> NodeClaims<F192> {
        self.claims.map(|w| self.b.e(w))
    }

    /// Verify the reduction the given source holds, then expose the statement: the kind, the digest, the reduced claims.
    pub(crate) fn reduce(mut self, design: &Design<'_>, source: ProofSource<'_>) -> Finished {
        let b = &mut self.b;
        let state = b.d_const(reduce::initial_state());
        let mut t = Transcript::from_state(state, source);
        let claims = &self.claims;
        let reduced = b.scope("reduction", |b| {
            infallible(claims.verify(&mut Rows::new(b, &mut t), &design.vars))
        });
        if !t.finished() {
            b.scope("reduction", |b| {
                b.fail("the reduction has data the verifier never reads");
            });
        }
        let statement = reduced.statement(b, design.statement, self.kind, self.digest);
        for &w in statement.words() {
            b.expose_e(w);
        }
        self.b.finish()
    }
}
