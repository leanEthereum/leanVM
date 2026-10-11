//! The tree's circuits, one per kind, and the heights they share.
//!
//! - A first-level node verifies leaves of one family, and reduces every claim they leave. RISC-V proofs of the program leave program claims, which become point claims on the bytecode table and the image; proofs of one recursion circuit leave hinted evaluations of that circuit's fixed columns, which become claims on the leaves' fixed polynomial.
//! - A node verifies tree proofs of any kind, and reduces their fresh claims with the claims they carry, each weighed by whether a child of its kind carries it.
//!
//! Every kind's circuit has the same heights, so a node verifies a child of any kind with one set of rows.

use super::claims::{Bits, DenseClaim, DensePoly, DenseTerm, MatrixClaim, NodeClaims};
use super::fixed::{FixedLayout, side_by_side};
use super::reduce::{DenseTables, DenseVars, Reduced};
use super::statement::{Kind, Level, Section, StatementLayout, TreeStatement, digest_halves_rows};
use super::{LeafCircuit, TreeError, reduce};
use crate::class_flock::FlockId;
use crate::cpu::{Claim, Lookup, ProgramPoint};
use crate::leaf::N_TUPLE_BITS;
use crate::pcs::Rate;
use crate::rec::circuit::{Builder, Dw, Ew, Finished, Kw, Limbs};
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
const DOMAIN: &[u8] = b"leanvm-tree-11";

/// One family of leaves, as the tree's circuits verify them.
pub(crate) enum Family<'p> {
    /// RISC-V proofs of one program, of one shape: the program, its tables' heights, its rate.
    Runs(ProofShape<'p>),
    /// Proofs of one recursion circuit.
    Circuit(CircuitFamily<'p>),
}

/// Proofs of one recursion circuit, as a first-level node verifies them.
pub(crate) struct CircuitFamily<'p> {
    /// The circuit, its fixed columns, its seed and its proofs' rate.
    pub(crate) leaf: LeafCircuit<'p>,
    /// The shape of its proofs, at its own heights.
    shape: RecShape,
    /// Where each of its fixed columns sits in its stack.
    fixed: FixedLayout,
    /// Its stack's place among the leaf circuits' in `W_leaf`.
    slot: usize,
}

/// What fixes a tree's circuits: the leaf families, the arities, the rate, and the nodes' heights.
pub(crate) struct Design<'p> {
    /// The leaf families, by index: `Kind::First(i)` verifies family `i`.
    pub(crate) families: Vec<Family<'p>>,
    /// The leaves a first-level node verifies.
    pub(crate) arity_0: usize,
    /// The children a node verifies.
    pub(crate) arity: usize,
    /// Every tree proof's rate.
    pub(crate) rate: Rate,
    /// The nodes' heights, which every kind's circuit shares.
    pub(crate) taus: PerRecTable<usize>,
    /// The shape of a child recursion proof.
    child: RecShape,
    /// Where each fixed column sits in one kind's circuit's stack.
    pub(crate) fixed: FixedLayout,
    /// The bits of a kind's code, which select its circuit's stack in `W_node`.
    pub(crate) kind_bits: usize,
    /// The variables of each leaf circuit's stack in `W_leaf`, the largest stack's.
    pub(crate) leaf_kappa: usize,
    /// The bits of a leaf circuit's slot, which select its stack in `W_leaf`.
    pub(crate) leaf_bits: usize,
    /// Each dense polynomial's variables.
    pub(crate) vars: DenseVars,
    /// Which dense polynomials the tree has.
    pub(crate) present: [bool; DensePoly::COUNT],
    /// Where each part of a statement sits.
    pub(crate) statement: StatementLayout,
    /// The transcript's seed for every proof of the tree.
    pub(crate) iv: [F64; 4],
}

/// A RISC-V leaf as a first-level node's prover holds it: its proof as its verifier read it, and its output.
pub(crate) struct LeafWitness {
    /// The proof, its Merkle paths written out.
    pub(crate) raw: RawProof,
    /// The output it proves.
    pub(crate) output: [u64; 4],
}

/// A leaf of a recursion circuit as a first-level node's prover holds it: its statement, its proof as its verifier read it, and its circuit's fixed columns.
pub(crate) struct CircuitWitness<'a> {
    /// What it states, word by word.
    pub(crate) statement: Vec<Limbs>,
    /// The proof, its Merkle paths written out.
    pub(crate) raw: RawProof,
    /// The fixed columns of its circuit.
    pub(crate) columns: &'a FixedColumns,
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
    /// The digest of what the leaves under it state.
    digest: Dw,
    /// The claims its rows leave.
    claims: NodeClaims<Ew>,
}

impl<'p> CircuitFamily<'p> {
    /// The family of a leaf circuit's proofs, its stack at `slot` in `W_leaf`.
    ///
    /// # Errors
    ///
    /// A circuit whose heights admit no recursion proof.
    pub(crate) fn new(leaf: LeafCircuit<'p>, slot: usize) -> Result<Self, TreeError> {
        let taus = leaf.circuit.heights();
        Ok(Self {
            shape: RecShape::new(taus, leaf.rate).map_err(|_| TreeError::TooLarge)?,
            fixed: FixedLayout::new(&taus),
            leaf,
            slot,
        })
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
}

impl NodeClaims<Ew> {
    /// Bind a verified proof's final transcript state, as two scalars: its first three words, then its fourth.
    fn bind_state(&mut self, b: &mut Builder, state: Dw) {
        let [w0, w1, w2, w3] = b.d_to_k(state);
        self.bound.extend([b.k_to_e([w0, w1, w2]), b.k_to_e1(w3)]);
    }
}

impl<'p> Design<'p> {
    /// The design at the given heights of every kind's circuit.
    ///
    /// # Errors
    ///
    /// Returns an error if the heights admit no recursion proof.
    pub(crate) fn new(
        families: Vec<Family<'p>>,
        arity_0: usize,
        arity: usize,
        rate: Rate,
        taus: PerRecTable<usize>,
    ) -> Result<Self, TreeError> {
        let child = RecShape::new(taus, rate).map_err(|_| TreeError::TooLarge)?;
        let fixed = FixedLayout::new(&taus);
        let kind_bits = crate::log2_ceil_usize(families.len() + 1);
        let runs = families.iter().find_map(|f| match f {
            Family::Runs(shape) => Some(shape.program().rv()),
            Family::Circuit(_) => None,
        });
        let circuits: Vec<&CircuitFamily<'_>> = (families.iter())
            .filter_map(|f| match f {
                Family::Circuit(c) => Some(c),
                Family::Runs(_) => None,
            })
            .collect();
        let leaf_kappa = circuits.iter().map(|c| c.fixed.kappa()).max().unwrap_or(0);
        let leaf_bits = crate::log2_ceil_usize(circuits.len().max(1));
        let present = [runs.is_some(), runs.is_some(), !circuits.is_empty(), true];
        let vars = DenseVars([
            runs.map_or(0, |rv| crate::log2_strict_usize(rv.entries().len()) + N_TUPLE_BITS),
            runs.map_or(0, |rv| crate::log2_ceil_usize(rv.image().len().max(1))),
            if circuits.is_empty() { 0 } else { leaf_kappa + leaf_bits },
            fixed.kappa() + kind_bits,
        ]);
        let n_dense = (vars.0.iter().zip(present))
            .filter_map(|(&n, p)| p.then_some(n))
            .max()
            .unwrap_or(0);
        let mut design = Self {
            families,
            arity_0,
            arity,
            rate,
            taus,
            child,
            fixed,
            kind_bits,
            leaf_kappa,
            leaf_bits,
            vars,
            present,
            statement: StatementLayout::new(n_dense),
            iv: [F64::ZERO; 4],
        };
        design.iv = design.seed();
        Ok(design)
    }

    /// The transcript's seed: everything that fixes the circuits.
    ///
    /// Every kind shares it.
    /// The kind is the statement's first word, and the statement's hash is the transcript's first block.
    fn seed(&self) -> [F64; 4] {
        let mut h = Hasher::new();
        h.update(DOMAIN);
        let word = |h: &mut Hasher, x: usize| {
            h.update(&(x as u64).to_le_bytes());
        };
        word(&mut h, self.families.len());
        for family in &self.families {
            match family {
                Family::Runs(shape) => {
                    h.update(b"runs....");
                    h.update(shape.program().digest());
                    shape.taus().values().for_each(|&t| word(&mut h, t));
                    h.update(&[shape.rate().log_inv_rate()]);
                }
                Family::Circuit(c) => {
                    h.update(b"circuit.");
                    for w in c.leaf.iv {
                        h.update(&w.0.to_le_bytes());
                    }
                    word(&mut h, c.leaf.circuit.statement_len);
                    for t in c.leaf.circuit.heights().into_values() {
                        word(&mut h, t);
                    }
                    h.update(&[c.leaf.rate.log_inv_rate()]);
                }
            }
        }
        let sizes = [self.arity_0, self.arity, self.statement.len()]
            .into_iter()
            .chain(self.taus.into_values());
        for x in sizes {
            word(&mut h, x);
        }
        h.update(&[self.rate.log_inv_rate()]);
        fiat_shamir::digest_words(&h.finalize())
    }

    /// Whether a proof of this kind carries a claim on the polynomial: a first-level node on those its leaves fix, a node on every one the tree has.
    pub(crate) fn active(&self, kind: Kind, poly: DensePoly) -> bool {
        self.present[poly as usize]
            && match kind {
                Kind::Node => true,
                Kind::First(i) => match self.families[i] {
                    Family::Runs(_) => matches!(poly, DensePoly::Bytecode | DensePoly::Image),
                    Family::Circuit(_) => poly == DensePoly::Leaf,
                },
            }
    }

    /// Every kind, by code.
    pub(crate) fn kinds(&self) -> Vec<Kind> {
        (0..self.families.len() + 1).map(Kind::of_code).collect()
    }

    /// The leaf circuits' families, by slot.
    fn circuits(&self) -> impl Iterator<Item = &CircuitFamily<'p>> {
        self.families.iter().filter_map(|f| match f {
            Family::Circuit(c) => Some(c),
            Family::Runs(_) => None,
        })
    }

    /// The nodes' fixed polynomial of the kinds' circuits' fixed columns, by code.
    pub(crate) fn node_polynomial(&self, columns: &[&FixedColumns]) -> Vec<F64> {
        let stacks = columns.iter().map(|&c| (&self.fixed, c));
        side_by_side(stacks, self.fixed.kappa(), self.kind_bits)
    }

    /// The leaves' fixed polynomial of the leaf circuits' fixed columns, by slot.
    pub(crate) fn leaf_polynomial(&self, columns: &[&FixedColumns]) -> Vec<F64> {
        let stacks = (self.circuits().zip(columns)).map(|(f, &c)| (&f.fixed, c));
        side_by_side(stacks, self.leaf_kappa, self.leaf_bits)
    }

    /// The dense polynomials, of the kinds' circuits' fixed columns by code: a polynomial the tree lacks is the zero table of no variables.
    pub(crate) fn tables(&self, columns: &[FixedColumns]) -> DenseTables {
        let none = || vec![F64::ZERO];
        let runs = self.families.iter().find_map(|f| match f {
            Family::Runs(shape) => Some(shape.program().rv()),
            Family::Circuit(_) => None,
        });
        let (bytecode, image) = runs.map_or_else(
            || (none(), none()),
            |rv| {
                let mut image: Vec<F64> = rv.image().iter().map(|&w| F64(w)).collect();
                image.resize(1 << self.vars.0[DensePoly::Image as usize], F64::ZERO);
                (Lookup::Bytecode.table(rv), image)
            },
        );
        let leaf = if self.present[DensePoly::Leaf as usize] {
            let leaves: Vec<&FixedColumns> = self.circuits().map(|f| f.leaf.columns).collect();
            self.leaf_polynomial(&leaves)
        } else {
            none()
        };
        let columns: Vec<&FixedColumns> = columns.iter().collect();
        DenseTables([bytecode, image, leaf, self.node_polynomial(&columns)])
    }

    /// The first level's rows over RISC-V proofs, verifying its leaves.
    pub(crate) fn first_runs(
        &self,
        kind: Kind,
        leaf: &ProofShape<'_>,
        inputs: &NodeInputs<'_, LeafWitness>,
    ) -> NodeRows {
        let mut b = Builder::new();
        let mut claims = NodeClaims::default();
        let mut outputs = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let item = inputs.item(i);
            let output = item.map_or([0; 4], |l| l.output).map(|o| b.free_k(o));
            let source = item.map_or(ProofSource::Shape, |l| ProofSource::Proof(&l.raw));
            let core = b.scope(format!("leaf {i}"), |b| leaf.verify_core(b, output, source));
            claims.bind_state(&mut b, core.state);
            b.scope(format!("leaf {i} program"), |b| {
                self.program_claims(b, &core.claims.program, inputs, &mut claims);
            });
            let fresh = FlockId::ALL.into_iter().zip(&core.claims.circuits);
            claims.matrices.extend(fresh.map(|(f, c)| MatrixClaim::fresh(f, c)));
            outputs.push(output);
        }
        let digest = Level::Runs.digest_rows(&mut b, &outputs);
        NodeRows {
            b,
            kind,
            digest,
            claims,
        }
    }

    /// The first level's rows over proofs of a recursion circuit, verifying its leaves at the circuit's own heights, rate and seed.
    ///
    /// Each leaf's statement is free wires, which its verifier's rows hash into its transcript's seed; the digest is over those hashes.
    pub(crate) fn first_circuit(
        &self,
        kind: Kind,
        family: &CircuitFamily<'_>,
        inputs: &NodeInputs<'_, CircuitWitness<'_>>,
    ) -> NodeRows {
        let leaf = &family.leaf;
        let mut b = Builder::new();
        let iv = b.d_const(leaf.iv.map(|w| w.0));
        let zeros = matches!(inputs, NodeInputs::Shape).then(|| FixedColumns::zeros(&leaf.circuit.heights()));
        let zero = b.k_const(0);
        let above = Bits {
            value: family.slot << (self.leaf_kappa - family.fixed.kappa()),
            len: self.leaf_kappa - family.fixed.kappa() + self.leaf_bits,
        };
        let mut claims = NodeClaims::default();
        let mut seeds = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let item = inputs.item(i);
            let limbs: Vec<[Kw; 4]> = (0..leaf.circuit.statement_len)
                .map(|z| {
                    let [l0, l1, l2, _] = item.map_or([0; 4], |l| l.statement[z]);
                    [b.free_k(l0), b.free_k(l1), b.free_k(l2), zero]
                })
                .collect();
            let columns = item.map_or_else(|| zeros.as_ref().expect("zero columns from a shape"), |l| l.columns);
            let source = item.map_or(ProofSource::Shape, |l| ProofSource::Proof(&l.raw));
            let rows = b.scope(format!("leaf {i}"), |b| {
                family.shape.verify(b, iv, &limbs, columns, source)
            });
            claims.bind_state(&mut b, rows.state);
            claims.bound.extend(rows.hints.iter().map(|h| h.value));
            claims
                .dense
                .push(fixed_claim(DensePoly::Leaf, &family.fixed, &rows.hints, above, &[]));
            claims.matrices.push(MatrixClaim::fresh(HashFlock::FLOCK, &rows.matrix));
            seeds.push(b.d_to_k(rows.seed));
        }
        let digest = Level::Circuit(leaf.iv.map(|w| w.0)).digest_rows(&mut b, &seeds);
        NodeRows {
            b,
            kind,
            digest,
            claims,
        }
    }

    /// The node's rows, verifying its children, of any kind.
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
            // The kind's bits select the child's circuit's stack of the nodes' fixed polynomial.
            let bits = b.scope(format!("child {i} kind"), |b| self.kind_bits(b, statement.kind()));
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
            claims.dense.push(fixed_claim(
                DensePoly::Fixed,
                &self.fixed,
                &rows.hints,
                Bits::NONE,
                &bits,
            ));
            claims.matrices.push(MatrixClaim::fresh(HashFlock::FLOCK, &rows.matrix));
            self.carried(&mut b, &statement, &bits, &mut claims);
            let digest = statement.digest_wire(&mut b);
            digests.push(b.d_to_k(digest));
        }
        let digest = Level::Node.digest_rows(&mut b, &digests);
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
            Kind::First(i) => match &self.families[i] {
                Family::Runs(leaf) => self.first_runs(kind, leaf, &NodeInputs::Shape),
                Family::Circuit(family) => self.first_circuit(kind, family, &NodeInputs::Shape),
            },
            Kind::Node => self.node(&NodeInputs::Shape),
        };
        rows.reduce(self, ProofSource::Shape)
    }

    /// A child's kind word's bits, lowest first, held Boolean and to name a kind of the tree.
    ///
    /// One bit is the word itself; more are free wires the word is held to be the sum of, `sum_j bit_j X^j`.
    fn kind_bits(&self, b: &mut Builder, kind: Ew) -> Vec<Ew> {
        let n = self.kind_bits;
        let bits = if n == 1 {
            vec![kind]
        } else {
            let code = b.e(kind).c0;
            (0..n).map(|j| b.free_e(F192::new(code >> j & 1, 0, 0))).collect()
        };
        for &bit in &bits {
            let square = b.square(bit);
            b.eq_e(square, bit);
        }
        if n > 1 {
            let zero = b.zero();
            let word = (bits.iter().enumerate()).fold(zero, |acc, (j, &bit)| {
                b.mul_const_add(bit, F192::new(1 << j, 0, 0), acc)
            });
            b.eq_e(word, kind);
        }
        let kinds = self.families.len() + 1;
        if kinds < 1 << n {
            // Exactly one of the `2^n` codes' indicators is one: the codes past the kinds' are refused.
            let indicators: Vec<Ew> = (0..kinds).map(|code| indicator(b, &bits, code)).collect();
            let sum = b.sum(&indicators);
            b.eq_e_const(sum, F192::ONE);
        }
        bits
    }

    /// Whether a child of the kind its bits name carries a claim on the polynomial, as a scale: none when every kind carries one.
    fn mask(&self, b: &mut Builder, bits: &[Ew], poly: DensePoly) -> Option<Ew> {
        let kinds = self.families.len() + 1;
        let codes: Vec<usize> = (0..kinds)
            .filter(|&code| self.active(Kind::of_code(code), poly))
            .collect();
        (codes.len() < kinds).then(|| {
            let indicators: Vec<Ew> = codes.into_iter().map(|code| indicator(b, bits, code)).collect();
            b.sum(&indicators)
        })
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

    /// The claims a child's statement carries, each weighed by whether a child of its kind carries it.
    ///
    /// A claim a kind does not carry is zero in its statement, and its scale is zero.
    fn carried(&self, b: &mut Builder, statement: &TreeStatement<Ew>, bits: &[Ew], claims: &mut NodeClaims<Ew>) {
        let point = statement.dense_point();
        for poly in DensePoly::ALL.into_iter().filter(|&p| self.present[p as usize]) {
            let n = self.vars.0[poly as usize];
            let scale = self.mask(b, bits, poly);
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

/// The indicator of a code among the codes of these bits: one exactly when the bits are the code's.
fn indicator(b: &mut Builder, bits: &[Ew], code: usize) -> Ew {
    let one = b.one();
    (bits.iter().enumerate()).fold(one, |acc, (j, &bit)| {
        let factor = if code >> j & 1 == 1 { bit } else { b.add(one, bit) };
        b.mul(acc, factor)
    })
}

/// A circuit's hinted fixed-column evaluations as claims on a fixed polynomial whose stack of that circuit has this layout.
///
/// Column `c` at the bus point's prefix `p` is the polynomial at `(p, block_c, above, top)`: `above` the public bits past the circuit's stack, `top` the kind's bits.
fn fixed_claim(poly: DensePoly, layout: &FixedLayout, hints: &[FixedHint], above: Bits, top: &[Ew]) -> DenseClaim<Ew> {
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
            let len = layout.kappa() - n_low;
            DenseTerm {
                n_low,
                bits: Bits {
                    value: layout.block(h.column) | above.value << len,
                    len: len + above.len,
                },
                top: top.to_vec(),
                scale: None,
                value: h.value,
            }
        })
        .collect();
    DenseClaim { poly, low, terms }
}

impl Reduced<Ew> {
    /// The statement of a circuit of this kind and digest whose reduction left these claims.
    ///
    /// A polynomial left unreduced has a zero value, and the point is zero past the reduction's rounds.
    fn statement(&self, b: &mut Builder, layout: StatementLayout, kind: Kind, digest: Dw) -> TreeStatement<Ew> {
        let zero = b.zero();
        let mut s = TreeStatement::filled(layout, zero);
        s.section_mut(Section::Kind)[0] = b.e_const(kind.word());
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
        let mut t = Transcript::from_label(b, reduce::LABEL, source);
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
