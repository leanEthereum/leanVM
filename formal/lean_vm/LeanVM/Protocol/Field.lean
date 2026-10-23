/-
  LeanVM.Protocol.Field

  The instances that make leanVM's fields usable by ArkLib's oracle-reduction framework: uniform
  sampling of challenges in `E`, the inner-product oracle on a committed column, and the trivial
  interface on scalar messages.
-/

module

public import LeanVM.Parameters.Field
public import LeanVM.Protocol.ToArkLib.InnerProduct
public import CompPoly.Multilinear.Basic
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# Fields for the proof system

leanVM's columns take values in `K` and its challenges in `E`, the cubic extension of `K`
(`LeanVM.Parameters.Field`). Three things are supplied.

* `SampleableType E`: the uniform sampler ArkLib requires of every challenge type. `E` is
  sampled as three independent limbs through `Ext.ofVector`; the `K` sampler it is built from
  reads a uniform `Fin (2^64)` as a bit pattern through `BitVec.ofFin` and `BF64.ofBitVec`.
  Neither enumerates its field: `Fintype K` is proof-only, and a sampler built from it would
  enumerate `2^64` elements at initialization. The shape follows ArkLib's own
  `KoalaBear.Ext6.sampleableType`.
* `card_E`: `Fintype.card E = 2^192`, the one cardinality fact every error bound rewrites with.
* `innerProductOracle`: the interface of the one committed oracle, the stack, on `Column n`,
  the value table of a `K`-multilinear on `n` variables. A query is a weight `W : Weight E n`
  (specification Definition 3.13, `def:ipcs`, `doc/leanvm/body/03-proving-primitives.tex:112-115`
  at `127510d14c98ade4e8a97646c44fa7f1ff5e752d`): a table over the cube with an evaluator of its
  extension the verifier can run. The answer is `⟨W, q⟩ = Σ_x W(x)·q(x)` in `E`. An evaluation
  `q̃(p)` at a point `p ∈ E^n` is the answer to the equality kernel `eqWeight p`
  (`answer_eqWeight`).
The scalars and coefficient lists a phase sends need no interface of their own: a one-message
schedule (`LeanVM.Protocol.ToArkLib.Schedule`) reads its message whole.

## Wrong readings excluded

* The oracle answers a weighted sum over the cube, `Σ_x W(x)·q(x)`, not the value `q(x)` at a
  position: a column is a structure, not `Vector K (2^n)`, so that instance search cannot also
  find ArkLib's position-query interface on `Vector` and read the column as a codeword.
* On a cube point `p`, `eqWeight p` is an indicator and the answer is the cell there; off the
  cube it is the multilinear extension (`CMlPolynomialEval.eval_mle_eq_eval`).
* The `K` sampler is only the building block of the `E` sampler; no challenge is drawn in `K`.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly OracleComp

@[expose] public section

/-! ## Columns -/

/-- A column of height `2^n`: the values of a `K`-multilinear on the cube, low bit first. A
structure rather than an abbreviation so that its oracle interface below does not overlap
ArkLib's position-query interface on `Vector`. -/
structure Column (n : ℕ) where
  /-- The value table, CompPoly's hypercube representation. -/
  values : CMlPolynomialEval K n

/-! ## Sampling -/

/-- `K` as the `2^64` bit patterns, the `BitVec` view of `Fin (2^64)`. -/
def finEquivK : Fin (2 ^ 64) ≃ K where
  toFun := fun i ↦ BF64.ofBitVec (BitVec.ofFin i)
  invFun := fun x ↦ x.toBitVec.toFin
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uniform sampling of `K`: a uniform `Fin (2^64)` read as a bit pattern. It is only the
building block of the `E` sampler; no challenge of the protocol is drawn in `K`. -/
instance instSampleableTypeK : SampleableType K :=
  haveI : NeZero (2 ^ 64) := ⟨by norm_num⟩
  SampleableType.ofEquiv finEquivK

/-- `E` as its three limbs, CompPoly's carrier view. -/
def limbsEquiv : Vector K 3 ≃ E where
  toFun := fun v ↦ CompPoly.Extension.Ext.ofVector (P := BF64.ext3Params) v
  invFun := fun x ↦ CompPoly.Extension.Ext.coeffs (P := BF64.ext3Params) x
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uniform sampling of `E`: three independent uniform limbs. -/
instance instSampleableTypeE : SampleableType E := SampleableType.ofEquiv limbsEquiv

/-- `|E| = 2^192`: the size of the challenge space in every error bound. -/
theorem card_E : Fintype.card E = 2 ^ 192 := BF64.card_ext3

/-! ## The inner-product oracle -/

/-- The stack as an oracle: a query is a weight `W` on the cube, the answer is the inner
product `⟨W, q⟩ = Σ_x W(x)·q(x)` in `E` (Definition 3.13). -/
instance innerProductOracle (n : ℕ) : OracleInterface (Column n) where
  Query := Weight E n
  toOC :=
    { spec := Weight E n →ₒ E
      impl := fun W ↦ do return W.pair (algebraMap K E) (← read).values }

/-- The oracle answers the inner product of the weight with the column. -/
theorem innerProductOracle_answer {n : ℕ} (q : Column n) (W : Weight E n) :
    OracleInterface.answer q W = W.pair (algebraMap K E) q.values := rfl

/-- The answer to the equality kernel at `p` is the column's extension at `p`. -/
theorem answer_eqWeight {n : ℕ} (q : Column n) (p : Vector E n) :
    OracleInterface.answer q (eqWeight p) =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) p :=
  Weight.pair_eqWeight (algebraMap K E) p q.values

end
end LeanVM.Protocol
