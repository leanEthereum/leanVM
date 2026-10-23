/-
  LeanVM.Protocol.FixedColumns

  Public index and bytecode columns and their native multilinear evaluations.
-/

module

public import LeanVM.Protocol.Field
public import LeanVM.Protocol.ToCompPoly.BitProductTable
public import LeanVM.Arithmetization.Bytecode

/-!
# Fixed public columns

The two columns both parties know, at leanVM revision
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`.

* **The index column** holds the address `g ^ i` at cell `i`. It is the geometric table of
  `ToCompPoly/BitProductTable.lean` at the generator, so its extension is a product of one
  factor per coordinate, `∏_k (1 + ζ_k (1 + g^(2^k)))` in characteristic two
  (specification §6.5, `doc/leanvm/body/06-bus-interactions.tex:98-103`).
* **The bytecode column** is the program as one table on `logSize + 4` variables: the
  instruction index in the low `logSize` coordinates, the slot in the high four, low bit first.
  The layout follows specification §8.1
  (`doc/leanvm/body/08-end-to-end-protocol.tex:4-25`) and
  `crates/leanvm_core/src/leaf.rs:543-577`; the Rust verifier evaluates the same table at
  `(zeta, alpha)` (`crates/verifier/src/bus.rs:140-146`, with `bytecode.rs:100-134`; the
  prover-side `bytecode_claim`, `leaf.rs:627-637` at `a386121f`, is removed at `127510d1`), and so
  does the second verifier (`python-verifier/verifier.py:549-558`). The content of a slot is
  `encodeSlots`, the one definition of the encoding, zero slots included.

Every index of the program is encoded, the last one too: the column knows no sentinel. These
are equalities about the columns' extensions; no theorem here proves that the Rust computes
them.

This module names the program, so it imports the bytecode encoding. It belongs with the leanISA
instance and the compiled verifier; no phase of the oracle protocol imports it.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open CompPoly CMlPolynomialEval

@[expose] public section

/-! ## The index column -/

/-- The fixed address column with entry `g ^ i` at Boolean index `i`. -/
def idxColumn (κ : ℕ) : Column κ := ⟨powersTable g κ⟩

/-- The native index-column evaluator over the challenge field. -/
def idxColumnEval {κ : ℕ} (z : Vector E κ) : E :=
  ∏ j : Fin κ, ((1 - z[j]) + z[j] * algebraMap K E (g ^ (2 ^ j.val)))

/-- The native evaluator is the column's extension. -/
theorem idxColumn_eval {κ : ℕ} (z : Vector E κ) :
    eval₂Mle (idxColumn κ).values (algebraMap K E) z = idxColumnEval z :=
  eval₂Mle_powersTable (algebraMap K E) g κ z

/-- The evaluator as the specification writes it in characteristic two (§6.5):
`∏_k (1 + ζ_k (1 + g^(2^k)))`. -/
theorem idxColumnEval_eq {κ : ℕ} (z : Vector E κ) :
    idxColumnEval z = ∏ k : Fin κ, (1 + z[k] * (1 + algebraMap K E (g ^ (2 ^ k.val)))) := by
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [CharTwo.sub_eq_add]
  ring

/-! ## The bytecode column -/

/-- The complete sixteen-slot public bytecode column, with instruction bits first. -/
def bytecodeColumn (prog : Program) : Column (prog.logSize + 4) :=
  ⟨Vector.ofFn fun i ↦
    let p := (cubeSplit prog.logSize 4).symm i
    (encodeSlots (prog.code p.1))[p.2]⟩

/-- The cell of instruction `i` and slot `s` holds that slot, spare slots included. -/
private theorem bytecodeColumn_slot (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : Fin 16) :
    (bytecodeColumn prog).values[cubeIndex (m := 4) i s] = (encodeSlots (prog.code i))[s] := by
  simp [bytecodeColumn, ← cubeSplit_apply]

/-- **The bytecode column names the program**: two programs of one size with the same column
are the same program. -/
theorem bytecodeColumn_injective {prog prog' : Program} (h : prog.logSize = prog'.logSize)
    (hv : (bytecodeColumn prog).values.toList = (bytecodeColumn prog').values.toList) :
    prog = prog' := by
  obtain ⟨n, hn, code⟩ := prog
  obtain ⟨n', hn', code'⟩ := prog'
  simp only at h
  subst h
  have hv' := Vector.toList_inj.mp hv
  have hcode : code = code' := by
    funext i
    apply entry_injective
    refine Vector.ext fun j hj ↦ ?_
    have h1 := congrArg (fun v ↦ v[cubeIndex (m := 4) i ⟨j + 3, by omega⟩]) hv'
    simp only at h1
    rw [bytecodeColumn_slot, bytecodeColumn_slot] at h1
    simp only [Fin.getElem_fin] at h1
    rw [encodeSlots_getElem _ _ (show j + 3 < 16 by omega),
      encodeSlots_getElem _ _ (show j + 3 < 16 by omega)] at h1
    simpa [show 3 ≤ j + 3 ∧ j + 3 < 11 by omega] using h1
  subst hcode
  rfl

/-- The bit order, stated at the extension: at the cube point whose low coordinates are the
bits of the instruction index and whose high four are the bits of the slot, the column holds
that slot of that instruction (§8.1: the opcode of instruction `z` is `P(z, 1, 1, 0, 0)`). -/
theorem bytecodeColumn_answer_boolVec (prog : Program) (i : Fin (2 ^ prog.logSize))
    (s : Fin 16) :
    eval₂Mle (bytecodeColumn prog).values (algebraMap K E)
        ((boolVec i : Vector E prog.logSize) ++ (boolVec (m := 4) s : Vector E 4)) =
      algebraMap K E ((encodeSlots (prog.code i))[s]) := by
  rw [eval₂Mle, evalMle_append_boolVec, evalMle_boolVec, slice_getElem]
  simpa only [CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map] using
    congrArg (algebraMap K E) (bytecodeColumn_slot prog i s)

/-- Native bytecode evaluation from the public instruction and slot tables. -/
def bytecodeColumnEval (prog : Program) (z : Vector E prog.logSize) (w : Vector E 4) : E :=
  ∑ s : Fin 16, (lagrangeBasis w)[s] *
    ∑ i : Fin (2 ^ prog.logSize),
      algebraMap K E ((encodeSlots (prog.code i))[s]) * (lagrangeBasis z)[i]

/-- The native evaluator is the column's extension, at every point of `E`. -/
theorem bytecodeColumn_eval (prog : Program) (z : Vector E prog.logSize) (w : Vector E 4) :
    eval₂Mle (bytecodeColumn prog).values (algebraMap K E) (z ++ w) =
      bytecodeColumnEval prog z w := by
  rw [eval₂Mle, evalMle_split]
  unfold bytecodeColumnEval
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [evalMle_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simpa only [slice, Vector.getElem_ofFn, CMlPolynomialEval.map, Vector.getElem_map,
    Fin.getElem_fin] using congrArg (algebraMap K E) (bytecodeColumn_slot prog i s)

end
end LeanVM.Protocol
