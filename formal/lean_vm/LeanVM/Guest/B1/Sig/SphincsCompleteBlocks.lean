/-
  LeanVM.Guest.B1.Sig.SphincsCompleteBlocks

  The completeness of `verify_sig_lean_sphincs`'s FORS block and of a layer of its hypertree
  (`lean_ethereum.py:4004-4139, 4222-4227`), as the statements its assembly
  consumes; the byte table's pointers.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBridgeCells
public import LeanVM.Guest.B1.Sig.SphincsGlue
public import LeanVM.Guest.B1.Sig.CompleteKit
public import LeanVM.Guest.B1.Sig.SphincsFieldsComplete
public import LeanVM.Guest.B1.Sig.SphincsSoundFors

/-!
# The blocks' completeness, as the assembly consumes it

`G` is `lean_ethereum.py`. `verify_sig_lean_sphincs`'s body is the digest block, FORS and three
layers, with addresses between them (`SphincsT`). Its completeness (`SphincsComplete`) is assembled
from the completeness of each block (`Completes`: a valuation extending the given one on the
block's fresh values, under which the block holds): the digest block's (`sDigestBlock_complete`)
and `sp_from_bytes`'s (`sFromMarks_complete`), and the two stated here:

* `ForsBlockCompletes` (`sForsB`, `G:4222-4227`): at the bottom key's `A0` and `A1`, the leaves `s c`
  (their bits, and their shifts with the trees' places, `fIdx`), any secrets and siblings, the FORS
  key is `T_k` of the roots
  (`forsRootCell`);
* `HtLayerCompletes` (`sHtLayer`, `G:4132-4139`): a layer whose `sp_wots` call holds of the
  encoding (`encDigestCell`) and a leaf `lv` reaches `pFold` of `pNodeE` from `lv`, along any
  siblings;
* `SphincsBlocksComplete`: the two.

The hints are free: the assembly picks them as `Guest/Hints.lean`'s `sphincsHints` pushes them.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The byte table's pointers -/

/-- The pointer a load reads through, unless it is the claim's `n0`. -/
def stmtPtrs : Stmt → List Nat
  | .atom (.load _ p _) => if p.idx = 0 then [] else [p.idx]
  | _ => []

/-- The pointers a block's loads read through, the claim's `n0` aside. -/
def loadPtrs (ss : List Stmt) : List Nat := ss.flatMap stmtPtrs

theorem loadPtrs_append (xs ys : List Stmt) : loadPtrs (xs ++ ys) = loadPtrs xs ++ loadPtrs ys :=
  List.flatMap_append

/-- Every pointer a block reads through is the byte table's. -/
def TablePtrs (bb : E) (σ : Val) (ss : List Stmt) : Prop := ∀ q ∈ loadPtrs ss, BytePtr bb (σ (.n q))

theorem TablePtrs.congr {bb : E} {σ σ' : Val} {ss : List Stmt} {b : Nat} (h : TablePtrs bb σ ss)
    (hb : ∀ q ∈ loadPtrs ss, q < b) (ha : ∀ k < b, σ' (.n k) = σ (.n k)) : TablePtrs bb σ' ss :=
  fun q hq => by rw [ha q (hb q hq)]; exact h q hq

theorem TablePtrs.nil_of {bb : E} {σ : Val} {ss : List Stmt} (h : loadPtrs ss = []) :
    TablePtrs bb σ ss := fun q hq => by rw [h] at hq; simp at hq

theorem TablePtrs.append {bb : E} {σ : Val} {xs ys : List Stmt} (h1 : TablePtrs bb σ xs)
    (h2 : TablePtrs bb σ ys) : TablePtrs bb σ (xs ++ ys) := fun q hq => by
  rw [loadPtrs_append, List.mem_append] at hq
  rcases hq with hq | hq
  · exact h1 q hq
  · exact h2 q hq

/-! ## Positions below the digest block's end -/

theorem sLeafBit_lt {b : Nat} (hb : b < 26) : ∃ k < 1372, sLeafBit b = .n k :=
  ⟨28 + leafPos b, by have := leafPos_lt hb; omega, sLeafBit_eq hb⟩

theorem sLVal_below (i : Nat) : ∃ k < 1372, sLVal i = .n k := by
  unfold sLVal; split_ifs <;> exact ⟨_, by omega, rfl⟩

theorem sOff_lt {l z : Nat} (hl : l < 3) (hz : z < sHeightOf l) : sOffOf l + z < 26 := by
  simp only [sOffOf, sLeafOff, sHeightOf, sLeafLen] at hz ⊢
  split_ifs at hz <;> omega

/-! ## Hinted runs -/

/-- **A hinted run** of fresh values completes to any values. -/
theorem hintRun_complete (σ : Val) (s : String) (b n : Nat) (f : Nat → E) :
    Completes C rd b (b + n) [hintW s (runV b n)] σ (fun σ' => ∀ j < n, σ' (.n (b + j)) = f j) :=
  ⟨updRun σ b n f, updRun_ext σ b n f, fun _ hj => updRun_at σ b n f hj,
    fun _ _ hn => ⟨trivial, hn⟩⟩

/-! ## The blocks -/

/-- **FORS completes** (`sForsB`, from `n1382` to `n5249`): at the bottom key's `A0` (`tree`) and
`A1` (`kp`), the leaves `s c` read off the digest's bits and `vals` (their shifts with the trees'
places, the FIPS 205 tree indices `fIdx c z (s c)`), any secrets and siblings, the FORS key is `T_k` of `P`, `A0`, `FORS_ROOTS` and the roots. -/
def ForsBlockCompletes : Prop :=
  ∀ (C : CallRel) (rd : Reader) (σ : Val) (tree kp : Nat) (s : Nat → Nat) (secret : Nat → E)
    (sib : Nat → Nat → E),
    PadOK σ sPad → σ sA0B = adrsCell0 0 tree →
    σ sKeyB = adrsCell1 0 kp 0 0 → (∀ c < 24, s c < 2 ^ 10) →
    (∀ c < 24, ∀ z < 10, σ (sForsBit (10 * c + z)) = if (s c).testBit z then 1 else 0) →
    (∀ c < 24, ∀ z < 10, σ (sVals (10 * c + z)) = eOfNat (fIdx c z (s c))) →
      Completes C rd 1382 5249 sForsB.1 σ (fun σ' => σ' sForsPk =
        (hcell ([σ sPP, adrsCell0 0 tree, adrsCell1 4 kp 0 0] ++
          List.ofFn fun c : Sphincs.ForsTreeIndex =>
            forsRootCell (σ sPP) (adrsCell0 0 tree) kp c.val (s c.val) (secret c.val)
              (sib c.val))).1)

/-- **A layer completes after its counter** (`sHtLayer` of layer `l` from `b`): its key's `A0`
and `A1`, the value it signs and the counter's cell (`N`'s bytes reversed), the call relation
holding of `sp_wots` on the encoding's digest (`encDigestCell`) returning `lv`, the leaf `e` read
off the digest's bits and shifts, and any siblings, the layer's root is `pFold` of `pNodeE` from
`lv`. -/
def HtLayerCompletes : Prop :=
  ∀ (C : CallRel) (rd : Reader) (σ : Val) (l : Nat) (a0 a1 signed ctr : V) (b : Nat) (lv : E)
    (e : Nat) (sib : Nat → E),
    l < 3 → 1372 ≤ b → NBv b a0 → NBv b a1 → NBv b signed → NBv b ctr → PadOK σ sPad →
    (∃ N < 2 ^ 32, σ ctr = eOfNat (beWordAt 0 N)) →
    C "sp_wots" [σ sPP, σ a0, σ a1,
      encDigestCell (σ sPP) (σ a0) (σ a1 + lit (7 * 2 ^ 24)) (σ signed) (σ ctr)] [lv] →
    e < 2 ^ sHeightOf l →
    (∀ z < sHeightOf l, σ (sLeafBit (sOffOf l + z)) = if e.testBit z then 1 else 0) →
    (∀ z < sHeightOf l, σ (sLVal (sOffOf l + z)) = eOfNat (e >>> z)) →
      Completes C rd b (sHtLayer sPad sPP a0 a1 signed ctr sLeafBit sLVal (sOffOf l) (sHeightOf l) b).2.1
        (sHtLayer sPad sPP a0 a1 signed ctr sLeafBit sLVal (sOffOf l) (sHeightOf l) b).1 σ
        (fun σ' => σ' (sHtLayer sPad sPP a0 a1 signed ctr sLeafBit sLVal (sOffOf l) (sHeightOf l) b).2.2 =
          pFold (pNodeE (σ sPP) (σ a0) e sib) (sHeightOf l) lv)

/-- **The blocks of `verify_sig_lean_sphincs` complete.** -/
structure SphincsBlocksComplete : Prop where
  fors : ForsBlockCompletes
  layer : HtLayerCompletes

end
end LeanVM.Guest.B1.Sig
