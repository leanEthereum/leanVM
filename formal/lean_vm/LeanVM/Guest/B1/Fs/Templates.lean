/-
  LeanVM.Guest.B1.Fs.Templates

  The expansions of the guest's inline Fiat-Shamir helpers as statement templates, what they ask
  of a valuation, and what their cells are.
-/

module

public import LeanVM.Guest.B1.Common.Sponge

/-!
# The inline Fiat-Shamir helpers (TRIAGE G #5-15)

The helpers of the guest's sponge (`lean_ethereum.py` at leanVM `40f877dc`, G below,
G:588-710) are `@inline`: their atoms sit in their callers' core IR, numbered by the caller.
Their expansions are uniform (`Expand.lean`, the compiler's `builtins.rs`), so each is a template
over its operands and its first value `b`; a caller's body is checked equal to its composition of
templates by kernel evaluation (`stmtsEqb_sound`).

* `fsPackT x b t` (`fs_pack`, G:616-624): `x`'s limbs hinted into `b .. b + 2`, then the two rate
  cells `b + 6 = x + y²·x₂` and `b + 8 = x₂ + y·t`. `fsPackT_cells`: once the first cell is
  canonical (a `KECCAK` reading it), they are `Keccak.scalarCells x t` (`fsPack_cells`).
* `fsNextT cur off b` (`fs_next`, G:695-702): the word at `cur·g^off` into `b`, then
  `fsPackT (.n b) (b + 1) 1`: its cells `b + 7`, `b + 9`.
* `challengeT s0 s1 b` (`challenge_from_state`, G:593-602): `b + 6` is the challenge of a state
  whose cells `0`, `1` are `s0`, `s1` (`challengeT_value`, `challengeOf_cells`).
* `keccakA` (`fs_perm`, `fs_perm4`, `fs_perm_pending`, `fs_absorb_nonce`'s permutation, G:627-670):
  one `KECCAK` atom in the even layouts; `keccakA_perm`: its outputs are `permOf` of its inputs.

The `…Vals` functions are the honest values of each template, from which a caller builds the
valuation of its completeness direction (`…Ok_of_vals`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## `fs_pack` -/

/-- `fs_pack(rate, k, x, tag)`'s atoms from the value `b`: the hinted limbs `b .. b + 2`, the tag
`b + 3`, `y²` at `b + 4`, `y²·x₂` at `b + 5`, the cells `b + 6`, `b + 8` (`y·tag` at `b + 7`). -/
def fsPackT (x : V) (b t : ℕ) : List Stmt :=
  [.atom (.hint (.limbs x [.n b, .n (b + 1), .n (b + 2)])),
    .atom (.const (.n (b + 3)) (word t 0 0)),
    .atom (.assertInK (.n (b + 2)) (.n (b + 3))),
    .atom (.const (.n (b + 4)) (word 0 0 1)),
    .atom (.mul (.n (b + 5)) (.n (b + 4)) (.n (b + 2))),
    .atom (.add (.n (b + 6)) x (.n (b + 5))),
    .atom (.const (.n (b + 7)) (word 0 t 0)),
    .atom (.add (.n (b + 8)) (.n (b + 2)) (.n (b + 7)))]

/-- What `fsPackT` asks of a valuation. -/
def FsPackOk (σ : Val) (x : V) (b t : ℕ) : Prop :=
  σ (.n (b + 3)) = word t 0 0 ∧ IsInK (σ (.n (b + 2))) ∧ IsInK (σ (.n (b + 3))) ∧
    σ (.n (b + 4)) = word 0 0 1 ∧ σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n (b + 2)) ∧
    σ (.n (b + 6)) = σ x + σ (.n (b + 5)) ∧ σ (.n (b + 7)) = word 0 t 0 ∧
    σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7))

theorem holds_fsPackT (x : V) (b t : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (fsPackT x b t) next kret ↔ FsPackOk σ x b t ∧ next := by
  simp only [fsPackT, FsPackOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_assoc]

/-- **`fs_pack`'s cells** (G:616-624): once its first cell is canonical, the two cells are the
scalar's rate cells `Keccak.scalarCells x t`. -/
theorem fsPackT_cells {x : V} {b t : ℕ} (h : FsPackOk σ x b t)
    (hcan : IsCanonical128 (σ (.n (b + 6)))) :
    (σ (.n (b + 6)), σ (.n (b + 8))) = Keccak.scalarCells (σ x) t := by
  obtain ⟨-, h2, -, h4, h5, h6, h7, h8⟩ := h
  have e6 : σ (.n (b + 6)) = σ x + y * y * σ (.n (b + 2)) := by rw [h6, h5, h4, word_yy]
  have e8 : σ (.n (b + 8)) = σ (.n (b + 2)) + y * eOfNat t := by rw [h8, h7, word_y_mul]
  rw [e6] at hcan ⊢
  rw [e8]
  exact (Keccak.fsPack_cells (σ x) (σ (.n (b + 2))) t h2 hcan).2

/-- The honest values of `fsPackT` on the word `x`: its three limbs, then the constants and
cells. -/
def fsPackVals (x : E) (t : ℕ) : ℕ → E
  | 0 => ofK (x.limb 0)
  | 1 => ofK (x.limb 1)
  | 2 => ofK (x.limb 2)
  | 3 => word t 0 0
  | 4 => word 0 0 1
  | 5 => word 0 0 1 * ofK (x.limb 2)
  | 6 => x + word 0 0 1 * ofK (x.limb 2)
  | 7 => word 0 t 0
  | _ => ofK (x.limb 2) + word 0 t 0

theorem fsPackOk_of_vals {x : V} {b t : ℕ} (h : ∀ i < 9, σ (.n (b + i)) = fsPackVals (σ x) t i) :
    FsPackOk σ x b t := by
  have e : ∀ i, i < 9 → σ (.n (b + i)) = fsPackVals (σ x) t i := h
  refine ⟨e 3 (by omega), ?_, ?_, e 4 (by omega), ?_, ?_, e 7 (by omega), ?_⟩
  · rw [e 2 (by omega)]; exact ofK_isInK _
  · rw [e 3 (by omega)]; show IsInK (word t 0 0); rw [word_eOfNat]; exact eOfNat_isInK _
  · rw [e 5 (by omega), e 4 (by omega), e 2 (by omega)]; rfl
  · rw [e 6 (by omega), e 5 (by omega)]; rfl
  · rw [e 8 (by omega), e 2 (by omega), e 7 (by omega)]; rfl

/-- The honest cells are the scalar's rate cells. -/
theorem fsPackVals_cells (x : E) (t : ℕ) :
    (fsPackVals x t 6, fsPackVals x t 8) = Keccak.scalarCells x t := by
  have hc : IsCanonical128 (x + y * y * ofK (x.limb 2)) := by
    rw [top_pin_eq]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have := (Keccak.fsPack_cells x (ofK (x.limb 2)) t (ofK_isInK _) hc).2
  simp only [fsPackVals, word_yy, word_y_mul]
  exact this

/-- The scalar's rate cells are canonical. -/
theorem scalarCells_canonical (x : E) (t : ℕ) :
    IsCanonical128 (Keccak.scalarCells x t).1 ∧ IsCanonical128 (Keccak.scalarCells x t).2 :=
  ⟨(isCanonical128_ofLimbs_iff _ _ _).mpr rfl, (isCanonical128_ofLimbs_iff _ _ _).mpr rfl⟩

/-- The honest cells are canonical. -/
theorem fsPackVals_canonical (x : E) (t : ℕ) :
    IsCanonical128 (fsPackVals x t 6) ∧ IsCanonical128 (fsPackVals x t 8) := by
  have h := fsPackVals_cells x t
  simp only [Prod.ext_iff] at h
  rw [h.1, h.2]
  exact scalarCells_canonical x t

/-! ## `fs_next` -/

/-- `fs_next(rate, k, cursor)`'s atoms from the value `b`: the word at `cur·g^off` into `b`, then
`fs_pack` of it with the tag `DS_OBSERVE = 1`, its cells `b + 7`, `b + 9`. -/
def fsNextT (cur : V) (off b : ℕ) : List Stmt :=
  .atom (.load (.n b) cur off) :: fsPackT (.n b) (b + 1) dsObserve

theorem holds_fsNextT (cur : V) (off b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (fsNextT cur off b) next kret ↔
      (LoadHolds rd (σ cur) off (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve) ∧ next := by
  rw [fsNextT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, holds_fsPackT, and_assoc]

/-! ## `challenge_from_state` -/

/-- `challenge_from_state(state)`'s atoms from the value `b`, on the state's cells `s0`, `s1`:
the hinted low limb `b`, the derived high limb `b + 3`, the challenge `b + 6`. -/
def challengeT (s0 s1 : V) (b : ℕ) : List Stmt :=
  [.atom (.hint (.limbs s1 [.n b])),
    .atom (.add (.n (b + 1)) s1 (.n b)),
    .atom (.const (.n (b + 2)) (word 1 0 1)),
    .atom (.mul (.n (b + 3)) (.n (b + 1)) (.n (b + 2))),
    .atom (.assertInK (.n b) (.n (b + 3))),
    .atom (.const (.n (b + 4)) (word 0 0 1)),
    .atom (.mul (.n (b + 5)) (.n (b + 4)) (.n b)),
    .atom (.add (.n (b + 6)) s0 (.n (b + 5)))]

/-- What `challengeT` asks of a valuation. -/
def ChallengeOk (σ : Val) (s0 s1 : V) (b : ℕ) : Prop :=
  σ (.n (b + 1)) = σ s1 + σ (.n b) ∧ σ (.n (b + 2)) = word 1 0 1 ∧
    σ (.n (b + 3)) = σ (.n (b + 1)) * σ (.n (b + 2)) ∧ IsInK (σ (.n b)) ∧
    IsInK (σ (.n (b + 3))) ∧ σ (.n (b + 4)) = word 0 0 1 ∧
    σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n b) ∧ σ (.n (b + 6)) = σ s0 + σ (.n (b + 5))

theorem holds_challengeT (s0 s1 : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (challengeT s0 s1 b) next kret ↔ ChallengeOk σ s0 s1 b ∧ next := by
  simp only [challengeT, ChallengeOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_assoc]

/-- **`challenge_from_state`** (G:593-602): on the cells `0`, `1` of a state, the template's
challenge is `challengeOf` of the state. -/
theorem challengeT_value {s0 s1 : V} {b : ℕ} {S : KeccakState} (h : ChallengeOk σ s0 s1 b)
    (h0 : σ s0 = cellsOfState S false 0) (h1 : σ s1 = cellsOfState S false 1) :
    σ (.n (b + 6)) = challengeOf S := by
  obtain ⟨e1, e2, e3, hk, hk3, e4, e5, e6⟩ := h
  have hsplit := (split_iff (σ s1) (σ (.n b))).mp ⟨hk, by rw [← word_y_inv, ← e2, ← e1, ← e3]; exact hk3⟩
  rw [e6, e5, e4, word_yy, hsplit.2, h0, h1, Keccak.challengeOf_cells]

/-- The honest values of `challengeT` on the cell `s1` (`s0 + …` the challenge). -/
def challengeVals (s0 s1 : E) : ℕ → E
  | 0 => ofK (s1.limb 0)
  | 1 => s1 + ofK (s1.limb 0)
  | 2 => word 1 0 1
  | 3 => (s1 + ofK (s1.limb 0)) * word 1 0 1
  | 4 => word 0 0 1
  | 5 => word 0 0 1 * ofK (s1.limb 0)
  | _ => s0 + word 0 0 1 * ofK (s1.limb 0)

theorem challengeOk_of_vals {s0 s1 : V} {b : ℕ} (hc : IsCanonical128 (σ s1))
    (h : ∀ i < 7, σ (.n (b + i)) = challengeVals (σ s0) (σ s1) i) : ChallengeOk σ s0 s1 b := by
  have e : ∀ i, i < 7 → σ (.n (b + i)) = challengeVals (σ s0) (σ s1) i := h
  have e0 : σ (.n b) = ofK ((σ s1).limb 0) := e 0 (by omega)
  have hhi := (split_iff (σ s1) (σ (.n b))).mpr ⟨hc, e0⟩
  refine ⟨?_, e 2 (by omega), ?_, hhi.1, ?_, e 4 (by omega), ?_, ?_⟩
  · rw [e 1 (by omega), e0]; rfl
  · rw [e 3 (by omega), e 1 (by omega), e 2 (by omega)]; rfl
  · rw [e 3 (by omega)]; show IsInK ((σ s1 + ofK ((σ s1).limb 0)) * word 1 0 1)
    rw [word_y_inv, ← e0]; exact hhi.2
  · rw [e 5 (by omega), e 4 (by omega), e0]; rfl
  · rw [e 6 (by omega), e 5 (by omega)]; rfl

/-- A state's cells are canonical. -/
theorem cellsOfState_canonical (S : KeccakState) (odd : Bool) (c : Fin 13) :
    IsCanonical128 (cellsOfState S odd c) := (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

/-- The honest challenge is the state's. -/
theorem challengeVals_six (S : KeccakState) :
    challengeVals (cellsOfState S false 0) (cellsOfState S false 1) 6 = challengeOf S := by
  rw [Keccak.challengeOf_cells]
  simp [challengeVals, word_yy]

/-! ## One permutation -/

/-- One `KECCAK` atom in the even layouts. -/
def keccakA (ins outs : List V) : Stmt := .atom (.keccak ins outs false false)

/-- **A permutation** (`fs_perm`, `fs_perm4`, `fs_perm_pending`, G:627-670): a `KECCAK` atom in
the even layouts writing the thirteen cells of the state (`out_cells` all) reads canonical cells
and writes the cells of `permOf` of them. -/
theorem keccakA_perm {ins outs : List V} (h : (Atom.keccak ins outs false false).Holds rd σ)
    (ho : outs.length = 13 := by first | rfl | simp) :
    ins.length = 13 ∧ outs.length = 13 ∧ AllCanonical (ins.map σ) ∧
      cells13 (outs.map σ) = cellsOfState (permOf (ins.map σ)) false := by
  obtain ⟨hi, -, hK⟩ := (keccak_holds_13 ho).mp h
  refine ⟨hi, ho, fun c hc => ?_, funext fun c => hK.2 c c.isLt⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  have := hK.1 ⟨k, by simpa [hi] using hk⟩
  simpa [cells13, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this

/-- **A thirteen-cell `KECCAK` holds** of canonical read cells and written cells their
Keccak-f[1600] (`KeccakCellsRelation … .all`, its parts). -/
theorem keccak13_mk {ins outs : List V} {i o : Bool} (hi : ins.length = 13)
    (ho : outs.length = 13) (hc : ∀ c, IsCanonical128 (cells13 (ins.map σ) c))
    (hw : ∀ c, cells13 (outs.map σ) c =
      cellsOfState (keccakF1600 (stateOfCells (cells13 (ins.map σ)) i)) o c) :
    (Atom.keccak ins outs i o).Holds rd σ :=
  (keccak_holds_13 ho).mpr ⟨hi, ho, hc, fun c _ => hw c⟩

/-- **A permutation's honest outputs**: canonical inputs and the outputs `permOf` of them make the
`KECCAK` atom hold. -/
theorem keccakA_of {ins outs : List V} (hi : ins.length = 13) (ho : outs.length = 13)
    (hc : AllCanonical (ins.map σ))
    (hout : cells13 (outs.map σ) = cellsOfState (permOf (ins.map σ)) false) :
    (Atom.keccak ins outs false false).Holds rd σ := by
  refine (keccak_holds_13 ho).mpr ⟨hi, ho, fun c => ?_, fun c _ => ?_⟩
  · have hc' : c.val < (ins.map σ).length := by simp [hi]
    have := hc _ (List.getElem_mem hc')
    simpa [cells13, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc'] using this
  · rw [hout]; rfl

end
end LeanVM.Guest.B1
