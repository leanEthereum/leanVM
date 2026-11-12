/-
  LeanVM.Guest.B1.Fs.Templates

  The expansions of the guest's inline Fiat-Shamir helpers as statement templates, what they ask
  of a valuation, and what their cells are.
-/

module

public import LeanVM.Guest.B1.Common.Run

/-!
# The inline Fiat-Shamir helpers

The helpers of the guest's sponge (`crates/rec_aggregation/guests/lean_ethereum.py`, G below, its
Fiat-Shamir section) are `@inline`: their atoms sit in their callers' core IR, numbered by the
caller. Their expansions are uniform (`Expand.lean`, the compiler's `builtins.rs`), so each is a
template over its operands and its first value `b`; a caller's body is checked equal to its
composition of templates by kernel evaluation (`stmtsEqb_sound`).

* `fsPackT x b t` (`fs_pack`): the rate cells `b = x` (a copy) and `b + 1 = y·t` (a constant,
  `word 0 t`); `fsPackT_cells`: they are `Keccak.scalarCells x t`.
* `fsNextT cur off b` (`fs_next`): the word at `cur·g^off` into `b`, then `fsPackT (.n b) (b + 1)
  dsObserve`: its cells `b + 1`, `b + 2`. `fsNonceT cur off b` (`fs_absorb_nonce`'s `fs_pack`):
  the same with the tag `dsPowNonce`.
* `padRunT b`: the constant run a function's first `fs_perm` with fewer than three scalars
  waiting emits (`word 1 0` at `b`, zeros at `b + 1 .. b + 4`), which every later one reuses;
  `zero2T b` (`fs_perm`'s `rate[6] = rate[7] = 0` at three scalars).
* `permIns k rate z cap` (`fs_perm(sp, rate, k)`): the thirteen cells its `KECCAK` reads, the
  rate's first `2k` cells, then the zero run from `z`, then the capacity; `keccakA` the atom.
* `challengeT s0 b` (`challenge_from_state`, a returned `nxt[0]`): the copy into `b` of the
  state's cell `0`, which is `challengeOf` (`challengeT_value`).
* `grindCallT bits w tabs` (`fs_grind_squeeze`'s `grind_check(nxt[1], tabs, bits)`): the call of
  `grind_check__L{bits}`.

`keccakA_perm`: a `KECCAK` atom writes `permOf` of its inputs; `keccakA_fs`: on the cells of a
carried sponge (`pendCells`, zeros, capacity) it writes the cells of `s.perm`; `grindSqueeze_cells`
turns a nonce's permutation and a passing `grind_check` into `Fs.grindSqueeze`. The `…Vals`
functions are the honest values of each template.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## `fs_pack` -/

/-- `fs_pack(rate, k, x, tag)`'s atoms from the value `b`: `rate[2k] = x` (a copy into `b`) and
`rate[2k + 1] = Y_TOWER * tag` (the constant `word 0 t` at `b + 1`). -/
def fsPackT (x : V) (b t : ℕ) : List Stmt :=
  [.atom (.copy (.n b) x), .atom (.const (.n (b + 1)) (word 0 t))]

/-- What `fsPackT` asks of a valuation. -/
def FsPackOk (σ : Val) (x : V) (b t : ℕ) : Prop :=
  σ (.n b) = σ x ∧ σ (.n (b + 1)) = word 0 t

theorem holds_fsPackT (x : V) (b t : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (fsPackT x b t) next kret ↔ FsPackOk σ x b t ∧ next := by
  simp only [fsPackT, FsPackOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

/-- The tag cell `word 0 t` is the scalar's second rate cell. -/
theorem word_zero_tag (t : ℕ) : word 0 t = (Keccak.scalarCells 0 t).2 := rfl

/-- **`fs_pack`'s cells** are the scalar's rate cells `Keccak.scalarCells x t`. -/
theorem fsPackT_cells {x : V} {b t : ℕ} (h : FsPackOk σ x b t) :
    (σ (.n b), σ (.n (b + 1))) = Keccak.scalarCells (σ x) t := by
  rw [h.1, h.2]
  rfl

/-- The honest values of `fsPackT` on the word `x`. -/
def fsPackVals (x : E) (t : ℕ) : ℕ → E
  | 0 => x
  | _ => word 0 t

theorem fsPackOk_of_vals {x : V} {b t : ℕ} (h : ∀ i < 2, σ (.n (b + i)) = fsPackVals (σ x) t i) :
    FsPackOk σ x b t :=
  ⟨h 0 (by omega), h 1 (by omega)⟩

/-! ## `fs_next` and the nonce -/

/-- `fs_next(rate, k, cursor)`'s atoms from the value `b`: the word at `cur·g^off` into `b`, then
`fs_pack` of it with the tag `DS_OBSERVE = 1`, its cells `b + 1`, `b + 2`. -/
def fsNextT (cur : V) (off b : ℕ) : List Stmt :=
  .atom (.load (.n b) cur off) :: fsPackT (.n b) (b + 1) dsObserve

theorem holds_fsNextT (cur : V) (off b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (fsNextT cur off b) next kret ↔
      (LoadHolds rd (σ cur) off (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve) ∧ next := by
  rw [fsNextT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, holds_fsPackT, and_assoc]

/-- `fs_absorb_nonce`'s `fs_pack` of the nonce `cursor[GEN ** 0]`, from the value `b`: the
nonce loaded into `b`, its cells `b + 1`, `b + 2` with the tag `DS_POW_NONCE = 4`. -/
def fsNonceT (cur : V) (off b : ℕ) : List Stmt :=
  .atom (.load (.n b) cur off) :: fsPackT (.n b) (b + 1) dsPowNonce

theorem holds_fsNonceT (cur : V) (off b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (fsNonceT cur off b) next kret ↔
      (LoadHolds rd (σ cur) off (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsPowNonce) ∧ next := by
  rw [fsNonceT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, holds_fsPackT, and_assoc]

/-! ## The zero cells of a permutation -/

/-- The constant run of a function's first `fs_perm` with fewer than three scalars waiting:
`word 1 0` at `b`, then the zeros `b + 1 .. b + 4` that its and every later permutation's
missing rate cells read. -/
def padRunT (b : ℕ) : List Stmt :=
  [.atom (.const (.n b) (word 1 0)), .atom (.const (.n (b + 1)) (word 0 0)),
    .atom (.const (.n (b + 2)) (word 0 0)), .atom (.const (.n (b + 3)) (word 0 0)),
    .atom (.const (.n (b + 4)) (word 0 0))]

/-- What `padRunT` asks of a valuation. -/
def PadRunOk (σ : Val) (b : ℕ) : Prop :=
  σ (.n b) = word 1 0 ∧ σ (.n (b + 1)) = 0 ∧ σ (.n (b + 2)) = 0 ∧ σ (.n (b + 3)) = 0 ∧
    σ (.n (b + 4)) = 0

theorem holds_padRunT (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (padRunT b) next kret ↔ PadRunOk σ b ∧ next := by
  simp only [padRunT, PadRunOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_zero, and_assoc]

/-- `fs_perm`'s `rate[6] = 0`, `rate[7] = 0` at three scalars waiting. -/
def zero2T (b : ℕ) : List Stmt :=
  [.atom (.const (.n b) (word 0 0)), .atom (.const (.n (b + 1)) (word 0 0))]

theorem holds_zero2T (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (zero2T b) next kret ↔
      (σ (.n b) = 0 ∧ σ (.n (b + 1)) = 0) ∧ next := by
  simp only [zero2T, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_zero, and_assoc]

/-- The thirteen cells `fs_perm(sp, rate, k)`'s `KECCAK` reads: the first `2k` rate cells, then
the zero run from `z` (`[0, 0]` literals read `z`, the default tail `z .. z + 3`), then the
capacity; at three or four scalars the rate's eight cells (`rate[6]`, `rate[7]` zero constants
at three). -/
def permIns (k : ℕ) (rate : List V) (z : ℕ) (cap : List V) : List V :=
  (match k with
    | 0 => [.n z, .n z, .n z, .n z, .n z, .n (z + 1), .n (z + 2), .n (z + 3)]
    | 1 => rate.take 2 ++ [.n z, .n z, .n z, .n (z + 1), .n (z + 2), .n (z + 3)]
    | 2 => rate.take 4 ++ [.n z, .n (z + 1), .n (z + 2), .n (z + 3)]
    | _ => rate.take 8) ++ cap

/-! ## `challenge_from_state` -/

/-- `challenge_from_state(state)` (or a returned `nxt[0]`): the copy of the state's cell `0`
into `b`. -/
def challengeT (s0 : V) (b : ℕ) : List Stmt := [.atom (.copy (.n b) s0)]

/-- What `challengeT` asks of a valuation. -/
def ChallengeOk (σ : Val) (s0 : V) (b : ℕ) : Prop := σ (.n b) = σ s0

theorem holds_challengeT (s0 : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (challengeT s0 b) next kret ↔ ChallengeOk σ s0 b ∧ next := by
  simp only [challengeT, ChallengeOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds]

/-- **`challenge_from_state`**: on the cell `0` of a state, the template's challenge is
`challengeOf` of the state. -/
theorem challengeT_value {s0 : V} {b : ℕ} {S : KeccakState} (h : ChallengeOk σ s0 b)
    (h0 : σ s0 = cellsOfState S false 0) : σ (.n b) = challengeOf S := by
  rw [h, h0, Keccak.challengeOf_cells]

/-! ## `grind_check` calls -/

/-- `grind_check(nxt[1], tabs, bits)`: the call of `grind_check__L{bits}` on the permutation's
cell `1` and the window table. -/
def grindCallT (bits : ℕ) (w tabs : V) : Stmt := .call (grindCheckName bits) [w, tabs] []

/-! ## One permutation -/

/-- One `KECCAK` atom in the even layouts. -/
def keccakA (ins outs : List V) : Stmt := .atom (.keccak ins outs false false)

/-- **A permutation** (`fs_perm`, `fs_perm_pending`): a `KECCAK` atom in the even
layouts writing the thirteen cells of the state writes the cells of `permOf` of the cells it
reads. -/
theorem keccakA_perm {ins outs : List V} (h : (Atom.keccak ins outs false false).Holds rd σ)
    (ho : outs.length = 13 := by first | rfl | simp) :
    ins.length = 13 ∧ outs.length = 13 ∧
      cells13 (outs.map σ) = cellsOfState (permOf (ins.map σ)) false := by
  obtain ⟨hi, -, hK⟩ := (keccak_holds_13 ho).mp h
  exact ⟨hi, ho, funext fun c => hK c c.isLt⟩

/-- **A permutation of a carried sponge**: when the cells read are the waiting scalars' rate
cells, zeros, then the capacity, the cells written are those of `s.perm`. -/
theorem keccakA_fs {ins outs : List V} {s : Fs} (h : (Atom.keccak ins outs false false).Holds rd σ)
    (hs : s.pend.length ≤ 4)
    (hins : ins.map σ = pendCells s.pend ++ List.replicate (8 - 2 * s.pend.length) 0 ++ s.cap)
    (ho : outs.length = 13 := by first | rfl | simp) :
    cells13 (outs.map σ) = cellsOfState s.perm false := by
  rw [(keccakA_perm h ho).2.2, hins, perm_eq_cells s hs]

/-- **A thirteen-cell `KECCAK` holds** of read cells whose Keccak-f[1600] the written cells
are. -/
theorem keccak13_mk {ins outs : List V} {i o : Bool} (hi : ins.length = 13)
    (ho : outs.length = 13)
    (hw : ∀ c, cells13 (outs.map σ) c =
      cellsOfState (keccakF1600 (stateOfCells (cells13 (ins.map σ)) i)) o c) :
    (Atom.keccak ins outs i o).Holds rd σ :=
  (keccak_holds_13 ho).mpr ⟨hi, ho, fun c _ => hw c⟩

/-- **A permutation's honest outputs**: the outputs `permOf` of the inputs make the `KECCAK` atom
hold. -/
theorem keccakA_of {ins outs : List V} (hi : ins.length = 13) (ho : outs.length = 13)
    (hout : cells13 (outs.map σ) = cellsOfState (permOf (ins.map σ)) false) :
    (Atom.keccak ins outs false false).Holds rd σ :=
  (keccak_holds_13 ho).mpr ⟨hi, ho, fun c _ => by rw [hout]; rfl⟩

/-! ## A grind then a challenge (`fs_grind_squeeze`) -/

/-- **`fs_grind_squeeze`'s meaning**, from its permutation's cells: at `bits ≠ 0`, cells `0`, `1`
of the nonce's permutation, the `grind_check` on cell `1` passing (`MeaningGrindCheck`'s
condition), give `Fs.GrindOk` and `Fs.grindSqueeze`'s challenge and sponge. -/
theorem grindSqueeze_cells {s : Fs} {bits : ℕ} (hb : bits ≠ 0) (n : E) (c0 c1 : E)
    (h0 : c0 = cellsOfState (s.nonceState n) false 0)
    (h1 : c1 = cellsOfState (s.nonceState n) false 1)
    (hpow : (c1.limb 0).lane.toNat % 2 ^ bits = 0) :
    s.GrindOk bits n ∧ (s.grindSqueeze bits n).1 = c0 ∧
      (s.grindSqueeze bits n).2 = ⟨capOf (s.nonceState n), []⟩ := by
  rw [Fs.grindSqueeze_pos s hb n, h0, Keccak.challengeOf_cells]
  refine ⟨Or.inr ?_, rfl, rfl⟩
  rw [Keccak.powLane_cells, ← h1]
  exact decide_eq_true hpow

/-- The proof of work passes exactly when `grind_check`'s condition holds of the permutation's
cell `1`. -/
theorem grindOk_iff {s : Fs} {bits : ℕ} (hb : bits ≠ 0) (n : E) :
    s.GrindOk bits n ↔
      ((cellsOfState (s.nonceState n) false 1).limb 0).lane.toNat % 2 ^ bits = 0 := by
  rw [Fs.GrindOk, Keccak.powLane_cells, powOk, decide_eq_true_iff]
  exact ⟨fun h => h.resolve_left hb, Or.inr⟩

end
end LeanVM.Guest.B1
