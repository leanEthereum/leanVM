/-
  LeanVM.Guest.CoreMode.CellLanes

  A function's values' cells (`B2C.cellJ`) as a lane vector the generator writes, checked against the certificate's
  cells in one streamed pass: a pointer's or a returned value's cell is then one shift of a literal, not a trie the
  kernel builds per declaration (`CoreMode.locT`).
-/

module

public import LeanVM.Guest.CoreMode.ResTab
public import LeanVM.Guest.Packed.Lanes

/-!
# The cells as lanes

`lanesEq w cs L`: lane `i` of `L` (lanes of `w` bits) is `cs[i]`, and `0` past `cs`, by one pass over `cs` dividing `L`
by `2^w` at each step (`lanesEq_getD`). `cellOkP L j`, `ptrCellP L j`, `retCellP L j` are `cellB j`, `ptrCellB j`,
`retCellB j` with each cell read from `L`, equal to them where `L` holds the cells (`ptrCellB_of_P`, `retCellB_of_P`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Packed (lane)

@[expose] public section

/-- **Lane `i` of `L` is `cs[i]`, and `0` past `cs`**: by the recursor, one division a step. -/
def lanesEq (w : ℕ) (cs : List ℕ) (L : ℕ) : Bool :=
  List.rec (motive := fun _ ↦ ℕ → Bool) (fun L ↦ Nat.beq L 0)
    (fun c _ ih L ↦ Nat.beq (Nat.mod L (Nat.pow 2 w)) c && ih (Nat.div L (Nat.pow 2 w))) cs L

/-- `cellB` with the cell read from the lanes `L`. -/
noncomputable def cellOkP (L j : ℕ) (v : V) : Bool :=
  ((Bridge.extraOf j).lookup v.idx).isNone && decide (v.idx < 2 ^ 30) && decide (2 ≤ lane L Bridge.cellBits v.idx) &&
    decide (lane L Bridge.cellBits v.idx < B2C.fsN j)

/-- `ptrCellB` with the cells read from the lanes `L`. -/
noncomputable def ptrCellP (L j : ℕ) : Stmt → Bool
  | .atom a => match ptrOf a with
    | some p => cellOkP L j p
    | none => true
  | _ => true

/-- `retCellB` with the cells read from the lanes `L`. -/
noncomputable def retCellP (L j : ℕ) : Stmt → Bool
  | .ret vs => vs.all (cellOkP L j)
  | _ => true

end

public section

theorem lane_eq (v w i : ℕ) : lane v w i = (v >>> (w * i)) % 2 ^ w := rfl

theorem lane_zero_div (L w : ℕ) : lane L w 0 = L % 2 ^ w := by
  rw [lane_eq, Nat.mul_zero, Nat.shiftRight_zero]

theorem lane_succ_div (L w i : ℕ) : lane L w (i + 1) = lane (L / 2 ^ w) w i := by
  rw [lane_eq, lane_eq, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show w * (i + 1) = w + w * i by ring]

theorem lanesEq_getD {w : ℕ} : ∀ {cs : List ℕ} {L : ℕ}, lanesEq w cs L = true → ∀ i, cs.getD i 0 = lane L w i
  | [], L, h, i => by
    have h0 : L = 0 := Nat.eq_of_beq_eq_true h
    subst h0
    simp [lane_eq]
  | c :: cs, L, h, i => by
    change (Nat.beq (Nat.mod L (Nat.pow 2 w)) c && lanesEq w cs (Nat.div L (Nat.pow 2 w))) = true at h
    rw [Bool.and_eq_true] at h
    cases i with
    | zero =>
      rw [lane_zero_div, List.getD_cons_zero]
      exact (Nat.eq_of_beq_eq_true h.1).symm
    | succ i =>
      rw [lane_succ_div, List.getD_cons_succ]
      exact lanesEq_getD h.2 i

theorem cellJ_of_lanes {j L : ℕ} (h : lanesEq Bridge.cellBits (certOf j).locs L = true) (v : V) :
    B2C.cellJ j v = lane L Bridge.cellBits v.idx := by
  unfold B2C.cellJ
  exact lanesEq_getD h v.idx

theorem cellB_of_P {j L : ℕ} (h : lanesEq Bridge.cellBits (certOf j).locs L = true) {v : V}
    (hv : cellOkP L j v = true) : cellB j v = true := by
  unfold cellOkP at hv
  unfold cellB
  rw [cellJ_of_lanes h]
  exact hv

/-- **The pointers' cells, from the lanes.** -/
theorem all_ptrCellB_of_P {j L : ℕ} {l : List Stmt} (h : lanesEq Bridge.cellBits (certOf j).locs L = true)
    (hl : l.all (ptrCellP L j) = true) : l.all (ptrCellB j) = true := by
  refine List.all_eq_true.2 fun s hs ↦ ?_
  have hp := List.all_eq_true.1 hl s hs
  cases s with
  | atom a =>
    simp only [ptrCellP] at hp
    simp only [ptrCellB]
    cases hq : ptrOf a with
    | none => rfl
    | some p =>
      rw [hq] at hp
      exact cellB_of_P h hp
  | _ => rfl

/-- **The returned values' cells, from the lanes.** -/
theorem all_retCellB_of_P {j L : ℕ} {l : List Stmt} (h : lanesEq Bridge.cellBits (certOf j).locs L = true)
    (hl : l.all (retCellP L j) = true) : l.all (retCellB j) = true := by
  refine List.all_eq_true.2 fun s hs ↦ ?_
  have hp := List.all_eq_true.1 hl s hs
  cases s with
  | ret vs =>
    simp only [retCellP] at hp
    simp only [retCellB]
    exact List.all_eq_true.2 fun v hv ↦ cellB_of_P h (List.all_eq_true.1 hp v hv)
  | _ => rfl

end

end LeanVM.Guest.CoreMode
