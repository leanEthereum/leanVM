/-
  LeanVM.Guest.Value.KeccakDuplex

  The guest's Fiat-Shamir duplex step, one `KECCAK` with `cap=`, is the Spec's `duplex`; its
  challenge cells are `challengeOf`.
-/

module

public import LeanVM.Guest.Value.KeccakLayout

/-!
# The duplex sponge in cells

The verifier's transcript (`Statement/LeanVmVerifier.lean`, `Sponge`, `duplex`, `absorb`, `squeeze`) is a
duplex over Keccak-f[1600] in overwrite mode: up to four waiting scalars, each its two limbs, a
zero lane and its tag (`pendingLanes`), overwrite the rate lanes `0..16`, zeros after them, and
lanes `16..25` are kept (`duplexInput`). The guest (`crates/rec_aggregation/guests/lean_ethereum.py`,
G below) holds the sponge as the thirteen-cell output of its last permutation, of which only the
five cells `8..12` (lanes `16..24`, `fs0 .. fs4`) travel; a waiting scalar `x` with tag `t` is two
rate cells, `x` itself and `y·t` (`fs_pack`); a permutation is `keccak(a, b, out, tail=, cap=sp)`
(`fs_perm`), lowered as one `KECCAK` in the even layouts whose eight rate cells are the waiting
cells (zeros past them) and whose cells `8..12` are `sp`'s last five.

* `keccak_duplex`: that `KECCAK` writes the cells of `keccakF (duplexInput ⟨S, pending⟩)`;
* `duplex_id`, `squeeze_id`, `absorb_id_lt`, `absorb_id_full`: the Spec's operations at
  `m = Id`, `F = keccakF`;
* `challengeOf_cells`: `challenge_from_state` reads `challengeOf`, the state's cell `0`;
* `powLane_cells`: the proof of work, lane `2`, is the low limb of cell `1` (`grind_check`).
-/

namespace LeanVM.Guest.Value.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Value.KeccakEval

@[expose] public section

/-! ## The rate cells of waiting scalars -/

/-- Rate cell `c < 8` of the waiting scalars: lanes `2c` and `2c + 1` of `pendingLanes`, zero past
them. -/
def rateCell (pending : List (E × ℕ)) (c : ℕ) : E :=
  E.ofLimbs (K.ofLane ((Compile.pendingLanes pending).getD (2 * c) 0))
    (K.ofLane ((Compile.pendingLanes pending).getD (2 * c + 1) 0))

/-- The two rate cells of one waiting scalar `x` with tag `t`: `x` itself, then the zero lane and
the tag (`fs_pack`: `rate[2k] = x`, `rate[2k + 1] = Y_TOWER * tag`). -/
def scalarCells (x : E) (t : ℕ) : E × E := (x, E.ofLimbs 0 (K.ofBits t))

theorem length_pendingLanes (ps : List (E × ℕ)) :
    (Compile.pendingLanes ps).length = 4 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [Compile.pendingLanes] at *; omega

/-- Lane `j < 4` of waiting scalar `k`. -/
theorem getD_pendingLanes (ps : List (E × ℕ)) {k : ℕ} (hk : k < ps.length) {j : ℕ} (hj : j < 4) :
    (Compile.pendingLanes ps).getD (4 * k + j) 0 =
      [(ps[k].1.limb 0).lane, (ps[k].1.limb 1).lane, 0, ps[k].2.toUInt64].getD j 0 := by
  induction ps generalizing k with
  | nil => simp at hk
  | cons p ps ih =>
    simp only [Compile.pendingLanes, List.flatMap_cons, List.getD_eq_getElem?_getD]
    cases k with
    | zero =>
      rw [List.getElem?_append_left (by simp; omega)]
      simp
    | succ k =>
      rw [List.getElem?_append_right (by simp; omega)]
      have := ih (k := k) (by simpa using hk)
      simp only [Compile.pendingLanes, List.getD_eq_getElem?_getD] at this
      simp only [List.length_cons, List.length_nil, List.getElem_cons_succ]
      rw [show 4 * (k + 1) + j - (0 + 1 + 1 + 1 + 1) = 4 * k + j by omega, this]

/-- **Waiting scalar `k` sits in rate cells `2k` and `2k + 1`** (`fs_pack(rate, k, x, tag)`). -/
theorem rateCell_scalar (ps : List (E × ℕ)) (k : ℕ) (hk : k < ps.length) :
    (rateCell ps (2 * k), rateCell ps (2 * k + 1)) = scalarCells ps[k].1 ps[k].2 := by
  have e0 : 2 * (2 * k) = 4 * k + 0 := by ring
  have e1 : 2 * (2 * k) + 1 = 4 * k + 1 := by ring
  have e2 : 2 * (2 * k + 1) = 4 * k + 2 := by ring
  have e3 : 2 * (2 * k + 1) + 1 = 4 * k + 3 := by ring
  rw [rateCell, rateCell, e1, e0, e3, e2, getD_pendingLanes ps hk (show 0 < 4 by omega),
    getD_pendingLanes ps hk (show 1 < 4 by omega), getD_pendingLanes ps hk (show 2 < 4 by omega),
    getD_pendingLanes ps hk (show 3 < 4 by omega)]
  exact Prod.ext (ofLimbs_limb _) rfl

/-- Rate cells past the waiting scalars are zero. -/
theorem rateCell_past (ps : List (E × ℕ)) {c : ℕ} (hc : 2 * ps.length ≤ c) : rateCell ps c = 0 := by
  have h1 : (Compile.pendingLanes ps).length ≤ 2 * c := by rw [length_pendingLanes]; omega
  simp only [rateCell, List.getD_eq_getElem?_getD, List.getElem?_eq_none h1,
    List.getElem?_eq_none (show (Compile.pendingLanes ps).length ≤ 2 * c + 1 by omega),
    Option.getD_none, ofLane_zero]
  exact zero_eq_ofLimbs.symm

/-! ## The duplex step -/

/-- The cells of a duplex step's input hold `duplexInput`. -/
theorem stateOfCells_duplex {S : KeccakState} {pending : List (E × ℕ)} {I : Fin 13 → E}
    (hrate : ∀ c : Fin 13, c.val < 8 → I c = rateCell pending c)
    (hcap : ∀ c : Fin 13, 8 ≤ c.val → I c = cellsOfState S false c) :
    stateOfCells I false = Compile.duplexInput ⟨S, pending, none⟩ := by
  apply Vector.ext
  intro i hi
  have e := lane_fin (stateOfCells I false) ⟨i, hi⟩
  simp only [Fin.getElem_fin] at e
  rw [← e, lane_stateOfCells I false ⟨i, hi⟩, Compile.duplexInput, Vector.getElem_ofFn]
  by_cases h : i < 16
  · have hc : (laneCell false ⟨i, hi⟩).val < 8 := by
      simp only [laneCell, laneCellIdx, Bool.false_eq_true, false_or]; split <;> omega
    rw [hrate _ hc]
    simp only [h, ↓reduceIte, laneCell, laneLimb, laneCellIdx, laneLimbIdx,
      show ¬ (false = true ∨ 17 ≤ i) by simp; omega, rateCell]
    rcases Nat.mod_two_eq_zero_or_one i with h2 | h2
    · simp only [h2, Fin.zero_eta, limb_ofLimbs, Matrix.cons_val_zero, lane_ofLane,
        show 2 * (i / 2) = i by omega]
    · simp only [h2, Fin.mk_one, limb_ofLimbs, Matrix.cons_val_one, Matrix.cons_val_zero,
        lane_ofLane, show 2 * (i / 2) + 1 = i by omega]
  · have hc : 8 ≤ (laneCell false ⟨i, hi⟩).val := by
      simp only [laneCell, laneCellIdx, Bool.false_eq_true, false_or]; split <;> omega
    rw [hcap _ hc, limb_cellsOfState, lane_ofLane]
    simp [h]

/-- **The guest's duplex step is the Spec's** (`keccak(…, cap=sp)`, `fs_perm`, `fs_perm4`,
`fs_perm_pending`): a `KECCAK` in the even layouts whose rate cells `0..7` are the waiting
scalars' (`rateCell`) and whose cells `8..12` are those of a state `S` writes the cells of
`keccakF (duplexInput ⟨S, pending⟩)`. -/
theorem keccak_duplex {S : KeccakState} {pending : List (E × ℕ)} {I O : Fin 13 → E}
    (hrate : ∀ c : Fin 13, c.val < 8 → I c = rateCell pending c)
    (hcap : ∀ c : Fin 13, 8 ≤ c.val → I c = cellsOfState S false c)
    (hK : KeccakCellsRelation I false O false .all) :
    O = cellsOfState (keccakF1600 (Compile.duplexInput ⟨S, pending, none⟩)) false := by
  funext c
  rw [hK c c.isLt, stateOfCells_duplex hrate hcap]

/-- `squeeze` with Keccak-f and no ground challenge: a permutation, its challenge. -/
theorem squeeze_id (sp : Compile.Sponge) (hg : sp.ground = none) :
    Compile.squeeze (m := Id) keccakF1600 sp =
      (Compile.challengeOf (keccakF1600 (Compile.duplexInput sp)),
        ⟨keccakF1600 (Compile.duplexInput sp), [], none⟩) := by
  obtain ⟨st, p, g⟩ := sp
  subst hg
  rfl

/-- `squeeze` returns a ground challenge and clears it. -/
theorem squeeze_id_ground (sp : Compile.Sponge) (c : E) (hg : sp.ground = some c) :
    Compile.squeeze (m := Id) keccakF1600 sp = (c, { sp with ground := none }) := by
  obtain ⟨st, p, g⟩ := sp
  subst hg
  rfl

/-- `absorb` at a full queue permutes first. -/
theorem absorb_id_full (sp : Compile.Sponge) (x : E) (t : ℕ) (h : sp.pending.length = 4) :
    Compile.absorb (m := Id) keccakF1600 sp x t =
      ⟨keccakF1600 (Compile.duplexInput sp), [(x, t)], sp.ground⟩ := by
  obtain ⟨st, p, g⟩ := sp
  simp only at h
  simp only [Compile.absorb, Compile.duplex, Compile.rateScalars, h, ↓reduceIte]
  rfl

/-! ## Reading a challenge, packing a scalar -/

/-- **`challenge_from_state`**: the challenge of a state is its cell `0`. -/
theorem challengeOf_cells (S : KeccakState) : Compile.challengeOf S = cellsOfState S false 0 := by
  simp [Compile.challengeOf, cellsOfState, cellLanes]

/-- The first limb of a challenge is cell `0`'s. -/
theorem challengeOf_limb0 (S : KeccakState) :
    (Compile.challengeOf S).limb 0 = (cellsOfState S false 0).limb 0 := by
  rw [challengeOf_cells]

/-- **The proof of work** (`absorbNonce`'s lane `2`) is the low limb of cell `1` (`grind_check`
reads it from `nxt[1]`). -/
theorem powLane_cells (S : KeccakState) : Keccak.lane S 2 = ((cellsOfState S false 1).limb 0).lane := by
  simp [cellsOfState, cellLanes]

/-- A `K` literal's lane. -/
@[simp] theorem ofLane_toUInt64 (t : ℕ) : K.ofLane t.toUInt64 = K.ofBits t := rfl

end
end LeanVM.Guest.Value.Keccak
