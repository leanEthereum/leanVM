/-
  LeanVM.Guest.B1.Opening.WalkPath

  `walk_path`, inline in a query: from the leaf digest and the position's windows, the path climbs
  by hinted siblings into the cap leaf, whose parent it flags; soundly.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesCap
public import LeanVM.Guest.B1.Opening.QueriesFlatC

/-!
# `walk_path`, soundly (lean_ethereum.py)

`walk_path(n0, n1, wins, cap, flags, path_depth)`, inline (`oqWalkT`): the siblings hinted
(`merkle_children`, two cells a level), the windows of the position at `wins` dispatched a window at
a time (`walk_window`, the arm's order bits the window's), the cap leaf `cap·q⁴·wb²` written with the
node reached and the parent's flag `flags·q` set, the cap and flags offset by the caller past the
levels above the cap's leaves.

`WalkOpens`: what the walk gives at the position `q` from the node `leaf`: the windows read, and
for some siblings the cap leaf's cells the node `climbD leaf q sibs`, the parent's flag `1`.
`oqWalk_sound`: the walk's statements holding, the leaf's halves its node, its windows (when read)
the position's, give `WalkOpens` with its hinted cells the siblings (`oqPath_sound`,
`oqCap_sound`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Flat pieces -/

/-- A list literal of atoms. -/
macro "atoms_lit" : tactic => `(tactic| (repeat' apply allAtoms_cons) <;> exact allAtoms_nil)

/-- A list literal of atoms. -/
theorem allAtoms_of_forall {ss : List Stmt} (h : ∀ s ∈ ss, ∃ a, s = .atom a) : AllAtoms ss := h

theorem oqPadT_atoms (pr : ℕ) : AllAtoms (oqPadT pr) :=
  allAtoms_of_forall fun x hx => by simp [oqPadT] at hx; rcases hx with h | h | h | h | h <;> exact ⟨_, h⟩

theorem oqStepT_atoms (pr ch l K n0 n1 : ℕ) (bit : Bool) : AllAtoms (oqStepT pr ch l K n0 n1 bit) := by
  unfold oqStepT; atoms_lit

theorem oqArmT_atoms (s : Oq) (pr kL ch i a : ℕ) : AllAtoms (oqArmT s pr kL ch i a) := by
  unfold oqArmT
  exact allAtoms_append (allAtoms_map_flatten fun _ _ => oqStepT_atoms _ _ _ _ _ _ _) (by atoms_lit)

theorem oqWinT_flat (s : Oq) (bp : V) (pr kL ch i : ℕ) : Flat (oqWinT s bp pr kL ch i) := by
  intro x hx
  simp only [oqWinT, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · refine Or.inr ⟨_, _, rfl, fun arm h ↦ ?_⟩
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
    exact oqArmT_atoms _ _ _ _ _ _

theorem oqPathT_flat (s : Oq) (bp : V) (pr kL ch : ℕ) : Flat (oqPathT s bp pr kL ch) :=
  flat_append (flat_of_atoms (by atoms_lit)) (flat_map_flatten fun _ _ => oqWinT_flat _ _ _ _ _ _)

theorem oqCapT_atoms (bp cap flags : V) (k n npw : ℕ) : AllAtoms (oqCapT bp cap flags k n npw) := by
  unfold oqCapT; atoms_lit

theorem oqWalkT_flat (s : Oq) (bp cap flags : V) (pr kN ch : ℕ) :
    Flat (oqWalkT s bp cap flags pr kN ch) :=
  flat_append (oqPathT_flat _ _ _ _ _) (flat_of_atoms (oqCapT_atoms _ _ _ _ _ _))

/-- The padding run's values: `1, 0, 0, 0, 0`. -/
theorem oqPad_values {pr : ℕ} (hA : ∀ a, Stmt.atom a ∈ oqPadT pr → a.Holds rd σ) :
    σ (.n pr) = word 1 0 ∧ ∀ i < 4, σ (.n (pr + 1 + i)) = 0 := by
  refine ⟨hA _ (by simp [oqPadT] : Stmt.atom (.const (.n pr) (word 1 0)) ∈ _), fun i hi => ?_⟩
  interval_cases i
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 1)) (word 0 0)) ∈ _)).trans word_zero
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 2)) (word 0 0)) ∈ _)).trans word_zero
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 3)) (word 0 0)) ∈ _)).trans word_zero
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 4)) (word 0 0)) ∈ _)).trans word_zero

/-! ## Windows -/

/-- A path window's place and width: `(6i, oqWw s i)`. -/
theorem qwWin_path {s : Oq} {cd i : ℕ} (hi : i < oqNpw s) :
    qwWin (s.pd + cd) cd i = (6 * i, oqWw s i) := by
  unfold oqNpw at hi
  simp only [qwWin, qwNp, Nat.add_sub_cancel, oqWw, oqNpw]
  simp only [show ¬ i = (s.pd + 5) / 6 by omega, show ¬ i = (s.pd + 5) / 6 + 1 by omega,
    ↓reduceIte]
  split <;> simp_all

/-- A path window's value has the position's bits from `6i`. -/
theorem qwVal_path {s : Oq} {cd i : ℕ} (hi : i < oqNpw s) (q : ℕ) :
    qwVal (s.pd + cd) cd q i < 2 ^ oqWw s i ∧
      ∀ r < oqWw s i, (qwVal (s.pd + cd) cd q i).testBit r = q.testBit (6 * i + r) := by
  rw [qwVal, qwWin_path hi]
  refine ⟨Nat.mod_lt _ (by positivity), fun r hr ↦ ?_⟩
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_eq_true hr, Bool.true_and]

theorem oqPathT_mem_load {s : Oq} {bp : V} {pr kL ch i : ℕ} (hi : i < oqNpw s) :
    Stmt.atom (.load (.n (oqWk s ch i)) bp i) ∈ oqPathT s bp pr kL ch :=
  oqPathT_mem_win hi (by simp [oqWinT])

theorem qwN_eq (s : Oq) (cd : ℕ) : qwN (s.pd + cd) cd = oqNpw s + 2 := by
  simp [qwN, qwNp, oqNpw]

/-- **The walk reads each of its position's windows.** -/
theorem oqWalk_winLoads {s : Oq} {cd : ℕ} {bp cap flags : V} {pr kL ch n : ℕ}
    (hPa : BlockOk rd σ (oqPathT s bp pr kL ch))
    (hC : ∀ a, Stmt.atom a ∈ oqCapT bp cap flags (oqCq s ch) n (oqNpw s) → a.Holds rd σ) :
    ∀ i < qwN (s.pd + cd) cd, ∃ v, LoadHolds rd (σ bp) i v := by
  intro i hi
  rw [qwN_eq] at hi
  by_cases h1 : i < oqNpw s
  · exact ⟨_, hPa.atom (oqPathT_mem_load h1)⟩
  by_cases h2 : i = oqNpw s
  · subst h2
    exact ⟨_, hC _ (by simp [oqCapT] : Stmt.atom (.load (.n (oqCq s ch)) bp (oqNpw s)) ∈ _)⟩
  obtain rfl : i = oqNpw s + 1 := by omega
  exact ⟨_, hC _ (by simp [oqCapT] : Stmt.atom (.load (.n (oqCq s ch + 1)) bp (oqNpw s + 1)) ∈ _)⟩

/-! ## The walk -/

/-- **What a walk gives** at the position `q` from the node `leaf`: its windows read, and for
some `pd` siblings the parent's flag set and the cap leaf's cells holding the node reached, at
the cap and flags the caller offset past the levels above the leaves. -/
def WalkOpens (rd : Reader) (pd cd : ℕ) (wins cap flags : E) (q : ℕ) (leaf : Digest) : Prop :=
  (∀ i < qwN (pd + cd) cd, LoadHolds rd wins i (gen ^ qwVal (pd + cd) cd q i)) ∧
    ∃ sibs : List Digest, sibs.length = pd ∧
      LoadHolds rd flags (q / 2 ^ (pd + 1)) 1 ∧
      LoadHolds rd cap (2 * (q / 2 ^ pd)) (digestHalves (climbD leaf q sibs)).1 ∧
      LoadHolds rd cap (2 * (q / 2 ^ pd) + 1) (digestHalves (climbD leaf q sibs)).2

/-- **The walk, inline** (its statements holding at `σ`): from the leaf's halves at `kN, kN + 1`,
its windows (when read) those of `q < 2^(pd + cd)`, the zero run at `pr`, it reads the windows,
its hinted cells from `ch` hold siblings, and the cap leaf and the flag are written. -/
theorem oqWalk_sound {s : Oq} {cd : ℕ} (hcd : 1 ≤ cd) {bp cap flags : V} {pr kN ch : ℕ}
    (hA : BlockOk rd σ (oqWalkT s bp cap flags pr kN ch))
    (hpad : σ (.n pr) = word 1 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0)
    {leaf : Digest} {q : ℕ} (hleaf : (σ (.n kN), σ (.n (kN + 1))) = digestHalves leaf)
    (hq : q < 2 ^ (s.pd + cd))
    (hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + cd) cd →
      v = gen ^ qwVal (s.pd + cd) cd q i) :
    (∀ i < qwN (s.pd + cd) cd, LoadHolds rd (σ bp) i (gen ^ qwVal (s.pd + cd) cd q i)) ∧
      ∃ sibs : List Digest, sibs.length = s.pd ∧ (∀ l < s.pd, SibAt σ ch l (sibs.getD l default)) ∧
        LoadHolds rd (σ flags) (q / 2 ^ (s.pd + 1)) 1 ∧
        LoadHolds rd (σ cap) (2 * (q / 2 ^ s.pd)) (digestHalves (climbD leaf q sibs)).1 ∧
        LoadHolds rd (σ cap) (2 * (q / 2 ^ s.pd) + 1) (digestHalves (climbD leaf q sibs)).2 := by
  have hPa : BlockOk rd σ (oqPathT s bp pr kN ch) :=
    BlockOk.mono hA fun x hx ↦ List.mem_append_left _ hx
  have hC : ∀ a, Stmt.atom a ∈ oqCapT bp cap flags (oqCq s ch) (oqNd s kN ch (oqNpw s) 0) (oqNpw s) →
      a.Holds rd σ :=
    fun a ha ↦ BlockOk.atom hA (List.mem_append_right _ ha)
  obtain ⟨sibs, hsl, hsib, hnd⟩ := oqPath_sound hPa hpad hz (q := q) (fun i hi ↦
    ⟨_, (qwVal_path hi q).1, hwin _ _ (hPa.atom (oqPathT_mem_load hi)) (by rw [qwN_eq]; omega),
      (qwVal_path hi q).2⟩) (by simpa [oqNd] using hleaf)
  obtain ⟨hflag, hc0, hc1⟩ := oqCap_sound (pd := s.pd) hcd hC hq hwin
  have e1 : oqNd s kN ch (oqNpw s) 0 + 1 = oqNd s kN ch (oqNpw s) 1 := by unfold oqNd; split <;> omega
  rw [e1] at hc1
  rw [show σ (.n (oqNd s kN ch (oqNpw s) 0)) = (digestHalves (climbD leaf q sibs)).1 by
    rw [← hnd]] at hc0
  rw [show σ (.n (oqNd s kN ch (oqNpw s) 1)) = (digestHalves (climbD leaf q sibs)).2 by
    rw [← hnd]] at hc1
  refine ⟨fun i hi ↦ ?_, sibs, hsl, hsib, hflag, hc0, hc1⟩
  obtain ⟨v, hv⟩ := oqWalk_winLoads (cd := cd) hPa hC i hi
  rw [← hwin i v hv hi]
  exact hv

end
end LeanVM.Guest.B1
