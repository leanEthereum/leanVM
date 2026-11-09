/-
  LeanVM.Guest.B1.Opening.WalkPath

  `walk_path` (a function of its own at 40f877dc): from a node and a position's windows, the path
  climbs by hinted siblings into the cap leaf, whose parent it flags; soundly.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesCap
public import LeanVM.Guest.B1.Opening.QueriesFlatC

/-!
# `walk_path`, soundly (lean_ethereum.py:1308-1343 at 40f877dc)

`walk_path__L{pd}_L{cd}(n0, n1, wins, cap, flags)`: the children hinted (`merkle_children`), the
windows of the position at `wins` dispatched a window at a time (`walk_window`, the arm's order
bits the window's), the cap leaf `cap·q⁴·wb²` at `2^(cd+1)` written with the node reached and the
parent's flag `flags·q` at `2^(cd-1)` set (`wpBodyT`).

`WalkOpens`: what a call gives at the position `q` from the node `leaf`: the windows read, and for
some siblings the cap leaf's cells the node `climbD leaf q sibs`, the parent's flag `1`.
`WalkSound walk pd cd`: every call of `walk` with the leaf's halves as its node, its windows (when
read) the position's, gives `WalkOpens`. `WalkFn.sound`: a function whose body is `wpBodyT` (`WalkFn`) is
`WalkSound` (`oqPath_sound`, `oqCap_sound`); `wp_frame_sound`, at a frame, names the siblings its
children cells hold.
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
  unfold oqWinT
  refine flat_append (flat_append (flat_of_atoms (by atoms_lit)) ?_) ?_
  · split
    · exact flat_of_atoms (oqPadT_atoms _)
    · exact flat_of_atoms allAtoms_nil
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · refine Or.inr ⟨_, _, rfl, fun arm h ↦ ?_⟩
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
      exact oqArmT_atoms _ _ _ _ _ _

theorem oqPathT_flat (s : Oq) (bp : V) (pr kL ch : ℕ) : Flat (oqPathT s bp pr kL ch) :=
  flat_append (flat_of_atoms (by atoms_lit)) (flat_map_flatten fun _ _ => oqWinT_flat _ _ _ _ _ _)

theorem oqCapT_atoms (s : Oq) (bp cap flags : V) (kL ch : ℕ) : AllAtoms (oqCapT s bp cap flags kL ch) := by
  unfold oqCapT; atoms_lit

/-- The padding run's values: `1, 0, 0, 0, 0`. -/
theorem oqPad_values {pr : ℕ} (hA : ∀ a, Stmt.atom a ∈ oqPadT pr → a.Holds rd σ) :
    σ (.n pr) = word 1 0 0 ∧ ∀ i < 4, σ (.n (pr + 1 + i)) = 0 := by
  refine ⟨hA _ (by simp [oqPadT] : Stmt.atom (.const (.n pr) (word 1 0 0)) ∈ _), fun i hi => ?_⟩
  interval_cases i
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 1)) (word 0 0 0)) ∈ _)).trans word_zero
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 2)) (word 0 0 0)) ∈ _)).trans word_zero
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 3)) (word 0 0 0)) ∈ _)).trans word_zero
  · exact (hA _ (by simp [oqPadT] : Stmt.atom (.const (.n (pr + 4)) (word 0 0 0)) ∈ _)).trans word_zero

/-- The path's first window places the padding run (`pd ≥ 1`). -/
theorem oqPath_pad {s : Oq} (hpd : 1 ≤ s.pd) {bp : V} {pr kL ch : ℕ}
    (hA : BlockOk rd σ (oqPathT s bp pr kL ch)) :
    σ (.n pr) = word 1 0 0 ∧ ∀ i < 4, σ (.n (pr + 1 + i)) = 0 :=
  oqPad_values fun a ha ↦ hA.atom (oqPathT_mem_win (i := 0) (by unfold oqNpw; omega)
    (by simp only [oqWinT, ↓reduceIte, List.mem_append]; exact Or.inl (Or.inr ha)))

/-! ## Windows -/

/-- A path window's place and width: `(6i, oqWw s i)`. -/
theorem qwWin_path {s : Oq} {i : ℕ} (hi : i < oqNpw s) :
    qwWin (s.pd + s.cd) s.cd i = (6 * i, oqWw s i) := by
  unfold oqNpw at hi
  simp only [qwWin, qwNp, Nat.add_sub_cancel, oqWw, oqNpw]
  simp only [show ¬ i = (s.pd + 5) / 6 by omega, show ¬ i = (s.pd + 5) / 6 + 1 by omega,
    ↓reduceIte]
  split <;> simp_all

/-- A path window's value has the position's bits from `6i`. -/
theorem qwVal_path {s : Oq} {i : ℕ} (hi : i < oqNpw s) (q : ℕ) :
    qwVal (s.pd + s.cd) s.cd q i < 2 ^ oqWw s i ∧
      ∀ r < oqWw s i, (qwVal (s.pd + s.cd) s.cd q i).testBit r = q.testBit (6 * i + r) := by
  rw [qwVal, qwWin_path hi]
  refine ⟨Nat.mod_lt _ (by positivity), fun r hr ↦ ?_⟩
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_eq_true hr, Bool.true_and]

theorem oqPathT_mem_load {s : Oq} {bp : V} {pr kL ch i : ℕ} (hi : i < oqNpw s) :
    Stmt.atom (.load (.n (oqWk s ch i)) bp i) ∈ oqPathT s bp pr kL ch :=
  oqPathT_mem_win hi (by simp [oqWinT])

theorem qwN_eq (s : Oq) : qwN (s.pd + s.cd) s.cd = oqNpw s + 2 := by
  simp [qwN, qwNp, oqNpw]

/-- **The walk reads each of its position's windows.** -/
theorem oqWalk_winLoads {s : Oq} {bp cap flags : V} {pr kL ch : ℕ}
    (hPa : BlockOk rd σ (oqPathT s bp pr kL ch))
    (hC : ∀ a, Stmt.atom a ∈ oqCapT s bp cap flags kL ch → a.Holds rd σ) :
    ∀ i < qwN (s.pd + s.cd) s.cd, ∃ v, LoadHolds rd (σ bp) i v := by
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
some `pd` siblings the parent's flag set and the cap leaf's cells holding the node reached. -/
def WalkOpens (rd : Reader) (pd cd : ℕ) (wins cap flags : E) (q : ℕ) (leaf : Digest) : Prop :=
  (∀ i < qwN (pd + cd) cd, LoadHolds rd wins i (gen ^ qwVal (pd + cd) cd q i)) ∧
    ∃ sibs : List Digest, sibs.length = pd ∧
      LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) 1 ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ pd)) (digestHalves (climbD leaf q sibs)).1 ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ pd) + 1) (digestHalves (climbD leaf q sibs)).2

/-- **`walk` is a sound walk of `pd` levels below a cap of depth `cd`**: a call on the halves of
`leaf`, its windows (when read) those of `q < 2^(pd + cd)`, returns nothing and opens. -/
def WalkSound (walk : String) (pd cd : ℕ) : Prop :=
  ∀ (rd : Reader) (n0 n1 wins cap flags : E) (rets : List E),
    coreProgram.Rel rd walk [n0, n1, wins, cap, flags] rets →
    ∀ (leaf : Digest) (q : ℕ), (n0, n1) = digestHalves leaf → q < 2 ^ (pd + cd) →
      (∀ i v, LoadHolds rd wins i v → i < qwN (pd + cd) cd → v = gen ^ qwVal (pd + cd) cd q i) →
      rets = [] ∧ WalkOpens rd pd cd wins cap flags q leaf

theorem wpBodyT_eq (s : Oq) :
    wpBodyT s = (oqPathT s (.n 2) (wpPr s) 0 wpCh ++ oqCapT s (.n 2) (.n 3) (.n 4) 0 wpCh) ++
      [.ret []] := by
  simp [wpBodyT]

/-- **A frame of a walk** (a valuation `τ` taking the parameters to the arguments and holding the
body `wpBodyT s`, calls in any `C`): on the halves of `leaf`, its windows (when read) those of
`q < 2^(pd + cd)`, it returns nothing, reads the windows, its children cells off the walk's side
hold siblings, and the cap leaf and the flag are written. -/
theorem wp_frame_sound {s : Oq} (hpd : 1 ≤ s.pd) (hcd : 1 ≤ s.cd) {C : CallRel} {τ : Val}
    {n0 n1 wins cap flags : E} {rets : List E}
    (hpar : [V.n 0, .n 1, .n 2, .n 3, .n 4].map τ = [n0, n1, wins, cap, flags])
    (h : Stmt.HoldsList C rd τ (wpBodyT s) False (fun rs ↦ rs = rets))
    {leaf : Digest} {q : ℕ} (hleaf : (n0, n1) = digestHalves leaf) (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i v, LoadHolds rd wins i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i) :
    rets = [] ∧ (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd wins i (gen ^ qwVal (s.pd + s.cd) s.cd q i)) ∧
      ∃ sibs : List Digest, sibs.length = s.pd ∧ (∀ l < s.pd, SibAt τ wpCh q l (sibs.getD l default)) ∧
        LoadHolds rd flags (2 ^ (s.cd - 1) + q / 2 ^ (s.pd + 1)) 1 ∧
        LoadHolds rd cap (2 * (2 ^ s.cd + q / 2 ^ s.pd)) (digestHalves (climbD leaf q sibs)).1 ∧
        LoadHolds rd cap (2 * (2 ^ s.cd + q / 2 ^ s.pd) + 1) (digestHalves (climbD leaf q sibs)).2 := by
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hpar
  rw [wpBodyT_eq, holdsList_append, holdsList_flat (flat_append (oqPathT_flat _ _ _ _ _)
    (flat_of_atoms (oqCapT_atoms _ _ _ _ _ _)))] at h
  obtain ⟨hA, hret⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at hret
  have hPa : BlockOk rd τ (oqPathT s (.n 2) (wpPr s) 0 wpCh) :=
    BlockOk.mono hA fun x hx ↦ List.mem_append_left _ hx
  have hC : ∀ a, Stmt.atom a ∈ oqCapT s (.n 2) (.n 3) (.n 4) 0 wpCh → a.Holds rd τ :=
    fun a ha ↦ BlockOk.atom hA (List.mem_append_right _ ha)
  obtain ⟨hpad, hz⟩ := oqPath_pad hpd hPa
  obtain ⟨sibs, hsl, hsib, hnd⟩ := oqPath_sound hPa hpad hz (q := q) (fun i hi ↦
    ⟨_, (qwVal_path hi q).1, hwin _ _ (hPa.atom (oqPathT_mem_load hi)) (by rw [qwN_eq]; omega),
      (qwVal_path hi q).2⟩) (by simpa [oqNd] using hleaf)
  obtain ⟨hflag, hc0, hc1⟩ := oqCap_sound hcd hC hq hwin
  rw [show τ (.n (oqNd s 0 wpCh (oqNpw s) 0)) = (digestHalves (climbD leaf q sibs)).1 by
    rw [← hnd]] at hc0
  rw [show τ (.n (oqNd s 0 wpCh (oqNpw s) 1)) = (digestHalves (climbD leaf q sibs)).2 by
    rw [← hnd]] at hc1
  refine ⟨hret.symm, fun i hi ↦ ?_, sibs, hsl, hsib, hflag, hc0, hc1⟩
  obtain ⟨v, hv⟩ := oqWalk_winLoads hPa hC i hi
  rw [← hwin i v hv hi]
  exact hv

/-- **`walk` is `walk_path__L{pd}_L{cd}`**: a function of five parameters whose body is the
template. -/
def WalkFn (walk : String) (pd cd : ℕ) : Prop :=
  ∃ fn : Fn, coreProgram.find? walk = some fn ∧ fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧
    fn.body = wpBodyT ⟨0, 0, pd, cd⟩

/-- **A `walk_path` specialization is a sound walk.** -/
theorem WalkFn.sound {walk : String} {pd cd : ℕ} (hpd : 1 ≤ pd) (hcd : 1 ≤ cd)
    (hW : WalkFn walk pd cd) : WalkSound walk pd cd := by
  intro rd n0 n1 wins cap flags rets h leaf q hleaf hq hwin
  obtain ⟨fn, hf, hp, hb⟩ := hW
  rw [rel_iff_sem hf, hb, hp] at h
  obtain ⟨τ, hpar, h⟩ := h
  obtain ⟨hr, hl, sibs, hsl, -, hfl, h0, h1⟩ :=
    wp_frame_sound (s := ⟨0, 0, pd, cd⟩) hpd hcd hpar h hleaf hq hwin
  exact ⟨hr, hl, sibs, hsl, hfl, h0, h1⟩

end
end LeanVM.Guest.B1
