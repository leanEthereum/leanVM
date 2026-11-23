/-
  LeanVM.Guest.B1.Bits.GrindPlaced

  `grind_check`'s expansion, placed: its atoms, its loads (the table reads, in the caller's
  words) and its exactness under the honest valuation.
-/

module

public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Bits.GrindFwd
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.Memory.PopsNil
public import LeanVM.Guest.B1.Main.RelAtInE
public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Budget.Bounded

/-!
# `grind_check`, placed

`gcPre_mem`: the expansion's statements are atoms placing nothing, and its loads are the table
reads. Those lie in the caller's words: a word that every memory holding them holds at a fixed
address is one of theirs (`forced_load_region`). `gcPre_atom`: every atom pops nothing and is exact
under the honest valuation (`gcVals`), its windows the executor's windows of the word's low limb
(`wordNat_window`). The callers' placed proofs (`bus_grind_check`'s, `BusGrindPlaced.lean`) build
on these.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen kToNat)
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Forced words lie in the caller's -/

/-- **A word every memory holding the caller's words reads lies among them**: if every memory
defined below `2^κ` and holding `Lin` reads `v` through `p` at `off`, and one such memory exists,
the address is one of `Lin`'s. -/
theorem forced_load_region {κ : ℕ} {Lin : Main.Layout} {p : E} {off : ℕ} {v : E} {rd0 : Reader}
    (h0 : LowDef κ rd0) (hL0 : MemL rd0 Lin)
    (h : ∀ rd, LowDef κ rd → MemL rd Lin → LoadHolds rd p off v) :
    ∃ i, p.limb 0 * addressOfIndex off = addressOfIndex i ∧ RegionL Lin i := by
  classical
  by_contra hn
  let rd : Reader := fun a => if a = p.limb 0 * addressOfIndex off then some (v + 1) else rd0 a
  have hlow : LowDef κ rd := fun i hi => by
    by_cases hA : addressOfIndex i = p.limb 0 * addressOfIndex off
    · simp [rd, hA]
    · simp only [rd, hA, ↓reduceIte]; exact h0 i hi
  have hL : MemL rd Lin := fun q hq k hk => by
    obtain ⟨hk1, hk2⟩ := hL0 q hq k hk
    refine ⟨hk1, ?_⟩
    have hne : (ofK (addressOfIndex q.1)).limb 0 * addressOfIndex k ≠
        p.limb 0 * addressOfIndex off := by
      rw [Main.addr_ofK]
      intro he
      exact hn ⟨q.1 + k, he.symm, q, hq, by omega, by omega⟩
    simp only [rd, hne, ↓reduceIte]; exact hk2
  have h1 := (h rd hlow hL).2
  simp only [rd, ↓reduceIte, Option.some.injEq] at h1
  exact one_ne_zero (add_eq_left.mp h1)

/-- **The windows' range checks pass** on every memory defined below `2^κ`, `11 ≤ κ`. -/
theorem gcRc_of_lowDef {κ : ℕ} (hκ : 11 ≤ κ) {rd : Reader} (hlow : LowDef κ rd) :
    ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2 := by
  intro v hv e he
  obtain ⟨a, b, c⟩ := rc_complete_low hlow (K := 2 ^ v)
    (Nat.pow_le_pow_right (by decide) (by omega)) he
  refine ⟨_, _, _, by rw [gen_pow_eq_ofK]; exact a, ?_, c⟩
  rw [wBound_eq hv, gen_pow_eq_ofK, gen_pow_eq_ofK]
  exact b

/-! ## The body -/

/-- The expansion's statements are atoms placing nothing; the loads are the table reads. -/
theorem gcPre_mem {b : ℕ} {s : Stmt} (hs : s ∈ gcPre b) :
    Main.Stmt.straight s = true ∧ Main.Stmt.allocSz s = none ∧ Main.Stmt.addrS s = none ∧
      Main.Stmt.callS s = none ∧
      (Stmt.loadS s = none ∨ Stmt.loadS s = some (.n (gcW b + 7), 0) ∨
        ∃ i < gcW b, Stmt.loadS s = some (.n (gcW b + 9 * (i + 1) + 6), 0)) := by
  simp only [gcPre, gcHead, gcTailPre, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_range] at hs
  rcases hs with (hs | ⟨l, ⟨i, hi, rfl⟩, hs⟩) | hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Main.Stmt.straight, Main.Stmt.allocSz, Main.Stmt.addrS, Main.Stmt.callS, Stmt.loadS]
  · simp only [gcIterAt, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Main.Stmt.straight, Main.Stmt.allocSz, Main.Stmt.addrS, Main.Stmt.callS,
        Stmt.loadS, true_and, reduceCtorEq, false_or, true_or]
    exact Or.inr ⟨i, hi, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Main.Stmt.straight, Main.Stmt.allocSz, Main.Stmt.addrS, Main.Stmt.callS, Stmt.loadS]

theorem gcPre_straight (b : ℕ) : (gcPre b).all Main.Stmt.straight = true :=
  List.all_eq_true.mpr fun _ hs => (gcPre_mem hs).1

/-! ## Exact -/

/-- **A window of a word within its low limb** is the low limb's. -/
theorem wordNat_window (w : E) {s n : ℕ} (h : s + n ≤ 64) :
    (LeanVM.Prover.Exec.wordNat w >>> s) % 2 ^ n = kToNat (w.limb 0) / 2 ^ s % 2 ^ n := by
  have e : LeanVM.Prover.Exec.wordNat w = kToNat (w.limb 0) + 2 ^ s * (2 ^ n * (2 ^ (64 - s - n) *
      kToNat (w.limb 1))) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add,
      show s + n + (64 - s - n) = 64 by omega]
    rfl
  rw [e, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

/-- **Every statement of `grind_check`'s expansion is an atom popping nothing and exact** under the
honest valuation: its two hints are the word's windows. -/
theorem gcPre_atom {rd : Reader} {b : ℕ} {w tabs : E}
    (hs : 1 ≤ gcTop b ∧ gcTop b ≤ 11 ∧ b + 11 * gcW b + gcTop b = 64) {s : Stmt} (hs' : s ∈ gcPre b) :
    ∃ a, s = .atom a ∧ atomNoWit a = true ∧ a.Exact rd (fun v => gcVals rd b w tabs v.idx) := by
  obtain ⟨hT1, hT, hsum⟩ := hs
  simp only [gcPre, gcHead, gcTailPre, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_range] at hs'
  rcases hs' with (hs' | ⟨l, ⟨i, hi, rfl⟩, hs'⟩) | hs'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨_, rfl, rfl, ?_⟩
      show ((List.range (gcW b)).map fun j => V.n (2 + j)).map (fun v => gcVals rd b w tabs v.idx) = _
      rw [List.map_map]
      refine List.map_congr_left fun j hj => ?_
      have hj : j < gcW b := List.mem_range.mp hj
      have e2 : 2 + j = gcW b + 2 - (gcW b - j) := by omega
      show gcVals rd b w tabs (2 + j) = ofK (g ^ ((LeanVM.Prover.Exec.wordNat (gcVals rd b w tabs 0) >>>
        (b + j * 11)) % 2 ^ 11))
      rw [e2, gv_win (by omega) (show gcW b - j ≤ gcW b by omega), show gcVals rd b w tabs 0 = w from rfl,
        wordNat_window w (by omega), gen_pow_eq_ofK, gcV, show gcW b - (gcW b - j) = j by omega,
        Nat.mul_comm 11 j]
    · refine ⟨_, rfl, rfl, ?_⟩
      show [gcVals rd b w tabs (gcW b + 2)] = (List.range 1).map fun i => ofK (g ^ ((LeanVM.Prover.Exec.wordNat
        (gcVals rd b w tabs 0) >>> (b + 11 * gcW b + i * gcTop b)) % 2 ^ gcTop b))
      have hv : kToNat (w.limb 0) / 2 ^ (b + 11 * gcW b) < 2 ^ gcTop b := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, show gcTop b + (b + 11 * gcW b) = 64 by omega]
        exact kToNat_lt _
      have e : gcVals rd b w tabs (gcW b + 2) = gen ^ gcV b w 0 := by
        unfold gcVals
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      simp only [List.range_one, List.map_cons, List.map_nil, Nat.zero_mul, Nat.add_zero]
      rw [e, show gcVals rd b w tabs 0 = w from rfl, wordNat_window w (by omega), Nat.mod_eq_of_lt hv,
        gen_pow_eq_ofK, gcV, Nat.sub_zero]
    all_goals exact ⟨_, rfl, rfl, trivial⟩
  · simp only [gcIterAt, List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl, trivial⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl, trivial⟩

/-! ## Inlined, evaluated: exact -/

theorem gc_mem_renameList_inv {r : V → V} : ∀ {ss : List Stmt} {s : Stmt}, s ∈ Stmt.renameList r ss →
    ∃ s0 ∈ ss, s0.rename r = s
  | [], _, h => absurd h (by simp [Stmt.renameList])
  | t :: ss, s, h => by
    simp only [Stmt.renameList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨t, List.mem_cons_self, rfl⟩
    · obtain ⟨s0, hs0, e⟩ := gc_mem_renameList_inv h
      exact ⟨s0, List.mem_cons_of_mem _ hs0, e⟩

/-- **`grind_check` inlined, evaluated, is exact**: on the caller's evaluated valuation (as in
`gcInline_vals_of_good`), every atom of the expansion is exact, its two hints the word's windows. -/
theorem gcInline_exact_of_good {rd : Reader} {S : List Atom} {wo : ℕ → E} {σ : Val} {b o : ℕ}
    (hb : b ∈ grindBitsDeployed) {w tabs : V} (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineT b o w tabs, Fwd.GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs)) (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j) :
    ∀ a, Stmt.atom a ∈ gcInlineT b o w tabs → a.Exact rd σ := by
  have hv := gcInline_vals_of_good hb hwo hto hg hS hrc ht hwin
  intro a ha
  rw [gcInlineT] at ha
  obtain ⟨s0, hs0, e0⟩ := gc_mem_renameList_inv ha
  obtain ⟨a0, rfl, -, hex⟩ := gcPre_atom (rd := rd) (w := σ w) (tabs := σ tabs) (gc_shape b hb) hs0
  simp only [Stmt.rename, Stmt.atom.injEq] at e0
  subst e0
  -- the values the expansion's hints write
  have hR : ∀ k, 2 ≤ k → k < gcLen b → σ (gcRen o w tabs (.n k)) = gcVals rd b (σ w) (σ tabs) k :=
    fun k h2 hk ↦ by rw [gcRen_own o w tabs h2]; exact hv k h2 hk
  have hW := gcW_pos b hb
  simp only [gcPre, gcHead, gcTailPre, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_range] at hs0
  rcases hs0 with (hs0 | ⟨l, ⟨i, hi, rfl⟩, hs0⟩) | hs0
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl
    · show (((List.range (gcW b)).map fun j => V.n (2 + j)).map (gcRen o w tabs)).map σ = _
      have e : ((List.range (gcW b)).map fun j => V.n (2 + j)).map
          (fun v => gcVals rd b (σ w) (σ tabs) v.idx) = _ := hex
      have e0 : σ (gcRen o w tabs (V.n 0)) = (fun v : V => gcVals rd b (σ w) (σ tabs) v.idx) (V.n 0) :=
        rfl
      rw [e0, ← e]
      simp only [List.map_map]
      refine List.map_congr_left fun j hj ↦ ?_
      have hj := List.mem_range.mp hj
      exact hR (2 + j) (by omega) (by unfold gcLen; omega)
    · show ((([V.n (gcW b + 2)]).map (gcRen o w tabs))).map σ = _
      have e : ([V.n (gcW b + 2)]).map (fun v => gcVals rd b (σ w) (σ tabs) v.idx) = _ := hex
      have e0 : σ (gcRen o w tabs (V.n 0)) = (fun v : V => gcVals rd b (σ w) (σ tabs) v.idx) (V.n 0) :=
        rfl
      rw [e0, ← e, List.map_map]
      simp only [List.map_cons, List.map_nil, Function.comp_apply,
        hR (gcW b + 2) (by omega) (by unfold gcLen; omega)]
    all_goals trivial
  · simp only [gcIterAt, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

end
end LeanVM.Guest.B1
