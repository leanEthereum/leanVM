/-
  LeanVM.Guest.B1.Bits.GrindPlaced

  `grind_check__L{bits}`, placed and bounded: complete at every frame pointer on every memory
  defined below `2^κ`, `11 ≤ κ`, where the caller's words hold the window tables and the word
  passes the proof of work, by a tree of its frame.
-/

module

public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Memory.Size

/-!
# `grind_check`, placed

`grindPre bits`: what a call asks (S5's `aggGrindPre` at `bits = 2`): nothing returned, the
window tables at the second argument, the first argument's low limb's `bits` low bits zero.

`grind_relAtIn`: a leaf (`gcBodyT`, `gcBodyT_split`), placed at `fp` by the honest valuation
(`gc_complete_of`, its range checks on the memory below `2^11`, `rc_complete_low`), its frame
alone. Its loads are the table reads `tabs·g^e`, `e < 2^11`, which lie in the caller's words: a
word that every memory holding them holds at a fixed address is one of theirs
(`forced_load_region`), and `grindPre` fixes the tables on every such memory.

`grind_check_completeB` (bound `fs name`), `grind_check_completeB_of` (any bound a `TotalLe`
gives), `grind_check_completeD`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- What `grind_check__L{bits}`'s completeness asks of its call: nothing returned, the window
tables at its second argument, and its first argument's low limb passing the proof of work. -/
def grindPre (bits : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  rets = [] ∧ ∃ w tabs, args = [w, tabs] ∧ WinTabs rd tabs ∧ (w.limb 0).lane.toNat % 2 ^ bits = 0

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

/-! ## The body -/

/-- The tail's statements before its `ret`. -/
def gcTailPre (b : ℕ) : List Stmt :=
  [.atom (.const (.n (10 * gcW b + 9)) (word (2 ^ b) 0)),
    .atom (.mul (.n (10 * gcW b + 10)) (.n (10 * gcW b + 8)) (.n (10 * gcW b + 9))),
    .atom (.add (.n (10 * gcW b + 11)) (.n 0) (.n (10 * gcW b + 10))),
    .atom (.const (.n (10 * gcW b + 12)) (word 2 1)),
    .atom (.mul (.n (10 * gcW b + 13)) (.n (10 * gcW b + 11)) (.n (10 * gcW b + 12))),
    .atom (.const (.n (10 * gcW b + 14)) (word (2 ^ b) 0)),
    .atom (.mul (.n (10 * gcW b + 15)) (.n (10 * gcW b + 8)) (.n (10 * gcW b + 14))),
    .atom (.assertInK (.n (10 * gcW b + 13)) (.n (10 * gcW b + 15)))]

/-- `grind_check__L{b}`'s statements before its `ret`. -/
def gcPre (b : ℕ) : List Stmt :=
  gcHead b ++ ((List.range (gcW b)).map fun i => gcIterAt (gcW b) (i + 1)).flatten ++ gcTailPre b

theorem gcBodyT_split (b : ℕ) : gcBodyT b = gcPre b ++ [.ret []] := by
  rw [gcBodyT, gcPre, List.append_assoc, List.append_assoc]
  rfl

/-- The statements before the `ret` are atoms placing nothing; the loads are the table reads. -/
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

theorem gcW_pos : ∀ b ∈ grindBitsDeployed, 1 ≤ gcW b := by decide

/-- The deployed `grind_check`s are no loop helpers. -/
theorem gc_not_loop {b : ℕ} {fn : Fn} (hf : coreProgram.find? (grindCheckName b) = some fn)
    (hbody : fn.body = gcBodyT b) : coreProgram.loop (grindCheckName b) = false := by
  rw [Program.loop_of_find? hf, Fn.loop, hbody, gcBodyT, gcTail]
  simp

/-! ## Placed -/

/-- **`grind_check__L{bits}` at `fp`**: on every memory defined below `2^κ`, `11 ≤ κ`, holding
the caller's words, on which `grindPre` holds wherever they are held, its tree of `fs name`
words holds, loading from the caller's words. -/
theorem grind_relAtIn {bits : ℕ} (hb : bits ∈ grindBitsDeployed) {κ : ℕ} (hκ : 11 ≤ κ)
    {args rets : List E} {Lin : Main.Layout}
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → grindPre bits rd args rets) (fp : ℕ) {rd : Reader}
    (hlow : LowDef κ rd) (hLin : MemL rd Lin) :
    RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL []) fp (fs (grindCheckName bits))
      (grindCheckName bits) args rets := by
  obtain ⟨fn, hf, hpar, hbody⟩ := grind_check_found bits hb
  have hl := gc_not_loop hf hbody
  obtain ⟨rfl, w, tabs, rfl, ht, hpow⟩ := hpre rd hlow hLin
  have hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2 := by
    intro v hv e he
    obtain ⟨a, b, c⟩ := rc_complete_low hlow (K := 2 ^ v)
      (Nat.pow_le_pow_right (by decide) (by omega)) he
    refine ⟨_, _, _, by rw [gen_pow_eq_ofK]; exact a, ?_, c⟩
    rw [wBound_eq hv, gen_pow_eq_ofK, gen_pow_eq_ofK]
    exact b
  obtain ⟨hh, hi, htl⟩ := gc_complete_of hrc (gc_shape bits hb) (gcW_pos bits hb) ht hpow
  set σ : Val := fun v => gcVals rd bits w tabs v.idx with hσ
  have hH : Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) := by
    rw [hbody, holds_gcBodyT]
    exact ⟨hh, hi, htl, rfl⟩
  have hsat := walk_sat (P := coreProgram) _
    (coreProgram_wf _ (List.mem_of_find?_eq_some hf)) hH
  have hw : walk σ fn.body = .ret ((gcPre bits).flatMap (Main.slEvs σ)) [] := by
    rw [hbody, gcBodyT_split, Main.walk_straight σ _ _ (gcPre_straight bits)]
  rw [hw] at hsat
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ _ (gcPre_straight bits)
  have ha : (gcPre bits).filterMap Main.Stmt.allocSz = [] :=
    List.filterMap_eq_nil_iff.mpr fun _ hs => (gcPre_mem hs).2.1
  have hd : (gcPre bits).filterMap Main.Stmt.addrS = [] :=
    List.filterMap_eq_nil_iff.mpr fun _ hs => (gcPre_mem hs).2.2.1
  have hc : (gcPre bits).filterMap Main.Stmt.callS = [] :=
    List.filterMap_eq_nil_iff.mpr fun _ hs => (gcPre_mem hs).2.2.2.1
  rw [ha] at i1 i2
  rw [hd] at i3
  rw [hc] at i4
  -- a table read `tabs·g^e`, `e < 2^11`, lies in the caller's words
  have htab : ∀ e < 2 ^ 11, ∃ i, (tabs * gen ^ e).limb 0 * addressOfIndex 0 = addressOfIndex i ∧
      RegionL Lin i := fun e he =>
    forced_load_region hlow hLin fun rd' hl' hL' => by
      obtain ⟨-, w', tabs', he', ht', -⟩ := hpre rd' hl' hL'
      simp only [List.cons.injEq, and_true] at he'
      rw [he'.2]
      exact winTab_load ht' he
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp) coreProgram_wf hf (Or.inl hl)
    (args := [w, tabs]) (rets := []) (by
      rw [hpar]
      show [gcVals rd bits w tabs 0, gcVals rd bits w tabs 1] = [w, tabs]
      unfold gcVals
      simp) hw rfl (fun e he => (hsat.1 e he).1) (by rw [i1, i2]; rfl) (by rw [i3]; simp)
    (by rw [i4]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [i2] at h
    simpa using h
  rw [loadAddrs_straight σ _ (gcPre_straight bits)] at hA
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
  obtain ⟨s, hs, hsq⟩ := List.mem_filterMap.mp hq
  rcases (gcPre_mem hs).2.2.2.2 with h0 | h0 | ⟨i, hi', h0⟩
  · rw [h0] at hsq; cases hsq
  · rw [h0, Option.some.injEq] at hsq
    subst hsq
    have hV0 : gcV bits w 0 < 2 ^ 11 := by
      obtain ⟨-, hT, hsum⟩ := gc_shape bits hb
      refine lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by decide) hT)
      unfold gcV
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_zero,
        show gcTop bits + (bits + 11 * gcW bits) = 64 by omega]
      exact kToNat_lt _
    have e7 : σ (.n (gcW bits + 7)) = tabs * gen ^ gcV bits w 0 := by
      show gcVals rd bits w tabs (gcW bits + 7) = _
      unfold gcVals
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    obtain ⟨j, hj, hr⟩ := htab _ hV0
    exact ⟨j, by rw [e7]; exact hj, Or.inr (Or.inl hr)⟩
  · rw [h0, Option.some.injEq] at hsq
    subst hsq
    have e6 : σ (.n (gcW bits + 9 * (i + 1) + 6)) = tabs * gen ^ (gcV bits w (i + 1) % 2 ^ 11) :=
      gv_iter (by omega) (by omega) (by omega)
    obtain ⟨j, hj, hr⟩ := htab _ (Nat.mod_lt _ (by positivity))
    exact ⟨j, by rw [e6]; exact hj, Or.inr (Or.inl hr)⟩

/-- **`grind_check__L{bits}`, placed and bounded by its frame.** -/
theorem grind_check_completeB {bits : ℕ} (hb : bits ∈ grindBitsDeployed) {κ : ℕ}
    (hκ : 11 ≤ κ) :
    CompleteRelB fs cert κ (grindCheckName bits) (grindPre bits) (fs (grindCheckName bits)) :=
  fun _ rets _ hpre fp => ⟨fs (grindCheckName bits), [], rets, [], ⟨rfl, rfl⟩, by simp [Within],
    disj_nil, le_rfl, fun _ hl hL => grind_relAtIn hb hκ hpre fp hl (by simpa using hL)⟩

/-- **`grind_check__L{bits}`, placed, within any bound on its valid trees.** -/
theorem grind_check_completeB_of {bits : ℕ} (hb : bits ∈ grindBitsDeployed) {κ : ℕ}
    (hκ : 11 ≤ κ) {B : ℕ} (hT : TotalLe coreProgram fs (grindCheckName bits) fun _ => B) :
    CompleteRelB fs cert κ (grindCheckName bits) (grindPre bits) B := by
  intro args rets Lin hpre fp
  by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd Lin
  · obtain ⟨rd0, h0, hL0⟩ := hex
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := grind_relAtIn (fs := fs) (cert := cert) hb hκ hpre fp h0 hL0
    refine ⟨fs (grindCheckName bits), [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      ht ▸ hT rd0 t _ _ hn hv hbo, fun _ hl hL => grind_relAtIn hb hκ hpre fp hl (by simpa using hL)⟩
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- **`grind_check__L{bits}`, placed.** -/
theorem grind_check_completeD {bits : ℕ} (hb : bits ∈ grindBitsDeployed) {κ : ℕ} (hκ : 11 ≤ κ) :
    CompleteRelD fs cert κ (grindCheckName bits) (grindPre bits) :=
  (grind_check_completeB hb hκ).toCompleteRelD

end
end LeanVM.Guest.B1
