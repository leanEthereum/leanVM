/-
  LeanVM.Guest.B1.Bits.BusGrindPlaced

  `bus_grind_check__L{d}`, placed and bounded: complete at every frame pointer on every memory
  defined below `2^κ`, `11 ≤ κ`, where the caller's words hold the window tables and the word
  passes the proof of work, by a tree of its frame.
-/

module

public import LeanVM.Guest.B1.Bits.BusGrind
public import LeanVM.Guest.B1.Bits.GrindPlaced
public import LeanVM.Guest.B1.Tables.FlatAtT

/-!
# `bus_grind_check`, placed

`busGrindPre d`: what a call asks, `0` returned, the window tables at its second argument, its
first argument's low limb passing the proof of work.

`bus_grind_relAtInE`: a leaf (`bgBody`, `grind_check` inlined then `0`), placed at `fp` by the
honest valuation (`gcVals`, its range checks on the memory below `2^11`, `rc_complete_low`), its
frame alone, every node exact (`gcPre_atom`). Its loads are the table reads `tabs·g^e`, `e < 2^11`,
which lie in the caller's words (`forced_load_region`).

`bus_grind_check_completeB`: within its frame.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen kToNat)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- What `bus_grind_check__L{d}`'s completeness asks of its call: `0` returned, the window tables
at its second argument, and its first argument's low limb passing the proof of work. -/
def busGrindPre (d : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  rets = [0] ∧ ∃ w tabs, args = [w, tabs] ∧ WinTabs rd tabs ∧
    (w.limb 0).lane.toNat % 2 ^ busGrindBits d = 0

theorem bgPre_mem {d : ℕ} {s : Stmt} (hs : s ∈ bgPre d) :
    s ∈ gcPre (busGrindBits d) ∨ s = .atom (.const (.n (bgZero d)) (word 0 0)) := by
  simpa [bgPre] using hs

theorem bgPre_straight (d : ℕ) : (bgPre d).all Main.Stmt.straight = true :=
  List.all_eq_true.mpr fun s hs => by
    rcases bgPre_mem hs with h | rfl
    · exact (gcPre_mem h).1
    · rfl

/-- **`bus_grind_check__L{d}` at `fp`**: on every memory defined below `2^κ`, `11 ≤ κ`, holding the
caller's words, on which `busGrindPre` holds wherever they are held, its tree of `fs name` words
holds, loading from the caller's words, every node exact. -/
theorem bus_grind_relAtInE {d : ℕ} (hd : d ∈ busGrindDeployed) {κ : ℕ} (hκ : 11 ≤ κ)
    {args rets : List E} {Lin : Layout}
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → busGrindPre d rd args rets) (fp : ℕ) {rd : Reader}
    (hlow : LowDef κ rd) (hLin : MemL rd Lin) :
    RelAtInPE coreProgram fs cert rd (ExactAt coreProgram rd) (RegionL Lin) (RegionL []) fp
      (fs (busGrindName d)) (busGrindName d) args rets [] := by
  obtain ⟨fn, hf, hpar, hbody⟩ := bus_grind_check_found d hd
  have hb := busGrindBits_mem d hd
  obtain ⟨rfl, w, tabs, rfl, ht, hpow⟩ := hpre rd hlow hLin
  have hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2 := by
    intro v hv e he
    obtain ⟨a, b, c⟩ := rc_complete_low hlow (K := 2 ^ v)
      (Nat.pow_le_pow_right (by decide) (by omega)) he
    refine ⟨_, _, _, by rw [gen_pow_eq_ofK]; exact a, ?_, c⟩
    rw [wBound_eq hv, gen_pow_eq_ofK, gen_pow_eq_ofK]
    exact b
  set bits := busGrindBits d with hbits
  set σ : Val := fun v => gcVals rd bits w tabs v.idx with hσ
  have hz : σ (.n (bgZero d)) = 0 := gcVals_len
  have hH : Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = [0]) := by
    rw [hbody, bgBody, bgPre, List.append_assoc, holdsList_append]
    refine gcPre_complete_of hrc hb ht hpow (fun k _ => rfl) ?_
    simp only [List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil]
    exact ⟨by rw [hz, word_zero], by rw [hz]⟩
  have hsat := walk_sat (P := coreProgram) _
    (coreProgram_wf _ (List.mem_of_find?_eq_some hf)) hH
  have hw : walk σ fn.body = .ret ((bgPre d).flatMap (Main.slEvs σ)) [.n (bgZero d)] := by
    rw [hbody, bgBody, Main.walk_straight σ _ _ (bgPre_straight d)]
  rw [hw] at hsat
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ _ (bgPre_straight d)
  have ha : (bgPre d).filterMap Main.Stmt.allocSz = [] :=
    List.filterMap_eq_nil_iff.mpr fun s hs => by
      rcases bgPre_mem hs with h | rfl
      · exact (gcPre_mem h).2.1
      · rfl
  have hdd : (bgPre d).filterMap Main.Stmt.addrS = [] :=
    List.filterMap_eq_nil_iff.mpr fun s hs => by
      rcases bgPre_mem hs with h | rfl
      · exact (gcPre_mem h).2.2.1
      · rfl
  have hc : (bgPre d).filterMap Main.Stmt.callS = [] :=
    List.filterMap_eq_nil_iff.mpr fun s hs => by
      rcases bgPre_mem hs with h | rfl
      · exact (gcPre_mem h).2.2.2.1
      · rfl
  rw [ha] at i1 i2
  rw [hdd] at i3
  rw [hc] at i4
  -- a table read `tabs·g^e`, `e < 2^11`, lies in the caller's words
  have htab : ∀ e < 2 ^ 11, ∃ i, (tabs * gen ^ e).limb 0 * addressOfIndex 0 = addressOfIndex i ∧
      RegionL Lin i := fun e he =>
    forced_load_region hlow hLin fun rd' hl' hL' => by
      obtain ⟨-, w', tabs', he', ht', -⟩ := hpre rd' hl' hL'
      simp only [List.cons.injEq, and_true] at he'
      rw [he'.2]
      exact winTab_load ht' he
  have hev : ∀ e ∈ (bgPre d).flatMap (Main.slEvs σ), ∃ a, e = .atom a ∧ atomNoWit a = true ∧
      a.Exact rd σ := fun e he => by
    obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
    rcases bgPre_mem hs with hs | rfl
    · obtain ⟨a, rfl, h1, h2⟩ := gcPre_atom (rd := rd) (w := w) (tabs := tabs) (gc_shape bits hb) hs
      simp only [Main.slEvs, List.mem_singleton] at he
      exact ⟨a, he, h1, h2⟩
    · simp only [Main.slEvs, List.mem_singleton] at he
      exact ⟨_, he, rfl, trivial⟩
  have h := relAtInPE_of_walk (P := coreProgram) (fs := fs) (cert := cert) (Q := ExactAt coreProgram rd)
    (R := RegionL Lin) (pss := []) (ps := [])
    (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp) coreProgram_wf hf
    (Or.inr (by rw [i4]; rfl))
    (args := [w, tabs]) (rets := [0]) (by
      rw [hpar]
      simp only [List.map_cons, List.map_nil, hσ]
      unfold gcVals
      simp) hw (by show [σ (.n (bgZero d))] = [0]; rw [hz]) (fun e he => (hsat.1 e he).1)
    (by rw [i1, i2]; rfl) (by rw [i3]; simp)
    (by rw [i4]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    (splice_nil_of _ _ (fun e he => by obtain ⟨a, rfl, h1, -⟩ := hev e he; exact h1) (by simp))
    (exactAt_of_walk hf hw fun e he => by obtain ⟨a, rfl, -, h2⟩ := hev e he; exact h2)
  · rw [i2] at h
    simpa using h
  rw [loadAddrs_straight σ _ (bgPre_straight d)] at hA
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
  obtain ⟨s, hs, hsq⟩ := List.mem_filterMap.mp hq
  rcases bgPre_mem hs with hs | rfl
  swap
  · cases hsq
  rcases (gcPre_mem hs).2.2.2.2 with h0 | h0 | ⟨i, hi', h0⟩
  · rw [h0] at hsq; cases hsq
  · rw [h0, Option.some.injEq] at hsq
    subst hsq
    have hV0 : gcV bits w 0 < 2 ^ 11 := by
      obtain ⟨-, hT, hsum⟩ := gc_shape bits hb
      exact lt_of_lt_of_le (gcV_zero_lt hsum w) (Nat.pow_le_pow_right (by decide) hT)
    have e7 : σ (.n (gcW bits + 7)) = tabs * gen ^ gcV bits w 0 := gv_top_ptr
    obtain ⟨j, hj, hr⟩ := htab _ hV0
    exact ⟨j, by rw [e7]; exact hj, Or.inr (Or.inl hr)⟩
  · rw [h0, Option.some.injEq] at hsq
    subst hsq
    have e6 : σ (.n (gcW bits + 9 * (i + 1) + 6)) = tabs * gen ^ (gcV bits w (i + 1) % 2 ^ 11) :=
      gv_iter (by omega) (show i + 1 ≤ gcW bits from hi') (by omega)
    obtain ⟨j, hj, hr⟩ := htab _ (Nat.mod_lt _ (by positivity))
    exact ⟨j, by rw [e6]; exact hj, Or.inr (Or.inl hr)⟩

/-- **`bus_grind_check__L{d}` at `fp`** (`bus_grind_relAtInE` without its pops and exactness). -/
theorem bus_grind_relAtIn {d : ℕ} (hd : d ∈ busGrindDeployed) {κ : ℕ} (hκ : 11 ≤ κ)
    {args rets : List E} {Lin : Layout}
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → busGrindPre d rd args rets) (fp : ℕ) {rd : Reader}
    (hlow : LowDef κ rd) (hLin : MemL rd Lin) :
    RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL []) fp (fs (busGrindName d))
      (busGrindName d) args rets :=
  RelAtInT.relAtIn (bus_grind_relAtInE hd hκ hpre fp hlow hLin)

/-- **`bus_grind_check__L{d}`, placed, within its frame.** -/
theorem bus_grind_check_completeB {d : ℕ} (hd : d ∈ busGrindDeployed) {κ : ℕ} (hκ : 11 ≤ κ) :
    CompleteRelB fs cert κ (busGrindName d) (busGrindPre d) (fs (busGrindName d)) :=
  fun _ rets _ hpre fp => ⟨fs (busGrindName d), [], rets, [], ⟨rfl, rfl⟩, by simp [Within],
    disj_nil, le_rfl, fun _ hl hL => bus_grind_relAtIn hd hκ hpre fp hl (by simpa using hL)⟩


end
end LeanVM.Guest.B1
