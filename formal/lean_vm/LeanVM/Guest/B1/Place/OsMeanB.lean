/-
  LeanVM.Guest.B1.Place.OsMeanB

  open_stacked's named callees placed within their words bounds on f128.
-/

module

public import LeanVM.Guest.B1.Place.OsSpec
public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.Budget.LiftB
public import LeanVM.Guest.Budget.Bounded

/-!
# The named callees within their bounds

`OsLeafBounds fs Bnd` (`Place/OsSpec`): each named callee `f`'s valid trees total at most `Bnd f`
words. **`kindDB`**: a named callee is complete placed on its meaning and regions within that
bound: the leaves by `completeRelRegDB_of_iff`, `grind_check` by `grind_check_completeB_of`, and
`opening_round`, which calls `grind_check__L8`, as a pure function (`completeAtDTB_of_relIn`: it
and `grind_check__L8` place nothing, `round_pureIn`) from its relation loading only the caller's
words on every memory holding them (`round_relIn`, its grinds' by `grind_relIn`).
**`os_kid_namedB`**: a named call of a body proved at `osCR` on every memory holding `Lk` is
`CompleteAtB` on `Lk` within its bound.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (AllOk StmtOk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-! ## `grind_check`, loading the caller's words -/

/-- **`grind_check__L{bits}` loads only the caller's words**: on every memory defined below `2^κ`,
`11 ≤ κ`, holding them, on which `grindPre` holds wherever they are held, its relation holds by a
tree loading from them. -/
theorem grind_relIn {bits : ℕ} (hb : bits ∈ grindBitsDeployed) (hκ : 11 ≤ κ)
    {args rets : List E} {Lin : Layout}
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → grindPre bits rd args rets) {rd : Reader}
    (hlow : LowDef κ rd) (hLin : MemL rd Lin) :
    coreProgram.RelIn rd (RegionL Lin) (grindCheckName bits) args rets := by
  obtain ⟨fn, hf, hpar, hbody⟩ := grind_check_found bits hb
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
  obtain ⟨-, -, -, i4⟩ := Main.straight_parts σ _ (gcPre_straight bits)
  have hc : (gcPre bits).filterMap Main.Stmt.callS = [] :=
    List.filterMap_eq_nil_iff.mpr fun _ hs => (gcPre_mem hs).2.2.2.1
  rw [hc] at i4
  have htab : ∀ e < 2 ^ 11, ∃ i, (tabs * gen ^ e).limb 0 * addressOfIndex 0 = addressOfIndex i ∧
      RegionL Lin i := fun e he =>
    forced_load_region hlow hLin fun rd' hl' hL' => by
      obtain ⟨-, w', tabs', he', ht', -⟩ := hpre rd' hl' hL'
      simp only [List.cons.injEq, and_true] at he'
      rw [he'.2]
      exact winTab_load ht' he
  refine relIn_of_walk (P := coreProgram) coreProgram_wf hf (by
      rw [hpar]
      show [gcVals rd bits w tabs 0, gcVals rd bits w tabs 1] = [w, tabs]
      unfold gcVals
      simp) hw rfl (fun e he => (hsat.1 e he).1) (fun A hA => ?_) (fun c hc' _ => ?_)
  · rw [loadAddrs_straight σ _ (gcPre_straight bits)] at hA
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
      exact ⟨j, by rw [e7]; exact hj, hr⟩
    · rw [h0, Option.some.injEq] at hsq
      subst hsq
      have e6 : σ (.n (gcW bits + 9 * (i + 1) + 6)) = tabs * gen ^ (gcV bits w (i + 1) % 2 ^ 11) :=
        gv_iter (by omega) (by omega) (by omega)
      obtain ⟨j, hj, hr⟩ := htab _ (Nat.mod_lt _ (by positivity))
      exact ⟨j, by rw [e6]; exact hj, hr⟩
  · rw [i4] at hc'; simp at hc'

/-! ## `opening_round`, loading the caller's words -/

theorem calls_ok {C : CallRel} {rd : Reader} {σ : Val} {es : List Ev}
    (h : ∀ e ∈ es, e.Ok C rd σ) {c : Call} (hc : c ∈ calls es) (ht : c.taken = true) :
    C c.f (c.args.map σ) (c.rets.map σ) := by
  obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
  match e, hce with
  | .call f a r, hce =>
    simp only [Ev.call?, Option.some.injEq] at hce
    subst hce
    exact (h _ he).2 f a r rfl
  | .skip f a, hce =>
    simp only [Ev.call?, Option.some.injEq] at hce
    subst hce
    simp at ht

/-- **`opening_round` loads only the caller's words**, on every memory defined below `2^κ`,
`11 ≤ κ`, holding them, on which its meaning and the window tables hold wherever they are held. -/
theorem round_relIn (hκ : 11 ≤ κ) {args rets : List E} {Lin : Layout}
    (hreg : RegPtrs roundSpec args (RegionL Lin))
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin →
      Whir.MeaningOpeningRound rd args rets ∧ WinTabs rd (args.getD 7 0)) {rd : Reader}
    (hlow : LowDef κ rd) (hLin : MemL rd Lin) :
    coreProgram.RelIn rd (RegionL Lin) "opening_round" args rets := by
  have h9 : (8 : ℕ) ∈ grindBitsDeployed := by decide
  have hname : grindCheckName 8 = "grind_check__L8" := rfl
  obtain ⟨hm, -⟩ := hpre rd hlow hLin
  obtain ⟨xs, -, -, -, hpar, hh⟩ := Whir.round_complete
    (C := coreProgram.RelIn rd (RegionL Lin)) hm (fun w hw ↦ by
      have := grind_relIn (args := [w, args.getD 7 0]) (rets := []) h9 hκ
        (fun rd' hl' hL' ↦ ⟨rfl, w, args.getD 7 0, rfl, (hpre rd' hl' hL').2, hw⟩) hlow hLin
      rwa [hname] at this)
  set σ : Val := fun v ↦ Whir.rdVals args xs v.idx with hσ
  have hst : roundPre.all Main.Stmt.straight = true := straight_of_flat _ roundPre_flat
  have hbody := Whir.core7_body.trans roundBody_eq
  have hw := Main.walk_straight σ [.n 86, .n 87, .n 88, .n 89, .n 90, .n 93, .n 94] roundPre hst
  rw [← hbody] at hw
  rw [← Whir.core7_body] at hh
  have hsat := walk_sat (P := coreProgram) _
    (coreProgram_wf _ (List.mem_of_find?_eq_some Whir.find_opening_round)) hh
  rw [hw] at hsat
  have hv : ∀ j < 10, Whir.rdVals args xs j = args.getD j 0 := fun j hj ↦ by
    simp [Whir.rdVals, hj]
  refine relIn_of_walk (P := coreProgram) coreProgram_wf Whir.find_opening_round hpar hw hsat.2
    (fun e he ↦ (hsat.1 e he).1) (fun A hA ↦ ?_) (fun c hc ht ↦ calls_ok hsat.1 hc ht)
  rw [loadAddrs_straight σ _ hst, roundPre_loadsS] at hA
  have r5 := hreg (5, 5) (by simp [roundSpec])
  have r8 := hreg (8, 1) (by simp [roundSpec])
  have r9 := hreg (9, 2) (by simp [roundSpec])
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
  have e5 : σ (.n 5) = args.getD 5 0 := hv 5 (by decide)
  have e8 : σ (.n 8) = args.getD 8 0 := hv 8 (by decide)
  have e9 : σ (.n 9) = args.getD 9 0 := hv 9 (by decide)
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [e5, e8, e9]
  · obtain ⟨i, h, r⟩ := r5 0 (by decide); exact ⟨i, h, r⟩
  · obtain ⟨i, h, r⟩ := r5 1 (by decide); exact ⟨i, h, r⟩
  · obtain ⟨i, h, r⟩ := r5 2 (by decide); exact ⟨i, h, r⟩
  · obtain ⟨i, h, r⟩ := r5 3 (by decide); exact ⟨i, h, r⟩
  · obtain ⟨i, h, r⟩ := r5 4 (by decide); exact ⟨i, h, r⟩
  · obtain ⟨i, h, r⟩ := r8 0 (by decide); exact ⟨i, h, r⟩
  · obtain ⟨i, h, r⟩ := r9 0 (by decide); exact ⟨i, h, r⟩
  · obtain ⟨i, h, r⟩ := r9 1 (by decide); exact ⟨i, h, r⟩

theorem round_pure_body : Stmt.pureList ["opening_round", "grind_check__L8"] Whir.roundBody = true := by
  decide +kernel

theorem grind8_pure_body : Stmt.pureList ["opening_round", "grind_check__L8"] (gcBodyT 8) = true := by
  decide +kernel

/-- **`opening_round` and `grind_check__L8` place nothing.** -/
theorem round_pureIn : coreProgram.PureIn ["opening_round", "grind_check__L8"] := by
  intro g hg fn hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · rw [Whir.find_opening_round] at hf
    cases hf
    rw [Whir.core7_body]
    exact round_pure_body
  · obtain ⟨fn', hf', -, hb'⟩ := grind_check_found 8 (by decide)
    rw [show grindCheckName 8 = "grind_check__L8" from rfl, hf] at hf'
    cases hf'
    rw [hb']
    exact grind8_pure_body

/-! ## The named callees within their bounds -/

/-- **A named callee is complete placed on its meaning and regions, within its bound.** -/
theorem kindDB (hκ : 11 ≤ κ) {Bnd : String → ℕ} (hT : OsLeafBounds fs Bnd) {f : String}
    {K : OsKind} (hK : osKindOf f = some K) :
    CompleteRelRegDB fs cert κ f K.Pre (RegPtrs K.spec) (fun _ ↦ Bnd f) := by
  have hb := hT f K hK
  have he := osKindEntry_ok hK
  cases K with
  | round =>
    simp only [osKindEntryOk, beq_iff_eq] at he
    subst he
    intro args rets Lin hreg hpre
    exact completeAtDTB_of_relIn round_pureIn (List.mem_cons_self ..) (TotalLe.at hb args)
      fun rd hl hL ↦ round_relIn hκ hreg hpre hl hL
  | tail =>
    simp only [osKindEntryOk, beq_iff_eq] at he
    subst he
    exact completeRelRegDB_of_iff (leafSpecOk_of tail_leafSpec) opening_tail_round_holds κ hb
  | msg n nonce =>
    simp only [osKindEntryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
    obtain ⟨hm, rfl⟩ := he
    exact completeRelRegDB_of_iff (leafSpecOk_allP msg_leafSpec _ hm) (opening_message_holds _ hm)
      κ hb
  | spf n =>
    simp only [osKindEntryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
    obtain ⟨hm, rfl⟩ := he
    exact completeRelRegDB_of_iff (leafSpecOk_allP spf_leafSpec _ hm)
      (squeeze_point_from_holds _ hm) κ hb
  | grind b =>
    simp only [osKindEntryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
    obtain ⟨hm, rfl⟩ := he
    intro args rets Lin _ hpre
    exact (grind_check_completeB_of hm hκ hb args rets Lin hpre).toDTB
  | cap d =>
    simp only [osKindEntryOk, decide_eq_true_eq] at he
    exact completeRelRegDB_of_iff (leafSpecOk_all merkleCap_leafSpec _ he)
      (verify_merkle_cap_holds _ he) κ hb
  | ffm n =>
    simp only [osKindEntryOk, decide_eq_true_eq] at he
    exact completeRelRegDB_of_iff (leafSpecOk_all foldFinal_leafSpec _ he)
      (fold_final_msg_holds _ he) κ hb

/-- **A named call of a body proved at `osCR` on every memory holding `Lk`** is complete placed on
`Lk` within its bound. -/
theorem os_kid_namedB (hκ : 11 ≤ κ) {Bnd : String → ℕ} (hT : OsLeafBounds fs Bnd) {Lk : Layout}
    {σ : Val} {pre : List Stmt} {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → AllOk (osCR rd Sp (OsXOk κ Lk)) rd σ pre)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk)
    {c : Call} (hc : c ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) (ht : c.taken = true)
    {K : OsKind} (hK : osKindOf c.f = some K) :
    CompleteAtB fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bnd c.f) := by
  have hpre : ∀ rd, LowDef κ rd → MemL rd Lk → K.Pre rd (c.args.map σ) (c.rets.map σ) ∧
      OsXOk κ Lk K (c.args.map σ) := fun rd hl hm ↦ by
    have h := os_calls_of_allOk (hall rd hl hm) c hc ht
    unfold osCR at h; rw [hK] at h; exact h
  obtain ⟨rd0, hl0, hm0⟩ := hex
  exact (kindDB (cert := cert) hκ hT hK _ _ Lk (fixedReads_region (hpre rd0 hl0 hm0).2 ⟨rd0, hl0, hm0⟩)
    fun rd hl hm ↦ (hpre rd hl hm).1).toCompleteAtB

end
end LeanVM.Guest.B1
