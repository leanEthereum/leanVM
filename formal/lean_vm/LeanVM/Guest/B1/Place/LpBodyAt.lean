/-
  LeanVM.Guest.B1.Place.LpBodyAt

  `level_positions` placed at one specialization: its squeeze run its own `HeapBuf`, its loop
  after it, its decoders' runs handed back.
-/

module

public import LeanVM.Guest.B1.Place.LpLoopAt

/-!
# `level_positions`, placed

`lpBody sq loop` is straight-line (`lpPreB`, then the `ret`): one `HeapBuf` of `(sq + 1)·5` words
(`sqz`, at `fp + fs name`), the capacity loaded from its first row, the loop entered behind the
guard `1 + g^sq`, the last row loaded and returned. The loop is the only callee, placed after the
buffer at `lpLoopFp`; decoder `j` sits at `lpDfp … fp j`, the loop's `lpDecAt`.

`lp_placed`: at every frame pointer, on every memory holding the decoders' runs, the squeeze run
(`lpSqzW`: row `j` the capacity `sqCaps cap j`), the loop's other words and the caller's words,
the specialization relates `cap ++ [pos, wp, tabs]` to `sqCaps cap sq` in `lpN` words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- Decoder `j`'s frame pointer, `level_positions` entered at `fp`: past its frame and its squeeze
run, the loop's `lpDecAt`. -/
def lpDfp (fs : String → ℕ) (name loop : String) (d cd sq fp j : ℕ) : ℕ :=
  lpDecAt fs loop (qwDecName d cd) sq (fp + fs name + (sq + 1) * 5) j

/-- The words of `level_positions`: its frame, its squeeze run and its loop's. -/
def lpN (fs : String → ℕ) (name loop : String) (d cd sq : ℕ) : ℕ :=
  fs name + (sq + 1) * 5 + lpTot fs loop (qwDecName d cd) sq 0

/-- The squeeze run's words: row `j` the capacity `sqCaps cap j`. -/
def lpSqzW (sq : ℕ) (cap : List E) : List E :=
  (List.range ((sq + 1) * 5)).map fun k ↦ (sqCaps cap (k / 5)).getD (k % 5) 0

theorem lpSqzW_length (sq : ℕ) (cap : List E) : (lpSqzW sq cap).length = (sq + 1) * 5 := by
  simp [lpSqzW]

theorem lpSqzW_get {sq : ℕ} {cap : List E} {j i : ℕ} (hi : i < 5)
    (h : 5 * j + i < (lpSqzW sq cap).length) :
    (lpSqzW sq cap)[5 * j + i] = (sqCaps cap j).getD i 0 := by
  simp only [lpSqzW, List.getElem_map, List.getElem_range]
  rw [show (5 * j + i) / 5 = j by omega, show (5 * j + i) % 5 = i by omega]

theorem lp_limb0_mul_ofK (p : E) (c : K) : (p * ofK c).limb 0 = p.limb 0 * c := by
  conv_lhs => rw [eq_ofLimbs p]
  rw [ofLimbs_mul_ofK]
  rfl

theorem lp_addr (b e t : ℕ) : (ofK (addressOfIndex b) * gen ^ e).limb 0 * addressOfIndex t =
    addressOfIndex (b + e + t) := by
  rw [gen_pow_eq_ofK, lp_limb0_mul_ofK, limb_ofK]
  simp only [Fin.val_zero, ↓reduceIte, Parameters.addressOfIndex, ← pow_add]

theorem lp_addr_shift (p : E) (e t : ℕ) : (p * gen ^ e).limb 0 * addressOfIndex t =
    p.limb 0 * addressOfIndex (e + t) := by
  rw [gen_pow_eq_ofK, lp_limb0_mul_ofK]
  simp only [Parameters.addressOfIndex, ← pow_add, mul_assoc]

/-- The body before its `ret`. -/
def lpPreB (sq : ℕ) (loop : String) : List Stmt :=
  osHeap ((sq + 1) * 5) 8 ++
    ((List.range 5).map fun i ↦ .atom (.load (.n i) (.n 9) i)) ++
    osLoopCall loop sq [9, 5, 6, 7] 10 ++
    [.atom (.const (.n 15) (gw (sq * 5))), .atom (.mul (.n 16) (.n 9) (.n 15))] ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (17 + i)) (.n 16) i)) ++
    ((List.range 5).map fun i ↦ .atom (.copy (.n (22 + i)) (.n (17 + i))))

theorem lpBody_pre (sq : ℕ) (loop : String) :
    lpBody sq loop = lpPreB sq loop ++ [.ret ((List.range 5).map fun i ↦ .n (22 + i))] := rfl

theorem lpPreB_straight (sq : ℕ) (loop : String) : (lpPreB sq loop).all Main.Stmt.straight = true :=
  rfl

theorem lpPreB_allocs (sq : ℕ) (loop : String) :
    (lpPreB sq loop).filterMap Main.Stmt.allocSz = [(.n 9, .inr (.n 8))] := rfl

theorem lpPreB_addrs (sq : ℕ) (loop : String) : (lpPreB sq loop).filterMap Main.Stmt.addrS = [] :=
  rfl

theorem lpPreB_calls (sq : ℕ) (loop : String) :
    (lpPreB sq loop).filterMap Main.Stmt.callS =
      [(some (.n 12), loop, [.n 13, .n 14, .n 9, .n 5, .n 6, .n 7], [])] := rfl

theorem lpPreB_loads (sq : ℕ) (loop : String) :
    (lpPreB sq loop).filterMap Stmt.loadS =
      ((List.range 5).map fun i ↦ ((.n 9 : V), i)) ++ ((List.range 5).map fun i ↦ ((.n 16 : V), i)) :=
  rfl

theorem lp_logG_gw {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gw e) = e := by
  rw [Whir.gw_eq (by unfold u128Bound; omega), logG_gen_pow he]

theorem lp_one_add_ne {n : ℕ} (h0 : 0 < n) (hn : n < 2 ^ 64 - 1) : (1 : E) + gen ^ n ≠ 0 := by
  intro h
  have h1 : gen ^ n = gen ^ 0 := by
    rw [pow_zero]
    have := congrArg (· + gen ^ n) h
    simpa [add_assoc, CharTwo.add_self_eq_zero] using this.symm
  have := gen_pow_inj hn (by omega) h1
  omega

theorem lp_getD5 {cap : List E} (hcl : cap.length = 5) (pos wp tabs : E) :
    (cap ++ [pos, wp, tabs]).getD 5 0 = pos ∧ (cap ++ [pos, wp, tabs]).getD 6 0 = wp ∧
      (cap ++ [pos, wp, tabs]).getD 7 0 = tabs := by
  match cap, hcl with
  | [_, _, _, _, _], _ => exact ⟨rfl, rfl, rfl⟩

/-- **`level_positions` at one specialization, placed at `fp`.** -/
theorem lp_placed (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {name loop : String}
    {sq d cd : ℕ} (hlp : FnIs name (osParams 8) (lpBody sq loop))
    (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop)) (hnl : coreProgram.loop name = false)
    (hll : coreProgram.loop loop = true) (hne : loop ≠ qwDecName d cd) (hsq : 0 < sq)
    (hsq64 : (sq + 1) * 5 < 2 ^ 64 - 1)
    (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d)
    (hdec : QwDecodeAtD fs cert κ d cd (qwDecName d cd))
    {cap : List E} {pos wp tabs : E} {Lin : Layout} (hcl : cap.length = 5)
    (hcan : AllCanonical cap) (fp : ℕ)
    (hreg : RegPtrs [(5, sq * (192 / d)), (6, sq * (192 / d)), (7, 128)] (cap ++ [pos, wp, tabs])
      (RegionL Lin))
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      LpMem cert d cd sq (lpDfp fs name loop d cd sq fp) cap pos wp tabs rd) :
    ∃ Lown : Layout,
      Within (lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap ++ Lown) fp
        (lpN fs name loop d cd sq) ∧
      DisjL (lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap ++ Lown) ∧
      ∀ rd, LowDef κ rd → MemL rd (lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin)
          (RegionL (lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap)) fp
          (lpN fs name loop d cd sq) name (cap ++ [pos, wp, tabs]) (sqCaps cap sq) := by
  obtain ⟨fnL, hfL, hpL, hbL⟩ := hl
  obtain ⟨fn, hf, hps, hb⟩ := hlp
  have hruns : lpRunsFrom cert d cd sq (lpDecAt fs loop (qwDecName d cd) sq (fp + fs name + (sq + 1) * 5))
      cap 0 = lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap := by
    simp [lpRunsFrom, lpRuns, lpDfp, List.flatMap]
  have hregL : ∀ i, RegionL Lin i → RegionL ((fp + fs name, lpSqzW sq cap) :: Lin) i :=
    fun i ⟨q, hq, h1, h2⟩ => ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
  have hsqzR : ∀ k < (sq + 1) * 5, RegionL ((fp + fs name, lpSqzW sq cap) :: Lin) (fp + fs name + k) :=
    fun k hk => ⟨(fp + fs name, lpSqzW sq cap), List.mem_cons_self .., by simp,
      by simp only [lpSqzW_length]; omega⟩
  have hQ : ∀ j < sq, ∀ t < 192 / d, j * (192 / d) + t < sq * (192 / d) := fun j hj t ht => by
    have := Nat.mul_le_mul_right (192 / d) (show j + 1 ≤ sq by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  obtain ⟨g5, g6, g7⟩ := lp_getD5 hcl pos wp tabs
  obtain ⟨LownL, hWL, hDL, hRL⟩ := lpLoop_relAtIn fs cert κ hfL hpL hbL hll hne hpw hdec (n := sq) hsq
    (by omega) (sqz := ofK (addressOfIndex (fp + fs name))) (pos := pos) (wp := wp) (tabs := tabs)
    hcl hcan (Lin := (fp + fs name, lpSqzW sq cap) :: Lin) (fp + fs name + (sq + 1) * 5)
    (fun rd _ hm j hj i hi => by
      have h := hm _ (List.mem_cons_self ..) (5 * j + i) (by simp only [lpSqzW_length]; omega)
      rwa [lpSqzW_get hi] at h)
    (fun rd hlow hm => hmem rd hlow (fun q hq => hm q (List.mem_cons_of_mem _ hq)))
    (fun j hj t ht => ⟨fp + fs name + j * 5 + t, by rw [← pow_mul, lp_addr],
      by rw [Nat.add_assoc]; exact hsqzR _ (by omega)⟩)
    (fun j hj => by
      intro p hp t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · obtain ⟨i, hi, hR⟩ := hreg (5, sq * (192 / d)) (by simp) (j * (192 / d) + t) (hQ j hj t ht)
        refine ⟨i, ?_, hregL i hR⟩
        rw [g5] at hi
        show (pos * (gen ^ j) ^ (192 / d)).limb 0 * addressOfIndex t = addressOfIndex i
        rw [← pow_mul, lp_addr_shift, ← hi]
      · obtain ⟨i, hi, hR⟩ := hreg (6, sq * (192 / d)) (by simp) (j * (192 / d) + t) (hQ j hj t ht)
        refine ⟨i, ?_, hregL i hR⟩
        rw [g6] at hi
        show (wp * (gen ^ j) ^ (192 / d)).limb 0 * addressOfIndex t = addressOfIndex i
        rw [← pow_mul, lp_addr_shift, ← hi]
      · obtain ⟨i, hi, hR⟩ := hreg (7, 128) (by simp) t ht
        refine ⟨i, ?_, hregL i hR⟩
        rw [g7] at hi
        exact hi)
  rw [hruns] at hWL hDL hRL
  refine ⟨(fp + fs name, lpSqzW sq cap) :: LownL, ?_, ?_, fun rd hlow hL => ?_⟩
  · intro q hq
    simp only [List.mem_append, List.mem_cons] at hq
    rcases hq with hq | rfl | hq
    · have := hWL q (List.mem_append_left _ hq); unfold lpN; omega
    · simp only [lpSqzW_length, lpN]; omega
    · have := hWL q (List.mem_append_right _ hq); unfold lpN; omega
  · have hc : DisjL ((fp + fs name, lpSqzW sq cap) ::
        (lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap ++ LownL)) := by
      unfold DisjL
      refine List.pairwise_cons.mpr ⟨fun q hq => Or.inl ?_, hDL⟩
      have := hWL q hq
      simp only [lpSqzW_length]; omega
    exact List.Pairwise.perm hc List.perm_middle.symm fun h => Or.symm h
  have hLin : MemL rd Lin := fun q hq => hL q (List.mem_append_right _ hq)
  have hE : ReadsAt rd (ofK (addressOfIndex (fp + fs name))) (lpSqzW sq cap) :=
    hL _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..)))
  have hLM : MemL rd (lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap ++ LownL ++
      (fp + fs name, lpSqzW sq cap) :: Lin) := fun q hq => hL q (by
    simp only [List.mem_append, List.mem_cons] at hq ⊢; tauto)
  have hrelL := hRL rd hlow hLM
  have hrow : ∀ j ≤ sq, ∀ i < 5, LoadHolds rd (ofK (addressOfIndex (fp + fs name))) (5 * j + i)
      ((sqCaps cap j).getD i 0) := fun j hj i hi => by
    have h := hE (5 * j + i) (by simp only [lpSqzW_length]; omega)
    rwa [lpSqzW_get hi] at h
  have hsq' : sq < u128Bound := by unfold u128Bound; omega
  have hsq5' : sq * 5 < u128Bound := by unfold u128Bound; omega
  have hK1 : (1 : E) + gen ^ sq ≠ 0 := lp_one_add_ne hsq (by omega)
  set sqz : E := ofK (addressOfIndex (fp + fs name)) with hsqz
  set last := sqCaps cap sq with hlast
  have hll5 : last.length = 5 := sqCaps_length cap hcl sq
  obtain ⟨l0, l1, l2, l3, l4, hl5⟩ : ∃ l0 l1 l2 l3 l4, last = [l0, l1, l2, l3, l4] := by
    match last, hll5 with
    | [l0, l1, l2, l3, l4], _ => exact ⟨l0, l1, l2, l3, l4, rfl⟩
  obtain ⟨c0, c1, c2, c3, c4, hc5⟩ : ∃ c0 c1 c2 c3 c4, cap = [c0, c1, c2, c3, c4] := by
    match cap, hcl with
    | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩
  set vals := [c0, c1, c2, c3, c4, pos, wp, tabs] ++ lpHonVals sq sqz last with hvals
  set σ : Val := fun v ↦ if v.path = [] ∧ v.tag = 0 then vals.getD v.idx 0 else 0 with hσ
  have hv : ∀ i, σ (.n i) = vals.getD i 0 := fun i ↦ by simp [hσ]
  have h0 : ∀ i < 5, LoadHolds rd sqz i ([c0, c1, c2, c3, c4].getD i 0) := fun i hi ↦ by
    have := hrow 0 (by omega) i hi
    simpa [sqCaps, hc5] using this
  have hs : ∀ i < 5, LoadHolds rd (sqz * gw (sq * 5)) i ([l0, l1, l2, l3, l4].getD i 0) :=
    fun i hi ↦ by
      have := hrow sq le_rfl i hi
      rw [← hlast, hl5] at this
      rw [Whir.gw_eq hsq5', loadHolds_mul_gen_pow, show sq * 5 + i = 5 * sq + i by ring]
      exact this
  have hst := lpPreB_straight sq loop
  have hw : walk σ fn.body = .ret ((lpPreB sq loop).flatMap (Main.slEvs σ))
      ((List.range 5).map fun i ↦ .n (22 + i)) := by
    rw [hb, lpBody_pre]; exact Main.walk_straight σ _ _ hst
  have hholds : Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun r => r = last) := by
    rw [hb, lpBody, holdsList_flat_ret _ (by simp [osHeap, osLoopCall, Stmt.flat])]
    refine ⟨?_, ?_⟩
    · simp only [osHeap, osLoopCall, allOk_cons, allOk_nil, and_true, StmtOk,
        Atom.Holds, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, hv, implies_true]
      simp only [hvals, lpHonVals, hl5, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, List.cons_append, List.nil_append, true_and,
        and_true]
      rw [word_one, Whir.gw_eq hsq']
      exact ⟨h0 0 (by omega), h0 1 (by omega), h0 2 (by omega), h0 3 (by omega), h0 4 (by omega),
        isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK _), hs 0 (by omega), hs 1 (by omega), hs 2 (by omega),
        hs 3 (by omega), hs 4 (by omega)⟩
    · simp [hv, hvals, lpHonVals, hl5, List.range_succ]
  set es := (lpPreB sq loop).flatMap (Main.slEvs σ) with hes_def
  have hes : ∀ e ∈ es, e.Holds rd σ := by
    have := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf))
      hholds
    rw [hw] at this
    exact fun e he => (this.1 e he).1
  have hr : ((List.range 5).map fun i ↦ V.n (22 + i)).map σ = last := by
    simp [hv, hvals, lpHonVals, hl5, List.range_succ]
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ _ hst
  have h8 : σ (.n 8) = gw ((sq + 1) * 5) := by simp [hv, hvals, lpHonVals]
  have h9 : σ (.n 9) = sqz := by simp [hv, hvals, lpHonVals]
  have h12 : σ (.n 12) = 1 + gen ^ sq := by
    simp [hv, hvals, lpHonVals, word_one, Whir.gw_eq hsq']
  have h16 : σ (.n 16) = sqz * gen ^ (sq * 5) := by
    simp [hv, hvals, lpHonVals, Whir.gw_eq hsq5']
  have hal : allocs σ es = [(sq + 1) * 5] := by
    rw [i2, lpPreB_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, h8, lp_logG_gw hsq64]
  have hcalls : calls es = [⟨loop, [.n 13, .n 14, .n 9, .n 5, .n 6, .n 7], [], true⟩] := by
    rw [i4, lpPreB_calls]
    simp [Main.mkCall, h12, hK1]
  have hargs : ([.n 13, .n 14, .n 9, .n 5, .n 6, .n 7] : List V).map σ =
      [1, gen ^ sq, sqz, pos, wp, tabs] := by
    simp [hv, hvals, lpHonVals, word_one, Whir.gw_eq hsq']
  have hown : ∀ k < (sq + 1) * 5, ownData cert fp (fp + fs name) name (allocs σ es) es
      (fp + fs name + k) := fun k hk => by
    rw [hal]
    exact Or.inl ⟨((sq + 1) * 5, fp + fs name), by simp [bases], by omega, by simp only; omega⟩
  have hrel := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL (lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap))
    (Dk := RegionL (lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap))
    (N := lpTot fs loop (qwDecName d cd) sq 0) (fp := fp)
    (args := cap ++ [pos, wp, tabs]) (rets := last)
    coreProgram_wf hf (Or.inl hnl)
    (by rw [hps, hc5]; simp [osParams, List.range_succ, hv, hvals]) hw hr hes
    (by rw [hal, i1, lpPreB_allocs]; simp [bases, h9, hsqz])
    (fun q hq => by rw [i3, lpPreB_addrs] at hq; simp at hq) ?_ (fun A hA => ?_) (fun i hi => Or.inr hi)
  · rw [hal] at hrel
    simpa [lpN] using hrel
  · rw [hcalls, hal]
    refine ⟨lpTot fs loop (qwDecName d cd) sq 0, 0, RegionL ((fp + fs name, lpSqzW sq cap) :: Lin),
      RegionL (lpRuns cert d cd sq (lpDfp fs name loop d cd sq fp) cap), by simp, fun i hi => ?_, ?_,
      rfl, fun i hi => Or.inr ⟨rfl, hi⟩⟩
    · obtain ⟨q, hq, h1, h2⟩ := hi
      rcases List.mem_cons.mp hq with rfl | hq
      · refine Or.inl (Or.inr ?_)
        rw [← hal]
        have := hown (i - (fp + fs name)) (by simp only [lpSqzW_length] at h2; omega)
        rwa [show fp + fs name + (i - (fp + fs name)) = i by simp only at h1; omega] at this
      · exact Or.inl (Or.inl ⟨q, hq, h1, h2⟩)
    · simp only [↓reduceIte, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [hargs]
      exact hrelL
  · rw [loadAddrs_straight σ _ hst, lpPreB_loads] at hA
    simp only [List.map_append, List.map_map, List.mem_append, List.mem_map, List.mem_range,
      Function.comp] at hA
    rcases hA with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · refine ⟨fp + fs name + i, ?_, Or.inl (hown i (by omega))⟩
      rw [h9, hsqz, Main.addr_ofK]
    · refine ⟨fp + fs name + sq * 5 + i, ?_, Or.inl ?_⟩
      · rw [h16, hsqz, lp_addr]
      · rw [Nat.add_assoc]; exact hown _ (by omega)

end
end LeanVM.Guest.B1
