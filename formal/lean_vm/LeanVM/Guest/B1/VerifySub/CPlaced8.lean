/-
  LeanVM.Guest.B1.VerifySub.CPlaced8

  `verify_sub` is complete in the uniform placed form.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced7

/-!
# `verify_sub` is complete, placed

`verify_sub_completeAtB`: for an accepting run within the deployed limits (`VsData.Ok`, `TOk`,
the opening's agreement at the cap `CapOk`), at every frame pointer one tree of one size serves
every memory holding `verify_sub`'s buffers, its callees' and the caller's words it reads (the
exponent tables at `g^lpA`, `g^sqA`, `defer_out`'s cells at `g^outA`): `verify_sub` holds of the
run's public input and seed, from its callees' placed completeness.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

set_option maxRecDepth 100000 in
theorem vs_not_loop : coreProgram.loop "verify_sub" = false := by
  rw [Program.loop_of_find? find_verify_sub]; decide +kernel

variable {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K} {D : VsData}

/-- The calls before the dispatch: their callees' bounds, the second loop's or its frame. -/
def vsKidsBound (fs : String → ℕ) (Bs : VsBounds) : ℕ :=
  2 * (fs "g_power_of_word__L6" + 6) + log2Bound0 fs + 2 * fs "assert_canonical" + Bs.gkr + Bs.tab +
    Bs.fl + 64 * (2 * fs "__loop84") + max (28 * (2 * fs "__loop85")) (fs "__loop85") + Bs.pl +
    log2Bound15 fs

/-- **`verify_sub`'s bound**: its frame, its buffers (at most `9086` words at the deployed
limits), its callees'. -/
def vsBound (fs : String → ℕ) (Bs : VsBounds) : ℕ :=
  fs "verify_sub" + 9086 + vsKidsBound fs Bs + Bs.op + Bs.term

theorem vsSizes_le (hok : D.Ok bytecode) :
    (vsSizes D).sum ≤ 9086 := by
  have hd : D.gr.2.1.length < 33 := by rw [hok.point_length]; exact hok.depth_lt
  have hτ := tau_lt hok
  simp only [vsSizes, List.sum_cons, List.sum_nil]
  omega

theorem vsKids1_bound {fp lpA sqA outA : ℕ} (Bs : VsBounds) :
    kidsBound fs (vsBd fs Bs) (vsKids1 fs D fp lpA sqA outA) ≤ vsKidsBound fs Bs := by
  simp (config := { decide := true }) only [kidsBound, vsKids1, vsBd, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, ↓reduceIte, vsKidsBound]
  split <;> omega

/-- The calls before the dispatch: their callees' weights. -/
def vsKidsBoundW {Θ : Type} (w : Θ → String → ℕ) (H : VsWeightHyps w) (Bsw : VsBoundsW Θ) (θ : Θ) : ℕ :=
  2 * H.gpw θ + H.l2a θ + 2 * H.ac θ + Bsw.gkr θ + Bsw.tab θ + Bsw.fl θ + 64 * (2 * w θ "__loop84") +
    28 * (2 * w θ "__loop85") + H.pl θ + H.l2b θ

/-- **`verify_sub`'s weight**: its frame's, its callees'. -/
def vsBoundW {Θ : Type} (w : Θ → String → ℕ) (H : VsWeightHyps w) (Bsw : VsBoundsW Θ) (θ : Θ) : ℕ :=
  w θ "verify_sub" + vsKidsBoundW w H Bsw θ + H.os θ + Bsw.term θ

theorem vsKids1_boundW {fp lpA sqA outA : ℕ} {Θ : Type} (w : Θ → String → ℕ) (H : VsWeightHyps w)
    (Bsw : VsBoundsW Θ) (θ : Θ) :
    Main.kidsBoundW (vsBdW w H Bsw) (vsKids1 fs D fp lpA sqA outA) θ ≤ vsKidsBoundW w H Bsw θ := by
  simp (config := { decide := true }) only [Main.kidsBoundW, vsKids1, vsBdW, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, ↓reduceIte, vsKidsBoundW]
  split <;> omega

/-- **`verify_sub` is complete**, uniformly and placed: on an accepting run within the deployed
limits, from its callees' placed completeness, by a tree within its callees' weights. -/
theorem verify_sub_completeAtW {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {Θ : Type} {w : Θ → String → ℕ} (H : VsWeightHyps w) {Bsw : VsBoundsW Θ}
    {Bs : VsBounds} (hG : CompleteGkrAtW fs cert κ w Bs.gkr Bsw.gkr)
    (hT : CompleteTablesAtW fs cert κ bytecode TCtx w Bs.tab Bsw.tab)
    (hF : CompleteFlockAtW fs cert κ w Bs.fl Bsw.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl) (hO : CompleteOpenAtB fs cert κ CapOk Bs.op)
    (hE : CompleteTermAtW fs cert κ TCtx PCtx w Bs.term Bsw.term)
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target)
    (lpA sqA outA : ℕ) :
    Main.CompleteAtW fs cert w κ "verify_sub" (vsExtL lpA sqA outA D)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) (vsBound fs Bs) fun θ => vsBoundW w H Bsw θ := by
  intro fp
  have hfit := vsBufs_fit hok htok
  -- the calls before the dispatch
  obtain ⟨N1, L1, outs1, ho1, hw1, hd1, hb1, hi1, hK1⟩ :=
    Main.kidsFromInW_of_kidsBW κ (vsBd fs Bs) (vsBdW w H Bsw) (vsKids1 fs D fp lpA sqA outA)
    (vsKids1_completeW hb hok htok H hG hT hF hPl hκ)
    (fp + fs "verify_sub" + (vsSizes D).sum)
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, rfl⟩ :=
    list12 (ho1.length.trans (by simp [vsKids1]))
  have h10 : PlaceOut D o10.1 o10.2 := by
    simp only [OutsOk, vsKids1, forall_const] at ho1
    exact ho1.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨off, kap, hr10, hpc⟩ := h10
  -- the opening
  obtain ⟨N2, L2, outs2, ho2, hw2, hd2, hb2, hi2, hK2⟩ := Main.kidsFromInW_of_kidsBW κ (fun _ => Bs.op) (fun _ θ => H.os θ)
    [vsOpenKid fs bytecode D fp lpA sqA outA] (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsOpenKid_completeW H hok hO hcap)
    (fp + fs "verify_sub" + (vsSizes D).sum + N1)
  obtain ⟨oO, rfl⟩ := list1 (ho2.length.trans rfl)
  have hoO : OpenOutK D oO.1 oO.2 := by simpa [OutsOk, vsOpenKid] using ho2
  obtain ⟨bp, hr2, hLo⟩ := hoO
  set ptw := D.w.point ++ List.replicate (pointCap - D.w.point.length) 0
  -- the terminal
  obtain ⟨N3, L3, outs3, ho3, hw3, hd3, hb3, hi3, hK3⟩ := Main.kidsFromInW_of_kidsBW κ (fun _ => Bs.term) (fun _ => Bsw.term)
    [vsTermKid fs D fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]]
    (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsTermKid_completeW hb hok htok hE hpc)
    (fp + fs "verify_sub" + (vsSizes D).sum + N1 + N2)
  obtain ⟨oT, rfl⟩ := list1 (ho3.length.trans rfl)
  have hoT : oT.1 = [] := by
    have := ho3; simp only [OutsOk, vsTermKid, Returns, forall_const] at this; exact this.1.1
  refine ⟨fs "verify_sub" + (vsSizes D).sum + (N1 + (N2 + N3)),
    vsOwnL fs fp D ++ (L1 ++ (L2 ++ L3)), [], [], ⟨rfl, rfl⟩, ?_, ?_, ?_, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    refine ⟨(bufL_within _ _ _ hfit).mono (by omega) (by omega), hw1.mono (by omega) (by omega),
      hw2.mono (by omega) (by omega), hw3.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    have w23 : Within (L2 ++ L3) (fp + fs "verify_sub" + (vsSizes D).sum + N1) (N2 + N3) :=
      within_append.mpr ⟨hw2.mono le_rfl (by omega), hw3.mono (by omega) (by omega)⟩
    have w123 : Within (L1 ++ (L2 ++ L3)) (fp + fs "verify_sub" + (vsSizes D).sum)
        (N1 + (N2 + N3)) :=
      within_append.mpr ⟨hw1.mono le_rfl (by omega), w23.mono (by omega) (by omega)⟩
    exact disj_append (bufL_disj _ _ _ hfit)
      (disj_append hd1 (disj_append hd2 hd3 hw2 hw3 le_rfl) hw1 w23 le_rfl)
      (bufL_within _ _ _ hfit) w123 le_rfl
  · have := vsSizes_le hok
    have := vsKids1_bound (fs := fs) (D := D) (fp := fp) (lpA := lpA) (sqA := sqA) (outA := outA) Bs
    simp only [kidsBound, vsOpenKid, vsTermKid, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ↓reduceIte] at hb2 hb3
    unfold vsBound
    omega
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLe⟩ := Main.memL_append.mp hL
  obtain ⟨hOwn, hLs⟩ := Main.memL_append.mp hLm
  obtain ⟨hL1, hL23⟩ := Main.memL_append.mp hLs
  obtain ⟨hL2, hL3⟩ := Main.memL_append.mp hL23
  have hAll : MemL rd (vsAllL fs D fp lpA sqA outA) := Main.memL_append.mpr ⟨hOwn, hLe⟩
  obtain ⟨hm0, ht, -, -⟩ := vsAll_mem (off := off) (kap := kap) (pt := ofK (Parameters.gpow bp)) hAll
  obtain ⟨σ, sel, hsel, hfix, hpar, hw, hev⟩ :=
    vs_run (bytecode := bytecode) (hlow.mono (by omega)) hb hok ht hm0
  obtain ⟨hcs, hcall⟩ := vs_calls hev
  obtain ⟨hal, hbuf⟩ := vs_allocs hb hok hfix sel
  have hR : ∀ i, RegionL (vsAllL fs D fp lpA sqA outA) i → RegionL (vsExtL lpA sqA outA D) i ∨
      ownData cert fp (fp + fs "verify_sub") "verify_sub" (vsSizes D) (vsEvs σ sel) i := by
    intro i ⟨q, hq, h1, h2⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inr (Or.inl (bufL_region _ _ _ hfit i ⟨q, hq, h1, h2⟩))
    · exact Or.inl ⟨q, hq, h1, h2⟩
  have hc : ∀ c ∈ calls (vsEvs σ sel), c.taken = true →
      (c.f, c.args.map σ, c.rets.map σ) ∈ vsTriples bytecode D
        (vsPtrsAt fs fp D off kap (ofK (Parameters.gpow bp))) (ofK (Parameters.gpow lpA))
        (ofK (Parameters.gpow sqA)) := hcall
  rw [hcs] at hc
  have h := Main.relAtInW_of_walk (fs := fs) (cert := cert) (w := w)
    (R := RegionL (vsExtL lpA sqA outA D)) (D := RegionL []) (Dk := fun _ => False)
    (N := N1 + (N2 + N3)) (fp := fp)
    (bws := Main.kidsWs (vsBdW w H Bsw) (vsKids1 fs D fp lpA sqA outA) ++
      (Main.kidsWs (fun _ θ => H.os θ) [vsOpenKid fs bytecode D fp lpA sqA outA] ++
        Main.kidsWs (fun _ => Bsw.term)
          [vsTermKid fs D fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]]))
    find_verify_sub (Or.inl vs_not_loop) hpar hw
    rfl (fun e he => (hev e he).1) (by rw [hal]; exact hbuf)
    (by rw [(vs_parts σ sel).2.2.1]; simp) ?_ ?_ (fun i ⟨q, hq, _⟩ => by simp at hq)
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    have := vsKids1_boundW (fs := fs) (D := D) (fp := fp) (lpA := lpA) (sqA := sqA) (outA := outA) w H Bsw θ
    simp only [List.map_append, List.sum_append, Main.kidsWs_sum]
    have e2 : Main.kidsBoundW (fun _ θ => H.os θ) [vsOpenKid fs bytecode D fp lpA sqA outA] θ = H.os θ := by
      simp [Main.kidsBoundW, vsOpenKid]
    have e3 : Main.kidsBoundW (fun _ => Bsw.term)
        [vsTermKid fs D fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]] θ =
          Bsw.term θ := by
      simp [Main.kidsBoundW, vsTermKid]
    rw [e2, e3]
    unfold vsBoundW
    omega
  · rw [hal, hcs]
    have hm1 := match1 hok hfix (fun c hc' ht' => hc c (List.mem_append_left _ hc') ht') ho1
      (by simpa using hr10)
    refine Main.kidsFromInW_append _ _ _ _ _ _ _ _ _ _
      (by rw [Main.kidsWs_length]; exact (Main.callsMatch_length hm1).symm) (hK1 rd σ _ _ (fun _ => False)
      hm1 (hlow) hL1 (memL_lins ?_) (regionsOk_of ?_))
      fun Dacc' hD1 => Main.kidsFromInW_append [_] [_] _ _ _ _ _ _ _ _ rfl (hK2 rd σ _ _ Dacc'
        (matchOpen (hc _ (List.mem_append_right _ List.mem_cons_self) rfl) hr2) hlow hL2
        (memL_lins ?_) (regionsOk_of ?_))
        fun Dacc'' hD2 => Main.kidsFromInW_dend _ _ _ _ _ (fun _ h => h.elim) (hK3 rd σ _ _ Dacc''
          (matchTerm (hc _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
            rfl) hoT) hlow hL3 (memL_lins ?_) (regionsOk_of ?_))
    · intro k hk
      simp only [vsKids1, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact gpwSq_mem hAll | exact hAll | exact fun _ h => (List.not_mem_nil h).elim
    · intro k hk ht' i hi
      simp only [vsKids1, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact Or.inl (hR i hi)
        | exact absurd hi (fun ⟨_, hq, _⟩ => List.not_mem_nil hq)
        | (obtain ⟨q, hq, h1, h2⟩ := hi
           simp only [List.mem_singleton] at hq
           subst hq
           exact Or.inl (Or.inl ⟨(sqA, (List.range sizeBits).map fun j => gen ^ 2 ^ j),
             by simp [vsExtL, expL], h1, by simp [gpwSq, sizeBits] at h2 ⊢; omega⟩))
    · intro k hk; rw [List.mem_singleton] at hk; subst hk; exact hAll
    · intro k hk _ i hi; rw [List.mem_singleton] at hk; subst hk; exact Or.inl (hR i hi)
    · intro k hk; rw [List.mem_singleton] at hk; subst hk
      simp only [OutsIn, vsKids1, forall_const] at hi1
      simp only [OutsIn] at hi2
      have hc10 := hi1.2.2.2.2.2.2.2.2.2.2.1
      refine Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨hAll, fun q hq => hL1 q (hc10 q hq)⟩,
        fun q hq => hL2 q (hi2.1 rfl q (by rw [hLo]; exact hq))⟩
    · intro k hk _ i hi; rw [List.mem_singleton] at hk; subst hk
      obtain ⟨q, hq, h1, h2⟩ := hi
      simp only [vsTermKid, List.mem_append] at hq
      rcases hq with (hq | hq) | hq
      · exact Or.inl (hR i ⟨q, hq, h1, h2⟩)
      · refine Or.inr (hD2 i (Or.inl (hD1 i (Or.inr ?_))))
        simp only [outRegion, vsKids1]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨trivial, q, hq, h1, h2⟩))))))))))
      · refine Or.inr (hD2 i (Or.inr ?_))
        simp only [outRegion, vsOpenKid]
        exact Or.inl ⟨trivial, q, by rw [hLo]; exact hq, h1, h2⟩
  · intro A hA
    rw [(vs_parts σ sel).2.2.2.2, List.mem_append] at hA
    have hq : ∃ q, loadOkB q = true ∧ A = (σ q.1).limb 0 * Parameters.gpow q.2 := by
      rcases hA with hA | hA <;> obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      · exact ⟨q, List.all_eq_true.mp vsPre1_loads q hq, rfl⟩
      · exact ⟨q, List.all_eq_true.mp vsPost2_loads q hq, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hq
    obtain ⟨i, hi, h⟩ := vs_load hb hok hfix q hq
    refine ⟨i, hi, ?_⟩
    rw [hal]
    rcases h with h | h
    · exact Or.inl (Or.inl (inBuf_own h))
    · exact Or.inr (Or.inl h)

/-- **`verify_sub` is complete**, uniformly and placed: on an accepting run within the deployed
limits, from its callees' placed completeness. -/
theorem verify_sub_completeAtB {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    {Bs : VsBounds} (hG : CompleteGkrAtB fs cert κ Bs.gkr)
    (hT : CompleteTablesAtB fs cert κ bytecode TCtx Bs.tab) (hF : CompleteFlockAtB fs cert κ Bs.fl)
    (hPl : CompletePlaceAtB fs cert κ PCtx Bs.pl) (hO : CompleteOpenAtB fs cert κ CapOk Bs.op)
    (hE : CompleteTermAtB fs cert κ TCtx PCtx Bs.term)
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target)
    (lpA sqA outA : ℕ) :
    CompleteAtB fs cert κ "verify_sub" (vsExtL lpA sqA outA D)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) (vsBound fs Bs) :=
  (verify_sub_completeAtW hκ (VsWeightHyps.empty fun e => e.elim)
    (Bsw := ⟨fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim⟩)
    hG.toWE hT.toWE hF.toWE hPl hO hE.toWE hb hok htok hcap lpA sqA outA).toB

/-- **`verify_sub` is complete**, uniformly and placed: on an accepting run within the deployed
limits, from its callees' placed completeness. -/
theorem verify_sub_completeAt {κ : ℕ} (hκ : 7 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    (hG : CompleteGkrAt fs cert κ) (hT : CompleteTablesAt fs cert κ bytecode TCtx)
    (hF : CompleteFlockAt fs cert κ) (hPl : CompletePlaceAt fs cert κ PCtx)
    (hO : CompleteOpenAt fs cert κ CapOk) (hE : CompleteTermAt fs cert κ TCtx PCtx)
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target)
    (lpA sqA outA : ℕ) :
    CompleteAtD fs cert κ "verify_sub" (vsExtL lpA sqA outA D)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) := by
  intro fp
  have hfit := vsBufs_fit hok htok
  -- the calls before the dispatch
  obtain ⟨N1, L1, outs1, ho1, hw1, hd1, hi1, hK1⟩ :=
    kidsFromIn_of_kidsD κ (vsKids1 fs D fp lpA sqA outA)
    (vsKids1_complete hb hok htok hG hT hF hPl hκ) (fp + fs "verify_sub" + (vsSizes D).sum)
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, rfl⟩ :=
    list12 (ho1.length.trans (by simp [vsKids1]))
  have h10 : PlaceOut D o10.1 o10.2 := by
    simp only [OutsOk, vsKids1, forall_const] at ho1
    exact ho1.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨off, kap, hr10, hpc⟩ := h10
  -- the opening
  obtain ⟨N2, L2, outs2, ho2, hw2, hd2, hi2, hK2⟩ := kidsFromIn_of_kidsD κ
    [vsOpenKid fs bytecode D fp lpA sqA outA] (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsOpenKid_complete hok hO hcap)
    (fp + fs "verify_sub" + (vsSizes D).sum + N1)
  obtain ⟨oO, rfl⟩ := list1 (ho2.length.trans rfl)
  have hoO : OpenOutK D oO.1 oO.2 := by simpa [OutsOk, vsOpenKid] using ho2
  obtain ⟨bp, hr2, hLo⟩ := hoO
  set ptw := D.w.point ++ List.replicate (pointCap - D.w.point.length) 0
  -- the terminal
  obtain ⟨N3, L3, outs3, ho3, hw3, hd3, hi3, hK3⟩ := kidsFromIn_of_kidsD κ
    [vsTermKid fs D fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]]
    (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsTermKid_complete hb hok htok hE hpc)
    (fp + fs "verify_sub" + (vsSizes D).sum + N1 + N2)
  obtain ⟨oT, rfl⟩ := list1 (ho3.length.trans rfl)
  have hoT : oT.1 = [] := by
    have := ho3; simp only [OutsOk, vsTermKid, Returns, forall_const] at this; exact this.1.1
  refine ⟨fs "verify_sub" + (vsSizes D).sum + (N1 + (N2 + N3)),
    vsOwnL fs fp D ++ (L1 ++ (L2 ++ L3)), [], [], ⟨rfl, rfl⟩, ?_, ?_, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    refine ⟨(bufL_within _ _ _ hfit).mono (by omega) (by omega), hw1.mono (by omega) (by omega),
      hw2.mono (by omega) (by omega), hw3.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    have w23 : Within (L2 ++ L3) (fp + fs "verify_sub" + (vsSizes D).sum + N1) (N2 + N3) :=
      within_append.mpr ⟨hw2.mono le_rfl (by omega), hw3.mono (by omega) (by omega)⟩
    have w123 : Within (L1 ++ (L2 ++ L3)) (fp + fs "verify_sub" + (vsSizes D).sum)
        (N1 + (N2 + N3)) :=
      within_append.mpr ⟨hw1.mono le_rfl (by omega), w23.mono (by omega) (by omega)⟩
    exact disj_append (bufL_disj _ _ _ hfit)
      (disj_append hd1 (disj_append hd2 hd3 hw2 hw3 le_rfl) hw1 w23 le_rfl)
      (bufL_within _ _ _ hfit) w123 le_rfl
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLe⟩ := Main.memL_append.mp hL
  obtain ⟨hOwn, hLs⟩ := Main.memL_append.mp hLm
  obtain ⟨hL1, hL23⟩ := Main.memL_append.mp hLs
  obtain ⟨hL2, hL3⟩ := Main.memL_append.mp hL23
  have hAll : MemL rd (vsAllL fs D fp lpA sqA outA) := Main.memL_append.mpr ⟨hOwn, hLe⟩
  obtain ⟨hm0, ht, -, -⟩ := vsAll_mem (off := off) (kap := kap) (pt := ofK (Parameters.gpow bp)) hAll
  obtain ⟨σ, sel, hsel, hfix, hpar, hw, hev⟩ :=
    vs_run (bytecode := bytecode) (hlow.mono (by omega)) hb hok ht hm0
  obtain ⟨hcs, hcall⟩ := vs_calls hev
  obtain ⟨hal, hbuf⟩ := vs_allocs hb hok hfix sel
  have hR : ∀ i, RegionL (vsAllL fs D fp lpA sqA outA) i → RegionL (vsExtL lpA sqA outA D) i ∨
      ownData cert fp (fp + fs "verify_sub") "verify_sub" (vsSizes D) (vsEvs σ sel) i := by
    intro i ⟨q, hq, h1, h2⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inr (Or.inl (bufL_region _ _ _ hfit i ⟨q, hq, h1, h2⟩))
    · exact Or.inl ⟨q, hq, h1, h2⟩
  have hc : ∀ c ∈ calls (vsEvs σ sel), c.taken = true →
      (c.f, c.args.map σ, c.rets.map σ) ∈ vsTriples bytecode D
        (vsPtrsAt fs fp D off kap (ofK (Parameters.gpow bp))) (ofK (Parameters.gpow lpA))
        (ofK (Parameters.gpow sqA)) := hcall
  rw [hcs] at hc
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert)
    (R := RegionL (vsExtL lpA sqA outA D)) (D := RegionL []) (Dk := fun _ => False)
    (N := N1 + (N2 + N3)) (fp := fp) coreProgram_wf find_verify_sub (Or.inl vs_not_loop) hpar hw
    rfl (fun e he => (hev e he).1) (by rw [hal]; exact hbuf)
    (by rw [(vs_parts σ sel).2.2.1]; simp) ?_ ?_ (fun i ⟨q, hq, _⟩ => by simp at hq)
  · rw [hal] at h; exact h
  · rw [hal, hcs]
    refine kidsFromIn_append _ _ _ _ _ _ _ _ (hK1 rd σ _ _ (fun _ => False)
      (match1 hok hfix (fun c hc' ht' => hc c (List.mem_append_left _ hc') ht') ho1
        (by simpa using hr10)) (hlow) hL1 (memL_lins ?_) (regionsOk_of ?_))
      fun Dacc' hD1 => kidsFromIn_append [_] [_] _ _ _ _ _ _ (hK2 rd σ _ _ Dacc'
        (matchOpen (hc _ (List.mem_append_right _ List.mem_cons_self) rfl) hr2) hlow hL2
        (memL_lins ?_) (regionsOk_of ?_))
        fun Dacc'' hD2 => kidsFromIn_dend _ _ _ _ (fun _ h => h.elim) (hK3 rd σ _ _ Dacc''
          (matchTerm (hc _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
            rfl) hoT) hlow hL3 (memL_lins ?_) (regionsOk_of ?_))
    · intro k hk
      simp only [vsKids1, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact gpwSq_mem hAll | exact hAll | exact fun _ h => (List.not_mem_nil h).elim
    · intro k hk ht' i hi
      simp only [vsKids1, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact Or.inl (hR i hi)
        | exact absurd hi (fun ⟨_, hq, _⟩ => List.not_mem_nil hq)
        | (obtain ⟨q, hq, h1, h2⟩ := hi
           simp only [List.mem_singleton] at hq
           subst hq
           exact Or.inl (Or.inl ⟨(sqA, (List.range sizeBits).map fun j => gen ^ 2 ^ j),
             by simp [vsExtL, expL], h1, by simp [gpwSq, sizeBits] at h2 ⊢; omega⟩))
    · intro k hk; rw [List.mem_singleton] at hk; subst hk; exact hAll
    · intro k hk _ i hi; rw [List.mem_singleton] at hk; subst hk; exact Or.inl (hR i hi)
    · intro k hk; rw [List.mem_singleton] at hk; subst hk
      simp only [OutsIn, vsKids1, forall_const] at hi1
      simp only [OutsIn] at hi2
      have hc10 := hi1.2.2.2.2.2.2.2.2.2.2.1
      refine Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨hAll, fun q hq => hL1 q (hc10 q hq)⟩,
        fun q hq => hL2 q (hi2.1 rfl q (by rw [hLo]; exact hq))⟩
    · intro k hk _ i hi; rw [List.mem_singleton] at hk; subst hk
      obtain ⟨q, hq, h1, h2⟩ := hi
      simp only [vsTermKid, List.mem_append] at hq
      rcases hq with (hq | hq) | hq
      · exact Or.inl (hR i ⟨q, hq, h1, h2⟩)
      · refine Or.inr (hD2 i (Or.inl (hD1 i (Or.inr ?_))))
        simp only [outRegion, vsKids1]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨trivial, q, hq, h1, h2⟩))))))))))
      · refine Or.inr (hD2 i (Or.inr ?_))
        simp only [outRegion, vsOpenKid]
        exact Or.inl ⟨trivial, q, by rw [hLo]; exact hq, h1, h2⟩
  · intro A hA
    rw [(vs_parts σ sel).2.2.2.2, List.mem_append] at hA
    have hq : ∃ q, loadOkB q = true ∧ A = (σ q.1).limb 0 * Parameters.gpow q.2 := by
      rcases hA with hA | hA <;> obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      · exact ⟨q, List.all_eq_true.mp vsPre1_loads q hq, rfl⟩
      · exact ⟨q, List.all_eq_true.mp vsPost2_loads q hq, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hq
    obtain ⟨i, hi, h⟩ := vs_load hb hok hfix q hq
    refine ⟨i, hi, ?_⟩
    rw [hal]
    rcases h with h | h
    · exact Or.inl (Or.inl (inBuf_own h))
    · exact Or.inr (Or.inl h)

end
end LeanVM.Guest.B1.VerifySub
