/-
  LeanVM.Guest.B1.VerifySub.CPlaced8

  `verify_sub` is complete in the uniform placed form.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced7

/-!
# `verify_sub` is complete, placed

`verify_sub_completeAt`: for an accepting run within the deployed limits (`VsData.Ok`, `TOk`,
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

/-- **`verify_sub` is complete**, uniformly and placed: on an accepting run within the deployed
limits, from its callees' placed completeness. -/
theorem verify_sub_completeAt {κ : ℕ} (hκ : 6 ≤ κ)
    {CapOk : ℕ → ℕ → Digest → Digest → List E → List Opening → E → Prop}
    (hG : CompleteGkrAt fs cert κ) (hT : CompleteTablesAt fs cert κ bytecode TCtx)
    (hF : CompleteFlockAt fs cert κ) (hPl : CompletePlaceAt fs cert κ PCtx)
    (hO : CompleteOpenAt fs cert κ CapOk) (hE : CompleteTermAt fs cert κ TCtx PCtx)
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (htok : D.TOk bytecode)
    (hcap : CapOk (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os
      D.target)
    (lpA sqA outA : ℕ) :
    CompleteAt fs cert κ "verify_sub" (vsExtL lpA sqA outA D)
      [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
        (digestScalars D.seed).2, ofK (Parameters.gpow lpA), ofK (Parameters.gpow sqA),
        ofK (Parameters.gpow outA)] (Returns []) := by
  intro fp
  have hfit := vsBufs_fit hok htok
  -- the calls before the dispatch
  obtain ⟨N1, L1, outs1, ho1, hw1, hi1, hK1⟩ := kidsFromIn_of_kids' κ (vsKids1 fs D fp lpA sqA outA)
    (vsKids1_complete hb hok htok hG hT hF hPl hκ) (fp + fs "verify_sub" + (vsSizes D).sum)
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, rfl⟩ :=
    list12 (ho1.length.trans (by simp [vsKids1]))
  have h10 : PlaceOut D o10.1 o10.2 := by
    simp only [OutsOk, vsKids1, forall_const] at ho1
    exact ho1.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨off, kap, hr10, hpc⟩ := h10
  -- the opening
  obtain ⟨N2, L2, outs2, ho2, hw2, hi2, hK2⟩ := kidsFromIn_of_kids' κ
    [vsOpenKid fs bytecode D fp lpA sqA outA] (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsOpenKid_complete hok hO hcap)
    (fp + fs "verify_sub" + (vsSizes D).sum + N1)
  obtain ⟨oO, rfl⟩ := list1 (ho2.length.trans rfl)
  have hoO : OpenOutK D oO.1 oO.2 := by simpa [OutsOk, vsOpenKid] using ho2
  obtain ⟨bp, hr2, hLo⟩ := hoO
  set ptw := D.w.point ++ List.replicate (pointCap - D.w.point.length) 0
  -- the terminal
  obtain ⟨N3, L3, outs3, ho3, hw3, hi3, hK3⟩ := kidsFromIn_of_kids' κ
    [vsTermKid fs D fp lpA sqA outA off kap (ofK (Parameters.gpow bp)) o10.2 [(bp, ptw)]]
    (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk; exact vsTermKid_complete hb hok htok hE hpc)
    (fp + fs "verify_sub" + (vsSizes D).sum + N1 + N2)
  obtain ⟨oT, rfl⟩ := list1 (ho3.length.trans rfl)
  have hoT : oT.1 = [] := by
    have := ho3; simp only [OutsOk, vsTermKid, Returns, forall_const] at this; exact this.1.1
  refine ⟨fs "verify_sub" + (vsSizes D).sum + (N1 + (N2 + N3)),
    vsOwnL fs fp D ++ (L1 ++ (L2 ++ L3)), [], [], ⟨rfl, rfl⟩, ?_, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    refine ⟨(bufL_within _ _ _ hfit).mono (by omega) (by omega), hw1.mono (by omega) (by omega),
      hw2.mono (by omega) (by omega), hw3.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLe⟩ := Main.memL_append.mp hL
  obtain ⟨hOwn, hLs⟩ := Main.memL_append.mp hLm
  obtain ⟨hL1, hL23⟩ := Main.memL_append.mp hLs
  obtain ⟨hL2, hL3⟩ := Main.memL_append.mp hL23
  have hAll : MemL rd (vsAllL fs D fp lpA sqA outA) := Main.memL_append.mpr ⟨hOwn, hLe⟩
  obtain ⟨hm0, ht, -, -⟩ := vsAll_mem (off := off) (kap := kap) (pt := ofK (Parameters.gpow bp)) hAll
  obtain ⟨σ, sel, hsel, hfix, hpar, hw, hev⟩ :=
    vs_run (bytecode := bytecode) (hlow.mono hκ) hb hok ht hm0
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
