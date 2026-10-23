/-
  LeanVM.Guest.B1.Tables.PlaceAt

  `certify_placement` complete in the uniform placed form, its three `HeapBuf`s its `Lout`.
-/

module

public import LeanVM.Guest.B1.Tables.Kappas
public import LeanVM.Guest.B1.Tables.TermAtProof
public import LeanVM.Guest.B1.Tables.FlatAtB

/-!
# `certify_placement`, placed

On any memory defined below `2^7` (the range checks' low reads) holding the exponent tables
and `kappa_base`, the honest valuation of `cp_complete` holds of the body (`cp_honest`): the
columns' sizes are `committedKappas (columnKappas log_mem 18 h)`, its buffers hold their logs,
their order and their offsets, and every load reads `kappa_base`, the squares or a buffer.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

section
variable {C : CallRel} {rd : Reader}

/-- `certify_placement`'s body, simplified to its conditions and its return. -/
theorem cp_holds (σ : Val) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ cpBody False kret ↔
      (∀ c < 92, CpInitOk rd σ c) ∧
      LoadHolds rd (σ (.n 99)) 0 (σ (.n 101)) ∧ σ (.n 102) = w91 ∧
      RcHolds rd σ 101 103 104 105 102 ∧ σ (.n 106) = σ (.n 2) * σ (.n 101) ∧
      LoadHolds rd (σ (.n 106)) 0 (σ (.n 107)) ∧ σ (.n 108) = word 1 0 0 ∧
      σ (.n 109) = σ (.n 100) * σ (.n 101) ∧ LoadHolds rd (σ (.n 109)) 0 (σ (.n 108)) ∧
      σ (.n 110) = w33 ∧ RcHolds rd σ 107 111 112 113 110 ∧
      σ (.n 114) = σ (.n 1) * σ (.n 107) ∧ LoadHolds rd (σ (.n 114)) 0 (σ (.n 115)) ∧
      (∀ r < 91, CpRankOk rd σ (r + 1)) ∧
      σ (.n 2482) = σ (.n 2481) ∧ σ (.n 2483) = σ (.n 100) ∧ σ (.n 2484) = σ (.n 2) ∧
      kret [σ (.n 2482), σ (.n 2483), σ (.n 2484)] := by
  rw [cpBody]
  simp only [holdsList_append, holdsList_range_flatten 92 cpInit (fun c => by
      unfold cpInit; split_ifs <;> rfl),
    holdsList_range_flatten 91 (fun r => cpRank (r + 1)) (fun _ => rfl), holds_cpInit,
    holds_cpRank, cpRank0, RcHolds, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil, true_and]

/-- **The honest valuation of `certify_placement`** on any memory defined below `2^7`: its
body holds, returning `g^(Σ 2^κ)` and the buffers' pointers, and its loads' pointers. -/
theorem cp_honest (hlow : LowDef 7 rd) {kb sq : E}
    (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) (κs : List ℕ) (hlen : κs.length = 92)
    (hκ : ∀ c < 92, κs.getD c 0 < 34 ∧
      ∃ w, LoadHolds rd kb (cpSrc c) w ∧ w * gen ^ cpAdj c = gen ^ κs.getD c 0)
    (p2 p99 p100 : E) (h99 : ReadsAt rd p99 ((stackOrder κs).map (gen ^ ·)))
    (h2 : ReadsAt rd p2 (κs.map (gen ^ ·)))
    (h100 : ReadsAt rd p100 ((stackOffsets κs).1.map (gen ^ ·))) :
    ∃ σ : Val, σ (.n 0) = kb ∧ σ (.n 1) = sq ∧ σ (.n 2) = p2 ∧ σ (.n 99) = p99 ∧
      σ (.n 100) = p100 ∧
      (∀ kret : List E → Prop, kret [gen ^ (κs.map (2 ^ ·)).sum, p100, p2] →
        Stmt.HoldsList C rd σ cpBody False kret) ∧
      (∀ r < 92, cpPi κs r < 92 ∧ cpK κs r < 34) ∧
      σ (.n 106) = p2 * gen ^ cpPi κs 0 ∧ σ (.n 109) = p100 * gen ^ cpPi κs 0 ∧
      σ (.n 114) = sq * gen ^ cpK κs 0 ∧
      ∀ r < 91, σ (.n (90 + 26 * (r + 1) + 5)) = p2 * gen ^ cpPi κs (r + 1) ∧
        σ (.n (90 + 26 * (r + 1) + 18)) = p100 * gen ^ cpPi κs (r + 1) ∧
        σ (.n (90 + 26 * (r + 1) + 23)) = sq * gen ^ cpK κs (r + 1) := by
  obtain ⟨w, hw⟩ := exists_fun_of_forall (n := 92) (fun c hc => (hκ c hc).2)
  have hol : (stackOrder κs).length = 92 := by rw [stackOrder_length, hlen]
  have hperm : (stackOrder κs).Perm (List.range 92) := by
    rw [← hlen]; exact List.mergeSort_perm _ _
  have hπ : ∀ r < 92, cpPi κs r < 92 := fun r hr => by
    have := hperm.subset (List.getElem_mem (show r < (stackOrder κs).length by omega))
    rw [cpPi, List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_range.mp this
  have hk : ∀ r < 92, cpK κs r < 34 := fun r hr => (hκ _ (hπ r hr)).1
  have l99 : ∀ r < 92, LoadHolds rd p99 r (gen ^ cpPi κs r) := fun r hr =>
    readsAt_map_iff.mp h99 r (by omega)
  have l2 : ∀ c < 92, LoadHolds rd p2 c (gen ^ κs.getD c 0) := fun c hc =>
    readsAt_map_iff.mp h2 c (by omega)
  have l100 : ∀ r < 92, LoadHolds rd p100 (cpPi κs r) (gen ^ cpS κs r) := fun r hr => by
    have := readsAt_map_iff.mp h100 (cpPi κs r) (by rw [stackOffsets_length, hlen]; exact hπ r hr)
    rwa [cpPi, stackOrder, stackOffsets_fst κs r (by omega)] at this
  obtain ⟨A, hA⟩ := exists_fun_of_forall (n := 92) (α := E × E × E)
    (P := fun r a => RcOk rd (gen ^ cpPi κs r) 92 a)
    fun r hr => ⟨_, (by
      rw [gen_pow_eq_ofK]
      exact rc_complete_low hlow (K := 92) (e := cpPi κs r) (by norm_num) (hπ r hr))⟩
  obtain ⟨B, hB⟩ := exists_fun_of_forall (n := 92) (α := E × E × E)
    (P := fun r a => RcOk rd (gen ^ (cpK κs (r - 1) - cpK κs r)) 34 a)
    fun r hr => ⟨_, (by
      rw [gen_pow_eq_ofK]
      exact rc_complete_low hlow (K := 34) (e := cpK κs (r - 1) - cpK κs r) (by norm_num)
        (lt_of_le_of_lt (Nat.sub_le _ _) (hk (r - 1) (by omega))))⟩
  obtain ⟨C, hC⟩ := exists_fun_of_forall (n := 92) (α := E × E × E)
    (P := fun r a => RcOk rd (gen ^ (cpPi κs r - cpPi κs (r - 1))) 92 a)
    fun r hr => ⟨_, (by
      rw [gen_pow_eq_ofK]
      exact rc_complete_low hlow (K := 92) (e := cpPi κs r - cpPi κs (r - 1)) (by norm_num)
        (lt_of_le_of_lt (Nat.sub_le _ _) (hπ r hr)))⟩
  obtain ⟨D, hD⟩ := exists_fun_of_forall (n := 92) (α := E × E × E)
    (P := fun r a => RcOk rd (gen ^ cpK κs r) 34 a)
    fun r hr => ⟨_, (by
      rw [gen_pow_eq_ofK]
      exact rc_complete_low hlow (K := 34) (e := cpK κs r) (by norm_num) (hk r hr))⟩
  obtain ⟨F, hF⟩ : ∃ F, F = cpF A B C D κs kb sq p2 p99 p100 w := ⟨_, rfl⟩
  have hR : ∀ R, 1 ≤ R → R ≤ 91 → ∀ j < 26,
      F (90 + 26 * R + j) = (cpRankVals A B C D κs sq p2 p100 R).getD j 0 := fun R h1 h2 j hj => by
    rw [hF]; exact cpF_rank A B C D κs rfl h1 h2 hj
  have h0 : ∀ j < 15, F (101 + j) = (cpRank0Vals A D κs sq p2 p100).getD j 0 := fun j hj => by
    rw [hF]; exact cpF_rank0 A B C D κs rfl hj
  have hG : ∀ R, 1 ≤ R → R ≤ 91 → F (90 + 26 * R - 1) = gen ^ cpS κs R := fun R h1 h2 => by
    rw [hF]; exact cpF_G A B C D κs hlen h1 h2
  have f0 : F 0 = kb := by rw [hF]; rfl
  have f1 : F 1 = sq := by rw [hF]; rfl
  have f2 : F 2 = p2 := by rw [hF]; rfl
  have f99 : F 99 = p99 := by rw [hF]; rfl
  have f100 : F 100 = p100 := by rw [hF]; rfl
  have hsum : cpS κs 92 = (κs.map (2 ^ ·)).sum := by
    have hfull := prefixSize_full (κs.getD · 0) (stackOrder κs)
    rw [hol] at hfull
    rw [cpS, hfull, (hperm.map _).sum_eq]
    congr 1
    refine List.ext_getElem (by simp [hlen]) fun c h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; simpa using h1)]
  have v := fun j hj => h0 j hj
  have v0 : F 101 = gen ^ cpPi κs 0 := v 0 (by omega)
  have v1 : F 102 = w91 := v 1 (by omega)
  have v2 : F 103 = (A 0).1 := v 2 (by omega)
  have v3 : F 104 = (A 0).2.1 := v 3 (by omega)
  have v4 : F 105 = (A 0).2.2 := v 4 (by omega)
  have v5 : F 106 = p2 * gen ^ cpPi κs 0 := v 5 (by omega)
  have v6 : F 107 = gen ^ cpK κs 0 := v 6 (by omega)
  have v7 : F 108 = word 1 0 0 := v 7 (by omega)
  have v8 : F 109 = p100 * gen ^ cpPi κs 0 := v 8 (by omega)
  have v9 : F 110 = w33 := v 9 (by omega)
  have v10 : F 111 = (D 0).1 := v 10 (by omega)
  have v11 : F 112 = (D 0).2.1 := v 11 (by omega)
  have v12 : F 113 = (D 0).2.2 := v 12 (by omega)
  have v13 : F 114 = sq * gen ^ cpK κs 0 := v 13 (by omega)
  have v14 : F 115 = gen ^ 2 ^ cpK κs 0 := v 14 (by omega)
  obtain ⟨a0, b0, c0⟩ := hA 0 (by omega)
  obtain ⟨a1, b1, c1⟩ := hD 0 (by omega)
  have hRv : ∀ r < 91, F (90 + 26 * (r + 1) + 5) = p2 * gen ^ cpPi κs (r + 1) ∧
      F (90 + 26 * (r + 1) + 18) = p100 * gen ^ cpPi κs (r + 1) ∧
      F (90 + 26 * (r + 1) + 23) = sq * gen ^ cpK κs (r + 1) := fun r hr => by
    have e5 := hR (r + 1) (by omega) (by omega) 5 (by omega)
    have e18 := hR (r + 1) (by omega) (by omega) 18 (by omega)
    have e23 := hR (r + 1) (by omega) (by omega) 23 (by omega)
    simp only [cpRankVals, List.getD_cons_succ, List.getD_cons_zero] at e5 e18 e23
    exact ⟨e5, e18, e23⟩
  refine ⟨fun v => F v.idx, f0, f1, f2, f99, f100, fun kret hkr => (cp_holds _ kret).mpr
    ⟨fun c hc => cp_init_ok rd κs hF hw l2 c hc, ?_⟩, fun r hr => ⟨hπ r hr, hk r hr⟩, v5, v8, v13,
    hRv⟩
  refine ⟨?_, v1, ?_, ?_, ?_, v7, ?_, ?_, v9, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · show LoadHolds _ (F 99) 0 (F 101); rw [f99, v0]; exact l99 0 (by omega)
  · show LoadHolds _ (F 101) 0 (F 104) ∧ F 102 = F 101 * F 103 ∧ LoadHolds _ (F 103) 0 (F 105)
    rw [v0, v1, v2, v3, v4]; exact ⟨a0, word_g91.trans b0, c0⟩
  · show F 106 = F 2 * F 101; rw [v5, f2, v0]
  · show LoadHolds _ (F 106) 0 (F 107)
    rw [v5, v6, loadHolds_mul_gen_pow, Nat.add_zero]; exact l2 _ (hπ 0 (by omega))
  · show F 109 = F 100 * F 101; rw [v8, f100, v0]
  · show LoadHolds _ (F 109) 0 (F 108)
    rw [v8, v7, loadHolds_mul_gen_pow, Nat.add_zero, word_one]
    have := l100 0 (by omega)
    rwa [show cpS κs 0 = 0 by simp [cpS, prefixSize], pow_zero] at this
  · show LoadHolds _ (F 107) 0 (F 112) ∧ F 110 = F 107 * F 111 ∧ LoadHolds _ (F 111) 0 (F 113)
    rw [v6, v9, v10, v11, v12]; exact ⟨a1, word_g33.trans b1, c1⟩
  · show F 114 = F 1 * F 107; rw [v13, f1, v6]
  · show LoadHolds _ (F 114) 0 (F 115)
    rw [v13, v14, loadHolds_mul_gen_pow, Nat.add_zero]; exact hsq _ (hk 0 (by omega))
  · exact cp_rank_ok rd hsq κs hlen hF hπ hk l99 l2 l100 hA hB hC hD r hr
  · show F 2482 = F 2481
    rw [show F 2482 = gen ^ cpS κs 92 by rw [hF]; rfl]
    have := hR 91 (by omega) (by omega) 25 (by omega)
    simp only [cpRankVals, List.getD_cons_succ, List.getD_cons_zero] at this
    exact this.symm
  · show F 2483 = F 100; rw [f100, hF]; rfl
  · show F 2484 = F 2; rw [f2, hF]; rfl
  · show kret [F 2482, F 2483, F 2484]
    rw [show F 2482 = gen ^ cpS κs 92 by rw [hF]; rfl, show F 2483 = p100 by rw [hF]; rfl,
      show F 2484 = p2 by rw [hF]; rfl, hsum]
    exact hkr


/-! ## The body's shape -/

/-- `certify_placement`'s body before its `ret`. -/
def cpPre : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 92))] ++ ((List.range 92).map cpInit).flatten ++
    [.atom (.hint (.alloc (.n 99) 92)),
      .atom (.hint (.witness "col_sort_order" (.heap (.n 99) 0 92))),
      .atom (.hint (.alloc (.n 100) 92))] ++
    cpRank0 ++ ((List.range 91).map fun r => cpRank (r + 1)).flatten ++
    [.atom (.copy (.n 2482) (.n 2481)), .atom (.copy (.n 2483) (.n 100)),
      .atom (.copy (.n 2484) (.n 2))]

theorem cp_body : Fn.body Data.core13 = cpPre ++ [.ret [.n 2482, .n 2483, .n 2484]] := by
  rw [core13_body, cpBody, cpPre]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem find_cp : coreProgram.find? "certify_placement" = some Data.core13 :=
  Program.find?_of_indexOf? (j := 13) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem cp_not_loop : coreProgram.loop "certify_placement" = false := by
  rw [Program.loop_of_find? find_cp]; decide +kernel

theorem cp_flat : cpPre.all Stmt.flat = true := by decide +kernel

theorem cp_addrs : cpPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem cp_allocs : cpPre.filterMap Main.Stmt.allocSz =
    [(.n 2, .inl 92), (.n 99, .inl 92), (.n 100, .inl 92)] := by decide +kernel

theorem cp_disps : cpPre.filterMap Stmt.dispX = [] := by decide +kernel

theorem cp_calls (σ : Val) : cpPre.filterMap (Stmt.callSF σ) = [] := by
  rw [callSF_nodisp σ _ (by decide +kernel)]; decide +kernel

/-- `certify_placement`'s loads: `kappa_base`, the buffers, and the products at a rank's column
or size. -/
def cpLoadB (q : V × ℕ) : Bool :=
  (q.1 == .n 0 && decide (q.2 < 8)) || ((q.1 == .n 2 || q.1 == .n 99) && decide (q.2 < 92)) ||
    (q.2 == 0 && (q.1 == .n 106 || q.1 == .n 109 || q.1 == .n 114 ||
      (List.range 91).any fun r => q.1 == .n (90 + 26 * (r + 1) + 5) ||
        q.1 == .n (90 + 26 * (r + 1) + 18) || q.1 == .n (90 + 26 * (r + 1) + 23)))

theorem cp_loads : (cpPre.filterMap Stmt.loadS).all cpLoadB = true := by decide +kernel

theorem limb_mul_gen_pow' {p : E} (hp : IsInK p) (j off : ℕ) :
    (p * gen ^ j).limb 0 * Parameters.gpow off = p.limb 0 * Parameters.gpow (j + off) := by
  conv_lhs => rw [eq_ofK_limb hp, gen_pow_eq_ofK, ← ofK_mul, limb_ofK]
  simp [Parameters.gpow, pow_add, mul_assoc]

end

set_option maxHeartbeats 4000000 in
/-- **`certify_placement` is complete, placed, by a bounded tree** (TRIAGE #41):
`CompletePlaceAtB` at its frame and its three `HeapBuf`s, on memories defined below `2^7`. -/
theorem certify_placement_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 7 ≤ κ) : CompletePlaceAtB fs cert κ PCtx (fs "certify_placement" + 276) := by
  intro lp sq kb lm hs Lin hlm hl hh h5 hpre
  set kps := columnKappas lm 18 hs
  set κs := committedKappas kps with hκsdef
  have hlen : κs.length = 92 := committedKappas_length _ (columnKappas_length_110 _ _ _)
  have hκv : ∀ c < 92, κs.getD c 0 = (0 :: lm :: hs).getD (cpSrc c) 0 + cpAdj c := fun c hc => by
    rw [hκsdef, committedKappas_columnKappas lm hs hl, getD_map_range _ _ hc]
  have hsrc : ∀ c, cpSrc c < 8 := fun c => by unfold cpSrc; split_ifs <;> omega
  have hb32 : ∀ s < 8, (0 :: lm :: hs).getD s 0 ≤ 32 := fun s hs8 => by
    rcases s with _ | _ | s
    · simp
    · simpa using hlm
    · simp only [List.getD_cons_succ]
      rw [List.getD_eq_getElem _ _ (by omega)]
      have := hh _ (List.getElem_mem (show s < hs.length by omega))
      omega
  have hκ34 : ∀ c < 92, κs.getD c 0 < 34 := fun c hc => by
    rw [hκv c hc]
    by_cases h4 : c = 4
    · subst h4; rw [show cpSrc 4 = 0 from rfl, show cpAdj 4 = 18 from rfl]; simp
    · by_cases h5' : c = 5
      · subst h5'; rw [show cpSrc 5 = 7 from rfl, show cpAdj 5 = 8 from rfl]; exact h5
      · have := hb32 _ (hsrc c)
        have h0 : cpAdj c = 0 := by unfold cpAdj; rw [ite_neg' h4, ite_neg' h5']
        omega
  have hkb8 : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd kb (1 :: gen ^ lm :: hs.map (gen ^ ·)) := fun rd h1 h2 => (hpre rd h1 h2).2
  have hbase : ∀ rd, LowDef κ rd → MemL rd Lin → ∀ s < 8,
      LoadHolds rd kb s (gen ^ (0 :: lm :: hs).getD s 0) := fun rd h1 h2 s hs8 => by
    have := hkb8 rd h1 h2 s (by simp [hl]; omega)
    rcases s with _ | _ | s
    · simpa using this
    · simpa using this
    · simp only [List.getElem_cons_succ, List.getElem_map] at this
      simp only [List.getD_cons_succ]
      rwa [List.getD_eq_getElem _ _ (by omega)]
  have hκf : ∀ rd, LowDef κ rd → MemL rd Lin → ∀ c < 92, κs.getD c 0 < 34 ∧
      ∃ w, LoadHolds rd kb (cpSrc c) w ∧ w * gen ^ cpAdj c = gen ^ κs.getD c 0 :=
    fun rd h1 h2 c hc => ⟨hκ34 c hc, _, hbase rd h1 h2 _ (hsrc c), by rw [hκv c hc, pow_add]⟩
  have hallSq : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd sq ((List.range 34).map fun j => gen ^ 2 ^ j) := fun rd h1 h2 j hj => by
    simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range]
    exact ((hpre rd h1 h2).1 j hj).2
  refine CompleteAtB.mono (B := fs "certify_placement" + [92, 92, 92].sum + 0) ?_ le_rfl (by simp)
  refine completeAt_flatOutB find_cp cp_not_loop κ Lin [kb, sq]
    (fun fp => [gen ^ stackTotal kps, ofK (Parameters.gpow (fp + fs "certify_placement" + 92 + 92)),
      ofK (Parameters.gpow (fp + fs "certify_placement"))]) _ cp_body cp_flat cp_addrs [92, 92, 92]
    (fun _ => [κs.map (gen ^ ·), (stackOrder κs).map (gen ^ ·), (stackOffsets κs).1.map (gen ^ ·)])
    (fun _ => by simp [hlen, stackOrder_length, stackOffsets_length]) (fun fp => ?_) (fun _ => [])
    (fun _ => 0) 0 (fun _ k hk => by simp at hk) (fun _ => by simp [kidsBound])
    (fun _ k hk => by simp at hk) (fun _ _ _ _ k hk => by simp at hk) ?_
  · refine ⟨_, _, rfl, fun rd hm => ⟨columnKappas_length_110 _ _ _,
      memL_one hm (by simp [bufL, bases, hκsdef]), memL_one hm (by simp [bufL, bases, hκsdef])⟩⟩
  intro fp outs ho rd hlow hB hL
  generalize hbd : fp + fs "certify_placement" = b at hB ⊢
  obtain ⟨hexp, -⟩ := hpre rd hlow hL
  have hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j) := fun j hj => (hexp j hj).2
  have h2 := memL_one hB (b := b) (w := κs.map (gen ^ ·)) (by simp [bufL, bases])
  have h99 := memL_one hB (b := b + 92) (w := (stackOrder κs).map (gen ^ ·)) (by simp [bufL, bases])
  have h100 := memL_one hB (b := b + 92 + 92) (w := (stackOffsets κs).1.map (gen ^ ·))
    (by simp [bufL, bases])
  obtain ⟨σ, s0, s1, s2, s99, s100, hh, hpk, s106, s109, s114, sR⟩ :=
    cp_honest (C := coreProgram.Rel rd) (hlow.mono hκ) hsq κs hlen (hκf rd hlow hL) _ _ _ h99 h2 h100
  obtain rfl : outs = [] := by match outs, ho with | [], _ => rfl
  refine ⟨σ, ?_, dispOk_of (by rw [cp_disps]; simp), ?_, ?_, ?_, ?_, ?_⟩
  · show [σ (.n 0), σ (.n 1)] = _; rw [s0, s1]
  · rw [core13_body]
    exact hh _ (by rw [stackTotal_eq])
  · rw [cp_allocs]; rfl
  · rw [cp_allocs]
    simp only [List.map_cons, List.map_nil]
    rw [s2, s99, s100]; rfl
  · rw [cp_calls]; trivial
  · intro q hq
    have hb := List.all_eq_true.mp cp_loads q hq
    obtain ⟨p, off⟩ := q
    simp only [cpLoadB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.any_eq_true, List.mem_range] at hb
    have hsqK : IsInK sq := (hsq 0 (by omega)).1
    have hW2 : (b, κs.map (gen ^ ·)) ∈ bufL b [92, 92, 92] [κs.map (gen ^ ·),
        (stackOrder κs).map (gen ^ ·), (stackOffsets κs).1.map (gen ^ ·)] := by simp [bufL, bases]
    have hW100 : (b + 92 + 92, (stackOffsets κs).1.map (gen ^ ·)) ∈ bufL b [92, 92, 92]
        [κs.map (gen ^ ·), (stackOrder κs).map (gen ^ ·), (stackOffsets κs).1.map (gen ^ ·)] := by
      simp [bufL, bases]
    have hl2 : (κs.map (gen ^ ·)).length = 92 := by simp [hlen]
    have hl100 : ((stackOffsets κs).1.map (gen ^ ·)).length = 92 := by
      simp [stackOffsets_length, hlen]
    have hsqA : ∀ k < 34, ∃ i, (sq * gen ^ k).limb 0 * Parameters.gpow 0 = Parameters.gpow i ∧
        RegionL Lin i := fun k hk => by
      obtain ⟨i, hi, hr⟩ := addr_in_region hallSq hlow hL (j := k) (by simp; omega)
      exact ⟨i, by rw [limb_mul_gen_pow' hsqK, Nat.add_zero]; exact hi, hr⟩
    rcases hb with (⟨rfl, hlo⟩ | ⟨rfl | rfl, hlo⟩) | ⟨rfl, ((rfl | rfl) | rfl) | ⟨r, hr, (rfl | rfl) | rfl⟩⟩
    · obtain ⟨i, hi, hr⟩ := addr_in_region hkb8 hlow hL (j := off) (by simp [hl]; omega)
      exact ⟨i, by rw [s0]; exact hi, Or.inl hr⟩
    · exact ⟨b + off, by rw [s2, addr_k], Or.inr (region_buf hW2 (by rw [hl2]; exact hlo))⟩
    · exact ⟨b + 92 + off, by rw [s99, addr_k], Or.inr (region_buf (w := (stackOrder κs).map (gen ^ ·))
        (by simp [bufL, bases]) (by simp [stackOrder_length, hlen]; exact hlo))⟩
    · exact ⟨b + cpPi κs 0, by rw [s106, addr_gen, Nat.add_zero],
        Or.inr (region_buf hW2 (by rw [hl2]; exact (hpk 0 (by omega)).1))⟩
    · exact ⟨b + 92 + 92 + cpPi κs 0, by rw [s109, addr_gen, Nat.add_zero],
        Or.inr (region_buf hW100 (by rw [hl100]; exact (hpk 0 (by omega)).1))⟩
    · obtain ⟨i, hi, hr⟩ := hsqA _ (hpk 0 (by omega)).2
      exact ⟨i, by rw [s114]; exact hi, Or.inl hr⟩
    · exact ⟨b + cpPi κs (r + 1), by rw [(sR r hr).1, addr_gen, Nat.add_zero],
        Or.inr (region_buf hW2 (by rw [hl2]; exact (hpk (r + 1) (by omega)).1))⟩
    · exact ⟨b + 92 + 92 + cpPi κs (r + 1), by rw [(sR r hr).2.1, addr_gen, Nat.add_zero],
        Or.inr (region_buf hW100 (by rw [hl100]; exact (hpk (r + 1) (by omega)).1))⟩
    · obtain ⟨i, hi, hr'⟩ := hsqA _ (hpk (r + 1) (by omega)).2
      exact ⟨i, by rw [(sR r hr).2.2]; exact hi, Or.inl hr'⟩

/-- **`certify_placement` is complete, placed** (TRIAGE #41): `CompletePlaceAt`, on memories
defined below `2^7`. -/
theorem certify_placement_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 7 ≤ κ) : CompletePlaceAt fs cert κ PCtx :=
  fun lp sq kb lm hs Lin h1 h2 h3 h4 h5 =>
    (certify_placement_completeAtB fs cert hκ lp sq kb lm hs Lin h1 h2 h3 h4 h5).toCompleteAtD

end
end LeanVM.Guest.B1
