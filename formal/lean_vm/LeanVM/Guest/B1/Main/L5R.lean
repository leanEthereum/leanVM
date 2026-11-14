/-
  LeanVM.Guest.B1.Main.L5R

  `main`'s honest children loop within its bound, its callees' trees satisfying predicates of the memory: `l5_stepAtTB`,
  `l5_completeAtTB`, `mainGoalL5TB` (same proofs) over `CompleteAtDTBR`.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5TB
public import LeanVM.Guest.Budget.BoundedL

/-!
# The children loop, its callees' predicates of the memory

`l5_stepAtTBR`, `l5_completeAtTBR`: `l5_stepAtTB`, `l5_completeAtTB` with the callees `CompleteAtDTBR`.
`VerifySubGoalsTBR`, `ChildListGoalsTBR`: each child's `verify_sub` call and claim lists' digests so;
`mainGoalL5TBR`: `mainGoalL5TB` with them.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds regionL_of_mem limb0_gen_pow_mul exists_of_length_succ
  fn_name_of_find)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB CompleteAtDTBR CompleteAtL CompleteAtLR completeAtLR_tail KidsDTB KidsDTBR
  kidsBoundL Returns Kid OutsOk CallsMatch RegionsOk outRegion
  DisjL Within disj_append disj_nil kidsFromIn_of_kidsD regionsOk_of within_append bufL bufL_within
  bufL_disj bufL_region LowDef)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

variable (fs cert)

set_option maxRecDepth 20000 in
/-- **One child of `main_loop4` within its bound, placed, its tree exposed**: `l5_stepAtTB` (same proof), its
callees' and tail call's trees satisfying predicates of the memory. -/
theorem l5_stepAtTBR (SB : String → ℕ)
    (hSD : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest"))
    {Bt Bv Bx Bs : ℕ} {Lin : Layout} {W D Pi Cr nk c : ℕ}
    {lxt cover lxs lst spc lss s0 s1 gsq cfresh : E} {k : KidH} {Px Ps Pv Tt : Reader → Tree → Prop}
    (hnk : nk < 2 ^ 34) (hc : c + 1 ≤ nk)
    (hk : KidOkC fs cert Lin W D Pi Cr lxt cover lxs lst spc lss s0 s1 gsq cfresh c k)
    (htail : c + 1 < nk → CompleteAtLR fs cert 23 name% «main_loop4» Lin
      [gen ^ (c + 1), gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns []) Tt (· ≤ Bt))
    (hVT : CompleteAtDTBR fs cert 20 "verify_sub" Lin
      [(k.pi s0 s1).1, (k.pi s0 s1).2, s0, s1, gsq, cfresh * gen ^ (24 * c)] (Returns []) Pv Bv)
    (hXT : CompleteAtDTBR fs cert 23 "child_claim_list_digest" Lin [lxt, cover, k.base, lxs, gen ^ k.ex]
      (Returns [k.cx.1, k.cx.2]) Px Bx)
    (hST : CompleteAtDTBR fs cert 23 "child_claim_list_digest" Lin
      [lst, spc, k.base * gen ^ k.ex, lss, gen ^ k.es] (Returns [k.cs.1, k.cs.2]) Ps Bs) :
    CompleteAtLR fs cert 23 name% «main_loop4» Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns []) (fun rd => L5Node k (Px rd) (Ps rd) (Pv rd) (Tt rd))
      (· ≤ fs name% «main_loop4» + (if c + 1 < nk then Bt else fs name% «main_loop4») +
        l5K SB Bx Bs Bv) := by
  -- the rest of the loop
  obtain ⟨Bt', hRest⟩ := completeAtLR_tail (fs := fs) (cert := cert) (g := name% «main_loop4»)
    (last := c + 1 = nk) fun h => htail (by omega)
  refine ⟨fs name% «main_loop4» + Bt', fun fp cur hcur => ?_⟩
  -- the callees
  let ks : List Kid :=
    [⟨"child_claim_list_digest", true, [lxt, cover, k.base, lxs, gen ^ k.ex], Lin,
        Returns [k.cx.1, k.cx.2]⟩,
      ⟨"child_claim_list_digest", true, [lst, spc, k.base * gen ^ k.ex, lss, gen ^ k.es], Lin,
        Returns [k.cs.1, k.cs.2]⟩,
      ⟨"statement_digest", true, [s0, s1, k.cx.1, k.cx.2, k.cs.1, k.cs.2, k.da.1, k.da.2,
        gen ^ Cr * gen ^ (24 * c)], Lin, Returns [(k.pi s0 s1).1, (k.pi s0 s1).2]⟩,
      ⟨"verify_sub", true, [(k.pi s0 s1).1, (k.pi s0 s1).2, s0, s1, gsq,
        cfresh * gen ^ (24 * c)], Lin, Returns []⟩]
  have ksd := statement_completeAtB fs cert (κ := 23) (Lin := Lin)
      (args := [s0, s1, k.cx.1, k.cx.2, k.cs.1, k.cs.2, k.da.1, k.da.2, gen ^ Cr * gen ^ (24 * c)])
      (rets := [(k.pi s0 s1).1, (k.pi s0 s1).2]) SB hSD fun rd hm => by
    obtain ⟨-, -, -, -, -, -, hdef⟩ := hk.mem rd hm
    exact ⟨k.defer, hk.defer_len, by rw [← pow_add]; exact hdef, rfl⟩
  have hokB : KidsDTBR fs cert 23 ks (fun rd => l5Ts4 (Px rd) (Ps rd) (Pv rd)) [Bx, Bs, SB "statement_digest", Bv] :=
    ⟨fun _ => hXT, fun _ => hST, fun _ => ksd.toR, fun _ => hVT.lowMono (by norm_num), trivial⟩
  obtain ⟨Nk, Lk, outs, hNB, hoo, hW, hD, -, hKids⟩ :=
    B1.kidsFromInT_of_kidsDTBR (fs := fs) (cert := cert) 23 ks (fun rd => l5Ts4 (Px rd) (Ps rd) (Pv rd))
      [Bx, Bs, SB "statement_digest", Bv] hokB cur
  have hNB' : Nk ≤ Bx + Bs + SB "statement_digest" + Bv := by
    refine hNB.trans ?_
    simp [ks, kidsBoundL]; omega
  have hl0 : outs.length = 4 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain ⟨o4, t4, rfl, hl4⟩ := exists_of_length_succ hl3
  obtain rfl := List.eq_nil_of_length_eq_zero hl4
  obtain ⟨h1, h2, h3, h4, -⟩ := hoo
  obtain ⟨nt, Lt, hlt, hBdt, hWt, hDt, hRt⟩ :=
    hRest (fp + fs name% «main_loop4») (cur + Nk) (by omega)
  -- the layout
  refine ⟨Nk + nt, Lk ++ Lt, [], [], ?_, ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append hD hDt hW hWt le_rfl, fun rd hlow hm => ?_⟩
  · show _ ≤ _
    simp only [l5K]
    by_cases hlast : c + 1 = nk
    · obtain ⟨rfl, rfl⟩ := hlt hlast
      simp only [show ¬ c + 1 < nk by omega, ↓reduceIte]
      omega
    · have := hBdt hlast
      simp only [show c + 1 < nk by omega, ↓reduceIte]
      omega
  · rw [List.nil_append, within_append]
    exact ⟨hW.mono le_rfl (by omega), hWt.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin⟩ := Main.memL_append.mp hm
  obtain ⟨hLk, hmt⟩ := Main.memL_append.mp hm1
  have ht := hRt rd hlow (Main.memL_append.mpr ⟨hmt, hLin⟩)
  obtain ⟨hb0, hb1, hd0, hd1, hpi0, hpi1, -⟩ := hk.mem rd hLin
  obtain ⟨rW0, rW1, rD0, rD1, rPi0, rPi1⟩ := hk.reg
  -- the block
  have hV := l5_core (rd := rd) (c := c) (N := gen ^ nk) (written := gen ^ W) (lxt := lxt)
    (cover := cover) (lxs := lxs) (lst := lst) (spc := spc) (lss := lss) (carried := gen ^ Cr)
    (dadig := gen ^ D) (s0 := s0) (s1 := s1) (cpi := gen ^ Pi) (gsq := gsq)
    (cfresh := cfresh) (cx0 := k.cx.1) (cx1 := k.cx.2) (cs0 := k.cs.1) (cs1 := k.cs.2)
    (d0 := k.da.1) (d1 := k.da.2) (p0 := (k.pi s0 s1).1) (p1 := (k.pi s0 s1).2)
    hlow hk.ex_lt hk.es_lt
    (by rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hb0)
    (by rw [gen_sq', loadHolds_mul_gen_pow, Nat.add_zero]; exact hd0)
    (by rw [gen_sq', loadHolds_mul_gen_pow]; exact hd1)
    (by rw [gen_sq', loadHolds_mul_gen_pow, Nat.add_zero]; exact hpi0)
    (by rw [gen_sq', loadHolds_mul_gen_pow]; exact hpi1)
    (by rw [loadHolds_mul_gen_pow]; exact hb1)
  set args : List E := [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
    gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] with hargs
  set σ := l5σ rd args (l5W k.ex k.es k.cx.1 k.cx.2 k.cs.1 k.cs.2 (k.pi s0 s1).1 (k.pi s0 s1).2)
    with hσ
  have pr : ∀ i (hi : i < 16), σ (.n i) = args.getD i 0 := hV.par
  -- the path
  have hw' := Main.walk_straight σ [] (l5Pre ++ [l5Tail]) l5Pre_straight
  rw [← l5Body_split, l5Body] at hw'
  rw [← l5_body] at hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ l5Pre_straight
  have hal : allocs σ ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) = [] := by
    rw [hpa, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.allocSz = [] from rfl]; rfl
  have h59 : decide (σ (.n 53) ≠ 0) = decide (c + 1 ≠ nk) := by
    rw [hV.v59]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
      fun h he => h ?_⟩
    exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  have hcalls : calls ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) =
      [⟨"child_claim_list_digest", [.n 3, .n 4, .n 17, .n 5, .n 18], [.n 23, .n 24], true⟩,
        ⟨"child_claim_list_digest", [.n 6, .n 7, .n 25, .n 8, .n 19], [.n 26, .n 27], true⟩,
        ⟨"statement_digest", [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 36, .n 37, .n 33],
          [.n 38, .n 39], true⟩,
        ⟨"verify_sub", [.n 38, .n 39, .n 11, .n 12, .n 14, .n 48], [], true⟩] ++
      [⟨name% «main_loop4», [.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
          .n 11,
        .n 12, .n 13, .n 14, .n 15], [], decide (c + 1 ≠ nk)⟩] := by
    rw [hpc, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.callS =
      [(none, "child_claim_list_digest", [.n 3, .n 4, .n 17, .n 5, .n 18], [.n 23, .n 24]),
        (none, "child_claim_list_digest", [.n 6, .n 7, .n 25, .n 8, .n 19], [.n 26, .n 27]),
        (none, "statement_digest", [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 36, .n 37, .n 33],
          [.n 38, .n 39]),
        (none, "verify_sub", [.n 38, .n 39, .n 11, .n 12, .n 14, .n 48], []),
        (some (.n 53), name% «main_loop4», [.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8,
            .n 9,
          .n 10, .n 11, .n 12, .n 13, .n 14, .n 15], [])] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, h59, List.cons_append, List.nil_append]
  have hev : ∀ e ∈ (l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun s hs => ?_
    rcases List.mem_append.mp hs with hs | hs
    · have hk' := List.all_eq_true.mp l5_kinds s hs
      match s, hk' with
      | .atom a, _ => exact hV.atoms a (Da.mem_atomsIn hs)
      | .call .., _ => trivial
      | .callIf .., hk' => simp [l5Kind] at hk'
      | .ite .., hk' => simp [l5Kind] at hk'
      | .match_ .., hk' => simp [l5Kind] at hk'
      | .dispatch .., hk' => simp [l5Kind] at hk'
      | .ret _, hk' => simp [l5Kind] at hk'
    · rw [List.mem_singleton] at hs
      subst hs
      show IsInK (σ (.n 53))
      rw [hV.v59]; exact gen_pow_add_isInK _ _
  have hparams : (coreProgram.getD idx% «main_loop4» default).params.map σ = args := by
    rw [l5_params]
    refine List.ext_getElem (by simp [hargs]) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    rw [pr i (by simpa using h1), List.getD_eq_getElem _ _ h2]
  have h := relAtInWT_of_walk_loop (P := coreProgram) (Tt := Tt rd) (Ts := l5Ts4 (Px rd) (Ps rd) (Pv rd)) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (Rt := RegionL Lin) (Dt := RegionL []) (fp := fp)
    (c := cur) (Bt := Bt') (m := nt) (N := Nk) (args := args)
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4] i)
    coreProgram_wf find_l5 l5_loop hparams hw' rfl hev hcalls
    (by
      rw [hal, List.sum_nil, Nat.add_zero]
      by_cases hlast : c + 1 = nk
      · simpa [hlast] using ht
      · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
        rw [show [V.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11,
          .n 12, .n 13, .n 14, .n 15].map σ = [σ (.n 55), σ (.n 1), σ (.n 2),
          σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10),
          σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15)] from rfl,
          hV.v61, pr 1 (by omega), pr 2 (by omega), pr 3 (by omega), pr 4 (by omega),
          pr 5 (by omega), pr 6 (by omega), pr 7 (by omega), pr 8 (by omega), pr 9 (by omega),
          pr 10 (by omega), pr 11 (by omega), pr 12 (by omega), pr 13 (by omega), pr 14 (by omega),
          pr 15 (by omega)]
        exact ht)
    (by rw [hal, hpd, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.allocSz = [] from rfl]; rfl)
    (fun q hq => by
      rw [hpad, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    rfl ?_ (fun i hi => Or.inl hi) ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · rw [hal, List.sum_nil, Nat.zero_add] at h
    obtain ⟨t, ht, ks', rfl, hk'⟩ := h
    refine ⟨_, ht, σ, _, ks', rfl, hV.v18, hV.v19, l5_calls σ, ?_⟩
    rw [← l5_calls σ]
    exact hk'
  · rw [hal]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun kd hkd _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 3), σ (.n 4), σ (.n 17), σ (.n 5), σ (.n 18)] = _
        rw [pr 3 (by omega), pr 4 (by omega), hV.v17, pr 5 (by omega), hV.v18]; rfl
      · rw [(h1 rfl).1]; show [σ (.n 23), σ (.n 24)] = _; rw [hV.v29, hV.v30]
      · show [σ (.n 6), σ (.n 7), σ (.n 25), σ (.n 8), σ (.n 19)] = _
        rw [pr 6 (by omega), pr 7 (by omega), hV.v31, pr 8 (by omega), hV.v19]
        rfl
      · rw [(h2 rfl).1]; show [σ (.n 26), σ (.n 27)] = _; rw [hV.v32, hV.v33]
      · show [σ (.n 11), σ (.n 12), σ (.n 23), σ (.n 24), σ (.n 26), σ (.n 27), σ (.n 36),
          σ (.n 37), σ (.n 33)] = _
        rw [pr 11 (by omega), pr 12 (by omega), hV.v29, hV.v30, hV.v32, hV.v33, hV.v42, hV.v43,
          hV.v39]
        rfl
      · rw [(h3 rfl).1]; show [σ (.n 38), σ (.n 39)] = _; rw [hV.v44, hV.v45]
      · show [σ (.n 38), σ (.n 39), σ (.n 11), σ (.n 12), σ (.n 14), σ (.n 48)] = _
        rw [hV.v44, hV.v45, pr 11 (by omega), pr 12 (by omega), pr 14 (by omega), hV.v54]
        rfl
      · rw [(h4 rfl).1]; rfl
    · intro q hq
      simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hq
      rcases hq with hq | hq | hq | hq
      all_goals exact hLin q hq
    · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hkd
      rcases hkd with rfl | rfl | rfl | rfl
      all_goals exact Or.inl (Or.inl hi)
  · intro A hA
    rw [B1.loadAddrs_straight σ _ l5Pre_straight,
      show (l5Pre ++ [l5Tail]).filterMap B1.Stmt.loadS =
        [(.n 16, 0), (.n 35, 0), (.n 35, 1), (.n 41, 0), (.n 42, 1), (.n 50, 1)] from rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rw [hal]
    have hW' : ∀ e, (gen ^ W * gen ^ c).limb 0 * addressOfIndex e = addressOfIndex (W + c + e) :=
        fun e => by
      rw [← pow_add, limb0_gen_pow_mul]
    have hsq : ∀ B e, (gen ^ B * (gen ^ c * gen ^ c)).limb 0 * addressOfIndex e = addressOfIndex (B
        + 2 * c + e) :=
      fun B e => by rw [gen_sq', ← pow_add, limb0_gen_pow_mul]
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨W + c + 0, ?_, Or.inr (Or.inl rW0)⟩
      rw [hV.v16]; exact hW' 0
    · refine ⟨D + 2 * c + 0, ?_, Or.inr (Or.inl rD0)⟩
      rw [hV.v41]; exact hsq D 0
    · refine ⟨D + 2 * c + 1, ?_, Or.inr (Or.inl rD1)⟩
      rw [hV.v41]; exact hsq D 1
    · refine ⟨Pi + 2 * c + 0, ?_, Or.inr (Or.inl rPi0)⟩
      rw [hV.v47]; exact hsq Pi 0
    · refine ⟨Pi + 2 * c + 1, ?_, Or.inr (Or.inl rPi1)⟩
      rw [hV.v48]; exact hsq Pi 1
    · refine ⟨W + c + 1, ?_, Or.inr (Or.inl rW1)⟩
      rw [hV.v56]; exact hW' 1

/-- **`main_loop4` is complete within `l5ChainB`, placed, its trees exposed**: `l5_completeAtTB`, the callees'
trees satisfying predicates of the memory. -/
theorem l5_completeAtTBR (SB : String → ℕ)
    (hSD : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest"))
    {Bv Bxs Bss : ℕ → ℕ} {Lin : Layout} {W D Pi Cr nk : ℕ}
    {lxt cover lxs lst spc lss s0 s1 gsq cfresh : E} {kid : ℕ → KidH} {Pxs Pss Pvs : Reader → ℕ → Tree → Prop}
    (hnk : nk < 2 ^ 34)
    (hk : ∀ c < nk, KidOkC fs cert Lin W D Pi Cr lxt cover lxs lst spc lss s0 s1 gsq cfresh c
      (kid c))
    (hVT : ∀ c < nk, CompleteAtDTBR fs cert 20 "verify_sub" Lin
      [((kid c).pi s0 s1).1, ((kid c).pi s0 s1).2, s0, s1, gsq, cfresh * gen ^ (24 * c)]
      (Returns []) (fun rd => Pvs rd c) (Bv c))
    (hXT : ∀ c < nk, CompleteAtDTBR fs cert 23 "child_claim_list_digest" Lin
      [lxt, cover, (kid c).base, lxs, gen ^ (kid c).ex] (Returns [(kid c).cx.1, (kid c).cx.2])
      (fun rd => Pxs rd c) (Bxs c))
    (hST : ∀ c < nk, CompleteAtDTBR fs cert 23 "child_claim_list_digest" Lin
      [lst, spc, (kid c).base * gen ^ (kid c).ex, lss, gen ^ (kid c).es]
      (Returns [(kid c).cs.1, (kid c).cs.2]) (fun rd => Pss rd c) (Bss c)) :
    ∀ c < nk, CompleteAtDTBR fs cert 23 name% «main_loop4» Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns [])
      (fun rd => L5From (fun c => (kid c).ex) (fun c => (kid c).es) (Pxs rd) (Pss rd) (Pvs rd) (nk - c) c)
      (l5ChainB fs (fun c => l5K SB (Bxs c) (Bss c) (Bv c)) (nk - c - 1) c) := by
  have key : ∀ t c, c + 1 + t = nk → CompleteAtLR fs cert 23 name% «main_loop4» Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns [])
      (fun rd => L5From (fun c => (kid c).ex) (fun c => (kid c).es) (Pxs rd) (Pss rd) (Pvs rd) (t + 1) c)
      (· ≤ l5ChainB fs (fun c => l5K SB (Bxs c) (Bss c) (Bv c)) t c) := by
    intro t
    induction t with
    | zero =>
      intro c hc
      refine (l5_stepAtTBR fs cert SB hSD (Bt := 0) (Tt := fun _ _ => False) hnk (by omega)
        (hk c (by omega)) (fun h => absurd h (by omega)) (hVT c (by omega)) (hXT c (by omega))
        (hST c (by omega))).mono (fun x hx => le_of_le_of_eq hx ?_) fun _ _ ht => ht
      simp only [l5ChainB, show ¬ c + 1 < nk by omega, ↓reduceIte]
    | succ t ih =>
      intro c hc
      refine (l5_stepAtTBR fs cert SB hSD hnk (by omega) (hk c (by omega))
        (fun _ => ih (c + 1) (by omega)) (hVT c (by omega)) (hXT c (by omega)) (hST c (by omega))).mono
        (fun x hx => le_of_le_of_eq hx ?_) fun _ _ ht => ht
      simp only [l5ChainB, show c + 1 < nk by omega, ↓reduceIte]
  intro c hc
  rw [show nk - c = nk - c - 1 + 1 by omega]
  exact (key (nk - c - 1) c (by omega)).toDTBR

variable {fs cert}

/-- **Each child's `verify_sub` call complete within `Bv c`, by a tree satisfying `Pvs rd c` on the memory `rd`.** -/
def VerifySubGoalsTBR (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (Pvs : Reader → ℕ → Tree → Prop) (Bv : ℕ → ℕ) : Prop :=
  ∀ c (hc : c < w.children.length), CompleteAtDTBR fs cert 20 "verify_sub" (hLmain fs fp seed s w)
    [(digestHalves (statementDigest seed w.children[c].statement)).1,
      (digestHalves (statementDigest seed w.children[c].statement)).2,
      (digestHalves seed).1, (digestHalves seed).2, (hm fs fp seed s w).et,
      (hm fs fp seed s w).a400 * gen ^ (24 * c)] (Returns []) (fun rd => Pvs rd c) (Bv c)

theorem VerifySubGoalsTBR.goals {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    {Pvs : Reader → ℕ → Tree → Prop} {Bv : ℕ → ℕ} (h : VerifySubGoalsTBR fs cert fp seed s w Pvs Bv) :
    VerifySubGoals fs cert fp seed s w :=
  fun c hc => ((h c hc).toDTB (T' := fun _ => True) fun _ _ _ => trivial).toDT.toD

/-- **Each child's claim lists' digests complete within `Bxs c`, `Bss c` words, by trees satisfying `Pxs rd c`,
`Pss rd c` on the memory `rd`.** -/
def ChildListGoalsTBR (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (Pxs Pss : Reader → ℕ → Tree → Prop) (Bxs Bss : ℕ → ℕ) : Prop :=
  ∀ c, c < w.children.length →
    CompleteAtDTBR fs cert 23 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a77, (hm fs fp seed s w).a117, (hKid s w c).base,
        gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd), gen ^ (hKid s w c).ex]
      (Returns [(hKid s w c).cx.1, (hKid s w c).cx.2]) (fun rd => Pxs rd c) (Bxs c) ∧
    CompleteAtDTBR fs cert 23 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hKid s w c).base * gen ^ (hKid s w c).ex,
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd), gen ^ (hKid s w c).es]
      (Returns [(hKid s w c).cs.1, (hKid s w c).cs.2]) (fun rd => Pss rd c) (Bss c)

variable (fs cert)

/-- **`main`'s honest children loop is complete within `l5B`, its trees exposed**: `mainGoalL5TB`, the callees'
trees satisfying predicates of the memory. -/
theorem mainGoalL5TBR (SB : String → ℕ)
    (hSD : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest"))
    {Bv Bxs Bss : ℕ → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    {bytecode : List K} {Pxs Pss Pvs : Reader → ℕ → Tree → Prop} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (hrel : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hV : VerifySubGoalsTBR fs cert fp seed s w Pvs Bv)
    (hX : ChildListGoalsTBR fs cert fp seed s w Pxs Pss Bxs Bss) : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop4» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns [])
      (fun rd => L5From (hEx w) (hEs w) (Pxs rd) (Pss rd) (Pvs rd) w.children.length 0)
      (l5B fs SB Bxs Bss Bv w) := by
  intro hnc
  have hnc16 := hl.atMostSixteenChildren
  have h := l5_completeAtTBR fs cert SB hSD (Bv := Bv) (Bxs := Bxs) (Bss := Bss)
    (Lin := hLmain fs fp seed s w) (W := hP fs fp seed s w 8) (D := hP fs fp seed s w 4)
    (Pi := hP fs fp seed s w 5) (Cr := hP fs fp seed s w 7) (nk := w.children.length)
    (kid := hKid s w) (Pxs := Pxs) (Pss := Pss) (Pvs := Pvs) (by omega)
    (fun c hc => kidOk cert hbl hrel hl hV.goals
      (((hX c hc).1.toDTB (T' := fun _ => True) fun _ _ _ => trivial).toDT.toD)
      (((hX c hc).2.toDTB (T' := fun _ => True) fun _ _ _ => trivial).toDT.toD) hc)
    (fun c hc => by rw [hKid_pi seed (s := s) hc]; exact hV c hc) (fun c hc => (hX c hc).1)
    (fun c hc => (hX c hc).2) 0 (by have : w.children.length ≠ 0 := hnc; omega)
  rw [pow_zero, Nat.sub_zero] at h
  exact h

end
end LeanVM.Guest.B1.Main
