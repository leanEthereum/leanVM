/-
  LeanVM.Guest.B1.Main.MainGoalsHL5TB

  `main`'s honest children loop within a bound before the memory (`CompleteAtDTB`): `l5_stepAtT`,
  `l5_completeAtT`, `mainGoalL5T` (same proofs), each iteration's callees within their bounds.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T
public import LeanVM.Guest.B1.Main.KidCoverAtB
public import LeanVM.Guest.B1.Main.ChildListGoalsTB
public import LeanVM.Guest.AcceptableChild

/-!
# The children loop, bounded

`l5K SB Bx Bs Bv`: an iteration's words but its frame and its tail call's: its claim lists'
digests (`Bx`, `Bs`), `statement_digest` (`SB`), `verify_sub` (`Bv`). `l5ChainB`: the chain's words. `l5_stepAtTB`,
`l5_completeAtTB`; `VerifySubGoalsTB`, `MainGoalL5TB`, `l5B`, `mainGoalL5TB`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest (DeployedLimits)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds regionL_of_mem limb0_gen_pow_mul exists_of_length_succ
  fn_name_of_find)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB KidsDTB kidsBoundL Returns Kid OutsOk CallsMatch RegionsOk outRegion
  DisjL Within disj_append disj_nil kidsFromIn_of_kidsD regionsOk_of within_append bufL bufL_within
  bufL_disj bufL_region LowDef)

@[expose] public section

/-- **An iteration's words but its frame and its tail call's.** -/
def l5K (SB : String → ℕ) (Bx Bs Bv : ℕ) : ℕ := Bx + Bs + SB "statement_digest" + Bv

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 20000 in
/-- **One child of `__loop4` within its bound, placed, its tree exposed**: `l5_stepAtT` (same
proof), its callees within their bounds, the tail call within `Bt`. -/
theorem l5_stepAtTB (SB : String → ℕ)
    (hSD : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest"))
    {Bt Bv Bx Bs : ℕ} {Lin : Layout} {W D Pi Cr nk c : ℕ}
    {lxt cover lxs lst spc lss s0 s1 gsq cfresh : E} {k : KidH} {Px Ps Pv Tt : Tree → Prop}
    (hnk : nk < 2 ^ 34) (hc : c + 1 ≤ nk) (hs01 : AllCanonical [s0, s1])
    (hk : KidOkC fs cert Lin W D Pi Cr lxt cover lxs lst spc lss s0 s1 gsq cfresh c k)
    (htail : c + 1 < nk → CompleteAtDTB fs cert 20 "__loop4" Lin
      [gen ^ (c + 1), gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns []) Tt Bt)
    (hVT : CompleteAtDTB fs cert 20 "verify_sub" Lin
      [(k.pi s0 s1).1, (k.pi s0 s1).2, s0, s1, gsq, cfresh * gen ^ (24 * c)] (Returns []) Pv Bv)
    (hXT : CompleteAtDTB fs cert 20 "child_claim_list_digest" Lin [lxt, cover, k.base, lxs, gen ^ k.ex]
      (Returns [k.cx.1, k.cx.2]) Px Bx)
    (hST : CompleteAtDTB fs cert 20 "child_claim_list_digest" Lin
      [lst, spc, k.base * gen ^ k.ex, lss, gen ^ k.es] (Returns [k.cs.1, k.cs.2]) Ps Bs) :
    CompleteAtDTB fs cert 20 "__loop4" Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns []) (L5Node k Px Ps Pv Tt)
      (fs "__loop4" + (if c + 1 < nk then Bt else fs "__loop4") + l5K SB Bx Bs Bv) := by
  intro fp
  -- the rest of the loop
  obtain ⟨nt, Lt, hnt, hWt, hDt, hRt⟩ : ∃ nt Lt, nt ≤ (if c + 1 < nk then Bt else fs "__loop4") ∧
      Within Lt (fp + fs "__loop4") nt ∧ DisjL Lt ∧
      ∀ rd, LowDef 20 rd → MemL rd (Lt ++ Lin) →
        if decide (c + 1 ≠ nk) = true then
          RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs "__loop4") nt "__loop4"
            [gen ^ (c + 1), gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
              gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] [] Tt
        else nt = fs "__loop4" := by
    by_cases hlast : c + 1 = nk
    · exact ⟨fs "__loop4", [], by simp [hlast], fun q hq => by simp at hq, List.Pairwise.nil,
        fun _ _ _ => by simp [hlast]⟩
    · obtain ⟨nt, Lt, rt, Lot, hnB, ⟨rfl, rfl⟩, hW, hD, hR⟩ := htail (by omega) (fp + fs "__loop4")
      refine ⟨nt, Lt, by simpa [show c + 1 < nk by omega] using hnB, by simpa using hW,
        by simpa using hD, fun rd hl hm => ?_⟩
      simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte]
      exact hR rd hl (by simpa using hm)
  set P1 := fp + fs "__loop4" + nt with hP1
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
  have ksd := statement_completeAtB fs cert (κ := 20) (Lin := Lin)
      (args := [s0, s1, k.cx.1, k.cx.2, k.cs.1, k.cs.2, k.da.1, k.da.2, gen ^ Cr * gen ^ (24 * c)])
      (rets := [(k.pi s0 s1).1, (k.pi s0 s1).2]) SB hSD fun rd hm => by
    obtain ⟨-, -, -, -, -, -, hdef⟩ := hk.mem rd hm
    refine ⟨k.defer, hk.defer_len, by rw [← pow_add]; exact hdef, ?_, rfl⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs01 _ (by simp)
    · exact hs01 _ (by simp)
    all_goals exact hk.can _ (by simp)
  have hokB : KidsDTB fs cert 20 ks (l5Ts4 Px Ps Pv) [Bx, Bs, SB "statement_digest", Bv] :=
    ⟨fun _ => hXT, fun _ => hST, fun _ => ksd, fun _ => hVT, trivial⟩
  obtain ⟨Nk, Lk, outs, hNB, hoo, hW, hD, -, hKids⟩ :=
    B1.kidsFromInT_of_kidsDTB (fs := fs) (cert := cert) 20 ks (l5Ts4 Px Ps Pv)
      [Bx, Bs, SB "statement_digest", Bv] hokB P1
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
  -- the layout
  refine ⟨fs "__loop4" + nt + Nk, Lt ++ Lk, [], [], by simp only [l5K]; omega, ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append hDt hD hWt hW (by omega), fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin⟩ := Main.memL_append.mp hm
  obtain ⟨hmt, hLk⟩ := Main.memL_append.mp hm1
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
      [⟨"__loop4", [.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11,
        .n 12, .n 13, .n 14, .n 15], [], decide (c + 1 ≠ nk)⟩] := by
    rw [hpc, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.callS =
      [(none, "child_claim_list_digest", [.n 3, .n 4, .n 17, .n 5, .n 18], [.n 23, .n 24]),
        (none, "child_claim_list_digest", [.n 6, .n 7, .n 25, .n 8, .n 19], [.n 26, .n 27]),
        (none, "statement_digest", [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 36, .n 37, .n 33],
          [.n 38, .n 39]),
        (none, "verify_sub", [.n 38, .n 39, .n 11, .n 12, .n 14, .n 48], []),
        (some (.n 53), "__loop4", [.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9,
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
  have hparams : (coreProgram.getD 38 default).params.map σ = args := by
    rw [l5_params]
    refine List.ext_getElem (by simp [hargs]) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    rw [pr i (by simpa using h1), List.getD_eq_getElem _ _ h2]
  have h := relAtInWT_of_walk_loop (P := coreProgram) (Tt := Tt) (Ts := l5Ts4 Px Ps Pv) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (Rt := RegionL Lin) (Dt := RegionL []) (fp := fp)
    (m := nt) (N := Nk) (args := args)
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4] i)
    coreProgram_wf find_l5 l5_loop hparams hw' rfl hev hcalls
    (by
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
  · rw [hal] at h
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

/-- **`__loop4`'s words over its last `t + 1` iterations from child `c`**: each iteration's frame
and constant part `K c`, the last one's phantom tail call's frame. -/
def l5ChainB (fs : String → ℕ) (K : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, c => fs "__loop4" + fs "__loop4" + K c
  | t + 1, c => fs "__loop4" + l5ChainB fs K t (c + 1) + K c

/-- **`__loop4` is complete within `l5ChainB`, placed, its trees exposed**: `l5_completeAtT`, each
iteration's callees within their bounds. -/
theorem l5_completeAtTB (SB : String → ℕ)
    (hSD : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest"))
    {Bv Bxs Bss : ℕ → ℕ} {Lin : Layout} {W D Pi Cr nk : ℕ}
    {lxt cover lxs lst spc lss s0 s1 gsq cfresh : E} {kid : ℕ → KidH} {Pxs Pss Pvs : ℕ → Tree → Prop}
    (hnk : nk < 2 ^ 34) (hs01 : AllCanonical [s0, s1])
    (hk : ∀ c < nk, KidOkC fs cert Lin W D Pi Cr lxt cover lxs lst spc lss s0 s1 gsq cfresh c
      (kid c))
    (hVT : ∀ c < nk, CompleteAtDTB fs cert 20 "verify_sub" Lin
      [((kid c).pi s0 s1).1, ((kid c).pi s0 s1).2, s0, s1, gsq, cfresh * gen ^ (24 * c)]
      (Returns []) (Pvs c) (Bv c))
    (hXT : ∀ c < nk, CompleteAtDTB fs cert 20 "child_claim_list_digest" Lin
      [lxt, cover, (kid c).base, lxs, gen ^ (kid c).ex] (Returns [(kid c).cx.1, (kid c).cx.2])
      (Pxs c) (Bxs c))
    (hST : ∀ c < nk, CompleteAtDTB fs cert 20 "child_claim_list_digest" Lin
      [lst, spc, (kid c).base * gen ^ (kid c).ex, lss, gen ^ (kid c).es]
      (Returns [(kid c).cs.1, (kid c).cs.2]) (Pss c) (Bss c)) :
    ∀ c < nk, CompleteAtDTB fs cert 20 "__loop4" Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns [])
      (L5From (fun c => (kid c).ex) (fun c => (kid c).es) Pxs Pss Pvs (nk - c) c)
      (l5ChainB fs (fun c => l5K SB (Bxs c) (Bss c) (Bv c)) (nk - c - 1) c) := by
  have key : ∀ t c, c + 1 + t = nk → CompleteAtDTB fs cert 20 "__loop4" Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns [])
      (L5From (fun c => (kid c).ex) (fun c => (kid c).es) Pxs Pss Pvs (t + 1) c)
      (l5ChainB fs (fun c => l5K SB (Bxs c) (Bss c) (Bv c)) t c) := by
    intro t
    induction t with
    | zero =>
      intro c hc
      refine (l5_stepAtTB fs cert SB hSD (Bt := 0) (Tt := fun _ => False) hnk (by omega) hs01
        (hk c (by omega)) (fun h => absurd h (by omega)) (hVT c (by omega)) (hXT c (by omega))
        (hST c (by omega))).mono (le_of_eq ?_) fun _ ht => ht
      simp only [l5ChainB, show ¬ c + 1 < nk by omega, ↓reduceIte]
    | succ t ih =>
      intro c hc
      refine (l5_stepAtTB fs cert SB hSD hnk (by omega) hs01 (hk c (by omega))
        (fun _ => ih (c + 1) (by omega)) (hVT c (by omega)) (hXT c (by omega)) (hST c (by omega))).mono
        (le_of_eq ?_) fun _ ht => ht
      simp only [l5ChainB, show c + 1 < nk by omega, ↓reduceIte]
  intro c hc
  rw [show nk - c = nk - c - 1 + 1 by omega]
  exact key (nk - c - 1) c (by omega)

variable {fs cert}

/-- **Each child's `verify_sub` call complete within `Bv c`, by a tree satisfying `Pvs c`.** -/
def VerifySubGoalsTB (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (Pvs : ℕ → Tree → Prop) (Bv : ℕ → ℕ) : Prop :=
  ∀ c (hc : c < w.children.length), CompleteAtDTB fs cert 20 "verify_sub" (hLmain fs fp seed s w)
    [(digestHalves (statementDigest seed w.children[c].statement)).1,
      (digestHalves (statementDigest seed w.children[c].statement)).2,
      (digestHalves seed).1, (digestHalves seed).2, (hm fs fp seed s w).et,
      (hm fs fp seed s w).a400 * gen ^ (24 * c)] (Returns []) (Pvs c) (Bv c)

theorem VerifySubGoalsTB.toT {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    {Pvs : ℕ → Tree → Prop} {Bv : ℕ → ℕ} (h : VerifySubGoalsTB fs cert fp seed s w Pvs Bv) :
    VerifySubGoalsT fs cert fp seed s w Pvs := fun c hc => (h c hc).toDT

theorem VerifySubGoalsTB.goals {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    {Pvs : ℕ → Tree → Prop} {Bv : ℕ → ℕ} (h : VerifySubGoalsTB fs cert fp seed s w Pvs Bv) :
    VerifySubGoals fs cert fp seed s w := h.toT.goals

theorem VerifySubGoalsTB.mono {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    {Pvs : ℕ → Tree → Prop} {Bv Bv' : ℕ → ℕ} (h : VerifySubGoalsTB fs cert fp seed s w Pvs Bv)
    (hB : ∀ c < w.children.length, Bv c ≤ Bv' c) : VerifySubGoalsTB fs cert fp seed s w Pvs Bv' :=
  fun c hc => (h c hc).mono (hB c hc) fun _ ht => ht

/-- The children's loop complete within `B5` by trees satisfying `T5`. -/
def MainGoalL5TB (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (T5 : Tree → Prop) (B5 : ℕ) : Prop :=
  (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTB fs cert 20 "__loop4" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns []) T5 B5

theorem MainGoalL5TB.toT {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    {T5 : Tree → Prop} {B5 : ℕ} (h : MainGoalL5TB fs cert fp seed s w T5 B5) :
    MainGoalL5T fs cert fp seed s w T5 := fun hn => (h hn).toDT

/-- **The honest children loop's words bound**: `l5ChainB` over the `nc` children, child `c`'s
iteration within its frame and its callees' bounds (`l5K`). -/
def l5B (fs : String → ℕ) (SB : String → ℕ) (Bxs Bss Bv : ℕ → ℕ) (w : NodeWitness) : ℕ :=
  l5ChainB fs (fun c => l5K SB (Bxs c) (Bss c) (Bv c)) (w.children.length - 1) 0

variable (fs cert)

/-- **`main`'s honest children loop is complete within `l5B`, its trees exposed** (`L5Hinted w Pvs`): under the
hypotheses of `mainGoalL5`, each child's `verify_sub` call by a tree satisfying `Pvs c`. -/
theorem mainGoalL5TB (SB : String → ℕ)
    (hSD : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest"))
    {Bv Bxs Bss : ℕ → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    {bytecode : List K} {Pxs Pss Pvs : ℕ → Tree → Prop} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (hrel : NodeRelation bytecode seed s w) (hl : DeployedLimits s w)
    (hV : VerifySubGoalsTB fs cert fp seed s w Pvs Bv)
    (hX : ChildListGoalsTB fs cert fp seed s w Pxs Pss Bxs Bss) :
    MainGoalL5TB fs cert fp seed s w (L5Hinted w Pxs Pss Pvs) (l5B fs SB Bxs Bss Bv w) := by
  intro hnc
  have hnc16 := hl.atMostSixteenChildren
  have h := l5_completeAtTB fs cert SB hSD (Bv := Bv) (Bxs := Bxs) (Bss := Bss)
    (Lin := hLmain fs fp seed s w) (W := hP fs fp seed s w 8) (D := hP fs fp seed s w 4)
    (Pi := hP fs fp seed s w 5) (Cr := hP fs fp seed s w 7) (nk := w.children.length)
    (kid := hKid s w) (Pxs := Pxs) (Pss := Pss) (Pvs := Pvs) (by omega)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (digestScalars_canonical _).1
      · exact (digestScalars_canonical _).2)
    (fun c hc => kidOk cert hbl hrel hl hV.goals (CompleteAtDTB.toDT (hX c hc).1).toD
      (CompleteAtDTB.toDT (hX c hc).2).toD hc)
    (fun c hc => by
      have hsh := kid_shapes hbl hrel _ (List.getElem_mem hc)
      rw [hKid_pi seed (s := s) hc (by simp [DeferredClaim.cells, hsh.2, bytecodeVars])]
      exact hV c hc) (fun c hc => (hX c hc).1) (fun c hc => (hX c hc).2) 0 (by have : w.children.length ≠ 0 := hnc; omega)
  rw [pow_zero, Nat.sub_zero] at h
  exact h

end
end LeanVM.Guest.B1.Main
