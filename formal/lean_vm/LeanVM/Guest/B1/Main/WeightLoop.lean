/-
  LeanVM.Guest.B1.Main.WeightLoop

  Callees, loop helpers and their straight-line iterations complete by trees within weights:
  `kidsFromIn_of_kidsB`, `completeAt_loop` and `loopStep_bufs` with the weights riding along.
-/

module

public import LeanVM.Guest.B1.Main.WeightAt
public import LeanVM.Guest.B1.VerifySub.StaticW

/-!
# Callees and loops within weights

`kidsFromInW_of_kidsW`: callees each `CompleteAtW` (`KidsW`) at their running offsets, within the
sum of their bounds, give `KidsFromInW`. `completeAt_loopW`: a loop helper from its iterations,
iteration `j` weighing its function's weight and `bws j` besides its tail, within `loopSum` at
every weight. `loopStep_bufsW`: `loopStep_bufs`'s iteration within its callees' weights.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB Returns Kid CallsMatch
  OutsOk OutsIn RegionsOk outRegion kidsBound within_append bufL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}

theorem kidsFromInW_dend {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (bws : List (Θ → ℕ)) (Dacc : ℕ → Prop) (b n : ℕ) {D D' : ℕ → Prop},
      (∀ i, D' i → D i) → KidsFromInW fs cert w rd σ R Dacc cs bws b n D →
      KidsFromInW fs cert w rd σ R Dacc cs bws b n D'
  | [], _, _, _, _, _, _, hD, ⟨hn, h⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: _, [], _, _, _, _, _, _, h => h.elim
  | _ :: cs, _ :: bws, _, _, _, _, _, hD, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, hR, hc, kidsFromInW_dend cs bws _ _ _ hD hk⟩

/-- **`kidsFromIn_of_kidsB` within weights.** -/
theorem kidsFromInW_of_kidsW (κ : ℕ) : ∀ (ks : List Kid) (bs : List ℕ) (bws : List (Θ → ℕ)),
    KidsW fs cert w κ ks bs bws → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      DisjL L ∧ N ≤ bs.sum ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInW fs cert w rd σ R Dacc cs bws b N (fun i => Dacc i ∨ outRegion ks outs i)
  | [], [], [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, disj_nil, le_rfl, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | [], _ :: _, _, h, _ => h.elim
  | [], [], _ :: _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], h, _ => h.elim
  | k :: ks, B :: bs, Bw :: bws, ⟨hok, hnk, hks⟩, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hnb, hrel⟩ := hok ht b
      obtain ⟨N, L, outs, ho, hW, hD, hNb, hI, hK⟩ := kidsFromInW_of_kidsW κ ks bs bws hks (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_,
        disj_append hd hD hw hW le_rfl, by simp only [List.sum_cons]; omega,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := memL_append.mp hL
          simp only [Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            exact hrel rd hlow (memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromInW_dend cs bws _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · have ht' : k.taken = false := by simpa using ht
      obtain ⟨N, L, outs, ho, hW, hD, hNb, hI, hK⟩ := kidsFromInW_of_kidsW κ ks bs bws hks (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, by have := hnk ht'; simp only [List.sum_cons]; omega,
        ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInW_dend cs bws _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

/-! ## Loops -/

/-- **`completeAt_loop` within weights**: iteration `j`, its tail within `bt`, weighs at most
`w θ f + bws j θ + bt θ`. -/
theorem completeAt_loopW {f : String} (κ : ℕ) (Lin : Layout) (A : ℕ → List E) (m : ℕ)
    (bs : ℕ → ℕ) (bws : ℕ → Θ → ℕ)
    (step : ∀ j < m, ∀ fp mt : ℕ, ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧
      n ≤ bs j ∧ ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) → ∀ bt : Θ → ℕ,
        (j + 1 < m → RelAtInW fs cert w rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          (A (j + 1)) [] bt) →
        (j + 1 = m → mt = fs f) →
        RelAtInW fs cert w rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f (A j) []
          fun θ => w θ f + bws j θ + bt θ) :
    ∀ j < m, CompleteAtW fs cert w κ f Lin (A j) (Returns []) (loopSum (fs f) bs j (m - j))
      fun θ => loopSum (w θ f) (fun i => bws i θ) j (m - j) := by
  have key : ∀ t j, j + t + 1 = m →
      CompleteAtW fs cert w κ f Lin (A j) (Returns []) (loopSum (fs f) bs j (t + 1))
        fun θ => loopSum (w θ f) (fun i => bws i θ) j (t + 1) := by
    intro t
    induction t with
    | zero =>
      intro j hj fp
      obtain ⟨n, L, hW, hD, hn, hS⟩ := step j (by omega) fp (fs f)
      refine ⟨fs f + fs f + n, L, [], [], ⟨rfl, rfl⟩, ?_, by simpa using hD,
        by simp only [loopSum]; omega, fun rd hl hL => ?_⟩
      · simpa using hW.mono (by omega) (by omega)
      · refine ((hS rd hl (by simpa using hL) (fun θ => w θ f) (fun h => by omega) (fun _ => rfl)).dmono
          fun i hi => ?_).wmono fun θ => ?_
        · obtain ⟨q, hq, _⟩ := hi; simp at hq
        · simp only [loopSum]; omega
    | succ t ih =>
      intro j hj fp
      obtain ⟨nt, Lt, rt, Lo, ⟨rfl, rfl⟩, hWt, hDt, hnt, hSt⟩ := ih (j + 1) (by omega) (fp + fs f)
      obtain ⟨n, L, hW, hD, hn, hS⟩ := step j (by omega) fp nt
      simp only [List.nil_append] at hWt hDt
      refine ⟨fs f + nt + n, Lt ++ L, [], [], ⟨rfl, rfl⟩, ?_, by simpa using disj_append hDt hD hWt hW le_rfl,
        by rw [loopSum]; omega, fun rd hl hL => ?_⟩
      · simp only [List.nil_append]
        rw [within_append]
        exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
      · simp only [List.nil_append, List.append_assoc] at hL
        obtain ⟨hL1, hL2⟩ := memL_append.mp hL
        refine ((hS rd hl hL2 (fun θ => loopSum (w θ f) (fun i => bws i θ) (j + 1) (t + 1)) (fun _ => ?_)
          (fun h => by omega)).dmono fun i hi => ?_).wmono fun θ => ?_
        · refine (hSt rd hl (by simpa using memL_append.mpr ⟨hL1, (memL_append.mp hL2).2⟩)).dmono
            fun i hi => ?_
          exact hi.elim
        · obtain ⟨q, hq, _⟩ := hi; simp at hq
        · conv_rhs => rw [loopSum]
  intro j hj
  have := key (m - 1 - j) j (by omega)
  rwa [show m - 1 - j + 1 = m - j by omega] at this

/-- **`loopStep_bufs` within weights**: the iteration's callees `KidsW` within `bs`, `bws`. -/
theorem loopStep_bufsW {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Stmt.straight = true) (AL : List (V × (ℕ ⊕ V))) (hal : pre.filterMap Stmt.allocSz = AL)
    (had : pre.filterMap Stmt.addrS = []) (κ : ℕ) (Lin : Layout) (args : List E)
    (fronts : List (Option V × String × List V × List V)) (tc : V) (targs : List V)
    (hcs : pre.filterMap Stmt.callS = fronts ++ [(some tc, f, targs, [])])
    (sizes : List ℕ) (bufs : List (List E)) (hbl : List.Forall₂ (fun c s => c.length ≤ s) bufs sizes)
    (fp mt : ℕ) (ks : List Kid) (bs : List ℕ) (bws : List (Θ → ℕ)) (hks : KidsW fs cert w κ ks bs bws)
    (hsub : ∀ k ∈ ks, SubL k.Lin (bufL (fp + fs f + mt) sizes bufs ++ Lin))
    (targs' : List E) (more : Bool)
    (hσ : ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f + mt) sizes bufs ++ Lin) → ∀ outs, OutsOk ks outs →
      ∃ σ : Val, fn.params.map σ = args ∧
      Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) ∧
      AL.map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
      (AL.map Prod.fst).map σ = (bases (fp + fs f + mt) sizes).map (fun b => ofK (gpow b)) ∧
      CallsMatch σ (fronts.map (mkCall σ)) ks outs ∧ decide (σ tc ≠ 0) = more ∧
      targs.map σ = targs' ∧
      ∀ q ∈ pre.filterMap LeanVM.Guest.B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL (fp + fs f + mt) sizes bufs) i)) :
    ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧ n ≤ sizes.sum + bs.sum ∧
      ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) → ∀ bt : Θ → ℕ,
        (more = true → RelAtInW fs cert w rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          targs' [] bt) →
        (more = false → mt = fs f) →
        RelAtInW fs cert w rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f args []
          fun θ => w θ f + (bws.map (· θ)).sum + bt θ := by
  set Lb := bufL (fp + fs f + mt) sizes bufs with hLb
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInW_of_kidsW κ ks bs bws hks
    (fp + fs f + mt + sizes.sum)
  refine ⟨sizes.sum + N, Lb ++ L, ?_,
    disj_append (bufL_disj _ _ _ hbl) hD (LeanVM.Guest.B1.bufL_within _ _ _ hbl) hW le_rfl,
    by omega, fun rd hlow hL bt htail hnot => ?_⟩
  · rw [within_append]
    exact ⟨(LeanVM.Guest.B1.bufL_within _ _ _ hbl).mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
  rw [List.append_assoc] at hL
  obtain ⟨hLb, hL'⟩ := memL_append.mp hL
  obtain ⟨hL1, hL2⟩ := memL_append.mp hL'
  obtain ⟨σ, hp, hH, hsz, hdst, hcm, htk, hta, hld⟩ := hσ rd hlow (memL_append.mpr ⟨hLb, hL2⟩) outs ho
  have hwf : Stmt.wfList coreProgram fn.body = true :=
    coreProgram_wf fn (List.mem_of_find?_eq_some hf)
  have hw := walk_straight σ [] pre hs
  rw [← hb] at hw
  have hsat := walk_sat fn.body hwf hH
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ pre hs
  rw [hal] at e1 e2
  have hsz' := e2.trans hsz
  rw [had] at e3
  rw [hcs, List.map_append] at e4
  have hld' := LeanVM.Guest.B1.loadAddrs_straight σ pre hs
  have hc : (mkCall σ (some tc, f, targs, [])).taken = more := htk
  have hown : ∀ i, RegionL Lb i → ownData cert fp (fp + fs f + mt) f (allocs σ (pre.flatMap (slEvs σ)))
      (pre.flatMap (slEvs σ)) i := fun i hi => by
    rw [hsz']
    exact Or.inl (LeanVM.Guest.B1.bufL_region _ _ _ hbl i hi)
  have := relAtInW_of_walk_loop (fs := fs) (cert := cert) (w := w) (R := RegionL Lin)
    (D := fun _ => False) (Dk := fun i => False ∨ outRegion ks outs i) (Rt := RegionL Lin)
    (Dt := fun _ => False) (fp := fp) (m := mt) (N := N) (σ := σ) (rd := rd) (bws := bws) (bt := bt)
    hf hl hp hw rfl
    (fun e he => (hsat.1 e he).1) e4 ?_ (by rw [e1, hsz']; exact hdst) (by rw [e3]; simp) ?_
    (fun i hi => Or.inl hi) ?_ (fun i hi => hi.elim)
  · rwa [hsz', Nat.add_assoc] at this
  · cases more with
    | true =>
      simp only [hc, ↓reduceIte]
      simp only [mkCall, List.map_nil]
      rw [hta]
      exact htail rfl
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact hnot rfl
  · have hsum : (allocs σ (pre.flatMap (slEvs σ))).sum = sizes.sum := by rw [hsz']
    rw [hsum]
    exact hK rd σ _ _ (fun _ => False) hcm hlow hL1
      (LeanVM.Guest.B1.memL_lins fun k hk => (hsub k hk).1 rd (memL_append.mpr ⟨hLb, hL2⟩))
      (regionsOk_of_sub _ _ _ fun k hk i hi =>
        (regionL_append_or ((hsub k hk).2 i hi)).elim (fun h => Or.inr (hown i h)) Or.inl)
  · intro A hA
    rw [hld', List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    obtain ⟨i, hi, hr⟩ := hld q hq
    exact ⟨i, hi, hr.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inl (hown i h)⟩

/-! ## `main`'s callees' weights -/

/-- **A loop helper from `g^a` to `g^e` weighs at most `K` per iteration**, on every valid tree. -/
def LoopWeightLe (ω : String → ℕ) (f : String) (K : ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E) (a e : ℕ), t.name = f →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram → args.getD 0 0 = ofK (gpow a) →
    args.getD 1 0 = ofK (gpow e) → a < e → e < 2 ^ 64 - 1 → t.weight ω ≤ (e - a) * K

/-- **The weights of `main`'s callees and of its children's** at `ω`, on every valid tree: the
loops' per iteration (`LoopWeightLe`), `aggregate_claims`' affine in its children (argument `0`
being `g^n`), constants for the others; the claim lists' within `α / 1000` times their words
(`WeightTot`); `verify_sub`'s statically bounded callees' constants (`VsStatOk`); `da_verify`'s and
`verify_sub`'s weights ride their completeness (`CalleesAt.da_verify`, `CalleesAt.verify_sub`). -/
structure MainWeightHyps (fs ω : String → ℕ) : Type where
  Bexp : ℕ
  exp : WeightLe coreProgram ω "exponent_tables" fun _ => Bexp
  Kl0 : ℕ
  l0 : LoopWeightLe ω "__loop0" Kl0
  Kl1 : ℕ
  l1 : LoopWeightLe ω "__loop1" Kl1
  Kl2 : ℕ
  l2 : LoopWeightLe ω "__loop2" Kl2
  Kl3 : ℕ
  l3 : LoopWeightLe ω "__loop3" Kl3
  Kl4 : ℕ
  l4 : LoopWeightLe ω "__loop4" Kl4
  Kl100 : ℕ
  l100 : LoopWeightLe ω "__loop100" Kl100
  Bdl : ℕ
  dl : WeightLe coreProgram ω "da_list_digest" fun _ => Bdl
  Bcov : ℕ
  cov : WeightLe coreProgram ω "cover_da_root" fun _ => Bcov
  cAgg : ℕ
  dAgg : ℕ
  agg : ∀ (rd : Reader) (t : Tree) (args rets : List E) (n : ℕ), t.name = "aggregate_claims" →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram → args.getD 0 0 = ofK (gpow n) → 0 < n →
    n < 2 ^ 64 - 1 → t.weight ω ≤ cAgg + dAgg * n
  Bsd : ℕ
  sd : WeightLe coreProgram ω "statement_digest" fun _ => Bsd
  αcl : ℕ
  cl : WeightTot fs ω "claim_list_digest" αcl
  αccl : ℕ
  ccl : WeightTot fs ω "child_claim_list_digest" αccl
  vsc : VerifySub.VsStat
  vsOk : VerifySub.VsStatOk ω vsc

/-- A loop from `1` to `g^e`, `0 < e`, entered: within `e` iterations. -/
theorem LoopWeightLe.from_one {ω : String → ℕ} {f : String} {K : ℕ} (h : LoopWeightLe ω f K) {e : ℕ}
    (he : 0 < e) (he' : e < 2 ^ 64 - 1) {args : List E} (h0 : args.getD 0 0 = 1)
    (h1 : args.getD 1 0 = gen ^ e) :
    ∀ (rd : Reader) (t : Tree) (rets : List E), t.name = f → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.weight ω ≤ e * K := fun rd t rets hn hv hb => by
  have := h rd t args rets 0 e hn hv hb (by rw [h0, ← gen_pow_eq_ofK, pow_zero])
    (by rw [h1, gen_pow_eq_ofK]) he he'
  simpa using this

end
end LeanVM.Guest.B1.Main
