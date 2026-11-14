/-
  LeanVM.Guest.B1.Main.AggAtTB

  `aggregate_claims` within a bound before the memory (`CompleteAtDTB`): `aggregate_claims_completeAtT`
  (same proof), its callees within their static bounds.
-/

module

public import LeanVM.Guest.B1.Main.AggAtT
public import LeanVM.Guest.B1.Main.BatchPops
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.B1.Main.IterK
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Budget.BoundedE
public import LeanVM.Guest.B1.Bits.GrindPlaced

/-!
# `aggregate_claims`, bounded

`aggBs fs SB SK m`: its callees' bounds,
`aggregate_claims_loop0`/`aggregate_claims_loop1`/`aggregate_claims_loop2` from `1` to `g^m` within
`m` times their per-iteration words `iterK fs SK` and their runs' phantom frames, `grind_check__L2`
and `batch_sumcheck__L23` within their static bounds `SB`. `aggB fs SB SK m`: its frame, its
`HeapBuf`s (`aggSizes m`) and those. `aggregate_claims_completeAtTBR`: its tree also pops the batching's hints
(`aggregate_claims_complete_pops` on its valuation and own buffers); `aggregate_claims_completeAtTBRE`: also every
node exact on the memory (`grind_check__L2` by `grind_check_completeDTBR_of`, the others for free);
`aggregate_claims_completeAtTB`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB CompleteAtDTBR KidsDT KidsDTB kidsBoundL Returns Kid
  OutsOk CallsMatch RegionsOk outRegion DisjL Within disj_append disj_nil kidsFromInT_of_kidsDTB
  completeAt_of_rel_pureBat CompleteRelB regionsOk_of within_append bufL bufL_within bufL_disj bufL_region)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- `aggregate_claims`' callees' bounds, in call order. -/
def aggBs (fs SB SK : String → ℕ) (m : ℕ) : List ℕ :=
  [m * iterK fs SK name% «aggregate_claims_loop0» + fs name% «aggregate_claims_loop0»,
      SB "grind_check__L2",
    m * iterK fs SK name% «aggregate_claims_loop1» + fs name% «aggregate_claims_loop1»,
        SB "batch_sumcheck__L23",
    m * iterK fs SK name% «aggregate_claims_loop2» + fs name% «aggregate_claims_loop2»]

/-- `aggregate_claims`' callees' words. -/
def aggKB (fs SB SK : String → ℕ) (m : ℕ) : ℕ :=
  (m * iterK fs SK name% «aggregate_claims_loop0» + fs name% «aggregate_claims_loop0») + SB
      "grind_check__L2" +
    (m * iterK fs SK name% «aggregate_claims_loop1» + fs name% «aggregate_claims_loop1») + SB
        "batch_sumcheck__L23" +
    (m * iterK fs SK name% «aggregate_claims_loop2» + fs name% «aggregate_claims_loop2»)

/-- **`aggregate_claims`' words bound** on `m` children: its frame, its `HeapBuf`s, its callees'. -/
def aggB (fs : String → ℕ) (SB SK : String → ℕ) (m : ℕ) : ℕ :=
  fs "aggregate_claims" + (aggSizes m).sum + aggKB fs SB SK m

/-- `aggregate_claims`' callees' predicates on the memory `rd`: their trees exact on it. -/
def aggTsE (rd : Reader) : List (Tree → Prop) :=
  aggTs.map fun T t => T t ∧ t.Every (ExactAt coreProgram rd)

theorem agg_l25_free : ExactFreeG name% «aggregate_claims_loop0» :=
  exactFreeG_of (j := idx% «aggregate_claims_loop0») (by decide +kernel)

theorem agg_l26_free : ExactFreeG name% «aggregate_claims_loop1» :=
  exactFreeG_of (j := idx% «aggregate_claims_loop1») (by decide +kernel)

theorem agg_l27_free : ExactFreeG name% «aggregate_claims_loop2» :=
  exactFreeG_of (j := idx% «aggregate_claims_loop2») (by decide +kernel)

theorem agg_bs_free : ExactFreeG "batch_sumcheck__L23" :=
  exactFreeG_of (j := idx% «batch_sumcheck__L23») (by decide +kernel)

/-- `aggregate_claims`' own computed hints are pinned by the next atom: it has none. -/
theorem agg_pinned : Stmt.blockNextOk isComputed pinsInverse (fn% «aggregate_claims»).body = true := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- **`aggregate_claims` is complete, placed, its tree of honest shape popping the batching's hints and exact, within
`aggB`**: on
`m ≤ 16` children whose words the caller's words `Lin` hold, the window tables at `tabs`, the hints of an accepting
batching, writing the batching's claim, which `Lin` holds at `g^ds`; given `grind_check__L2`'s trees within `SB`
(`hGr`). -/
theorem aggregate_claims_completeAtTBRE (fs : String → ℕ) (cert : String → V → ℕ) (SB SK : String → ℕ)
    (hGr : TotalLe coreProgram fs "grind_check__L2" (fun _ => SB "grind_check__L2"))
    (h25 : TotalLeOn coreProgram fs name% «aggregate_claims_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop0» + fs
          name% «aggregate_claims_loop0»))
    (h26 : TotalLeOn coreProgram fs name% «aggregate_claims_loop1» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop1» + fs
          name% «aggregate_claims_loop1»))
    (h27 : TotalLeOn coreProgram fs name% «aggregate_claims_loop2» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop2» + fs
          name% «aggregate_claims_loop2»))
    (hbs : TotalLe coreProgram fs "batch_sumcheck__L23" (fun _ => SB "batch_sumcheck__L23")) {m : ℕ}
    (hm1 : 1 ≤ m) (hm16 : m ≤ 16) {cs : List ChildClaims} (hcl : cs.length = m) {h : BatchingHints}
    {out : DeferredClaim} (hrl : h.sumcheckMessages.length = 23) (hb : batch cs h = some out)
    {cpi cfresh ccarried tabs : E} {ds : ℕ} {Lin : Main.Layout}
    (hcw : ∀ rd, Main.MemL rd Lin → ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (htabs : ∀ rd, LowDef 16 rd → Main.MemL rd Lin → WinTabs rd tabs)
    (hdst : (ds, out.cells) ∈ Lin) :
    CompleteAtDTBR fs cert 16 "aggregate_claims" Lin [gen ^ m, cpi, cfresh, ccarried, gen ^ ds, tabs]
      (Returns []) (fun rd t => (aggHonest m t ∧ t.pops coreProgram rd = Hints.batchPushes h) ∧
        t.Every (ExactAt coreProgram rd)) (aggB fs SB SK m) := by
  subst hcl
  obtain ⟨hout, hpow, -⟩ := batch_out hb
  subst hout
  intro fp
  set m := cs.length with hmd
  set b0 := fp + fs "aggregate_claims" with hb0
  set P := aggPtrsAt m b0 with hP
  set Own := aggOwn m cfresh ccarried cs h b0 with hOwn
  have hfit := aggConts_fit (m := m) (cfresh := cfresh) (ccarried := ccarried) (cs := cs) hrl
  have hbm : ∀ rd, Main.MemL rd (Own ++ Lin) → AggMem rd cfresh ccarried (gen ^ ds) cs h P :=
    fun rd hm => by
      obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
      exact aggMem_of_memL h1 (reads_of_memL h2 hdst)
  have hcw' : ∀ rd, Main.MemL rd (Own ++ Lin) → ∀ c (hc : c < cs.length),
      ChildWordsAt rd cpi cfresh ccarried c cs[c] :=
    fun rd hm => hcw rd (Main.memL_append.mp hm).2
  have hne : (1 : E) + gen ^ m ≠ 0 := (one_add_gen_ne (by omega)).mpr (by omega)
  -- the callees
  let ks : List Kid :=
    [⟨name% «aggregate_claims_loop0», true, [1, gen ^ m, P.absorb, cfresh, P.lf, ccarried, P.lc,
        cpi], Own ++ Lin,
        Returns []⟩,
      ⟨"grind_check__L2", true, [cellsOfState (aggN cs h.lambdaGrindNonce) false 1, tabs],
        Own ++ Lin, Returns []⟩,
      ⟨name% «aggregate_claims_loop1», true, [1, gen ^ m, P.chain, P.lf, P.lc,
          lamA cs h * lamA cs h, lamA cs h],
        Own ++ Lin, Returns []⟩,
      ⟨"batch_sumcheck__L23", true,
        capOf (aggN cs h.lambdaGrindNonce) ++ [P.msgs * gen, claimAt cs h m, P.pt, tabs],
        Own ++ Lin, Returns ((aggRun cs h).2.cap ++ [(aggRun cs h).1.2])⟩,
      ⟨name% «aggregate_claims_loop2», true, [1, gen ^ m, P.lf, P.lc, P.pt1, P.chain, P.w,
          lamA cs h], Own ++ Lin,
        Returns []⟩]
  have hm' : m < 2 ^ 64 - 1 := by omega
  have hL : ∀ {g : String} (hT : TotalLeOn coreProgram fs g LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK g + fs g))
      (rest rets : List E) (rd : Reader) (t : Tree), t.name = g →
      t.Valid coreProgram rd ((1 : E) :: gen ^ m :: rest) rets → t.BufsOk coreProgram →
      t.total fs ≤ m * iterK fs SK g + fs g := fun hT rest rets rd t hn hv hb => by
    have := hT rd t _ rets hn (loopPre_gen (by omega) hm' rest) hv hb
    simp only [List.getD_cons_succ, List.getD_cons_zero] at this
    rwa [logG_gen_pow hm'] at this
  have hokB : KidsDTBR fs cert 16 ks (aggTsE) (aggBs fs SB SK m) :=
    ⟨fun _ => ((completeAt_of_rel_pureBat aggPure (by simp [aggPureSet]) (fun rd hm =>
        (guard_complete find_l25 l25_shape' (rest := [P.absorb, cfresh, P.lf, ccarried, P.lc, cpi])
          (agg_l25 (hcw' rd hm) (hbm rd hm))).2 hne) 16 (hL h25 _ _)).toDTB.toR.andEvery
          (everyAll_exact agg_l25_free).everyOn).mono le_rfl fun _ _ h => ⟨trivial, h.2⟩,
      fun _ => (grind_check_completeDTBR_of (bits := 2) (by decide) (by norm_num) hGr fun rd hl hm =>
        ⟨rfl, _, _, rfl, htabs rd hl (Main.memL_append.mp hm).2, agg_pow hpow⟩).mono le_rfl
          fun _ _ h => ⟨trivial, h.2⟩,
      fun _ => ((completeAt_of_rel_pureBat aggPure (by simp [aggPureSet]) (fun rd hm =>
        (guard_complete find_l26 l26_shape.1
          (rest := [P.chain, P.lf, P.lc, lamA cs h * lamA cs h, lamA cs h])
          (agg_l26 (hcw' rd hm) (hbm rd hm))).2 hne) 16 (hL h26 _ _)).toDTB.toR.andEvery
          (everyAll_exact agg_l26_free).everyOn).mono le_rfl fun _ _ h => ⟨trivial, h.2⟩,
      fun _ => ((completeAt_of_rel_pureBat aggPure (by simp [aggPureSet])
        (fun rd hm => agg_bs tabs hrl (hbm rd hm)) 16
        (fun rd t hn hv hb => hbs rd t _ _ hn hv hb)).toDTB.toR.andEvery
          (everyAll_exact agg_bs_free).everyOn).mono le_rfl fun _ _ h => ⟨trivial, h.2⟩,
      fun _ => ((completeAt_of_rel_pureBat aggPure (by simp [aggPureSet]) (fun rd hm =>
        (guard_complete find_l27 l27_shape.1 (rest := [P.lf, P.lc, P.pt1, P.chain, P.w, lamA cs h])
          (agg_l27 (hcw' rd hm) hrl (hbm rd hm))).2 hne) 16 (hL h27 _ _)).toDTB.toR.andEvery
          (everyAll_exact agg_l27_free).everyOn).mono le_rfl fun _ _ h => ⟨trivial, h.2⟩, trivial⟩
  obtain ⟨Nk, Lk, outs, hNB, hoo, hW, hD, -, hKids⟩ :=
    kidsFromInT_of_kidsDTBR (fs := fs) (cert := cert) 16 ks aggTsE (aggBs fs SB SK m) hokB
      (b0 + (aggSizes m).sum)
  have hNB' : Nk ≤ aggKB fs SB SK m := by
    refine hNB.trans (le_of_eq ?_)
    simp [ks, kidsBoundL, aggBs, aggKB, Nat.add_assoc]
  have hl0 : outs.length = 5 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain ⟨o4, t4, rfl, hl4⟩ := exists_of_length_succ hl3
  obtain ⟨o5, t5, rfl, hl5⟩ := exists_of_length_succ hl4
  obtain rfl := List.eq_nil_of_length_eq_zero hl5
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hoo
  -- the layout
  have hWo : Within Own b0 (aggSizes m).sum := bufL_within _ _ _ hfit
  refine ⟨fs "aggregate_claims" + (aggSizes m).sum + Nk, Own ++ Lk, [], [],
    Nat.add_le_add_left hNB' _, ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append (bufL_disj _ _ _ hfit : DisjL Own) hD hWo hW le_rfl,
    fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1', hLin'⟩ := Main.memL_append.mp hm
  obtain ⟨hmO, hLk⟩ := Main.memL_append.mp hm1'
  have hmK : Main.MemL rd (Own ++ Lin) := Main.memL_append.mpr ⟨hmO, hLin'⟩
  have hmem := hbm rd hmK
  -- the valuation and the path
  have hV := agg_core (rd := rd) (cpi := cpi) (tabs := tabs) rfl (hcw' rd hmK) hrl hb hmem
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = aggσ rd m cpi cfresh ccarried (gen ^ ds) tabs P cs h := ⟨_, rfl⟩
  rw [← hσ] at hV
  have hw := Main.walk_straight σ [] aggP aggP_straight
  rw [← agg_shape] at hw
  set es := aggP.flatMap (Main.slEvs σ) with hes
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    refine slEvs_holds fun st hst => ?_
    have hk := List.all_eq_true.mp aggP_kinds st hst
    match st, hk with
    | .atom a, _ => exact hV.atoms a (mem_atomsIn hst)
    | .call .., _ => trivial
    | .ite .., hk => simp [aggKind] at hk
    | .match_ .., hk => simp [aggKind] at hk
    | .dispatch .., hk => simp [aggKind] at hk
    | .ret _, hk => simp [aggKind] at hk
    | .callIf c f args, hk =>
      simp only [aggKind, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at hk
      show IsInK (σ c)
      rcases hk with rfl | rfl | rfl
      · rw [hV.g35, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · rw [hV.g102, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · rw [hV.g191, ← pow_zero gen]; exact gen_pow_add_isInK _ _
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ aggP_straight
  obtain ⟨s32, s97, s187⟩ := agg_sizes hV.atoms hV.e0
  have hal : allocs σ es = aggSizes m := by
    rw [hes, hpa, aggP_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, hV.e0, s32, s97, s187,
      logG_gen_pow (show cs.length < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 13 * (cs.length + 1) < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 2 * (cs.length + 1) < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show cs.length + 1 < 2 ^ 64 - 1 by omega)]
    rfl
  have hT : ∀ {c : V}, σ c = 1 + gen ^ m → decide (σ c ≠ 0) = true :=
    fun h => by rw [h]; exact decide_eq_true hne
  have hcalls : calls es = aggCallList := by
    unfold aggCallList
    rw [hes, hpc, aggP_calls]
    simp only [List.map_cons, List.map_nil, Main.mkCall, hT hV.g35, hT hV.g102, hT hV.g191]
  -- the walk
  have hown : ∀ i, Main.RegionL Own i → ownData cert fp b0 "aggregate_claims" (aggSizes m) es i :=
    fun i hi => Or.inl (bufL_region _ _ _ hfit i hi)
  have hz : ∀ {s x j : ℕ}, (s, x) ∈ (aggSizes m).zip (bases b0 (aggSizes m)) → x ≤ j →
      j < x + s → ownData cert fp b0 "aggregate_claims" (aggSizes m) es j :=
    fun hq h1 h2 => Or.inl ⟨_, hq, h1, h2⟩
  have hrel := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := Main.RegionL Lin) (D := Main.RegionL []) (fp := fp) (N := Nk)
    (args := [gen ^ m, cpi, cfresh, ccarried, gen ^ ds, tabs]) (rets := [])
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4, o5] i)
    coreProgram_wf find_aggregate_claims (Or.inl agg_loop) (by
      show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] = _
      rw [hV.e0, hV.e1, hV.e2, hV.e3, hV.e4, hV.e5]) hw rfl hev
    (by
      rw [hal, hes, hpd, aggP_allocs]
      simp only [List.map_cons, List.map_nil, hV.v6, hV.v8, hV.v9, hV.v33, hV.v98, hV.v107,
        hV.v116, hV.v188, hP, aggPtrsAt, gen_pow_eq_ofK]
      rfl)
    (fun q hq => by
      rw [hes, hpad, aggP_addrs] at hq
      simp at hq)
    (aggTsE rd) ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · obtain ⟨t, ht, ⟨ks', he, hk⟩, hE⟩ := RelAtInT.every_of_walk find_aggregate_claims hw
      (by rw [hcalls]; simp [aggCallList, aggTs]) (exactAt_of_walk find_aggregate_claims hw
        (exact_of_pinned agg_pinned hw hev rd)) hrel
    rw [hal] at ht he
    refine ⟨t, ht, ⟨⟨σ, ks', he, ⟨hV.e0, agg_sizes hV.atoms hV.e0⟩, fun fn' es' vs' hf' hw' => ?_,
      by simp [aggCallList, aggTs], hcalls ▸ hk⟩, ?_⟩, hE⟩
    · rw [find_aggregate_claims, Option.some.injEq] at hf'
      subst hf'
      rw [hw] at hw'
      cases hw'
      exact hcalls
    · subst he
      have hv := ht.2.1
      rw [hσ] at hv ⊢
      exact (aggregate_claims_complete_pops rfl (hcw' rd hmK) hrl hb hmem).2 _ _ _ _ hv
  · rw [hcalls, hal]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩,
        rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 36), σ (.n 0), σ (.n 33), σ (.n 2), σ (.n 8), σ (.n 3), σ (.n 9), σ (.n 1)] = _
        rw [hV.g36, hV.e0, hV.v33, hV.e2, hV.v8, hV.e3, hV.v9, hV.e1]
      · rw [(h1 rfl).1]; rfl
      · exact hV.grArgs
      · rw [(h2 rfl).1]; rfl
      · show [σ (.n 103), σ (.n 0), σ (.n 98), σ (.n 8), σ (.n 9), σ (.n 94), σ (.n 81)] = _
        rw [hV.g103, hV.e0, hV.v98, hV.v8, hV.v9, hV.v94, hV.v81]
      · rw [(h3 rfl).1]; rfl
      · exact hV.bsArgs
      · rw [(h4 rfl).1]; exact hV.bsRets
      · show [σ (.n 192), σ (.n 0), σ (.n 8), σ (.n 9), σ (.n 116), σ (.n 98), σ (.n 188),
          σ (.n 81)] = _
        rw [hV.g192, hV.e0, hV.v8, hV.v9, hV.v116, hV.v98, hV.v188, hV.v81]
      · rw [(h5 rfl).1]; rfl
    · intro q hq
      apply hmK
      simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hq ⊢
      clear * - hq
      tauto
    · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
      have hkL : k.Lin = Own ++ Lin := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
      rw [hkL] at hi
      obtain ⟨q, hq, hq1, hq2⟩ := hi
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (Or.inr (hown i ⟨q, hq, hq1, hq2⟩))
      · exact Or.inl (Or.inl ⟨q, hq, hq1, hq2⟩)
  · intro A hA
    rw [hal]
    rw [hes, B1.loadAddrs_straight σ _ aggP_straight] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    have hq' := of_decide_eq_true (List.all_eq_true.mp aggP_loads q hq)
    have zl := agg_zip m b0
    simp only [aggLoadSet, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hq'
    rcases hq' with ((((((((⟨i, hi, rfl⟩ | (rfl | rfl)) | rfl) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) |
      rfl) | rfl) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | rfl
    · refine ⟨axAbs m b0 + i, ?_, Or.inl (hz (s := 13 * (m + 1)) (x := axAbs m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 33)).limb 0 * addressOfIndex i = _
      rw [hV.v33]; exact limb0_gen_pow_mul _ _
    · refine ⟨axChain m b0 + 0, ?_, Or.inl (hz (s := 2 * (m + 1)) (x := axChain m b0)
        (by rw [zl]; simp) (by omega) (by omega))⟩
      show (σ (.n 98)).limb 0 * addressOfIndex 0 = _
      rw [hV.v98]; exact limb0_gen_pow_mul _ _
    · refine ⟨axChain m b0 + 1, ?_, Or.inl (hz (s := 2 * (m + 1)) (x := axChain m b0)
        (by rw [zl]; simp) (by omega) (by omega))⟩
      show (σ (.n 98)).limb 0 * addressOfIndex 1 = _
      rw [hV.v98]; exact limb0_gen_pow_mul _ _
    · refine ⟨axW m b0 + 0, ?_, Or.inl (hz (s := m + 1) (x := axW m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 188)).limb 0 * addressOfIndex 0 = _
      rw [hV.v188]; exact limb0_gen_pow_mul _ _
    · have hcl2 : (aggOut cs h).cells.length = 24 := by
        simp [aggOut, DeferredClaim.cells, aggRun, bsRun_len, hrl]
      refine ⟨ds + k, ?_, Or.inr (Or.inl (regionL_of_mem hdst (by rw [hcl2]; exact hk)))⟩
      show (σ (.n 4)).limb 0 * addressOfIndex k = _
      rw [hV.e4]; exact limb0_gen_pow_mul _ _
    · refine ⟨axAbs m b0 + 13 * m + k, ?_, Or.inl (hz (s := 13 * (m + 1)) (x := axAbs m b0)
        (by rw [zl]; simp)
        (by omega) (by omega))⟩
      show (σ (.n 42)).limb 0 * addressOfIndex k = _
      rw [hV.p42, show P.absorb = gen ^ axAbs m b0 from rfl, ← pow_mul, ← pow_add,
        limb0_gen_pow_mul, Nat.mul_comm m 13]
    · refine ⟨axChain m b0 + 2 * m + 1, ?_, Or.inl (hz (s := 2 * (m + 1)) (x := axChain m b0)
        (by rw [zl]; simp)
        (by omega) (by omega))⟩
      show (σ (.n 105)).limb 0 * addressOfIndex 1 = _
      rw [hV.p105, show P.chain = gen ^ axChain m b0 from rfl, ← pow_mul, ← pow_add,
        limb0_gen_pow_mul, Nat.mul_comm m 2]
    · refine ⟨axW m b0 + m + 0, ?_, Or.inl (hz (s := m + 1) (x := axW m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 193)).limb 0 * addressOfIndex 0 = _
      rw [hV.p193, show P.w = gen ^ axW m b0 from rfl, ← pow_add, limb0_gen_pow_mul]
    · refine ⟨axPt m b0 + k, ?_, Or.inl (hz (s := 23) (x := axPt m b0) (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 107)).limb 0 * addressOfIndex k = _
      rw [hV.v107]; exact limb0_gen_pow_mul _ _
    · refine ⟨axPt1 m b0 + k, ?_, Or.inl (hz (s := 23) (x := axPt1 m b0) (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 116)).limb 0 * addressOfIndex k = _
      rw [hV.v116]; exact limb0_gen_pow_mul _ _
    · refine ⟨b0 + 0, ?_, Or.inl (hz (s := 47) (x := b0) (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 6)).limb 0 * addressOfIndex 0 = _
      rw [hV.v6]; exact limb0_gen_pow_mul _ _
/-- **`aggregate_claims` is complete, placed, its tree of honest shape popping the batching's hints, within `aggB`**
(`aggregate_claims_completeAtTBRE`, its exactness forgotten). -/
theorem aggregate_claims_completeAtTBR (fs : String → ℕ) (cert : String → V → ℕ) (SB SK : String → ℕ)
    (hGr : TotalLe coreProgram fs "grind_check__L2" (fun _ => SB "grind_check__L2"))
    (h25 : TotalLeOn coreProgram fs name% «aggregate_claims_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop0» + fs
          name% «aggregate_claims_loop0»))
    (h26 : TotalLeOn coreProgram fs name% «aggregate_claims_loop1» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop1» + fs
          name% «aggregate_claims_loop1»))
    (h27 : TotalLeOn coreProgram fs name% «aggregate_claims_loop2» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop2» + fs
          name% «aggregate_claims_loop2»))
    (hbs : TotalLe coreProgram fs "batch_sumcheck__L23" (fun _ => SB "batch_sumcheck__L23")) {m : ℕ}
    (hm1 : 1 ≤ m) (hm16 : m ≤ 16) {cs : List ChildClaims} (hcl : cs.length = m) {h : BatchingHints}
    {out : DeferredClaim} (hrl : h.sumcheckMessages.length = 23) (hb : batch cs h = some out)
    {cpi cfresh ccarried tabs : E} {ds : ℕ} {Lin : Main.Layout}
    (hcw : ∀ rd, Main.MemL rd Lin → ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (htabs : ∀ rd, LowDef 16 rd → Main.MemL rd Lin → WinTabs rd tabs)
    (hdst : (ds, out.cells) ∈ Lin) :
    CompleteAtDTBR fs cert 16 "aggregate_claims" Lin [gen ^ m, cpi, cfresh, ccarried, gen ^ ds, tabs]
      (Returns []) (fun rd t => aggHonest m t ∧ t.pops coreProgram rd = Hints.batchPushes h) (aggB fs SB SK m) :=
  (aggregate_claims_completeAtTBRE fs cert SB SK hGr h25 h26 h27 hbs hm1 hm16 hcl hrl hb hcw htabs hdst).mono le_rfl
    fun _ _ h => h.1

/-- **`aggregate_claims` is complete, placed, its tree of honest shape, within `aggB`** (`aggregate_claims_completeAtTBR`,
the pops forgotten). -/
theorem aggregate_claims_completeAtTB (fs : String → ℕ) (cert : String → V → ℕ) (SB SK : String → ℕ)
    (hGr : TotalLe coreProgram fs "grind_check__L2" (fun _ => SB "grind_check__L2"))
    (h25 : TotalLeOn coreProgram fs name% «aggregate_claims_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop0» + fs
          name% «aggregate_claims_loop0»))
    (h26 : TotalLeOn coreProgram fs name% «aggregate_claims_loop1» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop1» + fs
          name% «aggregate_claims_loop1»))
    (h27 : TotalLeOn coreProgram fs name% «aggregate_claims_loop2» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «aggregate_claims_loop2» + fs
          name% «aggregate_claims_loop2»))
    (hbs : TotalLe coreProgram fs "batch_sumcheck__L23" (fun _ => SB "batch_sumcheck__L23")) {m : ℕ}
    (hm1 : 1 ≤ m) (hm16 : m ≤ 16) {cs : List ChildClaims} (hcl : cs.length = m) {h : BatchingHints}
    {out : DeferredClaim} (hrl : h.sumcheckMessages.length = 23) (hb : batch cs h = some out)
    {cpi cfresh ccarried tabs : E} {ds : ℕ} {Lin : Main.Layout}
    (hcw : ∀ rd, Main.MemL rd Lin → ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (htabs : ∀ rd, LowDef 16 rd → Main.MemL rd Lin → WinTabs rd tabs)
    (hdst : (ds, out.cells) ∈ Lin) :
    CompleteAtDTB fs cert 16 "aggregate_claims" Lin [gen ^ m, cpi, cfresh, ccarried, gen ^ ds, tabs]
      (Returns []) (aggHonest m) (aggB fs SB SK m) :=
  (aggregate_claims_completeAtTBR fs cert SB SK hGr h25 h26 h27 hbs hm1 hm16 hcl hrl hb hcw htabs hdst).toDTB
    fun _ _ h => h.1

end
end LeanVM.Guest.B1.Main
