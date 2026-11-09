/-
  LeanVM.Guest.B1.Place.OsFinalB

  open_stacked at a configuration is complete, placed, within its frame-size bound.
-/

module

public import LeanVM.Guest.B1.Place.OsFinal
public import LeanVM.Guest.B1.Place.OsFinalKB
public import LeanVM.Guest.B1.Place.OsPlaceB
public import LeanVM.Guest.B1.Place.OsSqB
public import LeanVM.Guest.Memory.SizeTotal
public import LeanVM.Guest.Memory.LoopPre

/-!
# `open_stacked`, placed within its bound

`OsCalleeBounds fs Bk c`: the callees' words within `Bk` of their names: the named callees'
(`OsLeafBounds`), each residual loop's run, `K` words an iteration and its one phantom frame
(`TotalLeOn … LoopPre`, G7-cnt's `LoopRunLe.totalLeOn`), within `Bk`, each squeeze loop's `sqTot` and `opening_queries`' `oqBound`
within `Bk`.

**`os_completeAtB_cfg`**: `os_completeAtD_cfg` within `osBos fs Bk name c` words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **The callees' words within `Bk` of their names.** -/
structure OsCalleeBounds (fs : String → ℕ) (Bk : String → ℕ) (c : OsCfg) : Prop where
  leaf : OsLeafBounds fs Bk
  res : ∀ l < c.levels.length, ∃ K, TotalLeOn coreProgram fs (c.resLoop l) LoopPre
    (fun a ↦ logG (a.getD 1 0) * K + fs (c.resLoop l)) ∧
      (lvAt c l).queries / resBatch * K + fs (c.resLoop l) ≤ Bk (c.resLoop l)
  sq : ∀ l < c.levels.length,
    sqTot fs (lvAt c l) (c.sqLoop l) (lvAt c l).squeezes 0 ≤ Bk (c.sqLoop l)
  q : ∀ l < c.levels.length, oqBound fs (osQueriesName l (lvAt c l))
    (oqLoopOf (osQueriesName l (lvAt c l))) ((lvAt c l).queries / (1 + if l = 0 then 1 else 0)) ≤
      Bk (osQueriesName l (lvAt c l))

/-- The special callees' bounds: each level's squeeze loop's `sqTot`, its `opening_queries`'
`oqBound`, its residual loop's run (`Kr` words an iteration and its one phantom frame). -/
def osSpB (fs Kr : String → ℕ) (c : OsCfg) : List (String × ℕ) :=
  (List.range c.levels.length).flatMap fun l ↦
    [(c.sqLoop l, sqTot fs (lvAt c l) (c.sqLoop l) (lvAt c l).squeezes 0),
     (osQueriesName l (lvAt c l), oqBound fs (osQueriesName l (lvAt c l))
       (oqLoopOf (osQueriesName l (lvAt c l))) ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))),
     (c.resLoop l, (lvAt c l).queries / resBatch * Kr (c.resLoop l) + fs (c.resLoop l))]

/-- **The callees' bounds by name**: a named callee's `Bnd`, plus the special callees' bounds of
that name. -/
def osBk (fs Bnd Kr : String → ℕ) (c : OsCfg) (f : String) : ℕ :=
  Bnd f + (((osSpB fs Kr c).filter fun p ↦ decide (p.1 = f)).map Prod.snd).sum

theorem osBk_ge {fs Bnd Kr : String → ℕ} {c : OsCfg} {f : String} {b : ℕ}
    (h : (f, b) ∈ osSpB fs Kr c) : b ≤ osBk fs Bnd Kr c f := by
  unfold osBk
  have : b ∈ ((osSpB fs Kr c).filter fun p ↦ decide (p.1 = f)).map Prod.snd :=
    List.mem_map.mpr ⟨(f, b), List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩
  have := List.le_sum_of_mem this
  omega

theorem osSpB_mem {fs Kr : String → ℕ} {c : OsCfg} {l : ℕ} (hl : l < c.levels.length) :
    (c.sqLoop l, sqTot fs (lvAt c l) (c.sqLoop l) (lvAt c l).squeezes 0) ∈ osSpB fs Kr c ∧
    (osQueriesName l (lvAt c l), oqBound fs (osQueriesName l (lvAt c l))
       (oqLoopOf (osQueriesName l (lvAt c l))) ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))) ∈
      osSpB fs Kr c ∧
    (c.resLoop l, (lvAt c l).queries / resBatch * Kr (c.resLoop l) + fs (c.resLoop l)) ∈
      osSpB fs Kr c := by
  have hr : l ∈ List.range c.levels.length := List.mem_range.mpr hl
  refine ⟨?_, ?_, ?_⟩ <;> exact List.mem_flatMap.mpr ⟨l, hr, by simp⟩

/-- The residual loops' runs' words, `Kr` an iteration and the run's one phantom frame (G7-cnt's
`LoopRunLe.totalLeOn`). -/
def OsLoopBounds (fs Kr : String → ℕ) (c : OsCfg) : Prop :=
  ∀ l < c.levels.length, TotalLeOn coreProgram fs (c.resLoop l) LoopPre
    (fun a ↦ logG (a.getD 1 0) * Kr (c.resLoop l) + fs (c.resLoop l))

/-- **The callees within `osBk`**, from the named callees' and the residual loops' bounds. -/
theorem osCalleeBounds_of {fs Bnd Kr : String → ℕ} {c : OsCfg} (hT : OsLeafBounds fs Bnd)
    (hL : OsLoopBounds fs Kr c) : OsCalleeBounds fs (osBk fs Bnd Kr c) c := by
  refine ⟨fun f K hK rd t args rets hn hv hb ↦ ?_, fun l hl ↦ ⟨Kr (c.resLoop l), hL l hl,
    osBk_ge (osSpB_mem hl).2.2⟩, fun l hl ↦ osBk_ge (osSpB_mem hl).1,
    fun l hl ↦ osBk_ge (osSpB_mem hl).2.1⟩
  have := hT f K hK rd t args rets hn hv hb
  unfold osBk at ⊢
  dsimp only at this ⊢
  omega

/-- **`open_stacked` at a configuration is complete, placed, within `osBos fs Bk name c` words.** -/
theorem os_completeAtB_cfg (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 7 ≤ κ)
    {Bk : String → ℕ} {c : OsCfg} {μ r : ℕ}
    {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (hP : OsCfgPlaced fs cert c) (hBk : OsCalleeBounds fs Bk c) {name : String}
    {fn : Fn} (hfind : coreProgram.find? name = some fn) (hp : fn.params = osParams 9)
    (hb : fn.body = osBody c) (hloop : coreProgram.loop name = false) {S : KeccakState} {root : Digest}
    {target cur : E} {xs : List E} {os : List (List Opening)} {w : WhirEnd} {s' : Fs}
    {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hnz : Whir.NoZeroChallenge μ r target S xs os root)
    (hcaps : Whir.CapsAgree μ r target S xs os root)
    {Lin : Layout} (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs) :
    CompleteAtB fs cert κ name Lin
      (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur]) (OsOut μ w)
      (osBos fs Bk name c) := by
  obtain ⟨c0, c2, tr, hfit, hplen, hptC, hpt1C, hbody, hrunT⟩ := osBodyA_honest hF hP.sizes hrun hnz
  have hlen : tr.Ls.length = c.levels.length := hfit.len
  have hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap := by
    rw [hplen]; exact hF.mu40
  have htl : tr.Lf.ml ≤ yrLogCap := by rw [lf_ml hF hfit]; exact hP.sizes.yr
  set args := capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur] with hargs
  have hb' : fn.body = osBodyA c ++ [.ret (osFinishRet c (osTlSt c).2.1 (osTlSt c).2.2)] := by
    rw [hb, osBody_split]
  refine os_completeAt_placeJB hfind hloop κ Lin args (OsOut μ w) hb' (osBodyA_straight c)
    hP.body.addrs (osSizesL c) [osIxPT c, osIxPT1 c] (osJs_nodup c) (osJs_lt c)
    (C := fun _ _ _ ↦ True) (osKidsB fs Bk c) fun fp ↦ ?_
  -- the body at a memory
  have hBlk : ∀ (C : CallRel) (rd : Reader), OsMem rd (osAtOf c (fp + fs name)) c tr → OsCallsOk C rd (osAtOf c (fp + fs name)) c tr →
      ReadsAt rd cur xs →
      AllOk C rd (osSigma c tr (Val.ofArgs args) c0 c2 (fp + fs name)) (osBodyA c) ∧ (osFinishRet c (osTlSt c).2.1 (osTlSt c).2.2).map (osSigma c tr (Val.ofArgs args) c0 c2 (fp + fs name)) = [w.target, (osAtOf c (fp + fs name)).PT, (osAtOf c (fp + fs name)).PT1, w.inner, w.residual] := by
    intro C rd hm hc hx
    have h := hbody C rd (Val.ofArgs args) (osAtOf c (fp + fs name)) rfl rfl rfl rfl hx hm hc (osSigma c tr (Val.ofArgs args) c0 c2 (fp + fs name)) (agree_fill _ _ _ _) (range_fill _ _ _ _)
    exact ⟨h.1, h.2.1⟩
  have hLkLin : ∀ rd, MemL rd (osLk c tr (fp + fs name) Lin) → MemL rd Lin := fun rd hm ↦ (Main.memL_append.mp hm).2
  have hall : ∀ rd, LowDef κ rd → MemL rd (osLk c tr (fp + fs name) Lin) →
      AllOk (osCR rd (osSp c tr (osAtOf c (fp + fs name))) (OsXOk κ (osLk c tr (fp + fs name) Lin))) rd
        (osSigma c tr (Val.ofArgs args) c0 c2 (fp + fs name)) (osBodyA c) :=
    fun rd hl hm ↦ (hBlk _ rd (osMem_of_memLk hpt htl hm)
      (osCallsOk_honest hF hfit hP.sizes hrunT hcaps hP.names hpt htl hm)
      (hLin rd hl (hLkLin rd hm))).1
  have hparams : fn.params.map (osSigma c tr (Val.ofArgs args) c0 c2 (fp + fs name)) = args := by
    rw [hp]
    refine List.ext_getElem (by simp [osParams, hargs, capOf]) fun j h1 h2 ↦ ?_
    have hj : j < 9 := by simpa [osParams] using h1
    simp only [osParams, List.getElem_map, List.getElem_range]
    rw [osSigma_arg hj, ofArgs_n, List.getD_eq_getElem _ _ h2]
  have hOut : ∀ bp, OsOut μ w [w.target, (osAtOf c (fp + fs name)).PT, (osAtOf c (fp + fs name)).PT1, w.inner, w.residual] (osLoutJ (fp + fs name) (osSizesL c) (osOwnL c tr bp)
      [osIxPT c, osIxPT1 c]) := fun bp ↦ by
    rw [osLoutJ_eq]
    refine ⟨_, _, rfl, ?_⟩
    rw [hptC, hpt1C]
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLk c tr (fp + fs name) Lin)
  · -- the callees
    have hsp : OsSpecialsB fs cert κ Bk c tr (fp + fs name) Lin := by
      refine ⟨fun l hl ↦ ?_, fun l hl p ↦ ?_, fun l hl ↦ ?_⟩
      · obtain ⟨fn', h1, h2, h3, h4⟩ := hP.sqFn l hl
        exact (os_sq_completeAtPB fs cert κ hF hfit hP.sizes hl h1 h2 h3 h4
          (qwDecodeAtD_holds hrf hcons hκ _ (hP.dec l hl)) (fp + fs name) Lin).mono (hBk.sq l hl)
      · exact (os_q_completeAtB fs cert κ hfit hP.sizes hrunT hcaps hl (hP.qnames l hl) (hP.fits l hl)
          (hrunT.index l (by rw [hlen]; exact hl)) (hrunT.width l (by rw [hlen]; exact hl))
          (hP.il l hl) (hP.qo l hl) (fp + fs name) Lin p).mono le_rfl (hBk.q l hl)
      · obtain ⟨fn', h1, h2, h3⟩ := hP.resFn l hl
        have hb := hfit.lvb l hl
        have hq8 := hP.q8 l hl
        have hq0 : 0 < (lvAt c l).queries / resBatch := Nat.div_pos hq8 (by decide)
        have hqo : (lvAt c l).queries / resBatch < 2 ^ 64 - 1 := by
          have := hP.qo l hl; have := Nat.div_le_self (lvAt c l).queries resBatch
          unfold ordG at *; omega
        obtain ⟨K, hK, hKB⟩ := hBk.res l hl
        refine (os_res_completeAtB fs cert κ hF hfit hP.sizes hl h1 h2 h3 hq8
          (one_add_gen_pow_ne_zero hq0 hqo) (fp + fs name) Lin
          (B := (lvAt c l).queries / resBatch * K + fs (c.resLoop l)) fun rd t hn hv hbo ↦ ?_).mono
          le_rfl hKB
        have := hK rd t _ [] hn (loopPre_gen hq0 hqo _) hv hbo
        simp only [List.getD_cons_succ, List.getD_cons_zero, logG_gen_pow hqo] at this
        exact this
    obtain ⟨N, L, ps, hps, hW, hD, hNB, hK⟩ := os_kids_atB (σ0 := Val.ofArgs args) (c0 := c0) (c2 := c2) (b0 := fp + fs name)
      (Lin := Lin) hBk.leaf hP.names hlen hfit hP.pos hP.tot hsp hall hex ((fp + fs name) + (osSizesL c).sum)
    refine ⟨(osSigma c tr (Val.ofArgs args) c0 c2 (fp + fs name)), osOwnL c tr (osBp fs cert c fun l ↦ ps.getD l 0), [w.target, (osAtOf c (fp + fs name)).PT, (osAtOf c (fp + fs name)).PT1, w.inner, w.residual], N, L, fun _ ↦ False, _, rfl, hNB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact osOwnL_fit c tr _ hpt htl
    · exact hOut _
    · exact hW
    · exact hD
    · exact hparams
    · intro rd hl hmB hmLin
      have hmLk : MemL rd (osLk c tr (fp + fs name) Lin) := osLk_memL hmB hmLin
      have hM := osMem_of_memLk hpt htl hmLk
      obtain ⟨hA1, hr⟩ := hBlk _ rd hM
        (osCallsOk_honest (κ := κ) hF hfit hP.sizes hrunT hcaps hP.names hpt htl hmLk)
        (hLin rd hl hmLin)
      obtain ⟨hs1, hs2⟩ := body_allocs_placed c tr (Val.ofArgs args) c0 c2 (fp + fs name) hlen hP.sz
      refine ⟨?_, hs1, hs2⟩
      rw [hb', holdsList_flat_ret _ (osBodyA_flat c)]
      refine ⟨os_allOk_mono (fun _ _ _ _ ↦ trivial) hA1, ?_⟩
      exact hr
    · intro rd hl hmB hmL hmLin
      rw [← osBodyCalls_eq]
      exact os_kids_apply hK hps hP.sizes hpt htl hl hmB hmL hmLin
  · -- no memory holds the callees' words
    refine ⟨(osSigma c tr (Val.ofArgs args) c0 c2 (fp + fs name)), osOwnL c tr fun _ _ ↦ 0, [w.target, (osAtOf c (fp + fs name)).PT, (osAtOf c (fp + fs name)).PT1, w.inner, w.residual], 0, [], fun _ ↦ False, _, rfl, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact osOwnL_fit c tr _ hpt htl
    · exact hOut _
    · intro q hq; simp at hq
    · exact disj_nil
    · exact hparams
    · intro rd hl hmB hmLin
      have hmLk : MemL rd (osLk c tr (fp + fs name) Lin) := osLk_memL hmB hmLin
      exact (hex ⟨rd, hl, hmLk⟩).elim
    · intro rd hl hmB _ hmLin
      have hmLk : MemL rd (osLk c tr (fp + fs name) Lin) := osLk_memL hmB hmLin
      exact (hex ⟨rd, hl, hmLk⟩).elim

end
end LeanVM.Guest.B1
