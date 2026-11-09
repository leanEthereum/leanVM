/-
  LeanVM.Guest.B1.Place.OsFinal

  open_stacked at a configuration is complete, placed.
-/

module

public import LeanVM.Guest.B1.Place.OsFinalK
public import LeanVM.Guest.B1.Place.OsKidsSp1
public import LeanVM.Guest.B1.Place.OsKidsSp2
public import LeanVM.Guest.B1.Place.OsKidsSp5
public import LeanVM.Guest.B1.Place.OsBodyFacts
public import LeanVM.Guest.B1.Bits.QueryWindowsAtAll

/-!
# `open_stacked`, placed

`OsCfgPlaced fs cert c`: the configuration's decided facts the lift uses (the body's, its callee
names', its buffers' sizes, its loop helpers' and `opening_queries`' frames).

**`os_completeAtD_cfg`**: a function whose body is `osBody c`, at a configuration with those facts,
its frame runs fitting their frames with consecutive cells (`Lift.RunsFit`, `RunsConsec`; its
callees by `osCalleesRegD_holds` and dqwc's `qwDecodeAtD_holds`, memories defined below `2^κ`,
`7 ≤ κ`), is complete placed on every accepting run of
`whirOpen μ r target` from `⟨capOf S, []⟩` with no zero challenge and openings that agree in the
caps, the words at the cursor among the caller's: it returns the run's claim, the pointers of its
two point buffers, its glued weight and its residual's value, the buffers the run's point
zero-padded and one plus each coordinate one-padded (`OsOut`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **A configuration's facts the placed lift uses.** -/
structure OsCfgPlaced (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) : Prop where
  body : OsBodyFacts c
  names : OsNames c
  sizes : OsSizes c
  sz : ∀ e ∈ osSizesL c, e < 2 ^ 64 - 1
  pos : ∀ x ∈ osSizesL c, 0 < x
  tot : (osSizesL c).sum < 2 ^ 64 - 1
  qnames : ∀ l < c.levels.length, NamesOk c l (lvAt c l)
  fits : ∀ l < c.levels.length, OqFits fs cert (osQueriesName l (lvAt c l))
    (oqLoopOf (osQueriesName l (lvAt c l))) (osQShape c l)
    ((lvAt c l).queries % 2 * (if l = 0 then 1 else 0))
  il : ∀ l < c.levels.length,
    rowLo (lvAt c l).interleave + (lvAt c l).interleave / rowLo (lvAt c l).interleave ≤ c.maxIl
  qo : ∀ l < c.levels.length, (lvAt c l).queries + 1 < ordG
  q8 : ∀ l < c.levels.length, resBatch ≤ (lvAt c l).queries
  sqFn : ∀ l < c.levels.length, ∃ fn, coreProgram.find? (c.sqLoop l) = some fn ∧
    fn.params = osParams 6 ∧ fn.body = sqLoopBody (lvAt c l) (c.sqLoop l) ∧
    coreProgram.loop (c.sqLoop l) = true
  resFn : ∀ l < c.levels.length, ∃ fn, coreProgram.find? (c.resLoop l) = some fn ∧
    fn.params = osParams 6 ∧ fn.body = resLoopBody l (lvAt c l) (c.resLoop l)
  dec : ∀ l < c.levels.length,
    (sqDecName (lvAt c l), (lvAt c l).depth, (lvAt c l).capDepth) ∈ queryWindowsShapes

/-- What `open_stacked` returns and the buffers it hands back. -/
def OsOut (μ : ℕ) (w : WhirEnd) : List E → Layout → Prop := fun rets Lout ↦
  ∃ b b1 : ℕ, rets = [w.target, ofK (addressOfIndex b), ofK (addressOfIndex b1), w.inner,
      w.residual] ∧
    Lout = [(b, w.point ++ List.replicate (pointCap - μ) 0),
      (b1, w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)]

theorem lf_ml {c : OsCfg} {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) {tr : OsTr}
    (h : TrFit c tr) : tr.Lf.ml = c.yrLog := lf_ml' hF h

/-- **`open_stacked` at a configuration is complete, placed.** -/
theorem os_completeAtD_cfg (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 7 ≤ κ)
    {c : OsCfg} {μ r : ℕ}
    {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (hP : OsCfgPlaced fs cert c) {name : String}
    {fn : Fn} (hfind : coreProgram.find? name = some fn) (hp : fn.params = osParams 9)
    (hb : fn.body = osBody c) (hloop : coreProgram.loop name = false) {S : KeccakState} {root : Digest}
    {target cur : E} {xs : List E} {os : List (List Opening)} {w : WhirEnd} {s' : Fs}
    {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hnz : Whir.NoZeroChallenge μ r target S xs os root)
    (hcaps : Whir.CapsAgree μ r target S xs os root)
    {Lin : Layout} (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs) :
    CompleteAtD fs cert κ name Lin
      (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur]) (OsOut μ w) := by
  obtain ⟨c0, c2, tr, hfit, hplen, hptC, hpt1C, hbody, hrunT⟩ := osBodyA_honest hF hP.sizes hrun hnz
  have hlen : tr.Ls.length = c.levels.length := hfit.len
  have hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap := by
    rw [hplen]; exact hF.mu40
  have htl : tr.Lf.ml ≤ yrLogCap := by rw [lf_ml hF hfit]; exact hP.sizes.yr
  set args := capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur] with hargs
  have hb' : fn.body = osBodyA c ++ [.ret (osFinishRet c (osTlSt c).2.1 (osTlSt c).2.2)] := by
    rw [hb, osBody_split]
  refine os_completeAt_placeJ hfind hloop κ Lin args (OsOut μ w) hb' (osBodyA_straight c)
    hP.body.addrs (osSizesL c) [osIxPT c, osIxPT1 c] (osJs_nodup c) (osJs_lt c)
    (C := fun _ _ _ ↦ True) fun fp ↦ ?_
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
    have hsp : OsSpecials fs cert κ c tr (fp + fs name) Lin := by
      refine ⟨fun l hl ↦ ?_, fun l hl p ↦ ?_, fun l hl ↦ ?_, fun f a Out X h ↦
        completeAtD_lin_mono h fun q hq ↦ List.mem_append_left _ hq⟩
      · obtain ⟨fn', h1, h2, h3, h4⟩ := hP.sqFn l hl
        exact os_sq_completeAtP fs cert κ hF hfit hP.sizes hl h1 h2 h3 h4
          (qwDecodeAtD_holds hrf hcons hκ _ (hP.dec l hl)) (fp + fs name) Lin
      · exact os_q_completeAtD fs cert κ hfit hP.sizes hrunT hcaps hl (hP.qnames l hl) (hP.fits l hl)
          (hrunT.index l (by rw [hlen]; exact hl)) (hrunT.width l (by rw [hlen]; exact hl))
          (hP.il l hl) (hP.qo l hl) (fp + fs name) Lin p
      · obtain ⟨fn', h1, h2, h3⟩ := hP.resFn l hl
        have hb := hfit.lvb l hl
        have hq8 := hP.q8 l hl
        exact os_res_completeAtD fs cert κ hF hfit hP.sizes hl h1 h2 h3 hq8
          (one_add_gen_pow_ne_zero (Nat.div_pos hq8 (by decide))
            (by have := hP.qo l hl; have := Nat.div_le_self (lvAt c l).queries resBatch
                unfold ordG at *; omega)) (fp + fs name) Lin
    obtain ⟨N, L, ps, hps, hW, hD, hK⟩ := os_kids_at (σ0 := Val.ofArgs args) (c0 := c0) (c2 := c2) (b0 := fp + fs name)
      (Lin := Lin) (osCalleesRegD_holds κ) hP.names hlen hfit hP.pos hP.tot hsp hall hex ((fp + fs name) + (osSizesL c).sum)
    refine ⟨(osSigma c tr (Val.ofArgs args) c0 c2 (fp + fs name)), osOwnL c tr (osBp fs cert c fun l ↦ ps.getD l 0), [w.target, (osAtOf c (fp + fs name)).PT, (osAtOf c (fp + fs name)).PT1, w.inner, w.residual], N, L, fun _ ↦ False, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    refine ⟨(osSigma c tr (Val.ofArgs args) c0 c2 (fp + fs name)), osOwnL c tr fun _ _ ↦ 0, [w.target, (osAtOf c (fp + fs name)).PT, (osAtOf c (fp + fs name)).PT1, w.inner, w.residual], 0, [], fun _ ↦ False, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
