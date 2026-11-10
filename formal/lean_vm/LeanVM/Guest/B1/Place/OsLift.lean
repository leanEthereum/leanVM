/-
  LeanVM.Guest.B1.Place.OsLift

  f128's `open_stacked` at a configuration is complete, placed, from the body's completeness at
  honest values.
-/

module

public import LeanVM.Guest.B1.Place.OsLiftLv
public import LeanVM.Guest.B1.Whir.Flatness

/-!
# `open_stacked`, placed

**`os_completeAtD_lift`**: a function whose body is `osBody c`, its loop helpers the templates',
at a configuration with the lift's decided facts (`PlaceAll`), is `CompleteAtD` from the honest
data `OsHonest` (frame runs fitting their frames with consecutive cells, memories defined below
`2^κ`, `11 ≤ κ`, the caller's words holding the cursor's words and the window table): it returns
the claim, the point buffers' pointers, the glued weight and the residual's value, the buffers
`pt`, `pt1`.

The proof (`os_completeAt_placeJ`): the buffers at `osSizesF` after the frame; the body's values
from `OsHonest.body` at their base; the callees placed after the buffers, the levels' by
`os_levels_kidsP` (`os_lv_ok`), then the closing rounds', `fold_final_msg` and the residual loops
(`os_pure_completeAtD`) by `os_kids_block`; `query_win_ptrs` then holds the window pointers of the
decoders where they were placed (`osQbpC`). When no memory holds the callees' words, every
obligation on a memory is void.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- Slices in order end by every later one's start and by the top. -/
theorem slices_chain {n top : ℕ} {a w : ℕ → ℕ}
    (h : ∀ l < n, a l + w l ≤ (if l + 1 < n then a (l + 1) else top)) :
    (∀ l l', l < l' → l' < n → a l + w l ≤ a l') ∧ ∀ l < n, a l + w l ≤ top := by
  have step : ∀ l, l + 1 < n → a l + w l ≤ a (l + 1) := fun l hl ↦ by
    have := h l (by omega); simpa only [hl, ↓reduceIte] using this
  have up : ∀ d l, l + d < n → a l + w l ≤ a (l + d) + w (l + d) := by
    intro d
    induction d with
    | zero => intro l _; exact le_rfl
    | succ d ih =>
      intro l hl
      have h1 := ih l (by omega)
      have h2 := step (l + d) (by omega)
      rw [show l + (d + 1) = l + d + 1 by omega]
      omega
  refine ⟨fun l l' hll hl' ↦ ?_, fun l hl ↦ ?_⟩
  · have h1 := up (l' - 1 - l) l (by omega)
    have h2 := step (l + (l' - 1 - l)) (by omega)
    rw [show l + (l' - 1 - l) + 1 = l' by omega] at h2
    omega
  · have h1 := up (n - 1 - l) l (by omega)
    have h2 := h (l + (n - 1 - l)) (by omega)
    simp only [show ¬ (l + (n - 1 - l) + 1 < n) by omega, ↓reduceIte] at h2
    omega

theorem sqWinPtrs_length (fs : String → ℕ) (cert : String → V → ℕ) (lv : OsLv) (L : String)
    (n b : ℕ) : (sqWinPtrs fs cert lv L n b).length = n * sqPer lv := by
  simp [sqWinPtrs]

/-- **`open_stacked` at a configuration is complete, placed**, from the honest data. -/
theorem os_completeAtD_lift (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 11 ≤ κ)
    {c : OsCfg} (hA : PlaceAll c) {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hp : fn.params = osParams 10)
    (hb : fn.body = osBody c)
    (hsq : ∀ l < c.levels.length,
      FnIs (c.sqLoop l) (osParams 6) (sqLoopBody (osLvAt c l) (c.sqLoop l)))
    (hres : ∀ l < c.yrLevel,
      FnIs (c.resLoop l) (osParams 7) (resLoopBody l (osLvAt c l) (c.resLoop l)))
    {args : List E} (hal : args.length = 10) {cur tabs : E} {xs : List E} {tgt inn res : E}
    {pt pt1 : List E} (H : OsHonest c args cur tabs xs tgt inn res pt pt1) {Lin : Layout}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) :
    CompleteAtD fs cert κ name Lin args (fun rets Lout ↦ ∃ b b1 : ℕ,
      rets = [tgt, ofK (addressOfIndex b), ofK (addressOfIndex b1), inn, res] ∧
        Lout = [(b, pt), (b1, pt1)]) := by
  have hA0 := hA
  obtain ⟨hP, hyr, hSz, hLv⟩ := hA0
  obtain ⟨hPTl, hPT1l, -⟩ := hSz
  have hl : H.own.length = (osSizesF c).length := H.own_len.length_eq
  have hbA : fn.body = osBodyA c ++ [.ret (osBodyRet c)] := hb.trans (osBody_eq c)
  have hloop : coreProgram.loop name = false := by
    obtain ⟨a, l, he⟩ : ∃ a l, osBodyRet c = a :: l := ⟨_, _, rfl⟩
    rw [Program.loop_of_find? hfind, Fn.loop, hbA, he]
    simp [List.reverse_append]
  have hst : (osBodyA c).all Main.Stmt.straight = true := straight_of_flat _ (osBodyA_flat c)
  have hjs : [osIxPT c, osIxPT1 c].Nodup := by simp [osIxPT, osIxPT1]
  have hjl : ∀ j ∈ [osIxPT c, osIxPT1 c], j < (osSizesF c).length := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact hPTl
    · exact hPT1l
  refine os_completeAt_placeJ hfind hloop κ Lin args _ hbA hst hP.1 (osSizesF c)
    [osIxPT c, osIxPT1 c] hjs hjl (C := fun _ _ _ ↦ True) fun fp ↦ ?_
  set b0 := fp + fs name with hb0
  obtain ⟨kEnd, f, hbody⟩ := H.body b0
  set σ := fill (Val.ofArgs args) 10 kEnd f with hσ
  set Lk := osLkF c b0 H.own Lin with hLk
  have hBlk : ∀ rd, LowDef κ rd → MemL rd Lk →
      AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ Lk)) rd σ (osBodyA c) ∧
        OsOutF c b0 tabs tgt inn res H.word H.lamInv H.batched H.mu σ :=
    fun rd hlow hm ↦ hbody _ rd (osH_of_lk hl hLin hlow hm) σ (agree_fill _ _ _ _) (range_fill _ _ _ _)
  have hparams : fn.params.map σ = args := by
    rw [hp]
    refine List.ext_getElem (by simp [osParams, hal]) fun j h1 h2 ↦ ?_
    have hj : j < 10 := by simpa [osParams] using h1
    simp only [osParams, List.getElem_map, List.getElem_range]
    rw [hσ, fill_lt hj, ofArgs_n, List.getD_eq_getElem _ _ h2]
  have hfit : ∀ ws : ℕ → List E, List.Forall₂ (fun w s ↦ w.length ≤ s)
      (H.own.set osIxQbp (osQbpC c ws)) (osSizesF c) := fun ws ↦
    forall₂_set (H.own_len.imp fun _ _ h ↦ le_of_eq h) (by rw [osSizesF_qbp, osQbpC_length])
  have hgetD : ∀ ws : ℕ → List E, ∀ j, j ≠ osIxQbp →
      (H.own.set osIxQbp (osQbpC c ws)).getD j [] = H.own.getD j [] := fun ws j hj ↦ by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]
  have hOut : ∀ ws : ℕ → List E, ∃ b b1 : ℕ,
      [tgt, osPtrF c b0 (osIxPT c), osPtrF c b0 (osIxPT1 c), inn, res] =
        [tgt, ofK (addressOfIndex b), ofK (addressOfIndex b1), inn, res] ∧
      osLoutJ b0 (osSizesF c) (H.own.set osIxQbp (osQbpC c ws)) [osIxPT c, osIxPT1 c] =
        [(b, pt), (b1, pt1)] := fun ws ↦ by
    refine ⟨b0 + ((osSizesF c).take (osIxPT c)).sum, b0 + ((osSizesF c).take (osIxPT1 c)).sum,
      ?_, ?_⟩
    · rw [osPtrF, osPtrF, osBaseF_eq c b0 hPTl, osBaseF_eq c b0 hPT1l]
    · simp only [osLoutJ, List.map_cons, List.map_nil]
      rw [hgetD ws _ (by unfold osIxPT osIxQbp; omega), hgetD ws _ (by unfold osIxPT1 osIxQbp; omega),
        H.own_pt, H.own_pt1]
  have hcalls : ((osBodyA c).filterMap Stmt.callS).map (mkCall σ) =
      (osLvKs σ c 0 c.levels (osHead c).2).flatMap OsLvKP.calls ++
        ((osRest c).filterMap Stmt.callS).map (mkCall σ) := by
    rw [osBodyA_eq_rest, List.filterMap_append, List.filterMap_append, hP.2.1, List.nil_append,
      List.map_append, osLevels_calls]
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk
  swap
  · -- no memory holds the callees' words: every obligation on a memory is void
    refine ⟨σ, H.own.set osIxQbp (osQbpC c fun _ ↦ []),
      [tgt, osPtrF c b0 (osIxPT c), osPtrF c b0 (osIxPT1 c), inn, res], 0, [], fun _ ↦ False, _, hcalls,
      hfit _, hOut _, fun q hq ↦ by simp at hq, disj_nil, hparams, ?_, ?_⟩
    · intro rd hlow hB hLin'
      exact absurd ⟨rd, hlow, memL_osLkF (c := c) (b := b0) (own := H.own) (Lin := Lin) hB hLin'⟩ hex
    · intro rd hlow hB _ hLin'
      exfalso
      exact hex ⟨rd, hlow, memL_osLkF (c := c) (b := b0) (own := H.own) (Lin := Lin) hB hLin'⟩
  obtain ⟨rd0, hl0, hm0⟩ := hex
  obtain ⟨-, hret0, -, -, hSV⟩ := hBlk rd0 hl0 hm0
  have hall : ∀ rd, LowDef κ rd → MemL rd Lk →
      AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ Lk)) rd σ (osBodyA c) :=
    fun rd hlow hm ↦ (hBlk rd hlow hm).1
  -- the levels
  obtain ⟨N1, L1, ps, hps, hW1, hD1, hK1⟩ := os_levels_kidsP (fs := fs) (cert := cert) κ σ Lk
    (osWL fs cert c b0) (osSL fs cert c H.word) (osLvKs σ c 0 c.levels (osHead c).2) 0
    (fun i hi ↦ by
      have hi' : i < c.levels.length := by rwa [osLvKs_length] at hi
      rw [osLvKs_get' σ c hi', Nat.zero_add]
      refine os_lv_ok hrf hcons hκ hA hsq H hLin hall hl0 hm0 hSV hi' fun c' hc' ↦ ?_
      rw [hcalls]
      refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem hi, ?_⟩)
      rw [osLvKs_get' σ c hi']
      exact hc')
    (b0 + (osSizesF c).sum)
  -- the closing rounds, `fold_final_msg`, the residual loops
  obtain ⟨N2, L2, hW2, hD2, hK2⟩ := os_kids_block (fs := fs) (cert := cert) κ Lk σ
    (((osRest c).filterMap Stmt.callS).map (mkCall σ)) (fun c' hc' ht ↦ by
      have hcB : c' ∈ ((osBodyA c).filterMap Stmt.callS).map (mkCall σ) := by
        rw [hcalls]; exact List.mem_append_right _ hc'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
      rw [← List.take_append_drop (c.yrLog + 1) ((osRest c).filterMap Stmt.callS),
        List.mem_append] at hx
      rcases hx with hx | hx
      · have hnb := List.all_eq_true.mp hP.2.2.2.1 x hx
        simp only [osNamedB, Bool.and_eq_true, Option.isNone_iff_eq_none,
          Option.isSome_iff_exists] at hnb
        obtain ⟨-, K, hK⟩ := hnb
        exact os_kid_named (osCalleesRegD_holds hκ) (osRoundRegD_holds hκ) hall ⟨rd0, hl0, hm0⟩
          hcB ht (by rw [mkCall_f]; exact hK)
      · rw [hP.2.2.2.2.1] at hx
        obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hx
        have hl'' : l < c.yrLevel := List.mem_range.mp hl'
        obtain ⟨fnr, hfr1, -, hfr3⟩ := hres l hl''
        have hpure := (hP.2.2.2.2.2 l hl'').2
        obtain ⟨-, r2⟩ := hSV.2 l hl''
        rw [mkCall_f, mkCall_args, mkCall_rets]
        show CompleteAtD fs cert κ (c.resLoop l) Lk ((osResCall c l).2.2.1.map σ) (Returns [])
        rw [r2]
        exact os_pure_completeAtD hfr1 (by rw [hfr3]; exact hpure)
          (fun rd hm ↦ H.resRel b0 rd (osMemF_of_lk hl hm) l hl'') κ)
    (b0 + (osSizesF c).sum + N1)
  -- `query_win_ptrs`, the decoders placed
  set ws : ℕ → List E := fun l ↦
    sqWinPtrs fs cert (osLvAt c l) (c.sqLoop l) (osLvAt c l).squeezes (ps.getD l 0) with hws
  have hqfit : OsQbpFit c ws := by
    have := slices_chain (n := c.levels.length) (top := c.posLen) (a := fun l ↦ (osLvAt c l).posOff)
      (w := fun l ↦ (osLvAt c l).squeezes * sqPer (osLvAt c l))
      (fun l hl ↦ (hP.2.2.1 l hl).2.2.2.2.2)
    refine ⟨fun l l' h1 h2 ↦ ?_, fun l hl ↦ ?_⟩
    · rw [hws, sqWinPtrs_length]; exact this.1 l l' h1 h2
    · rw [hws, sqWinPtrs_length]; exact this.2 l hl
  refine ⟨σ, H.own.set osIxQbp (osQbpC c ws),
    [tgt, osPtrF c b0 (osIxPT c), osPtrF c b0 (osIxPT1 c), inn, res], N1 + N2, L1 ++ L2,
    fun _ ↦ False, _, hcalls, hfit ws, hOut ws, ?_,
    disj_append hD1 hD2 hW1 hW2 le_rfl, hparams, ?_, ?_⟩
  · rw [within_append]
    exact ⟨hW1.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
  · -- the body
    intro rd hlow hB hLin'
    obtain ⟨hA', hO⟩ := hBlk rd hlow (memL_osLkF hB hLin')
    refine ⟨?_, hO.2.1, hO.2.2.1⟩
    rw [hbA, holdsList_flat_ret _ (osBodyA_flat c)]
    exact ⟨os_allOk_mono (fun _ _ _ _ ↦ trivial) hA', hO.1⟩
  · -- the callees
    intro rd hlow hB hL hLin'
    have hmk : MemL rd Lk := memL_osLkF hB hLin'
    obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
    have hRk : ∀ i, RegionL Lk i →
        RegionL Lin i ∨ RegionL (bufL b0 (osSizesF c) (H.own.set osIxQbp (osQbpC c ws))) i :=
      fun i hi ↦ regionL_osLkF hi
    refine kidsFromIn_append _ _ _ _ _ _ _ _ (hK1 rd _ (fun _ ↦ False) hlow hL1 hmk
      (fun i hi ↦ ?_) hRk (fun l _ hl p i hi ↦ ?_)) fun D1 _ ↦
      hK2 rd _ D1 hlow hL2 hmk fun i hi ↦ Or.inl (hRk i hi)
    · have hi' : i < c.levels.length := by rw [hps, osLvKs_length] at hi; exact hi
      have := memL_osW (H.own_len.imp fun _ _ h ↦ le_of_eq h) hqfit hB hi'
      simp only [Nat.zero_add, osWL, sqW]
      rw [show ps[i] = ps.getD i 0 from (List.getD_eq_getElem _ _ hi).symm]
      exact this
    · have hl' : l < c.levels.length := by rw [osLvKs_length] at hl; omega
      obtain ⟨x, hx, h1, h2⟩ := hi
      simp only [osWL, sqW, List.mem_singleton] at hx
      subst hx
      refine Or.inr (regionL_osW (H.own_len.imp fun _ _ h ↦ le_of_eq h) hqfit hl'
        ⟨_, List.mem_singleton_self _, h1, ?_⟩)
      simp only [sqWinPtrs_length] at h2 ⊢
      rw [hws]
      simp only [sqWinPtrs_length]
      exact h2

end
end LeanVM.Guest.B1
