module

public import NativeVm.Code.Phase3.TailVals1

/-!
# Phase 3 after the transcript: the fingerprints

`tl_fp`: a side's fingerprints program (`fpOps`) from the slots `tlL` lists (the weights, the
constants, the two `indexMle`s, the program counter's final value, the memory's limbs and counters,
the share). `tl_vals2`: the push and pull sides' fingerprints into `fpR`, the model's
`fingerprints` (`TlVals`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

variable {env : Env} {inp : Input} {s : QState} {E : QState → Prop}

/-- The slots the fingerprints read and their values. -/
def tlL (w0 w1 w2 w3 w4 im ib pc m0 m1 mf bf share : EW) : List (Nat × EW) :=
  [(wsl 0, w0), (wsl 1, w1), (wsl 2, w2), (wsl 3, w3), (wsl 4, w4), (sOne, 1), (sGen, gen),
    (sG2, gen * gen), (sZero, 0), (sIm, im), (sIb, ib), (sPc, pc), (52840, m0), (52842, m1),
    (52844, mf), (52846, bf), (52848, share)]

/-- Their words. -/
def tlK : List Nat :=
  [wsl 0, wsl 1, wsl 2, wsl 3, wsl 4, sOne, sGen, sG2, sZero, sIm, sIb, sPc, 52840, 52842, 52844,
    52846, 52848]

theorem tlL_keys (w0 w1 w2 w3 w4 im ib pc m0 m1 mf bf share : EW) :
    (tlL w0 w1 w2 w3 w4 im ib pc m0 m1 mf bf share).map (·.1) = tlK := rfl

theorem tl_fp_ws {dst : Nat} (hd : dst = fpPush ∨ dst = fpPull) :
    ∀ r ∈ ([⟨sT6, 4⟩, ⟨dst, 6⟩] : List Region), Ok3 r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact tl_ok3 (by decide)
  · rcases hd with rfl | rfl <;> exact tl_ok3 (by decide)

/-- **A side's fingerprints program**: the three dot products into `dst`, `dst + 2`, `dst + 4`. -/
theorem tl_fp {pc mc bc dst : Nat} {w0 w1 w2 w3 w4 im ib pcv m0 m1 mf bf share : EW}
    (hi : Inputs env inp s.mem) (h14 : s.reg .r14 = env.work)
    (hS : ∀ p ∈ tlL w0 w1 w2 w3 w4 im ib pcv m0 m1 mf bf share, EWAt s.mem (wd env.work p.1) p.2)
    (hd : dst = fpPush ∨ dst = fpPull) (hpc : pc = sOne ∨ pc = sPc)
    (hmc : mc = sOne ∨ mc = 52844) (hbc : bc = sOne ∨ bc = 52846)
    (hval : opsValid (fpOps pc mc bc dst) tlK = true)
    (hde : ∀ d ∈ opsDsts (fpOps pc mc bc dst), d % 2 = 0 ∧
      ∃ r ∈ ([⟨sT6, 4⟩, ⟨dst, 6⟩] : List Region), r.off ≤ d ∧ d + 2 ≤ r.stop) :
    WP (opsCode (fpOps pc mc bc dst)) s (fun s' ↦
      EWArr s'.mem (wd env.work dst)
        #[(0 : EW) + w0 * (1 : EW) +
            w1 * vOf (tlL w0 w1 w2 w3 w4 im ib pcv m0 m1 mf bf share) pc + w2 * (1 : EW),
          (0 : EW) + w0 * gen + w1 * im +
            w2 * vOf (tlL w0 w1 w2 w3 w4 im ib pcv m0 m1 mf bf share) mc + w3 * m0 + w4 * m1,
          (0 : EW) + w0 * (gen * gen) + w1 * ib +
            w2 * vOf (tlL w0 w1 w2 w3 w4 im ib pcv m0 m1 mf bf share) bc + share] ∧
      Wrote env [⟨sT6, 4⟩, ⟨dst, 6⟩] s s') E := by
  set L := tlL w0 w1 w2 w3 w4 im ib pcv m0 m1 mf bf share with hL
  have hk := tlL_keys w0 w1 w2 w3 w4 im ib pcv m0 m1 mf bf share
  rw [← hL] at hk
  have hH := holds_vOf L (by rw [hk]; decide) hS
  rw [hk] at hH
  refine WP.mono (tl_ops_wrote (fpOps pc mc bc dst) (v := vOf L) (tl_fp_ws hd) hi h14 hH
    (by decide) hval hde) ?_ fun _ h ↦ h
  rintro s' ⟨H, w, -⟩
  obtain ⟨r0, r1, r2⟩ := fpOps_run (vOf L) pc mc bc dst hd hpc hmc hbc
  have v0 : vOf L sZero = 0 := rfl
  have v1 : vOf L sOne = 1 := rfl
  have v2 : vOf L sGen = gen := rfl
  have v3 : vOf L sG2 = gen * gen := rfl
  have v4 : vOf L sIm = im := rfl
  have v5 : vOf L sIb = ib := rfl
  have v6 : vOf L (wsl 0) = w0 := rfl
  have v7 : vOf L (wsl 1) = w1 := rfl
  have v8 : vOf L (wsl 2) = w2 := rfl
  have v9 : vOf L (wsl 3) = w3 := rfl
  have v10 : vOf L (wsl 4) = w4 := rfl
  have v11 : vOf L 52840 = m0 := rfl
  have v12 : vOf L 52842 = m1 := rfl
  have v13 : vOf L 52848 = share := rfl
  rw [v0, v1, v6, v7, v8] at r0
  rw [v0, v2, v4, v6, v7, v8, v9, v10, v11, v12] at r1
  rw [v0, v3, v5, v6, v7, v8, v13] at r2
  refine ⟨fun i hi' ↦ ?_, w⟩
  have hm : ∀ j, j = dst ∨ j = dst + 2 ∨ j = dst + 4 → j ∈ opsDsts (fpOps pc mc bc dst) ++ tlK :=
    fun j hj ↦ by
      rcases hj with rfl | rfl | rfl <;> simp [opsDsts, fpOps, EOp.dst]
  rw [wd_wd]
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hi'
  interval_cases i
  · have := H dst (hm _ (by simp)); rw [r0] at this; exact this
  · have := H (dst + 2) (hm _ (by simp)); rw [r1] at this; exact this
  · have := H (dst + 4) (hm _ (by simp)); rw [r2] at this; exact this

theorem tl_extract_min (a : Array EW) (n : Nat) : a.extract 0 (min n a.size) = a.extract 0 n := by
  apply Array.ext
  · simp only [Array.size_extract]; omega
  · intro i h1 h2
    simp only [Array.getElem_extract]

/-- What `tailCode`'s values leave: `1`, `0`, the two lengths, the two sides' fingerprints. -/
structure TlVals (env : Env) (layout : LayoutW) (point weights memory : Array EW) (mf bf share : EW)
    (s : QState) : Prop where
  hone : EWAt s.mem (wd env.work sOne) 1
  hzero : EWAt s.mem (wd env.work sZero) 0
  hl0 : NatAt s.mem (wd env.work (lenW 0)) (min layout.logMemory point.size)
  hl1 : NatAt s.mem (wd env.work (lenW 1)) (min layout.logBytecode point.size)
  hfp0 : EWArr s.mem (wd env.work fpPush) (fingerprints weights memory
    (point.extract 0 layout.logMemory) (point.extract 0 layout.logBytecode) share (gpow 0) 1 1)
  hfp1 : EWArr s.mem (wd env.work fpPull) (fingerprints weights memory
    (point.extract 0 layout.logMemory) (point.extract 0 layout.logBytecode) share
    (gpow (2 ^ layout.logBytecode - 1)) mf bf)

/-- **The push and pull sides' fingerprints.** -/
theorem tl_vals2 {layout : LayoutW} {rate : Nat} {point weights trees memory : Array EW}
    {beta mf bf share : EW} {xs : List Stmt} {P : QState → Prop}
    (h : TlIn env inp layout rate point weights trees memory beta mf bf share s)
    (hps : point.size < 64) (hws : weights.size = 16) (hts : trees.size = 3) (hms : memory.size = 2)
    (hv : TlV1 env layout point s)
    (k : ∀ s', Wrote env tlW s s' → TlVals env layout point weights memory mf bf share s' →
      WP (blk xs) s' P E) :
    WP (blk (I (.load .r14 (cw ctxWork)) :: opsCode (fpOps sOne sOne sOne fpPush) ::
      I (.load .r14 (cw ctxWork)) :: opsCode (fpOps sPc 52844 52846 fpPull) :: xs)) s P E := by
  obtain ⟨m0, m1, rfl⟩ : ∃ m0 m1, memory = #[m0, m1] := ⟨memory[0], memory[1], by
    apply Array.ext
    · simp [hms]
    · intro i h1 h2
      rw [hms] at h1
      interval_cases i <;> rfl⟩
  have hw := h.w
  set L := tlL weights[0] weights[1] weights[2] weights[3] weights[4]
    (indexMle (point.extract 0 (min layout.logMemory point.size)))
    (indexMle (point.extract 0 (min layout.logBytecode point.size)))
    (gpow (2 ^ layout.logBytecode - 1)) m0 m1 mf bf share with hL
  have ew : ∀ i (hi : i < 16), EWAt s.mem (wd env.work (wsl i)) (weights[i]'(by omega)) :=
    fun i hi ↦ by have := hw i (by omega); rwa [wd_wd] at this
  have hS : ∀ p ∈ L, EWAt s.mem (wd env.work p.1) p.2 := by
    simp only [hL, tlL, List.forall_mem_cons]
    exact ⟨ew 0 (by decide), ew 1 (by decide), ew 2 (by decide), ew 3 (by decide),
      ew 4 (by decide), hv.hone, hv.hgen, hv.hg2, hv.hzero, hv.him, hv.hib, hv.hpc, by have := h.mem 0 (by simp); rwa [wd_wd] at this,
      by have := h.mem 1 (by simp); rwa [wd_wd] at this, h.mf, h.bf, h.share, fun _ h ↦ absurd h List.not_mem_nil⟩
  have hb2 : ∀ k ∈ tlK, k + 2 ≤ 2 ^ 61 := by decide
  have hkeep : ∀ (ws : List Region) (s0 s' : QState), Wrote env ws s0 s' →
      (∀ k ∈ tlK, ∀ r ∈ ws, k + 2 ≤ r.off ∨ r.stop ≤ k) → (∀ r ∈ ws, r.stop ≤ 2 ^ 61) →
      (∀ p ∈ L, EWAt s0.mem (wd env.work p.1) p.2) →
      ∀ p ∈ L, EWAt s'.mem (wd env.work p.1) p.2 := fun ws s0 s' hw hc hb hS0 p hp ↦ by
    have hk : p.1 ∈ tlK := by rw [← tlL_keys]; exact List.mem_map_of_mem hp
    exact tl_ewat hw (hc _ hk) (hb2 _ hk) hb (hS0 p hp)
  -- the push side
  refine wp_load (eval_cw h.rdi ctxWork) h.wp ?_
  refine wp_then (tl_fp h.hin (by rsimp) hS (.inl rfl) (.inl rfl) (.inl rfl) (.inl rfl)
    (by decide) (by decide)) fun s1 ⟨f1, w1'⟩ ↦ ?_
  have w1'' := tl_pre w1' (by decide)
  have w1 : Wrote env tlW s s1 := tl_widen w1'' (by decide)
  have h1 := h.keep hps hws hts hms w1
  have hS1 := hkeep _ _ _ w1'' (by decide) (by decide) hS
  -- the pull side
  refine wp_load (eval_cw h1.rdi ctxWork) h1.wp ?_
  refine wp_then (tl_fp h1.hin (by rsimp) hS1 (.inr rfl) (.inr rfl) (.inr rfl) (.inr rfl)
    (by decide) (by decide)) fun s2 ⟨f2, w2'⟩ ↦ ?_
  have w2'' := tl_pre w2' (by decide)
  have w2 : Wrote env tlW s s2 := w1.trans (tl_widen w2'' (by decide))
  have hS2 := hkeep _ _ _ w2'' (by decide) (by decide) hS1
  have h5 : 5 ≤ weights.size := by omega
  refine k s2 w2 ⟨hS2 (sOne, 1) (by simp [hL, tlL]), hS2 (sZero, 0) (by simp [hL, tlL]), ?_, ?_, ?_, ?_⟩
  · exact tl_natAt w2'' (by decide) (by decide) (by decide)
      (tl_natAt w1'' (by decide) (by decide) (by decide) hv.hl0)
  · exact tl_natAt w2'' (by decide) (by decide) (by decide)
      (tl_natAt w1'' (by decide) (by decide) (by decide) hv.hl1)
  · rw [fingerprints_eq weights h5, gpow_zero']
    rw [tl_extract_min, tl_extract_min] at f1
    exact tl_ewarr w2'' (n := 6) (by decide) (by decide) (by decide) (by simp) f1
  · rw [fingerprints_eq weights h5]
    rw [tl_extract_min, tl_extract_min] at f2
    exact f2

end NativeVm.Code.P3
