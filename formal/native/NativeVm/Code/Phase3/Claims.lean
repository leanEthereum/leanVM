module

public import NativeVm.Code.Phase3.Pieces

/-!
# The bus's column claims

`claimsCode`: the count `4` at `claimsR`, then the four claims (`claimOne`): the memory's two limbs
and final counter on the memory's prefix of the GKR point, the bytecode's final counter on the
bytecode's prefix (`claims_spec`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters LeanVM.Protocol.Verifier

variable {env : Env} {inp : Input} {s : QState} {E : QState → Prop}

theorem pc_ofNat_u (n : Nat) : (Int64.ofNat n).toUInt64 = n.toUInt64 := UInt64.toNat_inj.mp (by simp)

theorem pc_vecWords : vecWords pointCap = 73 := by decide

theorem pc_claimWords : claimWords = 76 := by decide

theorem pc_extract_min {α : Type} (xs : Array α) (n : Nat) :
    xs.extract 0 (min n xs.size) = xs.extract 0 n := by
  apply Array.ext
  · simp
  · intro i h1 h2; simp

theorem pc_within {i : Nat} (hi : i < 4) : Within (claimR i) claimsR :=
  ⟨by rw [claimsR_off]; simp [claimR, claimW]; omega, by
    rw [Region.stop, Region.stop, claimsR_off, claimsR_size]; simp [claimR, claimW]; omega⟩

theorem claimOne_spec {i col li vw n : Nat} {pt : Array EW} {v : EW} (hi4 : i < 4) (hcol : col < 2 ^ 63)
    (hli : li < 2)
    (hrdi : s.reg .rdi = env.ctx) (h14 : s.reg .r14 = env.work) (hi : Inputs env inp s.mem)
    (hpt : EWArr s.mem (wd env.work 52704) pt) (hps : pt.size ≤ 63)
    (hn : NatAt s.mem (wd env.work (lenW li)) n) (hnp : n ≤ pt.size) (hn30 : n ≤ 30)
    (hv : EWAt s.mem (wd env.work vw) v) (hvw : vw % 2 = 0 ∧ vw + 1 < 2 ^ 60)
    (hvc : vw + 2 ≤ claimW i ∨ claimW i + 76 ≤ vw) :
    WP (claimOne i col li vw) s (fun s' ↦
      ColumnClaimAt s'.mem (wd env.work (claimW i)) ⟨col, pt.extract 0 n, v⟩ ∧
      Wrote env [claimR i] s s') E := by
  have hok := claimR_ok hi4
  have hcw : claimW i + 76 ≤ 15569 + 12161 := by unfold claimW; omega
  have hs0 := hi.ok3_some' hok (a := claimW i) (by simp [claimR, Region.stop])
  have hbd : ∀ r ∈ [claimR i], r.stop ≤ 2 ^ 61 := by simp [claimR, claimW, Region.stop]; omega
  rw [claimOne_eq]
  refine wp_storei (eval_work h14 _) hs0 ?_
  have w1 : Wrote env [claimR i] s (s.setMem (wd env.work (claimW i)) (Int64.ofNat col).toUInt64) :=
    wrote_store (r := claimR i) (by simp) (by simp [claimR]) (by simp [claimR, Region.stop]) rfl rfl
      hs0 _
  have kw : ∀ k, (k < claimW i ∨ claimW i + 76 ≤ k) → k < 2 ^ 61 →
      (s.setMem (wd env.work (claimW i)) (Int64.ofNat col).toUInt64).mem (wd env.work k) =
        s.mem (wd env.work k) := fun k hk hk' ↦
    w1.word (fun r hr ↦ by rw [List.mem_singleton.mp hr]; simpa [claimR, Region.stop] using hk) hk' hbd
  refine WP.mono (claimRest_spec (n := n) (pt := pt) (v := v) hi4 (by rsimp; exact hrdi)
    (by rsimp; exact h14) (hi.step3 (fun r hr ↦ (List.mem_singleton.mp hr) ▸ hok) w1.step hrdi)
    (hpt.congr (n := 2 * pt.size) (fun k hk ↦ by
      rw [wd_wd]; exact kw _ (by unfold claimW; omega) (by omega)) le_rfl)
    hps (hn.congr (kw _ (by unfold claimW lenW; omega) (by unfold lenW; omega))) hnp hn30
    (hv.congr fun k hk ↦ by rw [wd_wd]; exact kw _ (by omega) (by omega)) hvw hvc) ?_ fun _ h ↦ h
  rintro s' ⟨h1, h2, h3, h4, w2, -⟩
  have hsz : (pt.extract 0 n).size = n := by rw [Array.size_extract]; omega
  refine ⟨⟨⟨show col < 2 ^ 64 by omega, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩, w1.trans w2⟩
  · rw [h4]; simp
  · rw [hsz, show pointCap = 36 by decide]; omega
  · rw [wd_wd, hsz]; exact h1
  · rw [wd_wd, wd_wd, show claimW i + 1 + 1 = claimW i + 2 by omega]; exact h2
  · rw [wd_wd, pc_vecWords, show claimW i + (1 + 73) = claimW i + 74 by omega]; exact h3

/-- The context's word of the working area's address survives a run writing the claims. -/
theorem pc_ctx {s0 : QState} (h : Wrote env [claimsR] s0 s) (hi : Inputs env inp s0.mem) :
    s.mem (wd env.ctx ctxWork) = s0.mem (wd env.ctx ctxWork) := by
  refine h.mem _ fun r hr ⟨k, hk, e⟩ ↦ ?_
  rw [List.mem_singleton.mp hr] at hk e
  have := dataEnd_le inp.bytecode.size
  rw [claimsR_size] at hk
  rw [claimsR_off] at e
  exact hi.ctx_ne_work (j := ctxWork) (k := 15569 + k) (by lay_omega)
    (by rw [dataEnd_eq] at this; omega) e

theorem pc_unset {ws : List Region} {s' : QState} {r : Reg64} {v : UInt64}
    (h : Wrote env ws (s.setReg r v) s') (hr : r ≠ .rdi) : Wrote env ws s s' :=
  ⟨by rw [h.rdi, QState.setReg_reg, ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hr))], h.mem,
    h.dom⟩

/-- A word apart from claim `i` survives its run. -/
theorem pc_word {s' : QState} {i k : Nat} (hw : Wrote env [claimR i] s s') (hi4 : i < 4)
    (hk : k < claimW i ∨ claimW i + 76 ≤ k) (hk' : k < 2 ^ 61) :
    s'.mem (wd env.work k) = s.mem (wd env.work k) :=
  hw.word (fun r hr ↦ by rw [List.mem_singleton.mp hr]; simpa [claimR, Region.stop] using hk) hk'
    (by simp [claimR, claimW, Region.stop]; omega)

/-- Claim `j` survives claim `i`'s run. -/
theorem pc_keep {s' : QState} {i j : Nat} {c : ColumnClaimW} (hw : Wrote env [claimR i] s s')
    (hi4 : i < 4) (hj : j < 4) (hij : j ≠ i)
    (h : ColumnClaimAt s.mem (wd env.work (claimW j)) c) :
    ColumnClaimAt s'.mem (wd env.work (claimW j)) c :=
  h.congr fun k hk ↦ by
    rw [pc_claimWords] at hk
    rw [wd_wd]
    exact pc_word hw hi4 (by unfold claimW; omega) (by unfold claimW; omega)

/-- A claim after a run writing the claims since `s0`. -/
theorem pc_next {s0 : QState} {i col li vw n : Nat} {pt : Array EW} {v : EW} {xs : List Stmt}
    {P : QState → Prop} (hi4 : i < 4) (hcol : col < 2 ^ 63) (hli : li < 2)
    (hrdi : s0.reg .rdi = env.ctx) (h14 : s.reg .r14 = env.work) (hi : Inputs env inp s0.mem)
    (hw : Wrote env [claimsR] s0 s)
    (hpt : EWArr s0.mem (wd env.work 52704) pt) (hps : pt.size ≤ 63)
    (hn : NatAt s0.mem (wd env.work (lenW li)) n) (hnp : n ≤ pt.size) (hn30 : n ≤ 30)
    (hv : EWAt s0.mem (wd env.work vw) v) (hvw : vw % 2 = 0 ∧ vw + 1 < 2 ^ 60) (hv0 : 27730 ≤ vw)
    (k : ∀ s', ColumnClaimAt s'.mem (wd env.work (claimW i)) ⟨col, pt.extract 0 n, v⟩ →
      Wrote env [claimR i] s s' → Wrote env [claimsR] s0 s' → WP (blk xs) s' P E) :
    WP (blk (claimOne i col li vw :: xs)) s P E := by
  have hbd : ∀ r ∈ [claimsR], r.stop ≤ 2 ^ 61 := by
    simp [Region.stop, claimsR_off, claimsR_size]
  have kw : ∀ j, 27730 ≤ j → j < 2 ^ 60 → s.mem (wd env.work j) = s0.mem (wd env.work j) :=
    fun j h1 h2 ↦ hw.word (fun r hr ↦ by
      rw [List.mem_singleton.mp hr, Region.stop, claimsR_off, claimsR_size]; right; omega) (by omega) hbd
  refine WP.blk_cons (WP.mono (claimOne_spec (n := n) hi4 hcol hli (by rw [hw.rdi, hrdi]) h14
    (hi.step3 (fun r hr ↦ by rw [List.mem_singleton.mp hr]; exact ok3_claimsR) hw.step hrdi)
    (hpt.congr (n := 2 * pt.size) (fun j hj ↦ by
      rw [wd_wd]; exact kw _ (by omega) (by omega)) le_rfl) hps
    (hn.congr (kw _ (by unfold lenW; omega) (by unfold lenW; omega))) hnp hn30
    (hv.congr fun j hj ↦ by rw [wd_wd]; exact kw _ (by omega) (by omega)) hvw
    (by right; unfold claimW; omega)) ?_ fun _ h ↦ h)
  rintro s' ⟨hc, hw'⟩
  exact k s' hc hw' (hw.trans (hw'.widen fun r hr ↦
    ⟨claimsR, by simp, by rw [List.mem_singleton.mp hr]; exact pc_within hi4⟩))

/-- **The bus's claims.** -/
def claimsCode : Stmt := blk [
  I (.load .r14 (cw ctxWork)), I (.storei (at_ .r14 (wdisp claimsR.off)) 4),
  claimOne 0 memory0 0 52840, I (.load .r14 (cw ctxWork)),
  claimOne 1 memory1 0 52842, I (.load .r14 (cw ctxWork)),
  claimOne 2 memoryFinalCounters 0 52844, I (.load .r14 (cw ctxWork)),
  claimOne 3 bytecodeFinalCounters 1 52846]

theorem pc_claimAt (i : Nat) :
    wd (claimsR.at env.work) (1 + claimWords * i) = wd env.work (claimW i) := by
  rw [Region.at, wd_wd, claimsR_off, pc_claimWords]; unfold claimW; congr 1; omega

/-- **The bus's claims**, from the GKR point, the two lengths, the memory's limbs and the final
counters. -/
theorem claims_spec {lm lb : Nat} {pt : Array EW} {m0 m1 mf bf : EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hi : Inputs env inp s.mem)
    (hpt : EWArr s.mem (pointR.at env.work) pt) (hps : pt.size < 64)
    (hl0 : NatAt s.mem (wd env.work (lenW 0)) (min lm pt.size))
    (hl1 : NatAt s.mem (wd env.work (lenW 1)) (min lb pt.size)) (hlm : lm ≤ 30) (hlb : lb ≤ 30)
    (hm : EWArr s.mem (memR.at env.work) #[m0, m1]) (hmf : EWAt s.mem (memFinalR.at env.work) mf)
    (hbf : EWAt s.mem (bcFinalR.at env.work) bf) :
    WP claimsCode s (fun s' ↦ ClaimsAt s'.mem (claimsR.at env.work)
        #[⟨memory0, pt.extract 0 lm, m0⟩, ⟨memory1, pt.extract 0 lm, m1⟩,
          ⟨memoryFinalCounters, pt.extract 0 lm, mf⟩, ⟨bytecodeFinalCounters, pt.extract 0 lb, bf⟩] ∧
      Wrote env [claimsR] s s') E := by
  have hpt' : EWArr s.mem (wd env.work 52704) pt := by rwa [Region.at, pc_pointR_off] at hpt
  have hm0 : EWAt s.mem (wd env.work 52840) m0 := by
    have := hm 0 (by simp); rwa [Region.at, memR_off, wd_wd] at this
  have hm1 : EWAt s.mem (wd env.work 52842) m1 := by
    have := hm 1 (by simp); rwa [Region.at, memR_off, wd_wd] at this
  have hmf' : EWAt s.mem (wd env.work 52844) mf := by
    rwa [Region.at, show memFinalR.off = 52844 by decide] at hmf
  have hbf' : EWAt s.mem (wd env.work 52846) bf := by
    rwa [Region.at, show bcFinalR.off = 52846 by decide] at hbf
  have hc0 := hi.ok3_some' ok3_claimsR (a := 15569)
    (by rw [Region.stop, claimsR_off, claimsR_size]; omega)
  unfold claimsCode
  rw [claimsR_off]
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  refine wp_storei (eval_work (by rsimp) _) hc0 ?_
  have hcs : 15569 < claimsR.stop := by rw [Region.stop, claimsR_off, claimsR_size]; omega
  have w1 : Wrote env [claimsR] s
      ((s.setReg .r14 env.work).setMem (wd env.work 15569) (4 : Int64).toUInt64) :=
    wrote_store (s := s) (r := claimsR) (s1 := s.setReg .r14 env.work) (List.mem_singleton_self _)
      (le_of_eq claimsR_off) hcs rfl (by rsimp) hc0 _
  refine pc_next (s0 := s) (by decide) (by decide) (by decide) hrdi (by rsimp) hi w1 hpt' (by omega)
    hl0 (by omega) (by omega) hm0 ⟨by decide, by decide⟩ (by decide) fun s2 c0 w12 w2 ↦ ?_
  refine wp_load (eval_cw (by rw [w2.rdi, hrdi]) ctxWork) (by rw [pc_ctx w2 hi]; exact hwp) ?_
  refine pc_next (s0 := s) (by decide) (by decide) (by decide) hrdi (by rsimp) hi
    (w2.setReg (by decide) _) hpt' (by omega) hl0 (by omega) (by omega) hm1 ⟨by decide, by decide⟩
    (by decide) fun s3 c1 w23 w3 ↦ ?_
  refine wp_load (eval_cw (by rw [w3.rdi, hrdi]) ctxWork) (by rw [pc_ctx w3 hi]; exact hwp) ?_
  refine pc_next (s0 := s) (by decide) (by decide) (by decide) hrdi (by rsimp) hi
    (w3.setReg (by decide) _) hpt' (by omega) hl0 (by omega) (by omega) hmf' ⟨by decide, by decide⟩
    (by decide) fun s4 c2 w34 w4 ↦ ?_
  refine wp_load (eval_cw (by rw [w4.rdi, hrdi]) ctxWork) (by rw [pc_ctx w4 hi]; exact hwp) ?_
  refine pc_next (s0 := s) (by decide) (by decide) (by decide) hrdi (by rsimp) hi
    (w4.setReg (by decide) _) hpt' (by omega) hl1 (by omega) (by omega) hbf' ⟨by decide, by decide⟩
    (by decide) fun s5 c3 w45 w5 ↦ WP.blk_nil ⟨⟨?_, ⟨?_, ?_⟩, ?_⟩, w5⟩
  · simp only [List.size_toArray, List.length_cons, List.length_nil]; decide
  · simp
  · have w23' := pc_unset w23 (by decide)
    have w34' := pc_unset w34 (by decide)
    have w45' := pc_unset w45 (by decide)
    rw [Region.at, claimsR_off, pc_word w45' (by decide) (by unfold claimW; omega) (by omega),
      pc_word w34' (by decide) (by unfold claimW; omega) (by omega),
      pc_word w23' (by decide) (by unfold claimW; omega) (by omega),
      pc_word w12 (by decide) (by unfold claimW; omega) (by omega)]
    simp; rfl
  · have w23' := pc_unset w23 (by decide)
    have w34' := pc_unset w34 (by decide)
    have w45' := pc_unset w45 (by decide)
    intro i hi'
    rw [pc_claimAt]
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi'
    rw [pc_extract_min] at c0 c1 c2 c3
    interval_cases i
    · exact pc_keep w45' (by decide) (by decide) (by decide) <|
        pc_keep w34' (by decide) (by decide) (by decide) <|
        pc_keep w23' (by decide) (by decide) (by decide) c0
    · exact pc_keep w45' (by decide) (by decide) (by decide) <|
        pc_keep w34' (by decide) (by decide) (by decide) c1
    · exact pc_keep w45' (by decide) (by decide) (by decide) c2
    · exact c3

end NativeVm.Code.P3
