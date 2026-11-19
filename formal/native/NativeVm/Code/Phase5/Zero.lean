module

public import NativeVm.Code.Phase2.Kit

/-!
# Zeroing a run of a region's words

`zeroLoop`: while `rdx ≠ 0`, two zero words at `rcx`, `rcx` two words on, `rdx` down by one; from
word `j0` of a region of the phase's, `2 m` words zeroed, nothing else written (`zeroLoop_spec`).
Phase 5 fills a point's zero coordinates with it.
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript

variable {env : Env} {inp : Input} {rs : List Region} {s0 s : QState}

/-- Two zero words at `rcx`; `rcx` past them, `rdx` down by one. -/
def zeroPair : Stmt := blk [
  I (.storei (at_ .rcx (wdisp 0)) 0), I (.storei (at_ .rcx (wdisp 1)) 0),
  I (.addi .rcx (wdisp 2)), I (.subi .rdx 1)]

/-- `rdx` pairs of zero words from `rcx`. -/
def zeroLoop : Stmt := .loop (.cmp .ne .rdx (.imm 0)) zeroPair

theorem cond_ne_zero {s : QState} {r : Reg64} {n : Nat} (h : s.reg r = n.toUInt64)
    (hn : n < 2 ^ 64) : (Cond.cmp .ne r (.imm 0)).eval s = true ↔ n ≠ 0 := by
  rw [cond_ne, rhs_imm, h, show ((0 : Int64).toUInt64) = (0 : Nat).toUInt64 from rfl, bne_iff_ne,
    ne_eq, toUInt64_inj hn (by omega)]

/-- **`zeroLoop`**: `2 m` zero words from word `j0` of the region `q`. -/
theorem zeroLoop_spec {t : TState} {q : Region} (hq : q ∈ rs) (hqr : q ∈ regions) {j0 m : Nat}
    (hm : j0 + 2 * m ≤ q.size) (hin : Inputs env inp s0.mem) (hc : CodeRel env t s)
    (hb : Base env rs s0 s) (hrcx : s.reg .rcx = wd env.work (q.off + j0))
    (hrdx : s.reg .rdx = m.toUInt64) {E : QState → Prop} :
    WP zeroLoop s (fun s' ↦ CodeRel env t s' ∧ Base env rs s0 s' ∧ RegsFrame [.rcx, .rdx] s s' ∧
      (∀ k < 2 * m, s'.mem (wd env.work (q.off + (j0 + k))) = some 0) ∧
      ∀ a, (∀ k < 2 * m, a ≠ wd env.work (q.off + (j0 + k))) → s'.mem a = s.mem a) E := by
  have hlt : ∀ k, k < q.size → q.off + k < 2 ^ 61 := fun k hk ↦ by
    have := region_lt (inp := inp) hqr hk
    have := workWords_lt hin
    omega
  have hm64 : m < 2 ^ 64 := by
    have := stop_le_of_mem hqr inp.bytecode.size
    have := workWords_lt hin
    unfold Region.stop at *
    omega
  refine WP.loop (fun s' ↦ ∃ j ≤ m, CodeRel env t s' ∧ Base env rs s0 s' ∧
      RegsFrame [.rcx, .rdx] s s' ∧ s'.reg .rcx = wd env.work (q.off + (j0 + 2 * j)) ∧
      s'.reg .rdx = (m - j).toUInt64 ∧
      (∀ k < 2 * j, s'.mem (wd env.work (q.off + (j0 + k))) = some 0) ∧
      ∀ a, (∀ k < 2 * j, a ≠ wd env.work (q.off + (j0 + k))) → s'.mem a = s.mem a)
    (fun s' ↦ (s'.reg .rdx).toNat)
    ⟨0, Nat.zero_le _, hc, hb, rf_refl _ _, by simpa using hrcx, by simpa using hrdx,
      fun k hk ↦ absurd hk (by omega), fun _ _ ↦ rfl⟩ ?_ ?_
  · rintro s1 ⟨j, hj, hc1, hb1, hf1, hx1, hd1, hz1, hk1⟩ hcond
    have hjm : j < m := by
      rw [cond_ne_zero hd1 (by omega)] at hcond
      omega
    have hA := hlt (j0 + 2 * j) (by omega)
    have hA' := hlt (j0 + 2 * j + 1) (by omega)
    unfold zeroPair
    have hs0 := hin.region_some hb1 hqr (j := j0 + 2 * j) (by omega)
    refine wp_storei (eval_region hx1 0) hs0 ?_
    have hb2 := hb1.setMem hq (j := j0 + 2 * j) (by omega) rfl hs0 (0 : Int64).toUInt64
    have hs1 := hin.region_some hb2 hqr (j := j0 + 2 * j + 1) (by omega)
    refine wp_storei (eval_region (by reg_simp; exact hx1) 1) hs1 ?_
    have hb3 := hb2.setMem hq (j := j0 + 2 * j + 1) (by omega) rfl hs1 (0 : Int64).toUInt64
    refine wp_reg rfl (wp_reg rfl (wp_done ⟨⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩))
    · exact (((hc1.setMem hin hqr (j := j0 + 2 * j) (by omega) rfl hs0 _).setMem hin hqr
        (j := j0 + 2 * j + 1) (by omega) rfl hs1 _).setReg (by decide) _).setReg (by decide) _
    · exact (hb3.setReg (by decide) _).setReg (by decide) _
    · exact rf_setReg (rf_setReg hf1 (by simp) _) (by simp) _
    · reg_simp
      rw [hx1, wdisp_toUInt64, wd_add]
      congr 1
    · reg_simp
      rw [hd1, toUInt64_sub1 (by omega)]
      congr 1
    · intro k hk
      simp only [QState.setReg_mem]
      by_cases hk' : k < 2 * j
      · rw [setMem_wd_ne _ _ (by omega) (hlt _ (by omega)) (hlt _ (by omega)),
          setMem_wd_ne _ _ (by omega) (hlt _ (by omega)) (hlt _ (by omega))]
        exact hz1 k hk'
      · by_cases hk2 : k = 2 * j
        · rw [setMem_wd_ne _ _ (by omega) (hlt _ (by omega)) (hlt _ (by omega)),
            setMem_wd_eq _ _ (by omega)]
          rfl
        · rw [setMem_wd_eq _ _ (by omega)]
          rfl
    · intro a ha
      simp only [QState.setReg_mem, QState.setMem_mem]
      rw [ite_of_not (fun e ↦ ha (2 * j + 1) (by omega) (e.trans (by congr 1))),
        ite_of_not (fun e ↦ ha (2 * j) (by omega) (e.trans (by congr 1)))]
      exact hk1 a fun k hk ↦ ha k (by omega)
    · reg_simp
      rw [hd1, toUInt64_sub1 (by omega), toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · rintro s1 ⟨j, hj, hc1, hb1, hf1, -, hd1, hz1, hk1⟩ hcond
    have hjm : j = m := by
      have := (cond_ne_zero hd1 (by omega)).not.mp (by rw [hcond]; decide)
      omega
    subst hjm
    exact ⟨hc1, hb1, hf1, hz1, hk1⟩

end NativeVm.Code
