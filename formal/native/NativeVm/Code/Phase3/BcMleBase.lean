module

public import NativeVm.Code.Phase3.BcMleCode

/-!
# The bytecode's multilinear extension: runs that write only `tmpR`

Every part of `bcCode` writes no word outside `tmpR` (`Wrote env [tmpR] s0 s` from the start
`s0`): the words outside it, the context's and the bytecode's are the start's (`bc_out`, `bc_ctx`,
`bc_word`), and a store to a word of `tmpR` keeps the run so (`bc_set`). Then the specifications of
`bcMin` and `bcCopy`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Field NativeVm.Transcript NativeVm.Code

variable {env : Env} {inp : Input} {s0 s : QState}

theorem bc_tmp_off : tmpR.off = 54718 := by decide
theorem bc_tmp_size : tmpR.size = 6144 := (rfl)

/-- Unfold the regions' offsets, then `omega`. -/
scoped macro "bc_omega" : tactic => `(tactic| first
  | omega
  | (simp only [tmpR, pointR, slotR, depthR, valueR, layoutR_off, sreg, scratchR_off, bcStW, bcPtW,
      Region.stop, bc_tmp_off, bc_tmp_size] at *
     omega))

theorem bc_work_le (hi : Inputs env inp s0.mem) :
    85438 ≤ workWords inp.bytecode.size ∧ workWords inp.bytecode.size ≤ 2 ^ 61 :=
  ⟨dataEnd_val ▸ dataEnd_le _, workWords_lt hi⟩

/-- A word of the working area outside `tmpR` is the start's. -/
theorem bc_out (hw : Wrote env [tmpR] s0 s) {k : Nat} (hk : k < 54718 ∨ 60862 ≤ k)
    (hk2 : k < 2 ^ 61) : s.mem (wd env.work k) = s0.mem (wd env.work k) := by
  refine hw.mem _ fun r hr ⟨j, hj, e⟩ ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [bc_tmp_size] at hj
  rw [bc_tmp_off, wd_inj hk2 (by omega)] at e
  omega

/-- A context word is the start's. -/
theorem bc_ctx (hw : Wrote env [tmpR] s0 s) (hi : Inputs env inp s0.mem) {j : Nat}
    (hj : j < ctxEnd) : s.mem (wd env.ctx j) = s0.mem (wd env.ctx j) := by
  have := bc_work_le hi
  refine hw.mem _ fun r hr ⟨k, hk, e⟩ ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [bc_tmp_size] at hk
  rw [bc_tmp_off] at e
  exact hi.ctx_ne_work hj (by omega) e

/-- A word of the bytecode. -/
theorem bc_word (hw : Wrote env [tmpR] s0 s) (hi : Inputs env inp s0.mem) {i : Nat}
    (h : i < inp.bytecode.size) : s.mem (wd inp.bcA i) = some inp.bytecode[i] := by
  have := bc_work_le hi
  rw [← hi.bcWords i h]
  refine hw.mem _ fun r hr ⟨k, hk, e⟩ ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [bc_tmp_size] at hk
  rw [bc_tmp_off] at e
  exact wd_ne_of_disj hi.fitBc hi.fitWork hi.disjBcWork h (by omega) e

theorem bc_some (hw : Wrote env [tmpR] s0 s) (hi : Inputs env inp s0.mem) {k : Nat}
    (hk : k < 85438) : (s.mem (wd env.work k)).isSome := by
  rw [hw.dom]
  exact hi.workSome k (by have := bc_work_le hi; omega)

/-- A store to a word of `tmpR`. -/
theorem bc_set (hw : Wrote env [tmpR] s0 s) (hi : Inputs env inp s0.mem) {k : Nat}
    (h1 : 54718 ≤ k) (h2 : k < 60862) (v : UInt64) :
    Wrote env [tmpR] s0 (s.setMem (wd env.work k) v) := by
  have := hw.setMem (r := tmpR) (by simp) (k := k - 54718) (by rw [bc_tmp_size]; omega)
    (by rw [bc_tmp_off, show 54718 + (k - 54718) = k by omega]; exact bc_some hw hi (by omega)) v
  rwa [bc_tmp_off, show 54718 + (k - 54718) = k by omega] at this

theorem bc_eval0 {b : Reg64} {p : UInt64} {k : Nat} (h : s.reg b = wd p k) :
    (at_ b 0).eval s = wd p k := by
  rw [Transcript.eval_at, h, int64Zero_toUInt64, UInt64.add_zero]

theorem bc_eval8 {b : Reg64} {p : UInt64} {k : Nat} (h : s.reg b = wd p k) :
    (at_ b 8).eval s = wd p (k + 1) := by
  rw [Transcript.eval_at, h, show (8 : Int64).toUInt64 = (8 * 1 : Nat).toUInt64 from rfl, wd_add]

theorem bc_wd8 (p : UInt64) (k : Nat) : wd p k + 8 = wd p (k + 1) := by
  rw [show (8 : UInt64) = (8 * 1 : Nat).toUInt64 from rfl, wd_add]

/-! ## `bcMin` -/

theorem bc_min_toUInt64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if decide (b.toUInt64 < a.toUInt64) = true then b.toUInt64 else a.toUInt64) =
      (min a b).toUInt64 := by
  by_cases h : b < a
  · simp only [decide_eq_true_iff, toUInt64_lt hb ha, h, ↓reduceIte]; congr 1; omega
  · simp only [decide_eq_true_iff, toUInt64_lt hb ha, h, ↓reduceIte]; congr 1; omega

/-- **`bcMin`**: `rax := min(logBytecode, depth)`, `r11` the working area. -/
theorem bcMin_spec {logB d : Nat} {E : QState → Prop} (hrdi : s.reg .rdi = env.ctx)
    (hwk : s.mem (wd env.ctx ctxWork) = some env.work)
    (hl : NatAt s.mem (wd env.work (layoutR.off + 1)) logB)
    (hd : NatAt s.mem (wd env.work depthR.off) d) :
    WP bcMin s (fun s' ↦ s'.mem = s.mem ∧ s'.reg .rax = (min logB d).toUInt64 ∧
      s'.reg .r11 = env.work ∧ RegsFrame [.rax, .rbx, .r11] s s') E := by
  unfold bcMin
  refine wp_load (eval_cw hrdi _) hwk ?_
  refine wp_load (eval_work (by rsimp) _) hl.2 ?_
  refine wp_load (eval_work (by rsimp) _) hd.2 ?_
  refine WP.blk_cons (WP.ite ?_)
  rw [cond_ltu, rhs_reg]
  rsimp
  split
  · rename_i hc
    refine WP.ins rfl (WP.blk_nil ⟨rfl, ?_, by rsimp, by rf_tac⟩)
    rsimp
    rw [← bc_min_toUInt64 hl.1 hd.1]
    simp only [hc, ↓reduceIte]
  · rename_i hc
    refine WP.skip (WP.blk_nil ⟨rfl, ?_, by rsimp, by rf_tac⟩)
    rsimp
    rw [← bc_min_toUInt64 hl.1 hd.1]
    simp only [hc, ↓reduceIte, Bool.false_eq_true]

/-! ## `bcCopy` -/

/-- **`bcCopy`**: `rcx` words from `rsi` (before `tmpR`) to `rdx` (inside it). -/
theorem bcCopy_spec {a b n : Nat} {E : QState → Prop} (hw : Wrote env [tmpR] s0 s)
    (hi : Inputs env inp s0.mem) (hsi : s.reg .rsi = wd env.work a)
    (hdx : s.reg .rdx = wd env.work b) (hcx : s.reg .rcx = n.toUInt64) (han : a + n ≤ 54718)
    (hb : 54718 ≤ b) (hbn : b + n ≤ 60862) :
    WP bcCopy s (fun s' ↦ Wrote env [tmpR] s0 s' ∧
      (∀ j < n, s'.mem (wd env.work (b + j)) = s.mem (wd env.work (a + j))) ∧
      (∀ x, (∀ j < n, x ≠ wd env.work (b + j)) → s'.mem x = s.mem x) ∧
      s'.reg .rsi = wd env.work (a + n) ∧ s'.reg .rdx = wd env.work (b + n) ∧
      RegsFrame [.rcx, .rsi, .rdx, .r8] s s') E := by
  unfold bcCopy
  apply WP.loop (fun t ↦ ∃ j ≤ n, t.reg .rcx = (n - j).toUInt64 ∧
      t.reg .rsi = wd env.work (a + j) ∧ t.reg .rdx = wd env.work (b + j) ∧
      Wrote env [tmpR] s0 t ∧
      (∀ j' < j, t.mem (wd env.work (b + j')) = s.mem (wd env.work (a + j'))) ∧
      (∀ x, (∀ j' < j, x ≠ wd env.work (b + j')) → t.mem x = s.mem x) ∧
      RegsFrame [.rcx, .rsi, .rdx, .r8] s t)
    (fun t ↦ (t.reg .rcx).toNat)
  · exact ⟨0, Nat.zero_le _, by rw [hcx]; rfl, hsi, hdx, hw, fun _ h ↦ absurd h (by omega),
      fun _ _ ↦ rfl, rf_refl _ _⟩
  · rintro t ⟨j, hj, tcx, tsi, tdx, tw, tc, tk, tf⟩ hc
    rw [cond_ne, rhs_imm, tcx, int64Zero_toUInt64, bne_iff_ne, ne_eq] at hc
    have hjn : j < n := by
      by_contra h'
      exact hc (by rw [show n - j = 0 by omega]; rfl)
    have hsrc : t.mem (wd env.work (a + j)) = s.mem (wd env.work (a + j)) :=
      tk _ fun j' _ e ↦ by rw [wd_inj (by omega) (by omega)] at e; omega
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (bc_some (s := s) hw hi (k := a + j) (by omega))
    refine wp_load (bc_eval0 tsi) (by rw [hsrc, hv]) ?_
    refine wp_store (bc_eval0 (by rsimp; exact tdx)) (by rsimp; exact bc_some tw hi (by omega)) ?_
    fstep; fstep; fstep; fdone
    refine ⟨⟨j + 1, hjn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [tcx, show n - j = (n - (j + 1)) + 1 by omega, toUInt64_succ_sub]
    · rw [tsi, bc_wd8]; rfl
    · rw [tdx, bc_wd8]; rfl
    · exact ((bc_set (tw.setReg (r := .r8) (by decide) v) hi (k := b + j) (by omega) (by omega)
        _).setReg (r := .rsi) (by decide) _
        |>.setReg (r := .rdx) (by decide) _ |>.setReg (r := .rcx) (by decide) _)
    · intro j' hj'
      simp only [QState.setReg_mem, QState.setMem_mem]
      split
      · rename_i e
        rw [wd_inj (by omega) (by omega)] at e
        rw [show j' = j by omega, hv]
      · exact tc j' (by
          rename_i e
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
          · exact h
          · exact absurd (by rw [h]) e)
    · intro x hx
      simp only [QState.setReg_mem, QState.setMem_mem]
      split
      · exact absurd ‹_› (hx j (by omega))
      · exact tk x fun j' hj' ↦ hx j' (by omega)
    · rf_tac; exact rf_setMem (rf_setReg tf (by simp) _) _ _
    · rw [tcx, show n - j = (n - (j + 1)) + 1 by omega, toUInt64_succ_sub,
        Transcript.toNat_toUInt64 (by omega), Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro t ⟨j, hj, tcx, tsi, tdx, tw, tc, tk, tf⟩ hc
    rw [cond_ne, rhs_imm, tcx, int64Zero_toUInt64, bne_eq_false_iff_eq] at hc
    have hjn : j = n := by
      have := toUInt64_eq_zero (show n - j < 2 ^ 64 by omega) hc
      omega
    subst hjn
    exact ⟨tw, tc, tk, tsi, tdx, tf⟩

end NativeVm.Code.P3
