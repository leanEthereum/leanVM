module

public import NativeVm.Code.Phase4.Frames
public import NativeVm.Code.Phase4.MaxH

/-!
# A table's row: its point and its evaluations' count

`copyC_spec`: the point's first `n` coordinates copied; `rowPreC_spec`: table `k`'s point
(`point.extract 0 heights[k]`) and its evaluations' count to its entry of `evalsR`, `r12`, `r13`
set for `readN`.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env} {s : QState} {E : QState → Prop}

theorem extract_succ {xs : Array EW} {i : Nat} (h : i < xs.size) :
    xs.extract 0 (i + 1) = (xs.extract 0 i).push xs[i] := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.size_extract, Array.size_push] at h1 h2
    rw [Array.getElem_extract, Array.getElem_push]
    split
    · rw [Array.getElem_extract]
    · simp only [Array.size_extract] at *
      congr 1; omega

/-- An element stored after an array in memory. -/
theorem EWArr.snoc {mem mem' : UInt64 → Option UInt64} {w : UInt64} {b : Nat} {xs : Array EW}
    {x : EW} (h : EWArr mem (wd w b) xs) (h0 : mem' (wd w (b + 2 * xs.size)) = some x.c0)
    (h1 : mem' (wd w (b + 2 * xs.size + 1)) = some x.c1)
    (hr : ∀ k < 2 * xs.size, mem' (wd w (b + k)) = mem (wd w (b + k))) :
    EWArr mem' (wd w b) (xs.push x) := by
  intro j hj
  rw [Array.size_push] at hj
  rw [Array.getElem_push]
  simp only [EWAt, wd_wd]
  split
  · have := h j (by omega)
    simp only [EWAt, wd_wd] at this
    rw [hr (2 * j) (by omega), show b + 2 * j + 1 = b + (2 * j + 1) by omega, hr _ (by omega),
      ← show b + 2 * j + 1 = b + (2 * j + 1) by omega]
    exact this
  · have : j = xs.size := by omega
    subst this
    exact ⟨h0, h1⟩

/-- **The copy** of `n` elements from `wd w a` to `wd w b`. -/
theorem copyC_spec {a b n : Nat} {xs : Array EW} (hn : n ≤ xs.size) (hb : 69 ≤ b)
    (hbe : b + 2 * n ≤ 85438) (hab : a + 2 * xs.size ≤ b ∨ b + 2 * n ≤ a) (ha : a + 2 * xs.size ≤ 85438)
    (hws : WS env s) (hx : EWArr s.mem (wd env.work a) xs)
    (h13 : s.reg .r13 = wd env.work a) (h12 : s.reg .r12 = wd env.work b)
    (h15 : s.reg .r15 = n.toUInt64) :
    WP copyC s (fun s' ↦ EWArr s'.mem (wd env.work b) (xs.extract 0 n) ∧
      Wr env.work (fun k ↦ b ≤ k ∧ k < b + 2 * n) s s' ∧
      RegsFrame [.rax, .r12, .r13, .r15] s s') E := by
  unfold copyC
  apply WP.loop (fun t ↦ ∃ i ≤ n, t.reg .r13 = wd env.work (a + 2 * i) ∧
      t.reg .r12 = wd env.work (b + 2 * i) ∧ t.reg .r15 = (n - i).toUInt64 ∧
      EWArr t.mem (wd env.work b) (xs.extract 0 i) ∧
      Wr env.work (fun k ↦ b ≤ k ∧ k < b + 2 * i) s t ∧ RegsFrame [.rax, .r12, .r13, .r15] s t ∧
      WS env t)
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, by rw [h13]; rfl, by rw [h12]; rfl, by rw [h15]; rfl,
      fun i hi ↦ absurd hi (by simp), Wr.refl _ _ _, rf_refl _ _, hws⟩
  · rintro t ⟨i, hi, t13, t12, t15, harr, hw, hf, hwt⟩ hc
    have hin : i < n := (test_count t15 (by omega)).mp hc
    have hxi := hx i (by omega)
    simp only [EWAt, wd_wd] at hxi
    have hsrc : ∀ j, a + 2 * i ≤ j → j < a + 2 * i + 2 → t.mem (wd env.work j) = s.mem (wd env.work j) :=
      fun j h1 h2 ↦ hw.word (by omega) fun k hk ↦ ⟨by omega, by omega⟩
    refine wp_ldA (k := 0) t13 (by rw [hsrc _ (by omega) (by omega), Nat.add_zero]; exact hxi.1) ?_
    refine wp_stA (k := 0) (by rsimp; exact t12) (by rw [QState.setReg_mem]; exact hwt _ (by omega) (by omega)) ?_
    refine wp_ldA (k := 1) (by rsimp; exact t13) (by
      rw [QState.setMem_mem, ite_eq_right (fun e ↦ by
        rw [wd_inj (by omega) (by omega)] at e; omega), QState.setReg_mem,
        hsrc _ (by omega) (by omega)]
      exact hxi.2) ?_
    refine wp_stA (k := 1) (by rsimp; exact t12) (by
      apply isSome_setMem; rw [QState.setReg_mem]; exact hwt _ (by omega) (by omega)) ?_
    refine wp_addiA (k := 2) (by rsimp; exact t13) ?_
    refine wp_addiA (k := 2) (by rsimp; exact t12) ?_
    refine wp_regGuard (by decide) ?_
    fstep
    fdone
    refine ⟨⟨i + 1, by omega, by rw [Nat.mul_add, Nat.add_assoc], by rw [Nat.mul_add, Nat.add_assoc],
      ?_, ?_, ?_, by rfw, ?_⟩, ?_⟩
    · rw [t15]; exact natSub_toUInt64 hin
    · rw [extract_succ (by omega)]
      refine EWArr.snoc harr ?_ ?_ fun k hk ↦ ?_
      · rw [Array.size_extract, Nat.min_eq_left (by omega), Nat.sub_zero]
        simp only [QState.setReg_mem, QState.setMem_mem]
        rw [ite_eq_right (fun e ↦ by rw [wd_inj (by omega) (by omega)] at e; omega),
          ite_eq_left (by rw [Nat.add_zero])]
      · rw [Array.size_extract, Nat.min_eq_left (by omega), Nat.sub_zero]
        simp only [QState.setMem_mem, ↓reduceIte]
      · rw [Array.size_extract] at hk
        simp only [QState.setReg_mem, QState.setMem_mem]
        rw [ite_eq_right (fun e ↦ by rw [wd_inj (by omega) (by omega)] at e; omega),
          ite_eq_right (fun e ↦ by rw [wd_inj (by omega) (by omega)] at e; omega)]
    · exact (hw.mono fun k hk ↦ by omega).trans (by wr_tac)
    · exact WS.setMem (WS.setMem hwt _ _) _ _
    · rw [t15, show n - i = n - (i + 1) + 1 by omega, Field.toUInt64_succ_sub,
        Transcript.toNat_toUInt64 (by omega), Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro t ⟨i, hi, _, _, t15, harr, hw, hf, _⟩ hc
    have : i = n := by
      by_contra hne
      exact absurd ((test_count t15 (by omega)).mpr (by omega)) (by rw [hc]; decide)
    subst this
    exact ⟨harr, hw, hf⟩

/-- **Table `k`'s point and its evaluations' count** to its entry of `evalsR`. -/
theorem rowPreC_spec (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s) {k h width : Nat}
    (hk : k < 6) (hh : h ≤ 30) (hwd : width ≤ 92) {point : Array EW} (hph : h ≤ point.size)
    (hp30 : point.size ≤ 30)
    (hix : s.mem (wd env.work oTIX) = some k.toUInt64)
    (hep : s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * k)))
    (hhw : s.mem (wd env.work (oL + 4 + k)) = some h.toUInt64)
    (hwid : s.mem (wd env.work (oWID + k)) = some width.toUInt64)
    (hpt : EWArr s.mem (wd env.work oPT) point) :
    WP rowPreC s (fun s' ↦ EVec s'.mem (wd env.work (oE + eS * k)) tablePointCap (point.extract 0 h) ∧
      NatAt s'.mem (wd env.work (oE + eS * k + evOff)) width ∧
      s'.reg .r12 = wd env.work (oE + eS * k + evOff + 1) ∧ s'.reg .r13 = width.toUInt64 ∧
      Wr env.work (fun j ↦ oE + eS * k ≤ j ∧ j < oE + eS * k + evOff + 1) s s' ∧
      RegsFrame arrRegs s s') E := by
  have hix' := hix
  wnorm at hix' hep
  unfold rowPreC
  wst; wst
  refine wp_ldX (i := k) (by rsimp; rfl) (by rsimp) (by
    rw [QState.setReg_mem, show 0 + k + (oL + 4) = oL + 4 + k by omega]; exact hhw) ?_
  wst
  refine wp_stA (k := 0) (by rsimp; rfl) (by rw [QState.setReg_mem]; exact hws _ (by omega) (by omega)) ?_
  wst; wst
  refine WP.then (WP.dom (copyC_spec (a := 0 + oPT) (b := 14093 + 246 * k + 1) (n := h) (xs := point)
    hph (by omega) (by omega) (by simp only [oPT, oS]; omega) (by simp only [oPT, oS]; omega)
    (WS.setMem hws _ _) ?_ (by rsimp) (by rsimp) (by rsimp)))
    fun s1 ⟨⟨hc1, w1, rf1⟩, d1⟩ ↦ ?_
  · rw [Nat.zero_add]
    exact EWArr.wr (W := fun j ↦ j = 14093 + 246 * k + 0) (by wr_tac) hpt
      (by simp only [oPT, oS]; omega) fun j hj ↦ by simp only [oPT, oS]; omega
  have hb1 : s1.reg .rbp = wd env.work 0 := by rw [rf1 .rbp (by decide)]; rsimp
  have h14 : s1.reg .r14 = wd env.work (14093 + 246 * k) := by rw [rf1 .r14 (by decide)]; rsimp
  have wf1 := WF.ofWr (env := env) w1 fun j hj ↦ by omega
  have hix1 : s1.mem (wd env.work 52773) = some k.toUInt64 :=
    wf1.word (by omega) (by omega) (by omega) (by
      rw [QState.setReg_mem, QState.setReg_mem, QState.setMem_mem, ite_eq_right (fun e ↦ by
        rw [wd_inj (by omega) (by omega)] at e; omega)]
      exact hix')
  have hwid1 : s1.mem (wd env.work (oWID + k)) = some width.toUInt64 := by
    rw [show oWID + k = 52776 + k from rfl]
    refine wf1.word (by omega) (by omega) (by omega) ?_
    rw [QState.setReg_mem, QState.setReg_mem, QState.setMem_mem, ite_eq_right (fun e ↦ by
      rw [wd_inj (by omega) (by omega)] at e; omega)]
    exact hwid
  wst
  refine wp_ldX (i := k) (by rsimp; exact hb1) (by rsimp) (by
    rw [QState.setReg_mem, show 0 + k + oWID = oWID + k by omega]; exact hwid1) ?_
  refine wp_stA (k := evOff) (by rsimp; exact h14) (by
    rw [QState.setReg_mem, QState.setReg_mem]
    exact WS.wr (WS.setMem hws _ _) d1 _ (by simp only [evOff]; omega)
      (by simp only [evOff]; omega)) ?_
  refine wp_leaA (k := evOff + 1) (by rsimp; exact h14) ?_
  refine wp_done_gen fun s' hs' ↦ ?_
  subst hs'
  have hh0 : (s1.mem (wd env.work (14093 + 246 * k))) = some h.toUInt64 := by
    refine (w1.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩).trans ?_
    simp only [QState.setReg_mem, QState.setMem_mem, Nat.add_zero, ↓reduceIte]
    rfl
  refine ⟨⟨by rw [Array.size_extract]; simp only [tablePointCap]; omega, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Array.size_extract, Nat.min_eq_left hph, Nat.sub_zero]; omega
  · simp only [QState.setReg_mem, QState.setMem_mem]
    rw [ite_eq_right (fun e ↦ by rw [wd_inj (by p4omega) (by p4omega)] at e; simp only [oE, eS, evOff] at e ⊢; omega),
      Array.size_extract, Nat.min_eq_left hph, Nat.sub_zero]
    simpa using hh0
  · rw [wd_wd]
    simp only [oE, eS]
    exact EWArr.wr (W := fun j ↦ j = 14093 + 246 * k + evOff) (by wr_tac) hc1
      (by rw [Array.size_extract]; omega) fun j hj ↦ by
        simp only [evOff] at hj ⊢; rw [Array.size_extract]; omega
  · refine ⟨by omega, ?_⟩
    memw
  · rsimp
    congr 1
  · rsimp
  · simp only [oE, eS, evOff]
    refine Wr.trans (Wr.trans ?_ (w1.mono fun j hj ↦ ⟨by omega, by omega⟩)) ?_
    · wr_tac
    · wr_tac
  · refine rf_arr_of ?_ ?_
    · rsimp; rw [rf1 .rdi (by decide)]; rsimp
    · rsimp; rw [rf1 .rsp (by decide)]; rsimp

end NativeVm.Code.P4
