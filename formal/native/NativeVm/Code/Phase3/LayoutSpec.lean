module

public import NativeVm.Code.Phase3.LayoutSide

/-!
# Phase 3's placements: the contract

`depthC_spec`: the push side's depth, `log2Ceil` of its total size, as the bit length of the total
less one. `layout_spec`: the three sides' placements (`SidesAt`) and the push side's depth.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Protocol.Verifier

variable {env : Env} {inp : Input} {s : QState} {E : QState → Prop}

/-! ## Bit lengths -/

theorem bitLength_div (n : Nat) (hn : n ≠ 0) : bitLength n = bitLength (n / 2) + 1 := by
  unfold bitLength
  by_cases h2 : n / 2 = 0
  · have : ¬ 2 ≤ n := by omega
    simp only [hn, h2, ↓reduceIte, Nat.log2_def n, this]
  · have : 2 ≤ n := by omega
    simp only [hn, h2, ↓reduceIte, Nat.log2_def n, this]

theorem bitLength_le' {n k : Nat} (h : n < 2 ^ k) : bitLength n ≤ k := by
  unfold bitLength
  split
  · omega
  · have := (Nat.log2_lt (by omega)).mpr h
    omega

/-! ## The depth -/

theorem depthC_spec {p : UInt64} {v : Nat} (h15 : s.reg .r15 = p) (hsi : s.reg .rsi = v.toUInt64)
    (hv1 : 1 ≤ v) (hv : v < 2 ^ 64) (hd : (s.mem (wd p depthR.off)).isSome) :
    WP depthC s (fun s' ↦ s'.mem (wd p depthR.off) = some (log2Ceil v).toUInt64 ∧
      (∀ a, a ≠ wd p depthR.off → s'.mem a = s.mem a) ∧
      (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧ RegsFrame [.rax, .rdx] s s') E := by
  unfold depthC
  fstep; fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ d, u.reg .rdx = d.toUInt64 ∧
      d + bitLength (u.reg .rax).toNat = bitLength (v - 1) ∧ u.mem = s.mem ∧
      RegsFrame [.rax, .rdx] s u) (fun u ↦ (u.reg .rax).toNat)
  · refine ⟨0, by rsimp; rfl, ?_, by rsimp, by rf_tac⟩
    rsimp
    rw [hsi, toUInt64_sub_one hv1 hv, toNat_toUInt64 (by omega), Nat.zero_add]
  · rintro u ⟨d, hd', hb, hm, hf⟩ hc
    have hne : (u.reg .rax).toNat ≠ 0 := fun h ↦ by
      have : u.reg .rax = 0 := UInt64.toNat_inj.mp (by simpa using h)
      rw [cond_ne, rhs_imm, this, Field.int64Zero_toUInt64] at hc; simp at hc
    fstep; fstep; fdone
    have e : (u.reg .rax >>> 1).toNat = (u.reg .rax).toNat / 2 := by
      rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
    refine ⟨⟨d + 1, by rw [hd', toUInt64_succ], ?_, hm, by rf_tac; exact hf⟩, ?_⟩
    · rw [e, ← hb, bitLength_div _ hne]; omega
    · rw [e]; omega
  · rintro u ⟨d, hd', hb, hm, hf⟩ hc
    have h0 : u.reg .rax = 0 := by
      rw [cond_ne, rhs_imm, Field.int64Zero_toUInt64] at hc; simpa using hc
    have hl : log2Ceil v = d := by
      rw [h0, show (0 : UInt64).toNat = 0 from rfl, show bitLength 0 = 0 from rfl] at hb
      rw [log2Ceil, ← hb]; rfl
    have hd'' : (u.mem (wd p depthR.off)).isSome := by rw [hm]; exact hd
    refine wp_store (eval_aW (by rw [hf .r15 (by decide)]; exact h15) _) hd'' ?_
    refine WP.blk_nil ⟨by rw [setMem_same, hd', hl], fun a ha ↦ ?_, fun a ↦ ?_, rf_setMem hf _ _⟩
    · rw [QState.setMem_mem, ite_eq_right_of_eq_false _ _ (eq_false ha), hm]
    · rw [dom_setMem hd'', hm]

/-! ## The contract -/

theorem sreg_apart {a b m n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) : (sreg a m).Apart (sreg b n) := by
  unfold Region.Apart Region.stop sreg; simp only; omega

theorem totF_pos {S : Array Nat} (h : 0 < S.size) : 0 < totF S := by
  unfold totF
  obtain ⟨n, hn⟩ : ∃ n, S.size = n + 1 := ⟨S.size - 1, by omega⟩
  rw [hn, List.range_succ, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have := Nat.one_le_two_pow (n := S.getD n 0)
  omega

/-- The regions the placements' code writes. -/
abbrev layoutWs : List Region := [depthR, placeR 0, placeR 1, placeR 2, tmpR]

theorem ok3_layoutWs : ∀ r ∈ layoutWs, Ok3 r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact ok3_sreg (by omega)

/-- **Phase 3's placements**: the three sides' (`SidesAt`) and the push side's depth. -/
theorem layout_spec {env : Env} {inp : Input} {s : QState} {layout : LayoutW} {rate : Nat}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hi : Inputs env inp s.mem) (hl : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate) :
    WP layoutCode s (fun s' ↦ SidesAt s'.mem env.work layout ∧
        NatAt s'.mem (depthR.at env.work) (sideLayout layout 0).depth ∧
        Wrote env [depthR, placeR 0, placeR 1, placeR 2, tmpR] s s') (fun _ ↦ False) := by
  obtain ⟨rows, -, -, hbb⟩ := hl.rows
  have hws := ok3_layoutWs
  unfold layoutCode
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  have hw0 : Wrote env layoutWs s (s.setReg .r15 env.work) :=
    (Wrote.refl env layoutWs s).setReg (by decide) _
  -- the push side
  refine wp_then (sideC_spec (side := 0) (by decide) (by rsimp; exact hrdi) (by rsimp) hi hl)
    fun s₁ ⟨a15, aS, asi, at', aw⟩ ↦ ?_
  have hw1 : Wrote env layoutWs s s₁ := hw0.trans (aw.mono (by simp))
  have hi1 := hi.step3 hws hw1.step hrdi
  -- the depth
  have hS0 : 0 < (sizesOf (sideFr layout 0) (sideBlocks layout 0)).size := by
    rw [sizes_size, sideFr_size, sideBlocks_size hbb (by decide)]; decide
  have hdd : (s₁.mem (wd env.work depthR.off)).isSome :=
    hi1.ok3_some' (ok3_sreg (off := 209) (size := 1) (by omega)) (by simp [depthR, sreg, Region.stop])
  refine wp_then (depthC_spec a15 asi (totF_pos hS0) (by omega) hdd)
    fun s₂ ⟨b0, bo, bd, bf⟩ ↦ ?_
  have hw12 : Wrote env [depthR] s₁ s₂ := ⟨bf .rdi (by decide), fun a ha ↦ bo a fun e ↦
    ha depthR (by simp) ⟨0, by simp [depthR, sreg], by rw [e, Nat.add_zero]⟩, bd⟩
  have hw2 : Wrote env layoutWs s s₂ := hw1.trans (hw12.mono (by simp))
  have hi2 := hi.step3 hws hw2.step hrdi
  have hl2 := hl.congr (hw2.same (q := layoutR) hi hws (ok0_of_mem List.mem_cons_self)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      unfold Region.Apart Region.stop
      rw [layoutR_off, layoutR_size]
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [depthR, placeR, tmpR, sreg, scratchR_off]))
  -- the pull side
  refine wp_then (sideC_spec (side := 1) (by decide) (by rw [hw2.rdi, hrdi])
    (by rw [bf .r15 (by decide), a15]) hi2 hl2) fun s₃ ⟨c15, cS, _, _, cw⟩ ↦ ?_
  have hw3 : Wrote env layoutWs s s₃ := hw2.trans (cw.mono (by simp))
  have hi3 := hi.step3 hws hw3.step hrdi
  have hl3 := hl.congr (hw3.same (q := layoutR) hi hws (ok0_of_mem List.mem_cons_self)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      unfold Region.Apart Region.stop
      rw [layoutR_off, layoutR_size]
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [depthR, placeR, tmpR, sreg, scratchR_off]))
  -- the count side
  apply WP.blk_cons
  refine WP.mono (sideC_spec (side := 2) (by decide) (by rw [hw3.rdi, hrdi]) c15 hi3 hl3)
    (fun s₄ ⟨_, dS, _, _, dw⟩ ↦ WP.blk_nil ?_) fun _ h ↦ h
  have hw4 : Wrote env layoutWs s s₄ := hw3.trans (dw.mono (by simp))
  have w14 : Wrote env [depthR, placeR 1, placeR 2] s₁ s₄ :=
    ((hw12.mono (by simp)).trans (cw.mono (by simp))).trans (dw.mono (by simp))
  have w24 : Wrote env [placeR 1, placeR 2] s₂ s₄ := (cw.mono (by simp)).trans (dw.mono (by simp))
  have hok1 : ∀ r ∈ [depthR, placeR 1, placeR 2], Ok3 r := fun r hr ↦ hws r (by simp at hr ⊢; tauto)
  have hok2 : ∀ r ∈ [placeR 1, placeR 2], Ok3 r := fun r hr ↦ hws r (by simp at hr ⊢; tauto)
  refine ⟨fun side hs ↦ ?_, ?_, hw4⟩
  · interval_cases side
    · exact aS.congr (w14.same hi1 hok1 (ok3_placeR (by decide)).ok0 (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact sreg_apart (by omega)))
    · exact cS.congr (dw.same hi3 (ok3_place_all (side := 2) (by decide))
        (ok3_placeR (by decide)).ok0 (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl; exact sreg_apart (by omega)))
    · exact dS
  · have hd := (busLayout_all (sideFr layout 0) (sideBlocks layout 0)).2.1
    rw [← sideLayout_eq] at hd
    rw [hd]
    have hsame := w24.same (q := depthR) hi2 hok2 (ok3_sreg (by omega)).ok0 (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact sreg_apart (by omega))
    refine ⟨?_, ?_⟩
    · have := bitLength_le' (n := totF (sizesOf (sideFr layout 0) (sideBlocks layout 0)) - 1)
        (k := 37) (by omega)
      exact lt_of_le_of_lt (by unfold log2Ceil; exact this) (by norm_num)
    · rw [Region.at, ← b0]
      have := hsame 0 (by simp [depthR, sreg])
      simp only [Region.at, wd_zero] at this
      exact this

end NativeVm.Code.P3
