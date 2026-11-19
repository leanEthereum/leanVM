module

public import NativeVm.Code.Phase1.Checks
public import NativeVm.Code.Data

/-!
# Phase 1's placements

`placeLoop_spec`: the loop writes every global column's placement, `plF κ c` (`PlacementAt`), three
words from word `16 + 3 c` of the layout, and no other word; `placeBody_spec` is one column.
-/

@[expose] public section

namespace NativeVm.Code.Phase1

open Native NativeVm.Model LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wdisp eval_wd toNat_toUInt64 wp_load wp_store wp_storei wp_then
  setMem_wd_ne setMem_wd_eq toUInt64_add toUInt64_succ wd_add rf_trans)

variable {s : QState} {E : QState → Prop}

/-! ## The columns' kinds -/

theorem block_kind : ∀ c < 158, isBlockF c = true → slotF c = none ∧ outF c = false := by decide

theorem slot_lo : ∀ c < 158, isBlockF c = false → c < 80 → slotF c = some (c - 16) ∧ 16 ≤ c := by
  decide

theorem slot_hi : ∀ c < 158, isBlockF c = false → 80 ≤ c → c < 106 →
    slotF c = some (c - 81) ∧ 81 ≤ c := by decide

theorem out_kind : ∀ c < 158, isBlockF c = false → 106 ≤ c → slotF c = none ∧ outF c = true := by
  decide

theorem plF_block {κ : Nat → Nat} {c : Nat} (hc : c < 158) (hb : isBlockF c = true) :
    plF κ c = some ⟨κ c, sumF κ (keyF κ c)⟩ := by
  obtain ⟨h1, h2⟩ := block_kind c hc hb
  simp [plF, h1, h2]

theorem plF_slot {κ : Nat → Nat} {c sl : Nat} (hs : slotF c = some sl) :
    plF κ c = some ⟨κ c, sumF κ (keyF κ 4) + sl * 2 ^ κ c⟩ := by
  simp [plF, hs]

theorem plF_out {κ : Nat → Nat} {c : Nat} (hs : slotF c = none) (ho : outF c = true) :
    plF κ c = none := by
  simp [plF, hs, ho]

/-! ## Words -/

theorem shl_u {x k : Nat} (hk : k < 64) :
    x.toUInt64 <<< (k.toUInt64 &&& 63) = (2 ^ k * x).toUInt64 := by
  have : k.toUInt64 &&& 63 = k.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, toNat_toUInt64 (by omega), show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [this, NativeVm.Transcript.toUInt64_shl _ _ hk]

theorem int64_ofNat_u {d : Nat} (hd : d < 2 ^ 63) : (Int64.ofNat d).toUInt64 = d.toUInt64 :=
  UInt64.toNat_inj.mp (by rw [lit_toNat d hd, toNat_toUInt64 (by omega)])

/-- The layout's words of the column `c`'s placement. -/
theorem eval_P {p : UInt64} {c : Nat} (h : s.reg .r15 = wd p (16 + 3 * c)) (j : Nat) :
    (at_ .r15 (wdisp j)).eval s = wd p (16 + 3 * c + j) := eval_wd h j

/-! ## One column -/

theorem placeBody_spec {p : UInt64} {lm lb c : Nat} {hs : Array Nat} (hr14 : s.reg .r14 = p)
    (hd : LDom p s.mem) (hm : KapMem s.mem p lm lb hs) (hc : c < 158)
    (hr12 : s.reg .r12 = c.toUInt64) (hr15 : s.reg .r15 = wd p (16 + 3 * c))
    (hrbp : s.reg .rbp = (sumF (kapF lm lb hs) (keyF (kapF lm lb hs) 4)).toUInt64) :
    WP placeBody s (fun s' ↦ PlacementAt s'.mem (wd p (16 + 3 * c)) (plF (kapF lm lb hs) c) ∧
      (∀ k, (k < 16 + 3 * c ∨ 16 + 3 * c + 3 ≤ k) → k < 2 ^ 61 →
        s'.mem (wd p k) = s.mem (wd p k)) ∧ LFr p s s' ∧
      s'.reg .r12 = (c + 1).toUInt64 ∧ s'.reg .r15 = wd p (16 + 3 * (c + 1)) ∧
      s'.reg .rbp = s.reg .rbp) E := by
  have hκ := hm.kap_le
  have k1 := hκ c
  have hQ := sumF_lt hκ (keyF (kapF lm lb hs) 4)
  unfold placeBody
  -- The end: the two increments.
  have fin : ∀ s₄ : QState, PlacementAt s₄.mem (wd p (16 + 3 * c)) (plF (kapF lm lb hs) c) →
      (∀ k, (k < 16 + 3 * c ∨ 16 + 3 * c + 3 ≤ k) → k < 2 ^ 61 →
        s₄.mem (wd p k) = s.mem (wd p k)) → LFr p s s₄ → s₄.reg .r12 = c.toUInt64 →
      s₄.reg .r15 = wd p (16 + 3 * c) → s₄.reg .rbp = s.reg .rbp →
      WP (blk [I (.addi .r12 1), I (.addi .r15 24)]) s₄ (fun s' ↦
        PlacementAt s'.mem (wd p (16 + 3 * c)) (plF (kapF lm lb hs) c) ∧
        (∀ k, (k < 16 + 3 * c ∨ 16 + 3 * c + 3 ≤ k) → k < 2 ^ 61 →
          s'.mem (wd p k) = s.mem (wd p k)) ∧ LFr p s s' ∧
        s'.reg .r12 = (c + 1).toUInt64 ∧ s'.reg .r15 = wd p (16 + 3 * (c + 1)) ∧
        s'.reg .rbp = s.reg .rbp) E := by
    intro s₄ g1 g2 g3 g4 g5 g6
    fstep; fstep
    fdone
    refine ⟨g1, g2, by fr_tac hd, by rw [g4, toUInt64_succ], ?_, g6⟩
    rw [g5, show (24 : UInt64) = (8 * 3 : Nat).toUInt64 from rfl, wd_add]
    congr 1
  fstep
  refine wp_then (kapC_spec (c := c) (by rsimp; exact hr14) (hm.congr (by rsimp)) (by omega)
    (by rsimp; exact hr12)) fun s₂ ⟨h2, m2, f2⟩ ↦ ?_
  have F2 : LFr p s s₂ := (show LFr p s (s.setReg .rsi (s.reg .r12)) by fr_tac hd).trans
    (LFr.of_regs m2 f2 (by decide) (by decide))
  have r2 : ∀ r, r ≠ .rax → r ≠ .rsi → s₂.reg r = s.reg r := fun r h1 h2 ↦ by
    rw [f2 r (by simp [h1])]; rsimp; simp [h2]
  refine wp_then (blockFlag_spec (c := c) (by omega) (by rw [f2 _ (by decide)]; rsimp; exact hr12))
    fun s₃ ⟨h3, m3, f3⟩ ↦ ?_
  have F3 := F2.trans (LFr.of_regs m3 f3 (by decide) (by decide))
  have r3 : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₃.reg r = s.reg r := fun r h1 h2 h4 ↦ by
    rw [f3 r (by simp [h4]), r2 r h1 h2]
  have hm3 : s₃.mem = s.mem := by rw [m3, m2]; rsimp
  have rax3 : s₃.reg .rax = (kapF lm lb hs c).toUInt64 := by rw [f3 _ (by decide), h2]
  apply WP.blk_cons
  refine wp_ite_of (b := isBlockF c) (by simp only [Cond.eval, Rhs.eval, h3]; cases isBlockF c <;> rfl)
    (fun hb ↦ ?_) (fun hb ↦ ?_)
  · -- A stacked column.
    unfold blockP
    fstep; fstep; fstep; fstep; fstep
    rw [rax3, r3 .r12 (by decide) (by decide) (by decide), hr12, key_u k1 hc]
    refine wp_then (sumC_spec (kr := keyF (kapF lm lb hs) c) (lm := lm) (lb := lb) (hs := hs)
      (by rsimp; rw [r3 _ (by decide) (by decide) (by decide), hr14])
      (hm.congr (by rsimp; exact hm3)) (by unfold keyF; omega) (by rsimp; rfl))
      fun s₅ ⟨h5, m5, f5⟩ ↦ ?_
    have F5 : LFr p s s₅ := (show LFr p s _ by fr_tac hd).trans
      (LFr.of_regs m5 f5 (by decide) (by decide))
    have hm5 : s₅.mem = s.mem := by rw [m5]; rsimp; exact hm3
    have r5 : ∀ r, r ∉ sumRegs → r ≠ .rbx → r ≠ .r8 → s₅.reg r = s.reg r := fun r h1 h2 h4 ↦ by
      rw [f5 r h1]; rsimp; simp only [h2, h4, ↓reduceIte]
      exact r3 r (fun e ↦ h1 (by simp [e])) (fun e ↦ h1 (by simp [e])) (fun e ↦ h1 (by simp [e]))
    have rbx5 : s₅.reg .rbx = (kapF lm lb hs c).toUInt64 := by
      rw [f5 _ (by decide)]; rsimp
    have r15 : s₅.reg .r15 = wd p (16 + 3 * c) := by
      rw [r5 _ (by decide) (by decide) (by decide), hr15]
    refine wp_storei (by rw [eval_P r15 0, Nat.add_zero]) (by rw [hm5]; exact hd _ (by omega)) ?_
    refine wp_store (eval_P (by rsimp; exact r15) 1) (NativeVm.Field.isSome_setMem
      (by rw [hm5]; exact hd _ (by omega)) _ _) ?_
    refine wp_store (eval_P (by rsimp; exact r15) 2) (NativeVm.Field.isSome_setMem
      (NativeVm.Field.isSome_setMem (by rw [hm5]; exact hd _ (by omega)) _ _) _ _) ?_
    refine WP.blk_nil (fin _ ?_ (fun k hk hk' ↦ ?_) ?_ ?_ ?_ ?_)
    · rw [plF_block hc hb]
      have hl := sumF_lt hκ (keyF (kapF lm lb hs) c)
      refine ⟨by mem_simp, ⟨by dsimp only; omega, ?_⟩, ⟨by dsimp only; omega, ?_⟩⟩
      · rw [wd_wd]; mem_simp; rw [rbx5]
      · rw [wd_wd]; mem_simp; rw [h5]
    · mem_simp; rw [hm5]
    · have := F5.setMem hd (k := 16 + 3 * c) (by omega) (Int64.toUInt64 1)
      have := this.setMem hd (k := 16 + 3 * c + 1) (by omega) ((s₅.setMem (wd p (16 + 3 * c))
        (Int64.toUInt64 1)).reg .rbx)
      exact this.setMem hd (k := 16 + 3 * c + 2) (by omega) _
    · rsimp; rw [r5 _ (by decide) (by decide) (by decide), hr12]
    · rsimp; exact r15
    · rsimp; exact r5 _ (by decide) (by decide) (by decide)
  -- A `q_keccak` slot `c - d`.
  have slot : ∀ d, d ≤ c → d < 2 ^ 31 → slotF c = some (c - d) →
      WP (slotP d) s₃ (fun s₄ ↦ WP (blk [I (.addi .r12 1), I (.addi .r15 24)]) s₄ (fun s' ↦
        PlacementAt s'.mem (wd p (16 + 3 * c)) (plF (kapF lm lb hs) c) ∧
        (∀ k, (k < 16 + 3 * c ∨ 16 + 3 * c + 3 ≤ k) → k < 2 ^ 61 →
          s'.mem (wd p k) = s.mem (wd p k)) ∧ LFr p s s' ∧
        s'.reg .r12 = (c + 1).toUInt64 ∧ s'.reg .r15 = wd p (16 + 3 * (c + 1)) ∧
        s'.reg .rbp = s.reg .rbp) E) E := by
    intro d hdc hd31 hsl
    have hpos : c - d < 158 := by omega
    have hpw : 2 ^ kapF lm lb hs c ≤ 2 ^ 36 := Nat.pow_le_pow_right (by omega) k1
    have hprod : (c - d) * 2 ^ kapF lm lb hs c ≤ 158 * 2 ^ 36 := Nat.mul_le_mul (by omega) hpw
    have hidx : sumF (kapF lm lb hs) (keyF (kapF lm lb hs) 4) + (c - d) * 2 ^ kapF lm lb hs c
        < 2 ^ 64 := by
      have : 158 * 2 ^ 36 < 2 ^ 63 := by norm_num
      have : 2 ^ 44 < 2 ^ 63 := by norm_num
      omega
    unfold slotP
    fstep; fstep; fstep; fstep; fstep
    rw [rax3, r3 .r12 (by decide) (by decide) (by decide), hr12,
      r3 .rbp (by decide) (by decide) (by decide), int64_ofNat_u (by omega),
      toUInt64_sub (by omega) hdc, shl_u (by omega)]
    have r15 : s₃.reg .r15 = wd p (16 + 3 * c) := by
      rw [r3 _ (by decide) (by decide) (by decide), hr15]
    refine wp_storei (by rw [eval_P (by rsimp; exact r15) 0, Nat.add_zero])
      (by rsimp; rw [hm3]; exact hd _ (by omega)) ?_
    refine wp_store (eval_P (by rsimp; exact r15) 1) (NativeVm.Field.isSome_setMem
      (by rsimp; rw [hm3]; exact hd _ (by omega)) _ _) ?_
    refine wp_store (eval_P (by rsimp; exact r15) 2) (NativeVm.Field.isSome_setMem
      (NativeVm.Field.isSome_setMem (by rsimp; rw [hm3]; exact hd _ (by omega)) _ _) _ _) ?_
    refine WP.blk_nil (fin _ ?_ (fun k hk hk' ↦ ?_) ?_ ?_ ?_ ?_)
    · rw [plF_slot hsl]
      refine ⟨by mem_simp, ⟨by dsimp only; omega, ?_⟩, ⟨by dsimp only; omega, ?_⟩⟩
      · rw [wd_wd]; mem_simp; rw [rax3]
      · rw [wd_wd]; mem_simp
        rw [hrbp, toUInt64_add]
        exact congrArg (fun n : Nat ↦ some n.toUInt64) (by rw [Nat.mul_comm, Nat.add_comm])
    · mem_simp; rw [hm3]
    · refine LFr.setMem ?_ hd (by omega) _
      refine LFr.setMem ?_ hd (by omega) _
      refine LFr.setMem ?_ hd (by omega) _
      fr_tac hd
    · rsimp; rw [r3 _ (by decide) (by decide) (by decide), hr12]
    · rsimp; exact r15
    · rsimp; exact r3 _ (by decide) (by decide) (by decide)
  have h12 : s₃.reg .r12 = c.toUInt64 := by rw [r3 _ (by decide) (by decide) (by decide), hr12]
  refine wp_ite_of (cmp_ltu_imm 80 (by omega) (by omega) h12) (fun h80 ↦ ?_) (fun h80 ↦ ?_)
  · simp only [decide_eq_true_eq] at h80
    obtain ⟨hsl, h16⟩ := slot_lo c hc hb h80
    exact slot 16 h16 (by omega) hsl
  simp only [decide_eq_false_iff_not, not_lt] at h80
  refine wp_ite_of (cmp_ltu_imm 106 (by omega) (by omega) h12) (fun h106 ↦ ?_) (fun h106 ↦ ?_)
  · simp only [decide_eq_true_eq] at h106
    obtain ⟨hsl, h81⟩ := slot_hi c hc hb h80 h106
    exact slot 81 h81 (by omega) hsl
  simp only [decide_eq_false_iff_not, not_lt] at h106
  obtain ⟨hsl, ho⟩ := out_kind c hc hb h106
  have r15 : s₃.reg .r15 = wd p (16 + 3 * c) := by
    rw [r3 _ (by decide) (by decide) (by decide), hr15]
  refine WP.ins (s' := s₃.setMem (wd p (16 + 3 * c)) (Int64.toUInt64 0))
    (by simp [QInstr.step, eval_P r15 0, hm3, Option.isSome_iff_exists.mp (hd (16 + 3 * c) (by omega))])
    (fin _ ?_ (fun k hk hk' ↦ ?_) ?_ ?_ ?_ ?_)
  · rw [plF_out hsl ho]
    show (s₃.setMem (wd p (16 + 3 * c)) 0).mem (wd p (16 + 3 * c)) = some 0
    mem_simp
  · mem_simp; rw [hm3]
  · exact F3.setMem hd (by omega) _
  · rsimp; exact h12
  · rsimp; exact r15
  · rsimp; exact r3 _ (by decide) (by decide) (by decide)

/-! ## Every column -/

theorem placeLoop_spec {p : UInt64} {lm lb : Nat} {hs : Array Nat} (hr14 : s.reg .r14 = p)
    (hd : LDom p s.mem) (hm : KapMem s.mem p lm lb hs)
    (hrbp : s.reg .rbp = (sumF (kapF lm lb hs) (keyF (kapF lm lb hs) 4)).toUInt64) :
    WP placeLoop s (fun s' ↦ (∀ c < 158, PlacementAt s'.mem (wd p (16 + 3 * c)) (plF (kapF lm lb hs) c)) ∧
      (∀ k < 16, s'.mem (wd p k) = s.mem (wd p k)) ∧ LFr p s s') E := by
  unfold placeLoop
  fstep
  refine NativeVm.Transcript.wp_reg (s' := (s.setReg .r12 0).setReg .r15 (wd p 16)) (by
    simp [QInstr.step, eval_L (s := s.setReg .r12 0) (by rsimp; exact hr14) 16]) ?_
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ c ≤ 158, t.reg .r12 = c.toUInt64 ∧ t.reg .r15 = wd p (16 + 3 * c) ∧
      t.reg .rbp = s.reg .rbp ∧ LFr p s t ∧ (∀ k < 16, t.mem (wd p k) = s.mem (wd p k)) ∧
      ∀ c' < c, PlacementAt t.mem (wd p (16 + 3 * c')) (plF (kapF lm lb hs) c'))
    (fun t ↦ 158 - (t.reg .r12).toNat)
  · exact ⟨0, by omega, by rsimp; rfl, by rsimp, by rsimp, by fr_tac hd, fun k _ ↦ by rsimp,
      fun c' h ↦ absurd h (by omega)⟩
  · intro t ⟨c, hc, h12, h15, hbp, F, hk, hpl⟩ hcond
    have hc' : c < 158 := by
      have := (cmp_ltu_imm 158 (by omega) (by omega) h12).symm.trans hcond
      simpa using this
    have hmt : KapMem t.mem p lm lb hs := by
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hm
      exact ⟨by rw [hk 0 (by omega)]; exact a1, by rw [hk 1 (by omega)]; exact a2,
        fun i hi ↦ by rw [hk _ (by omega)]; exact a3 i hi, a4, a5, a6⟩
    refine WP.mono (placeBody_spec (by rw [F.r14, hr14]) (LDom.of_fr hd F) hmt hc' h12 h15
      (by rw [hbp, hrbp])) (fun t' ⟨g1, g2, g3, g4, g5, g6⟩ ↦ ⟨⟨c + 1, hc', g4, g5, g6.trans hbp,
        F.trans g3, fun k hk' ↦ ?_, fun c' hc'' ↦ ?_⟩, ?_⟩) (fun _ h ↦ h)
    · rw [g2 k (by omega) (by omega)]; exact hk k hk'
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hc'' with hlt | rfl
      · refine (hpl c' hlt).congr fun j hj ↦ ?_
        rw [wd_wd]
        exact g2 _ (by omega) (by omega)
      · exact g1
    · rw [g4, h12, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]; omega
  · intro t ⟨c, hc, h12, h15, hbp, F, hk, hpl⟩ hcond
    have hc' : ¬ c < 158 := by
      have := (cmp_ltu_imm 158 (by omega) (by omega) h12).symm.trans hcond
      simpa using this
    obtain rfl : c = 158 := by omega
    exact WP.blk_nil ⟨hpl, hk, F⟩

end NativeVm.Code.Phase1
