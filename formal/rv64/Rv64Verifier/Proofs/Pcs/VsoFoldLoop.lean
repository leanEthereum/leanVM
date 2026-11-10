import Rv64Verifier.Proofs.Pcs.VsoFoldRound
import Rv64Verifier.Proofs.Pcs.VsoFoldEnter

/-!
# `verify_stacked_opening`'s level loop: the fold rounds, whole

`0x8000a2e4` loops back to `0x8000a1e8` until the level's fold count is reached; `0x8000a2f4`
reloads the level's registers and goes on at `0x8000a304` (`Folded`), the mirror after its
`TM.loopN foldRoundRust`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000a304`, the level's fold rounds done: `lf` drawn, the quadratic `q`. -/
structure Folded (s : MachineState) (x : LCtx) (h u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q : List E) : Prop
    extends RB s x h u ℓ Wl (Wl.folds ++ lf) lf q where
  pc : u.pc = 0x8000a304
  x1 : u.getReg .x1 = BitVec.ofNat 64 (K0 s + 1)
  x5 : u.getReg .x5 = BitVec.ofNat 64 ℓ
  x6 : u.getReg .x6 = BitVec.ofNat 64 (Wl.folds ++ lf).length
  x17 : u.getReg .x17 = 8
  lfl : lf.length = fcOf s ℓ
  value : Runs s u ℓ (AFk s x ℓ (Model.Pcs.foldSt Wl lf q))

/-- The frame below the round's slots is the head's. -/
theorem FW.keepLow {s : MachineState} {x : LCtx} {h u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {fl lfs q : List E} (hpre : VsoPre s)
    (hr : RB s x h u ℓ Wl fl lfs q) {y : Word}
    (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 856).toNat) :
    u.getMem y = h.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hf := hr.head.facts
  have hhi := hr.heap.hi
  refine hr.fr y fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb]
  · addr_omega [hw, hi, hy, hb, hnx]
  · addr_omega [hw.2, hi, hy, hb, hhi]
  · simp only [W] at hw; addr_omega [hw, hi, hy, hb, hIs, hS]
  · rcases hf.F with h0 | h0
    · simp only [Within] at hw; omega
    · addr_omega [hw, hi, hy, hb, h0.2, hf.hend]

theorem roundEnd {s : MachineState} {x : LCtx} {h u : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {n : ℕ} {lf q : List E} (hpre : VsoPre s)
    (hd : Rd s x h u ℓ Wl n lf q) :
    ∃ v, Reaches Image.code u v ∧ ((n + 1 < fcOf s ℓ ∧ Rnd s x h v ℓ Wl (n + 1) lf q) ∨
      Folded s x h v ℓ Wl lf q) := by
  have hb := bounds hpre
  have hsp := hd.sp
  have hfc6 : fcOf s ℓ ≤ 6 := by rw [fcOf_eq s hd.head.lvl]; split <;> omega
  have hjlt := hd.jlt
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a2e4_spec hd.pc (by
    rv_eval [hsp]; valid_access hpre.stack.valid [hb])
  have k₁ := b8000a2e4_keeps h₁
  have hm₁ := b8000a2e4_mem_same h₁
  have inv := FW.inv hpre hd.head hd.fr hd.heap hd.mono (hsp.trans hd.head.sp.symm)
  have hRB₁ := RB.carry hpre hd.toRB (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (fun _ h ↦ h.elim) ⟨by simp only [heapNext, hm₁]; exact hd.heap.lo,
      by simp only [heapNext, hm₁]; exact hd.heap.hi⟩ (by simp only [heapNext, hm₁]; exact Nat.le_refl _)
    (fun r hr' ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₁ _ (by decide))
  have v₁ := hd.value.keepStk hpre inv (DFrame.of_same hm₁ (fun _ ↦ False)) fun _ h ↦ h.elim
  have h256 : u.getMem (u.getReg .x2 + 256) = BitVec.ofNat 64 (fcOf s ℓ) := by
    rw [hsp, ← hd.m256]; rv_eval []
  have hlp : vecPtr t₁ (s.getReg .x2 - 640) = vecPtr u (s.getReg .x2 - 640) := hm₁ _
  by_cases he : n + 1 = fcOf s ℓ
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a2f4_spec
      (b8000a2e4_pc_not_taken h₁ (by rw [h256, hd.x21, he])) (by
        rv_eval [(k₁ .x2 (by decide)).trans hsp]
        and_intros <;> valid_access hpre.stack.valid [hb])
    have k₂ := b8000a2f4_keeps h₂
    have hm₂ := b8000a2f4_mem_same h₂
    have inv₁ := FW.inv hpre hd.head hRB₁.fr hRB₁.heap hRB₁.mono (hRB₁.sp.trans hd.head.sp.symm)
    have hRB₂ := RB.carry hpre hRB₁ (DFrame.of_same hm₂ (fun _ ↦ False)) (fun _ h ↦ h.elim)
      (fun _ h ↦ h.elim) ⟨by simp only [heapNext, hm₂]; exact hRB₁.heap.lo,
        by simp only [heapNext, hm₂]; exact hRB₁.heap.hi⟩
      (by simp only [heapNext, hm₂]; exact Nat.le_refl _)
      (fun r hr' ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₂ _ (by decide))
    have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := hRB₁.sp
    have hFl : (vecLen t₁ (s.getReg .x2 - 688)).toNat = (Wl.folds ++ lf).length := by
      have := congrArg List.length hRB₁.F.2.1
      rw [vecEs, eListAt_length] at this; exact this
    refine ⟨t₂, hr₁.trans hr₂, Or.inr {
      toRB := hRB₂
      pc := b8000a2f4_pc h₂
      x1 := by
        rw [b8000a2f4_x1 h₂, sp₁, ← hd.head.m152]
        rw [show s.getReg .x2 - BitVec.ofNat 64 1040 + 152 = s.getReg .x2 - 888 by addr_omega [hb]]
        exact FW.keepLow hpre hRB₁ (by addr_omega [hb])
      x5 := by
        rw [b8000a2f4_x5 h₂, sp₁, ← hRB₁.m184]; congr 1; addr_omega [hb]
      x6 := by
        rw [b8000a2f4_x6 h₂, sp₁, ← hFl, ofNat_toNat']; simp only [vecLen]; congr 1
        addr_omega [hb]
      x17 := b8000a2f4_x17 h₂
      lfl := by rw [hd.lfl, he]
      value := by
        have v₂ := v₁.keepStk hpre inv₁ (DFrame.of_same hm₂ (fun _ ↦ False)) fun _ h ↦ h.elim
        rw [← he, Nat.sub_self] at v₂
        simpa only [Model.Pcs.TM.loopN, pure_bind] using v₂ }⟩
  · refine ⟨t₁, hr₁, Or.inl ⟨by omega, {
      toRB := hRB₁
      pc := b8000a2e4_pc_taken h₁ (by
        rw [h256, hd.x21]; intro h0; exact he (by addr_omega [h0, hfc6, hjlt]))
      x6 := by rw [b8000a2e4_x6 h₁, hd.x24]
      x19 := by rw [k₁ .x19 (by decide), hd.x19, hlp]
      x20 := by rw [b8000a2e4_x20 h₁, hd.x20]; addr_omega [hfc6, hjlt]
      x21 := by rw [k₁ .x21 (by decide), hd.x21]
      jlt := by omega
      lfl := hd.lfl
      value := v₁ }⟩⟩

/-- **The fold rounds**, from round `j` on. -/
theorem foldLoop (hD : DuplexSpec) (hG : GrowOneFreshSpec 0x80011c78 24 8) (hPE : PolyEvalSpec)
    (hRP : RoundPolyErrSpec) {s : MachineState} {x : LCtx} {h : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} (hpre : VsoPre s) :
    ∀ (k j : ℕ) (lf q : List E) (u : MachineState), fcOf s ℓ - j = k →
      Rnd s x h u ℓ Wl j lf q →
      ∃ v, Reaches Image.code u v ∧ (FailR s v ∨ ∃ lf' q', Folded s x h v ℓ Wl lf' q')
  | 0, j, _, _, _, hk, hr => absurd hr.jlt (by omega)
  | k + 1, j, lf, q, u, hk, hr => by
    obtain ⟨t₁, hr₁, hv₁⟩ := rnd_sample hD hpre hr
    rcases hv₁ with hd | ⟨c, hs₁⟩
    · exact ⟨t₁, hr₁, Or.inl (Or.inl hd)⟩
    obtain ⟨t₂, hr₂, hv₂⟩ : ∃ t₂, Reaches Image.code t₁ t₂ ∧ (Dead Image.code t₂ ∨
        (Smp s x h t₂ ℓ Wl j lf q c ∧ t₂.pc = 0x8000a228 ∧
          Wl.folds.length + j < (vecCap t₂ (s.getReg .x2 - 688)).toNat)) := by
      rcases hs₁.pc with ⟨hp, hlt⟩ | ⟨hp, heq⟩
      · exact ⟨t₁, Reaches.refl _, Or.inr ⟨hs₁, hp, hlt⟩⟩
      · obtain ⟨t₂, hr₂, hv₂⟩ := growF hG hpre hs₁ hp heq
        rcases hv₂ with hd | ⟨hs₂, hp₂⟩
        · exact ⟨t₂, hr₂, Or.inl hd⟩
        · rcases hs₂.pc with ⟨_, hlt⟩ | ⟨hp', _⟩
          · exact ⟨t₂, hr₂, Or.inr ⟨hs₂, hp₂, hlt⟩⟩
          · rw [hp₂] at hp'; exact absurd hp' (by decide)
    rcases hv₂ with hd | ⟨hs₂, hp₂, hlt₂⟩
    · exact ⟨t₂, hr₁.trans hr₂, Or.inl (Or.inl hd)⟩
    obtain ⟨t₃, hr₃, hs₃⟩ := pushF hpre hs₂ hp₂ hlt₂
    obtain ⟨t₄, hr₄, hv₄⟩ : ∃ t₄, Reaches Image.code t₃ t₄ ∧ (Dead Image.code t₄ ∨
        (PF s x h t₄ ℓ Wl j lf q c ∧ t₄.pc = 0x8000a270 ∧
          j < (vecCap t₄ (s.getReg .x2 - 640)).toNat)) := by
      rcases hs₃.pc with ⟨hp, hlt⟩ | ⟨hp, heq⟩
      · exact ⟨t₃, Reaches.refl _, Or.inr ⟨hs₃, hp, hlt⟩⟩
      · obtain ⟨t₄, hr₄, hv₄⟩ := growLF hG hpre hs₃ hp heq
        rcases hv₄ with hd | ⟨hs₄, hp₄⟩
        · exact ⟨t₄, hr₄, Or.inl hd⟩
        · rcases hs₄.pc with ⟨_, hlt⟩ | ⟨hp', _⟩
          · exact ⟨t₄, hr₄, Or.inr ⟨hs₄, hp₄, hlt⟩⟩
          · rw [hp₄] at hp'; exact absurd hp' (by decide)
    rcases hv₄ with hd | ⟨hs₄, hp₄, hlt₄⟩
    · exact ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl (Or.inl hd)⟩
    obtain ⟨t₅, hr₅, hv₅⟩ := pushLF hPE hpre hs₄ hp₄ hlt₄
    rcases hv₅ with hd | hs₅
    · exact ⟨t₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl (Or.inl hd)⟩
    obtain ⟨t₆, hr₆, hv₆⟩ := roundStep hRP hpre hs₅
    have hr₁₆ := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))
    rcases hv₆ with hf | ⟨q', hd₆⟩
    · exact ⟨t₆, hr₁₆, Or.inl hf⟩
    obtain ⟨t₇, hr₇, hv₇⟩ := roundEnd hpre hd₆
    rcases hv₇ with ⟨-, hn⟩ | hfo
    · obtain ⟨v, hrv, hvv⟩ := foldLoop hD hG hPE hRP hpre k (j + 1) _ _ t₇ (by omega) hn
      exact ⟨v, hr₁₆.trans (hr₇.trans hrv), hvv⟩
    · exact ⟨t₇, hr₁₆.trans hr₇, Or.inr ⟨_, _, hfo⟩⟩

/-- **A level's fold rounds**: from its head to `0x8000a304`, or an `Err`, or a dead end. -/
theorem foldRounds (hD : DuplexSpec) (hG : GrowOneFreshSpec 0x80011c78 24 8)
    (hPE : PolyEvalSpec) (hRP : RoundPolyErrSpec) {s : MachineState} {x : LCtx}
    {h : MachineState} {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} (hpre : VsoPre s)
    (hh : Head s x h ℓ Wl) :
    ∃ v, Reaches Image.code h v ∧ (FailR s v ∨ ∃ lf q, Folded s x h v ℓ Wl lf q) := by
  obtain ⟨u, hr, hu⟩ := enter hpre hh
  obtain ⟨v, hrv, hv⟩ := foldLoop hD hG hPE hRP hpre _ 0 [] _ u rfl hu
  exact ⟨v, hr.trans hrv, hv⟩

end Rv64Verifier.Proofs.Pcs.Vso
