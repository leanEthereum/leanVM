import Rv64Verifier.Proofs.Pcs.VsoRowsD4

/-!
# `verify_stacked_opening`'s level loop: a deeper level's rows, the loop

From `0x8000b158`: `try_allocate_in(S - 384, n, 0, 8, 24)` for the rows' values, the trap on `Err`,
the rows' `Vec` at `S - 464` and `reserve` with room (`0x8000b17c`), then at `0x8000b1a0` no rows
(`0x8000b428`, to `Rowed`) or the loop's setup (`0x8000b1ac`, to `DeepAt` at row `0`):
`rowsEntry`. `rowStep` is one row, `rowLoop` all of them, `rowsDeepOf` the whole of `RowsDeep`
from the callees' contracts.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso.RowsD
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- **One row**, from the loop's head. -/
theorem rowStep (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x80008a10)
    (hDt : MultilinearContracts.DotSpec) {s t' k u : MachineState} {lf : List E}
    {ws : List (List K)} {O : Word} {j : ℕ} (C : DCtx s t' k lf ws)
    (hu : DeepAt s k u ws (Model.eqKernelRust lf) O j) (hj : j < ws.length) :
    ∃ r, Reaches Image.code u r ∧ (FailR s r ∨
      (j + 1 < ws.length ∧ DeepAt s k r ws (Model.eqKernelRust lf) O (j + 1)) ∨
      (j + 1 = ws.length ∧ Rowed s k r (ws.map (rowF (Model.eqKernelRust lf))))) := by
  obtain ⟨v, r₁, hd | ⟨B, hv⟩⟩ := rowAlloc hT hRF C hu hj
  · exact ⟨v, r₁, Or.inl (Or.inl hd)⟩
  obtain ⟨w, r₂, hw⟩ := rowCopy C hu hj hv
  obtain ⟨r, r₃, h⟩ := rowFinish hDt C hu hj hw
  exact ⟨r, r₁.trans (r₂.trans r₃), h⟩

/-- **The rows from row `j` on.** -/
theorem rowLoop (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x80008a10)
    (hDt : MultilinearContracts.DotSpec) {s t' k : MachineState} {lf : List E}
    {ws : List (List K)} {O : Word} (C : DCtx s t' k lf ws) :
    ∀ c j (u : MachineState), j + c = ws.length → j < ws.length →
      DeepAt s k u ws (Model.eqKernelRust lf) O j →
      ∃ r, Reaches Image.code u r ∧
        (FailR s r ∨ Rowed s k r (ws.map (rowF (Model.eqKernelRust lf)))) := by
  intro c
  induction c with
  | zero => intro j u h1 h2; omega
  | succ c ih =>
    intro j u hjc hj hu
    obtain ⟨r, r₁, hf | ⟨hlt, hr⟩ | ⟨-, hr⟩⟩ := rowStep hT hRF hDt C hu hj
    · exact ⟨r, r₁, Or.inl hf⟩
    · obtain ⟨r', r₂, h⟩ := ih (j + 1) r (by omega) hlt hr
      exact ⟨r', r₁.trans r₂, h⟩
    · exact ⟨r, r₁, Or.inr hr⟩

/-- **The rows' buffer and the loop's setup**, from `0x8000b158`. -/
theorem rowsEntry (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x80008a10)
    {s t' k k' : MachineState} {lf : List E} {ws : List (List K)} (C : DCtx s t' k lf ws)
    (hpc : k'.pc = 0x8000b158) (hmem : ∀ a, k'.getMem a = k.getMem a)
    (hregs : ∀ q ∈ calleeSaved, k'.getReg q = k.getReg q) :
    ∃ u, Reaches Image.code k' u ∧ (FailR s u ∨
      (ws.length = 0 ∧ Rowed s k u (ws.map (rowF (Model.eqKernelRust lf)))) ∨
      (0 < ws.length ∧ ∃ O, DeepAt s k u ws (Model.eqKernelRust lf) O 0)) := by
  have hpre := C.pre
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hk := C.ker
  have hn := C.leaves.n
  have hkh := hk.heap
  have hkhi := hkh.hi
  have hsp0 : k'.getReg .x2 = s.getReg .x2 - 1040 := (hregs .x2 (by decide)).trans hk.sp
  have inv0 : InvR s k' (k.getMem nextAddr) := Inv.same' hk.inv hmem (hregs .x2 (by decide))
  -- `0x8000b158`: `try_allocate_in(S - 384, n, 0, 8, 24)`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b158_spec hpc trivial
  have k₁ := b8000b158_keeps h₁
  have m₁ := b8000b158_mem_same h₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := (k₁ .x2 (by decide)).trans hsp0
  have hn₁ : heapNext t₁ = heapNext k := by simp only [heapNext, m₁, hmem]
  have x11₁ : t₁.getReg .x11 = k.getReg .x20 := by rw [b8000b158_x11 h₁, hregs .x20 (by decide)]
  obtain ⟨t₂, r₂, hv₂⟩ := callTryAlloc24 hT hpre (b8000b158_pc h₁) sp₁
    (by rw [b8000b158_x10 h₁, hsp0]; rv_eval []) (b8000b158_x13 h₁) (b8000b158_x14 h₁)
    ⟨by rw [hn₁]; exact hkh.lo, by rw [hn₁]; exact hkh.hi⟩
  rcases hv₂ with hd | ⟨pc₂, pr₂, heap₂, mono₂, ok₂, fr₂⟩
  · exact ⟨t₂, r₁.trans r₂, Or.inl (Or.inl hd)⟩
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := (pr₂.reg .x2).trans sp₁
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000b174_spec
    (by rw [pc₂, returnAddress_eq, b8000b158_x1 h₁]; rfl) (by
      rv_eval [sp₂]; valid_access hst.valid [hb])
  have q656 : t₂.getMem (t₂.getReg .x2 + 656) = t₂.getMem (s.getReg .x2 - 384) := by
    rw [sp₂]; rv_eval []
  by_cases htag : t₂.getMem (s.getReg .x2 - 384) = 0
  swap
  · have hpc₃ := b8000b174_pc_taken h₃ (by rw [q656]; exact htag)
    exact ⟨t₃, r₁.trans (r₂.trans r₃),
      Or.inl (Or.inl (dead_of_fetch (by rw [hpc₃]; exact Vso.trap)))⟩
  have hpc₃ := b8000b174_pc_not_taken h₃ (by rw [q656]; exact htag)
  obtain ⟨hcap, hnew⟩ := ok₂ htag
  rw [x11₁] at hcap hnew
  have k₃ := b8000b174_keeps h₃
  have m₃ := b8000b174_mem_same h₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := (k₃ .x2 (by decide)).trans sp₂
  -- `0x8000b17c`: the rows' `Vec` at `S - 464`, `reserve` with room
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000b17c_spec hpc₃ (by
    rv_eval [sp₃]; and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000b17c_keeps h₄
  have fr₄ := DFrame.of_memFrame (b8000b17c_frame h₄ (by rw [sp₃]; addr_omega [hb]))
  rw [sp₃, show s.getReg .x2 - 1040 + 576 = s.getReg .x2 - 464 by rv_eval []] at fr₄
  have v0 := b8000b17c_m_x2_576 h₄
  have v1 := b8000b17c_m_x2_584 h₄
  have v2 := b8000b17c_m_x2_592 h₄
  rw [sp₃] at v0 v1 v2
  rv_eval [m₃] at v0 v1 v2
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1040 := (k₄ .x2 (by decide)).trans sp₃
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 464 := by rw [b8000b17c_x10 h₄, sp₃]; rv_eval []
  have x11₄ : t₄.getReg .x11 = k.getReg .x20 := by
    rw [b8000b17c_x11 h₄, k₃ .x20 (by decide), pr₂.reg .x20, k₁ .x20 (by decide),
      hregs .x20 (by decide)]
  obtain ⟨t₅, r₅, ⟨pc₅, pr₅, -, m₅⟩ | hd⟩ := hRF.call (Reaches.refl t₄) (b8000b17c_pc h₄)
    ⟨by rw [x10₄]; valid_sub hst.valid [hb], by
      rw [x10₄, x11₄]
      simp only [vecLen, vecCap]
      rw [show s.getReg .x2 - 464 + 16 = s.getReg .x2 - 448 by rv_eval [], v2, v0, hcap]
      exact Nat.le_of_eq (by rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_add])⟩
  swap
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl (Or.inl hd)⟩
  -- `0x8000b1a0`
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 1040 := (pr₅.reg .x2).trans sp₄
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b8000b1a0_spec
    (by rw [pc₅, returnAddress_eq, b8000b17c_x1 h₄]; rfl) (by
      rv_eval [sp₅]; and_intros <;> valid_access hst.valid [hb])
  have k₆ := b8000b1a0_keeps h₆
  have m₆ := b8000b1a0_mem_same h₆
  have sp₆ : t₆.getReg .x2 = s.getReg .x2 - 1040 := (k₆ .x2 (by decide)).trans sp₅
  have x10₆ : t₆.getReg .x10 = t₂.getMem (s.getReg .x2 - 368) := by
    rw [b8000b1a0_x10 h₆, sp₅, show s.getReg .x2 - 1040 + 584 = s.getReg .x2 - 456 by rv_eval [],
      m₅, v1]
  have x27₆ : t₆.getReg .x27 = 0 := by
    rw [b8000b1a0_x27 h₆, sp₅, show s.getReg .x2 - 1040 + 592 = s.getReg .x2 - 448 by rv_eval [],
      m₅, v2]
  have r₆k (q : Reg) (hq : q ∈ [Reg.x9, .x20, .x23, .x26]) : t₆.getReg q = k.getReg q := by
    have hq' := hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl <;>
      rw [k₆ _ (by decide), pr₅.reg _, k₄ _ (by decide), k₃ _ (by decide), pr₂.reg _,
        k₁ _ (by decide), hregs _ (by decide)]
  -- the frame from `k`
  have nx₄ : t₄.getMem nextAddr = t₂.getMem nextAddr := by
    rw [fr₄ _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx], m₃]
  have hn₆ : heapNext t₆ = heapNext t₂ := by simp only [heapNext, m₆, m₅, nx₄]
  have hk6 : heapNext k ≤ heapNext t₆ := by rw [hn₆, ← hn₁]; exact mono₂
  have F₆ : DFrame k t₆ (RowW s k t₆) := by
    have d1 : DFrame k t₂ (RowW s k t₆) :=
      ((DFrame.of_same hmem _).trans (DFrame.of_same m₁ _) fun _ h ↦ h).trans fr₂ fun a ha ↦ by
        rcases ha with ha | ha | ha | ⟨h1, h2⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨by rw [← hn₁]; exact h1, by rw [hn₆]; exact h2⟩)))))
    exact (((d1.trans (DFrame.of_same m₃ _) fun _ h ↦ h).trans fr₄ fun a ha ↦
      Or.inr (Or.inr (Or.inl ha))).trans (DFrame.of_same m₅ _) fun _ h ↦ h).trans
        (DFrame.of_same m₆ _) fun _ h ↦ h
  have hheap₆ : HeapOk t₆ := ⟨by rw [hn₆]; exact heap₂.lo, by rw [hn₆]; exact heap₂.hi⟩
  have kS (o : ℕ) (ho : o = 832 ∨ o = 880 ∨ o = 528 ∨ o = 520) :=
    keepSlot hpre F₆ hheap₆ o ho
  have hx20 : (k.getReg .x20).toNat = ws.length := hn
  have hO := hnew.1
  have hlen := (k.getReg .x20).isLt
  by_cases hz : ws.length = 0
  · -- no rows: `0x8000b428`
    have hpc₆ := b8000b1a0_pc_taken h₆ (by
      rw [← k₆ .x20 (by decide), r₆k .x20 (by simp)]; apply BitVec.eq_of_toNat_eq; rw [hx20, hz]; rfl)
    obtain ⟨t₇, r₇, h₇⟩ := Sym.BlockSpec.reaches b8000b428_spec hpc₆ trivial
    have k₇ := b8000b428_keeps h₇
    have m₇ := b8000b428_mem_same h₇
    have hn₇ : heapNext t₇ = heapNext t₆ := by simp only [heapNext, m₇]
    have F₇ : DFrame k t₇ (RowW s k t₇) :=
      (F₆.mono fun _ ha ↦ rowW_mono (le_of_eq hn₇.symm) ha).trans (DFrame.of_same m₇ _)
        fun _ h ↦ h
    refine ⟨t₇, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans r₇))))),
      Or.inr (Or.inl ⟨hz, {
        pc := b8000b428_pc h₇
        sp := (k₇ .x2 (by decide)).trans sp₆
        regs := fun q hq ↦ by
          have hq' := hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
          rcases hq' with rfl | rfl | rfl <;> exact (k₇ _ (by decide)).trans (r₆k _ (by simp))
        inv := rowW_inv hpre hk.inv inv0 (fun a ha ↦ (F₇ a ha).trans (hmem a).symm)
          (by have := hk6; rw [← hn₇] at this; exact this)
          (by have := hheap₆.hi; rw [← hn₇] at this; exact this)
          ((k₇ .x2 (by decide)).trans (sp₆.trans hsp0.symm))
        heap := ⟨by rw [hn₇]; exact hheap₆.lo, by rw [hn₇]; exact hheap₆.hi⟩
        mono := by rw [hn₇]; exact hk6
        value := by
          rw [k₇ .x27 (by decide), x27₆, List.length_eq_zero_iff.mp hz]; rfl
        buf := by
          rw [b8000b428_x25 h₇, x10₆, k₇ .x27 (by decide), x27₆]
          exact ⟨hO, Or.inl rfl⟩
        fr := F₇ }⟩)⟩
  -- the loop's setup: `0x8000b1ac`
  have hpc₆ := b8000b1a0_pc_not_taken h₆ (by
    rw [← k₆ .x20 (by decide), r₆k .x20 (by simp)]; intro he
    have := congrArg BitVec.toNat he; rw [hx20] at this; exact hz this)
  obtain ⟨t₇, r₇, h₇⟩ := Sym.BlockSpec.reaches b8000b1ac_spec hpc₆ (by
    rv_eval [sp₆]; and_intros <;> valid_access hst.valid [hb])
  have k₇ := b8000b1ac_keeps h₇
  have f₇ := DFrame.of_memFrame (b8000b1ac_frame h₇ (by rw [sp₆]; addr_omega [hb]))
  rw [sp₆, show s.getReg .x2 - 1040 + 256 = s.getReg .x2 - 784 by rv_eval []] at f₇
  have w784 := b8000b1ac_m_x2_256 h₇
  rw [sp₆, show s.getReg .x2 - 1040 + 256 = s.getReg .x2 - 784 by rv_eval [],
    show s.getReg .x2 - 1040 + 512 = s.getReg .x2 - 528 by rv_eval []] at w784
  have nx₇ : t₇.getMem nextAddr = t₆.getMem nextAddr :=
    f₇ _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx]
  have hn₇ : heapNext t₇ = heapNext t₆ := by simp only [heapNext, nx₇]
  have F₇ : DFrame k t₇ (RowW s k t₇) :=
    (F₆.mono fun _ ha ↦ rowW_mono (le_of_eq hn₇.symm) ha).trans f₇ fun a ha ↦
      Or.inr (Or.inl ha)
  have e528 : t₆.getMem (s.getReg .x2 - 528) = vecPtr k (s.getReg .x2 - 536) := by
    rw [show s.getReg .x2 - 528 = s.getReg .x2 - BitVec.ofNat 64 528 from rfl, kS 528 (by simp)]
    simp only [vecPtr]; congr 1; rv_eval []
  have e520 : t₆.getMem (s.getReg .x2 - 520) = vecLen k (s.getReg .x2 - 536) := by
    rw [show s.getReg .x2 - 520 = s.getReg .x2 - BitVec.ofNat 64 520 from rfl, kS 520 (by simp)]
    simp only [vecLen]; congr 1; rv_eval []
  have e832 : t₆.getMem (s.getReg .x2 - 832) = k.getMem (s.getReg .x2 - 832) :=
    kS 832 (by simp)
  obtain ⟨hO1, hO2⟩ : heapNext t₁ ≤ (t₂.getMem (s.getReg .x2 - 368)).toNat ∧
      (t₂.getMem (s.getReg .x2 - 368)).toNat + (k.getReg .x20).toNat * 24 ≤ heapNext t₂ := by
    rcases hnew.2 with h0 | h0
    · exfalso; apply hz; rw [← hx20]; omega
    · exact h0
  refine ⟨t₇, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans r₇))))),
    Or.inr (Or.inr ⟨by omega, t₂.getMem (s.getReg .x2 - 368), {
      pc := b8000b1ac_pc h₇
      sp := (k₇ .x2 (by decide)).trans sp₆
      x18 := b8000b1ac_x18 h₇
      x27 := by rw [k₇ .x27 (by decide), x27₆]; rfl
      x20 := (k₇ .x20 (by decide)).trans (r₆k .x20 (by simp))
      x21 := by
        rw [b8000b1ac_x21 h₇, sp₆, show s.getReg .x2 - 1040 + 520 = s.getReg .x2 - 520 by
          rv_eval [], e520]
      x24 := by
        rw [b8000b1ac_x24 h₇, sp₆, show s.getReg .x2 - 1040 + 208 = s.getReg .x2 - 832 by
          rv_eval [], e832]
      x25 := by rw [b8000b1ac_x25 h₇, x10₆]
      regs := fun q hq ↦ by
        have hq' := hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
        rcases hq' with rfl | rfl | rfl <;> exact (k₇ _ (by decide)).trans (r₆k _ (by simp))
      m784 := by rw [w784, e528]
      inv := rowW_inv hpre hk.inv inv0 (fun a ha ↦ (F₇ a ha).trans (hmem a).symm)
        (by have := hk6; rw [← hn₇] at this; exact this)
        (by have := hheap₆.hi; rw [← hn₇] at this; exact this)
        ((k₇ .x2 (by decide)).trans (sp₆.trans hsp0.symm))
      heap := ⟨by rw [hn₇]; exact hheap₆.lo, by rw [hn₇]; exact hheap₆.hi⟩
      mono := by rw [hn₇]; exact hk6
      buf := ⟨hO, by rw [← hn₁]; exact hO1, by rw [hn₇, hn₆]; rw [hx20] at hO2; omega⟩
      value := rfl
      fr := F₇ }⟩)⟩

/-- **A deeper level's rows**, from the callees' contracts. -/
theorem rowsDeepOf (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x80008a10)
    (hDt : MultilinearContracts.DotSpec) : RowsDeep := by
  intro s t' k k' lf ws ℓ hpre hℓ hk hL h880 hpc hmem hregs
  have C : DCtx s t' k lf ws := ⟨hpre, hk, hL, h880⟩
  have hv : Model.Pcs.rowValuesRust ℓ ws (Model.eqKernelRust lf) =
      ws.map (rowF (Model.eqKernelRust lf)) := by
    simp only [Model.Pcs.rowValuesRust, hℓ, ↓reduceIte]; rfl
  rw [hv]
  obtain ⟨u, r₁, hf | ⟨-, hr⟩ | ⟨hpos, O, hu⟩⟩ := rowsEntry hT hRF C hpc hmem hregs
  · exact ⟨u, r₁, Or.inl hf⟩
  · exact ⟨u, r₁, Or.inr hr⟩
  · obtain ⟨r, r₂, h⟩ := rowLoop hT hRF hDt C ws.length 0 u (by omega) hpos hu
    exact ⟨r, r₁.trans r₂, h⟩

end Rv64Verifier.Proofs.Pcs.Vso.RowsD
