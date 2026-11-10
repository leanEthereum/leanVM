import Rv64Verifier.Proofs.Bus.TsBase

/-!
# `table_sumcheck`: the prologue and the maximum

`0x80008010` saves the registers and spills the arguments (`Args`), keeping `out`, `tables.len()`,
`table_log_heights.len()`, `bus_forms.len()`, `form_powers.len()` and `&target` in saved registers
(`Regs`); the loop at `0x800080a4` leaves `n_rounds` in `a2` at `0x800080b8`.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem region_range {a : Word} {n : Nat} (h : Region a (8 * n)) : ValidMemRange a n :=
  fun i hi ↦ Region.valid h (by addr_omega [h, hi]) (by addr_omega [h, hi]) (by addr_omega [h, hi])

theorem _root_.Rv64Verifier.Bus.RO.range {s : MachineState} {k : Nat} {ws : List (Word × Nat)}
    {p a : Word} {n : Nat}
    (h : RO s k ws p a (8 * n)) : ValidMemRange a n := by
  rcases h.region with h0 | h0
  · intro i hi; omega
  · exact region_range h0

/-- `n_rounds`, the heights' maximum. -/
def nRounds (s : MachineState) : Nat :=
  (natsAt s (s.getReg .x13) (s.getReg .x14).toNat).max?.getD 0

/-- The arguments the prologue spills. -/
structure Args (s u : MachineState) : Prop where
  formPowers : u.getMem (s.getReg .x2 - 432) = s.getReg .x29
  forms : u.getMem (s.getReg .x2 - 424) = s.getReg .x15
  constraintPowers : u.getMem (s.getReg .x2 - 416) = s.getReg .x17
  constraintLen : u.getMem (s.getReg .x2 - 408) = s.getReg .x28
  tables : u.getMem (s.getReg .x2 - 400) = s.getReg .x11
  equalityPoint : u.getMem (s.getReg .x2 - 360) = s.getReg .x31
  heights : u.getMem (s.getReg .x2 - 352) = s.getReg .x13

theorem Args.step {s u v : MachineState} {w : Word → Prop} (h : Args s u) (hf : DFrame u v w)
    (hw : ∀ a, w a → ¬ Within a (s.getReg .x2 - 432) 40 ∧ ¬ Within a (s.getReg .x2 - 360) 16)
    (hb : 0xa0000f38 + 2128 ≤ (s.getReg .x2).toNat) : Args s v where
  formPowers := (hf _ fun i hi hw' ↦ (hw _ hw').1 (by addr_omega [hb, hi])).trans h.formPowers
  forms := (hf _ fun i hi hw' ↦ (hw _ hw').1 (by addr_omega [hb, hi])).trans h.forms
  constraintPowers :=
    (hf _ fun i hi hw' ↦ (hw _ hw').1 (by addr_omega [hb, hi])).trans h.constraintPowers
  constraintLen := (hf _ fun i hi hw' ↦ (hw _ hw').1 (by addr_omega [hb, hi])).trans h.constraintLen
  tables := (hf _ fun i hi hw' ↦ (hw _ hw').1 (by addr_omega [hb, hi])).trans h.tables
  equalityPoint := (hf _ fun i hi hw' ↦ (hw _ hw').2 (by addr_omega [hb, hi])).trans h.equalityPoint
  heights := (hf _ fun i hi hw' ↦ (hw _ hw').2 (by addr_omega [hb, hi])).trans h.heights

/-- The values the function keeps in saved registers. -/
structure Regs (s u : MachineState) : Prop where
  x8 : u.getReg .x8 = s.getReg .x16
  x18 : u.getReg .x18 = s.getReg .x10
  x19 : u.getReg .x19 = s.getReg .x14 * 8
  x22 : u.getReg .x22 = s.getReg .x30
  x23 : u.getReg .x23 = s.getReg .x12
  x26 : u.getReg .x26 = s.getReg .x14
  x27 : u.getReg .x27 = tsTarget s

def regsList : List Reg := [.x8, .x18, .x19, .x22, .x23, .x26, .x27]

theorem Regs.of {s u v : MachineState} (h : Regs s u)
    (hk : ∀ r ∈ regsList, v.getReg r = u.getReg r) : Regs s v where
  x8 := (hk .x8 (by decide)).trans h.x8
  x18 := (hk .x18 (by decide)).trans h.x18
  x19 := (hk .x19 (by decide)).trans h.x19
  x22 := (hk .x22 (by decide)).trans h.x22
  x23 := (hk .x23 (by decide)).trans h.x23
  x26 := (hk .x26 (by decide)).trans h.x26
  x27 := (hk .x27 (by decide)).trans h.x27

theorem Regs.call {s u v : MachineState} (h : Regs s u) (hp : Preserves u v) : Regs s v :=
  h.of fun r hr ↦ hp r (by unfold calleeSaved; exact mem_of_mem hr _)

/-- A step writing only the stack below the saved registers keeps the transcript. -/
theorem transcript_of_stack {s u : MachineState} (hpre : TableSumcheckPre s) {lo : Word} {n : Nat}
    (hf : DFrame s u (Within · lo n)) (hlo : (s.getReg .x2 - 2128).toNat ≤ lo.toNat)
    (hn : lo.toNat + n ≤ (s.getReg .x2).toNat) {T : TState} (hT : TranscriptAt s (tsSelf s) T) :
    TranscriptAt u (tsSelf s) T := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hS := hpre.self.self
  have hP := hpre.self.proof
  have ss := hpre.selfStack
  have ps := hpre.proofStack
  rw [stackLo_eq, stack_eq] at ss ps
  simp only [ProofApart] at ps
  have st (a : Word) (m : Nat) (h : Apart a m (s.getReg .x2 - 2128) 2128) :
      Misses (Within · lo n) a m :=
    fun y hy hw ↦ by addr_omega [hy, hw, h, hlo, hn, hb1]
  exact hf.transcriptAt hT hpre.self (st _ _ (by addr_omega [ss, hS])) (st _ _ ps.1) (st _ _ ps.2)
    (st _ _ (by addr_omega [ss, hS]))

/-- The prologue and the maximum, to `0x800080b8`. -/
theorem stageP {s : MachineState} (hpc : s.pc = 0x80008010) (hpre : TableSumcheckPre s) :
    ∃ u, Reaches Image.code s u ∧ Inv s u ∧ u.pc = 0x800080b8 ∧ Regs s u ∧ Args s u ∧
      (u.getReg .x12).toNat = nRounds s ∧ DFrame s u (Within · (s.getReg .x2 - 432) 432) := by
  obtain ⟨hb1, hb2, hb3, hlo⟩ := bounds hpre
  have hst := hpre.stack
  have hA := hpre.args.region
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hst.valid
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008010_spec hpc (by
    rv_eval []
    and_intros <;> first
      | valid_access hval [hb1]
      | (rcases hA with h0 | h0
         · omega
         · exact Region.valid h0 (by addr_omega [h0]) (by addr_omega [h0]) (by addr_omega [h0])))
  have hm₁ := DFrame.of_memFrame (b80008010_frame h₁ (by omega))
  have k₁ := b80008010_keeps h₁
  have hsp₁ := b80008010_x2 h₁
  have hn₁ : heapNext u₁ = heapNext s := by
    simp only [heapNext]
    have hx := hst.next
    rw [stackLo_eq, stack_eq] at hx
    exact congrArg BitVec.toNat (hm₁ nextAddr fun i hi hw ↦ by addr_omega [hx, hw, hi, hb1])
  have I₁ : Inv s u₁ := {
    sp := hsp₁
    heap := ⟨hn₁ ▸ hpre.heap.lo, hn₁ ▸ hpre.heap.hi⟩
    mono := hn₁.ge
    frame := hm₁.mono fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inl (by
      rw [stackLo_eq, stack_eq]; addr_omega [ha, hb1]))))
    saved := fun i hi ↦ by
      interval_cases i
      exacts [b80008010_m_x2_n8 h₁, b80008010_m_x2_n16 h₁, b80008010_m_x2_n24 h₁,
        b80008010_m_x2_n32 h₁, b80008010_m_x2_n40 h₁, b80008010_m_x2_n48 h₁,
        b80008010_m_x2_n56 h₁, b80008010_m_x2_n64 h₁, b80008010_m_x2_n72 h₁,
        b80008010_m_x2_n80 h₁, b80008010_m_x2_n88 h₁, b80008010_m_x2_n96 h₁,
        b80008010_m_x2_n104 h₁] }
  have A₁ : Args s u₁ := ⟨b80008010_m_x2_n432 h₁, b80008010_m_x2_n424 h₁,
    b80008010_m_x2_n416 h₁, b80008010_m_x2_n408 h₁, b80008010_m_x2_n400 h₁,
    b80008010_m_x2_n360 h₁, b80008010_m_x2_n352 h₁⟩
  have R₁ : Regs s u₁ := ⟨b80008010_x8 h₁, b80008010_x18 h₁, b80008010_x19 h₁, b80008010_x22 h₁,
    b80008010_x23 h₁, b80008010_x26 h₁, b80008010_x27 h₁⟩
  have hx13 : u₁.getReg .x13 = s.getReg .x13 := k₁ .x13 (by decide)
  have hhv := hpre.heights.range (n := (s.getReg .x14).toNat)
  -- what the loop reads is the entry's
  have hH (k : Nat) (hk : k < (s.getReg .x14).toNat) :
      u₁.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * k)) =
        s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * k)) := by
    have hb := ValidMemRange.bounds hhv (by omega)
    exact I₁.word hpre.heights (by addr_omega [hb, hk]) (by addr_omega [hb, hk])
  have hmax (u : MachineState) (hu : ∀ a, u.getMem a = u₁.getMem a) (n : Nat)
      (hn : n = (s.getReg .x14).toNat) : maxOf u (s.getReg .x13) n = nRounds s := by
    rw [maxOf_eq, nRounds, ← hn]
    simp only [natsAt, readWords_eq_map, List.map_map]
    refine congrArg (fun l ↦ List.max? l |>.getD 0) (List.map_congr_left fun k hk ↦ ?_)
    simp only [Function.comp, hu]
    rw [hH k (by simp at hk; omega)]
  have fin (u : MachineState) (hr : Reaches Image.code s u) (hpc : u.pc = 0x800080b8)
      (hu : ∀ a, u.getMem a = u₁.getMem a) (hk : ∀ r ∈ regsList, u.getReg r = u₁.getReg r)
      (hsp : u.getReg .x2 = u₁.getReg .x2) (h12 : (u.getReg .x12).toNat = nRounds s) :
      ∃ u, Reaches Image.code s u ∧ Inv s u ∧ u.pc = 0x800080b8 ∧ Regs s u ∧ Args s u ∧
        (u.getReg .x12).toNat = nRounds s ∧ DFrame s u (Within · (s.getReg .x2 - 432) 432) := by
    have hn : heapNext u = heapNext u₁ := by simp only [heapNext, hu]
    exact ⟨u, hr, I₁.step hpre (DFrame.of_same hu fun _ ↦ False) (fun _ h ↦ h.elim)
      ⟨hn ▸ I₁.heap.lo, hn ▸ I₁.heap.hi⟩ hn.ge hsp,
      hpc, R₁.of hk, A₁.step (DFrame.of_same hu fun _ ↦ False) (fun _ h ↦ h.elim) hb1, h12,
      (hm₁.trans (DFrame.of_same hu fun _ ↦ False) fun _ h ↦ h.elim)⟩
  by_cases hz : s.getReg .x14 = 0
  · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800080b4_spec
      (b80008010_pc_taken h₁ hz) trivial
    refine fin u₂ (hr₁.trans hr₂) (b800080b4_pc h₂) (b800080b4_mem_same h₂)
      (fun r hr ↦ b800080b4_keeps h₂ r (mem_of_mem hr _)) (b800080b4_keeps h₂ .x2 (by decide)) ?_
    rw [b800080b4_x12 h₂, nRounds, hz]; rfl
  have hn0 : 0 < (s.getReg .x14).toNat := by
    rcases Nat.eq_zero_or_pos (s.getReg .x14).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) hz
    · exact h
  have hb := ValidMemRange.bounds hhv hn0
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80008084_spec (b80008010_pc_not_taken h₁ hz) (by
    rv_eval [hx13]; valid_access hhv [hb, hn0])
  have hm₂ := b80008084_mem_same h₂
  have k₂ := b80008084_keeps h₂
  have h12₂ : u₂.getReg .x12 = s.getMem (s.getReg .x13) := by
    rw [b80008084_x12 h₂, hx13]
    simpa using hH 0 hn0
  by_cases h1 : s.getReg .x14 = 1
  · refine fin u₂ (hr₁.trans hr₂) (b80008084_pc_taken h₂ (by rw [R₁.x26, h1])) hm₂
      (fun r hr ↦ k₂ r (mem_of_mem hr _)) (k₂ .x2 (by decide)) ?_
    rw [h12₂, nRounds, ← maxOf_eq, h1, show (1 : Word).toNat = 0 + 1 from rfl, maxOf_succ]
    simp [maxOf]
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008090_spec
    (b80008084_pc_not_taken h₂ (by rw [R₁.x26]; exact h1)) trivial
  have hm₃ := b80008090_mem_same h₃
  have k₃ := b80008090_keeps h₃
  have hn1 : 1 < (s.getReg .x14).toNat := by
    rcases Nat.lt_or_ge 1 (s.getReg .x14).toNat with h | h
    · exact h
    · exact absurd (BitVec.eq_of_toNat_eq (by change _ = 1; omega)) h1
  have hmem₃ (a : Word) : u₃.getMem a = u₁.getMem a := by rw [hm₃, hm₂]
  obtain ⟨t, hr, hpc', h12', hm', hk'⟩ := maxLoop hhv _ 1 u₃ rfl (le_refl _) hn1
    (b80008090_pc h₃) (by rw [b80008090_x10 h₃, k₂ .x13 (by decide), hx13]; rfl)
    (by rw [b80008090_x11 h₃, k₂ .x13 (by decide), k₂ .x19 (by decide), hx13, R₁.x19]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_mul]
        try omega)
    (by have h0 := hH 0 hn0
        simp only [Nat.mul_zero, BitVec.add_zero] at h0
        rw [k₃ .x12 (by decide), h12₂, maxOf]
        simp [hmem₃, h0])
  refine fin t (hr₁.trans (hr₂.trans (hr₃.trans hr))) hpc' (fun a ↦ (hm' a).trans (hmem₃ a))
    (fun r hr ↦ ?_) ?_ (by rw [h12', hmax u₃ hmem₃ _ rfl])
  · have ne : r ≠ .x10 ∧ r ≠ .x12 ∧ r ≠ .x13 := by
      simp only [regsList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hk' r ne.1 ne.2.1 ne.2.2,
      k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _)]
  · rw [hk' .x2 (by decide) (by decide) (by decide), k₃ .x2 (by decide), k₂ .x2 (by decide)]

end Rv64Verifier.Proofs.Bus.TableSumcheck
