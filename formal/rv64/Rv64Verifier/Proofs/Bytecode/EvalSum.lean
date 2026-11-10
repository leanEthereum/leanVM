import Rv64Verifier.Proofs.Bytecode.EvalWord

/-!
# `Bytecode::evaluate`: a word's positions, summed

`E::sum(members.iter().map(|&position| low_weights[position as usize]))`: `lhu` loads a position
(`0x80011114`), traps unless it indexes the low eq table, and `0x8001111c` adds its weight, limb by
limb, into `a6`, `a5`, `a4` (`sum_body`). `sum_loop` runs it to the end of the word's positions.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

variable {e : Env}

/-- The low eq table, mapped. -/
theorem EnvOk.lowMapped (he : EnvOk e) : Mapped e.low (24 * 2 ^ e.m) := by
  have h1 := he.lowIn
  have h2 := he.pre.heap.lo
  have h3 := he.heapL.hi
  simp only [heapNext, heapStart, heapEnd] at h1 h2 h3
  simp only [Mapped]
  omega

theorem fetch_11114 : Image.code.fetch 0x80011114 = some (.base (.LHU .x7 .x5 0)) :=
  fetch_of (by decide +kernel)

set_option maxHeartbeats 2000000 in
/-- One position: its weight added, then the next position or the sum's end. -/
theorem sum_body (he : EnvOk e) {t : MachineState} {i j p : Nat} (hs : SInv e t i j p)
    (hpc : t.pc = 0x80011114) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x80011150 ∧ AInv e u i j) ∨
      (u.pc = 0x80011114 ∧ SInv e u i j (p + 1))) := by
  have hpc' := he.pre.bcClear.positions
  have hpm := he.pre.bc.positions
  have hpa := he.pre.bc.positionsAlign
  have hplen := bc_positions_length e
  have hp : p < e.bc.positions.length := Nat.lt_of_lt_of_le hs.phi hs.pend
  have hx5 := hs.x5
  have hp2 : 2 * p + 2 ≤ 2 * e.posLen.toNat := by rw [← hplen]; omega
  simp only [Env.posLen, Env.posPtr, Env.bcp] at hp2 hpm hpa hx5
  obtain ⟨u, hr, hx7, hreg, hm, hupc⟩ := lhu_bgeu hpc fetch_11114 rfl br11118 (by decide)
    (by decide) (by
      rw [hx5]
      refine valid_half hpm ?_ ?_ ?_ <;> addr_omega [hpm, hpa, hp2])
  have hpos : t.getHalfword (t.getReg .x5) = e.bc.positions[p] := by
    rw [bc_positions e hp, hx5]
    exact hs.mem.bcHalf he hpc' hpm (by addr_omega [hpm, hp2])
      (by addr_omega [hpm, hp2]) (by addr_omega [hpm, hpa, hp2])
  rw [hpos] at hx7 hupc
  have hzx : ((e.bc.positions[p]).zeroExtend 64 : Word).toNat = (e.bc.positions[p]).toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by have := (e.bc.positions[p]).isLt; omega)
  rw [hzx, hs.x18] at hupc
  by_cases hc : 2 ^ e.m ≤ (e.bc.positions[p]).toNat
  · simp only [hc, ↓reduceIte] at hupc
    exact ⟨u, hr, Or.inl (dead_of_fetch (by rw [hupc]; exact trap))⟩
  simp only [hc, ↓reduceIte] at hupc
  have hq : (e.bc.positions[p]).toNat < 2 ^ e.m := Nat.lt_of_not_le hc
  have hlm := he.lowMapped
  have hla := he.lowIn.2.2
  have hu9 : u.getReg .x9 = e.low := (hreg .x9 (by decide)).trans hs.x9
  have hu7 : u.getReg .x7 = BitVec.ofNat 64 (e.bc.positions[p]).toNat := by
    rw [hx7]; apply BitVec.eq_of_toNat_eq; rw [hzx, BitVec.toNat_ofNat]
    have := (e.bc.positions[p]).isLt
    omega
  have hum : LoopMem e u := hs.mem.same hm
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8001111c_spec hupc (by
    rv_eval [hu9, hu7, mul24]
    have hq' : (BitVec.ofNat 64 (e.bc.positions[p]).toNat).toNat = (e.bc.positions[p]).toNat := by
      rw [BitVec.toNat_ofNat]; have := (e.bc.positions[p]).isLt; omega
    rw [hq']
    and_intros <;> valid_in hlm [hlm, hla, hq])
  have k₂ := b8001111c_keeps h₂
  have hw := hum.low he hq
  have x16 := b8001111c_x16 h₂
  have x15 := b8001111c_x15 h₂
  have x14 := b8001111c_x14 h₂
  have hq' : (BitVec.ofNat 64 (e.bc.positions[p]).toNat).toNat = (e.bc.positions[p]).toNat := by
    rw [BitVec.toNat_ofNat]; have := (e.bc.positions[p]).isLt; omega
  rw [hu9, hu7, mul24, hq'] at x16 x15 x14
  have hacc : (v.getReg .x16, v.getReg .x15, v.getReg .x14) = limbs (memberSumRust e.lowW
      ((e.bc.positions.drop (e.ps i j)).take (p + 1 - e.ps i j))) := by
    rw [take_drop_succ _ hs.plo hp, memberSum_snoc, limbs_add, ← hs.acc, hw, x16, x15, x14,
      hreg .x16 (by decide), hreg .x15 (by decide), hreg .x14 (by decide)]
    simp only [Prod.mk.injEq]
    exact ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  have hvm : ∀ a, v.getMem a = t.getMem a := fun a ↦ by rw [b8001111c_mem_same h₂, hm]
  have kv : ∀ r ∈ [Reg.x2, .x9, .x11, .x12, .x13, .x17, .x18, .x19, .x20, .x21, .x23],
      v.getReg r = t.getReg r := fun r hr ↦ by
    rw [k₂ r (mem_of_mem hr _), hreg r (by revert hr; decide +revert)]
  have w0 : Word0 e v i j := { hs.toBlk.of_same hvm fun r hr ↦ kv r (mem_of_mem hr _) with
    jlo := hs.jlo
    jhi := hs.jhi
    x13 := (kv .x13 (by decide)).trans hs.x13
    x12 := (kv .x12 (by decide)).trans hs.x12
    buckets := (buckets_congr he fun a _ ↦ hvm a).trans hs.buckets
    pslo := hs.pslo
    pend := hs.pend
    x19 := by rw [kv .x19 (by decide)]; exact hs.x19
    x17 := (kv .x17 (by decide)).trans hs.x17 }
  have hx6 := hs.x6
  have hu6 : u.getReg .x6 = t.getReg .x6 := hreg .x6 (by decide)
  by_cases hend : p + 1 = (e.wd j).2
  · have h0 : u.getReg .x6 - 1 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [hu6, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
        rw [hx6]; simp only [Sym.wordToNatLit]; have := hs.phi; omega))]
      simp only [Sym.wordToNatLit]; rw [hx6]; omega
    refine ⟨v, hr.trans hr₂, Or.inr (Or.inl ⟨b8001111c_pc_not_taken h₂ h0, ?_⟩)⟩
    exact { w0 with acc := by rw [← hend]; exact hacc }
  · have h0 : u.getReg .x6 - 1 ≠ 0 := by
      intro h
      have := congrArg BitVec.toNat h
      rw [hu6, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
        rw [hx6]; simp only [Sym.wordToNatLit]; have := hs.phi; omega))] at this
      simp only [Sym.wordToNatLit] at this; rw [hx6] at this; have := hs.phi; omega
    refine ⟨v, hr.trans hr₂, Or.inr (Or.inr ⟨b8001111c_pc_taken h₂ h0, ?_⟩)⟩
    exact { w0 with
      plo := Nat.le_succ_of_le hs.plo
      phi := by have := hs.phi; omega
      x5 := by
        rw [b8001111c_x5 h₂, hreg .x5 (by decide), hx5, BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Sym.wordToNatLit]
        omega
      x6 := by
        rw [b8001111c_x6 h₂, hu6, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
          rw [hx6]; simp only [Sym.wordToNatLit]; have := hs.phi; omega))]
        simp only [Sym.wordToNatLit]; rw [hx6]; omega
      acc := hacc }

/-- The sum over word `j`'s positions, to its end. -/
theorem sum_loop (he : EnvOk e) {t : MachineState} {i j p : Nat} (hs : SInv e t i j p)
    (hpc : t.pc = 0x80011114) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x80011150 ∧ AInv e u i j)) := by
  refine Reaches.loop (fun t ↦ ∃ p, t.pc = 0x80011114 ∧ SInv e t i j p)
    (fun t ↦ (t.getReg .x6).toNat) _ (fun t ⟨p, hpc, hs⟩ ↦ ?_) t ⟨p, hpc, hs⟩
  obtain ⟨u, hr, hd | ⟨hu, ha⟩ | ⟨hu, hs'⟩⟩ := sum_body he hs hpc
  · exact Or.inl ⟨u, hr, Or.inl hd⟩
  · exact Or.inl ⟨u, hr, Or.inr ⟨hu, ha⟩⟩
  · refine Or.inr ⟨u, hr, ⟨p + 1, hu, hs'⟩, ?_⟩
    rw [hs'.x6, hs.x6]
    have := hs'.phi
    omega

end Rv64Verifier.Proofs.Bytecode.Eval
