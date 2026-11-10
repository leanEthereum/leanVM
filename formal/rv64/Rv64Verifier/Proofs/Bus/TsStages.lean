import Rv64Verifier.Proofs.Bus.TsWeightsStage

/-!
# `table_sumcheck`: the rows' and the terminal's interface

`AtTerminal` is the state at `0x80008520`, after the rows loop: the rows at `S - 296`, `a1` the
terminal loop's count before the weights' bound. `mirror_run` splits the mirror at the rows;
`err928` returns an `Err` from `0x80008928`, where both the rows loop and the terminal fail.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The tables and heights the rows loop zips, on the entry's arguments. -/
def rowItems (s : MachineState) : List (Table × ℕ) :=
  (tablesAt s (s.getReg .x11) (s.getReg .x12).toNat).zip
    (natsAt s (s.getReg .x13) (s.getReg .x14).toNat)

/-- The checked terminal on the entry's arguments, the rows and the weights. -/
def terminalOf (s : MachineState) (rows : List (List E × List E)) (weights : List E) : E :=
  terminalRust (eListAt s (s.getReg .x17) (s.getReg .x28).toNat)
    (eListAt s (s.getReg .x29) (s.getReg .x30).toNat)
    ((((tablesAt s (s.getReg .x11) (s.getReg .x12).toNat).zip rows).zip
      (formRowsAt s (s.getReg .x15) (s.getReg .x16).toNat)).zip weights)

/-- At `0x80008520`: the rows at `S - 296`, read from the transcript after `sumcheck`. -/
structure AtTerminal (s u : MachineState) (ch : List E) (cl : E) (P W : Word)
    (rows : List (List E × List E)) : Prop where
  inv : Inv s u
  kept : Kept s u cl P
  args : Args s u
  tablesLen : u.getMem (s.getReg .x2 - 392) = s.getReg .x12
  wptr : vecPtr u (s.getReg .x2 - 320) = W
  wlen : vecLen u (s.getReg .x2 - 320) = s.getReg .x12
  wbuf : NewBuf s u W (24 * (s.getReg .x12).toNat) 8
  weights : eListAt u W (s.getReg .x12).toNat = weightsOf s ch
  rowsAt : RowsAt s u (s.getReg .x2 - 296) rows
  rowsLen : rows.length = min (s.getReg .x12).toNat (s.getReg .x14).toNat
  x11 : u.getReg .x11 =
    BitVec.ofNat 64 (min (min (s.getReg .x12).toNat rows.length) (s.getReg .x16).toNat)
  run : ∀ T, TranscriptAt s (tsSelf s) T → ∃ T₁ T₂,
    (TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none)).run T =
      some ((ch, cl), T₁) ∧ (readRowsM ch.reverse (rowItems s) []).run T₁ = some (rows, T₂) ∧
      TranscriptAt u (tsSelf s) T₂

theorem tablesAt_length (s : MachineState) (a : Word) (n : Nat) : (tablesAt s a n).length = n := by
  simp [tablesAt]

/-- The mirror, once `sumcheck` and the rows have run: the terminal's check. -/
theorem mirror_run (s : MachineState) {T T₁ T₂ : TState} {ch : List E} {cl : E}
    {rows : List (List E × List E)}
    (h1 : (TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none)).run T =
      some ((ch, cl), T₁))
    (h2 : (readRowsM ch.reverse (rowItems s) []).run T₁ = some (rows, T₂)) :
    (mirror s).run T =
      if terminalOf s rows (weightsOf s ch) = cl then some (rows, T₂) else none := by
  rw [nRounds] at h1
  rw [rowItems] at h2
  simp only [mirror, tableSumcheckM, StateT.run_bind, h1, Option.bind_eq_bind, Option.bind_some,
    h2, terminalOf, weightsOf]
  rw [tablesAt_length]
  by_cases hc : terminalRust (eListAt s (s.getReg .x17) (s.getReg .x28).toNat)
      (eListAt s (s.getReg .x29) (s.getReg .x30).toNat)
      ((((tablesAt s (s.getReg .x11) (s.getReg .x12).toNat).zip rows).zip
        (formRowsAt s (s.getReg .x15) (s.getReg .x16).toNat)).zip
        (tableWeightsRust (s.getReg .x12).toNat (natsAt s (s.getReg .x13) (s.getReg .x14).toNat)
          (eListAt s (s.getReg .x31) (tsEqLen s).toNat) ch.reverse)) = cl
  · simp [hc, TM.require, StateT.run]; rfl
  · simp [hc, TM.require, StateT.run]

/-- The rows fail: so does the mirror. -/
theorem mirror_run_none (s : MachineState) {T T₁ : TState} {ch : List E} {cl : E}
    (h1 : (TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none)).run T =
      some ((ch, cl), T₁))
    (h2 : (readRowsM ch.reverse (rowItems s) []).run T₁ = none) : (mirror s).run T = none := by
  rw [nRounds] at h1
  rw [rowItems] at h2
  simp [mirror, tableSumcheckM, StateT.run_bind, h1, h2]

/-- `Err` from `0x80008928`: the capacity takes the niche, the error's payload `a0` bytes in. -/
theorem err928 {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u)
    (hpc : u.pc = 0x80008928) (hout : u.getMem (s.getReg .x2 - 456) = s.getReg .x10)
    (h10 : u.getReg .x10 = 8 ∨ u.getReg .x10 = 16)
    (hnone : ∀ T, TranscriptAt s (tsSelf s) T → (mirror s).run T = none) :
    ∃ t, Reaches Image.code u t ∧ Done s t := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have ho := hpre.out
  have os := hpre.outStack
  have ox := hpre.outFree.2
  simp only [stack_eq] at os
  have hout' : u.getMem (u.getReg .x2 + 40) = s.getReg .x10 := by
    rw [h.sp, show s.getReg .x2 - 496 + 40 = s.getReg .x2 - 456 by addr_omega [hb1]]; exact hout
  have h10' : (u.getReg .x10).toNat = 8 ∨ (u.getReg .x10).toNat = 16 := by
    rcases h10 with e | e <;> rw [e] <;> simp
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80008928_spec hpc (by
    rv_eval [hout']
    and_intros
    · exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho]) (by addr_omega [ho])
    · rcases h10' with e | e <;>
        exact Region.valid ho (by addr_omega [ho, e]) (by addr_omega [ho, e]) (by addr_omega [ho, e])
    · rw [h.sp]; valid_access hval [hb1]
    · rcases h10' with e | e <;> addr_omega [ho, e])
  have hf : DFrame u t (Within · (s.getReg .x10) 24) := fun a ha ↦
    ht.frame a (by
      rv_eval [hout']
      have h0 := ha 0 (by decide)
      rw [add_ofNat_zero] at h0
      refine ⟨fun e ↦ h0 (by rw [e]; addr_omega [ho]), fun e ↦ ?_⟩
      rcases h10' with e' | e' <;> exact h0 (by rw [e]; addr_omega [ho, e']))
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf nextAddr fun i hi hw ↦ by addr_omega [hw, hi, ox])
  have I : Inv s t := h.step hpre hf (fun a ha ↦ ⟨Or.inl ha, by addr_omega [ha, os, hb1]⟩)
    ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩ hn.ge (b80008928_keeps ht .x2 (by decide))
  obtain ⟨t', hr', ht'⟩ := errExit hpre I (b80008928_pc ht)
    (by rw [vecCap, ← hout', b80008928_m0 ht]; rfl) hnone
  exact ⟨t', hr.trans hr', ht'⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
