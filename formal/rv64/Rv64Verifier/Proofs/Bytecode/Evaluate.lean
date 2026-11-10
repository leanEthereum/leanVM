import Rv64Verifier.Proofs.Bytecode.EvalBlock
import Rv64Verifier.Proofs.Bytecode.EvalCalls
import Rv64Verifier.Proofs.Bytecode.EvalEnter

/-!
# `Bytecode::evaluate` meets its contract

`evaluate_spec`: from the entry, `Err` when the point's size is wrong (`prologue`, `err_exit`);
otherwise the three calls (`calls`, `enter`), then `Ok(ZERO)` for a table with no block or the
blocks (`blocks_loop`) and `Ok(total)` (`ok_exit`). The value is `evaluateRust`'s; what is written
is the result, the stack, `NEXT` and fresh memory.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84

variable {e : Env}

/-- The loop's state: `Outer` before block `0`. -/
theorem outer_zero (he : EnvOk e) (hi : InitRegs e e.tL) : Outer e e.tL 0 := by
  have hlen := bc_blocks_length e
  have hst : e.st 0 = evalInit := rfl
  exact {
    sp := he.saved.sp
    mem := fun _ _ ↦ rfl
    x9 := hi.x9
    x18 := hi.x18
    x20 := hi.x20
    x21 := hi.x21
    x23 := hi.x23
    lt := by
      rw [hlen]
      have := hi.nonempty
      exact Nat.pos_of_ne_zero fun h ↦ this (BitVec.eq_of_toNat_eq (by simpa using h))
    x13 := by rw [hi.x13]; simp
    ws := by rw [hi.x12, hst]; rfl
    ps := by rw [hi.x19, hst]; rfl
    bs := by rw [hi.x11, hst]; rfl
    total := by rw [hi.x5, hi.x17, hi.x16, hst]; exact limbs_zero_eq.symm
    buckets := by rw [hst, he.bkVals]; rfl }

/-- `evaluateRust` on what the entry's memory holds, when the size check passes. -/
theorem evaluateRust_env (e : Env) (h1 : e.n < 64) (h2 : e.bc.len = 2 ^ e.n) :
    evaluateRust e.bc e.point = some (e.st e.bc.blocks.length).total := by
  have hl : e.point.length = e.n := eListAt_length _ _ _
  unfold evaluateRust
  rw [hl]
  simp only [h1, h2, and_self, ↓reduceIte, Option.some.injEq]
  rw [Env.st, evalAfter_length]
  rfl

/-- The result slot is aligned. -/
theorem out_align {s : MachineState} (hpre : EvaluatePre s) : (s.getReg .x10).toNat % 8 = 0 :=
  (ValidMemRange.bounds hpre.out (by decide)).2.1

/-- The memory part of the contract: from a frame of doublewords to `m`, a frame of whole
doublewords outside `X` to `t`, and the result slot to `u`. -/
theorem post_frames {s m t u : MachineState}
    (hB : Transcript.DFrame s m fun a ↦
      Within a (stackLo s evalStack) evalStack ∨ Within a nextAddr 8 ∨ Fresh s m a)
    {X : Word → Prop} (hXW : ∀ a, X a → EvaluateW s u a)
    (hL : ∀ a, ¬ X a → t.getMem a = m.getMem a)
    (hU : ∀ a, ¬ Within a (s.getReg .x10) 32 → u.getMem a = t.getMem a)
    (hnext : u.getMem nextAddr = m.getMem nextAddr) (hheap : HeapOk m)
    (hmono : heapNext s ≤ heapNext m) :
    HeapOk u ∧ heapNext s ≤ heapNext u ∧
      ∀ a, (∀ i < 8, ¬ EvaluateW s u (a + BitVec.ofNat 64 i)) → u.getMem a = s.getMem a := by
  have hN : heapNext u = heapNext m := by simp only [heapNext, hnext]
  have hFr : ∀ a, Fresh s m a → Fresh s u a := fun a h ↦ by
    simp only [Fresh] at h ⊢; rw [hN]; exact h
  refine ⟨⟨by rw [hN]; exact hheap.lo, by rw [hN]; exact hheap.hi⟩, by rw [hN]; exact hmono,
    fun a ha ↦ ?_⟩
  have h0 := ha 0 (by decide)
  simp only [BitVec.add_zero] at h0
  rw [hU a fun h ↦ h0 (Or.inl h), hL a fun h ↦ h0 (hXW a h)]
  exact hB a fun i hi hw ↦ ha i hi (by
    rcases hw with hw | hw | hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr (hFr _ hw))))

/-- `evaluateRust` on an empty table of the right size: `ZERO`. -/
theorem evaluateRust_empty {s : MachineState} (h1 : (s.getReg .x13).toNat < 64)
    (h2 : (readBytecode s (s.getReg .x11)).len = 2 ^ (s.getReg .x13).toNat)
    (h0 : vecLen s (s.getReg .x11) = 0) :
    evaluateRust (readBytecode s (s.getReg .x11)) (eListAt s (s.getReg .x12)
      (s.getReg .x13).toNat) = some 0 := by
  have h := evaluateRust_env ⟨s, s, 0, 0, 0⟩ h1 h2
  have hl := bc_blocks_length ⟨s, s, 0, 0, 0⟩
  simp only [Env.blocksLen, Env.bcp, h0] at hl
  rw [hl] at h
  exact h

/-- **`Bytecode::evaluate` meets its contract**, given `eq_kernel`'s, `vec![x; n]`'s and `mul`'s. -/
theorem evaluate_spec (hEK : EqKernelSpec) (hFE : FromElemSpec) (hMul : MulSpec) :
    EvaluateSpec := by
  intro s hpc hpre
  have hsp := sp_bounds hpre.stack
  have hoa := out_align hpre
  have hof := hpre.outFree
  have hos := hpre.outStack
  have hstn := hpre.stack.next
  obtain ⟨t, hr, ⟨htpc, hs, h10, hmem, hbad⟩ | ⟨htpc, hc⟩⟩ := prologue hpc hpre
  · obtain ⟨u, hu, hupc, hpres, h1, hfr⟩ := err_exit htpc hs hpre.stack h10 hpre.out hpre.outStack
    obtain ⟨hh, hm, hdw⟩ := post_frames (m := s) (t := t) (u := u)
      (Transcript.DFrame.refl _ _) (X := fun a ↦ Within a (stackLo s evalStack) evalStack)
      (fun a h ↦ Or.inr (Or.inl h)) hmem hfr
      (by rw [hfr _ (by addr_omega [hof]), hmem _ (by addr_omega [hstn, hsp])]) hpre.heap
      (Nat.le_refl _)
    refine ⟨u, hr.trans hu, Or.inl ⟨hupc, hpres, hh, hm, Or.inr ⟨h1, ?_⟩, hdw⟩⟩
    have hl : (eListAt s (s.getReg .x12) (s.getReg .x13).toNat).length = (s.getReg .x13).toNat :=
      eListAt_length _ _ _
    unfold evaluateRust
    rw [hl]
    simp only [hbad, ↓reduceIte]
  obtain ⟨t₁, hr₁, hd | ⟨hpc₁, low, high, bk, hcl⟩⟩ := calls hEK hFE hpre htpc hc
  · exact ⟨t₁, hr.trans hr₁, Or.inr hd⟩
  obtain ⟨t₂, hr₂, ⟨hpc₂, hemp⟩ | ⟨hpc₂, he, hinit⟩⟩ := enter hpre hpc₁ hcl
  · obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800116ec_spec hpc₂ trivial
    have hm₃ := b800116ec_mem_same h₃
    obtain ⟨u, hu, hupc, hpres, h0, h8, h16, h24, hfr⟩ := ok_exit (b800116ec_pc h₃)
      (hemp.saved.of_frame ((b800116ec_keeps h₃) .x2 (by decide)) (fun a _ _ ↦ hm₃ a)
        (by addr_omega [hsp]))
      (by rw [hm₃]; exact hemp.out) hpre.stack hpre.out hpre.outStack
    obtain ⟨hh, hm, hdw⟩ := post_frames (m := t₂) (t := t₃) (u := u) hemp.frame
      (X := fun _ ↦ False) (fun _ h ↦ h.elim) (fun a _ ↦ hm₃ a) hfr
      (by rw [hfr _ (by addr_omega [hof]), hm₃]) hemp.heap hemp.mono
    refine ⟨u, hr.trans (hr₁.trans (hr₂.trans (hr₃.trans hu))), Or.inl ⟨hupc, hpres, hh, hm,
      Or.inl ⟨h0, ?_⟩, hdw⟩⟩
    rw [evaluateRust_empty hemp.short hemp.len hemp.empty]
    congr 1
    apply Eq.symm
    apply eAt_eq_of_limbs
    rw [show s.getReg .x10 + 8 + 8 = s.getReg .x10 + 16 by rw [BitVec.add_assoc]; rfl,
      show s.getReg .x10 + 8 + 16 = s.getReg .x10 + 24 by rw [BitVec.add_assoc]; rfl,
      h8, h16, h24, b800116ec_x5 h₃, b800116ec_x17 h₃, b800116ec_x16 h₃]
    exact limbs_zero_eq.symm
  · obtain ⟨t₃, hr₃, hd | ⟨hpc₃, hreg, htot⟩⟩ := blocks_loop hMul he (outer_zero he hinit) hpc₂
    · exact ⟨t₃, hr.trans (hr₁.trans (hr₂.trans hr₃)), Or.inr hd⟩
    have hbk := he.bkIn
    have hhh := he.heapL.hi
    simp only [heapNext, heapEnd] at hbk hhh
    have hsaved : Saved s t₃ := he.saved.of_frame (hreg.sp.trans he.saved.sp.symm)
      (fun a h1 h2 ↦ hreg.mem a (by addr_omega [h1, h2, hsp, hbk, hhh])) (by addr_omega [hsp])
    have hout : t₃.getMem (s.getReg .x2 - 1960) = s.getReg .x10 := by
      rw [hreg.mem.slot he]; exact he.out
    obtain ⟨u, hu, hupc, hpres, h0, h8, h16, h24, hfr⟩ :=
      ok_exit hpc₃ hsaved hout hpre.stack hpre.out hpre.outStack
    obtain ⟨hh, hm, hdw⟩ := post_frames (m := t₂) (t := t₃) (u := u) he.frame
      (X := Scratch ⟨s, t₂, low, high, bk⟩)
      (fun a h ↦ by
        have hb2 := he.bkIn
        simp only [Scratch, EvaluateW, Fresh, heapNext] at h ⊢
        rw [hfr _ (by addr_omega [hof]), hreg.mem _ (by addr_omega [hstn, hsp, hbk, hhh])]
        addr_omega [h, hsp, hb2, hhh])
      hreg.mem hfr (by rw [hfr _ (by addr_omega [hof]), hreg.mem _ (by
        addr_omega [hstn, hsp, hbk, hhh])]) he.heapL he.monoL
    refine ⟨u, hr.trans (hr₁.trans (hr₂.trans (hr₃.trans hu))), Or.inl ⟨hupc, hpres, hh, hm,
      Or.inl ⟨h0, ?_⟩, hdw⟩⟩
    have hv := evaluateRust_env ⟨s, t₂, low, high, bk⟩ he.short he.len
    refine hv.trans (congrArg some ?_)
    apply Eq.symm
    apply eAt_eq_of_limbs
    rw [show s.getReg .x10 + 8 + 8 = s.getReg .x10 + 16 by rw [BitVec.add_assoc]; rfl,
      show s.getReg .x10 + 8 + 16 = s.getReg .x10 + 24 by rw [BitVec.add_assoc]; rfl,
      h8, h16, h24]
    exact htot

end Rv64Verifier.Proofs.Bytecode.Eval
