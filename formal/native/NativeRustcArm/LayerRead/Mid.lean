module

public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.LayerRead.Inv
meta import NativeRustcArm.Code.Xmss.LayerRead

/-!
# `LayerSignature::read`: moving the chain values

Block 4 copies 928 bytes from `frame + 928` to `frame`, freeing the upper
part of the frame for the path.
-/

namespace NativeRustcArm.Xmss.LayerRead

open NativeRustcArm.Sym NativeRustcArm

set_option Elab.async false

sym_block b4_execM := exec b4 (init [] .sp)

/-- The chain values' slots hold their bytes. -/
theorem chainBytes_at {m₀ m : MachineData} (P : Pre m₀) (h : LoopDone m₀ m) :
    BytesAt m.dmem (frame m₀ + BitVec.ofNat 64 928) (chainBytes m₀) :=
  bytesAt_flatten 58 (fun j hj => P.chainSlot_length hj)
    fun j hj => by rw [addr_add_addr]; exact h.chain j hj

public theorem length_chainBytes {m₀ : MachineData} (P : Pre m₀) : (chainBytes m₀).length = 928 := by
  unfold chainBytes
  rw [List.length_flatten, List.map_map]
  have : ∀ n ≤ 58, ((List.range n).map (List.length ∘ chainSlot m₀)).sum = 16 * n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
      simp [P.chainSlot_length (j := n) (by omega)]
      omega
  exact this 58 le_rfl

/-- **The `memcpy` of the chain values.** -/
public theorem mid [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m₀ : MachineData} (P : Pre m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b4Offset)) (h : LoopDone m₀ st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b5Offset) → MidAt m₀ st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have hwf := Env.wf_nil st.data
  refine exec_at (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) b4_execM hwf hpc (match_nil st.data)
    fun st₁ hm₁ hpc₁ => ?_
  have hs₁ : Saved st.data st₁.data :=
    Match.saved (match_nil st.data) hm₁ hwf rfl (by decide +kernel)
  have hd₁ : st₁.data.dmem = st.data.dmem := hm₁.dmem_eq hwf rfl
  have hx0 : st₁.data.regs.X0.toBitVec = frame m₀ :=
    (hm₁.regs .X0 .sp (by decide +kernel)).trans C.sp
  have hx1 : st₁.data.regs.X1.toBitVec = frame m₀ + BitVec.ofNat 64 928 :=
    (hm₁.regs .X1 (.bin .add .W64 .sp (.lit 928)) (by decide +kernel)).trans
      (by simp [Sym.eval, BinOp.apply]; exact C.sp)
  have hx2 : st₁.data.regs.X2.toNat = 928 := by
    have := hm₁.regs .X2 (.lit 928) (by decide +kernel)
    simp only [Sym.eval] at this
    show st₁.data.regs.X2.toBitVec.toNat = 928
    erw [this]
    rfl
  have hF := P.frameNW
  unfold layerReadStack at hF
  have hpre : MemcpyPre st₁.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hx0, hx1, hx2]
    · exact (show Mapped m₀.dmem (frame m₀) 928 from
        fun i hi => P.frameMapped i (by unfold layerReadStack; omega)).kept
          (C.kept.trans (hd₁ ▸ Kept.refl _))
    · exact (P.frameMapped.sub (by unfold layerReadStack; omega)).kept (C.kept.trans (hd₁ ▸ Kept.refl _))
    · unfold NoWrap at *
      omega
    · exact P.frameNW.sub (by unfold layerReadStack; omega)
    · unfold Apart
      rw [toNat_addr hF (by omega)]
      omega
  refine call_then hpc₁ hmemcpy hpre fun st₂ hpc₂ hpost => cont st₂ hpc₂ ?_
  obtain ⟨-, hcopy, hsame, hs₂⟩ := hpost
  simp only [hx0, hx1, hx2] at hcopy hsame
  have hnot : ∀ x, 928 ≤ x → x < 1936 →
      ¬InRange (frame m₀) 928 (frame m₀ + BitVec.ofNat 64 x) := by
    intro x hx hx'
    rw [Sym.inRange_iff (show NoWrap (frame m₀) 928 by unfold NoWrap at *; omega),
      toNat_addr hF hx']
    omega
  have hs := hs₁.trans hs₂
  refine ⟨C.transfer P hs (R := InRange (frame m₀) 928)
      (hd₁ ▸ hsame) (fun p hp => Or.inl (by
        unfold InRange layerReadStack at *
        omega))
      (fun j hj hj3 t ht => by rw [addr_add_addr]; exact hnot _ (by omega) (by omega)),
    ?_, ?_, ?_, ?_⟩
  · rw [hs.1 .X22 rfl]; exact h.x22
  · rw [hs.1 .X23 rfl]; exact h.x23
  · rw [hs.1 .X24 rfl]; exact h.x24
  · have := (chainBytes_at P h).bytesOf
    rw [length_chainBytes P] at this
    rw [hd₁, this] at hcopy
    exact hcopy

end NativeRustcArm.Xmss.LayerRead
