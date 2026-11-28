module

public import NativeRustcVmArm.Ring.Coeff.Basic

/-!
# `ring_coefficients`: the environment of the loop's blocks

The entry's facts (`P`: the stack, `f`, `g`, `out` readable and apart), the loop's environment
(`envB`: the frame, the row of `out` turn `p` writes, `f_p`) well formed and matching `midS`
(`body_wf`, `body_match`), what a block keeps (`after_block`: the turn's registers and the frame;
`out`'s bytes below the block's writes) and what a call keeps (`after_call`).
-/

namespace NativeRustcVmArm.Ring.Coeff

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

public section

variable {m0 : MachineData}

/-! ## The entry's facts -/

theorem stack_eq : ringCoefficientsStack = 784 := rfl

/-- The entry's facts, unpacked. -/
structure P (m0 : MachineData) : Prop where
  st : StackOk m0 ringCoefficientsStack
  fm : Mapped m0.dmem (fA m0) 128
  fw : NoWrap (fA m0) 128
  fs : Apart (fA m0) 128 (stackBelow m0 ringCoefficientsStack) ringCoefficientsStack
  gm : Mapped m0.dmem (gA m0) 128
  gw : NoWrap (gA m0) 128
  gs : Apart (gA m0) 128 (stackBelow m0 ringCoefficientsStack) ringCoefficientsStack
  om : Mapped m0.dmem (oA m0) 1024
  ow : NoWrap (oA m0) 1024
  os : Apart (oA m0) 1024 (stackBelow m0 ringCoefficientsStack) ringCoefficientsStack
  of : Apart (oA m0) 1024 (fA m0) 128
  og : Apart (oA m0) 1024 (gA m0) 128

theorem P.intro (h : RingCoefficientsPre m0) : P m0 :=
  ⟨h.1, h.2.1.1.1, h.2.1.1.2, h.2.1.2, h.2.2.1.1.1, h.2.2.1.1.2, h.2.2.1.2, h.2.2.2.1.1.1,
    h.2.2.2.1.1.2, h.2.2.2.1.2, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem P.hN (h : P m0) : ringCoefficientsStack ≤ m0.regs.SP.toNat := h.st.2.1

theorem P.fbN (h : P m0) : (fb m0).toNat = m0.regs.SP.toNat - 176 :=
  base_toNat (by have := h.hN; rw [stack_eq] at this; omega)

theorem P.sN (h : P m0) : (stackBelow m0 ringCoefficientsStack).toNat = m0.regs.SP.toNat - 784 :=
  base_toNat h.hN

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 176 := by decide

theorem slots_ge : ∀ p ∈ slots, 80 ≤ p.1 := by decide

/-- `out`'s bytes are outputs. -/
theorem out_in (h : P m0) {i : Nat} (hi : i < 1024) :
    InRange (oA m0) 1024 (oA m0 + BitVec.ofNat 64 i) :=
  NativeRustcVm.inRange_add hi (by have := h.ow; unfold NoWrap at this; omega)

/-- `out` is apart from the frame. -/
theorem out_frame (h : P m0) : ∀ q, InRange (oA m0) 1024 q → ¬InRange (fb m0) 176 q := by
  intro q hq hf
  have hap : Apart (oA m0) 1024 (fb m0) 176 := apart_frame h.hN (by decide) h.os
  have hnw : NoWrap (fb m0) 176 := base_noWrap (by have := h.hN; rw [stack_eq] at this; omega)
  exact NativeRustcVm.Apart.not_inRange hap h.ow hnw hq hf

theorem rowA_toNat (h : P m0) {p : Nat} (hp : p < 8) :
    (rowA m0 p).toNat = (oA m0).toNat + 128 * p := by
  unfold rowA
  rw [NativeRustcVm.toNat_add_ofNat (by have := h.ow; unfold NoWrap at this; omega)]

theorem fp_toNat (h : P m0) {p : Nat} (hp : p < 8) :
    (fA m0 + BitVec.ofNat 64 (16 * p)).toNat = (fA m0).toNat + 16 * p := by
  rw [NativeRustcVm.toNat_add_ofNat (by have := h.fw; unfold NoWrap at this; omega)]

/-! ## The loop's environment -/

section
variable [Labels] {p : Nat} {m : MachineData}

omit [Labels] in
theorem body_wf (h : P m0) (hB : Body m0 p m) : (envB m0 p m).WF := by
  have hp := hB.lt
  have hN := h.hN
  have he := stack_eq
  have hSP := m0.regs.SP.toNat_lt
  have hfb := h.fbN
  have hsN := h.sN
  have hr := rowA_toNat h hp
  have hf := fp_toNat h hp
  have := h.ow; have := h.fw; have := h.os; have := h.fs; have := h.of
  unfold NoWrap Apart at *
  refine Env.wf_of ⟨⟨fun i hi ↦ hB.fr.kept _ (frame_mapped h.st (by decide) i hi), ?_⟩,
    ⟨fun i hi ↦ hB.fr.kept _ ?_, ?_⟩, ⟨fun i hi ↦ hB.fr.kept _ ?_, ?_⟩, trivial⟩ ?_
  · show (fb m0).toNat + 176 ≤ _; omega
  · have := h.om (128 * p + i) (by omega)
    rwa [← NativeRustcVm.addr_add_add] at this
  · show (rowA m0 p).toNat + 128 ≤ _; omega
  · have := h.fm (16 * p + i) (by omega)
    rwa [← NativeRustcVm.addr_add_add] at this
  · show (fA m0 + BitVec.ofNat 64 (16 * p)).toNat + 16 ≤ _; omega
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · show (fb m0).toNat + 176 ≤ (rowA m0 p).toNat ∨ (rowA m0 p).toNat + 128 ≤ (fb m0).toNat
        omega
      · show (fb m0).toNat + 176 ≤ (fA m0 + BitVec.ofNat 64 (16 * p)).toNat ∨
          (fA m0 + BitVec.ofNat 64 (16 * p)).toNat + 16 ≤ (fb m0).toNat
        omega
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      show (rowA m0 p).toNat + 128 ≤ (fA m0 + BitVec.ofNat 64 (16 * p)).toNat ∨
        (fA m0 + BitVec.ofNat 64 (16 * p)).toNat + 16 ≤ (rowA m0 p).toNat
      omega

theorem body_match (h : P m0) (hB : Body m0 p m) : Match (envB m0 p m) midS m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.st (by decide) (by decide), rfl,
      fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hB.fr.sp]; simp [Sym.eval])
    ⟨by show (m.regs.getXReg .X26).toBitVec = _; rw [hB.x26]; rfl,
      by show (m.regs.getXReg .X27).toBitVec = _; rw [hB.x27]; rfl, trivial⟩ trivial trivial trivial

/-- The value of a location of the frame in a block's environment. -/
theorem eval_gLoc1 (b : Nat) :
    (gLoc b).1.eval (envB m0 p m) = (locVal (fb m0) 176 m (gLoc b).1).toBitVec := by
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;> rfl

theorem eval_gLoc2 (b : Nat) :
    (gLoc b).2.eval (envB m0 p m) = (locVal (fb m0) 176 m (gLoc b).2).toBitVec := by
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;> rfl

omit [Labels] in
theorem gLoc_cs (b : Nat) : locCS 176 (gLoc b).1 = true ∧ locCS 176 (gLoc b).2 = true := by
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | b <;> exact ⟨rfl, rfl⟩

/-! ## After a block -/

/-- **After a block** of turn `p` that keeps the pointers and writes in the frame below the slots
and in the row's bytes from `lo` to `hi`: the turn's registers and frame, and `out`'s bytes before
the row's byte `lo`. -/
theorem after_block (h : P m0) (hB : Body m0 p m) {S' : SState} {m' : MachineData}
    (hm1 : Match (envB m0 p m) S' m') (hptr : ptrsOk S' = true) {lo hi : Nat}
    (hwr : wrOk lo hi S' = true) (hlo : lo ≤ hi) (hhi : hi ≤ 128) :
    Body m0 p m' ∧ ∀ L : List EW, 16 * L.length ≤ 128 * p + lo →
      NativeRustcVm.EWsAt m.dmem (oA m0) L → NativeRustcVm.EWsAt m'.dmem (oA m0) L := by
  have hwf := body_wf h hB
  simp only [ptrsOk, Bool.and_eq_true, beq_iff_eq] at hptr
  obtain ⟨⟨h26, h27⟩, hsp⟩ := hptr
  simp only [wrOk, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hwr
  have hp := hB.lt
  have hfr := hB.fr.ofBlockW (body_match h hB) hm1 hwf rfl (by rw [hsp]; rfl) (fun _ h ↦ by cases h)
    rfl (by decide) h.hN slots_le fun w hw ↦ by
      rcases hwr w hw with ⟨h0, h1⟩ | ⟨⟨h0, h1⟩, h2⟩
      · exact .inl ⟨h0, by omega, fun q hq ↦ .inl (by have := slots_ge q hq; omega)⟩
      · refine .inr ⟨by rw [h0]; decide, fun b sz hb ↦ ?_⟩
        rw [h0] at hb
        cases hb
        refine ⟨by omega, fun i hi ↦ ?_⟩
        rw [rowA, NativeRustcVm.addr_add_add]
        exact out_in h (by omega)
  refine ⟨⟨hfr, hp, ?_, ?_⟩, fun L hL hL0 ↦ ?_⟩
  · rw [hm1.regs .X26 _ h26]; rfl
  · rw [hm1.regs .X27 _ h27]; rfl
  · refine NativeRustcVm.BytesAt.of_sameOutside hL0 (hm1.sameOutside hwf) fun i hi ↦ ?_
    rw [NativeRustcVm.length_ewsBytes] at hi
    have hai : (oA m0 + BitVec.ofNat 64 i).toNat = (oA m0).toNat + i := by
      rw [NativeRustcVm.toNat_add_ofNat (by have := h.ow; unfold NoWrap at this; omega)]
    have hfbN := h.fbN
    have hfr0 := out_frame h _ (out_in h (i := i) (by omega))
    rw [Sym.inRange_iff (base_noWrap (by have := h.hN; rw [stack_eq] at this; omega)), hai,
      hfbN] at hfr0
    refine not_written fun w hw b sz hb ↦ ?_
    rw [hai]
    rcases hwr w hw with ⟨h0, h1⟩ | ⟨⟨h0, h1⟩, h2⟩
    · rw [h0] at hb
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hb)
      subst h1 h2
      rw [hfbN]
      omega
    · rw [h0] at hb
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hb)
      subst h1 h2
      rw [rowA_toNat h hp]
      omega

/-! ## After a call -/

/-- **After a call** that keeps the callee-saved registers and changes only its `N'` bytes of
stack: the turn's registers and frame, every location a call keeps, `out`. -/
theorem after_call (h : P m0) (hB : Body m0 p m) {m2 : MachineData} {N' : Nat}
    (hN' : 176 + N' ≤ ringCoefficientsStack)
    (hcs : ∀ r, calleeSaved r = true → m2.regs.getXReg r = m.regs.getXReg r)
    (hs : SameOutside m.dmem m2.dmem fun q ↦ InRange (stackBelow m N') N' q ∨ False)
    (hfr : CFr m0 m2) :
    Body m0 p m2 ∧ (∀ s, locCS 176 s = true → locVal (fb m0) 176 m2 s = locVal (fb m0) 176 m s) ∧
      ∀ L : List EW, 16 * L.length ≤ 1024 →
        NativeRustcVm.EWsAt m.dmem (oA m0) L → NativeRustcVm.EWsAt m2.dmem (oA m0) L := by
  have hN := h.hN
  refine ⟨⟨hfr, hB.lt, by rw [hcs .X26 rfl]; exact hB.x26, by rw [hcs .X27 rfl]; exact hB.x27⟩,
    fun s hl ↦ locVal_call hB.fr.sp (by omega) hcs hs hl, fun L hL hL0 ↦ ?_⟩
  have hap := hB.fr.apart hN h.os (N' := N') hN'
  refine NativeRustcVm.BytesAt.of_sameOutside hL0 hs fun i hi ↦ ?_
  rw [NativeRustcVm.length_ewsBytes] at hi
  rintro (hq | hq)
  · have hsb := stackBelow_eq hB.fr.sp (N' := N') (by omega)
    have hnw : NoWrap (stackBelow m N') N' := by
      rw [hsb]; unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
    exact NativeRustcVm.Apart.not_inRange_add hap h.ow hnw (i := i) (by omega) hq
  · exact hq

end

end

end NativeRustcVmArm.Ring.Coeff
