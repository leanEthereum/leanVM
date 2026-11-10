import Rv64Verifier.Proofs.Transcript.Sponge
import Rv64Verifier.Proofs.Transcript.Contracts
import Rv64Verifier.Blocks.F46

/-!
# `Transcript::next_scalar`

```rust
fn next(&mut self) -> Result<E, VerifierError> {
    require(self.stream_offset < self.proof.stream.len(), VerifierError::StreamExhausted)?;
    let value = self.proof.stream[self.stream_offset];
    self.stream_offset += 1;
    Ok(value)
}

pub fn next_scalar(&mut self) -> Result<E, VerifierError> {
    let value = self.next()?;
    self.sponge.observe(value);
    Ok(value)
}
```

compiled at `0x8000c720` (`Blocks/F46.lean`), `next` inlined: a 64-byte frame saving `ra`, `s0`..`s3`;
`stream_offset ≥ len` goes to `0x8000c7a4` (`Err(StreamExhausted)`: tag `1`, discriminant `3`);
otherwise `0x8000c74c` reads the scalar into `s1`..`s3` and onto the stack, advances
`stream_offset`, and calls `absorb` with tag `1`; `0x8000c794` writes the scalar's high limbs;
`0x8000c7ac` writes the tag and the first word, restores and returns (`exit`).
-/

namespace Rv64Verifier.Transcript.NextScalar
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F46
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem nextScalar_some {T : TState} {x : E} (h : T.proof.stream[T.streamOffset]? = some x) :
    TM.nextScalar.run T = some (x, { T with
      streamOffset := T.streamOffset + 1
      sponge := spAbsorb T.sponge x dsObserve }) := by
  simp only [TM.nextScalar, StateT.run, h]
  rfl

theorem nextScalar_none {T : TState} (h : T.proof.stream[T.streamOffset]? = none) :
    TM.nextScalar.run T = none := by
  simp only [TM.nextScalar, StateT.run, h]

attribute [local rv_addr] vecPtr vecLen

/-- The callee-saved registers the function never touches. -/
def keptRegs : List Reg := [.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem bounds {s : MachineState} (h : NextScalarPre s) :
    0xa0000000 + nextScalarStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000000 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s nextScalarStack).toNat = (s.getReg .x2).toNat - nextScalarStack := by
  have hm := h.stack.mapped (by decide) (by decide)
  have hb := h.stack.bounds (by decide) (by decide)
  omega

theorem mul24 (w : Word) : w * 16 + w * 8 = BitVec.ofNat 64 (24 * w.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

/-- `0x8000c7ac`: the result's first two words, the callee-saved registers back, return. -/
theorem exit {s v : MachineState} (hpre : NextScalarPre s) (hpc : v.pc = 0x8000c7ac)
    (x2 : v.getReg .x2 = s.getReg .x2 - 64) (x8 : v.getReg .x8 = s.getReg .x10)
    (kept : ∀ r ∈ keptRegs, v.getReg r = s.getReg r)
    (ra : v.getMem (s.getReg .x2 - 8) = s.getReg .x1)
    (s0 : v.getMem (s.getReg .x2 - 16) = s.getReg .x8)
    (s1 : v.getMem (s.getReg .x2 - 24) = s.getReg .x9)
    (s2 : v.getMem (s.getReg .x2 - 32) = s.getReg .x18)
    (s3 : v.getMem (s.getReg .x2 - 40) = s.getReg .x19) :
    ∃ t, Reaches Image.code v t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getMem (s.getReg .x10) = v.getReg .x10 ∧ t.getMem (s.getReg .x10 + 8) = v.getReg .x9 ∧
      MemFrame v t (s.getReg .x10) 16 := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b8000c7ac_spec hpc (by
    rv_eval [x2, x8]
    and_intros <;> first
      | addr_omega [hb, ho, hos]
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have k := b8000c7ac_keeps h
  have pc := b8000c7ac_pc h
  have y1 := b8000c7ac_x1 h
  have y2 := b8000c7ac_x2 h
  have y8 := b8000c7ac_x8 h
  have y9 := b8000c7ac_x9 h
  have y18 := b8000c7ac_x18 h
  have y19 := b8000c7ac_x19 h
  have m0 := b8000c7ac_m_x8_0 h
  have m8 := b8000c7ac_m_x8_8 h
  have f := b8000c7ac_frame h (by rw [x8]; addr_omega [ho])
  rv_eval [x2] at pc y2 y8 y9 y18 y19
  rw [x8] at m0 m8 f
  refine ⟨t, hr, by rw [pc, ra, returnAddress_eq], ?_, m0, m8, f⟩
  exact preserves_of y2 (by rw [y8, s0]) (by rw [y9, s1]) (by rw [y18, s2]) (by rw [y19, s3])
    fun r hr ↦ by rw [k r (mem_of_mem hr _), kept r (mem_of_mem hr _)]

set_option maxHeartbeats 1000000 in
/-- **`Transcript::next_scalar` meets its contract**, given `absorb`'s. -/
theorem next_scalar_spec (hA : AbsorbSpec) : NextScalarSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hself := hpre.self
  have hS := hself.self
  have hP := hself.proof
  have hPA := hself.apart
  have ho := hpre.out
  have hos := hpre.outStack
  have hss := hpre.selfStack
  have hosf := hpre.outSelf
  have hps := hpre.proofStack
  have hpo := hpre.proofOut
  have hro := hpre.stack.rodata
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c720_spec hpc (by
    rv_eval []
    and_intros <;> first
      | addr_omega [hb, hS, hP, hss, hps]
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hS ?_ ?_ ?_ <;> addr_omega [hS])
      | (refine Region.valid hP ?_ ?_ ?_ <;> addr_omega [hP]))
  have k₁ := b8000c720_keeps h₁
  have x2₁ := b8000c720_x2 h₁
  have x8₁ := b8000c720_x8 h₁
  have x12₁ := b8000c720_x12 h₁
  have x13₁ := b8000c720_x13 h₁
  have sl₀ := b8000c720_m_x2_n40 h₁
  have sl₁ := b8000c720_m_x2_n32 h₁
  have sl₂ := b8000c720_m_x2_n24 h₁
  have sl₃ := b8000c720_m_x2_n16 h₁
  have sl₄ := b8000c720_m_x2_n8 h₁
  have f₁ := b8000c720_frame h₁ (by addr_omega [hb])
  have x11₁ : t₁.getReg .x11 = s.getReg .x11 := k₁ .x11 (by decide)
  -- what the function writes
  have W₁ : DFrame s t₁ (fun a ↦ Within a (s.getReg .x10) 32 ∨ Within a (s.getReg .x11 + 8) 344 ∨
      Within a (stackLo s nextScalarStack) nextScalarStack) :=
    (DFrame.of_memFrame f₁).mono fun a ha ↦ Or.inr (Or.inr (by addr_omega [ha, hb]))
  by_cases hlt : (s.getMem (s.getReg .x11 + 344)).toNat <
    (s.getMem (s.getMem (s.getReg .x11) + 16)).toNat
  swap
  · -- `Err(StreamExhausted)`
    obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c7a4_spec
      (b8000c720_pc_taken h₁ (by omega)) trivial
    have k₂ := b8000c7a4_keeps h₂
    have hm₂ := b8000c7a4_mem_same h₂
    obtain ⟨t, hr₃, pc, pres, m0, m8, f⟩ := exit hpre (b8000c7a4_pc h₂)
      (by rw [k₂ .x2 (by decide), x2₁]) (by rw [k₂ .x8 (by decide), x8₁])
      (fun r hr ↦ by rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)])
      (by rw [hm₂, sl₄]) (by rw [hm₂, sl₃]) (by rw [hm₂, sl₂]) (by rw [hm₂, sl₁]) (by rw [hm₂, sl₀])
    refine ⟨t, (hr₁.trans hr₂).trans hr₃, Or.inl ⟨pc, pres, ?_, ?_⟩⟩
    · intro T hT
      have hlen : T.proof.stream.length = streamLen s (s.getReg .x11) := by
        rw [← hT.stream, eListAt_length]
      rw [nextScalar_none (List.getElem?_eq_none (by
        rw [hlen, ← hT.streamOffset]; simp only [streamLen, proofAt, vecLen]; omega))]
      exact ⟨by rw [m0, b8000c7a4_x10 h₂], by rw [m8, b8000c7a4_x9 h₂]⟩
    · exact (W₁.trans (DFrame.of_same hm₂ _) fun _ h ↦ h).trans (DFrame.of_memFrame f)
        fun a ha ↦ Or.inl (by addr_omega [ha])
  -- the scalar, `stream_offset += 1`, `absorb`
  have hB : Region (streamPtr s (s.getReg .x11)) (24 * streamLen s (s.getReg .x11)) :=
    hself.stream.resolve_left (by simp only [streamLen, proofAt, vecLen]; omega)
  have eB : t₁.getMem (s.getMem (s.getReg .x11) + 8) = s.getMem (s.getMem (s.getReg .x11) + 8) :=
    f₁ _ (by addr_omega [hps, hb, hP])
  have eE (k : Word) (hk : k.toNat < 24) (hk8 : k.toNat % 8 = 0) :
      t₁.getMem (s.getMem (s.getMem (s.getReg .x11) + 8) +
        BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x11 + 344)).toNat) + k) =
      s.getMem (s.getMem (s.getMem (s.getReg .x11) + 8) +
        BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x11 + 344)).toNat) + k) :=
    f₁ _ (by addr_omega [hps, hb, hB, hlt, hk])
  obtain ⟨u₁, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c74c_spec
    (b8000c720_pc_not_taken h₁ hlt) (by
      rv_eval [x2₁, x12₁, x13₁, x11₁, eB, mul24]
      and_intros <;> first
        | addr_omega [hb, hS, hss, hPA, hB, hlt]
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hS ?_ ?_ ?_ <;> addr_omega [hS])
        | (refine Region.valid hP ?_ ?_ ?_ <;> addr_omega [hP])
        | (refine Region.valid hB ?_ ?_ ?_ <;> addr_omega [hB, hlt]))
  have k₂ := b8000c74c_keeps h₂
  have x10₂ : u₁.getReg .x10 = s.getReg .x11 + 8 := by rw [b8000c74c_x10 h₂, x11₁]
  have x11₂ : u₁.getReg .x11 = s.getReg .x2 - 64 := by rw [b8000c74c_x11 h₂, x2₁]
  have x12₂ := b8000c74c_x12 h₂
  have x2₂ : u₁.getReg .x2 = s.getReg .x2 - 64 := by rw [k₂ .x2 (by decide), x2₁]
  have x8₂ : u₁.getReg .x8 = s.getReg .x10 := by rw [k₂ .x8 (by decide), x8₁]
  have x9₂ := b8000c74c_x9 h₂
  have x18₂ := b8000c74c_x18 h₂
  have x19₂ := b8000c74c_x19 h₂
  have v0 := b8000c74c_m_x2_0 h₂
  have v8 := b8000c74c_m_x2_8 h₂
  have v16 := b8000c74c_m_x2_16 h₂
  have mo := b8000c74c_m_x11_344 h₂
  rw [x12₁, x13₁, eB, mul24] at x9₂ x18₂ x19₂ v0 v8 v16
  rw [x2₁] at v0 v8 v16
  rw [x11₁, x12₁] at mo
  have e0 := eE 0 (by decide) (by decide)
  rw [Sym.add_zero_lit] at e0
  rw [e0] at x9₂ v0
  rw [eE 8 (by decide) (by decide)] at x18₂ v8
  rw [eE 16 (by decide) (by decide)] at x19₂ v16
  have fr₂ (y : Word) (hy : ¬ Within y (s.getReg .x2 - 64) 24) (hy' : y ≠ s.getReg .x11 + 344) :
      u₁.getMem y = t₁.getMem y :=
    h₂.frame y (by
      rv_eval [x2₁, x11₁]
      and_intros <;> addr_omega [hy, hy', hb])
  have W₂ : DFrame s u₁ (fun a ↦ Within a (s.getReg .x10) 32 ∨ Within a (s.getReg .x11 + 8) 344 ∨
      Within a (stackLo s nextScalarStack) nextScalarStack) :=
    W₁.trans (fun y hy ↦ fr₂ y (fun h ↦ hy 0 (by decide) (Or.inr (Or.inr (by
      rw [add_ofNat_zero]; addr_omega [h, hb])))) (fun h ↦ hy 0 (by decide) (Or.inr (Or.inl (by
      rw [add_ofNat_zero, h]; addr_omega [hS]))))) fun _ h ↦ h
  have hap : AbsorbPre u₁ := {
    sponge := by rw [x10₂]; addr_omega [hS]
    value := by rw [x11₂]; addr_omega [hpre.stack.mapped (by decide) (by decide), hb]
    stack := hpre.stack.sub 64 x2₂ (by simp only [nextScalarStack]; omega) (by decide)
      (by decide) (by decide) (by decide)
    spongeStack := by rw [x10₂]; simp only [stackLo, x2₂]; addr_omega [hb, hss, hS]
    valueStack := by rw [x11₂]; simp only [stackLo, x2₂]; addr_omega [hb]
    valueSponge := by rw [x11₂, x10₂]; addr_omega [hb, hss, hS]
    rodata := hpre.rodata.dframe W₂ fun a ha hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hro, hb, hpre.outRodata, hpre.selfRodata, hS]
    spongeRodata := by rw [x10₂]; addr_omega [hpre.selfRodata, hS] }
  obtain ⟨w, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hA.call (hr₁.trans hr₂) (b8000c74c_pc h₂) hap
  swap
  · exact ⟨_, hr₃, Or.inr hd⟩
  have val₃ := hpost₃.value
  rw [x10₂, x11₂, x12₂] at val₃
  have G₃ : DFrame u₁ w (fun a ↦ Within a (s.getReg .x11 + 8) 336 ∨
      Within a (stackLo s nextScalarStack) (nextScalarStack - 64)) :=
    hpost₃.frame.mono fun a ha ↦ by
      rw [x10₂] at ha
      simp only [stackLo, x2₂] at ha
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (by addr_omega [ha, hb])
  -- the high limbs
  have x8₃ : w.getReg .x8 = s.getReg .x10 := by rw [hpres₃.reg .x8, x8₂]
  obtain ⟨v, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c794_spec
    (by rw [hpc₃, returnAddress_eq, b8000c74c_x1 h₂]; decide) (by
      rv_eval [x8₃]
      and_intros <;> (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
  have k₄ := b8000c794_keeps h₄
  have m24 := b8000c794_m_x8_24 h₄
  have m16 := b8000c794_m_x8_16 h₄
  have f₄ := b8000c794_frame h₄ (by rw [x8₃]; addr_omega [ho])
  rw [x8₃, hpres₃.reg .x19, x19₂] at m24
  rw [x8₃, hpres₃.reg .x18, x18₂] at m16
  rw [x8₃] at f₄
  have slot (y : Word) (h1 : (s.getReg .x2).toNat - 40 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem y = t₁.getMem y := by
    rw [f₄ y (by addr_omega [h1, h2, hb, hos, ho]),
      G₃ y fun i hi h ↦ by rcases h with h | h <;> addr_omega [h, hi, h1, h2, hb, hss, hS],
      fr₂ y (by addr_omega [h1, h2, hb]) (by addr_omega [h1, h2, hb, hss, hS])]
  obtain ⟨t, hr₅, pc, pres, m0, m8, f⟩ := exit hpre (b8000c794_pc h₄)
    (by rw [k₄ .x2 (by decide), hpres₃.reg .x2, x2₂]) (by rw [k₄ .x8 (by decide), x8₃])
    (fun r hr ↦ by
      rw [k₄ r (mem_of_mem hr _), hpres₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
        k₁ r (mem_of_mem hr _)])
    (by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), sl₄])
    (by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), sl₃])
    (by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), sl₂])
    (by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), sl₁])
    (by rw [slot _ (by addr_omega [hb]) (by addr_omega [hb]), sl₀])
  have G₃' : DFrame u₁ w (fun a ↦ Within a (s.getReg .x10) 32 ∨
      Within a (s.getReg .x11 + 8) 344 ∨ Within a (stackLo s nextScalarStack) nextScalarStack) :=
    G₃.mono fun a h ↦ by
      rcases h with h | h
      · exact Or.inr (Or.inl (by addr_omega [h, hS]))
      · exact Or.inr (Or.inr (by addr_omega [h, hb]))
  have F₄ : DFrame w v (fun a ↦ Within a (s.getReg .x10) 32 ∨
      Within a (s.getReg .x11 + 8) 344 ∨ Within a (stackLo s nextScalarStack) nextScalarStack) :=
    (DFrame.of_memFrame f₄).mono fun a h ↦ Or.inl (by addr_omega [h, ho])
  have F₅ : DFrame v t (fun a ↦ Within a (s.getReg .x10) 32 ∨
      Within a (s.getReg .x11 + 8) 344 ∨ Within a (stackLo s nextScalarStack) nextScalarStack) :=
    (DFrame.of_memFrame f).mono fun a h ↦ Or.inl (by addr_omega [h, ho])
  have hF : DFrame s t (fun a ↦ Within a (s.getReg .x10) 32 ∨
      Within a (s.getReg .x11 + 8) 344 ∨ Within a (stackLo s nextScalarStack) nextScalarStack) :=
    ((W₂.trans G₃' fun _ h ↦ h).trans F₄ fun _ h ↦ h).trans F₅ fun _ h ↦ h
  have hw : spongeAt t (s.getReg .x11 + 8) = spongeAt w (s.getReg .x11 + 8) :=
    spongeAt_congr (by addr_omega [hS]) fun y h1 h2 ↦ by
      rw [f y (by addr_omega [h1, h2, hosf, hS, ho]), f₄ y (by addr_omega [h1, h2, hosf, hS, ho])]
  have hu : spongeAt u₁ (s.getReg .x11 + 8) = spongeAt s (s.getReg .x11 + 8) :=
    spongeAt_congr (by addr_omega [hS]) fun y h1 h2 ↦ by
      rw [fr₂ y (by addr_omega [h1, h2, hss, hb, hS]) (by addr_omega [h1, h2, hS]),
        f₁ y (by addr_omega [h1, h2, hss, hb, hS])]
  have hoff : t.getMem (s.getReg .x11 + 344) = s.getMem (s.getReg .x11 + 344) + 1 := by
    rw [f _ (by addr_omega [hosf, hS, ho]), f₄ _ (by addr_omega [hosf, hS, ho]),
      G₃ _ fun i hi h ↦ by rcases h with h | h <;> addr_omega [h, hi, hS, hss, hb], mo]
  refine ⟨t, (hr₃.trans hr₄).trans hr₅, Or.inl ⟨pc, pres, ?_, hF⟩⟩
  intro T hT
  have hlen : T.proof.stream.length = streamLen s (s.getReg .x11) := by
    rw [← hT.stream, eListAt_length]
  have hT4 := hT.streamOffset
  have hx : T.proof.stream[T.streamOffset]? = some (eAt s (s.getMem (s.getMem (s.getReg .x11) + 8) +
      BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x11 + 344)).toNat))) := by
    rw [← hT.stream, ← hT4, List.getElem?_eq_getElem (by
      rw [eListAt_length]; simp only [streamLen, proofAt, vecLen]; omega), eListAt_getElem]
    rfl
  rw [nextScalar_some hx]
  have a16 : s.getReg .x10 + 8 + 8 = s.getReg .x10 + 16 := by rw [BitVec.add_assoc]; rfl
  have a24 : s.getReg .x10 + 8 + 16 = s.getReg .x10 + 24 := by rw [BitVec.add_assoc]; rfl
  refine ⟨by rw [m0, b8000c794_x10 h₄], ?_, ?_⟩
  · unfold Rv64Verifier.eAt
    rw [m8, k₄ .x9 (by decide), hpres₃.reg .x9, x9₂, a16, a24,
      f _ (by addr_omega [ho]), f _ (by addr_omega [ho]), m16, m24]
  · have hP' : ProofApart s (s.getReg .x11) (s.getReg .x11 + 8) 344 := hPA
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hT.stream]
      exact hF.eListAt_stream
        (fun i hi h ↦ by rcases h with h | h | h <;> addr_omega [h, hi, hosf, hss, hS, hb])
        (fun i hi h ↦ by rcases h with h | h | h <;> addr_omega [h, hi, hpo, hps, hPA, hP, hb])
        (fun i hi h ↦ by rcases h with h | h | h <;> addr_omega [h, hi, hpo, hps, hPA, hB, hb])
    · rw [hw, val₃, hu, hT.sponge]
      have e : eAt u₁ (s.getReg .x2 - 64) = eAt s (s.getMem (s.getMem (s.getReg .x11) + 8) +
          BitVec.ofNat 64 (24 * (s.getMem (s.getReg .x11 + 344)).toNat)) := by
        unfold Rv64Verifier.eAt
        rw [v0, v8, v16]
      rw [e]
      rfl
    · rw [hoff, ← hT4]
      have : (s.getMem (s.getReg .x11 + 344)).toNat + 1 < 2 ^ 64 := by
        have := (s.getMem (s.getMem (s.getReg .x11) + 16)).isLt; omega
      rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl, Nat.mod_eq_of_lt this]
    · rw [← hT.openingOffset, hF _ fun i hi h ↦ by
        rcases h with h | h | h <;> addr_omega [h, hi, hosf, hss, hS, hb]]

end Rv64Verifier.Transcript.NextScalar
