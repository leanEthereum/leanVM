import Rv64Verifier.Proofs.Pcs.RingSwitchBase

/-!
# `ring_switch`: the prologue and `samples`

See `RingSwitchBase.lean` for the code's layout. `prologue` runs `0x80009754` and the call to
`samples`, to `AtB`: the challenges in the `Vec` at `F + 56`, the transcript standing for the
mirror's after `TM.samples 6`.
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19),
  (48, .x20), (56, .x21), (64, .x22), (72, .x23), (80, .x24), (88, .x25), (96, .x26), (104, .x27)]

/-- What the function writes up to its loops: the sponge, its stack, `NEXT`. -/
def W0 (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x14 + 8) 344 ∨ Within a (s.getReg .x2 - 1584) 1584 ∨ Within a nextAddr 8

/-- At `0x800097b4`, `samples` returned. -/
structure AtB (s B : MachineState) : Prop where
  pc : B.pc = 0x800097b4
  sp : B.getReg .x2 = s.getReg .x2 - 464
  x8 : B.getReg .x8 = 6
  x9 : B.getReg .x9 = s.getReg .x13
  x19 : B.getReg .x19 = s.getReg .x10
  x23 : B.getReg .x23 = s.getReg .x11
  heap : HeapOk B
  mono : heapNext s ≤ heapNext B
  frame : DFrame s B fun a ↦ W0 s a ∨ Fresh s B a
  sP : B.getMem (s.getReg .x2 - 448) = s.getReg .x12
  slots : ∀ p ∈ slots, B.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2
  vec : VecOk B (s.getReg .x2 - 408) 24 8
  buf : NewBuf s B (vecPtr B (s.getReg .x2 - 408)) ((vecCap B (s.getReg .x2 - 408)).toNat * 24) 8
  len : vecLen B (s.getReg .x2 - 408) = 6
  value : ∀ T, TranscriptAt s (s.getReg .x14) T → ∃ T',
    (Model.TM.samples 6).run T = some (vecEs B (s.getReg .x2 - 408), T') ∧
      TranscriptAt B (s.getReg .x14) T'

theorem prologue (hS : SamplesSpec) {s : MachineState} (hpc : s.pc = 0x80009754)
    (hpre : RingSwitchPre s) :
    ∃ B, Reaches Image.code s B ∧ (Dead Image.code B ∨ AtB s B) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hheap := hpre.heap
  have hTi := hpre.self
  have hok := hTi.ok
  have hP := Region.bounds hok.self
  simp only [transcriptSize] at hP
  have hQ := Region.bounds hok.proof
  have hTS := hTi.stack
  have hPS := hTi.proofStack
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009754_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have hm₁ := b80009754_frame h₁ (by omega)
  have hsp₁ : c.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 464 := b80009754_x2 h₁
  have hx10 := b80009754_x10 h₁
  have hx11 := b80009754_x11 h₁
  have hf₁ := DFrame.of_memFrame hm₁
  have hmiss₁ (x : Word) (hx : x.toNat < (s.getReg .x2).toNat - 1584 ∨
      (s.getReg .x2).toNat ≤ x.toNat) : ¬ Within x (s.getReg .x2 - 448) 448 := by
    addr_omega [hx, hb]
  obtain ⟨hpr, hsptr, hslen⟩ := hf₁.stream (p := s.getReg .x14)
    (fun i hi ↦ hmiss₁ _ (by addr_omega [hP, hi, hTS, hb]))
    (fun i hi ↦ hmiss₁ _ (by addr_omega [hQ, hi, hPS.1, hb]))
  have hnx₁ : heapNext c = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hb])]
  have hsl : stackLo c samplesStack = s.getReg .x2 - 1424 := by
    simp only [stackLo, samplesStack, duplexStack, keccakFStack, memStack, hsp₁, Nat.reduceAdd]
    rv_eval []
  have hfree := hTi.free
  have hpfree := hTi.proofFree
  have hsfree := hTi.streamFree
  simp only [Outside] at hfree hpfree hsfree
  have hpreS : SamplesPre c := {
    heap := ⟨hnx₁ ▸ hheap.lo, hnx₁ ▸ hheap.hi⟩
    out := by rw [hx10]; simp only [Region, Mapped]; addr_omega [hb]
    self := by
      rw [hx11]
      refine ⟨hok.self, by rw [hpr]; exact hok.proof, by rw [hsptr, hslen]; exact hok.stream, ?_⟩
      simp only [ProofApart, hpr, hsptr, hslen]; exact hok.apart
    stack := hst.sub 464 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [hx10, hsl]; addr_omega [hb]
    selfStack := by rw [hx11, hsl]; addr_omega [hTS, hb]
    outSelf := by rw [hx10, hx11]; addr_omega [hTS, hb]
    proofStack := by
      rw [hx11, hsl]; simp only [ProofApart, hpr, hsptr, hslen]
      exact ⟨by addr_omega [hPS.1, hb], by addr_omega [hPS.2, hb]⟩
    proofOut := by
      rw [hx11, hx10]; simp only [ProofApart, hpr, hsptr, hslen]
      exact ⟨by addr_omega [hPS.1, hb], by addr_omega [hPS.2, hb]⟩
    outFree := by rw [hx10]; simp only [Outside, hnx₁]; addr_omega [hb]
    selfFree := by rw [hx11]; simp only [Outside, hnx₁]; exact hfree
    proofFree := by rw [hx11]; simp only [Outside, hnx₁, hpr]; exact hpfree
    streamFree := by rw [hx11]; simp only [Outside, hnx₁, hsptr, hslen]; exact hsfree
    rodata := hpre.rodata.frame hm₁ (by addr_omega [hb])
    outRodata := by rw [hx10]; addr_omega [hb]
    selfRodata := by rw [hx11]; exact hTi.rodata }
  obtain ⟨B, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hS.call hr₁ (b80009754_pc h₁) hpreS
  swap
  · exact ⟨B, hr₂, Or.inl hdead⟩
  have hfB := hpost₂.heap.hi
  have hfr₂ := hpost₂.frame
  simp only [TFrame] at hfr₂
  rw [hx10, hx11, hsl] at hfr₂
  have keepB (a : Word) (h1 : (s.getReg .x2).toNat - 448 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 408 ∨ (s.getReg .x2).toNat - 384 ≤ a.toNat) :
      B.getMem a = c.getMem a :=
    hfr₂ a fun i hi hX ↦ by
      rcases hX with hX | hX | hX | hX | hX
      · addr_omega [hX, hi, h1, h2, h3, hb]
      · addr_omega [hX, hi, h1, h2, hTS, hP, hb]
      · addr_omega [hX, hi, h1, h2, hb]
      · addr_omega [hX, hi, h1, h2, hb]
      · simp only [Fresh] at hX; addr_omega [hX.2, hi, h1, h2, hfB, hb]
  have h6 : (c.getReg .x12).toNat = 6 := by rw [b80009754_x12 h₁]; rfl
  have hval := hpost₂.value
  rw [hx10, hx11, h6] at hval
  have hT (T : Model.TState) (hT : TranscriptAt s (s.getReg .x14) T) :
      TranscriptAt c (s.getReg .x14) T :=
    transcriptAt_frame hf₁ hT hok (fun x hx ↦ hmiss₁ _ (by addr_omega [hx, hTS, hb]))
      (fun x hx ↦ hmiss₁ _ (by addr_omega [hx, hQ, hPS.1, hb]))
      (fun x hx ↦ hmiss₁ _ (by addr_omega [hx, hPS.2, hb]))
  obtain ⟨T₀, hT₀⟩ := exists_T s (s.getReg .x14)
  obtain ⟨xs, T₀', hrun₀, hnv₀, -⟩ := hval T₀ (hT T₀ hT₀)
  have hl₀ := Model.Returns.samples 6 _ _ _ hrun₀
  have hel := hnv₀.elems
  refine ⟨B, hr₂, Or.inr {
    pc := by rw [hpc₂, returnAddress_eq, b80009754_x1 h₁]; decide
    sp := (hpres₂.reg .x2).trans hsp₁
    x8 := (hpres₂.reg .x8).trans (b80009754_x8 h₁)
    x9 := (hpres₂.reg .x9).trans (b80009754_x9 h₁)
    x19 := (hpres₂.reg .x19).trans (b80009754_x19 h₁)
    x23 := (hpres₂.reg .x23).trans (b80009754_x23 h₁)
    heap := hpost₂.heap
    mono := hnx₁ ▸ hpost₂.mono
    frame := ?_
    sP := by
      rw [keepB _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]),
        b80009754_m_x2_n448 h₁]
    slots := ?_
    vec := hnv₀.vec
    buf := by have := hnv₀.buf; simp only [NewBuf] at this ⊢; rw [← hnx₁]; exact this
    len := by
      apply BitVec.eq_of_toNat_eq
      have := congrArg List.length hel
      rw [hl₀, vecEs, eListAt_length] at this
      rw [this]; rfl
    value := fun T hTs ↦ by
      obtain ⟨xs', T', hrun, hnv, hT'⟩ := hval T (hT T hTs)
      exact ⟨T', by rw [hnv.elems]; exact hrun, hT'⟩ }⟩
  · refine (hf₁.mono (w' := fun a ↦ W0 s a ∨ Fresh s B a) fun a ha ↦
      Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb])))).trans hfr₂ fun a ha ↦ ?_
    rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb])))
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb])))
    · exact Or.inl (Or.inr (Or.inr ha))
    · exact Or.inr (by simp only [Fresh, hnx₁] at ha ⊢; exact ha)
  · simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    rv_eval []
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [keepB _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])]
    exacts [b80009754_m_x2_n8 h₁, b80009754_m_x2_n16 h₁, b80009754_m_x2_n24 h₁,
      b80009754_m_x2_n32 h₁, b80009754_m_x2_n40 h₁, b80009754_m_x2_n48 h₁,
      b80009754_m_x2_n56 h₁, b80009754_m_x2_n64 h₁, b80009754_m_x2_n72 h₁,
      b80009754_m_x2_n80 h₁, b80009754_m_x2_n88 h₁, b80009754_m_x2_n96 h₁,
      b80009754_m_x2_n104 h₁]

end Rv64Verifier.Proofs.Pcs.RingSwitch
