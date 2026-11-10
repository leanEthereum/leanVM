import Rv64Verifier.Proofs.Pcs.VsoLamPowers
import Rv64Verifier.Proofs.Pcs.VsoTailModel

/-!
# `verify_stacked_opening`'s level loop: the query grinding

`grind_check(QUERY_GRINDING_BITS)` inlined at `0x8000a790`: `Err(3)` if the stream is exhausted
(`0x8000b858`), else the nonce is copied to `S - 384`, the stream offset advanced, the nonce
absorbed with tag `4` (`absorb`) and the sponge permuted (`duplex`); `0x8000a80c` checks the low
`17` bits of the state's first lane, and on a nonzero one a checked transcript returns `Err(4)`
(`0x8000a828`). The mirror is `TM.grind 17`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen

theorem v4of8 {a : Word} (h : Sym.validAccess 8 a = true) : Sym.validAccess 4 a = true := by
  simp only [Sym.validAccess, isValidDwordAccess_eq, isValidMemAccess, Bool.and_eq_true, isAligned8,
    isAligned4, beq_iff_eq] at h ⊢
  exact ⟨h.1, by omega⟩

theorem v1of8 {a : Word} (h : Sym.validAccess 8 a = true) : Sym.validAccess 1 a = true := by
  simp only [Sym.validAccess, isValidDwordAccess_eq, isValidByteAccess, Bool.and_eq_true] at h ⊢
  exact h.1

theorem lw_mul47 (w : Word) :
    (extractWord32 w (0 / 4)).signExtend 64 * 140737488355328 = 0 ↔ w.toNat % 2 ^ 17 = 0 := by
  have h1 : ((extractWord32 w (0 / 4)).signExtend 64 * 140737488355328).toNat =
      ((extractWord32 w 0).signExtend 64).toNat * 2 ^ 47 % 2 ^ 64 := by
    rw [BitVec.toNat_mul]; rfl
  have h2 : (extractWord32 w 0).toNat = w.toNat % 2 ^ 32 := by
    simp [extractWord32]
  have h3 := BitVec.toNat_signExtend (v := 64) (extractWord32 w 0)
  rw [BitVec.toNat_setWidth, h2] at h3
  rw [← BitVec.toNat_inj, h1, h3]
  show _ = (0 : BitVec 64).toNat ↔ _
  rw [show (0 : BitVec 64).toNat = 0 from rfl]
  split <;> omega

theorem lw_shl47 (w : Word) :
    (extractWord32 w 0).signExtend 64 <<< 47 = 0 ↔ w.toNat % 2 ^ 17 = 0 := by
  have h1 : ((extractWord32 w 0).signExtend 64 <<< 47).toNat =
      ((extractWord32 w 0).signExtend 64).toNat * 2 ^ 47 % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have h2 : (extractWord32 w 0).toNat = w.toNat % 2 ^ 32 := by
    simp [extractWord32]
  have h3 := BitVec.toNat_signExtend (v := 64) (extractWord32 w 0)
  rw [BitVec.toNat_setWidth, h2] at h3
  rw [← BitVec.toNat_inj, h1, h3]
  show _ = (0 : BitVec 64).toNat ↔ _
  rw [show (0 : BitVec 64).toNat = 0 from rfl]
  split <;> omega

/-- The transcript's checked byte is `1`, kept by the function's invariant. -/
theorem checked_one {s u : MachineState} {nx : Word} (hpre : VsoPre s) (hinv : InvR s u nx) :
    extractByte (u.getMem (s.getReg .x10 + 360)) 0 = 1 := by
  have hS := Region.bounds hpre.self.ok.self
  have hst := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hst
  have hf := hpre.self.free
  simp only [Outside] at hf
  have hrs := hpre.rootSelf
  have hfit := hinv.fits
  have e : u.getMem (s.getReg .x10 + 360) = s.getMem (s.getReg .x10 + 360) :=
    hinv.mem.word (fun x hx hW ↦ by
      rcases hW with (hW | hW) | hW | hW | ⟨hW1, hW2⟩
      · simp only [W] at hW; addr_omega [hx, hW, hS]
      · addr_omega [hx, hW, hrs, hS]
      · rw [stackLo_vso, vso_stack] at hW; addr_omega [hx, hW, hst, hS]
      · addr_omega [hx, hW, hf.2, hS]
      · rcases hf.1 with h1 | h1
        · addr_omega [hx, hW1, h1, hS]
        · addr_omega [hx, hW2, h1, hS, hfit]) (by addr_omega [hS])
  rw [e]
  have h := hpre.checked
  rwa [← add_ofNat_zero (s.getReg .x10 + 360), byteAt_add (by addr_omega [hS]) (by decide)] at h

/-- An `Err` at `0x8000b844` (its discriminant in `ra`), to the exit. -/
theorem fail844 {s t : MachineState} {nx : Word} (hinv : InvR s t nx) (hpc : t.pc = 0x8000b844)
    (hne : t.getReg .x1 ≠ okTag) : ∃ w, Reaches Image.code t w ∧ FailR s w := by
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000b844_spec hpc trivial
  obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000b84c_spec (b8000b844_pc h1) trivial
  refine ⟨t2, r1.trans r2, Or.inr ⟨b8000b84c_pc h2, by rw [b8000b84c_x10 h2, b8000b844_x22 h1]; exact hne,
    nx, Inv.same' hinv (fun a ↦ by rw [b8000b84c_mem_same h2, b8000b844_mem_same h1])
      (by rw [b8000b84c_keeps h2 .x2 (by decide), b8000b844_keeps h1 .x2 (by decide)])⟩⟩

/-- A frame that writes only the sponge and offsets and the stack: the transcript stands for `T`
with the sponge and offsets read off memory. -/
theorem tr_frame {s u v : MachineState} {nx : Word} {T : Model.TState} {X : Word → Prop}
    (hpre : VsoPre s) (hinv : InvR s u nx) (hT : TranscriptAt u (s.getReg .x10) T)
    (hX : DFrame u v X) (hXs : ∀ a, X a → W s a ∨ Within a (s.getReg .x2 - 2464) 2464) :
    TranscriptAt v (s.getReg .x10)
      { T with
        sponge := spongeAt v (s.getReg .x10 + 8)
        streamOffset := (v.getMem (s.getReg .x10 + 344)).toNat
        openingOffset := (v.getMem (s.getReg .x10 + 352)).toNat } := by
  have hb := bounds hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  have hPs := hI.proofStack
  rw [stackLo_vso, vso_stack] at hIs hPs
  obtain ⟨-, e0, e1, e2⟩ := trR_facts hpre hinv
  have hpa := hpre.proofSponge
  simp only [ProofApart] at hpa hPs
  have hP := Region.bounds hI.ok.proof
  have hB : streamLen s (s.getReg .x10) = 0 ∨
      (streamPtr s (s.getReg .x10)).toNat + 24 * streamLen s (s.getReg .x10) ≤ 2 ^ 64 := by
    rcases hI.ok.stream with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by have := Region.bounds h0; omega)
  refine ⟨?_, rfl, rfl, rfl⟩
  rw [← hT.stream]
  apply hX.eListAt_stream
  · intro i hi hw
    rcases hXs _ hw with hw | hw
    · simp only [W] at hw; addr_omega [hw, hi, hS]
    · addr_omega [hw, hi, hS, hIs, hb]
  · rw [e0]; intro i hi hw
    rcases hXs _ hw with hw | hw
    · simp only [W] at hw; addr_omega [hw, hi, hpa.1, hP, hS]
    · addr_omega [hw, hi, hPs.1, hP, hb]
  · rw [e1, e2]; intro i hi hw
    rcases hB with h0 | h0
    · rw [h0] at hi; omega
    rcases hXs _ hw with hw | hw
    · simp only [W] at hw; addr_omega [hw, hi, hpa.2, h0, hS]
    · addr_omega [hw, hi, hPs.2, h0, hb]

/-! ## `Sponge::absorb` -/

theorem callAbsorb (hA : AbsorbSpec) {s t : MachineState} {nx : Word} (hpre : VsoPre s)
    (hinv : InvR s t nx) (hpc : t.pc = 0x8000c808) (hx10 : t.getReg .x10 = s.getReg .x10 + 8)
    (hx11 : t.getReg .x11 = s.getReg .x2 - 384) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      DFrame t v (fun a ↦ Within a (s.getReg .x10 + 8) 336 ∨
        Within a (s.getReg .x2 - 1952) 912) ∧
      spongeAt v (s.getReg .x10 + 8) = spAbsorb (spongeAt t (s.getReg .x10 + 8))
        (eAt t (s.getReg .x2 - 384)) (t.getReg .x12).toNat)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hsp := hinv.sp
  have hsl : stackLo t absorbStack = s.getReg .x2 - 1952 := by
    simp only [stackLo, absorbStack, duplexStack, keccakFStack, memStack, hsp, Nat.reduceAdd]
    rv_eval []
  have hpreA : AbsorbPre t := {
    sponge := by rw [hx10]; exact region_sub hI.ok.self 8 336 (by decide) (by decide)
    value := by
      rw [hx11]; exact stack_region hpre (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    spongeStack := by rw [hx10, hsl]; addr_omega [hIs, hS, hb]
    valueStack := by rw [hx11, hsl]; addr_omega [hb]
    valueSponge := by rw [hx11, hx10]; addr_omega [hIs, hS, hb]
    rodata := hinv.rodata' hpre
    spongeRodata := by rw [hx10]; have := hI.rodata; addr_omega [this, hS] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hA.call (Reaches.refl t) hpc hpreA
  · have hfr := hpost.frame
    have hval := hpost.value
    rw [hx10, hsl] at hfr
    rw [hx10, hx11] at hval
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hfr, hval⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-! ## The grinding -/

/-- What the grinding writes: the sponge and offsets, the callees' stacks, the spills at
`S - 968`, `S - 960` and the nonce at `S - 384`. -/
def GW (s : MachineState) (a : Word) : Prop :=
  W s a ∨ Within a (s.getReg .x2 - 2464) 1424 ∨ Within a (s.getReg .x2 - 968) 16 ∨
    Within a (s.getReg .x2 - 384) 24

/-- At `0x8000a82c`, the nonce accepted, from `u` on the transcript `T`. -/
structure GrindOut (s u w : MachineState) (T : Model.TState) : Prop where
  pc : w.pc = 0x8000a82c
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s w (w.getMem nextAddr)
  fr : DFrame u w (GW s)
  nx : w.getMem nextAddr = u.getMem nextAddr
  regs : ∀ r ∈ [Reg.x9, .x18, .x19, .x21, .x22, .x24, .x25, .x26, .x27], w.getReg r = u.getReg r
  x8 : w.getReg .x8 = s.getReg .x10 + 8
  x20 : w.getReg .x20 = s.getReg .x10
  x23 : w.getReg .x23 = u.getMem (s.getReg .x2 - 808)
  s72 : w.getMem (s.getReg .x2 - 968) = u.getReg .x1
  s80 : w.getMem (s.getReg .x2 - 960) = u.getReg .x31
  tr : ∃ T', (Model.TM.grind Model.Pcs.queryGrindingBitsRust).run T = some ((), T') ∧
    TranscriptAt w (s.getReg .x10) T' ∧ T'.proof = T.proof ∧ T'.roots = T.roots ∧
    T'.openingOffset = T.openingOffset

/-- **The grinding**, from `0x8000a790` to `0x8000a82c`, or an `Err`. -/
theorem grind (hD : DuplexSpec) (hA : AbsorbSpec) {s u : MachineState} {T : Model.TState}
    (hpre : VsoPre s) (hinv : InvR s u (u.getMem nextAddr)) (hpc : u.pc = 0x8000a790)
    (h224 : u.getMem (s.getReg .x2 - 816) = s.getReg .x10)
    (h248 : u.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8)
    (hT : TranscriptAt u (s.getReg .x10) T) :
    ∃ w, Reaches Image.code u w ∧ (FailR s w ∨ GrindOut s u w T) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  have hPs := hI.proofStack
  rw [stackLo_vso, vso_stack] at hIs hPs
  simp only [ProofApart] at hPs
  have hsp : u.getReg .x2 = s.getReg .x2 - 1040 := hinv.sp
  obtain ⟨hTok, e0, e1, e2⟩ := trR_facts hpre hinv
  rw [← e0, ← e1, ← e2] at hPs
  have hP := Region.bounds hTok.proof
  have q224 : u.getMem (u.getReg .x2 + 224) = s.getReg .x10 := by rw [hsp]; rv_eval [h224]
  have hoff : (u.getMem (s.getReg .x10 + 344)).toNat = T.streamOffset := hT.streamOffset
  have hlen : streamLen u (s.getReg .x10) = T.proof.stream.length := by
    rw [← hT.stream, eListAt_length]
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a790_spec hpc (by
    rv_eval [hsp, h224]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hI.ok.self (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS])
      | exact Region.valid hTok.proof (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP]))
  have k₁ := b8000a790_keeps h₁
  have hm₁ := b8000a790_mem_same h₁
  by_cases hlt : T.streamOffset < T.proof.stream.length
  swap
  · have hpc₁ := b8000a790_pc_not_taken h₁ (by
      rw [q224]; simp only [streamLen, vecLen, proofAt] at hlen; omega)
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a7ac_spec hpc₁ trivial
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000b858_spec (b8000a7ac_pc h₂) trivial
    have inv₃ : InvR s t₃ (u.getMem nextAddr) := Inv.same' hinv
      (fun a ↦ by rw [b8000b858_mem_same h₃, b8000a7ac_mem_same h₂, hm₁])
      (by rw [b8000b858_keeps h₃ .x2 (by decide), b8000a7ac_keeps h₂ .x2 (by decide),
        k₁ .x2 (by decide)])
    obtain ⟨w, hw, hf⟩ := fail844 inv₃ (b8000b858_pc h₃) (by rw [b8000b858_x1 h₃]; decide)
    exact ⟨w, hr₁.trans (hr₂.trans (hr₃.trans hw)), Or.inl hf⟩
  have hpc₁ := b8000a790_pc_taken h₁ (by
    rw [q224]; simp only [streamLen, vecLen, proofAt] at hlen; omega)
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₁ .x2 (by decide), hsp]
  have x8₁ : t₁.getReg .x8 = s.getReg .x10 + 8 := by rw [b8000a790_x8 h₁, hsp]; rv_eval [h248]
  have x10₁ : t₁.getReg .x10 = u.getMem (s.getReg .x10 + 344) := by rw [b8000a790_x10 h₁, q224]
  have x11₁ : t₁.getReg .x11 = u.getMem (s.getReg .x10) := by rw [b8000a790_x11 h₁, q224]
  have x20₁ : t₁.getReg .x20 = s.getReg .x10 := by rw [b8000a790_x20 h₁, q224]
  have hR : Region (streamPtr u (s.getReg .x10)) (24 * streamLen u (s.getReg .x10)) := by
    rcases hTok.stream with h0 | h0
    · omega
    · exact h0
  have hRb := Region.bounds hR
  have hlt' : (u.getMem (s.getReg .x10 + 344)).toNat < streamLen u (s.getReg .x10) := by omega
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a7b0_spec hpc₁ (by
    rv_eval [sp₁, x10₁, x11₁, x20₁, hm₁]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hI.ok.self (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS])
      | exact Region.valid hTok.proof (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP])
      | exact Region.valid hR (by addr_omega [hRb, hlt']) (by addr_omega [hRb, hlt'])
          (by addr_omega [hRb, hlt'])
      | addr_omega [hIs, hS, hb, hPs.1, hPs.2, hRb, hlt', hP])
  have k₂ := b8000a7b0_keeps h₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₂ .x2 (by decide), sp₁]
  have X₂ : DFrame u t₂ fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
      Within a (s.getReg .x2 - 968) 16 ∨ Within a (s.getReg .x10 + 344) 8 :=
    (DFrame.of_same hm₁ _).trans ((holds_dframe h₂).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a7b0, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rv_eval [sp₁, x20₁] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (Or.inl (by addr_omega [hw, hb]))
        | exact Or.inr (Or.inr (by addr_omega [hw, hS]))) fun _ h ↦ h
  have hfS := hI.free.2
  have nx₂ : t₂.getMem nextAddr = u.getMem nextAddr := X₂ _ fun i hi hw ↦ by
    rcases hw with hw | hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hS, hfS]
  have inv₂ : InvR s t₂ (t₂.getMem nextAddr) := by
    rw [nx₂]
    refine Inv.step' hpre hinv X₂ (fun a ha ↦ ?_) (fun a ha ↦ ?_) nx₂ (le_refl _) hinv.fits
      (by rw [sp₂, hsp])
    · rcases ha with ha | ha | ha
      · exact frame_wr hpre (by addr_omega [ha, hb])
      · exact frame_wr hpre (by addr_omega [ha, hb])
      · exact Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hS]))
    · rcases ha with ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hIs, hS, hb]
  have m0 := b8000a7b0_m_x2_656 h₂
  have m1 := b8000a7b0_m_x2_664 h₂
  have m2 := b8000a7b0_m_x2_672 h₂
  have m3 := b8000a7b0_m_x20_344 h₂
  rw [sp₁, x10₁, x11₁] at m0 m1 m2
  rw [x20₁, x10₁] at m3
  simp only [hm₁] at m0 m1 m2
  rv_eval [] at m0 m1 m2
  have ea : u.getMem (u.getMem (s.getReg .x10) + 8) +
      (u.getMem (s.getReg .x10 + 344) * 16 + u.getMem (s.getReg .x10 + 344) * 8) =
      streamPtr u (s.getReg .x10) + BitVec.ofNat 64 (24 * T.streamOffset) := by
    rw [← hoff]; addr_omega [hRb, hlt']
  rw [ea] at m0 m1 m2
  have hget : T.proof.stream[T.streamOffset]? = some (eAt t₂ (s.getReg .x2 - 384)) := by
    rw [← hT.stream, List.getElem?_eq_getElem (by rw [eListAt_length]; omega), eListAt_getElem]
    congr 1
    exact (eAt_congr m0 (by rv_eval [m1]) (by rv_eval [m2])).symm
  have sp0 : spongeAt t₂ (s.getReg .x10 + 8) = T.sponge := by
    rw [← hT.sponge]
    exact spongeAt_congr (by addr_omega [hS]) fun y h1 h2 ↦ X₂ y fun i hi hw ↦ by
      rcases hw with hw | hw | hw
      · addr_omega [hw, hi, h1, h2, hIs, hS, hb]
      · addr_omega [hw, hi, h1, h2, hIs, hS, hb]
      · addr_omega [hw, hi, h1, h2, hS]
  have x12₂ : (t₂.getReg .x12).toNat = 4 := by rw [b8000a7b0_x12 h₂]; rfl
  -- `absorb`
  obtain ⟨t₃, hr₃, hv₃⟩ := callAbsorb hA hpre inv₂ (b8000a7b0_pc h₂)
    (by rw [b8000a7b0_x10 h₂, x8₁]) (by rw [b8000a7b0_x11 h₂, sp₁]; rv_eval [])
  rcases hv₃ with hd | ⟨hpc₃, hpres₃, X₃, hsp₃⟩
  · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl (Or.inl hd)⟩
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres₃ .x2 (by decide), sp₂]
  have nx₃ : t₃.getMem nextAddr = t₂.getMem nextAddr := X₃ _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hS, hfS]
    · addr_omega [hw, hi, hb, hnx]
  have inv₃ : InvR s t₃ (t₃.getMem nextAddr) := by
    rw [nx₃]
    refine Inv.step' hpre inv₂ X₃ (fun a ha ↦ ?_) (fun a ha ↦ ?_) nx₃ (le_refl _) inv₂.fits
      (hpres₃ .x2 (by decide))
    · rcases ha with ha | ha
      · exact Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hS]))
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · rcases ha with ha | ha
      · addr_omega [ha, hS, hIs, hb]
      · addr_omega [ha, hb]
  -- `duplex`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a800_spec
    (by rw [hpc₃, returnAddress_eq, b8000a7b0_x1 h₂]; decide) trivial
  have hm₄ := b8000a800_mem_same h₄
  have k₄ := b8000a800_keeps h₄
  have inv₄ : InvR s t₄ (t₄.getMem nextAddr) := by
    rw [hm₄]; exact Inv.same' inv₃ hm₄ (k₄ .x2 (by decide))
  have x8₃ : t₃.getReg .x8 = s.getReg .x10 + 8 := by
    rw [hpres₃ .x8 (by decide), k₂ .x8 (by decide), x8₁]
  obtain ⟨t₅, hr₅, hv₅⟩ := callDuplex hD hpre inv₄ (b8000a800_pc h₄)
    (by rw [b8000a800_x10 h₄, x8₃])
  rcases hv₅ with hd | ⟨hpc₅, hpres₅, X₅, hsp₅⟩
  · exact ⟨t₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl (Or.inl hd)⟩
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [hpres₅ .x2 (by decide), k₄ .x2 (by decide), sp₃]
  have nx₅ : t₅.getMem nextAddr = t₄.getMem nextAddr := X₅ _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hS, hfS]
    · addr_omega [hw, hi, hb, hnx]
  have inv₅ : InvR s t₅ (t₅.getMem nextAddr) := by
    rw [nx₅]
    refine Inv.step' hpre inv₄ X₅ (fun a ha ↦ ?_) (fun a ha ↦ ?_) nx₅ (le_refl _) inv₄.fits
      (hpres₅ .x2 (by decide))
    · rcases ha with ha | ha
      · exact Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hS]))
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · rcases ha with ha | ha
      · addr_omega [ha, hS, hIs, hb]
      · addr_omega [ha, hb]
  have x20₅ : t₅.getReg .x20 = s.getReg .x10 := by
    rw [hpres₅ .x20 (by decide), k₄ .x20 (by decide), hpres₃ .x20 (by decide),
      k₂ .x20 (by decide), x20₁]
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000a80c_spec
    (by rw [hpc₅, returnAddress_eq, b8000a800_x1 h₄]; decide) (by
      rv_eval [x20₅]
      and_intros <;> first
        | addr_omega [hS]
        | exact v4of8 (Region.valid hI.ok.self (by addr_omega [hS]) (by addr_omega [hS])
            (by addr_omega [hS])))
  have hp₆ := h₆.1
  rv_eval [x20₅] at hp₆
  have hm₆ := b8000a80c_mem_same h₆
  have k₆ := b8000a80c_keeps h₆
  have sp₆ : t₆.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₆ .x2 (by decide), sp₅]
  have inv₆ : InvR s t₆ (t₆.getMem nextAddr) := by
    rw [hm₆]; exact Inv.same' inv₅ hm₆ (k₆ .x2 (by decide))
  have x20₆ : t₆.getReg .x20 = s.getReg .x10 := by rw [k₆ .x20 (by decide), x20₅]
  have hr₁₆ := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))
  by_cases hz : (t₅.getMem (s.getReg .x10 + 136)).toNat % 2 ^ 17 = 0
  swap
  · have hpc₆ : t₆.pc = 0x8000a81c := by
      rw [hp₆]; split
      · rename_i h; exact absurd ((lw_mul47 _).mp (beq_iff_eq.mp h)) hz
      · rfl
    have hbyte := checked_one hpre inv₆
    obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000a81c_spec hpc₆ (by
      rv_eval [x20₆]
      and_intros <;> first
        | addr_omega [hS]
        | exact v1of8 (Region.valid hI.ok.self (by addr_omega [hS]) (by addr_omega [hS])
            (by addr_omega [hS])))
    have hp₇ := h₇.1
    rv_eval [x20₆, hbyte] at hp₇
    obtain ⟨t₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000a828_spec (by rw [hp₇]; rfl) trivial
    have inv₈ : InvR s t₈ (t₆.getMem nextAddr) := Inv.same' inv₆
      (fun a ↦ by rw [b8000a828_mem_same h₈, b8000a81c_mem_same h₇])
      (by rw [b8000a828_keeps h₈ .x2 (by decide), b8000a81c_keeps h₇ .x2 (by decide)])
    obtain ⟨w, hw, hf⟩ := fail844 inv₈ (b8000a828_pc h₈) (by
      rw [b8000a828_keeps h₈ .x1 (by decide), b8000a81c_keeps h₇ .x1 (by decide), b8000a80c_x1 h₆]
      decide)
    exact ⟨w, hr₁₆.trans (hr₇.trans (hr₈.trans hw)), Or.inl hf⟩
  have hpc₆ : t₆.pc = 0x8000a82c := by rw [hp₆, (lw_mul47 _).mpr hz]; rfl
  -- what the grinding wrote, and what it kept
  have X : DFrame u t₆ (GW s) := by
    have X₃' : DFrame u t₃ (GW s) := X₂.mono (fun a ha ↦ by
        rcases ha with ha | ha | ha
        · exact Or.inr (Or.inr (Or.inr ha))
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inl (by simp only [W]; addr_omega [ha, hS])) |>.trans X₃ fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by simp only [W]; addr_omega [ha, hS])
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    have X₅' : DFrame u t₅ (GW s) := (X₃'.trans (DFrame.of_same hm₄ _) fun _ h ↦ h).trans X₅
      fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl (by simp only [W]; addr_omega [ha, hS])
        · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    exact X₅'.trans (DFrame.of_same hm₆ _) fun _ h ↦ h
  have keep {y : Word} (hy1 : (s.getReg .x10 + 344).toNat ≤ y.toNat)
      (hy2 : y.toNat + 8 ≤ (s.getReg .x10).toNat + 368) : t₆.getMem y = t₂.getMem y := by
    rw [hm₆, X₅ y fun i hi hw ↦ ?_, hm₄, X₃ y fun i hi hw ↦ ?_]
    · rcases hw with hw | hw <;> addr_omega [hw, hi, hy1, hy2, hS, hIs, hb]
    · rcases hw with hw | hw <;> addr_omega [hw, hi, hy1, hy2, hS, hIs, hb]
  have spg : spongeAt t₆ (s.getReg .x10 + 8) =
      spDuplex (spAbsorb T.sponge (eAt t₂ (s.getReg .x2 - 384)) 4) := by
    rw [spongeAt_congr (by addr_omega [hS]) fun y _ _ ↦ hm₆ y, hsp₅,
      spongeAt_congr (by addr_omega [hS]) fun y _ _ ↦ hm₄ y, hsp₃, sp0, x12₂]
  have off₆ : (t₆.getMem (s.getReg .x10 + 344)).toNat = T.streamOffset + 1 := by
    rw [keep (Nat.le_refl _) (by addr_omega [hS]), m3]
    addr_omega [hoff, hlt', hRb]
  have opn₆ : (t₆.getMem (s.getReg .x10 + 352)).toNat = T.openingOffset := by
    rw [keep (by addr_omega [hS]) (by addr_omega [hS]), ← hT.openingOffset,
      X₂ _ fun i hi hw ↦ ?_]
    rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hS, hIs, hb]
  have hT₆ := tr_frame hpre hinv hT X fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (by addr_omega [ha, hb])
    · exact Or.inr (by addr_omega [ha, hb])
    · exact Or.inr (by addr_omega [ha, hb])
  rw [spg, off₆, opn₆] at hT₆
  have hpow : Compile.powOk 17 (eAt t₂ (s.getReg .x2 - 384))
      (Compile.challengeOf (spDuplex (spAbsorb T.sponge (eAt t₂ (s.getReg .x2 - 384)) 4)).state) =
      true := by
    rw [← spg]
    show Compile.powOk 17 _ (Compile.challengeOf (stateAt t₆ (s.getReg .x10 + 8 + 128))) = true
    rw [show s.getReg .x10 + 8 + 128 = s.getReg .x10 + 136 by rv_eval [],
      Samples.challengeOf_stateAt]
    simp only [Compile.powOk, Nat.succ_ne_zero, ite_false, decide_eq_true_eq]
    show (t₆.getMem (s.getReg .x10 + 136)).toNat % 2 ^ 17 = 0
    rw [hm₆]
    exact hz
  have hg : (Model.TM.grind Model.Pcs.queryGrindingBitsRust).run T =
      some ((),
        { T with
          streamOffset := T.streamOffset + 1
          sponge := spDuplex (spAbsorb T.sponge (eAt t₂ (s.getReg .x2 - 384)) 4) }) := by
    simp only [StateT.run, Model.TM.grind, hget]
    split
    · rfl
    · rename_i hn; exact absurd hpow hn
  have stk {y : Word} (h1 : (s.getReg .x2 - 1040).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) : t₆.getMem y = t₂.getMem y := by
    rw [hm₆, X₅ y fun i hi hw ↦ ?_, hm₄, X₃ y fun i hi hw ↦ ?_]
    · rcases hw with hw | hw <;> addr_omega [hw, hi, h1, h2, hS, hIs, hb]
    · rcases hw with hw | hw <;> addr_omega [hw, hi, h1, h2, hS, hIs, hb]
  refine ⟨t₆, hr₁₆, Or.inr {
    pc := hpc₆
    sp := sp₆
    inv := inv₆
    fr := X
    nx := by rw [hm₆, nx₅, hm₄, nx₃, nx₂]
    regs := fun r hr ↦ by
      rw [k₆ r (mem_of_mem hr _), hpres₅ r (by simp only [calleeSaved]; exact mem_of_mem hr _),
        k₄ r (mem_of_mem hr _), hpres₃ r (by simp only [calleeSaved]; exact mem_of_mem hr _),
        k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    x8 := by rw [k₆ .x8 (by decide), hpres₅ .x8 (by decide), k₄ .x8 (by decide), x8₃]
    x20 := x20₆
    x23 := by
      rw [k₆ .x23 (by decide), hpres₅ .x23 (by decide), k₄ .x23 (by decide),
        hpres₃ .x23 (by decide), k₂ .x23 (by decide), b8000a790_x23 h₁, hsp]
      rv_eval []
    s72 := by
      rw [stk (by addr_omega [hb]) (by addr_omega [hb])]
      have := b8000a7b0_m_x2_72 h₂
      rw [sp₁, k₁ .x1 (by decide)] at this
      rv_eval [] at this
      exact this
    s80 := by
      rw [stk (by addr_omega [hb]) (by addr_omega [hb])]
      have := b8000a7b0_m_x2_80 h₂
      rw [sp₁, k₁ .x31 (by decide)] at this
      rv_eval [] at this
      exact this
    tr := ⟨_, hg, hT₆, rfl, rfl, rfl⟩ }⟩

end Rv64Verifier.Proofs.Pcs.Vso
