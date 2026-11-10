import Rv64Verifier.Proofs.Walk.New
import Rv64Verifier.Proofs.Runtime.Sub

/-!
# `walk` to its first `next_scalars`

The sponge filled (`spongeStep`), its count and both offsets zeroed, `checked` set (`newStep`):
at `next_scalars`' entry the transcript at `tp` stands for `initT` on every proof the memory holds
(`transcriptAt_init`), and the code runs `prog` from there (`Start.tracks`). `start` composes the
stages from the entry.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem valid1_of_valid8 {a : Word} (h : Sym.validAccess 8 a = true) :
    Sym.validAccess 1 a = true := by
  simp only [Sym.validAccess, isValidDwordAccess_eq, isValidByteAccess_eq, Bool.and_eq_true] at h ⊢
  exact h.1

/-! ## The sponge -/

structure Sponged (s v : MachineState) : Prop where
  inv : Inv s v
  regs : Regs s v
  proofPtr : v.getMem (s.getReg .x2 - 2448) = s.getReg .x13
  state : stateAt v (s.getReg .x2 - 2312) = keccakF1600 (seedState s)

theorem spongeStep (hMC : MemcpySpec 0x800126e4) {s u : MachineState} (hpre : WalkPre s)
    (hpc : u.pc = 0x80001118) (h : Zeroed s u) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = 0x80001130 ∧ Sponged s v) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := h.inv.sp
  obtain ⟨w₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80001118_spec hpc (by
    rv_eval [sp]
    valid_access hval [hb1])
  have k₀ := b80001118_keeps h₀
  have fr₀ := b80001118_frame h₀ (by rw [sp]; addr_omega [hb1])
  have e208 : u.getReg .x2 + 208 = s.getReg .x2 - BitVec.ofNat 64 2448 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e208] at fr₀
  have st₀ : Step s u w₀ (s.getReg .x2 - BitVec.ofNat 64 2448) 8 :=
    Step.ofMemFrame hpre h.inv.heap (inFrame hpre (by omega) (by omega)) fr₀ (k₀ .x2 (by decide))
  have I₀ := h.inv.after hpre (inFrame hpre (by omega) (by omega)) st₀
  have p₀ : w₀.getMem (s.getReg .x2 - BitVec.ofNat 64 2448) = s.getReg .x13 := by
    rw [← e208, b80001118_m_x2_208 h₀, h.x9]
  have x10₀ : w₀.getReg .x10 = s.getReg .x2 - 2440 := by
    rw [b80001118_x10 h₀, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₀ : w₀.getReg .x11 = s.getReg .x2 - 928 := by
    rw [b80001118_x11 h₀, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x12₀ : (w₀.getReg .x12).toNat = 328 := by rw [b80001118_x12 h₀]; rfl
  have hmc : MemcpyPre w₀ := {
    dst := by rw [x10₀, x12₀]; addr_omega [hb1, hb2]
    src := by rw [x11₀, x12₀]; addr_omega [hb1, hb2]
    apart := by rw [x10₀, x11₀, x12₀]; addr_omega [hb1]
    stack := calleeStack hpre I₀ (by decide) (by decide)
    dstStack := by rw [x10₀, x12₀, stackLo_callee I₀]; addr_omega [hb1]
    srcStack := by rw [x11₀, x12₀, stackLo_callee I₀]; addr_omega [hb1] }
  obtain ⟨v, hr₁, ⟨hpc₁, hp₁, post₁⟩ | hd⟩ := hMC.call hr₀ (b80001118_pc h₀) hmc
  swap
  · exact ⟨v, hr₁, Or.inr hd⟩
  have by₁ := post₁.bytes
  have fr₁ := post₁.frame
  rw [x10₀, x11₀, x12₀] at by₁
  rw [x10₀, x12₀] at fr₁
  have st : Step s w₀ v (s.getReg .x2 - BitVec.ofNat 64 2440) 328 :=
    stepOfBytes hpre I₀ (by omega) (by omega) (by decide)
      ((DFrame.of_byteFrame fr₁).mono fun _ ha ↦ ha) (hp₁.reg .x2)
  refine ⟨v, hr₁, Or.inl ⟨by rw [hpc₁, returnAddress_eq, b80001118_x1 h₀]; decide, {
    inv := I₀.after hpre (inFrame hpre (by omega) (by omega)) st
    regs := h.regs.keep fun r hr ↦ by rw [hp₁.reg r (mem_six hr), k₀ r (mem_of_mem hr _)]
    proofPtr := by
      rw [← p₀]
      exact st.word hpre (by addr_omega [hb1]) (by addr_omega [hb1])
    state := ?_ }⟩⟩
  rw [← h.state]
  refine stateAt_congr fun j hj ↦ ?_
  have a1 : s.getReg .x2 - 2312 + BitVec.ofNat 64 (8 * j) =
      s.getReg .x2 - 2440 + BitVec.ofNat 64 (128 + 8 * j) := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
  have a2 : s.getReg .x2 - 800 + BitVec.ofNat 64 (8 * j) =
      s.getReg .x2 - 928 + BitVec.ofNat 64 (128 + 8 * j) := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
  rw [a1, a2, getMem_eq_of_bytesAt by₁ (by addr_omega [hb1, hb3]) (by addr_omega [hb1, hb3])
    (by omega) (by omega)]
  exact st₀.word hpre (by addr_omega [hb1, hj]) (by addr_omega [hb1, hj])

/-! ## `next_scalars`' entry -/

/-- `Sponge::new` of the `Bytecode`'s IV and the public input permutes the seed. -/
theorem seedState_eq {s : MachineState} (hpre : WalkPre s) :
    (spongeNewRust (Proofs.Bytecode.readBytecode s (s.getReg .x11)).fiatShamirIv
      (bytesAt s (s.getReg .x12) 32)) = ⟨keccakF1600 (seedState s), []⟩ := by
  have hbc := hpre.bytecode.mem.self
  have hbcA := hpre.bytecode.mem.align
  have ha : (s.getReg .x11 + 104).toNat % 8 = 0 := by addr_omega [hbc, hbcA]
  have hp := hpre.input.2
  rw [spongeNewRust, seedState]
  refine congrArg (fun x ↦ (⟨keccakF1600 x, []⟩ : Sponge))
    (congrArg Vector.ofFn (funext fun i ↦ ?_))
  simp only [seedWord]
  split_ifs with h1 h2
  · exact congrArg UInt64.ofBitVec (digestWords_bytesAt s ha h1)
  · exact congrArg UInt64.ofBitVec (digestWords_bytesAt s hp (by omega))
  · rfl

/-- At `next_scalars`' entry the transcript at `tp` stands for `initT` on every proof the memory
holds. -/
theorem transcriptAt_init {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} (hpre : WalkPre s) (I : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13)
    (hst : stateAt u (tp s + 8 + 128) = keccakF1600 (seedState s))
    (hnp : u.getMem (tp s + 8 + 328) = 0) (hso : u.getMem (tp s + 344) = 0)
    (hoo : u.getMem (tp s + 352) = 0) {proof : Proof}
    (hp : ProofIn OI s (s.getReg .x13) proof) : TranscriptAt u (tp s) (initT s proof) := by
  have hP := hpre.proof
  have e8 : u.getMem (s.getReg .x13 + 8) = s.getMem (s.getReg .x13 + 8) :=
    I.word hpre.proofRO (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP])
  have e16 : u.getMem (s.getReg .x13 + 16) = s.getMem (s.getReg .x13 + 16) :=
    I.word hpre.proofRO (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP])
  have hR := hpre.stream
  have hRO := hpre.streamRO
  simp only [vecPtr, vecLen] at hR hRO
  refine ⟨?_, ?_, ?_, ?_⟩
  · show eListAt u (vecPtr u (u.getMem (tp s))) (vecLen u (u.getMem (tp s))).toNat = proof.stream
    rw [hptr, vecPtr, vecLen, e8, e16, ← hp.stream]
    refine I.frame.eListAt fun i hi ↦ ?_
    rcases hR with h0 | hR
    · omega
    · exact (I.miss hRO (by addr_omega [hR])) _ (by addr_omega [hR, hi])
  · rw [spongeAt_of_empty hnp, hst]
    exact (seedState_eq hpre).symm
  · rw [hso]; rfl
  · rw [hoo]; rfl

/-- At `next_scalars(8)`'s entry. -/
structure Start (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState) :
    Prop where
  inv : Inv s u
  regs : Regs s u
  x1 : u.getReg .x1 = 0x80001158
  x10 : u.getReg .x10 = s.getReg .x2 - 928
  x11 : u.getReg .x11 = tp s
  x12 : u.getReg .x12 = 8
  proofPtr : u.getMem (tp s) = s.getReg .x13
  checked : byteAt u (tp s + 360) = 1
  tracks : Tracks OI s u (prog s)

set_option maxRecDepth 8192 in
theorem newStep {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    (hpre : WalkPre s) (hpc : u.pc = 0x80001130) (h : Sponged s u) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x80004818 ∧ Start OI s v := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := h.inv.sp
  have v568 : Sym.validAccess 8 (s.getReg .x2 - 2088) = true := by
    valid_access hval [hb1]
  obtain ⟨v, hr, h₁⟩ := Sym.BlockSpec.reaches b80001130_spec hpc (by
    rv_eval [sp]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | exact valid1_of_valid8 v568
      | addr_omega [hb1, hb3])
  have k₁ := b80001130_keeps h₁
  have fr := b80001130_frame h₁ (by rw [sp]; addr_omega [hb1])
  have e544 : u.getReg .x2 + 544 = s.getReg .x2 - BitVec.ofNat 64 2112 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e544] at fr
  have st : Step s u v (s.getReg .x2 - BitVec.ofNat 64 2112) 32 :=
    Step.ofMemFrame hpre h.inv.heap (inFrame hpre (by omega) (by omega)) fr (k₁ .x2 (by decide))
  have I := h.inv.after hpre (inFrame hpre (by omega) (by omega)) st
  have hptr : v.getMem (tp s) = s.getReg .x13 := by
    rw [← h.proofPtr]
    exact st.word hpre (by addr_omega [hb1]) (by addr_omega [hb1])
  have a1 : tp s + 8 + 328 = u.getReg .x2 + 544 := by
    rw [sp, tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a2 : tp s + 344 = u.getReg .x2 + 552 := by
    rw [sp, tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a3 : tp s + 352 = u.getReg .x2 + 560 := by
    rw [sp, tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have c : v.getMem (u.getReg .x2 + 568) =
      Sym.StoreKind.merge .b (u.getMem (u.getReg .x2 + 568)) 0 1 :=
    h₁.mem_eq 0 (by decide) (by rv_eval []) rfl
  refine ⟨v, hr, b80001130_pc h₁, {
    inv := I
    regs := h.regs.keep fun r hr ↦ k₁ r (mem_of_mem hr _)
    x1 := b80001130_x1 h₁
    x10 := by rw [b80001130_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x11 := by rw [b80001130_x11 h₁, sp, tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x12 := b80001130_x12 h₁
    proofPtr := hptr
    checked := ?_
    tracks := fun proof hp ↦ ⟨initT s proof, rfl, transcriptAt_init hpre I hptr ?_
      (by rw [a1]; exact b80001130_m_x2_544 h₁) (by rw [a2]; exact b80001130_m_x2_552 h₁)
      (by rw [a3]; exact b80001130_m_x2_560 h₁) hp, rfl⟩ }⟩
  · rw [show tp s + 360 = u.getReg .x2 + 568 by
      rw [sp, tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    rw [byteAt_of_within (b := u.getReg .x2 + 568) (by rw [sp]; addr_omega [hb1, hb3]) (le_refl _)
      (by rw [sp]; addr_omega [hb1]), Nat.sub_self, c,
      Runtime.extractByte_merge _ _ _ (by decide) (by decide) (by decide)]
    split_ifs with hc
    · decide
    · exact absurd ⟨le_refl 0, by decide⟩ hc
  · rw [← h.state]
    refine stateAt_congr fun j hj ↦ ?_
    rw [show tp s + 8 + 128 + BitVec.ofNat 64 (8 * j) = s.getReg .x2 - 2312 + BitVec.ofNat 64 (8 * j) by
      rw [tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]]
    exact st.word hpre (by addr_omega [hb1, hj]) (by addr_omega [hb1, hj])

/-- **From the entry to `next_scalars(8)`**: the prologue and `Transcript::new`, given `memset`'s,
`memcpy`'s and `keccak_f`'s contracts. -/
theorem start (hMS : MemsetSpec 0x800126f4) (hMC : MemcpySpec 0x800126e4)
    (hK : Contracts.KeccakFSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s : MachineState} (hpc : s.pc = 0x80000ef8) (hpre : WalkPre s) :
    ∃ u, Reaches Image.code s u ∧ ((u.pc = 0x80004818 ∧ Start OI s u) ∨ Dead Image.code u) := by
  obtain ⟨u₁, r₁, ⟨p₁, h₁⟩ | d⟩ := prologue hMS hpc hpre
  swap
  · exact ⟨u₁, r₁, Or.inr d⟩
  obtain ⟨u₂, r₂, ⟨p₂, h₂⟩ | d⟩ := keccakStep hK hpre p₁ h₁
  swap
  · exact ⟨u₂, r₁.trans r₂, Or.inr d⟩
  obtain ⟨u₃, r₃, ⟨p₃, h₃⟩ | d⟩ := copyStep hMC hpre p₂ h₂
  swap
  · exact ⟨u₃, r₁.trans (r₂.trans r₃), Or.inr d⟩
  obtain ⟨u₄, r₄, ⟨p₄, h₄⟩ | d⟩ := zeroStep hMS hpre p₃ h₃
  swap
  · exact ⟨u₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inr d⟩
  obtain ⟨u₅, r₅, ⟨p₅, h₅⟩ | d⟩ := spongeStep hMC hpre p₄ h₄
  swap
  · exact ⟨u₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inr d⟩
  obtain ⟨u₆, r₆, p₆, h₆⟩ := newStep (OI := OI) hpre p₅ h₅
  exact ⟨u₆, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r₆)))), Or.inl ⟨p₆, h₆⟩⟩

end Rv64Verifier.Proofs.Walk
