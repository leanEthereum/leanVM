import Rv64Verifier.Proofs.Pcs.VsoLadder

/-!
# `verify_stacked_opening`: the configuration checked, the first round polynomial

From `0x8000a0fc`: `queries.len() != folds.len()` returns `Err` (`0x8000b828`); the impossible
niche of `Option<WhirConfig>` (`0x8000a108`) returns the rates' pointer; `0x8000a118` saves that
pointer at `S - 864` and calls `sumcheck_round_poly(S - 464, transcript, 3, &target, &None)`,
whose `Err` is returned (`0x8000b84c`). At `0x8000a150` the mirror's `verify_whir` is at its level
loop (`Configured`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What `derive_config` returns. -/
def cfgOf (s : MachineState) : Model.Pcs.WhirConfigRust :=
  ⟨Model.Pcs.ladderRates (s.getReg .x13).toNat (K0 s + 1), Model.Pcs.ladderFolds (K0 s + 1),
    (Model.Pcs.whirQueriesRust (s.getReg .x12).toNat (s.getReg .x13).toNat).getD []⟩

/-- The claims. -/
def claimsOf (s : MachineState) : List Model.Pcs.StackClaimRust := claimsAt s (s.getReg .x14) (ncl s)

theorem claimsOf_length (s : MachineState) : (claimsOf s).length = ncl s := by
  simp [claimsOf, claimsAt]

/-- At `0x8000a150`: the ladders in `FP` and `RP`, the first round polynomial at `x22`/`x23`, the
`StackBasis` at `S - 728`; the mirror at its level loop. -/
structure Configured (s b u : MachineState) (nxb QP QL FP RP : Word) : Prop where
  inv : Inv s u (u.getMem nextAddr)
  kept : Kept s b u QP QL
  pc : u.pc = 0x8000a150
  x9 : u.getReg .x9 = FP
  x19 : u.getReg .x19 = BitVec.ofNat 64 (K0 s + 2)
  x25 : u.getReg .x25 = s.getReg .x10 + 8
  x26 : u.getReg .x26 = s.getReg .x12
  x27 : u.getReg .x27 = s.getReg .x10
  rp : u.getMem (s.getReg .x2 - 864) = RP
  folds : u.readWords FP (K0 s + 2) = lw (Model.Pcs.ladderFolds (K0 s + 1))
  rates : u.readWords RP (K0 s + 2) = lw (Model.Pcs.ladderRates (s.getReg .x13).toNat (K0 s + 1))
  bufs : nxb.toNat ≤ FP.toNat ∧ FP.toNat + 8 * (K0 s + 2) ≤ heapNext u ∧ FP.toNat % 8 = 0 ∧
    nxb.toNat ≤ RP.toNat ∧ RP.toNat + 8 * (K0 s + 2) ≤ heapNext u ∧ RP.toNat % 8 = 0
  scales : (vecLen u (s.getReg .x2 - 728)).toNat = ncl s ∧ (ncl s = 0 ∨
    (vecPtr u (s.getReg .x2 - 728)).toNat + 24 * ncl s ≤ nxb.toNat)
  config : Model.Pcs.deriveConfigRust (s.getReg .x12).toNat (s.getReg .x13).toNat = some (cfgOf s)
  value : ∀ T, TranscriptAt s (s.getReg .x10) T → ∃ T',
    (Model.Pcs.verifyStackedOpeningRust (s.getReg .x12).toNat (s.getReg .x13).toNat
      (claimsOf s)).run T =
      (Model.Pcs.whirLevelsRust (s.getReg .x12).toNat (cfgOf s)
        (Model.Pcs.stackBasisEvaluate (claimsOf s) (vecEs u (s.getReg .x2 - 728))) 0
        ((cfgOf s).folds.zip (cfgOf s).logInvRates)
        ⟨eListAt u (u.getReg .x22) (u.getReg .x23).toNat, [], []⟩).run T' ∧
      TranscriptAt u (s.getReg .x10) T' ∧
      ((u.getReg .x23).toNat = 0 ∨ (nxb.toNat ≤ (u.getReg .x22).toNat ∧
        (u.getReg .x22).toNat + 24 * (u.getReg .x23).toNat ≤ heapNext u))

theorem tr_facts {s u : MachineState} {nx : Word} (hpre : VsoPre s) (h : Inv s u nx) :
    TranscriptOk u (s.getReg .x10) ∧ proofAt u (s.getReg .x10) = proofAt s (s.getReg .x10) ∧
      streamPtr u (s.getReg .x10) = streamPtr s (s.getReg .x10) ∧
      streamLen u (s.getReg .x10) = streamLen s (s.getReg .x10) := by
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hpa := hpre.proofSponge
  simp only [ProofApart] at hpa
  have hP := Region.bounds hI.ok.proof
  have hm8 : Misses (Wr s vsoStack (W s) nx) (s.getReg .x10) 8 := fun y hy hW ↦ by
    rcases hW with hW | hW
    · simp only [W] at hW; addr_omega [hy, hW, hS]
    · exact src_misses h.fits hI.stack hI.free y (by addr_omega [hy, hS]) (Or.inr hW)
  have hm48 : Misses (Wr s vsoStack (W s) nx) (proofAt s (s.getReg .x10)) 48 := fun y hy hW ↦ by
    rcases hW with hW | hW
    · simp only [W] at hW; addr_omega [hy, hW, hpa.1, hP]
    · exact src_misses h.fits hI.proofStack.1 hI.proofFree y hy (Or.inr hW)
  obtain ⟨e0, e1, e2⟩ := h.mem.stream' hm8 (by omega) hm48 (by omega)
  exact ⟨h.mem.transcriptOk hI.ok hm8 hm48, e0, e1, e2⟩

theorem outside_mono {s t : MachineState} {a : Word} {n : Nat} (h : Outside s a n)
    (hle : heapNext s ≤ heapNext t) : Outside t a n := by
  simp only [Outside] at h ⊢
  refine ⟨?_, h.2⟩
  rcases h.1 with h1 | h1
  · exact Or.inl (by omega)
  · exact Or.inr h1

theorem stack_region {s : MachineState} (hpre : VsoPre s) {x : Word} {n : Nat}
    (h1 : (s.getReg .x2 - 2464).toNat ≤ x.toNat) (h2 : x.toNat + n + 8 ≤ (s.getReg .x2).toNat)
    (h3 : x.toNat % 8 = 0) : Region x n := by
  have hm := hpre.stack.mapped (by decide) (by decide)
  have hb := bounds hpre
  simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
    shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack,
    stackLo] at hm
  exact ⟨Or.inr ⟨by addr_omega [hm, h1, hb], by addr_omega [hm, h2, hb]⟩, h3⟩

/-- A region apart from the stack, outside the free heap at entry, misses `RW`. -/
theorem RW.misses {s : MachineState} {lo hi a : Word} {n : Nat} (hpre : VsoPre s)
    (hs : Apart a n (stackLo s vsoStack) vsoStack) (hf : Outside s a n)
    (hlo : heapNext s ≤ lo.toNat) (hhi : hi.toNat ≤ heapEnd) : Misses (RW s lo hi) a n := by
  have hb := bounds hpre
  simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
    shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack,
    stackLo] at hs
  simp only [Outside] at hf
  intro y hy hw
  simp only [RW, RWl] at hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw
  · addr_omega [hy, hw, hs, hb]
  · addr_omega [hy, hw, hs, hb]
  · addr_omega [hy, hw, hs, hb]
  · addr_omega [hy, hw, hs, hb]
  · addr_omega [hy, hw, hs, hb]
  · addr_omega [hy, hw, hf.2]
  · rcases hf.1 with h1 | h1
    · addr_omega [hy, hw.1, h1, hlo]
    · addr_omega [hy, hw.2, h1, hhi]


/-- At `0x8000c334`, called from `0x8000a13c`: `sumcheck_round_poly(S - 464, transcript, 3,
&target, &None)`, the configuration checked. -/
structure Calling (s b u : MachineState) (nxb QP QL FP RP : Word) : Prop extends Since s b u nxb,
    Kept s b u QP QL where
  pc : u.pc = 0x8000c334
  x1 : u.getReg .x1 = 0x8000a13c
  x8 : u.getReg .x8 = 0xffffffffffffffff
  x9 : u.getReg .x9 = FP
  x10 : u.getReg .x10 = s.getReg .x2 - 464
  x11 : u.getReg .x11 = s.getReg .x10
  x12 : u.getReg .x12 = 3
  x13 : u.getReg .x13 = s.getReg .x2 - 752
  x14 : u.getReg .x14 = s.getReg .x2 - 384
  x19 : u.getReg .x19 = BitVec.ofNat 64 (K0 s + 2)
  qlen : QL = BitVec.ofNat 64 (K0 s + 2)
  none : u.getMem (s.getReg .x2 - 384) = 0
  rp : u.getMem (s.getReg .x2 - 864) = RP
  folds : u.readWords FP (K0 s + 2) = lw (Model.Pcs.ladderFolds (K0 s + 1))
  rates : u.readWords RP (K0 s + 2) = lw (Model.Pcs.ladderRates (s.getReg .x13).toNat (K0 s + 1))
  bufs : nxb.toNat ≤ FP.toNat ∧ FP.toNat + 8 * (K0 s + 2) ≤ heapNext u ∧ FP.toNat % 8 = 0 ∧
    nxb.toNat ≤ RP.toNat ∧ RP.toNat + 8 * (K0 s + 2) ≤ heapNext u ∧ RP.toNat % 8 = 0

theorem checked {s b u : MachineState} {nxb QP QL : Word} (hpre : VsoPre s)
    (h : LadEnd s b u nxb QP QL) :
    ∃ v, Reaches Image.code u v ∧ (Fail s v ∨ ∃ FP RP, Calling s b v nxb QP QL FP RP) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := h.sp
  have hF := h.folds
  have hR := h.rates
  have hFn := hF.len
  rw [lwF_len] at hFn
  have hRn := hR.len
  rw [lwR_len] at hRn
  have hFc := hF.vec.len
  have hRc := hR.vec.len
  have hFhi := hF.hi
  have hRhi := hR.hi
  have hhi := h.heap.hi
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a0fc_spec h.pc (by
    rv_eval [hsp]; valid_access hst.valid [hb])
  have k₁ := b8000a0fc_keeps h₁
  have hm₁ := b8000a0fc_mem_same h₁
  have S₁ := h.toSince.same hm₁ (fun r hr ↦ k₁ r (Runtime.mem_of_mem hr _))
  have hql : u.getMem (u.getReg .x2 + 240) = QL := by rw [hsp]; rv_eval [h.ql]
  by_cases hq : QL = BitVec.ofNat 64 (K0 s + 2)
  swap
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a104_spec
      (b8000a0fc_pc_not_taken h₁ (by rw [hql, h.x18]; exact hq)) trivial
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000b828_spec (b8000a104_pc h₂) trivial
    have S₃ := (S₁.same (b8000a104_mem_same h₂)
      (fun r hr ↦ b8000a104_keeps h₂ r (Runtime.mem_of_mem hr _))).same (b8000b828_mem_same h₃)
      (fun r hr ↦ b8000b828_keeps h₃ r (Runtime.mem_of_mem hr _))
    exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl (S₃.fail hpre (b8000b828_pc h₃)
      (by rw [b8000b828_x10 h₃]; decide))⟩
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := S₁.sp
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a108_spec
    (b8000a0fc_pc_taken h₁ (by rw [hql, h.x18]; exact hq)) (by
      rv_eval [sp₁]; and_intros <;> valid_access hst.valid [hb])
  have k₂ := b8000a108_keeps h₂
  have hm₂ := b8000a108_mem_same h₂
  have S₂ := S₁.same hm₂ (fun r hr ↦ k₂ r (Runtime.mem_of_mem hr _))
  obtain ⟨RP, hRP⟩ : ∃ R, vecPtr u (s.getReg .x2 - 384) = R := ⟨_, rfl⟩
  obtain ⟨FP, hFP⟩ : ∃ F, vecPtr u (s.getReg .x2 - 464) = F := ⟨_, rfl⟩
  have hRP' : t₁.getMem (s.getReg .x2 - 376) = RP := by
    rw [hm₁, ← hRP]; simp only [vecPtr]; rv_eval []
  have x10₂ : t₂.getReg .x10 = RP := by rw [b8000a108_x10 h₂, sp₁]; rv_eval [hRP']
  have hRhi' := hRhi
  have hFhi' := hFhi
  rw [hRP] at hRhi'
  rw [hFP] at hFhi'
  by_cases hcap : t₁.getMem (t₁.getReg .x2 + 656) = 0xffffffffffffffff
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl (S₂.fail hpre (b8000a108_pc_taken h₂ hcap)
      (by rw [x10₂]; simp only [okTag]; intro h0; rw [h0] at hRhi'; simp only [heapNext] at hRhi' hhi
          ; addr_omega [hRhi', hhi]))⟩
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a118_spec
    (b8000a108_pc_not_taken h₂ hcap) (by
      rv_eval [S₂.sp]; and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000a118_keeps h₃
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := S₂.sp
  have X₃ : DFrame t₂ t₃ fun a ↦ Within a (s.getReg .x2 - 384) 8 ∨
      Within a (s.getReg .x2 - 864) 8 :=
    (holds_dframe h₃).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a118, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [sp₂] at hw
      · exact Or.inl hw
      · exact Or.inr hw
  have nx₃ : t₃.getMem nextAddr = t₂.getMem nextAddr := X₃ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hw, hi, hb, hnx]
  have S₃ : Since s b t₃ nxb := S₂.blk X₃ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact RW.hdr (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb]))
    nx₃ (fun r hr ↦ k₃ r (Runtime.mem_of_mem hr _))
  have K₃ : Kept s b t₃ QP QL :=
    ((h.toKept.step hpre (DFrame.of_same hm₁ (fun _ ↦ False)) fun _ h ↦ h.elim).step hpre
      (DFrame.of_same hm₂ (fun _ ↦ False)) fun _ h ↦ h.elim).step hpre X₃ fun a ha hw ↦ by
      rcases ha with ha | ha <;> addr_omega [ha, hw, hb]
  have hm₁₂ (a : Word) : t₂.getMem a = u.getMem a := by rw [hm₂, hm₁]
  have keepH (p : Word) (n : Nat) (hp : p.toNat + 8 * n ≤ heapEnd) :
      t₃.readWords p n = u.readWords p n := by
    rw [DFrame.readWords' X₃ (fun a ha hw ↦ by
      rcases ha with ha | ha <;> addr_omega [ha, hw, hb, hp]) (by
        simp only [heapEnd] at hp; omega)]
    simp only [readWords_eq_map, hm₁₂]
  have hn3 : heapNext t₃ = heapNext u := by simp only [heapNext, nx₃, hm₁₂]
  have hFl := hF.lo
  have hRl := hR.lo
  have hF8 := hF.vec.raw.1
  have hR8 := hR.vec.raw.1
  rw [hFP] at hFl hF8
  rw [hRP] at hRl hR8
  have hFw := hF.words
  have hRw := hR.words
  rw [lwF_len, hFP] at hFw
  rw [lwR_len, hRP] at hRw
  refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨FP, RP, {
    toSince := S₃
    toKept := K₃
    pc := b8000a118_pc h₃
    x1 := b8000a118_x1 h₃
    x8 := by rw [k₃ .x8 (by decide), b8000a108_x8 h₂]
    x9 := by rw [k₃ .x9 (by decide), k₂ .x9 (by decide), k₁ .x9 (by decide), h.x9, hFP]
    x10 := by rw [b8000a118_x10 h₃, sp₂]; rv_eval []
    x11 := by rw [b8000a118_x11 h₃, S₂.x27]
    x12 := b8000a118_x12 h₃
    x13 := by rw [b8000a118_x13 h₃, sp₂]; rv_eval []
    x14 := by rw [b8000a118_x14 h₃, sp₂]; rv_eval []
    x19 := by rw [k₃ .x19 (by decide), k₂ .x19 (by decide), b8000a0fc_x19 h₁, hql, hq]
    qlen := hq
    none := by have := b8000a118_m_x2_656 h₃; rw [sp₂] at this; rv_eval [] at this; exact this
    rp := by
      have := b8000a118_m_x2_176 h₃; rw [sp₂, x10₂] at this; rv_eval [] at this; exact this
    folds := by
      rw [keepH _ _ (by simp only [heapNext] at hFhi' hhi; omega)]
      exact hFw
    rates := by
      rw [keepH _ _ (by simp only [heapNext] at hRhi' hhi; omega)]
      exact hRw
    bufs := by rw [hn3]; refine ⟨hFl, by omega, hF8, hRl, by omega, hR8⟩ }⟩⟩


theorem round (hRP : RoundPolyErrSpec) {s b u : MachineState} {nxb QP QL FP RP : Word}
    (hpre : VsoPre s) (hc : Cfg s QP QL) (h : Calling s b u nxb QP QL FP RP) :
    ∃ v, Reaches Image.code u v ∧ (Fail s v ∨ Configured s b v nxb QP QL FP RP) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, hro⟩ := sfacts hpre
  have hsp := h.sp
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  have hPs := hI.proofStack
  simp only [ProofApart, vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack,
    nextScalarsStack, shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack,
    memStack, stackLo] at hIs hPs
  have inv := h.toSince.inv hpre
  obtain ⟨hTok, e0, e1, e2⟩ := tr_facts hpre inv
  have hmb := h.bat.inv.mono
  have hmu := h.mono
  have hsu : heapNext s ≤ heapNext u := Nat.le_trans hmb hmu
  have hsl : stackLo u roundPolyStack = s.getReg .x2 - 2464 := by
    simp only [stackLo, roundPolyStack, nextScalarsStack, shuntNextStack, nextScalarStack,
      absorbStack, duplexStack, keccakFStack, memStack, hsp]
    addr_omega [hb]
  have hpreR : RoundPolyPre u := {
    heap := h.heap
    out := by
      rw [h.x10]; exact stack_region hpre (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    self := by rw [h.x11]; exact hTok
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [h.x10, hsl]; addr_omega [hb]
    selfStack := by rw [h.x11, hsl]; addr_omega [hIs, hb]
    outSelf := by rw [h.x10, h.x11]; addr_omega [hIs, hb]
    proofStack := by
      rw [h.x11, hsl]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [hPs.1, hb], by addr_omega [hPs.2, hb]⟩
    proofOut := by
      rw [h.x11, h.x10]; simp only [ProofApart, e0, e1, e2]
      exact ⟨by addr_omega [hPs.1, hb], by addr_omega [hPs.2, hb]⟩
    outFree := by rw [h.x10]; exact stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])
    selfFree := by rw [h.x11]; exact outside_mono hI.free hsu
    proofFree := by rw [h.x11, e0]; exact outside_mono hI.proofFree hsu
    streamFree := by rw [h.x11, e1, e2]; exact outside_mono hI.streamFree hsu
    rodata := h.toSince.rodata hpre
    outRodata := by rw [h.x10]; addr_omega [hro, hb]
    selfRodata := by rw [h.x11]; exact hI.rodata
    count := by rw [h.x12]; decide
    claim := by
      rw [h.x13]; exact stack_region hpre (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    eqFactor := by
      rw [h.x14]; exact stack_region hpre (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    claimFree := by rw [h.x13]; exact stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])
    eqFactorFree := by rw [h.x14]; exact stack_outside hpre (by addr_omega [hb]) (by addr_omega [hb])
    claimStack := by rw [h.x13, hsl]; addr_omega [hb]
    eqFactorStack := by rw [h.x14, hsl]; addr_omega [hb]
    claimSelf := by rw [h.x13, h.x11]; addr_omega [hIs, hb]
    eqFactorSelf := by rw [h.x14, h.x11]; addr_omega [hIs, hb] }
  obtain ⟨t₁, hr₁, ⟨hpc₁, hpres₁, hpost₁, herr₁⟩ | hdead⟩ := hRP.call (Reaches.refl u) h.pc hpreR
  swap
  · exact ⟨t₁, hr₁, Or.inl (Or.inl hdead)⟩
  have hfr := hpost₁.frame
  simp only [TFrame] at hfr
  rw [h.x10, h.x11, hsl] at hfr
  have hhi₁ := hpost₁.heap.hi
  have hmo₁ := hpost₁.mono
  have inv₁ : Inv s t₁ (t₁.getMem nextAddr) := Inv.step' hpre inv hfr
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
      · exact Or.inl (by simp only [W]; addr_omega [ha, hS])
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr ⟨Nat.le_trans hsu ha.1, ha.2⟩)))
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hIs, hS, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx]
      · simp only [Fresh] at ha; addr_omega [ha.2, hhi₁, hb])
    rfl hmo₁ hhi₁ (hpres₁.reg .x2)
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := inv₁.sp
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a13c_spec
    (by rw [hpc₁, returnAddress_eq, h.x1]; decide) (by
      rv_eval [sp₁]; and_intros <;> valid_access hst.valid [hb])
  have k₂ := b8000a13c_keeps h₂
  have hm₂ := b8000a13c_mem_same h₂
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := by
    rw [hm₂]; exact Inv.same' inv₁ hm₂ (k₂ .x2 (by decide))
  have x8₁ : t₁.getReg .x8 = 0xffffffffffffffff := by
    rw [hpres₁ .x8 (by simp only [calleeSaved]; decide), h.x8]
  have hcap0 : t₁.getMem (t₁.getReg .x2 + 576) = t₁.getMem (s.getReg .x2 - 464) := by
    rw [sp₁]; rv_eval []
  by_cases herr : t₁.getMem (s.getReg .x2 - 464) = 0xffffffffffffffff
  · obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a14c_spec
      (b8000a13c_pc_not_taken h₂ (by rw [hcap0, herr, x8₁])) trivial
    obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000b84c_spec (b8000a14c_pc h₃) trivial
    have hm₄ (a : Word) : t₄.getMem a = t₂.getMem a := by
      rw [b8000b84c_mem_same h₄, b8000a14c_mem_same h₃]
    have hne := herr₁ (by rw [h.x10]; exact herr)
    rw [h.x10] at hne
    refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl (Or.inr ⟨b8000b84c_pc h₄, ?_, _,
      Inv.same' inv₂ hm₄ (by rw [b8000b84c_keeps h₄ .x2 (by decide),
        b8000a14c_keeps h₃ .x2 (by decide)])⟩)⟩
    rw [b8000b84c_x10 h₄, b8000a14c_keeps h₃ .x22 (by decide), b8000a13c_x22 h₂, sp₁]
    rv_eval []
    rv_eval [] at hne
    exact hne
  have hpc₂ := b8000a13c_pc_taken h₂ (by rw [hcap0, x8₁]; exact herr)
  have hr := hc.rate
  have hn := hc.logN
  -- what the call leaves alone
  have hbuf := h.bufs
  have hFo := hI.free
  simp only [Outside] at hFo
  have fmiss (p : Word) (n : Nat) (h1 : heapNext s ≤ p.toNat) (h2 : p.toNat + n ≤ heapNext u) :
      ∀ a, (Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
        Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh u t₁ a) →
        ¬ Within a p n := fun a ha hw ↦ by
    have hhu := h.heap.hi
    rcases ha with ha | ha | ha | ha | ha
    · addr_omega [ha, hw, h2, hhu, hb]
    · rcases hFo.1 with h0 | h0
      · addr_omega [ha, hw, h0, h1]
      · addr_omega [ha, hw, h0, h2, hhu, hS]
    · addr_omega [ha, hw, h2, hhu, hb]
    · addr_omega [ha, hw, h2, hhu, hnx]
    · simp only [Fresh] at ha; addr_omega [ha.1, hw, h2]
  have smiss : ∀ a, (Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
      Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh u t₁ a) →
      ¬ Within a (s.getReg .x2 - 864) 176 := fun a ha hw ↦ by
    rcases ha with ha | ha | ha | ha | ha
    · addr_omega [ha, hw, hb]
    · addr_omega [ha, hw, hIs, hS, hb]
    · addr_omega [ha, hw, hb]
    · addr_omega [ha, hw, hb, hnx]
    · simp only [Fresh] at ha; addr_omega [ha.2, hw, hhi₁, hb]
  have hm12 (a : Word) : t₂.getMem a = t₁.getMem a := hm₂ a
  have K₂ : Kept s b t₂ QP QL :=
    (h.toKept.step hpre hfr fun a ha hw ↦ smiss a ha (by addr_omega [hw, hb])).step hpre
      (DFrame.of_same hm₂ (fun _ ↦ False)) fun _ h ↦ h.elim
  have hsF : heapNext s ≤ FP.toNat := by omega
  have hsR : heapNext s ≤ RP.toNat := by omega
  have hwF : t₂.readWords FP (K0 s + 2) = u.readWords FP (K0 s + 2) := by
    rw [show t₂.readWords FP (K0 s + 2) = t₁.readWords FP (K0 s + 2) by
      simp only [readWords_eq_map, hm12]]
    exact DFrame.readWords' hfr (fmiss FP _ hsF (by omega)) (by
      have := h.heap.hi; simp only [heapNext, heapEnd] at this hbuf; omega)
  have hwR : t₂.readWords RP (K0 s + 2) = u.readWords RP (K0 s + 2) := by
    rw [show t₂.readWords RP (K0 s + 2) = t₁.readWords RP (K0 s + 2) by
      simp only [readWords_eq_map, hm12]]
    exact DFrame.readWords' hfr (fmiss RP _ hsR (by omega)) (by
      have := h.heap.hi; simp only [heapNext, heapEnd] at this hbuf; omega)
  have hn₂ : heapNext t₂ = heapNext t₁ := by simp only [heapNext, hm12]
  have hreg (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x25, .x26, .x27]) : t₂.getReg r = u.getReg r := by
    rw [k₂ r (Runtime.mem_of_mem hr _),
      hpres₁ r (by simp only [calleeSaved]; exact Runtime.mem_of_mem hr _)]
  -- the scales
  have hBb := h.bat.buf
  have hBl := h.bat.len
  have hbn : heapNext b = nxb.toNat := by simp only [heapNext, h.bat.inv.next]
  have hsc0 : vecPtr t₂ (s.getReg .x2 - 728) = vecPtr b (s.getReg .x2 - 776) := by
    have := K₂.b1; simp only [vecPtr]; rv_eval []; exact this
  have hsc1 : vecLen t₂ (s.getReg .x2 - 728) = vecLen b (s.getReg .x2 - 776) := by
    have := K₂.b2; simp only [vecLen]; rv_eval []; exact this
  have hncl : (vecLen b (s.getReg .x2 - 776)).toNat = ncl s := by rw [hBl]; rfl
  have hBr : ncl s = 0 ∨ heapNext s ≤ (vecPtr b (s.getReg .x2 - 776)).toNat ∧
      (vecPtr b (s.getReg .x2 - 776)).toNat + 24 * ncl s ≤ nxb.toNat := by
    rcases hBb.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨h0.1, by rw [← hbn]; exact h0.2⟩
  have hscales : vecEs t₂ (s.getReg .x2 - 728) = vecEs b (s.getReg .x2 - 776) := by
    simp only [vecEs, hsc0, hsc1, hncl]
    rw [show eListAt t₂ (vecPtr b (s.getReg .x2 - 776)) (ncl s) =
      eListAt t₁ (vecPtr b (s.getReg .x2 - 776)) (ncl s) by simp only [eListAt, eAt, hm12]]
    have hhu := h.heap.hi
    rcases hBr with h0 | h0
    · rw [h0]; rfl
    rw [DFrame.eList hfr (fun x hx hw ↦ fmiss _ _ h0.1 (by omega) x hw hx) (Or.inr (by
      simp only [heapNext, heapEnd] at hhu h0 hmu; omega))]
    exact DFrame.eList h.fr (fun x hx hw ↦ by
      simp only [RW, RWl] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw
      · addr_omega [hx, hw, h0, hhu, hb, hmu]
      · addr_omega [hx, hw, h0, hhu, hb, hmu]
      · addr_omega [hx, hw, h0, hhu, hb, hmu]
      · addr_omega [hx, hw, h0, hhu, hb, hmu]
      · addr_omega [hx, hw, h0, hhu, hb, hmu]
      · addr_omega [hx, hw, h0, hhu, hmu, hnx]
      · addr_omega [hx, hw.1, h0]) (Or.inr (by simp only [heapNext, heapEnd] at hhu h0 hmu; omega))
  -- the configuration
  have ro := h.toSince.rodata hpre
  obtain ⟨hq, -, -, -⟩ := Model.Pcs.RodataOk.queries ro hr hn
  obtain ⟨hQP, hQL⟩ := hc.hQ u ro
  simp only [qEntry] at hQP hQL
  rw [hQP, hQL] at hq
  have hlen : (Model.Pcs.natsAt u QP QL.toNat).length =
      ((s.getReg .x12).toNat - 12) / 4 + 2 := by
    simp only [Model.Pcs.natsAt, List.length_map, List.length_range, h.qlen, K0]
    rw [BitVec.toNat_ofNat]; omega
  have hcfg : Model.Pcs.deriveConfigRust (s.getReg .x12).toNat (s.getReg .x13).toNat =
      some (cfgOf s) := by
    rw [Model.Pcs.deriveConfig_ladder hn.1 hq hlen]
    simp only [cfgOf, hq, Option.getD_some, K0]
  -- the round polynomial's `Vec`
  have hx22 : t₂.getReg .x22 = vecPtr t₁ (s.getReg .x2 - 464) := by
    rw [b8000a13c_x22 h₂, sp₁]; simp only [vecPtr]; rv_eval []
  have hx23 : t₂.getReg .x23 = vecLen t₁ (s.getReg .x2 - 464) := by
    rw [b8000a13c_x23 h₂, sp₁]; simp only [vecLen]; rv_eval []
  refine ⟨t₂, hr₁.trans hr₂, Or.inr {
    inv := inv₂
    kept := K₂
    pc := hpc₂
    x9 := by rw [hreg .x9 (by decide), h.x9]
    x19 := by rw [hreg .x19 (by decide), h.x19]
    x25 := by rw [hreg .x25 (by decide), h.x25]
    x26 := by rw [hreg .x26 (by decide), h.x26]
    x27 := by rw [hreg .x27 (by decide), h.x27]
    rp := by
      rw [hm12, hfr _ fun i hi hw ↦ smiss _ hw (by addr_omega [hi, hb])]
      exact h.rp
    folds := by rw [hwF]; exact h.folds
    rates := by rw [hwR]; exact h.rates
    bufs := by rw [hn₂]; have := hmo₁; omega
    scales := ?_
    config := hcfg
    value := ?_ }⟩
  · refine ⟨by rw [hsc1, hncl], ?_⟩
    rcases hBr with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by rw [hsc0]; exact h0.2)
  intro T hT
  obtain ⟨c, T1, hs1, hT1, hsc, htg⟩ := h.bat.value T hT
  obtain ⟨hTokb, eb0, eb1, eb2⟩ := tr_facts hpre h.bat.inv
  have hhu := h.heap.hi
  have mRW (a : Word) (n : Nat) (hs' : Apart a n (stackLo s vsoStack) vsoStack)
      (hf : Outside s a n) : Misses (RW s nxb (u.getMem nextAddr)) a n :=
    RW.misses hpre hs' hf hmb hhu
  have hTu : TranscriptAt u (s.getReg .x10) T1 := h.fr.transcriptAt hT1 hTokb
    (fun y hy ↦ mRW _ 368 hI.stack hI.free y (by addr_omega [hy, hS]))
    (by rw [eb0]; exact mRW _ 48 hI.proofStack.1 hI.proofFree)
    (by rw [eb1, eb2]; exact mRW _ _ hI.proofStack.2 hI.streamFree)
    (fun y hy ↦ mRW _ 368 hI.stack hI.free y (by addr_omega [hy, hS]))
  have hclaim : eAt u (u.getReg .x13) = eAt b (s.getReg .x2 - 752) := by
    rw [h.x13]
    exact h.fr.eAt' (fun y hy hw ↦ by
      simp only [RW, RWl] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw
      · addr_omega [hy, hw, hb]
      · addr_omega [hy, hw, hb]
      · addr_omega [hy, hw, hb]
      · addr_omega [hy, hw, hb]
      · addr_omega [hy, hw, hb]
      · addr_omega [hy, hw, hb, hnx]
      · addr_omega [hy, hw.2, hb, hhu]) (by addr_omega [hb])
  have hnone : optEAt u (u.getReg .x14) = none := by rw [h.x14, optEAt, ite_eq_left_of_eq_true _ _ (eq_true h.none)]
  have hv := hpost₁.value T1 (by rw [h.x11]; exact hTu)
  rw [h.x12, hclaim, hnone, htg] at hv
  have h3 : ((3 : Word)).toNat = 3 := rfl
  rw [h3] at hv
  rcases hrun : (Model.TM.sumcheckRoundPoly 3 (Model.dotRust (Verifier.powers c (ncl s))
    (valuesOf s)) none).run T1 with _ | ⟨q, T2⟩
  · simp only [hrun] at hv
    rw [h.x10] at hv
    exact absurd hv herr
  simp only [hrun] at hv
  obtain ⟨-, hnew, hT2⟩ := hv
  rw [h.x10] at hnew
  rw [h.x11] at hT2
  obtain ⟨hTok₁, -, -, -⟩ := tr_facts hpre inv₁
  have hT2' : TranscriptAt t₂ (s.getReg .x10) T2 :=
    (DFrame.of_same hm₂ (fun _ ↦ False)).transcriptAt hT2 hTok₁ (fun _ _ h ↦ h) (fun _ _ h ↦ h)
      (fun _ _ h ↦ h) (fun _ _ h ↦ h)
  have hquad : eListAt t₂ (t₂.getReg .x22) (t₂.getReg .x23).toNat = q := by
    rw [hx22, hx23, ← hnew.elems]; simp only [vecEs, eListAt, eAt, hm12]
  refine ⟨T2, ?_, hT2', ?_⟩
  · rw [hscales, hsc, hquad]
    have := Model.Pcs.vso_run (claims := claimsOf s) hs1 hcfg (by rw [claimsOf_length]; exact hrun)
    rw [claimsOf_length] at this
    exact this
  · rw [hx22, hx23, hn₂]
    have hbuf₁ := hnew.buf.2
    have hl := hnew.vec.len
    rcases hbuf₁ with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩

/-- **The configuration and the first round polynomial**: from `0x80009f08` to the level loop at
`0x8000a150`, or an `Err`, or a dead end. -/
theorem config (hA : AllocSpec) (hG : GrowOneFreshSpec 0x8000d7bc 8 8)
    (hRP : RoundPolyErrSpec) {s b : MachineState} {nxb : Word} (hpre : VsoPre s)
    (h : Batched s b nxb) :
    ∃ v, Reaches Image.code b v ∧ (Fail s v ∨
      ∃ QP QL FP RP, Cfg s QP QL ∧ Configured s b v nxb QP QL FP RP) := by
  obtain ⟨v₁, hr₁, hv₁⟩ := checks hpre h
  rcases hv₁ with hf | hv₁
  · exact ⟨v₁, hr₁, Or.inl hf⟩
  obtain ⟨v₂, hr₂, hv₂⟩ := allocs hA hpre hv₁
  rcases hv₂ with hf | ⟨QP, QL, P, Q, hv₂⟩
  · exact ⟨v₂, hr₁.trans hr₂, Or.inl hf⟩
  have hc : Cfg s QP QL := ⟨hv₂.rate, hv₂.logN, hv₂.hQ⟩
  obtain ⟨v₃, hr₃, hv₃⟩ := pushes hG hpre hv₂
  have hend : ∃ v₄, Reaches Image.code v₂ v₄ ∧ (Dead Image.code v₄ ∨ LadEnd s b v₄ nxb QP QL) := by
    rcases hv₃ with hd | hl | ⟨-, he⟩
    · exact ⟨v₃, hr₃, Or.inl hd⟩
    · obtain ⟨v₄, hr₄, hv₄⟩ := ladder_loop hG hpre hc (K0 s) 0 v₃ (by omega) hl
      exact ⟨v₄, hr₃.trans hr₄, hv₄⟩
    · exact ⟨v₃, hr₃, Or.inr he⟩
  obtain ⟨v₄, hr₄, hv₄⟩ := hend
  rcases hv₄ with hd | hv₄
  · exact ⟨v₄, hr₁.trans (hr₂.trans hr₄), Or.inl (Or.inl hd)⟩
  obtain ⟨v₅, hr₅, hv₅⟩ := checked hpre hv₄
  rcases hv₅ with hf | ⟨FP, RP, hv₅⟩
  · exact ⟨v₅, hr₁.trans (hr₂.trans (hr₄.trans hr₅)), Or.inl hf⟩
  obtain ⟨v₆, hr₆, hv₆⟩ := round hRP hpre hc hv₅
  refine ⟨v₆, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans hr₆))), ?_⟩
  rcases hv₆ with hf | hv₆
  · exact Or.inl hf
  · exact Or.inr ⟨QP, QL, FP, RP, hc, hv₆⟩

/-- **From the entry to the level loop.** -/
theorem toLevels (hT : TryAllocZeroedSpec) (hD : DuplexSpec) (hP : MultilinearContracts.PowersSpec)
    (hDot : MultilinearContracts.DotSpec) (hA : AllocSpec) (hG : GrowOneFreshSpec 0x8000d7bc 8 8)
    (hRP : RoundPolyErrSpec) {s : MachineState} (hpc : s.pc = 0x80009db8) (hpre : VsoPre s) :
    ∃ v, Reaches Image.code s v ∧ (Fail s v ∨
      ∃ b nxb QP QL FP RP, Cfg s QP QL ∧ Configured s b v nxb QP QL FP RP) := by
  obtain ⟨v₁, hr₁, hv₁⟩ := head hT hD hP hDot hpc hpre
  rcases hv₁ with hd | ⟨nxb, hv₁⟩
  · exact ⟨v₁, hr₁, Or.inl (Or.inl hd)⟩
  obtain ⟨v₂, hr₂, hv₂⟩ := config hA hG hRP hpre hv₁
  refine ⟨v₂, hr₁.trans hr₂, ?_⟩
  rcases hv₂ with hf | ⟨QP, QL, FP, RP, hc, hv₂⟩
  · exact Or.inl hf
  · exact Or.inr ⟨_, nxb, QP, QL, FP, RP, hc, hv₂⟩

end Rv64Verifier.Proofs.Pcs.Vso

