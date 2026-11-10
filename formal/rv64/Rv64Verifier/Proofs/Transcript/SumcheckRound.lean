import Rv64Verifier.Proofs.Transcript.SumcheckBase

/-!
# `transcript::sumcheck`'s rounds: `sumcheck_round_poly`

`Head s u ptr i` is the loop's registers, frame and `Vec` after `i` rounds, the `Vec`'s buffer
`ptr`; `Inv` adds what the mirror's first `i` rounds return. `roundPoly` runs
`sumcheck_round_poly` from the loop head and branches on its result: the `Err` exit, or `Msg` at
`0x80010658` with the message in `s6`/`s7`.
-/

namespace Rv64Verifier.Transcript.Sumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F76
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The loop's registers and frame after `i` of the `n` rounds, the `Vec`'s buffer `ptr`. -/
structure Head (s u : MachineState) (ptr : Word) (i : Nat) : Prop where
  fr : Fr s u
  x8 : u.getReg .x8 = errNiche
  x9 : u.getReg .x9 = s.getReg .x12
  x18 : u.getReg .x18 = s.getReg .x14 + BitVec.ofNat 64 (32 * i)
  x19 : u.getReg .x19 = s.getReg .x13
  x20 : u.getReg .x20 = s.getReg .x11
  x21 : u.getReg .x21 = s.getReg .x11 + 8
  x24 : u.getReg .x24 = ptr
  x25 : u.getReg .x25 = BitVec.ofNat 64 (24 * i)
  x26 : u.getReg .x26 = BitVec.ofNat 64 i
  x27 : u.getReg .x27 = BitVec.ofNat 64 (32 * ((s.getReg .x15).toNat - i))
  outM : u.getMem (s.getReg .x2 - 208) = s.getReg .x10
  capM : u.getMem (s.getReg .x2 - 200) = s.getReg .x15
  ptrM : u.getMem (s.getReg .x2 - 192) = ptr
  lenM : u.getMem (s.getReg .x2 - 184) = BitVec.ofNat 64 i
  buf : NewBuf s u ptr ((s.getReg .x15).toNat * 24) 8
  lt : i < (s.getReg .x15).toNat

/-- The registers `Head` names. -/
def headRegs : List Reg := [.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x24, .x25, .x26, .x27]

theorem headRegs_saved : ∀ r ∈ headRegs, r ∈ calleeSaved := by decide

/-- A step that keeps `Head`'s registers and its words at `S - 208`. -/
theorem Head.step {s u v : MachineState} {ptr : Word} {i : Nat} (h : Head s u ptr i) (F : Fr s v)
    (regs : ∀ r ∈ headRegs, v.getReg r = u.getReg r)
    (mem : ∀ y : Word, (s.getReg .x2).toNat - 208 ≤ y.toNat → y.toNat + 8 ≤ (s.getReg .x2).toNat - 176 →
      v.getMem y = u.getMem y)
    (hS : 208 ≤ (s.getReg .x2).toNat) (mono : heapNext u ≤ heapNext v) : Head s v ptr i where
  fr := F
  x8 := (regs .x8 (by decide)).trans h.x8
  x9 := (regs .x9 (by decide)).trans h.x9
  x18 := (regs .x18 (by decide)).trans h.x18
  x19 := (regs .x19 (by decide)).trans h.x19
  x20 := (regs .x20 (by decide)).trans h.x20
  x21 := (regs .x21 (by decide)).trans h.x21
  x24 := (regs .x24 (by decide)).trans h.x24
  x25 := (regs .x25 (by decide)).trans h.x25
  x26 := (regs .x26 (by decide)).trans h.x26
  x27 := (regs .x27 (by decide)).trans h.x27
  outM := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.outM]
  capM := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.capM]
  ptrM := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.ptrM]
  lenM := by rw [mem _ (by addr_omega [hS]) (by addr_omega [hS]), h.lenM]
  buf := by have := h.buf; simp only [NewBuf] at this ⊢; omega
  lt := h.lt

/-- The loop head after `i` rounds: `Head`, and the mirror's first `i` rounds return the point in
the buffer and the claim. -/
structure Inv (s u : MachineState) (ptr : Word) (i : Nat) : Prop extends Head s u ptr i where
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ T',
    (pre s i).run T = some ((eListAt u ptr i, eAt u (s.getReg .x12)), T') ∧
    TranscriptAt u (s.getReg .x11) T'

/-- Where the `i`-th equality lies. -/
theorem eq_region {s : MachineState} (hpre : SumcheckPre s) {i : Nat}
    (hi : i < (s.getReg .x15).toNat) :
    Region (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) 32 ∧
      Outside s (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) 32 ∧
      Apart (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) 32 (stackLo s sumcheckStack) sumcheckStack ∧
      Apart (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) 32 (s.getReg .x11) transcriptSize ∧
      Apart (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) 32 (s.getReg .x12) 24 := by
  have he : Region (s.getReg .x14) (32 * (s.getReg .x15).toNat) := by
    rcases hpre.eqs with h | h
    · omega
    · exact h
  have hf : Outside s (s.getReg .x14) (32 * (s.getReg .x15).toNat) := by
    rcases hpre.eqsFree with h | h
    · omega
    · exact h
  have hs := hpre.eqsStack
  have hT := hpre.eqsSelf
  have hc := hpre.claimEqs
  refine ⟨by addr_omega [he, hi], by addr_omega [he, hf, hi], by addr_omega [he, hs, hi],
    by addr_omega [he, hT, hi], by addr_omega [he, hc, hi]⟩

/-- The equalities are kept by a frame in `V`. -/
theorem eq_kept {s u : MachineState} (hpre : SumcheckPre s) (hu : heapNext u ≤ heapEnd)
    (F : DFrame s u (V s u)) {i : Nat} (hi : i < (s.getReg .x15).toNat) :
    optEAt u (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) =
      optEAt s (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) := by
  obtain ⟨hr, ho, hs, hT, hc⟩ := eq_region hpre hi
  have hS := hpre.self.self
  have m : Misses (V s u) (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) 32 :=
    V.miss hu (by addr_omega [hc]) (by addr_omega [hT, hS]) hs ho (by addr_omega [hr])
  have e0 := F _ (m.bytes (x := s.getReg .x14 + BitVec.ofNat 64 (32 * i)) (m := 8)
    (by addr_omega [hr]) (by addr_omega [hr]) (by addr_omega [hr]))
  have e1 := F.eAt (p := s.getReg .x14 + BitVec.ofNat 64 (32 * i) + 8)
    (m.bytes (by addr_omega [hr]) (by addr_omega [hr]) (by addr_omega [hr]))
  simp only [optEAt, e0, e1]

/-- At `0x80010658`, after `sumcheck_round_poly` returned `Ok`: the message's buffer in `s7` and
its length in `s6`, a buffer allocated past the point's, and what the round's mirror returned. -/
structure Msg (s u : MachineState) (ptr : Word) (i : Nat) : Prop extends Head s u ptr i where
  mbuf : (u.getReg .x22).toNat = 0 ∨
    (ptr.toNat + (s.getReg .x15).toNat * 24 ≤ (u.getReg .x23).toNat ∧
      (u.getReg .x23).toNat + 24 * (u.getReg .x22).toNat ≤ heapNext u ∧ (u.getReg .x23).toNat % 8 = 0)
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ Ti T',
    (pre s i).run T = some ((eListAt u ptr i, eAt u (s.getReg .x12)), Ti) ∧
    (TM.sumcheckRoundPoly (s.getReg .x13).toNat (eAt u (s.getReg .x12))
      (optEAt s (s.getReg .x14 + BitVec.ofNat 64 (32 * i)))).run Ti =
      some (eListAt u (u.getReg .x23) (u.getReg .x22).toNat, T') ∧
    TranscriptAt u (s.getReg .x11) T'

/-- Where the function ends: its return, with the contract, or a dead end. -/
def Done (s t : MachineState) : Prop :=
  (t.pc = returnAddress s ∧ Preserves s t ∧ SumcheckPost s t) ∨ Dead Image.code t

set_option maxHeartbeats 4000000 in
/-- From the loop head: `sumcheck_round_poly` into `S - 128`, then on its result. -/
theorem roundPoly (hRP : RoundPolySpec) {s u : MachineState} {ptr : Word} {i : Nat}
    (hpre : SumcheckPre s) (hpc : u.pc = 0x8001062c) (h : Inv s u ptr i) :
    ∃ v, Reaches Image.code u v ∧ (Done s v ∨ (v.pc = 0x80010658 ∧ Msg s v ptr i)) := by
  have hb := bounds hpre
  have hS : 208 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hself := hpre.selfStack
  have hSelf := hpre.self.self
  have hcl := hpre.claim
  have hbuf := h.buf
  simp only [NewBuf] at hbuf
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8001062c_spec hpc trivial
  have k₁ := b8001062c_keeps h₁
  have hm₁ := b8001062c_mem_same h₁
  have x2c : c.getReg .x2 = s.getReg .x2 - 208 := (k₁ .x2 (by decide)).trans h.fr.saved.x2
  have x10c : c.getReg .x10 = s.getReg .x2 - 128 := by
    rw [b8001062c_x10 h₁, h.fr.saved.x2]; ring
  have x11c : c.getReg .x11 = s.getReg .x11 := (b8001062c_x11 h₁).trans h.x20
  have x12c : c.getReg .x12 = s.getReg .x13 := (b8001062c_x12 h₁).trans h.x19
  have x13c : c.getReg .x13 = s.getReg .x12 := (b8001062c_x13 h₁).trans h.x9
  have x14c : c.getReg .x14 = s.getReg .x14 + BitVec.ofNat 64 (32 * i) :=
    (b8001062c_x14 h₁).trans h.x18
  have nxc : heapNext c = heapNext u := by simp only [heapNext, hm₁]
  have Fc : Fr s c := h.fr.same (by addr_omega [hb]) (k₁ .x2 (by decide)) hm₁
  obtain ⟨er, eo, es, eT, ec⟩ := eq_region hpre h.lt
  have hmono := Fc.mono
  have hrp : RoundPolyPre c := {
    toTPre := callee hpre Fc.heap Fc.mono Fc.frame x2c x11c (Nat.le_refl _) (by decide)
      (by rw [x10c]; refine ⟨?_, ?_, ?_⟩ <;> addr_omega [hb])
    count := by rw [x12c]; exact hpre.count
    claim := by rw [x13c]; exact hcl
    eqFactor := by rw [x14c]; exact er
    claimFree := by rw [x13c]; addr_omega [hpre.claimFree, hmono]
    eqFactorFree := by rw [x14c]; addr_omega [eo, hmono]
    claimStack := by rw [x13c]; simp only [stackLo, x2c]; addr_omega [hpre.claimStack, hb]
    eqFactorStack := by rw [x14c]; simp only [stackLo, x2c]; addr_omega [es, hb]
    claimSelf := by rw [x13c, x11c]; exact hpre.claimSelf
    eqFactorSelf := by rw [x14c, x11c]; exact eT }
  obtain ⟨t₁, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hRP.call hr₁ (b8001062c_pc h₁) hrp
  swap
  · exact ⟨t₁, hr₂, Or.inl (Or.inr hd)⟩
  have G := hpost₂.frame
  simp only [TFrame, stackLo, x2c, x10c, x11c] at G
  have mono₂ := hpost₂.mono
  have hhi₂ := hpost₂.heap.hi
  have F₁ : Fr s t₁ := Fc.step (by omega) (hpres₂.reg .x2) hpost₂.heap mono₂ G (fun a hw ↦ by
      rcases hw with hw | hw | hw | hw | hw
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb])))
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp only [Fresh] at hw; omega, hw.2⟩))))
    fun y h1 h2 j hj hw ↦ by
      rcases hw with hw | hw | hw | hw | hw <;>
        addr_omega [hw, hj, h1, h2, hb, hself, hSelf, hst.next, hst.above, hhi₂]
  have keep (y : Word) (h1 : (s.getReg .x2).toNat - 208 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 128) : t₁.getMem y = c.getMem y :=
    G y fun j hj hw ↦ by
      rcases hw with hw | hw | hw | hw | hw <;>
        addr_omega [hw, hj, h1, h2, hb, hself, hSelf, hst.next, hst.above, hhi₂]
  have H₁ : Head s t₁ ptr i := h.toHead.step F₁ (fun r hr ↦ by
      rw [hpres₂.reg r (headRegs_saved r hr), k₁ r (mem_of_mem hr _)])
    (fun y h1 h2 ↦ by rw [keep y h1 (by omega), hm₁]) hS
    (by omega)
  have x2₁ := H₁.fr.saved.x2
  obtain ⟨t₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010648_spec
    (by rw [hpc₂, returnAddress_eq, b8001062c_x1 h₁]; decide) (by
      rv_eval [x2₁]
      and_intros <;> valid_access hst.valid [hb])
  have k₃ := b80010648_keeps h₃
  have hm₃ := b80010648_mem_same h₃
  have x22₃ := b80010648_x22 h₃
  have x23₃ := b80010648_x23 h₃
  rv_eval [x2₁] at x22₃ x23₃
  have F₃ : Fr s t₂ := F₁.same (by omega) (k₃ .x2 (by decide)) hm₃
  have H₃ : Head s t₂ ptr i := H₁.step F₃ (fun r hr ↦ k₃ r (mem_of_mem hr _))
    (fun y _ _ ↦ hm₃ y) hS (by simp only [heapNext, hm₃]; exact Nat.le_refl _)
  -- the point and the claim, kept by the call
  have pk : eListAt t₂ ptr i = eListAt u ptr i := by
    rw [(DFrame.of_same hm₃ fun _ ↦ False).eListAt fun _ _ h ↦ h,
      G.eListAt fun j hj hw ↦ by
        rcases hw with hw | hw | hw | hw | hw <;>
          addr_omega [hw, hj, hbuf, h.lt, hb, hSelf, hpre.selfFree, hst.above, hhi₂, hmono,
            H₁.fr.heap.hi, h.fr.heap.hi, nxc],
      (DFrame.of_same hm₁ fun _ ↦ False).eListAt fun _ _ h ↦ h]
  have ck : eAt t₂ (s.getReg .x12) = eAt u (s.getReg .x12) := by
    rw [(DFrame.of_same hm₃ fun _ ↦ False).eAt fun _ _ h ↦ h,
      G.eAt fun j hj hw ↦ by
        rcases hw with hw | hw | hw | hw | hw <;>
          addr_omega [hw, hj, hcl, hpre.claimSelf, hpre.claimStack, hpre.claimFree, hb, hmono, hSelf, hhi₂],
      (DFrame.of_same hm₁ fun _ ↦ False).eAt fun _ _ h ↦ h]
  have ek : optEAt c (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) =
      optEAt s (s.getReg .x14 + BitVec.ofNat 64 (32 * i)) := eq_kept hpre Fc.heap.hi Fc.frame h.lt
  have cc : eAt c (s.getReg .x12) = eAt u (s.getReg .x12) :=
    (DFrame.of_same hm₁ fun _ ↦ False).eAt fun _ _ h ↦ h
  have hv := hpost₂.value
  rw [x10c, x11c, x12c, x13c, x14c, ek, cc] at hv
  have hcap : vecCap t₁ (s.getReg .x2 - 128) = t₂.getMem (s.getReg .x2 - 128) := by
    simp only [vecCap, hm₃]
  have e120 : s.getReg .x2 - 128 + 8 = s.getReg .x2 - 120 := by ring
  have hx8 : t₁.getMem (t₁.getReg .x2 + 80) = t₂.getMem (s.getReg .x2 - 128) ∧
      t₁.getReg .x8 = errNiche := by
    refine ⟨?_, H₁.x8⟩
    rw [hm₃, x2₁, show s.getReg .x2 - 208 + 80 = s.getReg .x2 - 128 by ring]
  by_cases herr : t₂.getMem (s.getReg .x2 - 128) = errNiche
  · -- `Err`: the result's `Err`, then return
    have hpc₃ := b80010648_pc_taken h₃ (by rw [hx8.1, hx8.2]; exact herr)
    have x23 : t₂.getReg .x23 ≠ errNiche := by
      have := hpost₂.err
      rw [x10c, e120] at this
      rw [x23₃]
      exact this (by rw [hcap]; exact herr)
    obtain ⟨t, hr₄, ht⟩ := exitErr hpre hpc₃ F₃ H₃.outM x23 fun T hT ↦ by
      obtain ⟨Ti, hrun, hTi⟩ := h.value T hT
      have hvT := hv Ti (hTi.congr hm₁)
      refine sumcheck_none s (i + 1) ?_
      rw [pre_succ' s h.lt, hrun]
      cases hq : (TM.sumcheckRoundPoly (s.getReg .x13).toNat (eAt u (s.getReg .x12))
          (optEAt s (s.getReg .x14 + BitVec.ofNat 64 (32 * i)))).run Ti with
      | none => simp only [Option.bind_some, round_run, hq, Option.bind_none]
      | some r =>
        rw [hq] at hvT
        exact absurd (hcap ▸ herr) hvT.1
    exact ⟨t, hr₂.trans (hr₃.trans hr₄), Or.inl (Or.inl ht)⟩
  · have hpc₃ := b80010648_pc_not_taken h₃ (by rw [hx8.1, hx8.2]; exact herr)
    have hok := hpost₂.ok
    rw [x10c] at hok
    obtain ⟨hvo, hnb⟩ := hok (by rw [hcap]; exact herr)
    have nx₃ : heapNext t₂ = heapNext t₁ := by simp only [heapNext, hm₃]
    have hlen : vecLen t₁ (s.getReg .x2 - 128) = t₂.getReg .x22 := by
      rw [x22₃]; simp only [vecLen]; congr 1; ring
    have hptr : vecPtr t₁ (s.getReg .x2 - 128) = t₂.getReg .x23 := by
      rw [x23₃]; simp only [vecPtr]; congr 1
    have hl := hvo.len
    rw [hlen] at hl
    rw [hptr] at hnb
    simp only [NewBuf] at hnb
    refine ⟨t₂, hr₂.trans hr₃, Or.inr ⟨hpc₃, { toHead := H₃, mbuf := ?_, value := fun T hT ↦ ?_ }⟩⟩
    · by_cases h0 : (t₂.getReg .x22).toNat = 0
      · exact Or.inl h0
      · have hlt := h.lt
        have hcp : (t₂.getReg .x22).toNat ≤ (vecCap t₁ (s.getReg .x2 - 128)).toNat := hl
        refine Or.inr ⟨?_, ?_, hnb.1⟩ <;> (try rw [nx₃]) <;> omega
    · obtain ⟨Ti, hrun, hTi⟩ := h.value T hT
      have hvT := hv Ti (hTi.congr hm₁)
      cases hq : (TM.sumcheckRoundPoly (s.getReg .x13).toNat (eAt u (s.getReg .x12))
          (optEAt s (s.getReg .x14 + BitVec.ofNat 64 (32 * i)))).run Ti with
      | none =>
        rw [hq] at hvT
        exact absurd (hcap ▸ hvT) herr
      | some r =>
        rcases r with ⟨q, T'⟩
        rw [hq] at hvT
        obtain ⟨-, hnv, hT'⟩ := hvT
        refine ⟨Ti, T', by rw [pk, ck]; exact hrun, ?_, hT'.congr hm₃⟩
        rw [ck, hq, ← hnv.elems]
        simp only [vecEs, hptr, hlen]
        exact congrArg (fun q ↦ some (q, T'))
          ((DFrame.of_same hm₃ fun _ ↦ False).eListAt fun _ _ h ↦ h).symm

end Rv64Verifier.Transcript.Sumcheck
