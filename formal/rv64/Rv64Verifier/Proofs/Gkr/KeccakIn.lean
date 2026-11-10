import Rv64Verifier.Proofs.Gkr.KeccakOut

/-!
# `keccak::verify_keccak`: the inputs' opening, first steps

`sumcheck(&claim.value, 3, &[None; 4])` (`to_low`), then `open(claim, 0, 2, &value)`, the row to
`f + 416` and `next_scalars(64)` (`to_slices`).
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- After the slices are read. -/
def kIn3 (l : Nat) (cl : KeccakClaim) (o : Option (List E × E)) (low : List E)
    (r : List E × List E × E) (slices : List E) : TM KeccakOpenings :=
  TM.ofOption (multilinearEvalRust cl.mu low) >>= fun atLow ↦
    TM.require (atLow * dotRust r.2.1 slices = r.2.2) >>= fun _ ↦
      pure ⟨o, (low ++ cl.point.take (l - 4) ++ r.1, slices)⟩

/-- After the inputs' `open`. -/
def kIn2 (l : Nat) (cl : KeccakClaim) (o : Option (List E × E)) (low : List E)
    (r : List E × List E × E) : TM KeccakOpenings :=
  TM.nextScalars kBits >>= kIn3 l cl o low r

theorem kInputs_eq (l : Nat) (cl : KeccakClaim) (o : Option (List E × E)) :
    kInputs l cl o = (TM.sumcheck cl.value 3 (List.replicate 4 none) >>= fun p ↦
      openRust ⟨l, 12⟩ cl 0 2 p.2 >>= kIn2 l cl o p.1) := by
  unfold kInputs kIn2 kIn3
  congr 1

/-- `[None; 4]` in `.rodata`. -/
theorem rodata_nones {u : MachineState} (h : RodataOk u) :
    optEListAt u 0xa0000e28 4 = List.replicate 4 none := by
  have h0 : u.getMem 0xa0000e28 = 0 := h.word
  have h1 : u.getMem 0xa0000e48 = 0 := h.word
  have h2 : u.getMem 0xa0000e68 = 0 := h.word
  have h3 : u.getMem 0xa0000e88 = 0 := h.word
  simp only [optEListAt, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, optEAt]
  rw [show (0xa0000e28 : Word) + BitVec.ofNat 64 (32 * 0) = 0xa0000e28 from rfl,
    show (0xa0000e28 : Word) + BitVec.ofNat 64 (32 * 1) = 0xa0000e48 from rfl,
    show (0xa0000e28 : Word) + BitVec.ofNat 64 (32 * 2) = 0xa0000e68 from rfl,
    show (0xa0000e28 : Word) + BitVec.ofNat 64 (32 * 3) = 0xa0000e88 from rfl, h0, h1, h2, h3]
  rfl

/-! ## A buffer allocated since the entry -/

/-- `n` elements `xs` at `p`, allocated since the entry. -/
structure HB (s u : MachineState) (p n : Word) (xs : List E) : Prop where
  buf : NewBuf s u p (24 * n.toNat) 8
  elems : eListAt u p n.toNat = xs
  reg : n.toNat = 0 ∨ (Region p (24 * n.toNat) ∧
    ∀ lo m, heapEnd ≤ lo.toNat → Apart p (24 * n.toNat) lo m)

theorem HB.of_vec {s u : MachineState} (hpre : VerifyKeccakPreW s) (B : Base s u) {a : Word}
    {xs : List E} (h : NewVecE s u a xs) : HB s u (vecPtr u a) (vecLen u a) xs := by
  have h1 := h.buf
  have h2 := h.vec.len
  refine ⟨by simp only [NewBuf] at h1 ⊢; omega, h.elems, ?_⟩
  rcases vec_heaped hpre B h with h0 | H
  · exact Or.inl h0
  · exact Or.inr ⟨H.region, H.above⟩

theorem HB.step {s u v : MachineState} (hpre : VerifyKeccakPreW s) (B : Base s u)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true) (F : DFrame u v (SW s u v rs sp))
    (hN : heapNext u ≤ heapNext v) {p n : Word} {xs : List E} (h : HB s u p n xs) : HB s v p n xs :=
  have b := buf_step hpre B hok F hN ⟨h.buf, h.elems⟩
  ⟨b.1, b.2, h.reg⟩

theorem HB.same {s u v : MachineState} (hm : ∀ a, v.getMem a = u.getMem a) {p n : Word}
    {xs : List E} (h : HB s u p n xs) : HB s v p n xs := by
  have hN : heapNext v = heapNext u := by simp only [heapNext, hm]
  refine ⟨by have := h.buf; simp only [NewBuf, hN] at this ⊢; exact this, ?_, h.reg⟩
  rw [← h.elems]; simp only [eListAt, eAt, hm]

/-- Its bytes lie outside the free heap. -/
theorem HB.outside {s u : MachineState} (hu : HeapOk u) {p n : Word} {xs : List E}
    (h : HB s u p n xs) (hn : n.toNat ≠ 0) : Outside u p (24 * n.toNat) := by
  have hb := h.buf
  have hi := hu.hi
  simp only [NewBuf] at hb
  rcases h.reg with h0 | ⟨hR, -⟩
  · omega
  · exact ⟨Or.inl (by omega), by addr_omega [hR, hb, hi]⟩

/-! ## What the inputs' opening keeps -/

/-- The last claim at `f + 296`, the outputs' point at `f + 392`, the word's limbs, the spills. -/
structure R2 (s u : MachineState) (cl : KeccakClaim) (mp ml : Word) (oslot : List E) (word : E) :
    Prop where
  base : Base s u
  ok : OK s
  m32 : u.getMem (s.getReg .x2 - 5216) = s.getReg .x12 - 4
  m40 : u.getMem (s.getReg .x2 - 5208) = (Model.limbs word).2.2
  m48 : u.getMem (s.getReg .x2 - 5200) = s.getReg .x10
  claim : ClaimOut s u (s.getReg .x2 - 4952) cl
  lens : Lens cl
  mptr : u.getMem (s.getReg .x2 - 4944) = mp
  mlen : u.getMem (s.getReg .x2 - 4936) = ml
  outV : NewVecE s u (s.getReg .x2 - 4856) (instOf s ++ oslot)
  x9 : u.getReg .x9 = s.getReg .x11
  x22 : u.getReg .x22 = mp
  x23 : u.getReg .x23 = ml
  x25 : u.getReg .x25 = (Model.limbs word).2.1
  x26 : u.getReg .x26 = (Model.limbs word).1

theorem R2.step {s u v : MachineState} {cl : KeccakClaim} {mp ml : Word} {oslot : List E}
    {word : E} (hpre : VerifyKeccakPreW s) (R : R2 s u cl mp ml oslot word)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hH : HeapOk v) (hN : heapNext u ≤ heapNext v)
    {rs : List (Nat × Nat)} {spb : Bool} (hok : SlotsOk rs = true)
    (h1 : SlotsSep rs 5216 24 = true) (h3 : SlotsSep rs 4952 96 = true)
    (h4 : SlotsSep rs 4856 24 = true) (F : DFrame u v (SW s u v rs spb))
    (hregs : ∀ r ∈ ([.x9, .x22, .x23, .x25, .x26] : List Reg),
      v.getReg r = u.getReg r) :
    R2 s v cl mp ml oslot word :=
  { base := R.base.step hpre hx2 hH hN hok F
    ok := R.ok
    m32 := (SW.mem hpre hH hok (J := 5216) (by decide) (by decide)
      (SlotsSep.sub h1 (le_refl _) (by omega)) F).trans R.m32
    m40 := (SW.mem hpre hH hok (J := 5208) (by decide) (by decide)
      (SlotsSep.sub h1 (by omega) (by omega)) F).trans R.m40
    m48 := (SW.mem hpre hH hok (J := 5200) (by decide) (by decide)
      (SlotsSep.sub h1 (by omega) (by omega)) F).trans R.m48
    claim := ClaimOut.step hpre R.base hH hN hok (J := 4952) (by decide) (by decide) h3 F R.claim
    lens := R.lens
    mptr := (SW.mem hpre hH hok (J := 4944) (by decide) (by decide)
      (SlotsSep.sub h3 (by omega) (by omega)) F).trans R.mptr
    mlen := (SW.mem hpre hH hok (J := 4936) (by decide) (by decide)
      (SlotsSep.sub h3 (by omega) (by omega)) F).trans R.mlen
    outV := SW.vec hpre R.base hH hN hok (J := 4856) (by decide) (by decide) h4 F R.outV
    x9 := (hregs .x9 (by decide)).trans R.x9
    x22 := (hregs .x22 (by decide)).trans R.x22
    x23 := (hregs .x23 (by decide)).trans R.x23
    x25 := (hregs .x25 (by decide)).trans R.x25
    x26 := (hregs .x26 (by decide)).trans R.x26 }

theorem R2.same {s u v : MachineState} {cl : KeccakClaim} {mp ml : Word} {oslot : List E}
    {word : E} (hpre : VerifyKeccakPreW s) (R : R2 s u cl mp ml oslot word)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (hm : ∀ a, v.getMem a = u.getMem a)
    (hregs : ∀ r ∈ ([.x9, .x22, .x23, .x25, .x26] : List Reg),
      v.getReg r = u.getReg r) : R2 s v cl mp ml oslot word := by
  have hN : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact R.step hpre hx2 ⟨by rw [hN]; exact R.base.heap.lo, by rw [hN]; exact R.base.heap.hi⟩
    (le_of_eq hN.symm) (rs := []) (spb := false) (by decide) (by decide) (by decide) (by decide)
    (DFrame.of_same hm _) hregs

theorem R2.block {s u v : MachineState} {cl : KeccakClaim} {mp ml : Word} {oslot : List E}
    {word : E} (hpre : VerifyKeccakPreW s) (R : R2 s u cl mp ml oslot word)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) {rs : List (Nat × Nat)} (hok : SlotsOk rs = true)
    (h1 : SlotsSep rs 5216 24 = true) (h3 : SlotsSep rs 4952 96 = true)
    (h4 : SlotsSep rs 4856 24 = true) (F : DFrame u v (Slots s rs))
    (hregs : ∀ r ∈ ([.x9, .x22, .x23, .x25, .x26] : List Reg),
      v.getReg r = u.getReg r) : R2 s v cl mp ml oslot word := by
  have hN := slots_next hpre hok F
  exact R.step hpre hx2
    ⟨by simp only [heapNext, hN]; exact R.base.heap.lo, by simp only [heapNext, hN]; exact R.base.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) hok h1 h3 h4 (slots_sw F) hregs

theorem regs7 {u v : MachineState} {l : List Reg} (hl : ∀ r ∈ l, v.getReg r = u.getReg r)
    (h : ([.x9, .x22, .x23, .x25, .x26] : List Reg).all (fun r ↦ decide (r ∈ l)) = true) :
    ∀ r ∈ ([.x9, .x22, .x23, .x25, .x26] : List Reg), v.getReg r = u.getReg r :=
  fun r hr ↦ hl r (by have := List.all_eq_true.mp h r hr; simpa using this)

theorem pres7 {u v : MachineState} (h : Preserves u v) :
    ∀ r ∈ ([.x9, .x22, .x23, .x25, .x26] : List Reg), v.getReg r = u.getReg r :=
  fun r hr ↦ h.reg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)

theorem I0.toR2 {s u : MachineState} {cl : KeccakClaim} {mp ml sp sl : Word} {slot : List E}
    {word : E} (A : I0 s u cl mp ml sp sl slot word) : R2 s u cl mp ml slot word :=
  { base := A.base, ok := A.ok, m32 := A.m32, m40 := A.m40, m48 := A.m48, claim := A.claim,
    lens := A.lens, mptr := A.mptr, mlen := A.mlen, outV := A.outV, x9 := A.x9, x22 := A.x22, x23 := A.x23, x25 := A.x25, x26 := A.x26 }

/-! ## `sumcheck` -/

/-- At `0x800094a4`: the sumcheck's point `low` (`s8`/`s5`), its value at `f + 1976`. -/
structure J1 (s u : MachineState) (cl : KeccakClaim) (mp ml : Word) (oslot : List E) (word : E)
    (lp ll : Word) (low : List E) (sv : E) : Prop extends R2 s u cl mp ml oslot word where
  pc : u.pc = 0x800094a4
  x18 : u.getReg .x18 = s.getReg .x12
  x19 : u.getReg .x19 = 12
  m64 : u.getMem (s.getReg .x2 - 5184) = 2
  x8 : u.getReg .x8 = 0xffffffffffffffff
  x20 : u.getReg .x20 = u.getMem (s.getReg .x2 - 4856)
  x21 : u.getReg .x21 = ll
  x24 : u.getReg .x24 = lp
  lowB : HB s u lp ll low
  sval : eAt u (s.getReg .x2 - 3272) = sv
  rest : Rest s u (openRust ⟨(s.getReg .x12).toNat, 12⟩ cl 0 2 sv >>=
    kIn2 (s.getReg .x12).toNat cl (some (instOf s ++ oslot, word)) low)

theorem to_low (hSC : SumcheckSpec) {s u : MachineState} {cl : KeccakClaim} {mp ml sp sl : Word}
    {oslot : List E} {word : E} (hpre : VerifyKeccakPreW s) (A : I0 s u cl mp ml sp sl oslot word) :
    ∃ t, Reaches Image.code u t ∧
      ((∃ lp ll low sv, J1 s t cl mp ml oslot word lp ll low sv) ∨ Done s t) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have B := A.base
  have ho := hpre.out
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80009454_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b80009454_keeps h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁ .x2 (by decide)).trans B.x2
  have F₁ : DFrame u u₁ (Slots s [(4832, 24)]) := by
    have f := b80009454_frame h₁ (by rw [B.x2]; addr_omega [hb])
    rw [B.x2] at f
    rv_eval [] at f
    exact (DFrame.of_memFrame f).mono fun a ha ↦ ⟨(4832, 24), List.mem_singleton_self _, ha⟩
  have R₁ := A.toR2.block hpre x2₁ (by decide) (by decide) (by decide) (by decide) F₁
    (regs7 k₁ (by decide))
  have a2 (n : Nat) (hn : n ≤ 5248) :
      s.getReg .x2 - 5248 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  have hval₁ : eAt u₁ (s.getReg .x2 - 4832) = cl.value := by
    rw [← A.claim.value]
    unfold Rv64Verifier.eAt
    have e416 := b80009454_m_x2_416 h₁
    have e424 := b80009454_m_x2_424 h₁
    have e432 := b80009454_m_x2_432 h₁
    rw [B.x2, show s.getReg .x2 - 5248 + 416 = s.getReg .x2 - 4832 from a2 416 (by decide),
      show s.getReg .x2 - 5248 + 368 = s.getReg .x2 - 4952 + 72 from
        (a2 368 (by decide)).trans (BitVec.eq_of_toNat_eq (by addr_omega [hb]))] at e416
    rw [B.x2, show s.getReg .x2 - 5248 + 424 = s.getReg .x2 - 4832 + 8 from
        (a2 424 (by decide)).trans (BitVec.eq_of_toNat_eq (by addr_omega [hb])),
      show s.getReg .x2 - 5248 + 376 = s.getReg .x2 - 4952 + 72 + 8 from
        (a2 376 (by decide)).trans (BitVec.eq_of_toNat_eq (by addr_omega [hb]))] at e424
    rw [B.x2, show s.getReg .x2 - 5248 + 432 = s.getReg .x2 - 4832 + 16 from
        (a2 432 (by decide)).trans (BitVec.eq_of_toNat_eq (by addr_omega [hb])),
      show s.getReg .x2 - 5248 + 384 = s.getReg .x2 - 4952 + 72 + 16 from
        (a2 384 (by decide)).trans (BitVec.eq_of_toNat_eq (by addr_omega [hb]))] at e432
    rw [e416, e424, e432]
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 3296 := by rw [b80009454_x10 h₁, B.x2]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x11 := by rw [b80009454_x11 h₁, A.x9]
  have x12₁ : u₁.getReg .x12 = s.getReg .x2 - 4832 := by rw [b80009454_x12 h₁, B.x2]; rv_eval []
  have x13₁ := b80009454_x13 h₁
  have x14₁ := b80009454_x14 h₁
  have x15₁ := b80009454_x15 h₁
  have tp : TPre 48 sumcheckStack u₁ := R₁.base.tpre hpre 3296 x10₁ x11₁ (by decide) (by decide)
    (by decide) (by unfold openStack; omega) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hsr := hpre.selfRodata
  obtain ⟨r1, r2, -⟩ := readsKW hpre R₁.base.heap
  have hS8 : (s.getReg .x11).toNat + 8 ≤ 2 ^ 64 := by addr_omega [hS]
  have hP48 : (proofAt s (s.getReg .x11)).toNat + 48 ≤ 2 ^ 64 := by addr_omega [hpre.self.proof]
  have h4 : (u₁.getReg .x15).toNat = 4 := by rw [x15₁]; rfl
  unfold verifyKeccakStack at hb hsm hab hnx hss hrs
  have hsp : SumcheckPre u₁ := { tp with
    count := by rw [x13₁]; decide
    claim := by rw [x12₁]; addr_omega [hb, hsm]
    eqs := by rw [h4, x14₁]; right; addr_omega []
    claimFree := by rw [x12₁]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    eqsFree := by rw [h4, x14₁]; right; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega []
    claimStack := by rw [x12₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    eqsStack := by rw [h4, x14₁]; simp only [stackLo, x2₁]; addr_omega [hb, hrs]
    claimSelf := by rw [x12₁, x11₁]; addr_omega [hb, hss, hS]
    eqsSelf := by rw [h4, x14₁, x11₁]; addr_omega [hsr]
    claimOut := by rw [x12₁, x10₁]; addr_omega [hb]
    eqsOut := by rw [h4, x14₁, x10₁]; addr_omega [hb, hrs]
    claimEqs := by rw [h4, x14₁, x12₁]; addr_omega [hb, hrs]
    proofClaim := by
      rw [x11₁, x12₁]
      refine R₁.base.frame.proofApart r1 hS8 r2 hP48
        (Open.ProofApart.mono' hpre.proofStack ?_ ?_) <;> unfold verifyKeccakStack <;> addr_omega [hb]
    claimRodata := by rw [x12₁]; addr_omega [hb, hrs] }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hSC.call hr₁ (b80009454_pc h₁) hsp
  swap
  · exact ⟨u₂, hr₂, Or.inr (Or.inr hd)⟩
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans x2₁
  have F₂ : DFrame u₁ u₂ (SW s u₁ u₂ [(3296, 48), (4832, 24)] true) :=
    hpost₂.frame.mono fun a ha ↦ by
      rcases ha with h | h | h | h | h | h
      · rw [x10₁] at h; exact Or.inl ⟨(3296, 48), by simp, h⟩
      · rw [x12₁] at h; exact Or.inl ⟨(4832, 24), by simp, h⟩
      · rw [x11₁] at h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))
      · exact Or.inr (Or.inl (stk_sw hpre x2₁ (by unfold openStack; omega) h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  have R₂ := R₁.step hpre x2₂ hpost₂.heap hpost₂.mono (by decide) (by decide) (by decide)
    (by decide) F₂ (pres7 hpres₂)
  have Rm : Rest s u₁ (TM.sumcheck cl.value 3 (List.replicate 4 none) >>= fun p ↦
      openRust ⟨(s.getReg .x12).toNat, 12⟩ cl 0 2 p.2 >>=
        kIn2 (s.getReg .x12).toNat cl (some (instOf s ++ oslot, word)) p.1) :=
    (A.rest.keep fun T hT ↦ B.block_tat hpre (by decide) F₁ hT).congr (kInputs_eq _ _ _)
  have hnones := rodata_nones (R₁.base.rodata hpre)
  have hv (T : TState) (hT : TranscriptAt u₁ (s.getReg .x11) T) :
      match (TM.sumcheck cl.value 3 (List.replicate 4 none)).run T with
      | some ((point, claim), T') => vecCap u₂ (s.getReg .x2 - 3296) ≠ errNiche ∧
          NewVecE u₁ u₂ (s.getReg .x2 - 3296) point ∧ eAt u₂ (s.getReg .x2 - 3296 + 24) = claim ∧
          TranscriptAt u₂ (s.getReg .x11) T'
      | none => vecCap u₂ (s.getReg .x2 - 3296) = errNiche := by
    have h := hpost₂.value T (by rw [x11₁]; exact hT)
    rw [x12₁, hval₁, x13₁, x14₁, h4, hnones, x10₁, x11₁] at h
    exact h
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009490_spec
    (by rw [hpc₂, returnAddress_eq, b80009454_x1 h₁]; decide) (by
      rv_eval [x2₂]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b80009490_keeps h₃
  have m₃ := b80009490_mem_same h₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (k₃ .x2 (by decide)).trans x2₂
  have R₃ := R₂.same hpre x2₃ m₃ (regs7 k₃ (by decide))
  have tag (n : Nat) (hn : n ≤ 5248) : u₂.getMem (u₂.getReg .x2 + BitVec.ofNat 64 n) =
      u₂.getMem (s.getReg .x2 - BitVec.ofNat 64 (5248 - n)) := by
    rw [x2₂]; exact congrArg _ (a2 n hn)
  have t1952 : u₂.getMem (u₂.getReg .x2 + 1952) = u₂.getMem (s.getReg .x2 - 3296) := tag 1952 (by decide)
  have t1960 : u₂.getMem (u₂.getReg .x2 + 1960) = u₂.getMem (s.getReg .x2 - 3288) := tag 1960 (by decide)
  have t1968 : u₂.getMem (u₂.getReg .x2 + 1968) = u₂.getMem (s.getReg .x2 - 3280) := tag 1968 (by decide)
  by_cases hcap : u₂.getMem (s.getReg .x2 - 3296) = errNiche
  · -- `Err`
    have pc₃ := b80009490_pc_taken h₃ (by rw [t1952, hcap]; rfl)
    have m48' : u₃.getMem (s.getReg .x2 - 5200) = s.getReg .x10 := R₃.m48
    have m48 : u₃.getMem (u₃.getReg .x2 + 48) = s.getReg .x10 := by
      rw [x2₃, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from a2 48 (by decide)]
      exact m48'
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800095b0_spec pc₃ (by
      rv_eval [x2₃]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₄ : MemFrame u₃ u₄ (s.getReg .x10) 24 := h₄.memFrame (by
      intro w hw
      simp only [b800095b0, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> rv_eval [m48] <;> addr_omega [ho])
    have hcap₄ := b800095b0_m2 h₄
    rw [m48, b80009490_x8 h₃] at hcap₄
    obtain ⟨t, hr₅, ht⟩ := err_exit hpre R₃.base (b800095b0_pc h₄)
      ((b800095b0_keeps h₄ .x2 (by decide)).trans x2₃) f₄ hcap₄ (Rm.fail fun T hT ↦ by
        have h := hv T hT
        generalize (TM.sumcheck cl.value 3 (List.replicate 4 none)).run T = o at h ⊢
        rcases o with _ | ⟨⟨pt, cv⟩, T'⟩
        · rfl
        · exact absurd hcap h.1)
    exact ⟨t, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr ht⟩
  -- `Ok`
  have pc₃ := b80009490_pc_not_taken h₃ (by rw [t1952]; exact hcap)
  obtain ⟨T₀, hT₀⟩ := Open.exists_T u₁ (s.getReg .x11)
  have h₀ := hv T₀ hT₀
  generalize (TM.sumcheck cl.value 3 (List.replicate 4 none)).run T₀ = o at h₀
  rcases o with _ | ⟨⟨low, sv⟩, T₀'⟩
  · exact absurd h₀ hcap
  obtain ⟨-, hlow, hsv, -⟩ := h₀
  have hp8 : s.getReg .x2 - 3296 + 8 = s.getReg .x2 - 3288 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hp16 : s.getReg .x2 - 3296 + 16 = s.getReg .x2 - 3280 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hp24 : s.getReg .x2 - 3296 + 24 = s.getReg .x2 - 3272 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have HB₂ := HB.of_vec hpre R₂.base (Open.newVecE_mono hlow R₁.base.mono)
  simp only [vecPtr, vecLen, hp8, hp16] at HB₂
  have k4856 : u₃.getMem (s.getReg .x2 - 4856) = u.getMem (s.getReg .x2 - 4856) := by
    rw [m₃]
    have e2 : u₂.getMem (s.getReg .x2 - 4856) = u₁.getMem (s.getReg .x2 - 4856) :=
      SW.mem hpre hpost₂.heap (by decide) (J := 4856) (by decide) (by decide) (by decide) F₂
    have e1 : u₁.getMem (s.getReg .x2 - 4856) = u.getMem (s.getReg .x2 - 4856) :=
      SW.mem hpre R₁.base.heap (by decide) (J := 4856) (by decide) (by decide) (by decide)
        (slots_sw F₁)
    rw [e2, e1]
  have k5184 : u₃.getMem (s.getReg .x2 - 5184) = 2 := by
    rw [m₃]
    have e2 : u₂.getMem (s.getReg .x2 - 5184) = u₁.getMem (s.getReg .x2 - 5184) :=
      SW.mem hpre hpost₂.heap (by decide) (J := 5184) (by decide) (by decide) (by decide) F₂
    have e1 : u₁.getMem (s.getReg .x2 - 5184) = u.getMem (s.getReg .x2 - 5184) :=
      SW.mem hpre R₁.base.heap (by decide) (J := 5184) (by decide) (by decide) (by decide)
        (slots_sw F₁)
    rw [e2, e1, A.m64]
  refine ⟨u₃, hr₂.trans hr₃, Or.inl ⟨_, _, low, sv, { R₃ with
    pc := pc₃
    x18 := by rw [k₃ .x18 (by decide), hpres₂.reg .x18, k₁ .x18 (by decide), A.x18]
    x19 := by rw [k₃ .x19 (by decide), hpres₂.reg .x19, k₁ .x19 (by decide), A.x19]
    m64 := k5184
    x8 := b80009490_x8 h₃
    x20 := by
      rw [k₃ .x20 (by decide), hpres₂.reg .x20, k₁ .x20 (by decide), A.x20, k4856]
    x21 := by rw [b80009490_x21 h₃, t1968]
    x24 := by rw [b80009490_x24 h₃, t1960]
    lowB := HB.same m₃ HB₂
    sval := by rw [← hsv, hp24]; simp only [Rv64Verifier.eAt, m₃]
    rest := Rm.step fun T hT ↦ by
      have h := hv T hT
      generalize (TM.sumcheck cl.value 3 (List.replicate 4 none)).run T = o at h ⊢
      rcases o with _ | ⟨⟨pt, cv⟩, T'⟩
      · exact absurd h hcap
      obtain ⟨-, hpt, hcv, hT'⟩ := h
      have e1 : pt = low := hpt.elems.symm.trans hlow.elems
      have e2 : cv = sv := hcv.symm.trans hsv
      subst e1 e2
      exact ⟨T', rfl, Layer.transcriptAt_congr m₃ hT'⟩ }⟩⟩

/-! ## `open`, the row, `next_scalars(64)` -/

theorem SW.elist {s u v : MachineState} (hpre : VerifyKeccakPreW s) (hH : HeapOk v)
    {rs : List (Nat × Nat)} {sp : Bool} (hok : SlotsOk rs = true) (F : DFrame u v (SW s u v rs sp))
    {J n : Nat} (hJ : J ≤ 5248) (hm : 24 * n ≤ J) (hsep : SlotsSep rs J (24 * n) = true) :
    eListAt v (s.getReg .x2 - BitVec.ofNat 64 J) n = eListAt u (s.getReg .x2 - BitVec.ofNat 64 J) n := by
  have hb := bounds hpre
  exact F.eListAt ((SW.slot hpre hH hok hJ hm hsep).bytes (le_refl _) (le_refl _)
    (by addr_omega [hb, hJ, hm]))

/-- A `Vec`'s buffer allocated since the entry, its header's values `c`, `p`, `n`. -/
structure VB (s u : MachineState) (c p n : Word) : Prop where
  raw : Buf u p (c.toNat * 24) 8
  len : n.toNat ≤ c.toNat
  fresh : NewBuf s u p (c.toNat * 24) 8

theorem VB.mono {s u v : MachineState} {c p n : Word} (h : VB s u c p n)
    (hN : heapNext u ≤ heapNext v) : VB s v c p n := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Buf, NewBuf] at h1 h3
  exact ⟨by simp only [Buf]; omega, h2, by simp only [NewBuf]; omega⟩

/-- At `0x8000955c`: the slices (`s2`, `s4`, `s0`), the inputs' slot (`s11`/`s3`), the row at
`f + 416`, the value's limbs at `f + 64`, `f + 24`, `f + 16`. -/
structure J2 (s u : MachineState) (cl : KeccakClaim) (mp ml : Word) (oslot : List E) (word : E)
    (lp ll : Word) (low : List E) (qp ql : Word) (slot2 row2 : List E) (v2 : E)
    (sc sp sn : Word) (slices : List E) : Prop extends R2 s u cl mp ml oslot word where
  pc : u.pc = 0x8000955c
  m56 : u.getMem (s.getReg .x2 - 5192) = u.getMem (s.getReg .x2 - 4856)
  vl : Model.limbs v2 = (u.getMem (s.getReg .x2 - 5184), u.getMem (s.getReg .x2 - 5224),
    u.getMem (s.getReg .x2 - 5232))
  x21 : u.getReg .x21 = ll
  x24 : u.getReg .x24 = lp
  lowB : HB s u lp ll low
  x27 : u.getReg .x27 = qp
  x19 : u.getReg .x19 = ql
  slotB : HB s u qp ql slot2
  row' : eListAt u (s.getReg .x2 - 4832) 64 = row2
  x18 : u.getReg .x18 = sc
  x20 : u.getReg .x20 = sp
  x8 : u.getReg .x8 = sn
  slicesB : HB s u sp sn slices
  slicesV : VB s u sc sp sn
  rest : Rest s u (kIn3 (s.getReg .x12).toNat cl (some (instOf s ++ oslot, word)) low
    (slot2, row2, v2) slices)

theorem to_slices (hO : OpenSpec) (hMC : Runtime.MemcpySpec 0x800126e4) (hNSs : NextScalarsSpec)
    {s u : MachineState} {cl : KeccakClaim} {mp ml : Word} {oslot : List E} {word : E}
    {lp ll : Word} {low : List E} {sv : E} (hpre : VerifyKeccakPreW s)
    (A : J1 s u cl mp ml oslot word lp ll low sv) :
    ∃ t, Reaches Image.code u t ∧ ((∃ qp ql slot2 row2 v2 sc sp sn slices,
      J2 s t cl mp ml oslot word lp ll low qp ql slot2 row2 v2 sc sp sn slices) ∨ Done s t) := by
  have hb := bounds hpre
  have B := A.base
  have ho := hpre.out
  have a2 (n : Nat) (hn : n ≤ 5248) :
      s.getReg .x2 - 5248 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  -- 0x800094a4: the value to `f + 5120`, the outputs' capacity to `f + 56`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800094a4_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b800094a4_keeps h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁ .x2 (by decide)).trans B.x2
  have F₁ : DFrame u u₁ (Slots s [(128, 24), (5192, 8)]) := block_slots h₁ (by
    intro w hw
    simp only [b800094a4, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h <;> subst h <;> rv_eval [B.x2] <;> exact slots_of hpre (by decide))
  have R₁ := A.toR2.block hpre x2₁ (by decide) (by decide) (by decide) (by decide) F₁
    (regs7 k₁ (by decide))
  have hN₁ : heapNext u₁ = heapNext u := by simp only [heapNext, slots_next hpre (by decide) F₁]
  have low₁ := A.lowB.step hpre B (by decide) (slots_sw F₁) (le_of_eq hN₁.symm)
  have st (n K : Nat) (hn : n + K = 5248) (x : Word)
      (h : u₁.getMem (u.getReg .x2 + BitVec.ofNat 64 n) = x) :
      u₁.getMem (s.getReg .x2 - BitVec.ofNat 64 K) = x := by
    rw [B.x2, a2 n (by omega), show 5248 - n = K by omega] at h; exact h
  have hsv : eAt u₁ (s.getReg .x2 - BitVec.ofNat 64 128) = sv := by
    rw [← A.sval]
    unfold Rv64Verifier.eAt
    have e0 := st 5120 128 rfl _ (b800094a4_m_x2_5120 h₁)
    have e8 := st 5128 120 rfl _ (b800094a4_m_x2_5128 h₁)
    have e16 := st 5136 112 rfl _ (b800094a4_m_x2_5136 h₁)
    rw [show s.getReg .x2 - BitVec.ofNat 64 128 + 8 = s.getReg .x2 - BitVec.ofNat 64 120 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]),
      show s.getReg .x2 - BitVec.ofNat 64 128 + 16 = s.getReg .x2 - BitVec.ofNat 64 112 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]), e0, e8, e16, B.x2,
      show s.getReg .x2 - 3272 + 8 = s.getReg .x2 - 5248 + 1984 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]),
      show s.getReg .x2 - 3272 + 16 = s.getReg .x2 - 5248 + 1992 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]),
      show s.getReg .x2 - 3272 = s.getReg .x2 - 5248 + 1976 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb])]
  have m56₁ : u₁.getMem (s.getReg .x2 - 5192) = u₁.getMem (s.getReg .x2 - 4856) :=
    (st 56 5192 rfl _ (b800094a4_m_x2_56 h₁)).trans (A.x20.trans
      (SW.mem hpre R₁.base.heap (by decide) (J := 4856) (by decide) (by decide) (by decide)
        (slots_sw F₁)).symm)
  have x16₁ : u₁.getReg .x16 = BitVec.ofNat 64 2 := by
    rw [b800094a4_x16 h₁, B.x2, show s.getReg .x2 - 5248 + 64 = s.getReg .x2 - 5184 from
      a2 64 (by decide)]
    exact A.m64
  have Rm : Rest s u₁ (openRust ⟨(s.getReg .x12).toNat, 12⟩ cl 0 2
      (eAt u₁ (s.getReg .x2 - BitVec.ofNat 64 128)) >>=
        kIn2 (s.getReg .x12).toNat cl (some (instOf s ++ oslot, word)) low) := by
    rw [hsv]; exact A.rest.keep fun T hT ↦ B.block_tat hpre (by decide) F₁ hT
  obtain ⟨t, hr₂, hd | ⟨hpc₂, hpres₂, B₂, hN₂, F₂, hres⟩⟩ := open_call hO hpre R₁.base
    (b800094a4_pc h₁) (J := 4952) (V := 128) (F := 0) (C := 2) (Or.inr ⟨rfl, rfl⟩) R₁.claim R₁.lens
    (by rw [b800094a4_x10 h₁, B.x2]; rv_eval []) (by rw [b800094a4_x11 h₁, A.x9])
    (by rw [b800094a4_x12 h₁, A.x18]) (by rw [b800094a4_x13 h₁, A.x19])
    (by rw [b800094a4_x14 h₁, B.x2]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb]))
    (b800094a4_x15 h₁) x16₁ (by decide)
    (by rw [b800094a4_x17 h₁, B.x2]; exact BitVec.eq_of_toNat_eq (by addr_omega [hb])) Rm
  · exact ⟨t, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  have x2t : t.getReg .x2 = s.getReg .x2 - 5248 := (hpres₂.reg .x2).trans x2₁
  have Rt := R₁.step hpre x2t B₂.heap hN₂ (by decide) (by decide) (by decide) (by decide) F₂
    (pres7 hpres₂)
  have lowt := low₁.step hpre R₁.base (by decide) F₂ hN₂
  have m56t : t.getMem (s.getReg .x2 - 5192) = t.getMem (s.getReg .x2 - 4856) :=
    (SW.mem hpre B₂.heap (by decide) (J := 5192) (by decide) (by decide) (by decide) F₂).trans
      (m56₁.trans (SW.mem hpre B₂.heap (by decide) (J := 4856) (by decide) (by decide) (by decide)
        F₂).symm)
  have pct : t.pc = 0x800094f8 := by rw [hpc₂, returnAddress_eq, b800094a4_x1 h₁]; decide
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800094f8_spec pct (by
    rv_eval [x2t]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b800094f8_keeps h₃
  have m₃ := b800094f8_mem_same h₃
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (k₃ .x2 (by decide)).trans x2t
  have R₃ := Rt.same hpre x2₃ m₃ (regs7 k₃ (by decide))
  have x8t : t.getReg .x8 = 0xffffffffffffffff := by rw [hpres₂.reg .x8, k₁ .x8 (by decide), A.x8]
  have tag (n : Nat) (hn : n ≤ 5248) : t.getMem (t.getReg .x2 + BitVec.ofNat 64 n) =
      t.getMem (s.getReg .x2 - BitVec.ofNat 64 (5248 - n)) := by
    rw [x2t]; exact congrArg _ (a2 n hn)
  have t1952 : t.getMem (t.getReg .x2 + 1952) = t.getMem (s.getReg .x2 - 3296) := tag 1952 (by decide)
  have t1960 : t.getMem (t.getReg .x2 + 1960) = t.getMem (s.getReg .x2 - 3288) := tag 1960 (by decide)
  have t1968 : t.getMem (t.getReg .x2 + 1968) = t.getMem (s.getReg .x2 - 3280) := tag 1968 (by decide)
  rcases hres with ⟨hcap, hfails⟩ | ⟨hcap, slot2, row2, v2, hslot, hrow, hv2, hR⟩
  · -- `Err`
    have pc₃ := b800094f8_pc_taken h₃ (by rw [t1952, hcap, x8t]; rfl)
    have m48' : u₃.getMem (s.getReg .x2 - 5200) = s.getReg .x10 := R₃.m48
    have m48 : u₃.getMem (u₃.getReg .x2 + 48) = s.getReg .x10 := by
      rw [x2₃, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from a2 48 (by decide)]
      exact m48'
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800095c4_spec pc₃ (by
      rv_eval [x2₃]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₄ : MemFrame u₃ u₄ (s.getReg .x10) 24 := h₄.memFrame (by
      intro w hw
      simp only [b800095c4, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> rv_eval [m48] <;> addr_omega [ho])
    have hcap₄ := b800095c4_m2 h₄
    rw [m48] at hcap₄
    obtain ⟨w, hr₅, hw⟩ := err_exit hpre R₃.base (b800095c4_pc h₄)
      ((b800095c4_keeps h₄ .x2 (by decide)).trans x2₃) f₄ hcap₄ hfails
    exact ⟨w, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr hw⟩
  -- `Ok`: the row to `f + 416`
  have pc₃ := b800094f8_pc_not_taken h₃ (by rw [t1952, x8t]; exact hcap)
  have hp8 : s.getReg .x2 - 3296 + 8 = s.getReg .x2 - 3288 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have hp16 : s.getReg .x2 - 3296 + 16 = s.getReg .x2 - 3280 :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb])
  have slotB := HB.of_vec hpre B₂ hslot
  simp only [vecPtr, vecLen, hp8, hp16] at slotB
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009508_spec pc₃ trivial
  have k₄ := b80009508_keeps h₄
  have m₄ := b80009508_mem_same h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans x2₃
  have R₄ := R₃.same hpre x2₄ m₄ (regs7 k₄ (by decide))
  have m34 : ∀ a, u₄.getMem a = t.getMem a := fun a ↦ by rw [m₄, m₃]
  obtain ⟨w, hr₅, hd | ⟨hpc₅, hpres₅, F₅, hN₅, hrow₅⟩⟩ := memcpy_row hMC hpre R₄.base
    (b80009508_pc h₄) (D := 4832) (S := 3272) ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ (Or.inr (by decide))
    (by rw [b80009508_x10 h₄, x2₃]; exact a2 416 (by decide))
    (by rw [b80009508_x11 h₄, x2₃]; exact a2 1976 (by decide)) (b80009508_x12 h₄)
  · exact ⟨w, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr (Or.inr hd)⟩
  have x2₅ : w.getReg .x2 = s.getReg .x2 - 5248 := (hpres₅.reg .x2).trans x2₄
  have hH₅ : HeapOk w := ⟨by rw [hN₅]; exact R₄.base.heap.lo, by rw [hN₅]; exact R₄.base.heap.hi⟩
  have R₅ := R₄.step hpre x2₅ hH₅ (le_of_eq hN₅.symm) (by decide) (by decide) (by decide)
    (by decide) F₅ (pres7 hpres₅)
  have x20₅ : w.getReg .x20 = s.getReg .x2 - 1736 := by
    rw [hpres₅.reg .x20, k₄ .x20 (by decide), k₃ .x20 (by decide), hpres₂.reg .x20,
      b800094a4_x20 h₁, B.x2]
    exact a2 3512 (by decide)
  have v2w : eAt w (s.getReg .x2 - 1736) = v2 := by
    rw [← hv2]
    have e := SW.e hpre hH₅ (by decide) (J := 1736) (by decide) (by decide) (by decide) F₅
    rw [show s.getReg .x2 - BitVec.ofNat 64 1736 = s.getReg .x2 - 1736 from rfl] at e
    rw [e]; simp only [Rv64Verifier.eAt, m34]
  -- 0x8000951c: the value's limbs to `f + 64`, `f + 24`, `f + 16`, `next_scalars(64)`
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000951c_spec
    (by rw [hpc₅, returnAddress_eq, b80009508_x1 h₄]; decide) (by
      rv_eval [x2₅, x20₅]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | addr_omega [hb])
  have k₆ := b8000951c_keeps h₆
  have x2₆ : u₆.getReg .x2 = s.getReg .x2 - 5248 := (k₆ .x2 (by decide)).trans x2₅
  have F₆ : DFrame w u₆ (Slots s [(5232, 8), (5224, 8), (5184, 8)]) := block_slots h₆ (by
    intro a ha
    simp only [b8000951c, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h <;> subst h <;> rv_eval [x2₅] <;> exact slots_of hpre (by decide))
  have R₆ := R₅.block hpre x2₆ (by decide) (by decide) (by decide) (by decide) F₆
    (regs7 k₆ (by decide))
  have st (n K : Nat) (hn : n + K = 5248) (x : Word)
      (h : u₆.getMem (w.getReg .x2 + BitVec.ofNat 64 n) = x) :
      u₆.getMem (s.getReg .x2 - BitVec.ofNat 64 K) = x := by
    rw [x2₅, a2 n (by omega), show 5248 - n = K by omega] at h; exact h
  have vl₆ : Model.limbs v2 = (u₆.getMem (s.getReg .x2 - 5184), u₆.getMem (s.getReg .x2 - 5224),
      u₆.getMem (s.getReg .x2 - 5232)) := by
    rw [← v2w, limbs_eAt]
    have e64 := st 64 5184 rfl _ (b8000951c_m_x2_64 h₆)
    have e24 := st 24 5224 rfl _ (b8000951c_m_x2_24 h₆)
    have e16 := st 16 5232 rfl _ (b8000951c_m_x2_16 h₆)
    rw [x20₅] at e64 e24 e16
    simp only [Prod.mk.injEq]
    exact ⟨e64.symm, e24.symm, e16.symm⟩
  have x10₆ : u₆.getReg .x10 = s.getReg .x2 - 3296 := by rw [b8000951c_x10 h₆, x2₅]; rv_eval []
  have x11₆ : u₆.getReg .x11 = s.getReg .x11 := by rw [b8000951c_x11 h₆, R₅.x9]
  have tp : TPre 24 nextScalarsStack u₆ := R₆.base.tpre hpre 3296 x10₆ x11₆ (by decide)
    (by decide) (by decide) (by unfold openStack sumcheckStack roundPolyStack; omega) (by decide)
  obtain ⟨u₇, hr₇, ⟨hpc₇, hpres₇, hpost₇⟩ | hd⟩ := hNSs.call hr₆ (b8000951c_pc h₆) tp
  swap
  · exact ⟨u₇, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₇)))), Or.inr (Or.inr hd)⟩
  have x2₇ : u₇.getReg .x2 = s.getReg .x2 - 5248 := (hpres₇.reg .x2).trans x2₆
  have F₇ : DFrame u₆ u₇ (SW s u₆ u₇ [(3296, 24)] true) := DFrame.mono hpost₇.frame
    fun a ha ↦ tframe_sw hpre 3296 x2₆ x10₆ x11₆
      (by unfold openStack sumcheckStack roundPolyStack; omega) a ha
  have R₇ := R₆.step hpre x2₇ hpost₇.heap hpost₇.mono (by decide) (by decide) (by decide)
    (by decide) F₇ (pres7 hpres₇)
  have Rs : Rest s u₆ (TM.nextScalars kBits >>=
      kIn3 (s.getReg .x12).toNat cl (some (instOf s ++ oslot, word)) low (slot2, row2, v2)) :=
    ((hR.keep fun T hT ↦ Layer.transcriptAt_congr m34 hT).keep fun T hT ↦
      SW.tat hpre R₄.base hH₅ (le_of_eq hN₅.symm) (by decide) F₅ hT).keep fun T hT ↦
        R₅.base.block_tat hpre (by decide) F₆ hT
  have h64 : (u₆.getReg .x12).toNat = kBits := by rw [b8000951c_x12 h₆]; rfl
  have hv (T : TState) (hT : TranscriptAt u₆ (s.getReg .x11) T) :
      match (TM.nextScalars kBits).run T with
      | some (xs, T') => vecCap u₇ (s.getReg .x2 - 3296) ≠ errNiche ∧
          NewVecE u₆ u₇ (s.getReg .x2 - 3296) xs ∧ TranscriptAt u₇ (s.getReg .x11) T'
      | none => vecCap u₇ (s.getReg .x2 - 3296) = errNiche := by
    have h := hpost₇.value T (by rw [x11₆]; exact hT)
    rw [h64, x10₆, x11₆] at h
    exact h
  -- 0x80009548
  obtain ⟨u₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80009548_spec
    (by rw [hpc₇, returnAddress_eq, b8000951c_x1 h₆]; decide) (by
      rv_eval [x2₇]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₈ := b80009548_keeps h₈
  have m₈ := b80009548_mem_same h₈
  have x2₈ : u₈.getReg .x2 = s.getReg .x2 - 5248 := (k₈ .x2 (by decide)).trans x2₇
  have R₈ := R₇.same hpre x2₈ m₈ (regs7 k₈ (by decide))
  have tag7 (n : Nat) (hn : n ≤ 5248) : u₇.getMem (u₇.getReg .x2 + BitVec.ofNat 64 n) =
      u₇.getMem (s.getReg .x2 - BitVec.ofNat 64 (5248 - n)) := by
    rw [x2₇]; exact congrArg _ (a2 n hn)
  have s1952 : u₇.getMem (u₇.getReg .x2 + 1952) = u₇.getMem (s.getReg .x2 - 3296) :=
    tag7 1952 (by decide)
  have s1960 : u₇.getMem (u₇.getReg .x2 + 1960) = u₇.getMem (s.getReg .x2 - 3288) :=
    tag7 1960 (by decide)
  have s1968 : u₇.getMem (u₇.getReg .x2 + 1968) = u₇.getMem (s.getReg .x2 - 3280) :=
    tag7 1968 (by decide)
  have hr08 : Reaches Image.code u u₈ :=
    hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₇.trans hr₈)))))
  by_cases hcap : u₇.getMem (s.getReg .x2 - 3296) = errNiche
  · -- `Err`
    have pc₈ := b80009548_pc_taken h₈ (by rw [s1952, hcap]; rfl)
    have m48' : u₈.getMem (s.getReg .x2 - 5200) = s.getReg .x10 := R₈.m48
    have m48 : u₈.getMem (u₈.getReg .x2 + 48) = s.getReg .x10 := by
      rw [x2₈, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from a2 48 (by decide)]
      exact m48'
    obtain ⟨u₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b800095f4_spec pc₈ (by
      rv_eval [x2₈]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₉ : MemFrame u₈ u₉ (s.getReg .x10) 24 := h₉.memFrame (by
      intro a ha
      simp only [b800095f4, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> rv_eval [m48] <;> addr_omega [ho])
    have hcap₉ := b800095f4_m2 h₉
    rw [m48, b80009548_x10 h₈] at hcap₉
    obtain ⟨t', hr₁₀, ht'⟩ := err_exit hpre R₈.base (b800095f4_pc h₉)
      ((b800095f4_keeps h₉ .x2 (by decide)).trans x2₈) f₉ hcap₉ (Rs.fail fun T hT ↦ by
        have h := hv T hT
        generalize (TM.nextScalars kBits).run T = o at h ⊢
        rcases o with _ | ⟨xs, T'⟩
        · rfl
        · exact absurd hcap h.1)
    exact ⟨t', hr08.trans (hr₉.trans hr₁₀), Or.inr ht'⟩
  -- `Ok`
  have pc₈ := b80009548_pc_not_taken h₈ (by rw [s1952]; exact hcap)
  obtain ⟨T₀, hT₀⟩ := Open.exists_T u₆ (s.getReg .x11)
  have h₀ := hv T₀ hT₀
  generalize (TM.nextScalars kBits).run T₀ = o at h₀
  rcases o with _ | ⟨slices, T₀'⟩
  · exact absurd h₀ hcap
  obtain ⟨-, hsl, -⟩ := h₀
  have hsl' := Open.newVecE_mono hsl R₆.base.mono
  have slB := HB.of_vec hpre R₇.base hsl'
  have slV : VB s u₇ (vecCap u₇ (s.getReg .x2 - 3296)) (vecPtr u₇ (s.getReg .x2 - 3296))
      (vecLen u₇ (s.getReg .x2 - 3296)) := ⟨hsl'.vec.raw, hsl'.vec.len, hsl'.buf⟩
  simp only [vecPtr, vecLen, vecCap, hp8, hp16] at slB slV
  -- what the steps from `t` keep
  have hN₆ := slots_next hpre (by decide) F₆
  have hH₆ : HeapOk u₆ := R₆.base.heap
  have slot8 : HB s u₈ (t.getMem (s.getReg .x2 - 3288)) (t.getMem (s.getReg .x2 - 3280)) slot2 :=
    HB.same m₈ (((HB.same m34 slotB).step hpre R₄.base (by decide) F₅ (le_of_eq hN₅.symm)).step hpre
      R₅.base (by decide) (slots_sw F₆) (by simp only [heapNext, hN₆]; exact le_refl _) |>.step hpre
      R₆.base (by decide) F₇ hpost₇.mono)
  have low8 : HB s u₈ lp ll low :=
    HB.same m₈ (((HB.same m34 lowt).step hpre R₄.base (by decide) F₅
      (le_of_eq hN₅.symm)).step hpre R₅.base (by decide) (slots_sw F₆)
        (by simp only [heapNext, hN₆]; exact le_refl _) |>.step hpre R₆.base (by decide) F₇
          hpost₇.mono)
  have row8 : eListAt u₈ (s.getReg .x2 - 4832) 64 = row2 := by
    rw [← hrow]
    have e7 := SW.elist hpre hpost₇.heap (by decide) F₇ (J := 4832) (n := 64) (by decide) (by decide)
      (by decide)
    have e6 := SW.elist hpre hH₆ (by decide) (slots_sw F₆) (J := 4832) (n := 64) (by decide)
      (by decide) (by decide)
    have e8 : eListAt u₈ (s.getReg .x2 - 4832) 64 = eListAt u₇ (s.getReg .x2 - 4832) 64 := by
      simp only [eListAt, eAt, m₈]
    rw [e8, show s.getReg .x2 - 4832 = s.getReg .x2 - BitVec.ofNat 64 4832 from rfl, e7, e6, hrow₅]
    simp only [eListAt, eAt, m34]; rfl
  have m56₈ : u₈.getMem (s.getReg .x2 - 5192) = u₈.getMem (s.getReg .x2 - 4856) := by
    rw [m₈, m₈]
    have a7 : u₇.getMem (s.getReg .x2 - 5192) = u₆.getMem (s.getReg .x2 - 5192) :=
      SW.mem hpre hpost₇.heap (by decide) (J := 5192) (by decide) (by decide) (by decide) F₇
    have b7 : u₇.getMem (s.getReg .x2 - 4856) = u₆.getMem (s.getReg .x2 - 4856) :=
      SW.mem hpre hpost₇.heap (by decide) (J := 4856) (by decide) (by decide) (by decide) F₇
    have a6 : u₆.getMem (s.getReg .x2 - 5192) = w.getMem (s.getReg .x2 - 5192) :=
      SW.mem hpre hH₆ (by decide) (J := 5192) (by decide) (by decide) (by decide) (slots_sw F₆)
    have b6 : u₆.getMem (s.getReg .x2 - 4856) = w.getMem (s.getReg .x2 - 4856) :=
      SW.mem hpre hH₆ (by decide) (J := 4856) (by decide) (by decide) (by decide) (slots_sw F₆)
    have a5 : w.getMem (s.getReg .x2 - 5192) = u₄.getMem (s.getReg .x2 - 5192) :=
      SW.mem hpre hH₅ (by decide) (J := 5192) (by decide) (by decide) (by decide) F₅
    have b5 : w.getMem (s.getReg .x2 - 4856) = u₄.getMem (s.getReg .x2 - 4856) :=
      SW.mem hpre hH₅ (by decide) (J := 4856) (by decide) (by decide) (by decide) F₅
    rw [a7, b7, a6, b6, a5, b5, m34, m34, m56t]
  have vl₈ : Model.limbs v2 = (u₈.getMem (s.getReg .x2 - 5184), u₈.getMem (s.getReg .x2 - 5224),
      u₈.getMem (s.getReg .x2 - 5232)) := by
    have a1 : u₇.getMem (s.getReg .x2 - 5184) = u₆.getMem (s.getReg .x2 - 5184) :=
      SW.mem hpre hpost₇.heap (by decide) (J := 5184) (by decide) (by decide) (by decide) F₇
    have a2' : u₇.getMem (s.getReg .x2 - 5224) = u₆.getMem (s.getReg .x2 - 5224) :=
      SW.mem hpre hpost₇.heap (by decide) (J := 5224) (by decide) (by decide) (by decide) F₇
    have a3 : u₇.getMem (s.getReg .x2 - 5232) = u₆.getMem (s.getReg .x2 - 5232) :=
      SW.mem hpre hpost₇.heap (by decide) (J := 5232) (by decide) (by decide) (by decide) F₇
    rw [vl₆, m₈, m₈, m₈, a1, a2', a3]
  refine ⟨u₈, hr08, Or.inl ⟨_, _, slot2, row2, v2, _, _, _, slices, { R₈ with
    pc := pc₈
    m56 := m56₈
    vl := vl₈
    x21 := by
      rw [k₈ .x21 (by decide), hpres₇.reg .x21, k₆ .x21 (by decide), hpres₅.reg .x21,
        k₄ .x21 (by decide), k₃ .x21 (by decide), hpres₂.reg .x21, k₁ .x21 (by decide), A.x21]
    x24 := by
      rw [k₈ .x24 (by decide), hpres₇.reg .x24, k₆ .x24 (by decide), hpres₅.reg .x24,
        k₄ .x24 (by decide), k₃ .x24 (by decide), hpres₂.reg .x24, k₁ .x24 (by decide), A.x24]
    lowB := low8
    x27 := by
      rw [k₈ .x27 (by decide), hpres₇.reg .x27, k₆ .x27 (by decide), hpres₅.reg .x27,
        k₄ .x27 (by decide), b800094f8_x27 h₃, t1960]
    x19 := by
      rw [k₈ .x19 (by decide), hpres₇.reg .x19, k₆ .x19 (by decide), hpres₅.reg .x19,
        k₄ .x19 (by decide), b800094f8_x19 h₃, t1968]
    slotB := slot8
    row' := row8
    x18 := by rw [b80009548_x18 h₈, s1952]
    x20 := by rw [b80009548_x20 h₈, s1960]
    x8 := by rw [b80009548_x8 h₈, s1968]
    slicesB := HB.same m₈ slB
    slicesV := slV.mono (by simp only [heapNext, m₈]; exact le_refl _)
    rest := Rs.step fun T hT ↦ by
      have h := hv T hT
      generalize (TM.nextScalars kBits).run T = o at h ⊢
      rcases o with _ | ⟨xs, T'⟩
      · exact absurd h hcap
      obtain ⟨-, hxs, hT'⟩ := h
      have e : xs = slices := hxs.elems.symm.trans hsl.elems
      subst e
      exact ⟨T', rfl, Layer.transcriptAt_congr m₈ hT'⟩ }⟩⟩

end Rv64Verifier.Gkr.Keccak
