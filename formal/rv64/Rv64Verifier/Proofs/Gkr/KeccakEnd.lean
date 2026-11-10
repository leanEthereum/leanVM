import Rv64Verifier.Proofs.Gkr.KeccakIn

/-!
# `keccak::verify_keccak`: the inputs' check

`multilinear_eval(mu, low)`, `dot(row, slices)`, their product compared with the opened value
(`Err(23)` when it differs), up to `0x80009610` (`to_check2`).
-/

namespace Rv64Verifier.Gkr.Keccak
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F35 Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- What the end keeps: the spills, the last claim, the outputs' point and its capacity's copy at
`f + 56`, the word's limbs. -/
structure R3 (s u : MachineState) (cl : KeccakClaim) (oslot : List E) (word : E) : Prop where
  base : Base s u
  ok : OK s
  m32 : u.getMem (s.getReg .x2 - 5216) = s.getReg .x12 - 4
  m40 : u.getMem (s.getReg .x2 - 5208) = (Model.limbs word).2.2
  m48 : u.getMem (s.getReg .x2 - 5200) = s.getReg .x10
  m56 : u.getMem (s.getReg .x2 - 5192) = u.getMem (s.getReg .x2 - 4856)
  claim : ClaimOut s u (s.getReg .x2 - 4952) cl
  lens : Lens cl
  outV : NewVecE s u (s.getReg .x2 - 4856) (instOf s ++ oslot)
  x25 : u.getReg .x25 = (Model.limbs word).2.1
  x26 : u.getReg .x26 = (Model.limbs word).1

theorem R3.step {s u v : MachineState} {cl : KeccakClaim} {oslot : List E} {word : E}
    (hpre : VerifyKeccakPreW s) (R : R3 s u cl oslot word) (hx2 : v.getReg .x2 = s.getReg .x2 - 5248)
    (hH : HeapOk v) (hN : heapNext u ≤ heapNext v) {rs : List (Nat × Nat)} {spb : Bool}
    (hok : SlotsOk rs = true) (h1 : SlotsSep rs 5216 32 = true) (h3 : SlotsSep rs 4952 96 = true)
    (h4 : SlotsSep rs 4856 24 = true) (F : DFrame u v (SW s u v rs spb))
    (h25 : v.getReg .x25 = u.getReg .x25) (h26 : v.getReg .x26 = u.getReg .x26) :
    R3 s v cl oslot word :=
  { base := R.base.step hpre hx2 hH hN hok F
    ok := R.ok
    m32 := (SW.mem hpre hH hok (J := 5216) (by decide) (by decide)
      (SlotsSep.sub h1 (le_refl _) (by omega)) F).trans R.m32
    m40 := (SW.mem hpre hH hok (J := 5208) (by decide) (by decide)
      (SlotsSep.sub h1 (by omega) (by omega)) F).trans R.m40
    m48 := (SW.mem hpre hH hok (J := 5200) (by decide) (by decide)
      (SlotsSep.sub h1 (by omega) (by omega)) F).trans R.m48
    m56 := (SW.mem hpre hH hok (J := 5192) (by decide) (by decide)
      (SlotsSep.sub h1 (by omega) (by omega)) F).trans (R.m56.trans
        (SW.mem hpre hH hok (J := 4856) (by decide) (by decide)
          (SlotsSep.sub h4 (le_refl _) (by omega)) F).symm)
    claim := ClaimOut.step hpre R.base hH hN hok (J := 4952) (by decide) (by decide) h3 F R.claim
    lens := R.lens
    outV := SW.vec hpre R.base hH hN hok (J := 4856) (by decide) (by decide) h4 F R.outV
    x25 := h25.trans R.x25
    x26 := h26.trans R.x26 }

theorem R3.same {s u v : MachineState} {cl : KeccakClaim} {oslot : List E} {word : E}
    (hpre : VerifyKeccakPreW s) (R : R3 s u cl oslot word) (hx2 : v.getReg .x2 = s.getReg .x2 - 5248)
    (hm : ∀ a, v.getMem a = u.getMem a) (h25 : v.getReg .x25 = u.getReg .x25)
    (h26 : v.getReg .x26 = u.getReg .x26) : R3 s v cl oslot word := by
  have hN : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact R.step hpre hx2 ⟨by rw [hN]; exact R.base.heap.lo, by rw [hN]; exact R.base.heap.hi⟩
    (le_of_eq hN.symm) (rs := []) (spb := false) (by decide) (by decide) (by decide) (by decide)
    (DFrame.of_same hm _) h25 h26

/-- At `0x80009610`: checked, the inputs' parts in registers. -/
structure K2 (s u : MachineState) (cl : KeccakClaim) (oslot : List E) (word : E)
    (lp ll : Word) (low : List E) (qp ql : Word) (slot2 : List E) (sc sp sn : Word)
    (slices : List E) : Prop extends R3 s u cl oslot word where
  pc : u.pc = 0x80009610
  x8 : u.getReg .x8 = s.getReg .x10
  x24 : u.getReg .x24 = lp
  x21 : u.getReg .x21 = ll
  lowB : HB s u lp ll low
  x27 : u.getReg .x27 = qp
  x19 : u.getReg .x19 = ql
  slotB : HB s u qp ql slot2
  x18 : u.getReg .x18 = sc
  x20 : u.getReg .x20 = sp
  x22 : u.getReg .x22 = sn
  slicesB : HB s u sp sn slices
  slicesV : VB s u sc sp sn
  rest : Rest s u (pure ⟨some (instOf s ++ oslot, word),
    (low ++ cl.point.take ((s.getReg .x12).toNat - 4) ++ slot2, slices)⟩)

theorem HB.apart {s u : MachineState} {p n : Word} {xs : List E} (h : HB s u p n xs) {lo : Word}
    {m : Nat} (hl : heapEnd ≤ lo.toNat) : Apart p (24 * n.toNat) lo m := by
  rcases h.reg with h0 | ⟨-, hA⟩
  · exact Or.inl (by omega)
  · exact hA _ _ hl

theorem apart_symm {a b : Word} {n m : Nat} (h : Apart a n b m) : Apart b m a n := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-- A block writing only the result's first 24 bytes. -/
theorem Base.outw {s u v : MachineState} (hpre : VerifyKeccakPreW s) (B : Base s u)
    (hx2 : v.getReg .x2 = s.getReg .x2 - 5248) (f : MemFrame u v (s.getReg .x10) 24) : Base s v := by
  have hb := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hN : v.getMem nextAddr = u.getMem nextAddr := f _ (by addr_omega [ho, hpre.outFree])
  exact B.next hpre hx2
    ⟨by simp only [heapNext, hN]; exact B.heap.lo, by simp only [heapNext, hN]; exact B.heap.hi⟩
    (by simp only [heapNext, hN]; exact le_refl _) (DFrame.of_memFrame f) fun a ha ↦
      ⟨Or.inl (by addr_omega [ha]), by unfold verifyKeccakStack at hb hos; addr_omega [ha, hos, hb]⟩

/-- `0x8000959c`: `Err` stored through `s0`, returned. -/
theorem err959c {s y : MachineState} (hpre : VerifyKeccakPreW s) (By : Base s y)
    (hpc : y.pc = 0x8000959c) (hx8 : y.getReg .x8 = s.getReg .x10) {k : Word}
    (hx11 : y.getReg .x11 = k) (hk : k = 8 ∨ k = 16) (hf : Fails s) :
    ∃ t, Reaches Image.code y t ∧ Done s t := by
  have hb := bounds hpre
  have ho := hpre.out
  obtain ⟨z, hr, h⟩ := Sym.BlockSpec.reaches b8000959c_spec hpc (by
    rv_eval [hx8, hx11]
    rcases hk with rfl | rfl <;> and_intros <;> first
      | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho])
      | addr_omega [ho])
  have f : MemFrame y z (s.getReg .x10) 24 := h.memFrame (by
    intro w hw
    simp only [b8000959c, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hk with rfl | rfl <;> rcases hw with rfl | rfl <;> rv_eval [hx8, hx11] <;> addr_omega [ho])
  have hcap := b8000959c_m_x8_0 h
  rw [hx8] at hcap
  obtain ⟨t, hr', ht⟩ := err_exit hpre By (b8000959c_pc h)
    ((b8000959c_keeps h .x2 (by decide)).trans By.x2) f hcap hf
  exact ⟨t, hr.trans hr', ht⟩

/-- At `0x800096c8`: `atLow` in `a1`, `a0` and at `f + 1976`. -/
structure K1 (s u : MachineState) (cl : KeccakClaim) (oslot : List E) (word : E)
    (lp ll : Word) (low : List E) (qp ql : Word) (slot2 row2 : List E) (v2 : E)
    (sc sp sn : Word) (slices : List E) (atLow : E) : Prop extends R3 s u cl oslot word where
  pc : u.pc = 0x800096c8
  vl : Model.limbs v2 = (u.getMem (s.getReg .x2 - 5184), u.getMem (s.getReg .x2 - 5224),
    u.getMem (s.getReg .x2 - 5232))
  x24 : u.getReg .x24 = lp
  x21 : u.getReg .x21 = ll
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
  atl : Model.limbs atLow = (u.getReg .x11, u.getReg .x10, u.getMem (s.getReg .x2 - 3272))
  rest : Rest s u (TM.require (atLow * dotRust row2 slices = v2) >>= fun _ ↦
    (pure ⟨some (instOf s ++ oslot, word),
      (low ++ cl.point.take ((s.getReg .x12).toNat - 4) ++ slot2, slices)⟩ : TM KeccakOpenings))

theorem to_check2 (hME : MleEvalSpec) {s u : MachineState}
    {cl : KeccakClaim} {mp ml : Word} {oslot : List E} {word : E} {lp ll : Word} {low : List E}
    {qp ql : Word} {slot2 row2 : List E} {v2 : E} {sc sp sn : Word} {slices : List E}
    (hpre : VerifyKeccakPreW s)
    (A : J2 s u cl mp ml oslot word lp ll low qp ql slot2 row2 v2 sc sp sn slices) :
    ∃ t, Reaches Image.code u t ∧
      ((∃ atLow, K1 s t cl oslot word lp ll low qp ql slot2 row2 v2 sc sp sn slices atLow) ∨
        Done s t) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have B := A.base
  have hS := hpre.self.self
  have ho := hpre.out
  have a2 (n : Nat) (hn : n ≤ 5248) :
      s.getReg .x2 - 5248 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  have muB : HB s u mp ml cl.mu := by
    have h := HB.of_vec hpre B A.claim.mu
    simp only [vecPtr, vecLen, show s.getReg .x2 - 4952 + 8 = s.getReg .x2 - 4944 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), show s.getReg .x2 - 4952 + 16 = s.getReg .x2 - 4936 from
      BitVec.eq_of_toNat_eq (by addr_omega [hb]), A.mptr, A.mlen] at h
    exact h
  have R0 : R3 s u cl oslot word :=
    ⟨A.base, A.ok, A.m32, A.m40, A.m48, A.m56, A.claim, A.lens, A.outV, A.x25, A.x26⟩
  -- 0x8000955c: checked mode
  have hck : extractByte (s.getMem (s.getReg .x11 + 360)) 0 ≠ 0 := by
    have h := hpre.checked
    simp only [Checked] at h
    rwa [← Transcript.add_ofNat_zero (s.getReg .x11 + 360),
      Runtime.byteAt_add (by addr_omega [hS]) (by decide)] at h
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000955c_spec A.pc (by
    rv_eval [A.x9]
    exact ⟨by addr_omega [hS], Mapped.valid hS.1 (i := 360) (by decide)⟩)
  have pc₁ : u₁.pc = 0x80009564 := Sym.Expect.Holds.pc_eq h₁ (by
    rv_eval [A.x9, B.byte hpre]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hck (by
      have := congrArg BitVec.toNat (beq_iff_eq.mp h)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
      simpa using this)))
  have k₁ := b8000955c_keeps h₁
  have m₁ := b8000955c_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁ .x2 (by decide)).trans B.x2
  -- 0x80009564: `multilinear_eval(mu, low)`
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80009564_spec pc₁ trivial
  have k₂ := b80009564_keeps h₂
  have m₂ := b80009564_mem_same h₂
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 5248 := (k₂ .x2 (by decide)).trans x2₁
  have m02 : ∀ a, u₂.getMem a = u.getMem a := fun a ↦ by rw [m₂, m₁]
  have R₂ := R0.same hpre x2₂ m02 (by rw [k₂ .x25 (by decide), k₁ .x25 (by decide)])
    (by rw [k₂ .x26 (by decide), k₁ .x26 (by decide)])
  have B₂ := R₂.base
  have muB₂ := HB.same m02 muB
  have lowB₂ := HB.same m02 A.lowB
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 3296 := by rw [b80009564_x10 h₂, x2₁]; rv_eval []
  have x11₂ : u₂.getReg .x11 = mp := by rw [b80009564_x11 h₂, k₁ .x22 (by decide), A.x22]
  have x12₂ : u₂.getReg .x12 = ml := by rw [b80009564_x12 h₂, k₁ .x23 (by decide), A.x23]
  have x13₂ : u₂.getReg .x13 = lp := by rw [b80009564_x13 h₂, k₁ .x24 (by decide), A.x24]
  have x14₂ : u₂.getReg .x14 = ll := by rw [b80009564_x14 h₂, k₁ .x21 (by decide), A.x21]
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  unfold verifyKeccakStack at hb hsm hab hnx hrs
  have st₂ : heapEnd ≤ (stackLo u₂ mleEvalStack).toNat := by
    simp only [stackLo, x2₂]; unfold mleEvalStack; addr_omega [hb, hab]
  have ot₂ : heapEnd ≤ (s.getReg .x2 - 3296).toNat := by addr_omega [hb, hab]
  have apz {p n : Word} {xs : List E} {lo : Word} {m : Nat} (h : HB s u₂ p n xs)
      (hl : heapEnd ≤ lo.toNat) : Apart p (24 * n.toNat) lo m := by
    rcases h.reg with h0 | ⟨-, hA⟩
    · exact Or.inl (by omega)
    · exact hA _ _ hl
  have outz {p n : Word} {xs : List E} (h : HB s u₂ p n xs) :
      n.toNat = 0 ∨ Outside u₂ p (24 * n.toNat) := by
    by_cases hz : n.toNat = 0
    · exact Or.inl hz
    · exact Or.inr (h.outside B₂.heap hz)
  have regz {p n : Word} {xs : List E} (h : HB s u₂ p n xs) :
      n.toNat = 0 ∨ Region p (24 * n.toNat) := by
    rcases h.reg with h0 | ⟨hR, -⟩
    · exact Or.inl h0
    · exact Or.inr hR
  have hmp : MleEvalPre u₂ := {
    heap := B₂.heap
    out := by rw [x10₂]; addr_omega [hb, hsm]
    mle := by rw [x11₂, x12₂]; exact regz muB₂
    point := by rw [x13₂, x14₂]; exact regz lowB₂
    stack := hpre.stack.sub 5248 x2₂ (by unfold verifyKeccakStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by rw [x10₂]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    mleFree := by rw [x11₂, x12₂]; exact outz muB₂
    pointFree := by rw [x13₂, x14₂]; exact outz lowB₂
    outStack := by rw [x10₂]; simp only [stackLo, x2₂]; unfold mleEvalStack; addr_omega [hb]
    mleStack := by rw [x11₂, x12₂]; exact apz muB₂ st₂
    pointStack := by rw [x13₂, x14₂]; exact apz lowB₂ st₂
    mleOut := by rw [x11₂, x12₂, x10₂]; exact apz muB₂ ot₂
    pointOut := by rw [x13₂, x14₂, x10₂]; exact apz lowB₂ ot₂
    rodata := B₂.rodata hpre
    outRodata := by rw [x10₂]; addr_omega [hb, hrs] }
  obtain ⟨u₃, hr₃, ⟨hpc₃, hpres₃, hpost₃⟩ | hd⟩ := hME.call (hr₁.trans hr₂) (b80009564_pc h₂) hmp
  swap
  · exact ⟨u₃, hr₃, Or.inr (Or.inr hd)⟩
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 5248 := (hpres₃.reg .x2).trans x2₂
  have F₃ : DFrame u₂ u₃ (SW s u₂ u₃ [(3296, 32)] false) := DFrame.mono hpost₃.frame
    fun a ha ↦ cframe_sw hpre 3296 x2₂ x10₂ (by unfold mleEvalStack openStack mulStack; omega) a ha
  have R₃ := R₂.step hpre x2₃ hpost₃.heap hpost₃.mono (by decide) (by decide) (by decide)
    (by decide) F₃ (hpres₃.reg .x25) (hpres₃.reg .x26)
  have hv := hpost₃.value
  rw [x11₂, x12₂, x13₂, x14₂, muB₂.elems, lowB₂.elems, x10₂] at hv
  -- 0x80009580: the tag
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80009580_spec
    (by rw [hpc₃, returnAddress_eq, b80009564_x1 h₂]; decide) (by
      rv_eval [x2₃]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₄ := b80009580_keeps h₄
  have m₄ := b80009580_mem_same h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 5248 := (k₄ .x2 (by decide)).trans x2₃
  have R₄ := R₃.same hpre x2₄ m₄ (k₄ .x25 (by decide)) (k₄ .x26 (by decide))
  have tag : u₃.getMem (u₃.getReg .x2 + 1952) = u₃.getMem (s.getReg .x2 - 3296) := by
    rw [x2₃]; exact congrArg _ (a2 1952 (by decide))
  have tat3 : ∀ T, TranscriptAt u (s.getReg .x11) T → TranscriptAt u₄ (s.getReg .x11) T :=
    fun T hT ↦ Layer.transcriptAt_congr m₄ (SW.tat hpre B₂ hpost₃.heap hpost₃.mono (by decide) F₃
      (Layer.transcriptAt_congr m02 hT))
  have R4 := A.rest.keep tat3
  rcases hmle : multilinearEvalRust cl.mu low with _ | atLow
  · -- `Err`: the sizes differ
    rw [hmle] at hv
    have pc₄ := b80009580_pc_not_taken h₄ (by rw [tag, hv]; decide)
    have m48' : u₄.getMem (s.getReg .x2 - 5200) = s.getReg .x10 := R₄.m48
    have m48 : u₄.getMem (u₄.getReg .x2 + 48) = s.getReg .x10 := by
      rw [x2₄, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from a2 48 (by decide)]
      exact m48'
    obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80009590_spec pc₄ (by
      rv_eval [x2₄]
      rv_eval [m48']
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid ho ?_ ?_ ?_ <;> addr_omega [ho]))
    have f₅ : MemFrame u₄ u₅ (s.getReg .x10) 24 := h₅.memFrame (by
      intro w hw
      simp only [b80009590, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      rv_eval [m48]
      addr_omega [ho])
    have x2₅ : u₅.getReg .x2 = s.getReg .x2 - 5248 := (b80009590_keeps h₅ .x2 (by decide)).trans x2₄
    obtain ⟨t, hr₆, ht⟩ := err959c hpre (R₄.base.outw hpre x2₅ f₅) (b80009590_pc h₅)
      (by rw [b80009590_x8 h₅, m48]) (b80009590_x11 h₅) (Or.inr rfl) (R4.fail fun T _ ↦ by
        rw [hmle]; rfl)
    exact ⟨t, hr₃.trans (hr₄.trans (hr₅.trans hr₆)), Or.inr ht⟩
  -- `Ok`: `atLow` at `f + 1960`
  rw [hmle] at hv
  obtain ⟨htag, hat⟩ := hv
  have pc₄ := b80009580_pc_taken h₄ (by rw [tag, htag])
  have R4' : Rest s u₄ (TM.ofOption (multilinearEvalRust cl.mu low) >>= fun a ↦
      TM.require (a * dotRust row2 slices = v2) >>= fun _ ↦
        (pure ⟨some (instOf s ++ oslot, word),
          (low ++ cl.point.take ((s.getReg .x12).toNat - 4) ++ slot2, slices)⟩ : TM KeccakOpenings)) :=
    R4
  have R5r := R4'.step (x := atLow) fun T hT ↦ ⟨T, by rw [hmle]; rfl, hT⟩
  have hB4 (p n : Word) (xs : List E) (h : HB s u p n xs) : HB s u₄ p n xs :=
    (HB.same m02 h).step hpre B₂ (by decide) F₃ hpost₃.mono |> HB.same m₄
  have row₄ : eListAt u₄ (s.getReg .x2 - 4832) 64 = row2 := by
    rw [← A.row']
    have e3 := SW.elist hpre hpost₃.heap (by decide) F₃ (J := 4832) (n := 64) (by decide)
      (by decide) (by decide)
    have e4 : eListAt u₄ (s.getReg .x2 - 4832) 64 = eListAt u₃ (s.getReg .x2 - 4832) 64 := by
      simp only [eListAt, eAt, m₄]
    have e2 : eListAt u₂ (s.getReg .x2 - 4832) 64 = eListAt u (s.getReg .x2 - 4832) 64 := by
      simp only [eListAt, eAt, m02]
    rw [e4, show s.getReg .x2 - 4832 = s.getReg .x2 - BitVec.ofNat 64 4832 from rfl, e3]
    exact e2
  have kw (J : Nat) (hJ : J = 5184 ∨ J = 5224 ∨ J = 5232) :
      u₄.getMem (s.getReg .x2 - BitVec.ofNat 64 J) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 J) := by
    have hJ1 : J ≤ 5248 := by omega
    have hJ2 : 8 ≤ J := by omega
    rw [m₄, SW.mem hpre hpost₃.heap (by decide) hJ1 hJ2 (by rcases hJ with rfl | rfl | rfl <;> decide) F₃,
      m02]
  have rg (r : Reg) (h4 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x13, .x14, .x15, .x16,
      .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] :
      List Reg)) (hc : r ∈ calleeSaved)
      (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x18, .x19, .x20, .x21,
        .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h1 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16,
        .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] :
        List Reg)) : u₄.getReg r = u.getReg r := by
    rw [k₄ r h4, hpres₃.reg r hc, k₂ r h2, k₁ r h1]
  have hNu4 : heapNext u ≤ heapNext u₄ := by
    have := hpost₃.mono
    simp only [heapNext, m02] at this
    simp only [heapNext, m₄]
    exact this
  refine ⟨u₄, hr₃.trans hr₄, Or.inl ⟨atLow, { R₄ with
    pc := pc₄
    vl := by
      rw [A.vl]
      exact Prod.ext (kw 5184 (by omega)).symm (Prod.ext (kw 5224 (by omega)).symm
        (kw 5232 (by omega)).symm)
    x24 := (rg .x24 (by decide) (by decide) (by decide) (by decide)).trans A.x24
    x21 := (rg .x21 (by decide) (by decide) (by decide) (by decide)).trans A.x21
    lowB := hB4 _ _ _ A.lowB
    x27 := (rg .x27 (by decide) (by decide) (by decide) (by decide)).trans A.x27
    x19 := (rg .x19 (by decide) (by decide) (by decide) (by decide)).trans A.x19
    slotB := hB4 _ _ _ A.slotB
    row' := row₄
    x18 := (rg .x18 (by decide) (by decide) (by decide) (by decide)).trans A.x18
    x20 := (rg .x20 (by decide) (by decide) (by decide) (by decide)).trans A.x20
    x8 := (rg .x8 (by decide) (by decide) (by decide) (by decide)).trans A.x8
    slicesB := hB4 _ _ _ A.slicesB
    slicesV := A.slicesV.mono hNu4
    atl := by
      rw [← hat, limbs_eAt, b80009580_x11 h₄, b80009580_x10 h₄, x2₃, m₄]
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
    rest := R5r }⟩⟩

/-- Back from `mul` at `0x8000971c`: the product `pv` at `f + 3536`. -/
structure K15 (s u : MachineState) (cl : KeccakClaim) (oslot : List E) (word : E)
    (lp ll : Word) (low : List E) (qp ql : Word) (slot2 : List E) (v2 : E)
    (sc sp sn : Word) (slices : List E) (pv : E) : Prop extends R3 s u cl oslot word where
  pc : u.pc = 0x8000971c
  vl : Model.limbs v2 = (u.getMem (s.getReg .x2 - 5184), u.getMem (s.getReg .x2 - 5224),
    u.getMem (s.getReg .x2 - 5232))
  x24 : u.getReg .x24 = lp
  x21 : u.getReg .x21 = ll
  lowB : HB s u lp ll low
  x27 : u.getReg .x27 = qp
  x19 : u.getReg .x19 = ql
  slotB : HB s u qp ql slot2
  x18 : u.getReg .x18 = sc
  x20 : u.getReg .x20 = sp
  x22 : u.getReg .x22 = sn
  slicesB : HB s u sp sn slices
  slicesV : VB s u sc sp sn
  x9 : u.getReg .x9 = s.getReg .x2 - 1736
  pl : Model.limbs pv = (u.getMem (s.getReg .x2 - 1712), u.getMem (s.getReg .x2 - 1704),
    u.getMem (s.getReg .x2 - 1696))
  rest : Rest s u (TM.require (pv = v2) >>= fun _ ↦
    (pure ⟨some (instOf s ++ oslot, word),
      (low ++ cl.point.take ((s.getReg .x12).toNat - 4) ++ slot2, slices)⟩ : TM KeccakOpenings))

theorem to_dotmul (hD : DotSpec) (hM : MulSpec) {s u : MachineState} {cl : KeccakClaim}
    {oslot : List E} {word : E} {lp ll : Word} {low : List E} {qp ql : Word}
    {slot2 row2 : List E} {v2 : E} {sc sp sn : Word} {slices : List E} {atLow : E}
    (hpre : VerifyKeccakPreW s)
    (A : K1 s u cl oslot word lp ll low qp ql slot2 row2 v2 sc sp sn slices atLow) :
    ∃ t, Reaches Image.code u t ∧
      (K15 s t cl oslot word lp ll low qp ql slot2 v2 sc sp sn slices
        (atLow * dotRust row2 slices) ∨ Done s t) := by
  have hb := bounds hpre
  have B := A.base
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  have a2 (n : Nat) (hn : n ≤ 5248) :
      s.getReg .x2 - 5248 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  unfold verifyKeccakStack at hb hab hnx hrs
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800096c8_spec A.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₅ := b800096c8_keeps h₅
  have x2₅ : u₅.getReg .x2 = s.getReg .x2 - 5248 := (k₅ .x2 (by decide)).trans B.x2
  have F₅ : DFrame u u₅ (Slots s [(1688, 24)]) := by
    have f := b800096c8_frame h₅ (by rw [B.x2]; addr_omega [hb])
    rw [B.x2] at f
    rv_eval [] at f
    exact (DFrame.of_memFrame f).mono fun a ha ↦ ⟨(1688, 24), List.mem_singleton_self _, ha⟩
  have hN₅ := slots_next hpre (by decide) F₅
  have hH₅ : HeapOk u₅ :=
    ⟨by simp only [heapNext, hN₅]; exact B.heap.lo, by simp only [heapNext, hN₅]; exact B.heap.hi⟩
  have hle₅ : heapNext u ≤ heapNext u₅ := by simp only [heapNext, hN₅]; exact le_refl _
  have R₅ := A.toR3.step hpre x2₅ hH₅ hle₅ (by decide) (by decide) (by decide) (by decide)
    (slots_sw F₅) (k₅ .x25 (by decide)) (k₅ .x26 (by decide))
  have st5 (n K : Nat) (hn : n + K = 5248) (x : Word)
      (h : u₅.getMem (u.getReg .x2 + BitVec.ofNat 64 n) = x) :
      u₅.getMem (s.getReg .x2 - BitVec.ofNat 64 K) = x := by
    rw [B.x2, a2 n (by omega), show 5248 - n = K by omega] at h; exact h
  have at5 : eAt u₅ (s.getReg .x2 - 1688) = atLow := by
    apply eq_of_limbs
    rw [limbs_eAt, A.atl,
      show s.getReg .x2 - 1688 + 8 = s.getReg .x2 - BitVec.ofNat 64 1680 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]),
      show s.getReg .x2 - 1688 + 16 = s.getReg .x2 - BitVec.ofNat 64 1672 from
        BitVec.eq_of_toNat_eq (by addr_omega [hb]),
      show s.getReg .x2 - 1688 = s.getReg .x2 - BitVec.ofNat 64 1688 from rfl,
      st5 3560 1688 rfl _ (b800096c8_m_x2_3560 h₅), st5 3568 1680 rfl _ (b800096c8_m_x2_3568 h₅),
      st5 3576 1672 rfl _ (b800096c8_m_x2_3576 h₅), B.x2]
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> first
      | exact True.intro
      | exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  have sl₅ : HB s u₅ sp sn slices := A.slicesB.step hpre B (by decide) (slots_sw F₅) hle₅
  have row₅ : eListAt u₅ (s.getReg .x2 - 4832) 64 = row2 := by
    rw [← A.row']
    exact SW.elist hpre hH₅ (by decide) (slots_sw F₅) (J := 4832) (n := 64) (by decide)
      (by decide) (by decide)
  have x9₅ : u₅.getReg .x9 = s.getReg .x2 - 1736 := by rw [b800096c8_x9 h₅, B.x2]; rv_eval []
  have x10₅ : u₅.getReg .x10 = s.getReg .x2 - 3296 := by rw [b800096c8_x10 h₅, B.x2]; rv_eval []
  have x11₅ : u₅.getReg .x11 = s.getReg .x2 - 4832 := by rw [b800096c8_x11 h₅, B.x2]; rv_eval []
  have x12₅ : u₅.getReg .x12 = 64 := b800096c8_x12 h₅
  have x13₅ : u₅.getReg .x13 = sp := by rw [b800096c8_x13 h₅, A.x20]
  have x14₅ : u₅.getReg .x14 = sn := by rw [b800096c8_x14 h₅, A.x8]
  have hhi := hH₅.hi
  have slb := sl₅.buf
  simp only [NewBuf] at slb
  have hlo := hpre.heap.lo
  have hsn : 3 * sn.toNat = 0 ∨ (heapStart ≤ sp.toNat ∧ sp.toNat + 8 * (3 * sn.toNat) ≤ heapEnd ∧
      sp.toNat % 8 = 0) := by
    by_cases hz : sn.toNat = 0
    · left; omega
    · right; refine ⟨by omega, by omega, slb.1⟩
  have st₅ : heapEnd ≤ (stackLo u₅ dotStack).toNat := by
    simp only [stackLo, x2₅]; unfold dotStack mulStack; addr_omega [hb, hab]
  have ot₅ : heapEnd ≤ (s.getReg .x2 - 3296).toNat := by addr_omega [hb, hab]
  have hdp : DotPre u₅ := {
    ret := by rw [x10₅]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    left := by rw [x11₅, x12₅]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    right := by
      rw [x13₅, x14₅]
      rcases hsn with h0 | ⟨h1, h2, h3⟩
      · intro i hi; omega
      · exact Layer.heap_vmr h1 h2 h3
    stack := (hpre.stack.sub 5248 x2₅ (by unfold verifyKeccakStack; decide) (by decide)
      (by decide) (by decide) (by decide)).toStackOk
    retLeft := by rw [x10₅, x11₅, x12₅]; addr_omega [hb]
    retRight := by rw [x10₅, x13₅, x14₅]; exact apart_symm (sl₅.apart ot₅)
    retStack := by rw [x10₅]; simp only [stackLo, x2₅]; unfold dotStack mulStack; addr_omega [hb]
    leftStack := by
      rw [x11₅, x12₅]; simp only [stackLo, x2₅]; unfold dotStack mulStack; addr_omega [hb]
    rightStack := by rw [x13₅, x14₅]; exact sl₅.apart st₅
    rodata := R₅.base.rodata hpre
    retRodata := by rw [x10₅]; addr_omega [hb, hrs]
    stackRodata := by simp only [stackLo, x2₅]; unfold dotStack mulStack; addr_omega [hb, hrs] }
  obtain ⟨u₆, hr₆, ⟨hpc₆, hpres₆, hpost₆⟩ | hd⟩ := hD.call hr₅ (b800096c8_pc h₅) hdp
  swap
  · exact ⟨u₆, hr₆, Or.inr (Or.inr hd)⟩
  have x2₆ : u₆.getReg .x2 = s.getReg .x2 - 5248 := (hpres₆.reg .x2).trans x2₅
  have hsn64 : sn = 64 := by have := hpost₆.len; rw [x12₅, x14₅] at this; exact this.symm
  have F₆ : DFrame u₅ u₆ (SW s u₅ u₆ [(3296, 24)] false) := (DFrame.of_two hpost₆.frame).mono
    fun a ha ↦ fframe_sw hpre 3296 x2₅ x10₅ (by unfold dotStack mulStack openStack; omega) a ha
  have hN₆ : heapNext u₆ = heapNext u₅ := by
    simp only [heapNext]
    rw [hpost₆.frame _ (by rw [x10₅]; addr_omega [hb, hnx])
      (by simp only [stackLo, x2₅]; unfold dotStack mulStack; addr_omega [hb, hnx])]
  have hH₆ : HeapOk u₆ := ⟨by rw [hN₆]; exact hH₅.lo, by rw [hN₆]; exact hH₅.hi⟩
  have R₆ := R₅.step hpre x2₆ hH₆ (le_of_eq hN₆.symm) (by decide) (by decide) (by decide)
    (by decide) F₆ (hpres₆.reg .x25) (hpres₆.reg .x26)
  have hsl : eListAt u₅ sp 64 = slices := by have := sl₅.elems; rw [hsn64] at this; exact this
  have dot₆ : eAt u₆ (s.getReg .x2 - 3296) = dotRust row2 slices := by
    have h := hpost₆.value
    rw [x10₅, x11₅, x12₅, x13₅, show ((64 : Word)).toNat = 64 from rfl, row₅, hsl] at h
    exact h
  obtain ⟨u₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80009700_spec
    (by rw [hpc₆, returnAddress_eq, b800096c8_x1 h₅]; decide) trivial
  have k₇ := b80009700_keeps h₇
  have m₇ := b80009700_mem_same h₇
  have x2₇ : u₇.getReg .x2 = s.getReg .x2 - 5248 := (k₇ .x2 (by decide)).trans x2₆
  have R₇ := R₆.same hpre x2₇ m₇ (k₇ .x25 (by decide)) (k₇ .x26 (by decide))
  obtain ⟨u₈, hr₈, hd | ⟨hpc₈, hpres₈, B₈, hN₈, F₈, hprod⟩⟩ := mul_slots hM hpre R₇.base
    (b80009700_pc h₇) (Ko := 1712) (Kl := 1688) (Kr := 3296) ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ (Or.inr (by decide))
    (Or.inl (by decide)) (by rw [b80009700_x10 h₇, x2₆]; exact a2 3536 (by decide))
    (by rw [b80009700_x11 h₇, x2₆]; exact a2 3560 (by decide))
    (by rw [b80009700_x12 h₇, x2₆]; exact a2 1952 (by decide))
  · exact ⟨u₈, hr₆.trans (hr₇.trans hr₈), Or.inr (Or.inr hd)⟩
  have x2₈ : u₈.getReg .x2 = s.getReg .x2 - 5248 := (hpres₈.reg .x2).trans x2₇
  have R₈ := R₇.step hpre x2₈ B₈.heap (le_of_eq hN₈.symm) (by decide) (by decide) (by decide)
    (by decide) F₈ (hpres₈.reg .x25) (hpres₈.reg .x26)
  have at7 : eAt u₇ (s.getReg .x2 - 1688) = atLow := by
    have e6 : eAt u₆ (s.getReg .x2 - 1688) = eAt u₅ (s.getReg .x2 - 1688) :=
      SW.e hpre hH₆ (by decide) (J := 1688) (by decide) (by decide) (by decide) F₆
    rw [← at5, ← e6]; simp only [Rv64Verifier.eAt, m₇]
  have dot7 : eAt u₇ (s.getReg .x2 - 3296) = dotRust row2 slices := by
    rw [← dot₆]; simp only [Rv64Verifier.eAt, m₇]
  have prod8 : eAt u₈ (s.getReg .x2 - 1712) = atLow * dotRust row2 slices := by
    rw [← at7, ← dot7]; exact hprod
  have kw (J : Nat) (hJ : J = 5184 ∨ J = 5224 ∨ J = 5232) :
      u₈.getMem (s.getReg .x2 - BitVec.ofNat 64 J) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 J) := by
    have hJ1 : J ≤ 5248 := by omega
    have hJ2 : 8 ≤ J := by omega
    rw [SW.mem hpre B₈.heap (by decide) hJ1 hJ2 (by rcases hJ with rfl | rfl | rfl <;> decide) F₈,
      m₇, SW.mem hpre hH₆ (by decide) hJ1 hJ2 (by rcases hJ with rfl | rfl | rfl <;> decide) F₆,
      SW.mem hpre hH₅ (by decide) hJ1 hJ2 (by rcases hJ with rfl | rfl | rfl <;> decide)
        (slots_sw F₅)]
  have hB8 (p n : Word) (xs : List E) (h : HB s u p n xs) : HB s u₈ p n xs :=
    ((h.step hpre B (by decide) (slots_sw F₅) hle₅).step hpre R₅.base (by decide) F₆
      (le_of_eq hN₆.symm) |> HB.same m₇).step hpre R₇.base (by decide) F₈ (le_of_eq hN₈.symm)
  have hle8 : heapNext u ≤ heapNext u₈ := by
    rw [hN₈]; simp only [heapNext, m₇]; rw [show (u₆.getMem nextAddr).toNat = heapNext u₆ from rfl,
      hN₆]; exact hle₅
  have rg (r : Reg) (h8 : r ∈ calleeSaved) (h7 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9,
      .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27,
      .x28, .x29, .x30, .x31] : List Reg)) (h5 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x15,
      .x16, .x17, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] :
      List Reg)) : u₈.getReg r = u.getReg r := by
    rw [hpres₈.reg r h8, k₇ r h7, hpres₆.reg r h8, k₅ r h5]
  refine ⟨u₈, hr₆.trans (hr₇.trans hr₈), Or.inl { R₈ with
    pc := by rw [hpc₈, returnAddress_eq, b80009700_x1 h₇]; decide
    vl := by
      rw [A.vl]
      exact Prod.ext (kw 5184 (by omega)).symm (Prod.ext (kw 5224 (by omega)).symm
        (kw 5232 (by omega)).symm)
    x24 := (rg .x24 (by decide) (by decide) (by decide)).trans A.x24
    x21 := (rg .x21 (by decide) (by decide) (by decide)).trans A.x21
    lowB := hB8 _ _ _ A.lowB
    x27 := (rg .x27 (by decide) (by decide) (by decide)).trans A.x27
    x19 := (rg .x19 (by decide) (by decide) (by decide)).trans A.x19
    slotB := hB8 _ _ _ A.slotB
    x18 := (rg .x18 (by decide) (by decide) (by decide)).trans A.x18
    x20 := (rg .x20 (by decide) (by decide) (by decide)).trans A.x20
    x22 := by
      rw [hpres₈.reg .x22, k₇ .x22 (by decide), hpres₆.reg .x22, b800096c8_x22 h₅, A.x8]
    slicesB := hB8 _ _ _ A.slicesB
    slicesV := A.slicesV.mono hle8
    x9 := by rw [hpres₈.reg .x9, k₇ .x9 (by decide), hpres₆.reg .x9, x9₅]
    pl := by
      rw [← prod8, limbs_eAt]
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> first
        | exact True.intro
        | exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
    rest := ((A.rest.keep fun T hT ↦ B.block_tat hpre (by decide) F₅ hT).keep fun T hT ↦
      SW.tat hpre R₅.base hH₆ (le_of_eq hN₆.symm) (by decide) F₆ hT).keep fun T hT ↦
        SW.tat hpre R₇.base B₈.heap (le_of_eq hN₈.symm) (by decide) F₈
          (Layer.transcriptAt_congr m₇ hT) }⟩

theorem to_cmp {s u : MachineState} {cl : KeccakClaim} {oslot : List E} {word : E}
    {lp ll : Word} {low : List E} {qp ql : Word} {slot2 : List E} {v2 : E} {sc sp sn : Word}
    {slices : List E} {pv : E} (hpre : VerifyKeccakPreW s)
    (A : K15 s u cl oslot word lp ll low qp ql slot2 v2 sc sp sn slices pv) :
    ∃ t, Reaches Image.code u t ∧
      (K2 s t cl oslot word lp ll low qp ql slot2 sc sp sn slices ∨ Done s t) := by
  have hb := bounds hpre
  have B := A.base
  have a2 (n : Nat) (hn : n ≤ 5248) :
      s.getReg .x2 - 5248 + BitVec.ofNat 64 n = s.getReg .x2 - BitVec.ofNat 64 (5248 - n) :=
    BitVec.eq_of_toNat_eq (by addr_omega [hb, hn])
  have m48₈ : u.getMem (u.getReg .x2 + 48) = s.getReg .x10 := by
    rw [B.x2, show s.getReg .x2 - 5248 + 48 = s.getReg .x2 - 5200 from a2 48 (by decide)]
    exact A.m48
  have limb_ne {a b c : Word} (h : (a, b, c) ≠ (u.getMem (s.getReg .x2 - 5184),
      u.getMem (s.getReg .x2 - 5224), u.getMem (s.getReg .x2 - 5232)))
      (e : Model.limbs pv = (a, b, c)) : pv ≠ v2 :=
    fun h' ↦ h (by rw [← e, ← A.vl, h'])
  have e1712 : u.getMem (u.getReg .x9 + 24) = u.getMem (s.getReg .x2 - 1712) := by
    rw [A.x9]; exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  have e1704 : u.getMem (u.getReg .x9 + 32) = u.getMem (s.getReg .x2 - 1704) := by
    rw [A.x9]; exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  have e1696 : u.getMem (u.getReg .x9 + 40) = u.getMem (s.getReg .x2 - 1696) := by
    rw [A.x9]; exact congrArg _ (BitVec.eq_of_toNat_eq (by addr_omega [hb]))
  have f64 : u.getMem (u.getReg .x2 + 64) = u.getMem (s.getReg .x2 - 5184) := by
    rw [B.x2]; exact congrArg _ (a2 64 (by decide))
  have f24 : u.getMem (u.getReg .x2 + 24) = u.getMem (s.getReg .x2 - 5224) := by
    rw [B.x2]; exact congrArg _ (a2 24 (by decide))
  have f16 : u.getMem (u.getReg .x2 + 16) = u.getMem (s.getReg .x2 - 5232) := by
    rw [B.x2]; exact congrArg _ (a2 16 (by decide))
  obtain ⟨u₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b8000971c_spec A.pc (by
    rv_eval [B.x2, A.x9]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₉ := b8000971c_keeps h₉
  have m₉ := b8000971c_mem_same h₉
  have x2₉ : u₉.getReg .x2 = s.getReg .x2 - 5248 := (k₉ .x2 (by decide)).trans B.x2
  have R₉ := A.toR3.same hpre x2₉ m₉ (k₉ .x25 (by decide)) (k₉ .x26 (by decide))
  have x8₉ : u₉.getReg .x8 = s.getReg .x10 := by rw [b8000971c_x8 h₉, m48₈]
  by_cases c1 : u.getMem (s.getReg .x2 - 1712) = u.getMem (s.getReg .x2 - 5184)
  swap
  · obtain ⟨t, hr, ht⟩ := err959c hpre R₉.base (b8000971c_pc_taken h₉ (by rw [e1712, f64]; exact c1))
      x8₉ (b8000971c_x11 h₉) (Or.inl rfl) (A.rest.require_fail (limb_ne
        (fun h ↦ c1 (Prod.mk.inj h).1) A.pl))
    exact ⟨t, hr₉.trans hr, Or.inr ht⟩
  obtain ⟨u₁₀, hr₁₀, h₁₀⟩ := Sym.BlockSpec.reaches b80009734_spec
    (b8000971c_pc_not_taken h₉ (by rw [e1712, f64]; exact c1)) (by
      rv_eval [x2₉, k₉ .x9 (by decide), A.x9]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁₀ := b80009734_keeps h₁₀
  have m₁₀ := b80009734_mem_same h₁₀
  have x2₁₀ : u₁₀.getReg .x2 = s.getReg .x2 - 5248 := (k₁₀ .x2 (by decide)).trans x2₉
  have m810 : ∀ a, u₁₀.getMem a = u.getMem a := fun a ↦ by rw [m₁₀, m₉]
  have R₁₀ := A.toR3.same hpre x2₁₀ m810 (by rw [k₁₀ .x25 (by decide), k₉ .x25 (by decide)])
    (by rw [k₁₀ .x26 (by decide), k₉ .x26 (by decide)])
  have c2' : u₉.getMem (u₉.getReg .x9 + 32) = u₉.getMem (u₉.getReg .x2 + 24) ↔
      u.getMem (s.getReg .x2 - 1704) = u.getMem (s.getReg .x2 - 5224) := by
    rw [m₉, m₉, k₉ .x9 (by decide), k₉ .x2 (by decide), e1704, f24]
  by_cases c2 : u.getMem (s.getReg .x2 - 1704) = u.getMem (s.getReg .x2 - 5224)
  swap
  · obtain ⟨t, hr, ht⟩ := err959c hpre R₁₀.base (b80009734_pc_taken h₁₀ (fun h ↦ c2 (c2'.mp h)))
      (by rw [k₁₀ .x8 (by decide), x8₉]) (by rw [k₁₀ .x11 (by decide), b8000971c_x11 h₉])
      (Or.inl rfl) (A.rest.require_fail (limb_ne
        (fun h ↦ c2 (Prod.mk.inj (Prod.mk.inj h).2).1) A.pl))
    exact ⟨t, hr₉.trans (hr₁₀.trans hr), Or.inr ht⟩
  obtain ⟨u₁₁, hr₁₁, h₁₁⟩ := Sym.BlockSpec.reaches b80009740_spec
    (b80009734_pc_not_taken h₁₀ (c2'.mpr c2)) (by
      rv_eval [x2₁₀, k₁₀ .x9 (by decide), k₉ .x9 (by decide), A.x9]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁₁ := b80009740_keeps h₁₁
  have m₁₁ := b80009740_mem_same h₁₁
  have x2₁₁ : u₁₁.getReg .x2 = s.getReg .x2 - 5248 := (k₁₁ .x2 (by decide)).trans x2₁₀
  have m811 : ∀ a, u₁₁.getMem a = u.getMem a := fun a ↦ by rw [m₁₁, m810]
  have c3' : u₁₀.getMem (u₁₀.getReg .x9 + 40) = u₁₀.getMem (u₁₀.getReg .x2 + 16) ↔
      u.getMem (s.getReg .x2 - 1696) = u.getMem (s.getReg .x2 - 5232) := by
    rw [m810, m810, k₁₀ .x9 (by decide), k₉ .x9 (by decide), k₁₀ .x2 (by decide),
      k₉ .x2 (by decide), e1696, f16]
  by_cases c3 : u.getMem (s.getReg .x2 - 1696) = u.getMem (s.getReg .x2 - 5232)
  swap
  · obtain ⟨u₁₂, hr₁₂, h₁₂⟩ := Sym.BlockSpec.reaches b8000974c_spec
      (b80009740_pc_not_taken h₁₁ (fun h ↦ c3 (c3'.mp h))) trivial
    have k₁₂ := b8000974c_keeps h₁₂
    have x2₁₂ : u₁₂.getReg .x2 = s.getReg .x2 - 5248 := (k₁₂ .x2 (by decide)).trans x2₁₁
    have m812 : ∀ a, u₁₂.getMem a = u.getMem a := fun a ↦ by rw [b8000974c_mem_same h₁₂, m811]
    have R₁₂ := A.toR3.same hpre x2₁₂ m812
      (by rw [k₁₂ .x25 (by decide), k₁₁ .x25 (by decide), k₁₀ .x25 (by decide), k₉ .x25 (by decide)])
      (by rw [k₁₂ .x26 (by decide), k₁₁ .x26 (by decide), k₁₀ .x26 (by decide), k₉ .x26 (by decide)])
    obtain ⟨t, hr, ht⟩ := err959c hpre R₁₂.base (b8000974c_pc h₁₂)
      (by rw [k₁₂ .x8 (by decide), k₁₁ .x8 (by decide), k₁₀ .x8 (by decide), x8₉])
      (by rw [k₁₂ .x11 (by decide), k₁₁ .x11 (by decide), k₁₀ .x11 (by decide), b8000971c_x11 h₉])
      (Or.inl rfl) (A.rest.require_fail (limb_ne
        (fun h ↦ c3 (Prod.mk.inj (Prod.mk.inj h).2).2) A.pl))
    exact ⟨t, hr₉.trans (hr₁₀.trans (hr₁₁.trans (hr₁₂.trans hr))), Or.inr ht⟩
  have heq : pv = v2 := by
    apply eq_of_limbs
    rw [A.pl, A.vl, c1, c2, c3]
  have R₁₁ := A.toR3.same hpre x2₁₁ m811
    (by rw [k₁₁ .x25 (by decide), k₁₀ .x25 (by decide), k₉ .x25 (by decide)])
    (by rw [k₁₁ .x26 (by decide), k₁₀ .x26 (by decide), k₉ .x26 (by decide)])
  refine ⟨u₁₁, hr₉.trans (hr₁₀.trans hr₁₁), Or.inl { R₁₁ with
    pc := b80009740_pc_taken h₁₁ (c3'.mpr c3)
    x8 := by rw [k₁₁ .x8 (by decide), k₁₀ .x8 (by decide), x8₉]
    x24 := by rw [k₁₁ .x24 (by decide), k₁₀ .x24 (by decide), k₉ .x24 (by decide), A.x24]
    x21 := by rw [k₁₁ .x21 (by decide), k₁₀ .x21 (by decide), k₉ .x21 (by decide), A.x21]
    x27 := by rw [k₁₁ .x27 (by decide), k₁₀ .x27 (by decide), k₉ .x27 (by decide), A.x27]
    x19 := by rw [k₁₁ .x19 (by decide), k₁₀ .x19 (by decide), k₉ .x19 (by decide), A.x19]
    x18 := by rw [k₁₁ .x18 (by decide), k₁₀ .x18 (by decide), k₉ .x18 (by decide), A.x18]
    x20 := by rw [k₁₁ .x20 (by decide), k₁₀ .x20 (by decide), k₉ .x20 (by decide), A.x20]
    x22 := by rw [k₁₁ .x22 (by decide), k₁₀ .x22 (by decide), k₉ .x22 (by decide), A.x22]
    lowB := HB.same m811 A.lowB
    slotB := HB.same m811 A.slotB
    slicesB := HB.same m811 A.slicesB
    slicesV := A.slicesV.mono (by simp only [heapNext, m811]; exact le_refl _)
    rest := (A.rest.require_pass heq).keep fun T hT ↦ Layer.transcriptAt_congr m811 hT }⟩

end Rv64Verifier.Gkr.Keccak
