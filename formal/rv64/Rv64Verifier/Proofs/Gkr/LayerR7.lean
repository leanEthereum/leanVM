import Rv64Verifier.Proofs.Gkr.LayerR6

/-!
# `keccak::verify_layer`: the pack rounds' start

`keccak.rs:114-117` at `0x8000f4f8..0x8000f56c`: `kappa = sum(mu)` into `f + 912`, the product
polynomial at `s` into `f + 120` (`value`), `scale = ONE` at `f + 240`, and the challenges' `Vec`
allocated for the point's length (`try_allocate_in`, tag at `f + 960`; a failure traps).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The pack rounds' state allocated, at `0x8000f56c`. -/
structure J7 (s u : MachineState) (ip : Word) (product : List E) (c : E) : Prop where
  pc : u.pc = 0x8000f56c
  base : Base s u
  out : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  claim : u.getMem (s.getReg .x2 - 1656) = s.getReg .x15
  sponge : u.getMem (s.getReg .x2 - 1616) = s.getReg .x11 + 8
  p : u.getMem (s.getReg .x2 - 1608) = s.getReg .x11
  x9 : u.getReg .x9 = ip
  x19 : u.getReg .x19 = s.getReg .x15
  x20 : u.getReg .x20 = s.getReg .x11
  x21 : u.getReg .x21 = s.getMem (s.getReg .x15 + 40)
  x26 : u.getReg .x26 = 16
  iw : eListAt u ip 16 = instanceWeightsRust c
  ibuf : heapNext s ≤ ip.toNat ∧ ip.toNat % 8 = 0 ∧ 16 ≤ (u.getReg .x8).toNat ∧
    ip.toNat + 24 * (u.getReg .x8).toNat ≤ heapNext u
  kappa : eAt u (s.getReg .x2 - 800) = sumE (instanceWeightsRust c)
  value : eAt u (s.getReg .x2 - 1592) = polyEvalRust product c
  scale : eAt u (s.getReg .x2 - 1472) = 1
  tag : u.getMem (s.getReg .x2 - 752) = 0
  ptCap : u.getMem (s.getReg .x2 - 744) = s.getMem (s.getReg .x15 + 40)
  ptBuf : (u.getMem (s.getReg .x2 - 736)).toNat % 8 = 0 ∧
    ((s.getMem (s.getReg .x15 + 40)).toNat * 24 = 0 ∨
      ip.toNat + 24 * (u.getReg .x8).toNat ≤ (u.getMem (s.getReg .x2 - 736)).toNat ∧
      (u.getMem (s.getReg .x2 - 736)).toNat + (s.getMem (s.getReg .x15 + 40)).toNat * 24 ≤
        heapNext u)
  rest : Rest s u (packRest (claimAt s (lClaim s)) (instanceWeightsRust c)
    (sumE (instanceWeightsRust c)) 0 (polyEvalRust product c, 1, []))

/-- What the stretch writes: the frame's slots, the callees' stacks, `NEXT`, what it
allocates. -/
@[rv_addr] def RW7b (s u v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1472) 24 ∨ Within a (s.getReg .x2 - 752) 24 ∨
    Within a (s.getReg .x2 - 1712 - BitVec.ofNat 64 sumcheckStack) sumcheckStack ∨
    Within a nextAddr 8 ∨ Fresh u v a

@[rv_addr] def RW7 (s u v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 800) 24 ∨ Within a (s.getReg .x2 - 1592) 24 ∨ RW7b s u v a

set_option maxHeartbeats 16000000 in
theorem pack_start (hSum : FieldContracts.SumSpec) (hPE : MultilinearContracts.PolyEvalSpec)
    (hT : TryAllocZeroedSpec) {s u : MachineState} {pp ip : Word} {product : List E} {c : E}
    (hpre : VerifyLayerPre s) (J : J6 s u pp ip product c) :
    ∃ v, Reaches Image.code u v ∧ (J7 s v ip product c ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := J.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  simp only [stackLo] at hnx hab hrs
  unfold verifyLayerStack at hb hnx hab hrs
  have hpb := J.pbuf
  have hib := J.ibuf
  have hHu := B.heap.hi
  have hsu := B.mono
  -- `0x8000f4f8`: `kappa = sum(mu)` into `f + 912`
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000f4f8_spec J.pc (by
    rv_eval [B.x2]; valid_access hpre.stack.valid [hb])
  have k₀ := b8000f4f8_keeps h₀
  have hm₀ := b8000f4f8_mem_same h₀
  have x2₀ : t₀.getReg .x2 = s.getReg .x2 - 1712 := (k₀ .x2 (by decide)).trans B.x2
  have B₀ : Base s t₀ := B.same x2₀ hm₀
  have x8₀ : t₀.getReg .x8 = u.getMem (s.getReg .x2 - 1448) := by
    rw [b8000f4f8_x8 h₀, B.x2]; rv_eval []
  have x10₀ : t₀.getReg .x10 = s.getReg .x2 - 800 := by rw [b8000f4f8_x10 h₀, B.x2]; rv_eval []
  have x11₀ : t₀.getReg .x11 = ip := by rw [b8000f4f8_x11 h₀, J.x9]
  have x12₀ : t₀.getReg .x12 = ip + 384 := by rw [b8000f4f8_x12 h₀, J.x9, J.x26]; rv_eval []
  have hsl : FieldContracts.sumLen t₀ = 16 := by
    simp only [FieldContracts.sumLen, x11₀, x12₀]; addr_omega [hib, hHu]
  have hHs := hpre.heap.lo
  have hvi : ValidMemRange ip 48 := heap_vmr (by addr_omega [hib, hpb, hHu, hsu, hHs])
    (by addr_omega [hib, hHu]) hib.1
  have hsp : FieldContracts.SumPre t₀ := {
    out := by rw [x10₀]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    slice := by rw [hsl, x11₀]; exact hvi
    bounds := by rw [x11₀, x12₀]; addr_omega [hib, hHu]
    whole := by rw [x11₀, x12₀]; addr_omega [hib, hHu] }
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, S⟩ | hd⟩ := hSum.call hr₀ (b8000f4f8_pc h₀) hsp
  swap
  · exact ⟨_, hr₁, Or.inr hd⟩
  have F₁ := S.frame
  have V₁ := S.value
  rw [x10₀] at F₁ V₁
  rw [x11₀, hsl] at V₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (hp₁.reg .x2).trans x2₀
  have B₁ : Base s t₁ := B₀.slots hpre x2₁ F₁ (by addr_omega [hb]) (by addr_omega [hb])
  have ekappa : eAt t₁ (s.getReg .x2 - 800) = sumE (instanceWeightsRust c) := by
    rw [V₁, sumE_eq_sum, ← J.iw]
    unfold Rv64Verifier.eListAt Rv64Verifier.eAt
    simp only [hm₀]
  -- `0x8000f51c`: the product polynomial at `s` into `f + 120`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f51c_spec
    (by rw [hpc₁, returnAddress_eq, b8000f4f8_x1 h₀]; decide) trivial
  have k₂ := b8000f51c_keeps h₂
  have hm₂ := b8000f51c_mem_same h₂
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have B₂ : Base s t₂ := B₁.same x2₂ hm₂
  have x10₂ : t₂.getReg .x10 = s.getReg .x2 - 1592 := by rw [b8000f51c_x10 h₂, x2₁]; rv_eval []
  have x11₂ : t₂.getReg .x11 = pp := by
    rw [b8000f51c_x11 h₂, hp₁.reg .x21, k₀ .x21 (by decide), J.x21]
  have x12₂ : t₂.getReg .x12 = 47 := by
    rw [b8000f51c_x12 h₂, hp₁.reg .x18, k₀ .x18 (by decide), J.x18]
  have x13₂ : t₂.getReg .x13 = s.getReg .x2 - 824 := by rw [b8000f51c_x13 h₂, x2₁]; rv_eval []
  have hlo : stackLo t₂ MultilinearContracts.polyEvalStack =
      s.getReg .x2 - 1712 - BitVec.ofNat 64 MultilinearContracts.polyEvalStack := by
    simp only [stackLo, x2₂]
  have hps : (MultilinearContracts.polyEvalStack : Nat) ≤ sumcheckStack := by decide
  have hpe : MultilinearContracts.PolyEvalPre t₂ := {
    ret := by rw [x10₂]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    coeffs := by
      rw [x11₂, x12₂]
      exact heap_vmr (by addr_omega [hpb, hsu, B.heap.lo, hpre.heap.lo])
        (by addr_omega [hpb, hib, hHu]) J.palign
    point := by rw [x13₂]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    stack := (hpre.stack.sub 1712 x2₂ (by unfold verifyLayerStack; omega) (by decide)
      (by decide) (by decide) (by decide)).toStackOk
    retCoeffs := by rw [x10₂, x11₂, x12₂]; addr_omega [hb, hpb, hib, hHu, hab]
    retPoint := by rw [x10₂, x13₂]; addr_omega [hb]
    retStack := by rw [x10₂, hlo]; addr_omega [hb, hps]
    coeffsStack := by rw [x11₂, x12₂, hlo]; addr_omega [hb, hpb, hib, hHu, hab, hps]
    pointStack := by rw [x13₂, hlo]; addr_omega [hb, hps]
    rodata := B₂.rodata hpre
    retRodata := by rw [x10₂]; addr_omega [hb, hrs]
    stackRodata := by rw [hlo]; addr_omega [hb, hrs, hps] }
  obtain ⟨t₃, hr₃, ⟨hpc₃, hp₃, PE⟩ | hd⟩ := hPE.call (hr₁.trans hr₂) (b8000f51c_pc h₂) hpe
  swap
  · exact ⟨_, hr₃, Or.inr hd⟩
  have V₃ := PE.value
  rw [x10₂, x11₂, x12₂, x13₂, show (47 : Word).toNat = 47 from rfl] at V₃
  have F₃ := DFrame.of_two PE.frame
  rw [x10₂, hlo] at F₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (hp₃.reg .x2).trans x2₂
  have hN₃ : t₃.getMem nextAddr = t₂.getMem nextAddr := F₃ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx, hps]
  have B₃ : Base s t₃ := B₂.next hpre x2₃
    ⟨by simp only [heapNext, hN₃]; exact B₂.heap.lo, by simp only [heapNext, hN₃]; exact B₂.heap.hi⟩
    (by simp only [heapNext, hN₃]; exact le_refl _) F₃ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;> addr_omega [h, hb, hps]
  have F₀₂ : DFrame u t₂ (Within · (s.getReg .x2 - 800) 24) :=
    ((DFrame.of_same hm₀ _).trans (DFrame.of_memFrame F₁) fun _ h ↦ h).trans
      (DFrame.of_same hm₂ _) fun _ h ↦ h
  have evalue : eAt t₃ (s.getReg .x2 - 1592) = polyEvalRust product c := by
    rw [V₃, F₀₂.eListAt fun j hj hw ↦ by addr_omega [hw, hj, hb, hpb, hib, hHu, hab], J.prod,
      F₀₂.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb], J.sc]
  have ekappa₃ : eAt t₃ (s.getReg .x2 - 800) = sumE (instanceWeightsRust c) := by
    rw [F₃.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb, hps],
      ← ekappa]
    unfold Rv64Verifier.eAt; rw [hm₂, hm₂, hm₂]
  have x19₃ : t₃.getReg .x19 = s.getReg .x15 := by
    rw [hp₃.reg .x19, k₂ .x19 (by decide), hp₁.reg .x19, k₀ .x19 (by decide), J.x19]
  have hc := hpre.claim
  have kc (y : Word) (h1 : (lClaim s).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (lClaim s).toNat + 96) :
      t₃.getMem y = s.getMem y :=
    B₃.keep (missClaim hpre B₃.heap) (by addr_omega [hc]) h1 h2
  -- `0x8000f534`: `scale = ONE`, `try_allocate_in(point.len)` into `f + 960`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000f534_spec
    (by rw [hpc₃, returnAddress_eq, b8000f51c_x1 h₂]; decide) (by
      rv_eval [x2₃, x19₃]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have k₄ := b8000f534_keeps h₄
  have f₄ := b8000f534_frame h₄ (by rw [x2₃]; addr_omega [hb])
  rw [x2₃] at f₄
  rv_eval [] at f₄
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (k₄ .x2 (by decide)).trans x2₃
  have B₄ : Base s t₄ := B₃.slots hpre x2₄ f₄ (by addr_omega [hb]) (by addr_omega [hb])
  have n240 := b8000f534_m_x2_240 h₄
  have n248 := b8000f534_m_x2_248 h₄
  have n256 := b8000f534_m_x2_256 h₄
  rw [x2₃] at n240 n248 n256
  rv_eval [] at n240 n248 n256
  have hlen : t₃.getMem (s.getReg .x15 + 40) = s.getMem (s.getReg .x15 + 40) :=
    kc _ (by addr_omega [hc]) (by addr_omega [hc])
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 752 := by rw [b8000f534_x10 h₄, x2₃]; rv_eval []
  have x11₄ : t₄.getReg .x11 = s.getMem (s.getReg .x15 + 40) := by
    rw [b8000f534_x11 h₄, x19₃, hlen]
  have x21₄ : t₄.getReg .x21 = s.getMem (s.getReg .x15 + 40) := by
    rw [b8000f534_x21 h₄, x19₃, hlen]
  have x13₄ : t₄.getReg .x13 = 8 := b8000f534_x13 h₄
  have x14₄ : t₄.getReg .x14 = 24 := b8000f534_x14 h₄
  have pre : TryAllocPre .x13 .x14 t₄ := {
    heap := B₄.heap
    out := by rw [x10₄]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    align := by rw [x13₄]; decide
    size := by rw [x14₄]; decide
    stack := hpre.stack.sub 1712 x2₄ (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by rw [x10₄]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    outStack := by rw [x10₄]; simp only [stackLo, x2₄]; addr_omega [hb] }
  obtain ⟨t₅, hr₅, ⟨hpc₅, hp₅, TA, -⟩ | hd⟩ := hT.call (hr₃.trans hr₄) (b8000f534_pc h₄) pre
  swap
  · exact ⟨_, hr₅, Or.inr hd⟩
  have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 1712 := (hp₅.reg .x2).trans x2₄
  have B₅ : Base s t₅ := B₄.next hpre x2₅ TA.heap TA.mono (DFrame.of_byteFrame TA.frame)
    fun a ha ↦ cframe_lw hpre B₄ 752 (by decide) (by decide) (by decide) TA.heap x10₄ a ha
  -- `0x8000f564`: the tag
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000f564_spec
    (by rw [hpc₅, returnAddress_eq, b8000f534_x1 h₄]; decide) (by
      rv_eval [x2₅]; valid_access hpre.stack.valid [hb])
  have k₆ := b8000f564_keeps h₆
  have hm₆ := b8000f564_mem_same h₆
  by_cases htag : t₅.getMem (s.getReg .x2 - 752) = 0
  swap
  · exact ⟨t₆, hr₅.trans hr₆, Or.inr (dead_of_fetch (by
      rw [b8000f564_pc_taken h₆ (by rw [x2₅]; rv_eval []; exact htag)]; exact trap))⟩
  have x2₆ : t₆.getReg .x2 = s.getReg .x2 - 1712 := (k₆ .x2 (by decide)).trans x2₅
  have B₆ : Base s t₆ := B₅.same x2₆ hm₆
  obtain ⟨tcap, tbuf⟩ := TA.ok (by rw [x10₄]; exact htag)
  rw [x10₄, x11₄] at tcap
  rw [x10₄, x11₄, x13₄, x14₄] at tbuf
  have hN₆ : heapNext t₆ = heapNext t₅ := by simp only [heapNext, hm₆]
  have hN₄ : heapNext t₄ = heapNext u := by
    simp only [heapNext]
    rw [f₄ _ (by addr_omega [hb, hnx]), hN₃, hm₂, F₁ _ (by addr_omega [hb, hnx]), hm₀]
  have hN3u : heapNext t₃ = heapNext u := by
    simp only [heapNext]
    rw [hN₃, hm₂, F₁ _ (by addr_omega [hb, hnx]), hm₀]
  have G : DFrame t₃ t₆ (RW7b s t₃ t₆) :=
    (((DFrame.of_memFrame f₄).mono (w' := RW7b s t₃ t₆) fun a h ↦ Or.inl h).trans (DFrame.of_byteFrame TA.frame)
      fun a h ↦ by
        simp only [RW7b, Fresh, stackLo, x10₄, x2₄] at h ⊢
        rcases h with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [hN3u, ← hN₄]; exact h.1,
            by rw [hN₆]; exact h.2⟩)))).trans (DFrame.of_same hm₆ _) fun _ h ↦ h
  have hps' := hps
  have Fu₃ : DFrame u t₃ (RW7 s u t₆) :=
    (F₀₂.mono (w' := RW7 s u t₆) fun a h ↦ Or.inl h).trans F₃ fun a h ↦ by
      simp only [RW7, RW7b]
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb, hps'])))))
  have Fu : DFrame u t₆ (RW7 s u t₆) :=
    Fu₃.trans G fun a h ↦ Or.inr (Or.inr (by simp only [RW7b, Fresh, hN3u] at h ⊢; exact h))
  have hH₆ := B₆.heap.hi
  have keep (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1592) : t₆.getMem y = u.getMem y :=
    Fu y fun i hi hw ↦ by
      simp only [RW7, RW7b, Fresh] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, h1, h2, hnx, hH₆, hab]
  have kG (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1472 ∨
        (s.getReg .x2).toNat - 1448 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 752) :
      t₆.getMem y = t₃.getMem y :=
    G y fun i hi hw ↦ by
      simp only [RW7b, Fresh] at hw
      rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, h1, h2, hnx, hH₆, hab]
  have x8₆ : t₆.getReg .x8 = u.getMem (s.getReg .x2 - 1448) := by
    rw [k₆ .x8 (by decide), hp₅.reg .x8, k₄ .x8 (by decide), hp₃.reg .x8, k₂ .x8 (by decide),
      hp₁.reg .x8, x8₀]
  have regs (r : Reg) (hr : r ∈ [Reg.x9, .x19, .x20, .x26]) : t₆.getReg r = u.getReg r := by
    rw [k₆ r (mem_of_mem hr _), hp₅.reg r (mem_of_mem hr _), k₄ r (mem_of_mem hr _),
      hp₃.reg r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), hp₁.reg r (mem_of_mem hr _),
      k₀ r (mem_of_mem hr _)]
  have hm56 := TA.mono
  simp only [NewBuf] at tbuf
  rv_eval [] at tcap tbuf
  refine ⟨t₆, hr₅.trans hr₆, Or.inl {
    pc := b8000f564_pc_not_taken h₆ (by rw [x2₅]; rv_eval []; exact htag)
    base := B₆
    out := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]), J.out]
    claim := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]), J.claim]
    sponge := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]), J.sponge]
    p := by rw [keep _ (by addr_omega [hb]) (by addr_omega [hb]), J.p]
    x9 := (regs .x9 (by decide)).trans J.x9
    x19 := (regs .x19 (by decide)).trans J.x19
    x20 := (regs .x20 (by decide)).trans J.x20
    x21 := by rw [k₆ .x21 (by decide), hp₅.reg .x21, x21₄]
    x26 := (regs .x26 (by decide)).trans J.x26
    iw := by
      rw [← J.iw]
      exact Fu.eListAt fun j hj hw ↦ by
        simp only [RW7, RW7b, Fresh] at hw
        rcases hw with hw | hw | hw | hw | hw | hw | hw <;>
          addr_omega [hw, hj, hb, hnx, hH₆, hab, hib, hHu]
    ibuf := by
      rw [x8₆, hN₆]
      exact ⟨by omega, hib.1, hib.2.1, by omega⟩
    kappa := by
      rw [← ekappa₃]
      exact G.eAt fun j hj hw ↦ by
        simp only [RW7b, Fresh] at hw
        rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hj, hb, hnx, hH₆, hab]
    value := by
      rw [← evalue]
      exact G.eAt fun j hj hw ↦ by
        simp only [RW7b, Fresh] at hw
        rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hj, hb, hnx, hH₆, hab]
    scale := by
      apply eAt_eq_of_limbs
      rw [limbs_one]
      rv_eval []
      have e6 (y : Word) (h1 : (s.getReg .x2).toNat - 1472 ≤ y.toNat)
          (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448) : t₆.getMem y = t₄.getMem y := by
        rw [hm₆]
        exact DFrame.of_byteFrame TA.frame y fun i hi hw ↦ by
          simp only [Fresh, stackLo, x10₄, x2₄] at hw
          rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, hb, h1, h2, hnx, TA.heap.hi, hab]
      rw [e6 _ (by addr_omega [hb]) (by addr_omega [hb]), e6 _ (by addr_omega [hb]) (by addr_omega [hb]),
        e6 _ (by addr_omega [hb]) (by addr_omega [hb]), n240, n248, n256]
    tag := by rw [hm₆]; exact htag
    ptCap := by rw [hm₆]; exact tcap
    ptBuf := by
      rw [hm₆, x8₆, hN₆]
      rw [hN₄] at tbuf
      exact ⟨tbuf.1, by omega⟩
    rest := Rest.body hpre B B₆ (Fu.mono fun a h ↦ by
      simp only [RW7, RW7b, BodyW, Fresh] at h ⊢
      rcases h with h | h | h | h | h | h | h
      · exact Or.inl (by unfold verifyLayerStack; addr_omega [h, hb])
      · exact Or.inl (by unfold verifyLayerStack; addr_omega [h, hb])
      · exact Or.inl (by unfold verifyLayerStack; addr_omega [h, hb])
      · exact Or.inl (by unfold verifyLayerStack; addr_omega [h, hb])
      · exact Or.inl (by unfold verifyLayerStack; addr_omega [h, hb])
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) J.rest }⟩

end Rv64Verifier.Gkr.Layer
