import Rv64Verifier.Proofs.Gkr.OpenZero

/-!
# `keccak::open`: the loops

Per segment `g` (`0x800103ac`), per chunk `l` of 64 weights (`0x800103e4`): the scale
`segments[g] * slots[25 (first + g) + l]` into `f + 1728` by `mul`, then per position `z`
(`0x8001043c`) the product of the scale and the weight into `f + 88`, added to `row[z]`. The heads'
invariants are `OI`, `MI` and `II`, each the row after the mirror's folds so far (`OpenRow.lean`).
-/

namespace Rv64Verifier.Gkr.Open
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F75
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- What a loop step writes: `f + 80 .. f + 112`, the row, the scale, `mul`'s stack. -/
@[rv_addr] def LW2 (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1776) 32 ∨ Within a (s.getReg .x2 - 1688) 1536 ∨
    Within a (s.getReg .x2 - 128) 24 ∨ Within a (stackLo s openStack) 1632

theorem LF.keep' {s m u v : MachineState} (hpre : OpenPre s) (h : LF s m u)
    (hf : DFrame u v (LW2 s)) (hx2 : v.getReg .x2 = s.getReg .x2 - 1856)
    (hr : ∀ r ∈ [Reg.x18, .x19, .x20, .x23], v.getReg r = u.getReg r) : LF s m v := by
  have hb := bounds hpre
  have keep (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h3 : (s.getReg .x2).toNat - 1744 ≤ y.toNat ∧
        y.toNat + 8 ≤ (s.getReg .x2).toNat - 1688 ∨ y.toNat + 8 ≤ (s.getReg .x2).toNat - 1776) :
      v.getMem y = u.getMem y :=
    hf y fun i hi hw ↦ by addr_omega [hw, hi, h1, h3, hb]
  exact {
    mid := h.mid.keep hpre (hf.mono fun a ha ↦ by
      simp only [LW2] at ha; simp only [LW]
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))) hx2
    x18 := (hr _ (by decide)).trans h.x18
    x19 := by
      rw [hr _ (by decide), keep _ (by addr_omega [hb]) (Or.inl ⟨by addr_omega [hb],
        by addr_omega [hb]⟩)]; exact h.x19
    x20 := by
      rw [hr _ (by decide), keep _ (by addr_omega [hb]) (Or.inl ⟨by addr_omega [hb],
        by addr_omega [hb]⟩)]; exact h.x20
    x23 := by
      rw [hr _ (by decide), keep _ (by addr_omega [hb]) (Or.inl ⟨by addr_omega [hb],
        by addr_omega [hb]⟩)]; exact h.x23
    sgp := by
      rw [keep _ (by addr_omega [hb]) (Or.inr (by addr_omega [hb])),
        keep _ (by addr_omega [hb]) (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.sgp
    wp := by rw [keep _ (by addr_omega [hb]) (Or.inr (by addr_omega [hb]))]; exact h.wp
    wl := by rw [keep _ (by addr_omega [hb]) (Or.inr (by addr_omega [hb]))]; exact h.wl }

theorem OI.keep {s m u v : MachineState} {g : Nat} (hpre : OpenPre s) (h : OI s m u g)
    (hf : DFrame u v (LW2 s)) (hx2 : v.getReg .x2 = s.getReg .x2 - 1856)
    (hr : ∀ r ∈ [Reg.x18, .x19, .x20, .x23], v.getReg r = u.getReg r) : LF s m v :=
  LF.keep' hpre h.toLF hf hx2 hr

/-- `.rodata` through `Mid`. -/
theorem rodata_of_mid {s m u : MachineState} (hpre : OpenPre s) (P : P2 s m) (M : Mid s m u) :
    RodataOk u := by
  have hrs := hpre.stack.rodata
  have hHm' := P.heap.hi
  have hHu' := M.heap.hi
  have monoSm := P.mono
  have mono := M.mono
  have rmM : RodataOk m := hpre.rodata.dframe P.frame fun a ha hw ↦ by
    simp only [OpenW, Fresh] at hw
    rcases hw with hw | hw | hw | hw | hw | hw <;>
      addr_omega [ha, hw, hrs, hpre.outRodata, hpre.valueRodata, hpre.selfRodata, hpre.self.self,
        hHm', monoSm]
  exact rmM.dframe M.frame fun a ha hw ↦ by
    simp only [SW, Fresh] at hw
    rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hrs, hHu', mono]

/-- The segments' and slots' buffers, from `Mid`: in the heap, below `NEXT`. -/
theorem bufs_of_mid {s m u : MachineState} (M : Mid s m u) :
    ((u.getMem (s.getReg .x2 - 1720)).toNat = 0 ∨
      heapStart ≤ (u.getMem (s.getReg .x2 - 1728)).toNat ∧
      (u.getMem (s.getReg .x2 - 1728)).toNat + 24 * (u.getMem (s.getReg .x2 - 1720)).toNat ≤
        heapNext u) ∧
      (u.getMem (s.getReg .x2 - 1728)).toNat % 8 = 0 ∧
    ((u.getMem (s.getReg .x2 - 1696)).toNat = 0 ∨
      heapStart ≤ (u.getMem (s.getReg .x2 - 1704)).toNat ∧
      (u.getMem (s.getReg .x2 - 1704)).toNat + 24 * (u.getMem (s.getReg .x2 - 1696)).toNat ≤
        heapNext u) ∧
      (u.getMem (s.getReg .x2 - 1704)).toNat % 8 = 0 ∧
    eListAt u (u.getMem (s.getReg .x2 - 1728)) (u.getMem (s.getReg .x2 - 1720)).toNat = sgOf s ∧
    eListAt u (u.getMem (s.getReg .x2 - 1704)) (u.getMem (s.getReg .x2 - 1696)).toNat =
      slOf s m := by
  have a := M.sg.vec.raw
  have al := M.sg.vec.len
  have ae := M.sg.elems
  have b := M.sl.vec.raw
  have bl := M.sl.vec.len
  have be := M.sl.elems
  simp only [RawVecOk, Buf, vecEs, vecPtr, vecLen, vecCap] at a al ae b bl be
  rv_eval [] at a al ae b bl be
  refine ⟨by omega, a.1, by omega, b.1, ae, be⟩

theorem vmr_heap {a : Word} (h1 : 0x20000000 ≤ a.toNat) (h2 : a.toNat + 24 ≤ 0x78000000)
    (h3 : a.toNat % 8 = 0) : ValidMemRange a 3 := fun i hi ↦
  (Sym.validAccess_eight _).mpr (by addr_omega [h1, h2, h3, hi])

theorem eAt_of_eListAt {u : MachineState} {p : Word} {n i : Nat} {xs : List E}
    (h : eListAt u p n = xs) (hi : i < n) : eAt u (p + BitVec.ofNat 64 (24 * i)) = xs.getD i 0 := by
  rw [← h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [eListAt_length]; exact hi),
    Option.getD_some, eListAt_getElem]

theorem ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The middle loop's head: segment `g`, `l` chunks done. -/
structure MI (s m u : MachineState) (g l : Nat) : Prop extends LF s m u where
  pc : u.pc = 0x800103e4
  x26 : u.getReg .x26 = BitVec.ofNat 64 g
  x9 : u.getReg .x9 = BitVec.ofNat 64 l
  x24 : u.getReg .x24 = BitVec.ofNat 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l)
  x22 : u.getReg .x22 = s.getMem (s.getReg .x14 + 56) + BitVec.ofNat 64 (24 * (64 * l))
  x21 : u.getReg .x21 = u.getMem (s.getReg .x2 - 1728) + BitVec.ofNat 64 (24 * g)
  x25 : u.getReg .x25 = BitVec.ofNat 64 (25 * ((s.getReg .x15).toNat + g))
  gp1 : u.getMem (s.getReg .x2 - 1776) = BitVec.ofNat 64 (g + 1)
  lt : g < (s.getReg .x16).toNat
  ll : 64 * l < (s.getMem (s.getReg .x14 + 64)).toNat
  row : eListAt u (s.getReg .x2 - 1688) 64 =
    midRow (sgOf s) (slOf s m) (claimAt s (oClaim s)).weights (s.getReg .x15).toNat g l

/-- The inner loop's head: chunk `l` of segment `g`, `z` positions done. -/
structure II (s m u : MachineState) (g l z : Nat) : Prop extends LF s m u where
  pc : u.pc = 0x8001043c
  x26 : u.getReg .x26 = BitVec.ofNat 64 g
  x9 : u.getReg .x9 = BitVec.ofNat 64 (l + 1)
  x24 : u.getReg .x24 = BitVec.ofNat 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l -
    min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l))
  x22 : u.getReg .x22 = s.getMem (s.getReg .x14 + 56) + BitVec.ofNat 64 (24 * (64 * l + z))
  x27 : u.getReg .x27 = s.getMem (s.getReg .x14 + 56) +
    BitVec.ofNat 64 (24 * (64 * l + min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l)))
  x8 : u.getReg .x8 = s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * z) + 16
  x21 : u.getReg .x21 = u.getMem (s.getReg .x2 - 1728) + BitVec.ofNat 64 (24 * g)
  x25 : u.getReg .x25 = BitVec.ofNat 64 (25 * ((s.getReg .x15).toNat + g))
  gp1 : u.getMem (s.getReg .x2 - 1776) = BitVec.ofNat 64 (g + 1)
  lt : g < (s.getReg .x16).toNat
  ll : 64 * l < (s.getMem (s.getReg .x14 + 64)).toNat
  zn : z < min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l)
  scale : eAt u (s.getReg .x2 - 128) =
    (sgOf s).getD g 0 * (slOf s m).getD (25 * ((s.getReg .x15).toNat + g) + l) 0
  row : eListAt u (s.getReg .x2 - 1688) 64 =
    inRow (sgOf s) (slOf s m) (claimAt s (oClaim s)).weights (s.getReg .x15).toNat g l z

theorem outer_step {s m u : MachineState} (hpre : OpenPre s) {g : Nat} (O : OI s m u g) :
    ∃ v, Reaches Image.code u v ∧ MI s m v g 0 := by
  have hb := bounds hpre
  have x2u := O.mid.x2
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b800103ac_spec O.pc (by
    rv_eval [x2u]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k := b800103ac_keeps h
  have f := b800103ac_frame h (by rw [x2u]; addr_omega [hb])
  rw [x2u] at f
  have hfc := hpre.firstCount
  have glt := O.lt
  have hg : g < 2 ^ 64 := by have := (s.getReg .x16).isLt; omega
  have x2v : v.getReg .x2 = s.getReg .x2 - 1856 := (k .x2 (by decide)).trans x2u
  have L := O.keep hpre ((DFrame.of_memFrame f).mono fun a ha ↦ by addr_omega [ha, hb]) x2v
    fun r hr ↦ k r (mem_of_mem hr _)
  have kv (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1776 ∨ (s.getReg .x2).toNat - 1768 ≤ y.toNat) :
      v.getMem y = u.getMem y := f y (by addr_omega [h1, h2, hb])
  have hfirst := O.mid.first
  exact ⟨v, hr, {
    toLF := L
    pc := b800103ac_pc h
    x26 := (k .x26 (by decide)).trans O.x26
    x9 := b800103ac_x9 h
    x24 := by
      rw [b800103ac_x24 h, x2u]; rv_eval []
      rw [O.wl, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat]; rfl
    x22 := by rw [b800103ac_x22 h, x2u]; rv_eval [O.wp]; simp
    x21 := by
      rw [b800103ac_x21 h, x2u, O.x26, mul24, ofNat_toNat_lt hg,
        kv (s.getReg .x2 - 1728) (by addr_omega [hb]) (Or.inr (by addr_omega [hb]))]
      rv_eval [O.sgp]
    x25 := by
      rw [b800103ac_x25 h, x2u, O.x26]
      rv_eval [hfirst]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
      have : (25 : Word).toNat = 25 := rfl
      rw [this]
      have := (s.getReg .x15).isLt
      omega
    gp1 := by
      have := b800103ac_m_x2_80 h
      rw [x2u, O.x26] at this; rv_eval [] at this
      rw [this]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : (1 : Word).toNat = 1 := rfl
      omega
    lt := glt
    ll := by have := O.wne; omega
    row := by
      rw [midRow_zero, ← O.row]
      exact (DFrame.of_memFrame f).eListAt fun i hi h ↦ by addr_omega [h, hi, hb] }⟩

theorem trap' : Image.code.fetch 0x80010534 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

set_option maxHeartbeats 2000000 in
theorem mid_step (hM : MulSpec) {s m u : MachineState} (hpre : OpenPre s) (P : P2 s m) {g l : Nat}
    (I : MI s m u g l) : ∃ v, Reaches Image.code u v ∧ (II s m v g l 0 ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  have hfc := hpre.firstCount
  have x2u := I.mid.x2
  have hL := (s.getMem (s.getReg .x14 + 64)).isLt
  have hll := I.ll
  have glt := I.lt
  have hg16 := (s.getReg .x16).isLt
  obtain ⟨bsg, bsgA, bsl, bslA, sge, sle⟩ := bufs_of_mid I.mid
  have hHu := I.mid.heap.hi
  -- `0x800103e4`, `0x800103f0`: the chunk's length into `a0`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800103e4_spec I.pc trivial
  have k₁ := b800103e4_keeps h₁
  have hm₁ := b800103e4_mem_same h₁
  obtain ⟨u₂, hr₂, pc₂, x10₂, k₂, hm₂⟩ : ∃ u₂, Reaches Image.code u u₂ ∧ u₂.pc = 0x800103f4 ∧
      u₂.getReg .x10 = BitVec.ofNat 64
        (min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l)) ∧
      (∀ r ∈ [Reg.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
        u₂.getReg r = u.getReg r) ∧ ∀ a, u₂.getMem a = u.getMem a := by
    by_cases hlt : (s.getMem (s.getReg .x14 + 64)).toNat - 64 * l < 64
    · refine ⟨u₁, hr₁, b800103e4_pc_taken h₁ (by
        rw [I.x24, ofNat_toNat_lt (by omega)]; exact hlt), ?_, fun r hr ↦ k₁ r (mem_of_mem hr _), hm₁⟩
      rw [b800103e4_x10 h₁, I.x24, Nat.min_eq_right (by omega)]
    · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800103f0_spec
        (b800103e4_pc_not_taken h₁ (by rw [I.x24, ofNat_toNat_lt (by omega)]; exact Nat.le_of_not_lt hlt))
        trivial
      refine ⟨u₂, hr₁.trans hr₂, b800103f0_pc h₂, ?_, fun r hr ↦ ?_, fun a ↦ ?_⟩
      · rw [b800103f0_x10 h₂, Nat.min_eq_left (by omega)]; rfl
      · rw [b800103f0_keeps h₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
      · rw [b800103f0_mem_same h₂, hm₁]
  -- `0x800103f4`: `segments[g]` in bounds
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800103f4_spec pc₂ trivial
  have hx19 : u₂.getReg .x19 = u.getMem (s.getReg .x2 - 1720) := by
    rw [k₂ _ (by decide), I.x19]
  have hx26 : u₂.getReg .x26 = BitVec.ofNat 64 g := by rw [k₂ _ (by decide), I.x26]
  have hg : g < 2 ^ 64 := by omega
  by_cases hgs : (u.getMem (s.getReg .x2 - 1720)).toNat ≤ g
  · exact ⟨u₃, hr₂.trans hr₃, Or.inr (dead_of_fetch (by
      rw [b800103f4_pc_taken h₃ (by rw [hx19, hx26, ofNat_toNat_lt hg]; exact hgs)]; exact trap'))⟩
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800103f8_spec
    (b800103f4_pc_not_taken h₃ (by rw [hx19, hx26, ofNat_toNat_lt hg]; omega)) trivial
  have k₃ := b800103f4_keeps h₃
  have hm₃ := b800103f4_mem_same h₃
  -- `0x800103f8`: `slots[25 (first + g) + l]` in bounds
  have hidx : (u₃.getReg .x9 + u₃.getReg .x25).toNat = 25 * ((s.getReg .x15).toNat + g) + l := by
    rw [k₃ .x9 (by decide), k₃ .x25 (by decide), k₂ .x9 (by decide), k₂ .x25 (by decide), I.x9,
      I.x25, BitVec.toNat_add, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
    omega
  have hx23 : u₃.getReg .x23 = u.getMem (s.getReg .x2 - 1696) := by
    rw [k₃ .x23 (by decide), k₂ _ (by decide), I.x23]
  by_cases his : (u.getMem (s.getReg .x2 - 1696)).toNat ≤ 25 * ((s.getReg .x15).toNat + g) + l
  · exact ⟨u₄, (hr₂.trans hr₃).trans hr₄, Or.inr (dead_of_fetch (by
      rw [b800103f8_pc_taken h₄ (by rw [hx23, hidx]; exact his)]; exact trap'))⟩
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80010400_spec
    (b800103f8_pc_not_taken h₄ (by rw [hx23, hidx]; omega)) trivial
  have k₄ := b800103f8_keeps h₄
  have hm₄ := b800103f8_mem_same h₄
  have k₅ := b80010400_keeps h₅
  have hm₅ := b80010400_mem_same h₅
  have hmu5 (a : Word) : u₅.getMem a = u.getMem a := by rw [hm₅, hm₄, hm₃, hm₂]
  have x2₅ : u₅.getReg .x2 = s.getReg .x2 - 1856 := by
    rw [k₅ .x2 (by decide), k₄ .x2 (by decide), k₃ .x2 (by decide), k₂ _ (by decide), x2u]
  have x10₅ : u₅.getReg .x10 = s.getReg .x2 - 128 := by
    rw [b80010400_x10 h₅, k₄ .x2 (by decide), k₃ .x2 (by decide), k₂ _ (by decide), x2u]; rv_eval []
  have x11₅ : u₅.getReg .x11 = u.getMem (s.getReg .x2 - 1728) + BitVec.ofNat 64 (24 * g) := by
    rw [b80010400_x11 h₅, k₄ .x21 (by decide), k₃ .x21 (by decide), k₂ _ (by decide), I.x21]
  have x12₅ : u₅.getReg .x12 = u.getMem (s.getReg .x2 - 1704) +
      BitVec.ofNat 64 (24 * (25 * ((s.getReg .x15).toNat + g) + l)) := by
    rw [b80010400_x12 h₅, b800103f8_x11 h₄, mul24, hidx, k₄ .x20 (by decide),
      k₃ .x20 (by decide), k₂ _ (by decide), I.x20]
  have rmu : RodataOk u₅ := (rodata_of_mid hpre P I.mid).dframe (DFrame.of_same hmu5 _)
    fun _ _ h ↦ h
  have hgs' : g < (u.getMem (s.getReg .x2 - 1720)).toNat := by omega
  have his' : 25 * ((s.getReg .x15).toNat + g) + l < (u.getMem (s.getReg .x2 - 1696)).toNat := by
    omega
  have hmp : MulPre u₅ := {
    out := by rw [x10₅]; valid_sub hpre.stack.valid [hb]
    lhs := by
      rw [x11₅]
      exact vmr_heap (by addr_omega [bsg, hgs']) (by addr_omega [bsg, hgs', hHu])
        (by addr_omega [bsgA, bsg, hgs'])
    rhs := by
      rw [x12₅]
      exact vmr_heap (by addr_omega [bsl, his']) (by addr_omega [bsl, his', hHu])
        (by addr_omega [bslA, bsl, his'])
    stack := ⟨by valid_sub hpre.stack.valid [hb, x2₅], by rw [x2₅]; addr_omega [hb]⟩
    outLhs := by rw [x10₅, x11₅]; addr_omega [hb, bsg, hgs', hHu, hab]
    outRhs := by rw [x10₅, x12₅]; addr_omega [hb, bsl, his', hHu, hab]
    outStack := by rw [x10₅]; simp only [stackLo, x2₅]; addr_omega [hb]
    lhsStack := by rw [x11₅]; simp only [stackLo, x2₅]; addr_omega [hb, bsg, hgs', hHu, hab]
    rhsStack := by rw [x12₅]; simp only [stackLo, x2₅]; addr_omega [hb, bsl, his', hHu, hab]
    rodata := rmu
    stackRodata := by simp only [stackLo, x2₅]; addr_omega [hb, hrs] }
  obtain ⟨v₁, hr₆, ⟨hpc₆, hpres₆, hpost₆⟩ | hd⟩ :=
    hM.call ((hr₂.trans hr₃).trans (hr₄.trans hr₅)) (b80010400_pc h₅) hmp
  swap
  · exact ⟨_, hr₆, Or.inr hd⟩
  have val := hpost₆.value
  have hEu5 (p : Word) : eAt u₅ p = eAt u p := by simp only [eAt, hmu5]
  rw [x10₅, x11₅, x12₅, hEu5, hEu5] at val
  have F₆ := DFrame.of_two hpost₆.frame
  rw [x10₅] at F₆
  simp only [stackLo, x2₅] at F₆
  obtain ⟨v, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80010438_spec
    (by rw [hpc₆, returnAddress_eq, b80010400_x1 h₅]; decide) trivial
  have k₇ := b80010438_keeps h₇
  have hm₇ := b80010438_mem_same h₇
  have Fine : DFrame u v fun a ↦ Within a (s.getReg .x2 - 128) 24 ∨
      Within a (stackLo s openStack) 1632 :=
    (((DFrame.of_same hmu5 _).trans F₆ fun a h ↦ by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by addr_omega [h, hb])).trans (DFrame.of_same hm₇ _) fun _ h ↦ h)
  have Fuv : DFrame u v (LW2 s) := Fine.mono fun a h ↦ by
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have pr (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27])
      (hr' : r ∈ calleeSaved) :
      v.getReg r = u₅.getReg r := by
    rw [k₇ r (mem_of_mem hr _),
      hpres₆ r hr']
  have back (r : Reg) (hr : r ∈ [Reg.x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26])
      (hr' : r ∈ calleeSaved) : v.getReg r = u.getReg r := by
    rw [pr r (mem_of_mem hr _) hr',
      k₅ r (mem_of_mem hr _),
      k₄ r (mem_of_mem hr _),
      k₃ r (mem_of_mem hr _),
      k₂ r (mem_of_mem hr _)]
  have x2v : v.getReg .x2 = s.getReg .x2 - 1856 := by
    rw [k₇ .x2 (by decide), hpres₆.reg .x2, x2₅]
  have Lv := LF.keep' hpre I.toLF Fuv x2v fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact back _ (by decide) (by decide)
  have kvm (y : Word) (hy8 : ∀ i < 8, ¬ (Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 128) 24 ∨
      Within (y + BitVec.ofNat 64 i) (stackLo s openStack) 1632)) :
      v.getMem y = u.getMem y := Fine y hy8
  have n0 : 0 < min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l) := by omega
  refine ⟨v, (hr₆.trans hr₇), Or.inl {
    toLF := Lv
    pc := b80010438_pc h₇
    x26 := (back .x26 (by decide) (by decide)).trans I.x26
    x9 := by
      rw [pr .x9 (by decide) (by decide), b80010400_x9 h₅, k₄ .x9 (by decide), k₃ .x9 (by decide),
        k₂ _ (by decide), I.x9]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : (1 : Word).toNat = 1 := rfl
      omega
    x24 := by
      rw [pr .x24 (by decide) (by decide), b80010400_x24 h₅, k₄ .x24 (by decide),
        k₃ .x24 (by decide), k₂ _ (by decide), I.x24, k₄ .x10 (by decide), k₃ .x10 (by decide),
        x10₂]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    x22 := by rw [back .x22 (by decide) (by decide), I.x22, Nat.add_zero]
    x27 := by
      rw [pr .x27 (by decide) (by decide), b80010400_x27 h₅, k₄ .x22 (by decide),
        k₃ .x22 (by decide), k₂ _ (by decide), I.x22, k₄ .x10 (by decide), k₃ .x10 (by decide),
        x10₂, mul24, ofNat_toNat_lt (by omega), add_ofNat_add, Nat.mul_add]
    x8 := by
      rw [b80010438_x8 h₇, hpres₆.reg .x18, k₅ .x18 (by decide), k₄ .x18 (by decide),
        k₃ .x18 (by decide), k₂ _ (by decide), I.x18]
      simp only [Nat.mul_zero]
      rv_eval []
    x21 := by
      rw [back .x21 (by decide) (by decide), I.x21, kvm _ (fun i hi h ↦ by addr_omega [h, hi, hb])]
    x25 := (back .x25 (by decide) (by decide)).trans I.x25
    gp1 := by rw [kvm _ (fun i hi h ↦ by addr_omega [h, hi, hb]), I.gp1]
    lt := glt
    ll := hll
    zn := n0
    scale := by
      have e : eAt v (s.getReg .x2 - 128) = eAt v₁ (s.getReg .x2 - 128) := by
        simp only [eAt, hm₇]
      rw [e, val, eAt_of_eListAt sge hgs', eAt_of_eListAt sle his']
    row := by
      rw [inRow_zero, ← I.row]
      exact Fine.eListAt fun i hi h ↦ by addr_omega [h, hi, hb] }⟩

/-- A chunk done, at `0x8001048c`. -/
structure CD (s m u : MachineState) (g l : Nat) : Prop extends LF s m u where
  pc : u.pc = 0x8001048c
  x26 : u.getReg .x26 = BitVec.ofNat 64 g
  x9 : u.getReg .x9 = BitVec.ofNat 64 (l + 1)
  x24 : u.getReg .x24 = BitVec.ofNat 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l -
    min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l))
  x27 : u.getReg .x27 = s.getMem (s.getReg .x14 + 56) +
    BitVec.ofNat 64 (24 * (64 * l + min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l)))
  x21 : u.getReg .x21 = u.getMem (s.getReg .x2 - 1728) + BitVec.ofNat 64 (24 * g)
  x25 : u.getReg .x25 = BitVec.ofNat 64 (25 * ((s.getReg .x15).toNat + g))
  gp1 : u.getMem (s.getReg .x2 - 1776) = BitVec.ofNat 64 (g + 1)
  lt : g < (s.getReg .x16).toNat
  ll : 64 * l < (s.getMem (s.getReg .x14 + 64)).toNat
  row : eListAt u (s.getReg .x2 - 1688) 64 =
    midRow (sgOf s) (slOf s m) (claimAt s (oClaim s)).weights (s.getReg .x15).toNat g (l + 1)

theorem eListAt_set {u v : MachineState} {R : Word} {n z : Nat} (hz : z < n)
    (hR : R.toNat + 24 * n ≤ 2 ^ 64)
    (hf : MemFrame u v (R + BitVec.ofNat 64 (24 * z)) 24) {x : E}
    (hx : eAt v (R + BitVec.ofNat 64 (24 * z)) = x) : eListAt v R n = (eListAt u R n).set z x := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i h1 h2
  rw [eListAt_length] at h1
  by_cases hi : i = z
  · subst hi; rw [List.getElem_set_self, eListAt_getElem, hx]
  · rw [List.getElem_set_ne (Ne.symm hi), eListAt_getElem, eListAt_getElem]
    exact hf.eAt (by addr_omega [hR, h1, hz, hi]) (by addr_omega [hR, h1])

set_option maxHeartbeats 2000000 in
theorem pos_step (hM : MulSpec) {s m u : MachineState} (hpre : OpenPre s) (P : P2 s m)
    {g l z : Nat} (I : II s m u g l z) :
    ∃ v, Reaches Image.code u v ∧ (II s m v g l (z + 1) ∨ CD s m v g l ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  have x2u := I.mid.x2
  have hL := (s.getMem (s.getReg .x14 + 64)).isLt
  have hll := I.ll
  have hzn := I.zn
  have wR := hpre.weights
  have wS := hpre.weightsStack
  simp only [VecRegion, VecApart, vecPtr, vecLen, oClaim] at wR wS
  rv_eval [] at wR wS
  have hR : Region (s.getMem (s.getReg .x14 + 56)) (24 * (s.getMem (s.getReg .x14 + 64)).toNat) :=
    wR.resolve_left (by omega)
  have wts := (claim_keep hpre P I.mid).2
  have hWl : (claimAt s (oClaim s)).weights.length = (s.getMem (s.getReg .x14 + 64)).toNat := by
    rw [← wts, eListAt_length]
  -- `0x8001043c`: `scale * w` into `f + 88`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8001043c_spec I.pc trivial
  have k₁ := b8001043c_keeps h₁
  have hm₁ := b8001043c_mem_same h₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 1856 := (k₁ .x2 (by decide)).trans x2u
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 1768 := by rw [b8001043c_x10 h₁, x2u]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 128 := by rw [b8001043c_x11 h₁, x2u]; rv_eval []
  have x12₁ : u₁.getReg .x12 = s.getMem (s.getReg .x14 + 56) +
      BitVec.ofNat 64 (24 * (64 * l + z)) := by rw [b8001043c_x12 h₁, I.x22]
  have hw : 64 * l + z < (s.getMem (s.getReg .x14 + 64)).toNat := by omega
  have hmp : MulPre u₁ := {
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hb]
    lhs := by rw [x11₁]; valid_sub hpre.stack.valid [hb]
    rhs := by
      rw [x12₁]
      intro i hi
      exact Region.valid hR (by addr_omega [hR, hw, hi]) (by addr_omega [hR, hw, hi])
        (by addr_omega [hR, hw, hi])
    stack := ⟨by valid_sub hpre.stack.valid [hb, x2₁], by rw [x2₁]; addr_omega [hb]⟩
    outLhs := by rw [x10₁, x11₁]; addr_omega [hb]
    outRhs := by rw [x10₁, x12₁]; addr_omega [hb, wS, hR, hw]
    outStack := by rw [x10₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    lhsStack := by rw [x11₁]; simp only [stackLo, x2₁]; addr_omega [hb]
    rhsStack := by rw [x12₁]; simp only [stackLo, x2₁]; addr_omega [hb, wS, hR, hw]
    rodata := (rodata_of_mid hpre P I.mid).dframe (DFrame.of_same hm₁ _) fun _ _ h ↦ h
    stackRodata := by simp only [stackLo, x2₁]; addr_omega [hb, hrs] }
  obtain ⟨v₁, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ := hM.call hr₁ (b8001043c_pc h₁) hmp
  swap
  · exact ⟨_, hr₂, Or.inr (Or.inr hd)⟩
  have val := hpost₂.value
  rw [x10₁, x11₁, x12₁] at val
  have e1 : eAt u₁ (s.getReg .x2 - 128) = eAt u (s.getReg .x2 - 128) := by simp only [eAt, hm₁]
  have e2 : eAt u₁ (s.getMem (s.getReg .x14 + 56) + BitVec.ofNat 64 (24 * (64 * l + z))) =
      (claimAt s (oClaim s)).weights.getD (64 * l + z) 0 := by
    simp only [eAt, hm₁]; exact eAt_of_eListAt wts hw
  rw [e1, e2, I.scale] at val
  have F₂ := DFrame.of_two hpost₂.frame
  rw [x10₁] at F₂
  simp only [stackLo, x2₁] at F₂
  have x2v₁ : v₁.getReg .x2 = s.getReg .x2 - 1856 := (hpres₂.reg .x2).trans x2₁
  have x8v₁ : v₁.getReg .x8 = s.getReg .x2 - 1688 + BitVec.ofNat 64 (24 * z) + 16 := by
    rw [hpres₂.reg .x8, k₁ .x8 (by decide), I.x8]
  -- `0x80010450`: `row[z] += product`
  obtain ⟨v, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010450_spec
    (by rw [hpc₂, returnAddress_eq, b8001043c_x1 h₁]; decide) (by
      rv_eval [x2v₁, x8v₁]
      and_intros <;> valid_access hpre.stack.valid [hb, hzn])
  have k₃ := b80010450_keeps h₃
  have f₃ := b80010450_frame h₃ (by rw [x8v₁]; addr_omega [hb, hzn])
  rw [x8v₁] at f₃
  rv_eval [] at f₃
  have m0 := b80010450_m_x8_n16 h₃
  have m8 := b80010450_m_x8_n8 h₃
  have m16 := b80010450_m_x8_0 h₃
  rw [x8v₁, x2v₁] at m0 m8 m16
  rv_eval [] at m0 m8 m16
  -- the frame of the whole step
  have Fine : DFrame u v fun a ↦ Within a (s.getReg .x2 - 1768) 24 ∨
      Within a (s.getReg .x2 - 1688) 1536 ∨ Within a (stackLo s openStack) 1632 :=
    (((DFrame.of_same hm₁ _).trans F₂ fun a h ↦ by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (by addr_omega [h, hb]))).trans (DFrame.of_memFrame f₃)
      fun a h ↦ Or.inr (Or.inl (by addr_omega [h, hb, hzn])))
  have Fuv : DFrame u v (LW2 s) := Fine.mono fun a h ↦ by
    rcases h with h | h | h
    · exact Or.inl (by addr_omega [h, hb])
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  have x2v : v.getReg .x2 = s.getReg .x2 - 1856 := (k₃ .x2 (by decide)).trans x2v₁
  have back (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27])
      (hr' : r ∈ calleeSaved) : v.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _),
      hpres₂ r hr', k₁ r (mem_of_mem hr _)]
  have Lv := LF.keep' hpre I.toLF Fuv x2v fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact back _ (by decide) (by decide)
  have kvm (y : Word) (hy8 : ∀ i < 8, ¬ (Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 1768) 24 ∨
      Within (y + BitVec.ofNat 64 i) (s.getReg .x2 - 1688) 1536 ∨
      Within (y + BitVec.ofNat 64 i) (stackLo s openStack) 1632)) :
      v.getMem y = u.getMem y := Fine y hy8
  -- the row
  have hrow : eListAt v (s.getReg .x2 - 1688) 64 =
      inRow (sgOf s) (slOf s m) (claimAt s (oClaim s)).weights (s.getReg .x15).toNat g l (z + 1) := by
    rw [inRow_succ, zf, ← I.row]
    have hz64 : z < 64 := by omega
    have h1 : eListAt v₁ (s.getReg .x2 - 1688) 64 = eListAt u (s.getReg .x2 - 1688) 64 :=
      ((DFrame.of_same hm₁ _).trans F₂ fun _ h ↦ h).eListAt fun i hi h ↦ by
        rcases h with h | h <;> addr_omega [h, hi, hb]
    rw [← h1]
    refine eListAt_set hz64 (by addr_omega [hb]) f₃ ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [eListAt_length]; exact hz64),
      Option.getD_some, eListAt_getElem, chunk_getD _ _ (by rw [hWl]; exact hzn), ← val]
    apply eAt_eq_of_limbs
    rw [limbs_add, limbs_eAt, limbs_eAt, m0, m8, m16]
    rv_eval []
    simp only [Prod.mk.injEq]
    refine ⟨BitVec.xor_comm _ _, BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩
  have x22v : v.getReg .x22 = s.getMem (s.getReg .x14 + 56) + BitVec.ofNat 64 (24 * (64 * l + (z + 1))) := by
    rw [b80010450_x22 h₃, hpres₂.reg .x22, k₁ .x22 (by decide), I.x22,
      show (24 : Word) = BitVec.ofNat 64 24 from rfl, add_ofNat_add]
    congr 2
  by_cases hlast : z + 1 = min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l)
  · refine ⟨v, hr₂.trans hr₃, Or.inr (Or.inl {
      toLF := Lv
      pc := b80010450_pc_not_taken h₃ (by
        rw [hpres₂.reg .x22, k₁ .x22 (by decide), I.x22, hpres₂.reg .x27, k₁ .x27 (by decide),
          I.x27, ← hlast, show (24 : Word) = BitVec.ofNat 64 24 from rfl, add_ofNat_add]
        congr 2)
      x26 := (back .x26 (by decide) (by decide)).trans I.x26
      x9 := (back .x9 (by decide) (by decide)).trans I.x9
      x24 := (back .x24 (by decide) (by decide)).trans I.x24
      x27 := (back .x27 (by decide) (by decide)).trans I.x27
      x21 := by
        rw [back .x21 (by decide) (by decide), I.x21, kvm _ fun i hi h ↦ by addr_omega [h, hi, hb]]
      x25 := (back .x25 (by decide) (by decide)).trans I.x25
      gp1 := by rw [kvm _ fun i hi h ↦ by addr_omega [h, hi, hb], I.gp1]
      lt := I.lt
      ll := hll
      row := by
        have e := inRow_full (sgOf s) (slOf s m) (claimAt s (oClaim s)).weights
          (s.getReg .x15).toNat g (l := l) (by rw [hWl]; exact hll)
        rw [hWl] at e
        rw [hrow, hlast, e] })⟩
  · have hz1 : z + 1 < min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l) := by omega
    refine ⟨v, hr₂.trans hr₃, Or.inl {
      toLF := Lv
      pc := b80010450_pc_taken h₃ (by
        rw [hpres₂.reg .x22, k₁ .x22 (by decide), I.x22, hpres₂.reg .x27, k₁ .x27 (by decide),
          I.x27]
        addr_omega [hR, hz1, hll])
      x26 := (back .x26 (by decide) (by decide)).trans I.x26
      x9 := (back .x9 (by decide) (by decide)).trans I.x9
      x24 := (back .x24 (by decide) (by decide)).trans I.x24
      x22 := x22v
      x27 := (back .x27 (by decide) (by decide)).trans I.x27
      x8 := by
        rw [b80010450_x8 h₃, x8v₁, show 24 * (z + 1) = 24 * z + 24 by ring, ← add_ofNat_add]
        rv_eval []
      x21 := by
        rw [back .x21 (by decide) (by decide), I.x21, kvm _ fun i hi h ↦ by addr_omega [h, hi, hb]]
      x25 := (back .x25 (by decide) (by decide)).trans I.x25
      gp1 := by rw [kvm _ fun i hi h ↦ by addr_omega [h, hi, hb], I.gp1]
      lt := I.lt
      ll := hll
      zn := hz1
      scale := by
        rw [← I.scale]
        exact Fine.eAt fun i hi h ↦ by addr_omega [h, hi, hb]
      row := hrow }⟩

theorem weights_length {s m u : MachineState} (hpre : OpenPre s) (P : P2 s m) (M : Mid s m u) :
    (claimAt s (oClaim s)).weights.length = (s.getMem (s.getReg .x14 + 64)).toNat := by
  rw [← (claim_keep hpre P M).2, eListAt_length]

theorem after_chunk {s m u : MachineState} (hpre : OpenPre s) (P : P2 s m) {g l : Nat}
    (C : CD s m u g l) :
    ∃ v, Reaches Image.code u v ∧ (MI s m v g (l + 1) ∨ OI s m v (g + 1) ∨ AtFinal s m v) := by
  have hb := bounds hpre
  have x2u := C.mid.x2
  have hL := (s.getMem (s.getReg .x14 + 64)).isLt
  have hll := C.ll
  have glt := C.lt
  have hg16 := (s.getReg .x16).isLt
  have hWl := weights_length hpre P C.mid
  obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8001048c_spec C.pc trivial
  have k := b8001048c_keeps h
  have hm := b8001048c_mem_same h
  have x2v : v.getReg .x2 = s.getReg .x2 - 1856 := (k .x2 (by decide)).trans x2u
  have Lv := LF.keep' hpre C.toLF (DFrame.of_same hm _) x2v fun r hr ↦ k r (mem_of_mem hr _)
  have rowv : eListAt v (s.getReg .x2 - 1688) 64 = eListAt u (s.getReg .x2 - 1688) 64 := by
    simp only [eListAt, eAt, hm]
  by_cases hmore : (s.getMem (s.getReg .x14 + 64)).toNat - 64 * l -
      min 64 ((s.getMem (s.getReg .x14 + 64)).toNat - 64 * l) = 0
  swap
  · refine ⟨v, hr, Or.inl {
      toLF := Lv
      pc := b8001048c_pc_taken h (by
        rw [C.x24]; intro h0
        have := congrArg BitVec.toNat h0
        rw [ofNat_toNat_lt (by omega)] at this; exact hmore this)
      x26 := (k .x26 (by decide)).trans C.x26
      x9 := (k .x9 (by decide)).trans C.x9
      x24 := by rw [k .x24 (by decide), C.x24]; congr 1; omega
      x22 := by rw [b8001048c_x22 h, C.x27]; congr 2; omega
      x21 := by rw [k .x21 (by decide), C.x21, hm]
      x25 := (k .x25 (by decide)).trans C.x25
      gp1 := by rw [hm, C.gp1]
      lt := glt
      ll := by omega
      row := by rw [rowv, C.row] }⟩
  have hnch : ((claimAt s (oClaim s)).weights.length + 63) / 64 = l + 1 := by rw [hWl]; omega
  obtain ⟨w, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80010494_spec
    (b8001048c_pc_not_taken h (by rw [C.x24, hmore]; rfl)) (by
      rv_eval [x2v]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₂ := b80010494_keeps h₂
  have hm₂ := b80010494_mem_same h₂
  have x2w : w.getReg .x2 = s.getReg .x2 - 1856 := (k₂ .x2 (by decide)).trans x2v
  have g1 : v.getMem (v.getReg .x2 + 80) = BitVec.ofNat 64 (g + 1) := by
    rw [x2v]; rv_eval []; rw [hm]; exact C.gp1
  have c1 : v.getMem (v.getReg .x2 + 72) = s.getReg .x16 := by
    rw [x2v]; rv_eval []; rw [hm]; exact C.mid.count
  have roww : eListAt w (s.getReg .x2 - 1688) 64 =
      outRow (sgOf s) (slOf s m) (claimAt s (oClaim s)).weights (s.getReg .x15).toNat (g + 1) := by
    rw [← midRow_full, hnch, ← C.row]; simp only [eListAt, eAt, hm₂, hm]
  have Lw := LF.keep' hpre Lv (DFrame.of_same hm₂ _) x2w fun r hr ↦ k₂ r (mem_of_mem hr _)
  by_cases hend : g + 1 = (s.getReg .x16).toNat
  · refine ⟨w, hr.trans hr₂, Or.inr (Or.inr (atFinal_of_mid Lw.mid
      (b80010494_pc_not_taken h₂ (by
        rw [g1, c1]; apply BitVec.eq_of_toNat_eq; rw [ofNat_toNat_lt (by omega)]; exact hend)) ?_))⟩
    rw [roww, openRow_outRow, hend]
  · refine ⟨w, hr.trans hr₂, Or.inr (Or.inl {
      toLF := Lw
      pc := b80010494_pc_taken h₂ (by
        rw [g1, c1]; intro h0
        have := congrArg BitVec.toNat h0
        rw [ofNat_toNat_lt (by omega)] at this; exact hend this)
      x26 := by rw [b80010494_x26 h₂, x2v]; rv_eval []; rw [hm]; exact C.gp1
      lt := by omega
      wne := by omega
      row := roww })⟩

theorem inner_loop (hM : MulSpec) {s m : MachineState} (hpre : OpenPre s) (P : P2 s m) (g l : Nat) :
    ∀ u, (∃ z, II s m u g l z) → ∃ v, Reaches Image.code u v ∧ (CD s m v g l ∨ Dead Image.code v) := by
  refine Reaches.loop _ (fun u ↦ (u.getReg .x27).toNat - (u.getReg .x22).toNat) _ ?_
  rintro u ⟨z, I⟩
  have wR := hpre.weights
  simp only [VecRegion, vecPtr, vecLen, oClaim] at wR
  rv_eval [] at wR
  have hll := I.ll
  have hR : Region (s.getMem (s.getReg .x14 + 56)) (24 * (s.getMem (s.getReg .x14 + 64)).toNat) :=
    wR.resolve_left (by omega)
  obtain ⟨v, hr, h | h | h⟩ := pos_step hM hpre P I
  · refine Or.inr ⟨v, hr, ⟨z + 1, h⟩, ?_⟩
    rw [h.x27, h.x22, I.x27, I.x22]
    have := h.zn
    addr_omega [hR, this, hll]
  · exact Or.inl ⟨v, hr, Or.inl h⟩
  · exact Or.inl ⟨v, hr, Or.inr h⟩

theorem mid_loop (hM : MulSpec) {s m : MachineState} (hpre : OpenPre s) (P : P2 s m) (g : Nat) :
    ∀ u, (∃ l, MI s m u g l) → ∃ v, Reaches Image.code u v ∧
      (OI s m v (g + 1) ∨ AtFinal s m v ∨ Dead Image.code v) := by
  refine Reaches.loop _ (fun u ↦ (u.getReg .x24).toNat) _ ?_
  rintro u ⟨l, I⟩
  have hL := (s.getMem (s.getReg .x14 + 64)).isLt
  obtain ⟨v, hr, h | h⟩ := mid_step hM hpre P I
  swap
  · exact Or.inl ⟨v, hr, Or.inr (Or.inr h)⟩
  obtain ⟨w, hr₂, h₂ | h₂⟩ := inner_loop hM hpre P g l v ⟨0, h⟩
  swap
  · exact Or.inl ⟨w, hr.trans hr₂, Or.inr (Or.inr h₂)⟩
  obtain ⟨x, hr₃, h₃ | h₃ | h₃⟩ := after_chunk hpre P h₂
  · refine Or.inr ⟨x, hr.trans (hr₂.trans hr₃), ⟨l + 1, h₃⟩, ?_⟩
    rw [h₃.x24, I.x24, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
    have := h₃.ll; omega
  · exact Or.inl ⟨x, hr.trans (hr₂.trans hr₃), Or.inl h₃⟩
  · exact Or.inl ⟨x, hr.trans (hr₂.trans hr₃), Or.inr (Or.inl h₃)⟩

theorem outer_loop (hM : MulSpec) {s m : MachineState} (hpre : OpenPre s) (P : P2 s m) :
    ∀ u, (∃ g, OI s m u g) → ∃ v, Reaches Image.code u v ∧ (AtFinal s m v ∨ Dead Image.code v) := by
  refine Reaches.loop _ (fun u ↦ (s.getReg .x16).toNat - (u.getReg .x26).toNat) _ ?_
  rintro u ⟨g, O⟩
  have hg16 := (s.getReg .x16).isLt
  obtain ⟨v, hr, h⟩ := outer_step hpre O
  obtain ⟨w, hr₂, h₂ | h₂ | h₂⟩ := mid_loop hM hpre P g v ⟨0, h⟩
  · refine Or.inr ⟨w, hr.trans hr₂, ⟨g + 1, h₂⟩, ?_⟩
    rw [h₂.x26, O.x26, ofNat_toNat_lt (by have := O.lt; omega),
      ofNat_toNat_lt (by have := h₂.lt; omega)]
    have := h₂.lt; omega
  · exact Or.inl ⟨w, hr.trans hr₂, Or.inl h₂⟩
  · exact Or.inl ⟨w, hr.trans hr₂, Or.inr h₂⟩

end Rv64Verifier.Gkr.Open
