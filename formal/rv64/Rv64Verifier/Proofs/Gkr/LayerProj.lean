import Rv64Verifier.Proofs.Gkr.LayerScalars

/-!
# `keccak::verify_layer`: the projected value

`keccak.rs:127-134`, inlined at `0x8000f118..0x8000f1cc`: per product coefficient `c` (`x10`), the
sum of the claim's instance weights `mu[i]` whose mask `RMFE_PROJECT[i]` (`.rodata` at
`0xa00000f8`) holds bit `c` (`inner_loop`, accumulated in `x13`, `x11`, `x12`), times `product[c]`
(`mul`), summed in `x27`, `x26`, `x25`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The first `i` masks' weights on coefficient `c`. -/
def projIn (mu : List E) (c i : Nat) : E :=
  sumE (((List.range i).filter fun j ↦ bit64 (rmfeProjectRust.getD j 0#64) c).map fun j ↦
    mu.getD j 0)

theorem projectedRust_eq_sum (mu product : List E) :
    projectedRust mu product =
      sumE ((List.range productBits).map fun c ↦ projIn mu c 16 * product.getD c 0) := rfl

theorem proj_word {u : MachineState} (h : RodataOk u) {i : Nat} (hi : i < 16) :
    u.getMem (0xa00000f8 + BitVec.ofNat 64 (8 * i)) = rmfeProjectRust.getD i 0#64 := by
  interval_cases i <;> exact h.word

theorem and_shift_eq_zero (w : Word) {c : Nat} (hc : c < 64) :
    (w &&& (1 : Word) <<< c) = 0 ↔ bit64 w c = false := by
  rw [bit64_eq]
  constructor
  · intro h
    have := congrArg (fun x : Word ↦ x.getLsbD c) h
    simpa [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hc, BitVec.testBit_toNat] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases e : i = c
    · subst e
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
      rw [show w.getLsbD i = w.toNat.testBit i from rfl, h]
      simp
    · rw [BitVec.getLsbD_and, Sym.shiftLeft_eq_mul,
        show (1 : Word) * BitVec.ofNat 64 (2 ^ c) = BitVec.ofNat 64 (2 ^ c) from BitVec.one_mul _,
        BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
      simp [Ne.symm e]

theorem trap : Image.code.fetch 0x80010180 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem ofNat_succ (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
  omega

theorem ofNat_step' (b : Word) (k i : Nat) (d : Word) :
    b + BitVec.ofNat 64 (k * i) + d + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (k * (i + 1)) + d := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mul_succ]
  omega

theorem ofNat_step (b : Word) (k i d : Nat) :
    b + BitVec.ofNat 64 (k * i) + BitVec.ofNat 64 (d + k) =
      b + BitVec.ofNat 64 (k * (i + 1)) + BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mul_succ]
  omega

theorem ofNat_step0 (b : Word) (k i : Nat) :
    b + BitVec.ofNat 64 (k * i) + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (k * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mul_succ]
  omega

theorem projIn_succ (mu : List E) (c i : Nat) : projIn mu c (i + 1) =
    projIn mu c i + if bit64 (rmfeProjectRust.getD i 0#64) c then mu.getD i 0 else 0 :=
  sumE_filter_succ _ _ _

/-- In the inner loop, from the outer loop's head `o`: `i` masks done. -/
structure PI (s o u : MachineState) (mp : Word) (mu : List E) (c i : Nat) : Prop where
  regs : ∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x8, .x9, .x10, .x18, .x19, .x20, .x21, .x22, .x24, .x25,
    .x26, .x27, .x28, .x29, .x30, .x31], u.getReg r = o.getReg r
  mem : ∀ a, u.getMem a = o.getMem a
  x14 : u.getReg .x14 = BitVec.ofNat 64 i
  x15 : u.getReg .x15 = (1 : Word) <<< c
  x16 : u.getReg .x16 = 0xa00000f8 + BitVec.ofNat 64 (8 * i)
  x17 : u.getReg .x17 = mp + BitVec.ofNat 64 (24 * i) + 16
  x23 : u.getReg .x23 = o.getReg .x10 + 1
  acc : (u.getReg .x13, u.getReg .x11, u.getReg .x12) = limbs (projIn mu c i)

/-- What the inner loop reads: the masks, the claim's weights. -/
structure InnerOk (o : MachineState) (mp : Word) (mu : List E) : Prop where
  rodata : RodataOk o
  x8 : (o.getReg .x8).toNat = mu.length
  x19 : o.getReg .x19 = 16
  elems : ∀ j < mu.length, eAt o (mp + BitVec.ofNat 64 (24 * j)) = mu.getD j 0
  region : ∀ j < mu.length, Region (mp + BitVec.ofNat 64 (24 * j)) 24

set_option maxHeartbeats 2000000 in
theorem inner_step {s o u : MachineState} {mp : Word} {mu : List E} {c i : Nat} (hc : c < 64)
    (I : PI s o u mp mu c i) (hpc : u.pc = 0x8000f164) (hi : i < 16) (K : InnerOk o mp mu) :
    ∃ v, Reaches Image.code u v ∧ ((PI s o v mp mu c (i + 1) ∧
      ((i + 1 < 16 ∧ v.pc = 0x8000f164) ∨ (i + 1 = 16 ∧ v.pc = 0x8000f178))) ∨
      Dead Image.code v) := by
  have hro : RodataOk u := fun p hp ↦ by rw [I.mem]; exact K.rodata p hp
  have hw := proj_word hro hi
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f164_spec hpc (by
    rv_eval [I.x16]
    exact Region.valid (a := 0xa00000f8) (n := 128) (by addr_omega []) (by addr_omega [hi])
      (by addr_omega [hi]) (by addr_omega [hi]))
  have k₁ := b8000f164_keeps h₁
  have hm₁ := b8000f164_mem_same h₁
  -- the step's tail, from `0x8000f154`
  have tail (w : MachineState) (hw154 : w.pc = 0x8000f154)
      (kw : ∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x8, .x9, .x10, .x14, .x15, .x16, .x17, .x18, .x19, .x20,
        .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31], w.getReg r = u.getReg r)
      (mw : ∀ a, w.getMem a = u.getMem a)
      (aw : (w.getReg .x13, w.getReg .x11, w.getReg .x12) = limbs (projIn mu c (i + 1))) :
      ∃ v, Reaches Image.code w v ∧ PI s o v mp mu c (i + 1) ∧
        ((i + 1 < 16 ∧ v.pc = 0x8000f164) ∨ (i + 1 = 16 ∧ v.pc = 0x8000f178)) := by
    obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000f154_spec hw154 trivial
    have k := b8000f154_keeps h
    have x14w : w.getReg .x14 = BitVec.ofNat 64 i := (kw .x14 (by decide)).trans I.x14
    have x19w : w.getReg .x19 = 16 :=
      ((kw .x19 (by decide)).trans (I.regs .x19 (by decide))).trans K.x19
    refine ⟨v, hr, {
      regs := fun r hr ↦ by
        rw [k r (mem_of_mem hr _), kw r (mem_of_mem hr _), I.regs r hr]
      mem := fun a ↦ by rw [b8000f154_mem_same h, mw, I.mem]
      x14 := by rw [b8000f154_x14 h, x14w, ofNat_succ]
      x15 := by rw [k .x15 (by decide), kw .x15 (by decide), I.x15]
      x16 := by rw [b8000f154_x16 h, kw .x16 (by decide), I.x16]; exact ofNat_step0 _ 8 i
      x17 := by rw [b8000f154_x17 h, kw .x17 (by decide), I.x17]; exact ofNat_step' _ 24 i 16
      x23 := by rw [k .x23 (by decide), kw .x23 (by decide), I.x23]
      acc := by rw [k .x13 (by decide), k .x11 (by decide), k .x12 (by decide), aw] }, ?_⟩
    by_cases hl : i + 1 < 16
    · refine Or.inl ⟨hl, b8000f154_pc_not_taken h ?_⟩
      rw [x14w, x19w, ofNat_succ]
      intro h16
      have := congrArg BitVec.toNat h16
      rw [BitVec.toNat_ofNat] at this
      change (i + 1) % 2 ^ 64 = 16 at this
      omega
    · refine Or.inr ⟨by omega, b8000f154_pc_taken h ?_⟩
      rw [x14w, x19w, ofNat_succ, show i + 1 = 16 by omega]
      rfl
  have x16u := I.x16
  have x15u := I.x15
  cases hb : bit64 (rmfeProjectRust.getD i 0#64) c
  · have hz : u.getMem (u.getReg .x16) &&& u.getReg .x15 = 0 := by
      rw [x16u, x15u, hw]; exact (and_shift_eq_zero _ hc).mpr hb
    obtain ⟨v, hr, P, hpc'⟩ := tail u₁ (b8000f164_pc_taken h₁ hz)
      (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁ (by
        rw [k₁ .x13 (by decide), k₁ .x11 (by decide), k₁ .x12 (by decide), I.acc, projIn_succ, hb]
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero])
    exact ⟨v, hr₁.trans hr, Or.inl ⟨P, hpc'⟩⟩
  · have hnz : u.getMem (u.getReg .x16) &&& u.getReg .x15 ≠ 0 := by
      rw [x16u, x15u, hw]; intro h; rw [(and_shift_eq_zero _ hc).mp h] at hb; cases hb
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f170_spec (b8000f164_pc_not_taken h₁ hnz)
      trivial
    have k₂ := b8000f170_keeps h₂
    have x14₁ : (u₁.getReg .x14).toNat = i := by
      rw [k₁ .x14 (by decide), I.x14, BitVec.toNat_ofNat]; omega
    have x8₁ : (u₁.getReg .x8).toNat = mu.length := by
      rw [k₁ .x8 (by decide), I.regs .x8 (by decide), K.x8]
    by_cases hlt : i < mu.length
    · have hR := K.region i hlt
      have x17₂ : u₂.getReg .x17 = mp + BitVec.ofNat 64 (24 * i) + 16 := by
        rw [k₂ .x17 (by decide), k₁ .x17 (by decide), I.x17]
      obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f13c_spec
        (b8000f170_pc_taken h₂ (by rw [x14₁, x8₁]; exact hlt)) (by
          rv_eval [x17₂]
          and_intros <;> (refine Region.valid hR ?_ ?_ ?_ <;> addr_omega [hR]))
      have k₃ := b8000f13c_keeps h₃
      have e := K.elems i hlt
      have m₂ (a : Word) : u₂.getMem a = o.getMem a := by
        rw [b8000f170_mem_same h₂, hm₁, I.mem]
      obtain ⟨v, hr, P, hpc'⟩ := tail u₃ (b8000f13c_pc h₃)
        (fun r hr ↦ by rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)])
        (fun a ↦ by rw [b8000f13c_mem_same h₃, b8000f170_mem_same h₂, hm₁]) (by
          rw [b8000f13c_x13 h₃, b8000f13c_x11 h₃, b8000f13c_x12 h₃, x17₂, projIn_succ, hb]
          simp only [↓reduceIte]
          rw [limbs_add, ← I.acc, ← e, limbs_eAt]
          rv_eval [m₂, k₂ .x13 (by decide), k₂ .x11 (by decide), k₂ .x12 (by decide),
            k₁ .x13 (by decide), k₁ .x11 (by decide), k₁ .x12 (by decide), BitVec.xor_comm])
      exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans hr)), Or.inl ⟨P, hpc'⟩⟩
    · obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f174_spec
        (b8000f170_pc_not_taken h₂ (by rw [x14₁, x8₁]; omega)) trivial
      exact ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inr (dead_of_fetch (by rw [b8000f174_pc h₃]; exact trap))⟩

theorem inner_loop {s o : MachineState} {mp : Word} {mu : List E} {c : Nat} (hc : c < 64)
    (K : InnerOk o mp mu) : ∀ n i u, i + n = 16 → 0 < n → PI s o u mp mu c i →
      u.pc = 0x8000f164 → ∃ v, Reaches Image.code u v ∧
        ((PI s o v mp mu c 16 ∧ v.pc = 0x8000f178) ∨ Dead Image.code v)
  | 0, _, _, _, h0, _, _ => absurd h0 (Nat.lt_irrefl 0)
  | n + 1, i, u, hn, _, I, hpc => by
    obtain ⟨v, hr, ⟨P, ⟨hl, hpc'⟩ | ⟨he, hpc'⟩⟩ | hd⟩ := inner_step hc I hpc (by omega) K
    · obtain ⟨w, hr', hw⟩ := inner_loop hc K n (i + 1) v (by omega) (by omega) P hpc'
      exact ⟨w, hr.trans hr', hw⟩
    · rw [he] at P
      exact ⟨v, hr, Or.inl ⟨P, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

theorem limbs_zero : Model.limbs (0 : E) = (0, 0, 0) := by
  decide +kernel

/-- What the outer loop writes: `f + 960`, `f + 264`, `mul`'s stack. -/
@[rv_addr] def ScrP (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 752) 24 ∨ Within a (s.getReg .x2 - 1448) 24 ∨
    Within a (s.getReg .x2 - 2736) 1024

/-- The outer loop's entry `o₀`: the masks' and weights' reads, the product at `pp`. -/
structure OuterOk (s o₀ : MachineState) (mp pp : Word) (mu product : List E) : Prop where
  base : Base s o₀
  inner : InnerOk o₀ mp mu
  mS : ∀ j < mu.length, Apart (mp + BitVec.ofNat 64 (24 * j)) 24 (s.getReg .x2 - 2736) 2736
  x9 : o₀.getReg .x9 = 1
  x18 : o₀.getReg .x18 = 47
  x20 : o₀.getReg .x20 = 0xa00000f8
  x21 : o₀.getReg .x21 = mp + 16
  x22 : o₀.getReg .x22 = 47
  ppM : o₀.getMem (s.getReg .x2 - 1600) = pp
  prod : ∀ c < 47, eAt o₀ (pp + BitVec.ofNat 64 (24 * c)) = product.getD c 0
  ppR : heapStart ≤ pp.toNat ∧ pp.toNat + 24 * 47 ≤ heapEnd ∧ pp.toNat % 8 = 0

/-- The outer loop after `c` coefficients. -/
structure PO (s o₀ o : MachineState) (mu product : List E) (c : Nat) : Prop where
  base : Base s o
  regs : ∀ r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x24], o.getReg r = o₀.getReg r
  x10 : o.getReg .x10 = BitVec.ofNat 64 c
  acc : (o.getReg .x27, o.getReg .x26, o.getReg .x25) =
    limbs (sumE ((List.range c).map fun c ↦ projIn mu c 16 * product.getD c 0))
  le : c ≤ 47
  frame : DFrame o₀ o (ScrP s)

theorem PO.innerOk {s o₀ o : MachineState} {mp pp : Word} {mu product : List E} {c : Nat}
    (hpre : VerifyLayerPre s) (L : OuterOk s o₀ mp pp mu product) (P : PO s o₀ o mu product c) :
    InnerOk o mp mu := by
  have hb := bounds hpre
  have hrs := hpre.stack.rodata
  unfold verifyLayerStack at hb hrs
  exact {
    rodata := L.inner.rodata.dframe P.frame fun a ha hw ↦ by
      simp only [ScrP] at hw
      rcases hw with hw | hw | hw <;> addr_omega [ha, hw, hb, hrs]
    x8 := by rw [P.regs .x8 (by decide)]; exact L.inner.x8
    x19 := by rw [P.regs .x19 (by decide)]; exact L.inner.x19
    elems := fun j hj ↦ by
      rw [← L.inner.elems j hj]
      have hR := L.inner.region j hj
      have hA := L.mS j hj
      exact P.frame.eAt fun i hi hw ↦ by
        simp only [ScrP] at hw
        rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hb, hR, hA]
    region := L.inner.region }


theorem scrP_lw {s v : MachineState} (hpre : VerifyLayerPre s) {a : Word} (h : ScrP s a) :
    LW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  have hb := bounds hpre
  unfold verifyLayerStack at hb
  simp only [ScrP] at h
  refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h | h <;> addr_omega [h, hb]

set_option maxHeartbeats 4000000 in
theorem outer_step (hM : MulSpec) {s o₀ o : MachineState} {mp pp : Word} {mu product : List E}
    {c : Nat} (hpre : VerifyLayerPre s) (L : OuterOk s o₀ mp pp mu product)
    (P : PO s o₀ o mu product c) (hpc : o.pc = 0x8000f118) (hc : c < 47) :
    ∃ v, Reaches Image.code o v ∧ ((PO s o₀ v mu product (c + 1) ∧
      ((c + 1 < 47 ∧ v.pc = 0x8000f118) ∨ (c + 1 = 47 ∧ v.pc = 0x8000f1cc))) ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  have B := P.base
  have K := P.innerOk hpre L
  have x2o : o.getReg .x2 = s.getReg .x2 - 1712 := B.x2
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f118_spec hpc trivial
  have k₁ := b8000f118_keeps h₁
  have hc64 : (BitVec.ofNat 64 c).toNat % 64 = c := by
    rw [BitVec.toNat_ofNat]; omega
  have x15₁ : u₁.getReg .x15 = (1 : Word) <<< c :=
    Sym.Expect.Holds.reg_eq h₁ .x15 rfl (by
      rv_eval [P.regs .x9 (by decide), L.x9, P.x10, hc64])
  have I₀ : PI s o u₁ mp mu c 0 := {
    regs := fun r hr ↦ k₁ r (mem_of_mem hr _)
    mem := b8000f118_mem_same h₁
    x14 := b8000f118_x14 h₁
    x15 := x15₁
    x16 := by rw [b8000f118_x16 h₁, P.regs .x20 (by decide), L.x20]; decide
    x17 := by
      rw [b8000f118_x17 h₁, P.regs .x21 (by decide), L.x21,
        show BitVec.ofNat 64 (24 * 0) = 0 from rfl, Sym.add_zero_lit]
    x23 := b8000f118_x23 h₁
    acc := by
      rw [b8000f118_x13 h₁, b8000f118_x11 h₁, b8000f118_x12 h₁,
        show projIn mu c 0 = 0 from rfl, limbs_zero] }
  obtain ⟨u₂, hr₂, ⟨I, hpc₂⟩ | hd⟩ :=
    inner_loop (by omega) K 16 0 u₁ (by omega) (by omega) I₀ (b8000f118_pc h₁)
  swap
  · exact ⟨u₂, hr₁.trans hr₂, Or.inr hd⟩
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 1712 := (I.regs .x2 (by decide)).trans x2o
  -- the sum stored at `f + 960`, the bound checked
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f178_spec hpc₂ (by
    rv_eval [x2₂]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000f178_keeps h₃
  have f₃ := b8000f178_frame h₃ (by rw [x2₂]; unfold verifyLayerStack at hb; addr_omega [hb])
  rw [x2₂] at f₃
  have x10₂ : u₂.getReg .x10 = BitVec.ofNat 64 c := (I.regs .x10 (by decide)).trans P.x10
  have x18₂ : u₂.getReg .x18 = 47 :=
    ((I.regs .x18 (by decide)).trans (P.regs .x18 (by decide))).trans L.x18
  have pc₃ := b8000f178_pc_not_taken h₃ (by
    rw [x10₂, x18₂]; intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat] at this; change c % 2 ^ 64 = 47 at this; omega)
  have e₃ : eAt u₃ (s.getReg .x2 - 752) = projIn mu c 16 := by
    apply eAt_eq_of_limbs
    rw [← I.acc]
    have m0 := b8000f178_m_x2_960 h₃
    have m8 := b8000f178_m_x2_968 h₃
    have m16 := b8000f178_m_x2_976 h₃
    rw [x2₂] at m0 m8 m16
    rv_eval [] at m0 m8 m16
    rv_eval [m0, m8, m16]
  -- `mul(f + 264, f + 960, product + 24 c)`
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000f188_spec pc₃ (by
    rv_eval [k₃ .x2 (by decide), x2₂]
    valid_access hpre.stack.valid [hb])
  have k₄ := b8000f188_keeps h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 1712 := by rw [k₄ .x2 (by decide), k₃ .x2 (by decide), x2₂]
  have m₃ (a : Word) (ha : ¬ Within a (s.getReg .x2 - 752) 24) : u₃.getMem a = o.getMem a := by
    rw [f₃ a (by rv_eval []; exact ha), I.mem]
  have ppo : o.getMem (s.getReg .x2 - 1600) = pp := by
    rw [← L.ppM]; exact P.frame _ fun i hi hw ↦ by
      simp only [ScrP] at hw; rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hb]
  have x12₄ : u₄.getReg .x12 = pp + BitVec.ofNat 64 (24 * c) := by
    rw [b8000f188_x12 h₄, k₃ .x2 (by decide), x2₂, k₃ .x10 (by decide), x10₂]
    rv_eval []
    rw [m₃ _ (by addr_omega [hb]), ppo, Open.mul24, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have x10₄ : u₄.getReg .x10 = s.getReg .x2 - 1448 := by
    rw [b8000f188_x10 h₄, k₃ .x2 (by decide), x2₂]; rv_eval []
  have x11₄ : u₄.getReg .x11 = s.getReg .x2 - 752 := by
    rw [b8000f188_x11 h₄, k₃ .x2 (by decide), x2₂]; rv_eval []
  have hm₄ := b8000f188_mem_same h₄
  have hppR := L.ppR
  have Bo := B.rodata hpre
  have hro₄ : RodataOk u₄ := by
    have hrs := hpre.stack.rodata
    unfold verifyLayerStack at hb hrs
    refine Bo.dframe (w := (Within · (s.getReg .x2 - 752) 24)) (fun a ha ↦ by
      rw [hm₄, m₃ a fun h ↦ ha 0 (by decide) (by rwa [Transcript.add_ofNat_zero])]) fun a ha hw ↦ by
        addr_omega [ha, hw, hb, hrs]
  have hmp : MulPre u₄ := mul_pre hpre x2₄ hro₄ 1448 x10₄ (by decide) (by decide) (by decide)
    (by rw [x11₄]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₄]; addr_omega [hb])
    (by rw [x10₄, x11₄]; addr_omega [hb])
    (by rw [x12₄]; exact heap_vmr (by addr_omega [hppR, hc]) (by addr_omega [hppR, hc]) (by addr_omega [hppR, hc]))
    (by rw [x12₄]; unfold verifyLayerStack at hb; have := hpre.stack.above
        simp only [stackLo] at this; unfold verifyLayerStack at this; addr_omega [hppR, hc, hb, this])
    (by rw [x10₄, x12₄]; unfold verifyLayerStack at hb; have := hpre.stack.above
        simp only [stackLo] at this; unfold verifyLayerStack at this; addr_omega [hppR, hc, hb, this])
  obtain ⟨t, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hd⟩ :=
    hM.call (hr₁.trans (hr₂.trans (hr₃.trans hr₄))) (b8000f188_pc h₄) hmp
  swap
  · exact ⟨t, hr₅, Or.inr hd⟩
  have F₅ := mul_frame x2₄ hpost₅
  rw [x10₄] at F₅
  have v₅ := hpost₅.value
  rw [x10₄, x11₄, x12₄] at v₅
  have x2t : t.getReg .x2 = s.getReg .x2 - 1712 := (hpres₅.reg .x2).trans x2₄
  have eprod : eAt u₄ (pp + BitVec.ofNat 64 (24 * c)) = product.getD c 0 := by
    have hA := hpre.stack.above
    simp only [stackLo] at hA
    unfold verifyLayerStack at hA hb
    rw [← L.prod c hc]
    unfold Rv64Verifier.eAt
    rw [hm₄, hm₄, hm₄, m₃ _ (by addr_omega [hppR, hc, hb, hA]), m₃ _ (by addr_omega [hppR, hc, hb, hA]),
      m₃ _ (by addr_omega [hppR, hc, hb, hA]),
      P.frame _ fun i hi hw ↦ by simp only [ScrP] at hw; rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hppR, hc, hb, hA],
      P.frame _ fun i hi hw ↦ by simp only [ScrP] at hw; rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hppR, hc, hb, hA],
      P.frame _ fun i hi hw ↦ by simp only [ScrP] at hw; rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hppR, hc, hb, hA]]
  have e264 : eAt t (s.getReg .x2 - 1448) = projIn mu c 16 * product.getD c 0 := by
    rw [v₅, eprod, ← e₃]
    unfold Rv64Verifier.eAt
    rw [hm₄, hm₄, hm₄]
  obtain ⟨v, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000f1ac_spec
    (by rw [hpc₅, returnAddress_eq, b8000f188_x1 h₄]; decide) (by
      rv_eval [x2t]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₆ := b8000f1ac_keeps h₆
  have hm₆ := b8000f1ac_mem_same h₆
  have rk (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27]) : t.getReg r = u₂.getReg r := by
    rw [hpres₅.reg r (mem_of_mem hr _), k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _)]
  have x23t : t.getReg .x23 = BitVec.ofNat 64 (c + 1) := by
    rw [rk .x23 (by decide), I.x23, P.x10, ofNat_succ]
  have x22t : t.getReg .x22 = 47 := by
    rw [rk .x22 (by decide), I.regs .x22 (by decide), P.regs .x22 (by decide), L.x22]
  -- the iteration's frame
  have Fv : DFrame o v (ScrP s) := by
    refine ((DFrame.of_same I.mem _).trans (DFrame.of_memFrame f₃) fun a h ↦ ?_).trans
      ((DFrame.of_same hm₄ _).trans (F₅.trans (DFrame.of_same hm₆ _) fun _ h ↦ h) fun _ h ↦ h)
      fun a h ↦ ?_
    · simp only [ScrP]; left; rv_eval [] at h; exact h
    · simp only [ScrP]; rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hNv : v.getMem nextAddr = o.getMem nextAddr := Fv _ fun i hi hw ↦ by
    have hnx := hpre.stack.next
    unfold verifyLayerStack at hb hnx
    simp only [ScrP] at hw; rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have Bv : Base s v := B.next hpre (by rw [k₆ .x2 (by decide), x2t])
    ⟨by simp only [heapNext, hNv]; exact B.heap.lo, by simp only [heapNext, hNv]; exact B.heap.hi⟩
    (by simp only [heapNext, hNv]; exact le_refl _) Fv fun a h ↦ scrP_lw hpre h
  refine ⟨v, hr₅.trans hr₆, Or.inl ⟨{
    base := Bv
    regs := fun r hr ↦ by
      rw [k₆ r (mem_of_mem hr _), rk r (mem_of_mem hr _), I.regs r (mem_of_mem hr _), P.regs r hr]
    x10 := by rw [b8000f1ac_x10 h₆, x23t]
    acc := by
      rw [b8000f1ac_x27 h₆, b8000f1ac_x26 h₆, b8000f1ac_x25 h₆, x2t, rk .x27 (by decide),
        rk .x26 (by decide), rk .x25 (by decide), I.regs .x27 (by decide), I.regs .x26 (by decide),
        I.regs .x25 (by decide), sumE_map_succ, limbs_add, ← P.acc, ← e264, limbs_eAt]
      rv_eval [BitVec.xor_comm]
    le := by omega
    frame := P.frame.trans Fv fun _ h ↦ h }, ?_⟩⟩
  by_cases hl : c + 1 < 47
  · refine Or.inl ⟨hl, b8000f1ac_pc_taken h₆ ?_⟩
    rw [x23t, x22t]; intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat] at this; change (c + 1) % 2 ^ 64 = 47 at this; omega
  · refine Or.inr ⟨by omega, b8000f1ac_pc_not_taken h₆ ?_⟩
    rw [x23t, x22t, show c + 1 = 47 by omega]; rfl


theorem outer_loop (hM : MulSpec) {s o₀ : MachineState} {mp pp : Word} {mu product : List E}
    (hpre : VerifyLayerPre s) (L : OuterOk s o₀ mp pp mu product) :
    ∀ n c o, c + n = 47 → 0 < n → PO s o₀ o mu product c → o.pc = 0x8000f118 →
      ∃ v, Reaches Image.code o v ∧
        ((PO s o₀ v mu product 47 ∧ v.pc = 0x8000f1cc) ∨ Dead Image.code v)
  | 0, _, _, _, h0, _, _ => absurd h0 (Nat.lt_irrefl 0)
  | n + 1, c, o, hn, _, P, hpc => by
    obtain ⟨v, hr, ⟨P', ⟨hl, hpc'⟩ | ⟨he, hpc'⟩⟩ | hd⟩ := outer_step hM hpre L P hpc (by omega)
    · obtain ⟨w, hr', hw⟩ := outer_loop hM hpre L n (c + 1) v (by omega) (by omega) P' hpc'
      exact ⟨w, hr.trans hr', hw⟩
    · rw [he] at P'
      exact ⟨v, hr, Or.inl ⟨P', hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

theorem byte_test {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u) :
    u.getMem (s.getReg .x11 + 360) = s.getMem (s.getReg .x11 + 360) := by
  have hS := hpre.self.self
  have hos := hpre.outSelf
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  exact B.keep (missLW B.heap (by addr_omega [hos, hS]) (by addr_omega [hS]) (by addr_omega [hss, hS])
    ⟨by have := hsf.1; addr_omega [this, hS], by have := hsf.2; addr_omega [this, hS]⟩
    (by addr_omega [hS])) (by addr_omega [hS]) (le_refl _) (le_refl _)

theorem getD_eListAt (u : MachineState) (p : Word) {n c : Nat} (hc : c < n) :
    (eListAt u p n).getD c 0 = eAt u (p + BitVec.ofNat 64 (24 * c)) := by
  rw [List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hc), eListAt_getElem]

/-- The frame's slots after the product: `f + 32` .. `f + 112`. -/
structure S1 (s u : MachineState) (mp pp : Word) : Prop where
  mp : u.getMem (s.getReg .x2 - 1680) = mp
  plen : u.getMem (s.getReg .x2 - 1672) = 47
  out : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  claim : u.getMem (s.getReg .x2 - 1656) = s.getReg .x15
  step : u.getMem (s.getReg .x2 - 1624) = s.getReg .x14
  depth : u.getMem (s.getReg .x2 - 1616) = s.getReg .x13
  p : u.getMem (s.getReg .x2 - 1608) = s.getReg .x11
  pp : u.getMem (s.getReg .x2 - 1600) = pp

/-- At the projected loop's entry. -/
structure E0 (s o : MachineState) (pp : Word) (product : List E) : Prop where
  pc : o.pc = 0x8000f118
  outer : OuterOk s o (vecPtr s (lClaim s)) pp (claimAt s (lClaim s)).mu product
  x10 : o.getReg .x10 = 0
  x24 : o.getReg .x24 = s.getReg .x12
  x25 : o.getReg .x25 = 0
  x26 : o.getReg .x26 = 0
  x27 : o.getReg .x27 = 0
  slots : S1 s o (vecPtr s (lClaim s)) pp
  plen : product.length = 47
  pbuf : heapNext s ≤ pp.toNat ∧ pp.toNat + 24 * 47 ≤ heapNext o
  rest : Rest s o (TM.require (check1 (shapeOf s) (s.getReg .x14).toNat (claimAt s (lClaim s))
    product) >>= fun _ ↦ stage2 (claimAt s (lClaim s)) product)

set_option maxHeartbeats 4000000 in
theorem to_proj {s u : MachineState} (hpre : VerifyLayerPre s) (N : N1 s u)
    (hok : vecCap u (s.getReg .x2 - 752) ≠ errNiche) :
    ∃ o, Reaches Image.code u o ∧
      E0 s o (vecPtr u (s.getReg .x2 - 752)) (vecEs u (s.getReg .x2 - 752)) := by
  have hb := bounds hpre
  have B := N.base
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hc := hpre.claim
  obtain ⟨T₀, hT₀⟩ := Open.exists_T s (s.getReg .x11)
  have hv₀ := N.result T₀ hT₀
  have hvec : NewVecE s u (s.getReg .x2 - 752) (vecEs u (s.getReg .x2 - 752)) ∧
      (vecLen u (s.getReg .x2 - 752)).toNat = 47 := by
    generalize hx : (TM.nextScalars productBits).run T₀ = o at hv₀
    rcases o with _ | ⟨xs, T'⟩
    · exact absurd hv₀ hok
    · have e := hv₀.2.1.elems
      have hl := nextScalars_length hx
      refine ⟨by rw [e]; exact hv₀.2.1, ?_⟩
      rw [show (47 : Nat) = productBits from rfl, ← hl, ← e]; simp only [vecEs, eListAt_length]
  obtain ⟨hnv, hlen⟩ := hvec
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f0ac_spec N.pc (by
    rv_eval [B.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000f0ac_keeps h₁
  have B₁ : Base s u₁ := B.same ((k₁ .x2 (by decide)).trans B.x2) (b8000f0ac_mem_same h₁)
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f0c0_spec
    (b8000f0ac_pc_not_taken h₁ (by rw [B.x2]; rv_eval []; exact hok)) (by
      rv_eval [k₁ .x2 (by decide), B.x2, k₁ .x20 (by decide), N.x20]
      refine ⟨by valid_access hpre.stack.valid [hb], by valid_access hpre.stack.valid [hb],
        by valid_access hpre.stack.valid [hb], by unfold verifyLayerStack at hb hss; addr_omega [hb, hss, hS],
        by addr_omega [hS], Mapped.valid hS.1 (i := 360) (by decide),
        by valid_access hpre.stack.valid [hb]⟩)
  have hck : extractByte (s.getMem (s.getReg .x11 + 360)) 0 ≠ 0 := by
    have h := hpre.checked
    simp only [Checked] at h
    rwa [← Transcript.add_ofNat_zero (s.getReg .x11 + 360),
      Runtime.byteAt_add (by addr_omega [hS]) (by decide)] at h
  have pc₂ : u₂.pc = 0x8000f0d8 := Sym.Expect.Holds.pc_eq h₂ (by
    rv_eval [k₁ .x20 (by decide), N.x20, byte_test hpre B₁]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hck (by
      have := congrArg BitVec.toNat (beq_iff_eq.mp h)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
      simpa using this)))
  have k₂ := b8000f0c0_keeps h₂
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 1712 := B₁.x2
  have f₂ := b8000f0c0_frame h₂ (by rw [x2₁]; unfold verifyLayerStack at hb; addr_omega [hb])
  rw [x2₁] at f₂
  rv_eval [] at f₂
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have B₂ : Base s u₂ := B₁.slots hpre x2₂ f₂ (by addr_omega [hb]) (by addr_omega [hb])
  have x19₂ : u₂.getReg .x19 = s.getReg .x15 := by
    rw [k₂ .x19 (by decide), k₁ .x19 (by decide), N.x19]
  have hcs := hpre.claimStack
  unfold verifyLayerStack at hb hcs
  obtain ⟨o, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f0d8_spec pc₂ (by
    rv_eval [x2₂, x19₂]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc])
      | addr_omega [hb, hcs, hc])
  have k₃ := b8000f0d8_keeps h₃
  have f₃ := b8000f0d8_frame h₃ (by rw [x2₂]; addr_omega [hb])
  rw [x2₂] at f₃
  rv_eval [] at f₃
  have x2₃ : o.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s o := B₂.slots hpre x2₃ f₃ (by addr_omega [hb]) (by addr_omega [hb])
  have kc (y : Word) (h1 : (lClaim s).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (lClaim s).toNat + 96) :
      u₂.getMem y = s.getMem y :=
    B₂.keep (missClaim hpre B₂.heap) (by addr_omega [hc]) h1 h2
  have keep₃ (a : Word) (hw : ∀ k ∈ b8000f0d8.writes, k.eval u₂ ≠ a) : o.getMem a = u₂.getMem a :=
    keep_of_writes h₃ hw
  have keep₂ (a : Word) (hw : ∀ k ∈ b8000f0c0.writes, k.eval u₁ ≠ a) : u₂.getMem a = u₁.getMem a :=
    keep_of_writes h₂ hw
  have x2u := B.x2
  -- the product
  have hnb := hnv.buf
  have hnl := hnv.vec.len
  simp only [NewBuf] at hnb
  have hHu := B.heap.hi
  have hHs := hpre.heap.lo
  have ppR : heapNext s ≤ (vecPtr u (s.getReg .x2 - 752)).toNat ∧
      (vecPtr u (s.getReg .x2 - 752)).toNat + 24 * 47 ≤ heapNext u ∧
      (vecPtr u (s.getReg .x2 - 752)).toNat % 8 = 0 := by
    rw [hlen] at hnl
    rcases hnb with ⟨ha, h0 | ⟨h1, h2⟩⟩
    · omega
    · exact ⟨h1, by omega, ha⟩
  have hN : heapNext o = heapNext u := by
    have hnx := hpre.stack.next
    unfold verifyLayerStack at hnx
    simp only [heapNext]
    rw [f₃ _ (by addr_omega [hb, hnx]), f₂ _ (by addr_omega [hb, hnx]), b8000f0ac_mem_same h₁]
  have Fp : DFrame u o (Within · (s.getReg .x2 - 1680) 88) :=
    ((DFrame.of_same (b8000f0ac_mem_same h₁) _).trans (DFrame.of_memFrame f₂) fun a h ↦ by
      addr_omega [h, hb]).trans (DFrame.of_memFrame f₃) fun _ h ↦ h
  have eprod : eListAt o (vecPtr u (s.getReg .x2 - 752)) 47 = vecEs u (s.getReg .x2 - 752) := by
    have hA := hpre.stack.above
    simp only [stackLo] at hA
    unfold verifyLayerStack at hA
    simp only [vecEs, hlen]
    exact Fp.eListAt fun i hi hw ↦ by addr_omega [hi, hw, hb, hA, ppR, hHu]
  -- the claim's weights
  have hmR := hpre.mu
  have hmS := hpre.muStack
  have emu : eListAt o (vecPtr s (lClaim s)) (vecLen s (lClaim s)).toNat = (claimAt s (lClaim s)).mu := by
    rw [B₃.eListAt (missVec B₃.heap hpre.mu hpre.muOut hpre.muSelf hpre.muStack hpre.muFree) (by
      rcases hmR with h0 | hR
      · exact Or.inl h0
      · exact Or.inr (by addr_omega [hR]))]
    rfl
  have hmulen : (claimAt s (lClaim s)).mu.length = (vecLen s (lClaim s)).toNat := by
    simp only [claimAt, vecEs, eListAt_length]
  have x8₃ : o.getReg .x8 = vecLen s (lClaim s) := by
    rw [b8000f0d8_x8 h₃, x19₂, kc _ (by addr_omega [hc]) (by addr_omega [hc])]; rfl
  have x21₃ : o.getReg .x21 = vecPtr s (lClaim s) + 16 := by
    rw [b8000f0d8_x21 h₃, x19₂, kc _ (by addr_omega [hc]) (by addr_omega [hc])]; rfl
  have w₃ (a : Word) (h1 : a ≠ s.getReg .x2 - 1680) (h2 : a ≠ s.getReg .x2 - 1600)
      (h3 : a ≠ s.getReg .x2 - 1616) (h4 : a ≠ s.getReg .x2 - 1624) : o.getMem a = u₂.getMem a :=
    keep₃ a (by rv_eval [x2₂, x19₂]; exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩)
  have m40 := b8000f0c0_m_x2_40 h₂
  have m48 := b8000f0c0_m_x2_48 h₂
  have m56 := b8000f0c0_m_x2_56 h₂
  have m104 := b8000f0c0_m_x2_104 h₂
  have m32 := b8000f0d8_m_x2_32 h₃
  have m88 := b8000f0d8_m_x2_88 h₃
  have m96 := b8000f0d8_m_x2_96 h₃
  have m112 := b8000f0d8_m_x2_112 h₃
  rw [x2₁] at m40 m48 m56 m104
  rw [x2₂] at m32 m88 m96 m112
  rv_eval [] at m40 m48 m56 m104 m32 m88 m96 m112
  have hl47 : u.getMem (s.getReg .x2 - 736) = 47 := by
    have e : vecLen u (s.getReg .x2 - 752) = 47 := BitVec.eq_of_toNat_eq hlen
    simp only [vecLen] at e; rv_eval [] at e; exact e
  have ptrEq : u.getMem (s.getReg .x2 - 744) = vecPtr u (s.getReg .x2 - 752) := by
    simp only [vecPtr]; rv_eval []
  refine ⟨o, hr₁.trans (hr₂.trans hr₃), {
    pc := b8000f0d8_pc h₃
    outer := {
      base := B₃
      inner := {
        rodata := B₃.rodata hpre
        x8 := by rw [x8₃, hmulen]
        x19 := b8000f0d8_x19 h₃
        elems := fun j hj ↦ by rw [← emu, getD_eListAt _ _ (by rw [← hmulen]; exact hj)]
        region := fun j hj ↦ by
          rcases hmR with h0 | hR
          · rw [hmulen, h0] at hj; omega
          · rw [hmulen] at hj; addr_omega [hR, hj] }
      mS := fun j hj ↦ by
        rcases hmR with h0 | hR
        · rw [hmulen, h0] at hj; omega
        · rw [hmulen] at hj; addr_omega [hR, hj, hmS, hb]
      x9 := b8000f0d8_x9 h₃
      x18 := by rw [k₃ .x18 (by decide), k₂ .x18 (by decide), b8000f0ac_x18 h₁, x2u]; rv_eval []; exact hl47
      x20 := b8000f0d8_x20 h₃
      x21 := x21₃
      x22 := b8000f0d8_x22 h₃
      ppM := by
        rw [m112, k₂ .x21 (by decide), b8000f0ac_x21 h₁, x2u]; rv_eval []; exact ptrEq
      prod := fun c hc ↦ by rw [← eprod, getD_eListAt _ _ hc]
      ppR := ⟨by have := hpre.heap.lo; omega, by have := B.heap.hi; omega, ppR.2.2⟩ }
    x10 := b8000f0d8_x10 h₃
    x24 := by rw [k₃ .x24 (by decide), k₂ .x24 (by decide), k₁ .x24 (by decide), N.x24]
    x25 := b8000f0d8_x25 h₃
    x26 := b8000f0d8_x26 h₃
    x27 := b8000f0d8_x27 h₃
    slots := {
      mp := by rw [m32, x19₂, kc _ (by addr_omega [hc]) (by addr_omega [hc])]; rfl
      plen := by
        rw [w₃ _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]),
          m40, b8000f0ac_x18 h₁, x2u]
        rv_eval []; exact hl47
      out := by
        rw [w₃ _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]),
          m48, k₁ .x8 (by decide), N.x8]
      claim := by
        rw [w₃ _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]),
          m56, k₁ .x19 (by decide), N.x19]
      step := by rw [m88, k₂ .x22 (by decide), k₁ .x22 (by decide), N.x22]
      depth := by rw [m96, k₂ .x9 (by decide), k₁ .x9 (by decide), N.x9]
      p := by
        rw [w₃ _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]),
          m104, k₁ .x20 (by decide), N.x20]
      pp := by rw [m112, k₂ .x21 (by decide), b8000f0ac_x21 h₁, x2u]; rv_eval []; exact ptrEq }
    plen := by simp only [vecEs, eListAt_length, hlen]
    pbuf := ⟨ppR.1, by rw [hN]; exact ppR.2.1⟩
    rest := ?_ }⟩
  refine ((Rest.start s).congr (verifyLayerRust_eq _ _ _)).step fun T hT ↦ ?_
  have hv := N.result T hT
  generalize hx : (TM.nextScalars productBits).run T = r at hv
  rcases r with _ | ⟨xs, T'⟩
  · exact absurd hv hok
  · refine ⟨T', by rw [hv.2.1.elems], ?_⟩
    exact B₂.slots_tat hpre B₃ f₃ (by addr_omega [hb]) (by addr_omega [hb])
      (B₁.slots_tat hpre B₂ f₂ (by addr_omega [hb]) (by addr_omega [hb])
        (transcriptAt_congr (b8000f0ac_mem_same h₁) hv.2.2))

/-- After the projected value, at `0x8000f1cc`. -/
structure J1 (s u : MachineState) (pp : Word) (product : List E) : Prop where
  pc : u.pc = 0x8000f1cc
  base : Base s u
  slots : S1 s u (vecPtr s (lClaim s)) pp
  x8 : u.getReg .x8 = vecLen s (lClaim s)
  x24 : u.getReg .x24 = s.getReg .x12
  acc : (u.getReg .x27, u.getReg .x26, u.getReg .x25) =
    limbs (projectedRust (claimAt s (lClaim s)).mu product)
  plen : product.length = 47
  prod : eListAt u pp 47 = product
  pbuf : heapNext s ≤ pp.toNat ∧ pp.toNat + 24 * 47 ≤ heapNext u
  palign : pp.toNat % 8 = 0
  rest : Rest s u (TM.require (check1 (shapeOf s) (s.getReg .x14).toNat (claimAt s (lClaim s))
    product) >>= fun _ ↦ stage2 (claimAt s (lClaim s)) product)

theorem proj (hM : MulSpec) {s o : MachineState} {pp : Word} {product : List E}
    (hpre : VerifyLayerPre s) (Z : E0 s o pp product) :
    ∃ v, Reaches Image.code o v ∧ (J1 s v pp product ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have L := Z.outer
  have P₀ : PO s o o (claimAt s (lClaim s)).mu product 0 := {
    base := L.base
    regs := fun _ _ ↦ rfl
    x10 := Z.x10
    acc := by rw [Z.x27, Z.x26, Z.x25]; exact limbs_zero.symm
    le := by decide
    frame := DFrame.refl _ _ }
  obtain ⟨v, hr, ⟨P, hpc⟩ | hd⟩ := outer_loop hM hpre L 47 0 o (by decide) (by decide) P₀ Z.pc
  swap
  · exact ⟨v, hr, Or.inr hd⟩
  have hA := hpre.stack.above
  simp only [stackLo] at hA
  unfold verifyLayerStack at hA hb
  have ppR := L.ppR
  have miss (a : Word) (h1 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 2736 ∨
      (s.getReg .x2).toNat - 1712 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
      (s.getReg .x2).toNat - 1424 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 752) :
      v.getMem a = o.getMem a := P.frame a fun i hi hw ↦ by
    simp only [ScrP] at hw; rcases hw with hw | hw | hw <;> addr_omega [hi, hw, h1, hb]
  have hNv : v.getMem nextAddr = o.getMem nextAddr := by
    have hnx := hpre.stack.next
    unfold verifyLayerStack at hnx
    exact P.frame _ fun i hi hw ↦ by
      simp only [ScrP] at hw; rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have S := Z.slots
  refine ⟨v, hr, Or.inl {
    pc := hpc
    base := P.base
    slots := {
      mp := by rw [miss _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)), S.mp]
      plen := by rw [miss _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)), S.plen]
      out := by rw [miss _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)), S.out]
      claim := by rw [miss _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)), S.claim]
      step := by rw [miss _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)), S.step]
      depth := by rw [miss _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)), S.depth]
      p := by rw [miss _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)), S.p]
      pp := by rw [miss _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)), S.pp] }
    x8 := by rw [P.regs .x8 (by decide)]; have := L.inner.x8; exact BitVec.eq_of_toNat_eq (by
      rw [this]; simp only [claimAt, vecEs, eListAt_length])
    x24 := by rw [P.regs .x24 (by decide), Z.x24]
    acc := by rw [P.acc, projectedRust_eq_sum]; rfl
    plen := Z.plen
    prod := by
      rw [← Z.plen]
      apply List.ext_getElem (by simp [eListAt_length])
      intro c h1 _
      rw [eListAt_length] at h1
      rw [eListAt_getElem, ← List.getD_eq_getElem _ 0, ← L.prod c (by rw [← Z.plen]; exact h1)]
      unfold Rv64Verifier.eAt
      rw [Z.plen] at h1
      rw [miss _ (Or.inl (by addr_omega [ppR, h1, hb, hA])), miss _ (Or.inl (by addr_omega [ppR, h1, hb, hA])),
        miss _ (Or.inl (by addr_omega [ppR, h1, hb, hA]))]
    pbuf := by simp only [heapNext, hNv]; exact Z.pbuf
    palign := ppR.2.2
    rest := Z.rest.keep fun T hT ↦ L.base.tat hpre P.base.heap P.frame (fun a ha ↦ by
      have hS := hpre.self.self
      have hss := hpre.selfStack
      unfold verifyLayerStack at hss
      exact ⟨by simp only [ScrP] at ha; rcases ha with ha | ha | ha <;> addr_omega [ha, hb, hS, hss],
        (scrP_lw hpre ha).1⟩) hT }⟩

end Rv64Verifier.Gkr.Layer
