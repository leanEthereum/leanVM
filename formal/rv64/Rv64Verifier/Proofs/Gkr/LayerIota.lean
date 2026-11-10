import Rv64Verifier.Proofs.Gkr.LayerProj

/-!
# `keccak::verify_layer`: `iota`

`keccak.rs:136-141`, inlined at `0x8000f1cc..0x8000f218`: `eq_kernel` of the point's segment part
into `f + 1560`, then per segment (at most `24 / depth = 2`) the claim's position weights on the
bits of its round constant (`KECCAK_RC`, `.rodata` at `0xa0000490`; `iota_inner_loop`, in `x13`,
`x12`, `x10`), times the segment's weight, summed in `x19`, `x20`, `x24`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The weights of the round constant's first `z` bits. -/
def iotaIn (w : List E) (cst : BitVec 64) (z : Nat) : E :=
  sumE (((List.range z).filter fun z ↦ bit64 cst z).map fun z ↦ w.getD z 0)

theorem iotaIn_succ (w : List E) (cst : BitVec 64) (z : Nat) :
    iotaIn w cst (z + 1) = iotaIn w cst z + if bit64 cst z then w.getD z 0 else 0 :=
  sumE_filter_succ _ _ _

theorem rc_word {u : MachineState} (h : RodataOk u) {i : Nat} (hi : i < 24) :
    u.getMem (0xa0000490 + BitVec.ofNat 64 (8 * i)) = (keccakRC.getD i 0).toBitVec := by
  interval_cases i <;> exact h.word

theorem shift_and_one (x : Word) (z : Nat) :
    ((x >>> z) &&& 1) = 0 ↔ bit64 x z = false := by
  unfold bit64
  have h : ((x >>> z) &&& 1#64) = 0 ∨ ((x >>> z) &&& 1#64) = 1#64 := by
    have : ((x >>> z) &&& 1#64).toNat < 2 := by
      rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    rcases (by omega : ((x >>> z) &&& 1#64).toNat = 0 ∨ ((x >>> z) &&& 1#64).toNat = 1) with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (BitVec.eq_of_toNat_eq h)
  rcases h with h | h <;> simp [h]

/-- In the bit loop, from `o` (at `0x8000f99c`): `z` bits done. -/
structure QI (o u : MachineState) (wp : Word) (w : List E) (cst : BitVec 64) (z : Nat) : Prop where
  regs : ∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x7, .x8, .x9, .x11, .x15, .x18, .x19, .x20, .x21, .x22,
    .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31], u.getReg r = o.getReg r
  mem : ∀ a, u.getMem a = o.getMem a
  x14 : u.getReg .x14 = BitVec.ofNat 64 z
  x15 : o.getReg .x15 = cst
  x16 : u.getReg .x16 = wp + BitVec.ofNat 64 (24 * z) + 16
  acc : (u.getReg .x13, u.getReg .x12, u.getReg .x10) = limbs (iotaIn w cst z)

/-- What the bit loop reads: the claim's position weights. -/
structure WOk (o : MachineState) (wp : Word) (w : List E) : Prop where
  x9 : (o.getReg .x9).toNat = w.length
  x22 : o.getReg .x22 = 64
  elems : ∀ j < w.length, eAt o (wp + BitVec.ofNat 64 (24 * j)) = w.getD j 0
  region : ∀ j < w.length, Region (wp + BitVec.ofNat 64 (24 * j)) 24

set_option maxHeartbeats 2000000 in
theorem iota_inner_step {o u : MachineState} {wp : Word} {w : List E} {cst : BitVec 64} {z : Nat}
    (I : QI o u wp w cst z) (hpc : u.pc = 0x8000f99c) (hz : z < 64) (K : WOk o wp w) :
    ∃ v, Reaches Image.code u v ∧ ((QI o v wp w cst (z + 1) ∧
      ((z + 1 < 64 ∧ v.pc = 0x8000f99c) ∨ (z + 1 = 64 ∧ v.pc = 0x8000f900))) ∨
      Dead Image.code v) := by
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f99c_spec hpc trivial
  have k₁ := b8000f99c_keeps h₁
  have hm₁ := b8000f99c_mem_same h₁
  have x15u : u.getReg .x15 = cst := (I.regs .x15 (by decide)).trans I.x15
  have hz64 : (BitVec.ofNat 64 z).toNat % 64 = z := by rw [BitVec.toNat_ofNat]; omega
  have tail (t : MachineState) (ht : t.pc = 0x8000f990)
      (kt : ∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x7, .x8, .x9, .x11, .x14, .x15, .x16, .x18, .x19, .x20,
        .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31], t.getReg r = u.getReg r)
      (mt : ∀ a, t.getMem a = u.getMem a)
      (at' : (t.getReg .x13, t.getReg .x12, t.getReg .x10) = limbs (iotaIn w cst (z + 1))) :
      ∃ v, Reaches Image.code t v ∧ QI o v wp w cst (z + 1) ∧
        ((z + 1 < 64 ∧ v.pc = 0x8000f99c) ∨ (z + 1 = 64 ∧ v.pc = 0x8000f900)) := by
    obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000f990_spec ht trivial
    have k := b8000f990_keeps h
    have x14t : t.getReg .x14 = BitVec.ofNat 64 z := (kt .x14 (by decide)).trans I.x14
    have x22t : t.getReg .x22 = 64 :=
      ((kt .x22 (by decide)).trans (I.regs .x22 (by decide))).trans K.x22
    refine ⟨v, hr, {
      regs := fun r hr ↦ by rw [k r (mem_of_mem hr _), kt r (mem_of_mem hr _), I.regs r hr]
      mem := fun a ↦ by rw [b8000f990_mem_same h, mt, I.mem]
      x14 := by rw [b8000f990_x14 h, x14t, ofNat_succ]
      x15 := I.x15
      x16 := by rw [b8000f990_x16 h, kt .x16 (by decide), I.x16]; exact ofNat_step' _ 24 z 16
      acc := by rw [k .x13 (by decide), k .x12 (by decide), k .x10 (by decide), at'] }, ?_⟩
    by_cases hl : z + 1 < 64
    · refine Or.inl ⟨hl, b8000f990_pc_not_taken h ?_⟩
      rw [x14t, x22t, ofNat_succ]
      intro h64
      have := congrArg BitVec.toNat h64
      rw [BitVec.toNat_ofNat] at this
      change (z + 1) % 2 ^ 64 = 64 at this
      omega
    · refine Or.inr ⟨by omega, b8000f990_pc_taken h ?_⟩
      rw [x14t, x22t, ofNat_succ, show z + 1 = 64 by omega]
      rfl
  cases hb : bit64 cst z
  · have pc₁ : u₁.pc = 0x8000f990 := Sym.Expect.Holds.pc_eq h₁ (by
      rv_eval [x15u, I.x14, hz64, (shift_and_one cst z).mpr hb]
      decide)
    obtain ⟨v, hr, P, hpc'⟩ := tail u₁ pc₁ (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁ (by
      rw [k₁ .x13 (by decide), k₁ .x12 (by decide), k₁ .x10 (by decide), I.acc, iotaIn_succ, hb]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero])
    exact ⟨v, hr₁.trans hr, Or.inl ⟨P, hpc'⟩⟩
  · have hnz : ((cst >>> z) &&& 1) ≠ 0 := fun h ↦ by
      rw [(shift_and_one cst z).mp h] at hb; cases hb
    have pc₁ : u₁.pc = 0x8000f9a8 := Sym.Expect.Holds.pc_eq h₁ (by
      rv_eval [x15u, I.x14, hz64]
      exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hnz (beq_iff_eq.mp h)))
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f9a8_spec pc₁ trivial
    have k₂ := b8000f9a8_keeps h₂
    have x14₁ : (u₁.getReg .x14).toNat = z := by
      rw [k₁ .x14 (by decide), I.x14, BitVec.toNat_ofNat]; omega
    have x9₁ : (u₁.getReg .x9).toNat = w.length := by
      rw [k₁ .x9 (by decide), I.regs .x9 (by decide), K.x9]
    by_cases hlt : z < w.length
    · have hR := K.region z hlt
      have x16₂ : u₂.getReg .x16 = wp + BitVec.ofNat 64 (24 * z) + 16 := by
        rw [k₂ .x16 (by decide), k₁ .x16 (by decide), I.x16]
      obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f9ac_spec
        (b8000f9a8_pc_not_taken h₂ (by rw [x14₁, x9₁]; exact hlt)) (by
          rv_eval [x16₂]
          and_intros <;> (refine Region.valid hR ?_ ?_ ?_ <;> addr_omega [hR]))
      have k₃ := b8000f9ac_keeps h₃
      have e := K.elems z hlt
      have m₂ (a : Word) : u₂.getMem a = o.getMem a := by
        rw [b8000f9a8_mem_same h₂, hm₁, I.mem]
      obtain ⟨v, hr, P, hpc'⟩ := tail u₃ (b8000f9ac_pc h₃)
        (fun r hr ↦ by rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)])
        (fun a ↦ by rw [b8000f9ac_mem_same h₃, b8000f9a8_mem_same h₂, hm₁]) (by
          rw [b8000f9ac_x13 h₃, b8000f9ac_x12 h₃, b8000f9ac_x10 h₃, x16₂, iotaIn_succ, hb]
          simp only [↓reduceIte]
          rw [limbs_add, ← I.acc, ← e, limbs_eAt]
          rv_eval [m₂, k₂ .x13 (by decide), k₂ .x12 (by decide), k₂ .x10 (by decide),
            k₁ .x13 (by decide), k₁ .x12 (by decide), k₁ .x10 (by decide), BitVec.xor_comm])
      exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans hr)), Or.inl ⟨P, hpc'⟩⟩
    · exact ⟨u₂, hr₁.trans hr₂, Or.inr (dead_of_fetch (by
        rw [b8000f9a8_pc_taken h₂ (by rw [x14₁, x9₁]; omega)]; exact trap))⟩

theorem iota_inner_loop {o : MachineState} {wp : Word} {w : List E} {cst : BitVec 64}
    (K : WOk o wp w) : ∀ n z u, z + n = 64 → 0 < n → QI o u wp w cst z →
      u.pc = 0x8000f99c → ∃ v, Reaches Image.code u v ∧
        ((QI o v wp w cst 64 ∧ v.pc = 0x8000f900) ∨ Dead Image.code v)
  | 0, _, _, _, h0, _, _ => absurd h0 (Nat.lt_irrefl 0)
  | n + 1, z, u, hn, _, I, hpc => by
    obtain ⟨v, hr, ⟨P, ⟨hl, hpc'⟩ | ⟨he, hpc'⟩⟩ | hd⟩ := iota_inner_step I hpc (by omega) K
    · obtain ⟨t, hr', ht⟩ := iota_inner_loop K n (z + 1) v (by omega) (by omega) P hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · rw [he] at P
      exact ⟨v, hr, Or.inl ⟨P, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

/-- The segments' weighted sums after `k` segments. -/
def iotaAcc (segs w : List E) (step k : Nat) : E :=
  (segs.zipIdx.take k).foldl (fun iota (ws : E × Nat) ↦ iota + ws.1 *
    iotaIn w (keccakRC.getD (12 * (ws.2 + 1) - step - 1) 0).toBitVec 64) 0

theorem iotaAcc_succ (segs w : List E) (step : Nat) {k : Nat} (hk : k < segs.length) :
    iotaAcc segs w step (k + 1) = iotaAcc segs w step k + segs.getD k 0 *
      iotaIn w (keccakRC.getD (12 * (k + 1) - step - 1) 0).toBitVec 64 := by
  unfold iotaAcc
  rw [List.take_succ_eq_append_getElem (by rw [List.length_zipIdx]; exact hk), List.foldl_append,
    List.getElem_zipIdx, List.getD_eq_getElem _ _ hk]
  simp

theorem iotaAcc_two (segs w : List E) (step : Nat) {k : Nat} (hk : k = min 2 segs.length) :
    iotaAcc segs w step k = iotaAcc segs w step 2 := by
  unfold iotaAcc
  congr 1
  rcases Nat.le_total 2 segs.length with h | h
  · rw [hk, Nat.min_eq_left h]
  · rw [hk, Nat.min_eq_right h, List.take_of_length_le (by rw [List.length_zipIdx]),
      List.take_of_length_le (by rw [List.length_zipIdx]; exact h)]

theorem iotaRust_acc (l step : Nat) (claim : KeccakClaim) :
    iotaRust ⟨l, 12⟩ step claim =
      iotaAcc (eqKernelRust (claim.point.drop (l - 4))) claim.weights step 2 := by
  simp only [iotaRust, iotaAcc, iotaIn, KeccakShape.segments, KeccakShape.packBits]

theorem rc_index (k : Nat) (x : Word) (hk : k < 2) (hs : x.toNat < 12) :
    (BitVec.ofNat 64 k + 1) * 12 + (x ^^^ 0xffffffffffffffff) =
      BitVec.ofNat 64 (12 * (k + 1) - x.toNat - 1) := by
  apply BitVec.eq_of_toNat_eq
  have e : (x ^^^ 0xffffffffffffffff).toNat = 2 ^ 64 - 1 - x.toNat := by
    rw [show (0xffffffffffffffff : Word) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes,
      BitVec.toNat_not]
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_add, e, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl, show (12 : Word).toNat = 12 from rfl]
  omega

theorem ofNat_mul8 (i : Nat) : BitVec.ofNat 64 i * 8 = BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]
  omega

/-- The segment loop's entry `o₀`. -/
structure QOk (s o₀ : MachineState) (wp sg : Word) (segs w : List E) : Prop where
  base : Base s o₀
  wok : WOk o₀ wp w
  wS : ∀ j < w.length, Apart (wp + BitVec.ofNat 64 (24 * j)) 24 (s.getReg .x2 - 2736) 2736
  sgE : ∀ k < segs.length, eAt o₀ (sg + BitVec.ofNat 64 (24 * k)) = segs.getD k 0
  sgR : heapStart ≤ sg.toNat ∧ sg.toNat + 24 * segs.length ≤ heapEnd ∧ sg.toNat % 8 = 0
  step : (s.getReg .x14).toNat < 12
  rc : o₀.getMem (s.getReg .x2 - 1648) = 0xa0000490
  wpM : o₀.getMem (s.getReg .x2 - 1640) = wp + 16
  nstep : o₀.getMem (s.getReg .x2 - 1632) = s.getReg .x14 ^^^ 0xffffffffffffffff
  endM : o₀.getMem (s.getReg .x2 - 1624) = sg + BitVec.ofNat 64 (24 * segs.length)
  depth : o₀.getMem (s.getReg .x2 - 1616) = 12

/-- The segment loop at its head `0x8000f93c` after `k` segments. -/
structure QO (s o₀ o : MachineState) (sg : Word) (segs w : List E) (k : Nat) : Prop where
  base : Base s o
  regs : ∀ r ∈ [Reg.x2, .x8, .x9, .x22, .x25, .x26, .x27], o.getReg r = o₀.getReg r
  x11 : o.getReg .x11 = sg + BitVec.ofNat 64 (24 * k)
  x21 : o.getReg .x21 = BitVec.ofNat 64 (2 - k)
  x23 : o.getReg .x23 = BitVec.ofNat 64 k
  acc : (o.getReg .x19, o.getReg .x20, o.getReg .x24) =
    limbs (iotaAcc segs w (s.getReg .x14).toNat k)
  lt : k < 2
  le : k ≤ segs.length
  frame : DFrame o₀ o (ScrP s)

/-- The segment loop done, at `0x8000f218`. -/
structure QX (s o₀ o : MachineState) (segs w : List E) : Prop where
  base : Base s o
  regs : ∀ r ∈ [Reg.x2, .x8, .x25, .x26, .x27], o.getReg r = o₀.getReg r
  acc : (o.getReg .x19, o.getReg .x20, o.getReg .x24) =
    limbs (iotaAcc segs w (s.getReg .x14).toNat 2)
  frame : DFrame o₀ o (ScrP s)

theorem scrP_miss {s : MachineState} (hpre : VerifyLayerPre s) {a : Word}
    (h : (s.getReg .x2).toNat - 1712 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
      (s.getReg .x2).toNat - 1424 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 752 ∨
      (s.getReg .x2).toNat - 728 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat ∨
      a.toNat + 8 ≤ (s.getReg .x2).toNat - 2736) :
    ∀ i < 8, ¬ ScrP s (a + BitVec.ofNat 64 i) := fun i hi hw ↦ by
  have hb := bounds hpre
  unfold verifyLayerStack at hb
  simp only [ScrP] at hw
  rcases hw with hw | hw | hw <;> addr_omega [hi, hw, h, hb]

theorem QO.wok {s o₀ o : MachineState} {wp sg : Word} {segs w : List E} {k : Nat}
    (hpre : VerifyLayerPre s) (L : QOk s o₀ wp sg segs w) (Q : QO s o₀ o sg segs w k) :
    WOk o wp w := by
  have hb := bounds hpre
  unfold verifyLayerStack at hb
  exact {
    x9 := by rw [Q.regs .x9 (by decide)]; exact L.wok.x9
    x22 := by rw [Q.regs .x22 (by decide)]; exact L.wok.x22
    elems := fun j hj ↦ by
      rw [← L.wok.elems j hj]
      have hR := L.wok.region j hj
      have hA := L.wS j hj
      exact Q.frame.eAt fun i hi hw ↦ by
        simp only [ScrP] at hw
        rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hb, hR, hA]
    region := L.wok.region }


set_option maxHeartbeats 4000000 in
theorem iota_step (hM : MulSpec) {s o₀ o : MachineState} {wp sg : Word} {segs w : List E}
    {k : Nat} (hpre : VerifyLayerPre s) (L : QOk s o₀ wp sg segs w) (Q : QO s o₀ o sg segs w k)
    (hpc : o.pc = 0x8000f93c) :
    ∃ v, Reaches Image.code o v ∧ ((QO s o₀ v sg segs w (k + 1) ∧ v.pc = 0x8000f93c) ∨
      (QX s o₀ v segs w ∧ v.pc = 0x8000f218) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := Q.base
  have hA := hpre.stack.above
  simp only [stackLo] at hA
  unfold verifyLayerStack at hA hb
  have sgR := L.sgR
  have mo (a : Word) (h : (s.getReg .x2).toNat - 1712 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
      (s.getReg .x2).toNat - 1424 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 752 ∨
      (s.getReg .x2).toNat - 728 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat ∨
      a.toNat + 8 ≤ (s.getReg .x2).toNat - 2736) : o.getMem a = o₀.getMem a :=
    Q.frame a (scrP_miss hpre h)
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f93c_spec hpc (by
    rv_eval [B.x2]; valid_access hpre.stack.valid [hb])
  have k₁ := b8000f93c_keeps h₁
  have hm₁ := b8000f93c_mem_same h₁
  have endo : o.getMem (o.getReg .x2 + 88) = sg + BitVec.ofNat 64 (24 * segs.length) := by
    rw [B.x2]; rv_eval []; rw [mo _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩), L.endM]
  by_cases hk : k = segs.length
  · -- every segment done
    refine ⟨u₁, hr₁, Or.inr (Or.inl ⟨{
      base := B.same ((k₁ .x2 (by decide)).trans B.x2) hm₁
      regs := fun r hr ↦ by rw [k₁ r (mem_of_mem hr _), Q.regs r (mem_of_mem hr _)]
      acc := by
        rw [k₁ .x19 (by decide), k₁ .x20 (by decide), k₁ .x24 (by decide), Q.acc,
          iotaAcc_two _ _ _ (by have := Q.lt; omega)]
      frame := Q.frame.trans (DFrame.of_same hm₁ _) fun _ h ↦ h }, ?_⟩)⟩
    exact b8000f93c_pc_taken h₁ (by rw [Q.x11, endo, hk])
  have hks : k < segs.length := by have := Q.le; omega
  have pc₁ : u₁.pc = 0x8000f944 := b8000f93c_pc_not_taken h₁ (by
    rw [Q.x11, endo]; addr_omega [sgR, hks])
  -- the round constant's index
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f944_spec pc₁ (by
    rv_eval [x2₁]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₂ := b8000f944_keeps h₂
  have hst := L.step
  have hlt := Q.lt
  have eidx : (u₁.getReg .x23 + 1) * u₁.getMem (u₁.getReg .x2 + 96) + u₁.getMem (u₁.getReg .x2 + 80) =
      BitVec.ofNat 64 (12 * (k + 1) - (s.getReg .x14).toNat - 1) := by
    rw [k₁ .x23 (by decide), Q.x23, x2₁, hm₁, hm₁]
    rv_eval []
    rw [mo _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
      mo _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩), L.depth, L.nstep]
    exact rc_index k _ hlt hst
  have pc₂ : u₂.pc = 0x8000f960 := b8000f944_pc_not_taken h₂ (by
    rw [eidx]; simp only [BitVec.toNat_ofNat, show (23 : Word).toNat = 23 from rfl]; omega)
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have hm₂ := b8000f944_mem_same h₂
  have hro₂ : RodataOk u₂ := (B.rodata hpre).dframe
    (DFrame.of_same (fun a ↦ by rw [hm₂, hm₁]) (fun _ ↦ False)) fun _ _ h ↦ h
  have hidx : 12 * (k + 1) - (s.getReg .x14).toNat - 1 < 24 := by omega
  have x15₂ : u₂.getReg .x15 = BitVec.ofNat 64 (12 * (k + 1) - (s.getReg .x14).toNat - 1) := by
    rw [b8000f944_x15 h₂, eidx]
  have m64 : u₂.getMem (s.getReg .x2 - 1648) = 0xa0000490 := by
    rw [hm₂, hm₁, mo _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩), L.rc]
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f960_spec pc₂ (by
    rv_eval [x2₂, m64, x15₂, ofNat_mul8]
    refine ⟨by valid_access hpre.stack.valid [hb], ?_, by valid_access hpre.stack.valid [hb]⟩
    exact Region.valid (a := 0xa0000490) (n := 192) (by addr_omega []) (by addr_omega [hidx])
      (by addr_omega [hidx]) (by addr_omega [hidx]))
  have k₃ := b8000f960_keeps h₃
  have hm₃ := b8000f960_mem_same h₃
  have x15₃ : u₃.getReg .x15 =
      (keccakRC.getD (12 * (k + 1) - (s.getReg .x14).toNat - 1) 0).toBitVec := by
    rw [b8000f960_x15 h₃, x2₂, x15₂]
    rv_eval [m64, ofNat_mul8]
    exact rc_word hro₂ hidx
  have Wo := Q.wok hpre L
  have m₃ (a : Word) : u₃.getMem a = o.getMem a := by rw [hm₃, hm₂, hm₁]
  have W₃ : WOk u₃ wp w := {
    x9 := by rw [k₃ .x9 (by decide), k₂ .x9 (by decide), k₁ .x9 (by decide)]; exact Wo.x9
    x22 := by rw [k₃ .x22 (by decide), k₂ .x22 (by decide), k₁ .x22 (by decide)]; exact Wo.x22
    elems := fun j hj ↦ by rw [← Wo.elems j hj]; unfold Rv64Verifier.eAt; rw [m₃, m₃, m₃]
    region := Wo.region }
  have wpo : u₂.getMem (s.getReg .x2 - 1640) = wp + 16 := by
    rw [hm₂, hm₁, mo _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩), L.wpM]
  have I₀ : QI u₃ u₃ wp w (keccakRC.getD (12 * (k + 1) - (s.getReg .x14).toNat - 1) 0).toBitVec 0 := {
    regs := fun _ _ ↦ rfl
    mem := fun _ ↦ rfl
    x14 := b8000f960_x14 h₃
    x15 := x15₃
    x16 := by
      rw [b8000f960_x16 h₃, x2₂]; rv_eval [wpo]
      rw [show BitVec.ofNat 64 (24 * 0) = 0 from rfl, Sym.add_zero_lit]
    acc := by
      rw [b8000f960_x13 h₃, b8000f960_x12 h₃, b8000f960_x10 h₃, show iotaIn w _ 0 = 0 from rfl,
        limbs_zero] }
  obtain ⟨u₄, hr₄, ⟨I, hpc₄⟩ | hd⟩ :=
    iota_inner_loop W₃ 64 0 u₃ (by omega) (by omega) I₀ (b8000f960_pc h₃)
  swap
  · exact ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr hd)⟩
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 1712 := by
    rw [I.regs .x2 (by decide), k₃ .x2 (by decide), x2₂]
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000f900_spec hpc₄ (by
    rv_eval [x2₄]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₅ := b8000f900_keeps h₅
  have f₅ := b8000f900_frame h₅ (by rw [x2₄]; addr_omega [hb])
  rw [x2₄] at f₅
  rv_eval [] at f₅
  have e₅ : eAt u₅ (s.getReg .x2 - 752) =
      iotaIn w (keccakRC.getD (12 * (k + 1) - (s.getReg .x14).toNat - 1) 0).toBitVec 64 := by
    apply eAt_eq_of_limbs
    rw [← I.acc]
    have n0 := b8000f900_m_x2_960 h₅
    have n8 := b8000f900_m_x2_968 h₅
    have n16 := b8000f900_m_x2_976 h₅
    rw [x2₄] at n0 n8 n16
    rv_eval [] at n0 n8 n16
    rv_eval [n0, n8, n16]
  have x11₄ : u₄.getReg .x11 = sg + BitVec.ofNat 64 (24 * k) := by
    rw [I.regs .x11 (by decide), k₃ .x11 (by decide), k₂ .x11 (by decide), k₁ .x11 (by decide), Q.x11]
  have x10₅ : u₅.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000f900_x10 h₅, x2₄]; rv_eval []
  have x12₅ : u₅.getReg .x12 = s.getReg .x2 - 752 := by rw [b8000f900_x12 h₅, x2₄]; rv_eval []
  have x11₅ : u₅.getReg .x11 = sg + BitVec.ofNat 64 (24 * k) := (k₅ .x11 (by decide)).trans x11₄
  have x2₅ : u₅.getReg .x2 = s.getReg .x2 - 1712 := (k₅ .x2 (by decide)).trans x2₄
  have m₅ (a : Word) (ha : ¬ Within a (s.getReg .x2 - 752) 24) : u₅.getMem a = o.getMem a := by
    rw [f₅ a ha, I.mem, m₃]
  have hro₅ : RodataOk u₅ := by
    have hrs := hpre.stack.rodata
    unfold verifyLayerStack at hrs
    refine (B.rodata hpre).dframe (w := (Within · (s.getReg .x2 - 752) 24)) (fun a ha ↦ by
      rw [m₅ a fun h ↦ ha 0 (by decide) (by rwa [Transcript.add_ofNat_zero])]) fun a ha hw ↦ by
        addr_omega [ha, hw, hb, hrs]
  have hvs : ValidMemRange (sg + BitVec.ofNat 64 (24 * k)) 3 :=
    heap_vmr (by addr_omega [sgR, hks]) (by addr_omega [sgR, hks]) (by addr_omega [sgR, hks])
  have hmp : MulPre u₅ := mul_pre hpre x2₅ hro₅ 1448 x10₅ (by decide) (by decide) (by decide)
    (by rw [x11₅]; exact hvs)
    (by rw [x11₅]; addr_omega [sgR, hks, hb, hA])
    (by rw [x10₅, x11₅]; addr_omega [sgR, hks, hb, hA])
    (by rw [x12₅]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x12₅]; addr_omega [hb])
    (by rw [x10₅, x12₅]; addr_omega [hb])
  obtain ⟨t, hr₆, ⟨hpc₆, hpres₆, hpost₆⟩ | hd⟩ :=
    hM.call (hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅)))) (b8000f900_pc h₅) hmp
  swap
  · exact ⟨t, hr₆, Or.inr (Or.inr hd)⟩
  have F₆ := mul_frame x2₅ hpost₆
  rw [x10₅] at F₆
  have v₆ := hpost₆.value
  rw [x10₅, x11₅, x12₅] at v₆
  have x2t : t.getReg .x2 = s.getReg .x2 - 1712 := (hpres₆.reg .x2).trans x2₅
  have eseg : eAt u₅ (sg + BitVec.ofNat 64 (24 * k)) = segs.getD k 0 := by
    rw [← L.sgE k hks]
    unfold Rv64Verifier.eAt
    rw [m₅ _ (by addr_omega [sgR, hks, hb, hA]), m₅ _ (by addr_omega [sgR, hks, hb, hA]),
      m₅ _ (by addr_omega [sgR, hks, hb, hA]), mo _ (Or.inr (Or.inr (Or.inr (by addr_omega [sgR, hks, hb, hA])))),
      mo _ (Or.inr (Or.inr (Or.inr (by addr_omega [sgR, hks, hb, hA])))),
      mo _ (Or.inr (Or.inr (Or.inr (by addr_omega [sgR, hks, hb, hA]))))]
  have e264 : eAt t (s.getReg .x2 - 1448) = segs.getD k 0 *
      iotaIn w (keccakRC.getD (12 * (k + 1) - (s.getReg .x14).toNat - 1) 0).toBitVec 64 := by
    rw [v₆, eseg, e₅]
  obtain ⟨v, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000f91c_spec
    (by rw [hpc₆, returnAddress_eq, b8000f900_x1 h₅]; decide) (by
      rv_eval [x2t]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₇ := b8000f91c_keeps h₇
  have hm₇ := b8000f91c_mem_same h₇
  have rk (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27]) : t.getReg r = u₄.getReg r := by
    rw [hpres₆.reg r (mem_of_mem hr _), k₅ r (mem_of_mem hr _)]
  have x21t : t.getReg .x21 = BitVec.ofNat 64 (2 - (k + 1)) := by
    rw [rk .x21 (by decide), I.regs .x21 (by decide), b8000f960_x21 h₃, k₂ .x21 (by decide),
      k₁ .x21 (by decide), Q.x21]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
    omega
  have Fv : DFrame o v (ScrP s) := by
    refine ((DFrame.of_same m₃ _).trans ((DFrame.of_same I.mem _).trans (DFrame.of_memFrame f₅)
      fun a h ↦ ?_) fun _ h ↦ h).trans (F₆.trans (DFrame.of_same hm₇ _) fun _ h ↦ h) fun a h ↦ ?_
    · simp only [ScrP]; left; exact h
    · simp only [ScrP]; rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hNv : v.getMem nextAddr = o.getMem nextAddr := Fv _ fun i hi hw ↦ by
    have hnx := hpre.stack.next
    unfold verifyLayerStack at hnx
    simp only [ScrP] at hw; rcases hw with hw | hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have Bv : Base s v := B.next hpre (by rw [k₇ .x2 (by decide), x2t])
    ⟨by simp only [heapNext, hNv]; exact B.heap.lo, by simp only [heapNext, hNv]; exact B.heap.hi⟩
    (by simp only [heapNext, hNv]; exact le_refl _) Fv fun a h ↦ scrP_lw hpre h
  have accv : (v.getReg .x19, v.getReg .x20, v.getReg .x24) =
      limbs (iotaAcc segs w (s.getReg .x14).toNat (k + 1)) := by
    rw [b8000f91c_x19 h₇, b8000f91c_x20 h₇, b8000f91c_x24 h₇, x2t, rk .x19 (by decide),
      rk .x20 (by decide), rk .x24 (by decide), I.regs .x19 (by decide), I.regs .x20 (by decide),
      I.regs .x24 (by decide), k₃ .x19 (by decide), k₃ .x20 (by decide), k₃ .x24 (by decide),
      k₂ .x19 (by decide), k₂ .x20 (by decide), k₂ .x24 (by decide), k₁ .x19 (by decide),
      k₁ .x20 (by decide), k₁ .x24 (by decide), iotaAcc_succ _ _ _ hks, limbs_add, ← Q.acc, ← e264,
      limbs_eAt]
    rv_eval [BitVec.xor_comm]
  have regsv (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x9, .x22, .x25, .x26, .x27]) :
      v.getReg r = o₀.getReg r := by
    rw [k₇ r (mem_of_mem hr _), rk r (mem_of_mem hr _), I.regs r (mem_of_mem hr _),
      k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), Q.regs r hr]
  by_cases hl : k + 1 < 2
  · refine ⟨v, hr₆.trans hr₇, Or.inl ⟨{
      base := Bv
      regs := regsv
      x11 := by
        rw [b8000f91c_x11 h₇, rk .x18 (by decide), I.regs .x18 (by decide), b8000f960_x18 h₃,
          k₂ .x11 (by decide), k₁ .x11 (by decide), Q.x11]
        exact ofNat_step0 _ 24 k
      x21 := by rw [k₇ .x21 (by decide), x21t]
      x23 := by
        rw [k₇ .x23 (by decide), rk .x23 (by decide), I.regs .x23 (by decide), k₃ .x23 (by decide),
          b8000f944_x23 h₂, k₁ .x23 (by decide), Q.x23, ofNat_succ]
      acc := accv
      lt := hl
      le := hks
      frame := Q.frame.trans Fv fun _ h ↦ h }, b8000f91c_pc_not_taken h₇ ?_⟩⟩
    rw [x21t]; intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat] at this; change (2 - (k + 1)) % 2 ^ 64 = 0 at this; omega
  · refine ⟨v, hr₆.trans hr₇, Or.inr (Or.inl ⟨{
      base := Bv
      regs := fun r hr ↦ regsv r (mem_of_mem hr _)
      acc := by rw [accv, show k + 1 = 2 by omega]
      frame := Q.frame.trans Fv fun _ h ↦ h }, b8000f91c_pc_taken h₇ ?_⟩)⟩
    rw [x21t, show 2 - (k + 1) = 0 by omega]; rfl


theorem iota_loop (hM : MulSpec) {s o₀ : MachineState} {wp sg : Word} {segs w : List E}
    (hpre : VerifyLayerPre s) (L : QOk s o₀ wp sg segs w) :
    ∀ n k o, k + n = 2 → QO s o₀ o sg segs w k → o.pc = 0x8000f93c →
      ∃ v, Reaches Image.code o v ∧ ((QX s o₀ v segs w ∧ v.pc = 0x8000f218) ∨ Dead Image.code v)
  | 0, k, o, hn, Q, _ => absurd Q.lt (by omega)
  | n + 1, k, o, hn, Q, hpc => by
    obtain ⟨v, hr, ⟨Q', hpc'⟩ | ⟨X, hpc'⟩ | hd⟩ := iota_step hM hpre L Q hpc
    · obtain ⟨t, hr', ht⟩ := iota_loop hM hpre L n (k + 1) v (by omega) Q' hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · exact ⟨v, hr, Or.inl ⟨X, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

end Rv64Verifier.Gkr.Layer
