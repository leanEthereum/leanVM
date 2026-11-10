import Rv64Verifier.Proofs.Gkr.LayerR9c

/-!
# `keccak::verify_layer`: `at_local`, its entry

`keccak.rs:163-170` at `0x8000f7e0..0x8000f888`: the value's upper limbs saved, the number of
lanes `min(ceil(weights.len / 64), eq_lane.len)`, the loop's head (`L10`) or, with no lane, the
second check's entry with `at_local = 0` (`K10`). What the loop and the second check write is
`W10`, what they keep `Fx`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-! ## The model -/

theorem atLocal_eq (w eqZ eqLane : List E) : atLocalRust w eqZ eqLane =
    sumE ((List.range (min ((w.length + 63) / 64) eqLane.length)).map fun k ↦
      eqLane.getD k 0 * dotRust eqZ ((w.drop (64 * k)).take 64)) := by
  unfold atLocalRust chunks
  congr 1
  have e : w.length + 64 - 1 = w.length + 63 := by omega
  apply List.ext_getElem
  · simp only [List.length_map, List.length_zip, List.length_range, e]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by omega)]

/-- The claim's weights. -/
abbrev wOf (s : MachineState) : List E := (claimAt s (lClaim s)).weights

/-- Lane `k`'s term of `at_local`. -/
abbrev atL (s : MachineState) (lp : List E) (k : Nat) : E :=
  (eqKernelRust (lp.drop 6)).getD k 0 * dotRust (eqKernelRust (lp.take 6)) (((wOf s).drop (64 * k)).take 64)

/-- The number of lanes. -/
abbrev mOf (s : MachineState) (lp : List E) : Nat :=
  min (((wOf s).length + 63) / 64) (eqKernelRust (lp.drop 6)).length

theorem atLocal_wOf (s : MachineState) (lp : List E) :
    atLocalRust (wOf s) (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) =
      sumE ((List.range (mOf s lp)).map (atL s lp)) :=
  atLocal_eq _ _ _

theorem claim_weights (s : MachineState) : wOf s =
    eListAt s (s.getMem (s.getReg .x15 + 56)) (s.getMem (s.getReg .x15 + 64)).toNat := by
  simp only [wOf, claimAt, vecEs, vecPtr, vecLen, lClaim]; rv_eval []

theorem ceil64 (x : Word) : (x >>> 6 + if BitVec.ult 0 (x &&& 63) = true then 1 else 0) =
    BitVec.ofNat 64 ((x.toNat + 63) / 64) := by
  have h1 : (x >>> 6).toNat = x.toNat / 64 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (x &&& 63).toNat = x.toNat % 64 := by
    rw [BitVec.toNat_and, show (63 : Word).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have z0 : (0 : Word).toNat = 0 := rfl
  have z1 : (1 : Word).toNat = 1 := rfl
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  by_cases h : x.toNat % 64 = 0
  · have e : BitVec.ult 0 (x &&& 63) = false := by
      simp only [BitVec.ult, h2, h, z0, Nat.lt_irrefl, decide_false]
    rw [e]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_add, h1, z0]
    omega
  · have e : BitVec.ult 0 (x &&& 63) = true := by
      simp only [BitVec.ult, h2, z0, decide_eq_true_eq]; omega
    rw [e]
    simp only [↓reduceIte, BitVec.toNat_add, h1, z1]
    omega

theorem f7f8_x23 {s t : MachineState} (h : b8000f7f8.Holds s t) :
    t.getReg .x23 = BitVec.ofNat 64 (((s.getReg .x9).toNat + 63) / 64) :=
  h.reg_eq .x23 rfl (by rv_eval []; exact ceil64 _)

theorem f7f8_pc {s t : MachineState} (h : b8000f7f8.Holds s t) :
    t.pc = if (BitVec.ofNat 64 (((s.getReg .x9).toNat + 63) / 64)).ult (s.getReg .x18) = true
      then 0x8000f810 else 0x8000f80c :=
  h.pc_eq (by
    rv_eval []
    exact congrArg (fun y : Word ↦ if y.ult (s.getReg .x18) = true then (0x8000f810 : Word)
      else 0x8000f80c) (ceil64 (s.getReg .x9)))

/-! ## What the loop and the second check write, and keep -/

/-- `f + 192 .. f + 240`, `f + 264`, `f + 960 .. f + 1008`, `f + 1560 .. f + 1608` and the callees'
stacks. -/
@[rv_addr] def W10 (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1520) 48 ∨ Within a (s.getReg .x2 - 1448) 24 ∨
    Within a (s.getReg .x2 - 752) 48 ∨ Within a (s.getReg .x2 - 152) 48 ∨
    Within a (s.getReg .x2 - 1712 - BitVec.ofNat 64 sumcheckStack) sumcheckStack

theorem w10_w9 {s w v : MachineState} (hpre : VerifyLayerPre s) {a : Word} (h : W10 s a) :
    W9 s w v a := by
  have hb := bounds hpre
  simp only [W10] at h
  rcases h with h | h | h | h | h
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inl (by addr_omega [h, hb])
  · exact Or.inr (Or.inl h)

theorem w10_body {s u v : MachineState} (hpre : VerifyLayerPre s) {a : Word} (h : W10 s a) :
    BodyW s u v a := by
  have hb := bounds hpre
  simp only [W10] at h
  exact Or.inl (by rcases h with h | h | h | h | h <;> addr_omega [h, hb])

theorem w10_lw {s v : MachineState} (hpre : VerifyLayerPre s) {a : Word} (h : W10 s a) :
    LW s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  have hb := bounds hpre
  simp only [W10] at h
  refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h | h | h | h <;> addr_omega [h, hb]

/-- A frame slot below `f + 192` misses `W10`. -/
theorem w10_low {s : MachineState} (hpre : VerifyLayerPre s) {y : Word} {n : Nat}
    (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat) (h2 : y.toNat + n ≤ (s.getReg .x2).toNat - 1520) :
    ∀ i < n, ¬ W10 s (y + BitVec.ofNat 64 i) := by
  intro i hi hw
  have hb := bounds hpre
  simp only [W10] at hw
  rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hb]

/-- What the loop and the second check keep: `K8`, the value's upper limbs at `f + 8` and
`f + 16`, `&t[2]` at `f + 32`, `t`, `eq_z` and `eq_lane`. -/
structure Fx (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale lv : E)
    (lp t : List E) (tp tn : Word) : Prop where
  k8 : K8 s v ip c point scale
  m8 : v.getMem (s.getReg .x2 - 1704) = (limbs lv).2.1
  m16 : v.getMem (s.getReg .x2 - 1696) = (limbs lv).2.2
  t2 : v.getMem (s.getReg .x2 - 1680) = tp + 48
  tl : t.length = 3
  tB : NewBuf s v tp (24 * tn.toNat) 8
  tE : eListAt v tp tn.toNat = t
  ezB : NewBuf s v (v.getMem (s.getReg .x2 - 1632)) (24 * (v.getMem (s.getReg .x2 - 1640)).toNat) 8
  ezE : eListAt v (v.getMem (s.getReg .x2 - 1632)) (v.getMem (s.getReg .x2 - 1640)).toNat =
    eqKernelRust (lp.take 6)
  elB : NewBuf s v (v.getMem (s.getReg .x2 - 1600)) (24 * (v.getMem (s.getReg .x2 - 1624)).toNat) 8
  elE : eListAt v (v.getMem (s.getReg .x2 - 1600)) (v.getMem (s.getReg .x2 - 1624)).toNat =
    eqKernelRust (lp.drop 6)

theorem Fx.keep {s v v' : MachineState} {ip : Word} {c : E} {point : List E} {scale lv : E}
    {lp t : List E} {tp tn : Word} (hpre : VerifyLayerPre s)
    (X : Fx s v ip c point scale lv lp t tp tn) (hH : HeapOk v) (hH' : HeapOk v')
    (hN : heapNext v ≤ heapNext v') (F : DFrame v v' (W10 s)) :
    Fx s v' ip c point scale lv lp t tp tn := by
  have hb := bounds hpre
  have F9 : DFrame v v' (W9 s v v') := F.mono fun a h ↦ w10_w9 hpre h
  have kw (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1520) : v'.getMem y = v.getMem y :=
    F y (w10_low hpre h1 h2)
  have e1632 := kw (s.getReg .x2 - 1632) (by addr_omega [hb]) (by addr_omega [hb])
  have e1640 := kw (s.getReg .x2 - 1640) (by addr_omega [hb]) (by addr_omega [hb])
  have e1600 := kw (s.getReg .x2 - 1600) (by addr_omega [hb]) (by addr_omega [hb])
  have e1624 := kw (s.getReg .x2 - 1624) (by addr_omega [hb]) (by addr_omega [hb])
  exact {
    k8 := X.k8.keep hpre hH hH' hN F9
    m8 := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb])]; exact X.m8
    m16 := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb])]; exact X.m16
    t2 := by rw [kw _ (by addr_omega [hb]) (by addr_omega [hb])]; exact X.t2
    tl := X.tl
    tB := newBuf_mono X.tB hN
    tE := by rw [w9_eList hpre hH F9 X.tB (le_refl _)]; exact X.tE
    ezB := by rw [e1632, e1640]; exact newBuf_mono X.ezB hN
    ezE := by rw [e1632, e1640, w9_eList hpre hH F9 X.ezB (le_refl _)]; exact X.ezE
    elB := by rw [e1600, e1624]; exact newBuf_mono X.elB hN
    elE := by rw [e1600, e1624, w9_eList hpre hH F9 X.elB (le_refl _)]; exact X.elE }

/-! ## The states -/

/-- The mirror's remaining run at the second check. -/
abbrev rest10 (s : MachineState) (c : E) (point : List E) (scale lv : E) (lp t : List E) :
    TM KeccakClaim :=
  TM.require (check2 (wOf s) (sumE (instanceWeightsRust c)) scale lv lp t) >>= fun _ ↦
    stage7 (instanceWeightsRust c) point (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) t

/-- The `at_local` loop's state, `k` lanes done. -/
structure AC (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale lv : E)
    (lp t : List E) (tp tn : Word) (k : Nat) : Prop where
  base : Base s v
  fx : Fx s v ip c point scale lv lp t tp tn
  x8 : v.getReg .x8 = (limbs lv).1
  x22 : v.getReg .x22 = s.getReg .x11
  x26 : v.getReg .x26 = 16
  x27 : v.getReg .x27 = tn
  x24 : v.getReg .x24 = tp
  x9 : v.getReg .x9 = BitVec.ofNat 64 ((wOf s).length - 64 * k)
  x19 : v.getReg .x19 = s.getMem (s.getReg .x15 + 56) + BitVec.ofNat 64 (1536 * k)
  x25 : v.getReg .x25 = v.getMem (s.getReg .x2 - 1600) + BitVec.ofNat 64 (24 * k)
  x23 : v.getReg .x23 = BitVec.ofNat 64 (mOf s lp - k)
  lt : k < mOf s lp
  acc : (v.getReg .x18, v.getReg .x20, v.getReg .x21) = limbs (sumE ((List.range k).map (atL s lp)))
  rest : Rest s v (rest10 s c point scale lv lp t)

/-- The `at_local` loop's head `0x8000f888`, `k` lanes done. -/
structure L10 (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale lv : E)
    (lp t : List E) (tp tn : Word) (k : Nat) : Prop extends
    AC s v ip c point scale lv lp t tp tn k where
  pc : v.pc = 0x8000f888

/-- `at_local` done, at `0x8000fa34`. -/
structure K10 (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale lv : E)
    (lp t : List E) (tp tn : Word) : Prop where
  pc : v.pc = 0x8000fa34
  base : Base s v
  fx : Fx s v ip c point scale lv lp t tp tn
  x8 : v.getReg .x8 = (limbs lv).1
  x22 : v.getReg .x22 = s.getReg .x11
  x26 : v.getReg .x26 = 16
  x27 : v.getReg .x27 = tn
  x24 : v.getReg .x24 = tp
  acc : (v.getReg .x18, v.getReg .x20, v.getReg .x21) =
    limbs (atLocalRust (wOf s) (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)))
  rest : Rest s v (rest10 s c point scale lv lp t)

/-! ## The entry -/

theorem sumE_range_zero (f : Nat → E) : sumE ((List.range 0).map f) = 0 := rfl

theorem reg_sub {r : Reg} {l l' : List Reg} (hl : ∀ x ∈ l, x ∈ l') (hr : r ∈ l) : r ∈ l' :=
  hl r hr

set_option maxHeartbeats 16000000 in
/-- `0x8000f7e0`: the value's upper limbs saved; no weight, or no lane, to the second check with
`at_local = 0`; otherwise the number of lanes and the loop's head. -/
theorem at_start {s v : MachineState} {ip : Word} {c : E} {point lp t : List E} {scale lv : E}
    (hpre : VerifyLayerPre s) (J : J10 s v ip c point scale lp lv t) :
    ∃ u, Reaches Image.code v u ∧
      (L10 s u ip c point scale lv lp t (v.getReg .x24) (v.getReg .x19) 0 ∨
        K10 s u ip c point scale lv lp t (v.getReg .x24) (v.getReg .x19) ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have B := J.base
  have K := J.k8
  have hc := hpre.claim
  have hcs := hpre.claimStack
  unfold verifyLayerStack at hb hcs
  have kc (y : Word) (h1 : (lClaim s).toNat ≤ y.toNat) (h2 : y.toNat + 8 ≤ (lClaim s).toNat + 96) :
      v.getMem y = s.getMem y :=
    B.keep (missClaim hpre B.heap) (by addr_omega [hc]) h1 h2
  have c64 : v.getMem (s.getReg .x15 + 64) = s.getMem (s.getReg .x15 + 64) :=
    kc _ (by addr_omega [hc]) (by addr_omega [hc])
  have c56 : v.getMem (s.getReg .x15 + 56) = s.getMem (s.getReg .x15 + 56) :=
    kc _ (by addr_omega [hc]) (by addr_omega [hc])
  have hwl : (wOf s).length = (s.getMem (s.getReg .x15 + 64)).toNat := by
    rw [claim_weights, eListAt_length]
  have hel : (eqKernelRust (lp.drop 6)).length = (v.getMem (s.getReg .x2 - 1624)).toNat := by
    rw [← J.elE, eListAt_length]
  -- `0x8000f7e0`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f7e0_spec J.pc (by
    rv_eval [B.x2, K.claim]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc])
      | addr_omega [hb, hcs, hc])
  have k₁ := b8000f7e0_keeps h₁
  have f₁ := b8000f7e0_frame h₁ (by rw [B.x2]; addr_omega [hb])
  rw [B.x2] at f₁
  rv_eval [] at f₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.slots hpre x2₁ f₁ (by addr_omega [hb]) (by addr_omega [hb])
  have hnx := hpre.stack.next
  simp only [stackLo] at hnx
  unfold verifyLayerStack at hnx
  have hN₁ : heapNext t₁ = heapNext v := by
    simp only [heapNext]; rw [f₁ _ (by addr_omega [hb, hnx])]
  have m16 := b8000f7e0_m_x2_16 h₁
  have m8 := b8000f7e0_m_x2_8 h₁
  rw [B.x2] at m16 m8
  rv_eval [] at m16 m8
  have x9₁ : t₁.getReg .x9 = s.getMem (s.getReg .x15 + 64) := by
    rw [b8000f7e0_x9 h₁, B.x2]; rv_eval [K.claim, c64]
  have kf (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1704 ∨
        (s.getReg .x2).toNat - 1688 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₁.getMem y = v.getMem y := f₁ y (by addr_omega [h1, h2, hb])
  have F9₁ : DFrame v t₁ (W9 s v t₁) := (DFrame.of_memFrame f₁).mono fun a h ↦
    Or.inl (by addr_omega [h, hb])
  have Fb₁ : DFrame v t₁ (BodyW s v t₁) := (DFrame.of_memFrame f₁).mono fun a h ↦
    slots_body hpre (by addr_omega [hb]) (by addr_omega [hb]) h
  have lv1 := J.lvL
  have X₁ : Fx s t₁ ip c point scale lv lp t (v.getReg .x24) (v.getReg .x19) := {
    k8 := K.keep hpre B.heap B₁.heap (le_of_eq hN₁.symm) F9₁
    m8 := by rw [m8, lv1]
    m16 := by rw [m16, lv1]
    t2 := by rw [kf _ (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩), J.t2]
    tl := J.tl
    tB := newBuf_mono J.tB (le_of_eq hN₁.symm)
    tE := by rw [w9_eList hpre B.heap F9₁ J.tB (le_refl _)]; exact J.tE
    ezB := by
      rw [kf (s.getReg .x2 - 1632) (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        kf (s.getReg .x2 - 1640) (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)]
      exact newBuf_mono J.ezB (le_of_eq hN₁.symm)
    ezE := by
      rw [kf (s.getReg .x2 - 1632) (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        kf (s.getReg .x2 - 1640) (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        w9_eList hpre B.heap F9₁ J.ezB (le_refl _)]
      exact J.ezE
    elB := by
      rw [kf (s.getReg .x2 - 1600) (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        kf (s.getReg .x2 - 1624) (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)]
      exact newBuf_mono J.elB (le_of_eq hN₁.symm)
    elE := by
      rw [kf (s.getReg .x2 - 1600) (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        kf (s.getReg .x2 - 1624) (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        w9_eList hpre B.heap F9₁ J.elB (le_refl _)]
      exact J.elE }
  have R₁ : Rest s t₁ (rest10 s c point scale lv lp t) := J.rest.body hpre B B₁ Fb₁
  have e1600 : t₁.getMem (s.getReg .x2 - 1600) = v.getMem (s.getReg .x2 - 1600) :=
    kf _ (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)
  have e1624 : t₁.getMem (s.getReg .x2 - 1624) = v.getMem (s.getReg .x2 - 1624) :=
    kf _ (by addr_omega [hb]) (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)
  have x18₁ : t₁.getReg .x18 = t₁.getMem (s.getReg .x2 - 1624) := by
    rw [k₁ .x18 (by decide), J.x18, e1624]
  have x27₁ : t₁.getReg .x27 = v.getReg .x19 := b8000f7e0_x27 h₁
  have x24₁ : t₁.getReg .x24 = v.getReg .x24 := k₁ .x24 (by decide)
  have x8₁ : t₁.getReg .x8 = (limbs lv).1 := by rw [k₁ .x8 (by decide), lv1]
  -- the second check with no lane: `at_local = 0`
  have zero (u : MachineState) (hr : Reaches Image.code v u) (hpc : u.pc = 0x8000fa34)
      (hm : ∀ a, u.getMem a = t₁.getMem a) (hx2 : u.getReg .x2 = s.getReg .x2 - 1712)
      (hregs : ∀ r ∈ [Reg.x8, .x24, .x26, .x27], u.getReg r = t₁.getReg r)
      (hx22 : u.getReg .x22 = s.getReg .x11)
      (hacc : (u.getReg .x18, u.getReg .x20, u.getReg .x21) = (0, 0, 0)) (hm0 : mOf s lp = 0) :
      ∃ u, Reaches Image.code v u ∧
        (L10 s u ip c point scale lv lp t (v.getReg .x24) (v.getReg .x19) 0 ∨
          K10 s u ip c point scale lv lp t (v.getReg .x24) (v.getReg .x19) ∨ Dead Image.code u) := by
    have Bu : Base s u := B₁.same hx2 hm
    have hNu : heapNext u = heapNext t₁ := by simp only [heapNext, hm]
    refine ⟨u, hr, Or.inr (Or.inl {
      pc := hpc
      base := Bu
      fx := X₁.keep hpre B₁.heap Bu.heap (le_of_eq hNu.symm) (DFrame.of_same hm _)
      x8 := by rw [hregs .x8 (by decide), x8₁]
      x22 := hx22
      x26 := by rw [hregs .x26 (by decide), k₁ .x26 (by decide), J.x26]
      x27 := by rw [hregs .x27 (by decide), x27₁]
      x24 := by rw [hregs .x24 (by decide), x24₁]
      acc := by rw [hacc, atLocal_wOf, hm0, sumE_range_zero, limbs_zero]
      rest := R₁.keep fun T hT ↦ transcriptAt_congr hm hT })⟩
  by_cases hn0 : s.getMem (s.getReg .x15 + 64) = 0
  · -- no weight: `0x8000fa24`, `0x8000fa2c`
    have pc₁ : t₁.pc = 0x8000fa24 :=
      b8000f7e0_pc_taken h₁ (by rw [B.x2]; rv_eval [K.claim, c64, hn0])
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000fa24_spec pc₁ trivial
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000fa2c_spec (b8000fa24_pc h₂) trivial
    have k₂ := b8000fa24_keeps h₂
    have k₃ := b8000fa2c_keeps h₃
    refine zero t₃ (hr₁.trans (hr₂.trans hr₃)) (b8000fa2c_pc h₃)
      (fun a ↦ by rw [b8000fa2c_mem_same h₃, b8000fa24_mem_same h₂])
      (by rw [k₃ .x2 (by decide), k₂ .x2 (by decide), x2₁]) (fun r hr ↦ ?_)
      (by rw [k₃ .x22 (by decide), b8000fa24_x22 h₂, k₁ .x20 (by decide), J.x20])
      (by rw [k₃ .x18 (by decide), b8000fa24_x18 h₂, b8000fa2c_x20 h₃, b8000fa2c_x21 h₃])
      (by simp only [mOf]; rw [hwl, hn0]; simp)
    rw [k₃ r (reg_sub (by decide) hr), k₂ r (reg_sub (by decide) hr)]
  have hn : 0 < (s.getMem (s.getReg .x15 + 64)).toNat := by
    have : (s.getMem (s.getReg .x15 + 64)).toNat ≠ 0 := fun h ↦ hn0 (BitVec.eq_of_toNat_eq h)
    omega
  have pc₁ : t₁.pc = 0x8000f7f8 :=
    b8000f7e0_pc_not_taken h₁ (by rw [B.x2]; rv_eval [K.claim, c64]; exact hn0)
  -- `0x8000f7f8`: the number of lanes
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f7f8_spec pc₁ trivial
  have k₂ := b8000f7f8_keeps h₂
  have hm₂ := b8000f7f8_mem_same h₂
  have x23₂ := f7f8_x23 h₂
  have pc₂ := f7f8_pc h₂
  rw [x9₁] at x23₂ pc₂
  rw [x18₁] at pc₂
  have hceil : ((s.getMem (s.getReg .x15 + 64)).toNat + 63) / 64 < 2 ^ 64 := by
    have := (s.getMem (s.getReg .x15 + 64)).isLt; omega
  -- `0x8000f810` with `x23` the number of lanes
  have at810 (u : MachineState) (hr : Reaches Image.code v u) (hpc : u.pc = 0x8000f810)
      (hm : ∀ a, u.getMem a = t₁.getMem a)
      (hregs : ∀ r ∈ [Reg.x2, .x8, .x9, .x18, .x20, .x24, .x25, .x26, .x27], u.getReg r = t₁.getReg r)
      (hx23 : u.getReg .x23 = BitVec.ofNat 64 (mOf s lp)) :
      ∃ u, Reaches Image.code v u ∧
        (L10 s u ip c point scale lv lp t (v.getReg .x24) (v.getReg .x19) 0 ∨
          K10 s u ip c point scale lv lp t (v.getReg .x24) (v.getReg .x19) ∨
          Dead Image.code u) := by
    obtain ⟨u₁, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000f810_spec hpc trivial
    have k₄ := b8000f810_keeps h₄
    have hm₄ := b8000f810_mem_same h₄
    have hm14 (a : Word) : u₁.getMem a = t₁.getMem a := by rw [hm₄, hm]
    have r (q : Reg) (hq : q ∈ [Reg.x2, .x8, .x9, .x18, .x20, .x24, .x25, .x26, .x27]) :
        u₁.getReg q = t₁.getReg q := by
      rw [k₄ q (reg_sub (by decide) hq), hregs q hq]
    have x22₄ : u₁.getReg .x22 = s.getReg .x11 := by
      rw [b8000f810_x22 h₄, hregs .x20 (by decide), k₁ .x20 (by decide), J.x20]
    by_cases hL : t₁.getMem (s.getReg .x2 - 1624) = 0
    · -- no lane
      obtain ⟨u₂, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000fa2c_spec
        (b8000f810_pc_taken h₄ (by rw [hregs .x18 (by decide), x18₁, hL])) trivial
      have k₅ := b8000fa2c_keeps h₅
      refine zero u₂ (hr.trans (hr₄.trans hr₅)) (b8000fa2c_pc h₅)
        (fun a ↦ by rw [b8000fa2c_mem_same h₅, hm14]) (by
          rw [k₅ .x2 (by decide), r .x2 (by decide), x2₁]) (fun q hq ↦ ?_)
        (by rw [k₅ .x22 (by decide), x22₄])
        (by rw [k₅ .x18 (by decide), r .x18 (by decide), x18₁, hL, b8000fa2c_x20 h₅,
          b8000fa2c_x21 h₅])
        (by simp only [mOf]; rw [hel, ← e1624, hL]; simp)
      rw [k₅ q (reg_sub (by decide) hq), r q (reg_sub (by decide) hq)]
    have hL' : 0 < (t₁.getMem (s.getReg .x2 - 1624)).toNat := by
      have : (t₁.getMem (s.getReg .x2 - 1624)).toNat ≠ 0 := fun h ↦ hL (BitVec.eq_of_toNat_eq h)
      omega
    have hm0 : 0 < mOf s lp := by
      simp only [mOf]; rw [hel, ← e1624, hwl]; omega
    -- `0x8000f818`: the loop's registers
    obtain ⟨u₂, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000f818_spec
      (b8000f810_pc_not_taken h₄ (by rw [hregs .x18 (by decide), x18₁]; exact hL)) (by
        rv_eval [r .x2 (by decide), x2₁, hm14, X₁.k8.claim]
        and_intros <;> first
          | valid_access hpre.stack.valid [hb]
          | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
    have k₅ := b8000f818_keeps h₅
    have hm₅ := b8000f818_mem_same h₅
    have hm15 (a : Word) : u₂.getMem a = t₁.getMem a := by rw [hm₅, hm14]
    have Bu : Base s u₂ := B₁.same (by rw [k₅ .x2 (by decide), r .x2 (by decide), x2₁])
      hm15
    have hNu : heapNext u₂ = heapNext t₁ := by simp only [heapNext, hm15]
    have x56 : t₁.getMem (s.getReg .x2 - 1656) = s.getReg .x15 := X₁.k8.claim
    refine ⟨u₂, hr.trans (hr₄.trans hr₅), Or.inl {
      pc := b8000f818_pc h₅
      base := Bu
      fx := X₁.keep hpre B₁.heap Bu.heap (le_of_eq hNu.symm) (DFrame.of_same hm15 _)
      x8 := by rw [k₅ .x8 (by decide), r .x8 (by decide), x8₁]
      x22 := by rw [k₅ .x22 (by decide), x22₄]
      x26 := by
        rw [k₅ .x26 (by decide), r .x26 (by decide), k₁ .x26 (by decide), J.x26]
      x27 := by rw [k₅ .x27 (by decide), r .x27 (by decide), x27₁]
      x24 := by rw [k₅ .x24 (by decide), r .x24 (by decide), x24₁]
      x9 := by
        rw [k₅ .x9 (by decide), r .x9 (by decide), x9₁, hwl, Nat.mul_zero, Nat.sub_zero]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
      x19 := by
        have e56 : t₁.getMem (s.getReg .x15 + 56) = s.getMem (s.getReg .x15 + 56) := by
          rw [f₁ _ (by addr_omega [hc, hcs, hb]), c56]
        rw [b8000f818_x19 h₅, r .x2 (by decide), x2₁, Nat.mul_zero]
        rv_eval [hm14, x56, e56]
      x25 := by
        rw [k₅ .x25 (by decide), r .x25 (by decide), k₁ .x25 (by decide), J.x25, hm15, e1600,
          Nat.mul_zero]
        rv_eval []
      x23 := by rw [k₅ .x23 (by decide), b8000f810_keeps h₄ .x23 (by decide), hx23, Nat.sub_zero]
      lt := hm0
      acc := by
        rw [b8000f818_x18 h₅, b8000f818_x20 h₅, b8000f818_x21 h₅, sumE_range_zero, limbs_zero]
      rest := R₁.keep fun T hT ↦ transcriptAt_congr hm15 hT }⟩
  by_cases hlt : ((s.getMem (s.getReg .x15 + 64)).toNat + 63) / 64 <
      (t₁.getMem (s.getReg .x2 - 1624)).toNat
  · refine at810 t₂ (hr₁.trans hr₂) ?_ hm₂ (fun r hr ↦ k₂ r (reg_sub (by decide) hr)) ?_
    · rw [pc₂]
      have : (BitVec.ofNat 64 (((s.getMem (s.getReg .x15 + 64)).toNat + 63) / 64)).ult
          (t₁.getMem (s.getReg .x2 - 1624)) = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hceil, decide_eq_true_eq]
        exact hlt
      rw [this]; rfl
    · rw [x23₂]; congr 1; simp only [mOf]; rw [hel, ← e1624, hwl]; omega
  · have pc₂' : t₂.pc = 0x8000f80c := by
      rw [pc₂]
      have : (BitVec.ofNat 64 (((s.getMem (s.getReg .x15 + 64)).toNat + 63) / 64)).ult
          (t₁.getMem (s.getReg .x2 - 1624)) = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hceil, decide_eq_false_iff_not]
        exact hlt
      rw [this]; rfl
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f80c_spec pc₂' trivial
    have k₃ := b8000f80c_keeps h₃
    refine at810 t₃ (hr₁.trans (hr₂.trans hr₃)) (b8000f80c_pc h₃)
      (fun a ↦ by rw [b8000f80c_mem_same h₃, hm₂]) (fun r hr ↦ by
        rw [k₃ r (reg_sub (by decide) hr), k₂ r (reg_sub (by decide) hr)]) ?_
    rw [b8000f80c_x23 h₃, k₂ .x18 (by decide), x18₁]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := (t₁.getMem (s.getReg .x2 - 1624)).isLt; simp only [mOf]; omega)]
    simp only [mOf]; rw [hel, ← e1624, hwl]; omega

end Rv64Verifier.Gkr.Layer
