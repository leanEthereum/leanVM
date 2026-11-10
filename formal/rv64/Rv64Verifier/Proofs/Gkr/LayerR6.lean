import Rv64Verifier.Proofs.Gkr.LayerWeights

/-!
# `keccak::verify_layer`: the instance weights' loop

`keccak.rs:109-113` at `0x8000f420..0x8000f4f8`: a `Vec` of sixteen `E` allocated and reserved at
`f + 264`, then per mask `RMFE_EMBED[e]` the powers at its bits summed in `x16`, `x14`, `x15`
(`bit_loop`) and pushed (`weight_loop`), the length kept in `x26`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The weight of the mask `m`'s first `b` bits. -/
def iwIn (c : E) (m : BitVec 32) (b : Nat) : E :=
  sumE (((List.range b).filter fun b ↦ bit32 m b).map fun b ↦ c ^ b)

theorem iwIn_succ (c : E) (m : BitVec 32) (b : Nat) :
    iwIn c m (b + 1) = iwIn c m b + if bit32 m b then c ^ b else 0 :=
  sumE_filter_succ _ _ _

theorem iwIn_zero (c : E) (m : BitVec 32) : iwIn c m 0 = 0 := rfl

theorem rmfe_length : rmfeEmbedRust.length = 16 := by
  simp only [rmfeEmbedRust, List.length_cons, List.length_nil]

theorem instanceWeights_getD (c : E) {e : Nat} (he : e < 16) :
    (instanceWeightsRust c).getD e 0 = iwIn c (rmfeEmbedRust.getD e 0) 24 := by
  have hl : e < rmfeEmbedRust.length := by rw [rmfe_length]; exact he
  unfold instanceWeightsRust
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
    Option.getD_some, List.getD_eq_getElem _ _ hl]
  unfold iwIn
  rw [show embedBits = 24 from rfl]
  refine congrArg sumE (List.map_congr_left fun b hb ↦ ?_)
  rw [List.mem_filter, List.mem_range] at hb
  exact powersRust_getD c hb.1

theorem instanceWeights_length (c : E) : (instanceWeightsRust c).length = 16 := by
  unfold instanceWeightsRust
  rw [List.length_map, rmfe_length]

theorem addw_ofNat {b : Nat} (hb : b < 24) :
    BitVec.signExtend 64 (wordResult .add (BitVec.truncate 32 (BitVec.ofNat 64 b))
      (BitVec.truncate 32 (1 : Word))) = BitVec.ofNat 64 (b + 1) := by
  interval_cases b <;> rfl

/-- In the bit loop at `0x8000f4d0`, from `o` (at `0x8000f4a0`): `b` bits done. -/
structure QB (o u : MachineState) (P : Word) (c : E) (m : BitVec 32) (b : Nat) : Prop where
  regs : ∀ r ∈ [Reg.x1, .x2, .x8, .x9, .x10, .x11, .x12, .x13, .x18, .x19, .x20, .x21, .x22,
    .x23, .x24, .x25, .x26, .x27], u.getReg r = o.getReg r
  mem : ∀ a, u.getMem a = o.getMem a
  x5 : u.getReg .x5 = BitVec.signExtend 64 m
  x6 : u.getReg .x6 = P + BitVec.ofNat 64 (24 * b) + 16
  x17 : u.getReg .x17 = BitVec.ofNat 64 b
  acc : (u.getReg .x16, u.getReg .x14, u.getReg .x15) = limbs (iwIn c m b)

set_option maxHeartbeats 2000000 in
theorem bit_step {o u : MachineState} {P : Word} {c : E} {m : BitVec 32} {b : Nat}
    (I : QB o u P c m b) (hpc : u.pc = 0x8000f4d0) (hb : b < 24) (h13 : o.getReg .x13 = 24)
    (pw : ∀ i < 24, eAt o (P + BitVec.ofNat 64 (24 * i)) = c ^ i)
    (hv : ∀ i < 24, Region (P + BitVec.ofNat 64 (24 * i)) 24) :
    ∃ v, Reaches Image.code u v ∧ QB o v P c m (b + 1) ∧
      ((b + 1 < 24 ∧ v.pc = 0x8000f4d0) ∨ (b + 1 = 24 ∧ v.pc = 0x8000f478)) := by
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f4d0_spec hpc trivial
  have k₁ := b8000f4d0_keeps h₁
  have hm₁ := b8000f4d0_mem_same h₁
  have tail (t : MachineState) (ht : t.pc = 0x8000f4c4)
      (kt : ∀ r ∈ [Reg.x1, .x2, .x5, .x6, .x8, .x9, .x10, .x11, .x12, .x13, .x17, .x18, .x19,
        .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], t.getReg r = u.getReg r)
      (mt : ∀ a, t.getMem a = u.getMem a)
      (at' : (t.getReg .x16, t.getReg .x14, t.getReg .x15) = limbs (iwIn c m (b + 1))) :
      ∃ v, Reaches Image.code t v ∧ QB o v P c m (b + 1) ∧
        ((b + 1 < 24 ∧ v.pc = 0x8000f4d0) ∨ (b + 1 = 24 ∧ v.pc = 0x8000f478)) := by
    obtain ⟨v, hr, h⟩ := Sym.BlockSpec.reaches b8000f4c4_spec ht trivial
    have k := b8000f4c4_keeps h
    have x17t : t.getReg .x17 = BitVec.ofNat 64 b := (kt .x17 (by decide)).trans I.x17
    have x13t : t.getReg .x13 = 24 :=
      ((kt .x13 (by decide)).trans (I.regs .x13 (by decide))).trans h13
    have x17v : v.getReg .x17 = BitVec.ofNat 64 (b + 1) :=
      h.reg_eq .x17 rfl (by rv_eval [x17t]; exact addw_ofNat hb)
    refine ⟨v, hr, {
      regs := fun r hr ↦ by rw [k r (mem_of_mem hr _), kt r (mem_of_mem hr _), I.regs r hr]
      mem := fun a ↦ by rw [b8000f4c4_mem_same h, mt, I.mem]
      x5 := by rw [k .x5 (by decide), kt .x5 (by decide), I.x5]
      x6 := by rw [b8000f4c4_x6 h, kt .x6 (by decide), I.x6]; exact ofNat_step' _ 24 b 16
      x17 := x17v
      acc := by rw [k .x16 (by decide), k .x14 (by decide), k .x15 (by decide), at'] }, ?_⟩
    by_cases hl : b + 1 < 24
    · refine Or.inl ⟨hl, h.pc_eq ?_⟩
      rv_eval [x17t, x13t]
      rw [addw_ofNat hb]
      have hne : BitVec.ofNat 64 (b + 1) ≠ 24 := by
        intro he
        have := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat] at this
        change (b + 1) % 2 ^ 64 = 24 at this
        omega
      simp only [hne, beq_iff_eq, ↓reduceIte]
    · refine Or.inr ⟨by omega, h.pc_eq ?_⟩
      rv_eval [x17t, x13t]
      rw [addw_ofNat hb, show b + 1 = 24 by omega]
      rfl
  cases hbit : bit32 m b
  · have pc₁ : u₁.pc = 0x8000f4c4 := h₁.pc_eq (by
      rv_eval [I.x5, I.x17, (srlw_bit m (b := b) (by omega)).mpr hbit]
      decide)
    obtain ⟨v, hr, Q, hc⟩ := tail u₁ pc₁ (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁ (by
      rw [k₁ .x16 (by decide), k₁ .x14 (by decide), k₁ .x15 (by decide), I.acc, iwIn_succ, hbit]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero])
    exact ⟨v, hr₁.trans hr, Q, hc⟩
  · have hnz : (BitVec.signExtend 64 (wordResult .srl (BitVec.truncate 32 (BitVec.signExtend 64 m))
        (BitVec.truncate 32 (BitVec.ofNat 64 b))) &&& 1) ≠ 0 := fun h ↦ by
      rw [(srlw_bit m (by omega)).mp h] at hbit; cases hbit
    have pc₁ : u₁.pc = 0x8000f4dc := h₁.pc_eq (by
      rv_eval [I.x5, I.x17]
      exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hnz (beq_iff_eq.mp h)))
    have x6₁ : u₁.getReg .x6 = P + BitVec.ofNat 64 (24 * b) + 16 := (k₁ .x6 (by decide)).trans I.x6
    have hR := hv b hb
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f4dc_spec pc₁ (by
      rv_eval [x6₁]
      and_intros <;> (refine Region.valid hR ?_ ?_ ?_ <;> addr_omega [hR]))
    have k₂ := b8000f4dc_keeps h₂
    have e := pw b hb
    have m₁ (a : Word) : u₁.getMem a = o.getMem a := by rw [hm₁, I.mem]
    obtain ⟨v, hr, Q, hc⟩ := tail u₂ (b8000f4dc_pc h₂)
      (fun r hr ↦ by rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)])
      (fun a ↦ by rw [b8000f4dc_mem_same h₂, hm₁]) (by
        rw [b8000f4dc_x16 h₂, b8000f4dc_x14 h₂, b8000f4dc_x15 h₂, x6₁, iwIn_succ, hbit]
        simp only [↓reduceIte]
        rw [limbs_add, ← I.acc, ← e, limbs_eAt]
        rv_eval [m₁, k₁ .x16 (by decide), k₁ .x14 (by decide), k₁ .x15 (by decide),
          BitVec.xor_comm])
    exact ⟨v, hr₁.trans (hr₂.trans hr), Q, hc⟩

theorem bit_loop {o : MachineState} {P : Word} {c : E} {m : BitVec 32} (h13 : o.getReg .x13 = 24)
    (pw : ∀ i < 24, eAt o (P + BitVec.ofNat 64 (24 * i)) = c ^ i)
    (hv : ∀ i < 24, Region (P + BitVec.ofNat 64 (24 * i)) 24) :
    ∀ n b u, b + n = 24 → 0 < n → QB o u P c m b → u.pc = 0x8000f4d0 →
      ∃ v, Reaches Image.code u v ∧ QB o v P c m 24 ∧ v.pc = 0x8000f478
  | 0, _, _, _, h0, _, _ => absurd h0 (Nat.lt_irrefl 0)
  | n + 1, b, u, hn, _, I, hpc => by
    obtain ⟨v, hr, Q, ⟨hl, hpc'⟩ | ⟨he, hpc'⟩⟩ := bit_step I hpc (by omega) h13 pw hv
    · obtain ⟨t, hr', ht⟩ := bit_loop h13 pw hv n (b + 1) v (by omega) (by omega) Q hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · rw [he] at Q
      exact ⟨v, hr, Q, hpc'⟩

/-! ## The masks -/

/-- What the mask loop reads, from its entry `w₀`. -/
structure W0 (s w₀ : MachineState) (ip : Word) (c : E) : Prop where
  x2 : w₀.getReg .x2 = s.getReg .x2 - 1712
  x8 : w₀.getReg .x8 = 16
  x9 : w₀.getReg .x9 = ip
  x11 : w₀.getReg .x11 = s.getReg .x2 - 736
  x12 : w₀.getReg .x12 = 0xa0000ea8
  x13 : w₀.getReg .x13 = 24
  ro : RodataOk w₀
  pow : ∀ i < 24, eAt w₀ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) = c ^ i
  buf : heapStart ≤ ip.toNat ∧ ip.toNat + 384 ≤ heapEnd ∧ ip.toNat % 8 = 0

/-- The mask loop at its head `0x8000f4a0`: `e` weights pushed. -/
structure QE (w₀ w : MachineState) (ip : Word) (c : E) (e : Nat) : Prop where
  regs : ∀ r ∈ [Reg.x2, .x8, .x9, .x11, .x12, .x13, .x18, .x19, .x20, .x21],
    w.getReg r = w₀.getReg r
  x10 : w.getReg .x10 = BitVec.ofNat 64 e
  x26 : w.getReg .x26 = BitVec.ofNat 64 e
  elems : ∀ j < e, eAt w (ip + BitVec.ofNat 64 (24 * j)) = (instanceWeightsRust c).getD j 0
  lt : e < 16
  frame : DFrame w₀ w (Within · ip 384)

/-- The masks done, at `0x8000f4f8`. -/
structure MX (w₀ w : MachineState) (ip : Word) (c : E) : Prop where
  regs : ∀ r ∈ [Reg.x2, .x9, .x18, .x19, .x20, .x21], w.getReg r = w₀.getReg r
  x26 : w.getReg .x26 = 16
  elems : eListAt w ip 16 = instanceWeightsRust c
  frame : DFrame w₀ w (Within · ip 384)

theorem mul24 (e : Nat) :
    BitVec.ofNat 64 e * 16 + BitVec.ofNat 64 e * 8 = BitVec.ofNat 64 (24 * e) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

set_option maxHeartbeats 4000000 in
theorem weight_step {s w₀ w : MachineState} {ip : Word} {c : E} {e : Nat}
    (hpre : VerifyLayerPre s) (W : W0 s w₀ ip c) (Q : QE w₀ w ip c e) (hpc : w.pc = 0x8000f4a0) :
    ∃ v, Reaches Image.code w v ∧ ((QE w₀ v ip c (e + 1) ∧ v.pc = 0x8000f4a0) ∨
      (MX w₀ v ip c ∧ v.pc = 0x8000f4f8)) := by
  have hb := bounds hpre
  unfold verifyLayerStack at hb
  have he := Q.lt
  have hip := W.buf
  have x10w := Q.x10
  have x12w : w.getReg .x12 = 0xa0000ea8 := (Q.regs .x12 (by decide)).trans W.x12
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches f4a0A_spec hpc (by
    simp only [f4a0A, maskE]
    rv_eval [x10w, x12w]
    interval_cases e <;> decide)
  have k₁ := h₁.keeps (rs := [.x1, .x2, .x8, .x9, .x10, .x11, .x12, .x13, .x18, .x19, .x20, .x21,
    .x22, .x23, .x24, .x25, .x26, .x27]) (by decide)
  have hm₁ : ∀ a, u₁.getMem a = w.getMem a := h₁.mem_same rfl
  have hrow : RodataOk w := W.ro.dframe Q.frame fun a ha hw ↦ by addr_omega [ha, hw, hip]
  have x5₁ : u₁.getReg .x5 = BitVec.signExtend 64 (rmfeEmbedRust.getD e 0) := by
    rw [f4a0A_x5 h₁, x10w, x12w]; exact mask_word hrow (by omega)
  have pw (i : Nat) (hi : i < 24) :
      eAt u₁ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) = c ^ i := by
    rw [← W.pow i hi, ← Q.frame.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb, hip, hi]]
    unfold Rv64Verifier.eAt; rw [hm₁, hm₁, hm₁]
  have hv (i : Nat) (hi : i < 24) : Region (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) 24 := by
    addr_omega [hb, hi]
  have I₀ : QB u₁ u₁ (s.getReg .x2 - 752) c (rmfeEmbedRust.getD e 0) 0 := {
    regs := fun _ _ ↦ rfl
    mem := fun _ ↦ rfl
    x5 := x5₁
    x6 := by
      rw [h₁.reg_eq .x6 (v := w.getReg .x11) rfl (by rv_eval []), (Q.regs .x11 (by decide)).trans W.x11,
        Nat.mul_zero, add_ofNat_zero]
      rv_eval []
    x17 := h₁.reg_eq .x17 (v := 0) rfl (by rv_eval [])
    acc := by
      rw [h₁.reg_eq .x16 (v := 0) rfl (by rv_eval []), h₁.reg_eq .x14 (v := 0) rfl (by rv_eval []),
        h₁.reg_eq .x15 (v := 0) rfl (by rv_eval []), iwIn_zero, limbs_zero] }
  have x13₁ : u₁.getReg .x13 = 24 := by
    rw [k₁ .x13 (by decide), Q.regs .x13 (by decide), W.x13]
  obtain ⟨u₂, hr₂, I, hpc₂⟩ := bit_loop x13₁ pw hv 24 0 u₁ (by decide) (by decide) I₀
    (h₁.pc_eq (by rv_eval []))
  have x9₂ : u₂.getReg .x9 = ip := by
    rw [I.regs .x9 (by decide), k₁ .x9 (by decide), Q.regs .x9 (by decide), W.x9]
  have x26₂ : u₂.getReg .x26 = BitVec.ofNat 64 e := by
    rw [I.regs .x26 (by decide), k₁ .x26 (by decide), Q.x26]
  have x10₂ : u₂.getReg .x10 = BitVec.ofNat 64 e := by
    rw [I.regs .x10 (by decide), k₁ .x10 (by decide), Q.x10]
  have x8₂ : u₂.getReg .x8 = 16 := by
    rw [I.regs .x8 (by decide), k₁ .x8 (by decide), Q.regs .x8 (by decide), W.x8]
  have hvb : ValidMemRange (ip + BitVec.ofNat 64 (24 * e)) 3 :=
    heap_vmr (by addr_omega [hip, he]) (by addr_omega [hip, he]) (by addr_omega [hip, he])
  obtain ⟨v, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f478_spec hpc₂ (by
    rv_eval [x9₂, x26₂, mul24]
    and_intros <;> valid_access hvb [hip, he])
  have k₃ := b8000f478_keeps h₃
  have f₃ : MemFrame u₂ v (ip + BitVec.ofNat 64 (24 * e)) 24 :=
    h₃.memFrame (by rv_eval [x9₂, x26₂, mul24]; and_intros <;> addr_omega [hip, he])
  have m0 := b8000f478_m0 h₃
  have m1 := b8000f478_m1 h₃
  have m2 := b8000f478_m2 h₃
  rw [x9₂, x26₂, mul24] at m0 m1 m2
  have hm₂ (a : Word) : u₂.getMem a = w.getMem a := by rw [I.mem, hm₁]
  have enew : eAt v (ip + BitVec.ofNat 64 (24 * e)) = (instanceWeightsRust c).getD e 0 := by
    rw [instanceWeights_getD c he]
    apply eAt_eq_of_limbs
    rw [m0, m1, m2, ← I.acc]
  have Fv : DFrame w₀ v (Within · ip 384) :=
    (Q.frame.trans (DFrame.of_same hm₂ _) fun _ h ↦ h).trans (DFrame.of_memFrame f₃) fun a h ↦ by
      addr_omega [h, hip, he]
  have regs₃ (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x9, .x11, .x12, .x13, .x18, .x19, .x20, .x21]) :
      v.getReg r = w₀.getReg r := by
    rw [k₃ r (mem_of_mem hr _), I.regs r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), Q.regs r hr]
  have elems₃ (j : Nat) (hj : j < e + 1) :
      eAt v (ip + BitVec.ofNat 64 (24 * j)) = (instanceWeightsRust c).getD j 0 := by
    by_cases hje : j = e
    · subst hje; exact enew
    · rw [f₃.eAt (by addr_omega [hip, he, hj, hje]) (by addr_omega [hip, he, hj]), ← Q.elems j (by omega)]
      unfold Rv64Verifier.eAt; rw [hm₂, hm₂, hm₂]
  have x10₃ : v.getReg .x10 = BitVec.ofNat 64 (e + 1) := by
    rw [b8000f478_x10 h₃, x10₂, ofNat_succ]
  have x26₃ : v.getReg .x26 = BitVec.ofNat 64 (e + 1) := by
    rw [b8000f478_x26 h₃, x26₂, ofNat_succ]
  by_cases hl : e + 1 < 16
  · refine ⟨v, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨{
      regs := regs₃
      x10 := x10₃
      x26 := x26₃
      elems := elems₃
      lt := hl
      frame := Fv }, b8000f478_pc_not_taken h₃ ?_⟩⟩
    rw [x10₂, x8₂, ofNat_succ]
    intro h16
    have := congrArg BitVec.toNat h16
    rw [BitVec.toNat_ofNat] at this
    change (e + 1) % 2 ^ 64 = 16 at this
    omega
  · have e15 : e = 15 := by omega
    subst e15
    refine ⟨v, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨{
      regs := fun r hr ↦ regs₃ r (mem_of_mem hr _)
      x26 := x26₃
      elems := by
        rw [← instanceWeights_length c]
        unfold Rv64Verifier.eListAt
        apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [elems₃ j (by simp only [List.length_map, List.length_range, instanceWeights_length] at h1; omega),
          List.getD_eq_getElem _ _ h2]
      frame := Fv }, b8000f478_pc_taken h₃ (by rw [x10₂, x8₂]; rfl)⟩⟩

theorem weight_loop {s w₀ : MachineState} {ip : Word} {c : E} (hpre : VerifyLayerPre s)
    (W : W0 s w₀ ip c) : ∀ n e w, e + n = 16 → QE w₀ w ip c e → w.pc = 0x8000f4a0 →
      ∃ v, Reaches Image.code w v ∧ MX w₀ v ip c ∧ v.pc = 0x8000f4f8
  | 0, _, _, hn, Q, _ => absurd Q.lt (by omega)
  | n + 1, e, w, hn, Q, hpc => by
    obtain ⟨v, hr, ⟨Q', hpc'⟩ | ⟨X, hpc'⟩⟩ := weight_step hpre W Q hpc
    · obtain ⟨t, hr', ht⟩ := weight_loop hpre W n (e + 1) v (by omega) Q' hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · exact ⟨v, hr, X, hpc'⟩

/-! ## The `Vec` -/

/-- What the stretch writes: the `Vec` at `f + 264`, the callees' stack, `NEXT`, what it
allocates. -/
@[rv_addr] def RW (s u v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1448) 24 ∨ Within a (s.getReg .x2 - 1872) 160 ∨ Within a nextAddr 8 ∨
    Fresh u v a

/-- The instance weights pushed, at `0x8000f4f8`. -/
structure J6 (s u : MachineState) (pp ip : Word) (product : List E) (c : E) : Prop where
  pc : u.pc = 0x8000f4f8
  base : Base s u
  plenM : u.getMem (s.getReg .x2 - 1672) = 47
  out : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  claim : u.getMem (s.getReg .x2 - 1656) = s.getReg .x15
  sponge : u.getMem (s.getReg .x2 - 1616) = s.getReg .x11 + 8
  p : u.getMem (s.getReg .x2 - 1608) = s.getReg .x11
  ppM : u.getMem (s.getReg .x2 - 1600) = pp
  x9 : u.getReg .x9 = ip
  x18 : u.getReg .x18 = 47
  x19 : u.getReg .x19 = s.getReg .x15
  x20 : u.getReg .x20 = s.getReg .x11
  x21 : u.getReg .x21 = pp
  x26 : u.getReg .x26 = 16
  sc : eAt u (s.getReg .x2 - 824) = c
  plen : product.length = 47
  prod : eListAt u pp 47 = product
  iw : eListAt u ip 16 = instanceWeightsRust c
  pbuf : heapNext s ≤ pp.toNat ∧ pp.toNat + 24 * 47 ≤ ip.toNat
  palign : pp.toNat % 8 = 0
  ibuf : ip.toNat % 8 = 0 ∧ 16 ≤ (u.getMem (s.getReg .x2 - 1448)).toNat ∧
    ip.toNat + 24 * (u.getMem (s.getReg .x2 - 1448)).toNat ≤ heapNext u
  rest : Rest s u (packRest (claimAt s (lClaim s)) (instanceWeightsRust c)
    (sumE (instanceWeightsRust c)) 0 (polyEvalRust product c, 1, []))

set_option maxHeartbeats 16000000 in
theorem weights (hA : AllocSpec) (hR : ReserveFreshSpec 0x80008a10 24 8) {s u : MachineState}
    {pp : Word} {product : List E} {c : E} (hpre : VerifyLayerPre s) (J : J5 s u pp product c) :
    ∃ v ip, Reaches Image.code u v ∧ (J6 s v pp ip product c ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := J.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  simp only [stackLo] at hnx hab hrs
  unfold verifyLayerStack at hb hnx hab hrs
  have hpb := J.pbuf
  have hHu := B.heap.hi
  -- `0x8000f420`: `alloc(8, 384)`
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000f420_spec J.pc trivial
  have k₀ := b8000f420_keeps h₀
  have hm₀ := b8000f420_mem_same h₀
  have x2₀ : t₀.getReg .x2 = s.getReg .x2 - 1712 := (k₀ .x2 (by decide)).trans B.x2
  have B₀ : Base s t₀ := B.same x2₀ hm₀
  have hN₀ : heapNext t₀ = heapNext u := by simp only [heapNext, hm₀]
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, A⟩ | hd⟩ := hA.call hr₀ (b8000f420_pc h₀)
    ⟨B₀.heap, by rw [b8000f420_x10 h₀]; decide⟩
  swap
  · exact ⟨_, 0, hr₁, Or.inr hd⟩
  have hal := A.aligned
  have hab₁ := A.above
  have hnx₁ := A.next
  rw [b8000f420_x10 h₀] at hal
  rw [b8000f420_x11 h₀] at hnx₁
  simp only [show (8 : Word).toNat = 8 from rfl] at hal
  simp only [show (384 : Word).toNat = 384 from rfl] at hnx₁
  have hH₀ := B₀.heap.lo
  have F₁ : DFrame t₀ t₁ (Within · nextAddr 8) := fun a ha ↦ A.mem a fun h ↦
    ha 0 (by decide) (by rw [h, add_ofNat_zero]; addr_omega [])
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (hp₁.reg .x2).trans x2₀
  have B₁ : Base s t₁ := B₀.next hpre x2₁ A.heap (by omega) F₁ fun a h ↦
    ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), by addr_omega [h, hb, hnx]⟩
  -- `0x8000f430`: the null check
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f430_spec
    (by rw [hpc₁, returnAddress_eq, b8000f420_x1 h₀]; decide) trivial
  have k₂ := b8000f430_keeps h₂
  have hm₂ := b8000f430_mem_same h₂
  have hne : t₁.getReg .x10 ≠ 0 := fun h ↦ by
    rw [h, show (0 : Word).toNat = 0 from rfl] at hab₁
    simp only [heapStart] at hH₀
    omega
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have B₂ : Base s t₂ := B₁.same x2₂ hm₂
  -- `0x8000f434`: the `Vec` `{16, ptr, 0}` at `f + 264`, `reserve(16)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f434_spec
    (b8000f430_pc_not_taken h₂ hne) (by
      rv_eval [x2₂]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000f434_keeps h₃
  have f₃ := b8000f434_frame h₃ (by rw [x2₂]; addr_omega [hb])
  rw [x2₂] at f₃
  rv_eval [] at f₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.slots hpre x2₃ f₃ (by addr_omega [hb]) (by addr_omega [hb])
  have n264 := b8000f434_m_x2_264 h₃
  have n272 := b8000f434_m_x2_272 h₃
  have n280 := b8000f434_m_x2_280 h₃
  rw [x2₂] at n264 n272 n280
  rw [k₂ .x10 (by decide)] at n272
  rv_eval [] at n264 n272 n280
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000f434_x10 h₃, x2₂]; rv_eval []
  have x11₃ : t₃.getReg .x11 = 16 := b8000f434_x11 h₃
  have hN₃ : heapNext t₃ = heapNext t₁ := by
    simp only [heapNext]
    rw [f₃ _ (by addr_omega [hb, hnx]), hm₂]
  have pre : ReservePre 24 8 t₃ := {
    heap := B₃.heap
    self := by rw [x10₃]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    vec := {
      raw := by
        simp only [RawVecOk, Buf, vecPtr, vecCap, x10₃]
        rv_eval [n264, n272]
        rw [hN₃, hnx₁]
        simp only [heapStart] at hH₀ ⊢
        omega
      len := by simp only [vecLen, vecCap, x10₃]; rv_eval [n264, n280]; decide }
    stack := hpre.stack.sub 1712 x2₃ (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    selfFree := by rw [x10₃]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    selfStack := by rw [x10₃]; simp only [stackLo, x2₃]; addr_omega [hb] }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, R, Rf⟩ | hd⟩ := hR.call hr₃ (b8000f434_pc h₃) pre
  swap
  · exact ⟨_, 0, hr₁.trans (hr₂.trans hr₄), Or.inr hd⟩
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (hp₄.reg .x2).trans x2₃
  have rcap := R.cap
  have rlen := R.len
  have rraw := R.vec.raw
  have rmono := R.mono
  have rH := R.heap.hi
  simp only [x10₃, x11₃, vecLen, vecCap, vecPtr, RawVecOk, Buf] at rcap rlen rraw Rf
  rv_eval [n264, n272, n280] at rcap rlen rraw Rf
  -- the buffer
  have hip : heapNext u ≤ (t₄.getMem (s.getReg .x2 - 1440)).toNat ∧
      (t₄.getMem (s.getReg .x2 - 1440)).toNat + 384 ≤ heapNext t₄ := by
    rcases Rf with ⟨e1, -⟩ | ⟨-, h0 | ⟨h1, h2⟩⟩
    · rw [e1]; rw [hN₀] at hab₁; omega
    · omega
    · rw [hN₃] at h1; rw [hN₀] at hab₁; omega
  have hcap : 16 ≤ (t₄.getMem (s.getReg .x2 - 1448)).toNat ∧ (t₄.getMem (s.getReg .x2 - 1440)).toNat +
      24 * (t₄.getMem (s.getReg .x2 - 1448)).toNat ≤ heapNext t₄ := by
    rcases Rf with ⟨-, e2⟩ | ⟨-, h0 | ⟨-, h2⟩⟩
    · rw [e2, show (16 : Word).toNat = 16 from rfl]; exact ⟨le_refl _, by have := hip.2; omega⟩
    · omega
    · omega
  obtain ⟨ip, hipd⟩ : ∃ ip, t₄.getMem (s.getReg .x2 - 1440) = ip := ⟨_, rfl⟩
  rw [hipd] at hip rraw hcap
  have hut₃ : heapNext u ≤ heapNext t₃ := by rw [hN₃, hnx₁, ← hN₀]; omega
  have B₄ : Base s t₄ := B₃.next hpre x2₄ R.heap R.mono (DFrame.of_byteFrame R.frame)
    fun a ha ↦ cframe_lw hpre B₃ 1448 (by decide) (by decide) (by decide) R.heap x10₃ a ha
  have F₄ : DFrame u t₄ (RW s u t₄) :=
    ((((DFrame.of_same hm₀ (RW s u t₄)).trans F₁ fun a h ↦ Or.inr (Or.inr (Or.inl h))).trans
      (DFrame.of_same hm₂ _) fun _ h ↦ h).trans (DFrame.of_memFrame f₃) fun a h ↦ Or.inl h).trans
      (DFrame.of_byteFrame R.frame) fun a h ↦ by
        simp only [RW, Fresh, stackLo, x10₃, x2₃] at h ⊢
        rcases h with h | h | h | h
        · exact Or.inl (by addr_omega [h])
        · exact Or.inr (Or.inl (by addr_omega [h, hb]))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))
  -- `0x8000f454`: the loop's registers
  obtain ⟨w₀, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000f454_spec
    (by rw [hpc₄, returnAddress_eq, b8000f434_x1 h₃]; decide) (by
      rv_eval [x2₄]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₅ := b8000f454_keeps h₅
  have hm₅ := b8000f454_mem_same h₅
  have x2₅ : w₀.getReg .x2 = s.getReg .x2 - 1712 := (k₅ .x2 (by decide)).trans x2₄
  have B₅ : Base s w₀ := B₄.same x2₅ hm₅
  have keep₄ (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
        (s.getReg .x2).toNat - 1424 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₄.getMem y = u.getMem y := F₄ y fun i hi hw ↦ by
    simp only [RW, Fresh] at hw
    rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, hb, h1, h2, hnx, rH, hab]
  have x9₅ : w₀.getReg .x9 = ip := by rw [b8000f454_x9 h₅, x2₄]; rv_eval [hipd]
  have x26₅ : w₀.getReg .x26 = BitVec.ofNat 64 0 := by rw [b8000f454_x26 h₅, x2₄]; rv_eval [rlen]
  have x18₅ : w₀.getReg .x18 = 47 := by
    rw [b8000f454_x18 h₅, x2₄]; rv_eval []
    rw [keep₄ _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.plenM]
  have W : W0 s w₀ ip c := {
    x2 := x2₅
    x8 := by rw [k₅ .x8 (by decide), hp₄.reg .x8, b8000f434_x8 h₃]
    x9 := x9₅
    x11 := by rw [b8000f454_x11 h₅, x2₄]; rv_eval []
    x12 := b8000f454_x12 h₅
    x13 := b8000f454_x13 h₅
    ro := B₅.rodata hpre
    pow := fun i hi ↦ by
      rw [← J.pow i hi, ← F₄.eAt fun j hj hw ↦ by
        simp only [RW, Fresh] at hw
        rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hj, hi, hb, hnx, rH, hab]]
      unfold Rv64Verifier.eAt; rw [hm₅, hm₅, hm₅]
    buf := ⟨by have := B.heap.lo; omega, by omega, rraw.1⟩ }
  have Q₀ : QE w₀ w₀ ip c 0 := {
    regs := fun _ _ ↦ rfl
    x10 := (b8000f454_x10 h₅).trans rfl
    x26 := x26₅
    elems := fun j hj ↦ absurd hj (Nat.not_lt_zero _)
    lt := by decide
    frame := DFrame.refl _ _ }
  obtain ⟨v, hr₆, X, hpc₆⟩ := weight_loop hpre W 16 0 w₀ (by decide) Q₀ (b8000f454_pc h₅)
  have hNv : heapNext v = heapNext t₄ := by
    simp only [heapNext]
    rw [X.frame _ fun i hi hw ↦ by addr_omega [hw, hi, hip, rH], hm₅]
  have hsu := B.mono
  have Bv : Base s v := B₅.next hpre ((X.regs .x2 (by decide)).trans x2₅)
    ⟨by rw [hNv]; exact R.heap.lo, by rw [hNv]; exact rH⟩ (by rw [hNv, heapNext, heapNext, hm₅])
    X.frame fun a h ↦ ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hip, hsu],
      by rw [hNv]; addr_omega [h, hip]⟩))), by addr_omega [h, hb, hip, rH, hab]⟩
  have Fv : DFrame u v (RW s u v) :=
    ((F₄.mono fun a h ↦ by simp only [RW, Fresh] at h; simp only [RW, Fresh, hNv]; exact h).trans
      (DFrame.of_same hm₅ _) fun _ h ↦ h).trans X.frame fun a h ↦
        Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hip], by rw [hNv]; addr_omega [h, hip]⟩))
  have hvH := Bv.heap.hi
  have keep (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
        (s.getReg .x2).toNat - 1424 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      v.getMem y = u.getMem y := Fv y fun i hi hw ↦ by
    simp only [RW, Fresh] at hw
    rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, hb, h1, h2, hnx, hvH, hab]
  have regs (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21]) : v.getReg r = u.getReg r := by
    rw [X.regs r (mem_of_mem hr _), k₅ r (mem_of_mem hr _), hp₄.reg r (mem_of_mem hr _),
      k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), hp₁.reg r (mem_of_mem hr _),
      k₀ r (mem_of_mem hr _)]
  refine ⟨v, ip, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans hr₆))), Or.inl {
    pc := hpc₆
    base := Bv
    plenM := by rw [keep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.plenM]
    out := by rw [keep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.out]
    claim := by rw [keep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.claim]
    sponge := by rw [keep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.sponge]
    p := by rw [keep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.p]
    ppM := by rw [keep _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), J.ppM]
    x9 := (X.regs .x9 (by decide)).trans x9₅
    x18 := (X.regs .x18 (by decide)).trans x18₅
    x19 := (regs .x19 (by decide)).trans J.x19
    x20 := (regs .x20 (by decide)).trans J.x20
    x21 := (regs .x21 (by decide)).trans J.x21
    x26 := X.x26
    sc := by
      rw [← J.sc]
      exact Fv.eAt fun j hj hw ↦ by
        simp only [RW, Fresh] at hw
        rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hj, hb, hnx, hvH, hab]
    plen := J.plen
    prod := by
      rw [← J.prod]
      exact Fv.eListAt fun j hj hw ↦ by
        simp only [RW, Fresh] at hw
        rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hj, hb, hnx, hvH, hab, hpb, hHu]
    iw := X.elems
    pbuf := ⟨hpb.1, by omega⟩
    palign := J.palign
    ibuf := by
      have e264 : v.getMem (s.getReg .x2 - 1448) = t₄.getMem (s.getReg .x2 - 1448) := by
        rw [X.frame _ fun i hi hw ↦ by addr_omega [hw, hi, hip, rH, hb, hab], hm₅]
      rw [e264, hNv]
      exact ⟨rraw.1, hcap⟩
    rest := Rest.body hpre B Bv (Fv.mono fun a h ↦ by
      simp only [RW, BodyW, Fresh] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl (by unfold verifyLayerStack; addr_omega [h, hb])
      · exact Or.inl (by unfold verifyLayerStack; addr_omega [h, hb])
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) J.rest }⟩

end Rv64Verifier.Gkr.Layer
