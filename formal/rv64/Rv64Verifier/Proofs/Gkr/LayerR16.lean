import Rv64Verifier.Proofs.Gkr.LayerR15

/-!
# `keccak::verify_layer`: `linear_transpose`'s output

`keccak.rs:96-100` at `0x8000ffb8..0x800100e8`: a `Vec` of 1600 `E` allocated and reserved at
`f + 960`, then for each `j`, `x = j / 64 % 5` (a `mulhu` division by five, `s11`) and `z = j % 64`,
`columns[64 ((x + 1) % 5) + z] + (g[j] + columns[64 ((x + 4) % 5) + (z + 1) % 64])` pushed
(`out_loop`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- The `j`-th output from the columns `cv` and `g`. -/
def outV (gv cv : Nat → E) (j : Nat) : E :=
  cv (64 * ((j / 64 % 5 + 1) % 5) + j % 64) + (gv j + cv (64 * ((j / 64 % 5 + 4) % 5) + (j % 64 + 1) % 64))

theorem outV_eq (w : List E) {j : Nat} (hj : j < 1600) :
    outV (gOf w) (colAcc (gOf w) 1600) j = (linearTransposeRust w).getD j 0 := by
  rw [linearTransposeRust_getD w hj, outV, colAcc_full _ (by omega) (by omega),
    colAcc_full _ (by omega) (by omega), thetaT]
  ring

theorem mod5 (L : Nat) :
    BitVec.ofNat 64 L - BitVec.ofNat 64 (L / 5) - BitVec.ofNat 64 (L / 5) * 4 = BitVec.ofNat 64 (L % 5) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl]
  omega

theorem x13_eq {x j : Nat} (hx : x < 5) (hj : j < 1600) :
    ((if (BitVec.ofNat 64 x - 4).ult 1 = true then (1 : Word) else 0) - 1 &&& (BitVec.ofNat 64 x + 1) * 64) |||
      (BitVec.ofNat 64 j &&& 63) = BitVec.ofNat 64 (64 * ((x + 1) % 5) + j % 64) := by
  have e : ((if (BitVec.ofNat 64 x - 4).ult 1 = true then (1 : Word) else 0) - 1 &&&
      (BitVec.ofNat 64 x + 1) * 64) = BitVec.ofNat 64 (64 * ((x + 1) % 5)) := by
    interval_cases x <;> decide
  rw [e, and63 (by omega), BitVec.or_comm, or_low (by omega) (by omega)]

theorem x14_dec {x : Nat} (hx : x < 5) (h0 : x ≠ 0) :
    BitVec.ofNat 64 x * 64 - 64 = BitVec.ofNat 64 (64 * ((x + 4) % 5)) := by
  interval_cases x <;> first | decide | omega

theorem x14_or {x j : Nat} (hj : j < 1600) :
    BitVec.ofNat 64 (64 * ((x + 4) % 5)) ||| (BitVec.ofNat 64 j + 1 &&& 63) =
      BitVec.ofNat 64 (64 * ((x + 4) % 5) + (j % 64 + 1) % 64) := by
  rw [ofNat_succ, and63 (by omega), BitVec.or_comm, or_low (by omega) (by omega),
    show (j + 1) % 64 = (j % 64 + 1) % 64 by omega]

theorem ne_ofNat {a : Word} {j : Nat} (hj : j < 2 ^ 64) (h : j ≠ a.toNat) : a ≠ BitVec.ofNat 64 j :=
  fun e ↦ h (by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj])

/-! ## The output loop -/

/-- What the output loop reads, at its start `w₀`: `g` at `G`, the columns at `C`, the output's
buffer at `O`, in that order. -/
structure OC (w₀ : MachineState) (O C G : Word) (gv cv : Nat → E) : Prop where
  x8 : w₀.getReg .x8 = C
  x22 : w₀.getReg .x22 = 1600
  x24 : w₀.getReg .x24 = 320
  x25 : w₀.getReg .x25 = 1600
  x27 : w₀.getReg .x27 = 0x3333333333333334
  g : ∀ p < 1600, eAt w₀ (G + BitVec.ofNat 64 (24 * p)) = gv p
  c : ∀ q < 320, eAt w₀ (C + BitVec.ofNat 64 (24 * q)) = cv q
  op : O.toNat % 8 = 0 ∧ heapStart ≤ O.toNat ∧ O.toNat + 38400 ≤ heapEnd
  cp : C.toNat % 8 = 0 ∧ heapStart ≤ C.toNat ∧ C.toNat + 7680 ≤ O.toNat
  gp : G.toNat % 8 = 0 ∧ heapStart ≤ G.toNat ∧ G.toNat + 38400 ≤ C.toNat

/-- The registers the output loop keeps. -/
abbrev oRegs : List Reg := [.x2, .x8, .x11, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27]

/-- The output loop at its head `0x80010014`, `j` pushed. -/
structure OI (w₀ w : MachineState) (O G : Word) (ov : Nat → E) (j : Nat) : Prop where
  regs : ∀ r ∈ oRegs, w.getReg r = w₀.getReg r
  x10 : w.getReg .x10 = BitVec.ofNat 64 j
  x12 : w.getReg .x12 = O + BitVec.ofNat 64 (24 * j) + 16
  x23 : w.getReg .x23 = G + BitVec.ofNat 64 (24 * j) + 16
  frame : DFrame w₀ w (Within · O 38400)
  out : ∀ i < j, eAt w (O + BitVec.ofNat 64 (24 * i)) = ov i
  lt : j < 1600

/-- The output loop done, at `0x800100e8`. -/
structure OX (w₀ w : MachineState) (O : Word) (ov : Nat → E) : Prop where
  regs : ∀ r ∈ oRegs, w.getReg r = w₀.getReg r
  x10 : w.getReg .x10 = 1600
  frame : DFrame w₀ w (Within · O 38400)
  out : ∀ i < 1600, eAt w (O + BitVec.ofNat 64 (24 * i)) = ov i

set_option maxHeartbeats 8000000 in
theorem out_step {w₀ w : MachineState} {O C G : Word} {gv cv : Nat → E} {j : Nat}
    (Oc : OC w₀ O C G gv cv) (I : OI w₀ w O G (outV gv cv) j) (hpc : w.pc = 0x80010014) :
    ∃ v, Reaches Image.code w v ∧ ((OI w₀ v O G (outV gv cv) (j + 1) ∧ v.pc = 0x80010014) ∨
      (OX w₀ v O (outV gv cv) ∧ v.pc = 0x800100e8) ∨ Dead Image.code v) := by
  have hj := I.lt
  have hop := Oc.op
  have hcp := Oc.cp
  have hgp := Oc.gp
  have hx : j / 64 % 5 < 5 := Nat.mod_lt _ (by omega)
  have ha3 : 64 * ((j / 64 % 5 + 1) % 5) + j % 64 < 320 := by omega
  have ha4 : 64 * ((j / 64 % 5 + 4) % 5) + (j % 64 + 1) % 64 < 320 := by omega
  -- `0x80010014`: `j` against `g`'s length
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010014_spec hpc trivial
  have pc₁ := b80010014_pc_not_taken h₁ (by
    rw [I.regs .x22 (by decide), Oc.x22, I.x10]
    exact ne_ofNat (by omega) (by rw [show (1600 : Word).toNat = 1600 from rfl]; omega))
  have k₁ := b80010014_keeps h₁
  have hm₁ := b80010014_mem_same h₁
  have x10₁ : t₁.getReg .x10 = BitVec.ofNat 64 j := by rw [k₁ .x10 (by decide), I.x10]
  have x27₁ : t₁.getReg .x27 = 0x3333333333333334 := by
    rw [k₁ .x27 (by decide), I.regs .x27 (by decide), Oc.x27]
  -- `0x80010018`: the two column indices
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80010018_spec pc₁ trivial
  have k₂ := b80010018_keeps h₂
  have hm₂ := b80010018_mem_same h₂
  have x14₂ : t₂.getReg .x14 = BitVec.ofNat 64 (j / 64 % 5) :=
    h₂.reg_eq .x14 rfl (by
      rv_eval [x10₁, x27₁, ushr6 (by omega : j < 2 ^ 64), mulhu5 (by omega : j / 64 < 2 ^ 32), mod5])
  have x13₂ : t₂.getReg .x13 = BitVec.ofNat 64 (64 * ((j / 64 % 5 + 1) % 5) + j % 64) :=
    h₂.reg_eq .x13 rfl (by
      rv_eval [x10₁, x27₁, ushr6 (by omega : j < 2 ^ 64), mulhu5 (by omega : j / 64 < 2 ^ 32), mod5]
      exact x13_eq hx hj)
  have pc₂ := h₂.pc
  rv_eval [x10₁, x27₁, ushr6 (by omega : j < 2 ^ 64), mulhu5 (by omega : j / 64 < 2 ^ 32), mod5] at pc₂
  rcases eq_ite_cases pc₂ with ⟨-, pc₂⟩ | ⟨-, pc₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inr (Or.inr (dead_of_fetch (by rw [pc₂]; exact trap)))⟩
  -- `0x80010050..0x80010064`: the second index's lane
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010050_spec pc₂ trivial
  have k₃ := b80010050_keeps h₃
  have hm₃ := b80010050_mem_same h₃
  have x14₃ : t₃.getReg .x14 = BitVec.ofNat 64 (j / 64 % 5) := by rw [k₃ .x14 (by decide), x14₂]
  have hst : ∃ t₄, Reaches Image.code t₃ t₄ ∧ t₄.pc = 0x80010064 ∧ (∀ a, t₄.getMem a = t₃.getMem a) ∧
      (∀ r ∈ [Reg.x2, .x8, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
        .x27], t₄.getReg r = t₃.getReg r) ∧
      t₄.getReg .x14 = BitVec.ofNat 64 (64 * ((j / 64 % 5 + 4) % 5)) := by
    by_cases h0 : j / 64 % 5 = 0
    · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80010054_spec
        (b80010050_pc_not_taken h₃ (by rw [x14₂, h0]; rfl)) trivial
      refine ⟨t₄, hr₄, b80010054_pc h₄, b80010054_mem_same h₄,
        fun r hr ↦ b80010054_keeps h₄ r (mem_of_mem hr _), ?_⟩
      rw [b80010054_x14 h₄, h0]; rfl
    · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8001005c_spec
        (b80010050_pc_taken h₃ (by rw [x14₂]; exact ofNat_ne0 (by omega) (by omega))) trivial
      refine ⟨t₄, hr₄, b8001005c_pc h₄, b8001005c_mem_same h₄,
        fun r hr ↦ b8001005c_keeps h₄ r (mem_of_mem hr _), ?_⟩
      rw [b8001005c_x14 h₄, x14₃, x14_dec hx h0]
  obtain ⟨t₄, hr₄, pc₄, hm₄, k₄, x14₄⟩ := hst
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80010064_spec pc₄ trivial
  have r₄ (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x10, .x11, .x12, .x19, .x20, .x21, .x22, .x23, .x24,
      .x25, .x26, .x27]) : t₄.getReg r = w.getReg r := by
    rw [k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
      k₁ r (mem_of_mem hr _)]
  have x10₄ : t₄.getReg .x10 = BitVec.ofNat 64 j := by rw [r₄ .x10 (by decide), I.x10]
  have x14₅ : t₅.getReg .x14 = BitVec.ofNat 64 (64 * ((j / 64 % 5 + 4) % 5) + (j % 64 + 1) % 64) := by
    rw [b80010064_x14 h₅, x14₄, x10₄, x14_or (x := j / 64 % 5) hj]
  have pc₅ := b80010064_pc_not_taken h₅ (by
    rw [x14₄, x10₄, x14_or (x := j / 64 % 5) hj, r₄ .x24 (by decide), I.regs .x24 (by decide), Oc.x24,
      BitVec.toNat_ofNat, show (320 : Word).toNat = 320 from rfl, Nat.mod_eq_of_lt (by omega)]
    exact ha4)
  have k₅ := b80010064_keeps h₅
  have hm₅ := b80010064_mem_same h₅
  have r₅ (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x11, .x12, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27]) : t₅.getReg r = w.getReg r := by
    rw [k₅ r (mem_of_mem hr _), r₄ r (mem_of_mem hr _)]
  have x13₅ : t₅.getReg .x13 = BitVec.ofNat 64 (64 * ((j / 64 % 5 + 1) % 5) + j % 64) := by
    rw [k₅ .x13 (by decide), k₄ .x13 (by decide), k₃ .x13 (by decide), x13₂]
  have x8₅ : t₅.getReg .x8 = C := by rw [r₅ .x8 (by decide), I.regs .x8 (by decide), Oc.x8]
  have x12₅ : t₅.getReg .x12 = O + BitVec.ofNat 64 (24 * j) + 16 := by rw [r₅ .x12 (by decide), I.x12]
  have x23₅ : t₅.getReg .x23 = G + BitVec.ofNat 64 (24 * j) + 16 := by rw [r₅ .x23 (by decide), I.x23]
  have hm05 (a : Word) : t₅.getMem a = w.getMem a := by rw [hm₅, hm₄, hm₃, hm₂, hm₁]
  have hOV : ValidMemRange O 4800 := heap_vmr hop.2.1 (by omega) hop.1
  have hCV : ValidMemRange C 960 := heap_vmr hcp.2.1 (by omega) hcp.1
  have hGV : ValidMemRange G 4800 := heap_vmr hgp.2.1 (by omega) hgp.1
  -- `0x80010074`: the output pushed
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80010074_spec pc₅ (by
    rv_eval [x8₅, x12₅, x13₅, x14₅, x23₅, mul24n]
    and_intros <;> first
      | valid_access hOV [hop, hj]
      | valid_access hCV [hcp, ha3, ha4]
      | valid_access hGV [hgp, hj])
  have k₆ := b80010074_keeps h₆
  have f₆ := b80010074_frame h₆ (by rw [x12₅]; constructor <;> addr_omega [hop, hj])
  rw [x12₅, show O + BitVec.ofNat 64 (24 * j) + 16 - 16 = O + BitVec.ofNat 64 (24 * j) by rv_eval []] at f₆
  have n0 := b80010074_m_x12_n16 h₆
  have n8 := b80010074_m_x12_n8 h₆
  have n16 := b80010074_m_x12_0 h₆
  rw [x8₅, x12₅, x13₅, x14₅, x23₅, mul24n, mul24n] at n0 n8 n16
  rv_eval [] at n0 n8 n16
  have cw (q : Nat) (hq : q < 320) : eAt t₅ (C + BitVec.ofNat 64 (24 * q)) = cv q := by
    rw [← Oc.c q hq, ← I.frame.eAt fun i hi hw ↦ by addr_omega [hw, hi, hcp, hq]]
    unfold Rv64Verifier.eAt; rw [hm05, hm05, hm05]
  have gw : eAt t₅ (G + BitVec.ofNat 64 (24 * j)) = gv j := by
    rw [← Oc.g j hj, ← I.frame.eAt fun i hi hw ↦ by addr_omega [hw, hi, hcp, hgp, hj]]
    unfold Rv64Verifier.eAt; rw [hm05, hm05, hm05]
  have enew : eAt t₆ (O + BitVec.ofNat 64 (24 * j)) = outV gv cv j := by
    apply eAt_eq_of_limbs
    rw [outV, limbs_add, limbs_add, ← cw _ ha3, ← gw, ← cw _ ha4]
    simp only [limbs_eAt]
    rv_eval [n0, n8, n16]
  have F₆ : DFrame w₀ t₆ (Within · O 38400) :=
    (I.frame.trans (DFrame.of_same hm05 _) fun _ h ↦ h).trans (DFrame.of_memFrame f₆) fun a h ↦ by
      addr_omega [h, hop, hj]
  have out₆ (i : Nat) (hi : i < j + 1) : eAt t₆ (O + BitVec.ofNat 64 (24 * i)) = outV gv cv i := by
    by_cases hij : i = j
    · rw [hij, enew]
    · rw [f₆.eAt (by addr_omega [hop, hj, hi, hij]) (by addr_omega [hop, hj, hi]), ← I.out i (by omega)]
      unfold Rv64Verifier.eAt; rw [hm05, hm05, hm05]
  have regs₆ (r : Reg) (hr : r ∈ oRegs) : t₆.getReg r = w₀.getReg r := by
    rw [k₆ r (mem_of_mem hr _), r₅ r (mem_of_mem hr _), I.regs r hr]
  have x10₆ : t₆.getReg .x10 = BitVec.ofNat 64 (j + 1) := by
    rw [k₆ .x10 (by decide), b80010064_x10 h₅, x10₄, ofNat_succ]
  have x25₅ : t₅.getReg .x25 = 1600 := by rw [r₅ .x25 (by decide), I.regs .x25 (by decide), Oc.x25]
  have hr := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))
  by_cases hl : j + 1 < 1600
  · refine ⟨t₆, hr, Or.inl ⟨{
      regs := regs₆
      x10 := x10₆
      x12 := by rw [b80010074_x12 h₆, x12₅, st24d]
      x23 := by rw [b80010074_x23 h₆, x23₅, st24d]
      frame := F₆
      out := out₆
      lt := hl }, b80010074_pc_taken h₆ ?_⟩⟩
    rw [b80010064_x10 h₅, x10₄, ofNat_succ, x25₅]
    exact (ne_ofNat (by omega) (by rw [show (1600 : Word).toNat = 1600 from rfl]; omega)).symm
  · refine ⟨t₆, hr, Or.inr (Or.inl ⟨{
      regs := regs₆
      x10 := by rw [x10₆, show j + 1 = 1600 by omega]; rfl
      frame := F₆
      out := fun i hi ↦ out₆ i (by omega) }, b80010074_pc_not_taken h₆ ?_⟩)⟩
    rw [b80010064_x10 h₅, x10₄, ofNat_succ, x25₅, show j + 1 = 1600 by omega]; rfl

theorem out_loop {w₀ : MachineState} {O C G : Word} {gv cv : Nat → E} (Oc : OC w₀ O C G gv cv) :
    ∀ n j w, j + n = 1600 → OI w₀ w O G (outV gv cv) j → w.pc = 0x80010014 →
      ∃ v, Reaches Image.code w v ∧ ((OX w₀ v O (outV gv cv) ∧ v.pc = 0x800100e8) ∨ Dead Image.code v)
  | 0, j, w, hn, Q, _ => absurd Q.lt (by omega)
  | n + 1, j, w, hn, Q, hpc => by
    obtain ⟨v, hr, ⟨Q', hpc'⟩ | ⟨X, hpc'⟩ | hd⟩ := out_step Oc Q hpc
    · obtain ⟨t, hr', ht⟩ := out_loop Oc n (j + 1) v (by omega) Q' hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · exact ⟨v, hr, Or.inl ⟨X, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

/-! ## From `J16` -/

/-- The output pushed, at `0x800100e8`: its `Vec` at `f + 960`, its length `0 + 1600` in `a1 + a0`. -/
structure J17 (s u v : MachineState) (eqZ eqLane t : List E) (beta : E) : Prop where
  pc : v.pc = 0x800100e8
  base : Base s v
  mono : heapNext u ≤ heapNext v
  frame : DFrame u v (SW2 s (heapNext u) (heapNext v))
  x10 : v.getReg .x10 = 1600
  x11 : v.getReg .x11 = 0
  ocap : 1600 ≤ (v.getMem (s.getReg .x2 - 752)).toNat
  obuf : heapNext u ≤ (v.getMem (s.getReg .x2 - 744)).toNat ∧
    (v.getMem (s.getReg .x2 - 744)).toNat + (v.getMem (s.getReg .x2 - 752)).toNat * 24 ≤ heapNext v ∧
    (v.getMem (s.getReg .x2 - 744)).toNat % 8 = 0
  oE : eListAt v (v.getMem (s.getReg .x2 - 744)) 1600 =
    linearTransposeRust (nextWeightsRust eqZ eqLane beta)
  val : (v.getReg .x19, v.getReg .x20, v.getReg .x21) =
    limbs (t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0))
  x26 : v.getReg .x26 = u.getReg .x26

set_option maxHeartbeats 16000000 in
theorem output (hA : AllocSpec) (hR : ReserveFreshSpec 0x80008a10 24 8) {s u w : MachineState}
    {eqZ eqLane t : List E} {beta : E} (hpre : VerifyLayerPre s) (hsu : heapNext s ≤ heapNext u)
    (K : J16 s u w eqZ eqLane t beta) :
    ∃ v, Reaches Image.code w v ∧ (J17 s u v eqZ eqLane t beta ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := K.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  simp only [stackLo] at hnx hab
  unfold verifyLayerStack at hb hnx hab
  have hHw := B.heap.hi
  have hH0 := hpre.heap.lo
  have hkm := K.mono
  have hgb := K.gbuf
  have hcb := K.cbuf
  -- `0x8000ffb8`: `alloc(8, 38400)`
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000ffb8_spec K.pc trivial
  have k₀ := b8000ffb8_keeps h₀
  have hm₀ := b8000ffb8_mem_same h₀
  have x2₀ : t₀.getReg .x2 = s.getReg .x2 - 1712 := (k₀ .x2 (by decide)).trans B.x2
  have B₀ : Base s t₀ := B.same x2₀ hm₀
  have hN₀ : heapNext t₀ = heapNext w := by simp only [heapNext, hm₀]
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, A⟩ | hd⟩ := hA.call hr₀ (b8000ffb8_pc h₀)
    ⟨B₀.heap, by rw [b8000ffb8_x10 h₀]; decide⟩
  swap
  · exact ⟨_, hr₁, Or.inr hd⟩
  have hal := A.aligned
  have hab₁ := A.above
  have hnx₁ := A.next
  rw [b8000ffb8_x10 h₀] at hal
  rw [b8000ffb8_x11 h₀] at hnx₁
  simp only [show (8 : Word).toNat = 8 from rfl] at hal
  simp only [show (38400 : Word).toNat = 38400 from rfl] at hnx₁
  rw [hN₀] at hab₁
  have F₁ : DFrame t₀ t₁ (Within · nextAddr 8) := fun a ha ↦ A.mem a fun h ↦
    ha 0 (by decide) (by rw [h, add_ofNat_zero]; addr_omega [])
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (hp₁.reg .x2).trans x2₀
  have B₁ : Base s t₁ := B₀.next hpre x2₁ A.heap (by omega) F₁ fun a h ↦
    ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), by addr_omega [h, hb, hnx]⟩
  -- `0x8000ffcc`: the null check
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000ffcc_spec
    (by rw [hpc₁, returnAddress_eq, b8000ffb8_x1 h₀]; decide) trivial
  have k₂ := b8000ffcc_keeps h₂
  have hm₂ := b8000ffcc_mem_same h₂
  have hne : t₁.getReg .x10 ≠ 0 := fun h ↦ by
    rw [h, show (0 : Word).toNat = 0 from rfl] at hab₁
    simp only [heapStart] at hH0
    omega
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have B₂ : Base s t₂ := B₁.same x2₂ hm₂
  -- `0x8000ffd0`: the `Vec` `{1600, ptr, 0}` at `f + 960`, `reserve(1600)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000ffd0_spec
    (b8000ffcc_pc_not_taken h₂ hne) (by
      rv_eval [x2₂]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000ffd0_keeps h₃
  have f₃ := b8000ffd0_frame h₃ (by rw [x2₂]; addr_omega [hb])
  rw [x2₂] at f₃
  rv_eval [] at f₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.slots hpre x2₃ f₃ (by addr_omega [hb]) (by addr_omega [hb])
  have n0 := b8000ffd0_m_x2_960 h₃
  have n8 := b8000ffd0_m_x2_968 h₃
  have n16 := b8000ffd0_m_x2_976 h₃
  rw [x2₂] at n0 n8 n16
  rw [k₂ .x10 (by decide)] at n8
  rv_eval [] at n0 n8 n16
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 752 := by rw [b8000ffd0_x10 h₃, x2₂]; rv_eval []
  have x11₃ : t₃.getReg .x11 = 1600 := b8000ffd0_x11 h₃
  have hN₃ : heapNext t₃ = heapNext t₁ := by
    simp only [heapNext]
    rw [f₃ _ (by addr_omega [hb, hnx]), hm₂]
  have pre : ReservePre 24 8 t₃ := {
    heap := B₃.heap
    self := by rw [x10₃]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    vec := {
      raw := by
        simp only [RawVecOk, Buf, vecPtr, vecCap, x10₃]
        rv_eval [n0, n8]
        rw [hN₃, hnx₁]
        simp only [heapStart] at hH0 ⊢
        omega
      len := by simp only [vecLen, vecCap, x10₃]; rv_eval [n0, n16]; decide }
    stack := hpre.stack.sub 1712 x2₃ (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)
    selfFree := by rw [x10₃]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    selfStack := by rw [x10₃]; simp only [stackLo, x2₃]; addr_omega [hb] }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, R, Rf⟩ | hd⟩ := hR.call hr₃ (b8000ffd0_pc h₃) pre
  swap
  · exact ⟨_, hr₁.trans (hr₂.trans hr₄), Or.inr hd⟩
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (hp₄.reg .x2).trans x2₃
  have rcap := R.cap
  have rlen := R.len
  have rraw := R.vec.raw
  have rH := R.heap.hi
  simp only [x10₃, x11₃, vecLen, vecCap, vecPtr, RawVecOk, Buf] at rcap rlen rraw Rf
  rv_eval [n0, n8, n16] at rcap rlen rraw Rf
  obtain ⟨O, hOd⟩ : ∃ O, t₄.getMem (s.getReg .x2 - 744) = O := ⟨_, rfl⟩
  obtain ⟨cap, hcd⟩ : ∃ cap, t₄.getMem (s.getReg .x2 - 752) = cap := ⟨_, rfl⟩
  rw [hOd] at rraw Rf
  rw [hcd] at rcap rraw Rf
  have hip : heapNext w ≤ O.toNat ∧ O.toNat + cap.toNat * 24 ≤ heapNext t₄ := by
    rcases Rf with ⟨e1, e2⟩ | ⟨-, h0 | ⟨h1, h2⟩⟩
    · rw [e1, e2]; have := R.mono; rw [hN₃] at this
      exact ⟨hab₁, by rw [show (1600 : Word).toNat = 1600 from rfl]; omega⟩
    · omega
    · rw [hN₃] at h1; exact ⟨by omega, h2⟩
  have hcap : 1600 ≤ cap.toNat := by omega
  have B₄ : Base s t₄ := B₃.next hpre x2₄ R.heap R.mono (DFrame.of_byteFrame R.frame)
    fun a ha ↦ cframe_lw hpre B₃ 752 (by decide) (by decide) (by decide) R.heap x10₃ a ha
  have F₄ : DFrame w t₄ (SW2 s (heapNext w) (heapNext t₄)) :=
    ((((DFrame.of_same hm₀ _).trans F₁ fun a h ↦ Or.inr (Or.inr (Or.inr (Or.inl h)))).trans
      (DFrame.of_same hm₂ _) fun _ h ↦ h).trans (DFrame.of_memFrame f₃) fun a h ↦
        Or.inr (Or.inl (by addr_omega [h, hb]))).trans
      (DFrame.of_byteFrame R.frame) fun a h ↦ by
        simp only [Fresh, stackLo, x10₃, x2₃] at h ⊢
        rcases h with h | h | h | h
        · exact Or.inr (Or.inl (by addr_omega [h, hb]))
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [hN₃] at h; omega, h.2⟩)))
  -- `0x8000fff0`: the loop's registers
  obtain ⟨w₀, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000fff0_spec
    (by rw [hpc₄, returnAddress_eq, b8000ffd0_x1 h₃]; decide) (by
      rv_eval [x2₄]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₅ := b8000fff0_keeps h₅
  have hm₅ := b8000fff0_mem_same h₅
  have x2₅ : w₀.getReg .x2 = s.getReg .x2 - 1712 := (k₅ .x2 (by decide)).trans x2₄
  have B₅ : Base s w₀ := B₄.same x2₅ hm₅
  have hN₅ : heapNext w₀ = heapNext t₄ := by simp only [heapNext, hm₅]
  have F₅ : DFrame w w₀ (SW2 s (heapNext w) (heapNext w₀)) := by
    rw [hN₅]; exact F₄.trans (DFrame.of_same hm₅ _) fun _ h ↦ h
  have rg (r : Reg) (hr : r ∈ [Reg.x8, .x19, .x20, .x21, .x22, .x24, .x26, .x27]) :
      w₀.getReg r = w.getReg r := by
    rw [k₅ r (mem_of_mem hr _), hp₄.reg r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
      hp₁.reg r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k₀ r (mem_of_mem hr _)]
  obtain ⟨G, hGd⟩ : ∃ G, w.getReg .x23 = G := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, w.getReg .x8 = C := ⟨_, rfl⟩
  rw [hGd, hCd] at hgb
  rw [hCd] at hcb
  have wb (p : Word) (n : Nat) (hp : p.toNat + n ≤ heapNext w) (k : Nat) (hk : k + 24 ≤ n) :
      eAt w₀ (p + BitVec.ofNat 64 k) = eAt w (p + BitVec.ofNat 64 k) :=
    F₅.eAt fun i hi ↦ by rw [add_ofNat_add]; exact sw2_buf hpre hHw (n := n) hp _ (by omega)
  have Oc : OC w₀ O C G (gOf (nextWeightsRust eqZ eqLane beta))
      (colAcc (gOf (nextWeightsRust eqZ eqLane beta)) 1600) := {
    x8 := by rw [rg .x8 (by decide), hCd]
    x22 := by rw [rg .x22 (by decide), K.x22]
    x24 := by rw [rg .x24 (by decide), K.x24]
    x25 := by rw [k₅ .x25 (by decide), hp₄.reg .x25, b8000ffd0_x25 h₃]
    x27 := by rw [rg .x27 (by decide), K.x27]
    g := fun p hp ↦ by rw [wb G 38400 (by omega) _ (by omega), ← hGd]; exact K.gE p hp
    c := fun q hq ↦ by rw [wb C 7680 hcb.1 _ (by omega), ← hCd]; exact K.cE q hq
    op := ⟨rraw.1, by simp only [heapStart] at hH0 ⊢; omega, by omega⟩
    cp := ⟨hcb.2, by simp only [heapStart] at hH0 ⊢; omega, by omega⟩
    gp := ⟨hgb.2.2, by have := hgb.1; simp only [heapStart] at hH0 ⊢; omega, hgb.2.1⟩ }
  have I₀ : OI w₀ w₀ O G (outV (gOf (nextWeightsRust eqZ eqLane beta))
      (colAcc (gOf (nextWeightsRust eqZ eqLane beta)) 1600)) 0 := {
    regs := fun _ _ ↦ rfl
    x10 := b8000fff0_x10 h₅
    x12 := by
      rw [b8000fff0_x12 h₅, x2₄, Nat.mul_zero, add_ofNat_zero]; rv_eval [rlen, hOd]
      bv_omega
    x23 := by
      rw [b8000fff0_x23 h₅, Nat.mul_zero, add_ofNat_zero, hp₄.reg .x23, k₃ .x23 (by decide),
        k₂ .x23 (by decide), hp₁.reg .x23, k₀ .x23 (by decide), hGd]
    frame := DFrame.refl _ _
    out := fun i hi ↦ absurd hi (Nat.not_lt_zero i)
    lt := by decide }
  obtain ⟨v, hr₆, ⟨X, hpc₆⟩ | hd⟩ := out_loop Oc 1600 0 w₀ rfl I₀ (b8000fff0_pc h₅)
  swap
  · exact ⟨v, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans hr₆))), Or.inr hd⟩
  have hNv : v.getMem nextAddr = w₀.getMem nextAddr := X.frame _ fun i hi hw ↦ by
    addr_omega [hw, hi, hip, rH]
  have hNv' : heapNext v = heapNext w₀ := by simp only [heapNext, hNv]
  have Bv : Base s v := B₅.next hpre ((X.regs .x2 (by decide)).trans x2₅)
    ⟨by rw [hNv']; exact B₅.heap.lo, by rw [hNv']; exact B₅.heap.hi⟩ (le_of_eq hNv'.symm)
    X.frame fun a h ↦ ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hip, hsu, hkm],
      by rw [hNv', hN₅]; addr_omega [h, hip, hcap]⟩))), by addr_omega [h, hb, hip, rH, hab, hcap]⟩
  have keepv (y : Word) (hy : (s.getReg .x2).toNat - 752 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 728) :
      v.getMem y = t₄.getMem y := by
    rw [X.frame _ fun i hi hw ↦ by addr_omega [hw, hi, hip, rH, hb, hab, hcap, hy], hm₅]
  refine ⟨v, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans hr₆))), Or.inl {
    pc := hpc₆
    base := Bv
    mono := by rw [hNv', hN₅]; have := R.mono; rw [hN₃] at this; omega
    frame := (K.frame.mono fun a h ↦ sw2_mono (by rw [hNv', hN₅]; have := R.mono; rw [hN₃] at this; omega) h).trans
      (F₅.trans X.frame fun a h ↦ Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hip],
        by rw [hN₅]; addr_omega [h, hip, hcap]⟩)))) fun a h ↦ by
      simp only [SW2] at h ⊢
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hNv']; exact h.2⟩)))
    x10 := X.x10
    x11 := by rw [X.regs .x11 (by decide), b8000fff0_x11 h₅, x2₄]; rv_eval [rlen]
    ocap := by rw [keepv _ (by addr_omega [hb]), hcd]; exact hcap
    obuf := by
      rw [keepv _ (by addr_omega [hb]), keepv _ (by addr_omega [hb]), hOd, hcd, hNv', hN₅]
      exact ⟨by omega, hip.2, rraw.1⟩
    oE := by
      rw [keepv _ (by addr_omega [hb]), hOd]
      exact eListAt_of_getD (linearTransposeRust_length _) fun i hi ↦ by
        rw [X.out i hi, outV_eq _ hi]
    val := by
      rw [X.regs .x19 (by decide), X.regs .x20 (by decide), X.regs .x21 (by decide),
        rg .x19 (by decide), rg .x20 (by decide), rg .x21 (by decide), K.val]
    x26 := by rw [X.regs .x26 (by decide), rg .x26 (by decide), K.x26] }⟩

end Rv64Verifier.Gkr.Layer
