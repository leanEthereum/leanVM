import Rv64Verifier.Proofs.Gkr.LayerR12
import Rv64Verifier.Proofs.Gkr.LayerWeights

/-!
# `keccak::verify_layer`: `linear_transpose`'s first loop

`keccak.rs:85-90` at `0x8000fe2c..0x8000fed8`: per lane `L` and bit `z`, `g[64 L + z] =
w[((RHO[L] + z) & 63) | (PI[L] << 6)]`, `PI` (`u64`) in `.rodata` at `0xa00005b8`, `RHO` (`u32`)
at `0xa0000550`.

`RHO`'s load `lw` reads at `0xa0000550 + 4 L`, a doubleword's upper half for odd `L`; the
generated block at `0x8000fe54` asks for an aligned address, so it is checked again here with
sub-doubleword loads at any address (`cfgA`), as `0x8000f4a0` is.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The tables -/

/-- `RHO[L]`'s address `x12 + 4 x15`. -/
def rhoE : Sym.E := .bin .add (.reg .x12) (.bin .sll (.reg .x15) (.c 2))

/-- `0x8000fe54` with `RHO[L]` loaded at any address. -/
def fe54A : Sym.Expect :=
  { b8000fe54 with
    regs := b8000fe54.regs.map fun p ↦ (p.1, if p.1 == .x16 then
      .bin (.ldx .w) (.ld (.bin .and rhoE (.c 0xfffffffffffffff8))) (.bin .and rhoE (.c 7))
      else p.2)
    obl := [.valid ⟨some rhoE, 0⟩ 4,
      .valid ⟨some (.bin .add (.reg .x11) (.bin .sll (.reg .x15) (.c 3))), 0⟩ 8,
      .align8 (.bin .add (.reg .x11) (.bin .sll (.reg .x15) (.c 3)))] }

theorem fe54A_spec : Sym.BlockSpec Image.code 0x8000fe54 11 (fun s ↦ Sym.Oblig.all s fe54A.obl)
    fe54A.Holds :=
  Sym.BlockSpec.of_expect (cfg := cfgA) (fuel := 11) (x := fe54A)
    (words := (Image.code.words.drop 16277).take 11) (by decide +kernel)
    (Sym.CodeAt.slice Image.code 16277 11 0x8000fe54 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

theorem fe54A_x16 {s t : MachineState} (h : fe54A.Holds s t) :
    t.getReg .x16 = BitVec.signExtend 64 (extractWord32
      (s.getMem ((s.getReg .x12 + s.getReg .x15 * 4) &&& 0xfffffffffffffff8))
      (((s.getReg .x12 + s.getReg .x15 * 4) &&& 7).toNat / 4)) :=
  h.reg_eq .x16 rfl (by rv_eval [rhoE])

theorem fe54A_x5 {s t : MachineState} (h : fe54A.Holds s t) : t.getReg .x5 = 64 :=
  h.reg_eq .x5 rfl (by rv_eval [])

theorem fe54A_x6 {s t : MachineState} (h : fe54A.Holds s t) : t.getReg .x6 = s.getReg .x10 :=
  h.reg_eq .x6 rfl (by rv_eval [])

theorem fe54A_x7 {s t : MachineState} (h : fe54A.Holds s t) : t.getReg .x7 = s.getReg .x14 :=
  h.reg_eq .x7 rfl (by rv_eval [])

theorem fe54A_x15 {s t : MachineState} (h : fe54A.Holds s t) : t.getReg .x15 = s.getReg .x15 + 1 :=
  h.reg_eq .x15 rfl (by rv_eval [])

theorem fe54A_x17 {s t : MachineState} (h : fe54A.Holds s t) :
    t.getReg .x17 = s.getMem (s.getReg .x11 + (s.getReg .x15 * (8 : Word))) * (64 : Word) :=
  h.reg_eq .x17 rfl (by rv_eval [])

theorem fe54A_keeps {s t : MachineState} (h : fe54A.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x18, .x19, .x20, .x21, .x22,
      .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem fe54A_pc {s t : MachineState} (h : fe54A.Holds s t) : t.pc = 0x8000fe80 :=
  h.pc_eq rfl

theorem fe54A_mem_same {s t : MachineState} (h : fe54A.Holds s t) (a : Word) :
    t.getMem a = s.getMem a :=
  h.mem_same rfl a

theorem pi_word {u : MachineState} (h : RodataOk u) {L : Nat} (hL : L < 25) :
    u.getMem (0xa00005b8 + BitVec.ofNat 64 L * 8) = BitVec.ofNat 64 (keccakPi L) := by
  interval_cases L <;> exact h.word

theorem rho_dword {u : MachineState} (h : RodataOk u) {k : Nat} (hk : k < 13) :
    u.getMem (0xa0000550 + BitVec.ofNat 64 (8 * k)) = BitVec.ofNat 64 (keccakRho.getD (2 * k) 0) |||
      BitVec.ofNat 64 (keccakRho.getD (2 * k + 1) 0) <<< 32 := by
  interval_cases k <;> exact h.word

/-- The `RHO[L]` `lw` loads, sign-extended. -/
theorem rho_word {u : MachineState} (h : RodataOk u) {L : Nat} (hL : L < 25) :
    BitVec.signExtend 64 (extractWord32
      (u.getMem ((0xa0000550 + BitVec.ofNat 64 L * 4) &&& 0xfffffffffffffff8))
      (((0xa0000550 + BitVec.ofNat 64 L * 4) &&& 7).toNat / 4)) =
      BitVec.ofNat 64 (keccakRho.getD L 0) := by
  have ha : (0xa0000550 + BitVec.ofNat 64 L * 4) &&& 0xfffffffffffffff8 =
      0xa0000550 + BitVec.ofNat 64 (8 * (L / 2)) := by interval_cases L <;> decide
  have ho : ((0xa0000550 + BitVec.ofNat 64 L * 4) &&& 7).toNat / 4 = L % 2 := by
    interval_cases L <;> decide
  rw [ha, ho, rho_dword h (by omega)]
  interval_cases L <;> decide

theorem pi_lt {L : Nat} (hL : L < 25) : keccakPi L < 25 := by interval_cases L <;> decide

theorem rho_lt {L : Nat} (hL : L < 25) : keccakRho.getD L 0 < 64 := by interval_cases L <;> decide

/-- Where `g[64 L + z]` comes from. -/
def src (L z : Nat) : Nat := 64 * keccakPi L + (z + keccakRho.getD L 0) % 64

theorem src_lt {L z : Nat} (hL : L < 25) : src L z < 1600 := by
  have := pi_lt hL
  unfold src; omega

theorem or_low {a p : Nat} (ha : a < 64) (hp : p < 25) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (64 * p) = BitVec.ofNat 64 (64 * p + a) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 64 (64 * p)).toNat = 64 * p := by rw [BitVec.toNat_ofNat]; omega
  have e3 : (BitVec.ofNat 64 (64 * p + a)).toNat = 64 * p + a := by rw [BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_or, e1, e2, e3, Nat.lor_comm,
    show 64 * p = p <<< 6 by rw [Nat.shiftLeft_eq]; ring,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega : a < 2 ^ 6)]

theorem src_eq {L z : Nat} (hL : L < 25) (hz : z < 64) :
    (BitVec.ofNat 64 (keccakRho.getD L 0 + z) &&& 63) ||| BitVec.ofNat 64 (64 * keccakPi L) =
      BitVec.ofNat 64 (src L z) := by
  have hp := pi_lt hL
  have hr := rho_lt hL
  rw [and63 (by omega), or_low (by omega) hp, src, Nat.add_comm z]

/-! ## The loops -/

/-- What the loops read, at their start `w₀`: `w` (1600 `E`) at `P`, `g` at `G` after it. -/
structure TC (w₀ : MachineState) (G P : Word) (W : Nat → E) : Prop where
  ro : RodataOk w₀
  x8 : w₀.getReg .x8 = 1600
  x11 : w₀.getReg .x11 = 0xa00005b8
  x12 : w₀.getReg .x12 = 0xa0000550
  x13 : w₀.getReg .x13 = 25
  x22 : w₀.getReg .x22 = 1600
  x25 : w₀.getReg .x25 = P
  w : ∀ i < 1600, eAt w₀ (P + BitVec.ofNat 64 (24 * i)) = W i
  gp : G.toNat % 8 = 0 ∧ heapStart ≤ G.toNat ∧ G.toNat + 38400 ≤ heapEnd
  pp : P.toNat % 8 = 0 ∧ heapStart ≤ P.toNat ∧ P.toNat + 38400 ≤ G.toNat

/-- The registers the loops keep. -/
abbrev tRegs : List Reg := [.x2, .x8, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27]

/-- The bit loop at its head `0x8000fe80`: lane `L`, `z` bits done. -/
structure TI (w₀ w : MachineState) (G : Word) (W : Nat → E) (L z : Nat) : Prop where
  regs : ∀ r ∈ tRegs, w.getReg r = w₀.getReg r
  x5 : w.getReg .x5 = BitVec.ofNat 64 (64 - z)
  x6 : w.getReg .x6 = BitVec.ofNat 64 (64 * L + z)
  x7 : w.getReg .x7 = G + BitVec.ofNat 64 (24 * (64 * L + z))
  x10 : w.getReg .x10 = BitVec.ofNat 64 (64 * L)
  x14 : w.getReg .x14 = G + BitVec.ofNat 64 (1536 * L)
  x15 : w.getReg .x15 = BitVec.ofNat 64 (L + 1)
  x16 : w.getReg .x16 = BitVec.ofNat 64 (keccakRho.getD L 0 + z)
  x17 : w.getReg .x17 = BitVec.ofNat 64 (64 * keccakPi L)
  frame : DFrame w₀ w (Within · G 38400)
  g : ∀ p < 64 * L + z, eAt w (G + BitVec.ofNat 64 (24 * p)) = W (src (p / 64) (p % 64))
  lt : L < 25
  le : z ≤ 64

/-- The lane loop at its head `0x8000fe54`, `L` lanes done. -/
structure TO (w₀ w : MachineState) (G : Word) (W : Nat → E) (L : Nat) : Prop where
  regs : ∀ r ∈ tRegs, w.getReg r = w₀.getReg r
  x10 : w.getReg .x10 = BitVec.ofNat 64 (64 * L)
  x14 : w.getReg .x14 = G + BitVec.ofNat 64 (1536 * L)
  x15 : w.getReg .x15 = BitVec.ofNat 64 L
  frame : DFrame w₀ w (Within · G 38400)
  g : ∀ p < 64 * L, eAt w (G + BitVec.ofNat 64 (24 * p)) = W (src (p / 64) (p % 64))
  lt : L < 25

/-- The loops done, at `0x8000fed8`. -/
structure TX (w₀ w : MachineState) (G : Word) (W : Nat → E) : Prop where
  regs : ∀ r ∈ tRegs, w.getReg r = w₀.getReg r
  frame : DFrame w₀ w (Within · G 38400)
  g : ∀ p < 1600, eAt w (G + BitVec.ofNat 64 (24 * p)) = W (src (p / 64) (p % 64))

theorem sub_one_ofNat {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
  omega

set_option maxHeartbeats 4000000 in
theorem bit_step' {w₀ w : MachineState} {G P : Word} {W : Nat → E} {L z : Nat}
    (C : TC w₀ G P W) (I : TI w₀ w G W L z) (hz : z < 64) (hpc : w.pc = 0x8000fe80) :
    ∃ v, Reaches Image.code w v ∧ ((TI w₀ v G W L (z + 1) ∧
      ((z + 1 < 64 ∧ v.pc = 0x8000fe80) ∨ (z + 1 = 64 ∧ v.pc = 0x8000fecc))) ∨
      Dead Image.code v) := by
  have hL := I.lt
  have hgp := C.gp
  have hpp := C.pp
  have hs := src_lt (z := z) hL
  have h64 : 64 * L + z < 1600 := by omega
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000fe80_spec hpc trivial
  have hx28 : (w.getReg .x16 &&& 63) ||| w.getReg .x17 = BitVec.ofNat 64 (src L z) := by
    rw [I.x16, I.x17, src_eq hL hz]
  have pc₁ := b8000fe80_pc_not_taken h₁ (by
    rw [hx28, I.regs .x8 (by decide), C.x8, BitVec.toNat_ofNat,
      show (1600 : Word).toNat = 1600 from rfl]; omega)
  have k₁ := b8000fe80_keeps h₁
  have hm₁ := b8000fe80_mem_same h₁
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000fe8c_spec pc₁ trivial
  have k₂ := b8000fe8c_keeps h₂
  have hm₂ := b8000fe8c_mem_same h₂
  have pc₂ := b8000fe8c_pc_not_taken h₂ (by
    rw [k₁ .x22 (by decide), I.regs .x22 (by decide), C.x22, k₁ .x6 (by decide), I.x6,
      BitVec.toNat_ofNat, show (1600 : Word).toNat = 1600 from rfl]; omega)
  have r₂ (r : Reg) (hr : r ∈ [Reg.x2, .x5, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
      .x17, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27]) : t₂.getReg r = w.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x28₂ : t₂.getReg .x28 = BitVec.ofNat 64 (src L z) := by
    rw [k₂ .x28 (by decide), b8000fe80_x28 h₁, hx28]
  have x7₂ : t₂.getReg .x7 = G + BitVec.ofNat 64 (24 * (64 * L + z)) := by
    rw [r₂ .x7 (by decide), I.x7]
  have x25₂ : t₂.getReg .x25 = P := by rw [r₂ .x25 (by decide), I.regs .x25 (by decide), C.x25]
  have hGV : ValidMemRange G 4800 := heap_vmr hgp.2.1 (by omega) hgp.1
  have hPV : ValidMemRange P 4800 := heap_vmr hpp.2.1 (by omega) hpp.1
  -- `0x8000fe90`: `g[64 L + z] = w[src]`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000fe90_spec pc₂ (by
    rv_eval [x7₂, x25₂, x28₂, mul24n]
    and_intros <;> first
      | valid_access hGV [hgp, h64]
      | valid_access hPV [hpp, hs]
      | addr_omega [hgp, hpp, hs, h64])
  have k₃ := b8000fe90_keeps h₃
  have f₃ := b8000fe90_frame h₃ (by rw [x7₂]; addr_omega [hgp, h64])
  rw [x7₂] at f₃
  have hm12 (a : Word) : t₂.getMem a = w.getMem a := by rw [hm₂, hm₁]
  have enew : eAt t₃ (G + BitVec.ofNat 64 (24 * (64 * L + z))) = W (src L z) := by
    have n0 := b8000fe90_m_x7_0 h₃
    have n8 := b8000fe90_m_x7_8 h₃
    have n16 := b8000fe90_m_x7_16 h₃
    rw [x7₂, x25₂, x28₂, mul24n] at n0 n8 n16
    rw [← C.w _ hs, ← I.frame.eAt fun i hi hw ↦ by addr_omega [hw, hi, hpp, hs]]
    apply eAt_congr <;> rv_eval [n0, n8, n16, hm12]
  have F₃ : DFrame w₀ t₃ (Within · G 38400) :=
    (I.frame.trans (DFrame.of_same hm12 _) fun _ h ↦ h).trans (DFrame.of_memFrame f₃) fun a h ↦ by
      addr_omega [h, hgp, h64]
  have g₃ (p : Nat) (hp : p < 64 * L + (z + 1)) :
      eAt t₃ (G + BitVec.ofNat 64 (24 * p)) = W (src (p / 64) (p % 64)) := by
    by_cases hpe : p = 64 * L + z
    · rw [hpe, enew, show (64 * L + z) / 64 = L by omega, show (64 * L + z) % 64 = z by omega]
    · rw [f₃.eAt (by addr_omega [hgp, h64, hp, hpe]) (by addr_omega [hgp, h64, hp]), ← I.g p (by omega)]
      unfold Rv64Verifier.eAt; rw [hm12, hm12, hm12]
  have x5₂ : t₂.getReg .x5 = BitVec.ofNat 64 (64 - z) := by rw [r₂ .x5 (by decide), I.x5]
  have e5 : t₂.getReg .x5 - 1 = BitVec.ofNat 64 (64 - (z + 1)) := by
    rw [x5₂, sub_one_ofNat (by omega) (by omega)]; congr 1
  have I' : TI w₀ t₃ G W L (z + 1) := {
    regs := fun r hr ↦ by
      rw [k₃ r (mem_of_mem hr _), r₂ r (mem_of_mem hr _), I.regs r hr]
    x5 := by rw [b8000fe90_x5 h₃, e5]
    x6 := by rw [b8000fe90_x6 h₃, r₂ .x6 (by decide), I.x6, ofNat_succ]; rfl
    x7 := by rw [b8000fe90_x7 h₃, x7₂, st24]; rfl
    x10 := by rw [k₃ .x10 (by decide), r₂ .x10 (by decide), I.x10]
    x14 := by rw [k₃ .x14 (by decide), r₂ .x14 (by decide), I.x14]
    x15 := by rw [k₃ .x15 (by decide), r₂ .x15 (by decide), I.x15]
    x16 := by rw [b8000fe90_x16 h₃, r₂ .x16 (by decide), I.x16, ofNat_succ]; rfl
    x17 := by rw [k₃ .x17 (by decide), r₂ .x17 (by decide), I.x17]
    frame := F₃
    g := g₃
    lt := hL
    le := by omega }
  have hr := hr₁.trans (hr₂.trans hr₃)
  by_cases hl : z + 1 < 64
  · refine ⟨t₃, hr, Or.inl ⟨I', Or.inl ⟨hl, b8000fe90_pc_taken h₃ ?_⟩⟩⟩
    rw [e5]; intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega
  · refine ⟨t₃, hr, Or.inl ⟨I', Or.inr ⟨by omega, b8000fe90_pc_not_taken h₃ ?_⟩⟩⟩
    rw [e5, show 64 - (z + 1) = 0 by omega]; rfl

theorem bit_loop' {w₀ : MachineState} {G P : Word} {W : Nat → E} {L : Nat} (C : TC w₀ G P W) :
    ∀ n z w, z + n = 64 → 0 < n → TI w₀ w G W L z → w.pc = 0x8000fe80 →
      ∃ v, Reaches Image.code w v ∧ ((TI w₀ v G W L 64 ∧ v.pc = 0x8000fecc) ∨ Dead Image.code v)
  | 0, _, _, _, h0, _, _ => absurd h0 (Nat.lt_irrefl 0)
  | n + 1, z, w, hn, _, I, hpc => by
    obtain ⟨v, hr, ⟨Q, ⟨hl, hpc'⟩ | ⟨he, hpc'⟩⟩ | hd⟩ := bit_step' C I (by omega) hpc
    · obtain ⟨t, hr', ht⟩ := bit_loop' C n (z + 1) v (by omega) (by omega) Q hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · rw [he] at Q
      exact ⟨v, hr, Or.inl ⟨Q, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

theorem ofNat_mul64 (n : Nat) : BitVec.ofNat 64 n * 64 = BitVec.ofNat 64 (64 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show (64 : Word).toNat = 64 from rfl]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

set_option maxHeartbeats 4000000 in
theorem lane_step' {w₀ w : MachineState} {G P : Word} {W : Nat → E} {L : Nat}
    (C : TC w₀ G P W) (Q : TO w₀ w G W L) (hpc : w.pc = 0x8000fe54) :
    ∃ v, Reaches Image.code w v ∧ ((TO w₀ v G W (L + 1) ∧ v.pc = 0x8000fe54) ∨
      (TX w₀ v G W ∧ v.pc = 0x8000fed8) ∨ Dead Image.code v) := by
  have hL := Q.lt
  have hgp := C.gp
  have x11w : w.getReg .x11 = 0xa00005b8 := by rw [Q.regs .x11 (by decide), C.x11]
  have x12w : w.getReg .x12 = 0xa0000550 := by rw [Q.regs .x12 (by decide), C.x12]
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches fe54A_spec hpc (by
    simp only [fe54A, rhoE]
    rv_eval [x11w, x12w, Q.x15]
    and_intros <;> interval_cases L <;> decide)
  have k₁ := fe54A_keeps h₁
  have hm₁ := fe54A_mem_same h₁
  have ro : RodataOk w := C.ro.dframe Q.frame fun a ha hw ↦ by addr_omega [ha, hw, hgp]
  have I₀ : TI w₀ t₁ G W L 0 := {
    regs := fun r hr ↦ by rw [k₁ r (mem_of_mem hr _), Q.regs r hr]
    x5 := fe54A_x5 h₁
    x6 := by rw [fe54A_x6 h₁, Q.x10]; rfl
    x7 := by rw [fe54A_x7 h₁, Q.x14]; congr 2; omega
    x10 := by rw [k₁ .x10 (by decide), Q.x10]
    x14 := by rw [k₁ .x14 (by decide), Q.x14]
    x15 := by rw [fe54A_x15 h₁, Q.x15, ofNat_succ]
    x16 := by rw [fe54A_x16 h₁, x12w, Q.x15, rho_word ro hL]; rfl
    x17 := by rw [fe54A_x17 h₁, x11w, Q.x15, pi_word ro hL, ofNat_mul64]
    frame := Q.frame.trans (DFrame.of_same hm₁ _) fun _ h ↦ h
    g := fun p hp ↦ by
      rw [← Q.g p (by omega)]; unfold Rv64Verifier.eAt; rw [hm₁, hm₁, hm₁]
    lt := hL
    le := by omega }
  obtain ⟨t₂, hr₂, ⟨I, hpc₂⟩ | hd⟩ := bit_loop' C 64 0 t₁ rfl (by decide) I₀ (fe54A_pc h₁)
  swap
  · exact ⟨t₂, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  obtain ⟨v, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000fecc_spec hpc₂ trivial
  have k₃ := b8000fecc_keeps h₃
  have hm₃ := b8000fecc_mem_same h₃
  have regs (r : Reg) (hr : r ∈ tRegs) : v.getReg r = w₀.getReg r := by
    rw [k₃ r (mem_of_mem hr _), I.regs r hr]
  have Fv : DFrame w₀ v (Within · G 38400) := I.frame.trans (DFrame.of_same hm₃ _) fun _ h ↦ h
  have gv (p : Nat) (hp : p < 64 * (L + 1)) :
      eAt v (G + BitVec.ofNat 64 (24 * p)) = W (src (p / 64) (p % 64)) := by
    rw [← I.g p (by omega)]; unfold Rv64Verifier.eAt; rw [hm₃, hm₃, hm₃]
  have x15₂ : t₂.getReg .x15 = BitVec.ofNat 64 (L + 1) := I.x15
  have x13₂ : t₂.getReg .x13 = 25 := by rw [I.regs .x13 (by decide), C.x13]
  have hr := hr₁.trans (hr₂.trans hr₃)
  by_cases hl : L + 1 < 25
  · refine ⟨v, hr, Or.inl ⟨{
      regs := regs
      x10 := by rw [b8000fecc_x10 h₃, I.x10]; apply BitVec.eq_of_toNat_eq; simp; omega
      x14 := by rw [b8000fecc_x14 h₃, I.x14]; apply BitVec.eq_of_toNat_eq; simp; omega
      x15 := by rw [k₃ .x15 (by decide), x15₂]
      frame := Fv
      g := gv
      lt := hl }, b8000fecc_pc_taken h₃ ?_⟩⟩
    rw [x15₂, x13₂]; intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, show (25 : Word).toNat = 25 from rfl] at this; omega
  · refine ⟨v, hr, Or.inr (Or.inl ⟨{
      regs := regs
      frame := Fv
      g := fun p hp ↦ gv p (by omega) }, b8000fecc_pc_not_taken h₃ ?_⟩)⟩
    rw [x15₂, x13₂, show L + 1 = 25 by omega]; rfl

theorem lane_loop' {w₀ : MachineState} {G P : Word} {W : Nat → E} (C : TC w₀ G P W) :
    ∀ n L w, L + n = 25 → TO w₀ w G W L → w.pc = 0x8000fe54 →
      ∃ v, Reaches Image.code w v ∧ ((TX w₀ v G W ∧ v.pc = 0x8000fed8) ∨ Dead Image.code v)
  | 0, L, w, hn, Q, _ => absurd Q.lt (by omega)
  | n + 1, L, w, hn, Q, hpc => by
    obtain ⟨v, hr, ⟨Q', hpc'⟩ | ⟨X, hpc'⟩ | hd⟩ := lane_step' C Q hpc
    · obtain ⟨t, hr', ht⟩ := lane_loop' C n (L + 1) v (by omega) Q' hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · exact ⟨v, hr, Or.inl ⟨X, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

end Rv64Verifier.Gkr.Layer
