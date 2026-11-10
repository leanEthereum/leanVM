import Rv64Verifier.Proofs.Walk.Rows
import Rv64Verifier.Proofs.Walk.Bits

/-!
# `walk`: `build_layout`'s head

From `0x80001238`: `log2_strict(bytecode.len())` (its power-of-two test, `Err` at `0x800012cc`),
`log_memory` in `16..=32` and each row count at most `2^32` (`Err` at `0x800012d0`), then
`trailing_zeros` by the de Bruijn table and `log_bytecode - 4 <= 32`, stored at `sp + 160`. These
are exactly the conditions of `buildLayoutRust`'s `if`; at `0x80001338` (`Head`) they hold.

The generated block at `0x8000128c` asks the table index to be 8-aligned; `f128cA` is that block
run again with byte loads at any address.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The table lookup at `0x8000128c` -/

def cfgW : Sym.Config := { noAlias := true, anyAlign := true }

/-- The table index, `(x15 & -x15) * [0xa0000020] >> 58`. -/
def idxE : Sym.E :=
  .bin .srl (.bin .mul (.bin .and (.reg .x15) (.bin .sub (.c 0) (.reg .x15))) (.ld (.c 0xa0000020)))
    (.c 0x3a)

def lookE : Sym.E := .bin .add idxE (.c 0xa0000028)

def f128cA : Sym.Expect :=
  { b8000128c with
    regs := b8000128c.regs.map fun p ↦ (p.1, if p.1 == .x11 then
      .bin (.ldx .bu) (.ld (.bin .and lookE (.c 0xfffffffffffffff8))) (.bin .and lookE (.c 7))
      else p.2)
    obl := [.valid ⟨some idxE, 0xa0000028⟩ 1] }

theorem f128cA_spec : Sym.BlockSpec Image.code 0x8000128c 11 (fun s ↦ Sym.Oblig.all s f128cA.obl)
    f128cA.Holds :=
  Sym.BlockSpec.of_expect (cfg := cfgW) (fuel := 11) (x := f128cA)
    (words := (Image.code.words.drop 1187).take 11) (by decide +kernel)
    (Sym.CodeAt.slice Image.code 1187 11 0x8000128c (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

theorem f128cA_x11 {s t : MachineState} (h : f128cA.Holds s t) :
    t.getReg .x11 = (extractByte (s.getMem
      ((((s.getReg .x15 &&& (0 - s.getReg .x15)) * s.getMem 0xa0000020) >>> 58) + 0xa0000028 &&&
        0xfffffffffffffff8))
      (((((s.getReg .x15 &&& (0 - s.getReg .x15)) * s.getMem 0xa0000020) >>> 58) + 0xa0000028 &&&
        7).toNat)).zeroExtend 64 :=
  h.reg_eq .x11 rfl (by rv_eval [lookE, idxE])

theorem f128cA_keeps {s t : MachineState} (h : f128cA.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17, .x18,
      .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg),
      t.getReg r = s.getReg r :=
  h.keeps rfl

theorem f128cA_pc {s t : MachineState} (h : f128cA.Holds s t) : t.pc = 0x80001328 :=
  h.pc_eq rfl

theorem f128cA_mem_same {s t : MachineState} (h : f128cA.Holds s t) (a : Word) :
    t.getMem a = s.getMem a :=
  h.mem_same rfl a

/-! ## Arithmetic of the checks -/

theorem lm_iff (x : Word) : (x - 16).toNat ≤ (16 : Word).toNat ↔ 16#64 ≤ x ∧ x ≤ 32#64 := by
  have h16 : (16 : Word).toNat = 16 := rfl
  have h16' : (16#64).toNat = 16 := rfl
  have h32' : (32#64).toNat = 32 := rfl
  have := x.isLt
  rw [BitVec.toNat_sub, h16, BitVec.le_def, BitVec.le_def, h16', h32']
  omega

theorem lb_iff {k : Nat} (hk : k < 64) :
    (BitVec.ofNat 64 k - 4).toNat ≤ (32 : Word).toNat ↔ 4 ≤ k ∧ k ≤ 36 := by
  have h4 : (4 : Word).toNat = 4 := rfl
  have h32 : (32 : Word).toNat = 32 := rfl
  rw [BitVec.toNat_sub, h4, h32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  omega

theorem lb_eq {k : Nat} (hk : 4 ≤ k ∧ k ≤ 36) : BitVec.ofNat 64 k - 4 = BitVec.ofNat 64 (k - 4) := by
  apply BitVec.eq_of_toNat_eq
  have h4 : (4 : Word).toNat = 4 := rfl
  rw [BitVec.toNat_sub, h4, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k - 4 < 2 ^ 64)]
  omega

theorem row_le {x : Word} (h : x.toNat ≤ (0x100000000 : Word).toNat) :
    decide (x ≤ 1#64 <<< LayoutMirror.maxTableLogRust) = true := by
  have e : (1#64 <<< LayoutMirror.maxTableLogRust).toNat = 0x100000000 := by decide
  have e' : (0x100000000 : Word).toNat = 0x100000000 := rfl
  rw [decide_eq_true_eq, BitVec.le_def, e]
  omega

theorem rows_le {a b c d e f : Word} (ha : a.toNat ≤ (0x100000000 : Word).toNat)
    (hb : b.toNat ≤ (0x100000000 : Word).toNat) (hc : c.toNat ≤ (0x100000000 : Word).toNat)
    (hd : d.toNat ≤ (0x100000000 : Word).toNat) (he : e.toNat ≤ (0x100000000 : Word).toNat)
    (hf : f.toNat ≤ (0x100000000 : Word).toNat) :
    [a, b, c, d, e, f].all (fun rows ↦ rows ≤ 1#64 <<< LayoutMirror.maxTableLogRust) = true := by
  simp only [List.all_cons, List.all_nil, row_le ha, row_le hb, row_le hc, row_le hd, row_le he,
    row_le hf, Bool.and_self]

/-! ## The checks -/

/-- The conditions of `buildLayoutRust`'s head: `log2_strict` gives `k`, and the `if` holds. -/
def HeadOk (s : MachineState) (A : List E) (k : Nat) : Prop :=
  log2StrictRust (BitVec.ofNat 64 (Proofs.Bytecode.readBytecode s (s.getReg .x11)).len) =
    some k ∧ (16#64 ≤ lmOf A ∧ lmOf A ≤ 32#64) ∧
    (rowsOf A).all (fun rows ↦ rows ≤ 1#64 <<< LayoutMirror.maxTableLogRust) = true ∧
    (LayoutMirror.busBitsRust ≤ k ∧ k ≤ 32 + LayoutMirror.busBitsRust)

/-- At `0x8000128c`: past the checks but `trailing_zeros`'; `u₀` the state at `0x80001238`. -/
structure Checked (s u₀ u : MachineState) (L : Word) : Prop where
  mem : ∀ a, u.getMem a = u₀.getMem a
  regs : ∀ r ∈ keepRegs, u.getReg r = u₀.getReg r
  x15 : u.getReg .x15 = L
  len : L = BitVec.ofNat 64 (Proofs.Bytecode.readBytecode s (s.getReg .x11)).len
  pow2 : L ≠ 0 ∧ L &&& (L - 1) = 0
  lm : 16#64 ≤ u₀.getReg .x25 ∧ u₀.getReg .x25 ≤ 32#64
  rows : [u₀.getReg .x16, u₀.getReg .x17, u₀.getReg .x13, u₀.getReg .x14, u₀.getReg .x11,
    u₀.getReg .x12].all (fun rows ↦ rows ≤ 1#64 <<< LayoutMirror.maxTableLogRust) = true

set_option maxRecDepth 8192 in
theorem headChecks {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} (hpre : WalkPre s) (hpc : u.pc = 0x80001238) (h : Rows OI s u A) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = 0x8000128c ∧ ∃ L, Checked s u t L) ∨ Done OI s t) := by
  have hI := h.inv
  have x23 := h.regs.x23
  have x24 := h.regs.x24
  have hbc := hpre.bytecode
  have hS := hbc.mem.self
  have hal := hbc.mem.align
  have lenW : u.getMem (u.getReg .x24 + 96) = s.getMem (s.getReg .x11 + 96) := by
    rw [x24]
    exact hI.word hbc.self (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS])
  have lenM : s.getMem (s.getReg .x11 + 96) =
      BitVec.ofNat 64 (Proofs.Bytecode.readBytecode s (s.getReg .x11)).len := by
    simp [Proofs.Bytecode.readBytecode]
  have err (t : MachineState) (hm : ∀ a, t.getMem a = u.getMem a)
      (hr : ∀ r ∈ keepRegs, t.getReg r = u.getReg r) (hp : t.pc = 0x800012d0) :
      ∃ t', Reaches Image.code t t' ∧ Done OI s t' :=
    err12d0 hpre (hI.same hm (hr .x2 (by decide))) (by rw [hr .x23 (by decide), x23]) hp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001238_spec hpc (by
    rv_eval [x24]
    exact Mapped.valid8 hS (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS, hal]))
  have m₁ (a : Word) : u₁.getMem a = u.getMem a := b80001238_mem_same h₁ a
  have k₁ (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x8, .x9, .x11, .x12, .x13, .x14, .x16, .x17, .x18,
      .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] := by decide) :
      u₁.getReg r = u.getReg r := b80001238_keeps h₁ r (mem_of_mem hr _)
  by_cases hc : (u.getMem (u.getReg .x24 + (96 : Word)) ^^^
      (u.getMem (u.getReg .x24 + (96 : Word)) - (1 : Word))).toNat ≤
      (u.getMem (u.getReg .x24 + (96 : Word)) - (1 : Word)).toNat
  · obtain ⟨t, hr, hd⟩ := err12cc (OI := OI) hpre (hI.same m₁ (k₁ .x2))
      (by rw [k₁ .x23, x23]) (b80001238_pc_taken h₁ hc)
    exact ⟨t, hr₁.trans hr, Or.inr hd⟩
  have hp2 := (pow2_word _).mp (Nat.lt_of_not_le hc)
  rw [lenW] at hp2
  have x15₁ : u₁.getReg .x15 = s.getMem (s.getReg .x11 + 96) := by rw [b80001238_x15 h₁, lenW]
  -- `log_memory`
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80001248_spec (b80001238_pc_not_taken h₁
    (Nat.lt_of_not_le hc)) (by rv_eval [])
  have m₂ (a : Word) : u₂.getMem a = u.getMem a := (b80001248_mem_same h₂ a).trans (m₁ a)
  have k₂ (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
      .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] := by decide) :
      u₂.getReg r = u₁.getReg r := b80001248_keeps h₂ r (mem_of_mem hr _)
  have kk₂ : ∀ r ∈ keepRegs, u₂.getReg r = u.getReg r := fun r hr ↦ by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  by_cases hlm : (16 : Word).toNat < (u₁.getReg .x25 - 16).toNat
  · obtain ⟨t, hr, hd⟩ := err u₂ m₂ kk₂ (b80001248_pc_taken h₂ hlm)
    exact ⟨t, hr₁.trans (hr₂.trans hr), Or.inr hd⟩
  have hlm' := (lm_iff _).mp (Nat.le_of_not_lt hlm)
  rw [k₁ .x25] at hlm'
  -- the row counts
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80001258_spec (b80001248_pc_not_taken h₂
    (Nat.le_of_not_lt hlm)) (by rv_eval [])
  have m₃ (a : Word) : u₃.getMem a = u.getMem a := (b80001258_mem_same h₃ a).trans (m₂ a)
  have k₃ (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
      .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] := by decide) :
      u₃.getReg r = u₂.getReg r := b80001258_keeps h₃ r (mem_of_mem hr _)
  have kk₃ : ∀ r ∈ keepRegs, u₃.getReg r = u.getReg r := fun r hr ↦ by
    rw [k₃ r (mem_of_mem hr _), kk₂ r hr]
  have r0 : u₂.getReg .x16 = u.getReg .x16 := by rw [k₂ .x16, k₁ .x16]
  by_cases c0 : (0x100000000 : Word).toNat < (u₂.getReg .x16).toNat
  · obtain ⟨t, hr, hd⟩ := err u₃ m₃ kk₃ (b80001258_pc_taken h₃ c0)
    exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), Or.inr hd⟩
  rw [r0] at c0
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80001264_spec (b80001258_pc_not_taken h₃
    (Nat.le_of_not_lt (by rwa [r0]))) (by rv_eval [])
  have m₄ (a : Word) : u₄.getMem a = u.getMem a := (b80001264_mem_same h₄ a).trans (m₃ a)
  have k₄ (r : Reg) (hr : r ∈ ([Reg.x1, .x2, .x5, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg) := by decide) :
      u₄.getReg r = u₃.getReg r := b80001264_keeps h₄ r (mem_of_mem hr _)
  have kk₄ : ∀ r ∈ keepRegs, u₄.getReg r = u.getReg r := fun r hr ↦ by rw [k₄ r (mem_of_mem hr _), kk₃ r hr]
  have x5₃ : u₃.getReg .x5 = 0x100000000 := b80001258_x5 h₃
  have r1 : u₃.getReg .x17 = u.getReg .x17 := by rw [k₃ .x17, k₂ .x17, k₁ .x17]
  by_cases c1 : (u₃.getReg .x5).toNat < (u₃.getReg .x17).toNat
  · obtain ⟨t, hr, hd⟩ := err u₄ m₄ kk₄ (b80001264_pc_taken h₄ c1)
    exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr))), Or.inr hd⟩
  have pc₄ := b80001264_pc_not_taken h₄ (Nat.le_of_not_lt c1)
  rw [x5₃, r1] at c1
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80001268_spec pc₄ (by rv_eval [])
  have m₅ (a : Word) : u₅.getMem a = u.getMem a := (b80001268_mem_same h₅ a).trans (m₄ a)
  have k₅ (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x17,
      .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] := by decide) :
      u₅.getReg r = u₄.getReg r := b80001268_keeps h₅ r (mem_of_mem hr _)
  have kk₅ : ∀ r ∈ keepRegs, u₅.getReg r = u.getReg r := fun r hr ↦ by
    rw [k₅ r (mem_of_mem hr _), kk₄ r hr]
  have r2 : u₄.getReg .x13 = u.getReg .x13 := by rw [k₄ .x13, k₃ .x13, k₂ .x13, k₁ .x13]
  by_cases c2 : (0x100000000 : Word).toNat < (u₄.getReg .x13).toNat
  · obtain ⟨t, hr, hd⟩ := err u₅ m₅ kk₅ (b80001268_pc_taken h₅ c2)
    exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr)))), Or.inr hd⟩
  have pc₅ := b80001268_pc_not_taken h₅ (Nat.le_of_not_lt c2)
  rw [r2] at c2
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80001274_spec pc₅ (by rv_eval [])
  have m₆ (a : Word) : u₆.getMem a = u.getMem a := (b80001274_mem_same h₆ a).trans (m₅ a)
  have k₆ (r : Reg) (hr : r ∈ ([Reg.x1, .x2, .x5, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg) := by decide) :
      u₆.getReg r = u₅.getReg r := b80001274_keeps h₆ r (mem_of_mem hr _)
  have kk₆ : ∀ r ∈ keepRegs, u₆.getReg r = u.getReg r := fun r hr ↦ by rw [k₆ r (mem_of_mem hr _), kk₅ r hr]
  have x16₅ : u₅.getReg .x16 = 0x100000000 := b80001268_x16 h₅
  have r3 : u₅.getReg .x14 = u.getReg .x14 := by rw [k₅ .x14, k₄ .x14, k₃ .x14, k₂ .x14, k₁ .x14]
  by_cases c3 : (u₅.getReg .x16).toNat < (u₅.getReg .x14).toNat
  · obtain ⟨t, hr, hd⟩ := err u₆ m₆ kk₆ (b80001274_pc_taken h₆ c3)
    exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hr))))), Or.inr hd⟩
  have pc₆ := b80001274_pc_not_taken h₆ (Nat.le_of_not_lt c3)
  rw [x16₅, r3] at c3
  obtain ⟨u₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80001278_spec pc₆ (by rv_eval [])
  have m₇ (a : Word) : u₇.getMem a = u.getMem a := (b80001278_mem_same h₇ a).trans (m₆ a)
  have k₇ (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x8, .x9, .x11, .x12, .x14, .x15, .x16, .x17,
      .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] := by decide) :
      u₇.getReg r = u₆.getReg r := b80001278_keeps h₇ r (mem_of_mem hr _)
  have kk₇ : ∀ r ∈ keepRegs, u₇.getReg r = u.getReg r := fun r hr ↦ by
    rw [k₇ r (mem_of_mem hr _), kk₆ r hr]
  have r4 : u₆.getReg .x11 = u.getReg .x11 := by
    rw [k₆ .x11, k₅ .x11, k₄ .x11, k₃ .x11, k₂ .x11, k₁ .x11]
  have hr₁₇ := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hr₇)))))
  by_cases c4 : (0x100000000 : Word).toNat < (u₆.getReg .x11).toNat
  · obtain ⟨t, hr, hd⟩ := err u₇ m₇ kk₇ (b80001278_pc_taken h₇ c4)
    exact ⟨t, hr₁₇.trans hr, Or.inr hd⟩
  have pc₇ := b80001278_pc_not_taken h₇ (Nat.le_of_not_lt c4)
  rw [r4] at c4
  obtain ⟨u₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80001284_spec pc₇ (by rv_eval [])
  have m₈ (a : Word) : u₈.getMem a = u.getMem a := (b80001284_mem_same h₈ a).trans (m₇ a)
  have k₈ (r : Reg) (hr : r ∈ ([Reg.x1, .x2, .x5, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg) := by decide) :
      u₈.getReg r = u₇.getReg r := b80001284_keeps h₈ r (mem_of_mem hr _)
  have kk₈ : ∀ r ∈ keepRegs, u₈.getReg r = u.getReg r := fun r hr ↦ by rw [k₈ r (mem_of_mem hr _), kk₇ r hr]
  have x13₇ : u₇.getReg .x13 = 0x100000000 := b80001278_x13 h₇
  have r5 : u₇.getReg .x12 = u.getReg .x12 := by
    rw [k₇ .x12, k₆ .x12, k₅ .x12, k₄ .x12, k₃ .x12, k₂ .x12, k₁ .x12]
  by_cases c5 : (u₇.getReg .x13).toNat < (u₇.getReg .x12).toNat
  · obtain ⟨t, hr, hd⟩ := err u₈ m₈ kk₈ (b80001284_pc_taken h₈ c5)
    exact ⟨t, hr₁₇.trans (hr₈.trans hr), Or.inr hd⟩
  have pc₈ := b80001284_pc_not_taken h₈ (Nat.le_of_not_lt c5)
  rw [x13₇, r5] at c5
  -- `bytecode.len() != 0`
  obtain ⟨u₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b80001288_spec pc₈ (by rv_eval [])
  have x15₈ : u₈.getReg .x15 = s.getMem (s.getReg .x11 + 96) := by
    rw [k₈ .x15, k₇ .x15, k₆ .x15, k₅ .x15, k₄ .x15, k₃ .x15, k₂ .x15, x15₁]
  refine ⟨u₉, hr₁₇.trans (hr₈.trans hr₉), Or.inl ⟨b80001288_pc_not_taken h₉ (by rw [x15₈]; exact hp2.1),
    _, {
      mem := fun a ↦ (b80001288_mem_same h₉ a).trans (m₈ a)
      regs := fun r hr ↦ by rw [b80001288_keeps h₉ r (mem_of_mem hr _), kk₈ r hr]
      x15 := by rw [b80001288_keeps h₉ .x15 (by decide), x15₈]
      len := lenM
      pow2 := hp2
      lm := hlm'
      rows := rows_le (Nat.le_of_not_lt c0) (Nat.le_of_not_lt c1) (Nat.le_of_not_lt c2)
        (Nat.le_of_not_lt c3) (Nat.le_of_not_lt c4) (Nat.le_of_not_lt c5) }⟩⟩

/-! ## `trailing_zeros` and `log_bytecode` -/

theorem shift58_lt (y : Word) : (y >>> 58).toNat < 64 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := y.isLt
  omega

theorem lookup_valid (y : Word) : Sym.validAccess 1 ((y >>> 58) + 0xa0000028) = true := by
  rw [BitVec.add_comm]
  exact valid1 (a := 0xa0000028) (n := 64) (Or.inr ⟨by decide, by decide⟩) _ (shift58_lt y)

/-- A step writing `n` bytes of the frame apart from the transcript keeps what it stands for. -/
theorem TranscriptAt.memFrame {s u v : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) {lo : Word} {n : Nat} (hl : InFrame s lo n)
    (hap : Apart lo n (tp s) 368) (hf : MemFrame u v lo n) {T : TState}
    (hT : TranscriptAt u (tp s) T) : TranscriptAt v (tp s) T := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [InFrame] at hl
  have pRO := hpre.proofRO.2.1
  have sRO := hpre.streamRO.2.1
  rw [stackLo_eq, stack_eq] at pRO sRO
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  rw [tp] at hap
  refine (DFrame.of_memFrame hf).transcriptAt hT (tok hpre h hptr) ?_ ?_ ?_ ?_
  · intro y hy hw; rw [tp] at hy; addr_omega [hap, hy, hw, hl, hb1]
  · rw [e0]; intro y hy hw; addr_omega [pRO, hy, hw, hl, hb1]
  · rw [e1, e2]; intro y hy hw; addr_omega [sRO, hy, hw, hl, hb1]
  · intro y hy hw; rw [tp] at hy; addr_omega [hap, hy, hw, hl, hb1]

/-- At `0x80001338`: `build_layout`'s head passed (`HeadOk`), `log_bytecode - 4` at `sp + 160`,
before `table_log_heights`' allocation. -/
structure Head (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) : Prop where
  inv : Inv s u
  regs : Regs s u
  proofPtr : u.getMem (tp s) = s.getReg .x13
  checked : byteAt u (tp s + 360) = 1
  x26 : u.getReg .x26 = s.getReg .x2 - 512
  x8 : u.getReg .x8 = rateOf A
  x25 : u.getReg .x25 = lmOf A
  buf : (u.getReg .x18).toNat % 8 = 0 ∧ 0x20000000 ≤ (u.getReg .x18).toNat ∧
    (u.getReg .x18).toNat + 48 ≤ heapNext u
  rows : [u.getMem (u.getReg .x18), u.getMem (u.getReg .x18 + 8), u.getMem (u.getReg .x18 + 16),
    u.getMem (u.getReg .x18 + 24), u.getMem (u.getReg .x18 + 32), u.getMem (u.getReg .x18 + 40)] =
    rowsOf A
  lb : u.getMem (s.getReg .x2 - 2496) = BitVec.ofNat 64 (k - 4)
  ok : HeadOk s A k
  rate : 1#64 ≤ rateOf A ∧ rateOf A ≤ 4#64
  tracks : Tracks OI s u (afterRate s A)

set_option maxRecDepth 8192 in
theorem headCtz {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ u : MachineState}
    {A : List E} {L : Word} (hpre : WalkPre s) (h₀ : Rows OI s u₀ A) (hpc : u.pc = 0x8000128c)
    (h : Checked s u₀ u L) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001338 ∧ ∃ k, Head OI s t A k) ∨ Done OI s t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have Iu : Inv s u := h₀.inv.same h.mem (h.regs .x2 (by decide))
  have ro : RodataOk u := Iu.rodata hpre
  obtain ⟨hLk, hk64⟩ := pow2_ctz h.pow2.1 h.pow2.2
  have hlog := log2StrictRust_of h.pow2.1 h.pow2.2
  generalize hkd : L.ctz.toNat = k at hLk hk64 hlog
  have hL : L = BitVec.ofNat 64 (2 ^ k) := by
    apply BitVec.eq_of_toNat_eq
    rw [hLk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk64)]
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches f128cA_spec hpc (by
    rv_eval [idxE]
    exact lookup_valid _)
  have x11₁ : u₁.getReg .x11 = BitVec.ofNat 64 k := by
    rw [f128cA_x11 h₁, h.x15, db_const ro, hL]
    exact ctz_lookup ro hk64
  have m₁ (a : Word) : u₁.getMem a = u.getMem a := f128cA_mem_same h₁ a
  have Iu₁ : Inv s u₁ := Iu.same m₁ (f128cA_keeps h₁ .x2 (by decide))
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := Iu₁.sp
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80001328_spec (f128cA_pc h₁) (by
    rv_eval [sp₁]
    valid_access hval [hb1])
  have e160 : u₁.getReg .x2 + 160 = s.getReg .x2 - 2496 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hf : MemFrame u₁ u₂ (s.getReg .x2 - 2496) 8 := by
    rw [← e160]; exact b80001328_frame h₂ (by rw [sp₁]; addr_omega [hb1])
  have hl : InFrame s (s.getReg .x2 - 2496) 8 := inFrame hpre (k := 2496) (n := 8) (by omega) (by omega)
  have st : Step s u₁ u₂ (s.getReg .x2 - 2496) 8 :=
    Step.ofMemFrame hpre Iu₁.heap hl hf (b80001328_keeps h₂ .x2 (by decide))
  have Iu₂ : Inv s u₂ := Iu₁.after hpre hl st
  have k₂ (r : Reg) (hr : r ∈ keepRegs) : u₂.getReg r = u₀.getReg r := by
    rw [b80001328_keeps h₂ r (mem_of_mem hr _), f128cA_keeps h₁ r (mem_of_mem hr _), h.regs r hr]
  have x23 : u₂.getReg .x23 = s.getReg .x10 := by rw [k₂ .x23 (by decide), h₀.regs.x23]
  by_cases hc : (32 : Word).toNat < (u₁.getReg .x11 - 4).toNat
  · obtain ⟨t, hr, hd⟩ := err12d0 (OI := OI) hpre Iu₂ x23 (b80001328_pc_taken h₂ hc)
    exact ⟨t, hr₁.trans (hr₂.trans hr), Or.inr hd⟩
  have hk := (lb_iff hk64).mp (by rw [← x11₁]; exact Nat.le_of_not_lt hc)
  have keepF (x : Word) (hx : ¬ Within x (s.getReg .x2 - 2496) 8) : u₂.getMem x = u₀.getMem x := by
    rw [hf x hx, m₁, h.mem]
  have ptr₀ := h₀.proofPtr
  have hm₀ : ∀ a, u.getMem a = u₀.getMem a := h.mem
  have hu0 := h₀.buf
  have hh₀ := h₀.inv.heap.hi
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapNext, heapEnd] at hu0 hh₀ hab
  have keepH (x : Word) (hx : x.toNat + 8 ≤ (u₀.getReg .x18).toNat + 48) :
      u₂.getMem x = u₀.getMem x :=
    keepF x (by simp only [Within]; addr_omega [hx, hu0, hh₀, hab, hb1])
  have x18 : u₂.getReg .x18 = u₀.getReg .x18 := k₂ .x18 (by decide)
  have hnx : u₂.getMem nextAddr = u₀.getMem nextAddr :=
    keepF _ (by simp only [Within]; addr_omega [hb1, hab])
  refine ⟨u₂, hr₁.trans hr₂, Or.inl ⟨b80001328_pc_not_taken h₂ (Nat.le_of_not_lt hc),
    k, {
      inv := Iu₂
      regs := h₀.regs.keep fun r hr ↦ k₂ r (mem_of_mem hr _)
      proofPtr := by rw [keepF _ (by rw [tp]; simp only [Within]; addr_omega [hb1])]; exact ptr₀
      checked := by
        have ha : (tp s + 360).toNat % 8 = 0 := by rw [tp]; addr_omega [hb1, hb3]
        rw [byteAt_congr ha (keepF _ (by rw [tp]; simp only [Within]; addr_omega [hb1]))]
        exact h₀.checked
      x26 := by rw [k₂ .x26 (by decide), h₀.x26]
      x8 := by rw [k₂ .x8 (by decide), h₀.x8]
      x25 := by rw [k₂ .x25 (by decide), h₀.x25]
      buf := by rw [x18]; simp only [heapNext, hnx]; exact h₀.buf
      rows := by
        rw [x18, keepH _ (by addr_omega [hu0]), keepH _ (by addr_omega [hu0]),
          keepH _ (by addr_omega [hu0]), keepH _ (by addr_omega [hu0]),
          keepH _ (by addr_omega [hu0]), keepH _ (by addr_omega [hu0])]
        exact h₀.rows
      lb := by
        rw [← e160, b80001328_m_x2_160 h₂, x11₁]
        exact lb_eq hk
      ok := ⟨by rw [← h.len]; exact hlog,
        by rw [← h₀.x25]; exact h.lm, by rw [← h₀.rowRegs]; exact h.rows, hk⟩
      rate := h₀.rate
      tracks := ((h₀.tracks.keep fun T hT ↦ TranscriptAt.same hpre h₀.inv ptr₀ hm₀ hT).keep
        fun T hT ↦ TranscriptAt.same hpre Iu (by rw [hm₀]; exact ptr₀) m₁ hT).keep
        fun T hT ↦ TranscriptAt.memFrame hpre Iu₁ (by rw [m₁, hm₀]; exact ptr₀) hl
          (by rw [tp]; addr_omega [hb1]) hf hT }⟩⟩

/-- **From `0x80001238` past `build_layout`'s head** (`0x80001338`), or `Err`. -/
theorem headStage {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} (hpre : WalkPre s) (hpc : u.pc = 0x80001238) (h : Rows OI s u A) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001338 ∧ ∃ k, Head OI s t A k) ∨ Done OI s t) := by
  obtain ⟨v, hr₁, ⟨pc₁, L, hc⟩ | hd⟩ := headChecks hpre hpc h
  · obtain ⟨t, hr₂, ht⟩ := headCtz hpre h pc₁ hc
    exact ⟨t, hr₁.trans hr₂, ht⟩
  · exact ⟨v, hr₁, Or.inr hd⟩

end Rv64Verifier.Proofs.Walk
