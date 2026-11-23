module

public import NativeRustcVmArm.Whir.WhirLevels.Final

/-!
# `whir_levels`: the stages of a level

The blocks of a level `k ≥ 1`, as rustc unrolled them, differ only in their offsets; each stage
is stated for any block whose literal end state passes a check (`FoldOk`, `WOk`, `NextOk`,
`keepR`), proved by `decide` on the literal states:

- `fold_stage`: the fold rounds' call block (reading level `k`'s fold), the call, the `None` test:
  `Mid k`, or the epilogue returning `None`.
- `w_stage`: the block computing `μ` (from the state's `α` count) and comparing the level.
- `next_stage`: `next_level`'s call block (reading level `k + 1`'s fold and rate exponent), the
  call, then (`cmp_stage`) the comparison of the next level with the count and the `None` test:
  `Head (k + 1)`, or the epilogue returning `None`.
- `jump_final`: the block setting X23 to the last level and jumping to the tail call.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Layout.Ladder
open NativeRustcVmArm.Vm.WhirLevels

@[expose] public section

/-- The registers `Regs` names, kept as `S₀`'s. -/
def keepR (S₀ S : SState) : Bool :=
  [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X27, .X28, .X29].all fun r ↦
    (S₀.reg r).isSome && S.reg r == S₀.reg r

/-- `μ`'s term: `logN` (X25) minus the `α` count at X19 + 16, saturating. -/
def muSym : Sym :=
  .ite (.cmp .ult .W64 (.reg .X25) (.load 0 16 8)) (.lit 0) (.bin .sub .W64 (.reg .X25) (.load 0 16 8))

/-- The fold rounds' call block of level `k` (from `lvS n`): `fold_rounds(t, levels[k].fold, w,
w + 61152)`, X26 kept below the sixth level, the sixth level's address there. -/
def FoldOk (k n : Nat) (S : SState) : Bool :=
  S.mem.isEmpty && S.sp == .sp && keepR (lvS n) S &&
    S.reg .X26 == (if k < 5 then some (.reg .X26) else some (.ptr 0 120)) &&
    S.reg .X0 == some (.reg .X21) && S.reg .X1 == some (.load 0 (24 * k) 8) &&
    S.reg .X2 == some (.reg .X19) && S.reg .X3 == some (.bin .add .W64 (.reg .X19) (.reg .X28))

/-- The block computing `μ` into X5. -/
def WOk (S : SState) : Bool :=
  S.mem.isEmpty && S.sp == .sp && keepR wS S && S.reg .X26 == some (.reg .X26) &&
    S.reg .X5 == some muSym

/-- `next_level`'s call block at level `k` (from `lvS n`): `next_level(t, k, levels + 24 k,
levels[k + 1].fold, levels[k + 1].logInvRate, μ, w)`, the level's address `v2`. -/
def NextOk (k n : Nat) (v2 : Sym) (S : SState) : Bool :=
  S.mem.isEmpty && S.sp == .sp && keepR (lvS n) S && S.reg .X26 == some (.reg .X26) &&
    S.reg .X0 == some (.reg .X21) && S.reg .X1 == some (.lit k) && S.reg .X2 == some v2 &&
    S.reg .X3 == some (.load 0 (24 * (k + 1)) 8) &&
    S.reg .X4 == some (.load 0 (24 * (k + 1) + 8) 8) && S.reg .X5 == some (.reg .X5) &&
    S.reg .X6 == some (.reg .X19)

/-- A block of registers only keeping `Regs`' registers, X26 and X0. -/
def RegsOk (S : SState) : Bool :=
  S.mem.isEmpty && S.sp == .sp && keepR regsS S && S.reg .X26 == some (.reg .X26) &&
    S.reg .X0 == some (.reg .X0)

end

public section

section
variable [Labels] {env : Env} {S₀ S : SState} {m m' : MachineData}

theorem keepR_reg (hm₀ : Match env S₀ m) (hm : Match env S m') (h : keepR S₀ S = true)
    {r : XReg} (hr : r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X27, .X28, .X29]) :
    m'.regs.getXReg r = m.regs.getXReg r := by
  simp only [keepR, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists]
    at h
  obtain ⟨⟨v, hv⟩, hS⟩ := h r hr
  exact Match.reg_eq hm₀ hm hv (hS.trans hv)

omit [Labels] in
theorem Regs.congr' {m0 : MachineData} {len : Nat} {st st' : MachineData} (h : Regs m0 len st)
    (he : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X27, .X28, .X29],
      st'.regs.getXReg r = st.regs.getXReg r) : Regs m0 len st' where
  x19 := (he .X19 (by simp)).trans h.x19
  x20 := (he .X20 (by simp)).trans h.x20
  x21 := (he .X21 (by simp)).trans h.x21
  x22 := (he .X22 (by simp)).trans h.x22
  x23 := (he .X23 (by simp)).trans h.x23
  x24 := by rw [he .X24 (by simp)]; exact h.x24
  x25 := (he .X25 (by simp)).trans h.x25
  x27 := by rw [he .X27 (by simp)]; exact h.x27
  x28 := by rw [he .X28 (by simp)]; exact h.x28

theorem Regs.ofKeep {m0 : MachineData} {len : Nat} (h : Regs m0 len m) (hm₀ : Match env S₀ m)
    (hm : Match env S m') (hk : keepR S₀ S = true) : Regs m0 len m' :=
  h.congr' fun _ hr ↦ keepR_reg hm₀ hm hk hr

end

/-! ## Values -/

theorem eval_cmp_eq [Labels] (env : Env) (r : XReg) {c : Nat} (hc : c < 2 ^ 64) :
    (SBool.cmp .eq .W64 (.reg r) (.lit c)).eval env = decide ((env.regs r).toNat = c) := by
  sym_simp
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem eval_muSym [Labels] (env : Env) :
    (muSym.eval env).toNat = (env.regs .X25).toNat - (env.load 0 16 8).toNat := by
  unfold muSym
  sym_simp
  split
  · rename_i h
    rw [BitVec.ult_iff_lt, BitVec.lt_def] at h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  · rename_i h
    rw [BitVec.ult_iff_lt, BitVec.lt_def] at h
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]

theorem eval_add_regs [Labels] (env : Env) (r r' : XReg) :
    (Sym.bin .add .W64 (.reg r) (.reg r')).eval env = env.regs r + env.regs r' := by
  sym_simp

theorem eval_ptr0 [Labels] {m : MachineData} {x : BitVec 64} {n : Nat} (c : Nat) :
    (Sym.ptr 0 c).eval (Env.ofMachine m [(x, n)]) = x + BitVec.ofNat 64 c := by
  simp only [Sym.eval, Env.base_ofMachine_eq]
  congr 1

/-- A word at the region's offset, as the environment loads it. -/
theorem load_at [Labels] {m : MachineData} {x : BitVec 64} {n o : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt m.dmem (x + BitVec.ofNat 64 o) v) :
    (Env.ofMachine m [(x, n)]).load 0 o 8 = v.toBitVec :=
  load_word h

section
variable [Labels] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat}

/-- Level `k`'s three words, as the environment of the levels' first `n` bytes loads them. -/
theorem load_level (c : Ctx a s0 levels ba b claim m0 rate) {st : MachineData} (hf : WFr m0 st)
    {k n : Nat} (hk : k < levels.length) :
    ((Env.ofMachine st [(lvA m0, n)]).load 0 (24 * k) 8).toNat = foldAt k ∧
      ((Env.ofMachine st [(lvA m0, n)]).load 0 (24 * k + 8) 8).toNat = rate + 3 * k := by
  obtain ⟨h1, h2, -, hw⟩ := c.levelAt hf hk
  have hw0 := hw.getElem (i := 0) (by simp)
  have hw1 := hw.getElem (i := 1) (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.mul_one,
    NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_zero, levelBytes] at hw0 hw1
  refine ⟨?_, ?_⟩
  · rw [load_at (o := 24 * k) hw0]
    exact natCast_toUInt64 h1
  · rw [load_at (o := 24 * k + 8) hw1]
    exact natCast_toUInt64 h2
where
  natCast_toUInt64 {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toBitVec.toNat = x := by
    show x.toUInt64.toNat = x
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt h

end

end

end NativeRustcVmArm.Whir.WhirLevels
