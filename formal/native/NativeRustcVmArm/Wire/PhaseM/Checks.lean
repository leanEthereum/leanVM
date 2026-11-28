module

public import NativeRustcVmArm.Code.Vm.PhaseM.Names
public import NativeRustcVmArm.Wire.PhaseM.Sort

/-!
# `phase_m`: the size checks and the rows

`checks_run`: from the size checks (`Chk`), the height, the leaf width, the row width and the last
position checked (`b20` to `b23`), the rows read by `rd_rows` into the leaves at the working area's
byte 352512 (`b24`), the rows' check (`b25`), to the hashing of the leaves (`Rows`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The leaves of the rows. -/
abbrev leavesOf (lw : Nat) (rows : List (List K)) : List (List K) :=
  rows.map fun r ↦ paddedLeaf r lw

/-- The first level's nodes. -/
abbrev nodes0 (qs : List Nat) (lw : Nat) (rows : List (List K)) : List (Nat × Digest) :=
  (sortD qs).zip ((leavesOf lw rows).map fun leaf ↦ keccak256 (leaf.flatMap K.toBytes))

/-- The phase from the climb on. -/
def climbFin (B : List UInt8) (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c : Nat) :
    Option (PhaseOut × Nat) :=
  match climbM B height (nodes0 qs lw rows) c with
  | none => none
  | some (sibs, c) =>
    some (⟨height, lw, qs.map (openingAt (sortD qs) (leavesOf lw rows) sibs height)⟩, c)

/-- **After the rows** (`b26`). -/
structure Rows [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 : Nat)
    (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b26Offset)
  base : Base m0 st.data
  model : phaseM B c = climbFin B qs height lw rows c6
  len : qs.length = count
  cnt0 : 0 < count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  h32 : height ≤ 32
  lw64 : lw ≤ 64
  ps0 : 0 < (sortD qs).length
  ps256 : (sortD qs).length ≤ 256
  rlen : rows.length = (sortD qs).length
  rw : ∀ r ∈ rows, r.length ≤ lw
  x21 : (st.data.regs.getXReg .X21).toNat = count
  x24 : (st.data.regs.getXReg .X24).toNat = height
  x26 : (st.data.regs.getXReg .X26).toNat = (sortD qs).length
  f56 : FW m0 st.data.dmem 56 lw.toUInt64
  f48 : FW m0 st.data.dmem 48 (UInt64.ofBitVec (wa m0 2048))
  f40 : FW m0 st.data.dmem 40 (UInt64.ofBitVec (wa m0 352512))
  qsW : WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  psW : WordsAt st.data.dmem (wa m0 2048) ((sortD qs).map Nat.toUInt64)
  lvW : LeavesAt st.data.dmem (wa m0 352512) (leavesOf lw rows)
  rd : ReaderAt st.data.dmem (rdr m0) bp B c6

end

public section

theorem gt_eval [Labels] (env : Sym.Env) (x y : Sym) :
    (SBool.and (.not (.cmp .ult .W64 x y)) (.not (.cmp .eq .W64 x y))).eval env =
      decide ((y.eval env).toNat < (x.eval env).toNat) := by
  simp only [SBool.eval]
  rw [ult_apply, eq_apply]
  by_cases h : (y.eval env).toNat < (x.eval env).toNat
  · rw [decide_eq_true h, decide_eq_false (by omega), decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h]
    by_cases h' : (x.eval env).toNat < (y.eval env).toNat
    · rw [decide_eq_true h']; rfl
    · rw [decide_eq_false h', decide_eq_true (by omega)]; rfl

theorem lsrv_apply (x y : BitVec 64) (hy : y.toNat < 64) :
    (BinOp.apply .lsrv .W64 x y).toNat = x.toNat / 2 ^ y.toNat := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
  rw [show RegWidth.W64.bits = 64 from rfl, Nat.mod_eq_of_lt hy]
  show (x >>> y.toNat).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The rows' check after `rd_rows`. -/
theorem rows_cond [Labels] (env : Sym.Env) {x0 : BitVec 64} (h0 : env.regs .X0 = x0)
    (hx : x0 = 0 ∨ x0 = 1 ∨ x0 = 2) :
    (SBool.bit .W32 (.ite (.not (.cmp .eq .W32 (.bin .and .W32 (.bin .and .W32 (.reg .X0)
        (.lit 255)) (.lit 255)) (.lit 2))) (.bin .and .W32 (.ite (.cmp .eq .W64 (.reg .X28)
        (.lit 0)) (.lit 0) (.lit 1)) (.bin .and .W32 (.reg .X0) (.lit 255))) (.lit 1)) 0).eval env =
      decide (x0 = 2 ∨ ((env.regs .X28).toNat ≠ 0 ∧ x0 = 1)) := by
  have hz' : CmpOp.apply .eq .W64 (env.regs .X28) (BitVec.ofNat 64 0) =
      decide ((env.regs .X28).toNat = 0) := by rw [eq_apply]; simp
  simp only [SBool.eval, Sym.eval, h0, hz']
  by_cases hz : (env.regs .X28).toNat = 0
  · have hr : decide (x0 = 2 ∨ ((env.regs .X28).toNat ≠ 0 ∧ x0 = 1)) = decide (x0 = 2) := by
      simp [hz]
    rw [hr]
    simp only [hz, decide_true, ↓reduceIte]
    rcases hx with rfl | rfl | rfl <;> decide
  · have hr : decide (x0 = 2 ∨ ((env.regs .X28).toNat ≠ 0 ∧ x0 = 1)) =
        decide (x0 = 2 ∨ x0 = 1) := by
      simp [hz]
    rw [hr]
    simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte]
    rcases hx with rfl | rfl | rfl <;> decide

theorem tail_none_of {B : List UInt8} {qs : List Nat} {height lw rw c : Nat}
    (h : ¬(height ≤ wireMaxHeight ∧ lw ≤ wireMaxLeafWords ∧ rw ≤ lw ∧ sortD qs ≠ [] ∧
      (sortD qs).getLastD 0 < 2 ^ height)) : tail B qs height lw rw c = none := by
  unfold tail
  split
  · rfl
  · contradiction

theorem tail_ok {B : List UInt8} {qs : List Nat} {height lw rw c : Nat}
    (h : height ≤ wireMaxHeight ∧ lw ≤ wireMaxLeafWords ∧ rw ≤ lw ∧ sortD qs ≠ [] ∧
      (sortD qs).getLastD 0 < 2 ^ height) : tail B qs height lw rw c =
    match rdRows B rw (sortD qs).length c with
    | none => none
    | some (rows, c) =>
      if 0 < rw ∧ ∀ r ∈ rows, r.getD 0 0 = 0 then none else climbFin B qs height lw rows c := by
  unfold tail climbFin
  split
  · contradiction
  · rfl

theorem getLastD_eq {l : List Nat} (h : 0 < l.length) :
    l.getLastD 0 = l[l.length - 1] := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  rfl

theorem kept_but8 : ∀ r : XReg, r ≠ .X8 → frS.reg r = some (.reg r) := by
  intro r _; cases r <;> rfl

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **A check** without writes, X8 its only register changed, to `None` when `y < x`. -/
theorem chk_step (hp : Placed code k) (G : Geo m0 bp B) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) (hne : b ≠ []) {S' : SState} {x y : Sym}
    (hx : exec b frS = some (S', .cond (SBool.and (.not (.cmp .ult .W64 x y))
      (.not (.cmp .eq .W64 x y))) NativeRustcVmArm.Vm.PhaseM.label_12)) (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    (hk : ∀ r : XReg, r ≠ .X8 → S'.reg r = some (.reg r))
    {st : MachineState} {R : MachineState → Prop} (hb0 : Base m0 st.data)
    (hpc : st.pc = Host.addrOf (k + j)) {a v : Nat}
    (hxv : (x.eval (frEnv m0 st.data)).toNat = a) (hyv : (y.eval (frEnv m0 st.data)).toNat = v)
    (cont : ∀ st', Base m0 st'.data → st'.data.dmem = st.data.dmem →
      (∀ r : XReg, r ≠ .X8 → st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      st'.pc = (if v < a then Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b18Offset) else Host.addrOf (k + j + b.length)) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  refine blk hp hb hne hx hmem hsp G.st hb0.fr hpc fun s1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have hm := frEnv_match G.st hb0.fr
  have r1 : ∀ r : XReg, r ≠ .X8 → s1.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ Match.reg_eq hm hm1 (kept_but8 r hr) (hk r hr)
  refine cont s1 (hb0.of_regs hfr1 fun r hr ↦ r1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hd1 r1 ?_
  simp only [PcOk, gt_eval, hxv, hyv] at hpc1
  rw [hpc1]
  by_cases h : v < a
  · simp only [h, decide_true, ↓reduceIte]; exact hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]

end

end NativeRustcVmArm.Wire.PhaseM
