module

public import NativeRustcVmX64.Tables.TableTerms.Read

/-!
# `table_terms`: the middle of an iteration (x86-64)

`Cm`: what holds from table `i`'s evaluations read until its sum is added (the body, the frame's
words, the iteration's outputs, the model's fold so far). The two dot products of the step
(`dotC`, `dotF`). Values the blocks compute: a word plus a literal, `x << 4`, the conditional
moves (`eval_*`); a callee's slice of an input or of the frame (`slice_*`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- The constraints' dot product of table `i` from the cursor `c`. -/
def dotC (m0 : MachineData) (i c : Nat) (xs : Array EW) : EW :=
  dot ((cpw m0).extract c (c + (tb i).nConstraints)) (constraintsW (tb i).opcode xs)

/-- The forms' dot product. -/
def dotF (m0 : MachineData) (fs : Array FormW) (xs : Array EW) : EW :=
  dot (fpw m0) (fs.map (·.evaluate xs))

/-- The frame's word `112`: the `TABLES` walk. -/
def tw112 (i : Nat) : List (Nat × UInt64) := [(112, .ofBitVec (BitVec.ofNat 64 (16 + 40 * i)))]

/-- **The middle of iteration `i`**: the body at offset `o`, the frame's words, the iteration's
outputs, the model's fold so far, the evaluations read. -/
structure Cm [Labels] (a : DecArea) (s : TState) (heights : Array Nat)
    (forms : Array (Array FormW)) (m0 : MachineData) (i : Nat) (acc : Acc) (si : TState)
    (xs : Array EW) (s' : TState) (d : MachineData) : Prop where
  bd : Bd m0 272 N slots (outs m0) 8 d
  fw : FW m0 d (cws m0 ++ lw m0 i acc.2.1 ++ tw112 i)
  it : It a m0 i acc.2.2 xs s' d
  run : preRun heights forms m0 i s = some (acc, si)
  cur : acc.1 = cursorAt i
  rs : (readScalars (tb i).width).run si = some (xs, s')

end

public section

theorem fwL_le {m0 : MachineData} {i : Nat} {f : EW} :
    ∀ p ∈ cws m0 ++ lw m0 i f ++ tw112 i, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280 ∧ (p.1 + 8 ≤ 144 ∨ 176 ≤ p.1) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact cws_le p hp
    · exact lw_le p hp
  · simp only [tw112, List.mem_singleton] at hp
    subst hp; simp

theorem fwL_U {m0 : MachineData} {i : Nat} {f : EW} :
    ((cws m0 ++ lw m0 i f ++ tw112 i).map Prod.fst) = [8, 24, 32, 40, 48, 56, 16, 120, 128, 136, 112] :=
  rfl

theorem missR_sub {Sy : SState} {lo hi hi' : Nat} (h : missR Sy lo hi = true) (hle : hi' ≤ hi) :
    missR Sy lo hi' = true := by
  unfold missR at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro w hw
  have := h w hw
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this ⊢
  rcases this with (h1 | h1) | h1
  · exact .inl (.inl h1)
  · exact .inl (.inr h1)
  · exact .inr (by omega)

theorem eval_add_lit [Labels] {env : Env} (x : Sym) (c : Nat) :
    (Sym.bin .add .W64 x (.lit c)).eval env = x.eval env + BitVec.ofNat 64 c := by
  simp [Sym.eval, BinOp.apply]

theorem eval_lit_add [Labels] {env : Env} (x : Sym) (c : Nat) :
    (Sym.bin .add .W64 (.lit c) x).eval env = x.eval env + BitVec.ofNat 64 c := by
  simp [Sym.eval, BinOp.apply, BitVec.add_comm]

theorem eval_add' [Labels] {env : Env} (x y : Sym) :
    (Sym.bin .add .W64 x y).eval env = x.eval env + y.eval env := by
  simp [Sym.eval, BinOp.apply]

theorem eval_xor' [Labels] {env : Env} (x y : Sym) :
    (Sym.bin .xor .W64 x y).eval env = x.eval env ^^^ y.eval env := by
  simp [Sym.eval, BinOp.apply]

theorem eval_shl4 [Labels] {env : Env} (x : Sym) :
    (Sym.bin .shl .W64 x (.lit 4)).eval env = x.eval env <<< 4 := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask]
  congr 1

theorem shl4_ofNat' (n : Nat) : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem eval_ite [Labels] {env : Env} (c : SBool) (x y : Sym) :
    (Sym.ite c x y).eval env = if c.eval env then x.eval env else y.eval env := rfl

theorem eval_ult [Labels] {env : Env} (x y : Sym) :
    (SBool.cmp .ult .W64 x y).eval env = decide ((x.eval env).toNat < (y.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, BitVec.ult]

theorem eval_not' [Labels] {env : Env} (b : SBool) : (SBool.not b).eval env = !b.eval env := rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n :=
  NativeRustcVm.toNat_ofNat_of_lt h

/-- `rdi5`: the constraint powers from the cursor `c ≤ 2`. -/
theorem eval_rdi5 [Labels] {env : Env} {c : Nat} (hc : c ≤ 2) {cp : BitVec 64}
    (h15 : env.regs .r15 = BitVec.ofNat 64 c) (h24 : env.load 0 24 8 = cp) :
    rdi5.eval env = cp + BitVec.ofNat 64 (16 * c) := by
  unfold rdi5
  rw [eval_ite, eval_not', eval_ult, eval_add', eval_shl4]
  simp only [Sym.eval, h15, toNat_ofNat_lt (show c < 2 ^ 64 by omega),
    toNat_ofNat_lt (show 3 < 2 ^ 64 by omega), decide_eq_true (show c < 3 by omega),
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  show env.load 0 24 8 + _ = _
  rw [h24, shl4_ofNat']

/-- `rsi5`: the table's constraints, at most `2 - c`, its count. -/
theorem eval_rsi5 [Labels] {env : Env} {c n : Nat} (hcn : c + n ≤ 2)
    (h15 : env.regs .r15 = BitVec.ofNat 64 c) (h14 : env.regs .r14 = BitVec.ofNat 64 n) :
    rsi5.eval env = BitVec.ofNat 64 n := by
  have e2 : sub2.eval env = BitVec.ofNat 64 (2 - c) := by
    unfold sub2
    rw [eval_ite, eval_ult]
    simp only [Sym.eval, h15, toNat_ofNat_lt (show c < 2 ^ 64 by omega),
      toNat_ofNat_lt (show 2 < 2 ^ 64 by omega), decide_eq_false (show ¬ 2 < c by omega),
      Bool.false_eq_true, ↓reduceIte, BinOp.apply, low_W64, ext_W64]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega),
      toNat_ofNat_lt (by omega), show Width.W64.bits = 64 from rfl]
    omega
  unfold rsi5
  rw [eval_ite, eval_ult, e2]
  simp only [Sym.eval, h14, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    toNat_ofNat_lt (show 2 - c < 2 ^ 64 by omega)]
  by_cases hlt : n < 2 - c
  · simp [hlt]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    omega

/-- A slice over bytes that stayed the same. -/
theorem slice_same {m0 m : MachineData} {x k : BitVec 64} {n : Nat} (hs : Same m0.dmem m.dmem x n)
    (hk : 16 * k.toNat ≤ n) : slice m x k = (ewsOf m0.dmem x k.toNat).toArray := by
  unfold slice
  rw [NativeRustcVm.ewsOf_congr (d := m0.dmem) fun j hj ↦ hs j (by omega)]

end

end NativeRustcVmX64.Tables.TableTerms
