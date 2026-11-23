module

public import NativeRustcVmX64.Whir.GlueLevel.Mem
public import NativeRustcVmX64.Transcript.Glue
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Field.LinSound

/-!
# `glue_level`'s steps: what they share (x86-64)

The machine state before the block at `off` (`At`), the variables' values of the templates
(`v1`, `v2`, `v3`, `vA`), the regions' bases (`base_1` to `base_8`), the templates' aliases
(`alias_tac`), a word of a region loaded (`ldW`), the branches `glue_level` never takes
(`above_false`, `al_false`).
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Whir.Rows
open NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero toNat_off)

@[expose] public section

/-- The environment of a block of `glue_level`. -/
abbrev envG (s : WhirStateW) (m0 m : MachineData) (vals : Nat → BitVec 64) (ret : BitVec 64) :
    Env :=
  envA m0 m 96 64 (rsOf s m0) vals ret

/-- Between blocks. -/
abbrev BndG [Labels] (s : WhirStateW) (m0 : MachineData) (wr : Nat → Bool) (T : SState)
    (vals : Nat → BitVec 64) (m : MachineData) : Prop :=
  BndA m0 96 64 glueLevelStack (rsOf s m0) wr T vals m

/-- **Before the block at `off`**: the template `T` with the values `vals`. -/
def At [Host] (s : WhirStateW) (m0 : MachineData) (k off : Nat) (wr : Nat → Bool) (T : SState)
    (vals : Nat → BitVec 64) (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + off) ∧ BndG s m0 wr T vals st.data

/-- No array written. -/
abbrev noWr : Nat → Bool := fun _ ↦ false

/-- After `λ · oodValue`. -/
abbrev v1 (s : WhirStateW) (m0 : MachineData) : Nat → BitVec 64 :=
  V s m0 (c0 (mul1 m0)) (c1 (mul1 m0))
/-- After `λ²`. -/
abbrev v2 (s : WhirStateW) (m0 : MachineData) : Nat → BitVec 64 := V s m0 (c0 (l2 m0)) (c1 (l2 m0))
/-- After `λ² · batched`. -/
abbrev v3 (s : WhirStateW) (m0 : MachineData) : Nat → BitVec 64 :=
  V s m0 (c0 (cc2 m0)) (c1 (cc2 m0))
/-- After the products. -/
abbrev vA (s : WhirStateW) (m0 : MachineData) : Nat → BitVec 64 := V s m0 0 0

end

/-- The values a block leaves: each link's symbolic value, evaluated. -/
macro "vtac0" : tactic => `(tactic|
  (simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval,
    NativeRustcVmX64.Field.Lin.xor_apply, NativeRustcVmX64.Field.Lin.add_apply,
    NativeRustcVmX64.Field.Lin.mul_apply, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]) <;> and_intros <;> (try rfl))

public section

variable {s : WhirStateW} {m0 : MachineData}

theorem rs_sizes : (rsOf s m0).map Prod.snd = [16, 488, 8, 40, 488, 40, 1848, 3688] := rfl

section
variable {m : MachineData} {vals : Nat → BitVec 64} {ret : BitVec 64}

theorem base_0 : (envG s m0 m vals ret).base 0 = stackBelow m0 96 := rfl
theorem base_1 : (envG s m0 m vals ret).base 1 = off (pOf m0) 0 := rfl
theorem base_2 : (envG s m0 m vals ret).base 2 = off (pOf m0) 16 := rfl
theorem base_3 : (envG s m0 m vals ret).base 3 = off (pOf m0) 504 := rfl
theorem base_4 : (envG s m0 m vals ret).base 4 = off (pOf m0) (o1 s.glued.size) := rfl
theorem base_5 : (envG s m0 m vals ret).base 5 = off (pOf m0) (o1 s.glued.size + 40) := rfl
theorem base_6 : (envG s m0 m vals ret).base 6 = off (pOf m0) (o2 s.glued.size) := rfl
theorem base_7 : (envG s m0 m vals ret).base 7 = off (pOf m0) (o2 s.glued.size + 528) := rfl
theorem base_8 : (envG s m0 m vals ret).base 8 = off (pOf m0) (o2 s.glued.size + 2376) := rfl

end

/-- Bases of a region as a sum, as the executor builds them. -/
theorem off_eq {p : BitVec 64} {a c : Nat} (b : Int) (hb : 0 ≤ b) (h : a + b.toNat = c) :
    off p a + BitVec.ofInt 64 b = off p c + BitVec.ofInt 64 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

end

/-- An alias's two sides: their numbers. -/
macro "alias_tac" : tactic => `(tactic|
  (apply BitVec.eq_of_toNat_eq
   simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, NativeRustcVm.Transcript.off,
     BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
   omega))

public section

variable {s : WhirStateW} {m0 : MachineData}

theorem toNat_mod_int (b : Nat) : ((b : Int) % 2 ^ 64).toNat = b % 2 ^ 64 := by omega

/-- **A word loaded** from a region. -/
theorem ldW {env : Env} {r o : Nat} {w : UInt64}
    (h : WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) w) : env.load r o 8 = w.toBitVec :=
  NativeRustcVmX64.Transcript.load_of_wordAt h

/-- `cmpq $9; ja`: not taken below `10`. -/
theorem above_false [Labels] {env : Env} {a : Sym} (h : (a.eval env).toNat ≤ 9) :
    (SBool.and (SBool.cmp .ult .W64 a (.lit 9)).not (SBool.cmp .eq .W64 a (.lit 9)).not).eval env =
      false := by
  simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval]
  generalize a.eval env = x at h
  rcases Nat.lt_or_eq_of_le h with h | h
  · have : x.ult (BitVec.ofNat 64 9) = true := by
      rw [BitVec.ult_eq_decide]
      simp [h]
    rw [this]
    rfl
  · have : x = BitVec.ofNat 64 9 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
    subst this
    simp

/-- `testb %al, %al; je`: not taken where AL is `1`. -/
theorem al_false [Labels] {env : Env} (h : (env.regs .rax).toNat % 256 = 1) :
    (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval env = false := by
  simp only [SBool.eval, CmpOp.apply, BinOp.apply, Sym.eval, BitVec.and_self]
  rw [Bool.eq_false_iff]
  intro he
  have := congrArg BitVec.toNat (beq_iff_eq.mp he)
  rw [toNat_low, toNat_low, toNat_ext, toNat_low] at this
  rw [show Width.W8.bits = 8 from rfl] at this
  simp only [BitVec.toNat_ofNat] at this
  omega

end

end NativeRustcVmX64.Whir.GlueLevel
