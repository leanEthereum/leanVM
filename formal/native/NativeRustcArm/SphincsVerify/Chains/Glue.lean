module

public import NativeRustcArm.SphincsVerify.Chains.Keep

/-!
# Running the chains' blocks

A block of the function at its directive `j` (`blk`), the pc its exit gives (`pc_true`,
`pc_false`, `pc_at`), registers after a block (`regIs_reg`, `x2_eq`) and after a call
(`RegIs.of_saved`), a literal word the memory holds put into the symbolic state
(`match_withLit`), and the bytes of the chain's word `i << 24` (`bytes_chainWord`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

public section

section
variable [NativeRustcArm.Host]

/-- **A block of the function** run from directive `j`, then `cont` from where it ends. -/
theorem blk (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) {ds : List Directive}
    {j : Nat} (hb : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hne : ds ≠ []) {env : Env}
    {S S' : SState} {x : Exit} (hx : exec ds S = some (S', x)) (hwf : env.WF) {m : MachineData}
    (hm : Match env S m) {R : MachineState → Prop}
    (cont : ∀ st, Match env S' st.data → PcOk env x (r.pc (j + ds.length)) st →
      Eventually (step1 NativeRustcArm.Host.exe) R st) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ :=
  exec_then (hb.trans hp.1 hne) hx hwf hm fun st h1 h2 ↦
    cont st h1 (by rw [Run.pc, ← Nat.add_assoc]; exact h2)

/-- A state at a known pc. -/
theorem pc_at {R : MachineState → Prop} {st : MachineState} {a : Int64} (h : st.pc = a)
    (k : Eventually (step1 NativeRustcArm.Host.exe) R ⟨st.data, a⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R st := by
  obtain ⟨d, pc⟩ := st
  subst h
  exact k

end

variable [Labels]

theorem pc_true {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit true) l) next st) : st.pc = Labels.label l := h

theorem pc_false {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit false) l) next st) : st.pc = next := h

/-- **A register a block keeps.** -/
theorem regIs_reg {r : Run} {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {y : XReg} (h : S.reg y = some (.reg y)) {v : BitVec 64}
    (hv : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs at *
  rw [hm.regs y _ h]
  exact hv

/-- A register a block sets to a literal: its number. -/
theorem toNat_of_lit {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {y : XReg}
    {c : Nat} (h : S.reg y = some (.lit c)) (hc : c < 2 ^ 64) : (m'.regs.getXReg y).toNat = c := by
  have := hm.regs y _ h
  rw [← UInt64.toNat_toBitVec, this]
  exact Nat.mod_eq_of_lt hc

/-- X2 set to a literal. -/
theorem x2_eq {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m') {c : Nat}
    (h : S.reg .X2 = some (.lit c)) (hc : c < 2 ^ 64) : m'.regs.X2.toNat = c :=
  toNat_of_lit hm h hc

/-- X1 set to `0`. -/
theorem x1_zero {env : Env} {m' : MachineData} {S : SState} (hm : Match env S m')
    (h : S.reg .X1 = some (.lit 0)) : m'.regs.X1.toUInt8 = 0 := by
  have := toNat_of_lit hm h (by decide)
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8]
  exact (congrArg (· % 256) this).trans rfl

omit [Labels] in
/-- **A callee-saved register after a call.** -/
theorem RegIs.of_saved {m m' : MachineData} (hS : Saved m m') {y : XReg}
    (hy : calleeSaved y = true) {v : BitVec 64} (h : Run.RegIs m y v) : Run.RegIs m' y v := by
  unfold Run.RegIs at *
  rw [hS.1 y hy]
  exact h

/-- **A literal word the memory holds**, as a write of the symbolic state. -/
theorem match_withLit {r : Run} {m : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m) (hS : S.mem = []) {o n c : Nat}
    (h : BytesAt m.dmem (r.off o) ((List.range n).map (byteOf (BitVec.ofNat 64 c)))) :
    Match (r.env m vars) { S with mem := [⟨0, o, n, .lit c⟩] } m :=
  Match.withWrite hm hS (b := r.base) (sz := 29376) rfl fun i hi ↦ by
    have := h i (by simp; omega)
    rw [r.off_add] at this
    show m.dmem.get? (r.off (o + i)) = _
    rw [this]
    simp [Sym.eval]

omit [Labels] in
/-- The bytes of a frame write of a value that is the frame's address. -/
theorem off_eq_base_add (r : Run) (o : Nat) : r.base + BitVec.ofNat 64 o = r.off o := rfl

omit [Labels] in
/-- **The chain's word**: the 32-bit `i << 24` stored is `i` big-endian. -/
theorem bytes_chainWord {i : Nat} (hi : i < 256) :
    (List.range 4).map (byteOf (BitVec.ofNat 64 (i * 16777216))) = be32 i.toUInt32 := by
  have h : ∀ t < 4, byteOf (BitVec.ofNat 64 (i * 16777216)) t =
      ((UInt32.ofNat (i * 16777216)) >>> (8 * t).toUInt32).toUInt8 := fun t ht ↦ by
    rw [byteOf_eq_toUInt32 _ ht, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), be32]
  congr 1 <;> [skip; congr 1 <;> [skip; congr 1 <;> [skip; congr 1]]] <;>
    apply UInt8.toNat_inj.mp <;>
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.toNat_ofNat',
      Nat.toUInt32_eq, Nat.shiftRight_eq_div_pow] <;>
    norm_num <;> omega

end

end NativeRustcArm.SphincsVerifyProof.Chains
