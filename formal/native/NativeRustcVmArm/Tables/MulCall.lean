module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Tables.Common
public import NativeRustcVmArm.Spec.Field

/-!
# A block calling `EW::mul`

A block run in an environment whose region 0 is the `F`-byte frame at SP, writing only the frame
and ending in `bl EW::mul` (`call_mul`, from the block's final `Match`): after the call, X0 and X1
are the product of the block's X0, X1 and X2, X3, the callee-saved registers and the frame's words
what the block left, SP the frame's base, and memory changed only in the frame and the
`ewMulStack` bytes below it.
-/

namespace NativeRustcVmArm.Tables

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVm (wordOf)

@[expose] public section

/-- The frame-only start state: region 0 the `F`-byte frame, SP its base. -/
def frameS (F : Nat) : SState := init [(F, true)] (.ptr 0 0)

/-- The `n` bytes below the frame base `fb` and the frame's `F`. -/
def StackArea (fb : BitVec 64) (n F : Nat) : BitVec 64 → Prop :=
  InRange (fb - BitVec.ofNat 64 n) (n + F)

/-- The block's writes are in the frame, region 0's first `F` bytes. -/
def FrameWrites (S : SState) (F : Nat) : Prop :=
  S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ F)) = true

/-- The frame below which `EW::mul` runs: `F` bytes at `fb`, aligned, the stack below mapped. -/
structure FrameOk (d : Mem 64) (fb : BitVec 64) (F : Nat) : Prop where
  al : fb.toNat % 16 = 0
  lo : ewMulStack ≤ fb.toNat
  hi : fb.toNat + F ≤ 2 ^ 64
  map : Mapped d (fb - BitVec.ofNat 64 ewMulStack) (ewMulStack + F)

/-- `EW::mul` of two pairs of symbolic values. -/
def mulOf [Labels] (env : Env) (v0 v1 v2 v3 : Sym) : EW :=
  EW.mul ⟨.ofBitVec (v0.eval env), .ofBitVec (v1.eval env)⟩
    ⟨.ofBitVec (v2.eval env), .ofBitVec (v3.eval env)⟩

end

public section

theorem sub_add_ofNat (fb : BitVec 64) (n o : Nat) :
    fb - BitVec.ofNat 64 n + BitVec.ofNat 64 (n + o) = fb + BitVec.ofNat 64 o := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem FrameOk.mapped {d : Mem 64} {fb : BitVec 64} {F : Nat} (h : FrameOk d fb F) :
    Mapped d fb F := fun i hi => by
  have := h.map (ewMulStack + i) (by omega)
  rwa [sub_add_ofNat] at this

variable [Host]

/-- **A block's call of `EW::mul`.** -/
theorem call_mul {env : Env} (hwf : env.WF) {F : Nat} {fb : BitVec 64}
    (hb0 : env.regions[0]? = some (fb, F)) (hok : FrameOk env.mem0 fb F)
    {S' : SState} {st : MachineState} {next : Int64} (hm' : Match env S' st.data)
    (hpc : PcOk env (.call NativeRustcVmArm.Vm.EWMul.entryLabel) next st) (hsp' : S'.sp = .ptr 0 0)
    (hw : FrameWrites S' F) {v0 v1 v2 v3 : Sym}
    (h0 : S'.reg .X0 = some v0) (h1 : S'.reg .X1 = some v1) (h2 : S'.reg .X2 = some v2)
    (h3 : S'.reg .X3 = some v3)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next →
      st'.data.regs.X0 = (mulOf env v0 v1 v2 v3).c0 →
      st'.data.regs.X1 = (mulOf env v0 v1 v2 v3).c1 →
      (∀ r v, calleeSaved r = true → S'.reg r = some v →
        (st'.data.regs.getXReg r).toBitVec = v.eval env) →
      st'.data.regs.SP.toBitVec = fb →
      (∀ o, o + 8 ≤ F → (wordOf st'.data.dmem (fb + BitVec.ofNat 64 o)).toBitVec =
        (loadSym S'.mem 0 o 8).eval env) →
      SameOutside env.mem0 st'.data.dmem (StackArea fb ewMulStack F) →
      Kept env.mem0 st'.data.dmem →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨hal, hlo, hhi, hmap⟩ := hok
  have hlo' : (fb - BitVec.ofNat 64 ewMulStack).toNat = fb.toNat - ewMulStack :=
    NativeRustcVm.toNat_sub_ofNat hlo
  have hspst : st.data.regs.SP.toBitVec = fb := by
    rw [hm'.sp, hsp']; simp [Sym.eval, Env.base_eq hb0]
  have hspn : st.data.regs.SP.toNat = fb.toNat := by rw [← UInt64.toNat_toBitVec, hspst]
  have hsb : stackBelow st.data ewMulStack = fb - BitVec.ofNat 64 ewMulStack := by
    rw [stackBelow, hspst]
  refine call_then hpc hmul ⟨by rw [hspn]; exact hal, by omega, fun i hi => ?_⟩
    fun st' hpc' hpost => ?_
  · rw [hspst]
    exact hm'.kept hwf _ (hmap i (by omega))
  obtain ⟨hx0, hx1, hsame, hsaved⟩ := hpost
  have e : ∀ r v, S'.reg r = some v → st.data.regs.getXReg r = .ofBitVec (v.eval env) :=
    fun r v h => UInt64.toBitVec_inj.mp (hm'.regs r v h)
  have hfr : ∀ k, k < F →
      ¬InRange (stackBelow st.data ewMulStack) ewMulStack (fb + BitVec.ofNat 64 k) := by
    intro k hk h
    rw [hsb, ← sub_add_ofNat fb ewMulStack k] at h
    unfold InRange at h
    rw [BitVec.add_comm, BitVec.add_sub_cancel, NativeRustcVm.toNat_ofNat_of_lt (by omega)] at h
    omega
  have hnwA : (fb - BitVec.ofNat 64 ewMulStack).toNat + (ewMulStack + F) ≤ 2 ^ 64 := by omega
  have hnwB : (fb - BitVec.ofNat 64 ewMulStack).toNat + ewMulStack ≤ 2 ^ 64 := by omega
  refine cont st' hpc' ?_ ?_
    (fun r v hr hv => by rw [hsaved.1 r hr]; exact hm'.regs r v hv)
    (by rw [hsaved.2.1]; exact hspst) (fun o ho => ?_) (fun p hp => ?_)
    (fun p h => hsaved.2.2 p (hm'.kept hwf p h))
  · rw [hx0, show st.data.regs.X0 = st.data.regs.getXReg .X0 from rfl,
      show st.data.regs.X1 = st.data.regs.getXReg .X1 from rfl,
      show st.data.regs.X2 = st.data.regs.getXReg .X2 from rfl,
      show st.data.regs.X3 = st.data.regs.getXReg .X3 from rfl,
      e .X0 v0 h0, e .X1 v1 h1, e .X2 v2 h2, e .X3 v3 h3]
    rfl
  · rw [hx1, show st.data.regs.X0 = st.data.regs.getXReg .X0 from rfl,
      show st.data.regs.X1 = st.data.regs.getXReg .X1 from rfl,
      show st.data.regs.X2 = st.data.regs.getXReg .X2 from rfl,
      show st.data.regs.X3 = st.data.regs.getXReg .X3 from rfl,
      e .X0 v0 h0, e .X1 v1 h1, e .X2 v2 h2, e .X3 v3 h3]
    rfl
  · rw [NativeRustcVm.wordOf_congr (d := st.data.dmem) fun i hi => hsame _ ?_]
    · exact match_wordOf hm' hwf hb0 ho
    · rw [NativeRustcVm.addr_add_add]
      exact hfr _ (by omega)
  · unfold StackArea at hp
    rw [inRange_iff hnwA, hlo'] at hp
    rw [hsame p fun h => hp (by rw [hsb, inRange_iff hnwB, hlo'] at h; omega)]
    refine hm'.get?_mem0 hwf fun ⟨w, hwm, b, sz, hb, hp1, hp2⟩ => hp ?_
    have hw' := List.all_eq_true.mp hw w hwm
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw'
    rw [hw'.1, hb0] at hb
    cases hb
    omega

end

end NativeRustcVmArm.Tables
