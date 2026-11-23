module

public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.WMem
import Mathlib.Tactic.IntervalCases

/-!
# `verify_layer`: the weights loop, to the first `EW::mul`

One iteration of the loop starts at `.LVerifyLayer_30` (`b57`, `WHead j`): the positions
`keccakAlong j 4` and `keccakAlong j 3` (`b57`, `b60`), the kernel's elements there (`b58`, `b53`)
and at `j` (`b54`), then `β · eq[keccakAlong j 3]` by `EW::mul` (`phaseA`). Between the calls the
iteration keeps `WMid`.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open LeanVM.Protocol.Verifier (keccakAlong)

@[expose] public section

/-- **Iteration `j` between its calls**: the head's facts, the frame's word `96` advanced, the
kernel's elements at `keccakAlong j 4` (X21, X22) and at `j` (X28, X27). -/
structure WMid (m0 : MachineData) (a : DecArea) (s' : TState) (t0 t1 t2 beta : EW)
    (mu point eq : Array EW) (j : Nat) (m : MachineData) : Prop where
  lt : j < 1600
  body : Body m0 m
  x19 : m.regs.X19.toNat = j
  x26 : m.regs.X26.toNat = 25600 - 16 * j
  x29 : m.regs.X29.toBitVec = sA m0 + BitVec.ofNat 64 (51200 + 16 * j)
  x20 : m.regs.X20.toBitVec = sA m0 + BitVec.ofNat 64 (51208 + 16 * j)
  x23 : m.regs.X23 = beta.c0
  x25 : m.regs.X25 = beta.c1
  x24 : m.regs.X24.toNat = point.size
  x21 : m.regs.X21 = (eq.getD (keccakAlong j 4) 0).c0
  x22 : m.regs.X22 = (eq.getD (keccakAlong j 4) 0).c1
  x28 : m.regs.X28 = (eq.getD j 0).c0
  x27 : m.regs.X27 = (eq.getD j 0).c1
  mem : WMem m0 a s' t0 t1 t2 beta mu point eq j m.dmem
  f96 : NativeRustcVm.WordAt m.dmem (base m0 2032 + BitVec.ofNat 64 96)
    (UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 (107528 + 16 * (j + 1))))

end

public section

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {s' : TState} {t0 t1 t2 beta : EW} {mu point eq : Array EW}

/-- The kernel's element at `p + 16 (A + B)`, as `b53`/`b58` compute its address. -/
theorem idx_eval [Labels] {env : Env} {x y : XReg} {p : BitVec 64} {A B : Nat}
    (hp : env.load 0 144 8 = p) (hx : (env.regs x).toNat = A) (hy : (env.regs y).toNat = B) :
    (Sym.bin .add .W64 (.bin .add .W64 (.load 0 144 8) (shl4 (.reg x))) (shl4 (.reg y))).eval env =
      p + BitVec.ofNat 64 (16 * (A + B)) := by
  rw [ev_bin, ev_bin, ev_load, hp, shl4, shl4, ev_un, ev_un, ev_reg, ev_reg]
  apply BitVec.eq_of_toNat_eq
  rw [add_toNat, add_toNat, shl4_toNat, shl4_toNat, hx, hy, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A register a block loaded from a word in a region. -/
theorem reg_load [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r : XReg} {q o : Nat} {v : UInt64} (h : S.reg r = some (.load q o 8))
    (hw : NativeRustcVm.WordAt env.mem0 (env.base q + BitVec.ofNat 64 o) v) :
    m.regs.getXReg r = v :=
  UInt64.toBitVec_inj.mp ((hm.regs r _ h).trans (by rw [ev_load]; exact Ring.load_word hw))

/-- **The kernel's element `i`**, word by word. -/
theorem kern_word {j : Nat} {d : DataMem} (h : WMem m0 a s' t0 t1 t2 beta mu point eq j d)
    (heq : eq.size = 2048) {i : Nat} (hi : i < 2048) :
    NativeRustcVm.WordAt d (sA m0 + BitVec.ofNat 64 (107520 + 16 * i) + BitVec.ofNat 64 0)
        (eq.getD i 0).c0 ∧
      NativeRustcVm.WordAt d (sA m0 + BitVec.ofNat 64 (107520 + 16 * i) + BitVec.ofNat 64 8)
        (eq.getD i 0).c1 := by
  have hi' : i < eq.toList.length := by rw [Array.length_toList, heq]; exact hi
  have := h.kern.getElem hi'
  rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add] at this
  have e : eq.getD i 0 = eq.toList[i] := by
    rw [Array.getElem_toList]
    simp only [Array.getD, show i < eq.size by omega, ↓reduceDIte]
    rfl
  rw [e, NativeRustcVm.addr_add_zero]
  exact this

/-- `WMid` kept by `EW::mul`. -/
theorem WMid.call [Labels] (hpre : VerifyLayerPre a s c m0) (hps : point.size ≤ 30)
    (heq : eq.size = 2048) {j : Nat} {m m' : MachineData}
    (h : WMid m0 a s' t0 t1 t2 beta mu point eq j m) (hb' : Body m0 m') (hsv : Saved m m')
    (hs : SameOutside m.dmem m'.dmem fun q ↦
      InRange (stackBelow m ewMulStack) ewMulStack q ∨ False) :
    WMid m0 a s' t0 t1 t2 beta mu point eq j m' := by
  have g := geo_of hpre
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN
  have hn : ewMulStack ≤ 1616 := by decide
  have hfr := same_stack g h.body.sp hn hs (x := base m0 2032) (len := 2032) (by rw [hbN]; omega)
    (by rw [hbN]; omega)
  have r : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r := hsv.1
  exact ⟨h.lt, hb', (congrArg UInt64.toNat (r .X19 rfl)).trans h.x19,
    (congrArg UInt64.toNat (r .X26 rfl)).trans h.x26,
    (congrArg UInt64.toBitVec (r .X29 rfl)).trans h.x29,
    (congrArg UInt64.toBitVec (r .X20 rfl)).trans h.x20, (r .X23 rfl).trans h.x23,
    (r .X25 rfl).trans h.x25, (congrArg UInt64.toNat (r .X24 rfl)).trans h.x24,
    (r .X21 rfl).trans h.x21, (r .X22 rfl).trans h.x22, (r .X28 rfl).trans h.x28,
    (r .X27 rfl).trans h.x27,
    h.mem.call hpre h.body hps heq (by have := h.lt; omega) hsv.2.2 hn hs,
    NativeRustcVm.Layout.WordAt.of_same h.f96 (hfr.sub (o := 96) (k := 8) (by omega))
      (Nat.le_refl _)⟩

/-- **`WMem` kept by a write of the frame's word `96`.** -/
theorem WMem.frame96 [Labels] (hpre : VerifyLayerPre a s c m0) (hps : point.size ≤ 30)
    (heq : eq.size = 2048) {j : Nat} (hj : j ≤ 1600) {d d' : DataMem}
    (h : WMem m0 a s' t0 t1 t2 beta mu point eq j d) (hk : Kept d d')
    (hs : SameOutside d d' (InRange (base m0 2032 + BitVec.ofNat 64 96) 8)) :
    WMem m0 a s' t0 t1 t2 beta mu point eq j d' := by
  have g := geo_of hpre
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN; have := g.hs; have := g.hss
  have e96 := g.fa (o := 96) (by omega)
  obtain ⟨hdw, hds, -, -⟩ := dec_geo hpre
  have := g.ht; have := g.hts
  refine h.keep hpre hps heq hj hk hs
    (fun o ho _ ↦ notIn (by rw [e96]; omega) (by rw [hbN]; omega) (by rw [e96, hbN]; omega))
    (fun o ho _ ↦ notIn (by rw [e96]; omega) (by omega) (by rw [e96]; omega)) fun q hq ↦ ?_
  rw [Sym.inRange_iff (by rw [e96]; omega), e96] at hq
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : InRange (tA m0) 760 q := h
    rw [Sym.inRange_iff (by omega)] at h'; omega
  · have h' : InRange a.words (8 * a.len) q := h
    rw [Sym.inRange_iff hdw] at h'; omega

/-- **`WMem` kept by the store of weight `j`**, then extended by it. -/
theorem WMem.store [Labels] (hpre : VerifyLayerPre a s c m0) (hps : point.size ≤ 30)
    (heq : eq.size = 2048) {j : Nat} (hj : j < 1600) {d d' : DataMem}
    (h : WMem m0 a s' t0 t1 t2 beta mu point eq j d) (hk : Kept d d')
    (hs : SameOutside d d' (InRange (sA m0 + BitVec.ofNat 64 (51200 + 16 * j)) 16))
    (hw : NativeRustcVm.EWAt d' (sA m0 + BitVec.ofNat 64 (51200 + 16 * j)) (lwF eq beta j)) :
    WMem m0 a s' t0 t1 t2 beta mu point eq (j + 1) d' := by
  have g := geo_of hpre
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN; have := g.hs; have := g.hss
  have ej := g.sa (o := 51200 + 16 * j) (by omega)
  have h' := h.keep hpre hps heq (by omega) hk hs
    (fun o ho _ ↦ notIn (by rw [ej]; omega) (by rw [hbN]; omega) (by rw [ej, hbN]; omega))
    (fun o ho ho' ↦ notIn (by rw [ej]; omega) (by omega) (by rw [ej]; omega))
    fun q hq ↦ sc_miss hpre (by omega) (by omega) hq
  refine ⟨h'.fw, h'.f144, h'.mu, h'.pt, h'.ts, h'.kern, fun i hi ↦ ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact h'.lw i hi
  · exact hw

/-- A conditional exit not taken. -/
theorem pc_false [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) (hc : c.eval env = false) : st.pc = next := by
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at h
  exact h

/-- A conditional exit taken. -/
theorem pc_true [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) (hc : c.eval env = true) : st.pc = Labels.label l := by
  simp only [PcOk, hc, ↓reduceIte] at h
  exact h

/-- `add` on 64 bits. -/
theorem add_apply (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]

variable [Host] {k : Nat}

/-- `.LVerifyLayer_33`'s address. -/
theorem label33 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_33 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b60Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b60Offset) NativeRustcVmArm.Vm.VerifyLayer.label_33_at

/-- `.LVerifyLayer_28`'s address. -/
theorem label28 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_28 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b53Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b53Offset) NativeRustcVmArm.Vm.VerifyLayer.label_28_at

/-- `.LVerifyLayer_35`'s address. -/
theorem label35 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_35 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b62Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b62Offset) NativeRustcVmArm.Vm.VerifyLayer.label_35_at

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
