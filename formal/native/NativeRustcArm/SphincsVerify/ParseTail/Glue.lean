module

public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names

public import NativeRustcArm.SphincsVerify.Parse.Glue
public import NativeRustcArm.SphincsVerify.Rev

/-!
# The parse's tail: what its blocks share

The tail (`b16 .. b44`) runs each straight block from `fs known`: region 0 the frame, SP its
base, X29 the saved registers' address, the `known` registers. A block ending in `bl memcpy`
(`block_memcpy`), `bl memset` (`block_memset`) or falling through (`block_fall`) is the block's
summary then, for a call, the callee's contract between frame offsets. The copy loops (`b18`,
`b26`, `b34`) copy 16 bytes a turn between two 16-byte regions rebased each turn (`loopS`,
`copy_turn`).
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.SphincsVerifyProof.Parse
  LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A straight block's start: region 0 the frame, SP its base, X29 the saved registers', `known`. -/
def fs (known : List (XReg × Sym)) : SState :=
  init [(29376, true)] (.ptr 0 0) ((.X29, .ptr 0 29280) :: known)

/-- A copy loop's turn: region 0 the 16 destination bytes at `D + X8`, region 1 the 16 source
bytes at `X9 + X8`. -/
def loopS (D : XReg) : SState :=
  init [(16, false), (16, false)] .sp [] [] []
    [(.bin .add .W64 (.reg D) (.reg .X8), 0, 0), (.bin .add .W64 (.reg .X9) (.reg .X8), 1, 0)]

end

public section

variable (r : Run) [NativeRustcArm.Host]

theorem ptr_eval (m : MachineData) (vars : Nat → BitVec 64) (a : Nat) :
    (Sym.ptr 0 a).eval (r.env m vars) = r.off a := by
  show r.base + BitVec.ofInt 64 (a : Int) = r.base + BitVec.ofNat 64 a
  rw [BitVec.ofInt_natCast]

/-- The frame's environment and `fs known` describe a state of the frame whose `known` registers
are their values. -/
theorem match_fs (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {known : List (XReg × Sym)}
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m)) known) :
    Match (r.env m) (fs known) m :=
  r.match_frame hpre hF ⟨hF.2.1.trans (ptr_eval r m (fun _ ↦ 0) 29280).symm, hkn⟩ trivial trivial
    trivial

/-- **A straight block ending in `bl memcpy`** between frame offsets: the block's summary, then
`memcpy`'s contract; `cont` from the return address. -/
theorem block_memcpy (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {known : List (XReg × Sym)} {S' : SState} (hx : exec ds (fs known) = some (S', .call NativeRustcArm.Common.Memcpy.entryLabel))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0) (h29 : S'.reg .X29 = some (.ptr 0 29280))
    {a b n : Nat} (h0 : S'.reg .X0 = some (.ptr 0 a)) (h1 : S'.reg .X1 = some (.ptr 0 b))
    (h2 : S'.reg .X2 = some (.lit n)) (hn : n < 2 ^ 64) (ha : a + n ≤ 29280) (hb : b + n ≤ 29376)
    (hab : a + n ≤ b ∨ b + n ≤ a) {m : MachineData} (hF : r.Frame m)
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m)) known)
    {R : MachineState → Prop}
    (cont : ∀ (m' : MachineData) (st' : MachineState), Match (r.env m) S' m' →
      st'.pc = r.pc (j + ds.length) → r.Frame st'.data → Saved m' st'.data →
      BytesAt st'.data.dmem (r.off a) (bytesOf m'.dmem (r.off b) n) →
      SameOutside m'.dmem st'.data.dmem (InRange (r.off a) n) →
      Eventually (step1 NativeRustcArm.Host.exe) R st') :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ := by
  have hk' : ds.IsInfixAt NativeRustcArm.Host.prog (r.k + j) := hk.trans hp.1 (by
    rintro rfl; cases hx)
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  refine exec_then hk' hx hwf (match_fs r hpre hF hkn) fun st hm' hpc ↦ ?_
  have hF' := Run.Frame.of_match r hpre hF hm' hwf hsp h29 hw
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = r.off a := by
    rw [hm'.regs .X0 _ h0, ptr_eval]
  have hx1 : (st.data.regs.getXReg .X1).toBitVec = r.off b := by
    rw [hm'.regs .X1 _ h1, ptr_eval]
  have hx2 : (st.data.regs.getXReg .X2).toNat = n := by
    show (st.data.regs.getXReg .X2).toBitVec.toNat = n
    rw [hm'.regs .X2 _ h2]
    simp only [Sym.eval, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hn
  refine memcpy_frame r hpre hc hpc hF' hx0 hx1 hx2 ha hb hab fun st' hpc' hF'' hS hb' hout ↦ ?_
  exact cont st.data st' hm' (by rw [hpc', Run.pc, Nat.add_assoc]) hF'' hS hb' hout

/-- **A straight block ending in `bl memset`** of frame offsets. -/
theorem block_memset (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {known : List (XReg × Sym)} {S' : SState} (hx : exec ds (fs known) = some (S', .call NativeRustcArm.Common.Memset.entryLabel))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0) (h29 : S'.reg .X29 = some (.ptr 0 29280))
    {a n : Nat} (h0 : S'.reg .X0 = some (.ptr 0 a)) (h2 : S'.reg .X2 = some (.lit n))
    (hn : n < 2 ^ 64) (ha : a + n ≤ 29280) {m : MachineData} (hF : r.Frame m)
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m)) known)
    {R : MachineState → Prop}
    (cont : ∀ (m' : MachineData) (st' : MachineState), Match (r.env m) S' m' →
      st'.pc = r.pc (j + ds.length) → r.Frame st'.data → Saved m' st'.data →
      SameOutside m'.dmem st'.data.dmem (InRange (r.off a) n) →
      Eventually (step1 NativeRustcArm.Host.exe) R st') :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ := by
  have hk' : ds.IsInfixAt NativeRustcArm.Host.prog (r.k + j) := hk.trans hp.1 (by
    rintro rfl; cases hx)
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  refine exec_then hk' hx hwf (match_fs r hpre hF hkn) fun st hm' hpc ↦ ?_
  have hF' := Run.Frame.of_match r hpre hF hm' hwf hsp h29 hw
  have hx0 : (st.data.regs.getXReg .X0).toBitVec = r.off a := by
    rw [hm'.regs .X0 _ h0, ptr_eval]
  have hx2 : (st.data.regs.getXReg .X2).toNat = n := by
    show (st.data.regs.getXReg .X2).toBitVec.toNat = n
    rw [hm'.regs .X2 _ h2]
    simp only [Sym.eval, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hn
  refine memset_frame r hpre hc hpc hF' hx0 hx2 ha fun st' hpc' hF'' hS hout ↦ ?_
  exact cont st.data st' hm' (by rw [hpc', Run.pc, Nat.add_assoc]) hF'' hS hout

/-- **A straight block falling through.** -/
theorem block_fall (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {known : List (XReg × Sym)} {S' : SState} (hne : ds ≠ [])
    (hx : exec ds (fs known) = some (S', .fall))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0) (h29 : S'.reg .X29 = some (.ptr 0 29280))
    {m : MachineData} (hF : r.Frame m)
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m)) known)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, Match (r.env m) S' st'.data → st'.pc = r.pc (j + ds.length) →
      r.Frame st'.data → Eventually (step1 NativeRustcArm.Host.exe) R st') :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ := by
  have hk' : ds.IsInfixAt NativeRustcArm.Host.prog (r.k + j) := hk.trans hp.1 hne
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  refine exec_then hk' hx hwf (match_fs r hpre hF hkn) fun st hm' hpc ↦ ?_
  exact cont st hm' (by rw [show st.pc = _ from hpc, Run.pc, Nat.add_assoc])
    (Run.Frame.of_match r hpre hF hm' hwf hsp h29 hw)

end

end NativeRustcArm.SphincsVerifyProof.ParseTail
