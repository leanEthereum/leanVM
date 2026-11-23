module

public import NativeRustcVmArm.Whir.FinalLevel.Entry

/-!
# `final_level`: what lives between the blocks

`Live`: after the folded lane's read, the frame, `Base`, the `TState` in X22, the index in X24,
the folded scalars' count in X23 and the scalars at the frame's byte `40`. `Live.saved`: kept
by a call or a block that keeps the callee-saved registers and those bytes. `Ctx.fblock`: a
block of the frame alone writing nothing. The environments with one more region (`Ctx.wf1`,
`Ctx.match1`) and register values (`ev_add`).
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (known_ptr load_ofMachine eval_ptr)

public section

/-- **Between the blocks**, after the folded lane's read. -/
structure Live (level : Whir.Level) (m0 st : MachineData) (folded : Array EW) : Prop where
  base : Base m0 st
  x22 : st.regs.X22 = m0.regs.X0
  x24 : st.regs.X24 = m0.regs.X1
  x23 : st.regs.X23.toNat = 2 ^ mu m0 + level.fold
  size : folded.size = 2 ^ mu m0 + level.fold
  fold : NativeRustcVm.EWsAt st.dmem (loc m0 40) folded.toList

theorem Live.fr {level : Whir.Level} {m0 st : MachineData} {folded : Array EW}
    (h : Live level m0 st folded) : FFr m0 st := h.base.fr

/-- The registers `Live` reads. -/
@[expose] def liveRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X27, .X28]

theorem liveRegs_cs : ∀ r ∈ liveRegs, calleeSaved r = true := by decide

/-- `Live` kept. -/
theorem Live.saved {level : Whir.Level} {m0 st st' : MachineData} {folded : Array EW}
    (h : Live level m0 st folded) (hf : FFr m0 st')
    (hk : ∀ r ∈ liveRegs, st'.regs.getXReg r = st.regs.getXReg r)
    (hs : NativeRustcVm.Layout.Same st.dmem st'.dmem (loc m0 40) 1024)
    (h64 : 2 ^ mu m0 + level.fold ≤ 64) : Live level m0 st' folded where
  base := ⟨hf, (by rw [show st'.regs.X19 = st.regs.X19 from hk .X19 (by simp [liveRegs])]
                   exact h.base.x19),
    (hk .X20 (by simp [liveRegs])).trans h.base.x20,
    (hk .X21 (by simp [liveRegs])).trans h.base.x21,
    (hk .X27 (by simp [liveRegs])).trans h.base.x27,
    (hk .X28 (by simp [liveRegs])).trans h.base.x28⟩
  x22 := (hk .X22 (by simp [liveRegs])).trans h.x22
  x24 := (hk .X24 (by simp [liveRegs])).trans h.x24
  x23 := by rw [show st'.regs.X23 = st.regs.X23 from hk .X23 (by simp [liveRegs])]; exact h.x23
  size := h.size
  fold := NativeRustcVm.Layout.BytesAt.of_same h.fold hs (by
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, h.size]; omega)

/-- The registers a block keeps, from its literal state. -/
theorem kept_of {S : SState} {rs : List XReg} (h : keptRegs S rs = true) :
    ∀ r ∈ rs, S.reg r = some (.reg r) := by
  simp only [keptRegs, List.all_eq_true, beq_iff_eq] at h
  exact h

/-- Callee-saved registers kept keep `liveRegs`. -/
theorem live_cs {st st' : MachineData}
    (hcs : ∀ r, calleeSaved r = true → st'.regs.getXReg r = st.regs.getXReg r) :
    ∀ r ∈ liveRegs, st'.regs.getXReg r = st.regs.getXReg r :=
  fun r hr ↦ hcs r (liveRegs_cs r hr)

theorem ev_add [Labels] (m : MachineData) (rs : List (BitVec 64 × Nat)) (r : XReg) (n : Nat) :
    (Sym.bin .add .W64 (.reg r) (.lit n)).eval (Env.ofMachine m rs) =
      (m.regs.getXReg r).toBitVec + BitVec.ofNat 64 n := by
  sym_simp; rfl

theorem ev_add2 [Labels] (m : MachineData) (rs : List (BitVec 64 × Nat)) (r r' : XReg) :
    (Sym.bin .add .W64 (.reg r) (.reg r')).eval (Env.ofMachine m rs) =
      (m.regs.getXReg r).toBitVec + (m.regs.getXReg r').toBitVec := by
  sym_simp; rfl

section
variable [Labels] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s0 level ba b w rounds m0)
include c

/-- The frame's environment with an input region `(x, n)`. -/
theorem wf1 {st : MachineData} (hf : FFr m0 st) {x : BitVec 64} {n : Nat}
    (hx : WhirIn m0 x n finalLevelStack) : (fenv m0 st [(x, n)]).WF :=
  c.fwf1 hf hx.1.1 hx.1.2 hx.2

/-- The frame's state with an input region `(x, n)` at register `r`. -/
theorem match1 {st : MachineData} (hf : FFr m0 st) {x : BitVec 64} {n : Nat} {r : XReg}
    (hr : (st.regs.getXReg r).toBitVec = x) :
    Match (fenv m0 st [(x, n)]) (init [(2672, true), (n, false)] (.ptr 0 0) [(r, .ptr 1 0)]) st :=
  match_ofMachine ⟨rfl, fun _ ↦ c.aligned, rfl, fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hf.sp]; simp [Sym.eval]) ⟨known_ptr (i := 1) rfl hr, trivial⟩ trivial trivial trivial

end Ctx

end

section
variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **A block of the frame alone** writing nothing. -/
theorem Ctx.fblock (c : Ctx a s0 level ba b w rounds m0) (hp : Placed code k)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt code j) (hne : ds ≠ []) {S' : SState}
    {x : Exit} (hx : exec ds fS = some (S', x)) (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hf : FFr m0 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Match (fenv m0 st.data []) S' st'.data →
      PcOk (fenv m0 st.data []) x (Host.addrOf (k + j + ds.length)) st' → FFr m0 st'.data →
      st'.data.dmem = st.data.dmem →
      (∀ r, S'.reg r = some (.reg r) → st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := c.fwf hf
  have hm := c.fmatch hf
  exact exec_at (inf hp hk hne) hx hwf hpc hm fun st' hm' hpc' ↦
    cont st' hm' hpc' (Fr.ofBlock hf hm hm' hwf rfl hmem (by rw [hsp]; rfl)
      (fun _ h ↦ by cases h)) (hm'.dmem_eq hwf hmem) fun r h ↦ reg_of hm' h rfl

end

end

end NativeRustcVmArm.Whir.FinalLevel
