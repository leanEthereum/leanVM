module

public import NativeRustcVmArm.Whir.Frame

/-!
# Blocks between a function's prologue and epilogue

A block run from a state of the frame (`Fr`) in the environment of that state alone (`regsBlock`:
no region, no write) keeps the frame and the memory; `reg_of`, `getXReg_init` read registers off
the final `Match`.
-/

namespace NativeRustcVmArm.Whir

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring

public section

theorem getXReg_init (r : XReg) : (init [] .sp).reg r = some (.reg r) := by
  cases r <;> rfl

/-- A register a block set. -/
theorem reg_of [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r : XReg} {v : Sym} (h : S.reg r = some v) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    m.regs.getXReg r = w :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

/-- A register's value, as the final `Match` gives it. -/
theorem reg_val [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r : XReg} {v : Sym} (h : S.reg r = some v) :
    (m.regs.getXReg r).toBitVec = v.eval env :=
  hm.regs r v h

/-- The callee-saved registers a block keeps (`keep`) as `.reg r`. -/
@[expose] def keptRegs (S : SState) (keep : List XReg) : Bool :=
  keep.all fun r ↦ S.reg r == some (.reg r)

theorem keptRegs_ok {S : SState} {keep : List XReg} (h : keptRegs S keep = true) :
    ∀ r ∈ keep, ∃ v, (init [] .sp).reg r = some v ∧ S.reg r = some v := by
  intro r hr
  simp only [keptRegs, List.all_eq_true, beq_iff_eq] at h
  exact ⟨_, getXReg_init r, h r hr⟩

/-- A block whose writes are all in region `0` writes only there. -/
theorem written_r0 {env : Env} {S : SState} {b : BitVec 64} {F : Nat} (hwf : env.WF)
    (h0 : env.regions[0]? = some (b, F)) (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F)
    {q : BitVec 64} (hq : Written env S q) : InRange b F q := by
  obtain ⟨w, hw, b', sz, hb, h1, h2⟩ := hq
  obtain ⟨hr, hle⟩ := hS w hw
  rw [hr, h0] at hb
  cases hb
  rw [Sym.inRange_iff (hwf.noWrap 0 b F h0)]
  omega

/-- A written byte is in the region of its write. -/
theorem written_inRange {env : Env} {S : SState} (hwf : env.WF)
    (hle : ∀ w ∈ S.mem, ∀ b sz, env.regions[w.r]? = some (b, sz) → w.off + w.n ≤ sz)
    {q : BitVec 64} (hq : Written env S q) :
    ∃ w ∈ S.mem, ∃ b sz, env.regions[w.r]? = some (b, sz) ∧ InRange b sz q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
  have := hle w hw b sz hb
  refine ⟨w, hw, b, sz, hb, ?_⟩
  rw [Sym.inRange_iff (hwf.noWrap _ b sz hb)]
  omega

section
variable [Host] {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
  {outs : BitVec 64 → Prop}

/-- **A block of registers only**, from a state of the frame: the frame and the memory kept. -/
theorem _root_.NativeRustcVmArm.Ring.Fr.regsBlock {st : MachineState}
    (h : Fr m0 F N slots keep outs st.data)
    {ds : List Directive} {k : Nat} {S' : SState} {x : Exit} {R : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog k) (hx : exec ds (init [] .sp) = some (S', x))
    (hpc : st.pc = Host.addrOf k) (hmem : S'.mem = []) (hsp : S'.sp = .sp)
    (hkeep : keptRegs S' keep = true)
    (cont : ∀ st', Fr m0 F N slots keep outs st'.data → st'.data.dmem = st.data.dmem →
      Match (Env.ofMachine st.data []) S' st'.data →
      PcOk (Env.ofMachine st.data []) x (Host.addrOf (k + ds.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at hk hx (Env.wf_nil st.data) hpc (match_nil st.data) fun st' hm' hpc' ↦
    cont st' (Fr.ofBlock h (match_nil st.data) hm' (Env.wf_nil st.data) rfl hmem
      (by rw [hsp]; rfl) (keptRegs_ok hkeep))
      (hm'.dmem_eq (Env.wf_nil st.data) hmem) hm' hpc'

end

end

end NativeRustcVmArm.Whir
