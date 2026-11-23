module

public import NativeRustcVmArm.Wire.PhaseM.Basic

/-!
# `phase_m`: steps through blocks, and the two ways out

A block of the frame without writes (`blk`) or writing the frame below the slots (`blkW`); a word
of the frame (`FW`) kept by them and by calls (`FW.call`). `Base`: the frame and the registers the
body keeps (X19 the working area, X20 the phase, X22 the reader). The exits: `none_run` (`b18`,
`b19`, the model's `none`), `done_run` (`b37`, `b19`, after `write_openings`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVm.Transcript (PhaseAt)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The word `v` at byte `o` of the frame. -/
abbrev FW (m0 : MachineData) (d : Mem 64) (o : Nat) (v : UInt64) : Prop :=
  WordAt d (base m0 192 + BitVec.ofNat 64 o) v

/-- **The body's state**: the frame, X19 the working area, X20 the phase, X22 the reader. -/
structure Base (m0 m : MachineData) : Prop where
  fr : Frm m0 m
  x19 : (m.regs.getXReg .X19).toBitVec = wk m0
  x20 : (m.regs.getXReg .X20).toBitVec = outA m0
  x22 : (m.regs.getXReg .X22).toBitVec = rdr m0

/-- At the way out with `None`. -/
def AtNone [Host] (m0 : MachineData) (B : List UInt8) (c k : Nat) (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b18Offset) ∧ Base m0 st.data ∧ phaseM B c = none

/-- At the way out after `write_openings`. -/
def AtDone [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b37Offset) ∧ Base m0 st.data ∧ st.data.regs.X0 = 1 ∧
    ∃ po c', phaseM B c = some (po, c') ∧ PhaseAt st.data.dmem (outA m0) (phaseW po) ∧
      ReaderAt st.data.dmem (rdr m0) bp B c'

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8}

theorem Base.of_regs {m m' : MachineData} (h : Base m0 m) (hfr : Frm m0 m')
    (hr : ∀ x ∈ [XReg.X19, .X20, .X22], m'.regs.getXReg x = m.regs.getXReg x) : Base m0 m' :=
  ⟨hfr, by rw [hr .X19 (by simp)]; exact h.x19, by rw [hr .X20 (by simp)]; exact h.x20,
    by rw [hr .X22 (by simp)]; exact h.x22⟩

theorem Base.call {m m' : MachineData} (h : Base m0 m) (hfr : Frm m0 m')
    (hcs : ∀ x, calleeSaved x = true → m'.regs.getXReg x = m.regs.getXReg x) : Base m0 m' :=
  h.of_regs hfr fun x hx ↦ hcs x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rfl)

theorem regs_of {env : Sym.Env} {S S' : SState} {m m' : MachineData} [Labels] (hm : Match env S m)
    (hm' : Match env S' m') {rs : List XReg}
    (h : ∀ r ∈ rs, S.reg r = some (.reg r) ∧ S'.reg r = some (.reg r)) :
    ∀ r ∈ rs, m'.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
  Match.reg_eq hm hm' (h r hr).1 (h r hr).2

/-- A frame word kept by a change of memory outside the frame's bytes `o` to `o + 8`. -/
theorem FW.keep {d d' : Mem 64} {R : BitVec 64 → Prop} {o : Nat} {v : UInt64}
    (h : FW m0 d o v) (hs : SameOutside d d' R)
    (hR : ∀ i < 8, ¬R (base m0 192 + BitVec.ofNat 64 o + BitVec.ofNat 64 i)) : FW m0 d' o v :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi ↦
    hR i (by rw [NativeRustcVm.length_wordBytes] at hi; exact hi)

section
variable [Labels]

/-- A frame word kept by a callee using `N'` bytes below the frame, writing the outputs and
possibly the frame's `n` bytes from `lo`. -/
theorem FW.call (G : Geo m0 bp B) {m m' : MachineData} (hfr : Frm m0 m) {N' lo n : Nat}
    (hN' : 192 + N' ≤ 1184)
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m N') N' q ∨
      InRange (base m0 192 + BitVec.ofNat 64 lo) n q ∨ outs (rdr m0) (W m0) q)
    {o : Nat} {v : UInt64} (ho : o + 8 ≤ 192) (hlo : o + 8 ≤ lo ∨ lo + n ≤ o) (hln : lo + n ≤ 192)
    (h : FW m0 m.dmem o v) : FW m0 m'.dmem o v := by
  have hsp := G.sp
  have hSP := m0.regs.SP.toNat_lt
  have hb := G.base_toNat (F := 192) (by omega)
  have hsb := Ring.stackBelow_eq hfr.sp (N' := N') (by omega)
  have hbN := G.base_toNat (F := 192 + N') (by omega)
  refine h.keep hs fun i hi hq ↦ ?_
  have hp : (base m0 192 + BitVec.ofNat 64 o + BitVec.ofNat 64 i).toNat =
      m0.regs.SP.toNat - 192 + o + i := by
    rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by rw [hb]; omega), hb]
    omega
  rcases hq with hq | hq | hq
  · rw [hsb, Sym.inRange_iff (by rw [hbN]; omega), hbN, hp] at hq
    omega
  · have hlo' : (base m0 192 + BitVec.ofNat 64 lo).toNat = m0.regs.SP.toNat - 192 + lo := by
      rw [NativeRustcVm.toNat_add_ofNat (by rw [hb]; omega), hb]
    rw [Sym.inRange_iff (by rw [hlo']; omega), hlo', hp] at hq
    omega
  · have hin : InRange (base m0 192) 192 (base m0 192 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
      rw [Sym.inRange_iff (by rw [hb]; omega), hb, hp]; omega
    exact G.rgeo.not_frame (by omega) hq hin

end

/-- A frame word kept by a block writing elsewhere in the frame. -/
theorem FW.blkW (hst : StackOk m0 1184) {d d' : Mem 64}
    (hs : SameOutside d d' (InRange (base m0 192 + BitVec.ofNat 64 0) 96)) {o : Nat} {v : UInt64}
    (ho : 96 ≤ o) (ho' : o + 8 ≤ 192) (h : FW m0 d o v) : FW m0 d' o v := by
  have hb := Ring.base_toNat (m0 := m0) (F := 192) (by have := hst.2.1; omega)
  have hSP := m0.regs.SP.toNat_lt
  have := hst.2.1
  refine h.keep hs fun i hi hq ↦ ?_
  rw [NativeRustcVm.addr_add_zero, Sym.inRange_iff (by rw [hb]; omega), hb,
    NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by rw [hb]; omega), hb] at hq
  omega

variable [Host] {k : Nat}

/-- **A block without writes** in the frame. -/
theorem blk (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) {S' : SState} {x : Exit} (hx : exec b frS = some (S', x)) (hmem : S'.mem = [])
    (hsp : S'.sp = .ptr 0 0) (hst : StackOk m0 1184) {st : MachineState} {R : MachineState → Prop}
    (hfr : Frm m0 st.data) (hpc : st.pc = Host.addrOf (k + j))
    (cont : ∀ st', Frm m0 st'.data → st'.data.dmem = st.data.dmem →
      Match (frEnv m0 st.data) S' st'.data →
      PcOk (frEnv m0 st.data) x (Host.addrOf (k + j + b.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := frEnv_wf hst hfr
  have hm := frEnv_match hst hfr
  refine exec_at (infix_of hb hne hp) hx hwf hpc hm fun st' hm' hpc' ↦ ?_
  exact cont st' (Fr.ofBlock hfr hm hm' hwf rfl hmem (by rw [hsp]; rfl)
    fun r hr ↦ absurd hr (by simp)) (hm'.dmem_eq hwf hmem) hm' hpc'

/-- **A block writing the frame** below the slots. -/
theorem blkW (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) {S' : SState} {x : Exit} (hx : exec b frS = some (S', x))
    (hW : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ 96)
    (hsp : S'.sp = .ptr 0 0) (hst : StackOk m0 1184) {st : MachineState} {R : MachineState → Prop}
    (hfr : Frm m0 st.data) (hpc : st.pc = Host.addrOf (k + j))
    (cont : ∀ st', Frm m0 st'.data →
      SameOutside st.data.dmem st'.data.dmem (InRange (base m0 192 + BitVec.ofNat 64 0) 96) →
      Match (frEnv m0 st.data) S' st'.data →
      PcOk (frEnv m0 st.data) x (Host.addrOf (k + j + b.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := frEnv_wf hst hfr
  have hm := frEnv_match hst hfr
  refine exec_at (infix_of hb hne hp) hx hwf hpc hm fun st' hm' hpc' ↦ ?_
  refine cont st' (Fr.ofBlockW hfr hm hm' hwf rfl (by rw [hsp]; rfl)
    (fun r hr ↦ absurd hr (by simp)) rfl (by omega) hst.2.1 (by decide) fun w hw ↦ ?_)
    (Match.sameOutside_in hm' hwf (r0 := 0) (o := 0) (n := 96) rfl (by omega) fun w hw ↦
      ⟨(hW w hw).1, Nat.zero_le _, (hW w hw).2⟩) hm' hpc'
  left
  obtain ⟨h0, h1⟩ := hW w hw
  refine ⟨h0, by omega, fun p hp ↦ .inl ?_⟩
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **The epilogue**: `b19` from a state of the body, X0 the result. -/
theorem epi_run (hp : Placed code k) (G : Geo m0 bp B) {st : MachineState}
    (hb : Base m0 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b19Offset))
    (hres : ∀ m' : MachineData, SameOutside st.data.dmem m'.dmem (fun _ ↦ False) →
      m'.regs.X0 = st.data.regs.X0 → ∀ bp' B' c', ReaderAt m0.dmem (rdr m0) bp' B' c' →
      match phaseM B' c' with
      | some (po, c') => m'.regs.X0 = 1 ∧ PhaseAt m'.dmem (outA m0) (phaseW po) ∧
          ReaderAt m'.dmem (rdr m0) bp' B' c'
      | none => m'.regs.X0 = 0) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hst := G.st
  have hwf := frEnv_wf hst hb.fr
  have hm := frEnv_match hst hb.fr
  refine exec_at (infix_of b19_in_code (by simp [b19]) hp) run_b19 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  obtain ⟨hret, hsv⟩ := Fr.exit hb.fr hm' hwf (by decide +kernel)
  simp only [PcOk] at hpc'
  refine ⟨hpc'.trans hret, ?_, ?_, hsv⟩
  · exact hres st'.data (fun p _ ↦ by rw [hd]) (Match.reg_eq (r := .X0) hm hm' rfl rfl)
  · intro p hp
    rw [hd]
    refine hb.fr.same p fun h ↦ hp ?_
    rcases h with h | h | h | h
    · exact ⟨stackR m0 phaseMStack, by simp, h⟩
    · exact ⟨curRegion (rdr m0), by simp, h⟩
    · exact ⟨⟨outA m0, phaseBytes⟩, by simp, h⟩
    · exact ⟨⟨wk m0, workBytes⟩, by simp, h⟩

/-- **The way out with `None`.** -/
theorem none_run (hp : Placed code k) (G : Geo m0 bp B) {c : Nat}
    (hR : ReaderAt m0.dmem (rdr m0) bp B c) {st : MachineState} (h : AtNone m0 B c k st) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hpc, hb, hn⟩ := h
  refine blk hp b18_in_code (by simp [b18]) run_b18 rfl rfl G.st hb.fr hpc
    fun st1 hfr1 hd1 hm1 hpc1 ↦ ?_
  refine epi_run hp G (hb.of_regs hfr1 (regs_of (frEnv_match G.st hb.fr) hm1
    (by decide))) hpc1 fun m' _ h0 bp' B' c' hR' ↦ ?_
  obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
  rw [hn]
  rw [h0]
  apply UInt64.toBitVec_inj.mp
  exact (hm1.regs .X0 _ rfl).trans rfl

/-- **The way out after `write_openings`.** -/
theorem done_run (hp : Placed code k) (G : Geo m0 bp B) {c : Nat}
    (hR : ReaderAt m0.dmem (rdr m0) bp B c) {st : MachineState} (h : AtDone m0 bp B c k st) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hpc, hb, hx0, po, c', hph, hPh, hR'⟩ := h
  refine blk hp b37_in_code (by simp [b37]) run_b37 rfl rfl G.st hb.fr hpc
    fun st1 hfr1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  refine epi_run hp G (hb.of_regs hfr1 (regs_of (frEnv_match G.st hb.fr) hm1
    (by decide))) (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b19Offset) NativeRustcVmArm.Vm.PhaseM.label_13_at)) fun m' hs h0 bp' B' c'' hR'' ↦ ?_
  obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR''
  rw [hph]
  have hd : m'.dmem = st.data.dmem := by
    rw [← hd1]
    exact Std.ExtHashMap.ext_getElem? fun a ↦ by
      rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
      exact hs a id
  refine ⟨?_, by rw [hd]; exact hPh, by rw [hd]; exact hR'⟩
  rw [h0, ← hx0]
  exact Match.reg_eq (r := .X0) (frEnv_match G.st hb.fr) hm1 rfl rfl

end

end NativeRustcVmArm.Wire.PhaseM
