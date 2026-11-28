module

public import NativeRustcVmX64.Tables.TablePhase.Defs

/-!
# `table_phase`: blocks and the exit in the frame (x86-64)

`blk`: a block run from `stO o` in a state of the frame at offset `o` keeps the frame (its writes
in it below the return address). `exit8`: the epilogue `b8` returns AL as RBP's low byte.
-/

namespace NativeRustcVmX64.Tables.TablePhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Vm.TablePhase
open NativeRustcVmX64.Bus.Gkr (Fr)
open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)

public section

section
variable [Labels] {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW} {m0 : MachineData}

/-- The frame's environment of a state of the frame is well formed. -/
theorem wfF (h : TablePhasePre a s L bus m0) {o : Nat} {d : MachineData} (fr : St m0 o d)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 d 160 [] vars ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped (pre_parts h).1 N_ge) fr.frame.kept,
    frame_noWrap (pre_parts h).1 N_ge⟩ (by simp) (List.pairwise_singleton _ _)

/-- A state of the frame at offset `o` in its frame's environment. -/
theorem matchF {o : Nat} {d : MachineData} (fr : St m0 o d) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : Match (frameEnv m0 d 160 [] vars ret) (stO o) d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨fr.frame.sp.trans (eval_ptr0 o).symm, trivial⟩ trivial trivial
    trivial

/-- The frame below its return address is in the stack. -/
theorem frame_in (h : TablePhasePre a s L bus m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 160) 160 q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q :=
  (ctx h N_ge).inRange_frame hq

end

section
variable [Host] {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW} {m0 : MachineData}

/-- **A block** from a state of the frame at offset `o`. -/
theorem blk (h : TablePhasePre a s L bus m0) {o o' : Nat} {st : MachineState} (fr : St m0 o st.data)
    {ds : List Directive} {kk : Nat} {S' : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds (stO o) = some (S', x)) (hmid : MidOk 160 o' slots S' = true)
    (h0 : ∀ w ∈ S'.mem, w.r = 0) (hpc : st.pc = Host.addrOf kk) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, St m0 o' st'.data →
      Match (frameEnv m0 st.data 160 [] (fun _ ↦ 0) (Host.addrOf (kk + ds.length)).toBitVec) S'
        st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 160) 160) →
      PcOk (frameEnv m0 st.data 160 [] (fun _ ↦ 0) (Host.addrOf (kk + ds.length)).toBitVec) x
        (Host.addrOf (kk + ds.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := wfF h fr (vars := fun _ ↦ 0) (ret := (Host.addrOf (kk + ds.length)).toBitVec)
  refine exec_at hk hx hwf (fun _ _ ↦ rfl) hpc (matchF fr) fun st' hm hpc' ↦ ?_
  obtain ⟨fr', hs⟩ := fr.block0 (pre_parts h).1 N_ge hwf hm hmid slots_le h0
  exact cont st' fr' hm hs hpc'

/-- **The epilogue** `b8`: AL is RBP's low byte. -/
theorem exit8 {k : Nat} (hp : Placed code k) (h : TablePhasePre a s L bus m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b8Offset)) (fr : St m0 24 st.data)
    (hal : (reg st.data .rbp).toNat % 256 = (okWord ((tablePhase L bus).run s).isSome).toNat)
    (hev : ∀ x s', (tablePhase L bus).run s = some (x, s') →
      TableEvalsAt st.data.dmem (reg m0 .rcx) x)
    (hnx : NextAt st.data.dmem (reg m0 .rdi) a ((tablePhase L bus).run s)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
      TablePhasePost a s L bus m0 st'.data) st := by
  have hS := (pre_parts h).1
  have hwf := wfF h fr (vars := fun _ ↦ 0) (ret := 0)
  obtain ⟨hepi, hmem, hrax⟩ := after_eq run_b8 ▸ ok_b8
  refine Fr.exit fr hS N_ge (b8_in_code.trans hp.1 (by simp [b8])) run_b8 hwf hpc (matchF fr)
    hepi (fun q hw ↦ by obtain ⟨w, hw, -⟩ := hw; rw [hmem] at hw; cases hw)
    fun st' hm' hpc' hrsp hs0 _ hsv ↦ .done _ ⟨hpc', hrsp, ?_, ?_, ?_, ?_, hsv⟩
  · have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
    show (reg st'.data .rax).toNat % 256 = _
    rw [show reg st'.data .rax = _ from hm'.regs _ _ (hrax (.rax, .un .trunc .W32 (.reg .rbp)) (by simp))]
    exact (NativeRustcVmX64.Transcript.trunc32_mod _).trans hal
  · have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
    intro x s' hr; rw [hd]; exact hev x s' hr
  · have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
    intro x s' hr; rw [hd]; exact hnx x s' hr
  · refine NativeRustcVm.SameOutside.mono hs0 fun q hq ↦ ?_
    rcases hq with hq | hq | hq
    · exact .inr (.inr hq)
    · exact .inl hq
    · exact .inr (.inl hq)

end

end

end NativeRustcVmX64.Tables.TablePhase
