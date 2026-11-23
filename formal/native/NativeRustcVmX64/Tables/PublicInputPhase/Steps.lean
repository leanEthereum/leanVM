module

public import NativeRustcVmX64.Tables.PublicInputPhase.Defs

/-!
# `public_input_phase`: blocks and the exit in the frame (x86-64)

`blk`: a block run from `stO o` keeps the frame; `blkPub`: one run from `pubS` (the public input
region 1 at R14). `exit9`: the epilogue `b9` returns AL as RBP's low byte.
-/

namespace NativeRustcVmX64.Tables.PublicInputPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Vm.PublicInputPhase
open NativeRustcVmX64.Bus.Gkr (Fr)
open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)
open NativeRustcVm.Layout (ClaimsWAt claimsBytes claimCap)

public section

section
variable [Labels] {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}

/-- The public input region's environment is well formed. -/
theorem wfPub (h : PublicInputPhasePre a s L pub cs m0) {o : Nat} {d : MachineData}
    (fr : St m0 o d) {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 d 608 [(reg m0 .rdx, 32)] vars ret).WF := by
  have p := pre_parts h
  have c := ctx h N_ge
  have hin := p.2.2.2.2.2.2.2.2.2.1
  refine frame_wf ⟨Mapped.keeps (frame_mapped p.1 N_ge) fr.frame.kept, frame_noWrap p.1 N_ge⟩
    (fun x hx ↦ ?_) (List.pairwise_pair.mpr ?_)
  · simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨Mapped.keeps hin.1.1 fr.frame.kept, hin.1.2⟩
  · exact Apart.symm' (apart_frame hin.2.1 c.spN N_ge)

end

section
variable [Host] {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}

/-- **A block** from a state of the frame at offset `o`. -/
theorem blk (h : PublicInputPhasePre a s L pub cs m0) {o o' : Nat} {st : MachineState}
    (fr : St m0 o st.data) {ds : List Directive} {kk : Nat} {S' : SState} {x : Exit}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds (stO o) = some (S', x))
    (hmid : MidOk 608 o' slots S' = true) (h0 : ∀ w ∈ S'.mem, w.r = 0)
    (hpc : st.pc = Host.addrOf kk) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, St m0 o' st'.data →
      Match (frameEnv m0 st.data 608 [] (fun _ ↦ 0) (Host.addrOf (kk + ds.length)).toBitVec) S'
        st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange (fb m0) 608) →
      PcOk (frameEnv m0 st.data 608 [] (fun _ ↦ 0) (Host.addrOf (kk + ds.length)).toBitVec) x
        (Host.addrOf (kk + ds.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := wfF h fr (vars := fun _ ↦ 0) (ret := (Host.addrOf (kk + ds.length)).toBitVec)
  refine exec_at hk hx hwf (fun _ _ ↦ rfl) hpc (matchF fr) fun st' hm hpc' ↦ ?_
  obtain ⟨fr', hs⟩ := fr.block0 (pre_parts h).1 N_ge hwf hm hmid slots_le h0
  exact cont st' fr' hm hs hpc'

/-- **A block reading the public input** (`pubS`), from a state of the frame at offset `8`. -/
theorem blkPub (h : PublicInputPhasePre a s L pub cs m0) {o' : Nat} {st : MachineState}
    (fr : St m0 8 st.data) (hr14 : reg st.data .r14 = reg m0 .rdx) {ds : List Directive}
    {kk : Nat} {S' : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds pubS = some (S', x)) (hmid : MidOk 608 o' slots S' = true)
    (h0 : ∀ w ∈ S'.mem, w.r = 0) (hpc : st.pc = Host.addrOf kk) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, St m0 o' st'.data →
      Match (frameEnv m0 st.data 608 [(reg m0 .rdx, 32)] (fun _ ↦ 0)
        (Host.addrOf (kk + ds.length)).toBitVec) S' st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange (fb m0) 608) →
      PcOk (frameEnv m0 st.data 608 [(reg m0 .rdx, 32)] (fun _ ↦ 0)
        (Host.addrOf (kk + ds.length)).toBitVec) x (Host.addrOf (kk + ds.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := wfPub h fr (vars := fun _ ↦ 0) (ret := (Host.addrOf (kk + ds.length)).toBitVec)
  have hm : Match (frameEnv m0 st.data 608 [(reg m0 .rdx, 32)] (fun _ ↦ 0)
      (Host.addrOf (kk + ds.length)).toBitVec) pubS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨fr.frame.sp.trans (eval_ptr0 8).symm, trivial⟩ trivial
      trivial ⟨by show reg st.data .r14 = _; rw [hr14]; simp, trivial⟩
  refine exec_at hk hx hwf (fun _ _ ↦ rfl) hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨fr', hs⟩ := fr.block0 (pre_parts h).1 N_ge hwf hm' hmid slots_le h0
  exact cont st' fr' hm' hs hpc'

/-- **The epilogue** `b9`: AL is RBP's low byte. -/
theorem exit9 {k : Nat} (hp : Placed code k) (h : PublicInputPhasePre a s L pub cs m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b9Offset)) (fr : St m0 8 st.data)
    (hal : (reg st.data .rbp).toNat % 256 =
      (okWord (((publicInputPhase L pub).run s).isSome && decide (cs.size + 2 ≤ claimCap))).toNat)
    (hcl : ∀ x s', (publicInputPhase L pub).run s = some (x, s') → cs.size + 2 ≤ claimCap →
      ClaimsWAt st.data.dmem (reg m0 .rcx) (cs ++ x))
    (hnx : NextAt st.data.dmem (reg m0 .rdi) a ((publicInputPhase L pub).run s)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
      PublicInputPhasePost a s L pub cs m0 st'.data) st := by
  have hS := (pre_parts h).1
  have hwf := wfF h fr (vars := fun _ ↦ 0) (ret := 0)
  obtain ⟨hepi, hmem, hrax⟩ := after_eq run_b9 ▸ ok_b9
  refine Fr.exit fr hS N_ge (b9_in_code.trans hp.1 (by simp [b9])) run_b9 hwf hpc (matchF fr)
    hepi (fun q hw ↦ by obtain ⟨w, hw, -⟩ := hw; rw [hmem] at hw; cases hw)
    fun st' hm' hpc' hrsp hs0 _ hsv ↦ .done _ ⟨hpc', hrsp, ?_, ?_, ?_, ?_, hsv⟩
  · show (reg st'.data .rax).toNat % 256 = _
    rw [show reg st'.data .rax = _ from
      hm'.regs _ _ (hrax (.rax, .un .trunc .W32 (.reg .rbp)) (by simp))]
    exact (NativeRustcVmX64.Transcript.trunc32_mod _).trans hal
  · have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
    intro x s' hr hf; rw [hd]; exact hcl x s' hr hf
  · have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
    intro x s' hr; rw [hd]; exact hnx x s' hr
  · refine NativeRustcVm.SameOutside.mono hs0 fun q hq ↦ ?_
    rcases hq with hq | hq | hq
    · exact .inr (.inr hq)
    · exact .inl hq
    · exact .inr (.inl hq)

end

end

end NativeRustcVmX64.Tables.PublicInputPhase
