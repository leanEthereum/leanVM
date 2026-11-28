module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.OutChg

/-! # Calling an extension after the output buffer reset -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeVm.Model
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {inst : Array EW}

theorem stepHeader (hp : Placed NativeRustcVmX64.Vm.VerifyKeccak.code k) (c : Ctx a inst m0)
    (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0))
    {T S T' S' : SState} {vals vals' : Nat → BitVec 64} {o : Nat} {st : MachineState}
    (hat : At m0 k o wrAll T vals st) {ds : List Directive}
    (hds : ds.IsInfixAt NativeRustcVmX64.Vm.VerifyKeccak.code o) (hne : ds ≠ [])
    {l : Label} (hrun : exec ds S = some (S', .call l))
    (hm : ∀ ret, Match (envZ m0 st.data 3344 3368 (rsOf m0) vals ret) S st.data)
    (hw0 : headerW S' = true)
    {oc : Nat} (hoc : oc + 8 ≤ 3344) (hsp : S'.reg .rsp = some (.ptr 0 (oc : Int)))
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) {Sk : Nat} (hS : 3344 - oc + Sk ≤ verifyKeccakStack)
    (hP : ∀ mc, Match (envZ m0 st.data 3344 3368 (rsOf m0) vals
        (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc →
      CallAt m0 wrAll oc mc → StackOk mc Sk →
      Chg m0 st.data.dmem mc.dmem (wsL S') [(4, 0, 8)] →
      Kept st.data.dmem mc.dmem → P mc)
    (hQ : ∀ mc m', Match (envZ m0 st.data 3344 3368 (rsOf m0) vals
        (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc → Q mc m' →
      SameOutside mc.dmem m'.dmem (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨
        ChgR m0 [] [(4, 0, 584)] q) ∧ Saved mc m')
    (htm : tplMiss oc [] T' = true)
    (hok : tplOk T' = true) (hrspT : T'.reg .rsp = some (.ptr 0 ((oc + 8 : Nat) : Int)))
    {L LW : List (Nat × Sym)} (hL : rlinksOf true S' T' noRsp = some L)
    (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envZ m0 st.data 3344 3368 (rsOf m0) vals ret) = vals' p.1)
    (hax : T'.reg .rax = some (.reg .rax)) (hdx : T'.reg .rdx = some (.reg .rdx))
    (hsz : T'.regions = sizes) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : T'.aliases = []) (hbd : T'.bounds = [])
    {R : MachineState → Prop}
    (cont : ∀ st', At m0 k (o + ds.length) wrAll T' vals' st' →
      (∃ mc, Match (envZ m0 st.data 3344 3368 (rsOf m0) vals
          (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc ∧ Q mc st'.data ∧
        Chg m0 st.data.dmem mc.dmem (wsL S') [(4, 0, 8)]) →
      Chg m0 st.data.dmem st'.data.dmem (wsL S' ++ [(0, oc)]) [(4, 0, 8), (4, 0, 584)] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB⟩ := hat
  simp only at hpc hB hm hvals cont hP hQ
  subst hpc
  rw [← sizes_eq m0] at hsz
  have hwr := headerW_ok (m0 := m0) hw0
  have hwf := h.wf hB.kept (m := d) (vals := vals)
    (ret := (Host.addrOf (k + o + ds.length)).toBitVec)
  have hra : k + (o + ds.length) = k + o + ds.length := by omega
  rw [hra] at hP hQ cont
  refine callZ (hknown := hknown) (hwrites := h.written hwr)
    (W := fun _ ↦ ChgR m0 [] [(4, 0, 584)]) h hB (hds.trans hp.1 hne) hrun
    (hm _) hoc hsp hspec hS
    (fun mc hmc hk hsk hso hrsp ↦ hP mc hmc ⟨hrsp, hoc, hk, hso⟩ hsk
      (chg_header c hmc hwf hw0) (hmc.kept hwf)) hQ
    (fun _ _ q hq ↦ ChgR.wo c rfl (by decide) (by decide) hq)
    hok hrspT hL hLW (hvals _)
    (fun i hi ↦ nomatch tregE hax hi) (fun i hi ↦ nomatch tregE hdx hi)
    (fun _ _ j v t _ hf ↦ ChgR.wt c rfl (by decide) htm hf)
    hsz hfl hlab (fun _ _ _ _ _ hx ↦ by simp [hal] at hx)
    (fun _ _ _ _ hx ↦ by rw [hbd] at hx; cases hx)
    fun st' hpc' hB' ⟨mc, hmc, hrsp, hq, _⟩ ↦ ?_
  have hc1 := chg_header c hmc hwf hw0
  have hc2 := chg_call c hrsp (by omega) hS (hQ mc st'.data hmc hq).1
  exact cont st' ⟨by simpa only [Nat.add_assoc] using hpc', hB'⟩ ⟨mc, hmc, hq, hc1⟩
    (by simpa using hc1.trans hc2)
    (NativeRustcVmX64.Transcript.kept_trans (hmc.kept hwf) (hQ _ _ hmc hq).2.2)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
