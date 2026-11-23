module

public import NativeRustcVmX64.Whir.FoldRound.Grind
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `fold_round` on x86-64: a block and a call of `EW::mul` or `squeeze`

`mulCall`: from a body state, a block writing the frame and ending in `EW::mul`, then the call:
a body state with the product of the block's registers in RAX, RDX, the callee-saved registers
and the frame's words the block's. `sqCall`: the same with `squeeze` of the `TState`'s sponge.
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn)
open NativeRustcVm (WordAt EWAt EWsAt)

public section

theorem kept_sub {S : SState} {l l' : List Reg64} (h : kept S l = true) (hs : ∀ r ∈ l', r ∈ l) :
    ∀ r ∈ l', S.reg r = some (.reg r) := fun r hr ↦ kept_spec h (hs r hr)

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- **A block and `EW::mul`**, the block from `S0` in the frame and the areas `rest`. -/
theorem mulCall (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {s : TState} {st : MachineState}
    {j : Nat} (hpc : st.pc = Host.addrOf (k + j)) (hb : Bd m0 a s st.data) {b : List Directive}
    (hbi : b.IsInfixAt code j) (hne : b ≠ []) {rest : List (BitVec 64 × Nat)} {S0 S : SState}
    (hwf : (frameEnv m0 st.data 176 rest (fun _ ↦ 0) (Host.addrOf (k + j + b.length)).toBitVec).WF)
    (hm0 : Match (frameEnv m0 st.data 176 rest (fun _ ↦ 0) (Host.addrOf (k + j + b.length)).toBitVec)
      S0 st.data)
    (hrun : exec b S0 = some (S, .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (hmid : MidOk 176 0 slots S = true) (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 176)
    (hregs : ∀ st1 : MachineData, Match (frameEnv m0 st.data 176 rest (fun _ ↦ 0)
      (Host.addrOf (k + j + b.length)).toBitVec) S st1 →
      reg st1 .rbx = reg st.data .rbx ∧ reg st1 .r14 = reg st.data .r14)
    (cont : ∀ (st1 : MachineData) (st' : MachineState),
      Match (frameEnv m0 st.data 176 rest (fun _ ↦ 0) (Host.addrOf (k + j + b.length)).toBitVec) S
        st1 →
      st'.pc = Host.addrOf (k + j + b.length) → Bd m0 a s st'.data →
      reg st'.data .rax = (EW.mul ⟨.ofBitVec (reg st1 .rdi), .ofBitVec (reg st1 .rsi)⟩
        ⟨.ofBitVec (reg st1 .rdx), .ofBitVec (reg st1 .rcx)⟩).c0.toBitVec →
      reg st'.data .rdx = (EW.mul ⟨.ofBitVec (reg st1 .rdi), .ofBitVec (reg st1 .rsi)⟩
        ⟨.ofBitVec (reg st1 .rdx), .ofBitVec (reg st1 .rcx)⟩).c1.toBitVec →
      (∀ r, calleeSaved r = true → reg st'.data r = reg st1 r) →
      (∀ {o : Nat} {v : UInt64}, o + 8 ≤ 176 → WordAt st1.dmem (off (fb m0) o) v →
        WordAt st'.data.dmem (off (fb m0) o) v) →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  refine exec_at (inf hp hbi hne) hrun hwf (fun _ _ ↦ rfl) hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hat, hs1⟩ := WFr.atCall cx hb.fr hb.ts hwf hm1 hmid slots_le hS
  have hmem1 := mem_trans hb.mem hs1 fun q hq ↦ .inl (cx.frame_stack hq)
  refine hat.ewMul cx hmul slots_le mul_le hpc1 fun st2 hpc2 hw2 hts2 hax hdx hcs hso ↦
    cont st1.data st2 hm1 hpc2 ⟨hw2, mem_trans hmem1 hso fun q hq ↦ .inl hq.1, hts2,
      (hcs .rbx rfl).trans ((hregs _ hm1).1.trans hb.rbx),
      (hcs .r14 rfl).trans ((hregs _ hm1).2.trans hb.r14)⟩
      hax hdx hcs fun ho hv ↦ frame_keep hso (fun i hi ↦ (frame_not_call h (x := _ + i)
        (by omega)).1) hv

/-- **A block and `squeeze`.** -/
theorem sqCall (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {s : TState} {st : MachineState}
    {j : Nat} (hpc : st.pc = Host.addrOf (k + j)) (hb : Bd m0 a s st.data) {b : List Directive}
    (hbi : b.IsInfixAt code j) (hne : b ≠ []) {S : SState}
    (hrun : exec b midS = some (S, .call NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel))
    (hmid : MidOk 176 0 slots S = true) (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 176)
    (hk : ∀ r ∈ [Reg64.rbx, .r13, .r14], S.reg r = some (.reg r))
    (hdi : S.reg .rdi = some (.reg .r13))
    (h13 : reg st.data .r13 = tA m0)
    (cont : ∀ (st1 : MachineData) (st' : MachineState),
      Match (frameEnv m0 st.data 176 [] (fun _ ↦ 0) (Host.addrOf (k + j + b.length)).toBitVec) S
        st1 →
      st'.pc = Host.addrOf (k + j + b.length) → Bd m0 a (sq s).2 st'.data →
      reg st'.data .rax = (sq s).1.c0.toBitVec → reg st'.data .rdx = (sq s).1.c1.toBitVec →
      (∀ r, calleeSaved r = true → reg st'.data r = reg st1 r) →
      (∀ {o : Nat} {v : UInt64}, o + 8 ≤ 176 → WordAt st1.dmem (off (fb m0) o) v →
        WordAt st'.data.dmem (off (fb m0) o) v) →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  have cx := ctx h
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + j + b.length)).toBitVec)
    hb.fr.fr.kept
  refine exec_at (inf hp hbi hne) hrun hwf (fun _ _ ↦ rfl) hpc hb.fr.mid fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hat, hs1⟩ := WFr.atCall cx hb.fr hb.ts hwf hm1 hmid slots_le hS
  have hmem1 := mem_trans hb.mem hs1 fun q hq ↦ .inl (cx.frame_stack hq)
  refine hat.squeeze cx hsq slots_le sq_le ((hm1.regs .rdi _ hdi).trans h13) hpc1
    fun st2 hpc2 hw2 hts2 hax hdx hcs hso ↦
    cont st1.data st2 hm1 hpc2 ⟨hw2, mem_trans hmem1 hso fun q hq ↦ hq.elim (fun h ↦ .inl h.1) .inr,
      hts2, (hcs .rbx rfl).trans ((hm1.regs .rbx _ (hk _ (by simp))).trans hb.rbx),
      (hcs .r14 rfl).trans ((hm1.regs .r14 _ (hk _ (by simp))).trans hb.r14)⟩
      hax hdx hcs fun ho hv ↦ frame_keep hso (fun i hi hq ↦ hq.elim
        (frame_not_call h (x := _ + i) (by omega)).1 (frame_not_call h (x := _ + i) (by omega)).2) hv

end

end NativeRustcVmX64.Whir.FoldRound
