module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Whir.FoldRound.Tail1

/-!
# `fold_round`: a block of the frame then `EW::mul`

`mstep`: a block from `midS` writing the frame off the slots and ending in `bl EW::mul`, then the
call. `Tb`: what the tail keeps (the frame, the output and the state in X19, X20, the state, the
`TState`), kept by such a step (`Tb.step`).
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

section
variable [Labels]

/-- What the tail keeps. -/
structure Tb (a : DecArea) (w : WhirStateW) (m0 : MachineData) (s : TState) (st : MachineData) :
    Prop where
  fr : FFr m0 st
  x19 : st.regs.X19 = m0.regs.X0
  x20 : st.regs.X20 = m0.regs.X2
  ws : WhirStateAt st.dmem (pA m0) w
  ts : TStateAt st.dmem (tA m0) a s

end

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

/-- **The `TState` kept** by a callee writing its stack only. -/
theorem ts_stack (h : FoldRoundPre a s0 w m0) {st : MachineData} (hf : FFr m0 st) {N' : Nat}
    (hle : 208 + N' ≤ foldRoundStack) {s : TState} (hts : TStateAt st.dmem (tA m0) a s)
    {d' : Mem 64} (hk : Kept st.dmem d')
    (hs : SameOutside st.dmem d' (InRange (stackBelow st N') N')) : TStateAt d' (tA m0) a s := by
  have htok := (ctx h).tstateOk hf hle
  have hS := (ctx h).stackOk hf hle
  have hfp := hts.footprint
  have hnt : NoWrap (tA m0) tstateBytes := hfp.1.2
  have hnd : NoWrap a.words (8 * a.len) := hfp.2.1.2
  have hnws : NoWrap (stackBelow st N') N' := by
    have h1 : N' ≤ st.regs.SP.toBitVec.toNat := hS.2.1
    have h2 := st.regs.SP.toBitVec.isLt
    unfold NoWrap stackBelow
    rw [NativeRustcVm.toNat_sub_ofNat h1]
    omega
  exact hts.frame hk (fun q hq ↦ ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange htok.1 hnt hnws ht hq,
    fun hd ↦ NativeRustcVm.Apart.not_inRange htok.2.1 hnd hnws hd hq⟩) hs

/-- **A block of the frame, then `EW::mul`.** -/
theorem mstep (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {ds : List Directive} {j : Nat}
    (hk : ds.IsInfixAt code j) (hne : ds ≠ []) {S' : SState}
    (hx : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel)) (hsp : S'.sp = .ptr 0 0)
    (hfw : frameWrites S' 208 slots [] = true)
    (hmem : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ 208)
    (h19 : S'.reg .X19 = some (.reg .X19)) (h20 : S'.reg .X20 = some (.reg .X20))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) {s : TState}
    (hb : Tb a w m0 s st.data) {R : MachineState → Prop}
    (cont : ∀ st1 : MachineState, ∀ m2, Match (frameEnv m0 st.data) S' st1.data →
      FFr m0 st1.data → Tb a w m0 s m2 →
      m2.regs.X0 = (EW.mul ⟨st1.data.regs.X0, st1.data.regs.X1⟩
        ⟨st1.data.regs.X2, st1.data.regs.X3⟩).c0 →
      m2.regs.X1 = (EW.mul ⟨st1.data.regs.X0, st1.data.regs.X1⟩
        ⟨st1.data.regs.X2, st1.data.regs.X3⟩).c1 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st1.data.regs.getXReg r) →
      SameOutside st1.data.dmem m2.dmem (InRange (stackBelow st1.data ewMulStack) ewMulStack) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + j + ds.length)⟩) :
    Eventually (step1 Host.exe) R st := by
  have hwf := frame_wf h hb.fr
  have hm := frame_match h hb.fr
  refine exec_at (inf hp hk hne) hx hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hs1 : SameOutside st.data.dmem st1.data.dmem (InRange (base m0 208) 208) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦ written_r0 hwf rfl hmem hq
  have hf1 : FFr m0 st1.data := Fr.ofBlockW hb.fr hm hm1 hwf rfl (by rw [hsp]; rfl)
    (fun _ h ↦ absurd h (by simp)) rfl (by decide) (pre_hN h) slots_le
    (writeOk_of (F := 208) (slots := slots) (wr := []) hm1 hfw (fun _ h ↦ by cases h))
  have hb1 : Tb a w m0 s st1.data :=
    ⟨hf1, (reg_of hm1 h19 rfl).trans hb.x19, (reg_of hm1 h20 rfl).trans hb.x20,
      ws_keep h hb.ws hs1 fun q hq ↦ frame_away h hq,
      hb.ts.frame (hm1.kept hwf) (fun q hq ↦ frame_not_t h hq) hs1⟩
  have hle : 208 + ewMulStack ≤ foldRoundStack := by decide
  refine mul_call h hmul hf1 hpc1 fun m2 hf2 h0 h1 hcs hs hk ↦ cont st1 m2 hm1 hf1 ?_ h0 h1 hcs hs
  exact ⟨hf2, (hcs .X19 rfl).trans hb1.x19, (hcs .X20 rfl).trans hb1.x20,
    ws_keep h hb1.ws hs fun q hq ↦ .inl (stack_sub h hf1 hle hq),
    ts_stack h hf1 hle hb1.ts hk hs⟩

omit [Host] in
theorem mul_le : 208 + ewMulStack ≤ foldRoundStack := by decide

/-- **Frame words** across a block missing them and a call to `EW::mul`. -/
theorem fw_through (h : FoldRoundPre a s0 w m0) {st st1 m2 : MachineData} {S' : SState}
    (hf : FFr m0 st) (hm1 : Match (frameEnv m0 st) S' st1) (hf1 : FFr m0 st1)
    (hs : SameOutside st1.dmem m2.dmem (InRange (stackBelow st1 ewMulStack) ewMulStack))
    {L : List (Nat × UInt64)} {os : List Nat} (hos : L.map Prod.fst = os)
    (hmiss : os.all (fun o ↦ missFrame S' o 8 && decide (o + 8 ≤ 208)) = true)
    (hw : FW st.dmem m0 L) : FW m2.dmem m0 L := by
  subst hos
  rw [List.all_map] at hmiss
  have hL : ∀ p ∈ L, p.1 + 8 ≤ 208 := fun p hp ↦ by
    simp only [List.all_eq_true, Function.comp_apply, Bool.and_eq_true,
      decide_eq_true_eq] at hmiss
    exact (hmiss p hp).2
  exact fw_call h hf1 mul_le (NativeRustcVm.SameOutside.mono hs fun _ hq ↦ .inl hq) hL
    (fw_block hm1 (frame_wf h hf) rfl hmiss hw)

/-- **A frame word** a block writes, across the call to `EW::mul`. -/
theorem fw_new (h : FoldRoundPre a s0 w m0) {st st1 m2 : MachineData} {S' : SState}
    (hm1 : Match (frameEnv m0 st) S' st1) (hf1 : FFr m0 st1)
    (hs : SameOutside st1.dmem m2.dmem (InRange (stackBelow st1 ewMulStack) ewMulStack))
    {o : Nat} (ho : o + 8 ≤ 208) {v : Sym}
    (hw : ∀ i < 8, findWrite 0 (o + i) S'.mem = some (v, i)) {x : UInt64}
    (hx : v.eval (frameEnv m0 st) = x.toBitVec) : FW m2.dmem m0 [(o, x)] :=
  fw_call h hf1 mul_le (NativeRustcVm.SameOutside.mono hs fun _ hq ↦ .inl hq) (by simpa using ho)
    (FW.cons (by have := fw_write hm1 rfl ho hw; rwa [hx] at this) (FW.nil _ _))

end

end NativeRustcVmArm.Whir.FoldRound
