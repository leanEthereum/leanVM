module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Out
public import NativeRustcVmX64.Code.Vm.Powers.Names

/-!
# `verify_stacked_opening`: the scales (x86-64)

`powers_b24`: from `NativeRustcVmX64.Vm.VerifyStackedOpening.label_19` (`AtB24`), `b24` reads the scales' address (the
stack argument `1`, `argScS`: the stack arguments as region 1), writes the count there and calls
`powers` (the challenge in RDI, RSI) into the scales: at `b25` (`AtB25`, the outputs `Outs`).
Helpers: the stack arguments' environment (`Parts.arg_ok`, `argAl_ok`, `Ok.argLoad`), the
`TState` across a step changing the stack and the outputs (`Parts.ts_keep`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

@[expose] public section

/-- **After the scales**, at `b25`. -/
structure AtB25 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 st : MachineData) : Prop where
  ok : Ok m0 st 8
  out : Outs a s layout cs m0 st.dmem
  fw : FW st.dmem m0 (fwL m0)
  r12 : reg st .r12 = off (scA m0) 8
  r14 : reg st .r14 = scA m0
  rbp : reg st .rbp = layA m0
  r13 : reg st .r13 = off (clA m0) 8
  r15 : (reg st .r15).toNat = cs.size

end

public section

theorem apart_shrink {x y : BitVec 64} {n m n' m' : Nat} (h : NativeRustcVm.Apart x n y m)
    (hn : n' ≤ n) (hm : m' ≤ m) : NativeRustcVm.Apart x n' y m' := by
  unfold NativeRustcVm.Apart at *
  omega

theorem arg_add (m0 : MachineData) (j : Nat) :
    stackBelow m0 512 + BitVec.ofNat 64 (520 + j) = rspOf m0 + 8#64 + BitVec.ofNat 64 j := by
  have := frame_add (m0 := m0) 512 (8 + j)
  rw [show 512 + (8 + j) = 520 + j by omega] at this
  rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
  exact this

/-- The stack arguments' aliases. -/
theorem argAl_ok [Labels] {m0 d : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    AllOf (fun p ↦ p.1.eval (frameEnv m0 d 512 ((rspOf m0 + 8#64, 24) :: rest) vars ret) =
      (frameEnv m0 d 512 ((rspOf m0 + 8#64, 24) :: rest) vars ret).base p.2.1 +
        BitVec.ofInt 64 p.2.2) argAl := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · show stackBelow m0 512 + BitVec.ofInt 64 520 = rspOf m0 + 8#64 + BitVec.ofInt 64 0
    rw [show BitVec.ofInt 64 520 = BitVec.ofNat 64 (520 + 0) from rfl,
      show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl]
    exact arg_add m0 0
  · show stackBelow m0 512 + BitVec.ofInt 64 528 = rspOf m0 + 8#64 + BitVec.ofInt 64 8
    rw [show BitVec.ofInt 64 528 = BitVec.ofNat 64 (520 + 8) from rfl,
      show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
    exact arg_add m0 8
  · show stackBelow m0 512 + BitVec.ofInt 64 536 = rspOf m0 + 8#64 + BitVec.ofInt 64 16
    rw [show BitVec.ofInt 64 536 = BitVec.ofNat 64 (520 + 16) from rfl,
      show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl]
    exact arg_add m0 16

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

/-- The stack arguments: mapped, not wrapping, apart from the stack. -/
theorem Parts.arg_ok : NativeRustcVm.Mapped m0.dmem (rspOf m0 + 8#64) 24 ∧
    NativeRustcVm.NoWrap (rspOf m0 + 8#64) 24 ∧
    NativeRustcVm.Apart (rspOf m0 + 8#64) 24 (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8) := by
  have hR := h.rsp
  have hs := h.sb
  have e : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  refine ⟨h.args.1, by unfold NativeRustcVm.NoWrap; omega, ?_⟩
  unfold NativeRustcVm.Apart
  rw [e, hs, stack_eq]
  omega

/-- A stack argument, loaded from region 1. -/
theorem Ok.argLoad {st : MachineData} {o : Nat} (hok : Ok m0 st o) {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {i : Nat} (hi : i < 3) :
    (frameEnv m0 st 512 ((rspOf m0 + 8#64, 24) :: rest) vars ret).load 1 (8 * i) 8 =
      stackArg m0 i :=
  load_ofMachine (r := 1) rfl (hok.arg h hi)

/-- **The `TState`** across a step changing the stack, the scales and the `WhirW` only. -/
theorem Parts.ts_keep {d d' : Mem 64} {s' : TState} (hts : TStateAt d (tA m0) a s')
    (hk : Keeps d d') {R : BitVec 64 → Prop}
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack)
      verifyStackedOpeningStack q ∨ NativeRustcVm.InRange (scA m0) scalesBytes q ∨
        NativeRustcVm.InRange (pA m0) whirBytes q)
    (hs : NativeRustcVm.SameOutside d d' R) : TStateAt d' (tA m0) a s' := by
  have hsnw := noWrap_stackBelow h.wt.1
  have hdn := hts.footprint.2.1.2
  refine hts.frame hk (fun q hq ↦ ?_) hs
  rcases hR q hq with hq | hq | hq
  · exact ⟨fun ht ↦ h.outs_not_stack (.inr (.inr ht)) hq,
      fun hd ↦ not_inRange_of_apart h.wt.2.2.2.1.2.1 hdn hsnw hd (inRange_mono hq (by omega))⟩
  · exact ⟨fun ht ↦ not_inRange_of_apart h.so.1.2.2.1 h.sc_nw h.t_nat.1 hq ht,
      fun hd ↦ not_inRange_of_apart h.so.1.2.2.2.1 h.sc_nw hdn hq hd⟩
  · exact ⟨fun ht ↦ not_inRange_of_apart h.po.1.2.2.1 h.p_nat.1 h.t_nat.1 hq ht,
      fun hd ↦ not_inRange_of_apart h.po.1.2.2.2.1 h.p_nat.1 hdn hq hd⟩

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **A block** writing the frame and an output area (region `i`), from a state of the frame
(RSP at offset `8`). -/
theorem Parts.runOut (h : Parts a s layout target coefficients point slices cs z value m0)
    {F : List Directive} (hp : Placed F k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt F j)
    (hne : b ≠ []) {st : MachineState} (hpc : st.pc = Host.addrOf (k + j))
    (hok : Ok m0 st.data 8) {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    (hwf : (frameEnv m0 st.data 512 rest vars
      (Host.addrOf (k + j + b.length)).toBitVec).WF)
    {S S' : SState} {x : Exit}
    (hm : Match (frameEnv m0 st.data 512 rest vars (Host.addrOf (k + j + b.length)).toBitVec)
      S st.data)
    (hrun : exec b S = some (S', x)) {o : Nat} (hS : MidOk 512 o slots S' = true)
    {i n : Nat} {y : BitVec 64}
    (hi : (frameEnv m0 st.data 512 rest vars (Host.addrOf (k + j + b.length)).toBitVec).regions[i]?
      = some (y, n))
    (hy : ∀ q, NativeRustcVm.InRange y n q → outs m0 q) (hW : outW i n S' = true)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, Ok m0 st'.data o →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (fun q ↦ NativeRustcVm.InRange (stackBelow m0 512) 512 q ∨ NativeRustcVm.InRange y n q) →
      Match (frameEnv m0 st.data 512 rest vars (Host.addrOf (k + j + b.length)).toBitVec) S'
        st'.data →
      PcOk (frameEnv m0 st.data 512 rest vars (Host.addrOf (k + j + b.length)).toBitVec) x
        (Host.addrOf (k + j + b.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at (infix_of hb hne hp) hrun hwf (fun _ _ ↦ rfl) hpc hm fun st' hm' hpc' ↦
    have hb' := hok.blockOut h hwf hm' hS hi hy hW
    cont st' hb'.1 hb'.2 hm' hpc'

/-- **The scales**: `b24` and `powers`, to `b25`. -/
theorem powers_b24 (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) (hpow : Spec (Labels.label NativeRustcVmX64.Vm.Powers.entryLabel) PowersPre PowersPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b24Offset))
    (hA : AtB24 a s layout cs m0 st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b25Offset) → AtB25 a s layout cs m0 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hA.ok
  have hP := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans h.n_le
  have hsb : scalesBytes = 2600 := rfl
  have hscn := h.sc_nw
  have hsc8 := h.sc8_le (layout := layout)
  have hR0 := h.rsp
  have hsbe := h.sb
  obtain ⟨ham, hanw, haap⟩ := h.arg_ok
  have hscap : NativeRustcVm.Apart (scA m0) scalesBytes (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8) := h.so.1.2.2.2.2.1
  have hwf : ∀ ret, (frameEnv m0 st.data 512 [(rspOf m0 + 8#64, 24), (scA m0, 8)] (fun _ ↦ 0)
      ret).WF := fun _ ↦
    hok.wf2 h ham hanw haap (fun i hi ↦ h.so.1.1 i (by omega))
      (by unfold NativeRustcVm.NoWrap at hscn ⊢; omega) (apart_shrink hscap (by omega) le_rfl)
      (apart_shrink h.argsc le_rfl (by omega))
  have hload : ∀ ret, (frameEnv m0 st.data 512 [(rspOf m0 + 8#64, 24), (scA m0, 8)] (fun _ ↦ 0)
      ret).load 1 8 8 = scA m0 := fun _ ↦ hok.argLoad h (i := 1) (by omega)
  have hm : ∀ ret, Match (frameEnv m0 st.data 512 [(rspOf m0 + 8#64, 24), (scA m0, 8)]
      (fun _ ↦ 0) ret) argScS st.data := fun ret ↦
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hok.fr.rsp_eval, trivial⟩ trivial trivial
      (by
        refine ⟨argAl_ok.1, argAl_ok.2.1, argAl_ok.2.2.1, ?_, trivial⟩
        show (frameEnv m0 st.data 512 _ (fun _ ↦ 0) ret).load 1 8 8 = scA m0 + BitVec.ofInt 64 0
        rw [hload, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero])
  refine h.runOut hp b24_in_code (List.cons_ne_nil _ _) hpc hok (hwf _) (hm _) run_b24 (o := 0)
    (by decide +kernel) (i := 2) rfl (fun q hq ↦ .inr (.inl (inRange_mono hq (by omega))))
    (by decide +kernel) fun st1 hok1 hs1 hm1 hpc1 ↦ ?_
  have hN : 512 + powersStack ≤ verifyStackedOpeningStack := by rw [stack_eq]; decide
  -- the registers `b24` sets
  have e_dx : reg st1.data .rdx = off (scA m0) 8 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ rfl, eval_add64]
    show (frameEnv m0 st.data 512 _ (fun _ ↦ 0) _).load 1 8 8 + _ = _
    rw [hload]
    rfl
  have e_12 : reg st1.data .r12 = off (scA m0) 8 := by
    rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ rfl, eval_add64]
    show (frameEnv m0 st.data 512 _ (fun _ ↦ 0) _).load 1 8 8 + _ = _
    rw [hload]
    rfl
  have e_14 : reg st1.data .r14 = scA m0 := by
    rw [show reg st1.data .r14 = _ from hm1.regs .r14 _ rfl]
    exact hload _
  have e_cx : (reg st1.data .rcx).toNat = cntOf layout cs := by
    rw [show reg st1.data .rcx = reg st.data .rbx from hm1.regs .rcx _ rfl]; exact hA.rbx
  have e_di : reg st1.data .rdi = (sq s).1.c0.toBitVec :=
    (show reg st1.data .rdi = reg st.data .rax from hm1.regs .rdi _ rfl).trans hA.rax
  have e_si : reg st1.data .rsi = (sq s).1.c1.toBitVec :=
    (show reg st1.data .rsi = reg st.data .rdx from hm1.regs .rsi _ rfl).trans hA.rdx
  -- the count word
  have hscw1 : NativeRustcVm.WordAt st1.data.dmem (scA m0) (cntOf layout cs).toUInt64 := by
    have := wordAt_write hm1 (r := 2) (b := scA m0) (sz := 8) rfl (o := 0) (by omega)
      (v := .reg .rbx) (by decide +kernel)
    rw [off_zero] at this
    rw [← ofBitVec_eq (x := reg st.data .rbx) hA.rbx]
    exact this
  have hts1 := h.ts_keep hA.ts (hm1.kept (hwf _)) (R := fun q ↦
    NativeRustcVm.InRange (stackBelow m0 512) 512 q ∨ NativeRustcVm.InRange (scA m0) 8 q)
    (fun q hq ↦ hq.elim (fun h' ↦ .inl (h.frame_stack h'))
      fun h' ↦ .inr (.inl (inRange_mono h' (by omega)))) hs1
  have hfw1 := FW.block_os (hwf _) hm1 rfl hA.fw [24, 40, 48, 56, 64] rfl (by decide +kernel)
  -- `powers`
  have hpre : PowersPre st1.data := by
    refine ⟨hok1.stackOk h hN, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rw [e_dx, e_cx]
      exact mapped_off (Mapped.keeps h.so.1.1 hok1.fr.kept) hsc8
    · rw [e_dx, e_cx]
      exact noWrap_off' hscn (by unfold cntOf; omega) hsc8
    · show NativeRustcVm.Apart _ _ _ _
      rw [e_dx, e_cx]
      refine apart_callee ?_ (Ok.sp hok1) h.wt.1.1 hN
      unfold NativeRustcVm.Apart at hscap ⊢
      rw [toNat_off (by unfold NativeRustcVm.NoWrap at hscn; omega)]
      omega
  refine call_then (P := PowersPre) (Q := PowersPost) hpc1 hpow hpre
    fun st2 hpc2 hrsp2 ⟨hews, hch, hsv⟩ ↦ ?_
  rw [e_dx, e_cx, e_di, e_si] at hews
  rw [e_dx, e_cx] at hch
  obtain ⟨hok2, hfs2⟩ := hok1.call h hsv hrsp2 (N' := powersStack) hN
    (Rw := NativeRustcVm.InRange (off (scA m0) 8) (16 * cntOf layout cs))
    (fun q hq ↦ .inr (.inl (inRange_of_off hscn hsc8 hq))) hch
  have hts2 := h.ts_keep hts1 hsv.2 (R := fun q ↦
    NativeRustcVm.InRange (off (scA m0) 8) (16 * cntOf layout cs) q ∨
      NativeRustcVm.InRange (stackBelow st1.data powersStack) powersStack q)
    (fun q hq ↦ hq.elim (fun h' ↦ .inr (.inl (inRange_of_off hscn hsc8 h')))
      fun h' ↦ .inl (h.callee_stack (Ok.sp hok1) hN h').1) hch
  have hscw2 : NativeRustcVm.WordAt st2.data.dmem (scA m0) (cntOf layout cs).toUInt64 := by
    refine NativeRustcVm.BytesAt.of_sameOutside hscw1 hch fun i hi hq ↦ ?_
    rw [NativeRustcVm.length_wordBytes] at hi
    have hq0 : NativeRustcVm.InRange (scA m0) scalesBytes (scA m0 + BitVec.ofNat 64 i) :=
      NativeRustcVm.inRange_add (by omega) (by unfold NativeRustcVm.NoWrap at hscn; omega)
    rcases hq with hq | hq
    · have ho : (off (scA m0) 8).toNat = (scA m0).toNat + 8 :=
        toNat_off (by unfold NativeRustcVm.NoWrap at hscn; omega)
      have hq' : NativeRustcVm.InRange (off (scA m0) 8) (16 * cntOf layout cs)
          (scA m0 + BitVec.ofNat 64 i) := hq
      rw [inR (noWrap_off' hscn (by unfold cntOf; omega) hsc8), ho,
        NativeRustcVm.toNat_add_ofNat (by unfold NativeRustcVm.NoWrap at hscn; omega)] at hq'
      omega
    · exact h.outs_not_stack (.inr (.inl hq0)) (h.callee_stack (Ok.sp hok1) hN hq).1
  have rr : ∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r := hsv.1
  refine cont st2 (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b24_next))
    ⟨hok2, ⟨hts2, hscw2, hews⟩, hfw1.call hfs2 (le_of_map [24, 40, 48, 56, 64] rfl (by decide)),
      by rw [rr .r12 rfl]; exact e_12, by rw [rr .r14 rfl]; exact e_14,
      by rw [rr .rbp rfl, regKeep hm1 .rbp rfl]; exact hA.rbp,
      by rw [rr .r13 rfl, regKeep hm1 .r13 rfl]; exact hA.r13,
      by rw [rr .r15 rfl, regKeep hm1 .r15 rfl]; exact hA.r15⟩

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
