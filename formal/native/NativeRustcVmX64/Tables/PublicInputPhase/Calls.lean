module

public import NativeRustcVmX64.Tables.PublicInputPhase.Words
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names

/-!
# `public_input_phase`: a limb's value and claim (x86-64)

`mleStep`: from `b3`/`b6` (the public input's words `i`, `2 + i` into the frame's offset `32`, the
challenge at `16`), `multilinear_eval_by` returns the limb's value. `pushStep`: from `b4`/`b7`,
`push_claim` appends the claim on column `col` at the point `pt` with that value. What both keep
(the `TState`, the claims, the point's words, the callee-saved registers).
-/

namespace NativeRustcVmX64.Tables.PublicInputPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmX64.Vm.PublicInputPhase
open NativeRustcVmX64.Bus.Gkr (Fr)
open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)
open NativeRustcVm.Layout (LayoutWAt layoutBytes Same ClaimsWAt claimsBytes claimCap pointCap)
open NativeRustcVm (wordOf ewsOf)
open NativeRustcVmX64.Arrays (eval_load eval_reg)

public section

section
variable [Labels] {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}

/-- **The claims kept** where the memory changed only in the stack. -/
theorem claims_keep (h : PublicInputPhasePre a s L pub cs m0) {d d' : DataMem}
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 N) N q) {cs' : Array ColumnClaimW}
    (hc : ClaimsWAt d (reg m0 .rcx) cs') : ClaimsWAt d' (reg m0 .rcx) cs' := by
  have c := ctx h N_ge
  have ho := (pre_parts h).2.2.2.2.1
  refine NativeRustcVm.Tables.ClaimsWAt.of_same hc fun j hj ↦ hs _ fun hq ↦ ?_
  exact NativeRustcVm.Apart.not_inRange_add ho.2.2.2.2.1 ho.2.1 c.noWrap_stack hj
    (inRange_mono (hR _ hq) (by omega))

/-- The public input's word `o / 8` as the block's environment loads it. -/
theorem load_pub (h : PublicInputPhasePre a s L pub cs m0) {o : Nat} {d : MachineData}
    (fr : St m0 o d) {ret : BitVec 64} {i : Nat} (hi : i < 4) :
    UInt64.ofBitVec ((frameEnv m0 d 608 [(reg m0 .rdx, 32)] (fun _ ↦ 0) ret).load 1 (8 * i) 8) =
      pub[i] := by
  have p := pre_parts h
  have hw : NativeRustcVm.WordsAt d.dmem (reg m0 .rdx) pub.toList :=
    NativeRustcVm.Tables.WordsAt.of_same p.2.2.2.2.2.2.2.2.2.2 (same_in h fr p.2.2.2.2.2.2.2.2.2.1)
      (by simp)
  have hi' : i < pub.toList.length := by simp; omega
  rw [NativeRustcVmX64.Arrays.load8_eq, Env.base_eq (b := reg m0 .rdx) (n := 32) rfl,
    Env.ofMachine_mem0, UInt64.ofBitVec_toBitVec, NativeRustcVm.wordOf_of_wordAt (hw.getElem hi')]
  simp

end

theorem le_mle : 608 + mleStack ≤ N := by decide
theorem le_push : 608 + pushClaimStack ≤ N := by decide

/-- The callee-saved registers. -/
theorem calleeSaved_cases {r : Reg64} (h : calleeSaved r = true) :
    r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 := by
  have := NativeRustcVmX64.Arrays.mem_calleeRegs h
  simpa [NativeRustcVmX64.Arrays.calleeRegs] using this

section
variable [Host] {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}


/-- **A limb's value**: `b3`/`b6` (`D`, at `kk`, the public input's words `2 i`, `2 i + 1` at
offsets `8 i`, `8 i + 16` of the input), then `multilinear_eval_by`. -/
theorem mleStep (h : PublicInputPhasePre a s L pub cs m0) {st : MachineState} (fr : St m0 8 st.data)
    (hr14 : reg st.data .r14 = reg m0 .rdx) {ch : EW} (hr15 : reg st.data .r15 = ch.c0.toBitVec)
    (hr12 : reg st.data .r12 = ch.c1.toBitVec) {i : Nat} (hi : i < 2) {D : List Directive}
    {kk : Nat} {S' : SState} (hk : D.IsInfixAt Host.prog kk)
    (hx : exec D pubS = some (S', .call NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel))
    (hmid : MidOk 608 0 slots S' = true) (hin0 : ∀ w ∈ S'.mem, w.r = 0)
    (hregs : RegsAre S' [(.rcx, .ptr 0 16), (.rdx, .lit 2), (.rsi, .ptr 0 32), (.rdi, .lit 2),
      (.r8, .lit 1), (.rbp, .reg .rbp), (.rbx, .reg .rbx), (.r12, .reg .r12), (.r13, .reg .r13),
      (.r14, .reg .r14), (.r15, .reg .r15)])
    (hwr : WrW 0 S' [(16, .reg .r15), (24, .reg .r12), (32, .load 1 (8 * i) 8), (40, .lit 0),
      (48, .load 1 (8 * i + 16) 8), (56, .lit 0)])
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hpc : st.pc = Host.addrOf kk) {R : MachineState → Prop}
    (cont : ∀ st1 st2 : MachineState, Match (frameEnv m0 st.data 608 [(reg m0 .rdx, 32)] (fun _ ↦ 0)
        (Host.addrOf (kk + D.length)).toBitVec) S' st1.data →
      st2.pc = Host.addrOf (kk + D.length) → St m0 8 st2.data →
      ewRet st2.data = multilinearEval #[EW.ofK pub[i], EW.ofK pub[2 + i]] #[ch] →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st.data r) →
      (∀ j, 8 ≤ j → j < 608 → st2.data.dmem.get? (off (fb m0) j) =
        st1.data.dmem.get? (off (fb m0) j)) →
      NativeRustcVm.SameOutside st.data.dmem st2.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 N) N) →
      Kept st.data.dmem st2.data.dmem →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st := by
  have p := pre_parts h
  have hS := p.1
  refine blkPub h fr hr14 hk hx hmid hin0 hpc fun st1 fr1 hm1 hs1 hpc1 ↦ ?_
  have hwf := wfPub h fr (vars := fun _ ↦ 0) (ret := (Host.addrOf (kk + D.length)).toBitVec)
  have gr : ∀ r v, (r, v) ∈ ([(.rcx, .ptr 0 16), (.rdx, .lit 2), (.rsi, .ptr 0 32), (.rdi, .lit 2),
      (.r8, .lit 1), (.rbp, .reg .rbp), (.rbx, .reg .rbx), (.r12, .reg .r12), (.r13, .reg .r13),
      (.r14, .reg .r14), (.r15, .reg .r15)] : List (Reg64 × Sym)) → reg st1.data r = v.eval
        (frameEnv m0 st.data 608 [(reg m0 .rdx, 32)] (fun _ ↦ 0)
          (Host.addrOf (kk + D.length)).toBitVec) := fun r v hr ↦ hm1.regs r v (hregs _ hr)
  have hat := at_call h fr1
  have hw := fun (o : Nat) (v : Sym) (hv : (o, v) ∈ ([(16, .reg .r15), (24, .reg .r12),
      (32, .load 1 (8 * i) 8), (40, .lit 0), (48, .load 1 (8 * i + 16) 8), (56, .lit 0)] :
        List (Nat × Sym))) (ho : o + 8 ≤ 616) ↦ wordW (m0 := m0) hm1 ho (hwr (o, v) hv)
  have hvals : NativeRustcVm.EWsAt st1.data.dmem (off (fb m0) 32) [EW.ofK pub[i], EW.ofK pub[2 + i]] := by
    have h0 := hw 32 (.load 1 (8 * i) 8) (by simp) (by omega)
    have h1 := hw 40 (.lit 0) (by simp) (by omega)
    have h2 := hw 48 (.load 1 (8 * i + 16) 8) (by simp) (by omega)
    have h3 := hw 56 (.lit 0) (by simp) (by omega)
    rw [eval_load, load_pub h fr (by omega)] at h0
    rw [eval_load, show 8 * i + 16 = 8 * (2 + i) by omega, load_pub h fr (by omega)] at h2
    refine ewsAt_two h0 (by rwa [off_off]) (by rwa [off_off]) (by rwa [off_off])
  have hpt : NativeRustcVm.EWsAt st1.data.dmem (off (fb m0) 16) [ch] := by
    have h0 := hw 16 (.reg .r15) (by simp) (by omega)
    have h1 := hw 24 (.reg .r12) (by simp) (by omega)
    rw [eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .r15 = reg st.data .r15 from rfl,
      hr15, UInt64.ofBitVec_toBitVec] at h0
    rw [eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .r12 = reg st.data .r12 from rfl,
      hr12, UInt64.ofBitVec_toBitVec] at h1
    exact ewsAt_one h0 (by rwa [off_off])
  have e1si : reg st1.data .rsi = off (fb m0) 32 := (gr .rsi (.ptr 0 32) (by simp)).trans
    (eval_ptr0 32)
  have e1cx : reg st1.data .rcx = off (fb m0) 16 := (gr .rcx (.ptr 0 16) (by simp)).trans
    (eval_ptr0 16)
  have e1dx : reg st1.data .rdx = BitVec.ofNat 64 2 := gr .rdx (.lit 2) (by simp)
  have e1di : reg st1.data .rdi = BitVec.ofNat 64 2 := gr .rdi (.lit 2) (by simp)
  have e18 : reg st1.data .r8 = BitVec.ofNat 64 1 := gr .r8 (.lit 1) (by simp)
  have hpre : MleOfMultilinearEvalPre st1.data := by
    have hO1 := local_out h hat le_mle (o := 32) (n := 32) (by omega) (by omega)
    have hO2 := local_out h hat le_mle (o := 16) (n := 16) (by omega) (by omega)
    refine ⟨(ctx h N_ge).stackOk hat le_mle, by rw [e1di, e1dx], by rw [e18]; decide, ?_, ?_⟩
    · unfold SliceOk; rw [e1si, e1dx]; exact ⟨⟨hO1.1, hO1.2.1⟩, hO1.2.2.2.2.1⟩
    · unfold SliceOk; rw [e1cx, e18]; exact ⟨⟨hO2.1, hO2.2.1⟩, hO2.2.2.2.2.1⟩
  refine Fr.call hS N_ge (c := 0) (lo := 0) (len := 0) (by omega) (by simpa using le_mle)
    (fun p hp ↦ by have := slots_le p hp; have := slots_hi p hp; omega) (by omega)
    (fun q hq ↦ outs_not_frame h hq) (X := fun _ ↦ False) (fun _ hq ↦ hq.elim) hmle fr1 hpc1 hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ hq'.elim
      (fun h ↦ absurd h (by unfold InRange; omega)) .inl, hq.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  have hsl1 : slice st1.data (off (fb m0) 32) (BitVec.ofNat 64 2) = #[EW.ofK pub[i], EW.ofK pub[2 + i]] := by
    unfold slice
    have := NativeRustcVm.ewsOf_of_ewsAt hvals
    simp only [List.length_cons, List.length_nil] at this
    rw [show (BitVec.ofNat 64 2).toNat = 2 from rfl, this]
  have hsl2 : slice st1.data (off (fb m0) 16) (BitVec.ofNat 64 1) = #[ch] := by
    unfold slice
    have := NativeRustcVm.ewsOf_of_ewsAt hpt
    simp only [List.length_cons, List.length_nil] at this
    rw [show (BitVec.ofNat 64 1).toNat = 1 from rfl, this]
  refine cont st1 ⟨m2, _⟩ hm1 rfl fr2 ?_ ?_ ?_ ?_ ?_
  · rw [hq2.1, e1si, e1dx, e1cx, e18, hsl1, hsl2]
  · intro r hc
    refine (hcs2 r hc).trans ?_
    rcases calleeSaved_cases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact gr .rbx (.reg .rbx) (by simp)
    · exact gr .rbp (.reg .rbp) (by simp)
    · exact gr .r12 (.reg .r12) (by simp)
    · exact gr .r13 (.reg .r13) (by simp)
    · exact gr .r14 (.reg .r14) (by simp)
    · exact gr .r15 (.reg .r15) (by simp)
  · intro j hj1 hj2
    rw [show off (fb m0) j = off (fb m0) 8 + BitVec.ofNat 64 (j - 8) by rw [off_add]; congr 1; omega,
      local_keep h hat le_mle (R := fun _ ↦ False) (o := 8) (n := 600) hs2 (by omega) (by omega)
        (fun _ hq ↦ hq.elim) (j - 8) (by omega),
      off_add, show 8 + (j - 8) = j by omega]
  · exact (hs1.trans hs2).mono fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact frame_in h hq
      · exact callee_in h hat le_mle hq
      · exact hq.elim
  · exact fun p hp ↦ hq2.2.2.2 p (hm1.kept hwf p hp)

/-- **A limb's claim**: `b4`/`b7` (`D`, at `kk`), then `push_claim` with the claims `cs'` on
column `col`, the point (`r13` elements at the frame's offset `64`), the value in RAX, RDX. -/
theorem pushStep (h : PublicInputPhasePre a s L pub cs m0) {st : MachineState}
    (fr : St m0 8 st.data) {cs' : Array ColumnClaimW} {ch : EW}
    (hcl : ClaimsWAt st.data.dmem (reg m0 .rcx) cs') (hpt : PtW m0 st.data.dmem ch 0)
    (hrbx : reg st.data .rbx = reg m0 .rcx)
    (hr13 : reg st.data .r13 = BitVec.ofNat 64 (max (vcOf L) 1)) (hvc : vcOf L ≤ 31)
    {col : Nat} {v : Sym} {D : List Directive} {kk : Nat} {S' : SState}
    (hk : D.IsInfixAt Host.prog kk) (hx : exec D (stO 8) = some (S', .call NativeRustcVmX64.Vm.PushClaim.entryLabel))
    (hmid : MidOk 608 0 slots S' = true) (hin0 : ∀ w ∈ S'.mem, w.r = 0)
    (hw8 : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ 8)
    (hregs : RegsAre S' [(.rcx, .reg .r13), (.rdx, .ptr 0 64), (.rsi, .lit col),
      (.rdi, .reg .rbx), (.rbp, v), (.r8, .reg .rax), (.r9, .reg .rdx), (.rbx, .reg .rbx),
      (.r12, .reg .r12), (.r13, .reg .r13), (.r14, .reg .r14), (.r15, .reg .r15)])
    (hcol : col < 2 ^ 64)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hpc : st.pc = Host.addrOf kk) {R : MachineState → Prop}
    (cont : ∀ st1 st2 : MachineState, Match (frameEnv m0 st.data 608 [] (fun _ ↦ 0)
        (Host.addrOf (kk + D.length)).toBitVec) S' st1.data →
      st2.pc = Host.addrOf (kk + D.length) → St m0 8 st2.data →
      (if cs'.size < claimCap then boolRet st2.data = 1 ∧ ClaimsWAt st2.data.dmem (reg m0 .rcx)
          (cs'.push ⟨col, pt ch (vcOf L), ewRet st.data⟩)
        else boolRet st2.data = 0) →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r) →
      PtW m0 st2.data.dmem ch 0 →
      NativeRustcVm.SameOutside st.data.dmem st2.data.dmem
        (fun q ↦ NativeRustcVm.InRange (stackBelow m0 N) N q ∨
          NativeRustcVm.InRange (reg m0 .rcx) claimsBytes q) →
      Kept st.data.dmem st2.data.dmem →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st := by
  have p := pre_parts h
  have hS := p.1
  have ho := p.2.2.2.2.1
  refine blk h fr hk hx hmid hin0 hpc fun st1 fr1 hm1 hs1 hpc1 ↦ ?_
  have hwf := wfF h fr (vars := fun _ ↦ 0) (ret := (Host.addrOf (kk + D.length)).toBitVec)
  have gr : ∀ r w, (r, w) ∈ ([(.rcx, .reg .r13), (.rdx, .ptr 0 64), (.rsi, .lit col),
      (.rdi, .reg .rbx), (.rbp, v), (.r8, .reg .rax), (.r9, .reg .rdx), (.rbx, .reg .rbx),
      (.r12, .reg .r12), (.r13, .reg .r13), (.r14, .reg .r14), (.r15, .reg .r15)] :
        List (Reg64 × Sym)) → reg st1.data r = w.eval
        (frameEnv m0 st.data 608 [] (fun _ ↦ 0) (Host.addrOf (kk + D.length)).toBitVec) :=
    fun r w hr ↦ hm1.regs r w (hregs _ hr)
  have hat := at_call h fr1
  have e1di : reg st1.data .rdi = reg m0 .rcx := (gr .rdi (.reg .rbx) (by simp)).trans hrbx
  have e1dx : reg st1.data .rdx = off (fb m0) 64 := (gr .rdx (.ptr 0 64) (by simp)).trans
    (eval_ptr0 64)
  have e1cx : reg st1.data .rcx = BitVec.ofNat 64 (max (vcOf L) 1) :=
    (gr .rcx (.reg .r13) (by simp)).trans hr13
  have e1cxn : (reg st1.data .rcx).toNat = max (vcOf L) 1 := by
    rw [e1cx, BitVec.toNat_ofNat]; omega
  have e1si : (reg st1.data .rsi).toNat = col := by
    rw [gr .rsi (.lit col) (by simp)]; simp only [Sym.eval, BitVec.toNat_ofNat]; omega
  have hk1 := hm1.kept hwf
  have hpt1 : PtW m0 st1.data.dmem ch 0 := hpt.block hwf hm1 (writesIn_of_mid hmid)
    (fun w hw ↦ ⟨(hw8 w hw).1, by have := (hw8 w hw).2; omega⟩)
  have hcl1 : ClaimsWAt st1.data.dmem (reg m0 .rcx) cs' :=
    claims_keep h hs1 (fun q hq ↦ frame_in h hq) hcl
  have hO := local_out h hat le_push (o := 64) (n := 16 * max (vcOf L) 1) (by omega) (by omega)
  have hpre : PushClaimPre cs' st1.data := by
    unfold PushClaimPre
    rw [e1di]
    refine ⟨(ctx h N_ge).stackOk hat le_push, hcl1, ⟨Mapped.keeps ho.1 (kept_trans fr1.frame.kept
      (fun _ h ↦ h)), ho.2.1⟩, (ctx h N_ge).apart hat le_push ho.2.2.2.2.1, ?_, ?_⟩
    · unfold SliceOk; rw [e1dx, e1cxn]; exact ⟨⟨hO.1, hO.2.1⟩, hO.2.2.2.2.1⟩
    · rw [e1dx, e1cxn]
      exact (ctx h N_ge).apart_of_stack ho.2.2.2.2.1 (o := 64) (k := 16 * max (vcOf L) 1)
        (by omega) |> Apart.symm' |> Apart.symm'
  refine Fr.call hS N_ge (c := 0) (lo := 0) (len := 0) (by omega) (by simpa using le_push)
    (fun p hp ↦ by have := slots_le p hp; have := slots_hi p hp; omega) (by omega)
    (fun q hq ↦ outs_not_frame h hq) (X := NativeRustcVm.InRange (reg m0 .rcx) claimsBytes)
    (fun _ hq ↦ .inl (.inr hq)) (hpush cs') fr1 hpc1 hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ by
      rw [e1di] at hq'; exact hq'.elim .inr .inl, hq.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  obtain ⟨hres, -, hsv2⟩ := hq2
  rw [e1di] at hres
  have hsl : slice st1.data (reg st1.data .rdx) (reg st1.data .rcx) = pt ch (vcOf L) := by
    rw [e1dx, e1cx, slice_pt hpt1 (by omega) (by omega), pt_max]
  have hval : ewArg (reg st1.data .r8) (reg st1.data .r9) = ewRet st.data := by
    rw [gr .r8 (.reg .rax) (by simp), gr .r9 (.reg .rdx) (by simp)]; rfl
  refine cont st1 ⟨m2, _⟩ hm1 rfl fr2 ?_ hcs2 ?_ ?_ ?_
  · by_cases hfit : cs'.size < claimCap
    · have hpc' : (reg st1.data .rcx).toNat ≤ pointCap := by rw [e1cxn]; unfold pointCap; omega
      simp only [hfit, hpc', and_self, ↓reduceIte] at hres ⊢
      rw [← hsl, ← hval, ← e1si]
      exact hres
    · simp only [hfit, false_and, ↓reduceIte] at hres ⊢
      exact hres
  · intro i h1 h2
    have := hpt1 i h1 h2
    refine fun j hj ↦ ?_
    have hj' : j < 8 := by simpa [NativeRustcVm.length_wordBytes] using hj
    rw [off_add, show 64 + 8 * i + j = 8 + (56 + 8 * i + j) by omega, ← off_add,
      local_keep h hat le_push (R := NativeRustcVm.InRange (reg m0 .rcx) claimsBytes) (o := 8)
        (n := 600) hs2 (by omega) (by omega) (fun q hq hq' ↦ ?_) _ (by omega), off_add,
      show 8 + (56 + 8 * i + j) = 64 + 8 * i + j by omega, ← off_add]
    · exact this j hj
    · exact NativeRustcVm.Apart.not_inRange ((ctx h N_ge).apart_of_stack
        ho.2.2.2.2.1 (o := 8) (k := 600) (by omega)) ho.2.1
        (local_out h hat le_push (o := 8) (n := 600) (by omega) (by omega)).2.1 hq hq'
  · exact (hs1.trans hs2).mono fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inl (frame_in h hq)
      · exact .inl (callee_in h hat le_push hq)
      · exact .inr hq
  · exact fun p hp ↦ hsv2.2 p (hk1 p hp)

end

end

end NativeRustcVmX64.Tables.PublicInputPhase
