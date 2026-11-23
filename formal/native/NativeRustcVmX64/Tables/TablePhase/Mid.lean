module

public import NativeRustcVmX64.Tables.TablePhase.Tail
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names
public import NativeRustcVmX64.Code.Vm.TableSumcheck.Names

/-!
# `table_phase`: `ξ`'s powers and the target (x86-64)

From `b4` (`ξ` in RAX, RDX): the five powers into the frame at offset `32` (`powers`), the target,
the dot of the last three and the bus's totals (`b5`, `dot`), then `tail6` (`mid4`).
-/

namespace NativeRustcVmX64.Tables.TablePhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Vm.TablePhase
open NativeRustcVmX64.Bus.Gkr (Fr off_fb)
open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)
open NativeRustcVm.Layout (LayoutWAt layoutBytes Same)
open NativeRustcVm.Bus (BusWAt busBytes)
open NativeRustcVm (wordOf ewsOf)

public section

section
variable [Labels] {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW} {m0 : MachineData}

/-- **A local of the frame** as an output of a callee entered at the frame's offset `c`. -/
theorem local_out (h : TablePhasePre a s L bus m0) {c : Nat} (hc : c ≤ 160) {d : MachineData}
    (hat : At m0 (160 - c) d) {Nc : Nat} (hle : 160 - c + Nc ≤ N) {o n : Nat} (ho : c + 8 ≤ o)
    (hon : o + n ≤ 160) : OutOk d (reg m0 .rdi) a (off (stackBelow m0 160) o) n Nc := by
  have e : off (stackBelow m0 160) o = off (stackBelow m0 (160 - c)) (o - c) := by
    rw [← off_fb (pre_parts h).1 N_ge hc, off_off]
    congr 1
    omega
  rw [e]
  exact (ctx h (F := 160 - c) (by omega)).outOk_frame hat hle (by omega) (by omega)

/-- **A local kept** across a callee's changes in its stack and elsewhere. -/
theorem local_keep (h : TablePhasePre a s L bus m0) {c : Nat} (hc : c ≤ 160) {d d' : MachineData}
    (hat : At m0 (160 - c) d) {Nc : Nat} (hle : 160 - c + Nc ≤ N) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow d Nc) Nc q ∨ R q)) {o n : Nat} (ho : c + 8 ≤ o)
    (hon : o + n ≤ 160) (hR : ∀ q, R q → ¬NativeRustcVm.InRange (off (stackBelow m0 160) o) n q) :
    ∀ j < n, d'.dmem.get? (off (stackBelow m0 160) o + BitVec.ofNat 64 j) =
      d.dmem.get? (off (stackBelow m0 160) o + BitVec.ofNat 64 j) := by
  have hO := local_out h hc hat hle ho hon
  have hnw : NativeRustcVm.NoWrap (stackBelow d Nc) (Nc + 8) := by
    have := (ctx h (F := 160 - c) (by omega)).stackOk hat hle
    exact noWrap_stackBelow this
  intro j hj
  refine hs _ fun hq ↦ hq.elim (fun hq ↦ ?_) fun hq ↦ hR _ hq ?_
  · exact NativeRustcVm.Apart.not_inRange_add hO.2.2.2.2.1 hO.2.1 hnw hj (inRange_mono hq (by omega))
  · exact NativeRustcVm.inRange_add hj (by have := hO.2.1; unfold NoWrap at this; omega)

end

variable [Host] {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW} {m0 : MachineData}
  {k : Nat}

/-- **`ξ`'s powers, the target**, from `b4`, then `tail6`. -/
theorem mid4 (hp : Placed code k)
    (hpow : Spec (Labels.label NativeRustcVmX64.Vm.Powers.entryLabel) PowersPre PowersPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hsum : ∀ a s heights bus, Spec (Labels.label NativeRustcVmX64.Vm.TableSumcheck.entryLabel)
      (TableSumcheckPre a s heights bus) (TableSumcheckPost a s heights bus))
    (h : TablePhasePre a s L bus m0) {s1 : TState}
    (hg : (grind (grindingBits 4)).run s = some ((), s1)) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b4Offset)) (fr : St m0 24 st.data)
    (r12 : reg st.data .r12 = reg m0 .rdi) (r15 : reg st.data .r15 = reg m0 .rsi)
    (r14 : reg st.data .r14 = reg m0 .rdx) (rbx : reg st.data .rbx = reg m0 .rcx)
    (hxi : ewRet st.data = s1.sponge.squeeze.1)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a { s1 with sponge := s1.sponge.squeeze.2 }) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
      TablePhasePost a s L bus m0 st'.data) st := by
  have p := pre_parts h
  have hS := p.1
  set P := powers s1.sponge.squeeze.1 5 with hPdef
  have hP5 : P.size = 5 := size_powers _ _
  -- `b4`, `powers`
  obtain ⟨hmid, h0, hw4, hregs⟩ := after_eq run_b4 ▸ ok_b4
  refine blk h fr (b4_in_code.trans hp.1 (by simp [b4])) run_b4 hmid h0 hpc
    fun st1 fr1 hm1 hs1 hpc1 ↦ ?_
  have hwf := wfF h fr (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b4Offset + b4.length)).toBitVec)
  have gr : ∀ r v, (r, v) ∈ ([(.r13, .ptr 0 64), (.rbp, .ptr 0 32), (.rcx, .lit 5),
      (.rdi, .reg .rax), (.rsi, .reg .rdx), (.rdx, .ptr 0 32), (.rbx, .reg .rbx), (.r12, .reg .r12),
      (.r14, .reg .r14), (.r15, .reg .r15)] : List (Reg64 × Sym)) →
      reg st1.data r = v.eval (frameEnv m0 st.data 160 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b4Offset + b4.length)).toBitVec) := fun r v hr ↦ hm1.regs r v (hregs _ hr)
  have e1dx : reg st1.data .rdx = off (stackBelow m0 160) 32 :=
    (gr .rdx (.ptr 0 32) (by simp)).trans (eval_ptr0 32)
  have e1cx : (reg st1.data .rcx).toNat = 5 := by rw [gr .rcx (.lit 5) (by simp)]; rfl
  have hle_p : 160 - 16 + powersStack ≤ N := by decide
  have hat1 := at_call h fr1 (by omega)
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a { s1 with sponge := s1.sponge.squeeze.2 } :=
    tstate_keep h hts (hm1.kept hwf) hs1 fun q hq ↦ .inl (frame_in h hq)
  have hpre1 : PowersPre st1.data := by
    have hO := local_out h (c := 16) (by omega) hat1 hle_p (o := 32) (n := 80) (by omega) (by omega)
    refine ⟨(ctx h (F := 144) (by decide)).stackOk hat1 hle_p, ?_⟩
    unfold SliceOk
    rw [e1dx, e1cx]
    exact ⟨⟨hO.1, hO.2.1⟩, hO.2.2.2.2.1⟩
  refine Fr.call hS N_ge (c := 16) (lo := 32) (len := 80) (by omega) hle_p
    (fun p hp ↦ by have := slots_le p hp; have := (show ∀ p ∈ slots, 112 ≤ p.1 by decide) p hp; omega)
    (by omega) (fun q hq ↦ outs_not_frame h hq)
    (X := NativeRustcVm.InRange (off (stackBelow m0 160) 32) 80) (fun q hq ↦ .inr hq)
    hpow fr1 hpc1 hpre1
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ by
      rw [e1dx, e1cx] at hq'
      exact hq'.elim .inr .inl, hq.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  obtain ⟨hpw2, -, hsv2⟩ := hq2
  rw [e1dx, e1cx] at hpw2
  have hxi1 : ewArg (reg st1.data .rdi) (reg st1.data .rsi) = s1.sponge.squeeze.1 := by
    rw [gr .rdi (.reg .rax) (by simp), gr .rsi (.reg .rdx) (by simp)]; exact hxi
  rw [hxi1] at hpw2
  have c144 := ctx h (F := 144) (by decide)
  have hfnw : NativeRustcVm.NoWrap (stackBelow m0 160) 160 :=
    ((ctx h N_ge).noWrap_frame).mono (by omega)
  have hts2 : TStateAt m2.dmem (reg m0 .rdi) a { s1 with sponge := s1.sponge.squeeze.2 } :=
    tstate_keep h hts1 hsv2.2 hs2 fun q hq ↦ hq.elim
      (fun hq ↦ .inl (c144.inRange_callee hat1 hle_p hq).1)
      (fun hq ↦ .inl (frame_in h (inRange_of_off hfnw (by omega) hq)))
  have hr2 : ∀ r, calleeSaved r = true → (r, Sym.reg r) ∈ ([(.r13, .ptr 0 64), (.rbp, .ptr 0 32),
      (.rcx, .lit 5), (.rdi, .reg .rax), (.rsi, .reg .rdx), (.rdx, .ptr 0 32), (.rbx, .reg .rbx),
      (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] : List (Reg64 × Sym)) →
      reg m2 r = reg st.data r := fun r hc hr ↦ (hcs2 r hc).trans (gr r _ hr)
  have h2r13 : reg m2 .r13 = off (stackBelow m0 160) 64 :=
    (hcs2 .r13 rfl).trans ((gr .r13 (.ptr 0 64) (by simp)).trans (eval_ptr0 64))
  have h2rbp : reg m2 .rbp = off (stackBelow m0 160) 32 :=
    (hcs2 .rbp rfl).trans ((gr .rbp (.ptr 0 32) (by simp)).trans (eval_ptr0 32))
  -- `b5`, `dot`
  obtain ⟨hmid5, h05, hw5, hregs5⟩ := after_eq run_b5 ▸ ok_b5
  refine blk h fr2 (st := ⟨m2, _⟩) (b5_in_code.trans hp.1 (by simp [b5])) run_b5 hmid5 h05
    (by show Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b4Offset + b4.length) = _; rfl) fun st3 fr3 hm3 hs3 hpc3 ↦ ?_
  have hwf3 := wfF h fr2 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b5Offset + b5.length)).toBitVec)
  have gr3 : ∀ r v, (r, v) ∈ ([(.rdx, .bin .add .W64 (.reg .r14) (.lit 107720)), (.rsi, .lit 3),
      (.rcx, .lit 3), (.rdi, .reg .r13), (.rbp, .reg .rbp), (.r13, .reg .r13), (.rbx, .reg .rbx),
      (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] : List (Reg64 × Sym)) →
      reg st3.data r = v.eval (frameEnv m0 m2 160 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b5Offset + b5.length)).toBitVec) := fun r v hr ↦ hm3.regs r v (hregs5 _ hr)
  have e3di : reg st3.data .rdi = off (stackBelow m0 160) 64 :=
    (gr3 .rdi (.reg .r13) (by simp)).trans h2r13
  have e3si : (reg st3.data .rsi).toNat = 3 := by rw [gr3 .rsi (.lit 3) (by simp)]; rfl
  have e3cx : (reg st3.data .rcx).toNat = 3 := by rw [gr3 .rcx (.lit 3) (by simp)]; rfl
  have e3dx : reg st3.data .rdx = reg m0 .rdx + BitVec.ofNat 64 107720 := by
    rw [gr3 .rdx (.bin .add .W64 (.reg .r14) (.lit 107720)) (by simp),
      NativeRustcVmX64.Arrays.eval_add, NativeRustcVmX64.Arrays.eval_lit]
    show reg m2 .r14 + _ = _
    rw [hr2 .r14 rfl (by simp), r14]
  have hle_d : 160 - 16 + dotStack ≤ N := by decide
  have hat3 := at_call h fr3 (by omega)
  have hloc3 : ∀ j < 80, st3.data.dmem.get? (off (stackBelow m0 160) 32 + BitVec.ofNat 64 j) =
      m2.dmem.get? (off (stackBelow m0 160) 32 + BitVec.ofNat 64 j) := fun j hj ↦ by
    rw [off_add]
    exact keep_hi hwf3 hm3 (writesIn_of_mid hmid5) (L := 24) (fun w hw _ ↦ hw5 w hw) (by omega)
      (by omega)
  have hpw3 : NativeRustcVm.EWsAt st3.data.dmem (off (stackBelow m0 160) 32) P.toList :=
    NativeRustcVmX64.Arrays.ewsAt_congr hpw2 fun j hj ↦ hloc3 j (by simp [hP5] at hj; omega)
  have hB3 : BusWAt st3.data.dmem (reg m0 .rdx) bus :=
    NativeRustcVm.Tables.BusWAt.of_same p.2.2.2.2.2.2.2.2.2.2.2
      (same_in h fr3 p.2.2.2.2.2.2.2.2.2.2.1)
  have hbt := ReadIn.sub p.2.2.2.2.2.2.2.2.2.2.1 (o := 107720) (k := 48) (by decide) (by decide)
  have hpre3 : DotPre st3.data := by
    have hO := local_out h (c := 16) (by omega) hat3 hle_d (o := 64) (n := 48) (by omega) (by omega)
    have hbt' := readIn_call h fr3 (by omega) hle_d hbt
    refine ⟨c144.stackOk hat3 hle_d, ?_, ?_⟩
    · unfold SliceOk; rw [e3di, e3si]; exact ⟨⟨hO.1, hO.2.1⟩, hO.2.2.2.2.1⟩
    · unfold SliceOk; rw [e3dx, e3cx]; exact ⟨hbt'.1, hbt'.2.1⟩
  refine Fr.call hS N_ge (c := 16) (lo := 0) (len := 0) (by omega) hle_d
    (fun p hp ↦ by have := slots_le p hp; have := (show ∀ p ∈ slots, 112 ≤ p.1 by decide) p hp; omega)
    (by omega) (fun q hq ↦ outs_not_frame h hq) (X := fun _ ↦ False) (fun _ hq ↦ hq.elim)
    hdot fr3 hpc3 hpre3
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ hq'.elim
      (fun h ↦ absurd h (by unfold InRange; omega)) .inl, hq.2.2⟩)
    fun m4 fr4 hq4 hs4 hcs4 ↦ ?_
  obtain ⟨hdot4, -, hsv4⟩ := hq4
  have hts4 : TStateAt m4.dmem (reg m0 .rdi) a { s1 with sponge := s1.sponge.squeeze.2 } := by
    have hts3 := tstate_keep h hts2 (hm3.kept hwf3) hs3 fun q hq ↦ .inl (frame_in h hq)
    exact tstate_keep h hts3 hsv4.2 hs4 fun q hq ↦ hq.elim
      (fun hq ↦ .inl (c144.inRange_callee hat3 hle_d hq).1) False.elim
  have hpw4 : NativeRustcVm.EWsAt m4.dmem (off (stackBelow m0 160) 32) P.toList :=
    NativeRustcVmX64.Arrays.ewsAt_congr hpw3
      (local_keep h (c := 16) (by omega) hat3 hle_d hs4 (o := 32) (n := 80) (by omega) (by omega)
        (fun _ hq ↦ hq.elim) |> fun H j hj ↦ H j (by
          have : P.toList.length = 5 := by simp [hP5]
          omega))
  have htg : ewRet m4 = dot (P.extract 2 5) bus.totals := by
    rw [hdot4]
    have hd := hpw3.drop 2
    rw [off_add] at hd
    have htot := NativeRustcVm.ewsOf_of_ewsAt hB3.totals
    rw [show bus.totals.toList.length = 3 by simp [hB3.totals_size]] at htot
    have htot' : (ewsOf st3.data.dmem (reg m0 .rdx + BitVec.ofNat 64 107720) 3).toArray =
        bus.totals := by
      rw [show reg m0 .rdx + BitVec.ofNat 64 107720 = off (reg m0 .rdx)
        NativeRustcVm.Bus.busTotalsOff from rfl, htot, Array.toArray_toList]
    unfold slice
    rw [e3di, e3si, e3dx, e3cx, ewsOf_take hd (by simp [hP5]), List.take_of_length_le (by simp [hP5]),
      extract_drop hP5, htot']
  refine tail6 hp hsum h hg (st := ⟨m4, _⟩) (by show Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b5Offset + b5.length) = _; rfl) fr4
    ?_ ?_ ?_ ?_ ?_ ?_ hpw4 htg hts4
  · exact (hcs4 .r12 rfl).trans ((gr3 .r12 (.reg .r12) (by simp)).trans ((hr2 .r12 rfl (by simp)).trans r12))
  · exact (hcs4 .r15 rfl).trans ((gr3 .r15 (.reg .r15) (by simp)).trans ((hr2 .r15 rfl (by simp)).trans r15))
  · exact (hcs4 .r14 rfl).trans ((gr3 .r14 (.reg .r14) (by simp)).trans ((hr2 .r14 rfl (by simp)).trans r14))
  · exact (hcs4 .rbx rfl).trans ((gr3 .rbx (.reg .rbx) (by simp)).trans ((hr2 .rbx rfl (by simp)).trans rbx))
  · exact (hcs4 .rbp rfl).trans ((gr3 .rbp (.reg .rbp) (by simp)).trans (h2rbp))
  · exact (hcs4 .r13 rfl).trans ((gr3 .r13 (.reg .r13) (by simp)).trans (h2r13))

end

end NativeRustcVmX64.Tables.TablePhase
