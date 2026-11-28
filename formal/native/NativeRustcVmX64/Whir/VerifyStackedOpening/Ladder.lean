module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Window
public import NativeRustcVmX64.Code.Vm.Ladder.Names

/-!
# `verify_stacked_opening`: the ladder (x86-64)

`ladder_b42`: from `b42` (`AtB42`), `b42` keeps the out-of-domain term (R12, R13), writes the
`BasisW`'s words (`basisW`) to the frame's `104` to `159`, reads the stack's log-size (R14) and
calls `ladder` into the frame's `160` to `319`; `b43` checks its tag: `None` fails (`b50`, the
model's `none`), `Some` goes on to `b44` (`AtB44`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening
open LeanVM.Parameters

@[expose] public section

/-- The target's terms but the out-of-domain one. -/
abbrev accP (s : TState) (layout : LayoutW) (target : EW) (cs : Array ColumnClaimW) (value : EW) :
    EW :=
  accOf s layout target cs value (1 + placedOf layout cs cs.size)

/-- **After the ladder**, at `b44`: its levels `ls` at the frame's `160`, the out-of-domain term
in R12, R13, the stack's log-size in R14. -/
structure AtB44 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (ls : List Whir.Level) (m0 st : MachineData) :
    Prop where
  ok : Ok m0 st 8
  out : Outs a s layout cs m0 st.dmem
  fw : FW st.dmem m0 (fwL m0 ++ basisW m0 layout cs)
  hi72 : NativeRustcVm.WordAt st.dmem (win m0 72) (accP s layout target cs value).c1
  rbx : reg st .rbx = (accP s layout target cs value).c0.toBitVec
  sum : accP s layout target cs value + ewArg (reg st .r12) (reg st .r13) =
    claimOf s layout target cs value
  r14 : reg st .r14 = layout.stackLog.toUInt64.toBitVec
  lad : Whir.ladder layout.stackLog (reg m0 .rdx).toNat = some ls
  lat : NativeRustcVm.Layout.LadderAt st.dmem (win m0 160) (some ls)

end

public section

/-- A word copied by a block from the frame. -/
theorem fw_copy [Labels] {m0 st st' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (frameEnv m0 st 512 rest vars ret) S st') {o o' : Nat} (ho : o + 8 ≤ 520)
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.load 0 o' 8, i))
    {L : List (Nat × UInt64)} (hL : FW st.dmem m0 L) {w : UInt64} (hp : (o', w) ∈ L) :
    NativeRustcVm.WordAt st'.dmem (win m0 o) w := by
  have := fw_write hm ho hw
  have e : (Sym.load 0 o' 8).eval (frameEnv m0 st 512 rest vars ret) = w.toBitVec := fw_load hL hp
  rw [e, UInt64.ofBitVec_toBitVec] at this
  exact this

/-- A register stored by a block in the frame. -/
theorem fw_reg [Labels] {m0 st st' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (frameEnv m0 st 512 rest vars ret) S st') {o : Nat} (ho : o + 8 ≤ 520) {r : Reg64}
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.reg r, i)) {x : BitVec 64}
    (hx : reg st r = x) : NativeRustcVm.WordAt st'.dmem (win m0 o) (UInt64.ofBitVec x) := by
  have := fw_write hm ho hw
  rw [← hx]
  exact this

theorem size_claims_le {layout : LayoutW} {cs : Array ColumnClaimW} (hn : cs.size ≤ 160)
    (target : EW) (point coefficients z : Array EW) (value : EW) :
    (stackClaims layout target point coefficients cs z value).size ≤ 512 := by
  rw [size_stackClaims]
  have := placedOf_le_self (layout := layout) (cs := cs) cs.size
  omega

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **The ladder**: `b42`, `ladder`, `b43`; `None` fails. -/
theorem ladder_b42 (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) (hlad : Spec (Labels.label NativeRustcVmX64.Vm.Ladder.entryLabel) LadderPre LadderPost)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b42Offset))
    (hA : AtB42 a s layout target cs value m0 st.data)
    (cont : ∀ ls st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b44Offset) →
      AtB44 a s layout target cs value ls m0 st'.data →
      Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0) st') :
    Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0) st := by
  have hok := hA.ok
  have hl := (h.ins _ mem_lay).1
  have hlb : NativeRustcVm.Layout.layoutBytes = 3912 := rfl
  simp only [hlb] at hl
  have hlay := hok.lay h
  -- `b42`
  have hwf1 : ∀ ret, (frameEnv m0 st.data 512 [(layA m0, 24)] (fun _ ↦ 0) ret).WF := fun _ ↦
    hok.wf1 h (fun i hi ↦ hl.1.1 i (by omega))
      (by
        have hh : (reg m0 .rsi).toNat + 3912 ≤ 2 ^ 64 := hl.1.2
        unfold NativeRustcVm.NoWrap; omega)
      (apart_shrink hl.2 (by omega) le_rfl)
  have hm1 : ∀ ret, Match (frameEnv m0 st.data 512 [(layA m0, 24)] (fun _ ↦ 0) ret) layS st.data :=
    fun _ ↦ match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by show reg st.data .r14 = _
          rw [hA.r14, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  have hlog : ∀ ret, (frameEnv m0 st.data 512 [(layA m0, 24)] (fun _ ↦ 0) ret).load 1 16 8 =
      layout.stackLog.toUInt64.toBitVec := fun _ ↦ load_ofMachine (r := 1) rfl hlay.stack_log
  refine h.run hp b42_in_code (List.cons_ne_nil _ _) hpc hok (hwf1 _) (hm1 _) run_b42 (o := 0)
    (by decide +kernel) (by decide +kernel) fun st1 hok1 hs1 hm1' hpc1 ↦ ?_
  have hout1 := Outs.keep h hA.out (hm1'.kept (hwf1 _)) (h.blk_stack hs1)
  have hfwL := FW.block_os (hwf1 _) hm1' rfl (hA.fw.left.append (FW.one hA.hi72))
    [24, 40, 48, 56, 64, 72] rfl (by decide +kernel)
  have hfA := hA.fw
  have hbw : FW st1.data.dmem m0 (basisW m0 layout cs) := by
    refine FW.cons (fw_copy hm1' (o' := 80) (by omega) (by decide +kernel) hfA (by simp [fwA]))
      (FW.cons (fw_copy hm1' (o' := 88) (by omega) (by decide +kernel) hfA (by simp [fwA]))
      (FW.cons (fw_reg hm1' (by omega) (r := .r14) (by decide +kernel) hA.r14)
      (FW.cons (fw_copy hm1' (o' := 64) (by omega) (by decide +kernel) hfA (by simp [fwA, fwL]))
      (FW.cons (fw_copy hm1' (o' := 56) (by omega) (by decide +kernel) hfA (by simp [fwA, fwL]))
      (FW.cons (fw_copy hm1' (o' := 40) (by omega) (by decide +kernel) hfA (by simp [fwA, fwL]))
      (FW.one (fw_reg hm1' (by omega) (r := .r15) (by decide +kernel) hA.r15)))))))
  have e1_rdi : reg st1.data .rdi = win m0 160 :=
    (hm1'.regs .rdi _ rfl).trans (eval_ptr0 160)
  have e1_rsi : (reg st1.data .rsi).toNat = layout.stackLog := by
    rw [show reg st1.data .rsi = _ from hm1'.regs .rsi _ rfl]
    show ((frameEnv m0 st.data 512 _ (fun _ ↦ 0) _).load 1 16 8).toNat = _
    rw [hlog]
    exact u64n hlay.stack_log_lt
  have e1_rdx : reg st1.data .rdx = reg m0 .rdx := by
    rw [show reg st1.data .rdx = _ from hm1'.regs .rdx _ rfl]
    exact fw_load hfA (o := 48) (v := UInt64.ofBitVec (reg m0 .rdx)) (by simp [fwA, fwL])
  have e1_r14 : reg st1.data .r14 = layout.stackLog.toUInt64.toBitVec :=
    (hm1'.regs .r14 _ rfl).trans (hlog _)
  have e1_sum : accP s layout target cs value + ewArg (reg st1.data .r12) (reg st1.data .r13) =
      claimOf s layout target cs value := by
    rw [show reg st1.data .r12 = reg st.data .rax from hm1'.regs .r12 _ rfl,
      show reg st1.data .r13 = reg st.data .rdx from hm1'.regs .r13 _ rfl]
    exact hA.sum
  have e1_rbx : reg st1.data .rbx = (accP s layout target cs value).c0.toBitVec :=
    (regKeep hm1' .rbx rfl).trans hA.rbx
  -- `ladder`
  have hN : 512 + ladderStack ≤ verifyStackedOpeningStack := by rw [stack_eq]; decide
  have hpre : LadderPre st1.data := by
    unfold LadderPre
    rw [e1_rdi]
    have hw := hok1.win_in h (lo := 160) (n := 160) (by omega) (by omega) hN
    exact ⟨hok1.stackOk h hN, hok1.rodataAt h hN, hw.1, hw.2,
      fun t ↦ h.win_apart (lo := 160) (n := 160) (by omega) (RodataAt.apart h.wt.2.2.1 t)⟩
  refine call_then (P := LadderPre) (Q := LadderPost) hpc1 hlad hpre
    fun st2 hpc2 hrsp2 ⟨hlat, hch, hsv⟩ ↦ ?_
  rw [e1_rdi, e1_rsi, e1_rdx] at hlat
  have hch' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
      (fun q ↦ NativeRustcVm.InRange (win m0 160) 160 q ∨
        NativeRustcVm.InRange (stackBelow st1.data ladderStack) ladderStack q) := by
    have := hch
    unfold Changes at this
    rw [e1_rdi] at this
    exact this
  obtain ⟨hok2, hs2⟩ := hok1.callWin h hsv hrsp2 hN (lo := 160) (n := 160) (by omega) hch'
  have hout2 := Outs.keep h hout1 hsv.2 hs2
  have hfw2 := FW.callWin h hok1 hN (by omega) hch' (hfwL.left.append hbw)
    (by
      intro p hp
      simp only [fwL, basisW, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp)
    (le_of_map [24, 40, 48, 56, 64, 104, 112, 120, 128, 136, 144, 152] rfl (by decide))
  have h722 := FW.callWin h hok1 hN (by omega) hch' hfwL.right
    (fun p hp ↦ by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp; simp)
    (le_of_map [72] rfl (by decide))
  -- `b43`
  refine h.run hp b43_in_code (List.cons_ne_nil _ _)
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b42_next)) hok2 (vars := fun _ ↦ 0) (hok2.wf0 h)
    hok2.m_reg run_b43 (o := 8) (by decide +kernel) (by decide) fun st3 hok3 hs3 hm3 hpc3 ↦ ?_
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (hok2.wf0 h) rfl
  simp only [PcOk] at hpc3
  cases hls : Whir.ladder layout.stackLog (reg m0 .rdx).toNat with
  | none =>
    rw [hls] at hlat
    have hl1 := load1_of_tag (env := frameEnv m0 st2.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b43Offset + b43.length)).toBitVec) (r := 0) (o := 160) (Or.inl rfl) hlat
    have hc : (SBool.cmp .eq .W8 (.load 0 160 1) (.lit 0)).eval (frameEnv m0 st2.data 512 []
        (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b43Offset + b43.length)).toBitVec) = true := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply]
      rw [hl1]
      decide
    rw [hc] at hpc3
    simp only [↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_40_at] at hpc3
    refine fail_b50 h hp hpc3 hok3 ?_
    unfold runOf
    rw [vso_run _ _ _ (size_claims_le h.n_le target point coefficients z value), hls]
    rfl
  | some ls =>
    rw [hls] at hlat
    have hl1 := load1_of_tag (env := frameEnv m0 st2.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b43Offset + b43.length)).toBitVec) (r := 0) (o := 160) (Or.inr rfl) hlat.1
    have hc : (SBool.cmp .eq .W8 (.load 0 160 1) (.lit 0)).eval (frameEnv m0 st2.data 512 []
        (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b43Offset + b43.length)).toBitVec) = false := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply]
      rw [hl1]
      decide
    rw [hc] at hpc3
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
    have k3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st1.data r := fun r hr ↦
      (regKeep hm3 r (by cases r <;> first | rfl | exact absurd hr (by decide))).trans (hsv.1 r hr)
    refine cont ls st3 (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b43_next))
      ⟨hok3, by rw [hd3]; exact hout2, by rw [hd3]; exact hfw2,
        by rw [hd3]; exact h722.get List.mem_cons_self, by rw [k3 .rbx rfl]; exact e1_rbx,
        by rw [k3 .r12 rfl, k3 .r13 rfl]; exact e1_sum, by rw [k3 .r14 rfl]; exact e1_r14,
        hls, by rw [hd3]; exact hlat⟩

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
