module

public import NativeRustcVmX64.Tables.ColumnClaims.Exit
public import NativeRustcVmX64.Code.Vm.PushClaim.Names

/-!
# `table_column_claims`: a table's loop (x86-64)

`loop`: from table `t`'s loop head with `j` values pushed, its test block (`T`) leaves the loop
after the last value (`hdone`), else its push block (`P`) calls `push_claim` with value `j` on
column `base t + j` at the table's point, and the block after the call (`A`) goes back to the head
when the claim was pushed or to the failure (`hfail`), where the claims do not fit.
-/

namespace NativeRustcVmX64.Tables.ColumnClaims

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableColumnClaims NativeRustcVmX64.Field NativeRustcVmX64.Tables
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap Same)
open NativeRustcVm (wordOf ewOf ewsOf)

public section

variable {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW} {m0 : MachineData}

theorem app_push (cs : Array ColumnClaimW) (l : List ColumnClaimW) (x : ColumnClaimW) :
    cs ++ (l ++ [x]).toArray = (cs ++ l.toArray).push x := by
  apply Array.toList_inj.mp; simp

/-- A part of the evaluations: readable, off the stack, apart from the claims. -/
theorem ev_part (h : TableColumnClaimsPre ev cs m0) {o k : Nat} (ho : o < tableEvalsBytes)
    (hk : o + k ≤ tableEvalsBytes) :
    Readable m0 (reg m0 .rdi + BitVec.ofNat 64 o) k ∧
      OffStack m0 (reg m0 .rdi + BitVec.ofNat 64 o) k N ∧
      Apart (reg m0 .rdi + BitVec.ofNat 64 o) k (reg m0 .rsi) claimsBytes := by
  obtain ⟨-, ⟨⟨hm, hnw⟩, hst, hws⟩, -⟩ := pre_parts h
  have hw := hws _ (List.mem_singleton.mpr rfl)
  have hE : tableEvalsBytes = 11808 := rfl
  unfold NoWrap at hnw
  rw [hE] at hk ho hnw
  have e : (reg m0 .rdi + BitVec.ofNat 64 o).toNat = (reg m0 .rdi).toNat + o :=
    toNat_add_ofNat _ _ (by omega)
  refine ⟨⟨fun i hi ↦ ?_, by unfold NoWrap; rw [e]; omega⟩, ?_, ?_⟩
  · rw [addr_add]; exact hm _ (by omega)
  · unfold OffStack Apart at hst ⊢; rw [e]; omega
  · unfold Apart at hw ⊢; rw [e]; simp only at hw; omega

/-- Bytes a block writing only the frame below `L ≤ 72` does not touch. -/
theorem frame_keep [Labels] {st st' : MachineData} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (Env.ofMachine st ((stackBelow m0 64, 64 + 8) :: rs) vars ret).WF)
    (hm : Match (Env.ofMachine st ((stackBelow m0 64, 64 + 8) :: rs) vars ret) S st')
    {L : Nat} (hL : L ≤ 64 + 8) (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ L) {p : BitVec 64}
    (hp : ¬InRange (stackBelow m0 64) L p) : st'.dmem.get? p = st.dmem.get? p :=
  hm.get?_mem0 hwf fun h ↦ hp (written_region0 rfl hwf hL hw h)

theorem not_inRange_le {b p : BitVec 64} {L L' : Nat} (hL : L ≤ L') (h : ¬InRange b L' p) :
    ¬InRange b L p := fun h' ↦ h (by unfold InRange at h' ⊢; omega)

theorem sub16 {c : Nat} (h : 1 ≤ c) (h' : 16 * c < 2 ^ 64) :
    BitVec.ofNat 64 18446744073709551600 + BitVec.ofNat 64 (16 * c) =
      BitVec.ofNat 64 (16 * (c - 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add16' (a : BitVec 64) (j : Nat) :
    a + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 16 = a + BitVec.ofNat 64 (16 * (j + 1)) := by
  rw [addr_add]; congr 2

variable [Host]

/-- **Table `t`'s loop.** -/
theorem loop
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hpre : TableColumnClaimsPre ev cs m0) {R : Regs} {t : Nat} (ht : t < 6)
    (hR : ([R.n, R.p, R.l, R.c, .rbx, .r14].all fun r ↦
      calleeSaved r && !([R.a, .rax, .rcx].contains r)) = true)
    (hRa : calleeSaved R.a = false ∧ R.a ≠ .rsp)
    {T P A : List Directive} {kT lenA : Nat} {lT lN : Label} {x : Sym}
    (hTk : T.IsInfixAt Host.prog kT) (hTlen : T.length = 3)
    (hTx : exec T regsS = some (after T regsS, .cond (testN R) lN))
    (hTm : (after T regsS).mem = []) (hTk' : KeptBut (after T regsS) [])
    (hPk : P.IsInfixAt Host.prog (kT + 3)) (hPlen : P.length = 10)
    (hPx : exec P (pushS R) = some (after P (pushS R), .call NativeRustcVmX64.Vm.PushClaim.entryLabel))
    (hPok : PushOk R (after P (pushS R)))
    (hAk : A.IsInfixAt Host.prog (kT + 3 + 10)) (hAlen : A.length = lenA)
    (hAx : exec A regsS = some (after A regsS, .cond (alNZ x) lT))
    (hAr : (after A regsS).reg R.a = some (.reg .r14)) (hAm : (after A regsS).mem = [])
    (hAk' : KeptBut (after A regsS) [R.a, .rax, .rcx])
    (hx : ∀ env : Env, (x.eval env).toNat % 256 = (env.regs .rax).toNat % 256)
    (hAax : ∀ (st st' : MachineData), Match (Env.ofMachine st [] (fun _ ↦ 0) 0) (after A regsS) st' →
      (reg st .rax).toNat % 256 = 0 → (reg st' .rax).toNat % 256 = 0)
    (hlT : Labels.label lT = Host.addrOf kT)
    (hfail : ∀ st : MachineState, st.pc = Host.addrOf (kT + 3 + 10 + lenA) → Bd m0 st.data →
      (reg st.data .rax).toNat % 256 = 0 → ¬Fits ev cs →
      Eventually (step1 Host.exe) (Goal ev cs m0) st)
    (hdone : ∀ st : MachineState, st.pc = Labels.label lN → LoopAt ev cs m0 R t (cnt ev t) st.data →
      Eventually (step1 Host.exe) (Goal ev cs m0) st) :
    ∀ (j : Nat) (st : MachineState), st.pc = Host.addrOf kT → LoopAt ev cs m0 R t j st.data →
      Eventually (step1 Host.exe) (Goal ev cs m0) st := by
  intro j0 st0 hpc0 hL0
  obtain ⟨hS, -, -, hCR, hCO, -⟩ := pre_parts hpre
  have hcntle := cnt_le hpre ht
  have hplen := plen_le hpre ht
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hR
  refine Sym.loop (fun c st ↦ st.pc = Host.addrOf kT ∧ ∃ j, cnt ev t - j = c ∧
    LoopAt ev cs m0 R t j st.data) (fun c st ⟨hpc, j, hc, hL⟩ ↦ ?_) ⟨hpc0, j0, rfl, hL0⟩
  -- the test
  refine exec_at hTk hTx (Env.wf_nil _) (fun _ h ↦ by cases h) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) hTm
  have hk1 : ∀ r, reg st1.data r = reg st.data r := fun r ↦ keptBut_reg hm1 hTk' (by simp)
  have hL1 : LoopAt ev cs m0 R t j st1.data :=
    ⟨Body.congr hL.body (fun r _ ↦ hk1 r) (hk1 .rsp) hd1, by unfold fw; rw [hd1]; exact hL.ev8,
      by rw [hk1]; exact hL.rbx, hL.le, by rw [hk1]; exact hL.a, by rw [hk1]; exact hL.n,
      by rw [hk1]; exact hL.p, by rw [hk1]; exact hL.l, by rw [hk1]; exact hL.c,
      by rw [hd1]; exact hL.claims⟩
  simp only [PcOk, hTlen, testN] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs, show st.data.regs.get64 R.n = reg st.data R.n from rfl,
    hL.n, ofNat_beq (by omega) (by decide)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hj : j = cnt ev t
  · subst hj
    exact Eventually.mono (hdone st1 (hT (by simp)) hL1) fun _ h ↦ Or.inl h
  have hjl : j < cnt ev t := by have := hL.le; omega
  have hpc1' : st1.pc = Host.addrOf (kT + 3) := hF (by simp; omega)
  -- the push block
  have hvp := ev_part hpre (o := 1968 * t + 496) (k := 16 * cnt ev t) (by rw [evB_eq]; omega)
    (by rw [evB_eq]; omega)
  have hpp := ev_part hpre (o := 1968 * t + 8) (k := 16 * plen ev t) (by rw [evB_eq]; omega)
    (by rw [evB_eq]; omega)
  have hev := ev_part hpre (o := 0) (k := tableEvalsBytes) (by decide) (by omega)
  rw [add_ofNat_zero] at hev
  obtain ⟨hwfP, hmP⟩ := Body.at_elem (a := valAddr m0 t) (n := cnt ev t) (i := j)
    (ret := (Host.addrOf (kT + 3 + 10)).toBitVec) hL1.body hS h64 hvp.1 hvp.2.1 hjl
    (x := .reg R.a) (o := 0) (by rw [eval_reg, Env.ofMachine_regs, add_ofNat_zero]; exact hL1.a)
  have hsm1 : Same m0.dmem st1.data.dmem (reg m0 .rdi) tableEvalsBytes := same_ev hpre hL1.body
  have hval : ewArg ((elemEnv m0 st1.data 64 (valAddr m0 t) j
      (Host.addrOf (kT + 3 + 10)).toBitVec).load 1 0 8) ((elemEnv m0 st1.data 64 (valAddr m0 t) j
      (Host.addrOf (kT + 3 + 10)).toBitVec).load 1 8 8) = (ent ev t).2[j]'hjl := by
    rw [← ewOf_loads, Env.base_eq (b := valAddr m0 t + BitVec.ofNat 64 (16 * j)) (n := 16) rfl,
      add_ofNat_zero, Env.ofMachine_mem0]
    exact val_eq hpre hsm1 ht hjl
  refine exec_at hPk hPx hwfP (fun _ _ ↦ by rw [hPlen]; rfl) hpc1' hmP fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hPr, hPw⟩ := hPok
  have gr2 : ∀ (r : Reg64) (v : Sym), (r, v) ∈ ([(.rdi, .reg .rbx), (.rsi, .bin .add .W64 (.reg R.c) (.lit 1)),
      (.rdx, .reg R.p), (.rcx, .reg R.l), (.r8, .load 1 0 8), (.r9, .load 1 8 8),
      (R.c, .bin .add .W64 (.reg R.c) (.lit 1)),
      (R.n, .bin .add .W64 (.lit 18446744073709551600) (.reg R.n)),
      (.r14, .bin .add .W64 (.reg R.a) (.lit 16)), (.rsp, .ptr 0 0), (.rbx, .reg .rbx),
      (R.p, .reg R.p), (R.l, .reg R.l)] : List (Reg64 × Sym)) →
      reg st2.data r = v.eval (elemEnv m0 st1.data 64 (valAddr m0 t) j
        (Host.addrOf (kT + 3 + 10)).toBitVec) := fun r v h ↦ hm2.regs r v (hPr (r, v) h)
  have hrsp2 : rspOf st2.data = stackBelow m0 64 := by
    show reg st2.data .rsp = _
    rw [gr2 .rsp (.ptr 0 0) (by simp)]
    simp [Sym.eval]
  have hrdi : reg st2.data .rdi = reg m0 .rsi := by
    rw [gr2 .rdi (.reg .rbx) (by simp), eval_reg, Env.ofMachine_regs]; exact hL1.rbx
  have hrdx : reg st2.data .rdx = ptAddr m0 t := by
    rw [gr2 .rdx (.reg R.p) (by simp), eval_reg, Env.ofMachine_regs]; exact hL1.p
  have hrcx : reg st2.data .rcx = BitVec.ofNat 64 (plen ev t) := by
    rw [gr2 .rcx (.reg R.l) (by simp), eval_reg, Env.ofMachine_regs]; exact hL1.l
  have hrcxn : (reg st2.data .rcx).toNat = plen ev t := by
    rw [hrcx, BitVec.toNat_ofNat]; omega
  have hk2 : Kept m0.dmem st2.data.dmem := fun p h ↦ hm2.kept hwfP p (hL1.body.kept p h)
  have hnf : ∀ {x : BitVec 64} {n : Nat}, NoWrap x n → OffStack m0 x n N → ∀ p, InRange x n p →
      st2.data.dmem.get? p = st1.data.dmem.get? p := fun hnw hO p hp ↦
    frame_keep hwfP hm2 (by omega) hPw (not_inRange_le (by omega) (not_frame hS h64 hnw hO hp))
  have hsm2 : Same m0.dmem st2.data.dmem (reg m0 .rdi) tableEvalsBytes := fun i hi ↦ by
    rw [hnf hev.1.2 hev.2.1 _ (NativeRustcVm.inRange_add hi (by have := hev.1.2; unfold NoWrap at this; omega))]
    exact hsm1 i hi
  let cs' := cs ++ (pre ev t j).toArray
  have hsize : cs'.size = cs.size + (pre ev t j).length := by simp [cs']
  have hjc : j < (claimsOf ev t).length := by rw [length_claimsOf]; exact hjl
  have hpre_lt := length_pre_lt ht hjc (size_ev hpre)
  refine Body.call (hpush cs') hL1.body hS (by decide : 64 + pushClaimStack ≤ N) (by omega : 8 ≤ 64)
    (fun p hp' ↦ ⟨(slots_ok p hp').1.trans' (by omega), (slots_ok p hp').2⟩)
    (fun p hp' ↦ not_frame hS h64 hCR.2 hCO hp') hwfP hmP hm2 (by rw [hPlen] at hpc2; exact hpc2)
    (by rw [freeRegs_slots]; rfl) (hPr (.rsp, .ptr 0 0) (by simp)) hPw
    (fun hst ↦ ?_) (fun m' hq ↦ ?_) fun st3 hpc3 hb3 hpost hsv hfr ↦ ?_
  · -- `push_claim`'s precondition
    refine ⟨hst, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrdi]
      exact NativeRustcVm.Tables.ClaimsWAt.of_same hL1.claims fun i hi ↦
        hnf hCR.2 hCO _ (NativeRustcVm.inRange_add hi (by have := hCR.2; unfold NoWrap at this; omega))
    · rw [hrdi]; exact ⟨fun i hi ↦ hk2 _ (hCR.1 i hi), hCR.2⟩
    · rw [hrdi]; exact offStack_callee hS hCO hrsp2 (by decide)
    · show Readable _ _ (16 * (reg st2.data .rcx).toNat) ∧
        OffStack _ _ (16 * (reg st2.data .rcx).toNat) _
      rw [hrdx, hrcxn]
      exact ⟨⟨fun i hi ↦ hk2 _ (hpp.1.1 i hi), hpp.1.2⟩,
        offStack_callee hS hpp.2.1 hrsp2 (by decide)⟩
    · rw [hrdi, hrdx, hrcxn]; exact apart_symm hpp.2.2
  · exact ⟨fun p hp' ↦ hq.2.1 p fun h ↦ hp' (by rw [hrdi] at h; exact h), hq.2.2⟩
  -- the block after the call
  refine exec_at hAk hAx (Env.wf_nil _) (fun _ h ↦ by cases h) hpc3 (match_nil _)
    fun st4 hm4 hpc4 ↦ ?_
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq (Env.wf_nil _) hAm
  have hk4 : ∀ r, r ∉ [R.a, .rax, .rcx] → reg st4.data r = reg st3.data r := fun r hr ↦
    keptBut_reg hm4 hAk' hr
  have hb4 : Bd m0 st4.data := Body.congr hb3 (fun r hc ↦ hk4 r (by
      intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · subst h; rw [hRa.1] at hc; cases hc
      · subst h; simp [calleeSaved] at hc
      · subst h; simp [calleeSaved] at hc)) (hk4 .rsp (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h ↦ hRa.2 h.symm, by decide, by decide⟩)) hd4
  have hkR : ∀ r, calleeSaved r = true → r ∉ [R.a, .rax, .rcx] → reg st4.data r = reg st2.data r :=
    fun r hc hr ↦ (hk4 r hr).trans (hsv r hc)
  have hnot : ∀ r, calleeSaved r = true → r ∉ [R.a, Reg64.rax, .rcx] := fun r hc h ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · subst h; rw [hRa.1] at hc; cases hc
    · subst h; simp [calleeSaved] at hc
    · subst h; simp [calleeSaved] at hc
  have e2 : ∀ r, (r, Sym.reg r) ∈ ([(.rdi, .reg .rbx), (.rsi, .bin .add .W64 (.reg R.c) (.lit 1)),
      (.rdx, .reg R.p), (.rcx, .reg R.l), (.r8, .load 1 0 8), (.r9, .load 1 8 8),
      (R.c, .bin .add .W64 (.reg R.c) (.lit 1)),
      (R.n, .bin .add .W64 (.lit 18446744073709551600) (.reg R.n)),
      (.r14, .bin .add .W64 (.reg R.a) (.lit 16)), (.rsp, .ptr 0 0), (.rbx, .reg .rbx),
      (R.p, .reg R.p), (R.l, .reg R.l)] : List (Reg64 × Sym)) → reg st2.data r = reg st1.data r :=
    fun r h ↦ gr2 r _ h
  obtain ⟨hres, -, -⟩ := hpost
  rw [hrdi, hrcxn] at hres
  have hpl : plen ev t ≤ pointCap := by unfold pointCap; omega
  simp only [PcOk] at hpc4
  have hcond : (alNZ x).eval (Env.ofMachine st3.data [] (fun _ ↦ 0) 0) =
      !decide ((reg st3.data .rax).toNat % 256 = 0) := by
    simp only [alNZ, SBool.eval, Sym.eval]
    rw [NativeRustcVmX64.Sumcheck.testAl_eq, hx]
    rfl
  rw [hcond] at hpc4
  obtain ⟨hT4, hF4⟩ := pc_cond hpc4
  by_cases hfit : cs'.size < claimCap
  · -- pushed: back to the head
    simp only [hfit, hpl, and_self, ↓reduceIte] at hres
    obtain ⟨hal, hcl⟩ := hres
    have hal' : (reg st3.data .rax).toNat % 256 ≠ 0 := by
      unfold boolRet at hal; rw [hal]; decide
    have hpc4' := (hT4 (by simp [hal'])).trans hlT
    have hev8 : fw m0 st4.data 8 = reg m0 .rdi := by
      unfold fw
      rw [hd4, NativeRustcVm.wordOf_congr (d := st1.data.dmem) fun i hi ↦ ?_]
      · exact hL1.ev8
      · rw [addr_add, hfr (8 + i) (by omega), frame_keep hwfP hm2 (by omega) hPw ?_]
        rw [Sym.inRange_iff (by have := frame_noWrap (stackOk_mono hS h64); omega),
          toNat_add_ofNat _ _ (by have := frame_noWrap (stackOk_mono hS h64); omega)]
        omega
    have hr14 : reg st2.data .r14 = valAddr m0 t + BitVec.ofNat 64 (16 * (j + 1)) := by
      rw [gr2 .r14 (.bin .add .W64 (.reg R.a) (.lit 16)) (by simp), eval_add, eval_reg, eval_lit, Env.ofMachine_regs]
      show reg st1.data R.a + _ = _
      rw [hL1.a, add16']
    refine .done _ (Or.inr ⟨cnt ev t - (j + 1), by omega, hpc4', j + 1, rfl, hb4, hev8, ?_, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [hkR .rbx rfl (hnot .rbx rfl), e2 .rbx (by simp)]; exact hL1.rbx
    · rw [show reg st4.data R.a = _ from hm4.regs _ _ hAr, eval_reg, Env.ofMachine_regs]
      show reg st3.data .r14 = _
      rw [hsv .r14 rfl]; exact hr14
    · rw [hkR R.n hR.1.1 (hnot _ hR.1.1), gr2 R.n (.bin .add .W64 (.lit 18446744073709551600) (.reg R.n)) (by simp), eval_add, eval_lit, eval_reg,
        Env.ofMachine_regs]
      show _ + reg st1.data R.n = _
      rw [hL1.n, sub16 (by omega) (by omega), Nat.sub_sub]
    · rw [hkR R.p hR.2.1.1 (hnot _ hR.2.1.1), e2 R.p (by simp)]; exact hL1.p
    · rw [hkR R.l hR.2.2.1.1 (hnot _ hR.2.2.1.1), e2 R.l (by simp)]; exact hL1.l
    · rw [hkR R.c hR.2.2.2.1.1 (hnot _ hR.2.2.2.1.1), gr2 R.c (.bin .add .W64 (.reg R.c) (.lit 1)) (by simp), eval_add, eval_lit,
        eval_reg, Env.ofMachine_regs]
      show reg st1.data R.c + _ = _
      rw [hL1.c, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [hd4, pre_succ t j hjc, app_push, getElem_claimsOf]
      convert hcl using 3
      · rw [gr2 .rsi (.bin .add .W64 (.reg R.c) (.lit 1)) (by simp), eval_add, eval_lit, eval_reg, Env.ofMachine_regs]
        show _ = (reg st1.data R.c + _).toNat
        rw [hL1.c, ← BitVec.ofNat_add, BitVec.toNat_ofNat]
        have h1 := base_ge ht
        have h2 := @base_lt t
        unfold base at h1 h2 ⊢
        omega
      · unfold slice
        rw [hrdx, hrcxn, point_eq hpre hsm2 ht]
        rfl
      · rw [gr2 .r8 (.load 1 0 8) (by simp), gr2 .r9 (.load 1 8 8) (by simp), eval_load, eval_load, hval]
        rfl
  · -- not pushed: the failure
    simp only [hfit, false_and, ↓reduceIte] at hres
    have hpc4' := hF4 (by unfold boolRet at hres; simp [hres])
    rw [hAlen] at hpc4'
    refine Eventually.mono (hfail st4 hpc4' hb4 (hAax _ _ hm4 hres) fun hf ↦ ?_) fun _ h ↦ Or.inl h
    unfold Fits at hf
    rw [hsize] at hfit
    omega

end

end NativeRustcVmX64.Tables.ColumnClaims
