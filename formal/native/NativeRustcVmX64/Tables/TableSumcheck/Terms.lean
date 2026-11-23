module

public import NativeRustcVmX64.Tables.TableSumcheck.Wts
public import NativeRustcVmX64.Bus.Common
public import NativeVm.Math.Tables.Weights
public import NativeRustcVmX64.Code.Vm.TableTerms.Names

/-!
# `table_sumcheck`: the terms and the final check (x86-64)

From `Wt`: `b11` stores the heights', the forms', the weights' and the evaluations' addresses as
`table_terms`' four stack arguments and calls it, its `Option<EW>` at `88` of the frame; `b12`
leaves for the rejection on `None`; `b13` compares the final sum with the claim (`48`, R14) into
AL and returns (`terms`).
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableSumcheck
open NativeRustcVmX64.Tables.TableTerms (at_pc addr_eq rin_sub)

public section

theorem stackArg_fb {m0 d : MachineData} (hsp : rspOf d = off (fb m0) 0) (i : Nat) {j : Nat}
    (hj : j = 8 + 8 * i) {w : UInt64} (hw : NativeRustcVm.WordAt d.dmem (off (fb m0) j) w) :
    stackArg d i = w.toBitVec := by
  subst hj
  unfold stackArg
  rw [hsp, off_add, Nat.zero_add, NativeRustcVm.wordOf_of_wordAt hw]

variable [Labels] {a : DecArea} {s s1 : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData}

/-- **The read-only data** for a callee at offset `o`. -/
theorem tablesAt_bd (h : TableSumcheckPre a s heights bus m0) {d : MachineData} {o : Nat}
    (hb : Bd m0 736 N slots (outs m0) o d) (ho : o ≤ 736) {Nc : Nat} (hn : 736 - o + Nc ≤ N) :
    TablesAt d Nc := by
  intro t
  have hR := Pre.tables h
  have hnwt := RodataAt.noWrap hR t
  refine ⟨NativeRustcVm.BytesAt.of_sameOutside (RodataAt.bytesAt hR t) hb.same fun i hi hq ↦ ?_,
    hnwt, hb.apart_at (Pre.stack h) ho hn (RodataAt.apart hR t)⟩
  have hin : NativeRustcVm.InRange (rodataAddr t) t.bytes.length (rodataAddr t + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi (by unfold NativeRustcVm.NoWrap at hnwt; omega)
  rcases hq with (hq | hq) | hq
  · exact NativeRustcVm.Apart.not_inRange (Pre.rt h t) (Pre.ts h).footprint.1.2 hnwt hq hin
  · exact NativeRustcVm.Apart.not_inRange (Pre.re h t) (ev_noWrap h) hnwt hq hin
  · exact NativeRustcVm.Apart.not_inRange (RodataAt.apart hR t) hnwt (stack_noWrap h) hin
      (inRange_mono hq (by omega))

/-- The regions `table_terms` writes, as its `ReadIn` lists them. -/
abbrev wsT (m0 d : MachineData) : List NativeRustcVm.Region :=
  [⟨off (fb m0) 88, 24⟩, ⟨tA m0, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩, ⟨rspOf d + 8#64, 32⟩]

omit [Labels] in
theorem rsp8 {d : MachineData} (hsp : rspOf d = off (fb m0) 0) :
    rspOf d + 8#64 = off (fb m0) 8 := by
  rw [hsp, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]

/-- **An input for `table_terms`.** -/
theorem rinT (h : TableSumcheckPre a s heights bus m0) {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) 0 d) {x : BitVec 64} {l : Nat}
    (hx : ReadIn m0 x l N (wsL m0)) : ReadIn d x l tableTermsStack (wsT m0 d) := by
  have hNle := N_ge
  refine ⟨⟨Mapped.keeps hx.1.1 hb.fr.kept, hx.1.2⟩,
    hb.apart_at (Pre.stack h) (by omega) (by omega) hx.2.1, fun w hw ↦ ?_⟩
  simp only [wsT, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact (ctx h).apart_of_stack (o := 88) (k := 24) hx.2.1 (by omega)
  · exact hx.2.2 ⟨tA m0, tstateBytes⟩ (by simp [wsL])
  · exact hx.2.2 ⟨ev m0, tableEvalsBytes⟩ (by simp [wsL])
  · show NativeRustcVm.Apart x l (rspOf d + 8#64) 32
    rw [rsp8 hb.fr.sp]
    exact (ctx h).apart_of_stack (o := 8) (k := 32) hx.2.1 (by omega)

/-- **A part of the frame from `112` as an input for `table_terms`.** -/
theorem rfrT (h : TableSumcheckPre a s heights bus m0) {d : MachineData}
    (hb : Bd m0 736 N slots (outs m0) 0 d) {o l : Nat} (ho : 112 ≤ o) (hol : o + l ≤ 736) :
    ReadIn d (off (fb m0) o) l tableTermsStack (wsT m0 d) := by
  have hNle := N_ge
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  have hat : At m0 736 d := Bd.atO h (o := 0) (by omega) hb
  have ok := (ctx h).outOk_frame hat (Nc := tableTermsStack) (by omega) (o := o) (n := l)
    (by omega) hol
  refine ⟨⟨ok.1, ok.2.1⟩, ok.2.2.2.2.1, fun w hw ↦ ?_⟩
  simp only [wsT, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · show NativeRustcVm.Apart (off (fb m0) o) l (off (fb m0) 88) 24
    unfold NativeRustcVm.Apart
    rw [toNat_off (by omega), toNat_off (by omega)]
    omega
  · exact Apart.symm' ((ctx h).apart_of_stack (Pre.tok h).1 hol)
  · exact Apart.symm' ((ctx h).apart_of_stack (Pre.evs h).2.2.2.2.1 hol)
  · show NativeRustcVm.Apart _ _ (rspOf d + 8#64) 32
    rw [rsp8 hb.fr.sp]
    unfold NativeRustcVm.Apart
    rw [toNat_off (by omega), toNat_off (by omega)]
    omega

end

public section

variable [Host] {k : Nat} {a : DecArea} {s s1 : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData} {xs : Array EW} {c : EW}

omit [Host] in
theorem ewArg_self (x : EW) : ewArg x.c0.toBitVec x.c1.toBitVec = x := by cases x; rfl

omit [Host] in
theorem beq_symm (x y : EW) : (x == y) = (y == x) := by
  have e : ∀ u v : UInt64, (u == v) = (v == u) := fun u v ↦ by
    by_cases huv : u = v
    · subst huv; rfl
    · rw [beq_eq_false_iff_ne.mpr huv, beq_eq_false_iff_ne.mpr (Ne.symm huv)]
  rw [ew_beq, ew_beq, e x.c0, e x.c1]

/-- **The terms and the check** (`b11` to `b13`). -/
theorem terms (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0)
    (htt : ∀ a s heights forms, Spec (Labels.label NativeRustcVmX64.Vm.TableTerms.entryLabel)
      (TableTermsPre a s heights forms) (TableTermsPost a s heights forms))
    (hsz : xs.size = nR heights)
    (hres : res s heights bus m0 = ((tableTerms (arrE m0 (cpA m0) 2) (arrE m0 (fpA m0) 3)
        xs.reverse (tableRows heights bus.forms (tableWeights heights bus.point xs.reverse))).run
          s1).bind fun q ↦ if q.1.1 == c then some (q.1.2, q.2) else none)
    {d : MachineData} (W : Wt a s1 heights bus m0 xs c d) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b11Offset)⟩ := by
  have hS := Pre.stack h
  have hH := Pre.hts h
  have hn30 : nR heights ≤ 30 := foldl_max_le heights hH.1 hH.2.1
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  have hNle := N_ge
  -- `b11`: the stack arguments.
  let ra := (Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b11Offset + b11.length)).toBitVec
  have hwf : (E m0 d [(argA m0, 16)] ra).WF :=
    frame_wf' hS (by unfold N tableSumcheckStack; omega) W.bd.fr.kept (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx; exact ⟨(Pre.args h).1, args_noWrap h⟩)
      (List.pairwise_pair.mpr (frame_args h))
  have hm : Match (E m0 d [(argA m0, 16)] ra) argS d := by
    refine match_body W.bd ⟨rfl, rfl, trivial⟩ ⟨?_, ?_, trivial⟩
    · show stackBelow m0 736 + BitVec.ofInt 64 744 = argA m0 + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 744 = BitVec.ofNat 64 (736 + 8) from rfl,
        show stackBelow m0 736 + BitVec.ofNat 64 (736 + 8) = off (stackBelow m0 736) (736 + 8)
          from rfl, frame_add, ofInt_zero64, BitVec.add_zero]
    · show stackBelow m0 736 + BitVec.ofInt 64 752 = argA m0 + BitVec.ofInt 64 8
      rw [show BitVec.ofInt 64 752 = BitVec.ofNat 64 (736 + 16) from rfl,
        show stackBelow m0 736 + BitVec.ofNat 64 (736 + 16) = off (stackBelow m0 736) (736 + 16)
          from rfl, frame_add, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
      unfold argA
      rw [NativeRustcVm.addr_add_add]
  refine exec_then (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf (fun _ _ ↦ rfl) hm
    fun st hm1 hpc1 ↦ ?_
  obtain ⟨mid1, W1, wr1, w8, w16, w24, w32, rdi1, rsi1, rdx1, rcx1, r8_1, r9_1, k1⟩ := ok_b11
  obtain ⟨hb1, hso1⟩ := blockB h W.bd hwf hm1 mid1 W1
  have hin1 := writesIn_of_mid mid1
  have rg : ∀ {r : Reg64} {v : Sym}, (after b11 argS).reg r = some v →
      reg st.data r = v.eval (E m0 d [(argA m0, 16)] ra) := fun hv ↦ hm1.regs _ _ hv
  have kw : ∀ {o : Nat} {w : UInt64}, 40 ≤ o → o + 8 ≤ 744 →
      NativeRustcVm.WordAt d.dmem (off (fb m0) o) w →
      NativeRustcVm.WordAt st.data.dmem (off (fb m0) o) w := fun h1 h2 hx ↦
    keepW hwf hm1 hin1 (by omega) (fun w hw _ ↦ by have := wr1 w hw; omega) hx
  have kE : ∀ {o : Nat} {L : List EW}, 40 ≤ o → o + 16 * L.length ≤ 744 →
      NativeRustcVm.EWsAt d.dmem (off (fb m0) o) L →
      NativeRustcVm.EWsAt st.data.dmem (off (fb m0) o) L := fun {o L} h1 h2 hx ↦
    keep_frame hwf hm1 hin1 (bs := L.flatMap NativeRustcVm.ewBytes)
      (by rw [NativeRustcVm.length_ewsBytes]; omega) (fun w hw _ ↦ by have := wr1 w hw; omega) hx
  have hsp : rspOf st.data = off (fb m0) 0 := hb1.fr.sp
  have a0 : stackArg st.data 0 = hA m0 :=
    stackArg_fb hsp 0 rfl (wroteW hm1 (by omega) w8 (w := .ofBitVec (hA m0)) W.rbx)
  have a1 : stackArg st.data 1 = bA m0 :=
    stackArg_fb hsp 1 rfl (wroteW hm1 (by omega) w16 (w := .ofBitVec (bA m0)) W.rbp)
  have a2 : stackArg st.data 2 = off (fb m0) 592 :=
    stackArg_fb hsp 2 rfl (wroteW hm1 (by omega) w24 (w := .ofBitVec (off (fb m0) 592)) W.r12)
  have a3 : stackArg st.data 3 = ev m0 := by
    refine stackArg_fb hsp 3 rfl (wroteW hm1 (by omega) w32 (w := .ofBitVec (ev m0)) ?_)
    show (E m0 d [(argA m0, 16)] ra).load 1 8 8 = _
    rw [NativeRustcVmX64.Tables.TableTerms.load_eq_wordOf]
    exact arg_word h W.bd (j := 1) (by omega)
  have e_rdi : reg st.data .rdi = off (fb m0) 88 := (rg rdi1).trans (eval_ptr0 88)
  have e_rsi : reg st.data .rsi = tA m0 := (rg rsi1).trans (ld0 W.w80)
  have e_rdx : reg st.data .rdx = cpA m0 := (rg rdx1).trans (ld0 W.w56)
  have e_rcx : reg st.data .rcx = fpA m0 := (rg rcx1).trans (ld0 W.w64)
  have e_r8 : reg st.data .r8 = off (fb m0) 112 := (rg r8_1).trans W.r15
  have e_r9 : reg st.data .r9 = BitVec.ofNat 64 (nR heights) := (rg r9_1).trans W.r13
  have t1 : TStateAt st.data.dmem (tA m0) a s1 :=
    W.ts.frame (hm1.kept hwf) (fun q hq ↦ (ctx h).stack_not_t (fr_stack h hq)) hso1
  have pt1 := kE (by omega) (by rw [List.length_reverse, Array.length_toList]; omega) W.pt
  have hws : (tableWeights heights bus.point xs.reverse).toList.length = 6 := by
    rw [Array.length_toList, NativeVm.Math.Tables.tableWeights_size, hH.1]; rfl
  have w1 := kE (by omega) (by rw [hws]; omega) W.w
  -- `table_terms`' precondition.
  have hat : At m0 736 st.data := Bd.atO h (o := 0) (by omega) hb1
  have hle : 736 + tableTermsStack ≤ N := hNle.1
  have e9 : (BitVec.ofNat 64 (nR heights)).toNat = nR heights := toNat_ofNat_lt (by omega)
  have hpre : TableTermsPre a s1 heights bus.forms st.data := by
    unfold TableTermsPre
    simp only [e_rdi, e_rsi, e_rdx, e_rcx, e_r8, e_r9, a0, a1, a2, a3, e9]
    refine ⟨hb1.stackOk_at hS (by omega) (by omega), (ctx h).rcAt hat hle,
      tablesAt_bd h hb1 (by omega) (by omega), ?_, t1, (ctx h).tstateOk hat hle,
      (ctx h).outOk_frame hat hle (o := 88) (n := 24) (by omega) (by omega),
      (ctx h).outOk hat hle (Pre.evs h),
      Apart.symm' ((ctx h).apart_of_stack (o := 88) (k := 24) (Pre.evs h).2.2.2.2.1 (by omega)),
      ?_, ?_, ?_, Pre.rt h,
      fun t ↦ Apart.symm' ((ctx h).apart_of_stack (o := 88) (k := 24)
        (RodataAt.apart (Pre.tables h) t) (by omega)),
      Pre.re h, hn30,
      rinT h hb1 (Pre.cp h), rinT h hb1 (Pre.fp h), rfrT h hb1 (by omega) (by omega),
      rinT h hb1 (Pre.hs h), heights_bd h hb1, ?_, (bus_bd h hb1).formsAt,
      rfrT h hb1 (by omega) (by omega), ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [rsp8 hsp]
        exact mapped_off (Mapped.keeps (frame_mapped hS (by unfold N tableSumcheckStack; omega))
          hb1.fr.kept) (by omega)
      · rw [hsp, toNat_off (by omega)]
        omega
    · rw [rsp8 hsp]
      show NativeRustcVm.Apart _ _ _ _
      unfold NativeRustcVm.Apart
      rw [toNat_off (by omega), toNat_off (by omega)]
      omega
    · rw [rsp8 hsp]
      exact (ctx h).apart_of_stack (o := 8) (k := 32) (Pre.tok h).1 (by omega)
    · rw [rsp8 hsp]
      exact (ctx h).apart_of_stack (o := 8) (k := 32) (Pre.evs h).2.2.2.2.1 (by omega)
    · have := rinT h hb1 (rin_sub (Pre.bs h) (o := 0) (k := formsBytes) (by decide))
      rwa [NativeRustcVm.addr_add_zero] at this
    · rw [rsp8 hsp]
      refine got_call h hb1 (by omega) hle ?_
      intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact got_apart_frame (Pre.got h) hS hl (ob := 88) (len := 24) (by omega) (by decide)
      · exact ((Pre.got h).1 l hl).2.2.2 (tA m0, tstateBytes) (by simp)
      · exact ((Pre.got h).1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
      · exact ((Pre.got h).1 l hl).2.2.2 (ev m0, tableEvalsBytes) (by simp)
      · exact got_apart_frame (Pre.got h) hS hl (ob := 8) (len := 32) (by omega) (by decide)
      · exact ((Pre.got h).1 l hl).2.2.2 (cpA m0, 32) (by simp)
      · exact ((Pre.got h).1 l hl).2.2.2 (fpA m0, 48) (by simp)
      · exact got_apart_frame (Pre.got h) hS hl (ob := 112) (len := 16 * nR heights)
          (by omega) (by omega)
      · exact ((Pre.got h).1 l hl).2.2.2 (hA m0, 48) (by simp)
      · change Apart (gotAddr l) 8 (bA m0) formsBytes
        have hg : Apart (gotAddr l) 8 (bA m0) busBytes :=
          ((Pre.got h).1 l hl).2.2.2 (bA m0, busBytes) (by simp)
        exact Apart.sub hg (Nat.le_refl _) (by
          have hsize : formsBytes ≤ busBytes := by decide
          omega)
      · exact got_apart_frame (Pre.got h) hS hl (ob := 592) (len := 96) (by omega) (by decide)
      · exact ((Pre.got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)
      · exact ((Pre.got h).1 l hl).2.2.2
          (rodataAddr .tables, NativeRustcVm.Data.Item.tables.bytes.length) (by simp)
  -- The model's terms.
  have hcp : arrE st.data (cpA m0) 2 = arrE m0 (cpA m0) 2 := by
    unfold arrE
    rw [NativeRustcVm.ewsOf_congr fun i hi ↦ same_readIn h hb1 (Pre.cp h) i (by omega)]
  have hfp : arrE st.data (fpA m0) 3 = arrE m0 (fpA m0) 3 := by
    unfold arrE
    rw [NativeRustcVm.ewsOf_congr fun i hi ↦ same_readIn h hb1 (Pre.fp h) i (by omega)]
  have hpt : slice st.data (off (fb m0) 112) (BitVec.ofNat 64 (nR heights)) = xs.reverse := by
    rw [slice_eq pt1 (by rw [List.length_reverse, Array.length_toList, hsz]) (by omega)]
    exact Array.toList_inj.mp (by simp)
  have hwt : (NativeRustcVm.ewsOf st.data.dmem (off (fb m0) 592) nTables).toArray =
      tableWeights heights bus.point xs.reverse := by
    have := NativeRustcVm.ewsOf_of_ewsAt w1
    rw [hws] at this
    rw [show nTables = 6 from rfl, this]
  simp only [PcOk] at hpc1
  refine call_then (env := E m0 d [(argA m0, 16)] ra) hpc1 (htt a s1 heights bus.forms) hpre
    fun st2 hpc2 hrsp2 hq ↦ ?_
  unfold TableTermsPost at hq
  simp only [e_rdi, e_rsi, e_rdx, e_rcx, e_r8, e_r9, a2, a3, hcp, hfp, hpt, hwt] at hq
  generalize hR : (tableTerms (arrE m0 (cpA m0) 2) (arrE m0 (fpA m0) 3) xs.reverse
    (tableRows heights bus.forms (tableWeights heights bus.point xs.reverse))).run s1 = R at hq hres
  obtain ⟨q0, q1, q2, q3, q4⟩ := hq
  have hb2 := call_frame h hb1 (by omega) (by omega) q4 hrsp2 (Ro := fun q ↦
    NativeRustcVm.InRange (off (fb m0) 88) 24 q ∨ outs m0 q)
    (NativeRustcVm.SameOutside.mono q3 fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inl (.inl hq)
      · exact .inl (.inr (.inl hq))
      · exact .inl (.inr (.inr hq))
      · exact .inr hq)
    fun q hq ↦ hq.elim (fun hq ↦ .inr ⟨88, 24, by omega, hq⟩) .inl
  have hd2 : ∀ {j : Nat} {w : UInt64}, 8 ≤ j → j + 8 ≤ 88 →
      NativeRustcVm.WordAt st.data.dmem (off (fb m0) j) w →
      NativeRustcVm.WordAt st2.data.dmem (off (fb m0) j) w := fun h1 h2 hx ↦
    keepB_call h hb1 (by omega) (by omega) (NativeRustcVm.SameOutside.mono q3 fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inl (.inl hq)
      · exact .inl (.inr (.inl hq))
      · exact .inl (.inr (.inr hq))
      · exact .inr hq) (Ro := fun q ↦ NativeRustcVm.InRange (off (fb m0) 88) 24 q ∨ outs m0 q)
      (by omega) (by rw [NativeRustcVm.length_wordBytes]; omega) (fun i hi hq ↦ by
        rw [NativeRustcVm.length_wordBytes] at hi
        rcases hq with hq | hq
        · rw [inRange_off_iff (by omega) (by omega)] at hq; omega
        · exact outs_not_frame h hq (inRange_off_self (by omega) (by omega))) hx
  have w48 := hd2 (by omega) (by omega) (kw (by omega) (by omega) W.w48)
  -- `b12`: the `Option`'s tag.
  have hwf2 : (E m0 st2.data [] 0).WF := wf_nil h hb2.fr.kept
  have hm2 : Match (E m0 st2.data [] 0) tS st2.data := match_body hb2 ⟨rfl, trivial⟩ trivial
  refine at_pc (hpc2.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b11_next)))
    (exec_then (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf2 nofun hm2
      fun st3 hm3 hpc3 ↦ ?_)
  obtain ⟨mid3, mem3, k3⟩ := ok_b12
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 mem3
  have hb3 := (blockB h hb2 hwf2 hm3 mid3 (by rw [WrOk, mem3]; rfl)).1
  simp only [PcOk] at hpc3
  cases R with
  | none =>
    have hl := NativeRustcVmX64.Transcript.load1_of_tag (env := E m0 st2.data [] 0) (r := 0)
      (o := 88) (w := 0) (Or.inl rfl) q0
    have hc : (SBool.cmp .eq .W8 (.load 0 88 1) (.lit 0)).eval (E m0 st2.data [] 0) = true := by
      simp only [SBool.eval, Sym.eval, hl, CmpOp.apply]
      decide
    rw [hc] at hpc3
    simp only [↓reduceIte] at hpc3
    exact at_pc (hpc3.trans (lbl_11 hp)) (exit_fail hp h hb3 (by rw [hres]; rfl))
  | some p =>
    obtain ⟨⟨f, evs⟩, s2⟩ := p
    obtain ⟨tag, hf⟩ := q0
    have hl := NativeRustcVmX64.Transcript.load1_of_tag (env := E m0 st2.data [] 0) (r := 0)
      (o := 88) (w := 1) (Or.inr rfl) tag
    have hc : (SBool.cmp .eq .W8 (.load 0 88 1) (.lit 0)).eval (E m0 st2.data [] 0) = false := by
      simp only [SBool.eval, Sym.eval, hl, CmpOp.apply]
      decide
    rw [hc] at hpc3
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
    -- `b13`: the comparison.
    have hwf3 : (E m0 st3.data [] 0).WF := wf_nil h hb3.fr.kept
    have hm3' : Match (E m0 st3.data [] 0) sF st3.data := match_body hb3 ⟨rfl, trivial⟩ trivial
    refine at_pc (hpc3.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b12_next)))
      (exec_then (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf3 nofun hm3'
        fun st4 hm4 hpc4 ↦ ?_)
    obtain ⟨mid4, mem4, rax4⟩ := ok_b13
    have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 mem4
    have hb4 := (blockB h hb3 hwf3 hm4 mid4 (by rw [WrOk, mem4]; rfl)).1
    have hf' := NativeRustcVm.ewAt_iff.mp hf
    rw [off_off, off_add] at hf'
    have l48 := ld0 (rest := []) (ret := 0) (d := st3.data) (by rw [hd3]; exact w48)
    have l96 := ld0 (rest := []) (ret := 0) (d := st3.data) (by rw [hd3]; exact hf'.1)
    have l104 := ld0 (rest := []) (ret := 0) (d := st3.data) (by rw [hd3]; exact hf'.2)
    have r14 : reg st3.data .r14 = c.c1.toBitVec := by
      refine (keeps_reg hm3 k3 (by simp)).trans ?_
      refine (show reg st2.data .r14 = reg st.data .r14 from q4.1 .r14 rfl).trans ?_
      exact (keeps_reg hm1 k1 (by simp)).trans W.r14
    have hax : boolRet st4.data = (okWord (f == c)).toNat := by
      unfold boolRet
      rw [show reg st4.data .rax = _ from hm4.regs _ _ rax4]
      show (BinOp.apply .merge .W8 _ (if CmpOp.apply .eq .W64 (BinOp.apply .or .W64
        (BinOp.apply .xor .W64 (reg st3.data .r14) ((Sym.load 0 104 8).eval (E m0 st3.data [] 0)))
        (BinOp.apply .xor .W64 ((Sym.load 0 48 8).eval (E m0 st3.data [] 0))
          ((Sym.load 0 96 8).eval (E m0 st3.data [] 0)))) (BitVec.ofNat 64 0) = true
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)).toNat % 256 = _
      rw [r14, l48, l96, l104, NativeRustcVmX64.Bus.sete_ew, ewArg_self, ewArg_self, beq_symm]
    have hres' : res s heights bus m0 = if f == c then some (evs, s2) else none := by
      rw [hres]; rfl
    simp only [PcOk] at hpc4
    refine at_pc (hpc4.trans (lbl_12 hp))
      (exit15 hp h hb4 fun d' hd' hra ↦ ⟨?_, ?_, ?_⟩)
    · unfold OkAl
      rw [hres']
      have : boolRet d' = boolRet st4.data := by unfold boolRet; rw [hra]
      rw [this, hax]
      cases f == c <;> rfl
    · intro x s' h'
      rw [hres'] at h'
      split at h'
      · cases h'
        rw [hd', hd4, hd3]
        exact q1 (f, evs) s2 rfl
      · cases h'
    · intro x s' h'
      rw [hres'] at h'
      split at h'
      · cases h'
        rw [hd', hd4, hd3]
        exact q2 (f, evs) s2 rfl
      · cases h'

end

end NativeRustcVmX64.Tables.TableSumcheck
