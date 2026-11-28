module

public import NativeRustcVmArm.Code.Vm.TableTerms.Names
public import NativeRustcVmArm.Tables.TableSumcheck.Weights
public import NativeRustcVmArm.Tables.TableSumcheck.Entry

/-!
# `table_sumcheck`: the terms and the final check

From `Wt`: `b7` stores the weights' address and the evaluations' as `table_terms`' stack
arguments and calls it, its `Option<EW>` at `600` of the frame; `b8` leaves for the rejection on
`None`; `b9` compares the final sum with the claim (X26, X27) into X0; `b11` returns (`terms`).
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableSumcheck
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm.Bus (BusWAt busBytes formsBytes)
open NativeRustcVmArm.Sumcheck (Ctx)
open NativeRustcVm (ewOf ewsOf wordOf)

public section

theorem size_tableWeights (heights : Array Nat) (eqp point : Array EW) :
    (tableWeights heights eqp point).size = heights.size := by
  rw [tableWeights_eq, size_twPrefix]

theorem loadSym_b7 : loadSym (Bus.after b7 sF).mem 0 0 8 = .reg .X28 ∧
    loadSym (Bus.after b7 sF).mem 0 8 8 = .reg .X24 := by
  rw [ok_b7.2.1]; decide

section
variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData} {n : Nat} {xs : Array EW} {c : EW} {s1 : TState}

/-- **The terms and the check** (`b7` to `b11`). -/
theorem terms (hp : Placed code k)
    (htt : ∀ a s heights forms, Spec (Labels.label NativeRustcVmArm.Vm.TableTerms.entryLabel)
      (TableTermsPre a s heights forms) (TableTermsPost a s heights forms))
    (hpre : TableSumcheckPre a s heights bus m0) (hn30 : n ≤ 30) (hxs : xs.size = n)
    (hres : res s heights bus m0 = ((tableTerms (arrE m0 m0.regs.X3 2) (arrE m0 m0.regs.X4 3)
        xs.reverse (tableRows heights bus.forms (tableWeights heights bus.point xs.reverse))).run
          s1).bind fun q ↦ if q.1.1 == c then some (q.1.2, q.2) else none)
    {m : MachineData} (hW : Wt m0 a n xs c s1 heights bus m) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b7Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hrc, hT, hts0, htok, heo, hRt, hRe, hHin, hH, hBin, -, hcpIn, hfpIn⟩ := hpre'
  have hN := hS.2.1
  have h720 : 720 ≤ tableSumcheckStack := N_ge
  have hSP := m0.regs.SP.toNat_lt
  have hfb := fb_toNat hS N_ge
  have cx : Ctx m0 m0.regs.X0.toBitVec a tableSumcheckStack 720 :=
    Bus.Gkr.ctx_of hS hrc hts0 htok N_ge rfl
  have hof : ∀ q, outs m0 q → ¬InRange (base m0 720) 720 q := fun q hq ↦
    hq.elim (Bus.Gkr.tstate_not_frame cx) (Bus.Gkr.out_not_frame cx heo)
  have hor : ∀ q, outs m0 q → ¬InRange rcAddr 192 q := fun q hq ↦
    hq.elim cx.not_rc_tstate (Bus.Gkr.out_not_rc cx heo)
  have hrod : ∀ q, outs m0 q → ∀ t : NativeRustcVm.Data.Item,
      ¬InRange (rodataAddr t) t.bytes.length q := fun q hq t ↦ hq.elim
    (fun h ↦ not_rodata hts0.footprint.1.2 hRt (fun t ↦ (hT t).2.1) h t)
    (fun h ↦ not_rodata heo.2.1 hRe (fun t ↦ (hT t).2.1) h t)
  -- `b7`.
  have hwf := Bus.wf_frame hS N_ge hW.fr.kept
  have hm := Bus.match_frame hS N_ge rfl hW.fr.sp
  refine exec_then (b7_in_code.trans hp.1 (by simp [b7])) run_b7 hwf hm fun st hm7 hpc ↦ ?_
  have hm7' : Match (Env.ofMachine m [(base m0 720, 720)]) (Bus.after b7 sF) st.data := by
    rw [Bus.after_eq run_b7]; exact hm7
  obtain ⟨hsp7, hmem7, hk7, g0, g1, g2, g3, g4, g5, g6, g7⟩ := ok_b7
  have hmw : ∀ w ∈ (Bus.after b7 sF).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by
    rw [hmem7]; decide
  have hfr7 : Fr m0 720 tableSumcheckStack slots keep (outs m0) st.data :=
    Bus.Fr.block hW.fr hN N_ge hm7' hwf hsp7 (fun w hw ↦ by
      obtain ⟨h1, h2⟩ := hmw w hw
      exact ⟨h1, by omega, fun p hp ↦ .inl (by have := slots_hi p hp; omega)⟩) nofun slots_le
  have hkb : ∀ {o L : Nat} {bs : List UInt8}, 16 ≤ o → o + L ≤ 720 → bs.length ≤ L →
      NativeRustcVm.BytesAt m.dmem (base m0 720 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st.data.dmem (base m0 720 + BitVec.ofNat 64 o) bs :=
    fun {o L bs} h1 h2 h3 h ↦ Bus.Gkr.keep_block hm7' hwf (sizes := [720]) rfl rfl (L := L)
      (by omega) (fun w hw ↦ .inl ⟨(hmw w hw).1, .inl (by have := (hmw w hw).2; omega)⟩) h3 h
  have hts7 : TStateAt st.data.dmem m0.regs.X0.toBitVec a s1 :=
    tstate_keep cx (fun q hq ↦ Bus.frame_inRange hN N_ge (Bus.Written.inRange rfl
      (base_noWrap (by omega)) (fun w hw ↦ ⟨(hmw w hw).1, by have := (hmw w hw).2; omega⟩) hq))
      hW.ts (hm7'.kept hwf) (hm7'.sameOutside hwf)
  have pt7 := hkb (o := 24) (L := 576) (by omega) (by omega)
    (by rw [NativeRustcVm.length_ewsBytes]; simp [hxs]; omega) hW.pt
  have w7 := hkb (o := 504) (L := 96) (by omega) (by omega)
    (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_tableWeights, hH.1]
        simp [nTables]) hW.w
  have rk : ∀ r ∈ mids, st.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    Bus.Gkr.reg_of hm7' (reg_keep hk7 hr)
  have e0 : st.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 600 := by
    show (st.data.regs.getXReg .X0).toBitVec = _
    rw [hm7'.regs .X0 _ g0]; simp [Sym.eval]
  have e1 : st.data.regs.X1 = m0.regs.X0 := by
    show st.data.regs.getXReg .X1 = _
    rw [Bus.Gkr.reg_of hm7' g1]; exact hW.regs.x23
  have e2 : st.data.regs.X2 = m0.regs.X3 := by
    show st.data.regs.getXReg .X2 = _
    rw [Bus.Gkr.reg_of hm7' g2]; exact hW.regs.x22
  have e3 : st.data.regs.X3 = m0.regs.X4 := by
    show st.data.regs.getXReg .X3 = _
    rw [Bus.Gkr.reg_of hm7' g3]; exact hW.regs.x20
  have e4 : st.data.regs.X4.toBitVec = fb m0 + BitVec.ofNat 64 24 := by
    show (st.data.regs.getXReg .X4).toBitVec = _
    rw [hm7'.regs .X4 _ g4]; simp [Sym.eval]
  have e5 : st.data.regs.X5.toNat = n := by
    show (st.data.regs.getXReg .X5).toBitVec.toNat = _
    rw [Bus.Gkr.reg_of hm7' g5]; exact hW.regs.x25
  have e6 : st.data.regs.X6 = m0.regs.X1 := by
    show st.data.regs.getXReg .X6 = _
    rw [Bus.Gkr.reg_of hm7' g6]; exact hW.regs.x21
  have e7 : st.data.regs.X7 = m0.regs.X2 := by
    show st.data.regs.getXReg .X7 = _
    rw [Bus.Gkr.reg_of hm7' g7]; exact hW.regs.x19
  have ew0 : stackWord st.data 0 = fb m0 + BitVec.ofNat 64 504 := by
    unfold stackWord
    rw [hfr7.sp, match_wordOf hm7' hwf (r := 0) rfl (by omega), loadSym_b7.1]
    simp only [Sym.eval, Env.ofMachine_regs]
    exact hW.x28
  have ew8 : stackWord st.data 8 = m0.regs.X7.toBitVec := by
    unfold stackWord
    rw [hfr7.sp, match_wordOf hm7' hwf (r := 0) rfl (by omega), loadSym_b7.2]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hW.regs.x24]
  -- `table_terms`' precondition.
  have hle : 720 + tableTermsStack ≤ tableSumcheckStack := by
    unfold tableSumcheckStack; omega
  have hat := Bus.Gkr.Fr.at_ cx hfr7 hor
  have rin : ∀ {x : BitVec 64} {l : Nat}, ReadIn m0 x l tableSumcheckStack
      [⟨m0.regs.X0.toBitVec, tstateBytes⟩, ⟨m0.regs.X7.toBitVec, tableEvalsBytes⟩] →
      ReadIn st.data x l tableTermsStack [⟨fb m0 + BitVec.ofNat 64 600, 24⟩,
        ⟨m0.regs.X0.toBitVec, tstateBytes⟩, ⟨m0.regs.X7.toBitVec, tableEvalsBytes⟩] :=
    fun {x l} h ↦ by
      have h' := ReadIn.fr hfr7 hS hle h
      refine ⟨h'.1, h'.2.1, fun w hw ↦ ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact NativeRustcVm.Apart.symm (cx.apart_of_stack (o := 600) (k := 24) (by omega) h.2.1)
      · exact h.2.2 _ (by simp)
      · exact h.2.2 _ (by simp)
  have rfr : ∀ {o l : Nat}, o + l ≤ 600 →
      ReadIn st.data (fb m0 + BitVec.ofNat 64 o) l tableTermsStack
        [⟨fb m0 + BitVec.ofNat 64 600, 24⟩, ⟨m0.regs.X0.toBitVec, tstateBytes⟩,
          ⟨m0.regs.X7.toBitVec, tableEvalsBytes⟩] := fun {o l} hol ↦ by
    have hl := Bus.local_ok (o := o) (n := l) hS hle (by omega) hfr7.kept hfr7.sp
    refine ⟨hl.1, hl.2, fun w hw ↦ ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · unfold Apart
      simp only
      rw [fb_add hS N_ge (by omega), fb_add hS N_ge (by omega)]
      omega
    · exact cx.apart_of_stack (by omega) htok.1
    · exact cx.apart_of_stack (by omega) heo.2.2.2.2.1
  have hfs : ReadIn m0 m0.regs.X2.toBitVec formsBytes tableSumcheckStack
      [⟨m0.regs.X0.toBitVec, tstateBytes⟩, ⟨m0.regs.X7.toBitVec, tableEvalsBytes⟩] := by
    have := ReadIn.sub hBin (o := 0) (k := formsBytes) (by decide) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hpre7 : TableTermsPre a s1 heights bus.forms st.data := by
    refine ⟨hfr7.stackOk hS rfl hle, cx.rcAt hat hle, tablesAt_fr hfr7 hS hle hT hrod, ?_,
      by rw [e1]; exact hts7, by rw [e1]; exact cx.tstateOk hat hle,
      by rw [e1, e0]; exact cx.outOk hat hle (o := 600) (n := 24) (by omega),
      by rw [e1, ew8]; exact cx.outOk_sub hat hle heo,
      by rw [e0, ew8]; exact cx.apart_of_stack (by omega) heo.2.2.2.2.1,
      by rw [e1]; exact hRt,
      by rw [e0]; exact fun t ↦ cx.apart_of_stack (o := 600) (k := 24) (by omega) (hT t).2.2,
      by rw [ew8]; exact hRe, by rw [e5]; exact hn30, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfr7.sp]
      have := (Bus.local_ok (o := 0) (n := 16) hS hle (by omega) hfr7.kept hfr7.sp).1
      rwa [NativeRustcVm.addr_add_zero] at this
    · rw [e0, e1, ew8, e2]; exact rin hcpIn
    · rw [e0, e1, ew8, e3]; exact rin hfpIn
    · rw [e0, e1, ew8, e4, e5]; exact rfr (by omega)
    · rw [e0, e1, ew8, e6]; exact rin hHin
    · rw [e6]; exact heights_fr hpre hfr7
    · rw [e0, e1, ew8, e7]; exact rin hfs
    · rw [e7]; exact (bus_fr hpre hfr7).formsAt
    · rw [e0, e1, ew8, ew0]; exact rfr (by omega)
  -- The model's terms.
  have hcp : arrE st.data st.data.regs.X2 2 = arrE m0 m0.regs.X3 2 := by
    unfold arrE
    rw [e2, NativeRustcVm.ewsOf_congr fun i hi ↦ same_input hpre hfr7 hcpIn i (by omega)]
  have hfp : arrE st.data st.data.regs.X3 3 = arrE m0 m0.regs.X4 3 := by
    unfold arrE
    rw [e3, NativeRustcVm.ewsOf_congr fun i hi ↦ same_input hpre hfr7 hfpIn i (by omega)]
  have hpt : slice st.data st.data.regs.X4 st.data.regs.X5 = xs.reverse := by
    unfold slice
    rw [e4, e5]
    have := NativeRustcVm.ewsOf_of_ewsAt pt7
    simp only [Array.length_toList, Array.size_reverse, hxs] at this
    rw [this]
  have hws : (ewsOf st.data.dmem (stackWord st.data 0) nTables).toArray =
      tableWeights heights bus.point xs.reverse := by
    rw [ew0]
    have := NativeRustcVm.ewsOf_of_ewsAt w7
    rw [Array.length_toList, size_tableWeights, hH.1] at this
    rw [this]
  have hr : (tableTerms (arrE st.data st.data.regs.X2 2) (arrE st.data st.data.regs.X3 3)
      (slice st.data st.data.regs.X4 st.data.regs.X5) (tableRows heights bus.forms
        (ewsOf st.data.dmem (stackWord st.data 0) nTables).toArray)).run s1 =
      (tableTerms (arrE m0 m0.regs.X3 2) (arrE m0 m0.regs.X4 3) xs.reverse
        (tableRows heights bus.forms (tableWeights heights bus.point xs.reverse))).run s1 := by
    rw [hcp, hfp, hpt, hws]
  -- `table_terms`.
  have hpc' : st.pc = Labels.label NativeRustcVmArm.Vm.TableTerms.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b8Offset) := hpc
  refine Bus.Gkr.Fr.callLocal (o := 600) (n := 24)
    (X := fun q ↦ InRange (fb m0 + BitVec.ofNat 64 600) 24 q ∨ outs m0 q) hfr7 hN hle keep_callee
    (fun p hp ↦ ⟨by have := slots_hi p hp; omega, slots_le p hp⟩) (by omega) hof
    (fun q hq ↦ hq.elim .inr .inl) (htt a s1 heights bus.forms) hpc' hpre7
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q h ↦ ?_, hq.2.2.2.2⟩)
    fun m3 hfr3 hq3 hcs3 _ ↦ ?_
  · rw [e0, e1, ew8] at h
    rcases h with h | h | h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
    · exact .inl h
  obtain ⟨q0, q1, q2, -, -⟩ := hq3
  rw [hr, e0] at q0
  rw [hr, ew8] at q1
  rw [hr, e1] at q2
  -- `b8`: the `Option`'s tag.
  refine Bus.Gkr.Fr.runBlock hS N_ge rfl hfr3 (b8_in_code.trans hp.1 (by simp [b8])) run_b8'
    ok_b8.2.1 ok_b8.1 rfl rfl fun st8 hfr8 hd8 hm8 hpc8 ↦ ?_
  have x26 : st8.data.regs.getXReg .X26 = c.c0 := by
    rw [Bus.Gkr.reg_of hm8 (reg_keep ok_b8.2.2 (by simp)), hcs3 .X26 rfl, rk .X26 (by simp),
      hW.x26]
  have x27 : st8.data.regs.getXReg .X27 = c.c1 := by
    rw [Bus.Gkr.reg_of hm8 (reg_keep ok_b8.2.2 (by simp)), hcs3 .X27 rfl, rk .X27 (by simp),
      hW.x27]
  have hb0 : (Env.ofMachine m3 [(base m0 720, 720)]).base 0 = fb m0 := rfl
  simp only [PcOk] at hpc8
  cases hT : (tableTerms (arrE m0 m0.regs.X3 2) (arrE m0 m0.regs.X4 3) xs.reverse
      (tableRows heights bus.forms (tableWeights heights bus.point xs.reverse))).run s1 with
  | none =>
    rw [hT] at q0
    have hl : (Env.ofMachine m3 [(base m0 720, 720)]).load 0 600 4 = BitVec.ofNat 64 0 :=
      NativeRustcVmArm.Transcript.load4_of_tag (w := 0) (.inl rfl) (by rw [hb0]; exact q0)
    have hc : SBool.eval (Env.ofMachine m3 [(base m0 720, 720)])
        (.not (.bit .W32 (.load 0 600 4) 0)) = true := by
      show (!(low .W32 ((Env.ofMachine m3 [(base m0 720, 720)]).load 0 600 4)).getLsbD 0) = true
      rw [hl]; rfl
    rw [hc] at hpc8
    simp only [↓reduceIte] at hpc8
    have hres' : res s heights bus m0 = none := by rw [hres, hT]; rfl
    exact Bus.Gkr.at_pc (hpc8.trans (hp.label (j := NativeRustcVmArm.Vm.TableSumcheck.b10Offset) NativeRustcVmArm.Vm.TableSumcheck.label_7_at)) (fail10 hp hS hfr8 hres')
  | some p =>
    obtain ⟨⟨f, ev⟩, s2⟩ := p
    rw [hT] at q0 q1 q2
    obtain ⟨q0a, q0b⟩ := q0
    have hl : (Env.ofMachine m3 [(base m0 720, 720)]).load 0 600 4 = BitVec.ofNat 64 1 :=
      NativeRustcVmArm.Transcript.load4_of_tag (w := 1) (.inr rfl) (by rw [hb0]; exact q0a)
    have hc : SBool.eval (Env.ofMachine m3 [(base m0 720, 720)])
        (.not (.bit .W32 (.load 0 600 4) 0)) = false := by
      show (!(low .W32 ((Env.ofMachine m3 [(base m0 720, 720)]).load 0 600 4)).getLsbD 0) = false
      rw [hl]; rfl
    rw [hc] at hpc8
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc8
    rw [show k + NativeRustcVmArm.Vm.TableSumcheck.b8Offset + b8.length = k + NativeRustcVmArm.Vm.TableSumcheck.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableSumcheck.b8_next]] at hpc8
    have hf := NativeRustcVm.ewAt_iff.mp q0b
    -- `b9`: the comparison.
    refine Bus.Gkr.at_pc hpc8 (Bus.Gkr.Fr.runBlock hS N_ge rfl hfr8
      (b9_in_code.trans hp.1 (by simp [b9])) run_b9 rfl rfl rfl rfl
      fun st9 hfr9 hd9 hm9 hpc9 ↦ ?_)
    have hm9' : Match (Env.ofMachine st8.data [(base m0 720, 720)]) (Bus.after b9 sF)
        st9.data := by rw [Bus.after_eq run_b9]; exact hm9
    have hd8' : st8.data.dmem = m3.dmem := hd8
    have l608 : (Env.ofMachine st8.data [(base m0 720, 720)]).load 0 608 8 = f.c0.toBitVec := by
      apply load_word
      show NativeRustcVm.WordAt st8.data.dmem (fb m0 + BitVec.ofNat 64 608) f.c0
      rw [hd8']
      have := hf.1
      rwa [off, NativeRustcVm.addr_add_add] at this
    have l616 : (Env.ofMachine st8.data [(base m0 720, 720)]).load 0 616 8 = f.c1.toBitVec := by
      apply load_word
      show NativeRustcVm.WordAt st8.data.dmem (fb m0 + BitVec.ofNat 64 616) f.c1
      rw [hd8']
      have := hf.2
      rwa [off, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
        NativeRustcVm.addr_add_add] at this
    have hx0 : (st9.data.regs.getXReg .X0).toBitVec = (okWord (f == c)).toBitVec := by
      rw [hm9'.regs .X0 _ ok_b9.2.2.2]
      simp only [eqS, Sym.eval, SBool.eval, Env.ofMachine_regs, l608, l616, x26, x27]
      exact Bus.cset_ew f c
    have hres' : res s heights bus m0 = if f == c then some (ev, s2) else none := by
      rw [hres, hT]; rfl
    simp only [PcOk] at hpc9
    refine Bus.Gkr.at_pc (hpc9.trans (hp.label (j := NativeRustcVmArm.Vm.TableSumcheck.b11Offset) NativeRustcVmArm.Vm.TableSumcheck.label_8_at))
      (exit11 hp hS hfr9 fun m' hd' hx' ↦ ⟨?_, fun x s' h ↦ ?_, fun x s' h ↦ ?_⟩)
    · rw [hx', hres']
      apply UInt64.toBitVec_inj.mp
      rw [show st9.data.regs.X0 = st9.data.regs.getXReg .X0 from rfl, hx0]
      cases f == c <;> rfl
    · rw [hres'] at h
      split at h
      · cases h
        rw [hd', hd9, hd8']
        exact q1 (f, ev) s2 rfl
      · cases h
    · rw [hres'] at h
      split at h
      · cases h
        rw [hd', hd9, hd8']
        exact q2 (f, ev) s2 rfl
      · cases h

end

end

end NativeRustcVmArm.Tables.TableSumcheck
