module

public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Tables.ColumnClaims.Iter
public import NativeRustcVmArm.Tables.ColumnClaims.Setup
public import NativeRustcVmArm.Arrays.Common

/-!
# `table_column_claims`: from the entry to the loops, between them, and the exits

`shapes_eval`: the loop registers a setup block sets (`Shapes`), read off the table's entry.
`entry`: the prologue and table `0`'s setup (`b0`), to table `0`'s head. `next`: a table's setup
after the previous table's loop, to its head. The exits: `exit25` (the epilogue keeping X0),
`exit31` (X0 one: all claims pushed), `fail24` (X0 zero, then `exit25`), `failJ` (a jump to `b24`).
-/

namespace NativeRustcVmArm.Tables.ColumnClaims

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.TableColumnClaims
open NativeRustcVm.Tables
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap)

@[expose] public section

/-- What `table_column_claims` reaches. -/
abbrev Goal [Labels] (ev : Array (Array EW × Array EW)) (cs : Array ColumnClaimW) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ TableColumnClaimsPost ev cs m0 st.data

end

public section

theorem eval_ite_ult [Labels] (env : Env) (c : Sym) (v : Nat) (a b : Sym) :
    (Sym.ite (.cmp .ult .W64 c (.lit v)) a b).eval env =
      if CmpOp.ult.apply .W64 (c.eval env) (BitVec.ofNat 64 v) then a.eval env else b.eval env := by
  simp only [Sym.eval, SBool.eval]
  exact if_congr Iff.rfl rfl rfl

section
variable [Labels] {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW} {m0 : MachineData}

/-- **The loop registers of a setup block**, read off table `t`'s entry. -/
theorem shapes_eval {m m' : MachineData} {fb e : BitVec 64} {S : SState} {R : Regs} {t c : Nat}
    (hm : Match (Env.ofMachine m [(fb, 64), (e, 11808)]) S m') (hev : TableEvalsAt m.dmem e ev)
    (ht : t < 6) (hc : c < 2 ^ 64) (hs : Shapes R t c S) :
    (m'.regs.getXReg R.a).toBitVec = e + BitVec.ofNat 64 (1968 * t + 496) ∧
    (m'.regs.getXReg R.n).toNat = 16 * (valsOf ev t).size ∧
    (m'.regs.getXReg R.p).toBitVec = e + BitVec.ofNat 64 (1968 * t + 8) ∧
    (m'.regs.getXReg R.l).toNat = (ptOf ev t).size ∧ (m'.regs.getXReg R.c).toNat = c := by
  obtain ⟨ha, hn, hp, hl, hcc⟩ := hs
  have hv := vals_le hev ht
  have hpl := pt_le hev ht
  have wv : (Sym.load 1 (1968 * t + 488) 8).eval (Env.ofMachine m [(fb, 64), (e, 11808)]) =
      ((valsOf ev t).size.toUInt64).toBitVec := by
    rw [Bus.load_r1, NativeRustcVm.wordOf_of_wordAt (count_at hev ht)]
  have wp : (Sym.load 1 (1968 * t) 8).eval (Env.ofMachine m [(fb, 64), (e, 11808)]) =
      ((ptOf ev t).size.toUInt64).toBitVec := by
    rw [Bus.load_r1, NativeRustcVm.wordOf_of_wordAt (ptCount_at hev ht)]
  have cv : CmpOp.ult.apply .W64 ((valsOf ev t).size.toUInt64).toBitVec (BitVec.ofNat 64 93) =
      true := by
    rw [cmp_ult_lit _ _ (by decide), toNat_toUInt64 (by omega)]
    simp only [decide_eq_true_eq]
    omega
  have cp : CmpOp.ult.apply .W64 ((ptOf ev t).size.toUInt64).toBitVec (BitVec.ofNat 64 31) =
      true := by
    rw [cmp_ult_lit _ _ (by decide), toNat_toUInt64 (by omega)]
    simp only [decide_eq_true_eq]
    omega
  have nv : ((valsOf ev t).size.toUInt64).toBitVec.toNat = (valsOf ev t).size :=
    toNat_toUInt64 (by omega)
  have np : ((ptOf ev t).size.toUInt64).toBitVec.toNat = (ptOf ev t).size :=
    toNat_toUInt64 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hm.regs _ _ ha, eval_ite_ult, wv, cv]
    simp only [eq_self, ite_true]
    show e + BitVec.ofInt 64 ((1968 * t + 496 : Nat) : Int) = _
    rw [BitVec.ofInt_natCast]
  · show (m'.regs.getXReg R.n).toBitVec.toNat = _
    rw [hm.regs _ _ hn]
    show (UnOp.apply (.ubfm 60 59) .W64 (Sym.eval _ (.ite _ _ _))).toNat = _
    rw [eval_ite_ult, wv, cv]
    simp only [eq_self, ite_true]
    rw [Arrays.lsl4, nv, BitVec.toNat_ofNat]
    omega
  · rw [hm.regs _ _ hp, eval_ite_ult, wp, cp]
    simp only [eq_self, ite_true]
    show e + BitVec.ofInt 64 ((1968 * t + 8 : Nat) : Int) = _
    rw [BitVec.ofInt_natCast]
  · show (m'.regs.getXReg R.l).toBitVec.toNat = _
    rw [hm.regs _ _ hl, eval_ite_ult, wp, cp]
    simp only [eq_self, ite_true]
    rw [np]
  · show (m'.regs.getXReg R.c).toBitVec.toNat = _
    rw [hm.regs _ _ hcc]
    show (BitVec.ofNat 64 c).toNat = c
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

end

section
variable [Host] {k : Nat} {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW}
  {m0 : MachineData}

/-- **The next table's setup**, after table `i`'s loop, to its head. -/
theorem next (hpre : TableColumnClaimsPre ev cs m0) {i : Nat} (hi : i < 5) {R R' : Regs}
    (S : SB k R' (i + 1)) {j' : Nat} (hj' : S.j + S.D.length = j') {Q : MachineState → Prop}
    (cont : ∀ m', LoopAt R' ev cs m0 (i + 1) 0 m' →
      Eventually (step1 Host.exe) Q ⟨m', Host.addrOf (k + j')⟩)
    {m : MachineData} (h : LoopAt R ev cs m0 i (valsOf ev i).size m) :
    Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + S.j)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hin, -, -, -, -⟩ := hpre'
  have hwf := Bus.wf_frame2 hS F_le h.fr.kept (a := m0.regs.X0.toBitVec) (n := 11808) hin.1
    hin.2.1
  have hm : Match (Env.ofMachine m [(base m0 64, 64), (m0.regs.X0.toBitVec, 11808)]) setS m := by
    have := Bus.match_frame2 (r := .X20) (n := 11808) hS F_le rfl h.fr.sp
    rwa [h.x20 hi] at this
  refine exec_then S.inD S.run hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hmem, hsp, hall, hsh⟩ := S.ok
  have hfr := Fr.ofBlock h.fr hm hm' hwf rfl hmem (by rw [hsp]; rfl) fun r hr ↦
    ⟨.reg r, reg_all (S := setS) (L := keep) (by decide) hr,
      reg_all hall (List.mem_cons_of_mem _ hr)⟩
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf hmem
  have hc66 : S.c < 2 ^ 64 := by have := S.hc; have := base_le (i + 1); omega
  obtain ⟨ea, en, ep, el, ec⟩ := shapes_eval hm' (evals_in hpre h.fr) (by omega) hc66 hsh
  simp only [PcOk] at hpc
  rw [Nat.add_assoc, hj'] at hpc
  refine Bus.Gkr.at_pc hpc (cont _ ⟨hfr, ?_, fun h5 ↦ ?_, ?_, ?_, ?_, ep, el, Nat.zero_le _, ?_⟩)
  · rw [Bus.Gkr.reg_of hm' (reg_all hall (by simp))]; exact h.x19
  · apply UInt64.toBitVec_inj.mp
    rw [hm'.regs .X20 _ (S.x20 h5)]
    show m0.regs.X0.toBitVec + BitVec.ofInt 64 0 = _
    simp
  · rw [ea]
  · rw [ec, S.hc]; rfl
  · rw [en]; rfl
  · rw [hd]
    have hl : (valsOf ev i).size = (claimsOf ev i).length := (length_claimsOf i).symm
    have := h.claims
    rwa [hl, pre_next] at this

/-- **The entry**: the prologue and table `0`'s setup (`b0`), to table `0`'s head. -/
theorem entry (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {Q : MachineState → Prop}
    (cont : ∀ m, LoopAt R04 ev cs m0 0 0 m →
      Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b1Offset)⟩) :
    Eventually (step1 Host.exe) Q ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b0Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hin, hev, hcR, hcO, hcs⟩ := hpre'
  have hN := hS.2.1
  have hwf := Bus.wf_frame2 hS F_le (m := m0) (fun _ h ↦ h) (a := m0.regs.X0.toBitVec)
    (n := 11808) hin.1 hin.2.1
  have hm : Match (Env.ofMachine m0 [(base m0 64, 64), (m0.regs.X0.toBitVec, 11808)]) entryS m0 :=
    match_ofMachine (sregions := [(64, true), (11808, false)])
      (regions := [(base m0 64, 64), (m0.regs.X0.toBitVec, 11808)])
      ⟨rfl, fun _ ↦ Bus.base_aligned hS F_le rfl, rfl, nofun, trivial⟩
      (Bus.env0_sp (F := 64) [(m0.regs.X0.toBitVec, 11808)])
      ⟨by show m0.regs.X0.toBitVec = m0.regs.X0.toBitVec + BitVec.ofInt 64 0; simp, trivial⟩
      trivial trivial trivial
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hm1' : Match (Env.ofMachine m0 [(base m0 64, 64), (m0.regs.X0.toBitVec, 11808)])
      (Bus.after b0 entryS) st.data := by
    rw [Bus.after_eq run_b0]; exact hm1
  obtain ⟨hsp0, hsl0, hmem0, hk0, h19, h20, hsh⟩ := ok_b0
  have hfrF : Fr m0 64 tableColumnClaimsStack slots keep (fun _ ↦ False) st.data :=
    Fr.ofPrologue hN F_le hm1' hwf hsp0 hsl0 slots_le hmem0 hk0
  have hfr := Bus.Fr.mono hfrF (outs' := outs m0) fun _ h ↦ h.elim
  obtain ⟨ea, en, ep, el, ec⟩ := shapes_eval hm1' hev (by decide) (by decide) hsh
  simp only [PcOk] at hpc
  rw [NativeRustcVmArm.Vm.TableColumnClaims.b0_length, NativeRustcVmArm.Vm.TableColumnClaims.b0Length] at hpc
  refine Bus.Gkr.at_pc hpc (cont _ ⟨hfr, ?_, fun _ ↦ ?_, ?_, ?_, ?_, ep, el, Nat.zero_le _, ?_⟩)
  · exact Bus.Gkr.reg_of hm1' h19
  · apply UInt64.toBitVec_inj.mp
    rw [hm1'.regs .X20 _ h20]
    show m0.regs.X0.toBitVec + BitVec.ofInt 64 0 = _
    simp
  · rw [ea]
  · rw [ec, bases_eq]; rfl
  · rw [en]; rfl
  · have he : cs ++ (pre ev 0 0).toArray = cs := by simp [pre]
    rw [he]
    exact ClaimsWAt.of_same hcs (same_fr hfrF hS hcR.2 hcO)

/-- **The epilogue keeping X0** (`b25`). -/
theorem exit25 (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {m : MachineData}
    (hfr : Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m)
    (h0 : m.regs.X0 = okWord (decide (cs.size + (tableColumnClaims ev).size ≤ claimCap)))
    (hc : cs.size + (tableColumnClaims ev).size ≤ claimCap →
      ClaimsWAt m.dmem m0.regs.X1.toBitVec (cs ++ tableColumnClaims ev)) :
    Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b25Offset)⟩ := by
  have hS := hpre.1
  have hwf := Bus.wf_frame hS F_le hfr.kept
  have hm := Bus.match_frame hS F_le rfl hfr.sp
  refine exec_then (b25_in_code.trans hp.1 (by simp [b25])) run_b25 hwf hm fun st hm' hpc ↦ ?_
  have hm'' : Match (Env.ofMachine m [(base m0 64, 64)]) (Bus.after b25 sF) st.data := by
    rw [Bus.after_eq run_b25]; exact hm'
  obtain ⟨hok, hmem, hx0⟩ := ok_b25
  obtain ⟨hret, hsv⟩ := hfr.exit hm'' hwf hok
  have hd : st.data.dmem = m.dmem := hm''.dmem_eq hwf hmem
  have e0 : st.data.regs.X0 = m.regs.X0 := Bus.Gkr.reg_of hm'' hx0
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], by rw [e0, h0], fun hf ↦ ?_, ?_, hsv⟩
  · rw [hd]; exact hc hf
  · show SameOutside m0.dmem st.data.dmem _
    rw [hd]
    exact NativeRustcVm.SameOutside.mono hfr.same fun q hq ↦ hq.elim .inr .inl

/-- **The epilogue with X0 one** (`b31`): all claims pushed. -/
theorem exit31 (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {m : MachineData}
    (hfr : Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m)
    (hc : ClaimsWAt m.dmem m0.regs.X1.toBitVec (cs ++ tableColumnClaims ev)) :
    Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b31Offset)⟩ := by
  have hS := hpre.1
  have hwf := Bus.wf_frame hS F_le hfr.kept
  have hm := Bus.match_frame hS F_le rfl hfr.sp
  refine exec_then (b31_in_code.trans hp.1 (by simp [b31])) run_b31 hwf hm fun st hm' hpc ↦ ?_
  have hm'' : Match (Env.ofMachine m [(base m0 64, 64)]) (Bus.after b31 sF) st.data := by
    rw [Bus.after_eq run_b31]; exact hm'
  obtain ⟨hok, hmem, hx0⟩ := ok_b31
  obtain ⟨hret, hsv⟩ := hfr.exit hm'' hwf hok
  have hd : st.data.dmem = m.dmem := hm''.dmem_eq hwf hmem
  have hfit : cs.size + (tableColumnClaims ev).size ≤ claimCap := by
    have := hc.len_le; simpa using this
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], ?_, fun _ ↦ by rw [hd]; exact hc, ?_,
    hsv⟩
  · rw [decide_eq_true hfit]
    exact UInt64.toBitVec_inj.mp (Bus.Gkr.reg_lit hm'' hx0)
  · show SameOutside m0.dmem st.data.dmem _
    rw [hd]
    exact NativeRustcVm.SameOutside.mono hfr.same fun q hq ↦ hq.elim .inr .inl

/-- **The failure** (`b24`): X0 zero, then the epilogue. -/
theorem fail24 (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {m : MachineData}
    (hfr : Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m)
    (hn : ¬cs.size + (tableColumnClaims ev).size ≤ claimCap) :
    Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b24Offset)⟩ := by
  obtain ⟨hmem, hsp, hk, hx0⟩ := ok_b24
  refine Bus.Gkr.Fr.runBlock hpre.1 F_le rfl hfr (b24_in_code.trans hp.1 (by simp [b24])) run_b24
    hmem hsp hk (by decide) fun st hfr' _ hm hpc ↦ ?_
  simp only [PcOk] at hpc
  rw [NativeRustcVmArm.Vm.TableColumnClaims.b24_length, NativeRustcVmArm.Vm.TableColumnClaims.b24Length] at hpc
  refine Bus.Gkr.at_pc hpc (exit25 hp hpre hfr' ?_ fun h ↦ absurd h hn)
  rw [decide_eq_false hn]
  exact UInt64.toBitVec_inj.mp (Bus.Gkr.reg_lit hm hx0)

/-- **A jump to the failure** (`b4`, `b9`, `b14`, `b19`). -/
theorem failJ (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {b : List Directive}
    {j : Nat} (hb : b.IsInfixAt Host.prog (k + j))
    (hx : exec b sF = some (Bus.after b sF, .jump NativeRustcVmArm.Vm.TableColumnClaims.label_15))
    (hok : JumpOk (Bus.after b sF)) {m : MachineData}
    (hfr : Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m)
    (hn : ¬cs.size + (tableColumnClaims ev).size ≤ claimCap) :
    Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + j)⟩ := by
  obtain ⟨hmem, hsp, hk⟩ := hok
  refine Bus.Gkr.Fr.runBlock hpre.1 F_le rfl hfr hb hx hmem hsp hk (by decide)
    fun st hfr' _ _ hpc ↦ ?_
  simp only [PcOk] at hpc
  rw [hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b24Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_15_at] at hpc
  exact Bus.Gkr.at_pc hpc (fail24 hp hpre hfr' hn)

/-- **The jump to the epilogue** after table `5`'s failed push (`b30`). -/
theorem fail30 (hp : Placed code k) (hpre : TableColumnClaimsPre ev cs m0) {m : MachineData}
    (hfr : Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m) (h0 : m.regs.X0 = 0)
    (hn : ¬cs.size + (tableColumnClaims ev).size ≤ claimCap) :
    Eventually (step1 Host.exe) (Goal ev cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableColumnClaims.b30Offset)⟩ := by
  obtain ⟨hmem, hsp, hk, hx0⟩ := ok_b30
  refine Bus.Gkr.Fr.runBlock hpre.1 F_le rfl hfr (b30_in_code.trans hp.1 (by simp [b30])) run_b30
    hmem hsp hk (by decide) fun st hfr' _ hm hpc ↦ ?_
  simp only [PcOk] at hpc
  rw [hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b25Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_16_at] at hpc
  refine Bus.Gkr.at_pc hpc (exit25 hp hpre hfr' ?_ fun h ↦ absurd h hn)
  rw [decide_eq_false hn]
  exact (Bus.Gkr.reg_of hm hx0).trans h0

end

end

end NativeRustcVmArm.Tables.ColumnClaims
