module

public import NativeRustcVmX64.Whir.BasisWEval.First

/-!
# `BasisW::eval`: a column claim, up to its weight's call (x86-64)

From `Mid i i` (`b11`): a column of `158` or more has no placement, `b11` jumps to `b10`; else
`b12` reads the placement entry, `b10` for none (`Mid i (i + 1)`); else `b13` reads the placement
and compares the next scale's address with the scales' end, `b14` takes the scale or `b15` `0`:
`A16` at `NativeRustcVmX64.Vm.BasisWEval.label_13` (`b16`) (`col_head`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVmX64.Vm.BasisWEval
open NativeRustcVm.Transcript (off off_add off_zero toNat_off OptEWAt)
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- **At `NativeRustcVmX64.Vm.BasisWEval.label_13`** (`b16`): column claim `i` has the placement `pl` (RSI, RDX), the scale
`j = |ws i|` in R14, R15, the next one's address in R13. -/
structure A16 (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (i : Nat)
    (pl : Placement) (d : MachineData) : Prop where
  base : Base m0 ba 24 d
  w56 : FW m0 d 56 (reg m0 .rsi)
  w104 : FW m0 d 104 (off ba.layout 120)
  w24 : FW m0 d 24 (dot b.scales (ws v (xpt m0) i)).c0.toBitVec
  w64 : FW m0 d 64 (dot b.scales (ws v (xpt m0) i)).c1.toBitVec
  rbp : reg d .rbp = sA ba ba.count
  r13 : reg d .r13 = sA ba (min ((ws v (xpt m0) i).size + 1) ba.count)
  r14 : reg d .r14 = (sAt b.scales (ws v (xpt m0) i).size).c0.toBitVec
  r15 : reg d .r15 = (sAt b.scales (ws v (xpt m0) i).size).c1.toBitVec
  rsi : reg d .rsi = pl.variableCount.toUInt64.toBitVec
  rdx : reg d .rdx = pl.index.toUInt64.toBitVec
  ilt : i < v.cs.size
  rbx : (reg d .rbx).toNat = 608 * (v.cs.size - i)
  r12 : reg d .r12 = off ba.claims (24 + 608 * i)
  hpl : (v.L.placements[v.cs[i].column]?).getD none = some pl
  pl_lt : pl.variableCount < 2 ^ 64 ∧ pl.index < 2 ^ 64

end

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

theorem In.claimIn (h : In m0 ba b v) {i : Nat} (hi : i < v.cs.size) :
    WhirIn m0 (cA ba i) 608 basisWEvalStack := by
  have hle := h.claims.len_le
  unfold claimCap at hle
  exact WhirIn.sub h.claimsIn (by unfold claimsBytes columnClaimBytes claimCap; omega)

theorem In.claimAt (h : In m0 ba b v) {o : Nat} {d : MachineData} (hf : Fb m0 o d) {i : Nat}
    (hi : i < v.cs.size) : ColumnClaimAt d.dmem (cA ba i) v.cs[i] :=
  (h.claimsAt hf).claims i hi

theorem In.placeIn (h : In m0 ba b v) {c : Nat} (hc : c < 158) :
    WhirIn m0 (pA ba c) 24 basisWEvalStack :=
  WhirIn.sub h.layoutIn (by unfold layoutBytes placementBytes columnCountW; omega)

theorem In.placeAt (h : In m0 ba b v) {o : Nat} {d : MachineData} (hf : Fb m0 o d) {c : Nat}
    (hc : c < 158) : PlacementWAt d.dmem (pA ba c) (v.L.placements[c]'(by
      rw [(h.layoutAt hf).placements_size]; exact hc)) :=
  (h.layoutAt hf).placements c _

theorem cA_16 (ba : BasisAddrs) (i : Nat) :
    off ba.claims (24 + 608 * i) = cA ba i + BitVec.ofInt 64 16 := by
  rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, cA, off_add,
    show 8 + 608 * i + 16 = 24 + 608 * i by omega]

theorem mem_sub {l1 l2 : List Reg64} (h : l1.all (fun x ↦ l2.any (· == x)) = true)
    {r : Reg64} (hr : r ∈ l1) : r ∈ l2 := by
  rw [List.all_eq_true] at h
  obtain ⟨y, hy, he⟩ := List.any_eq_true.mp (h r hr)
  rw [← Reg64.eq_of_beq he]
  exact hy

theorem getD_lt {L : LayoutW} {c : Nat} (hc : c < L.placements.size) :
    (L.placements[c]?).getD none = L.placements[c] := by
  rw [Array.getElem?_eq_getElem hc, Option.getD_some]

theorem getD_ge {L : LayoutW} {c : Nat} (hc : L.placements.size ≤ c) :
    (L.placements[c]?).getD none = none := by
  rw [Array.getElem?_eq_none hc]; rfl

/-- `Mid` in a state with the same memory and registers. -/
theorem Mid.keep {i j : Nat} {d d' : MachineData} (hm : Mid m0 ba b v i j d) (hf : Fb m0 24 d')
    (hdm : d'.dmem = d.dmem)
    (hr : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .rcx], reg d' r = reg d r) :
    Mid m0 ba b v i j d' where
  base := ⟨hf, by unfold FW; rw [hdm]; exact hm.base.w32, by unfold FW; rw [hdm]; exact hm.base.w40,
    by unfold FW; rw [hdm]; exact hm.base.w48, by unfold FW; rw [hdm]; exact hm.base.w72⟩
  w56 := by unfold FW; rw [hdm]; exact hm.w56
  w104 := by unfold FW; rw [hdm]; exact hm.w104
  acc := ⟨by unfold FW; rw [hdm]; exact hm.acc.w24, by unfold FW; rw [hdm]; exact hm.acc.w64,
    (hr .r13 (by simp)).trans hm.acc.r13, (hr .rbp (by simp)).trans hm.acc.rbp⟩
  ilt := hm.ilt
  rbx := by rw [hr .rbx (by simp)]; exact hm.rbx
  r12 := (hr .r12 (by simp)).trans hm.r12
  rcx := (hr .rcx (by simp)).trans hm.rcx

/-- Claim `i` without a placement: its weights are those before it. -/
theorem Mid.skip {i : Nat} {d : MachineData} (hm : Mid m0 ba b v i i d)
    (hn : (v.L.placements[v.cs[i]'hm.ilt |>.column]?).getD none = none) :
    Mid m0 ba b v i (i + 1) d := by
  have hw : ws v (xpt m0) (i + 1) = ws v (xpt m0) i := by
    rw [ws_succ _ _ hm.ilt, hn]
  exact ⟨hm.base, hm.w56, hm.w104, hw ▸ hm.acc, hm.ilt, hm.rbx, hm.r12, hm.rcx⟩

/-- `A16` from `Mid i i` and the registers the blocks set. -/
theorem A16.of {i : Nat} {pl : Placement} {d d' : MachineData} (hm : Mid m0 ba b v i i d)
    (hf : Fb m0 24 d') (hdm : d'.dmem = d.dmem)
    (hr : ∀ r ∈ [Reg64.rbx, .rbp, .r12], reg d' r = reg d r)
    (hsi : reg d' .rsi = pl.variableCount.toUInt64.toBitVec)
    (hdx : reg d' .rdx = pl.index.toUInt64.toBitVec)
    (h13 : reg d' .r13 = sA ba (min ((ws v (xpt m0) i).size + 1) ba.count))
    (h14 : reg d' .r14 = (sAt b.scales (ws v (xpt m0) i).size).c0.toBitVec)
    (h15 : reg d' .r15 = (sAt b.scales (ws v (xpt m0) i).size).c1.toBitVec)
    (hpl : (v.L.placements[v.cs[i]'hm.ilt |>.column]?).getD none = some pl)
    (hlt : pl.variableCount < 2 ^ 64 ∧ pl.index < 2 ^ 64) : A16 m0 ba b v i pl d' where
  base := ⟨hf, by unfold FW; rw [hdm]; exact hm.base.w32, by unfold FW; rw [hdm]; exact hm.base.w40,
    by unfold FW; rw [hdm]; exact hm.base.w48, by unfold FW; rw [hdm]; exact hm.base.w72⟩
  w56 := by unfold FW; rw [hdm]; exact hm.w56
  w104 := by unfold FW; rw [hdm]; exact hm.w104
  w24 := by unfold FW; rw [hdm]; exact hm.acc.w24
  w64 := by unfold FW; rw [hdm]; exact hm.acc.w64
  rbp := (hr .rbp (by simp)).trans hm.acc.rbp
  r13 := h13
  r14 := h14
  r15 := h15
  rsi := hsi
  rdx := hdx
  ilt := hm.ilt
  rbx := by rw [hr .rbx (by simp)]; exact hm.rbx
  r12 := (hr .r12 (by simp)).trans hm.r12
  hpl := hpl
  pl_lt := hlt

variable [Host] {k : Nat}

/-- **Column claim `i` up to its weight's call**, from `b11` to `b10` (no placement) or `b16`. -/
theorem col_head (hp : Placed code k) (h : In m0 ba b v) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b11Offset)) (hm : Mid m0 ba b v i i st.data)
    {R : MachineState → Prop}
    (hskip : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b10Offset) →
      Mid m0 ba b v i (i + 1) st'.data → Eventually (step1 Host.exe) R st')
    (hcol : ∀ st' : MachineState, ∀ pl, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b16Offset) →
      A16 m0 ba b v i pl st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hf := hm.base.fr
  have hi := hm.ilt
  have hcl := h.claimAt hf hi
  have hcin := h.claimIn hi
  -- b11
  have hwf := h.wf1 (ret := 0) hf.frame.kept hcin
  have hm0 : Match (envB m0 st.data [(cA ba i, 608)] 0) colS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hf.frame.rsp_eval, hm.r12.trans (cA_16 ba i), trivial⟩ trivial trivial trivial
  have l0 : (envB m0 st.data [(cA ba i, 608)] 0).load 1 0 8 = v.cs[i].column.toUInt64.toBitVec :=
    load_ofMachine (r := 1) (o := 0) rfl (by rw [off_zero]; exact hcl.column)
  obtain ⟨hmid, hmem, hrax, hr12, hk⟩ := ok_b11
  refine at_pc hpc (h.block hf hwf (inf hp b11_in_code (by simp [b11])) exit_b11 nofun hm0 hmid
    (h0_of_nil hmem) fun st1 hm1 hpc1 hf1 ↦ ?_)
  have hm1' : Mid m0 ba b v i i st1.data := hm.keep hf1 (hm1.dmem_eq hwf hmem) fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact keeps_reg hm1 hk (by simp)
    · exact keeps_reg hm1 hk (by simp)
    · exact (reg_eval hm1 hr12).trans ((hm0.regs .r12 _ rfl).symm)
    · exact keeps_reg hm1 hk (by simp)
    · exact keeps_reg hm1 hk (by simp)
  have hclt := hcl.column_lt
  simp only [PcOk, c11_eval l0 hclt] at hpc1
  have hpls := (h.layoutAt hf).placements_size
  by_cases hc : v.cs[i].column < 158
  · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    rw [show k + NativeRustcVmX64.Vm.BasisWEval.b11Offset + b11.length = k + NativeRustcVmX64.Vm.BasisWEval.b12Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b11_next]] at hpc1
    have hc' : v.cs[i].column < v.L.placements.size := by rw [hpls]; exact hc
    have e1 : reg st1.data .rax = v.cs[i].column.toUInt64.toBitVec := (reg_eval hm1 hrax).trans l0
    -- b12
    have hpin := h.placeIn hc
    have hpat := h.placeAt hf1 hc
    have hwf2 := h.wf1 (ret := 0) hf1.frame.kept hpin
    have hm2 : Match (envB m0 st1.data [(pA ba v.cs[i].column, 24)] 0) placeS st1.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf1.frame.rsp_eval, trivial⟩ trivial trivial
        ⟨(placeSym_eval hm1'.rcx e1 hc).trans (eval_ptr (i := 1) rfl).symm, trivial⟩
    obtain ⟨hmid2, hmem2, hrax2, hk2⟩ := ok_b12
    refine at_pc hpc1 (h.block hf1 hwf2 (inf hp b12_in_code (by simp [b12])) exit_b12 nofun hm2
      hmid2 (h0_of_nil hmem2) fun st2 hm3 hpc2 hf2 ↦ ?_)
    have hm2' : Mid m0 ba b v i i st2.data := hm1'.keep hf2 (hm3.dmem_eq hwf2 hmem2)
      fun r hr ↦ keeps_reg hm3 hk2 (mem_sub (by decide) hr)
    simp only [PcOk] at hpc2
    cases hpl : v.L.placements[v.cs[i].column] with
    | none =>
      rw [hpl] at hpat
      have l2 : (envB m0 st1.data [(pA ba v.cs[i].column, 24)] 0).load 1 0 8 = (0 : UInt64).toBitVec :=
        load_ofMachine (r := 1) (o := 0) rfl (by rw [off_zero]; exact hpat)
      simp only [c12_eval l2, show ((0 : UInt64).toBitVec).toNat = 0 from rfl, decide_true,
        ↓reduceIte] at hpc2
      rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_15_at] at hpc2
      exact hskip st2 hpc2 (hm2'.skip (by rw [getD_lt hc', hpl]))
    | some pl =>
      rw [hpl] at hpat
      obtain ⟨hp1, hvc, hix, hw8, hw16⟩ := hpat
      have l2 : (envB m0 st1.data [(pA ba v.cs[i].column, 24)] 0).load 1 0 8 = (1 : UInt64).toBitVec :=
        load_ofMachine (r := 1) (o := 0) rfl (by rw [off_zero]; exact hp1)
      simp only [c12_eval l2, show ((1 : UInt64).toBitVec).toNat = 1 from rfl,
        show decide ((1 : Nat) = 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hpc2
      rw [show k + NativeRustcVmX64.Vm.BasisWEval.b12Offset + b12.length = k + NativeRustcVmX64.Vm.BasisWEval.b13Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b12_next]] at hpc2
      -- b13
      have e2 : (reg st2.data .rax).toNat = 3 * v.cs[i].column := by
        rw [reg_eval hm3 hrax2]
        exact col3_eval (show (envB m0 st1.data [(pA ba v.cs[i].column, 24)] 0).regs .rax = _
          from e1) hc
      have hwf3 := h.wf1 (ret := 0) hf2.frame.kept hpin
      have hm4 : Match (envB m0 st2.data [(pA ba v.cs[i].column, 24)] 0) pentS st2.data :=
        match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.frame.rsp_eval, trivial⟩ trivial trivial
          ⟨(pentSym_eval hm2'.rcx e2).trans (eval_ptr (i := 1) rfl).symm, trivial⟩
      have hpat2 := h.placeAt hf2 hc
      rw [hpl] at hpat2
      obtain ⟨-, -, -, hw8', hw16'⟩ := hpat2
      obtain ⟨hmid4, hmem4, hrsi4, hrdx4, hk4⟩ := ok_b13
      refine at_pc hpc2 (h.block hf2 hwf3 (inf hp b13_in_code (by simp [b13])) exit_b13 nofun
        hm4 hmid4 (h0_of_nil hmem4) fun st3 hm5 hpc3 hf3 ↦ ?_)
      have hd3 : st3.data.dmem = st2.data.dmem := hm5.dmem_eq hwf3 hmem4
      have k3 : ∀ r ∈ [Reg64.rbx, .rbp, .r12], reg st3.data r = reg st2.data r :=
        fun r hr ↦ keeps_reg hm5 hk4 (mem_sub (by decide) hr)
      have esi : reg st3.data .rsi = pl.variableCount.toUInt64.toBitVec :=
        (reg_eval hm5 hrsi4).trans (load_ofMachine (r := 1) (o := 8) rfl hw8')
      have edx : reg st3.data .rdx = pl.index.toUInt64.toBitVec :=
        (reg_eval hm5 hrdx4).trans (load_ofMachine (r := 1) (o := 16) rfl hw16')
      have hgd : (v.L.placements[v.cs[i].column]?).getD none = some pl := by
        rw [getD_lt hc', hpl]
      have hsz := h.pre.2.1.scales_size
      simp only [PcOk, cScale_eval (env := envB m0 st2.data [(pA ba v.cs[i].column, 24)] 0)
        (j := (ws v (xpt m0) i).size) hm2'.acc.r13 hm2'.acc.rbp
        h.scales.1.2 h.scalesPos] at hpc3
      by_cases hj : ba.count ≤ (ws v (xpt m0) i).size
      · -- b15: no scale left
        simp only [hj, decide_true, ↓reduceIte] at hpc3
        rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_9_at] at hpc3
        obtain ⟨hmid6, hmem6, hr13, hr14, hr15, hk6⟩ := ok_b15
        have hwf6 := h.wf0 hf3 (ret := 0)
        refine at_pc hpc3 (h.block hf3 hwf6 (inf hp b15_in_code (by simp [b15])) exit_b15 nofun
          (match_body hf3 ⟨rfl, trivial⟩) hmid6 (h0_of_nil hmem6) fun st4 hm6 hpc4 hf4 ↦ ?_)
        simp only [PcOk] at hpc4
        have hs0 : sAt b.scales (ws v (xpt m0) i).size = 0 := sAt_ge (by omega)
        refine hcol st4 pl hpc4 (A16.of hm2' hf4 ((hm6.dmem_eq hwf6 hmem6).trans hd3)
          (fun r hr ↦ (keeps_reg hm6 hk6 (mem_sub (by decide) hr)).trans (k3 r hr))
          ((keeps_reg hm6 hk6 (by simp)).trans esi) ((keeps_reg hm6 hk6 (by simp)).trans edx)
          ?_ ?_ ?_ hgd ⟨hvc, hix⟩)
        · rw [reg_eval hm6 hr13, Nat.min_eq_right (by omega)]
          exact (k3 .rbp (by simp)).trans hm2'.acc.rbp
        · rw [reg_eval hm6 hr14, hs0]; rfl
        · rw [reg_eval hm6 hr15, hs0]; rfl
      · -- b14: the scale
        simp only [hj, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
        rw [show k + NativeRustcVmX64.Vm.BasisWEval.b13Offset + b13.length = k + NativeRustcVmX64.Vm.BasisWEval.b14Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.BasisWEval.b13_next]] at hpc3
        have hlt : (ws v (xpt m0) i).size < ba.count := by omega
        obtain ⟨hmid6, hmem6, hr13, hr14, hr15, hk6⟩ := ok_b14
        have hwf6 := h.wf1 (ret := 0) hf3.frame.kept (h.scaleIn hlt)
        have e13 : reg st3.data .r13 = sA ba (ws v (xpt m0) i).size := by
          rw [keeps_reg hm5 hk4 (by simp), hm2'.acc.r13, Nat.min_eq_left (by omega)]
        have hm6' : Match (envB m0 st3.data [(sA ba (ws v (xpt m0) i).size, 16)] 0) (scaleS .r13)
            st3.data :=
          match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf3.frame.rsp_eval, known_ptr rfl e13, trivial⟩
            trivial trivial trivial
        have ⟨s0, s1⟩ := h.scaleAt hf3 hlt
        refine at_pc hpc3 (h.block hf3 hwf6 (inf hp b14_in_code (by simp [b14])) exit_b14 nofun
          hm6' hmid6 (h0_of_nil hmem6) fun st4 hm6 hpc4 hf4 ↦ ?_)
        simp only [PcOk] at hpc4
        rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_13_at] at hpc4
        refine hcol st4 pl hpc4 (A16.of hm2' hf4 ((hm6.dmem_eq hwf6 hmem6).trans hd3)
          (fun r hr ↦ (keeps_reg hm6 hk6 (mem_sub (by decide) hr)).trans (k3 r hr))
          ((keeps_reg hm6 hk6 (by simp)).trans esi) ((keeps_reg hm6 hk6 (by simp)).trans edx)
          ?_ ((reg_eval hm6 hr14).trans (load_ofMachine (r := 1) (o := 0) rfl s0))
          ((reg_eval hm6 hr15).trans (load_ofMachine (r := 1) (o := 8) rfl s1)) hgd ⟨hvc, hix⟩)
        rw [reg_eval hm6 hr13, Nat.min_eq_left (by omega), ← sA_succ]
        rfl
  · simp only [hc, decide_false, Bool.not_false, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.BasisWEval.label_15_at] at hpc1
    exact hskip st1 hpc1 (hm1'.skip (getD_ge (by rw [hpls]; unfold columnCountW; omega)))

end

end NativeRustcVmX64.Whir.BasisWEval
