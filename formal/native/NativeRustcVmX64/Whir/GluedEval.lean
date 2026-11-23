module

public import NativeRustcVmX64.Whir.GluedEval.Exec
public import NativeRustcVmX64.Whir.SubspaceAtTable.Leaf
public import NativeRustcVmX64.Code.Vm.EqEval.Names
public import NativeRustcVmX64.Code.Vm.GluedEval.Names
public import NativeRustcVmX64.Code.Vm.InducedWeight.Names

/-!
# `glued_eval` on x86-64

**`gluedEval_spec`**: `b0` pushes RBX and reads the glued claim's `kind`. Kind `1`
(`induced μ queries weights`): `b1` passes `μ`, the queries' and the weights' slices (their
buffers' counts, below `231`) and pushes the point's slice as `induced_weight`'s two stack
arguments; after the call `b2` drops them, pops RBX and returns `induced_weight`'s output. Kind
`0` (`eq z`): `b3` calls `eq_eval` on `z` (its buffer's count, below `31`) and the point; `b4a`
stores `Some` of the result, `b4b` pops RBX and returns.
-/

namespace NativeRustcVmX64.Whir.GluedEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GluedEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region wordOf)
open NativeRustcVm.Transcript (off OptEWAt)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq wordAt_of_write ewAt_of_writes eval_reg
  eval_lit eval_load eval_cmp_eq not_inRange_of_apart apart_symm wf_two written_region0
  not_inRange_zero)

public section

theorem stack_le : 16 + eqEvalStack ≤ gluedEvalStack ∧ 32 + inducedWeightStack ≤ gluedEvalStack ∧
    32 ≤ gluedEvalStack := by
  decide

/-- A count below its cap, as `cmp` compares it. -/
theorem count_lt {c : UInt64} {N B : Nat} (h : c.toNat ≤ N) (hB : N < B) (hB' : B < 2 ^ 64) :
    c.toBitVec.ult (BitVec.ofNat 64 B) = true := by
  rw [ult_ofNat hB']
  simp only [UInt64.toNat_toBitVec, decide_eq_true_eq]
  omega

theorem toNat_len {n : Nat} (h : n ≤ 230) : n.toUInt64.toNat = n := toNat_toUInt64 (by omega)

/-- `b` below the entry's RSP plus `c` is `b - c` below it. -/
theorem sb_add {m : MachineData} {a b : Nat} (_h : a + b ≤ (rspOf m).toNat) :
    stackBelow m (a + b) + BitVec.ofNat 64 b = stackBelow m a := by
  apply BitVec.eq_of_toNat_eq
  unfold stackBelow
  have := (rspOf m).isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem eight (x : BitVec 64) : x + 8#64 = x + BitVec.ofNat 64 8 := rfl

/-- Bytes kept where a state's bytes are another's. -/
theorem bytesAt_eq {d d' : DataMem} {a : BitVec 64} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt d a bs)
    (he : ∀ j < bs.length, d'.get? (a + BitVec.ofNat 64 j) = d.get? (a + BitVec.ofNat 64 j)) :
    NativeRustcVm.BytesAt d' a bs := fun j hj ↦ by rw [he j hj]; exact h j hj

variable [Host] {k : Nat}

/-- `glued_eval`'s postcondition, reached. -/
abbrev Post (g : GluedClaimW) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ GluedEvalPost g m0 s.data

/-- **The `eq` branch.** -/
theorem eq_branch (hp : Placed code k)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost)
    {g : GluedClaimW} {m0 : MachineData} (hpre : GluedEvalPre g m0) {z : Array EW}
    (hgw : g.weight = .eq z) :
    Eventually (step1 Host.exe) (Post g m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b0Offset)⟩ := by
  obtain ⟨hS, ⟨-, -, -, hw⟩, hgin, hx, hout, _⟩ := hpre
  rw [hgw] at hw
  obtain ⟨hkind, hzlen, hzw, hzs⟩ := hw
  obtain ⟨hsle1, -, hF⟩ := stack_le
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hz30 : z.toList.length ≤ 30 := hzlen
  have hgb : gluedBytes = 6064 := rfl
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GluedEval.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GluedEval.b3Offset) := b3_in_code.trans hp.1 (by simp [b3])
  have hk4 : b4a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GluedEval.b4Offset) ∧ b4b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GluedEval.b4Offset + b4a.length) := by
    have h := b4_in_code.trans hp.1 (by simp [b4])
    rw [← List.take_append_drop 3 b4] at h
    exact h.append
  have hap1 : Apart (stackBelow m0 32) (32 + 8) (reg m0 .rsi) 6064 :=
    apart_symm (apart_frame' hS hF hgin.2)
  have hwf : (Env.ofMachine m0 [(stackBelow m0 32, 32 + 8), (reg m0 .rsi, 6064)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b4Offset)).toBitVec).WF :=
    wf_two (stackOk_mono hS hF) (fun _ h ↦ h) hgin.1 hap1
  have hm : Match (Env.ofMachine m0 [(stackBelow m0 32, 32 + 8), (reg m0 .rsi, 6064)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b4Offset)).toBitVec) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨show rspOf m0 = stackBelow m0 32 + BitVec.ofInt 64 32 by
          rw [show BitVec.ofInt 64 32 = BitVec.ofNat 64 (32 + 0) from rfl,
            NativeRustcVmX64.Field.frame_add]
          simp,
        show reg m0 .rsi = reg m0 .rsi + BitVec.ofInt 64 0 by
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
      trivial trivial trivial
  have hload : ∀ {o : Nat} {w : UInt64}, NativeRustcVm.WordAt m0.dmem (off (reg m0 .rsi) o) w →
      (Env.ofMachine m0 [(stackBelow m0 32, 32 + 8), (reg m0 .rsi, 6064)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b4Offset)).toBitVec).load 1 o 8 = w.toBitVec := fun h ↦ by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt h)
  refine exec_then hk0 run_b0 hwf (by intro l h; cases h) hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [eval_cmp_eq, eval_load, eval_lit, hload hkind,
    show ((0 : UInt64).toBitVec == BitVec.ofNat 64 0) = true from rfl] at hpc1
  simp only [↓reduceIte] at hpc1
  rw [show Labels.label NativeRustcVmX64.Vm.GluedEval.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b3Offset) from hp.label NativeRustcVmX64.Vm.GluedEval.label_1_at]
    at hpc1
  refine exec_at hk3 (exec_after run_b0 run_b3) hwf (fun _ _ ↦ rfl) hpc1 hm1
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hw3, hslot3, hoth3, hrdx3, hrcx3, hrbx3, hsp3⟩ := after_eq run_b3 ▸ b3_facts
  have hw3' := fun w h ↦ (⟨(hw3 w h).1, by have := (hw3 w h).2; omega⟩ :
    w.r = 0 ∧ w.off + w.n ≤ 32 + 8)
  have hkept2 : Kept m0.dmem st2.data.dmem := hm2.kept hwf
  have harg := fun {a : BitVec 64} {n : Nat} (ho : OffStack m0 a n gluedEvalStack)
    (hna : NoWrap a n) ↦ get?_of_frame hm2 hwf rfl hw3' hS hF ho hna
  have hrsp2 : rspOf st2.data = stackBelow m0 16 := by
    show st2.data.regs.get64 .rsp = _
    rw [hm2.regs .rsp _ hsp3]
    show stackBelow m0 32 + BitVec.ofInt 64 16 = _
    rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl]
    exact sb_add (a := 16) (b := 16) (by omega)
  have hzl := hload hzw
  have hcnt : (z.toList.length.toUInt64).toBitVec.ult (BitVec.ofNat 64 31) = true :=
    count_lt (N := 30) (by rw [toNat_len (by omega)]; exact hz30) (by decide) (by decide)
  have hx0 : reg st2.data .rdi = reg m0 .rsi + BitVec.ofNat 64 48 := by
    refine (hm2.regs .rdi _ rfl).trans ?_
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hzl, hcnt]
    rfl
  have hx1 : reg st2.data .rsi = (z.toList.length.toUInt64).toBitVec := by
    refine (hm2.regs .rsi _ rfl).trans ?_
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hzl, hcnt]
    rfl
  have hx2 : reg st2.data .rdx = reg m0 .rdx := hm2.regs .rdx _ hrdx3
  have hx3 : reg st2.data .rcx = reg m0 .rcx := hm2.regs .rcx _ hrcx3
  have hn1 : (z.toList.length.toUInt64).toBitVec.toNat = z.toList.length := by
    rw [UInt64.toNat_toBitVec, toNat_len (by omega)]
  have hpre2 : EqEvalPre st2.data := by
    refine ⟨stackOk_callee hS hkept2 hrsp2 hsle1, ?_, ?_⟩
    · rw [hx0, hx1]
      exact sliceOk_callee (WhirIn.sliceOk hgin (by rw [hn1]; omega)) hS hkept2 hrsp2 hsle1
    · rw [hx2, hx3]
      exact sliceOk_callee hx hS hkept2 hrsp2 hsle1
  refine call_then hpc2 heq hpre2 fun st3 hpc3 hrsp3 ⟨hval, hch, hsv⟩ ↦ ?_
  -- the values
  have hz : slice st2.data (reg st2.data .rdi) (reg st2.data .rsi) = z := by
    rw [hx0, hx1, slice, hn1, NativeRustcVm.ewsOf_congr (d := m0.dmem) fun i hi ↦ ?_]
    · rw [eight, addr_add] at hzs
      rw [NativeRustcVm.ewsOf_of_ewsAt hzs, Array.toArray_toList]
    · rw [addr_add]
      exact harg hgin.2 hgin.1.2 _ (by omega)
  have hpt : slice st2.data (reg st2.data .rdx) (reg st2.data .rcx) =
      slice m0 (reg m0 .rdx) (reg m0 .rcx) := by
    rw [hx2, hx3, slice, slice, NativeRustcVm.ewsOf_congr fun i hi ↦ harg hx.2 hx.1.2 i hi]
    rfl
  rw [hz, hpt] at hval
  -- a body of the 16 bytes below RSP
  have hfr3 : Frame m0 16 gluedEvalStack slots16 [⟨reg m0 .rdi, 24⟩] st3.data := by
    refine ⟨?_, fun q hq ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_, fun p h ↦ hsv.2 p (hkept2 p h)⟩
    · rw [hrsp3, hrsp2]; rfl
    · simp only [slots16, List.mem_singleton] at hq
      subst hq
      have h := hm2.bytesAt_write (r := 0) (sz := 32 + 8) rfl (by omega) hslot3
      rw [show stackBelow m0 32 + BitVec.ofNat 64 24 = stackBelow m0 16 + BitVec.ofNat 64 8 by
        rw [← sb_add (m := m0) (a := 16) (b := 16) (by omega), addr_add]] at h
      refine bytesAt_eq h fun j hj ↦ hch _ fun h' ↦ h'.elim (not_inRange_zero _) ?_
      simp only [List.length_map, List.length_range] at hj
      rw [addr_add]
      exact not_inRange_callee hS hrsp2 hsle1 (by omega)
    · exact (hsv.1 r hr).trans (hm2.regs r _ (hoth3 r (others_spec16 r hr hn)))
    · rw [hch p fun h ↦ h.elim (not_inRange_zero _)
        fun h ↦ hp (.inr (inRange_callee hS hrsp2 hsle1 h))]
      exact hm2.get?_mem0 hwf fun h ↦ hp (.inr (inRange_frame hS hF le_rfl
        (written_region0 rfl hwf (k := 32) (by omega) hw3 h)))
  -- `b4a`: `Some`
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b4Offset) := hpc3
  have hrd : Readable st3.data (reg m0 .rdi) 24 := Readable.keep hout.1 hfr3.kept
  have hwf4 : (Env.ofMachine st3.data [(reg m0 .rdi, 24)]).WF :=
    Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm4 : Match (Env.ofMachine st3.data [(reg m0 .rdi, 24)]) stS st3.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show reg st3.data .rbx = reg m0 .rdi + BitVec.ofInt 64 0 by
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
          exact (hsv.1 .rbx rfl).trans (hm2.regs .rbx _ hrbx3), trivial⟩
      trivial trivial trivial
  refine exec_at hk4.1 run_b4a hwf4 (by intro l h; cases h) hpc3' hm4 fun st4 hm5 hpc4 ↦ ?_
  obtain ⟨hk5, hw5, h0, h8, h16⟩ := after_eq run_b4a ▸ b4a_facts
  have hfr4 := hfr3.of_write hm4 hm5 hwf4 rfl hk5 (r := 0) rfl le_rfl hw5
    (fun p h ↦ .inl (inAny_one h)) fun q hq i hi ↦ by
      simp only [slots16, List.mem_singleton] at hq
      subst hq
      rw [addr_add]
      exact not_inRange_of_apart (apart_symm (apart_frame' hS (by omega) hout.2))
        (frame_ok hS (F := 16) (by omega)).2.1 hout.1.2 (by omega)
  have hopt : OptEWAt st4.data.dmem (reg m0 .rdi)
      (some (g.weight.eval (slice m0 (reg m0 .rdx) (reg m0 .rcx)))) := by
    refine ⟨?_, ?_⟩
    · have := wordAt_of_write hm5 (r := 0) (o := 0) rfl (by decide) (v := .lit 1) h0
      rwa [NativeRustcVm.addr_add_zero] at this
    · have := ewAt_of_writes hm5 (r := 0) (o := 8) rfl (by decide) h8 h16
      rw [hgw]
      show NativeRustcVm.EWAt _ _ (eqEval _ _)
      rw [← hval]
      exact this
  -- `b4b`: the epilogue
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b4Offset + b4a.length) := hpc4
  have hwf6 := hfr4.wf (vars := fun _ ↦ 0) (ret := 0) hS (by omega)
  refine exec_at hk4.2 run_b4b hwf6 (by intro l h; cases h) hpc4' hfr4.mid_match
    fun st5 hm6 hpc5 ↦ .done _ ?_
  obtain ⟨hpc', hrsp', hdm, hsaved⟩ := hfr4.done hS (by omega) (out_one hout) hm6 hpc5
    (after_eq run_b4b ▸ b4b_restores).1 (after_eq run_b4b ▸ b4b_restores).2
  exact ⟨hpc', hrsp', hdm ▸ hopt, fun p hp ↦ by rw [hdm]; exact hfr4.same p hp, hsaved⟩

/-- **The `induced` branch.** -/
theorem induced_branch (hp : Placed code k)
    (hind : Spec (Labels.label NativeRustcVmX64.Vm.InducedWeight.entryLabel) InducedWeightPre InducedWeightPost)
    {g : GluedClaimW} {m0 : MachineData} (hpre : GluedEvalPre g m0) {mu : Nat}
    {queries : Array UInt64} {weights : Array EW} (hgw : g.weight = .induced mu queries weights) :
    Eventually (step1 Host.exe) (Post g m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b0Offset)⟩ := by
  obtain ⟨hS, ⟨-, -, -, hw⟩, hgin, hx, hout, hgot⟩ := hpre
  rw [hgw] at hw
  obtain ⟨hkind, hmu, hmuw, ⟨hql, hqw, hqs⟩, ⟨hwl, hww, hws⟩⟩ := hw
  obtain ⟨-, hsle2, hF⟩ := stack_le
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hq230 : queries.toList.length ≤ 230 := hql
  have hw230 : weights.toList.length ≤ 230 := hwl
  have hmu30 : mu ≤ 30 := hmu
  have hgb : gluedBytes = 6064 := rfl
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GluedEval.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GluedEval.b1Offset) := b1_in_code.trans hp.1 (by simp [b1])
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GluedEval.b2Offset) := b2_in_code.trans hp.1 (by simp [b2])
  have hap1 : Apart (stackBelow m0 32) (32 + 8) (reg m0 .rsi) 6064 :=
    apart_symm (apart_frame' hS hF hgin.2)
  have hwf : (Env.ofMachine m0 [(stackBelow m0 32, 32 + 8), (reg m0 .rsi, 6064)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b2Offset)).toBitVec).WF :=
    wf_two (stackOk_mono hS hF) (fun _ h ↦ h) hgin.1 hap1
  have hm : Match (Env.ofMachine m0 [(stackBelow m0 32, 32 + 8), (reg m0 .rsi, 6064)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b2Offset)).toBitVec) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨show rspOf m0 = stackBelow m0 32 + BitVec.ofInt 64 32 by
          rw [show BitVec.ofInt 64 32 = BitVec.ofNat 64 (32 + 0) from rfl,
            NativeRustcVmX64.Field.frame_add]
          simp,
        show reg m0 .rsi = reg m0 .rsi + BitVec.ofInt 64 0 by
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
      trivial trivial trivial
  have hload : ∀ {o : Nat} {w : UInt64}, NativeRustcVm.WordAt m0.dmem (off (reg m0 .rsi) o) w →
      (Env.ofMachine m0 [(stackBelow m0 32, 32 + 8), (reg m0 .rsi, 6064)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b2Offset)).toBitVec).load 1 o 8 = w.toBitVec := fun h ↦ by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt h)
  refine exec_then hk0 run_b0 hwf (by intro l h; cases h) hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [eval_cmp_eq, eval_load, eval_lit, hload hkind,
    show ((1 : UInt64).toBitVec == BitVec.ofNat 64 0) = false from rfl] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte, NativeRustcVmX64.Vm.GluedEval.b0_length] at hpc1
  refine exec_at hk1 (exec_after run_b0 run_b1) hwf (fun _ _ ↦ rfl) hpc1 hm1
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hw1, hslot1, harg0, harg1, hoth1, hrdi1, hsp1⟩ := after_eq run_b1 ▸ b1_facts
  have hw1' := fun w h ↦ (⟨(hw1 w h).1, by have := (hw1 w h).2; omega⟩ :
    w.r = 0 ∧ w.off + w.n ≤ 32 + 8)
  have hkept2 : Kept m0.dmem st2.data.dmem := hm2.kept hwf
  have harg := fun {a : BitVec 64} {n : Nat} (ho : OffStack m0 a n gluedEvalStack)
    (hna : NoWrap a n) ↦ get?_of_frame hm2 hwf rfl hw1' hS hF ho hna
  have hrsp2 : rspOf st2.data = stackBelow m0 32 := by
    show st2.data.regs.get64 .rsp = _
    rw [hm2.regs .rsp _ hsp1]
    show stackBelow m0 32 + BitVec.ofInt 64 0 = _
    rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  have hql' := hload hqw
  have hwl' := hload hww
  have hcq : (queries.toList.length.toUInt64).toBitVec.ult (BitVec.ofNat 64 231) = true :=
    count_lt (N := 230) (by rw [toNat_len (by omega)]; exact hq230) (by decide) (by decide)
  have hcw : (weights.toList.length.toUInt64).toBitVec.ult (BitVec.ofNat 64 231) = true :=
    count_lt (N := 230) (by rw [toNat_len (by omega)]; exact hw230) (by decide) (by decide)
  have hqn : (queries.toList.length.toUInt64).toBitVec.toNat = queries.toList.length := by
    rw [UInt64.toNat_toBitVec, toNat_len (by omega)]
  have hwn : (weights.toList.length.toUInt64).toBitVec.toNat = weights.toList.length := by
    rw [UInt64.toNat_toBitVec, toNat_len (by omega)]
  have hmun : mu.toUInt64.toBitVec.toNat = mu := by
    rw [UInt64.toNat_toBitVec, toNat_len (by omega)]
  have hx0 : reg st2.data .rdi = reg m0 .rdi := hm2.regs .rdi _ hrdi1
  have hx1 : reg st2.data .rsi = mu.toUInt64.toBitVec := by
    refine (hm2.regs .rsi _ rfl).trans ?_
    rw [eval_load, hload hmuw]
  have hx2 : reg st2.data .rdx = reg m0 .rsi + BitVec.ofNat 64 536 := by
    refine (hm2.regs .rdx _ rfl).trans ?_
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hql', hcq]
    rfl
  have hx3 : reg st2.data .rcx = (queries.toList.length.toUInt64).toBitVec := by
    refine (hm2.regs .rcx _ rfl).trans ?_
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hql', hcq]
    rfl
  have hx4 : reg st2.data .r8 = reg m0 .rsi + BitVec.ofNat 64 2384 := by
    refine (hm2.regs .r8 _ rfl).trans ?_
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hwl', hcw]
    rfl
  have hx5 : reg st2.data .r9 = (weights.toList.length.toUInt64).toBitVec := by
    refine (hm2.regs .r9 _ rfl).trans ?_
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hwl', hcw]
    rfl
  have hsa : ∀ (i : Nat) (r : Reg64), i < 2 →
      (∀ j < 8, findWrite 0 (8 + 8 * i + j) (after b1 (after b0 entryS)).mem = some (.reg r, j)) →
      stackArg st2.data i = reg m0 r := by
    intro i r hi h
    have := wordAt_of_write hm2 (r := 0) (o := 8 + 8 * i) rfl (by omega)
      (v := .reg r) (after_eq run_b1 ▸ h)
    unfold stackArg
    rw [hrsp2, NativeRustcVm.wordOf_of_wordAt this]
    rfl
  have hsa0 : stackArg st2.data 0 = reg m0 .rdx := hsa 0 .rdx (by decide)
    (after_eq run_b1 ▸ harg0)
  have hsa1 : stackArg st2.data 1 = reg m0 .rcx := hsa 1 .rcx (by decide)
    (after_eq run_b1 ▸ harg1)
  have h8 : (stackBelow m0 32 + 8#64).toNat = (rspOf m0).toNat - 32 + 8 := by
    rw [eight, toNat_add_ofNat _ _ (by rw [hfe]; omega), hfe]
  have hpre2 : InducedWeightPre st2.data := by
    refine ⟨stackOk_callee hS hkept2 hrsp2 hsle2, ⟨fun i hi ↦ ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrsp2, eight, addr_add]
      exact hkept2 _ (hfmap _ (by omega))
    · rw [hrsp2, hfe]; omega
    · rw [hx2, hx3, hqn]
      exact whirIn_callee (WhirIn.sub hgin (by omega)) hS hkept2 hrsp2 hsle2
    · rw [hx4, hx5]
      exact sliceOk_callee (WhirIn.sliceOk hgin (by rw [hwn]; omega)) hS hkept2 hrsp2 hsle2
    · rw [hsa0, hsa1]
      exact sliceOk_callee hx hS hkept2 hrsp2 hsle2
    · rw [hx0]
      exact whirIn_callee hout hS hkept2 hrsp2 hsle2
    · have ho := hout.2
      have hnw := hout.1.2
      unfold OffStack Apart at ho
      unfold NoWrap at hnw
      rw [Arrays.stackBelow_toNat hS1] at ho
      unfold Apart
      rw [hx0, hrsp2, h8]
      omega
    · have hs : SameOutside m0.dmem st2.data.dmem (InRange (stackBelow m0 gluedEvalStack) gluedEvalStack) :=
        fun p hp => hm2.get?_mem0 hwf (fun h => hp (inRange_frame hS hF le_rfl
          (written_region0 rfl hwf (by omega)
            (fun w hw => ⟨(hw1 w hw).1, by have := (hw1 w hw).2; omega⟩) h)))
      have hb := stackBelow_toNat hS.1
      have hd : (stackBelow st2.data inducedWeightStack).toNat =
          (rspOf m0).toNat - 32 - inducedWeightStack := by
        rw [stackBelow_toNat (by rw [hrsp2, hfe]; omega), hrsp2, hfe]
      apply NativeRustcVmX64.GotAt.callee hgot
        (NativeRustcVmX64.GotAt.unchanged_stack hgot hS hs)
      · rw [hb, hd]; omega
      · rw [hb, hd]; omega
      · intro a ha
        simp only [hx0, hx2, hx3, hx4, hx5, hqn, hwn, hsa0, hsa1, hrsp2,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with (rfl | rfl | rfl | rfl) | ha
        · refine ⟨(reg m0 .rsi, gluedBytes), by simp, ?_, ?_⟩
          all_goals dsimp only [Prod.fst, Prod.snd]
          all_goals rw [toNat_add_ofNat _ _ (by have := hgin.1.2; unfold NoWrap at this; omega)]
          all_goals omega
        · refine ⟨(reg m0 .rsi, gluedBytes), by simp, ?_, ?_⟩
          all_goals dsimp only [Prod.fst, Prod.snd]
          all_goals rw [toNat_add_ofNat _ _ (by have := hgin.1.2; unfold NoWrap at this; omega)]
          all_goals omega
        · exact ⟨(reg m0 .rdi, 24), by simp, le_rfl, le_rfl⟩
        · refine ⟨(stackBelow m0 gluedEvalStack, gluedEvalStack + 8), by simp, ?_, ?_⟩ <;>
            rw [hb, h8] <;> omega
        · by_cases hn : 0 < (reg m0 .rcx).toNat
          · simp only [ite_eq_left hn, List.mem_singleton] at ha
            subst a
            exact ⟨(reg m0 .rdx, 16 * (reg m0 .rcx).toNat), by simp [hn], le_rfl, le_rfl⟩
          · simp [hn] at ha
  refine call_then hpc2 hind hpre2 fun st3 hpc3 hrsp3 ⟨hval, hch, hsv⟩ ↦ ?_
  -- the body of the 32 bytes below RSP
  have hfr3 : Frame m0 32 gluedEvalStack slots32 [⟨reg m0 .rdi, 24⟩] st3.data := by
    refine ⟨?_, fun q hq ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_, fun p h ↦ hsv.2 p (hkept2 p h)⟩
    · rw [hrsp3, hrsp2]; rfl
    · simp only [slots32, List.mem_singleton] at hq
      subst hq
      have h := hm2.bytesAt_write (r := 0) (sz := 32 + 8) rfl (by omega) hslot1
      refine bytesAt_eq h fun j hj ↦ ?_
      simp only [List.length_map, List.length_range] at hj
      rw [addr_add]
      rw [hx0] at hch
      exact frame_callee hS hF hrsp2 hsle2 (out_one hout) hch (by omega)
    · exact (hsv.1 r hr).trans (hm2.regs r _ (hoth1 r (others_spec r hr hn)))
    · rw [hch p fun h ↦ h.elim (fun h ↦ hp (.inl (by rw [hx0] at h; exact h)))
        fun h ↦ hp (.inr (inRange_callee hS hrsp2 hsle2 h))]
      exact hm2.get?_mem0 hwf fun h ↦ hp (.inr (inRange_frame hS hF le_rfl
        (written_region0 rfl hwf (k := 32) (by omega) hw1 h)))
  -- `b2`: the epilogue
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b2Offset) := hpc3
  have hwf3 := hfr3.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at hk2 run_b2 hwf3 (by intro l h; cases h) hpc3' hfr3.mid_match
    fun st4 hm4 hpc4 ↦ .done _ ?_
  obtain ⟨hpc', hrsp', hdm, hsaved⟩ := hfr3.done hS hF (out_one hout) hm4 hpc4
    (after_eq run_b2 ▸ b2_restores).1 (after_eq run_b2 ▸ b2_restores).2
  refine ⟨hpc', hrsp', ?_, fun p hp ↦ by rw [hdm]; exact hfr3.same p hp, hsaved⟩
  have hQ : wordSlice st2.data (reg m0 .rsi + BitVec.ofNat 64 536) queries.toList.length =
      queries := by
    rw [wordSlice, NativeRustcVm.wordsOf_congr (d := m0.dmem) fun i hi ↦ ?_]
    · rw [eight, addr_add] at hqs
      rw [NativeRustcVm.wordsOf_of_wordsAt hqs, Array.toArray_toList]
    · rw [addr_add]
      exact harg hgin.2 hgin.1.2 _ (by omega)
  have hW : slice st2.data (reg m0 .rsi + BitVec.ofNat 64 2384)
      (weights.toList.length.toUInt64).toBitVec = weights := by
    rw [slice, hwn, NativeRustcVm.ewsOf_congr (d := m0.dmem) fun i hi ↦ ?_]
    · rw [eight, addr_add] at hws
      rw [NativeRustcVm.ewsOf_of_ewsAt hws, Array.toArray_toList]
    · rw [addr_add]
      exact harg hgin.2 hgin.1.2 _ (by omega)
  have hX : slice st2.data (reg m0 .rdx) (reg m0 .rcx) = slice m0 (reg m0 .rdx) (reg m0 .rcx) := by
    rw [slice, slice, NativeRustcVm.ewsOf_congr fun i hi ↦ harg hx.2 hx.1.2 i hi]
    rfl
  rw [hx0, hx1, hx2, hx3, hx4, hx5, hsa0, hsa1, hmun, hqn] at hval
  simp only [hmu, ↓reduceIte] at hval
  rw [hQ, hW, hX] at hval
  rw [hdm, hgw]
  exact hval

/-- **`glued_eval` meets its contract.** -/
theorem gluedEval_spec (hp : Placed code k)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost)
    (hind : Spec (Labels.label NativeRustcVmX64.Vm.InducedWeight.entryLabel) InducedWeightPre InducedWeightPost)
    (g : GluedClaimW) : Spec (Labels.label NativeRustcVmX64.Vm.GluedEval.entryLabel) (GluedEvalPre g) (GluedEvalPost g) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.GluedEval.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.GluedEval.b0Offset) from hp.label NativeRustcVmX64.Vm.GluedEval.entry_at]
  cases hgw : g.weight with
  | eq z => exact eq_branch hp heq hpre hgw
  | induced mu queries weights => exact induced_branch hp hind hpre hgw

end

end NativeRustcVmX64.Whir.GluedEval
