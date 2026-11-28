module

public import NativeRustcVmX64.Whir.InducedWeight.Inv

/-!
# `induced_weight`'s ends (x86-64)

`tag_fin`: `b18a` stores the tag (RAX) at the output R14 points to, `b18b` returns. `finish`:
from `Done` at `b17`, the sum stored, the tag `1`. `none_fin`: for `μ > 30`, `b15` the tag `0`.
`zero_fin`: with no query, `b16` the sum `0`.
-/

namespace NativeRustcVmX64.Whir.InducedWeight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVm.Transcript (off OptEWAt)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq wordAt_of_write ewAt_of_writes eval_reg
  eval_lit eval_load wf_two apart_symm not_inRange_of_apart)

public section

/-- `induced_weight`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ InducedWeightPost m0 s.data

/-- The output's frame. -/
abbrev OFrame (m0 st : MachineData) : Prop :=
  Frame m0 1168 inducedWeightStack slots [⟨reg m0 .rdi, 24⟩] st

/-- The result. -/
def resOf (m0 : MachineData) : Option EW :=
  if (reg m0 .rsi).toNat ≤ stackCap then
    some (inducedWeight (reg m0 .rsi).toNat (wordSlice m0 (reg m0 .rdx) (reg m0 .rcx).toNat)
      (slice m0 (reg m0 .r8) (reg m0 .r9)) (slice m0 (stackArg m0 0) (stackArg m0 1)))
  else none

variable [Host] {k : Nat}

theorem hb15 (hp : Placed code k) : b15.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b15Offset) :=
  b15_in_code.trans hp.1 (by simp [b15])
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b16Offset) :=
  b16_in_code.trans hp.1 (by simp [b16])
theorem hb17 (hp : Placed code k) : b17.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b17Offset) :=
  b17_in_code.trans hp.1 (by simp [b17])
theorem hb18 (hp : Placed code k) : b18a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b18Offset) ∧
    b18b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b18Offset + b18a.length) := by
  have h := b18_in_code.trans hp.1 (by simp [b18])
  rw [← List.take_append_drop 2 b18] at h
  exact h.append

/-- **The tag and the epilogue** (`b18a`, `b18b`): R14 the output, RAX the tag, the value (for
`Some`) already stored. -/
theorem tag_fin (hp : Placed code k) {m0 : MachineData} (hpre : InducedWeightPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b18Offset)) (hfr : OFrame m0 st.data)
    (hr14 : reg st.data .r14 = reg m0 .rdi) {v : Option EW}
    (htag : reg st.data .rax = BitVec.ofNat 64 (if v.isSome then 1 else 0))
    (hval : ∀ x, v = some x → NativeRustcVm.EWAt st.data.dmem (off (reg m0 .rdi) 8) x)
    (hv : v = resOf m0) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hS, -, -, -, -, hout, -⟩ := hpre
  have hF : 1168 ≤ inducedWeightStack := stack_le.1
  have hrd : Readable st.data (reg m0 .rdi) 8 :=
    Readable.keep (Readable.mono hout.1 (by omega)) hfr.kept
  have hwf : (Env.ofMachine st.data [(reg m0 .rdi, 8)]).WF :=
    Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(reg m0 .rdi, 8)]) tagS st.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show reg st.data .r14 = reg m0 .rdi + BitVec.ofInt 64 0 by
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; exact hr14, trivial⟩
      trivial trivial trivial
  refine exec_at (hb18 hp).1 run_b18a hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk1, hw1, hv1⟩ := after_eq run_b18a ▸ b18a_write
  have hfr1 : OFrame m0 st1.data := hfr.of_write hm hm1 hwf rfl hk1 (r := 0) rfl le_rfl hw1
    (fun p h ↦ .inl (inAny_one (Arrays.inRange_sub hout.1.2 (c := 0) (m := 8) (by omega)
      (by rwa [NativeRustcVm.addr_add_zero]))))
    fun q hq i hi ↦ by
      rw [addr_add]
      exact not_inRange_of_apart (Arrays.apart_mono (apart_symm (apart_frame' hS hF hout.2))
        (n'' := 8) (by omega)) (frame_ok hS hF).2.1
        (NativeRustcVm.NoWrap.mono hout.1.2 (by omega)) (by have := slots_ok q hq; omega)
  have hso1 := same_region_le hm1 hwf (r := 0) rfl le_rfl hw1
  have htag1 : WordAt st1.data.dmem (reg m0 .rdi) (if v.isSome then 1 else 0) := by
    have := wordAt_of_write hm1 (r := 0) (o := 0) rfl (by decide) (v := .reg .rax) hv1
    rw [NativeRustcVm.addr_add_zero, eval_reg, Env.ofMachine_regs,
      show st.data.regs.get64 .rax = _ from htag] at this
    convert this using 1
    split <;> rfl
  -- `b18b`
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b18Offset + b18a.length) := hpc1
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb18 hp).2 run_b18b hwf2 (by intro l h; cases h) hpc1' hfr1.mid_match
    fun st2 hm2 hpc2 ↦ .done _ ?_
  obtain ⟨hpc', hrsp', hdm, hsaved⟩ := hfr1.done hS hF (out_one hout) hm2 hpc2
    (after_eq run_b18b ▸ b18b_restores).1 (after_eq run_b18b ▸ b18b_restores).2
  refine ⟨hpc', hrsp', ?_, fun p hp ↦ by rw [hdm]; exact hfr1.same p hp, hsaved⟩
  show OptEWAt st2.data.dmem (reg m0 .rdi) (resOf m0)
  rw [← hv, hdm]
  cases hvv : v with
  | none => rw [hvv] at htag1; exact htag1
  | some x =>
    rw [hvv] at htag1
    refine ⟨htag1, NativeRustcVm.BytesAt.of_sameOutside_apart (hval x hvv) hso1 ?_
      (NativeRustcVm.NoWrap.sub hout.1.2 (by rw [NativeRustcVm.length_ewBytes]))
      (NativeRustcVm.NoWrap.mono hout.1.2 (by omega))⟩
    rw [NativeRustcVm.length_ewBytes]
    have := hout.1.2
    unfold NoWrap at this
    unfold NativeRustcVm.Apart off
    rw [toNat_add_ofNat _ _ (by omega)]
    omega

/-- **The sum stored** (`b17`), then the tag and the epilogue. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : InducedWeightPre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b17Offset)) (hD : Done m0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hpre' := hpre
  obtain ⟨hS, -, -, -, -, hout, -⟩ := hpre'
  have hF : 1168 ≤ inducedWeightStack := stack_le.1
  have hfr : OFrame m0 st.data := frame_mono hD.fr
  have hwf : (Env.ofMachine st.data [(stackBelow m0 1168, 1168 + 8), (reg m0 .rdi, 24)]).WF :=
    wf_two (stackOk_mono hS hF) hfr.kept (Readable.keep hout.1 hfr.kept)
      (apart_symm (apart_frame' hS hF hout.2))
  have hm : Match (Env.ofMachine st.data [(stackBelow m0 1168, 1168 + 8), (reg m0 .rdi, 24)]) outS
      st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr.rsp, trivial⟩ trivial trivial
      ⟨by
        show (Sym.load 0 24 8).eval (Env.ofMachine st.data [(stackBelow m0 1168, 1168 + 8),
          (reg m0 .rdi, 24)]) = reg m0 .rdi + BitVec.ofInt 64 0
        rw [eval_load, load8_eq]
        show (wordOf st.data.dmem (fbOf m0 + BitVec.ofNat 64 24)).toBitVec = _
        rw [NativeRustcVm.wordOf_of_wordAt hD.out, UInt64.toBitVec_ofBitVec,
          show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine exec_at (hb17 hp) run_b17 hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk1, hw1, hv8, hv16⟩ := after_eq run_b17 ▸ b17_write
  have hfr1 : OFrame m0 st1.data := hfr.of_write hm hm1 hwf rfl hk1 (r := 1) rfl le_rfl hw1
    (fun p h ↦ .inl (inAny_one h))
    fun q hq i hi ↦ by
      rw [addr_add]
      exact not_inRange_of_apart (apart_symm (apart_frame' hS hF hout.2)) (frame_ok hS hF).2.1
        hout.1.2 (by have := slots_ok q hq; omega)
  have hval := ewAt_of_writes hm1 (r := 1) (o := 8) rfl (by decide) hv8 hv16
  rw [eval_reg, eval_reg, Env.ofMachine_regs, Env.ofMachine_regs,
    show st.data.regs.get64 .rcx = _ from hD.rcx, show st.data.regs.get64 .rax = _ from hD.rax]
    at hval
  have hr14 : reg st1.data .r14 = reg m0 .rdi := by
    refine (hm1.regs .r14 _ rfl).trans ?_
    rw [eval_load, load8_eq]
    show (wordOf st.data.dmem (fbOf m0 + BitVec.ofNat 64 24)).toBitVec = _
    rw [NativeRustcVm.wordOf_of_wordAt hD.out, UInt64.toBitVec_ofBitVec]
  have hmu : (reg m0 .rsi).toNat ≤ stackCap := hD.mu
  refine tag_fin hp hpre hpc1 hfr1 hr14 (v := some (totOf m0 (cntOf m0)))
    ((hm1.regs .rax _ rfl).trans rfl) (fun x hx ↦ ?_) ?_
  · cases hx
    exact hval
  · rw [totOf_cnt]
    simp only [resOf, hmu, ↓reduceIte]
    rfl

/-- **`μ > 30`**: `b15` the tag `0`, then the epilogue. -/
theorem none_fin (hp : Placed code k) {m0 : MachineData} (hpre : InducedWeightPre m0)
    (hmu : ¬(reg m0 .rsi).toNat ≤ stackCap) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b15Offset)) (hfr : Fr m0 st.data)
    (hr14 : reg st.data .r14 = reg m0 .rdi) :
    Eventually (step1 Host.exe) (Post m0) st := by
  refine exec_at (hb15 hp) run_b15 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (after_eq run_b15 ▸ b15_keeps)
  simp only [PcOk] at hpc1
  refine tag_fin hp hpre (hpc1.trans (hp.label NativeRustcVmX64.Vm.InducedWeight.label_4_at)) (frame_mono hfr1)
    ((Match.reg_eq (match_nil _) hm1 rfl rfl).trans hr14) (v := none)
    ((hm1.regs .rax _ rfl).trans rfl) (fun _ h ↦ by cases h) ?_
  simp only [resOf, hmu, ↓reduceIte]

/-- **No query**: `b16` the sum `0`, then the store. -/
theorem zero_fin (hp : Placed code k) {m0 : MachineData} (hpre : InducedWeightPre m0)
    (hmu : muOf m0 ≤ stackCap) (hc : cntOf m0 = 0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b16Offset)) (hfr : Fr m0 st.data)
    (hout : WordAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofBitVec (reg m0 .rdi))) :
    Eventually (step1 Host.exe) (Post m0) st := by
  refine exec_at (hb16 hp) run_b16 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (after_eq run_b16 ▸ b16_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  refine finish hp hpre hpc1 ⟨hfr1, hd1 ▸ hout, hmu, ?_, ?_⟩
  · rw [hc, totOf_zero]; exact (hm1.regs .rcx _ rfl).trans rfl
  · rw [hc, totOf_zero]; exact (hm1.regs .rax _ rfl).trans rfl

end

end NativeRustcVmX64.Whir.InducedWeight
