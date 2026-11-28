module

public import NativeRustcVmX64.Tables.ColumnClaims.Loop

/-!
# `table_column_claims`: the tables' setups (x86-64)

A table's setup block (`b0b` from the prologue `b0a`, then `b5`, `b10`, `b15`, `b20`, `b26` with
the evaluations' address from the frame's word `8`) reads its values' count and its point's
length and sets its loop's registers (`Shapes`): table `t`'s loop head with no value pushed
(`setup`, `entry`).
-/

namespace NativeRustcVmX64.Tables.ColumnClaims

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableColumnClaims NativeRustcVmX64.Field NativeRustcVmX64.Tables
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap Same)
open NativeRustcVm (wordOf ewOf ewsOf)

public section

variable {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW} {m0 : MachineData}

theorem addE_eval [Labels] (env : Env) (x : Sym) (o : Nat) (sw : Bool) :
    (addE x o sw).eval env = x.eval env + BitVec.ofNat 64 o := by
  cases sw
  · simp only [addE, Bool.false_eq_true, ↓reduceIte, eval_add, eval_lit]
  · simp only [addE, ↓reduceIte, eval_add, eval_lit]; exact BitVec.add_comm _ _

theorem ltW_eval [Labels] {env : Env} {o b v : Nat} (hv : env.load 1 o 8 = BitVec.ofNat 64 v)
    (hlt : v < b) (hb : b < 2 ^ 64) : (ltW o b).eval env = true := by
  simp only [ltW, SBool.eval, CmpOp.apply, low_W64, BitVec.ult, Sym.eval, hv, BitVec.toNat_ofNat,
    decide_eq_true_eq, show Width.W64.bits = 64 from rfl]
  omega

/-- **The registers a setup sets**: table `t`'s loop head. -/
theorem shapes_regs [Labels] (hpre : TableColumnClaimsPre ev cs m0) {R : Regs} {t c : Nat}
    (ht : t < 6) {x : Sym} {sw : Bool} {S : SState} (hs : Shapes R t c x sw S) {env : Env}
    {st : MachineData} (hm : Match env S st)
    (hx : x.eval env = reg m0 .rdi)
    (hcnt : env.load 1 (1968 * t + 488) 8 = BitVec.ofNat 64 (cnt ev t))
    (hpl : env.load 1 (1968 * t) 8 = BitVec.ofNat 64 (plen ev t)) :
    reg st R.a = valAddr m0 t + BitVec.ofNat 64 (16 * 0) ∧
      reg st R.n = BitVec.ofNat 64 (16 * (cnt ev t - 0)) ∧ reg st R.p = ptAddr m0 t ∧
      reg st R.l = BitVec.ofNat 64 (plen ev t) ∧ reg st R.c = BitVec.ofNat 64 c ∧
      reg st .rsp = (Sym.ptr 0 8).eval env := by
  have h1 := ltW_eval hcnt (show cnt ev t < 93 by have := cnt_le hpre ht; omega) (by decide)
  have h2 := ltW_eval hpl (show plen ev t < 31 by have := plen_le hpre ht; omega) (by decide)
  have hs' := hs
  simp only [Shapes, RegsAre, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hs'
  obtain ⟨sa, sn, sp, sl, sc, ssp⟩ := hs'
  refine ⟨?_, ?_, ?_, ?_, ?_, hm.regs _ _ ssp⟩
  · rw [show reg st R.a = _ from hm.regs _ _ sa]
    simp only [Sym.eval, SBool.eval, h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [addE_eval, hx, Nat.mul_zero, add_ofNat_zero]; rfl
  · rw [show reg st R.n = _ from hm.regs _ _ sn]
    simp only [Sym.eval, SBool.eval, h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [show BinOp.apply .shl .W64 (env.load 1 (1968 * t + 488) 8) (BitVec.ofNat 64 4) =
      (Sym.bin .shl .W64 (.load 1 (1968 * t + 488) 8) (.lit 4)).eval env from rfl,
      eval_shl_lit _ (by omega), eval_load, hcnt]
    apply BitVec.eq_of_toNat_eq
    have := cnt_le hpre ht
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  · rw [show reg st R.p = _ from hm.regs _ _ sp]
    simp only [Sym.eval, SBool.eval, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [addE_eval, hx]; rfl
  · rw [show reg st R.l = _ from hm.regs _ _ sl]
    simp only [Sym.eval, h2, ↓reduceIte]
    exact hpl
  · rw [show reg st R.c = _ from hm.regs _ _ sc]; rfl

variable [Host]

/-- **A table's setup** from the frame's word `8`: table `t`'s loop head, no value pushed. -/
theorem setup (hpre : TableColumnClaimsPre ev cs m0) {R : Regs} {t c : Nat} (ht : t < 6)
    (hc : c + 1 = base t) {D : List Directive} {kk : Nat} (hD : D.IsInfixAt Host.prog kk)
    (hx : exec D setS = some (after D setS, .fall)) (hs : Shapes R t c (.load 0 8 8) false (after D setS) ∨
      Shapes R t c (.load 0 8 8) true (after D setS))
    (hmem : (after D setS).mem = []) (hka : keepsAll setS (after D setS) (freeRegs slots) = true)
    (hrbx : RegsAre (after D setS) [(.rbx, .reg .rbx)])
    {st : MachineState} (hpc : st.pc = Host.addrOf kk) (hb : Bd m0 st.data)
    (h8 : fw m0 st.data 8 = reg m0 .rdi) (hrb : reg st.data .rbx = reg m0 .rsi)
    (hcl : ClaimsWAt st.data.dmem (reg m0 .rsi) (cs ++ (pre ev t 0).toArray)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (kk + D.length) ∧
      LoopAt ev cs m0 R t 0 st'.data) st := by
  obtain ⟨hS, -, -, -, -, -⟩ := pre_parts hpre
  have hev := ev_part hpre (o := 0) (k := tableEvalsBytes) (by decide) (by omega)
  rw [add_ofNat_zero] at hev
  have hap : Apart (stackBelow m0 64) (64 + 8) (reg m0 .rdi) tableEvalsBytes := by
    have h1 := hS.1
    have h2 := h64
    have hr := (rspOf m0).isLt
    have hh := hev.2.1
    unfold OffStack Apart at hh
    unfold Apart
    rw [stackBelow_toNat (by omega)]
    rw [stackBelow_toNat h1] at hh
    omega
  have hwf := wf_two (vars := fun _ ↦ 0) (ret := 0) (stackOk_mono hS h64) hb.kept
    (show Readable st.data (reg m0 .rdi) tableEvalsBytes from
      ⟨fun i hi ↦ hb.kept _ (hev.1.1 i hi), hev.1.2⟩) hap
  have hm : Match (Env.ofMachine st.data [(stackBelow m0 64, 64 + 8), (reg m0 .rdi, tableEvalsBytes)])
      setS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial
      ⟨by
        show (Sym.load 0 8 8).eval _ = _
        rw [eval_load, load8_eq, Env.base_eq (b := stackBelow m0 64) (n := 64 + 8) rfl,
          Env.ofMachine_mem0]
        simp only [Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.map_some, Option.getD_some, BitVec.ofInt_ofNat]
        rw [BitVec.add_zero]; exact h8, trivial⟩
  refine exec_at hD hx hwf (fun _ h ↦ by cases h) hpc hm fun st' hm' hpc' ↦ .done _ ⟨hpc', ?_⟩
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  have hsm := same_ev hpre hb
  have hld : ∀ o, (Env.ofMachine st.data [(stackBelow m0 64, 64 + 8),
      (reg m0 .rdi, tableEvalsBytes)]).load 1 o 8 = (wordOf st.data.dmem (reg m0 .rdi +
        BitVec.ofNat 64 o)).toBitVec := fun o ↦ by
    rw [load8_eq, Env.base_eq (b := reg m0 .rdi) (n := tableEvalsBytes) rfl, Env.ofMachine_mem0]
  have hx8 : (Sym.load 0 8 8).eval (Env.ofMachine st.data [(stackBelow m0 64, 64 + 8),
      (reg m0 .rdi, tableEvalsBytes)]) = reg m0 .rdi := by
    rw [eval_load, load8_eq, Env.base_eq (b := stackBelow m0 64) (n := 64 + 8) rfl,
      Env.ofMachine_mem0]; exact h8
  have hshape := fun sw (hs' : Shapes R t c (.load 0 8 8) sw (after D setS)) ↦
    shapes_regs hpre ht hs' hm' hx8 (by rw [hld]; exact cnt_word hpre hsm ht)
      (by rw [hld]; exact plen_word hpre hsm ht)
  obtain ⟨ha, hn, hp, hl, hcc, -⟩ := hs.elim (hshape false) (hshape true)
  refine ⟨hb.of_block hm hm' hwf rfl hka, by unfold fw; rw [hd]; exact h8, ?_, Nat.zero_le _,
    ha, hn, hp, hl, by rw [hcc]; congr 1; omega, by rw [hd]; exact hcl⟩
  rw [show reg st'.data .rbx = _ from hm'.regs _ _ (hrbx (.rbx, .reg .rbx) (by simp)), eval_reg,
    Env.ofMachine_regs]
  exact hrb

end

end NativeRustcVmX64.Tables.ColumnClaims
