module

public import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Exec
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Frame
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Model
public import NativeRustcVmArm.Spec.Whir

/-!
# `each_row` with `final_level`'s closure: frame, invariant, exit

The 1952-byte frame below the entry's SP (`fb`): `[sp + 8]` the `What`s' address (`fb + 1584`),
`[sp + 16]`, `[sp + 24]` the table's count and address (`fb + 56`), `[sp + 32]`, `[sp + 40]` the
folded scalars' count and address, the table from `fb + 48` (`Low`); the lanes at 552, the
`What`s at 1576, `novel_eval`'s result at 1832; X29, X30 and the callee-saved registers from 1856
(`slots`, with X7 at 40). The loop's invariant at `.LEachRowOfFinalLevel_3` (`Inv j`): rows
`0 … j - 1` checked, X25 = `j`, X19 the bytes of queries left, X28 the rows' count. The exit
(`exit_step`) returns `okWord b` for the outcome `b`.
-/

namespace NativeRustcVmArm.Whir.EachRowOfFinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfFinalLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- The prologue's slots: X7 (the folded scalars) at 40, X29, X30 and the callee-saved registers
from 1856. -/
def slots : List (Nat × XReg) :=
  [(40, .X7), (1856, .X29), (1864, .X30), (1872, .X28), (1880, .X27), (1888, .X26), (1896, .X25),
    (1904, .X24), (1912, .X23), (1920, .X22), (1928, .X21), (1936, .X20), (1944, .X19)]

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 1952

/-- Between the prologue and the epilogue. -/
abbrev FR (m0 m : MachineData) : Prop :=
  Fr m0 1952 eachRowFinalStack slots [] (fun _ ↦ False) m

/-- What the loop's steps change. -/
abbrev HitF (m0 : MachineData) : BitVec 64 → Prop := EachRow.Hit m0 1952 eachRowFinalStack 552 1856

/-- The queries. -/
abbrev qsOf (m0 : MachineData) : Array UInt64 := (eachRowArgs m0).1

/-- Row `i`'s check. -/
abbrev okOf (m0 : MachineData) (q : UInt64) (row : Array UInt64) : Bool :=
  EachRow.rowOk m0.regs.X0.toNat m0.regs.X4.toNat (eachRowArgs m0).2
    (slice m0 m0.regs.X7 (whirStackArg m0 0)) q row

/-- The table `subspace_table` computes. -/
abbrev tableOf (m0 : MachineData) : Array (UInt64 × UInt64) := subspaceTable m0.regs.X4.toNat

/-- **The frame's locals** below the lanes. -/
structure Low (m0 : MachineData) (d : Mem 64) : Prop where
  w8 : WordAt d (fb m0 + BitVec.ofNat 64 8) (UInt64.ofBitVec (fb m0 + BitVec.ofNat 64 1584))
  w16 : WordAt d (fb m0 + BitVec.ofNat 64 16) (tableOf m0).size.toUInt64
  w24 : WordAt d (fb m0 + BitVec.ofNat 64 24) (UInt64.ofBitVec (fb m0 + BitVec.ofNat 64 56))
  w32 : WordAt d (fb m0 + BitVec.ofNat 64 32) (whirStackArg m0 0)
  tab : BufPairsAt d (fb m0 + BitVec.ofNat 64 48) rootCap (tableOf m0).toList

/-- **The loop's invariant** at `.LEachRowOfFinalLevel_3`, before row `j`. -/
structure Inv (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 m
  low : Low m0 m.dmem
  hj : j < rows.size
  hjq : j ≤ (qsOf m0).size
  ok : ∀ i (h1 : i < (qsOf m0).size) (h2 : i < rows.size), i < j →
    okOf m0 (qsOf m0)[i] rows[i] = true
  x19 : m.regs.getXReg .X19 = (8 * ((qsOf m0).size - j)).toUInt64
  x25 : m.regs.getXReg .X25 = j.toUInt64
  x28 : m.regs.getXReg .X28 = rows.size.toUInt64
  x20 : m.regs.getXReg .X20 = m0.regs.X6
  x21 : m.regs.getXReg .X21 = m0.regs.X5
  x22 : m.regs.getXReg .X22 = m0.regs.X3
  x23 : m.regs.getXReg .X23 = m0.regs.X1
  x24 : m.regs.getXReg .X24 = m0.regs.X0

/-- The end: back at the caller with the contract's postcondition. -/
def Done (rows : Array (Array UInt64)) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ EachRowFinalPost rows m0 st.data

end

public section

theorem stack_eq : eachRowFinalStack = 3184 := rfl

theorem slots_ok : ∀ p ∈ slots, p.1 + 8 ≤ 552 ∨ (1856 ≤ p.1 ∧ p.1 + 8 ≤ 1952) := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1952 := by decide

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

/-- The layout. -/
theorem lay (hpre : EachRowFinalPre rows op m0) :
    EachRow.Lay m0 1952 eachRowFinalStack 552 1856 :=
  ⟨by decide, by decide, by decide, hpre.1.1.2.1⟩

/-- **The locals kept** by a step changing memory in `HitF`. -/
theorem Low.keep {d d' : Mem 64} (hl : EachRow.Lay m0 1952 eachRowFinalStack 552 1856)
    (h : Low m0 d) (hs : SameOutside d d' (HitF m0)) : Low m0 d' := by
  have kw : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 552 → WordAt d (fb m0 + BitVec.ofNat 64 o) w →
      WordAt d' (fb m0 + BitVec.ofNat 64 o) w := fun ho hw ↦
    EachRow.keep_low hl hs (by rw [NativeRustcVm.length_wordBytes]; omega) hw
  obtain ⟨hl', hw, hp⟩ := h.tab
  refine ⟨kw (by decide) h.w8, kw (by decide) h.w16, kw (by decide) h.w24, kw (by decide) h.w32,
    hl', kw (by decide) hw, ?_⟩
  have e : off (fb m0 + BitVec.ofNat 64 48) 8 = fb m0 + BitVec.ofNat 64 56 :=
    NativeRustcVm.addr_add_add _ _ _
  rw [e] at hp ⊢
  refine EachRow.keep_low hl hs ?_ hp
  rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords]
  have : (tableOf m0).toList.length ≤ 31 := hl'
  omega

variable [Host] {k : Nat}

/-- **The exit** with outcome `b`: from `.LEachRowOfFinalLevel_9` (`b`) or `_10` (not `b`). -/
theorem exit_step (hp : Placed code k) (hpre : EachRowFinalPre rows op m0) {m : MachineData}
    (hfr : FR m0 m) (b : Bool)
    (hres : finalOk m0.regs.X0.toNat m0.regs.X4.toNat (eachRowArgs m0).2
      (slice m0 m0.regs.X7 (whirStackArg m0 0)) (eachRowArgs m0).1 rows = b) :
    Eventually (step1 Host.exe) (Done rows m0)
      ⟨m, Host.addrOf (k + if b then NativeRustcVmArm.Vm.EachRowOfFinalLevel.b16Offset else NativeRustcVmArm.Vm.EachRowOfFinalLevel.b17Offset)⟩ := by
  have hstk := hpre.1.1
  have hl := lay hpre
  let env := Env.ofMachine m [(fb m0, 1952)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
      Ring.base_noWrap (by have := hstk.2.1; rw [stack_eq] at this; omega)⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match env frameS m :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  have hk18 : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b18Offset) := b18_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have fin : ∀ {S₁ : SState} {st : MachineState}, Match env S₁ st.data → S₁.mem = [] →
      Ring.exitOk S₁ 1952 slots [] = true → st.pc = retOf st.data →
      (st.data.regs.X0 = okWord b) → Done rows m0 st := fun hm' hmem hok hpc hx0 ↦ by
    obtain ⟨hret, hsaved⟩ := Ring.Fr.exit hfr hm' hwf hok
    refine ⟨hpc.trans hret, ?_, ?_, hsaved⟩
    · rw [hx0, hres]
    · intro q hq
      rw [hm'.dmem_eq hwf hmem]
      exact hfr.same q fun h ↦ hq (h.elim .inr False.elim)
  cases b with
  | true =>
    have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b16Offset) := b16_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_then hk16 run_b16 hwf hm fun st16 hm16 hpc16 ↦ ?_
    have hpc16' : st16.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b18Offset) := by
      rw [show Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b18Offset) = Labels.label NativeRustcVmArm.Vm.EachRowOfFinalLevel.label_11 from
        (hp.label (j := NativeRustcVmArm.Vm.EachRowOfFinalLevel.b18Offset)
          NativeRustcVmArm.Vm.EachRowOfFinalLevel.label_11_at).symm]
      exact hpc16
    exact exec_at hk18 (exec_after run_b16 run_b18t) hwf hpc16' hm16 fun st hm' hpc ↦
      .done _ (fin hm' rfl (by decide) hpc ((rv hm' (r := .X0) rfl).trans rfl))
  | false =>
    have hk17 : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b17Offset) := b17_in_code.trans hp.1 (List.cons_ne_nil _ _)
    exact exec_then hk17 run_b17 hwf hm fun st17 hm17 hpc17 ↦
      exec_at hk18 (exec_after run_b17 run_b18f) hwf hpc17 hm17 fun st hm' hpc ↦
        .done _ (fin hm' rfl (by decide) hpc ((rv hm' (r := .X0) rfl).trans rfl))

end

end NativeRustcVmArm.Whir.EachRowOfFinalLevel
