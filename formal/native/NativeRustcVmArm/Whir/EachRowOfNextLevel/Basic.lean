module

public import NativeRustcVmArm.Whir.EachRowOfNextLevel.Exec
public import NativeRustcVmArm.Whir.EachRowOfNextLevel.Model
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Frame
public import NativeRustcVmArm.Spec.Whir

/-!
# `each_row` with `next_level`'s closure: frame, invariant, exit

The 2000-byte frame below the entry's SP (`fb`): `[sp + 8]` the query weights' count, `[sp + 16]`
the `What`s' address (`fb + 1632`), `[sp + 24]` the table's count, `[sp + 32]`, `[sp + 40]` the
high part's count and address, `[sp + 48]` `μ`'s address, `[sp + 56]` the table's address
(`fb + 104`), the table from `fb + 96` (`Low`); X5, X6, X0, X1 at 64 to 88 and X29, X30 and the
callee-saved registers from 1904 (`slots`); the lanes at 600, the `What`s at 1624,
`novel_eval`'s result at 1880. Memory changes in the stack and the batched value at `bOf` (its
`nextEnv` word 3). The loop's invariant at `.LEachRowOfNextLevel_5` (`Inv j`): the batched value
the partial sum of `j` rows, X24 = `j`, X22 the queries' bytes left, X23 query weight `j`'s
address plus 8. The exit (`exit_step`) returns `1`.
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfNextLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(64, .X5), (72, .X6), (80, .X0), (88, .X1), (1904, .X29), (1912, .X30), (1920, .X28),
    (1928, .X27), (1936, .X26), (1944, .X25), (1952, .X24), (1960, .X23), (1968, .X22),
    (1976, .X21), (1984, .X20), (1992, .X19)]

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 2000

/-- The batched value's address. -/
abbrev bOf (m0 : MachineData) : BitVec 64 := (nextEnv m0 3).toBitVec

/-- Between the prologue and the epilogue. -/
abbrev FR (m0 m : MachineData) : Prop :=
  Fr m0 2000 eachRowNextStack slots [] (InRange (bOf m0) 16) m

/-- What the loop's calls change. -/
abbrev HitN (m0 : MachineData) : BitVec 64 → Prop := EachRow.Hit m0 2000 eachRowNextStack 600 1904

/-- The queries. -/
abbrev qsOf (m0 : MachineData) : Array UInt64 := (eachRowArgs m0).1

/-- The high part. -/
abbrev highOf (m0 : MachineData) : Array EW := slice m0 (nextEnv m0 1) (nextEnv m0 2)

/-- The query weights. -/
abbrev qwOf (m0 : MachineData) : Array EW := slice m0 (nextEnv m0 4) (nextEnv m0 5)

/-- The table `subspace_table` computes. -/
abbrev tableOf (m0 : MachineData) : Array (UInt64 × UInt64) := subspaceTable m0.regs.X4.toNat

/-- The batched value after `j` rows. -/
abbrev parOf (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) : EW :=
  EachRow.nextPartial m0.regs.X0.toNat m0.regs.X4.toNat (eachRowArgs m0).2 (highOf m0) (qsOf m0)
    rows (qwOf m0) j

/-- **The frame's locals** below the lanes. -/
structure Low (m0 : MachineData) (d : Mem 64) : Prop where
  w8 : WordAt d (fb m0 + BitVec.ofNat 64 8) (nextEnv m0 5)
  w16 : WordAt d (fb m0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (fb m0 + BitVec.ofNat 64 1632))
  w24 : WordAt d (fb m0 + BitVec.ofNat 64 24) (tableOf m0).size.toUInt64
  w32 : WordAt d (fb m0 + BitVec.ofNat 64 32) (nextEnv m0 2)
  w40 : WordAt d (fb m0 + BitVec.ofNat 64 40) (nextEnv m0 1)
  w48 : WordAt d (fb m0 + BitVec.ofNat 64 48) (nextEnv m0 0)
  w56 : WordAt d (fb m0 + BitVec.ofNat 64 56) (UInt64.ofBitVec (fb m0 + BitVec.ofNat 64 104))
  tab : BufPairsAt d (fb m0 + BitVec.ofNat 64 96) rootCap (tableOf m0).toList

/-- **The loop's invariant** at `.LEachRowOfNextLevel_5`, before row `j`. -/
structure Inv (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 m
  low : Low m0 m.dmem
  hj : j < rows.size
  hjq : j ≤ (qsOf m0).size
  bat : EWAt m.dmem (bOf m0) (parOf rows m0 j)
  x19 : m.regs.getXReg .X19 = rows.size.toUInt64
  x20 : (m.regs.getXReg .X20).toBitVec = bOf m0
  x21 : m.regs.getXReg .X21 = m0.regs.X3
  x22 : m.regs.getXReg .X22 = (8 * ((qsOf m0).size - j)).toUInt64
  x23 : (m.regs.getXReg .X23).toBitVec = (nextEnv m0 4).toBitVec + BitVec.ofNat 64 (8 + 16 * j)
  x24 : m.regs.getXReg .X24 = j.toUInt64

/-- The end: back at the caller with the contract's postcondition. -/
def Done (rows : Array (Array UInt64)) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ EachRowNextPost rows m0 st.data

end

public section

theorem stack_eq : eachRowNextStack = 3232 := rfl

theorem slots_ok : ∀ p ∈ slots, p.1 + 8 ≤ 600 ∨ (1904 ≤ p.1 ∧ p.1 + 8 ≤ 2000) := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 2000 := by decide

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

/-- The layout. -/
theorem lay (hpre : EachRowNextPre rows op m0) :
    EachRow.Lay m0 2000 eachRowNextStack 600 1904 :=
  ⟨by decide, by decide, by decide, hpre.1.1.2.1⟩

/-- The batched value is apart from the frame. -/
theorem bat_not_frame (hpre : EachRowNextPre rows op m0) :
    ∀ q, InRange (bOf m0) 16 q → ¬InRange (fb m0) 2000 q := by
  have hb := hpre.2.2.2.2.2.2.2.1
  have hap := Ring.apart_frame (F := 2000) hpre.1.1.2.1 (by decide) hb.2
  exact fun q hq ↦ NativeRustcVm.Transcript.not_inRange_of_apart hap hb.1.2
    (Ring.base_noWrap (by have := hpre.1.1.2.1; rw [stack_eq] at this; omega)) hq

/-- **The batched value kept** by a step changing memory in the stack only. -/
theorem bat_keep (hpre : EachRowNextPre rows op m0) {d d' : Mem 64} {x : EW}
    {W : BitVec 64 → Prop} (h : EWAt d (bOf m0) x) (hs : SameOutside d d' W)
    (hW : ∀ q, W q → InRange (base m0 eachRowNextStack) eachRowNextStack q) :
    EWAt d' (bOf m0) x := by
  have hb := hpre.2.2.2.2.2.2.2.1
  refine h.of_sameOutside hs fun i hi hq ↦ ?_
  rw [NativeRustcVm.length_ewBytes] at hi
  exact NativeRustcVm.Transcript.not_inRange_of_apart hb.2 hb.1.2 (Ring.base_noWrap hpre.1.1.2.1)
    (NativeRustcVm.inRange_add hi (by have := hb.1.2; unfold NoWrap at this; omega)) (hW _ hq)

/-- **The locals kept** by a step changing memory in `HitN`. -/
theorem Low.keep {d d' : Mem 64} (hl : EachRow.Lay m0 2000 eachRowNextStack 600 1904)
    (h : Low m0 d) (hs : SameOutside d d' (HitN m0)) : Low m0 d' := by
  have kw : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 600 → WordAt d (fb m0 + BitVec.ofNat 64 o) w →
      WordAt d' (fb m0 + BitVec.ofNat 64 o) w := fun ho hw ↦
    EachRow.keep_low hl hs (by rw [NativeRustcVm.length_wordBytes]; omega) hw
  obtain ⟨hl', hw, hp⟩ := h.tab
  refine ⟨kw (by decide) h.w8, kw (by decide) h.w16, kw (by decide) h.w24, kw (by decide) h.w32,
    kw (by decide) h.w40, kw (by decide) h.w48, kw (by decide) h.w56, hl', kw (by decide) hw, ?_⟩
  have e : off (fb m0 + BitVec.ofNat 64 96) 8 = fb m0 + BitVec.ofNat 64 104 :=
    NativeRustcVm.addr_add_add _ _ _
  rw [e] at hp ⊢
  refine EachRow.keep_low hl hs ?_ hp
  rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords]
  have : (tableOf m0).toList.length ≤ 31 := hl'
  omega

/-- **An input** of the entry apart from the batched value, unchanged in a body. -/
theorem input_same' (hpre : EachRowNextPre rows op m0) {m : MachineData} (hfr : FR m0 m)
    {a : BitVec 64} {n : Nat} (h : WhirIn m0 a n eachRowNextStack) (hA : Apart (bOf m0) 16 a n) :
    ∀ i < n, m.dmem.get? (a + BitVec.ofNat 64 i) = m0.dmem.get? (a + BitVec.ofNat 64 i) :=
  EachRow.input_same hfr hpre.1.1.2.1 h.1.2 h.2 fun i hi ↦
    NativeRustcVm.Transcript.not_inRange_of_apart (NativeRustcVm.Apart.symm hA) h.1.2
      hpre.2.2.2.2.2.2.2.1.1.2 (NativeRustcVm.inRange_add hi (by
        have := h.1.2; unfold NoWrap at this; omega))

/-- The frame alone, as an environment. -/
theorem frame_env [Labels] (hpre : EachRowNextPre rows op m0) {m : MachineData} (hfr : FR m0 m) :
    (Env.ofMachine m [(fb m0, 2000)]).WF ∧ Match (Env.ofMachine m [(fb m0, 2000)]) frameS m := by
  have hstk := hpre.1.1
  have hS : 3232 ≤ m0.regs.SP.toNat := hstk.2.1
  exact ⟨Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
      Ring.base_noWrap (by omega)⟩, trivial⟩ (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial trivial⟩

variable [Host] {k : Nat}

/-- **The exit**: from `.LEachRowOfNextLevel_13`, the batched value `batchedOf`, `1`. -/
theorem exit_step (hp : Placed code k) (hpre : EachRowNextPre rows op m0) {m : MachineData}
    (hfr : FR m0 m)
    (hbat : EWAt m.dmem (bOf m0) (batchedOf m0.regs.X0.toNat m0.regs.X4.toNat (eachRowArgs m0).2
      (highOf m0) (eachRowArgs m0).1 rows (qwOf m0))) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b23Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env hpre hfr
  have hk23 : b23.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b23Offset) := b23_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk24 : b24.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b24Offset) := b24_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk23 run_b23 hwf hm fun st23 hm23 hpc23 ↦
    exec_at hk24 (exec_after run_b23 run_b24t) hwf hpc23 hm23 fun st hm' hpc ↦ .done _ ?_
  obtain ⟨hret, hsaved⟩ := Ring.Fr.exit hfr hm' hwf (by decide)
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  refine ⟨hpc.trans hret, (rv hm' (r := .X0) rfl).trans rfl, hd ▸ hbat, ?_, hsaved⟩
  intro q hq
  rw [hd]
  exact hfr.same q fun h ↦ hq (h.elim .inr fun h' ↦ .inl ⟨_, List.mem_singleton_self _, h'⟩)

end

end NativeRustcVmArm.Whir.EachRowOfNextLevel
