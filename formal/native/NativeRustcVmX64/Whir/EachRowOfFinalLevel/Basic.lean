module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Exec
public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Frame
public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Model
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel.Names

/-!
# `each_row` with `final_level`'s closure: frame, invariant, exit (x86-64)

The 1936 bytes below the entry's RSP (`fb`, region 0's base; the body's `X(%rsp)` is region 0's
`X + 8`): `[16]` the `Rows`' address, `[24]` the queries' end, `[32]` the rounds' address, `[40]`
the index (`Low`); in an iteration `[48]` the query's address, `[56]` the rows left, `[64]` `j`,
`[72]` query `j`; `novel_eval`'s result at 80, the table's `Option` and then the lanes from 104,
the `What`s at 1128, the table's count at 1384 and its pairs from 1392 (`Low`), the pushes from
1888 (`slots`), the return address at 1936, the stack arguments at 1944, 1952, 1960. The calls
change the frame's `[80, 1384)` (`HitF`). The loop's invariant at `NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_3`
(`Inv j`): rows `0 … j - 1` checked, RBP query `j`'s address, RSI `j`, R13 the rows left. The exit
(`exit_true`, `exit_false`) returns the outcome in AL.
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfFinalLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(1888, .rbx), (1896, .r12), (1904, .r13), (1912, .r14), (1920, .r15), (1928, .rbp)]

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 1936

/-- Between the prologue and the epilogue, RSP at offset `o`. -/
abbrev FR (m0 : MachineData) (o : Nat) (m : MachineData) : Prop :=
  EachRow.Fr m0 1936 eachRowFinalStack slots (fun _ ↦ False) o m

/-- What the loop's calls change. -/
abbrev HitF (m0 : MachineData) : BitVec 64 → Prop :=
  EachRow.Hit m0 1936 eachRowFinalStack 80 1384

/-- The queries. -/
abbrev qsOf (m0 : MachineData) : Array UInt64 := (eachRowArgs m0).1

/-- The folded scalars. -/
abbrev foldedOf (m0 : MachineData) : Array EW := slice m0 (stackArg m0 1) (stackArg m0 2)

/-- Row `i`'s check. -/
abbrev okOf (m0 : MachineData) (q : UInt64) (row : Array UInt64) : Bool :=
  EachRow.rowOk (reg m0 .rdi).toNat (reg m0 .r8).toNat (eachRowArgs m0).2 (foldedOf m0) q row

/-- The table `subspace_table` computes. -/
abbrev tableOf (m0 : MachineData) : Array (UInt64 × UInt64) := subspaceTable (reg m0 .r8).toNat

/-- The queries' end. -/
abbrev qEnd (m0 : MachineData) : BitVec 64 :=
  reg m0 .rsi + BitVec.ofNat 64 (8 * (reg m0 .rdx).toNat)

/-- **The frame's locals** kept by the loop. -/
structure Low (m0 : MachineData) (d : DataMem) : Prop where
  w16 : WordAt d (fb m0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (reg m0 .rcx))
  w24 : WordAt d (fb m0 + BitVec.ofNat 64 24) (UInt64.ofBitVec (qEnd m0))
  w32 : WordAt d (fb m0 + BitVec.ofNat 64 32) (UInt64.ofBitVec (reg m0 .r9))
  w40 : WordAt d (fb m0 + BitVec.ofNat 64 40) (UInt64.ofBitVec (reg m0 .rdi))
  tab : BufPairsAt d (fb m0 + BitVec.ofNat 64 1384) rootCap (tableOf m0).toList

/-- **The loop's invariant** at `NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_3`, before row `j`. -/
structure Inv (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  low : Low m0 m.dmem
  hj : j < rows.size
  hjq : j ≤ (qsOf m0).size
  ok : ∀ i (h1 : i < (qsOf m0).size) (h2 : i < rows.size), i < j →
    okOf m0 (qsOf m0)[i] rows[i] = true
  rbp : reg m .rbp = reg m0 .rsi + BitVec.ofNat 64 (8 * j)
  rsi : reg m .rsi = BitVec.ofNat 64 j
  r13 : reg m .r13 = BitVec.ofNat 64 (rows.size - j)
  r14 : reg m .r14 = reg m0 .rcx
  r12 : reg m .r12 = BitVec.ofNat 64 (tableOf m0).size
  r15 : reg m .r15 = fb m0 + BitVec.ofNat 64 1392
  rbx : reg m .rbx = fb m0 + BitVec.ofNat 64 104

/-- The end: back at the caller with the contract's postcondition. -/
def Done (rows : Array (Array UInt64)) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ EachRowFinalPost rows m0 st.data

end

public section

theorem stack_eq : eachRowFinalStack = 3088 := rfl

theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ (p.1 + 8 ≤ 80 ∨ (1384 ≤ p.1 ∧ p.1 + 8 ≤ 1936)) := by
  decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1936 := by decide

theorem slots_cs : ∀ r, calleeSaved r = true → ∃ p ∈ slots, p.2 = r := by
  intro r hr
  cases r <;> simp_all [calleeSaved, slots]

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

/-- The layout. -/
theorem lay [Labels] (hpre : EachRowFinalPre rows op m0) : EachRow.Lay m0 1936 24 eachRowFinalStack :=
  ⟨hpre.1.1, by decide, by decide, hpre.1.2.1.1, hpre.1.2.1.2⟩

/-- The loader's protected row inputs do not wrap. -/
theorem got_nw [Labels] (hpre : EachRowFinalPre rows op m0) :
    ∀ a ∈ [(reg m0 .rcx, 32), (op, 8 * NativeRustcVm.Sumcheck.openingsWords),
      (reg m0 .rsi, 8 * (reg m0 .rdx).toNat),
      (reg m0 .r9, roundBytes * (stackArg m0 0).toNat),
      (stackArg m0 1, 16 * (stackArg m0 2).toNat), (rspOf m0 + 8#64, 24)],
      NoWrap a.1 a.2 := by
  have ht := (lay hpre).top
  obtain ⟨⟨_, _, _, hr, ho, hq, _, _, hround⟩, _, hc, _⟩ := hpre
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hr.1.2
  · exact ho.1.2
  · exact hq.1.2
  · exact hround.1.2
  · exact hc.1.2
  · unfold NoWrap
    rw [toNat_add_ofNat _ _ (by omega)]
    omega

/-- The frame alone, as an environment. -/
theorem frame_env [Labels] (hpre : EachRowFinalPre rows op m0) {m : MachineData}
    (hfr : FR m0 8 m) (ret : BitVec 64) :
    (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0) ret).WF ∧
      Match (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0) ret) frameS m :=
  ⟨EachRow.envE_wf (lay hpre) le_rfl hfr.kept (fun _ h ↦ by cases h)
      (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, trivial⟩ ⟨hfr.match_rsp, trivial⟩ trivial trivial trivial⟩

/-- A word of the frame from `8`, outside `[lo, hi)`, kept by a step changing memory in `Hit`. -/
theorem keepW {lo hi : Nat} (hl : EachRow.Lay m0 1936 24 eachRowFinalStack) (hlh : lo ≤ hi)
    (hhi : hi ≤ 1936) {d d' : DataMem}
    (hs : SameOutside d d' (EachRow.Hit m0 1936 eachRowFinalStack lo hi)) {o : Nat} {w : UInt64}
    (h8 : 8 ≤ o) (ho : o + 8 ≤ lo ∨ (hi ≤ o ∧ o + 8 ≤ 1968))
    (h : WordAt d (fb m0 + BitVec.ofNat 64 o) w) : WordAt d' (fb m0 + BitVec.ofNat 64 o) w :=
  EachRow.keep_frame hl hlh hhi hs h8 (by rw [NativeRustcVm.length_wordBytes]; omega) h

/-- A callee-saved register kept. -/
theorem sv {m m' : MachineData} (h : Saved m m') (r : Reg64) (hc : calleeSaved r = true) :
    reg m' r = reg m r :=
  h.1 r hc

/-- **The locals kept** by a step changing memory in `Hit … lo hi`, `80 ≤ lo`. -/
theorem Low.keep {lo hi : Nat} {d d' : DataMem} (hl : EachRow.Lay m0 1936 24 eachRowFinalStack)
    (hlh : lo ≤ hi) (hhi : hi ≤ 1384) (hlo : 48 ≤ lo) (h : Low m0 d)
    (hs : SameOutside d d' (EachRow.Hit m0 1936 eachRowFinalStack lo hi)) : Low m0 d' := by
  have kw : ∀ {o : Nat} {w : UInt64}, 8 ≤ o → o + 8 ≤ lo →
      WordAt d (fb m0 + BitVec.ofNat 64 o) w → WordAt d' (fb m0 + BitVec.ofNat 64 o) w :=
    fun h8 ho hw ↦ EachRow.keep_frame hl hlh (by omega) hs h8
      (.inl (by rw [NativeRustcVm.length_wordBytes]; omega)) hw
  obtain ⟨hl', hw, hp⟩ := h.tab
  refine ⟨kw (by decide) (by omega) h.w16, kw (by decide) (by omega) h.w24,
    kw (by decide) (by omega) h.w32, kw (by decide) (by omega) h.w40, hl',
    EachRow.keep_frame hl hlh (by omega) hs (by decide)
      (.inr ⟨by omega, by rw [NativeRustcVm.length_wordBytes]; decide⟩) hw, ?_⟩
  have e : off (fb m0 + BitVec.ofNat 64 1384) 8 = fb m0 + BitVec.ofNat 64 1392 :=
    NativeRustcVm.addr_add_add _ _ _
  rw [e] at hp ⊢
  refine EachRow.keep_frame hl hlh (by omega) hs (by decide) (.inr ⟨by omega, ?_⟩) hp
  rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords]
  have : (tableOf m0).toList.length ≤ 31 := hl'
  omega

/-- **A stack argument** loaded through region 0 in a body. -/
theorem argW [Labels] (hpre : EachRowFinalPre rows op m0) {o : Nat} {m : MachineData} (hfr : FR m0 o m)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} (i : Nat)
    (hi : i < 3) :
    (EachRow.envE m0 m 1936 24 rest vars ret).load 0 (1936 + 8 + 8 * i) 8 = stackArg m0 i :=
  EachRow.load_arg i fun j hj ↦ hfr.args_same (lay hpre) (fun _ _ h ↦ h) _ (by omega)

variable [Host] {k : Nat}

/-- The epilogue's facts, from a body. -/
theorem done_of (hpre : EachRowFinalPre rows op m0) {m : MachineData} (hfr : FR m0 8 m)
    {S : SState} {st : MachineState} {b : Bool}
    (hm : Match (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0) 0) S st.data)
    (hpc : PcOk (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0) 0) (.ret (.load 0 1936 8))
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b20End)) st)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 1936)
    (hrs : ∀ p ∈ slots, S.reg p.2 = some (.load 0 p.1 8))
    (hsp : S.reg .rsp = some (.ptr 0 ((1936 + 8 : Nat) : Int)))
    (hal : boolRet st.data = (okWord b).toNat)
    (hres : finalOk (reg m0 .rdi).toNat (reg m0 .r8).toNat (eachRowArgs m0).2 (foldedOf m0)
      (qsOf m0) rows = b) :
    Done rows m0 st := by
  have hwf := (frame_env hpre hfr 0).1
  obtain ⟨hpc', hrsp, hsv, hso⟩ := EachRow.Fr.exit (lay hpre) hfr hwf hm hpc hmem hrs slots_cs hsp
    fun _ _ h ↦ h
  refine ⟨hpc', hrsp, ?_, fun q hq ↦ hso q fun h ↦ hq (h.elim .inr False.elim), hsv⟩
  show boolRet st.data = _
  rw [hal, hres]

/-- **The exit** at `NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_13`, AL the outcome `b`. -/
theorem exit_at (hp : Placed code k) (hpre : EachRowFinalPre rows op m0) {m : MachineData}
    (hfr : FR m0 8 m) {b : Bool} (hal : boolRet m = (okWord b).toNat)
    (hres : finalOk (reg m0 .rdi).toNat (reg m0 .r8).toNat (eachRowArgs m0).2 (foldedOf m0)
      (qsOf m0) rows = b) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b20Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env hpre hfr 0
  have hk20 : b20.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b20Offset) := b20_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk20 run_b20 hwf (fun _ h ↦ by cases h) hm fun st' hm' hpc' ↦
    .done _ (done_of hpre hfr hm' hpc' (fun _ h ↦ by cases h) (by decide) rfl ?_ hres)
  show (st'.data.regs.get64 .rax).toNat % 256 = _
  rw [hm'.regs .rax _ rfl]
  exact hal

/-- **The exit with outcome `true`**, from `NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_14`. -/
theorem exit_true (hp : Placed code k) (hpre : EachRowFinalPre rows op m0) {m : MachineData}
    (hfr : FR m0 8 m)
    (hres : finalOk (reg m0 .rdi).toNat (reg m0 .r8).toNat (eachRowArgs m0).2 (foldedOf m0)
      (qsOf m0) rows = true) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b18Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env hpre hfr 0
  have hk18 : b18.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b18Offset) := b18_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk18 run_b18 hwf (fun _ h ↦ by cases h) hm fun st hm1 hpc1 ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only [PcOk] at hpc1
  subst hpc1
  rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_13 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b20Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_13_at]
  refine exit_at hp hpre (hfr.ofBlock hwf hm1 rfl (by decide)) ?_ hres
  show (d.regs.get64 .rax).toNat % 256 = 1
  rw [hm1.regs .rax _ rfl]
  exact NativeRustcVmX64.Arrays.merge_one_mod _

/-- **The exit with outcome `false`**, from `NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_12`. -/
theorem exit_false (hp : Placed code k) (hpre : EachRowFinalPre rows op m0) {m : MachineData}
    (hfr : FR m0 8 m)
    (hres : finalOk (reg m0 .rdi).toNat (reg m0 .r8).toNat (eachRowArgs m0).2 (foldedOf m0)
      (qsOf m0) rows = false) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b19Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env hpre hfr 0
  have hk19 : b19.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b19Offset) := b19_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk19 run_b19 hwf (fun _ h ↦ by cases h) hm fun st hm1 hpc1 ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only [PcOk] at hpc1
  subst hpc1
  refine exit_at hp hpre (hfr.ofBlock hwf hm1 rfl (by decide)) ?_ hres
  show (d.regs.get64 .rax).toNat % 256 = 0
  rw [hm1.regs .rax _ rfl]
  rfl

end

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
