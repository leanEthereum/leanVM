module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.Exec
public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Frame
public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Model
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names

/-!
# `each_row` with `next_level`'s closure: frame, invariant, exit (x86-64)

The 1984 bytes below the entry's RSP (`fb`, region 0's base; the body's `X(%rsp)` is region 0's
`X + 8`): `[8]`, `[16]` the query weights' address and count, `[24]` the `Rows`' address, `[32]`
the batched value's address, `[40]` the table's address (1440), `[48]`, `[56]` the high part's count
and address, `[64]` `μ`'s address, `[72]` the table's count, `[80]` the queries' end, `[88]` the
rounds' address, `[96]` the index (`Low`); in an iteration `[104]`, `[112]` the folded row, `[120]`
the rows left; `novel_eval`'s result at 128, the table's `Option` and then the lanes from 152, the
`What`s at 1176, the table's count at 1432 and its pairs from 1440 (`Low`), the pushes from 1936
(`slots`), the return address at 1984, the stack arguments at 1992, 2000. Memory changes in the
stack and the batched value at `bOf` (`FR`). The loop's invariant at `NativeRustcVmX64.Vm.EachRowOfNextLevel.label_5`
(`Inv j`): the batched value the partial sum of `j` rows, R15 query `j`'s address, RBX `j`, RDX
the rows left. The exit (`exit_at`) returns `1` in AL.
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(1936, .rbx), (1944, .r12), (1952, .r13), (1960, .r14), (1968, .r15), (1976, .rbp)]

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 1984

/-- The batched value's address. -/
abbrev bOf (m0 : MachineData) : BitVec 64 := nextEnv m0 3

/-- Between the prologue and the epilogue, RSP at offset `o`. -/
abbrev FR (m0 : MachineData) (o : Nat) (m : MachineData) : Prop :=
  EachRow.Fr m0 1984 eachRowNextStack slots (InRange (bOf m0) 16) o m

/-- The queries. -/
abbrev qsOf (m0 : MachineData) : Array UInt64 := (eachRowArgs m0).1

/-- The high part. -/
abbrev highOf (m0 : MachineData) : Array EW := slice m0 (nextEnv m0 1) (nextEnv m0 2)

/-- The query weights. -/
abbrev qwOf (m0 : MachineData) : Array EW := slice m0 (nextEnv m0 4) (nextEnv m0 5)

/-- The table `subspace_table` computes. -/
abbrev tableOf (m0 : MachineData) : Array (UInt64 × UInt64) := subspaceTable (reg m0 .r8).toNat

/-- The batched value after `j` rows. -/
abbrev parOf (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) : EW :=
  EachRow.nextPartial (reg m0 .rdi).toNat (reg m0 .r8).toNat (eachRowArgs m0).2 (highOf m0)
    (qsOf m0) rows (qwOf m0) j

/-- The queries' end. -/
abbrev qEnd (m0 : MachineData) : BitVec 64 :=
  reg m0 .rsi + BitVec.ofNat 64 (8 * (reg m0 .rdx).toNat)

/-- **The frame's locals** kept by the loop. -/
structure Low (m0 : MachineData) (d : DataMem) : Prop where
  w8 : WordAt d (fb m0 + BitVec.ofNat 64 8) (UInt64.ofBitVec (nextEnv m0 4))
  w16 : WordAt d (fb m0 + BitVec.ofNat 64 16) (UInt64.ofBitVec (nextEnv m0 5))
  w24 : WordAt d (fb m0 + BitVec.ofNat 64 24) (UInt64.ofBitVec (reg m0 .rcx))
  w32 : WordAt d (fb m0 + BitVec.ofNat 64 32) (UInt64.ofBitVec (nextEnv m0 3))
  w40 : WordAt d (fb m0 + BitVec.ofNat 64 40) (UInt64.ofBitVec (fb m0 + BitVec.ofNat 64 1440))
  w48 : WordAt d (fb m0 + BitVec.ofNat 64 48) (UInt64.ofBitVec (nextEnv m0 2))
  w56 : WordAt d (fb m0 + BitVec.ofNat 64 56) (UInt64.ofBitVec (nextEnv m0 1))
  w64 : WordAt d (fb m0 + BitVec.ofNat 64 64) (UInt64.ofBitVec (nextEnv m0 0))
  w72 : WordAt d (fb m0 + BitVec.ofNat 64 72) (UInt64.ofBitVec (BitVec.ofNat 64 (tableOf m0).size))
  w80 : WordAt d (fb m0 + BitVec.ofNat 64 80) (UInt64.ofBitVec (qEnd m0))
  w88 : WordAt d (fb m0 + BitVec.ofNat 64 88) (UInt64.ofBitVec (reg m0 .r9))
  w96 : WordAt d (fb m0 + BitVec.ofNat 64 96) (UInt64.ofBitVec (reg m0 .rdi))
  tab : BufPairsAt d (fb m0 + BitVec.ofNat 64 1432) rootCap (tableOf m0).toList

/-- **The loop's invariant** at `NativeRustcVmX64.Vm.EachRowOfNextLevel.label_5`, before row `j`. -/
structure Inv (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  low : Low m0 m.dmem
  hj : j < rows.size
  hjq : j ≤ (qsOf m0).size
  bat : EWAt m.dmem (bOf m0) (parOf rows m0 j)
  r15 : reg m .r15 = reg m0 .rsi + BitVec.ofNat 64 (8 * j)
  rbx : reg m .rbx = BitVec.ofNat 64 j
  rdx : reg m .rdx = BitVec.ofNat 64 (rows.size - j)
  rdi : reg m .rdi = reg m0 .rcx
  r13 : reg m .r13 = fb m0 + BitVec.ofNat 64 1440
  r14 : reg m .r14 = bOf m0

/-- The end: back at the caller with the contract's postcondition. -/
def Done (rows : Array (Array UInt64)) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ EachRowNextPost rows m0 st.data

/-- The precondition, by name. -/
structure Ctx [Labels] (rows : Array (Array UInt64)) (op : BitVec 64) (m0 : MachineData) : Prop where
  stk : StackOk m0 eachRowNextStack
  args : ArgsOk m0 2
  rowsAt : NativeRustcVm.Sumcheck.RowsAt m0.dmem (reg m0 .rcx) op rows
  rin : WhirIn m0 (reg m0 .rcx) 32 eachRowNextStack
  opin : WhirIn m0 op (8 * NativeRustcVm.Sumcheck.openingsWords) eachRowNextStack
  qin : WhirIn m0 (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) eachRowNextStack
  mu : (reg m0 .r8).toNat ≤ stackCap
  nr : (stackArg m0 0).toNat ≤ roundCap
  rdin : WhirIn m0 (reg m0 .r9) (roundBytes * (stackArg m0 0).toNat) eachRowNextStack
  envin : WhirIn m0 (stackArg m0 1) 48 eachRowNextStack
  muin : WhirIn m0 (nextEnv m0 0) 8 eachRowNextStack
  muw : NativeRustcVm.wordOf m0.dmem (nextEnv m0 0) = .ofBitVec (reg m0 .r8)
  hlen : (nextEnv m0 2).toNat ≤ laneCap
  hin : WhirIn m0 (nextEnv m0 1) (16 * (nextEnv m0 2).toNat) eachRowNextStack
  qwin : WhirIn m0 (nextEnv m0 4) (16 * (nextEnv m0 5).toNat) eachRowNextStack
  bin : WhirIn m0 (bOf m0) 16 eachRowNextStack
  b0 : EWAt m0.dmem (bOf m0) 0
  bargs : Apart (bOf m0) 16 (rspOf m0 + 8#64) 16
  benv : Apart (bOf m0) 16 (stackArg m0 1) 48
  bmu : Apart (bOf m0) 16 (nextEnv m0 0) 8
  brows : Apart (bOf m0) 16 (reg m0 .rcx) 32
  bop : Apart (bOf m0) 16 op (8 * NativeRustcVm.Sumcheck.openingsWords)
  bq : Apart (bOf m0) 16 (reg m0 .rsi) (8 * (reg m0 .rdx).toNat)
  brd : Apart (bOf m0) 16 (reg m0 .r9) (roundBytes * (stackArg m0 0).toNat)
  bh : Apart (bOf m0) 16 (nextEnv m0 1) (16 * (nextEnv m0 2).toNat)
  bqw : Apart (bOf m0) 16 (nextEnv m0 4) (16 * (nextEnv m0 5).toNat)
  got : GotAt m0 eachRowNextStack [(reg m0 .rcx, 32), (op, 8 * NativeRustcVm.Sumcheck.openingsWords),
    (reg m0 .rsi, 8 * (reg m0 .rdx).toNat), (reg m0 .r9, roundBytes * (stackArg m0 0).toNat),
    (stackArg m0 1, 48), (nextEnv m0 0, 8), (nextEnv m0 1, 16 * (nextEnv m0 2).toNat),
    (nextEnv m0 4, 16 * (nextEnv m0 5).toNat), (bOf m0, 16), (rspOf m0 + 8#64, 16)]
    ["memcpy", "memset"]

end

public section

theorem stack_eq : eachRowNextStack = 3136 := rfl

theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ (p.1 + 8 ≤ 104 ∨ (1432 ≤ p.1 ∧ p.1 + 8 ≤ 1984)) := by
  decide

theorem slots_cs : ∀ r, calleeSaved r = true → ∃ p ∈ slots, p.2 = r := by
  intro r hr
  cases r <;> simp_all [calleeSaved, slots]

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

theorem rv [Labels] {env : Env} {S : SState} {m : MachineData} {r : Reg64} {v : Sym}
    (hm : Match env S m) (h : S.reg r = some v) : reg m r = v.eval env :=
  hm.regs r v h

/-- A callee-saved register kept. -/
theorem sv {m m' : MachineData} (h : Saved m m') (r : Reg64) (hc : calleeSaved r = true) :
    reg m' r = reg m r :=
  h.1 r hc

section
variable [Labels]

theorem ctx (hpre : EachRowNextPre rows op m0) : Ctx rows op m0 where
  stk := hpre.1.1
  args := hpre.1.2.1
  rowsAt := hpre.1.2.2.1
  rin := hpre.1.2.2.2.1
  opin := hpre.1.2.2.2.2.1
  qin := hpre.1.2.2.2.2.2.1
  mu := hpre.1.2.2.2.2.2.2.1
  nr := hpre.1.2.2.2.2.2.2.2.1
  rdin := hpre.1.2.2.2.2.2.2.2.2
  envin := hpre.2.1
  muin := hpre.2.2.1
  muw := hpre.2.2.2.1
  hlen := hpre.2.2.2.2.1
  hin := hpre.2.2.2.2.2.1
  qwin := hpre.2.2.2.2.2.2.1
  bin := hpre.2.2.2.2.2.2.2.1
  b0 := hpre.2.2.2.2.2.2.2.2.1
  bargs := hpre.2.2.2.2.2.2.2.2.2.1
  benv := hpre.2.2.2.2.2.2.2.2.2.2.1
  bmu := hpre.2.2.2.2.2.2.2.2.2.2.2.1
  brows := hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  bop := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  bq := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  brd := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  bh := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  bqw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  got := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The layout. -/
theorem lay (c : Ctx rows op m0) : EachRow.Lay m0 1984 16 eachRowNextStack :=
  ⟨c.stk, by decide, by decide, c.args.1, c.args.2⟩

/-- The inputs and batched output protected from the loader slots do not wrap. -/
theorem Ctx.got_nw (c : Ctx rows op m0) :
    ∀ a ∈ [(reg m0 .rcx, 32), (op, 8 * NativeRustcVm.Sumcheck.openingsWords),
      (reg m0 .rsi, 8 * (reg m0 .rdx).toNat), (reg m0 .r9, roundBytes * (stackArg m0 0).toNat),
      (stackArg m0 1, 48), (nextEnv m0 0, 8), (nextEnv m0 1, 16 * (nextEnv m0 2).toNat),
      (nextEnv m0 4, 16 * (nextEnv m0 5).toNat), (bOf m0, 16), (rspOf m0 + 8#64, 16)],
      NoWrap a.1 a.2 := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c.rin.1.2
  · exact c.opin.1.2
  · exact c.qin.1.2
  · exact c.rdin.1.2
  · exact c.envin.1.2
  · exact c.muin.1.2
  · exact c.hin.1.2
  · exact c.qwin.1.2
  · exact c.bin.1.2
  · have ht := (lay c).top
    unfold NoWrap
    rw [toNat_add_ofNat _ _ (by omega)]
    omega

/-- The batched value is not in the stack, nor in region 0. -/
theorem notB (c : Ctx rows op m0) {o : Nat} (ho : o < 2008) :
    ¬InRange (bOf m0) 16 (fb m0 + BitVec.ofNat 64 o) := by
  have hl := lay c
  have hb := c.bin
  have hS : 3136 ≤ (rspOf m0).toNat := hl.sp
  have := hl.top; have := c.args.2
  have e := hl.addr (o := o) (by omega)
  have hba := c.bargs
  unfold Apart at hba
  rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)] at hba
  have := hb.2
  unfold OffStack Apart at this
  rw [hl.baseN, stack_eq] at this
  rw [Sym.inRange_iff hb.1.2, e]
  omega

/-- An input apart from the batched value: no byte of it is an output. -/
theorem notB_in (c : Ctx rows op m0) {a : BitVec 64} {n : Nat} (hin : WhirIn m0 a n eachRowNextStack)
    (hap : Apart (bOf m0) 16 a n) : ∀ i < n, ¬InRange (bOf m0) 16 (a + BitVec.ofNat 64 i) :=
  fun _ hi ↦ NativeRustcVmX64.Arrays.not_inRange_of_apart (NativeRustcVmX64.Arrays.apart_symm hap)
    hin.1.2 c.bin.1.2 hi

/-- A frame word kept by a change in the batched value. -/
theorem keepWB (c : Ctx rows op m0) {d d' : DataMem} (hs : SameOutside d d' (InRange (bOf m0) 16))
    {o : Nat} {w : UInt64} (ho : o + 8 ≤ 2008) (h : WordAt d (fb m0 + BitVec.ofNat 64 o) w) :
    WordAt d' (fb m0 + BitVec.ofNat 64 o) w :=
  EachRow.keep_frameR hs (fun i hi ↦ notB c (by rw [NativeRustcVm.length_wordBytes] at hi; omega))
    h

/-- The frame alone, as an environment. -/
theorem frame_env (c : Ctx rows op m0) {m : MachineData} (hfr : FR m0 8 m)
    (ret : BitVec 64) :
    (EachRow.envE m0 m 1984 16 [] (fun _ ↦ 0) ret).WF ∧
      Match (EachRow.envE m0 m 1984 16 [] (fun _ ↦ 0) ret) frameS m :=
  ⟨EachRow.envE_wf (lay c) le_rfl hfr.kept (fun _ h ↦ by cases h) (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, trivial⟩ ⟨hfr.match_rsp, trivial⟩ trivial trivial trivial⟩

/-- An environment with one input region, region 0 without the arguments. -/
theorem env1 (c : Ctx rows op m0) {m : MachineData} {o : Nat} (hfr : FR m0 o m)
    {a : BitVec 64} {n : Nat} (hin : WhirIn m0 a n eachRowNextStack) (ret : BitVec 64) :
    (EachRow.envE m0 m 1984 0 [(a, n)] (fun _ ↦ 0) ret).WF :=
  EachRow.envE_wf (lay c) (Nat.zero_le _) hfr.kept
    (by
      simp only [List.mem_singleton]
      rintro x rfl
      exact ⟨fun i hi ↦ hfr.kept _ (hin.1.1 i hi), hin.1.2⟩)
    (List.pairwise_pair.mpr ((lay c).apart0 hin.2))

omit [Labels] in
/-- **The locals kept** by a change outside them. -/
theorem Low.keepR {R : BitVec 64 → Prop} {d d' : DataMem} (h : Low m0 d)
    (hs : SameOutside d d' R)
    (hR : ∀ o, 8 ≤ o → o < 104 ∨ (1432 ≤ o ∧ o < 1936) → ¬R (fb m0 + BitVec.ofNat 64 o)) :
    Low m0 d' := by
  have kw : ∀ {o : Nat} {w : UInt64}, 8 ≤ o → o + 8 ≤ 104 →
      WordAt d (fb m0 + BitVec.ofNat 64 o) w → WordAt d' (fb m0 + BitVec.ofNat 64 o) w :=
    fun h8 ho hw ↦ EachRow.keep_frameR hs (fun i hi ↦ hR _ (by omega)
      (by rw [NativeRustcVm.length_wordBytes] at hi; omega)) hw
  obtain ⟨hl', hw, hp⟩ := h.tab
  refine ⟨kw (by decide) (by decide) h.w8, kw (by decide) (by decide) h.w16,
    kw (by decide) (by decide) h.w24, kw (by decide) (by decide) h.w32,
    kw (by decide) (by decide) h.w40, kw (by decide) (by decide) h.w48,
    kw (by decide) (by decide) h.w56, kw (by decide) (by decide) h.w64,
    kw (by decide) (by decide) h.w72, kw (by decide) (by decide) h.w80,
    kw (by decide) (by decide) h.w88, kw (by decide) (by decide) h.w96, hl',
    EachRow.keep_frameR hs (fun i hi ↦ hR _ (by omega)
      (by rw [NativeRustcVm.length_wordBytes] at hi; omega)) hw, ?_⟩
  have e : off (fb m0 + BitVec.ofNat 64 1432) 8 = fb m0 + BitVec.ofNat 64 1440 :=
    NativeRustcVm.addr_add_add _ _ _
  rw [e] at hp ⊢
  have : (tableOf m0).toList.length ≤ 31 := hl'
  refine EachRow.keep_frameR hs (fun i hi ↦ hR _ (by omega) ?_) hp
  rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords] at hi
  omega

/-- `Hit … lo hi` for `104 ≤ lo`, `hi ≤ 1432` misses the locals. -/
theorem hitR (c : Ctx rows op m0) {lo hi : Nat} (hlh : lo ≤ hi) (hlo : 104 ≤ lo) (hhi : hi ≤ 1432) :
    ∀ o, 8 ≤ o → o < 104 ∨ (1432 ≤ o ∧ o < 1936) →
      ¬EachRow.Hit m0 1984 eachRowNextStack lo hi (fb m0 + BitVec.ofNat 64 o) :=
  fun _ h8 ho ↦ (lay c).not_hit hlh (by omega) h8 (by omega)

/-- `InRange (bOf m0) 16` misses the locals. -/
theorem bR (c : Ctx rows op m0) :
    ∀ o, 8 ≤ o → o < 104 ∨ (1432 ≤ o ∧ o < 1936) →
      ¬InRange (bOf m0) 16 (fb m0 + BitVec.ofNat 64 o) :=
  fun _ _ ho ↦ notB c (by omega)

/-- The batched value kept by a step changing memory in `Hit`. -/
theorem bat_hit (c : Ctx rows op m0) {lo hi : Nat} (hlh : lo ≤ hi) (hhi : hi ≤ 1984)
    {d d' : DataMem} (hs : SameOutside d d' (EachRow.Hit m0 1984 eachRowNextStack lo hi)) {x : EW}
    (h : EWAt d (bOf m0) x) : EWAt d' (bOf m0) x :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi' hq ↦ by
    have hl := lay c
    have hst := hl.hit_stack hlh hhi hq
    rw [NativeRustcVm.length_ewBytes] at hi'
    have := c.bin.2
    exact NativeRustcVmX64.Arrays.not_inRange_of_apart
      (by unfold OffStack Apart at this; unfold Apart; omega) c.bin.1.2
      (by have := hl.sp; have := (rspOf m0).isLt; unfold NoWrap; rw [hl.baseN]; omega) hi' hst

/-- **A stack argument** loaded through region 0 in a body. -/
theorem argW (c : Ctx rows op m0) {o : Nat} {m : MachineData} (hfr : FR m0 o m)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} (i : Nat)
    (hi : i < 2) :
    (EachRow.envE m0 m 1984 16 rest vars ret).load 0 (1984 + 8 + 8 * i) 8 = stackArg m0 i :=
  EachRow.load_arg i fun j hj ↦ hfr.args_same (lay c) (fun q hq h ↦ by
    have := c.bargs
    have := c.bin.1.2
    have := c.args.2
    have hq' : q < 16 := hq
    rw [Sym.inRange_iff c.bin.1.2] at h
    unfold Apart at *
    rw [toNat_add_ofNat _ _ (by rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by have := (rspOf m0).isLt; omega)]; omega),
      BitVec.toNat_add, show (8#64).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by have := (rspOf m0).isLt; omega)] at h
    rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (by have := (rspOf m0).isLt; omega)] at *
    omega) _ (by omega)

end

variable [Host] {k : Nat}

/-- **The exit** at `NativeRustcVmX64.Vm.EachRowOfNextLevel.label_15`, AL `1`, the batched value `batchedOf`. -/
theorem exit_at (hp : Placed code k) (c : Ctx rows op m0) {m : MachineData}
    (hfr : FR m0 8 m) (hal : boolRet m = (okWord true).toNat)
    (hb : EWAt m.dmem (bOf m0) (batchedOf (reg m0 .rdi).toNat (reg m0 .r8).toNat
      (eachRowArgs m0).2 (highOf m0) (eachRowArgs m0).1 rows (qwOf m0))) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b26Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env c hfr 0
  have hk26 : b26.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b26Offset) := b26_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk26 run_b26 hwf (fun _ h ↦ by cases h) hm fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hpc'', hrsp, hsv, hso⟩ := EachRow.Fr.exit (lay c) hfr hwf hm' hpc'
    (fun _ h ↦ by cases h) (by decide) slots_cs rfl fun j hj h ↦ by
      have := c.bin
      have hs := this.2
      unfold OffStack Apart at hs
      rw [(lay c).baseN] at hs
      rw [Sym.inRange_iff this.1.2, toNat_add_ofNat _ _ (by have := (lay c).ok.2.1; omega)] at h
      omega
  have hd : st'.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  refine ⟨hpc'', hrsp, ?_, by rw [hd]; exact hb, fun q hq ↦ hso q fun h ↦ hq (h.elim .inr
    fun h' ↦ .inl ⟨_, List.mem_singleton_self _, h'⟩), hsv⟩
  show (st'.data.regs.get64 .rax).toNat % 256 = _
  rw [hm'.regs .rax _ rfl]
  exact hal

/-- **The exit** from `NativeRustcVmX64.Vm.EachRowOfNextLevel.label_17`. -/
theorem exit_17 (hp : Placed code k) (c : Ctx rows op m0) {m : MachineData}
    (hfr : FR m0 8 m)
    (hb : EWAt m.dmem (bOf m0) (batchedOf (reg m0 .rdi).toNat (reg m0 .r8).toNat
      (eachRowArgs m0).2 (highOf m0) (eachRowArgs m0).1 rows (qwOf m0))) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b27Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env c hfr 0
  have hk27 : b27.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b27Offset) := b27_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk27 run_b27 hwf (fun _ h ↦ by cases h) hm fun st hm1 hpc1 ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only [PcOk] at hpc1
  subst hpc1
  rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_15 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b26Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_15_at]
  have hd : d.dmem = m.dmem := hm1.dmem_eq hwf rfl
  refine exit_at hp c (hfr.ofBlock hwf hm1 rfl (by decide)) ?_ (by rw [hd]; exact hb)
  show (d.regs.get64 .rax).toNat % 256 = 1
  rw [hm1.regs .rax _ rfl]
  exact NativeRustcVmX64.Arrays.merge_one_mod _

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
