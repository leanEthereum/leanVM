module

public import NativeRustcVmArm.Whir.NextLevel.Ops
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Layout.RepLemmas

/-!
# `next_level`: what the rows' batching needs

`H24`: the state at `b24`, the batched value at the frame's `8080`. Frame offsets (`loc_off`,
`loc_add`); frame ranges apart from each other (`apart_ll`), from the inputs apart from the stack
(`apart_lx`, `apart_xf`) and from the `WhirW` (`apart_lp`); a frame slice for a callee
(`locSlice`); the closure's words (`nextEnv_of`); the rows moved (`rowsAt_move`); the rounds read
back (`roundsOf_of_roundsAt`).
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel
open NativeRustcVm.Sumcheck (RowsAt openingsWords)

@[expose] public section

/-- At `b24`: the batched value `bt` at `8080`, the query weights' address (X22) and count
(X21). -/
structure H24 [Labels] (a : DecArea) (level : Whir.Level) (m0 : MachineData) (xs ood : Array EW)
    (v lam : EW) (qs : Array UInt64) (bt : EW) (s9 : TState) (st : MachineData) : Prop where
  fr : NFr m0 st
  x19 : st.regs.X19 = m0.regs.X6
  x21 : st.regs.X21 = qs.size.toUInt64
  x22 : st.regs.X22.toBitVec = loc m0 688
  x23 : st.regs.X23.toBitVec = loc m0 200
  x25 : st.regs.X25 = v.c1
  x27 : st.regs.X27 = qs.size.toUInt64
  x29 : st.regs.X29.toBitVec = pA m0 + BitVec.ofNat 64 61360
  facts : Facts m0 st.dmem (F19 m0 xs ood v lam qs.size)
  pw : NativeRustcVm.EWsAt st.dmem (loc m0 688) (powers lam qs.size).toList
  bt : NativeRustcVm.EWAt st.dmem (loc m0 8080) bt
  size : xs.size = level.fold
  osize : ood.size = m0.regs.X5.toNat
  qsz : qs.size ≤ queryCap
  qbuf : NativeRustcVm.BufWordsAt st.dmem (qA m0) queryCap qs.toList
  ts : TStateAt st.dmem (tA m0) a s9

end

public section

theorem tob (x : BitVec 64) : (UInt64.ofBitVec x).toBitVec = x := rfl

theorem loc_off (m0 : MachineData) (o i : Nat) : off (loc m0 o) i = loc m0 (o + i) := by
  show _ + _ + _ = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem loc_add (m0 : MachineData) (o i : Nat) :
    loc m0 o + BitVec.ofNat 64 i = loc m0 (o + i) :=
  loc_off m0 o i

/-- The closure's word `i`. -/
theorem nextEnv_of {m m0 : MachineData} (h7 : m.regs.X7.toBitVec = loc m0 4368) {i : Nat}
    {u : UInt64} (hw : NativeRustcVm.WordAt m.dmem (loc m0 (4368 + 8 * i)) u) :
    nextEnv m i = u := by
  unfold nextEnv
  rw [h7, loc_add]
  exact NativeRustcVm.wordOf_of_wordAt hw

theorem roundsOf_succ (d : Mem 64) (p : BitVec 64) (n : Nat) :
    roundsOf d p (n + 1) =
      ⟨NativeRustcVm.ewOf d p, NativeRustcVm.ewOf d (p + BitVec.ofNat 64 16)⟩ ::
      roundsOf d (p + BitVec.ofNat 64 32) n := by
  unfold roundsOf
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ ↦ ?_⟩
  simp only [Function.comp, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 4 <;> omega

/-- The rounds read back. -/
theorem roundsOf_of_roundsAt {d : Mem 64} {p : BitVec 64} {rs : List FoldRoundW}
    (h : RoundsAt d p rs) : roundsOf d p rs.length = rs := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih =>
    unfold RoundsAt at h
    rw [show roundEWs (r :: rs) = r.alpha :: r.beta :: roundEWs rs from rfl, ewsAt_cons,
      ewsAt_cons, off_off] at h
    obtain ⟨ha, hb, hr⟩ := h
    rw [List.length_cons, roundsOf_succ, NativeRustcVm.ewOf_of_ewAt ha,
      show p + BitVec.ofNat 64 16 = off p 16 from rfl, NativeRustcVm.ewOf_of_ewAt hb,
      show p + BitVec.ofNat 64 32 = off p (16 + 16) from rfl, ih hr]

section
open LeanVM.Protocol.Compile

/-- **The rows moved**: their header copied to `r'`, their openings kept. -/
theorem rowsAt_move {d d' : Mem 64} {r r' p : BitVec 64} {rows : Array (Array UInt64)}
    (h : RowsAt d r p rows)
    (hh : ∀ w0 w1 w2 w3 : UInt64, NativeRustcVm.WordsAt d r [w0, w1, w2, w3] →
      NativeRustcVm.WordsAt d' r' [w0, w1, w2, w3])
    (ho : NativeRustcVm.Layout.Same d d' p (8 * openingsWords)) : RowsAt d' r' p rows := by
  obtain ⟨hp0, hsz, w, hw, hhdr, hrow⟩ := h
  refine ⟨hp0, hsz, w, hw, hh _ _ _ _ hhdr,
    fun j hj ↦ ⟨(hrow j hj).1, bytesAt_congr (hrow j hj).2 fun i hi ↦ ?_⟩⟩
  rw [off, NativeRustcVm.addr_add_add]
  refine ho _ ?_
  rw [NativeRustcVm.length_wordsBytes, Array.length_toList, (hrow j hj).1] at hi
  have e1 : wireMaxQueries = 256 := rfl
  have e2 : wireMaxLeafWords = 64 := rfl
  have e3 : NativeVm.openingWords = 193 := rfl
  have e4 : openingsWords = 49408 := rfl
  simp only [e1, e2, e3, e4] at hsz hw hj hi ⊢
  omega

end

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

/-- Frame ranges apart. -/
theorem apart_ll (h : NextLevelPre a s level w rounds m0) {o n o' n' : Nat}
    (h1 : o + n ≤ 8192) (h2 : o' + n' ≤ 8192) (hd : o + n ≤ o' ∨ o' + n' ≤ o) :
    Apart (loc m0 o) n (loc m0 o') n' := by
  unfold Apart
  rw [loc_toNat (hN8 h) (by omega), loc_toNat (hN8 h) (by omega)]
  omega

theorem stk_nat (h : NextLevelPre a s level w rounds m0) :
    (stackBelow m0 nextLevelStack).toNat = m0.regs.SP.toNat - 11424 :=
  base_nat (by rw [stack_eq]; exact (geo h).hN)

/-- A frame range apart from what is apart from the entry's stack. -/
theorem apart_lx (h : NextLevelPre a s level w rounds m0) {x : BitVec 64} {n o k : Nat}
    (hx : Apart x n (stackBelow m0 nextLevelStack) nextLevelStack) (hok : o + k ≤ 8192) :
    Apart (loc m0 o) k x n := by
  have g := geo h
  unfold Apart at hx ⊢
  rw [stk_nat h, stack_eq] at hx
  rw [loc_toNat (hN8 h) (by omega)]
  have := g.hN
  omega

/-- What is apart from the entry's stack is apart from the frame. -/
theorem apart_xf (h : NextLevelPre a s level w rounds m0) {x : BitVec 64} {n : Nat}
    (hx : Apart x n (stackBelow m0 nextLevelStack) nextLevelStack) :
    Apart x n (base m0 8192) 8192 := by
  have := NativeRustcVm.Apart.symm (apart_lx h hx (o := 0) (k := 8192) le_rfl)
  rwa [show loc m0 0 = base m0 8192 from BitVec.add_zero _] at this

/-- A frame range apart from bytes of the `WhirW`. -/
theorem apart_lp (h : NextLevelPre a s level w rounds m0) {o k j n : Nat} (hok : o + k ≤ 8192)
    (hj : j + n ≤ 63200) (hj' : j < 63200) : Apart (loc m0 o) k (pA m0 + BitVec.ofNat 64 j) n := by
  have g := geo h
  unfold Apart
  rw [loc_toNat (hN8 h) (by omega), toNat_off' (by have := g.pW; omega)]
  have := g.pS; have := g.hN
  omega

/-- A frame slice for a callee. -/
theorem locSlice (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st)
    {N' : Nat} (hle : 8192 + N' ≤ nextLevelStack) {o : Nat} {n : UInt64}
    (hon : o + 16 * n.toNat ≤ 8192) : SliceOk st (UInt64.ofBitVec (loc m0 o)) n N' :=
  locIn h hf hle hon

end

end

end NativeRustcVmArm.Whir.NextLevel
