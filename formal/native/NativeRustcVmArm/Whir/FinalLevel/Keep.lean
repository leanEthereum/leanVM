module

public import NativeRustcVmArm.Whir.FinalLevel.State
public import NativeRustcVmArm.Whir.WhirLevels.Calls

/-!
# `final_level`: the `WhirW`'s bytes across the calls

A callee's stack and the frame's bytes are in the entry's stack (`Ctx.in_stack`); bytes of the
`WhirW` are kept by a call writing those and the `TState` (`Ctx.w_same`).
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters

public section

theorem loc_off (m0 : MachineData) (o i : Nat) : off (loc m0 o) i = loc m0 (o + i) := by
  show _ + _ + _ = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ite_ult [Labels] {env : Env} {x y z : Sym} {n : Nat} (hx : (x.eval env).toNat < n)
    (hn : n < 2 ^ 64) : (Sym.ite (.cmp .ult .W64 x (.lit n)) y z).eval env = y.eval env := by
  sym_simp
  have hc : (x.eval env).ult (BitVec.ofNat 64 n) = true := by
    rw [bv_ult_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    exact decide_eq_true hx
  simp only [hc, ↓reduceIte]

theorem mu_le {m0 : MachineData} {f : Nat} (h : 2 ^ mu m0 + f ≤ 64) : mu m0 ≤ 6 := by
  by_contra hc
  have := Nat.pow_le_pow_right (n := 2) (by decide) (show 7 ≤ mu m0 by omega)
  have : (2 : Nat) ^ 7 = 128 := rfl
  omega

/-- An input's first `n` bytes. -/
theorem whirIn_pre {m : MachineData} {x : BitVec 64} {N n S : Nat} (h : WhirIn m x N S)
    (hn : n ≤ N) : WhirIn m x n S := by
  have := WhirIn.sub h (o := 0) (n := n) (by omega)
  rwa [show x + BitVec.ofNat 64 0 = x from BitVec.add_zero x] at this

variable [Labels] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s0 level ba b w rounds m0)
include c

/-- A callee's stack and the frame's bytes are in the entry's stack. -/
theorem in_stack {st : MachineData} (hf : FFr m0 st) {N' : Nat}
    (hle : 2672 + N' ≤ finalLevelStack) {lo n : Nat} (hln : lo + n ≤ 2672) {q : BitVec 64}
    (h : InRange (stackBelow st N') N' q ∨ InRange (loc m0 lo) n q) :
    InRange (stackBelow m0 finalLevelStack) finalLevelStack q := by
  have hN := c.hN'
  have hN2 := c.hN
  have hsp := m0.regs.SP.toNat_lt
  have hS : (stackBelow m0 finalLevelStack).toNat = m0.regs.SP.toNat - finalLevelStack :=
    NativeRustcVm.toNat_sub_ofNat hN2
  refine (Sym.inRange_iff (x := stackBelow m0 finalLevelStack) (by rw [hS]; omega)).mpr ?_
  rw [hS]
  rcases h with h | h
  · have hb := base_toNat (m0 := m0) (F := 2672 + N') (by omega)
    rw [stackBelow_eq hf.sp (N' := N') (by omega)] at h
    rw [Sym.inRange_iff (by rw [hb]; omega), hb] at h
    omega
  · rw [Sym.inRange_iff (by rw [c.loc_nat (by omega)]; omega), c.loc_nat (by omega)] at h
    omega

/-- **Bytes of the `WhirW` kept** by a call writing its stack, the frame's bytes `[lo, lo + n)`
and the `TState`. -/
theorem w_same {st : MachineData} (hf : FFr m0 st) {N' : Nat}
    (hle : 2672 + N' ≤ finalLevelStack) {d' : Mem 64} {lo n : Nat} (hln : lo + n ≤ 2672)
    (hs : SameOutside st.dmem d' fun q ↦
      InRange (stackBelow st N') N' q ∨ InRange (loc m0 lo) n q ∨ InRange (tA m0) tstateBytes q)
    {o len : Nat} (hol : o + len ≤ whirBytes) :
    NativeRustcVm.Layout.Same st.dmem d' (pA m0 + BitVec.ofNat 64 o) len := by
  have hx := WhirLevels.whirIn_sub c.pIn hol
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ ?_
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add hx.2 hx.1.2 (base_noWrap c.hN) hj
      (c.in_stack hf hle hln (.inl hq))
  · exact NativeRustcVm.Apart.not_inRange_add hx.2 hx.1.2 (base_noWrap c.hN) hj
      (c.in_stack hf hle hln (.inr hq))
  · exact NativeRustcVm.Apart.not_inRange_add (WhirLevels.apart_sub c.pout.1.2.2.1 c.pnw hol)
      hx.1.2 c.tnw hj hq

/-- The entry's stack. -/
abbrev Stk (m0 : MachineData) : BitVec 64 → Prop :=
  InRange (stackBelow m0 finalLevelStack) finalLevelStack

/-- A block writing the frame alone writes the entry's stack. -/
theorem blk_stk {st st' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (fenv m0 st rs) S st') (hwf : (fenv m0 st rs).WF)
    (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 2672) : SameOutside st.dmem st'.dmem (Stk m0) :=
  NativeRustcVm.SameOutside.mono (hm.sameOutside hwf) fun _ hq ↦
    frame_sub c.hN (by rw [stack_eq]; decide) (written_r0 hwf rfl hS hq)

/-- A call writing its stack and the frame's bytes `[lo, lo + n)` writes the entry's stack. -/
theorem call_stk {st : MachineData} (hf : FFr m0 st) {N' : Nat}
    (hle : 2672 + N' ≤ finalLevelStack) {d' : Mem 64} {lo n : Nat} (hln : lo + n ≤ 2672)
    (hs : SameOutside st.dmem d' fun q ↦
      InRange (stackBelow st N') N' q ∨ InRange (loc m0 lo) n q) :
    SameOutside st.dmem d' (Stk m0) :=
  NativeRustcVm.SameOutside.mono hs fun _ h ↦ c.in_stack hf hle hln h

/-- An input's bytes kept when only the entry's stack changes. -/
theorem same_in {d d' : Mem 64} (hs : SameOutside d d' (Stk m0)) {x : BitVec 64} {n : Nat}
    (h : WhirIn m0 x n finalLevelStack) : NativeRustcVm.Layout.Same d d' x n :=
  NativeRustcVm.Layout.Same.of_sameOutside hs fun _ hj hq ↦
    NativeRustcVm.Apart.not_inRange_add h.2 h.1.2 (base_noWrap c.hN) hj hq

/-- The `TState` kept when only the entry's stack changes. -/
theorem ts_stk {d d' : Mem 64} (hk : Keeps d d') (hs : SameOutside d d' (Stk m0)) {s : TState}
    (hts : TStateAt d (tA m0) a s) : TStateAt d' (tA m0) a s :=
  hts.frame hk (fun _ hq ↦ ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange c.tok.1 c.tnw
    (base_noWrap c.hN) ht hq, fun hd ↦ NativeRustcVm.Apart.not_inRange c.tok.2.1
    c.ts0.footprint.2.1.2 (base_noWrap c.hN) hd hq⟩) hs

/-- The decoded area as an input. -/
theorem decIn : WhirIn m0 a.words (8 * a.len) finalLevelStack :=
  ⟨⟨c.ts0.footprint.2.1.1, c.ts0.footprint.2.1.2⟩, c.tok.2.1⟩

end Ctx

section
open NativeRustcVm.Sumcheck LeanVM.Protocol.Compile

omit [Labels] in
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
  have : wireMaxQueries = 256 := rfl
  have : wireMaxLeafWords = 64 := rfl
  have : NativeVm.openingWords = 193 := rfl
  have : openingsWords = 49408 := rfl
  have hj' : j < 256 := by omega
  show _ < 8 * 49408
  nlinarith

end

end

end NativeRustcVmArm.Whir.FinalLevel
