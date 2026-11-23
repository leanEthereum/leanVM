module

public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.SharePre

/-!
# `verify_bus_balance`'s claims: what they start from

- `ClaimsMem`: the frame's locals at `b18` (the layouts, the weights, the GKR state, `β`'s limb
  `0`); `ClaimsMem.of_keep`.
- `AtClaims`: the state at `b18` (`k + 271`).
- `ult_ofNat`, `ite_len`, `ite_min`, `bv_of_toNat`: `b18`'s values.
- `rs_call`: `read_scalar` into the frame's `4176`.
- `pc_call`: `push_claim` of a prefix of the point.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- **The frame's locals at `b18`.** -/
structure ClaimsMem (m0 : MachineData) (L : LayoutW) (w pt tv : Array EW) (beta : EW)
    (d : Mem 64) : Prop where
  push : BusLayoutWAt d (loc m0 160) (pushL L)
  pull : BusLayoutWAt d (loc m0 1048) (pullL L)
  count : BusLayoutWAt d (loc m0 1936) (countL L)
  hw : NativeRustcVm.EWsAt d (loc m0 2824) w.toList
  wsz : w.size = 16
  gkr : GkrStateWAt d (loc m0 3080) ⟨tv, pt⟩
  w128 : NativeRustcVm.WordAt d (loc m0 128) beta.c0

/-- `ClaimsMem`'s intervals. -/
abbrev claimsIv : List (Nat × Nat) := [(128, 136), (160, 4144)]

/-- **`ClaimsMem` through what keeps it.** -/
theorem ClaimsMem.of_keep {m0 : MachineData} {L : LayoutW} {w pt tv : Array EW} {beta : EW}
    {d d' : Mem 64} (h : ClaimsMem m0 L w pt tv beta d) (hk : KeepIv claimsIv m0 d d') :
    ClaimsMem m0 L w pt tv beta d' := by
  have i3 : ((160, 4144) : Nat × Nat) ∈ claimsIv := by simp
  have hb : busLayoutBytes = 888 := rfl
  have hs := hk.sameIn i3 (o := 3080) (n := 1064) (by omega) (by omega)
  refine ⟨BusLayoutWAt.of_same h.push (hk.sameIn i3 (by omega) (by rw [hb]; omega)),
    BusLayoutWAt.of_same h.pull (hk.sameIn i3 (by omega) (by rw [hb]; omega)),
    BusLayoutWAt.of_same h.count (hk.sameIn i3 (by omega) (by rw [hb]; omega)),
    NativeRustcVm.Tables.EWsAt.of_same h.hw (hk.sameIn i3 (o := 2824) (n := 256) (by omega)
      (by omega)) (by rw [Array.length_toList, h.wsz]), h.wsz,
    gkrStateWAt_keep h.gkr (R := fun q ↦ d'.get? q ≠ d.get? q)
      (fun q hq ↦ not_not.mp hq) fun q hq h' ↦ ?_,
    NativeRustcVm.Layout.WordAt.of_same h.w128 (hk.sameIn (lo := 128) (hi := 136) (by simp)
      (by omega) (by omega)) le_rfl⟩
  obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists h'
  exact hq (hs j (by rw [gkrStateBytes_eq] at hj; exact hj))

/-- **Element `i`'s words** of `E` elements at the frame's byte `o`. -/
theorem ew_get {m0 : MachineData} {d : Mem 64} {o : Nat} {xs : Array EW}
    (h : NativeRustcVm.EWsAt d (loc m0 o) xs.toList) {i : Nat} (hi : i < xs.size) :
    NativeRustcVm.WordAt d (loc m0 (o + 16 * i)) (xs.getD i 0).c0 ∧
      NativeRustcVm.WordAt d (loc m0 (o + 16 * i + 8)) (xs.getD i 0).c1 := by
  have e := h.getElem (i := i) (by rw [Array.length_toList]; exact hi)
  rw [NativeRustcVm.addr_add_add] at e
  have e2 := NativeRustcVm.ewAt_iff.mp e
  rw [NativeRustcVm.addr_add_add] at e2
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  simpa using e2

/-- **The GKR state's parts**: the tree values' words, the point's length and coordinates. -/
theorem gkr_parts {m0 : MachineData} {d : Mem 64} {tv pt : Array EW}
    (h : GkrStateWAt d (loc m0 3080) ⟨tv, pt⟩) :
    tv.size = 3 ∧ NativeRustcVm.WordAt d (loc m0 3080) (tv.getD 0 0).c0 ∧
      NativeRustcVm.WordAt d (loc m0 3088) (tv.getD 0 0).c1 ∧
      NativeRustcVm.WordAt d (loc m0 3096) (tv.getD 1 0).c0 ∧
      NativeRustcVm.WordAt d (loc m0 3104) (tv.getD 1 0).c1 ∧
      NativeRustcVm.WordAt d (loc m0 3112) (tv.getD 2 0).c0 ∧
      NativeRustcVm.WordAt d (loc m0 3120) (tv.getD 2 0).c1 ∧
      NativeRustcVm.WordAt d (loc m0 3128) pt.size.toUInt64 ∧
      NativeRustcVm.EWsAt d (loc m0 3136) pt.toList ∧ pt.size ≤ 63 := by
  obtain ⟨hs, hv, hl, hw, he⟩ := h
  simp only at hs hv hl hw he
  have g0 := ew_get hv (i := 0) (by omega)
  have g1 := ew_get hv (i := 1) (by omega)
  have g2 := ew_get hv (i := 2) (by omega)
  refine ⟨hs, g0.1, g0.2, g1.1, g1.2, g2.1, g2.2, ?_, ?_, ?_⟩
  · simpa only [off, NativeRustcVm.addr_add_add, Array.length_toList] using hw
  · simpa only [off, NativeRustcVm.addr_add_add] using he
  · simpa [busPointCap] using hl

/-- `x < y` of two numbers. -/
theorem ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    CmpOp.apply .ult .W64 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [CmpOp.apply, Sym.low_W64, ult_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]

/-- A word as a number's bits. -/
theorem bv_of_toNat {x : UInt64} {n : Nat} (h : x.toNat = n) : x.toBitVec = BitVec.ofNat 64 n := by
  have hl : x.toNat < 2 ^ 64 := by rw [← UInt64.toNat_toBitVec]; exact x.toBitVec.isLt
  apply BitVec.eq_of_toNat_eq
  rw [UInt64.toNat_toBitVec, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The point's length as `b18` reads it: below `64`, itself. -/
abbrev lenS : Sym := .ite (.cmp .ult .W64 (.load 0 3128 8) (.lit 64)) (.load 0 3128 8) (.lit 0)

theorem ite_len [Labels] {env : Env} {n : Nat} (hl : env.load 0 3128 8 = BitVec.ofNat 64 n)
    (hn : n < 64) : lenS.eval env = BitVec.ofNat 64 n := by
  simp only [Sym.eval, SBool.eval, hl, ult_ofNat (a := n) (b := 64) (by omega) (by decide),
    decide_eq_true hn, ↓reduceIte]

theorem ite_min [Labels] {env : Env} {x : XReg} {L : Sym} {a n : Nat}
    (hx : env.regs x = BitVec.ofNat 64 a) (hL : L.eval env = BitVec.ofNat 64 n) (ha : a < 2 ^ 64)
    (hn : n < 2 ^ 64) :
    (Sym.ite (.cmp .ult .W64 (.reg x) L) (.reg x) L).eval env = BitVec.ofNat 64 (min a n) := by
  simp only [Sym.eval, SBool.eval, hx, hL, ult_ofNat ha hn]
  by_cases h : a < n
  · simp [h, Nat.min_eq_left (Nat.le_of_lt h)]
  · simp [h, Nat.min_eq_right (by omega : n ≤ a)]

theorem ite_ptr [Labels] {env : Env} {n : Nat} (hl : env.load 0 3128 8 = BitVec.ofNat 64 n)
    (hn : n < 64) :
    (Sym.ite (.cmp .ult .W64 (.load 0 3128 8) (.lit 64)) (.bin .add .W64 (.reg .X21) (.lit 56))
      (.lit 8)).eval env = env.regs .X21 + BitVec.ofNat 64 56 := by
  simp only [Sym.eval, SBool.eval, hl, ult_ofNat (a := n) (b := 64) (by omega) (by decide),
    decide_eq_true hn, ↓reduceIte, BinOp.apply, Sym.low_W64, Sym.ext_W64]

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

omit [Labels] in
/-- **A block's writes in the frame or the claims** are outputs' or the frame's below the
slots. -/
theorem writeOk_cl {m : MachineData} {S : SState}
    (hall : (S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 5392)) ||
      (w.r == 1 && decide (w.off + w.n ≤ 97288))) = true) :
    ∀ w ∈ S.mem, WriteOk (Env.ofMachine m [(base m0 5488, 5488), (m0.regs.X5.toBitVec, 97288)])
      5488 slots (outs m0) w := by
  intro w hw
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · exact .inl ⟨hr, by omega, fun p hp ↦ .inl (by have := (slots_ge p hp).1; omega)⟩
  · refine .inr ⟨by rw [hr]; decide, fun b sz hb ↦ ?_⟩
    rw [hr] at hb
    simp only [Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨hle, fun i hi ↦ .inr (.inr (NativeRustcVm.inRange_add
      (by rw [claimsBytes_eq]; exact hi) (by rw [claimsBytes_eq]; decide)))⟩

/-- **A byte a block wrote in the frame or the claims** is the frame's or the claims'. -/
theorem written_fc (h : VerifyBusBalancePre a s0 L m0) {m : MachineData} {S : SState}
    (hall : (S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 5488)) ||
      (w.r == 1 && decide (w.off + w.n ≤ 97288))) = true) {q : BitVec 64}
    (hq : Written (Env.ofMachine m [(base m0 5488, 5488), (m0.regs.X5.toBitVec, 97288)]) S q) :
    InRange (loc m0 0) 5488 q ∨ InRange m0.regs.X5.toBitVec claimsBytes q := by
  have hS := pre_stack h
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · rw [hr] at hb
    simp only [Env.ofMachine, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    left
    have hN := hS.2.1
    have := N_ge
    have hl := m0.regs.SP.toNat_lt
    have hb0 := base_toNat (m0 := m0) (F := 5488) (by omega)
    rw [show loc m0 0 = base m0 5488 from Bus.add_zero' _, Sym.inRange_iff (by omega)]
    omega
  · rw [hr] at hb
    simp only [Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    right
    have hnw : m0.regs.X5.toBitVec.toNat + claimsBytes ≤ 2 ^ 64 := (pre_cl h).2.1
    rw [claimsBytes_eq] at hnw ⊢
    rw [Sym.inRange_iff (by omega)]
    omega

/-- **At `b18`** (`k + 271`): the GKR walk done, its count root not zero. -/
structure AtClaims (a : DecArea) (s0 : TState) (L : LayoutW) (m0 : MachineData)
    (w pt tv : Array EW) (beta : EW) (s : TState) (m : MachineData) : Prop where
  fr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m
  run : (verifyBusBalance L).run s0 = tailRun L w beta pt tv s
  mem' : ClaimsMem m0 L w pt tv beta m.dmem
  x19 : m.regs.getXReg .X19 = m0.regs.X4
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : (m.regs.getXReg .X21).toBitVec = loc m0 3080
  x22 : m.regs.getXReg .X22 = beta.c1
  x23 : m.regs.getXReg .X23 = m0.regs.X3
  x24 : m.regs.getXReg .X24 = m0.regs.X2
  x25 : m.regs.getXReg .X25 = m0.regs.X0
  x27 : (m.regs.getXReg .X27).toNat = L.logMemory
  x28 : m.regs.getXReg .X28 = m0.regs.X5
  x29 : (m.regs.getXReg .X29).toNat = L.logBytecode
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **`read_scalar(out, t)`** from the frame, the output at `4176`. -/
theorem rs_call (h : VerifyBusBalancePre a s0 L m0)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel ∧ retOf st.data = next)
    (x0 : st.data.regs.X0.toBitVec = loc m0 4176) (x1 : st.data.regs.X1 = m0.regs.X0)
    {s : TState} (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s)
    (cont : ∀ m2, Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m2 →
      OptEWAt m2.dmem (loc m0 4176) ((readScalar.run s).map (·.1)) →
      NextAt m2.dmem m0.regs.X0.toBitVec a (readScalar.run s) →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦
        InRange (stackBelow st.data readScalarStack) readScalarStack q ∨
          InRange (loc m0 4176) 24 q ∨ InRange m0.regs.X0.toBitVec tstateBytes q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have c := ctx h
  have hat := Fr.at_ c hfr (outs_not_rc h)
  refine Fr.callLocal (o := 4176) (n := 24)
    (X := fun q ↦ InRange (loc m0 4176) 24 q ∨ InRange m0.regs.X0.toBitVec tstateBytes q)
    hfr hS.2.1 le_rs keep_callee (slots_lo (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hrs a s) hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [x0, x1] at hq'
      rcases hq' with hq' | hq' | hq'
      · exact .inr (.inl hq')
      · exact .inr (.inr hq')
      · exact .inl hq', hq.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · unfold ReadScalarPre
    rw [x0, x1]
    exact ⟨hfr.stackOk hS rfl le_rs, c.rcAt hat le_rs, hts, c.tstateOk hat le_rs,
      c.outOk hat le_rs (by omega)⟩
  · dsimp only [ReadScalarPost] at hq2
    rw [x0, x1] at hq2
    exact cont m2 hfr2 hq2.1 hq2.2.1 hq2.2.2.2.2.2 hcs2 hs2

/-- **`push_claim(claims, id, point[..j], value)`** from the frame, the point at `3136`. -/
theorem pc_call (h : VerifyBusBalancePre a s0 L m0)
    (hpcl : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel ∧ retOf st.data = next)
    {cs : Array ColumnClaimW} (hcl : ClaimsWAt st.data.dmem m0.regs.X5.toBitVec cs)
    (hcs : cs.size < claimCap) {pt : Array EW}
    (hpt : NativeRustcVm.EWsAt st.data.dmem (loc m0 3136) pt.toList) (hpsz : pt.size ≤ 63)
    {j id : Nat} {v : EW} (hj : j ≤ 30)
    (x0 : st.data.regs.X0 = m0.regs.X5) (x1 : st.data.regs.X1.toNat = id)
    (x2 : st.data.regs.X2 = UInt64.ofBitVec (loc m0 3136))
    (x3 : st.data.regs.X3 = (min j pt.size).toUInt64)
    (x4 : st.data.regs.X4 = v.c0) (x5 : st.data.regs.X5 = v.c1)
    (cont : ∀ m2, Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m2 → m2.regs.X0 = 1 →
      ClaimsWAt m2.dmem m0.regs.X5.toBitVec (cs.push ⟨id, pt.extract 0 j, v⟩) →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦
        InRange m0.regs.X5.toBitVec claimsBytes q ∨
          InRange (stackBelow st.data pushClaimStack) pushClaimStack q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have c := ctx h
  have hat := Fr.at_ c hfr (outs_not_rc h)
  have n3 : (min j pt.size).toUInt64.toNat = min j pt.size :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hcl' := pre_cl h
  refine Fr.callSpec hfr hS.2.1 le_pc keep_callee slots_le (outs_not_frame h) (hpcl cs) hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ by
      rw [x0] at hq'
      rcases hq' with hq' | hq'
      · exact .inr (.inr (.inr hq'))
      · exact .inl hq', hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 ↦ ?_
  · unfold PushClaimPre
    rw [x0]
    refine ⟨hfr.stackOk hS rfl le_pc, hcl, ⟨fun i hi ↦ hfr.kept _ (hcl'.1 i hi), hcl'.2.1⟩,
      c.apart hat le_pc hcl'.2.2.2.2.1, ?_, ?_⟩
    · unfold SliceOk
      rw [x2, x3, n3, UInt64.toBitVec_ofBitVec]
      exact loc_inOk h hfr le_pc (by omega)
    · rw [x2, x3, n3, UInt64.toBitVec_ofBitVec]
      exact (c.apart_of_stack (o := 3136) (k := 16 * min j pt.size) (by omega)
        hcl'.2.2.2.2.1).symm
  · obtain ⟨h1, h2, h3⟩ := hq2
    have hc : cs.size < claimCap ∧ st.data.regs.X3.toNat ≤ pointCap := ⟨hcs, by
      rw [x3, n3]; unfold pointCap; omega⟩
    simp only [hc, and_self, ↓reduceIte] at h1
    have hsl : slice st.data st.data.regs.X2 st.data.regs.X3 = pt.extract 0 j := by
      rw [x2, x3]; exact slice_prefix hpt hpsz j
    have hv : ewArg st.data.regs.X4 st.data.regs.X5 = v := by rw [x4, x5]; rfl
    rw [hsl, hv, x1, x0] at h1
    refine cont m2 hfr2 h1.1 h1.2 h3.2.2 hcs2 ?_
    rw [← x0]
    exact h2

end

end NativeRustcVmArm.Bus.VerifyBusBalance
