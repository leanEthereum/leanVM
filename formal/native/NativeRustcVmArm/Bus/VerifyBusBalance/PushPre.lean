module

public import NativeRustcVmArm.Bus.VerifyBusBalance.Pull
public import NativeRustcVmArm.Bus.VerifyBusBalance.Keep

/-!
# `verify_bus_balance`'s push side: what it starts from

- `PushMem`: the frame's locals at `b37` (the three layouts, the weights, the tree's values, the
  point, the memory's scalars, the final counters, `β`'s limb `0`, the share); `PushMem.of_keep`.
- `EnvW`: the closure's environment at `5264`; `EnvW.of_keep`.
- `AtPush`: the state at `b37` (`k + 502`).
- `mask_toNat`: `!(-1 << x)` is `2^x - 1`.
- `forms0_at`, `fits_forms0`: the emptied forms.
- `match_frF`, `writeOk_bus`, `written_fb`: `b38`'s start state and writes.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- **The frame's locals at `b37`.** -/
structure PushMem (m0 : MachineData) (L : LayoutW) (w pt tv mem : Array EW)
    (beta mf bf share : EW) (d : Mem 64) : Prop where
  push : BusLayoutWAt d (loc m0 160) (pushL L)
  pull : BusLayoutWAt d (loc m0 1048) (pullL L)
  count : BusLayoutWAt d (loc m0 1936) (countL L)
  hw : NativeRustcVm.EWsAt d (loc m0 2824) w.toList
  wsz : w.size = 16
  t0a : NativeRustcVm.WordAt d (loc m0 3080) (tv.getD 0 0).c0
  t0b : NativeRustcVm.WordAt d (loc m0 3088) (tv.getD 0 0).c1
  t1a : NativeRustcVm.WordAt d (loc m0 3096) (tv.getD 1 0).c0
  t1b : NativeRustcVm.WordAt d (loc m0 3104) (tv.getD 1 0).c1
  t2a : NativeRustcVm.WordAt d (loc m0 3112) (tv.getD 2 0).c0
  t2b : NativeRustcVm.WordAt d (loc m0 3120) (tv.getD 2 0).c1
  hpt : NativeRustcVm.EWsAt d (loc m0 3136) pt.toList
  psz : pt.size ≤ 63
  hmem : NativeRustcVm.EWsAt d (loc m0 4144) mem.toList
  msz : mem.size = 2
  w88 : NativeRustcVm.WordAt d (loc m0 88) bf.c1
  w96 : NativeRustcVm.WordAt d (loc m0 96) bf.c0
  w104 : NativeRustcVm.WordAt d (loc m0 104) mf.c1
  w112 : NativeRustcVm.WordAt d (loc m0 112) mf.c0
  w128 : NativeRustcVm.WordAt d (loc m0 128) beta.c0
  share : NativeRustcVm.EWAt d (loc m0 5248) share

/-- `PushMem`'s intervals. -/
abbrev pushIv : List (Nat × Nat) := [(88, 120), (128, 136), (160, 4176), (5248, 5264)]

/-- **`PushMem` through what keeps it.** -/
theorem PushMem.of_keep {m0 : MachineData} {L : LayoutW} {w pt tv mem : Array EW}
    {beta mf bf share : EW} {d d' : Mem 64} (h : PushMem m0 L w pt tv mem beta mf bf share d)
    (hk : KeepIv pushIv m0 d d') : PushMem m0 L w pt tv mem beta mf bf share d' := by
  have i1 : ((88, 120) : Nat × Nat) ∈ pushIv := by simp
  have i2 : ((128, 136) : Nat × Nat) ∈ pushIv := by simp
  have i3 : ((160, 4176) : Nat × Nat) ∈ pushIv := by simp
  have i4 : ((5248, 5264) : Nat × Nat) ∈ pushIv := by simp
  have wd : ∀ {lo hi o : Nat} {v : UInt64}, (lo, hi) ∈ pushIv → lo ≤ o → o + 8 ≤ hi →
      NativeRustcVm.WordAt d (loc m0 o) v → NativeRustcVm.WordAt d' (loc m0 o) v :=
    fun hm h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn hm h1 h2) le_rfl
  have hb : busLayoutBytes = 888 := rfl
  have hp := h.psz
  refine ⟨BusLayoutWAt.of_same h.push (hk.sameIn i3 (by omega) (by rw [hb]; omega)),
    BusLayoutWAt.of_same h.pull (hk.sameIn i3 (by omega) (by rw [hb]; omega)),
    BusLayoutWAt.of_same h.count (hk.sameIn i3 (by omega) (by rw [hb]; omega)),
    NativeRustcVm.Tables.EWsAt.of_same h.hw (hk.sameIn i3 (o := 2824) (n := 256) (by omega)
      (by omega)) (by rw [Array.length_toList, h.wsz]), h.wsz,
    wd i3 (by omega) (by omega) h.t0a, wd i3 (by omega) (by omega) h.t0b,
    wd i3 (by omega) (by omega) h.t1a, wd i3 (by omega) (by omega) h.t1b,
    wd i3 (by omega) (by omega) h.t2a, wd i3 (by omega) (by omega) h.t2b,
    NativeRustcVm.Tables.EWsAt.of_same h.hpt (hk.sameIn i3 (o := 3136) (n := 1008) (by omega)
      (by omega)) (by rw [Array.length_toList]; omega), h.psz,
    NativeRustcVm.Tables.EWsAt.of_same h.hmem (hk.sameIn i3 (o := 4144) (n := 32) (by omega)
      (by omega)) (by rw [Array.length_toList, h.msz]), h.msz,
    wd i1 (by omega) (by omega) h.w88, wd i1 (by omega) (by omega) h.w96,
    wd i1 (by omega) (by omega) h.w104, wd i1 (by omega) (by omega) h.w112,
    wd i2 (by omega) (by omega) h.w128,
    NativeRustcVm.Layout.EWAt.of_same h.share (hk.sameIn i4 (by omega) (by omega)) le_rfl⟩

/-- **The closure's environment** at `5264`: the weights', the memory's addresses, the
memory and bytecode points' addresses and lengths, the share's address. -/
structure EnvW (m0 : MachineData) (L : LayoutW) (pt : Array EW) (d : Mem 64) : Prop where
  e0 : NativeRustcVm.WordAt d (loc m0 5264) (UInt64.ofBitVec (loc m0 2824))
  e1 : NativeRustcVm.WordAt d (loc m0 5272) (UInt64.ofBitVec (loc m0 4144))
  e2 : NativeRustcVm.WordAt d (loc m0 5280) (UInt64.ofBitVec (loc m0 3136))
  e3 : NativeRustcVm.WordAt d (loc m0 5288) (min L.logMemory pt.size).toUInt64
  e4 : NativeRustcVm.WordAt d (loc m0 5296) (UInt64.ofBitVec (loc m0 3136))
  e5 : NativeRustcVm.WordAt d (loc m0 5304) (min L.logBytecode pt.size).toUInt64
  e6 : NativeRustcVm.WordAt d (loc m0 5312) (UInt64.ofBitVec (loc m0 5248))

/-- **`EnvW` through what keeps it.** -/
theorem EnvW.of_keep {m0 : MachineData} {L : LayoutW} {pt : Array EW} {d d' : Mem 64}
    (h : EnvW m0 L pt d) (hk : KeepIv [(5264, 5320)] m0 d d') : EnvW m0 L pt d' := by
  have wd : ∀ {o : Nat} {v : UInt64}, 5264 ≤ o → o + 8 ≤ 5320 →
      NativeRustcVm.WordAt d (loc m0 o) v → NativeRustcVm.WordAt d' (loc m0 o) v :=
    fun h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn (by simp) h1 h2) le_rfl
  exact ⟨wd (by omega) (by omega) h.e0, wd (by omega) (by omega) h.e1,
    wd (by omega) (by omega) h.e2, wd (by omega) (by omega) h.e3, wd (by omega) (by omega) h.e4,
    wd (by omega) (by omega) h.e5, wd (by omega) (by omega) h.e6⟩

/-- **`!(-1 << x)`** is `2^x - 1`. -/
theorem mask_toNat {x : BitVec 64} (hx : x.toNat < 64) :
    (BinOp.apply .orn .W64 (BitVec.ofNat 64 0)
      (BinOp.apply .lslv .W64 (BitVec.ofNat 64 18446744073709551615) x)).toNat =
      2 ^ x.toNat - 1 := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
  rw [show x.toNat % RegWidth.W64.bits = x.toNat from Nat.mod_eq_of_lt hx]
  rw [BitVec.toNat_or, BitVec.toNat_not, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_or]
  have h1 := Nat.one_le_two_pow (n := x.toNat)
  have h2 : 2 ^ x.toNat ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  generalize 2 ^ x.toNat = P at h1 h2 ⊢
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl] at h2 ⊢
  omega

/-- `tablesW` has a table per table. -/
theorem tablesW_size' : tablesW.size = nTables := by simp [tablesW]; rfl

/-- The emptied forms' slots. -/
theorem slot_forms0 (t side : Nat) : (forms0.getD t #[]).getD side #[] = #[] := by
  simp only [forms0, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases tablesW[t]? with
  | none => rfl
  | some _ => rcases side with _ | _ | _ | side <;> rfl

/-- **The emptied forms**: a count `0` at each form's first word. -/
theorem forms0_at {d : Mem 64} {a : BitVec 64}
    (h : ∀ j < 18, NativeRustcVm.WordAt d (off a (5928 * j)) 0) : FormsAt d a forms0 := by
  have hs : forms0.size = nTables := by simp [forms0, tablesW_size']
  have hrow : ∀ t (ht : t < forms0.size), forms0[t] = #[#[], #[], #[]] := fun t ht ↦ by
    simp [forms0]
  refine ⟨hs, fun t ht ↦ by rw [hrow t ht]; rfl, fun t ht s hs' ↦ ?_⟩
  have h3 : s < 3 := by rw [hrow t ht] at hs'; simpa using hs'
  have hf : forms0[t][s] = #[] := by
    have e := slot_forms0 t s
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht,
      Option.getD_some, Array.getElem?_eq_getElem hs', Option.getD_some] at e
    exact e
  rw [hf]
  have ht' : t < 6 := by rw [hs] at ht; exact ht
  exact ⟨by simp, h (3 * t + s) (by omega), fun i h' ↦ absurd h' (by simp)⟩

/-- **The emptied forms fit** before side `0`. -/
theorem fits_forms0 : FitsUpTo forms0 0 := by
  refine ⟨⟨by simp [forms0, tablesW_size'], fun row hr ↦ ?_⟩, fun o _ s _ ↦
    ⟨fun h ↦ absurd h (by omega), fun _ ↦ ?_⟩⟩
  · simp only [forms0, Array.mem_map] at hr
    obtain ⟨_, _, rfl⟩ := hr
    rfl
  · unfold slot
    rw [slot_forms0]
    rfl

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **`b38`'s start state**: the bus at X19, the forms' offsets in X23, X29, X27, X24, X21. -/
theorem match_frF (hS : StackOk m0 verifyBusBalanceStack) {m : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 5488)
    (x19 : (m.regs.getXReg .X19).toBitVec = m0.regs.X4.toBitVec)
    (x23 : (m.regs.getXReg .X23).toBitVec = BitVec.ofNat 64 35568)
    (x29 : (m.regs.getXReg .X29).toBitVec = BitVec.ofNat 64 41496)
    (x27 : (m.regs.getXReg .X27).toBitVec = BitVec.ofNat 64 47424)
    (x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 53352)
    (x21 : (m.regs.getXReg .X21).toBitVec = BitVec.ofNat 64 59280) :
    Match (Env.ofMachine m [(base m0 5488, 5488), (m0.regs.X4.toBitVec, 107768)]) frF m :=
  match_ofMachine (sregions := [(5488, true), (107768, false)])
    (regions := [(base m0 5488, 5488), (m0.regs.X4.toBitVec, 107768)])
    ⟨rfl, fun _ ↦ Bus.base_aligned hS N_ge rfl, rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hsp]; simp)
    ⟨by show (m.regs.getXReg .X19).toBitVec = _; rw [x19, eval_ptr_off (by rfl)]; simp,
      x23, x29, x27, x24, x21, trivial⟩ trivial trivial trivial

omit [Labels] in
/-- **A block's writes in the frame or the bus** are outputs' or the frame's below the slots. -/
theorem writeOk_bus {m : MachineData} {S : SState}
    (hall : (S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 5392)) ||
      (w.r == 1 && decide (w.off + w.n ≤ 107768))) = true) :
    ∀ w ∈ S.mem, WriteOk (Env.ofMachine m [(base m0 5488, 5488), (m0.regs.X4.toBitVec, 107768)])
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
    exact ⟨hle, fun i hi ↦ .inr (.inl (NativeRustcVm.inRange_add (by rw [busBytes_eq]; exact hi)
      (by rw [busBytes_eq]; decide)))⟩

/-- **A byte a block wrote in the frame or the bus** is the stack's or the bus's. -/
theorem written_fb (h : VerifyBusBalancePre a s0 L m0) {m : MachineData} {S : SState}
    (hall : (S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 5488)) ||
      (w.r == 1 && decide (w.off + w.n ≤ 107768))) = true) {q : BitVec 64}
    (hq : Written (Env.ofMachine m [(base m0 5488, 5488), (m0.regs.X4.toBitVec, 107768)]) S q) :
    InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack q ∨
      InRange m0.regs.X4.toBitVec busBytes q := by
  have hS := pre_stack h
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · rw [hr] at hb
    simp only [Env.ofMachine, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    left
    refine loc_stack hS (o := 0) (n := 5488) le_rfl ?_
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
    have hnw : m0.regs.X4.toBitVec.toNat + busBytes ≤ 2 ^ 64 := (pre_bus h).2.1
    rw [busBytes_eq] at hnw ⊢
    rw [Sym.inRange_iff (by omega)]
    omega

end

public section
variable [Labels]

/-- **At `b37`** (`k + 502`): `computed_bytecode_value` succeeded; the locals, `min(log_bytecode,
|point|)` at `120`. -/
structure AtPush (a : DecArea) (s0 : TState) (L : LayoutW) (m0 : MachineData)
    (w pt tv mem : Array EW) (beta mf bf share : EW) (bp : Array EW) (s' : TState)
    (m : MachineData) : Prop where
  fr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m
  run : (verifyBusBalance L).run s0 = some (resultOf L w beta pt tv mem mf bf share bp, s')
  mem' : PushMem m0 L w pt tv mem beta mf bf share m.dmem
  w120 : NativeRustcVm.WordAt m.dmem (loc m0 120) (min L.logBytecode pt.size).toUInt64
  x19 : m.regs.getXReg .X19 = m0.regs.X4
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x22 : m.regs.getXReg .X22 = beta.c1
  x25 : (m.regs.getXReg .X25).toBitVec = loc m0 3136
  x26 : (m.regs.getXReg .X26).toNat = pt.size
  x27 : m.regs.getXReg .X27 = (min L.logMemory pt.size).toUInt64
  x29 : (m.regs.getXReg .X29).toNat = L.logBytecode
  ts : TStateAt m.dmem m0.regs.X0.toBitVec a s'
  cl : ClaimsWAt m.dmem m0.regs.X5.toBitVec (claimsOf L pt mem mf bf)

end

end NativeRustcVmArm.Bus.VerifyBusBalance
