module

public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.Acc
public import NativeRustcVmArm.Bus.VerifyBusBalance.Tail

/-!
# `verify_bus_balance`'s locals from `b39` on

From `b39` to the count side the frame's locals at `[80, 136)`, `[160, 4176)` and `[5248, 5320)`
stay: the words at `80` to `128`, the sides' layouts, the weights, the GKR point, the memory's
scalars, the share and the closure's environment (`Locs`). The blocks and calls in between write
the stack arguments, the outputs at `5320` and `5344`, the bus's forms and their stacks
(`KeepLoc`).

- `Locs.of_keep`: the locals through what keeps them.
- `keepLoc_block`, `keepLoc_call`: a block's, a call's changes keep them.
- `slice_prefix`, `fingerprints_extract5`: the closure's arguments as the model's.
- `fp_call`: `verify_bus_balance::{closure#0}` called on the environment at `5264`.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- The kept locals' bytes. -/
@[expose] def InLocs (j : Nat) : Prop :=
  (80 ≤ j ∧ j < 136) ∨ (160 ≤ j ∧ j < 4176) ∨ (5248 ≤ j ∧ j < 5320)

/-- The kept locals' bytes the same. -/
@[expose] def KeepLoc (m0 : MachineData) (d d' : Mem 64) : Prop :=
  ∀ j, InLocs j → Same d d' (loc m0 j) 1

theorem KeepLoc.same {m0 : MachineData} {d d' : Mem 64} (h : KeepLoc m0 d d') {o n : Nat}
    (hj : ∀ j < n, InLocs (o + j)) : Same d d' (loc m0 o) n := fun j hj' ↦ by
  have := h (o + j) (hj j hj') 0 (by omega)
  rw [Bus.add_zero'] at this
  rw [NativeRustcVm.addr_add_add]
  exact this

theorem KeepLoc.trans {m0 : MachineData} {d d' d'' : Mem 64} (h : KeepLoc m0 d d')
    (h' : KeepLoc m0 d' d'') : KeepLoc m0 d d'' := fun j hj ↦ (h j hj).trans (h' j hj)

theorem KeepLoc.rfl' {m0 : MachineData} {d d' : Mem 64} (h : d' = d) : KeepLoc m0 d d' :=
  fun _ _ _ _ ↦ by rw [h]

/-- **The locals from `b39` on.** -/
structure Locs (m0 : MachineData) (L : LayoutW) (w pt tv mem : Array EW) (beta mf bf share : EW)
    (d : Mem 64) : Prop where
  pull : BusLayoutWAt d (loc m0 1048) (pullL L)
  count : BusLayoutWAt d (loc m0 1936) (countL L)
  hw : NativeRustcVm.EWsAt d (loc m0 2824) w.toList
  wsz : w.size = 16
  hpt : NativeRustcVm.EWsAt d (loc m0 3136) pt.toList
  psz : pt.size ≤ 63
  hmem : NativeRustcVm.EWsAt d (loc m0 4144) mem.toList
  msz : mem.size = 2
  w80 : NativeRustcVm.WordAt d (loc m0 80) (tv.getD 2 0).c0
  w88 : NativeRustcVm.WordAt d (loc m0 88) bf.c1
  w96 : NativeRustcVm.WordAt d (loc m0 96) bf.c0
  w104 : NativeRustcVm.WordAt d (loc m0 104) mf.c1
  w112 : NativeRustcVm.WordAt d (loc m0 112) mf.c0
  w120 : NativeRustcVm.WordAt d (loc m0 120) (gpowK (2 ^ L.logBytecode - 1))
  w128 : NativeRustcVm.WordAt d (loc m0 128) beta.c0
  share : NativeRustcVm.EWAt d (loc m0 5248) share
  e0 : NativeRustcVm.WordAt d (loc m0 5264) (UInt64.ofBitVec (loc m0 2824))
  e1 : NativeRustcVm.WordAt d (loc m0 5272) (UInt64.ofBitVec (loc m0 4144))
  e2 : NativeRustcVm.WordAt d (loc m0 5280) (UInt64.ofBitVec (loc m0 3136))
  e3 : NativeRustcVm.WordAt d (loc m0 5288) (min L.logMemory pt.size).toUInt64
  e4 : NativeRustcVm.WordAt d (loc m0 5296) (UInt64.ofBitVec (loc m0 3136))
  e5 : NativeRustcVm.WordAt d (loc m0 5304) (min L.logBytecode pt.size).toUInt64
  e6 : NativeRustcVm.WordAt d (loc m0 5312) (UInt64.ofBitVec (loc m0 5248))

/-- **The locals through what keeps them.** -/
theorem Locs.of_keep {m0 : MachineData} {L : LayoutW} {w pt tv mem : Array EW}
    {beta mf bf share : EW} {d d' : Mem 64} (h : Locs m0 L w pt tv mem beta mf bf share d)
    (hk : KeepLoc m0 d d') : Locs m0 L w pt tv mem beta mf bf share d' := by
  have wd : ∀ {o : Nat} {v : UInt64}, (80 ≤ o ∧ o + 8 ≤ 136) ∨ (5248 ≤ o ∧ o + 8 ≤ 5320) →
      NativeRustcVm.WordAt d (loc m0 o) v → NativeRustcVm.WordAt d' (loc m0 o) v :=
    fun ho hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.same (n := 8) fun j hj ↦ by
      unfold InLocs; omega) le_rfl
  have hb : busLayoutBytes = 888 := rfl
  refine ⟨BusLayoutWAt.of_same h.pull (hk.same fun j hj ↦ by unfold InLocs; rw [hb] at hj; omega),
    BusLayoutWAt.of_same h.count (hk.same fun j hj ↦ by unfold InLocs; rw [hb] at hj; omega),
    NativeRustcVm.Tables.EWsAt.of_same h.hw (hk.same (n := 256) fun j hj ↦ by unfold InLocs; omega)
      (by rw [Array.length_toList, h.wsz]), h.wsz,
    NativeRustcVm.Tables.EWsAt.of_same h.hpt (hk.same (n := 1008) fun j hj ↦ by
      unfold InLocs; omega) (by rw [Array.length_toList]; have := h.psz; omega), h.psz,
    NativeRustcVm.Tables.EWsAt.of_same h.hmem (hk.same (n := 32) fun j hj ↦ by unfold InLocs; omega)
      (by rw [Array.length_toList, h.msz]), h.msz,
    wd (by omega) h.w80, wd (by omega) h.w88, wd (by omega) h.w96, wd (by omega) h.w104,
    wd (by omega) h.w112, wd (by omega) h.w120, wd (by omega) h.w128,
    NativeRustcVm.Layout.EWAt.of_same h.share (hk.same (n := 16) fun j hj ↦ by
      unfold InLocs; omega) le_rfl,
    wd (by omega) h.e0, wd (by omega) h.e1, wd (by omega) h.e2, wd (by omega) h.e3,
    wd (by omega) h.e4, wd (by omega) h.e5, wd (by omega) h.e6⟩

/-- **A block's changes keep the locals**: its writes in the frame in `[lo, hi)`, apart from
them, the others within their regions. -/
theorem keepLoc_block [Labels] {m0 m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).WF) {sizes : List Nat}
    (hsz : (Env.ofMachine m ((base m0 5488, 5488) :: rs)).regions.map Prod.snd = sizes)
    {lo hi : Nat}
    (hw : (S.mem.all fun w ↦ (w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) ||
      (w.r != 0 && decide (w.off + w.n ≤ (sizes[w.r]?).getD 0))) = true)
    (hd : ∀ j, InLocs j → j + 1 ≤ lo ∨ hi ≤ j) : KeepLoc m0 m.dmem m'.dmem := fun j hj ↦
  same_out hm hwf hsz hw (o := j) (n := 1) (by unfold InLocs at hj; omega) (hd j hj)

/-- **A call's changes keep the locals**: below the frame and `X`, apart from them. -/
theorem keepLoc_call {m0 m d : MachineData} (hS : StackOk m0 verifyBusBalanceStack)
    (hsp : m.regs.SP.toBitVec = base m0 5488) {N' : Nat} (hle : 5488 + N' ≤ verifyBusBalanceStack)
    {X : BitVec 64 → Prop}
    (hs : SameOutside m.dmem d.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨ X q))
    (hX : ∀ j, InLocs j → ¬X (loc m0 j)) : KeepLoc m0 m.dmem d.dmem := fun j hj ↦
  same_call hS hsp hle hs (o := j) (n := 1) (by unfold InLocs at hj; omega) fun i hi ↦ by
    rw [show i = 0 by omega, Bus.add_zero']; exact hX j hj

/-- A local of `n` bytes at `o` misses the locals. -/
theorem not_locs {m0 : MachineData} (hS : StackOk m0 verifyBusBalanceStack) {o n : Nat}
    (hon : o + n ≤ 5488) (hd : ∀ j, InLocs j → j < o ∨ o + n ≤ j) :
    ∀ j, InLocs j → ¬InRange (loc m0 o) n (loc m0 j) := fun j hj ↦
  loc_not_loc hS (by unfold InLocs at hj; omega) hon (hd j hj)

end

/-! ## The closure's arguments -/

public section

/-- A prefix of the point read as a slice. -/
theorem slice_prefix {m : MachineData} {a : BitVec 64} {pt : Array EW}
    (h : NativeRustcVm.EWsAt m.dmem a pt.toList) (hsz : pt.size ≤ 63) (k : Nat) :
    slice m (UInt64.ofBitVec a) (min k pt.size).toUInt64 = pt.extract 0 k := by
  have e := NativeRustcVm.ewsOf_of_ewsAt (NativeRustcVm.EWsAt.take h k)
  have hl : (pt.toList.take k).length = min k pt.size := by simp
  rw [hl] at e
  have hn : (min k pt.size).toUInt64.toNat = min k pt.size :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  unfold slice
  rw [UInt64.toBitVec_ofBitVec, hn, e]
  apply Array.ext'
  simp

/-- `fingerprints` reads the first five weights. -/
theorem fingerprints_extract5 (w mem ml bl : Array EW) (share pc mc bc : EW) :
    fingerprints (w.extract 0 5) mem ml bl share pc mc bc =
      fingerprints w mem ml bl share pc mc bc := by
  unfold fingerprints
  simp only [Array.extract_extract, Nat.zero_add, Nat.min_def]
  rfl

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **The `TState` and the claims kept** by changes in the stack and the bus. -/
theorem keep_tc (h : VerifyBusBalancePre a s0 L m0) {d d' : Mem 64} (hk : Kept d d')
    {X : BitVec 64 → Prop} (hs : SameOutside d d' X)
    (hX : ∀ q, X q → InRange (stackBelow m0 verifyBusBalanceStack) verifyBusBalanceStack q ∨
      InRange m0.regs.X4.toBitVec busBytes q)
    {s : TState} {cs : Array ColumnClaimW} (hts : TStateAt d m0.regs.X0.toBitVec a s)
    (hcl : ClaimsWAt d m0.regs.X5.toBitVec cs) :
    TStateAt d' m0.regs.X0.toBitVec a s ∧ ClaimsWAt d' m0.regs.X5.toBitVec cs := by
  have hnw := Bus.stack_noWrap (pre_stack h)
  have htok := pre_tok h
  have fp := (pre_ts h).footprint
  refine ⟨hts.frame hk (fun q hq ↦ ?_) hs, NativeRustcVm.Tables.ClaimsWAt.of_same hcl
    (Same.of_sameOutside hs fun j hj hq ↦ ?_)⟩
  · rcases hX q hq with hq | hq
    · exact ⟨NativeRustcVm.Apart.not_inRange htok.1.symm hnw fp.1.2 hq,
        NativeRustcVm.Apart.not_inRange htok.2.1.symm hnw fp.2.1.2 hq⟩
    · exact bus_not_tsw h hq
  · have hc := (pre_cl h).2.1
    have hin : InRange m0.regs.X5.toBitVec claimsBytes (m0.regs.X5.toBitVec + BitVec.ofNat 64 j) :=
      NativeRustcVm.inRange_add hj (by unfold NoWrap at hc; rw [claimsBytes_eq] at hc hj ⊢; omega)
    rcases hX _ hq with hq | hq
    · exact NativeRustcVm.Apart.not_inRange (pre_cl h).2.2.2.2.1.symm hnw hc hq hin
    · exact bus_not_cl h hq hin

/-- A register a block loaded from the frame's byte `o`. -/
theorem reg_ld {m m' : MachineData} {S : SState} {x : XReg} {o : Nat}
    (hm : Match (Env.ofMachine m [(base m0 5488, 5488)]) S m') (hx : S.reg x = some (.load 0 o 8))
    {w : UInt64} (hw : NativeRustcVm.WordAt m.dmem (loc m0 o) w) : m'.regs.getXReg x = w :=
  UInt64.toBitVec_inj.mp ((hm.regs x _ hx).trans
    (Transcript.load_ofMachine (b := base m0 5488) (n := 5488) rfl hw))

/-- A register a block set to the frame's byte `o`. -/
theorem reg_ptr {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState} {x : XReg}
    (o : Nat) (hm : Match (Env.ofMachine m ((base m0 5488, 5488) :: rs)) S m')
    (hx : S.reg x = some (.ptr 0 (o : Int))) : (m'.regs.getXReg x).toBitVec = loc m0 o := by
  rw [hm.regs x _ hx, eval_ptr_off rfl, BitVec.ofInt_natCast]

/-- A stack argument a block wrote. -/
theorem stackArg_write {m st : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m [(base m0 5488, 5488)]) S st)
    (hsp : st.regs.SP.toBitVec = base m0 5488) {o : Nat} (ho : o + 8 ≤ 5488) {v : Sym}
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) :
    stackArg st o = UInt64.ofBitVec (v.eval (Env.ofMachine m [(base m0 5488, 5488)])) :=
  stackArg_of hsp (frame_write hm ho hw)

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

omit [Host] in
/-- An environment word the closure reads. -/
theorem envWord_eq {m : MachineData} (x1 : m.regs.X1.toBitVec = loc m0 5264) {i : Nat}
    {v : UInt64} (hw : NativeRustcVm.WordAt m.dmem (loc m0 (5264 + 8 * i)) v) :
    envWord m i = v := by
  unfold envWord
  rw [x1, NativeRustcVm.addr_add_add]
  exact NativeRustcVm.wordOf_of_wordAt hw

/-- **`verify_bus_balance::{closure#0}(out, env, pc, memory_count, bytecode_count)`** from the
frame: the output at `5344`, the environment at `5264`; the three fingerprints in the model's
terms. -/
theorem fp_call (h : VerifyBusBalancePre a s0 L m0)
    (hfc : Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryLabel ∧ retOf st.data = next)
    {w pt tv mem : Array EW} {beta mf bf share : EW}
    (hl : Locs m0 L w pt tv mem beta mf bf share st.data.dmem)
    (x0 : st.data.regs.X0.toBitVec = loc m0 5344) (x1 : st.data.regs.X1.toBitVec = loc m0 5264)
    (cont : ∀ m2, Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m2 →
      NativeRustcVm.EWsAt m2.dmem (loc m0 5344) (fingerprints w mem (pt.extract 0 L.logMemory)
        (pt.extract 0 L.logBytecode) share (EW.ofK st.data.regs.X2)
        ⟨st.data.regs.X3, st.data.regs.X4⟩ ⟨st.data.regs.X5, st.data.regs.X6⟩).toList →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦
        InRange (stackBelow st.data fpClosureStack) fpClosureStack q ∨
          InRange (loc m0 5344) 48 q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have hN := hS.2.1
  have lm := (pre_lay h).log_memory_le
  have lb := (pre_lay h).log_bytecode_le
  have hp := hl.psz
  have ew0 : envWord st.data 0 = UInt64.ofBitVec (loc m0 2824) := envWord_eq x1 hl.e0
  have ew1 : envWord st.data 1 = UInt64.ofBitVec (loc m0 4144) := envWord_eq x1 hl.e1
  have ew2 : envWord st.data 2 = UInt64.ofBitVec (loc m0 3136) := envWord_eq x1 hl.e2
  have ew3 : envWord st.data 3 = (min L.logMemory pt.size).toUInt64 := envWord_eq x1 hl.e3
  have ew4 : envWord st.data 4 = UInt64.ofBitVec (loc m0 3136) := envWord_eq x1 hl.e4
  have ew5 : envWord st.data 5 = (min L.logBytecode pt.size).toUInt64 := envWord_eq x1 hl.e5
  have ew6 : envWord st.data 6 = UInt64.ofBitVec (loc m0 5248) := envWord_eq x1 hl.e6
  have n3 : (min L.logMemory pt.size).toUInt64.toNat = min L.logMemory pt.size :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have n5 : (min L.logBytecode pt.size).toUInt64.toNat = min L.logBytecode pt.size :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have io : ∀ {o n : Nat}, o + n ≤ 5488 → InOk st.data (loc m0 o) n fpClosureStack :=
    fun hon ↦ loc_inOk h hfr le_fp hon
  refine Fr.callLocal (o := 5344) (n := 48) (X := InRange (loc m0 5344) 48)
    hfr hN le_fp keep_callee (slots_lo (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ .inr hq) hfc hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · unfold FpClosurePre
    rw [x0, x1, ew0, ew1, ew2, ew3, ew4, ew5, ew6]
    refine ⟨hfr.stackOk hS rfl le_fp, (io (o := 5264) (n := 56) (by omega)).1,
      (io (o := 5264) (n := 56) (by omega)).2, io (o := 2824) (n := 16 * 5) (by omega),
      io (o := 4144) (n := 16 * 2) (by omega), ?_, ?_, io (o := 5248) (n := 16 * 1) (by omega),
      (io (o := 5344) (n := 48) (by omega)).1, (io (o := 5344) (n := 48) (by omega)).2⟩
    · unfold SliceOk; rw [n3, UInt64.toBitVec_ofBitVec]; exact io (by omega)
    · unfold SliceOk; rw [n5, UInt64.toBitVec_ofBitVec]; exact io (by omega)
  · rcases hq' with hq' | hq'
    · rw [x0] at hq'; exact .inr hq'
    · exact .inl hq'
  · simp only [FpClosurePost, fpClosureArgs] at hq2
    obtain ⟨h1, -, hsv⟩ := hq2
    rw [x0, ew0, ew1, ew2, ew3, ew4, ew5, ew6, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofBitVec,
      UInt64.toBitVec_ofBitVec, slice_prefix hl.hpt hp, slice_prefix hl.hpt hp,
      NativeRustcVm.ewOf_of_ewAt hl.share] at h1
    have e1 : (NativeRustcVm.ewsOf st.data.dmem (loc m0 4144) 2).toArray = mem := by
      have := NativeRustcVm.ewsOf_of_ewsAt hl.hmem
      rw [Array.length_toList, hl.msz] at this
      rw [this]
    have e0 : (NativeRustcVm.ewsOf st.data.dmem (loc m0 2824) 5).toArray = w.extract 0 5 := by
      have := NativeRustcVm.ewsOf_of_ewsAt hl.hw
      rw [Array.length_toList, hl.wsz] at this
      have hk : (NativeRustcVm.ewsOf st.data.dmem (loc m0 2824) 16).take 5 =
          NativeRustcVm.ewsOf st.data.dmem (loc m0 2824) 5 := by
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp
      rw [← hk, this]
      apply Array.ext'
      simp
    rw [e0, e1, fingerprints_extract5] at h1
    exact cont m2 hfr2 h1 hsv.2.2 hcs2 hs2

end

end NativeRustcVmArm.Bus.VerifyBusBalance
