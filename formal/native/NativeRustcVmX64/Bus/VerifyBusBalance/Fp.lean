module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Count
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names

/-!
# The sides' locals, the closure's call (x86-64)

From `b45` to the count side the frame's locals at `[104, 192)`, `[216, 232)`, `[248, 624)`,
`[1800, 5472)` stay (`SideMem`): the bus's and the point's addresses, the point's length, the
`pc_final`, the counts, the β, the memory's scalars, the closure's environment, the share, the
weights, the point, the pull and count sides' layouts, the trees' second and third values.

- `SideMem.of_keep`: through `KeepIv sideIv`.
- `slice_prefix`, `fingerprints_extract5`: the closure's arguments as the model's.
- `fpCall`: `verify_bus_balance::{closure#0}(624, 248, pc, …)`, RSP at the frame's offset `80`.
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- **The sides' locals.** -/
structure SideMem (m0 : MachineData) (L : LayoutW) (w pt tv mem : Array EW)
    (beta mf bf share : EW) (d : Mem 64) : Prop where
  tail : TailMem m0 pt d
  pull : BusLayoutWAt d (loc m0 3696) (pullL L)
  count : BusLayoutWAt d (loc m0 4584) (countL L)
  hw : NativeRustcVm.EWsAt d (loc m0 368) w.toList
  wsz : w.size = 16
  hmem : NativeRustcVm.EWsAt d (loc m0 216) mem.toList
  msz : mem.size = 2
  w128 : NativeRustcVm.WordAt d (loc m0 128) (gpowK (2 ^ L.logBytecode - 1))
  w136 : NativeRustcVm.WordAt d (loc m0 136) (tv.getD 1 0).c0
  w320 : NativeRustcVm.WordAt d (loc m0 320) (tv.getD 1 0).c1
  w312 : NativeRustcVm.WordAt d (loc m0 312) (tv.getD 2 0).c0
  w304 : NativeRustcVm.WordAt d (loc m0 304) (tv.getD 2 0).c1
  w168 : NativeRustcVm.WordAt d (loc m0 168) mf.c0
  w160 : NativeRustcVm.WordAt d (loc m0 160) mf.c1
  w152 : NativeRustcVm.WordAt d (loc m0 152) bf.c0
  w144 : NativeRustcVm.WordAt d (loc m0 144) bf.c1
  w184 : NativeRustcVm.WordAt d (loc m0 184) beta.c0
  w176 : NativeRustcVm.WordAt d (loc m0 176) beta.c1
  share : NativeRustcVm.EWAt d (loc m0 352) share
  e0 : NativeRustcVm.WordAt d (loc m0 248) (UInt64.ofBitVec (loc m0 368))
  e1 : NativeRustcVm.WordAt d (loc m0 256) (UInt64.ofBitVec (loc m0 216))
  e2 : NativeRustcVm.WordAt d (loc m0 264) (UInt64.ofBitVec (loc m0 1800))
  e3 : NativeRustcVm.WordAt d (loc m0 272) (min L.logMemory pt.size).toUInt64
  e4 : NativeRustcVm.WordAt d (loc m0 280) (UInt64.ofBitVec (loc m0 1800))
  e5 : NativeRustcVm.WordAt d (loc m0 288) (min L.logBytecode pt.size).toUInt64
  e6 : NativeRustcVm.WordAt d (loc m0 296) (UInt64.ofBitVec (loc m0 352))

/-- The sides' locals' intervals. -/
abbrev sideIv : List (Nat × Nat) := [(104, 192), (216, 624), (1800, 5472)]

theorem SideMem.of_keep {m0 : MachineData} {L : LayoutW} {w pt tv mem : Array EW}
    {beta mf bf share : EW} {d d' : Mem 64} (h : SideMem m0 L w pt tv mem beta mf bf share d)
    (hk : KeepIv sideIv m0 d d') : SideMem m0 L w pt tv mem beta mf bf share d' := by
  have psz := h.tail.psz
  have i1 : (104, 192) ∈ sideIv := by simp
  have i2 : (216, 624) ∈ sideIv := by simp
  have i3 : (216, 624) ∈ sideIv := by simp
  have i4 : (1800, 5472) ∈ sideIv := by simp
  have w1 : ∀ {o : Nat} {x : UInt64}, 104 ≤ o → o + 8 ≤ 192 →
      NativeRustcVm.WordAt d (loc m0 o) x → NativeRustcVm.WordAt d' (loc m0 o) x :=
    fun h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn i1 h1 h2) le_rfl
  have w3 : ∀ {o : Nat} {x : UInt64}, 216 ≤ o → o + 8 ≤ 624 →
      NativeRustcVm.WordAt d (loc m0 o) x → NativeRustcVm.WordAt d' (loc m0 o) x :=
    fun h1 h2 hw ↦ NativeRustcVm.Layout.WordAt.of_same hw (hk.sameIn i3 h1 h2) le_rfl
  have hk4 : KeepIv tailIv m0 d d' := fun j ⟨p, hp, h1, h2⟩ ↦ hk j (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨_, i1, by simp only at h1 h2 ⊢; omega, by simp only at h1 h2 ⊢; omega⟩
    · exact ⟨_, i4, by simp only at h1 h2 ⊢; omega, by simp only at h1 h2 ⊢; omega⟩)
  refine ⟨h.tail.of_keep hk4,
    BusLayoutWAt.of_same h.pull (hk.sameIn i4 (by omega) (by have := busLayoutBytes_eq; omega)),
    BusLayoutWAt.of_same h.count (hk.sameIn i4 (by omega) (by have := busLayoutBytes_eq; omega)),
    NativeRustcVm.Tables.EWsAt.of_same h.hw (hk.sameIn i3 (n := 256) (by omega) (by omega))
      (by rw [Array.length_toList, h.wsz]), h.wsz,
    NativeRustcVm.Tables.EWsAt.of_same h.hmem (hk.sameIn i2 (n := 32) (by omega) (by omega))
      (by rw [Array.length_toList, h.msz]), h.msz,
    w1 (by omega) (by omega) h.w128, w1 (by omega) (by omega) h.w136,
    w3 (by omega) (by omega) h.w320, w3 (by omega) (by omega) h.w312,
    w3 (by omega) (by omega) h.w304, w1 (by omega) (by omega) h.w168,
    w1 (by omega) (by omega) h.w160, w1 (by omega) (by omega) h.w152,
    w1 (by omega) (by omega) h.w144, w1 (by omega) (by omega) h.w184,
    w1 (by omega) (by omega) h.w176,
    NativeRustcVm.Layout.EWAt.of_same h.share (hk.sameIn i3 (n := 16) (by omega) (by omega)) le_rfl,
    w3 (by omega) (by omega) h.e0, w3 (by omega) (by omega) h.e1, w3 (by omega) (by omega) h.e2,
    w3 (by omega) (by omega) h.e3, w3 (by omega) (by omega) h.e4, w3 (by omega) (by omega) h.e5,
    w3 (by omega) (by omega) h.e6⟩

/-- A prefix of the point read as a slice. -/
theorem slice_prefix {m : MachineData} {a : BitVec 64} {pt : Array EW}
    (h : NativeRustcVm.EWsAt m.dmem a pt.toList) (hsz : pt.size ≤ 63) (k : Nat) :
    slice m a (min k pt.size).toUInt64.toBitVec = pt.extract 0 k := by
  have e := NativeRustcVm.ewsOf_of_ewsAt (NativeRustcVm.EWsAt.take h k)
  have hl : (pt.toList.take k).length = min k pt.size := by simp
  rw [hl] at e
  have hn : (min k pt.size).toUInt64.toBitVec.toNat = min k pt.size := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  unfold slice
  rw [hn, e]
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
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

omit [Host] in
/-- An environment word the closure reads. -/
theorem envWord_eq {m : MachineData} (x1 : reg m .rsi = loc m0 248) {i : Nat} {v : UInt64}
    (hw : NativeRustcVm.WordAt m.dmem (loc m0 (248 + 8 * i)) v) : envWord m i = v.toBitVec := by
  unfold envWord
  rw [x1, off_add]
  exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt hw)

/-- **`verify_bus_balance::{closure#0}(624, 248, pc, mc, bc)`** from the frame, RSP at `80`: the
three fingerprints in the model's terms at `624`. -/
theorem fpCall (h : VerifyBusBalancePre a s0 L m0)
    (hfc : Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (fr : St m0 80 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel ∧ retOf st.data = next)
    {w pt tv mem : Array EW} {beta mf bf share : EW}
    (hl : SideMem m0 L w pt tv mem beta mf bf share st.data.dmem)
    (x0 : reg st.data .rdi = loc m0 624) (x1 : reg st.data .rsi = loc m0 248)
    (cont : ∀ m2, St m0 88 m2 →
      NativeRustcVm.EWsAt m2.dmem (loc m0 624) (fingerprints w mem (pt.extract 0 L.logMemory)
        (pt.extract 0 L.logBytecode) share (EW.ofK (.ofBitVec (reg st.data .rdx)))
        (ewArg (reg st.data .rcx) (reg st.data .r8))
        (ewArg (reg st.data .r9) (stackArg st.data 0))).toList →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow st.data fpClosureStack) fpClosureStack q ∨
          NativeRustcVm.InRange (loc m0 624) 48 q) →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.get64 r = st.data.regs.get64 r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have hle : 5520 - 80 + fpClosureStack ≤ NN := le_fp
  have psz := hl.tail.psz
  have lm := (pre_lay h).log_memory_le
  have lb := (pre_lay h).log_bytecode_le
  have ew0 : envWord st.data 0 = loc m0 368 := envWord_eq x1 hl.e0
  have ew1 : envWord st.data 1 = loc m0 216 := envWord_eq x1 hl.e1
  have ew2 : envWord st.data 2 = loc m0 1800 := envWord_eq x1 hl.e2
  have ew3 : envWord st.data 3 = (min L.logMemory pt.size).toUInt64.toBitVec := envWord_eq x1 hl.e3
  have ew4 : envWord st.data 4 = loc m0 1800 := envWord_eq x1 hl.e4
  have ew5 : envWord st.data 5 = (min L.logBytecode pt.size).toUInt64.toBitVec :=
    envWord_eq x1 hl.e5
  have ew6 : envWord st.data 6 = loc m0 352 := envWord_eq x1 hl.e6
  have n3 : (min L.logMemory pt.size).toUInt64.toBitVec.toNat = min L.logMemory pt.size := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have n5 : (min L.logBytecode pt.size).toUInt64.toBitVec.toNat = min L.logBytecode pt.size := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have io : ∀ {j n : Nat}, 88 ≤ j → j + n ≤ 5520 → InOk st.data (loc m0 j) n fpClosureStack :=
    fun h1 h2 ↦ cal_localIn h fr (by omega) hle h1 h2
  refine callF h (c := 80) (Nc := fpClosureStack) (lo := 624) (len := 48)
    (X := NativeRustcVm.InRange (loc m0 624) 48) (by omega) hle (by omega) (fun q hq ↦ .inr hq)
    hfc fr hpc ?_ (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · unfold FpClosurePre
    rw [x0, x1, ew0, ew1, ew2, ew3, ew4, ew5, ew6]
    refine ⟨cal_stack h fr (by omega) hle, ⟨?_, ?_⟩, (io (j := 248) (n := 56) (by omega)
      (by omega)).1, (io (j := 248) (n := 56) (by omega) (by omega)).2,
      io (j := 368) (n := 16 * 5) (by omega) (by omega),
      io (j := 216) (n := 16 * 2) (by omega) (by omega), ?_, ?_,
      io (j := 352) (n := 16 * 1) (by omega) (by omega),
      (io (j := 624) (n := 48) (by omega) (by omega)).1,
      (io (j := 624) (n := 48) (by omega) (by omega)).2⟩
    · rw [fr.frame.sp, off_add]
      exact mapped_off (Mapped.keeps (frame_mapped hS N_ge) fr.frame.kept) (by omega)
    · rw [fr.frame.sp, loc_toNat hS (by omega)]
      have := rsp_ge hS; have := rsp_top hS; have := N_ge
      omega
    · unfold SliceOk; rw [n3]; exact io (by omega) (by omega)
    · unfold SliceOk; rw [n5]; exact io (by omega) (by omega)
  · rw [x0] at hq'
    exact hq'.elim .inr .inl
  · obtain ⟨h1, -, hsv⟩ := hq2
    rw [x0, ew0, ew1, ew2, ew3, ew4, ew5, ew6, slice_prefix hl.tail.hpt psz,
      slice_prefix hl.tail.hpt psz, NativeRustcVm.ewOf_of_ewAt hl.share] at h1
    have e1 : (NativeRustcVm.ewsOf st.data.dmem (loc m0 216) 2).toArray = mem := by
      have := NativeRustcVm.ewsOf_of_ewsAt hl.hmem
      rw [Array.length_toList, hl.msz] at this
      rw [this]
    have e0 : (NativeRustcVm.ewsOf st.data.dmem (loc m0 368) 5).toArray = w.extract 0 5 := by
      have := NativeRustcVm.ewsOf_of_ewsAt hl.hw
      rw [Array.length_toList, hl.wsz] at this
      have hk : (NativeRustcVm.ewsOf st.data.dmem (loc m0 368) 16).take 5 =
          NativeRustcVm.ewsOf st.data.dmem (loc m0 368) 5 := by
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp
      rw [← hk, this]
      apply Array.ext'
      simp
    rw [e0, e1, fingerprints_extract5] at h1
    exact cont m2 fr2 h1 hs2 hsv.2 hcs2

end

end NativeRustcVmX64.Bus.VerifyBusBalance
