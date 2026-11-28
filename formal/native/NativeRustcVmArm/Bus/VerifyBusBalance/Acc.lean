module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.Common
public import NativeRustcVm.Bus.SideFits
public import NativeRustcVmArm.Bus.BusLayout.Model

/-!
# `accumulate_side` called from `verify_bus_balance`'s frame

- `sideOf`: a side's blocks in the layout; `sideOf_eq`: the data's blocks at the layout's rows.
- `loc_inOk`, `bus_apart`: a local of the frame for a callee; the forms apart from it.
- `acc_call`: the call, its precondition from the frame's facts, its result for the caller.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- A side's blocks in the layout. -/
@[expose] def sideOf (L : LayoutW) (side : Nat) : Array BusBlockW :=
  if side = 0 then L.push else if side = 1 then L.pull else L.count

/-- The layout's sides are the data's blocks at its rows. -/
theorem sideOf_eq {L : LayoutW} {rows : Array Nat}
    (hb : busBlocks L.tableLogHeights rows = (L.push, L.pull, L.count)) (side : Nat) :
    ((sideBlocks side).map (blockW L.tableLogHeights rows)).toArray = sideOf L side := by
  rw [busBlocks_eq] at hb
  simp only [Prod.mk.injEq] at hb
  obtain ⟨h0, h1, h2⟩ := hb
  unfold sideOf sideBlocks
  split
  · exact h0
  · split
    · exact h1
    · exact h2

/-- A side's layout has a placement per block. -/
theorem tables_size {L : LayoutW} {rows : Array Nat}
    (hb : busBlocks L.tableLogHeights rows = (L.push, L.pull, L.count)) (fw : Array Nat)
    (side : Nat) : (busLayout fw (sideOf L side)).tables.size = (sideBlocks side).length := by
  rw [← sideOf_eq hb side, BusLayout.busLayout_tables]
  simp

/-- Placements over bytes that stayed the same. -/
theorem PlacementsAt.of_same {d d' : Mem 64} {a : BitVec 64} {N : Nat}
    {ps : Array LeanVM.Protocol.Verifier.Placement} (h : PlacementsAt d a N ps)
    (hs : Same d d' a (8 + NativeRustcVm.Bus.placementBytes * N)) : PlacementsAt d' a N ps := by
  obtain ⟨hle, hw, hp⟩ := h
  refine ⟨hle, WordAt.of_same hw hs (by unfold NativeRustcVm.Bus.placementBytes; omega),
    fun i hi ↦ ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hp i hi
  have hk : 8 + NativeRustcVm.Bus.placementBytes * i + 16 ≤
      8 + NativeRustcVm.Bus.placementBytes * N := by
    unfold NativeRustcVm.Bus.placementBytes; omega
  have hs' := hs.sub (o := 8 + NativeRustcVm.Bus.placementBytes * i) (k := 16) hk
  exact ⟨h1, h2, WordAt.of_same h3 hs' (by omega),
    WordAt.of_same h4 (hs'.sub (o := 8) (k := 8) (by omega)) le_rfl⟩

/-- **A side's layout** over bytes that stayed the same. -/
theorem BusLayoutWAt.of_same {d d' : Mem 64} {a : BitVec 64} {SL : BusLayoutW}
    (h : BusLayoutWAt d a SL) (hs : Same d d' a busLayoutBytes) : BusLayoutWAt d' a SL := by
  have hb : busLayoutBytes = 888 := rfl
  refine ⟨h.depth_lt, WordAt.of_same h.depth hs (by rw [hb]; omega), ?_, ?_⟩
  · exact PlacementsAt.of_same h.framework
      (hs.sub (by unfold NativeRustcVm.Bus.placementBytes; rw [hb]; omega))
  · exact PlacementsAt.of_same h.tables
      (hs.sub (by unfold NativeRustcVm.Bus.placementBytes maxBlocks; rw [hb]))

/-- A slice of `E` elements at their place. -/
theorem slice_of_ewsAt {m : MachineData} {p n : UInt64} {xs : Array EW}
    (h : NativeRustcVm.EWsAt m.dmem p.toBitVec xs.toList) (hn : n.toNat = xs.size) :
    slice m p n = xs := by
  unfold slice
  have := NativeRustcVm.ewsOf_of_ewsAt h
  rw [Array.length_toList] at this
  rw [hn, this]

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **A local of the frame** for a callee using `N'` bytes. -/
theorem loc_inOk (h : VerifyBusBalancePre a s0 L m0) {m : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m) {N' : Nat}
    (hle : 5488 + N' ≤ verifyBusBalanceStack) {o n : Nat} (hon : o + n ≤ 5488) :
    InOk m (loc m0 o) n N' :=
  Bus.local_ok (pre_stack h) hle hon hfr.kept hfr.sp

/-- **The bus is apart from the frame's locals.** -/
theorem bus_apart (h : VerifyBusBalancePre a s0 L m0) {n o n' : Nat} (hn : n ≤ busBytes)
    (hon : o + n' ≤ 5488) : Apart m0.regs.X4.toBitVec n (loc m0 o) n' := by
  have hS := pre_stack h
  have hbus := pre_bus h
  have hbap := hbus.2.2.2.2.1
  have hN := hS.2.1
  have hstk : (stackBelow m0 verifyBusBalanceStack).toNat = m0.regs.SP.toNat - 18288 := by
    rw [Sumcheck.toNat_stackBelow hN, N_eq]
  rw [N_eq] at hbap hN hstk
  have hnw : m0.regs.X4.toBitVec.toNat + busBytes ≤ 2 ^ 64 := hbus.2.1
  have hl := m0.regs.SP.toNat_lt
  rw [busBytes_eq] at hn hbap hnw
  unfold Apart at hbap ⊢
  rw [loc_toNat hS (by omega)]
  omega

omit [Labels] in
/-- Two disjoint ranges of the frame are apart. -/
theorem loc_apart' {m0 : MachineData} (hS : StackOk m0 verifyBusBalanceStack) {o n o' n' : Nat}
    (h1 : o + n ≤ 5488) (h2 : o' + n' ≤ 5488) (hd : o + n ≤ o' ∨ o' + n' ≤ o) :
    Apart (loc m0 o) n (loc m0 o') n' := by
  have hN := hS.2.1
  have := N_ge
  unfold Apart
  rw [loc_toNat hS (by omega), loc_toNat hS (by omega)]
  omega

omit [Labels] in
/-- A block's bytes: sixteen. -/
theorem length_blocks (bl : List NativeRustcVm.Data.Block) :
    (bl.flatMap NativeRustcVm.Data.Block.bytes).length = 16 * bl.length :=
  NativeRustcVm.length_flatMap_const (fun b ↦ by
    simp [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes,
      NativeRustcVm.length_wordBytes]) bl

/-- **The layout's bytes** as at the entry. -/
theorem lay_same (h : VerifyBusBalancePre a s0 L m0) {m : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m) :
    Same m0.dmem m.dmem m0.regs.X1.toBitVec layoutBytes :=
  Same.of_sameOutside hfr.same fun j hj hq ↦ by
    have hnw := (pre_layOk h).1.2
    rcases hq with hq | hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange_add (pre_layOk h).2 hnw (stack_noWrap (pre_stack h))
        hj hq
    · exact NativeRustcVm.Apart.not_inRange_add (pre_layT h) hnw (pre_ts h).footprint.1.2 hj hq
    · exact NativeRustcVm.Apart.not_inRange_add (pre_busL h).symm hnw (pre_bus h).2.1 hj hq
    · exact NativeRustcVm.Apart.not_inRange_add (pre_clL h).symm hnw (pre_cl h).2.1 hj hq

/-- **A local of the frame** is apart from the read-only data. -/
theorem loc_rodataApart (h : VerifyBusBalancePre a s0 L m0) {o n : Nat} (hon : o + n ≤ 5488) :
    RodataApart (loc m0 o) n := fun t ↦ by
  have hS := pre_stack h
  have hap := ((pre_ro h) t).2.2
  have hN := hS.2.1
  have hstk : (stackBelow m0 verifyBusBalanceStack).toNat = m0.regs.SP.toNat - 18288 := by
    rw [Sumcheck.toNat_stackBelow hN, N_eq]
  rw [N_eq] at hap hN hstk
  have hl := m0.regs.SP.toNat_lt
  unfold NativeRustcVm.Apart at hap ⊢
  rw [loc_toNat hS (by omega)]
  omega

/-- **The read-only data's item** for a callee: readable, apart from its stack and the bus. -/
theorem ro_ok (h : VerifyBusBalancePre a s0 L m0) {m : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m) {N' : Nat}
    (hle : 5488 + N' ≤ verifyBusBalanceStack) (it : NativeRustcVm.Data.Item) :
    NativeRustcVm.BytesAt m.dmem (NativeRustcVmArm.rodataAddr it) it.bytes ∧
      InOk m (NativeRustcVmArm.rodataAddr it) it.bytes.length N' ∧
      Apart m0.regs.X4.toBitVec busBytes (NativeRustcVmArm.rodataAddr it) it.bytes.length := by
  have hR := Fr.rodataAt hfr (pre_ro h) (pre_stack h).2.1 hle fun t i hi hq ↦ by
    rcases hq with hq | hq | hq
    · exact rodataApart_out (pre_tR h) (pre_ro h) (pre_ts h).footprint.1.2 t i hi hq
    · exact rodataApart_out (pre_busR h) (pre_ro h) (pre_bus h).2.1 t i hi hq
    · exact rodataApart_out (pre_clR h) (pre_ro h) (pre_cl h).2.1 t i hi hq
  obtain ⟨hb, hnw, hap⟩ := hR it
  exact ⟨hb, ⟨⟨hb.mapped, hnw⟩, hap⟩, pre_busR h it⟩

omit [Labels] in
/-- A word the frame holds at `o` is the stack argument `o`. -/
theorem stackArg_of {m : MachineData} (hsp : m.regs.SP.toBitVec = base m0 5488) {o : Nat}
    {v : UInt64} (hw : NativeRustcVm.WordAt m.dmem (loc m0 o) v) : stackArg m o = v := by
  unfold stackArg
  rw [hsp]
  exact NativeRustcVm.wordOf_of_wordAt hw

/-- **A word a block wrote** at the frame's byte `o`. -/
theorem frame_write {m st : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m [(base m0 5488, 5488)]) S st) {o : Nat} (ho : o + 8 ≤ 5488)
    {v : Sym} (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) :
    NativeRustcVm.WordAt st.dmem (loc m0 o)
      (UInt64.ofBitVec (v.eval (Env.ofMachine m [(base m0 5488, 5488)]))) :=
  Transcript.wordAt_write hm rfl ho hw

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **`accumulate_side(out, bus.forms, side, blocks, layout, side_layout, fps, …)`** from the
frame: the output at `o`, the side's layout at `ol`, the blocks the read-only data's `it`, the
fingerprints (`n` of them) at X7, the weights at `wa`, the point at `3136`. -/
theorem acc_call (h : VerifyBusBalancePre a s0 L m0)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmArm.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.AccumulateSide.entryLabel ∧ retOf st.data = next)
    {side : Nat} (hside : side < 3) {it : NativeRustcVm.Data.Item}
    (hit : it.bytes = (sideBlocks side).flatMap NativeRustcVm.Data.Block.bytes)
    {o ol : Nat} (ho : o + 24 ≤ 5392) (hol : ol + 888 ≤ 5392)
    {SL : BusLayoutW} (hSL : BusLayoutWAt st.data.dmem (loc m0 ol) SL)
    (hSLs : SL.tables.size = (sideBlocks side).length)
    {F : Array (Array FormW)} (hF : FormsAt st.data.dmem m0.regs.X4.toBitVec F)
    (hfits : FitsUpTo F side)
    (x0 : st.data.regs.X0.toBitVec = loc m0 o) (x1 : st.data.regs.X1 = m0.regs.X4)
    (x2 : st.data.regs.X2.toNat = side)
    (x3 : st.data.regs.X3.toBitVec = NativeRustcVmArm.rodataAddr it)
    (x4 : st.data.regs.X4.toNat = (sideBlocks side).length) (x5 : st.data.regs.X5 = m0.regs.X1)
    (x6 : st.data.regs.X6.toBitVec = loc m0 ol) (hol0 : 72 ≤ ol)
    (hfp : 0 < (stackArg st.data 0).toNat →
      InOk st.data st.data.regs.X7.toBitVec (16 * (stackArg st.data 0).toNat) accumulateSideStack ∧
      Apart m0.regs.X4.toBitVec formsBytes st.data.regs.X7.toBitVec
        (16 * (stackArg st.data 0).toNat))
    (hfpL : 0 < (stackArg st.data 0).toNat →
      Apart (loc m0 ol) busLayoutBytes st.data.regs.X7.toBitVec (16 * (stackArg st.data 0).toNat))
    (hw : SliceOk st.data (stackArg st.data 8) (stackArg st.data 16) accumulateSideStack ∧
      Apart m0.regs.X4.toBitVec formsBytes (stackArg st.data 8).toBitVec
        (16 * (stackArg st.data 16).toNat))
    (hp40 : (stackArg st.data 40).toBitVec = loc m0 3136)
    (hp48 : (stackArg st.data 48).toNat ≤ 63)
    {fps w pt : Array EW} {beta tree : EW}
    (hfps : (NativeRustcVm.ewsOf st.data.dmem st.data.regs.X7.toBitVec
      (stackArg st.data 0).toNat).toArray = fps)
    (hwv : slice st.data (stackArg st.data 8) (stackArg st.data 16) = w)
    (hbeta : (⟨stackArg st.data 24, stackArg st.data 32⟩ : EW) = beta)
    (hptv : slice st.data (stackArg st.data 40) (stackArg st.data 48) = pt)
    (htree : (⟨stackArg st.data 56, stackArg st.data 64⟩ : EW) = tree)
    (cont : ∀ m2, Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m2 →
      OptEWAt m2.dmem (loc m0 o)
        (some (accumulateSide F side (sideOf L side) SL fps w beta pt tree).2) →
      FormsAt m2.dmem m0.regs.X4.toBitVec
        (accumulateSide F side (sideOf L side) SL fps w beta pt tree).1 →
      FitsUpTo (accumulateSide F side (sideOf L side) SL fps w beta pt tree).1 (side + 1) →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦
        InRange (stackBelow st.data accumulateSideStack) accumulateSideStack q ∨
          InRange (loc m0 o) 24 q ∨ InRange m0.regs.X4.toBitVec formsBytes q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have hN := hS.2.1
  have hle := le_acc
  have hbus := pre_bus h
  have hfb : formsBytes ≤ busBytes := by decide
  obtain ⟨rows, hrs, -, hrw, hbb⟩ := (pre_lay h).rows
  have hsl := lay_same h hfr
  have hlay : LayoutWAt st.data.dmem m0.regs.X1.toBitVec L :=
    NativeRustcVm.Tables.LayoutWAt.of_same (pre_lay h) hsl
  have hrw' : NativeRustcVm.WordsAt st.data.dmem (off m0.regs.X1.toBitVec 72)
      (rows.toList.map Nat.toUInt64) :=
    NativeRustcVm.Tables.WordsAt.of_same hrw (hsl.sub (o := 72) (k := 48) (by decide))
      (by simp [hrs, nTables])
  obtain ⟨hrb, hrok, hrap⟩ := ro_ok h hfr hle it
  rw [hit] at hrb hrok hrap
  rw [length_blocks] at hrok hrap
  have hsp0 : st.data.regs.SP.toBitVec = loc m0 0 := by rw [hfr.sp]; exact (Bus.add_zero' _).symm
  have hbl : 1 ≤ (sideBlocks side).length ∧ ∀ x ∈ sideBlocks side,
      x.owner < nTables ∧ x.tuple < NativeRustcVm.Data.tuples.length := by
    obtain rfl | rfl | rfl : side = 0 ∨ side = 1 ∨ side = 2 := by omega
    all_goals exact ⟨by decide, by decide +kernel⟩
  have hbusF : InOk st.data m0.regs.X4.toBitVec formsBytes accumulateSideStack :=
    ⟨⟨fun i hi ↦ hfr.kept _ (hbus.1 i (by omega)), NativeRustcVm.NoWrap.mono hbus.2.1 hfb⟩,
      NativeRustcVm.Apart.mono (hfr.apart hN hbus.2.2.2.2.1 hle) (Nat.le_refl _) (by omega)
        (Nat.le_refl _) (Nat.le_refl _)⟩
  have hfits' := fits_accumulateSide hside hfits L.tableLogHeights rows SL (by rw [hSLs])
    (NativeRustcVm.ewsOf st.data.dmem st.data.regs.X7.toBitVec (stackArg st.data 0).toNat).toArray
    (slice st.data (stackArg st.data 8) (stackArg st.data 16))
    ⟨stackArg st.data 24, stackArg st.data 32⟩
    (slice st.data (stackArg st.data 40) (stackArg st.data 48))
    ⟨stackArg st.data 56, stackArg st.data 64⟩
  have a1 : Apart m0.regs.X4.toBitVec formsBytes (NativeRustcVmArm.rodataAddr it)
      (16 * (sideBlocks side).length) :=
    NativeRustcVm.Apart.mono hrap (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)
  have a2 : Apart m0.regs.X4.toBitVec formsBytes m0.regs.X1.toBitVec layoutBytes :=
    NativeRustcVm.Apart.mono (pre_busL h) (Nat.le_refl _) (by omega) (Nat.le_refl _)
      (Nat.le_refl _)
  have a3 : InOk st.data m0.regs.X1.toBitVec layoutBytes accumulateSideStack :=
    ⟨⟨fun i hi ↦ hfr.kept _ ((pre_layOk h).1.1 i hi), (pre_layOk h).1.2⟩,
      hfr.apart hN (pre_layOk h).2 hle⟩
  have hlp : 3136 + 16 * (stackArg st.data 48).toNat ≤ 5488 := by omega
  refine Fr.callLocal (o := o) (n := 24)
    (X := fun q ↦ InRange (loc m0 o) 24 q ∨ InRange m0.regs.X4.toBitVec formsBytes q)
    hfr hN hle keep_callee (slots_lo ho) (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inr (.inl (NativeRustcVm.InRange.mono h'
      (NativeRustcVm.NoWrap.mono hbus.2.1 hfb) hbus.2.1 (Nat.le_refl _) (by omega)))))
    (hacc L rows (sideBlocks side) F SL) hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · refine ⟨hfr.stackOk hS rfl hle, Fr.rodataAt hfr (pre_ro h) hN hle fun t i hi hq ↦ ?_,
      by rw [hsp0]; exact (loc_inOk h hfr hle (o := 0) (n := 72) (by omega)).1,
      by rw [x2]; exact hside, by rw [x1]; exact hF, by rw [x1]; exact hbusF,
      by rw [x1]; exact fun t ↦ NativeRustcVm.Apart.mono ((pre_busR h) t) (Nat.le_refl _)
          (by omega) (Nat.le_refl _) (Nat.le_refl _),
      hbl.1, x4, hbl.2, by rw [x3]; exact hrb, by rw [x3]; exact hrok,
      by rw [x5]; exact hlay, hrs, by rw [x5]; exact hrw',
      by rw [x5]; exact a3,
      by rw [x6]; exact hSL, hSLs,
      by rw [x6, busLayoutBytes_eq]; exact loc_inOk h hfr hle (by omega),
      fun hn ↦ (hfp hn).1, hw.1, by omega,
      by unfold SliceOk; rw [hp40]; exact loc_inOk h hfr hle hlp,
      by rw [x2]; exact hfits'.1,
      by rw [x0]; exact loc_inOk h hfr hle (by omega),
      by rw [x0]; exact loc_rodataApart h (by omega),
      by rw [x0, x1]; exact (bus_apart h hfb (by omega)).symm,
      by rw [x1, x3]; exact a1,
      by rw [x1, x5]; exact a2,
      by rw [x1, x6, busLayoutBytes_eq]; exact bus_apart h hfb (by omega),
      fun hn ↦ by rw [x1]; exact (hfp hn).2, by rw [x1]; exact hw.2,
      by rw [x1, hp40]; exact bus_apart h hfb hlp,
      by rw [x1, hsp0]; exact bus_apart h hfb (by omega),
      by rw [x6, hsp0, busLayoutBytes_eq]; exact loc_apart' hS (by omega) (by omega) (.inr hol0),
      fun hn ↦ by rw [x6]; exact hfpL hn⟩
    rcases hq with hq | hq | hq
    · exact rodataApart_out (pre_tR h) (pre_ro h) (pre_ts h).footprint.1.2 t i hi hq
    · exact rodataApart_out (pre_busR h) (pre_ro h) (pre_bus h).2.1 t i hi hq
    · exact rodataApart_out (pre_clR h) (pre_ro h) (pre_cl h).2.1 t i hi hq
  · rw [x0, x1] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'
  · obtain ⟨h1, h2, -, hsv⟩ := hq2
    have e := sideOf_eq hbb side
    rw [x2, e, hfps, hwv, hbeta, hptv, htree] at h1 h2
    rw [x0] at h1
    rw [x1] at h2
    have hf := hfits'.2
    rw [e, hfps, hwv, hbeta, hptv, htree] at hf
    exact cont m2 hfr2 h1 h2 hf hsv.2.2 hcs2 hs2

end

end NativeRustcVmArm.Bus.VerifyBusBalance
