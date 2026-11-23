module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Calls
public import NativeRustcVmX64.Bus.VerifyBusBalanceClosure0
public import NativeRustcVm.Bus.SideFits
public import NativeVm.Math.Layout
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names

/-!
# `accumulate_side` called from `verify_bus_balance`'s frame (x86-64)

- `sideOf`, `sideOf_eq`: a side's blocks in the layout, the data's at the layout's rows.
- `busLayout_tables_size`: a side's layout has a placement per block.
- `PlacementsAt.of_same`, `BusLayoutWAt.of_same`, `FormsAt.of_same`: kept over bytes kept.
- `lay_same`, `bus_inOk`: the layout's bytes as at the entry, the bus's forms for a callee.
- `accCall`: the call, RSP at the frame's base (its 11 stack arguments at `8` to `96`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

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

/-- **A side's layout has a placement per block.** -/
theorem busLayout_tables_size (fw : Array Nat) (B : Array BusBlockW) :
    (busLayout fw B).tables.size = B.size := by
  have := (NativeVm.Math.Layout.stackOffsets_spec (fw ++ B.map (·.logRows))).2.1
  simp only [busLayout, Array.size_extract, Array.size_zipWith, this, Array.size_append,
    Array.size_map]
  omega

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

/-- The forms over bytes that stayed the same. -/
theorem FormsAt.of_same {d d' : Mem 64} {a : BitVec 64} {F : Array (Array FormW)}
    (h : FormsAt d a F) (hs : Same d d' a formsBytes) : FormsAt d' a F := by
  have hf : formBufBytes = 5928 := rfl
  have hb : formsBytes = 106704 := rfl
  refine ⟨h.size, h.row_size, fun t ht s hs' ↦ ?_⟩
  have h1 := h.row_size t ht
  have h2 := h.size
  exact NativeRustcVm.Tables.FormBufAt.of_same (h.forms t ht s hs')
    (hs.sub (by rw [hb, hf]; unfold nTables at h2; omega))

/-- A block's bytes: sixteen. -/
theorem length_blocks (bl : List NativeRustcVm.Data.Block) :
    (bl.flatMap NativeRustcVm.Data.Block.bytes).length = 16 * bl.length :=
  NativeRustcVm.length_flatMap_const (fun b ↦ by
    simp [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes,
      NativeRustcVm.length_wordBytes]) bl

theorem formsBytes_le : formsBytes ≤ busBytes := by decide

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **The layout's bytes** as at the entry. -/
theorem lay_same (h : VerifyBusBalancePre a s0 L m0) {d : MachineData} {o : Nat}
    (fr : St m0 o d) : Same m0.dmem d.dmem (reg m0 .rsi) layoutBytes :=
  Same.of_sameOutside fr.same fun j hj hq ↦ by
    have hnw := (pre_layOk h).1.2
    rcases hq with hq | hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange_add (pre_layOk h).2 hnw
        (noWrap_stackBelow (pre_stack h)) hj (inRange_mono hq (by omega))
    · exact NativeRustcVm.Apart.not_inRange_add (pre_layT h) hnw (pre_ts h).footprint.1.2 hj hq
    · exact NativeRustcVm.Apart.not_inRange_add (pre_busL h).symm hnw (pre_bus h).2.1 hj hq
    · exact NativeRustcVm.Apart.not_inRange_add (pre_clL h).symm hnw (pre_cl h).2.1 hj hq

theorem lay_at (h : VerifyBusBalancePre a s0 L m0) {d : MachineData} {o : Nat}
    (fr : St m0 o d) : LayoutWAt d.dmem (reg m0 .rsi) L :=
  NativeRustcVm.Tables.LayoutWAt.of_same (pre_lay h) (lay_same h fr)

/-- The bus's first `n` bytes for a callee. -/
theorem bus_inOk (h : VerifyBusBalancePre a s0 L m0) {d : MachineData} {c Nc n : Nat}
    (fr : St m0 c d) (hc : c ≤ 5472) (hle : 5520 - c + Nc ≤ NN) (hn : n ≤ busBytes) :
    InOk d (reg m0 .r8) n Nc :=
  have hb := cal_out h fr hc hle (pre_bus h)
  ⟨⟨fun i hi ↦ hb.1 i (by omega), NativeRustcVm.NoWrap.mono hb.2.1 hn⟩,
    NativeRustcVm.Apart.mono hb.2.2.2.2.1 (Nat.le_refl _) (by omega) (Nat.le_refl _)
      (Nat.le_refl _)⟩

/-- The bus is apart from the frame's locals. -/
theorem bus_loc (h : VerifyBusBalancePre a s0 L m0) {n j l : Nat} (hn : n ≤ busBytes)
    (hjl : j + l ≤ 5520) : NativeRustcVm.Apart (reg m0 .r8) n (loc m0 j) l :=
  NativeRustcVm.Apart.mono (apart_loc (pre_stack h) (pre_bus h).2.2.2.2.1 hjl) (Nat.le_refl _)
    (by omega) (Nat.le_refl _) (Nat.le_refl _)

/-- A local of the frame is apart from the read-only data. -/
theorem loc_ro (h : VerifyBusBalancePre a s0 L m0) {j l : Nat} (hjl : j + l ≤ 5520) :
    RodataApart (loc m0 j) l := fun t ↦
  (apart_loc (pre_stack h) ((pre_ro h) t).2.2 hjl).symm

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

open NativeRustcVmX64.Bus.FpClosure (stackArg_eq)

/-- **`accumulate_side(out, bus.forms, side, blocks, layout, side_layout, fps, n, w, wn, β,
point, pn, tree)`** from the frame's base: the output at `o`, the side's layout at `ol`, the
blocks the read-only data's `it`, the point at `1800`. -/
theorem accCall (h : VerifyBusBalancePre a s0 L m0)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (fr : St m0 0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel ∧ retOf st.data = next)
    {side : Nat} (hside : side < 3) {it : NativeRustcVm.Data.Item}
    (hit : it.bytes = (sideBlocks side).flatMap NativeRustcVm.Data.Block.bytes)
    (hitgot : it ∈ [.pushBlocks, .pullBlocks, .countBlocks])
    {o ol : Nat} (ho8 : 96 ≤ o) (ho : o + 24 ≤ 5472) (hol8 : 96 ≤ ol) (hol : ol + 888 ≤ 5472)
    {SL : BusLayoutW} (hSL : BusLayoutWAt st.data.dmem (loc m0 ol) SL)
    (hSLs : SL.tables.size = (sideBlocks side).length)
    {F : Array (Array FormW)} (hF : FormsAt st.data.dmem (reg m0 .r8) F)
    (hfits : FitsUpTo F side)
    (x0 : reg st.data .rdi = loc m0 o) (x1 : reg st.data .rsi = reg m0 .r8)
    (x2 : (reg st.data .rdx).toNat = side) (x3 : reg st.data .rcx = rodataAddr it)
    (x4 : (reg st.data .r8).toNat = (sideBlocks side).length) (x5 : reg st.data .r9 = reg m0 .rsi)
    (a0 : stackArg st.data 0 = loc m0 ol)
    (hfp : 0 < (stackArg st.data 2).toNat →
      InOk st.data (stackArg st.data 1) (16 * (stackArg st.data 2).toNat) accumulateSideStack ∧
      NativeRustcVm.Apart (reg m0 .r8) formsBytes (stackArg st.data 1)
        (16 * (stackArg st.data 2).toNat) ∧
      NativeRustcVm.Apart (loc m0 ol) busLayoutBytes (stackArg st.data 1)
        (16 * (stackArg st.data 2).toNat))
    (hw : SliceOk st.data (stackArg st.data 3) (stackArg st.data 4) accumulateSideStack ∧
      NativeRustcVm.Apart (reg m0 .r8) formsBytes (stackArg st.data 3)
        (16 * (stackArg st.data 4).toNat))
    (a7 : stackArg st.data 7 = loc m0 1800) (a8 : (stackArg st.data 8).toNat ≤ 63)
    {fps w pt : Array EW} {beta tree : EW}
    (hfps : (NativeRustcVm.ewsOf st.data.dmem (stackArg st.data 1)
      (stackArg st.data 2).toNat).toArray = fps)
    (hwv : slice st.data (stackArg st.data 3) (stackArg st.data 4) = w)
    (hbeta : ewArg (stackArg st.data 5) (stackArg st.data 6) = beta)
    (hptv : slice st.data (stackArg st.data 7) (stackArg st.data 8) = pt)
    (htree : ewArg (stackArg st.data 9) (stackArg st.data 10) = tree)
    (harggot : ∀ l ∈ ["memcpy", "memset"],
      (0 < (stackArg st.data 2).toNat →
        Apart (gotAddr l) 8 (stackArg st.data 1) (16 * (stackArg st.data 2).toNat)) ∧
      Apart (gotAddr l) 8 (stackArg st.data 3) (16 * (stackArg st.data 4).toNat))
    (cont : ∀ m2, St m0 8 m2 →
      OptEWAt m2.dmem (loc m0 o)
        (some (accumulateSide F side (sideOf L side) SL fps w beta pt tree).2) →
      FormsAt m2.dmem (reg m0 .r8) (accumulateSide F side (sideOf L side) SL fps w beta pt tree).1 →
      FitsUpTo (accumulateSide F side (sideOf L side) SL fps w beta pt tree).1 (side + 1) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow st.data accumulateSideStack) accumulateSideStack q ∨
          (NativeRustcVm.InRange (loc m0 o) 24 q ∨
            NativeRustcVm.InRange (reg m0 .r8) formsBytes q)) →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.get64 r = st.data.regs.get64 r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have hle := le_acc
  have hle' : 5520 - 0 + accumulateSideStack ≤ NN := hle
  have hbus := pre_bus h
  obtain ⟨rows, hrs, -, hrw, hbb⟩ := (pre_lay h).rows
  have hsl := lay_same h fr
  have hlay : LayoutWAt st.data.dmem (reg m0 .rsi) L := lay_at h fr
  have hrw' : NativeRustcVm.WordsAt st.data.dmem (off (reg m0 .rsi) 72)
      (rows.toList.map Nat.toUInt64) :=
    NativeRustcVm.Tables.WordsAt.of_same hrw (hsl.sub (o := 72) (k := 48) (by decide))
      (by simp [hrs, nTables])
  have hR := cal_ro h fr (by omega) hle'
  obtain ⟨hrb, hrnw, hrap⟩ := hR it
  rw [hit] at hrb hrnw hrap
  rw [length_blocks] at hrnw hrap
  have hsp0 : rspOf st.data = loc m0 0 := fr.frame.sp
  have hsp8 : rspOf st.data + 8#64 = loc m0 8 := by
    rw [hsp0]; exact off_add _ _ _
  have hbl : 1 ≤ (sideBlocks side).length ∧ ∀ x ∈ sideBlocks side,
      x.owner < nTables ∧ x.tuple < NativeRustcVm.Data.tuples.length := by
    obtain rfl | rfl | rfl : side = 0 ∨ side = 1 ∨ side = 2 := by omega
    all_goals exact ⟨by decide, by decide +kernel⟩
  have hfits' := fits_accumulateSide hside hfits L.tableLogHeights rows SL (by rw [hSLs])
    (NativeRustcVm.ewsOf st.data.dmem (stackArg st.data 1) (stackArg st.data 2).toNat).toArray
    (slice st.data (stackArg st.data 3) (stackArg st.data 4))
    (ewArg (stackArg st.data 5) (stackArg st.data 6))
    (slice st.data (stackArg st.data 7) (stackArg st.data 8))
    (ewArg (stackArg st.data 9) (stackArg st.data 10))
  have hfb := formsBytes_le
  have hFb : formsBytes = 106704 := rfl
  have hpt : 1800 + 16 * (stackArg st.data 8).toNat ≤ 5520 := by omega
  refine callF h (c := 0) (Nc := accumulateSideStack) (lo := o) (len := 24)
    (X := fun q ↦ NativeRustcVm.InRange (loc m0 o) 24 q ∨
      NativeRustcVm.InRange (reg m0 .r8) formsBytes q)
    (by omega) hle' ho (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inr (.inl
      (inRange_mono h' hfb)))) (hacc L rows (sideBlocks side) F SL) fr hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · simp only [AccumulateSidePre, accArgs]
    rw [x0, x1, x2, x3, x4, x5, a0, hsp8, a7]
    refine ⟨cal_stack h fr (by omega) hle', hR, ⟨?_, ?_⟩, hside, hF,
      bus_inOk h fr (by omega) hle' hfb,
      fun t ↦ NativeRustcVm.Apart.mono ((pre_busR h) t) (Nat.le_refl _) (by omega)
        (Nat.le_refl _) (Nat.le_refl _),
      hbl.1, rfl, hbl.2, hrb, ⟨⟨by rw [← length_blocks]; exact hrb.mapped, hrnw⟩, hrap⟩, hlay, hrs, hrw',
      cal_in h fr (by omega) hle' (pre_layOk h), hSL, hSLs,
      cal_localIn h fr (by omega) hle' (by omega) (by rw [busLayoutBytes_eq]; omega),
      fun hn ↦ (hfp hn).1, hw.1, by omega,
      cal_localIn h fr (by omega) hle' (by omega) hpt, ?_,
      cal_localIn h fr (by omega) hle' (by omega) (by omega),
      loc_ro h (by omega), (bus_loc h hfb (by omega)).symm, ?_, ?_,
      bus_loc h hfb (by rw [busLayoutBytes_eq]; omega), fun hn ↦ (hfp hn).2.1, hw.2,
      bus_loc h hfb hpt, bus_loc h hfb (by omega),
      loc_apart hS (by rw [busLayoutBytes_eq]; omega) (by omega) (.inr (by omega)),
      fun hn ↦ (hfp hn).2.2, cal_got h fr (by omega) hle' (by decide) ?_⟩
    · rw [hsp8]
      exact mapped_off (Mapped.keeps (frame_mapped hS N_ge) fr.frame.kept) (by omega)
    · rw [hsp0, loc_toNat hS (by omega)]
      have := rsp_ge hS; have := rsp_top hS; have := N_ge
      omega
    · have := hfits'.1
      rw [a7] at this
      exact this
    · have hbr := (pre_busR h) it
      rw [hit, length_blocks] at hbr
      exact NativeRustcVm.Apart.mono hbr (Nat.le_refl _) (by omega) (Nat.le_refl _)
        (Nat.le_refl _)
    · exact NativeRustcVm.Apart.mono (pre_busL h) (Nat.le_refl _) (by omega) (Nat.le_refl _)
        (Nat.le_refl _)
    · intro l hl b hb
      simp only [List.mem_append] at hb
      rcases hb with (hb | hb) | hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
        · exact NativeRustcVm.Apart.mono_right
            (((pre_got h).1 l hl).2.2.2 (reg m0 .r8, busBytes) (by simp))
            (Nat.le_refl _) (by dsimp only; omega)
        · rw [← length_blocks, ← hit]
          apply ((pre_got h).1 l hl).2.2.2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hitgot
          rcases hitgot with rfl | rfl | rfl <;> simp
        · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
        · exact got_apart_frame (pre_got h) hS hl N_ge
            (by rw [busLayoutBytes_eq]; omega)
        · exact (harggot l hl).2
        · exact got_apart_frame (pre_got h) hS hl N_ge hpt
        · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
      · by_cases hn : (stackArg st.data 2).toNat = 0
        · simp only [hn, ↓reduceIte, List.not_mem_nil] at hb
        · simp only [hn, ↓reduceIte, List.mem_singleton] at hb
          subst b
          exact (harggot l hl).1 (by omega)
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        apply ((pre_got h).1 l hl).2.2.2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> simp
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
    exact cont m2 fr2 h1 h2 hf hs2 hsv.2 hcs2

end

end NativeRustcVmX64.Bus.VerifyBusBalance
