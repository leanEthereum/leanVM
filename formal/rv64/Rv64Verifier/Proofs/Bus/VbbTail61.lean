import Rv64Verifier.Proofs.Bus.VbbTail60

/-!
# `verify_bus_balance`'s side loop: into the block loop

Past `0x800077b0` (`At3`): with no block, `0x80007b18` zeroes the sum and reaches the side's sums at
`0x80007b24` (`enterNone`, `Tl`); else `0x800077c8` stores the loop's frame and reaches its head
`0x800078f0` (`enterBlk`: `Entry`, `Ex`, `Blk` after no block). `blkEnter` is both from `known`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem At3.frH {s z h u t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E}
    (hpre : BusBalancePre s) (F : Front s z h u i sd point) (A : At3 s z h u t i sd point) :
    DFrame h t (FrW s h t) :=
  (F.fr.mono fun _ ha ↦ FrW.mono A.mono ha).trans A.fr fun _ ha ↦ EW.frW hpre F.cur.step.mono ha

theorem hPb_of {bev : MachineState → Word → List E → Option E} {s z w v h₀ : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E}
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) :
    (w.getReg .x25).toNat = 0 ∨ heapNext z ≤ (w.getReg .x23).toNat := by
  have ho := C.rows1.obuf
  simp only [NewBuf] at ho
  rcases ho.2 with h0 | h0
  · exact Or.inl (by omega)
  · exact Or.inr h0.1

/-- With no block: `0x80007b18` to the sums. -/
theorem enterNone {bev : MachineState → Word → List E → Option E} {s z w v h₀ h u t : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E}
    {acc : List (List Form) × List E} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E}
    (hpre : BusBalancePre s) (C : SCtx bev s z w v h₀ k state mem mf bf bv)
    (Sd : Sides s z h₀ h (w.getReg .x23) (w.getReg .x25).toNat acc) (F : Front s z h u i sd point)
    (A : At3 s z h u t i sd point) (h0 : t.getReg .x21 = 0) (hpc : t.pc = 0x80007b18) :
    ∃ e, Reaches Image.code t e ∧ e.pc = 0x80007b24 ∧ min sd.2.1.tables.length sd.1.length = 0 ∧
      Tl s z h e e i sd point (w.getReg .x23) (w.getReg .x25).toNat acc.1 acc.2 := by
  have hsz : heapNext s ≤ heapNext z := C.fps.inv.mono
  obtain ⟨e, hr, he⟩ := Sym.BlockSpec.reaches b80007b18_spec hpc trivial
  have m := b80007b18_mem_same he
  have kk := b80007b18_keeps he
  have hn : heapNext e = heapNext t := by simp only [heapNext, m]
  have Ce : Cur s z h e := A.cur.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m A.cur.inv.heap (kk .x2 (by decide))) fun _ h ↦ h.elim
  have fhe : DFrame h e (FrW s h e) :=
    ((At3.frH hpre F A).mono fun _ ha ↦ FrW.mono hn.ge ha).trans (DFrame.of_same m _) fun _ h ↦ h
  have hm0 : min sd.2.1.tables.length sd.1.length = 0 := by rw [← A.x21, h0]; rfl
  have htb := A.tbBuf
  refine ⟨e, hr, b80007b18_pc he, hm0, ⟨?_, Ex.keep hpre A.ex Sd.inv A.cur.inv.heap
    (DFrame.of_same m _) hn.ge (kk .x25 (by decide)), ?_, ?_, ?_, (kk .x22 (by decide)).trans A.x22,
    (m _).trans A.m1176, (m _).trans A.m1184⟩⟩
  · rw [hm0]; exact Sides.mm hpre hsz (hPb_of C) Sd Ce fhe
  · rw [b80007b18_x17 he, b80007b18_x16 he, b80007b18_x15 he, hm0]; exact eOf3_zero
  · rw [kk .x20 (by decide), (DFrame.of_same m fun _ ↦ False).eListAt fun _ _ h ↦ h]; exact A.tb
  · rw [kk .x20 (by decide)]
    exact ⟨htb.1, htb.2.imp_right fun h ↦ ⟨h.1, by rw [hn]; exact h.2⟩⟩

/-- Words of the frame at the side loop's head, from the loop's entry. -/
theorem headWords {bev : MachineState → Word → List E → Option E} {s z w v h₀ h : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E}
    {acc : List (List Form) × List E} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv)
    (Sd : Sides s z h₀ h (w.getReg .x23) (w.getReg .x25).toNat acc) :
    h.getMem (s.getReg .x2 - 1232) = BitVec.ofNat 64 (w.getReg .x25).toNat ∧
      h.getMem (s.getReg .x2 - 1224) = w.getReg .x23 ∧
      h.getMem (s.getReg .x2 - 1240) = vecPtr s (s.getReg .x11) ∧
      h.getMem (s.getReg .x2 - 1256) = h.getReg .x27 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hw25 : BitVec.ofNat 64 (w.getReg .x25).toNat = w.getReg .x25 := by simp
  have h0E (j : Nat) (hj : 1144 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 1280 ∨ 1312 ≤ j)
      (h2 : j ≤ 1256 ∨ 1280 ≤ j) (h3 : j ≠ 1248) (h4 : j ≤ 1144 ∨ 1224 ≤ j) (h8 : j % 8 = 0) :
      h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = h₀.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    Sd.step.slot' hpre (by omega) hj2 fun y hy hy' ↦ by
      simp only [LoopW] at hy'
      rcases hy' with hy' | hy' | hy' | hy' | hy' | hy' | hy' | hy' <;>
        addr_omega [hy, hy', hb1, hj, hj2, h1, h2, h3, h4, h8]
  have stZH := (C.rows1.step.trans C.setup.step).trans Sd.step
  have h1256 : h.getMem (s.getReg .x2 - BitVec.ofNat 64 1256) =
      z.getMem (s.getReg .x2 - BitVec.ofNat 64 1256) :=
    stZH.slot' hpre (by omega) (by omega) fun y hy hy' ↦ by
      simp only [RowsW, SetupW, LoopW] at hy'
      rcases hy' with ((hy' | hy' | hy') | (hy' | hy')) | (hy' | hy' | hy' | hy' | hy' | hy' | hy' |
        hy') <;> addr_omega [hy, hy', hb1]
  have hx27 : h.getReg .x27 = z.getMem (s.getReg .x2 - 1256) :=
    Sd.x27.trans ((C.setup.regs .x27 (by decide)).trans ((C.rows1.regs .x27 (by decide)).trans
      ((C.rows0.regs .x27 (by decide)).trans C.fps.x27)))
  refine ⟨?_, ?_, ?_, h1256.trans hx27.symm⟩
  · exact (h0E 1232 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans
      ((C.setup.words (1232, v.getReg .x25) (by simp [setupWords])).trans
        ((C.rows1.regs .x25 (by decide)).trans hw25.symm))
  · refine (h0E 1224 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans ?_
    refine (C.setup.step.slot' hpre (j := 1224) (by omega) (by omega) fun y hy hy' ↦ ?_).trans
      C.rows1.ptr
    rcases hy' with hy' | hy' <;> addr_omega [hy, hy', hb1]
  · have hl := hpre.layout
    have hlb := hl.bound
    refine (h0E 1240 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans ?_
    rw [C.setup.words (1240, v.getMem (v.getMem (s.getReg .x2 - 1240) + 8)) (by simp [setupWords]),
      C.kept.layout]
    exact C.rows1.inv.word hl (by addr_omega [hlb]) (by addr_omega [hlb])

set_option maxRecDepth 8192 in
/-- With a block: `0x800077c8` to the block loop's head. -/
theorem enterBlk {bev : MachineState → Word → List E → Option E} {s z w v h₀ h u t : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E}
    {acc : List (List Form) × List E} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E}
    (hpre : BusBalancePre s) (C : SCtx bev s z w v h₀ k state mem mf bf bv)
    (Sd : Sides s z h₀ h (w.getReg .x23) (w.getReg .x25).toNat acc) (SO : SideOk s z h i sd)
    (F : Front s z h u i sd state.point) (A : At3 s z h u t i sd state.point) (hi : i < 3)
    (h0 : t.getReg .x21 ≠ 0) (hpc : t.pc = 0x800077c8) :
    ∃ e, Reaches Image.code t e ∧ e.pc = 0x800078f0 ∧
      0 < min sd.2.1.tables.length sd.1.length ∧
      Entry s z h e i sd state.point (w.getReg .x23) (w.getReg .x25).toNat ∧
      Ex s h e i sd state.point ∧
      Blk s z h e e i sd state.point (w.getReg .x23) (w.getReg .x25).toNat acc.1 acc.2 0 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have hsz : heapNext s ≤ heapNext z := C.fps.inv.mono
  have Ih := Sd.inv
  have hlo := Ih.heap.lo
  have sp₃ : t.getReg .x2 = s.getReg .x2 - 1344 := A.cur.inv.sp
  obtain ⟨e, hr, he⟩ := Sym.BlockSpec.reaches b800077c8_spec hpc (by
    rv_eval [sp₃]; and_intros <;> valid_access hval [hb1])
  have kk := b800077c8_keeps he
  have fe : DFrame t e fun a ↦ Within a (s.getReg .x2 - 1272) 8 ∨
      Within a (s.getReg .x2 - 1216) 24 := fun a ha ↦ he.frame a (by
    rv_eval [sp₃]
    and_intros <;> intro hh <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, hh]
      first
        | exact Or.inl (by addr_omega [hb1])
        | exact Or.inr (by addr_omega [hb1])))
  have hn : heapNext e = heapNext t := by
    simp only [heapNext]; rw [fe nextAddr fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hb1, hnx]]
  have st : StepS s t e fun a ↦ Within a (s.getReg .x2 - 1272) 8 ∨
      Within a (s.getReg .x2 - 1216) 24 :=
    StepS.ofDFrame A.cur.inv.heap fe (fun _ h ↦ h) (fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hb1, hnx]) (kk .x2 (by decide))
  have Ce : Cur s z h e := A.cur.next hpre hsz st fun a ha ↦ Or.inl (by
    simp only [SlotW]
    rcases ha with ha | ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))
  have fhe : DFrame h e (FrW s h e) :=
    ((At3.frH hpre F A).mono fun _ ha ↦ FrW.mono hn.ge ha).trans fe fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))
  have fue : DFrame u e (EW s u e) :=
    (A.fr.mono fun _ ha ↦ EW.mono hn.ge ha).trans fe fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
  have heE := Ce.inv.heap.hi
  -- slots of `Front`'s state kept
  have ue (j : Nat) (hj : 1144 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≠ 1304) (h2 : j ≠ 1272)
      (h3 : j ≤ 1192 ∨ 1224 ≤ j) (h4 : j ≤ 1168 ∨ 1192 ≤ j) (h8 : j % 8 = 0) :
      e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    fue _ fun q hq hw ↦ by
      rcases hw with hw | hw | hw | hw | hw | hw | hw | ⟨-, a2⟩
      · addr_omega [hw, hq, hb1, hj, hj2, h1, h8]
      · addr_omega [hw, hq, hb1, hj, hj2, h2, h8]
      · addr_omega [hw, hq, hb1, hj, hj2, h3, h8]
      · addr_omega [hw, hq, hb1, hj, hj2, h4, h8]
      · addr_omega [hw, hq, hb1, hj, hj2]
      · addr_omega [hw, hq, hb1, hj, hj2]
      · addr_omega [hw, hq, hb1, hj, hj2, hnx]
      · simp only [heapNext, heapEnd] at a2 heE; addr_omega [a2, hq, hb1, hj, hj2, heE]
  -- slots of the head kept
  have hE (j : Nat) (hj : 1144 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 1280 ∨ 1312 ≤ j)
      (h2 : j ≤ 1256 ∨ 1280 ≤ j) (h3 : j ≠ 1248) (h4 : j ≤ 1144 ∨ 1224 ≤ j) (h8 : j % 8 = 0) :
      e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    fhe _ fun q hq hw ↦ by
      rcases hw with hw | hw | hw | hw | hw | hw | hw | ⟨-, a2⟩
      · addr_omega [hw, hq, hb1, hj, hj2, h1, h8]
      · addr_omega [hw, hq, hb1, hj, hj2, h2, h8]
      · addr_omega [hw, hq, hb1, hj, hj2, h3, h8]
      · addr_omega [hw, hq, hb1, hj, hj2, h4, h8]
      · addr_omega [hw, hq, hb1, hj, hj2]
      · addr_omega [hw, hq, hb1, hj, hj2]
      · addr_omega [hw, hq, hb1, hj, hj2, hnx]
      · simp only [heapNext, heapEnd] at a2 heE; addr_omega [a2, hq, hb1, hj, hj2, heE]
  -- the block's stores
  have a128 : t.getReg .x2 + 128 = s.getReg .x2 - 1216 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a136 : t.getReg .x2 + 136 = s.getReg .x2 - 1208 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a144 : t.getReg .x2 + 144 = s.getReg .x2 - 1200 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a72 : t.getReg .x2 + 72 = s.getReg .x2 - 1272 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a96 : t.getReg .x2 + 96 = s.getReg .x2 - 1248 := by
    rw [sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have m1216 := b800077c8_m_x2_128 he
  have m1208 := b800077c8_m_x2_136 he
  have m1200 := b800077c8_m_x2_144 he
  have m1272 := b800077c8_m_x2_72 he
  rw [a128] at m1216
  rw [a136] at m1208
  rw [a144] at m1200
  rw [a72, a96] at m1272
  have t1248 : e.getMem (s.getReg .x2 - 1248) = t.getMem (s.getReg .x2 - 1248) :=
    fe _ fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1]
  have tE (j : Nat) (hj : 1144 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≠ 1272) (h3 : j ≤ 1192 ∨ 1224 ≤ j)
      (h8 : j % 8 = 0) :
      e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    fe _ fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1, hj, hj2, h1, h3, h8]
  -- the frame's words
  have e1160 : e.getMem (s.getReg .x2 - 1160) = sideWord s h i 72 :=
    (ue 1160 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans F.m1160
  have e1168 : e.getMem (s.getReg .x2 - 1168) = sideWord s h i 80 :=
    (ue 1168 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans F.m1168
  have e1264 : e.getMem (s.getReg .x2 - 1264) = sideWord s h i 48 :=
    (ue 1264 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans F.m1264
  have e1248 : e.getMem (s.getReg .x2 - 1248) = sideWord s h i 56 :=
    (ue 1248 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans F.m1248
  have x25h : e.getReg .x25 = h.getReg .x25 := (kk .x25 (by decide)).trans A.ex.x25
  have x25w : h.getReg .x25 = w.getReg .x25 :=
    Sd.x25.trans ((C.setup.regs .x25 (by decide)).trans (C.rows1.regs .x25 (by decide)))
  have hw25 : BitVec.ofNat 64 (w.getReg .x25).toNat = w.getReg .x25 := by simp
  -- the point
  have PA := pointAt hpre C Sd
  have W := headWords hpre C Sd
  have e1256 : e.getMem (s.getReg .x2 - 1256) = h.getReg .x27 :=
    (hE 1256 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans W.2.2.2
  have e1144 : e.getMem (s.getReg .x2 - 1144) = h.getMem (s.getReg .x2 - 1144) :=
    hE 1144 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl
  have htb := A.tbBuf
  have htE := A.cur.inv.heap.hi
  have M := Sides.mm hpre hsz (hPb_of C) Sd Ce fhe
  have hmin : 0 < min sd.2.1.tables.length sd.1.length := by
    have := A.x21
    have : (t.getReg .x21).toNat ≠ 0 := fun h' ↦ h0 (BitVec.eq_of_toNat_eq h')
    omega
  refine ⟨e, hr, b800077c8_pc he, hmin, ⟨hi, by rw [C.rows0.x25]; exact hpre.tablesLen,
    (w.getReg .x25).isLt, ?_, ?_, ?_, ?_, (kk .x22 (by decide)).trans A.x22, ?_, ?_, ?_, ?_,
    (ue 1152 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans F.m1152,
    (tE 1176 (by omega) (by omega) (by omega) (by omega) rfl).trans A.m1176,
    (tE 1184 (by omega) (by omega) (by omega) (by omega) rfl).trans A.m1184, (hE 1232 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans W.1,
    (hE 1224 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans W.2.1,
    (hE 1240 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans W.2.2.1,
    (ue 1192 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans
      (F.m1192.trans SO.bptr), ?_, SO.blocks, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    Ex.keep hpre A.ex Ih A.cur.inv.heap fe hn.ge (kk .x25 (by decide)),
    Mm.blk M (fun _ _ ↦ rfl) (b800077c8_x24 he) ?_⟩
  · rw [kk .x9 (by decide), A.x9, e1160]
  · rw [kk .x18 (by decide), A.x18, e1168]
  · rw [kk .x20 (by decide), m1208]
  · rw [kk .x21 (by decide), m1216]
  · rw [x25h, x25w, hw25]
  · rw [kk .x26 (by decide), m1200]
  · rw [m1200, A.x26, e1160, e1168]; exact SO.beta
  · rw [m1216]; exact A.x21
  · interval_cases i
    · exact hpre.push
    · exact hpre.pull
    · exact hpre.count
  · rw [e1256, e1144]; exact PA
  · rw [e1264, e1248]; exact SO.weights
  · rw [e1264, e1248]; exact SO.wBuf
  · rw [m1272, t1248]
  · rw [kk .x20 (by decide), DFrame.eListNew fe htb (le_refl _) hlo htE fun a h1 h2 hw ↦ by
      simp only [heapStart, heapNext, heapEnd] at h1 h2 htE
      rcases hw with hw | hw <;> addr_omega [hw, h1, h2, htE, hb1]]
    exact A.tb
  · rw [kk .x20 (by decide)]
    exact ⟨htb.1, htb.2.imp_right fun h ↦ ⟨h.1, by rw [hn]; exact h.2⟩⟩
  · rw [b800077c8_x17 he, b800077c8_x16 he, b800077c8_x15 he]; exact eOf3_zero

/-- From `known` into the block loop, or with no block to the sums. -/
theorem blkEnter {bev : MachineState → Word → List E → Option E} {s z w v h₀ h u t : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E}
    {acc : List (List Form) × List E} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E}
    (hpre : BusBalancePre s) (C : SCtx bev s z w v h₀ k state mem mf bf bv)
    (Sd : Sides s z h₀ h (w.getReg .x23) (w.getReg .x25).toNat acc) (SO : SideOk s z h i sd)
    (F : Front s z h u i sd state.point) (D : Dotted s z h u t i sd state.point) (hi : i < 3)
    (hpc : t.pc = 0x8000779c) :
    ∃ e, Reaches Image.code t e ∧
      ((e.pc = 0x800078f0 ∧ 0 < min sd.2.1.tables.length sd.1.length ∧
        Entry s z h e i sd state.point (w.getReg .x23) (w.getReg .x25).toNat ∧
        Ex s h e i sd state.point ∧
        Blk s z h e e i sd state.point (w.getReg .x23) (w.getReg .x25).toNat acc.1 acc.2 0) ∨
      (e.pc = 0x80007b24 ∧ min sd.2.1.tables.length sd.1.length = 0 ∧
        Tl s z h e e i sd state.point (w.getReg .x23) (w.getReg .x25).toNat acc.1 acc.2)) := by
  obtain ⟨t₃, hr₃, A, ⟨h0, hpc₃⟩ | ⟨h0, hpc₃⟩⟩ :=
    enterHead hpre C.fps.inv.mono Sd.inv SO F D hi hpc
  · obtain ⟨e, hr, he, hm, T⟩ := enterNone hpre C Sd F A h0 hpc₃
    exact ⟨e, hr₃.trans hr, Or.inr ⟨he, hm, T⟩⟩
  · obtain ⟨e, hr, he, hm, En, X, B⟩ := enterBlk hpre C Sd SO F A hi h0 hpc₃
    exact ⟨e, hr₃.trans hr, Or.inl ⟨he, hm, En, X, B⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
