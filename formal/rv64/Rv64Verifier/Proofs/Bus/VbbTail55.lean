import Rv64Verifier.Proofs.Bus.VbbTail54
import Rv64Verifier.Proofs.Bus.TsTerminalForms

/-!
# `verify_bus_balance`'s side loop: the block's term of the sum

From `0x800077f8` (the padding weight `pad` in registers): `(1 + bit) * pad` (the weight), times the
selector, and `Form::evaluate` of the block's form at its owner's padding row, to `0x8000787c`
(`Ev`, `accA`). Past `0x800077f8` the owner's register is gone; `Q2` is `Q` without it.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Past `0x800077f8`, from `Cd` at `t₆`. -/
structure Q2 (s z h e t₀ t₆ t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) (P : Word)
    (n : Nat) (forms : List (List Form)) (tot : List E) (k : Nat) : Prop where
  cd : Cd s z h e t₀ t₆ i sd point P n forms tot k
  cur : Cur s z h t
  fr : DFrame t₆ t fun a ↦ QW s a ∨ Within a (s.getReg .x2 - 1136) 8
  hn : heapNext t = heapNext t₆
  m1136 : t.getMem (s.getReg .x2 - 1136) = vecPtr t₆ (s.getReg .x2 - 296)
  x23 : t.getReg .x23 = t₆.getReg .x23
  x24 : t.getReg .x24 = t₆.getReg .x24 + 1

theorem Q2.next {s z h e t₀ t₆ t t' : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat} (hpre : BusBalancePre s)
    (Qt : Q2 s z h e t₀ t₆ t i sd point P n forms tot k) (cur : Cur s z h t')
    (fr : DFrame t t' (QW s)) (hn : heapNext t' = heapNext t)
    (regs : ∀ r ∈ ([.x23, .x24] : List Reg), t'.getReg r = t.getReg r) :
    Q2 s z h e t₀ t₆ t' i sd point P n forms tot k := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine ⟨Qt.cd, cur, Qt.fr.trans (fr.mono fun a ha ↦ Or.inl ha) fun _ h ↦ h, hn.trans Qt.hn, ?_,
    by rw [regs .x23 (by decide), Qt.x23], by rw [regs .x24 (by decide), Qt.x24]⟩
  rw [fr _ fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1]]
  exact Qt.m1136

theorem Q2.blk {s z h e t₀ t₆ t t' : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (Qt : Q2 s z h e t₀ t₆ t i sd point P n forms tot k)
    (fr : DFrame t t' (Within · (s.getReg .x2 - 248) 144)) (sp : t'.getReg .x2 = t.getReg .x2)
    (regs : ∀ r ∈ ([.x23, .x24] : List Reg), t'.getReg r = t.getReg r) :
    Q2 s z h e t₀ t₆ t' i sd point P n forms tot k := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have hN : ∀ q < 8, ¬ Within (nextAddr + BitVec.ofNat 64 q) (s.getReg .x2 - 248) 144 :=
    fun q hq hw ↦ by addr_omega [hw, hq, hb1, hnx]
  have hn : heapNext t' = heapNext t := by simp only [heapNext]; rw [fr nextAddr hN]
  exact Qt.next hpre (Qt.cur.next hpre hsz (StepS.ofDFrame Qt.cur.inv.heap fr (fun _ h ↦ h) hN sp)
    fun a ha ↦ QW.side hpre ha) (fr.mono fun a ha ↦ Or.inl ha) hn regs

theorem Q2.mul (hMul : MulSpec) {s z h e t₀ t₆ u : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (Qu : Q2 s z h e t₀ t₆ u i sd point P n forms tot k)
    (hpc : u.pc = 0x80008c48) {o a b : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 o)
    (h11 : u.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 a)
    (h12 : u.getReg .x12 = s.getReg .x2 - BitVec.ofNat 64 b)
    (ho : 128 ≤ o ∧ o ≤ 248 ∧ o % 8 = 0) (ha : 128 ≤ a ∧ a ≤ 1344 ∧ a % 8 = 0)
    (hb : 128 ≤ b ∧ b ≤ 1344 ∧ b % 8 = 0) (hoa : o + 24 ≤ a ∨ a + 24 ≤ o)
    (hob : o + 24 ≤ b ∨ b + 24 ≤ o) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      Q2 s z h e t₀ t₆ v i sd point P n forms tot k ∧
      DFrame u v (fun x ↦ Within x (s.getReg .x2 - BitVec.ofNat 64 o) 24 ∨
        Within x (s.getReg .x2 - BitVec.ofNat 64 2368) 1024) ∧
      eAt v (s.getReg .x2 - BitVec.ofNat 64 o) =
        eAt u (s.getReg .x2 - BitVec.ofNat 64 a) * eAt u (s.getReg .x2 - BitVec.ofNat 64 b)) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨v, hrv, ⟨hpcv, hp, Cv, fr, hn, hval⟩ | hd⟩ := mulCallC hMul hpre hsz Qu.cur
    (Reaches.refl u) hpc h10 h11 h12 ⟨ho.1, by omega, ho.2.2⟩ ha hb hoa hob
  · refine ⟨v, hrv, Or.inl ⟨hpcv, hp, Qu.next hpre Cv (fr.mono fun x hx ↦ ?_) hn fun r hr ↦ ?_, fr,
      hval⟩⟩
    · rcases hx with hx | hx
      · exact Or.inl (by addr_omega [hx, hb1, ho])
      · exact Or.inr (by addr_omega [hx, hb1])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hp.reg _
  · exact ⟨v, hrv, Or.inr hd⟩

theorem Q2.mm {s z h e t₀ t₆ t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (hPb : n = 0 ∨ heapNext z ≤ P.toNat)
    (Qt : Q2 s z h e t₀ t₆ t i sd point P n forms tot k) :
    Mm s z h e t P n (blkFold point i sd forms (k + 1)).1 tot := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine Qt.cd.mm.keep hpre hsz hPb (Qt.fr.mono fun a ha ↦ ?_) Qt.cur.inv.heap Qt.hn.ge
    (Qt.cur.inv.sp.trans Qt.cd.mm.cur.inv.sp.symm)
  rcases ha with (ha | ha) | ha
  · exact Or.inl (Or.inr (by addr_omega [ha, hb1]))
  · exact Or.inr (Or.inl ha)
  · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))

theorem mul80 (w : Word) :
    w * 64 + w * 16 = BitVec.ofNat 64 (80 * w.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (64 : Word).toNat = 64 from rfl, show (16 : Word).toNat = 16 from rfl]
  omega

/-- At `0x8000787c`: the selector times the weight at `S - 152`, the block's form's value at its
owner's padding row at `S - 248`. -/
structure Ev (s z h e t₀ t₆ t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) (P : Word)
    (n : Nat) (forms : List (List Form)) (tot : List E) (k : Nat) : Prop where
  q : Q2 s z h e t₀ t₆ t i sd point P n forms tot k
  w : eAt t (s.getReg .x2 - BitVec.ofNat 64 152) = (tbSel sd point).getD k 0 *
    ((1 + bitE (s.getMem (blkAddr s i k + 32)) (s.getMem (blkAddr s i k + 24)).toNat) *
      padLow (s.getMem (blkAddr s i k + 32)) point (s.getMem (blkAddr s i k + 24)).toNat)
  ev : eAt t (s.getReg .x2 - BitVec.ofNat 64 248) =
    formEvaluateRust (blockFormRust (blockAt s (blkAddr s i k)) sd.2.2.2.1 sd.2.2.2.2)
      (tables.getD (blkOwner s i k) default).padding
  lr : (s.getMem (blkAddr s i k + 24)).toNat ≤ point.length

/-- A frame slot outside the scratch, past `Cd`, is the block loop's entry's. -/
theorem slot_of_fr {s z h e t₆ t : MachineState} {P : Word} {n : Nat} {fs : List (List Form)}
    {tot : List E} (hpre : BusBalancePre s) (M : Mm s z h e t₆ P n fs tot)
    (fr : DFrame t₆ t fun a ↦ QW s a ∨ Within a (s.getReg .x2 - 1136) 8) {j : Nat} (hj : 8 ≤ j)
    (hj2 : j ≤ 1344) (h1 : j ≤ 1104 ∨ 1144 ≤ j) (h2 : j ≤ 104 ∨ 304 ≤ j) :
    t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine (fr _ fun q hq hw ↦ ?_).trans (M.slots j hj hj2 (blkW_miss hpre hj hj2 h1 h2))
  rcases hw with (hw | hw) | hw <;> addr_omega [hw, hq, hb1, hj, hj2, h1, h2]

/-- An `E` list read only keeps its value. -/
theorem Inv.eList {s u : MachineState} (I : Inv s u) {p : Word} {m : Nat}
    (hr : RO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) p (24 * m)) :
    eListAt u p m = eListAt s p m := by
  have hb := hr.bound
  refine eListAt_congr fun q hq ↦ eAt_congr ?_ ?_ ?_
  · exact I.word hr (by addr_omega [hb, hq]) (by addr_omega [hb, hq])
  · exact I.word hr (by addr_omega [hb, hq]) (by addr_omega [hb, hq])
  · exact I.word hr (by addr_omega [hb, hq]) (by addr_omega [hb, hq])

set_option maxRecDepth 8192 in
/-- From `0x800077f8` to `0x8000787c`. -/
theorem accA (hMul : MulSpec) (hFE : TableSumcheck.FormEvaluateSpecE) {s z h e t₀ t₆ t : MachineState}
    {i : Nat} {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E}
    {P : Word} {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (En : Entry s z h e i sd point P n)
    (Qt : Q s z h e t₀ t₆ t i sd point P n forms tot k) (hpc : t.pc = 0x800077f8)
    (hpad : eOf3 (t.getReg .x12) (t.getReg .x10) (t.getReg .x11) =
      padLow (s.getMem (blkAddr s i k + 32)) point (s.getMem (blkAddr s i k + 24)).toNat) :
    ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
      (t'.pc = 0x8000787c ∧ Ev s z h e t₀ t₆ t' i sd point P n forms tot k)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hS : 1344 ≤ (s.getReg .x2).toNat := by omega
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have sp : t.getReg .x2 = s.getReg .x2 - 1344 := Qt.cur.inv.sp
  have D := Qt.cd
  have slotQ (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 1104 ∨ 1144 ≤ j)
      (h2 : j ≤ 104 ∨ 304 ≤ j) := slot_of_fr hpre D.mm Qt.fr hj hj2 h1 h2
  have own := D.own
  have hnt : n = tables.length := En.nt
  -- `0x800077f8`
  obtain ⟨a₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800077f8_spec hpc (by
    rv_eval [sp]; and_intros <;> valid_access hval [hb1])
  have k₁ := b800077f8_keeps h₁
  have fr₁ : DFrame t a₁ (Within · (s.getReg .x2 - 248) 144) := by
    have := DFrame.of_memFrame (b800077f8_frame h₁ (by rw [sp]; addr_omega [hb1]))
    rw [sp] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have hN : ∀ q < 8, ¬ Within (nextAddr + BitVec.ofNat 64 q) (s.getReg .x2 - 248) 144 :=
    fun q hq hw ↦ by addr_omega [hw, hq, hb1, hnx]
  have hn₁ : heapNext a₁ = heapNext t := by simp only [heapNext]; rw [fr₁ nextAddr hN]
  have C₁ : Cur s z h a₁ := Qt.cur.next hpre hsz (StepS.ofDFrame Qt.cur.inv.heap fr₁ (fun _ h ↦ h) hN
    (k₁ .x2 (by decide))) fun a ha ↦ QW.side hpre ha
  have Q₁ : Q2 s z h e t₀ t₆ a₁ i sd point P n forms tot k :=
    ⟨D, C₁, Qt.fr.trans (fr₁.mono fun a ha ↦ Or.inl (Or.inl ha)) fun _ h ↦ h, hn₁.trans Qt.hn,
      by rw [fr₁ _ fun q hq hw ↦ by addr_omega [hw, hq, hb1]]; exact Qt.m1136,
      by rw [k₁ .x23 (by decide), Qt.regs .x23 (by decide)],
      by rw [b800077f8_x24 h₁, Qt.regs .x24 (by decide)]⟩
  have sp₁ : a₁.getReg .x2 = s.getReg .x2 - 1344 := (k₁ .x2 (by decide)).trans sp
  have e248 : eAt a₁ (s.getReg .x2 - BitVec.ofNat 64 248) =
      1 + bitE (s.getMem (blkAddr s i k + 32)) (s.getMem (blkAddr s i k + 24)).toNat := by
    rw [← bit_eq]
    have m0 := b800077f8_m_x2_1096 h₁
    have m8 := b800077f8_m_x2_1104 h₁
    have m16 := b800077f8_m_x2_1112 h₁
    rw [Qt.x27, Qt.x26] at m0
    rw [sp] at m0 m8 m16
    exact eAt_three hS (by omega) (by omega) (sp_slot (off := 1096) hS (by omega) m0)
      (sp_slot (off := 1104) hS (by omega) m8) (sp_slot (off := 1112) hS (by omega) m16)
  have e128 : eAt a₁ (s.getReg .x2 - BitVec.ofNat 64 128) =
      padLow (s.getMem (blkAddr s i k + 32)) point (s.getMem (blkAddr s i k + 24)).toNat := by
    rw [← hpad]
    have m0 := b800077f8_m_x2_1216 h₁
    have m8 := b800077f8_m_x2_1224 h₁
    have m16 := b800077f8_m_x2_1232 h₁
    rw [sp] at m0 m8 m16
    exact eAt_three hS (by omega) (by omega) (sp_slot (off := 1216) hS (by omega) m0)
      (sp_slot (off := 1224) hS (by omega) m8) (sp_slot (off := 1232) hS (by omega) m16)
  have x8₁ : a₁.getReg .x8 = vecPtr s (s.getReg .x11) + BitVec.ofNat 64 (80 * blkOwner s i k) := by
    rw [b800077f8_x8 h₁, sp, Qt.x19, mul80]
    congr 1
    rw [show s.getReg .x2 - 1344 + (104 : Word) = s.getReg .x2 - BitVec.ofNat 64 1240 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact (slotQ 1240 (by omega) (by omega) (by omega) (by omega)).trans En.tbl
  -- `mul`: the weight `(1 + bit) * pad` into `S - 176`
  obtain ⟨v₁, hrv₁, ⟨hpv₁, hp₁, Qv₁, frv₁, val₁⟩ | hd⟩ := Q₁.mul hMul hpre hsz (b800077f8_pc h₁)
    (o := 176) (a := 248) (b := 128)
    (by rw [b800077f8_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b800077f8_x11 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b800077f8_x12 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by omega) (by omega) (by omega) (by omega) (by omega)
  swap
  · exact ⟨v₁, hr₁.trans hrv₁, Or.inl hd⟩
  rw [e248, e128] at val₁
  have spv₁ : v₁.getReg .x2 = s.getReg .x2 - 1344 := (hp₁.reg .x2).trans sp₁
  -- `0x8000784c`
  obtain ⟨a₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000784c_spec
    (by rw [hpv₁, returnAddress_eq, b800077f8_x1 h₁]; decide) trivial
  have m₂ := b8000784c_mem_same h₂
  have k₂ := b8000784c_keeps h₂
  have Q₂ := Qv₁.blk hpre hsz (DFrame.of_same m₂ _) (k₂ .x2 (by decide)) fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact k₂ _ (by decide)
  have sel₂ : eAt a₂ (s.getReg .x2 - BitVec.ofNat 64 272) = (tbSel sd point).getD k 0 := by
    rw [← D.sel]
    exact Q₂.fr.eAt fun q hq hw ↦ by rcases hw with (hw | hw) | hw <;> addr_omega [hw, hq, hb1]
  have e176₂ : eAt a₂ (s.getReg .x2 - BitVec.ofNat 64 176) =
      (1 + bitE (s.getMem (blkAddr s i k + 32)) (s.getMem (blkAddr s i k + 24)).toNat) *
        padLow (s.getMem (blkAddr s i k + 32)) point (s.getMem (blkAddr s i k + 24)).toNat := by
    rw [eAt_of_same' m₂]; exact val₁
  -- `mul`: the selector times the weight into `S - 152`
  obtain ⟨v₂, hrv₂, ⟨hpv₂, hp₂, Qv₂, frv₂, val₂⟩ | hd⟩ := Q₂.mul hMul hpre hsz (b8000784c_pc h₂)
    (o := 152) (a := 272) (b := 176)
    (by rw [b8000784c_x10 h₂, spv₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b8000784c_x11 h₂, spv₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b8000784c_x12 h₂, spv₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by omega) (by omega) (by omega) (by omega) (by omega)
  swap
  · exact ⟨v₂, hr₁.trans (hrv₁.trans (hr₂.trans hrv₂)), Or.inl hd⟩
  rw [sel₂, e176₂] at val₂
  have spv₂ : v₂.getReg .x2 = s.getReg .x2 - 1344 := (hp₂.reg .x2).trans ((k₂ .x2 (by decide)).trans spv₁)
  have x8₂ : v₂.getReg .x8 = vecPtr s (s.getReg .x11) + BitVec.ofNat 64 (80 * blkOwner s i k) := by
    rw [hp₂.reg .x8, k₂ .x8 (by decide), hp₁.reg .x8, x8₁]
  -- the owner's table and its padding row, read only
  have hTR := hpre.tablesRO
  have hTb := hTR.bound
  have hTs := hTR.stack
  rw [stackLo_eq, stack_eq] at hTs
  have hT : ValidMemRange (vecPtr s (s.getReg .x11)) (10 * tables.length) :=
    Bus.RO.range (n := 10 * tables.length)
      (by rw [show 8 * (10 * tables.length) = 80 * tables.length by omega]; exact hTR)
  have ownT : blkOwner s i k < tables.length := hnt ▸ own
  have hlenT : tables.length = 6 := rfl
  have own6 : blkOwner s i k < 6 := hlenT ▸ ownT
  have hTb6 : (vecPtr s (s.getReg .x11)).toNat + 480 ≤ 2 ^ 64 := by rw [hlenT] at hTb; exact hTb
  rw [hlenT] at hT
  set row := vecPtr s (s.getReg .x11) + BitVec.ofNat 64 (80 * blkOwner s i k) with hrow
  have rdT (q : Nat) (hq : q + 8 ≤ 80) : v₂.getMem (row + BitVec.ofNat 64 q) =
      s.getMem (row + BitVec.ofNat 64 q) :=
    Qv₂.cur.inv.word hTR (by rw [hrow]; addr_omega [hTb6, own6, hq])
      (by rw [hrow]; addr_omega [hTb, ownT, hq, hlenT])
  have hRb : row.toNat + 80 ≤ 2 ^ 64 := by rw [hrow]; addr_omega [hTb6, own6]
  have hRV : ValidMemRange row 10 := by
    intro q hq
    have := hT (10 * blkOwner s i k + q) (by omega)
    rwa [show vecPtr s (s.getReg .x11) + BitVec.ofNat 64 (8 * (10 * blkOwner s i k + q)) =
      row + BitVec.ofNat 64 (8 * q) by rw [hrow]; apply BitVec.eq_of_toNat_eq; addr_omega [hTb6, own6, hq]]
      at this
  have hPR : RO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (vecPtr s row)
      (24 * (vecLen s row).toNat) := hpre.paddingRO _ ownT
  have hPs := hPR.stack
  rw [stackLo_eq, stack_eq] at hPs
  -- `0x80007860`
  obtain ⟨a₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007860_spec
    (by rw [hpv₂, returnAddress_eq, b8000784c_x1 h₂]; decide) (by
      rv_eval [spv₂, x8₂]
      and_intros <;> first
        | valid_access hval [hb1]
        | valid_access hRV [hRb])
  have m₃ := b80007860_mem_same h₃
  have k₃ := b80007860_keeps h₃
  have Q₃ := Qv₂.blk hpre hsz (DFrame.of_same m₃ _) (k₃ .x2 (by decide)) fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact k₃ _ (by decide)
  have sp₃ : a₃.getReg .x2 = s.getReg .x2 - 1344 := (k₃ .x2 (by decide)).trans spv₂
  have x10₃ : a₃.getReg .x10 = s.getReg .x2 - 248 := by
    rw [b80007860_x10 h₃, spv₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₃ : a₃.getReg .x11 = vecPtr t₆ (s.getReg .x2 - 296) := by
    rw [b80007860_x11 h₃, spv₂, show s.getReg .x2 - 1344 + 208 = s.getReg .x2 - 1136 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact Qv₂.m1136
  have x12₃ : a₃.getReg .x12 = vecLen t₆ (s.getReg .x2 - 296) := by
    rw [b80007860_x12 h₃, Qv₂.x23]; exact D.x23
  have x13₃ : a₃.getReg .x13 = vecPtr s row := by
    rw [b80007860_x13 h₃, x8₂]; exact rdT 8 (by omega)
  have x14₃ : a₃.getReg .x14 = vecLen s row := by
    rw [b80007860_x14 h₃, x8₂]; exact rdT 16 (by omega)
  -- the block's form, in the heap
  have okF := D.ok
  have lenF := D.len
  have hraw := okF.vec.raw
  have hlF := okF.vec.len
  have h₆E := D.mm.cur.inv.heap.hi
  simp only [RawVecOk, Buf] at hraw
  have fB : heapStart ≤ (vecPtr t₆ (s.getReg .x2 - 296)).toNat ∧
      (vecPtr t₆ (s.getReg .x2 - 296)).toNat + 48 * (vecLen t₆ (s.getReg .x2 - 296)).toNat ≤
        heapNext t₆ := by
    rcases hraw.2 with h0 | h0
    · omega
    · exact ⟨h0.1, by omega⟩
  obtain ⟨fB1, fB2⟩ := fB
  simp only [heapStart, heapNext, heapEnd] at fB1 fB2 h₆E
  have hsl : stackLo a₃ formEvaluateStack = s.getReg .x2 - BitVec.ofNat 64 2512 := by
    simp only [stackLo, formEvaluateStack, mulStack, Nat.reduceAdd, sp₃]
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hrs := hpre.stack.rodata
  simp only [stack_eq] at hrs
  have pre : TableSumcheck.FormEvaluatePreE a₃ := {
    ret := by
      rw [x10₃]; simp only [Region, Mapped]
      exact ⟨Or.inr ⟨by addr_omega [hb1], by addr_omega [hb1, hb2]⟩, by addr_omega [hb1, hb3]⟩
    terms := by
      rw [x11₃, x12₃]; right; simp only [Region, Mapped]
      exact ⟨Or.inl ⟨by omega, by omega⟩, hraw.1⟩
    columns := by rw [x13₃, x14₃]; exact hPR.region
    stack := hpre.stack.sub 1344 sp₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    retStack := by rw [x10₃, hsl]; addr_omega [hb1]
    termsStack := by rw [x11₃, x12₃, hsl]; addr_omega [hb1, fB2, h₆E]
    columnsStack := by
      rw [x13₃, x14₃, hsl]
      have hPb := hPR.bound
      rcases hPs with h0 | h0 | h0 | h0
      · exact Or.inl h0
      · omega
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h0, hb1, hPb])))
      · exact Or.inr (Or.inr (Or.inr (by addr_omega [h0, hb1, hPb])))
    rodata := Q₃.cur.inv.rodata hpre
    retRodata := by rw [x10₃]; addr_omega [hrs, hb1] }
  obtain ⟨v₃, hrv₃, ⟨hpv₃, hp₃, post⟩ | hd⟩ := hFE.call (Reaches.refl a₃) (b80007860_pc h₃) pre
  swap
  · exact ⟨v₃, hr₁.trans (hrv₁.trans (hr₂.trans (hrv₂.trans (hr₃.trans hrv₃)))), Or.inl hd⟩
  have fr₃ := post.frame
  rw [x10₃, hsl] at fr₃
  have hn₃ : heapNext v₃ = heapNext a₃ := by
    simp only [heapNext]
    rw [fr₃ nextAddr fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1, hnx]]
  have hv₃ : HeapOk v₃ := by have := Q₃.cur.inv.heap; exact ⟨hn₃ ▸ this.lo, hn₃ ▸ this.hi⟩
  have Q₄ : Q2 s z h e t₀ t₆ v₃ i sd point P n forms tot k := by
    refine Q₃.next hpre (Q₃.cur.next hpre hsz (A := fun a ↦ Within a (s.getReg .x2 - 248) 24)
      ⟨fr₃.mono fun a ha ↦ ?_, hv₃, hn₃.ge, hp₃.reg .x2⟩ fun a ha ↦ QW.side hpre (by
        addr_omega [ha, hb1])) (fr₃.mono fun a ha ↦ ?_) hn₃ fun r hr ↦ ?_
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (by addr_omega [ha, hb1])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hp₃.reg _
  have hv := post.value
  rw [x10₃, x11₃, x12₃, x13₃, x14₃, Inv.eList Q₃.cur.inv hPR,
    Q₃.fr.termsAt fun q hq hw ↦ by
      rcases hw with (hw | hw) | hw <;> addr_omega [hw, hq, hb1, fB1, fB2, h₆E]] at hv
  refine ⟨v₃, hr₁.trans (hrv₁.trans (hr₂.trans (hrv₂.trans (hr₃.trans hrv₃)))),
    Or.inr ⟨by rw [hpv₃, returnAddress_eq, b80007860_x1 h₃]; decide, Q₄, ?_, ?_, Qt.lr⟩⟩
  · rw [fr₃.eAt fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1],
      eAt_of_same' m₃]
    exact val₂
  · rw [← D.form, formEvaluateRust_eq, ← LayoutMirror.FormRust.evaluate_eq, ← hpre.padding _ ownT]
    exact hv

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
