import Rv64Verifier.Proofs.Bus.VbbTail52

/-!
# `verify_bus_balance`'s side loop: the block's checks

From `0x80007a34` (`Cd`): the owner's and the point's checks and the block's `log_rows` and `rows`
into `s10` and `s11` (`cdChecks`), to the padding weight's loop or past it. From there to the next
block the iteration writes only `S - [248, 104)` and the stack below the frame (`QW`), so `Q`
carries `Cd` along (`Q.next`, `Q.mm`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Arithmetic and block facts -/

theorem not_and_one (y : Word) : (y ^^^ 0xffffffffffffffff) &&& 1 = 1 ^^^ (y &&& 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases h : i = 0
  · subst h; simp
  · simp [BitVec.getLsbD_one, h]

/-- The code's `1 + bit`. -/
theorem bit_eq (n : Word) (k : Nat) :
    eOf3 (((n >>> (k % 64)) ^^^ 0xffffffffffffffff) &&& 1) 0 0 = 1 + bitE n k := by
  apply eq_of_limbs
  rw [limbs_eOf3', limbs_add, limbs_one, bitE, limbs_eNew, not_and_one]
  simp

theorem padLow_take (n : BitVec 64) (point : List E) (L : Nat) :
    ∀ k ≤ L, padLow n (point.take L) k = padLow n point k
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [padLow, padLow_take n point L k (by omega)]
    congr 1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (show k < L by omega)]

theorem b80007a68_x25' {s t : MachineState} (h : b80007a68.Holds s t) :
    t.getReg .x25 = ((s.getReg .x27 >>> ((s.getReg .x9).toNat % 64)) ^^^ 0xffffffffffffffff) &&& 1 :=
  h.reg_eq .x25 rfl (by rv_eval [])

theorem b80007a68_m_x2_1192 {s t : MachineState} (h : b80007a68.Holds s t) :
    t.getMem (s.getReg .x2 + 1192) =
      ((s.getReg .x27 >>> ((s.getReg .x9).toNat % 64)) ^^^ 0xffffffffffffffff) &&& 1 :=
  h.mem_eq 3 (by decide) (by rv_eval []) (by rv_eval [])

theorem b80007a68_frame' {s t : MachineState} (h : b80007a68.Holds s t)
    (hb : (s.getReg .x2).toNat + 1240 ≤ 2 ^ 64) (h18 : s.getReg .x18 = s.getReg .x2 + 1200) :
    MemFrame s t (s.getReg .x2 + 1096) 144 :=
  h.memFrame (by rv_eval [h18]; and_intros <;> addr_omega [hb])

theorem b800077f8_m_x2_1096 {s t : MachineState} (h : b800077f8.Holds s t) :
    t.getMem (s.getReg .x2 + 1096) =
      ((s.getReg .x27 >>> ((s.getReg .x26).toNat % 64)) ^^^ 0xffffffffffffffff) &&& 1 :=
  h.mem_eq 0 (by decide) (by rv_eval []) (by rv_eval [])

/-- Block `k`'s words, read only. -/
theorem blkRead {s z h e t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n k : Nat} (En : Entry s z h e i sd point P n) (hk : k < sd.1.length) (It : Inv s t) {q : Nat}
    (hq : q + 8 ≤ 48) :
    t.getMem (blkAddr s i k + BitVec.ofNat 64 q) = s.getMem (blkAddr s i k + BitVec.ofNat 64 q) := by
  have hro0 := En.bro.blocks
  have hlen : (vecLen s (blkVec s i)).toNat = sd.1.length := by
    rw [← En.blocks, blocksAt, List.length_map, List.length_range]
  rw [hlen] at hro0
  have hBb := hro0.bound
  exact It.word hro0 (by simp only [blkAddr]; addr_omega [hBb, hk, hq])
    (by simp only [blkAddr]; addr_omega [hBb, hk, hq])

theorem blkValid {s z h e : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n k : Nat} (En : Entry s z h e i sd point P n) (hk : k < sd.1.length) :
    ValidMemRange (blkAddr s i k) 6 := by
  have hro0 := En.bro.blocks
  have hlen : (vecLen s (blkVec s i)).toNat = sd.1.length := by
    rw [← En.blocks, blocksAt, List.length_map, List.length_range]
  rw [hlen] at hro0
  have hBb := hro0.bound
  have hvB : ValidMemRange (vecPtr s (blkVec s i)) (6 * sd.1.length) :=
    Bus.RO.range (n := 6 * sd.1.length)
      (by rw [show 8 * (6 * sd.1.length) = 48 * sd.1.length by omega]; exact hro0)
  intro q hq
  have := hvB (6 * k + q) (by omega)
  simp only [blkAddr] at this ⊢
  rwa [show vecPtr s (blkVec s i) + BitVec.ofNat 64 (48 * k) + BitVec.ofNat 64 (8 * q) =
    vecPtr s (blkVec s i) + BitVec.ofNat 64 (8 * (6 * k + q)) by
      apply BitVec.eq_of_toNat_eq; addr_omega [hBb, hk, hq]]

/-! ## Past the checks -/

/-- What the iteration writes past the owner's form: `S - [248, 104)` and the stack. -/
def QW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 248) 144 ∨ Within a (s.getReg .x2 - 4544) 3200

/-- Past the checks, from `Cd` at `t₆`. -/
structure Q (s z h e t₀ t₆ t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) (P : Word)
    (n : Nat) (forms : List (List Form)) (tot : List E) (k : Nat) : Prop where
  cd : Cd s z h e t₀ t₆ i sd point P n forms tot k
  cur : Cur s z h t
  fr : DFrame t₆ t fun a ↦ QW s a ∨ Within a (s.getReg .x2 - 1136) 8
  hn : heapNext t = heapNext t₆
  m1136 : t.getMem (s.getReg .x2 - 1136) = vecPtr t₆ (s.getReg .x2 - 296)
  regs : ∀ r ∈ ([.x2, .x23, .x24] : List Reg), t.getReg r = t₆.getReg r
  x19 : t.getReg .x19 = s.getMem (blkAddr s i k + 40)
  x26 : t.getReg .x26 = s.getMem (blkAddr s i k + 24)
  x27 : t.getReg .x27 = s.getMem (blkAddr s i k + 32)
  lr : (s.getMem (blkAddr s i k + 24)).toNat ≤ point.length

theorem QW.side {s z u : MachineState} (hpre : BusBalancePre s) {a : Word}
    (h : Within a (s.getReg .x2 - 248) 144) : SideW s z u a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb1])))))))

/-- A step writing `QW`, keeping `NEXT`, the registers `Q` names. -/
theorem Q.next {s z h e t₀ t₆ t t' : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat} (hpre : BusBalancePre s)
    (Qt : Q s z h e t₀ t₆ t i sd point P n forms tot k) (cur : Cur s z h t')
    (fr : DFrame t t' (QW s)) (hn : heapNext t' = heapNext t)
    (regs : ∀ r ∈ ([.x2, .x19, .x23, .x24, .x26, .x27] : List Reg), t'.getReg r = t.getReg r) :
    Q s z h e t₀ t₆ t' i sd point P n forms tot k := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine ⟨Qt.cd, cur, Qt.fr.trans (fr.mono fun a ha ↦ Or.inl ha) fun _ h ↦ h, hn.trans Qt.hn, ?_,
    fun r hr ↦ ?_, by rw [regs .x19 (by decide), Qt.x19], by rw [regs .x26 (by decide), Qt.x26],
    by rw [regs .x27 (by decide), Qt.x27], Qt.lr⟩
  · rw [fr _ fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1]]
    exact Qt.m1136
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [regs _ (by decide), Qt.regs _ (by decide)]

/-- `Mm` past the checks. -/
theorem Q.mm {s z h e t₀ t₆ t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (hPb : n = 0 ∨ heapNext z ≤ P.toNat)
    (Qt : Q s z h e t₀ t₆ t i sd point P n forms tot k) :
    Mm s z h e t P n (blkFold point i sd forms (k + 1)).1 tot := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine Qt.cd.mm.keep hpre hsz hPb (Qt.fr.mono fun a ha ↦ ?_) Qt.cur.inv.heap Qt.hn.ge
    ((Qt.regs .x2 (by decide)))
  rcases ha with (ha | ha) | ha
  · exact Or.inl (Or.inr (by addr_omega [ha, hb1]))
  · exact Or.inr (Or.inl ha)
  · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))

set_option maxRecDepth 8192 in
/-- The checks, to the padding weight's loop (`log_rows > 0`) or past it. -/
theorem cdChecks {s z h e t₀ t₆ : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (En : Entry s z h e i sd point P n)
    (B : Blk s z h e t₀ i sd point P n forms tot k) (hk : k < min sd.2.1.tables.length sd.1.length)
    (D : Cd s z h e t₀ t₆ i sd point P n forms tot k) (hpc : t₆.pc = 0x80007a34) :
    ∃ t, Reaches Image.code t₆ t ∧ (Dead Image.code t ∨ (Q s z h e t₀ t₆ t i sd point P n forms tot k ∧
      ((s.getMem (blkAddr s i k + 24) = 0 ∧ t.pc = 0x800077f4 ∧ t.getReg .x10 = 0 ∧
          t.getReg .x11 = 0) ∨
        (s.getMem (blkAddr s i k + 24) ≠ 0 ∧ t.pc = 0x80007a68 ∧
          t.getReg .x8 = e.getMem (s.getReg .x2 - 1256) ∧ t.getReg .x9 = 0 ∧
          t.getReg .x10 = 0 ∧ t.getReg .x11 = 0 ∧ t.getReg .x12 = 1 ∧
          t.getReg .x18 = s.getReg .x2 - 144)))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hkB : k < sd.1.length := lt_of_lt_of_le hk (min_le_right _ _)
  have hro0 := En.bro.blocks
  have hlen : (vecLen s (blkVec s i)).toNat = sd.1.length := by
    rw [← En.blocks, blocksAt, List.length_map, List.length_range]
  rw [hlen] at hro0
  have hBb := hro0.bound
  have hBs := hro0.stack
  rw [stackLo_eq, stack_eq] at hBs
  have hvB : ValidMemRange (vecPtr s (blkVec s i)) (6 * sd.1.length) :=
    Bus.RO.range (n := 6 * sd.1.length)
      (by rw [show 8 * (6 * sd.1.length) = 48 * sd.1.length by omega]; exact hro0)
  have M := D.mm
  have C₆ := M.cur
  have I₆ := C₆.inv
  have sp₆ : t₆.getReg .x2 = s.getReg .x2 - 1344 := I₆.sp
  have x27₆ := D.x27
  have rd (q : Nat) (hq : q + 8 ≤ 48) := blkRead En hkB I₆ hq
  -- `0x80007a34`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007a34_spec hpc (by
    rv_eval [x27₆]; simp only [blkAddr]; valid_access hvB [hBb, hkB])
  have m₁ := b80007a34_mem_same h₁
  have k₁ := b80007a34_keeps h₁
  have e40 : t₆.getMem (t₆.getReg .x27 + 40) = s.getMem (blkAddr s i k + 40) := by
    rw [x27₆]; exact rd 40 (by omega)
  have x25₆ : t₆.getReg .x25 = BitVec.ofNat 64 n :=
    (D.regs .x25 (by decide)).trans ((B.regs .x25 (by decide)).trans En.x25)
  have own := D.own
  have hn64 := En.n64
  have pc₁ := b80007a34_pc_not_taken h₁ (by
    rw [e40, x25₆, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]; exact own)
  -- `0x80007a3c`
  have x27₁ : t₁.getReg .x27 = blkAddr s i k := by rw [k₁ .x27 (by decide), x27₆]
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007a3c_spec pc₁ (by
    rv_eval [x27₁]; simp only [blkAddr]; valid_access hvB [hBb, hkB])
  have m₂ := b80007a3c_mem_same h₂
  have k₂ := b80007a3c_keeps h₂
  have e24 : t₁.getMem (t₁.getReg .x27 + 24) = s.getMem (blkAddr s i k + 24) := by
    rw [x27₁, m₁]; exact rd 24 (by omega)
  have x20₁ : t₁.getReg .x20 = e.getMem (s.getReg .x2 - 1144) := by
    rw [k₁ .x20 (by decide)]; exact D.x20
  have hpl : (e.getMem (s.getReg .x2 - 1144)).toNat = point.length := by
    have := En.pt.elems; rw [← this, eListAt_length]
  by_cases hd : (e.getMem (s.getReg .x2 - 1144)).toNat < (s.getMem (blkAddr s i k + 24)).toNat
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl (dead_of_fetch (by
      rw [b80007a3c_pc_taken h₂ (by rw [x20₁, e24]; exact hd)]
      exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have pc₂ := b80007a3c_pc_not_taken h₂ (by rw [x20₁, e24]; omega)
  -- `0x80007a44`
  have x27₂ : t₂.getReg .x27 = blkAddr s i k := by rw [k₂ .x27 (by decide), x27₁]
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1344 := by
    rw [k₂ .x2 (by decide), k₁ .x2 (by decide), sp₆]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007a44_spec pc₂ (by
    rv_eval [x27₂, sp₂]
    and_intros <;> first
      | valid_access hval [hb1]
      | (simp only [blkAddr]; valid_access hvB [hBb, hkB])
      | (simp only [blkAddr]; addr_omega [hb1, hBb, hBs, hkB]))
  have m₃ := b80007a44_m_x2_208 h₃
  have k₃ := b80007a44_keeps h₃
  have fr₃ : DFrame t₂ t₃ (Within · (s.getReg .x2 - 1136) 8) := by
    have := DFrame.of_memFrame (b80007a44_frame h₃ (by rw [sp₂]; addr_omega [hb1]))
    rw [sp₂] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have hn₃ : heapNext t₃ = heapNext t₆ := by
    simp only [heapNext]; rw [fr₃ nextAddr fun q hq hw ↦ by addr_omega [hw, hq, hb1, hnx], m₂, m₁]
  have st : StepS s t₆ t₃ (Within · (s.getReg .x2 - 1136) 8) :=
    ⟨((DFrame.of_same m₁ _).trans (DFrame.of_same m₂ _) fun _ h ↦ h).trans
      (fr₃.mono fun a ha ↦ Or.inl ha) fun _ h ↦ h, by
        have := I₆.heap; exact ⟨hn₃ ▸ this.lo, hn₃ ▸ this.hi⟩, hn₃.ge,
      by rw [k₃ .x2 (by decide), sp₂, sp₆]⟩
  have C₃ : Cur s z h t₃ := C₆.next hpre hsz st fun a ha ↦ Or.inl (by
    simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
  have x26₂ : t₂.getReg .x26 = s.getMem (blkAddr s i k + 24) := by
    rw [b80007a3c_x26 h₂, e24]
  have x26₃ : t₃.getReg .x26 = s.getMem (blkAddr s i k + 24) := by
    rw [k₃ .x26 (by decide), x26₂]
  have Q₃ : Q s z h e t₀ t₆ t₃ i sd point P n forms tot k := by
    refine ⟨D, C₃, ((DFrame.of_same m₁ _).trans (DFrame.of_same m₂ _) fun _ h ↦ h).trans
      (fr₃.mono fun a ha ↦ Or.inr ha) fun _ h ↦ h, hn₃, ?_, fun r hr ↦ ?_, ?_, x26₃, ?_, ?_⟩
    · rw [show s.getReg .x2 - 1136 = t₂.getReg .x2 + 208 by rw [sp₂]; rv_eval [], m₃,
        k₂ .x9 (by decide), k₁ .x9 (by decide)]
      exact D.x9
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [k₃ _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]
    · rw [k₃ .x19 (by decide), k₂ .x19 (by decide), b80007a34_x19 h₁, e40]
    · rw [b80007a44_x27 h₃, x27₂, m₂, m₁]; exact rd 32 (by omega)
    · omega
  by_cases hL : s.getMem (blkAddr s i k + 24) = 0
  · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨Q₃, Or.inl ⟨hL, b80007a44_pc_taken h₃ (by
      rw [x26₂]; exact hL), b80007a44_x10 h₃, b80007a44_x11 h₃⟩⟩⟩
  have pc₃ := b80007a44_pc_not_taken h₃ (by rw [x26₂]; exact hL)
  -- `0x80007a58`
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1344 := by rw [k₃ .x2 (by decide), sp₂]
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80007a58_spec pc₃ (by
    rv_eval [sp₃]; valid_access hval [hb1])
  have m₄ := b80007a58_mem_same h₄
  have k₄ := b80007a58_keeps h₄
  have hn₄ : heapNext t₄ = heapNext t₃ := by simp only [heapNext, m₄]
  have Q₄ := Q₃.next hpre (C₃.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₄ C₃.inv.heap (k₄ .x2 (by decide))) fun _ h ↦ h.elim) (DFrame.of_same m₄ _) hn₄
    fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₄ _ (by decide)
  have e1256 : t₃.getMem (s.getReg .x2 - 1256) = e.getMem (s.getReg .x2 - 1256) := by
    rw [fr₃ _ fun q hq hw ↦ by addr_omega [hw, hq, hb1], m₂, m₁]
    exact M.slots 1256 (by omega) (by omega) (blkW_miss hpre (by omega) (by omega) (by omega)
      (by omega))
  refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr ⟨Q₄, Or.inr ⟨hL, b80007a58_pc h₄, ?_,
    b80007a58_x9 h₄, ?_, ?_, b80007a58_x12 h₄, ?_⟩⟩⟩
  · rw [b80007a58_x8 h₄, sp₃]; rv_eval []; exact e1256
  · rw [k₄ .x10 (by decide), b80007a44_x10 h₃]
  · rw [k₄ .x11 (by decide), b80007a44_x11 h₃]
  · rw [b80007a58_x18 h₄, sp₃]; rv_eval []

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
