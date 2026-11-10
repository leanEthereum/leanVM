import Rv64Verifier.Proofs.Bus.VbbTail43

/-!
# `verify_bus_balance`'s side loop: the block loop's invariant

The block loop (`0x800078f0`, counter `s8`) folds `busBlockStepRust` over the tables' selectors
zipped with the side's blocks (`blkFold`). From its entry `e` (`Entry`: what the loop reads of the
frame) to its head after `k` blocks (`Blk`), it writes only its scratch slots (`BlkW`), the forms'
pieces and the heap it allocates; the heap allocated in the iteration, from `h`'s `NEXT` to `e`'s,
is kept, and no piece lies there (`Blk.gap`). `termC` is `Form::term` into `S - 296`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- The block loop's scratch slots: `S - [1136, 1104)` and `S - [296, 104)`. -/
def BlkW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1136) 32 ∨ Within a (s.getReg .x2 - 296) 192

/-- What a stretch of an iteration from `t₀` to `t` writes: the scratch slots, the stack below the
frame, `NEXT` and the heap from `t₀`'s `NEXT` on. -/
def ItW (s t₀ t : MachineState) (a : Word) : Prop :=
  BlkW s a ∨ Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨
    (heapNext t₀ ≤ a.toNat ∧ a.toNat < heapNext t)

/-- The tables' selectors of side `sd` at `point`. -/
def tbSel (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) : List E :=
  sd.2.1.tables.map (·.eqAbove point)

/-- The block loop's fold after `k` blocks, from the forms `forms`. -/
def blkFold (point : List E) (i : Nat) (sd : List BusBlock × BusLayoutRust × List E × List E × E)
    (forms : List (List Form)) (k : Nat) : List (List Form) × E :=
  (((tbSel sd point).zip sd.1).take k).foldl (busBlockStepRust point i sd.2.2.2.1 sd.2.2.2.2)
    (forms, 0)

/-- Side `i`'s blocks' `Vec`, in the `Layout`. -/
def blkVec (s : MachineState) (i : Nat) : Word := s.getReg .x11 + BitVec.ofNat 64 (24 * (i + 1))

/-- At the block loop's entry `e`: what the loop reads of the frame and the registers. -/
structure Entry (s z h e : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) (P : Word)
    (n : Nat) : Prop where
  i3 : i < 3
  nt : n = tables.length
  n64 : n < 2 ^ 64
  x9 : e.getReg .x9 = e.getMem (s.getReg .x2 - 1160)
  x18 : e.getReg .x18 = e.getMem (s.getReg .x2 - 1168)
  x20 : e.getReg .x20 = e.getMem (s.getReg .x2 - 1208)
  x21 : e.getReg .x21 = e.getMem (s.getReg .x2 - 1216)
  x22 : e.getReg .x22 = BitVec.ofNat 64 i
  x25 : e.getReg .x25 = BitVec.ofNat 64 n
  x26 : e.getReg .x26 = e.getMem (s.getReg .x2 - 1200)
  beta : eOf3 (e.getMem (s.getReg .x2 - 1200)) (e.getMem (s.getReg .x2 - 1160))
    (e.getMem (s.getReg .x2 - 1168)) = sd.2.2.2.2
  m : (e.getMem (s.getReg .x2 - 1216)).toNat = min sd.2.1.tables.length sd.1.length
  i1152 : e.getMem (s.getReg .x2 - 1152) = BitVec.ofNat 64 i
  i1176 : e.getMem (s.getReg .x2 - 1176) = BitVec.ofNat 64 (8 * i)
  i1184 : e.getMem (s.getReg .x2 - 1184) = BitVec.ofNat 64 (16 * i)
  n1232 : e.getMem (s.getReg .x2 - 1232) = BitVec.ofNat 64 n
  p1224 : e.getMem (s.getReg .x2 - 1224) = P
  tbl : e.getMem (s.getReg .x2 - 1240) = vecPtr s (s.getReg .x11)
  blk : e.getMem (s.getReg .x2 - 1192) = vecPtr s (blkVec s i)
  bro : BlocksRO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (blkVec s i)
  blocks : blocksAt s (blkVec s i) = sd.1
  pt : PointAt z h (e.getMem (s.getReg .x2 - 1256)) (e.getMem (s.getReg .x2 - 1144)) point
  wts : eListAt h (e.getMem (s.getReg .x2 - 1264)) (e.getMem (s.getReg .x2 - 1248)).toNat =
    sd.2.2.2.1
  wBuf : LowBuf (e.getMem (s.getReg .x2 - 1264)) (24 * (e.getMem (s.getReg .x2 - 1248)).toNat)
      (heapNext z) ∨
    (e.getMem (s.getReg .x2 - 1264) = 0xa00000b0 ∧ e.getMem (s.getReg .x2 - 1248) = 1)
  w1272 : e.getMem (s.getReg .x2 - 1272) = e.getMem (s.getReg .x2 - 1248) + 1
  tb : eListAt e (e.getReg .x20) sd.2.1.tables.length = tbSel sd point
  tbBuf : NewBuf h e (e.getReg .x20) (24 * sd.2.1.tables.length) 8

/-- At the block loop's head after `k` blocks (`t`, from the entry `e`), from the forms `forms` and
the totals `tot` of the side loop's head `h`. -/
structure Blk (s z h e t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) (P : Word)
    (n : Nat) (forms : List (List Form)) (tot : List E) (k : Nat) : Prop where
  cur : Cur s z h t
  slots : ∀ j, 8 ≤ j → j ≤ 1344 → (∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 8 → ¬ BlkW s y) →
    t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = e.getMem (s.getReg .x2 - BitVec.ofNat 64 j)
  regs : ∀ r ∈ ([.x2, .x9, .x18, .x20, .x21, .x22, .x25, .x26] : List Reg), t.getReg r = e.getReg r
  x24 : t.getReg .x24 = BitVec.ofNat 64 k
  acc : eOf3 (t.getReg .x17) (t.getReg .x16) (t.getReg .x15) = (blkFold point i sd forms k).2
  mat : Mat z t P n
  below : ∀ a < n, ∀ j < 3, (vecPtr t (cellAt t (rowAt P a) j)).toNat +
    48 * (vecLen t (cellAt t (rowAt P a) j)).toNat ≤ heapNext t
  value : formRowsAt t P n = (blkFold point i sd forms k).1
  gap : ∀ a < n, ∀ j ≤ 3, ∀ x, piece t P a j x → x.toNat < heapNext h ∨ heapNext e ≤ x.toNat
  mono : heapNext e ≤ heapNext t
  hk : HeapKept h e t (heapNext e)
  totals : NewVecE z t (s.getReg .x2 - 632) tot
  tbuf : ∀ x, Within x (vecPtr t (s.getReg .x2 - 632)) (24 * (vecCap t (s.getReg .x2 - 632)).toNat) →
    ¬ Within x P (24 * n) ∧ ∀ a < n, ∀ j ≤ 3, ¬ piece t P a j x

theorem ItW.mono {s t₀ t t' : MachineState} (h : heapNext t ≤ heapNext t') {a : Word}
    (ha : ItW s t₀ t a) : ItW s t₀ t' a := by
  rcases ha with ha | ha | ha | ⟨a1, a2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ⟨a1, by omega⟩))

theorem ItW.base {s t₀ t₁ t : MachineState} (h : heapNext t₀ ≤ heapNext t₁) {a : Word}
    (ha : ItW s t₁ t a) : ItW s t₀ t a := by
  rcases ha with ha | ha | ha | ⟨a1, a2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, a2⟩))

/-- A frame slot outside the scratch misses `ItW`. -/
theorem ItW.slot {s t₀ t : MachineState} (hpre : BusBalancePre s) (ht : HeapOk t) {j : Nat}
    (hj : 8 ≤ j) (hj2 : j ≤ 1344) (hx : ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 8 → ¬ BlkW s y) :
    ∀ k < 8, ¬ ItW s t₀ t (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 k) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have hh := ht.hi
  simp only [heapNext, heapEnd] at hh
  intro k hk hw
  have hy : Within (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 k)
      (s.getReg .x2 - BitVec.ofNat 64 j) 8 := by addr_omega [hk, hb1, hj, hj2]
  rcases hw with hw | hw | hw | ⟨-, hw⟩
  · exact hx _ hy hw
  · addr_omega [hw, hk, hb1, hj, hj2]
  · addr_omega [hw, hk, hb1, hj, hj2, hnx]
  · simp only [heapNext] at hw; addr_omega [hw, hk, hb1, hj, hj2, hh]

/-- A heap address below `t₀`'s `NEXT` misses `ItW`. -/
theorem ItW.low {s t₀ t : MachineState} (hpre : BusBalancePre s) (h0 : HeapOk t₀) {a : Word}
    (h1 : heapStart ≤ a.toNat) (h2 : a.toNat < heapNext t₀) : ¬ ItW s t₀ t a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := h0.hi
  simp only [heapNext, heapEnd, heapStart] at hh h1 h2
  rintro (hw | hw | hw | ⟨hw, -⟩)
  · rcases hw with hw | hw <;> addr_omega [hw, h1, h2, hh, hb1]
  · addr_omega [hw, h1, h2, hh, hb1]
  · simp only [nextAddr] at hw; addr_omega [hw, h1, h2, hh]
  · simp only [heapNext] at hw; omega

/-- `Form::term(S - 296, S - 248, S - 128)` with the `One` monomial: `constant` of `S - 128`. -/
theorem termC (hTm : Layout.TermSpec) {s z h u : MachineState} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (C : Cur s z h u) (hpc : u.pc = 0x800050a8)
    (h10 : u.getReg .x10 = s.getReg .x2 - 296) (h11 : u.getReg .x11 = s.getReg .x2 - 248)
    (h12 : u.getReg .x12 = s.getReg .x2 - 128) (htag : u.getMem (s.getReg .x2 - 248) = 0) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Cur s z h v ∧
      DFrame u v (fun a ↦ Within a (s.getReg .x2 - 296) 24 ∨ Within a (s.getReg .x2 - 4544) 3200 ∨
        Within a nextAddr 8 ∨ (heapNext u ≤ a.toNat ∧ a.toNat < heapNext v)) ∧
      heapNext u ≤ heapNext v ∧ Layout.FormOk v (s.getReg .x2 - 296) ∧
      (∀ x, Layout.formBuf v (s.getReg .x2 - 296) x → heapNext u ≤ x.toNat ∧ x.toNat < heapNext v) ∧
      Layout.formOf v (s.getReg .x2 - 296) = LayoutMirror.constantRust (eAt u (s.getReg .x2 - 128))) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hab hnx
  have I := C.inv
  have hsl : stackLo u Layout.termStack = s.getReg .x2 - BitVec.ofNat 64 1424 := by
    simp only [stackLo, Layout.termStack, I.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have pre : Layout.TermPre u := {
    heap := I.heap
    stack := hpre.stack.sub 1344 I.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    out := by rw [h10]; valid_sub hval [hb1]
    mono := by rw [h11]; valid_sub hval [hb1]
    coeff := by rw [h12]; valid_sub hval [hb1]
    monoOk := by rw [h11]; simp only [Layout.MonoOk, htag]; decide
    outFree := by
      have hh := I.heap.hi
      rw [h10]; simp only [Outside, heapNext, heapEnd] at hh ⊢; addr_omega [hb1, hh, hnx]
    monoNext := by rw [h11]; addr_omega [hb1, hnx]
    coeffNext := by rw [h12]; addr_omega [hb1, hnx]
    outStack := by rw [h10, hsl]; addr_omega [hb1]
    monoStack := by rw [h11, hsl]; addr_omega [hb1]
    coeffStack := by rw [h12, hsl]; addr_omega [hb1] }
  obtain ⟨v, hrv, ⟨hpcv, hp, N, hval'⟩ | hd⟩ := hTm.call (Reaches.refl u) hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  rw [h10] at N hval'
  rw [h11, h12] at hval'
  have frL : DFrame u v fun a ↦ Within a (s.getReg .x2 - 296) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 1424) 80 ∨ Within a nextAddr 8 ∨ Fresh u v a := by
    have := layoutFrame hrv N.frame; rw [hsl] at this; exact this
  have fr : DFrame u v fun a ↦ Within a (s.getReg .x2 - 296) 24 ∨
      Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨
        (heapNext u ≤ a.toNat ∧ a.toNat < heapNext v) := frL.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ha))
  have st : StepS s u v (Within · (s.getReg .x2 - 296) 24) :=
    ⟨frL.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ha)), N.heap, N.mono, hp.reg .x2⟩
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, C.next hpre hsz st fun a ha ↦ Or.inl ?_, fr, N.mono, N.ok,
    fun x hx ↦ ?_, ?_⟩⟩
  · simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
  · have hf := N.fresh
    simp only [NewBuf] at hf
    simp only [Layout.formBuf, Within] at hx
    rcases hf.2 with h0 | ⟨b1, b2⟩
    · omega
    · exact ⟨by omega, by omega⟩
  · rw [hval', Layout.monoOf, htag]; rfl

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
