import Rv64Verifier.Proofs.Bus.VbbTail51

/-!
# `verify_bus_balance`'s side loop: the owner's form

From `0x80007a08` (`Bf`): `Form::add_scaled` of block `k`'s form at `S - 296`, times its selector,
into form `i` of its owner's row of the matrix, to `0x80007a34` (`Cd`, `cellStage`): the matrix holds
the fold's forms after `k + 1` blocks (`Mat.update`, `formRowsAt_update`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem eAt_of_same' {u v : MachineState} (h : ∀ a, v.getMem a = u.getMem a) (p : Word) :
    eAt v p = eAt u p := by
  simp only [eAt, h]

/-- At `0x80007a34`, block `k` added into its owner's form, from the loop's head `t₀`. -/
structure Cd (s z h e t₀ t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) (P : Word)
    (n : Nat) (forms : List (List Form)) (tot : List E) (k : Nat) : Prop where
  mm : Mm s z h e t P n (blkFold point i sd forms (k + 1)).1 tot
  regs : ∀ r ∈ ([.x2, .x21, .x22, .x24, .x25] : List Reg), t.getReg r = t₀.getReg r
  x20 : t.getReg .x20 = e.getMem (s.getReg .x2 - 1144)
  x27 : t.getReg .x27 = blkAddr s i k
  x9 : t.getReg .x9 = vecPtr t (s.getReg .x2 - 296)
  x23 : t.getReg .x23 = vecLen t (s.getReg .x2 - 296)
  own : blkOwner s i k < n
  sel : eAt t (s.getReg .x2 - 272) = (tbSel sd point).getD k 0
  acc : eAt t (s.getReg .x2 - 1128) = eOf3 (t₀.getReg .x17) (t₀.getReg .x16) (t₀.getReg .x15)
  ok : Layout.FormOk t (s.getReg .x2 - 296)
  fbuf : ∀ x, Layout.formBuf t (s.getReg .x2 - 296) x → heapNext t₀ ≤ x.toNat ∧ x.toNat < heapNext t
  form : (Layout.formOf t (s.getReg .x2 - 296)).toSpec =
    blockFormRust (blockAt s (blkAddr s i k)) sd.2.2.2.1 sd.2.2.2.2
  len : 1 ≤ (vecLen t (s.getReg .x2 - 296)).toNat

/-- The fold's forms after block `k`: its form, times its selector, into its owner's form `i`. -/
theorem blkFold_forms {s : MachineState} {point : List E} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {forms : List (List Form)} {k : Nat}
    (hb : blocksAt s (blkVec s i) = sd.1) (hk : k < min sd.2.1.tables.length sd.1.length) :
    (blkFold point i sd forms (k + 1)).1 = (blkFold point i sd forms k).1.modify (blkOwner s i k)
      fun row ↦ row.modify i fun f ↦ addScaledRust f
        (blockFormRust (blockAt s (blkAddr s i k)) sd.2.2.2.1 sd.2.2.2.2) ((tbSel sd point).getD k 0) := by
  rw [blkFold_succ hk, blocks_get hb]
  rfl

/-- `Mm` past `add_scaled` into form `i` of row `o`: the matrix `Mat.update` gives, holding `fs'`. -/
theorem cellMm {s z h e u v : MachineState} {P : Word} {n o i : Nat}
    {fs fs' : List (List Form)} {tot : List E} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (Mu : Mm s z h e u P n fs tot) (own : o < n) (i3 : i < 3)
    (frL : DFrame u v fun a ↦ Within a (cellAt u (rowAt P o) i) 24 ∨
      Layout.formBuf u (cellAt u (rowAt P o) i) a ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 2512) 1168 ∨ Within a nextAddr 8 ∨ Fresh u v a)
    (hv : HeapOk v) (hvm : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2)
    (okv : Layout.FormOk v (cellAt u (rowAt P o) i))
    (lv : 1 ≤ (vecLen v (cellAt u (rowAt P o) i)).toNat) (M₆ : Mat z v P n)
    (hrow₆ : ∀ a < n, ∀ k < 3, v.getMem (rowAt P a + BitVec.ofNat 64 (8 * k)) =
      u.getMem (rowAt P a + BitVec.ofNat 64 (8 * k)))
    (pe₆ : ∀ a < n, ∀ j ≤ 3, (a ≠ o ∨ j ≠ i) → ∀ x, piece v P a j x ↔ piece u P a j x)
    (pn₆ : ∀ x, piece v P o i x → piece u P o i x ∨ Fresh u v x)
    (hcell₆ : ∀ a < n, ∀ j < 3, (a ≠ o ∨ j ≠ i) → ∀ k < 3,
      v.getMem (cellAt u (rowAt P a) j + BitVec.ofNat 64 (8 * k)) =
        u.getMem (cellAt u (rowAt P a) j + BitVec.ofNat 64 (8 * k)))
    (value : formRowsAt v P n = fs') : Mm s z h e v P n fs' tot := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have Iu := Mu.cur.inv
  have huE := Iu.heap.hi
  have hlo := hpre.heap.lo
  have Mt := Mu.mat
  have hcRow (x : Word) (hx : Within x (cellAt u (rowAt P o) i) 24) : piece u P o 3 x :=
    Mt.inRow Iu.heap own i3 hx
  have wHeap (a : Word) (ha : Within a (cellAt u (rowAt P o) i) 24 ∨
      Layout.formBuf u (cellAt u (rowAt P o) i) a ∨ Fresh u v a) :
      heapStart ≤ a.toNat ∧ a.toNat < heapNext v := by
    rcases ha with ha | ha | ⟨a1, a2⟩
    · have h3 := (Mt.below own (le_refl _) (hcRow a ha))
      exact ⟨h3.1, lt_of_lt_of_le h3.2 hvm⟩
    · have h3 := (Mt.below own i3.le ((piece_form i3).mpr ha))
      exact ⟨h3.1, lt_of_lt_of_le h3.2 hvm⟩
    · have := Iu.heap.lo; exact ⟨by omega, a2⟩
  have hvE' := hv.hi
  simp only [heapNext, heapEnd] at hvE'
  have vw (a : Word) (h1 : (s.getReg .x2 - 1344).toNat ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem a = u.getMem a :=
    frL a fun q hq hw ↦ by
      rcases hw with hw | hw | hw | hw | hw
      · have := wHeap _ (Or.inl hw); simp only [heapNext] at this
        addr_omega [this, h1, h2, hq, hb1, hvE']
      · have := wHeap _ (Or.inr (Or.inl hw)); simp only [heapNext] at this
        addr_omega [this, h1, h2, hq, hb1, hvE']
      · addr_omega [hw, h1, h2, hq, hb1]
      · simp only [nextAddr] at hw; addr_omega [hw, h1, h2, hq, hb1]
      · have := wHeap _ (Or.inr (Or.inr hw)); simp only [heapNext] at this
        addr_omega [this, h1, h2, hq, hb1, hvE']
  have st : StepS s u v fun a ↦ Within a (cellAt u (rowAt P o) i) 24 ∨
      Layout.formBuf u (cellAt u (rowAt P o) i) a :=
    ⟨frL.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr ha)
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ha)), hv, hvm, sp⟩
  have Cv : Cur s z h v := Mu.cur.next hpre hsz st fun a ha ↦ Or.inr (by
    rcases ha with ha | ha
    · have hp3 := hcRow a ha
      exact ⟨Mt.fresh o own 3 (le_refl _) a hp3, lt_of_lt_of_le (Mt.below own (le_refl _) hp3).2 hvm⟩
    · have hpi : piece u P o i a := (piece_form i3).mpr ha
      exact ⟨Mt.fresh o own i i3.le a hpi, lt_of_lt_of_le (Mt.below own i3.le hpi).2 hvm⟩)
  -- the slot `S - 632`
  have tw (q : Nat) (hq : q < 24) : ¬ (Within (s.getReg .x2 - 632 + BitVec.ofNat 64 q)
      (cellAt u (rowAt P o) i) 24 ∨
      Layout.formBuf u (cellAt u (rowAt P o) i) (s.getReg .x2 - 632 + BitVec.ofNat 64 q) ∨
      Within (s.getReg .x2 - 632 + BitVec.ofNat 64 q) (s.getReg .x2 - BitVec.ofNat 64 2512) 1168 ∨
      Within (s.getReg .x2 - 632 + BitVec.ofNat 64 q) nextAddr 8 ∨
      Fresh u v (s.getReg .x2 - 632 + BitVec.ofNat 64 q)) := by
    intro hw
    rcases hw with hw | hw | hw | hw | hw
    · have := wHeap _ (Or.inl hw); simp only [heapNext] at this; addr_omega [this, hq, hb1, hvE']
    · have := wHeap _ (Or.inr (Or.inl hw)); simp only [heapNext] at this
      addr_omega [this, hq, hb1, hvE']
    · addr_omega [hw, hq, hb1]
    · simp only [nextAddr] at hw; addr_omega [hw, hq, hb1]
    · have := wHeap _ (Or.inr (Or.inr hw)); simp only [heapNext] at this
      addr_omega [this, hq, hb1, hvE']
  have h632 (q : Nat) (hq : q + 8 ≤ 24) : v.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 q) =
      u.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 q) :=
    frL _ fun r hr ↦ by rw [add_ofNat_add]; exact tw _ (by omega)
  have tp : vecPtr v (s.getReg .x2 - 632) = vecPtr u (s.getReg .x2 - 632) := h632 8 (by omega)
  have tc : vecCap v (s.getReg .x2 - 632) = vecCap u (s.getReg .x2 - 632) := by
    have := h632 0 (by omega); simp only [add_ofNat_zero] at this; exact this
  have TB := Mu.totals
  refine ⟨Cv, fun j hj hj2 hx ↦ ?_, M₆, fun a ha j hj ↦ ?_, value, fun a ha j hj x hx ↦ ?_,
    le_trans Mu.mono hvm, fun x h1 h2 ↦ ?_, ?_, fun x hx ↦ ?_⟩
  · exact (vw _ (by addr_omega [hb1, hj, hj2]) (by addr_omega [hb1, hj, hj2])).trans
      (Mu.slots j hj hj2 hx)
  · have er : vecPtr v (rowAt P a) = vecPtr u (rowAt P a) := by
      simpa [vecPtr] using hrow₆ a ha 1 (by omega)
    have ec : cellAt v (rowAt P a) j = cellAt u (rowAt P a) j := by simp only [cellAt, er]
    rw [ec]
    by_cases hc' : a = o ∧ j = i
    · obtain ⟨rfl, rfl⟩ := hc'
      have hraw := okv.vec.raw
      have hl := okv.vec.len
      simp only [RawVecOk, Buf] at hraw
      rcases hraw.2 with h0 | h0
      · omega
      · omega
    · have hne : a ≠ o ∨ j ≠ i := not_and_or.mp hc'
      have ep : vecPtr v (cellAt u (rowAt P a) j) = vecPtr u (cellAt u (rowAt P a) j) := by
        simpa [vecPtr] using hcell₆ a ha j hj hne 1 (by omega)
      have el : vecLen v (cellAt u (rowAt P a) j) = vecLen u (cellAt u (rowAt P a) j) := by
        simpa [vecLen] using hcell₆ a ha j hj hne 2 (by omega)
      rw [ep, el]
      exact le_trans (Mu.below a ha j hj) hvm
  · by_cases hc' : a = o ∧ j = i
    · obtain ⟨rfl, rfl⟩ := hc'
      rcases pn₆ x hx with h' | h'
      · exact Mu.gap a ha j hj x h'
      · exact Or.inr (le_trans Mu.mono h'.1)
    · exact Mu.gap a ha j hj x ((pe₆ a ha j hj (not_and_or.mp hc') x).mp hx)
  · rw [← Mu.hk x h1 h2]
    refine frL x fun q hq hw ↦ ?_
    have he := Mu.mono
    have hu := huE
    simp only [heapNext, heapEnd] at h1 h2 he hu
    have hxE : x.toNat + 8 ≤ 2013265920 := by omega
    have hxq : (x + BitVec.ofNat 64 q).toNat = x.toNat + q := by addr_omega [hxE, hq]
    rcases hw with hw | hw | hw | hw | ⟨hw, -⟩
    · rcases Mu.gap o own 3 (le_refl _) _ (hcRow _ hw) with g | g <;>
        (simp only [heapNext] at g; omega)
    · rcases Mu.gap o own i i3.le _ ((piece_form i3).mpr hw) with g | g <;>
        (simp only [heapNext] at g; omega)
    · addr_omega [hw, hxq, hxE, hb1, hq]
    · simp only [nextAddr] at hw; addr_omega [hw, hxq, hxE, hq]
    · simp only [heapNext] at hw; omega
  · refine TB.dframe' frL hvm (fun q hq ↦ tw q hq) fun q hq hw ↦ ?_
    have hl := TB.vec.len
    have hbuf := TB.buf
    simp only [NewBuf] at hbuf
    rcases hbuf.2 with h0 | ⟨b1, b2⟩
    · omega
    · have hin : Within (vecPtr u (s.getReg .x2 - 632) + BitVec.ofNat 64 q)
          (vecPtr u (s.getReg .x2 - 632)) (24 * (vecCap u (s.getReg .x2 - 632)).toNat) := by
        have hu := huE
        simp only [heapNext, heapEnd] at b2 hu; addr_omega [b2, hu, hq, hl]
      obtain ⟨-, t2⟩ := Mu.tbuf _ hin
      have hu := huE
      have hzl := le_trans hlo hsz
      simp only [heapNext, heapEnd, heapStart] at b1 b2 hu hzl
      have hpq : (vecPtr u (s.getReg .x2 - 632) + BitVec.ofNat 64 q).toNat =
          (vecPtr u (s.getReg .x2 - 632)).toNat + q := by addr_omega [b2, hu, hq, hl]
      rcases hw with hw | hw | hw | hw | ⟨hw, -⟩
      · exact t2 o own 3 (le_refl _) (hcRow _ hw)
      · exact t2 o own i i3.le ((piece_form i3).mpr hw)
      · addr_omega [hw, hpq, b2, hu, hq, hl, hb1]
      · simp only [nextAddr] at hw; addr_omega [hw, hpq, b2, hu, hq, hl]
      · simp only [heapNext] at hw; omega
  · rw [tp, tc] at hx
    obtain ⟨t1, t2⟩ := Mu.tbuf x hx
    refine ⟨t1, fun a ha j hj hp' ↦ ?_⟩
    by_cases hc' : a = o ∧ j = i
    · obtain ⟨rfl, rfl⟩ := hc'
      rcases pn₆ x hp' with h' | h'
      · exact t2 a ha j hj h'
      · have hl := TB.vec.len
        have hbuf := TB.buf
        simp only [NewBuf, Within] at hbuf hx
        simp only [Fresh] at h'
        rcases hbuf.2 with h0 | ⟨b1, b2⟩ <;> omega
    · exact t2 a ha j hj ((pe₆ a ha j hj (not_and_or.mp hc') x).mp hp')

/-- `add_scaled`'s precondition on a form `c` in the heap below `B`, the terms from `p`, in the heap
from `B` on, and the weight at `S - 272`. -/
theorem cellPre {s u : MachineState} {c p L : Word} {B : Nat} (hpre : BusBalancePre s)
    (Iu : Inv s u) (x10 : u.getReg .x10 = c) (x11 : u.getReg .x11 = p) (x12 : u.getReg .x12 = L)
    (x13 : u.getReg .x13 = s.getReg .x2 - 272) (hc1 : heapStart ≤ c.toNat) (hc8 : c.toNat % 8 = 0)
    (hcB : c.toNat + 24 ≤ B) (hp1 : heapStart ≤ p.toNat) (hp8 : p.toNat % 8 = 0)
    (hp3 : B ≤ p.toNat) (hp4 : p.toNat + 48 * L.toNat ≤ heapNext u) (hBu : B ≤ heapNext u)
    (ok : Layout.FormOk u c) (tags : ∀ q < L.toNat, Layout.MonoOk u (p + BitVec.ofNat 64 (48 * q)))
    (buf : ∀ x, Layout.formBuf u c x → x.toNat < B ∧ ¬ Within x c 24) : Layout.AddScaledPre u := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have spu : u.getReg .x2 = s.getReg .x2 - 1344 := Iu.sp
  have huE := Iu.heap.hi
  have hsl : stackLo u Layout.addScaledStack = s.getReg .x2 - BitVec.ofNat 64 2512 := by
    simp only [stackLo, Layout.addScaledStack, Contracts.mulStack, spu]
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  simp only [heapNext, heapEnd] at hp4 hBu huE
  exact {
    heap := Iu.heap
    stack := hpre.stack.sub 1344 spu (by decide) (by decide) (by decide) (by decide) (by decide)
    self := by rw [x10]; exact heapRange hc8 hc1 (by simp only [heapEnd]; omega)
    ok := by rw [x10]; exact ok
    other := by rw [x11, x12]; exact heapRange hp8 hp1 (by simp only [heapEnd]; omega)
    otherTags := fun q hq ↦ by rw [x11]; rw [x12] at hq; exact tags q hq
    weight := by rw [x13]; valid_sub hval [hb1]
    rodata := Iu.rodata hpre
    selfFree := by
      rw [x10]; simp only [Outside, heapNext, heapEnd]; exact ⟨Or.inl (by omega), by addr_omega [hcB, hBu, huE]⟩
    otherFree := by
      rw [x11, x12]; simp only [Outside, heapNext, heapEnd]; exact ⟨Or.inl hp4, by addr_omega [hp4, huE]⟩
    weightFree := by
      rw [x13]; simp only [Outside, heapNext, heapEnd]; addr_omega [hb1, huE, hnx]
    selfStack := by rw [x10, hsl]; addr_omega [hb1, hcB, hBu, huE]
    otherStack := by rw [x11, x12, hsl]; addr_omega [hb1, hp4, huE]
    weightStack := by rw [x13, hsl]; addr_omega [hb1]
    selfOther := by rw [x10, x11, x12]; addr_omega [hcB, hp3]
    selfWeight := by rw [x10, x13]; addr_omega [hb1, hcB, hBu, huE]
    selfRodata := by rw [x10]; addr_omega [hrb, hcB, hBu, huE]
    buf := fun x hx ↦ by
      rw [x10] at hx
      obtain ⟨hxB, hxc⟩ := buf x hx
      rw [x10, x11, x12, x13]
      rintro (hw | hw | hw)
      · exact hxc hw
      · simp only [Within] at hw; omega
      · addr_omega [hw, hxB, hBu, huE, hb1] }

set_option maxRecDepth 8192 in
theorem cellCall (hAS : Layout.AddScaledSpec) {s z h e t₀ t₄ t₅ : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (hPb : n = 0 ∨ heapNext z ≤ P.toNat)
    (En : Entry s z h e i sd point P n) (B : Blk s z h e t₀ i sd point P n forms tot k)
    (hk : k < min sd.2.1.tables.length sd.1.length) (H : Hd s z h e t₀ t₄ i sd point P n k)
    (F : Bf s z h t₀ t₄ t₅ i sd k) (hpc : t₅.pc = 0x80007a08) :
    ∃ v, Reaches Image.code t₅ v ∧ (Dead Image.code v ∨
      (v.pc = 0x80007a34 ∧ Mm s z h e v P n (blkFold point i sd forms (k + 1)).1 tot ∧
        DFrame t₅ v (fun a ↦ a.toNat < heapNext t₀ ∨
          Within a (s.getReg .x2 - BitVec.ofNat 64 2512) 1168 ∨ Within a nextAddr 8 ∨ Fresh t₅ v a) ∧
        heapNext t₅ ≤ heapNext v ∧
        (∀ r ∈ ([.x2, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg), v.getReg r = t₅.getReg r) ∧
        v.getReg .x9 = vecPtr t₅ (s.getReg .x2 - 296) ∧
        v.getReg .x23 = vecLen t₅ (s.getReg .x2 - 296))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  rw [stackLo_eq] at hab hnx hrs
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have I₀ := B.cur.inv
  have C₅ := F.cur
  have I₅ := C₅.inv
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 1344 := I₅.sp
  have h₀E := I₀.heap.hi
  have h₅E := I₅.heap.hi
  have hlo := hpre.heap.lo
  have m₀₄ := H.mono
  have m₄₅ := F.mono
  have i3 := En.i3
  have own := H.own
  set o := blkOwner s i k with ho
  -- memory from `t₀` to `t₅`
  have fr₀₅ : DFrame t₀ t₅ (ItW s t₀ t₅) :=
    (H.fr.mono fun a ha ↦ ItW.mono m₄₅ ha).trans (F.fr.mono fun a ha ↦ CoW.itW hpre ha) fun _ h ↦ h
  have M₅ : Mm s z h e t₅ P n (blkFold point i sd forms k).1 tot :=
    B.mm.keep hpre hsz hPb fr₀₅ I₅.heap (le_trans m₀₄ m₄₅) (sp₅.trans I₀.sp.symm)
  have kept (x : Word) (h1 : heapStart ≤ x.toNat) (h2 : x.toNat + 8 ≤ heapNext t₀) :
      t₅.getMem x = t₀.getMem x := ItW.kept hpre I₀.heap fr₀₅ h2
  -- the owner's row at `t₀`
  have hrowB : heapStart ≤ (vecPtr t₀ (rowAt P o)).toNat ∧ (vecPtr t₀ (rowAt P o)).toNat % 8 = 0 ∧
      3 ≤ (vecCap t₀ (rowAt P o)).toNat ∧
      (vecPtr t₀ (rowAt P o)).toNat + 24 * (vecCap t₀ (rowAt P o)).toNat ≤ heapNext t₀ := by
    obtain ⟨hv, hl⟩ := B.mat.rows o own
    have hc := hv.len
    rw [hl] at hc
    have e3 : (3 : Word).toNat = 3 := rfl
    have hraw := hv.raw
    simp only [RawVecOk, Buf] at hraw
    rcases hraw.2 with h0 | h0
    · omega
    · exact ⟨h0.1, hraw.1, by omega, by omega⟩
  have hPr : (P.toNat + 24 * n ≤ heapNext t₀) ∧ heapStart ≤ P.toNat := by
    rcases B.mat.hdr.2 with h0 | h0
    · omega
    · exact ⟨h0.2, h0.1⟩
  have rowW (q : Nat) (hq : q < 3) : t₅.getMem (rowAt P o + BitVec.ofNat 64 (8 * q)) =
      t₀.getMem (rowAt P o + BitVec.ofNat 64 (8 * q)) := by
    obtain ⟨p1, p2⟩ := hPr
    simp only [heapStart, heapNext] at p1 p2 h₀E
    exact kept _ (by simp only [rowAt, heapStart]; addr_omega [p1, p2, own, hq, h₀E])
      (by simp only [rowAt, heapNext]; addr_omega [p1, p2, own, hq, h₀E])
  have rp : vecPtr t₅ (rowAt P o) = vecPtr t₀ (rowAt P o) := by
    have h := rowW 1 (by omega); simp only [Nat.mul_one] at h; exact h
  -- the frame's slots the block reads
  have slot (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 1104 ∨ 1144 ≤ j)
      (h2 : j ≤ 104 ∨ 304 ≤ j) :
      t₅.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    M₅.slots j hj hj2 (blkW_miss hpre hj hj2 h1 h2)
  -- `0x80007a08`
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007a08_spec hpc (by
    rv_eval [sp₅]
    and_intros <;> valid_access hval [hb1])
  have m₁ := b80007a08_mem_same h₁
  have k₁ := b80007a08_keeps h₁
  have spu : u.getReg .x2 = s.getReg .x2 - 1344 := (k₁ .x2 (by decide)).trans sp₅
  have Mu : Mm s z h e u P n (blkFold point i sd forms k).1 tot :=
    M₅.keep hpre hsz hPb (DFrame.of_same m₁ _) (by
      have := I₅.heap; exact ⟨by simp only [heapNext, m₁]; exact this.lo,
        by simp only [heapNext, heapEnd, m₁]; exact this.hi⟩) (by simp only [heapNext, m₁]; exact le_refl _)
      (k₁ .x2 (by decide))
  have Iu := Mu.cur.inv
  have huE := Iu.heap.hi
  have hnu : heapNext u = heapNext t₅ := by simp only [heapNext, m₁]
  have e1184 : t₅.getMem (t₅.getReg .x2 + 160) = BitVec.ofNat 64 (16 * i) := by
    rw [sp₅]; rv_eval []; exact (slot 1184 (by omega) (by omega) (by omega) (by omega)).trans En.i1184
  have e1176 : t₅.getMem (t₅.getReg .x2 + 168) = BitVec.ofNat 64 (8 * i) := by
    rw [sp₅]; rv_eval []; exact (slot 1176 (by omega) (by omega) (by omega) (by omega)).trans En.i1176
  have hx8 : t₅.getReg .x8 = vecPtr t₀ (rowAt P o) :=
    (F.regs .x8 (by decide)).trans H.x8
  set c := cellAt u (rowAt P o) i with hc
  have hcu : cellAt u (rowAt P o) i = cellAt t₀ (rowAt P o) i := by
    simp only [cellAt, vecPtr, m₁]; rw [show vecPtr t₅ (rowAt P o) = t₅.getMem (rowAt P o + 8) from rfl] at rp
    rw [rp]; rfl
  have x10u : u.getReg .x10 = c := by
    rw [b80007a08_x10 h₁, hx8, e1184, e1176, hc, hcu]
    simp only [cellAt]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨rB1, rB2, rB3, rB4⟩ := hrowB
  have hcN : (cellAt t₀ (rowAt P o) i).toNat = (vecPtr t₀ (rowAt P o)).toNat + 24 * i := by
    simp only [cellAt]; simp only [heapNext] at rB4 h₀E; addr_omega [rB4, h₀E, i3]
  have hcB : c.toNat + 24 ≤ heapNext t₀ := by rw [hc, hcu, hcN]; omega
  -- the block's form
  have okF := F.ok
  have lenF := F.len
  have bfB : heapStart ≤ (vecPtr t₅ (s.getReg .x2 - 296)).toNat ∧
      (vecPtr t₅ (s.getReg .x2 - 296)).toNat % 8 = 0 ∧
      heapNext t₀ ≤ (vecPtr t₅ (s.getReg .x2 - 296)).toNat ∧
      (vecPtr t₅ (s.getReg .x2 - 296)).toNat + 48 * (vecLen t₅ (s.getReg .x2 - 296)).toNat ≤
        heapNext t₅ := by
    have hraw := okF.vec.raw
    have hl := okF.vec.len
    simp only [RawVecOk, Buf] at hraw
    rcases hraw.2 with h0 | h0
    · omega
    · have := F.fbuf (vecPtr t₅ (s.getReg .x2 - 296))
        (by simp only [Layout.formBuf, Within]; omega)
      exact ⟨h0.1, hraw.1, this.1, by omega⟩
  obtain ⟨fB1, fB2, fB3, fB4⟩ := bfB
  have x11u : u.getReg .x11 = vecPtr t₅ (s.getReg .x2 - 296) := by
    rw [b80007a08_x11 h₁, sp₅, vecPtr]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x12u : u.getReg .x12 = vecLen t₅ (s.getReg .x2 - 296) := by
    rw [b80007a08_x12 h₁, sp₅, vecLen]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x13u : u.getReg .x13 = s.getReg .x2 - 272 := by
    rw [b80007a08_x13 h₁, sp₅]; rv_eval []
  have hsl : stackLo u Layout.addScaledStack = s.getReg .x2 - BitVec.ofNat 64 2512 := by
    simp only [stackLo, Layout.addScaledStack, Contracts.mulStack, spu]
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  -- the pieces at `u` against `t₀`
  have peU (a : Nat) (ha : a < n) (j : Nat) (x : Word) : piece u P a j x ↔ piece t₀ P a j x := by
    refine piece_congr (fun q hq ↦ ?_) (fun hj q hq ↦ ?_) x
    · obtain ⟨p1, p2⟩ := hPr
      simp only [heapStart, heapNext] at p1 p2 h₀E
      rw [m₁]
      exact kept _ (by simp only [rowAt, heapStart]; addr_omega [p1, p2, ha, hq, h₀E])
        (by simp only [rowAt, heapNext]; addr_omega [p1, p2, ha, hq, h₀E])
    · obtain ⟨hv, hl⟩ := B.mat.rows a ha
      have hcap := hv.len
      rw [hl] at hcap
      have e3 : (3 : Word).toNat = 3 := rfl
      have hraw := hv.raw
      simp only [RawVecOk, Buf] at hraw
      simp only [heapNext] at h₀E
      rw [m₁]
      rcases hraw.2 with h0 | ⟨r1, r2⟩
      · omega
      · simp only [heapStart, heapNext] at r1 r2
        exact kept _ (by simp only [cellAt, heapStart]; addr_omega [r1, r2, hj, hq, h₀E, hcap])
          (by simp only [cellAt, heapNext]; addr_omega [r1, r2, hj, hq, h₀E, hcap])
  have Mt := Mu.mat
  have hcRow (x : Word) (hx : Within x c 24) : piece u P o 3 x := Mt.inRow Iu.heap own i3 hx
  have pB (a : Nat) (ha : a < n) (j : Nat) (hj : j ≤ 3) (x : Word) (hx : piece u P a j x) :
      x.toNat < heapNext t₀ := (B.mat.below ha hj ((peU a ha j x).mp hx)).2
  -- `add_scaled`'s precondition
  have pre : Layout.AddScaledPre u := cellPre hpre Iu x10u x11u x12u x13u
    (by rw [hc, hcu, hcN]; omega) (by rw [hc, hcu, hcN]; omega) hcB fB1 fB2 fB3 (by rw [hnu]; exact fB4)
    (by rw [hnu]; exact le_trans m₀₄ m₄₅) (Mt.forms o own i i3)
    (fun q hq ↦ by simp only [Layout.MonoOk]; rw [m₁]; exact okF.tags q hq)
    fun x hx ↦ by
      have hp : piece u P o i x := (piece_form i3).mpr hx
      exact ⟨pB o own i i3.le x hp, fun hw ↦
        Mt.apart o own i i3.le o own 3 (le_refl _) (Or.inr (by omega)) x hp (hcRow x hw)⟩
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hAS.call (Reaches.refl u) (b80007a08_pc h₁) pre
  swap
  · exact ⟨v, hr₁.trans hrv, Or.inl hd⟩
  have hvm := post.mono
  have frL : DFrame u v fun a ↦ Within a c 24 ∨ Layout.formBuf u c a ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 2512) 1168 ∨ Within a nextAddr 8 ∨ Fresh u v a := by
    have := layoutFrame hrv post.frame; rw [x10u, hsl] at this; exact this
  -- the matrix
  obtain ⟨M₆, hrow₆, hother₆, pe₆, pn₆, hcell₆⟩ := Mt.update own i3 Iu.heap hvm
    (Other := fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 2512) 1168 ∨ Within a nextAddr 8)
    (frL.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inl (Or.inr ha)))
      · exact Or.inr (Or.inr (Or.inr ha)))
    (fun x hx ↦ by
      obtain ⟨p1, p2⟩ := hPr
      have h0 := h₀E
      have hu := huE
      simp only [heapNext, heapEnd, heapStart] at p1 p2 h0 hu
      refine ⟨fun hw ↦ ?_, fun a ha j hj hpc' ↦ ?_⟩
      · rcases hx with hx | hx
        · addr_omega [hx, hw, hb1, p1, p2, h0]
        · simp only [nextAddr] at hx; addr_omega [hx, hw, p1, p2, h0]
      · have := Mt.below ha hj hpc'
        simp only [heapNext, heapStart] at this
        rcases hx with hx | hx
        · addr_omega [hx, this, hb1, hu]
        · simp only [nextAddr] at hx; addr_omega [hx, this, hu])
    (by have := post.ok; rw [x10u] at this; exact this)
    (fun x hx ↦ by have := post.buf x (by rw [x10u]; exact hx); rw [x10u] at this; exact this)
  have hpv : v.pc = 0x80007a34 := by rw [hpcv, returnAddress_eq, b80007a08_x1 h₁]; decide
  -- the new form
  have hval := post.value
  rw [x10u, x11u, x12u, x13u] at hval
  have okv : Layout.FormOk v c := by have := post.ok; rw [x10u] at this; exact this
  have tU (p : Word) (m : Nat) : Layout.termsOf u p m = Layout.termsOf t₅ p m := by
    simp only [Layout.termsOf, Layout.termOf, Layout.monoOf, eAt, m₁]
  have fU (a : Word) : Layout.formOf u a = Layout.formOf t₅ a := by
    simp only [Layout.formOf, vecPtr, vecLen, m₁, tU]
  have lv : 1 ≤ (vecLen v c).toNat := by
    have := addScaled_pos (Layout.formOf u c)
      ⟨Layout.termsOf u (vecPtr t₅ (s.getReg .x2 - 296)) (vecLen t₅ (s.getReg .x2 - 296)).toNat⟩
      (eAt u (s.getReg .x2 - 272)) (by simp only [Layout.termsOf_length]; exact lenF)
    rw [← hval] at this
    simpa [Layout.formOf, Layout.termsOf_length] using this
  -- the selector and the sum, at `t₅`
  have selT : eAt t₅ (s.getReg .x2 - 272) = eAt t₄ (s.getReg .x2 - 272) :=
    F.fr.eAt fun q hq hw ↦ by
      rcases hw with hw | hw | hw | hw | ⟨-, hw⟩
      · addr_omega [hw, hq, hb1]
      · addr_omega [hw, hq, hb1]
      · addr_omega [hw, hq, hb1]
      · simp only [nextAddr] at hw; addr_omega [hw, hq, hb1]
      · simp only [heapNext, heapEnd] at hw h₅E; addr_omega [hw, hq, hb1, h₅E]
  have hsel : eAt u (s.getReg .x2 - 272) = (tbSel sd point).getD k 0 := by
    rw [eAt_of_same' m₁, selT]; exact H.sel
  have hX : (Layout.formOf v c).toSpec = addScaledRust (Layout.formOf u c).toSpec
      (blockFormRust (blockAt s (blkAddr s i k)) sd.2.2.2.1 sd.2.2.2.2) ((tbSel sd point).getD k 0) := by
    rw [hval, LayoutMirror.FormRust.toSpec_addScaled, hsel, addScaledRust_eq, ← F.form, fU]
    simp only [Layout.formOf, tU]
  have hv6 := formRowsAt_update (fun a ha ↦ (Mt.rows a ha).2) hrow₆ hother₆
  have value : formRowsAt v P n = (blkFold point i sd forms (k + 1)).1 := by
    rw [hv6, hX, blkFold_forms En.blocks hk, ← Mu.value]
    exact modify_modify_const (x := (Layout.formOf u c).toSpec)
      (f := fun f ↦ addScaledRust f (blockFormRust (blockAt s (blkAddr s i k)) sd.2.2.2.1 sd.2.2.2.2)
        ((tbSel sd point).getD k 0)) fun h1 h2 ↦ formRowsAt_getElem h1 h2
  have mm := cellMm hpre hsz Mu own i3 frL post.heap hvm (hp.reg .x2) okv lv M₆ hrow₆ pe₆ pn₆
    hcell₆ value
  have hn5 : heapNext t₅ ≤ heapNext v := by rw [← hnu]; exact hvm
  refine ⟨v, hr₁.trans hrv, Or.inr ⟨hpv, mm, ?_, hn5, fun r hr ↦ ?_, ?_, ?_⟩⟩
  · refine (DFrame.of_same m₁ _).trans (frL.mono fun a ha ↦ ?_) fun _ h ↦ h
    rcases ha with ha | ha | ha | ha | ⟨a1, a2⟩
    · exact Or.inl (by simp only [Within] at ha; omega)
    · exact Or.inl (pB o own i i3.le a ((piece_form i3).mpr ha))
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨by rw [← hnu]; exact a1, a2⟩))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hp.reg _, k₁ _ (by decide)]
  · rw [hp.reg .x9, x11u.symm.trans (b80007a08_x11 h₁), ← b80007a08_x9 h₁]
  · rw [hp.reg .x23, x12u.symm.trans (b80007a08_x12 h₁), ← b80007a08_x23 h₁]

theorem cellStage (hAS : Layout.AddScaledSpec) {s z h e t₀ t₄ t₅ : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (hPb : n = 0 ∨ heapNext z ≤ P.toNat)
    (En : Entry s z h e i sd point P n) (B : Blk s z h e t₀ i sd point P n forms tot k)
    (hk : k < min sd.2.1.tables.length sd.1.length) (H : Hd s z h e t₀ t₄ i sd point P n k)
    (F : Bf s z h t₀ t₄ t₅ i sd k) (hpc : t₅.pc = 0x80007a08) :
    ∃ t, Reaches Image.code t₅ t ∧ (Dead Image.code t ∨
      (t.pc = 0x80007a34 ∧ Cd s z h e t₀ t i sd point P n forms tot k)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨v, hrv, hd | ⟨hpv, mm, fr, hn5, regs, x9, x23⟩⟩ := cellCall hAS hpre hsz hPb En B hk H F hpc
  · exact ⟨v, hrv, Or.inl hd⟩
  have h₀E := B.cur.inv.heap.hi
  have h₅E := F.cur.inv.heap.hi
  have hvE := mm.cur.inv.heap.hi
  have h₀₅ : heapNext t₀ ≤ heapNext t₅ := le_trans H.mono F.mono
  have vw (a : Word) (h1 : (s.getReg .x2 - 1344).toNat ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem a = t₅.getMem a :=
    fr a fun q hq hw ↦ by
      rcases hw with hw | hw | hw | ⟨-, hw⟩
      · simp only [heapNext, heapEnd] at hw h₀E; addr_omega [hw, h1, h2, hq, hb1, h₀E]
      · addr_omega [hw, h1, h2, hq, hb1]
      · simp only [nextAddr] at hw; addr_omega [hw, h1, h2, hq, hb1]
      · simp only [heapNext, heapEnd] at hw hvE; addr_omega [hw, h1, h2, hq, hb1, hvE]
  have eV (a : Word) (h1 : (s.getReg .x2 - 1344).toNat ≤ a.toNat)
      (h2 : a.toNat + 24 ≤ (s.getReg .x2).toNat) : eAt v a = eAt t₅ a :=
    eAt_congr (vw a h1 (by omega)) (vw _ (by addr_omega [h1, h2]) (by addr_omega [h1, h2]))
      (vw _ (by addr_omega [h1, h2]) (by addr_omega [h1, h2]))
  have selT : eAt t₅ (s.getReg .x2 - 272) = eAt t₄ (s.getReg .x2 - 272) :=
    F.fr.eAt fun q hq hw ↦ by
      rcases hw with hw | hw | hw | hw | ⟨-, hw⟩
      · addr_omega [hw, hq, hb1]
      · addr_omega [hw, hq, hb1]
      · addr_omega [hw, hq, hb1]
      · simp only [nextAddr] at hw; addr_omega [hw, hq, hb1]
      · simp only [heapNext, heapEnd] at hw h₅E; addr_omega [hw, hq, hb1, h₅E]
  have accT : eAt t₅ (s.getReg .x2 - 1128) = eAt t₄ (s.getReg .x2 - 1128) :=
    F.fr.eAt fun q hq hw ↦ by
      rcases hw with hw | hw | hw | hw | ⟨-, hw⟩
      · addr_omega [hw, hq, hb1]
      · addr_omega [hw, hq, hb1]
      · addr_omega [hw, hq, hb1]
      · simp only [nextAddr] at hw; addr_omega [hw, hq, hb1]
      · simp only [heapNext, heapEnd] at hw h₅E; addr_omega [hw, hq, hb1, h₅E]
  have fo := Layout.formOf_frame (toLayoutFrame fr) F.ok
    (fun x hx hw ↦ by
      rcases hw with hw | hw | hw | ⟨-, hw⟩
      · simp only [heapNext, heapEnd] at hw h₀E; addr_omega [hw, hx, hb1, h₀E]
      · addr_omega [hw, hx, hb1]
      · simp only [nextAddr] at hw; addr_omega [hw, hx, hb1]
      · simp only [heapNext, heapEnd] at hw hvE; addr_omega [hw, hx, hb1, hvE])
    (fun x hx hw ↦ by
      have hb := F.fbuf x hx
      rcases hw with hw | hw | hw | ⟨hw, -⟩
      · omega
      · simp only [heapNext, heapEnd] at hb h₅E; addr_omega [hw, hb, hb1, h₅E]
      · simp only [nextAddr, heapNext, heapEnd] at hw hb h₅E; addr_omega [hw, hb, h₅E]
      · omega)
    (by addr_omega [hb1]) F.cur.inv.heap hn5
  have e296 (q : Nat) (hq : q + 8 ≤ 24) : v.getMem (s.getReg .x2 - 296 + BitVec.ofNat 64 q) =
      t₅.getMem (s.getReg .x2 - 296 + BitVec.ofNat 64 q) :=
    vw _ (by addr_omega [hb1, hq]) (by addr_omega [hb1, hq])
  have ep : vecPtr v (s.getReg .x2 - 296) = vecPtr t₅ (s.getReg .x2 - 296) := e296 8 (by omega)
  have el : vecLen v (s.getReg .x2 - 296) = vecLen t₅ (s.getReg .x2 - 296) := e296 16 (by omega)
  have ec : vecCap v (s.getReg .x2 - 296) = vecCap t₅ (s.getReg .x2 - 296) := by
    have := e296 0 (by omega); simp only [add_ofNat_zero] at this; exact this
  refine ⟨v, hrv, Or.inr ⟨hpv, mm, fun r hr ↦ ?_, ?_, ?_, by rw [x9, ep], by rw [x23, el], H.own,
    ?_, ?_, fo.2, fun x hx ↦ ?_, by rw [fo.1]; exact F.form, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [regs _ (by decide), F.regs _ (by decide), H.regs _ (by decide)]
  · rw [regs .x20 (by decide), F.regs .x20 (by decide), H.x20]
  · rw [regs .x27 (by decide), F.regs .x27 (by decide), H.x27]
  · rw [eV _ (by addr_omega [hb1]) (by addr_omega [hb1]), selT]; exact H.sel
  · rw [eV _ (by addr_omega [hb1]) (by addr_omega [hb1]), accT]; exact H.acc
  · have hx' : Layout.formBuf t₅ (s.getReg .x2 - 296) x := by
      simp only [Layout.formBuf] at hx ⊢; rw [ep, ec] at hx; exact hx
    have := F.fbuf x hx'
    exact ⟨this.1, by omega⟩
  · rw [el]; exact F.len

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
