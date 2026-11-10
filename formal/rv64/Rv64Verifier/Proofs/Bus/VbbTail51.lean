import Rv64Verifier.Proofs.Bus.VbbTail50

/-!
# `verify_bus_balance`'s side loop: what the block loop keeps of memory

`Mm` is `Blk` but its registers and its sum: the iteration's frame, the matrix holding `fs`, the
heap allocated before the loop kept, the totals. A stretch that writes only `ItW` keeps it
(`Mm.keep`); the fold's step (`blkFold_succ`, `blocks_get`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- What the block loop keeps of memory at `t`, its matrix holding `fs`. -/
structure Mm (s z h e t : MachineState) (P : Word) (n : Nat) (fs : List (List Form))
    (tot : List E) : Prop where
  cur : Cur s z h t
  slots : ∀ j, 8 ≤ j → j ≤ 1344 → (∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 8 → ¬ BlkW s y) →
    t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = e.getMem (s.getReg .x2 - BitVec.ofNat 64 j)
  mat : Mat z t P n
  below : ∀ a < n, ∀ j < 3, (vecPtr t (cellAt t (rowAt P a) j)).toNat +
    48 * (vecLen t (cellAt t (rowAt P a) j)).toNat ≤ heapNext t
  value : formRowsAt t P n = fs
  gap : ∀ a < n, ∀ j ≤ 3, ∀ x, piece t P a j x → x.toNat < heapNext h ∨ heapNext e ≤ x.toNat
  mono : heapNext e ≤ heapNext t
  hk : HeapKept h e t (heapNext e)
  totals : NewVecE z t (s.getReg .x2 - 632) tot
  tbuf : ∀ x, Within x (vecPtr t (s.getReg .x2 - 632)) (24 * (vecCap t (s.getReg .x2 - 632)).toNat) →
    ¬ Within x P (24 * n) ∧ ∀ a < n, ∀ j ≤ 3, ¬ piece t P a j x

theorem Blk.mm {s z h e t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (B : Blk s z h e t i sd point P n forms tot k) :
    Mm s z h e t P n (blkFold point i sd forms k).1 tot :=
  ⟨B.cur, B.slots, B.mat, B.below, B.value, B.gap, B.mono, B.hk, B.totals, B.tbuf⟩

/-- A piece keeps its bytes when its row's header and its form's header do. -/
theorem piece_congr {t t' : MachineState} {P : Word} {a j : Nat}
    (hrow : ∀ k < 3, t'.getMem (rowAt P a + BitVec.ofNat 64 (8 * k)) =
      t.getMem (rowAt P a + BitVec.ofNat 64 (8 * k)))
    (hcell : j < 3 → ∀ k < 3, t'.getMem (cellAt t (rowAt P a) j + BitVec.ofNat 64 (8 * k)) =
      t.getMem (cellAt t (rowAt P a) j + BitVec.ofNat 64 (8 * k)))
    (x : Word) : piece t' P a j x ↔ piece t P a j x := by
  have hptr : vecPtr t' (rowAt P a) = vecPtr t (rowAt P a) := by
    have h := hrow 1 (by omega); simp only [Nat.mul_one] at h; exact h
  have hcap : vecCap t' (rowAt P a) = vecCap t (rowAt P a) := by
    have h := hrow 0 (by omega); simp only [Nat.mul_zero, add_ofNat_zero] at h; exact h
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · have hc : cellAt t' (rowAt P a) j = cellAt t (rowAt P a) j := by simp only [cellAt, hptr]
    rw [piece_form h3, piece_form h3, hc]
    have e0 := hcell h3 0 (by omega)
    have e8 := hcell h3 1 (by omega)
    simp only [Nat.mul_zero, Nat.mul_one, add_ofNat_zero] at e0 e8
    simp only [Layout.formBuf, vecPtr, vecCap]
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, e0, e8]
  · simp only [piece, show ¬ j < 3 by omega, ↓reduceIte, Layout.formVecBuf, hptr, hcap]

theorem CoW.itW {s t₀ t : MachineState} (hpre : BusBalancePre s) {a : Word} (h : CoW s t₀ t a) :
    ItW s t₀ t a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases h with h | h | h | h | h
  · exact Or.inl (Or.inr (by addr_omega [h, hb1]))
  · exact Or.inl (Or.inr (by addr_omega [h, hb1]))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- A stretch writing `ItW` keeps the heap below its start's `NEXT`. -/
theorem ItW.kept {s t t' : MachineState} (hpre : BusBalancePre s) (ht : HeapOk t)
    (fr : DFrame t t' (ItW s t t')) {x : Word} (h2 : x.toNat + 8 ≤ heapNext t) :
    t'.getMem x = t.getMem x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hhE := ht.hi
  simp only [heapNext, heapEnd] at hhE h2
  exact fr x fun q hq hw ↦ by
    rcases hw with (hw | hw) | hw | hw | ⟨hw, -⟩
    · addr_omega [hw, hq, h2, hhE, hb1]
    · addr_omega [hw, hq, h2, hhE, hb1]
    · addr_omega [hw, hq, h2, hhE, hb1]
    · simp only [nextAddr] at hw; addr_omega [hw, hq, h2, hhE]
    · simp only [heapNext] at hw; addr_omega [hw, hq, h2, hhE]

/-- A `Vec<E>` whose header and elements miss a frame keeps them. -/
theorem _root_.Rv64Verifier.Transcript.NewVecE.dframe' {s t t' : MachineState} {w : Word → Prop}
    {a : Word} {xs : List E}
    (h : NewVecE s t a xs) (hf : DFrame t t' w) (hn : heapNext t ≤ heapNext t')
    (ha : ∀ i < 24, ¬ w (a + BitVec.ofNat 64 i))
    (hb : ∀ i < 24 * (vecLen t a).toNat, ¬ w (vecPtr t a + BitVec.ofNat 64 i)) :
    NewVecE s t' a xs := by
  have off (k : Nat) (hk : k + 8 ≤ 24) : t'.getMem (a + BitVec.ofNat 64 k) =
      t.getMem (a + BitVec.ofNat 64 k) :=
    hf _ fun i hi ↦ by rw [add_ofNat_add]; exact ha _ (by omega)
  have e0 : vecCap t' a = vecCap t a := by
    have := off 0 (by omega); simp only [add_ofNat_zero] at this; exact this
  have e1 : vecPtr t' a = vecPtr t a := off 8 (by omega)
  have e2 : vecLen t' a = vecLen t a := off 16 (by omega)
  obtain ⟨⟨hr, hl⟩, hb', he⟩ := h
  simp only [RawVecOk, Buf, NewBuf, heapStart] at hr hb'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, Buf, heapStart, e0, e1]; omega
  · rw [e0, e2]; exact hl
  · simp only [NewBuf, e0, e1]; omega
  · simp only [vecEs, e1, e2]; rw [← he]; exact hf.eListAt hb

/-- A stretch writing the scratch slots, the stack below the frame, `NEXT` and what it allocates
keeps `Mm`. -/
theorem Mm.keep {s z h e t t' : MachineState} {P : Word} {n : Nat} {fs : List (List Form)}
    {tot : List E} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z)
    (hPb : n = 0 ∨ heapNext z ≤ P.toNat) (M : Mm s z h e t P n fs tot)
    (fr : DFrame t t' (ItW s t t')) (heap : HeapOk t') (mono : heapNext t ≤ heapNext t')
    (sp : t'.getReg .x2 = t.getReg .x2) : Mm s z h e t' P n fs tot := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have It := M.cur.inv
  have hhE := It.heap.hi
  have hz := M.mat.mono
  have hlo := hpre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hhE hz hlo hsz
  have hw (x : Word) (h1 : heapStart ≤ x.toNat) (h2 : x.toNat + 8 ≤ heapNext t) :
      t'.getMem x = t.getMem x := ItW.kept hpre It.heap fr h2
  obtain ⟨M', hrow, hcell, hform⟩ := M.mat.keep It.heap mono hPb fun x h1 h2 ↦
    hw x (by simp only [heapStart, heapNext] at h1 ⊢; omega) h2
  have pe (a : Nat) (ha : a < n) (j : Nat) (hj : j ≤ 3) (x : Word) :
      piece t' P a j x ↔ piece t P a j x :=
    piece_congr (hrow a ha) (fun h3 k hk ↦ hcell a ha j h3 k hk) x
  have st : StepS s t t' (BlkW s) :=
    ⟨fr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ha)), heap, mono, sp⟩
  have hslot (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344)
      (hx : ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 8 → ¬ BlkW s y) :
      t'.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    fr _ (ItW.slot (t₀ := t) hpre heap hj hj2 hx)
  -- the totals' header
  have tw (q : Nat) (hq : q < 24) : ¬ ItW s t t' (s.getReg .x2 - 632 + BitVec.ofNat 64 q) := by
    rintro ((hw | hw) | hw | hw | ⟨-, hw⟩)
    · addr_omega [hw, hq, hb1]
    · addr_omega [hw, hq, hb1]
    · addr_omega [hw, hq, hb1]
    · addr_omega [hw, hq, hb1, hnx]
    · have := heap.hi; simp only [heapNext, heapEnd] at hw this; addr_omega [hw, hq, hb1, this]
  have h632 (q : Nat) (hq : q + 8 ≤ 24) : t'.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 q) =
      t.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 q) :=
    fr _ fun r hr ↦ by rw [add_ofNat_add]; exact tw _ (by omega)
  have tp : vecPtr t' (s.getReg .x2 - 632) = vecPtr t (s.getReg .x2 - 632) := h632 8 (by omega)
  have tc : vecCap t' (s.getReg .x2 - 632) = vecCap t (s.getReg .x2 - 632) := by
    have := h632 0 (by omega); simp only [add_ofNat_zero] at this; exact this
  have TB := M.totals
  refine ⟨M.cur.next hpre hsz st fun a ha ↦ Or.inl ?_, fun j hj hj2 hx ↦ (hslot j hj hj2 hx).trans
    (M.slots j hj hj2 hx), M', fun a ha j hj ↦ ?_, ?_, fun a ha j hj x hx ↦ M.gap a ha j hj x
    ((pe a ha j hj x).mp hx), le_trans M.mono mono, fun x h1 h2 ↦ ?_, ?_, fun x hx ↦ ?_⟩
  · simp only [SlotW]
    rcases ha with ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
  · have hptr : vecPtr t' (rowAt P a) = vecPtr t (rowAt P a) := by
      have h := hrow a ha 1 (by omega); simp only [Nat.mul_one] at h; exact h
    have hc : cellAt t' (rowAt P a) j = cellAt t (rowAt P a) j := by simp only [cellAt, hptr]
    have ep : vecPtr t' (cellAt t (rowAt P a) j) = vecPtr t (cellAt t (rowAt P a) j) := by
      simpa [vecPtr] using hcell a ha j hj 1 (by omega)
    have el : vecLen t' (cellAt t (rowAt P a) j) = vecLen t (cellAt t (rowAt P a) j) := by
      simpa [vecLen] using hcell a ha j hj 2 (by omega)
    rw [hc, ep, el]
    exact le_trans (M.below a ha j hj) mono
  · rw [formRowsAt_keep (fun a ha ↦ (M.mat.rows a ha).2) hrow hform]; exact M.value
  · have hk := M.hk x h1 h2
    have hm := M.mono
    simp only [heapNext] at h1 h2 hm
    rw [← hk]
    exact ItW.kept hpre It.heap fr (by simp only [heapNext]; omega)
  · refine TB.dframe' fr mono tw fun q hq hw ↦ ?_
    have hl := TB.vec.len
    have hbuf := TB.buf
    simp only [NewBuf] at hbuf
    rcases hbuf.2 with h0 | ⟨b1, b2⟩
    · omega
    · rcases hw with (hw | hw) | hw | hw | ⟨hw, -⟩
      · addr_omega [hw, hq, b1, b2, hl, hhE, hb1, hsz]
      · addr_omega [hw, hq, b1, b2, hl, hhE, hb1, hsz]
      · addr_omega [hw, hq, b1, b2, hl, hhE, hb1, hsz]
      · simp only [nextAddr] at hw; addr_omega [hw, hq, b1, b2, hl, hhE, hsz, hlo]
      · simp only [heapNext] at hw b2; addr_omega [hw, hq, b1, b2, hl, hhE]
  · rw [tp, tc] at hx
    obtain ⟨t1, t2⟩ := M.tbuf x hx
    exact ⟨t1, fun a ha j hj hp ↦ t2 a ha j hj ((pe a ha j hj x).mp hp)⟩

/-- `Blk` from `Mm`, the registers and the sum. -/
theorem Mm.blk {s z h e t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (M : Mm s z h e t P n (blkFold point i sd forms k).1 tot)
    (regs : ∀ r ∈ ([.x2, .x9, .x18, .x20, .x21, .x22, .x25, .x26] : List Reg), t.getReg r = e.getReg r)
    (x24 : t.getReg .x24 = BitVec.ofNat 64 k)
    (acc : eOf3 (t.getReg .x17) (t.getReg .x16) (t.getReg .x15) = (blkFold point i sd forms k).2) :
    Blk s z h e t i sd point P n forms tot k :=
  ⟨M.cur, M.slots, regs, x24, acc, M.mat, M.below, M.value, M.gap, M.mono, M.hk, M.totals, M.tbuf⟩

/-! ## The fold's step -/

theorem blkFold_succ {point : List E} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {forms : List (List Form)} {k : Nat}
    (hk : k < min sd.2.1.tables.length sd.1.length) :
    blkFold point i sd forms (k + 1) = busBlockStepRust point i sd.2.2.2.1 sd.2.2.2.2
      (blkFold point i sd forms k)
        ((tbSel sd point).getD k 0, sd.1[k]'(lt_of_lt_of_le hk (min_le_right _ _))) := by
  have h1 : k < (tbSel sd point).length := by
    simp only [tbSel, List.length_map]; exact lt_of_lt_of_le hk (min_le_left _ _)
  have h2 : k < sd.1.length := lt_of_lt_of_le hk (min_le_right _ _)
  simp only [blkFold]
  rw [List.take_add_one, List.foldl_append,
    List.getElem?_eq_getElem (by simp only [List.length_zip]; omega)]
  simp only [List.getElem_zip, List.getD_eq_getElem _ _ h1, Option.toList_some, List.foldl_cons,
    List.foldl_nil]

theorem blocks_get {s : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E}
    (hb : blocksAt s (blkVec s i) = sd.1) {k : Nat} (hk : k < sd.1.length) :
    sd.1[k] = blockAt s (blkAddr s i k) := by
  obtain ⟨b, rest⟩ := sd
  dsimp only at hb hk ⊢
  subst hb
  simp [blocksAt, blkAddr]

theorem modify_modify_const {l : List (List Form)} {o j : Nat} {f : Form → Form} {x : Form}
    (hx : ∀ (h1 : o < l.length) (h2 : j < l[o].length), l[o][j] = x) :
    l.modify o (fun row ↦ row.modify j fun _ ↦ f x) = l.modify o (fun row ↦ row.modify j f) := by
  apply List.ext_getElem (by simp)
  intro a h1 h2
  simp only [List.getElem_modify]
  by_cases ha : o = a
  · subst ha
    simp only [↓reduceIte]
    apply List.ext_getElem (by simp)
    intro b g1 g2
    simp only [List.getElem_modify]
    by_cases hb : j = b
    · subst hb; simp only [↓reduceIte]; rw [hx (by simpa using h1) (by simpa using g1)]
    · simp [hb]
  · simp [ha]

theorem formRowsAt_getElem {t : MachineState} {P : Word} {n o j : Nat} :
    ∀ (h1 : o < (formRowsAt t P n).length) (h2 : j < ((formRowsAt t P n)[o]'h1).length),
      ((formRowsAt t P n)[o]'h1)[j]'h2 = (Layout.formOf t (cellAt t (rowAt P o) j)).toSpec := by
  intro h1 h2
  simp [formRowsAt, formVecAt, cellAt, rowAt, Layout.formAt_eq]

/-- A form's header lies in its row's buffer. -/
theorem Mat.inRow {b t : MachineState} {P : Word} {n : Nat} (M : Mat b t P n) (hh : HeapOk t)
    {a j : Nat} (ha : a < n) (hj : j < 3) {x : Word} (hx : Within x (cellAt t (rowAt P a) j) 24) :
    piece t P a 3 x := by
  rw [piece_row]
  obtain ⟨hv, hl⟩ := M.rows a ha
  have hc := hv.len
  rw [hl] at hc
  have e3 : (3 : Word).toNat = 3 := rfl
  have hraw := hv.raw
  have hnt := hh.hi
  simp only [RawVecOk, Buf] at hraw
  simp only [heapNext, heapEnd] at hnt
  rcases hraw.2 with h0 | h0
  · omega
  · simp only [Layout.formVecBuf, cellAt, Within, heapNext] at hx h0 ⊢
    addr_omega [hx, h0, hc, hj, hnt]

theorem addTermRust_pos (terms : List LayoutMirror.Term) (m : LayoutMirror.Monomial) (c : E) :
    1 ≤ (LayoutMirror.addTermRust terms m c).length := by
  cases terms with
  | nil => simp [LayoutMirror.addTermRust]
  | cons t rest =>
    unfold LayoutMirror.addTermRust
    split <;> simp

theorem foldl_addTerm_length (w : E) (l : List LayoutMirror.Term) (A : List LayoutMirror.Term) :
    A.length ≤ (l.foldl (fun terms t ↦ LayoutMirror.addTermRust terms t.1 (w * t.2)) A).length := by
  induction l generalizing A with
  | nil => exact le_refl _
  | cons t rest ih =>
    simp only [List.foldl_cons]
    exact le_trans (addTermRust_length A t.1 (w * t.2)) (ih _)

theorem addScaled_pos (f g : LayoutMirror.FormRust) (w : E) (hg : 1 ≤ g.terms.length) :
    1 ≤ (f.addScaled g w).terms.length := by
  simp only [LayoutMirror.FormRust.addScaled]
  obtain ⟨gt⟩ := g
  cases gt with
  | nil => simp at hg
  | cons t rest =>
    simp only [List.foldl_cons]
    exact le_trans (addTermRust_pos _ _ _) (foldl_addTerm_length w rest _)

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
