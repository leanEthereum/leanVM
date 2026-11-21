module

public import NativeVm.Code.Phase3.Common
public import NativeVm.Code.Phase3.FormsDataDefs
public import NativeVm.Equiv.FormFacts

/-!
# The bus forms of a side: the model's facts

* A block of the data as a form: `buildF es ws β`, `const β` and each entry's term added
  (`FormW.addTerm`), is `blockForm` of a block with those entries (`blockForm_eq_buildF`).
* Shapes: a form's monomials (`shape`) do not depend on the coefficients: `addTerm` appends a new
  monomial (`shape_addTerm`, `addMono`), so a side's forms' shapes are static (`blockShape`,
  `ownerShape`), each a prefix of the whole data's (`ownerShape_prefix`).
* Keys: monomials of degree at most two are equal when their degree and two columns are
  (`eq_iff_key`).
* The padding row: column `a` of a table's padding row is `Pv a` in limb `0` (`padding_getD`), the
  lane of `keccakF1600` of zeros for `KECCAK`'s output lanes, else `0`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open NativeVm.Model NativeVm.Equiv LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Semantics

theorem iteT {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem iteF {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-! ## Products by an element of `K` -/

/-- An element of `K` in limb `0`. -/
abbrev kE (k : UInt64) : EW := ⟨k, 0⟩

theorem scale_eq_mul (k : UInt64) (w : EW) : EW.scale k w = w * kE k := by
  apply EW.toE_injective
  rw [EW.toE_scale, EW.toE_mul, show kE k = EW.ofK k from rfl, EW.toE_ofK, mul_comm]

theorem zero_add_ew (c : EW) : (0 : EW) + c = c := by
  rcases c with ⟨a, b⟩
  show EW.mk (0 ^^^ a) (0 ^^^ b) = _
  rw [UInt64.zero_xor, UInt64.zero_xor]

/-! ## Shapes -/

/-- A monomial appended unless present. -/
def addMono (l : List (List Nat)) (m : List Nat) : List (List Nat) := if m ∈ l then l else l ++ [m]

/-- A form's monomials, in order. -/
def shape (f : FormW) : List (List Nat) := f.toList.map fun t ↦ t.cols.toList

theorem shape_addTerm (f : FormW) (m : Array Nat) (c : EW) :
    shape (f.addTerm m c) = addMono (shape f) m.toList := by
  unfold FormW.addTerm
  split
  · rename_i i h
    rw [Array.findIdx?_eq_some_iff_getElem] at h
    obtain ⟨hi, he, -⟩ := h
    have hm : m.toList ∈ shape f := by
      simp only [beq_iff_eq] at he
      simp only [shape, List.mem_map, Array.mem_toList_iff]
      exact ⟨f[i], Array.getElem_mem hi, by rw [he]⟩
    simp only [addMono, hm, ite_true]
    unfold shape
    rw [Array.toList_modify]
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_modify]
    split <;> rfl
  · rename_i h
    rw [Array.findIdx?_eq_none_iff] at h
    have hm : m.toList ∉ shape f := by
      simp only [shape, List.mem_map, Array.mem_toList_iff, not_exists, not_and]
      intro t ht e
      have := h t ht
      rw [Array.toList_inj] at e
      simp [e] at this
    rw [addMono, iteF hm]
    simp [shape]

/-- `addTerm`'s fold over a list of terms, by shapes. -/
theorem shape_foldl_addTerm (l : List TermW) (g : TermW → EW) (f : FormW) :
    shape (l.foldl (fun acc t ↦ acc.addTerm t.cols (g t)) f) =
      (l.map fun t ↦ t.cols.toList).foldl addMono (shape f) := by
  induction l generalizing f with
  | nil => rfl
  | cons t l ih => rw [List.foldl_cons, ih, shape_addTerm]; rfl

theorem shape_addScaled (f g : FormW) (w : EW) :
    shape (f.addScaled g w) = (shape g).foldl addMono (shape f) := by
  unfold FormW.addScaled
  rw [← Array.foldl_toList, shape_foldl_addTerm]
  rfl

theorem addMono_prefix (l : List (List Nat)) (m : List Nat) : l <+: addMono l m := by
  unfold addMono; split
  · exact List.prefix_refl l
  · exact List.prefix_append l _

theorem foldl_addMono_prefix (xs : List (List Nat)) (l : List (List Nat)) :
    l <+: xs.foldl addMono l := by
  induction xs generalizing l with
  | nil => exact List.prefix_refl l
  | cons x xs ih => exact (addMono_prefix l x).trans (ih _)

theorem foldl_addMono_append (xs ys l : List (List Nat)) :
    xs.foldl addMono l <+: (xs ++ ys).foldl addMono l := by
  rw [List.foldl_append]
  exact foldl_addMono_prefix _ _

theorem mem_foldl_addMono {xs l : List (List Nat)} {x : List Nat} (h : x ∈ xs.foldl addMono l) :
    x ∈ l ∨ x ∈ xs := by
  induction xs generalizing l with
  | nil => exact .inl h
  | cons y ys ih =>
    rcases ih h with h' | h'
    · unfold addMono at h'
      split at h'
      · exact .inl h'
      · rcases List.mem_append.mp h' with h'' | h''
        · exact .inl h''
        · exact .inr (by simp_all)
    · exact .inr (List.mem_cons_of_mem _ h')

theorem length_foldl_addMono (xs l : List (List Nat)) :
    (xs.foldl addMono l).length ≤ l.length + xs.length := by
  induction xs generalizing l with
  | nil => simp
  | cons y ys ih =>
    have := ih (addMono l y)
    have : (addMono l y).length ≤ l.length + 1 := by unfold addMono; split <;> simp
    simp only [List.foldl_cons, List.length_cons]
    omega

/-! ## A block of the data as a form -/

/-- An entry's term: the monomial and the slot weight times the coefficient. -/
def entStep (ws : Array EW) (f : FormW) (e : DEnt) : FormW :=
  f.addTerm e.2.1.toArray (ws.getD e.1 0 * kE e.2.2.toUInt64)

/-- **A block's form** from its entries: `const β`, then each entry's term. -/
def buildF (es : List DEnt) (ws : Array EW) (β : EW) : FormW :=
  es.foldl (entStep ws) (FormW.const β)

/-- A block's monomials. -/
def blockShape (es : List DEnt) : List (List Nat) := (es.map (·.2.1)).foldl addMono [[]]

theorem shape_foldl_entStep (es : List DEnt) (ws : Array EW) (f : FormW) :
    shape (es.foldl (entStep ws) f) = (es.map (·.2.1)).foldl addMono (shape f) := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih => rw [List.foldl_cons, ih, entStep, shape_addTerm, List.toList_toArray]; rfl

theorem shape_buildF (es : List DEnt) (ws : Array EW) (β : EW) :
    shape (buildF es ws β) = blockShape es := by
  rw [buildF, shape_foldl_entStep]
  rfl

/-- A bus block's entries: each coordinate's terms with its slot. -/
def blockEnts (b : BusBlockW) : List (Nat × List Nat × EW) :=
  b.coordinates.toList.zipIdx.flatMap fun (c, k) ↦ c.toList.map fun t ↦ (k, t.cols.toList, t.coeff)

/-- The data's entries as a bus block's. -/
def entsW (es : List DEnt) : List (Nat × List Nat × EW) :=
  es.map fun e ↦ (e.1, e.2.1, kE e.2.2.toUInt64)

theorem blockForm_eq_buildF {b : BusBlockW} {es : List DEnt} (h : blockEnts b = entsW es)
    (ws : Array EW) (β : EW) : Model.blockForm b ws β = buildF es ws β := by
  have e1 : Model.blockForm b ws β = (blockEnts b).foldl
      (fun f x ↦ f.addTerm x.2.1.toArray (ws.getD x.1 0 * x.2.2)) (FormW.const β) := by
    unfold Model.blockForm blockEnts
    rw [← Array.foldl_toList, Array.toList_zipIdx, List.foldl_flatMap]
    congr 1
    funext f x
    rcases x with ⟨c, k⟩
    show Array.foldl _ f c = _
    rw [← Array.foldl_toList]
    show _ = List.foldl _ f (c.toList.map _)
    rw [List.foldl_map]
  rw [e1, h, entsW, List.foldl_map]
  rfl

/-! ## The shapes of a side's forms -/

/-- One block's monomials added to an owner's. -/
def shapeStep (o : Nat) (sh : List (List Nat)) (b : DBlk) : List (List Nat) :=
  if b.1 = o then (blockShape b.2).foldl addMono sh else sh

/-- Owner `o`'s form's monomials after the blocks `Dp`. -/
def ownerShape (Dp : List DBlk) (o : Nat) : List (List Nat) := Dp.foldl (shapeStep o) []

theorem shapeStep_prefix (o : Nat) (sh : List (List Nat)) (b : DBlk) : sh <+: shapeStep o sh b := by
  unfold shapeStep; split
  · exact foldl_addMono_prefix _ _
  · exact List.prefix_refl sh

theorem foldl_shapeStep_prefix (o : Nat) (xs : List DBlk) (sh : List (List Nat)) :
    sh <+: xs.foldl (shapeStep o) sh := by
  induction xs generalizing sh with
  | nil => exact List.prefix_refl sh
  | cons x xs ih => exact (shapeStep_prefix o sh x).trans (ih _)

theorem ownerShape_prefix (D : List DBlk) (i o : Nat) : ownerShape (D.take i) o <+: ownerShape D o := by
  conv_rhs => rw [← List.take_append_drop i D]
  unfold ownerShape
  rw [List.foldl_append]
  exact foldl_shapeStep_prefix _ _ _

theorem ownerShape_succ {D : List DBlk} {i : Nat} (hi : i < D.length) (o : Nat) :
    ownerShape (D.take (i + 1)) o = shapeStep o (ownerShape (D.take i) o) D[i] := by
  unfold ownerShape
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

/-! ## Keys -/

/-- A monomial of degree at most two is its degree and two columns, zero past the degree. -/
theorem eq_iff_key {a b : Array Nat} (ha : a.size ≤ 2) (hb : b.size ≤ 2)
    (ha' : ∀ i (h : i < a.size), a[i] < 2 ^ 64) (hb' : ∀ i (h : i < b.size), b[i] < 2 ^ 64) :
    a = b ↔ a.size.toUInt64 = b.size.toUInt64 ∧ (a.getD 0 0).toUInt64 = (b.getD 0 0).toUInt64 ∧
      (a.getD 1 0).toUInt64 = (b.getD 1 0).toUInt64 := by
  have g : ∀ (c : Array Nat) (j : Nat), (∀ i (h : i < c.size), c[i] < 2 ^ 64) → c.getD j 0 < 2 ^ 64 :=
    fun c j h ↦ by
      rw [Array.getD_eq_getD_getElem?]
      by_cases hj : j < c.size
      · rw [Array.getElem?_eq_getElem hj]; exact h j hj
      · rw [Array.getElem?_eq_none (by omega)]; simp
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    rw [NativeVm.Transcript.toUInt64_inj (by omega) (by omega)] at h1
    rw [NativeVm.Transcript.toUInt64_inj (g a 0 ha') (g b 0 hb')] at h2
    rw [NativeVm.Transcript.toUInt64_inj (g a 1 ha') (g b 1 hb')] at h3
    refine Array.ext h1 fun i hi hi' ↦ ?_
    have e1 : a[i] = a.getD i 0 := by rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]; rfl
    have e2 : b[i] = b.getD i 0 := by rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']; rfl
    rw [e1, e2]
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact h2
    · exact h3

theorem key_test (a b c a' b' c' : UInt64) :
    (a ^^^ a' ||| (b ^^^ b') ||| (c ^^^ c')) = 0 ↔ a = a' ∧ b = b' ∧ c = c' := by
  simp only [UInt64.or_eq_zero_iff, UInt64.xor_eq_zero_iff, and_assoc]

/-! ## The padding row -/

/-- `KECCAK`'s padding row's output lanes: `keccakF1600` of the zero state. -/
def padOut : KeccakState := keccakF1600 (Vector.replicate 25 0)

/-- Column `a` of the padding row, as a lane: output lane `a - 40` for `40 ≤ a < 65`, else `0`. -/
def Pv (a : Nat) : UInt64 := if 40 ≤ a ∧ a < 65 then Keccak.lane padOut (a - 40) else 0

theorem tables_shape6 : tables.map (fun t ↦ (t.opcode, t.width)) =
    [(0, 13), (1, 13), (2, 7), (3, 14), (4, 14), (5, 92)] := by decide +kernel

theorem keccakOut_val : keccakOut = 40 := by decide +kernel

theorem opKeccak_val : opKeccak = 5 := by decide +kernel

theorem ofE_eOfNat (n : Nat) : EW.ofE (eOfNat n) = ⟨n.toUInt64, 0⟩ := by
  rw [← EW.toE_ofNat, EW.ofE_toE]; rfl

theorem ofE_zero : EW.ofE 0 = (⟨0, 0⟩ : EW) := by
  rw [← EW.toE_zero, EW.ofE_toE]; rfl

/-- A table's padding row at a column: its padding lane if `KECCAK`'s output lane, else `0`. -/
theorem table_padding_getD (t : Table) (a : Nat) :
    (t.padding.toArray.map EW.ofE).getD a 0 =
      if a < t.width ∧ t.opcode = opKeccak ∧ keccakOut ≤ a ∧ a < keccakOut + 25 then
        ⟨Keccak.lane (keccakF1600 (Vector.replicate 25 0)) (a - keccakOut), 0⟩ else ⟨0, 0⟩ := by
  unfold Table.padding
  generalize keccakF1600 (Vector.replicate 25 0) = out
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray]
  by_cases ha : a < t.width
  · rw [List.getElem?_map, List.getElem?_range ha]
    simp only [Option.map_some, Option.getD_some]
    by_cases hc : t.opcode = opKeccak ∧ keccakOut ≤ a ∧ a < keccakOut + 25
    · rw [iteT (hc), iteT (⟨ha, hc⟩), ofE_eOfNat]
      congr 1
      exact UInt64.ofNat_toNat
    · rw [iteF (hc), iteF ((fun h ↦ hc h.2)),
        ofE_zero]
  · rw [List.getElem?_eq_none (by simpa using ha), iteF ((fun h ↦ ha h.1))]
    rfl

/-- **The padding row**: column `a` of table `o`'s padding row is `Pv a` in limb `0`, for a column
of `KECCAK` or a column below its output lanes. -/
theorem padding_getD {o a : Nat} (ho : o < 6) (ha : a < 92) (h5 : o ≠ 5 → a < 40) :
    (tablesW.getD o default).padding.getD a 0 = kE (Pv a) := by
  have hw : ∀ i < 6, ((tables.getD i default).opcode, (tables.getD i default).width) =
      [(0, 13), (1, 13), (2, 7), (3, 14), (4, 14), (5, 92)].getD i (0, 0) := by
    intro i hi
    rw [← tables_shape6]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    have : i < tables.length := by
      have := congrArg List.length tables_shape6; simp at this; omega
    rw [List.getElem?_eq_getElem this]; rfl
  have ht : tablesW.getD o default = TableW.ofTable (tables.getD o default) := by
    have : o < tables.length := by
      have := congrArg List.length tables_shape6; simp at this; omega
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, tablesW, Array.getElem?_map,
      List.getElem?_toArray, List.getElem?_eq_getElem this]
    rfl
  rw [ht, show (TableW.ofTable (tables.getD o default)).padding =
    (tables.getD o default).padding.toArray.map EW.ofE from rfl, table_padding_getD]
  have := hw o ho
  rw [keccakOut_val, opKeccak_val]
  unfold Pv
  generalize (tables.getD o default).opcode = op at this ⊢
  generalize (tables.getD o default).width = w at this ⊢
  rw [show keccakF1600 (Vector.replicate 25 0) = padOut from rfl]
  rcases (show o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [List.getD_cons_succ, List.getD_cons_zero,
      Prod.mk.injEq] at this <;> obtain ⟨rfl, rfl⟩ := this
  all_goals first
    | (have := h5 (by decide)
       rw [iteF ((by omega)), iteF ((by omega))])
    | (by_cases hc : 40 ≤ a ∧ a < 65
       · rw [iteT (⟨ha, rfl, hc.1, by omega⟩), iteT (hc)]
       · rw [iteF ((by omega)), iteF (hc)])

end NativeVm.Code.P3
