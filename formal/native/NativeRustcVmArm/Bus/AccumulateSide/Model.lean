module

public import NativeRustcVmArm.Tables.TableTerms.Model
public import NativeRustcVm.Bus.Blocks
public import NativeRustcVm.Bus.FitsModel
public import Mathlib.Data.List.GetD

/-!
# `accumulate_side`: the model as the Rust computes it

`accumulateSide` loop by loop (`accumulateSide_eq`): the known part over the first
`min |framework| |fingerprints|` framework blocks (`knownN`), the ones over the framework then
the table blocks (`onesF`, `onesT`), the table blocks' forms and padding rows (`stAt`, a turn
`stepT`). `E`'s sum limb by limb (`add_c0`, `add_c1`), commutative and associative. `TABLES`'
padding spans read `PADDING` (`padding_read`). The forms only grow through the loop
(`slot_size_mono`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeVm.Model NativeRustcVm.Bus

@[expose] public section

section
variable (SL : BusLayoutW) (point : Array EW)

/-- Framework block `i`'s selector. -/
def fsel (i : Nat) : EW := eqAbove (SL.framework.getD i default) point

/-- Table block `i`'s selector. -/
def tsel (i : Nat) : EW := eqAbove (SL.tables.getD i default) point

/-- The ones over the first `k` framework blocks. -/
def onesF (k : Nat) : EW := (List.range k).foldl (fun acc i ↦ acc + fsel SL point i) 1

/-- The ones over the framework and the first `j` table blocks. -/
def onesT (j : Nat) : EW :=
  (List.range j).foldl (fun acc i ↦ acc + tsel SL point i) (onesF SL point SL.framework.size)

end

/-- The known part over the first `c` framework blocks. -/
def knownN (SL : BusLayoutW) (point fps : Array EW) (beta : EW) (c : Nat) : EW :=
  (List.range c).foldl (fun acc i ↦ acc + fsel SL point i * (beta + fps.getD i 0)) 0

/-- A turn of the table loop: block `i`'s form added to its owner's form of the side, its padding
row. -/
def stepT (side : Nat) (B : Array BusBlockW) (SL : BusLayoutW) (w : Array EW) (beta : EW)
    (point : Array EW) (acc : Array (Array FormW) × EW) (i : Nat) : Array (Array FormW) × EW :=
  let block := B.getD i default
  let selector := tsel SL point i
  let form := blockForm block w beta
  let padding := (tablesW.getD block.owner default).padding
  (acc.1.modify block.owner fun row ↦ row.modify side fun f ↦ f.addScaled form selector,
    acc.2 + selector * paddingWeight (point.extract 0 block.logRows) block.rows *
      (form.evaluate padding + 1))

/-- The first `j` turns. -/
def stAt (F : Array (Array FormW)) (side : Nat) (B : Array BusBlockW) (SL : BusLayoutW)
    (w : Array EW) (beta : EW) (point : Array EW) (j : Nat) : Array (Array FormW) × EW :=
  (List.range j).foldl (stepT side B SL w beta point) (F, 0)

end

public section

/-! ## `E`'s sum -/

theorem ew_ext {a b : EW} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp only at h0 h1; rw [h0, h1]

theorem add_c0 (a b : EW) : (a + b).c0 = a.c0 ^^^ b.c0 := rfl
theorem add_c1 (a b : EW) : (a + b).c1 = a.c1 ^^^ b.c1 := rfl

theorem ew_add_comm (a b : EW) : a + b = b + a :=
  ew_ext (UInt64.xor_comm _ _) (UInt64.xor_comm _ _)

theorem ew_add_assoc (a b c : EW) : a + b + c = a + (b + c) :=
  ew_ext (UInt64.xor_assoc _ _ _) (UInt64.xor_assoc _ _ _)

theorem ew_zero_add (a : EW) : 0 + a = a := ew_ext UInt64.zero_xor UInt64.zero_xor

theorem ew_add_zero (a : EW) : a + 0 = a := ew_ext UInt64.xor_zero UInt64.xor_zero

theorem c0_zero : (0 : EW).c0 = 0 := rfl
theorem c1_zero : (0 : EW).c1 = 0 := rfl
theorem c0_one : (1 : EW).c0 = 1 := rfl
theorem c1_one : (1 : EW).c1 = 0 := rfl

/-- A sum's start moved out. -/
theorem foldl_add_shift (l : List EW) (a b : EW) :
    l.foldl (· + ·) a + b = l.foldl (· + ·) (a + b) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [ih, ew_add_assoc, ew_add_comm x b, ← ew_add_assoc]

/-! ## Folds over indices -/

theorem foldl_congr_mem {α β : Type} {l : List β} {f g : α → β → α} (a : α)
    (h : ∀ acc, ∀ x ∈ l, f acc x = g acc x) : l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h a x (List.mem_cons_self ..)]
    exact ih _ fun acc y hy ↦ h acc y (List.mem_cons_of_mem _ hy)

theorem foldl_range_congr {α : Type} {n : Nat} {f g : α → Nat → α} (a : α)
    (h : ∀ acc, ∀ i < n, f acc i = g acc i) :
    (List.range n).foldl f a = (List.range n).foldl g a :=
  foldl_congr_mem a fun acc i hi ↦ h acc i (List.mem_range.mp hi)

theorem foldl_range_getD {α β : Type} [Inhabited β] (l : List β) (f : α → β → α) (a : α) :
    l.foldl f a = (List.range l.length).foldl (fun acc i ↦ f acc (l.getD i default)) a := by
  induction l using List.reverseRecOn generalizing a with
  | nil => rfl
  | append_singleton l x ih =>
    rw [List.foldl_append, ih, List.length_append, List.length_singleton, List.range_succ,
      List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    congr 1
    · refine foldl_range_congr _ fun acc i hi ↦ ?_
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
      simp

/-- A fold over a mapped array, by indices. -/
theorem foldl_map_range {α β γ : Type} [Inhabited β] (a : Array β) (g : β → γ) (f : α → γ → α)
    (x : α) : (a.map g).toList.foldl f x =
      (List.range a.size).foldl (fun acc i ↦ f acc (g (a.getD i default))) x := by
  rw [Array.toList_map, List.foldl_map, foldl_range_getD a.toList, Array.length_toList]
  refine foldl_range_congr _ fun acc i hi ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hi), Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hi, Option.getD_some, Array.getElem_toList]

theorem foldl_range_succ {α : Type} (f : α → Nat → α) (a : α) (n : Nat) :
    (List.range (n + 1)).foldl f a = f ((List.range n).foldl f a) n := by
  rw [List.range_succ, List.foldl_append]; rfl

/-! ## The loops -/

section
variable (SL : BusLayoutW) (point fps : Array EW) (beta : EW)

theorem knownN_zero : knownN SL point fps beta 0 = 0 := rfl

theorem knownN_succ (c : Nat) : knownN SL point fps beta (c + 1) =
    knownN SL point fps beta c + fsel SL point c * (beta + fps.getD c 0) :=
  foldl_range_succ _ _ _

theorem onesF_zero : onesF SL point 0 = 1 := rfl

theorem onesF_succ (k : Nat) : onesF SL point (k + 1) = onesF SL point k + fsel SL point k :=
  foldl_range_succ _ _ _

theorem onesT_zero : onesT SL point 0 = onesF SL point SL.framework.size := rfl

theorem onesT_succ (j : Nat) : onesT SL point (j + 1) = onesT SL point j + tsel SL point j :=
  foldl_range_succ _ _ _

end

theorem stAt_zero (F : Array (Array FormW)) (side : Nat) (B : Array BusBlockW) (SL : BusLayoutW)
    (w : Array EW) (beta : EW) (point : Array EW) : stAt F side B SL w beta point 0 = (F, 0) := rfl

theorem stAt_succ (F : Array (Array FormW)) (side : Nat) (B : Array BusBlockW) (SL : BusLayoutW)
    (w : Array EW) (beta : EW) (point : Array EW) (j : Nat) :
    stAt F side B SL w beta point (j + 1) =
      stepT side B SL w beta point (stAt F side B SL w beta point j) j :=
  foldl_range_succ _ _ _

/-- **`accumulateSide` loop by loop.** -/
theorem accumulateSide_eq (F : Array (Array FormW)) (side : Nat) (B : Array BusBlockW)
    (SL : BusLayoutW) (fps w : Array EW) (beta : EW) (point : Array EW) (tree : EW)
    (hsz : SL.tables.size = B.size) :
    accumulateSide F side B SL fps w beta point tree =
      ((stAt F side B SL w beta point B.size).1,
        tree + knownN SL point fps beta (min SL.framework.size fps.size) +
          onesT SL point B.size + (stAt F side B SL w beta point B.size).2) := by
  unfold accumulateSide
  simp only
  have hloop : ((SL.tables.map (eqAbove · point)).zip B).foldl
      (fun (acc : Array (Array FormW) × EW) (x : EW × BusBlockW) ↦
        (acc.1.modify x.2.owner fun row ↦ row.modify side fun f ↦
          f.addScaled (blockForm x.2 w beta) x.1,
         acc.2 + x.1 * paddingWeight (point.extract 0 x.2.logRows) x.2.rows *
          ((blockForm x.2 w beta).evaluate (tablesW.getD x.2.owner default).padding + 1)))
      (F, 0) = stAt F side B SL w beta point B.size := by
    rw [← Array.foldl_toList, foldl_range_getD]
    simp only [Array.toList_zip, List.length_zip, Array.length_toList, Array.size_map, hsz,
      Nat.min_self]
    refine foldl_range_congr _ fun acc i hi ↦ ?_
    have h1 : i < SL.tables.size := by omega
    rw [List.getD_eq_getElem _ _ (by simp [hsz]; exact hi), List.getElem_zip]
    simp only [Array.getElem_toList, Array.getElem_map]
    unfold stepT tsel
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem hi, Option.getD_some]
  have hknown : dot (SL.framework.map (eqAbove · point)) (fps.map (beta + ·)) =
      knownN SL point fps beta (min SL.framework.size fps.size) := by
    unfold dot knownN
    rw [← Array.foldl_toList, foldl_range_getD]
    simp only [Array.toList_zipWith, List.length_zipWith, Array.length_toList, Array.size_map]
    refine foldl_range_congr _ fun acc i hi ↦ ?_
    have h1 : i < SL.framework.size := by omega
    have h2 : i < fps.size := by omega
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_zipWith]
    simp [fsel, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h2]
  have hones : sumE (SL.framework.map (eqAbove · point) ++ SL.tables.map (eqAbove · point)) + 1 =
      onesT SL point B.size := by
    unfold sumE onesT onesF
    rw [← Array.foldl_toList, foldl_add_shift, ew_zero_add, Array.toList_append,
      List.foldl_append, foldl_map_range, foldl_map_range, ← hsz]
    rfl
  rw [hknown, hones]
  rw [hloop]

/-! ## The data -/

/-- **`TABLES`' padding spans read `PADDING`.** -/
theorem padding_read {o : Nat} (ho : o < 6) :
    let st := (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 3) 0).toNat
    let ln := (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + 4) 0).toNat
    st + ln < 154 ∧ ((NativeRustcVm.Data.padding.drop st).take ln) =
      (tablesW.getD o default).padding.toList := by
  have h1 : ∀ o : Fin 6,
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o.val + 3) 0).toNat +
        (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o.val + 4) 0).toNat < 154 := by
    decide +kernel
  have h2 : ∀ o : Fin 6,
      ((NativeRustcVm.Data.padding.drop
          (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o.val + 3) 0).toNat).take
        (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o.val + 4) 0).toNat) =
        ((LeanVM.Protocol.Verifier.tables.map TableW.ofTable).getD o.val default).padding.toList := by
    decide +kernel
  refine ⟨h1 ⟨o, ho⟩, ?_⟩
  rw [NativeVm.Math.Tables.tablesW_get]
  exact h2 ⟨o, ho⟩

theorem padding_length : NativeRustcVm.Data.padding.length = 153 := by decide +kernel

/-! ## The forms grow -/

theorem addTerm_size_le (f : FormW) (m : Array Nat) (c : EW) : f.size ≤ (f.addTerm m c).size := by
  unfold FormW.addTerm
  split <;> simp

theorem addScaled_size_le (f other : FormW) (w : EW) : f.size ≤ (f.addScaled other w).size := by
  unfold FormW.addScaled
  rw [← Array.foldl_toList]
  generalize other.toList = l
  induction l generalizing f with
  | nil => exact Nat.le_refl _
  | cons t l ih => exact Nat.le_trans (addTerm_size_le _ _ _) (ih _)

/-- A slot's form. -/
@[expose] def slotOf (G : Array (Array FormW)) (o s : Nat) : FormW := (G.getD o #[]).getD s #[]

theorem slotOf_modify (G : Array (Array FormW)) (o s o' s' : Nat) (g : FormW → FormW) :
    slotOf (G.modify o fun row ↦ row.modify s g) o' s' =
      if o = o' ∧ s = s' ∧ o < G.size ∧ s < (G.getD o #[]).size then g (slotOf G o' s')
      else slotOf G o' s' := by
  unfold slotOf
  by_cases ho : o = o'
  · subst ho
    by_cases hoG : o < G.size
    · have e : (G.modify o fun row ↦ row.modify s g).getD o #[] = G[o].modify s g := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getElem?_eq_getElem hoG]
        simp
      have e2 : G.getD o #[] = G[o] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hoG]; rfl
      rw [e, e2]
      by_cases hs : s = s'
      · subst hs
        by_cases hsr : s < G[o].size
        · simp [Array.getD_eq_getD_getElem?, hsr, hoG, Array.getElem_modify]
        · simp [Array.getD_eq_getD_getElem?, hsr]
      · simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, hs]
    · simp [Array.getD_eq_getD_getElem?, hoG]
  · simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, ho]

theorem slot_size_step (side : Nat) (B : Array BusBlockW) (SL : BusLayoutW) (w : Array EW)
    (beta : EW) (point : Array EW) (acc : Array (Array FormW) × EW) (i o s : Nat) :
    (slotOf acc.1 o s).size ≤ (slotOf (stepT side B SL w beta point acc i).1 o s).size := by
  unfold stepT
  simp only
  rw [slotOf_modify]
  split
  · exact addScaled_size_le _ _ _
  · exact Nat.le_refl _

/-- **The forms only grow** through the loop. -/
theorem slot_size_mono (F : Array (Array FormW)) (side : Nat) (B : Array BusBlockW)
    (SL : BusLayoutW) (w : Array EW) (beta : EW) (point : Array EW) (o s : Nat) {j k : Nat}
    (hjk : j ≤ k) :
    (slotOf (stAt F side B SL w beta point j).1 o s).size ≤
      (slotOf (stAt F side B SL w beta point k).1 o s).size := by
  induction k, hjk using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ k _ ih =>
    rw [stAt_succ]
    exact Nat.le_trans ih (slot_size_step _ _ _ _ _ _ _ _ _ _)

theorem stAt_size (F : Array (Array FormW)) (side : Nat) (B : Array BusBlockW)
    (SL : BusLayoutW) (w : Array EW) (beta : EW) (point : Array EW) (j : Nat) :
    (stAt F side B SL w beta point j).1.size = F.size ∧
      ∀ o (h1 : o < F.size) (h2 : o < (stAt F side B SL w beta point j).1.size),
        ((stAt F side B SL w beta point j).1[o]).size = F[o].size := by
  induction j with
  | zero => exact ⟨rfl, fun o _ _ ↦ rfl⟩
  | succ j ih =>
    rw [stAt_succ]
    unfold stepT
    simp only [Array.size_modify]
    refine ⟨ih.1, fun o h1 h2 ↦ ?_⟩
    rw [Array.getElem_modify]
    split
    · rw [Array.size_modify]; exact ih.2 o h1 (by rw [ih.1]; exact h1)
    · exact ih.2 o h1 (by rw [ih.1]; exact h1)

end

end NativeRustcVmArm.Bus.AccumulateSide
