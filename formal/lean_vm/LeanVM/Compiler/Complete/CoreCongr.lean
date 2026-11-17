/-
  LeanVM.Compiler.Complete.CoreCongr
  A valid tree's words, placement, data and loads depend on the frame sizes and cells of the
  program's functions only.
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.Memory.SizeTransfer

/-!
# Two layouts agreeing on the program

`AgreeOn P fs fs' cert cert'`: the frame sizes and the cells agree on every function of `P`. A
valid tree of `P` names only functions of `P` (its instances and its phantoms), so its words
(`total_eq`), and whether it is placed (`placed_iff`), its data (`data_iff`) and whether it loads in
a region (`loadsIn_iff`) are the same at the two layouts.
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Guest LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Two layouts agreeing on the functions of `P`.** -/
def AgreeOn (P : Core.Program) (fs fs' : String → ℕ) (cert cert' : String → V → ℕ) : Prop :=
  ∀ g fn, P.find? g = some fn → fs g = fs' g ∧ cert g = cert' g

variable {P : Core.Program} {rd : Reader} {fs fs' : String → ℕ} {cert cert' : String → V → ℕ}

theorem callsIn_true : CallsIn P (fun _ => True) := fun _ _ _ _ _ _ _ _ _ _ => trivial

/-- **The words of a valid tree** at two agreeing layouts. -/
theorem total_eq (hA : AgreeOn P fs fs' cert cert') {t : Tree} {args rets : List E}
    (hv : t.Valid P rd args rets) : t.total fs = t.total fs' :=
  total_congr callsIn_true (fun g _ fn hf => (hA g fn hf).1) t trivial hv

/-- The words of valid callees at two agreeing layouts. -/
theorem mapTotal_eq (hA : AgreeOn P fs fs' cert cert') :
    ∀ {ks : List Tree} {σ : Val} {cs : List Call}, Tree.KidsValid P rd σ cs ks →
      ks.map (Tree.total fs) = ks.map (Tree.total fs')
  | [], _, _, _ => rfl
  | _ :: _, _, [], hv => hv.elim
  | k :: ks, σ, c :: cs, hv => by
      obtain ⟨-, hk, hv'⟩ := hv
      rw [List.map_cons, List.map_cons, mapTotal_eq hA hv']
      congr 1
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        exact total_eq hA hk
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, fn', hfn', -⟩ := hk
        simp only [Tree.name] at hfn'
        rw [Tree.total, Tree.total, (hA f' fn' hfn').1]

theorem bufBase_eq {lp : String → Bool} {fp : ℕ} {f : String} {ns : List ℕ} (h : fs f = fs' f) :
    bufBase fs lp fp f ns = bufBase fs' lp fp f ns := by
  unfold bufBase
  rw [h]

theorem kidPos_eq {lp : String → Bool} {fp : ℕ} {f : String} {bufs ns : List ℕ} (h : fs f = fs' f) :
    kidPos fs lp fp f bufs ns = kidPos fs' lp fp f bufs ns := by
  unfold kidPos bufBase
  rw [h]

theorem nodeAt_iff {fp : ℕ} {f : String} {σ : Val} {bufs ns : List ℕ} {es : List Ev}
    (hfs : fs f = fs' f) (hc : cert f = cert' f) :
    NodeAt P fs cert fp f σ bufs ns es ↔ NodeAt P fs' cert' fp f σ bufs ns es := by
  unfold NodeAt bufBase
  rw [hfs, hc]

theorem ownData_iff {fp b : ℕ} {f : String} {bufs : List ℕ} {es : List Ev} {i : ℕ}
    (hc : cert f = cert' f) : ownData cert fp b f bufs es i ↔ ownData cert' fp b f bufs es i := by
  unfold ownData
  rw [hc]

mutual
/-- **A valid tree is placed** at two agreeing layouts alike. -/
theorem placed_iff (hA : AgreeOn P fs fs' cert cert') :
    ∀ (t : Tree) {args rets : List E} (fp : ℕ), t.Valid P rd args rets →
      (t.Placed P fs cert fp ↔ t.Placed P fs' cert' fp)
  | .node f σ bufs kids, args, rets, fp, hv => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      obtain ⟨hfs, hc⟩ := hA f fn hf
      rw [placed_node, placed_node, mapTotal_eq hA hk, nodeAt_iff hfs hc, kidPos_eq hfs,
        placedKids_iff hA kids _ hk]
  | .phantom .., _, _, _, hv => hv.elim

/-- `placed_iff` for valid callees. -/
theorem placedKids_iff (hA : AgreeOn P fs fs' cert cert') :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call} (ps : List ℕ), Tree.KidsValid P rd σ cs ks →
      (Tree.PlacedKids P fs cert ps ks ↔ Tree.PlacedKids P fs' cert' ps ks)
  | [], _, _, ps, _ => iff_of_true (by cases ps <;> (rw [Tree.PlacedKids]; trivial))
      (by cases ps <;> (rw [Tree.PlacedKids]; trivial))
  | _ :: _, _, _, [], _ => iff_of_true (by rw [Tree.PlacedKids]; trivial)
      (by rw [Tree.PlacedKids]; trivial)
  | _ :: _, _, [], _ :: _, hv => hv.elim
  | k :: ks, σ, c :: cs, p :: ps, hv => by
      obtain ⟨-, hk, hv'⟩ := hv
      rw [placedKids_cons, placedKids_cons, placedKids_iff hA ks ps hv']
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        rw [placed_iff hA k p hk]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        exact and_congr_left' (iff_of_true (by rw [Tree.Placed]; trivial)
          (by rw [Tree.Placed]; trivial))
end

mutual
/-- **A valid tree's data** at two agreeing layouts. -/
theorem data_iff (hA : AgreeOn P fs fs' cert cert') :
    ∀ (t : Tree) {args rets : List E} (fp i : ℕ), t.Valid P rd args rets →
      (t.Data P fs cert fp i ↔ t.Data P fs' cert' fp i)
  | .node f σ bufs kids, args, rets, fp, i, hv => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      obtain ⟨hfs, hc⟩ := hA f fn hf
      rw [data_node, data_node, mapTotal_eq hA hk, bufBase_eq hfs, kidPos_eq hfs, ownData_iff hc,
        dataKids_iff hA kids _ i hk]
  | .phantom .., _, _, _, _, hv => hv.elim

/-- `data_iff` for valid callees. -/
theorem dataKids_iff (hA : AgreeOn P fs fs' cert cert') :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call} (ps : List ℕ) (i : ℕ),
      Tree.KidsValid P rd σ cs ks →
      (Tree.DataKids P fs cert ps ks i ↔ Tree.DataKids P fs' cert' ps ks i)
  | [], _, _, ps, _, _ => iff_of_false (by cases ps <;> (rw [Tree.DataKids]; exact id))
      (by cases ps <;> (rw [Tree.DataKids]; exact id))
  | _ :: _, _, _, [], _, _ => iff_of_false (by rw [Tree.DataKids]; exact id)
      (by rw [Tree.DataKids]; exact id)
  | _ :: _, _, [], _ :: _, _, hv => hv.elim
  | k :: ks, σ, c :: cs, p :: ps, i, hv => by
      obtain ⟨-, hk, hv'⟩ := hv
      rw [dataKids_cons, dataKids_cons, dataKids_iff hA ks ps i hv']
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        rw [data_iff hA k p i hk]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        exact or_congr_left (iff_of_false (by rw [Tree.Data]; exact id)
          (by rw [Tree.Data]; exact id))
end

mutual
/-- **A valid tree loads in a region** at two agreeing layouts alike. -/
theorem loadsIn_iff (hA : AgreeOn P fs fs' cert cert') :
    ∀ (t : Tree) {args rets : List E} (R : ℕ → Prop) (fp : ℕ), t.Valid P rd args rets →
      (t.LoadsIn P fs cert R fp ↔ t.LoadsIn P fs' cert' R fp)
  | .node f σ bufs kids, args, rets, R, fp, hv => by
      have hD : Tree.Data P fs cert fp (.node f σ bufs kids) =
          Tree.Data P fs' cert' fp (.node f σ bufs kids) :=
        funext fun i => propext (data_iff hA _ fp i hv)
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      obtain ⟨hfs, -⟩ := hA f fn hf
      rw [loadsIn_node, loadsIn_node, hD, mapTotal_eq hA hk, kidPos_eq hfs,
        loadsInKids_iff hA kids _ _ hk]
  | .phantom .., _, _, _, _, hv => hv.elim

/-- `loadsIn_iff` for valid callees. -/
theorem loadsInKids_iff (hA : AgreeOn P fs fs' cert cert') :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call} (R : ℕ → Prop) (ps : List ℕ),
      Tree.KidsValid P rd σ cs ks →
      (Tree.LoadsInKids P fs cert R ps ks ↔ Tree.LoadsInKids P fs' cert' R ps ks)
  | [], _, _, _, ps, _ => iff_of_true (by cases ps <;> (rw [Tree.LoadsInKids]; trivial))
      (by cases ps <;> (rw [Tree.LoadsInKids]; trivial))
  | _ :: _, _, _, _, [], _ => iff_of_true (by rw [Tree.LoadsInKids]; trivial)
      (by rw [Tree.LoadsInKids]; trivial)
  | _ :: _, _, [], _, _ :: _, hv => hv.elim
  | k :: ks, σ, c :: cs, R, p :: ps, hv => by
      obtain ⟨-, hk, hv'⟩ := hv
      rw [loadsInKids_cons, loadsInKids_cons, loadsInKids_iff hA ks R ps hv']
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        rw [loadsIn_iff hA k R p hk]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        exact and_congr_left' (iff_of_true (by rw [Tree.LoadsIn]; trivial)
          (by rw [Tree.LoadsIn]; trivial))
end

end
end LeanVM.Compiler.Complete
