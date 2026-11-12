/-
  LeanVM.Guest.B1.Whir.CFinO

  The finish's out-of-domain weights and returns are pure blocks in order.
-/

module

public import LeanVM.Guest.B1.Whir.CFinEval
public import LeanVM.Guest.B1.Whir.OodW

/-!
# The out-of-domain weights, in order (G:1838-1848)

`osOodWeights_ssa`: the weights of the levels `ol ..` define their values in order, reading only
`ood_scalars`, `ood_z` and the coordinates' sources (`fold_challenges`, `tail_challenges`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

theorem osOodFacs_ssa : ∀ (cs : List (ℕ × ℕ × ℕ)) (sc k : ℕ), 33 ≤ k → sc < k →
    (∀ x ∈ cs, x.2.1 < k) →
    SsaP k (osOodFacs sc cs k).1 (osOodFacs sc cs k).2.2 ∧
      (osOodFacs sc cs k).2.1 < (osOodFacs sc cs k).2.2 ∧
      (∀ p o, (p, o) ∈ loadsOf (osOodFacs sc cs k).1 →
        (p = osOodz ∧ ∃ x ∈ cs, o = x.1) ∨ (∃ x ∈ cs, (p, o) = x.2))
  | [], sc, k, _, hsc, _ => ⟨.nil, hsc, by simp [osOodFacs, loadsOf]⟩
  | (zo, src) :: rest, sc, k, hk, hsc, hs => by
    have hsrc : src.1 < k := hs _ (List.mem_cons_self ..)
    obtain ⟨r1, r2, r3⟩ := osOodFacs_ssa rest (k + 5) (k + 6) (by omega) (by omega)
      (fun x hx ↦ lt_trans (hs x (List.mem_cons_of_mem _ hx)) (by omega))
    refine ⟨.const le_rfl (.load (by omega) (by show 26 < k + 1; omega) (.add (by omega) (by omega)
      (by omega) (.load (by omega) (by omega) (.add (by omega) (by omega) (by omega)
        (.mul (by omega) (by omega) (by omega) r1))))), r2, fun p o hm ↦ ?_⟩
    simp only [osOodFacs, List.cons_append, loadsOf, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | hm
    · exact Or.inl ⟨h1, (zo, src), List.mem_cons_self .., h2⟩
    · exact Or.inr ⟨(zo, src), List.mem_cons_self .., by rw [h1, h2]⟩
    · rcases r3 p o hm with ⟨hp, x, hx, ho⟩ | ⟨x, hx, he⟩
      · exact Or.inl ⟨hp, x, List.mem_cons_of_mem _ hx, ho⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, he⟩

theorem osOodWeight_ssa (c : OsCfg) (tch prevCols ol : ℕ) (lv : OsLv) (k : ℕ) (htch : tch < k)
    (hk : 33 ≤ k) :
    SsaP k (osOodWeight c tch prevCols ol lv k).1 (osOodWeight c tch prevCols ol lv k).2.2 ∧
      (osOodWeight c tch prevCols ol lv k).2.1 < (osOodWeight c tch prevCols ol lv k).2.2 ∧
      (∀ p o, (p, o) ∈ loadsOf (osOodWeight c tch prevCols ol lv k).1 →
        (p = osOodSc ∧ o = ol) ∨
        (p = osOodz ∧ ∃ x ∈ oodCoords c tch prevCols ol lv, o = x.1) ∨
        (∃ x ∈ oodCoords c tch prevCols ol lv, (p, o) = x.2)) := by
  rw [osOodWeight_eq]
  obtain ⟨r1, r2, r3⟩ := osOodFacs_ssa (oodCoords c tch prevCols ol lv) k (k + 1) (by omega)
    (by omega) (fun x hx ↦ by
      simp only [oodCoords, List.mem_map, List.mem_range] at hx
      obtain ⟨t, -, rfl⟩ := hx
      have h19 : osFch < k + 1 := by show 16 < k + 1; omega
      split_ifs <;> simp only <;> omega)
  refine ⟨.load le_rfl (by show 28 < k; omega) r1, r2, fun p o hm ↦ ?_⟩
  simp only [loadsOf, List.mem_cons, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | hm
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (r3 p o hm)

theorem osAcc_ssa (acc : Option ℕ) (w k : ℕ) (hw : w < k) (hacc : ∀ x, acc = some x → x < k) :
    SsaP k (osAcc acc w k).1 (osAcc acc w k).2.2 ∧ (∀ x, (osAcc acc w k).2.1 = some x → x < (osAcc acc w k).2.2) ∧
      loadsOf (osAcc acc w k).1 = [] := by
  rcases acc with _ | x
  · refine ⟨.nil, fun x hx ↦ ?_, rfl⟩
    simp only [osAcc, Option.some.injEq] at hx ⊢; omega
  · refine ⟨.add le_rfl (hacc x rfl) hw .nil, fun y hy ↦ ?_, rfl⟩
    simp only [osAcc, Option.some.injEq] at hy ⊢; omega

/-- What the weights of the levels `ol ..` read: the scalar and point of each, and their
coordinates' sources. -/
def OodLoads (c : OsCfg) (tch : ℕ) : ℕ → ℕ → List OsLv → ℕ → ℕ → Prop
  | _, _, [], _, _ => False
  | prevCols, ol, lv :: rest, p, o =>
    ((p = osOodSc ∧ o = ol) ∨
      (p = osOodz ∧ ∃ x ∈ oodCoords c tch prevCols ol lv, o = x.1) ∨
      (∃ x ∈ oodCoords c tch prevCols ol lv, (p, o) = x.2)) ∨
    OodLoads c tch lv.logCols (ol + 1) rest p o

theorem osOodWeights_ssa (c : OsCfg) (tch : ℕ) :
    ∀ (prevCols ol : ℕ) (lvs : List OsLv) (acc : Option ℕ) (k : ℕ), tch < k → 33 ≤ k →
      (∀ x, acc = some x → x < k) →
      SsaP k (osOodWeights c tch prevCols ol lvs acc k).1 (osOodWeights c tch prevCols ol lvs acc k).2.2 ∧
        (∀ x, (osOodWeights c tch prevCols ol lvs acc k).2.1 = some x →
          x < (osOodWeights c tch prevCols ol lvs acc k).2.2) ∧
        (∀ p o, (p, o) ∈ loadsOf (osOodWeights c tch prevCols ol lvs acc k).1 →
          OodLoads c tch prevCols ol lvs p o)
  | _, _, [], acc, k, _, _, hacc => ⟨.nil, hacc, by simp [osOodWeights, loadsOf]⟩
  | prevCols, ol, lv :: rest, acc, k, htch, hk, hacc => by
    obtain ⟨w1, w2, w3⟩ := osOodWeight_ssa c tch prevCols ol lv k htch hk
    set W0 := osOodWeight c tch prevCols ol lv k with hW0
    have hw0 := w1.le
    obtain ⟨a1, a2, a3⟩ := osAcc_ssa acc W0.2.1 W0.2.2 w2 (fun x hx ↦ lt_of_lt_of_le (hacc x hx) hw0)
    set A0 := osAcc acc W0.2.1 W0.2.2 with hA0
    have ha0 := a1.le
    obtain ⟨r1, r2, r3⟩ := osOodWeights_ssa c tch lv.logCols (ol + 1) rest A0.2.1 A0.2.2 (by omega)
      (by omega) a2
    refine ⟨?_, ?_, fun p o hm ↦ ?_⟩
    · have h := (w1.append a1).append r1
      simp only [osOodWeights, ← hW0, ← hA0]
      simpa only [List.append_assoc] using h
    · simp only [osOodWeights, ← hW0, ← hA0]
      exact r2
    · simp only [osOodWeights, ← hW0, ← hA0, loadsOf_append, List.mem_append, a3,
        List.not_mem_nil, or_false] at hm
      simp only [OodLoads]
      rcases hm with hm | hm
      · exact Or.inl (w3 p o hm)
      · exact Or.inr (r3 p o hm)

end
end LeanVM.Guest.B1.Whir
