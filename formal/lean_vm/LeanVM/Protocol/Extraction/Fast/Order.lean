module

public import LeanVM.Protocol.Extraction.Extractor
public import LeanVM.Protocol.Extraction.Lane
public import LeanVM.Semantics.Lemmas

/-!
# The lane lists' order

`laneListAt` sorts each lane's list by `coeffsLE` (lexicographic on the coefficients' lanes,
`LeanVM/Protocol/Extraction/Extractor.lean`), so the list depends only on the set the decoder returns:

* `lexLE` is total, transitive and antisymmetric; `coeffsLE` too (`K.lane` is injective);
* **`mergeSort_dedup_eq`**: two lists with the same elements give the same sorted list without
  duplicates.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Extraction

public section

theorem lexLE_total : ∀ a b : List ℕ, (lexLE a b || lexLE b a) = true
  | [], _ => by simp [lexLE]
  | _ :: _, [] => by simp [lexLE]
  | x :: as, y :: bs => by
    have ih := lexLE_total as bs
    simp only [lexLE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
    rcases Nat.lt_trichotomy x y with h | rfl | h
    · exact .inl (.inl h)
    · rcases ih with ih | ih
      · exact .inl (.inr ⟨rfl, ih⟩)
      · exact .inr (.inr ⟨rfl, ih⟩)
    · exact .inr (.inl h)

theorem lexLE_trans : ∀ a b c : List ℕ, lexLE a b = true → lexLE b c = true → lexLE a c = true
  | [], _, _, _, _ => by simp [lexLE]
  | _ :: _, [], _, h, _ => by simp [lexLE] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLE] at h
  | x :: as, y :: bs, z :: cs, h₁, h₂ => by
    simp only [lexLE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
    rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
    · exact .inl (by omega)
    · exact .inl h₁
    · exact .inl h₂
    · exact .inr ⟨rfl, lexLE_trans as bs cs h₁ h₂⟩

theorem lexLE_antisymm : ∀ a b : List ℕ, lexLE a b = true → lexLE b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [lexLE] at h
  | _ :: _, [], h, _ => by simp [lexLE] at h
  | x :: as, y :: bs, h₁, h₂ => by
    simp only [lexLE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
    rcases h₁ with h₁ | ⟨rfl, h₁⟩
    · omega
    · rcases h₂ with h₂ | ⟨_, h₂⟩
      · omega
      · rw [lexLE_antisymm as bs h₁ h₂]

theorem coeffsLE_antisymm {a b : Array K} (h₁ : coeffsLE a b = true) (h₂ : coeffsLE b a = true) :
    a = b := by
  have h := lexLE_antisymm _ _ h₁ h₂
  have hinj : Function.Injective fun x : K ↦ x.lane.toNat := fun x y hxy ↦
    LeanVM.Semantics.K.lane_injective (UInt64.toNat_inj.1 hxy)
  exact Array.toList_inj.1 (List.map_injective_iff.2 hinj h)

/-- **Same elements, same sorted list.** -/
theorem mergeSort_dedup_eq {l l' : List (Array K)} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    l.dedup.mergeSort coeffsLE = l'.dedup.mergeSort coeffsLE := by
  have htrans : ∀ a b c : Array K, coeffsLE a b = true → coeffsLE b c = true →
      coeffsLE a c = true := fun _ _ _ ↦ lexLE_trans _ _ _
  have htotal : ∀ a b : Array K, (coeffsLE a b || coeffsLE b a) = true := fun _ _ ↦
    lexLE_total _ _
  have hperm : List.Perm (l.dedup.mergeSort coeffsLE) (l'.dedup.mergeSort coeffsLE) :=
    (List.mergeSort_perm _ _).trans <|
      ((List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).2 fun x ↦ by
        simp [List.mem_dedup, h x]).trans (List.mergeSort_perm _ _).symm
  exact hperm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ ↦ coeffsLE_antisymm h₁ h₂)
    (List.pairwise_mergeSort htrans htotal _) (List.pairwise_mergeSort htrans htotal _)

end

end LeanVM.Extraction.Fast
