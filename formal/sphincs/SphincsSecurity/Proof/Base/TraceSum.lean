import Mathlib.Algebra.FreeMonoid.Basic

namespace SphincsSecurity.TraceSum

variable {Entry : Type} (charge : FreeMonoid Entry → Entry → Nat)

def run (history : FreeMonoid Entry) : List Entry → Nat
  | [] => 0
  | entry :: tail => charge history entry + run (history * FreeMonoid.of entry) tail

theorem run_nil (history : FreeMonoid Entry) : run charge history [] = 0 := rfl

theorem run_cons (history : FreeMonoid Entry) (entry : Entry) (tail : List Entry) :
    run charge history (entry :: tail) = charge history entry + run charge (history * FreeMonoid.of entry) tail := rfl

theorem run_append (history : FreeMonoid Entry) (first second : List Entry) :
    run charge history (first ++ second) = run charge history first + run charge (history * FreeMonoid.ofList first) second := by
  induction first generalizing history with
  | nil => simp only [List.nil_append, run_nil, FreeMonoid.ofList_nil, mul_one, Nat.zero_add]
  | cons entry tail ih =>
      simp only [List.cons_append, run_cons, ih, FreeMonoid.ofList_cons, mul_assoc, Nat.add_assoc]

theorem run_le_length_mul (history : FreeMonoid Entry) (entries : List Entry) (bound : Nat)
    (hbound : ∀ before entry after, entries = before ++ entry :: after → charge (history * FreeMonoid.ofList before) entry ≤ bound) :
    run charge history entries ≤ entries.length * bound := by
  induction entries generalizing history with
  | nil => simp only [run_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons entry tail ih =>
      have hhead := hbound [] entry tail rfl
      simp only [FreeMonoid.ofList_nil, mul_one] at hhead
      have htail := ih (history * FreeMonoid.of entry) (by
        intro before next after he
        have h := hbound (entry :: before) next after (by simp only [List.cons_append, he])
        simpa only [FreeMonoid.ofList_cons, mul_assoc] using h)
      simpa only [run_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using Nat.add_le_add hhead htail

theorem run_pos_iff (history : FreeMonoid Entry) (entries : List Entry) :
    0 < run charge history entries ↔
      ∃ before entry after, entries = before ++ entry :: after ∧ 0 < charge (history * FreeMonoid.ofList before) entry := by
  induction entries generalizing history with
  | nil => simp [run_nil]
  | cons entry tail ih =>
      rw [run_cons, Nat.add_pos_iff_pos_or_pos, ih]
      constructor
      · rintro (h | ⟨before, next, after, he, hp⟩)
        · exact ⟨[], entry, tail, rfl, by simpa only [FreeMonoid.ofList_nil, mul_one] using h⟩
        · refine ⟨entry :: before, next, after, by simp only [List.cons_append, he], ?_⟩
          simpa only [FreeMonoid.ofList_cons, mul_assoc] using hp
      · rintro ⟨before, next, after, he, hp⟩
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact Or.inl (by simpa only [FreeMonoid.ofList_nil, mul_one] using hp)
        | cons head before =>
            simp only [List.cons_append, List.cons.injEq] at he
            obtain ⟨rfl, he⟩ := he
            exact Or.inr ⟨before, next, after, he, by simpa only [FreeMonoid.ofList_cons, mul_assoc] using hp⟩

end SphincsSecurity.TraceSum
