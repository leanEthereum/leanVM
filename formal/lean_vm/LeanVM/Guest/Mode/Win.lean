module

public import LeanVM.Guest.Mode.Abs

/-!
# Code read past whole chunks

`drop_flatten_chunked`: dropping whole chunks of a chunked code drops their instructions.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

end

public section

theorem drop_flatten_chunked {C : ℕ} (hC : 0 < C) : ∀ {cs : List (List OffsetInstruction)} {n : ℕ},
    chunked C cs n = true → ∀ a, cs.flatten.drop a = (cs.drop (a / C)).flatten.drop (a % C)
  | [], _, _, a => by simp
  | c :: cs, n, h, a => by
    by_cases ha : a < C
    · rw [Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha, List.drop_zero]
    · have hq : a / C = (a - C) / C + 1 := Nat.div_eq_sub_div hC (by omega)
      have hr : a % C = (a - C) % C := Nat.mod_eq_sub_mod (by omega)
      unfold chunked at h
      split_ifs at h with hn
      · simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
        obtain ⟨rfl, hl⟩ := h
        rw [hq, List.drop_succ_cons, List.drop_nil, List.flatten_nil, List.drop_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.drop_eq_nil_of_le (by omega)]
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hl, h'⟩ := h
        rw [hq, hr, List.drop_succ_cons, List.flatten_cons, List.drop_append,
          List.drop_eq_nil_of_le (by omega), List.nil_append, hl]
        exact drop_flatten_chunked hC h' (a - C)

end

end LeanVM.Guest.Mode
