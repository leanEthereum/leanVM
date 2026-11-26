/-
  LeanVM.Guest.Bridge.JumpCellsPack

  What the alignment context's tables hold: an entry of a table built from a list is one of the list's, and the packed cells decode to the certificate's.
-/

module

public import LeanVM.Guest.Bridge.AlignDefs

/-!
# The alignment context's tables

`getF_trieOf`: an entry found in `trieOf l` is one of `l`'s. `getF_buildT`: `buildT d L` finds entry `n` of `L` below `2^d - 1`. `packGo_digits`: the cells packed `2^20`-ary, 64 to a chunk (`packGo`), are read back digit by digit. `locAt_ofData`: so the context's cell map is the certificate's cells, but for the hint-only cells, at every value below `2^30`.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest.Exec (Trie natSeq natSeq_eq)
open LeanVM.Guest.Check (getF setF getF_eq setF_eq)

public section

/-! ## Tables from lists -/

theorem getF_trieGo {α : Type} : ∀ (l : List (ℕ × α)) (t : Trie α) {k : ℕ} {v : α},
    getF (trieGo l t) k = some v → (k, v) ∈ l ∨ getF t k = some v
  | [], _, _, _, h => Or.inr h
  | p :: l, t, k, v, h => by
    simp only [trieGo, Trie.seq_eq] at h
    rcases getF_trieGo l _ h with h1 | h1
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · rw [getF_eq, setF_eq] at h1
      rcases Exec.Trie.get_set h1 with ⟨rfl, rfl⟩ | h2
      · exact Or.inl List.mem_cons_self
      · exact Or.inr (by rw [getF_eq]; exact h2)

/-- **An entry of a table built from a list is one of the list's.** -/
theorem getF_trieOf {α : Type} {l : List (ℕ × α)} {k : ℕ} {v : α} (h : getF (trieOf l) k = some v) :
    (k, v) ∈ l := by
  rcases getF_trieGo l .nil h with h | h
  · exact h
  · rw [getF_eq] at h
    simp [Trie.get] at h

/-! ## Lists by halves -/

theorem evens_getElem? {α : Type} : ∀ (l : List α) (i : ℕ), (evens l)[i]? = l[2 * i]?
  | [], _ => by simp [evens]
  | [_], 0 => rfl
  | [_], _ + 1 => by simp [evens]
  | _ :: _ :: _, 0 => rfl
  | a :: b :: l, i + 1 => by
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    simp only [evens, List.getElem?_cons_succ]
    exact evens_getElem? l i

theorem getF_node_succ {α : Type} (v : Option α) (l r : Trie α) (m : ℕ) :
    getF (.node v l r) (m + 1) = if m % 2 = 0 then getF l (m / 2) else getF r (m / 2) := by
  show @Bool.rec (fun _ ↦ Option α) (getF r (Nat.div m 2)) (getF l (Nat.div m 2)) (Nat.beq (Nat.mod m 2) 0) = _
  cases hb : Nat.beq (Nat.mod m 2) 0
  · have h : ¬ m % 2 = 0 := Nat.ne_of_beq_eq_false hb
    rw [ite_eq_right h]; rfl
  · have h : m % 2 = 0 := Nat.eq_of_beq_eq_true hb
    rw [ite_eq_left h]; rfl

/-- **A list as a trie by halves finds its entries**, those below `2^d - 1`. -/
theorem getF_buildT {α : Type} : ∀ (d : ℕ) (L : List α) (n : ℕ), n + 1 < 2 ^ d → getF (buildT d L) n = L[n]?
  | 0, _, _, h => by simp at h
  | _ + 1, [], _, _ => by simp [buildT, getF_eq, Trie.get]
  | d + 1, a :: l, n, h => by
    simp only [buildT, Trie.seq_eq]
    cases n with
    | zero => rfl
    | succ m =>
      rw [getF_node_succ, List.getElem?_cons_succ]
      rw [pow_succ] at h
      split_ifs with hm
      · rw [getF_buildT d _ _ (by omega), evens_getElem?]
        congr 1
        omega
      · rw [getF_buildT d _ _ (by omega), evens_getElem?, List.getElem?_tail]
        congr 1
        omega

/-! ## Packed cells -/

theorem digit_eq (ch t : ℕ) : digit ch t = ch / 2 ^ (20 * t) % 2 ^ 20 := by
  unfold digit cellBits
  show (ch >>> (20 * t)) % 2 ^ 20 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem digit_high {acc j t : ℕ} (h : acc < 2 ^ (20 * j)) (ht : j ≤ t) : digit acc t = 0 := by
  rw [digit_eq, Nat.div_eq_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  rfl

theorem digit_low (acc c : ℕ) {j t : ℕ} (ht : t < j) : digit (acc + c * 2 ^ (20 * j)) t = digit acc t := by
  rw [digit_eq, digit_eq]
  have hp : 2 ^ (20 * j) = 2 ^ 20 * 2 ^ (20 * (j - t - 1)) * 2 ^ (20 * t) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hp, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (by positivity), Nat.mul_left_comm,
    Nat.add_mul_mod_self_left]

theorem digit_at {acc c j : ℕ} (h : acc < 2 ^ (20 * j)) (hc : c < 2 ^ 20) :
    digit (acc + c * 2 ^ (20 * j)) j = c := by
  rw [digit_eq, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt h, Nat.zero_add,
    Nat.mod_eq_of_lt hc]

theorem pack_lt {acc c j : ℕ} (h : acc < 2 ^ (20 * j)) (hc : c < 2 ^ 20) :
    acc + c * 2 ^ (20 * j) < 2 ^ (20 * (j + 1)) := by
  have hp : 2 ^ (20 * (j + 1)) = 1048576 * 2 ^ (20 * j) := by
    rw [show 20 * (j + 1) = 20 + 20 * j by omega, pow_add]; rfl
  have h1 : c * 2 ^ (20 * j) ≤ 1048575 * 2 ^ (20 * j) :=
    Nat.mul_le_mul_right _ (by norm_num at hc; omega)
  omega

/-- Cell `i` of the packed chunks `R`. -/
def chunkD (R : List ℕ) (i : ℕ) : ℕ :=
  match R[i / 64]? with
  | some ch => digit ch (i % 64)
  | none => 0

/-- **The packed cells read back**: from `j` cells in the chunk `acc`, the chunks `packGo` makes
read the digits of `acc`, then `cs`. -/
theorem packGo_digits : ∀ (cs : List ℕ) (j acc : ℕ), j < 64 → acc < 2 ^ (20 * j) → (∀ c ∈ cs, c < 2 ^ 20) →
    ∀ i, chunkD (packGo cs j acc) i = ((List.range j).map (digit acc) ++ cs).getD i 0
  | [], j, acc, hj, hacc, _, i => by
    simp only [packGo, chunkD, List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases Nat.lt_or_ge i 64 with hi | hi
    · rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, List.getElem?_cons_zero]
      by_cases hij : i < j
      · rw [List.getElem?_range hij]; rfl
      · rw [List.getElem?_eq_none (by simp; omega)]
        exact digit_high hacc (by omega)
    · rw [List.getElem?_eq_none (l := [acc]) (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      rfl
  | c :: cs, j, acc, hj, hacc, hcs, i => by
    have hc : c < 2 ^ 20 := hcs c List.mem_cons_self
    have hcs' : ∀ c ∈ cs, c < 2 ^ 20 := fun c' h ↦ hcs c' (List.mem_cons_of_mem _ h)
    have ha : Nat.add acc (Nat.shiftLeft c (Nat.mul cellBits j)) = acc + c * 2 ^ (20 * j) := by
      show acc + (c <<< (20 * j)) = _
      rw [Nat.shiftLeft_eq]
    simp only [packGo, natSeq_eq, ha, Bool.cond_eq_ite, Nat.beq_eq]
    have hdig : (List.range j).map (digit (acc + c * 2 ^ (20 * j))) = (List.range j).map (digit acc) :=
      List.map_congr_left fun t ht ↦ digit_low acc c (List.mem_range.mp ht)
    split_ifs with h63
    · subst h63
      rcases Nat.lt_or_ge i 64 with hi | hi
      · simp only [chunkD, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, List.getElem?_cons_zero]
        rw [List.getD_eq_getElem?_getD]
        rcases Nat.lt_or_ge i 63 with hi' | hi'
        · rw [List.getElem?_append_left (by simpa using hi'), List.getElem?_map, List.getElem?_range hi',
            Option.map_some, Option.getD_some, digit_low acc c hi']
        · obtain rfl : i = 63 := by omega
          rw [List.getElem?_append_right (by simp), digit_at hacc hc]
          simp
      · have hrec := packGo_digits cs 0 0 (by norm_num) (by norm_num) hcs' (i - 64)
        simp only [List.range_zero, List.map_nil, List.nil_append] at hrec
        have hd : i / 64 = (i - 64) / 64 + 1 := by omega
        have hm : i % 64 = (i - 64) % 64 := by omega
        simp only [chunkD, hd, hm, List.getElem?_cons_succ] at hrec ⊢
        rw [hrec, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by simp; omega)]
        simp only [List.length_map, List.length_range]
        rw [show i - 63 = i - 64 + 1 by omega, List.getElem?_cons_succ]
    · rw [packGo_digits cs (j + 1) _ (by omega) (pack_lt hacc hc) hcs' i, List.range_succ, List.map_append,
        hdig, List.map_singleton, digit_at hacc hc, List.append_assoc]
      rfl

/-- **The context's cell map is the certificate's**, at a value below `2^30` without a hint-only
cell. -/
theorem locAt_ofData {locs : List ℕ} {extra : List (ℕ × ℕ)} {entry : ℕ} {main : Bool} {p : B2C.Plumb}
    {pows : Exec.PowTree} {jt : Trie ℕ} {ents : List (String × ℕ)} {halt len : ℕ}
    (hlocs : locs.all (fun c ↦ Nat.blt c (2 ^ cellBits)) = true) {i : ℕ} (hx : extra.lookup i = none)
    (hi : i < 2 ^ 30) :
    (AlignCtx.ofData locs extra entry main p pows jt ents halt len).locAt i = locs.getD i 0 := by
  have hall : ∀ c ∈ locs, c < 2 ^ 20 := fun c hc ↦ by
    have := List.all_eq_true.mp hlocs c hc
    simpa [cellBits] using this
  have hd := packGo_digits locs 0 0 (by norm_num) (by norm_num) hall i
  simp only [List.range_zero, List.map_nil, List.nil_append] at hd
  simp only [AlignCtx.locAt, AlignCtx.ofData, hx, Option.getD_none]
  rw [show Nat.div i 64 = i / 64 from rfl, getF_buildT 32 _ _ (by omega)]
  exact hd

end

end LeanVM.Guest.Bridge
