module

public import LeanVM.Guest.Fast.LogG
public import LeanVM.Guest.Fast.Numbers
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.B1.Sig.CodewordComplete

/-!
# A codeword's chain starts, as numbers

`cwStart W G b σ i` (`B1/Sig/Codeword.lean`), the cell holding chain `i`'s hinted start, is read
off the template generators (`armBase`, `armT`, a `WotsT` of functions). It is arithmetic in the
step's size `W.size`, the group's selector cell and the digit value its dispatch takes:

* `walkBaseN`, `armBaseN`, `selN`, `startN` (`Fast/Numbers.lean`): the walks' and arms' bases, the
  groups' selector cells and a chain's start, in numbers (`walkBase_eq`, `armBase_eq`,
  `cwState_eq`, `cwStart_eq`);
* translated: `startN sz n fold sel k r = sel + startN sz n fold 0 k r` (`startN_shift`), so a
  scheme's starts are its selectors plus three small tables (`WotsTabs`), one for the first group
  (`fold`), one for the others, one for the last chain;
* `cwCell`: the start's cell off the tables and the exponent search `logGT`
  (`cwStart_eq_cwCell`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## Equal to the generators -/

theorem walkBase_eq (stride k : ℕ) :
    ∀ (r j b : ℕ), walkBase stride k r j b = walkBaseN stride k r j b
  | _, 0, _ => rfl
  | r, j + 1, _ => walkBase_eq stride k (r + 1) j _

theorem armBase_eq (W : WotsT) (slots : ℕ → ℕ → ℕ) (first n : ℕ) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ (k j b : ℕ),
    armBase W slots first n fold prodIn encIn prodOut encOut k j b = armBaseN W.size n fold k j b
  | _, 0, _ => rfl
  | k, j + 1, b => by
      rw [armBase, armT_snd, walkBase_eq, walkBase_eq, armBaseN,
        armBase_eq W slots first n fold prodIn encIn prodOut encOut]
      congr 1
      unfold armNextN
      by_cases hk : k = 0 <;> simp [hk]

theorem cwState_eq (W : WotsT) (b : ℕ) : ∀ p, (cwState W b p).2.2 = selN W.size b p
  | 0 => rfl
  | p + 1 => by
      rw [cwState_succ, groupT_snd_eq, armB, armBase_eq, cwState_eq W b p]
      rfl

theorem cwStart_eq (W : WotsT) (G b : ℕ) (σ : Val) (i : ℕ) :
    cwStart W G b σ i = .n (startN W.size (cwN G (i / 3)) (i / 3 == 0)
      (cwState W b (i / 3)).2.2 (cwK W G b σ (i / 3)) (i % 3)) := by
  unfold cwStart armStart walkStartV startN
  rw [armBase_eq, walkBase_eq]
  split <;> rfl

/-! ## Translated -/

theorem walkBaseN_shift (stride k : ℕ) : ∀ (r j b : ℕ),
    walkBaseN stride k r j b = b + walkBaseN stride k r j 0
  | _, 0, _ => by simp [walkBaseN]
  | r, j + 1, b => by
      rw [walkBaseN, walkBaseN, walkBaseN_shift stride k (r + 1) j,
        walkBaseN_shift stride k (r + 1) j (0 + _)]
      omega

theorem armNextN_shift (sz n : ℕ) (fold : Bool) (k a : ℕ) :
    armNextN sz n fold k a = a + armNextN sz n fold k 0 := by
  unfold armNextN
  cases fold <;> by_cases hk : k = 0 <;>
    simp only [hk, ↓reduceIte, Bool.false_eq_true, Nat.zero_add]
  · rw [walkBaseN_shift _ _ _ _ a]; omega
  · rw [walkBaseN_shift _ _ _ _ a]; omega
  · rw [walkBaseN_shift _ _ _ _ (a + 1), walkBaseN_shift _ _ _ _ 1]; omega
  · rw [walkBaseN_shift _ _ _ _ (a + 1), walkBaseN_shift _ _ _ _ 1]; omega

theorem armBaseN_shift (sz n : ℕ) (fold : Bool) : ∀ (k j b : ℕ),
    armBaseN sz n fold k j b = b + armBaseN sz n fold k j 0
  | _, 0, _ => by simp [armBaseN]
  | k, j + 1, b => by
      rw [armBaseN, armBaseN, armBaseN_shift sz n fold (k + 1) j,
        armBaseN_shift sz n fold (k + 1) j (armNextN sz n fold k 0), armNextN_shift sz n fold k b]
      omega

theorem startN_shift (sz n : ℕ) (fold : Bool) (sel k r : ℕ) :
    startN sz n fold sel k r = sel + startN sz n fold 0 k r := by
  unfold startN slotsN
  rw [armBaseN_shift sz n fold 0 k (sel + 6), armBaseN_shift sz n fold 0 k (0 + 6)]
  split
  · omega
  · rw [walkBaseN_shift _ _ _ _ (if fold then _ else _),
      walkBaseN_shift _ _ _ _ (if fold then 0 + 6 + _ + 1 else 0 + 6 + _)]
    cases fold <;> simp <;> omega

/-! ## Off tables -/

theorem offAt_offTab {sz n : ℕ} {fold : Bool} {r k : ℕ} (hr : r < n) (hk : k < 4 ^ n) :
    offAt (offTab sz n fold) r k = startN sz n fold 0 k r := by
  simp [offAt, offTab, List.getD_eq_getElem?_getD, hr, hk]

/-- **Chain `i`'s start cell**, off the selector cells `sel` of the `G + 1` groups and the
tables. -/
def cwCell (G : ℕ) (sel : List ℕ) (first rest last : List (List ℕ)) (σ : Val) (i : ℕ) : ℕ :=
  let s := sel.getD (i / 3) 0
  if i / 3 < G then
    s + offAt (if i / 3 = 0 then first else rest) (i % 3) (logGT (σ (.n s)) 64)
  else s + offAt last (i % 3) (logGT (σ (.n s)) 4)

theorem cwStart_eq_cwCell {W : WotsT} {G b : ℕ} {sel : List ℕ} {first rest last : List (List ℕ)}
    (hsel : sel = (List.range (G + 1)).map (selN W.size b)) (ht : WotsTabs W.size first rest last)
    (hG0 : 0 < G) (σ : Val) {i : ℕ} (hi : i < 3 * G + 1) :
    cwStart W G b σ i = .n (cwCell G sel first rest last σ i) := by
  have hp : i / 3 < G + 1 := by omega
  have hs : sel.getD (i / 3) 0 = (cwState W b (i / 3)).2.2 := by
    rw [hsel, cwState_eq]; simp [List.getD_eq_getElem?_getD, hp]
  rw [cwStart_eq]
  unfold cwCell cwK
  simp only [hs]
  rw [startN_shift]
  generalize (cwState W b (i / 3)).2.2 = S
  by_cases hG : i / 3 < G
  · have hn : cwN G (i / 3) = 3 := by simp [cwN, hG]
    simp only [hG, ↓reduceIte, hn]
    have hk := logG_lt (σ (.n S)) (bound := 4 ^ 3) (by norm_num)
    rw [logG_eq_logGT _ (by norm_num), show (4 : ℕ) ^ 3 = 64 by norm_num] at *
    by_cases h0 : i / 3 = 0
    · simp only [h0, ↓reduceIte, beq_self_eq_true, ht.first]
      rw [offAt_offTab (by omega) (by norm_num; exact hk)]
    · simp only [h0, ↓reduceIte, ht.rest, show (i / 3 == 0) = false by simpa using h0]
      rw [offAt_offTab (by omega) (by norm_num; exact hk)]
  · have hn : cwN G (i / 3) = 1 := by simp [cwN, hG]
    have hiG : i / 3 = G := by omega
    have hr : i % 3 = 0 := by omega
    simp only [hG, ↓reduceIte, hn]
    have hk := logG_lt (σ (.n S)) (bound := 4 ^ 1) (by norm_num)
    rw [logG_eq_logGT _ (by norm_num), show (4 : ℕ) ^ 1 = 4 by norm_num] at *
    have hf : (i / 3 == 0) = false := by
      have : i / 3 ≠ 0 := by
        intro h; rw [h] at hiG; subst hiG; omega
      simpa using this
    rw [hf, ht.last, hr, offAt_offTab (r := 0) (n := 1) (by omega) (by norm_num; exact hk)]

/-- **Chain `i`'s start cell, off arrays** (`cwCell`): the selectors `sel`, the tables `first`,
`rest`, `last` (`tabA`) and the lanes of `g^k` (`gLanes`), built once by the caller. -/
def cwCellA (lanes : List ℕ) (G : ℕ) (sel : Array ℕ) (first rest last : Array (Array ℕ))
    (σ : Val) (i : ℕ) : ℕ :=
  let s := sel.getD (i / 3) 0
  if i / 3 < G then
    s + offAtA (if i / 3 = 0 then first else rest) (i % 3) (logGTWith lanes (σ (.n s)) 64)
  else s + offAtA last (i % 3) (logGTWith lanes (σ (.n s)) 4)

theorem cwCellA_eq (G : ℕ) (sel : List ℕ) (first rest last : List (List ℕ)) (σ : Val) (i : ℕ) :
    cwCellA gLanes G sel.toArray (tabA first) (tabA rest) (tabA last) σ i =
      cwCell G sel first rest last σ i := by
  unfold cwCellA cwCell
  simp only [getD_toArray, logGTWith_gLanes]
  split_ifs <;> simp only [offAtA_tabA]

end
end LeanVM.Guest.Fast
