/-
  LeanVM.Guest.B2C.ShareSound

  Soundness of the sharing check: on every path of a function whose check passes, the values the
  path names at one frame cell hold one word, a fixed cell's constant if it has one.
-/

module

public import LeanVM.Guest.B2C.Share
public import LeanVM.Guest.CheckSound

/-!
# Soundness of the sharing check

Along a path, the state of `swL` is read against a word per cell `Ψ` (`Inv`): every value named
so far and not pending holds its cell's word, the known constants are the cells' words, the keys
hold of them, and the pending values' facts hold. Naming a value at a cell nothing occupies sets
that cell's word (`Ψ` changes only there), so a join keeps the facts of before the branch for the
`Ψ` of the branch taken. At a return nothing is pending: every value the path names holds its
cell's word (`sw_sound`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-! ## Tries -/

namespace Trie

variable {α : Type}

theorem get_set_self (a : α) : ∀ {d n : ℕ} (t : Exec.Trie α), n + 1 < 2 ^ d →
    (t.set a d n).get n = some a
  | 0, n, _, h => by simp at h
  | d + 1, n, t, h => by
    have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
    rw [Exec.Trie.set_succ]
    by_cases h0 : n = 0
    · simp [h0, Exec.Trie.get_node]
    · by_cases h1 : n % 2 = 1
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        exact get_set_self a _ (by omega)
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        exact get_set_self a _ (by omega)

theorem get_set_ne (a : α) : ∀ {d n m : ℕ} (t : Exec.Trie α), m ≠ n →
    (t.set a d n).get m = t.get m
  | 0, _, _, _, _ => rfl
  | d + 1, n, m, t, hmn => by
    rw [Exec.Trie.set_succ, Exec.Trie.get_eq_node t m]
    by_cases h0 : n = 0
    · subst h0
      simp [Exec.Trie.get_node, hmn]
    · by_cases h1 : n % 2 = 1
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        by_cases hm : m = 0
        · simp [hm]
        · by_cases hm1 : m % 2 = 1
          · simp only [hm, hm1, ↓reduceIte]
            exact get_set_ne a _ (by omega)
          · simp [hm, hm1]
      · simp only [h0, h1, ↓reduceIte, Exec.Trie.get_node]
        by_cases hm : m = 0
        · simp [hm]
        · by_cases hm1 : m % 2 = 1
          · simp [hm, hm1]
          · simp only [hm, hm1, ↓reduceIte]
            exact get_set_ne a _ (by omega)

variable {f : Option α → Option α → Option α}

theorem get_mergeR (hf : f none none = none) : ∀ (b : Exec.Trie α) (n : ℕ),
    (mergeR f b).get n = f none (b.get n)
  | .nil, n => by simp [mergeR, hf]
  | .node v l r, n => by
    rw [mergeR, Exec.Trie.get_node, Exec.Trie.get_node]
    split_ifs
    · rfl
    · exact get_mergeR hf l _
    · exact get_mergeR hf r _

theorem get_merge (hf : f none none = none) : ∀ (a b : Exec.Trie α) (n : ℕ),
    (merge f a b).get n = f (a.get n) (b.get n)
  | .nil, b, n => by rw [merge, get_mergeR hf]; rfl
  | .node v l r, .nil, n => by
    rw [merge, Exec.Trie.get_node, Exec.Trie.get_node, Exec.Trie.get_nil]
    split_ifs
    · rfl
    · rw [get_merge hf l .nil]; rfl
    · rw [get_merge hf r .nil]; rfl
  | .node v l r, .node v' l' r', n => by
    rw [merge, Exec.Trie.get_node, Exec.Trie.get_node, Exec.Trie.get_node]
    split_ifs
    · rfl
    · exact get_merge hf l l' _
    · exact get_merge hf r r' _

end Trie

theorem getF_setF_self {α : Type} (a : α) {d n : ℕ} (t : Exec.Trie α) (h : n + 1 < 2 ^ d) :
    getF (setF a d t n) n = some a := by
  rw [getF_eq, setF_eq]; exact Trie.get_set_self a t h

theorem getF_setF_ne {α : Type} (a : α) {d n m : ℕ} (t : Exec.Trie α) (h : m ≠ n) :
    getF (setF a d t n) m = getF t m := by
  rw [getF_eq, getF_eq, setF_eq]; exact Trie.get_set_ne a t h

theorem getF_setF {α : Type} {a b : α} {d n m : ℕ} {t : Exec.Trie α}
    (h : getF (setF a d t n) m = some b) : (m = n ∧ b = a) ∨ getF t m = some b := by
  rw [getF_eq, setF_eq] at h; rw [getF_eq]; exact Exec.Trie.get_set h

/-! ## Keys -/

/-- **What a key says** of an output word and its inputs' words: a sum, a product, one of the two
words of a compression, a load at offset `op - 4`. -/
def KeyHolds (rd : Reader) (out : E) : ℕ → List E → Prop
  | 0, [a, b] => out = a + b
  | 1, [a, b] => out = a * b
  | 2, [m0, m1, m2, m3, c0, c1, md] => ∃ o1, CompressCells ![m0, m1, m2, m3] c0 c1 out o1 md
  | 3, [m0, m1, m2, m3, c0, c1, md] => ∃ o0, CompressCells ![m0, m1, m2, m3] c0 c1 o0 out md
  | n + 4, [p] => LoadHolds rd p n out
  | _, _ => False

theorem cellWords_inj {x y : E} (hx : IsCanonical128 x) (hy : IsCanonical128 y)
    (h : cellWords x = cellWords y) : x = y := by
  rw [← wordsCell_cellWords hx, ← wordsCell_cellWords hy, h]

theorem append4_inj {a b c d : Vector UInt32 4} (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  have h' := congrArg Vector.toList h
  simp only [Vector.toList_append] at h'
  have := List.append_inj h' (by simp)
  exact ⟨Vector.toList_inj.mp this.1, Vector.toList_inj.mp this.2⟩

/-- **A key's output is a function of its inputs.** -/
theorem KeyHolds.unique {rd : Reader} {x y : E} : ∀ {op : ℕ} {ins : List E},
    KeyHolds rd x op ins → KeyHolds rd y op ins → x = y
  | 0, [_, _], hx, hy => hx.trans hy.symm
  | 1, [_, _], hx, hy => hx.trans hy.symm
  | 2, [_, _, _, _, _, _, _], ⟨_, hx⟩, ⟨_, hy⟩ =>
    cellWords_inj hx.2.2.2.1 hy.2.2.2.1 (append4_inj (hx.2.2.2.2.2.2.trans hy.2.2.2.2.2.2.symm)).1
  | 3, [_, _, _, _, _, _, _], ⟨_, hx⟩, ⟨_, hy⟩ =>
    cellWords_inj hx.2.2.2.2.1 hy.2.2.2.2.1 (append4_inj (hx.2.2.2.2.2.2.trans hy.2.2.2.2.2.2.symm)).2
  | _ + 4, [_], hx, hy => Option.some.inj (hx.2.symm.trans hy.2)

/-- A sum's and a product's inputs in either order. -/
theorem keyHolds_keyCells {rd : Reader} {x : E} {Ψ : ℕ → E} (op : ℕ) (cs : List ℕ) :
    KeyHolds rd x op ((keyCells op cs).map Ψ) ↔ KeyHolds rd x op (cs.map Ψ) := by
  match op, cs with
  | 0, [a, b] =>
    simp only [keyCells]
    cases Nat.ble a b <;> simp [KeyHolds, add_comm]
  | 1, [a, b] =>
    simp only [keyCells]
    cases Nat.ble a b <;> simp [KeyHolds, mul_comm]
  | 0, [] => simp [keyCells]
  | 0, [_] => simp [keyCells]
  | 0, _ :: _ :: _ :: _ => simp [keyCells]
  | 1, [] => simp [keyCells]
  | 1, [_] => simp [keyCells]
  | 1, _ :: _ :: _ :: _ => simp [keyCells]
  | n + 2, cs => simp [keyCells]

/-! ## The invariant -/

/-- The word of a constant's limbs. -/
def tw (x : ℕ × ℕ × ℕ) : E := OInstr.imm x.1 x.2.1 x.2.2

section Inv

variable (loc : Exec.Trie ℕ) (rd : Reader) (σ : Val)

/-- **What the state says** of a path whose values named so far are `pre`, for the cells' words
`Ψ`. -/
structure Inv (st : SSt) (pre : List V) (Ψ : ℕ → E) : Prop where
  vn : ∀ v ∈ pre, v = V.n v.idx
  occ : ∀ v ∈ pre, 2 ≤ cellOf loc v → (getF st.occ (cellOf loc v)).isSome
  good : ∀ v ∈ pre, 2 ≤ cellOf loc v → isPend st v.idx = false → σ v = Ψ (cellOf loc v)
  named : ∀ n, isNamed st n = true → 2 ≤ cellN loc n →
    σ (V.n n) = Ψ (cellN loc n) ∧ (getF st.occ (cellN loc n)).isSome
  kc : ∀ c x, getF st.occ c = some (some x) → Ψ c = tw x
  keys : ∀ c, ∀ k ∈ (getF st.keys c).getD [], KeyHolds rd (Ψ c) k.1 (k.2.map Ψ) ∧
    (getF st.occ c).isSome ∧ ∀ c' ∈ k.2, (getF st.occ c').isSome
  pend : ∀ p ∈ st.pend, cellN loc p.v = p.c ∧ 2 ≤ p.c ∧ (getF st.occ p.c).isSome ∧
    (∀ x, p.kc = some x → σ (V.n p.v) = tw x) ∧
    (∀ k ∈ p.keys, KeyHolds rd (σ (V.n p.v)) k.1 (k.2.map fun u ↦ σ (V.n u))) ∧
    (∀ x ∈ p.eqs, σ (V.n p.v) = σ (V.n x))

/-- From `st` to `st'`: every occupied cell stays occupied with its word. -/
def Step (st : SSt) (Ψ : ℕ → E) (st' : SSt) (Ψ' : ℕ → E) : Prop :=
  ∀ c, (getF st.occ c).isSome → (getF st'.occ c).isSome ∧ Ψ' c = Ψ c

theorem Step.refl (st : SSt) (Ψ : ℕ → E) : Step st Ψ st Ψ := fun _ h ↦ ⟨h, rfl⟩

theorem Step.trans {st₁ st₂ st₃ : SSt} {Ψ₁ Ψ₂ Ψ₃ : ℕ → E} (h₁ : Step st₁ Ψ₁ st₂ Ψ₂)
    (h₂ : Step st₂ Ψ₂ st₃ Ψ₃) : Step st₁ Ψ₁ st₃ Ψ₃ := fun c hc ↦
  ⟨(h₂ c (h₁ c hc).1).1, (h₂ c (h₁ c hc).1).2.trans (h₁ c hc).2⟩

/-- A step with the occupancy and the words unchanged. -/
theorem Step.of_occ {st st' : SSt} {Ψ : ℕ → E} (h : ∀ c, (getF st.occ c).isSome → (getF st'.occ c).isSome) :
    Step st Ψ st' Ψ := fun c hc ↦ ⟨h c hc, rfl⟩

variable {loc rd σ}

theorem isPend_iff {st : SSt} {v : ℕ} : isPend st v = true ↔ ∃ p ∈ st.pend, p.v = v := by
  simp only [isPend, List.any_eq_true]
  exact exists_congr fun p ↦ and_congr_right fun _ ↦ ⟨Nat.eq_of_beq_eq_true, fun h ↦ h ▸ Nat.beq_refl _⟩

theorem nameV_skip {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {v : V}
    (h : (isNamed st v.idx || isPend st v.idx) = true) : nameV loc kc st v = st := by
  unfold nameV; rw [h]; rfl

theorem nameV_low {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {v : V}
    (h : (isNamed st v.idx || isPend st v.idx) = false) (h2 : cellOf loc v < 2) :
    nameV loc kc st v = ⟨st.occ, st.keys, setF () indexDepth st.named v.idx, st.pend⟩ := by
  unfold nameV; rw [h]; simp only [Bool.cond_false, natSeq_eq, Nat.blt_eq.mpr h2, Bool.cond_true]

theorem nameV_occ {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {v : V} {y : Option (ℕ × ℕ × ℕ)}
    (h : (isNamed st v.idx || isPend st v.idx) = false) (h2 : 2 ≤ cellOf loc v)
    (ho : getF st.occ (cellOf loc v) = some y) :
    nameV loc kc st v = ⟨st.occ, st.keys, st.named, ⟨v.idx, cellOf loc v, none, [], []⟩ :: st.pend⟩ := by
  have : Nat.blt (cellOf loc v) 2 = false :=
    Bool.eq_false_iff.mpr fun hb ↦ absurd (Nat.blt_eq.mp hb) (by omega)
  unfold nameV; rw [h]; simp only [Bool.cond_false, natSeq_eq, this, ho]

theorem nameV_fresh {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {v : V}
    (h : (isNamed st v.idx || isPend st v.idx) = false) (h2 : 2 ≤ cellOf loc v)
    (ho : getF st.occ (cellOf loc v) = none) :
    nameV loc kc st v = ⟨setF (kc v.idx) envDepth st.occ (cellOf loc v), st.keys,
      setF () indexDepth st.named v.idx, st.pend⟩ := by
  have : Nat.blt (cellOf loc v) 2 = false :=
    Bool.eq_false_iff.mpr fun hb ↦ absurd (Nat.blt_eq.mp hb) (by omega)
  unfold nameV; rw [h]; simp only [Bool.cond_false, natSeq_eq, this, ho]

theorem cellN_of_vn {v : V} (h : v = V.n v.idx) : cellN loc v.idx = cellOf loc v := by
  rw [cellN, ← h]

/-- **Naming a value** keeps the invariant: `Ψ` changes only at a cell nothing occupied. -/
theorem nameV_inv {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {pre : List V} {Ψ : ℕ → E} {v : V}
    (hI : Inv loc rd σ st pre Ψ) (hv : v = V.n v.idx) (hb : cellOf loc v + 1 < 2 ^ envDepth)
    (hkc : ∀ x, kc v.idx = some x → σ v = tw x) :
    ∃ Ψ', Inv loc rd σ (nameV loc kc st v) (pre ++ [v]) Ψ' ∧ Step st Ψ (nameV loc kc st v) Ψ' := by
  have hvn : ∀ u ∈ pre ++ [v], u = V.n u.idx := fun u hu ↦ by
    rcases List.mem_append.mp hu with hu | hu
    · exact hI.vn u hu
    · rw [List.mem_singleton.mp hu]; exact hv
  cases hnp : (isNamed st v.idx || isPend st v.idx)
  · -- a value not named before
    have hnp' := hnp
    simp only [Bool.or_eq_false_iff] at hnp'
    obtain ⟨hn, hp⟩ := hnp'
    by_cases h2 : cellOf loc v < 2
    · rw [nameV_low hnp h2]
      refine ⟨Ψ, ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_, fun n hn' hc ↦ ?_, hI.kc, hI.keys, hI.pend⟩,
        Step.refl _ _⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hI.occ u hu hc
        · rw [List.mem_singleton.mp hu] at hc; omega
      · rcases List.mem_append.mp hu with hu | hu
        · exact hI.good u hu hc hpe
        · rw [List.mem_singleton.mp hu] at hc; omega
      · simp only [isNamed] at hn'
        rcases Option.isSome_iff_exists.mp hn' with ⟨_, h⟩
        rcases getF_setF h with ⟨rfl, -⟩ | h
        · rw [cellN_of_vn hv] at hc; omega
        · exact hI.named n (by simp [isNamed, h]) hc
    · have h2' : 2 ≤ cellOf loc v := by omega
      cases ho : getF st.occ (cellOf loc v) with
      | some y =>
        -- pending
        rw [nameV_occ hnp h2' ho]
        refine ⟨Ψ, ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_, hI.named, hI.kc, hI.keys, ?_⟩,
          Step.refl _ _⟩
        · rcases List.mem_append.mp hu with hu | hu
          · exact hI.occ u hu hc
          · rw [List.mem_singleton.mp hu, ho]; rfl
        · rcases List.mem_append.mp hu with hu | hu
          · refine hI.good u hu hc ?_
            simp only [isPend, List.any_cons, Bool.or_eq_false_iff] at hpe ⊢
            exact hpe.2
          · rw [List.mem_singleton.mp hu] at hpe
            simp [isPend] at hpe
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨cellN_of_vn hv, h2', by rw [ho]; rfl, (fun _ h ↦ by cases h), (fun _ h ↦ by cases h),
              (fun _ h ↦ by cases h)⟩
          · exact hI.pend p hp
      | none =>
        -- the first value at its cell
        rw [nameV_fresh hnp h2' ho]
        refine ⟨Function.update Ψ (cellOf loc v) (σ v), ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_,
          fun n hn' hc ↦ ?_, fun c x hx ↦ ?_, fun c k hk ↦ ?_, fun p hp ↦ ?_⟩, fun c hc ↦ ?_⟩
        · by_cases hcu : cellOf loc u = cellOf loc v
          · rw [hcu, getF_setF_self _ _ hb]; rfl
          · rcases List.mem_append.mp hu with hu | hu
            · rw [getF_setF_ne _ _ hcu]; exact hI.occ u hu hc
            · exact absurd (by rw [List.mem_singleton.mp hu]) hcu
        · rcases List.mem_append.mp hu with hu | hu
          · have hocc := hI.occ u hu hc
            have hne : cellOf loc u ≠ cellOf loc v := fun he ↦ by rw [he, ho] at hocc; cases hocc
            rw [Function.update_of_ne hne]
            exact hI.good u hu hc hpe
          · rw [List.mem_singleton.mp hu, Function.update_self]
        · simp only [isNamed] at hn'
          rcases Option.isSome_iff_exists.mp hn' with ⟨_, h⟩
          rcases getF_setF h with ⟨rfl, -⟩ | h
          · rw [cellN_of_vn hv, ← hv, Function.update_self, getF_setF_self _ _ hb]
            exact ⟨rfl, rfl⟩
          · obtain ⟨h1, h3⟩ := hI.named n (by simp [isNamed, h]) hc
            have hne : cellN loc n ≠ cellOf loc v := fun he ↦ by rw [he, ho] at h3; cases h3
            rw [Function.update_of_ne hne, getF_setF_ne _ _ hne]
            exact ⟨h1, h3⟩
        · by_cases hcv : c = cellOf loc v
          · subst hcv
            rw [getF_setF_self _ _ hb] at hx
            rw [Function.update_self]
            exact hkc x (Option.some.inj hx)
          · rw [getF_setF_ne _ _ hcv] at hx
            rw [Function.update_of_ne hcv]
            exact hI.kc c x hx
        · obtain ⟨h1, h3, h4⟩ := hI.keys c k hk
          have hne : ∀ c', (getF st.occ c').isSome → c' ≠ cellOf loc v := fun c' h he ↦ by
            rw [he, ho] at h; cases h
          rw [Function.update_of_ne (hne c h3), getF_setF_ne _ _ (hne c h3)]
          refine ⟨?_, h3, fun c' hc' ↦ by rw [getF_setF_ne _ _ (hne c' (h4 c' hc'))]; exact h4 c' hc'⟩
          have : k.2.map (Function.update Ψ (cellOf loc v) (σ v)) = k.2.map Ψ :=
            List.map_congr_left fun c' hc' ↦ Function.update_of_ne (hne c' (h4 c' hc')) _ _
          rw [this]; exact h1
        · obtain ⟨h1, h3, h4, h5⟩ := hI.pend p hp
          have hne : p.c ≠ cellOf loc v := fun he ↦ by rw [he, ho] at h4; cases h4
          exact ⟨h1, h3, by rw [getF_setF_ne _ _ hne]; exact h4, h5⟩
        · have hne : c ≠ cellOf loc v := fun he ↦ by rw [he, ho] at hc; cases hc
          exact ⟨by rw [getF_setF_ne _ _ hne]; exact hc, Function.update_of_ne hne _ _⟩
  · -- named or pending already
    rw [nameV_skip hnp]
    refine ⟨Ψ, ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_, hI.named, hI.kc, hI.keys, hI.pend⟩,
      Step.refl _ _⟩
    · rcases List.mem_append.mp hu with hu | hu
      · exact hI.occ u hu hc
      · rw [List.mem_singleton.mp hu] at hc ⊢
        rcases Bool.or_eq_true_iff.mp hnp with hn | hp
        · rw [← cellN_of_vn hv] at hc ⊢; exact (hI.named _ hn hc).2
        · obtain ⟨p, hp, hpv⟩ := isPend_iff.mp hp
          obtain ⟨h1, -, h3, -⟩ := hI.pend p hp
          rw [← cellN_of_vn hv, ← hpv, h1]; exact h3
    · rcases List.mem_append.mp hu with hu | hu
      · exact hI.good u hu hc hpe
      · rw [List.mem_singleton.mp hu] at hc hpe ⊢
        rw [hpe, Bool.or_false] at hnp
        rw [← cellN_of_vn hv] at hc ⊢
        rw [hv]; exact (hI.named _ hnp hc).1

end Inv

section Steps

variable {loc : Exec.Trie ℕ} {rd : Reader} {σ : Val}

theorem nameAll_inv {kc : ℕ → Option (ℕ × ℕ × ℕ)} : ∀ (vs : List V) {st : SSt} {pre : List V}
    {Ψ : ℕ → E}, Inv loc rd σ st pre Ψ →
    (∀ v ∈ vs, v = V.n v.idx ∧ cellOf loc v + 1 < 2 ^ envDepth ∧ ∀ x, kc v.idx = some x → σ v = tw x) →
    ∃ Ψ', Inv loc rd σ (nameAll loc kc st vs) (pre ++ vs) Ψ' ∧ Step st Ψ (nameAll loc kc st vs) Ψ'
  | [], st, pre, Ψ, hI, _ => ⟨Ψ, by simpa [nameAll] using hI, by simpa [nameAll] using Step.refl st Ψ⟩
  | v :: vs, st, pre, Ψ, hI, h => by
    simp only [nameAll, SSt.seq_eq]
    obtain ⟨hv, hb, hk⟩ := h v List.mem_cons_self
    obtain ⟨Ψ1, hI1, hs1⟩ := nameV_inv hI hv hb hk
    obtain ⟨Ψ2, hI2, hs2⟩ := nameAll_inv vs hI1 fun u hu ↦ h u (List.mem_cons_of_mem _ hu)
    exact ⟨Ψ2, by simpa using hI2, hs1.trans hs2⟩

@[simp] theorem nbeq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h ↦ h ▸ Nat.beq_refl a⟩

theorem ofBits_one : K.ofBits 1 = 1 := by decide

theorem tw_limbs (x : E) : tw (limbNat x 0, limbNat x 1, limbNat x 2) = x :=
  (eq_imm_of_limbs rfl rfl rfl).symm

theorem tw_one : tw (1, 0, 0) = 1 := by
  rw [tw, imm_of_ofBits ofBits_one, ofK_one]

/-- The values of an atom are named by their numbers. -/
def VnA (a : Core.Atom) : Prop := ∀ u ∈ Memory.atomUses a, u = V.n u.idx

theorem constOf_sound {a : Core.Atom} {v : ℕ} {x : ℕ × ℕ × ℕ} (ha : a.Holds rd σ) (hvn : VnA a)
    (h : constOf a v = some x) : σ (V.n v) = tw x := by
  cases a with
  | const d c =>
    simp only [constOf, Bool.cond_eq_ite, nbeq_iff] at h
    split_ifs at h with hd
    obtain rfl := Option.some.inj h
    rw [← hd, ← hvn d (by simp [Memory.atomUses]), tw_limbs]
    exact ha
  | assertNe x' i p =>
    simp only [constOf, Bool.cond_eq_ite, nbeq_iff] at h
    split_ifs at h with hd
    obtain rfl := Option.some.inj h
    rw [← hd, ← hvn p (by simp [Memory.atomUses]), tw_one]
    exact ha.2
  | _ => simp [constOf] at h

theorem keysOf_sound {a : Core.Atom} {v : ℕ} {k : ℕ × List ℕ} (ha : a.Holds rd σ) (hvn : VnA a)
    (h : k ∈ keysOf a v) : KeyHolds rd (σ (V.n v)) k.1 (k.2.map fun u ↦ σ (V.n u)) := by
  cases a with
  | add d x y =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hx := hvn x (by simp [Memory.atomUses])
    have hy := hvn y (by simp [Memory.atomUses])
    simp only [keysOf, Bool.cond_eq_ite, nbeq_iff, List.mem_append] at h
    have ha' : σ d = σ x + σ y := ha
    rcases h with (h | h) | h <;> split_ifs at h with he <;> simp only [List.mem_singleton,
      List.not_mem_nil] at h <;> subst h <;> subst he <;> simp only [KeyHolds, List.map_cons, List.map_nil]
    · rw [← hd, ← hx, ← hy]; exact ha'
    · rw [← hd, ← hx, ← hy, ha', add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [← hd, ← hx, ← hy, ha', add_comm (σ x), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  | mul d x y =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hx := hvn x (by simp [Memory.atomUses])
    have hy := hvn y (by simp [Memory.atomUses])
    simp only [keysOf, Bool.cond_eq_ite, nbeq_iff] at h
    split_ifs at h with he <;> simp only [List.mem_singleton, List.not_mem_nil] at h
    subst h; subst he
    simp only [KeyHolds, List.map_cons, List.map_nil]
    rw [← hd, ← hx, ← hy]; exact ha
  | blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    have e : ∀ u ∈ [m0, m1, m2, m3, c0, c1, o0, o1, md], σ (V.n u.idx) = σ u := fun u hu ↦ by
      rw [← hvn u (by simpa [Memory.atomUses] using hu)]
    simp only [keysOf, Bool.cond_eq_ite, nbeq_iff, List.mem_append] at h
    rcases h with h | h <;> split_ifs at h with he <;> simp only [List.mem_singleton,
      List.not_mem_nil] at h <;> subst h <;> subst he <;>
      simp only [KeyHolds, List.map_cons, List.map_nil, e m0 (by simp), e m1 (by simp),
        e m2 (by simp), e m3 (by simp), e c0 (by simp), e c1 (by simp), e md (by simp),
        e o0 (by simp), e o1 (by simp)]
    · exact ⟨_, ha⟩
    · exact ⟨_, ha⟩
  | load d p off =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hp := hvn p (by simp [Memory.atomUses])
    simp only [keysOf, Bool.cond_eq_ite, nbeq_iff] at h
    split_ifs at h with he <;> simp only [List.mem_singleton, List.not_mem_nil] at h
    subst h; subst he
    simp only [KeyHolds, List.map_cons, List.map_nil]
    rw [← hd, ← hp]; exact ha
  | _ => simp [keysOf] at h

theorem eqsOf_sound {a : Core.Atom} {v x : ℕ} (ha : a.Holds rd σ) (hvn : VnA a) (h : x ∈ eqsOf a v) :
    σ (V.n v) = σ (V.n x) := by
  cases a with
  | copy d y =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hy := hvn y (by simp [Memory.atomUses])
    have ha' : σ d = σ y := ha
    simp only [eqsOf, Bool.cond_eq_ite, nbeq_iff, List.mem_append] at h
    rcases h with h | h <;> split_ifs at h with he <;> simp only [List.mem_singleton,
      List.not_mem_nil] at h <;> subst h <;> subst he
    · rw [← hd, ← hy]; exact ha'
    · rw [← hd, ← hy]; exact ha'.symm
  | assertEq d y =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hy := hvn y (by simp [Memory.atomUses])
    have ha' : σ d = σ y := eq_of_add_eq_zero ha
    simp only [eqsOf, Bool.cond_eq_ite, nbeq_iff, List.mem_append] at h
    rcases h with h | h <;> split_ifs at h with he <;> simp only [List.mem_singleton,
      List.not_mem_nil] at h <;> subst h <;> subst he
    · rw [← hd, ← hy]; exact ha'
    · rw [← hd, ← hy]; exact ha'.symm
  | _ => simp [eqsOf] at h

theorem isPend_addFacts {a : Core.Atom} {st : SSt} {v : ℕ} :
    isPend ⟨st.occ, st.keys, st.named, addFacts a st.pend⟩ v = isPend st v := by
  simp only [isPend, addFacts, List.any_map]
  rfl

/-- **An atom's facts** about the pending values hold. -/
theorem addFacts_inv {a : Core.Atom} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : Inv loc rd σ st pre Ψ) (ha : a.Holds rd σ) (hvn : VnA a) :
    Inv loc rd σ ⟨st.occ, st.keys, st.named, addFacts a st.pend⟩ pre Ψ := by
  refine ⟨hI.vn, hI.occ, fun u hu hc hp ↦ hI.good u hu hc (by rwa [isPend_addFacts] at hp),
    hI.named, hI.kc, hI.keys, fun p hp ↦ ?_⟩
  simp only [addFacts, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.pend q hq
  refine ⟨h1, h2, h3, fun x hx ↦ ?_, fun k hk ↦ ?_, fun x hx ↦ ?_⟩
  · simp only at hx
    cases hk : q.kc with
    | some y =>
      rw [hk] at hx
      simp only [Option.some.injEq] at hx
      rw [← hx]; exact h4 y hk
    | none => rw [hk] at hx; exact constOf_sound ha hvn hx
  · rcases List.mem_append.mp hk with hk | hk
    · exact keysOf_sound ha hvn hk
    · exact h5 k hk
  · rcases List.mem_append.mp hx with hx | hx
    · exact eqsOf_sound ha hvn hx
    · exact h6 x hx

/-- **A pending value shown** holds its cell's word. -/
theorem pfOk_sound {st : SSt} {pre : List V} {Ψ : ℕ → E} (hI : Inv loc rd σ st pre Ψ) {p : PF}
    (hp : p ∈ st.pend) (h : pfOk loc st p = true) : σ (V.n p.v) = Ψ p.c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.pend p hp
  simp only [pfOk, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with (h | ⟨k, hk, hok⟩) | ⟨x, hx, hok⟩
  · cases hkc : p.kc with
    | none => rw [hkc] at h; simp at h
    | some x =>
      rw [hkc] at h
      cases ho : getF st.occ p.c with
      | none => rw [ho] at h; simp at h
      | some y =>
        rw [ho] at h
        cases y with
        | none => simp at h
        | some y =>
          simp only [beq_iff_eq] at h
          subst h
          rw [h4 x hkc, hI.kc p.c x ho]
  · simp only [keyOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hok
    obtain ⟨hin, k', hk', hkk⟩ := hok
    simp only [nbeq_iff, beq_iff_eq] at hkk
    obtain ⟨hop, hcs⟩ := hkk
    have hK := (hI.keys p.c k' hk').1
    rw [hop, hcs, keyHolds_keyCells, List.map_map] at hK
    have hmap : k.2.map (Ψ ∘ cellN loc) = k.2.map fun u ↦ σ (V.n u) := by
      refine List.map_congr_left fun u hu ↦ ?_
      have := hin u hu
      simp only [knownIn, Bool.and_eq_true, Nat.ble_eq] at this
      exact ((hI.named u this.1 this.2).1).symm
    rw [hmap] at hK
    exact (h5 k hk).unique hK
  · simp only [Bool.and_eq_true, nbeq_iff] at hok
    obtain ⟨hn, hc⟩ := hok
    rw [h6 x hx, ← hc]
    exact (hI.named x hn (by rw [hc]; exact h2)).1

theorem splitPend_spec (st : SSt) : ∀ (ps : List PF) {ok rest : List PF},
    splitPend loc st ps = (ok, rest) →
      (∀ p ∈ ok, p ∈ ps ∧ pfOk loc st p = true) ∧ (∀ p ∈ rest, p ∈ ps) ∧ ∀ p ∈ ps, p ∈ ok ∨ p ∈ rest
  | [], ok, rest, h => by
    simp only [splitPend, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | p :: ps, ok, rest, h => by
    simp only [splitPend] at h
    rcases hs : splitPend loc st ps with ⟨ok', rest'⟩
    rw [hs] at h
    obtain ⟨h1, h2, h3⟩ := splitPend_spec st ps hs
    cases hp : pfOk loc st p
    · simp only [hp, Bool.cond_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun q hq ↦ ⟨List.mem_cons_of_mem _ (h1 q hq).1, (h1 q hq).2⟩, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h2 q hq)
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inr List.mem_cons_self
        · rcases h3 q hq with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [hp, Bool.cond_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun q hq ↦ ?_, fun q hq ↦ List.mem_cons_of_mem _ (h2 q hq), fun q hq ↦ ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨List.mem_cons_self, hp⟩
        · exact ⟨List.mem_cons_of_mem _ (h1 q hq).1, (h1 q hq).2⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl List.mem_cons_self
        · rcases h3 q hq with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h

theorem getF_foldl_setF {α : Type} {a b : α} {d n : ℕ} : ∀ (ps : List PF) (t : Exec.Trie α),
    getF (ps.foldl (fun t p ↦ setF a d t p.v) t) n = some b → (∃ p ∈ ps, p.v = n) ∨ getF t n = some b
  | [], t, h => Or.inr h
  | p :: ps, t, h => by
    rcases getF_foldl_setF ps _ h with ⟨q, hq, he⟩ | h
    · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, he⟩
    · rcases getF_setF h with ⟨he, -⟩ | h
      · exact Or.inl ⟨p, List.mem_cons_self, he.symm⟩
      · exact Or.inr h

/-- **Showing pending values** keeps the invariant. -/
theorem discharge_inv : ∀ (n : ℕ) {st : SSt} {pre : List V} {Ψ : ℕ → E}, Inv loc rd σ st pre Ψ →
    Inv loc rd σ (discharge loc n st) pre Ψ ∧ (discharge loc n st).occ = st.occ
  | 0, st, pre, Ψ, hI => ⟨hI, rfl⟩
  | n + 1, st, pre, Ψ, hI => by
    simp only [discharge]
    rcases hs : splitPend loc st st.pend with ⟨ok, rest⟩
    obtain ⟨h1, h2, h3⟩ := splitPend_spec st st.pend hs
    cases ok with
    | nil => exact ⟨hI, rfl⟩
    | cons p ok =>
      simp only [Exec.Trie.seq_eq, SSt.seq_eq]
      have hokv : ∀ q ∈ p :: ok, σ (V.n q.v) = Ψ q.c := fun q hq ↦ pfOk_sound hI (h1 q hq).1 (h1 q hq).2
      refine (discharge_inv n ?_).imp id (fun h ↦ h)
      refine ⟨hI.vn, hI.occ, fun u hu hc hpe ↦ ?_, fun m hm hc ↦ ?_, hI.kc, hI.keys,
        fun q hq ↦ hI.pend q (h2 q hq)⟩
      · by_cases hold : isPend st u.idx = true
        · obtain ⟨q, hq, hqv⟩ := isPend_iff.mp hold
          rcases h3 q hq with hq' | hq'
          · obtain ⟨e1, -⟩ := hI.pend q hq
            rw [hI.vn u hu, ← hqv, hokv q hq', ← e1, cellN, hqv, ← hI.vn u hu]
          · have : isPend ⟨st.occ, st.keys, (p :: ok).foldl (fun t p ↦ setF () indexDepth t p.v) st.named,
                rest⟩ u.idx = true := isPend_iff.mpr ⟨q, hq', hqv⟩
            rw [hpe] at this; cases this
        · exact hI.good u hu hc (by simpa using hold)
      · simp only [isNamed] at hm
        rcases Option.isSome_iff_exists.mp hm with ⟨_, hm⟩
        rcases getF_foldl_setF _ _ hm with ⟨q, hq, rfl⟩ | hm
        · obtain ⟨e1, -, e3, -⟩ := hI.pend q (h1 q hq).1
          rw [e1]
          exact ⟨hokv q hq, e3⟩
        · exact hI.named m (by simp [isNamed, hm]) hc

end Steps

section Record

variable {loc : Exec.Trie ℕ} {rd : Reader} {σ : Val}

theorem mem_keyCells {c op : ℕ} {cs : List ℕ} : c ∈ keyCells op cs ↔ c ∈ cs := by
  match op, cs with
  | 0, [a, b] => simp only [keyCells]; cases Nat.ble a b <;> simp [or_comm]
  | 1, [a, b] => simp only [keyCells]; cases Nat.ble a b <;> simp [or_comm]
  | 0, [] => simp [keyCells]
  | 0, [_] => simp [keyCells]
  | 0, _ :: _ :: _ :: _ => simp [keyCells]
  | 1, [] => simp [keyCells]
  | 1, [_] => simp [keyCells]
  | 1, _ :: _ :: _ :: _ => simp [keyCells]
  | n + 2, cs => simp [keyCells]

/-- An entry of `cellKeys`: an output and inputs of the atom, the key holding of their words. -/
theorem cellKeys_sound {a : Core.Atom} (ha : a.Holds rd σ) {c op : ℕ} {ins : List ℕ}
    (h : (c, op, ins) ∈ cellKeys loc a) :
    ∃ out ∈ Memory.atomUses a, ∃ insV : List V, (∀ u ∈ insV, u ∈ Memory.atomUses a) ∧
      c = cellOf loc out ∧ ins = keyCells op (insV.map (cellOf loc)) ∧
      KeyHolds rd (σ out) op (insV.map σ) := by
  cases a with
  | add d x y =>
    have ha' : σ d = σ x + σ y := ha
    simp only [cellKeys, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨d, by simp [Memory.atomUses], [x, y], by simp [Memory.atomUses], rfl, rfl, ha'⟩
    · refine ⟨x, by simp [Memory.atomUses], [d, y], by simp [Memory.atomUses], rfl, rfl, ?_⟩
      show σ x = σ d + σ y
      rw [ha', add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · refine ⟨y, by simp [Memory.atomUses], [d, x], by simp [Memory.atomUses], rfl, rfl, ?_⟩
      show σ y = σ d + σ x
      rw [ha', add_comm (σ x), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  | mul d x y =>
    simp only [cellKeys, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨d, by simp [Memory.atomUses], [x, y], by simp [Memory.atomUses], rfl, rfl, ha⟩
  | blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    simp only [cellKeys, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨o0, by simp [Memory.atomUses], [m0, m1, m2, m3, c0, c1, md], by simp [Memory.atomUses],
        rfl, rfl, ⟨σ o1, ha⟩⟩
    · exact ⟨o1, by simp [Memory.atomUses], [m0, m1, m2, m3, c0, c1, md], by simp [Memory.atomUses],
        rfl, rfl, ⟨σ o0, ha⟩⟩
  | load d p off =>
    simp only [cellKeys, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨d, by simp [Memory.atomUses], [p], by simp [Memory.atomUses], rfl, rfl, ha⟩
  | _ => simp [cellKeys] at h

/-- The keys after `record`: the old ones, or one of the atom's with its cells in frame. -/
theorem mem_foldl_keys : ∀ (ks : List (ℕ × ℕ × List ℕ)) (t : Exec.Trie (List (ℕ × List ℕ))) (c : ℕ)
    (k : ℕ × List ℕ),
    k ∈ (getF (ks.foldl (fun t k ↦ bif Nat.ble 2 k.1 && k.2.2.all (Nat.ble 2) then
      setF ((k.2.1, k.2.2) :: (getF t k.1).getD []) envDepth t k.1 else t) t) c).getD [] →
    k ∈ (getF t c).getD [] ∨ ((c, k.1, k.2) ∈ ks ∧ 2 ≤ c ∧ ∀ c' ∈ k.2, 2 ≤ c')
  | [], t, c, k, h => Or.inl h
  | k0 :: ks, t, c, k, h => by
    rcases mem_foldl_keys ks _ c k h with h | ⟨h1, h2, h3⟩
    · cases hb : (Nat.ble 2 k0.1 && k0.2.2.all (Nat.ble 2))
      · simp only [hb, Bool.cond_false] at h; exact Or.inl h
      · simp only [hb, Bool.cond_true] at h
        simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at hb
        cases hg : getF (setF ((k0.2.1, k0.2.2) :: (getF t k0.1).getD []) envDepth t k0.1) c with
        | none => rw [hg] at h; cases h
        | some l =>
          rw [hg] at h
          rcases getF_setF hg with ⟨rfl, rfl⟩ | hg'
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr ⟨List.mem_cons_self, hb.1, hb.2⟩
            · exact Or.inl h
          · rw [hg']; exact Or.inl h
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2, h3⟩

/-- Cells of an atom fit the occupancy trie. -/
def CellsFit (loc : Exec.Trie ℕ) (vs : List V) : Prop := ∀ u ∈ vs, cellOf loc u + 1 < 2 ^ envDepth

/-- **Recording an atom's cell facts** keeps the invariant. -/
theorem record_inv {a : Core.Atom} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : Inv loc rd σ st pre Ψ) (ha : a.Holds rd σ) (hvn : VnA a)
    (hfit : CellsFit loc (Memory.atomUses a)) :
    Inv loc rd σ (record loc a st) pre Ψ ∧ Step st Ψ (record loc a st) Ψ := by
  unfold record
  cases hall : (Memory.atomUses a).all fun v ↦ isNamed st v.idx
  · rw [Bool.cond_false]; exact ⟨hI, Step.refl _ _⟩
  rw [Bool.cond_true]
  simp only [List.all_eq_true] at hall
  -- every value of the atom holds its cell's word, its cell occupied
  have hval : ∀ u ∈ Memory.atomUses a, 2 ≤ cellOf loc u →
      σ u = Ψ (cellOf loc u) ∧ (getF st.occ (cellOf loc u)).isSome := fun u hu hc ↦ by
    have := hI.named u.idx (hall u hu) (by rw [cellN_of_vn (hvn u hu)]; exact hc)
    rw [cellN_of_vn (hvn u hu), ← hvn u hu] at this
    exact this
  -- a refinement at one cell `c0` of the word `w`
  have hrefine : ∀ (c0 : ℕ) (x : ℕ × ℕ × ℕ), getF st.occ c0 = some none → c0 + 1 < 2 ^ envDepth →
      Ψ c0 = tw x → (∀ c, (getF (setF (some x) envDepth st.occ c0) c).isSome = (getF st.occ c).isSome) ∧
        ∀ c y, getF (setF (some x) envDepth st.occ c0) c = some (some y) → Ψ c = tw y := by
    intro c0 x h0 hb hw
    refine ⟨fun c ↦ ?_, fun c y hy ↦ ?_⟩
    · by_cases hc : c = c0
      · subst hc; rw [getF_setF_self _ _ hb, h0]; rfl
      · rw [getF_setF_ne _ _ hc]
    · by_cases hc : c = c0
      · subst hc; rw [getF_setF_self _ _ hb] at hy; cases hy; exact hw
      · rw [getF_setF_ne _ _ hc] at hy; exact hI.kc c y hy
  have hO : (∀ c, (getF (recOcc loc a st.occ) c).isSome = (getF st.occ c).isSome) ∧
      ∀ c y, getF (recOcc loc a st.occ) c = some (some y) → Ψ c = tw y := by
    unfold recOcc
    cases a with
    | const d x =>
      simp only
      cases h0 : getF st.occ (cellOf loc d) with
      | none => exact ⟨fun _ ↦ rfl, hI.kc⟩
      | some y =>
        cases y with
        | some _ => exact ⟨fun _ ↦ rfl, hI.kc⟩
        | none =>
          simp only
          cases hd2 : Nat.ble 2 (cellOf loc d)
          · exact ⟨fun _ ↦ rfl, hI.kc⟩
          · rw [Bool.cond_true]
            have hdv := hval d (by simp [Memory.atomUses]) (Nat.ble_eq.mp hd2)
            refine hrefine _ _ h0 (hfit d (by simp [Memory.atomUses])) ?_
            rw [← hdv.1, tw_limbs]; exact ha
    | assertNe x i p =>
      simp only
      cases h0 : getF st.occ (cellOf loc p) with
      | none => exact ⟨fun _ ↦ rfl, hI.kc⟩
      | some y =>
        cases y with
        | some _ => exact ⟨fun _ ↦ rfl, hI.kc⟩
        | none =>
          simp only
          cases hp2 : Nat.ble 2 (cellOf loc p)
          · exact ⟨fun _ ↦ rfl, hI.kc⟩
          · rw [Bool.cond_true]
            have hpv := hval p (by simp [Memory.atomUses]) (Nat.ble_eq.mp hp2)
            refine hrefine _ _ h0 (hfit p (by simp [Memory.atomUses])) ?_
            rw [← hpv.1, tw_one]; exact ha.2
    | _ => exact ⟨fun _ ↦ rfl, hI.kc⟩
  have hsome : ∀ c, (getF st.occ c).isSome → (getF (recOcc loc a st.occ) c).isSome := fun c h ↦ by
    rw [hO.1 c]; exact h
  refine ⟨⟨hI.vn, fun u hu hc ↦ hsome _ (hI.occ u hu hc), hI.good,
    fun n hn hc ↦ ⟨(hI.named n hn hc).1, hsome _ (hI.named n hn hc).2⟩, hO.2, fun c k hk ↦ ?_,
    fun p hp ↦ ?_⟩, fun c hc ↦ ⟨hsome c hc, rfl⟩⟩
  · rcases mem_foldl_keys _ _ c k hk with hk | ⟨hk, hc2, hins⟩
    · obtain ⟨h1, h2, h3⟩ := hI.keys c k hk
      exact ⟨h1, hsome _ h2, fun c' hc' ↦ hsome _ (h3 c' hc')⟩
    · obtain ⟨out, hout, insV, hinsV, rfl, hins', hK⟩ := cellKeys_sound ha hk
      have hcell : ∀ c' ∈ k.2, ∃ u ∈ insV, c' = cellOf loc u := fun c' hc' ↦ by
        rw [hins', mem_keyCells] at hc'
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc'
        exact ⟨u, hu, rfl⟩
      have hmap : insV.map σ = (insV.map (cellOf loc)).map Ψ := by
        rw [List.map_map]
        refine List.map_congr_left fun u hu ↦ ?_
        exact (hval u (hinsV u hu) (hins _ (by rw [hins', mem_keyCells]; exact List.mem_map_of_mem hu))).1
      rw [hmap, (hval out hout hc2).1, ← keyHolds_keyCells, ← hins'] at hK
      refine ⟨hK, hsome _ (hval out hout hc2).2, fun c' hc' ↦ ?_⟩
      obtain ⟨u, hu, rfl⟩ := hcell c' hc'
      exact hsome _ (hval u (hinsV u hu) (hins _ hc')).2
  · obtain ⟨h1, h2, h3, h4⟩ := hI.pend p hp
    exact ⟨h1, h2, hsome _ h3, h4⟩

end Record

section Atoms

variable {loc : Exec.Trie ℕ} {rd : Reader} {σ : Val}

/-- **An atom on the path** keeps the invariant, its values named. -/
theorem stepAtom_inv {a : Core.Atom} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : Inv loc rd σ st pre Ψ) (ha : a.Holds rd σ) (hvn : VnA a)
    (hfit : CellsFit loc (Memory.atomUses a)) :
    ∃ Ψ', Inv loc rd σ (stepAtom loc st a) (pre ++ Memory.atomUses a) Ψ' ∧
      Step st Ψ (stepAtom loc st a) Ψ' := by
  unfold stepAtom
  simp only [SSt.seq_eq]
  obtain ⟨Ψ1, hI1, hs1⟩ := nameAll_inv (kc := constOf a) (Memory.atomUses a) hI fun v hv ↦
    ⟨hvn v hv, hfit v hv, fun x hx ↦ by rw [hvn v hv]; exact constOf_sound ha hvn hx⟩
  have hI2 := addFacts_inv hI1 ha hvn
  obtain ⟨hI3, ho3⟩ := discharge_inv (_ + 1) hI2
  obtain ⟨hI4, hs4⟩ := record_inv hI3 ha hvn hfit
  refine ⟨Ψ1, hI4, hs1.trans ((Step.of_occ fun c h ↦ ?_).trans hs4)⟩
  rw [ho3]; exact h

/-- **Other values named** keep the invariant. -/
theorem nameStep_inv {vs : List V} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : Inv loc rd σ st pre Ψ) (hvn : ∀ v ∈ vs, v = V.n v.idx) (hfit : CellsFit loc vs) :
    ∃ Ψ', Inv loc rd σ (nameStep loc st vs) (pre ++ vs) Ψ' ∧ Step st Ψ (nameStep loc st vs) Ψ' := by
  unfold nameStep
  simp only [SSt.seq_eq]
  obtain ⟨Ψ1, hI1, hs1⟩ := nameAll_inv (kc := fun _ ↦ none) vs hI fun v hv ↦
    ⟨hvn v hv, hfit v hv, fun x hx ↦ by cases hx⟩
  obtain ⟨hI2, ho2⟩ := discharge_inv (_ + 1) hI1
  refine ⟨Ψ1, hI2, hs1.trans (Step.of_occ fun c h ↦ ?_)⟩
  rw [ho2]; exact h

end Atoms

/-! ## Joins -/

section Join

theorem occJoin_none : occJoin none none = none := rfl

theorem bothU_none : bothU none none = none := rfl

theorem get_occFold : ∀ (bs : List SSt) (acc : Exec.Trie (Option (ℕ × ℕ × ℕ))) (c : ℕ),
    (bs.foldl (fun t b ↦ Trie.merge occJoin t b.occ) acc).get c =
      match acc.get c with
      | some x => some x
      | none => if ∃ b ∈ bs, (b.occ.get c).isSome then some none else none
  | [], acc, c => by cases h : acc.get c <;> simp [h]
  | b :: bs, acc, c => by
    simp only [List.foldl_cons]
    rw [get_occFold bs _ c, Trie.get_merge occJoin_none]
    cases ha : acc.get c with
    | some x => simp [occJoin]
    | none =>
      cases hb : b.occ.get c with
      | some y => simp [occJoin, hb]
      | none =>
        simp only [occJoin]
        congr 1
        simp only [List.mem_cons, exists_eq_or_imp, hb, Option.isSome_none, Bool.false_eq_true,
          false_or]

theorem get_namedFold : ∀ (bs : List SSt) (acc : Exec.Trie Unit) (n : ℕ),
    (bs.foldl (fun t b ↦ Trie.merge bothU t b.named) acc).get n = some () →
      acc.get n = some () ∧ ∀ b ∈ bs, b.named.get n = some ()
  | [], acc, n, h => ⟨h, fun _ h ↦ by cases h⟩
  | b :: bs, acc, n, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := get_namedFold bs _ n h
    rw [Trie.get_merge bothU_none] at h1
    cases ha : acc.get n <;> cases hb : b.named.get n <;> rw [ha, hb] at h1 <;> simp only [bothU,
      reduceCtorEq] at h1
    exact ⟨rfl, fun b' hb' ↦ by
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact hb
      · exact h2 b' hb'⟩

variable {loc : Exec.Trie ℕ} {rd : Reader} {σ : Val}

/-- **After a join**, for the branch taken: the facts from before the branch, with the branch's
cell words. -/
theorem joinSt_inv {st1 b : SSt} {bs : List SSt} {pre1 preb : List V} {Ψ1 Ψb : ℕ → E}
    (hI1 : Inv loc rd σ st1 pre1 Ψ1) (hIb : Inv loc rd σ b preb Ψb) (hs : Step st1 Ψ1 b Ψb)
    (hb : b ∈ bs) (hp : b.pend = []) :
    Inv loc rd σ (joinSt st1 bs) preb Ψb ∧ Step st1 Ψ1 (joinSt st1 bs) Ψb := by
  have hocc : ∀ c, getF (joinSt st1 bs).occ c =
      match getF st1.occ c with
      | some x => some x
      | none => if ∃ b ∈ bs, (getF b.occ c).isSome then some none else none := fun c ↦ by
    simp only [joinSt, getF_eq]; exact get_occFold bs st1.occ c
  have hsome : ∀ c, (getF b.occ c).isSome → (getF (joinSt st1 bs).occ c).isSome := fun c h ↦ by
    rw [hocc]
    cases h1 : getF st1.occ c with
    | some x => rfl
    | none => simp only [show ∃ b ∈ bs, (getF b.occ c).isSome = true from ⟨b, hb, h⟩, ↓reduceIte]; rfl
  have hsome1 : ∀ c, (getF st1.occ c).isSome → getF (joinSt st1 bs).occ c = getF st1.occ c := fun c h ↦ by
    rw [hocc]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    rw [hx]
  refine ⟨⟨hIb.vn, fun u hu hc ↦ hsome _ (hIb.occ u hu hc), fun u hu hc _ ↦ ?_, fun n hn hc ↦ ?_,
    fun c x hx ↦ ?_, fun c k hk ↦ ?_, fun p hp' ↦ by simp [joinSt] at hp'⟩,
    fun c hc ↦ ⟨by rw [hsome1 c hc]; exact hc, (hs c hc).2⟩⟩
  · exact hIb.good u hu hc (by simp [isPend, hp])
  · have hnb : isNamed b n = true := by
      simp only [isNamed, joinSt] at hn ⊢
      cases bs with
      | nil => cases hb
      | cons b0 bs' =>
        simp only at hn
        rcases Option.isSome_iff_exists.mp hn with ⟨u, hu⟩
        rw [getF_eq] at hu
        obtain ⟨h1, h2⟩ := get_namedFold bs' b0.named n (by cases u; exact hu)
        rcases List.mem_cons.mp hb with rfl | hb'
        · rw [getF_eq, h1]; rfl
        · rw [getF_eq, h2 b hb']; rfl
    exact ⟨(hIb.named n hnb hc).1, hsome _ (hIb.named n hnb hc).2⟩
  · rw [hocc] at hx
    cases h1 : getF st1.occ c with
    | some y =>
      rw [h1] at hx
      cases hx
      rw [(hs c (by rw [h1]; rfl)).2]
      exact hI1.kc c x h1
    | none =>
      rw [h1] at hx
      simp only at hx
      split_ifs at hx
      cases hx
  · have hk' : k ∈ (getF st1.keys c).getD [] := hk
    obtain ⟨h1, h2, h3⟩ := hI1.keys c k hk'
    refine ⟨?_, by rw [hsome1 c h2]; exact h2, fun c' hc' ↦ by rw [hsome1 c' (h3 c' hc')]; exact h3 c' hc'⟩
    rw [(hs c h2).2]
    have : k.2.map Ψb = k.2.map Ψ1 := List.map_congr_left fun c' hc' ↦ (hs c' (h3 c' hc')).2
    rw [this]; exact h1

end Join

/-! ## Paths -/

section Paths

open LeanVM.Guest.Memory

variable {σ : Val}

theorem pick_noRet {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ) {es : List Ev}
    {vs : List V}, pick σ x args rets j fs ≠ .ret es vs
  | [], _, _, _, h => by simp [pick] at h
  | f :: fs, j, _, _, h => by
      unfold pick at h
      split_ifs at h
      exact pick_noRet fs (j + 1) h

mutual
theorem walk1_noRet : ∀ (s : Stmt), Stmt.noRet s = true → ∀ es vs, walk1 σ s ≠ .ret es vs
  | .atom _, _, _, _, h => by simp [walk1] at h
  | .ite c z n, hn, es, vs, h => by
      simp only [Stmt.noRet, Bool.and_eq_true] at hn
      rw [walk1] at h
      split_ifs at h
      · cases hz : walk σ z <;> rw [hz] at h <;> simp only [Out.pre, reduceCtorEq] at h
        exact walk_noRet z hn.1 _ _ hz
      · cases hz : walk σ n <;> rw [hz] at h <;> simp only [Out.pre, reduceCtorEq] at h
        exact walk_noRet n hn.2 _ _ hz
  | .match_ x arms, hn, es, vs, h => by
      simp only [Stmt.noRet] at hn
      rw [walk1] at h
      exact walkArms_noRet x arms hn 0 es vs h
  | .call .., _, _, _, h => by simp [walk1] at h
  | .callIf .., _, _, _, h => by simp [walk1] at h
  | .dispatch x fs args rets, _, es, vs, h => by
      rw [walk1] at h
      exact pick_noRet fs 0 h
  | .ret _, hn, _, _, _ => by simp [Stmt.noRet] at hn

theorem walk_noRet : ∀ (ss : List Stmt), Stmt.noRetList ss = true → ∀ es vs, walk σ ss ≠ .ret es vs
  | [], _, _, _, h => by simp [walk] at h
  | s :: ss, hn, es, vs, h => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at hn
      rw [walk] at h
      cases h1 : walk1 σ s with
      | fall es1 =>
        rw [h1] at h
        cases h2 : walk σ ss <;> rw [h2] at h <;> simp only [Out.seq, Out.pre, reduceCtorEq] at h
        exact walk_noRet ss hn.2 _ _ h2
      | ret es1 vs1 => exact walk1_noRet s hn.1 es1 vs1 h1
      | stuck => rw [h1] at h; simp [Out.seq] at h

theorem walkArms_noRet (x : V) : ∀ (arms : List (List Stmt)), Stmt.noRetArms arms = true →
    ∀ (j : ℕ) es vs, walkArms σ x j arms ≠ .ret es vs
  | [], _, _, _, _, h => by simp [walkArms] at h
  | a :: as, hn, j, es, vs, h => by
      simp only [Stmt.noRetArms, Bool.and_eq_true] at hn
      unfold walkArms at h
      split_ifs at h
      · exact walk_noRet a hn.1 _ _ h
      · exact walkArms_noRet x as hn.2 (j + 1) _ _ h
end

theorem mayRetArms_eq : ∀ (arms : List (List Stmt)), mayRetArms arms = !Stmt.noRetArms arms
  | [] => rfl
  | a :: as => by simp [mayRetArms, Stmt.noRetArms, mayRetArms_eq as]

/-- A statement whose walk returns may return. -/
theorem mayRet_of_walk1 {s : Stmt} {es : List Ev} {vs : List V} (h : walk1 σ s = .ret es vs) :
    mayRet s = true := by
  cases hm : mayRet s
  · have : Stmt.noRet s = true := by
      cases s with
      | ite c z n => simpa [mayRet, Stmt.noRet] using hm
      | match_ x arms => simpa [mayRet, mayRetArms_eq, Stmt.noRet] using hm
      | ret vs => simp [mayRet] at hm
      | _ => rfl
    exact absurd h (walk1_noRet s this es vs)
  · rfl

end Paths

section Walk

open LeanVM.Guest.Memory

variable {loc : Exec.Trie ℕ} {P : Plumb} {rd : Reader} {σ : Val}

/-- Values named by their numbers whose cells fit the tries. -/
def FitV (loc : Exec.Trie ℕ) (vs : List V) : Prop :=
  ∀ v ∈ vs, v = V.n v.idx ∧ cellOf loc v + 1 < 2 ^ envDepth

theorem FitV.mono {vs ws : List V} (h : FitV loc ws) (hs : ∀ v ∈ vs, v ∈ ws) : FitV loc vs :=
  fun v hv ↦ h v (hs v hv)

/-- What a walk gives of an outcome: at a fall-through, the end state with the path's values named;
at a return, a state with every value named and nothing pending (or the end state itself). -/
def Conc (loc : Exec.Trie ℕ) (rd : Reader) (σ : Val) (st : SSt) (Ψ : ℕ → E) (pre : List V)
    (st' : SSt) : Out → Prop
  | .fall es => ∃ pre' Ψ', Inv loc rd σ st' pre' Ψ' ∧ Step st Ψ st' Ψ' ∧ (∀ v ∈ pre, v ∈ pre') ∧
      ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ pre'
  | .ret es vs => ∃ st'' pre' Ψ', Inv loc rd σ st'' pre' Ψ' ∧ Step st Ψ st'' Ψ' ∧
      (st''.pend = [] ∨ st'' = st') ∧
      (∀ v ∈ pre, v ∈ pre') ∧ (∀ e ∈ es, ∀ v ∈ e.uses, v ∈ pre') ∧ ∀ v ∈ vs, v ∈ pre'
  | .stuck => True

/-- Names `vs` after `pre`: a fall-through naming `vs`. -/
theorem conc_names {st st' : SSt} {Ψ Ψ' : ℕ → E} {pre vs : List V} {es : List Ev}
    (hI : Inv loc rd σ st' (pre ++ vs) Ψ') (hs : Step st Ψ st' Ψ')
    (hu : ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ vs) : Conc loc rd σ st Ψ pre st' (.fall es) :=
  ⟨pre ++ vs, Ψ', hI, hs, fun _ hv ↦ List.mem_append_left _ hv,
    fun e he v hv ↦ List.mem_append_right _ (hu e he v hv)⟩

/-- A statement's outcome followed by the rest of its block's. -/
theorem conc_seq {st st1 st' : SSt} {Ψ : ℕ → E} {pre : List V} {o1 o2 : Out}
    (h1 : Conc loc rd σ st Ψ pre st1 o1)
    (h2 : ∀ es1, o1 = .fall es1 → ∀ pre1 Ψ1, Inv loc rd σ st1 pre1 Ψ1 → Step st Ψ st1 Ψ1 →
      (∀ v ∈ pre, v ∈ pre1) → Conc loc rd σ st1 Ψ1 pre1 st' o2)
    (hr : ∀ es vs, o1 = .ret es vs → st1.pend = []) : Conc loc rd σ st Ψ pre st' (o1.seq o2) := by
  cases o1 with
  | fall es1 =>
    obtain ⟨pre1, Ψ1, hI1, hs1, hp1, hu1⟩ := h1
    have h2' := h2 es1 rfl pre1 Ψ1 hI1 hs1 hp1
    cases o2 with
    | fall es2 =>
      obtain ⟨pre2, Ψ2, hI2, hs2, hp2, hu2⟩ := h2'
      exact ⟨pre2, Ψ2, hI2, hs1.trans hs2, fun v hv ↦ hp2 v (hp1 v hv), fun e he v hv ↦
        (List.mem_append.mp he).elim (fun he ↦ hp2 v (hu1 e he v hv)) (fun he ↦ hu2 e he v hv)⟩
    | ret es2 vs =>
      obtain ⟨st'', pre2, Ψ2, hI2, hs2, hp, hp2, hu2, hv2⟩ := h2'
      exact ⟨st'', pre2, Ψ2, hI2, hs1.trans hs2, hp, fun v hv ↦ hp2 v (hp1 v hv), fun e he v hv ↦
        (List.mem_append.mp he).elim (fun he ↦ hp2 v (hu1 e he v hv)) (fun he ↦ hu2 e he v hv), hv2⟩
    | stuck => trivial
  | ret es vs =>
    obtain ⟨st'', pre', Ψ', hI', hs', hp, h3⟩ := h1
    refine ⟨st'', pre', Ψ', hI', hs', Or.inl ?_, h3⟩
    rcases hp with hp | rfl
    · exact hp
    · exact hr es vs rfl
  | stuck => trivial

theorem evs_seq_fall {es1 : List Ev} {o : Out} {e : Ev} (he : e ∈ o.evs) :
    e ∈ ((Out.fall es1).seq o).evs := by
  cases o <;> simp_all [Out.seq, Out.pre, Out.evs]

theorem evs_pre {es : List Ev} {o : Out} {e : Ev} (he : e ∈ o.evs) : e ∈ (o.pre es).evs := by
  cases o <;> simp_all [Out.pre, Out.evs]

theorem evs_pre_head {es : List Ev} {o : Out} {e : Ev} (he : e ∈ es) (hs : o ≠ .stuck) :
    e ∈ (o.pre es).evs := by
  cases o <;> simp_all [Out.pre, Out.evs]

/-- A walk's end state has nothing pending. -/
theorem swL_pend : ∀ (ss : List Stmt) {st st' : SSt}, swL loc P st ss = some st' → st'.pend = []
  | [], st, st', h => by
    simp only [swL, Bool.cond_eq_ite] at h
    split_ifs at h with hp
    cases h; exact List.isEmpty_iff.mp hp
  | s :: ss, st, st', h => by
    simp only [swL] at h
    cases hs : swS loc P st s with
    | none => rw [hs] at h; cases h
    | some st1 =>
      rw [hs] at h
      simp only [SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h
      exact swL_pend ss h

/-- A conclusion for the values `vs` named first, before the events `es`. -/
theorem conc_pre {st st' : SSt} {Ψ : ℕ → E} {pre vs : List V} {es : List Ev} {o : Out}
    (h : Conc loc rd σ st Ψ (pre ++ vs) st' o) (hu : ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ vs) :
    Conc loc rd σ st Ψ pre st' (o.pre es) := by
  cases o with
  | fall es' =>
    obtain ⟨pre', Ψ', hI, hs, hp, hu'⟩ := h
    refine ⟨pre', Ψ', hI, hs, fun v hv ↦ hp v (List.mem_append_left _ hv), fun e he v hv ↦ ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact hp v (List.mem_append_right _ (hu e he v hv))
    · exact hu' e he v hv
  | ret es' vs' =>
    obtain ⟨st'', pre', Ψ', hI, hs, hpe, hp, hu', hv⟩ := h
    refine ⟨st'', pre', Ψ', hI, hs, hpe, fun v hv ↦ hp v (List.mem_append_left _ hv), fun e he v hv ↦ ?_,
      hv⟩
    rcases List.mem_append.mp he with he | he
    · exact hp v (List.mem_append_right _ (hu e he v hv))
    · exact hu' e he v hv
  | stuck => trivial

/-- A conclusion for fewer values named before. -/
theorem conc_shrink {st st' : SSt} {Ψ : ℕ → E} {pre vs : List V} {o : Out}
    (h : Conc loc rd σ st Ψ (pre ++ vs) st' o) : Conc loc rd σ st Ψ pre st' o := by
  cases o with
  | fall es =>
    obtain ⟨pre', Ψ', hI, hs, hp, hu⟩ := h
    exact ⟨pre', Ψ', hI, hs, fun v hv ↦ hp v (List.mem_append_left _ hv), hu⟩
  | ret es vs' =>
    obtain ⟨st'', pre', Ψ', hI, hs, hpe, hp, hu, hv⟩ := h
    exact ⟨st'', pre', Ψ', hI, hs, hpe, fun v hv ↦ hp v (List.mem_append_left _ hv), hu, hv⟩
  | stuck => trivial

/-- **A branch's conclusion** after the join, from before the branch. -/
theorem conc_join {st st1 b : SSt} {bs : List SSt} {Ψ Ψ1 : ℕ → E} {pre1 : List V} {o : Out}
    (hI1 : Inv loc rd σ st1 pre1 Ψ1) (hs1 : Step st Ψ st1 Ψ1) (hb : b ∈ bs)
    (hC : Conc loc rd σ st1 Ψ1 pre1 b o) (hp : b.pend = []) :
    Conc loc rd σ st Ψ pre1 (joinSt st1 bs) o := by
  cases o with
  | fall es =>
    obtain ⟨pre', Ψ', hI', hs', hp1, hu⟩ := hC
    obtain ⟨hIj, hsj⟩ := joinSt_inv hI1 hI' hs' hb hp
    exact ⟨pre', Ψ', hIj, hs1.trans hsj, hp1, hu⟩
  | ret es vs =>
    obtain ⟨st'', pre', Ψ', hI', hs', hp2, hp1, hu, hvs⟩ := hC
    refine ⟨st'', pre', Ψ', hI', hs1.trans hs', Or.inl ?_, hp1, hu, hvs⟩
    rcases hp2 with hp2 | rfl
    · exact hp2
    · exact hp
  | stuck => trivial

theorem pick_cases {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ),
    pick σ x args rets j fs = .stuck ∨ ∃ g, pick σ x args rets j fs = .fall [.call g args rets]
  | [], _ => Or.inl (by simp [pick])
  | f :: fs, j => by
    unfold pick
    split_ifs
    · exact Or.inr ⟨f, rfl⟩
    · exact pick_cases fs (j + 1)

theorem seq_evs {o1 o2 : Out} (h : o1.seq o2 ≠ .stuck) :
    (∀ e ∈ o1.evs, e ∈ (o1.seq o2).evs) ∧ ∀ es1, o1 = .fall es1 → ∀ e ∈ o2.evs, e ∈ (o1.seq o2).evs := by
  cases o1 <;> cases o2 <;> simp_all [Out.seq, Out.pre, Out.evs]

mutual
/-- **One statement**: what the walk gives of its outcome on a path. -/
theorem swS_sound : ∀ (s : Stmt) {st st' : SSt} {pre : List V} {Ψ : ℕ → E},
    swS loc P st s = some st' → Inv loc rd σ st pre Ψ → FitV loc (Stmt.uses s) →
    (∀ e ∈ (walk1 σ s).evs, e.Holds rd σ) → Conc loc rd σ st Ψ pre st' (walk1 σ s)
  | .atom a, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swS, Bool.cond_eq_ite] at h
      split_ifs at h
      cases h
      have ha : a.Holds rd σ := he (.atom a) (by simp [walk1, Out.evs])
      obtain ⟨Ψ', hI', hs⟩ := stepAtom_inv hI ha (fun u hu ↦ (hv u hu).1) (fun u hu ↦ (hv u hu).2)
      refine conc_names hI' hs fun e he' v hv' ↦ ?_
      simp only [List.mem_singleton] at he'
      subst he'
      exact hv'
  | .ite c z n, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h with hp
      cases hz : swL loc P (nameStep loc st [c]) z <;> cases hn : swL loc P (nameStep loc st [c]) n <;>
        rw [hz, hn] at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i sz sn
      have hc := hv c List.mem_cons_self
      obtain ⟨Ψ1, hI1, hs1⟩ := nameStep_inv hI (fun u hu ↦ by
        rw [List.mem_singleton.mp hu]; exact hc.1) (fun u hu ↦ by rw [List.mem_singleton.mp hu]; exact hc.2)
      have hu : ∀ e ∈ [Ev.inK c], ∀ v ∈ e.uses, v ∈ [c] := fun e he v hv ↦ by
        simp only [List.mem_singleton] at he; subst he; exact hv
      simp only [walk1] at he ⊢
      by_cases hc0 : σ c = 0
      · simp only [hc0, ↓reduceIte] at he ⊢
        refine conc_pre (conc_join hI1 hs1 List.mem_cons_self ?_ (swL_pend z hz)) hu
        exact swL_sound z hz hI1 (hv.mono fun v hv ↦ by simp [Stmt.uses, hv])
          fun e he' ↦ he e (evs_pre he')
      · simp only [hc0, ↓reduceIte] at he ⊢
        refine conc_pre (conc_join hI1 hs1 (by simp) ?_ (swL_pend n hn)) hu
        exact swL_sound n hn hI1 (hv.mono fun v hv ↦ by simp [Stmt.uses, hv])
          fun e he' ↦ he e (evs_pre he')
  | .match_ x arms, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h with hp
      cases ha : swArms loc P (nameStep loc st [x]) arms <;> rw [ha] at h <;>
        simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i bs
      have hx := hv x List.mem_cons_self
      obtain ⟨Ψ1, hI1, hs1⟩ := nameStep_inv hI (fun u hu ↦ by
        rw [List.mem_singleton.mp hu]; exact hx.1) (fun u hu ↦ by rw [List.mem_singleton.mp hu]; exact hx.2)
      simp only [walk1] at he ⊢
      rcases swArms_sound x arms 0 ha hI1 (hv.mono fun v hv ↦ by simp [Stmt.uses, hv]) he with
        hst | ⟨b, hb, hC, hbp⟩
      · rw [hst]; trivial
      · exact conc_shrink (conc_join hI1 hs1 hb hC hbp)
  | .call f args rets, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStep_inv hI (fun u hu ↦ (hv u hu).1) (fun u hu ↦ (hv u hu).2)
      refine conc_names hI' hs fun e he' v hv' ↦ ?_
      simp only [List.mem_singleton] at he'
      subst he'
      simpa [Ev.uses, Stmt.uses] using hv'
  | .callIf c f args, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStep_inv hI (fun u hu ↦ (hv u hu).1) (fun u hu ↦ (hv u hu).2)
      refine conc_names hI' hs fun e he' v hv' ↦ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl
      · simp only [Ev.uses, List.mem_singleton] at hv'
        simp [Stmt.uses, hv']
      · split_ifs at hv' <;> simp_all [Ev.uses, Stmt.uses]
  | .dispatch x fs args rets, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStep_inv hI (fun u hu ↦ (hv u hu).1) (fun u hu ↦ (hv u hu).2)
      simp only [walk1]
      rcases pick_cases (σ := σ) (x := x) (args := args) (rets := rets) fs 0 with hp | ⟨g, hp⟩
      · rw [hp]; trivial
      · rw [hp]
        refine conc_names hI' hs fun e he' v hv' ↦ ?_
        simp only [List.mem_singleton] at he'
        subst he'
        simp only [Ev.uses] at hv' ⊢
        exact List.mem_cons_of_mem _ hv'
  | .ret vs, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStep_inv hI (fun u hu ↦ (hv u hu).1) (fun u hu ↦ (hv u hu).2)
      simp only [walk1]
      exact ⟨nameStep loc st (stmtNames (.ret vs)), pre ++ stmtNames (.ret vs), Ψ', hI', hs, Or.inr rfl,
        fun _ hv ↦ List.mem_append_left _ hv, fun e he ↦ absurd he List.not_mem_nil,
        fun v hv ↦ List.mem_append_right _ hv⟩

/-- **A block**: what the walk gives of its outcome on a path. -/
theorem swL_sound : ∀ (ss : List Stmt) {st st' : SSt} {pre : List V} {Ψ : ℕ → E},
    swL loc P st ss = some st' → Inv loc rd σ st pre Ψ → FitV loc (Stmt.usesList ss) →
    (∀ e ∈ (walk σ ss).evs, e.Holds rd σ) → Conc loc rd σ st Ψ pre st' (walk σ ss)
  | [], st, st', pre, Ψ, h, hI, _, _ => by
      simp only [swL, Bool.cond_eq_ite] at h
      split_ifs at h
      cases h
      exact ⟨pre, Ψ, hI, Step.refl _ _, fun _ hv ↦ hv, fun e he ↦ by simp at he⟩
  | s :: ss, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swL] at h
      cases hs : swS loc P st s with
      | none => rw [hs] at h; cases h
      | some st1 =>
        rw [hs] at h
        simp only [SSt.seq_eq, Bool.cond_eq_ite] at h
        split_ifs at h with hm
        rw [walk] at he ⊢
        by_cases hst : (walk1 σ s).seq (walk σ ss) = .stuck
        · rw [hst]; trivial
        obtain ⟨he1, he2⟩ := seq_evs hst
        have hvs : FitV loc (Stmt.uses s) := hv.mono fun v hv ↦ by simp [Stmt.usesList, hv]
        have hvss : FitV loc (Stmt.usesList ss) := hv.mono fun v hv ↦ by simp [Stmt.usesList, hv]
        refine conc_seq (swS_sound s hs hI hvs fun e h ↦ he e (he1 e h))
          (fun es1 h1 pre1 Ψ1 hI1 _ _ ↦ swL_sound ss h hI1 hvss fun e h ↦ he e (he2 es1 h1 e h))
          fun es vs hr ↦ ?_
        have := mayRet_of_walk1 hr
        simp only [this, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hm
        simpa using hm

/-- **The arms of a `match`**: the arm taken. -/
theorem swArms_sound (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {st : SSt} {bs : List SSt}
    {pre : List V} {Ψ : ℕ → E}, swArms loc P st arms = some bs → Inv loc rd σ st pre Ψ →
    FitV loc (Stmt.usesArms arms) → (∀ e ∈ (walkArms σ x j arms).evs, e.Holds rd σ) →
    walkArms σ x j arms = .stuck ∨
      ∃ b ∈ bs, Conc loc rd σ st Ψ pre b (walkArms σ x j arms) ∧ b.pend = []
  | [], j, _, _, _, _, _, _, _, _ => Or.inl (by simp [walkArms])
  | a :: as, j, st, bs, pre, Ψ, h, hI, hv, he => by
      simp only [swArms] at h
      cases ha : swL loc P st a <;> cases has : swArms loc P st as <;> rw [ha, has] at h <;>
        simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i b bs'
      unfold walkArms at he ⊢
      split_ifs at he ⊢
      · exact Or.inr ⟨b, List.mem_cons_self, swL_sound a ha hI (hv.mono fun v hv ↦ by
          simp [Stmt.usesArms, hv]) he, swL_pend a ha⟩
      · rcases swArms_sound x as (j + 1) has hI (hv.mono fun v hv ↦ by simp [Stmt.usesArms, hv]) he with
          h | ⟨b', hb', h⟩
        · exact Or.inl h
        · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', h⟩
end

end Walk

/-! ## Atoms of a body -/

mutual
/-- The atoms of a statement, at any depth. -/
def sAtoms : Stmt → List Core.Atom
  | .atom a => [a]
  | .ite _ z n => lAtoms z ++ lAtoms n
  | .match_ _ arms => aAtoms arms
  | _ => []

/-- The atoms of a block. -/
def lAtoms : List Stmt → List Core.Atom
  | [] => []
  | s :: ss => sAtoms s ++ lAtoms ss

/-- The atoms of arms. -/
def aAtoms : List (List Stmt) → List Core.Atom
  | [] => []
  | a :: as => lAtoms a ++ aAtoms as
end

section Atoms2

open LeanVM.Guest.Memory

variable {loc : Exec.Trie ℕ} {P : Plumb}

mutual
theorem swS_listed : ∀ (s : Stmt) {st st' : SSt}, swS loc P st s = some st' →
    ∀ a ∈ sAtoms s, atomListed loc P a = true
  | .atom a, st, st', h, a', ha' => by
      simp only [swS, Bool.cond_eq_ite] at h
      split_ifs at h with hl
      simp only [sAtoms, List.mem_singleton] at ha'
      subst ha'; exact hl
  | .ite c z n, st, st', h, a, ha => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h
      cases hz : swL loc P (nameStep loc st [c]) z <;> cases hn : swL loc P (nameStep loc st [c]) n <;>
        rw [hz, hn] at h <;> simp only [reduceCtorEq] at h
      simp only [sAtoms, List.mem_append] at ha
      rcases ha with ha | ha
      · exact swL_listed z hz a ha
      · exact swL_listed n hn a ha
  | .match_ x arms, st, st', h, a, ha => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h
      cases har : swArms loc P (nameStep loc st [x]) arms <;> rw [har] at h <;>
        simp only [reduceCtorEq] at h
      exact swArms_listed arms har a ha
  | .call .., _, _, _, _, ha => by simp [sAtoms] at ha
  | .callIf .., _, _, _, _, ha => by simp [sAtoms] at ha
  | .dispatch .., _, _, _, _, ha => by simp [sAtoms] at ha
  | .ret _, _, _, _, _, ha => by simp [sAtoms] at ha

theorem swL_listed : ∀ (ss : List Stmt) {st st' : SSt}, swL loc P st ss = some st' →
    ∀ a ∈ lAtoms ss, atomListed loc P a = true
  | [], _, _, _, _, ha => by simp [lAtoms] at ha
  | s :: ss, st, st', h, a, ha => by
      simp only [swL] at h
      cases hs : swS loc P st s with
      | none => rw [hs] at h; cases h
      | some st1 =>
        rw [hs] at h
        simp only [SSt.seq_eq, Bool.cond_eq_ite] at h
        split_ifs at h
        simp only [lAtoms, List.mem_append] at ha
        rcases ha with ha | ha
        · exact swS_listed s hs a ha
        · exact swL_listed ss h a ha

theorem swArms_listed : ∀ (arms : List (List Stmt)) {st : SSt} {bs : List SSt},
    swArms loc P st arms = some bs → ∀ a ∈ aAtoms arms, atomListed loc P a = true
  | [], _, _, _, _, ha => by simp [aAtoms] at ha
  | b :: as, st, bs, h, a, ha => by
      simp only [swArms] at h
      cases hb : swL loc P st b <;> cases has : swArms loc P st as <;> rw [hb, has] at h <;>
        simp only [reduceCtorEq] at h
      simp only [aAtoms, List.mem_append] at ha
      rcases ha with ha | ha
      · exact swL_listed b hb a ha
      · exact swArms_listed as has a ha
end

variable {σ : Val}

theorem pick_atoms {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ) {a : Core.Atom},
    Ev.atom a ∉ (pick σ x args rets j fs).evs
  | [], _, _, h => by simp [pick, Out.evs] at h
  | f :: fs, j, a, h => by
      unfold pick at h
      split_ifs at h
      · simp [Out.evs] at h
      · exact pick_atoms fs (j + 1) h

theorem evs_seq_sub {o1 o2 : Out} {e : Ev} (h : e ∈ (o1.seq o2).evs) : e ∈ o1.evs ∨ e ∈ o2.evs := by
  cases o1 <;> cases o2 <;> simp_all [Out.seq, Out.pre, Out.evs]

theorem evs_pre_sub {es : List Ev} {o : Out} {e : Ev} (h : e ∈ (o.pre es).evs) : e ∈ es ∨ e ∈ o.evs := by
  cases o <;> simp_all [Out.pre, Out.evs]

mutual
/-- **Every atom a path runs is an atom of the body.** -/
theorem walk1_atoms : ∀ (s : Stmt) {a : Core.Atom}, Ev.atom a ∈ (walk1 σ s).evs → a ∈ sAtoms s
  | .atom a', a, h => by simp [walk1, Out.evs] at h; simp [sAtoms, h]
  | .ite c z n, a, h => by
      simp only [walk1] at h
      rcases evs_pre_sub h with h | h
      · simp at h
      · simp only [sAtoms, List.mem_append]
        split_ifs at h
        · exact Or.inl (walk_atoms z h)
        · exact Or.inr (walk_atoms n h)
  | .match_ x arms, a, h => by simp only [walk1] at h; exact walkArms_atoms x arms 0 h
  | .call .., a, h => by simp [walk1, Out.evs] at h
  | .callIf .., a, h => by simp only [walk1, Out.evs] at h; split_ifs at h <;> simp at h
  | .dispatch x fs args rets, a, h => by simp only [walk1] at h; exact absurd h (pick_atoms fs 0)
  | .ret _, a, h => by simp [walk1, Out.evs] at h

theorem walk_atoms : ∀ (ss : List Stmt) {a : Core.Atom}, Ev.atom a ∈ (walk σ ss).evs → a ∈ lAtoms ss
  | [], a, h => by simp [walk, Out.evs] at h
  | s :: ss, a, h => by
      simp only [walk] at h
      simp only [lAtoms, List.mem_append]
      rcases evs_seq_sub h with h | h
      · exact Or.inl (walk1_atoms s h)
      · exact Or.inr (walk_atoms ss h)

theorem walkArms_atoms (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {a : Core.Atom},
    Ev.atom a ∈ (walkArms σ x j arms).evs → a ∈ aAtoms arms
  | [], _, a, h => by simp [walkArms, Out.evs] at h
  | b :: as, j, a, h => by
      unfold walkArms at h
      simp only [aAtoms, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_atoms b h)
      · exact Or.inr (walkArms_atoms x as (j + 1) h)
end

mutual
/-- **Every temporary is a range check's.** -/
theorem tmps_atoms : ∀ (s : Stmt) {t : V}, t ∈ Stmt.tmps s → ∃ a ∈ sAtoms s, t ∈ atomTmps a
  | .atom a, t, h => ⟨a, by simp [sAtoms], h⟩
  | .ite c z n, t, h => by
      simp only [Stmt.tmps, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨a, ha, ht⟩ := tmpsList_atoms z h; exact ⟨a, by simp [sAtoms, ha], ht⟩
      · obtain ⟨a, ha, ht⟩ := tmpsList_atoms n h; exact ⟨a, by simp [sAtoms, ha], ht⟩
  | .match_ x arms, t, h => by
      obtain ⟨a, ha, ht⟩ := tmpsArms_atoms arms h; exact ⟨a, by simpa [sAtoms] using ha, ht⟩
  | .call .., _, h => by simp [Stmt.tmps] at h
  | .callIf .., _, h => by simp [Stmt.tmps] at h
  | .dispatch .., _, h => by simp [Stmt.tmps] at h
  | .ret _, _, h => by simp [Stmt.tmps] at h

theorem tmpsList_atoms : ∀ (ss : List Stmt) {t : V}, t ∈ Stmt.tmpsList ss → ∃ a ∈ lAtoms ss, t ∈ atomTmps a
  | [], _, h => by simp [Stmt.tmpsList] at h
  | s :: ss, t, h => by
      simp only [Stmt.tmpsList, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨a, ha, ht⟩ := tmps_atoms s h; exact ⟨a, by simp [lAtoms, ha], ht⟩
      · obtain ⟨a, ha, ht⟩ := tmpsList_atoms ss h; exact ⟨a, by simp [lAtoms, ha], ht⟩

theorem tmpsArms_atoms : ∀ (arms : List (List Stmt)) {t : V}, t ∈ Stmt.tmpsArms arms →
    ∃ a ∈ aAtoms arms, t ∈ atomTmps a
  | [], _, h => by simp [Stmt.tmpsArms] at h
  | b :: as, t, h => by
      simp only [Stmt.tmpsArms, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨a, ha, ht⟩ := tmpsList_atoms b h; exact ⟨a, by simp [aAtoms, ha], ht⟩
      · obtain ⟨a, ha, ht⟩ := tmpsArms_atoms as h; exact ⟨a, by simp [aAtoms, ha], ht⟩
end

end Atoms2

/-! ## Cells by number -/

theorem locTrieFrom_lt : ∀ (cs : List ℕ) (k : ℕ) (t : Exec.Trie ℕ) {v : ℕ}, v < k →
    getF (locTrieFrom cs k t) v = getF t v
  | [], _, _, _, _ => rfl
  | c0 :: cs, k, t, v, h => by
    simp only [locTrieFrom, natSeq_eq, Exec.Trie.seq_eq]
    rw [locTrieFrom_lt cs (k + 1) _ (by omega), getF_setF_ne _ _ (by omega)]

theorem locTrieFrom_ge : ∀ (cs : List ℕ) (k : ℕ) (t : Exec.Trie ℕ) {v : ℕ}, k + cs.length ≤ v →
    getF (locTrieFrom cs k t) v = getF t v
  | [], _, _, _, _ => rfl
  | c0 :: cs, k, t, v, h => by
    simp only [locTrieFrom, natSeq_eq, Exec.Trie.seq_eq]
    rw [locTrieFrom_ge cs (k + 1) _ (by simp at h; omega), getF_setF_ne _ _ (by simp at h; omega)]

theorem locTrieFrom_self : ∀ (cs : List ℕ) (k : ℕ) (t : Exec.Trie ℕ) (m : ℕ) (hm : m < cs.length),
    k + cs.length + 1 < 2 ^ indexDepth → getF (locTrieFrom cs k t) (k + m) = some cs[m]
  | [], _, _, _, hm, _ => absurd hm (by simp)
  | c0 :: cs, k, t, 0, _, hb => by
    simp only [locTrieFrom, natSeq_eq, Exec.Trie.seq_eq, List.getElem_cons_zero]
    rw [locTrieFrom_lt cs (k + 1) _ (by omega), Nat.add_zero, getF_setF_self _ _ (by simp at hb; omega)]
  | c0 :: cs, k, t, m + 1, hm, hb => by
    simp only [locTrieFrom, natSeq_eq, Exec.Trie.seq_eq, List.getElem_cons_succ]
    rw [show k + (m + 1) = (k + 1) + m by omega]
    exact locTrieFrom_self cs (k + 1) _ m (by simpa using hm) (by simp at hb ⊢; omega)

/-- **A value's cell by its number**, in the trie of a list of cells. -/
theorem cellOf_locTrie {l : List ℕ} (hl : l.length + 1 < 2 ^ indexDepth) (v : V) :
    cellOf (locTrie l) v = l.getD v.idx 0 := by
  unfold cellOf locTrie
  by_cases hv : v.idx < l.length
  · have := locTrieFrom_self l 0 .nil v.idx hv (by omega)
    rw [Nat.zero_add] at this
    rw [this, List.getD_eq_getElem _ _ hv]; rfl
  · rw [locTrieFrom_ge l 0 .nil (by omega), List.getD_eq_default _ _ (by omega)]; rfl

/-! ## The check of a function -/

section Fn

open LeanVM.Guest.Memory

/-- The cell of a value of function `j`, as the sharing check reads it. -/
noncomputable def cellJ (j : ℕ) (v : V) : ℕ := cellOf (locTrie (certOf j).locs) v

/-- **What the sharing check of function `j` says statically**: its values' cells, its lists, every
atom's temporaries and run listed. -/
theorem shareOk_static {j : ℕ} (h : shareOk j = true) :
    fsN j < 2 ^ envDepth ∧ (certOf j).locs.length + 1 < 2 ^ indexDepth ∧
    (∀ v ∈ (coreOf j).params ++ Stmt.usesList (coreOf j).body ++ Stmt.tmpsList (coreOf j).body,
      valOk (locTrie (certOf j).locs) (plumbOf j) (tmpCells (plumbOf j)) (fpgCells (plumbOf j)) (fsN j) v
        = true) ∧
    listsOk (plumbOf j) (fsN j) = true ∧
    ∀ a ∈ lAtoms (coreOf j).body, atomListed (locTrie (certOf j).locs) (plumbOf j) a = true := by
  simp only [shareOk, Exec.Trie.seq_eq, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq,
    Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, st, h5⟩ := h
  exact ⟨h1, h2, h3, h4, swL_listed _ h5⟩

theorem cellJ_eq {j : ℕ} (h : shareOk j = true) (v : V) : cellJ j v = (certOf j).locs.getD v.idx 0 :=
  cellOf_locTrie (shareOk_static h).2.1 v

/-- **The sharing check's conclusion on a path** of function `j` that returns: one word per cell
for every value the path names, a fixed cell's constant. -/
theorem shareOk_path {j : ℕ} (h : shareOk j = true) {σ : Val} {rd : Reader} {es : List Ev}
    {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs) (he : ∀ e ∈ es, e.Holds rd σ) :
    ∃ Ψ : ℕ → E, (∀ v ∈ (coreOf j).params ++ es.flatMap Ev.uses ++ vs, 2 ≤ cellJ j v →
      σ v = Ψ (cellJ j v)) ∧
      ∀ o a b c, (o, PC.k a b c) ∈ (plumbOf j).stat → Ψ o = OInstr.imm a b c := by
  obtain ⟨hfs, -, hval, hlists, -⟩ := shareOk_static h
  simp only [shareOk, Exec.Trie.seq_eq, Bool.and_eq_true, List.all_eq_true,
    Option.isSome_iff_exists] at h
  obtain ⟨-, st', hst⟩ := h
  set loc := locTrie (certOf j).locs
  set P := plumbOf j
  have hfit : ∀ v ∈ (coreOf j).params ++ Stmt.usesList (coreOf j).body ++ Stmt.tmpsList (coreOf j).body,
      v = V.n v.idx ∧ cellOf loc v + 1 < 2 ^ envDepth := fun v hv ↦ by
    have := hval v hv
    simp only [valOk, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at this
    exact ⟨this.1.1.1, by have := this.1.1.2; omega⟩
  -- the start: the fixed cells' constants
  let Ψ0 : ℕ → E := fun c ↦ match getF (initSt P).occ c with
    | some (some x) => tw x
    | _ => 0
  have hI0 : Inv loc rd σ (initSt P) [] Ψ0 :=
    ⟨(fun _ h ↦ absurd h List.not_mem_nil), (fun _ h ↦ absurd h List.not_mem_nil),
      (fun _ h ↦ absurd h List.not_mem_nil),
      (fun n hn ↦ by simp [isNamed, initSt, getF_eq] at hn),
      (fun c x hx ↦ by simp only [Ψ0, hx]),
      (fun c k hk ↦ by simp [initSt, getF_eq] at hk),
      (fun p hp ↦ by simp [initSt] at hp)⟩
  obtain ⟨Ψ1, hI1, hs1⟩ := nameStep_inv (vs := (coreOf j).params) hI0 (fun v hv ↦ (hfit v (by simp [hv])).1)
    (fun v hv ↦ (hfit v (by simp [hv])).2)
  have hC := swL_sound (coreOf j).body hst hI1 (fun v hv ↦ hfit v (by simp [hv]))
    (by rw [hw]; exact he)
  rw [hw] at hC
  obtain ⟨st'', pre', Ψ', hI', hs', hpe, hpre, hus, hvs⟩ := hC
  have hpe' : st''.pend = [] := by
    rcases hpe with hpe | rfl
    · exact hpe
    · exact swL_pend _ hst
  refine ⟨Ψ', fun v hv hc ↦ ?_, fun o a b c ho ↦ ?_⟩
  · have hv' : v ∈ pre' := by
      simp only [List.mem_append, List.mem_flatMap] at hv
      rcases hv with (hv | ⟨e, he', hv⟩) | hv
      · exact hpre v (List.mem_append_right _ hv)
      · exact hus e he' v hv
      · exact hvs v hv
    exact hI'.good v hv' hc (by simp [isPend, hpe'])
  · simp only [listsOk, Exec.Trie.seq_eq, Bool.and_eq_true, List.all_eq_true] at hlists
    have := (hlists.1.1.1.1.1 _ ho)
    simp only [beq_iff_eq] at this
    have hocc := this.2
    have h0 : Ψ0 o = OInstr.imm a b c := by simp only [Ψ0, hocc]; rfl
    rw [(hs1.trans hs') o (by rw [hocc]; rfl) |>.2, h0]

end Fn

end
end LeanVM.Guest.B2C
