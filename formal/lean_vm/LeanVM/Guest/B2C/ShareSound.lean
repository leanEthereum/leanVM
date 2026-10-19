/-
  LeanVM.Guest.B2C.ShareSound

  Soundness of the sharing check: on every path of a function whose check passes, the values the
  path names at one frame cell hold one word, a fixed cell's constant if it has one.
-/

module

public import LeanVM.Guest.B2C.Share
public import LeanVM.Guest.CheckSound
public import LeanVM.Guest.B2C.Cells

/-!
# Soundness of the sharing check

Along a path, the state of `swL` is read against a word per cell `Ψ` (`Inv`), the values' cells
being the certificate's `cg`: every value named so far and not pending holds its cell's word, the
known constants are the cells' words, the keys hold of them, and the pending values' facts hold.
Naming a value at a cell nothing occupies sets that cell's word (`Ψ` changes only there), so a
join keeps the facts of before the branch for the `Ψ` of the branch taken. The walk reads cells
through a window's `Loc`, which agrees with `cg` on the window's values (`FitV`). A window's end
state refines the next one's snapshot (`refines_inv`), so the windows chain (`chain_sound`); at a
return nothing is pending: every value the path names holds its cell's word (`shareOk_path`).
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

/-! ## Bit sets -/

@[simp] theorem nbeq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h ↦ h ▸ Nat.beq_refl a⟩

theorem bitN_eq (s n : ℕ) : bitN s n = s.testBit n := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  show Nat.beq ((s >>> n) % 2) 1 = _
  rw [Nat.shiftRight_eq_div_pow]
  cases h : Nat.beq (s / 2 ^ n % 2) 1
  · simp only [Bool.false_eq, decide_eq_false_iff_not]
    exact fun h' ↦ by rw [nbeq_iff.mpr h'] at h; cases h
  · exact (decide_eq_true (nbeq_iff.mp h)).symm

theorem testBit_setBit (s n m : ℕ) : (setBit s n).testBit m = (s.testBit m || decide (n = m)) := by
  show (s ||| 1 <<< n).testBit m = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_foldl_setBit {α : Type} (g : α → ℕ) : ∀ (l : List α) (s n : ℕ),
    (l.foldl (fun s x ↦ setBit s (g x)) s).testBit n = true ↔ s.testBit n = true ∨ ∃ x ∈ l, g x = n
  | [], s, n => by simp
  | x :: l, s, n => by
    rw [List.foldl_cons, testBit_foldl_setBit g l, testBit_setBit]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    tauto

theorem testBit_bitsOf (l : List ℕ) (n : ℕ) : (bitsOf l).testBit n = true ↔ n ∈ l := by
  have := testBit_foldl_setBit id l 0 n
  simp only [id, Nat.zero_testBit, Bool.false_eq_true, false_or, exists_eq_right] at this
  exact this

theorem testBit_lor' (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

theorem testBit_land' (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i


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

variable (cg : V → ℕ) (rd : Reader) (σ : Val)

/-- **What the state says** of a path whose values named so far are `pre`, for the cells' words
`Ψ`, the values' cells being `cg`. -/
structure Inv (st : SSt) (pre : List V) (Ψ : ℕ → E) : Prop where
  vn : ∀ v ∈ pre, v = V.n v.idx
  occ : ∀ v ∈ pre, 2 ≤ cg v → st.occ.testBit (cg v)
  good : ∀ v ∈ pre, 2 ≤ cg v → isPend st v.idx = false → σ v = Ψ (cg v)
  named : ∀ n, isNamed st n = true → 2 ≤ cg (V.n n) →
    σ (V.n n) = Ψ (cg (V.n n)) ∧ st.occ.testBit (cg (V.n n))
  kc : ∀ c x, getF st.cst c = some x → st.occ.testBit c ∧ Ψ c = tw x
  keys : ∀ c, ∀ k ∈ (getF st.keys c).getD [], KeyHolds rd (Ψ c) k.1 (k.2.map Ψ) ∧
    st.occ.testBit c ∧ ∀ c' ∈ k.2, st.occ.testBit c'
  pend : ∀ p ∈ st.pend, cg (V.n p.v) = p.c ∧ 2 ≤ p.c ∧ st.occ.testBit p.c ∧
    (∀ x, p.kc = some x → σ (V.n p.v) = tw x) ∧
    (∀ k ∈ p.keys, KeyHolds rd (σ (V.n p.v)) k.1 (k.2.map fun u ↦ σ (V.n u))) ∧
    (∀ x ∈ p.eqs, σ (V.n p.v) = σ (V.n x))

/-- From `st` to `st'`: every occupied cell stays occupied with its word. -/
def Step (st : SSt) (Ψ : ℕ → E) (st' : SSt) (Ψ' : ℕ → E) : Prop :=
  ∀ c, st.occ.testBit c → st'.occ.testBit c ∧ Ψ' c = Ψ c

theorem Step.refl (st : SSt) (Ψ : ℕ → E) : Step st Ψ st Ψ := fun _ h ↦ ⟨h, rfl⟩

theorem Step.trans {st₁ st₂ st₃ : SSt} {Ψ₁ Ψ₂ Ψ₃ : ℕ → E} (h₁ : Step st₁ Ψ₁ st₂ Ψ₂)
    (h₂ : Step st₂ Ψ₂ st₃ Ψ₃) : Step st₁ Ψ₁ st₃ Ψ₃ := fun c hc ↦
  ⟨(h₂ c (h₁ c hc).1).1, (h₂ c (h₁ c hc).1).2.trans (h₁ c hc).2⟩

/-- A step with the occupancy and the words unchanged. -/
theorem Step.of_occ {st st' : SSt} {Ψ : ℕ → E} (h : ∀ c, st.occ.testBit c → st'.occ.testBit c) :
    Step st Ψ st' Ψ := fun c hc ↦ ⟨h c hc, rfl⟩

variable {cg rd σ}

theorem isPend_iff {st : SSt} {v : ℕ} : isPend st v = true ↔ ∃ p ∈ st.pend, p.v = v := by
  simp only [isPend, List.any_eq_true]
  exact exists_congr fun p ↦ and_congr_right fun _ ↦ ⟨Nat.eq_of_beq_eq_true, fun h ↦ h ▸ Nat.beq_refl _⟩

theorem isNamed_eq (st : SSt) (n : ℕ) : isNamed st n = st.named.testBit n := bitN_eq _ _

variable {loc : Loc} {sh : ℕ}

theorem nameV_skip {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {v : V}
    (h : (isNamed st v.idx || isPend st v.idx) = true) : nameV loc sh kc st v = st := by
  unfold nameV; rw [h]; rfl

theorem nameV_low {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {v : V}
    (h : (isNamed st v.idx || isPend st v.idx) = false) (h2 : loc.cell v < 2) :
    nameV loc sh kc st v = ⟨st.occ, st.cst, st.keys, setBit st.named v.idx, st.pend⟩ := by
  unfold nameV; rw [h]; simp only [Bool.cond_false, natSeq_eq, Nat.blt_eq.mpr h2, Bool.cond_true]

theorem nameV_occ {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {v : V}
    (h : (isNamed st v.idx || isPend st v.idx) = false) (h2 : 2 ≤ loc.cell v)
    (ho : st.occ.testBit (loc.cell v) = true) :
    nameV loc sh kc st v = ⟨st.occ, st.cst, st.keys, st.named, ⟨v.idx, loc.cell v, none, [], []⟩ :: st.pend⟩ := by
  have : Nat.blt (loc.cell v) 2 = false :=
    Bool.eq_false_iff.mpr fun hb ↦ absurd (Nat.blt_eq.mp hb) (by omega)
  unfold nameV; rw [h]; simp only [Bool.cond_false, natSeq_eq, this, bitN_eq, ho, Bool.cond_true]

theorem nameV_fresh {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {v : V}
    (h : (isNamed st v.idx || isPend st v.idx) = false) (h2 : 2 ≤ loc.cell v)
    (ho : st.occ.testBit (loc.cell v) = false) :
    nameV loc sh kc st v = ⟨setBit st.occ (loc.cell v), cstAt sh st.cst (loc.cell v) (kc v.idx), st.keys,
      setBit st.named v.idx, st.pend⟩ := by
  have : Nat.blt (loc.cell v) 2 = false :=
    Bool.eq_false_iff.mpr fun hb ↦ absurd (Nat.blt_eq.mp hb) (by omega)
  unfold nameV; rw [h]; simp only [Bool.cond_false, natSeq_eq, this, bitN_eq, ho]

theorem getF_cstAt {cst : Exec.Trie (ℕ × ℕ × ℕ)} {c c' : ℕ} {k : Option (ℕ × ℕ × ℕ)} {x : ℕ × ℕ × ℕ}
    (h : getF (cstAt sh cst c k) c' = some x) : (c' = c ∧ k = some x) ∨ getF cst c' = some x := by
  cases k with
  | none => exact Or.inr h
  | some y =>
    simp only [cstAt, Bool.cond_eq_ite] at h
    split_ifs at h
    · rcases getF_setF h with ⟨h1, rfl⟩ | h
      · exact Or.inl ⟨h1, rfl⟩
      · exact Or.inr h
    · exact Or.inr h

/-- **Naming a value** keeps the invariant: `Ψ` changes only at a cell nothing occupied. -/
theorem nameV_inv {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {pre : List V} {Ψ : ℕ → E} {v : V}
    (hI : Inv cg rd σ st pre Ψ) (hv : v = V.n v.idx) (hcg : loc.cell v = cg v)
    (hkc : ∀ x, kc v.idx = some x → σ v = tw x) :
    ∃ Ψ', Inv cg rd σ (nameV loc sh kc st v) (pre ++ [v]) Ψ' ∧ Step st Ψ (nameV loc sh kc st v) Ψ' := by
  have hvn : ∀ u ∈ pre ++ [v], u = V.n u.idx := fun u hu ↦ by
    rcases List.mem_append.mp hu with hu | hu
    · exact hI.vn u hu
    · rw [List.mem_singleton.mp hu]; exact hv
  have hcv : cg (V.n v.idx) = cg v := by rw [← hv]
  cases hnp : (isNamed st v.idx || isPend st v.idx)
  · -- a value not named before
    have hnp' := hnp
    simp only [Bool.or_eq_false_iff] at hnp'
    obtain ⟨hn, hp⟩ := hnp'
    by_cases h2 : loc.cell v < 2
    · rw [nameV_low hnp h2]
      refine ⟨Ψ, ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_, fun n hn' hc ↦ ?_, hI.kc, hI.keys, hI.pend⟩,
        Step.refl _ _⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hI.occ u hu hc
        · rw [List.mem_singleton.mp hu] at hc; omega
      · rcases List.mem_append.mp hu with hu | hu
        · exact hI.good u hu hc hpe
        · rw [List.mem_singleton.mp hu] at hc; omega
      · simp only [isNamed_eq, testBit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hn'
        rcases hn' with hn' | rfl
        · exact hI.named n (by rw [isNamed_eq]; exact hn') hc
        · rw [hcv] at hc; omega
    · have h2' : 2 ≤ loc.cell v := by omega
      cases ho : st.occ.testBit (loc.cell v)
      · -- the first value at its cell
        rw [nameV_fresh hnp h2' ho]
        have ho' : st.occ.testBit (cg v) = false := by rw [← hcg]; exact ho
        have hne : ∀ c', st.occ.testBit c' = true → c' ≠ cg v := fun c' h he ↦ by
          rw [he, ho'] at h; cases h
        refine ⟨Function.update Ψ (cg v) (σ v), ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_,
          fun n hn' hc ↦ ?_, fun c x hx ↦ ?_, fun c k hk ↦ ?_, fun p hp ↦ ?_⟩, fun c hc ↦ ?_⟩
        · rw [testBit_setBit, Bool.or_eq_true, decide_eq_true_eq]
          rcases List.mem_append.mp hu with hu | hu
          · exact Or.inl (hI.occ u hu hc)
          · rw [List.mem_singleton.mp hu, hcg]; exact Or.inr rfl
        · rcases List.mem_append.mp hu with hu | hu
          · rw [Function.update_of_ne (hne _ (hI.occ u hu hc))]
            exact hI.good u hu hc hpe
          · rw [List.mem_singleton.mp hu, Function.update_self]
        · simp only [isNamed_eq, testBit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hn'
          rcases hn' with hn' | rfl
          · obtain ⟨h1, h3⟩ := hI.named n (by rw [isNamed_eq]; exact hn') hc
            rw [Function.update_of_ne (hne _ h3), testBit_setBit, h3, Bool.true_or]
            exact ⟨h1, rfl⟩
          · rw [hcv, ← hv, Function.update_self, testBit_setBit, hcg]
            simp
        · rcases getF_cstAt hx with ⟨rfl, hk⟩ | hx
          · rw [hcg, testBit_setBit, Function.update_self]
            exact ⟨by simp, hkc x hk⟩
          · obtain ⟨h1, h3⟩ := hI.kc c x hx
            rw [testBit_setBit, h1, Bool.true_or, Function.update_of_ne (hne c h1)]
            exact ⟨rfl, h3⟩
        · obtain ⟨h1, h3, h4⟩ := hI.keys c k hk
          rw [Function.update_of_ne (hne c h3), testBit_setBit, h3, Bool.true_or]
          refine ⟨?_, rfl, fun c' hc' ↦ by rw [testBit_setBit, h4 c' hc', Bool.true_or]⟩
          have : k.2.map (Function.update Ψ (cg v) (σ v)) = k.2.map Ψ :=
            List.map_congr_left fun c' hc' ↦ Function.update_of_ne (hne c' (h4 c' hc')) _ _
          rw [this]; exact h1
        · obtain ⟨h1, h3, h4, h5⟩ := hI.pend p hp
          exact ⟨h1, h3, by rw [testBit_setBit, h4, Bool.true_or], h5⟩
        · exact ⟨by rw [testBit_setBit, hc, Bool.true_or], Function.update_of_ne (hne c hc) _ _⟩
      · -- pending
        rw [nameV_occ hnp h2' ho]
        refine ⟨Ψ, ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_, hI.named, hI.kc, hI.keys, ?_⟩,
          Step.refl _ _⟩
        · rcases List.mem_append.mp hu with hu | hu
          · exact hI.occ u hu hc
          · rw [List.mem_singleton.mp hu, ← hcg]; exact ho
        · rcases List.mem_append.mp hu with hu | hu
          · refine hI.good u hu hc ?_
            simp only [isPend, List.any_cons, Bool.or_eq_false_iff] at hpe ⊢
            exact hpe.2
          · rw [List.mem_singleton.mp hu] at hpe
            simp [isPend] at hpe
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨by rw [hcv, hcg], h2', ho, (fun _ h ↦ by cases h), (fun _ h ↦ by cases h),
              (fun _ h ↦ by cases h)⟩
          · exact hI.pend p hp
  · -- named or pending already
    rw [nameV_skip hnp]
    refine ⟨Ψ, ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_, hI.named, hI.kc, hI.keys, hI.pend⟩,
      Step.refl _ _⟩
    · rcases List.mem_append.mp hu with hu | hu
      · exact hI.occ u hu hc
      · rw [List.mem_singleton.mp hu] at hc ⊢
        rcases Bool.or_eq_true_iff.mp hnp with hn | hp
        · rw [← hcv] at hc ⊢; exact (hI.named _ hn hc).2
        · obtain ⟨p, hp, hpv⟩ := isPend_iff.mp hp
          obtain ⟨h1, -, h3, -⟩ := hI.pend p hp
          rw [← hcv, ← hpv, h1]; exact h3
    · rcases List.mem_append.mp hu with hu | hu
      · exact hI.good u hu hc hpe
      · rw [List.mem_singleton.mp hu] at hc hpe ⊢
        rw [hpe, Bool.or_false] at hnp
        rw [← hcv] at hc ⊢
        rw [hv]; exact (hI.named _ hnp hc).1

end Inv

/-- Values named by their numbers whose window cells are their cells. -/
def FitV (loc : Loc) (cg : V → ℕ) (vs : List V) : Prop :=
  ∀ v ∈ vs, v = V.n v.idx ∧ loc.cell v = cg v

theorem FitV.mono {loc : Loc} {cg : V → ℕ} {vs ws : List V} (h : FitV loc cg ws) (hs : ∀ v ∈ vs, v ∈ ws) :
    FitV loc cg vs :=
  fun v hv ↦ h v (hs v hv)

/-- A window's cells are the values' cells, wherever it has one. -/
def LocAgree (loc : Loc) (cg : V → ℕ) : Prop := ∀ v, 2 ≤ loc.cell v → loc.cell v = cg v

section Steps

variable {loc : Loc} {sh : ℕ} {cg : V → ℕ} {rd : Reader} {σ : Val}

theorem nameAll_inv {kc : ℕ → Option (ℕ × ℕ × ℕ)} : ∀ (vs : List V) {st : SSt} {pre : List V}
    {Ψ : ℕ → E}, Inv cg rd σ st pre Ψ → FitV loc cg vs → (∀ v ∈ vs, ∀ x, kc v.idx = some x → σ v = tw x) →
    ∃ Ψ', Inv cg rd σ (nameAll loc sh kc st vs) (pre ++ vs) Ψ' ∧ Step st Ψ (nameAll loc sh kc st vs) Ψ'
  | [], st, pre, Ψ, hI, _, _ => ⟨Ψ, by simpa [nameAll] using hI, by simpa [nameAll] using Step.refl st Ψ⟩
  | v :: vs, st, pre, Ψ, hI, hf, hk => by
    simp only [nameAll, SSt.seq_eq]
    obtain ⟨hv, hc⟩ := hf v List.mem_cons_self
    obtain ⟨Ψ1, hI1, hs1⟩ := nameV_inv (sh := sh) hI hv hc (hk v List.mem_cons_self)
    obtain ⟨Ψ2, hI2, hs2⟩ := nameAll_inv vs hI1 (hf.mono fun u hu ↦ List.mem_cons_of_mem _ hu)
      fun u hu ↦ hk u (List.mem_cons_of_mem _ hu)
    exact ⟨Ψ2, by simpa using hI2, hs1.trans hs2⟩


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
    isPend ⟨st.occ, st.cst, st.keys, st.named, addFacts a st.pend⟩ v = isPend st v := by
  simp only [isPend, addFacts, List.any_map]
  rfl

/-- **An atom's facts** about the pending values hold. -/
theorem addFacts_inv {a : Core.Atom} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : Inv cg rd σ st pre Ψ) (ha : a.Holds rd σ) (hvn : VnA a) :
    Inv cg rd σ ⟨st.occ, st.cst, st.keys, st.named, addFacts a st.pend⟩ pre Ψ := by
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
theorem pfOk_sound (hA : LocAgree loc cg) {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : Inv cg rd σ st pre Ψ) {p : PF} (hp : p ∈ st.pend) (h : pfOk loc st p = true) :
    σ (V.n p.v) = Ψ p.c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.pend p hp
  simp only [pfOk, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with (h | ⟨k, hk, hok⟩) | ⟨x, hx, hok⟩
  · cases hkc : p.kc with
    | none => rw [hkc] at h; simp at h
    | some x =>
      rw [hkc] at h
      cases ho : getF st.cst p.c with
      | none => rw [ho] at h; simp at h
      | some y =>
        rw [ho] at h
        simp only [beq_iff_eq] at h
        subst h
        rw [h4 x hkc, (hI.kc p.c x ho).2]
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
      have hc : cellN loc u = cg (V.n u) := hA _ this.2
      rw [Function.comp_apply, hc]
      exact ((hI.named u this.1 (hc ▸ this.2)).1).symm
    rw [hmap] at hK
    exact (h5 k hk).unique hK
  · simp only [Bool.and_eq_true, nbeq_iff] at hok
    obtain ⟨hn, hc⟩ := hok
    have hc' : cellN loc x = cg (V.n x) := hA _ (show 2 ≤ cellN loc x by rw [hc]; exact h2)
    rw [h6 x hx, ← hc, hc']
    exact (hI.named x hn (by rw [← hc', hc]; exact h2)).1


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


theorem testBit_foldl_pf (ps : List PF) (s n : ℕ) :
    (ps.foldl (fun s p ↦ setBit s p.v) s).testBit n = true → (∃ p ∈ ps, p.v = n) ∨ s.testBit n = true := by
  intro h
  rcases (testBit_foldl_setBit (fun p : PF ↦ p.v) ps s n).mp h with h | ⟨p, hp, he⟩
  · exact Or.inr h
  · exact Or.inl ⟨p, hp, he⟩

/-- **Showing pending values** keeps the invariant. -/
theorem discharge_inv (hA : LocAgree loc cg) : ∀ (n : ℕ) {st : SSt} {pre : List V} {Ψ : ℕ → E},
    Inv cg rd σ st pre Ψ → Inv cg rd σ (discharge loc n st) pre Ψ ∧ (discharge loc n st).occ = st.occ
  | 0, st, pre, Ψ, hI => ⟨hI, rfl⟩
  | n + 1, st, pre, Ψ, hI => by
    simp only [discharge]
    rcases hs : splitPend loc st st.pend with ⟨ok, rest⟩
    obtain ⟨h1, h2, h3⟩ := splitPend_spec st st.pend hs
    cases ok with
    | nil => exact ⟨hI, rfl⟩
    | cons p ok =>
      simp only [natSeq_eq, SSt.seq_eq]
      have hokv : ∀ q ∈ p :: ok, σ (V.n q.v) = Ψ q.c := fun q hq ↦
        pfOk_sound hA hI (h1 q hq).1 (h1 q hq).2
      refine (discharge_inv hA n ?_).imp id (fun h ↦ h)
      refine ⟨hI.vn, hI.occ, fun u hu hc hpe ↦ ?_, fun m hm hc ↦ ?_, hI.kc, hI.keys,
        fun q hq ↦ hI.pend q (h2 q hq)⟩
      · by_cases hold : isPend st u.idx = true
        · obtain ⟨q, hq, hqv⟩ := isPend_iff.mp hold
          rcases h3 q hq with hq' | hq'
          · obtain ⟨e1, -⟩ := hI.pend q hq
            rw [hI.vn u hu, ← hqv, hokv q hq', ← e1]
          · have : isPend ⟨st.occ, st.cst, st.keys, (p :: ok).foldl (fun s p ↦ setBit s p.v) st.named,
                rest⟩ u.idx = true := isPend_iff.mpr ⟨q, hq', hqv⟩
            rw [hpe] at this; cases this
        · exact hI.good u hu hc (by simpa using hold)
      · rw [isNamed_eq] at hm
        rcases testBit_foldl_pf _ _ _ hm with ⟨q, hq, rfl⟩ | hm
        · obtain ⟨e1, -, e3, -⟩ := hI.pend q (h1 q hq).1
          rw [e1]
          exact ⟨hokv q hq, e3⟩
        · exact hI.named m (by rw [isNamed_eq]; exact hm) hc

end Steps


section Record

variable {loc : Loc} {sh : ℕ} {cg : V → ℕ} {rd : Reader} {σ : Val}

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
      c = loc.cell out ∧ ins = keyCells op (insV.map loc.cell) ∧
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
    k ∈ (getF (ks.foldl (fun t k ↦ bif Nat.ble 2 k.1 && bitN sh k.1 && k.2.2.all (Nat.ble 2) then
      setF ((k.2.1, k.2.2) :: (getF t k.1).getD []) envDepth t k.1 else t) t) c).getD [] →
    k ∈ (getF t c).getD [] ∨ ((c, k.1, k.2) ∈ ks ∧ 2 ≤ c ∧ ∀ c' ∈ k.2, 2 ≤ c')
  | [], t, c, k, h => Or.inl h
  | k0 :: ks, t, c, k, h => by
    rcases mem_foldl_keys ks _ c k h with h | ⟨h1, h2, h3⟩
    · cases hb : (Nat.ble 2 k0.1 && bitN sh k0.1 && k0.2.2.all (Nat.ble 2))
      · simp only [hb, Bool.cond_false] at h; exact Or.inl h
      · simp only [hb, Bool.cond_true] at h
        simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at hb
        cases hg : getF (setF ((k0.2.1, k0.2.2) :: (getF t k0.1).getD []) envDepth t k0.1) c with
        | none => rw [hg] at h; cases h
        | some l =>
          rw [hg] at h
          rcases getF_setF hg with ⟨rfl, rfl⟩ | hg'
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr ⟨List.mem_cons_self, hb.1.1, hb.2⟩
            · exact Or.inl h
          · rw [hg']; exact Or.inl h
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2, h3⟩

theorem getF_recCst {a : Core.Atom} {cst : Exec.Trie (ℕ × ℕ × ℕ)} {c : ℕ} {x : ℕ × ℕ × ℕ}
    (h : getF (recCst loc sh a cst) c = some x) : getF cst c = some x ∨
      (getF cst c = none ∧ 2 ≤ c ∧ ((∃ d y, a = .const d y ∧ c = loc.cell d ∧
        x = (limbNat y 0, limbNat y 1, limbNat y 2)) ∨
        ∃ u i p, a = .assertNe u i p ∧ c = loc.cell p ∧ x = (1, 0, 0))) := by
  unfold recCst at h
  cases a with
  | const d y =>
    simp only at h
    cases h0 : getF cst (loc.cell d) with
    | some _ => rw [h0] at h; exact Or.inl h
    | none =>
      rw [h0] at h
      simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.ble_eq] at h
      split_ifs at h with hc
      · rcases getF_setF h with ⟨rfl, rfl⟩ | h
        · exact Or.inr ⟨h0, hc.1, Or.inl ⟨d, y, rfl, rfl, rfl⟩⟩
        · exact Or.inl h
      · exact Or.inl h
  | assertNe u i p =>
    simp only at h
    cases h0 : getF cst (loc.cell p) with
    | some _ => rw [h0] at h; exact Or.inl h
    | none =>
      rw [h0] at h
      simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.ble_eq] at h
      split_ifs at h with hc
      · rcases getF_setF h with ⟨rfl, rfl⟩ | h
        · exact Or.inr ⟨h0, hc.1, Or.inr ⟨u, i, p, rfl, rfl, rfl⟩⟩
        · exact Or.inl h
      · exact Or.inl h
  | _ => exact Or.inl h

/-- **Recording an atom's cell facts** keeps the invariant. -/
theorem record_inv {a : Core.Atom} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : Inv cg rd σ st pre Ψ) (ha : a.Holds rd σ) (hvn : VnA a)
    (hfit : FitV loc cg (Memory.atomUses a)) :
    Inv cg rd σ (record loc sh a st) pre Ψ ∧ Step st Ψ (record loc sh a st) Ψ := by
  unfold record
  cases hall : (Memory.atomUses a).all fun v ↦ isNamed st v.idx
  · rw [Bool.cond_false]; exact ⟨hI, Step.refl _ _⟩
  rw [Bool.cond_true]
  simp only [List.all_eq_true] at hall
  -- every value of the atom holds its cell's word, its cell occupied
  have hval : ∀ u ∈ Memory.atomUses a, 2 ≤ loc.cell u →
      σ u = Ψ (loc.cell u) ∧ st.occ.testBit (loc.cell u) := fun u hu hc ↦ by
    obtain ⟨hv, hcg⟩ := hfit u hu
    have hcv : cg (V.n u.idx) = loc.cell u := by rw [← hv, hcg]
    have := hI.named u.idx (hall u hu) (by rw [hcv]; exact hc)
    rw [hcv, ← hv] at this
    exact this
  refine ⟨⟨hI.vn, hI.occ, hI.good, hI.named, fun c x hx ↦ ?_, fun c k hk ↦ ?_, hI.pend⟩,
    Step.refl _ _⟩
  · rcases getF_recCst hx with hx | ⟨-, hc2, ⟨d, y, rfl, rfl, rfl⟩ | ⟨u, i, p, rfl, rfl, rfl⟩⟩
    · exact hI.kc c x hx
    · have hdv := hval d (by simp [Memory.atomUses]) hc2
      refine ⟨hdv.2, ?_⟩
      rw [← hdv.1, tw_limbs]; exact ha
    · have hpv := hval p (by simp [Memory.atomUses]) hc2
      refine ⟨hpv.2, ?_⟩
      rw [← hpv.1, tw_one]; exact ha.2
  · rcases mem_foldl_keys _ _ c k hk with hk | ⟨hk, hc2, hins⟩
    · exact hI.keys c k hk
    · obtain ⟨out, hout, insV, hinsV, rfl, hins', hK⟩ := cellKeys_sound ha hk
      have hcell : ∀ c' ∈ k.2, ∃ u ∈ insV, c' = loc.cell u := fun c' hc' ↦ by
        rw [hins', mem_keyCells] at hc'
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc'
        exact ⟨u, hu, rfl⟩
      have hmap : insV.map σ = (insV.map loc.cell).map Ψ := by
        rw [List.map_map]
        refine List.map_congr_left fun u hu ↦ ?_
        exact (hval u (hinsV u hu) (hins _ (by rw [hins', mem_keyCells]; exact List.mem_map_of_mem hu))).1
      rw [hmap, (hval out hout hc2).1, ← keyHolds_keyCells, ← hins'] at hK
      refine ⟨hK, (hval out hout hc2).2, fun c' hc' ↦ ?_⟩
      obtain ⟨u, hu, rfl⟩ := hcell c' hc'
      exact (hval u (hinsV u hu) (hins _ hc')).2

end Record

section Atoms

variable {loc : Loc} {sh : ℕ} {cg : V → ℕ} {rd : Reader} {σ : Val}

/-- **An atom on the path** keeps the invariant, its values named. -/
theorem stepAtom_inv (hA : LocAgree loc cg) {a : Core.Atom} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : Inv cg rd σ st pre Ψ) (ha : a.Holds rd σ) (hfit : FitV loc cg (Memory.atomUses a)) :
    ∃ Ψ', Inv cg rd σ (stepAtom loc sh st a) (pre ++ Memory.atomUses a) Ψ' ∧
      Step st Ψ (stepAtom loc sh st a) Ψ' := by
  have hvn : VnA a := fun u hu ↦ (hfit u hu).1
  unfold stepAtom
  simp only [SSt.seq_eq]
  obtain ⟨Ψ1, hI1, hs1⟩ := nameAll_inv (sh := sh) (kc := constOf a) (Memory.atomUses a) hI hfit
    fun v hv x hx ↦ by rw [hvn v hv]; exact constOf_sound ha hvn hx
  have hI2 := addFacts_inv hI1 ha hvn
  obtain ⟨hI3, ho3⟩ := discharge_inv hA (_ + 1) hI2
  obtain ⟨hI4, hs4⟩ := record_inv (sh := sh) hI3 ha hvn hfit
  refine ⟨Ψ1, hI4, hs1.trans ((Step.of_occ fun c h ↦ ?_).trans hs4)⟩
  rw [ho3]; exact h

/-- **Other values named** keep the invariant. -/
theorem nameStep_inv (hA : LocAgree loc cg) {vs : List V} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : Inv cg rd σ st pre Ψ) (hfit : FitV loc cg vs) :
    ∃ Ψ', Inv cg rd σ (nameStep loc sh st vs) (pre ++ vs) Ψ' ∧ Step st Ψ (nameStep loc sh st vs) Ψ' := by
  unfold nameStep
  simp only [SSt.seq_eq]
  obtain ⟨Ψ1, hI1, hs1⟩ := nameAll_inv (sh := sh) (kc := fun _ ↦ none) vs hI hfit
    fun v hv x hx ↦ by cases hx
  obtain ⟨hI2, ho2⟩ := discharge_inv hA (_ + 1) hI1
  refine ⟨Ψ1, hI2, hs1.trans (Step.of_occ fun c h ↦ ?_)⟩
  rw [ho2]; exact h

end Atoms

/-! ## Joins -/

section Join

theorem testBit_foldl_lor (bs : List SSt) (s c : ℕ) :
    (bs.foldl (fun o b ↦ Nat.lor o b.occ) s).testBit c = true ↔ s.testBit c = true ∨ ∃ b ∈ bs, b.occ.testBit c = true := by
  induction bs generalizing s with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, testBit_lor']
    simp only [Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    tauto

theorem testBit_foldl_land (bs : List SSt) (s n : ℕ) :
    (bs.foldl (fun t b ↦ Nat.land t b.named) s).testBit n = true → s.testBit n = true ∧ ∀ b ∈ bs, b.named.testBit n = true := by
  induction bs generalizing s with
  | nil => simp
  | cons b bs ih =>
    intro h
    rw [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := ih _ h
    rw [testBit_land', Bool.and_eq_true] at h1
    exact ⟨h1.1, fun b' hb' ↦ by
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact h1.2
      · exact h2 b' hb'⟩

variable {cg : V → ℕ} {rd : Reader} {σ : Val}

/-- **After a join**, for the branch taken: the facts from before the branch, with the branch's
cell words. -/
theorem joinSt_inv {st1 b : SSt} {bs : List SSt} {pre1 preb : List V} {Ψ1 Ψb : ℕ → E}
    (hI1 : Inv cg rd σ st1 pre1 Ψ1) (hIb : Inv cg rd σ b preb Ψb) (hs : Step st1 Ψ1 b Ψb)
    (hb : b ∈ bs) (hp : b.pend = []) :
    Inv cg rd σ (joinSt st1 bs) preb Ψb ∧ Step st1 Ψ1 (joinSt st1 bs) Ψb := by
  have hsome : ∀ c, b.occ.testBit c = true → (joinSt st1 bs).occ.testBit c = true := fun c h ↦
    (testBit_foldl_lor bs st1.occ c).mpr (Or.inr ⟨b, hb, h⟩)
  have hsome1 : ∀ c, st1.occ.testBit c = true → (joinSt st1 bs).occ.testBit c = true := fun c h ↦
    (testBit_foldl_lor bs st1.occ c).mpr (Or.inl h)
  refine ⟨⟨hIb.vn, fun u hu hc ↦ hsome _ (hIb.occ u hu hc), fun u hu hc _ ↦ ?_, fun n hn hc ↦ ?_,
    fun c x hx ↦ ?_, fun c k hk ↦ ?_, fun p hp' ↦ by simp [joinSt] at hp'⟩,
    fun c hc ↦ ⟨hsome1 c hc, (hs c hc).2⟩⟩
  · exact hIb.good u hu hc (by simp [isPend, hp])
  · have hnb : isNamed b n = true := by
      rw [isNamed_eq] at hn ⊢
      simp only [joinSt] at hn
      cases bs with
      | nil => cases hb
      | cons b0 bs' =>
        obtain ⟨h1, h2⟩ := testBit_foldl_land bs' b0.named n hn
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact h1
        · exact h2 b hb'
    exact ⟨(hIb.named n hnb hc).1, hsome _ (hIb.named n hnb hc).2⟩
  · obtain ⟨h1, h2⟩ := hI1.kc c x hx
    exact ⟨hsome1 c h1, by rw [(hs c h1).2]; exact h2⟩
  · obtain ⟨h1, h2, h3⟩ := hI1.keys c k hk
    refine ⟨?_, hsome1 c h2, fun c' hc' ↦ hsome1 c' (h3 c' hc')⟩
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

variable {loc : Loc} {sh : ℕ} {tt : Exec.Trie ℕ} {P : Plumb} {cg : V → ℕ} {rd : Reader} {σ : Val}


/-- What a walk gives of an outcome: at a fall-through, the end state with the path's values named;
at a return, a state with every value named and nothing pending (or the end state itself). -/
def Conc (cg : V → ℕ) (rd : Reader) (σ : Val) (st : SSt) (Ψ : ℕ → E) (pre : List V)
    (st' : SSt) : Out → Prop
  | .fall es => ∃ pre' Ψ', Inv cg rd σ st' pre' Ψ' ∧ Step st Ψ st' Ψ' ∧ (∀ v ∈ pre, v ∈ pre') ∧
      ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ pre'
  | .ret es vs => ∃ st'' pre' Ψ', Inv cg rd σ st'' pre' Ψ' ∧ Step st Ψ st'' Ψ' ∧
      (st''.pend = [] ∨ st'' = st') ∧
      (∀ v ∈ pre, v ∈ pre') ∧ (∀ e ∈ es, ∀ v ∈ e.uses, v ∈ pre') ∧ ∀ v ∈ vs, v ∈ pre'
  | .stuck => True

/-- Names `vs` after `pre`: a fall-through naming `vs`. -/
theorem conc_names {st st' : SSt} {Ψ Ψ' : ℕ → E} {pre vs : List V} {es : List Ev}
    (hI : Inv cg rd σ st' (pre ++ vs) Ψ') (hs : Step st Ψ st' Ψ')
    (hu : ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ vs) : Conc cg rd σ st Ψ pre st' (.fall es) :=
  ⟨pre ++ vs, Ψ', hI, hs, fun _ hv ↦ List.mem_append_left _ hv,
    fun e he v hv ↦ List.mem_append_right _ (hu e he v hv)⟩

/-- A statement's outcome followed by the rest of its block's. -/
theorem conc_seq {st st1 st' : SSt} {Ψ : ℕ → E} {pre : List V} {o1 o2 : Out}
    (h1 : Conc cg rd σ st Ψ pre st1 o1)
    (h2 : ∀ es1, o1 = .fall es1 → ∀ pre1 Ψ1, Inv cg rd σ st1 pre1 Ψ1 → Step st Ψ st1 Ψ1 →
      (∀ v ∈ pre, v ∈ pre1) → Conc cg rd σ st1 Ψ1 pre1 st' o2)
    (hr : ∀ es vs, o1 = .ret es vs → st1.pend = []) : Conc cg rd σ st Ψ pre st' (o1.seq o2) := by
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
theorem swL_pend : ∀ (ss : List Stmt) {st st' : SSt}, swL loc sh tt P st ss = some st' → st'.pend = []
  | [], st, st', h => by
    simp only [swL, Bool.cond_eq_ite] at h
    split_ifs at h with hp
    cases h; exact List.isEmpty_iff.mp hp
  | s :: ss, st, st', h => by
    simp only [swL] at h
    cases hs : swS loc sh tt P st s with
    | none => rw [hs] at h; cases h
    | some st1 =>
      rw [hs] at h
      simp only [SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h
      exact swL_pend ss h

/-- A conclusion for the values `vs` named first, before the events `es`. -/
theorem conc_pre {st st' : SSt} {Ψ : ℕ → E} {pre vs : List V} {es : List Ev} {o : Out}
    (h : Conc cg rd σ st Ψ (pre ++ vs) st' o) (hu : ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ vs) :
    Conc cg rd σ st Ψ pre st' (o.pre es) := by
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
    (h : Conc cg rd σ st Ψ (pre ++ vs) st' o) : Conc cg rd σ st Ψ pre st' o := by
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
    (hI1 : Inv cg rd σ st1 pre1 Ψ1) (hs1 : Step st Ψ st1 Ψ1) (hb : b ∈ bs)
    (hC : Conc cg rd σ st1 Ψ1 pre1 b o) (hp : b.pend = []) :
    Conc cg rd σ st Ψ pre1 (joinSt st1 bs) o := by
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

theorem pick_cases_sh {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ),
    pick σ x args rets j fs = .stuck ∨ ∃ g, pick σ x args rets j fs = .fall [.call g args rets]
  | [], _ => Or.inl (by simp [pick])
  | f :: fs, j => by
    unfold pick
    split_ifs
    · exact Or.inr ⟨f, rfl⟩
    · exact pick_cases_sh fs (j + 1)

theorem seq_evs {o1 o2 : Out} (h : o1.seq o2 ≠ .stuck) :
    (∀ e ∈ o1.evs, e ∈ (o1.seq o2).evs) ∧ ∀ es1, o1 = .fall es1 → ∀ e ∈ o2.evs, e ∈ (o1.seq o2).evs := by
  cases o1 <;> cases o2 <;> simp_all [Out.seq, Out.pre, Out.evs]

mutual
/-- **One statement**: what the walk gives of its outcome on a path. -/
theorem swS_sound (hA : LocAgree loc cg) : ∀ (s : Stmt) {st st' : SSt} {pre : List V} {Ψ : ℕ → E},
    swS loc sh tt P st s = some st' → Inv cg rd σ st pre Ψ → FitV loc cg (Stmt.uses s) →
    (∀ e ∈ (walk1 σ s).evs, e.Holds rd σ) → Conc cg rd σ st Ψ pre st' (walk1 σ s)
  | .atom a, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swS, Bool.cond_eq_ite] at h
      split_ifs at h
      cases h
      have ha : a.Holds rd σ := he (.atom a) (by simp [walk1, Out.evs])
      obtain ⟨Ψ', hI', hs⟩ := stepAtom_inv hA hI ha hv
      refine conc_names hI' hs fun e he' v hv' ↦ ?_
      simp only [List.mem_singleton] at he'
      subst he'
      exact hv'
  | .ite c z n, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h with hp
      cases hz : swL loc sh tt P (nameStep loc sh st [c]) z <;> cases hn : swL loc sh tt P (nameStep loc sh st [c]) n <;>
        rw [hz, hn] at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i sz sn
      have hc := hv c List.mem_cons_self
      obtain ⟨Ψ1, hI1, hs1⟩ := nameStep_inv hA hI (fun u hu ↦ by rw [List.mem_singleton.mp hu]; exact hc)
      have hu : ∀ e ∈ [Ev.inK c], ∀ v ∈ e.uses, v ∈ [c] := fun e he v hv ↦ by
        simp only [List.mem_singleton] at he; subst he; exact hv
      simp only [walk1] at he ⊢
      by_cases hc0 : σ c = 0
      · simp only [hc0, ↓reduceIte] at he ⊢
        refine conc_pre (conc_join hI1 hs1 List.mem_cons_self ?_ (swL_pend z hz)) hu
        exact swL_sound hA z hz hI1 (hv.mono fun v hv ↦ by simp [Stmt.uses, hv])
          fun e he' ↦ he e (evs_pre he')
      · simp only [hc0, ↓reduceIte] at he ⊢
        refine conc_pre (conc_join hI1 hs1 (by simp) ?_ (swL_pend n hn)) hu
        exact swL_sound hA n hn hI1 (hv.mono fun v hv ↦ by simp [Stmt.uses, hv])
          fun e he' ↦ he e (evs_pre he')
  | .match_ x arms, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h with hp
      cases ha : swArms loc sh tt P (nameStep loc sh st [x]) arms <;> rw [ha] at h <;>
        simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i bs
      have hx := hv x List.mem_cons_self
      obtain ⟨Ψ1, hI1, hs1⟩ := nameStep_inv hA hI (fun u hu ↦ by rw [List.mem_singleton.mp hu]; exact hx)
      simp only [walk1] at he ⊢
      rcases swArms_sound hA x arms 0 ha hI1 (hv.mono fun v hv ↦ by simp [Stmt.uses, hv]) he with
        hst | ⟨b, hb, hC, hbp⟩
      · rw [hst]; trivial
      · exact conc_shrink (conc_join hI1 hs1 hb hC hbp)
  | .call f args rets, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStep_inv hA hI hv
      refine conc_names hI' hs fun e he' v hv' ↦ ?_
      simp only [List.mem_singleton] at he'
      subst he'
      simpa [Ev.uses, Stmt.uses] using hv'
  | .callIf c f args, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStep_inv hA hI hv
      refine conc_names hI' hs fun e he' v hv' ↦ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl
      · simp only [Ev.uses, List.mem_singleton] at hv'
        simp [Stmt.uses, hv']
      · split_ifs at hv' <;> simp_all [Ev.uses, Stmt.uses]
  | .dispatch x fs args rets, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStep_inv hA hI hv
      simp only [walk1]
      rcases pick_cases_sh (σ := σ) (x := x) (args := args) (rets := rets) fs 0 with hp | ⟨g, hp⟩
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
      obtain ⟨Ψ', hI', hs⟩ := nameStep_inv hA hI hv
      simp only [walk1]
      exact ⟨nameStep loc sh st (stmtNames (.ret vs)), pre ++ stmtNames (.ret vs), Ψ', hI', hs, Or.inr rfl,
        fun _ hv ↦ List.mem_append_left _ hv, fun e he ↦ absurd he List.not_mem_nil,
        fun v hv ↦ List.mem_append_right _ hv⟩

/-- **A block**: what the walk gives of its outcome on a path. -/
theorem swL_sound (hA : LocAgree loc cg) : ∀ (ss : List Stmt) {st st' : SSt} {pre : List V} {Ψ : ℕ → E},
    swL loc sh tt P st ss = some st' → Inv cg rd σ st pre Ψ → FitV loc cg (Stmt.usesList ss) →
    (∀ e ∈ (walk σ ss).evs, e.Holds rd σ) → Conc cg rd σ st Ψ pre st' (walk σ ss)
  | [], st, st', pre, Ψ, h, hI, _, _ => by
      simp only [swL, Bool.cond_eq_ite] at h
      split_ifs at h
      cases h
      exact ⟨pre, Ψ, hI, Step.refl _ _, fun _ hv ↦ hv, fun e he ↦ by simp at he⟩
  | s :: ss, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swL] at h
      cases hs : swS loc sh tt P st s with
      | none => rw [hs] at h; cases h
      | some st1 =>
        rw [hs] at h
        simp only [SSt.seq_eq, Bool.cond_eq_ite] at h
        split_ifs at h with hm
        rw [walk] at he ⊢
        by_cases hst : (walk1 σ s).seq (walk σ ss) = .stuck
        · rw [hst]; trivial
        obtain ⟨he1, he2⟩ := seq_evs hst
        have hvs : FitV loc cg (Stmt.uses s) := hv.mono fun v hv ↦ by simp [Stmt.usesList, hv]
        have hvss : FitV loc cg (Stmt.usesList ss) := hv.mono fun v hv ↦ by simp [Stmt.usesList, hv]
        refine conc_seq (swS_sound hA s hs hI hvs fun e h ↦ he e (he1 e h))
          (fun es1 h1 pre1 Ψ1 hI1 _ _ ↦ swL_sound hA ss h hI1 hvss fun e h ↦ he e (he2 es1 h1 e h))
          fun es vs hr ↦ ?_
        have := mayRet_of_walk1 hr
        simp only [this, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hm
        simpa using hm

/-- **The arms of a `match`**: the arm taken. -/
theorem swArms_sound (hA : LocAgree loc cg) (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {st : SSt} {bs : List SSt}
    {pre : List V} {Ψ : ℕ → E}, swArms loc sh tt P st arms = some bs → Inv cg rd σ st pre Ψ →
    FitV loc cg (Stmt.usesArms arms) → (∀ e ∈ (walkArms σ x j arms).evs, e.Holds rd σ) →
    walkArms σ x j arms = .stuck ∨
      ∃ b ∈ bs, Conc cg rd σ st Ψ pre b (walkArms σ x j arms) ∧ b.pend = []
  | [], j, _, _, _, _, _, _, _, _ => Or.inl (by simp [walkArms])
  | a :: as, j, st, bs, pre, Ψ, h, hI, hv, he => by
      simp only [swArms] at h
      cases ha : swL loc sh tt P st a <;> cases has : swArms loc sh tt P st as <;> rw [ha, has] at h <;>
        simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i b bs'
      unfold walkArms at he ⊢
      split_ifs at he ⊢
      · exact Or.inr ⟨b, List.mem_cons_self, swL_sound hA a ha hI (hv.mono fun v hv ↦ by
          simp [Stmt.usesArms, hv]) he, swL_pend a ha⟩
      · rcases swArms_sound hA x as (j + 1) has hI (hv.mono fun v hv ↦ by simp [Stmt.usesArms, hv]) he with
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

variable {loc : Loc} {sh : ℕ} {tt : Exec.Trie ℕ} {P : Plumb}

mutual
theorem swS_listed : ∀ (s : Stmt) {st st' : SSt}, swS loc sh tt P st s = some st' →
    ∀ a ∈ sAtoms s, atomListed loc tt P a = true
  | .atom a, st, st', h, a', ha' => by
      simp only [swS, Bool.cond_eq_ite] at h
      split_ifs at h with hl
      simp only [sAtoms, List.mem_singleton] at ha'
      subst ha'; exact hl
  | .ite c z n, st, st', h, a, ha => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h
      cases hz : swL loc sh tt P (nameStep loc sh st [c]) z <;> cases hn : swL loc sh tt P (nameStep loc sh st [c]) n <;>
        rw [hz, hn] at h <;> simp only [reduceCtorEq] at h
      simp only [sAtoms, List.mem_append] at ha
      rcases ha with ha | ha
      · exact swL_listed z hz a ha
      · exact swL_listed n hn a ha
  | .match_ x arms, st, st', h, a, ha => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h
      cases har : swArms loc sh tt P (nameStep loc sh st [x]) arms <;> rw [har] at h <;>
        simp only [reduceCtorEq] at h
      exact swArms_listed arms har a ha
  | .call .., _, _, _, _, ha => by simp [sAtoms] at ha
  | .callIf .., _, _, _, _, ha => by simp [sAtoms] at ha
  | .dispatch .., _, _, _, _, ha => by simp [sAtoms] at ha
  | .ret _, _, _, _, _, ha => by simp [sAtoms] at ha

theorem swL_listed : ∀ (ss : List Stmt) {st st' : SSt}, swL loc sh tt P st ss = some st' →
    ∀ a ∈ lAtoms ss, atomListed loc tt P a = true
  | [], _, _, _, _, ha => by simp [lAtoms] at ha
  | s :: ss, st, st', h, a, ha => by
      simp only [swL] at h
      cases hs : swS loc sh tt P st s with
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
    swArms loc sh tt P st arms = some bs → ∀ a ∈ aAtoms arms, atomListed loc tt P a = true
  | [], _, _, _, _, ha => by simp [aAtoms] at ha
  | b :: as, st, bs, h, a, ha => by
      simp only [swArms] at h
      cases hb : swL loc sh tt P st b <;> cases has : swArms loc sh tt P st as <;> rw [hb, has] at h <;>
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


/-! ## A window's cells -/

section Cells

theorem packCells_digit : ∀ (l : List ℕ) (m : ℕ) (hm : m < l.length), (∀ c ∈ l, c < 65536) →
    packCells l / 65536 ^ m % 65536 = l[m]
  | [], _, hm, _ => absurd hm (by simp)
  | c :: cs, 0, _, h => by
    have hc := h c List.mem_cons_self
    show (c + packCells cs * 65536) / 65536 ^ 0 % 65536 = c
    rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  | c :: cs, m + 1, hm, h => by
    have hc := h c List.mem_cons_self
    have ih := packCells_digit cs m (by simpa using hm) fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    rw [List.getElem_cons_succ, ← ih]
    show (c + packCells cs * 65536) / 65536 ^ (m + 1) % 65536 = packCells cs / 65536 ^ m % 65536
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by norm_num),
      Nat.div_eq_of_lt hc, Nat.zero_add]

/-- **A window's cells are the certificate's.** -/
theorem locW_get {C : Cert} {n i : ℕ} (hcont : Cont C n) (hi : i ≤ n)
    (hins : C.insOk (nth C.ins i []) = true) (hn : C.cuts.length = n)
    (hcells : ∀ c ∈ nth C.cells i [], c < 65536) {v c : ℕ} (h : (locW C i).get? v = some c) :
    C.locs.getD v 0 = c := by
  simp only [Loc.get?, locW, Bool.cond_eq_ite, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  split_ifs at h with hr
  · cases h
    obtain ⟨h1, h2⟩ := hr
    have hm : v - nth C.los i 0 < (nth C.cells i []).length := by
      show Nat.sub v (nth C.los i 0) < _
      have : Nat.add (nth C.los i 0) (nth C.cells i []).length = nth C.los i 0 + (nth C.cells i []).length := rfl
      rw [this] at h2; show v - nth C.los i 0 < _; omega
    have hd := packCells_digit _ _ hm hcells
    have e1 := cont_locs hcont hi hm
    rw [show nth C.los i 0 + (v - nth C.los i 0) = v by omega] at e1
    rw [e1]; exact hd.symm
  · obtain ⟨j, hj⟩ := (insTrie_get _ _ h).resolve_right (by simp [getF_eq])
    have := List.all_eq_true.mp hins _ hj
    simp only [Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at this
    obtain ⟨⟨hjn, hlo⟩, hget⟩ := this
    obtain ⟨hm, hget⟩ := List.getElem?_eq_some_iff.mp hget
    rw [show v = nth C.los j 0 + (v - nth C.los j 0) by omega, cont_locs hcont (hn ▸ hjn) hm, hget]

theorem locAgree_of {C : Cert} {n i : ℕ} {cg : V → ℕ} (hcg : ∀ v, cg v = C.locs.getD v.idx 0)
    (hcont : Cont C n) (hi : i ≤ n) (hins : C.insOk (nth C.ins i []) = true) (hn : C.cuts.length = n)
    (hcells : ∀ c ∈ nth C.cells i [], c < 65536) : LocAgree (locW C i) cg := fun v hv ↦ by
  unfold Loc.cell at hv ⊢
  cases hg : (locW C i).get? v.idx with
  | none => rw [hg] at hv; simp at hv
  | some c => rw [hcg, locW_get hcont hi hins hn hcells hg]; rfl

end Cells

/-! ## Snapshots -/

section Snaps

variable {cg : V → ℕ} {rd : Reader} {σ : Val}

theorem getF_foldl_cst : ∀ (l : List (ℕ × ℕ × ℕ × ℕ)) (t : Exec.Trie (ℕ × ℕ × ℕ)) {c : ℕ} {x : ℕ × ℕ × ℕ},
    getF (l.foldl (fun t q ↦ setF q.2 envDepth t q.1) t) c = some x → (c, x) ∈ l ∨ getF t c = some x
  | [], _, _, _, h => Or.inr h
  | q :: l, t, c, x, h => by
    rcases getF_foldl_cst l _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases getF_setF h with ⟨rfl, rfl⟩ | h
      · exact Or.inl List.mem_cons_self
      · exact Or.inr h

theorem mem_foldl_snapKeys : ∀ (l : List (ℕ × ℕ × List ℕ)) (t : Exec.Trie (List (ℕ × List ℕ))) {c : ℕ}
    {k : ℕ × List ℕ}, k ∈ (getF (l.foldl (fun t q ↦ setF (q.2 :: (getF t q.1).getD []) envDepth t q.1) t) c).getD [] →
    (c, k) ∈ l ∨ k ∈ (getF t c).getD []
  | [], _, _, _, h => Or.inr h
  | q :: l, t, c, k, h => by
    rcases mem_foldl_snapKeys l _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · cases hg : getF (setF (q.2 :: (getF t q.1).getD []) envDepth t q.1) c with
      | none => rw [hg] at h; cases h
      | some l' =>
        rw [hg] at h
        rcases getF_setF hg with ⟨rfl, rfl⟩ | hg'
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl List.mem_cons_self
          · exact Or.inr h
        · rw [hg']; exact Or.inr h

/-- **A window's end state refines the next one's snapshot**: the snapshot's state holds for the
same words, every occupied cell staying occupied. -/
theorem refines_inv {m : SSt} {pre : List V} {Ψ : ℕ → E} {s : Snap} (hI : Inv cg rd σ m pre Ψ)
    (hr : refines m s = true) : Inv cg rd σ s.st [] Ψ ∧ Step m Ψ s.st Ψ := by
  simp only [refines, Bool.and_eq_true, List.all_eq_true, nbeq_iff, beq_iff_eq, List.any_eq_true] at hr
  obtain ⟨⟨⟨hocc, hnm⟩, hcst⟩, hky⟩ := hr
  have hsub : ∀ c, m.occ.testBit c = true → s.occ.testBit c = true := fun c h ↦ by
    have := congrArg (fun x ↦ x.testBit c) hocc
    simp only [testBit_land', h, Bool.true_and] at this
    exact this
  refine ⟨⟨fun _ h ↦ absurd h List.not_mem_nil, fun _ h ↦ absurd h List.not_mem_nil,
    fun _ h ↦ absurd h List.not_mem_nil, fun n hn hc ↦ ?_, fun c x hx ↦ ?_, fun c k hk ↦ ?_,
    fun p hp ↦ by simp [Snap.st] at hp⟩, fun c hc ↦ ⟨hsub c hc, rfl⟩⟩
  · rw [isNamed_eq] at hn
    simp only [Snap.st] at hn
    have hn' := hnm n ((testBit_bitsOf _ _).mp hn)
    rw [bitN_eq] at hn'
    obtain ⟨h1, h2⟩ := hI.named n (by rw [isNamed_eq]; exact hn') hc
    exact ⟨h1, hsub _ h2⟩
  · simp only [Snap.st] at hx
    rcases getF_foldl_cst _ _ hx with hx | hx
    · have := hcst _ hx
      obtain ⟨h1, h2⟩ := hI.kc c x this
      exact ⟨hsub c h1, h2⟩
    · simp [getF_eq] at hx
  · simp only [Snap.st] at hk
    rcases mem_foldl_snapKeys _ _ hk with hk | hk
    · obtain ⟨k', hk', he⟩ := hky _ hk
      subst he
      obtain ⟨h1, h2, h3⟩ := hI.keys c k' hk'
      exact ⟨h1, hsub c h2, fun c' hc' ↦ hsub c' (h3 c' hc')⟩
    · simp [getF_eq] at hk

end Snaps

/-! ## The check of a function -/

section Fn

open LeanVM.Guest.Memory

variable {j : ℕ}

/-- The state window `i` of function `j` starts from. -/
noncomputable def startSt (j i : ℕ) : SSt :=
  bif i == 0 then nameStep (locW (certOf j) 0) (bitsOf (plumbOf j).sh) (initSt (plumbOf j)) (coreOf j).params
  else (snapAt (snapsOf j) i).st

/-- What the static check says. -/
theorem shareStatic_spec (h : shareStatic j = true) :
    fsN j < 2 ^ envDepth ∧ listsOk (plumbOf j) (fsN j) = true ∧ snapsOk (certOf j) (snapsOf j) = true ∧
      apartOk j = true ∧
      ∀ v ∈ (coreOf j).params, valOk (locW (certOf j) 0) (byCell (plumbOf j).tmps) (tmpCells (plumbOf j))
        (fpgCells (plumbOf j)) (fsN j) v = true := by
  unfold shareStatic at h
  simp only [Loc.seq_eq, natSeq_eq, Exec.Trie.seq_eq, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- What a window's check says. -/
theorem shareWin_spec {i : ℕ} (h : shareWin j (snapsOf j) i = true) :
    (∀ c ∈ nth (certOf j).cells (winW (snapsOf j) i) [], c < 65536) ∧
    (∀ v ∈ Stmt.usesList (stmtsW (coreOf j).body (snapsOf j) i) ++ Stmt.tmpsList (stmtsW (coreOf j).body (snapsOf j) i),
      valOk (locW (certOf j) (winW (snapsOf j) i)) (byCell (plumbOf j).tmps) (tmpCells (plumbOf j)) (fpgCells (plumbOf j)) (fsN j) v
        = true) ∧
    ∃ m, swL (locW (certOf j) (winW (snapsOf j) i)) (bitsOf (plumbOf j).sh) (byCell (plumbOf j).tmps) (plumbOf j) (startSt j i)
        (stmtsW (coreOf j).body (snapsOf j) i) = some m ∧
      (i < (snapsOf j).length → refines m (snapAt (snapsOf j) (i + 1)) = true) := by
  unfold shareWin at h
  simp only [Loc.seq_eq, natSeq_eq, Exec.Trie.seq_eq, Bool.and_eq_true, List.all_eq_true,
    Nat.blt_eq] at h
  obtain ⟨⟨hc, hv⟩, hw⟩ := h
  refine ⟨hc, hv, ?_⟩
  have hs : startSt j i = (bif i == 0 then nameStep (locW (certOf j) (winW (snapsOf j) i)) (bitsOf (plumbOf j).sh)
      (initSt (plumbOf j)) (coreOf j).params else (snapAt (snapsOf j) i).st) := by
    unfold startSt
    cases hi : i == 0
    · rfl
    · obtain rfl := beq_iff_eq.mp hi; rfl
  rw [hs]
  split at hw
  · rename_i m hm
    refine ⟨m, hm, fun hi ↦ ?_⟩
    simpa [Nat.blt_eq.mpr hi] using hw
  · cases hw

end Fn

/-! ## The windows chained -/

section Chain

open LeanVM.Guest.Memory

variable {j : ℕ} {rd : Reader} {σ : Val}

theorem out_seq_assoc_sh : ∀ (o k l : Out), (o.seq k).seq l = o.seq (k.seq l)
  | .fall es, .fall es', l => by cases l <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .fall es, .ret es' vs, l => by simp [Out.seq, Out.pre]
  | .fall es, .stuck, l => by simp [Out.seq, Out.pre]
  | .ret es vs, k, l => by simp [Out.seq]
  | .stuck, k, l => by simp [Out.seq]

theorem walk_append_sh : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by rw [List.cons_append, walk, walk, walk_append_sh l l', out_seq_assoc_sh]

/-- The statements from window `k` on. -/
def fromW (body : List Stmt) (snaps : List Snap) (k : ℕ) : List Stmt := body.drop (startW snaps k)

theorem fromW_split {body : List Stmt} {snaps : List Snap} {k : ℕ} (hk : k < snaps.length)
    (hle : startW snaps k ≤ startW snaps (k + 1)) :
    fromW body snaps k = stmtsW body snaps k ++ fromW body snaps (k + 1) := by
  simp only [fromW, stmtsW, Nat.blt_eq.mpr hk, Bool.cond_true]
  have := List.take_append_drop (startW snaps (k + 1) - startW snaps k) (body.drop (startW snaps k))
  rw [List.drop_drop, Nat.add_sub_cancel' hle] at this
  exact this.symm

theorem fromW_last {body : List Stmt} {snaps : List Snap} {k : ℕ} (hk : snaps.length ≤ k) :
    fromW body snaps k = stmtsW body snaps k := by
  simp only [fromW, stmtsW, blt_false hk, Bool.cond_false]

theorem snapsOk_spec {C : Check.Cert} {snaps : List Snap} (h : snapsOk C snaps = true) {k : ℕ}
    (hk : k < snaps.length) : startW snaps k ≤ startW snaps (k + 1) ∧ winW snaps (k + 1) ≤ C.cuts.length := by
  simp only [snapsOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.ble_eq] at h
  exact h k hk

theorem winW_le {C : Check.Cert} {snaps : List Snap} (h : snapsOk C snaps = true) :
    ∀ {k : ℕ}, k ≤ snaps.length → winW snaps k ≤ C.cuts.length
  | 0, _ => Nat.zero_le _
  | _ + 1, hk => (snapsOk_spec h hk).2

theorem valOk_spec {loc : Loc} {tt : Exec.Trie ℕ} {tc fc n : ℕ} {v : V} (h : valOk loc tt tc fc n v = true) :
    v = V.n v.idx ∧ (loc.get? v.idx).isSome ∧ loc.cell v < n ∧ bitN fc (loc.cell v) = false ∧
      (bitN tc (loc.cell v) = false ∨ listedT tt v (loc.cell v) = true) := by
  simp only [valOk, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Bool.not_eq_true', Bool.or_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- A window's values, its cells the certificate's. -/
theorem fitV_of {loc : Loc} {tt : Exec.Trie ℕ} {tc fc n : ℕ} {cg : V → ℕ} {vs : List V}
    (hA : ∀ v c, loc.get? v.idx = some c → cg v = c) (h : ∀ v ∈ vs, valOk loc tt tc fc n v = true) :
    FitV loc cg vs := fun v hv ↦ by
  obtain ⟨h1, h2, -⟩ := valOk_spec (h v hv)
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h2
  refine ⟨h1, ?_⟩
  unfold Loc.cell
  rw [hc, hA v c hc]; rfl

theorem locAgree_strong {loc : Loc} {cg : V → ℕ} (hA : ∀ v c, loc.get? v.idx = some c → cg v = c) :
    LocAgree loc cg := fun v hv ↦ by
  unfold Loc.cell at hv ⊢
  cases hg : loc.get? v.idx with
  | none => rw [hg] at hv; simp at hv
  | some c => rw [hA v c hg]; rfl

/-- The events of a walk that returns. -/
theorem evs_ret {o : Out} {es : List Ev} {vs : List V} (h : o = .ret es vs) : o.evs = es := by
  rw [h]; rfl

/-- **The windows chained**: from window `i`'s start, on a path from there that returns, every value
named before or on it holds its cell's word, and the cells occupied at the start keep theirs. -/
theorem chain_sound (hS : ShareOk j)
    (hA : ∀ i ≤ (snapsOf j).length, ∀ v c, (locW (certOf j) (winW (snapsOf j) i)).get? v.idx = some c → cellJ j v = c) :
    ∀ k i, i + k = (snapsOf j).length → ∀ (pre : List V) (Ψ : ℕ → E),
      Inv (cellJ j) rd σ (startSt j i) pre Ψ → ∀ es vs, walk σ (fromW (coreOf j).body (snapsOf j) i) = .ret es vs →
      (∀ e ∈ es, e.Holds rd σ) → ∃ Ψf : ℕ → E,
        (∀ v ∈ pre ++ es.flatMap Ev.uses ++ vs, 2 ≤ cellJ j v → σ v = Ψf (cellJ j v)) ∧
        ∀ c, (startSt j i).occ.testBit c = true → Ψf c = Ψ c := by
  intro k
  induction k with
  | zero =>
    intro i hi pre Ψ hI es vs hw he
    have hiN : i ≤ (snapsOf j).length := by omega
    obtain ⟨-, hval, m, hsw, -⟩ := shareWin_spec (hS.2 i hiN)
    rw [fromW_last (by omega)] at hw
    have hfit : FitV (locW (certOf j) (winW (snapsOf j) i)) (cellJ j) (Stmt.usesList (stmtsW (coreOf j).body (snapsOf j) i)) :=
      fitV_of (hA i hiN) fun v hv ↦ hval v (List.mem_append_left _ hv)
    have hC := swL_sound (locAgree_strong (hA i hiN)) _ hsw hI hfit (by rw [evs_ret hw]; exact he)
    rw [hw] at hC
    obtain ⟨st'', pre', Ψ', hI', hs', hpe, hpre, hus, hvs⟩ := hC
    have hpe' : st''.pend = [] := by
      rcases hpe with hpe | rfl
      · exact hpe
      · exact swL_pend _ hsw
    refine ⟨Ψ', fun v hv hc ↦ ?_, fun c hc ↦ (hs' c hc).2⟩
    have hv' : v ∈ pre' := by
      simp only [List.mem_append, List.mem_flatMap] at hv
      rcases hv with (hv | ⟨e, he', hv⟩) | hv
      · exact hpre v hv
      · exact hus e he' v hv
      · exact hvs v hv
    exact hI'.good v hv' hc (by simp [isPend, hpe'])
  | succ k ih =>
    intro i hi pre Ψ hI es vs hw he
    have hiN : i < (snapsOf j).length := by omega
    obtain ⟨-, hval, m, hsw, href⟩ := shareWin_spec (hS.2 i hiN.le)
    obtain ⟨-, -, hmono, -, -⟩ := shareStatic_spec hS.1
    rw [fromW_split hiN (snapsOk_spec hmono hiN).1, walk_append_sh] at hw
    have hfit : FitV (locW (certOf j) (winW (snapsOf j) i)) (cellJ j) (Stmt.usesList (stmtsW (coreOf j).body (snapsOf j) i)) :=
      fitV_of (hA i hiN.le) fun v hv ↦ hval v (List.mem_append_left _ hv)
    have hAi := locAgree_strong (hA i hiN.le)
    cases hW : walk σ (stmtsW (coreOf j).body (snapsOf j) i) with
    | stuck => rw [hW] at hw; simp [Out.seq] at hw
    | ret es' vs' =>
      rw [hW] at hw
      simp only [Out.seq, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hC := swL_sound hAi _ hsw hI hfit (by rw [evs_ret hW]; exact he)
      rw [hW] at hC
      obtain ⟨st'', pre', Ψ', hI', hs', hpe, hpre, hus, hvs⟩ := hC
      have hpe' : st''.pend = [] := by
        rcases hpe with hpe | rfl
        · exact hpe
        · exact swL_pend _ hsw
      refine ⟨Ψ', fun v hv hc ↦ ?_, fun c hc ↦ (hs' c hc).2⟩
      have hv' : v ∈ pre' := by
        simp only [List.mem_append, List.mem_flatMap] at hv
        rcases hv with (hv | ⟨e, he', hv⟩) | hv
        · exact hpre v hv
        · exact hus e he' v hv
        · exact hvs v hv
      exact hI'.good v hv' hc (by simp [isPend, hpe'])
    | fall es1 =>
      rw [hW] at hw
      simp only [Out.seq] at hw
      cases hD : walk σ (fromW (coreOf j).body (snapsOf j) (i + 1)) with
      | fall _ => rw [hD] at hw; simp [Out.pre] at hw
      | stuck => rw [hD] at hw; simp [Out.pre] at hw
      | ret es2 vs2 =>
        rw [hD] at hw
        simp only [Out.pre, Out.ret.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        have hC := swL_sound hAi _ hsw hI hfit (by
          rw [hW]; exact fun e he' ↦ he e (List.mem_append_left _ he'))
        rw [hW] at hC
        obtain ⟨pre', Ψ', hI', hs', hpre, hus⟩ := hC
        have hpe : m.pend = [] := swL_pend _ hsw
        obtain ⟨hIs, hss⟩ := refines_inv hI' (href hiN)
        have hst : startSt j (i + 1) = (snapAt (snapsOf j) (i + 1)).st := rfl
        obtain ⟨Ψf, hf1, hf2⟩ := ih (i + 1) (by omega) [] Ψ' (hst ▸ hIs) es2 vs2 hD
          fun e he' ↦ he e (List.mem_append_right _ he')
        have hkeep : ∀ c, m.occ.testBit c = true → Ψf c = Ψ' c := fun c hc ↦
          hf2 c (by rw [hst]; exact (hss c hc).1)
        refine ⟨Ψf, fun v hv hc ↦ ?_, fun c hc ↦ ?_⟩
        · have old : v ∈ pre' → σ v = Ψf (cellJ j v) := fun hv' ↦ by
            rw [hkeep _ (hI'.occ v hv' hc)]
            exact hI'.good v hv' hc (by simp [isPend, hpe])
          rcases List.mem_append.mp hv with hv | hv
          · rcases List.mem_append.mp hv with hv | hv
            · exact old (hpre v hv)
            · rw [List.flatMap_append] at hv
              rcases List.mem_append.mp hv with hv | hv
              · obtain ⟨e, he', hv⟩ := List.mem_flatMap.mp hv
                exact old (hus e he' v hv)
              · exact hf1 v (List.mem_append_left _ (by simpa using hv)) hc
          · exact hf1 v (List.mem_append_right _ hv) hc
        · rw [hkeep c (hs' c hc).1, (hs' c hc).2]

end Chain

/-! ## The check of a function -/

section FnPath

open LeanVM.Guest.Memory

variable {j : ℕ} {rd : Reader} {σ : Val}

theorem getF_initCst : ∀ (l : List (ℕ × PC)) (t : Exec.Trie (ℕ × ℕ × ℕ)) {c : ℕ} {x : ℕ × ℕ × ℕ},
    getF (l.foldl (fun t q ↦ match q.2 with
      | .k a b c => setF (a, b, c) envDepth t q.1
      | .fpg _ => t) t) c = some x → (∃ q ∈ l, q.1 = c) ∨ getF t c = some x
  | [], _, _, _, h => Or.inr h
  | q :: l, t, c, x, h => by
    rcases getF_initCst l _ h with ⟨q', hq', he⟩ | h
    · exact Or.inl ⟨q', List.mem_cons_of_mem _ hq', he⟩
    · rcases q with ⟨o, _ | _⟩
      · simp only at h
        rcases getF_setF h with ⟨rfl, -⟩ | h
        · exact Or.inl ⟨_, List.mem_cons_self, rfl⟩
        · exact Or.inr h
      · exact Or.inr h

/-- The words the fixed cells start with. -/
noncomputable def initW (P : Plumb) (c : ℕ) : E :=
  match getF (initSt P).cst c with
  | some x => tw x
  | none => 0

theorem initSt_inv (P : Plumb) (cg : V → ℕ) : Inv cg rd σ (initSt P) [] (initW P) where
  vn _ h := absurd h List.not_mem_nil
  occ _ h := absurd h List.not_mem_nil
  good _ h := absurd h List.not_mem_nil
  named n hn _ := by simp [isNamed_eq, initSt] at hn
  kc c x hx := by
    refine ⟨?_, by simp only [initW, hx]⟩
    rcases getF_initCst _ _ hx with ⟨q, hq, rfl⟩ | hx
    · simp only [initSt]
      exact (testBit_bitsOf _ _).mpr (List.mem_map_of_mem hq)
    · simp [getF_eq] at hx
  keys c k hk := by simp [initSt, getF_eq] at hk
  pend p hp := by simp [initSt] at hp

/-- **The sharing check's conclusion on a path** of function `j` that returns: one word per cell
for every value the path names, a fixed cell's constant. -/
theorem shareOk_path {G : Glob} {f : CompiledFn} {main : Bool} (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G f (coreOf j) (certOf j) main i = true)
    {es : List Ev} {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs) (he : ∀ e ∈ es, e.Holds rd σ) :
    ∃ Ψ : ℕ → E, (∀ v ∈ (coreOf j).params ++ es.flatMap Ev.uses ++ vs, 2 ≤ cellJ j v →
      σ v = Ψ (cellJ j v)) ∧
      ∀ o a b c, (o, PC.k a b c) ∈ (plumbOf j).stat → Ψ o = OInstr.imm a b c := by
  have hcont := cont_of hchk
  obtain ⟨-, hlists, hsn, -, hpv⟩ := shareStatic_spec hS.1
  have hA : ∀ i ≤ (snapsOf j).length, ∀ v c, (locW (certOf j) (winW (snapsOf j) i)).get? v.idx = some c →
      cellJ j v = c := fun i hi v c h ↦
    locW_get hcont (winW_le hsn hi) (checkWin_parts (hchk _ (winW_le hsn hi))).2 rfl (shareWin_spec (hS.2 i hi)).1 h
  have hA0 : ∀ v c, (locW (certOf j) 0).get? v.idx = some c → cellJ j v = c := hA 0 (Nat.zero_le _)
  obtain ⟨Ψ1, hI1, hs1⟩ := nameStep_inv (sh := bitsOf (plumbOf j).sh) (locAgree_strong hA0)
    (initSt_inv (plumbOf j) (cellJ j) (rd := rd) (σ := σ)) (fitV_of hA0 hpv)
  have hst0 : startSt j 0 = nameStep (locW (certOf j) 0) (bitsOf (plumbOf j).sh) (initSt (plumbOf j))
      (coreOf j).params := rfl
  have hfrom : fromW (coreOf j).body (snapsOf j) 0 = (coreOf j).body := by
    simp only [fromW, startW, beq_self_eq_true, Bool.cond_true, List.drop_zero]
  obtain ⟨Ψf, hf1, hf2⟩ := chain_sound hS hA _ 0 (Nat.zero_add _) (coreOf j).params Ψ1 (hst0 ▸ by
    simpa using hI1) es vs (by rw [hfrom]; exact hw) he
  refine ⟨Ψf, fun v hv hc ↦ hf1 v (by simpa [List.append_assoc] using hv) hc, fun o a b c ho ↦ ?_⟩
  simp only [listsOk, Exec.Trie.seq_eq, natSeq_eq, Bool.and_eq_true, List.all_eq_true] at hlists
  have := hlists.1.1.1.1.1 _ ho
  simp only [beq_iff_eq] at this
  have hocc : (initSt (plumbOf j)).occ.testBit o = true :=
    (testBit_bitsOf _ _).mpr (List.mem_map_of_mem (f := Prod.fst) ho)
  have h0 : initW (plumbOf j) o = OInstr.imm a b c := by simp only [initW, this.2]; rfl
  rw [hf2 o (by rw [hst0]; exact (hs1 o hocc).1), (hs1 o hocc).2, h0]

end FnPath

end
end LeanVM.Guest.B2C
