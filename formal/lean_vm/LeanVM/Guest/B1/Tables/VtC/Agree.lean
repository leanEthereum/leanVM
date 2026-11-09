/-
  LeanVM.Guest.B1.Tables.VtC.Agree

  The forward evaluation on two memories agrees off the range checks' auxiliary reads, when its
  loads read words the two memories agree on and nothing uses those reads.
-/

module

public import LeanVM.Guest.B1.Fwd.Canon

/-!
# (List K → List E → Prog E) on two memories

A range check `rangeCheck x y t1 t2 k` reads the memory at `x` and `y` into `t1`, `t2`
(`auxIdx`); in the guest's bodies nothing else uses them (`deadB`). `ev_agree`: then `Fwd.ev` on
two memories gives the same words at every other index, when every load reads, at its address
under the first evaluation, the same word from both memories. So a function's honest valuation
is the same, off those reads, on every memory holding its buffers, and its calls' arguments and
returns with it.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The indices a statement's range check reads the memory into. -/
def auxS : Stmt → List ℕ
  | .atom (.rangeCheck _ _ t1 t2 _) => [t1.idx, t2.idx]
  | _ => []

/-- The indices the range checks of a block read the memory into. -/
def auxIdx (ss : List Stmt) : List ℕ := ss.flatMap auxS

/-- A statement uses none of `A` (a range check: none but its two reads). -/
def deadS (A : ℕ → Bool) : Stmt → Bool
  | .atom (.rangeCheck x y _ _ k) => !(A x.idx) && !(A y.idx) && !(A k.idx)
  | s => s.vals.all fun v ↦ !(A v.idx)

/-- Two word lists agree off `A`. -/
def AgreeOff (A : ℕ → Bool) (l1 l2 : List E) : Prop := ∀ i, A i = false → l1.getD i 0 = l2.getD i 0

theorem agreeOff_val {A : ℕ → Bool} {l1 l2 : List E} (h : AgreeOff A l1 l2) {v : V}
    (hv : A v.idx = false) : B1.Val.ofArgs l1 v = B1.Val.ofArgs l2 v := h _ hv

theorem not_mem_of_contains {A : ℕ → Bool} {i : ℕ} (h : (!(A i)) = true) : A i = false := by
  simpa using h

theorem dead_vals {A : ℕ → Bool} {s : Stmt} (hd : deadS A s = true)
    (hr : ∀ x y t1 t2 k, s ≠ .atom (.rangeCheck x y t1 t2 k)) : ∀ v ∈ s.vals, A v.idx = false := by
  intro v hv
  have : deadS A s = s.vals.all fun v ↦ !(A v.idx) := by
    cases s with
    | atom a => cases a with
      | rangeCheck x y t1 t2 k => exact absurd rfl (hr x y t1 t2 k)
      | _ => rfl
    | _ => rfl
  rw [this] at hd
  exact not_mem_of_contains (List.all_eq_true.mp hd v hv)

/-- **One atom's words agree off `A`.** -/
theorem newA_agree {rd1 rd2 : Reader} {w : ℕ → E} {A : ℕ → Bool} {l1 l2 : List E}
    (hlen : l1.length = l2.length) (hl : AgreeOff A l1 l2) {a : Atom} {c' : ℕ}
    (hc : chkA l1.length a = some c') (hd : deadS A (.atom a) = true)
    (haux : ∀ i ∈ auxS (.atom a), A i = true)
    (hrd : ∀ d p off, a = .load d p off →
      rd1 ((B1.Val.ofArgs l1 p).limb 0 * addressOfIndex off) = rd2 ((B1.Val.ofArgs l1 p).limb 0 *
          addressOfIndex off)) :
    ∀ j, A (l1.length + j) = false → (newA rd1 w l1 a).getD j 0 = (newA rd2 w l2 a).getD j 0 := by
  intro j hj
  have hσ : ∀ v, A v.idx = false → B1.Val.ofArgs l1 v = B1.Val.ofArgs l2 v := fun v hv ↦
    agreeOff_val hl hv
  by_cases hrc : ∃ x y t1 t2 k, a = .rangeCheck x y t1 t2 k
  · obtain ⟨x, y, t1, t2, k, rfl⟩ := hrc
    simp only [deadS, Bool.and_eq_true] at hd
    obtain ⟨⟨hx, hy⟩, hk⟩ := hd
    have h1 : A t1.idx = true := haux _ (by simp [auxS])
    have h2 : A t2.idx = true := haux _ (by simp [auxS])
    simp only [chkA] at hc
    split at hc
    · rename_i hc1
      simp only [Bool.and_eq_true] at hc1
      obtain ⟨⟨⟨⟨-, hyn⟩, ht1⟩, ht2⟩, -⟩ := hc1
      have hyn2 : isN l2.length y = true := hlen ▸ hyn
      simp only [newA, hyn, hyn2, ↓reduceIte]
      rcases j with _ | _ | _ | j
      · simp only [List.getD_cons_zero]
        rw [hσ k (not_mem_of_contains hk), hσ x (not_mem_of_contains hx)]
      · have e := idx_of_isN ht1
        rw [e] at h1
        simp only [Nat.zero_add] at hj
        rw [hj] at h1
        exact absurd h1 (by decide)
      · have e := idx_of_isN ht2
        rw [e] at h2
        simp only [Nat.zero_add, Nat.reduceAdd] at hj
        rw [hj] at h2
        exact absurd h2 (by decide)
      · simp
    · split at hc
      · rename_i hc2
        simp only [Bool.and_eq_true] at hc2
        obtain ⟨⟨⟨⟨-, hyo⟩, ht1⟩, ht2⟩, -⟩ := hc2
        have hny : isN l1.length y = false := not_isN_of_old hyo
        have hny2 : isN l2.length y = false := hlen ▸ hny
        simp only [newA, hny, hny2, Bool.false_eq_true, ↓reduceIte]
        rcases j with _ | _ | _ | j
        · have e := idx_of_isN ht1
          rw [e] at h1
          simp only [Nat.add_zero] at hj
          rw [hj] at h1
          exact absurd h1 (by decide)
        · have e := idx_of_isN ht2
          rw [e] at h2
          simp only [Nat.zero_add] at hj
          rw [hj] at h2
          exact absurd h2 (by decide)
        · simp only [List.getD_cons_succ, List.getD_cons_zero]
          rw [hσ x (not_mem_of_contains hx), hσ y (not_mem_of_contains hy)]
        · simp
      · exact absurd hc (by simp)
  · have hv := dead_vals hd (fun x y t1 t2 k h ↦ hrc ⟨x, y, t1, t2, k, by cases h; rfl⟩)
    have hs : ∀ v ∈ a.vals, B1.Val.ofArgs l1 v = B1.Val.ofArgs l2 v := fun v hm ↦ hσ v (hv v hm)
    congr 1
    cases a with
    | const d e => rfl
    | add d x y => simp only [newA, hs x (by simp [Atom.vals]), hs y (by simp [Atom.vals])]
    | mul d x y =>
      simp only [newA, ← hlen, hs x (by simp [Atom.vals]), hs y (by simp [Atom.vals]),
        hs d (by simp [Atom.vals])]
    | copy d s => simp only [newA, hs s (by simp [Atom.vals])]
    | load d p off =>
      simp only [newA, ← hlen]
      split
      · rw [rdAt, rdAt, hrd d p off rfl, hs p (by simp [Atom.vals])]
      · rfl
    | assertEq => rfl
    | assertInK => rfl
    | assertNe x i p => simp only [newA, hs x (by simp [Atom.vals])]
    | rangeCheck x y t1 t2 k => exact absurd ⟨x, y, t1, t2, k, rfl⟩ hrc
    | keccak ins outs i o =>
      simp only [newA]
      rw [List.map_congr_left (fun v hm ↦ hs v (by simp [Atom.vals, hm]))]
    | frameAddr p run => simp only [newA, hlen]
    | hint h =>
      cases h with
      | limbs v ds => simp only [newA, hs v (by simp [Atom.vals, Hint.vals])]
      | inverse x d => simp only [newA, hs x (by simp [Atom.vals, Hint.vals])]
      | witness n dst => cases dst <;> simp only [newA, hlen]
      | bits v a b dst => cases dst <;> simp only [newA, hlen]
      | bitsExp v a dst => cases dst <;> simp only [newA, hlen]
      | digitsExp v nb nd db st sc dst => cases dst <;> simp only [newA, hlen]
      | windowsExp v st wd ct dst => cases dst <;> simp only [newA, hlen]
      | log2Ceil b a f dst => simp only [newA, hlen]
      | alloc d n => simp only [newA, hlen]
      | allocDyn d n => simp only [newA, hlen]

/-- **The evaluations on two memories agree off the range checks' reads**: when nothing uses
those reads and every load reads, at its address under the first evaluation, the same word. -/
theorem ev_agree (rd1 rd2 : Reader) (w : ℕ → E) (A : ℕ → Bool) :
    ∀ (ss : List Stmt) (l1 l2 : List E) {c' : ℕ}, chk l1.length ss = some c' →
      l1.length = l2.length → AgreeOff A l1 l2 → ss.all (deadS A) = true →
      (∀ i ∈ auxIdx ss, A i = true) →
      (∀ d p off, Stmt.atom (.load d p off) ∈ ss →
        rd1 ((B1.Val.ofArgs (ev rd1 w l1 ss) p).limb 0 * addressOfIndex off) =
          rd2 ((B1.Val.ofArgs (ev rd1 w l1 ss) p).limb 0 * addressOfIndex off)) →
      AgreeOff A (ev rd1 w l1 ss) (ev rd2 w l2 ss)
  | [], l1, l2, _, _, _, hl, _, _, _ => hl
  | s :: ss, l1, l2, c', h, hlen, hl, hd, haux, hrd => by
    simp only [chk] at h
    split at h
    · rename_i c1 hc1
      have hc2 : chkS l2.length s = some c1 := by rw [← hlen]; exact hc1
      obtain ⟨hl1, -, -⟩ := stepS rd1 w l1 hc1
      obtain ⟨hl2, -, -⟩ := stepS rd2 w l2 hc2
      simp only [List.all_cons, Bool.and_eq_true] at hd
      have haux1 : ∀ i ∈ auxS s, A i = true := fun i hi ↦ haux i (by simp [auxIdx, hi])
      have haux2 : ∀ i ∈ auxIdx ss, A i = true := fun i hi ↦
        haux i (by simp only [auxIdx, List.flatMap_cons, List.mem_append] at hi ⊢; exact Or.inr hi)
      have hnew : AgreeOff A (l1 ++ newS rd1 w l1 s) (l2 ++ newS rd2 w l2 s) := by
        intro i hi
        rcases Nat.lt_or_ge i l1.length with hlt | hge
        · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]
          exact hl i hi
        · obtain ⟨j, rfl⟩ : ∃ j, i = l1.length + j := ⟨i - l1.length, by omega⟩
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _
            (by omega), Nat.add_sub_cancel_left, hlen, Nat.add_sub_cancel_left]
          cases s with
          | atom a =>
            refine newA_agree hlen hl hc1 hd.1 haux1 (fun d p off he ↦ ?_) j hi
            subst he
            have hp : p.idx < l1.length := by
              simp only [chkS, chkA] at hc1
              split at hc1
              · rename_i hp; exact (oldB_spec hp).2
              · exact absurd hc1 (by simp)
            have hm := hrd d p off List.mem_cons_self
            obtain ⟨m, hm'⟩ := (ev_spec rd1 w (.atom (.load d p off) :: ss) l1
              (by simp only [chk, hc1]; exact h)).2.1
            rwa [hm', ofArgs_old hp] at hm
          | call f args rets => simp only [newS, hlen]
          | dispatch x fs args rets => simp only [newS, hlen]
          | _ => simp only [newS]
      have h' : chk (l1 ++ newS rd1 w l1 s).length ss = some c' := by rw [hl1]; exact h
      exact ev_agree rd1 rd2 w A ss _ _ h' (by rw [hl1, hl2]) hnew hd.2 haux2
        (fun d p off hm ↦ hrd d p off (List.mem_cons_of_mem _ hm))
    · exact absurd h (by simp)

end
end LeanVM.Guest.B1.Tables
