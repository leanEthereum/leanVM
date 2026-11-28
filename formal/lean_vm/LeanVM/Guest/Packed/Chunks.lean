/-
  LeanVM.Guest.Packed.Chunks

  Long lane vectors as lists of small chunks, tested a chunk at a time.
-/

module

public import LeanVM.Guest.Packed.Lanes

/-!
# Chunked lane vectors

A test of `Lanes` on one big `ℕ` is a constant number of operations, whatever its size. What
walks a big number lane by lane, or reads its lanes one at a time, shifts the whole number at each
step, and the kernel keeps every intermediate number in its caches: time and memory quadratic in
the size. A vector to be walked is a list of chunks instead, each `c` lanes of `w` bits in a few
kilobits (lane `i` is lane `i % c` of chunk `i / c`, `Chunks.lane`), and a whole-vector test is
a `Lanes` test applied to each chunk (`all`) or each pair of chunks (`all2`). `all_lanes` and
`all2_lanes` turn a test's per-chunk spec into the spec of the whole vector.
-/

namespace LeanVM.Guest.Packed.Chunks

@[expose] public section

/-- Lane `i` of the chunked vector `cs`, chunks of `c` lanes of `w` bits. -/
def lane (cs : List ℕ) (w c i : ℕ) : ℕ := Packed.lane (cs.getD (i / c) 0) w (i % c)

/-- `t` holds of every chunk. -/
noncomputable def all (t : ℕ → Bool) (cs : List ℕ) : Bool :=
  List.rec (motive := fun _ ↦ Bool) true (fun a _ r ↦ Bool.rec false r (t a)) cs

/-- `as` and `bs` have as many chunks, and `t` holds of each pair. -/
noncomputable def all2 (t : ℕ → ℕ → Bool) (as : List ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ ↦ List ℕ → Bool)
    (fun bs ↦ List.rec (motive := fun _ ↦ Bool) true (fun _ _ _ ↦ false) bs)
    (fun a _ r bs ↦ List.rec (motive := fun _ ↦ Bool) false (fun b bs _ ↦ Bool.rec false (r bs) (t a b)) bs) as

end

variable {t : ℕ → Bool} {t2 : ℕ → ℕ → Bool} {w c : ℕ}

public theorem all_iff (cs : List ℕ) : all t cs = true ↔ ∀ j < cs.length, t (cs.getD j 0) = true := by
  induction cs with
  | nil => simp [all]
  | cons a cs ih =>
    show Bool.rec false (all t cs) (t a) = true ↔ _
    rw [List.length_cons]
    constructor
    · intro h j hj
      cases ht : t a <;> rw [ht] at h
      · cases h
      · cases j with
        | zero => simpa using ht
        | succ j => simpa using (ih.1 h) j (by omega)
    · intro h
      have h0 := h 0 (by omega)
      simp only [List.getD_cons_zero] at h0
      rw [h0]; exact ih.2 fun j hj ↦ by simpa using h (j + 1) (by omega)

public theorem all2_iff (as bs : List ℕ) : all2 t2 as bs = true ↔
    as.length = bs.length ∧ ∀ j < as.length, t2 (as.getD j 0) (bs.getD j 0) = true := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [all2]
  | cons a as ih =>
    cases bs with
    | nil => simp [all2]
    | cons b bs =>
      show Bool.rec false (all2 t2 as bs) (t2 a b) = true ↔ _
      simp only [List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · intro h
        cases ht : t2 a b <;> rw [ht] at h
        · cases h
        · refine ⟨(ih bs |>.1 h).1, fun j hj ↦ ?_⟩
          cases j with
          | zero => simpa using ht
          | succ j => simpa using (ih bs |>.1 h).2 j (by omega)
      · rintro ⟨hl, h⟩
        have h0 := h 0 (by omega)
        simp only [List.getD_cons_zero] at h0
        rw [h0]; exact (ih bs).2 ⟨hl, fun j hj ↦ by simpa using h (j + 1) (by omega)⟩

/-- A lane `i < c·n` of `n` chunks is lane `i % c` of chunk `i / c`, and every lane of a chunk
is one. -/
theorem forall_lanes (hc : 0 < c) (n : ℕ) (Q : ℕ → ℕ → Prop) :
    (∀ j < n, ∀ i < c, Q j i) ↔ ∀ i < c * n, Q (i / c) (i % c) := by
  constructor
  · intro h i hi
    exact h _ ((Nat.div_lt_iff_lt_mul hc).2 (by rwa [Nat.mul_comm])) _ (Nat.mod_lt _ hc)
  · intro h j hj i hi
    have hlt : c * j + i < c * n := calc
      c * j + i < c * j + c := by omega
      _ = c * (j + 1) := by rw [Nat.mul_succ]
      _ ≤ c * n := Nat.mul_le_mul_left c hj
    have := h (c * j + i) hlt
    rwa [Nat.mul_add_div hc, Nat.div_eq_of_lt hi, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hi] at this

/-- `all t` of a per-chunk lane test: its lane predicate on every lane. -/
public theorem all_lanes (hc : 0 < c) {P : ℕ → Prop} (cs : List ℕ)
    (h : ∀ j < cs.length, t (cs.getD j 0) = true ↔ ∀ i < c, P (Packed.lane (cs.getD j 0) w i)) :
    all t cs = true ↔ ∀ i < c * cs.length, P (lane cs w c i) := by
  rw [all_iff]
  exact (forall₂_congr h).trans (forall_lanes hc _ fun j i ↦ P (Packed.lane (cs.getD j 0) w i))

/-- `all2 t` of a per-chunk lane test: equal lengths, and its lane predicate on every lane. -/
public theorem all2_lanes (hc : 0 < c) {P : ℕ → ℕ → Prop} (as bs : List ℕ)
    (h : ∀ j < as.length, t2 (as.getD j 0) (bs.getD j 0) = true ↔
      ∀ i < c, P (Packed.lane (as.getD j 0) w i) (Packed.lane (bs.getD j 0) w i)) :
    all2 t2 as bs = true ↔ as.length = bs.length ∧ ∀ i < c * as.length, P (lane as w c i) (lane bs w c i) := by
  rw [all2_iff]
  exact and_congr_right fun _ ↦ (forall₂_congr h).trans
    (forall_lanes hc _ fun j i ↦ P (Packed.lane (as.getD j 0) w i) (Packed.lane (bs.getD j 0) w i))

end LeanVM.Guest.Packed.Chunks
