/-
  LeanVM.Guest.B1.Tables.VerifyTablesFwd

  A window of atoms completed forward: each value it defines set from those before it.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesPoly
public import LeanVM.Guest.B1.Sig.Frame
public import LeanVM.Guest.Memory.Retemp

/-!
# Forward completion

A window of atoms over values `lo ..< hi`: every value from `lo` it names is defined by its first
atom (a constant, a copy, a sum, a product, a load, a range check's complement and words) and
read only after. `fRun` sets each defined value from the values before it, a product whose
result is already set solving for its one unset factor. Every atom then holds (`fRun_holds`)
once the obligations `fObl` do: the atoms that define nothing, and the loads' and divisions'
conditions. `completes_fwd` is the window's `Completes`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Sig LeanVM.Guest.Memory

@[expose] public section

/-- A plain value's number. -/
def vNum : V → Option ℕ
  | ⟨[], 0, k⟩ => some k
  | _ => none

theorem vNum_some {v : V} {k : ℕ} (h : vNum v = some k) : v = .n k := by
  match v, h with
  | ⟨[], 0, k⟩, rfl => rfl

/-- `v` is set: anything but a plain value from `lo` outside `D`. -/
def fDef (lo : ℕ) (D : List ℕ) (v : V) : Bool :=
  match vNum v with
  | some k => decide (k < lo ∨ k ∈ D)
  | none => true

/-- `v` is unset, a plain value below `hi`. -/
def fNew (lo hi : ℕ) (D : List ℕ) (v : V) : Bool :=
  match vNum v with
  | some k => !decide (k < lo ∨ k ∈ D) && decide (k < hi)
  | none => false

/-- `D` with `v`. -/
def fAdd (D : List ℕ) (v : V) : List ℕ :=
  match vNum v with
  | some k => k :: D
  | none => D

/-- The word at `p + off`, or `0`. -/
def memAt (rd : Reader) (p : E) (off : ℕ) : E := (rd (p.limb 0 * gpow off)).getD 0

/-- One atom forward. -/
noncomputable def fStep (rd : Reader) (lo : ℕ) (D : List ℕ) (σ : Val) : Atom → List ℕ × Val
  | .const d c => if fDef lo D d then (D, σ) else (fAdd D d, Function.update σ d c)
  | .copy d s => if fDef lo D d then (D, σ) else (fAdd D d, Function.update σ d (σ s))
  | .add d x y => if fDef lo D d then (D, σ) else (fAdd D d, Function.update σ d (σ x + σ y))
  | .mul d x y =>
    if !fDef lo D d then (fAdd D d, Function.update σ d (σ x * σ y))
    else if !fDef lo D x then (fAdd D x, Function.update σ x (σ d * (σ y)⁻¹))
    else if !fDef lo D y then (fAdd D y, Function.update σ y (σ d * (σ x)⁻¹))
    else (D, σ)
  | .load d p off => if fDef lo D d then (D, σ) else (fAdd D d, Function.update σ d (memAt rd (σ p) off))
  | .assertNe x i p => if fDef lo D p then (D, σ) else (fAdd D p, Function.update σ p (σ x * σ i))
  | .rangeCheck x y t1 t2 k =>
    if fDef lo D y || fDef lo D t1 || fDef lo D t2 then (D, σ) else
      (fAdd (fAdd (fAdd D y) t1) t2, Function.update (Function.update (Function.update σ y
        (σ k * (σ x)⁻¹)) t1 (memAt rd (σ x) 0)) t2 (memAt rd (σ k * (σ x)⁻¹) 0))
  | _ => (D, σ)

/-- The atoms forward. -/
noncomputable def fRun (rd : Reader) (lo : ℕ) : List ℕ → Val → List Atom → Val
  | _, σ, [] => σ
  | D, σ, a :: as => fRun rd lo (fStep rd lo D σ a).1 (fStep rd lo D σ a).2 as

/-- An atom of a window. -/
def fOk1 (lo hi : ℕ) (D : List ℕ) : Atom → Bool
  | .const d _ => fDef lo D d || fNew lo hi D d
  | .copy d s => fDef lo D s && (fDef lo D d || fNew lo hi D d)
  | .add d x y => fDef lo D x && fDef lo D y && (fDef lo D d || fNew lo hi D d)
  | .mul d x y => (fDef lo D x && fDef lo D y && (fDef lo D d || fNew lo hi D d)) ||
      (fDef lo D d && fNew lo hi D x && fDef lo D y) || (fDef lo D d && fDef lo D x && fNew lo hi D y)
  | .load d p _ => fDef lo D p && (fDef lo D d || fNew lo hi D d)
  | .rangeCheck x y t1 t2 k => fDef lo D x && fDef lo D k &&
      ((fDef lo D y && fDef lo D t1 && fDef lo D t2) ||
        (fNew lo hi D y && fNew lo hi D t1 && fNew lo hi D t2 && decide (y ≠ t1) && decide (y ≠ t2) &&
          decide (t1 ≠ t2)))
  | .assertEq x y => fDef lo D x && fDef lo D y
  | .assertNe x i p => fDef lo D x && fDef lo D i && (fDef lo D p || fNew lo hi D p)
  | .assertInK x y => fDef lo D x && fDef lo D y
  | _ => false

/-- The new values of `D` after an atom, by its shape. -/
def fDStep (lo : ℕ) (D : List ℕ) : Atom → List ℕ
  | .const d _ | .copy d _ | .add d _ _ | .load d _ _ | .assertNe _ _ d => if fDef lo D d then D else fAdd D d
  | .mul d x y =>
    if !fDef lo D d then fAdd D d else if !fDef lo D x then fAdd D x
    else if !fDef lo D y then fAdd D y else D
  | .rangeCheck _ y t1 t2 _ =>
    if fDef lo D y || fDef lo D t1 || fDef lo D t2 then D else fAdd (fAdd (fAdd D y) t1) t2
  | _ => D

theorem fStep_fst (rd : Reader) (lo : ℕ) (D : List ℕ) (σ : Val) (a : Atom) :
    (fStep rd lo D σ a).1 = fDStep lo D a := by
  cases a <;> simp only [fStep, fDStep] <;> split_ifs <;> rfl

/-- A window: each atom's shape, from the values set before it. -/
def fOk (lo hi : ℕ) : List ℕ → List Atom → Bool
  | _, [] => true
  | D, a :: as => fOk1 lo hi D a && fOk lo hi (fDStep lo D a) as

/-- What an atom asks of the final valuation `σf`. -/
def fObl1 (rd : Reader) (lo : ℕ) (D : List ℕ) (σf : Val) : Atom → Prop
  | .const d c => fDef lo D d = true → σf d = c
  | .copy d s => fDef lo D d = true → σf d = σf s
  | .add d x y => fDef lo D d = true → σf d = σf x + σf y
  | .mul d x y => (fDef lo D d = true → fDef lo D x = true → fDef lo D y = true → σf d = σf x * σf y) ∧
      (fDef lo D d = true → fDef lo D x = false → σf y ≠ 0) ∧
      (fDef lo D d = true → fDef lo D x = true → fDef lo D y = false → σf x ≠ 0)
  | .load d p off => (fDef lo D d = true → LoadHolds rd (σf p) off (σf d)) ∧
      (fDef lo D d = false → IsInK (σf p) ∧ (rd ((σf p).limb 0 * gpow off)).isSome)
  | a@(.assertNe x i p) => (fDef lo D p = true → a.Holds rd σf) ∧ (fDef lo D p = false → σf x * σf i = 1)
  | a@(.rangeCheck x y _ _ _) => (fDef lo D y = true → a.Holds rd σf) ∧
      (fDef lo D y = false → σf x ≠ 0 ∧ IsInK (σf x) ∧ (rd ((σf x).limb 0 * gpow 0)).isSome ∧
        IsInK (σf y) ∧ (rd ((σf y).limb 0 * gpow 0)).isSome)
  | a => a.Holds rd σf

/-- The obligations of a window. -/
def fObl (rd : Reader) (lo : ℕ) (σf : Val) : List ℕ → List Atom → Prop
  | _, [] => True
  | D, a :: as => fObl1 rd lo D σf a ∧ fObl rd lo σf (fDStep lo D a) as

/-! ## Framing -/

theorem fDef_add {lo : ℕ} {D : List ℕ} {v : V} (w : V) (h : fDef lo D v = true) :
    fDef lo (fAdd D w) v = true := by
  unfold fDef at h ⊢
  cases hv : vNum v with
  | none => rfl
  | some k =>
    rw [hv] at h
    unfold fAdd
    cases hw : vNum w with
    | none => exact h
    | some j =>
      simp only [decide_eq_true_eq, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem fDef_add_self {lo : ℕ} {D : List ℕ} (w : V) : fDef lo (fAdd D w) w = true := by
  unfold fDef fAdd
  split <;> simp_all

theorem fNew_not_def {lo hi : ℕ} {D : List ℕ} {v : V} (h : fNew lo hi D v = true) :
    fDef lo D v = false := by
  unfold fNew at h; unfold fDef
  split <;> simp_all

theorem ne_of_def {lo : ℕ} {D : List ℕ} {u v : V} (hu : fDef lo D u = true) (hv : fDef lo D v = false) :
    u ≠ v := fun h => by rw [h] at hu; simp_all

theorem fDStep_mono {lo : ℕ} {D : List ℕ} {v : V} (a : Atom) (h : fDef lo D v = true) :
    fDef lo (fDStep lo D a) v = true := by
  cases a <;> simp only [fDStep] <;> (try split_ifs) <;>
    first | exact h | exact fDef_add _ h | exact fDef_add _ (fDef_add _ (fDef_add _ h))

/-- A step changes no set value. -/
theorem fStep_frame (rd : Reader) (lo : ℕ) (D : List ℕ) (σ : Val) (a : Atom) {v : V}
    (h : fDef lo D v = true) : (fStep rd lo D σ a).2 v = σ v := by
  cases a with
  | const d c =>
    simp only [fStep]; split_ifs with h1
    · rfl
    · exact Function.update_of_ne (ne_of_def h (by simpa using h1)) _ _
  | copy d s =>
    simp only [fStep]; split_ifs with h1
    · rfl
    · exact Function.update_of_ne (ne_of_def h (by simpa using h1)) _ _
  | add d x y =>
    simp only [fStep]; split_ifs with h1
    · rfl
    · exact Function.update_of_ne (ne_of_def h (by simpa using h1)) _ _
  | load d p off =>
    simp only [fStep]; split_ifs with h1
    · rfl
    · exact Function.update_of_ne (ne_of_def h (by simpa using h1)) _ _
  | assertNe x i p =>
    simp only [fStep]; split_ifs with h1
    · rfl
    · exact Function.update_of_ne (ne_of_def h (by simpa using h1)) _ _
  | mul d x y =>
    simp only [fStep]; split_ifs with h1 h2 h3
    · exact Function.update_of_ne (ne_of_def h (by simpa using h1)) _ _
    · exact Function.update_of_ne (ne_of_def h (by simpa using h2)) _ _
    · exact Function.update_of_ne (ne_of_def h (by simpa using h3)) _ _
    · rfl
  | rangeCheck x y t1 t2 k =>
    simp only [fStep]; split_ifs with h1
    · rfl
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1
      obtain ⟨⟨hy, ht1⟩, ht2⟩ := h1
      dsimp only
      rw [Function.update_of_ne (ne_of_def h ht2), Function.update_of_ne (ne_of_def h ht1),
        Function.update_of_ne (ne_of_def h hy)]
  | _ => rfl

theorem fRun_frame (rd : Reader) (lo : ℕ) : ∀ (as : List Atom) (D : List ℕ) (σ : Val) {v : V},
    fDef lo D v = true → fRun rd lo D σ as v = σ v
  | [], _, _, _, _ => rfl
  | a :: as, D, σ, v, h => by
    simp only [fRun]
    rw [fRun_frame rd lo as _ _ (by rw [fStep_fst]; exact fDStep_mono a h), fStep_frame rd lo D σ a h]

theorem fNew_num {lo hi : ℕ} {D : List ℕ} {v : V} (h : fNew lo hi D v = true) :
    ∃ k, v = .n k ∧ lo ≤ k ∧ k < hi := by
  unfold fNew at h
  split at h
  · next k hk =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
      not_or] at h
    exact ⟨k, vNum_some hk, by omega, h.2⟩
  · exact absurd h (by simp)

theorem def_or_new {lo hi : ℕ} {D : List ℕ} {v : V} (h : (fDef lo D v || fNew lo hi D v) = true)
    (hn : fDef lo D v = false) : fNew lo hi D v = true := by
  simpa [hn] using h

theorem update_ne_imp {σ : Val} {d v : V} {e : E} (h : Function.update σ d e v ≠ σ v) : v = d := by
  by_contra hne; exact h (Function.update_of_ne hne _ _)

/-- A step sets only new values. -/
theorem fStep_upd (rd : Reader) {lo hi : ℕ} {D : List ℕ} (σ : Val) {a : Atom}
    (hok : fOk1 lo hi D a = true) {v : V} (hv : (fStep rd lo D σ a).2 v ≠ σ v) : fNew lo hi D v = true := by
  cases a with
  | const d c =>
    simp only [fStep] at hv; simp only [fOk1] at hok
    split_ifs at hv with h1
    · exact absurd rfl hv
    · rw [update_ne_imp hv]; exact def_or_new hok (by simpa using h1)
  | copy d s =>
    simp only [fStep] at hv; simp only [fOk1, Bool.and_eq_true] at hok
    split_ifs at hv with h1
    · exact absurd rfl hv
    · rw [update_ne_imp hv]; exact def_or_new hok.2 (by simpa using h1)
  | add d x y =>
    simp only [fStep] at hv; simp only [fOk1, Bool.and_eq_true] at hok
    split_ifs at hv with h1
    · exact absurd rfl hv
    · rw [update_ne_imp hv]; exact def_or_new hok.2 (by simpa using h1)
  | load d p off =>
    simp only [fStep] at hv; simp only [fOk1, Bool.and_eq_true] at hok
    split_ifs at hv with h1
    · exact absurd rfl hv
    · rw [update_ne_imp hv]; exact def_or_new hok.2 (by simpa using h1)
  | assertNe x i p =>
    simp only [fStep] at hv; simp only [fOk1, Bool.and_eq_true] at hok
    split_ifs at hv with h1
    · exact absurd rfl hv
    · rw [update_ne_imp hv]; exact def_or_new hok.2 (by simpa using h1)
  | mul d x y =>
    simp only [fStep] at hv; simp only [fOk1, Bool.and_eq_true, Bool.or_eq_true] at hok
    split_ifs at hv with h1 h2 h3
    · rw [update_ne_imp hv]
      simp only [Bool.not_eq_true'] at h1
      rcases hok with (⟨-, hd⟩ | ⟨hd, -⟩) | ⟨hd, -⟩
      · exact def_or_new (by simpa using hd) h1
      · rw [h1] at hd; exact absurd hd (by simp)
      · rw [h1] at hd; exact absurd hd.1 (by simp)
    · rw [update_ne_imp hv]
      simp only [Bool.not_eq_true'] at h2
      rcases hok with (⟨⟨hx, -⟩, -⟩ | ⟨⟨-, hx⟩, -⟩) | ⟨⟨-, hx⟩, -⟩
      · rw [h2] at hx; exact absurd hx (by simp)
      · exact hx
      · rw [h2] at hx; exact absurd hx (by simp)
    · rw [update_ne_imp hv]
      simp only [Bool.not_eq_true', Bool.not_eq_false] at h3 h2
      rcases hok with (⟨⟨-, hy⟩, -⟩ | ⟨-, hy⟩) | ⟨-, hy⟩
      · rw [h3] at hy; exact absurd hy (by simp)
      · rw [h3] at hy; exact absurd hy (by simp)
      · exact hy
    · exact absurd rfl hv
  | rangeCheck x y t1 t2 k =>
    simp only [fStep] at hv; simp only [fOk1, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    split_ifs at hv with h1
    · exact absurd rfl hv
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1
      obtain ⟨⟨hy, ht1⟩, ht2⟩ := h1
      have hn : fNew lo hi D y = true ∧ fNew lo hi D t1 = true ∧ fNew lo hi D t2 = true := by
        simp only [hy, ht1, ht2, Bool.false_eq_true, and_false, false_or] at hok
        tauto
      obtain ⟨hny, hnt1, hnt2⟩ := hn
      dsimp only at hv
      by_cases e2 : v = t2
      · rw [e2]; exact hnt2
      rw [Function.update_of_ne e2] at hv
      by_cases e1 : v = t1
      · rw [e1]; exact hnt1
      rw [Function.update_of_ne e1] at hv
      rw [update_ne_imp hv]; exact hny
  | _ => exact absurd rfl hv

theorem fRun_upd (rd : Reader) {lo hi : ℕ} : ∀ (as : List Atom) (D : List ℕ) (σ : Val),
    fOk lo hi D as = true → ∀ v, fRun rd lo D σ as v ≠ σ v → ∃ k, v = .n k ∧ lo ≤ k ∧ k < hi
  | [], _, _, _, v, hv => absurd rfl hv
  | a :: as, D, σ, hok, v, hv => by
    simp only [fOk, Bool.and_eq_true] at hok
    simp only [fRun] at hv
    by_cases h : (fStep rd lo D σ a).2 v = σ v
    · rw [← h] at hv
      exact fRun_upd rd as _ _ (by rw [fStep_fst]; exact hok.2) v hv
    · exact fNew_num (fStep_upd rd σ hok.1 h)

/-- **A window changes only its values.** -/
theorem fRun_ext (rd : Reader) {lo hi : ℕ} {as : List Atom} {D : List ℕ} {σ : Val}
    (hok : fOk lo hi D as = true) : Ext lo hi σ (fRun rd lo D σ as) := by
  intro v hv
  by_contra hne
  obtain ⟨k, rfl, h1, h2⟩ := fRun_upd rd as D σ hok v hne
  exact hv k h1 h2 rfl

/-! ## The atoms hold -/

theorem fDef_step_of {lo : ℕ} {D : List ℕ} {a : Atom} {v : V}
    (h : fDef lo D v = true ∨ fDef lo (fDStep lo D a) v = true) : fDef lo (fDStep lo D a) v = true :=
  h.elim (fDStep_mono a) id

/-- After an atom of a window, all its values are set. -/
theorem fOk1_vars {lo hi : ℕ} {D : List ℕ} {a : Atom} (hok : fOk1 lo hi D a = true) :
    ∀ v ∈ atomUses a ++ atomTmps a, fDef lo (fDStep lo D a) v = true := by
  intro v hv
  cases a with
  | const d c =>
    simp only [atomUses, atomTmps, List.append_nil, List.mem_singleton] at hv; subst hv
    simp only [fDStep]; split_ifs with h1
    · exact h1
    · exact fDef_add_self _
  | copy d s =>
    simp only [fOk1, Bool.and_eq_true] at hok
    simp only [atomUses, atomTmps, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · simp only [fDStep]; split_ifs with h1
      · exact h1
      · exact fDef_add_self _
    · exact fDStep_mono _ hok.1
  | add d x y =>
    simp only [fOk1, Bool.and_eq_true] at hok
    simp only [atomUses, atomTmps, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · simp only [fDStep]; split_ifs with h1
      · exact h1
      · exact fDef_add_self _
    · exact fDStep_mono _ hok.1.1
    · exact fDStep_mono _ hok.1.2
  | load d p off =>
    simp only [fOk1, Bool.and_eq_true] at hok
    simp only [atomUses, atomTmps, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · simp only [fDStep]; split_ifs with h1
      · exact h1
      · exact fDef_add_self _
    · exact fDStep_mono _ hok.1
  | mul d x y =>
    simp only [fOk1, Bool.and_eq_true, Bool.or_eq_true] at hok
    simp only [atomUses, atomTmps, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    simp only [fDStep]
    split_ifs with h1 h2 h3
    · simp only [Bool.not_eq_true'] at h1
      have hx : fDef lo D x = true := by
        rcases hok with (⟨⟨hx, -⟩, -⟩ | ⟨⟨hd, -⟩, -⟩) | ⟨⟨hd, -⟩, -⟩
        · exact hx
        · rw [h1] at hd; exact absurd hd (by simp)
        · rw [h1] at hd; exact absurd hd (by simp)
      have hy : fDef lo D y = true := by
        rcases hok with (⟨⟨-, hy⟩, -⟩ | ⟨⟨hd, -⟩, -⟩) | ⟨⟨hd, -⟩, -⟩
        · exact hy
        · rw [h1] at hd; exact absurd hd (by simp)
        · rw [h1] at hd; exact absurd hd (by simp)
      rcases hv with rfl | rfl | rfl
      · exact fDef_add_self _
      · exact fDef_add _ hx
      · exact fDef_add _ hy
    · simp only [Bool.not_eq_true', Bool.not_eq_false] at h1 h2
      have hy : fDef lo D y = true := by
        rcases hok with (⟨⟨hx, -⟩, -⟩ | ⟨-, hy⟩) | ⟨⟨-, hx⟩, -⟩
        · rw [h2] at hx; exact absurd hx (by simp)
        · exact hy
        · rw [h2] at hx; exact absurd hx (by simp)
      rcases hv with rfl | rfl | rfl
      · exact fDef_add _ h1
      · exact fDef_add_self _
      · exact fDef_add _ hy
    · simp only [Bool.not_eq_true', Bool.not_eq_false] at h1 h2 h3
      rcases hv with rfl | rfl | rfl
      · exact fDef_add _ h1
      · exact fDef_add _ h2
      · exact fDef_add_self _
    · simp only [Bool.not_eq_true', Bool.not_eq_false] at h1 h2 h3
      rcases hv with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
  | rangeCheck x y t1 t2 k =>
    simp only [fOk1, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hx, hk⟩, hr⟩ := hok
    simp only [atomUses, atomTmps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    simp only [fDStep]
    split_ifs with h1
    · simp only [Bool.or_eq_true] at h1
      rcases hr with ⟨⟨hy, ht1⟩, ht2⟩ | ⟨⟨⟨⟨⟨hy, ht1⟩, ht2⟩, -⟩, -⟩, -⟩
      · rcases hv with (rfl | rfl | rfl) | rfl | rfl <;> assumption
      · rw [fNew_not_def hy, fNew_not_def ht1, fNew_not_def ht2] at h1; simp at h1
    · rcases hv with (rfl | rfl | rfl) | rfl | rfl
      · exact fDef_add _ (fDef_add _ (fDef_add _ hx))
      · exact fDef_add _ (fDef_add _ (fDef_add_self _))
      · exact fDef_add _ (fDef_add _ (fDef_add _ hk))
      · exact fDef_add _ (fDef_add_self _)
      · exact fDef_add_self _
  | assertEq x y =>
    simp only [fOk1, Bool.and_eq_true] at hok
    simp only [atomUses, atomTmps, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hok.1
    · exact hok.2
  | assertNe x i p =>
    simp only [fOk1, Bool.and_eq_true] at hok
    simp only [atomUses, atomTmps, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact fDStep_mono _ hok.1.1
    · exact fDStep_mono _ hok.1.2
    · simp only [fDStep]; split_ifs with h1
      · exact h1
      · exact fDef_add_self _
  | assertInK x y =>
    simp only [fOk1, Bool.and_eq_true] at hok
    simp only [atomUses, atomTmps, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hok.1
    · exact hok.2
  | _ => simp [fOk1] at hok

theorem loadHolds_memAt {rd : Reader} {p : E} {off : ℕ} (hp : IsInK p)
    (hs : (rd (p.limb 0 * gpow off)).isSome) : LoadHolds rd p off (memAt rd p off) := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨hp, by rw [memAt, hw]; rfl⟩

/-- **An atom holds** at a valuation agreeing with its step on its values, once its obligation
does. -/
theorem fStep_holds (rd : Reader) {lo hi : ℕ} {D : List ℕ} {σ : Val} {a : Atom}
    (hok : fOk1 lo hi D a = true) {σf : Val}
    (hag : ∀ v ∈ atomUses a ++ atomTmps a, σf v = (fStep rd lo D σ a).2 v) (hob : fObl1 rd lo D σf a) :
    a.Holds rd σf := by
  cases a with
  | const d c =>
    by_cases hd : fDef lo D d = true
    · exact hob hd
    · have e := hag d (by simp [atomUses])
      simp only [fStep, hd, Bool.false_eq_true, ↓reduceIte, Function.update_self] at e
      exact e
  | copy d s =>
    by_cases hd : fDef lo D d = true
    · exact hob hd
    · simp only [fOk1, Bool.and_eq_true] at hok
      have ed := hag d (by simp [atomUses])
      have es := hag s (by simp [atomUses])
      simp only [Bool.not_eq_true] at hd
      simp only [fStep, hd, Bool.false_eq_true, ↓reduceIte, Function.update_self] at ed es
      rw [Function.update_of_ne (ne_of_def hok.1 hd)] at es
      show σf d = σf s
      rw [ed, es]
  | add d x y =>
    by_cases hd : fDef lo D d = true
    · exact hob hd
    · simp only [fOk1, Bool.and_eq_true] at hok
      have ed := hag d (by simp [atomUses])
      have ex := hag x (by simp [atomUses])
      have ey := hag y (by simp [atomUses])
      simp only [Bool.not_eq_true] at hd
      simp only [fStep, hd, Bool.false_eq_true, ↓reduceIte, Function.update_self] at ed ex ey
      rw [Function.update_of_ne (ne_of_def hok.1.1 hd)] at ex
      rw [Function.update_of_ne (ne_of_def hok.1.2 hd)] at ey
      show σf d = σf x + σf y
      rw [ed, ex, ey]
  | load d p off =>
    by_cases hd : fDef lo D d = true
    · exact hob.1 hd
    · simp only [fOk1, Bool.and_eq_true] at hok
      have ed := hag d (by simp [atomUses])
      have ep := hag p (by simp [atomUses])
      simp only [Bool.not_eq_true] at hd
      simp only [fStep, hd, Bool.false_eq_true, ↓reduceIte, Function.update_self] at ed ep
      rw [Function.update_of_ne (ne_of_def hok.1 hd)] at ep
      obtain ⟨h1, h2⟩ := hob.2 hd
      rw [ep] at h1 h2
      show LoadHolds rd (σf p) off (σf d)
      rw [ed, ep]
      exact loadHolds_memAt h1 h2
  | mul d x y =>
    have ed := hag d (by simp [atomUses])
    have ex := hag x (by simp [atomUses])
    have ey := hag y (by simp [atomUses])
    obtain ⟨o1, o2, o3⟩ := hob
    simp only [fOk1, Bool.and_eq_true, Bool.or_eq_true] at hok
    show σf d = σf x * σf y
    simp only [fStep] at ed ex ey
    by_cases hd : fDef lo D d = true
    · by_cases hx : fDef lo D x = true
      · by_cases hy : fDef lo D y = true
        · exact o1 hd hx hy
        · simp only [Bool.not_eq_true] at hy
          simp only [hd, hx, hy, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
            Function.update_self] at ed ex ey
          have hy0 := o3 hd hx hy
          rw [Function.update_of_ne (ne_of_def hd hy)] at ed
          rw [Function.update_of_ne (ne_of_def hx hy)] at ex
          rw [ex] at hy0; rw [ed, ex, ey]
          rw [mul_comm (σ d), ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
      · simp only [Bool.not_eq_true] at hx
        have hy : fDef lo D y = true := by
          rcases hok with (⟨⟨hx', -⟩, -⟩ | ⟨-, hy⟩) | ⟨⟨-, hx'⟩, -⟩
          · rw [hx] at hx'; exact absurd hx' (by simp)
          · exact hy
          · rw [hx] at hx'; exact absurd hx' (by simp)
        simp only [hd, hx, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
          Function.update_self] at ed ex ey
        have hy0 := o2 hd hx
        rw [Function.update_of_ne (ne_of_def hd hx)] at ed
        rw [Function.update_of_ne (ne_of_def hy hx)] at ey
        rw [ey] at hy0; rw [ed, ex, ey]
        rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one]
    · simp only [Bool.not_eq_true] at hd
      have hx : fDef lo D x = true := by
        rcases hok with (⟨⟨hx, -⟩, -⟩ | ⟨⟨hd', -⟩, -⟩) | ⟨⟨hd', -⟩, -⟩
        · exact hx
        · rw [hd] at hd'; exact absurd hd' (by simp)
        · rw [hd] at hd'; exact absurd hd' (by simp)
      have hy : fDef lo D y = true := by
        rcases hok with (⟨⟨-, hy⟩, -⟩ | ⟨⟨hd', -⟩, -⟩) | ⟨⟨hd', -⟩, -⟩
        · exact hy
        · rw [hd] at hd'; exact absurd hd' (by simp)
        · rw [hd] at hd'; exact absurd hd' (by simp)
      simp only [hd, Bool.not_false, ↓reduceIte, Function.update_self] at ed ex ey
      rw [Function.update_of_ne (ne_of_def hx hd)] at ex
      rw [Function.update_of_ne (ne_of_def hy hd)] at ey
      rw [ed, ex, ey]
  | rangeCheck x y t1 t2 k =>
    by_cases hy : fDef lo D y = true
    · exact hob.1 hy
    · simp only [Bool.not_eq_true] at hy
      simp only [fOk1, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hx, hk⟩, hr⟩ := hok
      have hn : fNew lo hi D t1 = true ∧ fNew lo hi D t2 = true ∧ y ≠ t1 ∧ y ≠ t2 ∧ t1 ≠ t2 := by
        rcases hr with ⟨⟨hy', -⟩, -⟩ | h
        · rw [hy] at hy'; exact absurd hy' (by simp)
        · tauto
      obtain ⟨hn1, hn2, n1, n2, n3⟩ := hn
      have d1 := fNew_not_def hn1
      have d2 := fNew_not_def hn2
      obtain ⟨o0, o1, o2, o3, o4⟩ := hob.2 hy
      have ex := hag x (by simp [atomUses])
      have ey := hag y (by simp [atomUses])
      have ek := hag k (by simp [atomUses])
      have e1 := hag t1 (by simp [atomTmps])
      have e2 := hag t2 (by simp [atomTmps])
      simp only [fStep, hy, d1, d2, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at ex ey ek e1 e2
      rw [Function.update_of_ne (ne_of_def hx d2), Function.update_of_ne (ne_of_def hx d1),
        Function.update_of_ne (ne_of_def hx hy)] at ex
      rw [Function.update_of_ne (ne_of_def hk d2), Function.update_of_ne (ne_of_def hk d1),
        Function.update_of_ne (ne_of_def hk hy)] at ek
      rw [Function.update_of_ne n2, Function.update_of_ne n1, Function.update_self] at ey
      rw [Function.update_of_ne n3, Function.update_self] at e1
      rw [Function.update_self] at e2
      show LoadHolds rd (σf x) 0 (σf t1) ∧ σf k = σf x * σf y ∧ LoadHolds rd (σf y) 0 (σf t2)
      rw [ex] at o0 o1 o2; rw [ey] at o3 o4
      rw [ex, ey, ek, e1, e2]
      refine ⟨loadHolds_memAt o1 o2, ?_, loadHolds_memAt o3 o4⟩
      rw [mul_comm (σ k), ← mul_assoc, mul_inv_cancel₀ o0, one_mul]
  | assertEq x y => exact hob
  | assertNe x i p =>
    by_cases hp : fDef lo D p = true
    · exact hob.1 hp
    · simp only [Bool.not_eq_true] at hp
      simp only [fOk1, Bool.and_eq_true] at hok
      have ep := hag p (by simp [atomUses])
      have ex := hag x (by simp [atomUses])
      have ei := hag i (by simp [atomUses])
      simp only [fStep, hp, Bool.false_eq_true, ↓reduceIte, Function.update_self] at ep ex ei
      rw [Function.update_of_ne (ne_of_def hok.1.1 hp)] at ex
      rw [Function.update_of_ne (ne_of_def hok.1.2 hp)] at ei
      have h1 := hob.2 hp
      show σf p = σf x * σf i ∧ σf p = 1
      rw [ep, ex, ei]; rw [ex, ei] at h1
      exact ⟨rfl, h1⟩
  | assertInK x y => exact hob
  | _ => simp [fOk1] at hok

/-- **A window's atoms hold** once its obligations do. -/
theorem fRun_holds (rd : Reader) {lo hi : ℕ} (σf : Val) : ∀ (as : List Atom) (D : List ℕ) (σ : Val),
    fOk lo hi D as = true →
      (∀ v, fRun rd lo D σ as v = σf v) → fObl rd lo σf D as → ∀ a ∈ as, a.Holds rd σf
  | [], _, _, _, _, _, a, ha => absurd ha (by simp)
  | b :: as, D, σ, hok, hf, hob, a, ha => by
    simp only [fOk, Bool.and_eq_true] at hok
    simp only [fRun] at hf
    rw [fStep_fst] at hf
    obtain ⟨hob1, hob2⟩ := hob
    rcases List.mem_cons.mp ha with rfl | ha
    · refine fStep_holds (σ := σ) rd hok.1 (fun v hv => ?_) hob1
      rw [← hf v, ← fStep_fst rd lo D σ, fRun_frame rd lo as _ _ (by rw [fStep_fst]; exact fOk1_vars hok.1 v hv)]
    · exact fRun_holds rd σf as _ _ hok.2 hf hob2 a ha

/-! ## The window's `Completes` -/

theorem holdsList_atoms {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop} :
    ∀ as : List Atom, (∀ a ∈ as, a.Holds rd σ) → next → Stmt.HoldsList C rd σ (as.map .atom) next kret
  | [], _, hn => hn
  | a :: as, h, hn => ⟨h a (List.mem_cons_self ..), holdsList_atoms as (fun b hb => h b (List.mem_cons_of_mem _ hb)) hn⟩

/-- A statement that is an atom. -/
def Stmt.isAtom : Stmt → Bool
  | .atom _ => true
  | _ => false

theorem eq_map_atoms : ∀ ss : List Stmt, ss.all Stmt.isAtom = true → ss = (ss.filterMap atomOf).map .atom
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    match s, h.1 with
    | .atom a, _ =>
      simp only [List.filterMap_cons, atomOf, List.map_cons]
      exact congrArg _ (eq_map_atoms ss h.2)

/-- **A window completes forward**, its values set by `fRun`, once its obligations hold there. -/
theorem completes_fwd {C : CallRel} {rd : Reader} {lo hi : ℕ} (ss : List Stmt)
    (hat : ss.all Stmt.isAtom = true) (hok : fOk lo hi [] (ss.filterMap atomOf) = true) (σ : Val)
    (hob : fObl rd lo (fRun rd lo [] σ (ss.filterMap atomOf)) [] (ss.filterMap atomOf)) :
    Completes C rd lo hi ss σ (fun σ' => σ' = fRun rd lo [] σ (ss.filterMap atomOf)) := by
  refine ⟨_, fRun_ext rd hok, rfl, fun next kret hn => ?_⟩
  rw [eq_map_atoms ss hat]
  rw [show (List.map Stmt.atom (ss.filterMap atomOf)).filterMap atomOf = ss.filterMap atomOf by
    rw [← eq_map_atoms ss hat]]
  exact holdsList_atoms _ (fRun_holds rd _ _ [] σ hok (fun _ => rfl) hob) hn

/-! ## What a window defines -/

/-- An atom defining its result by arithmetic. -/
def fIsDef (lo : ℕ) (D : List ℕ) : Atom → Bool
  | .const d _ | .copy d _ | .add d _ _ | .mul d _ _ => !fDef lo D d
  | _ => false

/-- The atoms of a window defining their results by arithmetic. -/
def fDefAtoms (lo : ℕ) : List ℕ → List Atom → List Atom
  | _, [] => []
  | D, a :: as => (if fIsDef lo D a then [a] else []) ++ fDefAtoms lo (fDStep lo D a) as

/-- The loads of a window defining their results: `(result, pointer, offset)`. -/
def fLoads (lo : ℕ) : List ℕ → List Atom → List (V × V × ℕ)
  | _, [] => []
  | D, a :: as => (match a with
      | .load d p off => if fDef lo D d then [] else [(d, p, off)]
      | _ => []) ++ fLoads lo (fDStep lo D a) as

theorem fObl1_of_def {rd : Reader} {lo : ℕ} {D : List ℕ} {σf : Val} {a : Atom}
    (h : fIsDef lo D a = true) : fObl1 rd lo D σf a := by
  cases a <;> simp [fIsDef] at h <;> simp [fObl1, h]

/-- **The defining atoms hold**, with no obligation. -/
theorem fRun_defs (rd : Reader) {lo hi : ℕ} (σf : Val) : ∀ (as : List Atom) (D : List ℕ) (σ : Val),
    fOk lo hi D as = true → (∀ v, fRun rd lo D σ as v = σf v) → ∀ a ∈ fDefAtoms lo D as, a.Holds rd σf
  | [], _, _, _, _, a, ha => absurd ha (by simp [fDefAtoms])
  | b :: as, D, σ, hok, hf, a, ha => by
    simp only [fOk, Bool.and_eq_true] at hok
    simp only [fRun] at hf
    simp only [fDefAtoms, List.mem_append] at ha
    rcases ha with ha | ha
    · split_ifs at ha with hd
      · rcases List.mem_singleton.mp ha with rfl
        rw [fStep_fst] at hf
        refine fStep_holds (σ := σ) rd hok.1 (fun v hv => ?_) (fObl1_of_def hd)
        rw [← hf v, ← fStep_fst rd lo D σ, fRun_frame rd lo as _ _ (by rw [fStep_fst]; exact fOk1_vars hok.1 v hv)]
      · exact absurd ha (by simp)
    · rw [fStep_fst] at hf
      exact fRun_defs rd σf as _ _ hok.2 hf a ha

/-- **The defining loads read the memory.** -/
theorem fRun_loads (rd : Reader) {lo hi : ℕ} (σf : Val) : ∀ (as : List Atom) (D : List ℕ) (σ : Val),
    fOk lo hi D as = true → (∀ v, fRun rd lo D σ as v = σf v) →
      ∀ q ∈ fLoads lo D as, σf q.1 = memAt rd (σf q.2.1) q.2.2
  | [], _, _, _, _, q, hq => absurd hq (by simp [fLoads])
  | b :: as, D, σ, hok, hf, q, hq => by
    simp only [fOk, Bool.and_eq_true] at hok
    simp only [fRun] at hf
    simp only [fLoads, List.mem_append] at hq
    rcases hq with hq | hq
    · cases b with
      | load d p off =>
        simp only at hq
        split_ifs at hq with hd
        · exact absurd hq (by simp)
        · rcases List.mem_singleton.mp hq with rfl
          simp only [Bool.not_eq_true] at hd
          have hok1 := hok.1
          simp only [fOk1, Bool.and_eq_true] at hok
          have hfr := fun v (hv : fDef lo (fStep rd lo D σ (.load d p off)).1 v = true) =>
            (hf v).symm.trans (fRun_frame rd lo as _ _ hv)
          have e1 := hfr d (by rw [fStep_fst]; exact fOk1_vars hok1 d (by simp [atomUses]))
          have e2 := hfr p (by rw [fStep_fst]; exact fOk1_vars hok1 p (by simp [atomUses]))
          simp only [fStep, hd, Bool.false_eq_true, ↓reduceIte, Function.update_self] at e1 e2
          rw [Function.update_of_ne (ne_of_def hok.1.1 hd)] at e2
          dsimp only
          rw [e1, e2]
      | _ => simp at hq
    · rw [fStep_fst] at hf
      exact fRun_loads rd σf as _ _ hok.2 hf q hq

/-! ## The obligations as a list -/

/-- An obligation: an atom that holds, a nonzero divisor, a defined load, a defined range check. -/
inductive Ob where
  | holds (a : Atom)
  | nz (v : V)
  | unit (x i : V)
  | ld (p : V) (off : ℕ)
  | rc (x y : V)
  deriving DecidableEq

/-- What an obligation asks of the final valuation. -/
def Ob.Holds (rd : Reader) (σf : Val) : Ob → Prop
  | .holds a => a.Holds rd σf
  | .nz v => σf v ≠ 0
  | .unit x i => σf x * σf i = 1
  | .ld p off => IsInK (σf p) ∧ (rd ((σf p).limb 0 * gpow off)).isSome
  | .rc x y => σf x ≠ 0 ∧ IsInK (σf x) ∧ (rd ((σf x).limb 0 * gpow 0)).isSome ∧ IsInK (σf y) ∧
      (rd ((σf y).limb 0 * gpow 0)).isSome

/-- An atom's obligations. -/
def fObs1 (lo : ℕ) (D : List ℕ) : Atom → List Ob
  | a@(.const d _) | a@(.copy d _) | a@(.add d _ _) => if fDef lo D d then [.holds a] else []
  | a@(.mul d x y) => if !fDef lo D d then [] else if !fDef lo D x then [.nz y]
      else if !fDef lo D y then [.nz x] else [.holds a]
  | a@(.load d p off) => if fDef lo D d then [.holds a] else [.ld p off]
  | a@(.rangeCheck x y _ _ _) => if fDef lo D y then [.holds a] else [.rc x y]
  | a@(.assertNe x i p) => if fDef lo D p then [.holds a] else [.unit x i]
  | a => [.holds a]

/-- A window's obligations. -/
def fObs (lo : ℕ) : List ℕ → List Atom → List Ob
  | _, [] => []
  | D, a :: as => fObs1 lo D a ++ fObs lo (fDStep lo D a) as

theorem fObl1_of_obs {rd : Reader} {lo : ℕ} {D : List ℕ} {σf : Val} {a : Atom}
    (h : ∀ o ∈ fObs1 lo D a, o.Holds rd σf) : fObl1 rd lo D σf a := by
  cases a with
  | const d c =>
    intro hd; simp only [fObs1, hd, ↓reduceIte, List.mem_singleton, forall_eq] at h; exact h
  | copy d s =>
    intro hd; simp only [fObs1, hd, ↓reduceIte, List.mem_singleton, forall_eq] at h; exact h
  | add d x y =>
    intro hd; simp only [fObs1, hd, ↓reduceIte, List.mem_singleton, forall_eq] at h; exact h
  | mul d x y =>
    refine ⟨fun hd hx hy => ?_, fun hd hx => ?_, fun hd hx hy => ?_⟩
    · simp only [fObs1, hd, hx, hy, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mem_singleton,
        forall_eq] at h
      exact h
    · simp only [fObs1, hd, hx, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        List.mem_singleton, forall_eq] at h
      exact h
    · simp only [fObs1, hd, hx, hy, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        List.mem_singleton, forall_eq] at h
      exact h
  | load d p off =>
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · simp only [fObs1, hd, ↓reduceIte, List.mem_singleton, forall_eq] at h; exact h
    · simp only [fObs1, hd, Bool.false_eq_true, ↓reduceIte, List.mem_singleton, forall_eq] at h; exact h
  | rangeCheck x y t1 t2 k =>
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · simp only [fObs1, hy, ↓reduceIte, List.mem_singleton, forall_eq] at h; exact h
    · simp only [fObs1, hy, Bool.false_eq_true, ↓reduceIte, List.mem_singleton, forall_eq] at h; exact h
  | assertEq x y => simpa [fObs1, Ob.Holds, fObl1] using h
  | assertNe x i p =>
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · simp only [fObs1, hp, ↓reduceIte, List.mem_singleton, forall_eq] at h; exact h
    · simp only [fObs1, hp, Bool.false_eq_true, ↓reduceIte, List.mem_singleton, forall_eq] at h; exact h
  | assertInK x y => simpa [fObs1, Ob.Holds, fObl1] using h
  | blake2s m0 m1 m2 m3 c0 c1 o0 o1 md => simpa [fObs1, Ob.Holds, fObl1] using h
  | frameAddr p run => simpa [fObs1, Ob.Holds, fObl1] using h
  | hint x => simpa [fObs1, Ob.Holds, fObl1] using h

theorem fObl_of_obs {rd : Reader} {lo : ℕ} {σf : Val} : ∀ (as : List Atom) (D : List ℕ),
    (∀ o ∈ fObs lo D as, o.Holds rd σf) → fObl rd lo σf D as
  | [], _, _ => trivial
  | _ :: as, _, h => ⟨fObl1_of_obs fun o ho => h o (List.mem_append_left _ ho),
      fObl_of_obs as _ fun o ho => h o (List.mem_append_right _ ho)⟩

end
end LeanVM.Guest.B1.VerifySub
