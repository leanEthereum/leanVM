/-
  LeanVM.Protocol.Hotwire.StateLink

  Hotwire's state link: one identity over the cycles, between the rows' states and successors
  scattered at their cycle pointers, says that the rows are the cycles `0 … T - 1`, once each, and
  that their states chain from `s_init` to `s_fin`.
-/

module

public import ToMathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.CommRing
public import LeanVM.Protocol.Hotwire.Eq

/-!
# The state link

Hotwire (`crates/verifier/src/link.rs`, the verifier's `verify_link`; the prover's `link::prove`,
`crates/lean_vm_core/src/link/prove.rs`) links the instruction tables' rows
to the execution's states without a bus. Each row `u` (`R` holds every table's head rows) names
its cycle by a one-hot pointer, decoded here to `σ u : Fin (2^W)`, and carries its state `s u`
and its successor `s' u` in `F^k` (`k = 2` in leanVM: `pc` and `fp`). The *augmented* state
`(1, s)` (`aug`) has a constant component, which counts the rows. Scattering at the cycle pointer
gives two arrays over the cycles (`scatter`):

  `A(j) = Σ_{σ u = j} (1, s u)`, `B(j) = Σ_{σ u = j} (1, s' u)`.

The link checks, coefficient-wise (`LinkHolds`), for every cycle `j < 2^W`:

  `A(j) - [j ≥ 1]·B(j - 1) = [j = 0]·(1, s_init) - [j = T]·(1, s_fin)`  (I)

(`B(2^W - 1)` never appears).

* **Soundness** (`linkHolds_sound`): with `T = |R|` rows and `T < 2^W`, (I) makes `σ` a bijection
  onto `{0, …, T - 1}` (`ValidChain.bijective`), the row at cycle `0` holds `s_init`, each row's
  successor is the next cycle's state, and the row at cycle `T - 1` has successor `s_fin`
  (`ValidChain`). The constant component says `C(0) = 1`, `C(j) = C(j - 1)` for `j ∉ {0, T}` and
  `C(T) = C(T - 1) - 1`, so `C(j) = [j < T]` in `F` (`card_fiber_cast`), where `C(j)` is the
  number of rows at cycle `j` cast to `F`. In any characteristic `(n : F) = 1` forces `n ≥ 1`;
  `T` rows over the `T` cycles below `T`, at least one each, leave exactly one each and none
  above (`card_fiber_eq`). The other components then read off the chain.
* **Completeness** (`linkHolds_complete`): a valid chain with `T ≥ 1` satisfies (I).
* **The polynomial form** (`stateIdentity_iff`): (I) is equivalent to the identity
  `Σ_j eq(ζ, j)·A(j) - Σ_{j + 1 < 2^W} eq(ζ, j + 1)·B(j) = eq(ζ, 0)·(1, s_init) - eq(ζ, T)·(1, s_fin)`
  for every `ζ ∈ F^W` (`stateLhs`, `stateRhs`), the form the sum-check proves: the difference of
  the two sides is `Σ_j eq(ζ, j)·Err(j)` with `Err(j)` the defect of (I) at `j`
  (`stateLhs_sub_stateRhs`), and `eq(·, j)` at the Boolean point of `m` is `[j = m]`
  (`eqAt_bits`). A point `ζ : Fin W → F` is read as the list `List.ofFn ζ`, and `eqAt` is
  `Eq.lean`'s, the verifier's `eq_at`; `Σ_{j + 1 < 2^W} eq(r, j)·eq(ζ, j + 1)` is its `shift_eq(ζ, r)`
  (`ShiftEq.lean`).
* **Schwartz-Zippel** (`card_scalarIdentity_le`): the protocol checks the identity dotted with
  `(1, γ)` (`dotAug`, the verifier's `state_gamma`), at random `(ζ, γ)`. If (I) fails, the
  scalar identity is a nonzero polynomial of total degree at most `W + 1` in `(ζ, γ)`
  (`defectPoly`), so it holds at no more than `(W + 1)·|F|^(W + k - 1)` of the `|F|^(W + k)`
  points of a finite field.

The Rust works over `E`, of characteristic two, where the identity's signs are all `+`.
-/

namespace LeanVM.Protocol.Hotwire

open Finset MvPolynomial

@[expose] public section

variable {F : Type*} [Field F] {R : Type*} [Fintype R] {W k : ℕ}

/-! ## The scattered arrays -/

/-- The augmented state `(1, x)`, whose constant component counts the rows. -/
def aug (x : Fin k → F) : Fin (k + 1) → F := Fin.cons 1 x

/-- The rows whose cycle pointer names `j`. -/
def fiber (σ : R → Fin (2 ^ W)) (j : ℕ) : Finset R := univ.filter fun u ↦ (σ u : ℕ) = j

/-- The augmented values `x u` scattered at the cycle pointer: `A` for the states, `B` for the
successors (the verifier's `verify_link`, the index side). -/
def scatter (σ : R → Fin (2 ^ W)) (x : R → Fin k → F) (j : ℕ) : Fin (k + 1) → F :=
  ∑ u ∈ fiber σ j, aug (x u)

/-- The state link's identity (I), coefficient-wise: for every cycle `j < 2^W`,
`A(j) - [j ≥ 1]·B(j - 1) = [j = 0]·(1, s_init) - [j = T]·(1, s_fin)`. -/
def LinkHolds (T : ℕ) (σ : R → Fin (2 ^ W)) (s s' : R → Fin k → F) (sInit sFin : Fin k → F) :
    Prop :=
  ∀ j < 2 ^ W, scatter σ s j - (if 1 ≤ j then scatter σ s' (j - 1) else 0) =
    (if j = 0 then aug sInit else 0) - (if j = T then aug sFin else 0)

/-- A valid execution of `T` cycles: the rows are the cycles `0 … T - 1`, once each, the first
holds `s_init`, each row's successor is the next cycle's state, and the last's is `s_fin`. -/
structure ValidChain (T : ℕ) (σ : R → Fin (2 ^ W)) (s s' : R → Fin k → F)
    (sInit sFin : Fin k → F) : Prop where
  lt : ∀ u, (σ u : ℕ) < T
  existsUnique : ∀ j < T, ∃! u, (σ u : ℕ) = j
  init : ∀ u, (σ u : ℕ) = 0 → s u = sInit
  step : ∀ u v, (σ v : ℕ) = σ u + 1 → s' u = s v
  fin : ∀ u, (σ u : ℕ) + 1 = T → s' u = sFin

variable {T : ℕ} {σ : R → Fin (2 ^ W)} {s s' : R → Fin k → F} {sInit sFin : Fin k → F}

theorem aug_zero (x : Fin k → F) : aug x 0 = 1 := rfl

theorem aug_succ (x : Fin k → F) (i : Fin k) : aug x i.succ = x i := Fin.cons_succ _ _ _

theorem aug_injective : Function.Injective (aug : (Fin k → F) → Fin (k + 1) → F) :=
  fun _ _ h ↦ Fin.cons_right_injective (α := fun _ ↦ F) (1 : F) h

theorem mem_fiber {j : ℕ} {u : R} : u ∈ fiber σ j ↔ (σ u : ℕ) = j := by simp [fiber]

theorem scatter_zero_apply (x : R → Fin k → F) (j : ℕ) :
    scatter σ x j 0 = ((fiber σ j).card : F) := by
  simp [scatter, Finset.sum_apply, aug_zero]

theorem scatter_of_fiber_eq {x : R → Fin k → F} {j : ℕ} {u : R} (h : fiber σ j = {u}) :
    scatter σ x j = aug (x u) := by
  simp [scatter, h]

theorem scatter_of_fiber_empty {x : R → Fin k → F} {j : ℕ} (h : fiber σ j = ∅) :
    scatter σ x j = 0 := by
  simp [scatter, h]

/-- A fiber of one row is the fiber of any row in it. -/
theorem fiber_eq_singleton {j : ℕ} {u : R} (hc : (fiber σ j).card = 1) (hu : (σ u : ℕ) = j) :
    fiber σ j = {u} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have : u ∈ fiber σ j := mem_fiber.mpr hu
  rw [ha, Finset.mem_singleton] at this
  rw [ha, this]

/-! ## Soundness -/

/-- The constant component of (I): the row counts, cast to `F`. -/
theorem link_count (hlink : LinkHolds T σ s s' sInit sFin) {j : ℕ} (hj : j < 2 ^ W) :
    ((fiber σ j).card : F) - (if 1 ≤ j then ((fiber σ (j - 1)).card : F) else 0) =
      (if j = 0 then 1 else 0) - (if j = T then 1 else 0) := by
  have h := congrFun (hlink j hj) 0
  simp only [Pi.sub_apply, scatter_zero_apply] at h
  split_ifs at h ⊢ <;> simpa [aug_zero, scatter_zero_apply] using h

/-- The row count at each cycle is `[j < T]` in `F`. -/
theorem card_fiber_cast (hlink : LinkHolds T σ s s' sInit sFin) :
    ∀ j < 2 ^ W, ((fiber σ j).card : F) = if j < T then 1 else 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    have h := link_count hlink hj
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simpa using h
    · simpa [hT.ne, hT] using h
  | succ j ih =>
    intro hj
    have h := link_count hlink hj
    have ih := ih (by omega)
    rw [ite_eq_left (show 1 ≤ j + 1 by omega), Nat.add_sub_cancel, ih,
      ite_eq_right (show j + 1 ≠ 0 by omega), sub_eq_iff_eq_add] at h
    rw [h]
    by_cases h1 : j + 1 < T
    · rw [ite_eq_right (show j + 1 ≠ T by omega), ite_eq_left (show j < T by omega),
        ite_eq_left h1]
      simp
    · by_cases h2 : j + 1 = T
      · rw [ite_eq_left h2, ite_eq_left (show j < T by omega), ite_eq_right h1]
        simp
      · rw [ite_eq_right h2, ite_eq_right (show ¬ j < T by omega), ite_eq_right h1]
        simp

/-- Every row's cycle is below `2^W`, so the fibers below `2^W` partition the rows. -/
theorem sum_card_fiber :
    ∑ j ∈ range (2 ^ W), (fiber σ j).card = Fintype.card R := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun u ↦ (σ u : ℕ))
    (fun u _ ↦ Finset.mem_range.mpr (σ u).isLt)).symm

/-- With `T` rows, exactly one row at each cycle below `T` and none above. -/
theorem card_fiber_eq (hcard : Fintype.card R = T) (hT : T < 2 ^ W)
    (hlink : LinkHolds T σ s s' sInit sFin) :
    ∀ j < 2 ^ W, (fiber σ j).card = if j < T then 1 else 0 := by
  have hpos : ∀ j ∈ range T, 1 ≤ (fiber σ j).card := by
    intro j hj
    have hj := Finset.mem_range.mp hj
    have h := card_fiber_cast (F := F) hlink j (by omega)
    rw [ite_eq_left hj] at h
    rcases Nat.eq_zero_or_pos (fiber σ j).card with h0 | h0
    · rw [h0, Nat.cast_zero] at h
      exact absurd h zero_ne_one
    · exact h0
  have hsplit := Finset.sum_range_add_sum_Ico (fun j ↦ (fiber σ j).card) hT.le
  rw [sum_card_fiber, hcard] at hsplit
  have hge : T ≤ ∑ j ∈ range T, (fiber σ j).card := by
    simpa using Finset.card_nsmul_le_sum (range T) (fun j ↦ (fiber σ j).card) 1 hpos
  have hhigh : ∑ j ∈ Ico T (2 ^ W), (fiber σ j).card = 0 := by omega
  have hlow : ∑ j ∈ range T, (fun _ ↦ 1) j = ∑ j ∈ range T, (fiber σ j).card := by
    simp only [sum_const, card_range, smul_eq_mul, mul_one]
    omega
  rw [Finset.sum_eq_sum_iff_of_le hpos] at hlow
  intro j hj
  split_ifs with hjT
  · exact (hlow j (Finset.mem_range.mpr hjT)).symm
  · exact Finset.sum_eq_zero_iff.mp hhigh j (Finset.mem_Ico.mpr ⟨by omega, hj⟩)

/-- **Soundness of the state link.** With `T = |R|` rows and `T < 2^W` cycles addressable, the
identity (I) makes the rows a valid chain of `T` cycles from `s_init` to `s_fin`. -/
theorem linkHolds_sound (hcard : Fintype.card R = T) (hT : T < 2 ^ W)
    (hlink : LinkHolds T σ s s' sInit sFin) : ValidChain T σ s s' sInit sFin := by
  have hc := card_fiber_eq hcard hT hlink
  have lt : ∀ u, (σ u : ℕ) < T := by
    intro u
    by_contra hge
    have h := hc (σ u) (σ u).isLt
    rw [ite_eq_right hge] at h
    exact absurd (mem_fiber.mpr rfl) (Finset.card_eq_zero.mp h ▸ Finset.notMem_empty u)
  have one : ∀ u, (fiber σ (σ u : ℕ)) = {u} := fun u ↦
    fiber_eq_singleton (by rw [hc _ (σ u).isLt, ite_eq_left (lt u)]) rfl
  have empty : ∀ j, T ≤ j → j < 2 ^ W → fiber σ j = ∅ := fun j hj hjW ↦
    Finset.card_eq_zero.mp (by rw [hc j hjW, ite_eq_right (show ¬ j < T by omega)])
  refine ⟨lt, fun j hj ↦ ?_, fun u hu ↦ ?_, fun u v huv ↦ ?_, fun u hu ↦ ?_⟩
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by rw [hc j (by omega), ite_eq_left hj])
    have ha' : a ∈ fiber σ j := by rw [ha]; exact Finset.mem_singleton_self a
    refine ⟨a, mem_fiber.mp ha', fun v hv ↦ ?_⟩
    have : v ∈ fiber σ j := mem_fiber.mpr hv
    rwa [ha, Finset.mem_singleton] at this
  · have h := hlink 0 (Nat.two_pow_pos W)
    have hT0 : (0 : ℕ) ≠ T := by have := lt u; omega
    rw [ite_eq_right (show ¬ 1 ≤ 0 by omega), sub_zero, ite_eq_left rfl, ite_eq_right hT0,
      sub_zero, ← hu, scatter_of_fiber_eq (one u)] at h
    exact aug_injective h
  · have h := hlink (σ v) (σ v).isLt
    have hv := lt v
    rw [ite_eq_left (show 1 ≤ (σ v : ℕ) by omega), ite_eq_right (show (σ v : ℕ) ≠ 0 by omega),
      ite_eq_right (show (σ v : ℕ) ≠ T by omega), scatter_of_fiber_eq (one v), huv,
      Nat.add_sub_cancel, scatter_of_fiber_eq (one u)] at h
    exact (aug_injective (sub_eq_zero.mp (h.trans (sub_self 0)))).symm
  · have h := hlink T hT
    rw [ite_eq_left (show 1 ≤ T by omega), ite_eq_right (show T ≠ 0 by omega), ite_eq_left rfl,
      scatter_of_fiber_empty (empty T le_rfl hT), ← hu, Nat.add_sub_cancel,
      scatter_of_fiber_eq (one u)] at h
    simp only [zero_sub, neg_inj] at h
    exact aug_injective h

omit [Field F] [Fintype R] in
/-- The cycle pointer of a valid chain is a bijection from the rows onto the cycles below `T`. -/
theorem ValidChain.bijective (h : ValidChain T σ s s' sInit sFin) :
    Function.Bijective (fun u ↦ (⟨σ u, h.lt u⟩ : Fin T)) := by
  refine ⟨fun u v huv ↦ ?_, fun j ↦ ?_⟩
  · simp only [Fin.mk.injEq] at huv
    exact (h.existsUnique _ (h.lt v)).unique huv rfl
  · obtain ⟨u, hu, -⟩ := h.existsUnique j j.isLt
    exact ⟨u, Fin.ext hu⟩

/-! ## Completeness -/

/-- **Completeness of the state link.** A valid chain of `T ≥ 1` cycles satisfies (I). -/
theorem linkHolds_complete (hT1 : 1 ≤ T) (h : ValidChain T σ s s' sInit sFin) :
    LinkHolds T σ s s' sInit sFin := by
  have one : ∀ j < T, ∃ u, (σ u : ℕ) = j ∧ fiber σ j = {u} := by
    intro j hj
    obtain ⟨u, hu, huniq⟩ := h.existsUnique j hj
    refine ⟨u, hu, Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_fiber.mpr hu, fun v hv ↦ ?_⟩⟩
    exact huniq v (mem_fiber.mp hv)
  have empty : ∀ j, T ≤ j → fiber σ j = ∅ := fun j hj ↦
    Finset.eq_empty_of_forall_notMem fun u hu ↦ by have := h.lt u; rw [mem_fiber] at hu; omega
  intro j hj
  rcases Nat.lt_or_ge j T with hjT | hjT
  · obtain ⟨v, hv, hfv⟩ := one j hjT
    rw [scatter_of_fiber_eq hfv, ite_eq_right (show j ≠ T by omega), sub_zero]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [h.init v hv]
    · obtain ⟨u, hu, hfu⟩ := one (j - 1) (by omega)
      rw [ite_eq_left (show 1 ≤ j by omega), ite_eq_right (show j ≠ 0 by omega),
        scatter_of_fiber_eq hfu, h.step u v (by omega), sub_self]
  · rw [scatter_of_fiber_empty (empty j hjT), zero_sub, ite_eq_right (show j ≠ 0 by omega),
      zero_sub, ite_eq_left (show 1 ≤ j by omega)]
    rcases Nat.eq_or_lt_of_le hjT with rfl | hjT'
    · obtain ⟨u, hu, hfu⟩ := one (T - 1) (by omega)
      rw [scatter_of_fiber_eq hfu, h.fin u (by omega), ite_eq_left rfl]
    · rw [scatter_of_fiber_empty (empty _ (show T ≤ j - 1 by omega)),
        ite_eq_right (show j ≠ T by omega)]

/-! ## The polynomial form -/

/-- The Boolean point of `m`, bits LSB first. -/
def bits (m : ℕ) : Fin W → F := fun i ↦ if m.testBit i then 1 else 0

/-- The left side of the state identity at `ζ`:
`Σ_j eq(ζ, j)·A(j) - Σ_{j + 1 < 2^W} eq(ζ, j + 1)·B(j)`. Summed against `eq(r, j)` its second sum
is the verifier's `shift_eq(ζ, r)` times `B(r)`. -/
def stateLhs (σ : R → Fin (2 ^ W)) (s s' : R → Fin k → F) (ζ : Fin W → F) : Fin (k + 1) → F :=
  ∑ j ∈ range (2 ^ W), eqAt (List.ofFn ζ) j • scatter σ s j -
    ∑ j ∈ range (2 ^ W - 1), eqAt (List.ofFn ζ) (j + 1) • scatter σ s' j

/-- The right side of the state identity at `ζ`: `eq(ζ, 0)·(1, s_init) - eq(ζ, T)·(1, s_fin)`. -/
def stateRhs (T : ℕ) (sInit sFin : Fin k → F) (ζ : Fin W → F) : Fin (k + 1) → F :=
  eqAt (List.ofFn ζ) 0 • aug sInit - eqAt (List.ofFn ζ) T • aug sFin

/-- The defect of (I) at cycle `j`, `Err(j)`. -/
def defect (T : ℕ) (σ : R → Fin (2 ^ W)) (s s' : R → Fin k → F) (sInit sFin : Fin k → F)
    (j : ℕ) : Fin (k + 1) → F :=
  scatter σ s j - (if 1 ≤ j then scatter σ s' (j - 1) else 0) -
    ((if j = 0 then aug sInit else 0) - (if j = T then aug sFin else 0))

theorem linkHolds_iff_defect :
    LinkHolds T σ s s' sInit sFin ↔ ∀ j < 2 ^ W, defect T σ s s' sInit sFin j = 0 := by
  simp [LinkHolds, defect, sub_eq_zero]

/-- `eq(·, j)` at the Boolean point of `m` is `[j = m]`, for `j, m < 2^W`. -/
theorem eqAt_bits {j m : ℕ} (hj : j < 2 ^ W) (hm : m < 2 ^ W) :
    eqAt (List.ofFn (bits m : Fin W → F)) j = if j = m then 1 else 0 := by
  rw [eqAt_ofFn]
  split_ifs with h
  · subst h
    refine Finset.prod_eq_one fun i _ ↦ ?_
    by_cases hb : j.testBit i <;> simp [bits, hb]
  · obtain ⟨i, hi⟩ : ∃ i : Fin W, j.testBit i ≠ m.testBit i := by
      by_contra hne
      push Not at hne
      refine h (Nat.eq_of_testBit_eq fun i ↦ ?_)
      by_cases hiW : i < W
      · exact hne ⟨i, hiW⟩
      · have hW : 2 ^ W ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (not_lt.mp hiW)
        rw [Nat.testBit_lt_two_pow (hj.trans_le hW), Nat.testBit_lt_two_pow (hm.trans_le hW)]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hb : j.testBit i <;> cases hb' : m.testBit i <;> simp_all [bits]

/-- Summing against `eq(bits m, ·)` picks the value at `m`. -/
theorem sum_eqAt_bits {M : Type*} [AddCommGroup M] [Module F M] {m : ℕ} (hm : m < 2 ^ W)
    (f : ℕ → M) : ∑ j ∈ range (2 ^ W), eqAt (List.ofFn (bits m : Fin W → F)) j • f j = f m := by
  rw [Finset.sum_congr rfl fun j hj ↦ by rw [eqAt_bits (Finset.mem_range.mp hj) hm]]
  simp [ite_smul, hm]

/-- Shifting the successors' sum by one cycle. -/
theorem sum_shift (ζ : Fin W → F) (B : ℕ → Fin (k + 1) → F) (n : ℕ) :
    ∑ j ∈ range (n + 1), eqAt (List.ofFn ζ) j • (if 1 ≤ j then B (j - 1) else 0) =
      ∑ j ∈ range n, eqAt (List.ofFn ζ) (j + 1) • B j := by
  rw [Finset.sum_range_succ']
  simp

/-- The two sides of the state identity differ by `Σ_j eq(ζ, j)·Err(j)`. -/
theorem stateLhs_sub_stateRhs (hT : T < 2 ^ W) (ζ : Fin W → F) :
    stateLhs σ s s' ζ - stateRhs T sInit sFin ζ =
      ∑ j ∈ range (2 ^ W), eqAt (List.ofFn ζ) j • defect T σ s s' sInit sFin j := by
  have hW : 2 ^ W = 2 ^ W - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  have hshift := sum_shift ζ (scatter σ s') (2 ^ W - 1)
  rw [← hW] at hshift
  simp only [smul_ite, smul_zero] at hshift
  simp only [defect, smul_sub, Finset.sum_sub_distrib, hshift, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_range, Nat.two_pow_pos, hT, ite_true, stateLhs, stateRhs]

/-- **The polynomial form.** For `T < 2^W`, the state identity holds at every `ζ ∈ F^W` exactly
when (I) holds. -/
theorem stateIdentity_iff (hT : T < 2 ^ W) :
    (∀ ζ : Fin W → F, stateLhs σ s s' ζ = stateRhs T sInit sFin ζ) ↔
      LinkHolds T σ s s' sInit sFin := by
  rw [linkHolds_iff_defect]
  constructor
  · intro h m hm
    have h := sub_eq_zero.mpr (h (bits m))
    rwa [stateLhs_sub_stateRhs hT, sum_eqAt_bits hm] at h
  · intro h ζ
    rw [← sub_eq_zero, stateLhs_sub_stateRhs hT]
    exact Finset.sum_eq_zero fun j hj ↦ by rw [h j (Finset.mem_range.mp hj), smul_zero]

/-! ## The scalar identity and Schwartz-Zippel -/

/-- `⟨(1, γ), v⟩`: the combination the verifier takes of the augmented state, its
`state_gamma` (`1 + γ_pc·pc + γ_fp·fp`). -/
def dotAug (γ : Fin k → F) (v : Fin (k + 1) → F) : F := ∑ i, aug γ i * v i

/-- The left side of the scalar identity the sum-check proves, at `(ζ, γ)`. -/
def scalarLhs (σ : R → Fin (2 ^ W)) (s s' : R → Fin k → F) (ζ : Fin W → F) (γ : Fin k → F) : F :=
  ∑ j ∈ range (2 ^ W), eqAt (List.ofFn ζ) j * dotAug γ (scatter σ s j) -
    ∑ j ∈ range (2 ^ W - 1), eqAt (List.ofFn ζ) (j + 1) * dotAug γ (scatter σ s' j)

/-- The right side of the scalar identity, the sum-check's claim in `verify_link`:
`eq(ζ, 0)·ŝ_init,γ - eq(ζ, T)·ŝ_fin,γ`. -/
def scalarRhs (T : ℕ) (sInit sFin : Fin k → F) (ζ : Fin W → F) (γ : Fin k → F) : F :=
  eqAt (List.ofFn ζ) 0 * dotAug γ (aug sInit) - eqAt (List.ofFn ζ) T * dotAug γ (aug sFin)

/-- `eq(ζ, j)` as a polynomial in the variables `ζ` (`Sum.inl`) and `γ` (`Sum.inr`). -/
noncomputable def eqPoly (j : ℕ) : MvPolynomial (Fin W ⊕ Fin k) F :=
  ∏ i : Fin W, if j.testBit i then X (Sum.inl i) else 1 - X (Sum.inl i)

/-- `(1, γ)` as polynomials. -/
noncomputable def augPoly : Fin (k + 1) → MvPolynomial (Fin W ⊕ Fin k) F :=
  Fin.cons 1 fun l ↦ X (Sum.inr l)

/-- `Σ_j eq(ζ, j)·⟨(1, γ), Err(j)⟩` as a polynomial in `(ζ, γ)`. -/
noncomputable def defectPoly (T : ℕ) (σ : R → Fin (2 ^ W)) (s s' : R → Fin k → F)
    (sInit sFin : Fin k → F) : MvPolynomial (Fin W ⊕ Fin k) F :=
  ∑ j ∈ range (2 ^ W), eqPoly j * ∑ i, augPoly i * C (defect T σ s s' sInit sFin j i)

theorem dotAug_sub (γ : Fin k → F) (v w : Fin (k + 1) → F) :
    dotAug γ (v - w) = dotAug γ v - dotAug γ w := by
  simp [dotAug, mul_sub, Finset.sum_sub_distrib]

theorem dotAug_sum_smul (γ : Fin k → F) (S : Finset ℕ) (c : ℕ → F) (v : ℕ → Fin (k + 1) → F) :
    dotAug γ (∑ j ∈ S, c j • v j) = ∑ j ∈ S, c j * dotAug γ (v j) := by
  simp only [dotAug, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

theorem dotAug_smul (γ : Fin k → F) (c : F) (v : Fin (k + 1) → F) :
    dotAug γ (c • v) = c * dotAug γ v := by
  simp [dotAug, Finset.mul_sum, mul_left_comm]

theorem dotAug_eq (γ : Fin k → F) (v : Fin (k + 1) → F) :
    dotAug γ v = v 0 + ∑ l, γ l * v l.succ := by
  simp [dotAug, Fin.sum_univ_succ, aug_zero, aug_succ]

/-- The scalar identity is the vector identity dotted with `(1, γ)`. -/
theorem scalarLhs_sub_scalarRhs (hT : T < 2 ^ W) (ζ : Fin W → F) (γ : Fin k → F) :
    scalarLhs σ s s' ζ γ - scalarRhs T sInit sFin ζ γ =
      ∑ j ∈ range (2 ^ W), eqAt (List.ofFn ζ) j * dotAug γ (defect T σ s s' sInit sFin j) := by
  rw [← dotAug_sum_smul, ← stateLhs_sub_stateRhs hT, stateLhs, stateRhs, dotAug_sub, dotAug_sub,
    dotAug_sub, dotAug_sum_smul, dotAug_sum_smul, dotAug_smul, dotAug_smul, scalarLhs, scalarRhs]

theorem eval_eqPoly (x : Fin W ⊕ Fin k → F) (j : ℕ) :
    eval x (eqPoly j) = eqAt (List.ofFn (x ∘ Sum.inl)) j := by
  simp only [eqPoly, eqAt_ofFn, map_prod]
  exact Finset.prod_congr rfl fun i _ ↦ by split_ifs <;> simp

theorem eval_augPoly (x : Fin W ⊕ Fin k → F) (i : Fin (k + 1)) :
    eval x (augPoly i) = aug (x ∘ Sum.inr) i := by
  refine Fin.cases ?_ (fun l ↦ ?_) i
  · simp [augPoly, aug]
  · simp [augPoly, aug]

theorem eval_defectPoly (x : Fin W ⊕ Fin k → F) :
    eval x (defectPoly T σ s s' sInit sFin) =
      ∑ j ∈ range (2 ^ W), eqAt (List.ofFn (x ∘ Sum.inl)) j *
        dotAug (x ∘ Sum.inr) (defect T σ s s' sInit sFin j) := by
  simp [defectPoly, eval_eqPoly, eval_augPoly, dotAug]

theorem totalDegree_eqPoly (j : ℕ) :
    (eqPoly j : MvPolynomial (Fin W ⊕ Fin k) F).totalDegree ≤ W := by
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦ (?_ : _ ≤ 1)).trans (by simp)
  split_ifs
  · exact (totalDegree_X _).le
  · exact (totalDegree_sub _ _).trans (by simp [totalDegree_X])

theorem totalDegree_augPoly (i : Fin (k + 1)) :
    (augPoly i : MvPolynomial (Fin W ⊕ Fin k) F).totalDegree ≤ 1 := by
  refine Fin.cases ?_ (fun l ↦ ?_) i
  · simp [augPoly]
  · simp [augPoly, totalDegree_X]

theorem totalDegree_defectPoly :
    (defectPoly T σ s s' sInit sFin).totalDegree ≤ W + 1 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
  refine (totalDegree_mul _ _).trans (add_le_add (totalDegree_eqPoly j) ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  refine (totalDegree_mul _ _).trans ?_
  simpa [totalDegree_C] using totalDegree_augPoly i

/-- If (I) fails at some cycle, its defect polynomial is not zero: at the Boolean point of that
cycle, and `γ` zero or a unit vector picking a nonzero coefficient, it evaluates to that
coefficient. -/
theorem defectPoly_ne_zero (hfail : ¬ LinkHolds T σ s s' sInit sFin) :
    defectPoly T σ s s' sInit sFin ≠ 0 := by
  rw [linkHolds_iff_defect] at hfail
  push Not at hfail
  obtain ⟨m, hm, hne⟩ := hfail
  set e := defect T σ s s' sInit sFin m
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin k → F, dotAug γ e ≠ 0 := by
    by_cases h0 : e 0 = 0
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      refine Fin.cases (fun h ↦ absurd h0 h) (fun l hl ↦ ⟨Pi.single l 1, ?_⟩) i hi
      simpa [dotAug_eq, h0, Pi.single_apply] using hl
    · exact ⟨0, by simpa [dotAug_eq] using h0⟩
  intro hz
  have h := congrArg (eval (Sum.elim (bits m : Fin W → F) γ)) hz
  rw [eval_defectPoly, map_zero] at h
  have hl : Sum.elim (bits m : Fin W → F) γ ∘ Sum.inl = bits m := rfl
  have hr : Sum.elim (bits m : Fin W → F) γ ∘ Sum.inr = γ := rfl
  rw [hl, hr] at h
  have h' := sum_eqAt_bits (F := F) hm (fun j ↦ dotAug γ (defect T σ s s' sInit sFin j))
  simp only [smul_eq_mul] at h'
  exact hγ (h'.symm.trans h)

/-- **Schwartz-Zippel for the state link.** If (I) fails, the scalar identity the verifier
checks holds at no more than `(W + 1)·|F|^(W + k - 1)` of the `|F|^(W + k)` points `(ζ, γ)`
(VCVio's `MvPolynomial.card_zeros_le_of_totalDegree_le`). -/
theorem card_scalarIdentity_le [Fintype F] [DecidableEq F] (hT : T < 2 ^ W)
    (hfail : ¬ LinkHolds T σ s s' sInit sFin) :
    (univ.filter fun x : Fin W ⊕ Fin k → F ↦
        scalarLhs σ s s' (x ∘ Sum.inl) (x ∘ Sum.inr) =
          scalarRhs T sInit sFin (x ∘ Sum.inl) (x ∘ Sum.inr)).card ≤
      (W + 1) * Fintype.card F ^ (W + k - 1) := by
  have h := card_zeros_le_of_totalDegree_le _ (defectPoly_ne_zero hfail)
    (totalDegree_defectPoly (T := T) (σ := σ) (s := s) (s' := s') (sInit := sInit) (sFin := sFin))
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  refine le_of_eq_of_le (congrArg Finset.card (Finset.filter_congr fun x _ ↦ ?_)) h
  rw [← sub_eq_zero, scalarLhs_sub_scalarRhs hT, eval_defectPoly]

end

end LeanVM.Protocol.Hotwire

/-! The state link's theorems use Lean's three standard axioms only. -/

/-- info: 'LeanVM.Protocol.Hotwire.linkHolds_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.linkHolds_sound

/-- info: 'LeanVM.Protocol.Hotwire.linkHolds_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.linkHolds_complete

/-- info: 'LeanVM.Protocol.Hotwire.stateIdentity_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.stateIdentity_iff

/-- info: 'LeanVM.Protocol.Hotwire.card_scalarIdentity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.card_scalarIdentity_le
