/-
  LeanVM.Protocol.Hotwire.Lookup

  Hotwire's lookup link: the index side's agreement identity between the accesses scattered at the
  entries they name and the coordinates the rows claim, its completeness, the reads' cancellation,
  and its soundness as a polynomial in the link's challenges.
-/

module

public import LeanVM.Protocol.Hotwire.Window
public import ToMathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Nat.Bitwise

/-!
# The lookup link

A lookup target `M` (the memory, or the program) has columns `M_c` over the entries `j < 2^W` and a
presence column `LT_N(j) = [j < N]`, one on its `N` real entries and zero on the padding (the
verifier's `below(log_memory)`, `below(log_bytecode)`, `crates/verifier/src/link.rs`). Rows reach it
through *access slots* `k` (`Lookup`; one per table, pointer column and offset, the Rust's `Access`,
each with its own challenge `μ_k`): in row `u < 2^{h_k}` of its table the slot is on when its
selector and gate are (`on`), names the entry `hit k u` (`none` when the access drops out of the
scattered sum, as a block entry past its pointer's window does: `windowHit`), and claims the
coordinates `rv_c(k, u)`. A coordinate is a committed part plus reads (`coord`): a read `ρ` is
`λ_ρ(u)·M'_{c'}(σ_ρ(u))`, a column `c'` of any target read at a row's pointer `σ_ρ` at offset `0`.

With the challenges `θ` (per table), `τ` (the row point), `μ` (per slot) and `γ` (per column, and
`γ_★` on presence), each access weighs `coef = θ_F·eq(τ_F, u)·μ_k` (zero when off), and the index
side's lookup identity (`identity`) is

  `Σ_j access(j)·M_γ(j) − Σ_{c'} Σ_j read_{c'}(j)·M'_{c'}(j) − Z = 0`,

where `access(j) = Σ_{k,u} coef·[hit k u = j]`, `M_γ = Σ_c γ_c·M_c + γ_★·LT_N` (`targetγ`),
`read_{c'}(j) = Σ_ρ Σ_u coef·γ_{c_ρ}·λ_ρ(u)·[σ_ρ(u) = j]` and `Z = Σ_{k,u} coef·(Σ_c γ_c·rv^com_c +
γ_★)` holds the committed parts only (`rowSum`).

* **Reads cancel** (`readTerm_eq`, `identity_eq_plain`): the index side's read term is
  `Σ_{k,u} coef·Σ_c γ_c·(reads of rv_c)` with every read at its true value, so the identity is the
  plain lookup identity `Σ_j access(j)·M_γ(j) − Σ_{k,u} coef·rv_γ(k, u)` of the full coordinates.
* **The defect form** (`identity_eq_sum_err`): the identity's left side is
  `Σ_{k,u} coef·Σ_i γ_i·err(k, u)_i`, where `err` is the access's entry minus its
  coordinates, column by column, and `LT_N(entry) − 1` on presence; an access that drops out has
  entry `0`, presence `0`.
* **Completeness** (`identity_eq_zero`): if every access that is on names a real entry that agrees
  with its coordinates (`LinkHolds`, the paper's Definition 5.1), the identity holds at every
  challenge.
* **Soundness** (`identityPoly_ne_zero`, `totalDegree_identityPoly`, `card_identity_zero_le`): the
  left side is the evaluation of a polynomial in `(θ, τ, μ, β)` (`identityPoly`, `eval_identityPoly`),
  `β` the variables of the coordinate coefficients (`Coeffs`). If the link fails at some access
  (a wrong value, an entry at or past `N`, or an entry dropped out of a window), it is nonzero, of
  total degree at most `m + 2 + ν`; by Schwartz-Zippel the identity holds at no more than
  `(m + 2 + ν)·|F|^(n − 1)` of the `|F|^n` challenge points. `ν = 1` for independent coefficients
  (`Coeffs.independent`, as the Rust draws `γ_addr, γ_word, γ_★`: `card_identity_zero_le_independent`),
  `ν` for `γ_i = eq(β, idx i)` over `2^ν` indices (`Coeffs.eqWeights`, `card_identity_zero_le_eqWeights`),
  as the program side weighs an instruction's slots by `eq(α, slot)` over `2^BYTECODE_SLOT_BITS` slots (`slot_weights`).
* **The window** (`windowHit`, `windowHit_lt`, `window_read_hit`, `sum_eqAt_mul_access`): the
  Rust's access names `σ + s` when `(σ mod 2^{w_0}) + s < 2^{w_0}` and drops out otherwise, and the
  row side's read of it, `T_s(e_0)·Π_{i ≥ 1} ẽ_i(r_i)` (`Window.lean`), is the scattered access
  array's indicator read at `r`: `Σ_j eq(r, j)·access(j)` is the row side's sum of the slots'
  coefficients times their window reads.

What is modeled rather than transcribed: pointers by their decoded index (`Window.lean` ties the
one-hot chunks to it); gates and selectors as Booleans (the tables' constraints and the public
selectors make them so); one target per identity, the targets' identities then separated by `η` as
in the paper; the reads' targets as given columns `readable` (a read of the same column of its own
entry is allowed, the virtual read value); the Rust's word `lo + y·hi` as one element, and its
address and value forms, frame and program-slot reads as committed parts and reads; the per-table
row point as the first `h_k` coordinates of `τ`, as `omega_at` reads `τ[..heights[t]]`, with the
selector `active` (`u < n_F`) folded into `on`. The degree bound counts the challenges the access's
coefficient multiplies; the sum-check's own soundness and `η`'s separation of targets are not here.
-/

namespace LeanVM.Protocol.Hotwire

open Finset MvPolynomial

@[expose] public section

variable {F : Type*} [Field F]

/-! ## Equality weights on a prefix of the point -/

/-- `eq(τ_h, u) = Π_{i < h} eq(τ_i, bit i of u)`: row `u` of a table of `2^h` rows weighed at the
first `h` coordinates of the row point `τ ∈ F^m` (the verifier's `omega_at` on `τ[..heights[t]]`). -/
def eqLow {m : ℕ} (h : ℕ) (τ : Fin m → F) (u : ℕ) : F :=
  ∏ i : Fin m, if (i : ℕ) < h then (if u.testBit i then τ i else 1 - τ i) else 1

/-- The Boolean point of `v`, bits LSB first. -/
def bitPt {m : ℕ} (v : ℕ) : Fin m → F := fun i ↦ if v.testBit i then 1 else 0

/-- At the Boolean point of `v`, `eq(·_h, u)` is `[u = v]` for `u, v < 2^h`, `h ≤ m`. -/
theorem eqLow_bitPt {m h u v : ℕ} (hh : h ≤ m) (hu : u < 2 ^ h) (hv : v < 2 ^ h) :
    eqLow h (bitPt v : Fin m → F) u = if u = v then 1 else 0 := by
  split_ifs with huv
  · subst huv
    unfold eqLow
    refine prod_eq_one fun i _ ↦ ?_
    by_cases hb : u.testBit i <;> simp [bitPt, hb]
  · obtain ⟨i, hih, hi⟩ : ∃ i < h, u.testBit i ≠ v.testBit i := by
      by_contra hne
      push Not at hne
      refine huv (Nat.eq_of_testBit_eq fun i ↦ ?_)
      by_cases hi : i < h
      · exact hne i hi
      · have hW : 2 ^ h ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (not_lt.mp hi)
        rw [Nat.testBit_lt_two_pow (hu.trans_le hW), Nat.testBit_lt_two_pow (hv.trans_le hW)]
    unfold eqLow
    refine prod_eq_zero (mem_univ (⟨i, hih.trans_le hh⟩ : Fin m)) ?_
    simp only [hih, ite_true]
    cases hb : u.testBit i <;> cases hb' : v.testBit i <;> simp_all [bitPt]

/-- `eq(X_h, u)` as a polynomial in the `m` coordinates. -/
noncomputable def eqLowPoly (m h u : ℕ) : MvPolynomial (Fin m) F :=
  ∏ i : Fin m, if (i : ℕ) < h then (if u.testBit i then X i else 1 - X i) else 1

theorem eval_eqLowPoly {m h u : ℕ} (τ : Fin m → F) : eval τ (eqLowPoly m h u) = eqLow h τ u := by
  simp only [eqLowPoly, eqLow, map_prod]
  exact prod_congr rfl fun i _ ↦ by split_ifs <;> simp

theorem totalDegree_eqLowPoly {m h u : ℕ} : (eqLowPoly m h u : MvPolynomial (Fin m) F).totalDegree ≤ m := by
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (sum_le_sum fun i _ ↦ (?_ : _ ≤ 1)).trans (by simp)
  split_ifs
  · exact (totalDegree_X _).le
  · exact (totalDegree_sub _ _).trans (by simp [totalDegree_X])
  · simp

/-! ## The coordinate coefficients -/

/-- The coefficients of a target's `nC` columns and of its presence column (`Sum.inr ()`), as
polynomials of total degree at most `ν` in variables `G` that separate coefficient vectors: for
every nonzero `e`, some point makes `Σ_i γ_i·e_i` nonzero. -/
structure Coeffs (F : Type*) [Field F] (G : Type*) (nC : ℕ) where
  ν : ℕ
  poly : Fin nC ⊕ Unit → MvPolynomial G F
  degree_le : ∀ i, (poly i).totalDegree ≤ ν
  separates : ∀ e : Fin nC ⊕ Unit → F, e ≠ 0 → ∃ y : G → F, ∑ i, eval y (poly i) * e i ≠ 0

/-- Independent coefficients, one challenge per column and one on presence (the Rust's `γ_addr`,
`γ_word`, `γ_★`): `ν = 1`. -/
noncomputable def Coeffs.independent (nC : ℕ) : Coeffs F (Fin nC ⊕ Unit) nC where
  ν := 1
  poly := X
  degree_le i := (totalDegree_X i).le
  separates e he := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp he
    refine ⟨Pi.single i₀ 1, ?_⟩
    simpa [Pi.single_apply] using hi₀

/-- The coefficients `γ_i = eq(β, idx i)` at one point `β ∈ F^ν`, for distinct indices
`idx i < 2^ν` of the columns and presence: `ν` is their degree. -/
noncomputable def Coeffs.eqWeights (nC ν : ℕ) (idx : Fin nC ⊕ Unit → ℕ) (hinj : Function.Injective idx)
    (hlt : ∀ i, idx i < 2 ^ ν) : Coeffs F (Fin ν) nC where
  ν := ν
  poly i := eqLowPoly ν ν (idx i)
  degree_le _ := totalDegree_eqLowPoly
  separates e he := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp he
    refine ⟨bitPt (idx i₀), ?_⟩
    rw [sum_eq_single i₀]
    · rwa [eval_eqLowPoly, eqLow_bitPt le_rfl (hlt i₀) (hlt i₀), ite_eq_left rfl, one_mul]
    · intro i _ hi
      rw [eval_eqLowPoly, eqLow_bitPt le_rfl (hlt i) (hlt i₀), ite_eq_right (hinj.ne hi), zero_mul]
    · simp

/-! ## The lookup -/

/-- A lookup into one target with `nC` columns, by the access slots `S` of tables `Fin nT`, with
reads `Q` of the `nD` readable columns, over entries below `2^W` and row points in `F^m`. -/
structure Lookup (F : Type*) [Field F] (S Q : Type*) (nT nC nD m W : ℕ) where
  /-- The target's columns. -/
  entry : Fin nC → ℕ → F
  /-- The target's real entries are `j < real`: its presence column is `LT_real`. -/
  real : ℕ
  /-- The columns a read may read, of this or another target. -/
  readable : Fin nD → ℕ → F
  /-- A slot's table, and that table's row variables `h_k ≤ m`. -/
  table : S → Fin nT
  height : S → ℕ
  height_le : ∀ k, height k ≤ m
  /-- Whether slot `k` is on in row `u`: its selector and gate. -/
  on : S → ℕ → Bool
  /-- The entry slot `k` names in row `u`, `none` when the access drops out. -/
  hit : S → ℕ → Option ℕ
  hit_lt : ∀ k u j, hit k u = some j → j < 2 ^ W
  /-- The committed part of each coordinate. -/
  comm : S → ℕ → Fin nC → F
  /-- A read: the slot and coordinate it is part of, the column it reads, the pointer it reads
  through (its offset-`0` entry) and its scale. -/
  rSlot : Q → S
  rCoord : Q → Fin nC
  rCol : Q → Fin nD
  rPtr : Q → ℕ → ℕ
  rPtr_lt : ∀ ρ u, rPtr ρ u < 2 ^ W
  rScale : Q → ℕ → F

variable {S Q : Type*} [Fintype S] [DecidableEq S] [Fintype Q] {nT nC nD m W : ℕ}
variable (L : Lookup F S Q nT nC nD m W)

namespace Lookup

/-- The presence column, `LT_N(j) = [j < N]`. -/
def presence (j : ℕ) : F := if j < L.real then 1 else 0

/-- The reads of coordinate `c` of slot `k` in row `u`, at their true values. -/
def readPart (k : S) (u : ℕ) (c : Fin nC) : F :=
  ∑ ρ, if L.rSlot ρ = k ∧ L.rCoord ρ = c then L.rScale ρ u * L.readable (L.rCol ρ) (L.rPtr ρ u) else 0

/-- The coordinate `rv_c(k, u)`: its committed part plus its reads. -/
def coord (k : S) (u : ℕ) (c : Fin nC) : F := L.comm k u c + L.readPart k u c

/-- **The lookup link** (the paper's Definition 5.1): every access that is on names a real entry
that agrees with its coordinates. -/
def LinkHolds : Prop :=
  ∀ k, ∀ u < 2 ^ L.height k, L.on k u = true →
    ∃ j, L.hit k u = some j ∧ j < L.real ∧ ∀ c, L.entry c j = L.coord k u c

/-- An access's coefficient `θ_F·eq(τ_F, u)·μ_k`, zero when it is off. -/
def coef (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (k : S) (u : ℕ) : F :=
  if L.on k u then θ (L.table k) * eqLow (L.height k) τ u * μ k else 0

/-- `M_γ(j) = Σ_c γ_c·M_c(j) + γ_★·LT_N(j)`. -/
def targetγ (γ : Fin nC ⊕ Unit → F) (j : ℕ) : F :=
  ∑ c, γ (.inl c) * L.entry c j + γ (.inr ()) * L.presence j

/-- `access(j) = Σ_{k, u} coef·[hit k u = j]`: the accesses scattered at the entries they name. -/
def access (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (j : ℕ) : F :=
  ∑ k, ∑ u ∈ range (2 ^ L.height k), if L.hit k u = some j then L.coef θ τ μ k u else 0

/-- `read_{c'}(j) = Σ_ρ Σ_u coef·γ_{c_ρ}·λ_ρ(u)·[σ_ρ(u) = j]` over the reads of column `c'`, each
with its access's coefficient in this lookup. -/
def read (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (γ : Fin nC ⊕ Unit → F) (d : Fin nD) (j : ℕ) : F :=
  ∑ ρ, if L.rCol ρ = d then
    ∑ u ∈ range (2 ^ L.height (L.rSlot ρ)),
      if L.rPtr ρ u = j then L.coef θ τ μ (L.rSlot ρ) u * γ (.inl (L.rCoord ρ)) * L.rScale ρ u else 0
  else 0

/-- The committed parts combined, `rv^com_γ = Σ_c γ_c·rv^com_c + γ_★`. -/
def commγ (γ : Fin nC ⊕ Unit → F) (k : S) (u : ℕ) : F := ∑ c, γ (.inl c) * L.comm k u c + γ (.inr ())

/-- The full coordinates combined, `rv_γ = Σ_c γ_c·rv_c + γ_★`. -/
def coordγ (γ : Fin nC ⊕ Unit → F) (k : S) (u : ℕ) : F := ∑ c, γ (.inl c) * L.coord k u c + γ (.inr ())

/-- `Z`'s lookup part, the sum over rows of the committed parts: `Σ_{k,u} coef·rv^com_γ`. -/
def rowSum (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (γ : Fin nC ⊕ Unit → F) : F :=
  ∑ k, ∑ u ∈ range (2 ^ L.height k), L.coef θ τ μ k u * L.commγ γ k u

/-- The index side's lookup identity, as its left side minus its right:
`Σ_j access(j)·M_γ(j) − Σ_{c'} Σ_j read_{c'}(j)·M'_{c'}(j) − Z`. -/
def identity (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (γ : Fin nC ⊕ Unit → F) : F :=
  ∑ j ∈ range (2 ^ W), L.access θ τ μ j * L.targetγ γ j -
    ∑ d, ∑ j ∈ range (2 ^ W), L.read θ τ μ γ d j * L.readable d j - L.rowSum θ τ μ γ

/-- The plain lookup identity of the full coordinates, with no reads on the index side:
`Σ_j access(j)·M_γ(j) − Σ_{k,u} coef·rv_γ`. -/
def plainIdentity (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (γ : Fin nC ⊕ Unit → F) : F :=
  ∑ j ∈ range (2 ^ W), L.access θ τ μ j * L.targetγ γ j -
    ∑ k, ∑ u ∈ range (2 ^ L.height k), L.coef θ τ μ k u * L.coordγ γ k u

/-- An access's defect, per coordinate: its entry's column minus the coordinate, and its entry's
presence minus `1`; an access that drops out reads `0` in every column and in presence. -/
def err (k : S) (u : ℕ) : Fin nC ⊕ Unit → F
  | .inl c => (L.hit k u).elim 0 (L.entry c) - L.coord k u c
  | .inr _ => (L.hit k u).elim 0 L.presence - 1

/-! ### The reads cancel -/

/-- A sum over the entries of an indicator of the entry an access names. -/
theorem sum_range_ite_hit {M : Type*} [AddCommMonoid M] (o : Option ℕ) (n : ℕ)
    (ho : ∀ j, o = some j → j < n) (f : ℕ → M) :
    ∑ j ∈ range n, (if o = some j then f j else 0) = o.elim 0 f := by
  cases o with
  | none => simp
  | some a =>
    simp only [Option.some.injEq, Option.elim_some]
    rw [sum_ite_eq, ite_eq_left (mem_range.mpr (ho a rfl))]

omit [Fintype S] in
/-- The reads of one row, combined: `Σ_c γ_c·readPart_c = Σ_ρ [slot ρ = k]·γ_{c_ρ}·λ_ρ·M'(σ_ρ)`. -/
theorem sum_γ_readPart (γ : Fin nC ⊕ Unit → F) (k : S) (u : ℕ) :
    ∑ c, γ (.inl c) * L.readPart k u c =
      ∑ ρ, if L.rSlot ρ = k then
        γ (.inl (L.rCoord ρ)) * (L.rScale ρ u * L.readable (L.rCol ρ) (L.rPtr ρ u)) else 0 := by
  simp only [readPart, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun ρ _ ↦ ?_
  by_cases hk : L.rSlot ρ = k
  · simp only [hk, true_and, ite_true, mul_ite, mul_zero]
    rw [sum_ite_eq]
    simp
  · simp [hk]

/-- **Each read at its true value**: the index side's read term
`Σ_{c'} Σ_j read_{c'}(j)·M'_{c'}(j)` is `Σ_{k,u} coef·Σ_c γ_c·(reads of rv_c)`. -/
theorem readTerm_eq (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (γ : Fin nC ⊕ Unit → F) :
    ∑ d, ∑ j ∈ range (2 ^ W), L.read θ τ μ γ d j * L.readable d j =
      ∑ k, ∑ u ∈ range (2 ^ L.height k), L.coef θ τ μ k u * ∑ c, γ (.inl c) * L.readPart k u c := by
  have lhs : ∑ d, ∑ j ∈ range (2 ^ W), L.read θ τ μ γ d j * L.readable d j =
      ∑ ρ, ∑ u ∈ range (2 ^ L.height (L.rSlot ρ)), L.coef θ τ μ (L.rSlot ρ) u *
        (γ (.inl (L.rCoord ρ)) * (L.rScale ρ u * L.readable (L.rCol ρ) (L.rPtr ρ u))) := by
    simp only [read, sum_mul, ite_mul, zero_mul]
    calc _ = ∑ ρ, ∑ d, ∑ j ∈ range (2 ^ W), if L.rCol ρ = d then
            ∑ u ∈ range (2 ^ L.height (L.rSlot ρ)), (if L.rPtr ρ u = j then
              L.coef θ τ μ (L.rSlot ρ) u * γ (.inl (L.rCoord ρ)) * L.rScale ρ u * L.readable d j
              else 0) else 0 :=
          (sum_congr rfl fun _ _ ↦ sum_comm).trans sum_comm
      _ = _ := by
          refine sum_congr rfl fun ρ _ ↦ ?_
          rw [sum_comm]
          simp only [sum_ite_eq, mem_univ, ite_true]
          rw [sum_comm]
          refine sum_congr rfl fun u _ ↦ ?_
          rw [sum_ite_eq, ite_eq_left (mem_range.mpr (L.rPtr_lt ρ u))]
          ring
  rw [lhs]
  simp only [sum_γ_readPart, mul_sum, mul_ite, mul_zero]
  calc _ = ∑ ρ, ∑ k, ∑ u ∈ range (2 ^ L.height k), if L.rSlot ρ = k then L.coef θ τ μ k u *
          (γ (.inl (L.rCoord ρ)) * (L.rScale ρ u * L.readable (L.rCol ρ) (L.rPtr ρ u))) else 0 := by
        refine sum_congr rfl fun ρ _ ↦ ?_
        rw [sum_eq_single (L.rSlot ρ)]
        · simp
        · intro k _ hk
          exact sum_eq_zero fun u _ ↦ ite_eq_right (Ne.symm hk)
        · simp
    _ = _ := sum_comm.trans (sum_congr rfl fun _ _ ↦ sum_comm)

variable (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (γ : Fin nC ⊕ Unit → F)

/-- **The reads cancel**: the index side's identity, reads included, is the plain lookup identity
of the full coordinates, every read at its true value. -/
theorem identity_eq_plain : L.identity θ τ μ γ = L.plainIdentity θ τ μ γ := by
  rw [identity, plainIdentity, readTerm_eq, sub_sub, rowSum, ← sum_add_distrib]
  refine congrArg (_ - ·) (sum_congr rfl fun k _ ↦ ?_)
  rw [← sum_add_distrib]
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [coordγ, commγ, coord, mul_add, sum_add_distrib]
  ring

omit [DecidableEq S] [Fintype Q] in
/-- The accesses scattered at their entries, read against any `g`: `Σ_j access(j)·g(j)` is
`Σ_{k,u} coef·g(entry)`, an access that drops out giving `0`. -/
theorem sum_access_mul (g : ℕ → F) :
    ∑ j ∈ range (2 ^ W), L.access θ τ μ j * g j =
      ∑ k, ∑ u ∈ range (2 ^ L.height k), L.coef θ τ μ k u * (L.hit k u).elim 0 g := by
  simp only [access, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [sum_range_ite_hit _ _ (L.hit_lt k u)]
  rcases L.hit k u with _ | j <;> simp

omit [Fintype S] in
/-- An access's defect combined: `Σ_i γ_i·err_i = M_γ(entry) − rv_γ`. -/
theorem sum_γ_err (k : S) (u : ℕ) :
    ∑ i, γ i * L.err k u i = (L.hit k u).elim 0 (L.targetγ γ) - L.coordγ γ k u := by
  rw [Fintype.sum_sum_type]
  simp only [err, coordγ, Finset.univ_unique, sum_singleton, mul_sub, sum_sub_distrib]
  rcases L.hit k u with _ | j
  · simp only [Option.elim_none, mul_zero, sum_const_zero]
    ring
  · simp only [Option.elim_some, targetγ, PUnit.default_eq_unit]
    ring

/-- **The defect form**: the identity's left side is `Σ_{k,u} coef·Σ_i γ_i·err(k, u)_i`. -/
theorem identity_eq_sum_err :
    L.identity θ τ μ γ = ∑ k, ∑ u ∈ range (2 ^ L.height k), L.coef θ τ μ k u * ∑ i, γ i * L.err k u i := by
  rw [identity_eq_plain, plainIdentity, sum_access_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [sum_γ_err, mul_sub]

omit [Fintype S] in
/-- An access's defect is zero exactly when it names a real entry that agrees with its
coordinates. -/
theorem err_eq_zero_iff (k : S) (u : ℕ) :
    L.err k u = 0 ↔ ∃ j, L.hit k u = some j ∧ j < L.real ∧ ∀ c, L.entry c j = L.coord k u c := by
  constructor
  · intro h
    have hp := congrFun h (.inr ())
    simp only [err, Pi.zero_apply, sub_eq_zero] at hp
    rcases hhit : L.hit k u with _ | j
    · rw [hhit] at hp
      exact absurd hp.symm (by simp)
    · rw [hhit] at hp
      simp only [Option.elim_some, presence] at hp
      refine ⟨j, rfl, ?_, fun c ↦ ?_⟩
      · by_contra hj
        rw [ite_eq_right hj] at hp
        exact zero_ne_one hp
      · have hc := congrFun h (.inl c)
        simp only [err, hhit, Option.elim_some, Pi.zero_apply, sub_eq_zero] at hc
        exact hc
  · rintro ⟨j, hhit, hj, hc⟩
    funext i
    rcases i with c | _
    · simp [err, hhit, hc]
    · simp [err, hhit, presence, hj]

/-- **Completeness**: if the lookup link holds, the identity holds at every challenge. -/
theorem identity_eq_zero (h : L.LinkHolds) : L.identity θ τ μ γ = 0 := by
  rw [identity_eq_sum_err]
  refine sum_eq_zero fun k _ ↦ sum_eq_zero fun u hu ↦ ?_
  by_cases hon : L.on k u = true
  · rw [(L.err_eq_zero_iff k u).mpr (h k u (mem_range.mp hu) hon)]
    simp
  · simp [coef, hon]

end Lookup

/-! ## The identity as a polynomial in the challenges -/

/-- The challenges' variables: `θ` per table, `τ` over the row point, `μ` per slot, and the
coordinate coefficients' variables `G`. -/
abbrev LookupVar (S G : Type*) (nT m : ℕ) := Fin nT ⊕ Fin m ⊕ S ⊕ G

section Poly

variable {G : Type*}

/-- The point of the challenges `(θ, τ, μ, β)`. -/
def lookupPt (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (β : G → F) : LookupVar S G nT m → F :=
  Sum.elim θ (Sum.elim τ (Sum.elim μ β))

/-- `θ` at a point. -/
def θOf (x : LookupVar S G nT m → F) : Fin nT → F := fun t ↦ x (.inl t)
/-- `τ` at a point. -/
def τOf (x : LookupVar S G nT m → F) : Fin m → F := fun i ↦ x (.inr (.inl i))
/-- `μ` at a point. -/
def μOf (x : LookupVar S G nT m → F) : S → F := fun k ↦ x (.inr (.inr (.inl k)))
/-- The coordinate coefficients' variables at a point. -/
def βOf (x : LookupVar S G nT m → F) : G → F := fun g ↦ x (.inr (.inr (.inr g)))
/-- The coordinate coefficients `γ` at a point. -/
noncomputable def γOf (Γ : Coeffs F G nC) (x : LookupVar S G nT m → F) : Fin nC ⊕ Unit → F :=
  fun i ↦ eval (βOf x) (Γ.poly i)

omit [Field F] [Fintype S] [DecidableEq S] in
@[simp] theorem θOf_lookupPt (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (β : G → F) :
    θOf (lookupPt θ τ μ β) = θ := rfl
omit [Field F] [Fintype S] [DecidableEq S] in
@[simp] theorem τOf_lookupPt (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (β : G → F) :
    τOf (lookupPt θ τ μ β) = τ := rfl
omit [Field F] [Fintype S] [DecidableEq S] in
@[simp] theorem μOf_lookupPt (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (β : G → F) :
    μOf (lookupPt θ τ μ β) = μ := rfl
omit [Field F] [Fintype S] [DecidableEq S] in
@[simp] theorem βOf_lookupPt (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) (β : G → F) :
    βOf (lookupPt θ τ μ β) = β := rfl

namespace Lookup

/-- An access's coefficient `θ_F·eq(τ_F, u)·μ_k` as a polynomial, zero when it is off. -/
noncomputable def coefPoly (G : Type*) (k : S) (u : ℕ) : MvPolynomial (LookupVar S G nT m) F :=
  if L.on k u then
    X (.inl (L.table k)) * rename (fun i ↦ .inr (.inl i)) (eqLowPoly m (L.height k) u) *
      X (.inr (.inr (.inl k)))
  else 0

/-- `Σ_{k,u} coef·Σ_i γ_i·err(k, u)_i` as a polynomial in `(θ, τ, μ, β)`. -/
noncomputable def identityPoly (Γ : Coeffs F G nC) : MvPolynomial (LookupVar S G nT m) F :=
  ∑ k, ∑ u ∈ range (2 ^ L.height k),
    L.coefPoly G k u * ∑ i, rename (fun g ↦ .inr (.inr (.inr g))) (Γ.poly i) * C (L.err k u i)

omit [Fintype S] [DecidableEq S] [Fintype Q] in
theorem eval_coefPoly (x : LookupVar S G nT m → F) (k : S) (u : ℕ) :
    eval x (L.coefPoly G k u) = L.coef (θOf x) (τOf x) (μOf x) k u := by
  unfold coefPoly coef
  split_ifs
  · simp only [map_mul, eval_X, eval_rename, eval_eqLowPoly]
    rfl
  · simp

/-- The polynomial evaluates to the identity's left side at the challenges. -/
theorem eval_identityPoly (Γ : Coeffs F G nC) (x : LookupVar S G nT m → F) :
    eval x (L.identityPoly Γ) = L.identity (θOf x) (τOf x) (μOf x) (γOf Γ x) := by
  rw [identity_eq_sum_err]
  simp only [identityPoly, map_sum, map_mul, eval_coefPoly, eval_rename, eval_C]
  rfl

omit [Fintype S] [DecidableEq S] [Fintype Q] in
theorem totalDegree_coefPoly (k : S) (u : ℕ) : (L.coefPoly G k u).totalDegree ≤ m + 2 := by
  unfold coefPoly
  split_ifs
  · refine (totalDegree_mul _ _).trans ?_
    have h1 := (totalDegree_mul (X (.inl (L.table k)) : MvPolynomial (LookupVar S G nT m) F)
      (rename (fun i ↦ .inr (.inl i)) (eqLowPoly m (L.height k) u))).trans
      (add_le_add (totalDegree_X _).le ((totalDegree_rename_le _ _).trans totalDegree_eqLowPoly))
    have h2 := (totalDegree_X (R := F) (.inr (.inr (.inl k)) : LookupVar S G nT m)).le
    omega
  · simp

/-- The identity's polynomial has total degree at most `m + 2 + ν`. -/
theorem totalDegree_identityPoly (Γ : Coeffs F G nC) : (L.identityPoly Γ).totalDegree ≤ m + 2 + Γ.ν := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ ↦ ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun u _ ↦ ?_)
  refine (totalDegree_mul _ _).trans (add_le_add (L.totalDegree_coefPoly k u) ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  refine (totalDegree_mul _ _).trans ?_
  simpa [totalDegree_C] using (totalDegree_rename_le _ _).trans (Γ.degree_le i)

/-- **Soundness, the polynomial**: if the lookup link fails at some access, the identity's
polynomial is not zero. At `θ = 1`, `μ` the indicator of the failing slot, `τ` the Boolean point of
the failing row and `γ` a point where the coefficients see that access's defect, it evaluates to
`Σ_i γ_i·err_i ≠ 0`. -/
theorem identityPoly_ne_zero (Γ : Coeffs F G nC) (hfail : ¬ L.LinkHolds) : L.identityPoly Γ ≠ 0 := by
  obtain ⟨k₀, u₀, hu₀, hon, hbad⟩ :
      ∃ k u, u < 2 ^ L.height k ∧ L.on k u = true ∧ L.err k u ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hfail fun k u hu hon ↦ (L.err_eq_zero_iff k u).mp (hall k u hu hon)
  obtain ⟨y, hy⟩ := Γ.separates _ hbad
  intro hz
  have h := congrArg (eval (lookupPt (fun _ ↦ 1) (bitPt u₀) (fun k ↦ if k = k₀ then 1 else 0) y)) hz
  rw [map_zero, eval_identityPoly, identity_eq_sum_err] at h
  simp only [θOf_lookupPt, τOf_lookupPt, μOf_lookupPt] at h
  rw [sum_eq_single_of_mem k₀ (mem_univ _) (fun k _ hk ↦ sum_eq_zero fun u _ ↦ by simp [coef, hk])] at h
  rw [sum_eq_single_of_mem u₀ (mem_range.mpr hu₀) (fun u hu hne ↦ by
    simp [coef, eqLow_bitPt (L.height_le k₀) (mem_range.mp hu) hu₀, hne])] at h
  simp only [coef, hon, ite_true, eqLow_bitPt (L.height_le k₀) hu₀ hu₀, one_mul, mul_one] at h
  exact hy h

/-- **Schwartz-Zippel for the lookup**: if the lookup link fails, the identity holds at no more than
`(m + 2 + ν)·|F|^(n − 1)` of the `|F|^n` challenge points `(θ, τ, μ, β)`, `n = n_T + m + |S| + |G|`. -/
theorem card_identity_zero_le [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    (Γ : Coeffs F G nC) (hfail : ¬ L.LinkHolds) :
    (univ.filter fun x : LookupVar S G nT m → F ↦
        L.identity (θOf x) (τOf x) (μOf x) (γOf Γ x) = 0).card ≤
      (m + 2 + Γ.ν) * Fintype.card F ^ (nT + m + Fintype.card S + Fintype.card G - 1) := by
  have h := card_zeros_le_of_totalDegree_le _ (L.identityPoly_ne_zero Γ hfail) (L.totalDegree_identityPoly Γ)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  refine le_of_eq_of_le (congrArg card (filter_congr fun x _ ↦ ?_)) (h.trans_eq ?_)
  · rw [eval_identityPoly]
  · simp only [add_assoc]

end Lookup

end Poly

namespace Lookup

/-- With independent coordinate coefficients (`γ_c` per column and `γ_★`, as the Rust draws
them), a failed link passes the identity at no more than `(m + 3)·|F|^(n − 1)` points. -/
theorem card_identity_zero_le_independent [Fintype F] [DecidableEq F] (hfail : ¬ L.LinkHolds) :
    (univ.filter fun x : LookupVar S (Fin nC ⊕ Unit) nT m → F ↦
        L.identity (θOf x) (τOf x) (μOf x) (βOf x) = 0).card ≤
      (m + 3) * Fintype.card F ^ (nT + m + Fintype.card S + (nC + 1) - 1) := by
  have h := L.card_identity_zero_le (Coeffs.independent nC) hfail
  have hγ : ∀ x : LookupVar S (Fin nC ⊕ Unit) nT m → F, γOf (Coeffs.independent nC) x = βOf x :=
    fun x ↦ funext fun i ↦ eval_X (f := βOf x) i
  simp only [hγ, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h
  exact h

/-- With `γ_i = eq(β, idx i)` over `2^ν` indices, a failed link passes the identity at no more
than `(m + 2 + ν)·|F|^(n − 1)` points. -/
theorem card_identity_zero_le_eqWeights [Fintype F] [DecidableEq F] (ν : ℕ) (idx : Fin nC ⊕ Unit → ℕ)
    (hinj : Function.Injective idx) (hlt : ∀ i, idx i < 2 ^ ν) (hfail : ¬ L.LinkHolds) :
    (univ.filter fun x : LookupVar S (Fin ν) nT m → F ↦
        L.identity (θOf x) (τOf x) (μOf x) (fun i ↦ eqLow ν (βOf x) (idx i)) = 0).card ≤
      (m + 2 + ν) * Fintype.card F ^ (nT + m + Fintype.card S + ν - 1) := by
  have h := L.card_identity_zero_le (Coeffs.eqWeights nC ν idx hinj hlt) hfail
  have hγ : ∀ x : LookupVar S (Fin ν) nT m → F,
      γOf (Coeffs.eqWeights nC ν idx hinj hlt) x = fun i ↦ eqLow ν (βOf x) (idx i) :=
    fun x ↦ funext fun i ↦ eval_eqLowPoly (βOf x)
  simp only [hγ, Fintype.card_fin] at h
  exact h

end Lookup

/-! ## The window -/

/-- The entry an access at shift `s` names through the pointer `σ`, inside its window of `2^{w_0}`
cells: `σ + s` when `(σ mod 2^{w_0}) + s < 2^{w_0}`, none past the window (the prover's
`Chunks::shifted`). -/
def windowHit (w0 σ s : ℕ) : Option ℕ := if σ % 2 ^ w0 + s < 2 ^ w0 then some (σ + s) else none

/-- A window's entry stays below `2^W`. -/
theorem windowHit_lt {w0 W σ s j : ℕ} (hw : w0 ≤ W) (hσ : σ < 2 ^ W) (h : windowHit w0 σ s = some j) :
    j < 2 ^ W := by
  unfold windowHit at h
  split_ifs at h with hin
  obtain rfl := Option.some.inj h
  have hW : 2 ^ W = 2 ^ w0 * 2 ^ (W - w0) := by rw [← pow_add, Nat.add_sub_cancel' hw]
  have h1 := Nat.mod_add_div σ (2 ^ w0)
  have h2 : σ / 2 ^ w0 < 2 ^ (W - w0) := Nat.div_lt_of_lt_mul (hW ▸ hσ)
  have h3 : 2 ^ w0 * (σ / 2 ^ w0) + 2 ^ w0 ≤ 2 ^ W := by
    rw [hW, ← mul_add_one]
    exact Nat.mul_le_mul_left _ h2
  generalize 2 ^ w0 * (σ / 2 ^ w0) = t at h1 h3
  generalize σ % 2 ^ w0 = a at h1 hin
  generalize 2 ^ w0 = P at hin h3
  generalize 2 ^ W = Q at h3 ⊢
  omega

/-- The row side's read of a window access, `T_s(e_0)·Π_{i ≥ 1} ẽ_i(r_i)` (`Window.lean`), is the
equality weight at the entry it names, `0` when it drops out. -/
theorem window_read_hit (r0 : List F) (rs : List (List F)) (e0 : ℕ → F) (es : List (ℕ → F)) (σ s : ℕ)
    (h : Encodes (r0 :: rs) (e0 :: es) σ) :
    windowShift r0 e0 s * chunksEval rs es = (windowHit r0.length σ s).elim 0 (eqAt (r0 :: rs).flatten) := by
  rw [window_read r0 rs e0 es σ s h, windowHit]
  split_ifs <;> rfl

namespace Lookup

omit [DecidableEq S] [Fintype Q] in
/-- **The access array at the index point is the row side's sum**: when every access is a window
access through one-hot chunks, `Σ_j eq(r, j)·access(j)` is `Σ_{k,u} coef·T_{s_k}(e_0)·Π_{i ≥ 1}
ẽ_i(r_i)`, the slots' shares of the verifier's `Functionals::summand`. -/
theorem sum_eqAt_mul_access (r0 : List F) (rs : List (List F)) (σ : S → ℕ → ℕ) (s : S → ℕ)
    (e0 : S → ℕ → ℕ → F) (es : S → ℕ → List (ℕ → F))
    (hhit : ∀ k, ∀ u < 2 ^ L.height k, L.hit k u = windowHit r0.length (σ k u) (s k))
    (henc : ∀ k, ∀ u < 2 ^ L.height k, Encodes (r0 :: rs) (e0 k u :: es k u) (σ k u))
    (θ : Fin nT → F) (τ : Fin m → F) (μ : S → F) :
    ∑ j ∈ range (2 ^ W), eqAt (r0 :: rs).flatten j * L.access θ τ μ j =
      ∑ k, ∑ u ∈ range (2 ^ L.height k),
        L.coef θ τ μ k u * (windowShift r0 (e0 k u) (s k) * chunksEval rs (es k u)) := by
  simp only [mul_comm (eqAt _ _)]
  rw [sum_access_mul]
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun u hu ↦ ?_
  rw [window_read_hit _ _ _ _ _ _ (henc k u (mem_range.mp hu)), hhit k u (mem_range.mp hu)]

end Lookup

end

end LeanVM.Protocol.Hotwire

/-! The lookup link's theorems use Lean's three standard axioms only. -/

/-- info: 'LeanVM.Protocol.Hotwire.Lookup.identity_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.Lookup.identity_eq_zero

/-- info: 'LeanVM.Protocol.Hotwire.Lookup.identity_eq_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.Lookup.identity_eq_plain

/-- info: 'LeanVM.Protocol.Hotwire.Lookup.card_identity_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.Lookup.card_identity_zero_le

/--
info: 'LeanVM.Protocol.Hotwire.Lookup.card_identity_zero_le_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.Lookup.card_identity_zero_le_independent

/--
info: 'LeanVM.Protocol.Hotwire.Lookup.card_identity_zero_le_eqWeights' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.Lookup.card_identity_zero_le_eqWeights

/-- info: 'LeanVM.Protocol.Hotwire.Lookup.sum_eqAt_mul_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Hotwire.Lookup.sum_eqAt_mul_access
