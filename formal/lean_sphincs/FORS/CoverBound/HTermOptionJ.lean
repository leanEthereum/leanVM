import FORS.CoverBound.HTermOption
import FORS.CoverBound.ClassLaw
import FORS.CoverBound.IntTables

/-! **The option of the split by big indices.** An option fixes the cap `c1`, the Chernoff parameters
`θ_0, …, θ_m`, the threshold `cthr`, the number `nb` of views above which an index is big (with
`c2 = κ (nb / A)^k ≥ y` at the other indices, `c2 ≤ c1`), the counts `nx` of views where the per-index
tables read the class law (`CoverBound/ClassLaw.lean`) with overflow `T`, and the bound `B`. The tables
`ḡ ≥ E[(y - c1)^+ | n]`, `ā_j ≥ E[[n > nb] e^{θ_j min(y, c1)} | n]` and
`h̄_j - 1 ≥ E[e^{θ_j min(y, cap_j)} | n] - 1` (`cap_j = c2` for `j < m`, `c1` for `j = m`) are the best of
the support bound `y ≤ κ (n / A)^k`, the class law on `nx` and the moment tables elsewhere; they are
computed in integers (numerators over powers of two, exponentials by `expUpN`), made convex, and
averaged against the Poisson table. The bound is
`B ≥ L E[ḡ] + Σ_j C(L, j) E[ā_j]^j E[h̄_j]^L e^{-θ_j cthr} / (e θ_j)` (`hTermO_le_optJ`). With `m = 0` and
no class law it is the option of `CoverBound/HTermOption.lean` with the support bound added. -/

open ENNReal NNReal

namespace FORS.Security.H0

variable [Params]

open Concrete ForsPrice FORS.Base.H0 FORS.Base.Domination H0Avg

set_option linter.unusedSectionVars false

/-! ### The exponential in integers -/

/-- Iterated squaring of a numerator over `2^P`, rounded up. -/
def sqUpN (P : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | s + 1, x => sqUpN P s ((x * x + (2 ^ P - 1)) / 2 ^ P)

/-- The numerator over `2^P` of an upper bound of `e^(un / ud)`: `(1 - u / 2^s)^(-2^s)`, rounded up. -/
def expUpN (un ud s P : ℕ) : ℕ :=
  sqUpN P s ((2 ^ P * (2 ^ s * ud) + (2 ^ s * ud - un - 1)) / (2 ^ s * ud - un))

/-- The numerator over `2^P` of the bound of `e^u`. -/
def expQN (u : ℚ) (s P : ℕ) : ℕ := expUpN u.num.toNat u.den s P

theorem le_ceilDiv' (a d : ℕ) (hd : 0 < d) : (a : ℝ) / d ≤ (((a + (d - 1)) / d : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast le_ceilDiv a d hd

theorem sqUpN_ge (P : ℕ) : ∀ (s x : ℕ) (y : ℝ), 0 ≤ y → y ≤ (x : ℝ) / 2 ^ P →
    y ^ (2 ^ s) ≤ (sqUpN P s x : ℝ) / 2 ^ P
  | 0, x, y, _, h => by simpa [sqUpN] using h
  | s + 1, x, y, hy, h => by
      simp only [sqUpN]
      have h2 : y ^ 2 ≤ (((x * x + (2 ^ P - 1)) / 2 ^ P : ℕ) : ℝ) / 2 ^ P := by
        have hx : (0 : ℝ) ≤ (x : ℝ) / 2 ^ P := le_trans hy h
        calc y ^ 2 ≤ ((x : ℝ) / 2 ^ P) ^ 2 := pow_le_pow_left₀ hy h 2
          _ = ((x * x : ℕ) : ℝ) / ((2 ^ P : ℕ) : ℝ) / 2 ^ P := by push_cast; ring
          _ ≤ _ := by
              gcongr
              exact le_ceilDiv' (x * x) (2 ^ P) (Nat.two_pow_pos P)
      have := sqUpN_ge P s _ (y ^ 2) (by positivity) h2
      rw [← pow_mul, ← pow_succ'] at this
      exact this

/-- **`e^(un / ud) ≤ expUpN un ud s P / 2^P`** for `un < 2^s ud`. -/
theorem exp_le_expUpN (un ud s P : ℕ) (hd : 0 < ud) (hus : un < 2 ^ s * ud) :
    Real.exp ((un : ℝ) / ud) ≤ (expUpN un ud s P : ℝ) / 2 ^ P := by
  set v : ℝ := (un : ℝ) / ud / 2 ^ s with hv
  have hv0 : 0 ≤ v := by positivity
  have hD : (0 : ℝ) < ((2 ^ s * ud - un : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hus
  have hDe : ((2 ^ s * ud - un : ℕ) : ℝ) = 2 ^ s * ud - un := by
    rw [Nat.cast_sub hus.le]; push_cast; ring
  have hv1 : v < 1 := by
    rw [hv, div_div, div_lt_one (by positivity)]
    have : ((un : ℕ) : ℝ) < ((2 ^ s * ud : ℕ) : ℝ) := by exact_mod_cast hus
    push_cast at this
    linarith
  have hexpv : Real.exp v ≤ 1 / (1 - v) := by
    have h := Real.one_sub_le_exp_neg v
    rw [le_div_iff₀ (by linarith)]
    calc Real.exp v * (1 - v) ≤ Real.exp v * Real.exp (-v) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have hround : (1 / (1 - v) : ℝ) ≤
      (((2 ^ P * (2 ^ s * ud) + (2 ^ s * ud - un - 1)) / (2 ^ s * ud - un) : ℕ) : ℝ) / 2 ^ P := by
    have h1 := le_ceilDiv' (2 ^ P * (2 ^ s * ud)) (2 ^ s * ud - un) (Nat.sub_pos_of_lt hus)
    rw [show 2 ^ s * ud - un - 1 = (2 ^ s * ud - un) - 1 by omega]
    rw [le_div_iff₀ (by positivity)]
    refine le_trans (le_of_eq ?_) h1
    rw [hDe, hv]
    have hud : (0 : ℝ) < ud := by exact_mod_cast hd
    have hne : (2 : ℝ) ^ s * ud - un ≠ 0 := by rw [← hDe]; exact hD.ne'
    have h2s : (0 : ℝ) < 2 ^ s := by positivity
    have h1v : 1 - (un : ℝ) / ud / 2 ^ s ≠ 0 := by
      rw [div_div]
      intro h0
      have : (un : ℝ) = ud * 2 ^ s := by
        have hpos : (0 : ℝ) < ud * 2 ^ s := by positivity
        field_simp at h0
        linarith
      apply hne; rw [this]; ring
    push_cast
    field_simp
  have h := sqUpN_ge P s _ (Real.exp v) (Real.exp_pos v).le (le_trans hexpv hround)
  rw [← Real.exp_nat_mul] at h
  unfold expUpN
  convert h using 2
  rw [hv]
  push_cast
  field_simp

/-- `e^u ≤ expQN u s P / 2^P` for `0 ≤ u < 2^s`. -/
theorem exp_le_expQN (u : ℚ) (s P : ℕ) (hu : 0 ≤ u) (hus : u < 2 ^ s) :
    Real.exp (u : ℝ) ≤ (expQN u s P : ℝ) / 2 ^ P := by
  have hnum : (u.num.toNat : ℚ) = u.num := by exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hu)
  have hu' : (u : ℚ) = (u.num.toNat : ℚ) / u.den := by rw [hnum, Rat.num_div_den]
  have hlt : u.num.toNat < 2 ^ s * u.den := by
    have h1 : (u.num.toNat : ℚ) / u.den < 2 ^ s := by rw [← hu']; exact hus
    rw [div_lt_iff₀ (by exact_mod_cast u.den_pos)] at h1
    exact_mod_cast h1
  have h := exp_le_expUpN u.num.toNat u.den s P u.den_pos hlt
  unfold expQN
  refine le_trans (le_of_eq ?_) h
  congr 1
  have h2 : ((u : ℚ) : ℝ) = (((u.num.toNat : ℚ) / u.den : ℚ) : ℝ) := by rw [← hu']
  rw [h2]
  push_cast
  rfl

theorem one_le_expUpN_div (un ud s P : ℕ) (hd : 0 < ud) (hus : un < 2 ^ s * ud) :
    (1 : ℝ) ≤ (expUpN un ud s P : ℝ) / 2 ^ P :=
  le_trans (Real.one_le_exp (by positivity)) (exp_le_expUpN un ud s P hd hus)

/-- The quotient of two naturals, below its numerator rounded up over `2^R`. -/
theorem div_le_cdiv_divR (R : ℕ) {x d : ℕ} (hd : 0 < d) :
    (x : ℝ) / d ≤ ((cdiv (2 ^ R * x) d : ℕ) : ℝ) / 2 ^ R := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ R)]
  calc (x : ℝ) / d * 2 ^ R = ((2 ^ R * x : ℕ) : ℝ) / d := by push_cast; ring
    _ ≤ _ := le_cdiv hd

/-! ### The option -/

/-- An option of the split by big indices: the cap `c1`, the Chernoff parameters `ths = [θ_0, …, θ_m]`,
the threshold `cthr`, `s` squarings for the exponentials, the big-index count `nb`, the counts `nx`
read through the class law with overflow `T`, and the bound `B`. -/
structure OptJ where
  c1 : ℚ
  ths : List ℚ
  cthr : ℚ
  s : ℕ
  nb : ℕ
  nx : List ℕ
  T : ℕ
  B : ℚ

namespace OptJ

/-- The index `m` of the last term. -/
def m (o : OptJ) : ℕ := o.ths.length - 1

/-- `θ_j`. -/
def θ (o : OptJ) (j : ℕ) : ℚ := o.ths.getD j 0

end OptJ

/-- `c2 = κ (nb / A)^k = nb^k / 2^(H + a k)`. -/
def c2Q (H k a nb : ℕ) : ℚ := ((nb ^ k : ℕ) : ℚ) / 2 ^ (H + a * k)

/-- The cap of the `j`-th term off the big set: `c2` for `j < m`, `c1` for `j = m`. -/
def capQ (H k a : ℕ) (o : OptJ) (j : ℕ) : ℚ := if j < o.m then c2Q H k a o.nb else o.c1

/-- The numerator over `2^P` of the bound of `e^{θ min(Y / 2^E, cap)}`. -/
def expAtN (θ cap : ℚ) (E Y s P : ℕ) : ℕ :=
  expUpN (θ.num.toNat * min (Y * cap.den) (cap.num.toNat * 2 ^ E)) (θ.den * 2 ^ E * cap.den) s P

/-- The weights of the classes times `f` at their representatives, plus the overflow: a numerator
over `A^(n k)`. -/
def lawSumN (k a n T : ℕ) (f : ℕ → ℕ) : ℕ :=
  ((lawStates T).map fun p => lawWt k a n p.1 p.2 * f (lawY k n p.1 p.2)).sum +
    ((2 ^ a) ^ (n * k) - lawMass k a n T) * f (lawY k n T 0)

/-- The numerator over `2^191` of the class-law bound of `E[(y - c1)^+ | n]`. -/
def lawGN (H k a n T : ℕ) (c1 : ℚ) : ℕ :=
  cdiv (2 ^ 191 * lawSumN k a n T (fun Y => Y * c1.den - c1.num.toNat * 2 ^ (H + a * k)))
    ((2 ^ a) ^ (n * k) * (2 ^ (H + a * k) * c1.den))

/-- The numerator over `2^128` of the class-law bound of `E[e^{θ min(y, cap)} | n]`. -/
def lawEN (H k a n T s P : ℕ) (θ cap : ℚ) : ℕ :=
  cdiv (2 ^ 128 * lawSumN k a n T (fun Y => expAtN θ cap (H + a * k) Y s P)) ((2 ^ a) ^ (n * k) * 2 ^ P)

/-- The numerator over `2^191` of `ḡ(n)`: zero by the support bound, the class law on `nx`, the moment
tables elsewhere. -/
def gEntryJ (H k a : ℕ) (o : OptJ) (n : ℕ) : ℤ :=
  if n ^ k * o.c1.den ≤ o.c1.num.toNat * 2 ^ (H + a * k) then 0
  else if n ∈ o.nx then (lawGN H k a n o.T o.c1 : ℤ)
  else min (cdivZ (((p1N a n ^ k : ℕ) : ℤ) * 2 ^ 191) (p2 (H + 128 * k)))
    (cdivZ (((p2N a n ^ k * o.c1.den : ℕ) : ℤ) * 2 ^ 191) (p2 (2 * H + 128 * k) * 4 * o.c1.num))

/-- The numerator over `2^P` of the bound of `e^{θ_j c1}`. -/
def eAN (o : OptJ) (P j : ℕ) : ℕ := expQN (o.θ j * o.c1) o.s P

/-- The numerator over `2^P` of the bound of `e^{θ_j cap_j}`. -/
def eHN (H k a : ℕ) (o : OptJ) (P j : ℕ) : ℕ := expQN (o.θ j * capQ H k a o j) o.s P

/-- The numerator over `2^128` of `e^{θ_j cap_j} - 1`, rounded up. -/
def eH1N (H k a : ℕ) (o : OptJ) (P j : ℕ) : ℕ := cdiv (2 ^ 128 * (eHN H k a o P j - 2 ^ P)) (2 ^ P)

/-- The cap of the quadratic bound at `n` views: `U(n) = n^k / 2^(H + a k)` (which bounds `y` there) if
`n ≥ 1` and it is below `cap_j`, else `cap_j`. -/
def zQ (H k a : ℕ) (o : OptJ) (j n : ℕ) : ℚ :=
  if 1 ≤ n ∧ c2Q H k a n < capQ H k a o j then c2Q H k a n else capQ H k a o j

/-- The quadratic coefficient `(e^{θ z} - 1 - θ z) / z^2` at `z = zQ`, rounded up. -/
def A2Jn (H k a : ℕ) (o : OptJ) (P j n : ℕ) : ℚ :=
  rup (((expQN (o.θ j * zQ H k a o j n) o.s P : ℚ) / 2 ^ P - 1 - o.θ j * zQ H k a o j n) / zQ H k a o j n ^ 2)
    (2 * 127 + 64)

/-- The numerator over `2^128` of `ā_j(n)`. -/
def aEntryJ (H k a : ℕ) (o : OptJ) (P j n : ℕ) : ℤ :=
  if n ≤ o.nb then 0
  else if n ∈ o.nx then (lawEN H k a n o.T o.s P (o.θ j) o.c1 : ℤ)
  else (cdiv (2 ^ 128 * eAN o P j) (2 ^ P) : ℤ)

/-- The numerator over `2^128` of `h̄_j(n) - 1`. -/
def hEntryJ (H k a : ℕ) (o : OptJ) (P j n : ℕ) : ℤ :=
  if j < o.m ∧ o.nb < n then (eH1N H k a o P j : ℤ)
  else if n ∈ o.nx then ((lawEN H k a n o.T o.s P (o.θ j) (capQ H k a o j) - 2 ^ 128 : ℕ) : ℤ)
  else min (eH1N H k a o P j : ℤ)
    (cdivZ (((o.θ j).num * (A2Jn H k a o P j n).den * ((p1N a n ^ k : ℕ) : ℤ) * p2 H +
      (A2Jn H k a o P j n).num * (o.θ j).den * ((p2N a n ^ k : ℕ) : ℤ)) * 2 ^ 128)
      ((o.θ j).den * (A2Jn H k a o P j n).den * p2 (2 * H + 128 * k)))

/-- A table of numerators over `n ≤ n1`, made convex. -/
def tabJ (n1 : ℕ) (f : ℕ → ℤ) : List ℤ := convexZ ((List.range (n1 + 1)).map f)

/-- `ḡ` (numerators over `2^191`). -/
def gkJ (H k a : ℕ) (t : PoisT) (o : OptJ) : List ℤ := tabJ t.n1 (gEntryJ H k a o)
def gtJ (H k a : ℕ) (t : PoisT) (o : OptJ) : List ℚ := overP 191 (gkJ H k a t o)
def JgJ (H k a : ℕ) (t : PoisT) (o : OptJ) : ℚ := leafJ t.n1 (gtJ H k a t o) (κQ H)
def EgJ (H b k a : ℕ) (t : PoisT) (o : OptJ) : ℚ :=
  rup (meanZ t 191 (gkJ H k a t o) (JgJ H k a t o)) (64 + 127 + 2 * b)

/-- `ā_j` (numerators over `2^128`). -/
def akJ (H k a : ℕ) (t : PoisT) (o : OptJ) (j : ℕ) : List ℤ := tabJ t.n1 (aEntryJ H k a o t.P j)
def atJ (H k a : ℕ) (t : PoisT) (o : OptJ) (j : ℕ) : List ℚ := overP 128 (akJ H k a t o j)
def JaJ (H k a : ℕ) (t : PoisT) (o : OptJ) (j : ℕ) : ℚ :=
  leafJ t.n1 (atJ H k a t o j) ((eAN o t.P j : ℚ) / 2 ^ t.P)
def EaJ (H b k a : ℕ) (t : PoisT) (o : OptJ) (j : ℕ) : ℚ :=
  rup (meanZ t 128 (akJ H k a t o j) (JaJ H k a t o j)) (64 + 2 * b)

/-- `h̄_j - 1` (numerators over `2^128`). -/
def hkJ (H k a : ℕ) (t : PoisT) (o : OptJ) (j : ℕ) : List ℤ := tabJ t.n1 (hEntryJ H k a o t.P j)
def htJ (H k a : ℕ) (t : PoisT) (o : OptJ) (j : ℕ) : List ℚ := overP 128 (hkJ H k a t o j)
def JhJ (H k a : ℕ) (t : PoisT) (o : OptJ) (j : ℕ) : ℚ :=
  leafJ t.n1 (htJ H k a t o j) ((eHN H k a o t.P j : ℚ) / 2 ^ t.P - 1)
def EhJ (H b k a : ℕ) (t : PoisT) (o : OptJ) (j : ℕ) : ℚ :=
  rup (meanZ t 128 (hkJ H k a t o j) (JhJ H k a t o j)) (64 + 2 * b)

/-- The lower bound of `e^{θ_j cthr}` (`expLow`, in integers). -/
def expLowJ (t : PoisT) (o : OptJ) (j : ℕ) : ℚ :=
  (expLowN (o.θ j * o.cthr).num.toNat (o.θ j * o.cthr).den t.P t.J 0 (2 ^ t.P) 0 : ℚ) / 2 ^ t.P

/-- The `j`-th term: `C(L, j) E[ā_j]^j E[h̄_j]^L e^{-θ_j cthr} / (e θ_j)`, `L = 2^b`. -/
def termJ (H b k a : ℕ) (t : PoisT) (o : OptJ) (j : ℕ) : ℚ :=
  (((2 ^ b).descFactorial j / j.factorial : ℕ) : ℚ) * EaJ H b k a t o j ^ j * sqUp t.P b (1 + EhJ H b k a t o j) /
    (expLowJ t o j * eLowQ * o.θ j)

/-- The bound of the option. -/
def BJ (H b k a : ℕ) (t : PoisT) (o : OptJ) : ℚ :=
  rup (2 ^ b * EgJ H b k a t o + ((List.range (o.m + 1)).map (termJ H b k a t o)).sum) (64 + 127)

/-- The conditions on the scalars and the signs of the tables and of the means. -/
def okJ (H b k a : ℕ) (t : PoisT) (o : OptJ) : Bool :=
  decide (0 < o.c1) && decide (1 ≤ o.ths.length) &&
    decide (∀ j < o.m + 1, 0 < o.θ j ∧ o.θ j * o.c1 < 2 ^ o.s) &&
    decide (0 ≤ o.cthr) && decide (1 ≤ o.nb) &&
    decide (o.nb ^ k * o.c1.den ≤ o.c1.num.toNat * 2 ^ (H + a * k)) &&
    decide (o.T ≤ k) && decide (∀ n ∈ o.nx, 2 ≤ n) && decide (1 ≤ t.n1) && decide (t.n1 ≤ 150) &&
    decide (0 ≤ (gtJ H k a t o).getD 0 0) &&
    decide (∀ j < o.m + 1, 0 ≤ (atJ H k a t o j).getD 0 0 ∧ 0 ≤ (htJ H k a t o j).getD 0 0) &&
    decide (0 ≤ EgJ H b k a t o) && decide (∀ j < o.m + 1, 0 ≤ EaJ H b k a t o j ∧ 0 ≤ EhJ H b k a t o j)

/-- The check of an option against a Poisson table, for subtree height `b`. -/
def checkOptJ (H b k a : ℕ) (t : PoisT) (o : OptJ) : Bool :=
  okJ H b k a t o && decide (BJ H b k a t o ≤ o.B)

theorem okJ_parts {H b k a : ℕ} {t : PoisT} {o : OptJ} (h : okJ H b k a t o = true) :
    0 < o.c1 ∧ 1 ≤ o.ths.length ∧ (∀ j < o.m + 1, 0 < o.θ j ∧ o.θ j * o.c1 < 2 ^ o.s) ∧
      0 ≤ o.cthr ∧ 1 ≤ o.nb ∧ o.nb ^ k * o.c1.den ≤ o.c1.num.toNat * 2 ^ (H + a * k) ∧ o.T ≤ k ∧
      (∀ n ∈ o.nx, 2 ≤ n) ∧ 1 ≤ t.n1 ∧ t.n1 ≤ 150 ∧ 0 ≤ (gtJ H k a t o).getD 0 0 ∧
      (∀ j < o.m + 1, 0 ≤ (atJ H k a t o j).getD 0 0 ∧ 0 ≤ (htJ H k a t o j).getD 0 0) ∧
      0 ≤ EgJ H b k a t o ∧ (∀ j < o.m + 1, 0 ≤ EaJ H b k a t o j ∧ 0 ≤ EhJ H b k a t o j) := by
  simp only [okJ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-! ### The per-index bounds -/

theorem κE_toReal_eq {H b : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) : κE.toReal = 1 / 2 ^ H := by
  rw [κE_toReal H b hH hb, κQ]; push_cast; ring

/-- **The support bound** with `n` views: `y ≤ n^k / 2^(H + a k)`. -/
theorem κy_le_card {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) (Ms : Multiset (FTree → FLeaf)) :
    κE.toReal * (yM Ms).toReal ≤ ((Ms.card ^ k : ℕ) : ℝ) / 2 ^ (H + a * k) := by
  have h := yM_toReal_le_card Ms
  rw [κE_toReal_eq hH hb]
  calc 1 / 2 ^ H * (yM Ms).toReal ≤ 1 / 2 ^ H * ((Ms.card : ℝ) / leavesR) ^ forsTrees := by gcongr
    _ = _ := by
        rw [leavesR, hk, ha, pow_add, div_pow, ← pow_mul]
        push_cast
        field_simp

/-- The representatives of the class law over `2^(H + a k)`. -/
theorem κ_rep {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (Y : ℕ) :
    κE.toReal * (Y : ℝ) / (2 ^ a : ℝ) ^ k = (Y : ℝ) / 2 ^ (H + a * k) := by
  rw [κE_toReal_eq hH hb, pow_add, ← pow_mul]
  field_simp

/-- **The class law in integers.** If `F(Y / 2^(H + a k)) ≤ f(Y) / Q` for every `Y`, the average of `F(y)`
over `n ≥ 2` views is at most `lawSumN f / (A^(n k) Q)`, rounded up over `2^R`. -/
theorem avgN_law_le {H b k a n T : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) (hn : 2 ≤ n) (hT : T ≤ k) (F : ℝ → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hFm : Monotone F)
    (f : ℕ → ℕ) (Q R : ℕ) (hQ : 0 < Q) (hf : ∀ Y : ℕ, F ((Y : ℝ) / 2 ^ (H + a * k)) ≤ (f Y : ℝ) / Q) :
    avgN (fun Ms => ENNReal.ofReal (F (κE.toReal * (yM Ms).toReal))) n 0 ≤
      ENNReal.ofReal (((cdiv (2 ^ R * lawSumN k a n T f) ((2 ^ a) ^ (n * k) * Q) : ℕ) : ℝ) / 2 ^ R) := by
  refine le_trans (avgN_classLaw k a n T hk ha hn hT F hF0 hFm) (ENNReal.ofReal_le_ofReal ?_)
  simp only [mul_div_assoc] at *
  have hrep : ∀ Y : ℕ, F (κE.toReal * ((Y : ℝ) / (2 ^ a : ℝ) ^ k)) ≤ (f Y : ℝ) / Q := fun Y => by
    rw [← mul_div_assoc, κ_rep hH hb]; exact hf Y
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsum : ((lawSumN k a n T f : ℕ) : ℝ) / Q =
      ((lawStates T).map fun p => (lawWt k a n p.1 p.2 : ℝ) * ((f (lawY k n p.1 p.2) : ℝ) / Q)).sum +
        (((2 ^ a) ^ (n * k) - lawMass k a n T : ℕ) : ℝ) * ((f (lawY k n T 0) : ℝ) / Q) := by
    unfold lawSumN
    push_cast [Nat.cast_list_sum, List.map_map]
    rw [add_div]
    congr 1
    · rw [div_eq_mul_inv, ← List.sum_map_mul_right]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      simp only [Function.comp_apply]
      push_cast
      ring
    · ring
  have hD : (0 : ℝ) < (2 ^ a : ℝ) ^ (n * k) := by positivity
  calc (((lawStates T).map fun p => (lawWt k a n p.1 p.2 : ℝ) *
          F (κE.toReal * ((lawY k n p.1 p.2 : ℝ) / (2 ^ a : ℝ) ^ k))).sum +
        (((2 ^ a) ^ (n * k) - lawMass k a n T : ℕ) : ℝ) * F (κE.toReal * ((lawY k n T 0 : ℝ) / (2 ^ a : ℝ) ^ k))) /
        (2 ^ a : ℝ) ^ (n * k) ≤ ((lawSumN k a n T f : ℕ) : ℝ) / Q / (2 ^ a : ℝ) ^ (n * k) := by
        rw [hsum]
        refine div_le_div_of_nonneg_right (add_le_add (List.sum_le_sum fun p _ =>
          mul_le_mul_of_nonneg_left (hrep _) (Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_left (hrep _)
          (Nat.cast_nonneg _))) hD.le
    _ = ((lawSumN k a n T f : ℕ) : ℝ) / (((2 ^ a) ^ (n * k) * Q : ℕ) : ℝ) := by
        push_cast; rw [div_div, mul_comm]
    _ ≤ _ := div_le_cdiv_divR R (by positivity)

/-- `(Y / 2^E - c1)^+` is exactly `(Y c1.den - c1.num 2^E)^+ / (2^E c1.den)`. -/
theorem max_sub_eq_natSub (Y E : ℕ) (c1 : ℚ) (hc : 0 < c1) :
    max ((Y : ℝ) / 2 ^ E - (c1 : ℝ)) 0 =
      ((Y * c1.den - c1.num.toNat * 2 ^ E : ℕ) : ℝ) / ((2 ^ E * c1.den : ℕ) : ℝ) := by
  have hnum : ((c1.num.toNat : ℕ) : ℝ) = (c1.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr hc).le
  have hc1 : (c1 : ℝ) = (c1.num : ℝ) / (c1.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hd : (0 : ℝ) < c1.den := by exact_mod_cast c1.den_pos
  have h2 : (0 : ℝ) < 2 ^ E := by positivity
  rcases le_total (c1.num.toNat * 2 ^ E) (Y * c1.den) with h | h
  · rw [Nat.cast_sub h]
    push_cast
    rw [hnum, hc1, max_eq_left]
    · field_simp
    · rw [sub_nonneg, div_le_div_iff₀ hd h2]
      have : ((c1.num.toNat * 2 ^ E : ℕ) : ℝ) ≤ ((Y * c1.den : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      rw [hnum] at this
      linarith
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, zero_div, max_eq_right]
    rw [sub_nonpos, hc1, div_le_div_iff₀ h2 hd]
    have : ((Y * c1.den : ℕ) : ℝ) ≤ ((c1.num.toNat * 2 ^ E : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    rw [hnum] at this
    linarith

/-- `e^{θ min(Y / 2^E, cap)} ≤ expAtN / 2^P`. -/
theorem exp_le_expAtN (θ cap : ℚ) (E Y s P : ℕ) (hθ : 0 < θ) (hcap : 0 < cap) (hs : θ * cap < 2 ^ s) :
    Real.exp ((θ : ℝ) * min ((Y : ℝ) / 2 ^ E) (cap : ℝ)) ≤ (expAtN θ cap E Y s P : ℝ) / 2 ^ P := by
  have hθn : ((θ.num.toNat : ℕ) : ℝ) = (θ.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr hθ).le
  have hcn : ((cap.num.toNat : ℕ) : ℝ) = (cap.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr hcap).le
  have hθe : (θ : ℝ) = (θ.num : ℝ) / (θ.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hce : (cap : ℝ) = (cap.num : ℝ) / (cap.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hθd : (0 : ℝ) < θ.den := by exact_mod_cast θ.den_pos
  have hcd : (0 : ℝ) < cap.den := by exact_mod_cast cap.den_pos
  have h2 : (0 : ℝ) < 2 ^ E := by positivity
  set un := θ.num.toNat * min (Y * cap.den) (cap.num.toNat * 2 ^ E)
  set ud := θ.den * 2 ^ E * cap.den
  have hud : 0 < ud := by positivity
  have heq : (un : ℝ) / ud = (θ : ℝ) * min ((Y : ℝ) / 2 ^ E) (cap : ℝ) := by
    simp only [un, ud]
    push_cast
    rw [hθn, hcn, hθe, hce, show min ((Y : ℝ) / 2 ^ E) ((cap.num : ℝ) / cap.den) =
      min ((Y : ℝ) * cap.den) ((cap.num : ℝ) * 2 ^ E) / (2 ^ E * cap.den) by
        rw [← min_div_div_right (by positivity)]
        congr 1 <;> field_simp]
    field_simp
  have hlt : un < 2 ^ s * ud := by
    have h1 : (θ : ℝ) * min ((Y : ℝ) / 2 ^ E) (cap : ℝ) ≤ (θ : ℝ) * cap :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by exact_mod_cast hθ.le)
    have h2' : ((θ * cap : ℚ) : ℝ) < ((2 ^ s : ℚ) : ℝ) := by exact_mod_cast hs
    push_cast at h2'
    have h3 : (un : ℝ) / ud < 2 ^ s := by rw [heq]; linarith
    rw [div_lt_iff₀ (by exact_mod_cast hud)] at h3
    exact_mod_cast h3
  rw [← heq]
  exact exp_le_expUpN un ud s P hud hlt

/-! ### The moment bounds in integers -/

/-- The excess part by the moment tables, in integers over `2^191`. -/
theorem avgN_gS_le_mom {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) (c1 : ℚ) (hc1 : 0 < c1) (n : ℕ) (hn : n ≤ 150) :
    avgN (gS (c1 : ℝ)) n 0 ≤ ENNReal.ofReal ((((min (cdivZ (((p1N a n ^ k : ℕ) : ℤ) * 2 ^ 191) (p2 (H + 128 * k)))
      (cdivZ (((p2N a n ^ k * c1.den : ℕ) : ℤ) * 2 ^ 191) (p2 (2 * H + 128 * k) * 4 * c1.num)) : ℤ) : ℚ) /
        2 ^ 191 : ℚ) : ℝ) := by
  subst hk
  subst ha
  have hc1' : (0 : ℝ) < (c1 : ℝ) := by exact_mod_cast hc1
  have hκ := κE_toReal H b hH hb
  have hP1 := Ψ1R_le_tab n hn
  have hP2 := Ψ2R_le_tab n hn
  have hΨ1 : 0 ≤ Ψ1R n := avgNR_nonneg coverAvg_nonneg n 0
  have hΨ2 : 0 ≤ Ψ2R n := avgNR_nonneg (fun X => sq_nonneg _) n 0
  have hlin : avgN (gS (c1 : ℝ)) n 0 ≤
      ENNReal.ofReal ((κQ H * (P1tab forsHeight).getD n 0 ^ forsTrees : ℚ) : ℝ) := by
    calc avgN (gS (c1 : ℝ)) n 0 ≤ avgN (fun Ms => ENNReal.ofReal κE.toReal * yM Ms) n 0 :=
          avgN_mono (fun Ms => gS_le_lin _ hc1' Ms) n 0
      _ = ENNReal.ofReal κE.toReal * ENNReal.ofReal (Ψ1R n) ^ forsTrees := by rw [avgN_const_mul, avgN_yM]
      _ ≤ _ := by
          rw [← ENNReal.ofReal_pow hΨ1, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
          apply ENNReal.ofReal_le_ofReal
          rw [hκ]
          push_cast
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΨ1 hP1 forsTrees) (by unfold κQ; positivity)
  have hsq : avgN (gS (c1 : ℝ)) n 0 ≤
      ENNReal.ofReal ((κQ H ^ 2 * (P2tab forsHeight).getD n 0 ^ forsTrees / (4 * c1) : ℚ) : ℝ) := by
    calc avgN (gS (c1 : ℝ)) n 0 ≤ avgN (fun Ms => ENNReal.ofReal (κE.toReal ^ 2 / (4 * c1)) * yM Ms ^ 2) n 0 :=
          avgN_mono (fun Ms => gS_le_sq _ hc1' Ms) n 0
      _ = ENNReal.ofReal (κE.toReal ^ 2 / (4 * c1)) * ENNReal.ofReal (Ψ2R n) ^ forsTrees := by
          rw [avgN_const_mul, avgN_yM_sq]
      _ ≤ _ := by
          rw [← ENNReal.ofReal_pow hΨ2, ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [hκ]
          push_cast
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΨ2 hP2 forsTrees) (by unfold κQ; positivity)
  have hu : 0 < c1.num := Rat.num_pos.mpr hc1
  have hc1e : (c1 : ℚ) = c1.num / c1.den := (Rat.num_div_den c1).symm
  have hq1 : κQ H * (P1tab forsHeight).getD n 0 ^ forsTrees ≤
      (cdivZ (((p1N forsHeight n ^ forsTrees : ℕ) : ℤ) * 2 ^ 191) (p2 (H + 128 * forsTrees)) : ℚ) / 2 ^ 191 := by
    apply le_cdivZ_div (p2_pos _)
    rw [getD_P1tab _ _ hn, P1Q]
    unfold κQ; simp only [tab_pow]; push_cast; field_simp; ring
  have hq2 : κQ H ^ 2 * (P2tab forsHeight).getD n 0 ^ forsTrees / (4 * c1) ≤
      (cdivZ (((p2N forsHeight n ^ forsTrees * c1.den : ℕ) : ℤ) * 2 ^ 191)
        (p2 (2 * H + 128 * forsTrees) * 4 * c1.num) : ℚ) / 2 ^ 191 := by
    apply le_cdivZ_div (mul_pos (mul_pos (p2_pos _) (by norm_num)) hu)
    rw [getD_P2tab _ _ hn, P2Q]
    conv_lhs => rw [hc1e]
    unfold κQ; simp only [tab_pow]; push_cast
    have : (0 : ℚ) < c1.num := by exact_mod_cast hu
    have : (0 : ℚ) < c1.den := by exact_mod_cast c1.den_pos
    field_simp; ring
  rw [min_overP]
  rcases min_choice ((cdivZ (((p1N forsHeight n ^ forsTrees : ℕ) : ℤ) * 2 ^ 191) (p2 (H + 128 * forsTrees)) : ℚ) /
      2 ^ 191) ((cdivZ (((p2N forsHeight n ^ forsTrees * c1.den : ℕ) : ℤ) * 2 ^ 191)
        (p2 (2 * H + 128 * forsTrees) * 4 * c1.num) : ℚ) / 2 ^ 191) with h | h <;> rw [h]
  · exact le_trans hlin (ENNReal.ofReal_le_ofReal ((Rat.cast_le (K := ℝ)).mpr hq1))
  · exact le_trans hsq (ENNReal.ofReal_le_ofReal ((Rat.cast_le (K := ℝ)).mpr hq2))

/-- The Chernoff factor by the moment tables, in integers over `2^128`. -/
theorem avgN_hS_le_mom {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) (cap θ A2 : ℚ) (hcap : 0 < cap) (hθ : 0 < θ)
    (hA2 : (Real.exp ((θ : ℝ) * cap) - 1 - (θ : ℝ) * cap) / (cap : ℝ) ^ 2 ≤ (A2 : ℝ)) (n : ℕ) (hn : n ≤ 150) :
    avgN (hS (cap : ℝ) (θ : ℝ)) n 0 ≤ 1 + ENNReal.ofReal ((((cdivZ ((θ.num * A2.den * ((p1N a n ^ k : ℕ) : ℤ) * p2 H +
      A2.num * θ.den * ((p2N a n ^ k : ℕ) : ℤ)) * 2 ^ 128) (θ.den * A2.den * p2 (2 * H + 128 * k)) : ℤ) : ℚ) /
        2 ^ 128 : ℚ) : ℝ) := by
  subst hk
  subst ha
  have hcap' : (0 : ℝ) < (cap : ℝ) := by exact_mod_cast hcap
  have hθ' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ
  have hκ := κE_toReal H b hH hb
  have hκ0 : (0 : ℝ) ≤ (κQ H : ℝ) := by unfold κQ; positivity
  have hP1 := Ψ1R_le_tab n hn
  have hP2 := Ψ2R_le_tab n hn
  have hΨ1 : 0 ≤ Ψ1R n := avgNR_nonneg coverAvg_nonneg n 0
  have hΨ2 : 0 ≤ Ψ2R n := avgNR_nonneg (fun X => sq_nonneg _) n 0
  set A2r : ℝ := (Real.exp ((θ : ℝ) * cap) - 1 - (θ : ℝ) * cap) / (cap : ℝ) ^ 2 with hA2r
  have hA2r0 : 0 ≤ A2r := by
    have := Real.add_one_le_exp ((θ : ℝ) * cap)
    exact div_nonneg (by linarith) (by positivity)
  have hA20 : (0 : ℝ) ≤ (A2 : ℝ) := le_trans hA2r0 hA2
  have hquad : avgN (hS (cap : ℝ) (θ : ℝ)) n 0 ≤
      1 + ENNReal.ofReal ((θ * κQ H * (P1tab forsHeight).getD n 0 ^ forsTrees +
        A2 * κQ H ^ 2 * (P2tab forsHeight).getD n 0 ^ forsTrees : ℚ) : ℝ) := by
    calc avgN (hS (cap : ℝ) (θ : ℝ)) n 0 ≤ avgN (fun Ms => 1 + ENNReal.ofReal ((θ : ℝ) * κE.toReal) * yM Ms +
          ENNReal.ofReal (A2r * κE.toReal ^ 2) * yM Ms ^ 2) n 0 :=
          avgN_mono (fun Ms => hS_le_quad _ _ hcap' hθ' Ms) n 0
      _ = 1 + ENNReal.ofReal ((θ : ℝ) * κE.toReal) * ENNReal.ofReal (Ψ1R n) ^ forsTrees +
          ENNReal.ofReal (A2r * κE.toReal ^ 2) * ENNReal.ofReal (Ψ2R n) ^ forsTrees := by
          rw [avgN_add, avgN_add, avgN_const, avgN_const_mul, avgN_const_mul, avgN_yM, avgN_yM_sq]
      _ ≤ _ := by
          rw [add_assoc]
          refine add_le_add le_rfl ?_
          rw [← ENNReal.ofReal_pow hΨ1, ← ENNReal.ofReal_pow hΨ2, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [hκ]
          push_cast
          have h1 := pow_le_pow_left₀ hΨ1 hP1 forsTrees
          have h2 := pow_le_pow_left₀ hΨ2 hP2 forsTrees
          have hP20 : (0 : ℝ) ≤ Ψ2R n ^ forsTrees := by positivity
          apply add_le_add
          · rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hκ0) hθ'.le
          · calc A2r * (κQ H : ℝ) ^ 2 * Ψ2R n ^ forsTrees ≤ (A2 : ℝ) * (κQ H : ℝ) ^ 2 * Ψ2R n ^ forsTrees := by
                  gcongr
              _ ≤ _ := by gcongr
  refine le_trans hquad (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hθe : (θ : ℚ) = θ.num / θ.den := (Rat.num_div_den θ).symm
  have hAe : (A2 : ℚ) = A2.num / A2.den := (Rat.num_div_den A2).symm
  have hq : θ * κQ H * (P1tab forsHeight).getD n 0 ^ forsTrees + A2 * κQ H ^ 2 * (P2tab forsHeight).getD n 0 ^ forsTrees ≤
      (cdivZ ((θ.num * A2.den * ((p1N forsHeight n ^ forsTrees : ℕ) : ℤ) * p2 H +
        A2.num * θ.den * ((p2N forsHeight n ^ forsTrees : ℕ) : ℤ)) * 2 ^ 128)
        (θ.den * A2.den * p2 (2 * H + 128 * forsTrees)) : ℚ) / 2 ^ 128 := by
    apply le_cdivZ_div (mul_pos (mul_pos (by exact_mod_cast θ.den_pos) (by exact_mod_cast A2.den_pos)) (p2_pos _))
    rw [getD_P1tab _ _ hn, getD_P2tab _ _ hn, P1Q, P2Q]
    conv_lhs => rw [hθe, hAe]
    unfold κQ; simp only [tab_pow]; push_cast
    have : (0 : ℚ) < θ.den := by exact_mod_cast θ.den_pos
    have : (0 : ℚ) < A2.den := by exact_mod_cast A2.den_pos
    field_simp; ring
  exact (Rat.cast_le (K := ℝ)).mpr hq

/-! ### The entries of the tables -/

/-- `N / 2^E ≤ c1` from its integer form. -/
theorem nat_div_le_of {N E : ℕ} {c1 : ℚ} (hc : 0 < c1) (h : N * c1.den ≤ c1.num.toNat * 2 ^ E) :
    (N : ℝ) / 2 ^ E ≤ (c1 : ℝ) := by
  have hnum : ((c1.num.toNat : ℕ) : ℝ) = (c1.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr hc).le
  have hc1 : (c1 : ℝ) = (c1.num : ℝ) / (c1.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hd : (0 : ℝ) < c1.den := by exact_mod_cast c1.den_pos
  have h' : ((N * c1.den : ℕ) : ℝ) ≤ ((c1.num.toNat * 2 ^ E : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  rw [hnum] at h'
  rw [hc1, div_le_div_iff₀ (by positivity) hd]
  linarith

theorem ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

theorem gS_eq_F (c1 : ℝ) : gS c1 = fun Ms => ENNReal.ofReal ((fun x => max (x - c1) 0) (κE.toReal * (yM Ms).toReal)) := by
  funext Ms
  unfold gS
  rw [ofReal_max_zero]

theorem expMin_mono (θ cap : ℝ) (hθ : 0 ≤ θ) : Monotone fun x : ℝ => Real.exp (θ * min x cap) :=
  fun _ _ h => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (min_le_min_right _ h) hθ)

theorem aS_le_hS (c1 θ : ℝ) (nb : ℕ) (Ms : Multiset (FTree → FLeaf)) : aS c1 θ nb Ms ≤ hS c1 θ Ms := by
  unfold aS; split_ifs <;> simp

theorem avgN_zero_of_card {φ : Multiset (FTree → FLeaf) → ℝ≥0∞} {n : ℕ}
    (h : ∀ Ms : Multiset (FTree → FLeaf), Ms.card = n → φ Ms = 0) : avgN φ n 0 = 0 := by
  refine le_antisymm (le_trans (avgN_mono_card n 0 (ψ := fun _ => 0) fun Ms hMs => ?_) (le_of_eq (avgN_const 0 n 0)))
    (by simp)
  rw [h Ms (by simpa using hMs)]

/-- `x / D ≤ 1 + (x - D) / D`. -/
theorem div_le_one_add_sub (x D : ℕ) (hD : 0 < D) : (x : ℝ) / D ≤ 1 + ((x - D : ℕ) : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rcases le_total D x with h | h
  · rw [Nat.cast_sub h, _root_.sub_div, div_self hD'.ne']
    linarith
  · have h1 : (x : ℝ) / D ≤ 1 := by
      rw [div_le_one hD']
      exact_mod_cast h
    have h0 : (0 : ℝ) ≤ ((x - D : ℕ) : ℝ) / D := div_nonneg (Nat.cast_nonneg _) hD'.le
    linarith

/-- The facts on the scalars that the bounds use. -/
theorem okJ_facts {H b k a : ℕ} {t : PoisT} {o : OptJ} (ho : okJ H b k a t o = true) (j : ℕ) (hj : j < o.m + 1) :
    0 < o.c1 ∧ 0 < o.θ j ∧ 0 < capQ H k a o j ∧ capQ H k a o j ≤ o.c1 ∧ o.θ j * o.c1 < 2 ^ o.s ∧
      o.θ j * capQ H k a o j < 2 ^ o.s := by
  obtain ⟨hc1, -, hθs, -, hnb, hc2, -⟩ := okJ_parts ho
  obtain ⟨hθ, hs⟩ := hθs j hj
  have hc2pos : 0 < c2Q H k a o.nb := by unfold c2Q; have : 0 < o.nb ^ k := Nat.pow_pos hnb; positivity
  have hc2le : c2Q H k a o.nb ≤ o.c1 := by
    have := nat_div_le_of hc1 hc2
    have h' : ((c2Q H k a o.nb : ℚ) : ℝ) ≤ (o.c1 : ℝ) := by unfold c2Q; push_cast at this ⊢; exact this
    exact (Rat.cast_le (K := ℝ)).mp h'
  have hcap0 : 0 < capQ H k a o j := by unfold capQ; split_ifs <;> assumption
  have hcap1 : capQ H k a o j ≤ o.c1 := by unfold capQ; split_ifs <;> [exact hc2le; exact le_rfl]
  exact ⟨hc1, hθ, hcap0, hcap1, hs, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcap1 hθ.le) hs⟩

/-- **The entries of `ḡ`.** -/
theorem avgN_gS_le_entry {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) {t : PoisT} {o : OptJ} (ho : okJ H b k a t o = true) (n : ℕ) (hn : n ≤ 150) :
    avgN (gS (o.c1 : ℝ)) n 0 ≤ ENNReal.ofReal ((((gEntryJ H k a o n : ℤ) : ℚ) / 2 ^ 191 : ℚ) : ℝ) := by
  obtain ⟨hc1, -, -, -, -, -, hT, hnx, -⟩ := okJ_parts ho
  unfold gEntryJ
  split_ifs with h1 h2
  · rw [avgN_zero_of_card fun Ms hMs => ?_]
    · positivity
    unfold gS
    rw [ENNReal.ofReal_eq_zero, sub_nonpos]
    refine le_trans (κy_le_card hH hb hk ha Ms) ?_
    rw [hMs]
    exact nat_div_le_of hc1 h1
  · rw [gS_eq_F]
    refine le_trans (avgN_law_le hH hb hk ha (hnx n h2) hT (fun x => max (x - (o.c1 : ℝ)) 0)
      (fun _ => le_max_right _ _) (fun _ _ h => max_le_max (sub_le_sub_right h _) le_rfl)
      (fun Y => Y * o.c1.den - o.c1.num.toNat * 2 ^ (H + a * k)) (2 ^ (H + a * k) * o.c1.den) 191
      (by positivity) (fun Y => le_of_eq (max_sub_eq_natSub Y _ o.c1 hc1))) (le_of_eq ?_)
    unfold lawGN
    push_cast
    rfl
  · exact avgN_gS_le_mom hH hb hk ha o.c1 hc1 n hn

/-- **The entries of `ā_j`.** -/
theorem avgN_aS_le_entry {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) {t : PoisT} {o : OptJ} (ho : okJ H b k a t o = true) (j : ℕ) (hj : j < o.m + 1)
    (n : ℕ) :
    avgN (aS (o.c1 : ℝ) (o.θ j : ℝ) o.nb) n 0 ≤
      ENNReal.ofReal ((((aEntryJ H k a o t.P j n : ℤ) : ℚ) / 2 ^ 128 : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, hT, hnx, -⟩ := okJ_parts ho
  obtain ⟨hc1, hθ, -, -, hs, -⟩ := okJ_facts ho j hj
  have hθ' : (0 : ℝ) ≤ (o.θ j : ℝ) := by exact_mod_cast hθ.le
  unfold aEntryJ
  split_ifs with h1 h2
  · rw [avgN_zero_of_card fun Ms hMs => ?_]
    · positivity
    unfold aS
    rw [if_neg (by omega)]
  · refine le_trans (avgN_mono (aS_le_hS _ _ _) n 0) ?_
    refine le_trans (avgN_law_le hH hb hk ha (hnx n h2) hT (fun x => Real.exp ((o.θ j : ℝ) * min x (o.c1 : ℝ)))
      (fun _ => (Real.exp_pos _).le) (expMin_mono _ _ hθ') (fun Y => expAtN (o.θ j) o.c1 (H + a * k) Y o.s t.P)
      (2 ^ t.P) 128 (by positivity) (fun Y => ?_)) (le_of_eq ?_)
    · have := exp_le_expAtN (o.θ j) o.c1 (H + a * k) Y o.s t.P hθ hc1 hs
      push_cast
      exact this
    · unfold lawEN
      push_cast
      rfl
  · have hcap : ∀ Ms, aS (o.c1 : ℝ) (o.θ j : ℝ) o.nb Ms ≤ ENNReal.ofReal (Real.exp ((o.θ j : ℝ) * o.c1)) :=
      fun Ms => le_trans (aS_le_hS _ _ _ Ms) (hS_le_cap _ _ (by exact_mod_cast hθ) Ms)
    refine le_trans (avgN_mono hcap n 0) ?_
    rw [avgN_const]
    apply ENNReal.ofReal_le_ofReal
    have he := exp_le_expQN (o.θ j * o.c1) o.s t.P (by positivity) hs
    have hc := div_le_cdiv_divR 128 (x := eAN o t.P j) (d := 2 ^ t.P) (by positivity)
    unfold eAN at hc ⊢
    push_cast at he hc ⊢
    linarith

/-- `e^{θ_j cap_j} ≤ 1 + eH1N / 2^128`. -/
theorem exp_cap_le {H b k a : ℕ} {t : PoisT} {o : OptJ} (ho : okJ H b k a t o = true) (j : ℕ) (hj : j < o.m + 1) :
    Real.exp ((o.θ j : ℝ) * (capQ H k a o j : ℝ)) ≤ 1 + (eH1N H k a o t.P j : ℝ) / 2 ^ 128 := by
  obtain ⟨-, hθ, hcap, -, -, hs⟩ := okJ_facts ho j hj
  unfold eH1N eHN
  set X := expQN (o.θ j * capQ H k a o j) o.s t.P with hX
  have he : Real.exp ((o.θ j : ℝ) * (capQ H k a o j : ℝ)) ≤ (X : ℝ) / 2 ^ t.P := by
    have := exp_le_expQN (o.θ j * capQ H k a o j) o.s t.P (by positivity) hs
    rw [← hX] at this
    push_cast at this
    exact this
  have h1 : 2 ^ t.P ≤ X := by
    have h0 := Real.one_le_exp (by positivity : (0 : ℝ) ≤ (o.θ j : ℝ) * capQ H k a o j)
    have h2 : (1 : ℝ) ≤ (X : ℝ) / 2 ^ t.P := le_trans h0 he
    rw [le_div_iff₀ (by positivity), one_mul] at h2
    exact_mod_cast h2
  have hc := div_le_cdiv_divR 128 (x := X - 2 ^ t.P) (d := 2 ^ t.P) (by positivity)
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat] at hc
  have : (X : ℝ) / 2 ^ t.P = 1 + ((X : ℝ) - 2 ^ t.P) / 2 ^ t.P := by
    field_simp; ring
  linarith

/-- **The entries of `h̄_j - 1`.** -/
theorem avgN_hS_le_entry {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) {t : PoisT} {o : OptJ} (ho : okJ H b k a t o = true) (j : ℕ) (hj : j < o.m + 1)
    (n : ℕ) (hn : n ≤ 150) :
    avgN (hS (capQ H k a o j : ℝ) (o.θ j : ℝ)) n 0 ≤
      1 + ENNReal.ofReal ((((hEntryJ H k a o t.P j n : ℤ) : ℚ) / 2 ^ 128 : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, hT, hnx, -⟩ := okJ_parts ho
  obtain ⟨hc1, hθ, hcap, hcapc1, hs1, hs⟩ := okJ_facts ho j hj
  have hθ' : (0 : ℝ) ≤ (o.θ j : ℝ) := by exact_mod_cast hθ.le
  -- the cap
  have hcapb : avgN (hS (capQ H k a o j : ℝ) (o.θ j : ℝ)) n 0 ≤
      1 + ENNReal.ofReal ((((eH1N H k a o t.P j : ℤ) : ℚ) / 2 ^ 128 : ℚ) : ℝ) := by
    refine le_trans (avgN_mono (hS_le_cap _ _ (by exact_mod_cast hθ)) n 0) ?_
    rw [avgN_const, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := exp_cap_le ho j hj
    push_cast
    exact this
  unfold hEntryJ
  split_ifs with h1 h2
  · exact hcapb
  · refine le_trans (avgN_law_le hH hb hk ha (hnx n h2) hT
      (fun x => Real.exp ((o.θ j : ℝ) * min x (capQ H k a o j : ℝ)))
      (fun _ => (Real.exp_pos _).le) (expMin_mono _ _ hθ')
      (fun Y => expAtN (o.θ j) (capQ H k a o j) (H + a * k) Y o.s t.P)
      (2 ^ t.P) 128 (by positivity) (fun Y => ?_)) ?_
    · have := exp_le_expAtN (o.θ j) (capQ H k a o j) (H + a * k) Y o.s t.P hθ hcap hs
      push_cast
      exact this
    · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (Rat.cast_nonneg.mpr (div_nonneg
        (Int.cast_nonneg (Int.natCast_nonneg _)) (pow_nonneg (by norm_num) _)))]
      apply ENNReal.ofReal_le_ofReal
      have := div_le_one_add_sub (lawEN H k a n o.T o.s t.P (o.θ j) (capQ H k a o j)) (2 ^ 128)
        (Nat.two_pow_pos 128)
      rw [Nat.cast_pow, Nat.cast_ofNat] at this
      unfold lawEN at this ⊢
      push_cast at this ⊢
      exact this
  · -- the moments, with the cap `z = zQ`
    set A2 := A2Jn H k a o t.P j n
    have hz0 : 0 < zQ H k a o j n := by
      unfold zQ
      split_ifs with hn1
      · unfold c2Q; have : 0 < n ^ k := Nat.pow_pos hn1.1; positivity
      · exact hcap
    have hzc : zQ H k a o j n ≤ capQ H k a o j := by
      unfold zQ; split_ifs with hn1
      · exact hn1.2.le
      · exact le_rfl
    have hzs : o.θ j * zQ H k a o j n < 2 ^ o.s := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hzc hθ.le) hs
    have hA2 : (Real.exp ((o.θ j : ℝ) * zQ H k a o j n) - 1 - (o.θ j : ℝ) * zQ H k a o j n) /
        ((zQ H k a o j n : ℚ) : ℝ) ^ 2 ≤ (A2 : ℝ) := by
      have he := exp_le_expQN (o.θ j * zQ H k a o j n) o.s t.P (by positivity) hzs
      have hr0 : ((expQN (o.θ j * zQ H k a o j n) o.s t.P : ℚ) / 2 ^ t.P - 1 - o.θ j * zQ H k a o j n) /
          zQ H k a o j n ^ 2 ≤ A2 := le_rup _ _
      have hr := (Rat.cast_le (K := ℝ)).mpr hr0
      push_cast at he hr
      refine le_trans ?_ hr
      have hc0 : (0 : ℝ) < ((zQ H k a o j n : ℚ) : ℝ) ^ 2 := by
        have : (0 : ℝ) < ((zQ H k a o j n : ℚ) : ℝ) := by exact_mod_cast hz0
        positivity
      apply div_le_div_of_nonneg_right _ hc0.le
      linarith
    -- with `n` views `y ≤ U(n)`, so the cap `z` gives the same factor
    have hzeq : avgN (hS (capQ H k a o j : ℝ) (o.θ j : ℝ)) n 0 ≤ avgN (hS (zQ H k a o j n : ℝ) (o.θ j : ℝ)) n 0 := by
      refine avgN_mono_card n 0 fun Ms hMs => le_of_eq ?_
      rw [Multiset.card_zero, add_zero] at hMs
      unfold hS
      congr 3
      unfold zQ
      split_ifs with hn1
      · have hy : κE.toReal * (yM Ms).toReal ≤ ((c2Q H k a n : ℚ) : ℝ) := by
          refine le_trans (κy_le_card hH hb hk ha Ms) ?_
          rw [hMs]; unfold c2Q; push_cast; exact le_rfl
        have hlt : ((c2Q H k a n : ℚ) : ℝ) < ((capQ H k a o j : ℚ) : ℝ) := by exact_mod_cast hn1.2
        rw [min_eq_left (hy.trans hlt.le), min_eq_left hy]
      · rfl
    have hmom := le_trans hzeq (avgN_hS_le_mom hH hb hk ha (zQ H k a o j n) (o.θ j) A2 hz0 hθ hA2 n hn)
    rw [Int.cast_min, ← min_div_div_right (by positivity)]
    rcases min_choice (((eH1N H k a o t.P j : ℤ) : ℚ) / 2 ^ 128)
      (((cdivZ (((o.θ j).num * A2.den * ((p1N a n ^ k : ℕ) : ℤ) * p2 H +
        A2.num * (o.θ j).den * ((p2N a n ^ k : ℕ) : ℤ)) * 2 ^ 128)
        ((o.θ j).den * A2.den * p2 (2 * H + 128 * k)) : ℤ) : ℚ) / 2 ^ 128) with h | h <;> rw [h]
    · exact hcapb
    · exact hmom

/-! ### The tables -/

/-- A convex table of entry bounds, extended with the slope to its cap, bounds an average at every
count of views. -/
theorem avgN_le_tab {φ : Multiset (FTree → FLeaf) → ℝ≥0∞} (c0 : ℝ≥0∞) {n1 P : ℕ} (f : ℕ → ℤ) (cap : ℚ)
    (h1 : 1 ≤ n1) (h0 : 0 ≤ (overP P (convexZ ((List.range (n1 + 1)).map f))).getD 0 0)
    (hent : ∀ n < n1 + 1, avgN φ n 0 ≤ c0 + ENNReal.ofReal ((((f n : ℤ) : ℚ) / 2 ^ P : ℚ) : ℝ))
    (hcap : ∀ n, avgN φ n 0 ≤ c0 + ENNReal.ofReal ((cap : ℚ) : ℝ)) (n : ℕ) :
    avgN φ n 0 ≤ c0 + ENNReal.ofReal ((leafQ (overP P (convexZ ((List.range (n1 + 1)).map f)))
      (leafJ n1 (overP P (convexZ ((List.range (n1 + 1)).map f))) cap) n : ℚ) : ℝ) := by
  set ks := (List.range (n1 + 1)).map f with hks
  have hl : ks.length = n1 + 1 := by rw [hks, List.length_map, List.length_range]
  have hlo : (overP P (convexZ ks)).length = n1 + 1 := by rw [length_overP, length_convexZ, hl]
  have hlg := checkLeaf_overP (P := P) hl h1 h0 cap
  by_cases hn : n < n1 + 1
  · rw [leafQ_of_lt (by omega)]
    refine le_trans (hent n hn) (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ((Rat.cast_le (K := ℝ)).mpr ?_)))
    refine le_overP (by omega) (le_of_eq ?_)
    rw [hks, getD_map_range _ _ _ _ hn]
  · refine le_trans (hcap n) (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ((Rat.cast_le (K := ℝ)).mpr ?_)))
    have h := leafQ_ge_end hlg (n := n) (by omega)
    rw [hlo, show n1 + 1 - 1 = n1 by omega] at h
    exact le_trans (le_leafJ _ _ _) h

/-- **The table `ḡ`.** -/
theorem avgN_gS_le_tabJ {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) {t : PoisT} {o : OptJ} (ho : okJ H b k a t o = true) (n : ℕ) :
    avgN (gS (o.c1 : ℝ)) n 0 ≤ ENNReal.ofReal ((leafQ (gtJ H k a t o) (JgJ H k a t o) n : ℚ) : ℝ) := by
  obtain ⟨hc1, -, -, -, -, -, -, -, h1, h150, hg0, -⟩ := okJ_parts ho
  have hc1' : (0 : ℝ) < (o.c1 : ℝ) := by exact_mod_cast hc1
  have h := avgN_le_tab (φ := gS (o.c1 : ℝ)) 0 (P := 191) (gEntryJ H k a o) (κQ H) h1 hg0
    (fun n hn => by rw [zero_add]; exact avgN_gS_le_entry hH hb hk ha ho n (by omega))
    (fun n => by
      rw [zero_add]
      calc avgN (gS (o.c1 : ℝ)) n 0 ≤ avgN (fun _ => ENNReal.ofReal κE.toReal) n 0 :=
            avgN_mono (fun Ms => le_trans (gS_le_lin _ hc1' Ms) (mul_le_of_le_one_right' (yM_le_one Ms))) n 0
        _ = _ := by rw [avgN_const, κE_toReal H b hH hb]) n
  rw [zero_add] at h
  exact h

/-- **The tables `ā_j`.** -/
theorem avgN_aS_le_tabJ {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) {t : PoisT} {o : OptJ} (ho : okJ H b k a t o = true) (j : ℕ) (hj : j < o.m + 1)
    (n : ℕ) :
    avgN (aS (o.c1 : ℝ) (o.θ j : ℝ) o.nb) n 0 ≤
      ENNReal.ofReal ((leafQ (atJ H k a t o j) (JaJ H k a t o j) n : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, -, -, hht0, -⟩ := okJ_parts ho
  obtain ⟨hc1, hθ, -, -, hs, -⟩ := okJ_facts ho j hj
  have h := avgN_le_tab (φ := aS (o.c1 : ℝ) (o.θ j : ℝ) o.nb) 0 (P := 128) (aEntryJ H k a o t.P j)
    ((eAN o t.P j : ℚ) / 2 ^ t.P) h1 (hht0 j hj).1
    (fun n _ => by rw [zero_add]; exact avgN_aS_le_entry hH hb hk ha ho j hj n)
    (fun n => by
      rw [zero_add]
      refine le_trans (avgN_mono (fun Ms => le_trans (aS_le_hS _ _ _ Ms) (hS_le_cap _ _ (by exact_mod_cast hθ) Ms))
        n 0) ?_
      rw [avgN_const]
      apply ENNReal.ofReal_le_ofReal
      have he := exp_le_expQN (o.θ j * o.c1) o.s t.P (by positivity) hs
      unfold eAN
      push_cast at he ⊢
      exact he) n
  rw [zero_add] at h
  exact h

/-- **The tables `h̄_j - 1`.** -/
theorem avgN_hS_le_tabJ {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) {t : PoisT} {o : OptJ} (ho : okJ H b k a t o = true) (j : ℕ) (hj : j < o.m + 1)
    (n : ℕ) :
    avgN (hS (capQ H k a o j : ℝ) (o.θ j : ℝ)) n 0 ≤
      1 + ENNReal.ofReal ((leafQ (htJ H k a t o j) (JhJ H k a t o j) n : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, h150, -, hht0, -⟩ := okJ_parts ho
  obtain ⟨-, hθ, hcap, -, -, hs⟩ := okJ_facts ho j hj
  exact avgN_le_tab (φ := hS (capQ H k a o j : ℝ) (o.θ j : ℝ)) 1 (P := 128) (hEntryJ H k a o t.P j)
    ((eHN H k a o t.P j : ℚ) / 2 ^ t.P - 1) h1 (hht0 j hj).2
    (fun n hn => avgN_hS_le_entry hH hb hk ha ho j hj n (by omega))
    (fun n => by
      refine le_trans (avgN_mono (hS_le_cap _ _ (by exact_mod_cast hθ)) n 0) ?_
      rw [avgN_const]
      have he := exp_le_expQN (o.θ j * capQ H k a o j) o.s t.P (by positivity) hs
      have he1 := Real.one_le_exp (by positivity : (0 : ℝ) ≤ ((o.θ j * capQ H k a o j : ℚ) : ℝ))
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by
        have : (1 : ℝ) ≤ (eHN H k a o t.P j : ℝ) / 2 ^ t.P := by unfold eHN; linarith
        push_cast; linarith)]
      apply ENNReal.ofReal_le_ofReal
      unfold eHN
      push_cast at he ⊢
      linarith) n

/-! ### Soundness -/

theorem sqUp_nonneg_of (P b : ℕ) (x : ℚ) (hx : 0 ≤ x) : 0 ≤ sqUp P b x := by
  have h := sqUp_ge P b x (x : ℝ) (by exact_mod_cast hx) le_rfl
  have h0 : (0 : ℝ) ≤ (x : ℝ) ^ (2 ^ b) := pow_nonneg (by exact_mod_cast hx) _
  exact_mod_cast le_trans h0 h

theorem okJ_cap_eq {H k a : ℕ} (o : OptJ) (j : ℕ) :
    ((capQ H k a o j : ℚ) : ℝ) = if j < o.m then ((c2Q H k a o.nb : ℚ) : ℝ) else (o.c1 : ℝ) := by
  unfold capQ; split_ifs <;> rfl

theorem choose_eq_desc (L j : ℕ) : (L.choose j : ℝ≥0∞) = ((L.descFactorial j / j.factorial : ℕ) : ℝ≥0∞) := by
  rw [Nat.choose_eq_descFactorial_div_factorial]

/-- **One option of the split by big indices bounds the FORS H-term**: `H ≤ B` whenever the rate
`N / 2^b + q λ w / 2^b` is below the table rate and the base `b0` is at least the threshold `cthr`. -/
theorem hTermO_le_optJ {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) (t : PoisT) (o : OptJ) (ht : checkPT t = true)
    (ho : checkOptJ H b k a t o = true) (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ)
    (hrate : (N : ℝ) / 2 ^ b + (q : ℝ) * (lam * w).toReal / 2 ^ b ≤ (t.mu : ℝ))
    (b0 : ℝ≥0∞) (hb0 : ENNReal.ofReal (o.cthr : ℝ) ≤ b0) :
    hTermO (Finset.univ : Finset View) w lam N q (ForsPotential.excess b0) ≤ ENNReal.ofReal (o.B : ℝ) := by
  simp only [checkOptJ, Bool.and_eq_true, decide_eq_true_eq] at ho
  obtain ⟨hok, hB⟩ := ho
  obtain ⟨hc1, hlen, hθs, hcthr, hnb, hc2n, hT, hnx, h1, h150, hg0, hah0, hEg0, hEah0⟩ := okJ_parts hok
  have hlw : lam * w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (mul_le_one' hlam hw)
  have hcard : Fintype.card (Fin (2 ^ subtreeHeight)) = 2 ^ b := by rw [Fintype.card_fin, hb]
  set α : ℝ≥0 := ((2 : ℝ≥0) ^ b)⁻¹ with hαdef
  set γ : ℝ≥0 := (lam * w).toNNReal / (2 : ℝ≥0) ^ b with hγdef
  set μ : ℝ≥0 := ⟨(t.mu : ℝ), by exact_mod_cast t.mu_nonneg⟩ with hμdef
  have h2b0 : ((2 : ℝ≥0) ^ b) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hL : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ b := by rw [hcard]; push_cast; rfl
  have hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1 := by
    rw [hL, hαdef, ENNReal.coe_inv h2b0]
    push_cast
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = lam * w := by
    rw [hL, hγdef, ENNReal.coe_div h2b0, ENNReal.coe_toNNReal hlw]
    push_cast
    exact ENNReal.mul_div_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hμdef, hγdef, hαdef]
    push_cast
    calc (N : ℝ) * ((2 : ℝ) ^ b)⁻¹ + (q : ℝ) * ((lam * w).toReal / 2 ^ b)
        = (N : ℝ) / 2 ^ b + (q : ℝ) * (lam * w).toReal / 2 ^ b := by ring
      _ ≤ _ := hrate
  -- the scalars
  have hc2 : ((c2Q H k a o.nb : ℚ) : ℝ) ≤ (o.c1 : ℝ) := by
    have := nat_div_le_of hc1 hc2n
    unfold c2Q; push_cast at this ⊢; exact this
  have hsmall : ∀ Ms : Multiset (FTree → FLeaf), Ms.card ≤ o.nb →
      κE.toReal * (yM Ms).toReal ≤ ((c2Q H k a o.nb : ℚ) : ℝ) := by
    intro Ms hMs
    refine le_trans (κy_le_card hH hb hk ha Ms) ?_
    unfold c2Q
    push_cast
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.pow_le_pow_left hMs k) (by positivity)
  have hθR : ∀ j ≤ o.m, 0 < ((o.θ j : ℚ) : ℝ) := fun j hj => by exact_mod_cast (hθs j (by omega)).1
  set S := Finset.range (o.m + 1) with hS
  have hmain := hTermO_fors_leJ w lam hw hlam N q b0 (o.cthr : ℝ) (o.c1 : ℝ) ((c2Q H k a o.nb : ℚ) : ℝ) hb0 hc2
    o.nb hsmall o.m (fun j => ((o.θ j : ℚ) : ℝ)) hθR
    (fun n => ENNReal.ofReal ((leafQ (gtJ H k a t o) (JgJ H k a t o) n : ℚ) : ℝ))
    (fun j n => ENNReal.ofReal ((leafQ (atJ H k a t o j) (JaJ H k a t o j) n : ℚ) : ℝ))
    (fun j n => 1 + ENNReal.ofReal ((leafQ (htJ H k a t o j) (JhJ H k a t o j) n : ℚ) : ℝ))
    (leaf_sepGood (checkLeaf_overP (by simp) h1 hg0 _))
    (fun j hj => leaf_sepGood (checkLeaf_overP (by simp) h1 (hah0 j (Finset.mem_range.1 hj)).1 _))
    (fun j hj => SepGood.one_add (leaf_sepGood (checkLeaf_overP (by simp) h1 (hah0 j (Finset.mem_range.1 hj)).2 _)))
    (avgN_gS_le_tabJ hH hb hk ha hok)
    (fun j hj n => avgN_aS_le_tabJ hH hb hk ha hok j (Finset.mem_range.1 hj) n)
    (fun j hj n => by
      rw [← okJ_cap_eq]
      exact avgN_hS_le_tabJ hH hb hk ha hok j (Finset.mem_range.1 hj) n) α γ hα hγ μ hμ
  refine le_trans hmain ?_
  -- the Poisson means
  have hlenT : ∀ (f : ℕ → ℤ), (overP 0 (convexZ ((List.range (t.n1 + 1)).map f))).length = t.n1 + 1 := fun f => by
    simp [length_overP, length_convexZ]
  have hp : 2 ≤ t.pm.length := by unfold PoisT.n1 at h1; omega
  have hEg : poisMean μ (fun n => ENNReal.ofReal ((leafQ (gtJ H k a t o) (JgJ H k a t o) n : ℚ) : ℝ)) ≤
      ENNReal.ofReal (EgJ H b k a t o : ℝ) := by
    refine le_trans (poisMean_leaf_le ht (checkLeaf_overP (by simp) h1 hg0 _) (by simp [gtJ, gkJ, tabJ,
      length_overP, length_convexZ])) (ENNReal.ofReal_le_ofReal ((Rat.cast_le (K := ℝ)).mpr ?_))
    exact (meanZ_eq (P := 191) (ks := gkJ H k a t o) (JgJ H k a t o)
      (by simp [gkJ, tabJ, length_convexZ]) hp).trans_le (le_rup _ _)
  have hEa : ∀ j ∈ S, poisMean μ (fun n => ENNReal.ofReal ((leafQ (atJ H k a t o j) (JaJ H k a t o j) n : ℚ) : ℝ)) ≤
      ENNReal.ofReal (EaJ H b k a t o j : ℝ) := fun j hj => by
    refine le_trans (poisMean_leaf_le ht (checkLeaf_overP (by simp) h1 (hah0 j (Finset.mem_range.1 hj)).1 _)
      (by simp [atJ, akJ, tabJ, length_overP, length_convexZ])) (ENNReal.ofReal_le_ofReal ((Rat.cast_le (K := ℝ)).mpr ?_))
    exact (meanZ_eq (P := 128) (ks := akJ H k a t o j) (JaJ H k a t o j)
      (by simp [akJ, tabJ, length_convexZ]) hp).trans_le (le_rup _ _)
  have hEh : ∀ j ∈ S, poisMean μ (fun n => 1 + ENNReal.ofReal ((leafQ (htJ H k a t o j) (JhJ H k a t o j) n : ℚ) : ℝ)) ≤
      ENNReal.ofReal ((1 + EhJ H b k a t o j : ℚ) : ℝ) := fun j hj => by
    rw [poisMean_one_add, show ((1 + EhJ H b k a t o j : ℚ) : ℝ) = 1 + (EhJ H b k a t o j : ℝ) by push_cast; ring,
      ENNReal.ofReal_add zero_le_one (by exact_mod_cast (hEah0 j (Finset.mem_range.1 hj)).2), ENNReal.ofReal_one]
    refine add_le_add le_rfl (le_trans (poisMean_leaf_le ht (checkLeaf_overP (by simp) h1
      (hah0 j (Finset.mem_range.1 hj)).2 _) (by simp [htJ, hkJ, tabJ, length_overP, length_convexZ]))
      (ENNReal.ofReal_le_ofReal ((Rat.cast_le (K := ℝ)).mpr ?_)))
    exact (meanZ_eq (P := 128) (ks := hkJ H k a t o j) (JhJ H k a t o j)
      (by simp [hkJ, tabJ, length_convexZ]) hp).trans_le (le_rup _ _)
  -- the terms
  have hterm : ∀ j ∈ S, ENNReal.ofReal (prefR ((o.θ j : ℚ) : ℝ) (o.cthr : ℝ)) *
      (((Fintype.card (Fin (2 ^ subtreeHeight))).choose j : ℝ≥0∞) *
        poisMean μ (fun n => ENNReal.ofReal ((leafQ (atJ H k a t o j) (JaJ H k a t o j) n : ℚ) : ℝ)) ^ j *
        poisMean μ (fun n => 1 + ENNReal.ofReal ((leafQ (htJ H k a t o j) (JhJ H k a t o j) n : ℚ) : ℝ)) ^
          (Fintype.card (Fin (2 ^ subtreeHeight)) - j)) ≤ ENNReal.ofReal (termJ H b k a t o j : ℝ) := by
    intro j hj
    have hjm := Finset.mem_range.1 hj
    have hθj := (hθs j hjm).1
    have hEa0 := (hEah0 j hjm).1
    have hEh0 := (hEah0 j hjm).2
    have hpref := pref_le (o.θ j) o.cthr t.J t.P hθj hcthr
    have hLe : expLow (o.θ j * o.cthr) t.J t.P = expLowJ t o j := by
      have h0 : 0 ≤ (o.θ j * o.cthr).num := Rat.num_nonneg.mpr (mul_nonneg hθj.le hcthr)
      refine expLow_eq (o.θ j * o.cthr).den_pos ?_
      rw [show (((o.θ j * o.cthr).num.toNat : ℕ) : ℚ) = ((o.θ j * o.cthr).num : ℚ) by
        exact_mod_cast Int.toNat_of_nonneg h0, Rat.num_div_den]
    rw [hLe] at hpref
    have hE1 : (1 : ℚ) ≤ 1 + EhJ H b k a t o j := by linarith
    have hpow : poisMean μ (fun n => 1 + ENNReal.ofReal ((leafQ (htJ H k a t o j) (JhJ H k a t o j) n : ℚ) : ℝ)) ^
        (Fintype.card (Fin (2 ^ subtreeHeight)) - j) ≤ ENNReal.ofReal (sqUp t.P b (1 + EhJ H b k a t o j) : ℝ) := by
      refine le_trans (pow_le_pow_left' (hEh j hj) _) (le_trans ?_ (ofReal_pow_le_sqUp t.P b _))
      rw [hcard]
      exact pow_le_pow_right₀ (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hE1))
        (Nat.sub_le _ _)
    have hsq0 : (0 : ℝ) ≤ (sqUp t.P b (1 + EhJ H b k a t o j) : ℝ) := by
      exact_mod_cast sqUp_nonneg_of t.P b _ (by linarith)
    have hpref0 : (0 : ℝ) ≤ ((1 / (expLowJ t o j * eLowQ * o.θ j) : ℚ) : ℝ) := by
      have := one_le_expLow (o.θ j * o.cthr) t.J t.P (mul_nonneg hθj.le hcthr)
      rw [hLe] at this
      have : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
      exact_mod_cast (by positivity : (0 : ℚ) ≤ 1 / (expLowJ t o j * eLowQ * o.θ j))
    calc ENNReal.ofReal (prefR ((o.θ j : ℚ) : ℝ) (o.cthr : ℝ)) *
          (((Fintype.card (Fin (2 ^ subtreeHeight))).choose j : ℝ≥0∞) *
            poisMean μ (fun n => ENNReal.ofReal ((leafQ (atJ H k a t o j) (JaJ H k a t o j) n : ℚ) : ℝ)) ^ j *
            poisMean μ (fun n => 1 + ENNReal.ofReal ((leafQ (htJ H k a t o j) (JhJ H k a t o j) n : ℚ) : ℝ)) ^
              (Fintype.card (Fin (2 ^ subtreeHeight)) - j))
        ≤ ENNReal.ofReal ((1 / (expLowJ t o j * eLowQ * o.θ j) : ℚ) : ℝ) *
          ((((2 ^ b).descFactorial j / j.factorial : ℕ) : ℝ≥0∞) * ENNReal.ofReal (EaJ H b k a t o j : ℝ) ^ j *
            ENNReal.ofReal (sqUp t.P b (1 + EhJ H b k a t o j) : ℝ)) := by
          rw [hcard, choose_eq_desc]
          gcongr
          · exact hpref
          · exact hEa j hj
          · rw [← hcard]; exact hpow
      _ = ENNReal.ofReal (termJ H b k a t o j : ℝ) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by exact_mod_cast hEa0),
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul hpref0]
          congr 1
          unfold termJ
          push_cast
          ring
  -- the sum
  have hsumT : ((List.range (o.m + 1)).map (termJ H b k a t o)).sum = ∑ j ∈ S, termJ H b k a t o j :=
    list_sum_range _ _
  have hterm0 : ∀ j ∈ S, (0 : ℝ) ≤ (termJ H b k a t o j : ℝ) := fun j hj => by
    have hjm := Finset.mem_range.1 hj
    have hθj := (hθs j hjm).1
    have hEa0 := (hEah0 j hjm).1
    have hEh0 := (hEah0 j hjm).2
    have h0 := one_le_expLow (o.θ j * o.cthr) t.J t.P (mul_nonneg hθj.le hcthr)
    have hLe : expLow (o.θ j * o.cthr) t.J t.P = expLowJ t o j := by
      have h0 : 0 ≤ (o.θ j * o.cthr).num := Rat.num_nonneg.mpr (mul_nonneg hθj.le hcthr)
      refine expLow_eq (o.θ j * o.cthr).den_pos ?_
      rw [show (((o.θ j * o.cthr).num.toNat : ℕ) : ℚ) = ((o.θ j * o.cthr).num : ℚ) by
        exact_mod_cast Int.toNat_of_nonneg h0, Rat.num_div_den]
    rw [hLe] at h0
    have hsq : (0 : ℚ) ≤ sqUp t.P b (1 + EhJ H b k a t o j) := sqUp_nonneg_of t.P b _ (by linarith)
    have : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
    have : (0 : ℚ) ≤ termJ H b k a t o j := by unfold termJ; positivity
    exact_mod_cast this
  have hEgr : (0 : ℝ) ≤ (EgJ H b k a t o : ℝ) := by exact_mod_cast hEg0
  rw [hL, hcard]
  calc _ ≤ ENNReal.ofReal ((2 : ℝ) ^ b * (EgJ H b k a t o : ℝ)) + ∑ j ∈ S, ENNReal.ofReal (termJ H b k a t o j : ℝ) := by
        gcongr with j hj
        · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
          exact mul_le_mul_right hEg _
        · have := hterm j hj
          rw [hcard] at this
          exact this
    _ = ENNReal.ofReal (((2 ^ b * EgJ H b k a t o + ((List.range (o.m + 1)).map (termJ H b k a t o)).sum : ℚ)) : ℝ) := by
        rw [← ENNReal.ofReal_sum_of_nonneg hterm0, ← ENNReal.ofReal_add (by positivity)
          (Finset.sum_nonneg hterm0), hsumT]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal (o.B : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        have : 2 ^ b * EgJ H b k a t o + ((List.range (o.m + 1)).map (termJ H b k a t o)).sum ≤ o.B :=
          le_trans (le_rup _ _) hB
        exact_mod_cast this

/-- The bound of a checked option is nonnegative. -/
theorem optJ_B_nonneg {H b k a : ℕ} {t : PoisT} {o : OptJ} (ho : checkOptJ H b k a t o = true) : 0 ≤ o.B := by
  simp only [checkOptJ, Bool.and_eq_true, decide_eq_true_eq] at ho
  obtain ⟨hok, hB⟩ := ho
  obtain ⟨hc1, hlen, hθs, hcthr, -, -, -, -, -, -, -, -, hEg0, hEah0⟩ := okJ_parts hok
  refine le_trans ?_ (le_trans (le_rup _ _) hB)
  refine add_nonneg (by positivity) ?_
  rw [list_sum_range]
  refine Finset.sum_nonneg fun j hj => ?_
  have hjm := Finset.mem_range.1 hj
  have hθj := (hθs j hjm).1
  have hEa0 := (hEah0 j hjm).1
  have hEh0 := (hEah0 j hjm).2
  have h0 := one_le_expLow (o.θ j * o.cthr) t.J t.P (mul_nonneg hθj.le hcthr)
  have hLe : expLow (o.θ j * o.cthr) t.J t.P = expLowJ t o j := by
    have h0 : 0 ≤ (o.θ j * o.cthr).num := Rat.num_nonneg.mpr (mul_nonneg hθj.le hcthr)
    refine expLow_eq (o.θ j * o.cthr).den_pos ?_
    rw [show (((o.θ j * o.cthr).num.toNat : ℕ) : ℚ) = ((o.θ j * o.cthr).num : ℚ) by
      exact_mod_cast Int.toNat_of_nonneg h0, Rat.num_div_den]
  rw [hLe] at h0
  have hsq : (0 : ℚ) ≤ sqUp t.P b (1 + EhJ H b k a t o j) := sqUp_nonneg_of t.P b _ (by linarith)
  have : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
  unfold termJ
  positivity

/-! ### Options of either kind -/

theorem optF_B_nonneg {H b k a : ℕ} {t : PoisT} {o : OptF} (ho : checkOptF H b k a t o = true) :
    0 ≤ o.B := by
  obtain ⟨-, hθ, hcthr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hB, hEg0, hEe0⟩ := checkOptF_parts ho
  have hsq0 : 0 ≤ sqUp t.P b (1 + o.Ee) := sqUp_nonneg_of t.P b _ (by linarith)
  have hE := one_le_expLow (o.θ * o.cthr) t.J t.P (by positivity)
  have he : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
  refine le_trans ?_ hB
  positivity

/-- An option of either kind: the option of one Chernoff factor (`OptF`, `CoverBound/HTermOption.lean`)
or of the split by big indices (`OptJ`). -/
inductive Opt where
  | F (o : OptF)
  | J (o : OptJ)

namespace Opt

/-- The threshold of an option. -/
def cthr : Opt → ℚ
  | .F o => o.cthr
  | .J o => o.cthr

/-- The bound of an option. -/
def B : Opt → ℚ
  | .F o => o.B
  | .J o => o.B

end Opt

/-- The check of an option of either kind. -/
def checkOpt (H b k a : ℕ) (t : PoisT) : Opt → Bool
  | .F o => checkOptF H b k a t o
  | .J o => checkOptJ H b k a t o

/-- **A checked option of either kind bounds the FORS H-term** (`hTermO_le_optF`, `hTermO_le_optJ`). -/
theorem hTermO_le_opt {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) (t : PoisT) (o : Opt) (ht : checkPT t = true)
    (ho : checkOpt H b k a t o = true) (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ)
    (hrate : (N : ℝ) / 2 ^ b + (q : ℝ) * (lam * w).toReal / 2 ^ b ≤ (t.mu : ℝ))
    (b0 : ℝ≥0∞) (hb0 : ENNReal.ofReal (o.cthr : ℝ) ≤ b0) :
    hTermO (Finset.univ : Finset View) w lam N q (ForsPotential.excess b0) ≤ ENNReal.ofReal (o.B : ℝ) := by
  cases o with
  | F o => exact hTermO_le_optF hH hb hk ha t o ht ho w lam hw hlam N q hrate b0 hb0
  | J o => exact hTermO_le_optJ hH hb hk ha t o ht ho w lam hw hlam N q hrate b0 hb0

/-- The bound of a checked option is nonnegative. -/
theorem opt_B_nonneg {H b k a : ℕ} {t : PoisT} {o : Opt} (ho : checkOpt H b k a t o = true) : 0 ≤ o.B := by
  cases o with
  | F o => exact optF_B_nonneg ho
  | J o => exact optJ_B_nonneg ho

end FORS.Security.H0
