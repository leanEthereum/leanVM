import FORS.CoverBound.HTermCertificate

/-! **Integer tables.** The leaf tables of the certificates are computed in integers: numerators over a
power of two, made convex and increasing (`convexZ`), read as rationals (`overP`), extended with the
slope `leafJ` and averaged against a Poisson table in one integer sum (`meanZ`); the exponential series
of `expLow` is summed in integers (`expLowN`). Shared by the options (`CoverBound/HTermOptionJ.lean`) and
the certificates rebuilt from their scalars (`Certificates/Build.lean`). -/

namespace FORS.Security.H0

open FORS.Base.H0

set_option linter.unusedSectionVars false

/-! ### Extension slopes -/

/-- The extension slope of a leaf table with cap `cap`. -/
def leafJ (n1 : ℕ) (tab : List ℚ) (cap : ℚ) : ℚ :=
  max (max (tab.getD n1 0 - tab.getD (n1 - 1) 0) (cap - tab.getD n1 0)) 0

/-! ### Convex integer tables -/

theorem getD_eq_get {α : Type*} {l : List α} {n : ℕ} {d : α} (h : n < l.length) : l.getD n d = l[n] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The loop of `convexZ`: each entry raised to at least the line through the two before it. -/
def convexGoZ : ℤ → ℤ → List ℤ → List ℤ
  | _, _, [] => []
  | a, b, x :: xs => max x (2 * b - a) :: convexGoZ b (max x (2 * b - a)) xs

/-- The least convex increasing list above a list (from the left). -/
def convexZ : List ℤ → List ℤ
  | [] => []
  | [x] => [x]
  | x :: y :: xs => x :: max y x :: convexGoZ x (max y x) xs

theorem length_convexGoZ : ∀ (a b : ℤ) (xs : List ℤ), (convexGoZ a b xs).length = xs.length
  | _, _, [] => rfl
  | _, _, _ :: xs => by simp only [convexGoZ, List.length_cons, length_convexGoZ _ _ xs]

theorem length_convexZ : ∀ xs : List ℤ, (convexZ xs).length = xs.length
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: xs => by simp only [convexZ, List.length_cons, length_convexGoZ]

theorem le_convexGoZ : ∀ (a b : ℤ) (xs : List ℤ) (n : ℕ), n < xs.length →
    xs.getD n 0 ≤ (convexGoZ a b xs).getD n 0
  | _, _, [], _, h => absurd h (Nat.not_lt_zero _)
  | _, _, _ :: _, 0, _ => by simp only [convexGoZ, List.getD_cons_zero]; exact le_max_left _ _
  | _, _, _ :: xs, n + 1, h => by
      simp only [convexGoZ, List.getD_cons_succ]
      exact le_convexGoZ _ _ xs n (by simpa using h)

theorem le_convexZ : ∀ (xs : List ℤ) (n : ℕ), n < xs.length → xs.getD n 0 ≤ (convexZ xs).getD n 0
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | [_], 0, _ => le_rfl
  | [_], _ + 1, h => absurd h (by simp)
  | _ :: _ :: _, 0, _ => le_rfl
  | _ :: _ :: _, 1, _ => by
      simp only [convexZ, List.getD_cons_succ, List.getD_cons_zero]; exact le_max_left _ _
  | _ :: _ :: xs, n + 2, h => by
      simp only [convexZ, List.getD_cons_succ]
      exact le_convexGoZ _ _ xs n (by simpa using h)

/-- Increasing and convex, as `checkLeaf` reads it. -/
def LeafShape {α : Type*} [Zero α] [Add α] [Mul α] [OfNat α 2] [LE α] (l : List α) : Prop :=
  (∀ n < l.length - 1, l.getD n 0 ≤ l.getD (n + 1) 0) ∧
    (∀ n < l.length - 2, 2 * l.getD (n + 1) 0 ≤ l.getD n 0 + l.getD (n + 2) 0)

theorem shape_convexGoZ : ∀ (a b : ℤ) (xs : List ℤ), a ≤ b → LeafShape (a :: b :: convexGoZ a b xs)
  | a, b, [], hab => by
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · simp only [convexGoZ, List.length_cons, List.length_nil] at hn
        obtain rfl : n = 0 := by omega
        simpa using hab
      · simp only [convexGoZ, List.length_cons, List.length_nil] at hn
        omega
  | a, b, x :: xs, hab => by
      have hc : b ≤ max x (2 * b - a) := le_trans (by omega) (le_max_right _ _)
      have hc2 : 2 * b ≤ a + max x (2 * b - a) := by have := le_max_right x (2 * b - a); omega
      obtain ⟨ih1, ih2⟩ := shape_convexGoZ b (max x (2 * b - a)) xs hc
      simp only [convexGoZ]
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · cases n with
        | zero => simpa using hab
        | succ n =>
            have := ih1 n (by simp only [List.length_cons] at hn ⊢; omega)
            simpa only [List.getD_cons_succ] using this
      · cases n with
        | zero => simpa using hc2
        | succ n =>
            have := ih2 n (by simp only [List.length_cons] at hn ⊢; omega)
            simpa only [List.getD_cons_succ] using this

theorem shape_convexZ : ∀ xs : List ℤ, LeafShape (convexZ xs)
  | [] => ⟨fun n hn => by simp [convexZ] at hn, fun n hn => by simp [convexZ] at hn⟩
  | [_] => ⟨fun n hn => by simp [convexZ] at hn, fun n hn => by simp [convexZ] at hn⟩
  | x :: y :: xs => shape_convexGoZ x (max y x) xs (le_max_right _ _)

/-- The loop of `convexN`. -/
def convexGoN : ℕ → ℕ → List ℕ → List ℕ
  | _, _, [] => []
  | a, b, x :: xs => max x (2 * b - a) :: convexGoN b (max x (2 * b - a)) xs

/-- `convexZ` on natural numbers (`convexN_map`), which the kernel evaluates in fewer steps. -/
def convexN : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: y :: xs => x :: max y x :: convexGoN x (max y x) xs

theorem convexGoN_map : ∀ (a b : ℕ) (xs : List ℕ),
    (convexGoN a b xs).map (↑) = convexGoZ a b (xs.map (↑) : List ℤ)
  | _, _, [] => rfl
  | a, b, x :: xs => by
      have e : ((max x (2 * b - a) : ℕ) : ℤ) = max (x : ℤ) (2 * b - a) := by omega
      simp only [convexGoN, convexGoZ, List.map_cons, e, convexGoN_map b _ xs]

theorem convexN_map : ∀ xs : List ℕ, (convexN xs).map (↑) = convexZ (xs.map (↑) : List ℤ)
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs => by
      have e : ((max y x : ℕ) : ℤ) = max (y : ℤ) x := by omega
      simp only [convexN, convexZ, List.map_cons, e, convexGoN_map]

theorem length_convexN (xs : List ℕ) : (convexN xs).length = xs.length := by
  rw [← List.length_map (f := ((↑) : ℕ → ℤ)), convexN_map, length_convexZ, List.length_map]

/-- The rationals of the numerators `ks` over `2^P`. -/
def overP (P : ℕ) (ks : List ℤ) : List ℚ := ks.map fun k : ℤ => (k : ℚ) / 2 ^ P

theorem length_overP (P : ℕ) (ks : List ℤ) : (overP P ks).length = ks.length := by simp [overP]

theorem getD_overP {P : ℕ} {ks : List ℤ} {n : ℕ} (h : n < ks.length) :
    (overP P ks).getD n 0 = (ks.getD n 0 : ℚ) / 2 ^ P := by
  rw [getD_eq_get (by rw [length_overP]; exact h), getD_eq_get h]
  simp [overP]

theorem shape_overP (P : ℕ) {ks : List ℤ} (h : LeafShape ks) : LeafShape (overP P ks) := by
  have hP : (0 : ℚ) < 2 ^ P := by positivity
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [length_overP] at hn
    rw [getD_overP (by omega), getD_overP (by omega)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h.1 n hn) hP.le
  · rw [length_overP] at hn
    rw [getD_overP (by omega), getD_overP (by omega), getD_overP (by omega), ← mul_div_assoc, ← add_div,
      div_le_div_iff_of_pos_right hP]
    exact_mod_cast h.2 n hn

theorem checkLeaf_overP {P n1 : ℕ} {ks : List ℤ} (hl : ks.length = n1 + 1) (h1 : 1 ≤ n1)
    (h0 : 0 ≤ (overP P (convexZ ks)).getD 0 0) (cap : ℚ) :
    checkLeaf (overP P (convexZ ks)) (leafJ n1 (overP P (convexZ ks)) cap) = true := by
  have hs := shape_overP P (shape_convexZ ks)
  have hl' : (overP P (convexZ ks)).length = n1 + 1 := by rw [length_overP, length_convexZ, hl]
  simp only [checkLeaf, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨by omega, h0⟩, hs.1⟩, hs.2⟩, ?_⟩
  rw [hl', show n1 + 1 - 1 = n1 by omega, show n1 + 1 - 2 = n1 - 1 by omega]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

theorem le_leafJ (n1 : ℕ) (tab : List ℚ) (cap : ℚ) : cap ≤ tab.getD n1 0 + leafJ n1 tab cap := by
  have : cap - tab.getD n1 0 ≤ leafJ n1 tab cap := le_trans (le_max_right _ _) (le_max_left _ _)
  linarith

/-- A bound `f` below the numerators `ks` over `2^P` stays below the convex table. -/
theorem le_overP {P : ℕ} {ks : List ℤ} {n : ℕ} (h : n < ks.length) {f : ℚ} (hf : f ≤ (ks.getD n 0 : ℚ) / 2 ^ P) :
    f ≤ (overP P (convexZ ks)).getD n 0 := by
  rw [getD_overP (by rw [length_convexZ]; exact h)]
  exact le_trans hf (div_le_div_of_nonneg_right (by exact_mod_cast le_convexZ ks n h) (by positivity))

/-! ### Rounding up in integers

`cdivZ` and its two bounds are in `CoverBound/MomentBounds.lean`, with the moment numerators. -/

theorem min_overP (a b : ℤ) (P : ℕ) : ((min a b : ℤ) : ℚ) / 2 ^ P = min ((a : ℚ) / 2 ^ P) ((b : ℚ) / 2 ^ P) := by
  rw [Int.cast_min, min_div_div_right (by positivity)]

/-- `rup` of a quotient of integers. -/
theorem rup_intCast_div (N : ℤ) (D P : ℕ) : rup ((N : ℚ) / D) P = mkRat (cdivZ (N * 2 ^ P) D) (2 ^ P) := by
  unfold rup
  rw [Rat.mkRat_eq_div, cdivZ_eq_ceil]
  push_cast
  congr 2
  ring_nf

/-! ### Tables from the moment tables -/

/-- `f` on the first `n1 + 1` entries of two lists. -/
def zipTab {α β γ : Type*} (n1 : ℕ) (f : α → β → γ) (l : List α) (l' : List β) : List γ :=
  (List.zipWith f l l').take (n1 + 1)

theorem length_zipTab {α β γ : Type*} {n1 : ℕ} {f : α → β → γ} {l : List α} {l' : List β}
    (h : n1 + 1 ≤ l.length) (h' : n1 + 1 ≤ l'.length) : (zipTab n1 f l l').length = n1 + 1 := by
  simp [zipTab]; omega

theorem getD_zipTab {α β γ : Type*} {n1 n : ℕ} {f : α → β → γ} {l : List α} {l' : List β} {a : α} {b : β} {c : γ}
    (h : n1 + 1 ≤ l.length) (h' : n1 + 1 ≤ l'.length) (hn : n < n1 + 1) :
    (zipTab n1 f l l').getD n c = f (l.getD n a) (l'.getD n b) := by
  rw [getD_eq_get (by rw [length_zipTab h h']; exact hn), getD_eq_get (by omega), getD_eq_get (by omega)]
  simp [zipTab]

theorem getD_tab {L : List ℕ} {T : List ℚ} (hT : L.map (fun x : ℕ => (x : ℚ) / 2 ^ 128) = T) {n : ℕ}
    (hn : n < L.length) : T.getD n 0 = (L.getD n 0 : ℚ) / 2 ^ 128 := by
  rw [← hT, getD_eq_get (by simpa using hn), getD_eq_get hn]; simp

/-- `2^k` in `ℤ`, by the power in `ℕ`. -/
abbrev p2 (k : ℕ) : ℤ := ((2 ^ k : ℕ) : ℤ)

theorem p2_pos (k : ℕ) : 0 < p2 k := by unfold p2; exact_mod_cast Nat.two_pow_pos k

/-- A power of a moment-table entry, over one power of two. -/
theorem tab_pow (x : ℚ) (k : ℕ) : (x / 2 ^ 128) ^ k = x ^ k / 2 ^ (128 * k) := by
  rw [div_pow, ← pow_mul]

/-! ### Entries in natural numbers

The kernel evaluates an entry of a table in `ℕ` in far fewer steps than the same entry in `ℤ`;
`gNat_eq` and `hNat_eq` give the `ℤ` forms the bounds are proved for. -/

/-- The excess entry from the moment numerators `x`, `y` and the cap `cn / cd` (over `2^191`). -/
def gNat (H k cn cd x y : ℕ) : ℕ :=
  min (cdiv (Nat.pow x k * 2 ^ 191) (2 ^ (H + 128 * k)))
    (cdiv (Nat.pow y k * cd * 2 ^ 191) (2 ^ (2 * H + 128 * k) * 4 * cn))

/-- The quadratic entry from the moment numerators `x`, `y`, `θ = tn / td` and `A2 = an / ad`
(over `2^128`). -/
def hNat (H k tn td an ad x y : ℕ) : ℕ :=
  cdiv ((tn * ad * Nat.pow x k * 2 ^ H + an * td * Nat.pow y k) * 2 ^ 128) (td * ad * 2 ^ (2 * H + 128 * k))

theorem gNat_eq {c1 : ℚ} (hc : 0 < c1) (H k x y : ℕ) :
    (gNat H k c1.num.toNat c1.den x y : ℤ) = min (cdivZ (((x ^ k : ℕ) : ℤ) * 2 ^ 191) (p2 (H + 128 * k)))
      (cdivZ (((y ^ k * c1.den : ℕ) : ℤ) * 2 ^ 191) (p2 (2 * H + 128 * k) * 4 * c1.num)) := by
  have hn : c1.num = (c1.num.toNat : ℤ) := (Int.toNat_of_nonneg (Rat.num_pos.mpr hc).le).symm
  have hn' : 0 < c1.num.toNat := by have := Rat.num_pos.mpr hc; omega
  unfold gNat p2
  rw [Nat.cast_min]
  conv_rhs => rw [hn]
  congr 1
  · rw [show ((x ^ k : ℕ) : ℤ) * 2 ^ 191 = ((Nat.pow x k * 2 ^ 191 : ℕ) : ℤ) by push_cast; rfl,
      cdivZ_natCast _ _ (by positivity)]
  · rw [show ((y ^ k * c1.den : ℕ) : ℤ) * 2 ^ 191 = ((Nat.pow y k * c1.den * 2 ^ 191 : ℕ) : ℤ) by push_cast; rfl,
      show ((2 ^ (2 * H + 128 * k) : ℕ) : ℤ) * 4 * (c1.num.toNat : ℤ) =
        ((2 ^ (2 * H + 128 * k) * 4 * c1.num.toNat : ℕ) : ℤ) by push_cast; rfl,
      cdivZ_natCast _ _ (by positivity)]

theorem hNat_eq {θ A2 : ℚ} (hθ : 0 ≤ θ) (hA : 0 ≤ A2) (H k x y : ℕ) :
    (hNat H k θ.num.toNat θ.den A2.num.toNat A2.den x y : ℤ) =
      cdivZ ((θ.num * A2.den * ((x ^ k : ℕ) : ℤ) * p2 H + A2.num * θ.den * ((y ^ k : ℕ) : ℤ)) * 2 ^ 128)
        (θ.den * A2.den * p2 (2 * H + 128 * k)) := by
  have hθn : θ.num = (θ.num.toNat : ℤ) := (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hθ)).symm
  have hAn : A2.num = (A2.num.toNat : ℤ) := (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hA)).symm
  unfold hNat p2
  rw [hθn, hAn, ← cdivZ_natCast _ _ (by have := θ.den_pos; have := A2.den_pos; positivity)]
  push_cast
  rfl

/-! ### Means -/

/-- The mean `poisMean` of `leafQ` over the table `overP P ks`, the weights times the numerators
summed in integers. -/
def meanZ (t : PoisT) (P : ℕ) (ks : List ℤ) (J : ℚ) : ℚ :=
  ((List.zipWith (fun (p : ℕ) (k : ℤ) => (p : ℤ) * k) t.pm ks).sum : ℚ) / 2 ^ (t.P + P) +
    t.pb (t.n1 + 1) * ((overP P ks).getD t.n1 0 / (1 - t.r) + J / (1 - t.r) ^ 2)

theorem sum_map_div (l : List ℚ) (c : ℚ) : (l.map (· / c)).sum = l.sum / c := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, add_div]

theorem meanZ_eq {t : PoisT} {P : ℕ} {ks : List ℤ} (J : ℚ) (hk : ks.length = t.n1 + 1) (hp : 2 ≤ t.pm.length) :
    ((List.range (t.n1 + 1)).map fun n => t.pb n * (overP P ks).getD n 0).sum +
      t.pb (t.n1 + 1) * ((overP P ks).getD t.n1 0 / (1 - t.r) + J / (1 - t.r) ^ 2) = meanZ t P ks J := by
  have hn : t.pm.length = t.n1 + 2 := by unfold PoisT.n1; omega
  have hl : ((List.range (t.n1 + 1)).map fun n => t.pb n * (overP P ks).getD n 0) =
      ((List.zipWith (fun (p : ℕ) (k : ℤ) => (p : ℤ) * k) t.pm ks).map (fun z : ℤ => (z : ℚ))).map
        (· / 2 ^ (t.P + P)) := by
    apply List.ext_getElem
    · simp [hk, hn]
    · intro i h1 _
      have hi : i < t.n1 + 1 := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith]
      unfold PoisT.pb
      rw [getD_overP (by omega), getD_eq_get (show i < ks.length by omega),
        getD_eq_get (show i < t.pm.length by omega)]
      push_cast
      field_simp
      ring
  unfold meanZ
  rw [hl, sum_map_div, Int.cast_list_sum]

/-! ### The exponential series in integers -/

/-- `expLowGo` on numerators over `2^P`, for `u = un / ud`: the terms `k`, the partial sum `A`. -/
def expLowN (un ud P : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, k, A => A + k
  | r + 1, j, k, A => expLowN un ud P r (j + 1) (k * un / (ud * (j + 1))) (A + k)

theorem expLowGo_eq {u : ℚ} {un ud P : ℕ} (hu : u = (un : ℚ) / ud) (hd : 0 < ud) :
    ∀ (r j k A : ℕ), expLowGo u P r j ((k : ℚ) / 2 ^ P) ((A : ℚ) / 2 ^ P) =
      (expLowN un ud P r j k A : ℚ) / 2 ^ P
  | 0, _, k, A => by simp only [expLowGo, expLowN]; push_cast; ring
  | r + 1, j, k, A => by
      simp only [expLowGo, expLowN]
      rw [← expLowGo_eq hu hd r (j + 1) (k * un / (ud * (j + 1))) (A + k)]
      congr 1
      · unfold rdown
        have e : (k : ℚ) / 2 ^ P * u / ((j : ℚ) + 1) * 2 ^ P = ((k * un : ℕ) : ℚ) / ((ud * (j + 1) : ℕ) : ℚ) := by
          rw [hu]; push_cast; field_simp
        rw [e, Rat.floor_natCast_div_natCast, ← Int.natCast_div, Int.cast_natCast]
      · push_cast; ring

/-- **`expLow` in integers.** -/
theorem expLow_eq {u : ℚ} {un ud J P : ℕ} (hd : 0 < ud) (hu : u = (un : ℚ) / ud) :
    expLow u J P = (expLowN un ud P J 0 (2 ^ P) 0 : ℚ) / 2 ^ P := by
  unfold expLow
  rw [← expLowGo_eq hu hd]
  push_cast
  rw [div_self (by positivity), zero_div]

theorem le_ceilDiv (a d : ℕ) (hd : 0 < d) : a ≤ (a + (d - 1)) / d * d := by
  have h1 := Nat.div_add_mod (a + (d - 1)) d
  have h2 := Nat.mod_lt (a + (d - 1)) hd
  rw [Nat.mul_comm]
  omega

end FORS.Security.H0
