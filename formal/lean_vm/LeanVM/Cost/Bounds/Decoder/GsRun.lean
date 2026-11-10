module

public import LeanVM.Cost.Bounds.Decoder.Roots
public import LeanVM.Cost.Extractor.PMLane
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Basic

/-!
# Bound: one node of Roth–Ruckenstein's search, compiled

The prices of the pieces of a node of `prefixesNF` (`Cost/Extractor/GsRun.lean`), on a node of at
most `Y` rows of at most `X` coefficients:

* the `X`-adic order (`xAdicOrderBC_cost`), the division by `X^s` (`divXPowerFastC_cost`), the
  initial coefficient polynomial (`initialCoeffFastC_cost`), its roots
  (`rootsNonzeroC_cost`, the root finder of `Bounds/Decoder/Roots.lean`);
* the substitution `Y := a + X·Y` by the butterfly (`substituteBFC_cost`: the Taylor shift's
  `log₂ Y + 1` levels, `bfLoopC_cost`, each a power by squaring and `bfLevelC_cost`, a row
  gaining at most one scaled row `u + c·v`, its raw sum trimmed once, `bfLevelLamC_cost`; then
  each row shifted by `X^t`, `shiftXC_cost`), the truncation (`truncateXC_cost`), the prefix
  extended (`extendPrefixC_cost`);
* the lane filter's pieces: Horner's evaluation, the mismatch count (`mismatchCountC_cost`),
  `degreeLtBool`.

The recursion itself, and the run, are bounded in `Bounds/Decoder/Prefixes.lean`.

**Looseness.** The bound charges a scaled row addition (`100` per coefficient) to every row of
every level, `(log₂ Y + 1)·Y` of them; the butterfly makes one per bit set below `Y` (`8631` at
`Y = 1663`, against `11·1663 = 18293` charged). The former substitution (`substituteFast`, a
Taylor coefficient per row, `≈ Y²/2` scaled additions) cost `O(X·Y²)` per node.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-! ## Orders and divisions by powers of `X` -/

theorem cpoly_xAdicOrder?_lt {p : CPolynomial K} {v : ℕ} (h : CPolynomial.xAdicOrder? p = some v) :
    v < p.val.size := by
  unfold CPolynomial.xAdicOrder? at h
  have := List.mem_of_find?_eq_some h
  rw [List.mem_range'] at this
  omega

/-- The `X`-adic order of a polynomial over `K`: at most `38·|p| + 17`. -/
theorem xAdicOrderC_cost (hP : Includes P Auto.CompPoly.CPolynomial.xAdicOrder?.c83.costDeps)
    (p : CPolynomial K) (hp : p.val.size < 2 ^ 62) :
    machineCost P Auto.CompPoly.CPolynomial.xAdicOrder?.c83.costIdx [encodeValue p] ≤ 38 * p.val.size + 17 := by
  rw [Auto.CompPoly.CPolynomial.xAdicOrder?.c83.costEq P hP]
  have := rangeC_cost P (by includes) p.val.size 0 (by omega)
  have hf := fun i ↦ RunsApp.of_spec (us := [encodeValue p]) (vs := [encodeValue i])
    (Auto.CompPoly.CPolynomial.xAdicOrder?.c83.lam0.costSpec P (by includes) p i)
  have := findNat_cost P (by includes) _ (.closure Auto.CompPoly.CPolynomial.xAdicOrder?.c83.lam0.costIdx
    [encodeValue p]) hf 9 (List.range' 0 p.val.size) (fun i _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.CPolynomial.xAdicOrder?.c83.lam0.costEq P (by includes)])
  simp only [List.length_range'] at this
  omega

/-- **The `X`-adic order of a bivariate polynomial** (`xAdicOrder?`, the least over its rows):
at most `(38·X + 67)·|Q| + 18`, rows of at most `X` coefficients. -/
theorem xAdicOrderBC_cost (hP : Includes P Auto.CompPoly.CBivariate.xAdicOrder?.c81.costDeps)
    (Q : CBivariate K) {X : ℕ} (hX : X < 2 ^ 60) (hQ : InnerLe Q.val X) (hQs : Q.val.size < 2 ^ 60) :
    machineCost P Auto.CompPoly.CBivariate.xAdicOrder?.c81.costIdx [encodeValue Q] ≤
      (38 * X + 67) * Q.val.size + 18 := by
  rw [Auto.CompPoly.CBivariate.xAdicOrder?.c81.costEq P hP]
  have := rangeC_cost P (by includes) Q.val.size 0 (by omega)
  have hf := listFoldl_le P (by includes) _
    (.closure Auto.CompPoly.CBivariate.xAdicOrder?.c81.lam0.costIdx [encodeValue Q])
    (fun best y ↦ RunsApp.of_spec (us := [encodeValue Q]) (vs := [encodeValue best, encodeValue y])
      (Auto.CompPoly.CBivariate.xAdicOrder?.c81.lam0.costSpec P (by includes) Q best y))
    (38 * X + 38) (fun best ↦ ∀ v, best = some v → v < 2 ^ 60) (List.range' 0 Q.val.size) none
    (by simp)
    (fun best hb y _ ↦ by
      have hcs := coeff_size_le_of_innerLe hQ y
      refine ⟨?_, ?_⟩
      · intro v hv
        generalize ho : CPolynomial.xAdicOrder? (Q.val.coeff y) = o at hv
        cases o with
        | none => exact hb v hv
        | some w =>
          have := cpoly_xAdicOrder?_lt ho
          cases best with
          | none => simp only [Option.some.injEq] at hv; omega
          | some b =>
            have := hb b rfl
            simp only [Option.some.injEq] at hv
            omega
      · simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [Auto.CompPoly.CBivariate.xAdicOrder?.c81.lam0.costEq P (by includes)]
        have := xAdicOrderC_cost P (by includes) (Q.val.coeff y) (by omega)
        generalize ho : CPolynomial.xAdicOrder? (Q.val.coeff y) = o
        cases o with
        | none => dsimp only; omega
        | some w =>
          have := cpoly_xAdicOrder?_lt ho
          cases best with
          | none => dsimp only; omega
          | some b =>
            have := hb b rfl
            dsimp only
            cost_simp
            split_ifs <;> omega)
  simp only [List.length_range'] at hf
  have e : (38 * X + 67) * Q.val.size = (38 * X + 38 + 11) * Q.val.size + 18 * Q.val.size := by
    ring
  omega

theorem dropXPowerFast_size_le (p : CPolynomial K) (n : ℕ) :
    (dropXPowerFast p n).val.size ≤ p.val.size :=
  (raw_trim_size_le _).trans (by simp)

/-- `p / X^n` (`dropXPowerFast`): at most `22·|p| + 20`. -/
theorem dropXPowerFastC_cost (hP : Includes P dropXPowerFast.c91.costDeps) (p : CPolynomial K)
    (n : ℕ) (hp : p.val.size < 2 ^ 60) :
    machineCost P dropXPowerFast.c91.costIdx [encodeValue p, encodeValue n] ≤ 22 * p.val.size + 20 := by
  rw [dropXPowerFast.c91.costEq P hP]
  have h1 : (Array.extract p.val n).size ≤ p.val.size := by simp
  have := ofArray_cost P (by includes) (Array.extract p.val n) (by omega)
  omega

/-- **`Q / X^n`** (`divXPowerFast`, each row): at most `(25·X + 73)·|Q| + 25`. -/
theorem divXPowerFastC_cost (hP : Includes P divXPowerFast.c87.costDeps) (Q : CBivariate K)
    (n : ℕ) {X : ℕ} (hX : X < 2 ^ 58) (hQ : InnerLe Q.val X) (hQs : Q.val.size < 2 ^ 58) :
    machineCost P divXPowerFast.c87.costIdx [encodeValue Q, encodeValue n] ≤ (25 * X + 73) * Q.val.size + 25 := by
  rw [divXPowerFast.c87.costEq P hP]
  have hf := fun c ↦ RunsApp.of_spec (us := [encodeValue n]) (vs := [encodeValue c])
    (divXPowerFast.c87.lam0.costSpec P (by includes) n c)
  have hm := listMap_le P Auto.List.map.c30.costIdx (.closure divXPowerFast.c87.lam0.costIdx [encodeValue n])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) (22 * X + 24) Q.val.toList
    (fun c hc ↦ by
      rw [appCost_fn, List.singleton_append, List.length_singleton,
        divXPowerFast.c87.lam0.costEq P (by includes)]
      have := hQ c (by simpa using hc)
      have := dropXPowerFastC_cost P (by includes) c n (by omega)
      omega)
  have := ofArrayB_cost P (by includes) (Q.val.map fun c ↦ dropXPowerFast c n) X
    (fun x hx ↦ by
      obtain ⟨c, hc, rfl⟩ := Array.mem_map.1 hx
      exact (dropXPowerFast_size_le c n).trans (hQ c hc))
    (by simp; omega)
  simp only [Array.length_toList, List.length_map, Array.size_map] at hm this ⊢
  have e : (25 * X + 73) * Q.val.size =
      (22 * X + 24 + 13) * Q.val.size + (3 * X + 32) * Q.val.size + 4 * Q.val.size := by ring
  omega

/-- **The initial coefficient polynomial** (`initialCoeffFast`: each row's constant term):
at most `42·|Q| + 23`. -/
theorem initialCoeffFastC_cost (hP : Includes P initialCoeffFast.c109.costDeps) (Q : CBivariate K)
    (hQs : Q.val.size < 2 ^ 60) :
    machineCost P initialCoeffFast.c109.costIdx [encodeValue Q] ≤ 42 * Q.val.size + 23 := by
  rw [initialCoeffFast.c109.costEq P hP]
  have hf := fun c ↦ RunsApp.of_spec (us := []) (vs := [encodeValue c])
    (initialCoeffFast.c109.lam0.costSpec P (by includes) c)
  have hm := listMap_le P Auto.List.map.c30.costIdx (.closure initialCoeffFast.c109.lam0.costIdx [])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) 4 Q.val.toList
    (fun c _ ↦ by rw [appCost_fn, List.nil_append, initialCoeffFast.c109.lam0.costEq P (by includes)]; simp)
  have := ofArray_cost P (by includes) (Q.val.map fun c ↦ c.coeff 0) (by simp; omega)
  simp only [Array.length_toList, List.length_map, Array.size_map] at hm this ⊢
  omega

theorem initialCoeffFast_size_le (Q : CBivariate K) :
    (initialCoeffFast Q).val.size ≤ Q.val.size :=
  (raw_trim_size_le _).trans (by simp)

/-- **The roots of the initial coefficient polynomial** (`rootsInFieldForNonzeroEquation`, the root
finder on a nonzero polynomial of at most `B` coefficients): at most `rootsBound B + 3·B + 16`. -/
theorem rootsNonzeroC_cost
    (hP : Includes P Auto.CompPoly.GuruswamiSudan.rootsInFieldForNonzeroEquation.c108.costDeps)
    {B : ℕ} (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (p : CPolynomial K) (hp : p.val.size ≤ B) :
    machineCost P Auto.CompPoly.GuruswamiSudan.rootsInFieldForNonzeroEquation.c108.costIdx [encodeValue p] ≤
      rootsBound B + 3 * B + 16 := by
  rw [Auto.CompPoly.GuruswamiSudan.rootsInFieldForNonzeroEquation.c108.costEq P hP]
  have := beqNilK_cost P (by includes) p.val.toList
  have := rootsInFieldC_cost P (by includes) hB hB2 p hp
  simp only [size_zero_val, toList_zero_val] at *
  split_ifs <;> omega

/-! ## The substitution `Y := a + X·Y` -/

theorem cpoly_smul_size_le (r : K) (p : CPolynomial K) : (r • p).val.size ≤ p.val.size := by
  show (CPolynomial.Raw.smul r p.val).trim.size ≤ _
  exact (raw_trim_size_le _).trans (by rw [size_smul])

theorem taylorCoeff_size_le {Q : CBivariate K} {X : ℕ} (hQ : InnerLe Q.val X) (a : K) (t : ℕ) :
    (taylorCoeff Q a t).val.size ≤ X := by
  unfold taylorCoeff
  suffices ∀ (l : List ℕ) (acc : CPolynomial K), acc.val.size ≤ X →
      (l.foldl (fun acc y ↦ if chooseOdd y t then acc + a ^ (y - t) • Q.val.coeff y else acc)
        acc).val.size ≤ X from this _ 0 (by simp [size_zero_val])
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons y l ih =>
    intro acc h
    apply ih
    dsimp only
    split_ifs
    · have := cpoly_add_size_le acc (a ^ (y - t) • Q.val.coeff y)
      have := cpoly_smul_size_le (a ^ (y - t)) (Q.val.coeff y)
      have := coeff_size_le_of_innerLe hQ y
      omega
    · exact h

theorem axpyRow_size_le (u : CPolynomial K) (c : K) (v : CPolynomial K) :
    (axpyRow u c v).val.size ≤ max u.val.size v.val.size := by
  show (CPolynomial.Raw.trim (CPolynomial.Raw.addRaw u.val (CPolynomial.Raw.smul c v.val))).size ≤ _
  refine (raw_trim_size_le _).trans ?_
  rw [size_addRaw, size_smul]

theorem getD_size_le {rows : Array (CPolynomial K)} {X : ℕ} (h : InnerLe rows X) (i : ℕ) :
    (rows.getD i 0).val.size ≤ X := by
  rw [Array.getD_eq_getD_getElem?]
  cases hi : rows[i]? with
  | none => exact Nat.zero_le _
  | some r => exact h r (Array.mem_of_getElem? hi)

theorem bfLevel_innerLe {rows : Array (CPolynomial K)} {X : ℕ} (h : InnerLe rows X) (hh : ℕ)
    (c : K) : InnerLe (bfLevel rows hh c) X := by
  intro r hr
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hr
  have h1 := getD_size_le h i.val
  have h2 := getD_size_le h (i.val + hh)
  split
  · have := axpyRow_size_le (rows.getD i.val 0) c (rows.getD (i.val + hh) 0)
    omega
  · exact h1

theorem bfLoop_innerLe (a : K) {X : ℕ} : ∀ (fuel : ℕ) (rows : Array (CPolynomial K)) (hh : ℕ),
    InnerLe rows X → InnerLe (bfLoop a fuel rows hh) X
  | 0, rows, hh, h => by rw [bfLoop]; exact h
  | fuel + 1, rows, hh, h => by
    rw [bfLoop]
    split
    · exact bfLoop_innerLe a fuel _ _ (bfLevel_innerLe h hh _)
    · exact h

/-- One entry of a butterfly level (`bfLevel`'s closure: unless it is kept, `u + c·v` with the
raw sum trimmed once), rows of at most `X` coefficients: at most `100·X + 101`. -/
theorem bfLevelLamC_cost (hP : Includes P bfLevel.c99.lam0.costDeps)
    (rows : Array (CPolynomial K)) (hh : ℕ) (c : K) (i : Fin rows.size) {X : ℕ} (hX : X < 2 ^ 56)
    (hr : InnerLe rows X) (hn : rows.size < 2 ^ 56) (hh' : hh < 2 ^ 56) :
    machineCost P bfLevel.c99.lam0.costIdx
      [encodeValue rows, encodeValue hh, encodeValue c, encodeValue i] ≤ 100 * X + 101 := by
  rw [bfLevel.c99.lam0.costEq P hP]
  have hi := i.isLt
  have h1 := getD_size_le hr i.val
  have h2 := getD_size_le hr (i.val + hh)
  generalize rows.getD i.val 0 = u at h1 ⊢
  generalize rows.getD (i.val + hh) 0 = v at h2 ⊢
  have := smulK_cost P (by includes) c v.val
  have := addRawK_cost P (by includes) u.val (CPolynomial.Raw.smul c v.val) (by omega)
    (by rw [size_smul]; omega)
  have := ofArray_cost P (by includes) (u.val.addRaw (CPolynomial.Raw.smul c v.val))
    (by rw [size_addRaw, size_smul]; omega)
  rw [size_addRaw, size_smul] at *
  have hdiv : i.val / hh ≤ i.val := Nat.div_le_self _ _
  have hmod : i.val / hh % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [limbs_of_lt (show i.val < 2 ^ 64 by omega), limbs_of_lt (show hh < 2 ^ 64 by omega),
    limbs_of_lt (show i.val / hh < 2 ^ 64 by omega), limbs_of_lt (show i.val / hh % 2 < 2 ^ 64 by omega),
    limbs_of_lt (show i.val + hh < 2 ^ 64 by omega), limbs_of_lt (show rows.size < 2 ^ 64 by omega)]
  split_ifs <;> omega

/-- **One butterfly level** (`bfLevel`), `n` rows of at most `X` coefficients: at most
`(100·X + 121)·n + 17`. -/
theorem bfLevelC_cost (hP : Includes P bfLevel.c99.costDeps) (rows : Array (CPolynomial K))
    (hh : ℕ) (c : K) {X : ℕ} (hX : X < 2 ^ 56) (hr : InnerLe rows X) (hn : rows.size < 2 ^ 56)
    (hh' : hh < 2 ^ 56) :
    machineCost P bfLevel.c99.costIdx [encodeValue rows, encodeValue hh, encodeValue c] ≤
      (100 * X + 121) * rows.size + 17 := by
  rw [bfLevel.c99.costEq P hP]
  have hf := fun i ↦ RunsApp.of_spec (us := [encodeValue rows, encodeValue hh, encodeValue c])
    (vs := [encodeValue i]) (bfLevel.c99.lam0.costSpec P (by includes) rows hh c i)
  have := ofFnFrom_cost P (by includes) (n := rows.size) (by omega) _
    (.closure bfLevel.c99.lam0.costIdx [encodeValue rows, encodeValue hh, encodeValue c]) hf
    (100 * X + 104) (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      have := bfLevelLamC_cost P (by includes) rows hh c i hX hr hn hh'
      omega) 0 (by omega)
  simp only [length_ofFnFrom, Nat.sub_zero] at *
  have e : (100 * X + 121) * rows.size = (100 * X + 104 + 16) * rows.size + rows.size := by
    ring
  omega

/-- **The butterfly's levels** (`bfLoop`: while `h` is below the rows' number, a level at
`c = a^h`, then `2·h`), `n ≤ Y` rows of at most `X` coefficients, `h ≤ 2·Y + 1`, `h·2^L ≥ n`: at
most `bfLoopBound X Y L`. -/
theorem bfLoopC_cost (hP : Includes P bfLoop.c98.costDeps) (a : K) {X Y : ℕ} (hX : X < 2 ^ 56)
    (hY : Y < 2 ^ 56) : ∀ (L fuel : ℕ) (rows : Array (CPolynomial K)) (hh : ℕ),
      InnerLe rows X → rows.size ≤ Y → fuel < 2 ^ 64 → hh ≤ 2 * Y + 1 → rows.size ≤ hh * 2 ^ L →
      machineCost P bfLoop.c98.costIdx [encodeValue a, encodeValue fuel, encodeValue rows,
        encodeValue hh] ≤ bfLoopBound X Y L := by
  intro L
  induction L with
  | zero =>
    intro fuel rows hh hr hn hf hh2 hL
    simp only [pow_zero, Nat.mul_one] at hL
    cases fuel with
    | zero => rw [bfLoop.c98.costEq_zero P hP]; unfold bfLoopBound; omega
    | succ fuel =>
      rw [bfLoop.c98.costEq_succ P hP]
      rw [limbs_of_lt hf, limbs_of_lt (show rows.size < 2 ^ 64 by omega),
        limbs_of_lt (show hh < 2 ^ 64 by omega)]
      unfold bfLoopBound
      split_ifs with h
      · omega
      · omega
  | succ L ih =>
    intro fuel rows hh hr hn hf hh2 hL
    cases fuel with
    | zero => rw [bfLoop.c98.costEq_zero P hP]; unfold bfLoopBound; omega
    | succ fuel =>
      rw [bfLoop.c98.costEq_succ P hP]
      rw [limbs_of_lt hf, limbs_of_lt (show rows.size < 2 ^ 64 by omega),
        limbs_of_lt (show hh < 2 ^ 64 by omega)]
      split_ifs with h
      · have hlv := bfLevelC_cost P (by includes) rows hh (a ^ hh) hX hr (by omega) (by omega)
        have hpw := powSq_cost P (by includes) a hh (by omega)
        have hlog : Nat.log2 hh ≤ Nat.log2 Y := log2_mono (by omega)
        have hrec := ih fuel (bfLevel rows hh (a ^ hh)) (2 * hh) (bfLevel_innerLe hr hh _)
          (by rw [size_bfLevel]; omega) (by omega) (by omega)
          (by rw [size_bfLevel, show 2 * hh * 2 ^ L = hh * 2 ^ (L + 1) by rw [pow_succ]; ring]
              exact hL)
        have h1 : (100 * X + 121) * rows.size ≤ (100 * X + 121) * Y := Nat.mul_le_mul_left _ hn
        rw [limbs_of_lt (show 2 * hh < 2 ^ 64 by omega)]
        unfold bfLoopBound at hrec ⊢
        have e : (L + 1) * ((100 * X + 121) * Y + 73 * (Nat.log2 Y + 1) + 47) =
            L * ((100 * X + 121) * Y + 73 * (Nat.log2 Y + 1) + 47) +
              ((100 * X + 121) * Y + 73 * (Nat.log2 Y + 1) + 47) := by ring
        omega
      · unfold bfLoopBound
        omega

theorem taylorShiftBF_innerLe {Q : CBivariate K} {X : ℕ} (hQ : InnerLe Q.val X) (a : K) :
    InnerLe (taylorShiftBF Q.val a) X :=
  bfLoop_innerLe a _ _ _ hQ

/-- **The substitution `Y := a + X·Y`, by the butterfly** (`substituteBF`: the Taylor shift's
`log₂ Y + 1` levels, then per row its shift by `X^t`): at most `substBound X Y`, its rows of at
most `X + Y` coefficients. -/
theorem substituteBFC_cost (hP : Includes P substituteBF.c97.costDeps) (Q : CBivariate K)
    (a : K) {X Y : ℕ} (hX : X < 2 ^ 56) (hY : Y < 2 ^ 56) (hQ : InnerLe Q.val X)
    (hQs : Q.val.size ≤ Y) :
    machineCost P substituteBF.c97.costIdx [encodeValue Q, encodeValue a] ≤ substBound X Y := by
  rw [substituteBF.c97.costEq P hP]
  have hY1 : Y < 2 ^ (Nat.log2 Y + 1) := Nat.lt_log2_self
  have hloop := bfLoopC_cost P (by includes) a hX hY (Nat.log2 Y + 1) Q.val.size Q.val 1 hQ hQs
    (by omega) (by omega) (by rw [Nat.one_mul]; omega)
  have hrows := taylorShiftBF_innerLe hQ a
  have hsz : (taylorShiftBF Q.val a).size = Q.val.size := size_taylorShiftBF Q.val a
  have hf := fun t ↦ RunsApp.of_spec (us := [encodeValue Q, encodeValue (taylorShiftBF Q.val a)])
    (vs := [encodeValue t]) (substituteBF.c97.lam0.costSpec P (by includes) Q (taylorShiftBF Q.val a) t)
  have := ofFnFrom_cost P (by includes) (n := Q.val.size) (by omega) _
    (.closure substituteBF.c97.lam0.costIdx [encodeValue Q, encodeValue (taylorShiftBF Q.val a)])
    hf (23 * (X + Y) + 29) (fun t ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [substituteBF.c97.lam0.costEq P (by includes)]
      have ht := t.isLt
      have hr := getD_size_le hrows t.val
      have := shiftXC_cost P (by includes) t ((taylorShiftBF Q.val a).getD t.val 0) (by omega)
      have : 23 * (↑t + ((taylorShiftBF Q.val a).getD t.val 0).val.size) ≤ 23 * (X + Y) := by
        omega
      omega) 0 (by omega)
  have := ofArrayB_cost P (by includes)
    (Array.ofFn fun t : Fin Q.val.size ↦ shiftX t.val ((taylorShiftBF Q.val a).getD t.val 0)) (X + Y)
    (fun x hx ↦ by
      obtain ⟨t, rfl⟩ := Array.mem_ofFn.1 hx
      have := getD_size_le hrows t.val
      have h1 : (shiftX t.val ((taylorShiftBF Q.val a).getD t.val 0)).val.size ≤
          t.val + ((taylorShiftBF Q.val a).getD t.val 0).val.size :=
        (raw_trim_size_le _).trans (by simp)
      have := t.isLt
      omega)
    (by simp; omega)
  simp only [length_ofFnFrom, Array.size_ofFn, Nat.sub_zero] at *
  have h1 : (23 * (X + Y) + 29 + 16) * Q.val.size ≤ (23 * (X + Y) + 45) * Y :=
    Nat.mul_le_mul_left _ hQs
  have h2 : (3 * (X + Y) + 32) * Q.val.size ≤ (3 * (X + Y) + 32) * Y := Nat.mul_le_mul_left _ hQs
  have e : (26 * (X + Y) + 78) * Y = (23 * (X + Y) + 45) * Y + (3 * (X + Y) + 32) * Y + Y := by
    ring
  unfold substBound
  omega

theorem substituteFast_sizes {Q : CBivariate K} {X : ℕ} (hQ : InnerLe Q.val X) (a : K) :
    (substituteFast Q a).val.size ≤ Q.val.size ∧
      InnerLe (substituteFast Q a).val (X + Q.val.size) := by
  refine ⟨(raw_trim_size_le _).trans (by simp), ?_⟩
  refine InnerLe.trim (fun x hx ↦ ?_)
  obtain ⟨t, rfl⟩ := Array.mem_ofFn.1 hx
  have := taylorCoeff_size_le hQ a t
  have h1 : (shiftX t.val (taylorCoeff Q a t.val)).val.size ≤ t.val + (taylorCoeff Q a t).val.size :=
    (raw_trim_size_le _).trans (by simp)
  have := t.isLt
  omega

theorem substituteBF_sizes {Q : CBivariate K} {X : ℕ} (hQ : InnerLe Q.val X) (a : K) :
    (substituteBF Q a).val.size ≤ Q.val.size ∧
      InnerLe (substituteBF Q a).val (X + Q.val.size) := by
  rw [substituteBF_eq]
  exact substituteFast_sizes hQ a

/-- `p mod X^n` (`truncate`): at most `22·|p| + 19`. -/
theorem truncateC_cost (hP : Includes P Auto.CompPoly.CPolynomial.truncate.c96.costDeps)
    (p : CPolynomial K) (n : ℕ) (hp : p.val.size < 2 ^ 60) :
    machineCost P Auto.CompPoly.CPolynomial.truncate.c96.costIdx [encodeValue p, encodeValue n] ≤
      22 * p.val.size + 19 := by
  rw [Auto.CompPoly.CPolynomial.truncate.c96.costEq P hP]
  have h1 : (Array.extract p.val 0 n).size ≤ p.val.size := by simp
  have := ofArray_cost P (by includes) (Array.extract p.val 0 n) (by omega)
  omega

/-- **`Q mod X^n`** (`truncateX`, each row): at most `(25·X + 72)·|Q| + 25`. -/
theorem truncateXC_cost (hP : Includes P Auto.CompPoly.CBivariate.truncateX.c94.costDeps)
    (Q : CBivariate K) (n : ℕ) {X : ℕ} (hX : X < 2 ^ 60) (hQ : InnerLe Q.val X)
    (hQs : Q.val.size < 2 ^ 58) :
    machineCost P Auto.CompPoly.CBivariate.truncateX.c94.costIdx [encodeValue Q, encodeValue n] ≤
      (25 * X + 72) * Q.val.size + 25 := by
  rw [Auto.CompPoly.CBivariate.truncateX.c94.costEq P hP]
  have hf := fun c ↦ RunsApp.of_spec (us := [encodeValue n]) (vs := [encodeValue c])
    (Auto.CompPoly.CBivariate.truncateX.c94.lam0.costSpec P (by includes) n c)
  have hm := listMap_le P Auto.List.map.c30.costIdx
    (.closure Auto.CompPoly.CBivariate.truncateX.c94.lam0.costIdx [encodeValue n])
    (Auto.List.map.c30.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c30.costEq_cons P (by includes) _ _ hf) (22 * X + 23) Q.val.toList
    (fun c hc ↦ by
      rw [appCost_fn, List.singleton_append, List.length_singleton,
        Auto.CompPoly.CBivariate.truncateX.c94.lam0.costEq P (by includes)]
      have := hQ c (by simpa using hc)
      have := truncateC_cost P (by includes) c n (by omega)
      omega)
  have := ofArrayB_cost P (by includes) (Q.val.map fun c ↦ CPolynomial.truncate c n) X
    (fun x hx ↦ by
      obtain ⟨c, hc, rfl⟩ := Array.mem_map.1 hx
      have := hQ c hc
      have : (CPolynomial.truncate c n).val.size ≤ c.val.size :=
        (raw_trim_size_le _).trans (by simp)
      omega)
    (by simp; omega)
  simp only [Array.length_toList, List.length_map, Array.size_map] at hm this ⊢
  have e : (25 * X + 72) * Q.val.size =
      (22 * X + 23 + 13) * Q.val.size + (3 * X + 32) * Q.val.size + 4 * Q.val.size := by ring
  omega

/-- **The prefix extended** (`extendPrefix pref depth a = pref + a·X^depth`): at most
`53·(|pref| + depth + 1) + 2·depth + 86`. -/
theorem extendPrefixC_cost (hP : Includes P Auto.CompPoly.GuruswamiSudan.extendPrefix.c104.costDeps)
    (pref : CPolynomial K) (depth : ℕ) (a : K) (hp : pref.val.size < 2 ^ 58)
    (hd : depth < 2 ^ 58) :
    machineCost P Auto.CompPoly.GuruswamiSudan.extendPrefix.c104.costIdx
      [encodeValue pref, encodeValue depth, encodeValue a] ≤ 53 * (pref.val.size + depth + 1) + 2 * depth + 86 := by
  rw [Auto.CompPoly.GuruswamiSudan.extendPrefix.c104.costEq P hP,
    Auto.CompPoly.CPolynomial.monomial.c105.costEq P (by includes),
    Auto.CompPoly.CPolynomial.Raw.monomial.c106.costEq P (by includes)]
  have hm : (CPolynomial.monomial depth a).val.size ≤ depth + 1 := by
    show (CPolynomial.Raw.monomial depth a).size ≤ _
    unfold CPolynomial.Raw.monomial
    split <;> simp [CPolynomial.Raw.mk]
  have := addK_cost P (by includes) pref.val (CPolynomial.monomial depth a).val (by omega)
    (by omega)
  simp only [Array.size_replicate, List.size_toArray, List.length_cons, List.length_nil] at *
  split_ifs <;> omega


/-! ## The lane filter -/

/-- `p(x)` by Horner's rule (`hornerEval`): at most `46·|p| + 10`. -/
theorem hornerEvalC_cost (hP : Includes P hornerEval.c652.costDeps) (x : K) (p : CPolynomial K) :
    machineCost P hornerEval.c652.costIdx [encodeValue x, encodeValue p] ≤ 46 * p.val.size + 10 := by
  rw [hornerEval.c652.costEq P hP]
  have := foldr_cost P (by includes) _ (.closure hornerEval.c652.lam0.costIdx [encodeValue x])
    (fun a acc ↦ RunsApp.of_spec (us := [encodeValue x]) (vs := [encodeValue a, encodeValue acc])
      (hornerEval.c652.lam0.costSpec P (by includes) x a acc)) 32 (0 : K) p.val.toList
    (fun a _ acc ↦ by
      rw [appCost_fn, List.singleton_append, hornerEval.c652.lam0.costEq P (by includes)]; simp)
  simp only [Array.length_toList] at this
  omega

/-- **The mismatch count** (`mismatchCountFast`: `p` evaluated at each of `n` points): at most
`(46·|p| + 36)·n + 10`. -/
theorem mismatchCountC_cost (hP : Includes P mismatchCountFast.c650.costDeps)
    (points : Array (K × K)) (p : CPolynomial K) (hn : points.size < 2 ^ 63) :
    machineCost P mismatchCountFast.c650.costIdx [encodeValue points, encodeValue p] ≤
      (46 * p.val.size + 36) * points.size + 10 := by
  rw [mismatchCountFast.c650.costEq P hP]
  have := listFoldl_le_idx P (by includes) _ (.closure mismatchCountFast.c650.lam0.costIdx [encodeValue p])
    (fun c pt ↦ RunsApp.of_spec (us := [encodeValue p]) (vs := [encodeValue c, encodeValue pt])
      (mismatchCountFast.c650.lam0.costSpec P (by includes) p c pt)) (46 * p.val.size + 22)
    (fun k c ↦ c + k ≤ points.size) points.toList
    (fun k c hc pt _ ↦ by
      refine ⟨by split_ifs <;> omega, ?_⟩
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [mismatchCountFast.c650.lam0.costEq P (by includes)]
      have := hornerEvalC_cost P (by includes) pt.1 p
      cost_simp
      split_ifs <;> omega)
    points.toList 0 (fun _ h ↦ h) (by simp)
  simp only [Array.length_toList] at this
  have e : (46 * p.val.size + 36) * points.size =
      (46 * p.val.size + 22 + 11) * points.size + 3 * points.size := by ring
  omega

theorem mismatchCountFast_le (points : Array (K × K)) (p : CPolynomial K) :
    mismatchCountFast points p ≤ points.size := by
  unfold mismatchCountFast
  rw [← Array.foldl_toList]
  suffices ∀ (l : List (K × K)) (c : ℕ), l.foldl (fun count point ↦
      if hornerEval point.1 p == point.2 then count else count + 1) c ≤ c + l.length by
    simpa using this points.toList 0
  intro l
  induction l with
  | nil => intro c; simp
  | cons x l ih =>
    intro c
    rw [List.foldl_cons]
    simp only [List.length_cons]
    by_cases h : (hornerEval x.1 p == x.2) = true
    · simp only [h, ↓reduceIte]; have := ih c; omega
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; have := ih (c + 1); omega


/-! ## Roth–Ruckenstein's prefixes: sizes -/

theorem mem_foldl_append {α β : Type} (g : α → Array β) :
    ∀ (l : List α) (init : Array β) (x : β), x ∈ l.foldl (fun out a ↦ out ++ g a) init →
      x ∈ init ∨ ∃ a ∈ l, x ∈ g a := by
  intro l
  induction l with
  | nil => intro init x h; exact Or.inl h
  | cons a l ih =>
    intro init x h
    rcases ih _ x h with h | ⟨b, hb, hx⟩
    · rcases Array.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, by simp, h⟩
    · exact Or.inr ⟨b, by simp [hb], hx⟩

theorem extendPrefix_size_le (pref : CPolynomial K) (depth : ℕ) (a : K) :
    (GuruswamiSudan.extendPrefix pref depth a).val.size ≤ max pref.val.size (depth + 1) := by
  have hm : (CPolynomial.monomial depth a).val.size ≤ depth + 1 := by
    show (CPolynomial.Raw.monomial depth a).size ≤ _
    unfold CPolynomial.Raw.monomial
    split <;> simp [CPolynomial.Raw.mk]
  have := cpoly_add_size_le pref (CPolynomial.monomial depth a)
  show (pref + CPolynomial.monomial depth a).val.size ≤ _
  omega

/-- **Roth–Ruckenstein's prefixes have at most `depth + fuel` coefficients.** -/
theorem prefixesWithFuelFast_mem_size_le (fr : GuruswamiSudan.FieldRootContext K) (fuel : ℕ) :
    ∀ (Q : CBivariate K) (depth : ℕ) (pref : CPolynomial K), pref.val.size ≤ depth →
      ∀ p ∈ prefixesWithFuelFast fr fuel Q depth pref, p.val.size ≤ depth + fuel := by
  induction fuel with
  | zero =>
    intro Q depth pref hp p hmem
    simp only [prefixesWithFuelFast, Array.mem_singleton] at hmem
    subst hmem; omega
  | succ fuel ih =>
    intro Q depth pref hp p hmem
    rw [prefixesWithFuelFast] at hmem
    split at hmem
    · simp at hmem
    · rw [← Array.foldl_toList] at hmem
      rcases mem_foldl_append _ _ _ p hmem with h | ⟨a, -, ha⟩
      · simp at h
      · have := ih _ (depth + 1) _ (by have := extendPrefix_size_le pref depth a; omega) p ha
        omega

open CompPoly.GuruswamiSudan in
end

end LeanVM.Cost.Bounds.Decoder
