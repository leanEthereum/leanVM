/-
  LeanVM.Protocol.Link.Sound

  The soundness of `verify_link`'s two chained sum-checks in the sample model: an accepting run
  with correct output claims implies the link's identities, except with the paper's error
  (Theorem 5.4 of the Hotwire paper), from the arithmetization's facts and the Schwartz-Zippel
  counts.
-/

module

public import LeanVM.Protocol.Link.Sumcheck
public import LeanVM.Protocol.Link.Skeleton

/-!
# The link's sum-checks, sound

`verifyLink` (`Statement/Verifier/Link.lean`, `verify_link` in `crates/verifier/src/link.rs`) draws
`θ_0` and the packed challenges, runs the index side's sum-check over the pointer width `W` (degree
`2`, three coefficients a round) from `indexClaim`, reads the memory term `m1`, draws five fresh
coefficients (the certificate's `α_onehot` and `JUMP`'s four, after `r`), runs the row side's
sum-check over the `m` row variables and the `m_Q` pointer-column variables from the index side's
final claim, reads the values at the row point and the bit-slices, and checks the summand
(`linkSkeleton`, `verifyLink_eq_linkSkeleton`).

`verifyLink_sound` bounds the best prover's chance (`win`, the sample model) of an accepting run
whose output `LinkEnd` satisfies `Win` (its claims on the commitment correct) when the commitment
fails the link: some used pointer's chunk is not one-hot (`¬ OneHot`), or a lookup or the state link
fails (`¬ LinksHold`). The proof is the paper's (Theorem 5.4's sketch), case by case, the case fixed
by the commitment:

* **(a) not one-hot.** The index side's challenges are uniform whatever the prover sends
  (`win_sumcheck_le`). At `(θ_0, drawn, r)` the one-hot term `B_0` (the coefficient of `α_onehot`
  in the row side's true sum) is nonzero except on `D_A·|E|^(N+W)` of the points (`hA`: the mirror
  test's Schwartz-Zippel bound, `D_A = m + 3 + 2·w_max`). The row side's true sum is affine in the
  fresh coefficients with that nonzero coefficient, so the index side's final claim, fixed before
  them, is it for at most `|E|^4` of the `|E|^5` (`card_fresh_le`); off those the row side's claim is
  false.
* **(b) one-hot, a link fails.** The index side's claim differs from the true sum by the link's
  error `errB` (the state link's defect plus `η`-weighted lookup identities), nonzero except on
  `D_B·|E|^N` of the challenge points (`hB`: Schwartz-Zippel, `D_B = max(W + 1, m + 3 + ν)`,
  `card_linkError_le`).
  A false claim survives the index side with probability at most `2W/|E|`
  (`win_sumcheck_le_of_ne`); its final claim then differs from the true index summand at `r`, the
  row side's true sum at fresh coefficients off `|E|^4` of them.

In both, a false row-side claim survives its `m` rounds of degree `Δ = max(d + 2, 4)` and `m_Q`
rounds of degree `max(d + 1, 3)` with probability at most `(m·Δ + m_Q·(max(d+1, 3)))/|E|`
(`win_linkRowPhase_le`), and with a false final claim the terminal check rejects every output with
correct claims (`htail`). Summing, the bound is
`(max(D_A, D_B + 2W) + 1 + m·Δ + m_Q·max(d + 1, 3))/|E|`.

## What the theorem takes

The theorem is stated against `verifyLink` itself, and takes as hypotheses the facts that tie the
verifier's arithmetic to the commitment, which are the link's arithmetization, not sum-check
soundness:

* `hidx`: when the pointers are one-hot, the index summand `idx θ_0 drawn` (the scattered arrays
  against the targets, as `Lookup.lean` and `StateLink.lean` define them) is a table of partial sums
  of degree `2` in each index variable, whose total is `indexClaim` plus the link's error `errB`;
* `hrow`: the row side's summand `row θ_0 drawn r fresh` is a table of partial sums of the row
  degrees, whose total is the index summand at `r` plus the fresh coefficients' terms (`B`);
* `htail`: with a final claim other than the row summand at the final point, no packed message makes
  the terminal check pass with an output satisfying `Win` (correct values give the summand);
* `hsplit`: the program's split is a function of the point (`computedSplit` and `freshSplit` are,
  `win_require_ret_bind`);
* `hA`, `hB`: the Schwartz-Zippel counts, which `LeanVM.Protocol.Link.Errors` proves from
  `Mirror.lean`, `StateLink.lean` and `Lookup.lean` for the errors written as those modules'
  polynomials.
-/

namespace LeanVM.Protocol.Link

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Finset
open scoped ENNReal

@[expose] public section

/-! ## Moves -/

theorem bind_eq_bind' {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) :
    (p >>= f) = p.bind f := rfl

theorem liftOption_some {α : Type} (a : α) : liftOption (some a) = .ret a := rfl

theorem ret_bind {α β : Type} (a : α) (f : α → VerifierProgram β) :
    (VerifierProgram.ret a).bind f = f a := rfl

/-- The program's split as `computedSplit` and `freshSplit` take it, a check and a value. -/
theorem win_require_ret_bind {α β : Type} (W : β → Prop) (c : Prop) [Decidable c] (s : α)
    (k : α → VerifierProgram β) :
    win W (((VerifierProgram.require c).bind fun _ ↦ VerifierProgram.ret s).bind k) ≤ win W (k s) := by
  rw [bind_assoc]
  exact win_require_bind W c _

/-- The deployed verifier's split is a function of the point. -/
theorem win_computedSplit_bind (W : LinkEnd → Prop) (bytecode : List K) (pt : List E)
    (pc : List (ℕ × ℕ)) (k : Split → VerifierProgram LinkEnd) :
    win W ((computedSplit bytecode pt pc).bind k) ≤ win W (k (splitAt bytecode pt pc)) :=
  win_require_ret_bind W _ _ k

/-- The deferring verifier's split is a function of the point too (`freshSplit`, a constant). -/
theorem win_freshSplit_bind (W : LinkEnd → Prop) (fresh : FreshClaim) (bytecode : List K)
    (pt : List E) (pc : List (ℕ × ℕ)) (k : Split → VerifierProgram LinkEnd) :
    win W ((freshSplit fresh bytecode pt pc).bind k) ≤
      win W (k (Split.ofColumns tables fresh.values)) :=
  win_require_ret_bind W _ _ k

/-! ## Averages -/

theorem avgL_congr {n : ℕ} {f g : List E → ℝ≥0∞} (h : ∀ l, l.length = n → f l = g l) :
    avgL n f = avgL n g :=
  le_antisymm (avgL_mono fun l hl ↦ (h l hl).le) (avgL_mono fun l hl ↦ (h l hl).ge)

theorem getD_ofFn {n : ℕ} (v : Fin n → E) (i : Fin n) : (List.ofFn v).getD i 0 = v i := by
  simp [List.getD_eq_getElem?_getD]

/-- **The fresh coefficients.** A claim `f` fixed before them equals the row side's true sum
`a + Σ_i fresh_i·b_i` at no more than `|E|^4` of the `|E|^5` fresh coefficients, when `f ≠ a` or the
first coefficient's weight is nonzero. -/
theorem card_fresh_le (f a : E) (b : Fin 5 → E) (h : a ≠ f ∨ b 0 ≠ 0) :
    (univ.filter fun v : Fin 5 → E ↦ f = a + ∑ i : Fin 5, (List.ofFn v).getD i 0 * b i).card ≤
      Fintype.card E ^ 4 := by
  classical
  have h' : a - f ≠ 0 ∨ ∃ i, b i ≠ 0 := by
    rcases h with h | h
    · exact Or.inl (sub_ne_zero.mpr h)
    · exact Or.inr ⟨0, h⟩
  refine le_of_eq_of_le (congrArg card (filter_congr fun v _ ↦ ?_)) (card_affine_le (a - f) b h')
  simp only [getD_ofFn]
  constructor <;> intro hv <;> linear_combination -hv

/-! ## The row side -/

/-- The row side's degree in each round: `count − 1` of the row rounds' and of the pointer-column
rounds' coefficient counts. -/
def rowDegrees (nR rc cc : ℕ) (i : ℕ) : ℕ := if i < nR then rc - 1 else cc - 1

theorem two_le_roundCoefficients (d : ℕ) :
    2 ≤ (roundCoefficients d).1 ∧ 2 ≤ (roundCoefficients d).2 := by
  simp only [roundCoefficients]
  omega

/-- **The row side.** From an index point `r` and a claim `f` that is the row side's true sum for at
most `|E|^4` of the fresh coefficients, the best prover reaches an output satisfying `Win` with
probability at most `(1 + m·(rc − 1) + m_Q·(cc − 1))/|E|`: the fresh coefficients, then the two
sum-checks, then the terminal check (`htail`). -/
theorem win_linkRowPhase_le
    (bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split) (layout : Layout)
    (Win : LinkEnd → Prop) (chunks : Chunks) (S : List E → Split)
    (hsplit : ∀ pt (k : Split → VerifierProgram LinkEnd),
      win Win ((bytecodeSplit layout.bytecode pt (pcSlots layout.tables)).bind k) ≤ win Win (k (S pt)))
    (theta0 : E) (drawn r : List E) (row : List E → List E → E)
    (hrow : ∀ fresh, RoundPolys (row fresh) (linkRows layout + linkQVars layout)
      (rowDegrees (linkRows layout) (roundCoefficients chunks.d).1 (roundCoefficients chunks.d).2))
    (htail : ∀ m1 fresh chi q c, c ≠ row fresh (chi ++ q) →
      win Win (linkTail layout chunks theta0 drawn r m1 fresh (S (r.take layout.logBytecode)) chi q c) = 0)
    (f : E) (hf : (univ.filter fun v : Fin 5 → E ↦ f = row (List.ofFn v) []).card ≤
      Fintype.card E ^ 4) :
    win Win (linkRowPhase bytecodeSplit layout chunks theta0 drawn r f) ≤
      ((1 + linkRows layout * ((roundCoefficients chunks.d).1 - 1) +
        linkQVars layout * ((roundCoefficients chunks.d).2 - 1) : ℕ) : ℝ≥0∞) / cardE := by
  classical
  obtain ⟨hrc, hcc⟩ := two_le_roundCoefficients chunks.d
  unfold linkRowPhase
  simp only [bind_eq_bind']
  rw [win_readScalar_bind]
  refine iSup_le fun m1 ↦ ?_
  rw [win_sampleChallengesPacked_bind]
  refine (avgL_le_bad (b := ((linkRows layout * ((roundCoefficients chunks.d).1 - 1) +
      linkQVars layout * ((roundCoefficients chunks.d).2 - 1) : ℕ) : ℝ≥0∞) / cardE)
    (fun fresh ↦ f = row fresh []) (fun _ ↦ win_le_one _ _) fun fresh _ hne ↦ ?_).trans ?_
  · refine (hsplit _ _).trans ?_
    refine (win_sumcheck_le_of_ne Win _ hrc (linkRows layout) _ (row fresh) f _
      (RoundPolys.take (m := linkQVars layout) (hrow fresh))
      (fun i hi ↦ by simp [rowDegrees, hi]) hne).trans ?_
    rw [Nat.cast_add, ENNReal.add_div]
    refine add_le_add le_rfl (avgL_le_of_le fun chi hchi ↦ iSup₂_le fun f' hf' ↦ ?_)
    refine (win_sumcheck_le_of_ne Win _ hcc (linkQVars layout) _ (fun p ↦ row fresh (chi ++ p)) f' _
      ((hrow fresh).drop chi hchi) (fun i _ ↦ by simp [rowDegrees]) (by simpa using hf')).trans ?_
    refine (add_le_add le_rfl (avgL_le_of_le (b := 0) fun q _ ↦
      iSup₂_le fun c hc ↦ (htail m1 fresh chi q c hc).le)).trans ?_
    rw [add_zero]
  · have hbad := avgL_le_card (n := 5) (D := 1) (by norm_num) (fun fresh ↦ f = row fresh [])
      (by simpa using hf)
    refine (add_le_add hbad le_rfl).trans ?_
    rw [← ENNReal.add_div, ← Nat.cast_add, add_assoc]

/-! ## The theorem -/

/-- **Soundness of `verify_link`'s sum-checks** (the paper's Theorem 5.4, revised, in leanVM's
form). For a commitment that fails the link (`¬ (OneHot ∧ LinksHold)`), the best prover's chance,
every challenge uniform, of a run of `verifyLink` returning an output that satisfies `Win` is at most
`(max(D_A, D_B + 2W) + 1 + m·(rc − 1) + m_Q·(cc − 1))/|E|`, where `W` is the pointer width, `m`
the tallest table's row variables, `m_Q` the pointer columns' variables, `rc − 1 = max(d + 2, 4)` and
`cc − 1 = max(d + 1, 3)` the row side's round degrees (`roundCoefficients`), `D_A` the one-hot
term's and `D_B` the link error's Schwartz-Zippel degree. The hypotheses are the arithmetization's
facts and the counts (the module's docstring). -/
theorem verifyLink_sound
    (bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split) (layout : Layout)
    (Win : LinkEnd → Prop) (chunks : Chunks) (hch : Chunks.new (linkWidth layout) = some chunks)
    (S : List E → Split)
    (hsplit : ∀ pt (k : Split → VerifierProgram LinkEnd),
      win Win ((bytecodeSplit layout.bytecode pt (pcSlots layout.tables)).bind k) ≤ win Win (k (S pt)))
    (OneHot LinksHold : Prop)
    (idx : E → List E → List E → E) (errB : E → List E → E)
    (row : E → List E → List E → List E → List E → E) (B : E → List E → List E → Fin 5 → E)
    (hidx : OneHot → ∀ theta0 drawn, RoundPolys (idx theta0 drawn) chunks.width (fun _ ↦ 2) ∧
      idx theta0 drawn [] = indexClaim layout chunks drawn + errB theta0 drawn)
    (hrow : ∀ theta0 drawn r fresh,
      RoundPolys (row theta0 drawn r fresh) (linkRows layout + linkQVars layout)
        (rowDegrees (linkRows layout) (roundCoefficients chunks.d).1 (roundCoefficients chunks.d).2) ∧
      row theta0 drawn r fresh [] = idx theta0 drawn r + ∑ i : Fin 5, fresh.getD i 0 * B theta0 drawn r i)
    (htail : ∀ theta0 drawn r m1 fresh chi q c, c ≠ row theta0 drawn r fresh (chi ++ q) →
      win Win (linkTail layout chunks theta0 drawn r m1 fresh (S (r.take layout.logBytecode)) chi q c) = 0)
    {DA DB : ℕ}
    (hA : ¬ OneHot →
      (univ.filter fun v : Fin (linkDrawn layout chunks + 1 + chunks.width) → E ↦
        B (((List.ofFn v).take (linkDrawn layout chunks + 1)).headD 0)
          ((List.ofFn v).take (linkDrawn layout chunks + 1)).tail
          ((List.ofFn v).drop (linkDrawn layout chunks + 1)) 0 = 0).card ≤
        DA * Fintype.card E ^ (linkDrawn layout chunks + chunks.width))
    (hB : OneHot → ¬ LinksHold →
      (univ.filter fun v : Fin (linkDrawn layout chunks + 1) → E ↦
        errB ((List.ofFn v).headD 0) (List.ofFn v).tail = 0).card ≤
        DB * Fintype.card E ^ linkDrawn layout chunks)
    (hfail : ¬ (OneHot ∧ LinksHold)) :
    win Win (verifyLink bytecodeSplit layout) ≤
      ((max DA (DB + 2 * chunks.width) + 1 + linkRows layout * ((roundCoefficients chunks.d).1 - 1) +
        linkQVars layout * ((roundCoefficients chunks.d).2 - 1) : ℕ) : ℝ≥0∞) / cardE := by
  classical
  -- The row side, from any index point and a claim off the fresh coefficients' bad set.
  have hphase : ∀ theta0 drawn r f, (idx theta0 drawn r ≠ f ∨ B theta0 drawn r 0 ≠ 0) →
      win Win (linkRowPhase bytecodeSplit layout chunks theta0 drawn r f) ≤
        ((1 + linkRows layout * ((roundCoefficients chunks.d).1 - 1) +
          linkQVars layout * ((roundCoefficients chunks.d).2 - 1) : ℕ) : ℝ≥0∞) / cardE := by
    intro theta0 drawn r f hne
    refine win_linkRowPhase_le bytecodeSplit layout Win chunks S hsplit theta0 drawn r
      (row theta0 drawn r) (fun fresh ↦ (hrow theta0 drawn r fresh).1) (htail theta0 drawn r) f ?_
    refine le_of_eq_of_le (congrArg card (filter_congr fun v _ ↦ ?_))
      (card_fresh_le f (idx theta0 drawn r) (B theta0 drawn r) hne)
    rw [(hrow theta0 drawn r (List.ofFn v)).2]
  -- The skeleton, to the index side's sum-check.
  rw [verifyLink_eq_linkSkeleton]
  unfold linkSkeleton
  simp only [bind_eq_bind', hch, liftOption_some, ret_bind]
  rw [win_grindProofOfWork_bind, win_sampleChallenge_bind]
  simp only [win_sampleChallengesPacked_bind]
  show (∑ theta0 : E, avgL (linkDrawn layout chunks) fun drawn ↦ win Win
    ((sumcheck (indexClaim layout chunks drawn) 3 (List.replicate chunks.width none)).bind
      fun x ↦ linkRowPhase bytecodeSplit layout chunks theta0 drawn x.1 x.2)) / cardE ≤ _
  refine le_of_eq_of_le (avgL_succ (linkDrawn layout chunks) fun l ↦ win Win
    ((sumcheck (indexClaim layout chunks l.tail) 3 (List.replicate chunks.width none)).bind
      fun x ↦ linkRowPhase bytecodeSplit layout chunks (l.headD 0) l.tail x.1 x.2)).symm ?_
  have hfinal : max DA (DB + 2 * chunks.width) + 1 + linkRows layout *
      ((roundCoefficients chunks.d).1 - 1) + linkQVars layout * ((roundCoefficients chunks.d).2 - 1) =
      max DA (DB + 2 * chunks.width) + (1 + linkRows layout * ((roundCoefficients chunks.d).1 - 1) +
        linkQVars layout * ((roundCoefficients chunks.d).2 - 1)) := by
    ring
  rw [hfinal]
  by_cases hOH : OneHot
  · -- (b) One-hot, and a link fails: the index side's claim is false off `hB`'s set.
    have hLH : ¬ LinksHold := fun h ↦ hfail ⟨hOH, h⟩
    refine (avgL_le_bad (b := ((2 * chunks.width : ℕ) : ℝ≥0∞) / cardE + ((1 + linkRows layout * ((roundCoefficients chunks.d).1 - 1) +
        linkQVars layout * ((roundCoefficients chunks.d).2 - 1) : ℕ) : ℝ≥0∞) / cardE)
      (fun l ↦ errB (l.headD 0) l.tail = 0) (fun _ ↦ win_le_one _ _) fun l _ hne ↦ ?_).trans ?_
    · obtain ⟨hg, hsum⟩ := hidx hOH (l.headD 0) l.tail
      have hclaim : indexClaim layout chunks l.tail ≠ idx (l.headD 0) l.tail [] := by
        rw [hsum]
        intro h
        exact hne (by linear_combination -h)
      refine (win_sumcheck_le_of_ne Win 3 (by norm_num) chunks.width (fun _ ↦ 2) _ _ _ hg
        (fun _ _ ↦ le_rfl) hclaim).trans ?_
      refine add_le_add (le_of_eq (by rw [mul_comm])) (avgL_le_of_le fun r _ ↦
        iSup₂_le fun f hf ↦ hphase _ _ _ _ (Or.inl (Ne.symm hf)))
    · have hbad := avgL_le_card (n := linkDrawn layout chunks + 1) (D := DB) (by omega)
        (fun l ↦ errB (l.headD 0) l.tail = 0) (by simpa using hB hOH hLH)
      refine (add_le_add hbad le_rfl).trans ?_
      rw [← ENNReal.add_div, ← ENNReal.add_div, ← Nat.cast_add, ← Nat.cast_add]
      refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
      have := le_max_right DA (DB + 2 * chunks.width)
      omega
  · -- (a) Not one-hot: the index side's challenges are uniform, the one-hot term nonzero off `hA`'s
    -- set.
    refine (avgL_mono fun l _ ↦ win_sumcheck_le Win 3 chunks.width _ _).trans ?_
    set N := linkDrawn layout chunks
    have hjoin : (avgL (N + 1) fun a ↦ avgL chunks.width fun r ↦ ⨆ f,
        win Win (linkRowPhase bytecodeSplit layout chunks (a.headD 0) a.tail r f)) =
        avgL (N + 1 + chunks.width) fun l ↦ ⨆ f, win Win (linkRowPhase bytecodeSplit layout chunks
          ((l.take (N + 1)).headD 0) (l.take (N + 1)).tail (l.drop (N + 1)) f) := by
      rw [avgL_append (N + 1) chunks.width]
      refine avgL_congr fun a ha ↦ avgL_congr fun r _ ↦ ?_
      simp only [List.take_left' ha, List.drop_left' ha]
    refine (le_of_eq hjoin).trans ?_
    refine (avgL_le_bad (b := ((1 + linkRows layout * ((roundCoefficients chunks.d).1 - 1) +
        linkQVars layout * ((roundCoefficients chunks.d).2 - 1) : ℕ) : ℝ≥0∞) / cardE)
      (fun l ↦ B ((l.take (N + 1)).headD 0) (l.take (N + 1)).tail (l.drop (N + 1)) 0 = 0)
      (fun _ ↦ iSup_le fun _ ↦ win_le_one _ _) fun l _ hne ↦
        iSup_le fun f ↦ hphase _ _ _ _ (Or.inr hne)).trans ?_
    have hbad := avgL_le_card (n := N + 1 + chunks.width) (D := DA) (by omega)
      (fun l ↦ B ((l.take (N + 1)).headD 0) (l.take (N + 1)).tail (l.drop (N + 1)) 0 = 0)
      (by rw [show N + 1 + chunks.width - 1 = N + chunks.width by omega]; exact hA hOH)
    refine (add_le_add hbad le_rfl).trans ?_
    rw [← ENNReal.add_div, ← Nat.cast_add]
    refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
    have := le_max_left DA (DB + 2 * chunks.width)
    omega

/-- **The deployed verifier's link** (`leanVmVerifierProgram` calls `verifyLink` with
`computedSplit`): `verifyLink_sound` with the split computed, `hsplit` discharged. -/
theorem verifyLink_sound_computedSplit (layout : Layout)
    (Win : LinkEnd → Prop) (chunks : Chunks) (hch : Chunks.new (linkWidth layout) = some chunks)
    (OneHot LinksHold : Prop)
    (idx : E → List E → List E → E) (errB : E → List E → E)
    (row : E → List E → List E → List E → List E → E) (B : E → List E → List E → Fin 5 → E)
    (hidx : OneHot → ∀ theta0 drawn, RoundPolys (idx theta0 drawn) chunks.width (fun _ ↦ 2) ∧
      idx theta0 drawn [] = indexClaim layout chunks drawn + errB theta0 drawn)
    (hrow : ∀ theta0 drawn r fresh,
      RoundPolys (row theta0 drawn r fresh) (linkRows layout + linkQVars layout)
        (rowDegrees (linkRows layout) (roundCoefficients chunks.d).1 (roundCoefficients chunks.d).2) ∧
      row theta0 drawn r fresh [] = idx theta0 drawn r + ∑ i : Fin 5, fresh.getD i 0 * B theta0 drawn r i)
    (htail : ∀ theta0 drawn r m1 fresh chi q c, c ≠ row theta0 drawn r fresh (chi ++ q) →
      win Win (linkTail layout chunks theta0 drawn r m1 fresh
        (splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)) chi q c) = 0)
    {DA DB : ℕ}
    (hA : ¬ OneHot →
      (univ.filter fun v : Fin (linkDrawn layout chunks + 1 + chunks.width) → E ↦
        B (((List.ofFn v).take (linkDrawn layout chunks + 1)).headD 0)
          ((List.ofFn v).take (linkDrawn layout chunks + 1)).tail
          ((List.ofFn v).drop (linkDrawn layout chunks + 1)) 0 = 0).card ≤
        DA * Fintype.card E ^ (linkDrawn layout chunks + chunks.width))
    (hB : OneHot → ¬ LinksHold →
      (univ.filter fun v : Fin (linkDrawn layout chunks + 1) → E ↦
        errB ((List.ofFn v).headD 0) (List.ofFn v).tail = 0).card ≤
        DB * Fintype.card E ^ linkDrawn layout chunks)
    (hfail : ¬ (OneHot ∧ LinksHold)) :
    win Win (verifyLink computedSplit layout) ≤
      ((max DA (DB + 2 * chunks.width) + 1 + linkRows layout * ((roundCoefficients chunks.d).1 - 1) +
        linkQVars layout * ((roundCoefficients chunks.d).2 - 1) : ℕ) : ℝ≥0∞) / cardE :=
  verifyLink_sound computedSplit layout Win chunks hch
    (fun pt ↦ splitAt layout.bytecode pt (pcSlots layout.tables))
    (fun pt k ↦ win_computedSplit_bind Win layout.bytecode pt _ k) OneHot LinksHold idx errB row B
    hidx hrow htail hA hB hfail

end

end LeanVM.Protocol.Link
