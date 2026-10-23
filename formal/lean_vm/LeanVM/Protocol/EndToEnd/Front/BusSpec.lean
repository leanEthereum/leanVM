/-
  LeanVM.Protocol.EndToEnd.Front.BusSpec

  Specifications of the verifier program's building blocks with doom on a relation: reading
  scalars, a sumcheck round in either mode, and a sequence of rounds, from the security of the
  oracle protocol's sumcheck components.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.EndToEnd.Front.BusDoom
public import LeanVM.Protocol.EndToEnd.Front.CommitDoom
public import LeanVM.Protocol.ToArkLib.SumcheckRound
public import LeanVM.Protocol.Spine.Instance
public import LeanVM.Protocol.Verifier

/-!
# Building blocks with doom on a relation

The doom of the front phases is `HDoom cands R x h`: the history's first commitment is a word
`W`, and no oracle of `cands W` puts the statement `x` in the relation `R` (`RelDoom`). It is
stable under later events (`HDoom.append`), so prover moves that leave the statement unchanged
keep it. This module specifies, in the calculus of `LeanVM.Protocol.Compile.Spec`:

* `readNSpec`: reading `n` scalars keeps any property stable under reads;
* `wireSumcheckSpec`: the verifier program's `sumcheck` (`verifier.py:405-426`), round by round,
  from doom on stage `j` of a sumcheck family to doom on its last stage, each challenge charged
  `L₀ · d / |E|`: the wire's round polynomial (the coefficient the claim fixes left out) is
  decoded into the protocol's message, which passes the protocol's check by construction.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## Doom on a relation, on histories -/

/-- **Doom on histories**: the history's first commitment is a word `W`, and no oracle of
`cands W` puts `x` in `R`. -/
def HDoom {S : Type} {ι : Type} {O : ι → Type} (cands : Word → Set (∀ i, O i))
    (R : Set ((S × ∀ i, O i) × Unit)) (x : S) (h : List Ev) : Prop :=
  ∃ W, firstWord h = some W ∧ RelDoom (cands W) R x

/-- Doom on histories survives later events. -/
theorem HDoom.append {S : Type} {ι : Type} {O : ι → Type} {cands : Word → Set (∀ i, O i)}
    {R : Set ((S × ∀ i, O i) × Unit)} {x : S} {h : List Ev} (hD : HDoom cands R x h)
    (l : List Ev) : HDoom cands R x (h ++ l) := by
  obtain ⟨W, hW, hR⟩ := hD
  exact ⟨W, firstWord_append hW l, hR⟩

variable {εmax T : ENNReal}

/-! ## Reading scalars -/

/-- **Reading `n` scalars** keeps a property of the history that reads keep, and returns `n`
values. Its lead is the follower's. -/
noncomputable def readNSpec (P : List Ev → Prop) (hP : ∀ h x, P h → P (h ++ [Ev.read x]))
    (hT : T ≤ εmax) : (n : ℕ) →
      Spec (Prog.readN n) P (fun xs h ↦ xs.length = n ∧ P h) εmax T T
  | 0 => (Spec.ret (Post := fun xs h ↦ xs.length = 0 ∧ P h) []).mono
      (fun _ h ↦ ⟨rfl, h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1 =>
    ((Spec.readE (Post := fun _ h ↦ P h) (fun h₀ x hp ↦ hP h₀ x hp) hT).bind' fun x ↦
      (readNSpec P hP hT n).bind' fun xs ↦
        (Spec.ret (Post := fun xs h ↦ xs.length = n + 1 ∧ P h) (x :: xs)).mono
          (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
        (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-- **Reading `n + 1` scalars** ends the current group of challenges: its lead is `0`. -/
noncomputable def readNSuccSpec (P : List Ev → Prop) (hP : ∀ h x, P h → P (h ++ [Ev.read x]))
    (hT : T ≤ εmax) (n : ℕ) :
    Spec (Prog.readN (n + 1)) P (fun xs h ↦ xs.length = n + 1 ∧ P h) εmax 0 T :=
  (Spec.readE (Post := fun _ h ↦ P h) (fun h₀ x hp ↦ hP h₀ x hp) hT).bind' fun x ↦
    (readNSpec P hP hT n).bind' fun xs ↦
      (Spec.ret (Post := fun xs h ↦ xs.length = n + 1 ∧ P h) (x :: xs)).mono
        (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## A sumcheck round of the protocol, on doom -/

section Round

variable {I : M3Instance} {X : Type} {d : ℕ}
  (Φ : SumcheckRound.Family E X (TheOracle I) Unit d) (j : ℕ)

/-- **The round's message keeps doom**: the message is recorded, whatever it is. -/
theorem sendPoly_keep {C : Set (∀ i, TheOracle I i)} {s : SumcheckRound.Stmt X E j}
    (hpre : RelDoom C (SumcheckRound.rel Φ j) s) (q : SumcheckRound.Message E d) :
    RelDoom C (SumcheckRound.relMid Φ j) (s, q) :=
  say_keep (SumcheckRound.sendPolySecurity j Φ) hpre q rfl

open Classical in
/-- **The round's challenge escapes doom** with probability at most `L₀ · d / |E|`, when the
recorded polynomial passes the check. -/
theorem drawChallenge_escape {m : ℕ} (H : Φ.Consistent m) (S : Φ.Sound m) (hj : j < m)
    {C : Set (∀ i, TheOracle I i)} (hfin : C.Finite) {L₀ : ℕ} (hcard : C.ncard ≤ L₀)
    {p : SumcheckRound.MidStmt X E j d} (hpre : RelDoom C (SumcheckRound.relMid Φ j) p)
    (hchk : SumcheckRound.check j Φ.weight p.1 p.2 = true) :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c ↦ ¬ RelDoom C
        (SumcheckRound.rel Φ (j + 1)) (SumcheckRound.next j p.1
          (SumcheckRound.evaluate d p.2 c) c)).card : ℝ≥0∞) ≤
      L₀ * (((d : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞) :=
  draw_escape_le (SumcheckRound.drawChallengeSecurity j Φ H S hj) hfin hcard hpre hchk

end Round

/-! ## Wire messages -/

/-- The weighted domain of a wire round: the plain round's unit weights on `0, 1`, or the
weights `1 - r, r` against the equality factor `r`. -/
def wireDomain : Option E → SumcheckRound.WeightedDomain E
  | none => [(0, 1), (1, 1)]
  | some r => [(0, 1 - r), (1, r)]

/-- A wire round polynomial read as the protocol's message: its first `d + 1` coefficients. -/
def toMessage (d : ℕ) (msg : List E) : SumcheckRound.Message E d :=
  Vector.ofFn fun i ↦ msg.getD i 0

/-- `E.sum` is the list's sum. -/
theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  unfold sumE
  rw [List.sum_eq_foldl]

/-- Horner's rule is the sum of the coefficients against the powers. -/
theorem polyEval_eq_sum_range (l : List E) (x : E) :
    polyEval l x = ∑ i ∈ Finset.range l.length, l.getD i 0 * x ^ i := by
  induction l with
  | nil => simp [polyEval]
  | cons a l ih =>
    show polyEval l x * x + a = _
    rw [ih, List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ, mul_assoc]

/-- A wire message of `d + 1` coefficients evaluates as the protocol's message. -/
theorem evaluate_toMessage {d : ℕ} (msg : List E) (hlen : msg.length = d + 1) (x : E) :
    SumcheckRound.evaluate d (toMessage d msg) x = polyEval msg x := by
  rw [polyEval_eq_sum_range, hlen, SumcheckRound.evaluate, ← Fin.sum_univ_eq_sum_range]
  simp [toMessage]

/-- Horner at `0` is the constant coefficient. -/
theorem polyEval_zero (a : E) (l : List E) : polyEval (a :: l) 0 = a := by
  show polyEval l 0 * 0 + a = a
  rw [mul_zero, zero_add]

/-- Horner at `1` is the sum of the coefficients. -/
theorem polyEval_one (l : List E) : polyEval l 1 = l.sum := by
  rw [polyEval_eq_sum_range]
  simp only [one_pow, mul_one]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ← ih]
    simp [add_comm]

/-- **The plain wire round passes the protocol's check**: the coefficient `c₁ = claim + Σ_{k≥2}
c_k` makes `q(0) + q(1)` the claim. -/
theorem weightedSum_plain {d : ℕ} (claim c₀ : E) (tail : List E) (hlen : tail.length + 2 = d + 1) :
    SumcheckRound.weightedSum d (wireDomain none)
      (toMessage d (c₀ :: (claim + sumE tail) :: tail)) = claim := by
  have hl : (c₀ :: (claim + sumE tail) :: tail).length = d + 1 := by simp; omega
  simp only [SumcheckRound.weightedSum, wireDomain, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, one_mul]
  rw [evaluate_toMessage _ hl, evaluate_toMessage _ hl, polyEval_zero, polyEval_one]
  simp only [List.sum_cons, sumE_eq_sum]
  linear_combination (CharTwo.add_self_eq_zero c₀) + CharTwo.add_self_eq_zero tail.sum

/-- **The equality-mode wire round passes the protocol's check**: the coefficient
`c₀ = claim + r · Σ_{k≥1} c_k` makes `(1 - r) q(0) + r q(1)` the claim. -/
theorem weightedSum_eq {d : ℕ} (claim r : E) (tail : List E) (hlen : tail.length + 1 = d + 1) :
    SumcheckRound.weightedSum d (wireDomain (some r))
      (toMessage d ((claim + r * sumE tail) :: tail)) = claim := by
  have hl : ((claim + r * sumE tail) :: tail).length = d + 1 := by simp; omega
  simp only [SumcheckRound.weightedSum, wireDomain, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [evaluate_toMessage _ hl, evaluate_toMessage _ hl, polyEval_zero, polyEval_one]
  simp only [List.sum_cons, sumE_eq_sum]
  linear_combination r * CharTwo.add_self_eq_zero tail.sum

/-! ## The wire's round polynomial -/

section Sumcheck

variable {I : M3Instance} {X : Type} {d : ℕ} (Φ : SumcheckRound.Family E X (TheOracle I) Unit d)
  (cands : Word → Set (∀ i, TheOracle I i))

/-- The vector of `m` coordinates a list gives, `0` past its end. -/
def vecOf (m : ℕ) (l : List E) : Vector E m := Vector.ofFn fun i ↦ l.getD i 0

/-- What a round's wire polynomial gives: `d + 1` coefficients that pass the protocol's check at
the running claim, and doom after the protocol's message. -/
def RoundPolyPost (j : ℕ) (s : SumcheckRound.Stmt X E j) (eq : Option E) (msg : List E)
    (h : List Ev) : Prop :=
  msg.length = d + 1 ∧ SumcheckRound.weightedSum d (wireDomain eq) (toMessage d msg) = s.2.2 ∧
    HDoom cands (SumcheckRound.relMid Φ j) (s, toMessage d msg) h

/-- Doom on the relation is kept by reads. -/
theorem hdoom_read {S : Type} {R : Set ((S × ∀ i, TheOracle I i) × Unit)} {y : S} (h : List Ev)
    (x : E) (hD : HDoom cands R y h) : HDoom cands R y (h ++ [Ev.read x]) :=
  hD.append _

/-- The message's doom from the stage's. -/
theorem hdoom_relMid {j : ℕ} {s : SumcheckRound.Stmt X E j} {h : List Ev}
    (hD : HDoom cands (SumcheckRound.rel Φ j) s h) (q : SumcheckRound.Message E d) :
    HDoom cands (SumcheckRound.relMid Φ j) (s, q) h := by
  obtain ⟨W, hW, hR⟩ := hD
  exact ⟨W, hW, sendPoly_keep Φ j hR q⟩

variable {εmax T : ENNReal}

/-- **The wire's round polynomial** (`Transcript.sumcheck_round_poly`, `verifier.py:405-412`):
reading it keeps doom, and it returns the protocol's message, which passes the check and is
doomed. It ends the group of challenges before it: its lead is `0`. -/
noncomputable def wireRoundPolySpec (hd : 1 ≤ d) (j : ℕ) (s : SumcheckRound.Stmt X E j)
    (eq : Option E) (hT : T ≤ εmax) :
    Spec (sumcheckRoundPoly (d + 1) s.2.2 eq) (HDoom cands (SumcheckRound.rel Φ j) s)
      (RoundPolyPost Φ cands j s eq) εmax 0 T :=
  match eq with
  | none =>
    (Spec.readE (Post := fun _ h ↦ HDoom cands (SumcheckRound.rel Φ j) s h)
      (fun h₀ x hp ↦ hdoom_read cands h₀ x hp) hT).bind' fun c ↦
      (readNSpec (HDoom cands (SumcheckRound.rel Φ j) s) (hdoom_read cands) hT
        (d + 1 - 2)).bind' fun tail ↦
        (Spec.ret (Post := RoundPolyPost Φ cands j s none)
          (c :: (s.2.2 + sumE tail) :: tail)).mono
          (fun h hp ↦ ⟨by simp [hp.1]; omega, weightedSum_plain _ _ _ (by rw [hp.1]; omega),
            hdoom_relMid Φ cands hp.2 _⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | some r =>
    Spec.congr (show (do
        let tail ← Prog.readN (d - 1 + 1)
        return (s.2.2 + r * sumE tail) :: tail : Prog (List E)) =
          sumcheckRoundPoly (d + 1) s.2.2 (some r) by
        show _ = (do
          let tail ← Prog.readN (d + 1 - 1)
          return (s.2.2 + r * sumE tail) :: tail)
        rw [show d - 1 + 1 = d + 1 - 1 by omega])
      ((readNSuccSpec (HDoom cands (SumcheckRound.rel Φ j) s) (hdoom_read cands) hT
        (d - 1)).bind' fun tail ↦
        (Spec.ret (Post := RoundPolyPost Φ cands j s (some r))
          ((s.2.2 + r * sumE tail) :: tail)).mono
          (fun h hp ↦ ⟨by simp [hp.1]; omega, weightedSum_eq _ _ _ (by rw [hp.1]; omega),
            hdoom_relMid Φ cands hp.2 _⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)

/-- The error of a round's challenge over at most `L₀` candidates: `L₀ · d / |E|`. -/
noncomputable def roundError (L₀ d : ℕ) : ℝ≥0∞ :=
  L₀ * (((d : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)

open Classical in
/-- **A round's challenge**, from a doomed message that passes the check, escapes doom on the next
stage with probability at most `L₀ · d / |E|`. -/
noncomputable def roundChallengeSpec {m : ℕ} (H : Φ.Consistent m) (S : Φ.Sound m) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) (j : ℕ) (hj : j < m)
    (s : SumcheckRound.Stmt X E j) (eq : Option E) (hw : Φ.weight s.1 j = wireDomain eq)
    (msg : List E) :
    Spec Prog.sampleE (RoundPolyPost Φ cands j s eq msg)
      (fun c h ↦ HDoom cands (SumcheckRound.rel Φ (j + 1)) (s.1, (s.2.1.push c, polyEval msg c)) h)
      εmax (roundError L₀ d + T) T :=
  Spec.sampleE (roundError L₀ d) fun h₀ hpre ↦ by
    obtain ⟨hlen, hcheck, W, hW, hR⟩ := hpre
    refine le_trans ?_ (drawChallenge_escape Φ j H S hj (hfin W) (hcard W) hR
      (by rw [SumcheckRound.check, hw, hcheck]; exact decide_eq_true rfl))
    gcongr with c _
    intro hR'
    refine ⟨W, firstWord_append hW _, ?_⟩
    have he := evaluate_toMessage msg hlen c
    simp only [SumcheckRound.next, he] at hR'
    exact hR'

/-- The lead of the wire's sumcheck: the follower's with no round, `0` otherwise (it starts with a
read). -/
def sumcheckLead : List (Option E) → ℝ≥0∞ → ℝ≥0∞
  | [], T => T
  | _ :: _, _ => 0

theorem sumcheckLead_le (eqs : List (Option E)) (T : ℝ≥0∞) : sumcheckLead eqs T ≤ T := by
  cases eqs <;> simp [sumcheckLead]

/-- A vector is the vector of its list. -/
theorem vecOf_toList {m : ℕ} (v : Vector E m) : vecOf m v.toList = v := by
  apply Vector.ext
  intro i hi
  simp [vecOf]

/-- What the wire's sumcheck gives from stage `j`: doom on its last stage `m`, at the point the
challenges complete and the final claim. -/
def SumcheckPost (x : X) (m : ℕ) {j : ℕ} (cv : Vector E j) (r : List E × E) (h : List Ev) :
    Prop :=
  j + r.1.length = m ∧ HDoom cands (SumcheckRound.rel Φ m) (x, (vecOf m (cv.toList ++ r.1), r.2)) h

/-- **The wire's sumcheck** (`sumcheck`, `verifier.py:419-426`) from stage `j`, the rounds' modes
given by `eqs`: from doom on stage `j` at the challenges `cv` so far and the running claim, to doom
on the last stage `m`; each challenge charged `L₀ · d / |E|`, every group of challenges being one
challenge followed by a read. -/
noncomputable def wireSumcheckSpec {m : ℕ} (H : Φ.Consistent m) (S : Φ.Sound m) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) (hd : 1 ≤ d)
    (he : roundError L₀ d + T ≤ εmax) (x : X) :
    (eqs : List (Option E)) → (j : ℕ) → (cv : Vector E j) → (claim : E) →
      j + eqs.length = m → (∀ k (hk : k < eqs.length), Φ.weight x (j + k) = wireDomain eqs[k]) →
      Spec (sumcheck claim (d + 1) eqs) (HDoom cands (SumcheckRound.rel Φ j) (x, (cv, claim)))
        (SumcheckPost Φ cands x m cv) εmax (sumcheckLead eqs T) T
  | [], j, cv, claim, hj, _ =>
    (Spec.ret (Post := SumcheckPost Φ cands x m cv) ([], claim)).mono (fun h hp ↦ by
      obtain rfl : m = j := by simpa using hj.symm
      exact ⟨rfl, by simpa [vecOf_toList] using hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | eq :: eqs, j, cv, claim, hj, hw =>
    (wireRoundPolySpec (T := roundError L₀ d + sumcheckLead eqs T) Φ cands hd j (x, (cv, claim)) eq
      (le_trans (add_le_add_right (sumcheckLead_le eqs T) _) he)).bind' fun msg ↦
      (roundChallengeSpec Φ cands H S hfin hcard j (by simp at hj; omega) (x, (cv, claim)) eq
        (hw 0 (by simp)) msg).bind' fun c ↦
        (wireSumcheckSpec H S hfin hcard hd he x eqs (j + 1) (cv.push c) (polyEval msg c)
          (by simp at hj; omega)
          (fun k hk ↦ by
            have h := hw (k + 1) (by simp; omega)
            rwa [show j + (k + 1) = j + 1 + k by omega] at h)).bind'
          fun ⟨pt, fin⟩ ↦ (Spec.ret (Post := SumcheckPost Φ cands x m cv) (c :: pt, fin)).mono
            (fun h hp ↦ ⟨by have := hp.1; dsimp only at this ⊢; simp only [List.length_cons]; omega,
              by simpa [Vector.toList_push] using hp.2⟩)
            (fun _ _ h ↦ h)
            le_rfl le_rfl le_rfl

end Sumcheck

end
end LeanVM.Protocol.EndToEnd.Front
