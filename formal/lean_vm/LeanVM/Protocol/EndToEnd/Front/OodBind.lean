/-
  LeanVM.Protocol.EndToEnd.Front.OodBind

  The commitment's out-of-domain sample binds it: after the grind and the point `z₀`, the stack
  word's candidates are separated at `z₀` except with probability `C(L, 2)·μ/|E|`, and then at
  most one of them answers the prover's `y₀`. The specification of `readOod`.
-/

module

public import LeanVM.Protocol.EndToEnd.Candidates
public import LeanVM.Protocol.EndToEnd.Front.LayoutArith
public import LeanVM.Protocol.ToArkLib.Whir.Ood
public import LeanVM.Protocol.Whir.Sound.Prob

/-!
# The commitment's OOD binding

`readOod μ` (`crates/verifier/src/lib.rs:158-165` at leanVM `f128`; Annex B, the Commit step) grinds
`oodGrindingBits = 15` bits, draws `z₀ ∈ E^μ`, reads `y₀` and returns the claim
`(eq(z₀, ·), y₀)` (`oodClaim`), which joins the stacked opening's claims last. Annex B: "The
commitment's list is `Lst(f^(0); a_0, d_0)`, of size at most `L_0`. Its members' multilinears are
pairwise distinct at `z_0` except with probability at most `C(L_0, 2)·ν/|E|` (Lemma `lem:sz`), which
`b_ood` grinds. Then at most one member answers the OOD claim, so the commitment is binding, and
every challenge drawn after it and before the opening faces a single candidate."

* `stackAt q z`: the stack's multilinear extension at `z`, what the OOD claim reads
  (`holds_oodClaim`); `stackAt_eq_evalMle`: CompPoly's `evalMle` of the stack's table in `E`.
* `OodSep S z`: distinct members of `S` have distinct extensions at `z`;
  `card_not_oodSep_le`: for a finite `S` of at most `L` stacks, at most `C(L, 2)·μ·|E|^(μ-1)` of the
  `|E|^μ` points are not separating (`card_ood_collision_image_le`, Schwartz-Zippel for
  multilinears), so `escRet_oodSep_le`: the group of the point escapes separation with probability
  at most `C(L, 2)·μ/|E|`.
* `oodCands S z y`: the member of `S` answering `y` at `z`, when it is the only one. At most one
  stack (`oodCands_ncard_le`) whatever `z` and `y`, so a phase specification charged per candidate
  is charged once; under separation it is every member answering `y`
  (`mem_oodCands_of_sep`), so a member outside it violates the OOD claim
  (`not_holds_of_not_mem`).
* `oodSpec`: the specification of `readOod μ` from any doom `D` on the commitments that carries a
  finite candidate set of at most `L` stacks, to `OodPost`: the returned claim is
  `oodClaim z₀ y₀`, `D` still holds, and the candidates are separated at `z₀`. Its one group, the
  point, is charged `C(L, 2)·μ/|E|`, discounted by the grind before it.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier VerifierProgram
open CompPoly CMlPolynomialEval
open scoped ENNReal

@[expose] public section

/-! ## The claim -/

/-- The claim of the commitment's OOD sample: weight `eq(z, ·)`, value `y` (`readOod`). -/
def oodClaim (z : List E) (y : E) : StackClaim := (fun x ↦ eqEval z x, y)

/-- `readOod` is the grind, the point, the answer and the claim. -/
theorem readOod_eq (μ : ℕ) :
    readOod μ = (grindProofOfWork Whir.oodGrindingBits).bind fun _ ↦
      (sampleChallenges μ).bind fun z ↦ readScalar.bind fun y ↦ ret (oodClaim z y) := rfl

variable {μ : ℕ}

/-- The stack's multilinear extension at `z`, with the verifier's `eq_eval`. -/
def stackAt (q : Column μ) (z : List E) : E :=
  ∑ x : Fin (2 ^ μ), eqEval z (boolPoint μ x) * ofK (q.values.getD x 0)

/-- **The OOD claim holds of a stack** exactly when its extension at `z` is `y`. -/
theorem holds_oodClaim (q : Column μ) (z : List E) (y : E) :
    StackClaim.Holds μ (oodClaim z y) q ↔ stackAt q z = y := Iff.rfl

/-- A stack's table in `E`. -/
def tableE (q : Column μ) : CMlPolynomialEval E μ := Vector.map ofK q.values

theorem tableE_injective : Function.Injective (tableE (μ := μ)) := by
  rintro ⟨a⟩ ⟨b⟩ h
  congr 1
  refine Vector.ext fun i hi ↦ ?_
  have := congrArg (·[i]) h
  simp only [tableE, Vector.getElem_map] at this
  exact ofK_injective this

/-- The extension at a point is CompPoly's `evalMle` of the table. -/
theorem stackAt_eq_evalMle (q : Column μ) (z : Vector E μ) :
    stackAt q z.toList = evalMle (tableE q) z := by
  rw [stackAt, LeanVM.Protocol.evalMle_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqEval_boolPoint, mul_comm]
  congr 1
  simp [tableE, Vector.getD, x.isLt]

/-! ## Separation -/

/-- Distinct members of `S` have distinct extensions at `z`. -/
def OodSep (S : Set (Column μ)) (z : List E) : Prop :=
  ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → stackAt q z ≠ stackAt q' z

/-- The member of `S` answering `y` at `z`, when it is the only one. -/
def oodCands (S : Set (Column μ)) (z : List E) (y : E) : Set (Column μ) :=
  {q | q ∈ S ∧ stackAt q z = y ∧ ∀ q' ∈ S, stackAt q' z = y → q' = q}

theorem oodCands_subset (S : Set (Column μ)) (z : List E) (y : E) : oodCands S z y ⊆ S :=
  fun _ hq ↦ hq.1

/-- **At most one candidate is left**, whatever the point and the answer. -/
theorem oodCands_ncard_le (S : Set (Column μ)) (z : List E) (y : E) :
    (oodCands S z y).ncard ≤ 1 := by
  have hsub : (oodCands S z y).Subsingleton := fun _ ha _ hb ↦ hb.2.2 _ ha.1 ha.2.1
  exact (Set.ncard_le_one hsub.finite).2 hsub

/-- Under separation, every member answering `y` is the one left. -/
theorem mem_oodCands_of_sep {S : Set (Column μ)} {z : List E} {y : E} (hs : OodSep S z)
    {q : Column μ} (hq : q ∈ S) (hy : stackAt q z = y) : q ∈ oodCands S z y := by
  refine ⟨hq, hy, fun q' hq' hy' ↦ ?_⟩
  by_contra hne
  exact hs q' hq' q hq hne (hy'.trans hy.symm)

/-- **Under separation, a member not left violates the OOD claim.** -/
theorem not_holds_of_not_mem {S : Set (Column μ)} {z : List E} {y : E} (hs : OodSep S z)
    {q : Column μ} (hq : q ∈ S) (hn : q ∉ oodCands S z y) :
    ¬ StackClaim.Holds μ (oodClaim z y) q :=
  fun h ↦ hn (mem_oodCands_of_sep hs hq h)

/-- Separation of a set gives separation of a subset. -/
theorem OodSep.mono {S S' : Set (Column μ)} {z : List E} (hs : OodSep S z) (h : S' ⊆ S) :
    OodSep S' z :=
  fun q hq q' hq' ↦ hs q (h hq) q' (h hq')

open Classical in
/-- **The non-separating points are few**: for a finite set of at most `L` stacks, at most
`C(L, 2)·μ·|E|^(μ-1)` of the points of `E^μ`. -/
theorem card_not_oodSep_le {S : Set (Column μ)} (hS : S.Finite) {L : ℕ} (hL : S.ncard ≤ L) :
    (Finset.univ.filter fun f : Fin μ → E ↦ ¬ OodSep S (List.ofFn f)).card ≤
      L.choose 2 * (μ * Fintype.card E ^ (μ - 1)) := by
  set T := hS.toFinset
  have hT : T.card ≤ L := by rw [← Set.ncard_eq_toFinset_card S hS]; exact hL
  have hc := Whir.card_ood_collision_image_le T tableE (tableE_injective.injOn)
  calc (Finset.univ.filter fun f : Fin μ → E ↦ ¬ OodSep S (List.ofFn f)).card
      = (Finset.univ.filter fun z : Vector E μ ↦
          ∃ U ∈ T, ∃ U' ∈ T, U ≠ U' ∧ evalMle (tableE U) z = evalMle (tableE U') z).card := by
        refine Finset.card_bij' (fun f _ ↦ Vector.ofFn f) (fun v _ ↦ fun j : Fin μ ↦ v[j.val])
          ?_ ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, OodSep, not_forall,
            not_not, exists_prop, T, Set.Finite.mem_toFinset] at hf ⊢
          obtain ⟨q, hq, q', hq', hne, heq⟩ := hf
          refine ⟨q, hq, q', hq', hne, ?_⟩
          rw [← stackAt_eq_evalMle, ← stackAt_eq_evalMle, Vector.toList_ofFn]
          exact heq
        · intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, OodSep, not_forall,
            not_not, exists_prop, T, Set.Finite.mem_toFinset] at hv ⊢
          obtain ⟨q, hq, q', hq', hne, heq⟩ := hv
          refine ⟨q, hq, q', hq', hne, ?_⟩
          have hv' : List.ofFn (fun j : Fin μ ↦ v[j.val]) = v.toList := by
            rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
          rw [hv', stackAt_eq_evalMle, stackAt_eq_evalMle]
          exact heq
        · intro f _; funext j; simp
        · intro v _; exact Vector.ofFn_getElem
    _ ≤ T.card.choose 2 * (μ * Fintype.card E ^ (μ - 1)) := hc
    _ ≤ L.choose 2 * (μ * Fintype.card E ^ (μ - 1)) :=
        Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hT)

/-! ## The group of the point -/

/-- Every node of the program is a sample, a return or a rejection. -/
private inductive SamplesOnly {α : Type} : VerifierProgram α → Prop where
  | ret (a : α) : SamplesOnly (VerifierProgram.ret a)
  | sample {k : E → VerifierProgram α} : (∀ c, SamplesOnly (k c)) →
      SamplesOnly (VerifierProgram.sample k)

private theorem SamplesOnly.after {α : Type} {p q : VerifierProgram α} (hp : SamplesOnly p) :
    ∀ {l : List Ev}, p.after l = some q → SamplesOnly q := by
  intro l
  induction l generalizing p with
  | nil => intro h; simp [VerifierProgram.after] at h; exact h ▸ hp
  | cons e l ih =>
    intro h
    cases hp with
    | ret a => cases e <;> simp [VerifierProgram.after] at h
    | sample hk =>
      cases e <;> simp [VerifierProgram.after] at h
      exact ih (hk _) h

private theorem SamplesOnly.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : SamplesOnly p) (hf : ∀ a, SamplesOnly (f a)) : SamplesOnly (p.bind f) := by
  induction hp with
  | ret a => exact hf a
  | sample _ ih => exact SamplesOnly.sample ih

private theorem samplesOnly_sampleN : ∀ n, SamplesOnly (sampleChallenges n)
  | 0 => SamplesOnly.ret []
  | n + 1 => (SamplesOnly.sample fun c ↦ SamplesOnly.ret c).bind fun _ ↦
      (samplesOnly_sampleN n).bind fun _ ↦ SamplesOnly.ret _

/-- The point's draw makes no prover move. -/
theorem sampleN_noMove (n : ℕ) {h₀ l : List Ev} {q : VerifierProgram (List E)}
    (_ : (sampleChallenges n).Reach h₀ l) (ha : (sampleChallenges n).after l = some q) :
    ¬ q.IsMove := by
  cases (samplesOnly_sampleN n).after ha <;> simp [VerifierProgram.IsMove]

/-- The OOD error, `C(L, 2)·μ/|E|`. -/
noncomputable def oodError (L μ : ℕ) : ℝ≥0∞ := ((L.choose 2 * μ : ℕ) : ℝ≥0∞) / Fintype.card E

open Classical in
/-- **The point's group**: for any predicate `J` of the point and the commitments that holds of
every separating point of length `μ ≥ 1`, the point escapes `J` with probability at most
`C(L, 2)·μ/|E|`. -/
theorem escRet_oodSep_le {S : Set (Column μ)} (hS : S.Finite) {L : ℕ} (hL : S.ncard ≤ L)
    (hμ : μ ≠ 0) (J : List E → List (ℕ × ℕ × Word) → Prop) (h₀ : List Ev)
    (hJ : ∀ z : List E, z.length = μ → OodSep S z → J z (commits h₀)) :
    escRet (fun z h ↦ J z (commits h)) h₀ [] (sampleChallenges μ) ≤ oodError L μ := by
  unfold escRet
  rw [Whir.Sound.retExp_commits (fun z cs ↦ if J z cs then 0 else 1), List.append_nil,
    Whir.Sound.retExp_sampleN]
  have hsum : ∑ f : Fin μ → E, (if J (List.ofFn f) (commits h₀) then 0 else 1 : ℝ≥0∞) ≤
      ((L.choose 2 * (μ * Fintype.card E ^ (μ - 1)) : ℕ) : ℝ≥0∞) := by
    calc ∑ f : Fin μ → E, (if J (List.ofFn f) (commits h₀) then 0 else 1 : ℝ≥0∞)
        ≤ ∑ f : Fin μ → E, (if OodSep S (List.ofFn f) then 0 else 1 : ℝ≥0∞) := by
          gcongr with f
          by_cases hs : OodSep S (List.ofFn f)
          · simp [hs, hJ _ (List.length_ofFn) hs]
          · split_ifs <;> simp
      _ = ((Finset.univ.filter fun f : Fin μ → E ↦ ¬ OodSep S (List.ofFn f)).card : ℝ≥0∞) := by
          rw [Finset.card_filter, Nat.cast_sum]
          exact Finset.sum_congr rfl fun f _ ↦ by
            by_cases h : OodSep S (List.ofFn f) <;> simp [h]
      _ ≤ _ := by exact_mod_cast card_not_oodSep_le hS hL
  obtain ⟨k, rfl⟩ : ∃ k, μ = k + 1 := ⟨μ - 1, by omega⟩
  have hE : (Fintype.card E : ℝ≥0∞) ≠ 0 := by simp
  have hT : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h1 : (Fintype.card E : ℝ≥0∞)⁻¹ ^ k * (Fintype.card E : ℝ≥0∞) ^ k = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel hE hT, one_pow]
  calc (Fintype.card E : ℝ≥0∞)⁻¹ ^ (k + 1) * ∑ f : Fin (k + 1) → E, _
      ≤ (Fintype.card E : ℝ≥0∞)⁻¹ ^ (k + 1) *
          ((L.choose 2 * ((k + 1) * Fintype.card E ^ (k + 1 - 1)) : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = oodError L (k + 1) := by
        rw [oodError, ENNReal.div_eq_inv_mul, Nat.add_sub_cancel]
        push_cast
        calc (Fintype.card E : ℝ≥0∞)⁻¹ ^ (k + 1) *
              ((L.choose 2 : ℝ≥0∞) * ((k + 1 : ℝ≥0∞) * (Fintype.card E : ℝ≥0∞) ^ k))
            = (Fintype.card E : ℝ≥0∞)⁻¹ * ((L.choose 2 : ℝ≥0∞) * (k + 1)) *
              ((Fintype.card E : ℝ≥0∞)⁻¹ ^ k * (Fintype.card E : ℝ≥0∞) ^ k) := by ring
          _ = _ := by rw [h1, mul_one]

/-! ## The specification of `readOod` -/

section Spec

variable (cands : List (ℕ × ℕ × Word) → Set (Column μ)) (D : List (ℕ × ℕ × Word) → Prop)

/-- After the point: the doom on the commitments, and the candidates separated at the point. -/
def OodPointPost (z : List E) (h : List Ev) : Prop :=
  z.length = μ ∧ D (commits h) ∧ OodSep (cands (commits h)) z

/-- **After `readOod`**: the returned claim is `oodClaim z y` at a point of `μ` coordinates
separating the candidates, and the doom on the commitments still holds. -/
def OodPost (claim : StackClaim) (h : List Ev) : Prop :=
  ∃ z y, claim = oodClaim z y ∧ OodPointPost cands D z h

private theorem commits_Spec.grindEvs (h : List Ev) (b : ℕ) : commits (h ++ Spec.grindEvs b) = commits h := by
  unfold Spec.grindEvs
  split_ifs <;> simp [commits_append, commits]

variable {εmax T : ℝ≥0∞}

/-- **The specification of the commitment's OOD sample.** From the doom `D` on the commitments,
under which the candidates are finite and at most `L`: the grind, then the point's group, charged
`C(L, 2)·μ/|E|` (`hε`, discounted by the grind), then the answer, ending in `OodPost`. Lead `0`;
the follower's lead `T` is carried at the answer's boundary. -/
noncomputable def oodSpec (hμ : μ ≠ 0) {L : ℕ}
    (hfin : ∀ cs, D cs → (cands cs).Finite) (hcard : ∀ cs, D cs → (cands cs).ncard ≤ L)
    (he : oodError L μ < 1)
    (hε : (2 : ℝ≥0∞)⁻¹ ^ Whir.oodGrindingBits * (oodError L μ + 0) ≤ εmax) (hT : T ≤ εmax) :
    Spec (readOod μ) (fun h ↦ D (commits h)) (OodPost cands D) εmax 0 T :=
  Spec.congr (readOod_eq μ).symm <|
    (Spec.grindPos (Post := fun _ h ↦ D (commits h)) (by decide)
      (fun h₀ hd ↦ by simpa [commits_append, commits] using hd) hε).bind fun _ ↦
    (Spec.ofNoMove (Post := fun z h ↦ OodPointPost cands D z h) (T := 0)
      (fun hl ha ↦ sampleN_noMove μ hl ha) he fun h₀ hd ↦
        escRet_oodSep_le (hfin _ hd) (hcard _ hd) hμ
          (fun z cs ↦ z.length = μ ∧ D cs ∧ OodSep (cands cs) z) h₀
          fun _ hz hs ↦ ⟨hz, hd, hs⟩).bind fun z ↦
    (Spec.readE (Post := fun y h ↦ OodPost cands D (oodClaim z y) h)
      (fun h₀ y hp ↦ ⟨z, y, rfl, by
        simpa only [OodPointPost, commits_append, commits, List.append_nil] using hp⟩) hT).bind
      fun y ↦ Spec.ret (Post := OodPost cands D) (oodClaim z y)

end Spec

end
end LeanVM.Protocol.EndToEnd.Front
