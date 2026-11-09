/-
# Explicit code-binding bound

The composed corollary: code-binding of the scheme, bounded explicitly in
terms of the primitive assumptions. `scheme_codeBinding` bounds the
code-binding probability by knowledge soundness + the non-interactive
committed soundness game + weak position-binding; the forking bound
(`niCommittedSoundness_forking_bound`, applied to the committed-soundness
reduction, which makes at most `Q + 1` oracle queries) bounds the middle term
implicitly by a quadratic inequality. Solving that inequality yields, in
square-free `ℝ≥0∞` form:

`(Pr[code-binding] − (ε_ks + ε_wpb))² ≤ (Q + 2) · (ε_coll + δ + |L|⁻¹)`.

Informally: `Pr[code-binding] ≤ ε_ks + ε_wpb + √((Q + 2)(ε_coll + δ + |L|⁻¹))`,
the square-root loss being inherent to the rewinding argument. A second
variant replaces the weak position-binding and commit-collision terms by
position-binding of the vector commitment (via the reductions of
`Assumptions/VectorCommitment.lean`), so that every term on the right refers
to a primitive assumption: knowledge soundness of the argument system,
position-binding of the vector commitment, and `δ`-soundness of the code
checker.

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified for VCVio afa6593.
-/
module

public import PqDas.Proof.CodeBinding
public import PqDas.Proof.CommittedSoundness.ForkingBound

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

open CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

section corollary

variable [Nonempty Γ] [Fintype Γ] [DecidableEq Λ] [DecidableEq ComVC]
  [SampleableType L] [Fintype L] [Inhabited L] [DecidableEq L]
  [NeZero n] [Inhabited Opn] [Inhabited Λ]

omit [Nonempty Γ] [Fintype Γ] [DecidableEq Λ] [DecidableEq ComVC] [SampleableType L]
  [Fintype L] [Inhabited L] [DecidableEq L] [NeZero n] [Inhabited Opn] [Inhabited Λ] in
/-- A lifted plain probabilistic computation makes no random-oracle queries. -/
private lemma hashQueryBound_liftM {α : Type} (oa : ProbComp α) (m : ℕ) :
    HashQueryBound (ComVC := ComVC) (L := L)
      (liftM oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) m := by
  induction oa using OracleComp.inductionOn generalizing m with
  | pure x => exact trivial
  | query_bind t mx ih =>
      rw [show (liftM (liftM (unifSpec.query t) >>= mx) :
          OracleComp (unifSpec + (ComVC →ₒ L)) _) =
        liftM ((unifSpec + (ComVC →ₒ L)).query (Sum.inl t)) >>=
          fun u => liftM (mx u) from by simp [monad_norm]; rfl]
      rw [hashQueryBound_query_bind_iff]
      exact ⟨trivial, fun u => ih u m⟩

omit [Nonempty Γ] [Fintype Γ] [DecidableEq Λ] [Fintype L] [Inhabited L]
  [DecidableEq L] [NeZero n] [Inhabited Opn] [Inhabited Λ] in
/-- The committed-soundness reduction of a `Q`-query code-binding adversary
makes at most `Q + 1` random-oracle queries (the `+ 1` for its own challenge
query). -/
private lemma csReduction_hashQueryBound
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    {A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn} {Q : ℕ}
    (hA : ∀ ck, HashQueryBound (A ck) Q) (ckVC : CkVC) :
    HashQueryBound (csReduction ps ext A ckVC) (Q + 1) := by
  unfold csReduction
  rw [show (Q + 1 : ℕ) = 0 + (Q + 1) from (Nat.zero_add _).symm]
  refine OracleComp.isQueryBoundP_bind (hashQueryBound_liftM ps.setup 0) fun crs _ => ?_
  refine OracleComp.isQueryBoundP_bind (hA (ckVC, crs)) fun out _ => ?_
  obtain ⟨com, rest⟩ := out
  show HashQueryBound
    ((liftM ((unifSpec + (ComVC →ₒ L)).query (Sum.inr com.1)) :
        OracleComp (unifSpec + (ComVC →ₒ L)) _) >>= fun l =>
      (pure (com.1, ext crs (ckVC, com.1, l) com.2) :
        OracleComp (unifSpec + (ComVC →ₒ L)) (ComVC × (Fin n → Λ)))) (0 + 1)
  rw [hashQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun u => by simp [HashQueryBound]⟩

/-- Solving the forking inequality: if `x·(x/q − c) ≤ B` for a probability
`x ≤ 1` and finite positive `q`, then `x² ≤ q·(B + c)`. -/
private lemma sq_le_of_forking {x q c B : ℝ≥0∞} (hx : x ≤ 1) (hq0 : q ≠ 0)
    (hqt : q ≠ ∞) (h : x * (x / q - c) ≤ B) : x ^ 2 ≤ q * (B + c) := by
  have h1 : x * (x / q) ≤ x * (x / q - c) + x * c := by
    rw [← mul_add]
    gcongr
    exact le_tsub_add
  have h2 : x * (x / q) ≤ B + c := by
    refine h1.trans (add_le_add h ?_)
    calc x * c ≤ 1 * c := by gcongr
    _ = c := one_mul c
  have h3 : x ^ 2 / q ≤ B + c := by
    rw [sq, mul_div_assoc]
    exact h2
  rw [ENNReal.div_le_iff hq0 hqt] at h3
  exact h3.trans_eq (mul_comm _ q)

/-- **Explicit code-binding bound** (squared form). For a code-binding
adversary making at most `Q` random-oracle queries, with a `δ`-sound code
checker:

`(Pr[code-binding] − (ε_ks + ε_wpb))² ≤ (Q + 2) · (ε_coll + δ + |L|⁻¹)`

where `ε_ks`, `ε_wpb`, `ε_coll` are the success probabilities of the explicit
reductions against knowledge soundness of the argument system, weak
position-binding of the vector commitment, and collision resistance of its
deterministic commit. -/
theorem scheme_codeBinding_concrete {δ : ℝ≥0∞}
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) {Q : ℕ}
    (hSound : chk.Sound C δ) (hA : ∀ ck, HashQueryBound (A ck) Q) :
    ((scheme (m := OracleComp (unifSpec + (ComVC →ₒ L)))
          C vc chk ps).codeBindingExp C (roRuntime ComVC L) A {true} -
        (Pr{let x ← ps.knowledgeSoundnessExp ext (ksReduction vc A)}[x = true] +
          Pr{let x ← vc.weakPosBindingExp (wpbReduction ps ext A)}[x = true])) ^ 2 ≤
      ((Q : ℝ≥0∞) + 2) *
        (Pr{let x ← (vc.collisionExp
            (forkCollisionReduction C vc chk (csReduction ps ext A) (Q + 1)))}[x = true] +
          δ + (Fintype.card L : ℝ≥0∞)⁻¹) := by
  set εcb := (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L)))
      C vc chk ps).codeBindingExp C (roRuntime ComVC L) A {true}
  set εks := Pr{let x ← ps.knowledgeSoundnessExp ext (ksReduction vc A)}[x = true]
  set εwpb := Pr{let x ← vc.weakPosBindingExp (wpbReduction ps ext A)}[x = true]
  set acc := niCommittedSoundnessExp C vc chk (csReduction ps ext A) {true}
  set εcoll := Pr{let x ← (vc.collisionExp
      (forkCollisionReduction C vc chk (csReduction ps ext A) (Q + 1)))}[x = true]
  have hchain : εcb - (εks + εwpb) ≤ acc := by
    rw [tsub_le_iff_right]
    calc εcb ≤ εks + acc + εwpb := scheme_codeBinding C vc chk ps ext A
    _ = acc + (εks + εwpb) := by ring
  have hfork := niCommittedSoundness_forking_bound
    (C := C) (vc := vc) (chk := chk) (A := csReduction ps ext A) (Q := Q + 1)
    hSound (csReduction_hashQueryBound ps ext hA)
  have hsq : acc ^ 2 ≤ ((Q : ℝ≥0∞) + 2) * (εcoll + δ + (Fintype.card L : ℝ≥0∞)⁻¹) := by
    have hcast : ((Q + 1 : ℕ) : ℝ≥0∞) + 1 = (Q : ℝ≥0∞) + 2 := by push_cast; ring
    rw [hcast] at hfork
    simpa [add_assoc] using sq_le_of_forking (niCommittedSoundnessExp_le_one _ _ _ _ _)
      (by simp) (by finiteness) hfork
  calc (εcb - (εks + εwpb)) ^ 2 ≤ acc ^ 2 := pow_le_pow_left' hchain 2
  _ ≤ _ := hsq

/-- **Explicit code-binding bound, from primitive assumptions only**: as
`scheme_codeBinding_concrete`, but with the weak position-binding and
commit-collision terms replaced by position-binding of the vector commitment
(via the explicit reductions of `Assumptions/VectorCommitment.lean`), assuming
perfect completeness of the vector commitment. -/
theorem scheme_codeBinding_concrete_posBinding {δ : ℝ≥0∞}
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) {Q : ℕ}
    (hvc : vc.PerfectlyComplete) (hSound : chk.Sound C δ)
    (hA : ∀ ck, HashQueryBound (A ck) Q) :
    ((scheme (m := OracleComp (unifSpec + (ComVC →ₒ L)))
          C vc chk ps).codeBindingExp C (roRuntime ComVC L) A {true} -
        (Pr{let x ← ps.knowledgeSoundnessExp ext (ksReduction vc A)}[x = true] +
          Pr{let x ← (vc.posBindingExp
            ((wpbReduction ps ext A).toPosBindingAdv vc))}[x = true])) ^ 2 ≤
      ((Q : ℝ≥0∞) + 2) *
        (Pr{let x ← (vc.posBindingExp
            ((forkCollisionReduction C vc chk (csReduction ps ext A)
              (Q + 1)).toPosBindingAdv vc))}[x = true] +
          δ + (Fintype.card L : ℝ≥0∞)⁻¹) := by
  have h1 := scheme_codeBinding_concrete C vc chk ps ext A hSound hA
  have hw := VectorCommitment.weakPosBindingExp_le_posBindingExp vc hvc
    (wpbReduction ps ext A)
  have hc := VectorCommitment.collisionExp_le_posBindingExp vc hvc
    (forkCollisionReduction C vc chk (csReduction ps ext A) (Q + 1))
  refine le_trans (le_trans ?_ h1) ?_
  · gcongr
  · gcongr

end corollary

end PqDas
