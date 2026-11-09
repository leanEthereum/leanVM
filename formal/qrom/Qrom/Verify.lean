module

public import Qrom.ProtHit
public import VCVio.Quantum.Oracle.Classical

@[expose] public section

/-!
# A classical verifier after the adversary

A game ends by checking the adversary's result with a classical algorithm on the hash, run as
classical queries (`Qrom.OvGame.withVerifier`). In the game with the function `G`, the hash read in
side state `s` is `g.answer s G`, and side ports are not called during the check, so on each side
state the check returns what the classical algorithm returns against that function: an event of the
result and the check is the event of the adversary's result with the check computed classically on
each side state (`Qrom.OvGame.sideW_withVerifier`). A classical query keeps an entry of the side
register when both of its side states read the reported value (`Qrom.OvGame.hashQuery_single`).
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]

/-- A classical hash query beside the trivial register. -/
noncomputable def hashQuery (t : X) :
    QComp (ovSpec X Y S P Res) (QReg.of Unit) (QReg.of Unit) Y :=
  QComp.callBasis (spec := ovSpec X Y S P Res) (Sum.inl ()) (QReg.of Unit) (t, (0 : Y))
    (fun o _ ↦ o.2)

section single

variable {A B ι : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem submatrix_single (e : A ≃ B) (a a' : A) :
    (Matrix.single a a' (1 : ℂ)).submatrix e.symm e.symm = Matrix.single (e a) (e a') 1 := by
  ext b b'
  simp only [submatrix_apply, Matrix.single_apply]
  congr 1
  apply propext
  constructor <;> rintro ⟨rfl, rfl⟩ <;> simp

theorem relabel_single (e : A ≃ B) (a a' : A) :
    (SubInstrument.relabel e).branch () (Matrix.single a a' 1) = Matrix.single (e a) (e a') 1 := by
  rw [SubInstrument.relabel_branch_apply, submatrix_single]

theorem frame_single {R : Type} [Fintype R] [DecidableEq R] {C : ι → Type} [∀ i, Fintype (C i)]
    (p : DSubInstrument A ι C) (i : ι) (a a' : A) (r r' : R) :
    (p.frame R).branch i (Matrix.single (a, r) (a', r') 1) =
      p.branch i (Matrix.single a a' 1) ⊗ₖ Matrix.single r r' 1 := by
  rw [DSubInstrument.branch_frame_apply, ← MatrixMap.amplify_kronecker,
    Matrix.single_kronecker_single, one_mul]

theorem conj_single_single (u : Unit) (b a a' : A) :
    MatrixMap.conj (Matrix.single u b (1 : ℂ)) (Matrix.single a a' 1) =
      if b = a ∧ b = a' then Matrix.single () () 1 else 0 := by
  cases u
  rw [MatrixMap.conj_apply, Matrix.conjTranspose_single, star_one]
  by_cases h1 : b = a
  · subst h1
    rw [Matrix.single_mul_single_same, one_mul]
    by_cases h2 : b = a'
    · subst h2
      rw [Matrix.single_mul_single_same, one_mul, ite_eq_left ⟨rfl, rfl⟩]
    · rw [Matrix.single_mul_single_of_ne (h := Ne.symm h2), ite_eq_right fun h ↦ h2 h.2]
  · rw [Matrix.single_mul_single_of_ne (h := h1), Matrix.zero_mul, ite_eq_right fun h ↦ h1 h.1]

theorem classical_single [DecidableEq ι] (g : A → ι) (a a' : A) (c : ι) :
    (DSubInstrument.classical (B := fun _ ↦ Unit) g (fun _ ↦ ())).branch c
        (Matrix.single a a' 1) = if a = a' ∧ g a = c then Matrix.single () () 1 else 0 := by
  rw [DSubInstrument.classical, DSubInstrument.branch_map_apply_univ, LinearMap.sum_apply]
  simp only [cast_eq]
  rw [Finset.sum_eq_single a (fun b _ hb ↦ ?_) (by simp)]
  · split_ifs with h1 h2 h2
    · rw [DSubInstrument.branch_ofKraus_apply, conj_single_single, ite_eq_left ⟨rfl, h2.1⟩]
    · rw [DSubInstrument.branch_ofKraus_apply, conj_single_single, ite_eq_right]
      rintro ⟨-, h⟩
      exact h2 ⟨h, h1⟩
    · exact absurd h2.2 h1
    · rfl
  · split_ifs
    · rw [DSubInstrument.branch_ofKraus_apply, conj_single_single, ite_eq_right]
      rintro ⟨h, -⟩
      exact hb h
    · rfl

end single

theorem callBasisPrep_single {spec : QuantumOracleSpec.{0, 0}} (p : spec.Port) (a : spec.In p)
    {D : Type} [Fintype D] [DecidableEq D] (u : PUnit.{1}) (d d' : D) :
    ((QComp.callBasisPrep p (QReg.of Unit) a).frame D).branch u
        (Matrix.single ((), d) ((), d') 1) = Matrix.single ((a, ()), d) ((a, ()), d') 1 := by
  rw [frame_single, QComp.callBasisPrep, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    relabel_single]
  rw [show (Equiv.uniqueProd (QReg.of Unit).carrier Unit).symm () = ((), ()) from rfl, frame_single,
    DSubInstrument.branch_classical_basis]
  simp [Matrix.single_kronecker_single]

theorem callBasisMeasure_single {spec : QuantumOracleSpec.{0, 0}} (p : spec.Port) {β : Type}
    [DecidableEq β] (read : spec.Out p → spec.Result p → β) (r : spec.Result p)
    (o o' : spec.Out p) (b : β) :
    (QComp.callBasisMeasure p (QReg.of Unit) read r).branch b
        (Matrix.single (o, ()) (o', ()) 1) =
      if o = o' ∧ read o r = b then Matrix.single () () 1 else 0 := by
  rw [QComp.callBasisMeasure, DSubInstrument.branch_bind_apply, tsum_eq_single (read o r) ?_]
  · rw [frame_single, classical_single, DSubInstrument.branch_bind_unit, LinearMap.comp_apply]
    by_cases ho : o = o'
    · subst ho
      simp only [true_and, ↓reduceIte, Matrix.single_kronecker_single, mul_one, relabel_single]
      by_cases hb : read o r = b
      · rw [ite_eq_left hb, hb, SubInstrument.branch_pure_self]
        rfl
      · rw [ite_eq_right hb, SubInstrument.branch_pure_of_ne (Ne.symm hb)]
        rfl
    · simp [ho]
  · intro c hc
    rw [frame_single, classical_single, ite_eq_right fun h ↦ hc h.2.symm]
    simp

theorem conj_basisMatrix_single {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (a a' : A) :
    MatrixMap.conj (basisMatrix e) (Matrix.single a a' 1) = Matrix.single (e a) (e a') 1 := by
  rw [conj_basisMatrix_equiv, submatrix_single]

/-- A classical hash query on an entry of the side register: it reports the hash at `t` read in
both side states, and keeps the entry when both read `y`. -/
theorem hashQuery_single (g : OvGame X Y S P Res) (G : X → Y) (t : X) (y : Y) (d d' : S × Unit) :
    ((g.sampled G).run₂ .instruments (hashQuery (S := S) (P := P) (Res := Res) t)).branch y
      (Matrix.single ((), d) ((), d') 1) =
      if g.answer d.1 G t = y ∧ g.answer d'.1 G t = y then Matrix.single ((), d) ((), d') 1
      else 0 := by
  let _ : Unique ((ovSpec X Y S P Res).Result (Sum.inl ())) := inferInstanceAs (Unique Unit)
  let _ : Fintype ((ovSpec X Y S P Res).Result (Sum.inl ())) := inferInstanceAs (Fintype Unit)
  rw [hashQuery]
  rw [QComp.run₂_callBasis (g.sampled G) (Sum.inl ()) (QReg.of Unit) ((t, (0 : Y)) : X × Y)
    (fun o _ ↦ o.2)]
  rw [DSubInstrument.branch_bind_apply, tsum_fintype, Fintype.sum_unique]
  erw [callBasisPrep_single]
  rw [DSubInstrument.branch_bind_apply, tsum_fintype, Fintype.sum_unique,
    QuantumRuntime.queryStep_branch_apply, relabel_single, frame_single]
  have hstep : ∀ m m' : (X × Y) × (S × Unit),
      ((g.sampled G).step (Sum.inl ())).branch () (Matrix.single m m' 1) =
        Matrix.single (tableOracleEquiv (fun t ↦ g.answer t.1 G) m)
          (tableOracleEquiv (fun t ↦ g.answer t.1 G) m') 1 :=
    fun m m' ↦ conj_basisMatrix_single _ m m'
  simp only [QuantumRuntime.queryEquivIn_apply, Equiv.refl_apply]
  erw [hstep]
  erw [Matrix.single_kronecker_single, one_mul, relabel_single]
  simp only [QuantumRuntime.queryEquivOut_apply]
  rw [SubInstrument.bind_pure]
  erw [frame_single, callBasisMeasure_single]
  split_ifs with h1 h2 h2 <;> simp_all [Matrix.single_kronecker_single]
  exact absurd (h1.1 ▸ h1.2) h2

/-- A classical algorithm on the hash, run beside the trivial register with classical queries. -/
noncomputable def classicalProg {β : Type} (oa : OracleComp (X →ₒ Y) β) :
    QComp (ovSpec X Y S P Res) (QReg.of Unit) (QReg.of Unit) β :=
  oa.toQuantumAt fun t ↦ hashQuery t

/-- On an entry of the side register, a classical algorithm keeps the entry up to a scalar, which
on the diagonal is whether the algorithm returns `b` against the hash read in that side state. -/
theorem classicalProg_single (g : OvGame X Y S P Res) (G : X → Y) {β : Type} [DecidableEq β]
    (oa : OracleComp (X →ₒ Y) β) (b : β) (d d' : S × Unit) :
    ∃ c : ℂ, ((g.sampled G).run₂ .instruments (classicalProg (S := S) (P := P) (Res := Res) oa)).branch
        b (Matrix.single ((), d) ((), d') 1) = c • Matrix.single ((), d) ((), d') 1 ∧
      (d = d' → c = if evalWithAnswerFn (QueryImpl.ofFn (g.answer d.1 G)) oa = b then 1 else 0) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [classicalProg, OracleComp.toQuantumAt_pure, QuantumRuntime.run₂_pure]
    refine ⟨if a = b then 1 else 0, ?_, fun _ ↦ by rw [evalWithAnswerFn_pure]⟩
    by_cases h : a = b
    · subst h
      rw [SubInstrument.branch_pure_self, ite_eq_left rfl, one_smul]
      rfl
    · rw [SubInstrument.branch_pure_of_ne (Ne.symm h), ite_eq_right h, zero_smul]
      rfl
  | query_bind t k ih =>
    rw [classicalProg, OracleComp.toQuantumAt_query_bind, QuantumRuntime.run₂_bind,
      DSubInstrument.branch_bind_apply, tsum_eq_single (g.answer d.1 G t) fun y hy ↦ by
        rw [hashQuery_single, ite_eq_right fun h ↦ hy h.1.symm, map_zero], hashQuery_single]
    by_cases h : g.answer d'.1 G t = g.answer d.1 G t
    · rw [ite_eq_left ⟨rfl, h⟩]
      obtain ⟨c, hc, hdiag⟩ := ih (g.answer d.1 G t)
      refine ⟨c, hc, fun hd ↦ ?_⟩
      rw [hdiag hd, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]
      rfl
    · rw [ite_eq_right fun h' : _ ∧ _ ↦ h h'.2, map_zero]
      refine ⟨0, (zero_smul _ _).symm, fun hd ↦ absurd (hd ▸ rfl) h⟩

/-- A classical algorithm scales each diagonal entry of the side register by whether it returns `b`
against the hash read in that side state. -/
theorem classicalProg_apply_diag (g : OvGame X Y S P Res) (G : X → Y) {β : Type} [DecidableEq β]
    (oa : OracleComp (X →ₒ Y) β) (b : β) (M : Matrix (Unit × (S × Unit)) (Unit × (S × Unit)) ℂ)
    (d : S × Unit) :
    ((g.sampled G).run₂ .instruments (classicalProg (S := S) (P := P) (Res := Res) oa)).branch b M
        ((), d) ((), d) =
      (if evalWithAnswerFn (QueryImpl.ofFn (g.answer d.1 G)) oa = b then 1 else 0) *
        M ((), d) ((), d) := by
  have hM : M = ∑ i, ∑ j, M i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp [Matrix.smul_single]
  have hentry : ∀ i j : Unit × (S × Unit),
      ((g.sampled G).run₂ .instruments (classicalProg (S := S) (P := P) (Res := Res) oa)).branch b
          (Matrix.single i j 1) ((), d) ((), d) =
        if i = ((), d) ∧ j = ((), d) then
          (if evalWithAnswerFn (QueryImpl.ofFn (g.answer d.1 G)) oa = b then 1 else 0) else 0 := by
    rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩
    obtain ⟨c, hc, hdiag⟩ := classicalProg_single g G oa b i j
    rw [hc]
    by_cases hij : i = d ∧ j = d
    · obtain ⟨rfl, rfl⟩ := hij
      simp [hdiag rfl]
    · rw [ite_eq_right fun h ↦ hij ⟨congrArg Prod.snd h.1, congrArg Prod.snd h.2⟩]
      simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      rw [ite_eq_right fun h ↦ hij ⟨congrArg Prod.snd h.1, congrArg Prod.snd h.2⟩,
        mul_zero]
  conv_lhs => rw [hM]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, hentry, smul_eq_mul]
  rw [Finset.sum_eq_single ((), d) (fun i _ hi ↦ Finset.sum_eq_zero fun j _ ↦ by
    rw [ite_eq_right fun h ↦ hi h.1, mul_zero]) (by simp),
    Finset.sum_eq_single ((), d) (fun j _ hj ↦ by rw [ite_eq_right fun h ↦ hj h.2, mul_zero])
      (by simp)]
  simp only [and_self, ↓reduceIte]
  split_ifs <;> simp [mul_comm]

/-- A program followed by a classical verifier of its result, whose result it returns beside. -/
noncomputable def withVerifier {A : QReg} {α β : Type}
    (adv : QComp (ovSpec X Y S P Res) A (QReg.of Unit) α) (ver : α → OracleComp (X →ₒ Y) β) :
    QComp (ovSpec X Y S P Res) A (QReg.of Unit) (α × β) :=
  adv.bind fun a ↦ (classicalProg (ver a)).map fun b ↦ (a, b)

/-- The diagonal entries of the side register after the verifier: those of the program, kept when the
verifier returns `b` against the hash read in that side state. -/
theorem jointPost_withVerifier_diag (g : OvGame X Y S P Res) (G : X → Y) {A : QReg} {α β : Type}
    [DecidableEq α] [DecidableEq β] (adv : QComp (ovSpec X Y S P Res) A (QReg.of Unit) α)
    (ver : α → OracleComp (X →ₒ Y) β) (ρ : SubState A) (a : α) (b : β) (d : S × Unit) :
    ((g.sampled G).jointPost₂ .instruments (withVerifier adv ver) ρ (a, b)).matrix ((), d) ((), d) =
      (if evalWithAnswerFn (QueryImpl.ofFn (g.answer d.1 G)) (ver a) = b then 1 else 0) *
        ((g.sampled G).jointPost₂ .instruments adv ρ a).matrix ((), d) ((), d) := by
  rw [QuantumRuntime.matrix_jointPost₂, QuantumRuntime.matrix_jointPost₂, withVerifier,
    QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply, tsum_eq_single a ?_]
  · rw [QuantumRuntime.run₂_map, SubInstrument.branch_map_apply,
      tsum_eq_single (⟨b, rfl⟩ : (fun b' ↦ (a, b')) ⁻¹' {(a, b)}) ?_]
    · exact classicalProg_apply_diag g G (ver a) b _ d
    · rintro ⟨b', hb'⟩ hne
      exact absurd (Subtype.ext (Prod.mk.inj hb').2) hne
  · intro a' ha'
    rw [QuantumRuntime.run₂_map, SubInstrument.branch_map_apply]
    have : IsEmpty ((fun b' ↦ (a', b')) ⁻¹' {(a, b)}) :=
      ⟨fun ⟨b', hb'⟩ ↦ ha' (Prod.mk.inj hb').1⟩
    rw [tsum_empty]

theorem blockW_withVerifier (g : OvGame X Y S P Res) (G : X → Y) {A : QReg} {α β : Type}
    [DecidableEq α] [DecidableEq β] (adv : QComp (ovSpec X Y S P Res) A (QReg.of Unit) α)
    (ver : α → OracleComp (X →ₒ Y) β) (ρ : SubState A) (a : α) (b : β) (s : S) :
    blockW s ((g.sampled G).jointPost₂ .instruments (withVerifier adv ver) ρ (a, b)).matrix =
      if evalWithAnswerFn (QueryImpl.ofFn (g.answer s G)) (ver a) = b then
        blockW s ((g.sampled G).jointPost₂ .instruments adv ρ a).matrix else 0 := by
  have h := fun u : Unit ↦ jointPost_withVerifier_diag g G adv ver ρ a b (s, ())
  unfold blockW
  split_ifs with hb
  · congr 1
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    cases u
    erw [h (), ite_eq_left hb, one_mul]
  · rw [← ENNReal.ofReal_zero]
    congr 1
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    cases u
    erw [h (), ite_eq_right hb, zero_mul, Complex.zero_re]

/-- **The verifier read on the side states.** An event of the result and of the verifier's answer
on the program followed by the verifier is the event of the program's result with the verifier run
against the hash read in each side state. -/
theorem sideW_withVerifier (g : OvGame X Y S P Res) (G : X → Y) {A : QReg} {α β : Type}
    [DecidableEq α] [DecidableEq β] (adv : QComp (ovSpec X Y S P Res) A (QReg.of Unit) α)
    (ver : α → OracleComp (X →ₒ Y) β) (ρ : SubState A) (ev : α × β → S → Bool) :
    sideW g G .instruments (withVerifier adv ver) ρ (fun p s ↦ ev p.2.2 s) =
      sideW g G .instruments adv ρ (fun p s ↦
        ev (p.2.2, evalWithAnswerFn (QueryImpl.ofFn (g.answer s G)) (ver p.2.2)) s) := by
  rw [sideW_eq_sum g G _ (withVerifier adv ver), sideW_eq_sum g G _ adv,
    ← (QuantumComp₂.leafEquiv _ _).tsum_eq,
    ← (QuantumComp₂.leafEquiv _ _).tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun a ↦ ?_
  rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hb := fun b ↦ blockW_withVerifier g G adv ver ρ a b s
  simp only [QuantumRuntime.jointPost₂_eq_jointPost] at hb
  change ∑' b, (if ev (a, b) s = true then blockW s ((g.sampled G).jointPost .instruments
    (withVerifier adv ver) ρ ⟨QReg.of Unit, rfl, (a, b)⟩).matrix else 0) = _
  simp only [hb]
  rw [tsum_eq_single (evalWithAnswerFn (QueryImpl.ofFn (g.answer s G)) (ver a)) fun b hb' ↦ by
    split_ifs with h1 h2
    · exact absurd h2.symm hb'
    · rfl
    · rfl]
  simp only [↓reduceIte]
  rfl

end OvGame

end Qrom
