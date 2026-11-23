module

public import Quantum.Sig.Sampled
public import Quantum.Xmss.Hybrid.CoinsHiding
public import Quantum.Sphincs.Assembly.GameR

@[expose] public section

/-!
# The stream relabelling: `msgPol` and `strPol` have the same averaged law

Step 3 of leanSPHINCS's chain (`uavg_p2R_msgPol_eq_strPol`): for every public data `p`, the
average over uniform hidden values `v` of the win probability of the canonical runtime-2 game
(`p2R`) is the same at the hybrid side's digest policy `msgPol` and at the event side's `strPol`.

**Route.** By lazy sampling (`Quantum.Sig.uavg_realizeT_outcome_eq_sampled`, with Template's
`disc_gameT`, `keepsLab_gameT`) each side is the run of the template game against the sampled
runtime. There the two games are related by a *renaming simulation* of the sampled register
(`RenSim`): `strPol`'s label `L` and store `σ` are renamed to `msgPol`'s by `rl L` and
`rs L σ`, the rest of the register kept. The renaming map `renMap` dephases the classical part
of the register (the hardwired cells, the memory, the store: `SCls`) and renames it (`rnOf`); it
keeps the trace. Along the simulation every step of the `strPol` run, summed over the outcomes
renamed to one outcome of the `msgPol` run, is that step after the renaming
(`sum_renMap_conj_ckr`, on states supported on good classes), so the runs intertwine leaf by
leaf (`renSim_branch`) and have the same laws (`evalDistMap_sampled_eq_of_renSim`).

**The generic part** (abstract `X Z S D M`): the classical Kraus operators `ckr` of the sampled
runtime's ports (`ctrlK_clsKraus`, `ctrlK_liftBlocks`, `revKS_eq_ckr`), the renaming map, the
relation `RenSim` (sponge and read ports kept, program ports realized alike at the renamed store,
reveals with a bijection of their values), its program-level forms (`renSim_revealThen`,
`renSim_progThen` with `PortSim`) and its run theorem, one case per port (`RunsInter`,
`runsInter_*`). The calls are stated in the sampled runtime's own register
(`sampled_queryStep_branch`), whose instances differ syntactically from those of `SReg`.

**leanSPHINCS's renaming** (`msgLab`, `msgStore`): a stream entry `.str j i` of a message `M`
marked with `.asg M j` is renamed to `.dig M i`; marks and unmarked entries vanish; the values,
randomizers and the `.dig` coordinates of the fallback past `signatureLimit` stay. The invariant
`StreamInv` (the store holds values only on the label, each message marked at most once, an
entry revealed exactly when marked, marked entries below the number of marks, `.dig`
coordinates only once the stream is used up) holds along the `strPol` run; no bound on the
number of signing requests is needed. Reveals of positions and randomizers are simulated by
themselves (`renSim_revealThen_vr`); the digest reveal of `strPol` by `msgPol`'s, its values
exchanged by `entryEquiv` (a stream entry, new or marked) or kept by `fallEquiv` (past the
stream); the `H_msg` ports agree at the renamed store (`forall₂_hmsgPorts`). Hence the games
(`renSim_gameT`) and their averaged laws (`uavg_p2R_msgPol_eq_strPol`).
-/

open Matrix MeasureTheory
open scoped ENNReal Kronecker

universe u v w

namespace Quantum.Sphincs.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Sig
open Quantum.Xmss.Hybrid (LazyProg restrictTo SuppOn suppOn_conj suppOn_amplify
  suppOn_amplify_right suppOn_relabel queryEquivIn_symm_snd queryEquivOut_symm_fst_snd kraus2 uavg)
open Quantum.Xmss.Assembly (tmplSpec RevealVals revealThen progThen readLift readLiftQ realizeT
  runtimeR liftRead readMono_liftRead readLens conj_conj_apply amplifyLeft_sum conj_single_apply)

/-! ## The classical part of the sampled register -/

section classes0

variable {X Z : Type} {S : Type} {D : S → Type} {M : Type}

variable (X Z S D M) in
/-- The classical part of the sampled register: the hardwired cells, the memory, the store. -/
abbrev SCls : Type :=
  Hw X Z × (Finset S × M) × Store D

/-- The classical part of a sampled register. -/
def sCls (x : SReg X Z S D M) : SCls X Z S D M :=
  (x.1.2.1, x.1.2.2, x.2)

/-- The sampled register with the databases `d` and the classical part `c`. -/
def sMk (d : DbReg X Z) (c : SCls X Z S D M) : SReg X Z S D M :=
  ((d, c.1, c.2.1), c.2.2)

@[simp]
theorem sCls_sMk (d : DbReg X Z) (c : SCls X Z S D M) : sCls (sMk d c) = c :=
  rfl

@[simp]
theorem sMk_fst_fst (d : DbReg X Z) (c : SCls X Z S D M) : (sMk d c).1.1 = d :=
  rfl

theorem sMk_sCls (x : SReg X Z S D M) : sMk x.1.1 (sCls x) = x :=
  rfl

theorem eq_sMk_iff {x : SReg X Z S D M} {d : DbReg X Z} {c : SCls X Z S D M} :
    x = sMk d c ↔ x.1.1 = d ∧ sCls x = c := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The renaming of a sampled register by a renaming `rn` of its classical part. -/
def renS (rn : SCls X Z S D M → SCls X Z S D M) (x : SReg X Z S D M) : SReg X Z S D M :=
  sMk x.1.1 (rn (sCls x))

@[simp]
theorem sCls_renS (rn : SCls X Z S D M → SCls X Z S D M) (x : SReg X Z S D M) :
    sCls (renS rn x) = rn (sCls x) :=
  rfl

@[simp]
theorem renS_fst_fst (rn : SCls X Z S D M → SCls X Z S D M) (x : SReg X Z S D M) :
    (renS rn x).1.1 = x.1.1 :=
  rfl

theorem eq_of_renS_eq {rn : SCls X Z S D M → SCls X Z S D M} {x x' : SReg X Z S D M}
    (h₁ : sCls x = sCls x') (h₂ : renS rn x = renS rn x') : x = x' := by
  have h₃ : x.1.1 = x'.1.1 := by simpa using congrArg (fun y : SReg X Z S D M ↦ y.1.1) h₂
  rw [← sMk_sCls x, ← sMk_sCls x', h₃, h₁]

theorem eq_renS_iff {rn : SCls X Z S D M → SCls X Z S D M} {x y : SReg X Z S D M} :
    y = renS rn x ↔ y.1.1 = x.1.1 ∧ sCls y = rn (sCls x) :=
  eq_sMk_iff

end classes0

section classes

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]

/-- The Kraus operator of the renaming on the class `c`: `|renS x⟩⟨x|` on the registers `x` of
class `c`. -/
def renJ (rn : SCls X Z S D M → SCls X Z S D M) (c : SCls X Z S D M) :
    Matrix (SReg X Z S D M) (SReg X Z S D M) ℂ :=
  Matrix.of fun y x ↦ if sCls x = c ∧ y = renS rn x then 1 else 0

/-- **The renaming map**: dephase the classical part of the sampled register and rename it. -/
noncomputable def renMap (rn : SCls X Z S D M → SCls X Z S D M) :
    MatrixMap (SReg X Z S D M) (SReg X Z S D M) :=
  ∑ c, MatrixMap.conj (renJ rn c)

theorem renMap_amplifyLeft (rn : SCls X Z S D M → SCls X Z S D M) (A : Type) [Fintype A]
    [DecidableEq A] :
    (renMap rn).amplifyLeft A = ∑ c, MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ renJ rn c) := by
  rw [renMap, amplifyLeft_sum]
  simp only [MatrixMap.amplifyLeft_conj]

theorem sum_conjTranspose_renJ_mul_self (rn : SCls X Z S D M → SCls X Z S D M) :
    ∑ c, (renJ rn c)ᴴ * renJ rn c = (1 : Matrix (SReg X Z S D M) (SReg X Z S D M) ℂ) := by
  ext x x'
  rw [Matrix.sum_apply, Finset.sum_eq_single (sCls x)]
  · rw [mul_apply, Finset.sum_eq_single (renS rn x)]
    · by_cases h : x = x'
      · subst h
        simp [renJ, conjTranspose_apply]
      · have h' : ¬(sCls x' = sCls x ∧ renS rn x = renS rn x') := fun h' ↦
          h (eq_of_renS_eq h'.1.symm h'.2)
        rw [one_apply_ne h]
        simp only [renJ, conjTranspose_apply, of_apply, and_self, ↓reduceIte, star_one, one_mul]
        rw [ite_eq_right h']
    · intro y _ hy
      simp [renJ, conjTranspose_apply, hy]
    · simp
  · intro c _ hc
    rw [mul_apply]
    refine Finset.sum_eq_zero fun y _ ↦ ?_
    simp [renJ, conjTranspose_apply, Ne.symm hc]
  · simp

/-- **The renaming keeps the trace.** -/
theorem trace_renMap (rn : SCls X Z S D M → SCls X Z S D M) (A : Type) [Fintype A]
    [DecidableEq A] (ρ : Matrix (A × SReg X Z S D M) (A × SReg X Z S D M) ℂ) :
    ((renMap rn).amplifyLeft A ρ).trace = ρ.trace := by
  rw [renMap_amplifyLeft, LinearMap.sum_apply, trace_sum]
  simp only [MatrixMap.trace_conj_apply]
  rw [← trace_sum, ← Finset.sum_mul]
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronecker_right, sum_conjTranspose_renJ_mul_self, one_kronecker_one, Matrix.one_mul]

/-! ### Classical Kraus operators -/

/-- **A classical Kraus operator of the sampled register**: on the registers whose classical part
`c` satisfies `P`, move the classical part to `φ c` and act on the databases (beside the port
registers) by `R c`. -/
noncomputable def ckr {O I : Type} (P : SCls X Z S D M → Prop) [DecidablePred P]
    (φ : SCls X Z S D M → SCls X Z S D M)
    (R : SCls X Z S D M → Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ) :
    Matrix (O × SReg X Z S D M) (I × SReg X Z S D M) ℂ :=
  Matrix.of fun y x ↦ if P (sCls x.2) ∧ sCls y.2 = φ (sCls x.2) then
    R (sCls x.2) (y.1, y.2.1.1) (x.1, x.2.1.1) else 0

omit [∀ s, Fintype (D s)] [Fintype M] in
theorem ckr_zero {O I : Type} (P : SCls X Z S D M → Prop) [DecidablePred P]
    (φ : SCls X Z S D M → SCls X Z S D M) :
    ckr P φ (fun _ ↦ (0 : Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ)) = 0 := by
  ext y x
  simp [ckr]

omit [∀ s, Fintype (D s)] [Fintype M] in
theorem ckr_false {O I : Type} (φ : SCls X Z S D M → SCls X Z S D M)
    (R : SCls X Z S D M → Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ) :
    ckr (fun _ ↦ False) φ R = 0 := by
  ext y x
  simp [ckr]

theorem one_kron_renJ_mul_ckr {O I : Type} [Fintype O] [DecidableEq O]
    (rn : SCls X Z S D M → SCls X Z S D M) (c₁ : SCls X Z S D M) (P : SCls X Z S D M → Prop)
    [DecidablePred P] (φ : SCls X Z S D M → SCls X Z S D M)
    (R : SCls X Z S D M → Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ) :
    ((1 : Matrix O O ℂ) ⊗ₖ renJ rn c₁) * ckr P φ R =
      ckr (fun z ↦ P z ∧ c₁ = φ z) (fun _ ↦ rn c₁) R := by
  ext ⟨o, y⟩ ⟨i, x⟩
  rw [mul_apply, Finset.sum_eq_single (o, sMk y.1.1 c₁)]
  · rw [kroneckerMap_apply, one_apply_eq, one_mul]
    simp only [renJ, ckr, of_apply]
    by_cases h₁ : sCls y = rn c₁
    · rw [ite_eq_left (show sCls (sMk y.1.1 c₁) = c₁ ∧ y = renS rn (sMk y.1.1 c₁) from
        ⟨rfl, eq_renS_iff.mpr ⟨rfl, h₁⟩⟩), one_mul]
      by_cases h₂ : P (sCls x) ∧ c₁ = φ (sCls x)
      · rw [ite_eq_left (show P (sCls x) ∧ sCls (sMk y.1.1 c₁) = φ (sCls x) from h₂),
          ite_eq_left (show (P (sCls x) ∧ c₁ = φ (sCls x)) ∧ sCls y = rn c₁ from ⟨h₂, h₁⟩)]
        rfl
      · rw [ite_eq_right (show ¬(P (sCls x) ∧ sCls (sMk y.1.1 c₁) = φ (sCls x)) from h₂),
          ite_eq_right fun h : (P (sCls x) ∧ c₁ = φ (sCls x)) ∧ sCls y = rn c₁ ↦ h₂ h.1]
    · rw [ite_eq_right (show ¬(sCls (sMk y.1.1 c₁) = c₁ ∧ y = renS rn (sMk y.1.1 c₁)) from
        fun h ↦ h₁ (eq_renS_iff.mp h.2).2), zero_mul,
        ite_eq_right fun h : (P (sCls x) ∧ c₁ = φ (sCls x)) ∧ sCls y = rn c₁ ↦ h₁ h.2]
  · rintro ⟨o', x'⟩ _ hne
    simp only [kroneckerMap_apply, renJ, of_apply]
    by_cases ho : o = o'
    · subst ho
      rw [ite_eq_right, mul_zero, zero_mul]
      rintro ⟨h₁, h₂⟩
      refine hne (Prod.ext rfl ?_)
      rw [eq_sMk_iff]
      exact ⟨(eq_renS_iff.mp h₂).1.symm, h₁⟩
    · rw [one_apply_ne ho]
      simp
  · simp

theorem ckr_mul_one_kron_renJ {O I : Type} [Fintype I] [DecidableEq I]
    (rn : SCls X Z S D M → SCls X Z S D M) (c : SCls X Z S D M) (P : SCls X Z S D M → Prop)
    [DecidablePred P] (φ : SCls X Z S D M → SCls X Z S D M)
    (R : SCls X Z S D M → Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ) :
    ckr P φ R * ((1 : Matrix I I ℂ) ⊗ₖ renJ rn c) =
      ckr (fun z ↦ z = c ∧ P (rn c)) (fun _ ↦ φ (rn c)) (fun _ ↦ R (rn c)) := by
  ext ⟨o, y⟩ ⟨i, x⟩
  rw [mul_apply, Finset.sum_eq_single (i, renS rn x)]
  · rw [kroneckerMap_apply, one_apply_eq, one_mul]
    simp only [renJ, ckr, of_apply, and_true]
    by_cases h : sCls x = c
    · subst h
      rw [ite_eq_left (show sCls x = sCls x from rfl), mul_one]
      by_cases h₂ : P (rn (sCls x)) ∧ sCls y = φ (rn (sCls x))
      · rw [ite_eq_left (show P (sCls (renS rn x)) ∧ sCls y = φ (sCls (renS rn x)) from h₂),
          ite_eq_left (show (sCls x = sCls x ∧ P (rn (sCls x))) ∧ sCls y = φ (rn (sCls x)) from
            ⟨⟨rfl, h₂.1⟩, h₂.2⟩)]
        rfl
      · rw [ite_eq_right (show ¬(P (sCls (renS rn x)) ∧ sCls y = φ (sCls (renS rn x))) from h₂),
          ite_eq_right fun h : (sCls x = sCls x ∧ P (rn (sCls x))) ∧
            sCls y = φ (rn (sCls x)) ↦ h₂ ⟨h.1.2, h.2⟩]
    · rw [ite_eq_right h,
        mul_zero, ite_eq_right fun h' : (sCls x = c ∧ P (rn c)) ∧ sCls y = φ (rn c) ↦ h h'.1.1]
  · rintro ⟨i', x'⟩ _ hne
    simp only [kroneckerMap_apply, renJ, of_apply]
    by_cases hi : i' = i
    · subst hi
      rw [ite_eq_right, mul_zero, mul_zero]
      rintro ⟨-, h⟩
      exact hne (by rw [h])
    · rw [one_apply_ne hi]
      simp
  · simp

/-- Classical Kraus operators that agree on the good classes act alike on operators supported
there. -/
theorem conj_ckr_congr {O I : Type} [Fintype I] [DecidableEq I] (G : SCls X Z S D M → Prop)
    {P P' : SCls X Z S D M → Prop} [DecidablePred P] [DecidablePred P']
    {φ φ' : SCls X Z S D M → SCls X Z S D M}
    {R R' : SCls X Z S D M → Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ}
    (h : ∀ c, G c → (P c ↔ P' c) ∧ (P c → φ c = φ' c ∧ R c = R' c))
    {ρ : Matrix (I × SReg X Z S D M) (I × SReg X Z S D M) ℂ}
    (hρ : SuppOn (fun x : I × SReg X Z S D M ↦ G (sCls x.2)) ρ) :
    MatrixMap.conj (ckr P φ R) ρ = MatrixMap.conj (ckr P' φ' R') ρ :=
  conj_eq_of_cols (fun x : I × SReg X Z S D M ↦ G (sCls x.2)) hρ fun y x hx ↦ by
    obtain ⟨hPP, hφR⟩ := h _ hx
    simp only [ckr, of_apply]
    by_cases hp : P (sCls x.2)
    · obtain ⟨h₁, h₂⟩ := hφR hp
      have hp' := hPP.mp hp
      simp only [hp, hp', true_and, h₁, h₂]
    · have hp' : ¬P' (sCls x.2) := fun h' ↦ hp (hPP.mpr h')
      simp only [hp, hp', false_and, ↓reduceIte]

theorem conj_ckr_eq_zero {O I : Type} [Fintype I] [DecidableEq I] (G : SCls X Z S D M → Prop)
    {P : SCls X Z S D M → Prop} [DecidablePred P] {φ : SCls X Z S D M → SCls X Z S D M}
    {R : SCls X Z S D M → Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ}
    (h : ∀ c, G c → ¬P c) {ρ : Matrix (I × SReg X Z S D M) (I × SReg X Z S D M) ℂ}
    (hρ : SuppOn (fun x : I × SReg X Z S D M ↦ G (sCls x.2)) ρ) :
    MatrixMap.conj (ckr P φ R) ρ = 0 := by
  rw [conj_ckr_congr G (P' := fun _ ↦ False) (φ' := φ) (R' := R)
    (fun c hc ↦ ⟨iff_false_intro (h c hc), fun hp ↦ absurd hp (h c hc)⟩) hρ, ckr_false,
    MatrixMap.conj_zero]
  rfl

/-- **A classical Kraus step and the renaming.** Let the outcomes `F` of the `strPol` step be those
renamed to one outcome of the `msgPol` step `(Pm, φm, Rm)`. If, on the good classes, the `strPol`
step is injective, its outcomes `F` are exactly those accepted by the renamed class, at most one
of them, with the renamed target and the same action, then the sum over `F` of the steps followed
by the renaming is the renaming followed by the `msgPol` step, on operators supported on good
classes. -/
theorem sum_renMap_conj_ckr {O I ι : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (rn : SCls X Z S D M → SCls X Z S D M) (G : SCls X Z S D M → Prop) (F : Finset ι)
    (Ps : ι → SCls X Z S D M → Prop) [∀ r, DecidablePred (Ps r)]
    (φs : ι → SCls X Z S D M → SCls X Z S D M)
    (Rs : ι → SCls X Z S D M → Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ)
    (Pm : SCls X Z S D M → Prop) [DecidablePred Pm] (φm : SCls X Z S D M → SCls X Z S D M)
    (Rm : SCls X Z S D M → Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ)
    (hinj : ∀ r ∈ F, ∀ c c', G c → G c' → Ps r c → Ps r c' → φs r c = φs r c' → c = c')
    (hex : ∀ c, G c → Pm (rn c) → ∃ r ∈ F, Ps r c)
    (huniq : ∀ c, G c → ∀ r ∈ F, ∀ r' ∈ F, Ps r c → Ps r' c → r = r')
    (hP : ∀ c, G c → ∀ r ∈ F, Ps r c → Pm (rn c))
    (hR : ∀ c, G c → ∀ r ∈ F, Ps r c → Rm (rn c) = Rs r c)
    (hφ : ∀ c, G c → ∀ r ∈ F, Ps r c → Rs r c ≠ 0 → φm (rn c) = rn (φs r c))
    (ρ : Matrix (I × SReg X Z S D M) (I × SReg X Z S D M) ℂ)
    (hρ : SuppOn (fun x : I × SReg X Z S D M ↦ G (sCls x.2)) ρ) :
    ∑ r ∈ F, (renMap rn).amplifyLeft O (MatrixMap.conj (ckr (Ps r) (φs r) (Rs r)) ρ) =
      MatrixMap.conj (ckr Pm φm Rm) ((renMap rn).amplifyLeft I ρ) := by
  classical
  have hL : ∀ r ∈ F, (renMap rn).amplifyLeft O (MatrixMap.conj (ckr (Ps r) (φs r) (Rs r)) ρ) =
      ∑ c, if G c ∧ Ps r c then MatrixMap.conj (ckr (· = c) (fun _ ↦ rn (φs r c))
        (fun _ ↦ Rs r c)) ρ else 0 := by
    intro r hr
    rw [renMap_amplifyLeft, LinearMap.sum_apply]
    simp only [conj_conj_apply, one_kron_renJ_mul_ckr]
    have hc₁ : ∀ c₁, MatrixMap.conj (ckr (fun z ↦ Ps r z ∧ c₁ = φs r z) (fun _ ↦ rn c₁)
        (Rs r)) ρ =
        ∑ c, if G c ∧ Ps r c ∧ φs r c = c₁ then
          MatrixMap.conj (ckr (· = c) (fun _ ↦ rn c₁) (fun _ ↦ Rs r c)) ρ else 0 := by
      intro c₁
      by_cases hex₁ : ∃ c₀, G c₀ ∧ Ps r c₀ ∧ φs r c₀ = c₁
      · obtain ⟨c₀, hg, hp, he⟩ := hex₁
        rw [Finset.sum_eq_single c₀ (fun c _ hc ↦ ite_eq_right fun h ↦
            hc (hinj r hr c c₀ h.1 hg h.2.1 hp (h.2.2.trans he.symm))) (by simp),
          ite_eq_left ⟨hg, hp, he⟩]
        refine conj_ckr_congr G (fun c hc ↦ ⟨⟨fun h ↦ hinj r hr c c₀ hc hg h.1 hp
          (h.2.symm.trans he.symm), fun h ↦ h ▸ ⟨hp, he.symm⟩⟩, fun h ↦ ⟨rfl, ?_⟩⟩) hρ
        rw [hinj r hr c c₀ hc hg h.1 hp (h.2.symm.trans he.symm)]
      · rw [Finset.sum_eq_zero fun c _ ↦ ite_eq_right fun h ↦ hex₁ ⟨c, h⟩]
        exact conj_ckr_eq_zero G (fun c hc h ↦ hex₁ ⟨c, hc, h.1, h.2.symm⟩) hρ
    simp only [hc₁]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Finset.sum_eq_single (φs r c) (fun c₁ _ hne ↦ ite_eq_right fun h ↦ hne h.2.2.symm)
      (by simp)]
    by_cases h : G c ∧ Ps r c
    · rw [ite_eq_left ⟨h.1, h.2, rfl⟩, ite_eq_left h]
    · rw [ite_eq_right fun h' ↦ h ⟨h'.1, h'.2.1⟩, ite_eq_right h]
  have hR' : MatrixMap.conj (ckr Pm φm Rm) ((renMap rn).amplifyLeft I ρ) =
      ∑ c, if G c ∧ Pm (rn c) then MatrixMap.conj (ckr (· = c) (fun _ ↦ φm (rn c))
        (fun _ ↦ Rm (rn c))) ρ else 0 := by
    rw [renMap_amplifyLeft, LinearMap.sum_apply, map_sum]
    simp only [conj_conj_apply, ckr_mul_one_kron_renJ]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    by_cases h : G c ∧ Pm (rn c)
    · rw [ite_eq_left h]
      exact conj_ckr_congr G (fun z _ ↦ ⟨⟨fun hz ↦ hz.1, fun hz ↦ ⟨hz, h.2⟩⟩,
        fun _ ↦ ⟨rfl, rfl⟩⟩) hρ
    · rw [ite_eq_right h]
      exact conj_ckr_eq_zero G (P := fun z ↦ z = c ∧ Pm (rn c))
        (fun z hz hz' ↦ h ⟨hz'.1 ▸ hz, hz'.2⟩) hρ
  rw [Finset.sum_congr rfl hL, hR', Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases hc : G c ∧ Pm (rn c)
  · obtain ⟨r, hr, hps⟩ := hex c hc.1 hc.2
    rw [Finset.sum_eq_single_of_mem r hr fun r' hr' hne ↦ ite_eq_right fun h ↦
        hne (huniq c hc.1 r' hr' r hr h.2 hps), ite_eq_left ⟨hc.1, hps⟩, ite_eq_left hc,
      hR c hc.1 r hr hps]
    by_cases h0 : Rs r c = 0
    · rw [h0, ckr_zero, ckr_zero]
    · rw [hφ c hc.1 r hr hps h0]
  · rw [ite_eq_right hc]
    exact Finset.sum_eq_zero fun r hr ↦ ite_eq_right fun h ↦ hc ⟨h.1, hP c h.1 r hr h.2⟩

/-- A classical Kraus step moves the support from the good classes to the targets of the good
classes it acts on. -/
theorem suppOn_conj_ckr {O I : Type} [Fintype I] (G G' : SCls X Z S D M → Prop)
    {P : SCls X Z S D M → Prop} [DecidablePred P] {φ : SCls X Z S D M → SCls X Z S D M}
    {R : SCls X Z S D M → Matrix (O × DbReg X Z) (I × DbReg X Z) ℂ}
    (h : ∀ c, G c → P c → R c ≠ 0 → G' (φ c))
    {ρ : Matrix (I × SReg X Z S D M) (I × SReg X Z S D M) ℂ}
    (hρ : SuppOn (fun x : I × SReg X Z S D M ↦ G (sCls x.2)) ρ) :
    SuppOn (fun x : O × SReg X Z S D M ↦ G' (sCls x.2)) (MatrixMap.conj (ckr P φ R) ρ) := by
  refine suppOn_conj _ (fun y x hK hx ↦ ?_) hρ
  simp only [ckr, of_apply] at hK
  split_ifs at hK with hc
  · rw [hc.2]
    exact h _ hx hc.1 fun h0 ↦ hK (by simp [h0])
  · exact absurd rfl hK

end classes

/-! ## The renaming of the classical part and the good classes -/

section rn

variable {X Z : Type} {S : Type} {D : S → Type} {M : Type}

/-- The renaming of the classical part by a renaming `rl` of the label and `rs` of the store (as a
function of the label): the hardwired cells and the inner memory stay. -/
def rnOf (rl : Finset S → Finset S) (rs : Finset S → Store D → Store D)
    (c : SCls X Z S D M) : SCls X Z S D M :=
  (c.1, (rl c.2.1.1, c.2.1.2), rs c.2.1.1 c.2.2)

/-- A good class: its label satisfies `P`, its label and store the invariant `G`. -/
def GoodC (G : Finset S → Store D → Prop) (P : Finset S → Prop) (c : SCls X Z S D M) : Prop :=
  P c.2.1.1 ∧ G c.2.1.1 c.2.2

end rn

/-! ## The ports of the sampled runtime as classical Kraus operators -/

section ports

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]

omit [∀ s, Fintype (D s)] [Fintype M] in
/-- A classical step controlled by the store. -/
theorem ctrlK_clsKraus (p : Store D → Hw X Z × (Finset S × M) → Prop)
    [∀ σ, DecidablePred (p σ)]
    (φ : Store D → Hw X Z × (Finset S × M) → Hw X Z × (Finset S × M))
    (Rf : Store D → Hw X Z × (Finset S × M) → Matrix (DbReg X Z) (DbReg X Z) ℂ) :
    ctrlK (fun σ ↦ (1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus (p σ) (φ σ) (Rf σ)) =
      ckr (fun c ↦ p c.2.2 (c.1, c.2.1))
        (fun c ↦ ((φ c.2.2 (c.1, c.2.1)).1, (φ c.2.2 (c.1, c.2.1)).2, c.2.2))
        (fun c ↦ (1 : Matrix Unit Unit ℂ) ⊗ₖ Rf c.2.2 (c.1, c.2.1)) := by
  ext ⟨⟨⟩, ⟨d', W', m'⟩, σ'⟩ ⟨⟨⟩, ⟨d, W, m⟩, σ⟩
  simp only [ctrlK, ckr, of_apply, kroneckerMap_apply, clsKraus_apply, sCls, one_apply_eq,
    one_mul, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

omit [∀ s, Fintype (D s)] [Fintype M] in
/-- The sponge ports: blocks of the classical part, the store kept. -/
theorem ctrlK_liftBlocks {P : Type} [Fintype P] [DecidableEq P]
    (B : Hw X Z × (Finset S × M) → Matrix (P × DbReg X Z) (P × DbReg X Z) ℂ) :
    ctrlK (D := D) (fun _ ↦ liftBlocks (hwSplit X Z (Finset S × M) P) B) =
      ckr (fun _ ↦ True) id (fun c ↦ B (c.1, c.2.1)) := by
  ext ⟨a', ⟨d', W', m'⟩, σ'⟩ ⟨a, ⟨d, W, m⟩, σ⟩
  simp only [ctrlK, ckr, of_apply, liftBlocks, submatrix_apply, hwSplit,
    Equiv.prodAssoc_symm_apply, blockDiagonal_apply, sCls, id, true_and, Prod.mk.injEq]
  split_ifs <;> simp_all

variable [∀ s, Nonempty (D s)]

omit [Fintype M] in
/-- The sampled reveals. -/
theorem revKS_eq_ckr (T : Finset S) (r : RevealVals D T × (Finset S × M)) :
    revKS (X := X) (Z := Z) T r = ckr (fun c ↦ c.2.1 = r.2)
      (fun c ↦ (c.1, (r.2.1 ∪ T, r.2.2), swapIn T r.2.1 r.1 c.2.2))
      (fun c ↦ revAmp T r.2.1 c.2.2 r.1 •
        (1 : Matrix (Unit × DbReg X Z) (Unit × DbReg X Z) ℂ)) := by
  ext ⟨⟨⟩, ⟨d', W', m'⟩, σ'⟩ ⟨⟨⟩, ⟨d, W, m⟩, σ⟩
  simp only [revKS, ckr, of_apply, recU, sCls, Matrix.smul_apply, one_apply, Prod.mk.injEq,
    smul_eq_mul]
  split_ifs <;> simp_all

omit [Fintype S] in
/-- The amplitude of a reveal depends on the agreement and on the number of new values only. -/
theorem revAmp_congr {T T' L L' : Finset S} {σ σ' : Store D} {w : RevealVals D T}
    {w' : RevealVals D T'} (hag : Agrees T' L' (fill σ') w' ↔ Agrees T L (fill σ) w)
    (hcard : Fintype.card (RevealVals D (T' \ L')) = Fintype.card (RevealVals D (T \ L))) :
    revAmp T' L' σ' w' = revAmp T L σ w := by
  unfold revAmp cAmp
  rw [hcard]
  by_cases h : Agrees T L (fill σ) w
  · rw [ite_eq_left (hag.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' ↦ h (hag.mp h')), ite_eq_right h]

omit [Fintype S] in
theorem agrees_of_revAmp_ne_zero {T L : Finset S} {σ : Store D} {w : RevealVals D T}
    (h : revAmp T L σ w • (1 : Matrix (Unit × DbReg X Z) (Unit × DbReg X Z) ℂ) ≠ 0) :
    Agrees T L (fill σ) w := by
  by_contra ha
  refine h ?_
  unfold revAmp
  rw [ite_eq_right ha, zero_smul]

end ports

/-! ## Fibers of steps on the classical part -/

section fibers

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]
  (rl : Finset S → Finset S) (rs : Finset S → Store D → Store D)

/-- The Kraus operator of a read with outcome `s = (o, (L, m))`: on the memory `(L, m)`, keep the
label, update the inner memory with `upd`, act on the databases by `Rr o` of the cells. -/
noncomputable def strRdK {Y : Type} (upd : M → Y → M)
    (Rr : Y → Hw X Z → Matrix (DbReg X Z) (DbReg X Z) ℂ)
    (s : Y × (Finset S × M)) : Matrix (Unit × SReg X Z S D M) (Unit × SReg X Z S D M) ℂ :=
  ckr (fun c ↦ c.2.1 = s.2) (fun c ↦ (c.1, (s.2.1, upd s.2.2 s.1), c.2.2))
    (fun c ↦ (1 : Matrix Unit Unit ℂ) ⊗ₖ Rr s.1 c.1)

/-- **Reads and the renaming**: the outcomes renamed to `r` are those with the renamed label. -/
theorem read_fiber {Y : Type} [Fintype Y] [DecidableEq Y] (upd : M → Y → M)
    (Rr : Y → Hw X Z → Matrix (DbReg X Z) (DbReg X Z) ℂ) (r : Y × (Finset S × M))
    (Gc : SCls X Z S D M → Prop) (τ : Matrix (Unit × SReg X Z S D M) (Unit × SReg X Z S D M) ℂ)
    (hτ : SuppOn (fun x : Unit × SReg X Z S D M ↦ Gc (sCls x.2)) τ) :
    ∑ s ∈ Finset.univ.filter (fun s : Y × (Finset S × M) ↦ (s.1, (rl s.2.1, s.2.2)) = r),
      (renMap (rnOf rl rs)).amplifyLeft Unit (MatrixMap.conj (strRdK upd Rr s) τ) =
      MatrixMap.conj (strRdK upd Rr r) ((renMap (rnOf rl rs)).amplifyLeft Unit τ) := by
  refine sum_renMap_conj_ckr (rnOf rl rs) Gc
    (Finset.univ.filter fun s : Y × (Finset S × M) ↦ (s.1, (rl s.2.1, s.2.2)) = r)
    (fun s c ↦ c.2.1 = s.2)
    (fun s c ↦ (c.1, (s.2.1, upd s.2.2 s.1), c.2.2))
    (fun s c ↦ (1 : Matrix Unit Unit ℂ) ⊗ₖ Rr s.1 c.1) (fun c ↦ c.2.1 = r.2)
    (fun c ↦ (c.1, (r.2.1, upd r.2.2 r.1), c.2.2))
    (fun c ↦ (1 : Matrix Unit Unit ℂ) ⊗ₖ Rr r.1 c.1) (fun s _ c c' _ _ h₁ h₂ he ↦ ?_)
    (fun c _ hm ↦ ⟨(r.1, c.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, Prod.ext rfl hm⟩,
      rfl⟩)
    (fun c _ s hs s' hs' h₁ h₂ ↦ ?_) (fun c _ s hs h₁ ↦ ?_) (fun c _ s hs _ ↦ ?_)
    (fun c _ s hs h₁ _ ↦ ?_) τ hτ
  · obtain ⟨W, mm, σ⟩ := c
    obtain ⟨W', mm', σ'⟩ := c'
    simp only [Prod.mk.injEq] at he ⊢
    exact ⟨he.1, h₁.trans h₂.symm, he.2.2⟩
  · have e₁ := (Finset.mem_filter.mp hs).2
    have e₂ := (Finset.mem_filter.mp hs').2
    exact Prod.ext ((congrArg Prod.fst e₁).trans (congrArg Prod.fst e₂).symm) (h₁.symm.trans h₂)
  · rw [← (Finset.mem_filter.mp hs).2]
    show (rl c.2.1.1, c.2.1.2) = (rl s.2.1, s.2.2)
    rw [h₁]
  · rw [← (Finset.mem_filter.mp hs).2]
    rfl
  · obtain ⟨W, mm, σ⟩ := c
    obtain rfl : mm = s.2 := h₁
    rw [← (Finset.mem_filter.mp hs).2]
    rfl

/-- Reads keep the label's good classes. -/
theorem suppOn_conj_strRdK (G : Finset S → Store D → Prop) (P : Finset S → Prop) {Y : Type}
    (upd : M → Y → M) (Rr : Y → Hw X Z → Matrix (DbReg X Z) (DbReg X Z) ℂ)
    (s : Y × (Finset S × M)) (τ : Matrix (Unit × SReg X Z S D M) (Unit × SReg X Z S D M) ℂ)
    (hτ : SuppOn (fun x : Unit × SReg X Z S D M ↦ GoodC G P (sCls x.2)) τ) :
    SuppOn (fun x : Unit × SReg X Z S D M ↦ GoodC G P (sCls x.2))
      (MatrixMap.conj (strRdK upd Rr s) τ) :=
  suppOn_conj_ckr (GoodC G P) (GoodC G P) (fun c hc hm _ ↦ by
    obtain ⟨W, mm, σ⟩ := c
    obtain rfl : mm = s.2 := hm
    exact hc) hτ

/-- The Kraus operator of a program port at the store: on the cells satisfying `ps σ`, hardwire
them by `us σ`, act on the databases by `Rs σ`. -/
noncomputable def pgK (ps : Store D → Hw X Z → Prop) [∀ σ, DecidablePred (ps σ)]
    (us : Store D → Hw X Z → Hw X Z) (Rs : Store D → Matrix (DbReg X Z) (DbReg X Z) ℂ) :
    Matrix (Unit × SReg X Z S D M) (Unit × SReg X Z S D M) ℂ :=
  ckr (fun c ↦ ps c.2.2 c.1) (fun c ↦ (us c.2.2 c.1, c.2.1, c.2.2))
    (fun c ↦ (1 : Matrix Unit Unit ℂ) ⊗ₖ Rs c.2.2)

/-- Program ports keep the good classes. -/
theorem suppOn_conj_pgK (G : Finset S → Store D → Prop) (P : Finset S → Prop)
    (ps : Store D → Hw X Z → Prop) [∀ σ, DecidablePred (ps σ)]
    (us : Store D → Hw X Z → Hw X Z) (Rs : Store D → Matrix (DbReg X Z) (DbReg X Z) ℂ)
    (τ : Matrix (Unit × SReg X Z S D M) (Unit × SReg X Z S D M) ℂ)
    (hτ : SuppOn (fun x : Unit × SReg X Z S D M ↦ GoodC G P (sCls x.2)) τ) :
    SuppOn (fun x : Unit × SReg X Z S D M ↦ GoodC G P (sCls x.2))
      (MatrixMap.conj (pgK ps us Rs) τ) :=
  suppOn_conj_ckr (GoodC G P) (GoodC G P) (fun c hc _ _ ↦ by
    obtain ⟨W, mm, σ⟩ := c
    exact hc) hτ

/-- **Program ports and the renaming**: ports realized alike at the store and at the renamed
store. -/
theorem prog_fiber (ps : Store D → Hw X Z → Prop) [∀ σ, DecidablePred (ps σ)]
    (us : Store D → Hw X Z → Hw X Z) (Rs : Store D → Matrix (DbReg X Z) (DbReg X Z) ℂ)
    (pm : Store D → Hw X Z → Prop) [∀ σ, DecidablePred (pm σ)]
    (um : Store D → Hw X Z → Hw X Z) (Rm : Store D → Matrix (DbReg X Z) (DbReg X Z) ℂ)
    (Gc : SCls X Z S D M → Prop)
    (hinj : ∀ σ W W', ps σ W → ps σ W' → us σ W = us σ W' → W = W')
    (hcomp : ∀ c : SCls X Z S D M, Gc c → (pm (rs c.2.1.1 c.2.2) c.1 ↔ ps c.2.2 c.1) ∧
      um (rs c.2.1.1 c.2.2) c.1 = us c.2.2 c.1 ∧ Rm (rs c.2.1.1 c.2.2) = Rs c.2.2)
    (τ : Matrix (Unit × SReg X Z S D M) (Unit × SReg X Z S D M) ℂ)
    (hτ : SuppOn (fun x : Unit × SReg X Z S D M ↦ Gc (sCls x.2)) τ) :
    (renMap (rnOf rl rs)).amplifyLeft Unit (MatrixMap.conj (pgK ps us Rs) τ) =
      MatrixMap.conj (pgK (M := M) pm um Rm) ((renMap (rnOf rl rs)).amplifyLeft Unit τ) := by
  have h := sum_renMap_conj_ckr (rnOf rl rs) Gc ({()} : Finset Unit)
    (fun _ c ↦ ps c.2.2 c.1) (fun _ c ↦ (us c.2.2 c.1, c.2.1, c.2.2))
    (fun _ c ↦ (1 : Matrix Unit Unit ℂ) ⊗ₖ Rs c.2.2) (fun c ↦ pm c.2.2 c.1)
    (fun c ↦ (um c.2.2 c.1, c.2.1, c.2.2)) (fun c ↦ (1 : Matrix Unit Unit ℂ) ⊗ₖ Rm c.2.2)
    (fun _ _ c c' _ _ h₁ h₂ he ↦ ?_) (fun c hc hm ↦ ⟨(), Finset.mem_singleton_self _,
      (hcomp c hc).1.mp hm⟩) (fun _ _ _ h _ h' _ _ ↦ by rw [Finset.mem_singleton.mp h,
        Finset.mem_singleton.mp h']) (fun c hc _ _ hp ↦ (hcomp c hc).1.mpr hp)
    (fun c hc _ _ _ ↦ by rw [← (hcomp c hc).2.2]; rfl)
    (fun c hc _ _ _ _ ↦ by
      show (um (rs c.2.1.1 c.2.2) c.1, _, _) = (us c.2.2 c.1, _, _)
      rw [(hcomp c hc).2.1]
      rfl) τ hτ
  · rwa [Finset.sum_singleton] at h
  · obtain ⟨W, mm, σ⟩ := c
    obtain ⟨W', mm', σ'⟩ := c'
    simp only [Prod.mk.injEq] at he ⊢
    obtain ⟨hu, rfl, rfl⟩ := he
    exact ⟨hinj σ W W' h₁ h₂ hu, rfl, rfl⟩

/-- **Sponge ports and the renaming**: blocks of the hardwired cells commute with it. -/
theorem sponge_fiber {P : Type} [Fintype P] [DecidableEq P]
    (B : Hw X Z × (Finset S × M) → Matrix (P × DbReg X Z) (P × DbReg X Z) ℂ)
    (hB : ∀ W m m', B (W, m) = B (W, m'))
    (τ : Matrix (P × SReg X Z S D M) (P × SReg X Z S D M) ℂ) :
    (renMap (rnOf rl rs)).amplifyLeft P (MatrixMap.conj (ckr (fun _ ↦ True) id
        (fun c ↦ B (c.1, c.2.1))) τ) =
      MatrixMap.conj (ckr (fun _ ↦ True) id (fun c ↦ B (c.1, c.2.1)))
        ((renMap (rnOf rl rs)).amplifyLeft P τ) := by
  have h := sum_renMap_conj_ckr (rnOf rl rs) (fun _ ↦ True) ({()} : Finset Unit)
    (fun _ _ ↦ True) (fun _ ↦ id) (fun _ c ↦ B (c.1, c.2.1)) (fun _ ↦ True) id
    (fun c ↦ B (c.1, c.2.1)) (fun _ _ _ _ _ _ _ _ he ↦ he)
    (fun _ _ _ ↦ ⟨(), Finset.mem_singleton_self _, trivial⟩)
    (fun _ _ _ h _ h' _ _ ↦ by rw [Finset.mem_singleton.mp h, Finset.mem_singleton.mp h'])
    (fun _ _ _ _ _ ↦ trivial) (fun c _ _ _ _ ↦ hB _ _ _) (fun _ _ _ _ _ _ ↦ rfl) τ
    fun _ _ _ ↦ ⟨trivial, trivial⟩
  rwa [Finset.sum_singleton] at h

omit [∀ s, Fintype (D s)] [Fintype M] in
/-- The reads of `h` lifted to the label, as classical Kraus operators. -/
theorem ctrlK_readH (z : Z) (u : M → Option X → M) (s : Option X × (Finset S × M)) :
    ctrlK (D := D) (fun _ ↦ hwReadKraus (liftRead (S := S) (.readH z u)) s) =
      strRdK u (fun o W ↦ cellRead W.1 z o ⊗ₖ
        (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ)) s := by
  ext ⟨⟨⟩, ⟨d', W', m'⟩, σ'⟩ ⟨⟨⟩, ⟨d, W, m⟩, σ⟩
  simp only [ctrlK, strRdK, ckr, of_apply, hwReadKraus, liftRead, readKrausH, kroneckerMap_apply,
    clsKraus_apply, sCls, one_apply_eq, one_mul, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

omit [∀ s, Fintype (D s)] [Fintype M] in
/-- The reads of `k` lifted to the label. -/
theorem ctrlK_readK (x : X) (u : M → Option Z → M) (s : Option Z × (Finset S × M)) :
    ctrlK (D := D) (fun _ ↦ hwReadKraus (liftRead (S := S) (.readK x u)) s) =
      strRdK u (fun o W ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        (cellRead W.2.1 x o ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))) s := by
  ext ⟨⟨⟩, ⟨d', W', m'⟩, σ'⟩ ⟨⟨⟩, ⟨d, W, m⟩, σ⟩
  simp only [ctrlK, strRdK, ckr, of_apply, hwReadKraus, liftRead, readKrausK, kroneckerMap_apply,
    clsKraus_apply, sCls, one_apply_eq, one_mul, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

omit [∀ s, Fintype (D s)] [Fintype M] in
/-- The reads of `k'` lifted to the label. -/
theorem ctrlK_readK' (x : X) (u : M → Option Z → M) (s : Option Z × (Finset S × M)) :
    ctrlK (D := D) (fun _ ↦ hwReadKraus (liftRead (S := S) (.readK' x u)) s) =
      strRdK u (fun o W ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead W.2.2 x o)) s := by
  ext ⟨⟨⟩, ⟨d', W', m'⟩, σ'⟩ ⟨⟨⟩, ⟨d, W, m⟩, σ⟩
  simp only [ctrlK, strRdK, ckr, of_apply, hwReadKraus, liftRead, readKrausK',
    kroneckerMap_apply,
    clsKraus_apply, sCls, one_apply_eq, one_mul, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

omit [∀ s, Fintype (D s)] [Fintype M] in
/-- The program ports of `h` at cells and values read from the store. -/
theorem ctrlK_progH (cf : Store D → Z × X) (r : Option X × Option X) :
    ctrlK (fun σ ↦ hwProgKraus (M := Finset S × M) (.programH (cf σ).1 (cf σ).2) r) =
      pgK (fun σ W ↦ W.1 (cf σ).1 = r.2)
        (fun σ W ↦ (Function.update W.1 (cf σ).1 (some (cf σ).2), W.2))
        (fun σ ↦ cellDiscard (cf σ).1 r.1 ⊗ₖ
          (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ)) := by
  ext ⟨⟨⟩, ⟨d', W', m'⟩, σ'⟩ ⟨⟨⟩, ⟨d, W, m⟩, σ⟩
  simp only [ctrlK, pgK, ckr, of_apply, hwProgKraus, programKrausH, kroneckerMap_apply,
    clsKraus_apply, sCls, one_apply_eq, one_mul, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

omit [∀ s, Fintype (D s)] [Fintype M] in
/-- The program ports of `k` at cells and values read from the store. -/
theorem ctrlK_progK (cf : Store D → X × Z) (r : Option Z × Option Z) :
    ctrlK (fun σ ↦ hwProgKraus (M := Finset S × M) (.programK (cf σ).1 (cf σ).2) r) =
      pgK (fun σ W ↦ W.2.1 (cf σ).1 = r.2)
        (fun σ W ↦ (W.1, Function.update W.2.1 (cf σ).1 (some (cf σ).2), W.2.2))
        (fun σ ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          (cellDiscard (cf σ).1 r.1 ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))) := by
  ext ⟨⟨⟩, ⟨d', W', m'⟩, σ'⟩ ⟨⟨⟩, ⟨d, W, m⟩, σ⟩
  simp only [ctrlK, pgK, ckr, of_apply, hwProgKraus, programKrausK, kroneckerMap_apply,
    clsKraus_apply, sCls, one_apply_eq, one_mul, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

omit [∀ s, Fintype (D s)] [Fintype M] in
/-- The program ports of `k'` at cells and values read from the store. -/
theorem ctrlK_progK' (cf : Store D → X × Z) (r : Option Z × Option Z) :
    ctrlK (fun σ ↦ hwProgKraus (M := Finset S × M) (.programK' (cf σ).1 (cf σ).2) r) =
      pgK (fun σ W ↦ W.2.2 (cf σ).1 = r.2)
        (fun σ W ↦ (W.1, W.2.1, Function.update W.2.2 (cf σ).1 (some (cf σ).2)))
        (fun σ ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellDiscard (cf σ).1 r.1)) := by
  ext ⟨⟨⟩, ⟨d', W', m'⟩, σ'⟩ ⟨⟨⟩, ⟨d, W, m⟩, σ⟩
  simp only [ctrlK, pgK, ckr, of_apply, hwProgKraus, programKrausK', kroneckerMap_apply,
    clsKraus_apply, sCls, one_apply_eq, one_mul, Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

end fibers

/-! ## Calls and sequences on supported states -/

section calls

variable {Dt : Type} [Fintype Dt] [DecidableEq Dt] {A I O E : Type} [Fintype A] [DecidableEq A]
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O] [Fintype E] [DecidableEq E]

/-- **A call on supported states**: relabel, a port step framed by `E`, relabel back; the steps
summed over a fiber of outcomes intertwine with a step through `V` on supported states. -/
theorem relabelFrame_fiber {ι : Type} (V : MatrixMap Dt Dt) (g : Dt → Prop) (ℓ : A ≃ I × E)
    (F : Finset ι) (Ss : ι → MatrixMap (I × Dt) (O × Dt)) (Sm : MatrixMap (I × Dt) (O × Dt))
    (h : ∀ τ, SuppOn (fun x : I × Dt ↦ g x.2) τ →
      ∑ r ∈ F, V.amplifyLeft O (Ss r τ) = Sm (V.amplifyLeft I τ))
    (ρ : Matrix (A × Dt) (A × Dt) ℂ) (hρ : SuppOn (fun x : A × Dt ↦ g x.2) ρ) :
    ∑ r ∈ F, V.amplifyLeft (O × E) ((SubInstrument.relabel (queryEquivOut O Dt E)).branch ()
        ((Ss r).amplify E ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ))) =
      (SubInstrument.relabel (queryEquivOut O Dt E)).branch ()
        (Sm.amplify E ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch ()
          (V.amplifyLeft A ρ))) := by
  have hin := LinearMap.congr_fun (intertwines_relabel_queryEquivIn V ℓ ()) ρ
  simp only [LinearMap.comp_apply] at hin
  rw [hin]
  have hσ : SuppOn (fun p : (I × Dt) × E ↦ g p.1.2)
      ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ) :=
    suppOn_relabel _ (fun q hq ↦ by rwa [queryEquivIn_symm_snd] at hq) hρ
  have hamp : Sm.amplify E ((V.amplifyLeft I).amplify E
      ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ)) =
      ∑ r ∈ F, (V.amplifyLeft O).amplify E ((Ss r).amplify E
        ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ)) := by
    ext x y
    rw [Matrix.sum_apply]
    simp only [MatrixMap.amplify_apply, MatrixMap.amplify_apply_submatrix]
    rw [← h (((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ).submatrix (·, x.2)
      (·, y.2)) fun a b hab ↦ hσ (a, x.2) (b, y.2) hab, Matrix.sum_apply]
  rw [hamp, map_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hout := LinearMap.congr_fun (intertwines_relabel_queryEquivOut V O E ())
    ((Ss r).amplify E ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ))
  simp only [LinearMap.comp_apply] at hout
  exact hout.symm

/-- A call whose step vanishes on supported states vanishes on them. -/
theorem relabelFrame_zero (g : Dt → Prop) (ℓ : A ≃ I × E) (S₀ : MatrixMap (I × Dt) (O × Dt))
    (h : ∀ τ, SuppOn (fun x : I × Dt ↦ g x.2) τ → S₀ τ = 0)
    (ρ : Matrix (A × Dt) (A × Dt) ℂ) (hρ : SuppOn (fun x : A × Dt ↦ g x.2) ρ) :
    (SubInstrument.relabel (queryEquivOut O Dt E)).branch ()
      (S₀.amplify E ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ)) = 0 := by
  have hσ : SuppOn (fun p : (I × Dt) × E ↦ g p.1.2)
      ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ) :=
    suppOn_relabel _ (fun q hq ↦ by rwa [queryEquivIn_symm_snd] at hq) hρ
  have h0 : S₀.amplify E ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ) = 0 := by
    ext x y
    rw [MatrixMap.amplify_apply, h (((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ)
      |>.submatrix (·, x.2) (·, y.2)) fun a b hab ↦ hσ (a, x.2) (b, y.2) hab]
    rfl
  rw [h0, map_zero]

/-- A call moves supports as its step does. -/
theorem suppOn_relabelFrame (g g' : Dt → Prop) (ℓ : A ≃ I × E)
    (S₀ : MatrixMap (I × Dt) (O × Dt))
    (h : ∀ τ, SuppOn (fun x : I × Dt ↦ g x.2) τ → SuppOn (fun x : O × Dt ↦ g' x.2) (S₀ τ))
    (ρ : Matrix (A × Dt) (A × Dt) ℂ) (hρ : SuppOn (fun x : A × Dt ↦ g x.2) ρ) :
    SuppOn (fun x : (O × E) × Dt ↦ g' x.2)
      ((SubInstrument.relabel (queryEquivOut O Dt E)).branch ()
        (S₀.amplify E ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ))) :=
  suppOn_relabel _ (fun q hq ↦ by rwa [queryEquivOut_symm_fst_snd] at hq)
    (suppOn_amplify S₀ h (suppOn_relabel _ (fun q hq ↦ by rwa [queryEquivIn_symm_snd] at hq) hρ))

omit [Fintype A] [DecidableEq A] in
/-- **Sequencing on supported states, over fibers of outcomes.** The instances are those of the
subinstruments (implicit), so that the statement matches the runs syntactically. -/
theorem bind_fiber_supp {instA : Fintype A} {B : Type} {instB : Fintype B} {ιs ιm : Type}
    [Fintype ιs] [Fintype ιm] [DecidableEq ιm] {κ : Type*} {C : κ → Type*}
    {instC : ∀ c, Fintype (C c)}
    (ps : SubInstrument A B ιs) (pm : SubInstrument A B ιm)
    (ks : ιs → DSubInstrument B κ C) (km : ιm → DSubInstrument B κ C)
    (VA : MatrixMap A A) (VB : MatrixMap B B) (VC : ∀ c, MatrixMap (C c) (C c))
    (gA : A → Prop) (g : ιs → ιm)
    (hfib : ∀ r ρ, SuppOn gA ρ →
      ∑ s ∈ Finset.univ.filter (fun s ↦ g s = r), VB (ps.branch s ρ) = pm.branch r (VA ρ))
    (hk : ∀ s ρ, SuppOn gA ρ → ∀ c,
      VC c ((ks s).branch c (ps.branch s ρ)) = (km (g s)).branch c (VB (ps.branch s ρ)))
    (ρ : Matrix A A ℂ) (hρ : SuppOn gA ρ) (c : κ) :
    VC c ((DSubInstrument.bind ps ks).branch c ρ) =
      (DSubInstrument.bind pm km).branch c (VA ρ) := by
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply, tsum_fintype,
    tsum_fintype, map_sum]
  simp only [hk _ ρ hρ c]
  rw [← Finset.sum_fiberwise Finset.univ g (fun s ↦ (km (g s)).branch c (VB (ps.branch s ρ)))]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← hfib r ρ hρ, map_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [(Finset.mem_filter.mp hs).2]

omit [Fintype A] [DecidableEq A] in
/-- Sequencing on supported states, outcome by outcome. -/
theorem bind_same_supp {instA : Fintype A} {B : Type} {instB : Fintype B} {ι : Type}
    [Fintype ι] [DecidableEq ι] {κ : Type*} {C : κ → Type*} {instC : ∀ c, Fintype (C c)}
    (ps pm : SubInstrument A B ι) (ks km : ι → DSubInstrument B κ C)
    (VA : MatrixMap A A) (VB : MatrixMap B B) (VC : ∀ c, MatrixMap (C c) (C c))
    (gA : A → Prop)
    (hfib : ∀ r ρ, SuppOn gA ρ → VB (ps.branch r ρ) = pm.branch r (VA ρ))
    (hk : ∀ s ρ, SuppOn gA ρ → ∀ c,
      VC c ((ks s).branch c (ps.branch s ρ)) = (km s).branch c (VB (ps.branch s ρ)))
    (ρ : Matrix A A ℂ) (hρ : SuppOn gA ρ) (c : κ) :
    VC c ((DSubInstrument.bind ps ks).branch c ρ) =
      (DSubInstrument.bind pm km).branch c (VA ρ) :=
  bind_fiber_supp ps pm ks km VA VB VC gA id (fun r ρ hρ ↦ by
    rw [← hfib r ρ hρ]
    simp [Finset.filter_eq']) hk ρ hρ c

/-- A call whose step intertwines with a step through `V` on supported states. -/
theorem relabelFrame_same (V : MatrixMap Dt Dt) (g : Dt → Prop) (ℓ : A ≃ I × E)
    (S₁ S₂ : MatrixMap (I × Dt) (O × Dt))
    (h : ∀ τ, SuppOn (fun x : I × Dt ↦ g x.2) τ → V.amplifyLeft O (S₁ τ) = S₂ (V.amplifyLeft I τ))
    (ρ : Matrix (A × Dt) (A × Dt) ℂ) (hρ : SuppOn (fun x : A × Dt ↦ g x.2) ρ) :
    V.amplifyLeft (O × E) ((SubInstrument.relabel (queryEquivOut O Dt E)).branch ()
        (S₁.amplify E ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch () ρ))) =
      (SubInstrument.relabel (queryEquivOut O Dt E)).branch ()
        (S₂.amplify E ((SubInstrument.relabel (queryEquivIn ℓ Dt)).branch ()
          (V.amplifyLeft A ρ))) := by
  have h' := relabelFrame_fiber V g ℓ ({()} : Finset Unit) (fun _ ↦ S₁) S₂
    (fun τ hτ ↦ by rw [Finset.sum_singleton]; exact h τ hτ) ρ hρ
  rwa [Finset.sum_singleton] at h'

omit [Fintype Dt] [DecidableEq Dt] [Fintype O] [DecidableEq O] in
/-- Rewriting the summands of a sum of renamed operators. -/
theorem sum_amplifyLeft_congr {ι : Type} (F : Finset ι) (V : MatrixMap Dt Dt)
    {S S' : ι → Matrix (O × Dt) (O × Dt) ℂ} (h : ∀ r, S r = S' r) :
    ∑ r ∈ F, V.amplifyLeft O (S r) = ∑ r ∈ F, V.amplifyLeft O (S' r) :=
  Finset.sum_congr rfl fun r _ ↦ congrArg _ (h r)

/-- An equation from equations of both sides. -/
theorem eq_of_sides {α : Sort*} {a b a' b' : α} (ha : a = a') (hb : b = b') (h : a' = b') :
    a = b :=
  ha.trans (h.trans hb.symm)

/-- Support of an operator equal to a supported one. -/
theorem suppOn_of_eq {α : Type*} {g : α → Prop} {τ τ' : Matrix α α ℂ} (h : τ = τ')
    (h' : SuppOn g τ') : SuppOn g τ :=
  h ▸ h'

/-- Two composites of linear maps agree at zero. -/
theorem map_map_eq_of_eq_zero {α β γ δ : Type*} (f₁ : MatrixMap α β) (f₂ : MatrixMap β γ)
    (g₁ : MatrixMap α δ) (g₂ : MatrixMap δ γ) {τ : Matrix α α ℂ} (h : τ = 0) :
    f₂ (f₁ τ) = g₂ (g₁ τ) := by
  rw [h, map_zero, map_zero, map_zero, map_zero]

end calls

/-! ## The renaming simulation -/

section sim

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] {M : Type} [Fintype M] [DecidableEq M]
  {good : LazyProg X Z S D → Prop} {L : LocalSig.{u, v}}

variable (rl : Finset S → Finset S) (rs : Finset S → Store D → Store D)
  (G : Finset S → Store D → Prop)

/-- The renaming of a read's result: the label of the memory renamed. -/
def readRen : (c : HwRead X Z M) → (liftRead (S := S) c).Result → (liftRead (S := S) c).Result
  | .readH _ _, r => (r.1, (rl r.2.1, r.2.2))
  | .readK _ _, r => (r.1, (rl r.2.1, r.2.2))
  | .readK' _ _, r => (r.1, (rl r.2.1, r.2.2))

variable (good) in
/-- The template port of a lifted read. -/
abbrev rdPort (c : HwRead X Z M) : (tmplSpec X Z S D M good).Port :=
  .inl (.inl (.inr ⟨liftRead c, readMono_liftRead c⟩))

/-- **The renaming simulation** of two template programs, from states whose label satisfies `P`
and whose label and store satisfy `G`: local operations, sponge and read ports alike (a read's
result renamed); program ports whose cells and values agree at the store and at the renamed
store; reveals of `T` and `T'` whose values correspond by `f L` and whose labels, stores, amplitudes
and invariant follow the renaming. -/
inductive RenSim {Ω : QReg → Type w} : (Finset S → Prop) → {A : QReg} →
    QuantumComp L (tmplSpec X Z S D M good) Ω A → QuantumComp L (tmplSpec X Z S D M good) Ω A →
      Prop
  | pure (P : Finset S → Prop) {A : QReg} (y : Ω A) :
      RenSim P (QuantumComp.pure y) (QuantumComp.pure y)
  | prim (P : Finset S → Prop) {A : QReg} (o : L.Op A)
      {k k' : (b : L.Outcome o) → QuantumComp L (tmplSpec X Z S D M good) Ω (L.next o b)}
      (h : ∀ b, RenSim P (k b) (k' b)) :
      RenSim P (QuantumComp.primBind o k) (QuantumComp.primBind o k')
  | sponge (P : Finset S → Prop) {A : QReg} (i : SpongePort) (E : QReg)
      (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inl (.inl (.inl i))) × E)
      {k k' : (tmplSpec X Z S D M good).Result (.inl (.inl (.inl i))) →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inl (.inl i))) × E))}
      (h : ∀ r, RenSim P (k r) (k' r)) :
      RenSim P (QuantumComp.queryBind (.inl (.inl (.inl i))) E ℓ k)
        (QuantumComp.queryBind (.inl (.inl (.inl i))) E ℓ k')
  | read (P : Finset S → Prop) {A : QReg} (c : HwRead X Z M) (E : QReg)
      (ℓ : A ≃ (tmplSpec X Z S D M good).In (rdPort good c) × E)
      {k k' : (tmplSpec X Z S D M good).Result (rdPort good c) →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (rdPort good c) × E))}
      (h : ∀ r, RenSim P (k r) (k' (readRen rl c r))) :
      RenSim P (QuantumComp.queryBind (rdPort good c) E ℓ k)
        (QuantumComp.queryBind (rdPort good c) E ℓ k')
  | progH (P : Finset S → Prop) {A : QReg} (T T' : Finset S) (c : RevealVals D T → Z × X)
      (c' : RevealVals D T' → Z × X) (hp : good (.programH T c)) (hp' : good (.programH T' c'))
      (E : QReg) (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inl (.inr ⟨.programH T c, hp⟩)) × E)
      {k : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programH T c, hp⟩)) →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programH T c, hp⟩)) × E))}
      {k' : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programH T' c', hp'⟩)) →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programH T' c', hp'⟩)) × E))}
      (hc : ∀ L σ, P L → G L σ →
        c (restrictTo T (fill σ)) = c' (restrictTo T' (fill (rs L σ))))
      (h : ∀ r, RenSim P (k r) (k' r)) :
      RenSim P (QuantumComp.queryBind (.inl (.inr ⟨.programH T c, hp⟩)) E ℓ k)
        (QuantumComp.queryBind (.inl (.inr ⟨.programH T' c', hp'⟩)) E ℓ k')
  | progK (P : Finset S → Prop) {A : QReg} (T T' : Finset S) (c : RevealVals D T → X × Z)
      (c' : RevealVals D T' → X × Z) (hp : good (.programK T c)) (hp' : good (.programK T' c'))
      (E : QReg) (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inl (.inr ⟨.programK T c, hp⟩)) × E)
      {k : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programK T c, hp⟩)) →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programK T c, hp⟩)) × E))}
      {k' : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programK T' c', hp'⟩)) →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programK T' c', hp'⟩)) × E))}
      (hc : ∀ L σ, P L → G L σ →
        c (restrictTo T (fill σ)) = c' (restrictTo T' (fill (rs L σ))))
      (h : ∀ r, RenSim P (k r) (k' r)) :
      RenSim P (QuantumComp.queryBind (.inl (.inr ⟨.programK T c, hp⟩)) E ℓ k)
        (QuantumComp.queryBind (.inl (.inr ⟨.programK T' c', hp'⟩)) E ℓ k')
  | progK' (P : Finset S → Prop) {A : QReg} (T T' : Finset S) (c : RevealVals D T → X × Z)
      (c' : RevealVals D T' → X × Z) (hp : good (.programK' T c))
      (hp' : good (.programK' T' c')) (E : QReg)
      (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inl (.inr ⟨.programK' T c, hp⟩)) × E)
      {k : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programK' T c, hp⟩)) →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programK' T c, hp⟩)) × E))}
      {k' : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programK' T' c', hp'⟩)) →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programK' T' c', hp'⟩)) × E))}
      (hc : ∀ L σ, P L → G L σ →
        c (restrictTo T (fill σ)) = c' (restrictTo T' (fill (rs L σ))))
      (h : ∀ r, RenSim P (k r) (k' r)) :
      RenSim P (QuantumComp.queryBind (.inl (.inr ⟨.programK' T c, hp⟩)) E ℓ k)
        (QuantumComp.queryBind (.inl (.inr ⟨.programK' T' c', hp'⟩)) E ℓ k')
  | reveal (P : Finset S → Prop) {A : QReg} (T T' : Finset S)
      (f : Finset S → RevealVals D T ≃ RevealVals D T') (E : QReg)
      (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inr T) × E)
      {k : (tmplSpec X Z S D M good).Result (.inr T) →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (.inr T) × E))}
      {k' : (tmplSpec X Z S D M good).Result (.inr T') →
        QuantumComp L (tmplSpec X Z S D M good) Ω
          (QReg.of ((tmplSpec X Z S D M good).Out (.inr T') × E))}
      (hrl : ∀ L σ, P L → G L σ → rl (L ∪ T) = rl L ∪ T')
      (hrs : ∀ L σ w, P L → G L σ → Agrees T L (fill σ) w →
        rs (L ∪ T) (swapIn T L w σ) = swapIn T' (rl L) (f L w) (rs L σ))
      (hag : ∀ L σ w, P L → G L σ →
        (Agrees T' (rl L) (fill (rs L σ)) (f L w) ↔ Agrees T L (fill σ) w))
      (hcard : ∀ L σ, P L → G L σ →
        Fintype.card (RevealVals D (T' \ rl L)) = Fintype.card (RevealVals D (T \ L)))
      (hG : ∀ L σ w, P L → G L σ → Agrees T L (fill σ) w → G (L ∪ T) (swapIn T L w σ))
      (h : ∀ w L m, P L →
        RenSim (fun L' ↦ L' = L ∪ T) (k (w, (L, m))) (k' (f L w, (rl L, m)))) :
      RenSim P (QuantumComp.queryBind (.inr T) E ℓ k) (QuantumComp.queryBind (.inr T') E ℓ k')

variable {rl rs G}

omit [Fintype S] [Fintype M] [DecidableEq M] in
/-- A simulation from more labels is one from fewer. -/
theorem RenSim.mono {Ω : QReg → Type w} {P : Finset S → Prop} {A : QReg}
    {x y : QuantumComp L (tmplSpec X Z S D M good) Ω A} (h : RenSim rl rs G P x y)
    {P' : Finset S → Prop} (hP : ∀ L, P' L → P L) : RenSim rl rs G P' x y := by
  induction h generalizing P' with
  | pure P y => exact .pure P' y
  | prim P o _ ih => exact .prim P' o fun b ↦ ih b hP
  | sponge P i E ℓ _ ih => exact .sponge P' i E ℓ fun r ↦ ih r hP
  | read P c E ℓ _ ih => exact .read P' c E ℓ fun r ↦ ih r hP
  | progH P T T' c c' hp hp' E ℓ hc _ ih =>
    exact .progH P' T T' c c' hp hp' E ℓ (fun L σ hL ↦ hc L σ (hP L hL)) fun r ↦ ih r hP
  | progK P T T' c c' hp hp' E ℓ hc _ ih =>
    exact .progK P' T T' c c' hp hp' E ℓ (fun L σ hL ↦ hc L σ (hP L hL)) fun r ↦ ih r hP
  | progK' P T T' c c' hp hp' E ℓ hc _ ih =>
    exact .progK' P' T T' c c' hp hp' E ℓ (fun L σ hL ↦ hc L σ (hP L hL)) fun r ↦ ih r hP
  | reveal P T T' f E ℓ hrl hrs hag hcard hG h _ =>
    exact .reveal P' T T' f E ℓ (fun L σ hL ↦ hrl L σ (hP L hL))
      (fun L σ w hL ↦ hrs L σ w (hP L hL)) (fun L σ w hL ↦ hag L σ w (hP L hL))
      (fun L σ hL ↦ hcard L σ (hP L hL)) (fun L σ w hL ↦ hG L σ w (hP L hL))
      fun w L m hL ↦ h w L m (hP L hL)

omit [Fintype S] [Fintype M] [DecidableEq M] in
/-- **Sequencing**: continuations simulated from every label. -/
theorem RenSim.bind {Ω : QReg → Type w} {Ω' : QReg → Type w} {P : Finset S → Prop} {A : QReg}
    {x y : QuantumComp L (tmplSpec X Z S D M good) Ω A} (h : RenSim rl rs G P x y)
    {k k' : ∀ u, Ω u → QuantumComp L (tmplSpec X Z S D M good) Ω' u}
    (hk : ∀ u l, RenSim rl rs G (fun _ ↦ True) (k u l) (k' u l)) :
    RenSim rl rs G P (x.bind k) (y.bind k') := by
  induction h with
  | pure P y => exact (hk _ y).mono fun _ _ ↦ trivial
  | prim P o _ ih => exact .prim P o ih
  | sponge P i E ℓ _ ih => exact .sponge P i E ℓ ih
  | @read P A c E ℓ k₀ k₀' _ ih =>
    exact .read P c E ℓ (k := fun r ↦ (k₀ r).bind k) (k' := fun r ↦ (k₀' r).bind k') ih
  | progH P T T' c c' hp hp' E ℓ hc _ ih => exact .progH P T T' c c' hp hp' E ℓ hc ih
  | progK P T T' c c' hp hp' E ℓ hc _ ih => exact .progK P T T' c c' hp hp' E ℓ hc ih
  | progK' P T T' c c' hp hp' E ℓ hc _ ih => exact .progK' P T T' c c' hp hp' E ℓ hc ih
  | @reveal P A T T' f E ℓ k₀ k₀' hrl hrs hag hcard hG _ ih =>
    exact .reveal P T T' f E ℓ (k := fun r ↦ (k₀ r).bind k) (k' := fun r ↦ (k₀' r).bind k')
      hrl hrs hag hcard hG ih

omit [Fintype S] [Fintype M] [DecidableEq M] in
/-- Sequencing of programs on fixed final registers. -/
theorem RenSim.bind₂ {P : Finset S → Prop} {A B C : QReg} {α β : Type}
    {x y : QComp (tmplSpec X Z S D M good) A B α} (h : RenSim rl rs G P x y)
    {k k' : α → QComp (tmplSpec X Z S D M good) B C β}
    (hk : ∀ a, RenSim rl rs G (fun _ ↦ True) (k a) (k' a)) :
    RenSim rl rs G P (x.bind k) (y.bind k') :=
  RenSim.bind h (by rintro u ⟨rfl, a⟩; exact hk a)

omit [Fintype S] [Fintype M] [DecidableEq M] in
variable (rl rs G) in
/-- **Substitutions** whose commands are simulated from every label. -/
theorem renSim_substitute {spec₀ : QuantumOracleSpec.{0, 0}}
    {σ₁ σ₂ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (tmplSpec X Z S D M good))}
    (h : ∀ A c, RenSim rl rs G (fun _ ↦ True) (σ₁ A c) (σ₂ A c)) {Ω : QReg → Type} {A : QReg}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Ω A) :
    RenSim rl rs G (fun _ ↦ True) (x.substitute σ₁) (x.substitute σ₂) := by
  induction x using IPFunctor.IFreeM.inductionOn with
  | pure _ y => exact .pure _ y
  | liftBind A c next ih =>
    rw [IPFunctor.IFreeM.substitute_liftBind, IPFunctor.IFreeM.substitute_liftBind]
    refine (h A c).bind fun u ans ↦ ?_
    obtain ⟨b, hb⟩ := ans
    subst hb
    exact ih b

omit [Fintype S] [Fintype M] [DecidableEq M] in
variable (rl rs G) in
/-- **Runtime 1's programs** (sponge and read ports) are simulated by themselves. -/
theorem renSim_readLift {Ω : QReg → Type w} (P : Finset S → Prop) {A : QReg}
    (y : QuantumComp L (hwReadSpec X Z M) Ω A) :
    RenSim rl rs G P (readLift good y) (readLift good y) := by
  induction y using QuantumComp.inductionOn with
  | pure _ y => exact .pure P y
  | primBind _ o k ih => exact .prim P o ih
  | queryBind _ i E ℓ k ih =>
    rcases i with i | c
    · exact .sponge P i E ℓ ih
    · cases c with
      | readH z u =>
        exact .read P (.readH z u) E ℓ (k := fun r ↦ readLift good (k (r.1, r.2.2)))
          (k' := fun r ↦ readLift good (k (r.1, r.2.2))) fun r ↦ ih (r.1, r.2.2)
      | readK x u =>
        exact .read P (.readK x u) E ℓ (k := fun r ↦ readLift good (k (r.1, r.2.2)))
          (k' := fun r ↦ readLift good (k (r.1, r.2.2))) fun r ↦ ih (r.1, r.2.2)
      | readK' x u =>
        exact .read P (.readK' x u) E ℓ (k := fun r ↦ readLift good (k (r.1, r.2.2)))
          (k' := fun r ↦ readLift good (k (r.1, r.2.2))) fun r ↦ ih (r.1, r.2.2)

variable (rl rs G) in
/-- **Simulated program ports**: ports of the same kind whose cells and values agree at the store
and at the renamed store, on good classes with labels in `P`. -/
inductive PortSim (P : Finset S → Prop) : LazyProg X Z S D → LazyProg X Z S D → Prop
  | progH (T T' : Finset S) (c : RevealVals D T → Z × X) (c' : RevealVals D T' → Z × X)
      (hc : ∀ L₁ σ, P L₁ → G L₁ σ →
        c (restrictTo T (fill σ)) = c' (restrictTo T' (fill (rs L₁ σ)))) :
      PortSim P (.programH T c) (.programH T' c')
  | progK (T T' : Finset S) (c : RevealVals D T → X × Z) (c' : RevealVals D T' → X × Z)
      (hc : ∀ L₁ σ, P L₁ → G L₁ σ →
        c (restrictTo T (fill σ)) = c' (restrictTo T' (fill (rs L₁ σ)))) :
      PortSim P (.programK T c) (.programK T' c')
  | progK' (T T' : Finset S) (c : RevealVals D T → X × Z) (c' : RevealVals D T' → X × Z)
      (hc : ∀ L₁ σ, P L₁ → G L₁ σ →
        c (restrictTo T (fill σ)) = c' (restrictTo T' (fill (rs L₁ σ)))) :
      PortSim P (.programK' T c) (.programK' T' c')

omit [Fintype S] [Fintype M] [DecidableEq M] in
/-- A local subinstrument followed by simulated continuations. -/
theorem renSim_act_bind {P : Finset S → Prop} {A B C : QReg} {α β : Type}
    (p : SubInstrument A B α) {k k' : α → QComp (tmplSpec X Z S D M good) B C β}
    (h : ∀ a, RenSim rl rs G P (k a) (k' a)) :
    RenSim rl rs G P ((QComp.act p).bind k) ((QComp.act p).bind k') := by
  rw [QComp.act_bind, QComp.act_bind]
  exact RenSim.prim P _ h

omit [Fintype S] [Fintype M] [DecidableEq M] in
/-- **A simulated reveal** of `T` and `T'` beside a held register. -/
theorem renSim_revealThen {P : Finset S → Prop} {B C : QReg} {α : Type} (T T' : Finset S)
    (f : Finset S → RevealVals D T ≃ RevealVals D T')
    {k : RevealVals D T × (Finset S × M) → QComp (tmplSpec X Z S D M good) B C α}
    {k' : RevealVals D T' × (Finset S × M) → QComp (tmplSpec X Z S D M good) B C α}
    (hrl : ∀ L₁ σ, P L₁ → G L₁ σ → rl (L₁ ∪ T) = rl L₁ ∪ T')
    (hrs : ∀ L₁ σ w, P L₁ → G L₁ σ → Agrees T L₁ (fill σ) w →
      rs (L₁ ∪ T) (swapIn T L₁ w σ) = swapIn T' (rl L₁) (f L₁ w) (rs L₁ σ))
    (hag : ∀ L₁ σ w, P L₁ → G L₁ σ →
      (Agrees T' (rl L₁) (fill (rs L₁ σ)) (f L₁ w) ↔ Agrees T L₁ (fill σ) w))
    (hcard : ∀ L₁ σ, P L₁ → G L₁ σ →
      Fintype.card (RevealVals D (T' \ rl L₁)) = Fintype.card (RevealVals D (T \ L₁)))
    (hG : ∀ L₁ σ w, P L₁ → G L₁ σ → Agrees T L₁ (fill σ) w → G (L₁ ∪ T) (swapIn T L₁ w σ))
    (h : ∀ w L₁ m, P L₁ →
      RenSim rl rs G (fun L' ↦ L' = L₁ ∪ T) (k (w, (L₁, m))) (k' (f L₁ w, (rl L₁, m)))) :
    RenSim rl rs G P (revealThen good T k) (revealThen good T' k') :=
  RenSim.reveal P T T' f B _ hrl hrs hag hcard hG fun w L₁ m hL ↦
    renSim_act_bind _ fun _ ↦ h w L₁ m hL

omit [Fintype S] [Fintype M] [DecidableEq M] in
/-- **Simulated program ports** beside a held register. -/
theorem renSim_progThen {P : Finset S → Prop} {B C : QReg} {α : Type} {p p' : LazyProg X Z S D}
    (hpp : PortSim rs G P p p') (hp : good p) (hp' : good p')
    {k k' : QComp (tmplSpec X Z S D M good) B C α} (h : RenSim rl rs G P k k') :
    RenSim rl rs G P (progThen p hp k) (progThen p' hp' k') := by
  cases hpp with
  | progH T T' c c' hc =>
    exact RenSim.progH P T T' c c' hp hp' B _ hc fun _ ↦ renSim_act_bind _ fun _ ↦ h
  | progK T T' c c' hc =>
    exact RenSim.progK P T T' c c' hp hp' B _ hc fun _ ↦ renSim_act_bind _ fun _ ↦ h
  | progK' T T' c c' hc =>
    exact RenSim.progK' P T T' c c' hp hp' B _ hc fun _ ↦ renSim_act_bind _ fun _ ↦ h

end sim

/-! ## The runs of simulated programs intertwine -/

section run

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] {M : Type} [Fintype M] [DecidableEq M]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {good : LazyProg X Z S D → Prop} {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}
  {rl : Finset S → Finset S} {rs : Finset S → Store D → Store D} {G : Finset S → Store D → Prop}

/-- A call of the sampled runtime, in the runtime's own register. -/
theorem sampled_queryStep_branch (m₀ : M) {A : QReg} (i : (tmplSpec X Z S D M good).Port)
    (E : QReg) (ℓ : A ≃ (tmplSpec X Z S D M good).In i × E)
    (r : (tmplSpec X Z S D M good).Result i)
    (ρ : Matrix (A × (sampledRuntime good m₀).D) (A × (sampledRuntime good m₀).D) ℂ) :
    ((sampledRuntime good m₀).queryStep i E ℓ).branch r ρ =
      (SubInstrument.relabel (queryEquivOut ((tmplSpec X Z S D M good).Out i)
        (sampledRuntime good m₀).D E)).branch ()
        ((((sampledRuntime good m₀).step i).branch r).amplify E
          ((SubInstrument.relabel (queryEquivIn ℓ (sampledRuntime good m₀).D)).branch () ρ)) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]

variable (rl rs G) in
/-- The runs of `x` and `y` against the sampled runtime intertwine through the renaming, leaf by
leaf, from states supported on good classes with labels in `P`. -/
abbrev RunsInter (m₀ : M) (P : Finset S → Prop) {A : QReg}
    (x y : QuantumComp L (tmplSpec X Z S D M good) Ω A) : Prop :=
  ∀ ρ : Matrix (A × SReg X Z S D M) (A × SReg X Z S D M) ℂ,
    SuppOn (fun z : A × SReg X Z S D M ↦ GoodC G P (sCls z.2)) ρ → ∀ p : Σ u, Ω u,
      (renMap (rnOf rl rs)).amplifyLeft p.1 (((sampledRuntime good m₀).run I x).branch p ρ) =
        ((sampledRuntime good m₀).run I y).branch p ((renMap (rnOf rl rs)).amplifyLeft A ρ)

theorem runsInter_pure (m₀ : M) (P : Finset S → Prop) {A : QReg} (y : Ω A) :
    RunsInter I rl rs G m₀ P (QuantumComp.pure (spec := tmplSpec X Z S D M good) y)
      (QuantumComp.pure y) := by
  intro ρ _ p
  simp only [QuantumRuntime.run_pure]
  by_cases hp : p = ⟨_, y⟩
  · subst hp
    simp only [DSubInstrument.branch_ret_self, LinearMap.id_apply]
  · simp only [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply, map_zero]

theorem runsInter_prim (m₀ : M) {P : Finset S → Prop} {A : QReg} (o : L.Op A)
    {k k' : (b : L.Outcome o) → QuantumComp L (tmplSpec X Z S D M good) Ω (L.next o b)}
    (ih : ∀ b, RunsInter I rl rs G m₀ P (k b) (k' b)) :
    RunsInter I rl rs G m₀ P (QuantumComp.primBind o k) (QuantumComp.primBind o k') := by
  intro ρ hρ p
  simp only [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
  have hs : Summable fun b ↦ ((sampledRuntime good m₀).run I (k b)).branch p
      (((I o).frame (SReg X Z S D M)).branch b ρ) :=
    (((I o).frame _).isCPTNIFamily.comp_eval
      (fun b ↦ ((sampledRuntime good m₀).run I (k b)).isCPTNIFamily) p).summable_apply ρ
  rw [MatrixMap.map_tsum _ hs]
  refine tsum_congr fun b ↦ ?_
  rw [ih b _ (by
    rw [DSubInstrument.branch_frame_apply]
    exact suppOn_amplify_right (g := fun d : SReg X Z S D M ↦ GoodC G P (sCls d)) _ hρ) p]
  exact congrArg _ (LinearMap.congr_fun
    ((DSubInstrument.Intertwines.frame_amplifyLeft (I o) (renMap (rnOf rl rs))) b) ρ).symm

theorem runsInter_sponge (m₀ : M) {P : Finset S → Prop} {A : QReg} (i : SpongePort) (E : QReg)
    (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inl (.inl (.inl i))) × E)
    {k k' : (tmplSpec X Z S D M good).Result (.inl (.inl (.inl i))) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inl (.inl i))) × E))}
    (ih : ∀ r, RunsInter I rl rs G m₀ P (k r) (k' r)) :
    RunsInter I rl rs G m₀ P (QuantumComp.queryBind (.inl (.inl (.inl i))) E ℓ k)
      (QuantumComp.queryBind (.inl (.inl (.inl i))) E ℓ k') := by
  intro ρ hρ p
  obtain ⟨B, hB, hU⟩ : ∃ B : Hw X Z × (Finset S × M) →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ,
      (∀ W m m', B (W, m) = B (W, m')) ∧
        (spongeHardwired X Z (hwEmpty X Z) ((∅ : Finset S), m₀)).U i =
          liftBlocks (hwSplit X Z (Finset S × M) (spongeIn X Z i)) B := by
    refine ⟨_, ?_, spongeHardwired_U _ _ i⟩
    intro W m m'
    rfl
  have hK : ∀ r, ((sampledRuntime good m₀).step (.inl (.inl (.inl i)))).branch r =
      MatrixMap.conj (ckr (fun _ ↦ True) id (fun c ↦ B (c.1, c.2.1))) := fun r ↦ by
    rw [← ctrlK_liftBlocks, ← hU]
    rfl
  rw [QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind]
  refine bind_same_supp (ι := Unit)
    (ps := (sampledRuntime good m₀).queryStep (.inl (.inl (.inl i))) E ℓ)
    (pm := (sampledRuntime good m₀).queryStep (.inl (.inl (.inl i))) E ℓ)
    (ks := fun r ↦ (sampledRuntime good m₀).run I (k r))
    (km := fun r ↦ (sampledRuntime good m₀).run I (k' r))
    ((renMap (rnOf rl rs)).amplifyLeft _) ((renMap (rnOf rl rs)).amplifyLeft _)
    (fun q : Σ u, Ω u ↦ (renMap (rnOf rl rs)).amplifyLeft q.1)
    (fun w : A × SReg X Z S D M ↦ GoodC G P (sCls w.2)) (fun r ρ hρ ↦ ?_)
    (fun s ρ hρ q ↦ ?_) ρ hρ p
  · erw [sampled_queryStep_branch, sampled_queryStep_branch]
    exact relabelFrame_same _ (fun d ↦ GoodC G P (sCls d)) ℓ _ _
      (fun τ _ ↦ by erw [hK]; exact sponge_fiber rl rs B hB τ) ρ hρ
  · refine ih s _ ?_ q
    erw [sampled_queryStep_branch]
    exact suppOn_relabelFrame (fun d ↦ GoodC G P (sCls d)) (fun d ↦ GoodC G P (sCls d)) ℓ _
      (fun τ hτ ↦ by
        erw [hK]
        exact suppOn_conj_ckr (GoodC G P) (GoodC G P) (fun c hc _ _ ↦ hc) hτ) ρ hρ

theorem runsInter_readH (m₀ : M) {P : Finset S → Prop} {A : QReg} (z : Z) (u : M → Option X → M)
    (E : QReg) (ℓ : A ≃ (tmplSpec X Z S D M good).In (rdPort good (.readH z u)) × E)
    {k k' : (tmplSpec X Z S D M good).Result (rdPort good (.readH z u)) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (rdPort good (.readH z u)) × E))}
    (ih : ∀ r, RunsInter I rl rs G m₀ P (k r) (k' (readRen rl (.readH z u) r))) :
    RunsInter I rl rs G m₀ P (QuantumComp.queryBind (rdPort good (.readH z u)) E ℓ k)
      (QuantumComp.queryBind (rdPort good (.readH z u)) E ℓ k') := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind]
  have hK : ∀ s, ((sampledRuntime good m₀).step (rdPort good (.readH z u))).branch s =
      MatrixMap.conj (strRdK u (fun o W ↦ cellRead W.1 z o ⊗ₖ
        (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ)) s) :=
    fun s ↦ congrArg MatrixMap.conj (ctrlK_readH z u s)
  refine bind_fiber_supp (ιs := Option X × (Finset S × M)) (ιm := Option X × (Finset S × M))
    (ps := (sampledRuntime good m₀).queryStep (rdPort good (.readH z u)) E ℓ)
    (pm := (sampledRuntime good m₀).queryStep (rdPort good (.readH z u)) E ℓ)
    (ks := fun r ↦ (sampledRuntime good m₀).run I (k r))
    (km := fun r ↦ (sampledRuntime good m₀).run I (k' r))
    ((renMap (rnOf rl rs)).amplifyLeft _) ((renMap (rnOf rl rs)).amplifyLeft _)
    (fun q : Σ u, Ω u ↦ (renMap (rnOf rl rs)).amplifyLeft q.1)
    (fun w : A × SReg X Z S D M ↦ GoodC G P (sCls w.2)) (readRen rl (.readH z u))
    (fun r ρ hρ ↦ ?_) (fun s ρ hρ q ↦ ?_) ρ hρ p
  · refine (sum_amplifyLeft_congr _ _ fun s ↦
      sampled_queryStep_branch m₀ (rdPort good (.readH z u)) E ℓ s ρ).trans ?_
    erw [sampled_queryStep_branch]
    refine relabelFrame_fiber _ (fun d ↦ GoodC G P (sCls d)) ℓ _ _ _ (fun τ hτ ↦ ?_) ρ hρ
    refine (sum_amplifyLeft_congr _ _ fun s ↦ LinearMap.congr_fun (hK s) τ).trans ?_
    erw [hK]
    exact read_fiber rl rs u _ r _ τ hτ
  · refine ih s _ ?_ q
    erw [sampled_queryStep_branch]
    refine suppOn_relabelFrame (fun d ↦ GoodC G P (sCls d)) (fun d ↦ GoodC G P (sCls d)) ℓ _
      (fun τ hτ ↦ ?_) ρ hρ
    erw [hK]
    exact suppOn_conj_strRdK G P u _ s τ hτ

theorem runsInter_readK (m₀ : M) {P : Finset S → Prop} {A : QReg} (x : X) (u : M → Option Z → M)
    (E : QReg) (ℓ : A ≃ (tmplSpec X Z S D M good).In (rdPort good (.readK x u)) × E)
    {k k' : (tmplSpec X Z S D M good).Result (rdPort good (.readK x u)) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (rdPort good (.readK x u)) × E))}
    (ih : ∀ r, RunsInter I rl rs G m₀ P (k r) (k' (readRen rl (.readK x u) r))) :
    RunsInter I rl rs G m₀ P (QuantumComp.queryBind (rdPort good (.readK x u)) E ℓ k)
      (QuantumComp.queryBind (rdPort good (.readK x u)) E ℓ k') := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind]
  have hK : ∀ s, ((sampledRuntime good m₀).step (rdPort good (.readK x u))).branch s =
      MatrixMap.conj (strRdK u (fun o W ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        (cellRead W.2.1 x o ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))) s) :=
    fun s ↦ congrArg MatrixMap.conj (ctrlK_readK x u s)
  refine bind_fiber_supp (ιs := Option Z × (Finset S × M)) (ιm := Option Z × (Finset S × M))
    (ps := (sampledRuntime good m₀).queryStep (rdPort good (.readK x u)) E ℓ)
    (pm := (sampledRuntime good m₀).queryStep (rdPort good (.readK x u)) E ℓ)
    (ks := fun r ↦ (sampledRuntime good m₀).run I (k r))
    (km := fun r ↦ (sampledRuntime good m₀).run I (k' r))
    ((renMap (rnOf rl rs)).amplifyLeft _) ((renMap (rnOf rl rs)).amplifyLeft _)
    (fun q : Σ u, Ω u ↦ (renMap (rnOf rl rs)).amplifyLeft q.1)
    (fun w : A × SReg X Z S D M ↦ GoodC G P (sCls w.2)) (readRen rl (.readK x u))
    (fun r ρ hρ ↦ ?_) (fun s ρ hρ q ↦ ?_) ρ hρ p
  · refine (sum_amplifyLeft_congr _ _ fun s ↦
      sampled_queryStep_branch m₀ (rdPort good (.readK x u)) E ℓ s ρ).trans ?_
    erw [sampled_queryStep_branch]
    refine relabelFrame_fiber _ (fun d ↦ GoodC G P (sCls d)) ℓ _ _ _ (fun τ hτ ↦ ?_) ρ hρ
    refine (sum_amplifyLeft_congr _ _ fun s ↦ LinearMap.congr_fun (hK s) τ).trans ?_
    erw [hK]
    exact read_fiber rl rs u _ r _ τ hτ
  · refine ih s _ ?_ q
    erw [sampled_queryStep_branch]
    refine suppOn_relabelFrame (fun d ↦ GoodC G P (sCls d)) (fun d ↦ GoodC G P (sCls d)) ℓ _
      (fun τ hτ ↦ ?_) ρ hρ
    erw [hK]
    exact suppOn_conj_strRdK G P u _ s τ hτ

theorem runsInter_readK' (m₀ : M) {P : Finset S → Prop} {A : QReg} (x : X)
    (u : M → Option Z → M) (E : QReg)
    (ℓ : A ≃ (tmplSpec X Z S D M good).In (rdPort good (.readK' x u)) × E)
    {k k' : (tmplSpec X Z S D M good).Result (rdPort good (.readK' x u)) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (rdPort good (.readK' x u)) × E))}
    (ih : ∀ r, RunsInter I rl rs G m₀ P (k r) (k' (readRen rl (.readK' x u) r))) :
    RunsInter I rl rs G m₀ P (QuantumComp.queryBind (rdPort good (.readK' x u)) E ℓ k)
      (QuantumComp.queryBind (rdPort good (.readK' x u)) E ℓ k') := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind]
  have hK : ∀ s, ((sampledRuntime good m₀).step (rdPort good (.readK' x u))).branch s =
      MatrixMap.conj (strRdK u (fun o W ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead W.2.2 x o)) s) :=
    fun s ↦ congrArg MatrixMap.conj (ctrlK_readK' x u s)
  refine bind_fiber_supp (ιs := Option Z × (Finset S × M)) (ιm := Option Z × (Finset S × M))
    (ps := (sampledRuntime good m₀).queryStep (rdPort good (.readK' x u)) E ℓ)
    (pm := (sampledRuntime good m₀).queryStep (rdPort good (.readK' x u)) E ℓ)
    (ks := fun r ↦ (sampledRuntime good m₀).run I (k r))
    (km := fun r ↦ (sampledRuntime good m₀).run I (k' r))
    ((renMap (rnOf rl rs)).amplifyLeft _) ((renMap (rnOf rl rs)).amplifyLeft _)
    (fun q : Σ u, Ω u ↦ (renMap (rnOf rl rs)).amplifyLeft q.1)
    (fun w : A × SReg X Z S D M ↦ GoodC G P (sCls w.2)) (readRen rl (.readK' x u))
    (fun r ρ hρ ↦ ?_) (fun s ρ hρ q ↦ ?_) ρ hρ p
  · refine (sum_amplifyLeft_congr _ _ fun s ↦
      sampled_queryStep_branch m₀ (rdPort good (.readK' x u)) E ℓ s ρ).trans ?_
    erw [sampled_queryStep_branch]
    refine relabelFrame_fiber _ (fun d ↦ GoodC G P (sCls d)) ℓ _ _ _ (fun τ hτ ↦ ?_) ρ hρ
    refine (sum_amplifyLeft_congr _ _ fun s ↦ LinearMap.congr_fun (hK s) τ).trans ?_
    erw [hK]
    exact read_fiber rl rs u _ r _ τ hτ
  · refine ih s _ ?_ q
    erw [sampled_queryStep_branch]
    refine suppOn_relabelFrame (fun d ↦ GoodC G P (sCls d)) (fun d ↦ GoodC G P (sCls d)) ℓ _
      (fun τ hτ ↦ ?_) ρ hρ
    erw [hK]
    exact suppOn_conj_strRdK G P u _ s τ hτ

theorem runsInter_progH (m₀ : M) {P : Finset S → Prop} {A : QReg} (T T' : Finset S)
    (c : RevealVals D T → Z × X) (c' : RevealVals D T' → Z × X) (hp : good (.programH T c))
    (hp' : good (.programH T' c')) (E : QReg)
    (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inl (.inr ⟨.programH T c, hp⟩)) × E)
    {k : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programH T c, hp⟩)) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programH T c, hp⟩)) × E))}
    {k' : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programH T' c', hp'⟩)) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programH T' c', hp'⟩)) × E))}
    (hc : ∀ L₁ σ, P L₁ → G L₁ σ →
      c (restrictTo T (fill σ)) = c' (restrictTo T' (fill (rs L₁ σ))))
    (ih : ∀ r, RunsInter I rl rs G m₀ P (k r) (k' r)) :
    RunsInter I rl rs G m₀ P (QuantumComp.queryBind (.inl (.inr ⟨.programH T c, hp⟩)) E ℓ k)
      (QuantumComp.queryBind (.inl (.inr ⟨.programH T' c', hp'⟩)) E ℓ k') := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind
    (spec := tmplSpec X Z S D M good) (i := .inl (.inr ⟨.programH T' c', hp'⟩)) (E := E)
    (ℓ := ℓ)]
  have hK : ∀ (T₀ : Finset S) (c₀ : RevealVals D T₀ → Z × X) (hp₀ : good (.programH T₀ c₀))
      (r : Option X × Option X),
      ((sampledRuntime good m₀).step (.inl (.inr ⟨.programH T₀ c₀, hp₀⟩))).branch r =
        MatrixMap.conj (ctrlK fun σ ↦ hwProgKraus (M := Finset S × M)
          (.programH (c₀ (restrictTo T₀ (fill σ))).1 (c₀ (restrictTo T₀ (fill σ))).2) r) :=
    fun _ _ _ _ ↦ rfl
  have hKs := fun r' ↦ (hK T c hp r').trans (congrArg MatrixMap.conj
    (ctrlK_progH (S := S) (D := D) (M := M) (fun σ ↦ c (restrictTo T (fill σ))) r'))
  have hKm := fun r' ↦ (hK T' c' hp' r').trans (congrArg MatrixMap.conj
    (ctrlK_progH (S := S) (D := D) (M := M) (fun σ ↦ c' (restrictTo T' (fill σ))) r'))
  refine bind_same_supp (ι := Option X × Option X)
    (ps := (sampledRuntime good m₀).queryStep (.inl (.inr ⟨.programH T c, hp⟩)) E ℓ)
    (pm := (sampledRuntime good m₀).queryStep (.inl (.inr ⟨.programH T' c', hp'⟩)) E ℓ)
    (ks := fun r ↦ (sampledRuntime good m₀).run I (k r))
    (km := fun r ↦ (sampledRuntime good m₀).run I (k' r))
    ((renMap (rnOf rl rs)).amplifyLeft _) ((renMap (rnOf rl rs)).amplifyLeft _)
    (fun q : Σ u, Ω u ↦ (renMap (rnOf rl rs)).amplifyLeft q.1)
    (fun w : A × SReg X Z S D M ↦ GoodC G P (sCls w.2)) (fun r ρ hρ ↦ ?_)
    (fun s ρ hρ q ↦ ?_) ρ hρ p
  · refine eq_of_sides (congrArg ((renMap (rnOf rl rs)).amplifyLeft _)
      (sampled_queryStep_branch m₀ (.inl (.inr ⟨.programH T c, hp⟩)) E ℓ r ρ))
      (sampled_queryStep_branch m₀ (.inl (.inr ⟨.programH T' c', hp'⟩)) E ℓ r _) ?_
    refine relabelFrame_same _ (fun d ↦ GoodC G P (sCls d)) ℓ _ _ (fun τ hτ ↦ ?_) ρ hρ
    refine eq_of_sides (congrArg ((renMap (rnOf rl rs)).amplifyLeft _)
      (LinearMap.congr_fun (hKs r) τ)) (LinearMap.congr_fun (hKm r) _) ?_
    refine prog_fiber rl rs _ _ _ _ _ _ (GoodC G P) (fun σ W W' h₁ h₂ hu ↦ ?_)
      (fun d hd ↦ ?_) τ hτ
    · obtain ⟨h₃, h₄⟩ := Prod.mk.inj hu
      exact Prod.ext (update_eq_update_iff (h₁.trans h₂.symm) h₃) h₄
    · rw [← hc _ _ hd.1 hd.2]
      exact ⟨Iff.rfl, rfl, rfl⟩
  · refine ih s _ ?_ q
    refine suppOn_of_eq
      (sampled_queryStep_branch m₀ (.inl (.inr ⟨.programH T c, hp⟩)) E ℓ s ρ) ?_
    refine suppOn_relabelFrame (fun d ↦ GoodC G P (sCls d)) (fun d ↦ GoodC G P (sCls d)) ℓ _
      (fun τ hτ ↦ ?_) ρ hρ
    refine suppOn_of_eq (LinearMap.congr_fun (hKs s) τ) ?_
    exact suppOn_conj_pgK G P _ _ _ τ hτ

theorem runsInter_progK (m₀ : M) {P : Finset S → Prop} {A : QReg} (T T' : Finset S)
    (c : RevealVals D T → X × Z) (c' : RevealVals D T' → X × Z) (hp : good (.programK T c))
    (hp' : good (.programK T' c')) (E : QReg)
    (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inl (.inr ⟨.programK T c, hp⟩)) × E)
    {k : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programK T c, hp⟩)) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programK T c, hp⟩)) × E))}
    {k' : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programK T' c', hp'⟩)) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programK T' c', hp'⟩)) × E))}
    (hc : ∀ L₁ σ, P L₁ → G L₁ σ →
      c (restrictTo T (fill σ)) = c' (restrictTo T' (fill (rs L₁ σ))))
    (ih : ∀ r, RunsInter I rl rs G m₀ P (k r) (k' r)) :
    RunsInter I rl rs G m₀ P (QuantumComp.queryBind (.inl (.inr ⟨.programK T c, hp⟩)) E ℓ k)
      (QuantumComp.queryBind (.inl (.inr ⟨.programK T' c', hp'⟩)) E ℓ k') := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind
    (spec := tmplSpec X Z S D M good) (i := .inl (.inr ⟨.programK T' c', hp'⟩)) (E := E)
    (ℓ := ℓ)]
  have hK : ∀ (T₀ : Finset S) (c₀ : RevealVals D T₀ → X × Z) (hp₀ : good (.programK T₀ c₀))
      (r : Option Z × Option Z),
      ((sampledRuntime good m₀).step (.inl (.inr ⟨.programK T₀ c₀, hp₀⟩))).branch r =
        MatrixMap.conj (ctrlK fun σ ↦ hwProgKraus (M := Finset S × M)
          (.programK (c₀ (restrictTo T₀ (fill σ))).1 (c₀ (restrictTo T₀ (fill σ))).2) r) :=
    fun _ _ _ _ ↦ rfl
  have hKs := fun r' ↦ (hK T c hp r').trans (congrArg MatrixMap.conj
    (ctrlK_progK (S := S) (D := D) (M := M) (fun σ ↦ c (restrictTo T (fill σ))) r'))
  have hKm := fun r' ↦ (hK T' c' hp' r').trans (congrArg MatrixMap.conj
    (ctrlK_progK (S := S) (D := D) (M := M) (fun σ ↦ c' (restrictTo T' (fill σ))) r'))
  refine bind_same_supp (ι := Option Z × Option Z)
    (ps := (sampledRuntime good m₀).queryStep (.inl (.inr ⟨.programK T c, hp⟩)) E ℓ)
    (pm := (sampledRuntime good m₀).queryStep (.inl (.inr ⟨.programK T' c', hp'⟩)) E ℓ)
    (ks := fun r ↦ (sampledRuntime good m₀).run I (k r))
    (km := fun r ↦ (sampledRuntime good m₀).run I (k' r))
    ((renMap (rnOf rl rs)).amplifyLeft _) ((renMap (rnOf rl rs)).amplifyLeft _)
    (fun q : Σ u, Ω u ↦ (renMap (rnOf rl rs)).amplifyLeft q.1)
    (fun w : A × SReg X Z S D M ↦ GoodC G P (sCls w.2)) (fun r ρ hρ ↦ ?_)
    (fun s ρ hρ q ↦ ?_) ρ hρ p
  · refine eq_of_sides (congrArg ((renMap (rnOf rl rs)).amplifyLeft _)
      (sampled_queryStep_branch m₀ (.inl (.inr ⟨.programK T c, hp⟩)) E ℓ r ρ))
      (sampled_queryStep_branch m₀ (.inl (.inr ⟨.programK T' c', hp'⟩)) E ℓ r _) ?_
    refine relabelFrame_same _ (fun d ↦ GoodC G P (sCls d)) ℓ _ _ (fun τ hτ ↦ ?_) ρ hρ
    refine eq_of_sides (congrArg ((renMap (rnOf rl rs)).amplifyLeft _)
      (LinearMap.congr_fun (hKs r) τ)) (LinearMap.congr_fun (hKm r) _) ?_
    refine prog_fiber rl rs _ _ _ _ _ _ (GoodC G P) (fun σ W W' h₁ h₂ hu ↦ ?_)
      (fun d hd ↦ ?_) τ hτ
    · obtain ⟨h₃, h₄⟩ := Prod.mk.inj hu
      obtain ⟨h₅, h₆⟩ := Prod.mk.inj h₄
      exact Prod.ext h₃ (Prod.ext (update_eq_update_iff (h₁.trans h₂.symm) h₅) h₆)
    · rw [← hc _ _ hd.1 hd.2]
      exact ⟨Iff.rfl, rfl, rfl⟩
  · refine ih s _ ?_ q
    refine suppOn_of_eq
      (sampled_queryStep_branch m₀ (.inl (.inr ⟨.programK T c, hp⟩)) E ℓ s ρ) ?_
    refine suppOn_relabelFrame (fun d ↦ GoodC G P (sCls d)) (fun d ↦ GoodC G P (sCls d)) ℓ _
      (fun τ hτ ↦ ?_) ρ hρ
    refine suppOn_of_eq (LinearMap.congr_fun (hKs s) τ) ?_
    exact suppOn_conj_pgK G P _ _ _ τ hτ

theorem runsInter_progK' (m₀ : M) {P : Finset S → Prop} {A : QReg} (T T' : Finset S)
    (c : RevealVals D T → X × Z) (c' : RevealVals D T' → X × Z) (hp : good (.programK' T c))
    (hp' : good (.programK' T' c')) (E : QReg)
    (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inl (.inr ⟨.programK' T c, hp⟩)) × E)
    {k : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programK' T c, hp⟩)) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programK' T c, hp⟩)) × E))}
    {k' : (tmplSpec X Z S D M good).Result (.inl (.inr ⟨.programK' T' c', hp'⟩)) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨.programK' T' c', hp'⟩)) × E))}
    (hc : ∀ L₁ σ, P L₁ → G L₁ σ →
      c (restrictTo T (fill σ)) = c' (restrictTo T' (fill (rs L₁ σ))))
    (ih : ∀ r, RunsInter I rl rs G m₀ P (k r) (k' r)) :
    RunsInter I rl rs G m₀ P (QuantumComp.queryBind (.inl (.inr ⟨.programK' T c, hp⟩)) E ℓ k)
      (QuantumComp.queryBind (.inl (.inr ⟨.programK' T' c', hp'⟩)) E ℓ k') := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind
    (spec := tmplSpec X Z S D M good) (i := .inl (.inr ⟨.programK' T' c', hp'⟩)) (E := E)
    (ℓ := ℓ)]
  have hK : ∀ (T₀ : Finset S) (c₀ : RevealVals D T₀ → X × Z) (hp₀ : good (.programK' T₀ c₀))
      (r : Option Z × Option Z),
      ((sampledRuntime good m₀).step (.inl (.inr ⟨.programK' T₀ c₀, hp₀⟩))).branch r =
        MatrixMap.conj (ctrlK fun σ ↦ hwProgKraus (M := Finset S × M)
          (.programK' (c₀ (restrictTo T₀ (fill σ))).1 (c₀ (restrictTo T₀ (fill σ))).2) r) :=
    fun _ _ _ _ ↦ rfl
  have hKs := fun r' ↦ (hK T c hp r').trans (congrArg MatrixMap.conj
    (ctrlK_progK' (S := S) (D := D) (M := M) (fun σ ↦ c (restrictTo T (fill σ))) r'))
  have hKm := fun r' ↦ (hK T' c' hp' r').trans (congrArg MatrixMap.conj
    (ctrlK_progK' (S := S) (D := D) (M := M) (fun σ ↦ c' (restrictTo T' (fill σ))) r'))
  refine bind_same_supp (ι := Option Z × Option Z)
    (ps := (sampledRuntime good m₀).queryStep (.inl (.inr ⟨.programK' T c, hp⟩)) E ℓ)
    (pm := (sampledRuntime good m₀).queryStep (.inl (.inr ⟨.programK' T' c', hp'⟩)) E ℓ)
    (ks := fun r ↦ (sampledRuntime good m₀).run I (k r))
    (km := fun r ↦ (sampledRuntime good m₀).run I (k' r))
    ((renMap (rnOf rl rs)).amplifyLeft _) ((renMap (rnOf rl rs)).amplifyLeft _)
    (fun q : Σ u, Ω u ↦ (renMap (rnOf rl rs)).amplifyLeft q.1)
    (fun w : A × SReg X Z S D M ↦ GoodC G P (sCls w.2)) (fun r ρ hρ ↦ ?_)
    (fun s ρ hρ q ↦ ?_) ρ hρ p
  · refine eq_of_sides (congrArg ((renMap (rnOf rl rs)).amplifyLeft _)
      (sampled_queryStep_branch m₀ (.inl (.inr ⟨.programK' T c, hp⟩)) E ℓ r ρ))
      (sampled_queryStep_branch m₀ (.inl (.inr ⟨.programK' T' c', hp'⟩)) E ℓ r _) ?_
    refine relabelFrame_same _ (fun d ↦ GoodC G P (sCls d)) ℓ _ _ (fun τ hτ ↦ ?_) ρ hρ
    refine eq_of_sides (congrArg ((renMap (rnOf rl rs)).amplifyLeft _)
      (LinearMap.congr_fun (hKs r) τ)) (LinearMap.congr_fun (hKm r) _) ?_
    refine prog_fiber rl rs _ _ _ _ _ _ (GoodC G P) (fun σ W W' h₁ h₂ hu ↦ ?_)
      (fun d hd ↦ ?_) τ hτ
    · obtain ⟨h₃, h₄⟩ := Prod.mk.inj hu
      obtain ⟨h₅, h₆⟩ := Prod.mk.inj h₄
      exact Prod.ext h₃ (Prod.ext h₅ (update_eq_update_iff (h₁.trans h₂.symm) h₆))
    · rw [← hc _ _ hd.1 hd.2]
      exact ⟨Iff.rfl, rfl, rfl⟩
  · refine ih s _ ?_ q
    refine suppOn_of_eq
      (sampled_queryStep_branch m₀ (.inl (.inr ⟨.programK' T c, hp⟩)) E ℓ s ρ) ?_
    refine suppOn_relabelFrame (fun d ↦ GoodC G P (sCls d)) (fun d ↦ GoodC G P (sCls d)) ℓ _
      (fun τ hτ ↦ ?_) ρ hρ
    refine suppOn_of_eq (LinearMap.congr_fun (hKs s) τ) ?_
    exact suppOn_conj_pgK G P _ _ _ τ hτ

theorem runsInter_reveal (m₀ : M) {P : Finset S → Prop} {A : QReg} (T T' : Finset S)
    (f : Finset S → RevealVals D T ≃ RevealVals D T') (E : QReg)
    (ℓ : A ≃ (tmplSpec X Z S D M good).In (.inr T) × E)
    {k : (tmplSpec X Z S D M good).Result (.inr T) →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (.inr T) × E))}
    {k' : (tmplSpec X Z S D M good).Result (.inr T') →
      QuantumComp L (tmplSpec X Z S D M good) Ω
        (QReg.of ((tmplSpec X Z S D M good).Out (.inr T') × E))}
    (hrl : ∀ L₁ σ, P L₁ → G L₁ σ → rl (L₁ ∪ T) = rl L₁ ∪ T')
    (hrs : ∀ L₁ σ w, P L₁ → G L₁ σ → Agrees T L₁ (fill σ) w →
      rs (L₁ ∪ T) (swapIn T L₁ w σ) = swapIn T' (rl L₁) (f L₁ w) (rs L₁ σ))
    (hag : ∀ L₁ σ w, P L₁ → G L₁ σ →
      (Agrees T' (rl L₁) (fill (rs L₁ σ)) (f L₁ w) ↔ Agrees T L₁ (fill σ) w))
    (hcard : ∀ L₁ σ, P L₁ → G L₁ σ →
      Fintype.card (RevealVals D (T' \ rl L₁)) = Fintype.card (RevealVals D (T \ L₁)))
    (hG : ∀ L₁ σ w, P L₁ → G L₁ σ → Agrees T L₁ (fill σ) w → G (L₁ ∪ T) (swapIn T L₁ w σ))
    (ih : ∀ w L₁ m, P L₁ → RunsInter I rl rs G m₀ (fun L' ↦ L' = L₁ ∪ T) (k (w, (L₁, m)))
      (k' (f L₁ w, (rl L₁, m)))) :
    RunsInter I rl rs G m₀ P (QuantumComp.queryBind (.inr T) E ℓ k)
      (QuantumComp.queryBind (.inr T') E ℓ k') := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind
    (spec := tmplSpec X Z S D M good) (i := .inr T') (E := E) (ℓ := ℓ)]
  have hK : ∀ (T₀ : Finset S) (r : RevealVals D T₀ × (Finset S × M)),
      ((sampledRuntime good m₀).step (.inr T₀)).branch r = MatrixMap.conj (ckr
        (fun c ↦ c.2.1 = r.2) (fun c ↦ (c.1, (r.2.1 ∪ T₀, r.2.2), swapIn T₀ r.2.1 r.1 c.2.2))
        (fun c ↦ revAmp T₀ r.2.1 c.2.2 r.1 •
          (1 : Matrix (Unit × DbReg X Z) (Unit × DbReg X Z) ℂ))) :=
    fun T₀ r ↦ congrArg MatrixMap.conj (revKS_eq_ckr T₀ r)
  refine bind_fiber_supp (ιs := RevealVals D T × (Finset S × M))
    (ιm := RevealVals D T' × (Finset S × M))
    (ps := (sampledRuntime good m₀).queryStep (.inr T) E ℓ)
    (pm := (sampledRuntime good m₀).queryStep (.inr T') E ℓ)
    (ks := fun r ↦ (sampledRuntime good m₀).run I (k r))
    (km := fun r ↦ (sampledRuntime good m₀).run I (k' r))
    ((renMap (rnOf rl rs)).amplifyLeft _) ((renMap (rnOf rl rs)).amplifyLeft _)
    (fun q : Σ u, Ω u ↦ (renMap (rnOf rl rs)).amplifyLeft q.1)
    (fun w : A × SReg X Z S D M ↦ GoodC G P (sCls w.2))
    (fun s : RevealVals D T × (Finset S × M) ↦ (f s.2.1 s.1, (rl s.2.1, s.2.2)))
    (fun r ρ hρ ↦ ?_) (fun s ρ hρ q ↦ ?_) ρ hρ p
  · refine eq_of_sides (sum_amplifyLeft_congr _ _ fun s ↦
      sampled_queryStep_branch m₀ (.inr T) E ℓ s ρ)
      (sampled_queryStep_branch m₀ (.inr T') E ℓ r _) ?_
    refine relabelFrame_fiber _ (fun d ↦ GoodC G P (sCls d)) ℓ _ _ _ (fun τ hτ ↦ ?_) ρ hρ
    refine eq_of_sides (sum_amplifyLeft_congr _ _ fun s ↦ LinearMap.congr_fun (hK T s) τ)
      (LinearMap.congr_fun (hK T' r) _) ?_
    refine sum_renMap_conj_ckr (rnOf rl rs) (GoodC G P)
      (Finset.univ.filter fun s : RevealVals D T × (Finset S × M) ↦
        (f s.2.1 s.1, (rl s.2.1, s.2.2)) = r) (fun s c ↦ c.2.1 = s.2)
      (fun s c ↦ (c.1, (s.2.1 ∪ T, s.2.2), swapIn T s.2.1 s.1 c.2.2))
      (fun s c ↦ revAmp T s.2.1 c.2.2 s.1 •
        (1 : Matrix (Unit × DbReg X Z) (Unit × DbReg X Z) ℂ)) (fun c ↦ c.2.1 = r.2)
      (fun c ↦ (c.1, (r.2.1 ∪ T', r.2.2), swapIn T' r.2.1 r.1 c.2.2))
      (fun c ↦ revAmp T' r.2.1 c.2.2 r.1 •
        (1 : Matrix (Unit × DbReg X Z) (Unit × DbReg X Z) ℂ))
      (fun s _ c c' _ _ h₁ h₂ he ↦ ?_) (fun c _ hm ↦ ⟨((f c.2.1.1).symm r.1, c.2.1),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [Equiv.apply_symm_apply]
          exact Prod.ext rfl hm⟩, rfl⟩)
      (fun c _ s hs s' hs' h₁ h₂ ↦ ?_) (fun c _ s hs h₁ ↦ ?_) (fun c hc s hs h₁ ↦ ?_)
      (fun c hc s hs h₁ h0 ↦ ?_) τ hτ
    · obtain ⟨W, mm, σ⟩ := c
      obtain ⟨W', mm', σ'⟩ := c'
      simp only [Prod.mk.injEq] at he ⊢
      refine ⟨he.1, h₁.trans h₂.symm, ?_⟩
      rw [← swapIn_swapIn T s.2.1 s.1 σ, he.2.2, swapIn_swapIn]
    · have e₂ : s.2 = s'.2 := h₁.symm.trans h₂
      have e₁ : f s.2.1 s.1 = f s'.2.1 s'.1 := congrArg Prod.fst
        ((Finset.mem_filter.mp hs).2.trans (Finset.mem_filter.mp hs').2.symm)
      rw [e₂] at e₁
      exact Prod.ext ((f s'.2.1).injective e₁) e₂
    · rw [← (Finset.mem_filter.mp hs).2]
      show (rl c.2.1.1, c.2.1.2) = (rl s.2.1, s.2.2)
      rw [h₁]
    · obtain ⟨w, L₀, m⟩ := s
      obtain ⟨W, mm, σ⟩ := c
      obtain rfl : mm = (L₀, m) := h₁
      obtain rfl := (Finset.mem_filter.mp hs).2
      exact congrArg (· • (1 : Matrix (Unit × DbReg X Z) (Unit × DbReg X Z) ℂ))
        (revAmp_congr (hag L₀ σ w hc.1 hc.2) (hcard L₀ σ hc.1 hc.2))
    · obtain ⟨w, L₀, m⟩ := s
      obtain ⟨W, mm, σ⟩ := c
      obtain rfl : mm = (L₀, m) := h₁
      obtain rfl := (Finset.mem_filter.mp hs).2
      have ha := agrees_of_revAmp_ne_zero h0
      show (W, (rl L₀ ∪ T', m), swapIn T' (rl L₀) (f L₀ w) (rs L₀ σ)) =
        (W, (rl (L₀ ∪ T), m), rs (L₀ ∪ T) (swapIn T L₀ w σ))
      rw [hrl L₀ σ hc.1 hc.2, hrs L₀ σ w hc.1 hc.2 ha]
  · obtain ⟨w, L₀, m⟩ := s
    by_cases hP : P L₀
    · refine ih w L₀ m hP _ ?_ q
      refine suppOn_of_eq (sampled_queryStep_branch m₀ (.inr T) E ℓ _ ρ) ?_
      refine suppOn_relabelFrame (fun d ↦ GoodC G P (sCls d))
        (fun d ↦ GoodC G (fun L' ↦ L' = L₀ ∪ T) (sCls d)) ℓ _ (fun τ hτ ↦ ?_) ρ hρ
      refine suppOn_of_eq (LinearMap.congr_fun (hK T _) τ) ?_
      refine suppOn_conj_ckr (GoodC G P) (GoodC G (fun L' ↦ L' = L₀ ∪ T))
        (fun c hc hm h0 ↦ ?_) hτ
      obtain ⟨W, mm, σ⟩ := c
      obtain rfl : mm = (L₀, m) := hm
      exact ⟨rfl, hG L₀ σ w hc.1 hc.2 (agrees_of_revAmp_ne_zero h0)⟩
    · have h0 : ((sampledRuntime good m₀).queryStep (.inr T) E ℓ).branch (w, (L₀, m)) ρ =
          0 := by
        refine (sampled_queryStep_branch m₀ (.inr T) E ℓ _ ρ).trans ?_
        refine relabelFrame_zero (fun d ↦ GoodC G P (sCls d)) ℓ _ (fun τ hτ ↦ ?_) ρ hρ
        refine (LinearMap.congr_fun (hK T _) τ).trans ?_
        refine conj_ckr_eq_zero (GoodC G P) (fun c hc hm ↦ ?_) hτ
        exact hP ((show c.2.1.1 = L₀ from congrArg Prod.fst hm) ▸ hc.1)
      exact map_map_eq_of_eq_zero _ _ _ _ h0

/-- **The runs intertwine** through the renaming, leaf by leaf, from states supported on good
classes. -/
theorem renSim_branch (m₀ : M) {P : Finset S → Prop} {A : QReg}
    {x y : QuantumComp L (tmplSpec X Z S D M good) Ω A} (h : RenSim rl rs G P x y) :
    RunsInter I rl rs G m₀ P x y := by
  induction h with
  | pure P y => exact runsInter_pure I m₀ P y
  | prim P o _ ih => exact runsInter_prim I m₀ o ih
  | sponge P i E ℓ _ ih => exact runsInter_sponge I m₀ i E ℓ ih
  | read P c E ℓ _ ih =>
    cases c with
    | readH z u => exact runsInter_readH I m₀ z u E ℓ ih
    | readK x u => exact runsInter_readK I m₀ x u E ℓ ih
    | readK' x u => exact runsInter_readK' I m₀ x u E ℓ ih
  | progH P T T' c c' hp hp' E ℓ hc _ ih =>
    exact runsInter_progH I m₀ T T' c c' hp hp' E ℓ hc ih
  | progK P T T' c c' hp hp' E ℓ hc _ ih =>
    exact runsInter_progK I m₀ T T' c c' hp hp' E ℓ hc ih
  | progK' P T T' c c' hp hp' E ℓ hc _ ih =>
    exact runsInter_progK' I m₀ T T' c c' hp hp' E ℓ hc ih
  | reveal P T T' f E ℓ hrl hrs hag hcard hG _ ih =>
    exact runsInter_reveal I m₀ T T' f E ℓ hrl hrs hag hcard hG ih

omit [∀ s, Nonempty (D s)] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- The renaming of a basis state. -/
theorem renMap_single (rn : SCls X Z S D M → SCls X Z S D M) (x : SReg X Z S D M) :
    renMap rn (Matrix.single x x 1) = Matrix.single (renS rn x) (renS rn x) 1 := by
  ext b b'
  rw [renMap, LinearMap.sum_apply, Matrix.sum_apply, Finset.sum_eq_single (sCls x)]
  · rw [conj_single_apply]
    simp only [renJ, of_apply, true_and, single_apply]
    by_cases hb : b = renS rn x <;> by_cases hb' : b' = renS rn x <;> simp [hb, hb', eq_comm]
  · intro c _ hc
    rw [conj_single_apply]
    simp [renJ, Ne.symm hc]
  · simp

/-- **Simulated programs have the same laws** against the sampled runtime, from the empty label
and store when the renaming keeps them and they are good. -/
theorem evalDistMap_sampled_eq_of_renSim (m₀ : M) {P : Finset S → Prop} {A : QReg}
    {x y : QuantumComp L (tmplSpec X Z S D M good) Ω A} (h : RenSim rl rs G P x y)
    (hP : P ∅) (hG : G ∅ fun _ ↦ none) (hrl : rl ∅ = ∅)
    (hrs : rs ∅ (fun _ ↦ none) = fun _ ↦ none)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ] (f : (Σ u, Ω u) → γ) :
    (sampledRuntime good m₀).evalDistMap I x ρ f =
      (sampledRuntime good m₀).evalDistMap I y ρ f := by
  have hinit : (renMap (rnOf rl rs)).amplifyLeft A
      (ρ.matrix ⊗ₖ (sampledRuntime good m₀).init.matrix) =
      ρ.matrix ⊗ₖ (sampledRuntime good m₀).init.matrix := by
    have he : renS (rnOf rl rs) ((((Database.empty, Database.empty, Database.empty),
        hwEmpty X Z, ((∅ : Finset S), m₀)), fun _ ↦ none) : SReg X Z S D M) =
        (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, ((∅ : Finset S), m₀)),
          fun _ ↦ none) := by
      show (((_, _, _), _, (rl ∅, m₀)), rs ∅ fun _ ↦ none) = _
      rw [hrl, hrs]
      rfl
    rw [MatrixMap.amplifyLeft_kronecker]
    refine congrArg _ ?_
    simp only [SubState.matrix_basis]
    rw [renMap_single, he]
  have hsupp : SuppOn (fun z : A × SReg X Z S D M ↦ GoodC G P (sCls z.2))
      (ρ.matrix ⊗ₖ (sampledRuntime good m₀).init.matrix) := by
    intro a b hab
    simp only [SubState.matrix_basis, kroneckerMap_apply, single_apply] at hab
    split_ifs at hab with h₁
    · show GoodC G P (sCls a.2) ∧ GoodC G P (sCls b.2)
      rw [← h₁.1, ← h₁.2]
      exact ⟨⟨hP, hG⟩, hP, hG⟩
    · simp at hab
  rw [QuantumRuntime.evalDistMap, QuantumRuntime.evalDistMap]
  congr 1
  funext p
  have ht : ((sampledRuntime good m₀).jointPost I y ρ p).matrix.trace =
      ((sampledRuntime good m₀).jointPost I x ρ p).matrix.trace := by
    rw [QuantumRuntime.matrix_jointPost, QuantumRuntime.matrix_jointPost,
      ← trace_renMap (rnOf rl rs) p.1 (((sampledRuntime good m₀).run I x).branch p
        (ρ.matrix ⊗ₖ (sampledRuntime good m₀).init.matrix)), renSim_branch I m₀ h _ hsupp p,
      hinit]
  rw [ht]

end run

/-! ## leanSPHINCS's renaming of the digest stream -/

section stream

open _root_.Sphincs
open HashSig (HashOutput Message)
open Quantum.Xmss (X Z)

/-- A coordinate of a position or a randomizer. -/
def IsVR : HPos → Prop
  | .val _ => True
  | .rnd _ => True
  | _ => False

/-- **Coordinates of positions and randomizers only**: every reveal and program port of the game
outside the digest policy. -/
def ValRnd (T : Finset HPos) : Prop :=
  ∀ s ∈ T, IsVR s

theorem ValRnd.dig {T : Finset HPos} (hT : ValRnd T) (m : Message) (i : DigestCall) :
    HPos.dig m i ∉ T :=
  fun h ↦ hT _ h

theorem ValRnd.str {T : Finset HPos} (hT : ValRnd T) (j : Fin signatureLimit) (i : DigestCall) :
    HPos.str j i ∉ T :=
  fun h ↦ hT _ h

theorem ValRnd.asg {T : Finset HPos} (hT : ValRnd T) (m : Message) (j : Fin signatureLimit) :
    HPos.asg m j ∉ T :=
  fun h ↦ hT _ h

theorem valRnd_valSet (U : Finset ValPos) : ValRnd (valSet U) := fun s hs ↦ by
  obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hs
  exact trivial

theorem valRnd_rootRnd (msg : Message) : ValRnd {.val rootPos, .rnd msg} := fun s hs ↦ by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl <;> exact trivial

theorem valRnd_single (p : ValPos) : ValRnd {.val p} := fun s hs ↦ by
  rw [Finset.mem_singleton.1 hs]
  exact trivial

/-- At most one mark per message. -/
def OneMark (L : Finset HPos) : Prop :=
  ∀ m j j', HPos.asg m j ∈ L → HPos.asg m j' ∈ L → j = j'

/-- The stream entry marked for `M` in the label `L`, if any. -/
noncomputable def markOf (L : Finset HPos) (msg : Message) : Option (Fin signatureLimit) :=
  @dite _ (∃ j, HPos.asg msg j ∈ L) (Classical.propDecidable _)
    (fun h ↦ some (Classical.choose h)) fun _ ↦ none

theorem markOf_of_mem {L : Finset HPos} (hL : OneMark L) {msg : Message}
    {j : Fin signatureLimit} (h : HPos.asg msg j ∈ L) : markOf L msg = some j := by
  have hex : ∃ j, HPos.asg msg j ∈ L := ⟨j, h⟩
  unfold markOf
  rw [dite_eq_left hex]
  exact congrArg some (hL msg _ _ (Classical.choose_spec hex) h)

theorem markOf_of_free {L : Finset HPos} {msg : Message} (h : ∀ j, HPos.asg msg j ∉ L) :
    markOf L msg = none := by
  unfold markOf
  rw [dite_eq_right fun hex : ∃ j, HPos.asg msg j ∈ L ↦ h _ hex.choose_spec]

theorem mem_of_markOf {L : Finset HPos} {msg : Message} {j : Fin signatureLimit}
    (h : markOf L msg = some j) : HPos.asg msg j ∈ L := by
  by_cases hex : ∃ j, HPos.asg msg j ∈ L
  · unfold markOf at h
    rw [dite_eq_left hex, Option.some.injEq] at h
    exact h ▸ hex.choose_spec
  · exact absurd h (by rw [markOf_of_free fun j hj ↦ hex ⟨j, hj⟩]; simp)

/-- A mark of `M` added by `U` only if `U` marks `M`. -/
theorem markOf_union {L U : Finset HPos} (hL : OneMark (L ∪ U)) {msg : Message}
    (hU : ∀ j, HPos.asg msg j ∉ U) : markOf (L ∪ U) msg = markOf L msg := by
  by_cases hex : ∃ j, HPos.asg msg j ∈ L
  · obtain ⟨j, hj⟩ := hex
    rw [markOf_of_mem hL (Finset.mem_union_left _ hj),
      markOf_of_mem (fun m a b ha hb ↦ hL m a b (Finset.mem_union_left _ ha)
        (Finset.mem_union_left _ hb)) hj]
  · rw [markOf_of_free fun j hj ↦ (Finset.mem_union.1 hj).elim (fun h ↦ hex ⟨j, h⟩) (hU j),
      markOf_of_free fun j hj ↦ hex ⟨j, hj⟩]

/-- **The renamed store**: the `H_msg` outputs of a marked message are its stream entry's; the
stream and the marks are dropped; the values and randomizers are kept. -/
noncomputable def msgStore (L : Finset HPos) (σ : Store XD) : Store XD
  | .val p => σ (.val p)
  | .rnd m => σ (.rnd m)
  | .dig m i => match markOf L m with
    | some j => (σ (.str j i) : Option HashOutput)
    | none => σ (.dig m i)
  | .str _ _ => none
  | .asg _ _ => none

theorem msgStore_dig_some {L : Finset HPos} {σ : Store XD} {m : Message} {j : Fin signatureLimit}
    (h : markOf L m = some j) (i : DigestCall) :
    msgStore L σ (.dig m i) = (σ (.str j i) : Option HashOutput) := by
  simp only [msgStore, h]
  rfl

theorem msgStore_dig_none {L : Finset HPos} {σ : Store XD} {m : Message}
    (h : markOf L m = none) (i : DigestCall) : msgStore L σ (.dig m i) = σ (.dig m i) := by
  simp only [msgStore, h]

theorem msgStore_of_isVR (L : Finset HPos) (σ : Store XD) {s : HPos} (hs : IsVR s) :
    msgStore L σ s = σ s := by
  cases s with
  | val p => rfl
  | rnd m => rfl
  | _ => exact absurd hs id

/-- The coordinates of the renamed label. -/
def InMsg (L : Finset HPos) : HPos → Prop
  | .val p => HPos.val p ∈ L
  | .rnd m => HPos.rnd m ∈ L
  | .dig m i => HPos.dig m i ∈ L ∨ ∃ j, HPos.asg m j ∈ L ∧ HPos.str j i ∈ L
  | .str _ _ => False
  | .asg _ _ => False

/-- The coordinates a label coordinate is renamed to, at most: a mark's `H_msg` outputs. -/
def expandC : HPos → Finset HPos
  | .asg m _ => {.dig m 0, .dig m 1}
  | s => {s}

/-- **The renamed label**: the values and randomizers, the fallback `H_msg` outputs, and the
`H_msg` outputs of the marked messages whose entries are revealed. -/
@[irreducible]
noncomputable def msgLab (L : Finset HPos) : Finset HPos :=
  @Finset.filter _ (InMsg L) (Classical.decPred _) (L.biUnion expandC)

theorem mem_msgLab {L : Finset HPos} {s : HPos} : s ∈ msgLab L ↔ InMsg L s := by
  unfold msgLab
  rw [@Finset.mem_filter _ (InMsg L) (Classical.decPred _)]
  refine and_iff_right_of_imp fun h ↦ Finset.mem_biUnion.2 ?_
  cases s with
  | val p => exact ⟨_, h, Finset.mem_singleton_self _⟩
  | rnd m => exact ⟨_, h, Finset.mem_singleton_self _⟩
  | dig m i =>
    rcases h with h | ⟨j, hj, -⟩
    · exact ⟨_, h, Finset.mem_singleton_self _⟩
    · refine ⟨_, hj, ?_⟩
      rcases digestCall_cases i with rfl | rfl <;> simp [expandC]
  | str _ _ => exact False.elim h
  | asg _ _ => exact False.elim h

theorem mem_msgLab_of_isVR {L : Finset HPos} {s : HPos} (hs : IsVR s) :
    s ∈ msgLab L ↔ s ∈ L := by
  rw [mem_msgLab]
  cases s with
  | val p => exact Iff.rfl
  | rnd m => exact Iff.rfl
  | _ => exact absurd hs id

/-- **The stream invariant** of the `strPol` run's label `L` and store `σ`: the store holds values
only on `L`; each message is marked at most once; an entry is revealed exactly when it is marked;
the marked entries lie below the number of marks; a fallback `H_msg` output is revealed only once
the stream is used up, for an unmarked message. -/
structure StreamInv (L : Finset HPos) (σ : Store XD) : Prop where
  dom : ∀ s, s ∉ L → σ s = none
  one : OneMark L
  str : ∀ j i, HPos.str j i ∈ L ↔ ∃ m, HPos.asg m j ∈ L
  used : ∀ m j, HPos.asg m j ∈ L → j.val < asgCount L
  dig : ∀ m i, HPos.dig m i ∈ L → signatureLimit ≤ asgCount L ∧ ∀ j, HPos.asg m j ∉ L

theorem streamInv_empty : StreamInv ∅ fun _ ↦ none :=
  ⟨fun _ _ ↦ rfl, fun _ _ _ h ↦ absurd h (Finset.notMem_empty _),
    fun _ _ ↦ iff_of_false (Finset.notMem_empty _) fun ⟨_, h⟩ ↦ Finset.notMem_empty _ h,
    fun _ _ h ↦ absurd h (Finset.notMem_empty _), fun _ _ h ↦ absurd h (Finset.notMem_empty _)⟩

theorem msgLab_empty : msgLab ∅ = ∅ := by
  ext s
  rw [mem_msgLab]
  simp only [Finset.notMem_empty, iff_false]
  cases s <;> simp [InMsg]

theorem msgStore_empty : msgStore ∅ (fun _ ↦ none) = fun _ ↦ none := by
  funext s
  cases s with
  | dig m i => rw [msgStore_dig_none (markOf_of_free fun _ h ↦ Finset.notMem_empty _ h)]
  | _ => rfl

/-! ### Reveals of positions and randomizers -/

theorem asgCount_union_noAsg {L U : Finset HPos} (hU : ∀ m j, HPos.asg m j ∉ U) :
    asgCount (L ∪ U) = asgCount L := by
  have hU' : U.filter (fun s ↦ s.isAsg = true) = ∅ := Finset.filter_eq_empty_iff.2 fun s hs ha ↦ by
    cases s with
    | asg m j => exact hU m j hs
    | _ => cases ha
  unfold asgCount
  rw [Finset.filter_union, hU', Finset.union_empty]

theorem oneMark_union_noAsg {L U : Finset HPos} (hL : OneMark L) (hU : ∀ m j, HPos.asg m j ∉ U) :
    OneMark (L ∪ U) := fun m j j' h h' ↦
  hL m j j' ((Finset.mem_union.1 h).resolve_right (hU m j))
    ((Finset.mem_union.1 h').resolve_right (hU m j'))

theorem msgLab_union_vr (L : Finset HPos) {T : Finset HPos} (hT : ValRnd T) :
    msgLab (L ∪ T) = msgLab L ∪ T := by
  ext s
  rw [Finset.mem_union, mem_msgLab, mem_msgLab]
  cases s with
  | val p => exact Finset.mem_union
  | rnd m => exact Finset.mem_union
  | dig m i =>
    simp only [InMsg, Finset.mem_union, hT.dig m i, hT.str, hT.asg, or_false]
  | str j i => simp only [InMsg, false_or, hT.str j i]
  | asg m j => simp only [InMsg, false_or, hT.asg m j]

theorem swapIn_apply_of_notMem {T L : Finset HPos} (w : RevealVals XD T) (σ : Store XD) {s : HPos}
    (hs : s ∉ T) : swapIn T L w σ s = σ s :=
  dite_eq_right fun h ↦ hs h.1

theorem msgStore_swapIn_vr {L T : Finset HPos} {σ : Store XD} (hL : StreamInv L σ)
    (hT : ValRnd T) (w : RevealVals XD T) :
    msgStore (L ∪ T) (swapIn T L w σ) = swapIn T (msgLab L) w (msgStore L σ) := by
  funext s
  cases s with
  | val p =>
    show swapIn T L w σ (.val p) = swapIn T (msgLab L) w (msgStore L σ) (.val p)
    unfold swapIn
    simp only [mem_msgLab_of_isVR (show IsVR (.val p) from trivial)]
    rfl
  | rnd m =>
    show swapIn T L w σ (.rnd m) = swapIn T (msgLab L) w (msgStore L σ) (.rnd m)
    unfold swapIn
    simp only [mem_msgLab_of_isVR (show IsVR (.rnd m) from trivial)]
    rfl
  | dig m i =>
    have hm := markOf_union (oneMark_union_noAsg hL.one hT.asg) (hT.asg m)
    rw [swapIn_apply_of_notMem _ _ (hT.dig m i)]
    rcases h : markOf L m with _ | j
    · rw [msgStore_dig_none (hm.trans h), msgStore_dig_none h,
        swapIn_apply_of_notMem _ _ (hT.dig m i)]
    · rw [msgStore_dig_some (hm.trans h), msgStore_dig_some h,
        swapIn_apply_of_notMem _ _ (hT.str j i)]
  | str j i => exact (swapIn_apply_of_notMem _ _ (hT.str j i)).symm
  | asg m j => exact (swapIn_apply_of_notMem _ _ (hT.asg m j)).symm

theorem agrees_msg_vr {L T : Finset HPos} (σ : Store XD) (hT : ValRnd T) (w : RevealVals XD T) :
    Agrees T (msgLab L) (fill (msgStore L σ)) w ↔ Agrees T L (fill σ) w := by
  refine forall_congr' fun s ↦ ?_
  rw [mem_msgLab_of_isVR (hT _ s.2)]
  unfold fill
  rw [msgStore_of_isVR L σ (hT _ s.2)]

theorem sdiff_msgLab_vr (L : Finset HPos) {T : Finset HPos} (hT : ValRnd T) :
    T \ msgLab L = T \ L := by
  ext s
  simp only [Finset.mem_sdiff]
  exact and_congr_right fun hs ↦ not_congr (mem_msgLab_of_isVR (hT _ hs))

theorem streamInv_swapIn_vr {L T : Finset HPos} {σ : Store XD} (hL : StreamInv L σ)
    (hT : ValRnd T) (w : RevealVals XD T) : StreamInv (L ∪ T) (swapIn T L w σ) where
  dom s hs := by
    rw [swapIn_apply_of_notMem _ _ fun h ↦ hs (Finset.mem_union_right _ h)]
    exact hL.dom s fun h ↦ hs (Finset.mem_union_left _ h)
  one := oneMark_union_noAsg hL.one hT.asg
  str j i := by
    simp only [Finset.mem_union, hT.str j i, or_false, hT.asg, (hL.str j i)]
  used m j h := by
    rw [asgCount_union_noAsg hT.asg]
    exact hL.used m j ((Finset.mem_union.1 h).resolve_right (hT.asg m j))
  dig m i h := by
    rw [asgCount_union_noAsg hT.asg]
    obtain ⟨h₁, h₂⟩ := hL.dig m i ((Finset.mem_union.1 h).resolve_right (hT.dig m i))
    exact ⟨h₁, fun j hj ↦ (Finset.mem_union.1 hj).elim (h₂ j) (hT.asg m j)⟩

/-! ### The digest reveal -/

theorem swapIn_of_subset {T L : Finset HPos} (w : RevealVals XD T) (σ : Store XD) (h : T ⊆ L) :
    swapIn T L w σ = σ :=
  funext fun _ ↦ dite_eq_right fun h' ↦ h'.2 (h h'.1)

theorem swapIn_apply_new {T L : Finset HPos} (w : RevealVals XD T) {σ : Store XD} {s : HPos}
    (hT : s ∈ T) (hL : s ∉ L) (hσ : σ s = none) : swapIn T L w σ s = some (w ⟨s, hT⟩) := by
  unfold swapIn
  rw [dite_eq_left ⟨hT, hL⟩, hσ]
  rfl

theorem swapIn_apply_of_mem {T L : Finset HPos} (w : RevealVals XD T) (σ : Store XD) {s : HPos}
    (hT : s ∈ T) (hL : s ∉ L) : swapIn T L w σ s = swapOpt (w ⟨s, hT⟩) (σ s) :=
  dite_eq_left ⟨hT, hL⟩

theorem swapIn_apply_of_memL {T L : Finset HPos} (w : RevealVals XD T) (σ : Store XD) {s : HPos}
    (hL : s ∈ L) : swapIn T L w σ s = σ s :=
  dite_eq_right fun h ↦ h.2 hL

theorem fill_msgStore_dig_some {L : Finset HPos} (σ : Store XD) {m : Message}
    {j : Fin signatureLimit} (h : markOf L m = some j) (i : DigestCall) :
    fill (msgStore L σ) (.dig m i) = (fill σ (.str j i) : HashOutput) := by
  unfold fill
  rw [msgStore_dig_some h]
  rfl

theorem fill_msgStore_dig_none {L : Finset HPos} (σ : Store XD) {m : Message}
    (h : markOf L m = none) (i : DigestCall) :
    fill (msgStore L σ) (.dig m i) = fill σ (.dig m i) := by
  unfold fill
  rw [msgStore_dig_none h]

/-- The values on `T`, a default value off `T`. -/
noncomputable def extW {T : Finset HPos} (w : RevealVals XD T) : (s : HPos) → XD s :=
  fun s ↦ if h : s ∈ T then w ⟨s, h⟩ else Classical.arbitrary _

theorem extW_of_mem {T : Finset HPos} (w : RevealVals XD T) {s : HPos} (h : s ∈ T) :
    extW w s = w ⟨s, h⟩ :=
  dite_eq_left h

/-- **The values on `T` and on `T'`** in bijection through an involution of the values that reads
`T` from `T'` and `T'` from `T`. -/
noncomputable def valsEquiv (T T' : Finset HPos) (φ : ((s : HPos) → XD s) → (s : HPos) → XD s)
    (hφ : ∀ v, φ (φ v) = v)
    (h₁ : ∀ v v', (∀ s ∈ T', v s = v' s) → ∀ s ∈ T, φ v s = φ v' s)
    (h₂ : ∀ v v', (∀ s ∈ T, v s = v' s) → ∀ s ∈ T', φ v s = φ v' s) :
    RevealVals XD T ≃ RevealVals XD T' where
  toFun w := restrictTo T' (φ (extW w))
  invFun w' := restrictTo T (φ (extW w'))
  left_inv w := funext fun s ↦ by
    show φ (extW (restrictTo T' (φ (extW w)))) s.1 = w s
    rw [h₁ _ (φ (extW w)) (fun s' hs' ↦ extW_of_mem _ hs') s.1 s.2, hφ, extW_of_mem _ s.2]
  right_inv w' := funext fun s ↦ by
    show φ (extW (restrictTo T (φ (extW w')))) s.1 = w' s
    rw [h₂ _ (φ (extW w')) (fun s' hs' ↦ extW_of_mem _ hs') s.1 s.2, hφ, extW_of_mem _ s.2]

/-- **The exchange of a message's `H_msg` outputs and a stream entry's** in the values. -/
def swapSD (j : Fin signatureLimit) (msg : Message) (v : (s : HPos) → XD s) : (s : HPos) → XD s
  | .dig m i => if m = msg then (v (.str j i) : HashOutput) else v (.dig m i)
  | .str j' i => if j' = j then (v (.dig msg i) : HashOutput) else v (.str j' i)
  | s => v s

theorem swapSD_dig (j : Fin signatureLimit) (msg : Message) (v : (s : HPos) → XD s)
    (i : DigestCall) : swapSD j msg v (.dig msg i) = (v (.str j i) : HashOutput) := by
  simp only [swapSD]
  rfl

theorem swapSD_str (j : Fin signatureLimit) (msg : Message) (v : (s : HPos) → XD s)
    (i : DigestCall) : swapSD j msg v (.str j i) = (v (.dig msg i) : HashOutput) := by
  simp only [swapSD]
  rfl

theorem swapSD_swapSD (j : Fin signatureLimit) (msg : Message) (v : (s : HPos) → XD s) :
    swapSD j msg (swapSD j msg v) = v := by
  funext s
  cases s with
  | dig m i =>
    by_cases h : m = msg
    · subst h
      rw [swapSD_dig, swapSD_str]
    · simp [swapSD, h]
  | str j' i =>
    by_cases h : j' = j
    · subst h
      rw [swapSD_str, swapSD_dig]
    · simp [swapSD, h]
  | val p => rfl
  | rnd m => rfl
  | asg m j' => rfl

section entry

variable {T T' : Finset HPos} {msg : Message} {j : Fin signatureLimit}

/-- **The values of a stream entry and of a message's `H_msg` outputs** in bijection. -/
noncomputable def entryEquiv (hT : ∀ s, s ∈ T ↔ s = .str j 0 ∨ s = .str j 1 ∨ s = .asg msg j)
    (hT' : ∀ s, s ∈ T' ↔ s = .dig msg 0 ∨ s = .dig msg 1) : RevealVals XD T ≃ RevealVals XD T' :=
  valsEquiv T T' (swapSD j msg) (swapSD_swapSD j msg)
    (fun v v' hv s hs ↦ by
      rcases (hT s).1 hs with rfl | rfl | rfl
      · rw [swapSD_str, swapSD_str, hv _ ((hT' _).2 (Or.inl rfl))]
      · rw [swapSD_str, swapSD_str, hv _ ((hT' _).2 (Or.inr rfl))]
      · exact Subsingleton.elim (α := Unit) _ _)
    (fun v v' hv s hs ↦ by
      rcases (hT' s).1 hs with rfl | rfl
      · rw [swapSD_dig, swapSD_dig, hv _ ((hT _).2 (Or.inl rfl))]
      · rw [swapSD_dig, swapSD_dig, hv _ ((hT _).2 (Or.inr (Or.inl rfl)))])

theorem str_mem_of_entry (hT : ∀ s, s ∈ T ↔ s = .str j 0 ∨ s = .str j 1 ∨ s = .asg msg j)
    (i : DigestCall) : HPos.str j i ∈ T :=
  (hT _).2 (by rcases digestCall_cases i with rfl | rfl <;> simp)

theorem dig_mem_of_entry (hT' : ∀ s, s ∈ T' ↔ s = .dig msg 0 ∨ s = .dig msg 1) (i : DigestCall) :
    HPos.dig msg i ∈ T' :=
  (hT' _).2 (by rcases digestCall_cases i with rfl | rfl <;> simp)

theorem entryEquiv_dig (hT : ∀ s, s ∈ T ↔ s = .str j 0 ∨ s = .str j 1 ∨ s = .asg msg j)
    (hT' : ∀ s, s ∈ T' ↔ s = .dig msg 0 ∨ s = .dig msg 1) (w : RevealVals XD T) (i : DigestCall)
    (h : HPos.dig msg i ∈ T') :
    entryEquiv hT hT' w ⟨.dig msg i, h⟩ = (w ⟨.str j i, str_mem_of_entry hT i⟩ : HashOutput) := by
  show swapSD j msg (extW w) (.dig msg i) = _
  rw [swapSD_dig, extW_of_mem _ (str_mem_of_entry hT i)]

variable {L₂ : Finset HPos} {σ : Store XD}
  (hT : ∀ s, s ∈ T ↔ s = .str j 0 ∨ s = .str j 1 ∨ s = .asg msg j)
  (hT' : ∀ s, s ∈ T' ↔ s = .dig msg 0 ∨ s = .dig msg 1) (hG : StreamInv L₂ σ)
  (hj : HPos.asg msg j ∈ L₂ ∨ ((∀ j', HPos.asg msg j' ∉ L₂) ∧ j.val = asgCount L₂))

include hT hT' in
theorem entry_mem_iff {s : HPos} :
    (s ∈ T ↔ (∃ i, s = .str j i) ∨ s = .asg msg j) ∧ (s ∈ T' ↔ ∃ i, s = .dig msg i) := by
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_⟩, ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · rcases (hT s).1 h with rfl | rfl | rfl
    exacts [Or.inl ⟨_, rfl⟩, Or.inl ⟨_, rfl⟩, Or.inr rfl]
  · rcases h with ⟨i, rfl⟩ | rfl
    exacts [str_mem_of_entry hT i, (hT _).2 (Or.inr (Or.inr rfl))]
  · rcases (hT' s).1 h with rfl | rfl
    exacts [⟨_, rfl⟩, ⟨_, rfl⟩]
  · obtain ⟨i, rfl⟩ := h
    exact dig_mem_of_entry hT' i

include hT in
theorem entry_asg_mem (m : Message) (j' : Fin signatureLimit) :
    HPos.asg m j' ∈ T ↔ m = msg ∧ j' = j := by
  constructor
  · intro h
    rcases (hT _).1 h with h | h | h
    · cases h
    · cases h
    · exact HPos.asg.inj h
  · rintro ⟨rfl, rfl⟩
    exact (hT _).2 (Or.inr (Or.inr rfl))

include hT in
theorem entry_str_mem (j' : Fin signatureLimit) (i : DigestCall) :
    HPos.str j' i ∈ T ↔ j' = j := by
  constructor
  · intro h
    rcases (hT _).1 h with h | h | h
    · exact (HPos.str.inj h).1
    · exact (HPos.str.inj h).1
    · cases h
  · rintro rfl
    exact str_mem_of_entry hT i

include hT' in
theorem entry_dig_mem' (m : Message) (i : DigestCall) : HPos.dig m i ∈ T' ↔ m = msg := by
  constructor
  · intro h
    rcases (hT' _).1 h with h | h <;> exact (HPos.dig.inj h).1
  · rintro rfl
    exact dig_mem_of_entry hT' i

include hT in
theorem entry_dig_notMem (m : Message) (i : DigestCall) : HPos.dig m i ∉ T := fun h ↦ by
  rcases (hT _).1 h with h | h | h <;> cases h

include hT hG in
theorem entry_marked_sub (hm : HPos.asg msg j ∈ L₂) : T ⊆ L₂ := fun s hs ↦ by
  rcases (hT s).1 hs with rfl | rfl | rfl
  · exact (hG.str j 0).2 ⟨msg, hm⟩
  · exact (hG.str j 1).2 ⟨msg, hm⟩
  · exact hm

include hT' hG in
theorem entry_marked_sub' (hm : HPos.asg msg j ∈ L₂) : T' ⊆ msgLab L₂ := fun s hs ↦ by
  rcases (hT' s).1 hs with rfl | rfl <;>
    exact mem_msgLab.2 (Or.inr ⟨j, hm, (hG.str j _).2 ⟨msg, hm⟩⟩)

include hT hG in
theorem entry_new_disj (hfree : ∀ j', HPos.asg msg j' ∉ L₂) (hc : j.val = asgCount L₂) :
    ∀ s ∈ T, s ∉ L₂ := fun s hs ↦ by
  rcases (hT s).1 hs with rfl | rfl | rfl
  · intro h
    obtain ⟨m', hm'⟩ := (hG.str j 0).1 h
    exact absurd (hG.used m' j hm') (by omega)
  · intro h
    obtain ⟨m', hm'⟩ := (hG.str j 1).1 h
    exact absurd (hG.used m' j hm') (by omega)
  · exact hfree j

include hT' hG in
theorem entry_new_disj' (hfree : ∀ j', HPos.asg msg j' ∉ L₂) (hc : j.val = asgCount L₂) :
    ∀ s ∈ T', s ∉ msgLab L₂ := fun s hs h ↦ by
  rcases (hT' s).1 hs with rfl | rfl <;>
    exact Or.elim (mem_msgLab.1 h) (fun h ↦ absurd (hG.dig msg _ h).1 (by have := j.isLt; omega))
      fun ⟨j', ha, _⟩ ↦ hfree j' ha

include hT hG in
theorem oneMark_union_entry (hfree : ∀ j', HPos.asg msg j' ∉ L₂) : OneMark (L₂ ∪ T) :=
  fun m a b ha hb ↦ by
    rcases Finset.mem_union.1 ha with ha | ha <;> rcases Finset.mem_union.1 hb with hb | hb
    · exact hG.one m a b ha hb
    · obtain ⟨rfl, -⟩ := (entry_asg_mem hT m b).1 hb
      exact absurd ha (hfree a)
    · obtain ⟨rfl, -⟩ := (entry_asg_mem hT m a).1 ha
      exact absurd hb (hfree b)
    · exact ((entry_asg_mem hT m a).1 ha).2.trans ((entry_asg_mem hT m b).1 hb).2.symm

include hT in
theorem asgCount_union_entry (hfree : HPos.asg msg j ∉ L₂) :
    asgCount (L₂ ∪ T) = asgCount L₂ + 1 := by
  have hf : T.filter (fun s ↦ s.isAsg = true) = {HPos.asg msg j} := by
    ext s
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, ha⟩
      rcases (hT s).1 hs with rfl | rfl | rfl
      · cases ha
      · cases ha
      · rfl
    · rintro rfl
      exact ⟨(hT _).2 (Or.inr (Or.inr rfl)), rfl⟩
  unfold asgCount
  rw [Finset.filter_union, hf, Finset.card_union_of_disjoint
    (Finset.disjoint_singleton_right.2 fun h ↦ hfree (Finset.mem_filter.1 h).1),
    Finset.card_singleton]

include hT hT' hG hj in
/-- The digest reveal grows the renamed label by the message's `H_msg` outputs. -/
theorem msgLab_union_entry : msgLab (L₂ ∪ T) = msgLab L₂ ∪ T' := by
  ext s
  rw [Finset.mem_union, mem_msgLab, mem_msgLab]
  cases s with
  | val p =>
    show HPos.val p ∈ L₂ ∪ T ↔ HPos.val p ∈ L₂ ∨ HPos.val p ∈ T'
    rw [Finset.mem_union]
    refine or_congr_right (iff_of_false (fun h ↦ ?_) fun h ↦ ?_)
    · rcases (hT _).1 h with h | h | h <;> cases h
    · rcases (hT' _).1 h with h | h <;> cases h
  | rnd m =>
    show HPos.rnd m ∈ L₂ ∪ T ↔ HPos.rnd m ∈ L₂ ∨ HPos.rnd m ∈ T'
    rw [Finset.mem_union]
    refine or_congr_right (iff_of_false (fun h ↦ ?_) fun h ↦ ?_)
    · rcases (hT _).1 h with h | h | h <;> cases h
    · rcases (hT' _).1 h with h | h <;> cases h
  | str j' i =>
    refine iff_of_false id fun h ↦ h.elim id fun h ↦ ?_
    rcases (hT' _).1 h with h | h <;> cases h
  | asg m j' =>
    refine iff_of_false id fun h ↦ h.elim id fun h ↦ ?_
    rcases (hT' _).1 h with h | h <;> cases h
  | dig m i =>
    show (HPos.dig m i ∈ L₂ ∪ T ∨ ∃ j', HPos.asg m j' ∈ L₂ ∪ T ∧ HPos.str j' i ∈ L₂ ∪ T) ↔
      (HPos.dig m i ∈ L₂ ∨ ∃ j', HPos.asg m j' ∈ L₂ ∧ HPos.str j' i ∈ L₂) ∨ HPos.dig m i ∈ T'
    rw [entry_dig_mem' hT']
    constructor
    · rintro (h | ⟨j', ha, hs⟩)
      · exact Or.inl (Or.inl ((Finset.mem_union.1 h).resolve_right (entry_dig_notMem hT m i)))
      · rcases Finset.mem_union.1 ha with ha | ha
        · rcases Finset.mem_union.1 hs with hs | hs
          · exact Or.inl (Or.inr ⟨j', ha, hs⟩)
          · obtain rfl := (entry_str_mem hT j' i).1 hs
            rcases hj with hj | ⟨-, hc⟩
            · exact Or.inl (Or.inr ⟨_, ha, (hG.str _ i).2 ⟨m, ha⟩⟩)
            · exact absurd (hG.used m _ ha) (by omega)
        · exact Or.inr ((entry_asg_mem hT m j').1 ha).1
    · rintro ((h | ⟨j', ha, hs⟩) | hm)
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr ⟨j', Finset.mem_union_left _ ha, Finset.mem_union_left _ hs⟩
      · exact Or.inr ⟨j, Finset.mem_union_right _ ((entry_asg_mem hT m j).2 ⟨hm, rfl⟩),
          Finset.mem_union_right _ (str_mem_of_entry hT i)⟩

include hT hT' hG hj in
/-- The digest reveal and the renaming of the stores. -/
theorem msgStore_swapIn_entry (w : RevealVals XD T) :
    msgStore (L₂ ∪ T) (swapIn T L₂ w σ) =
      swapIn T' (msgLab L₂) (entryEquiv hT hT' w) (msgStore L₂ σ) := by
  rcases hj with hj | ⟨hfree, hc⟩
  · rw [Finset.union_eq_left.2 (entry_marked_sub hT hG hj),
      swapIn_of_subset _ _ (entry_marked_sub hT hG hj),
      swapIn_of_subset _ _ (entry_marked_sub' hT' hG hj)]
  have hone := oneMark_union_entry hT hG hfree
  have hnT' : ∀ {s : HPos}, (∀ i, s ≠ .dig msg i) → s ∉ T' := fun hs h ↦ by
    rcases (hT' _).1 h with h | h
    exacts [hs 0 h, hs 1 h]
  funext s
  cases s with
  | val p =>
    show swapIn T L₂ w σ (.val p) = _
    rw [swapIn_apply_of_notMem _ _ (fun h ↦ by rcases (hT _).1 h with h | h | h <;> cases h),
      swapIn_apply_of_notMem _ _ (hnT' fun _ h ↦ by cases h)]
    rfl
  | rnd m =>
    show swapIn T L₂ w σ (.rnd m) = _
    rw [swapIn_apply_of_notMem _ _ (fun h ↦ by rcases (hT _).1 h with h | h | h <;> cases h),
      swapIn_apply_of_notMem _ _ (hnT' fun _ h ↦ by cases h)]
    rfl
  | str j' i => exact (swapIn_apply_of_notMem _ _ (hnT' fun _ h ↦ by cases h)).symm
  | asg m j' => exact (swapIn_apply_of_notMem _ _ (hnT' fun _ h ↦ by cases h)).symm
  | dig m i =>
    by_cases hm : m = msg
    · subst hm
      have hsL : HPos.str j i ∉ L₂ := entry_new_disj hT hG hfree hc _ (str_mem_of_entry hT i)
      have hdM : HPos.dig m i ∉ msgLab L₂ :=
        entry_new_disj' hT' hG hfree hc _ (dig_mem_of_entry hT' i)
      have hdL : HPos.dig m i ∉ L₂ := fun h ↦ hdM (mem_msgLab.2 (Or.inl h))
      rw [msgStore_dig_some (markOf_of_mem hone
          (Finset.mem_union_right _ ((entry_asg_mem hT _ _).2 ⟨rfl, rfl⟩))),
        swapIn_apply_new w (str_mem_of_entry hT i) hsL (hG.dom _ hsL),
        swapIn_apply_new _ (dig_mem_of_entry hT' i) hdM
          (by rw [msgStore_dig_none (markOf_of_free hfree)]; exact hG.dom _ hdL),
        entryEquiv_dig]
      rfl
    · have hmk := markOf_union hone (fun j' h ↦ hm ((entry_asg_mem hT m j').1 h).1)
      rw [swapIn_apply_of_notMem _ _ fun h ↦ hm ((entry_dig_mem' hT' m i).1 h)]
      rcases h : markOf L₂ m with _ | j'
      · rw [msgStore_dig_none (hmk.trans h), msgStore_dig_none h,
          swapIn_apply_of_notMem _ _ (entry_dig_notMem hT m i)]
      · have hj' : j' ≠ j := fun e ↦ by
          subst e
          exact absurd (hG.used m _ (mem_of_markOf h)) (by omega)
        rw [msgStore_dig_some (hmk.trans h), msgStore_dig_some h,
          swapIn_apply_of_notMem _ _ fun h' ↦ hj' ((entry_str_mem hT j' i).1 h')]

include hT hT' hG hj in
/-- The digest reveal agrees with the store exactly when its renaming agrees with the renamed
store. -/
theorem agrees_entry (w : RevealVals XD T) :
    Agrees T' (msgLab L₂) (fill (msgStore L₂ σ)) (entryEquiv hT hT' w) ↔
      Agrees T L₂ (fill σ) w := by
  rcases hj with hj | ⟨hfree, hc⟩
  · have hmk : markOf L₂ msg = some j := markOf_of_mem hG.one hj
    constructor
    · rintro hA ⟨s, hs⟩ -
      rcases (hT s).1 hs with rfl | rfl | rfl
      · have := hA ⟨_, dig_mem_of_entry hT' 0⟩
          (entry_marked_sub' hT' hG hj (dig_mem_of_entry hT' 0))
        rw [entryEquiv_dig, fill_msgStore_dig_some σ hmk] at this
        exact this
      · have := hA ⟨_, dig_mem_of_entry hT' 1⟩
          (entry_marked_sub' hT' hG hj (dig_mem_of_entry hT' 1))
        rw [entryEquiv_dig, fill_msgStore_dig_some σ hmk] at this
        exact this
      · exact Subsingleton.elim (α := Unit) _ _
    · rintro hA ⟨s, hs⟩ -
      obtain ⟨i, rfl⟩ := (entry_mem_iff hT hT').2.1 hs
      rw [entryEquiv_dig, fill_msgStore_dig_some σ hmk]
      exact hA ⟨_, str_mem_of_entry hT i⟩ (entry_marked_sub hT hG hj (str_mem_of_entry hT i))
  · exact iff_of_true (fun s hs ↦ absurd hs (entry_new_disj' hT' hG hfree hc s.1 s.2))
      fun s hs ↦ absurd hs (entry_new_disj hT hG hfree hc s.1 s.2)

include hT hT' hG hj in
/-- The digest reveal samples as many new values as its renaming. -/
theorem card_entry :
    Fintype.card (RevealVals XD (T' \ msgLab L₂)) = Fintype.card (RevealVals XD (T \ L₂)) := by
  rcases hj with hj | ⟨hfree, hc⟩
  · rw [Finset.sdiff_eq_empty_iff_subset.2 (entry_marked_sub' hT' hG hj),
      Finset.sdiff_eq_empty_iff_subset.2 (entry_marked_sub hT hG hj)]
  · rw [Finset.sdiff_eq_self_of_disjoint
        (Finset.disjoint_left.2 (entry_new_disj' hT' hG hfree hc)),
      Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_left.2 (entry_new_disj hT hG hfree hc))]
    exact (Fintype.card_congr (entryEquiv hT hT')).symm

include hT hG hj in
/-- The digest reveal keeps the stream invariant. -/
theorem streamInv_entry (w : RevealVals XD T) : StreamInv (L₂ ∪ T) (swapIn T L₂ w σ) := by
  rcases hj with hj | ⟨hfree, hc⟩
  · rw [Finset.union_eq_left.2 (entry_marked_sub hT hG hj),
      swapIn_of_subset _ _ (entry_marked_sub hT hG hj)]
    exact hG
  have hcount := asgCount_union_entry hT (hfree j)
  refine ⟨fun s hs ↦ ?_, oneMark_union_entry hT hG hfree, fun j' i ↦ ?_, fun m j' h ↦ ?_,
    fun m i h ↦ ?_⟩
  · rw [swapIn_apply_of_notMem _ _ fun h ↦ hs (Finset.mem_union_right _ h)]
    exact hG.dom s fun h ↦ hs (Finset.mem_union_left _ h)
  · rw [Finset.mem_union, entry_str_mem hT]
    constructor
    · rintro (h | rfl)
      · obtain ⟨m, hm⟩ := (hG.str j' i).1 h
        exact ⟨m, Finset.mem_union_left _ hm⟩
      · exact ⟨msg, Finset.mem_union_right _ ((entry_asg_mem hT _ _).2 ⟨rfl, rfl⟩)⟩
    · rintro ⟨m, hm⟩
      rcases Finset.mem_union.1 hm with hm | hm
      · exact Or.inl ((hG.str j' i).2 ⟨m, hm⟩)
      · exact Or.inr ((entry_asg_mem hT m j').1 hm).2
  · rw [hcount]
    rcases Finset.mem_union.1 h with h | h
    · have := hG.used m j' h
      omega
    · obtain ⟨-, rfl⟩ := (entry_asg_mem hT m j').1 h
      omega
  · have hd := (Finset.mem_union.1 h).resolve_right (entry_dig_notMem hT m i)
    exact absurd (hG.dig m i hd).1 (by have := j.isLt; omega)

end entry

section fallback

variable {T T' : Finset HPos} {msg : Message}

/-- The values of a fallback digest reveal, identically. -/
noncomputable def fallEquiv (hT : ∀ s, s ∈ T ↔ s = .dig msg 0 ∨ s = .dig msg 1)
    (hT' : ∀ s, s ∈ T' ↔ s = .dig msg 0 ∨ s = .dig msg 1) : RevealVals XD T ≃ RevealVals XD T' :=
  valsEquiv T T' id (fun _ ↦ rfl) (fun _ _ hv s hs ↦ hv s ((hT' s).2 ((hT s).1 hs)))
    (fun _ _ hv s hs ↦ hv s ((hT s).2 ((hT' s).1 hs)))

theorem fallEquiv_apply (hT : ∀ s, s ∈ T ↔ s = .dig msg 0 ∨ s = .dig msg 1)
    (hT' : ∀ s, s ∈ T' ↔ s = .dig msg 0 ∨ s = .dig msg 1) (w : RevealVals XD T) (s : HPos)
    (h : s ∈ T') : fallEquiv hT hT' w ⟨s, h⟩ = w ⟨s, (hT s).2 ((hT' s).1 h)⟩ :=
  extW_of_mem w _

variable {L₂ : Finset HPos} {σ : Store XD}
  (hT : ∀ s, s ∈ T ↔ s = .dig msg 0 ∨ s = .dig msg 1)
  (hT' : ∀ s, s ∈ T' ↔ s = .dig msg 0 ∨ s = .dig msg 1) (hG : StreamInv L₂ σ)
  (hfree : ∀ j, HPos.asg msg j ∉ L₂) (hN : signatureLimit ≤ asgCount L₂)

include hT in
theorem fall_asg_notMem (m : Message) (j : Fin signatureLimit) : HPos.asg m j ∉ T := fun h ↦ by
  rcases (hT _).1 h with h | h <;> cases h

include hT in
theorem fall_str_notMem (j : Fin signatureLimit) (i : DigestCall) : HPos.str j i ∉ T := fun h ↦ by
  rcases (hT _).1 h with h | h <;> cases h

include hT in
theorem fall_dig_mem (m : Message) (i : DigestCall) : HPos.dig m i ∈ T ↔ m = msg := by
  constructor
  · intro h
    rcases (hT _).1 h with h | h <;> exact (HPos.dig.inj h).1
  · rintro rfl
    exact (hT _).2 (by rcases digestCall_cases i with rfl | rfl <;> simp)

include hfree in
theorem fall_mem_msgLab (i : DigestCall) : HPos.dig msg i ∈ msgLab L₂ ↔ HPos.dig msg i ∈ L₂ :=
  ⟨fun h ↦ Or.elim (mem_msgLab.1 h) id fun ⟨j', ha, _⟩ ↦ absurd ha (hfree j'),
    fun h ↦ mem_msgLab.2 (Or.inl h)⟩

include hT hT' in
/-- The fallback reveal grows the renamed label by the same `H_msg` outputs. -/
theorem msgLab_union_fall : msgLab (L₂ ∪ T) = msgLab L₂ ∪ T' := by
  ext s
  rw [Finset.mem_union, mem_msgLab, mem_msgLab]
  cases s with
  | val p =>
    show HPos.val p ∈ L₂ ∪ T ↔ HPos.val p ∈ L₂ ∨ HPos.val p ∈ T'
    rw [Finset.mem_union]
    refine or_congr_right (iff_of_false (fun h ↦ ?_) fun h ↦ ?_)
    · rcases (hT _).1 h with h | h <;> cases h
    · rcases (hT' _).1 h with h | h <;> cases h
  | rnd m =>
    show HPos.rnd m ∈ L₂ ∪ T ↔ HPos.rnd m ∈ L₂ ∨ HPos.rnd m ∈ T'
    rw [Finset.mem_union]
    refine or_congr_right (iff_of_false (fun h ↦ ?_) fun h ↦ ?_)
    · rcases (hT _).1 h with h | h <;> cases h
    · rcases (hT' _).1 h with h | h <;> cases h
  | str j' i =>
    refine iff_of_false id fun h ↦ h.elim id fun h ↦ ?_
    rcases (hT' _).1 h with h | h <;> cases h
  | asg m j' =>
    refine iff_of_false id fun h ↦ h.elim id fun h ↦ ?_
    rcases (hT' _).1 h with h | h <;> cases h
  | dig m i =>
    show (HPos.dig m i ∈ L₂ ∪ T ∨ ∃ j', HPos.asg m j' ∈ L₂ ∪ T ∧ HPos.str j' i ∈ L₂ ∪ T) ↔
      (HPos.dig m i ∈ L₂ ∨ ∃ j', HPos.asg m j' ∈ L₂ ∧ HPos.str j' i ∈ L₂) ∨ HPos.dig m i ∈ T'
    have hTT : HPos.dig m i ∈ T ↔ HPos.dig m i ∈ T' := by rw [hT, hT']
    simp only [Finset.mem_union, fall_asg_notMem hT, fall_str_notMem hT, or_false, hTT]
    exact or_right_comm

include hT hT' hG hfree in
/-- The fallback reveal and the renaming of the stores. -/
theorem msgStore_swapIn_fall (w : RevealVals XD T) :
    msgStore (L₂ ∪ T) (swapIn T L₂ w σ) =
      swapIn T' (msgLab L₂) (fallEquiv hT hT' w) (msgStore L₂ σ) := by
  have hone := oneMark_union_noAsg hG.one (fall_asg_notMem hT)
  have hnT' : ∀ {s : HPos}, (∀ i, s ≠ .dig msg i) → s ∉ T' := fun hs h ↦ by
    rcases (hT' _).1 h with h | h
    exacts [hs 0 h, hs 1 h]
  funext s
  cases s with
  | val p =>
    show swapIn T L₂ w σ (.val p) = _
    rw [swapIn_apply_of_notMem _ _ (fun h ↦ by rcases (hT _).1 h with h | h <;> cases h),
      swapIn_apply_of_notMem _ _ (hnT' fun _ h ↦ by cases h)]
    rfl
  | rnd m =>
    show swapIn T L₂ w σ (.rnd m) = _
    rw [swapIn_apply_of_notMem _ _ (fun h ↦ by rcases (hT _).1 h with h | h <;> cases h),
      swapIn_apply_of_notMem _ _ (hnT' fun _ h ↦ by cases h)]
    rfl
  | str j' i => exact (swapIn_apply_of_notMem _ _ (hnT' fun _ h ↦ by cases h)).symm
  | asg m j' => exact (swapIn_apply_of_notMem _ _ (hnT' fun _ h ↦ by cases h)).symm
  | dig m i =>
    have hmk := markOf_union hone (fall_asg_notMem hT m)
    by_cases hm : m = msg
    · subst hm
      have hf : markOf L₂ m = none := markOf_of_free hfree
      have hdT := (fall_dig_mem hT m i).2 rfl
      have hdT' : HPos.dig m i ∈ T' := (hT' _).2 ((hT _).1 hdT)
      rw [msgStore_dig_none (hmk.trans hf)]
      by_cases hd : HPos.dig m i ∈ L₂
      · rw [swapIn_apply_of_memL _ _ hd, swapIn_apply_of_memL _ _ ((fall_mem_msgLab hfree i).2 hd),
          msgStore_dig_none hf]
      · rw [swapIn_apply_of_mem _ _ hdT hd,
          swapIn_apply_of_mem _ _ hdT' fun h ↦ hd ((fall_mem_msgLab hfree i).1 h),
          msgStore_dig_none hf, fallEquiv_apply]
    · have hdT : HPos.dig m i ∉ T := fun h ↦ hm ((fall_dig_mem hT m i).1 h)
      rw [swapIn_apply_of_notMem _ _ fun h ↦ hdT ((hT _).2 ((hT' _).1 h))]
      rcases h : markOf L₂ m with _ | j'
      · rw [msgStore_dig_none (hmk.trans h), msgStore_dig_none h,
          swapIn_apply_of_notMem _ _ hdT]
      · rw [msgStore_dig_some (hmk.trans h), msgStore_dig_some h,
          swapIn_apply_of_notMem _ _ (fall_str_notMem hT j' i)]

include hT hT' hfree in
theorem agrees_fall (w : RevealVals XD T) :
    Agrees T' (msgLab L₂) (fill (msgStore L₂ σ)) (fallEquiv hT hT' w) ↔
      Agrees T L₂ (fill σ) w := by
  have hmk : markOf L₂ msg = none := markOf_of_free hfree
  have hdig : ∀ {s : HPos}, s ∈ T → ∃ i, s = .dig msg i := fun hs ↦ by
    rcases (hT _).1 hs with rfl | rfl
    exacts [⟨_, rfl⟩, ⟨_, rfl⟩]
  constructor
  · rintro hA ⟨s, hs⟩ hsL
    obtain ⟨i, rfl⟩ := hdig hs
    have := hA ⟨_, (hT' _).2 ((hT _).1 hs)⟩ ((fall_mem_msgLab hfree i).2 hsL)
    rw [fallEquiv_apply, fill_msgStore_dig_none σ hmk] at this
    exact this
  · rintro hA ⟨s, hs⟩ hsL
    obtain ⟨i, rfl⟩ := hdig ((hT _).2 ((hT' _).1 hs))
    rw [fallEquiv_apply, fill_msgStore_dig_none σ hmk]
    exact hA _ ((fall_mem_msgLab hfree i).1 hsL)

include hT hT' hfree in
theorem card_fall :
    Fintype.card (RevealVals XD (T' \ msgLab L₂)) = Fintype.card (RevealVals XD (T \ L₂)) := by
  have h : T' \ msgLab L₂ = T \ L₂ := by
    ext s
    rw [Finset.mem_sdiff, Finset.mem_sdiff, hT, hT']
    refine and_congr_right fun hs ↦ not_congr ?_
    rcases hs with rfl | rfl
    exacts [fall_mem_msgLab hfree 0, fall_mem_msgLab hfree 1]
  rw [h]

include hT hG hfree hN in
theorem streamInv_fall (w : RevealVals XD T) : StreamInv (L₂ ∪ T) (swapIn T L₂ w σ) := by
  refine ⟨fun s hs ↦ ?_, oneMark_union_noAsg hG.one (fall_asg_notMem hT), fun j' i ↦ ?_,
    fun m j' h ↦ ?_, fun m i h ↦ ?_⟩
  · rw [swapIn_apply_of_notMem _ _ fun h ↦ hs (Finset.mem_union_right _ h)]
    exact hG.dom s fun h ↦ hs (Finset.mem_union_left _ h)
  · simp only [Finset.mem_union, fall_str_notMem hT, fall_asg_notMem hT, or_false]
    exact hG.str j' i
  · rw [asgCount_union_noAsg (fall_asg_notMem hT)]
    exact hG.used m j' ((Finset.mem_union.1 h).resolve_right (fall_asg_notMem hT m j'))
  · rw [asgCount_union_noAsg (fall_asg_notMem hT)]
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨h₁, h₂⟩ := hG.dig m i h
      exact ⟨h₁, fun j hj ↦ (Finset.mem_union.1 hj).elim (h₂ j) (fall_asg_notMem hT m j)⟩
    · obtain rfl := (fall_dig_mem hT m i).1 h
      exact ⟨hN, fun j hj ↦ (Finset.mem_union.1 hj).elim (hfree j) (fall_asg_notMem hT m j)⟩

end fallback

/-! ### The digest policies -/

theorem strPolOut_some {L : Finset HPos} {msg : Message} {j : Fin signatureLimit}
    (hs : streamIdx L msg = some j) (i : DigestCall) : strPol.out L msg i = .str j i := by
  show (match streamIdx L msg with
    | some j => HPos.str j i
    | none => .dig msg i) = _
  rw [hs]

theorem strPolMarks_some {L : Finset HPos} {msg : Message} {j : Fin signatureLimit}
    (hs : streamIdx L msg = some j) : strPol.marks L msg = {.asg msg j} := by
  show (match streamIdx L msg with
    | some j => ({HPos.asg msg j} : Finset HPos)
    | none => ∅) = _
  rw [hs]

theorem strPolOut_none {L : Finset HPos} {msg : Message} (hs : streamIdx L msg = none)
    (i : DigestCall) : strPol.out L msg i = .dig msg i := by
  show (match streamIdx L msg with
    | some j => HPos.str j i
    | none => .dig msg i) = _
  rw [hs]

theorem strPolMarks_none {L : Finset HPos} {msg : Message} (hs : streamIdx L msg = none) :
    strPol.marks L msg = ∅ := by
  show (match streamIdx L msg with
    | some j => ({HPos.asg msg j} : Finset HPos)
    | none => ∅) = _
  rw [hs]

theorem mem_strNeed_some {L : Finset HPos} {msg : Message} {j : Fin signatureLimit}
    (hs : streamIdx L msg = some j) (s : HPos) :
    s ∈ strPol.need L msg ↔ s = .str j 0 ∨ s = .str j 1 ∨ s = .asg msg j := by
  rw [DigestPolicy.need, strPolOut_some hs, strPolOut_some hs, strPolMarks_some hs]
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem mem_strNeed_none {L : Finset HPos} {msg : Message} (hs : streamIdx L msg = none)
    (s : HPos) : s ∈ strPol.need L msg ↔ s = .dig msg 0 ∨ s = .dig msg 1 := by
  rw [DigestPolicy.need, strPolOut_none hs, strPolOut_none hs, strPolMarks_none hs]
  simp only [Finset.mem_insert, Finset.notMem_empty, or_false]

theorem mem_msgNeed (L : Finset HPos) (msg : Message) (s : HPos) :
    s ∈ msgPol.need L msg ↔ s = .dig msg 0 ∨ s = .dig msg 1 := by
  show s ∈ insert (HPos.dig msg 0) (insert (HPos.dig msg 1) (∅ : Finset HPos)) ↔ _
  simp only [Finset.mem_insert, Finset.notMem_empty, or_false]

/-- **A message with a stream entry**, after a reveal without marks: marked by it, or unmarked
with the entry the number of marks. -/
theorem streamIdx_some_facts {L U : Finset HPos} {msg : Message} {j : Fin signatureLimit}
    (hs : streamIdx L msg = some j) (hU : ∀ m j, HPos.asg m j ∉ U) :
    HPos.asg msg j ∈ L ∪ U ∨ ((∀ j', HPos.asg msg j' ∉ L ∪ U) ∧ j.val = asgCount (L ∪ U)) := by
  rw [asgCount_union_noAsg hU]
  unfold streamIdx at hs
  by_cases hex : ∃ j', HPos.asg msg j' ∈ L
  · rw [dite_eq_left hex, Option.some.injEq] at hs
    exact Or.inl (Finset.mem_union_left _ (hs ▸ hex.choose_spec))
  · rw [dite_eq_right hex] at hs
    split_ifs at hs with hc
    · rw [Option.some.injEq] at hs
      refine Or.inr ⟨fun j' h ↦ (Finset.mem_union.1 h).elim (fun h ↦ hex ⟨j', h⟩) (hU msg j'), ?_⟩
      rw [← hs]

/-- **A message past the stream**, after a reveal without marks: unmarked, the stream used up. -/
theorem streamIdx_none_facts {L U : Finset HPos} {msg : Message} (hs : streamIdx L msg = none)
    (hU : ∀ m j, HPos.asg m j ∉ U) :
    (∀ j, HPos.asg msg j ∉ L ∪ U) ∧ signatureLimit ≤ asgCount (L ∪ U) := by
  rw [asgCount_union_noAsg hU]
  unfold streamIdx at hs
  by_cases hex : ∃ j', HPos.asg msg j' ∈ L
  · rw [dite_eq_left hex] at hs
    cases hs
  · rw [dite_eq_right hex] at hs
    split_ifs at hs with hc
    exact ⟨fun j' h ↦ (Finset.mem_union.1 h).elim (fun h ↦ hex ⟨j', h⟩) (hU msg j'), by omega⟩

variable (M : Type)

/-- **A reveal of positions and randomizers** is simulated by itself. -/
theorem renSim_revealThen_vr {P : Finset HPos → Prop} {B C : QReg} {α : Type}
    {T : Finset HPos} (hT : ValRnd T)
    {k k' : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B C α}
    (h : ∀ w L₁ m, P L₁ → RenSim msgLab msgStore StreamInv (fun L' ↦ L' = L₁ ∪ T)
      (k (w, (L₁, m))) (k' (w, (msgLab L₁, m)))) :
    RenSim msgLab msgStore StreamInv P (revealThen goodAll T k) (revealThen goodAll T k') :=
  renSim_revealThen T T (fun _ ↦ Equiv.refl _) (fun L₁ _ _ _ ↦ msgLab_union_vr L₁ hT)
    (fun _ _ w _ hG _ ↦ msgStore_swapIn_vr hG hT w) (fun _ σ w _ _ ↦ agrees_msg_vr σ hT w)
    (fun L₁ _ _ _ ↦ by rw [sdiff_msgLab_vr L₁ hT]) (fun _ _ w _ hG _ ↦ streamInv_swapIn_vr hG hT w)
    h

theorem progPorts_nil_bind (B : QReg) {C : QReg} {α : Type} (k : Unit → QComp (SSpec M) B C α) :
    (progPorts M B []).bind k = k () :=
  rfl

theorem progPorts_cons_bind (B : QReg) {C : QReg} {α : Type} (p : LazyProg X Z HPos XD)
    (ps : List (LazyProg X Z HPos XD)) (k : Unit → QComp (SSpec M) B C α) :
    (progPorts M B (p :: ps)).bind k = progThen p trivial ((progPorts M B ps).bind k) :=
  rfl

/-- **Program ports simulated pairwise.** -/
theorem renSim_progPorts_bind {P : Finset HPos → Prop} {B C : QReg} {α : Type}
    {ps ps' : List (LazyProg X Z HPos XD)}
    (h : List.Forall₂ (PortSim msgStore StreamInv P) ps ps')
    {k k' : Unit → QComp (SSpec M) B C α}
    (hk : RenSim msgLab msgStore StreamInv P (k ()) (k' ())) :
    RenSim msgLab msgStore StreamInv P ((progPorts M B ps).bind k)
      ((progPorts M B ps').bind k') := by
  induction h with
  | nil =>
    rw [progPorts_nil_bind, progPorts_nil_bind]
    exact hk
  | cons hpp _ ih =>
    rw [progPorts_cons_bind, progPorts_cons_bind]
    exact renSim_progThen hpp trivial trivial ih

/-- Program ports at positions and randomizers are simulated by themselves. -/
theorem portSim_self {P : Finset HPos → Prop} {p : LazyProg X Z HPos XD} (hp : ValRnd p.need) :
    PortSim msgStore StreamInv P p p := by
  have key : ∀ {T : Finset HPos}, ValRnd T → ∀ L σ,
      restrictTo T (fill σ) = restrictTo T (fill (msgStore L σ)) := fun hT L σ ↦
    funext fun s ↦ by
      show fill σ s.1 = fill (msgStore L σ) s.1
      unfold fill
      rw [msgStore_of_isVR L σ (hT _ s.2)]
  cases p with
  | programH T c => exact .progH T T c c fun L σ _ _ ↦ congrArg c (key hp L σ)
  | programK T c => exact .progK T T c c fun L σ _ _ ↦ congrArg c (key hp L σ)
  | programK' T c => exact .progK' T T c c fun L σ _ _ ↦ congrArg c (key hp L σ)

variable (pub : Pub)

/-- The honest paths of slots are simulated by themselves. -/
theorem renSim_progSlots_bind {P : Finset HPos → Prop} {B C : QReg} {α : Type} (ss : List Slot)
    {k k' : Unit → QComp (SSpec M) B C α}
    (hk : RenSim msgLab msgStore StreamInv P (k ()) (k' ())) :
    RenSim msgLab msgStore StreamInv P ((progSlots M pub B ss).bind k)
      ((progSlots M pub B ss).bind k') := by
  induction ss with
  | nil => exact hk
  | cons s ss ih =>
    rw [progSlots, QuantumComp₂.bind_assoc, QuantumComp₂.bind_assoc]
    exact renSim_progPorts_bind M (List.forall₂_same.2 fun p hp ↦
      portSim_self (by rw [need_of_mem_slotPorts pub hp]; exact valRnd_valSet _)) ih

/-- **The FORS opening** is simulated by itself. -/
theorem renSim_forsOpenT {P : Finset HPos → Prop} (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    RenSim msgLab msgStore StreamInv P (forsOpenT M pub B idx lv) (forsOpenT M pub B idx lv) :=
  renSim_revealThen_vr M (valRnd_valSet _) fun _ _ _ _ ↦
    renSim_progSlots_bind M pub _ (RenSim.pure _ _)

variable (upd : TrialUpd M)

/-- **A layer signature** is simulated by itself. -/
theorem renSim_signLayerT {P : Finset HPos → Prop} (B : QReg) (K : Key) :
    RenSim msgLab msgStore StreamInv P (signLayerT M upd pub B K) (signLayerT M upd pub B K) := by
  refine renSim_revealThen_vr M (valRnd_single _) fun _ _ _ _ ↦
    RenSim.bind₂ (renSim_readLift _ _ _ _ _) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · exact RenSim.pure _ _
  · exact renSim_revealThen_vr M (valRnd_valSet _) fun _ _ _ _ ↦
      renSim_progSlots_bind M pub _ (RenSim.pure _ _)

theorem renSim_forsOpenT_eq {P : Finset HPos → Prop} (B : QReg) {idx idx' : Index}
    {lv lv' : ForsTreeIndex → ForsLeafIndex} (hidx : idx = idx') (hlv : lv = lv') :
    RenSim msgLab msgStore StreamInv P (forsOpenT M pub B idx lv) (forsOpenT M pub B idx' lv') := by
  subst hidx hlv
  exact renSim_forsOpenT M pub B _ _

theorem renSim_signLayerT_keyOf {P : Finset HPos → Prop} (B : QReg) (l : Layer)
    {idx idx' : Index} (h : idx = idx') :
    RenSim msgLab msgStore StreamInv P (signLayerT M upd pub B (keyOf l idx))
      (signLayerT M upd pub B (keyOf l idx')) := by
  subst h
  exact renSim_signLayerT M pub upd B _

/-- **An absorption's program ports simulated pairwise**: blocks and corrections that agree at the
store and at the renamed store. -/
theorem forall₂_pathPorts {P : Finset HPos → Prop} {T₀ T₀' : Finset HPos}
    {b : RevealVals XD T₀ → ℕ → X} {b' : RevealVals XD T₀' → ℕ → X}
    {cor : RevealVals XD T₀ → X → X → X} {cor' : RevealVals XD T₀' → X → X → X} (n : ℕ)
    (hb : ∀ L₁ σ, P L₁ → StreamInv L₁ σ →
      b (restrictTo T₀ (fill σ)) = b' (restrictTo T₀' (fill (msgStore L₁ σ))))
    (hcor : ∀ L₁ σ, P L₁ → StreamInv L₁ σ →
      cor (restrictTo T₀ (fill σ)) = cor' (restrictTo T₀' (fill (msgStore L₁ σ)))) :
    List.Forall₂ (PortSim msgStore StreamInv P) (pathPorts pub T₀ b cor n)
      (pathPorts pub T₀' b' cor' n) := by
  unfold pathPorts
  generalize List.range n = l
  induction l with
  | nil => exact List.Forall₂.nil
  | cons j l ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine List.rel_append (.cons ?_ (.cons ?_ (.cons ?_ .nil))) ih
    · exact .progK _ _ _ _ fun L₁ σ hL hG ↦ congrArg (fun b ↦ cellK pub b j) (hb L₁ σ hL hG)
    · exact .progK' _ _ _ _ fun L₁ σ hL hG ↦ congrArg (fun b ↦ cellK' pub b j) (hb L₁ σ hL hG)
    · exact .progH _ _ _ _ fun L₁ σ hL hG ↦
        congrArg₂ (fun b c ↦ cellH pub b (n - 1) c j) (hb L₁ σ hL hG) (hcor L₁ σ hL hG)

theorem extendVals_notMem {T : Finset HPos} (w : RevealVals XD T) {p : ValPos}
    (h : HPos.val p ∉ T) : extendVals w p = 0 :=
  dite_eq_right h

theorem extendVals_congr {T₀ T₀' : Finset HPos} {v v' : (s : HPos) → XD s}
    (hm : ∀ p, HPos.val p ∈ T₀ ↔ HPos.val p ∈ T₀')
    (hv : ∀ p, HPos.val p ∈ T₀ → v (.val p) = v' (.val p)) :
    extendVals (restrictTo T₀ v) = extendVals (restrictTo T₀' v') := funext fun p ↦ by
  by_cases h : HPos.val p ∈ T₀
  · rw [extendVals_restrictTo h, extendVals_restrictTo ((hm p).1 h)]
    exact hv p h
  · have h' : HPos.val p ∉ T₀' := fun h' ↦ h ((hm p).2 h')
    exact (extendVals_notMem _ h).trans (extendVals_notMem _ h').symm

/-- **`H_msg` call `i`'s program ports** under the two policies, for an output coordinate `o` of
`strPol` whose value is the renamed store's `.dig M i`. -/
theorem forall₂_hmsgPorts {P : Finset HPos → Prop} {L : Finset HPos} {msg : Message}
    (i : DigestCall) {o : HPos} (ho : strPol.out L msg i = o) (hvo : ∀ p, HPos.val p ≠ o)
    (hout : ∀ L₁ σ, P L₁ → StreamInv L₁ σ →
      hashOut o (fill σ o) = hashOut (.dig msg i) (fill (msgStore L₁ σ) (.dig msg i))) :
    List.Forall₂ (PortSim msgStore StreamInv P) (hmsgPorts pub strPol L msg i)
      (hmsgPorts pub msgPol (msgLab L) msg i) := by
  unfold hmsgPorts hmsgNeed
  rw [ho, show msgPol.out (msgLab L) msg i = HPos.dig msg i from rfl]
  have hr : HPos.rnd msg ∈ ({.val rootPos, .rnd msg, o} : Finset HPos) := by simp
  have hr' : HPos.rnd msg ∈ ({.val rootPos, .rnd msg, .dig msg i} : Finset HPos) := by simp
  have hm : ∀ p, HPos.val p ∈ ({.val rootPos, .rnd msg, o} : Finset HPos) ↔
      HPos.val p ∈ ({.val rootPos, .rnd msg, .dig msg i} : Finset HPos) := fun p ↦ by
    simp only [Finset.mem_insert, Finset.mem_singleton, hvo p, or_false]
    simp
  refine forall₂_pathPorts pub 1 (fun L₁ σ _ _ ↦ ?_) fun L₁ σ hL hG ↦ ?_
  · rw [extendRnd_restrictTo hr, extendRnd_restrictTo hr',
      extendVals_congr (v := fill σ) (v' := fill (msgStore L₁ σ)) hm fun p _ ↦ rfl]
    rfl
  · show cor256 (extendOut _ o) = cor256 (extendOut _ (.dig msg i))
    rw [extendOut_restrictTo (by simp), extendOut_restrictTo (by simp), hout L₁ σ hL hG]

/-- **The signer at `strPol` is simulated by the signer at `msgPol`.** -/
theorem renSim_signT (B : QReg) (msg : Message) :
    RenSim msgLab msgStore StreamInv (fun _ ↦ True) (signT M upd strPol pub B msg)
      (signT M upd msgPol pub B msg) := by
  have hU := (valRnd_rootRnd msg).asg
  refine renSim_revealThen_vr M (valRnd_rootRnd msg) fun w₁ L m₁ _ ↦ ?_
  dsimp only
  rcases hs : streamIdx L msg with _ | j
  · have hT := mem_strNeed_none hs
    have hT' := mem_msgNeed (msgLab L) msg
    obtain ⟨hfree, hN⟩ := streamIdx_none_facts hs hU
    refine renSim_revealThen _ _ (fun _ ↦ fallEquiv hT hT')
      (fun _ _ _ _ ↦ msgLab_union_fall hT hT')
      (fun _ _ w hL hG _ ↦ by subst hL; exact msgStore_swapIn_fall hT hT' hG hfree w)
      (fun _ _ w hL _ ↦ by subst hL; exact agrees_fall hT hT' hfree w)
      (fun _ _ hL _ ↦ by subst hL; exact card_fall hT hT' hfree)
      (fun _ _ w hL hG _ ↦ by subst hL; exact streamInv_fall hT hG hfree hN w)
      fun w₂ L₂ m₂ hL ↦ ?_
    dsimp only
    subst hL
    have hfree₃ : ∀ j, HPos.asg msg j ∉ L ∪ {.val rootPos, .rnd msg} ∪ strPol.need L msg :=
      fun j h ↦ (Finset.mem_union.1 h).elim (hfree j) (fall_asg_notMem hT msg j)
    have hd : digestOf strPol L msg w₂ = digestOf msgPol (msgLab L) msg (fallEquiv hT hT' w₂) :=
      congrArg truncateMessageDigest (funext fun i ↦ by
        rw [strPolOut_none hs]
        show extendOut w₂ (.dig msg i) = extendOut (fallEquiv hT hT' w₂) (.dig msg i)
        have hi : HPos.dig msg i ∈ msgPol.need (msgLab L) msg :=
          (hT' _).2 (by rcases digestCall_cases i with rfl | rfl <;> simp)
        unfold extendOut
        rw [dite_eq_left ((hT _).2 ((hT' _).1 hi)), dite_eq_left hi, fallEquiv_apply])
    refine renSim_progPorts_bind M (List.rel_append
      (forall₂_hmsgPorts pub 0 (strPolOut_none hs 0) (fun _ h ↦ by cases h)
        fun L₁ σ hL₁ _ ↦ by
          subst hL₁
          rw [fill_msgStore_dig_none σ (markOf_of_free hfree₃)])
      (forall₂_hmsgPorts pub 1 (strPolOut_none hs 1) (fun _ h ↦ by cases h)
        fun L₁ σ hL₁ _ ↦ by
          subst hL₁
          rw [fill_msgStore_dig_none σ (markOf_of_free hfree₃)])) ?_
    refine RenSim.bind₂ (renSim_forsOpenT_eq M pub _ (congrArg digestIndex hd)
      (congrArg digestForsLeaves hd)) fun _ ↦ ?_
    refine RenSim.bind₂ (α := Option (LayerSignature 0))
      (renSim_signLayerT_keyOf M pub upd _ 0 (congrArg digestIndex hd))
      fun s₀ ↦ ?_
    rcases s₀ with _ | bottom
    · exact RenSim.pure _ _
    refine RenSim.bind₂ (α := Option (LayerSignature 1))
      (renSim_signLayerT_keyOf M pub upd _ 1 (congrArg digestIndex hd))
      fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · exact RenSim.pure _ _
    refine RenSim.bind₂ (α := Option (LayerSignature 2))
      (renSim_signLayerT_keyOf M pub upd _ 2 (congrArg digestIndex hd))
      fun s₂ ↦ ?_
    rcases s₂ with _ | top <;> exact RenSim.pure _ _
  · have hT := mem_strNeed_some hs
    have hT' := mem_msgNeed (msgLab L) msg
    have hj := streamIdx_some_facts hs hU
    refine renSim_revealThen _ _ (fun _ ↦ entryEquiv hT hT')
      (fun _ _ hL hG ↦ by subst hL; exact msgLab_union_entry hT hT' hG hj)
      (fun _ _ w hL hG _ ↦ by subst hL; exact msgStore_swapIn_entry hT hT' hG hj w)
      (fun _ _ w hL hG ↦ by subst hL; exact agrees_entry hT hT' hG hj w)
      (fun _ _ hL hG ↦ by subst hL; exact card_entry hT hT' hG hj)
      (fun _ _ w hL hG _ ↦ by subst hL; exact streamInv_entry hT hG hj w)
      fun w₂ L₂ m₂ hL ↦ ?_
    dsimp only
    subst hL
    have hmark : ∀ L₁ σ, L₁ = L ∪ {.val rootPos, .rnd msg} ∪ strPol.need L msg →
        StreamInv L₁ σ → markOf L₁ msg = some j := fun L₁ σ hL₁ hG ↦ by
      subst hL₁
      exact markOf_of_mem hG.one (Finset.mem_union_right _ ((hT _).2 (Or.inr (Or.inr rfl))))
    have hd : digestOf strPol L msg w₂ = digestOf msgPol (msgLab L) msg (entryEquiv hT hT' w₂) :=
      congrArg truncateMessageDigest (funext fun i ↦ by
        rw [strPolOut_some hs]
        show extendOut w₂ (.str j i) = extendOut (entryEquiv hT hT' w₂) (.dig msg i)
        unfold extendOut
        rw [dite_eq_left (str_mem_of_entry hT i), dite_eq_left (dig_mem_of_entry hT' i),
          entryEquiv_dig]
        rfl)
    refine renSim_progPorts_bind M (List.rel_append
      (forall₂_hmsgPorts pub 0 (strPolOut_some hs 0) (fun _ h ↦ by cases h)
        fun L₁ σ hL₁ hG ↦ by rw [fill_msgStore_dig_some σ (hmark L₁ σ hL₁ hG)]; rfl)
      (forall₂_hmsgPorts pub 1 (strPolOut_some hs 1) (fun _ h ↦ by cases h)
        fun L₁ σ hL₁ hG ↦ by rw [fill_msgStore_dig_some σ (hmark L₁ σ hL₁ hG)]; rfl)) ?_
    refine RenSim.bind₂ (renSim_forsOpenT_eq M pub _ (congrArg digestIndex hd)
      (congrArg digestForsLeaves hd)) fun _ ↦ ?_
    refine RenSim.bind₂ (α := Option (LayerSignature 0))
      (renSim_signLayerT_keyOf M pub upd _ 0 (congrArg digestIndex hd))
      fun s₀ ↦ ?_
    rcases s₀ with _ | bottom
    · exact RenSim.pure _ _
    refine RenSim.bind₂ (α := Option (LayerSignature 1))
      (renSim_signLayerT_keyOf M pub upd _ 1 (congrArg digestIndex hd))
      fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · exact RenSim.pure _ _
    refine RenSim.bind₂ (α := Option (LayerSignature 2))
      (renSim_signLayerT_keyOf M pub upd _ 2 (congrArg digestIndex hd))
      fun s₂ ↦ ?_
    rcases s₂ with _ | top <;> exact RenSim.pure _ _

/-- **The challenger at `strPol` is simulated by the challenger at `msgPol`.** -/
theorem renSim_challengeT (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    RenSim msgLab msgStore StreamInv (fun _ ↦ True) (challengeT M upd strPol pub A c)
      (challengeT M upd msgPol pub A c) := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact renSim_readLift _ _ _ _ _
  · exact renSim_readLift _ _ _ _ _
  · exact RenSim.bind (renSim_act_bind _ fun _ ↦ renSim_signT M pub upd _ msg)
      fun _ _ ↦ RenSim.pure _ _

/-- **The game at `strPol` is simulated by the game at `msgPol`**: the renaming of the stream
entries of the marked messages to their `H_msg` outputs. -/
theorem renSim_gameT (A : SAdversary) :
    RenSim msgLab msgStore StreamInv (fun _ ↦ True) (gameT M upd strPol pub A)
      (gameT M upd msgPol pub A) :=
  renSim_revealThen_vr M (valRnd_single _) fun _ _ _ _ ↦
    (RenSim.bind₂ (renSim_substitute _ _ _ (renSim_challengeT M pub upd) _) fun _ ↦
      RenSim.bind₂ (renSim_readLift _ _ _ _ _) fun _ ↦ RenSim.pure _ _).mono fun _ _ ↦ trivial

end stream

/-! ## The averaged laws of the two policies -/

/-- **The win probability of the canonical runtime-2 game** at the digest policy `pol`, the public
data `p` and the hidden values `v`. -/
noncomputable def p2R (pol : DigestPolicy) (A : SAdversary) (p : Pub) (v : (s : HPos) → XD s) :
    ℝ≥0∞ :=
  (runtimeR m0R).evalDistMap .instruments (gameR pol A p v) (SubState.basis ()) winObs {true}

/-- **The stream relabelling** (step 3 of leanSPHINCS's chain): for every public data `p`, the
averages over the hidden values of the canonical game's win probability at `msgPol` and at
`strPol` are equal. -/
theorem uavg_p2R_msgPol_eq_strPol (A : SAdversary) (p : Pub) :
    uavg (p2R msgPol A p) = uavg (p2R strPol A p) := by
  have h := fun pol ↦ uavg_realizeT_outcome_eq_sampled (good := goodAll)
    LocalSig.Interp.instruments m0 (gameT Selections cwUpd pol p A)
    (disc_gameT Selections cwUpd pol p A ∅) (keepsLab_gameT Selections cwUpd pol p A)
    (SubState.basis ()) winObs (measurableSet_singleton true)
  calc uavg (p2R msgPol A p)
      = (sampledRuntime goodAll m0).evalDistMap .instruments (gameT Selections cwUpd msgPol p A)
          (SubState.basis ()) winObs {true} := h msgPol
    _ = (sampledRuntime goodAll m0).evalDistMap .instruments (gameT Selections cwUpd strPol p A)
          (SubState.basis ()) winObs {true} :=
        congrArg (· {true}) (evalDistMap_sampled_eq_of_renSim LocalSig.Interp.instruments m0
          (renSim_gameT Selections p cwUpd A) trivial streamInv_empty msgLab_empty
          msgStore_empty (SubState.basis ()) winObs).symm
    _ = uavg (p2R strPol A p) := (h strPol).symm

end Quantum.Sphincs.Assembly

end
