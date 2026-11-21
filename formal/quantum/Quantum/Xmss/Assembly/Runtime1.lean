module

public import Quantum.Xmss.Hybrid.Kraus

@[expose] public section

/-!
# Runtime 1 of the hybrid is S5's runtime 1 on the programs S8 runs

The hybrid's runtime 1 (`Quantum.Xmss.Hybrid.runtime1 X Z L m₀`, signature `hwSpec`) starts with
no hardwired cell, reads the table `L` under its hardwired cells (`hwView W L`), and has the
program ports of runtime 2. S5's runtime 1 (`spongeHardwiredReadRuntime X Z L m₀`, signature
`hwReadSpec`) has `L` hardwired from the start and no program ports.

`DropsTo L x y`: the program `x` over `hwSpec` is the program `y` over `hwReadSpec` with program
calls inserted, each programming a cell of `L` with its `L` value (`ProgOf L c`) and followed by
the relabelling back to the register before the call (the shape of `progCall`). The two programs
have the same law (`evalDistMap_runtime1_eq_spongeHardwiredReadRuntime`).

The proof is a simulation through the map `forget L` from the register of runtime 1 to that of S5's
runtime 1: on the states with hardwired cells `W ≤ L` (`HwLe`) and databases empty on the cells of
`L` (`DbOff`), it sets the hardwired cells to `L`, and it kills the other states; it is
classical (dephased) in `W`. The sponge and read ports intertwine with it on every input (runtime
1 hardwires every cell of `L`, so its database never changes there; `blk_comm`), a program call
of a cell of `L` intertwines with the identity on the states above (`sum_prog`), and runtime 1
keeps its states there (`good`).
-/

open Matrix MeasureTheory
open scoped Kronecker ENNReal

universe w

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss.Hybrid QuantumRuntime

/-! ## Matrix facts -/

section matrix

/-- A matrix whose nonzero entries join states that agree on `g` commutes with the projector on
`g`. -/
theorem diagonal_ind_mul_comm {n : Type} [Fintype n] [DecidableEq n] (g : n → Prop)
    [DecidablePred g] (A : Matrix n n ℂ) (h : ∀ i j, A i j ≠ 0 → (g i ↔ g j)) :
    diagonal (fun i ↦ if g i then (1 : ℂ) else 0) * A =
      A * diagonal fun i ↦ if g i then (1 : ℂ) else 0 := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hA : A i j = 0
  · simp [hA]
  · have hg := h i j hA
    by_cases hi : g i
    · simp [hi, hg.1 hi]
    · simp [hi, mt hg.2 hi]

variable {T B : Type} [Fintype T] [DecidableEq T] [Fintype B] [DecidableEq B]

omit [DecidableEq T] in
/-- Composing classical Kraus operators. -/
theorem clsKraus_mul_clsKraus (p₁ p₂ : B → Prop) [DecidablePred p₁] [DecidablePred p₂]
    (φ₁ φ₂ : B → B) (R₁ R₂ : B → Matrix T T ℂ) :
    clsKraus p₁ φ₁ R₁ * clsKraus p₂ φ₂ R₂ =
      clsKraus (fun b ↦ p₂ b ∧ p₁ (φ₂ b)) (fun b ↦ φ₁ (φ₂ b)) fun b ↦ R₁ (φ₂ b) * R₂ b := by
  ext ⟨t', b'⟩ ⟨t, b⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single (φ₂ b)]
  · simp only [clsKraus_apply, and_true]
    by_cases h : p₂ b ∧ p₁ (φ₂ b) ∧ b' = φ₁ (φ₂ b)
    · obtain ⟨h₂, h₁, h₃⟩ := h
      simp [h₁, h₂, h₃, Matrix.mul_apply]
    · rw [ite_eq_right (fun h' ↦ h ⟨h'.1.1, h'.1.2, h'.2⟩)]
      refine Finset.sum_eq_zero fun t₁ _ ↦ ?_
      by_cases h₂ : p₂ b
      · have h₁ : ¬ (p₁ (φ₂ b) ∧ b' = φ₁ (φ₂ b)) := fun h₁ ↦ h ⟨h₂, h₁⟩
        simp [h₁]
      · simp [h₂]
  · intro b₁ _ hb₁
    refine Finset.sum_eq_zero fun t₁ _ ↦ ?_
    simp [clsKraus_apply, hb₁]
  · simp

omit [Fintype T] [DecidableEq T] [Fintype B] in
/-- Classical Kraus operators agreeing on their acceptance condition, and on the moves and blocks
of the accepted states, are equal. -/
theorem clsKraus_congr {p p' : B → Prop} [DecidablePred p] [DecidablePred p'] {φ φ' : B → B}
    {R R' : B → Matrix T T ℂ} (hp : ∀ b, p b ↔ p' b) (hφ : ∀ b, p b → φ b = φ' b)
    (hR : ∀ b, p b → R b = R' b) : clsKraus p φ R = clsKraus p' φ' R' := by
  ext s' s
  simp only [clsKraus_apply]
  by_cases h : p s.2
  · simp [h, (hp _).1 h, hφ _ h, hR _ h]
  · simp [h, mt (hp _).2 h]

omit [Fintype T] [DecidableEq T] [Fintype B] in
/-- A classical Kraus operator whose accepted blocks vanish is zero. -/
theorem clsKraus_eq_zero {p : B → Prop} [DecidablePred p] {φ : B → B} {R : B → Matrix T T ℂ}
    (h : ∀ b, p b → R b = 0) : clsKraus p φ R = 0 := by
  ext s' s
  simp only [clsKraus_apply, Matrix.zero_apply]
  split_ifs with hp
  · rw [h _ hp.1, Matrix.zero_apply]
  · rfl

omit [Fintype T] [DecidableEq T] [Fintype B] in
/-- A block-diagonal matrix is the classical Kraus operator accepting everything, moving nothing. -/
theorem blockDiagonal_eq_clsKraus (f : B → Matrix T T ℂ) :
    blockDiagonal f = clsKraus (fun _ ↦ True) id f := by
  ext ⟨t', b'⟩ ⟨t, b⟩
  rw [blockDiagonal_apply, clsKraus_apply]
  by_cases hb : b' = b
  · subst hb
    simp
  · simp [hb]

omit [Fintype T] [DecidableEq T] [Fintype B] in
/-- A classical Kraus operator beside a register `P`, as a classical Kraus operator on `P × T`. -/
theorem one_kronecker_clsKraus (P : Type) [Fintype P] [DecidableEq P] (p : B → Prop)
    [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ) :
    (1 : Matrix P P ℂ) ⊗ₖ clsKraus p φ R =
      (clsKraus p φ fun b ↦ (1 : Matrix P P ℂ) ⊗ₖ R b).submatrix (Equiv.prodAssoc P T B).symm
        (Equiv.prodAssoc P T B).symm := by
  ext ⟨q', t', b'⟩ ⟨q, t, b⟩
  simp only [kroneckerMap_apply, clsKraus_apply, submatrix_apply, Equiv.prodAssoc_symm_apply]
  split_ifs <;> simp

omit [DecidableEq T] in
/-- **A classical Kraus operator intertwines block-diagonal matrices** whose blocks it
intertwines. -/
theorem one_kronecker_clsKraus_mul_liftBlocks {P : Type} [Fintype P] [DecidableEq P]
    (p : B → Prop) [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ)
    (f g : B → Matrix (P × T) (P × T) ℂ)
    (h : ∀ b, p b → ((1 : Matrix P P ℂ) ⊗ₖ R b) * f b = g (φ b) * ((1 : Matrix P P ℂ) ⊗ₖ R b)) :
    ((1 : Matrix P P ℂ) ⊗ₖ clsKraus p φ R) * liftBlocks (Equiv.prodAssoc P T B).symm f =
      liftBlocks (Equiv.prodAssoc P T B).symm g * ((1 : Matrix P P ℂ) ⊗ₖ clsKraus p φ R) := by
  rw [one_kronecker_clsKraus, liftBlocks, liftBlocks, submatrix_mul_equiv, submatrix_mul_equiv,
    blockDiagonal_eq_clsKraus, blockDiagonal_eq_clsKraus, clsKraus_mul_clsKraus,
    clsKraus_mul_clsKraus]
  congr 1
  exact clsKraus_congr (fun b ↦ ⟨fun h' ↦ ⟨h'.2, trivial⟩, fun h' ↦ ⟨trivial, h'.1⟩⟩)
    (fun _ _ ↦ rfl) fun b hb ↦ h b hb.2

end matrix

/-! ## Function facts -/

section fn

variable {A Y : Type} [DecidableEq A]

/-- Two contents agreeing off `c`, and at `c` unless `l` is empty there, are empty on the same
cells of `l`. -/
theorem off_iff_of_agree {l f g : A → Option Y} {c : A} (hfg : ∀ a, a ≠ c → f a = g a)
    (hc : l c = none ∨ f c = g c) :
    (∀ a, l a = none ∨ f a = none) ↔ ∀ a, l a = none ∨ g a = none := by
  refine forall_congr' fun a ↦ ?_
  by_cases ha : a = c
  · subst ha
    rcases hc with hc | hc
    · simp [hc]
    · rw [hc]
  · rw [hfg a ha]

/-- Emptying `c'` and emptying `c` agree on every content, and some two contents differ at `c`:
then `c' = c`. -/
theorem cell_eq_of_update {f g : A → Option Y} {c c' : A} (hne : f c ≠ g c)
    (hcell : ∀ F : A → Option Y, Function.update F c' none = Function.update F c none) :
    c' = c := by
  by_contra hcc
  have hf := congrFun (hcell f) c
  have hg := congrFun (hcell g) c
  rw [Function.update_of_ne (Ne.symm hcc), Function.update_self] at hf hg
  exact hne (hf.trans hg.symm)

theorem agree_of_update {f g : A → Option Y} {c : A}
    (h : Function.update f c none = Function.update g c none) : ∀ a, a ≠ c → f a = g a :=
  fun a ha ↦ by simpa [Function.update_of_ne ha] using congrFun h a

/-- One cell of a compressed port: emptying the queried cell `c` gives the same content, the
queried cell is `c'` for every content, and `l` is empty at `c'`. -/
theorem off_iff_of_update {l f g : A → Option Y} {c c' : A}
    (h : Function.update f c none = Function.update g c none)
    (hcell : ∀ F : A → Option Y, Function.update F c' none = Function.update F c none)
    (hl : l c' = none) :
    (∀ a, l a = none ∨ f a = none) ↔ ∀ a, l a = none ∨ g a = none := by
  refine off_iff_of_agree (agree_of_update h) ?_
  by_cases he : f c = g c
  · exact Or.inr he
  · rw [← cell_eq_of_update he hcell]
    exact Or.inl hl

theorem eq_none_of_isSome_eq_false {o : Option Y} (h : o.isSome = false) : o = none := by
  cases o <;> simp_all

end fn

/-! ## The register map -/

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-- The hardwired cells `W` lie in `L`, with `L`'s values. -/
def HwLe (W L : Hw X Z) : Prop :=
  (∀ z, W.1 z = none ∨ W.1 z = L.1 z) ∧ (∀ x, W.2.1 x = none ∨ W.2.1 x = L.2.1 x) ∧
    ∀ x, W.2.2 x = none ∨ W.2.2 x = L.2.2 x

instance (W L : Hw X Z) : Decidable (HwLe W L) := by
  unfold HwLe
  infer_instance

/-- The databases are empty on the cells of `L`. -/
def DbOff (L : Hw X Z) (D : DbReg X Z) : Prop :=
  (∀ z, L.1 z = none ∨ D.1 z = none) ∧ (∀ x, L.2.1 x = none ∨ D.2.1 x = none) ∧
    ∀ x, L.2.2 x = none ∨ D.2.2 x = none

instance (L : Hw X Z) (D : DbReg X Z) : Decidable (DbOff L D) := by
  unfold DbOff
  infer_instance

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- Below `L`, the view of the hardwired cells over `L` is `L`. -/
theorem hwView_eq_of_hwLe {W L : Hw X Z} (h : HwLe W L) : hwView W L = L := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  have key : ∀ {A Y : Type} {f l : A → Option Y}, (∀ a, f a = none ∨ f a = l a) →
      (fun a ↦ (f a).or (l a)) = l := fun h ↦ funext fun a ↦ by
    rcases h a with h | h
    · simp [h]
    · rw [h, Option.or_self]
  exact Prod.ext (key h₁) (Prod.ext (key h₂) (key h₃))

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem hwLe_hwEmpty (L : Hw X Z) : HwLe (hwEmpty X Z) L :=
  ⟨fun _ ↦ Or.inl rfl, fun _ ↦ Or.inl rfl, fun _ ↦ Or.inl rfl⟩

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem dbOff_empty (L : Hw X Z) : DbOff L (Database.empty, Database.empty, Database.empty) :=
  ⟨fun _ ↦ Or.inr rfl, fun _ ↦ Or.inr rfl, fun _ ↦ Or.inr rfl⟩

/-- The projector on the databases empty on the cells of `L`. -/
noncomputable def offProj (L : Hw X Z) : Matrix (DbReg X Z) (DbReg X Z) ℂ :=
  diagonal fun D ↦ if DbOff L D then 1 else 0

theorem offProj_mul_self (L : Hw X Z) : offProj L * offProj L = offProj L := by
  rw [offProj, diagonal_mul_diagonal]
  congr 1
  funext D
  split_ifs <;> simp

theorem one_kronecker_offProj (P : Type) [Fintype P] [DecidableEq P] (L : Hw X Z) :
    (1 : Matrix P P ℂ) ⊗ₖ offProj L =
      diagonal fun q : P × DbReg X Z ↦ if DbOff L q.2 then 1 else 0 := by
  rw [offProj, ← diagonal_one, diagonal_kronecker_diagonal]
  congr 1
  funext q
  simp

/-- `offProj L` after a matrix that fixes the databases empty on `L` when `o` holds, and kills them
otherwise. -/
theorem mul_offProj_of (L : Hw X Z) (Rd : Matrix (DbReg X Z) (DbReg X Z) ℂ) (o : Prop)
    [Decidable o] (h : ∀ D' D, DbOff L D → Rd D' D = if o ∧ D' = D then 1 else 0) :
    Rd * offProj L = if o then offProj L else 0 := by
  ext D' D
  rw [offProj, mul_diagonal]
  by_cases hD : DbOff L D
  · rw [h D' D hD]
    by_cases ho : o
    · by_cases hDD : D' = D
      · subst hDD
        simp [ho, hD]
      · simp [ho, hDD]
    · simp [ho]
  · by_cases ho : o
    · by_cases hDD : D' = D
      · subst hDD
        simp [ho, hD]
      · simp [ho, hD, hDD]
    · simp [ho, hD]

variable (M) in
/-- On the states with hardwired cells `W ≤ L` and databases empty on `L`, set the hardwired
cells to `L`; kill the other states. -/
noncomputable def hwKraus (L W : Hw X Z) : Matrix (HwReg X Z M) (HwReg X Z M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.1 = W ∧ HwLe W L) (fun b ↦ (L, b.2)) fun _ ↦ offProj L

variable (M) in
/-- The projector on the states with hardwired cells below `L` and databases empty on `L`. -/
noncomputable def goodProj (L : Hw X Z) : Matrix (HwReg X Z M) (HwReg X Z M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ HwLe b.1 L) id fun _ ↦ offProj L

variable (M) in
/-- **The register map** from runtime 1 to S5's runtime 1, classical in the hardwired cells. -/
noncomputable def forget (L : Hw X Z) : MatrixMap (HwReg X Z M) (HwReg X Z M) :=
  ∑ W, MatrixMap.conj (hwKraus M L W)

variable (M) in
/-- The projection on the states runtime 1 reaches. -/
noncomputable def good (L : Hw X Z) : MatrixMap (HwReg X Z M) (HwReg X Z M) :=
  MatrixMap.conj (goodProj M L)

theorem hwKraus_mul_goodProj (L W : Hw X Z) : hwKraus M L W * goodProj M L = hwKraus M L W := by
  rw [hwKraus, goodProj, clsKraus_mul_clsKraus]
  refine clsKraus_congr (fun b ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩) (fun _ _ ↦ rfl)
    fun _ _ ↦ offProj_mul_self L
  rw [h.1]
  exact h.2

theorem goodProj_mul_self (L : Hw X Z) : goodProj M L * goodProj M L = goodProj M L := by
  rw [goodProj, clsKraus_mul_clsKraus]
  exact clsKraus_congr (fun b ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, h⟩⟩) (fun _ _ ↦ rfl)
    fun _ _ ↦ offProj_mul_self L

/-- A sum of maps, amplified on the left. -/
theorem amplifyLeft_sum {R S : Type*} {ι : Type*} (s : Finset ι) (Φ : ι → MatrixMap R S)
    (P : Type*) : (∑ i ∈ s, Φ i).amplifyLeft P = ∑ i ∈ s, (Φ i).amplifyLeft P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha,
      MatrixMap.amplifyLeft_add, ih]

theorem forget_amplifyLeft (L : Hw X Z) (P : Type) [Fintype P] [DecidableEq P] :
    (forget M L).amplifyLeft P = ∑ W, MatrixMap.conj ((1 : Matrix P P ℂ) ⊗ₖ hwKraus M L W) := by
  rw [forget, amplifyLeft_sum]
  simp only [MatrixMap.amplifyLeft_conj]

theorem good_amplifyLeft (L : Hw X Z) (P : Type) [Fintype P] [DecidableEq P] :
    (good M L).amplifyLeft P = MatrixMap.conj ((1 : Matrix P P ℂ) ⊗ₖ goodProj M L) :=
  MatrixMap.amplifyLeft_conj _

theorem forget_good (L : Hw X Z) (P : Type) [Fintype P] [DecidableEq P]
    (ρ : Matrix (P × HwReg X Z M) (P × HwReg X Z M) ℂ) :
    (forget M L).amplifyLeft P ((good M L).amplifyLeft P ρ) = (forget M L).amplifyLeft P ρ := by
  rw [forget_amplifyLeft, good_amplifyLeft, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul,
    hwKraus_mul_goodProj]

theorem good_good (L : Hw X Z) (P : Type) [Fintype P] [DecidableEq P]
    (ρ : Matrix (P × HwReg X Z M) (P × HwReg X Z M) ℂ) :
    (good M L).amplifyLeft P ((good M L).amplifyLeft P ρ) = (good M L).amplifyLeft P ρ := by
  rw [good_amplifyLeft, ← LinearMap.comp_apply, ← MatrixMap.conj_mul, ← mul_kronecker_mul,
    Matrix.one_mul, goodProj_mul_self]

/-- The Gram operators of `forget` add up to the projector of `good`. -/
theorem sum_hwKraus_gram (L : Hw X Z) :
    ∑ W, (hwKraus M L W)ᴴ * hwKraus M L W = (goodProj M L)ᴴ * goodProj M L := by
  have hW : ∀ W, (hwKraus M L W)ᴴ * hwKraus M L W = blockDiagonal fun b : Hw X Z × M ↦
      if b.1 = W ∧ HwLe W L then (offProj L)ᴴ * offProj L else 0 :=
    fun W ↦ conjTranspose_clsKraus_mul_self _ _ _ fun b b' hb hb' h ↦
      Prod.ext (hb.1.trans hb'.1.symm) (Prod.mk.inj h).2
  have hG : (goodProj M L)ᴴ * goodProj M L = blockDiagonal fun b : Hw X Z × M ↦
      if HwLe b.1 L then (offProj L)ᴴ * offProj L else 0 :=
    conjTranspose_clsKraus_mul_self _ _ _ fun _ _ _ _ h ↦ h
  have hs : ∀ b : Hw X Z × M, ∑ W,
      (if b.1 = W ∧ HwLe W L then (offProj L)ᴴ * offProj L else 0) =
        if HwLe b.1 L then (offProj L)ᴴ * offProj L else 0 := fun b ↦ by
    simp only [ite_and]
    rw [Finset.sum_ite_eq]
    simp
  rw [hG]
  ext ⟨t, b⟩ ⟨t', b'⟩
  rw [Matrix.sum_apply]
  simp only [hW, blockDiagonal_apply]
  by_cases hb : b = b'
  · subst hb
    simp only [ite_true]
    rw [← Matrix.sum_apply, hs]
  · simp [hb]

theorem trace_forget (L : Hw X Z) (P : Type) [Fintype P] [DecidableEq P]
    (σ : Matrix (P × HwReg X Z M) (P × HwReg X Z M) ℂ) :
    ((forget M L).amplifyLeft P σ).trace = ((good M L).amplifyLeft P σ).trace := by
  rw [forget_amplifyLeft, good_amplifyLeft, LinearMap.sum_apply, trace_sum,
    MatrixMap.trace_conj_apply]
  simp only [MatrixMap.trace_conj_apply]
  rw [← trace_sum, ← Finset.sum_mul]
  congr 2
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronecker_right, sum_hwKraus_gram]

omit [Fintype M] in
theorem hwKraus_eq_clsMap (L W : Hw X Z) :
    hwKraus M L W = clsMap (fun s : HwReg X Z M ↦ s.2.1 = W ∧ HwLe W L ∧ DbOff L s.1)
      fun s ↦ (s.1, L, s.2.2) := by
  ext ⟨D', b'⟩ ⟨D, b⟩
  simp only [hwKraus, clsKraus_apply, clsMap, of_apply, offProj, diagonal_apply]
  by_cases h : b.1 = W ∧ HwLe W L
  · by_cases hD : DbOff L D
    · by_cases he : (D', b') = (D, L, b.2)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simp [h, hD]
      · have : ¬ (b' = (L, b.2) ∧ D' = D) := fun h' ↦ he (by rw [h'.1, h'.2])
        by_cases hb : b' = (L, b.2)
        · have hDD : D' ≠ D := fun e ↦ this ⟨hb, e⟩
          simp [h, hD, hb, hDD]
        · simp [h, hb, he]
    · by_cases hb : b' = (L, b.2)
      · by_cases hDD : D' = D
        · subst hDD
          simp [h, hD, hb]
        · simp [h, hD, hb, hDD]
      · simp [h, hD, hb]
  · have : ¬ (b.1 = W ∧ HwLe W L ∧ DbOff L D) := fun h' ↦ h ⟨h'.1, h'.2.1⟩
    simp only [h, false_and, ↓reduceIte]
    rw [ite_eq_right (fun h' ↦ this h'.1)]

omit [Fintype M] in
theorem goodProj_eq_clsMap (L : Hw X Z) :
    goodProj M L = clsMap (fun s : HwReg X Z M ↦ HwLe s.2.1 L ∧ DbOff L s.1) id := by
  ext ⟨D', b'⟩ ⟨D, b⟩
  simp only [goodProj, clsKraus_apply, clsMap, of_apply, offProj, diagonal_apply, id]
  by_cases h : HwLe b.1 L
  · by_cases hb : b' = b
    · subst hb
      by_cases hDD : D' = D
      · subst hDD
        by_cases hD : DbOff L D' <;> simp [h, hD]
      · simp [h, hDD]
    · simp [h, hb]
  · simp [h]

/-- The initial state of runtime 1 is mapped to that of S5's runtime 1. -/
theorem forget_single (L : Hw X Z) (m₀ : M) :
    forget M L (Matrix.single ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀)
      ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) 1) =
      Matrix.single ((Database.empty, Database.empty, Database.empty), L, m₀)
        ((Database.empty, Database.empty, Database.empty), L, m₀) 1 := by
  rw [forget, LinearMap.sum_apply]
  simp only [hwKraus_eq_clsMap, conj_clsMap_single]
  rw [Finset.sum_eq_single (hwEmpty X Z)]
  · rw [ite_eq_left ⟨rfl, hwLe_hwEmpty L, dbOff_empty L⟩]
  · intro W _ hW
    rw [ite_eq_right fun h ↦ hW h.1.symm]
  · simp

theorem good_single (L : Hw X Z) (m₀ : M) :
    good M L (Matrix.single ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀)
      ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) 1) =
      Matrix.single ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀)
        ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) 1 := by
  rw [good, goodProj_eq_clsMap, conj_clsMap_single,
    ite_eq_left ⟨hwLe_hwEmpty L, dbOff_empty L⟩]
  rfl

/-! ## The read ports -/

/-- A read port of runtime 1 and the read port of S5 intertwine through the hardwired cells. -/
theorem hwKraus_mul_read (L W : Hw X Z) (m₁ m₂ : M)
    (R : Hw X Z → Matrix (DbReg X Z) (DbReg X Z) ℂ) (hR : offProj L * R L = R L * offProj L) :
    hwKraus M L W * clsKraus (fun b : Hw X Z × M ↦ b.2 = m₁) (fun b ↦ (b.1, m₂))
        (fun b ↦ R (hwView b.1 L)) =
      clsKraus (fun b : Hw X Z × M ↦ b.2 = m₁) (fun b ↦ (b.1, m₂)) (fun b ↦ R b.1) *
        hwKraus M L W := by
  rw [hwKraus, clsKraus_mul_clsKraus, clsKraus_mul_clsKraus]
  refine clsKraus_congr (fun b ↦ ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩) (fun _ _ ↦ rfl)
    fun b hb ↦ ?_
  obtain ⟨-, hW, hle⟩ := hb
  dsimp only at hW ⊢
  rw [hW, hwView_eq_of_hwLe hle]
  exact hR

/-- A read port of runtime 1 keeps the states it reaches. -/
theorem goodProj_mul_read (L : Hw X Z) (m₁ m₂ : M)
    (R : Hw X Z → Matrix (DbReg X Z) (DbReg X Z) ℂ) (hR : offProj L * R L = R L * offProj L) :
    goodProj M L * clsKraus (fun b : Hw X Z × M ↦ b.2 = m₁) (fun b ↦ (b.1, m₂))
        (fun b ↦ R (hwView b.1 L)) =
      clsKraus (fun b : Hw X Z × M ↦ b.2 = m₁) (fun b ↦ (b.1, m₂)) (fun b ↦ R (hwView b.1 L)) *
        goodProj M L := by
  rw [goodProj, clsKraus_mul_clsKraus, clsKraus_mul_clsKraus]
  refine clsKraus_congr (fun b ↦ ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩) (fun _ _ ↦ rfl)
    fun b hb ↦ ?_
  obtain ⟨-, hle⟩ := hb
  dsimp only [id] at hle ⊢
  rw [hwView_eq_of_hwLe hle]
  exact hR

omit [Fintype X] [Fintype Z] in
/-- A nonzero entry of a read leaves the other cells, and the read cell unless it is not
hardwired. -/
theorem cellRead_ne_zero {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    {w : Database A Y} {a : A} {o : Option Y} {D' D : Database A Y}
    (h : cellRead w a o D' D ≠ 0) : (∀ x, x ≠ a → D' x = D x) ∧ (w a = none ∨ D' a = D a) := by
  refine ⟨cellRead_apply_ne_zero h, ?_⟩
  rcases hw : w a with _ | v
  · exact Or.inl rfl
  · right
    simp only [cellRead, hw] at h
    split_ifs at h
    · rw [Matrix.one_apply] at h
      split_ifs at h with hD
      · rw [hD]
      · exact absurd rfl h
    · exact absurd rfl h

theorem offProj_comm_readH (L : Hw X Z) (z : Z) (o : Option X) :
    offProj L * (cellRead L.1 z o ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ)) =
      (cellRead L.1 z o ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ)) * offProj L := by
  refine diagonal_ind_mul_comm _ _ fun D' D h ↦ ?_
  rw [kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with h2
  · obtain ⟨hagree, hz⟩ := cellRead_ne_zero (left_ne_zero_of_mul h)
    unfold DbOff
    rw [h2, off_iff_of_agree hagree hz]
  · exact absurd (mul_zero _) h

theorem offProj_comm_readK (L : Hw X Z) (x : X) (o : Option Z) :
    offProj L * ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      (cellRead L.2.1 x o ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))) =
      ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        (cellRead L.2.1 x o ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))) * offProj L := by
  refine diagonal_ind_mul_comm _ _ fun D' D h ↦ ?_
  rw [kroneckerMap_apply, kroneckerMap_apply, Matrix.one_apply, Matrix.one_apply] at h
  split_ifs at h with h1 h3
  · obtain ⟨hagree, hx⟩ := cellRead_ne_zero (left_ne_zero_of_mul (right_ne_zero_of_mul h))
    unfold DbOff
    rw [h1, h3, off_iff_of_agree hagree hx]
  all_goals simp at h

theorem offProj_comm_readK' (L : Hw X Z) (x : X) (o : Option Z) :
    offProj L * ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead L.2.2 x o)) =
      ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead L.2.2 x o)) * offProj L := by
  refine diagonal_ind_mul_comm _ _ fun D' D h ↦ ?_
  rw [kroneckerMap_apply, kroneckerMap_apply, Matrix.one_apply, Matrix.one_apply] at h
  split_ifs at h with h1 h2
  · obtain ⟨hagree, hx⟩ := cellRead_ne_zero (right_ne_zero_of_mul (right_ne_zero_of_mul h))
    unfold DbOff
    rw [h1, h2, off_iff_of_agree hagree hx]
  all_goals simp at h

/-- A read port of runtime 1 and that of S5 intertwine through the hardwired cells. -/
theorem hwKraus_mul_hwReadKraus1 (L W : Hw X Z) (c : HwRead X Z M) (r : c.Result) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwKraus M L W) * hwReadKraus1 L c r =
      hwReadKraus c r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwKraus M L W) := by
  cases c with
  | readH z upd =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwKraus M L W) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1H L z upd r) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwKraus M L W)
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    exact congrArg (fun K ↦ (1 * 1 : Matrix Unit Unit ℂ) ⊗ₖ K)
      (hwKraus_mul_read L W r.2 (upd r.2 r.1) (fun W ↦ cellRead W.1 z r.1 ⊗ₖ 1)
        (offProj_comm_readH L z r.1))
  | readK x upd =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwKraus M L W) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K L x upd r) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK x upd r) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwKraus M L W)
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    exact congrArg (fun K ↦ (1 * 1 : Matrix Unit Unit ℂ) ⊗ₖ K)
      (hwKraus_mul_read L W r.2 (upd r.2 r.1)
        (fun W ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (cellRead W.2.1 x r.1 ⊗ₖ 1))
        (offProj_comm_readK L x r.1))
  | readK' x upd =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwKraus M L W) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K' L x upd r) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' x upd r) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwKraus M L W)
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    exact congrArg (fun K ↦ (1 * 1 : Matrix Unit Unit ℂ) ⊗ₖ K)
      (hwKraus_mul_read L W r.2 (upd r.2 r.1)
        (fun W ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (1 ⊗ₖ cellRead W.2.2 x r.1))
        (offProj_comm_readK' L x r.1))

/-- A read port of runtime 1 keeps the states it reaches. -/
theorem goodProj_mul_hwReadKraus1 (L : Hw X Z) (c : HwRead X Z M) (r : c.Result) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ goodProj M L) * hwReadKraus1 L c r =
      hwReadKraus1 L c r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ goodProj M L) := by
  cases c with
  | readH z upd =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ goodProj M L) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1H L z upd r) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1H L z upd r) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ goodProj M L)
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    exact congrArg (fun K ↦ (1 * 1 : Matrix Unit Unit ℂ) ⊗ₖ K)
      (goodProj_mul_read L r.2 (upd r.2 r.1) (fun W ↦ cellRead W.1 z r.1 ⊗ₖ 1)
        (offProj_comm_readH L z r.1))
  | readK x upd =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ goodProj M L) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K L x upd r) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K L x upd r) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ goodProj M L)
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    exact congrArg (fun K ↦ (1 * 1 : Matrix Unit Unit ℂ) ⊗ₖ K)
      (goodProj_mul_read L r.2 (upd r.2 r.1)
        (fun W ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (cellRead W.2.1 x r.1 ⊗ₖ 1))
        (offProj_comm_readK L x r.1))
  | readK' x upd =>
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ goodProj M L) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K' L x upd r) =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K' L x upd r) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ goodProj M L)
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    exact congrArg (fun K ↦ (1 * 1 : Matrix Unit Unit ℂ) ⊗ₖ K)
      (goodProj_mul_read L r.2 (upd r.2 r.1)
        (fun W ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (1 ⊗ₖ cellRead W.2.2 x r.1))
        (offProj_comm_readK' L x r.1))

/-! ## The program ports -/

/-- One cell of the hardwired cells, with its laws. -/
structure HwCell (X Z Y : Type) [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] where
  /-- The hardwired value of the cell. -/
  get : Hw X Z → Option Y
  /-- Set the hardwired value of the cell. -/
  set : Hw X Z → Option Y → Hw X Z
  get_set : ∀ W o, get (set W o) = o
  set_set : ∀ W o o', set (set W o) o' = set W o'
  set_get : ∀ W, set W (get W) = W

/-- Cell `z` of `h`. -/
def cellH (z : Z) : HwCell X Z X where
  get W := W.1 z
  set W o := (Function.update W.1 z o, W.2)
  get_set W o := by simp
  set_set W o o' := by simp
  set_get W := by simp

/-- Cell `x` of `k`. -/
def cellK (x : X) : HwCell X Z Z where
  get W := W.2.1 x
  set W o := (W.1, Function.update W.2.1 x o, W.2.2)
  get_set W o := by simp
  set_set W o o' := by simp
  set_get W := by simp

/-- Cell `x` of `k'`. -/
def cellK' (x : X) : HwCell X Z Z where
  get W := W.2.2 x
  set W o := (W.1, W.2.1, Function.update W.2.2 x o)
  get_set W o := by simp
  set_set W o o' := by simp
  set_get W := by simp

variable (M) in
/-- The Kraus operator of programming a cell to `v`, with outcome `r` (old database content and old
hardwired value), with the database part `Rd`. -/
noncomputable def progMat {Y : Type} [DecidableEq Y] (C : HwCell X Z Y) (v : Y)
    (Rd : Option Y → Matrix (DbReg X Z) (DbReg X Z) ℂ) (r : Option Y × Option Y) :
    Matrix (HwReg X Z M) (HwReg X Z M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ C.get b.1 = r.2) (fun b ↦ (C.set b.1 (some v), b.2))
    fun _ ↦ Rd r.1

section prog

variable {Y : Type} [Fintype Y] [DecidableEq Y] (L : Hw X Z) (C : HwCell X Z Y) (v : Y)
  (hle : ∀ W, HwLe W L → HwLe (C.set W (some v)) L)
  (Rd : Option Y → Matrix (DbReg X Z) (DbReg X Z) ℂ)
  (hRd : ∀ o, Rd o * offProj L = if none = o then offProj L else 0)

omit [Fintype Y] in
include hle hRd in
/-- **Programming a cell of `L` with its value, between the two maps.** -/
theorem hwKraus_mul_progMat_mul_goodProj (W : Hw X Z) (r : Option Y × Option Y) :
    hwKraus M L W * progMat M C v Rd r * goodProj M L =
      if r.1 = none ∧ C.get W = some v then hwKraus M L (C.set W r.2) else 0 := by
  rw [Matrix.mul_assoc, progMat, goodProj, clsKraus_mul_clsKraus, hwKraus,
    clsKraus_mul_clsKraus]
  by_cases hr : r.1 = none ∧ C.get W = some v
  · rw [ite_eq_left hr]
    refine clsKraus_congr (fun b ↦ ?_) (fun _ _ ↦ rfl) fun b _ ↦ ?_
    · dsimp only [id]
      constructor
      · rintro ⟨⟨hb, hg⟩, hs, -⟩
        have e : b.1 = C.set W r.2 := by rw [← hs, C.set_set, ← hg, C.set_get]
        exact ⟨e, e ▸ hb⟩
      · rintro ⟨hb, hl⟩
        have hb' : HwLe b.1 L := by rw [hb]; exact hl
        have hs : C.set b.1 (some v) = W := by rw [hb, C.set_set, ← hr.2, C.set_get]
        refine ⟨⟨hb', by rw [hb, C.get_set]⟩, hs, ?_⟩
        rw [← hs]
        exact hle _ hb'
    · rw [hRd, ite_eq_left hr.1.symm, offProj_mul_self]
  · rw [ite_eq_right hr]
    refine clsKraus_eq_zero fun b hb ↦ ?_
    have hs : C.set b.1 (some v) = W := hb.2.1
    rw [hRd]
    by_cases h1 : none = r.1
    · exact absurd ⟨h1.symm, by rw [← hs, C.get_set]⟩ hr
    · rw [ite_eq_right h1, Matrix.mul_zero]

omit [Fintype Y] in
include hle hRd in
/-- Programming a cell of `L` with its value keeps the states runtime 1 reaches. -/
theorem goodProj_mul_progMat_mul_goodProj (r : Option Y × Option Y) :
    goodProj M L * progMat M C v Rd r * goodProj M L = progMat M C v Rd r * goodProj M L := by
  rw [Matrix.mul_assoc, progMat, goodProj, clsKraus_mul_clsKraus, clsKraus_mul_clsKraus]
  refine clsKraus_congr (fun b ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, hle _ h.1⟩⟩) (fun _ _ ↦ rfl)
    fun b _ ↦ ?_
  rw [hRd]
  split_ifs
  · exact offProj_mul_self L
  · exact Matrix.mul_zero _

/-- Reindexing a sum by the old value of a cell set to `v`. -/
theorem sum_reindex_cell {β : Type} [AddCommMonoid β] (F : Hw X Z → β) :
    ∑ r : Option Y × Option Y, ∑ W,
        (if r.1 = none ∧ C.get W = some v then F (C.set W r.2) else 0) = ∑ W, F W := by
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single none fun o ho ↦ by simp [ho]]
  simp only [true_and]
  have key : ∀ o : Option Y, ∑ W, (if C.get W = some v then F (C.set W o) else 0) =
      ∑ W, if C.get W = o then F W else 0 := fun o ↦ by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun W ↦ C.set W o) (fun W ↦ C.set W (some v)) ?_ ?_ ?_ ?_
      fun _ _ ↦ rfl
    · intro W _
      simp [C.get_set]
    · intro W _
      simp [C.get_set]
    · intro W hW
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
      rw [C.set_set, ← hW, C.set_get]
    · intro W hW
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
      rw [C.set_set, ← hW, C.set_get]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  rw [Finset.sum_ite_eq]
  simp

include hle hRd in
/-- **A program call of a cell of `L` with its value, after the states runtime 1 reaches, is
invisible to `forget`.** -/
theorem sum_prog {A : Type} [Fintype A] [DecidableEq A]
    (ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ) :
    ∑ r : Option Y × Option Y, (forget M L).amplifyLeft A
        ((MatrixMap.conj (progMat M C v Rd r)).amplifyLeft A ((good M L).amplifyLeft A ρ)) =
      (forget M L).amplifyLeft A ρ := by
  have e : ∀ r W, MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ hwKraus M L W)
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ progMat M C v Rd r)
        (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ goodProj M L) ρ)) =
      if r.1 = none ∧ C.get W = some v then
        MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ hwKraus M L (C.set W r.2)) ρ else 0 := by
    intro r W
    have h3 : ∀ (K₁ K₂ K₃ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ),
        MatrixMap.conj K₁ (MatrixMap.conj K₂ (MatrixMap.conj K₃ ρ)) =
          MatrixMap.conj (K₁ * K₂ * K₃) ρ := fun K₁ K₂ K₃ ↦ by
      simp only [MatrixMap.conj_apply, conjTranspose_mul, Matrix.mul_assoc]
    rw [h3, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
      hwKraus_mul_progMat_mul_goodProj L C v hle Rd hRd]
    split_ifs
    · rfl
    · rw [kronecker_zero, MatrixMap.conj_zero, LinearMap.zero_apply]
  simp only [forget_amplifyLeft, good_amplifyLeft, MatrixMap.amplifyLeft_conj,
    LinearMap.sum_apply, e]
  exact sum_reindex_cell C v fun W ↦ MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ hwKraus M L W) ρ

omit [Fintype Y] in
include hle hRd in
theorem good_prog {A : Type} [Fintype A] [DecidableEq A] (r : Option Y × Option Y)
    (ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ) :
    (good M L).amplifyLeft A ((MatrixMap.conj (progMat M C v Rd r)).amplifyLeft A
        ((good M L).amplifyLeft A ρ)) =
      (MatrixMap.conj (progMat M C v Rd r)).amplifyLeft A ((good M L).amplifyLeft A ρ) := by
  have h2 : ∀ (K₁ K₂ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ)
      (σ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ),
      MatrixMap.conj K₁ (MatrixMap.conj K₂ σ) = MatrixMap.conj (K₁ * K₂) σ := fun K₁ K₂ σ ↦ by
    rw [MatrixMap.conj_mul, LinearMap.comp_apply]
  simp only [good_amplifyLeft, MatrixMap.amplifyLeft_conj, h2, ← mul_kronecker_mul,
    Matrix.one_mul]
  rw [← Matrix.mul_assoc, goodProj_mul_progMat_mul_goodProj L C v hle Rd hRd]

end prog

theorem hwLe_set_cellH {L : Hw X Z} {z : Z} {v : X} (hv : L.1 z = some v) (W : Hw X Z)
    (h : HwLe W L) : HwLe ((cellH z).set W (some v)) L := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun z' ↦ ?_, h₂, h₃⟩
  by_cases hz : z' = z
  · subst hz
    simp [cellH, hv]
  · simpa [cellH, Function.update_of_ne hz] using h₁ z'

theorem hwLe_set_cellK {L : Hw X Z} {x : X} {v : Z} (hv : L.2.1 x = some v) (W : Hw X Z)
    (h : HwLe W L) : HwLe ((cellK x).set W (some v)) L := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨h₁, fun x' ↦ ?_, h₃⟩
  by_cases hx : x' = x
  · subst hx
    simp [cellK, hv]
  · simpa [cellK, Function.update_of_ne hx] using h₂ x'

theorem hwLe_set_cellK' {L : Hw X Z} {x : X} {v : Z} (hv : L.2.2 x = some v) (W : Hw X Z)
    (h : HwLe W L) : HwLe ((cellK' x).set W (some v)) L := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨h₁, h₂, fun x' ↦ ?_⟩
  by_cases hx : x' = x
  · subst hx
    simp [cellK', hv]
  · simpa [cellK', Function.update_of_ne hx] using h₃ x'

theorem discardH_mul_offProj {L : Hw X Z} {z : Z} {v : X} (hv : L.1 z = some v) (o : Option X) :
    (cellDiscard z o ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ)) * offProj L =
      if none = o then offProj L else 0 := by
  refine mul_offProj_of L _ _ fun D' D hD ↦ ?_
  have hz : D.1 z = none := (hD.1 z).resolve_left (by simp [hv])
  have hu : Function.update D.1 z none = D.1 := by rw [Function.update_eq_self_iff, hz]
  simp only [kroneckerMap_apply, cellDiscard, of_apply, Matrix.one_apply, hz, hu]
  by_cases hDD : D' = D
  · subst hDD
    simp
  · by_cases h1 : D'.1 = D.1
    · have h2 : ¬ D'.2 = D.2 := fun h2 ↦ hDD (Prod.ext h1 h2)
      simp [h2, hDD]
    · simp [h1, hDD]

theorem discardK_mul_offProj {L : Hw X Z} {x : X} {v : Z} (hv : L.2.1 x = some v) (o : Option Z) :
    ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      (cellDiscard x o ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))) * offProj L =
      if none = o then offProj L else 0 := by
  refine mul_offProj_of L _ _ fun D' D hD ↦ ?_
  have hx : D.2.1 x = none := (hD.2.1 x).resolve_left (by simp [hv])
  have hu : Function.update D.2.1 x none = D.2.1 := by rw [Function.update_eq_self_iff, hx]
  simp only [kroneckerMap_apply, cellDiscard, of_apply, Matrix.one_apply, hx, hu]
  by_cases hDD : D' = D
  · subst hDD
    simp
  · by_cases h0 : D'.1 = D.1
    · by_cases h1 : D'.2.1 = D.2.1
      · have h2 : ¬ D'.2.2 = D.2.2 := fun h2 ↦ hDD (Prod.ext h0 (Prod.ext h1 h2))
        simp [h2, hDD]
      · simp [h1, hDD]
    · simp [h0, hDD]

theorem discardK'_mul_offProj {L : Hw X Z} {x : X} {v : Z} (hv : L.2.2 x = some v)
    (o : Option Z) :
    ((1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellDiscard x o)) * offProj L =
      if none = o then offProj L else 0 := by
  refine mul_offProj_of L _ _ fun D' D hD ↦ ?_
  have hx : D.2.2 x = none := (hD.2.2 x).resolve_left (by simp [hv])
  have hu : Function.update D.2.2 x none = D.2.2 := by rw [Function.update_eq_self_iff, hx]
  simp only [kroneckerMap_apply, cellDiscard, of_apply, Matrix.one_apply, hx, hu]
  by_cases hDD : D' = D
  · subst hDD
    simp
  · by_cases h0 : D'.1 = D.1
    · by_cases h1 : D'.2.1 = D.2.1
      · have h2 : ¬ D'.2.2 = D.2.2 := fun h2 ↦ hDD (Prod.ext h0 (Prod.ext h1 h2))
        simp [h2, hDD]
      · simp [h1, hDD]
    · simp [h0, hDD]

/-- The cells a program port may program: those of `L`, with their `L` values. -/
def ProgOf (L : Hw X Z) : HwProg X Z → Prop
  | .programH z v => L.1 z = some v
  | .programK x v => L.2.1 x = some v
  | .programK' x v => L.2.2 x = some v

/-- The Kraus operators of the program ports on the hardwired register. -/
noncomputable def progK : (c : HwProg X Z) → c.Result → Matrix (HwReg X Z M) (HwReg X Z M) ℂ
  | .programH z v, r => programKrausH z v r
  | .programK x v, r => programKrausK x v r
  | .programK' x v, r => programKrausK' x v r

omit [Fintype M] in
theorem hwProgKraus_eq (c : HwProg X Z) (r : c.Result) :
    hwProgKraus (M := M) c r = (1 : Matrix Unit Unit ℂ) ⊗ₖ progK c r := by
  cases c <;> rfl

instance (c : HwProg X Z) : Fintype c.Result := by
  cases c <;> exact inferInstanceAs (Fintype (Option _ × Option _))

/-- **A program call of a cell of `L` with its value, on the states runtime 1 reaches, is
invisible to `forget`.** -/
theorem sum_progK (L : Hw X Z) (c : HwProg X Z) (hc : ProgOf L c) {A : Type} [Fintype A]
    [DecidableEq A] (ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ) :
    ∑' r : c.Result, (forget M L).amplifyLeft A
        ((MatrixMap.conj (progK c r)).amplifyLeft A ((good M L).amplifyLeft A ρ)) =
      (forget M L).amplifyLeft A ρ := by
  rw [tsum_fintype]
  cases c with
  | programH z v =>
    exact sum_prog L (cellH z) v (hwLe_set_cellH hc) _ (discardH_mul_offProj hc) ρ
  | programK x v =>
    exact sum_prog L (cellK x) v (hwLe_set_cellK hc) _ (discardK_mul_offProj hc) ρ
  | programK' x v =>
    exact sum_prog L (cellK' x) v (hwLe_set_cellK' hc) _ (discardK'_mul_offProj hc) ρ

theorem good_progK (L : Hw X Z) (c : HwProg X Z) (hc : ProgOf L c) (r : c.Result) {A : Type}
    [Fintype A] [DecidableEq A] (ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ) :
    (good M L).amplifyLeft A ((MatrixMap.conj (progK c r)).amplifyLeft A
        ((good M L).amplifyLeft A ρ)) =
      (MatrixMap.conj (progK c r)).amplifyLeft A ((good M L).amplifyLeft A ρ) := by
  cases c with
  | programH z v =>
    exact good_prog L (cellH z) v (hwLe_set_cellH hc) _ (discardH_mul_offProj hc) r ρ
  | programK x v =>
    exact good_prog L (cellK x) v (hwLe_set_cellK hc) _ (discardK_mul_offProj hc) r ρ
  | programK' x v =>
    exact good_prog L (cellK' x) v (hwLe_set_cellK' hc) _ (discardK'_mul_offProj hc) r ρ

/-! ## The sponge ports -/

variable [AddCommGroup X] [AddCommGroup Z]

/-- The block of a sponge port of the hardwired runtime at the classical data `b`. -/
noncomputable def blk (i : SpongePort) (b : Hw X Z × M) :
    Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ :=
  labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1) false *
      (spongeCompressed X Z).U i +
    hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)

/-- The sponge ports of runtime 1 on blocks: those of the hardwired runtime at the view over
`L`. -/
theorem spongeHardwired1_U_eq (L : Hw X Z) (m₀ : M) (i : SpongePort) :
    (spongeHardwired1 X Z L m₀).U i =
      liftBlocks (hwSplit X Z M (spongeIn X Z i)) fun b ↦ blk i (hwView b.1 L, b.2) := by
  cases i
  · change hwPort _ = _
    unfold blk
    rw [hwPort_eq_liftBlocks, spongeCompressed_U_h]
    congr 1
    funext b
    exact conj_tableOracle_getD (compressDbs X Z) compressDbs_mul_self
      (fun D : DbReg X Z ↦ D.1.lookup) (hwView b.1 L).1
  · change hwPort _ = _
    unfold blk
    rw [hwPort_eq_liftBlocks, spongeCompressed_U_k]
    congr 1
    funext b
    exact conj_tableOracle_getD (compressDbs X Z) compressDbs_mul_self
      (fun D : DbReg X Z ↦ D.2.1.lookup) (hwView b.1 L).2.1
  · change hwPort _ = _
    unfold blk
    rw [hwPort_eq_liftBlocks, spongeCompressed_U_k']
    congr 1
    funext b
    exact conj_tableOracle_getD (compressDbs X Z) compressDbs_mul_self
      (fun D : DbReg X Z ↦ D.2.2.lookup) (hwView b.1 L).2.2

omit [Fintype M] [DecidableEq M] in
/-- **The hardwired cells' database stays.** A nonzero entry of a block of the hardwired runtime
at `L` joins databases that are empty on the cells of `L` together. -/
theorem dbOff_iff_of_blk_ne_zero (L : Hw X Z) (m : M) (i : SpongePort) {a a' : spongeIn X Z i}
    {D D' : DbReg X Z} (h : blk i (L, m) (a', D') (a, D) ≠ 0) : DbOff L D' ↔ DbOff L D := by
  by_cases hDD : D' = D
  · rw [hDD]
  simp only [blk, Matrix.add_apply, labelProjector, diagonal_mul, kroneckerMap_apply,
    Matrix.one_apply, hDD, ↓reduceIte, mul_zero, add_zero] at h
  have hm : hwMaskFn L i a' = false := by
    by_contra hm
    simp [hm] at h
  have hO : (spongeCompressed X Z).U i (a', D') (a, D) ≠ 0 := right_ne_zero_of_mul h
  obtain ⟨hc, hD⟩ := eraseCell_of_spongeCompressed_U_ne_zero i a a' D D' hO
  cases i
  · simp only [eraseCell, Prod.mk.injEq] at hD
    obtain ⟨hD1, hD2, hD3⟩ := hD
    have hcell : ∀ F : Database Z X, Function.update F (a' : Z × X).1 none =
        Function.update F (a : Z × X).1 none := fun F ↦ by
      simpa [eraseCell] using congrArg Prod.fst (congrFun hc (F, D.2.1, D.2.2))
    unfold DbOff
    rw [hD2, hD3, off_iff_of_update hD1 hcell (eq_none_of_isSome_eq_false hm)]
  · simp only [eraseCell, Prod.mk.injEq] at hD
    obtain ⟨hD1, hD2, hD3⟩ := hD
    have hcell : ∀ F : Database X Z, Function.update F (a' : X × Z).1 none =
        Function.update F (a : X × Z).1 none := fun F ↦ by
      simpa [eraseCell] using congrArg (·.2.1) (congrFun hc (D.1, F, D.2.2))
    unfold DbOff
    rw [hD1, hD3, off_iff_of_update hD2 hcell (eq_none_of_isSome_eq_false hm)]
  · simp only [eraseCell, Prod.mk.injEq] at hD
    obtain ⟨hD1, hD2, hD3⟩ := hD
    have hcell : ∀ F : Database X Z, Function.update F (a' : X × Z).1 none =
        Function.update F (a : X × Z).1 none := fun F ↦ by
      simpa [eraseCell] using congrArg (·.2.2) (congrFun hc (D.1, D.2.1, F))
    unfold DbOff
    rw [hD1, hD2, off_iff_of_update hD3 hcell (eq_none_of_isSome_eq_false hm)]

omit [Fintype M] [DecidableEq M] in
theorem blk_comm (L : Hw X Z) (m : M) (i : SpongePort) :
    ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ offProj L) * blk i (L, m) =
      blk i (L, m) * ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ offProj L) := by
  rw [one_kronecker_offProj]
  exact diagonal_ind_mul_comm _ _ fun q' q h ↦ dbOff_iff_of_blk_ne_zero L m i h

/-- **A sponge port of runtime 1 and that of S5 intertwine through the hardwired cells.** -/
theorem hwKraus_mul_U (L W : Hw X Z) (m₀ : M) (i : SpongePort) :
    ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ hwKraus M L W) *
        (spongeHardwired1 X Z L m₀).U i =
      (spongeHardwired X Z L m₀).U i *
        ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ hwKraus M L W) := by
  rw [spongeHardwired1_U_eq, spongeHardwired_U]
  exact one_kronecker_clsKraus_mul_liftBlocks _ _ _ _ _ fun b hb ↦ by
    rw [hb.1, hwView_eq_of_hwLe hb.2]
    exact blk_comm L b.2 i

/-- A sponge port of runtime 1 keeps the states it reaches. -/
theorem goodProj_mul_U (L : Hw X Z) (m₀ : M) (i : SpongePort) :
    ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ goodProj M L) *
        (spongeHardwired1 X Z L m₀).U i =
      (spongeHardwired1 X Z L m₀).U i *
        ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ goodProj M L) := by
  rw [spongeHardwired1_U_eq]
  exact one_kronecker_clsKraus_mul_liftBlocks _ _ _ _ _ fun b hb ↦ by
    dsimp only [id]
    rw [hwView_eq_of_hwLe hb]
    exact blk_comm L b.2 i

/-! ## The runtimes -/

variable [Nonempty X] [Nonempty Z]

variable (X Z) in
/-- **S5's runtime 1** at `L` (`runtimeS5_eq`), with its register and initial state written out. -/
@[reducible]
noncomputable def runtimeS5 (L : Hw X Z) (m₀ : M) : QuantumRuntime (hwReadSpec X Z M) where
  D := QReg.of (HwReg X Z M)
  init := SubState.basis ((Database.empty, Database.empty, Database.empty), L, m₀)
  step := (spongeHardwiredReadRuntime X Z L m₀).step

omit [Nonempty X] [Nonempty Z] in
theorem runtimeS5_eq (L : Hw X Z) (m₀ : M) :
    runtimeS5 X Z L m₀ = spongeHardwiredReadRuntime X Z L m₀ :=
  rfl

variable (X Z) in
/-- The sponge and read ports of the hybrid's runtime 1. -/
@[reducible]
noncomputable def runtime1Read (L : Hw X Z) (m₀ : M) : QuantumRuntime (hwReadSpec X Z M) where
  D := QReg.of (HwReg X Z M)
  init := initHw X Z m₀
  step i := (runtime1 X Z L m₀).step (.inl i)

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem forget_comp_branch (L : Hw X Z) {P : Type} [Fintype P] [DecidableEq P]
    (K₁ K₂ : Matrix (P × HwReg X Z M) (P × HwReg X Z M) ℂ)
    (h : ∀ W, ((1 : Matrix P P ℂ) ⊗ₖ hwKraus M L W) * K₁ =
      K₂ * ((1 : Matrix P P ℂ) ⊗ₖ hwKraus M L W)) :
    MatrixMap.conj K₂ ∘ₗ (forget M L).amplifyLeft P =
      (forget M L).amplifyLeft P ∘ₗ MatrixMap.conj K₁ := by
  rw [forget_amplifyLeft]
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
    h W]

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem good_comp_branch (L : Hw X Z) {P : Type} [Fintype P] [DecidableEq P]
    (K : Matrix (P × HwReg X Z M) (P × HwReg X Z M) ℂ)
    (h : ((1 : Matrix P P ℂ) ⊗ₖ goodProj M L) * K = K * ((1 : Matrix P P ℂ) ⊗ₖ goodProj M L)) :
    MatrixMap.conj K ∘ₗ (good M L).amplifyLeft P = (good M L).amplifyLeft P ∘ₗ MatrixMap.conj K := by
  rw [good_amplifyLeft, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul, h]

/-- The sponge and read ports of runtime 1 and S5 intertwine through `forget`. -/
theorem intertwines_forget_step (L : Hw X Z) (m₀ : M) (i : (hwReadSpec X Z M).Port) :
    DSubInstrument.Intertwines ((forget M L).amplifyLeft ((hwReadSpec X Z M).In i))
      (fun _ ↦ (forget M L).amplifyLeft ((hwReadSpec X Z M).Out i))
      ((runtime1Read X Z L m₀).step i) ((runtimeS5 X Z L m₀).step i) := by
  intro r
  rcases i with i | c
  · change MatrixMap.conj ((spongeHardwired X Z L m₀).U i) ∘ₗ _ =
      _ ∘ₗ MatrixMap.conj ((spongeHardwired1 X Z L m₀).U i)
    exact forget_comp_branch L _ _ fun W ↦ hwKraus_mul_U L W m₀ i
  · have h1 : ((runtime1Read X Z L m₀).step (.inr c)).branch r =
        MatrixMap.conj (hwReadKraus1 L c r) := runtime1_branch L m₀ (.inl (.inr c)) r
    have h2 : ((runtimeS5 X Z L m₀).step (.inr c)).branch r = MatrixMap.conj (hwReadKraus c r) :=
      hwReadStep_branch c r
    rw [h1, h2]
    exact forget_comp_branch L _ _ fun W ↦ hwKraus_mul_hwReadKraus1 L W c r

/-- The sponge and read ports of runtime 1 keep the states it reaches. -/
theorem intertwines_good_step (L : Hw X Z) (m₀ : M) (i : (hwReadSpec X Z M).Port) :
    DSubInstrument.Intertwines ((good M L).amplifyLeft ((hwSpec X Z M).In (.inl i)))
      (fun _ ↦ (good M L).amplifyLeft ((hwSpec X Z M).Out (.inl i)))
      ((runtime1 X Z L m₀).step (.inl i)) ((runtime1 X Z L m₀).step (.inl i)) := by
  intro r
  rw [runtime1_branch]
  rcases i with i | c
  · exact good_comp_branch L _ (goodProj_mul_U L m₀ i)
  · exact good_comp_branch L _ (goodProj_mul_hwReadKraus1 L c r)

/-- A relabelling to a port's register beside `H`, a block on `H` written on the port's
one-point registers, and the relabellings back: the block beside the register. -/
theorem relabel_frame_step {A E I O H : Type} [Fintype A] [DecidableEq A] [Fintype E]
    [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O] [Fintype H]
    [DecidableEq H] [Unique I] [Unique O] (ℓ : A ≃ I × E) (e : O × E ≃ A)
    (he : ∀ a, e (default, (ℓ a).2) = a) (K : Matrix (O × H) (I × H) ℂ) (K' : Matrix H H ℂ)
    (hK : ∀ o i h h', K (o, h) (i, h') = K' h h') (ρ : Matrix (A × H) (A × H) ℂ) :
    ((SubInstrument.relabel e).branch ()).amplify H
        ((SubInstrument.relabel (queryEquivOut O H E)).branch ()
          ((MatrixMap.conj K).amplify E
            ((SubInstrument.relabel (queryEquivIn ℓ H)).branch () ρ))) =
      (MatrixMap.conj K').amplifyLeft A ρ := by
  set g : I × H ≃ O × H := (Equiv.ofUnique I O).prodCongr (Equiv.refl H) with hg
  have hKg : MatrixMap.conj K =
      (SubInstrument.relabel g).branch () ∘ₗ (MatrixMap.conj K').amplifyLeft I := by
    rw [SubInstrument.branch_relabel, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul]
    congr 1
    ext ⟨o, h⟩ ⟨i, h'⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_unique,
      Finset.sum_eq_single h]
    · have hi : i = default := Subsingleton.elim _ _
      have ho : o = default := Subsingleton.elim _ _
      subst hi ho
      simp [hg, hK, basisMatrix_apply, kroneckerMap_apply]
    · intro h₁ _ hh
      simp [hg, basisMatrix_apply, Ne.symm hh]
    · simp
  have hInt := LinearMap.congr_fun (intertwines_relabel_queryEquivIn (MatrixMap.conj K') ℓ ()) ρ
  simp only [LinearMap.comp_apply] at hInt
  rw [hKg, MatrixMap.amplify_comp, LinearMap.comp_apply, ← hInt]
  have he' : ∀ a, e.symm a = (default, (ℓ a).2) := fun a ↦ e.symm_apply_eq.mpr (he a).symm
  have hO : ∀ (ε : E) (h : H), (queryEquivOut O H E).symm ((default, ε), h) =
      ((default, h), ε) := fun _ _ ↦ (Equiv.symm_apply_eq _).mpr rfl
  have hgs : ∀ h : H, g.symm (default, h) = (default, h) := fun _ ↦
    (Equiv.symm_apply_eq _).mpr (Prod.ext (Subsingleton.elim _ _) rfl)
  have hIn : ∀ (a : A) (h : H), (queryEquivIn ℓ H).symm ((default, h), (ℓ a).2) = (a, h) :=
    fun a _ ↦ (Equiv.symm_apply_eq _).mpr
      (Prod.ext (Prod.ext (Subsingleton.elim _ _) rfl) rfl)
  ext ⟨a, h⟩ ⟨a', h'⟩
  simp only [MatrixMap.amplify_apply, SubInstrument.relabel_branch_apply, submatrix_apply, he',
    hO, hgs, hIn]

omit [Nonempty X] [Nonempty Z] in
/-- The entries of the program ports of runtime 1. -/
theorem kraus1_apply_inr (L : Hw X Z) (m₀ : M) (c : HwProg X Z)
    (r : (hwSpec X Z M).Result (.inr c)) (o : (hwSpec X Z M).Out (.inr c))
    (i : (hwSpec X Z M).In (.inr c)) (h h' : HwReg X Z M) :
    kraus1 X Z L m₀ (.inr c) r (o, h) (i, h') = progK c r h h' := by
  have e : kraus1 X Z L m₀ (.inr c) r (o, h) (i, h') =
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ progK c r) ((), h) ((), h') := by
    cases c <;> rfl
  rw [e, kroneckerMap_apply, Matrix.one_apply_eq, one_mul]

/-- A program call followed by the relabelling back: the program port's Kraus map beside the
register. -/
theorem relabel_queryStep_prog (L : Hw X Z) (m₀ : M) (c : HwProg X Z) {A E : QReg}
    (ℓ : A ≃ (hwSpec X Z M).In (.inr c) × E) (e : (hwSpec X Z M).Out (.inr c) × E ≃ A)
    (he : ∀ a, e (ℓ a) = a)
    (r : (hwSpec X Z M).Result (.inr c)) (ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ) :
    ((SubInstrument.relabel e).branch ()).amplify (HwReg X Z M)
        (((runtime1 X Z L m₀).queryStep (.inr c) E ℓ).branch r ρ) =
      (MatrixMap.conj (progK c r)).amplifyLeft A ρ := by
  let _ : Unique ((hwSpec X Z M).In (.inr c)) := inferInstanceAs (Unique Unit)
  let _ : Unique ((hwSpec X Z M).Out (.inr c)) := inferInstanceAs (Unique Unit)
  rw [queryStep_branch_apply, DSubInstrument.branch_frame_apply, runtime1_branch]
  exact relabel_frame_step ℓ e
    (fun a ↦ (congrArg e (Prod.ext (Subsingleton.elim _ _) rfl)).trans (he a)) _ (progK c r)
    (kraus1_apply_inr L m₀ c r) ρ

/-! ## Programs with program calls of `L` -/

variable (L : Hw X Z) in
/-- **`DropsTo L x y`**: the program `x` over `hwSpec` is `y` over `hwReadSpec` with program
calls inserted, each of a cell of `L` with its `L` value (`ProgOf L c`), each followed by the
relabelling `e` back to the register before the call, and with any continuation after it. -/
inductive DropsTo {Ω : QReg → Type w} : {A : QReg} →
    QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω A →
      QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A → Prop
  | pure {A : QReg} (y : Ω A) : DropsTo (QuantumComp.pure y) (QuantumComp.pure y)
  | prim {A : QReg} (o : LocalSig.instruments.{0}.Op A)
      {k : (b : LocalSig.instruments.{0}.Outcome o) →
        QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω (LocalSig.instruments.next o b)}
      {k' : (b : LocalSig.instruments.{0}.Outcome o) →
        QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω
          (LocalSig.instruments.next o b)}
      (h : ∀ b, DropsTo (k b) (k' b)) :
      DropsTo (QuantumComp.primBind o k) (QuantumComp.primBind o k')
  | query {A : QReg} (i : (hwReadSpec X Z M).Port) (E : QReg)
      (ℓ : A ≃ (hwReadSpec X Z M).In i × E)
      {k : (hwReadSpec X Z M).Result i →
        QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω
          (QReg.of ((hwReadSpec X Z M).Out i × E))}
      {k' : (hwReadSpec X Z M).Result i →
        QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω
          (QReg.of ((hwReadSpec X Z M).Out i × E))}
      (h : ∀ r, DropsTo (k r) (k' r)) :
      DropsTo (QuantumComp.queryBind (spec := hwSpec X Z M) (.inl i) E ℓ k)
        (QuantumComp.queryBind i E ℓ k')
  | program {A : QReg} (c : HwProg X Z) (hc : ProgOf L c) (E : QReg)
      (ℓ : A ≃ (hwSpec X Z M).In (.inr c) × E) (e : (hwSpec X Z M).Out (.inr c) × E ≃ A)
      (he : ∀ a, e (ℓ a) = a)
      {k : (hwSpec X Z M).Result (.inr c) →
        QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω A}
      {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A}
      (h : ∀ r, DropsTo (k r) y) :
      DropsTo (QuantumComp.queryBind (spec := hwSpec X Z M) (.inr c) E ℓ fun r ↦
        QuantumComp.primBind (L := LocalSig.instruments.{0})
          ⟨Unit, fun _ ↦ A, SubInstrument.relabel e⟩ fun _ ↦ k r) y

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- `DropsTo` is compatible with sequencing. -/
theorem DropsTo.bind {L : Hw X Z} {Ω Ω' : QReg → Type w} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω A}
    {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A} (h : DropsTo L x y)
    {k : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω' u}
    {k' : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω' u}
    (hk : ∀ u l, DropsTo L (k u l) (k' u l)) : DropsTo L (x.bind k) (y.bind k') := by
  induction h with
  | pure y => exact hk _ y
  | prim o _ ih => exact DropsTo.prim o ih
  | query i E ℓ _ ih => exact DropsTo.query i E ℓ ih
  | program c hc E ℓ e he _ ih => exact DropsTo.program c hc E ℓ e he ih

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- `DropsTo` is compatible with sequencing of programs on a fixed final register. -/
theorem DropsTo.bind₂ {L : Hw X Z} {A B C : QReg} {α β : Type}
    {x : QComp (hwSpec X Z M) A B α} {y : QComp (hwReadSpec X Z M) A B α} (h : DropsTo L x y)
    {k : α → QComp (hwSpec X Z M) B C β} {k' : α → QComp (hwReadSpec X Z M) B C β}
    (hk : ∀ a, DropsTo L (k a) (k' a)) : DropsTo L (x.bind k) (y.bind k') :=
  DropsTo.bind h (by rintro u ⟨rfl, a⟩; exact hk a)

/-- The lens sending the ports of `hwReadSpec` to the same ports of `hwSpec`. -/
def liftReadLens : IPFunctor.Lens (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (hwReadSpec X Z M)) (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec X Z M)) where
  toFunA _
    | .prim o => .prim o
    | .query i E ℓ => .query (.inl i) E ℓ
  toFunB _ c := by
    rcases c with o | ⟨i, E, ℓ⟩
    · exact id
    · exact id
  src_eq _ c _ := by
    rcases c with o | ⟨i, E, ℓ⟩ <;> rfl

/-- A program over `hwReadSpec` as a program over `hwSpec`, without program calls. -/
def liftReadProg {Ω : QReg → Type w} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A) :
    QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω A :=
  IPFunctor.IFreeM.mapLens liftReadLens y

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem dropsTo_liftReadProg (L : Hw X Z) {Ω : QReg → Type w} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A) :
    DropsTo L (liftReadProg y) y := by
  induction y using QuantumComp.inductionOn with
  | pure _ y => exact DropsTo.pure y
  | primBind _ o k ih => exact DropsTo.prim o ih
  | queryBind _ i E ℓ k ih => exact DropsTo.query i E ℓ ih

/-- The held register `B` as the trivial register of a program port beside `B`. -/
def progSplit (c : HwProg X Z) (B : QReg) : B ≃ (hwSpec X Z M).In (.inr c) × B :=
  (Equiv.uniqueProd B Unit).symm

/-- The trivial register of a program port beside `B` as `B`. -/
def progJoin (c : HwProg X Z) (B : QReg) : (hwSpec X Z M).Out (.inr c) × B ≃ B :=
  Equiv.uniqueProd B Unit

/-- **One program call beside a held register `B`**: relabel `B` as the port's trivial register
beside `B`, call the port, relabel back, and return the call's result. -/
noncomputable def progCall (c : HwProg X Z) (B : QReg) :
    QComp (hwSpec X Z M) B B ((hwSpec X Z M).Result (.inr c)) :=
  (QuantumComp₂.query (L := LocalSig.instruments) (spec := hwSpec X Z M) (.inr c) B
      (progSplit c B)).bind fun r ↦
    (QComp.act (A := QReg.of ((hwSpec X Z M).Out (.inr c) × B)) (B := B)
      (SubInstrument.relabel (progJoin c B))).bind fun _ ↦ QuantumComp₂.pure r

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
/-- A program call of a cell of `L` with its value, before `x`, is dropped. -/
theorem DropsTo.progCall_bind {L : Hw X Z} (c : HwProg X Z) (hc : ProgOf L c) {B C : QReg}
    {α : Type} {x : QComp (hwSpec X Z M) B C α} {y : QComp (hwReadSpec X Z M) B C α}
    (h : DropsTo L x y) : DropsTo L ((progCall c B).bind fun _ ↦ x) y :=
  DropsTo.program c hc B (progSplit c B) (progJoin c B)
    (fun b ↦ (progJoin (M := M) c B).apply_symm_apply b) fun _ ↦ h

/-! ## Simulation with a precondition -/

section pint

variable {Aτ A' : Type*} [Fintype Aτ] [Fintype A'] {ι : Type*} {B B' : ι → Type*}
  [∀ i, Fintype (B i)] [∀ i, Fintype (B' i)] {κ : Type*} {C C' : κ → Type*}
  [∀ c, Fintype (C c)] [∀ c, Fintype (C' c)]

/-- `p'` after `VA` is `VB` after `p`, on the inputs projected by `PA`. -/
def PInt (PA : MatrixMap Aτ Aτ) (VA : MatrixMap Aτ A') (VB : ∀ i, MatrixMap (B i) (B' i))
    (p : DSubInstrument Aτ ι B) (p' : DSubInstrument A' ι B') : Prop :=
  ∀ i ρ, p'.branch i (VA ρ) = VB i (p.branch i (PA ρ))

/-- `p` keeps the projection: on inputs projected by `PA`, its outputs are projected by `PB`. -/
def Pres (PA : MatrixMap Aτ Aτ) (PB : ∀ i, MatrixMap (B i) (B i)) (p : DSubInstrument Aτ ι B) :
    Prop :=
  ∀ i ρ, PB i (p.branch i (PA ρ)) = p.branch i (PA ρ)

theorem PInt.bind {PA : MatrixMap Aτ Aτ} {VA : MatrixMap Aτ A'} {PB : ∀ i, MatrixMap (B i) (B i)}
    {VB : ∀ i, MatrixMap (B i) (B' i)} {VC : ∀ c, MatrixMap (C c) (C' c)}
    {p : DSubInstrument Aτ ι B} {p' : DSubInstrument A' ι B'}
    {k : (i : ι) → DSubInstrument (B i) κ C} {k' : (i : ι) → DSubInstrument (B' i) κ C'}
    (hp : PInt PA VA VB p p') (hpres : Pres PA PB p) (hk : ∀ i, PInt (PB i) (VB i) VC (k i) (k' i)) :
    PInt PA VA VC (p.bind k) (p'.bind k') := by
  intro c ρ
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply,
    MatrixMap.map_tsum (VC c) (f := fun i ↦ (k i).branch c (p.branch i (PA ρ)))
      ((p.isCPTNIFamily.comp_eval (fun i ↦ (k i).isCPTNIFamily) c).summable_apply (PA ρ))]
  refine tsum_congr fun i ↦ ?_
  rw [hp i ρ, hk i, hpres i ρ]

theorem Pres.bind {PA : MatrixMap Aτ Aτ} {PB : ∀ i, MatrixMap (B i) (B i)}
    {PC : ∀ c, MatrixMap (C c) (C c)} {p : DSubInstrument Aτ ι B}
    {k : (i : ι) → DSubInstrument (B i) κ C} (hp : Pres PA PB p) (hk : ∀ i, Pres (PB i) PC (k i)) :
    Pres PA PC (p.bind k) := by
  intro c ρ
  rw [DSubInstrument.branch_bind_apply,
    MatrixMap.map_tsum (PC c) (f := fun i ↦ (k i).branch c (p.branch i (PA ρ)))
      ((p.isCPTNIFamily.comp_eval (fun i ↦ (k i).isCPTNIFamily) c).summable_apply (PA ρ))]
  refine tsum_congr fun i ↦ ?_
  rw [← hp i ρ, hk i]

theorem PInt.ret (PB : ∀ i, MatrixMap (B i) (B i)) (VB : ∀ i, MatrixMap (B i) (B' i))
    (hV : ∀ j ρ, VB j (PB j ρ) = VB j ρ) (i : ι) :
    PInt (PB i) (VB i) VB (DSubInstrument.ret B i) (DSubInstrument.ret B' i) := by
  intro j ρ
  obtain rfl | hj := eq_or_ne j i
  · rw [DSubInstrument.branch_ret_self, DSubInstrument.branch_ret_self, LinearMap.id_apply,
      LinearMap.id_apply, hV]
  · rw [DSubInstrument.branch_ret_of_ne B hj, DSubInstrument.branch_ret_of_ne B' hj,
      LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

theorem Pres.ret (PB : ∀ i, MatrixMap (B i) (B i))
    (hP : ∀ j ρ, PB j (PB j ρ) = PB j ρ) (i : ι) : Pres (PB i) PB (DSubInstrument.ret B i) := by
  intro j ρ
  obtain rfl | hj := eq_or_ne j i
  · rw [DSubInstrument.branch_ret_self, LinearMap.id_apply, hP]
  · rw [DSubInstrument.branch_ret_of_ne B hj, LinearMap.zero_apply, map_zero]

theorem PInt.of_intertwines {PA : MatrixMap Aτ Aτ} {VA : MatrixMap Aτ A'}
    {PB : ∀ i, MatrixMap (B i) (B i)} {VB : ∀ i, MatrixMap (B i) (B' i)}
    {p : DSubInstrument Aτ ι B} {p' : DSubInstrument A' ι B'}
    (h₁ : DSubInstrument.Intertwines PA PB p p) (h₂ : DSubInstrument.Intertwines VA VB p p')
    (hV : ∀ i ρ, VB i (PB i ρ) = VB i ρ) : PInt PA VA VB p p' := by
  intro i ρ
  have e₁ := LinearMap.congr_fun (h₁ i) ρ
  have e₂ := LinearMap.congr_fun (h₂ i) ρ
  simp only [LinearMap.comp_apply] at e₁ e₂
  rw [e₂, e₁, hV]

theorem Pres.of_intertwines {PA : MatrixMap Aτ Aτ} {PB : ∀ i, MatrixMap (B i) (B i)}
    {p : DSubInstrument Aτ ι B} (h₁ : DSubInstrument.Intertwines PA PB p p)
    (hP : ∀ i ρ, PB i (PB i ρ) = PB i ρ) : Pres PA PB p := by
  intro i ρ
  have e₁ := LinearMap.congr_fun (h₁ i) ρ
  simp only [LinearMap.comp_apply] at e₁
  rw [e₁, hP]

end pint

/-! ## The simulation -/

/-- The run of a program call followed by the relabelling back. -/
theorem run_program_branch (L : Hw X Z) (m₀ : M) {Ω : QReg → Type w} {A : QReg} (c : HwProg X Z)
    (E : QReg) (ℓ : A ≃ (hwSpec X Z M).In (.inr c) × E)
    (e : (hwSpec X Z M).Out (.inr c) × E ≃ A) (he : ∀ a, e (ℓ a) = a)
    (k : (hwSpec X Z M).Result (.inr c) →
      QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω A)
    (q : Σ u, Ω u) (ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ) :
    ((runtime1 X Z L m₀).run .instruments
        (QuantumComp.queryBind (spec := hwSpec X Z M) (.inr c) E ℓ fun r ↦
          QuantumComp.primBind (L := LocalSig.instruments.{0})
            ⟨Unit, fun _ ↦ A, SubInstrument.relabel e⟩ fun _ ↦ k r)).branch q ρ =
      ∑' r, ((runtime1 X Z L m₀).run .instruments (k r)).branch q
        ((MatrixMap.conj (progK c r)).amplifyLeft A ρ) := by
  rw [run_queryBind, DSubInstrument.branch_bind_apply]
  refine tsum_congr fun r ↦ ?_
  rw [run_primBind, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    DSubInstrument.branch_frame_apply, ← relabel_queryStep_prog L m₀ c ℓ e he r ρ]
  rfl

/-- **The simulation**: along `DropsTo`, the run against S5's runtime 1 after `forget` is `forget`
after the run against runtime 1 on the states it reaches, and runtime 1 keeps those states. -/
theorem dropsTo_run (L : Hw X Z) (m₀ : M) {Ω : QReg → Type w} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω A}
    {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A} (h : DropsTo L x y) :
    PInt ((good M L).amplifyLeft A) ((forget M L).amplifyLeft A)
        (fun p : Σ u, Ω u ↦ (forget M L).amplifyLeft p.1)
        ((runtime1 X Z L m₀).run .instruments x) ((runtimeS5 X Z L m₀).run .instruments y) ∧
      Pres ((good M L).amplifyLeft A) (fun p : Σ u, Ω u ↦ (good M L).amplifyLeft p.1)
        ((runtime1 X Z L m₀).run .instruments x) := by
  induction h with
  | pure y =>
    rw [run_pure, run_pure]
    exact ⟨PInt.ret (B := fun p : Σ u, Ω u ↦ p.1 × (runtime1 X Z L m₀).D)
        (B' := fun p : Σ u, Ω u ↦ p.1 × (runtimeS5 X Z L m₀).D) _ _
        (fun (p : Σ u, Ω u) ρ ↦ forget_good (M := M) L p.1 ρ) ⟨_, y⟩,
      Pres.ret (B := fun p : Σ u, Ω u ↦ p.1 × (runtime1 X Z L m₀).D) _
        (fun (p : Σ u, Ω u) ρ ↦ good_good (M := M) L p.1 ρ) ⟨_, y⟩⟩
  | prim o h ih =>
    rw [run_primBind, run_primBind]
    have hG := DSubInstrument.Intertwines.frame_amplifyLeft (LocalSig.Interp.instruments o)
      (good M L)
    have hV := DSubInstrument.Intertwines.frame_amplifyLeft (LocalSig.Interp.instruments o)
      (forget M L)
    have hp := PInt.of_intertwines hG hV fun b ρ ↦ forget_good L _ ρ
    have hpres := Pres.of_intertwines hG fun b ρ ↦ good_good L _ ρ
    exact ⟨PInt.bind hp hpres fun b ↦ (ih b).1, Pres.bind hpres fun b ↦ (ih b).2⟩
  | query i E ℓ h ih =>
    have hG := intertwines_queryStep (R₁ := runtime1 X Z L m₀) (R₂ := runtime1 X Z L m₀)
      (intertwines_good_step L m₀ i) E ℓ
    have hV : DSubInstrument.Intertwines _ _ ((runtime1 X Z L m₀).queryStep (.inl i) E ℓ)
        ((runtimeS5 X Z L m₀).queryStep i E ℓ) :=
      intertwines_queryStep (R₁ := runtime1Read X Z L m₀) (R₂ := runtimeS5 X Z L m₀)
        (intertwines_forget_step L m₀ i) E ℓ
    have hp := PInt.of_intertwines hG hV fun b ρ ↦ forget_good L _ ρ
    have hpres := Pres.of_intertwines hG fun b ρ ↦ good_good L _ ρ
    exact ⟨PInt.bind hp hpres fun r ↦ (ih r).1, Pres.bind hpres fun r ↦ (ih r).2⟩
  | @program A c hc E ℓ e he k y h ih =>
    have : Finite ((hwSpec X Z M).Result (.inr c)) := inferInstanceAs (Finite c.Result)
    have hsum : ∀ (q : Σ u, Ω u) ρ, Summable fun r : (hwSpec X Z M).Result (.inr c) ↦
        ((runtime1 X Z L m₀).run .instruments (k r)).branch q
          ((MatrixMap.conj (progK c r)).amplifyLeft A ρ) := fun _ _ ↦ Summable.of_finite
    have hpre : ∀ (r : (hwSpec X Z M).Result (.inr c)) ρ,
        (MatrixMap.conj (progK c r)).amplifyLeft A ((good M L).amplifyLeft A ρ) =
          (good M L).amplifyLeft A ((MatrixMap.conj (progK c r)).amplifyLeft A
            ((good M L).amplifyLeft A ρ)) := fun r ρ ↦ (good_progK L c hc r ρ).symm
    refine ⟨fun q ρ ↦ ?_, fun q ρ ↦ ?_⟩
    · rw [run_program_branch L m₀ c E ℓ e he k q, MatrixMap.map_tsum _ (hsum q _)]
      have e1 : ∀ r : (hwSpec X Z M).Result (.inr c),
          (forget M L).amplifyLeft q.1 (((runtime1 X Z L m₀).run .instruments (k r)).branch q
            ((MatrixMap.conj (progK c r)).amplifyLeft A ((good M L).amplifyLeft A ρ))) =
          ((runtimeS5 X Z L m₀).run .instruments y).branch q ((forget M L).amplifyLeft A
            ((MatrixMap.conj (progK c r)).amplifyLeft A ((good M L).amplifyLeft A ρ))) := by
        intro r
        rw [hpre r ρ, ← (ih r).1 q]
        rw [← hpre r ρ]
      simp only [e1]
      have hsum2 : Summable fun r : (hwSpec X Z M).Result (.inr c) ↦ (forget M L).amplifyLeft A
          ((MatrixMap.conj (progK c r)).amplifyLeft A ((good M L).amplifyLeft A ρ)) :=
        Summable.of_finite
      rw [← MatrixMap.map_tsum _ hsum2]
      exact congrArg _ (sum_progK L c hc ρ).symm
    · rw [run_program_branch L m₀ c E ℓ e he k q, MatrixMap.map_tsum _ (hsum q _)]
      refine tsum_congr fun r ↦ ?_
      rw [hpre r ρ, (ih r).2 q]

/-- **The weights of the two runs agree.** -/
theorem trace_jointPost_eq (L : Hw X Z) (m₀ : M) {Ω : QReg → Type w} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω A}
    {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A} (h : DropsTo L x y)
    (ρ : SubState A) (p : Σ u, Ω u) :
    ((runtimeS5 X Z L m₀).jointPost .instruments y ρ p).matrix.trace =
      ((runtime1 X Z L m₀).jointPost .instruments x ρ p).matrix.trace := by
  obtain ⟨hp, hpres⟩ := dropsTo_run L m₀ h
  rw [matrix_jointPost, matrix_jointPost]
  change (((runtimeS5 X Z L m₀).run .instruments y).branch p (ρ.matrix ⊗ₖ
      (SubState.basis (((Database.empty, Database.empty, Database.empty), L, m₀) :
        HwReg X Z M)).matrix)).trace =
    (((runtime1 X Z L m₀).run .instruments x).branch p (ρ.matrix ⊗ₖ
      (SubState.basis (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) :
        HwReg X Z M)).matrix)).trace
  rw [SubState.matrix_basis, SubState.matrix_basis]
  have h0 : ρ.matrix ⊗ₖ Matrix.single (((Database.empty, Database.empty, Database.empty), L, m₀) :
      HwReg X Z M) ((Database.empty, Database.empty, Database.empty), L, m₀) 1 =
      (forget M L).amplifyLeft A (ρ.matrix ⊗ₖ Matrix.single
        (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) : HwReg X Z M)
        ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) 1) := by
    rw [MatrixMap.amplifyLeft_kronecker, forget_single]
  have h1 : (good M L).amplifyLeft A (ρ.matrix ⊗ₖ Matrix.single
      (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) : HwReg X Z M)
      ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) 1) =
      ρ.matrix ⊗ₖ Matrix.single
        (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) : HwReg X Z M)
        ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) 1 := by
    rw [MatrixMap.amplifyLeft_kronecker, good_single]
  rw [h0, hp p, trace_forget, hpres p, h1]

/-- **Runtime 1 of the hybrid is S5's runtime 1 on the programs S8 runs.** A program `x` over
`hwSpec` whose program calls program cells of `L` with their `L` values (`DropsTo L x y`), run
against the hybrid's runtime 1, has the law of the program `y` without them run against S5's
runtime 1 with `L` hardwired. -/
theorem evalDistMap_runtime1_eq_spongeHardwiredReadRuntime (L : Hw X Z) (m₀ : M)
    {Ω : QReg → Type w} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω A}
    {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A} (h : DropsTo L x y)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ] (f : (Σ u, Ω u) → γ) :
    (runtime1 X Z L m₀).evalDistMap .instruments x ρ f =
      (spongeHardwiredReadRuntime X Z L m₀).evalDistMap .instruments y ρ f := by
  rw [← runtimeS5_eq, QuantumRuntime.evalDistMap, QuantumRuntime.evalDistMap]
  congr 1
  funext p
  rw [trace_jointPost_eq L m₀ h ρ p]

end Quantum.Xmss.Assembly

end
