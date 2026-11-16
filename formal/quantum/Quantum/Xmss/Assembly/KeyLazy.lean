module

public import Quantum.Xmss.Assembly.ProgView
public import Quantum.Xmss.Assembly.FullTable

@[expose] public section

/-!
# The fresh `k`, `k'` program flips, averaged over the keys

ProgView's remaining lemma `hk` (`uavg_kTot_le`, in ProgView's shape `uavg_kTot_le_of_gd`): averaged
over the tables, the fresh `k`, `k'` flips `kTot A L` of the game are at most `progCap · 2^-301` plus
`progCap` times the bad fraction of a reparametrization in which the keys `k`, `k'` are coordinates.

* **Target-free flips** (`FlipK`, `FlipK'`, `flipK_facts`, `kfSet`, `kfW`, `kFlip_le_kfW`,
  `kTot_le_kfTot`): a value flipping a state into the event lies in `badAttachK` (resp.
  `badCompleteOutK'`) of the union with the cell emptied, a set depending on the table only through
  `π`; along the game every call has low grade (`progCap + dbGrade ≤ 2^68`), so the flips are at
  most these target-free flips, counted by `uavg_kfSet_le`, `uavg_kfSet'_le` (`2^-301`).
* **Lazy sampling of a key cell** (`KRel`, `totalWeight_tcW_eq_of_krel`): two realized programs
  agreeing command by command until a touched port (here: a `k` port at the cell `y`), from states
  agreeing on the block of register states with `y` free (`Agr`), give equal weights read at the
  touched ports, when those weights read only the block's diagonal. Every port keeps the agreement
  (`agr_runtimeR_step`; a program never frees a cell) and a touched port leaves no mass on the
  block (`agr_runtimeR_step_out`).
* **The game at keys differing in one cell** (`prel_slotPorts_k`, `prel_slotPorts_k'`,
  `krel_gameT`): the template reads the keys only through its slots' round ports; the sponge
  states of a slot's rounds agree up to its first round at the cell (`stateAt_keysK`), so its ports
  agree until its first `k` (resp. `k'`) port at the cell, which carries the keys' values there.
  Hence `totalWeight_kfSet_update`: resampling `k y` to `a` gives the flips of value `a` read in
  the game at `k`.
* **Averaging** (`sum_update_eq`, `sum_le_of_cells`, `sum_two_cells`, `sum_kfTot_le`): summed over
  the keys, cell by cell (`kfW_split`), the resampled flips are `2^-301` times the traces at the
  `k`, `k'` ports, at most `progCap` program calls (`totalWeight_kTrace_le`).

The consumer supplies the reparametrization `e` with the keys as coordinates, its injectivity on a
good set, `hgame` (the game at the table is the template game at the reparametrized public datum,
as MassesR0/GameCongr's `hgame`) and that the reparametrized `π` is the table's.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe w w₁

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

attribute [local instance] badRDec

/-! ## Flip counts uniform in the targets -/

section count

variable {X₁ Z₁ Y₁ : Type} [AddCommGroup X₁] [AddCommGroup Z₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Z₁] [DecidableEq Z₁] {π : Equiv.Perm (X₁ × Z₁)} {out : X₁ → Y₁}
  {tgt : List X₁ → Option Y₁} {D : Dbs X₁ Z₁}

/-- **A fresh `k` value flipping a database into `TargetBad` lies in `badAttachK`**, a set that
does not depend on the targets. -/
theorem mem_badAttachK_of_targetBad (hD : D ∉ TargetBad π out tgt) {x : X₁} (hx : D.k x = none)
    {y : Z₁} (hy : { D with k := Function.update D.k x (some y) } ∈ TargetBad π out tgt) :
    y ∈ badAttachK π D x := by
  by_contra hb
  obtain ⟨hG, hT⟩ := not_mem_targetBad_iff.1 hD
  obtain ⟨hG', htl⟩ := updateK_tails hG hx hb
  rcases hy with h | ⟨s, y₀, hs, hr⟩
  · exact h hG'
  · exact hT s y₀ hs (hr.of_tails (extends_update_k hx) rfl htl)

/-- **A fresh `k'` value flipping a database into `TargetBad` lies in `badCompleteOutK'`**, a set
that does not depend on the targets. -/
theorem mem_badCompleteOutK'_of_targetBad (hD : D ∉ TargetBad π out tgt) {x : X₁}
    (hx : D.k' x = none) {y : Z₁}
    (hy : { D with k' := Function.update D.k' x (some y) } ∈ TargetBad π out tgt) :
    y ∈ badCompleteOutK' π D x := by
  by_contra hb
  obtain ⟨hG, hT⟩ := not_mem_targetBad_iff.1 hD
  obtain ⟨hG', htl⟩ := updateK'_tails hG hx hb
  rcases hy with h | ⟨s, y₀, hs, hr⟩
  · exact h hG'
  · exact hT s y₀ hs (hr.of_tails (extends_update_k' hx) rfl htl)

end count

section flipGen

variable {X₁ Z₁ Y₁ M₁ : Type} [AddCommGroup X₁] [AddCommGroup Z₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Z₁] [DecidableEq Z₁] {π : Equiv.Perm (X₁ × Z₁)} {out : X₁ → Y₁}
  {tgt : Hw X₁ Z₁ → M₁ → List X₁ → Option Y₁} {N : ℕ} {D : DbReg X₁ Z₁} {W : Hw X₁ Z₁} {m : M₁}

variable (π) in
/-- **The target-free facts of a fresh `k` flip** at the cell `x` with value `a`: the cell is not
hardwired, the union with the cell emptied is good, and `a` lies in its `badAttachK`. -/
def FlipK (W : Hw X₁ Z₁) (D : DbReg X₁ Z₁) (x : X₁) (a : Z₁) : Prop :=
  W.2.1 x = none ∧ Good π { union W D with k := Function.update (union W D).k x none } ∧
    a ∈ badAttachK π { union W D with k := Function.update (union W D).k x none } x

variable (π) in
/-- **The target-free facts of a fresh `k'` flip** at the cell `x` with value `a`. -/
def FlipK' (W : Hw X₁ Z₁) (D : DbReg X₁ Z₁) (x : X₁) (a : Z₁) : Prop :=
  W.2.2 x = none ∧ Good π { union W D with k' := Function.update (union W D).k' x none } ∧
    a ∈ badCompleteOutK' π { union W D with k' := Function.update (union W D).k' x none } x

/-- **A fresh `k` flip of a hardwired register** has few hardwired cells and the target-free
facts (none of which depends on the targets). -/
theorem flipK_facts (hanti : TgtAnti tgt) {x : X₁} (hW : W.2.1 x = none) {v : Z₁}
    (hs : (D, W, m) ∉ HwTargetBad π out tgt N)
    (hp : ((D.1, Function.update D.2.1 x none, D.2.2), (W.1, Function.update W.2.1 x (some v),
      W.2.2), m) ∈ HwTargetBad π out tgt N) :
    dbGrade W ≤ N ∧ FlipK π W D x v := by
  have hN : dbGrade W ≤ N := (hwLe_programK hW v).dbGrade_le.trans hp.1
  have hU0 : ({ union W D with k := Function.update (union W D).k x none } : Dbs X₁ Z₁) ∉
      TargetBad π out (tgt W m) :=
    fun h ↦ hs ⟨hN, TargetBad.mono (extendsAll_eraseK _ x) h⟩
  have h2 : union (W.1, Function.update W.2.1 x (some v), W.2.2)
      (D.1, Function.update D.2.1 x none, D.2.2) ∈
      TargetBad π out (tgt (W.1, Function.update W.2.1 x (some v), W.2.2) m) := hp.2
  rw [union_programK] at h2
  exact ⟨hN, hW, (not_mem_targetBad_iff.1 hU0).1, mem_badAttachK_of_targetBad hU0 (by simp)
    (targetBad_mono (hanti _ _ _ (hwLe_programK hW v)) h2)⟩

/-- **A fresh `k'` flip of a hardwired register** has few hardwired cells and the target-free
facts. -/
theorem flipK'_facts (hanti : TgtAnti tgt) {x : X₁} (hW : W.2.2 x = none) {v : Z₁}
    (hs : (D, W, m) ∉ HwTargetBad π out tgt N)
    (hp : ((D.1, D.2.1, Function.update D.2.2 x none), (W.1, W.2.1,
      Function.update W.2.2 x (some v)), m) ∈ HwTargetBad π out tgt N) :
    dbGrade W ≤ N ∧ FlipK' π W D x v := by
  have hN : dbGrade W ≤ N := (hwLe_programK' hW v).dbGrade_le.trans hp.1
  have hU0 : ({ union W D with k' := Function.update (union W D).k' x none } : Dbs X₁ Z₁) ∉
      TargetBad π out (tgt W m) :=
    fun h ↦ hs ⟨hN, TargetBad.mono (extendsAll_eraseK' _ x) h⟩
  have h2 : union (W.1, W.2.1, Function.update W.2.2 x (some v))
      (D.1, D.2.1, Function.update D.2.2 x none) ∈
      TargetBad π out (tgt (W.1, W.2.1, Function.update W.2.2 x (some v)) m) := hp.2
  rw [union_programK'] at h2
  exact ⟨hN, hW, (not_mem_targetBad_iff.1 hU0).1, mem_badCompleteOutK'_of_targetBad hU0 (by simp)
    (targetBad_mono (hanti _ _ _ (hwLe_programK' hW v)) h2)⟩

omit [AddCommGroup X₁] in
/-- **The values of fresh `k` flips at a state**: at most the capacity-scale count of
`badAttachK`, for at most `T` entries in the hardwired and database cells together. -/
theorem card_flipK_le {G T : ℕ} (hπ : PermGood π G) (hT : dbGrade W + dbGrade D ≤ T) {x : X₁}
    (t : Finset Z₁) (ht : ∀ a ∈ t, FlipK π W D x a) (a₀ : Z₁) (ha₀ : a₀ ∈ t) :
    t.card ≤ (T + 1) * ((T + 1) * T + 2 * T) * G :=
  (Finset.card_le_card fun a ha ↦ (ht a ha).2.2).trans (card_badAttachK_le (ht a₀ ha₀).2.1 hπ
    ((size_update_none_le _ _).trans ((size_unionK_le W D).trans hT))
    ((size_unionK'_le W D).trans hT))

omit [AddCommGroup X₁] in
/-- **The values of fresh `k'` flips at a state**: at most the capacity-scale count of
`badCompleteOutK'`. -/
theorem card_flipK'_le {G T : ℕ} (hπ : PermGood π G) (hT : dbGrade W + dbGrade D ≤ T) {x : X₁}
    (t : Finset Z₁) (ht : ∀ a ∈ t, FlipK' π W D x a) (a₀ : Z₁) (ha₀ : a₀ ∈ t) :
    t.card ≤ (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T :=
  (Finset.card_le_card fun a ha ↦ (ht a ha).2.2).trans ((card_badCompleteOutK'_le (ht a₀ ha₀).2.1
    hπ x ((size_unionK_le W D).trans hT)
    ((size_update_none_le _ _).trans ((size_unionK'_le W D).trans hT))).trans
      (Nat.add_le_add_left ((size_unionH_le W D).trans hT) _))

end flipGen

/-! ## Operators agreeing on a block of basis states -/

section agr

variable {α β : Type*}

/-- Two operators agree on the block of the basis states satisfying `P`. -/
def Agr (P : α → Prop) (ρ ρ' : Matrix α α ℂ) : Prop :=
  ∀ a b, P a → P b → ρ a b = ρ' a b

theorem agr_relabel [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P : α → Prop}
    {P' : β → Prop} (e : α ≃ β) (he : ∀ a, P' (e a) ↔ P a) {ρ ρ' : Matrix α α ℂ}
    (h : Agr P ρ ρ') :
    Agr P' ((SubInstrument.relabel e).branch () ρ) ((SubInstrument.relabel e).branch () ρ') := by
  intro a b ha hb
  simp only [SubInstrument.relabel_branch_apply, submatrix_apply]
  exact h _ _ ((he _).1 (by rwa [e.apply_symm_apply])) ((he _).1 (by rwa [e.apply_symm_apply]))

/-- A map beside the labelled factor keeps the agreement. -/
theorem agr_amplify_left {R : Type*} (Φ : MatrixMap α β) {P : R → Prop}
    {ρ ρ' : Matrix (α × R) (α × R) ℂ} (h : Agr (fun p : α × R ↦ P p.2) ρ ρ') :
    Agr (fun p : β × R ↦ P p.2) (Φ.amplify R ρ) (Φ.amplify R ρ') := by
  intro a b ha hb
  simp only [MatrixMap.amplify_apply]
  have hs : ρ.submatrix (·, a.2) (·, b.2) = ρ'.submatrix (·, a.2) (·, b.2) := by
    ext x y
    exact h (x, a.2) (y, b.2) ha hb
  rw [hs]

/-- A map on the labelled factor keeping the agreement keeps it beside an ancilla. -/
theorem agr_amplify_right {E : Type*} {P : α → Prop} {P' : β → Prop} (Φ : MatrixMap α β)
    (hΦ : ∀ σ σ', Agr P σ σ' → Agr P' (Φ σ) (Φ σ')) {ρ ρ' : Matrix (α × E) (α × E) ℂ}
    (h : Agr (fun p : α × E ↦ P p.1) ρ ρ') :
    Agr (fun p : β × E ↦ P' p.1) (Φ.amplify E ρ) (Φ.amplify E ρ') := by
  intro a b ha hb
  simp only [MatrixMap.amplify_apply]
  exact hΦ _ _ (fun x y hx hy ↦ h (x, a.2) (y, b.2) hx hy) a.1 b.1 ha hb

/-- A map whose outputs all agree on the block makes all outputs agree beside an ancilla. -/
theorem agr_amplify_right_out {E : Type*} {P' : β → Prop} (Φ : MatrixMap α β)
    (hΦ : ∀ σ σ', Agr P' (Φ σ) (Φ σ')) (ρ ρ' : Matrix (α × E) (α × E) ℂ) :
    Agr (fun p : β × E ↦ P' p.1) (Φ.amplify E ρ) (Φ.amplify E ρ') := by
  intro a b ha hb
  simp only [MatrixMap.amplify_apply]
  exact hΦ _ _ a.1 b.1 ha hb

theorem agr_traceRight {E : Type*} [Fintype E] {P : α → Prop}
    {ρ ρ' : Matrix (α × E) (α × E) ℂ} (h : Agr (fun p : α × E ↦ P p.1) ρ ρ') :
    Agr P (MatrixMap.traceRight α E ρ) (MatrixMap.traceRight α E ρ') := by
  intro a b ha hb
  simp only [MatrixMap.traceRight_apply]
  exact Finset.sum_congr rfl fun r _ ↦ h (a, r) (b, r) ha hb

/-- **A Kraus map whose nonzero entries lead from the block only into the block** keeps the
agreement. -/
theorem agr_conj [Fintype α] {P : α → Prop} {P' : β → Prop} (K : Matrix β α ℂ)
    (hK : ∀ b a, K b a ≠ 0 → P' b → P a) {ρ ρ' : Matrix α α ℂ} (h : Agr P ρ ρ') :
    Agr P' (MatrixMap.conj K ρ) (MatrixMap.conj K ρ') := by
  intro b b' hb hb'
  simp only [MatrixMap.conj_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a' _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases h1 : K b a = 0
  · simp [h1]
  by_cases h2 : K b' a' = 0
  · simp [h2]
  rw [h a a' (hK b a h1 hb) (hK b' a' h2 hb')]

/-- **A Kraus map leading nowhere into the block** makes all its outputs agree there (with `0`). -/
theorem agr_conj_out [Fintype α] {P' : β → Prop} (K : Matrix β α ℂ)
    (hK : ∀ b a, K b a ≠ 0 → ¬P' b) (ρ ρ' : Matrix α α ℂ) :
    Agr P' (MatrixMap.conj K ρ) (MatrixMap.conj K ρ') := by
  intro b b' hb _
  have h0 : ∀ a, K b a = 0 := fun a ↦ by
    by_contra h
    exact hK b a h hb
  simp only [MatrixMap.conj_apply, Matrix.mul_apply, conjTranspose_apply, h0, zero_mul,
    Finset.sum_const_zero]

end agr

/-! ## Calls of runtime 2 with record ports on the block of a free cell

`Fr` is a property of the hardwired cells that no program port creates (`Fr (progUpdate c W) →
Fr W`), e.g. "the `k` cell `x` is not hardwired". Every port of `runtimeR` keeps the agreement of
operators on the block of the register states with `Fr` (`agr_runtimeR_step`); a port that
destroys `Fr` makes all its outputs agree there (`agr_runtimeR_step_out`). -/

section block

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset HPos × M) (Fr : Hw X Z → Prop)

theorem agr_runtimeR_step (hFr : ∀ c W, Fr (progUpdate c W) → Fr W)
    (i : (recHwSpec X Z HPos M).Port) (r : (recHwSpec X Z HPos M).Result i)
    (σ σ' : Matrix ((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (h : Agr (fun p ↦ Fr p.2.2.1) σ σ') :
    Agr (fun p : (recHwSpec X Z HPos M).Out i × (runtimeR (X := X) (Z := Z) m₀).D ↦ Fr p.2.2.1)
      (((runtimeR m₀).step i).branch r σ) (((runtimeR m₀).step i).branch r σ') := by
  rcases i with ((i | c) | c) | T
  · have hb : ∀ τ, ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r τ =
        MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U i) τ := fun τ ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ i r) τ
    rw [hb, hb]
    refine agr_conj _ (fun q' q hK hq ↦ ?_) h
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m₀ i q.1 q'.1 q.2 q'.2 hK
    rwa [congrArg Prod.fst he] at hq
  · have hb : ∀ τ, ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r τ =
        MatrixMap.conj (hwReadKraus c r) τ := fun τ ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) τ
    rw [hb, hb]
    refine agr_conj _ (fun q' q hK hq ↦ ?_) h
    rwa [hwReadKraus_ne_zero_hw c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK] at hq
  · have hb : ∀ τ, ((runtimeR m₀).step (.inl (.inr c))).branch r τ =
        MatrixMap.conj (hwProgKraus c r) τ := fun τ ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) τ
    rw [hb, hb]
    refine agr_conj _ (fun q' q hK hq ↦ ?_) h
    have he := hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
    rw [congrArg Prod.fst he] at hq
    exact hFr c _ hq
  · refine agr_conj (recKraus T r) (fun q' q hK hq ↦ ?_) h
    rwa [congrArg Prod.fst (recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK)]
      at hq

/-- **A program port destroying `Fr`** makes all its outputs agree on the block. -/
theorem agr_runtimeR_step_out (c : HwProg X Z) (hc : ∀ W, ¬Fr (progUpdate c W))
    (r : c.Result)
    (σ σ' : Matrix ((recHwSpec X Z HPos M).In (.inl (.inr c)) ×
        (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z HPos M).In (.inl (.inr c)) × (runtimeR (X := X) (Z := Z) m₀).D) ℂ) :
    Agr (fun p : (recHwSpec X Z HPos M).Out (.inl (.inr c)) ×
        (runtimeR (X := X) (Z := Z) m₀).D ↦ Fr p.2.2.1)
      (((runtimeR m₀).step (.inl (.inr c))).branch r σ)
      (((runtimeR m₀).step (.inl (.inr c))).branch r σ') := by
  have hb : ∀ τ, ((runtimeR m₀).step (.inl (.inr c))).branch r τ =
      MatrixMap.conj (hwProgKraus c r) τ := fun τ ↦
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) τ
  rw [hb, hb]
  refine agr_conj_out _ (fun q' q hK hq ↦ ?_) _ _
  have he := hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
  rw [congrArg Prod.fst he] at hq
  exact hc _ hq

end block

section queryAgr

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) (P : R.D → Prop)

/-- **A call keeps the agreement** when the port's branch does. -/
theorem agr_queryStep (i : spec.Port) (E : QReg) {A : QReg} (ℓ : A ≃ spec.In i × E)
    (r : spec.Result i)
    (hstep : ∀ σ σ', Agr (fun p : spec.In i × R.D ↦ P p.2) σ σ' →
      Agr (fun p : spec.Out i × R.D ↦ P p.2) ((R.step i).branch r σ) ((R.step i).branch r σ'))
    {ρ ρ' : Matrix (A × R.D) (A × R.D) ℂ} (h : Agr (fun p ↦ P p.2) ρ ρ') :
    Agr (fun p : QReg.of (spec.Out i × E) × R.D ↦ P p.2) ((R.queryStep i E ℓ).branch r ρ)
      ((R.queryStep i E ℓ).branch r ρ') := by
  have he : ∀ τ, (R.queryStep i E ℓ).branch r τ =
      (SubInstrument.relabel (queryEquivOut (spec.Out i) R.D E)).branch ()
        (((R.step i).branch r).amplify E
          ((SubInstrument.relabel (queryEquivIn ℓ R.D)).branch () τ)) :=
    fun τ ↦ queryStep_branch_apply (R := R) i E ℓ r τ
  rw [he, he]
  exact agr_relabel (P := fun p : (spec.Out i × R.D) × E ↦ P p.1.2) _ (fun _ ↦ Iff.rfl)
    (agr_amplify_right _ hstep (agr_relabel _ (fun _ ↦ Iff.rfl) h))

/-- **A call whose port's branch makes all outputs agree** makes all its outputs agree. -/
theorem agr_queryStep_out (i : spec.Port) (E : QReg) {A : QReg} (ℓ : A ≃ spec.In i × E)
    (r : spec.Result i)
    (hstep : ∀ σ σ', Agr (fun p : spec.Out i × R.D ↦ P p.2) ((R.step i).branch r σ)
      ((R.step i).branch r σ'))
    (ρ ρ' : Matrix (A × R.D) (A × R.D) ℂ) :
    Agr (fun p : QReg.of (spec.Out i × E) × R.D ↦ P p.2) ((R.queryStep i E ℓ).branch r ρ)
      ((R.queryStep i E ℓ).branch r ρ') := by
  have he : ∀ τ, (R.queryStep i E ℓ).branch r τ =
      (SubInstrument.relabel (queryEquivOut (spec.Out i) R.D E)).branch ()
        (((R.step i).branch r).amplify E
          ((SubInstrument.relabel (queryEquivIn ℓ R.D)).branch () τ)) :=
    fun τ ↦ queryStep_branch_apply (R := R) i E ℓ r τ
  rw [he, he]
  exact agr_relabel (P := fun p : (spec.Out i × R.D) × E ↦ P p.1.2) _ (fun _ ↦ Iff.rfl)
    (agr_amplify_right_out _ hstep _ _)

/-- The input of a call through a port with a one-point input register: its diagonal at `((), s)`
is the diagonal of the state summed over the program register. -/
theorem callInput_unit_diag {A E : QReg} (ℓ : A ≃ Unit × E) (ρ : Matrix (A × R.D) (A × R.D) ℂ)
    (s : R.D) : callInput ℓ R.D ρ ((), s) ((), s) = ∑ a, ρ (a, s) (a, s) := by
  simp only [callInput, LinearMap.comp_apply, MatrixMap.traceRight_apply,
    SubInstrument.relabel_branch_apply, submatrix_apply]
  exact Fintype.sum_equiv ((Equiv.uniqueProd E Unit).symm.trans ℓ.symm) _ _ fun _ ↦ rfl

end queryAgr

/-! ## Programs agreeing until a touched cell

`KRel tc a a' y y'`: the realized programs `y`, `y'` agree command by command until a program port
whose touch value `tc c` is set; there `y` calls a port of touch value `a`, `y'` one of touch value
`a'`, and their continuations are arbitrary. The weights `tcW tc g` read only the touched ports,
through `g` at the touch value. -/

section krel

variable {M : Type} (tc : HwProg X Z → Option Z)

/-- The touch value of a command: `tc c` at a program port `c`, `none` elsewhere. -/
def cmdTc {A : QReg} : QuantumComp.Cmd LocalSig.instruments.{0} (recHwSpec X Z HPos M) A →
    Option Z
  | .query (.inl (.inr c)) _ _ => tc c
  | _ => none

/-- **Programs agreeing until a touched cell.** -/
def KRel (a a' : Z) {Ω : QReg → Type w} : {A : QReg} →
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos M)) Ω A →
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos M)) Ω A → Prop
  | _, .pure y, y' => y' = .pure y
  | _, .liftBind c next, y' =>
      (cmdTc tc c = some a ∧ ∃ c' next', cmdTc tc c' = some a' ∧ y' = .liftBind c' next') ∨
        (cmdTc tc c = none ∧ ∃ next', y' = .liftBind c next' ∧
          ∀ b, KRel a a' (next b) (next' b))

/-- **Programs without touched ports.** -/
def NoTc {Ω : QReg → Type w} : {A : QReg} →
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos M)) Ω A → Prop
  | _, .pure _ => True
  | _, .liftBind c next => cmdTc tc c = none ∧ ∀ b, NoTc (next b)

variable {tc} {a a' : Z} {Ω : QReg → Type w} {A : QReg}

theorem krel_pure (y : Ω A) :
    KRel tc a a' (QuantumComp.pure (L := LocalSig.instruments.{0})
      (spec := recHwSpec X Z HPos M) y) (QuantumComp.pure y) :=
  rfl

theorem krel_primBind (o : LocalSig.instruments.{0}.Op A)
    {k k' : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω
        (LocalSig.instruments.{0}.next o b)} (hk : ∀ b, KRel tc a a' (k b) (k' b)) :
    KRel tc a a' (QuantumComp.primBind o k) (QuantumComp.primBind o k') :=
  Or.inr ⟨rfl, _, rfl, fun b ↦ hk b.down⟩

theorem krel_queryBind_same (i : (recHwSpec X Z HPos M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    (hi : cmdTc (M := M) tc (.query i E ℓ) = none)
    {k k' : (recHwSpec X Z HPos M).Result i →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω
        (QReg.of ((recHwSpec X Z HPos M).Out i × E))} (hk : ∀ r, KRel tc a a' (k r) (k' r)) :
    KRel tc a a' (QuantumComp.queryBind i E ℓ k) (QuantumComp.queryBind i E ℓ k') :=
  Or.inr ⟨hi, _, rfl, fun r ↦ hk r.down⟩

theorem krel_queryBind_touch (i : (recHwSpec X Z HPos M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E) (i' : (recHwSpec X Z HPos M).Port) (E' : QReg)
    (ℓ' : A ≃ (recHwSpec X Z HPos M).In i' × E')
    (hi : cmdTc (M := M) tc (.query i E ℓ) = some a)
    (hi' : cmdTc (M := M) tc (.query i' E' ℓ') = some a')
    (k : (recHwSpec X Z HPos M).Result i →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω
        (QReg.of ((recHwSpec X Z HPos M).Out i × E)))
    (k' : (recHwSpec X Z HPos M).Result i' →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω
        (QReg.of ((recHwSpec X Z HPos M).Out i' × E'))) :
    KRel tc a a' (QuantumComp.queryBind i E ℓ k) (QuantumComp.queryBind i' E' ℓ' k') :=
  Or.inl ⟨hi, _, _, hi', rfl⟩

theorem krel_primBind_inv {o : LocalSig.instruments.{0}.Op A}
    {k : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω
        (LocalSig.instruments.{0}.next o b)}
    {y' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω A}
    (h : KRel tc a a' (QuantumComp.primBind o k) y') :
    ∃ k', y' = QuantumComp.primBind o k' ∧ ∀ b, KRel tc a a' (k b) (k' b) := by
  rcases h with ⟨h1, -⟩ | ⟨-, next', rfl, hn⟩
  · simp [cmdTc] at h1
  · exact ⟨fun b ↦ next' (ULift.up b), rfl, fun b ↦ hn (ULift.up b)⟩

theorem krel_queryBind_inv {i : (recHwSpec X Z HPos M).Port} {E : QReg}
    {ℓ : A ≃ (recHwSpec X Z HPos M).In i × E}
    {k : (recHwSpec X Z HPos M).Result i →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω
        (QReg.of ((recHwSpec X Z HPos M).Out i × E))}
    {y' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω A}
    (h : KRel tc a a' (QuantumComp.queryBind i E ℓ k) y') :
    (cmdTc tc (.query i E ℓ) = some a ∧ ∃ c' next', cmdTc tc c' = some a' ∧
        y' = IFreeM.liftBind c' next') ∨
      (cmdTc tc (.query i E ℓ) = none ∧ ∃ k', y' = QuantumComp.queryBind i E ℓ k' ∧
        ∀ r, KRel tc a a' (k r) (k' r)) := by
  rcases h with h | ⟨h1, next', rfl, hn⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, fun r ↦ next' (ULift.up r), rfl, fun r ↦ hn (ULift.up r)⟩

theorem krel_refl {y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0}
    (recHwSpec X Z HPos M)) Ω A} (h : NoTc tc y) : KRel tc a a' y y := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ c next ih => exact Or.inr ⟨h.1, next, rfl, fun b ↦ ih b (h.2 b)⟩

theorem krel_bind {Ω' : QReg → Type w₁}
    {x x' : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos M)) Ω A}
    {g g' : ∀ u, Ω u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos M)) Ω' u}
    (hx : KRel tc a a' x x') (hg : ∀ u y, KRel tc a a' (g u y) (g' u y)) :
    KRel tc a a' (x.bind g) (x'.bind g') := by
  induction x using IFreeM.inductionOn with
  | pure _ y =>
    obtain rfl : x' = IFreeM.pure y := hx
    exact hg _ y
  | liftBind _ c next ih =>
    rcases hx with ⟨hc, c', next', hc', rfl⟩ | ⟨hc, next', rfl, hn⟩
    · exact Or.inl ⟨hc, c', _, hc', rfl⟩
    · exact Or.inr ⟨hc, _, rfl, fun b ↦ ih b (hn b)⟩

theorem noTc_bind {Ω' : QReg → Type w₁}
    {x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos M)) Ω A}
    {g : ∀ u, Ω u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos M)) Ω' u}
    (hx : NoTc tc x) (hg : ∀ u y, NoTc tc (g u y)) : NoTc tc (x.bind g) := by
  induction x using IFreeM.inductionOn with
  | pure _ y => exact hg _ y
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem krel_cast {A' : QReg} (e : A = A')
    {y y' : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos M)) Ω A} :
    KRel tc a a' (e ▸ y) (e ▸ y') ↔ KRel tc a a' y y' := by
  subst e
  rfl

theorem krel_bind₂ {B C : QReg} {α β : Type}
    {x x' : QuantumComp₂ LocalSig.instruments.{0} (recHwSpec X Z HPos M) A B α}
    {g g' : α → QuantumComp₂ LocalSig.instruments.{0} (recHwSpec X Z HPos M) B C β}
    (hx : KRel tc a a' x x') (hg : ∀ b, KRel tc a a' (g b) (g' b)) :
    KRel tc a a' (x.bind g) (x'.bind g') := by
  refine krel_bind hx fun u p ↦ ?_
  obtain ⟨e, b⟩ := p
  subst e
  exact hg b

theorem krel_substitute {spec₀ : QuantumOracleSpec.{0, 0}}
    {σ σ' : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos M))}
    (hσ : ∀ A c, KRel tc a a' (σ A c) (σ' A c)) {Ω : QReg → Type}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Ω A) :
    KRel tc a a' (x.substitute σ) (x.substitute σ') := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind, IFreeM.substitute_liftBind]
    exact krel_bind (hσ s c) fun u ans ↦ (krel_cast ans.2).mpr (ih ans.1)

end krel

/-! ## Weights read at the touched ports, and their totals on related programs -/

section tcWeight

variable {M : Type} [Fintype M] [DecidableEq M] (tc : HwProg X Z → Option Z)

/-- **Weights read only at the touched ports**: `g a` at a program port of touch value `a`, `0`
elsewhere. -/
noncomputable def tcW (m₀ : Finset HPos × M)
    (g : Z → Matrix (Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞) :
    ∀ i : (recHwSpec X Z HPos M).Port,
      Matrix ((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (fun _ _ ↦ 0) fun c σ ↦ (tc c).elim 0 fun a ↦ g a σ)

/-- A local operation keeps the agreement (it acts beside the runtime register). -/
theorem agr_frame {A : QReg} (o : LocalSig.instruments.{0}.Op A)
    (b : LocalSig.instruments.{0}.Outcome o) {D : QReg} {P : D → Prop}
    {ρ ρ' : Matrix (A × D) (A × D) ℂ} (h : Agr (fun p ↦ P p.2) ρ ρ') :
    Agr (fun p : LocalSig.instruments.{0}.next o b × D ↦ P p.2)
      (((LocalSig.Interp.instruments o).frame D).branch b ρ)
      (((LocalSig.Interp.instruments o).frame D).branch b ρ') := by
  rw [DSubInstrument.branch_frame_apply]
  exact agr_amplify_left _ h

/-- **A call of a port destroying `Fr`** makes all its outputs agree on the block (with `0`). -/
theorem agr_queryStep_touch (m₀ : Finset HPos × M) (Fr : Hw X Z → Prop)
    (htc : ∀ c b, tc c = some b → ∀ W, ¬Fr (progUpdate c W))
    (c : HwProg X Z) (b : Z) (hb : tc c = some b) {A : QReg} (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z HPos M).In (.inl (.inr c)) × E) (r : c.Result)
    (τ : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D) (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ) :
    Agr (fun p ↦ Fr p.2.2.1) (((runtimeR m₀).queryStep (.inl (.inr c)) E ℓ).branch r τ) 0 := by
  have h := agr_queryStep_out (runtimeR m₀) (fun s ↦ Fr s.2.1) (.inl (.inr c)) E ℓ r
    (fun σ σ' ↦ agr_runtimeR_step_out m₀ Fr c (htc c b hb) r σ σ') τ 0
  rwa [map_zero] at h

variable {tc} (m₀ : Finset HPos × M) {Fr : Hw X Z → Prop}
  (hFr : ∀ c W, Fr (progUpdate c W) → Fr W)

include hFr in
/-- **A touched-port weight vanishes from a state without mass on the block**: no port moves
mass into the block, and `g` reads only the block's diagonal. -/
theorem totalWeight_tcW_eq_zero
    {g : Z → Matrix (Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞}
    (hg0 : ∀ b σ, (∀ s : (runtimeR (X := X) (Z := Z) m₀).D, Fr s.2.1 → σ ((), s) ((), s) = 0) →
      g b σ = 0)
    {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω A)
    (ρ : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D) (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hρ : Agr (fun p ↦ Fr p.2.2.1) ρ 0) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g) y ρ = 0 := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => exact totalWeight_pure _ _ _ _
  | primBind _ o k ih =>
    rw [totalWeight_primBind]
    refine ENNReal.tsum_eq_zero.2 fun b ↦ ih b _ ?_
    have h := agr_frame (P := fun s : (runtimeR (X := X) (Z := Z) m₀).D ↦ Fr s.2.1) o b hρ
    rwa [map_zero] at h
  | queryBind _ i E ℓ k ih =>
    rw [totalWeight_queryBind]
    have hr : ∀ r, Agr (fun p ↦ Fr p.2.2.1) (((runtimeR m₀).queryStep i E ℓ).branch r ρ) 0 :=
      fun r ↦ by
        have h := agr_queryStep (runtimeR m₀) (fun s ↦ Fr s.2.1) i E ℓ r
          (agr_runtimeR_step m₀ Fr hFr i r) hρ
        rwa [map_zero] at h
    rw [ENNReal.tsum_eq_zero.2 fun r ↦ ih r _ (hr r), add_zero]
    rcases i with ((i | c) | c) | T
    · rfl
    · rfl
    · show (tc c).elim 0 (fun a ↦ g a (callInput ℓ _ ρ)) = 0
      rcases tc c with _ | b
      · rfl
      · exact hg0 b _ fun s hs ↦ (callInput_unit_diag (runtimeR m₀) ℓ ρ s).trans
          (Finset.sum_eq_zero fun x _ ↦ hρ (x, s) (x, s) hs hs)
    · rfl

include hFr in
/-- **The touched-port weights of related programs agree.** Let `y` and `y'` agree until a
touched port (`KRel`), from states agreeing on the block of `Fr`, every touched port destroying
`Fr`. If `g a` and `g' a'` agree on operators with the same diagonal on the block, and vanish on
operators without diagonal there, the total weights agree. -/
theorem totalWeight_tcW_eq_of_krel
    (htc : ∀ c b, tc c = some b → ∀ W, ¬Fr (progUpdate c W)) {a a' : Z}
    {g g' : Z → Matrix (Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞}
    (hg0 : ∀ b σ, (∀ s : (runtimeR (X := X) (Z := Z) m₀).D, Fr s.2.1 → σ ((), s) ((), s) = 0) →
      g b σ = 0)
    (hg0' : ∀ b σ, (∀ s : (runtimeR (X := X) (Z := Z) m₀).D, Fr s.2.1 → σ ((), s) ((), s) = 0) →
      g' b σ = 0)
    (hgg : ∀ σ σ', (∀ s : (runtimeR (X := X) (Z := Z) m₀).D, Fr s.2.1 →
      σ ((), s) ((), s) = σ' ((), s) ((), s)) → g a σ = g' a' σ')
    {Ω : QReg → Type} {A : QReg}
    (y y' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) Ω A)
    (h : KRel tc a a' y y')
    (ρ ρ' : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D)
      (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hρ : Agr (fun p ↦ Fr p.2.2.1) ρ ρ') :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g) y ρ =
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g') y' ρ' := by
  induction y using QuantumComp.inductionOn with
  | pure _ x =>
    obtain rfl : y' = QuantumComp.pure x := h
    rw [totalWeight_pure, totalWeight_pure]
  | primBind _ o k ih =>
    obtain ⟨k', rfl, hk⟩ := krel_primBind_inv h
    rw [totalWeight_primBind, totalWeight_primBind]
    exact tsum_congr fun b ↦ ih b (k' b) (hk b) _ _
      (agr_frame (P := fun s : (runtimeR (X := X) (Z := Z) m₀).D ↦ Fr s.2.1) o b hρ)
  | queryBind _ i E ℓ k ih =>
    rcases krel_queryBind_inv h with ⟨hi, c', next', hc', rfl⟩ | ⟨hi, k', rfl, hk⟩
    · rcases i with ((i | c) | c) | T
      · simp [cmdTc] at hi
      · simp [cmdTc] at hi
      swap
      · simp [cmdTc] at hi
      have hi₀ : tc c = some a := hi
      rcases c' with o' | ⟨((i' | c₀) | c₀) | T', E', ℓ'⟩
      · simp [cmdTc] at hc'
      · simp [cmdTc] at hc'
      · simp [cmdTc] at hc'
      swap
      · simp [cmdTc] at hc'
      have hc₀ : tc c₀ = some a' := hc'
      refine (totalWeight_queryBind (runtimeR m₀) LocalSig.Interp.instruments _ _ _ _ _).trans
        (Eq.trans ?_ (totalWeight_queryBind (runtimeR m₀) LocalSig.Interp.instruments
          (w := tcW tc m₀ g') (.inl (.inr c₀)) E' ℓ' (fun r ↦ next' (ULift.up r)) ρ').symm)
      have h1 : ∑' r, (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g) (k r)
          (((runtimeR m₀).queryStep (.inl (.inr c)) E ℓ).branch r ρ) = 0 :=
        ENNReal.tsum_eq_zero.2 fun r ↦ totalWeight_tcW_eq_zero m₀ hFr hg0 (k r) _
          (agr_queryStep_touch tc m₀ Fr htc c a hi₀ E ℓ r ρ)
      have h2 : ∑' r, (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g')
          (next' (ULift.up r)) (((runtimeR m₀).queryStep (.inl (.inr c₀)) E' ℓ').branch r ρ') =
            0 :=
        ENNReal.tsum_eq_zero.2 fun r ↦ totalWeight_tcW_eq_zero m₀ hFr hg0' (next' (ULift.up r)) _
          (agr_queryStep_touch tc m₀ Fr htc c₀ a' hc₀ E' ℓ' r ρ')
      refine (congrArg (_ + ·) h1).trans (Eq.trans ?_ (congrArg (_ + ·) h2).symm)
      rw [add_zero, add_zero]
      show (tc c).elim 0 (fun b ↦ g b (callInput ℓ _ ρ)) =
        (tc c₀).elim 0 (fun b ↦ g' b (callInput ℓ' _ ρ'))
      rw [hi₀, hc₀]
      exact hgg _ _ fun s hs ↦ (callInput_unit_diag (runtimeR m₀) ℓ ρ s).trans
        ((Finset.sum_congr rfl fun x _ ↦ hρ (x, s) (x, s) hs hs).trans
          (callInput_unit_diag (runtimeR m₀) ℓ' ρ' s).symm)
    · rw [totalWeight_queryBind, totalWeight_queryBind]
      have hw : ∀ (gg : Z → Matrix (Unit × (runtimeR (X := X) (Z := Z) m₀).D)
          (Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞) (σ : Matrix
            ((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D)
            ((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ),
          tcW tc m₀ gg i σ = 0 := by
        intro gg σ
        rcases i with ((i | c) | c) | T
        · rfl
        · rfl
        · show (tc c).elim 0 (fun a ↦ gg a σ) = 0
          rw [show tc c = none from hi]
          rfl
        · rfl
      rw [hw, hw]
      exact congrArg (0 + ·) (tsum_congr fun r ↦ ih r (k' r) (hk r) _ _
        (agr_queryStep (runtimeR m₀) (fun s ↦ Fr s.2.1) i E ℓ r
          (agr_runtimeR_step m₀ Fr hFr i r) hρ))

end tcWeight

/-! ## The game at keys differing in one cell

The template game reads `pub.keys` only through the program ports of its slots (`slotPorts`), and
a slot's ports at public keys differing only at the `k` cell `x` (resp. the `k'` cell `x`) agree
until the slot's first `k` (resp. `k'`) port at `x`, which has the respective key values there
(`prel_slotPorts_k`, `prel_slotPorts_k'`): every round's cells are computed from the earlier
rounds' cells. So the realized games are related by `KRel` (`krel_gameT_k`, `krel_gameT_k'`). -/

section touch

variable {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]

/-- The touch value of a `k` port at `x`: its value. -/
def tcK (x : X₁) : HwProg X₁ Z₁ → Option Z₁
  | .programK y u => if y = x then some u else none
  | _ => none

/-- The touch value of a `k'` port at `x`: its value. -/
def tcK' (x : X₁) : HwProg X₁ Z₁ → Option Z₁
  | .programK' y u => if y = x then some u else none
  | _ => none

/-- No program port fills an empty `k` cell's emptiness backwards: an empty cell after a program
was empty before. -/
theorem progUpdate_k_none {c : HwProg X₁ Z₁} {W : Hw X₁ Z₁} {x : X₁}
    (h : (progUpdate c W).2.1 x = none) : W.2.1 x = none := by
  cases c with
  | programH z u => exact h
  | programK y u =>
    by_cases hy : x = y
    · subst hy
      simp [progUpdate] at h
    · simpa [progUpdate, Function.update_of_ne hy] using h
  | programK' y u => exact h

theorem progUpdate_k'_none {c : HwProg X₁ Z₁} {W : Hw X₁ Z₁} {x : X₁}
    (h : (progUpdate c W).2.2 x = none) : W.2.2 x = none := by
  cases c with
  | programH z u => exact h
  | programK y u => exact h
  | programK' y u =>
    by_cases hy : x = y
    · subst hy
      simp [progUpdate] at h
    · simpa [progUpdate, Function.update_of_ne hy] using h

/-- A touched `k` port fills its cell. -/
theorem tcK_some {x : X₁} {c : HwProg X₁ Z₁} {b : Z₁} (h : tcK x c = some b) (W : Hw X₁ Z₁) :
    ¬(progUpdate c W).2.1 x = none := by
  cases c with
  | programH z u => simp [tcK] at h
  | programK y u =>
    by_cases hy : y = x
    · subst hy
      simp [progUpdate]
    · simp [tcK, hy] at h
  | programK' y u => simp [tcK] at h

/-- A touched `k'` port fills its cell. -/
theorem tcK'_some {x : X₁} {c : HwProg X₁ Z₁} {b : Z₁} (h : tcK' x c = some b) (W : Hw X₁ Z₁) :
    ¬(progUpdate c W).2.2 x = none := by
  cases c with
  | programH z u => simp [tcK'] at h
  | programK y u => simp [tcK'] at h
  | programK' y u =>
    by_cases hy : y = x
    · subst hy
      simp [progUpdate]
    · simp [tcK', hy] at h

end touch

section prel

/-- **Lists of ports agreeing until a touched port.** -/
def PRel (tc : HwProg X Z → Option Z) (a a' : Z) : List (HwProg X Z) → List (HwProg X Z) → Prop
  | [], [] => True
  | p :: ps, p' :: ps' =>
      (tc p = some a ∧ tc p' = some a') ∨ (p = p' ∧ tc p = none ∧ PRel tc a a' ps ps')
  | _, _ => False

end prel

section rounds

/-- The `k` cell of round `j` of the absorption of `msg` under the public keys. -/
def kcell (pub : Pub) (msg : List X) (j : ℕ) : X :=
  (stateAt pub msg j).1 + msg.getD j 0

/-- The `k'` cell of round `j`. -/
def kcell' (pub : Pub) (msg : List X) (j : ℕ) : X :=
  (midAt pub (stateAt pub msg j) (msg.getD j 0)).1

/-- The program ports of round `j` of a slot's honest path. -/
def roundPorts (pub : Pub) (s : Slot) (f : ValPos → Digest) (j : ℕ) : List (HwProg X Z) :=
  [.programK (roundK pub s f j).1 (roundK pub s f j).2,
    .programK' (roundK' pub s f j).1 (roundK' pub s f j).2,
    .programH (roundH pub s f j).1 (roundH pub s f j).2]

/-- The realized ports of a slot: the ports of its rounds. -/
theorem map_realize_slotPorts_rounds (pub : Pub) (s : Slot) (v : HPos → Digest) :
    (slotPorts pub s).map (LazyProg.realize v) =
      (List.range' 0 (nBlocks pub s)).flatMap
        (roundPorts pub s (extendVals (restrictTo (inlSet (slotNeed s)) v))) := by
  rw [← List.range_eq_range']
  simp only [slotPorts, List.map_flatMap, List.map_cons, List.map_nil]
  rfl

theorem stateAt_succ_of_length_le (pub : Pub) (msg : List X) {j : ℕ} (hj : msg.length ≤ j) :
    stateAt pub msg (j + 1) = stateAt pub msg j := by
  unfold stateAt
  rw [List.take_of_length_le hj, List.take_of_length_le (by omega)]

theorem roundK_eq (pub : Pub) (s : Slot) (f : ValPos → Digest) (j : ℕ) :
    roundK pub s f j = (kcell pub (blocks (slotInput pub s f)) j,
      pub.keys.2.1 (kcell pub (blocks (slotInput pub s f)) j)) :=
  rfl

theorem roundK'_eq (pub : Pub) (s : Slot) (f : ValPos → Digest) (j : ℕ) :
    roundK' pub s f j = (kcell' pub (blocks (slotInput pub s f)) j,
      pub.keys.2.2 (kcell' pub (blocks (slotInput pub s f)) j)) :=
  rfl

variable {P : PublicParameter} {π : Equiv.Perm (X × Z)} {h : Z → X}

section keyK

variable {t t' k' : X → Z} {x : X} (ht : ∀ y, y ≠ x → t y = t' y)
include ht

/-- **The states agree up to the first round at the `k` cell `x`.** -/
theorem stateAt_keysK (msg : List X) : ∀ j, (∀ i < j, kcell ⟨P, π, (h, t, k')⟩ msg i ≠ x) →
    stateAt ⟨P, π, (h, t, k')⟩ msg j = stateAt ⟨P, π, (h, t', k')⟩ msg j
  | 0, _ => rfl
  | j + 1, hj => by
    have ih := stateAt_keysK msg j fun i hi ↦ hj i (by omega)
    by_cases hl : j < msg.length
    · have hne := hj j (by omega)
      unfold kcell at hne
      rw [stateAt_succ _ msg hl, stateAt_succ _ msg hl]
      simp only [midAt]
      rw [← ih, ← ht _ hne]
    · rw [stateAt_succ_of_length_le _ msg (by omega), stateAt_succ_of_length_le _ msg (by omega),
        ih]

/-- **A round off the `k` cell `x`** has the same ports at both keys. -/
theorem roundPorts_keysK (s : Slot) (f : ValPos → Digest) (j : ℕ)
    (hst : stateAt ⟨P, π, (h, t, k')⟩ (blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)) j =
      stateAt ⟨P, π, (h, t', k')⟩ (blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)) j)
    (hne : kcell ⟨P, π, (h, t, k')⟩ (blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)) j ≠ x) :
    roundPorts ⟨P, π, (h, t, k')⟩ s f j = roundPorts ⟨P, π, (h, t', k')⟩ s f j := by
  have hin : slotInput ⟨P, π, (h, t', k')⟩ s f = slotInput ⟨P, π, (h, t, k')⟩ s f := rfl
  have hnb : nBlocks ⟨P, π, (h, t', k')⟩ s = nBlocks ⟨P, π, (h, t, k')⟩ s := rfl
  unfold kcell at hne
  have hm : midAt ⟨P, π, (h, t, k')⟩
      (stateAt ⟨P, π, (h, t, k')⟩ (blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)) j)
      ((blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)).getD j 0) =
      midAt ⟨P, π, (h, t', k')⟩
        (stateAt ⟨P, π, (h, t', k')⟩ (blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)) j)
        ((blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)).getD j 0) := by
    rw [← hst]
    show π (_, _ + t _) = π (_, _ + t' _)
    rw [ht _ hne]
  unfold roundPorts roundK roundK' roundH
  dsimp only
  rw [hin, hnb, hm, ← hst, ht _ hne]

/-- **A slot's ports at keys differing at the `k` cell `x`** agree until its first `k` port at
`x`, which has the keys' values there. -/
theorem prel_rounds_k (s : Slot) (f : ValPos → Digest) : ∀ n j₀,
    (∀ i < j₀, kcell ⟨P, π, (h, t, k')⟩ (blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)) i ≠ x) →
    PRel (tcK x) (t x) (t' x) ((List.range' j₀ n).flatMap (roundPorts ⟨P, π, (h, t, k')⟩ s f))
      ((List.range' j₀ n).flatMap (roundPorts ⟨P, π, (h, t', k')⟩ s f))
  | 0, _, _ => trivial
  | n + 1, j₀, hj => by
    rw [List.range'_succ, List.flatMap_cons, List.flatMap_cons]
    have hst := stateAt_keysK ht (blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)) j₀ hj
    by_cases hc : kcell ⟨P, π, (h, t, k')⟩ (blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)) j₀ = x
    · have hc' : kcell ⟨P, π, (h, t', k')⟩ (blocks (slotInput ⟨P, π, (h, t', k')⟩ s f)) j₀ =
          x :=
        (congrArg (fun st : X × Z ↦ st.1 + (blocks (slotInput ⟨P, π, (h, t, k')⟩ s f)).getD j₀ 0)
          hst).symm.trans hc
      refine Or.inl ⟨?_, ?_⟩
      · show tcK x (.programK (roundK _ s f j₀).1 (roundK _ s f j₀).2) = _
        rw [roundK_eq, hc]
        exact ite_eq_left rfl
      · show tcK x (.programK (roundK _ s f j₀).1 (roundK _ s f j₀).2) = _
        rw [roundK_eq, hc']
        exact ite_eq_left rfl
    · rw [← roundPorts_keysK ht s f j₀ hst hc]
      refine Or.inr ⟨rfl, ?_, Or.inr ⟨rfl, rfl, Or.inr ⟨rfl, rfl,
        prel_rounds_k s f n (j₀ + 1) fun i hi ↦ ?_⟩⟩⟩
      · show tcK x (.programK (roundK _ s f j₀).1 (roundK _ s f j₀).2) = none
        rw [roundK_eq]
        exact ite_eq_right hc
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hj i hi
        · exact hc

/-- **The slot ports at keys differing at the `k` cell `x`.** -/
theorem prel_slotPorts_k (s : Slot) (v : HPos → Digest) :
    PRel (tcK x) (t x) (t' x) ((slotPorts ⟨P, π, (h, t, k')⟩ s).map (LazyProg.realize v))
      ((slotPorts ⟨P, π, (h, t', k')⟩ s).map (LazyProg.realize v)) := by
  rw [map_realize_slotPorts_rounds, map_realize_slotPorts_rounds]
  exact prel_rounds_k ht s _ _ 0 fun i hi ↦ absurd hi (Nat.not_lt_zero i)

end keyK

section keyK'

variable {k t t' : X → Z} {x : X} (ht : ∀ y, y ≠ x → t y = t' y)
include ht

/-- **The states agree up to the first round at the `k'` cell `x`.** -/
theorem stateAt_keysK' (msg : List X) : ∀ j, (∀ i < j, kcell' ⟨P, π, (h, k, t)⟩ msg i ≠ x) →
    stateAt ⟨P, π, (h, k, t)⟩ msg j = stateAt ⟨P, π, (h, k, t')⟩ msg j
  | 0, _ => rfl
  | j + 1, hj => by
    have ih := stateAt_keysK' msg j fun i hi ↦ hj i (by omega)
    by_cases hl : j < msg.length
    · have hne := hj j (by omega)
      unfold kcell' at hne
      rw [stateAt_succ _ msg hl, stateAt_succ _ msg hl, ← ih]
      have hm : midAt ⟨P, π, (h, k, t)⟩ (stateAt ⟨P, π, (h, k, t)⟩ msg j) (msg.getD j 0) =
          midAt ⟨P, π, (h, k, t')⟩ (stateAt ⟨P, π, (h, k, t)⟩ msg j) (msg.getD j 0) := rfl
      rw [← hm]
      show (_ + h (_ + t _), _ + t _) = (_ + h (_ + t' _), _ + t' _)
      rw [ht _ hne]
    · rw [stateAt_succ_of_length_le _ msg (by omega), stateAt_succ_of_length_le _ msg (by omega),
        ih]

/-- **A round off the `k'` cell `x`** has the same ports at both keys. -/
theorem roundPorts_keysK' (s : Slot) (f : ValPos → Digest) (j : ℕ)
    (hst : stateAt ⟨P, π, (h, k, t)⟩ (blocks (slotInput ⟨P, π, (h, k, t)⟩ s f)) j =
      stateAt ⟨P, π, (h, k, t')⟩ (blocks (slotInput ⟨P, π, (h, k, t)⟩ s f)) j)
    (hne : kcell' ⟨P, π, (h, k, t)⟩ (blocks (slotInput ⟨P, π, (h, k, t)⟩ s f)) j ≠ x) :
    roundPorts ⟨P, π, (h, k, t)⟩ s f j = roundPorts ⟨P, π, (h, k, t')⟩ s f j := by
  have hin : slotInput ⟨P, π, (h, k, t')⟩ s f = slotInput ⟨P, π, (h, k, t)⟩ s f := rfl
  have hnb : nBlocks ⟨P, π, (h, k, t')⟩ s = nBlocks ⟨P, π, (h, k, t)⟩ s := rfl
  unfold kcell' at hne
  unfold roundPorts roundK roundK' roundH
  dsimp only
  rw [hin, hnb, ← hst, ht _ hne]
  rfl

/-- **A slot's ports at keys differing at the `k'` cell `x`** agree until its first `k'` port at
`x`, which has the keys' values there. -/
theorem prel_rounds_k' (s : Slot) (f : ValPos → Digest) : ∀ n j₀,
    (∀ i < j₀, kcell' ⟨P, π, (h, k, t)⟩ (blocks (slotInput ⟨P, π, (h, k, t)⟩ s f)) i ≠ x) →
    PRel (tcK' x) (t x) (t' x) ((List.range' j₀ n).flatMap (roundPorts ⟨P, π, (h, k, t)⟩ s f))
      ((List.range' j₀ n).flatMap (roundPorts ⟨P, π, (h, k, t')⟩ s f))
  | 0, _, _ => trivial
  | n + 1, j₀, hj => by
    rw [List.range'_succ, List.flatMap_cons, List.flatMap_cons]
    have hst := stateAt_keysK' ht (blocks (slotInput ⟨P, π, (h, k, t)⟩ s f)) j₀ hj
    have hkc : kcell ⟨P, π, (h, k, t')⟩ (blocks (slotInput ⟨P, π, (h, k, t')⟩ s f)) j₀ =
        kcell ⟨P, π, (h, k, t)⟩ (blocks (slotInput ⟨P, π, (h, k, t)⟩ s f)) j₀ :=
      (congrArg (fun st : X × Z ↦ st.1 + (blocks (slotInput ⟨P, π, (h, k, t)⟩ s f)).getD j₀ 0)
        hst).symm
    have hk : roundK ⟨P, π, (h, k, t)⟩ s f j₀ = roundK ⟨P, π, (h, k, t')⟩ s f j₀ := by
      rw [roundK_eq, roundK_eq, hkc]
    have hk0 : tcK' x (.programK (roundK ⟨P, π, (h, k, t)⟩ s f j₀).1
        (roundK ⟨P, π, (h, k, t)⟩ s f j₀).2) = none := rfl
    by_cases hc : kcell' ⟨P, π, (h, k, t)⟩ (blocks (slotInput ⟨P, π, (h, k, t)⟩ s f)) j₀ = x
    · have hc' : kcell' ⟨P, π, (h, k, t')⟩ (blocks (slotInput ⟨P, π, (h, k, t')⟩ s f)) j₀ = x :=
        (congrArg (fun st : X × Z ↦ (midAt ⟨P, π, (h, k, t)⟩ st
          ((blocks (slotInput ⟨P, π, (h, k, t)⟩ s f)).getD j₀ 0)).1) hst).symm.trans hc
      refine Or.inr ⟨?_, hk0, Or.inl ⟨?_, ?_⟩⟩
      · show HwProg.programK _ _ = HwProg.programK _ _
        rw [hk]
      · show tcK' x (.programK' (roundK' _ s f j₀).1 (roundK' _ s f j₀).2) = _
        rw [roundK'_eq, hc]
        exact ite_eq_left rfl
      · show tcK' x (.programK' (roundK' _ s f j₀).1 (roundK' _ s f j₀).2) = _
        rw [roundK'_eq, hc']
        exact ite_eq_left rfl
    · rw [← roundPorts_keysK' ht s f j₀ hst hc]
      refine Or.inr ⟨rfl, hk0, Or.inr ⟨rfl, ?_, Or.inr ⟨rfl, rfl,
        prel_rounds_k' s f n (j₀ + 1) fun i hi ↦ ?_⟩⟩⟩
      · show tcK' x (.programK' (roundK' _ s f j₀).1 (roundK' _ s f j₀).2) = none
        rw [roundK'_eq]
        exact ite_eq_right hc
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hj i hi
        · exact hc

/-- **The slot ports at keys differing at the `k'` cell `x`.** -/
theorem prel_slotPorts_k' (s : Slot) (v : HPos → Digest) :
    PRel (tcK' x) (t x) (t' x) ((slotPorts ⟨P, π, (h, k, t)⟩ s).map (LazyProg.realize v))
      ((slotPorts ⟨P, π, (h, k, t')⟩ s).map (LazyProg.realize v)) := by
  rw [map_realize_slotPorts_rounds, map_realize_slotPorts_rounds]
  exact prel_rounds_k' ht s _ _ 0 fun i hi ↦ absurd hi (Nat.not_lt_zero i)

end keyK'

end rounds

/-! ## The realized games at keys differing in one cell -/

section gameRel

variable {M : Type} {tc : HwProg X Z → Option Z} {a a' : Z} (v : HPos → Digest)

/-- **A realized template without program ports has no touched port**: `ProgsIn` with the empty
table (no port programs a cell of it). -/
theorem noTc_realizeT {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (XSpec M) Ω A) :
    ProgsIn (hwEmpty X Z) v y → NoTc tc (realizeT v y) := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _; trivial
  | primBind _ o k ih => exact fun hy ↦ ⟨rfl, fun b ↦ ih b.down (hy.2 (ULift.up b.down))⟩
  | queryBind _ i E ℓ k ih =>
    intro hy
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact ⟨rfl, fun r ↦ ih r.down (hy.2 (ULift.up r.down))⟩
    · exact ⟨rfl, fun r ↦ ih r.down (hy.2 (ULift.up r.down))⟩
    · exfalso
      have h : ProgOf (hwEmpty X Z) (p.realize v) := hy.1
      cases hc : p.realize v with
      | programH z u => rw [hc] at h; cases h
      | programK y u => rw [hc] at h; cases h
      | programK' y u => rw [hc] at h; cases h
    · exact ⟨rfl, fun r ↦ ih (restrictTo T v, r.down) (hy.2 (ULift.up (restrictTo T v, r.down)))⟩

theorem krel_realizeT_bind₂ {A B C : QReg} {α β : Type} {x x' : QComp (XSpec M) A B α}
    {k k' : α → QComp (XSpec M) B C β} (hx : KRel tc a a' (realizeT v x) (realizeT v x'))
    (hk : ∀ b, KRel tc a a' (realizeT v (k b)) (realizeT v (k' b))) :
    KRel tc a a' (realizeT v (x.bind k)) (realizeT v (x'.bind k')) := by
  rw [realizeT_bind₂, realizeT_bind₂]
  exact krel_bind₂ hx hk

/-- A reveal, realized: the record port of `T`, continuing with the values of `v` on `T`. -/
theorem realizeT_revealThen_def {B C : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B C α) :
    realizeT v (revealThen goodAll T k) =
      QuantumComp.queryBind (L := LocalSig.instruments.{0}) (spec := recHwSpec X Z HPos M) (.inr T)
        B (Equiv.uniqueProd B Unit).symm fun r ↦
          QuantumComp.primBind (L := LocalSig.instruments.{0})
            ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦
              realizeT v (k (restrictTo T v, r)) :=
  rfl

/-- A program port, realized: the program port it realizes at `v`. -/
theorem realizeT_progThen_def {B C : QReg} {α : Type} (p : LazyProg X Z HPos XD)
    (k : QComp (XSpec M) B C α) :
    realizeT v (progThen p trivial k) =
      QuantumComp.queryBind (L := LocalSig.instruments.{0}) (spec := recHwSpec X Z HPos M)
        (Sum.inl (Sum.inr (p.realize v))) B (Equiv.uniqueProd B Unit).symm fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{0})
            ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦
              realizeT v k :=
  rfl

theorem krel_realizeT_revealThen {B C : QReg} {α : Type} (T : Finset HPos)
    {k k' : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B C α}
    (hk : ∀ r, KRel tc a a' (realizeT v (k r)) (realizeT v (k' r))) :
    KRel tc a a' (realizeT v (revealThen goodAll T k)) (realizeT v (revealThen goodAll T k')) := by
  rw [realizeT_revealThen_def, realizeT_revealThen_def]
  exact krel_queryBind_same _ B _ rfl fun r ↦ krel_primBind _ fun _ ↦ hk (restrictTo T v, r)

theorem krel_realizeT_bind {Ω Ω' : QReg → Type} {A : QReg}
    {x x' : QuantumComp LocalSig.instruments.{0} (XSpec M) Ω A}
    {g g' : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (XSpec M) Ω' u}
    (hx : KRel tc a a' (realizeT v x) (realizeT v x'))
    (hg : ∀ u y, KRel tc a a' (realizeT v (g u y)) (realizeT v (g' u y))) :
    KRel tc a a' (realizeT v (x.bind g)) (realizeT v (x'.bind g')) := by
  rw [realizeT_bind, realizeT_bind]
  exact krel_bind hx hg

theorem krel_realizeT_readLift {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A) :
    KRel tc a a' (realizeT v (readLift goodAll y)) (realizeT v (readLift goodAll y)) :=
  krel_refl (noTc_realizeT v _ (progsIn_readLift (hwEmpty X Z) v y))

theorem krel_realizeT_substitute {spec₀ : QuantumOracleSpec.{0, 0}}
    {σ σ' : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpec M))}
    (hσ : ∀ A c, KRel tc a a' (realizeT v (σ A c)) (realizeT v (σ' A c))) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Ω A) :
    KRel tc a a' (realizeT v (x.substitute σ)) (realizeT v (x.substitute σ')) := by
  rw [realizeT_substitute, realizeT_substitute]
  exact krel_substitute hσ x

/-- **Port lists agreeing until a touched port** realize related programs. -/
theorem krel_progPorts (B : QReg) : ∀ ps ps' : List (LazyProg X Z HPos XD),
    PRel tc a a' (ps.map (LazyProg.realize v)) (ps'.map (LazyProg.realize v)) →
      KRel tc a a' (realizeT v (progPorts M B ps)) (realizeT v (progPorts M B ps'))
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | p :: ps, p' :: ps', h => by
    rcases h with ⟨h1, h2⟩ | ⟨he, h1, h⟩
    · rw [progPorts, progPorts, realizeT_progThen_def, realizeT_progThen_def]
      exact krel_queryBind_touch (Sum.inl (Sum.inr (p.realize v))) B _
        (Sum.inl (Sum.inr (p'.realize v))) B _ h1 h2 _ _
    · rw [progPorts, progPorts, realizeT_progThen_def, realizeT_progThen_def, ← he]
      exact krel_queryBind_same (Sum.inl (Sum.inr (p.realize v))) B _ h1 fun _ ↦
        krel_primBind _ fun _ ↦
        krel_progPorts B ps ps' h

theorem krel_progSlots {pub pub' : Pub} (B : QReg)
    (hs : ∀ s, PRel tc a a' ((slotPorts pub s).map (LazyProg.realize v))
      ((slotPorts pub' s).map (LazyProg.realize v))) :
    ∀ ss : List Slot,
      KRel tc a a' (realizeT v (progSlots M pub B ss)) (realizeT v (progSlots M pub' B ss))
  | [] => rfl
  | s :: ss => krel_realizeT_bind₂ v (krel_progPorts v B _ _ (hs s)) fun _ ↦
      krel_progSlots B hs ss

variable [Fintype M] [DecidableEq M] (upd : TrialUpd M) {P : PublicParameter}
  {π : Equiv.Perm (X × Z)} {t t' : SpongeKeys X Z}
  (hs : ∀ s, PRel tc a a' ((slotPorts ⟨P, π, t⟩ s).map (LazyProg.realize v))
    ((slotPorts ⟨P, π, t'⟩ s).map (LazyProg.realize v)))
include hs

theorem krel_signLayerT (B : QReg) (lab : RLabel) :
    KRel tc a a' (realizeT v (signLayerT M upd ⟨P, π, t⟩ B lab))
      (realizeT v (signLayerT M upd ⟨P, π, t'⟩ B lab)) := by
  rw [signLayerT, signLayerT]
  refine krel_realizeT_revealThen v _ fun r₀ ↦ ?_
  rw [grindR_keys M upd P π t t']
  refine krel_realizeT_bind₂ v (krel_realizeT_readLift v _) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · rfl
  · exact krel_realizeT_revealThen v _ fun r ↦
      krel_realizeT_bind₂ v (krel_progSlots v B hs _) fun _ ↦ rfl

theorem krel_signT (B : QReg) (r : SigningRequest) :
    KRel tc a a' (realizeT v (signT M upd ⟨P, π, t⟩ B r))
      (realizeT v (signT M upd ⟨P, π, t'⟩ B r)) := by
  rw [signT, signT]
  refine krel_realizeT_bind₂ v (krel_signLayerT v upd hs B _) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · rfl
  · exact krel_realizeT_bind₂ v (krel_signLayerT v upd hs B _) fun b ↦ by
      rcases b with _ | ⟨top, _⟩ <;> rfl

theorem krel_challengeT (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))).A A) :
    KRel tc a a' (realizeT v (challengeT M upd ⟨P, π, t⟩ A c))
      (realizeT v (challengeT M upd ⟨P, π, t'⟩ A c)) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact krel_realizeT_readLift v _
  · exact krel_realizeT_readLift v _
  · refine krel_realizeT_bind v ?_ fun _ _ ↦ rfl
    rw [signAt, signAt]
    exact krel_realizeT_bind₂ v (krel_refl ⟨rfl, fun _ ↦ trivial⟩) fun _ ↦
      krel_signT v upd hs _ r

/-- **The realized games at keys related slot by slot are related.** -/
theorem krel_gameT (A : Adversary (X × Z)) :
    KRel tc a a' (realizeT v (gameT M upd ⟨P, π, t⟩ A))
      (realizeT v (gameT M upd ⟨P, π, t'⟩ A)) := by
  refine krel_realizeT_revealThen v _ fun r₀ ↦ ?_
  refine krel_realizeT_bind₂ v ?_ fun _ ↦
    krel_realizeT_bind₂ v (krel_realizeT_readLift v _) fun _ ↦ rfl
  exact krel_realizeT_substitute v (fun A c ↦ krel_challengeT v upd hs A c) _

end gameRel

/-! ## Averaging over one coordinate of a function -/

section avgCell

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

omit [Fintype α] [Fintype β] in
theorem update_funSplitAt_symm (y : α) (b a : β) (r : {j // j ≠ y} → β) :
    Function.update ((Equiv.funSplitAt y β).symm (b, r)) y a = (Equiv.funSplitAt y β).symm (a, r) := by
  funext j
  by_cases h : j = y
  · subst h
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

/-- **Summing over a function, one coordinate averaged out**: resampling the coordinate `y`
uniformly does not change the sum. -/
theorem sum_update_eq (F : (α → β) → ℝ≥0∞) (y : α) :
    ∑ k, ∑ a, F (Function.update k y a) = Fintype.card β * ∑ k, F k := by
  set e := Equiv.funSplitAt y β
  calc ∑ k, ∑ a, F (Function.update k y a)
      = ∑ p : β × ({j // j ≠ y} → β), ∑ a, F (Function.update (e.symm p) y a) :=
        (e.symm.sum_comp fun k ↦ ∑ a, F (Function.update k y a)).symm
    _ = ∑ p : β × ({j // j ≠ y} → β), ∑ a, F (e.symm (a, p.2)) :=
        Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun a _ ↦ by
          rw [update_funSplitAt_symm]
    _ = ∑ _b : β, ∑ r : {j // j ≠ y} → β, ∑ a, F (e.symm (a, r)) := Fintype.sum_prod_type _
    _ = Fintype.card β * ∑ r : {j // j ≠ y} → β, ∑ a, F (e.symm (a, r)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = Fintype.card β * ∑ k, F k := by
        rw [Finset.sum_comm, ← Fintype.sum_prod_type' (fun a r ↦ F (e.symm (a, r)))]
        exact congrArg (_ * ·) (e.symm.sum_comp F)

/-- **Per-cell resampling bounds.** Let a weight of functions `k` be bounded by per-cell weights
`W y k`; let the cell `y`'s weight at `k` with `y` resampled to `a` be `R y k a`, and let the
average over `a` be at most `c` times `T y k`. Then the sum over the functions of the weight is
at most `c` times the sum of the `T`. -/
theorem sum_le_of_cells [Nonempty β] (W : α → (α → β) → ℝ≥0∞) (R : α → (α → β) → β → ℝ≥0∞)
    (T : α → (α → β) → ℝ≥0∞) (c : ℝ≥0∞)
    (hW : ∀ y k a, W y (Function.update k y a) = R y k a)
    (hR : ∀ y k, (Fintype.card β : ℝ≥0∞)⁻¹ * ∑ a, R y k a ≤ c * T y k) :
    ∑ k, ∑ y, W y k ≤ c * ∑ k, ∑ y, T y k := by
  have h0 : (Fintype.card β : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have htop : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ∑ k, ∑ y, W y k = ∑ y, ∑ k, W y k := Finset.sum_comm
    _ = ∑ y, ∑ k, (Fintype.card β : ℝ≥0∞)⁻¹ * ∑ a, R y k a :=
        Finset.sum_congr rfl fun y _ ↦ by
          rw [← Finset.mul_sum]
          have hs : ∑ k, ∑ a, R y k a = ∑ k, ∑ a, W y (Function.update k y a) :=
            Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun a _ ↦ (hW y k a).symm
          rw [hs, sum_update_eq (W y) y, ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
    _ ≤ ∑ y, ∑ k, c * T y k := Finset.sum_le_sum fun y _ ↦ Finset.sum_le_sum fun k _ ↦ hR y k
    _ = c * ∑ k, ∑ y, T y k := by
        rw [Finset.mul_sum, Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ ↦ (Finset.mul_sum _ _ _).symm

end avgCell

/-! ## Two coordinates averaged out -/

section avgTwo

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β] [Fintype γ]

/-- **Resampling two function coordinates cell by cell** (`sum_le_of_cells` for `k` and `k'`). -/
theorem sum_two_cells (F : (α → β) → (α → β) → ℝ≥0∞)
    (Wk Wk' : α → (α → β) → (α → β) → ℝ≥0∞)
    (hF : ∀ k k', F k k' ≤ ∑ y, Wk y k k' + ∑ y, Wk' y k k')
    (Rk Rk' : α → (α → β) → (α → β) → β → ℝ≥0∞)
    (hWk : ∀ y k k' a, Wk y (Function.update k y a) k' = Rk y k k' a)
    (hWk' : ∀ y k k' a, Wk' y k (Function.update k' y a) = Rk' y k k' a)
    (Tk Tk' : α → (α → β) → (α → β) → ℝ≥0∞) (c N : ℝ≥0∞)
    (hRk : ∀ y k k', (Fintype.card β : ℝ≥0∞)⁻¹ * ∑ a, Rk y k k' a ≤ c * Tk y k k')
    (hRk' : ∀ y k k', (Fintype.card β : ℝ≥0∞)⁻¹ * ∑ a, Rk' y k k' a ≤ c * Tk' y k k')
    (hT : ∀ k k', ∑ y, Tk y k k' + ∑ y, Tk' y k k' ≤ N) :
    ∑ k, ∑ k', F k k' ≤ c * ∑ _k : α → β, ∑ _k' : α → β, N := by
  have h1 : ∑ k, ∑ k', ∑ y, Wk y k k' ≤ c * ∑ k, ∑ y, ∑ k', Tk y k k' := by
    calc ∑ k, ∑ k', ∑ y, Wk y k k' = ∑ k, ∑ y, ∑ k', Wk y k k' :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ ≤ c * ∑ k, ∑ y, ∑ k', Tk y k k' :=
          sum_le_of_cells (fun y k ↦ ∑ k', Wk y k k') (fun y k a ↦ ∑ k', Rk y k k' a)
            (fun y k ↦ ∑ k', Tk y k k') c
            (fun y k a ↦ Finset.sum_congr rfl fun k' _ ↦ hWk y k k' a) fun y k ↦ by
              rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_le_sum fun k' _ ↦ hRk y k k'
  have h2 : ∑ k, ∑ k', ∑ y, Wk' y k k' ≤ c * ∑ k', ∑ y, ∑ k, Tk' y k k' := by
    calc ∑ k, ∑ k', ∑ y, Wk' y k k' = ∑ k', ∑ y, ∑ k, Wk' y k k' := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ ≤ c * ∑ k', ∑ y, ∑ k, Tk' y k k' :=
          sum_le_of_cells (fun y k' ↦ ∑ k, Wk' y k k') (fun y k' a ↦ ∑ k, Rk' y k k' a)
            (fun y k' ↦ ∑ k, Tk' y k k') c
            (fun y k' a ↦ Finset.sum_congr rfl fun k _ ↦ hWk' y k k' a) fun y k' ↦ by
              rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_le_sum fun k _ ↦ hRk' y k k'
  have h3 : ∑ k, ∑ y, ∑ k', Tk y k k' + ∑ k', ∑ y, ∑ k, Tk' y k k' =
      ∑ k, ∑ k', (∑ y, Tk y k k' + ∑ y, Tk' y k k') := by
    simp only [Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    · exact (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm).trans Finset.sum_comm
  calc ∑ k, ∑ k', F k k' ≤ ∑ k, ∑ k', (∑ y, Wk y k k' + ∑ y, Wk' y k k') :=
        Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun k' _ ↦ hF k k'
    _ = ∑ k, ∑ k', ∑ y, Wk y k k' + ∑ k, ∑ k', ∑ y, Wk' y k k' := by
        simp only [Finset.sum_add_distrib]
    _ ≤ c * ∑ k, ∑ y, ∑ k', Tk y k k' + c * ∑ k', ∑ y, ∑ k, Tk' y k k' := add_le_add h1 h2
    _ = c * ∑ k, ∑ k', (∑ y, Tk y k k' + ∑ y, Tk' y k k') := by rw [← mul_add, h3]
    _ ≤ c * ∑ _k : α → β, ∑ _k' : α → β, N := by
        gcongr with k _ k' _
        exact hT k k'

omit [Nonempty β] in
/-- **The sum over the key pairs and further data**, from a bound for each datum. -/
theorem sum_pair_le (H : (α → β) → (α → β) → γ → ℝ≥0∞) (c N : ℝ≥0∞)
    (hH : ∀ v, ∑ k, ∑ k', H k k' v ≤ c * ∑ _k : α → β, ∑ _k' : α → β, N) :
    ∑ x : ((α → β) × (α → β)) × γ, H x.1.1 x.1.2 x.2 ≤
      c * N * Fintype.card (((α → β) × (α → β)) × γ) := by
  calc ∑ x : ((α → β) × (α → β)) × γ, H x.1.1 x.1.2 x.2
      = ∑ kk : (α → β) × (α → β), ∑ v, H kk.1 kk.2 v := Fintype.sum_prod_type _
    _ = ∑ v, ∑ kk : (α → β) × (α → β), H kk.1 kk.2 v := Finset.sum_comm
    _ = ∑ v, ∑ k, ∑ k', H k k' v :=
        Finset.sum_congr rfl fun v _ ↦ Fintype.sum_prod_type (fun kk : (α → β) × (α → β) ↦
          H kk.1 kk.2 v)
    _ ≤ ∑ _v : γ, c * ∑ _k : α → β, ∑ _k' : α → β, N := Finset.sum_le_sum fun v _ ↦ hH v
    _ = c * N * Fintype.card (((α → β) × (α → β)) × γ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
          Nat.cast_mul]
        ring

end avgTwo

/-! ## Flip sets free of the targets -/

section kfree

/-- **The target-free flip set of a `k` port at `y` with value `a`**: the facts `FlipK`, few
hardwired cells, low grade. It depends on the table only through `π`. -/
def kfSet (π : Equiv.Perm (X × Z)) (y : X) (a : Z) : Set (Unit × HwReg X Z Mem) :=
  {q | FlipK π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ progCap ∧ progCap + dbGrade q.2.1 ≤ 2 ^ 68}

/-- **The target-free flip set of a `k'` port at `y` with value `a`.** -/
def kfSet' (π : Equiv.Perm (X × Z)) (y : X) (a : Z) : Set (Unit × HwReg X Z Mem) :=
  {q | FlipK' π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ progCap ∧ progCap + dbGrade q.2.1 ≤ 2 ^ 68}

theorem mem_kfSet {π : Equiv.Perm (X × Z)} {y : X} {a : Z} {q : Unit × HwReg X Z Mem} :
    q ∈ kfSet π y a ↔ FlipK π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ progCap ∧
      progCap + dbGrade q.2.1 ≤ 2 ^ 68 :=
  Iff.rfl

theorem mem_kfSet' {π : Equiv.Perm (X × Z)} {y : X} {a : Z} {q : Unit × HwReg X Z Mem} :
    q ∈ kfSet' π y a ↔ FlipK' π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ progCap ∧
      progCap + dbGrade q.2.1 ≤ 2 ^ 68 :=
  Iff.rfl

/-- **The target-free flip weights of the program ports.** -/
noncomputable def kfW (π : Equiv.Perm (X × Z)) :
    HwProg X Z → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ → ℝ≥0∞
  | .programK y a, σ => diagMass (kfSet π y a) σ
  | .programK' y a, σ => diagMass (kfSet' π y a) σ
  | .programH _ _, _ => 0

/-- **The target-free `k` flips averaged over the value**: at most `2^-301` per unit of trace. -/
theorem uavg_kfSet_le {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, diagMass (kfSet π y a) σ ≤
      (2 ^ 301)⁻¹ * ENNReal.ofReal σ.trace.re := by
  have hs : ∑ a : Z, diagMass (kfSet π y a) σ ≤
      (((2 ^ 68 + 1) * ((2 ^ 68 + 1) * 2 ^ 68 + 2 * 2 ^ 68) * 18 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal σ.trace.re :=
    sum_diagMass_le_card (fun a ↦ kfSet π y a) _ hσ fun q _ t ht a₀ ha₀ ↦ by
      obtain ⟨-, hW, hT⟩ := mem_kfSet.mp (ht a₀ ha₀)
      exact card_flipK_le (W := q.2.2.1) (D := q.2.1) hπ (by omega) t
        (fun a ha ↦ (mem_kfSet.mp (ht a ha)).1) a₀ ha₀
  exact inv_card_Z_mul_le (by norm_num) hs

/-- **The target-free `k'` flips averaged over the value**: at most `2^-301` per unit of trace. -/
theorem uavg_kfSet'_le {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, diagMass (kfSet' π y a) σ ≤
      (2 ^ 301)⁻¹ * ENNReal.ofReal σ.trace.re := by
  have hs : ∑ a : Z, diagMass (kfSet' π y a) σ ≤
      (((2 ^ 68 + 1) + 2 ^ 68 * ((2 ^ 68 + 1) * 2 ^ 68 + 2 ^ 68 + 1) * 18 +
        2 ^ 68 * 2 ^ 68 * 18 + 2 ^ 68 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re :=
    sum_diagMass_le_card (fun a ↦ kfSet' π y a) _ hσ fun q _ t ht a₀ ha₀ ↦ by
      obtain ⟨-, hW, hT⟩ := mem_kfSet'.mp (ht a₀ ha₀)
      exact card_flipK'_le (W := q.2.2.1) (D := q.2.1) hπ (by omega) t
        (fun a ha ↦ (mem_kfSet'.mp (ht a ha)).1) a₀ ha₀
  exact inv_card_Z_mul_le (by norm_num) hs

/-- A diagonal mass grows with the set, on the support. -/
theorem diagMass_mono_supp {α : Type} [Fintype α] {S S' : Set α} {σ : Matrix α α ℂ}
    (h : ∀ a, σ a a ≠ 0 → a ∈ S → a ∈ S') : diagMass S σ ≤ diagMass S' σ := by
  unfold diagMass
  refine Finset.sum_le_sum fun a _ ↦ ?_
  by_cases hS : a ∈ S
  · by_cases ha : σ a a = 0
    · rw [Set.indicator_of_mem hS, ha, Complex.zero_re, ENNReal.ofReal_zero]
      exact zero_le
    · rw [Set.indicator_of_mem hS, Set.indicator_of_mem (h a ha hS)]
  · rw [Set.indicator_of_notMem hS]
    exact zero_le

/-- A diagonal mass is at most the trace. -/
theorem diagMass_le_trace {α : Type} [Fintype α] (S : Set α) {σ : Matrix α α ℂ}
    (hσ : σ.PosSemidef) : diagMass S σ ≤ ENNReal.ofReal σ.trace.re := by
  have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [diagMass, Matrix.trace, Complex.re_sum]
  simp only [Matrix.diag_apply]
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hre a]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  by_cases hS : a ∈ S
  · rw [Set.indicator_of_mem hS]
  · rw [Set.indicator_of_notMem hS]
    exact zero_le

/-- **A fresh `k`, `k'` flip at low grade is a target-free flip.** -/
theorem kFlip_le_kfW (L : HonestTable) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hg : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    kFlip L c σ ≤ kfW L.perm c σ := by
  cases c with
  | programH z u =>
    exact (diagMass_mono_supp (S' := ∅) fun q _ h ↦ absurd h (Set.notMem_empty q.2)).trans_eq
      (diagMass_empty σ)
  | programK y a =>
    refine diagMass_mono_supp fun q hq h ↦ ?_
    obtain ⟨hs, hx, hp⟩ : q.2 ∈ kFlipSet L (.programK y a) := h
    have hs' : (q.2.1, q.2.2.1, q.2.2.2.2) ∉ HwTargetBad L.perm trunc128 (xmssTgtHw L) progCap :=
      hs
    have hp' : ((q.2.1.1, Function.update q.2.1.2.1 y none, q.2.1.2.2), (q.2.2.1.1,
        Function.update q.2.2.1.2.1 y (some a), q.2.2.1.2.2), q.2.2.2.2) ∈
        HwTargetBad L.perm trunc128 (xmssTgtHw L) progCap := hp
    obtain ⟨hN, hF⟩ := flipK_facts (tgtAnti_xmssTgtHw L) hx hs' hp'
    exact mem_kfSet.mpr ⟨hF, hN, hg q hq⟩
  | programK' y a =>
    refine diagMass_mono_supp fun q hq h ↦ ?_
    obtain ⟨hs, hx, hp⟩ : q.2 ∈ kFlipSet L (.programK' y a) := h
    have hs' : (q.2.1, q.2.2.1, q.2.2.2.2) ∉ HwTargetBad L.perm trunc128 (xmssTgtHw L) progCap :=
      hs
    have hp' : ((q.2.1.1, q.2.1.2.1, Function.update q.2.1.2.2 y none), (q.2.2.1.1,
        q.2.2.1.2.1, Function.update q.2.2.1.2.2 y (some a)), q.2.2.2.2) ∈
        HwTargetBad L.perm trunc128 (xmssTgtHw L) progCap := hp
    obtain ⟨hN, hF⟩ := flipK'_facts (tgtAnti_xmssTgtHw L) hx hs' hp'
    exact mem_kfSet'.mpr ⟨hF, hN, hg q hq⟩

end kfree

/-! ## The fresh `k`, `k'` flips along the game, cell by cell -/

section cells

theorem tcK_programK_self (x : X) (a : Z) : tcK x (.programK x a) = some a := by
  simp [tcK]

theorem tcK_programK_ne {x y : X} (h : y ≠ x) (a : Z) : tcK x (.programK y a) = none := by
  simp [tcK, h]

theorem tcK'_programK'_self (x : X) (a : Z) : tcK' x (.programK' x a) = some a := by
  simp [tcK']

theorem tcK'_programK'_ne {x y : X} (h : y ≠ x) (a : Z) : tcK' x (.programK' y a) = none := by
  simp [tcK', h]

theorem kfW_programK (π : Equiv.Perm (X × Z)) (y : X) (a : Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    kfW π (.programK y a) σ = diagMass (kfSet π y a) σ :=
  rfl

theorem kfW_programK' (π : Equiv.Perm (X × Z)) (y : X) (a : Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    kfW π (.programK' y a) σ = diagMass (kfSet' π y a) σ :=
  rfl

/-- The target-free flip weight of a program port, cell by cell. -/
theorem kfW_split_prog (π : Equiv.Perm (X × Z)) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    kfW π c σ = ∑ y, (tcK y c).elim 0 (fun b ↦ diagMass (kfSet π y b) σ) +
      ∑ y, (tcK' y c).elim 0 (fun b ↦ diagMass (kfSet' π y b) σ) := by
  cases c with
  | programH z u =>
    show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp
  | programK y a =>
    have h2 : ∑ y', (tcK' y' (.programK y a)).elim 0 (fun b ↦ diagMass (kfSet' π y' b) σ) = 0 :=
      Finset.sum_eq_zero fun y' _ ↦ rfl
    rw [Finset.sum_eq_single y (fun y' _ hy' ↦ by rw [tcK_programK_ne (Ne.symm hy')]; rfl)
      (fun h ↦ absurd (Finset.mem_univ y) h), tcK_programK_self, h2, add_zero, Option.elim_some,
      kfW_programK]
  | programK' y a =>
    have h1 : ∑ y', (tcK y' (.programK' y a)).elim 0 (fun b ↦ diagMass (kfSet π y' b) σ) = 0 :=
      Finset.sum_eq_zero fun y' _ ↦ rfl
    rw [h1, zero_add,
      Finset.sum_eq_single y (fun y' _ hy' ↦ by rw [tcK'_programK'_ne (Ne.symm hy')]; rfl)
      (fun h ↦ absurd (Finset.mem_univ y) h), tcK'_programK'_self, Option.elim_some,
      kfW_programK']

/-- A weight read at the `k` and `k'` ports of a program port, cell by cell, is at most the
weight. -/
theorem kSplit_prog_le {α : Type*} (c : HwProg X Z) (f : α → ℝ≥0∞) (σ : α) :
    ∑ y, (tcK y c).elim 0 (fun _ ↦ f σ) + ∑ y, (tcK' y c).elim 0 (fun _ ↦ f σ) ≤ f σ := by
  cases c with
  | programH z u =>
    show ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞) ≤ _
    simp
  | programK y a =>
    have h2 : ∑ y', (tcK' y' (.programK y a)).elim 0 (fun _ ↦ f σ) = 0 :=
      Finset.sum_eq_zero fun y' _ ↦ rfl
    rw [Finset.sum_eq_single y (fun y' _ hy' ↦ by rw [tcK_programK_ne (Ne.symm hy')]; rfl)
      (fun h ↦ absurd (Finset.mem_univ y) h), tcK_programK_self, h2, add_zero, Option.elim_some]
  | programK' y a =>
    have h1 : ∑ y', (tcK y' (.programK' y a)).elim 0 (fun _ ↦ f σ) = 0 :=
      Finset.sum_eq_zero fun y' _ ↦ rfl
    rw [h1, zero_add,
      Finset.sum_eq_single y (fun y' _ hy' ↦ by rw [tcK'_programK'_ne (Ne.symm hy')]; rfl)
      (fun h ↦ absurd (Finset.mem_univ y) h), tcK'_programK'_self, Option.elim_some]

/-- A bound averaged over the values, read at a port of touch value `o`. -/
theorem elim_avg_le (o : Option Z) (g : Z → ℝ≥0∞) (t κ : ℝ≥0∞)
    (h : (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a, g a ≤ κ * t) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a, o.elim 0 (fun _ ↦ g a) ≤ κ * o.elim 0 (fun _ ↦ t) := by
  cases o with
  | none => simp only [Option.elim_none, Finset.sum_const_zero, mul_zero, le_refl]
  | some b =>
    simp only [Option.elim_some]
    exact h

/-- The averaged target-free `k` flips of a program port at the cell `y`. -/
theorem uavg_kfSet_prog_le {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (tcK y c).elim 0 (fun _ ↦ diagMass (kfSet π y a) σ) ≤
      (2 ^ 301)⁻¹ * (tcK y c).elim 0 (fun _ ↦ ENNReal.ofReal σ.trace.re) := by
  exact elim_avg_le (tcK y c) (fun a ↦ diagMass (kfSet π y a) σ) _ _ (uavg_kfSet_le hπ y hσ)

/-- The averaged target-free `k'` flips of a program port at the cell `y`. -/
theorem uavg_kfSet'_prog_le {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X)
    (c : HwProg X Z) {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (tcK' y c).elim 0 (fun _ ↦ diagMass (kfSet' π y a) σ) ≤
      (2 ^ 301)⁻¹ * (tcK' y c).elim 0 (fun _ ↦ ENNReal.ofReal σ.trace.re) := by
  exact elim_avg_le (tcK' y c) (fun a ↦ diagMass (kfSet' π y a) σ) _ _ (uavg_kfSet'_le hπ y hσ)

/-- **The target-free flip weight, cell by cell**: a `k` port at `y` is read by the `y` term of the
first sum, a `k'` port at `y` by the `y` term of the second. -/
theorem kfW_split (π : Equiv.Perm (X × Z)) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ) :
    extWeight (hwCost (fun _ _ ↦ 0) (kfW π)) i σ =
      ∑ y, tcW (tcK y) m0R (fun b ↦ diagMass (kfSet π y b)) i σ +
        ∑ y, tcW (tcK' y) m0R (fun b ↦ diagMass (kfSet' π y b)) i σ := by
  rcases i with ((p | c) | c) | T
  · show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp
  · show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp
  · exact kfW_split_prog π c σ
  · show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp

/-- **The traces at the `k` and `k'` ports, cell by cell**, are at most the traces at the program
ports. -/
theorem kTrace_split_le (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ) :
    ∑ y, tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re) i σ +
        ∑ y, tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re) i σ ≤
      extWeight (hwCost (fun _ _ ↦ 0) fun _ τ ↦ ENNReal.ofReal τ.trace.re) i σ := by
  rcases i with ((p | c) | c) | T
  · show ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞) ≤ 0
    simp
  · show ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞) ≤ 0
    simp
  · exact kSplit_prog_le c (fun τ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ ↦
      ENNReal.ofReal τ.trace.re) σ
  · show ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞) ≤ 0
    simp

variable {Ω : QReg → Type}
  (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))

/-- **The target-free flips along a run, cell by cell.** -/
theorem totalWeight_kfW_eq (π : Equiv.Perm (X × Z)) :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (kfW π))) x initR =
      ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK y) m0R (fun b ↦ diagMass (kfSet π y b))) x initR +
        ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK' y) m0R (fun b ↦ diagMass (kfSet' π y b))) x initR := by
  refine (congrArg (fun w ↦ (runtimeR m0R).totalWeight .instruments w x initR)
    (funext fun i ↦ funext fun σ ↦ kfW_split π i σ)).trans
    ((totalWeight_add_weight (runtimeR m0R) .instruments _ _ x initR).trans ?_)
  exact congrArg₂ (· + ·)
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK y) m0R (fun b ↦ diagMass (kfSet π y b))) x initR)
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK' y) m0R (fun b ↦ diagMass (kfSet' π y b))) x initR)

/-- **The traces at the `k`, `k'` ports along a run with at most `progCap` program calls.** -/
theorem totalWeight_kTrace_le (hK : IFreeM.IsChargeBound x (progChargeR HPos Selections) progCap) :
    ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR +
        ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR ≤ progCap := by
  refine (Eq.trans (congrArg₂ (· + ·)
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR).symm
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR).symm)
    (totalWeight_add_weight (runtimeR m0R) .instruments _ _ x initR).symm).trans_le ?_
  exact (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (fun i σ _ ↦ kTrace_split_le i σ) x initR_posSemidef).trans (totalWeight_progs_le x hK)

/-- **The resampled `k` flips of a cell along a run**: averaged over the value, at most `2^-301`
times the traces at the `k` ports of the cell. -/
theorem uavg_totalWeight_kfSet_le {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R (fun _ ↦ diagMass (kfSet π y a))) x initR ≤
      (2 ^ 301)⁻¹ * (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR := by
  refine ((congrArg ((Fintype.card Z : ℝ≥0∞)⁻¹ * ·) (totalWeight_fintype_sum (runtimeR m0R)
    .instruments (fun a ↦ tcW (tcK y) m0R (fun _ ↦ diagMass (kfSet π y a))) x initR).symm).trans
    (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ _ x initR).symm).trans_le
    ((totalWeight_le_totalWeight (runtimeR m0R) .instruments (fun i σ hσ ↦ ?_) x
      initR_posSemidef).trans_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments
        (2 ^ 301)⁻¹ (tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR))
  rcases i with ((p | c) | c) | T
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · exact uavg_kfSet_prog_le hπ y c hσ
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]

/-- **The resampled `k'` flips of a cell along a run.** -/
theorem uavg_totalWeight_kfSet'_le {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R (fun _ ↦ diagMass (kfSet' π y a))) x initR ≤
      (2 ^ 301)⁻¹ * (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR := by
  refine ((congrArg ((Fintype.card Z : ℝ≥0∞)⁻¹ * ·) (totalWeight_fintype_sum (runtimeR m0R)
    .instruments (fun a ↦ tcW (tcK' y) m0R (fun _ ↦ diagMass (kfSet' π y a))) x initR).symm).trans
    (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ _ x initR).symm).trans_le
    ((totalWeight_le_totalWeight (runtimeR m0R) .instruments (fun i σ hσ ↦ ?_) x
      initR_posSemidef).trans_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments
        (2 ^ 301)⁻¹ (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR))
  rcases i with ((p | c) | c) | T
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · exact uavg_kfSet'_prog_le hπ y c hσ
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]

end cells

/-! ## The fresh `k`, `k'` flips averaged over the keys -/

section keyAvg

theorem diagMass_kfSet_eq_zero (π : Equiv.Perm (X × Z)) (y : X) (b : Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    (h : ∀ s : HwReg X Z Mem, s.2.1.2.1 y = none → σ ((), s) ((), s) = 0) :
    diagMass (kfSet π y b) σ = 0 := by
  unfold diagMass
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  by_cases hq : q ∈ kfSet π y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, h s (mem_kfSet.mp hq).1.1, Complex.zero_re, ENNReal.ofReal_zero]
  · exact Set.indicator_of_notMem hq _

theorem diagMass_kfSet'_eq_zero (π : Equiv.Perm (X × Z)) (y : X) (b : Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    (h : ∀ s : HwReg X Z Mem, s.2.1.2.2 y = none → σ ((), s) ((), s) = 0) :
    diagMass (kfSet' π y b) σ = 0 := by
  unfold diagMass
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  by_cases hq : q ∈ kfSet' π y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, h s (mem_kfSet'.mp hq).1.1, Complex.zero_re, ENNReal.ofReal_zero]
  · exact Set.indicator_of_notMem hq _

theorem diagMass_kfSet_congr (π : Equiv.Perm (X × Z)) (y : X) (b : Z)
    {σ σ' : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (h : ∀ s : HwReg X Z Mem, s.2.1.2.1 y = none → σ ((), s) ((), s) = σ' ((), s) ((), s)) :
    diagMass (kfSet π y b) σ = diagMass (kfSet π y b) σ' := by
  unfold diagMass
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hq : q ∈ kfSet π y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, h s (mem_kfSet.mp hq).1.1]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

theorem diagMass_kfSet'_congr (π : Equiv.Perm (X × Z)) (y : X) (b : Z)
    {σ σ' : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (h : ∀ s : HwReg X Z Mem, s.2.1.2.2 y = none → σ ((), s) ((), s) = σ' ((), s) ((), s)) :
    diagMass (kfSet' π y b) σ = diagMass (kfSet' π y b) σ' := by
  unfold diagMass
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hq : q ∈ kfSet' π y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, h s (mem_kfSet'.mp hq).1.1]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

variable (A : Adversary (X × Z)) (P₀ : PublicParameter) (π₀ : Equiv.Perm (X × Z)) (h₀ : Z → X)
  (v : HPos → Digest)

/-- **The realized game at the keys `k`, `k'`**, the other public data and the hidden values
fixed. -/
noncomputable def gameKK (k k' : X → Z) :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit) Bool :=
  realizeT v (gameT Selections cwUpd ⟨P₀, π₀, (h₀, k, k')⟩ A)

/-- **Resampling the `k` key at one cell** (the lazy sampling of the key): the target-free flips at
the `k` ports of the cell `y`, in the game at `k` with `y` resampled to `a`, are the flips of value
`a` read at the `k` ports of `y` in the game at `k`. Before its first program of `y`, the game does
not read `k y`, and on the states with `y` free the presented operators agree. -/
theorem totalWeight_kfSet_update (y : X) (k k' : X → Z) (a : Z) :
    (runtimeR m0R).totalWeight .instruments (tcW (tcK y) m0R fun b ↦ diagMass (kfSet π₀ y b))
        (gameKK A P₀ π₀ h₀ v (Function.update k y a) k') initR =
      (runtimeR m0R).totalWeight .instruments (tcW (tcK y) m0R fun _ ↦ diagMass (kfSet π₀ y a))
        (gameKK A P₀ π₀ h₀ v k k') initR := by
  have ht : ∀ z, z ≠ y → Function.update k y a z = k z := fun z hz ↦ by
    rw [Function.update_apply, ite_eq_right hz]
  have hrel := krel_gameT (M := Selections) (tc := tcK y) (P := P₀) (π := π₀)
    (t := (h₀, Function.update k y a, k')) (t' := (h₀, k, k')) v cwUpd
    (fun s ↦ prel_slotPorts_k (x := y) ht s v) A
  rw [Function.update_self] at hrel
  exact totalWeight_tcW_eq_of_krel m0R (Fr := fun W ↦ W.2.1 y = none)
    (fun _ _ ↦ progUpdate_k_none) (fun _ _ hb W ↦ tcK_some hb W)
    (g := fun b ↦ diagMass (kfSet π₀ y b)) (g' := fun _ ↦ diagMass (kfSet π₀ y a))
    (fun b σ h ↦ diagMass_kfSet_eq_zero π₀ y b σ h)
    (fun _ σ h ↦ diagMass_kfSet_eq_zero π₀ y a σ h)
    (fun σ σ' h ↦ diagMass_kfSet_congr π₀ y a h)
    _ _ hrel initR initR fun _ _ _ _ ↦ rfl

/-- **Resampling the `k'` key at one cell.** -/
theorem totalWeight_kfSet'_update (y : X) (k k' : X → Z) (a : Z) :
    (runtimeR m0R).totalWeight .instruments (tcW (tcK' y) m0R fun b ↦ diagMass (kfSet' π₀ y b))
        (gameKK A P₀ π₀ h₀ v k (Function.update k' y a)) initR =
      (runtimeR m0R).totalWeight .instruments (tcW (tcK' y) m0R fun _ ↦ diagMass (kfSet' π₀ y a))
        (gameKK A P₀ π₀ h₀ v k k') initR := by
  have ht : ∀ z, z ≠ y → Function.update k' y a z = k' z := fun z hz ↦ by
    rw [Function.update_apply, ite_eq_right hz]
  have hrel := krel_gameT (M := Selections) (tc := tcK' y) (P := P₀) (π := π₀)
    (t := (h₀, k, Function.update k' y a)) (t' := (h₀, k, k')) v cwUpd
    (fun s ↦ prel_slotPorts_k' (x := y) ht s v) A
  rw [Function.update_self] at hrel
  exact totalWeight_tcW_eq_of_krel m0R (Fr := fun W ↦ W.2.2 y = none)
    (fun _ _ ↦ progUpdate_k'_none) (fun _ _ hb W ↦ tcK'_some hb W)
    (g := fun b ↦ diagMass (kfSet' π₀ y b)) (g' := fun _ ↦ diagMass (kfSet' π₀ y a))
    (fun b σ h ↦ diagMass_kfSet'_eq_zero π₀ y b σ h)
    (fun _ σ h ↦ diagMass_kfSet'_eq_zero π₀ y a σ h)
    (fun σ σ' h ↦ diagMass_kfSet'_congr π₀ y a h)
    _ _ hrel initR initR fun _ _ _ _ ↦ rfl

/-- **The target-free flips summed over the keys `k`, `k'`**: at most `2^-301` times `progCap` per
key pair, for `PermGood π 18`. -/
theorem sum_kfTot_le {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (hπ₀ : PermGood π₀ 18) :
    ∑ k, ∑ k', (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW π₀))) (gameKK A P₀ π₀ h₀ v k k') initR ≤
      (2 ^ 301)⁻¹ * ∑ _k : X → Z, ∑ _k' : X → Z, (progCap : ℝ≥0∞) :=
  sum_two_cells
    (fun k k' ↦ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW π₀))) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun b ↦ diagMass (kfSet π₀ y b)) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun b ↦ diagMass (kfSet' π₀ y b)) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun _ _ ↦ (totalWeight_kfW_eq _ π₀).le)
    (fun y k k' a ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun _ ↦ diagMass (kfSet π₀ y a)) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun y k k' a ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun _ ↦ diagMass (kfSet' π₀ y a)) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun y k k' a ↦ totalWeight_kfSet_update A P₀ π₀ h₀ v y k k' a)
    (fun y k k' a ↦ totalWeight_kfSet'_update A P₀ π₀ h₀ v y k k' a)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun _ τ ↦ ENNReal.ofReal τ.trace.re) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun _ τ ↦ ENNReal.ofReal τ.trace.re) (gameKK A P₀ π₀ h₀ v k k') initR)
    (2 ^ 301)⁻¹ progCap
    (fun y _ _ ↦ uavg_totalWeight_kfSet_le _ hπ₀ y)
    (fun y _ _ ↦ uavg_totalWeight_kfSet'_le _ hπ₀ y)
    (fun _ _ ↦ totalWeight_kTrace_le _ (hN_prog cwUpd A hperm hsign _ v))

/-- **The fresh `k`, `k'` flips along the game are target-free flips**: along the run every call
has low grade (at most `6q` sponge and `clsCap` classical calls, `q ≤ 2^64`). -/
theorem kTot_le_kfTot {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (hq : q ≤ 2 ^ 64) (L : HonestTable) :
    kTot A L ≤ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW L.perm))) (gameR A L) initR := by
  set κ : (recHwSpec X Z HPos Selections).Port → ℕ := fun i ↦
    (if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls X Z Mem (recSpec HPos Selections) i = true <;> simp [h]
  have hx : IFreeM.IsChargeBound (gameR A L) (portCharge κ) (6 * q + clsCap) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      ((advCalls_gameR hperm hsign L).add (clsCalls_gameR hperm hsign L))
  have hfq := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1) κ (fun _ ↦ 0)
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_step m0R i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments (gameR A L) hx
    (isChargeBound_portCharge_zero _) querySupportedOn_initR
  have hT := progCap_add_le hq
  unfold kTot costTot
  refine totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun _ τ ↦ ∀ a, τ a a ≠ 0 → dbGrade a.2.1 ≤ 6 * q + clsCap)
    (fun i E σ hP a ha ↦ ?_) (fun i τ _ hok ↦ ?_) (gameR A L) initR_posSemidef hfq
  · obtain ⟨e, he⟩ : ∃ e, σ (a, e) (a, e) ≠ 0 := by
      by_contra h
      exact ha (traceRight_diag_eq_zero fun e ↦ not_not.1 fun he ↦ h ⟨e, he⟩)
    have h := (hP.2 (a, e) (a, e) he).1
    rw [Set.mem_Iic, Nat.zero_add] at h
    exact h
  · rcases i with ((p | c) | c) | T
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl
    · dsimp only [extWeight, sumWeight, hwCost]
      exact kFlip_le_kfW L c fun a ha ↦ by
        have := hok a ha
        omega
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl

/-- The fresh `k`, `k'` flips along the game are at most its program calls. -/
theorem kTot_le_progCap {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (L : HonestTable) : kTot A L ≤ progCap := by
  unfold kTot costTot
  refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := extWeight (hwCost (fun _ _ ↦ 0) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
    (fun i σ hσ ↦ ?_) (gameR A L) initR_posSemidef).trans
    (totalWeight_progs_le (gameR A L) (progCalls_gameR hperm hsign L))
  rcases i with ((p | c) | c) | T
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl
  · dsimp only [extWeight, sumWeight, hwCost]
    exact diagMass_le_trace _ hσ
  · show (0 : ℝ≥0∞) ≤ 0
    exact le_rfl

/-- **ProgView's `hk`: the fresh `k`, `k'` flips averaged over the tables.** The table, padded by
`E`, is mapped by `e` to public data `Q`, the keys `(k, k')` and hidden data `V`, injectively on a
good set `G`, with `|Q| |(X → Z)²| |V| ≤ |table| |E|`. On `G` the game at the table is the
template game at the public datum `⟨par, perm, (hk, k, k')⟩` realized at `val` (`hgame`), with the
table's `π`. Then the averaged fresh flips on the `PermGood` tables are at most `progCap · 2^-301`
plus `progCap` times the bad fraction: averaging the keys at each programmed cell (the game does not
read the key of a cell before its first program there, `totalWeight_kfSet_update`) leaves the
capacity-scale count of `badAttachK`, `badCompleteOutK'` per unit of program-call weight. -/
theorem uavg_kTot_le {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (hq : q ≤ 2 ^ 64) {E Q V : Type} [Fintype E] [Nonempty E] [Fintype Q] [Fintype V]
    (e : HonestTable × E → Q × (((X → Z) × (X → Z)) × V)) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card Q * Fintype.card (((X → Z) × (X → Z)) × V) ≤
      Fintype.card (HonestTable × E))
    (par : Q → PublicParameter) (perm : Q → Equiv.Perm (X × Z)) (hk : Q → Z → X)
    (val : V → HPos → Digest)
    (hgame : ∀ t, G t → gameR A t.1 = gameKK A (par (e t).1) (perm (e t).1) (hk (e t).1)
      (val (e t).2.2) (e t).2.1.1 (e t).2.1.2)
    (hπ : ∀ t, G t → perm (e t).1 = t.1.perm) :
    uavg (fun L ↦ if PermGood L.perm 18 then kTot A L else 0) ≤
      (2 ^ 301)⁻¹ * progCap + progCap * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬G t).card) := by
  refine uavg_le_of_injOn e G hinj hcard _
    (fun p x ↦ if PermGood (perm p) 18 then (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW (perm p))))
        (gameKK A (par p) (perm p) (hk p) (val x.2) x.1.1 x.1.2) initR else 0)
    (fun t ht ↦ ?_) progCap (fun t _ ↦ ?_) ((2 ^ 301)⁻¹ * progCap) (fun p ↦ ?_)
  · by_cases hL : PermGood t.1.perm 18
    · have hp : PermGood (perm (e t).1) 18 := (hπ t ht).symm ▸ hL
      rw [ite_eq_left hL, ite_eq_left hp]
      refine (kTot_le_kfTot hperm hsign hq t.1).trans_eq ?_
      rw [hgame t ht, hπ t ht]
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hL : PermGood t.1.perm 18
    · rw [ite_eq_left hL]
      exact kTot_le_progCap hperm hsign t.1
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hp : PermGood (perm p) 18
    · refine (Finset.sum_congr rfl fun x _ ↦ ite_eq_left hp).trans_le ?_
      exact sum_pair_le (fun k k' w ↦ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW (perm p))))
          (gameKK A (par p) (perm p) (hk p) (val w) k k') initR) _ _
        fun w ↦ sum_kfTot_le A (par p) (perm p) (hk p) (val w) hperm hsign hp
    · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right hp]
      exact zero_le

/-- **ProgView's `hk` in its shape**: the flips on the tables with `PermGood π 18` and a further
condition `Gd` are at most those on the `PermGood` tables. -/
theorem uavg_kTot_le_of_gd (A : Adversary (X × Z)) (Gd : HonestTable → Prop) [DecidablePred Gd] :
    uavg (fun L ↦ if PermGood L.perm 18 ∧ Gd L then kTot A L else 0) ≤
      uavg (fun L ↦ if PermGood L.perm 18 then kTot A L else 0) :=
  uavg_mono fun L ↦ by
    by_cases h : PermGood L.perm 18 ∧ Gd L
    · rw [ite_eq_left h, ite_eq_left h.1]
    · rw [ite_eq_right h]
      exact zero_le

end keyAvg

end Quantum.Xmss.Assembly

end
