module

public import Quantum.Xmss.Assembly.GameT

@[expose] public section

/-!
# Dropping the record ports of the canonical game

The canonical runtime-2 game `realizeT v (gameT M upd pub A)` (Template) runs over `recHwSpec`:
memory `Finset ValPos × M`, record ports, and trial reads that update the inner memory with `upd`.
Its program `gameD Unit pub v A` over `hwSpec` with memory `Unit` (GameT) drops the record calls
and keeps the memory on every read.

* `dropRec_gameT`: `DropRec ValPos (realizeT v (gameT M upd pub A)) (gameD Unit pub v A)`, by the
  structure of the two programs (`ReadsRel` for the read programs: one read at a time,
  `readsRel_readH_bind`, then the sponge rounds, the trials, the randomizer search and the
  verification's reads).
* `evalDistMap_runtime1R_eq`: for `DropRec S x y`, runtime 1 with record ports from any memory
  `m₀` running `x` has the law of runtime 1 with the memory `Unit` running `y`. The simulation
  (`dropRec_intertwines`, for every input) is through `memFgt`, the partial trace over the memory
  (Kraus operators `memDrop p`): the sponge and program ports do not read the memory
  (`memDrop_mul_spongeU`, `memDrop_mul_hwProgKraus`); a read with result `(o, p)` and update `u`
  acts beside the memory `p` it read and moves it to `u p o`, so summed over `p` it is the read
  keeping the memory `Unit` (`sum_memFgt_comp_conj`); records, summed over the memory before them,
  are forgotten (`sum_memFgt_recC`).
-/

open Matrix
open scoped Kronecker

universe w

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

/-! ## One read at a time -/

section reads

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {S : Type}
  {D : S → Type} {good : LazyProg X Z S D → Prop} {M : Type}

/-- **A read with any update against a read keeping the memory `Unit`**, each followed by
continuations that agree on the read value. -/
theorem readsRel_readH_bind (v : (s : S) → D s) {B C : QReg} {β : Type} (z : Z)
    (u : M → Option X → M) (u' : Unit → Option X → Unit)
    {k : Option X × M → QComp (hwReadSpec X Z M) B C β}
    {k' : Option X × Unit → QComp (hwReadSpec X Z Unit) B C β}
    (h : ∀ o p, ReadsRel good v (k (o, p)) (k' (o, ()))) :
    ReadsRel good v ((readCall (.readH z u) B).bind k) ((readCall (.readH z u') B).bind k') := by
  obtain rfl : u' = keepMem := funext fun _ ↦ funext fun _ ↦ rfl
  exact DropRec.readH z (fun m o ↦ (m.1, u m.2 o)) B (Equiv.uniqueProd B Unit).symm
    (k := fun r ↦ realizeT v (readLiftQ good
      ((QComp.act (spec := hwReadSpec X Z M) (A := QReg.of (QReg.of Unit × B)) (B := B)
        (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦ k (r.1, r.2.2))))
    (k' := fun r ↦ liftReadC
      ((QComp.act (spec := hwReadSpec X Z Unit) (A := QReg.of (QReg.of Unit × B)) (B := B)
        (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦ k' r))
    fun o p ↦ readsRel_act_bind v _ fun _ ↦ h o p.2

theorem readsRel_readK_bind (v : (s : S) → D s) {B C : QReg} {β : Type} (x : X)
    (u : M → Option Z → M) (u' : Unit → Option Z → Unit)
    {k : Option Z × M → QComp (hwReadSpec X Z M) B C β}
    {k' : Option Z × Unit → QComp (hwReadSpec X Z Unit) B C β}
    (h : ∀ o p, ReadsRel good v (k (o, p)) (k' (o, ()))) :
    ReadsRel good v ((readCall (.readK x u) B).bind k) ((readCall (.readK x u') B).bind k') := by
  obtain rfl : u' = keepMem := funext fun _ ↦ funext fun _ ↦ rfl
  exact DropRec.readK x (fun m o ↦ (m.1, u m.2 o)) B (Equiv.uniqueProd B Unit).symm
    (k := fun r ↦ realizeT v (readLiftQ good
      ((QComp.act (spec := hwReadSpec X Z M) (A := QReg.of (QReg.of Unit × B)) (B := B)
        (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦ k (r.1, r.2.2))))
    (k' := fun r ↦ liftReadC
      ((QComp.act (spec := hwReadSpec X Z Unit) (A := QReg.of (QReg.of Unit × B)) (B := B)
        (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦ k' r))
    fun o p ↦ readsRel_act_bind v _ fun _ ↦ h o p.2

theorem readsRel_readK'_bind (v : (s : S) → D s) {B C : QReg} {β : Type} (x : X)
    (u : M → Option Z → M) (u' : Unit → Option Z → Unit)
    {k : Option Z × M → QComp (hwReadSpec X Z M) B C β}
    {k' : Option Z × Unit → QComp (hwReadSpec X Z Unit) B C β}
    (h : ∀ o p, ReadsRel good v (k (o, p)) (k' (o, ()))) :
    ReadsRel good v ((readCall (.readK' x u) B).bind k) ((readCall (.readK' x u') B).bind k') := by
  obtain rfl : u' = keepMem := funext fun _ ↦ funext fun _ ↦ rfl
  exact DropRec.readK' x (fun m o ↦ (m.1, u m.2 o)) B (Equiv.uniqueProd B Unit).symm
    (k := fun r ↦ realizeT v (readLiftQ good
      ((QComp.act (spec := hwReadSpec X Z M) (A := QReg.of (QReg.of Unit × B)) (B := B)
        (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦ k (r.1, r.2.2))))
    (k' := fun r ↦ liftReadC
      ((QComp.act (spec := hwReadSpec X Z Unit) (A := QReg.of (QReg.of Unit × B)) (B := B)
        (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦ k' r))
    fun o p ↦ readsRel_act_bind v _ fun _ ↦ h o p.2

variable (good) in
/-- Stateful read programs at memories `M` and `Unit` that read alike from every log. -/
def ReadsRelS (v : (s : S) → D s) {B : QReg} {α : Type}
    (x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α)
    (y : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z Unit) B B) α) : Prop :=
  ∀ s, ReadsRel good v (x.run s) (y.run s)

variable {v : (s : S) → D s} {B : QReg}

theorem readsRelS_pure {α : Type} (a : α) :
    ReadsRelS good v
      (pure a : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α) (pure a) :=
  fun s ↦ readsRel_pure v (a, s)

theorem ReadsRelS.bind {α β : Type}
    {x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α}
    {y : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z Unit) B B) α}
    {f : α → StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) β}
    {g : α → StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z Unit) B B) β}
    (hx : ReadsRelS good v x y) (hf : ∀ a, ReadsRelS good v (f a) (g a)) :
    ReadsRelS good v (x >>= f) (y >>= g) := fun s ↦ by
  rw [StateT.run_bind, StateT.run_bind]
  exact (hx s).bind fun p ↦ hf p.1 p.2

theorem ReadsRelS.map {α β : Type}
    {x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α}
    {y : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z Unit) B B) α}
    (hx : ReadsRelS good v x y) (f : α → β) : ReadsRelS good v (f <$> x) (f <$> y) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact hx.bind fun a ↦ readsRelS_pure (f a)

variable [AddCommGroup X] [AddCommGroup Z]

omit [AddCommGroup X] in
theorem readsRelS_rdK (x : X) :
    ReadsRelS good v (rdK (M := M) B x) (rdK (M := Unit) B x) := fun s ↦
  readsRel_readK_bind (M := M)
    (k := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [.k x (r.1.getD 0)]))
    (k' := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [.k x (r.1.getD 0)])) v x keepMem keepMem
    fun _ _ ↦ readsRel_pure v _

omit [AddCommGroup X] in
theorem readsRelS_rdK' (x : X) :
    ReadsRelS good v (rdK' (M := M) B x) (rdK' (M := Unit) B x) := fun s ↦
  readsRel_readK'_bind (M := M)
    (k := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [.k' x (r.1.getD 0)]))
    (k' := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [.k' x (r.1.getD 0)])) v x keepMem keepMem
    fun _ _ ↦ readsRel_pure v _

omit [AddCommGroup Z] in
theorem readsRelS_rdH (z : Z) :
    ReadsRelS good v (rdH (M := M) B z) (rdH (M := Unit) B z) := fun s ↦
  readsRel_readH_bind (M := M)
    (k := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [.h z (r.1.getD 0)]))
    (k' := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [.h z (r.1.getD 0)])) v z keepMem keepMem
    fun _ _ ↦ readsRel_pure v _

variable (π : Equiv.Perm (X × Z))

theorem readsRelS_rdRound (s : X × Z) (b : X) :
    ReadsRelS good v (rdRound M π B s b) (rdRound Unit π B s b) := by
  unfold rdRound
  exact (readsRelS_rdK _).bind fun _ ↦ (readsRelS_rdK' _).bind fun _ ↦ (readsRelS_rdH _).bind
    fun _ ↦ readsRelS_pure _

theorem readsRelS_foldlM (msg : List X) (s : X × Z) :
    ReadsRelS good v (msg.foldlM (rdRound M π B) s) (msg.foldlM (rdRound Unit π B) s) := by
  induction msg generalizing s with
  | nil => exact readsRelS_pure s
  | cons b msg ih =>
    rw [List.foldlM_cons, List.foldlM_cons]
    exact (readsRelS_rdRound π s b).bind ih

end reads

/-! ## The read programs of leanXMSS -/

section xreads

variable {S : Type} {D : S → Type} {good : LazyProg X Z S D → Prop} {M : Type}
  {v : (s : S) → D s} {B : QReg} (π : Equiv.Perm (X × Z))

theorem readsRelS_rdHU (z : Z) (u : M → Option X → M) (u' : Unit → Option X → Unit) :
    ReadsRelS good v (rdHU M B z u) (rdHU Unit B z u') := fun s ↦
  readsRel_readH_bind (k := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [.h z (r.1.getD 0)]))
    (k' := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [.h z (r.1.getD 0)])) v z u u'
    fun _ _ ↦ readsRel_pure v _

theorem readsRelS_rdRoundU (u : X → X → M → Option X → M)
    (u' : X → X → Unit → Option X → Unit) (s : X × Z) (b : X) :
    ReadsRelS good v (rdRoundU M u π B s b) (rdRoundU Unit u' π B s b) := by
  unfold rdRoundU
  exact (readsRelS_rdK _).bind fun _ ↦ (readsRelS_rdK' _).bind fun _ ↦
    (readsRelS_rdHU _ _ _).bind fun _ ↦ readsRelS_pure _

theorem readsRelS_foldlM_rdRoundU (u : X → X → M → Option X → M)
    (u' : X → X → Unit → Option X → Unit) (msg : List X) (s : X × Z) :
    ReadsRelS good v (msg.foldlM (rdRoundU M u π B) s) (msg.foldlM (rdRoundU Unit u' π B) s) := by
  induction msg generalizing s with
  | nil => exact readsRelS_pure s
  | cons b msg ih =>
    rw [List.foldlM_cons, List.foldlM_cons]
    exact (readsRelS_rdRoundU π u u' s b).bind ih

theorem readsRel_hashTrial (u : X → X → M → Option X → M)
    (u' : X → X → Unit → Option X → Unit) (input : HashInput) :
    ReadsRel good v (hashTrial M u π B input) (hashTrial Unit u' π B input) :=
  ((((readsRelS_foldlM_rdRoundU π u u' (blocks input) (0, 0)).map fun s ↦ s.1).map out256)
    []).map Prod.fst

theorem readsRelS_readsImpl (input : HashInput) :
    ReadsRelS good v (readsImpl M π B input) (readsImpl Unit π B input) :=
  ((readsRelS_foldlM π (blocks input) (0, 0)).map fun s ↦ s.1).map out256

theorem readsRelS_simulateQ {α : Type} (x : OracleComp LeanXmss.HashSpec α) :
    ReadsRelS good v (simulateQ (readsImpl M π B) x) (simulateQ (readsImpl Unit π B) x) := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    rw [simulateQ_pure, simulateQ_pure]
    exact readsRelS_pure a
  | query_bind input k ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query]
    exact (readsRelS_readsImpl π input).bind ih

/-- **The read program of a hash computation at memories `M` and `Unit`.** -/
theorem readsRel_readsProgram {α : Type} (x : OracleComp LeanXmss.HashSpec α) :
    ReadsRel good v (readsProgram M π B x) (readsProgram Unit π B x) :=
  readsRelS_simulateQ π x []

end xreads

/-! ## The realized game drops to `gameD` -/

section game

variable {M : Type} (upd : TrialUpd M) (v : ValPos → Digest)

/-- **The randomizer search at memories `M` and `Unit`.** -/
theorem readsRel_grindR (pub : Pub) (B : QReg) (l : Layer) (e : KeyIndex) (message : HashInput)
    (base : Randomizer) :
    ∀ n trial, ReadsRel goodAll v (grindR M upd pub B l e message base n trial)
      (grindR Unit (keepUpd Unit) pub B l e message base n trial)
  | 0, _ => readsRel_pure v _
  | n + 1, trial => by
    rw [grindR, grindR]
    refine (readsRel_hashTrial pub.perm (upd l e) (keepUpd Unit l e) _).bind fun out ↦ ?_
    generalize Codeword.decode (truncateHash out) = d
    cases d with
    | none => exact readsRel_grindR pub B l e message base n (trial + 1)
    | some x => exact readsRel_pure v _

theorem dropRec_signLayerT (pub : Pub) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : HashInput) :
    DropRec ValPos (realizeT v (signLayerT M upd pub B l e message))
      (signLayerD Unit pub v B l e message) := by
  rw [signLayerT, signLayerD, realizeT_bind₂]
  refine DropRec.bind₂ (readsRel_grindR upd v pub B l e message _ _ _) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · exact DropRec.pure _
  · refine dropRec_revealThen v _ _ fun _ ↦ ?_
    rw [realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_progSlots v pub B _) fun _ ↦ DropRec.pure _

theorem dropRec_signT (pub : Pub) (B : QReg) (r : SigningRequest) :
    DropRec ValPos (realizeT v (signT M upd pub B r)) (signWith B (signLayerD Unit pub v B) r) := by
  rw [signT, signWith, realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_signLayerT upd v pub B _ _ _) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · exact DropRec.pure _
  · dsimp only
    rw [realizeT_bind₂]
    refine DropRec.bind₂ (dropRec_signLayerT upd v pub B _ _ _) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩
    · exact DropRec.pure _
    · exact DropRec.pure _

theorem dropRec_signAt (pub : Pub) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec (X × Z)).In (.sign r) × E) :
    DropRec ValPos (realizeT v (signAt M upd pub r E ℓ)) (signAtD Unit pub v r E ℓ) := by
  rw [signAt, signAtD, signAtWith]
  exact dropRec_realizeT_act_bind v _ fun _ ↦ dropRec_signT upd v pub _ r

theorem dropRec_challengeT (pub : Pub) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))).A A) :
    DropRec ValPos (realizeT v (challengeT M upd pub A c)) (challengeD Unit pub v A c) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact dropRec_readLift_liftOrdinary v _
  · exact dropRec_readLift_liftOrdinary v _
  · exact dropRec_realizeT_bind v (dropRec_signAt upd v pub r E ℓ) fun _ _ ↦ DropRec.pure _

/-- **The realized game drops to `gameD`**: with its record calls removed and its reads keeping
the memory `Unit`, the canonical game is `gameD Unit pub v A`. -/
theorem dropRec_gameT (pub : Pub) (A : Adversary (X × Z)) :
    DropRec ValPos (realizeT v (gameT M upd pub A)) (gameD Unit pub v A) := by
  refine dropRec_revealThen v _ _ fun _ ↦ ?_
  dsimp only
  rw [realizeT_bind₂, gameD]
  refine DropRec.bind₂ (dropRec_realizeT_substitute v (dropRec_challengeT upd v pub) _)
    fun run ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ ((readsRel_readsProgram pub.perm _).map Prod.fst) fun _ ↦ DropRec.pure _

end game

/-! ## Forgetting the memory -/

section forget

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {P : Type} [Fintype P] [DecidableEq P]

/-- The memory `p` dropped: `|D, W, ()⟩⟨D, W, p|`. -/
def memDrop (p : P) : Matrix (HwReg X Z Unit) (HwReg X Z P) ℂ :=
  Matrix.of fun b a ↦ if a.2.2 = p ∧ b = (a.1, a.2.1, ()) then 1 else 0

variable (X Z P) in
/-- **Forgetting the memory**: the partial trace over the (classical) memory register. -/
noncomputable def memFgt : MatrixMap (HwReg X Z P) (HwReg X Z Unit) :=
  ∑ p, MatrixMap.conj (memDrop p)

theorem one_kronecker_memDrop_mul_apply {I J : Type} [Fintype I] [DecidableEq I] (p : P)
    (N : Matrix (I × HwReg X Z P) J ℂ) (i' : I) (b : HwReg X Z Unit) (j : J) :
    (((1 : Matrix I I ℂ) ⊗ₖ memDrop p) * N : Matrix (I × HwReg X Z Unit) J ℂ) (i', b) j =
      N (i', (b.1, b.2.1, p)) j := by
  obtain ⟨D, W, ⟨⟩⟩ := b
  rw [Matrix.mul_apply, Finset.sum_eq_single (i', (D, W, p))]
  · simp [kroneckerMap_apply, memDrop]
  · rintro ⟨i'', D₁, W₁, m₁⟩ _ hne
    rw [kroneckerMap_apply]
    by_cases hi : i' = i''
    · subst hi
      simp only [memDrop, Matrix.of_apply, Matrix.one_apply_eq, one_mul]
      rw [ite_eq_right, zero_mul]
      rintro ⟨rfl, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      exact hne rfl
    · rw [Matrix.one_apply_ne hi]
      simp
  · simp

omit [Fintype P] in
theorem mul_one_kronecker_memDrop_apply {I J : Type} [Fintype I] [DecidableEq I] (p : P)
    (N : Matrix J (I × HwReg X Z Unit) ℂ) (j : J) (i : I) (a : HwReg X Z P) :
    (N * ((1 : Matrix I I ℂ) ⊗ₖ memDrop p) : Matrix J (I × HwReg X Z P) ℂ) j (i, a) =
      if a.2.2 = p then N j (i, (a.1, a.2.1, ())) else 0 := by
  obtain ⟨D, W, m⟩ := a
  rw [Matrix.mul_apply, Finset.sum_eq_single (i, (D, W, ()))]
  · simp [kroneckerMap_apply, memDrop]
  · rintro ⟨i'', D₁, W₁, ⟨⟩⟩ _ hne
    rw [kroneckerMap_apply]
    by_cases hi : i'' = i
    · subst hi
      simp only [memDrop, Matrix.of_apply, Matrix.one_apply_eq, one_mul]
      rw [ite_eq_right, mul_zero]
      rintro ⟨-, he⟩
      exact hne (by rw [he])
    · rw [Matrix.one_apply_ne hi]
      simp
  · simp

theorem memDrop_mul_apply {J : Type} (p : P) (N : Matrix (HwReg X Z P) J ℂ)
    (b : HwReg X Z Unit) (j : J) :
    (memDrop p * N : Matrix (HwReg X Z Unit) J ℂ) b j = N (b.1, b.2.1, p) j := by
  obtain ⟨D, W, ⟨⟩⟩ := b
  rw [Matrix.mul_apply, Finset.sum_eq_single (D, W, p)]
  · simp [memDrop]
  · rintro ⟨D₁, W₁, m₁⟩ _ hne
    simp only [memDrop, Matrix.of_apply]
    rw [ite_eq_right, zero_mul]
    rintro ⟨rfl, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact hne rfl
  · simp

omit [Fintype P] in
theorem mul_memDrop_apply {J : Type} (p : P) (N : Matrix J (HwReg X Z Unit) ℂ) (j : J)
    (a : HwReg X Z P) :
    (N * memDrop p : Matrix J (HwReg X Z P) ℂ) j a =
      if a.2.2 = p then N j (a.1, a.2.1, ()) else 0 := by
  obtain ⟨D, W, m⟩ := a
  rw [Matrix.mul_apply, Finset.sum_eq_single (D, W, ())]
  · simp [memDrop]
  · rintro ⟨D₁, W₁, ⟨⟩⟩ _ hne
    simp only [memDrop, Matrix.of_apply]
    rw [ite_eq_right, mul_zero]
    rintro ⟨-, he⟩
    exact hne (by rw [he])
  · simp

theorem sum_conjTranspose_memDrop_mul_self :
    ∑ p, (memDrop (X := X) (Z := Z) (P := P) p)ᴴ * memDrop p = 1 := by
  ext ⟨D', W', m'⟩ ⟨D, W, m⟩
  rw [Matrix.sum_apply]
  simp only [mul_memDrop_apply]
  simp only [conjTranspose_apply, memDrop, Matrix.of_apply, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Matrix.one_apply, Prod.mk.injEq]
  by_cases h : D' = D ∧ W' = W ∧ m' = m
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  · have h' : ¬ (m' = m ∧ D = D' ∧ W = W' ∧ True) := fun h' ↦
      h ⟨h'.2.1.symm, h'.2.2.1.symm, h'.1⟩
    simp only [h, h', ↓reduceIte, star_zero]

theorem amplifyLeft_memFgt (I : Type) [Fintype I] [DecidableEq I] :
    (memFgt X Z P).amplifyLeft I = ∑ p, MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ memDrop p) := by
  rw [memFgt, amplifyLeft_sum]
  simp only [MatrixMap.amplifyLeft_conj]

/-- Forgetting the memory keeps the trace. -/
theorem trace_memFgt (I : Type) [Fintype I] [DecidableEq I]
    (σ : Matrix (I × HwReg X Z P) (I × HwReg X Z P) ℂ) :
    ((memFgt X Z P).amplifyLeft I σ).trace = σ.trace := by
  rw [amplifyLeft_memFgt, LinearMap.sum_apply, trace_sum]
  simp only [MatrixMap.trace_conj_apply]
  rw [← trace_sum, ← Finset.sum_mul]
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronecker_right, sum_conjTranspose_memDrop_mul_self, one_kronecker_one, Matrix.one_mul]

theorem conj_single_apply {A B : Type} [Fintype A] [DecidableEq A] (K : Matrix B A ℂ) (s : A)
    (b b' : B) : MatrixMap.conj K (Matrix.single s s 1) b b' = K b s * star (K b' s) := by
  rw [MatrixMap.conj_apply, Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.mul_apply, Finset.sum_eq_single s]
    · simp [conjTranspose_apply]
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  · intro a _ ha
    rw [conjTranspose_apply, Matrix.mul_apply]
    simp [Ne.symm ha]
  · simp

/-- Forgetting the memory of a basis state. -/
theorem memFgt_single (a : HwReg X Z P) :
    memFgt X Z P (Matrix.single a a 1) = Matrix.single (a.1, a.2.1, ()) (a.1, a.2.1, ()) 1 := by
  rw [memFgt, LinearMap.sum_apply, Finset.sum_eq_single a.2.2]
  · ext b b'
    rw [conj_single_apply, Matrix.single_apply]
    by_cases hb : (a.1, a.2.1, ()) = b
    · by_cases hb' : (a.1, a.2.1, ()) = b'
      · subst hb hb'
        simp [memDrop]
      · simp [memDrop, Ne.symm hb', hb']
    · simp [memDrop, Ne.symm hb, hb]
  · intro p _ hp
    ext b b'
    rw [conj_single_apply]
    simp [memDrop, Ne.symm hp]
  · simp

theorem conj_conj_apply {A B C : Type} [Fintype A] [Fintype B] (K : Matrix C B ℂ)
    (K' : Matrix B A ℂ) (ρ : Matrix A A ℂ) :
    MatrixMap.conj K (MatrixMap.conj K' ρ) = MatrixMap.conj (K * K') ρ := by
  rw [MatrixMap.conj_mul, LinearMap.comp_apply]

theorem conj_ite_zero {A B : Type} [Fintype A] (c : Prop) [Decidable c] (K : Matrix B A ℂ)
    (ρ : Matrix A A ℂ) :
    MatrixMap.conj (if c then K else 0) ρ = if c then MatrixMap.conj K ρ else 0 := by
  split_ifs <;> simp

/-- A step that does not touch the memory commutes with forgetting it. -/
theorem conj_comp_memFgt {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (K₁ : Matrix (O × HwReg X Z P) (I × HwReg X Z P) ℂ)
    (K₂ : Matrix (O × HwReg X Z Unit) (I × HwReg X Z Unit) ℂ)
    (h : ∀ p, ((1 : Matrix O O ℂ) ⊗ₖ memDrop p) * K₁ = K₂ * ((1 : Matrix I I ℂ) ⊗ₖ memDrop p)) :
    MatrixMap.conj K₂ ∘ₗ (memFgt X Z P).amplifyLeft I =
      (memFgt X Z P).amplifyLeft O ∘ₗ MatrixMap.conj K₁ := by
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [LinearMap.comp_apply, amplifyLeft_memFgt, LinearMap.sum_apply, map_sum,
    conj_conj_apply, h]

/-- **A step that writes the memory, summed over the memory it read**, commutes with forgetting
the memory, when it acts as `K₂` beside the memory it read and moves that memory to `u p`. -/
theorem sum_memFgt_comp_conj {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (K₁ : P → Matrix (O × HwReg X Z P) (I × HwReg X Z P) ℂ)
    (K₂ : Matrix (O × HwReg X Z Unit) (I × HwReg X Z Unit) ℂ) (u : P → P)
    (h : ∀ p p', ((1 : Matrix O O ℂ) ⊗ₖ memDrop p') * K₁ p =
      if p' = u p then K₂ * ((1 : Matrix I I ℂ) ⊗ₖ memDrop p) else 0) :
    ∑ p, (memFgt X Z P).amplifyLeft O ∘ₗ MatrixMap.conj (K₁ p) =
      MatrixMap.conj K₂ ∘ₗ (memFgt X Z P).amplifyLeft I := by
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [LinearMap.comp_apply, amplifyLeft_memFgt, LinearMap.sum_apply, map_sum, conj_conj_apply, h, conj_ite_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- A classical step that reads the memory `p` and writes `g p`, acting on the databases by `R`
of the hardwired cells. -/
theorem memDrop_mul_clsKraus_mem (p p' : P) (g : P → P)
    (R : Hw X Z → Matrix (DbReg X Z) (DbReg X Z) ℂ) :
    memDrop p' * clsKraus (fun b : Hw X Z × P ↦ b.2 = p) (fun b ↦ (b.1, g b.2)) (fun b ↦ R b.1) =
      if p' = g p then
        clsKraus (fun b : Hw X Z × Unit ↦ b.2 = ()) (fun b ↦ (b.1, ())) (fun b ↦ R b.1) *
          memDrop p
      else 0 := by
  ext b a
  obtain ⟨D', W', ⟨⟩⟩ := b
  rw [memDrop_mul_apply]
  split_ifs with hp
  · rw [mul_memDrop_apply]
    by_cases hm : a.2.2 = p
    · subst hm hp
      simp [clsKraus_apply]
    · simp [clsKraus_apply, hm]
  · rw [Matrix.zero_apply, clsKraus_apply, ite_eq_right]
    rintro ⟨hm, he⟩
    rw [← hm] at hp
    exact hp (Prod.mk.inj he).2

/-- A classical step acting on the hardwired cells only. -/
theorem memDrop_mul_clsKraus_hw (p : P) (c : Hw X Z → Prop) [DecidablePred c]
    (f : Hw X Z → Hw X Z) (R : Hw X Z → Matrix (DbReg X Z) (DbReg X Z) ℂ) :
    memDrop p * clsKraus (fun b : Hw X Z × P ↦ c b.1) (fun b ↦ (f b.1, b.2)) (fun b ↦ R b.1) =
      clsKraus (fun b : Hw X Z × Unit ↦ c b.1) (fun b ↦ (f b.1, b.2)) (fun b ↦ R b.1) *
        memDrop p := by
  ext b a
  obtain ⟨D', W', ⟨⟩⟩ := b
  rw [memDrop_mul_apply, mul_memDrop_apply]
  by_cases hm : a.2.2 = p
  · subst hm
    simp [clsKraus_apply]
  · simp only [clsKraus_apply, hm, ↓reduceIte]
    rw [ite_eq_right]
    rintro ⟨-, he⟩
    exact hm (Prod.mk.inj he).2.symm

theorem one_kronecker_mul_one_kronecker {I : Type} [Fintype I] [DecidableEq I] {B C D : Type}
    [Fintype C] (K : Matrix B C ℂ) (K' : Matrix C D ℂ) :
    ((1 : Matrix I I ℂ) ⊗ₖ K) * ((1 : Matrix I I ℂ) ⊗ₖ K') = (1 : Matrix I I ℂ) ⊗ₖ (K * K') := by
  rw [← mul_kronecker_mul, Matrix.one_mul]

end forget

/-! ## Runtime 1 forgets the memory -/

section relabel

variable {A I O E D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype E] [DecidableEq E] [Fintype D₁] [DecidableEq D₁]
  [Fintype D₂] [DecidableEq D₂]

/-- A call (relabel, step beside `E`, relabel back) intertwines when its step does. -/
theorem intertwines_relabelFrame {ι : Type} (ℓ : A ≃ I × E) (V : MatrixMap D₁ D₂)
    (s₁ : SubInstrument (I × D₁) (O × D₁) ι) (s₂ : SubInstrument (I × D₂) (O × D₂) ι)
    (h : DSubInstrument.Intertwines (V.amplifyLeft I) (fun _ ↦ V.amplifyLeft O) s₁ s₂) :
    DSubInstrument.Intertwines (V.amplifyLeft A) (fun _ ↦ V.amplifyLeft (O × E))
      ((SubInstrument.relabel (queryEquivIn ℓ D₁)).bind fun _ ↦ (s₁.frame E).bind fun r ↦
        (SubInstrument.relabel (queryEquivOut O D₁ E)).bind fun _ ↦ SubInstrument.pure r)
      ((SubInstrument.relabel (queryEquivIn ℓ D₂)).bind fun _ ↦ (s₂.frame E).bind fun r ↦
        (SubInstrument.relabel (queryEquivOut O D₂ E)).bind fun _ ↦ SubInstrument.pure r) :=
  (intertwines_relabel_queryEquivIn V ℓ).bind fun _ ↦ (h.frame E).bind fun r ↦
    (intertwines_relabel_queryEquivOut V O E).bind fun _ ↦
      DSubInstrument.Intertwines.ret (fun _ ↦ V.amplifyLeft (O × E)) r

/-- A call whose steps, summed over a fiber of outcomes, intertwine. -/
theorem sum_relabelFrame {ι : Type} [Fintype ι] (ℓ : A ≃ I × E) (V : MatrixMap D₁ D₂)
    (s₁ : ι → MatrixMap (I × D₁) (O × D₁)) (s₂ : MatrixMap (I × D₂) (O × D₂))
    (h : ∑ j, V.amplifyLeft O ∘ₗ s₁ j = s₂ ∘ₗ V.amplifyLeft I) (ρ : Matrix (A × D₁) (A × D₁) ℂ) :
    ∑ j, V.amplifyLeft (O × E) ((SubInstrument.relabel (queryEquivOut O D₁ E)).branch ()
        ((s₁ j).amplify E ((SubInstrument.relabel (queryEquivIn ℓ D₁)).branch () ρ))) =
      (SubInstrument.relabel (queryEquivOut O D₂ E)).branch ()
        (s₂.amplify E ((SubInstrument.relabel (queryEquivIn ℓ D₂)).branch ()
          (V.amplifyLeft A ρ))) := by
  have hin := LinearMap.congr_fun (intertwines_relabel_queryEquivIn V ℓ ()) ρ
  simp only [LinearMap.comp_apply] at hin
  rw [hin, ← LinearMap.comp_apply (s₂.amplify E), ← MatrixMap.amplify_comp, ← h,
    MatrixMap.amplify_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hout := LinearMap.congr_fun (intertwines_relabel_queryEquivOut V O E ())
    ((s₁ j).amplify E ((SubInstrument.relabel (queryEquivIn ℓ D₁)).branch () ρ))
  simp only [LinearMap.comp_apply] at hout
  rw [MatrixMap.amplify_comp, LinearMap.comp_apply, hout]

end relabel

/-- Sequencing after a step whose outcomes `(y, p)` merge to `(y, ())`. -/
theorem intertwines_bind_fiber {Aτ A' B B' Y P : Type} [Fintype Aτ] [Fintype A'] [Fintype B]
    [Fintype B'] [Fintype Y] [Fintype P] {κ : Type*} {C C' : κ → Type*} [∀ c, Fintype (C c)]
    [∀ c, Fintype (C' c)] (VA : MatrixMap Aτ A') (VB : MatrixMap B B')
    (VC : ∀ c, MatrixMap (C c) (C' c)) (p₁ : SubInstrument Aτ B (Y × P))
    (p₂ : SubInstrument A' B' (Y × Unit)) (k₁ : Y × P → DSubInstrument B κ C)
    (k₂ : Y × Unit → DSubInstrument B' κ C')
    (hp : ∀ y ρ, ∑ p, VB (p₁.branch (y, p) ρ) = p₂.branch (y, ()) (VA ρ))
    (hk : ∀ y p, DSubInstrument.Intertwines VB VC (k₁ (y, p)) (k₂ (y, ()))) :
    DSubInstrument.Intertwines VA VC (DSubInstrument.bind p₁ k₁) (DSubInstrument.bind p₂ k₂) := by
  intro c
  refine LinearMap.ext fun ρ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, DSubInstrument.branch_bind_apply,
    DSubInstrument.branch_bind_apply, tsum_fintype, tsum_fintype, map_sum, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Fintype.sum_unique]
  have e : ∀ p, VC c ((k₁ (y, p)).branch c (p₁.branch (y, p) ρ)) =
      (k₂ (y, ())).branch c (VB (p₁.branch (y, p) ρ)) := fun p ↦ by
    have := LinearMap.congr_fun (hk y p c) (p₁.branch (y, p) ρ)
    simp only [LinearMap.comp_apply] at this
    exact this.symm
  simp only [e]
  rw [← map_sum, hp]

section steps

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] {P : Type} [Fintype P] [DecidableEq P]

/-- The sponge ports of runtime 1 do not read the memory. -/
theorem memDrop_mul_spongeU (L : Hw X Z) (m₀ : P) (i : SpongePort) (p : P) :
    ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ memDrop p) *
        (spongeHardwired1 X Z L m₀).U i =
      (spongeHardwired1 X Z L ()).U i *
        ((1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ memDrop p) := by
  rw [spongeHardwired1_U_eq, spongeHardwired1_U_eq]
  ext ⟨i', D', W', u⟩ ⟨i₀, D, W, m⟩
  rw [one_kronecker_memDrop_mul_apply, mul_one_kronecker_memDrop_apply]
  simp only [liftBlocks, submatrix_apply, hwSplit, Equiv.prodAssoc_symm_apply,
    blockDiagonal_apply, Prod.mk.injEq]
  by_cases hm : m = p
  · subst hm
    simp only [and_true, ↓reduceIte]
    rfl
  · simp [hm, Ne.symm hm]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The program ports do not read the memory. -/
theorem memDrop_mul_hwProgKraus (c : HwProg X Z) (r : c.Result) (p : P) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ memDrop p) * hwProgKraus (M := P) c r =
      hwProgKraus (M := Unit) c r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ memDrop p) := by
  cases c with
  | programH z v =>
    change _ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ _) = ((1 : Matrix Unit Unit ℂ) ⊗ₖ _) * _
    rw [one_kronecker_mul_one_kronecker, one_kronecker_mul_one_kronecker]
    exact congrArg _ (memDrop_mul_clsKraus_hw p (fun W ↦ W.1 z = r.2)
      (fun W ↦ (Function.update W.1 z (some v), W.2)) fun _ ↦ cellDiscard z r.1 ⊗ₖ 1)
  | programK x v =>
    change _ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ _) = ((1 : Matrix Unit Unit ℂ) ⊗ₖ _) * _
    rw [one_kronecker_mul_one_kronecker, one_kronecker_mul_one_kronecker]
    exact congrArg _ (memDrop_mul_clsKraus_hw p (fun W ↦ W.2.1 x = r.2)
      (fun W ↦ (W.1, Function.update W.2.1 x (some v), W.2.2)) fun _ ↦
        (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (cellDiscard x r.1 ⊗ₖ 1))
  | programK' x v =>
    change _ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ _) = ((1 : Matrix Unit Unit ℂ) ⊗ₖ _) * _
    rw [one_kronecker_mul_one_kronecker, one_kronecker_mul_one_kronecker]
    exact congrArg _ (memDrop_mul_clsKraus_hw p (fun W ↦ W.2.2 x = r.2)
      (fun W ↦ (W.1, W.2.1, Function.update W.2.2 x (some v))) fun _ ↦
        (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ (1 ⊗ₖ cellDiscard x r.1))

omit [AddCommGroup X] [AddCommGroup Z] in
/-- A classical step reading the memory `p` and writing `g p`, beside the trivial register. -/
theorem one_kronecker_memDrop_mul_clsKraus_mem (p p' : P) (g : P → P)
    (R : Hw X Z → Matrix (DbReg X Z) (DbReg X Z) ℂ) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ memDrop p') * ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        clsKraus (fun b : Hw X Z × P ↦ b.2 = p) (fun b ↦ (b.1, g b.2)) (fun b ↦ R b.1)) =
      if p' = g p then
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ
          clsKraus (fun b : Hw X Z × Unit ↦ b.2 = ()) (fun b ↦ (b.1, ())) (fun b ↦ R b.1)) *
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ memDrop p)
      else 0 := by
  rw [one_kronecker_mul_one_kronecker, one_kronecker_mul_one_kronecker, memDrop_mul_clsKraus_mem]
  by_cases hp : p' = g p
  · simp [hp]
  · simp [hp]

variable [Nonempty X] [Nonempty Z]

theorem intertwines_sponge_step (L : Hw X Z) (m₀ : P) (i : SpongePort) :
    DSubInstrument.Intertwines ((memFgt X Z P).amplifyLeft (spongeIn X Z i))
      (fun _ ↦ (memFgt X Z P).amplifyLeft (spongeIn X Z i))
      ((runtime1 X Z L m₀).step (.inl (.inl i))) ((runtime1 X Z L ()).step (.inl (.inl i))) :=
  fun _ ↦ by
    change MatrixMap.conj ((spongeHardwired1 X Z L ()).U i) ∘ₗ _ =
      _ ∘ₗ MatrixMap.conj ((spongeHardwired1 X Z L m₀).U i)
    exact conj_comp_memFgt _ _ (memDrop_mul_spongeU L m₀ i)

theorem intertwines_prog_step (L : Hw X Z) (m₀ : P) (c : HwProg X Z) :
    DSubInstrument.Intertwines ((memFgt X Z P).amplifyLeft Unit)
      (fun _ ↦ (memFgt X Z P).amplifyLeft Unit)
      ((runtime1 X Z L m₀).step (.inr c)) ((runtime1 X Z L ()).step (.inr c)) := by
  rcases c with ⟨z, v⟩ | ⟨x, v⟩ | ⟨x, v⟩
  · intro r
    exact conj_comp_memFgt (hwProgKraus (M := P) (.programH z v) r)
      (hwProgKraus (M := Unit) (.programH z v) r) fun p ↦
        memDrop_mul_hwProgKraus (.programH z v) r p
  · intro r
    exact conj_comp_memFgt (hwProgKraus (M := P) (.programK x v) r)
      (hwProgKraus (M := Unit) (.programK x v) r) fun p ↦
        memDrop_mul_hwProgKraus (.programK x v) r p
  · intro r
    exact conj_comp_memFgt (hwProgKraus (M := P) (.programK' x v) r)
      (hwProgKraus (M := Unit) (.programK' x v) r) fun p ↦
        memDrop_mul_hwProgKraus (.programK' x v) r p

theorem sum_readH_step (L : Hw X Z) (m₀ : P) (z : Z) (upd : P → Option X → P) (o : Option X) :
    ∑ p, (memFgt X Z P).amplifyLeft Unit ∘ₗ
        ((runtime1 X Z L m₀).step (.inl (.inr (.readH z upd)))).branch (o, p) =
      ((runtime1 X Z L ()).step (.inl (.inr (.readH z keepMem)))).branch (o, ()) ∘ₗ
        (memFgt X Z P).amplifyLeft Unit := by
  change ∑ p, _ ∘ₗ MatrixMap.conj (hwReadKraus1 L (.readH z upd) (o, p)) =
    MatrixMap.conj (hwReadKraus1 L (.readH z keepMem) (o, ())) ∘ₗ _
  exact sum_memFgt_comp_conj (fun p ↦ hwReadKraus1 L (.readH z upd) (o, p))
    (hwReadKraus1 L (.readH z keepMem) (o, ())) (fun p ↦ upd p o) fun p p' ↦
      one_kronecker_memDrop_mul_clsKraus_mem p p' (fun _ ↦ upd p o) fun W ↦
        cellRead (hwView W L).1 z o ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ)

theorem sum_readK_step (L : Hw X Z) (m₀ : P) (x : X) (upd : P → Option Z → P) (o : Option Z) :
    ∑ p, (memFgt X Z P).amplifyLeft Unit ∘ₗ
        ((runtime1 X Z L m₀).step (.inl (.inr (.readK x upd)))).branch (o, p) =
      ((runtime1 X Z L ()).step (.inl (.inr (.readK x keepMem)))).branch (o, ()) ∘ₗ
        (memFgt X Z P).amplifyLeft Unit := by
  change ∑ p, _ ∘ₗ MatrixMap.conj (hwReadKraus1 L (.readK x upd) (o, p)) =
    MatrixMap.conj (hwReadKraus1 L (.readK x keepMem) (o, ())) ∘ₗ _
  exact sum_memFgt_comp_conj (fun p ↦ hwReadKraus1 L (.readK x upd) (o, p))
    (hwReadKraus1 L (.readK x keepMem) (o, ())) (fun p ↦ upd p o) fun p p' ↦
      one_kronecker_memDrop_mul_clsKraus_mem p p' (fun _ ↦ upd p o) fun W ↦
        (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          (cellRead (hwView W L).2.1 x o ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))

theorem sum_readK'_step (L : Hw X Z) (m₀ : P) (x : X) (upd : P → Option Z → P) (o : Option Z) :
    ∑ p, (memFgt X Z P).amplifyLeft Unit ∘ₗ
        ((runtime1 X Z L m₀).step (.inl (.inr (.readK' x upd)))).branch (o, p) =
      ((runtime1 X Z L ()).step (.inl (.inr (.readK' x keepMem)))).branch (o, ()) ∘ₗ
        (memFgt X Z P).amplifyLeft Unit := by
  change ∑ p, _ ∘ₗ MatrixMap.conj (hwReadKraus1 L (.readK' x upd) (o, p)) =
    MatrixMap.conj (hwReadKraus1 L (.readK' x keepMem) (o, ())) ∘ₗ _
  exact sum_memFgt_comp_conj (fun p ↦ hwReadKraus1 L (.readK' x upd) (o, p))
    (hwReadKraus1 L (.readK' x keepMem) (o, ())) (fun p ↦ upd p o) fun p p' ↦
      one_kronecker_memDrop_mul_clsKraus_mem p p' (fun _ ↦ upd p o) fun W ↦
        (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead (hwView W L).2.2 x o)

end steps

section records

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]

/-- The record operator of `T` on the memory `m`, without the trivial register. -/
noncomputable def recC (T : Finset S) (m : Finset S × M) :
    Matrix (HwReg X Z (Finset S × M)) (HwReg X Z (Finset S × M)) ℂ :=
  clsKraus (fun b : Hw X Z × (Finset S × M) ↦ b.2 = m) (fun b ↦ (b.1, (b.2.1 ∪ T, b.2.2)))
    fun _ ↦ 1

omit [Fintype S] [Fintype M] in
theorem clsKraus_unit_one :
    clsKraus (fun b : Hw X Z × Unit ↦ b.2 = ()) (fun b ↦ (b.1, ()))
      (fun _ ↦ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) = 1 := by
  ext ⟨D', W', u'⟩ ⟨D, W, u⟩
  by_cases hW : W' = W
  · subst hW
    simp [clsKraus_apply, Matrix.one_apply]
  · have : ((D', W', u') : HwReg X Z Unit) ≠ (D, W, u) := fun h ↦ hW (by
      simp only [Prod.mk.injEq] at h
      exact h.2.1)
    simp [clsKraus_apply, Matrix.one_apply_ne this, hW]

/-- **Records, summed over the memory before them**, are forgotten with the memory. -/
theorem sum_memFgt_recC (T : Finset S) (A : Type) [Fintype A] [DecidableEq A]
    (ρ : Matrix (A × HwReg X Z (Finset S × M)) (A × HwReg X Z (Finset S × M)) ℂ) :
    ∑ r, (memFgt X Z (Finset S × M)).amplifyLeft A
        ((MatrixMap.conj (recC (X := X) (Z := Z) T r)).amplifyLeft A ρ) =
      (memFgt X Z (Finset S × M)).amplifyLeft A ρ := by
  have h := sum_memFgt_comp_conj (I := A) (O := A)
    (fun r : Finset S × M ↦ (1 : Matrix A A ℂ) ⊗ₖ recC (X := X) (Z := Z) T r) 1
    (fun r : Finset S × M ↦ (r.1 ∪ T, r.2)) fun r p' ↦ by
      rw [one_kronecker_mul_one_kronecker, recC, memDrop_mul_clsKraus_mem r p'
        (fun r : Finset S × M ↦ (r.1 ∪ T, r.2)) fun _ ↦ 1, clsKraus_unit_one]
      by_cases hp : p' = (r.1 ∪ T, r.2)
      · simp [hp]
      · simp [hp]
  have h' := LinearMap.congr_fun h ρ
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, MatrixMap.conj_one, LinearMap.id_apply]
    at h'
  simp only [MatrixMap.amplifyLeft_conj]
  exact h'

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]

variable (X Z) in
/-- Runtime 1 with record ports, its register written out. -/
@[reducible]
noncomputable def runtime1RD (L : Hw X Z) (m₀ : Finset S × M) :
    QuantumRuntime (recHwSpec X Z S M) where
  D := QReg.of (HwReg X Z (Finset S × M))
  init := initHw X Z m₀
  step := (runtime1R X Z L m₀).step

/-- A record call followed by the relabelling back: the record operator beside the register. -/
theorem relabel_queryStep_rec (L : Hw X Z) (m₀ : Finset S × M) (T : Finset S) {A E : QReg}
    (ℓ : A ≃ (recHwSpec X Z S M).In (.inr T) × E) (e : (recHwSpec X Z S M).Out (.inr T) × E ≃ A)
    (he : ∀ a, e (ℓ a) = a) (r : (recHwSpec X Z S M).Result (.inr T))
    (ρ : Matrix (A × HwReg X Z (Finset S × M)) (A × HwReg X Z (Finset S × M)) ℂ) :
    ((SubInstrument.relabel e).branch ()).amplify (HwReg X Z (Finset S × M))
        (((runtime1RD X Z L m₀).queryStep (.inr T) E ℓ).branch r ρ) =
      (MatrixMap.conj (recC T r)).amplifyLeft A ρ := by
  let _ : Unique ((recHwSpec X Z S M).In (.inr T)) := inferInstanceAs (Unique Unit)
  let _ : Unique ((recHwSpec X Z S M).Out (.inr T)) := inferInstanceAs (Unique Unit)
  rw [queryStep_branch_apply, DSubInstrument.branch_frame_apply,
    show ((runtime1RD X Z L m₀).step (.inr T)).branch r = MatrixMap.conj (recKraus T r) from
      recStep_branch T r]
  exact relabel_frame_step ℓ e
    (fun a ↦ (congrArg e (Prod.ext (Subsingleton.elim _ _) rfl)).trans (he a)) _ (recC T r)
    (fun o i h h' ↦ by
      have e₀ : recKraus (X := X) (Z := Z) T r (o, h) (i, h') =
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ recC T r) ((), h) ((), h') := rfl
      exact e₀.trans (by rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul])) ρ

/-- The run of a record call followed by the relabelling back. -/
theorem run_record_branch (L : Hw X Z) (m₀ : Finset S × M) {Ω : QReg → Type w} {A : QReg}
    (T : Finset S) (E : QReg) (ℓ : A ≃ (recHwSpec X Z S M).In (.inr T) × E)
    (e : (recHwSpec X Z S M).Out (.inr T) × E ≃ A) (he : ∀ a, e (ℓ a) = a)
    (k : (recHwSpec X Z S M).Result (.inr T) →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A)
    (q : Σ u, Ω u)
    (ρ : Matrix (A × HwReg X Z (Finset S × M)) (A × HwReg X Z (Finset S × M)) ℂ) :
    ((runtime1RD X Z L m₀).run .instruments
        (QuantumComp.queryBind (spec := recHwSpec X Z S M) (.inr T) E ℓ fun r ↦
          QuantumComp.primBind (L := LocalSig.instruments.{0})
            ⟨Unit, fun _ ↦ A, SubInstrument.relabel e⟩ fun _ ↦ k r)).branch q ρ =
      ∑' r, ((runtime1RD X Z L m₀).run .instruments (k r)).branch q
        ((MatrixMap.conj (recC T r)).amplifyLeft A ρ) := by
  rw [run_queryBind, DSubInstrument.branch_bind_apply]
  refine tsum_congr fun r ↦ ?_
  rw [run_primBind, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    DSubInstrument.branch_frame_apply, ← relabel_queryStep_rec L m₀ T ℓ e he r ρ]
  rfl

/-- **The simulation**: along `DropRec`, the run against runtime 1 with the memory `Unit` after
forgetting the memory is forgetting the memory after the run against runtime 1 with record
ports, for every input. -/
theorem dropRec_intertwines (L : Hw X Z) (m₀ : Finset S × M) {Ω : QReg → Type w} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A}
    {y : QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω A} (h : DropRec S x y) :
    DSubInstrument.Intertwines ((memFgt X Z (Finset S × M)).amplifyLeft A)
      (fun q : Σ u, Ω u ↦ (memFgt X Z (Finset S × M)).amplifyLeft q.1)
      ((runtime1RD X Z L m₀).run .instruments x) ((runtime1 X Z L ()).run .instruments y) := by
  induction h with
  | pure y =>
    rw [run_pure, run_pure]
    exact DSubInstrument.Intertwines.ret
      (B := fun p : Σ u, Ω u ↦ p.1 × (runtime1RD X Z L m₀).D)
      (B' := fun p : Σ u, Ω u ↦ p.1 × (runtime1 X Z L ()).D)
      (fun p ↦ (memFgt X Z (Finset S × M)).amplifyLeft p.1) ⟨_, y⟩
  | prim o _ ih =>
    rw [run_primBind, run_primBind]
    exact (DSubInstrument.Intertwines.frame_amplifyLeft (LocalSig.Interp.instruments o) _).bind ih
  | sponge i E ℓ _ ih =>
    erw [run_queryBind, run_queryBind]
    exact (intertwines_relabelFrame ℓ _ _ _ (intertwines_sponge_step L m₀ i)).bind ih
  | prog c E ℓ _ ih =>
    erw [run_queryBind, run_queryBind]
    exact (intertwines_relabelFrame ℓ _ _ _ (intertwines_prog_step L m₀ c)).bind ih
  | readH z upd E ℓ _ ih =>
    erw [run_queryBind, run_queryBind]
    refine intertwines_bind_fiber _ _ _ _ _ _ _ (fun o ρ ↦ ?_) ih
    have key := sum_relabelFrame ℓ _ _ _ (sum_readH_step L m₀ z upd o) ρ
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) (key.trans ?_)
    · erw [queryStep_branch_apply, DSubInstrument.branch_frame_apply]
      try rfl
    · erw [queryStep_branch_apply, DSubInstrument.branch_frame_apply]
      try rfl
  | readK x' upd E ℓ _ ih =>
    erw [run_queryBind, run_queryBind]
    refine intertwines_bind_fiber _ _ _ _ _ _ _ (fun o ρ ↦ ?_) ih
    have key := sum_relabelFrame ℓ _ _ _ (sum_readK_step L m₀ x' upd o) ρ
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) (key.trans ?_)
    · erw [queryStep_branch_apply, DSubInstrument.branch_frame_apply]
      try rfl
    · erw [queryStep_branch_apply, DSubInstrument.branch_frame_apply]
      try rfl
  | readK' x' upd E ℓ _ ih =>
    erw [run_queryBind, run_queryBind]
    refine intertwines_bind_fiber _ _ _ _ _ _ _ (fun o ρ ↦ ?_) ih
    have key := sum_relabelFrame ℓ _ _ _ (sum_readK'_step L m₀ x' upd o) ρ
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) (key.trans ?_)
    · erw [queryStep_branch_apply, DSubInstrument.branch_frame_apply]
      try rfl
    · erw [queryStep_branch_apply, DSubInstrument.branch_frame_apply]
      try rfl
  | @record A₀ T E ℓ e he k y₀ _ ih =>
    intro q
    refine LinearMap.ext fun ρ ↦ ?_
    let _ : Fintype ((recHwSpec X Z S M).Result (.inr T)) := inferInstanceAs (Fintype (Finset S × M))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, run_record_branch L m₀ T E ℓ e he k q,
      tsum_fintype, map_sum]
    have h1 : ∀ r, (memFgt X Z (Finset S × M)).amplifyLeft q.1
        (((runtime1RD X Z L m₀).run .instruments (k r)).branch q
          ((MatrixMap.conj (recC T r)).amplifyLeft A₀ ρ)) =
        ((runtime1 X Z L ()).run .instruments y₀).branch q
          ((memFgt X Z (Finset S × M)).amplifyLeft A₀
            ((MatrixMap.conj (recC T r)).amplifyLeft A₀ ρ)) := fun r ↦ by
      have := LinearMap.congr_fun (ih r q) ((MatrixMap.conj (recC T r)).amplifyLeft A₀ ρ)
      simp only [LinearMap.comp_apply] at this
      exact this.symm
    simp only [h1]
    rw [← map_sum]
    exact congrArg _ (sum_memFgt_recC T A₀ ρ).symm

/-- **Forgetting the record ports and the memory** (`DropRec`): runtime 1 with record ports from
any memory `m₀` running `x` has the law of runtime 1 with the memory `Unit` running `y`. -/
theorem evalDistMap_runtime1R_eq (L : Hw X Z) (m₀ : Finset S × M) {Ω : QReg → Type w}
    {A : QReg} {x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A}
    {y : QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω A} (h : DropRec S x y)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ] (f : (Σ u, Ω u) → γ) :
    (runtime1R X Z L m₀).evalDistMap .instruments x ρ f =
      (runtime1 X Z L ()).evalDistMap .instruments y ρ f := by
  change (runtime1RD X Z L m₀).evalDistMap .instruments x ρ f = _
  rw [QuantumRuntime.evalDistMap, QuantumRuntime.evalDistMap]
  congr 1
  funext p
  have hinit : (memFgt X Z (Finset S × M)).amplifyLeft A
      (ρ.matrix ⊗ₖ (runtime1RD X Z L m₀).init.matrix) =
      ρ.matrix ⊗ₖ (runtime1 X Z L ()).init.matrix := by
    rw [MatrixMap.amplifyLeft_kronecker]
    change ρ.matrix ⊗ₖ memFgt X Z (Finset S × M) (initHw X Z m₀).matrix =
      ρ.matrix ⊗ₖ (initHw X Z ()).matrix
    rw [initHw, initHw, SubState.matrix_basis, SubState.matrix_basis, memFgt_single]
  have ht : ((runtime1 X Z L ()).jointPost .instruments y ρ p).matrix.trace =
      ((runtime1RD X Z L m₀).jointPost .instruments x ρ p).matrix.trace := by
    rw [QuantumRuntime.matrix_jointPost, QuantumRuntime.matrix_jointPost, ← hinit]
    have := LinearMap.congr_fun (dropRec_intertwines L m₀ h p)
      (ρ.matrix ⊗ₖ (runtime1RD X Z L m₀).init.matrix)
    simp only [LinearMap.comp_apply] at this
    rw [this, trace_memFgt]
  rw [ht]

end records


end Quantum.Xmss.Assembly

end
