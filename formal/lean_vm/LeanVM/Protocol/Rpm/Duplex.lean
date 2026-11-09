/-
  LeanVM.Protocol.Rpm.Duplex

  The duplex discipline of the verifier and of the honest prover: every permutation query keeps
  lanes `16..24` of the zero state or of an earlier answer.
-/

import LeanVM.Protocol.LeanVM
import LeanVM.Protocol.WithHash

/-!
# The duplex discipline

The transfer from the two-oracle random-oracle model to the random-permutation model
(`Common.keccak256_transfer2`) asks of the honest parties' direct calls of the permutation a
*duplex discipline* (`Common.Duplex`): every call absorbs a non-final block into the initial
state or into the answer of an earlier call, keeping the capacity. On leanVM's states this is
`DuplexVm`: every query `F x` keeps lanes `16..24` of the zero state or of an earlier answer
(`AdmissibleVm`); lane `16` holds the padding's last byte, lanes `17..24` the capacity.

leanVM's Fiat-Shamir sponge (`Statement/LeanVmVerifier.lean`) follows it: its seed is
`F (seedInput iv publicInput)`, zero from lane `8` on, and each later call is
`F (duplexInput sp)`, which overwrites lanes `0..15` and keeps lanes `16..24` of the sponge's
state, itself the seed or a later answer. Hence `duplexVm_verifier` and, for the honest prover
followed by the verifier, `duplexVm_honest`.

The proofs carry a postcondition (`DuplexP`): a computation follows the discipline from the
answers `hist`, and each of its outcomes satisfies `Q` with the answers at its end.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Prover (Tree buildTreeWithHash parentsWithHash levelsWithHash powStepM searchM findNonceM)
open OracleComp OracleSpec

/-! ## The discipline -/

/-- A direct call at `x` is admissible after the answers `hist` of earlier direct calls: `x`
keeps lanes `16..24` of the zero state or of an earlier answer. -/
def AdmissibleVm (hist : List KeccakState) (x : KeccakState) : Prop :=
  (∀ i : Fin 25, 16 ≤ i.val → x[i] = 0) ∨ ∃ y ∈ hist, ∀ i : Fin 25, 16 ≤ i.val → x[i] = y[i]

/-- The duplex discipline of an oracle computation (as `Common.Duplex`,
`common/Common/Transfer2.lean`): along every run, every permutation query is admissible after
the answers of the earlier ones (newest first). -/
def DuplexVm {α : Type} : OracleComp KeccakCalls α → List KeccakState → Prop
  | .pure _, _ => True
  | .liftBind (.inr x) k, hist => AdmissibleVm hist x ∧ ∀ y, DuplexVm (k y) (y :: hist)
  | .liftBind _ k, hist => ∀ u, DuplexVm (k u) hist

/-- The duplex discipline with a postcondition: every permutation query is admissible, and every
outcome satisfies `Q` with the answers at the end of its run. -/
def DuplexP {α : Type} : OracleComp KeccakCalls α → List KeccakState → (α → List KeccakState → Prop) → Prop
  | .pure a, hist, Q => Q a hist
  | .liftBind (.inr x) k, hist, Q => AdmissibleVm hist x ∧ ∀ y, DuplexP (k y) (y :: hist) Q
  | .liftBind _ k, hist, Q => ∀ u, DuplexP (k u) hist Q

/-- A computation that queries the hash only. -/
def HOnly {α : Type} : OracleComp KeccakCalls α → Prop
  | .pure _ => True
  | .liftBind (.inr _) _ => False
  | .liftBind _ k => ∀ u, HOnly (k u)

section Rules

variable {α β : Type}

theorem admissibleVm_mono {h h' : List KeccakState} (hs : h ⊆ h') {x : KeccakState}
    (hx : AdmissibleVm h x) : AdmissibleVm h' x := by
  rcases hx with hx | ⟨y, hy, hx⟩
  · exact Or.inl hx
  · exact Or.inr ⟨y, hs hy, hx⟩

theorem duplexP_queryF_bind (x : KeccakState) (k : KeccakState → OracleComp KeccakCalls α) (h : List KeccakState)
    (Q : α → List KeccakState → Prop) :
    DuplexP (callKeccakF1600 x >>= k) h Q ↔ AdmissibleVm h x ∧ ∀ y, DuplexP (k y) (y :: h) Q :=
  Iff.rfl

theorem duplexVm_query_bind (t : KeccakCalls.Domain) (k : KeccakCalls.Range t → OracleComp KeccakCalls α)
    (h : List KeccakState) :
    DuplexVm (liftM (KeccakCalls.query t) >>= k) h ↔
      match t with
      | .inr x => AdmissibleVm h x ∧ ∀ y, DuplexVm (k y) (y :: h)
      | .inl _ => ∀ u, DuplexVm (k u) h := by
  rcases t with x | x <;> exact Iff.rfl

theorem duplexP_query_bind (t : KeccakCalls.Domain) (k : KeccakCalls.Range t → OracleComp KeccakCalls α)
    (h : List KeccakState) (Q : α → List KeccakState → Prop) :
    DuplexP (liftM (KeccakCalls.query t) >>= k) h Q ↔
      match t with
      | .inr x => AdmissibleVm h x ∧ ∀ y, DuplexP (k y) (y :: h) Q
      | .inl _ => ∀ u, DuplexP (k u) h Q := by
  rcases t with x | x <;> exact Iff.rfl

theorem hOnly_query_bind (t : KeccakCalls.Domain) (k : KeccakCalls.Range t → OracleComp KeccakCalls α) :
    HOnly (liftM (KeccakCalls.query t) >>= k) ↔
      match t with
      | .inr _ => False
      | .inl _ => ∀ u, HOnly (k u) := by
  rcases t with x | x <;> exact Iff.rfl

/-- The discipline without postcondition is the discipline with the trivial one. -/
theorem duplexVm_iff_duplexP (X : OracleComp KeccakCalls α) (h : List KeccakState) :
    DuplexVm X h ↔ DuplexP X h fun _ _ ↦ True := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => exact Iff.rfl
  | query_bind t k ih =>
    rw [duplexVm_query_bind, duplexP_query_bind]
    rcases t with x | x
    · exact forall_congr' fun u ↦ ih u h
    · exact and_congr Iff.rfl (forall_congr' fun y ↦ ih y _)

/-- A weaker postcondition. -/
theorem DuplexP.mono {X : OracleComp KeccakCalls α} {h : List KeccakState}
    {Q R : α → List KeccakState → Prop} (hX : DuplexP X h Q) (hQR : ∀ a h', Q a h' → R a h') :
    DuplexP X h R := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => exact hQR a h hX
  | query_bind t k ih =>
    rw [duplexP_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y)⟩

/-- **The answers only grow**: an outcome's answers contain the answers at the start. -/
theorem DuplexP.grow {X : OracleComp KeccakCalls α} {h : List KeccakState}
    {Q : α → List KeccakState → Prop} (hX : DuplexP X h Q) :
    DuplexP X h fun a h' ↦ Q a h' ∧ h ⊆ h' := by
  suffices ∀ h₀ : List KeccakState, h₀ ⊆ h → DuplexP X h fun a h' ↦ Q a h' ∧ h₀ ⊆ h' from
    this h (List.Subset.refl h)
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => exact fun h₀ hs ↦ ⟨hX, hs⟩
  | query_bind t k ih =>
    intro h₀ hs
    rw [duplexP_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u) h₀ hs
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y) h₀ (List.subset_cons_of_subset y hs)⟩

/-- **Sequencing.** -/
theorem DuplexP.bind {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {h : List KeccakState} {Q : α → List KeccakState → Prop} {R : β → List KeccakState → Prop}
    (hX : DuplexP X h Q) (hf : ∀ a h', Q a h' → DuplexP (f a) h' R) :
    DuplexP (X >>= f) h R := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => simpa using hf a h hX
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [duplexP_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y)⟩

/-- **Monotonicity in the earlier answers.** -/
theorem DuplexP.of_subset {X : OracleComp KeccakCalls α} {h h' : List KeccakState}
    {Q : α → List KeccakState → Prop} (hX : DuplexP X h Q) (hs : h ⊆ h')
    (hQ : ∀ a h₁ h₂, h₁ ⊆ h₂ → Q a h₁ → Q a h₂) : DuplexP X h' Q := by
  induction X using OracleComp.inductionOn generalizing h h' with
  | pure a => exact hQ a h h' hs hX
  | query_bind t k ih =>
    rw [duplexP_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u) hs
    · exact ⟨admissibleVm_mono hs hX.1,
        fun y ↦ ih y (hX.2 y) (List.cons_subset_cons y hs)⟩

/-- **Monotonicity in the earlier answers**, without postcondition. -/
theorem DuplexVm.of_subset {X : OracleComp KeccakCalls α} {h h' : List KeccakState} (hX : DuplexVm X h)
    (hs : h ⊆ h') : DuplexVm X h' := by
  rw [duplexVm_iff_duplexP] at hX ⊢
  exact hX.of_subset hs fun _ _ _ _ _ ↦ trivial

/-- **Sequencing** without postcondition: a disciplined computation, then disciplined
continuations from no answer. -/
theorem DuplexVm.bind {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {h : List KeccakState} (hX : DuplexVm X h) (hf : ∀ a, DuplexVm (f a) []) :
    DuplexVm (X >>= f) h := by
  rw [duplexVm_iff_duplexP] at hX ⊢
  exact hX.bind fun a h' _ ↦ (duplexVm_iff_duplexP _ _).mp ((hf a).of_subset (List.nil_subset _))

/-- A computation that only hashes keeps the discipline, and its answers. -/
theorem HOnly.duplexP {X : OracleComp KeccakCalls α} (hX : HOnly X) (h : List KeccakState) :
    DuplexP X h fun _ h' ↦ h' = h := by
  induction X using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [hOnly_query_bind] at hX
    rw [duplexP_query_bind]
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact hX.elim

theorem hOnly_pure (a : α) : HOnly (pure a : OracleComp KeccakCalls α) := trivial

theorem HOnly.bind {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β} (hX : HOnly X)
    (hf : ∀ a, HOnly (f a)) : HOnly (X >>= f) := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [hOnly_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact hX

theorem hOnly_queryH (x : Bytes) : HOnly (callKeccak256 x) := by
  have : HOnly (callKeccak256 x >>= pure) := (hOnly_query_bind (.inl x) pure).mpr fun _ ↦ trivial
  simpa using this

theorem hOnly_mapM {γ : Type} (f : γ → OracleComp KeccakCalls β) (hf : ∀ c, HOnly (f c)) :
    ∀ l : List γ, HOnly (l.mapM f)
  | [] => trivial
  | c :: l => by
    rw [List.mapM_cons]
    exact (hf c).bind fun _ ↦ (hOnly_mapM f hf l).bind fun _ ↦ trivial

end Rules

/-! ## The sponge -/

theorem lane_eq_getElem_fin (a : KeccakState) (i : Fin 25) : Keccak.lane a i = a[i] := by
  simp [Keccak.lane, Array.getD_eq_getD_getElem?]

/-- A permutation of the sponge keeps lanes `16..24` of its state. -/
theorem admissibleVm_duplexInput {h : List KeccakState} {sp : Sponge} (hs : sp.state ∈ h) :
    AdmissibleVm h (duplexInput sp) := by
  refine Or.inr ⟨sp.state, hs, fun i hi ↦ ?_⟩
  have : ¬ (i.val < 16) := by omega
  simp [duplexInput, lane_eq_getElem_fin, this]

theorem duplexP_duplex {h : List KeccakState} {sp : Sponge} (hs : sp.state ∈ h) :
    DuplexP (duplex callKeccakF1600 sp) h fun sp' h' ↦ sp'.state ∈ h' := by
  simp only [duplex]
  exact (duplexP_queryF_bind _ _ _ _).mpr
    ⟨admissibleVm_duplexInput hs, fun y ↦ List.mem_cons_self⟩

theorem duplexP_absorb {h : List KeccakState} {sp : Sponge} (hs : sp.state ∈ h) (x : E) (tag : ℕ) :
    DuplexP (Compile.absorb callKeccakF1600 sp x tag) h fun sp' h' ↦ sp'.state ∈ h' := by
  simp only [Compile.absorb]
  split
  · exact (duplexP_duplex hs).bind fun sp' h' hsp ↦ hsp
  · exact hs

theorem duplexP_squeeze {h : List KeccakState} {sp : Sponge} (hs : sp.state ∈ h) :
    DuplexP (squeeze callKeccakF1600 sp) h fun r h' ↦ r.2.state ∈ h' := by
  simp only [squeeze]
  exact (duplexP_duplex hs).bind fun sp' h' hsp ↦ hsp

/-! ## The verifier -/

theorem hOnly_climb : ∀ (node : Digest) (q : ℕ) (path : List Digest),
    HOnly (climbWithHash callKeccak256 node q path)
  | _, _, [] => trivial
  | node, q, s :: ss => by
    simp only [climbWithHash]
    split <;> exact (hOnly_queryH _).bind fun _ ↦ hOnly_climb _ _ ss

theorem hOnly_openOne (root : Digest) (height width q : ℕ) (o : Opening) :
    HOnly (openOneWithHash callKeccak256 root height width q o) := by
  simp only [openOneWithHash]
  split
  · exact (hOnly_queryH _).bind fun _ ↦ (hOnly_climb _ _ _).bind fun _ ↦ trivial
  · trivial

theorem hOnly_openAll (root : Digest) (height width : ℕ) :
    ∀ (qs : List ℕ) (os : List Opening), HOnly (openAllWithHash callKeccak256 root height width qs os)
  | [], _ => trivial
  | _ :: _, [] => trivial
  | q :: qs, o :: os => by
    simp only [openAllWithHash]
    refine (hOnly_openOne _ _ _ _ _).bind fun b ↦ ?_
    split
    · exact (hOnly_openAll root height width qs os).bind fun _ ↦ trivial
    · trivial

theorem hOnly_openPhase (root : Digest) (height width : ℕ) (ps : List ℕ) (phase : List Opening) :
    HOnly (openPhaseWithHash callKeccak256 root height width ps phase) := by
  unfold openPhaseWithHash
  split
  · exact (hOnly_openAll root height width ps phase).bind fun _ ↦ by split <;> trivial
  · trivial

/-- **The compiled run keeps the discipline**, from a sponge whose state is an earlier answer. -/
theorem duplexP_run {α : Type} (P : VerifierProgram α) :
    ∀ (s : VerifierProgramState) (h : List KeccakState), s.sponge.state ∈ h →
      DuplexP (Compile.runWithHash callKeccak256 callKeccakF1600 P s) h fun _ _ ↦ True := by
  induction P with
  | ret a => intro s h _; trivial
  | fail => intro s h _; trivial
  | read k ih =>
    intro s h hs
    simp only [Compile.runWithHash]
    split
    · trivial
    · exact (duplexP_absorb hs _ _).bind fun sp h' hsp ↦ ih _ _ _ hsp
  | sample k ih =>
    intro s h hs
    simp only [Compile.runWithHash]
    exact (duplexP_squeeze hs).bind fun r h' hr ↦ ih _ _ _ hr
  | grind bits k ih =>
    intro s h hs
    simp only [Compile.runWithHash]
    split
    · trivial
    · refine (duplexP_absorb hs _ _).bind fun sp h' hsp ↦ ?_
      refine (duplexP_squeeze hsp).bind fun r h'' hr ↦ ?_
      split
      · exact ih _ _ hr
      · trivial
  | commit height width k ih =>
    intro s h hs
    simp only [Compile.runWithHash]
    split
    · refine (duplexP_absorb hs _ _).bind fun sp h' hsp ↦ ?_
      refine (duplexP_absorb hsp _ _).bind fun sp' h'' hsp' ↦ ?_
      split
      · exact ih _ _ hsp'
      · trivial
    · trivial
  | query i ps k ih =>
    intro s h hs
    simp only [Compile.runWithHash]
    split
    · refine ((hOnly_openPhase _ _ _ _ _).duplexP h).bind fun r h' hh ↦ ?_
      subst hh
      split
      · exact ih _ _ _ hs
      · trivial
    · trivial

theorem duplexP_runProof (P : VerifierProgram Bool) {seed : KeccakState} {h : List KeccakState} (hs
    : seed ∈ h)
    (π : Proof) : DuplexP (runProofWithHash callKeccak256 callKeccakF1600 P seed π) h fun _ _ ↦ True := by
  simp only [runProofWithHash]
  refine (duplexP_run P _ h hs).bind fun r h' _ ↦ ?_
  split <;> trivial

theorem hOnly_fiatShamirIvWith (bytecode : List K) :
    HOnly (fiatShamirIvWithHash callKeccak256 bytecode) := by
  simp only [fiatShamirIvWithHash]
  exact hOnly_queryH _

/-- The seed's input is zero from lane `8` on. -/
theorem admissibleVm_seedInput (h : List KeccakState) (iv publicInput : Digest) :
    AdmissibleVm h (seedInput iv publicInput) := by
  refine Or.inl fun i hi ↦ ?_
  have h4 : ¬ (i.val < 4) := by omega
  have h8 : ¬ (i.val < 8) := by omega
  simp [seedInput, h4, h8]

theorem duplexP_seedWith (bytecode : List K) (publicInput : Digest) (h : List KeccakState) :
    DuplexP (seedWithHash callKeccak256 callKeccakF1600 bytecode publicInput) h fun seed h' ↦ seed ∈ h' := by
  simp only [seedWithHash]
  refine ((hOnly_fiatShamirIvWith bytecode).duplexP h).bind fun iv h' hh ↦ ?_
  subst hh
  exact (duplexP_queryF_bind _ _ _ _).mpr
    ⟨admissibleVm_seedInput _ _ _, fun y ↦ List.mem_cons_self⟩

/-- **The verifier follows the duplex discipline.** -/
theorem duplexVm_verifier (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    DuplexVm (verifierWithHash callKeccak256 callKeccakF1600 prog input proof) [] := by
  rw [duplexVm_iff_duplexP]
  change DuplexP (verifyWithHash callKeccak256 callKeccakF1600 (bytecodeWords prog) (publicInputDigest input) proof) [] _
  simp only [verifyWithHash]
  exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦ duplexP_runProof _ hs _

/-! ## The honest prover -/

theorem hOnly_arrayMapM {β γ : Type} (f : γ → OracleComp KeccakCalls β) (hf : ∀ c, HOnly (f c))
    (xs : Array γ) : HOnly (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_bind_pure_comp]
  exact (hOnly_mapM f hf _).bind fun _ ↦ trivial

theorem hOnly_parentsM (level : Array Digest) (n : ℕ) : HOnly (parentsWithHash callKeccak256 level n) :=
  hOnly_arrayMapM _ (fun _ ↦ hOnly_queryH _) _

theorem hOnly_levelsM : ∀ (k : ℕ) (level : Array Digest), HOnly (levelsWithHash callKeccak256 k level)
  | 0, _ => trivial
  | k + 1, _ => (hOnly_parentsM _ _).bind fun _ ↦ (hOnly_levelsM k _).bind fun _ ↦ trivial

theorem hOnly_buildTreeM (height : ℕ) (word : Word) : HOnly (buildTreeWithHash callKeccak256 height word) :=
  (hOnly_arrayMapM _ (fun _ ↦ hOnly_queryH _) _).bind fun _ ↦
    (hOnly_levelsM _ _).bind fun _ ↦ trivial

theorem duplexP_powStepM {h : List KeccakState} {sp : Sponge} (hs : sp.state ∈ h) (n : E) :
    DuplexP (powStepM callKeccakF1600 sp n) h fun r h' ↦ r.2.state ∈ h' :=
  (duplexP_absorb hs _ _).bind fun _ _ hsp ↦ duplexP_squeeze hsp

/-- The nonce search keeps the discipline, and the sponge it searches at. -/
theorem duplexP_searchM (bits : ℕ) {h : List KeccakState} {sp : Sponge} (hs : sp.state ∈ h) :
    ∀ (count n : ℕ), DuplexP (searchM callKeccakF1600 bits sp n count) h fun _ h' ↦ sp.state ∈ h'
  | 0, _ => hs
  | count + 1, n => by
    simp only [searchM]
    refine (duplexP_powStepM hs _).grow.bind fun r h' hr ↦ ?_
    split
    · exact hr.2 hs
    · exact duplexP_searchM bits (hr.2 hs) count (n + 1)

theorem duplexP_findNonceM (bits : ℕ) {h : List KeccakState} {sp : Sponge} (hs : sp.state ∈ h)
    (fuel : ℕ) : DuplexP (findNonceM callKeccakF1600 bits sp fuel) h fun _ h' ↦ sp.state ∈ h' := by
  simp only [findNonceM]
  split
  · exact hs
  · exact duplexP_searchM bits hs _ _

/-- **The honest prover keeps the discipline**, from a sponge whose state is an earlier answer. -/
theorem duplexP_proveFromM (S : Strategy) (fuel : ℕ) {α : Type} (P : VerifierProgram α) :
    ∀ (sp : Sponge) (ev : List Ev) (cs : List Tree) (h : List KeccakState), sp.state ∈ h →
      DuplexP (proveFromM callKeccak256 callKeccakF1600 S fuel P sp ev cs) h fun _ _ ↦ True := by
  induction P with
  | ret a => intro sp ev cs h _; trivial
  | fail => intro sp ev cs h _; trivial
  | read k ih =>
    intro sp ev cs h hs
    simp only [proveFromM]
    exact (duplexP_absorb hs _ _).bind fun sp' h' hsp ↦
      (ih _ _ _ _ _ hsp).bind fun _ _ _ ↦ trivial
  | sample k ih =>
    intro sp ev cs h hs
    simp only [proveFromM]
    exact (duplexP_squeeze hs).bind fun r h' hr ↦ ih _ _ _ _ _ hr
  | grind bits k ih =>
    intro sp ev cs h hs
    simp only [proveFromM]
    refine (duplexP_findNonceM bits hs fuel).bind fun r h' hr ↦ ?_
    split
    · trivial
    · exact (duplexP_powStepM hr _).bind fun r' h'' hr' ↦
        (ih _ _ _ _ hr').bind fun _ _ _ ↦ trivial
  | commit height width k ih =>
    intro sp ev cs h hs
    simp only [proveFromM]
    refine ((hOnly_buildTreeM _ _).duplexP h).bind fun tree h' hh ↦ ?_
    subst hh
    exact (duplexP_absorb hs _ _).bind fun sp0 h0 hs0 ↦ (duplexP_absorb hs0 _ _).bind
      fun sp1 h1 hs1 ↦ (ih _ _ _ _ hs1).bind fun _ _ _ ↦ trivial
  | query i ps k ih =>
    intro sp ev cs h hs
    simp only [proveFromM]
    split
    · trivial
    · exact (ih _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial

/-- **The specification's honest prover of any strategy follows the duplex discipline.** -/
theorem duplexVm_romHonestComp (prog : LeanIsaProgram) (input : PublicInput) (S : Strategy)
    (fuel : ℕ) :
    DuplexVm (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S fuel) [] := by
  rw [duplexVm_iff_duplexP]
  simp only [Rom.honestComp, seedRun_leanVmSeed, proveM, bind_assoc]
  exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦
    (duplexP_proveFromM _ _ _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial

end LeanVM.Rpm
