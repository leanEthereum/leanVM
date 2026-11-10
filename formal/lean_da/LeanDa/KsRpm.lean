module

public import LeanDa.WpbBound
public import LeanDa.WithHash
import all Init.Data.String.Defs

@[expose] public section

/-!
# Wagner's knowledge-soundness term, from the argument's knowledge soundness in the
random-permutation model

Benedikt Wagner's knowledge-soundness term (`ksExpH`, averaged over a uniformly random table of
`H`) is his reduction `ksReduction` against the argument: it runs the code-binding adversary in the
simulated world, reads the challenges of its root, and outputs the statement and the adversary's
proof. Read back in the random-permutation model, it is the argument's knowledge-soundness
experiment (`ksExpRpm`) against the adversary that runs the code-binding adversary and computes the
challenges of its root by the deployed duplex over `π` (`ksAdv`): the two differ by the two-oracle
transfer (`Common.keccak256_transfer2`) and the duplex lemma, reversed (`Common.SeedDuplex.duplex_ge`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace LeanDa

/-! ## The commitment hashes only short strings -/

section Congr

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem mapM_bind_congr {γ β δ : Type} (f : γ → m β) (l : List γ) (g g' : List β → m δ)
    (h : ∀ ds : List β, ds.length = l.length → g ds = g' ds) :
    (l.mapM f >>= g) = (l.mapM f >>= g') := by
  induction l generalizing g g' with
  | nil => simpa using h [] rfl
  | cons a l ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    exact bind_congr fun x ↦ ih _ _ fun ds hds ↦ h _ (by simp [hds])

variable {H₁ H₂ : List UInt8 → m Common.DigestBytes} (hH : ∀ a, shortP a → H₁ a = H₂ a)
include hH

theorem upM_congr {f₁ f₂ : ℕ → m Common.DigestBytes} (hf : ∀ i, f₁ i = f₂ i) (i : ℕ) :
    upMWithHash H₁ f₁ i = upMWithHash H₂ f₂ i := by
  simp only [upMWithHash, hf]
  exact bind_congr fun a ↦ bind_congr fun b ↦ hH _ (by simp [shortP, length_pairBytes])

theorem merkleRootM_congr (d : ℕ) : ∀ {f₁ f₂ : ℕ → m Common.DigestBytes}, (∀ i, f₁ i = f₂ i) →
    merkleRootMWithHash H₁ d f₁ = merkleRootMWithHash H₂ d f₂ := by
  induction d with
  | zero => intro f₁ f₂ hf; exact hf 0
  | succ d ih => intro f₁ f₂ hf; exact ih (upM_congr hH hf)

/-- **The commitment over two hashes that agree on short strings.** -/
theorem commitCellsM_congr {r : ℕ} (c : Fin (r * 128) → Cell) :
    commitCellsMWithHash H₁ c = commitCellsMWithHash H₂ c := by
  have hblob : ∀ i, blobRootMWithHash H₁ c i = blobRootMWithHash H₂ c i := fun i ↦
    merkleRootM_congr hH 7 fun j ↦ hH (cellBytes (paddedCell c i j)) (by simp [shortP, length_cellBytes])
  exact merkleRootM_congr hH _ hblob

end Congr

/-! ## The adversary of the knowledge-soundness term -/

/-- Keccak-256 among the adversary's oracles. -/
abbrev keccakA (a : List UInt8) : OracleComp AdvSpec Common.DigestBytes := liftM (AdvSpec.query (.inr (.inl a)))

/-- `π` among the adversary's oracles. -/
abbrev piA (x : KState) : OracleComp AdvSpec KState := liftM (AdvSpec.query (.inr (.inr (.forward x))))

section Chain

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- **The knowledge-soundness adversary of a code-binding adversary**: run it, compute the
duplex's samples of its root over `π` (the deployed challenge component `1`), and output the
statement and its proof. -/
noncomputable def ksAdv : KsAdvB Crs Proof := fun crs ↦ do
  let out ← A ((), crs)
  let z ← membershipChallengeVecM keccakA (lanePerm piA) out.1.1
  pure (((), out.1.1, z), out.1.2)

/-- The same game with the challenges computed by the verifier's direct calls. -/
noncomputable def postK (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :
    OracleComp Rom2 Bool := do
  let z ← membershipChallengeVecM hR pR out.1.1
  ksPost r ps ext crs (((), out.1.1, z), out.1.2)

theorem toOne_chal (root : Common.DigestBytes) :
    simulateQ (toOne (E := KRest) (C := KCap)) (simulateQ (advEmbed (Msg := List UInt8))
        (membershipChallengeVecM keccakA (lanePerm piA) root)) =
      simulateQ (toOne (E := KRest) (C := KCap)) (simulateQ (hfEmbed (Msg := List UInt8))
        (membershipChallengeVecM hR pR root)) := by
  have m1 := membershipChallengeVecM_map
    (fun {α} (x : OracleComp AdvSpec α) ↦ simulateQ (toOne (E := KRest) (C := KCap))
      (simulateQ (advEmbed (Msg := List UInt8)) x)) (fun _ ↦ rfl)
    (fun x f ↦ by simp only [simulateQ_bind]) keccakA (lanePerm piA) root
  have m2 := membershipChallengeVecM_map
    (fun {α} (x : OracleComp Rom2 α) ↦ simulateQ (toOne (E := KRest) (C := KCap))
      (simulateQ (hfEmbed (Msg := List UInt8)) x)) (fun _ ↦ rfl)
    (fun x f ↦ by simp only [simulateQ_bind]) hR pR root
  rw [m1, m2]
  congr 1

theorem ksGame_toOne :
    simulateQ (toOne (E := KRest) (C := KCap)) (ksGame2 r ps ext (ksAdv r A)) =
      simulateQ (toOne (E := KRest) (C := KCap))
        (rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (postK r ps ext)) := by
  unfold ksGame2 rpmGame2
  rw [simulateQ_bind, simulateQ_bind]
  refine bind_congr fun crs ↦ ?_
  simp only [ksAdv, postK, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  refine bind_congr fun out ↦ ?_
  rw [toOne_chal]

/-- **The knowledge-soundness experiment of `ksAdv A`** is the game with the challenges computed by
the verifier's direct calls. -/
theorem ksExpRpm_ksAdv :
    ksExpRpm r ps ext (ksAdv r A) =
      realGame2 keccakPadding KState.zero (rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs))
        (postK r ps ext)) := by
  rw [ksExpRpm, realGame2, realGame2, ksGame_toOne]

end Chain

/-! ## Permutation calls -/

/-- Permutation calls of the verifier's oracles: a hash of `n` bytes `⌊n / 136⌋ + 1`, a direct
call one. -/
def rCalls : Rom2.Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => m.length / 136 + 1
  | .inr (.inr _) => 1

theorem isWeightBound_hfEmbed {α : Type} {X : OracleComp Rom2 α} {N : ℕ}
    (h : QueryCostAtMost X rCalls N) :
    QueryCostAtMost (simulateQ (hfEmbed (Msg := List UInt8) (Dg := DigestBytes) (E := KRest) (C := KCap)) X)
      permCalls2 N :=
  isWeightBound_simulateQ _ rCalls permCalls2 (fun t ↦ by
    rcases t with n | m | x
    · exact isWeightBound_query permCalls2 (.inl n)
    · exact isWeightBound_query permCalls2 (.inr (.inl m))
    · exact isWeightBound_query permCalls2 (.inr (.inr (.inr x)))) h

theorem isWeightBound_advEmbed {α : Type} {X : OracleComp AdvSpec α} {N : ℕ}
    (h : QueryCostAtMost X permCallsB N) :
    QueryCostAtMost (simulateQ (advEmbed (Msg := List UInt8) (Dg := DigestBytes) (E := KRest) (C := KCap)) X)
      permCalls2 N :=
  isWeightBound_simulateQ _ permCallsB permCalls2 (fun t ↦ by
    rcases t with n | m | q
    · exact isWeightBound_query permCalls2 (.inl n)
    · exact isWeightBound_query permCalls2 (.inr (.inl m))
    · exact isWeightBound_query permCalls2 (.inr (.inr (.inl q)))) h

theorem isWeightBound_hEmbed2_setup {Crs : Type} (setup : ProbComp Crs) :
    QueryCostAtMost (simulateQ (hEmbed2 (Msg := List UInt8) (Dg := DigestBytes) (E := KRest) (C := KCap))
      (liftM setup : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Crs)) permCalls2 0 := by
  let w₁ : (unifSpec + roSpec (List UInt8) DigestBytes).Domain → ℕ := fun t ↦ match t with
    | .inl _ => 0
    | .inr m => m.length / 136 + 1
  refine isWeightBound_simulateQ _ w₁ permCalls2 (fun t ↦ ?_)
    (isWeightBound_liftM_probComp w₁ (fun _ ↦ rfl) setup)
  rcases t with n | m
  · exact isWeightBound_query permCalls2 (.inl n)
  · exact isWeightBound_query permCalls2 (.inr (.inl m))

section ChalWeight

variable {ι : Type} {spec : OracleSpec ι} (w : ι → ℕ) (H : List UInt8 → OracleComp spec Common.DigestBytes)
  (P : Lanes → OracleComp spec Lanes) (hH : QueryCostAtMost (H membershipLabel) w 1)
  (hP : ∀ L, QueryCostAtMost (P L) w 1)

include hP in
theorem isWeightBound_branchDrawsM (y : Lanes) : ∀ js : List (Fin nLabels),
    QueryCostAtMost (branchDrawsM P y js) w js.length
  | [] => isWeightBound_pure _ _ _
  | j :: js => by
    unfold branchDrawsM
    exact ((hP _).bind fun _ ↦ (isWeightBound_branchDrawsM y js).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono (by simp; omega)

include hH hP in
/-- **The duplex's draws take `nLabels + 1` calls**: the label's hash, the fresh sponge and one
per nonce. -/
theorem isWeightBound_membershipChallengeVecM (root : Common.DigestBytes) :
    QueryCostAtMost (membershipChallengeVecM H P root) w (nLabels + 1) := by
  unfold membershipChallengeVecM Sponge.newWith
  have hl := Common.SeedDuplex.branchIdx_length (n := nLabels)
  generalize Common.SeedDuplex.branchIdx nLabels = js at hl ⊢
  exact (hH.bind fun _ ↦ ((hP _).bind fun _ ↦ isWeightBound_pure _ _ 0).bind fun _ ↦
    (isWeightBound_branchDrawsM w P hP _ js).bind fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by have h0 : 0 < nLabels := by simp
          rw [hl]; omega)

include hP in
theorem isWeightBound_grindM (y : Lanes) : ∀ fuel nonce,
    QueryCostAtMost (grindMWithHash P y nonce fuel) w fuel
  | 0, _ => isWeightBound_pure _ _ _
  | fuel + 1, nonce => by
    unfold grindMWithHash
    refine ((hP _).bind (b := fuel) fun o ↦ ?_).mono (by omega)
    split
    · exact (isWeightBound_pure _ _ 0).mono (Nat.zero_le _)
    · exact isWeightBound_grindM y fuel (nonce + 1)

include hH hP in
/-- **The nonce search takes at most `nLabels + 1` calls**: the label's hash, the fresh sponge
and one per nonce. -/
theorem isWeightBound_membershipChallengeM (root : Common.DigestBytes) :
    QueryCostAtMost (membershipChallengeMWithHash H P root) w (nLabels + 1) := by
  unfold membershipChallengeMWithHash Sponge.newWith
  exact (hH.bind fun _ ↦ ((hP _).bind fun _ ↦ isWeightBound_pure _ _ 0).bind fun _ ↦
    isWeightBound_grindM w P hP _ _ _).mono (by simp only [nLabels]; omega)

end ChalWeight

theorem label_calls : membershipLabel.length / 136 + 1 = 1 := by decide +kernel

section ChainW

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- The permutation calls of the relation's check: at most `2176` per padded row (`128` cells of
`16` calls and `128` pairs of one). -/
abbrev relCalls (r : ℕ) : ℕ := 2176 * paddedRowCount r

theorem isWeightBound_ksPost (crs : Crs) (out : (Unit × Common.DigestBytes × MembershipChallenge) ×
    Proof) :
    QueryCostAtMost (ksPost r ps ext crs out) rCalls (relCalls r) := by
  unfold ksPost
  have h := isWeightBound_commitCellsM hR rCalls 1 16
    (fun a b ↦ (isWeightBound_query rCalls (.inr (.inl (pairBytes a b)))).mono
      (by simp [rCalls, length_pairBytes]))
    (fun x ↦ (isWeightBound_query rCalls (.inr (.inl (cellBytes x)))).mono
      (by simp [rCalls, length_cellBytes])) (ext crs out.1 out.2)
  exact (h.bind fun _ ↦ isWeightBound_pure _ _ 0).mono (le_of_eq (by ring))

theorem isWeightBound_postK (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :
    QueryCostAtMost (postK r ps ext crs out) rCalls (nLabels + 1 + relCalls r) :=
  (isWeightBound_membershipChallengeVecM rCalls hR pR
    ((isWeightBound_query rCalls (.inr (.inl membershipLabel))).mono
        (by simp [rCalls, label_calls]))
    (fun L ↦ isWeightBound_map _ (isWeightBound_query rCalls (.inr (.inr _)))) _).bind fun _ ↦
      isWeightBound_ksPost r ps ext crs _

theorem isWeightBound_advEmbed_A (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q)
    (x : Crs) (hx : x ∈ support (simulateQ (hEmbed2 (Msg := List UInt8) (Dg := DigestBytes)
      (E := KRest) (C := KCap)) (liftM ps.setup : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Crs))) :
    QueryCostAtMost (simulateQ (advEmbed (Msg := List UInt8) (Dg := DigestBytes) (E := KRest) (C := KCap))
      (A ((), x))) permCalls2 Q :=
  (hQ.of_bind_mem_support hx).of_bind

/-- The permutation calls of the knowledge-soundness game of `ksAdv A`. -/
abbrev ksCalls (r Q : ℕ) : ℕ := Q + (nLabels + 1 + relCalls r)

theorem isWeightBound_postKGame (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    QueryCostAtMost (rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (postK r ps ext)) permCalls2
      (ksCalls r Q) :=
  (IsWeightBound.bind_of_mem_support (isWeightBound_hEmbed2_setup ps.setup) fun x hx ↦
    (isWeightBound_advEmbed_A r ps A Q hQ x hx).bind fun _ ↦
      isWeightBound_hfEmbed (isWeightBound_postK r ps ext x _)).mono (by unfold ksCalls; omega)

theorem isWeightBound_ksGame (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    QueryCostAtMost (ksGame2 r ps ext (ksAdv r A)) permCalls2 (ksCalls r Q) := by
  refine (IsWeightBound.bind_of_mem_support (isWeightBound_hEmbed2_setup ps.setup)
    fun x hx ↦ (?_ : QueryCostAtMost _ permCalls2 (ksCalls r Q))).mono (by omega)
  have e : simulateQ (advEmbed (Msg := List UInt8) (Dg := DigestBytes) (E := KRest) (C := KCap))
      (ksAdv r A x) = simulateQ advEmbed (A ((), x)) >>= fun out ↦
        simulateQ advEmbed (membershipChallengeVecM keccakA (lanePerm piA) out.1.1) >>= fun z ↦
          pure (((), out.1.1, z), out.1.2) := by
    simp only [ksAdv, simulateQ_bind, simulateQ_pure]
  rw [e]
  refine (((isWeightBound_advEmbed_A r ps A Q hQ x hx).bind fun out ↦
    (isWeightBound_advEmbed (isWeightBound_membershipChallengeVecM permCallsB keccakA (lanePerm piA)
      ((isWeightBound_query permCallsB (.inr (.inl membershipLabel))).mono
        (by simp [permCallsB, label_calls]))
      (fun L ↦ isWeightBound_map _ (isWeightBound_query permCallsB (.inr (.inr (.forward _)))))
      _)).bind fun _ ↦ isWeightBound_pure _ _ 0).bind fun a ↦
        isWeightBound_hfEmbed (isWeightBound_ksPost r ps ext x a)).mono (by unfold ksCalls; omega)

end ChainW

/-! ## From the two-oracle model to the simulated world and back to Wagner's -/

section Chain2

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- The knowledge-soundness verdict with `H` among coins and `H`, for the challenges `l`. -/
noncomputable def ksPostH (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening))
    (l : MembershipChallenge) : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Bool := do
  let root ← commitCellsMWithHash hH (ext crs ((), out.1.1, l) out.1.2)
  pure (ps.verify crs ((), out.1.1, l) out.1.2 &&
    !(decide (root = out.1.1) && membershipCheckOpt (selectChal l) (ext crs ((), out.1.1, l) out.1.2)))

theorem ksPost_embH (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening))
    (l : MembershipChallenge) :
    ksPost r ps ext crs (((), out.1.1, l), out.1.2) = simulateQ embH (ksPostH r ps ext crs out l) := by
  rw [ksPostH, simulateQ_bind, commitCellsM_map (fun x ↦ simulateQ embH x) (fun _ ↦ rfl)
    (fun x f ↦ simulateQ_bind _ x f)]
  simp only [simulateQ_embH_hH, simulateQ_pure, ksPost]

theorem postK_eq (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :
    postK r ps ext crs out = chalR out.1.1 >>= fun zs ↦
      simulateQ embH (ksPostH r ps ext crs out (toVec zs)) := by
  rw [postK, membershipChallengeVecM_eq_chalP, bind_map_left]
  exact bind_congr fun zs ↦ ksPost_embH r ps ext crs out _

theorem duplexP_embH {α : Type} (X : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α)
    (hist : List KState) :
    DuplexP (fun _ _ ↦ True) (simulateQ (embH (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) X) hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => exact duplexP_pure trivial
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    rcases t with n | m
    · exact (duplexP_query_bind_other (.inl n) (by simp) _ hist).mpr fun u ↦ ih u hist
    · exact (duplexP_query_bind_other (.inr (.inl m)) (by simp) _ hist).mpr fun u ↦ ih u hist

theorem duplex_postK (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :
    Duplex KState.zero keccakNF (postK r ps ext crs out) [] := by
  rw [postK]
  exact duplex_of_duplexP (Q := fun _ _ ↦ True) <|
    duplexP_bind (duplexP_membershipChallengeVecR _ []) fun zs _ _ ↦ by
      rw [ksPost_embH]; exact duplexP_embH _ _

/-- **From the two-oracle model to the RPM**: the knowledge-soundness game with the simulated
adversary is at most the RPM experiment of `ksAdv A` plus the transfer `q² / 2^508`. -/
theorem rom2_le_ksExpRpm (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    Pr{let b ← romRun2 (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun x ↦
        advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ postK r ps ext x a)}[b = true] ≤
      Pr{let b ← ksExpRpm r ps ext (ksAdv r A)}[b = true] +
        ((ksCalls r Q) ^ 2 : ℝ≥0∞) / 2 ^ 508 := by
  rw [ksExpRpm_ksAdv]
  have hq := isWeightBound_postKGame r ps ext A Q hQ
  rw [permCalls2_eq] at hq
  exact (keccak256_transfer2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (postK r ps ext)
    (fun x a ↦ duplex_postK r ps ext x a) (ksCalls r Q) hq (· = true)).2

/-- **The simulated world of knowledge soundness** for a crs. -/
noncomputable def ksIdealG (crs : Crs) : ProbComp Bool :=
  (simulateQ (GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels).romImpl
    ((simulateQ (simImpl daDuplex hP gaP) (Common.SeedDuplex.hQ (St := KState) daDuplex.label >>= fun _ ↦
        advS2 keccakPadding KState.zero (A ((), crs)))).run' SimSt.init >>= fun out ↦
      readVec (Msg := List UInt8) (Dg := DigestBytes) out.1.1 >>= fun l ↦
        simulateQ embG (ksPostH r ps ext crs out l))).run' ∅

/-! ### The draws and the nonce search agree in the two-oracle model

The verifier's part of Wagner's game reads all the draws of the root and selects the challenge
(`selectChal`); the statement's relation runs the nonce search, which stops at the first valid
draw. Over the random function `F` the two give the same distribution: the search's calls are the
draws' first ones, and the draws past the selected one are never read again
(`run'_bind_const`). -/

/-- An unused computation before another is invisible in the random-oracle model. -/
theorem run'_bind_const {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] {β γ : Type}
    (X : OracleComp (unifSpec + hs) β) (Y : OracleComp (unifSpec + hs) γ) (c : hs.QueryCache) :
    (simulateQ hs.romImpl (X >>= fun _ ↦ Y)).run' c =ᵈ (simulateQ hs.romImpl Y).run' c := by
  have h := run_bind_bind_comm X Y (fun _ r ↦ pure r) c
  simp only [bind_pure] at h
  rw [StateT.run'_eq, StateT.run'_eq]
  refine (h.map Prod.fst).trans ?_
  rw [simulateQ_bind, StateT.run_bind, map_bind, map_eq_bind_pure_comp]
  refine EvalDistEq.bind_right _ fun z ↦ ?_
  rw [simulateQ_bind, StateT.run_bind, map_bind]
  simp only [simulateQ_pure, StateT.run_pure, map_pure, Function.comp_apply]
  exact EvalDistEq.bind_const _ _

theorem run'_bind_eq {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] {β γ : Type}
    (X : OracleComp (unifSpec + hs) β) (f : β → OracleComp (unifSpec + hs) γ) (c : hs.QueryCache) :
    (simulateQ hs.romImpl (X >>= f)).run' c =
      (simulateQ hs.romImpl X).run c >>= fun p ↦ (simulateQ hs.romImpl (f p.1)).run' p.2 := by
  rw [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rfl

/-- **Runs with equal continuations from every cache** agree. -/
theorem run'_bind_congr {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] {β γ : Type}
    (X : OracleComp (unifSpec + hs) β) (f g : β → OracleComp (unifSpec + hs) γ) (c : hs.QueryCache)
    (h : ∀ b c', (simulateQ hs.romImpl (f b)).run' c' =ᵈ (simulateQ hs.romImpl (g b)).run' c') :
    (simulateQ hs.romImpl (X >>= f)).run' c =ᵈ (simulateQ hs.romImpl (X >>= g)).run' c := by
  rw [run'_bind_eq, run'_bind_eq]
  exact EvalDistEq.bind_right _ fun p ↦ h p.1 p.2

/-- The draws of a list of nonces from the seeded answer `y`. -/
def drawsL {m : Type → Type} [Monad m] (P : Lanes → m Lanes) (y : Lanes) (L : List ℕ) :
    m (List Draw) :=
  L.mapM fun n ↦ drawOfState <$> P (nonceInput y n)

/-- The nonce search over a list of nonces from the seeded answer `y`. -/
def grindL {m : Type → Type} [Monad m] (P : Lanes → m Lanes) (y : Lanes) : List ℕ → m (Option E)
  | [] => pure none
  | n :: L => do
    let o ← P (nonceInput y n)
    if powValid o[2] then pure (some (chalOfState o)) else grindL P y L

/-- The selection over a list of draws: the first valid one's challenge. -/
def selectList : List Draw → Option E
  | [] => none
  | d :: ds => if powValid d.2.lane then some d.1 else selectList ds

theorem grindM_eq_grindL {m : Type → Type} [Monad m] (P : Lanes → m Lanes) (y : Lanes) :
    ∀ fuel nonce, grindMWithHash P y nonce fuel = grindL P y (List.range' nonce fuel)
  | 0, _ => rfl
  | fuel + 1, nonce => by
    rw [List.range'_succ, grindMWithHash, grindL, grindM_eq_grindL P y fuel (nonce + 1)]

theorem branchDrawsM_eq_drawsL {m : Type → Type} [Monad m] [LawfulMonad m] (P : Lanes → m Lanes)
    (y : Lanes) : ∀ js : List (Fin nLabels),
      branchDrawsM P y js = drawsL P y (js.map fun j ↦ j.val - 1)
  | [] => rfl
  | j :: js => by
    rw [branchDrawsM, List.map_cons, drawsL, List.mapM_cons, ← drawsL,
      ← branchDrawsM_eq_drawsL P y js]
    simp only [bind_map_left]

theorem branchIdx_map (n : ℕ) :
    (Common.SeedDuplex.branchIdx (n + 1)).map (fun j : Fin (n + 1) ↦ j.val - 1) = List.range' 0 n := by
  refine List.ext_getElem (by simp [Common.SeedDuplex.branchIdx_length]) fun i h1 h2 ↦ ?_
  rw [List.getElem_map, Common.SeedDuplex.branchIdx_getElem, List.getElem_range']
  simp

theorem membershipChallengeVecM_eq_drawsL {m : Type → Type} [Monad m] [LawfulMonad m]
    (H : List UInt8 → m Common.DigestBytes) (P : Lanes → m Lanes) (root : Common.DigestBytes) :
    membershipChallengeVecM H P root = (do
      let iv ← H membershipLabel
      let s ← Sponge.newWith P iv root
      let zs ← drawsL P s.state (List.range' 0 nonceCount)
      pure (drawsVec (drawOfState s.state :: zs))) := by
  unfold membershipChallengeVecM
  simp only [branchDrawsM_eq_drawsL, branchIdx_map]

theorem membershipChallengeM_eq_grindL {m : Type → Type} [Monad m]
    (H : List UInt8 → m Common.DigestBytes) (P : Lanes → m Lanes) (root : Common.DigestBytes) :
    membershipChallengeMWithHash H P root = (do
      let iv ← H membershipLabel
      let s ← Sponge.newWith P iv root
      grindL P s.state (List.range' 0 nonceCount)) := by
  unfold membershipChallengeMWithHash
  simp only [grindM_eq_grindL]

/-- **The deployed challenge of the draws is the selection over the nonces'.** -/
theorem selectChal_drawsVec (d0 : Draw) (zs : List Draw) (hz : zs.length = nonceCount) :
    selectChal (drawsVec (d0 :: zs)) = selectList zs := by
  have key : ∀ fuel nonce, nonce + fuel = zs.length →
      selectFrom (drawsVec (d0 :: zs)) nonce fuel = selectList (zs.drop nonce) := by
    intro fuel
    induction fuel with
    | zero =>
      intro nonce h
      rw [List.drop_of_length_le (by omega)]
      rfl
    | succ fuel ih =>
      intro nonce h
      have hn : nonce < zs.length := by omega
      have hd : drawAt (drawsVec (d0 :: zs)) (nonce + 1) = zs[nonce] := by
        have hl : nonce + 1 < nLabels := by simp only [nLabels]; omega
        simp only [drawAt, hl, ↓reduceDIte, drawsVec]
        rw [List.getD_eq_getElem _ _ (by simp; omega)]
        simp
      rw [selectFrom, hd, List.drop_eq_getElem_cons hn, selectList, ih (nonce + 1) (by omega)]
  exact key nonceCount 0 (by omega)

/-- **The draws then their selection, or the nonce search**, over the random function `F`. -/
theorem run'_drawsL_select {β : Type} (y : Lanes) (K : Option E → OracleComp Rom2 β) :
    ∀ (L : List ℕ) (c : Cache2),
      (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
          (drawsL pR y L >>= fun zs ↦ K (selectList zs))).run' c =ᵈ
        (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl (grindL pR y L >>= K)).run' c
  | [], c => by simp [drawsL, grindL, selectList]
  | n :: L, c => by
    rw [drawsL, List.mapM_cons, ← drawsL]
    simp only [grindL, bind_assoc, bind_map_left, pure_bind]
    refine run'_bind_congr _ _ _ c fun o c' ↦ ?_
    have hv : (drawOfState o).2.lane = o[2] := rfl
    simp only [selectList, hv]
    split
    · exact run'_bind_const _ _ c'
    · exact run'_drawsL_select y K L c'

/-- The knowledge-soundness verdict on the challenge `z`, the statement's draws `default`. -/
noncomputable def ksPostG (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) (z : Option E) :
    OracleComp Rom2 Bool := do
  let root ← commitCellsMWithHash hR (ext crs ((), out.1.1, default) out.1.2)
  pure (ps.verify crs ((), out.1.1, default) out.1.2 &&
    !(decide (root = out.1.1) && membershipCheckOpt z (ext crs ((), out.1.1, default) out.1.2)))

/-- The same with `H` among coins and `H`. -/
noncomputable def ksPostHG (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) (z : Option E) :
    OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Bool := do
  let root ← commitCellsMWithHash hH (ext crs ((), out.1.1, default) out.1.2)
  pure (ps.verify crs ((), out.1.1, default) out.1.2 &&
    !(decide (root = out.1.1) && membershipCheckOpt z (ext crs ((), out.1.1, default) out.1.2)))

theorem ksPostG_embH (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) (z : Option E) :
    ksPostG r ps ext crs out z = simulateQ embH (ksPostHG r ps ext crs out z) := by
  rw [ksPostHG, simulateQ_bind, commitCellsM_map (fun x ↦ simulateQ embH x) (fun _ ↦ rfl)
    (fun x f ↦ simulateQ_bind _ x f)]
  simp only [simulateQ_embH_hH, simulateQ_pure, ksPostG]

theorem isWeightBound_ksPostG (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) (z : Option E) :
    QueryCostAtMost (ksPostG r ps ext crs out z) rCalls (relCalls r) := by
  unfold ksPostG
  have h := isWeightBound_commitCellsM hR rCalls 1 16
    (fun a b ↦ (isWeightBound_query rCalls (.inr (.inl (pairBytes a b)))).mono
      (by simp [rCalls, length_pairBytes]))
    (fun x ↦ (isWeightBound_query rCalls (.inr (.inl (cellBytes x)))).mono
      (by simp [rCalls, length_cellBytes])) (ext crs ((), out.1.1, default) out.1.2)
  exact (h.bind fun _ ↦ isWeightBound_pure _ _ 0).mono (le_of_eq (by ring))

/-- **The knowledge-soundness game with the deployed challenge**, by the nonce search over the
verifier's direct calls. -/
noncomputable def postKG (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :
    OracleComp Rom2 Bool :=
  membershipChallengeMWithHash hR pR out.1.1 >>= ksPostG r ps ext crs out

/-- **Wagner's verdict and the deployed one agree** for an argument and an extractor that ignore
the statement's draws. -/
theorem run'_postK_eq_postKG
    (hver : ∀ crs root l proof, ps.verify crs ((), root, l) proof = ps.verify crs ((), root, default) proof)
    (hext : ∀ crs root l proof, ext crs ((), root, l) proof = ext crs ((), root, default) proof)
    (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening))
    (c : Cache2) :
    (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl (postK r ps ext crs out)).run' c =ᵈ
      (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl (postKG r ps ext crs out)).run' c := by
  have hpost : ∀ l, ksPost r ps ext crs (((), out.1.1, l), out.1.2) =
      ksPostG r ps ext crs out (selectChal l) := fun l ↦ by
    simp only [ksPost, ksPostG, hver crs out.1.1 l, hext crs out.1.1 l]
  have e1 : postK r ps ext crs out = hR membershipLabel >>= fun iv ↦
      Sponge.newWith pR iv out.1.1 >>= fun s ↦
        drawsL pR s.state (List.range' 0 nonceCount) >>= fun zs ↦
          ksPostG r ps ext crs out (selectList zs) := by
    rw [postK, membershipChallengeVecM_eq_drawsL]
    simp only [bind_assoc, pure_bind, hpost]
    refine bind_congr fun iv ↦ bind_congr fun s ↦ ?_
    rw [drawsL]
    exact mapM_bind_congr _ _ _ _ fun zs hzs ↦ by
      rw [selectChal_drawsVec _ zs (by simpa using hzs)]
  have e2 : postKG r ps ext crs out = hR membershipLabel >>= fun iv ↦
      Sponge.newWith pR iv out.1.1 >>= fun s ↦
        grindL pR s.state (List.range' 0 nonceCount) >>= ksPostG r ps ext crs out := by
    rw [postKG, membershipChallengeM_eq_grindL]
    simp only [bind_assoc]
  rw [e1, e2]
  exact run'_bind_congr (hR membershipLabel) _ _ c fun iv c₁ ↦
    run'_bind_congr (Sponge.newWith pR iv out.1.1) _ _ c₁ fun s c₂ ↦
      run'_drawsL_select s.state _ _ c₂

theorem duplex_postKG (crs : Crs) (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :
    Duplex KState.zero keccakNF (postKG r ps ext crs out) [] :=
  duplex_of_duplexP (Q := fun _ _ ↦ True) <|
    duplexP_bind (duplexP_membershipChallengeR _ []) fun z _ _ ↦ by
      rw [ksPostG_embH]; exact duplexP_embH _ _

/-- **The duplex lemma, reversed, for knowledge soundness.** -/
theorem ksIdealG_le (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    Pr{let b ← ps.setup >>= ksIdealG r ps ext A}[b = true] ≤
      Pr{let b ← romRun2 (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun x ↦
        advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ postK r ps ext x a)}[b = true] +
        ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 ^ 576 : ℝ≥0∞)⁻¹) := by
  have hsplit : Pr{let b ← romRun2 (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>=
        fun x ↦ advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ postK r ps ext x a)}[
          b = true] =
      Pr{let b ← ps.setup >>= fun crs ↦ romRun2 (advS2 keccakPadding KState.zero (A ((), crs)) >>=
        fun out ↦ postK r ps ext crs out)}[b = true] := by
    rw [romRun2, simulateQ_liftM_of_coins _ (fun _ ↦ rfl), simulateQ_bind,
      StateT.run'_eq, StateT.run_bind, simulateQ_romImpl_liftM_run, bind_map_left, map_bind]
    rfl
  rw [hsplit]
  refine prEvent_bind_le_add_const_of_support _ _ _ _ _ _ fun crs hcrs ↦ ?_
  have hB := isWeightBound_advS2 r ps A Q hQ crs hcrs
  have e : romRun2 (advS2 keccakPadding KState.zero (A ((), crs)) >>= fun out ↦ postK r ps ext crs out) =
      (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
        (advS2 keccakPadding KState.zero (A ((), crs)) >>= fun out ↦ chalR out.1.1 >>= fun zs ↦
          simulateQ embH (ksPostH r ps ext crs out (toVec zs)))).run' ∅ := by
    rw [romRun2]
    simp only [postK_eq]
  rw [e]
  exact duplex_ge (D := daDuplex) daDuplex_cap _ Q hB (fun out ↦ out.1.1)
    (fun out l ↦ ksPostH r ps ext crs out l)

theorem isWeightBound_postKG (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) :
    QueryCostAtMost (postKG r ps ext crs out) rCalls (nLabels + 1 + relCalls r) :=
  (isWeightBound_membershipChallengeM rCalls hR pR
    ((isWeightBound_query rCalls (.inr (.inl membershipLabel))).mono
        (by simp [rCalls, label_calls]))
    (fun L ↦ isWeightBound_map _ (isWeightBound_query rCalls (.inr (.inr _)))) _).bind fun z ↦
      isWeightBound_ksPostG r ps ext crs out z

theorem isWeightBound_postKGGame (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    QueryCostAtMost (rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (postKG r ps ext)) permCalls2
      (ksCalls r Q) :=
  (IsWeightBound.bind_of_mem_support (isWeightBound_hEmbed2_setup ps.setup) fun x hx ↦
    (isWeightBound_advEmbed_A r ps A Q hQ x hx).bind fun _ ↦
      isWeightBound_hfEmbed (isWeightBound_postKG r ps ext x _)).mono (by unfold ksCalls; omega)

/-- **From the two-oracle model to the RPM, with the deployed challenge**: the transfer
`q² / 2^508`. -/
theorem rom2G_le_rpm (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    Pr{let b ← romRun2 (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun x ↦
        advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ postKG r ps ext x a)}[b = true] ≤
      Pr{let b ← realGame2 keccakPadding KState.zero
          (rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (postKG r ps ext))}[b = true] +
        ((ksCalls r Q) ^ 2 : ℝ≥0∞) / 2 ^ 508 := by
  have hq := isWeightBound_postKGGame r ps ext A Q hQ
  rw [permCalls2_eq] at hq
  exact (keccak256_transfer2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (postKG r ps ext)
    (fun x a ↦ duplex_postKG r ps ext x a) (ksCalls r Q) hq (· = true)).2

/-- **The simulated world of knowledge soundness is at most the RPM game with the deployed
challenge**, for an argument and an extractor that ignore the statement's draws: the duplex
lemma reversed, the draws read as the nonce search reads them, and the transfer. -/
theorem ksIdealG_le_rpmG
    (hver : ∀ crs root l proof, ps.verify crs ((), root, l) proof = ps.verify crs ((), root, default) proof)
    (hext : ∀ crs root l proof, ext crs ((), root, l) proof = ext crs ((), root, default) proof)
    (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    Pr{let b ← ps.setup >>= ksIdealG r ps ext A}[b = true] ≤
      Pr{let b ← realGame2 keccakPadding KState.zero
          (rpmGame2 (liftM ps.setup) (fun crs ↦ A ((), crs)) (postKG r ps ext))}[b = true] +
        ((ksCalls r Q) ^ 2 : ℝ≥0∞) / 2 ^ 508 +
        ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 ^ 576 : ℝ≥0∞)⁻¹) := by
  have heq : Pr{let b ← romRun2 (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun x ↦
        advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ postK r ps ext x a)}[b = true] =
      Pr{let b ← romRun2 (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun x ↦
        advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ postKG r ps ext x a)}[b = true] := by
    rw [romRun2, romRun2]
    exact (run'_bind_congr _ _ _ ∅ fun x c₁ ↦ run'_bind_congr _ _ _ c₁ fun a c₂ ↦
      run'_postK_eq_postKG r ps ext hver hext x a c₂).prEvent_eq _
  refine (ksIdealG_le r ps ext A Q hQ).trans ?_
  rw [heq]
  refine add_le_add (rom2G_le_rpm r ps ext A Q hQ) le_rfl


end Chain2

/-! ## The simulated world is the average of Wagner's knowledge-soundness experiments -/

section Chain3

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- The knowledge-soundness verdict with the hash of the table `h`. -/
noncomputable def ksP (h : HTab) (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) (l : MembershipChallenge) : Bool :=
  ps.verify crs ((), out.1.1, l) out.1.2 &&
    !(decide (commitCellsWithHash (Hh h) (ext crs ((), out.1.1, l) out.1.2) = out.1.1) &&
      membershipCheckOpt (selectChal l) (ext crs ((), out.1.1, l) out.1.2))

theorem run_ksPostH_phiG (h : HTab) (crs : Crs)
    (out : (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) (l : MembershipChallenge) (s : HCache) :
    (simulateQ (phiG h) (simulateQ embG (ksPostH r ps ext crs out l))).run s =
      pure (ksP r ps ext h crs out l, s) := by
  rw [← QueryImpl.simulateQ_compose]
  have hp : ∀ {α} (a : α), simulateQ (phiG h ∘ₛ embG) (pure a :
      OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α) = pure a :=
    fun a ↦ simulateQ_pure _ a
  have hb : ∀ {α β} (x : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α)
      (f : α → OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) β),
      simulateQ (phiG h ∘ₛ embG) (x >>= f) =
        simulateQ (phiG h ∘ₛ embG) x >>= fun a ↦ simulateQ (phiG h ∘ₛ embG) (f a) :=
    fun x f ↦ simulateQ_bind _ x f
  have hHs : ∀ a, shortP a → simulateQ (phiG h ∘ₛ embG) (LeanDa.hH a) =
      (pure (Hh h a) : StateT HCache (OracleComp WSpec) Common.DigestBytes) := by
    intro a ha
    rw [LeanDa.hH, simulateQ_spec_query, QueryImpl.apply_compose]
    simp only [embG]
    rw [hP, simulateQ_spec_query]
    ext s
    rw [phiG_H_run h a ha]
    rfl
  rw [ksPostH, hb, commitCellsM_map (fun x ↦ simulateQ (phiG h ∘ₛ embG) x) hp hb,
    commitCellsM_congr hHs,
    commitCellsM_eval (fun x ↦ x) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun a ↦ pure (Hh h a)) (Hh h)
      (fun _ ↦ rfl), pure_bind, hp]
  rfl

/-- **The simulated world of knowledge soundness is, for each table of `H`, Wagner's.** -/
theorem ksIdealG_evalDistEq {crs : Crs} (hcrs : crs ∈ support ps.setup) :
    ksIdealG r ps ext A crs =ᵈ ($ᵗ HTab >>= fun h ↦
      (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (advH r ps A h ((), crs) >>=
          fun out ↦
        ksP r ps ext h crs out <$> readVecW out.1.1)).run' ∅) := by
  rw [ksIdealG]
  refine (run'_romImpl_evalDistEq_vec _).trans ?_
  refine (run'_romImpl_evalDistEq_swap _ _).trans ?_
  rw [swapCache_empty]
  refine (run'_romImpl_evalDistEq_eager shortP _ ∅).trans ?_
  refine EvalDistEq.bind_right _ fun h ↦ (run'_eagerImpl_tImpl h _).trans ?_
  rw [simulateQ_phiG]
  have e : (simulateQ (phiG h) ((simulateQ (simImpl daDuplex hP gaP)
      (Common.SeedDuplex.hQ (St := KState) daDuplex.label >>= fun _ ↦
        advS2 keccakPadding KState.zero (A ((), crs)))).run' SimSt.init >>= fun out ↦
          readVec (Msg := List UInt8) (Dg := DigestBytes) out.1.1 >>= fun l ↦
            simulateQ embG (ksPostH r ps ext crs out l))).run' ∅ =
        advH r ps A h ((), crs) >>= fun out ↦ ksP r ps ext h crs out <$> readVecW out.1.1 := by
    rw [advH, fixCrs_of_mem r ps hcrs, ← advSim, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, StateT.run'_eq, map_bind, bind_map_left]
    refine bind_congr fun z ↦ ?_
    rw [simulateQ_bind, StateT.run_bind, run_readVec_phiG, bind_map_left]
    simp only [run_ksPostH_phiG, map_pure, map_bind]
    rw [map_eq_bind_pure_comp]
    rfl
  rw [e]

theorem run'_readVecW (f : MembershipChallenge → Bool) (d : Common.DigestBytes) (c : WCache) :
    (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (f <$> readVecW d)).run' c =ᵈ
      (fun w ↦ f w.1) <$> roStep d c := by
  have hfin : List.finRange nLabels = (0 : Fin nLabels) :: (List.finRange nonceCount).map Fin.succ :=
    List.finRange_succ
  rw [readVecW, Functor.map_map, StateT.run'_eq, simulateQ_map, StateT.run_map, hfin,
    Functor.map_map]
  refine ((run_mapM_wQ d (fun j v ↦ v j) 0 _ c).map _).trans ?_
  rw [Functor.map_map]
  have hv : ∀ v : MembershipChallenge, (fun j : Fin nLabels ↦
      (List.map (fun b ↦ v b) (0 :: List.map Fin.succ (List.finRange nonceCount))).getD j default) =
        v := by
    intro v
    rw [← hfin]
    funext j
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_finRange]; omega), List.getElem_map, List.getElem_finRange]
    rfl
  simp only [hv]
  exact EvalDistEq.rfl

/-- **Wagner's knowledge-soundness experiment for the table `h`**, unfolded. -/
theorem ksExpH_eq (h : HTab) :
    ksExpH r ps ext A h = ps.setup >>= fun crs ↦
      (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (advH r ps A h ((), crs) >>=
          fun out ↦
        ksP r ps ext h crs out <$> wQ out.1.1)).run' ∅ := by
  simp only [ksExpH, Nark.knowledgeSoundnessExp, ksReduction, argH, merkleVC, simulateRom,
    simulateRomWithCache, runWithChallenge, bind_assoc, pure_bind]
  refine bind_congr fun crs ↦ ?_
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    bind_assoc, pure_bind, map_eq_bind_pure_comp]
  rfl

/-- **The average of Wagner's knowledge-soundness term is the simulated world's.** -/
theorem prT_ksExpH :
    Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= ksExpH r ps ext A}[b = true] =
      Pr{let b ← ps.setup >>= ksIdealG r ps ext A}[b = true] := by
  rw [show ksExpH r ps ext A = fun h ↦ ps.setup >>= fun crs ↦
      (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (advH r ps A h ((), crs) >>=
          fun out ↦
        ksP r ps ext h crs out <$> wQ out.1.1)).run' ∅ from funext (ksExpH_eq r ps ext A)]
  rw [(EvalDistEq.bind_bind_swap _ _ _).prEvent_eq]
  refine prEvent_bind_congr_of_support _ _ _ _ fun crs hcrs ↦ ?_
  rw [((ksIdealG_evalDistEq r ps ext A hcrs).prEvent_eq _)]
  refine Common.prEvent_bind_congr _ _ _ _ _ fun h ↦ ?_
  have e : ∀ K : ((Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) → OracleComp WSpec Bool,
      (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (advH r ps A h ((), crs) >>= K)).run' ∅ =
        (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (advH r ps A h ((), crs))).run ∅ >>= fun z ↦
          (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (K z.1)).run' z.2 := by
    intro K
    simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
  rw [e, e]
  refine Common.prEvent_bind_congr _ _ _ _ _ fun z ↦ ?_
  rw [(run'_readVecW _ _ _).prEvent_eq, StateT.run'_eq, simulateQ_map, StateT.run_map, run_wQ,
    Functor.map_map, prEvent_map, prEvent_map]

end Chain3

end LeanDa
