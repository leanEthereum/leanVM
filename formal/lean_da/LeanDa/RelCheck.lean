module

public import LeanDa.SimWorld
public import LeanDa.WithHash
import all Init.Data.String.Defs

@[expose] public section

/-!
# The relation's check: its calls, and its nonce search read off the root's draws

The membership game's check (`relationWith`) commits to the matrix and runs the nonce search. Its
hash and permutation calls are bounded (`relCalls`, `ksCalls` and the `isWeightBound_` lemmas), and
the nonce search over the duplex is the selection of the first valid draw among all the root's
draws (`grindM_eq_grindL`, `membershipChallengeM_eq_grindL`, `run'_drawsL_select`), the form the
straight-line argument reads (`LeanDa.Straight`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP)
open scoped ENNReal

namespace LeanDa

/-- The hash calls of the commitment over `H` as queries (at most). -/
abbrev commitCalls (_r : ℕ) : ℕ := 256 * maxRows

attribute [local irreducible] logMaxRows

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

end Congr

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
  (A : CodeBindingAdvB r Crs Proof)

/-- The permutation calls of the relation's check: at most `2176` per padded row (`128` cells of
`16` calls and `128` pairs of one). -/
abbrev relCalls (_r : ℕ) : ℕ := 2176 * maxRows

theorem isWeightBound_advEmbed_A (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q)
    (x : Crs) (hx : x ∈ support (simulateQ (hEmbed2 (Msg := List UInt8) (Dg := DigestBytes)
      (E := KRest) (C := KCap)) (liftM ps.setup : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Crs))) :
    QueryCostAtMost (simulateQ (advEmbed (Msg := List UInt8) (Dg := DigestBytes) (E := KRest) (C := KCap))
      (A ((), x))) permCalls2 Q :=
  (hQ.of_bind_mem_support hx).of_bind

/-- The permutation calls of the membership game: the adversary's, the challenge's and the relation's check. -/
abbrev ksCalls (r Q : ℕ) : ℕ := Q + (nLabels + 1 + relCalls r)

end ChainW

/-! ## The nonce search as a selection over the root's draws -/

section Chain2

variable (r : ℕ) {Crs Proof : Type}
  (A : CodeBindingAdvB r Crs Proof)

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

end Chain2

end LeanDa
