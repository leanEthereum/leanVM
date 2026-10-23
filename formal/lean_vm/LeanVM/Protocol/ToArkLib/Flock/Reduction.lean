/-
  LeanVM.Protocol.ToArkLib.Flock.Reduction

  The Flock argument for a batch of Boolean R1CS blocks as one component: the zerocheck with a
  univariate skip, the lincheck and ring switching in sequence, its witness that the verifier
  never reads the oracles, and its completeness. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Flock.RingSwitch

/-!
# The Flock argument

`flock` composes, in this order (Annex C, Protocol C.1, and Annex A): the `nRand` drawn
coordinates of the zerocheck point; `P` on the coset of the skip domain; `z_skip`; the `m`
zerocheck rounds on the within-block coordinates and the `κ` on the batch coordinates; `â, b̂`;
`α`; the `m` lincheck rounds; the slices `s`, checked against the native terminal; the `s' + 1`
ring-switching coefficients and the weighted claim. Its slot is `flockSlot`. It is a typed
front component, so its verifier reads the statement and the path alone, and an honest prover
with a batch that satisfies its R1CS makes it accept a true weighted claim (`flockComplete`).

Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval OracleComp OracleSpec SumcheckRound BlockR1CS

@[expose] public section

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] (P : Params F)
  {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type}
  (C : BlockR1CS F (P.s + P.m))
  (z : (∀ i, O i) → Fin (2 ^ P.s) → CMlPolynomialEval F (P.m + P.κ))
  {S : Type} (side : S → (∀ i, O i) → Prop) (s' : ℕ)
  {K : Type} [CommRing K] (φ : K →+* F) (g : K) {μ : ℕ}
  (lift : Vector F (P.m + P.κ) → Vector F μ) {StmtOut : Type}
  (finish : S → Weight F μ → F → StmtOut)

/-- The typed slot of a Flock argument. -/
abbrev flockSlot (F : Type) [SampleableType F] (s m κ nRand s' : ℕ) : Typed.Slot :=
  (((((((((Typed.drawsSlot F nRand).append (Typed.saySlot (Vector F (2 ^ s)))).append
    (Typed.drawSlot F)).append (Typed.roundsSlot F 2 m)).append (Typed.roundsSlot F 2 κ)).append
    (Typed.saySlot (Vector F 2))).append (Typed.drawSlot F)).append (Typed.roundsSlot F 2 m)).append
    (Typed.saySlot (Vector F (2 ^ s)))).append (Typed.drawsSlot F (s' + 1))

/-- The Flock argument as one typed component. -/
def flock : Typed.Def O S W StmtOut W (flockSlot F P.s P.m P.κ P.nRand s') :=
  (pointDraws P.nRand).append (skipMsg P C z) |>.append (skipDraw P) |>.append
    (zcRoundsLow P C z side) |>.append (zcRoundsHigh P C z side) |>.append (zcEnd P C z) |>.append
    (alphaDraw P) |>.append (linRounds P C z side) |>.append (linEnd P C z) |>.append
    (ringSwitch P s' φ g lift finish)

variable [CharP F 2] (col : (∀ i, O i) → CMlPolynomialEval K (P.m + P.κ))
  (stack : (∀ i, O i) → CMlPolynomialEval K μ)

omit [∀ i, OracleInterface (O i)] in
/-- **Completeness of the Flock argument on the typed framework.** -/
theorem flockComplete
    (hnodes : Function.Injective fun j : Fin (2 ^ P.s + 2 ^ P.s) ↦ P.nodes.pts[j])
    (relIn : Set ((S × ∀ i, O i) × W)) (relOut : Set ((StmtOut × ∀ i, O i) × W))
    (hIn : ∀ s o w, ((s, o), w) ∈ relIn → side s o ∧ BatchHolds C P.cpos (z o))
    (hout : ∀ sIn o w (Wt : Weight F μ) T, side sIn o → Wt.pair φ (stack o) = T →
      ((finish sIn Wt T, o), w) ∈ relOut)
    (hcell : ∀ o (u : Fin (2 ^ (P.m + P.κ))),
      φ (col o)[u] = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * (z o i)[u])
    (hbool : ∀ o i (u : Fin (2 ^ (P.m + P.κ))), (z o i)[u] = 0 ∨ (z o i)[u] = 1)
    (hread : ∀ o p, eval₂Mle (col o) φ p = eval₂Mle (stack o) φ (lift p)) :
    Typed.Complete (flock P C z side s' φ g lift finish (W := W)) relIn relOut :=
  (pointDrawsComplete P C z side relIn (fun s o w h ↦ by
      obtain ⟨hside, hholds⟩ := hIn s o w h
      obtain ⟨herr, hconst⟩ := (batchHolds_iff C P.cpos (z o)).mp hholds
      refine ⟨hside, fun i b ↦ ?_, hconst⟩
      rw [evalMle_eq_sum]
      exact Finset.sum_eq_zero fun u _ ↦ by rw [herr i u, zero_mul])
    P.nRand).append (skipMsgComplete P C z side) |>.append
    (skipDrawComplete P C z side hnodes) |>.append (zcRoundsLowComplete P C z side) |>.append
    (zcRoundsHighComplete P C z side) |>.append (zcEndComplete P C z side) |>.append
    (alphaDrawComplete P C z side) |>.append (linRoundsComplete P C z side) |>.append
    (linEndComplete P C z side) |>.append
    (ringSwitchComplete P z side s' φ g lift col stack finish relOut hout hcell hbool hread)

end

end Flock

end LeanVM.Protocol
