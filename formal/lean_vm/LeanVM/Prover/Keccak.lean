/-
  LeanVM.Prover.Keccak

  The executable Keccak phase makes the moves of the specification's `hKeccakPhase`.
-/

module

public import LeanVM.Prover.Keccak.Reduction
public import LeanVM.Protocol.EndToEnd.Complete.KeccakPhase

/-!
# The Keccak phase

`corr_keccakPhase`: given the instance's columns as arrays indexed by the verifier's column
numbers (`cols`, the witness's), and claims whose output lanes are the `KECCAK` table's
evaluations' (`evaluations`), at a point of its `τ` coordinates, the executable phase
`keccakPhaseProve (s.τ 5) cols evaluations` makes the moves of `hKeccakPhase prog s q claims`.
`q_keccak`'s column of `cols` agrees with the honest stack's `q_keccak` words (`qkH`) on its
`2^(τ + 6)` words (`colAgree_qk`).

The modules: `Keccak/Tables` (loops, equality tables, folded tables, coefficient lists, bits),
`Keccak/States` (the masks are the bits entering χ), `Keccak/Product` (`G`'s coefficients),
`Keccak/Rounds` (the bounded stateful sumcheck, the openings' products), `Keccak/Pack`,
`Keccak/Position`, `Keccak/Layer`, `Keccak/Open`, `Keccak/Reduction`.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

variable (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))

theorem tau_sub_add : s.τ 5 - 4 + 4 = s.τ 5 := by
  have := s.minSteps_le
  simp only [keccakMinStepsLog] at this
  omega

/-- **`q_keccak`'s column of the witness's arrays is the honest stack's `q_keccak`**, on its
words. -/
theorem colAgree_qk (cols : Array (Array K))
    (hcols : ∀ c : Col, cols.getD (refCol c) #[] = ((inst prog s).column q c).values.toArray) :
    ColAgree (s.τ 5 - 4) (fun n ↦ (cols.getD qkeccak #[]).getD n 0) (qkH prog s q) := by
  intro n hn
  have hn' : n < 2 ^ (s.τ 5 + 6) := by
    have e : s.τ 5 - 4 + 10 = s.τ 5 + 6 := by have := tau_sub_add s; omega
    rwa [e] at hn
  have h := keccakCol_getD prog s (fromI prog s q) hn'
  rw [toI_fromI, qkOf_fromI] at h
  rw [← h, ← refCol_keccakCol, hcols keccakCol]
  rfl

/-- **The executable Keccak phase makes the moves of `hKeccakPhase`**, on claims whose output
lanes are the `KECCAK` table's evaluations'. -/
theorem corr_keccakPhase (cols : Array (Array K))
    (hcols : ∀ c : Col, cols.getD (refCol c) #[] = ((inst prog s).column q c).values.toArray)
    (claims : List ColumnClaim) (evaluations : List (List E × List E))
    (hl : lanesOf claims = Claims.laneClaims (evaluations.getD opKeccak ([], [])))
    (hlen : (evaluations.getD opKeccak ([], [])).1.length = s.τ 5) :
    Corr (fun _ _ ↦ True) (keccakPhaseProve (s.τ 5) cols evaluations)
      (hKeccakPhase prog s q claims) := by
  unfold keccakPhaseProve hKeccakPhase
  dsimp only
  have hpt : ((Claims.laneClaims (evaluations.getD opKeccak ([], []))).headD default).point =
      (evaluations.getD opKeccak ([], [])).1 := rfl
  have hval : (Claims.laneClaims (evaluations.getD opKeccak ([], []))).map (·.value) =
      (List.range 25).map fun lane ↦ (evaluations.getD opKeccak ([], [])).2.getD (keccakOut + lane) 0 := by
    simp only [Claims.laneClaims, List.map_map]
    rfl
  rw [Script.ret_bind, hl, hpt, hval, ← Script.bind_ret (keccakProve _ _ _ _)]
  exact Corr.bind (fun _ _ _ ↦ trivial) _ _ (corr_keccak (colAgree_qk prog s q cols hcols)
    (by rw [hlen, tau_sub_add]) _)

end
end LeanVM.Prover.KeccakGkr
