/-
  LeanVM.Protocol.Whir.Sound.LevelFinal

  The specification of the final WHIR level: the fold rounds, the folded lane in the clear, the
  query group after its grind (positions, openings, the check of each row against the lane), the
  tail sumcheck and the terminal check.
-/

module

public import LeanVM.Protocol.Whir.Sound.LevelMid
public import LeanVM.Protocol.Whir.Sound.Tail

/-!
# The final level

`whirLevels` on `[level]` (`crates/verifier/src/whir.rs:273-301`): the level's fold rounds, then
`finalTail`: the folded lane's `2^μ + ℓ` coefficients, a `17`-bit grind, the positions, their
rows and the check that each row folds to the lane's value at its point (one group, `eQuery`),
the tail sumcheck on the lane's low part (`tailSpec`), and the terminal check, which fails.

The query group's doom is `TailInv` with no tail challenge: if the lane `P` agrees with the folded
word on at least `A` columns it violates the running claim, and so does its low part; otherwise a
position off their agreement set fails the check.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset Polynomial

@[expose] public section

/-! ## The query group -/

open Classical in
/-- **A group of positions, openings and a check**: if every position list (in range, `t` of
them) whose rows pass the check while the commitments break `Post` lies in `S`, the group
escapes `Post` with probability at most `(|S| / 2^depth)^t`. -/
theorem escRet_queryCheck_le (Post : List (ℕ × ℕ × Word) → Prop) (i depth t : ℕ)
    (h1 : 1 ≤ depth) (h128 : depth ≤ 128) (h₀ : List Ev) {wd : ℕ} {W : Word}
    (hc : (commits h₀)[i]? = some (depth, wd, W))
    (check : List ℕ → List (List K) → Prop) [∀ qs words, Decidable (check qs words)]
    (S : ℕ → Prop) [DecidablePred S]
    (hS : ∀ qs : List ℕ, (∀ q ∈ qs, q < 2 ^ depth) → qs.length = t → check qs (qs.map W) →
      ¬ Post (commits h₀) → ∀ q ∈ qs, S q) :
    escRet (fun _ h ↦ Post (commits h)) h₀ []
      (sampleQueries depth t >>= fun qs ↦ queryOpenings i qs >>= fun words ↦
        VerifierProgram.require (check qs words)) ≤
      ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ t := by
  unfold escRet
  rw [bind_eq, retExp_bind]
  let G : List ℕ → List (ℕ × ℕ × Word) → ENNReal := fun qs cs ↦
    match cs[i]?.map fun c ↦ qs.map fun p ↦ c.2.2 (p % 2 ^ c.1) with
    | some rows => if check qs rows then (if Post cs then 0 else 1) else 0
    | none => 0
  have hin : ∀ qs h, retExp (fun _ h ↦ if Post (commits h) then (0 : ENNReal) else 1) h []
      (queryOpenings i qs >>= fun words ↦ VerifierProgram.require (check qs words)) =
      G qs (commits h) := by
    intro qs h
    rw [bind_eq, retExp_bind, retExp_queryP, List.append_nil]
    simp only [answer, G]
    split
    · rename_i rows hr
      rw [hr]
      simp only [VerifierProgram.require]
      split_ifs <;> simp_all [retExp, commits_append_query]
    · rename_i hr
      rw [hr]
  simp only [hin]
  rw [retExp_commits G, List.append_nil, sampleQueries,
    retExp_sampleQueriesAux_restrict_len depth h1 h128 _ t t le_rfl]
  refine le_trans (retExp_mono (g' := fun qs _ ↦ allIn S qs) (fun qs _ ↦ ?_) _ _ _)
    (retExp_sampleQueries_le depth t h1 h128 S h₀ [])
  split_ifs with hr
  · simp only [G, hc, Option.map_some]
    have hmap : (qs.map fun p ↦ W (p % 2 ^ depth)) = qs.map W :=
      List.map_congr_left fun q hq ↦ by rw [Nat.mod_eq_of_lt (hr.1 q hq)]
    rw [hmap]
    split_ifs with hch hP <;> simp only [allIn, zero_le]
    split_ifs with hall
    · exact le_rfl
    · exact absurd (hS qs hr.1 hr.2 hch hP) hall
  · exact zero_le

end
end LeanVM.Protocol.Whir.Sound
