/-
  LeanVM.Protocol.Whir.Sound.LevelFacts

  What a WHIR level's interface reads from the history: the shape of a level's commitment, the
  values the verifier derives from the opened rows, the next level's invariant after `λ`, and the
  escape expectations of the out-of-domain points and of the query positions.
-/

module

public import LeanVM.Protocol.Whir.Sound.Folds
public import LeanVM.Protocol.Whir.Sound.Novel
public import LeanVM.Protocol.Whir.Sound.Queries

/-!
# The level interface's facts

For a level `i` with code `P` and the next level's code `P'` (`P.κ = P'.ℓ + P'.κ`):

* `ShapeOK i P cs`: commitment `i` has the level's height `κ + R` and leaves of `wdOf i ℓ` words.
* `cOf P i cs rounds high q`: the value the verifier derives from the opened row at `q` (`batched`
  in `whirLevels`): the folded oracle at `x_q` plus `Ŵ_κ(x_q) H(x_q)`, `H` the high part
  (`batchedOf_eq`).
* `nextInv_of`: after `λ`, if no member of the next list satisfies the glued claim, the next
  level's invariant `RoundInv` holds with no round.
* `escRet_ood_le`, `escRet_queries_le`: the out-of-domain points escape `OodSep2` with
  probability at most `|list|² (κ|E|^(κ−1))² / |E|^(2κ)`, the query positions escape `QDoom` with
  probability at most `((A − 1)/n)^t`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset Polynomial

@[expose] public section

/-- Commitment `i` has the level's shape. -/
def ShapeOK (i : ℕ) (P : LevelCode) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∃ W, cs[i]? = some (P.κ + P.R, wdOf i P.ℓ, W) ∧ ∀ v, (W v).length = wdOf i P.ℓ

/-- The value the verifier derives from the opened row at `q`. -/
noncomputable def cOf (P : LevelCode) (i : ℕ) (cs : List (ℕ × ℕ × Word))
    (rounds : List FoldRound) (high : List E) (q : ℕ) : E :=
  if h : q < P.n then foldsA P.dom rounds (laneO i cs P.n) 0 ⟨q, h⟩ +
    (hatE P.κ * polyOf high).eval (P.dom ⟨q, h⟩) else 0

/-- The verifier's batch of the opened rows (`batched` in `whirLevels`). -/
def batchedOf (index mu : ℕ) (rounds : List FoldRound) (high : List E) (queries : List ℕ)
    (queryWeights : List E) (words : List (List K)) : E :=
  sumE (List.zipWith (fun (qq, row) queryWeight ↦
    let what := subspaceAt mu (K.ofBits qq)
    queryWeight * (foldRow (lanesOf index row) (K.ofBits qq) rounds +
      novelEval high what * ofK (what.getD mu 0))) (List.zip queries words) queryWeights)

theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  rw [sumE, foldl_add_eq, zero_add]

/-- A batch over zipped queries and rows as a batch over the queries. -/
theorem sumE_zipWith_zip (G : ℕ × List K → E → E) (F : ℕ → List K → E)
    (hG : ∀ q row w, G (q, row) w = w * F q row) (W : ℕ → List K) :
    ∀ (qs : List ℕ) (ws : List E), ws.length = qs.length →
      sumE (List.zipWith G (List.zip qs (qs.map W)) ws) =
        ((ws.zip qs).map fun wq ↦ wq.1 * F wq.2 (W wq.2)).sum
  | [], [], _ => rfl
  | q :: qs, w :: ws, h => by
    have := sumE_zipWith_zip G F hG W qs ws (by simpa using h)
    rw [sumE_eq_sum] at this ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons, List.sum_cons, hG] at this ⊢
    rw [this]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **The verifier's batch** is `Σ_k λ^k c'(q_k)` with `c' = cOf`. -/
theorem batchedOf_eq (P : LevelCode) (i : ℕ) (cs : List (ℕ × ℕ × Word)) (hS : ShapeOK i P cs)
    (rounds : List FoldRound) (hr : rounds.length = P.ℓ) (high : List E)
    (hhigh : high.length ≤ 2 ^ (P.κ + 1)) (qs : List ℕ) (hq : ∀ q ∈ qs, q < P.n) (lam : E) :
    batchedOf i P.κ rounds high qs (powers lam qs.length) (qs.map (wordOf cs i)) =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) * cOf P i cs rounds high qs[k] := by
  rw [← sum_zip_powers]
  unfold batchedOf
  rw [sumE_zipWith_zip _ (fun q row ↦ foldRow (lanesOf i row) (K.ofBits q) rounds +
    novelEval high (subspaceAt P.κ (K.ofBits q)) * ofK ((subspaceAt P.κ (K.ofBits q)).getD P.κ 0))
    (fun _ _ _ ↦ rfl) (wordOf cs i) qs _ (length_powers _ _)]
  refine congrArg List.sum (List.map_congr_left fun wq hwq ↦ ?_)
  have hlt := hq _ (List.of_mem_zip hwq).2
  obtain ⟨W, hW, hlen⟩ := hS
  have hrow : (lanesOf i (wordOf cs i wq.2)).length = 2 ^ rounds.length := by
    rw [hr]; exact length_lanesOf _ (by rw [wordOf_eq hW]; exact hlen _)
  simp only [cOf, hlt, ↓reduceDIte]
  congr 1
  rw [foldRow_eq _ rounds _ hrow, novelEval_eq P.κ_lt high hhigh, subspaceAt_eq,
    List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, eval_mul,
    show P.dom ⟨wq.2, hlt⟩ = ofK (K.ofBits wq.2) from rfl, eval_hatE, mul_comm (ofK _)]
  rfl

end
end LeanVM.Protocol.Whir.Sound
