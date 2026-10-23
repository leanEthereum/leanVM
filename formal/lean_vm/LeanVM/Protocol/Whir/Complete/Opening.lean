/-
  LeanVM.Protocol.Whir.Complete.Opening

  The honest prover of leanVM's WHIR opening and its perfect completeness: the stack's level-0
  word, the round polynomials of the running glued claim, the folded levels' words, the
  out-of-domain values, the intro polynomials and the residual, against which the verifier's
  `verifyStackedOpening` accepts for every challenge.
-/

module

public import LeanVM.Protocol.Whir.Complete.Script
public import LeanVM.Protocol.Whir.Complete.Encoding

/-!
# Completeness of the WHIR opening

The verifier is the port `LeanVM.Protocol.Verifier.verifyStackedOpening` /
`verifyWhir` of `python-verifier/verifier.py:1008-1086, 1349-1355` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, with the commitment `commitStack`. The honest prover
is a specification, written as a `Script` (`LeanVM.Protocol.Whir.Complete.Script`) that sends
its messages in the order the verifier reads them. Its round messages are the two scalars the
Rust prover sends, `u_0 = h(0)` and the quadratic coefficient `u_2` (`send_msg`,
`crates/pcs/src/whir.rs:258-260` at the same revision); its words are the ones the verifier's
reading of an opening (`row.reverse` at level `0`, `_ext_row` deeper) and the Annex's encoder
fix. No correspondence with the Rust prover's memory layout or code is claimed.

## The prover

The prover holds the stack as the table `f₀ = stackTable μ q` in the WHIR variable order (the six
lane variables first), and the weight table `W` of the running claim `Σ_x W(x)·g(x)`, where `g`
is `f₀` with its first coordinates fixed at the fold challenges so far (`foldAll f₀ folds`).
Initially `W` is the table of the batched basis `B(p) = Σ_k s_k·w_k(rotate p)` of the stack
claims.

* Every round polynomial it sends is `(roundC0 W g, roundC2 W g)`, the constant and quadratic
  coefficients of `h(X) = Σ_x W(…, X, x)·g(…, X, x)`; a fold fixes the first coordinate of both
  tables at the challenge.
* A non-final level commits `levelWord`: the current message cut into `2^fold` lanes along the
  next level's fold variables, each lane encoded (`enc`) and written as `E` limbs. It then sends
  the out-of-domain value `ĝ(z) = multilinearEval g z` and the intro polynomial of the claim with
  weight `eq(z, ·)`.
* Every level sends the intro polynomial of its query claim, whose weight table is
  `queryTable`: the batched column weights `Σ_q w_q·X_i(x_q)` at the queried points, which is the
  table of the verifier's own `inducedWeight` (`queryTable_eq`).
* Gluing adds `λ^k` times each claim's table to `W`, as the verifier adds `λ^k` times the intro
  polynomial to its running quadratic.
* The final level sends the residual message `g` in the clear, then the tail round polynomials.

## The invariant

`Inv μ lf f₀ B s W` relates the verifier's state `s` to the weight table `W`: the running target
is `Σ W·g`, the running quadratic is the round polynomial of `(W, g)`, and the weight the
verifier will evaluate at the terminal point (`termWeight`, the basis plus every glued claim's
weight) is the multilinear extension of `W`. A fold keeps it (`Inv.fold`, by
`polyEval_roundQuad`); a glue keeps it when every glued claim's value, intro polynomial and
weight are those of a table (`Inv.glue`). At the end the terminal value is
`W̃(tail)·g̃(tail)`, which the tail rounds compute (`follows_tailRounds`): the terminal check holds.

The claims a level glues are honest because the opened rows are the lanes' codeword entries, so
the enforced sum is the pairing of the folded message with the column weights
(`enforcedSum_honest`), and the verifier's `inducedWeight` and `eqEval z` are multilinear.

## Main results

* `follows_whirLevels`: the honest level script follows `whirLevels` from any state satisfying
  the invariant and any commitments holding the level's word at its index;
  `follows_whirRun`: the same for the whole run of `verify_whir` past `derive_config`, on any
  ladder that starts with the lane fold and whose folds fit in the stack.
* `follows_commitStack`, `follows_verifyStackedOpening`: the honest scripts follow the
  commitment and the opening.
* `runFrom_verifyStackedOpening`, `runFrom_commitStack_verifyStackedOpening`: the interactive
  runs return `()` for every challenge function and commit well-shaped words.
* `runI_openingProgram`, `exists_prove_runProof_openingProgram`: the opening as a whole program
  (`commitStack`, `verifyStackedOpening`, accept) is interactively perfectly complete, hence its
  compiled verifier accepts the honest proof for every hash function, conditioned on the
  proofs of work (`exists_prove_runProof`).

## Hypotheses

* `Whir.Admissible μ R`: the ladder exists (`deriveConfig` returns it), starts with the lane
  fold `6` at rate `R`, and its folds fit in the stack (`ladder_head_sum`, decided over the 56
  pairs); `μ ≤ 64` keeps every message log within the novel basis.
* Every stack claim holds of `q` (`StackClaim.Holds`) and has a multilinear weight
  (`IsMultilinearFn`): the terminal check evaluates the weights at a random point.
* The opening runs after a history whose only commitment is the stack's honest word
  (`stackCommit`): level `ℓ` opens commitment `ℓ`, an absolute index, so no other phase may
  commit between `commitStack` and the opening, as in `verifyExecution`.

No `require` of the opening fails on the honest prover: the deployed program is perfectly
complete.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
  LeanVM.Protocol.Compile LeanVM.Protocol.Whir Finset

@[expose] public section

/-! ## The honest moves -/

/-- Send the round polynomial of `(W, g)`: its constant and quadratic coefficients. -/
def hRound (W g : List E) : Script Unit := do
  Script.sendE (roundC0 W g)
  Script.sendList [roundC2 W g]

/-- The honest round polynomial meets the verifier's `sumcheckRoundPoly 3 claim none`, which
builds `roundQuad claim W g` from it. -/
theorem follows_round (W g : List E) (claim : E) (cs : Commits) :
    Follows (fun cs' _ b ↦ cs' = cs ∧ b = roundQuad claim W g) (hRound W g)
      (sumcheckRoundPoly 3 claim none) cs := by
  simp [hRound, sumcheckRoundPoly, Script.sendE, Script.sendList, Prog.readE, Prog.readN,
    Follows, roundQuad, Script.bind, Prog.bind]

/-- The fold rounds of a level (`foldRounds`): receive the challenge, fix the first coordinate
of both tables at it, send the next round polynomial. -/
def hFoldRounds (f₀ : List E) :
    ℕ → WhirState → List E → List E → Script (WhirState × List E × List E)
  | 0, s, levelFolds, W => return (s, levelFolds, W)
  | n + 1, s, levelFolds, W => do
    let challenge ← Script.sampleE
    let target := polyEval s.quad challenge
    let W' := foldPairs challenge W
    let g' := foldAll f₀ (s.folds ++ [challenge])
    hRound W' g'
    hFoldRounds f₀ n
      { s with target, quad := roundQuad target W' g', folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge]) W'

/-- The tail rounds of the final level (`tailRounds`). -/
def hTailRounds : ℕ → E → List E → List E → List E → Script (List E × E)
  | 0, target, _, _, _ => return ([], target)
  | n + 1, _, quad, W, g => do
    let challenge ← Script.sampleE
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let W' := foldPairs challenge W
      let g' := foldPairs challenge g
      hRound W' g'
      let (rest, target) ← hTailRounds n target (roundQuad target W' g') W' g'
      return (challenge :: rest, target)

/-- The query positions (`sampleQueriesAux`), received as the verifier samples them. -/
def hSampleQueriesAux (depth : ℕ) : ℕ → ℕ → Script (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← Script.sampleE)
      let n := min (192 / depth) remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← hSampleQueriesAux depth fuel (remaining - n)
      return chunk ++ rest

/-- Gluing the claims' tables into the weight table, with the powers of `λ` the verifier uses
(`glue`). -/
def glueTables (lam : E) (W : List E) (Ts : List (List E)) : List E :=
  (Ts.foldl (fun (acc : List E × E) T ↦ (axpy (acc.2 * lam) acc.1 T, acc.2 * lam)) (W, 1)).1

/-- The rows the verifier reads from the commitment it opens at level `index`: the stack's leaf
reversed and lifted at level `0`, the regrouped limbs deeper. -/
def readRow (index : ℕ) (row : List K) : List E :=
  if index = 0 then row.reverse.map ofK else extRow row

/-- **The honest prover of the WHIR levels** (`whirLevels`), from the level `index` with the
verifier's state `s` and the weight table `W`. -/
def hLevels (μ : ℕ) (f₀ : List E) : ℕ → List Whir.Level → WhirState → List E → Script Unit
  | _, [], _, _ => return ()
  | index, level :: rest, s, W => do
    let (s, levelFolds, W) ← hFoldRounds f₀ level.fold s [] W
    let messageLog := μ - s.folds.length
    let g := foldAll f₀ s.folds
    let (residual, pending, tables) ← match rest with
      | [] => do
        Script.sendList g
        pure (g, ([] : List (E × List E × (List E → E))), ([] : List (List E)))
      | next :: _ => do
        Script.commitS (levelWord (messageLog - next.fold) next.fold g)
        let oodPoint ← Script.sampleN messageLog
        let oodValue := multilinearEval g oodPoint
        Script.sendE oodValue
        let T := tableOf messageLog (eqEval oodPoint)
        hRound T g
        pure ([], [(oodValue, roundQuad oodValue T g, fun x ↦ eqEval oodPoint x)], [T])
    Script.grindS
    let queries ← hSampleQueriesAux (messageLog + level.logInvRate) level.queries level.queries
    let lam ← Script.sampleE
    let queryWeights := powers lam queries.length
    let words ← Script.queryS
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let T := queryTable messageLog queries queryWeights
    hRound T g
    let pending := pending ++
      [(enforced, roundQuad enforced T g,
        fun x ↦ Verifier.inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    let W := glueTables lam W (tables ++ [T])
    match rest with
    | [] => do
      let _ ← hTailRounds messageLog s.target s.quad W residual
      return ()
    | _ :: _ => hLevels μ f₀ (index + 1) rest s W

/-! ## The invariant -/

/-- The weight the verifier evaluates at the terminal point `s.folds ++ p`: the basis at the
rotated point plus every glued claim's weight on its level's coordinates (`verify_whir`'s
`weight`). -/
def termWeight (lf : ℕ) (B : List E → E) (s : WhirState) (p : List E) : E :=
  s.glued.foldl (fun weight claim ↦
      weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ p))
    (B ((s.folds ++ p).drop lf ++ (s.folds ++ p).take lf))

/-- **The prover's invariant**: the verifier's state `s` is the running claim `Σ W·g` of the
weight table `W` and the folded stack `g = foldAll f₀ s.folds`, with its round polynomial, and
the terminal weight is the extension of `W`. -/
structure Inv (μ lf : ℕ) (f₀ : List E) (B : List E → E) (s : WhirState) (W : List E) : Prop where
  folds_le : s.folds.length ≤ μ
  len_W : W.length = 2 ^ (μ - s.folds.length)
  target : s.target = dot W (foldAll f₀ s.folds)
  quad : s.quad = roundQuad s.target W (foldAll f₀ s.folds)
  start_le : ∀ c ∈ s.glued, c.foldStart ≤ s.folds.length
  weight : ∀ p : List E, p.length = μ - s.folds.length →
    termWeight lf B s p = multilinearEval W p

section Invariant

variable {μ lf : ℕ} {f₀ : List E} {B : List E → E}

/-- `2^(k+1)` is even: a table on a nonempty cube has its entries in pairs. -/
theorem even_two_pow_succ (k : ℕ) : Even (2 ^ (k + 1)) := by
  rw [pow_succ]; exact even_iff_two_dvd.mpr (dvd_mul_left 2 _)

/-- The stack table with its first `|r|` coordinates fixed has `2^(μ − |r|)` entries. -/
theorem length_foldAll_f₀ (hf₀ : f₀.length = 2 ^ μ) (r : List E) (hr : r.length ≤ μ) :
    (foldAll f₀ r).length = 2 ^ (μ - r.length) :=
  length_foldAll r f₀ _ (by rw [hf₀, Nat.add_sub_cancel' hr])

private theorem foldl_glued_congr (F G : E → GluedClaim → E) :
    ∀ (L : List GluedClaim) (a : E), (∀ c ∈ L, ∀ x, F x c = G x c) → L.foldl F a = L.foldl G a
  | [], _, _ => rfl
  | c :: L, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h c (by simp) a]
    exact foldl_glued_congr F G L _ fun c' hc' ↦ h c' (by simp [hc'])

/-- After a fold, the terminal weight at `p` is the one before at `c :: p`. -/
theorem termWeight_fold (s : WhirState) (c : E) (t : E) (qd : List E)
    (hs : ∀ cl ∈ s.glued, cl.foldStart ≤ s.folds.length) (p : List E) :
    termWeight lf B { s with target := t, quad := qd, folds := s.folds ++ [c] } p =
      termWeight lf B s (c :: p) := by
  simp only [termWeight, List.append_assoc, List.singleton_append]
  exact foldl_glued_congr _ _ _ _ fun cl hcl x ↦ by
    rw [List.drop_append_of_le_length (hs cl hcl), List.append_assoc, List.singleton_append]

/-- **A fold keeps the invariant.** -/
theorem Inv.fold (hf₀ : f₀.length = 2 ^ μ) {s : WhirState} {W : List E}
    (hI : Inv μ lf f₀ B s W) (hlt : s.folds.length < μ) (c : E) :
    Inv μ lf f₀ B
      { s with target := polyEval s.quad c,
               quad := roundQuad (polyEval s.quad c) (foldPairs c W) (foldAll f₀ (s.folds ++ [c])),
               folds := s.folds ++ [c] } (foldPairs c W) := by
  have hm : μ - s.folds.length = μ - (s.folds.length + 1) + 1 := by omega
  have hg := length_foldAll_f₀ hf₀ s.folds hI.folds_le
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · simp only [List.length_append, List.length_singleton]
    rw [length_foldPairs, hI.len_W, hm, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  · simp only
    rw [hI.quad, hI.target, polyEval_roundQuad c _ _ (by rw [hI.len_W, hg])
      (by rw [hI.len_W, hm]; exact even_two_pow_succ _), foldAll_concat]
  · intro cl hcl
    have := hI.start_le cl hcl
    simp only [List.length_append, List.length_singleton]; omega
  · intro p hp
    simp only [List.length_append, List.length_singleton] at hp
    rw [termWeight_fold s c _ _ hI.start_le, hI.weight (c :: p) (by simp; omega),
      multilinearEval_cons]

/-- A claim glued honestly: its value, intro polynomial and weight are those of a table on the
current cube. -/
def HonestClaim (m : ℕ) (g : List E) (item : E × List E × (List E → E)) (T : List E) : Prop :=
  T.length = 2 ^ m ∧ item.1 = dot T g ∧ item.2.1 = roundQuad item.1 T g ∧
    ∀ p : List E, p.length = m → item.2.2 p = multilinearEval T p

/-- One glue step keeps the invariant. -/
theorem Inv.glue_step {s : WhirState} {W : List E} (hI : Inv μ lf f₀ B s W) (sc : E)
    {item : E × List E × (List E → E)} {T : List E}
    (hT : HonestClaim (μ - s.folds.length) (foldAll f₀ s.folds) item T) :
    Inv μ lf f₀ B
      { s with quad := List.zipWith (fun q i ↦ q + sc * i) s.quad item.2.1,
               target := s.target + sc * item.1,
               glued := s.glued ++ [⟨sc, s.folds.length, item.2.2⟩] } (axpy sc W T) := by
  obtain ⟨hTl, hv, hi, hw⟩ := hT
  have hWT : W.length = T.length := by rw [hI.len_W, hTl]
  refine ⟨hI.folds_le, ?_, ?_, ?_, ?_, ?_⟩
  · simp only; rw [length_axpy _ _ _ hWT, hI.len_W]
  · simp only; rw [dot_axpy _ _ _ _ hWT, hI.target, hv]
  · simp only
    rw [hI.quad, hi, hv]
    simp only [roundQuad, List.zipWith_cons_cons, List.zipWith_nil_right, sumE_eq, List.sum_cons,
      List.sum_nil, add_zero, roundC0_axpy _ _ _ _ hWT, roundC2_axpy _ _ _ _ hWT]
    refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨by ring, rfl⟩⟩
  · intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hI.start_le c hc
    · exact le_rfl
  · intro p hp
    simp only at hp ⊢
    rw [multilinearEval_axpy _ _ _ _ hWT, ← hI.weight p hp, ← hw p hp]
    simp [termWeight, List.foldl_append]

/-- **Gluing keeps the invariant** when every glued claim is honest. -/
theorem Inv.glue (lam : E) :
    ∀ (pending : List (E × List E × (List E → E))) (Ts : List (List E)) (s : WhirState)
      (W : List E) (sc : E), Inv μ lf f₀ B s W →
      List.Forall₂ (HonestClaim (μ - s.folds.length) (foldAll f₀ s.folds)) pending Ts →
      Inv μ lf f₀ B
        (pending.foldl (fun (acc : WhirState × E) (item : E × List E × (List E → E)) ↦
          let scalar := acc.2 * lam
          let s := acc.1
          ({ s with quad := List.zipWith (fun q i ↦ q + scalar * i) s.quad item.2.1,
                    target := s.target + scalar * item.1,
                    glued := s.glued ++ [⟨scalar, s.folds.length, item.2.2⟩] }, scalar))
          (s, sc)).1
        (Ts.foldl (fun (acc : List E × E) T ↦ (axpy (acc.2 * lam) acc.1 T, acc.2 * lam)) (W, sc)).1
  | [], [], _, _, _, hI, _ => hI
  | item :: pending, T :: Ts, s, W, sc, hI, hF => by
    rw [List.forall₂_cons] at hF
    rw [List.foldl_cons, List.foldl_cons]
    exact Inv.glue lam pending Ts _ _ _ (hI.glue_step (sc * lam) hF.1) hF.2
  | [], _ :: _, _, _, _, _, hF => by simp at hF
  | _ :: _, [], _, _, _, _, hF => by simp at hF

/-- `glue` unfolded: the left fold over the pending claims, the running claim keeping `λ⁰`. -/
theorem glue_eq (lam : E) (s : WhirState) (pending : List (E × List E × (List E → E))) :
    glue lam s pending =
      (pending.foldl (fun (acc : WhirState × E) (item : E × List E × (List E → E)) ↦
          let scalar := acc.2 * lam
          let s := acc.1
          ({ s with quad := List.zipWith (fun q i ↦ q + scalar * i) s.quad item.2.1,
                    target := s.target + scalar * item.1,
                    glued := s.glued ++ [⟨scalar, s.folds.length, item.2.2⟩] }, scalar))
          (s, 1)).1 := rfl

/-- Gluing leaves the fold challenges unchanged. -/
theorem glue_folds (lam : E) (s : WhirState) (pending : List (E × List E × (List E → E))) :
    (glue lam s pending).folds = s.folds := by
  rw [glue_eq]
  suffices h : ∀ (L : List (E × List E × (List E → E))) (a : WhirState × E),
      (L.foldl (fun (acc : WhirState × E) (item : E × List E × (List E → E)) ↦
          let scalar := acc.2 * lam
          let s := acc.1
          ({ s with quad := List.zipWith (fun q i ↦ q + scalar * i) s.quad item.2.1,
                    target := s.target + scalar * item.1,
                    glued := s.glued ++ [⟨scalar, s.folds.length, item.2.2⟩] }, scalar))
          a).1.folds = a.1.folds from h pending (s, 1)
  intro L
  induction L with
  | nil => intro a; rfl
  | cons x L ih => intro a; rw [List.foldl_cons, ih]

end Invariant

/-! ## The rounds -/

section Rounds

variable {μ lf : ℕ} {f₀ : List E} {B : List E → E}

/-- **The fold rounds.** -/
theorem follows_foldRounds (hf₀ : f₀.length = 2 ^ μ) :
    ∀ (n : ℕ) (s : WhirState) (lfs W : List E) (cs : Commits), Inv μ lf f₀ B s W →
      s.folds.length + n ≤ μ →
      Follows (fun cs' a b ↦ cs' = cs ∧ b = (a.1, a.2.1) ∧ Inv μ lf f₀ B a.1 a.2.2 ∧
          ∃ new : List E, new.length = n ∧ a.1.folds = s.folds ++ new ∧ a.2.1 = lfs ++ new)
        (hFoldRounds f₀ n s lfs W) (foldRounds n s lfs) cs
  | 0, s, lfs, W, cs, hI, _ => by
    simp only [hFoldRounds, foldRounds]
    exact ⟨rfl, rfl, hI, [], rfl, by simp, by simp⟩
  | n + 1, s, lfs, W, cs, hI, hn => by
    simp only [hFoldRounds, foldRounds]
    refine Follows.bind_of (Follows.sampleE_sampleE cs) ?_
    rintro cs' c c' ⟨rfl, rfl⟩
    refine Follows.bind_of (follows_round _ _ (polyEval s.quad c) cs') ?_
    rintro cs'' _ qd ⟨rfl, rfl⟩
    refine Follows.mono ?_ _ _ _ (follows_foldRounds hf₀ n _ (lfs ++ [c]) _ cs''
      (hI.fold hf₀ (by omega) c) (by simp; omega))
    rintro cs a b ⟨h1, h2, h3, new, hl, hf, hlf⟩
    refine ⟨h1, h2, h3, c :: new, by simp [hl], ?_, ?_⟩
    · rw [hf]; simp
    · rw [hlf]; simp

/-- **The tail rounds** end on the product of the two tables' extensions at the tail point. -/
theorem follows_tailRounds :
    ∀ (n : ℕ) (target : E) (quad W g : List E) (cs : Commits),
      W.length = 2 ^ n → g.length = 2 ^ n → target = dot W g → quad = roundQuad target W g →
      Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ b.1.length = n ∧
          b.2 = multilinearEval W b.1 * multilinearEval g b.1)
        (hTailRounds n target quad W g) (tailRounds n target quad) cs
  | 0, target, quad, W, g, cs, hW, hg, ht, _ => by
    simp only [hTailRounds, tailRounds]
    refine ⟨rfl, rfl, rfl, ?_⟩
    obtain ⟨w, rfl⟩ : ∃ w, W = [w] := List.length_eq_one_iff.mp hW
    obtain ⟨x, rfl⟩ : ∃ x, g = [x] := List.length_eq_one_iff.mp hg
    simp [ht, dot_cons, multilinearEval]
  | n + 1, target, quad, W, g, cs, hW, hg, ht, hq => by
    simp only [hTailRounds, tailRounds]
    refine Follows.bind_of (Follows.sampleE_sampleE cs) ?_
    rintro cs' c c' ⟨rfl, rfl⟩
    have hWg : W.length = g.length := by rw [hW, hg]
    have hev : Even W.length := by rw [hW]; exact even_two_pow_succ n
    have hpe : polyEval quad c = dot (foldPairs c W) (foldPairs c g) := by
      rw [hq, ht, polyEval_roundQuad c W g hWg hev]
    have hlW : (foldPairs c W).length = 2 ^ n := by
      rw [length_foldPairs, hW, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hlg : (foldPairs c g).length = 2 ^ n := by
      rw [length_foldPairs, hg, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true]
      refine ⟨rfl, rfl, rfl, ?_⟩
      obtain ⟨w, hw⟩ : ∃ w, foldPairs c W = [w] := List.length_eq_one_iff.mp hlW
      obtain ⟨x, hx⟩ : ∃ x, foldPairs c g = [x] := List.length_eq_one_iff.mp hlg
      simp only
      rw [hpe, multilinearEval_cons, multilinearEval_cons, hw, hx]
      simp [dot_cons, multilinearEval]
    · simp only [hn, ite_false]
      refine Follows.bind_of (follows_round _ _ (polyEval quad c) cs') ?_
      rintro cs'' _ qd ⟨rfl, rfl⟩
      refine Follows.bind_of (follows_tailRounds n _ _ _ _ cs'' hlW hlg hpe rfl) ?_
      rintro cs''' ⟨rest, t⟩ b ⟨rfl, rfl, hl, ht'⟩
      simp only at hl ht' ⊢
      refine ⟨rfl, rfl, by simp [hl], ?_⟩
      rw [multilinearEval_cons, multilinearEval_cons, ht']

/-- **The query positions** are the verifier's, each below `2^depth`. -/
theorem follows_sampleQueriesAux (depth : ℕ) :
    ∀ (fuel remaining : ℕ) (cs : Commits),
      Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ ∀ x ∈ b, x < 2 ^ depth)
        (hSampleQueriesAux depth fuel remaining) (sampleQueriesAux depth fuel remaining) cs
  | 0, _, cs => by simp [hSampleQueriesAux, sampleQueriesAux, Follows]
  | fuel + 1, remaining, cs => by
    simp only [hSampleQueriesAux, sampleQueriesAux]
    split
    · simp [Follows]
    · refine Follows.bind_of (Follows.sampleE_sampleE cs) ?_
      rintro cs' c c' ⟨rfl, rfl⟩
      refine Follows.bind_of (follows_sampleQueriesAux depth fuel _ cs') ?_
      rintro cs'' a b ⟨rfl, rfl, hb⟩
      refine ⟨rfl, rfl, fun x hx ↦ ?_⟩
      simp only [List.mem_append, List.mem_map] at hx
      rcases hx with ⟨k, _, rfl⟩ | hx
      · exact Nat.mod_lt _ (by positivity)
      · exact hb x hx

end Rounds

/-! ## The levels -/

/-- The commitments in place when a level starts: the word it opens sits at its index and reads,
at every position, as the lanes' codeword entries of the level's message `g` on `m` variables. -/
def LevelCommit (cs : Commits) (index m : ℕ) (g : List E) (level : Whir.Level) : Prop :=
  cs.length = index + 1 ∧ ∃ w word, cs[index]? = some (m - level.fold + level.logInvRate, w, word) ∧
    ∀ p, readRow index (word p) = laneCodes (m - level.fold) level.fold g p

section Levels

variable {μ lf : ℕ} {f₀ : List E} {B : List E → E}

/-- The out-of-domain claim is honest. -/
theorem honestClaim_ood {m : ℕ} {g : List E} (hg : g.length = 2 ^ m) (z : List E)
    (hz : z.length = m) :
    HonestClaim m g (multilinearEval g z, roundQuad (multilinearEval g z) (tableOf m (eqEval z)) g,
      fun x ↦ eqEval z x) (tableOf m (eqEval z)) := by
  subst hz
  refine ⟨length_tableOf _ _, ?_, rfl, fun p hp ↦ ?_⟩
  · simp only
    rw [multilinearEval_eq_sum _ g z hg rfl, dot_tableOf _ _ _ hg]
    exact sum_congr rfl fun i _ ↦ by rw [eqEval_comm, mul_comm]
  · exact (multilinearEval_tableOf (isMultilinearFn_eqEval z) p hp).symm

/-- The query claim is honest. -/
theorem honestClaim_query {κ : ℕ} (hκ : κ ≤ 64) (g r : List E)
    (hg : g.length = 2 ^ (r.length + κ)) (queries : List ℕ) (queryWeights : List E) :
    HonestClaim κ (foldAll g r)
      (enforcedSum (queries.map (laneCodes κ r.length g)) r queryWeights,
        roundQuad (enforcedSum (queries.map (laneCodes κ r.length g)) r queryWeights)
          (tableOf κ (Verifier.inducedWeight κ queries queryWeights)) (foldAll g r),
        fun x ↦ Verifier.inducedWeight κ queries queryWeights x)
      (tableOf κ (Verifier.inducedWeight κ queries queryWeights)) :=
  ⟨length_tableOf _ _, enforcedSum_honest hκ g r queries queryWeights hg, rfl, fun p hp ↦
    (multilinearEval_tableOf (isMultilinearFn_inducedWeight κ queries queryWeights) p hp).symm⟩

/-- The verifier's reading of opened rows, row by row (`readRow`). -/
theorem readRows_eq (index : ℕ) (words : List (List K)) :
    (if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow) =
      words.map (readRow index) := by
  by_cases h : index = 0 <;> simp [readRow, h]

/-- **The honest prover of the WHIR levels follows `whirLevels`** from any state satisfying the
invariant, provided the remaining folds fit and the level's word is committed at its index. -/
theorem follows_whirLevels (hf₀ : f₀.length = 2 ^ μ) (hμ : μ ≤ 64) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (W : List E) (cs : Commits),
      levels ≠ [] → Inv μ lf f₀ B s W →
      (levels.map (·.fold)).sum ≤ μ - s.folds.length →
      (∀ level ∈ levels.head?,
        LevelCommit cs index (μ - s.folds.length) (foldAll f₀ s.folds) level) →
      Follows (fun _ _ _ ↦ True) (hLevels μ f₀ index levels s W)
        (whirLevels μ lf B index levels s) cs
  | [], _, _, _, _, h, _, _, _ => absurd rfl h
  | level :: rest, index, s, W, cs, _, hI, hsum, hC => by
    obtain ⟨hcl, w, word, hcs, hrow⟩ := hC level (by simp)
    simp only [List.map_cons, List.sum_cons] at hsum
    have hle := hI.folds_le
    rw [hLevels, whirLevels]
    refine Follows.bind_of (follows_foldRounds hf₀ level.fold s [] W cs hI (by omega)) ?_
    rintro cs1 ⟨s1, lfs1, W1⟩ b ⟨hcs1, rfl, hI1, new, hnl, hs1, hlf1⟩
    simp only [List.nil_append] at hlf1
    subst cs1 lfs1
    dsimp only at hI1 hs1 ⊢
    -- The level's message before and after its folds.
    have hm : μ - s1.folds.length = μ - s.folds.length - level.fold := by
      rw [hs1, List.length_append, hnl, Nat.sub_sub]
    have hg : (foldAll f₀ s.folds).length = 2 ^ (new.length + (μ - s1.folds.length)) := by
      rw [length_foldAll_f₀ hf₀ _ hI.folds_le, hm, hnl, Nat.add_sub_cancel' (by omega)]
    have hg' : (foldAll f₀ s1.folds).length = 2 ^ (μ - s1.folds.length) :=
      length_foldAll_f₀ hf₀ _ hI1.folds_le
    have hgg : foldAll (foldAll f₀ s.folds) new = foldAll f₀ s1.folds := by
      rw [hs1, foldAll_append]
    have hκ : μ - s1.folds.length ≤ 64 := by omega
    -- The opening of the level's word answers the lanes at the queried positions, as long as
    -- the commitment at the level's index is unchanged.
    have hans0 : ∀ cs' : Commits, cs'[index]? = cs[index]? → ∀ queries : List ℕ,
        (∀ x ∈ queries, x < 2 ^ (μ - s1.folds.length + level.logInvRate)) →
          answerOf cs' index queries = some (queries.map fun p ↦ word p) := by
      intro cs' hidx queries hq
      simp only [answerOf, hidx, hcs, Option.map_some]
      congr 1
      refine List.map_congr_left fun p hp ↦ ?_
      rw [Nat.mod_eq_of_lt (by have := hq p hp; rwa [hm] at this)]
    rcases rest with _ | ⟨next, rest'⟩
    on_goal 1 =>
      dsimp only
      have := Follows.sendList_readN cs (foldAll f₀ s1.folds)
      rw [hg'] at this
      refine Follows.bind_of this ?_
      rintro cs' _ b ⟨rfl, rfl⟩
      refine Follows.bind_of (R' := fun cs' (a : List E × List (E × List E × (List E → E)) ×
          List (List E)) (b : List E × List (E × List E × (List E → E))) ↦
          b = (a.1, a.2.1) ∧
          List.Forall₂ (HonestClaim (μ - s1.folds.length) (foldAll f₀ s1.folds)) a.2.1 a.2.2 ∧
          (∀ queries : List ℕ, (∀ x ∈ queries, x < 2 ^ (μ - s1.folds.length + level.logInvRate)) →
            answerOf cs' index queries = some (queries.map fun p ↦ word p)) ∧
          a.1 = foldAll f₀ s1.folds)
        (Follows.ret_ret ⟨rfl, List.Forall₂.nil, hans0 cs' rfl, rfl⟩) ?_
    on_goal 2 =>
      dsimp only [levelShape]
      refine Follows.bind_of (Follows.commitS_commitP (wellShaped_levelWord _ _ _) cs) ?_
      rintro cs' _ _ rfl
      refine Follows.bind_of (Follows.sampleN_sampleN _ (μ - s1.folds.length)) ?_
      rintro c2 z _ ⟨rfl, rfl, hz⟩
      refine Follows.bind_of (Follows.sendE_readE _ _) ?_
      rintro c3 _ v ⟨rfl, rfl⟩
      refine Follows.bind_of (follows_round _ _ _ _) ?_
      rintro c4 _ intro ⟨rfl, rfl⟩
      refine Follows.bind_of (R' := fun cs' (a : List E × List (E × List E × (List E → E)) ×
          List (List E)) (b : List E × List (E × List E × (List E → E))) ↦
          b = (a.1, a.2.1) ∧
          List.Forall₂ (HonestClaim (μ - s1.folds.length) (foldAll f₀ s1.folds)) a.2.1 a.2.2 ∧
          (∀ queries : List ℕ, (∀ x ∈ queries, x < 2 ^ (μ - s1.folds.length + level.logInvRate)) →
            answerOf cs' index queries = some (queries.map fun p ↦ word p)) ∧
          LevelCommit cs' (index + 1) (μ - s1.folds.length) (foldAll f₀ s1.folds) next)
        (Follows.ret_ret ⟨rfl, List.Forall₂.cons (honestClaim_ood hg' z hz) List.Forall₂.nil,
          hans0 _ (List.getElem?_append_left (by omega)), ?_⟩) ?_
      refine ⟨by simp [hcl], 3 * 2 ^ next.fold,
        levelWord (μ - s1.folds.length - next.fold) next.fold (foldAll f₀ s1.folds), ?_,
        fun p ↦ ?_⟩
      · rw [List.getElem?_append_right (by omega)]
        simp [hcl]
      · simp only [readRow, Nat.add_one_ne_zero, ite_false]
        exact extRow_levelWord _ _ _ p
    all_goals
      rintro cs2 ⟨residual, pending, tables⟩ b ⟨rfl, hF, hans, hfinal⟩
      dsimp only
      refine Follows.bind_of (Follows.grindS_grindP _ _) ?_
      rintro cs3 _ _ rfl
      dsimp only [sampleQueries]
      refine Follows.bind_of (follows_sampleQueriesAux _ _ _ _) ?_
      rintro cs4 queries _ ⟨rfl, rfl, hq⟩
      refine Follows.bind_of (Follows.sampleE_sampleE _) ?_
      rintro cs5 lam _ ⟨rfl, rfl⟩
      refine Follows.bind_of (Follows.queryS_queryP (hans queries hq)) ?_
      rintro cs6 _ _ ⟨rfl, rfl, rfl⟩
      have hrows : (if index = 0 then (queries.map fun p ↦ word p).map fun row ↦ row.reverse.map ofK
          else (queries.map fun p ↦ word p).map extRow) =
            queries.map (laneCodes (μ - s1.folds.length) new.length (foldAll f₀ s.folds)) := by
        rw [readRows_eq, List.map_map]
        refine List.map_congr_left fun p _ ↦ ?_
        simp only [Function.comp_apply]
        rw [hrow p, hm, hnl]
      rw [hrows, queryTable_eq hκ]
      refine Follows.bind_of (follows_round _ _ _ _) ?_
      rintro cs7 _ intro ⟨rfl, rfl⟩
      -- The glued state keeps the invariant.
      have hq' := honestClaim_query hκ (foldAll f₀ s.folds) new hg queries
        (powers lam queries.length)
      rw [hgg] at hq'
      have hI2 : Inv μ lf f₀ B (glue lam s1 (pending ++ _)) (glueTables lam W1 (tables ++ _)) :=
        Inv.glue lam _ _ s1 W1 1 hI1 (List.rel_append hF (List.Forall₂.cons hq' List.Forall₂.nil))
      have hfolds := glue_folds lam s1 (pending ++ [(enforcedSum
        (queries.map (laneCodes (μ - s1.folds.length) new.length (foldAll f₀ s.folds))) new
          (powers lam queries.length), roundQuad (enforcedSum
        (queries.map (laneCodes (μ - s1.folds.length) new.length (foldAll f₀ s.folds))) new
          (powers lam queries.length)) (tableOf (μ - s1.folds.length)
            (Verifier.inducedWeight (μ - s1.folds.length) queries (powers lam queries.length)))
            (foldAll f₀ s1.folds), fun x ↦ Verifier.inducedWeight (μ - s1.folds.length) queries
              (powers lam queries.length) x)])
    on_goal 1 =>
      subst hfinal
      have ht2 := hI2.target
      have hq2 := hI2.quad
      have hl2 := hI2.len_W
      rw [hfolds] at ht2 hq2 hl2
      refine Follows.bind_of (follows_tailRounds _ _ _ _ _ _ hl2 hg' ht2 hq2) ?_
      rintro cs8 ⟨tail, t⟩ _ ⟨rfl, rfl, hl, ht⟩
      dsimp only at hl ht ⊢
      refine Follows.ret_require ?_ trivial
      change termWeight lf B _ tail * _ = t
      rw [hI2.weight tail (by rw [hl, hfolds]), ht]
    on_goal 1 =>
      refine follows_whirLevels hf₀ hμ (next :: rest') (index + 1) _ _ _ (by simp) hI2 ?_ ?_
      · rw [hfolds, hm]
        simp only [List.map_cons, List.sum_cons] at hsum ⊢
        omega
      · intro level' hl'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hl'
        subst hl'
        rw [hfolds]
        exact hfinal

end Levels

/-! ## The ladder -/

private theorem admissible_bounded {μ R : ℕ} (h : Whir.Admissible μ R) :
    μ < Whir.maxLogStack + 1 ∧ R < Whir.maxLogInvRate + 1 := by
  obtain ⟨_, h2, _, h4⟩ := h
  exact ⟨Nat.lt_succ_of_le h2, Nat.lt_succ_of_le h4⟩

/-- Every admissible ladder starts with the lane fold at the announced rate, and its folds fit
in the stack. -/
theorem ladder_head_sum {μ R : ℕ} (h : Whir.Admissible μ R) :
    ∀ levels, Whir.ladder μ R = some levels →
      levels.head?.map (fun l ↦ (l.fold, l.logInvRate)) = some (laneBits, R) ∧
        (levels.map (·.fold)).sum ≤ μ := by
  have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < Whir.maxLogInvRate + 1, Whir.Admissible μ r →
      ∀ levels, Whir.ladder μ r = some levels →
        levels.head?.map (fun l ↦ (l.fold, l.logInvRate)) = some (laneBits, r) ∧
          (levels.map (·.fold)).sum ≤ μ := by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 R h2 h

/-- The ladder of an admissible pair, with its first level made explicit. -/
theorem exists_ladder {μ R : ℕ} (h : Whir.Admissible μ R) :
    ∃ q₀ rest, deriveConfig μ R = some (⟨laneBits, R, q₀⟩ :: rest) ∧
      laneBits + (rest.map (·.fold)).sum ≤ μ := by
  obtain ⟨config, hc⟩ := Option.isSome_iff_exists.mp (Whir.ladder_isSome h)
  obtain ⟨hhead, hsum⟩ := ladder_head_sum h config hc
  rcases config with _ | ⟨⟨f, r, q₀⟩, rest⟩
  · simp at hhead
  · simp only [List.head?_cons, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hhead
    obtain ⟨rfl, rfl⟩ := hhead
    refine ⟨q₀, rest, hc, ?_⟩
    simpa using hsum

/-! ## The stack claims -/

/-- The batched basis of the stack claims, `p ↦ Σ_k s_k·w_k(p)` (`verify_stacked_opening`'s
`evaluate_basis`). -/
def batchedBasis (scales : List E) (claims : List StackClaim) : List E → E :=
  fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- The batched basis of multilinear weights is multilinear. -/
theorem isMultilinearFn_batchedBasis {m : ℕ} :
    ∀ (scales : List E) (claims : List StackClaim), (∀ c ∈ claims, IsMultilinearFn m c.1) →
      IsMultilinearFn m (batchedBasis scales claims)
  | [], _, _ => isMultilinearFn_congr (isMultilinearFn_const_zero m) fun p _ ↦ by
      simp [batchedBasis]
  | _ :: _, [], _ => isMultilinearFn_congr (isMultilinearFn_const_zero m) fun p _ ↦ by
      simp [batchedBasis]
  | a :: scales, c :: claims, h => by
    refine isMultilinearFn_congr (isMultilinearFn_add (isMultilinearFn_const_mul (h c (by simp)) a)
      (isMultilinearFn_batchedBasis scales claims fun c' hc' ↦ h c' (by simp [hc'])))
      fun p _ ↦ ?_
    simp [batchedBasis, dot_cons]

/-- The batched value of claims that hold is the batched basis paired with the stack. -/
theorem dot_values_eq_sum {μ : ℕ} (q : Column μ) :
    ∀ (scales : List E) (claims : List StackClaim), (∀ c ∈ claims, StackClaim.Holds μ c q) →
      dot scales (claims.map (·.2)) =
        ∑ x ∈ range (2 ^ μ), batchedBasis scales claims (boolPoint μ x) * ofK (q.values.getD x 0)
  | [], _, _ => by simp [batchedBasis]
  | _ :: _, [], _ => by simp [batchedBasis]
  | a :: scales, c :: claims, h => by
    have hc := h c (by simp)
    rw [StackClaim.Holds, Fin.sum_univ_eq_sum_range
      (fun x ↦ c.1 (boolPoint μ x) * ofK (q.values.getD x 0))] at hc
    simp only [List.map_cons, dot_cons, batchedBasis] at *
    rw [dot_values_eq_sum q scales claims fun c' hc' ↦ h c' (by simp [hc']), ← hc, mul_sum,
      ← sum_add_distrib]
    exact sum_congr rfl fun x _ ↦ by simp only [batchedBasis]; ring

/-- The batched basis at the rotated point: the weight table of the opening's starting claim. -/
def basisTable (μ : ℕ) (scales : List E) (claims : List StackClaim) : List E :=
  tableOf μ fun p ↦ batchedBasis scales claims (p.drop laneBits ++ p.take laneBits)

/-- **The starting claim.** The batched value of claims that hold is the pairing of the basis
table with the stack table, both in the WHIR variable order. -/
theorem dot_values_eq_dot {μ : ℕ} (hμ : laneBits ≤ μ) (q : Column μ) (scales : List E)
    (claims : List StackClaim) (h : ∀ c ∈ claims, StackClaim.Holds μ c q) :
    dot scales (claims.map (·.2)) = dot (basisTable μ scales claims) (stackTable μ q) := by
  rw [dot_values_eq_sum q scales claims h, basisTable, dot_tableOf _ _ _ (length_stackTable μ q)]
  obtain ⟨n, rfl⟩ : ∃ n, μ = laneBits + n := ⟨μ - laneBits, by omega⟩
  have hn : laneBits + n - laneBits = n := by omega
  have hrot := sum_rotIndex laneBits n
    (fun x ↦ batchedBasis scales claims (boolPoint (n + laneBits) x) *
      ofK (q.values.getD x 0))
  rw [Nat.add_comm n laneBits] at hrot
  rw [← hrot]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' : i < 2 ^ (laneBits + n) := mem_range.mp hi
  have hb := boolPoint_rotIndex laneBits n i hi'
  rw [Nat.add_comm n laneBits] at hb
  simp only [stackTable, hn]
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range, hb]

/-- The batched basis at the rotated point is the extension of the basis table. -/
theorem multilinearEval_basisTable {μ : ℕ} (hμ : laneBits ≤ μ) (scales : List E)
    (claims : List StackClaim) (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) (p : List E)
    (hp : p.length = μ) :
    multilinearEval (basisTable μ scales claims) p =
      batchedBasis scales claims (p.drop laneBits ++ p.take laneBits) := by
  obtain ⟨n, rfl⟩ : ∃ n, μ = laneBits + n := ⟨μ - laneBits, by omega⟩
  have hB := isMultilinearFn_batchedBasis scales claims hml
  rw [Nat.add_comm] at hB
  exact multilinearEval_tableOf (isMultilinearFn_rotate hB) p hp

/-! ## The opening -/

/-- `verify_whir` past `derive_config`: the first round polynomial, then the levels of the ladder
`levels` from the claim `target` on the basis `B`. -/
def whirRun (μ : ℕ) (levels : List Whir.Level) (target : E) (B : List E → E) : Prog Unit := do
  let quad ← sumcheckRoundPoly 3 target none
  whirLevels μ ((levels.head?.map (·.fold)).getD 0) B 0 levels ⟨target, quad, [], []⟩

/-- `verifyWhir` is `whirRun` on the configuration `derive_config` returns. -/
theorem verifyWhir_eq (μ R : ℕ) (target : E) (B : List E → E) :
    verifyWhir μ R target B =
      Verifier.liftOption (deriveConfig μ R) >>= fun config ↦ whirRun μ config target B := rfl

/-- The honest prover of `whirRun`: the round polynomial of the starting claim `Σ W₀·f₀`, then
the levels. -/
def hWhirRun (μ : ℕ) (f₀ W₀ : List E) (levels : List Whir.Level) (target : E) : Script Unit := do
  hRound W₀ f₀
  hLevels μ f₀ 0 levels ⟨target, roundQuad target W₀ f₀, [], []⟩ W₀

/-- **The honest prover of the stacked opening** (`verify_stacked_opening`, then `verify_whir`):
receive the batching challenge, then run the levels from the starting claim
`Σ_x B(x)·f₀(x)` with the basis table as the weight. -/
def honestOpening (μ R : ℕ) (q : Column μ) (claims : List StackClaim) : Script Unit := do
  let c ← Script.sampleE
  let scales := powers c claims.length
  match deriveConfig μ R with
  | none => return ()
  | some config =>
    hWhirRun μ (stackTable μ q) (basisTable μ scales claims) config (dot scales (claims.map (·.2)))

/-- The commitment the opening opens at level `0`: the stack's word, `2^(μ−6+R)` leaves of `64`
words. -/
def stackCommit (μ R : ℕ) (q : Column μ) : ℕ × ℕ × Word :=
  (μ - laneBits + R, 2 ^ laneBits, stackWord μ q)

/-- **The honest commitment follows `commitStack`.** -/
theorem follows_commitStack {μ R : ℕ} (hadm : Whir.Admissible μ R) (q : Column μ)
    (cs : Commits) :
    Follows (fun cs' _ _ ↦ cs' = cs ++ [stackCommit μ R q]) (Script.commitS (stackWord μ q))
      (commitStack μ R) cs := by
  obtain ⟨q₀, rest, hc, _⟩ := exists_ladder hadm
  simp only [commitStack, hc, Verifier.liftOption, Prog.bind_eq, Prog.ret_bind, levelShape]
  exact Follows.commitS_commitP (wellShaped_stackWord μ q) cs

/-- **Completeness of the WHIR run on any ladder** that starts with the lane fold at rate `R`
and whose folds fit in the stack: for stack claims that hold of `q` with multilinear weights,
batched by any scales, the honest prover follows `whirRun` from the commitments
`[stackCommit μ R q]`. -/
theorem follows_whirRun {μ R q₀ : ℕ} {rest : List Whir.Level} (hμ6 : laneBits ≤ μ) (hμ64 : μ ≤ 64)
    (hsum : laneBits + (rest.map (·.fold)).sum ≤ μ) (q : Column μ) (scales : List E)
    (claims : List StackClaim) (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q)
    (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) :
    Follows (fun _ _ _ ↦ True)
      (hWhirRun μ (stackTable μ q) (basisTable μ scales claims) (⟨laneBits, R, q₀⟩ :: rest)
        (dot scales (claims.map (·.2))))
      (whirRun μ (⟨laneBits, R, q₀⟩ :: rest) (dot scales (claims.map (·.2)))
        (batchedBasis scales claims))
      [stackCommit μ R q] := by
  simp only [hWhirRun, whirRun]
  refine Follows.bind_of (follows_round _ _ _ _) ?_
  rintro _ _ _ ⟨rfl, rfl⟩
  refine follows_whirLevels (lf := laneBits) (B := batchedBasis scales claims)
    (length_stackTable μ q) hμ64 _ 0 _ _ _ (by simp) ⟨by simp, by simp [basisTable], ?_, rfl,
      by simp, fun p hp ↦ ?_⟩ (by simpa using hsum) ?_
  · exact dot_values_eq_dot hμ6 q _ claims hholds
  · simp only [termWeight, List.foldl_nil, List.nil_append]
    exact (multilinearEval_basisTable hμ6 _ claims hml p (by simpa using hp)).symm
  · intro level hl
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hl
    subst hl
    refine ⟨rfl, 2 ^ laneBits, stackWord μ q, by simp [stackCommit], fun p ↦ ?_⟩
    simp only [readRow, ite_true, List.length_nil, Nat.sub_zero, foldAll_nil]
    exact readRow_stackWord hμ6 q p

/-- **Perfect completeness of the stacked opening, as a simulation.** For an admissible
`(μ, R)` and stack claims that hold of `q` with multilinear weights, the honest prover follows
`verifyStackedOpening` from the commitments `[stackCommit μ R q]`: every `require`, WHIR's
terminal check included, holds whatever the challenges. -/
theorem follows_verifyStackedOpening {μ R : ℕ} (hadm : Whir.Admissible μ R) (q : Column μ)
    (claims : List StackClaim) (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q)
    (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) :
    Follows (fun _ _ _ ↦ True) (honestOpening μ R q claims) (verifyStackedOpening μ R claims)
      [stackCommit μ R q] := by
  obtain ⟨q₀, rest, hc, hsum⟩ := exists_ladder hadm
  have hμ6 : laneBits ≤ μ := le_trans (by decide) hadm.1
  have hμ64 : μ ≤ 64 := le_trans hadm.2.1 (by decide)
  simp only [honestOpening, verifyStackedOpening, verifyWhir_eq]
  refine Follows.bind_of (Follows.sampleE_sampleE _) ?_
  rintro cs c _ ⟨rfl, rfl⟩
  simp only [hc, Verifier.liftOption, Prog.bind_eq, Prog.ret_bind]
  exact follows_whirRun hμ6 hμ64 hsum q _ claims hholds hml

/-! ## The interactive runs -/

/-- The honest strategy of the opening: the replay of `honestOpening` after the first `n`
events of the history. -/
def openingStrategy (μ R : ℕ) (q : Column μ) (claims : List StackClaim) (n : ℕ) : Strategy :=
  Strategy.ofScript (honestOpening μ R q claims) n

/-- **Perfect completeness of the stacked opening.** For an admissible `(μ, R)` and stack claims
that hold of `q` with multilinear weights: from any history whose only commitment is the stack's
honest word, every strategy that sends what the honest prover sends after that history makes the
interactive run of `verifyStackedOpening` return `()` against every challenge function (every
`require` holds, WHIR's terminal check included), and commits well-shaped words. -/
theorem runFrom_verifyStackedOpening {μ R : ℕ} (hadm : Whir.Admissible μ R) (q : Column μ)
    (claims : List StackClaim) (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q)
    (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) (h : List Ev)
    (hcs : commits h = [stackCommit μ R q]) (S : Strategy)
    (hS : ∀ e, S.msg (h ++ e) = (honestOpening μ R q claims).msgAt e ∧
      S.word (h ++ e) = (honestOpening μ R q claims).wordAt e) (chal : List Ev → E) :
    S.runFrom chal (verifyStackedOpening μ R claims) h = some () ∧
      S.ShapedFrom chal (verifyStackedOpening μ R claims) h := by
  obtain ⟨⟨b, hb, -⟩, hsh⟩ := runFrom_of_follows' S chal hS
    (hcs ▸ follows_verifyStackedOpening hadm q claims hholds hml)
  exact ⟨hb, hsh⟩

/-- The same for the replayed honest strategy itself. -/
theorem runFrom_openingStrategy {μ R : ℕ} (hadm : Whir.Admissible μ R) (q : Column μ)
    (claims : List StackClaim) (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q)
    (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) (h : List Ev)
    (hcs : commits h = [stackCommit μ R q]) (chal : List Ev → E) :
    (openingStrategy μ R q claims h.length).runFrom chal (verifyStackedOpening μ R claims) h =
        some () ∧
      (openingStrategy μ R q claims h.length).ShapedFrom chal (verifyStackedOpening μ R claims) h :=
  runFrom_verifyStackedOpening hadm q claims hholds hml h hcs _
    (ofScript_agrees _ h) chal

/-- The commitment and the opening in sequence, as the honest prover runs them when no other
phase commits in between. -/
def honestCommitOpening (μ R : ℕ) (q : Column μ) (claims : List StackClaim) : Script Unit := do
  Script.commitS (stackWord μ q)
  honestOpening μ R q claims

/-- The honest commitment followed by the honest opening follows `commitStack` followed by
`verifyStackedOpening`, from no commitments. -/
theorem follows_commitStack_verifyStackedOpening {μ R : ℕ} (hadm : Whir.Admissible μ R)
    (q : Column μ) (claims : List StackClaim) (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q)
    (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) :
    Follows (fun _ _ _ ↦ True) (honestCommitOpening μ R q claims)
      (do commitStack μ R; verifyStackedOpening μ R claims) [] :=
  Follows.bind_of (follows_commitStack hadm q []) fun _ _ _ h ↦ by
    subst h; exact follows_verifyStackedOpening hadm q claims hholds hml

/-- **The commitment and the opening, from a history without commitments.** -/
theorem runFrom_commitStack_verifyStackedOpening {μ R : ℕ} (hadm : Whir.Admissible μ R)
    (q : Column μ) (claims : List StackClaim) (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q)
    (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) (h : List Ev) (hcs : commits h = [])
    (chal : List Ev → E) :
    let S := Strategy.ofScript (honestCommitOpening μ R q claims) h.length
    S.runFrom chal (do commitStack μ R; verifyStackedOpening μ R claims) h = some () ∧
      S.ShapedFrom chal (do commitStack μ R; verifyStackedOpening μ R claims) h := by
  intro S
  obtain ⟨⟨b, hb, -⟩, hsh⟩ := runFrom_of_follows' S chal (ofScript_agrees _ h)
    (hcs ▸ follows_commitStack_verifyStackedOpening hadm q claims hholds hml)
  exact ⟨hb, hsh⟩

/-! ## Through the compilation -/

/-- The commitment and the opening as a whole verifier: commit, open, accept. -/
def openingProgram (μ R : ℕ) (claims : List StackClaim) : Prog Bool := do
  commitStack μ R
  verifyStackedOpening μ R claims
  return true

/-- The honest prover of `openingProgram`. -/
def openingProver (μ R : ℕ) (q : Column μ) (claims : List StackClaim) : Strategy :=
  Strategy.ofScript (honestCommitOpening μ R q claims >>= fun _ ↦ Script.ret ()) 0

/-- The honest prover of `openingProgram` follows it to `true`. -/
theorem follows_openingProgram {μ R : ℕ} (hadm : Whir.Admissible μ R) (q : Column μ)
    (claims : List StackClaim) (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q)
    (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) :
    Follows (fun _ _ b ↦ b = true) (honestCommitOpening μ R q claims >>= fun _ ↦ Script.ret ())
      (openingProgram μ R claims) [] := by
  have h := follows_commitStack_verifyStackedOpening hadm q claims hholds hml
  have : openingProgram μ R claims =
      (do commitStack μ R; verifyStackedOpening μ R claims) >>= fun _ ↦ Prog.ret true := by
    simp only [openingProgram, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc]
  rw [this]
  exact Follows.bind_of h fun _ _ _ _ ↦ rfl

/-- **The opening is interactively perfectly complete**: the honest prover wins every
interactive run of `openingProgram` and commits well-shaped words. -/
theorem runI_openingProgram {μ R : ℕ} (hadm : Whir.Admissible μ R) (q : Column μ)
    (claims : List StackClaim) (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q)
    (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) (chal : List Ev → E) :
    runI (openingProgram μ R claims) (openingProver μ R q claims) chal = some true ∧
      shapedI (openingProgram μ R claims) (openingProver μ R q claims) chal := by
  obtain ⟨⟨b, hb, _, _, rfl⟩, hsh⟩ := runFrom_of_follows' (h₀ := []) (openingProver μ R q claims)
    chal (ofScript_agrees _ []) (follows_openingProgram hadm q claims hholds hml)
  exact ⟨hb, hsh⟩

/-- **Completeness of the compiled opening.** For every hash function, the honest compiled
prover of `openingProgram` produces a proof the compiled verifier accepts, as soon as every
proof-of-work search finds its nonce below `fuel`. -/
theorem exists_prove_runProof_openingProgram (H : Bytes → Digest) {μ R : ℕ}
    (hadm : Whir.Admissible μ R) (q : Column μ) (claims : List StackClaim)
    (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q) (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1)
    (seed : Digest) (fuel : ℕ)
    (hg : ∀ h bits k cv, (openingProgram μ R claims).after h = some (.grind bits k) →
      findNonce H bits cv fuel ≠ none) :
    ∃ π, prove H (openingProgram μ R claims) (openingProver μ R q claims) seed fuel = some π ∧
      runProof (m := Id) H (openingProgram μ R claims) seed π = true :=
  exists_prove_runProof H _ _ seed fuel
    (fun chal ↦ (runI_openingProgram hadm q claims hholds hml chal).1)
    (fun chal ↦ (runI_openingProgram hadm q claims hholds hml chal).2) hg

end
end LeanVM.Protocol.Whir.Complete
