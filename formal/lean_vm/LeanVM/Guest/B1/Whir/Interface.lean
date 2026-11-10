/-
  LeanVM.Guest.B1.Whir.Interface

  The interface of `open_stacked` (B1-b): the Spec's stacked WHIR opening split at the terminal
  the guest checks elsewhere, what a call of each of the 14 specializations establishes about it,
  and the statement that every specialization's core IR establishes it.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Common.Sponge
public import LeanVM.Protocol.Compile.Prog

/-!
# `open_stacked` (TRIAGE G #42): the interface

`open_stacked(m_idx, fs0..fs4, target, commit_root_0, commit_root_1, cursor)`
(`crates/rec_aggregation/guests/lean_ethereum.py:1430-1762` at leanVM `40f877dc`, G below) runs
the stacked WHIR opening of one child's proof, `verifyWhir` (`Statement/LeanVmVerifier.lean`, V:1836;
`crates/verifier/src/whir.rs:142-265`) from `verifyStackedOpening` (V:1854), up to its terminal:
the terminal's check `(inner + evaluateBasis point) · residual = target` is
`check_opening_terminal`'s, which evaluates the transparent weight `evaluateBasis`. It has 14
specializations `open_stacked__L{m}`, one per stack log `μ = 19 + m ≤ 32`, each reading its size's
rows of the `LIG_*` tables at compile time; the rate `1 ≤ r ≤ 4` is its first argument
`rateSel r = g^(r - 1)`, which each level's `match` on the rate dispatches into helpers
specialized on the rate's shapes.

* `WhirEnd`, `whirLevelsOpen`, `whirOpen`: `whirLevels` and `verifyWhir` without the final
  `require`, returning what the terminal reads; `WhirEnd.Accepts` the terminal's check;
  `verifyWhir_split`: `verifyWhir` is `whirOpen` then `require Accepts` (proved here).
* `stackShape μ r`: the shape `commitStack` gives the stack's root (`commitStack_eq`, proved).
* `RunsWith p s xs os roots a s' roots'`: `RunsTo` (`B1/Common/Sponge.lean`) with the openings
  `os` read and the commitments `roots` growing to `roots'`, on any rest of the stream and of the
  openings.
* `OpenOut rd μ r root fs target cur rets`: what a call establishes: from the sponge the guest
  carries as the capacity `fs` with nothing waiting, the stack's root committed with its shape,
  the stream words at the cursor and some openings run `whirOpen μ r target` to `w`; the call
  returns `w`'s claim, two buffers holding `w`'s point (`μ` coordinates, witness order) and its
  coordinates plus one, zero-padded (one-padded) to `pointCap = 40`, `w`'s glued weight and its
  residual's value.
* `open_stacked_sound_Spec`: every specialization's call relation at `rateSel r` gives `OpenOut`,
  on a memory image of at most `2^32` words (the query windows' range checks,
  `decode_query_windows`).

The guest's completeness statement (an honest run with no zero fold, tail or batching challenge,
on a memory holding the hinted caps and rows, gives the call relation; DESIGN §5.2.1) follows the
soundness proof, its memory predicate named by the body's buffers.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The opening up to its terminal (V:1791-1842) -/

/-- What the stacked opening leaves for its terminal: the point in witness order, the glued
claims' weight there, the residual's value at the tail challenges, and the running claim. -/
structure WhirEnd where
  /-- The terminal point, rotated into witness order (`point.drop laneFolds ++ point.take …`). -/
  point : List E
  /-- `Σ scalar · weightAt` over the glued claims. -/
  inner : E
  /-- `multilinearEval residual tailFolds`. -/
  residual : E
  /-- The final running claim. -/
  target : E

/-- `whirLevels` (V:1791) without the final `require`: it returns what the terminal reads. -/
def whirLevelsOpen (logN laneFolds : ℕ) : ℕ → List Whir.Level → WhirStateT → VerifierProgram WhirEnd
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRoundsT level.foldGrinding level.fold s []
    let messageLog := logN - s.folds.length
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← VerifierProgram.readScalars (2 ^ messageLog)
        pure (residual, ([] : List (E × List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        VerifierProgram.readCommitment height width
        let oodPoint ← VerifierProgram.sampleChallenges messageLog
        let oodValue ← VerifierProgram.readScalar
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])
    VerifierProgram.grindProofOfWork Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← VerifierProgram.sampleChallenge
    let queryWeights := powers lam queries.length
    let words ← VerifierProgram.queryOpenings index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++
      [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glueT lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRoundsT messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let inner := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds)) 0
      return ⟨point.drop laneFolds ++ point.take laneFolds, inner,
        multilinearEval residual tailFolds, target⟩
    | _ :: _ => whirLevelsOpen logN laneFolds (index + 1) rest s

/-- `verifyWhir` (V:1836) up to its terminal: what `open_stacked` runs. -/
def whirOpen (logN logInvRate : ℕ) (target : E) : VerifierProgram WhirEnd := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsOpen logN ((config.head?.map (·.fold)).getD 0) 0 config ⟨target, quad, [], []⟩

/-- The terminal's check: the weight at the point times the residual's value is the claim. -/
def WhirEnd.Accepts (w : WhirEnd) (evaluateBasis : List E → E) : Prop :=
  (w.inner + evaluateBasis w.point) * w.residual = w.target

instance (w : WhirEnd) (evaluateBasis : List E → E) : Decidable (w.Accepts evaluateBasis) :=
  inferInstanceAs (Decidable (_ = _))

theorem foldl_add_shift {α : Type} (f : α → E) (a : E) (l : List α) :
    l.foldl (fun w c ↦ w + f c) a = a + l.foldl (fun w c ↦ w + f c) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + f x), zero_add, add_assoc]

theorem prog_bind_congr {α β : Type} {p : VerifierProgram α} {f g : α → VerifierProgram β} (h : ∀ a,
    f a = g a) :
    p.bind f = p.bind g := by rw [funext h]

theorem whirLevels_split (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirStateT),
      whirLevelsT logN laneFolds eb index levels s =
        (whirLevelsOpen logN laneFolds index levels s).bind fun w ↦ VerifierProgram.require
            (w.Accepts eb)
  | _, [], _ => rfl
  | index, [level], s => by
    rw [whirLevelsT, whirLevelsOpen]
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
        VerifierProgram.ret_bind, WhirEnd.Accepts]
    repeat refine prog_bind_congr fun _ ↦ ?_
    rw [foldl_add_shift _ (eb _), add_comm (eb _)]
    congr 1
  | index, level :: next :: rest, s => by
    rw [whirLevelsT, whirLevelsOpen]
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
        VerifierProgram.ret_bind,
      whirLevels_split logN laneFolds eb (index + 1) (next :: rest)]

/-- **`verifyWhir` is `whirOpen`, then the terminal's check.** -/
theorem verifyWhir_split (logN logInvRate : ℕ) (target : E) (eb : List E → E) :
    verifyWhirT logN logInvRate target eb = (do
      let w ← whirOpen logN logInvRate target
      VerifierProgram.require (w.Accepts eb)) := by
  simp only [verifyWhirT, whirOpen, VerifierProgram.bind_eq, VerifierProgram.bind_assoc,
      whirLevels_split]

/-- The shape `commitStack` gives the stack's root (V:1844): `(height, width)`. -/
def stackShape (logN logInvRate : ℕ) : ℕ × ℕ :=
  match Whir.ladder logN logInvRate with
  | some (level :: _) => levelShape logN level (2 ^ level.fold)
  | _ => (0, 0)

/-- **`commitStack` commits the stack's shape**, when the configuration has a level. -/
theorem commitStack_eq {logN logInvRate : ℕ} {level : Whir.Level} {rest : List Whir.Level}
    (h : Whir.ladder logN logInvRate = some (level :: rest)) :
    commitStack logN logInvRate =
      VerifierProgram.readCommitment (stackShape logN logInvRate).1 (stackShape logN
          logInvRate).2 := by
  simp only [commitStack, stackShape, h, VerifierProgram.bind_eq]
  rfl

/-! ## The specializations -/

/-- `open_stacked`'s 14 specializations, in dispatch order. -/
def openNames : List String :=
  (List.range 14).map fun m ↦ "open_stacked__L" ++ toString m

/-- The smallest stack log a child's opening takes (`verifier::MIN_EXECUTION_STACKED_LOG`). -/
abbrev minOpenLog : ℕ := 19

/-- The specialization of `open_stacked` for the stack log `μ`: `μ - 19` in dispatch order. -/
def openName (μ : ℕ) : String := openNames.getD (μ - minOpenLog) ""

/-- The rate's selector, `open_stacked`'s first argument: `g^(r - 1)`. -/
def rateSel (r : ℕ) : E := ofK (addressOfIndex (r - 1))

/-- The length of the point buffers, `SIZE_BITS + QKECCAK_SLOT_LOG` (G:1672-1673). -/
abbrev pointCap : ℕ := 40

/-! ## Runs with openings and commitments -/

/-- From any Spec sponge the guest carries as `s`, the program `p` reads exactly the stream words
`xs` and the phases of openings `os`, the commitments read so far being `roots`, and returns `a`,
leaving a sponge the guest carries as `s'` and the commitments `roots'`, on any rest of the stream
and of the phases. -/
def RunsWith {α : Type} (p : VerifierProgram α) (s : Fs) (xs : List E) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)) (a : α) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)) : Prop :=
  ∀ sp : Sponge, s.Carries sp → ∀ (rest : List E) (orest : List (List Opening)),
    ∃ sp' : Sponge, s'.Carries sp' ∧ runId p ⟨sp, xs ++ rest, os ++ orest, roots⟩ = some (a, ⟨sp', rest, orest, roots'⟩)

/-! ## What a call establishes -/

/-- **`open_stacked__L{μ - 19}(rateSel r, fs0..fs4, target, root_0, root_1, cursor)`**: from the sponge the guest carries as the capacity `fs` with nothing waiting (the
batching challenge of `verifyStackedOpening` was just squeezed, G:3467), the stack's root `root`
committed with its shape and nothing else, the words `xs` at the cursor and some openings `os`
run `whirOpen μ r target` to `w`; the function returns `w`'s claim, a buffer holding its point
(`μ` coordinates, zero-padded to `pointCap`), a buffer holding one plus each of them (one-padded),
its glued weight and its residual's value. -/
def OpenOut (rd : Reader) (μ r : ℕ) (root : Digest) (fs : List E) (target cur : E)
    (rets : List E) : Prop :=
  ∃ (xs : List E) (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
    ReadsAt rd cur xs ∧
    RunsWith (whirOpen μ r target) ⟨fs, []⟩ xs os [(root, stackShape μ r)] w s' roots' ∧
    w.point.length = μ ∧
    ∃ pt pt1 : E, rets = [w.target, pt, pt1, w.inner, w.residual] ∧
      ReadsAt rd pt (w.point ++ List.replicate (pointCap - μ) 0) ∧
      ReadsAt rd pt1 (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)

/-- **`open_stacked` is sound** at every stack log and rate: a call of the specialization of `μ`
on the rate's selector, the capacity cells `fs`, the claim `target`, the root's two cells and the
cursor establishes `OpenOut`, on a memory image of at most `2^32` words (`decode_query_windows`'
range checks). -/
def open_stacked_sound_Spec : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → ∀ (L : MemoryImage κ) (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 32 → 1 ≤ r → r ≤ 4 →
    ∀ (root : Digest) (fs : List E) (target root0 root1 cur : E) (rets : List E),
      fs.length = 5 → (root0, root1) = digestHalves root →
      coreProgram.Rel L.read (openName μ) (rateSel r :: fs ++ [target, root0, root1, cur]) rets →
        OpenOut L.read μ r root fs target cur rets

end
end LeanVM.Guest.B1.Whir
