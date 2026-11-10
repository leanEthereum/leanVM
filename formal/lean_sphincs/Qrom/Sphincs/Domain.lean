module

public import FORS.Classification.Accepted
public import Qrom.Assembly

@[expose] public section

/-!
# The hash on a finite domain

The quantum random oracle is a function on a finite set: the byte strings of length at most
`maxLen` (`Qrom.Sphincs.Input`), which holds every input that key generation, the signer and the
verifier of leanSPHINCS hash. A hash computation of the scheme runs on such a function `f` by
answering a longer input with zero (`Qrom.Sphincs.extend`, `Qrom.Sphincs.liftH`), and its run records
the inputs it reads (`Qrom.Sphincs.traced`).
-/

open OracleComp OracleSpec FORS

noncomputable section

namespace Qrom.Sphincs

/-- The longest hash input. -/
def maxLen : ℕ := 2048

/-- The lists of length at most `n` over a finite type are finitely many. -/
instance boundedListFintype (α : Type) [Fintype α] (n : ℕ) : Fintype {l : List α // l.length ≤ n} :=
  Fintype.ofEquiv (Σ k : Fin (n + 1), List.Vector α k)
    { toFun := fun v ↦ ⟨v.2.toList, by simpa using Nat.le_of_lt_succ v.1.2⟩
      invFun := fun x ↦ ⟨⟨x.1.length, Nat.lt_succ_of_le x.2⟩, ⟨x.1, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨k, hk⟩, l, hl⟩
        simp only at hl
        subst hl
        rfl
      right_inv := fun _ ↦ rfl }

/-- The byte strings of length at most `maxLen`. -/
abbrev Input := {l : HashInput // l.length ≤ maxLen}

/-- A byte string as an input, when it is short enough. -/
def embed (l : HashInput) : Option Input :=
  if h : l.length ≤ maxLen then some ⟨l, h⟩ else none

theorem embed_val (x : Input) : embed x.1 = some x := by
  simp [embed, x.2]

theorem val_of_embed {l : HashInput} {x : Input} (h : embed l = some x) : x.1 = l := by
  unfold embed at h
  split_ifs at h with hl
  cases h
  rfl

/-- A function on inputs, on every byte string: zero past `maxLen`. -/
def extend (f : Input → HashOutput) (l : HashInput) : HashOutput :=
  match embed l with
  | some x => f x
  | none => 0

theorem extend_val (f : Input → HashOutput) (x : Input) : extend f x.1 = f x := by
  simp [extend, embed_val]

/-- A hash query of the scheme, as a query to the finite oracle. -/
def liftImpl : QueryImpl HashSpec (OracleComp (Input →ₒ HashOutput)) := fun l ↦
  match embed l with
  | some x => (Input →ₒ HashOutput).query x
  | none => pure 0

/-- A hash computation of the scheme on the finite oracle. -/
def liftH {α : Type} (oa : OracleComp HashSpec α) : OracleComp (Input →ₒ HashOutput) α :=
  simulateQ liftImpl oa

theorem eval_liftH {α : Type} (f : Input → HashOutput) (oa : OracleComp HashSpec α) :
    evalWithAnswerFn (QueryImpl.ofFn f) (liftH oa) =
      evalWithAnswerFn (QueryImpl.ofFn (extend f)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [liftH, simulateQ_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, simulateQ_spec_query]
    have ht : evalWithAnswerFn (QueryImpl.ofFn f) (liftImpl t) = extend f t := by
      unfold liftImpl extend
      cases embed t with
      | none => rfl
      | some x => exact evalWithAnswerFn_liftM_query _ x
    rw [ht]
    exact ih _

/-- A hash computation that also returns the inputs it reads, in order. -/
def traced {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × List HashInput) :=
  OracleComp.construct (C := fun _ ↦ OracleComp HashSpec (α × List HashInput))
    (fun a ↦ pure (a, [])) (fun t _ next ↦ do
      let u ← liftM (HashSpec.query t)
      let r ← next u
      pure (r.1, t :: r.2)) oa

theorem eval_traced [Params] {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) :
    evalWithAnswerFn f (traced oa) = (evalWithAnswerFn f oa, Security.queriedInputs f oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [traced, construct_query_bind, Security.queriedInputs_query_bind, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, evalWithAnswerFn_bind]
    simp only [evalWithAnswerFn_pure]
    rw [← traced, ih, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]

end Qrom.Sphincs
