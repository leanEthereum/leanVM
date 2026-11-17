module

public import Common.MultiKey.TwoCache

@[expose] public section

/-!
# The reduction to one key

Against `k` keys, the reduction for key `i` (`reduction`) is an adversary of the single-key
random-oracle game: it receives key `i`'s public key, generates the other `k - 1` keys itself with
a private random oracle sampled with coins (`setup`, the private oracle's queries tagged `true`),
recording each one's key-generation queries (`loggedKeygen`); it runs the multi-key adversary
(`advImpl`), answering a request to key `i` by its own signing oracle, a request to another key by
that key's signer over the private oracle, and a hash query `x` by the private oracle when `x` is
another key's (`groute`: one of its key-generation queries, or publicly owned by it and not by key
`i`), else by the real oracle; it outputs the adversary's forgery.

`taggedGame` is the single-key game against the reduction, with the private oracle's queries left
as queries tagged `true` and the real oracle's tagged `false`; in the two-oracle world it is the
single-key game (`prob_taggedGame_eq`), forgetting the tags it is the multi-key game with key `i`
generated first (`Common.MultiKey.KeyPhase`).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig.OverPermutation (sequenceFin)

namespace Common.SufCma.MultiKey

variable {Seed PK SK Req Resp F : Type}

/-! ## Logged key generation, the tagged oracles -/

/-- A key's record: its key pair and the inputs its key generation queried, in order. -/
abbrev KeyRec (PK SK : Type) := (PK × SK) × List (List UInt8)

/-- Each hash query logs its input. -/
def logImpl : QueryImpl SchemeHashSpec (WriterT (List (List UInt8)) (OracleComp SchemeHashSpec)) :=
  fun x ↦ do
    tell [x]
    liftM (SchemeHashSpec.query x)

/-- **Key generation with its queries logged.** -/
def loggedKeygen (S : SchemeWithHash Seed PK SK Req Resp F) (seed : Seed) :
    OracleComp SchemeHashSpec (KeyRec PK SK) :=
  (simulateQ logImpl (S.keygen seed)).run

/-- The hash as the real oracle (`false`). -/
def tagF : QueryImpl SchemeHashSpec (OracleComp TSpec) :=
  fun x ↦ liftM (TSpec.query (.inr (false, x)))

/-- The hash as the private oracle (`true`). -/
def tagG : QueryImpl SchemeHashSpec (OracleComp TSpec) :=
  fun x ↦ liftM (TSpec.query (.inr (true, x)))

/-- Coins. -/
def coinsT : QueryImpl unifSpec (OracleComp TSpec) :=
  fun n ↦ liftM (TSpec.query (.inl n))

/-- The tagged oracles inside a computation that also makes requests. -/
def toTR : QueryImpl TSpec (OracleComp (TSpec + (Req →ₒ Resp))) :=
  fun t ↦ liftM ((TSpec + (Req →ₒ Resp)).query (.inl t))

/-! ## The reduction -/

variable (S : SchemeWithHash Seed PK SK Req Resp F) {k : ℕ}

/-- **The other keys**: for each `j ≠ i`, a fresh seed and its key generation over the private
oracle, logged; nothing at `i`. -/
def setup (i : Fin k) : OracleComp TSpec (Fin k → Option (KeyRec PK SK)) :=
  sequenceFin fun j ↦ if j = i then pure none else do
    let s ← simulateQ coinsT S.sample
    some <$> simulateQ tagG (loggedKeygen S s)

/-- The public keys the adversary sees: key `i`'s, and the others'. -/
def pksOf (pk : PK) (others : Fin k → Option (KeyRec PK SK)) (j : Fin k) : PK :=
  match others j with
  | some z => z.1.1
  | none => pk

variable (ownedPub : PK → List UInt8 → Prop) [∀ pk, DecidablePred (ownedPub pk)]

/-- **The routing**: `x` goes to the private oracle when some other key queried it at key
generation, or owns it publicly while key `i` (public key `pk`) does not. -/
def groute (pk : PK) (others : Fin k → Option (KeyRec PK SK)) (x : List UInt8) : Bool :=
  (List.finRange k).any fun j ↦ match others j with
    | some z => decide (x ∈ z.2) || (decide (ownedPub z.1.1 x) && !decide (ownedPub pk x))
    | none => false

theorem groute_iff (pk : PK) (others : Fin k → Option (KeyRec PK SK)) (x : List UInt8) :
    groute ownedPub pk others x = true ↔
      ∃ j z, others j = some z ∧ (x ∈ z.2 ∨ (ownedPub z.1.1 x ∧ ¬ownedPub pk x)) := by
  simp only [groute, List.any_eq_true, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj⟩
    rcases h : others j with _ | z
    · rw [h] at hj; cases hj
    · rw [h] at hj
      exact ⟨j, z, h, by simpa using hj⟩
  · rintro ⟨j, z, hz, hx⟩
    refine ⟨j, ?_⟩
    rw [hz]
    simpa using hx

/-- **The multi-key adversary inside the reduction**: coins forwarded; a hash query to the oracle
the routing picks; a request to key `i` forwarded, to another key answered by its signer over the
private oracle. -/
def advImpl (i : Fin k) (pk : PK) (others : Fin k → Option (KeyRec PK SK)) :
    QueryImpl (World + (Fin k × Req →ₒ Resp)) (OracleComp (TSpec + (Req →ₒ Resp)))
  | .inl (.inl n) => liftM ((TSpec + (Req →ₒ Resp)).query (.inl (.inl n)))
  | .inl (.inr x) => liftM ((TSpec + (Req →ₒ Resp)).query
      (.inl (.inr (groute ownedPub pk others x, x))))
  | .inr r => if r.1 = i then liftM ((TSpec + (Req →ₒ Resp)).query (.inr r.2)) else
      match others r.1 with
      | some z => simulateQ toTR (simulateQ tagG (S.sign z.1.2 r.2))
      | none => liftM ((TSpec + (Req →ₒ Resp)).query (.inr r.2))

/-- **The reduction with its private oracle as tagged queries**: the other keys, then the
adversary; its forgery and the other keys' records. -/
def reductionT (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) (pk : PK) :
    OracleComp (TSpec + (Req →ₒ Resp)) ((Fin k × F) × (Fin k → Option (KeyRec PK SK))) := do
  let others ← simulateQ toTR (setup S i)
  let r ← simulateQ (advImpl S ownedPub i pk others) (A (pksOf pk others))
  return (r, others)

/-- `World` computations inside a computation that also makes requests. -/
def toWR : QueryImpl World (OracleComp (World + (Req →ₒ Resp))) :=
  fun t ↦ liftM ((World + (Req →ₒ Resp)).query (.inl t))

/-- The private oracle sampled inside, requests forwarded. -/
noncomputable def innerR :
    QueryImpl (TSpec + (Req →ₒ Resp))
      (StateT SchemeHashSpec.QueryCache (OracleComp (World + (Req →ₒ Resp))))
  | .inl t => StateT.mk fun c ↦ simulateQ toWR ((inner t).run c)
  | .inr r => StateT.lift (liftM ((World + (Req →ₒ Resp)).query (.inr r)))

/-- **The reduction for key `i`**: an adversary of the single-key random-oracle game. -/
noncomputable def reduction (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    PK → OracleComp (World + (Req →ₒ Resp)) F :=
  fun pk ↦ (fun r ↦ r.1.2) <$> (simulateQ innerR (reductionT S ownedPub i A pk)).run' ∅

/-! ## The tagged game -/

/-- Key `i`'s signer over the real oracle, logged. -/
def signT (sk : SK) :
    QueryImpl (Req →ₒ Resp) (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp TSpec)) :=
  QueryImpl.withLogging fun r ↦ simulateQ tagF (S.sign sk r)

/-- The tagged game's oracles: the tagged oracles forwarded, key `i`'s signer logging. -/
abbrev gameOraclesT (sk : SK) :=
  QueryImpl.ofLift TSpec (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp TSpec)) + signT S sk

/-- **The single-key game against the reduction, tagged**: key `i` generated over the real
oracle (logged), the reduction with its signing oracle, the forgery verified over the real
oracle; the forgery's index and the win, key `i`'s record and the others'. -/
def taggedGame (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    OracleComp TSpec ((Fin k × Bool) × KeyRec PK SK × (Fin k → Option (KeyRec PK SK))) := do
  let s ← simulateQ coinsT S.sample
  let zi ← simulateQ tagF (loggedKeygen S s)
  let p ← (simulateQ (gameOraclesT S zi.1.2) (reductionT S ownedPub i A zi.1.1)).run
  let b ← simulateQ tagF (S.verify zi.1.1 p.1.1.2)
  return ((p.1.1.1, S.win p.2 p.1.1.2 && b), zi, p.1.2)

end Common.SufCma.MultiKey
