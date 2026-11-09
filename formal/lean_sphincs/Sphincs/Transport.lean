module

public import Common.WithHashBridge

@[expose] public section

/-!
# A SUF-CMA game through maps of the keys, the answers and the forgeries

A scheme of the statement (`Common.SufCma.Scheme`, over `π`) whose algorithms are a hash-query
scheme's (`Common.SufCma.SchemeWithHash`) with each query answered by Keccak-256 over `π`, through
maps of the keys, the signing answers and the forgeries, has the hash-query scheme's game, adversary
by adversary (`forgeryGame_eq`: the adversary against the statement's scheme, its public key, its
signing answers and its forgery read through the maps, is one against the hash-query scheme).
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace Sphincs.Transport

variable {Seed PK₁ PK₂ SK₁ SK₂ Req Resp₁ Resp₂ F₁ F₂ : Type}

local notation "σ" => schemeHashOverPermutation

/-- A signing log, every answer read through `φ`. -/
def mapLog (φ : Resp₁ → Resp₂) (log : QueryLog (Req →ₒ Resp₁)) : QueryLog (Req →ₒ Resp₂) :=
  log.map fun entry ↦ ⟨entry.1, φ entry.2⟩

theorem mapLog_length (φ : Resp₁ → Resp₂) (log : QueryLog (Req →ₒ Resp₁)) :
    (mapLog φ log).length = log.length :=
  List.length_map _

theorem mem_mapLog {φ : Resp₁ → Resp₂} {log : QueryLog (Req →ₒ Resp₁)}
    {entry : (t : (Req →ₒ Resp₂).Domain) × (Req →ₒ Resp₂).Range t} :
    entry ∈ mapLog φ log ↔ ∃ original ∈ log, (⟨original.1, φ original.2⟩ :
      (t : (Req →ₒ Resp₂).Domain) × (Req →ₒ Resp₂).Range t) = entry :=
  List.mem_map

/-- An adversary's oracles against a scheme answering `Resp₂`, from those of one answering `Resp₁`:
the permutation's queries forwarded, the signing oracle's answers read through `φ`. -/
def mapAnswers (φ : Resp₁ → Resp₂) :
    QueryImpl (RandomPermutationOracles + (Req →ₒ Resp₂))
      (OracleComp (RandomPermutationOracles + (Req →ₒ Resp₁)))
  | .inl t => liftM ((RandomPermutationOracles + (Req →ₒ Resp₁)).query (.inl t))
  | .inr r => φ <$> liftM ((RandomPermutationOracles + (Req →ₒ Resp₁)).query (.inr r))

/-- The statement's game's oracles: the permutation's queries lifted, the signing oracle logging. -/
abbrev statementGameImpl (S : Scheme Seed PK₂ SK₂ Req Resp₂ F₂) (sk : SK₂) :=
  QueryImpl.ofLift RandomPermutationOracles
      (WriterT (QueryLog (Req →ₒ Resp₂)) (OracleComp RandomPermutationOracles)) +
    QueryImpl.withLogging (spec := Req →ₒ Resp₂) (S.sign sk)

/-- The hash-query game's oracles. -/
abbrev hashGameImpl (S : SchemeWithHash Seed PK₁ SK₁ Req Resp₁ F₁) (sk : SK₁) :=
  QueryImpl.ofLift RandomPermutationOracles
      (WriterT (QueryLog (Req →ₒ Resp₁)) (OracleComp RandomPermutationOracles)) +
    loggedSigningOracleWithHash S sk

/-- **The adversary's run, through the map**: run against the statement's scheme with the key
`skMap sk`, an adversary's run is its run against the hash-query scheme with the key `sk`, the
signing answers read through `φ`, the log read through `φ`. -/
theorem run_gameImpl (S₁ : SchemeWithHash Seed PK₁ SK₁ Req Resp₁ F₁)
    (S₂ : Scheme Seed PK₂ SK₂ Req Resp₂ F₂) (skMap : SK₁ → SK₂) (φ : Resp₁ → Resp₂)
    (hsign : ∀ sk r, S₂.sign (skMap sk) r = φ <$> simulateQ σ (S₁.sign sk r)) (sk : SK₁)
    {α : Type} (oa : OracleComp (RandomPermutationOracles + (Req →ₒ Resp₂)) α) :
    (simulateQ (statementGameImpl S₂ (skMap sk)) oa).run =
      (fun z ↦ (z.1, mapLog φ z.2)) <$>
        (simulateQ (hashGameImpl S₁ sk) (simulateQ (mapAnswers φ) oa)).run := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [mapLog]
  | query_bind t k ih =>
    rcases t with t | r
    · have h₂ : (statementGameImpl S₂ (skMap sk) (.inl t)).run =
          (·, ∅) <$> (liftM (RandomPermutationOracles.query t) :
            OracleComp RandomPermutationOracles _) := rfl
      have h₁ : (simulateQ (hashGameImpl S₁ sk) (mapAnswers φ (.inl t))).run =
          (·, ∅) <$> (liftM (RandomPermutationOracles.query t) :
            OracleComp RandomPermutationOracles _) := by
        simp only [mapAnswers, simulateQ_spec_query]
        rfl
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, WriterT.run_bind', h₂, h₁, ih, bind_map_left, map_bind,
        Functor.map_map]
      refine bind_congr fun u ↦ ?_
      congr 1
    · have h₂ : (statementGameImpl S₂ (skMap sk) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
          S₂.sign (skMap sk) r := by
        simp [statementGameImpl]
      have h₁ : (simulateQ (hashGameImpl S₁ sk) (mapAnswers φ (.inr r))).run =
          (fun u ↦ (φ u, [⟨r, u⟩])) <$> simulateQ σ (S₁.sign sk r) := by
        have hs : (hashGameImpl S₁ sk (.inr r)).run =
            (fun u ↦ (u, [⟨r, u⟩])) <$> simulateQ σ (S₁.sign sk r) := by
          simp [hashGameImpl, loggedSigningOracleWithHash]
        simp only [mapAnswers, simulateQ_map, simulateQ_spec_query, WriterT.run_map']
        rw [hs, Functor.map_map]
        rfl
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, WriterT.run_bind', h₂, h₁, hsign, ih,
        bind_map_left, map_bind, Functor.map_map]
      refine bind_congr fun u ↦ ?_
      congr 1

/-- The adversary against the hash-query scheme that runs `main` against the statement's: the
public key read through `pkMap`, the signing answers through `φ`, the forgery through `ψ`. -/
def mapAdversary (pkMap : PK₁ → PK₂) (φ : Resp₁ → Resp₂) (ψ : F₂ → F₁)
    (main : PK₂ → OracleComp (RandomPermutationOracles + (Req →ₒ Resp₂)) F₂) (pk : PK₁) :
    OracleComp (RandomPermutationOracles + (Req →ₒ Resp₁)) F₁ :=
  ψ <$> simulateQ (mapAnswers φ) (main (pkMap pk))

/-- **The same game**: when the statement's scheme samples as the hash-query scheme, generates the
keys as it does through `pkMap` and `skMap`, signs with `skMap sk` as it signs with `sk` through
`φ`, verifies a forgery under `pkMap pk` as it verifies the forgery through `ψ` under `pk`, and
wins on a log read through `φ` as it wins on the log with the forgery through `ψ`, the statement's
game against `main` is the hash-query game against `mapAdversary pkMap φ ψ main`. -/
theorem forgeryGame_eq (S₁ : SchemeWithHash Seed PK₁ SK₁ Req Resp₁ F₁)
    (S₂ : Scheme Seed PK₂ SK₂ Req Resp₂ F₂) (pkMap : PK₁ → PK₂) (skMap : SK₁ → SK₂)
    (φ : Resp₁ → Resp₂) (ψ : F₂ → F₁) (hsample : S₂.sampleSeed = S₁.sample)
    (hkeygen : ∀ seed, S₂.generateKeys seed =
      (fun keys ↦ (pkMap keys.1, skMap keys.2)) <$> simulateQ σ (S₁.keygen seed))
    (hsign : ∀ sk r, S₂.sign (skMap sk) r = φ <$> simulateQ σ (S₁.sign sk r))
    (hverify : ∀ pk f, S₂.verify (pkMap pk) f = simulateQ σ (S₁.verify pk (ψ f)))
    (hwin : ∀ log f, S₂.winningCondition (mapLog φ log) f = S₁.win log (ψ f))
    (main : PK₂ → OracleComp (RandomPermutationOracles + (Req →ₒ Resp₂)) F₂) :
    forgeryGame S₂ main = forgeryGameWithHash S₁ (mapAdversary pkMap φ ψ main) := by
  unfold forgeryGame forgeryGameWithHash mapAdversary
  rw [hsample]
  refine bind_congr fun seed ↦ ?_
  rw [hkeygen, bind_map_left]
  refine bind_congr fun keys ↦ ?_
  rcases keys with ⟨pk, sk⟩
  dsimp only
  have h := run_gameImpl S₁ S₂ skMap φ hsign sk (main (pkMap pk))
  simp only [statementGameImpl, hashGameImpl] at h
  rw [h, simulateQ_map, WriterT.run_map', bind_map_left, bind_map_left]
  refine bind_congr fun z ↦ ?_
  simp only [Prod.map, id, hverify, hwin]

end Sphincs.Transport
