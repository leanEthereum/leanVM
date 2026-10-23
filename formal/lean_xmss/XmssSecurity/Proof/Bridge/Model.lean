import XmssSecurity.Proof.Bridge.Seed
import XmssSecurity.Proof.Bridge.Reference
import XmssSecurity.Proof.Bridge.Keygen

/-!
# From the clean table game to the model

The randomizer table is independent of key generation. For each key, memoizing the adversary and
drawing the table lazily turns the table signer into the model's signer, and the key distribution is
the model's: the clean table game is at most the model's game against the memoized adversary, and the
real budget bounds the model's calls after key generation.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-- The model's adversary: the statement's, translated and memoized. -/
noncomputable def modelAdversary (adversary : LeanXmss.Security.Adversary) : Adversary :=
  memoAdversary (toModelAdversary adversary)

/-- The clean game with the model's signer. -/
noncomputable def refGame (adversary : LeanXmss.Security.Adversary) : ProbComp Bool := do
  let d ← drawDerivations
  let p ← (simulateQ randomOracle (honestRun d).withQueryLog).run ∅
  (simulateQ romImpl (Seeded.gameRest Concrete.scheme (modelAdversary adversary)
    (modelPublicKey d p.1) (modelSecretKey d p.1))).run' p.2

/-- The table with another randomizer table. -/
def Derivations.withRnd (d : Derivations) (rnd : RandomizerOutputs) : Derivations := { d with rnd := rnd }

private theorem prob_bind_mono {α : Type} {mx : ProbComp α} {f g : α → ProbComp Bool}
    (h : ∀ a ∈ support mx, Pr{let x ← f a}[x = true] ≤ Pr{let x ← g a}[x = true]) :
    Pr{let x ← mx >>= f}[x = true] ≤ Pr{let x ← mx >>= g}[x = true] :=
  prEvent_bind_mono_of_forall_le_of_support mx f g _ _ h

theorem cleanGame_le_ref (adversary : LeanXmss.Security.Adversary) :
    Pr{let x ← cleanGame adversary}[x = true] ≤ Pr{let x ← refGame adversary}[x = true] := by
  unfold cleanGame refGame drawDerivations modelAdversary
  simp only [bind_assoc, pure_bind, honestRun, modelSecretKey, modelPublicKey, Derivations.parameter,
    Derivations.topBase, secret_eq, topSecret_eq]
  refine prob_bind_mono fun param _ => prob_bind_mono fun bottom _ =>
    prob_bind_mono fun top _ => ?_
  conv_rhs => rw [(evalDist_drop_randomizers _).prEvent_eq (· = true)]
  conv_lhs => rw [(OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq (· = true)]
  refine prob_bind_mono fun topRnd _ => ?_
  rw [(OracleComp.EvalDistEq.bind_bind_swap _ _ _).prEvent_eq (· = true)]
  refine prob_bind_mono fun p _ => ?_
  calc _ ≤ Pr{let x ← (sampleRandomizerOutputs >>= fun rnd => (simulateQ romImpl (Seeded.gameRest
        (tableScheme rnd) (memoAdversary (toModelAdversary adversary)) ⟨p.1.1.1, truncateHash param⟩
          (Concrete.precomputedSecretKey (truncateHash param) (pairEquiv LeafIndex bottom)
            (pairEquiv TopIndex top) p.1.1.2 (hashCacheOfLog p.1.2)))).run' p.2)}[x = true] :=
        prob_bind_mono fun rnd _ => prob_table_le_memo _ _ _ _ _
    _ = _ := (evalDist_table_memo _ _ _ _).prEvent_eq (· = true)

theorem refGame_eq (adversary : LeanXmss.Security.Adversary) :
    Pr{let x ← refGame adversary}[x = true] = forgeAdvantage Concrete.scheme (modelAdversary adversary) := by
  unfold refGame forgeAdvantage gameCore
  refine ((evalDist_keygen (fun pk sk cache => (simulateQ romImpl (Seeded.gameRest Concrete.scheme
    (modelAdversary adversary) pk sk)).run' cache)).prEvent_eq (· = true)).trans
      (congrArg (fun mx : ProbComp Bool => Pr{let x ← mx}[x = true]) ?_)
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-! ## Budget -/

theorem mem_support_keygen {key : (PublicKey × XmssSecurity.SecretKey) × QueryCache HashSpec}
    (hkey : key ∈ support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅)) :
    ∃ d p, p ∈ support ((simulateQ randomOracle (honestRun d).withQueryLog).run ∅) ∧
      key = ((modelPublicKey d p.1, modelSecretKey d p.1), p.2) := by
  have h := evalDist_keygen (fun pk sk cache => (pure ((pk, sk), cache) :
    ProbComp ((PublicKey × XmssSecurity.SecretKey) × QueryCache HashSpec)))
  have hmem : key ∈ support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅ >>= fun k =>
      (pure ((k.1.1, k.1.2), k.2) : ProbComp ((PublicKey × XmssSecurity.SecretKey) × QueryCache HashSpec))) := by
    rw [mem_support_bind_iff]
    exact ⟨key, hkey, by simp⟩
  rw [← OracleComp.support_eq_of_evalDistEq h, mem_support_bind_iff] at hmem
  obtain ⟨d, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨p, hp, hmem⟩ := hmem
  exact ⟨d, p, hp, by simpa using hmem⟩

theorem afterKeygenBudget (adversary : LeanXmss.Security.Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (hbound : SeededBudget adversary q) :
    HasAfterKeygenHashQueryBound Concrete.scheme (modelAdversary adversary) (q - keygenQueries) := by
  intro key hkey result hresult
  obtain ⟨d, p, hp, rfl⟩ := mem_support_keygen hkey
  have hrnd : ∀ rnd, HashQueryBound (Seeded.gameRest (tableScheme rnd) (toModelAdversary adversary)
      (modelPublicKey d p.1) (modelSecretKey d p.1)) p.2 (q - keygenQueries) := fun rnd =>
    (cleanBudget adversary q hq hbound (d.withRnd rnd) hp).2
  have h := hashQueryBound_reference (toModelAdversary adversary) _ _ p.2 _ fun rnd =>
    hashQueryBound_table_memo _ rnd _ _ p.2 _ (hrnd rnd)
  apply h result
  rw [← simulateQ_countHashQueries] at hresult
  exact hresult

end XmssSecurity.Bridge
