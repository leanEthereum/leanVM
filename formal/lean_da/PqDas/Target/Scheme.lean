/-
# The scheme: erasure code commitments from vector commitments and NARKs

The construction of an erasure code commitment from a vector commitment, a code
checker, and a non-interactive argument of knowledge, in the random-oracle
model. It follows the generic construction of Foundations of Data Availability
Sampling (eprint 2023/1079), Section 7, with one crucial difference: instead of
proving exact code membership of the committed vector inside the argument
system, the argument only proves that the vector passes the code checker on
randomness `l` derived from the commitment via a random oracle (Fiat-Shamir
outside the argument system).

Concretely, to commit to a message:
* encode it, `c := C.encode msg`;
* commit to the codeword, `comVC := vc.commit ckVC c`;
* derive the check randomness `l := H(comVC)` from the random oracle;
* prove knowledge of a `c` that (i) commits to `comVC` and (ii) passes
  `chk.check l c`, using the argument system;
* output `(comVC, π)`.

Openings are vector-commitment openings; verification checks the argument
proof (recomputing `l` from the oracle) and then the opening.

The random oracle hashes only `comVC`. Hashing additional context (such as the
commitment key) only helps in practice; hashing the commitment alone keeps the
oracle domains of this scheme and of the committed-soundness game (used in the
code-binding proof) identical, avoiding a query-translation step in the
reduction.

The construction is written generically over an ambient monad `m` providing
uniform sampling and the random oracle, following the conventions of VCVio's
`FiatShamir`. The random-oracle semantics is fixed by `roRuntime`: a fresh
lazily-sampled random oracle whose cache is threaded through the whole
experiment (adversary and scheme algorithms alike).

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import PqDas.Assumptions.ErasureCode
import PqDas.Assumptions.VectorCommitment
import PqDas.Assumptions.CodeChecker
import PqDas.Assumptions.Nark
import PqDas.Target.ErasureCodeCommitment
import PqDas.RomRuntime
import VCVio.CryptoFoundations.SignatureAlg

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

/-- The relation proven by the argument of knowledge. The statement is a
commitment key, a commitment, and check randomness; the witness is an alleged
codeword `c`. The relation holds if `c` commits to the given commitment and
passes the code check. Note that code membership of `c` is *not* part of the
relation; this is the whole point of the construction, and the reason the
code-binding proof is nontrivial. -/
def schemeRel [DecidableEq ComVC] (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) : CkVC × ComVC × L → (Fin n → Λ) → Bool := fun stmt c =>
  decide (vc.commit stmt.1 c = stmt.2.1) && chk.check stmt.2.2 c

/-- The erasure code commitment scheme built from an erasure code `C`, a vector
commitment `vc`, a code checker `chk`, and an argument of knowledge `ps` for
`schemeRel vc chk`, in any ambient monad `m` providing uniform sampling and a
random oracle from commitments to check randomness.

The commitment key is `(ckVC, crs)`, a commitment is `(comVC, π)`, and the
opening state is the codeword itself (valid since `vc.commit` is
deterministic). -/
def scheme {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    [HasQuery (ComVC →ₒ L) m] [DecidableEq ComVC]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk)) :
    ErasureCodeCommitment m Γ Λ k n (CkVC × Crs) (ComVC × Proof) (Fin n → Λ) Opn where
  setup := do
    let ckVC ← (monadLift vc.setup : m CkVC)
    let crs ← (monadLift ps.setup : m Crs)
    return (ckVC, crs)
  commit := fun ck msg => do
    let c := C.encode msg
    let comVC := vc.commit ck.1 c
    let l ← HasQuery.query (spec := (ComVC →ₒ L)) comVC
    let π := ps.prove ck.2 (ck.1, comVC, l) c
    return ((comVC, π), c)
  openAt := fun ck c i => pure (vc.openAt ck.1 c i)
  verify := fun ck com i x τ => do
    let l ← HasQuery.query (spec := (ComVC →ₒ L)) com.1
    return (ps.verify ck.2 (ck.1, com.1, l) com.2 && vc.verify ck.1 com.1 i x τ)

/-! ### Completeness -/

section completeness

variable [DecidableEq ComVC] [SampleableType L]
  (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
  (chk : CodeChecker Λ n L)
  (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))

/-- The completeness experiment of the scheme, with the random oracle
evaluated away: the honest execution queries the oracle only on `comVC`, first
in `commit` (a cache miss, answered by a fresh uniform `l`) and then in
`verify` (a cache hit, returning the same `l`). The result is a plain
probabilistic computation in which `l` is sampled uniformly once. -/
private lemma completeness_evalDist_eq (msg : Fin k → Γ) (i : Fin n) :
    (roRuntime ComVC L).evalDist (do
      let ck ← (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L))) C vc chk ps).setup
      let (com, st) ←
        (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L))) C vc chk ps).commit ck msg
      let τ ← (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L))) C vc chk ps).openAt ck st i
      (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L))) C vc chk ps).verify
        ck com i (C.encode msg i) τ) =
    𝒟[do
      let ckVC ← vc.setup
      let crs ← ps.setup
      let l ← $ᵗ L
      pure (ps.verify crs (ckVC, vc.commit ckVC (C.encode msg), l)
              (ps.prove crs (ckVC, vc.commit ckVC (C.encode msg), l) (C.encode msg)) &&
            vc.verify ckVC (vc.commit ckVC (C.encode msg)) i (C.encode msg i)
              (vc.openAt ckVC (C.encode msg) i))] := by
  let ro : QueryImpl (ComVC →ₒ L)
      (StateT ((ComVC →ₒ L).QueryCache) ProbComp) := randomOracle
  let impl := unifFwdImpl (ComVC →ₒ L) + ro
  have hSimQuery : ∀ (q : ComVC),
      simulateQ impl (HasQuery.query q) = ro q :=
    roSim.simulateQ_HasQuery_query ro
  have hpeel : ∀ {α β : Type} (oa : ProbComp α)
      (rest : α → StateT ((ComVC →ₒ L).QueryCache) ProbComp β)
      (s : (ComVC →ₒ L).QueryCache),
      (simulateQ impl (liftM oa) >>= rest).run' s =
        oa >>= fun x => (rest x).run' s :=
    fun oa rest s => roSim.run'_liftM_bind ro oa rest s
  have hro_miss : ∀ {β : Type} (q : ComVC)
      (rest : L → StateT ((ComVC →ₒ L).QueryCache) ProbComp β),
      (ro q >>= rest).run' ∅ =
        $ᵗ L >>= fun r =>
          (rest r).run' ((∅ : (ComVC →ₒ L).QueryCache).cacheQuery q r) := by
    intro β q rest
    change Prod.fst <$> ((ro q >>= rest).run ∅) =
      $ᵗ L >>= fun r =>
        Prod.fst <$> (rest r).run ((∅ : (ComVC →ₒ L).QueryCache).cacheQuery q r)
    simp only [ro, randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
      StateT.run_get, pure_bind, uniformSampleImpl, bind_assoc, map_bind,
      liftM, MonadLiftT.monadLift,
      MonadLift.monadLift, QueryCache.empty_apply]
    simp only [StateT.run_lift, StateT.run_modifyGet]
    rw [bind_assoc]
    simp only [pure_bind]
  have hro_hit : ∀ {β : Type} (q : ComVC) (r : L)
      (rest : L → StateT ((ComVC →ₒ L).QueryCache) ProbComp β),
      (ro q >>= rest).run' ((∅ : (ComVC →ₒ L).QueryCache).cacheQuery q r) =
        (rest r).run' ((∅ : (ComVC →ₒ L).QueryCache).cacheQuery q r) := by
    intro β q r rest
    change Prod.fst <$> ((ro q >>= rest).run
        ((∅ : (ComVC →ₒ L).QueryCache).cacheQuery q r)) =
      Prod.fst <$> (rest r).run
        ((∅ : (ComVC →ₒ L).QueryCache).cacheQuery q r)
    rw [StateT.run_bind]
    simp only [ro, randomOracle, QueryImpl.withCaching_apply, StateT.run_bind,
      StateT.run_get, pure_bind, QueryCache.cacheQuery_self, StateT.run_pure]
  change 𝒟[StateT.run' (simulateQ impl (do
      let ck ← (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L))) C vc chk ps).setup
      let (com, st) ←
        (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L))) C vc chk ps).commit ck msg
      let τ ← (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L))) C vc chk ps).openAt ck st i
      (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L))) C vc chk ps).verify
        ck com i (C.encode msg i) τ)) ∅] = _
  dsimp only [scheme]
  simp only [monad_norm, simulateQ_bind, simulateQ_pure, hSimQuery]
  simp_rw [hpeel, hro_miss, hro_hit, StateT.run'_pure']

/-- **Completeness of the scheme**: if the vector commitment is perfectly
complete, the code checker is complete for `C`, and the argument system is
perfectly complete, then the scheme is a perfectly complete erasure code
commitment for `C` under the fresh-random-oracle semantics. -/
theorem scheme_perfectlyComplete (hvc : vc.PerfectlyComplete)
    (hchk : chk.Complete C) (hps : ps.PerfectlyComplete) :
    (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L))) C vc chk ps).PerfectlyComplete C
      (roRuntime ComVC L) := by
  intro msg i
  rw [completeness_evalDist_eq C vc chk ps msg i, evalDist_singleton_eq_prEvent,
    OracleComp.prEvent_eq_one_iff]
  intro b hb
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
    exists_prop] at hb
  obtain ⟨ckVC, hck, crs, hcrs, l, -, rfl⟩ := hb
  have hrel : schemeRel vc chk (ckVC, vc.commit ckVC (C.encode msg), l) (C.encode msg) = true := by
    simp [schemeRel, hchk _ (C.encode_mem_code msg) l]
  have hpv := hps crs hcrs _ _ hrel
  have hvv := hvc ckVC hck (C.encode msg) i
  simp [hpv, hvv]

end completeness

end PqDas
