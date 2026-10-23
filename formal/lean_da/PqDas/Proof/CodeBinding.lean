/-
# Code-binding of the scheme

Code-binding of the erasure code commitment scheme, by reduction to three
assumptions (compare Foundations of Data Availability Sampling,
eprint 2023/1079, Lemma 14, which treats the variant where the argument system
proves exact code membership):

* knowledge soundness of the argument system,
* hardness of the non-interactive committed soundness game (which encapsulates
  the interplay between the code checker and the oracle-derived randomness;
  bounded separately), and
* weak position-binding of the vector commitment.

Given a code-binding adversary, run it and extract a witness `c` from the
proof it output, using the argument system's straightline extractor at the
statement `(ckVC, comVC, H(comVC))`. Decompose the winning event:

* if extraction fails (the proof verifies but the extracted witness does not
  satisfy the relation), the run breaks knowledge soundness (`ksReduction`);
* if extraction succeeds but `c` is not a codeword, then `c` passes the code
  check on randomness `H(comVC)` and commits to `comVC`: a win in the
  non-interactive committed soundness game (`csReduction`);
* if extraction succeeds and `c` is a codeword, then since no codeword is
  consistent with the adversary's opened symbols, some opened `(i, x, τ)` has
  `x ≠ c i`, and `τ` is a valid opening of the honest commitment
  `comVC = vc.commit ckVC c`, breaking weak position-binding
  (`wpbReduction`).

All three reductions are explicit algorithms; each reproduces the code-binding
experiment's distribution exactly (simulating the random-oracle world
internally where needed), so the union bound is a sum of their winning
probabilities.

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import PqDas.Target.Scheme
import PqDas.Proof.CommittedSoundness.Defs
import PqDas.VcvioExtras
import VCVio.OracleComp.EvalDist.Sum

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

/-- The adversary's continuation shared by the reductions below: run the
code-binding adversary, then query the oracle once more on the commitment it
output (a cache hit if the adversary already queried it), obtaining the check
randomness that the scheme's verification would use. -/
def runWithChallenge
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn)
    (ck : CkVC × Crs) :
    OracleComp (unifSpec + (ComVC →ₒ L))
      (((ComVC × Proof) × List (Fin n × Λ × Opn)) × L) := do
  let out ← A ck
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) out.1.1
  return (out, l)

/-- Reduction to knowledge soundness (an explicit PPT algorithm): sample the
vector-commitment key, simulate the random-oracle world for the code-binding
adversary, and output the statement `(ckVC, comVC, l)` together with the
adversary's proof. -/
noncomputable def ksReduction [DecidableEq ComVC] [SampleableType L]
    (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    Nark.KnowledgeSoundnessAdv (CkVC × ComVC × L) Crs Proof := fun crs => do
  let ckVC ← vc.setup
  let ((com, _), l) ← simulateRom (runWithChallenge A (ckVC, crs))
  return ((ckVC, com.1, l), com.2)

/-- Reduction to the non-interactive committed soundness game (an explicit PPT
algorithm): sample the crs, relay the code-binding adversary's oracle access,
and output the vector-commitment part of its commitment together with the
extracted witness. -/
noncomputable def csReduction [DecidableEq ComVC] [SampleableType L]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    NiCsAdv Λ n CkVC ComVC L := fun ckVC => do
  let crs ← liftM ps.setup
  let (com, _) ← A (ckVC, crs)
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) com.1
  return (com.1, ext crs (ckVC, com.1, l) com.2)

/-- Reduction to weak position-binding (an explicit PPT algorithm): sample the
crs, simulate the random-oracle world for the code-binding adversary, extract
the witness `c` from its proof, and search its openings for one whose symbol
disagrees with `c`. If none disagrees the reduction has lost anyway and
outputs a dummy tuple. -/
noncomputable def wpbReduction [NeZero n] [DecidableEq Λ] [DecidableEq ComVC]
    [SampleableType L] [Inhabited Opn]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    VectorCommitment.WeakPosBindingAdv Λ n CkVC Opn := fun ckVC => do
  let crs ← ps.setup
  let ((com, openings), l) ← simulateRom (runWithChallenge A (ckVC, crs))
  let c := ext crs (ckVC, com.1, l) com.2
  match openings.find? (fun p => decide (p.2.1 ≠ c p.1)) with
  | some p => return (c, p.1, p.2.1, p.2.2)
  | none => return (c, 0, c 0, default)

/-! ### Proof of code-binding

All four experiments share a common core: sample the two keys, run the
adversary in the simulated random-oracle world, and query the oracle once on
the vector-commitment part of its output commitment (`challengedRun`). Aligned
on this shared prefix, each experiment's winning condition is a deterministic
Boolean function of the prefix outcome (`gameWinBit`, `ksWinBit`, `csWinBit`,
`wpbWinBit`): every random-oracle query made downstream of the prefix hits the
cache entry pinned by the challenge query, so it returns the same answer and
leaves the cache unchanged. The game's bit implies one of the reductions' bits
(`gameWinBit_implies`), so a pointwise union bound over the shared prefix
(`prEvent_bind_le_add₃`) concludes. -/

section codeBindingProof

/-- Union bound over a shared prefix: if pointwise on the support the first
continuation's success probability is bounded by the sum of the other three
continuations' success probabilities, the same holds after composing all four
with the shared prefix. -/
private lemma prEvent_bind_le_add₃ {α : Type} (oa : ProbComp α)
    (f g₁ g₂ g₃ : α → ProbComp Bool)
    (h : ∀ x ∈ support oa, Pr{let y ← f x}[y = true] ≤
        Pr{let y ← g₁ x}[y = true] + Pr{let y ← g₂ x}[y = true] + Pr{let y ← g₃ x}[y = true]) :
    Pr{let x ← oa >>= f}[x = true] ≤
      Pr{let x ← oa >>= g₁}[x = true] + Pr{let x ← oa >>= g₂}[x = true] + Pr{let x ← oa >>= g₃}[x = true] := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support oa
  · rw [← mul_add, ← mul_add]
    exact mul_le_mul_right (h x hx) _
  · simp [(prEvent_eq_zero_of_not_mem_support _) hx]

/-- Three-way Boolean union bound for `pure` computations. -/
private lemma prEvent_pure_bool_le_or₃ (win b₁ b₂ b₃ : Bool)
    (h : win = true → b₁ = true ∨ b₂ = true ∨ b₃ = true) :
    Pr{let x ← (pure win : ProbComp Bool)}[x = true] ≤
      Pr{let x ← (pure b₁ : ProbComp Bool)}[x = true] + Pr{let x ← (pure b₂ : ProbComp Bool)}[x = true] +
        Pr{let x ← (pure b₃ : ProbComp Bool)}[x = true] := by
  cases win <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> simp_all

/-- Simulating a `mapM` whose every step queries the oracle at the same point
`q`, starting from a cache that already answers `q` with `l`: every query is a
cache hit, so the verdicts are computed by a plain `map` at answer `l` and the
cache is unchanged. -/
private lemma simulateRomWithCache_mapM_query_hit [DecidableEq ComVC] [SampleableType L]
    {α β : Type} {q : ComVC} {cache : (ComVC →ₒ L).QueryCache} {l : L}
    (h : cache q = some l) (g : α → L → Bool) (xs : List α)
    (k : List Bool → OracleComp (unifSpec + (ComVC →ₒ L)) β) :
    simulateRomWithCache cache
        (xs.mapM (fun p => HasQuery.query (spec := (ComVC →ₒ L)) q >>=
          fun l' => pure (g p l')) >>= k) =
      simulateRomWithCache cache (k (xs.map fun p => g p l)) := by
  induction xs generalizing k with
  | nil => rw [List.mapM_nil, pure_bind, List.map_nil]
  | cons p ps ih =>
      rw [List.mapM_cons, List.map_cons]
      simp only [bind_assoc, pure_bind]
      rw [simulateRomWithCache_query_bind, randomOracle_run_hit h, pure_bind]
      exact ih _

variable [Nonempty Γ] [Fintype Γ] [DecidableEq Λ] [DecidableEq ComVC] [SampleableType L]
  [NeZero n] [Inhabited Opn]
  (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
  (chk : CodeChecker Λ n L)
  (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
  (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
  (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
    Λ n (CkVC × Crs) (ComVC × Proof) Opn)

/-- The prefix shared by all four experiments, with the challenge query
appended: sample both keys, run the adversary in the simulated random-oracle
world, then query the oracle once on the vector-commitment part of its output
commitment (a cache hit if the adversary already queried it). -/
private noncomputable def challengedRun :
    ProbComp (CkVC × Crs × ((ComVC × Proof) × List (Fin n × Λ × Opn)) × L) := do
  let ckVC ← vc.setup
  let crs ← ps.setup
  let z ← (simulateQ (romImpl ComVC L) (A (ckVC, crs))).run ∅
  let x ← ((randomOracle : QueryImpl (ComVC →ₒ L)
      (StateT ((ComVC →ₒ L).QueryCache) ProbComp)) z.1.1.1).run z.2
  return (ckVC, crs, z.1, x.1)

/-- The code-binding game's winning bit as a function of the shared prefix
outcome: all openings verify (each verification's oracle query returns the
pinned challenge) and no codeword is consistent with the opened symbols. -/
private def gameWinBit (ckVC : CkVC) (crs : Crs)
    (out : (ComVC × Proof) × List (Fin n × Λ × Opn)) (l : L) : Bool :=
  ((out.2.map fun p => ps.verify crs (ckVC, out.1.1, l) out.1.2 &&
      vc.verify ckVC out.1.1 p.1 p.2.1 p.2.2).all id) &&
    !decide (C.Consistent (out.2.map fun p => (p.1, p.2.1)))

/-- The knowledge-soundness reduction's winning bit as a function of the
shared prefix outcome. -/
private def ksWinBit (ckVC : CkVC) (crs : Crs)
    (out : (ComVC × Proof) × List (Fin n × Λ × Opn)) (l : L) : Bool :=
  ps.verify crs (ckVC, out.1.1, l) out.1.2 &&
    !schemeRel vc chk (ckVC, out.1.1, l) (ext crs (ckVC, out.1.1, l) out.1.2)

/-- The committed-soundness reduction's winning bit as a function of the
shared prefix outcome. -/
private def csWinBit (ckVC : CkVC) (crs : Crs)
    (out : (ComVC × Proof) × List (Fin n × Λ × Opn)) (l : L) : Bool :=
  decide (ext crs (ckVC, out.1.1, l) out.1.2 ∉ C.code) &&
    chk.check l (ext crs (ckVC, out.1.1, l) out.1.2) &&
    decide (vc.commit ckVC (ext crs (ckVC, out.1.1, l) out.1.2) = out.1.1)

/-- The weak position-binding reduction's winning bit as a function of the
shared prefix outcome. -/
private def wpbWinBit (ckVC : CkVC) (crs : Crs)
    (out : (ComVC × Proof) × List (Fin n × Λ × Opn)) (l : L) : Bool :=
  match out.2.find? fun p =>
      decide (p.2.1 ≠ ext crs (ckVC, out.1.1, l) out.1.2 p.1) with
  | some p => decide (p.2.1 ≠ ext crs (ckVC, out.1.1, l) out.1.2 p.1) &&
      vc.verify ckVC (vc.commit ckVC (ext crs (ckVC, out.1.1, l) out.1.2))
        p.1 p.2.1 p.2.2
  | none => decide (ext crs (ckVC, out.1.1, l) out.1.2 0 ≠
        ext crs (ckVC, out.1.1, l) out.1.2 0) &&
      vc.verify ckVC (vc.commit ckVC (ext crs (ckVC, out.1.1, l) out.1.2)) 0
        (ext crs (ckVC, out.1.1, l) out.1.2 0) default

omit [SampleableType L] in
/-- Pointwise event decomposition: whenever the game's winning bit is set, one
of the three reductions' winning bits is set. If extraction fails the
knowledge-soundness bit is set (the game's win includes a verifying proof,
since consistency of the empty opening list rules out an empty win); if it
succeeds with a non-codeword the committed-soundness bit is set; if it
succeeds with a codeword some opened symbol disagrees with it, setting the
weak position-binding bit. -/
private lemma gameWinBit_implies (ckVC : CkVC) (crs : Crs)
    (out : (ComVC × Proof) × List (Fin n × Λ × Opn)) (l : L)
    (h : gameWinBit C vc chk ps ckVC crs out l = true) :
    ksWinBit vc chk ps ext ckVC crs out l = true ∨
      csWinBit C vc chk ext ckVC crs out l = true ∨
      wpbWinBit vc ext ckVC crs out l = true := by
  obtain ⟨⟨comVC, π⟩, openings⟩ := out
  simp only [gameWinBit, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨hall, hncons⟩ := h
  have hver : ∀ p ∈ openings, ps.verify crs (ckVC, comVC, l) π = true ∧
      vc.verify ckVC comVC p.1 p.2.1 p.2.2 = true := by
    intro p hp
    have := hall _ ⟨p, hp, rfl⟩
    simpa [Bool.and_eq_true] using this
  have hne : openings ≠ [] := by
    rintro rfl
    exact hncons ⟨Classical.arbitrary _, by simp⟩
  obtain ⟨p₀, hp₀⟩ := List.exists_mem_of_ne_nil openings hne
  have hps : ps.verify crs (ckVC, comVC, l) π = true := (hver p₀ hp₀).1
  cases hrel : schemeRel vc chk (ckVC, comVC, l) (ext crs (ckVC, comVC, l) π) with
  | false => exact Or.inl (by simp [ksWinBit, hps, hrel])
  | true =>
      rw [schemeRel, Bool.and_eq_true, decide_eq_true_eq] at hrel
      obtain ⟨hcommit, hchk⟩ := hrel
      by_cases hcode : ext crs (ckVC, comVC, l) π ∈ C.code
      · refine Or.inr (Or.inr ?_)
        have hbad : ∃ p ∈ openings, p.2.1 ≠ ext crs (ckVC, comVC, l) π p.1 := by
          by_contra hno
          push Not at hno
          obtain ⟨m, hm⟩ := hcode
          refine hncons ⟨m, fun pr hpr => ?_⟩
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hpr
          rw [hm]
          exact (hno p hp).symm
        have hfind : (openings.find? fun p =>
            decide (p.2.1 ≠ ext crs (ckVC, comVC, l) π p.1)).isSome := by
          rw [List.find?_isSome]
          obtain ⟨p, hp, hne'⟩ := hbad
          exact ⟨p, hp, decide_eq_true hne'⟩
        obtain ⟨p₁, hfind⟩ := Option.isSome_iff_exists.mp hfind
        have hpred := List.find?_some hfind
        have hv : vc.verify ckVC comVC p₁.1 p₁.2.1 p₁.2.2 = true :=
          (hver p₁ (List.mem_of_find?_eq_some hfind)).2
        simp only [wpbWinBit, hfind]
        rw [hcommit]
        simp [hpred, hv]
      · exact Or.inr (Or.inl (by simp [csWinBit, hcode, hchk, hcommit]))

omit [NeZero n] [Inhabited Opn] in
/-- Alignment of the code-binding game with the challenged shared prefix. If
the adversary opens nothing the game cannot win (the empty list is
consistent); otherwise the game's first verification query is the challenge
query, and all further verification queries are cache hits. -/
private lemma game_le_challengedRun :
    (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L)))
        C vc chk ps).codeBindingExp C (roRuntime ComVC L) A {true} ≤
      Pr{let x ← (challengedRun vc chk ps A >>= fun w =>
        pure (gameWinBit C vc chk ps w.1 w.2.1 w.2.2.1 w.2.2.2))}[x = true] := by
  unfold ErasureCodeCommitment.codeBindingExp challengedRun
  rw [← evalDist_simulateRom, evalDist_singleton_eq_prEvent]
  dsimp only [scheme]
  simp only [monad_norm, simulateRom]
  rw [simulateRomWithCache_liftM_bind]
  simp only [bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun ckVC _ => ?_
  rw [simulateRomWithCache_liftM_bind]
  simp only [bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun crs _ => ?_
  rw [simulateRomWithCache_bind]
  simp only [bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun z _ => ?_
  obtain ⟨⟨⟨comVC, π⟩, openings⟩, cache₁⟩ := z
  simp only [monad_norm]
  rcases openings with _ | ⟨p₀, rest⟩
  · have hcons : C.Consistent [] := ⟨Classical.arbitrary _, by simp⟩
    refine le_trans (le_of_eq ?_) zero_le
    simp [hcons]
  · cases hc : cache₁ comVC with
    | some l₀ =>
        rw [randomOracle_run_hit hc, pure_bind]
        rw [simulateRomWithCache_mapM_query_hit hc, simulateRomWithCache_pure]
        simp [gameWinBit]
    | none =>
        rw [List.mapM_cons]
        simp only [bind_assoc, pure_bind]
        rw [simulateRomWithCache_query_bind, randomOracle_run_miss hc]
        simp only [bind_assoc, pure_bind]
        refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun r _ => ?_
        rw [simulateRomWithCache_mapM_query_hit (QueryCache.cacheQuery_self cache₁ comVC r),
          simulateRomWithCache_pure]
        simp [gameWinBit]

omit [DecidableEq Λ] [NeZero n] [Inhabited Opn] in
/-- Alignment of the knowledge-soundness experiment with the challenged shared
prefix (the two key samplings commute). -/
private lemma challengedRun_ks_le :
    Pr{let x ← (challengedRun vc chk ps A >>= fun w =>
        pure (ksWinBit vc chk ps ext w.1 w.2.1 w.2.2.1 w.2.2.2))}[x = true] ≤
      Pr{let x ← ps.knowledgeSoundnessExp ext (ksReduction vc A)}[x = true] := by
  unfold challengedRun Nark.knowledgeSoundnessExp ksReduction runWithChallenge
  simp only [monad_norm, simulateRom]
  refine le_trans (le_of_eq (OracleComp.prEvent_bind_bind_swap vc.setup ps.setup _)) ?_
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun crs _ => ?_
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun ckVC _ => ?_
  rw [simulateRomWithCache_bind]
  simp only [bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun z _ => ?_
  obtain ⟨⟨⟨comVC, π⟩, openings⟩, cache₁⟩ := z
  simp only [monad_norm]
  rw [simulateRomWithCache_query_bind]
  simp only [simulateRomWithCache_pure, bind_assoc, pure_bind]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun x _ => ?_
  simp [ksWinBit]

omit [Nonempty Γ] [NeZero n] [Inhabited Opn] in
/-- Alignment of the non-interactive committed soundness experiment with the
challenged shared prefix: the reduction's challenge query pins the cache entry
for the output commitment, so the game's own challenge query is a hit
returning the same answer. -/
private lemma challengedRun_cs_le :
    Pr{let x ← (challengedRun vc chk ps A >>= fun w =>
        pure (csWinBit C vc chk ext w.1 w.2.1 w.2.2.1 w.2.2.2))}[x = true] ≤
      niCommittedSoundnessExp C vc chk (csReduction ps ext A) {true} := by
  unfold challengedRun niCommittedSoundnessExp csReduction
  rw [← evalDist_simulateRom, evalDist_singleton_eq_prEvent]
  simp only [monad_norm, simulateRom]
  simp only [simulateRomWithCache_liftM_bind, bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun ckVC _ => ?_
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun crs _ => ?_
  rw [simulateRomWithCache_bind]
  simp only [bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun z _ => ?_
  obtain ⟨⟨⟨comVC, π⟩, openings⟩, cache₁⟩ := z
  simp only [monad_norm]
  rw [simulateRomWithCache_query_bind]
  cases hc : cache₁ comVC with
  | some l₀ =>
      rw [randomOracle_run_hit hc]
      simp only [pure_bind]
      rw [simulateRomWithCache_query_bind, randomOracle_run_hit hc]
      simp [csWinBit]
  | none =>
      rw [randomOracle_run_miss hc]
      simp only [bind_assoc, pure_bind]
      refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun r _ => ?_
      rw [simulateRomWithCache_query_bind,
        randomOracle_run_hit (QueryCache.cacheQuery_self cache₁ comVC r)]
      simp [csWinBit]

/-- Alignment of the weak position-binding experiment with the challenged
shared prefix. -/
private lemma challengedRun_wpb_le :
    Pr{let x ← (challengedRun vc chk ps A >>= fun w =>
        pure (wpbWinBit vc ext w.1 w.2.1 w.2.2.1 w.2.2.2))}[x = true] ≤
      Pr{let x ← vc.weakPosBindingExp (wpbReduction ps ext A)}[x = true] := by
  unfold challengedRun VectorCommitment.weakPosBindingExp wpbReduction runWithChallenge
  simp only [monad_norm, simulateRom]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun ckVC _ => ?_
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun crs _ => ?_
  rw [simulateRomWithCache_bind]
  simp only [bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun z _ => ?_
  obtain ⟨⟨⟨comVC, π⟩, openings⟩, cache₁⟩ := z
  simp only [monad_norm]
  rw [simulateRomWithCache_query_bind]
  simp only [simulateRomWithCache_pure, bind_assoc, pure_bind]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun x _ => ?_
  simp only [wpbWinBit, ne_eq, decide_not]
  cases hfind : openings.find? fun p =>
      !decide (p.2.1 = ext crs (ckVC, comVC, x.1) π p.1) with
  | some p₁ => simp
  | none => simp

/-- Union bound over the challenged shared prefix, via the pointwise event
decomposition `gameWinBit_implies`. -/
private lemma challengedRun_split :
    Pr{let x ← (challengedRun vc chk ps A >>= fun w =>
        pure (gameWinBit C vc chk ps w.1 w.2.1 w.2.2.1 w.2.2.2))}[x = true] ≤
      Pr{let x ← (challengedRun vc chk ps A >>= fun w =>
          pure (ksWinBit vc chk ps ext w.1 w.2.1 w.2.2.1 w.2.2.2))}[x = true] +
        Pr{let x ← (challengedRun vc chk ps A >>= fun w =>
          pure (csWinBit C vc chk ext w.1 w.2.1 w.2.2.1 w.2.2.2))}[x = true] +
        Pr{let x ← (challengedRun vc chk ps A >>= fun w =>
          pure (wpbWinBit vc ext w.1 w.2.1 w.2.2.1 w.2.2.2))}[x = true] :=
  prEvent_bind_le_add₃ _ _ _ _ _ fun w _ =>
    prEvent_pure_bool_le_or₃ _ _ _ _
      (gameWinBit_implies C vc chk ps ext w.1 w.2.1 w.2.2.1 w.2.2.2)

end codeBindingProof

/-- **Code-binding of the scheme**, by reduction to knowledge soundness of the
argument system, the non-interactive committed soundness game, and weak
position-binding of the vector commitment, via the three explicit reductions
above.

The hypothesis `Nonempty Γ` rules out a degenerate vacuous win: if there were
no messages at all, the empty list of openings would be inconsistent with the
(empty) code without the adversary ever producing a verifying proof or
opening. -/
theorem scheme_codeBinding [Nonempty Γ] [Fintype Γ] [DecidableEq Λ]
    [DecidableEq ComVC] [SampleableType L] [NeZero n] [Inhabited Opn]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L)))
        C vc chk ps).codeBindingExp C (roRuntime ComVC L) A {true} ≤
      Pr{let x ← ps.knowledgeSoundnessExp ext (ksReduction vc A)}[x = true] +
      niCommittedSoundnessExp C vc chk (csReduction ps ext A) {true} +
      Pr{let x ← vc.weakPosBindingExp (wpbReduction ps ext A)}[x = true] := by
  refine le_trans (game_le_challengedRun C vc chk ps A) ?_
  refine le_trans (challengedRun_split C vc chk ps ext A) ?_
  exact add_le_add (add_le_add (challengedRun_ks_le vc chk ps ext A)
    (challengedRun_cs_le C vc chk ps ext A)) (challengedRun_wpb_le vc chk ps ext A)

end PqDas
