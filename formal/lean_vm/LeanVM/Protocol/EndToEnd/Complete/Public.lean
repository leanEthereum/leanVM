/-
  LeanVM.Protocol.EndToEnd.Complete.Public

  The honest prover of the verifier program's public-input step: the challenge, after which the
  verifier's three memory claims, computed from the public digest, are true of a stack whose
  public lines hold.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Claims
public import LeanVM.Protocol.Whir.Complete.Script
public import LeanVM.Protocol.PublicInput
public import LeanVM.Protocol.Blake2sHash
public import LeanVM.Spec.Statement
import LeanVM.Protocol.Compile.Rom.Encoding

/-!
# The public input

Step 5 of `verify_execution` (`publicInputPhase`, `python-verifier/verifier.py:1390-1396` at
leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`): sample `r`, and claim of memory column `ℓ` at
`(r, 0, …, 0)` the line through limb `ℓ` of the halves `(h₀, h₁)` of the public-input digest,
`(1 + r)·h₀,ℓ + r·h₁,ℓ`. The prover sends nothing.

* `publicDigest input`: the digest of a public input, its eight 32-bit words (the low and high
  words of each lane), so that its two halves are the public input's two memory words
  (`digestScalars_publicDigest`); the inverse of the soundness side's reading
  `Front.publicInputOfDigest`.
* `hPub`: the honest prover receives `r` and sends nothing; it returns the claims at the
  extensions of the three memory limbs at `(r, 0, …, 0)`, the lines through their cells `0, 1`
  (`PublicInput.eval₂Mle_linePoint`).
* `follows_publicInputPhase`: on a stack satisfying `M3Holds`, its public lines (`MEM_LO` holds
  `input₀, input₂`, `MEM_HI` holds `input₁, input₃`, `MEM_TOP` holds `0, 0`) make the verifier's
  claims those values, so they are true claims (`TrueClaim`).
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.PublicInput CompPoly CMlPolynomialEval

@[expose] public section

/-! ## The digest of a public input -/

export LeanVM (publicDigest)

/-- **The digest names the public input.** -/
theorem publicDigest_injective : Function.Injective publicDigest := by
  intro a b h
  have hw : ∀ i : Fin 8, (publicDigest a)[i] = (publicDigest b)[i] := fun i ↦ by rw [h]
  have hl : ∀ i : Fin 4, a.lanes i = b.lanes i := by
    intro i
    have h0 := hw ⟨2 * i, by omega⟩
    have h1 := hw ⟨2 * i + 1, by omega⟩
    rw [← Compile.Rom.ofWords_lowWord_highWord (a.lanes i),
      ← Compile.Rom.ofWords_lowWord_highWord (b.lanes i)]
    fin_cases i <;> simp_all [publicDigest]
  cases a; cases b
  simp only [PublicInput.mk.injEq]
  exact funext hl

/-- The digest's two halves are the public input's two memory words. -/
theorem digestScalars_publicDigest (input : PublicInput) :
    digestScalars (publicDigest input) = (input.word0, input.word1) := by
  simp [digestScalars, publicDigest, wordsCell, PublicInput.word0, PublicInput.word1,
    Compile.Rom.ofWords_lowWord_highWord]

/-! ## The honest prover -/

/-- The public point `(r, 0, …, 0)` the program claims the memory columns at. -/
def publicPoint (layout : Verifier.Layout) (r : E) : List E :=
  r :: List.replicate ((layout.placements.getD memory0 default).vars - 1) 0

/-- Claims of the three memory columns at the public point after the challenge `r`, at the given
values. -/
def publicClaims (layout : Verifier.Layout) (r : E) (limbs : List E) : List Verifier.ColumnClaim :=
  List.zipWith (fun column value ↦ ⟨column, publicPoint layout r, value⟩)
    [memory0, memory1, memory2] limbs

/-- The true value of memory limb `i` on the line through its cells `0, 1`. -/
def memLine (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (i : Fin 4) (r : E) : E :=
  colEval prog s q (memCol i) (linePoint s.logMem_pos r)

/-- **The honest prover of the public input**: receive `r` and send nothing; return the claims
at the true values of the three memory limbs on their lines, which are the program's. -/
def hPub (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Script (List Verifier.ColumnClaim) :=
  Script.sampleE.bind fun r ↦
    .ret (publicClaims (verifierLayout prog s) r
      [memLine prog s q 0 r, memLine prog s q 1 r, memLine prog s q 2 r])

/-! ## Completeness -/

/-- The public point at the verifier's layout is the line point of the memory columns. -/
theorem publicPoint_eq (prog : Program) (s : Sizes) (r : E) :
    publicPoint (verifierLayout prog s) r = (linePoint s.logMem_pos r).toList := by
  have hp := placement_committed prog s (memCol 0) (by decide)
  rw [pyCol_memCol] at hp
  have hv : ((verifierLayout prog s).placements.getD memory0 default).vars = s.logMem := by
    rw [show memory0 = ((0 : Fin 4) : ℕ) from rfl, hp]
    rfl
  rw [publicPoint, hv]
  simp [linePoint, Vector.toList_cast, Vector.toList_append]

/-- A memory limb's line value, from its cells `0, 1`. -/
theorem memLine_eq (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (i : Fin 4)
    (r : E) :
    memLine prog s q i r =
      (1 + r) * ofK (((inst prog s).column q (memCol i)).values.get ⟨0, Nat.two_pow_pos _⟩) +
        r * ofK (((inst prog s).column q (memCol i)).values.get
          ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩) := by
  have h := eval₂Mle_linePoint s.logMem_pos ((inst prog s).column q (memCol i)).values r
  rw [CharTwo.sub_eq_add] at h
  exact h

/-- The program's claim on memory limb `i` at the public point is a true claim, when its value
is the limb's line value. -/
theorem trueClaim_memLine (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (i : Fin 4)
    (r v : E) (hv : v = memLine prog s q i r) :
    TrueClaim prog s q ⟨i, publicPoint (verifierLayout prog s) r, v⟩ :=
  ⟨memCol i, linePoint s.logMem_pos r, by rw [pyCol_memCol, publicPoint_eq, hv]; rfl⟩

/-- **The honest public-input step.** On a stack satisfying `M3Holds`, the verifier's claims,
computed from the public input's digest, are the honest ones, and they are true. -/
theorem follows_publicInputPhase {prog : Program} {s : Sizes} {input : PublicInput}
    {q : Column (leanIsaμ prog s)} (hq : M3Holds (inst prog s) input q) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b) (hPub prog s q)
      (Verifier.publicInputPhase (verifierLayout prog s) (publicDigest input)) cs := by
  have hlines := hq.2.2.2.1
  have hl : ∀ l ∈ ((inst prog s).publicLines input).toList,
      ((inst prog s).column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩ = l.cell0 ∧
        ((inst prog s).column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩ = l.cell1 :=
    hlines
  have h0 := hl _ (by simp [inst, leanIsaInstance, publicLines] : (⟨memCol 0, input.lanes 0,
    input.lanes 2, false, s.logMem_pos⟩ : PublicLine (shape prog s)) ∈ _)
  have h1 := hl _ (by simp [inst, leanIsaInstance, publicLines] : (⟨memCol 1, input.lanes 1,
    input.lanes 3, false, s.logMem_pos⟩ : PublicLine (shape prog s)) ∈ _)
  have h2 := hl _ (by simp [inst, leanIsaInstance, publicLines] : (⟨memCol 2, 0, 0, false,
    s.logMem_pos⟩ : PublicLine (shape prog s)) ∈ _)
  simp only at h0 h1 h2
  unfold Verifier.publicInputPhase hPub
  simp only [Prog.bind_eq]
  refine Follows.bind (fun cs₁ r r' hr ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs)
  obtain ⟨rfl, rfl⟩ := hr
  have hz : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  have hlimbs : (([0, 1, 2] : List (Fin 3)).map fun limb ↦
      multilinearEval [ofK ((digestScalars (publicDigest input)).1.limb limb),
        ofK ((digestScalars (publicDigest input)).2.limb limb)] [r]) =
      [memLine prog s q 0 r, memLine prog s q 1 r, memLine prog s q 2 r] := by
    simp only [List.map_cons, List.map_nil, digestScalars_publicDigest, PublicInput.word0,
      PublicInput.word1, limb_ofLimbs, memLine_eq, h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
    simp only [multilinearEval, List.foldl, foldPairs, List.headD]
    refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
    all_goals (try simp [hz])
    all_goals ring
  simp only [Prog.pure_eq]
  refine ⟨rfl, ?_, ?_⟩
  · show publicClaims (verifierLayout prog s) r _ = List.zipWith _ _ _
    rw [hlimbs]
    rfl
  · intro cl hcl
    rw [hlimbs] at hcl
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hcl
    rcases hcl with rfl | rfl | rfl
    · exact trueClaim_memLine prog s q 0 r _ rfl
    · exact trueClaim_memLine prog s q 1 r _ rfl
    · exact trueClaim_memLine prog s q 2 r _ rfl

end
end LeanVM.Protocol.EndToEnd.Complete
