/-
  LeanVM.Guest.B1.VsC.OpenStackedA

  The statement of `open_stacked`'s placed completeness, which `verify_sub`'s assembly takes.
-/

module

public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Complete.CallCompleteA
public import LeanVM.Guest.ExpTables
public import Statement.LeanVmGuestProver

/-!
# `open_stacked`, placed: the statement

`OpenRunQueries μ r root target s xs os qs`: from every sponge the guest carries as `s`, on any rest
of the stream and the phases, the run of `whirOpen μ r target` on the words `xs` and the openings
`os` (its first commitment `root`) has its query steps' openings agreeing in their trees
(`Limits.OpeningsAgree`, what `VsChildOk`'s last conjunct gives for the child's run), and records
the queries `qs`, each with its tree's height (as `childQueries` reads them).

`OpenStackedCompleteA fs al cert k m`: `open_stacked__L{m}` at every rate `r`, on capacity cells `fsv`
that some Spec sponge carries (else `RunsWith` holds of every end `w` and the statement is false), the
claim `target`, the root's halves, the stream's cursor `g^ic` and the window tables at
`g^it` (cells of the caller's region `R`), at every frame `fp` and cursor `c` past its block,
returns the run's end (`w.target`, the point's two buffers `g^bp`, `g^bp1` it owns, `w.inner`,
`w.residual`, the cursor past `xs`), claiming the point buffers as its data, which hold the point
(and its plus-one form) padded to `pointCap`; it pops the run's Merkle hints (`merkleHints true qs
os`) stream by stream (`SameStreams`: a level pops its cap and flags before its queries' rows and
paths, which `levelHints` pushes after them), every node exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The run of `whirOpen μ r target` on `xs` and `os` from the capacity `s`: its query steps'
openings agree, and it records the queries `qs`, each with its tree's height. -/
def OpenRunQueries (μ r : ℕ) (root : Digest) (target : E) (s : Fs) (xs : List E) (os : List (List Opening))
    (qs : List (ℕ × List ℕ)) : Prop :=
  ∀ sp : Sponge, s.Carries sp → ∀ (rest : List E) (orest : List (List Opening)),
    (∀ step ∈ Limits.queryStepsOf (whirOpen μ r target) ⟨sp, xs ++ rest, os ++ orest, [(root, stackShape μ r)]⟩,
      Limits.OpeningsAgree step.1 step.2) ∧
    ∃ (a : WhirEnd) (qr : List (ℕ × List ℕ)) (st : VerifierProgramState),
      runId (Prover.recordQueries (whirOpen μ r target)) ⟨sp, xs ++ rest, os ++ orest, [(root, stackShape μ r)]⟩ =
        some ((a, qr), st) ∧
      qs = qr.map fun q => ((st.roots[q.1]?.map (·.2.1)).getD 0, q.2)

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) in
/-- **`open_stacked__L{m}` completes placed**, at every rate. -/
def OpenStackedCompleteA (k m : ℕ) : Prop :=
  ∀ (r : ℕ) (root : Digest) (fsv : List E) (target : E) (ic it : ℕ) (xs : List E)
    (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ))
    (qs : List (ℕ × List ℕ)) (R : ℕ → Prop),
    1 ≤ r → r ≤ 4 → fsv.length = 5 → (∃ sp : Sponge, (⟨fsv, []⟩ : Fs).Carries sp) →
    RunsWith (whirOpen (minOpenLog + m) r target) ⟨fsv, []⟩ xs os [(root, stackShape (minOpenLog + m) r)]
      w s' roots' →
    OpenRunQueries (minOpenLog + m) r root target ⟨fsv, []⟩ xs os qs →
    (∀ i < xs.length, R (ic + i)) → (∀ n < 2 ^ winTabBits, R (it + n)) →
    ∀ fp c, fp + fs (openName (minOpenLog + m)) ≤ c → ∃ bp bp1 e : ℕ,
      CallAtA fs al cert k (openName (minOpenLog + m))
        (rateSel r :: fsv ++ [target, (digestHalves root).1, (digestHalves root).2, ofK (addressOfIndex ic), ofK (addressOfIndex it)])
        [w.target, ofK (addressOfIndex bp), ofK (addressOfIndex bp1), w.inner, w.residual, ofK (addressOfIndex (ic + xs.length))] R
        (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
        (fun rd => ReadsAt rd (ofK (addressOfIndex bp)) (w.point ++ List.replicate (pointCap - (minOpenLog + m)) 0) ∧
          ReadsAt rd (ofK (addressOfIndex bp1)) (w.point.map (1 + ·) ++ List.replicate (pointCap - (minOpenLog + m)) 1))
        (fun rd => ReadsAt rd (ofK (addressOfIndex ic)) xs ∧ WinTabs rd (ofK (addressOfIndex it)))
        (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.merkleHints true qs os) ∧
          t.Every (ExactAt coreProgram rd))
        (fs (openName (minOpenLog + m))) fp c e

end
end LeanVM.Guest.B1.VsC
