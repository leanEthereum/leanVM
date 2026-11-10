/-
  LeanVM.Guest.B1.Whir.Run

  Runs of the stacked opening with openings and commitments: composing them, a commitment, a
  query.
-/

module

public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Common.Phase
public import LeanVM.Guest.B1.Whir.Interface

/-!
# Runs of the stacked opening (TRIAGE G #42)

The Spec's side of `open_stacked`, no guest value in it.

* `RunsTo.withRoots`, `RunsWith.bind`, `runsWith_ret`: `RunsTo` (`B1/Common/Sponge.lean`) is a
  `RunsWith` reading no opening; runs compose.
* `runsWith_commitP`: a commitment reads the root's two scalars (absorbed with `dsObserve`) and
  appends the root they encode with its shape; `runsWith_queryP`: a query consumes one phase, one
  opening per position at the position, each passing `openOne` against the commitment's root, and
  returns their leaves.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Composing runs -/

/-- A run reading no opening, at any commitments. -/
theorem RunsTo.withRoots {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') (roots : List (Digest × ℕ × ℕ)) : RunsWith p s xs [] roots a s' roots :=
  fun sp hs rest orest ↦ h sp hs rest ([] ++ orest) roots

theorem runsWith_ret {α : Type} (a : α) (s : Fs) (roots : List (Digest × ℕ × ℕ)) :
    RunsWith (pure a : VerifierProgram α) s [] [] roots a s roots :=
  fun sp h _ _ ↦ ⟨sp, h, rfl⟩

theorem RunsWith.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {s s1 s2 : Fs} {xs ys : List E} {os1 os2 : List (List Opening)}
    {r0 r1 r2 : List (Digest × ℕ × ℕ)} {a : α} {b : β}
    (h1 : RunsWith p s xs os1 r0 a s1 r1) (h2 : RunsWith (f a) s1 ys os2 r1 b s2 r2) :
    RunsWith (p >>= f) s (xs ++ ys) (os1 ++ os2) r0 b s2 r2 := by
  intro sp hs rest orest
  obtain ⟨sp1, hs1, e1⟩ := h1 sp hs (ys ++ rest) (os2 ++ orest)
  obtain ⟨sp2, hs2, e2⟩ := h2 sp1 hs1 rest orest
  refine ⟨sp2, hs2, ?_⟩
  rw [prog_bind_eq, run_bind, List.append_assoc, List.append_assoc, e1]
  exact e2

/-- `RunsWith.bind` on `VerifierProgram.bind`. -/
theorem RunsWith.bind' {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {s s1 s2 : Fs} {xs ys : List E} {os1 os2 : List (List Opening)}
    {r0 r1 r2 : List (Digest × ℕ × ℕ)} {a : α} {b : β}
    (h1 : RunsWith p s xs os1 r0 a s1 r1) (h2 : RunsWith (f a) s1 ys os2 r1 b s2 r2) :
    RunsWith (p.bind f) s (xs ++ ys) (os1 ++ os2) r0 b s2 r2 := RunsWith.bind h1 h2

/-- `RunsTo.bind` on `VerifierProgram.bind`. -/
theorem RunsTo.bind' {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {s s1 s2 : Fs} {xs ys : List E} {a : α} {b : β} (h1 : RunsTo p s xs a s1)
    (h2 : RunsTo (f a) s1 ys b s2) : RunsTo (p.bind f) s (xs ++ ys) b s2 := RunsTo.bind h1 h2

theorem RunsWith.of_eq {α : Type} {p : VerifierProgram α} {s s' t t' : Fs} {xs xs' : List E}
    {os os' : List (List Opening)} {r r' q q' : List (Digest × ℕ × ℕ)} {a a' : α}
    (h : RunsWith p s xs os r a t q) (hs : s = s') (hx : xs = xs') (ho : os = os') (hr : r = r')
    (ha : a = a') (ht : t = t') (hq : q = q') : RunsWith p s' xs' os' r' a' t' q' := by
  subst hs hx ho hr ha ht hq; exact h

/-! ## Commitments and queries -/

/-- **A commitment** reads the root's two scalars, absorbs them, and appends the root they encode
with its shape. -/
theorem runsWith_commitP (s : Fs) (x0 x1 : E) (height width : ℕ)
    (roots : List (Digest × ℕ × ℕ)) :
    RunsWith (VerifierProgram.readCommitment height width) s [x0, x1] [] roots ()
      ((s.absorb x0 dsObserve).absorb x1 dsObserve)
      (roots ++ [(digestFromHalves (x0, x1), height, width)]) := by
  intro sp hs rest orest
  have h1 := carries_absorb hs x0 dsObserve
  have h2 := carries_absorb h1 x1 dsObserve
  refine ⟨_, h2, ?_⟩
  obtain ⟨st, p, g⟩ := sp
  have hg : g = none := hs.2.2
  subst hg
  rfl

/-- **A query** consumes one phase: one opening per position, at the position, each passing
`openOne` against commitment `i`'s root; it returns their leaves. -/
theorem runsWith_queryP (s : Fs) (roots : List (Digest × ℕ × ℕ)) {i : ℕ} {root : Digest}
    {height width : ℕ} (hi : roots[i]? = some (root, height, width)) (ps : List ℕ)
    (os : List Opening) (hl : os.length = ps.length)
    (hok : ∀ k (hk : k < ps.length) (ho : k < os.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width ps[k] os[k]) = true)
    (hidx : os.map Opening.leafIndex = ps) :
    RunsWith (VerifierProgram.queryOpenings i ps) s [] [os] roots (os.map (·.leaf)) s roots := by
  intro sp hs rest orest
  refine ⟨sp, hs, ?_⟩
  have := openPhase_eq_leaves keccak256 hl hok hidx
  simp only [Id.run] at this
  simp only [runId, VerifierProgram.queryOpenings, Compile.runWithHash, hi, List.nil_append,
      List.cons_append, bind, this]
  rfl

end
end LeanVM.Guest.B1.Whir
