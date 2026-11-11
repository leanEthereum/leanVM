/-
  LeanVM.Protocol.Compile.Cost

  The query cost of a verifier program: a budget calculus on the verifier language that bounds
  the number of hash queries of every compiled run, and the total query bound of the seeded
  compiled verifier against the random oracle that `romSound` asks for.
-/

module

public import LeanVM.Protocol.Compile.Rom.Bridge
public import LeanVM.Protocol.WithHash

/-!
# The query cost of a verifier program

The random-oracle theorem (`LeanVM.Protocol.Compile.Rom.Sound`, `romSound`) needs a bound `QV`
on the number of oracle queries the compiled verifier makes on *every* proof
(`IsTotalQueryBound (verifierComp σ P π) QV`). The compiled run (`LeanVM.Protocol.Compile.run`)
makes, per node of the program,

* `read`: one absorption, which permutes the sponge (one query) when four scalars wait;
* `sample`: one permutation;
* `grind`: one absorption, then one permutation;
* `commit`: two absorptions;
* `query i ps`: per position, one hash query for the leaf and one per level of its path, when the
  opening has the committed shape, and none otherwise; the run stops at the first failure;
* `ret`, `fail`: none.

A permutation forced by an absorption empties the four waiting scalars, so at most one
absorption in four forces one. The cost is counted in quarters of a query: an absorption costs
`1` (a quarter of the permutation it may force), a permutation `4`, a hash query `4`. So a read
costs `1`, a sample `4`, a proof of work `5`, a commitment `2`, and an opening of `k` positions
`4 · k · (1 + height)`.

A program's cost depends on the heights of its commitments. `VerifierProgram.Costs height p n Q`
says: every commitment `p` reads has height at most `height`, every run of `p` costs at most `n`
quarters, and every value `p` returns satisfies `Q`. The postcondition is what lets a cost
depend on the values earlier parts of the program return (the announced sizes, the number of
query positions): the sequencing rule (`VerifierProgram.Costs.bind`) charges the continuation only
at the values the first part can return. `VerifierProgram.CostLE height p n` is the cost without a
postcondition.

* `isTotalQueryBound_run`: a program of cost `n`, run from a state whose roots have height at
  most `height` and whose sponge has `k ≤ 4` scalars waiting, makes at most `(n + k) / 4`
  queries (the waiting scalars' quarters are paid by the permutation that empties them);
* `isTotalQueryBound_verifierComp`: the seeded compiled verifier makes at most
  `|σ.hs| + 1 + n / 4` queries on every proof (the seed's hashes and permutation, then the
  program).
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile.Rom
open OracleComp OracleSpec

@[expose] public section

/-! ## The cost calculus -/

namespace VerifierProgram

variable {α β : Type}

/-- The cost of opening `k` positions of a commitment of height at most `height`, in quarters:
`k · (1 + height)` hash queries. -/
def openCost (height k : ℕ) : ℕ := 4 * (k * (1 + height))

/-- **The cost of a program**, in quarters of a query. `Costs height p n Q`: every commitment of
`p` has height at most `height`, every run of `p` costs at most `n` (a read `1`, a sample `4`, a
proof of work `5`, a commitment `2`, an opening of `k` positions `openCost height k`), and every
value `p` returns satisfies `Q`. -/
def Costs (height : ℕ) : VerifierProgram α → ℕ → (α → Prop) → Prop
  | ret a, _, Q => Q a
  | fail, _, _ => True
  | read k, n, Q => 1 ≤ n ∧ ∀ x, Costs height (k x) (n - 1) Q
  | sample k, n, Q => 4 ≤ n ∧ ∀ c, Costs height (k c) (n - 4) Q
  | grind _ k, n, Q => 5 ≤ n ∧ Costs height k (n - 5) Q
  | commit h _ k, n, Q => h ≤ height ∧ 2 ≤ n ∧ Costs height k (n - 2) Q
  | query _ ps k, n, Q => openCost height ps.length ≤ n ∧
      ∀ rows, Costs height (k rows) (n - openCost height ps.length) Q

/-- **The cost of a program, without a postcondition**: every run of `p` costs at most `n`, every
commitment having height at most `height`. -/
def CostLE (height : ℕ) (p : VerifierProgram α) (n : ℕ) : Prop := Costs height p n fun _ ↦ True

namespace Costs

variable {height : ℕ}

theorem ret' {a : α} {n : ℕ} {Q : α → Prop} (h : Q a) : Costs height (ret a) n Q := h

theorem fail' {n : ℕ} {Q : α → Prop} : Costs height (fail : VerifierProgram α) n Q := trivial

/-- Monotonicity in the budget and the postcondition. -/
theorem mono {p : VerifierProgram α} {n m : ℕ} {Q R : α → Prop} (h : Costs height p n Q) (hnm
    : n ≤ m)
    (hQR : ∀ a, Q a → R a) : Costs height p m R := by
  induction p generalizing n m with
  | ret a => exact hQR a h
  | fail => trivial
  | read k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | sample k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | grind b k ih => exact ⟨by have := h.1; omega, ih h.2 (by omega)⟩
  | commit ht w k ih => exact ⟨h.1, by have := h.2.1; omega, ih h.2.2 (by omega)⟩
  | query i ps k ih => exact ⟨by have := h.1; omega, fun r ↦ ih r (h.2 r) (by omega)⟩

/-- Two postconditions at one budget. -/
theorem and {p : VerifierProgram α} {n : ℕ} {Q R : α → Prop} (hQ : Costs height p n Q)
    (hR : Costs height p n R) : Costs height p n fun a ↦ Q a ∧ R a := by
  induction p generalizing n with
  | ret a => exact ⟨hQ, hR⟩
  | fail => trivial
  | read k ih => exact ⟨hQ.1, fun x ↦ ih x (hQ.2 x) (hR.2 x)⟩
  | sample k ih => exact ⟨hQ.1, fun x ↦ ih x (hQ.2 x) (hR.2 x)⟩
  | grind b k ih => exact ⟨hQ.1, ih hQ.2 hR.2⟩
  | commit ht w k ih => exact ⟨hQ.1, hQ.2.1, ih hQ.2.2 hR.2.2⟩
  | query i ps k ih => exact ⟨hQ.1, fun r ↦ ih r (hQ.2 r) (hR.2 r)⟩

/-- **Sequencing**: the costs add, the continuation charged only at the values the first part
returns. -/
theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {n m : ℕ} {Q : α → Prop} {R : β
    → Prop}
    (hp : Costs height p n Q) (hf : ∀ a, Q a → Costs height (f a) m R) :
    Costs height (p.bind f) (n + m) R := by
  induction p generalizing n with
  | ret a => exact (hf a hp).mono (by omega) fun _ h ↦ h
  | fail => trivial
  | read k ih =>
    refine ⟨by have := hp.1; omega, fun x ↦ ?_⟩
    have := ih x (hp.2 x)
    rwa [show n - 1 + m = n + m - 1 by have := hp.1; omega] at this
  | sample k ih =>
    refine ⟨by have := hp.1; omega, fun x ↦ ?_⟩
    have := ih x (hp.2 x)
    rwa [show n - 4 + m = n + m - 4 by have := hp.1; omega] at this
  | grind b k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2
    rwa [show n - 5 + m = n + m - 5 by have := hp.1; omega] at this
  | commit ht w k ih =>
    refine ⟨hp.1, by have := hp.2.1; omega, ?_⟩
    have := ih hp.2.2
    rwa [show n - 2 + m = n + m - 2 by have := hp.2.1; omega] at this
  | query i ps k ih =>
    refine ⟨by have := hp.1; omega, fun r ↦ ?_⟩
    have := ih r (hp.2 r)
    rwa [show n - openCost height ps.length + m = n + m - openCost height ps.length by
      have := hp.1; omega] at this

/-- Sequencing in `do` notation. -/
theorem bind' {p : VerifierProgram α} {f : α → VerifierProgram β} {n m : ℕ} {Q : α → Prop} {R : β
    → Prop}
    (hp : Costs height p n Q) (hf : ∀ a, Q a → Costs height (f a) m R) :
    Costs height (p >>= f) (n + m) R := bind hp hf

/-- Sequencing against a fixed budget: the first part spends `a` of `n`, the continuation the
rest. -/
theorem seq {p : VerifierProgram α} {f : α → VerifierProgram β} {a n : ℕ} {Q : α → Prop} {R : β
    → Prop}
    (hp : Costs height p a Q) (hf : ∀ x, Q x → Costs height (f x) (n - a) R) (ha : a ≤ n) :
    Costs height (p >>= f) n R :=
  (bind hp hf).mono (by omega) fun _ h ↦ h

/-- A conditional costs the larger of its branches. -/
theorem ite {c : Prop} [Decidable c] {p q : VerifierProgram α} {n : ℕ} {Q : α → Prop}
    (hp : c → Costs height p n Q) (hq : ¬ c → Costs height q n Q) :
    Costs height (if c then p else q) n Q := by
  split
  · exact hp ‹_›
  · exact hq ‹_›

theorem pure0 (a : α) : Costs height (pure a : VerifierProgram α) 0 fun _ ↦ True := trivial

theorem readE : Costs height VerifierProgram.readScalar 1 fun _ ↦ True := ⟨le_rfl, fun _ ↦ trivial⟩

theorem sampleE : Costs height VerifierProgram.sampleChallenge 4 fun _ ↦ True := ⟨le_rfl, fun _ ↦
    trivial⟩

/-- `n` reads cost `n`, and return `n` scalars. -/
theorem readN : ∀ n, Costs height (VerifierProgram.readScalars n) n fun xs ↦ xs.length = n
  | 0 => rfl
  | n + 1 => by
    have h := bind (height := height) readE fun x (_ : True) ↦
      bind (m := 0) (readN n) fun xs (hxs : xs.length = n) ↦
        (show Costs height (ret (x :: xs)) 0 fun ys ↦ ys.length = n + 1 by
          show (x :: xs).length = n + 1
          simp [hxs])
    exact h.mono (by omega) fun _ h ↦ h

/-- `n` samples cost `4n`, and return `n` challenges. -/
theorem sampleN : ∀ n, Costs height (VerifierProgram.sampleChallenges n) (4 * n) fun xs ↦
    xs.length = n
  | 0 => rfl
  | n + 1 => by
    have h := bind (height := height) sampleE fun x (_ : True) ↦
      bind (m := 0) (sampleN n) fun xs (hxs : xs.length = n) ↦
        (show Costs height (ret (x :: xs)) 0 fun ys ↦ ys.length = n + 1 by
          show (x :: xs).length = n + 1
          simp [hxs])
    exact h.mono (by omega) fun _ h ↦ h

theorem grindP (bits : ℕ) : Costs height (VerifierProgram.grindProofOfWork bits) 5 fun _ ↦ True := by
  unfold VerifierProgram.grindProofOfWork
  split
  · trivial
  · exact ⟨le_rfl, trivial⟩

theorem commitP {ht : ℕ} (w : ℕ) (hht : ht ≤ height) :
    Costs height (VerifierProgram.readCommitment ht w) 2 fun _ ↦ True := ⟨hht, le_rfl, trivial⟩

theorem queryP (i : ℕ) (ps : List ℕ) :
    Costs height (VerifierProgram.queryOpenings i ps) (openCost height ps.length) fun _ ↦ True :=
  ⟨le_rfl, fun _ ↦ trivial⟩

theorem require (c : Prop) [Decidable c] {n : ℕ} :
    Costs height (VerifierProgram.require c) n fun _ ↦ c := by
  unfold VerifierProgram.require
  split
  · exact ‹c›
  · trivial

end Costs

namespace CostLE

variable {height : ℕ}

theorem ret' (a : α) (n : ℕ) : CostLE height (ret a) n := trivial

theorem fail' (n : ℕ) : CostLE height (fail : VerifierProgram α) n := trivial

theorem read {k : E → VerifierProgram α} {n : ℕ} (h : ∀ x, CostLE height (k x) n) :
    CostLE height (VerifierProgram.read k) (n + 1) :=
  ⟨by omega, fun x ↦ by rw [Nat.add_sub_cancel]; exact h x⟩

theorem sample {k : E → VerifierProgram α} {n : ℕ} (h : ∀ c, CostLE height (k c) n) :
    CostLE height (VerifierProgram.sample k) (n + 4) :=
  ⟨by omega, fun x ↦ by rw [Nat.add_sub_cancel]; exact h x⟩

theorem commit {ht : ℕ} (w : ℕ) {k : VerifierProgram α} {n : ℕ} (hht : ht ≤ height)
    (h : CostLE height k n) : CostLE height (VerifierProgram.commit ht w k) (n + 2) :=
  ⟨hht, by omega, by rw [Nat.add_sub_cancel]; exact h⟩

theorem query (i : ℕ) (ps : List ℕ) {k : List (List K) → VerifierProgram α} {n : ℕ}
    (h : ∀ rows, CostLE height (k rows) n) :
    CostLE height (VerifierProgram.query i ps k) (n + openCost height ps.length) :=
  ⟨by omega, fun r ↦ by rw [Nat.add_sub_cancel]; exact h r⟩

end CostLE

end VerifierProgram

/-! ## The compiled run's queries -/

section Run

/-- A query to the hash, then a continuation of `n` queries, makes `n + 1`. -/
theorem isTotalQueryBound_queryH_bind {β : Type} (x : Bytes)
    {f : Digest → OracleComp KeccakCalls β} {n : ℕ} (h : ∀ d, IsTotalQueryBound (f d) n) :
    IsTotalQueryBound (callKeccak256 x >>= f) (n + 1) :=
  isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun d ↦ by simpa using h d⟩

/-- A query to the permutation, then a continuation of `n` queries, makes `n + 1`. -/
theorem isTotalQueryBound_queryF_bind {β : Type} (s : KeccakState)
    {f : KeccakState → OracleComp KeccakCalls β} {n : ℕ} (h : ∀ d, IsTotalQueryBound (f d) n) :
    IsTotalQueryBound (callKeccakF1600 s >>= f) (n + 1) :=
  isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun d ↦ by simpa using h d⟩

theorem isTotalQueryBound_pure' {β : Type} (b : β) (n : ℕ) :
    IsTotalQueryBound (pure b : OracleComp KeccakCalls β) n := trivial

/-- A climb up a path makes one query per level. -/
theorem isTotalQueryBound_climb :
    ∀ (node : Digest) (q : ℕ) (path : List Digest),
      IsTotalQueryBound (climbWithHash callKeccak256 node q path) path.length
  | _, _, [] => trivial
  | node, q, s :: ss => by
    simp only [climbWithHash, List.length_cons]
    split <;> exact isTotalQueryBound_queryH_bind _ fun p ↦ isTotalQueryBound_climb p _ ss

/-- An opening against a root of height `ht` makes at most `1 + ht` queries. -/
theorem isTotalQueryBound_openOne (root : Digest) (ht w q : ℕ) (o : Opening) :
    IsTotalQueryBound (openOneWithHash callKeccak256 root ht w q o) (1 + ht) := by
  unfold openOneWithHash
  split
  · rename_i hw
    rw [show 1 + ht = (o.path.length + 0) + 1 by omega]
    exact isTotalQueryBound_queryH_bind _ fun d ↦
      isTotalQueryBound_bind (isTotalQueryBound_climb d q o.path) fun _ ↦
        isTotalQueryBound_pure' _ 0
  · trivial

/-- Opening `ps` against a root of height `ht` makes at most `|ps| · (1 + ht)` queries. -/
theorem isTotalQueryBound_openAll (root : Digest) (ht w : ℕ) :
    ∀ (ps : List ℕ) (os : List Opening),
      IsTotalQueryBound (openAllWithHash callKeccak256 root ht w ps os) (ps.length * (1 + ht))
  | [], _ => trivial
  | _ :: _, [] => trivial
  | q :: qs, o :: os => by
    simp only [openAllWithHash]
    rw [show (q :: qs).length * (1 + ht) = (1 + ht) + qs.length * (1 + ht) by
      simp only [List.length_cons]; ring]
    refine isTotalQueryBound_bind (isTotalQueryBound_openOne root ht w q o) fun b ↦ ?_
    split
    · exact (isTotalQueryBound_bind (isTotalQueryBound_openAll root ht w qs os)
        fun _ ↦ isTotalQueryBound_pure' _ 0).mono (by omega)
    · trivial

/-- Opening a phase at `ps` against a root of height `ht` makes at most `|ps| · (1 + ht)`
queries. -/
theorem isTotalQueryBound_openPhase (root : Digest) (ht w : ℕ) (ps : List ℕ)
    (phase : List Opening) :
    IsTotalQueryBound (openPhaseWithHash callKeccak256 root ht w ps phase)
      (ps.length * (1 + ht)) := by
  unfold openPhaseWithHash
  split
  · rw [← Nat.add_zero (ps.length * (1 + ht))]
    exact isTotalQueryBound_bind (isTotalQueryBound_openAll root ht w ps phase) fun o ↦ by
      split <;> exact isTotalQueryBound_pure' _ 0
  · trivial

/-- An absorption followed by a continuation: the continuation runs at the sponge with the
scalar appended, after one permutation when four scalars wait. -/
theorem absorb_bind {β : Type} (sp : Sponge) (x : E) (tag : ℕ)
    (f : Sponge → OracleComp KeccakCalls β) :
    (Compile.absorb callKeccakF1600 sp x tag >>= f) =
      if sp.pending.length = 4 then callKeccakF1600 (duplexInput sp) >>= fun st ↦ f ⟨st, [(x, tag)]⟩
      else f { sp with pending := sp.pending ++ [(x, tag)] } := by
  unfold Compile.absorb duplex
  split
  · rename_i h4
    simp only [rateScalars] at h4
    simp [h4]
  · rename_i h4
    simp only [rateScalars] at h4
    simp [h4]

/-- A squeeze followed by a continuation: one permutation. -/
theorem squeeze_bind {β : Type} (sp : Sponge) (f : E × Sponge → OracleComp KeccakCalls β) :
    (squeeze callKeccakF1600 sp >>= f) = callKeccakF1600 (duplexInput sp) >>= fun st ↦ f (challengeOf st, ⟨st, []⟩) := by
  unfold squeeze duplex
  simp

/-- **An absorption's queries.** An absorption costs a quarter: a continuation of cost `n - 1`
from every sponge, run from the sponge after the absorption, gives cost `n` from the sponge
before it. -/
theorem isTotalQueryBound_absorb {β : Type} (sp : Sponge) (hk : sp.pending.length ≤ 4) (x : E)
    (tag : ℕ) (g : Sponge → OracleComp KeccakCalls β) (n : ℕ) (hn : 1 ≤ n)
    (hg : ∀ sp' : Sponge, sp'.pending.length ≤ 4 →
      IsTotalQueryBound (g sp') ((n - 1 + sp'.pending.length) / 4)) :
    IsTotalQueryBound (Compile.absorb callKeccakF1600 sp x tag >>= g) ((n + sp.pending.length) / 4) := by
  rw [absorb_bind]
  split
  · rename_i h4
    refine (isTotalQueryBound_queryF_bind (n := (n - 1 + 1) / 4) _ fun st ↦ ?_).mono ?_
    · simpa using hg ⟨st, [(x, tag)]⟩ (by simp)
    · omega
  · rename_i h4
    refine (hg _ (by simp; omega)).mono ?_
    simp only [List.length_append, List.length_singleton]
    omega

/-- **The compiled run's queries.** A program of cost `n` at `height`, run from a state whose
roots have height at most `height` and whose sponge has at most four scalars waiting, makes at
most `(n + k) / 4` queries, `k` the number of waiting scalars. -/
theorem isTotalQueryBound_run {α : Type} (height : ℕ) :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (n : ℕ) (Q : α → Prop), p.Costs
        height n Q →
      (∀ r ∈ s.roots, r.2.1 ≤ height) → s.sponge.pending.length ≤ 4 →
      IsTotalQueryBound (runWithHash callKeccak256 callKeccakF1600 p s) ((n + s.sponge.pending.length) / 4)
  | .ret a, s, n, Q, _, _, _ => trivial
  | .fail, s, n, Q, _, _, _ => trivial
  | .read k, s, n, Q, hp, hs, hk => by
    simp only [runWithHash]
    split
    · trivial
    · rename_i x xs _
      exact isTotalQueryBound_absorb _ hk _ _ _ n hp.1 fun sp' hsp' ↦
        isTotalQueryBound_run height (k x) _ (n - 1) Q (hp.2 x) hs hsp'
  | .sample k, s, n, Q, hp, hs, hk => by
    simp only [runWithHash]
    rw [squeeze_bind]
    refine (isTotalQueryBound_queryF_bind (n := (n - 4) / 4) _ fun st ↦ ?_).mono ?_
    · simpa using isTotalQueryBound_run height (k (challengeOf st))
        { s with sponge := ⟨st, []⟩ } (n - 4) Q (hp.2 _) hs (by simp)
    · have := hp.1
      omega
  | .grind bits k, s, n, Q, hp, hs, hk => by
    simp only [runWithHash]
    split
    · trivial
    · rename_i nn xs _
      have h5 := hp.1
      refine isTotalQueryBound_absorb _ hk _ _ _ n (by omega) fun sp' hsp' ↦ ?_
      rw [squeeze_bind]
      refine (isTotalQueryBound_queryF_bind (n := (n - 5) / 4) _ fun st ↦ ?_).mono ?_
      · dsimp only
        split
        · simpa using isTotalQueryBound_run height k { s with sponge := ⟨st, []⟩, stream := xs }
            (n - 5) Q hp.2 hs (by simp)
        · trivial
      · omega
  | .commit ht w k, s, n, Q, hp, hs, hk => by
    simp only [runWithHash]
    split
    · rename_i x0 x1 xs _
      have h2 := hp.2.1
      refine isTotalQueryBound_absorb _ hk _ _ _ n (by omega) fun sp0 hsp0 ↦ ?_
      refine isTotalQueryBound_absorb _ hsp0 _ _ _ (n - 1) (by omega) fun sp1 hsp1 ↦ ?_
      split
      · rename_i root _
        refine (isTotalQueryBound_run height k _ (n - 2) Q hp.2.2 ?_ hsp1).mono
          (by dsimp only; omega)
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hs r hr
        · rw [List.mem_singleton.mp hr]; exact hp.1
      · trivial
    · trivial
  | .query i ps k, s, n, Q, hp, hs, hk => by
    simp only [runWithHash]
    split
    · next root ht w phase rest hroot hopen =>
      have hht : ht ≤ height := hs _ (List.mem_of_getElem? hroot)
      have hle : VerifierProgram.openCost height ps.length ≤ n := hp.1
      rw [show (n + s.sponge.pending.length) / 4 = ps.length * (1 + height) +
          (n - VerifierProgram.openCost height ps.length + s.sponge.pending.length) / 4 by
        unfold VerifierProgram.openCost at hle ⊢; omega]
      refine isTotalQueryBound_bind ((isTotalQueryBound_openPhase root ht w ps phase).mono
        (Nat.mul_le_mul_left _ (by omega))) fun o ↦ ?_
      split
      · exact isTotalQueryBound_run height _ _ _ Q (hp.2 _) hs hk
      · trivial
    · trivial

/-- A program of cost `n`, run on a proof from any seed, makes at most `n / 4` queries. -/
theorem isTotalQueryBound_runProof {P : VerifierProgram Bool} {height n : ℕ} (hP : P.CostLE
    height n)
    (seed : KeccakState) (π : Proof) : IsTotalQueryBound (runProofWithHash callKeccak256 callKeccakF1600 P seed π) (n / 4) := by
  unfold runProofWithHash
  rw [← Nat.add_zero (n / 4)]
  refine isTotalQueryBound_bind ((isTotalQueryBound_run height P _ n _ hP
    (by intro r hr; simp at hr) (by simp)).mono (by simp)) fun o ↦ ?_
  split <;> trivial

/-- The seeding's hash steps make one query each. -/
theorem isTotalQueryBound_hsRun :
    ∀ (fs : List (List Digest → Bytes)) (ds : List Digest),
      IsTotalQueryBound (Seed.hsRun callKeccak256 fs ds) fs.length
  | [], ds => trivial
  | f :: fs, ds => by
    simp only [Seed.hsRun, List.length_cons]
    exact isTotalQueryBound_queryH_bind _ fun d ↦ isTotalQueryBound_hsRun fs _

/-- The seed makes `|σ.hs| + 1` queries. -/
theorem isTotalQueryBound_seedRun (σ : Seed) :
    IsTotalQueryBound (σ.run callKeccak256 callKeccakF1600) (σ.hs.length + 1) := by
  unfold Seed.run
  exact isTotalQueryBound_bind (isTotalQueryBound_hsRun _ _) fun ds ↦
    isTotalQueryBound_queryF_bind (n := 0) _ fun _ ↦ isTotalQueryBound_pure' _ 0

/-- **The query bound of the compiled verifier.** A verifier program of cost `n` at `height`
makes, seeded by `σ`, at most `|σ.hs| + 1 + n / 4` queries to the random oracles on every proof:
the hypothesis `hV` of `romSound`. -/
theorem isTotalQueryBound_verifierComp {P : VerifierProgram Bool} {height n : ℕ} (hP : P.CostLE
    height n)
    (σ : Seed) (π : Proof) :
    IsTotalQueryBound (verifierComp σ P π) (σ.hs.length + 1 + n / 4) :=
  isTotalQueryBound_bind (isTotalQueryBound_seedRun σ) fun seed ↦
    isTotalQueryBound_runProof hP seed π

end Run

end
end LeanVM.Protocol.Compile
