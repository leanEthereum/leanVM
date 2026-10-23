/-
  LeanVM.Protocol.Compile.Cost

  The query cost of a verifier program: a budget calculus on the verifier language that bounds
  the number of hash queries of every compiled run, and the total query bound of the seeded
  compiled verifier against the random oracle that `romSound` asks for.
-/

module

public import LeanVM.Protocol.Compile.Rom.Bridge

/-!
# The query cost of a verifier program

The random-oracle theorem (`LeanVM.Protocol.Compile.Rom.Sound`, `romSound`) needs a bound `QV`
on the number of oracle queries the compiled verifier makes on *every* proof
(`IsTotalQueryBound (verifierComp σ P π) QV`). The compiled run (`LeanVM.Protocol.Compile.Run`)
makes, per node of the program,

* `read`: one query (the absorb), none if the stream is empty;
* `sample`: one query (the squeeze);
* `grind`: three queries (the base, the check and the absorb), none if the stream is empty;
* `commit`: two queries (one absorb per half of the root), none if the stream is short;
* `query i ps`: per position, one query for the leaf and one per level of its path, when the
  opening has the committed shape, and none otherwise; the run stops at the first failure;
* `ret`, `fail`: none.

A program's cost therefore depends on the heights of its commitments. `Prog.Costs height p n Q`
says: every commitment `p` reads has height at most `height`, every run of `p` costs at most `n`
when an opening of `k` positions is charged `k · (1 + height)`, and every value `p` returns
satisfies `Q`. The postcondition is what lets a cost depend on the values earlier parts of the
program return (the announced sizes, the number of query positions): the sequencing rule
(`Prog.Costs.bind`) charges the continuation only at the values the first part can return.
`Prog.CostLE height p n` is the cost without a postcondition.

* `isTotalQueryBound_run`: a program of cost `n`, run from a state whose roots have height at
  most `height`, makes at most `n` queries;
* `isTotalQueryBound_verifierComp`: the seeded compiled verifier makes at most
  `1 + |σ.steps| + n` queries on every proof (the seed's `1 + |σ.steps|` hashes, then the
  program).
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile.Rom
open OracleComp OracleSpec

@[expose] public section

/-! ## The cost calculus -/

namespace Prog

variable {α β : Type}

/-- **The cost of a program.** `Costs height p n Q`: every commitment of `p` has height at most
`height`, every run of `p` costs at most `n` (a read and a sample `1`, a proof of work `3`, a
commitment `2`, an opening of `k` positions `k · (1 + height)`), and every value `p` returns
satisfies `Q`. -/
def Costs (height : ℕ) : Prog α → ℕ → (α → Prop) → Prop
  | ret a, _, Q => Q a
  | fail, _, _ => True
  | read k, n, Q => 1 ≤ n ∧ ∀ x, Costs height (k x) (n - 1) Q
  | sample k, n, Q => 1 ≤ n ∧ ∀ c, Costs height (k c) (n - 1) Q
  | grind _ k, n, Q => 3 ≤ n ∧ Costs height k (n - 3) Q
  | commit h _ k, n, Q => h ≤ height ∧ 2 ≤ n ∧ Costs height k (n - 2) Q
  | query _ ps k, n, Q => ps.length * (1 + height) ≤ n ∧
      ∀ rows, Costs height (k rows) (n - ps.length * (1 + height)) Q

/-- **The cost of a program, without a postcondition**: every run of `p` costs at most `n`, every
commitment having height at most `height`. -/
def CostLE (height : ℕ) (p : Prog α) (n : ℕ) : Prop := Costs height p n fun _ ↦ True

namespace Costs

variable {height : ℕ}

theorem ret' {a : α} {n : ℕ} {Q : α → Prop} (h : Q a) : Costs height (ret a) n Q := h

theorem fail' {n : ℕ} {Q : α → Prop} : Costs height (fail : Prog α) n Q := trivial

/-- Monotonicity in the budget and the postcondition. -/
theorem mono {p : Prog α} {n m : ℕ} {Q R : α → Prop} (h : Costs height p n Q) (hnm : n ≤ m)
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
theorem and {p : Prog α} {n : ℕ} {Q R : α → Prop} (hQ : Costs height p n Q)
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
theorem bind {p : Prog α} {f : α → Prog β} {n m : ℕ} {Q : α → Prop} {R : β → Prop}
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
    rwa [show n - 1 + m = n + m - 1 by have := hp.1; omega] at this
  | grind b k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2
    rwa [show n - 3 + m = n + m - 3 by have := hp.1; omega] at this
  | commit ht w k ih =>
    refine ⟨hp.1, by have := hp.2.1; omega, ?_⟩
    have := ih hp.2.2
    rwa [show n - 2 + m = n + m - 2 by have := hp.2.1; omega] at this
  | query i ps k ih =>
    refine ⟨by have := hp.1; omega, fun r ↦ ?_⟩
    have := ih r (hp.2 r)
    rwa [show n - ps.length * (1 + height) + m = n + m - ps.length * (1 + height) by
      have := hp.1; omega] at this

/-- Sequencing in `do` notation. -/
theorem bind' {p : Prog α} {f : α → Prog β} {n m : ℕ} {Q : α → Prop} {R : β → Prop}
    (hp : Costs height p n Q) (hf : ∀ a, Q a → Costs height (f a) m R) :
    Costs height (p >>= f) (n + m) R := bind hp hf

/-- Sequencing against a fixed budget: the first part spends `a` of `n`, the continuation the
rest. -/
theorem seq {p : Prog α} {f : α → Prog β} {a n : ℕ} {Q : α → Prop} {R : β → Prop}
    (hp : Costs height p a Q) (hf : ∀ x, Q x → Costs height (f x) (n - a) R) (ha : a ≤ n) :
    Costs height (p >>= f) n R :=
  (bind hp hf).mono (by omega) fun _ h ↦ h

/-- A conditional costs the larger of its branches. -/
theorem ite {c : Prop} [Decidable c] {p q : Prog α} {n : ℕ} {Q : α → Prop}
    (hp : c → Costs height p n Q) (hq : ¬ c → Costs height q n Q) :
    Costs height (if c then p else q) n Q := by
  split
  · exact hp ‹_›
  · exact hq ‹_›

theorem pure0 (a : α) : Costs height (pure a : Prog α) 0 fun _ ↦ True := trivial

theorem readE : Costs height Prog.readE 1 fun _ ↦ True := ⟨le_rfl, fun _ ↦ trivial⟩

theorem sampleE : Costs height Prog.sampleE 1 fun _ ↦ True := ⟨le_rfl, fun _ ↦ trivial⟩

/-- `n` reads cost `n`, and return `n` scalars. -/
theorem readN : ∀ n, Costs height (Prog.readN n) n fun xs ↦ xs.length = n
  | 0 => rfl
  | n + 1 => by
    have h := bind (height := height) readE fun x (_ : True) ↦
      bind (m := 0) (readN n) fun xs (hxs : xs.length = n) ↦
        (show Costs height (ret (x :: xs)) 0 fun ys ↦ ys.length = n + 1 by
          show (x :: xs).length = n + 1
          simp [hxs])
    exact h.mono (by omega) fun _ h ↦ h

/-- `n` samples cost `n`, and return `n` challenges. -/
theorem sampleN : ∀ n, Costs height (Prog.sampleN n) n fun xs ↦ xs.length = n
  | 0 => rfl
  | n + 1 => by
    have h := bind (height := height) sampleE fun x (_ : True) ↦
      bind (m := 0) (sampleN n) fun xs (hxs : xs.length = n) ↦
        (show Costs height (ret (x :: xs)) 0 fun ys ↦ ys.length = n + 1 by
          show (x :: xs).length = n + 1
          simp [hxs])
    exact h.mono (by omega) fun _ h ↦ h

theorem grindP (bits : ℕ) : Costs height (Prog.grindP bits) 3 fun _ ↦ True :=
  ⟨le_rfl, trivial⟩

theorem commitP {ht : ℕ} (w : ℕ) (hht : ht ≤ height) :
    Costs height (Prog.commitP ht w) 2 fun _ ↦ True := ⟨hht, le_rfl, trivial⟩

theorem queryP (i : ℕ) (ps : List ℕ) :
    Costs height (Prog.queryP i ps) (ps.length * (1 + height)) fun _ ↦ True :=
  ⟨le_rfl, fun _ ↦ trivial⟩

theorem require (c : Prop) [Decidable c] {n : ℕ} :
    Costs height (Prog.require c) n fun _ ↦ c := by
  unfold Prog.require
  split
  · exact ‹c›
  · trivial

end Costs

namespace CostLE

variable {height : ℕ}

theorem ret' (a : α) (n : ℕ) : CostLE height (ret a) n := trivial

theorem fail' (n : ℕ) : CostLE height (fail : Prog α) n := trivial

theorem mono {p : Prog α} {n m : ℕ} (h : CostLE height p n) (hnm : n ≤ m) :
    CostLE height p m := Costs.mono h hnm fun _ h ↦ h

/-- Sequencing: the costs add. -/
theorem bind {p : Prog α} {f : α → Prog β} {n m : ℕ} (hp : CostLE height p n)
    (hf : ∀ a, CostLE height (f a) m) : CostLE height (p.bind f) (n + m) :=
  Costs.bind hp fun a _ ↦ hf a

theorem read {k : E → Prog α} {n : ℕ} (h : ∀ x, CostLE height (k x) n) :
    CostLE height (Prog.read k) (n + 1) :=
  ⟨by omega, fun x ↦ by rw [Nat.add_sub_cancel]; exact h x⟩

theorem sample {k : E → Prog α} {n : ℕ} (h : ∀ c, CostLE height (k c) n) :
    CostLE height (Prog.sample k) (n + 1) :=
  ⟨by omega, fun x ↦ by rw [Nat.add_sub_cancel]; exact h x⟩

theorem grind (bits : ℕ) {k : Prog α} {n : ℕ} (h : CostLE height k n) :
    CostLE height (Prog.grind bits k) (n + 3) := ⟨by omega, by rw [Nat.add_sub_cancel]; exact h⟩

theorem commit {ht : ℕ} (w : ℕ) {k : Prog α} {n : ℕ} (hht : ht ≤ height)
    (h : CostLE height k n) : CostLE height (Prog.commit ht w k) (n + 2) :=
  ⟨hht, by omega, by rw [Nat.add_sub_cancel]; exact h⟩

theorem query (i : ℕ) (ps : List ℕ) {k : List (List K) → Prog α} {n : ℕ}
    (h : ∀ rows, CostLE height (k rows) n) :
    CostLE height (Prog.query i ps k) (n + ps.length * (1 + height)) :=
  ⟨by omega, fun r ↦ by rw [Nat.add_sub_cancel]; exact h r⟩

theorem ite {c : Prop} [Decidable c] {p q : Prog α} {n : ℕ} (hp : c → CostLE height p n)
    (hq : ¬ c → CostLE height q n) : CostLE height (if c then p else q) n :=
  Costs.ite hp hq

end CostLE

end Prog

/-! ## The compiled run's queries -/

section Run

/-- A query to the random oracle, then a continuation of `n` queries, makes `n + 1`. -/
theorem isTotalQueryBound_queryH_bind {β : Type} (x : Bytes)
    {f : Digest → OracleComp HashSpec β} {n : ℕ} (h : ∀ d, IsTotalQueryBound (f d) n) :
    IsTotalQueryBound (queryH x >>= f) (n + 1) :=
  isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun d ↦ by simpa using h d⟩

theorem isTotalQueryBound_pure' {β : Type} (b : β) (n : ℕ) :
    IsTotalQueryBound (pure b : OracleComp HashSpec β) n := trivial

/-- A climb up a path makes one query per level. -/
theorem isTotalQueryBound_climb :
    ∀ (node : Digest) (q : ℕ) (path : List Digest),
      IsTotalQueryBound (climb queryH node q path) path.length
  | _, _, [] => trivial
  | node, q, s :: ss => by
    simp only [climb, List.length_cons]
    split <;> exact isTotalQueryBound_queryH_bind _ fun p ↦ isTotalQueryBound_climb p _ ss

/-- An opening against a root of height `ht` makes at most `1 + ht` queries. -/
theorem isTotalQueryBound_openOne (root : Digest) (ht w q : ℕ) (o : Opening) :
    IsTotalQueryBound (openOne queryH root ht w q o) (1 + ht) := by
  unfold openOne
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
      IsTotalQueryBound (openAll queryH root ht w ps os) (ps.length * (1 + ht))
  | [], _ => trivial
  | _ :: _, [] => trivial
  | q :: qs, o :: os => by
    simp only [openAll]
    rw [show (q :: qs).length * (1 + ht) = (1 + ht) + qs.length * (1 + ht) by
      simp only [List.length_cons]; ring]
    refine isTotalQueryBound_bind (isTotalQueryBound_openOne root ht w q o) fun b ↦ ?_
    split
    · exact (isTotalQueryBound_bind (isTotalQueryBound_openAll root ht w qs os)
        fun _ ↦ isTotalQueryBound_pure' _ 0).mono (by omega)
    · trivial

/-- **The compiled run's queries.** A program of cost `n` at `height`, run from a state whose
roots have height at most `height`, makes at most `n` queries. -/
theorem isTotalQueryBound_run {α : Type} (height : ℕ) :
    ∀ (p : Prog α) (s : St) (n : ℕ) (Q : α → Prop), p.Costs height n Q →
      (∀ r ∈ s.roots, r.2.1 ≤ height) → IsTotalQueryBound (run queryH p s) n
  | .ret a, s, n, Q, _, _ => trivial
  | .fail, s, n, Q, _, _ => trivial
  | .read k, s, n, Q, hp, hs => by
    simp only [run]
    split
    · trivial
    · rw [show n = (n - 1) + 1 by have := hp.1; omega]
      exact isTotalQueryBound_queryH_bind _ fun cv ↦
        isTotalQueryBound_run height _ _ _ Q (hp.2 _) hs
  | .sample k, s, n, Q, hp, hs => by
    simp only [run]
    rw [show n = (n - 1) + 1 by have := hp.1; omega]
    exact isTotalQueryBound_queryH_bind _ fun cv ↦
      isTotalQueryBound_run height _ _ _ Q (hp.2 _) hs
  | .grind bits k, s, n, Q, hp, hs => by
    simp only [run]
    split
    · trivial
    · rw [show n = (((n - 3) + 1) + 1) + 1 by have := hp.1; omega]
      refine isTotalQueryBound_queryH_bind _ fun base ↦ isTotalQueryBound_queryH_bind _
        fun d ↦ isTotalQueryBound_queryH_bind _ fun cv ↦ ?_
      split
      · exact isTotalQueryBound_run height _ _ _ Q hp.2 hs
      · trivial
  | .commit ht w k, s, n, Q, hp, hs => by
    simp only [run]
    split
    · rw [show n = ((n - 2) + 1) + 1 by have := hp.2.1; omega]
      refine isTotalQueryBound_queryH_bind _ fun cv0 ↦ isTotalQueryBound_queryH_bind _
        fun cv1 ↦ ?_
      split
      · refine isTotalQueryBound_run height _ _ _ Q hp.2.2 ?_
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hs r hr
        · rw [List.mem_singleton.mp hr]; exact hp.1
      · trivial
    · trivial
  | .query i ps k, s, n, Q, hp, hs => by
    simp only [run]
    split
    · trivial
    · rename_i root ht w hroot
      have hht : ht ≤ height := hs _ (List.mem_of_getElem? hroot)
      rw [show n = ps.length * (1 + height) + (n - ps.length * (1 + height)) by
        have := hp.1; omega]
      refine isTotalQueryBound_bind ((isTotalQueryBound_openAll root ht w ps s.openings).mono
        (Nat.mul_le_mul_left _ (by omega))) fun o ↦ ?_
      split
      · exact isTotalQueryBound_run height _ _ _ Q (hp.2 _) hs
      · trivial

/-- A program of cost `n`, run on a proof from any seed, makes at most `n` queries. -/
theorem isTotalQueryBound_runProof {P : Prog Bool} {height n : ℕ} (hP : P.CostLE height n)
    (seed : Digest) (π : Proof) : IsTotalQueryBound (runProof queryH P seed π) n := by
  unfold runProof
  rw [← Nat.add_zero n]
  refine isTotalQueryBound_bind (isTotalQueryBound_run height P _ n _ hP
    (by intro r hr; simp at hr)) fun o ↦ ?_
  split <;> trivial

/-- The seeding steps make one query each. -/
theorem isTotalQueryBound_foldlM_seed :
    ∀ (as : List (Bytes × Bytes)) (d : Digest),
      IsTotalQueryBound (as.foldlM (fun d a ↦ queryH (Seed.input a d)) d) as.length
  | [], d => trivial
  | a :: as, d => by
    simp only [List.foldlM_cons, List.length_cons]
    exact isTotalQueryBound_queryH_bind _ fun d' ↦ isTotalQueryBound_foldlM_seed as d'

/-- The seed makes `1 + |σ.steps|` queries. -/
theorem isTotalQueryBound_seedRun (σ : Seed) :
    IsTotalQueryBound (σ.run queryH) (1 + σ.steps.length) := by
  unfold Seed.run
  rw [Nat.add_comm]
  exact isTotalQueryBound_queryH_bind _ fun d ↦ isTotalQueryBound_foldlM_seed _ d

/-- **The query bound of the compiled verifier.** A verifier program of cost `n` at `height`
makes, seeded by `σ`, at most `1 + |σ.steps| + n` queries to the random oracle on every proof:
the hypothesis `hV` of `romSound`. -/
theorem isTotalQueryBound_verifierComp {P : Prog Bool} {height n : ℕ} (hP : P.CostLE height n)
    (σ : Seed) (π : Proof) :
    IsTotalQueryBound (verifierComp σ P π) (1 + σ.steps.length + n) :=
  isTotalQueryBound_bind (isTotalQueryBound_seedRun σ) fun seed ↦
    isTotalQueryBound_runProof hP seed π

end Run

end
end LeanVM.Protocol.Compile
