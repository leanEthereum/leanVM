/-
  LeanVM.Arithmetization.Soundness.Lookup

  The offline memory-checking argument behind the two lookup channels: a list of nonzero counts
  closed under multiplication by `g` and shorter than the order of `g` is empty, so a balanced
  read/write pair with nonzero read counts reads only keys its seed holds.
-/

module

public import LeanVM.Parameters.Generator
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

/-!
# Offline memory checking

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`. Specification Lemma 6.3, Theorem 6.4 and
Corollary 6.5 (`doc/leanvm/body/06-bus-interactions.tex`, §6.2 "Flush rules" and §6.3), stated over
abstract lists so that the memory pair and the bytecode pair (`Soundness.MemChannel`,
`Soundness.BytecodeChannel`) are two instances of one argument: the counting argument of the
lookup theorem. It uses only the field `K` and its generator `g` (`Parameters.Field`,
`Parameters.Generator`), nothing about the witness.

**Lemma 6.3** (`eq_nil_of_perm_map_mul_g`): a list `P` of nonzero elements of `K` with
`g · P` a permutation of `P` and fewer than `2^64 - 1` entries is empty. An entry `c` gives the
entries `g^k · c` for every `k` (closure), which are pairwise distinct for `k < 2^64 - 1` since
`c ≠ 0` and `g` has that order (`gpow_injOn`, from `orderOf_g`), so the list would have at least
`2^64 - 1` distinct entries.

**The lookup argument** (`lookup_sound`). Messages of an arbitrary type `M` carry a key and a
count. A read pulls a message and pushes it with its count multiplied by `g` (`bump`, which keeps
the key); a seed pushes some messages and a finalize step pulls some. If the pushes (the bumped
reads and the seeds) and the pulls (the reads and the finalizes) are permutations of each other,
every read count is nonzero, there are fewer than `2^64 - 1` reads, and every finalized key is a
seeded key, then every read key is a seeded key. Restricted to a key no seed holds, the balance
says the read counts of that key are closed under multiplication by `g`, and Lemma 6.3 makes them
empty.

## Wrong readings excluded

* The counts are counted in `ℕ` (a `List.Perm`), never summed in `K`: in characteristic two a
  message pushed twice and never pulled has field-sum balance `0`.
* The nonzero hypothesis is load-bearing: the count list `[0]` is closed under multiplication by
  `g` (tests).
* The length bound is load-bearing: the `2^64 - 1` powers of `g` are closed under multiplication
  by `g`.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters

/-! ## Lemma 6.3 -/

/-- Every entry of a list closed under multiplication by `g` gives all its multiples by powers
of `g`. -/
theorem pow_mul_mem_of_perm {P : List K} (hp : (P.map (g * ·)).Perm P) {c : K} (hc : c ∈ P)
    (k : ℕ) : g ^ k * c ∈ P := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact hp.subset (List.mem_map_of_mem ih)

/-- **Specification Lemma 6.3.** A list of nonzero counts closed under multiplication by `g`, with
fewer than `2^64 - 1` entries, is empty: `g` has order `2^64 - 1`. -/
theorem eq_nil_of_perm_map_mul_g (P : List K) (h0 : ∀ c ∈ P, c ≠ 0)
    (hp : (P.map (g * ·)).Perm P) (hlen : P.length < 2 ^ 64 - 1) : P = [] := by
  by_contra hne
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil P hne
  have hinj : Set.InjOn (fun k : ℕ ↦ g ^ k * c) (Finset.range (2 ^ 64 - 1) : Set ℕ) := by
    intro a ha b hb hab
    have hab' : gpow a = gpow b := mul_right_cancel₀ (h0 c hc) hab
    exact gpow_injOn (by simpa using ha) (by simpa using hb) hab'
  have hsub : (Finset.range (2 ^ 64 - 1)).image (fun k : ℕ ↦ g ^ k * c) ⊆ P.toFinset := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (pow_mul_mem_of_perm hp hc k)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  have := List.toFinset_card_le P
  omega

/-! ## The lookup argument -/

/-- **The lookup argument** (specification Theorem 6.4): if the bumped reads and the seed pushes
are a permutation of the reads and the finalize pulls, every read count is nonzero, there are
fewer than `2^64 - 1` reads, and every finalized key is seeded, then every read key is seeded. -/
theorem lookup_sound {M κ : Type} [DecidableEq κ] (key : M → κ) (cnt : M → K) (bump : M → M)
    (reads seedPush seedPull : List M)
    (hkey : ∀ m ∈ reads, key (bump m) = key m) (hcnt : ∀ m ∈ reads, cnt (bump m) = g * cnt m)
    (hbal : (reads.map bump ++ seedPush).Perm (reads ++ seedPull))
    (h0 : ∀ m ∈ reads, cnt m ≠ 0) (hlen : reads.length < 2 ^ 64 - 1)
    (hseed : ∀ m ∈ seedPull, key m ∈ seedPush.map key) :
    ∀ m ∈ reads, key m ∈ seedPush.map key := by
  intro m hm
  by_contra hbad
  let p : M → Bool := fun x ↦ decide (key x = key m)
  have hpush : seedPush.filter p = [] := by
    refine List.filter_eq_nil_iff.mpr fun s hs hps ↦ hbad ?_
    rw [← of_decide_eq_true hps]
    exact List.mem_map_of_mem hs
  have hpull : seedPull.filter p = [] := by
    refine List.filter_eq_nil_iff.mpr fun s hs hps ↦ hbad ?_
    rw [← of_decide_eq_true hps]
    exact hseed s hs
  let R := reads.filter p
  have hR : (R.map bump).Perm R := by
    have h := hbal.filter p
    rw [List.filter_append, List.filter_append, hpush, hpull, List.append_nil,
      List.append_nil, List.filter_map] at h
    convert h using 2
    refine List.filter_congr fun x hx ↦ ?_
    simp only [Function.comp_apply, p, hkey x hx]
  have hRsub : ∀ x ∈ R, x ∈ reads := fun x hx ↦ List.mem_of_mem_filter hx
  have hP : ((R.map cnt).map (g * ·)).Perm (R.map cnt) := by
    have h := hR.map cnt
    rw [List.map_map] at h
    rw [List.map_map]
    convert h using 1
    exact List.map_congr_left fun x hx ↦ (hcnt x (hRsub x hx)).symm
  have hnil := eq_nil_of_perm_map_mul_g (R.map cnt)
    (fun c hc ↦ by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      exact h0 x (hRsub x hx))
    hP
    (by rw [List.length_map]; exact lt_of_le_of_lt (List.length_filter_le _ _) hlen)
  have hmR : cnt m ∈ R.map cnt :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, decide_eq_true rfl⟩)
  rw [hnil] at hmR
  exact List.not_mem_nil hmR

end LeanVM.Arithmetization
