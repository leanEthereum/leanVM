/-
  LeanVM.Protocol.Compile.Rom.Chain

  Without failure, the permutation inputs of a replay on the log's answers are logged in order:
  each after the entry whose answer the sponge holds before it.
-/

module

public import LeanVM.Protocol.Compile.Rom.Replay
public import LeanVM.Protocol.Compile.Rom.Log

/-!
# The replay's chain of permutations

A permutation input carries the capacity of the state the sponge holds, the answer of the
permutation before it. Without failure, a permutation entry whose answer's capacity an input
carries comes before the input's entry (`lt_of_cap`), so the permutations of a replay on the
log's answers (`replayU (lookF ℓ)`) are first logged in the order the replay makes them
(`replay_chain`). In particular, once one of them is first logged past the adversary's part of
the log, so is every later one, and the state the replay ends with is a verifier's fresh answer.

* `OutAt ℓ i u`: `u` is the answer of the permutation entry `i`.
* `FirstAt ℓ j x`: the entry `j` is the first to answer `x`.
* `ChainIn ℓ i i' ys`: every input of `ys` is first answered strictly after `i` and at most at
  `i'`.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom

@[expose] public section

/-- The state `u` is the answer of the permutation entry `i` of the log. -/
def OutAt (ℓ : Log) (i : ℕ) (u : KeccakState) : Prop :=
  ∃ (hi : i < ℓ.length) (x : KeccakState), ℓ[i] = .inr (x, u)

/-- The entry `j` of the log is the first to answer the permutation input `x`. -/
def FirstAt (ℓ : Log) (j : ℕ) (x : KeccakState) : Prop :=
  ∃ (hj : j < ℓ.length) (v : KeccakState), ℓ[j] = .inr (x, v) ∧ lookF (ℓ.take j) x = none

/-- Every input of `ys` is first answered strictly after the entry `i` and at most at `i'`. -/
def ChainIn (ℓ : Log) (i i' : ℕ) (ys : List KeccakState) : Prop :=
  ∀ y ∈ ys, ∃ j, i < j ∧ j ≤ i' ∧ FirstAt ℓ j y

theorem ChainIn.nil (ℓ : Log) (i i' : ℕ) : ChainIn ℓ i i' [] := fun _ h ↦ by simp at h

theorem ChainIn.append {ℓ : Log} {i i₁ i' : ℕ} {ys zs : List KeccakState} (h1 : ChainIn ℓ i i₁ ys)
    (h2 : ChainIn ℓ i₁ i' zs) (hi : i ≤ i₁) (hi' : i₁ ≤ i') : ChainIn ℓ i i' (ys ++ zs) := by
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨j, h1j, h2j, hj⟩ := h1 y hy
    exact ⟨j, h1j, by omega, hj⟩
  · obtain ⟨j, h1j, h2j, hj⟩ := h2 y hy
    exact ⟨j, by omega, h2j, hj⟩

/-- A first answer at `j` is the log's answer in every prefix past `j`. -/
theorem FirstAt.lookF_take {ℓ : Log} {j : ℕ} {x : KeccakState} (h : FirstAt ℓ j x) {m : ℕ}
    (hm : j < m) : lookF (ℓ.take m) x = lookF ℓ x := by
  obtain ⟨hj, v, hej, hn⟩ := h
  have h1 : lookF ℓ x = some v := (lookF_eq_some_iff ℓ x v).mpr ⟨j, hj, hej, hn⟩
  rw [h1, lookF_eq_some_iff]
  exact ⟨j, by simp; omega, by simpa using hej, by rwa [List.take_take, min_eq_left hm.le]⟩

/-- A first answer at `j` is no answer in a prefix up to `j`. -/
theorem FirstAt.lookF_take_none {ℓ : Log} {j : ℕ} {x : KeccakState} (h : FirstAt ℓ j x) {m : ℕ}
    (hm : m ≤ j) : lookF (ℓ.take m) x = none := by
  obtain ⟨-, -, -, hn⟩ := h
  rcases hl : lookF (ℓ.take m) x with _ | w
  · rfl
  · have hp : ℓ.take m <+: ℓ.take j := by
      rw [show ℓ.take m = (ℓ.take j).take m by rw [List.take_take, min_eq_left hm]]
      exact List.take_prefix _ _
    rw [lookF_of_prefix hp hl] at hn
    cases hn

/-- A permutation input keeps the capacity of the state. -/
theorem capOf_duplexInput (sp : Sponge) : capOf (duplexInput sp) = capOf sp.state := by
  funext i
  simp only [capOf, duplexInput]
  rw [lane_ofFn _ _ (by omega)]
  simp

variable {X : Type} {σ : Seeds X} {ℓ : Log}

/-- **One link of the chain**: without failure, an input carrying the capacity of the answer of
the entry `i` is first answered past `i`. -/
theorem chain_step (hf : ¬ Fail σ ℓ) {i : ℕ} {u t v : KeccakState} (hu : OutAt ℓ i u)
    (hc : capOf t = capOf u) (ht : lookF ℓ t = some v) :
    ∃ j, i < j ∧ FirstAt ℓ j t ∧ OutAt ℓ j v := by
  obtain ⟨j, hj, hej, hn⟩ := (lookF_eq_some_iff ℓ t v).mp ht
  obtain ⟨hi, x, hei⟩ := hu
  exact ⟨j, lt_of_cap hf hi hj hei hej hc, ⟨hj, v, hej, hn⟩, ⟨hj, t, hej⟩⟩

theorem duplex_chain (hf : ¬ Fail σ ℓ) {i : ℕ} {sp sp' : Sponge} (hs : OutAt ℓ i sp.state)
    (h : duplex (m := Option) (lookF ℓ) sp = some sp') :
    ∃ j, i < j ∧ FirstAt ℓ j (duplexInput sp) ∧ OutAt ℓ j sp'.state := by
  simp only [duplex, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨st, hst, rfl⟩ := h
  exact chain_step hf hs (capOf_duplexInput sp) hst

theorem absorb_chain (hf : ¬ Fail σ ℓ) {i : ℕ} {sp sp' : Sponge} {x : E} {tag : ℕ}
    (hs : OutAt ℓ i sp.state) (h : absorb (m := Option) (lookF ℓ) sp x tag = some sp') :
    ∃ i', i ≤ i' ∧ OutAt ℓ i' sp'.state ∧ ChainIn ℓ i i' (absorbIn sp) := by
  unfold absorb absorbIn at *
  split_ifs at h ⊢ with hp
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨sp1, h1, rfl⟩ := h
    obtain ⟨j, hij, hj, hout⟩ := duplex_chain hf hs h1
    refine ⟨j, hij.le, hout, fun y hy ↦ ?_⟩
    rw [List.mem_singleton] at hy
    subst hy
    exact ⟨j, hij, le_rfl, hj⟩
  · simp only [bind, pure, Option.bind_some, Option.some.injEq] at h
    subst h
    exact ⟨i, le_rfl, hs, ChainIn.nil ℓ i i⟩

theorem squeeze_chain (hf : ¬ Fail σ ℓ) {i : ℕ} {sp : Sponge} {r : E × Sponge}
    (hs : OutAt ℓ i sp.state) (h : squeeze (m := Option) (lookF ℓ) sp = some r) :
    ∃ i', i ≤ i' ∧ OutAt ℓ i' r.2.state ∧ ChainIn ℓ i i' (squeezeIn sp) := by
  unfold squeeze squeezeIn at *
  split at h
  · rename_i c hg
    simp only [hg, pure, Option.some.injEq] at h ⊢
    subst h
    exact ⟨i, le_rfl, hs, ChainIn.nil ℓ i i⟩
  · rename_i hg
    simp only [hg, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨sp1, h1, rfl⟩ := h
    obtain ⟨j, hij, hj, hout⟩ := duplex_chain hf hs h1
    refine ⟨j, hij.le, hout, fun y hy ↦ ?_⟩
    rw [List.mem_singleton] at hy
    subst hy
    exact ⟨j, hij, le_rfl, hj⟩

/-- **The replay's chain**: without failure, a replay on the log's answers from a state holding
the answer of the entry `i` ends holding the answer of an entry `i' ≥ i`, and every permutation
input it makes is first answered past `i` and at most at `i'`. -/
theorem replay_chain (hf : ¬ Fail σ ℓ) {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) {a : α} {s' : VerifierProgramState}
      {i : ℕ}, replayU (lookF ℓ) p s = some (a, s') → OutAt ℓ i s.sponge.state →
      ∃ i', i ≤ i' ∧ OutAt ℓ i' s'.sponge.state ∧ ChainIn ℓ i i' (replayIn (lookF ℓ) p s)
  | .ret _, s, _, _, i, h, hs => by
    simp only [replayU, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨i, le_rfl, hs, ChainIn.nil ℓ i i⟩
  | .fail, _, _, _, _, h, _ => by simp [replayU] at h
  | .read k, s, _, _, i, h, hs => by
    simp only [replayU] at h
    simp only [replayIn]
    split at h
    · rename_i x xs hst hg
      obtain ⟨sp, hsp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨i₁, hi₁, hout₁, hc₁⟩ := absorb_chain hf hs hsp
      obtain ⟨i', hi', hout', hc'⟩ := replay_chain hf (k x) _ h hout₁
      rw [hsp]
      exact ⟨i', by omega, hout', hc₁.append hc' hi₁ hi'⟩
    · simp at h
  | .sample k, s, _, _, i, h, hs => by
    simp only [replayU] at h
    simp only [replayIn]
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i₁, hi₁, hout₁, hc₁⟩ := squeeze_chain hf hs hr
    obtain ⟨i', hi', hout', hc'⟩ := replay_chain hf (k r.1) _ h hout₁
    rw [hr]
    exact ⟨i', by omega, hout', hc₁.append hc' hi₁ hi'⟩
  | .grind bits k, s, _, _, i, h, hs => by
    simp only [replayU] at h
    simp only [replayIn]
    split at h
    · rename_i n xs hst hg
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      split_ifs at h with hp
      have hr' := hr
      simp only [absorbNonce, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr'
      obtain ⟨sp1, hsp1, sp2, hsp2, rfl⟩ := hr'
      obtain ⟨i₁, hi₁, hout₁, hc₁⟩ := absorb_chain hf hs hsp1
      obtain ⟨j₂, hj₂, hfirst₂, hout₂⟩ := duplex_chain hf hout₁ hsp2
      obtain ⟨i', hi', hout', hc'⟩ := replay_chain hf k _ h hout₂
      rw [hsp1]
      have hr2 : absorbNonce (m := Option) (lookF ℓ) s.sponge n =
          some (Keccak.lane sp2.state 2, { sp2 with ground := some (challengeOf sp2.state) }) := hr
      simp only [hr2, hp, ↓reduceIte]
      refine ⟨i', by omega, hout', hc₁.append (ChainIn.append (i₁ := j₂) ?_ hc' hj₂.le hi')
        hi₁ (by omega)⟩
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨j₂, hj₂, le_rfl, hfirst₂⟩
    · simp at h
  | .commit height width k, s, _, _, i, h, hs => by
    simp only [replayU] at h
    simp only [replayIn]
    split at h
    · rename_i x0 x1 xs hst hg
      obtain ⟨sp0, hsp0, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sp1, hsp1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨i₀, hi₀, hout₀, hc₀⟩ := absorb_chain hf hs hsp0
      obtain ⟨i₁, hi₁, hout₁, hc₁⟩ := absorb_chain hf hout₀ hsp1
      obtain ⟨i', hi', hout', hc'⟩ := replay_chain hf k _ h hout₁
      rw [hsp0]
      simp only [hsp1]
      exact ⟨i', by omega, hout', hc₀.append (hc₁.append hc' hi₁ hi') hi₀ (by omega)⟩
    · simp at h
  | .query idx _ k, s, _, _, i, h, hs => by
    simp only [replayU] at h
    simp only [replayIn]
    split at h
    · rename_i r phase rest hr ho
      exact replay_chain hf _ _ h hs
    · simp at h

end
end LeanVM.Protocol.Compile.Rom
