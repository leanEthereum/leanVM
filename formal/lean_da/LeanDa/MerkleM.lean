module

public import LeanDa.Merkle
public import Common.Lemmas
public import LeanDa.RpmCodeBinding
public import LeanDa.WithHash

@[expose] public section

/-!
# LeanDA's Merkle commitment over a hash oracle

The commitment (`commitCellsWith`), the honest opening (`openCellM`), the climb of an opening's hash
inputs (`hashInputsM`) and the search for a collision between two climbs (`findCollisionM`), each
transcribed from its pure definition with the hash `H` an oracle, in any monad. Over a pure hash
each is its pure definition (the `_eval` lemmas, for any monad morphism that answers `H` by a
function), and each makes a bounded number of hash calls (the `isWeightBound_` lemmas).

They let the hash be a random oracle in the proofs: Benedikt Wagner's reductions compute these
with a fixed hash function, and through these transcriptions they query it.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common

namespace LeanDa

section Defs

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Common.DigestBytes)

/-- The authentication path over an oracle (`merklePath`). -/
def merklePathM : ℕ → (ℕ → m Common.DigestBytes) → ℕ → m (List Common.DigestBytes)
  | 0, _, _ => pure []
  | d + 1, f, idx => do
    let s ← f (sibling idx)
    let rest ← merklePathM d (upMWithHash H f) (idx / 2)
    pure (s :: rest)

/-- The honest opening of a position over an oracle (`openCell`). -/
def openCellM {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) : m CellOpening := do
  let low ← merklePathM H 7 (cellLeavesMWithHash H c (positionRow p)) (positionCell p)
  let high ← merklePathM H (logPaddedRowCount r) (blobRootMWithHash H c) (positionRow p)
  pure ⟨low ++ high⟩

/-- The hash inputs of a climb over an oracle (`hashInputs`). -/
def hashInputsM : ℕ → List UInt8 → List Common.DigestBytes → m (List (List UInt8))
  | _, a, [] => pure [a]
  | idx, a, s :: rest => do
    let d ← H a
    let tl ← hashInputsM (idx / 2) (if idx % 2 = 0 then pairBytes d s else pairBytes s d) rest
    pure (a :: tl)

/-- The first colliding pair of two climbs over an oracle (`findCollision`). -/
def findCollisionM : List (List UInt8) → List (List UInt8) → m (List UInt8 × List UInt8)
  | a :: as, b :: bs => do
    let ha ← H a
    let hb ← H b
    if a ≠ b ∧ ha = hb then pure (a, b) else findCollisionM as bs
  | _, _ => pure ([], [])

end Defs

/-! ## Over a pure hash -/

theorem ofFn_val_eq_map_range {β : Type} (k : ℕ) (g : ℕ → β) :
    List.ofFn (fun j : Fin k ↦ g j) = (List.range k).map g := by
  apply List.ext_getElem <;> simp

section Eval

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
  (φ : ∀ {α}, m α → n α) (hpure : ∀ {α} (a : α), φ (pure a) = pure a)
  (hbind : ∀ {α β} (x : m α) (f : α → m β), φ (x >>= f) = φ x >>= fun a ↦ φ (f a))
  (H : List UInt8 → m Common.DigestBytes) (H' : List UInt8 → Common.DigestBytes) (hH : ∀ a, φ (H a) = pure (H' a))

include hpure hbind hH

theorem upM_eval (f : ℕ → m Common.DigestBytes) (f' : ℕ → Common.DigestBytes) (hf : ∀ i, φ (f i) = pure (f' i))
    (i : ℕ) : φ (upMWithHash H f i) = pure (upWithHash H' f' i) := by
  simp only [upMWithHash, hbind, hf, pure_bind, hH, upWithHash]

theorem merkleRootM_eval (d : ℕ) : ∀ (f : ℕ → m Common.DigestBytes) (f' : ℕ → Common.DigestBytes),
    (∀ i, φ (f i) = pure (f' i)) → φ (merkleRootMWithHash H d f) = pure (merkleRootWithHash H' d f') := by
  induction d with
  | zero => intro f f' hf; exact hf 0
  | succ d ih =>
    intro f f' hf
    exact ih _ _ (upM_eval φ hpure hbind H H' hH f f' hf)

theorem merklePathM_eval (d : ℕ) : ∀ (f : ℕ → m Common.DigestBytes) (f' : ℕ → Common.DigestBytes),
    (∀ i, φ (f i) = pure (f' i)) → ∀ idx,
      φ (merklePathM H d f idx) = pure (merklePathWithHash H' d f' idx) := by
  induction d with
  | zero => intro f f' _ idx; exact hpure _
  | succ d ih =>
    intro f f' hf idx
    simp only [merklePathM, merklePathWithHash, hbind, hf, pure_bind,
      ih _ _ (upM_eval φ hpure hbind H H' hH f f' hf), hpure]

theorem cellLeavesM_eval {r : ℕ} (c : Fin (r * 128) → Cell) (i j : ℕ) :
    φ (cellLeavesMWithHash H c i j) = pure (cellLeavesWithHash H' c i j) :=
  hH _

theorem blobRootM_eval {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) :
    φ (blobRootMWithHash H c i) = pure (blobRootWithHash H' c i) :=
  merkleRootM_eval φ hpure hbind H H' hH _ _ _ (cellLeavesM_eval φ hpure hbind H H' hH c i)

theorem commitCellsM_eval {r : ℕ} (c : Fin (r * 128) → Cell) :
    φ (commitCellsMWithHash H c) = pure (commitCellsWithHash H' c) :=
  merkleRootM_eval φ hpure hbind H H' hH _ _ _ (blobRootM_eval φ hpure hbind H H' hH c)

theorem openCellM_eval {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    φ (openCellM H c p) = pure (openCellWithHash H' c p) := by
  simp only [openCellM, hbind,
    merklePathM_eval φ hpure hbind H H' hH _ _ _ (cellLeavesM_eval φ hpure hbind H H' hH c _),
    merklePathM_eval φ hpure hbind H H' hH _ _ _ (blobRootM_eval φ hpure hbind H H' hH c),
    pure_bind, hpure]
  rfl

theorem hashInputsM_eval (path : List Common.DigestBytes) : ∀ (idx : ℕ) (a : List UInt8),
    φ (hashInputsM H idx a path) = pure (hashInputs H' idx a path) := by
  induction path with
  | nil => intro idx a; exact hpure _
  | cons s rest ih =>
    intro idx a
    simp only [hashInputsM, hashInputs, hbind, hH, pure_bind, ih, hpure]

theorem findCollisionM_eval (l₁ : List (List UInt8)) : ∀ l₂ : List (List UInt8),
    φ (findCollisionM H l₁ l₂) = pure (findCollision H' l₁ l₂) := by
  induction l₁ with
  | nil => intro l₂; exact hpure _
  | cons a as ih =>
    intro l₂
    cases l₂ with
    | nil => exact hpure _
    | cons b bs =>
      simp only [findCollisionM, findCollision, hbind, hH, pure_bind]
      split_ifs
      · exact hpure _
      · exact ih bs

end Eval

/-! ## Hash calls -/

section Weight

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- **A weight bound through a bind**, the continuation bounded on the support only. -/
theorem IsWeightBound.bind_of_mem_support {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {w : ι → ℕ} {a b : ℕ} (ha : QueryCostAtMost oa w a)
    (hb : ∀ x ∈ support oa, QueryCostAtMost (ob x) w b) : QueryCostAtMost (oa >>= ob) w (a + b) := by
  induction oa using OracleComp.inductionOn generalizing a with
  | pure x => exact (hb x (by simp)).mono (by omega)
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at ha
    rw [bind_assoc, isWeightBound_query_bind_iff]
    refine ⟨by omega, fun u ↦ ?_⟩
    have := ih u (ha.2 u) fun x hx ↦ hb x (by
      simp only [support_bind, Set.mem_iUnion]
      exact ⟨u, by simp, hx⟩)
    exact this.mono (by omega)

theorem length_of_mem_support_mapM {γ : Type} (f : γ → OracleComp spec β) (l : List γ)
    {x : List β} (hx : x ∈ support (l.mapM f)) : x.length = l.length := by
  induction l generalizing x with
  | nil =>
    simp only [List.mapM_nil, support_pure, Set.mem_singleton_iff] at hx
    subst hx; rfl
  | cons a l ih =>
    rw [List.mapM_cons] at hx
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨y, -, ys, hys, rfl⟩ := hx
    simp [ih hys]

theorem isWeightBound_mapM {γ : Type} (f : γ → OracleComp spec β) (w : ι → ℕ) (c : ℕ)
    (hf : ∀ x, QueryCostAtMost (f x) w c) (l : List γ) :
    QueryCostAtMost (l.mapM f) w (l.length * c) := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    rw [List.mapM_cons]
    exact ((hf a).bind fun _ ↦ ih.bind fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by simp only [List.length_cons]; ring_nf; omega)

variable (H : List UInt8 → OracleComp spec Common.DigestBytes) (w : ι → ℕ) (cP cC : ℕ)
  (hP : ∀ a b, QueryCostAtMost (H (pairBytes a b)) w cP)
  (hC : ∀ x, QueryCostAtMost (H (cellBytes x)) w cC)

include hP in
theorem isWeightBound_upM (f : ℕ → OracleComp spec Common.DigestBytes) (c : ℕ)
    (hf : ∀ i, QueryCostAtMost (f i) w c) (i : ℕ) :
    QueryCostAtMost (upMWithHash H f i) w (2 * c + cP) :=
  ((hf _).bind fun _ ↦ (hf _).bind fun _ ↦ hP _ _).mono (by omega)

include hP in
theorem isWeightBound_merkleRootM (d : ℕ) : ∀ (f : ℕ → OracleComp spec Common.DigestBytes) (c : ℕ),
    (∀ i, QueryCostAtMost (f i) w c) →
      QueryCostAtMost (merkleRootMWithHash H d f) w (2 ^ d * c + (2 ^ d - 1) * cP) := by
  induction d with
  | zero => intro f c hf; simpa [merkleRootMWithHash] using hf 0
  | succ d ih =>
    intro f c hf
    refine (ih _ _ (isWeightBound_upM H w cP hP f c hf)).mono ?_
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [pow_succ]
    generalize 2 ^ d = n at h1 ⊢
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show (k + 1) * 2 - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega]
    exact le_of_eq (by ring)

include hP in
theorem isWeightBound_merklePathM (d : ℕ) : ∀ (f : ℕ → OracleComp spec Common.DigestBytes) (c : ℕ),
    (∀ i, QueryCostAtMost (f i) w c) → ∀ idx,
      QueryCostAtMost (merklePathM H d f idx) w ((2 ^ d - 1) * (c + cP)) := by
  induction d with
  | zero => intro f c _ idx; exact isWeightBound_pure _ _ _
  | succ d ih =>
    intro f c hf idx
    refine ((hf _).bind fun _ ↦ (ih _ _ (isWeightBound_upM H w cP hP f c hf) _).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono ?_
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [pow_succ]
    generalize 2 ^ d = n at h1 ⊢
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show (k + 1) * 2 - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega]
    nlinarith

include hP hC in
theorem isWeightBound_blobRootM {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) :
    QueryCostAtMost (blobRootMWithHash H c i) w (128 * cC + 127 * cP) := by
  unfold blobRootMWithHash
  exact (isWeightBound_merkleRootM H w cP hP 7 _ cC fun _ ↦ hC _).mono (by norm_num)

include hP hC in
/-- The commitment's hash calls: `128` cells and `127` pairs per blob tree, and `2^⌈log₂ r⌉ - 1`
pairs over the blob roots, at most `2^⌈log₂ r⌉ · 128 (cC + cP)`. -/
theorem isWeightBound_commitCellsM {r : ℕ} (c : Fin (r * 128) → Cell) :
    QueryCostAtMost (commitCellsMWithHash H c) w (paddedRowCount r * (128 * cC + 128 * cP)) := by
  unfold commitCellsMWithHash
  refine (isWeightBound_merkleRootM H w cP hP _ _ _
    (isWeightBound_blobRootM H w cP cC hP hC c)).mono ?_
  have h1 : 1 ≤ 2 ^ logPaddedRowCount r := Nat.one_le_two_pow
  unfold paddedRowCount
  generalize 2 ^ logPaddedRowCount r = n at h1 ⊢
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega]
  nlinarith

include hP hC in
theorem isWeightBound_openCellM {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    QueryCostAtMost (openCellM H c p) w (paddedRowCount r * (128 * cC + 128 * cP)) := by
  unfold openCellM
  refine ((isWeightBound_merklePathM H w cP hP 7 _ cC (fun _ ↦ hC _) _).bind fun _ ↦
    (isWeightBound_merklePathM H w cP hP _ _ _ (isWeightBound_blobRootM H w cP cC hP hC c) _).bind
      fun _ ↦ isWeightBound_pure _ _ 0).mono ?_
  have h1 : 1 ≤ 2 ^ logPaddedRowCount r := Nat.one_le_two_pow
  unfold paddedRowCount
  generalize 2 ^ logPaddedRowCount r = n at h1 ⊢
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega]
  norm_num
  nlinarith

theorem isWeightBound_hashInputsM (h1 : ∀ a, QueryCostAtMost (H a) w 1) (path : List Common.DigestBytes) :
    ∀ (idx : ℕ) (a : List UInt8), QueryCostAtMost (hashInputsM H idx a path) w path.length := by
  induction path with
  | nil => intro idx a; exact isWeightBound_pure _ _ _
  | cons s rest ih =>
    intro idx a
    exact ((h1 a).bind fun _ ↦ (ih _ _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by simp only [List.length_cons]; omega)

theorem isWeightBound_findCollisionM (h1 : ∀ a, QueryCostAtMost (H a) w 1)
    (l₁ : List (List UInt8)) : ∀ l₂ : List (List UInt8),
      QueryCostAtMost (findCollisionM H l₁ l₂) w (2 * l₂.length) := by
  induction l₁ with
  | nil => intro l₂; exact isWeightBound_pure _ _ _
  | cons a as ih =>
    intro l₂
    cases l₂ with
    | nil => exact isWeightBound_pure _ _ _
    | cons b bs =>
      unfold findCollisionM
      refine ((h1 a).bind fun _ ↦ (h1 b).bind fun _ ↦
        (?_ : QueryCostAtMost _ w (2 * bs.length))).mono (by simp only [List.length_cons]; omega)
      split_ifs
      · exact isWeightBound_pure _ _ _
      · exact ih bs

end Weight

end LeanDa
