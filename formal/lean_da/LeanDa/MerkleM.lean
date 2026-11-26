module

public import LeanDa.Merkle
public import Common.Lemmas
public import LeanDa.SimWorld
public import LeanDa.WithHash

@[expose] public section

/-!
# LeanDA's commitment over a hash oracle

The commitment with the hash `H` an oracle, in any monad (`commitCellsMWithHash`,
`LeanDa.WithHash`), is its pure definition over a pure hash (the `_eval` lemmas, for any monad
morphism that answers `H` by a function), and makes a bounded number of hash calls (the
`isWeightBound_` lemmas).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common

namespace LeanDa

/-! ## Over a pure hash -/

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

theorem cellLeavesM_eval {r : ℕ} (c : Fin (r * 128) → Cell) (i j : ℕ) :
    φ (cellLeavesMWithHash H c i j) = pure (cellLeavesWithHash H' c i j) :=
  hH _

theorem blobRootM_eval {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) :
    φ (blobRootMWithHash H c i) = pure (blobRootWithHash H' c i) :=
  merkleRootM_eval φ hpure hbind H H' hH _ _ _ (cellLeavesM_eval φ hpure hbind H H' hH c i)

theorem commitCellsM_eval {r : ℕ} (c : Fin (r * 128) → Cell) :
    φ (commitCellsMWithHash H c) = pure (commitCellsWithHash H' c) := by
  simp only [commitCellsMWithHash, hbind,
    merkleRootM_eval φ hpure hbind H H' hH _ _ _ (blobRootM_eval φ hpure hbind H H' hH c), pure_bind, hH,
    commitCellsWithHash]

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

include hP hC in
theorem isWeightBound_blobRootM {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) :
    QueryCostAtMost (blobRootMWithHash H c i) w (128 * cC + 127 * cP) := by
  unfold blobRootMWithHash
  exact (isWeightBound_merkleRootM H w cP hP 7 _ cC fun _ ↦ hC _).mono (by norm_num)

include hP hC in
/-- The commitment's hash calls: `128` cells and `127` pairs per blob tree, `maxRows - 1` pairs
over the blob roots and the count's pair, `maxRows · 128 (cC + cP)`. -/
theorem isWeightBound_commitCellsM {r : ℕ} (c : Fin (r * 128) → Cell) :
    QueryCostAtMost (commitCellsMWithHash H c) w (maxRows * (128 * cC + 128 * cP)) := by
  unfold commitCellsMWithHash
  refine ((isWeightBound_merkleRootM H w cP hP _ _ _
    (isWeightBound_blobRootM H w cP cC hP hC c)).bind fun _ ↦ hP _ _).mono ?_
  unfold maxRows
  have h1 : 1 ≤ 2 ^ logMaxRows := Nat.one_le_two_pow
  generalize 2 ^ logMaxRows = n at h1 ⊢
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega]
  nlinarith

end Weight

end LeanDa
