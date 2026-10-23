/-
# Vector commitments

Vector commitments with deterministic commit and open, following Foundations of
Data Availability Sampling (eprint 2023/1079), Definitions 15 and 16. Since
`commit` is deterministic, the opening state `St` of the paper can WLOG be
taken to be the committed vector itself, so `openAt` takes the vector. This
setting matches the main instantiation of interest, Merkle trees, which also
satisfy *perfect* completeness.

Besides position-binding (Definition 16) we define two derived notions used by
the code-binding proof of the erasure code commitment scheme:

* *weak position-binding*: the adversary outputs a full vector together with a
  single symbol/opening pair, and wins if the opening verifies against the
  *honestly computed* commitment to the vector while the symbol differs from
  the vector at that position. In the code-binding proof, the vector is a
  witness extracted from an argument of knowledge, whose honest commitment
  coincides with the adversary's commitment, and the symbol/opening pair is one
  of the adversary's openings.
* *collision resistance of `commit`*: the adversary wins if it outputs two
  distinct vectors with the same commitment. This is meaningful because
  `commit` is deterministic. It is used in the rewinding analysis: two
  accepting runs that answer the same commitment with different vectors yield
  exactly such a collision.

Both notions are implied by position-binding (plus perfect completeness), via
the reductions `WeakPosBindingAdv.toPosBindingAdv` and
`CollisionAdv.toPosBindingAdv`. The reductions are explicit algorithms so that
a human reader can verify they are PPT.

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import VCVio.CryptoFoundations.CommitmentScheme

open OracleComp ENNReal

namespace PqDas

/-- A vector commitment scheme for vectors in `Fin n → Λ`, with commitment key
type `Ck`, commitment type `Com`, and opening type `Opn` (Foundations
Definition 15, derandomized: `commit` and `openAt` are deterministic, and the
opening state is the committed vector itself, which is WLOG since `commit` is
deterministic). -/
structure VectorCommitment (Λ : Type) (n : ℕ) (Ck Com Opn : Type) where
  /-- Sample a commitment key. -/
  setup : ProbComp Ck
  /-- Commit to a vector (deterministic). -/
  commit : Ck → (Fin n → Λ) → Com
  /-- Open the commitment to position `i` (deterministic; takes the committed
  vector in place of an opening state). -/
  openAt : Ck → (Fin n → Λ) → Fin n → Opn
  /-- Verify an opening `τ` of symbol `x` at position `i` (deterministic). -/
  verify : Ck → Com → Fin n → Λ → Opn → Bool

namespace VectorCommitment

variable {Λ : Type} {n : ℕ} {Ck Com Opn : Type}

/-- Perfect completeness: honest openings of honest commitments always verify.
Merkle trees satisfy this. -/
def PerfectlyComplete (vc : VectorCommitment Λ n Ck Com Opn) : Prop :=
  ∀ ck ∈ support vc.setup, ∀ (v : Fin n → Λ) (i : Fin n),
    vc.verify ck (vc.commit ck v) i (v i) (vc.openAt ck v i) = true

/-! ### Position-binding (Foundations Definition 16) -/

/-- A position-binding adversary: outputs a commitment, a position, and two
symbol/opening pairs. -/
def PosBindingAdv (Λ : Type) (n : ℕ) (Ck Com Opn : Type) :=
  Ck → ProbComp (Com × Fin n × Λ × Opn × Λ × Opn)

/-- Position-binding experiment (Foundations Definition 16): the adversary wins
if it opens the same commitment at the same position to two different symbols. -/
def posBindingExp [DecidableEq Λ] (vc : VectorCommitment Λ n Ck Com Opn)
    (A : PosBindingAdv Λ n Ck Com Opn) : ProbComp Bool := do
  let ck ← vc.setup
  let (com, i, x, τ, x', τ') ← A ck
  return (decide (x ≠ x') && vc.verify ck com i x τ && vc.verify ck com i x' τ')

/-! ### Weak position-binding -/

/-- A weak position-binding adversary: outputs a full vector, a position, and a
symbol/opening pair. -/
def WeakPosBindingAdv (Λ : Type) (n : ℕ) (Ck Opn : Type) :=
  Ck → ProbComp ((Fin n → Λ) × Fin n × Λ × Opn)

/-- Weak position-binding experiment: the adversary outputs a vector `v`, a
position `i`, a symbol `x`, and an opening `τ`; it wins if `τ` opens the
*honest* commitment to `v` at position `i` to a symbol `x ≠ v i`. -/
def weakPosBindingExp [DecidableEq Λ] (vc : VectorCommitment Λ n Ck Com Opn)
    (A : WeakPosBindingAdv Λ n Ck Opn) : ProbComp Bool := do
  let ck ← vc.setup
  let (v, i, x, τ) ← A ck
  return (decide (x ≠ v i) && vc.verify ck (vc.commit ck v) i x τ)

/-- Reduction (an explicit PPT algorithm): a weak position-binding adversary
becomes a position-binding adversary by committing to `v` honestly and opening
position `i` honestly as the second symbol/opening pair. -/
def WeakPosBindingAdv.toPosBindingAdv (vc : VectorCommitment Λ n Ck Com Opn)
    (A : WeakPosBindingAdv Λ n Ck Opn) : PosBindingAdv Λ n Ck Com Opn := fun ck => do
  let (v, i, x, τ) ← A ck
  return (vc.commit ck v, i, x, τ, v i, vc.openAt ck v i)

/-- Weak position-binding is implied by position-binding (given perfect
completeness), via the reduction `WeakPosBindingAdv.toPosBindingAdv`: the
adversarial opening and the honest opening exhibit two different symbols with
verifying openings at the same position. -/
theorem weakPosBindingExp_le_posBindingExp [DecidableEq Λ]
    (vc : VectorCommitment Λ n Ck Com Opn) (hvc : vc.PerfectlyComplete)
    (A : WeakPosBindingAdv Λ n Ck Opn) :
    Pr{let x ← vc.weakPosBindingExp A}[x = true] ≤
      Pr{let x ← vc.posBindingExp (A.toPosBindingAdv vc)}[x = true] := by
  unfold weakPosBindingExp posBindingExp WeakPosBindingAdv.toPosBindingAdv
  simp only [monad_norm]
  refine OracleComp.prEvent_bind_mono_of_support _ _ _ fun ck hck => ?_
  refine OracleComp.prEvent_bind_mono_of_support _ _ _ fun ⟨v, i, x, τ⟩ _ => ?_
  have hopen := hvc ck hck v i
  simp only [Function.comp_apply]
  exact prEvent_pure_mono (by grind)

/-! ### Collision resistance of `commit` -/

/-- A collision adversary: outputs two vectors, trying to make them collide
under the (deterministic) `commit`. -/
def CollisionAdv (Λ : Type) (n : ℕ) (Ck : Type) :=
  Ck → ProbComp ((Fin n → Λ) × (Fin n → Λ))

/-- Collision experiment: the adversary wins if it outputs two *distinct*
vectors with the same commitment. Meaningful because `commit` is deterministic. -/
def collisionExp [DecidableEq Λ] [DecidableEq Com] (vc : VectorCommitment Λ n Ck Com Opn)
    (A : CollisionAdv Λ n Ck) : ProbComp Bool := do
  let ck ← vc.setup
  let (v, v') ← A ck
  return (decide (v ≠ v') && decide (vc.commit ck v = vc.commit ck v'))

/-- Reduction (an explicit PPT algorithm): a collision adversary becomes a
position-binding adversary by locating a position where the two vectors differ
(`Fin.find`) and opening both honestly at that position. If the vectors do not
differ the adversary has lost anyway and we output a dummy tuple. -/
def CollisionAdv.toPosBindingAdv [NeZero n] [DecidableEq Λ]
    (vc : VectorCommitment Λ n Ck Com Opn) (A : CollisionAdv Λ n Ck) :
    PosBindingAdv Λ n Ck Com Opn := fun ck => do
  let (v, v') ← A ck
  if h : v = v' then
    return (vc.commit ck v, 0, v 0, vc.openAt ck v 0, v 0, vc.openAt ck v 0)
  else
    let i := Fin.find (fun j => v j ≠ v' j) (Function.ne_iff.mp h)
    return (vc.commit ck v, i, v i, vc.openAt ck v i, v' i, vc.openAt ck v' i)

/-- Collision resistance of `commit` is implied by position-binding (given
perfect completeness), via the reduction `CollisionAdv.toPosBindingAdv`: if
distinct `v ≠ v'` collide, the honest openings of `v` and `v'` at a differing
position both verify against the common commitment and exhibit two different
symbols. -/
theorem collisionExp_le_posBindingExp [NeZero n] [DecidableEq Λ] [DecidableEq Com]
    (vc : VectorCommitment Λ n Ck Com Opn) (hvc : vc.PerfectlyComplete)
    (A : CollisionAdv Λ n Ck) :
    Pr{let x ← vc.collisionExp A}[x = true] ≤
      Pr{let x ← vc.posBindingExp (A.toPosBindingAdv vc)}[x = true] := by
  unfold collisionExp posBindingExp CollisionAdv.toPosBindingAdv
  simp only [monad_norm]
  refine OracleComp.prEvent_bind_mono_of_support _ _ _ fun ck hck => ?_
  refine OracleComp.prEvent_bind_mono_of_support _ _ _ fun ⟨v, v'⟩ _ => ?_
  by_cases h : v = v'
  · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_and, Function.comp_apply]
    exact prEvent_pure_mono (by simp)
  · have hfind := Fin.find_spec (p := fun j => v j ≠ v' j) (Function.ne_iff.mp h)
    have hopen := hvc ck hck v (Fin.find (fun j => v j ≠ v' j) (Function.ne_iff.mp h))
    have hopen' := hvc ck hck v' (Fin.find (fun j => v j ≠ v' j) (Function.ne_iff.mp h))
    simp only [h, ↓reduceDIte, pure_bind, Function.comp_apply]
    exact prEvent_pure_mono (by grind)

end VectorCommitment

end PqDas
