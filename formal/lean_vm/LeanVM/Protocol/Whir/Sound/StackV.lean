/-
  LeanVM.Protocol.Whir.Sound.StackV

  Level 0's stack from a tuple: its blocks the lanes' low parts, read off their values on `U_κ`.
-/

module

public import LeanVM.Protocol.Whir.Sound.DescentV
public import LeanVM.Protocol.Whir.Params.DescentCheck

/-!
# Level 0's stack

`tupleStack hμ U`: block `u` is the `K`-limb of lane `u`'s low part; a stack whose blocks are a
tuple's low parts is its tuple's stack (`tupleStack_eq`). `stackV`: the same from the tuple's
values on `U_κ`, through the inverse transform (`stackV_valsT`). `descend_good`: the descent of a
good trace, at the deployed parameters, returns a level-0 tuple whose stack is not bad.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Params
open LeanVM.Protocol.Compile
open Polynomial

@[expose] public section

/-- **The stack of a level-0 tuple**: block `u` is the `K`-limb of lane `u`'s low part. -/
noncomputable def tupleStack {μ : ℕ} (hμ : laneBits ≤ μ) (U : (Fin laneBits → Bool) → E[X]) :
    Column μ :=
  stackOf hμ fun u x ↦ (lowMsg (μ - laneBits) (U ((bitsEquiv laneBits).symm u)) x).limb 0

/-- A stack whose blocks are a tuple's low parts is the tuple's stack. -/
theorem tupleStack_eq {μ : ℕ} (hμ : laneBits ≤ μ) {U : (Fin laneBits → Bool) → E[X]}
    {q : Column μ} (h : ∀ u, lowMsg (μ - laneBits) (U u) = blockOf q (bitsEquiv laneBits u)) :
    tupleStack hμ U = q := by
  refine eq_of_blockOf_eq hμ fun u ↦ ?_
  rw [tupleStack, blockOf_stackOf]
  funext x
  have hx := congrFun (h ((bitsEquiv laneBits).symm u)) x
  rw [Equiv.apply_symm_apply] at hx
  rw [hx]
  simp [EndToEnd.blockOf, limb_ofK]

/-- **The descent of a good trace ends on a good stack** at the deployed parameters: the descent
returns a tuple of level 0, and its stack is not bad. -/
theorem descend_good {μ R : ℕ} (h : Whir.Admissible μ R) (D : NearDecoder)
    (Bad : Column μ → Prop) (tr : WhirTrace) (cs : List (ℕ × ℕ × Word))
    (hg : traceGood (codesOf μ R) 0 (lvl0Pred μ Bad) tr cs) :
    ∃ m T, descendTrace D (codesOf μ R) cs tr 0 = some ⟨m, T⟩ ∧
      ∃ (hm : m = laneBits) (hμ : laneBits ≤ μ), ¬ Bad (tupleStack hμ (hm ▸ T)) := by
  obtain ⟨level, rest, F⟩ := level0Facts (shapeOK_of_admissible h)
  obtain ⟨T, hd, hT, -⟩ := descendTrace_of_traceGood D (codesOf μ R) cs
    (fun i j h1 h2 ↦ codesOf_thr h i j h1 h2) tr 0 _ hg
  refine ⟨_, T, hd, ?_⟩
  simp only [lvl0Pred] at hT
  push Not at hT
  obtain ⟨hm, q, hq, hb⟩ := hT
  exact ⟨hm, F.hμ, by rwa [tupleStack_eq F.hμ hq]⟩

/-- **Level 0's stack from its values**: block `u` is the `K`-limb of the low part of lane `u`,
the inverse transform of its values on `U_κ`. -/
def stackV {μ : ℕ} (hμ : laneBits ≤ μ) {n : ℕ} (hn : 2 ^ (μ - laneBits) ≤ n)
    (V : (Fin laneBits → Bool) → Fin n → E) : Column μ :=
  stackOf hμ fun u x ↦ ((novelInvE (μ - laneBits) (Array.ofFn fun v : Fin (2 ^ (μ - laneBits)) ↦
    V ((bitsEquiv laneBits).symm u) (Fin.castLE hn v))).getD (bitsToNat x) 0).limb 0

theorem stackV_valsT {μ : ℕ} (hμ : laneBits ≤ μ) (P : LevelCode) (hn : 2 ^ (μ - laneBits) ≤ P.n)
    (T : (Fin laneBits → Bool) → E[X]) : stackV hμ hn (valsT P.dom T) = tupleStack hμ T := by
  have h64 : μ - laneBits ≤ 64 := by
    have h1 : 2 ^ (μ - laneBits) ≤ 2 ^ 64 :=
      hn.trans (Nat.pow_le_pow_right (by norm_num) P.h64)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hv : ∀ u, (Array.ofFn fun v : Fin (2 ^ (μ - laneBits)) ↦
      valsT P.dom T u (Fin.castLE hn v)) = valsU (μ - laneBits) (T u) := fun u ↦ rfl
  unfold stackV tupleStack
  simp only [hv]
  congr 1
  funext u x
  rw [lowMsg_eq_novelInvE h64]

end
end LeanVM.Protocol.Whir.Sound
