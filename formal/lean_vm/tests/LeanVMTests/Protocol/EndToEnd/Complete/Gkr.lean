import LeanVM.Protocol.EndToEnd.Complete.Gkr

/-!
# The honest GKR prover: tests

* **Statement lock** of `follows_verifyGkrGrandProducts`.
* **The step's claims** (`#guard`, compiled) on small trees: the batched layer values at the
  point are the step's starting claim (`stepClaim_nil`); every round's claims at `0, 1` split the
  claim as the equality-mode round checks it (`stepClaim_split`); with every coordinate bound the
  claim is the batched children's products (`stepClaim_self`); the root of the tree is the
  leaves' product (`multilinearEval_up_root`).
* **Negative**: a tampered child breaks the product check, and pull leaves with another product
  than the push leaves break the shared root.
-/

namespace LeanVMTests.Protocol.EndToEnd.Complete.Gkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Whir.Complete

/-! ## Statement lock -/

example : ∀ (D : ℕ) (L₀ L₁ L₂ : List E), L₀.length = 2 ^ D → L₁.length = 2 ^ D →
    L₂.length = 2 ^ D → L₀.prod = L₁.prod → ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ b.1 = L₂.prod ∧ b.2.1.length = D ∧
        b.2.2 = [multilinearEval L₀ b.2.1, multilinearEval L₁ b.2.1, multilinearEval L₂ b.2.1])
      (hGkr D L₀ L₁ L₂) (verifyGkrGrandProducts D) cs :=
  follows_verifyGkrGrandProducts

/-! ## Small trees -/

/-- A field element from three words. -/
def eK (a b c : ℕ) : E := E.ofLimbs (K.ofBits a) (K.ofBits b) (K.ofBits c)

/-- A pseudo-random list of `n` entries. -/
def tbl (seed n : ℕ) : List E :=
  (List.range n).map fun i ↦ eK (i * 0x9E3779B97F4A7C15 + seed) (i * i + 3 * seed) (seed + 7 * i)

/-- Three leaf lists of `2^3` entries, the second a permutation of the first. -/
def C₀ : List E := tbl 1 8
def C₁ : List E := (tbl 1 8).reverse
def C₂ : List E := tbl 2 8

-- The root of a tree is the product of its leaves.
#guard multilinearEval (up 3 C₀) [] == C₀.prod
#guard (up 3 C₀).prod == (up 3 C₁).prod

-- A step of two levels from a point of one coordinate: the layers' batched values are the
-- step's claim.
#guard
  let p := [eK 3 4 5]
  let c := eK 6 7 8
  polyEval [multilinearEval (up 2 C₀) p, multilinearEval (up 2 C₁) p,
    multilinearEval (up 2 C₂) p] c == stepClaim C₀ C₁ C₂ 2 p c []

-- Every round splits its claim as the equality-mode check reads it (a step of one level from a
-- point of two coordinates).
#guard
  let p := [eK 3 4 5, eK 9 10 11]
  let c := eK 6 7 8
  let x := eK 12 13 14
  [[], [x]].all fun pre ↦
    let r := p.getD pre.length 0
    (1 + r) * stepClaim C₀ C₁ C₂ 1 p c (pre ++ [0]) + r * stepClaim C₀ C₁ C₂ 1 p c (pre ++ [1]) ==
      stepClaim C₀ C₁ C₂ 1 p c pre

-- With every coordinate bound, the claim is the batched products of the children the honest
-- prover sends; a tampered child breaks the check.
#guard
  let p := [eK 3 4 5, eK 9 10 11]
  let c := eK 6 7 8
  let x := [eK 12 13 14, eK 15 16 17]
  stepClaim C₀ C₁ C₂ 1 p c x == stepF C₀ C₁ C₂ 1 c x &&
    stepClaim C₀ C₁ C₂ 1 p c x !=
      polyEval [((child C₀ 1 x).set 0 1).prod, (child C₁ 1 x).prod, (child C₂ 1 x).prod] c

-- Negative: pull leaves with another product than the push leaves have another root, so the one
-- root the verifier reads cannot be both.
#guard (up 3 C₀).prod != (up 3 C₂).prod

end LeanVMTests.Protocol.EndToEnd.Complete.Gkr
