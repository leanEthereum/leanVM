/-
  LeanVM.Prover.Complete.Link.IndexSplit

  The index side's identity, split into the state chain's telescoping and the lookups' balance.
-/

module

public import LeanVM.Prover.Complete.Link.Open

/-!
# The index side, split

`indexProds W ch` (`Statement/Prover/LinkIndex.lean`) has seven terms over the thirteen index
arrays. Its cube sum is the sum of two sums of products over the same arrays (`cubeSum_split`):

* `stateProds`: the state chain, `eq(ζ, j)·A(j) + eq(ζ, j + 1)·B(j)`, the arrays `6, 0` and `7, 1`;
* `balanceProds`: the memory `η_mem·w_mem·Y`, the program `w_bc·X_ω`, the payload, the word reads
  `η_mem·v_word·words` and the frame reads `w_fp·P_fp`.

`IndexStateIdentity W`: the first is `linkEqAt ζ 0·ŝ_init + linkEqAt ζ T·ŝ_fin`;
`IndexBalance W`: the second is zero (in characteristic two the payload is the lookups' other
side). `linkIndexIdentity_of`: together they give `LinkIndexIdentity W`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers

/-- The state chain's terms of the index side. -/
def stateProds (W : Witness) (ch : LinkChallenges) : Prods :=
  ⟨indexArrays W ch, #[(1, #[6, 0]), (1, #[7, 1])]⟩

/-- The lookups' and the payload's terms of the index side. -/
def balanceProds (W : Witness) (ch : LinkChallenges) : Prods :=
  ⟨indexArrays W ch, #[(ch.etaMem, #[2, 3]), (1, #[4, 5]), (1, #[8]), (ch.etaMem, #[9, 10]),
    (1, #[11, 12])]⟩

theorem terms_split (W : Witness) (ch : LinkChallenges) :
    (indexProds W ch).terms.toList =
      (stateProds W ch).terms.toList ++ (balanceProds W ch).terms.toList := rfl

theorem termAt_tables {P Q : Prods} (h : P.tables = Q.tables) (k : ℕ) (cf : E × Array ℕ) :
    termAt P k cf = termAt Q k cf := by
  unfold termAt; rw [h]

theorem cubeSum_split (m : ℕ) (W : Witness) (ch : LinkChallenges) :
    cubeSum m (indexProds W ch) = cubeSum m (stateProds W ch) + cubeSum m (balanceProds W ch) := by
  unfold cubeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [termsAt_eq, termsAt_eq, termsAt_eq, terms_split, List.foldl_append,
    foldl_add_shift _ (balanceProds W ch).terms.toList]
  have h1 : (indexProds W ch).tables = (stateProds W ch).tables := rfl
  have h3 : (stateProds W ch).tables = (balanceProds W ch).tables := rfl
  simp only [termAt_tables h1, termAt_tables h3]

/-- **The state chain telescopes**: the index side's state terms sum to the chain's ends. -/
def IndexStateIdentity (W : Witness) : Prop :=
  ∀ theta0 drawn, drawn.length = packedChallenges tables (linkNRows W) W.chunks.width →
    let ch := LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0 drawn
    cubeSum (2 ^ W.chunks.width) (stateProds W ch) =
      linkEqAt ch.zeta 0 * (1 + ch.gammaState.getD 0 0 * 1 + ch.gammaState.getD 1 0 * 1) +
        linkEqAt ch.zeta (W.layout.tableRows.foldl (· + ·) 0) *
          (1 + ch.gammaState.getD 0 0 * gpow (2 ^ W.layout.logBytecode - 1) +
            ch.gammaState.getD 1 0 * 1)

/-- **The lookups balance**: the index side's memory, program, payload, word-read and frame-read
terms sum to zero. -/
def IndexBalance (W : Witness) : Prop :=
  ∀ theta0 drawn, drawn.length = packedChallenges tables (linkNRows W) W.chunks.width →
    let ch := LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0 drawn
    cubeSum (2 ^ W.chunks.width) (balanceProds W ch) = 0

/-- **The index side's identity** from the two. -/
theorem linkIndexIdentity_of {W : Witness} (hs : IndexStateIdentity W) (hb : IndexBalance W) :
    LinkIndexIdentity W := by
  intro theta0 drawn hlen
  simp only
  rw [cubeSum_split, hs theta0 drawn hlen, hb theta0 drawn hlen, add_zero]

end LeanVM.Prover.Complete

end
