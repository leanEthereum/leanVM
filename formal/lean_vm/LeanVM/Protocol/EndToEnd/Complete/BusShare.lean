/-
  LeanVM.Protocol.EndToEnd.Complete.BusShare

  The honest prover of the bus phase's bytecode share: the program's share of a bytecode leaf,
  reduced by a sumcheck over the tuple slot to one value of the stacked bytecode, which the
  deployed verifier evaluates itself.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.BusFramework
public import LeanVM.Protocol.Keccak.Multilinear

/-!
# The bytecode's share

`bytecodeShare weights bytecodeLow` (`crates/verifier/src/bus.rs:168-184` at leanVM `f128`; the
prover's `prove_bytecode_share`, `crates/leanvm_core/src/leaf.rs`) reads the share
`S = Σ_x w_x P(z, x)` of the stacked bytecode `P` at the instructions' point `z`, runs a plain
sumcheck of three coefficients over the slot `x`, four rounds, the low bit first, and reads
`P(z, r)` at its challenges `r`, checking the last claim against `w̃(r) · P(z, r)`; the deployed
verifier then checks `P(z, r)` itself (`computedBytecodeValue`).

The honest prover's running claim after the challenges `acc` is the sum, over the slots not yet
bound, of the product of the two extensions `w̃` and `P(z, ·)` (`shareClaim`): before the rounds
it is the share (`shareClaim_nil`), each round's polynomial has degree two (`shareClaim_polyLE`)
and splits the running claim (`shareClaim_split`), and after the four rounds it is the product
the verifier checks (`shareClaim_full`, `wMle_eq_dot`, `pMle_eq_multilinearEval`).

* `follows_bytecodeShare`: the honest prover `hShare` follows `bytecodeShare`, to the share
  `bcShare prog w z`, the point `z ++ r` and the value `P(z, r)`, which is the stacked bytecode's
  extension there, so `computedBytecodeValue` accepts it (`follows_bytecodeShare_value`).
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd.Front Finset
open LeanVM.Protocol.KeccakGkr (eqAt bitsE sum_cube_succ bitsE_two_mul bitsE_two_mul_add_one
  sum_eqAt_bitsE polyLE_mle multilinearEval_eq eqKernel_length)

@[expose] public section

section Share

variable (prog : LeanIsaProgram)

/-- The extension of the slot weights at `pt`. -/
noncomputable def wMle (w pt : List E) : E := ∑ o ∈ range 16, eqAt pt o * w.getD o 0

/-- The extension of the stacked bytecode's slots at `pt`, the instructions' point `z`. -/
noncomputable def pMle (z pt : List E) : E := ∑ o ∈ range 16, eqAt pt o * bcSlot prog o z

/-- The running claim of the share's sumcheck after the challenges `acc`: the sum over the slots
not yet bound of `w̃ · P(z, ·)`. -/
noncomputable def shareClaim (w z acc : List E) : E :=
  ∑ u ∈ range (2 ^ (4 - acc.length)),
    wMle w (acc ++ bitsE u (4 - acc.length)) * pMle prog z (acc ++ bitsE u (4 - acc.length))

/-- **Before the rounds the claim is the share.** -/
theorem shareClaim_nil (w z : List E) : shareClaim prog w z [] = bcShare prog w z := by
  simp only [shareClaim, List.length_nil, Nat.sub_zero, List.nil_append, bcShare]
  refine sum_congr rfl fun u hu ↦ ?_
  have hu' : u < 2 ^ 4 := mem_range.mp hu
  rw [wMle, pMle, show (16 : ℕ) = 2 ^ 4 from rfl, sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']

/-- **Each round's polynomial has degree two.** -/
theorem shareClaim_polyLE (w z acc : List E) :
    PolyLE 2 fun x ↦ shareClaim prog w z (acc ++ [x]) := by
  have e : ∀ x, shareClaim prog w z (acc ++ [x]) =
      ∑ u ∈ range (2 ^ (4 - (acc.length + 1))),
        wMle w (acc ++ x :: bitsE u (4 - (acc.length + 1))) *
          pMle prog z (acc ++ x :: bitsE u (4 - (acc.length + 1))) := by
    intro x
    simp only [shareClaim, List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append]
  refine PolyLE.congr (PolyLE.sum _ fun u _ ↦ PolyLE.mul (polyLE_mle acc _ 16 _)
    (polyLE_mle acc _ 16 _)) fun x ↦ (e x).symm

/-- **Each round splits the claim**: its values at `0` and `1` add up to the claim before it. -/
theorem shareClaim_split (w z acc : List E) (hacc : acc.length < 4) :
    shareClaim prog w z (acc ++ [0]) + shareClaim prog w z (acc ++ [1]) =
      shareClaim prog w z acc := by
  have hm : 4 - acc.length = (4 - (acc.length + 1)) + 1 := by omega
  simp only [shareClaim, List.length_append, List.length_singleton]
  rw [hm, sum_cube_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [bitsE_two_mul, bitsE_two_mul_add_one]
  simp only [List.append_assoc, List.singleton_append]

/-- **After the rounds the claim is the product** of the two extensions at the challenges. -/
theorem shareClaim_full (w z r : List E) (hr : r.length = 4) :
    shareClaim prog w z r = wMle w r * pMle prog z r := by
  simp [shareClaim, hr, bitsE]

/-- The weights' extension is the verifier's `dot(eq_kernel(r), w)`. -/
theorem wMle_eq_dot (w r : List E) (hw : w.length = 16) (hr : r.length = 4) :
    wMle w r = dot (eqKernel r) w := by
  have h := KeccakGkr.dot_eqKernel r w (by rw [hw, hr]; norm_num)
  rw [show (eqKernel r).take w.length = eqKernel r by
    rw [List.take_of_length_le (by rw [eqKernel_length, hw, hr]; norm_num)]] at h
  rw [h, hw, wMle]

/-- The slots' extension is the stacked bytecode's extension at `z ++ r`. -/
theorem pMle_eq_multilinearEval (z r : List E) (hz : z.length = prog.logSize)
    (hr : r.length = 4) :
    pMle prog z r = multilinearEval ((bytecodeWords prog).map ofK) (z ++ r) := by
  have hlen : ((bytecodeWords prog).map ofK).length = 2 ^ (z.length + 4) := by
    rw [List.length_map, length_bytecodeWords, hz]
  rw [multilinearEval_eq_foldAll, foldAll_append, ← multilinearEval_eq_foldAll,
    multilinearEval_eq r _ (by rw [length_foldAll z _ 4 hlen, hr]), hr, pMle]
  refine sum_congr rfl fun o ho ↦ ?_
  rw [getD_foldAll z _ 4 o hlen (mem_range.mp ho), bcSlot, hz]
  exact congrArg _ (sum_congr rfl fun y _ ↦ mul_comm _ _)

end Share

/-! ## The honest prover -/

/-- **The honest prover of the bytecode's share**: send the share `Σ_x w_x P(z, x)`, run the
honest sumcheck over the slot, then send `P(z, r)` at its challenges. -/
noncomputable def hShare (prog : LeanIsaProgram) (w z : List E) : Script (E × List E × E) :=
  (Script.sendE (bcShare prog w z)).bind fun _ ↦
  (hSumcheck 3 (shareClaim prog w z) (List.replicate busBits none) []).bind fun r ↦
  (Script.sendE (pMle prog z r.1)).bind fun _ ↦
  .ret (bcShare prog w z, z ++ r.1, pMle prog z r.1)

/-- **Completeness of the bytecode's share.** For sixteen slot weights and a point of the
instructions' coordinates, the honest prover follows `bytecodeShare`, to the share, the point
`z ++ r` and the value `P(z, r)` there, the stacked bytecode's extension at that point. -/
theorem follows_bytecodeShare (prog : LeanIsaProgram) (w z : List E) (hw : w.length = 16)
    (hz : z.length = prog.logSize) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ b.1 = bcShare prog w z ∧
        b.2.2 = multilinearEval ((bytecodeWords prog).map ofK) b.2.1)
      (hShare prog w z) (bytecodeShare w z) cs := by
  unfold hShare bytecodeShare
  simp only [VerifierProgram.bind_eq]
  refine Follows.bind (fun cs₁ _ share h ↦ ?_) _ _ _ (Follows.sendE_readE _ cs)
  obtain ⟨rfl, rfl⟩ := h
  rw [← shareClaim_nil prog w z]
  refine Follows.bind (fun cs₂ r r' h ↦ ?_) _ _ _
    (follows_sumcheck 3 (by norm_num) (shareClaim prog w z) (List.replicate busBits none) [] cs₁
      (fun ext hext ↦ by
        simpa using shareClaim_polyLE prog w z ext)
      (fun ext hext ↦ by
        simp only [List.getElem_replicate, RoundSplit, List.nil_append]
        exact shareClaim_split prog w z ext (by simpa [busBits] using hext)))
  obtain ⟨rfl, rfl, hl, hf⟩ := h
  obtain ⟨r, fin⟩ := r
  simp only [List.length_replicate, List.nil_append] at hl hf
  subst hf
  refine Follows.bind (fun cs₃ _ value h ↦ ?_) _ _ _ (Follows.sendE_readE _ cs₂)
  obtain ⟨rfl, rfl⟩ := h
  have hr : r.length = 4 := hl
  rw [shareClaim_full prog w z r hr, wMle_eq_dot w r hw hr, shareClaim_nil]
  simp only [VerifierProgram.require, ↓reduceIte, VerifierProgram.ret_bind]
  exact ⟨rfl, rfl, rfl, pMle_eq_multilinearEval prog z r hz hr⟩

end
end LeanVM.Protocol.EndToEnd.Complete
