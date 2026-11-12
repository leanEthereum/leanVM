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
bound, of the weights and the slots `P(z, ·)` (`slotList`), each folded at `acc` (`shareClaim`):
before the rounds it is the share (`shareClaim_nil`), each round's polynomial has degree two
(`shareClaim_polyLE`) and splits the running claim (`shareClaim_split`), and after the four rounds
it is the product the verifier checks (`shareClaim_full`, `multilinearEval_eq_dot`,
`slotList_multilinearEval`).

* `follows_bytecodeShare`: the honest prover `hShare` follows `bytecodeShare`, to the share
  `bcShare prog w z`, the point `z ++ r` and the value `P(z, r)`, which is the stacked bytecode's
  extension there, so `computedBytecodeValue` accepts it (`follows_bytecodeShare`).
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd.Front Finset
open LeanVM.Protocol.KeccakGkr (multilinearEval_eq eqKernel_length)

@[expose] public section

section Share

variable (prog : LeanIsaProgram)

/-- The stacked bytecode's sixteen slots at the instructions' point `z`, `P(z, x)`. -/
noncomputable def slotList (z : List E) : List E := (List.range 16).map (bcSlot prog · z)

/-- The running claim of the share's sumcheck after the challenges `acc`: the weights and the
slots, each folded at `acc` (the low bit first), multiplied entry by entry and summed. -/
noncomputable def shareClaim (w z acc : List E) : E :=
  ∑ i ∈ range (2 ^ (4 - acc.length)),
    (foldAll w acc).getD i 0 * (foldAll (slotList prog z) acc).getD i 0

theorem length_slotList (z : List E) : (slotList prog z).length = 16 := by simp [slotList]

theorem getD_slotList (z : List E) {k : ℕ} (hk : k < 16) :
    (slotList prog z).getD k 0 = bcSlot prog k z := by
  rw [slotList, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

/-- **Before the rounds the claim is the share.** -/
theorem shareClaim_nil (w z : List E) : shareClaim prog w z [] = bcShare prog w z := by
  simp only [shareClaim, List.length_nil, Nat.sub_zero, foldAll_nil, bcShare]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [getD_slotList prog z (by simpa using mem_range.mp hk)]

/-- One more challenge folds the tables. -/
theorem shareClaim_snoc (w z acc : List E) (x : E) (hw : w.length = 16)
    (hacc : acc.length < 4) :
    shareClaim prog w z (acc ++ [x]) =
      ∑ i ∈ range (2 ^ (4 - (acc.length + 1))),
        ((foldAll w acc).getD (2 * i) 0 * (1 + x) + (foldAll w acc).getD (2 * i + 1) 0 * x) *
          ((foldAll (slotList prog z) acc).getD (2 * i) 0 * (1 + x) +
            (foldAll (slotList prog z) acc).getD (2 * i + 1) 0 * x) := by
  have hm : 4 - acc.length = (4 - (acc.length + 1)) + 1 := by omega
  have hw' : (foldAll w acc).length = 2 ^ (4 - acc.length) :=
    length_foldAll acc w _ (by rw [hw, show acc.length + (4 - acc.length) = 4 by omega]; rfl)
  have hp' : (foldAll (slotList prog z) acc).length = 2 ^ (4 - acc.length) :=
    length_foldAll acc _ _ (by
      rw [length_slotList, show acc.length + (4 - acc.length) = 4 by omega]; rfl)
  simp only [shareClaim, List.length_append, List.length_singleton, foldAll_concat]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  have hlt : 2 * i + 1 < 2 ^ (4 - acc.length) := by rw [hm, pow_succ]; omega
  rw [getD_foldPairs _ _ _ (by rw [hw']; exact hlt), getD_foldPairs _ _ _ (by rw [hp']; exact hlt)]

/-- **Each round's polynomial has degree two.** -/
theorem shareClaim_polyLE (w z acc : List E) (hw : w.length = 16) (hacc : acc.length < 4) :
    PolyLE 2 fun x ↦ shareClaim prog w z (acc ++ [x]) := by
  refine PolyLE.congr (PolyLE.sum _ fun i _ ↦ PolyLE.mul
    ((PolyLE.affine ((foldAll w acc).getD (2 * i) 0)
      ((foldAll w acc).getD (2 * i) 0 + (foldAll w acc).getD (2 * i + 1) 0)).congr
        fun x ↦ by ring)
    ((PolyLE.affine ((foldAll (slotList prog z) acc).getD (2 * i) 0)
      ((foldAll (slotList prog z) acc).getD (2 * i) 0 +
        (foldAll (slotList prog z) acc).getD (2 * i + 1) 0)).congr fun x ↦ by ring))
    fun x ↦ (shareClaim_snoc prog w z acc x hw hacc).symm

/-- **Each round splits the claim**: its values at `0` and `1` add up to the claim before it. -/
theorem shareClaim_split (w z acc : List E) (hw : w.length = 16) (hacc : acc.length < 4) :
    shareClaim prog w z (acc ++ [0]) + shareClaim prog w z (acc ++ [1]) =
      shareClaim prog w z acc := by
  rw [shareClaim_snoc prog w z acc 0 hw hacc, shareClaim_snoc prog w z acc 1 hw hacc,
    ← sum_add_distrib, shareClaim]
  rw [show 2 ^ (4 - acc.length) = 2 * 2 ^ (4 - (acc.length + 1)) by
    rw [← pow_succ', show 4 - (acc.length + 1) + 1 = 4 - acc.length by omega],
    KeccakGkr.sum_range_two_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  have h2 : (1 : E) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharTwo.two_eq_zero
  simp only [add_zero, mul_one, mul_zero, h2]
  ring

/-- **After the rounds the claim is the product** of the two extensions at the challenges. -/
theorem shareClaim_full (w z r : List E) (hr : r.length = 4) :
    shareClaim prog w z r =
      multilinearEval w r * multilinearEval (slotList prog z) r := by
  simp only [shareClaim, hr, Nat.sub_self, pow_zero, sum_range_one, multilinearEval_eq_foldAll,
    List.headD_eq_getD]

/-- The weights' extension is the verifier's `dot(eq_kernel(r), w)`. -/
theorem multilinearEval_eq_dot (w r : List E) (hw : w.length = 16) (hr : r.length = 4) :
    multilinearEval w r = dot (eqKernel r) w := by
  have h := KeccakGkr.dot_eqKernel r w (by rw [hw, hr]; norm_num)
  rw [show (eqKernel r).take w.length = eqKernel r by
    rw [List.take_of_length_le (by rw [eqKernel_length, hw, hr]; norm_num)]] at h
  rw [h, multilinearEval_eq r w (by rw [hw, hr]; norm_num), hr, hw]
  rfl

/-- The slots' extension is the stacked bytecode's extension at `z ++ r`. -/
theorem slotList_multilinearEval (z r : List E) (hz : z.length = prog.logSize)
    (hr : r.length = 4) :
    multilinearEval (slotList prog z) r =
      multilinearEval ((bytecodeWords prog).map ofK) (z ++ r) := by
  have hlen : ((bytecodeWords prog).map ofK).length = 2 ^ (z.length + 4) := by
    rw [List.length_map, length_bytecodeWords, hz]
  rw [multilinearEval_eq_foldAll ((bytecodeWords prog).map ofK), foldAll_append,
    ← multilinearEval_eq_foldAll, multilinearEval_eq r _ (by rw [length_slotList, hr]; norm_num),
    multilinearEval_eq r _ (by rw [length_foldAll z _ 4 hlen, hr])]
  refine sum_congr rfl fun o ho ↦ ?_
  have ho' : o < 16 := by rw [hr] at ho; simpa using ho
  rw [getD_foldAll z _ 4 o hlen (by rw [hr] at ho; simpa using ho), slotList,
    List.getD_eq_getElem _ _ (by simpa using ho')]
  simp only [List.getElem_map, List.getElem_range, bcSlot, hz]
  exact congrArg _ (sum_congr rfl fun y _ ↦ mul_comm _ _)

end Share

/-! ## The honest prover -/

/-- **The honest prover of the bytecode's share**: send the share `Σ_x w_x P(z, x)`, run the
honest sumcheck over the slot, then send `P(z, r)` at its challenges. -/
noncomputable def hShare (prog : LeanIsaProgram) (w z : List E) : Script (E × List E × E) :=
  (Script.sendE (bcShare prog w z)).bind fun _ ↦
  (hSumcheck 3 (shareClaim prog w z) (List.replicate busBits none) []).bind fun r ↦
  (Script.sendE (multilinearEval (slotList prog z) r.1)).bind fun _ ↦
  .ret (bcShare prog w z, z ++ r.1, multilinearEval (slotList prog z) r.1)

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
        simpa using shareClaim_polyLE prog w z ext hw (by simpa [busBits] using hext))
      (fun ext hext ↦ by
        simp only [List.getElem_replicate, RoundSplit, List.nil_append]
        exact shareClaim_split prog w z ext hw (by simpa [busBits] using hext)))
  obtain ⟨rfl, rfl, hl, hf⟩ := h
  obtain ⟨r, fin⟩ := r
  simp only [List.length_replicate, List.nil_append] at hl hf
  subst hf
  refine Follows.bind (fun cs₃ _ value h ↦ ?_) _ _ _ (Follows.sendE_readE _ cs₂)
  obtain ⟨rfl, rfl⟩ := h
  have hr : r.length = 4 := hl
  rw [shareClaim_full prog w z r hr, multilinearEval_eq_dot w r hw hr, shareClaim_nil]
  simp only [VerifierProgram.require, ↓reduceIte, VerifierProgram.ret_bind]
  exact ⟨rfl, rfl, rfl, slotList_multilinearEval prog z r hz hr⟩

end
end LeanVM.Protocol.EndToEnd.Complete
