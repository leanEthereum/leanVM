/-
  LeanVM.Guest.B1.Tables.Vt.Pi

  `verify_tables`' public input binding and its return: the challenge squeezed after the table
  evaluations, the two memory limbs' claims, and the returned capacity, cursor, round count,
  bytecode value and challenge.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Evals
public import LeanVM.Guest.B1.Bits.Templates

/-!
# The public input's binding (G:2678-2691)

`vt_pi`: `rm` is the squeeze after the 153 evaluations; `split_limbs` splits the public input's
two words (`splitLimbsT`), and the pool's last two claims are the lines through their limbs `0`
and `1` at `rm`; the function returns the sponge's capacity after the squeeze, the cursor `153`
words on, `g^n`, the bytecode value and `rm`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The sponge after the evaluations. -/
def vtEvalFs (σ : Val) : Fs := (⟨vtCapV σ 0, []⟩ : Fs).absorbAll (vtEvs σ) dsObserve

theorem vtW153 : word 10905190400 0 = gen ^ 153 := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 10905190400) = gen ^ 153
  rw [gen_pow_eq_ofK, show K.ofBits 10905190400 = Parameters.addressOfIndex 153 by decide +kernel]

theorem vt_evalFs_eq {rd : Reader} {σ : Val} (h : VtH rd σ) :
    vtEvalFs σ = ⟨vtCapV σ 38, [(σ (.n (vtEvB 152)), dsObserve)]⟩ := by
  obtain ⟨h37, hp37⟩ := vt_evals_fs h 37 (by norm_num)
  have hr : vtEvs σ = (List.range 152).map (fun k ↦ σ (.n (vtEvB k))) ++
      [σ (.n (vtEvB 152))] := by
    show (List.range (152 + 1)).map _ = _
    rw [List.range_succ, List.map_append, List.map_singleton]
  have ht : (vtEvs σ).take (4 * (37 + 1)) = (List.range 152).map fun k ↦ σ (.n (vtEvB k)) := by
    rw [hr, List.take_left' (by simp)]
  rw [ht] at h37
  rw [vtEvalFs, hr, fs_absorbAll_append, h37, tb_absorbAll_full' _ (by simp [vtEvs]) _
    (by simp) (by simp), ← hp37]
  rfl

set_option maxRecDepth 10000 in
/-- **The public input's binding and the return.** -/
theorem vt_pi {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 5966) = (vtEvalFs σ).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (5983 + k))) = (vtEvalFs σ).squeeze.2.cap ∧
      σ (.n 5990) = σ (.n 2652) * gen ^ 153 ∧ σ (.n 5991) = σ (.n 2545) ∧
      σ (.n 5992) = σ (.n 1906) ∧ σ (.n 5993) = σ (.n 5966) ∧ σ (.n 5994) = σ (.n 2652) ∧
      LoadHolds rd (σ (.n 15)) 157 (multilinearEval [ofK ((σ (.n 6)).limb 0),
        ofK ((σ (.n 7)).limb 0)] [σ (.n 5966)]) ∧
      LoadHolds rd (σ (.n 15)) 158 (multilinearEval [ofK ((σ (.n 6)).limb 1),
        ofK ((σ (.n 7)).limb 1)] [σ (.n 5966)]) := by
  have z3 := h.atomAt 2627 (.const (.n 2594) (word 0 0)) (by decide +kernel)
  have z4 := h.atomAt 2628 (.const (.n 2595) (word 0 0)) (by decide +kernel)
  have z5 := h.atomAt 2629 (.const (.n 2596) (word 0 0)) (by decide +kernel)
  have z6 := h.atomAt 2630 (.const (.n 2597) (word 0 0)) (by decide +kernel)
  have k := h.atomAt 5530 (.keccak [.n 4693, .n 4694, .n 2594, .n 2594, .n 2594, .n 2595, .n 2596,
    .n 2597, .n 4687, .n 4688, .n 4689, .n 4690, .n 4691] (lyOuts 5953) false false)
    (by decide +kernel)
  obtain ⟨_, hch⟩ := h.sliceAt 5531 (challengeT (.n 5953) 5966) (by decide +kernel)
  rw [holds_challengeT] at hch
  obtain ⟨_, s6⟩ := h.sliceAt 5532 (splitLimbsT (.n 6) 5967) (by decide +kernel)
  obtain ⟨_, s7⟩ := h.sliceAt 5538 (splitLimbsT (.n 7) 5972) (by decide +kernel)
  rw [holds_splitLimbsT] at s6 s7
  obtain ⟨⟨l6, -, -, h6⟩, -⟩ := s6
  obtain ⟨⟨l7, -, -, h7⟩, -⟩ := s7
  have a5532 := h.atomAt 5537 (.copy (.n 5971) (.n 5967)) (by decide +kernel)
  have a5538 := h.atomAt 5543 (.copy (.n 5976) (.n 5972)) (by decide +kernel)
  have a5539 := h.atomAt 5544 (.add (.n 5977) (.n 5971) (.n 5976)) (by decide +kernel)
  have a5540 := h.atomAt 5545 (.mul (.n 5978) (.n 5966) (.n 5977)) (by decide +kernel)
  have a5541 := h.atomAt 5546 (.add (.n 5979) (.n 5971) (.n 5978)) (by decide +kernel)
  have a5542 := h.atomAt 5547 (.load (.n 5979) (.n 15) 157) (by decide +kernel)
  have a5543 := h.atomAt 5548 (.add (.n 5980) (.n 5970) (.n 5975)) (by decide +kernel)
  have a5544 := h.atomAt 5549 (.mul (.n 5981) (.n 5966) (.n 5980)) (by decide +kernel)
  have a5545 := h.atomAt 5550 (.add (.n 5982) (.n 5970) (.n 5981)) (by decide +kernel)
  have a5546 := h.atomAt 5551 (.load (.n 5982) (.n 15) 158) (by decide +kernel)
  have r0 := h.atomAt 5552 (.copy (.n 5983) (.n 5961)) (by decide +kernel)
  have r1 := h.atomAt 5553 (.copy (.n 5984) (.n 5962)) (by decide +kernel)
  have r2 := h.atomAt 5554 (.copy (.n 5985) (.n 5963)) (by decide +kernel)
  have r3 := h.atomAt 5555 (.copy (.n 5986) (.n 5964)) (by decide +kernel)
  have r4 := h.atomAt 5556 (.copy (.n 5987) (.n 5965)) (by decide +kernel)
  have c5552 := h.atomAt 5557 (.const (.n 5988) (word 10905190400 0)) (by decide +kernel)
  have m5553 := h.atomAt 5558 (.mul (.n 5989) (.n 2652) (.n 5988)) (by decide +kernel)
  have r5 := h.atomAt 5559 (.copy (.n 5990) (.n 5989)) (by decide +kernel)
  have r6 := h.atomAt 5560 (.copy (.n 5991) (.n 2545)) (by decide +kernel)
  have r7 := h.atomAt 5561 (.copy (.n 5992) (.n 1906)) (by decide +kernel)
  have r8 := h.atomAt 5562 (.copy (.n 5993) (.n 5966)) (by decide +kernel)
  have r9 := h.atomAt 5563 (.copy (.n 5994) (.n 2652)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at z3 z4 z5 z6 a5532 a5538 a5539 a5540 a5541 a5542
  simp only [Atom.Holds] at a5543 a5544 a5545 a5546
  simp only [Atom.Holds] at r0 r1 r2 r3 r4 c5552 m5553 r5 r6 r7 r8 r9
  -- the squeeze
  obtain ⟨hP, hC⟩ := ly_keccak k
  have e152 := fsPackT_cells (vt_eval h (k := 152) (by norm_num)).2.1
  have hin : ([.n 4693, .n 4694, .n 2594, .n 2594, .n 2594, .n 2595, .n 2596, .n 2597, .n 4687,
      .n 4688, .n 4689, .n 4690, .n 4691] : List V).map σ =
      rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap := by
    rw [vt_evalFs_eq h, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      z3, z4, z5, z6]
    have e1 : σ (.n 4693) = (Keccak.scalarCells (σ (.n (vtEvB 152))) dsObserve).1 :=
      congrArg Prod.fst e152
    have e2 : σ (.n 4694) = (Keccak.scalarCells (σ (.n (vtEvB 152))) dsObserve).2 :=
      congrArg Prod.snd e152
    rw [e1, e2]
    rfl
  rw [hin] at hP hC
  refine ⟨challengeT_value hch.1 (hP 0 (by omega)), ?_, ?_, r6, r7, r8, r9, ?_, ?_⟩
  · show _ = capOf (permOf (rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap))
    rw [← hC]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, lyCap, r0, r1, r2, r3, r4]
  · rw [r5, m5553, c5552, vtW153]
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [σ (.n 5966)] =
        σ (.n 5979) := by
      rw [a5541, a5540, a5539, a5538, a5532, ← l6, ← l7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a5542
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [σ (.n 5966)] =
        σ (.n 5982) := by
      rw [a5545, a5544, a5543, ← h6, ← h7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a5546

end
end LeanVM.Guest.B1.Tables
