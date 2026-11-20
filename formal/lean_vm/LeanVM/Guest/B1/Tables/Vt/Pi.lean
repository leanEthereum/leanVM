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
# The public input's binding

`vt_pi`: `rm` is the squeeze after the 153 evaluations; `split_limbs` splits the public input's
two words (`splitLimbsT`), and the pool's last two claims are the lines through their limbs `0`
and `1` at `rm`; the function returns the sponge's capacity after the squeeze, the cursor `153`
words on, `g^n`, the bytecode value and `rm`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
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
    σ (.n 5600) = (vtEvalFs σ).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (5627 + k))) = (vtEvalFs σ).squeeze.2.cap ∧
      σ (.n 5634) = σ (.n 2299) * gen ^ 153 ∧ σ (.n 5635) = σ (.n 2197) ∧
      σ (.n 5636) = σ (.n 1558) ∧ σ (.n 5637) = σ (.n 5600) ∧ σ (.n 5638) = σ (.n 2299) ∧
      LoadHolds rd (σ (.n 15)) 157 (multilinearEval [ofK ((σ (.n 6)).limb 0),
        ofK ((σ (.n 7)).limb 0)] [σ (.n 5600)]) ∧
      LoadHolds rd (σ (.n 15)) 158 (multilinearEval [ofK ((σ (.n 6)).limb 1),
        ofK ((σ (.n 7)).limb 1)] [σ (.n 5600)]) := by
  have z3 := h.atomAt 2268 (.const (.n 2246) (word 0 0)) (by decide +kernel)
  have z4 := h.atomAt 2269 (.const (.n 2247) (word 0 0)) (by decide +kernel)
  have z5 := h.atomAt 2270 (.const (.n 2248) (word 0 0)) (by decide +kernel)
  have z6 := h.atomAt 2271 (.const (.n 2249) (word 0 0)) (by decide +kernel)
  have k := h.atomAt 5165 (.keccak [.n 4340, .n 4341, .n 2246, .n 2246, .n 2246, .n 2247, .n 2248,
    .n 2249, .n 4334, .n 4335, .n 4336, .n 4337, .n 4338] (lyOuts 5600) false false)
    (by decide +kernel)
  obtain ⟨_, s6⟩ := h.sliceAt 5166 (splitLimbsT (.n 6) 5613) (by decide +kernel)
  obtain ⟨_, s7⟩ := h.sliceAt 5171 (splitLimbsT (.n 7) 5617) (by decide +kernel)
  rw [holds_splitLimbsT] at s6 s7
  obtain ⟨⟨l6, -, -, h6⟩, -⟩ := s6
  obtain ⟨⟨l7, -, -, h7⟩, -⟩ := s7
  have a5534 := h.atomAt 5176 (.add (.n 5621) (.n 5613) (.n 5617)) (by decide +kernel)
  have a5535 := h.atomAt 5177 (.mul (.n 5622) (.n 5600) (.n 5621)) (by decide +kernel)
  have a5536 := h.atomAt 5178 (.add (.n 5623) (.n 5613) (.n 5622)) (by decide +kernel)
  have a5537 := h.atomAt 5179 (.load (.n 5623) (.n 15) 157) (by decide +kernel)
  have a5538 := h.atomAt 5180 (.add (.n 5624) (.n 5616) (.n 5620)) (by decide +kernel)
  have a5539 := h.atomAt 5181 (.mul (.n 5625) (.n 5600) (.n 5624)) (by decide +kernel)
  have a5540 := h.atomAt 5182 (.add (.n 5626) (.n 5616) (.n 5625)) (by decide +kernel)
  have a5541 := h.atomAt 5183 (.load (.n 5626) (.n 15) 158) (by decide +kernel)
  have r0 := h.atomAt 5184 (.copy (.n 5627) (.n 5608)) (by decide +kernel)
  have r1 := h.atomAt 5185 (.copy (.n 5628) (.n 5609)) (by decide +kernel)
  have r2 := h.atomAt 5186 (.copy (.n 5629) (.n 5610)) (by decide +kernel)
  have r3 := h.atomAt 5187 (.copy (.n 5630) (.n 5611)) (by decide +kernel)
  have r4 := h.atomAt 5188 (.copy (.n 5631) (.n 5612)) (by decide +kernel)
  have c5547 := h.atomAt 5189 (.const (.n 5632) (word 10905190400 0)) (by decide +kernel)
  have m5548 := h.atomAt 5190 (.mul (.n 5633) (.n 2299) (.n 5632)) (by decide +kernel)
  have r5 := h.atomAt 5191 (.copy (.n 5634) (.n 5633)) (by decide +kernel)
  have r6 := h.atomAt 5192 (.copy (.n 5635) (.n 2197)) (by decide +kernel)
  have r7 := h.atomAt 5193 (.copy (.n 5636) (.n 1558)) (by decide +kernel)
  have r8 := h.atomAt 5194 (.copy (.n 5637) (.n 5600)) (by decide +kernel)
  have r9 := h.atomAt 5195 (.copy (.n 5638) (.n 2299)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at z3 z4 z5 z6 a5534 a5535 a5536 a5537
  simp only [Atom.Holds] at a5538 a5539 a5540 a5541
  simp only [Atom.Holds] at r0 r1 r2 r3 r4 c5547 m5548 r5 r6 r7 r8 r9
  -- the squeeze
  obtain ⟨hP, hC⟩ := ly_keccak k
  have e152 := fsPackT_cells (vt_eval h (k := 152) (by norm_num)).2.1
  have hin : ([.n 4340, .n 4341, .n 2246, .n 2246, .n 2246, .n 2247, .n 2248, .n 2249, .n 4334,
      .n 4335, .n 4336, .n 4337, .n 4338] : List V).map σ =
      rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap := by
    rw [vt_evalFs_eq h, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      z3, z4, z5, z6]
    have e1 : σ (.n 4340) = (Keccak.scalarCells (σ (.n (vtEvB 152))) dsObserve).1 :=
      congrArg Prod.fst e152
    have e2 : σ (.n 4341) = (Keccak.scalarCells (σ (.n (vtEvB 152))) dsObserve).2 :=
      congrArg Prod.snd e152
    rw [e1, e2]
    rfl
  rw [hin] at hP hC
  refine ⟨challengeT_value (s0 := .n 5600) (b := 5600) rfl (hP 0 (by omega)), ?_, ?_, r6, r7, r8, r9, ?_, ?_⟩
  · show _ = capOf (permOf (rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap))
    rw [← hC]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, lyCap, r0, r1, r2, r3, r4]
  · rw [r5, m5548, c5547, vtW153]
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [σ (.n 5600)] =
        σ (.n 5623) := by
      rw [a5536, a5535, a5534, ← l6, ← l7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a5537
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [σ (.n 5600)] =
        σ (.n 5626) := by
      rw [a5540, a5539, a5538, ← h6, ← h7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a5541

end
end LeanVM.Guest.B1.Tables
