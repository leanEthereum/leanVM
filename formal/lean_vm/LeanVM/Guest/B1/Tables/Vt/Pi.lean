/-
  LeanVM.Guest.B1.Tables.Vt.Pi

  `verify_tables`' public input binding and its return: the challenge squeezed after the table
  evaluations, the three memory limbs' claims, and the returned capacity, cursor, round count,
  bytecode value and challenge.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Evals

/-!
# The public input's binding (G:2517-2528)

`vt_pi`: `rm` is the squeeze after the 159 evaluations; the public input's two words are
canonical, and the pool's last three claims are the lines through their limbs `0`, `1` at `rm`
and `0`; the function returns the sponge's capacity after the squeeze, the cursor `159` words
on, `g^n`, the bytecode value and `rm`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The sponge after the evaluations. -/
def vtEvalFs (σ : Val) : Fs := (⟨vtCapV σ 0, []⟩ : Fs).absorbAll (vtEvs σ) dsObserve

theorem vtW159 : word 697932185600 0 = gen ^ 159 := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 697932185600) = gen ^ 159
  rw [gen_pow_eq_ofK, show K.ofBits 697932185600 = Parameters.addressOfIndex 159 by decide +kernel]

theorem vt_evalFs_eq {rd : Reader} {σ : Val} (h : VtH rd σ) :
    vtEvalFs σ = ⟨vtCapV σ 39, [(σ (.n (vtEvB 156)), dsObserve), (σ (.n (vtEvB 157)), dsObserve),
      (σ (.n (vtEvB 158)), dsObserve)]⟩ := by
  obtain ⟨h38, hp38⟩ := vt_evals_fs h 38 (by norm_num)
  have hr : vtEvs σ = (List.range 156).map (fun k ↦ σ (.n (vtEvB k))) ++
      [σ (.n (vtEvB 156)), σ (.n (vtEvB 157)), σ (.n (vtEvB 158))] := by
    show (List.range (156 + 1 + 1 + 1)).map _ = _
    rw [List.range_succ, List.range_succ, List.range_succ, List.map_append, List.map_append,
      List.map_append, List.map_singleton, List.map_singleton, List.map_singleton]
    simp
  have ht : (vtEvs σ).take (4 * (38 + 1)) = (List.range 156).map fun k ↦ σ (.n (vtEvB k)) := by
    rw [hr, List.take_left' (by simp)]
  rw [ht] at h38
  rw [vtEvalFs, hr, fs_absorbAll_append, h38, tb_absorbAll_full' _ (by simp [vtEvs]) _
    (by simp) (by simp), ← hp38]
  rfl

set_option maxRecDepth 10000 in
/-- **The public input's binding and the return.** -/
theorem vt_pi {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 6943) = (vtEvalFs σ).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (6961 + k))) = (vtEvalFs σ).squeeze.2.cap ∧
      σ (.n 6968) = σ (.n 2625) * gen ^ 159 ∧ σ (.n 6969) = σ (.n 2516) ∧
      σ (.n 6970) = σ (.n 581) ∧ σ (.n 6971) = σ (.n 6943) ∧ σ (.n 6972) = σ (.n 2625) ∧
      IsCanonical128 (σ (.n 6)) ∧ IsCanonical128 (σ (.n 7)) ∧
      LoadHolds rd (σ (.n 15)) 164 (multilinearEval [ofK ((σ (.n 6)).limb 0),
        ofK ((σ (.n 7)).limb 0)] [σ (.n 6943)]) ∧
      LoadHolds rd (σ (.n 15)) 165 (multilinearEval [ofK ((σ (.n 6)).limb 1),
        ofK ((σ (.n 7)).limb 1)] [σ (.n 6943)]) ∧
      LoadHolds rd (σ (.n 15)) 166 0 := by
  have z6 := h.atomAt 6353 (.const (.n 6922) (word 0 0)) (by decide +kernel)
  have z7 := h.atomAt 6354 (.const (.n 6923) (word 0 0)) (by decide +kernel)
  have k := h.atomAt 6355 (.keccak [.n 5712, .n 5714, .n 5723, .n 5725, .n 5734, .n 5736, .n 6922,
    .n 6923, .n 5700, .n 5701, .n 5702, .n 5703, .n 5704] (lyOuts 6924) false false)
    (by decide +kernel)
  obtain ⟨_, hch⟩ := h.sliceAt 6356 (challengeT (.n 6924) (.n 6925) 6937) (by decide +kernel)
  rw [holds_challengeT] at hch
  have a10218 := h.atomAt 6365 (.add (.n 6945) (.n 6) (.n 6944)) (by decide +kernel)
  have a10220 := h.atomAt 6366 (.const (.n 6946) (word 1 0 1)) (by decide +kernel)
  have a10221 := h.atomAt 6367 (.mul (.n 6947) (.n 6945) (.n 6946)) (by decide +kernel)
  have a10222 := h.atomAt 6368 (.assertInK (.n 6944) (.n 6947)) (by decide +kernel)
  have a10223 := h.atomAt 6369 (.copy (.n 6948) (.n 6944)) (by decide +kernel)
  have a10225 := h.atomAt 6371 (.add (.n 6950) (.n 7) (.n 6949)) (by decide +kernel)
  have a10226 := h.atomAt 6372 (.const (.n 6951) (word 1 0 1)) (by decide +kernel)
  have a10227 := h.atomAt 6373 (.mul (.n 6952) (.n 6950) (.n 6951)) (by decide +kernel)
  have a10228 := h.atomAt 6374 (.assertInK (.n 6949) (.n 6952)) (by decide +kernel)
  have a10229 := h.atomAt 6375 (.copy (.n 6953) (.n 6949)) (by decide +kernel)
  have a10230 := h.atomAt 6376 (.add (.n 6954) (.n 6948) (.n 6953)) (by decide +kernel)
  have a10231 := h.atomAt 6377 (.mul (.n 6955) (.n 6943) (.n 6954)) (by decide +kernel)
  have a10232 := h.atomAt 6378 (.add (.n 6956) (.n 6948) (.n 6955)) (by decide +kernel)
  have a10233 := h.atomAt 6379 (.load (.n 6956) (.n 15) 164) (by decide +kernel)
  have a10234 := h.atomAt 6380 (.add (.n 6957) (.n 6947) (.n 6952)) (by decide +kernel)
  have a10235 := h.atomAt 6381 (.mul (.n 6958) (.n 6943) (.n 6957)) (by decide +kernel)
  have a10236 := h.atomAt 6382 (.add (.n 6959) (.n 6947) (.n 6958)) (by decide +kernel)
  have a10237 := h.atomAt 6383 (.load (.n 6959) (.n 15) 165) (by decide +kernel)
  have a10238 := h.atomAt 6384 (.const (.n 6960) (word 0 0)) (by decide +kernel)
  have a10239 := h.atomAt 6385 (.load (.n 6960) (.n 15) 166) (by decide +kernel)
  have r0 := h.atomAt 6386 (.copy (.n 6961) (.n 6932)) (by decide +kernel)
  have r1 := h.atomAt 6387 (.copy (.n 6962) (.n 6933)) (by decide +kernel)
  have r2 := h.atomAt 6388 (.copy (.n 6963) (.n 6934)) (by decide +kernel)
  have r3 := h.atomAt 6389 (.copy (.n 6964) (.n 6935)) (by decide +kernel)
  have r4 := h.atomAt 6390 (.copy (.n 6965) (.n 6936)) (by decide +kernel)
  have c10245 := h.atomAt 6391 (.const (.n 6966) (word 697932185600 0)) (by decide +kernel)
  have m10246 := h.atomAt 6392 (.mul (.n 6967) (.n 2625) (.n 6966)) (by decide +kernel)
  have r5 := h.atomAt 6393 (.copy (.n 6968) (.n 6967)) (by decide +kernel)
  have r6 := h.atomAt 6394 (.copy (.n 6969) (.n 2516)) (by decide +kernel)
  have r7 := h.atomAt 6395 (.copy (.n 6970) (.n 581)) (by decide +kernel)
  have r8 := h.atomAt 6396 (.copy (.n 6971) (.n 6943)) (by decide +kernel)
  have r9 := h.atomAt 6397 (.copy (.n 6972) (.n 2625)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at z6 z7 a10218 a10220 a10221 a10222 a10223 a10225
  simp only [Atom.Holds] at a10226 a10227 a10228 a10229 a10230 a10231 a10232
  simp only [Atom.Holds, tb_word_zero] at a10233 a10234 a10235 a10236 a10237 a10238 a10239
  simp only [Atom.Holds] at r0 r1 r2 r3 r4 c10245 m10246 r5 r6 r7 r8 r9
  -- the squeeze
  obtain ⟨hcan, hP, hC⟩ := ly_keccak k
  have e156 := tb_pack_cells (vt_eval h (k := 156) (by norm_num)).2.1
    (hcan _ (by rw [show vtEvB 156 + 7 = 5712 from rfl]; simp))
  have e157 := tb_pack_cells (vt_eval h (k := 157) (by norm_num)).2.1
    (hcan _ (by rw [show vtEvB 157 + 7 = 5723 from rfl]; simp))
  have e158 := tb_pack_cells (vt_eval h (k := 158) (by norm_num)).2.1
    (hcan _ (by rw [show vtEvB 158 + 7 = 5734 from rfl]; simp))
  have hin : ([.n 5712, .n 5714, .n 5723, .n 5725, .n 5734, .n 5736, .n 6922, .n 6923, .n 5700,
      .n 5701, .n 5702, .n 5703, .n 5704] : List V).map σ =
      rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap := by
    rw [vt_evalFs_eq h, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      z6, z7]
    rw [show vtEvB 156 + 7 = 5712 from rfl, show vtEvB 156 + 9 = 5714 from rfl] at e156
    rw [show vtEvB 157 + 7 = 5723 from rfl, show vtEvB 157 + 9 = 5725 from rfl] at e157
    rw [show vtEvB 158 + 7 = 5734 from rfl, show vtEvB 158 + 9 = 5736 from rfl] at e158
    rw [e156.1, e156.2, e157.1, e157.2, e158.1, e158.2]
    rfl
  rw [hin] at hP hC
  -- the public input's limbs
  rw [word_y_inv] at a10220 a10226
  rw [a10221, a10218, a10220] at a10222
  rw [a10227, a10225, a10226] at a10228
  obtain ⟨hc6, hl6⟩ := (split_iff _ _).mp a10222
  obtain ⟨hc7, hl7⟩ := (split_iff _ _).mp a10228
  have hh6 : σ (.n 6947) = ofK ((σ (.n 6)).limb 1) := by
    rw [a10221, a10218, a10220, hl6]; exact split_hi hc6
  have hh7 : σ (.n 6952) = ofK ((σ (.n 7)).limb 1) := by
    rw [a10227, a10225, a10226, hl7]; exact split_hi hc7
  refine ⟨challengeT_value hch.1 (hP 0 (by omega)) (hP 1 (by omega)), ?_, ?_, r6, r7, r8, r9, hc6,
    hc7, ?_, ?_, by rw [← a10238]; exact a10239⟩
  · show _ = capOf (permOf (rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap))
    rw [← hC]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, lyCap, r0, r1, r2, r3, r4]
  · rw [r5, m10246, c10245, vtW159]
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [σ (.n 6943)] =
        σ (.n 6956) := by
      rw [a10232, a10231, a10230, a10229, a10223, ← hl6, ← hl7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a10233
  · have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [σ (.n 6943)] =
        σ (.n 6959) := by
      rw [a10236, a10235, a10234, ← hh6, ← hh7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a10237

end
end LeanVM.Guest.B1.Tables
