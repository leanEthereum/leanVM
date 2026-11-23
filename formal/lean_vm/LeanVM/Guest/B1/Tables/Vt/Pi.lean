/-
  LeanVM.Guest.B1.Tables.Vt.Pi

  `verify_tables`' public input binding and its return: the challenge squeezed after the table
  evaluations, the two memory limbs' claims, and the returned capacity, cursor, round count,
  bytecode value and challenge.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Evals
public import LeanVM.Guest.B1.Bits.Templates
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The public input's binding

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
    σ (.n (val% «verify_tables» "nxt[0]@42")) = (vtEvalFs σ).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n ((val% «verify_tables» "s92#0") + k))) = (vtEvalFs σ).squeeze.2.cap ∧
      σ (.n (val% «verify_tables» "s92#0[5]")) = σ (.n (val% «verify_tables» "cursor@5")) * gen ^ 153 ∧ σ (.n (val% «verify_tables» "s92#0[6]")) = σ (.n (val% «verify_tables» "g_zc_n")) ∧
      σ (.n (val% «verify_tables» "s92#0[7]")) = σ (.n (val% «verify_tables» "x@8")) ∧ σ (.n (val% «verify_tables» "s92#0[8]")) = σ (.n (val% «verify_tables» "nxt[0]@42")) ∧ σ (.n (val% «verify_tables» "s92#0[9]")) = σ (.n (val% «verify_tables» "cursor@5")) ∧
      LoadHolds rd (σ (.n (val% «verify_tables» "claim_pool"))) 157 (multilinearEval [ofK ((σ (.n (val% «verify_tables» "pi_0"))).limb 0),
        ofK ((σ (.n (val% «verify_tables» "pi_1"))).limb 0)] [σ (.n (val% «verify_tables» "nxt[0]@42"))]) ∧
      LoadHolds rd (σ (.n (val% «verify_tables» "claim_pool"))) 158 (multilinearEval [ofK ((σ (.n (val% «verify_tables» "pi_0"))).limb 1),
        ofK ((σ (.n (val% «verify_tables» "pi_1"))).limb 1)] [σ (.n (val% «verify_tables» "nxt[0]@42"))]) := by
  have z3 := h.atomAt 2322 (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]")) (word 0 0)) (by decide +kernel)
  have z4 := h.atomAt 2323 (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]")) (word 0 0)) (by decide +kernel)
  have z5 := h.atomAt 2324 (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]")) (word 0 0)) (by decide +kernel)
  have z6 := h.atomAt 2325 (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]")) (word 0 0)) (by decide +kernel)
  have k := h.atomAt 5209 (.keccak [.n (val% «verify_tables» "rate[0]@42"), .n (val% «verify_tables» "rate[1]@42"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"),
    .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "nxt[8]@41"), .n (val% «verify_tables» "nxt[9]@41"), .n (val% «verify_tables» "nxt[10]@41"), .n (val% «verify_tables» "nxt[11]@41"), .n (val% «verify_tables» "nxt[12]@41")] (lyOuts (val% «verify_tables» "nxt[0]@42")) false false)
    (by decide +kernel)
  obtain ⟨_, s6⟩ := h.sliceAt 5210 (splitLimbsT (.n (val% «verify_tables» "pi_0")) 5646) (by decide +kernel)
  obtain ⟨_, s7⟩ := h.sliceAt 5215 (splitLimbsT (.n (val% «verify_tables» "pi_1")) 5650) (by decide +kernel)
  rw [holds_splitLimbsT] at s6 s7
  obtain ⟨⟨l6, -, -, h6⟩, -⟩ := s6
  obtain ⟨⟨l7, -, -, h7⟩, -⟩ := s7
  have a5534 := h.atomAt 5220 (.add (.n (val% «verify_tables» "s88#0")) (.n (val% «verify_tables» "lo[0]@1")) (.n (val% «verify_tables» "lo[0]@2"))) (by decide +kernel)
  have a5535 := h.atomAt 5221 (.mul (.n (val% «verify_tables» "s88#1")) (.n (val% «verify_tables» "nxt[0]@42")) (.n (val% «verify_tables» "s88#0"))) (by decide +kernel)
  have a5536 := h.atomAt 5222 (.add (.n (val% «verify_tables» "s88#2")) (.n (val% «verify_tables» "lo[0]@1")) (.n (val% «verify_tables» "s88#1"))) (by decide +kernel)
  have a5537 := h.atomAt 5223 (.load (.n (val% «verify_tables» "s88#2")) (.n (val% «verify_tables» "claim_pool")) 157) (by decide +kernel)
  have a5538 := h.atomAt 5224 (.add (.n (val% «verify_tables» "s90#0")) (.n (val% «verify_tables» "hi@1")) (.n (val% «verify_tables» "hi@2"))) (by decide +kernel)
  have a5539 := h.atomAt 5225 (.mul (.n (val% «verify_tables» "s90#1")) (.n (val% «verify_tables» "nxt[0]@42")) (.n (val% «verify_tables» "s90#0"))) (by decide +kernel)
  have a5540 := h.atomAt 5226 (.add (.n (val% «verify_tables» "s90#2")) (.n (val% «verify_tables» "hi@1")) (.n (val% «verify_tables» "s90#1"))) (by decide +kernel)
  have a5541 := h.atomAt 5227 (.load (.n (val% «verify_tables» "s90#2")) (.n (val% «verify_tables» "claim_pool")) 158) (by decide +kernel)
  have r0 := h.atomAt 5228 (.copy (.n (val% «verify_tables» "s92#0")) (.n (val% «verify_tables» "nxt[8]@42"))) (by decide +kernel)
  have r1 := h.atomAt 5229 (.copy (.n (val% «verify_tables» "s92#0[1]")) (.n (val% «verify_tables» "nxt[9]@42"))) (by decide +kernel)
  have r2 := h.atomAt 5230 (.copy (.n (val% «verify_tables» "s92#0[2]")) (.n (val% «verify_tables» "nxt[10]@42"))) (by decide +kernel)
  have r3 := h.atomAt 5231 (.copy (.n (val% «verify_tables» "s92#0[3]")) (.n (val% «verify_tables» "nxt[11]@42"))) (by decide +kernel)
  have r4 := h.atomAt 5232 (.copy (.n (val% «verify_tables» "s92#0[4]")) (.n (val% «verify_tables» "nxt[12]@42"))) (by decide +kernel)
  have c5547 := h.atomAt 5233 (.const (.n (val% «verify_tables» "s92#1")) (word 10905190400 0)) (by decide +kernel)
  have m5548 := h.atomAt 5234 (.mul (.n (val% «verify_tables» "s92#2")) (.n (val% «verify_tables» "cursor@5")) (.n (val% «verify_tables» "s92#1"))) (by decide +kernel)
  have r5 := h.atomAt 5235 (.copy (.n (val% «verify_tables» "s92#0[5]")) (.n (val% «verify_tables» "s92#2"))) (by decide +kernel)
  have r6 := h.atomAt 5236 (.copy (.n (val% «verify_tables» "s92#0[6]")) (.n (val% «verify_tables» "g_zc_n"))) (by decide +kernel)
  have r7 := h.atomAt 5237 (.copy (.n (val% «verify_tables» "s92#0[7]")) (.n (val% «verify_tables» "x@8"))) (by decide +kernel)
  have r8 := h.atomAt 5238 (.copy (.n (val% «verify_tables» "s92#0[8]")) (.n (val% «verify_tables» "nxt[0]@42"))) (by decide +kernel)
  have r9 := h.atomAt 5239 (.copy (.n (val% «verify_tables» "s92#0[9]")) (.n (val% «verify_tables» "cursor@5"))) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at z3 z4 z5 z6 a5534 a5535 a5536 a5537
  simp only [Atom.Holds] at a5538 a5539 a5540 a5541
  simp only [Atom.Holds] at r0 r1 r2 r3 r4 c5547 m5548 r5 r6 r7 r8 r9
  -- the squeeze
  obtain ⟨hP, hC⟩ := ly_keccak k
  have e152 := fsPackT_cells (vt_eval h (k := 152) (by norm_num)).2.1
  have hin : ([.n (val% «verify_tables» "rate[0]@42"), .n (val% «verify_tables» "rate[1]@42"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "nxt[8]@41"),
      .n (val% «verify_tables» "nxt[9]@41"), .n (val% «verify_tables» "nxt[10]@41"), .n (val% «verify_tables» "nxt[11]@41"), .n (val% «verify_tables» "nxt[12]@41")] : List V).map σ =
      rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap := by
    rw [vt_evalFs_eq h, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      z3, z4, z5, z6]
    have e1 : σ (.n (val% «verify_tables» "rate[0]@42")) = (Keccak.scalarCells (σ (.n (vtEvB 152))) dsObserve).1 :=
      congrArg Prod.fst e152
    have e2 : σ (.n (val% «verify_tables» "rate[1]@42")) = (Keccak.scalarCells (σ (.n (vtEvB 152))) dsObserve).2 :=
      congrArg Prod.snd e152
    rw [e1, e2]
    rfl
  rw [hin] at hP hC
  refine ⟨challengeT_value (s0 := .n (val% «verify_tables» "nxt[0]@42")) (b := 5633) rfl (hP 0 (by omega)), ?_, ?_, r6, r7, r8, r9, ?_, ?_⟩
  · show _ = capOf (permOf (rateOf (vtEvalFs σ).pend ++ (vtEvalFs σ).cap))
    rw [← hC]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, lyCap, r0, r1, r2, r3, r4]
  · rw [r5, m5548, c5547, vtW153]
  · have e : multilinearEval [ofK ((σ (.n (val% «verify_tables» "pi_0"))).limb 0), ofK ((σ (.n (val% «verify_tables» "pi_1"))).limb 0)] [σ (.n (val% «verify_tables» "nxt[0]@42"))] =
        σ (.n (val% «verify_tables» "s88#2")) := by
      rw [a5536, a5535, a5534, ← l6, ← l7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a5537
  · have e : multilinearEval [ofK ((σ (.n (val% «verify_tables» "pi_0"))).limb 1), ofK ((σ (.n (val% «verify_tables» "pi_1"))).limb 1)] [σ (.n (val% «verify_tables» "nxt[0]@42"))] =
        σ (.n (val% «verify_tables» "s90#2")) := by
      rw [a5540, a5539, a5538, ← h6, ← h7]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [e]; exact a5541

end
end LeanVM.Guest.B1.Tables
