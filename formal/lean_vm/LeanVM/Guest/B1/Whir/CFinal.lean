/-
  LeanVM.Guest.B1.Whir.CFinal

  The last level's final message and its proof of work, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFold
public import LeanVM.Guest.B1.Whir.Final

/-!
# The final message, honestly

`osFinal_complete`: the final message and the nonce at the cursor, the message in `final_msg`,
the nonce's proof of work passing: the block, with `grind_check` after it, holds
(`opening_final_message`, `grind_check` holding of their meanings), the sponge after the nonce's
permutation carried (`FinalOut`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- What a final message leaves: the permutation's capacity carried, nothing waiting. -/
structure FinalOut (σ : Val) (st st' : OsSt) (S : Fs) (n : ℕ) : Prop where
  F : st'.fsv σ = S.squeeze.2.cap
  cur : st'.cur σ = st.cur σ * gen ^ (n + 1)
  fs : st'.fs.length = 5
  can : AllCanonical (st'.fsv σ)
  co : st'.co = 0
  below : st'.Below
  pad : st'.pad = st.pad
  w0 : st'.w0 = st.w0
  w1 : st'.w1 = st.w1

/-- A proof of work's word: the permutation's first cell's low bits. -/
theorem grind_meaning {bits : ℕ} (hb : bits ≠ 0) {n : E} {S : Fs}
    (h : powOk bits n S.squeeze.1 = true) :
    MeaningGrindCheck bits [cellsOfState S.perm false 0] [] := by
  refine ⟨rfl, cellsOfState_canonical _ _ _, ?_⟩
  simp only [powOk, hb, ↓reduceIte, decide_eq_true_eq] at h
  rw [← Keccak.challengeOf_limb0]
  exact h

theorem osFinal_below (c : OsCfg) {st : OsSt} (hb : st.Below) : (osFinal c st).2.1.Below := by
  have := osMat_next st.cb st.co st.k
  have := hb.w0; have := hb.w1; have := hb.c; have := hb.b; have := hb.a; have := hb.t
  refine ⟨fun f hf ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [osFinal] at *
  all_goals omega

/-- The values of a final message after its pointer. -/
def finalVals (σ : Val) (st : OsSt) (ms : List E) (nonce : E) : List E :=
  let S := ((st.F σ).absorbAll ms dsObserve).absorb nonce dsPowNonce
  [cellsOfState S.perm false 0] ++ capOf S.perm ++ [st.cur σ * gen ^ (ms.length + 1), nonce]

/-- The block's values. -/
def osFinalF (σ : Val) (st : OsSt) (ms : List E) (nonce : E) (i : ℕ) : E :=
  if i < (osMat st.cb st.co st.k).2.2 then matVal σ st.cb st.co st.k i
  else (finalVals σ st ms nonce).getD (i - (osMat st.cb st.co st.k).2.2) 0

/-- **The final message and its proof of work, honestly.** -/
theorem osFinal_complete {c : OsCfg} {FM : E}
    (hFm : ∀ args rets, MeaningOpeningFinalMessage c.yrLen rd args rets → args.getD 8 0 = FM →
      C ("opening_final_message__L" ++ natStr c.yrLen) args rets)
    {g : ℕ} (hGr : ∀ args rets, MeaningGrindCheck Whir.queryGrindingBits args rets →
      C ("grind_check__L" ++ natStr g) args rets)
    {st : OsSt} (σ : Val) (hfs : st.fs.length = 5) (hco : st.co < u128Bound) (hb : st.Below)
    (hcan : AllCanonical (st.fsv σ)) (hfm : osFmsg < st.k) (hFM : σ (.n osFmsg) = FM)
    {ms : List E} {nonce : E}
    (hml : ms.length = c.yrLen) (hrd : ReadsAt rd (st.cur σ) (ms ++ [nonce]))
    (hout : ReadsAt rd (σ (.n osFmsg)) ms)
    (hpow : powOk Whir.queryGrindingBits nonce
      (((st.F σ).absorbAll ms dsObserve).absorb nonce dsPowNonce).squeeze.1 = true) :
    BlkF C rd σ st.k (osFinal c st).2.1.k (osFinalF σ st ms nonce)
      ((osFinal c st).1 ++ [.call ("grind_check__L" ++ natStr g) [.n (osFinal c st).2.2] []])
      (fun σ' ↦ FinalOut σ' st (osFinal c st).2.1
        (((st.F σ).absorbAll ms dsObserve).absorb nonce dsPowNonce) c.yrLen ∧
        AgreeBelow st.k σ σ') := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  intro σ' ha hv
  have hk' : (osFinal c st).2.1.k = (osMat st.cb st.co st.k).2.2 + 8 := rfl
  have hmk : st.k ≤ (osMat st.cb st.co st.k).2.2 := osMat_next _ _ _
  have hmv : RangeVals σ' st.k (osMat st.cb st.co st.k).2.2 (matVal σ st.cb st.co st.k) :=
    fun i h1 h2 ↦ by
      rw [hv i h1 (by omega)]
      simp only [osFinalF, h2, ↓reduceIte]
  obtain ⟨okm, hcur⟩ := osMat_complete (C := C) (rd := rd) hco hb.cb ha hmv
  have hval : ∀ j < 8, σ' (.n ((osMat st.cb st.co st.k).2.2 + j)) =
      (finalVals σ st ms nonce).getD j 0 := fun j hj ↦ by
    rw [hv _ (by omega) (by omega)]
    simp only [osFinalF, show ¬ ((osMat st.cb st.co st.k).2.2 + j < (osMat st.cb st.co st.k).2.2)
      by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  set r := (osMat st.cb st.co st.k).2.2 with hr
  have hfl : ∀ f ∈ st.fs, f < st.k := hb.fs
  rw [hf] at hfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hfl
  have hagree : ∀ i < st.k, σ' (.n i) = σ (.n i) := ha
  obtain ⟨-, hFe, -, -, hCe⟩ := OsSt.agree hb ha
  set S := ((st.F σ).absorbAll ms dsObserve).absorb nonce dsPowNonce with hS
  have v : ∀ j, j < 8 → σ' (.n (r + j)) = _ := hval
  simp only [finalVals, ← hS, capOf, List.getD_eq_getElem?_getD] at v
  have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
  have v3 := v 3 (by omega); have v4 := v 4 (by omega); have v5 := v 5 (by omega)
  have v6 := v 6 (by omega); have v7 := v 7 (by omega)
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)],
      [(σ (.n st.w0), dsObserve), (σ (.n st.w1), dsObserve)]⟩ := by
    simp [OsSt.F, OsSt.fsv, hf]
  refine ⟨?_, ⟨?_, ?_, by simp [osFinal], ?_, rfl, ?_, rfl, rfl, rfl⟩, ha⟩
  · simp only [osFinal]
    rw [allOk_append, allOk_append]
    refine ⟨⟨okm, ?_⟩, ?_⟩
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, List.map_cons, List.map_nil, osRun,
        List.range_succ, List.range_zero, List.nil_append, List.cons_append, hf, Nat.add_zero]
      refine hFm _ _ ?_ (by simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [hagree osFmsg hfm, hFM])
      rw [hagree f0 hfl.1, hagree f1 hfl.2.1, hagree f2 hfl.2.2.1, hagree f3 hfl.2.2.2.1,
        hagree f4 hfl.2.2.2.2, hagree st.w0 hb.w0, hagree st.w1 hb.w1, hcur,
        hagree osFmsg hfm, v0, v1, v2, v3, v4, v5, v6, v7]
      refine ⟨by simpa [OsSt.fsv, hf] using hcan, ms, nonce, hml, ?_, hout, ?_⟩
      · simpa [OsSt.cur] using hrd
      · rw [← hF, ← hS, hml]
        simp only [capOf, OsSt.cur, List.cons_append, List.nil_append]
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, List.map_cons, List.map_nil]
      apply hGr
      rw [v0]
      exact grind_meaning (by decide) hpow
  · simp only [OsSt.fsv, osFinal, List.map_cons, List.map_nil, Fs.squeeze, capOf]
    rw [v1, v2, v3, v4, v5]
  · rw [hCe]
    simp only [OsSt.cur, osFinal, pow_zero, mul_one]
    rw [v6, hml]
    rfl
  · simp only [OsSt.fsv, osFinal, List.map_cons, List.map_nil]
    rw [v1, v2, v3, v4, v5]
    exact squeeze_cap_canonical S
  · exact osFinal_below c hb

end
end LeanVM.Guest.B1.Whir
