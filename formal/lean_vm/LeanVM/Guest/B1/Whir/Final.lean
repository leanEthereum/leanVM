/-
  LeanVM.Guest.B1.Whir.Final

  The last level's final message and the proof of work after it: the template's block runs the
  Spec's `levelMid` at the last level and `grindP`.
-/

module

public import LeanVM.Guest.B1.Whir.Commit

/-!
# The final message (TRIAGE G #37, #42; G:1491-1492)

The last level reads the final message (its `2^m` words, stored in `final_msg`) and the nonce,
absorbing them, and permutes (`opening_final_message`, `MeaningOpeningFinalMessage`);
`grind_check` reads the permutation's first cell. In the Spec (V:1798-1800, 1752) that is
`levelMid m []` (`readN (2^m)`) and `grindP`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **The last level's final message**, with the grinding check after it: the message's words
and the nonce read at the cursor, the message stored at `final_msg`; they run the Spec's
`levelMid` (its residual) and `grindP`. -/
theorem osFinal_sound {c : OsCfg} {m : ℕ} (hlen : 2 ^ m = c.yrLen)
    (hFm : ∀ args rets, C ("opening_final_message__L" ++ natStr c.yrLen) args rets →
      MeaningOpeningFinalMessage c.yrLen rd args rets)
    {g : ℕ} (hGr : ∀ args rets, C ("grind_check__L" ++ natStr g) args rets →
      MeaningGrindCheck Whir.queryGrindingBits args rets)
    {st : OsSt} (hfs : st.fs.length = 5) (hco : st.co < u128Bound)
    (hok : AllOk C rd σ ((osFinal c st).1 ++
      [.call ("grind_check__L" ++ natStr g) [.n (osFinal c st).2.2] []])) :
    ∃ (ms : List E) (nonce : E), ms.length = c.yrLen ∧
      ReadsAt rd (st.cur σ) (ms ++ [nonce]) ∧ ReadsAt rd (σ (.n osFmsg)) ms ∧
      RunsTo (do
          let r ← levelMid m []
          VerifierProgram.grindProofOfWork Whir.queryGrindingBits
          pure r)
        (st.F σ) (ms ++ [nonce]) (ms, []) ⟨(osFinal c st).2.1.fsv σ, []⟩ ∧
      (osFinal c st).2.1.cur σ = st.cur σ * gen ^ (c.yrLen + 1) ∧
      (osFinal c st).2.1.fs.length = 5 := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  have hF : st.F σ = ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)],
      [(σ (.n st.w0), dsObserve), (σ (.n st.w1), dsObserve)]⟩ := by
    simp [OsSt.F, OsSt.fsv, hf]
  unfold osFinal at hok ⊢
  rw [allOk_append, allOk_append] at hok
  obtain ⟨⟨hm, hok⟩, hgr⟩ := hok
  have hcv := osMat_val hco hm
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, hf, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, osRun, List.range_succ, List.range_zero, Nat.add_zero] at hok hgr
  obtain ⟨-, ms, nonce, hml, hrd, hout, hret⟩ := hFm _ _ hok
  rw [← hF, hcv] at hret
  rw [hcv] at hrd
  set s := ((st.F σ).absorbAll ms dsObserve).absorb nonce dsPowNonce
  simp only [capOf, List.cons_append, List.nil_append, List.cons.injEq] at hret
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, -⟩ := hret
  obtain ⟨-, -, hlow⟩ := hGr _ _ hgr
  have hpow : powOk Whir.queryGrindingBits nonce
      (((st.F σ).absorbAll ms dsObserve).absorb nonce dsPowNonce).squeeze.1 = true := by
    have h17 : ((challengeOf s.perm).limb 0).lane.toNat % 2 ^ Whir.queryGrindingBits = 0 := by
      rw [Keccak.challengeOf_limb0, ← e0]; exact hlow
    simp only [powOk, show Whir.queryGrindingBits ≠ 0 by decide, ↓reduceIte]
    exact decide_eq_true h17
  have e : (do
        let r ← levelMid m []
        VerifierProgram.grindProofOfWork Whir.queryGrindingBits
        pure r) =
      (VerifierProgram.readScalars ms.length).bind fun residual ↦ (VerifierProgram.grindProofOfWork Whir.queryGrindingBits).bind
        fun _ ↦ VerifierProgram.ret (residual, ([] : List (E × List E × (List E → E)))) := by
    simp only [levelMid, hlen, hml, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine ⟨ms, nonce, hml, ?_, hout, ?_, ?_, rfl⟩
  · simpa [OsSt.cur] using hrd
  · rw [e]
    show RunsTo _ (st.F σ) (ms ++ ([nonce] ++ [])) _ _
    refine RunsTo.bind' (runsTo_readN (st.F σ) ms)
      (RunsTo.bind' (runsTo_grindP Whir.queryGrindingBits _ nonce hpow) ?_)
    refine RunsTo.of_eq (runsTo_ret (ms, []) _) rfl rfl rfl ?_
    simp only [OsSt.fsv, List.map_cons, List.map_nil, e1, e2, e3, e4, e5, Fs.squeeze, capOf]
    rfl
  · simp only [OsSt.cur, pow_zero, mul_one, e6]

end
end LeanVM.Guest.B1.Whir
