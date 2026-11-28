module

public import LeanVM.Guest.Complete.Agg.Wins
public import LeanVM.Guest.Complete.Agg.Loop0A
public import LeanVM.Guest.Complete.Agg.Loop1A
public import LeanVM.Guest.Complete.Agg.Loop2A
public import LeanVM.Guest.Complete.Agg.Loop3A
public import LeanVM.Guest.Complete.Agg.SumcheckA
public import LeanVM.Guest.Data.NameStrings

/-!
# `aggregate_claims`' callees, at every position

The call windows of `wAgg` take their callee's `AtEvery` (`winsHypT_cif_of_atEvery`,
`winsHypT_call_of_atEvery`). `atEvery_of_completesA`: a callee
placed at every position past its block (`agg_bs_callCompletesA`) gives it for that block. `agg_loop{0,1,2,3}_atEvery`, `agg_bs_atEvery`: the five callees so.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Complete
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **A loop helper from its first counter, at every position**, ending at its cursor. -/
theorem atEveryB_of_loop {al : String → Bool} {k m : ℕ} {f : String} {args : ℕ → List E} {R : ℕ → Prop}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B : ℕ → ℕ} {T β : ℕ} (hm : m ≠ 0)
    (H : ∀ j < m, ∀ fp c, fp + B (m - j) ≤ c → CallAtA B2C.fs al B2C.cert k f (args j) [] R (fun _ => False)
      (fun _ => True) Pre Post (B (m - j)) fp c c) :
    AtEveryB al k f (args 0) [] R Pre Post (B m) 0 T β :=
  atEveryB_of_le fun fp c _ hfc => ⟨c, le_rfl, by simpa using H 0 (Nat.pos_of_ne_zero hm) fp c (by simpa using hfc)⟩

/-- **A callee placed at every position past its block, at every position.** -/
theorem atEvery_of_completesA {al : String → Bool} {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop}
    {D : ℕ → ℕ → ℕ → Prop} {Pre : Reader → Prop} {Post : Reader → Tree → Prop}
    (h : CallCompletesA B2C.fs al B2C.cert k f args rets R D (fun _ => True) Pre Post) :
    ∃ B, AtEvery al k f args rets R Pre Post B 0 := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun fp c _ hfc => ?_⟩
  obtain ⟨e, he⟩ := hB fp c hfc
  exact ⟨e, he.mono (fun _ h => h) (fun _ h => h.elim) (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)⟩

section
variable {al : String → Bool} {k m : ℕ} {R : ℕ → Prop} {Pre : Reader → Prop} {T β : ℕ}

set_option maxRecDepth 20000 in
theorem agg_loop0_atEvery (hm : m < 2 ^ 34) (hm0 : m ≠ 0) {st : ℕ → Fs} {iab ipi icf ilf icc ilc : ℕ}
    (hpre : ∀ rd, Pre rd → ∀ c < m, A0PreA st iab ipi icf ilf icc ilc rd c)
    (hR : ∀ c < m, ∀ i, A0Reg iab ipi icf ilf icc ilc c i → R i) :
    AtEveryB al k name% «aggregate_claims_loop0»
      (gen ^ 0 :: gen ^ m :: [ptrAt iab, ptrAt icf, ptrAt ilf, ptrAt icc, ptrAt ilc, ptrAt ipi]) [] R Pre FreePost
      (lpBlk B2C.fs name% «aggregate_claims_loop0» m) 0 T β :=
  atEveryB_of_loop (args := fun j => gen ^ j :: gen ^ m :: [ptrAt iab, ptrAt icf, ptrAt ilf, ptrAt icc, ptrAt ilc,
    ptrAt ipi]) hm0 (agg_loop0_callAtA hm hpre hR)

set_option maxRecDepth 20000 in
theorem agg_loop1_atEvery (hm : m < 2 ^ 34) (hm0 : m ≠ 0) {lf e v : ℕ} {qs : ℕ → ℕ}
    (hpre : ∀ rd, Pre rd → ∀ c < m, LoadHolds rd (ptrAt lf * gen ^ c) 0 (ptrAt (qs c)) ∧
      (∀ i < 36, ∃ w, LoadHolds rd (ptrAt e) i w) ∧ (∀ i < 36, ∃ w, LoadHolds rd (ptrAt (qs c)) (19 + i) w) ∧
      LoadHolds rd (ptrAt v * gen ^ c) 0 (fvAcc rd (ptrAt e) (ptrAt (qs c)) 36))
    (hR : ∀ c < m, ∀ i, A1Reg lf e (qs c) v c i → R i) :
    AtEveryB al k name% «aggregate_claims_loop1» (gen ^ 0 :: gen ^ m :: [ptrAt lf, ptrAt e, ptrAt v]) [] R Pre
      FreePost (lpBlk B2C.fs name% «aggregate_claims_loop1» m) 0 T β :=
  atEveryB_of_loop (args := fun j => gen ^ j :: gen ^ m :: [ptrAt lf, ptrAt e, ptrAt v]) hm0
    (agg_loop1_callAtA hm hpre hR)

set_option maxRecDepth 20000 in
theorem agg_loop2_atEvery (hm : m < 2 ^ 34) (hm0 : m ≠ 0) {ich ilf ilc ifv : ℕ} {lamSq lam : E} {ipc : ℕ → ℕ}
    (hpre : ∀ rd, Pre rd → ∀ c < m, ∃ pf fv cv pw acc : E,
      ReadsAt rd (ptrAt ich * (gen ^ c) ^ 2) [pw, acc] ∧
      ReadsAt rd (ptrAt ich * (gen ^ c) ^ 2 * gen ^ 2) [pw * lamSq, acc + pw * (fv + lam * cv)] ∧
      LoadHolds rd (ptrAt ilf * gen ^ c) 0 pf ∧ LoadHolds rd (ptrAt ilc * gen ^ c) 0 (ptrAt (ipc c)) ∧
      LoadHolds rd (ptrAt ifv * gen ^ c) 0 fv ∧ LoadHolds rd (ptrAt (ipc c)) 25 cv)
    (hR : ∀ c < m, ∀ i, A2Reg ich ilf ilc ifv (ipc c) c i → R i) :
    AtEveryB al k name% «aggregate_claims_loop2»
      (gen ^ 0 :: gen ^ m :: [ptrAt ich, ptrAt ilf, ptrAt ilc, lamSq, ptrAt ifv, lam]) [] R Pre FreePost
      (lpBlk B2C.fs name% «aggregate_claims_loop2» m) 0 T β :=
  atEveryB_of_loop (args := fun j => gen ^ j :: gen ^ m :: [ptrAt ich, ptrAt ilf, ptrAt ilc, lamSq, ptrAt ifv, lam])
    hm0 (agg_loop2_callAtA hm hpre hR)

set_option maxRecDepth 20000 in
theorem agg_loop3_atEvery (hm : m < 2 ^ 34) (hm0 : m ≠ 0) {ilf ilc ipt ich iw : ℕ} {eqc lam : E}
    {ipf ipc : ℕ → ℕ}
    (hpre : ∀ rd, Pre rd → ∀ c < m, ∃ pw w0 : E,
      LoadHolds rd (ptrAt ilf * gen ^ c) 0 (ptrAt (ipf c)) ∧ LoadHolds rd (ptrAt ilc * gen ^ c) 0 (ptrAt (ipc c)) ∧
      (∀ j < 19, ∃ v, LoadHolds rd (ptrAt (ipf c)) j v) ∧ (∀ j < 25, ∃ v, LoadHolds rd (ptrAt (ipc c)) j v) ∧
      (∀ j < 25, ∃ v, LoadHolds rd (ptrAt ipt) j v) ∧
      LoadHolds rd (ptrAt ich * (gen ^ c) ^ 2) 0 pw ∧ LoadHolds rd (ptrAt iw * gen ^ c) 0 w0 ∧
      LoadHolds rd (ptrAt iw * gen ^ c) 1 (w0 + pw *
        (eqEval (memRun rd (ptrAt (ipf c)) 19) ((memRun rd (ptrAt ipt) 19).map (1 + ·)) * eqc +
          lam * eqEval (memRun rd (ptrAt (ipc c)) 25) ((memRun rd (ptrAt ipt) 25).map (1 + ·)))))
    (hR : ∀ c < m, ∀ i, A3Reg ilf ilc iw ich (ipf c) (ipc c) ipt c i → R i) :
    AtEveryB al k name% «aggregate_claims_loop3»
      (gen ^ 0 :: gen ^ m :: [ptrAt ilf, ptrAt ilc, ptrAt ipt, ptrAt ich, ptrAt iw, eqc, lam]) [] R Pre FreePost
      (lpBlk B2C.fs name% «aggregate_claims_loop3» m) 0 T β :=
  atEveryB_of_loop (args := fun j => gen ^ j :: gen ^ m :: [ptrAt ilf, ptrAt ilc, ptrAt ipt, ptrAt ich, ptrAt iw, eqc,
    lam]) hm0 (agg_loop3_callAtA hm hpre hR)

theorem agg_bs_atEvery (hwf : coreProgram.Wf) {args rets : List E} (hlen : args.length = 9) {bm bp : ℕ}
    (hm : args.getD 5 0 = ptrAt bm) (hp : args.getD 7 0 = ptrAt bp)
    (hpre : ∀ rd, Pre rd → MeaningBatchSumcheck 25 rd args rets) :
    ∃ B, AtEvery al k "batch_sumcheck__L25" args rets (argRegion args [(5, 50), (7, 25)]) Pre FreePost B 0 :=
  atEvery_of_completesA (agg_bs_callCompletesA hwf k hlen hm hp hpre)

end

end
end LeanVM.Guest.Complete.Agg
