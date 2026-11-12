/-
  LeanVM.Guest.B1.Whir.LqSound

  `level_queries` (a level's cap checked to its root, its `opening_queries` call, `λ^q`), unfolded
  at a frame map.
-/

module

public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.Whir.SqLoop
public import LeanVM.Guest.B1.Main.Frames

/-!
# `level_queries`, unfolded

`lq_unfold`: under a call relation `C` unfolding at the frame map `V`, a call of a
specialization whose body is `lqBody q base folds leaf d cd mu nhs hbits fin` on
`[lam, lam_inv, coefs, hs, positions, win_ptrs]`, its valuation `V name args rets`: the cap and
its flags at cells `7`, `9` checked to the root `[σ 10, σ 11]` (`verify_merkle_cap__L{cd}`), the
`opening_queries` call on `[cap, flags, lam_inv, coefs, hs, positions, win_ptrs, g^iters]`
returning `σ 13`, and the returns `[root_0, root_1, σ 13, lam^q]`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The iterations of `opening_queries` at `q` queries of base `base`: pairs at level `0`. -/
def lqIters (q base : ℕ) : ℕ := if base = 1 then q / 2 else q

theorem lqBody_split (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    lqBody q base folds leaf d cd mu nhs hbits fin =
      (osHeap (4 * 2 ^ cd) 6 ++
        [Stmt.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))] ++
        osHeap (2 ^ cd) 8 ++
        [Stmt.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd)))),
          .call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11],
          osCst 12 (gw (lqIters q base)),
          .call (oqName q base folds leaf d cd mu nhs hbits fin)
            [.n 7, .n 9, .n 1, .n 2, .n 3, .n 4, .n 5, .n 12] [.n 13],
          osCp 14 10, osCp 15 11, osCp 16 13] ++
        (osPowSteps 0 (osPowDigits q) 0 17).1 ++
        [osCp (17 + osPowLen q) (osPowSteps 0 (osPowDigits q) 0 17).2]) ++
      [.ret [.n 14, .n 15, .n 16, .n (17 + osPowLen q)]] := by
  simp [lqBody, lqIters]

theorem lqBodyA_flat (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (osHeap (4 * 2 ^ cd) 6 ++
        [Stmt.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))] ++
        osHeap (2 ^ cd) 8 ++
        [Stmt.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd)))),
          .call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11],
          osCst 12 (gw (lqIters q base)),
          .call (oqName q base folds leaf d cd mu nhs hbits fin)
            [.n 7, .n 9, .n 1, .n 2, .n 3, .n 4, .n 5, .n 12] [.n 13],
          osCp 14 10, osCp 15 11, osCp 16 13] ++
        (osPowSteps 0 (osPowDigits q) 0 17).1 ++
        [osCp (17 + osPowLen q) (osPowSteps 0 (osPowDigits q) 0 17).2]).all Stmt.flat = true := by
  simp [osHeap, Stmt.flat, osPowSteps_flat]

/-- **`level_queries`, unfolded at `V`.** -/
theorem lq_unfold {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V) {name : String}
    {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (hf : FnIs name (osParams 6) (lqBody q base folds leaf d cd mu nhs hbits fin))
    (hit : lqIters q base < u128Bound) (hq : digitsVal (osPowDigits q) 1 = q)
    {args rets : List E} (hc : C name args rets) :
    (∀ i < 6, V name args rets (.n i) = args.getD i 0) ∧
      C ("verify_merkle_cap__L" ++ natStr cd) [V name args rets (.n 7), V name args rets (.n 9)]
        [V name args rets (.n 10), V name args rets (.n 11)] ∧
      C (oqName q base folds leaf d cd mu nhs hbits fin)
        [V name args rets (.n 7), V name args rets (.n 9), args.getD 1 0, args.getD 2 0,
          args.getD 3 0, args.getD 4 0, args.getD 5 0, gen ^ lqIters q base]
        [V name args rets (.n 13)] ∧
      rets = [V name args rets (.n 10), V name args rets (.n 11), V name args rets (.n 13),
        args.getD 0 0 ^ q] := by
  obtain ⟨fn, hfind, hps, hb⟩ := hf
  obtain ⟨fn', hf', hp, hh⟩ := hU name args rets hc
  rw [hfind] at hf'
  cases hf'
  set σ := V name args rets
  rw [hps] at hp
  have ha : ∀ i < 6, σ (.n i) = args.getD i 0 := by
    intro i hi
    rw [← hp]
    simp [osParams, List.getD_eq_getElem?_getD, hi]
  rw [hb, lqBody_split, holdsList_flat_ret _ (lqBodyA_flat _ _ _ _ _ _ _ _ _ _)] at hh
  obtain ⟨hok, hret⟩ := hh
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hmid⟩, hpw⟩, hcp⟩ := hok
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, stmtOk_atom, holds_const, holds_copy,
    osCst, osCp, List.map_cons, List.map_nil] at hmid hcp
  obtain ⟨-, hvm, c12, hoq, c14, c15, c16⟩ := hmid
  have hpow := osPowSteps_val (rd := rd) 0 (osPowDigits q) 0 17 1 (by rw [pow_one]) hpw
  rw [hq] at hpow
  refine ⟨ha, hvm, ?_, ?_⟩
  · rw [c12, gw_eq hit, ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
      ha 5 (by decide)] at hoq
    exact hoq
  · rw [← hret]
    simp only [List.map_cons, List.map_nil]
    rw [c14, c15, c16, hcp, hpow, ha 0 (by decide)]

end
end LeanVM.Guest.B1.Whir
