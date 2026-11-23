/-
  LeanVM.Guest.B1.Whir.LqSound

  `level_queries` (a level's cap checked to its root, its `opening_queries` call, `λ^q`), unfolded
  at a frame map.
-/

module

public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.B1.Whir.SqLoop
public import LeanVM.Guest.B1.Main.FramesP

/-!
# `level_queries`, unfolded

`lq_unfold`: under a call relation `C` unfolding at the frame map `V`, a call of a
specialization whose body is `lqBody q base folds leaf d cd mu nhs hbits fin` on
`[lam, lam_inv, coefs, hs, positions, win_ptrs]`, its valuation `V name args rets`: the cap and
its flags at cells `7`, `9` checked to the root `[σ 10, σ 11]` (`verify_merkle_cap__L{cd}`), the
`opening_queries` call on `[cap·g^(2^(cd+1)), flags·g^(2^(cd-1)), lam_inv, coefs, hs, positions,
win_ptrs, g^iters, g^odd]` (cells `13`, `15` the offset cap and flags) returning `σ 18`, and the
returns `[root_0, root_1, σ 18, lam^q]`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {P : Program} {rd : Reader}

/-- The iterations of `opening_queries` at `q` queries of base `base`: pairs at level `0`. -/
def lqIters (q base : ℕ) : ℕ := if base = 1 then q / 2 else q

/-- The odd first query of `opening_queries` at `q` queries of base `base`: at level `0` only. -/
def lqOdd (q base : ℕ) : ℕ := if base = 1 then q % 2 else 0

/-- `level_queries`' body but its return. -/
def lqBodyA (q base folds leaf d cd mu nhs hbits fin : ℕ) : List Stmt :=
  osHeap (4 * 2 ^ cd) 6 ++
    [.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))] ++
    osHeap (2 ^ cd) 8 ++
    [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd)))),
      .call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11],
      osCst 12 (gw (2 ^ (cd + 1))), osMul 13 7 12, osCst 14 (gw (2 ^ (cd - 1))), osMul 15 9 14,
      osCst 16 (gw (lqIters q base)), osCst 17 (gw (lqOdd q base)),
      .call (oqName base folds leaf (d - cd) mu nhs hbits fin)
        [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17] [.n 18],
      osCp 19 10, osCp 20 11, osCp 21 18] ++
    (osPowSteps 0 (osPowDigits q) 0 22).1 ++ [osCp (22 + osPowLen q) (osPowSteps 0 (osPowDigits q) 0 22).2]

theorem lqBody_split (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    lqBody q base folds leaf d cd mu nhs hbits fin =
      lqBodyA q base folds leaf d cd mu nhs hbits fin ++ [.ret [.n 19, .n 20, .n 21, .n (22 + osPowLen q)]] := by
  simp [lqBody, lqBodyA, lqIters, lqOdd]

theorem lqBodyA_flat (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqBodyA q base folds leaf d cd mu nhs hbits fin).all Stmt.flat = true := by
  simp [lqBodyA, osHeap, Stmt.flat, osPowSteps_flat]

/-- **`level_queries`, unfolded at `V`.** -/
theorem lq_unfold {C : CallRel} {V : FrameMap} (hU : UnfoldsVP P rd C V) {name : String}
    {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (hf : FnIsP P name (osParams 6) (lqBody q base folds leaf d cd mu nhs hbits fin))
    (hit : lqIters q base < u128Bound) (hodd : lqOdd q base < u128Bound)
    (hc1 : 2 ^ (cd + 1) < u128Bound) (hc2 : 2 ^ (cd - 1) < u128Bound)
    (hq : digitsVal (osPowDigits q) 1 = q)
    {args rets : List E} (hc : C name args rets) :
    (∀ i < 6, V name args rets (.n i) = args.getD i 0) ∧
      C ("verify_merkle_cap__L" ++ natStr cd) [V name args rets (.n 7), V name args rets (.n 9)]
        [V name args rets (.n 10), V name args rets (.n 11)] ∧
      V name args rets (.n 13) = V name args rets (.n 7) * gen ^ 2 ^ (cd + 1) ∧
      V name args rets (.n 15) = V name args rets (.n 9) * gen ^ 2 ^ (cd - 1) ∧
      C (oqName base folds leaf (d - cd) mu nhs hbits fin)
        [V name args rets (.n 13), V name args rets (.n 15), args.getD 1 0, args.getD 2 0,
          args.getD 3 0, args.getD 4 0, args.getD 5 0, gen ^ lqIters q base, gen ^ lqOdd q base]
        [V name args rets (.n 18)] ∧
      rets = [V name args rets (.n 10), V name args rets (.n 11), V name args rets (.n 18),
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
  simp only [lqBodyA, allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hmid⟩, hpw⟩, hcp⟩ := hok
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, stmtOk_atom, holds_const, holds_copy,
    holds_mul, osCst, osCp, osMul, List.map_cons, List.map_nil] at hmid hcp
  obtain ⟨-, hvm, c12, m13, c14, m15, c16, c17, hoq, c19, c20, c21⟩ := hmid
  have hpow := osPowSteps_val (rd := rd) 0 (osPowDigits q) 0 22 1 (by rw [pow_one]) hpw
  rw [hq] at hpow
  refine ⟨ha, hvm, by rw [m13, c12, gw_eq hc1], by rw [m15, c14, gw_eq hc2], ?_, ?_⟩
  · rw [c16, c17, gw_eq hit, gw_eq hodd, ha 1 (by decide), ha 2 (by decide), ha 3 (by decide),
      ha 4 (by decide), ha 5 (by decide)] at hoq
    exact hoq
  · rw [← hret]
    simp only [List.map_cons, List.map_nil]
    rw [c19, c20, c21, hcp, hpow, ha 0 (by decide)]

end
end LeanVM.Guest.B1.Whir
