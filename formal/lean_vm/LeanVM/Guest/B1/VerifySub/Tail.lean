/-
  LeanVM.Guest.B1.VerifySub.Tail

  `verify_sub`'s three calls (`verify_bus_gkr`, `verify_tables`, `verify_keccak`) and its tail:
  the dispatch to `open_stacked`, the terminal, the deferred claim.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.Proof
public import LeanVM.Guest.B1.Tables.Basic
public import LeanVM.Guest.B1.Whir.Names

/-!
# The calls and the tail of `verify_sub`

* `vsCallsT_holds` (G:3665-3676): the three calls on their argument words, `tabs` three times,
  the Keccak table's `g^τ` read off `dims_g`, the output lanes at `col_eval_words·g^101`.
* `vsTailT_holds` (G:3732-3747): the candidate `size_sel·rate_sel^7 = g^candidate`, the call of
  its `open_stacked` specialization (the dispatch), the cursor past the ring grind's nonce,
  `check_opening_terminal`'s call, the deferred claim's words, and the return.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

set_option maxRecDepth 100000 in
/-- `KECCAK_OUT_POOL - N_BUS_CLAIMS = 101`: the output lanes' offset in `col_eval_words`. -/
theorem word_g101 : word 3710851743744 0 = gen ^ 101 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

/-- **The three calls** (G:3665-3676). -/
theorem vsCallsT_holds (h : Stmt.HoldsList C rd σ vsCallsT next kret) :
    σ (.n 561) = σ (.n 4) * gen ^ winTabAt ∧
    C "verify_bus_gkr" [σ (.n 554), σ (.n 555), σ (.n 556), σ (.n 557), σ (.n 558), σ (.n 320),
      σ (.n 253), σ (.n 254), σ (.n 561)]
      [σ (.n 562), σ (.n 563), σ (.n 564), σ (.n 565), σ (.n 566), σ (.n 567), σ (.n 568)] ∧
    σ (.n 572) = σ (.n 4) * gen ^ winTabAt ∧
    C "verify_tables" [σ (.n 562), σ (.n 563), σ (.n 564), σ (.n 565), σ (.n 566), σ (.n 567),
      σ (.n 0), σ (.n 1), σ (.n 254), σ (.n 253), σ (.n 71), σ (.n 26), σ (.n 4), σ (.n 335),
      σ (.n 559), σ (.n 6), σ (.n 569), σ (.n 568), σ (.n 572), σ (.n 570)]
      [σ (.n 573), σ (.n 574), σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579),
        σ (.n 580), σ (.n 581), σ (.n 582)] ∧
    LoadHolds rd (σ (.n 71)) 6 (σ (.n 583)) ∧ σ (.n 587) = σ (.n 582) * gen ^ 101 ∧
    σ (.n 589) = σ (.n 4) * gen ^ winTabAt ∧
    C "verify_keccak" [σ (.n 573), σ (.n 574), σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578),
      σ (.n 583), σ (.n 569), σ (.n 587), σ (.n 584), σ (.n 585), σ (.n 589)]
      [σ (.n 590), σ (.n 591), σ (.n 592), σ (.n 593), σ (.n 594), σ (.n 595), σ (.n 596)] ∧
    next := by
  simp only [vsCallsT, vsTabsT, holdsList_append, Stmt.HoldsList, Stmt.Holds, vsCall, vsAlloc,
    vsLd, vsConst, vsMul, Atom.Holds, List.map_cons, List.map_nil,
    show List.range 7 = [0, 1, 2, 3, 4, 5, 6] from rfl,
    show List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl] at h
  obtain ⟨c560, m561, cG, -, -, c571, m572, cT, l583, -, -, e586, m587, c588, m589, cK, hn⟩ := h
  refine ⟨by rw [m561, c560, vsWinWord_eq], cG, by rw [m572, c571, vsWinWord_eq], cT, l583,
    by rw [m587, e586, word_g101], by rw [m589, c588, vsWinWord_eq], cK, hn⟩

/-- `vsOpenNames` is `open_stacked`'s specializations in dispatch order. -/
theorem vsOpenNames_natStr :
    vsOpenNames = (List.range 28).map fun m ↦ "open_stacked__L" ++ Whir.natStr m := by
  decide +kernel

theorem vsOpenNames_eq : vsOpenNames = Whir.openNames := by
  rw [vsOpenNames_natStr, Whir.openNames]
  simp only [Whir.natStr_eq]

/-- **The tail** (G:3732-3747): the candidate, the call of its `open_stacked`, the terminal, the
deferred claim's words, the return. -/
theorem vsTailT_holds {m lir : ℕ} (hm22 : 22 ≤ m) (hm28 : m ≤ 28) (hl1 : 1 ≤ lir)
    (hl4 : lir ≤ 4) (h278 : σ (.n 278) = gen ^ (m - 22)) (h66 : σ (.n 66) = gen ^ (lir - 1))
    {rets : List E} (h : Stmt.HoldsList C rd σ vsTailT False (fun rs ↦ rs = rets)) :
    rets = [] ∧ σ (.n 1922) = gen ^ Whir.candidate m lir ∧ σ (.n 1928) = σ (.n 595) * gen ∧
    σ (.n 1930) = σ (.n 4) * gen ^ winTabAt ∧ C (Whir.openName m lir) (vsOsArgs σ) (vsOsRets σ) ∧
    C "check_opening_terminal" [σ (.n 4), σ (.n 254), σ (.n 569), σ (.n 581), σ (.n 253),
      σ (.n 579), σ (.n 72), σ (.n 583), σ (.n 83), σ (.n 1375), σ (.n 275), σ (.n 584),
      σ (.n 848), σ (.n 1932), σ (.n 1933), σ (.n 1934), σ (.n 1935), σ (.n 1931), σ (.n 304),
      σ (.n 276)] [] ∧
    (∀ k < 19, ∃ w, LoadHolds rd (σ (.n 254)) k w ∧ LoadHolds rd (σ (.n 5)) k w) ∧
    (∀ k < 4, ∃ w, LoadHolds rd (σ (.n 570)) k w ∧ LoadHolds rd (σ (.n 5)) (19 + k) w) ∧
    LoadHolds rd (σ (.n 5)) 23 (σ (.n 580)) := by
  rw [vsTailT, List.flatMap_def, List.flatMap_def] at h
  simp only [holdsList_append] at h
  rw [Tables.tb_holdsList_range_flatten 19 _ (fun _ ↦ rfl), Tables.tb_holdsList_range_flatten 4 _ (fun _ ↦ rfl)]
    at h
  simp only [vsTabsT, Stmt.HoldsList, Stmt.Holds, vsMul, vsConst, vsRange, vsLd, Atom.Holds,
    List.map_nil] at h
  obtain ⟨m1918, m1919, m1920, m1921, m1922, -, -, e1927, m1928, c1929, m1930,
    ⟨j, hj, hj1922, hc⟩, cT, hz, hb, l580, hr⟩ := h
  have h1930 : σ (.n 1930) = σ (.n 4) * gen ^ winTabAt := by rw [m1930, c1929, vsWinWord_eq]
  -- the candidate
  have h1922 : σ (.n 1922) = gen ^ Whir.candidate m lir := by
    have e : σ (.n 1922) = gen ^ (m - 22) * (gen ^ (lir - 1)) ^ 7 := by
      rw [m1922, m1921, m1920, m1919, m1918, h278, h66]; ring
    rw [e, ← pow_mul, ← pow_add, Whir.candidate, mul_comm (lir - 1) 7]
  have hcand : Whir.candidate m lir < 28 := by unfold Whir.candidate; omega
  have hlen : vsOpenNames.length = 28 := by rw [vsOpenNames_eq]; simp [Whir.openNames]
  have hjc : j = Whir.candidate m lir := by
    rw [h1922] at hj1922
    exact (gen_pow_inj (by omega) (by omega)
      (by rw [hj1922, gen_pow_eq_ofK])).symm
  subst hjc
  have hname : vsOpenNames[Whir.candidate m lir] = Whir.openName m lir := by
    rw [Whir.openName, List.getD_eq_getElem _ _ (by rw [← vsOpenNames_eq]; omega)]
    simp only [vsOpenNames_eq]
  rw [hname] at hc
  refine ⟨hr.symm, h1922, by rw [m1928, e1927, word_gen], h1930, hc, cT, fun k hk ↦ ?_,
    fun k hk ↦ ?_, l580⟩
  · have := hz k hk
    simp only [and_true] at this
    exact ⟨_, this⟩
  · have := hb k hk
    simp only [and_true] at this
    exact ⟨_, this⟩

end
end LeanVM.Guest.B1.VerifySub
