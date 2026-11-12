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

* `vsCallsT_holds` (G:3624-3635): the three calls on their argument words, `tabs` three times,
  the Keccak table's `g^τ` read off `dims_g`, the output lanes at `col_eval_words·g^101`.
* `vsTailT_holds` (G:3691-3706): the call of the stack size's `open_stacked` specialization (the
  dispatch on `size_sel`, the rate's selector its first argument), the cursor past the ring grind's nonce,
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

/-- **The three calls** (G:3624-3635). -/
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
    vsOpenNames = (List.range Whir.openArms).map fun m ↦ "open_stacked__L" ++ Whir.natStr m := by
  decide +kernel

theorem vsOpenNames_eq : vsOpenNames = Whir.openNames := by
  rw [vsOpenNames_natStr, Whir.openNames]
  simp only [Whir.natStr_eq]

/-- **The tail** (G:3691-3706): the call of the stack size's `open_stacked` on the rate's selector
(the dispatch on `size_sel = g^(m - 20)`), the terminal, the deferred claim's words, the return. -/
theorem vsTailT_holds {m : ℕ} (hm20 : Whir.minOpenLog ≤ m) (hm30 : m ≤ 30)
    (h278 : σ (.n 278) = gen ^ (m - Whir.minOpenLog))
    {rets : List E} (h : Stmt.HoldsList C rd σ vsTailT False (fun rs ↦ rs = rets)) :
    rets = [] ∧ σ (.n 1919) = σ (.n 595) * gen ∧
    σ (.n 1921) = σ (.n 4) * gen ^ winTabAt ∧ C (Whir.openName m) (vsOsArgs σ) (vsOsRets σ) ∧
    C "check_opening_terminal" [σ (.n 4), σ (.n 254), σ (.n 569), σ (.n 581), σ (.n 253),
      σ (.n 579), σ (.n 72), σ (.n 583), σ (.n 83), σ (.n 1375), σ (.n 275), σ (.n 584),
      σ (.n 848), σ (.n 1923), σ (.n 1924), σ (.n 1925), σ (.n 1926), σ (.n 1922), σ (.n 304),
      σ (.n 276)] [] ∧
    (∀ k < 19, ∃ w, LoadHolds rd (σ (.n 254)) k w ∧ LoadHolds rd (σ (.n 5)) k w) ∧
    (∀ k < 4, ∃ w, LoadHolds rd (σ (.n 570)) k w ∧ LoadHolds rd (σ (.n 5)) (19 + k) w) ∧
    LoadHolds rd (σ (.n 5)) 23 (σ (.n 580)) := by
  rw [vsTailT, List.flatMap_def, List.flatMap_def] at h
  simp only [holdsList_append] at h
  rw [Tables.tb_holdsList_range_flatten 19 _ (fun _ ↦ rfl), Tables.tb_holdsList_range_flatten 4 _ (fun _ ↦ rfl)]
    at h
  simp only [vsTabsT, Stmt.HoldsList, Stmt.Holds, vsMul, vsConst, vsLd, Atom.Holds, List.map_nil] at h
  obtain ⟨e1918, m1919, c1920, m1921, ⟨j, hj, hj278, hc⟩, cT, hz, hb, l580, hr⟩ := h
  have h1921 : σ (.n 1921) = σ (.n 4) * gen ^ winTabAt := by rw [m1921, c1920, vsWinWord_eq]
  -- the size's arm
  have hlen : vsOpenNames.length = Whir.openArms := by rw [vsOpenNames_eq]; simp [Whir.openNames]
  have hA : Whir.openArms = 11 := rfl
  have hM : Whir.minOpenLog = 20 := rfl
  have harm : m - Whir.minOpenLog < Whir.openArms := by omega
  have hjc : j = m - Whir.minOpenLog := by
    rw [h278] at hj278
    exact (gen_pow_inj (by omega) (by omega) (by rw [hj278, gen_pow_eq_ofK])).symm
  subst hjc
  have hname : vsOpenNames[m - Whir.minOpenLog] = Whir.openName m := by
    rw [Whir.openName, List.getD_eq_getElem _ _ (by rw [← vsOpenNames_eq]; omega)]
    simp only [vsOpenNames_eq]
  rw [hname] at hc
  refine ⟨hr.symm, by rw [m1919, e1918, word_gen], h1921, hc, cT, fun k hk ↦ ?_,
    fun k hk ↦ ?_, l580⟩
  · have := hz k hk
    simp only [and_true] at this
    exact ⟨_, this⟩
  · have := hb k hk
    simp only [and_true] at this
    exact ⟨_, this⟩

end
end LeanVM.Guest.B1.VerifySub
