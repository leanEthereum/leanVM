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
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The calls and the tail of `verify_sub`

* `vsCallsT_holds`: the three calls on their argument words, `tabs` three times,
  the Keccak table's `g^τ` read off `dims_g`, the output lanes at `col_eval_words·g^101`.
* `vsTailT_holds`: the call of the stack size's `open_stacked` specialization (the
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

/-- **The three calls**. -/
theorem vsCallsT_holds (h : Stmt.HoldsList C rd σ vsCallsT next kret) :
    σ (.n (val% «verify_sub» "fs0@3~8")) = σ (.n (val% «verify_sub» "g_squares")) * gen ^ winTabAt ∧
    C "verify_bus_gkr" [σ (.n (val% «verify_sub» "nxt[8]@19")), σ (.n (val% «verify_sub» "nxt[9]@19")), σ (.n (val% «verify_sub» "nxt[10]@19")), σ (.n (val% «verify_sub» "nxt[11]@19")), σ (.n (val% «verify_sub» "nxt[12]@19")), σ (.n (val% «verify_sub» "cursor@1")),
      σ (.n (val% «verify_sub» "g_bus_mu")), σ (.n (val% «verify_sub» "zeta")), σ (.n (val% «verify_sub» "fs0@3~8")), σ (.n (val% «verify_sub» "stream"))]
      [σ (.n (val% «verify_sub» "fs0@3")), σ (.n (val% «verify_sub» "fs1@3")), σ (.n (val% «verify_sub» "fs2@3")), σ (.n (val% «verify_sub» "fs3@3")), σ (.n (val% «verify_sub» "fs4@3")), σ (.n (val% «verify_sub» "cursor@2")), σ (.n (val% «verify_sub» "gkr_leaves"))] ∧
    σ (.n (val% «verify_sub» "fs0@4~11")) = σ (.n (val% «verify_sub» "g_squares")) * gen ^ winTabAt ∧
    C "verify_tables" [σ (.n (val% «verify_sub» "fs0@3")), σ (.n (val% «verify_sub» "fs1@3")), σ (.n (val% «verify_sub» "fs2@3")), σ (.n (val% «verify_sub» "fs3@3")), σ (.n (val% «verify_sub» "fs4@3")), σ (.n (val% «verify_sub» "cursor@2")),
      σ (.n (val% «verify_sub» "pi_0")), σ (.n (val% «verify_sub» "pi_1")), σ (.n (val% «verify_sub» "zeta")), σ (.n (val% «verify_sub» "g_bus_mu")), σ (.n (val% «verify_sub» "dims_g")), σ (.n (val% «verify_sub» "table_rows")), σ (.n (val% «verify_sub» "g_squares")), σ (.n (val% «verify_sub» "fp_w")),
      σ (.n (val% «verify_sub» "nxt[0]@19")), σ (.n (val% «verify_sub» "claim_pool")), σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "gkr_leaves")), σ (.n (val% «verify_sub» "fs0@4~11")), σ (.n (val% «verify_sub» "bc_point")), σ (.n (val% «verify_sub» "stream"))]
      [σ (.n (val% «verify_sub» "fs0@4")), σ (.n (val% «verify_sub» "fs1@4")), σ (.n (val% «verify_sub» "fs2@4")), σ (.n (val% «verify_sub» "fs3@4")), σ (.n (val% «verify_sub» "fs4@4")), σ (.n (val% «verify_sub» "cursor@3")), σ (.n (val% «verify_sub» "g_zc_n")),
        σ (.n (val% «verify_sub» "bc_value")), σ (.n (val% «verify_sub» "rm")), σ (.n (val% «verify_sub» "col_eval_words"))] ∧
    LoadHolds rd (σ (.n (val% «verify_sub» "dims_g"))) 6 (σ (.n (val% «verify_sub» "tau_keccak_g"))) ∧ σ (.n (val% «verify_sub» "fs0@5~8")) = σ (.n (val% «verify_sub» "col_eval_words")) * gen ^ 101 ∧
    σ (.n (val% «verify_sub» "fs0@5~10")) = σ (.n (val% «verify_sub» "g_squares")) * gen ^ winTabAt ∧
    C "verify_keccak" [σ (.n (val% «verify_sub» "fs0@4")), σ (.n (val% «verify_sub» "fs1@4")), σ (.n (val% «verify_sub» "fs2@4")), σ (.n (val% «verify_sub» "fs3@4")), σ (.n (val% «verify_sub» "fs4@4")), σ (.n (val% «verify_sub» "cursor@3")),
      σ (.n (val% «verify_sub» "tau_keccak_g")), σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "fs0@5~8")), σ (.n (val% «verify_sub» "z_vals")), σ (.n (val% «verify_sub» "slices")), σ (.n (val% «verify_sub» "fs0@5~10")), σ (.n (val% «verify_sub» "stream"))]
      [σ (.n (val% «verify_sub» "fs0@5")), σ (.n (val% «verify_sub» "fs1@5")), σ (.n (val% «verify_sub» "fs2@5")), σ (.n (val% «verify_sub» "fs3@5")), σ (.n (val% «verify_sub» "fs4@5")), σ (.n (val% «verify_sub» "cursor@4")), σ (.n (val% «verify_sub» "keccak_word"))] ∧
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

/-- **The tail**: the call of the stack size's `open_stacked` on the rate's selector
(the dispatch on `size_sel = g^(m - 20)`), the terminal, the deferred claim's words, the return. -/
theorem vsTailT_holds {m : ℕ} (hm20 : Whir.minOpenLog ≤ m) (hm30 : m ≤ 30)
    (h278 : σ (.n (val% «verify_sub» "size_sel")) = gen ^ (m - Whir.minOpenLog))
    {rets : List E} (h : Stmt.HoldsList C rd σ vsTailT False (fun rs ↦ rs = rets)) :
    rets = [] ∧ σ (.n (val% «verify_sub» "sumcheck_target~2")) = σ (.n (val% «verify_sub» "cursor@4")) * gen ∧
    σ (.n (val% «verify_sub» "sumcheck_target~4")) = σ (.n (val% «verify_sub» "g_squares")) * gen ^ winTabAt ∧ C (Whir.openName m) (vsOsArgs σ) (vsOsRets σ) ∧
    C "check_opening_terminal" [σ (.n (val% «verify_sub» "g_squares")), σ (.n (val% «verify_sub» "zeta")), σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "rm")), σ (.n (val% «verify_sub» "g_bus_mu")),
      σ (.n (val% «verify_sub» "g_zc_n")), σ (.n (val% «verify_sub» "g_log_mem")), σ (.n (val% «verify_sub» "tau_keccak_g")), σ (.n (val% «verify_sub» "kappa_base")), σ (.n (val% «verify_sub» "nxt[0]@36")), σ (.n (val% «verify_sub» "col_offsets")), σ (.n (val% «verify_sub» "z_vals")),
      σ (.n (val% «verify_sub» "c_table")), σ (.n (val% «verify_sub» "point")), σ (.n (val% «verify_sub» "point1")), σ (.n (val% «verify_sub» "inner_total")), σ (.n (val% «verify_sub» "yr_at_tail")), σ (.n (val% «verify_sub» "sumcheck_target")), σ (.n (val% «verify_sub» "ood_z")),
      σ (.n (val% «verify_sub» "gmv"))] [] ∧
    (∀ k < 19, ∃ w, LoadHolds rd (σ (.n (val% «verify_sub» "zeta"))) k w ∧ LoadHolds rd (σ (.n (val% «verify_sub» "defer_out"))) k w) ∧
    (∀ k < 4, ∃ w, LoadHolds rd (σ (.n (val% «verify_sub» "bc_point"))) k w ∧ LoadHolds rd (σ (.n (val% «verify_sub» "defer_out"))) (19 + k) w) ∧
    LoadHolds rd (σ (.n (val% «verify_sub» "defer_out"))) 23 (σ (.n (val% «verify_sub» "bc_value"))) := by
  rw [vsTailT, List.flatMap_def, List.flatMap_def] at h
  simp only [holdsList_append] at h
  rw [Tables.tb_holdsList_range_flatten 19 _ (fun _ ↦ rfl), Tables.tb_holdsList_range_flatten 4 _ (fun _ ↦ rfl)]
    at h
  simp only [vsTabsT, Stmt.HoldsList, Stmt.Holds, vsMul, vsConst, vsLd, Atom.Holds, List.map_nil] at h
  obtain ⟨e1918, m1919, c1920, m1921, ⟨j, hj, hj278, hc⟩, cT, hz, hb, l580, hr⟩ := h
  have h1921 : σ (.n (val% «verify_sub» "sumcheck_target~4")) = σ (.n (val% «verify_sub» "g_squares")) * gen ^ winTabAt := by rw [m1921, c1920, vsWinWord_eq]
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
