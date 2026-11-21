/-
  LeanVM.Guest.B1.Tables.VtC.ABound

  **`verify_tables` is complete, placed, within an explicit bound** (`CompleteAtDTB`): its frame,
  its buffers, its callees' bounds and its skipped frames.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AComplete
public import LeanVM.Guest.B1.Tables.VtC.Calls
public import LeanVM.Guest.B1.Tables.FlatLiftT
public import LeanVM.Core.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_tables`, placed, within its bound

The callees' words come as hypotheses in G7's forms: every statically bounded callee `g` of
`vtKidS` (`selector_run_nibbles` among them) within a constant `Kf g` (`TotalLe`),
`shared_selector_tables` within `Ksh` on a run length `g^n`, `n < 64`, and its split `g^(n/4)`
(`TotalLeOn`; the honest valuation passes each table's, `vt_shCalls`), `verify_tables_loop0`'s
run within `K10` words an iteration and its one phantom frame (`TotalLeOn … LoopPre`). Call by
call (`vtCallBnd`): a call's callee's constant (`Ksh` for the shared tables), a dispatch's largest
arm's, the rounds loop's run `vtRunB` at the honest round count `n`.
`verify_tables_completeAtTB`: within `fs "verify_tables" + Σ sizes + Σ vtBs + ifFrames`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Core.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- A call's frame under `σ`, by its statement among the body's calls. -/
theorem flatCalls_getElem {σ : Val} : ∀ (pre : List Stmt) (i : ℕ) (c : Call),
    (flatCalls pre σ)[i]? = some c → ∃ s, (pre.filter callB)[i]? = some s ∧
      ∃ tup, Stmt.callSF σ s = some tup ∧ c = mkCall σ tup
  | [], _, _, h => by simp [flatCalls] at h
  | s :: ss, i, c, h => by
    cases hs : callB s
    · have hn : Stmt.callSF σ s = none := by
        cases s <;> simp_all [callB, Stmt.callSF, Main.Stmt.callS]
      have h' : (flatCalls ss σ)[i]? = some c := by
        simpa [flatCalls, List.filterMap_cons, hn] using h
      obtain ⟨s', h1, h2⟩ := flatCalls_getElem ss i c h'
      exact ⟨s', by simpa [List.filter_cons, hs] using h1, h2⟩
    · obtain ⟨tup, ht⟩ : ∃ tup, Stmt.callSF σ s = some tup := by
        cases s <;> simp_all [callB, Stmt.callSF, Main.Stmt.callS]
      rcases i with _ | i
      · simp only [flatCalls, List.filterMap_cons, ht, List.map_cons, List.getElem?_cons_zero,
          Option.some.injEq] at h
        exact ⟨s, by simp [hs], tup, ht, h.symm⟩
      · have h' : (flatCalls ss σ)[i]? = some c := by
          simpa [flatCalls, List.filterMap_cons, ht] using h
        obtain ⟨s', h1, h2⟩ := flatCalls_getElem ss i c h'
        exact ⟨s', by simpa [List.filter_cons, hs] using h1, h2⟩

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem getElem?_filter_mem {l : List Stmt} {p : Stmt → Bool} {i : ℕ} {s : Stmt}
    (h : (l.filter p)[i]? = some s) : s ∈ l ∧ p s = true := by
  have hm := List.mem_of_getElem? h
  exact ⟨List.mem_of_mem_filter hm, (List.mem_filter.mp hm).2⟩

/-- A `shared_selector_tables` call. -/
def isShCallB : Stmt → Bool
  | .call f _ _ => f == "shared_selector_tables"
  | _ => false

set_option maxRecDepth 100000 in
/-- **The shared tables' calls, by the kernel**: one per table, `shCall t`. -/
theorem vt_shCalls : tbStmtsEqb (vtPre.filter isShCallB) ((List.range 6).map shCall) = true := by
  decide +kernel

/-- **The honest values the calls' bounds read**: `g^n` and the rounds loop's condition and
counter, each table's run length and split. -/
theorem vt_honest_vals {κ : ℕ} (hκ : 14 ≤ κ) {H : VtHonest} (h : H.Ok) (hs : VtShape H)
    (B : VtBases) (o : ℕ) {rd : Reader} (hlow : LowDef κ rd)
    (hm : MemLay rd (H.linL (B.at o) ++ H.ownL (B.at o))) :
    vtσ rd (vtW H (B.at o)) (H.args B) (.n 2245) = gen ^ H.n ∧
      vtσ rd (vtW H (B.at o)) (H.args B) (.n 2335) = 1 + gen ^ H.n ∧
      vtσ rd (vtW H (B.at o)) (H.args B) (.n 2336) = 1 ∧
      ∀ u < 6, vtσ rd (vtW H (B.at o)) (H.args B) (.n (vtShLen u)) = gen ^ (H.μ - H.τ u) ∧
        vtσ rd (vtW H (B.at o)) (H.args B) (.n (vtShQ u)) = gen ^ ((H.μ - H.τ u) / 4) := by
  have hl : (H.args B).length = 20 := rfl
  have hlow14 : LowDefB 14 rd := hlow.mono hκ
  have hks := (vt_rel_completeF h hs (B.at o) (vtW_ok H (B.at o)) hlow14 hm).2
  have hsl : ∀ u < 6, vtσ rd (vtW H (B.at o)) (H.args B) (.n (vtShLen u)) =
      gen ^ (H.μ - H.τ u) := hks.2
  have hq : ∀ u < 6, vtσ rd (vtW H (B.at o)) (H.args B) (.n (vtShQ u)) =
      gen ^ ((H.μ - H.τ u) / 4) := fun u hu ↦ by
    rw [vtc_ret1 (rd := rd) (w := vtW H (B.at o)) hl (699 + 20 * u) _ _ _ (vt_srn_at u hu)]
    exact (vtW_ok H (B.at o)).hq u hu
  have g1 := vt_goodL (rd := rd) (w := vtW H (B.at o)) hl 2292
    [.atom (.hint (.witness "zc_tau_max" (.stack [.n 2245])))] (by decide +kernel)
  have g2 := vt_goodL (rd := rd) (w := vtW H (B.at o)) hl 2364
    [.atom (.const (.n 2334) (word 1 0)), .atom (.add (.n 2335) (.n 2334) (.n 2245)),
      .atom (.const (.n 2336) (word 1 0))] (by decide +kernel)
  generalize vtσ rd (vtW H (B.at o)) (H.args B) = σ at g1 g2 hsl hq ⊢
  simp only [GoodL, GoodS, fixNe, Good, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, and_true] at g1 g2
  obtain ⟨c19, a20, c21⟩ := g2
  have w17 : σ (.n 2245) = gen ^ H.n := by
    rw [g1]; exact (vtW_ok H (B.at o)).w2544
  exact ⟨w17, by rw [a20, c19, w17, tb_word_one], by rw [c21, tb_word_one],
    fun u hu ↦ ⟨hsl u hu, hq u hu⟩⟩

/-- **A shared tables' call's run length and split**, on the honest values: `g^n`, `g^(n/4)`. -/
theorem vt_sh_pre {H : VtHonest} (hμ33 : H.μ < 33) {σ : Val}
    (vsh : ∀ u < 6, σ (.n (vtShLen u)) = gen ^ (H.μ - H.τ u) ∧
      σ (.n (vtShQ u)) = gen ^ ((H.μ - H.τ u) / 4))
    {a : List V} (hsm : Stmt.call "shared_selector_tables" a [] ∈ vtPre) :
    ∃ n < 64, (a.map σ).getD 5 0 = gen ^ n ∧ (a.map σ).getD 6 0 = gen ^ (n / 4) := by
  have hsc : Stmt.call "shared_selector_tables" a [] ∈ (List.range 6).map shCall := by
    rw [← tbStmtsEqb_sound vt_shCalls]
    exact List.mem_filter.mpr ⟨hsm, by simp [isShCallB]⟩
  obtain ⟨u, hu, he⟩ := List.mem_map.mp hsc
  simp only [shCall, Stmt.call.injEq, true_and, and_true] at he
  subst he
  obtain ⟨e5, e6⟩ := vsh u (List.mem_range.mp hu)
  exact ⟨H.μ - H.τ u, by omega, by simp [e5], by simp [e6]⟩

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxRecDepth 20000 in
/-- **`verify_tables` is complete, placed, within its bound**: from the specification's accepting
run (`H.Ok`) and the deployed shapes (`VtShape`), on the caller's honest buffers `H.linL B`, for
memories defined below `2^κ`, `κ ≥ 14`, its tree of at most `fs "verify_tables"` words, its
buffers, its callees' bounds and its skipped frames. -/
theorem verify_tables_completeAtTB {κ : ℕ} (hκ : 14 ≤ κ) {H : VtHonest} (h : H.Ok)
    (hs : VtShape H) (B : VtBases) (Kf : String → ℕ) (Ksh K10 : ℕ)
    (hKf : ∀ g ∈ vtKidS, g ≠ name% «verify_tables_loop0» → g ≠ name% «shared_selector_tables_loop0»
        → g ≠ "shared_selector_tables" →
      TotalLe coreProgram fs g (fun _ ↦ Kf g))
    (hsh : TotalLeOn coreProgram fs "shared_selector_tables"
      (fun a ↦ ∃ n < 64, a.getD 5 0 = gen ^ n ∧ a.getD 6 0 = gen ^ (n / 4)) (fun _ ↦ Ksh))
    (h10 : TotalLeOn coreProgram fs name% «verify_tables_loop0» LoopPre
      (fun a ↦ logG (a.getD 1 0) * K10 + fs name% «verify_tables_loop0»)) :
    CompleteAtDTB fs cert κ "verify_tables" (H.linL B) (H.args B) (Returns (H.retsH B))
      (fun _ ↦ True)
      (fs "verify_tables" + H.sizes.sum + ((vtBs Kf Ksh (vtRunB fs K10 H.n)).sum + ifFrames fs vtPre)) := by
  have hrun : ∀ fp rd, LowDef κ rd → MemL rd (vtL (H.linL B) H.sizes (fun _ ↦ H.ownW B) fs fp) →
      (∀ s ∈ vtPre, VSH (coreProgram.RelIn rd (RegionL (vtL (H.linL B) H.sizes
        (fun _ ↦ H.ownW B) fs fp))) rd (vtσ rd (vtW H (B.at (fp + fs "verify_tables")))
          (H.args B)) s) ∧
      LoadsInBuf (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B))
        (H.bufs (B.at (fp + fs "verify_tables"))) vtPre ∧
      (vtPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG
        (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B) s)) = H.sizes ∧
      ((vtPre.filterMap Main.Stmt.allocSz).map Prod.fst).map
        (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B)) =
        (bases (fp + fs "verify_tables") H.sizes).map (fun b => ofK (addressOfIndex b)) ∧
      vtRets.map (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B)) = H.retsH B := by
    intro fp rd hlow hL
    have hlow14 : LowDefB 14 rd := hlow.mono hκ
    have hm : MemLay rd (H.linL (B.at (fp + fs "verify_tables")) ++
        H.ownL (B.at (fp + fs "verify_tables"))) := hL
    obtain ⟨-, h2, h3, h4, h5⟩ :=
      vt_rel_complete_vtW h hs (B.at (fp + fs "verify_tables")) hlow14 hm
    exact ⟨vt_relIn_complete h hs _ (vtW_ok H _) hlow14 hm, h2, h3, h4, h5⟩
  have hμ33 : H.μ < 33 := hs.hμ33
  have hn32 : H.n < 33 := by
    have := hs.hτ33
    unfold VtHonest.n
    have hall : ∀ x ∈ tableHeightsOf H.rows, x < 33 := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
      have ht6 : t < 6 := by
        have h6 := hs.hr
        have ht' := ht
        unfold tableHeightsOf at ht'
        rw [List.length_zipWith] at ht'
        omega
      have := hs.hτ33 t ht6
      rw [vtHt, List.getD_eq_getElem _ _ ht] at this
      exact this
    clear this
    generalize tableHeightsOf H.rows = l at hall
    have : ∀ a, a < 33 → l.foldl max a < 33 := by
      induction l with
      | nil => intro a ha; exact ha
      | cons x l ih =>
        intro a ha
        exact ih (fun y hy ↦ hall y (List.mem_cons_of_mem _ hy)) _
          (max_lt ha (hall x List.mem_cons_self))
    exact this 0 (by norm_num)
  refine (flat_completeAtTB vtFlat (H.linL B) (H.args B) (H.retsH B) rfl H.sizes
    (fun _ ↦ H.ownW B) (fun _ ↦ by rw [← ownW_lengths H B]; exact forall₂_length_le _)
    (fun fp ↦ vtW H (B.at (fp + fs "verify_tables")))
    (fun fp ↦ H.bufs (B.at (fp + fs "verify_tables"))) ?hbufs ?hrun (fun _ ↦ True)
    (List.replicate 125 fun _ ↦ True) (fun _ _ _ _ ↦ trivial) (by change (vtPre.filter callB).length ≤ _; rw [vt_ncalls]; simp)
    (fun _ _ _ _ i _ _ _ t _ _ _ _ ↦ by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> trivial)
    (vtBs Kf Ksh (vtRunB fs K10 H.n)) _ ?hB
    (fun σ ↦ callsBound_le vtPre σ (vtBs Kf Ksh (vtRunB fs K10 H.n)))).mono le_rfl fun _ _ ↦ trivial
  case hbufs =>
    intro fp q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    refine ⟨q'.1, rfl, fun i hi ↦ ?_⟩
    unfold RegionL
    exact ⟨q', hq', by omega, by omega⟩
  case hrun =>
    intro fp rd hlow hL
    have h := hrun fp rd hlow hL
    exact ⟨h.1, fun d p off hm ↦ h.2.1 d p off (vtEvL_load_mem hm), h.2.2⟩
  case hB =>
    intro fp rd hlow hL i c hc ht rd' hlow' hL' t r hn hv hbo
    obtain ⟨hvsh, -⟩ := hrun fp rd hlow hL
    obtain ⟨v17, v20, v21, vsh⟩ := vt_honest_vals hκ h hs B (fp + fs "verify_tables") hlow hL
    change (flatCalls vtPre (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B)))[i]? =
      some c at hc
    change t.Valid coreProgram rd'
      (c.args.map (vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B))) r at hv
    generalize vtσ rd (vtW H (B.at (fp + fs "verify_tables"))) (H.args B) = σ at hvsh v17 v20 v21 vsh hc hv
    obtain ⟨s, hs, tup, hst, rfl⟩ := flatCalls_getElem vtPre i c hc
    obtain ⟨hsm, -⟩ := getElem?_filter_mem hs
    have hbi : (vtBs Kf Ksh (vtRunB fs K10 H.n)).getD i 0 = vtCallBnd Kf Ksh (vtRunB fs K10 H.n) s := by
      simp [vtBs, List.getD_eq_getElem?_getD, hs]
    rw [hbi]
    have hok := List.all_eq_true.mp vtFlat.hcall s hsm
    have hkind := List.all_eq_true.mp vt_callKinds s hsm
    have hvs := hvsh s hsm
    cases s with
    | call f a rr =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [mkCall] at hn hv ⊢
      simp only [callOk, List.contains_iff_mem] at hok
      simp only [vtCallKindB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
        beq_iff_eq, List.isEmpty_iff] at hkind
      obtain ⟨⟨h10', h9'⟩, hsh'⟩ := hkind
      simp only [vtCallBnd]
      split
      · rename_i hfs
        subst hfs
        obtain ⟨-, hr0⟩ := hsh'.resolve_left (by simp)
        subst hr0
        exact hsh rd' t _ r hn (vt_sh_pre hμ33 vsh hsm) hv hbo
      · rename_i hfs
        exact hKf f hok h10' h9' hfs rd' t _ r hn hv hbo
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [mkCall, decide_eq_true_eq] at hn hv ht ⊢
      simp only [vtCallKindB, Bool.and_eq_true, beq_iff_eq] at hkind
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hkind
      simp only [vtCallBnd]
      have hn0 : 0 < H.n := by
        rcases Nat.eq_zero_or_pos H.n with h0 | h0
        · exfalso; apply ht; rw [v20, h0, pow_zero]; exact e_add_eq_zero_iff.mpr rfl
        · exact h0
      have hpre : LoopPre ([V.n 2336, V.n 2245, V.n 2327, V.n 18, V.n 16, V.n 2245, V.n 2330].map σ) := by
        simp only [List.map_cons, List.map_nil, v21, v17]
        exact loopPre_gen hn0 (by omega) _
      have := h10 rd' t _ r hn hpre hv hbo
      simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero, v17,
        gen_pow_eq_ofK] at this
      rw [logG_spec (by omega)] at this
      unfold vtRunB
      rw [ite_neg' (show ¬H.n = 0 by omega)]
      exact this
    | dispatch x fs' a rr =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      obtain ⟨j, hj, hxj, -⟩ := hvs
      simp only [callOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
        decide_eq_true_eq] at hok
      simp only [vtCallKindB, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hkind
      have hlog : logG (σ x) = j := by rw [hxj]; exact logG_spec (by omega)
      simp only [mkCall, hlog, List.getD_eq_getElem _ _ hj] at hn hv ⊢
      simp only [vtCallBnd]
      obtain ⟨⟨k1, k9⟩, k2⟩ := hkind _ (List.getElem_mem hj)
      exact (hKf _ (hok.1 _ (List.getElem_mem hj)) k1 k9 k2 rd' t _ r hn hv hbo).trans
        (le_foldr_max (List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩))
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst

end
end LeanVM.Guest.B1.Tables
