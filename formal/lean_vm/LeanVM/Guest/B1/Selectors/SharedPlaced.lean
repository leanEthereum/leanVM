/-
  LeanVM.Guest.B1.Selectors.SharedPlaced

  `shared_selector_tables` is complete in the uniform placed form (`CompleteAtD`): its two tables
  at the bump allocator's positions, returned with their honest words.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTablesComplete
public import LeanVM.Guest.B1.Selectors.SharedVals
public import LeanVM.Guest.B1.Selectors.ColumnSelector
public import LeanVM.Guest.B1.Selectors.TableLemmas
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Terminal.KidsDep
public import LeanVM.Guest.B1.Fwd.PureIn
public import LeanVM.Guest.Data.NameStrings

/-!
# `shared_selector_tables`, placed

On `n < 64` coordinates `zs`, complements `zs1` and shares `gs` at `g^bz`, `g^bz1`, `g^bg`,
`shared_selector_tables` is complete at every frame pointer (`ss_completeAt`): its tables
(`HeapBuf`s of `ssEqW n = 32 (n / 4 + 1)` and `ssGW n = 16 (n / 4 + 1)` words, by `allocDyn`) at the
bump allocator's positions hold the honest nibble tables (`ssEqTab`, `ssGTab`: nibble `j`'s eq
levels at `32j`, its `g` table at `16j`, `padTo`), its callees `shared_selector_tables_loop0` and
`sel_partial_nibble__L{n % 4}` (pure) are complete from their relations (`ss_kids_rel`), its
valuation is the honest one (`ssVal`), and it returns the two tables' pointers with their words
(`SsOut`). `tbReadsAt_chunks`: a buffer of padded blocks holds each block at its stride.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Core.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## Strided buffers -/

/-- `l` padded with zeros to `S` words. -/
def padTo (S : ℕ) (l : List E) : List E := l ++ List.replicate (S - l.length) 0

theorem padTo_length {S : ℕ} {l : List E} (h : l.length ≤ S) : (padTo S l).length = S := by
  simp [padTo]; omega

theorem getD_flatMap_const {S : ℕ} (f : ℕ → List E) (hf : ∀ i, (f i).length = S) :
    ∀ (m i k : ℕ), i < m → k < S →
      ((List.range m).flatMap f).getD (S * i + k) 0 = (f i).getD k 0
  | 0, _, _, hi, _ => absurd hi (by omega)
  | m + 1, i, k, hi, hk => by
    rw [List.range_succ, List.flatMap_append]
    have hlen : ((List.range m).flatMap f).length = S * m := by
      rw [List.length_flatMap]
      simp [hf, List.sum_replicate, Nat.mul_comm]
    rcases Nat.lt_or_ge i m with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact getD_flatMap_const f hf m i k h hk
    · obtain rfl : i = m := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp

theorem length_flatMap_padTo {S m : ℕ} (blk : ℕ → List E) (hb : ∀ i, (blk i).length ≤ S) :
    ((List.range m).flatMap fun i ↦ padTo S (blk i)).length = S * m := by
  rw [List.length_flatMap]
  simp [padTo_length (hb _), List.sum_replicate, Nat.mul_comm]

/-- **A buffer of padded blocks holds each block at its stride.** -/
theorem tbReadsAt_chunks {rd : Reader} {p : E} {S m : ℕ} (blk : ℕ → List E)
    (hb : ∀ i, (blk i).length ≤ S) (h : TbReadsAt rd p ((List.range m).flatMap fun i ↦ padTo S (blk i)))
    {i : ℕ} (hi : i < m) : TbReadsAt rd (p * gen ^ (S * i)) (blk i) := by
  intro k hk
  rw [tb_loadHolds_mul_gen_pow]
  have hS : k < S := lt_of_lt_of_le hk (hb i)
  have hidx : S * i + k < S * m := by nlinarith
  have := h (S * i + k) (by rw [length_flatMap_padTo blk hb]; exact hidx)
  rw [← List.getD_eq_getElem _ 0,
    getD_flatMap_const (fun i ↦ padTo S (blk i)) (fun i ↦ padTo_length (hb i)) m i k hi hS] at this
  rwa [padTo, List.getD_append _ _ _ _ hk, List.getD_eq_getElem _ _ hk] at this

/-! ## The honest tables -/

/-- The eq levels' table: nibble `j`'s eq levels at `32j`. -/
def ssEqTab (zs zs1 : List E) (n : ℕ) : List E :=
  (List.range ((n + 3) / 4)).flatMap fun j ↦ padTo 32 (eqLevels (nib zs j) (nib zs1 j))

/-- The `g` tables' table: nibble `j`'s `g`-power table at `16j`. -/
def ssGTab (gs : List E) (n : ℕ) : List E :=
  (List.range ((n + 3) / 4)).flatMap fun j ↦ padTo 16 (gTable (nib gs j))

theorem ss_nib_length {l : List E} {n : ℕ} (h : l.length = n) (j : ℕ) :
    (nib l j).length = min 4 (n - 4 * j) := by
  simp [nib, h]

theorem eqLevels_nib_le {zs zs1 : List E} {n : ℕ} (hz : zs.length = n) (hz1 : zs1.length = n)
    (j : ℕ) : (eqLevels (nib zs j) (nib zs1 j)).length ≤ 32 := by
  rw [eqLevels_length (ss_nib_length hz j) (ss_nib_length hz1 j)]
  have : min 4 (n - 4 * j) ≤ 4 := min_le_left _ _
  have : 2 ^ (min 4 (n - 4 * j) + 1) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem gTable_nib_le {gs : List E} {n : ℕ} (hg : gs.length = n) (j : ℕ) :
    (gTable (nib gs j)).length ≤ 16 := by
  rw [gTable_length (ss_nib_length hg j)]
  have : min 4 (n - 4 * j) ≤ 4 := min_le_left _ _
  have : 2 ^ min 4 (n - 4 * j) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
  simpa using this

theorem ssEqTab_le {zs zs1 : List E} {n : ℕ} (hz : zs.length = n) (hz1 : zs1.length = n) :
    (ssEqTab zs zs1 n).length ≤ ssEqW n := by
  rw [ssEqTab, length_flatMap_padTo _ (eqLevels_nib_le hz hz1), ssEqW]; omega

theorem ssGTab_le {gs : List E} {n : ℕ} (hg : gs.length = n) : (ssGTab gs n).length ≤ ssGW n := by
  rw [ssGTab, length_flatMap_padTo _ (gTable_nib_le hg), ssGW]; omega

/-- **The tables give `RunTables`.** -/
theorem runTables_of {rd : Reader} {eqt gt : E} {n : ℕ} {zs zs1 gs : List E}
    (hz : zs.length = n) (hz1 : zs1.length = n) (hg : gs.length = n)
    (he : TbReadsAt rd eqt (ssEqTab zs zs1 n)) (hgt : TbReadsAt rd gt (ssGTab gs n)) :
    RunTables rd eqt gt n zs zs1 gs := fun _ hj ↦
  ⟨tbReadsAt_chunks _ (eqLevels_nib_le hz hz1) he hj, tbReadsAt_chunks _ (gTable_nib_le hg) hgt hj⟩

/-! ## The callees -/

/-- `shared_selector_tables`' callees. -/
def ssPureNames : List String := name% «shared_selector_tables_loop0» ::
  ["sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2",
    "sel_partial_nibble__L3"]

theorem ss_pure : coreProgram.PureIn ssPureNames := pureIn_of_pureInB (by decide +kernel)

theorem lName_sel_mem {j : ℕ} (hj : j < 4) : lName "sel_partial_nibble" j ∈ ssPureNames := by
  interval_cases j <;> decide

/-- **`shared_selector_tables`' callees on its words**: `shared_selector_tables_loop0` over the
`n / 4` full nibbles (guarded by `1 + g^(n / 4)`), the partial nibble's
`sel_partial_nibble__L{n % 4}`. -/
theorem ss_kids_rel {rd : Reader} {eqt gt z z1 gsq : E} {n : ℕ} {zs zs1 gs : List E}
    (hzl : zs.length = n) (hz1l : zs1.length = n) (hgl : gs.length = n) (hz : TbReadsAt rd z zs)
    (hz1 : TbReadsAt rd z1 zs1) (hg : TbReadsAt rd gsq gs) (hrt : RunTables rd eqt gt n zs zs1 gs) :
    (1 + gen ^ (n / 4) ≠ 0 → coreProgram.Rel rd name% «shared_selector_tables_loop0»
      [1, gen ^ (n / 4), eqt, z, z1, gt, gsq] []) ∧
    coreProgram.Rel rd (lName "sel_partial_nibble" (n % 4))
      [eqt * gen ^ (32 * (n / 4)), gt * gen ^ (16 * (n / 4)), z * gen ^ (4 * (n / 4)),
        z1 * gen ^ (4 * (n / 4)), gsq * gen ^ (4 * (n / 4))] [0] := by
  set q := n / 4 with hqd
  have hlz : 4 * q ≤ zs.length := by omega
  have hlz1 : 4 * q ≤ zs1.length := by omega
  have hlg : 4 * q ≤ gs.length := by omega
  refine ⟨fun hne ↦ ?_, ?_⟩
  · have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exfalso; apply hne; rw [h0, pow_zero]; exact e_add_self 1
      · exact h0
    have := lp_chain hlz hlz1 hlg hz hz1 hg (fun j hj ↦ hrt j (by omega)) 0 hq0
    rwa [pow_zero] at this
  · have hr4 : n % 4 < 4 := by omega
    have hlen : ∀ l : List E, l.length = n → (nib l q).length = n % 4 := fun l hl ↦ by
      simp [nib, hl]; omega
    refine sel_partial_nibble_complete_holds (n % 4) hr4 rd _ _
      ⟨rfl, nib zs q, nib zs1 q, nib gs q, hlen zs hzl, hlen zs1 hz1l, hlen gs hgl,
        tbReadsAt_nib hz q, tbReadsAt_nib hz1 q, tbReadsAt_nib hg q, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (n % 4) with h0 | h0
      · have e0 : nib zs q = [] := List.length_eq_zero_iff.mp ((hlen zs hzl).trans h0)
        have e1 : nib zs1 q = [] := List.length_eq_zero_iff.mp ((hlen zs1 hz1l).trans h0)
        rw [e0, e1]
        exact fun k hk ↦ absurd hk (by simp [eqLevels])
      · exact (hrt q (by omega)).1
    · rcases Nat.eq_zero_or_pos (n % 4) with h0 | h0
      · rw [h0]; exact tbReadsAt_nil _ _
      · rw [tb_ite_neg'' (show ¬ n % 4 = 0 by omega)]; exact (hrt q (by omega)).2

/-! ## The honest valuation -/

/-- The honest valuation of `shared_selector_tables`' body. -/
noncomputable def ssσ (eqt gt z z1 gsq : E) (n : ℕ) : Val := fun x ↦ ssVal eqt gt z z1 gsq n x.idx

/-- **The honest valuation's words**: the selector, the loop's guard, start and end, the tables
and their sizes, the partial nibble's pointers and return. -/
theorem ssσ_vals (eqt gt z z1 gsq : E) {n : ℕ} (hn : n < 64) :
    ssσ eqt gt z z1 gsq n (.n 18) = gen ^ (n % 4) ∧
      ssσ eqt gt z z1 gsq n (.n 37) = gen ^ (n / 4) ∧
      ssσ eqt gt z z1 gsq n (.n 51) = 1 + gen ^ (n / 4) ∧ ssσ eqt gt z z1 gsq n (.n 52) = 1 ∧
      ssσ eqt gt z z1 gsq n (.n 47) = gen ^ ssEqW n ∧ ssσ eqt gt z z1 gsq n (.n 46) = gen ^ ssGW n ∧
      ssσ eqt gt z z1 gsq n (.n 56) = eqt * gen ^ (32 * (n / 4)) ∧
      ssσ eqt gt z z1 gsq n (.n 57) = gt * gen ^ (16 * (n / 4)) ∧
      ssσ eqt gt z z1 gsq n (.n 58) = z * gen ^ (4 * (n / 4)) ∧
      ssσ eqt gt z z1 gsq n (.n 59) = z1 * gen ^ (4 * (n / 4)) ∧
      ssσ eqt gt z z1 gsq n (.n 60) = gsq * gen ^ (4 * (n / 4)) ∧
      ssσ eqt gt z z1 gsq n (.n 61) = 0 := by
  obtain ⟨hr, hq⟩ := ss_bits hn
  have v18 : ssF n 0 0 * ssF n 1 1 = gen ^ (n % 4) := by
    rw [ssF_eq n 0 0 (by norm_num), ssF_eq n 1 1 (by norm_num), ← pow_add, hr]; ring_nf
  have v37 : ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3 = gen ^ (n / 4) := by
    rw [ssF_eq n 2 0 (by norm_num), ssF_eq n 3 1 (by norm_num), ssF_eq n 4 2 (by norm_num),
      ssF_eq n 5 3 (by norm_num), ← pow_add, ← pow_add, ← pow_add, hq]; ring_nf
  have e45 : ∀ a : E, (fun v42 : E ↦ v42 * v42 * (v42 * v42) * (v42 * v42 * (v42 * v42)))
      (a * word 2 0) = (a * gen) ^ 8 := fun a ↦ by simp only [tb_word_gen]; ring
  refine ⟨v18, v37, ?_, tb_word_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · show word 1 0 + ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3 = _
    rw [v37, tb_word_one]
  · show (fun v45 : E ↦ v45 * v45 * (v45 * v45))
      ((fun v42 : E ↦ v42 * v42 * (v42 * v42) * (v42 * v42 * (v42 * v42))) ((ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3) * word 2 0)) = _
    rw [e45, v37, ssEqW]; ring
  · show (fun v45 : E ↦ v45 * v45)
      ((fun v42 : E ↦ v42 * v42 * (v42 * v42) * (v42 * v42 * (v42 * v42))) ((ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3) * word 2 0)) = _
    rw [e45, v37, ssGW]; ring
  · show eqt * (fun v : E ↦ v * v * (v * v)) ((fun v : E ↦ v * v * (v * v)) (ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3)) *
      (fun v : E ↦ v * v * (v * v)) ((fun v : E ↦ v * v * (v * v)) (ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3)) = _
    beta_reduce; rw [v37]; ring
  · show gt * (fun v : E ↦ v * v * (v * v)) ((fun v : E ↦ v * v * (v * v)) (ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3)) = _
    beta_reduce; rw [v37]; ring
  · show z * (fun v : E ↦ v * v * (v * v)) (ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3) = _
    beta_reduce; rw [v37]; ring
  · show z1 * (fun v : E ↦ v * v * (v * v)) (ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3) = _
    beta_reduce; rw [v37]; ring
  · show gsq * (fun v : E ↦ v * v * (v * v)) (ssF n 2 0 * ssF n 3 1 * ssF n 4 2 * ssF n 5 3) = _
    beta_reduce; rw [v37]; ring

/-! ## The body -/

theorem ss_not_loop : coreProgram.loop "shared_selector_tables" = false := by decide +kernel

theorem ss_flat : ssPre.all Stmt.flat = true := by decide +kernel

theorem ss_addrs : ssPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem ss_allocSzPre : ssPre.filterMap Main.Stmt.allocSz =
    [(.n 48, .inr (.n 47)), (.n 49, .inr (.n 46))] := by decide +kernel

theorem ss_notIte : ssPre.all notIteB = true := by decide +kernel

theorem ss_loadS : ssPre.filterMap Stmt.loadS = [] := by decide +kernel

theorem ssS_noDisp : (ssS ++ ssTail).all (fun s ↦ match s with | .dispatch .. => false | _ => true) =
    true := by decide +kernel

theorem ss_callSF (σ : Val) : ssPre.filterMap (Stmt.callSF σ) =
    [(some (.n 51), name% «shared_selector_tables_loop0», [.n 52, .n 37, .n 48, .n 0, .n 1, .n 49,
      .n 2], []),
      (none, ["sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2",
        "sel_partial_nibble__L3"].getD (logG (σ (.n 18))) "", [.n 56, .n 57, .n 58, .n 59, .n 60],
        [.n 61])] := rfl

theorem ss_dispOk {σ : Val} {n : ℕ} (h : σ (.n 18) = ofK (addressOfIndex (n % 4))) :
    ∀ s ∈ ssPre, DispOk σ s := by
  intro s hs
  rw [ssPre_eq_disp] at hs
  rcases List.mem_append.mp hs with hs | hs
  · have := List.all_eq_true.mp ssS_noDisp s (List.mem_append_left _ hs)
    cases s <;> simp_all [DispOk]
  · rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨n % 4, by simp; omega, by omega, h⟩
    · have := List.all_eq_true.mp ssS_noDisp s (List.mem_append_right _ hs)
      cases s <;> simp_all [DispOk]

theorem ss_names_getD (n : ℕ) :
    ["sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2",
      "sel_partial_nibble__L3"].getD (logG (gen ^ (n % 4))) "" = lName "sel_partial_nibble" (n % 4) := by
  rw [gen_pow_eq_ofK, logG_spec (by omega), List.getD_eq_getElem _ _ (by simp; omega)]
  exact lName_sel_partial (n % 4) (by omega)

/-! ## Placed -/

/-- `shared_selector_tables`' words: its tables, the coordinates, complements and shares. -/
def ssLin (b bz bz1 bg n : ℕ) (zs zs1 gs : List E) : Layout :=
  [(b, ssEqTab zs zs1 n), (b + ssEqW n, ssGTab gs n), (bz, zs), (bz1, zs1), (bg, gs)]

/-- **What `shared_selector_tables` returns**: its two tables' pointers, the tables the buffers. -/
def SsOut (zs zs1 gs : List E) (n : ℕ) : List E → Layout → Prop := fun rets L ↦
  ∃ b, rets = [ofK (addressOfIndex b), ofK (addressOfIndex (b + ssEqW n))] ∧
    L = [(b, ssEqTab zs zs1 n), (b + ssEqW n, ssGTab gs n)]

/-- `shared_selector_tables`' callees, its tables at `g^b`. -/
noncomputable def ssKids (b bz bz1 bg n : ℕ) (zs zs1 gs : List E) : List Kid :=
  [⟨name% «shared_selector_tables_loop0», decide (1 + gen ^ (n / 4) ≠ 0),
      [1, gen ^ (n / 4), ofK (addressOfIndex b), ofK (addressOfIndex bz), ofK (addressOfIndex bz1),
        ofK (addressOfIndex (b + ssEqW n)), ofK (addressOfIndex bg)],
      ssLin b bz bz1 bg n zs zs1 gs, Returns []⟩,
    ⟨lName "sel_partial_nibble" (n % 4), true,
      [ofK (addressOfIndex b) * gen ^ (32 * (n / 4)),
        ofK (addressOfIndex (b + ssEqW n)) * gen ^ (16 * (n / 4)),
        ofK (addressOfIndex bz) * gen ^ (4 * (n / 4)), ofK (addressOfIndex bz1) * gen ^ (4 * (n / 4)),
        ofK (addressOfIndex bg) * gen ^ (4 * (n / 4))], ssLin b bz bz1 bg n zs zs1 gs, Returns [0]⟩]

theorem bufL_ss (b n : ℕ) (zs zs1 gs : List E) :
    bufL b [ssEqW n, ssGW n] [ssEqTab zs zs1 n, ssGTab gs n] =
      [(b, ssEqTab zs zs1 n), (b + ssEqW n, ssGTab gs n)] := by
  simp [bufL, bases]

/-- The callees' Rel from the layout. -/
theorem ss_kids_rel_of {rd : Reader} {b bz bz1 bg n : ℕ} {zs zs1 gs : List E}
    (hzl : zs.length = n) (hz1l : zs1.length = n) (hgl : gs.length = n)
    (hL : MemL rd (ssLin b bz bz1 bg n zs zs1 gs)) :
    (1 + gen ^ (n / 4) ≠ 0 → coreProgram.Rel rd name% «shared_selector_tables_loop0»
      [1, gen ^ (n / 4), ofK (addressOfIndex b), ofK (addressOfIndex bz), ofK (addressOfIndex bz1),
        ofK (addressOfIndex (b + ssEqW n)), ofK (addressOfIndex bg)] []) ∧
    coreProgram.Rel rd (lName "sel_partial_nibble" (n % 4))
      [ofK (addressOfIndex b) * gen ^ (32 * (n / 4)),
        ofK (addressOfIndex (b + ssEqW n)) * gen ^ (16 * (n / 4)),
        ofK (addressOfIndex bz) * gen ^ (4 * (n / 4)), ofK (addressOfIndex bz1) * gen ^ (4 * (n / 4)),
        ofK (addressOfIndex bg) * gen ^ (4 * (n / 4))] [0] :=
  ss_kids_rel hzl hz1l hgl (hL (bz, zs) (by simp [ssLin])) (hL (bz1, zs1) (by simp [ssLin]))
    (hL (bg, gs) (by simp [ssLin]))
    (runTables_of hzl hz1l hgl (hL (b, ssEqTab zs zs1 n) (by simp [ssLin]))
      (hL (b + ssEqW n, ssGTab gs n) (by simp [ssLin])))

/-- **`shared_selector_tables`' honest valuation on its words.** -/
theorem ss_hσ {rd : Reader} {b bz bz1 bg n : ℕ} {zs zs1 gs : List E} (hn : n < 64)
    (hzl : zs.length = n) (hz1l : zs1.length = n) (hgl : gs.length = n)
    {outs : List (List E × Layout)} (ho : OutsOk (ssKids b bz bz1 bg n zs zs1 gs) outs)
    (hL : MemL rd (ssLin b bz bz1 bg n zs zs1 gs)) :
    ∃ σ : Val, (Fn.params (Classical.choose ssFound)).map σ =
        [ofK (addressOfIndex bz), ofK (addressOfIndex bz1), ofK (addressOfIndex bg), gen ^ n] ∧
      (∀ s ∈ ssPre, DispOk σ s) ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (Fn.body (Classical.choose ssFound)) False
        (fun r ↦ r = [ofK (addressOfIndex b), ofK (addressOfIndex (b + ssEqW n))]) ∧
      (ssPre.filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) =
        [ssEqW n, ssGW n] ∧
      ((ssPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        [ofK (addressOfIndex b), ofK (addressOfIndex (b + ssEqW n))] ∧
      CallsMatch σ ((ssPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (ssKids b bz bz1 bg n zs zs1 gs) outs ∧
      ∀ q ∈ ssPre.flatMap (loadsEv σ), False := by
  obtain ⟨-, hp, hb⟩ := Classical.choose_spec ssFound
  set eqt := ofK (addressOfIndex b)
  set gt := ofK (addressOfIndex (b + ssEqW n))
  refine ⟨ssσ eqt gt (ofK (addressOfIndex bz)) (ofK (addressOfIndex bz1)) (ofK (addressOfIndex bg))
    n, ?_⟩
  obtain ⟨e18, e37, e51, e52, e47, e46, e56, e57, e58, e59, e60, e61⟩ :=
    ssσ_vals eqt gt (ofK (addressOfIndex bz)) (ofK (addressOfIndex bz1)) (ofK (addressOfIndex bg)) hn
  rcases outs with _ | ⟨o1, _ | ⟨o2, _ | ⟨o3, os⟩⟩⟩
  · exact absurd ho (by simp [OutsOk, ssKids])
  · exact absurd ho (by simp [OutsOk, ssKids])
  swap
  · exact absurd ho.2.2 (by simp [OutsOk])
  obtain ⟨ho1, ho2, -⟩ := ho
  have hrt : RunTables rd eqt gt n zs zs1 gs :=
    runTables_of hzl hz1l hgl (hL (b, ssEqTab zs zs1 n) (by simp [ssLin]))
      (hL (b + ssEqW n, ssGTab gs n) (by simp [ssLin]))
  refine ⟨by rw [hp]; rfl, ss_dispOk (n := n) (by rw [e18, gen_pow_eq_ofK]), ?_, ?_,
    by rw [ss_allocSzPre]; rfl, ?_, fun q hq ↦ ?_⟩
  · rw [hb, holdsList_append, holdsList_noRet _ ssPre_noRet]
    exact ⟨ss_holds rd hn hzl hz1l hgl (hL (bz, zs) (by simp [ssLin]))
      (hL (bz1, zs1) (by simp [ssLin])) (hL (bg, gs) (by simp [ssLin])) hrt, rfl⟩
  · rw [ss_allocSzPre]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, e47, e46, gen_pow_eq_ofK]
    rw [logG_spec (by simp only [ssEqW]; omega), logG_spec (by simp only [ssGW]; omega)]
  · rw [ss_callSF, e18, ss_names_getD n]
    simp only [List.map_cons, List.map_nil, Main.mkCall, ssKids]
    refine ⟨rfl, by rw [e51], fun ht ↦ ⟨?_, ((ho1 ht).1).symm⟩, rfl, rfl, fun _ ↦ ⟨?_, ?_⟩,
      trivial⟩
    · simp only [List.map_cons, List.map_nil, e52, e37]; rfl
    · simp only [List.map_cons, List.map_nil, e56, e57, e58, e59, e60]; rfl
    · simp only [List.map_cons, List.map_nil, e61]
      rw [(ho2 rfl).1]
  · have hq' := filterMap_of_loadsEv ss_notIte hq
    rw [ss_loadS] at hq'
    exact List.not_mem_nil hq'

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The callees' words: the tables, the caller's. -/
theorem ss_kids_region {b bz bz1 bg n : ℕ} {zs zs1 gs : List E} {L : Layout}
    (hL : (bz, zs) ∈ L ∧ (bz1, zs1) ∈ L ∧ (bg, gs) ∈ L) :
    ∀ k ∈ ssKids b bz bz1 bg n zs zs1 gs, ∀ i, RegionL k.Lin i →
      RegionL L i ∨ RegionL [(b, ssEqTab zs zs1 n), (b + ssEqW n, ssGTab gs n)] i := by
  intro k hk i hi
  have hkL : k.Lin = ssLin b bz bz1 bg n zs zs1 gs := by
    simp only [ssKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> rfl
  rw [hkL] at hi
  obtain ⟨q, hq, hi⟩ := hi
  simp only [ssLin, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp, hi⟩
  · exact Or.inr ⟨_, by simp, hi⟩
  · exact Or.inl ⟨_, hL.1, hi⟩
  · exact Or.inl ⟨_, hL.2.1, hi⟩
  · exact Or.inl ⟨_, hL.2.2, hi⟩

theorem ss_lin_mem {rd : Reader} {b bz bz1 bg n : ℕ} {zs zs1 gs : List E} {L : Layout}
    (hL : (bz, zs) ∈ L ∧ (bz1, zs1) ∈ L ∧ (bg, gs) ∈ L)
    (hB : MemL rd [(b, ssEqTab zs zs1 n), (b + ssEqW n, ssGTab gs n)]) (hLin : MemL rd L) :
    MemL rd (ssLin b bz bz1 bg n zs zs1 gs) := by
  intro q hq
  simp only [ssLin, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hB _ (by simp)
  · exact hB _ (by simp)
  · exact hLin _ hL.1
  · exact hLin _ hL.2.1
  · exact hLin _ hL.2.2

/-- **`shared_selector_tables` is complete, placed**: on the coordinates, complements and shares,
at every frame pointer, its tables at the bump allocator's positions, returning them with their
honest words. -/
theorem ss_completeAt (κ : ℕ) {bz bz1 bg n : ℕ} {zs zs1 gs : List E} (hn : n < 64)
    (hzl : zs.length = n) (hz1l : zs1.length = n) (hgl : gs.length = n) :
    CompleteAtD fs cert κ "shared_selector_tables" [(bz, zs), (bz1, zs1), (bg, gs)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bz1), ofK (addressOfIndex bg), gen ^ n]
      (SsOut zs zs1 gs n) := by
  obtain ⟨hf, -, hb⟩ := Classical.choose_spec ssFound
  have hmem : (bz, zs) ∈ [(bz, zs), (bz1, zs1), (bg, gs)] ∧
      (bz1, zs1) ∈ [(bz, zs), (bz1, zs1), (bg, gs)] ∧ (bg, gs) ∈ [(bz, zs), (bz1, zs1), (bg, gs)] :=
    ⟨by simp, by simp, by simp⟩
  refine completeAt_flatOutD (fs := fs) (cert := cert) hf ss_not_loop κ _ _
    (fun fp ↦ [ofK (addressOfIndex (fp + fs "shared_selector_tables")),
      ofK (addressOfIndex (fp + fs "shared_selector_tables" + ssEqW n))]) _ hb ss_flat ss_addrs
    [ssEqW n, ssGW n] (fun _ ↦ [ssEqTab zs zs1 n, ssGTab gs n])
    (fun _ ↦ .cons (ssEqTab_le hzl hz1l) (.cons (ssGTab_le hgl) .nil))
    (fun fp ↦ ⟨_, rfl, bufL_ss _ _ _ _ _⟩)
    (fun fp ↦ ssKids (fp + fs "shared_selector_tables") bz bz1 bg n zs zs1 gs) ?_ ?_ ?_ ?_
  · intro fp k hk ht
    simp only [ssKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp only [decide_eq_true_eq] at ht
      exact completeAt_of_rel_pureD ss_pure (by simp [ssPureNames])
        (fun rd hL ↦ (ss_kids_rel_of hzl hz1l hgl hL).1 ht) κ
    · exact completeAt_of_rel_pureD ss_pure (lName_sel_mem (by omega))
        (fun rd hL ↦ (ss_kids_rel_of hzl hz1l hgl hL).2) κ
  · intro fp k hk _ i hi
    rw [bufL_ss]
    exact ss_kids_region hmem k hk i hi
  · intro fp rd hB hLin k hk
    rw [bufL_ss] at hB
    have hkL : k.Lin = ssLin (fp + fs "shared_selector_tables") bz bz1 bg n zs zs1 gs := by
      simp only [ssKids, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rfl
    rw [hkL]
    exact ss_lin_mem hmem hB hLin
  · intro fp outs ho rd _ hB hLin
    rw [bufL_ss] at hB ⊢
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := ss_hσ hn hzl hz1l hgl ho (ss_lin_mem hmem hB hLin)
    exact ⟨σ, h1, h2, h3, h4, by rw [h5]; simp [bases], h6, fun q hq ↦ (h7 q hq).elim⟩

end
end LeanVM.Guest.B1.Tables
