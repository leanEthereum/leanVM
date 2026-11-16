/-
  LeanVM.Guest.Backend.Sound.Obl.Guest

  The guest's obligations: every function's, from the analysis, the `ext` sites' checks and two
  named facts about the core program.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.World
public import LeanVM.Guest.Backend.Sound.Obl.Gkr
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E00
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E01
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E02
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E03
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E04
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E05
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E06
public import LeanVM.Guest.Backend.Sound.Obl.Eval.E07
public import LeanVM.Guest.Backend.Sound.Obl.Eval.Misc
public import LeanVM.Guest.Backend.Sound.Obl.Eval.XMain
public import LeanVM.Guest.Backend.Sound.Obl.Eval.XLoop0
public import LeanVM.Guest.Backend.Sound.Obl.Eval.XLoop1
public import LeanVM.Guest.Backend.Sound.Obl.Eval.XLq
public import LeanVM.Guest.Backend.Sound.Obl.Eval.XOs0
public import LeanVM.Guest.Backend.Sound.Obl.Eval.XOs1

/-!
# The guest's obligations

The guest's `World.U` is `guestU`: the table's bounds (`guestTab`), relation `0` the exponent
table with its window section, relation `1` the window table, the path windows and the bounded
words read (`guestRel`), and the `ext` functions' relations (`guestX`). With it:

* the analysis accepts every function but `verify_sub` and the `356` of `guestXIdx`, by kernel
  evaluation (`guest_chk`, from `Eval/E00` to `Eval/E07`);
* it accepts `verify_sub` with B1's bounds on `dims_g` and `kappa_base` and its window table as
  facts (`evalVs`), which `VsFacts` states over the core program;
* the `356` of `guestXIdx` have their obligations by the analysis with `ext` sites and B1's facts
  on their bodies (`guestX_obl`: `Obl.Gkr`, `Obl.Walk`, `Obl.Lq`, `Obl.Os`, their checks evaluated
  in `Eval/XMain`, `Eval/XLoop0`, `Eval/XLoop1`, `Eval/XLq`, `Eval/XOs0`, `Eval/XOs1`);
* `exponent_tables` returns the exponent table and its window section (`ExpPost`, over the core
  program).

`guest_obligations_of` gives `W.Obligations tf` for every function of a compiled program whose
core is `coreProgram` and whose `U` is `guestU`, from `ExpPost` and `VsFacts`. Neither mentions a
certificate: they are B1's theorems' statements (`Obl/GuestB1.lean`).
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`exponent_tables` returns the exponent table and its window section** (B1-a's
`exponent_tables_holds`). -/
def ExpPost : Prop :=
  ∀ (rd : Reader) (a r : List E), coreProgram.Rel rd "exponent_tables" a r →
    B1.ExpTables rd ((a ++ r).getD 0 0) ∧ B1.ExpWinTab rd ((a ++ r).getD 0 0)

/-- **`verify_sub`'s facts** (B1-d's `vsDimsKnown0_holds`, `vsKnown_holds`, `vsTabsT_holds`): on a
memory of `2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`, over the exponent table and its window section
at its argument `4`, its first `i` statements put the bounds and relation `vsFacts` lists at `i`. -/
def VsFacts : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ σ : Val,
    B1.ExpTables L.read (σ (.n 4)) ∧ B1.ExpWinTab L.read (σ (.n 4)) →
    ∀ p ∈ vsFacts, Stmt.HoldsList (coreProgram.Rel L.read) L.read σ
      ((coreProgram.getD vsIdx default).body.take p.1) True (fun _ => True) →
      p.2.Holds guestRel L.read σ

/-! ## The evaluations, assembled -/

theorem range_step {p : ℕ → Bool} {a n b m k : ℕ} (h1 : (List.range' a n).all p = true)
    (hb : a + n = b) (h2 : (List.range' b m).all p = true) (hk : n + m = k) :
    (List.range' a k).all p = true := by
  subst hb hk
  rw [← List.range'_append_1, List.all_append, h1, h2]
  rfl

theorem all_step {α : Type} {l : List α} {p : α → Bool} {a n b : ℕ}
    (h1 : ((l.drop a).take n).all p = true) (hb : a + n = b) (h2 : (l.drop b).all p = true) :
    (l.drop a).all p = true := by
  have e : (l.drop a).drop n = l.drop b := by rw [List.drop_drop, ← hb, Nat.add_comm]
  rw [← List.take_append_drop n (l.drop a), List.all_append, h1, e, h2]
  rfl

theorem all_end {α : Type} {l : List α} {p : α → Bool} {a : ℕ} (h : l.length ≤ a) :
    (l.drop a).all p = true := by
  rw [List.drop_eq_nil_of_le h]
  rfl

/-- **The analysis accepts every guest function it does not skip**, assembled. -/
theorem guest_chk_all : (List.range' 0 1549).all (fun j =>
    guestSkip j || chkFn guestTab (Data.coreFunctions.getD j default)) = true := by
  have h := evalE_1505
  have h := range_step evalE_1432 (rfl : 1432 + 73 = 1505) h (rfl : 73 + 44 = 117)
  have h := range_step evalE_1401 (rfl : 1401 + 31 = 1432) h (rfl : 31 + 117 = 148)
  have h := range_step evalE_1376 (rfl : 1376 + 25 = 1401) h (rfl : 25 + 148 = 173)
  have h := range_step evalE_1345 (rfl : 1345 + 31 = 1376) h (rfl : 31 + 173 = 204)
  have h := range_step evalE_1317 (rfl : 1317 + 28 = 1345) h (rfl : 28 + 204 = 232)
  have h := range_step evalE_1289 (rfl : 1289 + 28 = 1317) h (rfl : 28 + 232 = 260)
  have h := range_step evalE_1258 (rfl : 1258 + 31 = 1289) h (rfl : 31 + 260 = 291)
  have h := range_step evalE_1230 (rfl : 1230 + 28 = 1258) h (rfl : 28 + 291 = 319)
  have h := range_step evalE_1202 (rfl : 1202 + 28 = 1230) h (rfl : 28 + 319 = 347)
  have h := range_step evalE_1171 (rfl : 1171 + 31 = 1202) h (rfl : 31 + 347 = 378)
  have h := range_step evalE_1146 (rfl : 1146 + 25 = 1171) h (rfl : 25 + 378 = 403)
  have h := range_step evalE_1115 (rfl : 1115 + 31 = 1146) h (rfl : 31 + 403 = 434)
  have h := range_step evalE_1083 (rfl : 1083 + 32 = 1115) h (rfl : 32 + 434 = 466)
  have h := range_step evalE_1051 (rfl : 1051 + 32 = 1083) h (rfl : 32 + 466 = 498)
  have h := range_step evalE_1026 (rfl : 1026 + 25 = 1051) h (rfl : 25 + 498 = 523)
  have h := range_step evalE_994 (rfl : 994 + 32 = 1026) h (rfl : 32 + 523 = 555)
  have h := range_step evalE_960 (rfl : 960 + 34 = 994) h (rfl : 34 + 555 = 589)
  have h := range_step evalE_930 (rfl : 930 + 30 = 960) h (rfl : 30 + 589 = 619)
  have h := range_step evalE_886 (rfl : 886 + 44 = 930) h (rfl : 44 + 619 = 663)
  have h := range_step evalE_841 (rfl : 841 + 45 = 886) h (rfl : 45 + 663 = 708)
  have h := range_step evalE_796 (rfl : 796 + 45 = 841) h (rfl : 45 + 708 = 753)
  have h := range_step evalE_754 (rfl : 754 + 42 = 796) h (rfl : 42 + 753 = 795)
  have h := range_step evalE_712 (rfl : 712 + 42 = 754) h (rfl : 42 + 795 = 837)
  have h := range_step evalE_670 (rfl : 670 + 42 = 712) h (rfl : 42 + 837 = 879)
  have h := range_step evalE_628 (rfl : 628 + 42 = 670) h (rfl : 42 + 879 = 921)
  have h := range_step evalE_587 (rfl : 587 + 41 = 628) h (rfl : 41 + 921 = 962)
  have h := range_step evalE_546 (rfl : 546 + 41 = 587) h (rfl : 41 + 962 = 1003)
  have h := range_step evalE_505 (rfl : 505 + 41 = 546) h (rfl : 41 + 1003 = 1044)
  have h := range_step evalE_472 (rfl : 472 + 33 = 505) h (rfl : 33 + 1044 = 1077)
  have h := range_step evalE_439 (rfl : 439 + 33 = 472) h (rfl : 33 + 1077 = 1110)
  have h := range_step evalE_414 (rfl : 414 + 25 = 439) h (rfl : 25 + 1110 = 1135)
  have h := range_step evalE_399 (rfl : 399 + 15 = 414) h (rfl : 15 + 1135 = 1150)
  have h := range_step evalE_374 (rfl : 374 + 25 = 399) h (rfl : 25 + 1150 = 1175)
  have h := range_step evalE_349 (rfl : 349 + 25 = 374) h (rfl : 25 + 1175 = 1200)
  have h := range_step evalE_313 (rfl : 313 + 36 = 349) h (rfl : 36 + 1200 = 1236)
  have h := range_step evalE_288 (rfl : 288 + 25 = 313) h (rfl : 25 + 1236 = 1261)
  have h := range_step evalE_263 (rfl : 263 + 25 = 288) h (rfl : 25 + 1261 = 1286)
  have h := range_step evalE_238 (rfl : 238 + 25 = 263) h (rfl : 25 + 1286 = 1311)
  have h := range_step evalE_213 (rfl : 213 + 25 = 238) h (rfl : 25 + 1311 = 1336)
  have h := range_step evalE_188 (rfl : 188 + 25 = 213) h (rfl : 25 + 1336 = 1361)
  have h := range_step evalE_163 (rfl : 163 + 25 = 188) h (rfl : 25 + 1361 = 1386)
  have h := range_step evalE_138 (rfl : 138 + 25 = 163) h (rfl : 25 + 1386 = 1411)
  have h := range_step evalE_113 (rfl : 113 + 25 = 138) h (rfl : 25 + 1411 = 1436)
  have h := range_step evalE_87 (rfl : 87 + 26 = 113) h (rfl : 26 + 1436 = 1462)
  have h := range_step evalE_62 (rfl : 62 + 25 = 87) h (rfl : 25 + 1462 = 1487)
  have h := range_step evalE_37 (rfl : 37 + 25 = 62) h (rfl : 25 + 1487 = 1512)
  have h := range_step evalE_36 (rfl : 36 + 1 = 37) h (rfl : 1 + 1512 = 1513)
  have h := range_step evalE_12 (rfl : 12 + 24 = 36) h (rfl : 24 + 1513 = 1537)
  have h := range_step evalE_11 (rfl : 11 + 1 = 12) h (rfl : 1 + 1537 = 1538)
  have h := range_step evalE_0 (rfl : 0 + 11 = 11) h (rfl : 11 + 1538 = 1549)
  exact h

theorem guest_chk {j : Nat} (hj : j < 1549) (hs : guestSkip j = false) :
    chkFn guestTab (coreProgram.getD j default) = true := by
  have := List.all_eq_true.mp guest_chk_all j (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  rw [hs, Bool.false_or] at this
  exact this

theorem mainTab_ok : ∀ e ∈ mainTab, mainOk e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
  have h : (mainTab.drop 76).all (fun e => mainOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := all_end (by decide)
  have h := all_step evalMain_70 (rfl : 70 + 6 = 76) h
  have h := all_step evalMain_60 (rfl : 60 + 10 = 70) h
  have h := all_step evalMain_50 (rfl : 50 + 10 = 60) h
  have h := all_step evalMain_40 (rfl : 40 + 10 = 50) h
  have h := all_step evalMain_30 (rfl : 30 + 10 = 40) h
  have h := all_step evalMain_20 (rfl : 20 + 10 = 30) h
  have h := all_step evalMain_10 (rfl : 10 + 10 = 20) h
  have h := all_step evalMain_0 (rfl : 0 + 10 = 10) h
  rw [List.drop_zero] at h
  exact List.all_eq_true.mp h

theorem loopTab_ok : ∀ e ∈ loopTab, loopOk e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
  have h : (loopTab.drop 76).all (fun e => loopOk e.1 e.2.1 e.2.2.1 e.2.2.2) = true := all_end (by decide)
  have h := all_step evalLoop_70 (rfl : 70 + 6 = 76) h
  have h := all_step evalLoop_62 (rfl : 62 + 8 = 70) h
  have h := all_step evalLoop_54 (rfl : 54 + 8 = 62) h
  have h := all_step evalLoop_46 (rfl : 46 + 8 = 54) h
  have h := all_step evalLoop_38 (rfl : 38 + 8 = 46) h
  have h := all_step evalLoop_32 (rfl : 32 + 6 = 38) h
  have h := all_step evalLoop_24 (rfl : 24 + 8 = 32) h
  have h := all_step evalLoop_16 (rfl : 16 + 8 = 24) h
  have h := all_step evalLoop_8 (rfl : 8 + 8 = 16) h
  have h := all_step evalLoop_0 (rfl : 0 + 8 = 8) h
  rw [List.drop_zero] at h
  exact List.all_eq_true.mp h

set_option maxRecDepth 4000 in
theorem lqTab_ok : ∀ e ∈ lqTab, lqOk e.1 e.2.1 e.2.2 = true := by
  have h : (lqTab.drop 191).all (fun e => lqOk e.1 e.2.1 e.2.2) = true := all_end (by decide)
  have h := all_step evalLq_144 (rfl : 144 + 47 = 191) h
  have h := all_step evalLq_96 (rfl : 96 + 48 = 144) h
  have h := all_step evalLq_48 (rfl : 48 + 48 = 96) h
  have h := all_step evalLq_0 (rfl : 0 + 48 = 48) h
  rw [List.drop_zero] at h
  exact List.all_eq_true.mp h

theorem osTab_ok : ∀ e ∈ osTab, osOk e.1 e.2 = true := by
  have h : (osTab.drop 11).all (fun e => osOk e.1 e.2) = true := all_end (by decide)
  have h := all_step evalOs_10 (rfl : 10 + 1 = 11) h
  have h := all_step evalOs_9 (rfl : 9 + 1 = 10) h
  have h := all_step evalOs_8 (rfl : 8 + 1 = 9) h
  have h := all_step evalOs_7 (rfl : 7 + 1 = 8) h
  have h := all_step evalOs_6 (rfl : 6 + 1 = 7) h
  have h := all_step evalOs_5 (rfl : 5 + 1 = 6) h
  have h := all_step evalOs_4 (rfl : 4 + 1 = 5) h
  have h := all_step evalOs_3 (rfl : 3 + 1 = 4) h
  have h := all_step evalOs_2 (rfl : 2 + 1 = 3) h
  have h := all_step evalOs_1 (rfl : 1 + 1 = 2) h
  have h := all_step evalOs_0 (rfl : 0 + 1 = 1) h
  rw [List.drop_zero] at h
  exact List.all_eq_true.mp h

/-- The functions of `guestXIdx` are the families'. -/
theorem guestX_cover : guestXIdx.all (fun j => j == 9 || j == 90 || mainTab.any (·.1 == j) ||
    loopTab.any (·.1 == j) || lqTab.any (·.1 == j) || osTab.any (·.1 == j)) = true := by
  decide +kernel

/-- **The obligations of the functions of `guestXIdx`.** -/
theorem guestX_obl : ∀ j ∈ guestXIdx, OblFn (coreProgram.getD j default) := by
  intro j hj
  have := List.all_eq_true.mp guestX_cover j hj
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at this
  rcases this with ((((rfl | rfl) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
  · exact gkrBus_obl
  · exact gkrLoop_obl
  · exact main_obl (mainTab_ok e he)
  · exact loop_obl (loopTab_ok e he)
  · exact lq_obl (lqTab_ok e he)
  · exact os_obl (osTab_ok e he)

/-! ## The table's postconditions and relations -/

/-- A signature with an `xpost` is `exponent_tables`'. -/
theorem sig_xpost {f : String} (h : (guestTab.sig f).xpost ≠ []) :
    f = "exponent_tables" ∧ (guestTab.sig f).xpost = [(0, 0)] := by
  unfold Tab.sig at h ⊢
  cases hf : guestTab.sigs.find? (fun p => nameKey p.1 == nameKey f) with
  | none =>
    simp only [hf] at h
    exact absurd rfl h
  | some p =>
    simp only [hf] at h ⊢
    have hk := List.find?_some hf
    rw [beq_iff_eq] at hk
    obtain ⟨he, hx⟩ := guestTab_xpost p (List.mem_of_find?_eq_some hf) h
    exact ⟨(nameKey_inj hk).symm.trans he, hx⟩

/-- A signature with a postcondition is one of `postNames`'. -/
theorem sig_post {f : String} (h : (guestTab.sig f).post ≠ []) : f ∈ postNames := by
  unfold Tab.sig at h
  cases hf : guestTab.sigs.find? (fun p => nameKey p.1 == nameKey f) with
  | none =>
    simp only [hf] at h
    exact absurd rfl h
  | some p =>
    simp only [hf] at h
    have hk := List.find?_some hf
    rw [beq_iff_eq] at hk
    rw [← nameKey_inj hk]
    exact guestTab_post p (List.mem_of_find?_eq_some hf) h

theorem skip_post {j : Nat} (hs : guestSkip j = true) :
    (coreProgram.getD j default).name ∉ postNames := by
  have hm : j ∈ vsIdx :: guestXIdx := by
    simp only [guestSkip, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hs
    rcases hs with rfl | hs
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hs
  have := List.all_eq_true.mp skip_names j hm
  intro h
  have hc : postNames.contains (coreProgram.getD j default).name = true := List.contains_iff_mem.mpr h
  rw [show coreProgram.getD j default = Data.coreFunctions.getD j default from rfl] at hc
  rw [hc] at this
  exact absurd this (by decide)

theorem getD_of_mem {l : List Fn} {fn : Fn} (h : fn ∈ l) :
    ∃ j < l.length, l.getD j default = fn := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, hj]⟩

/-! ## The guest's obligations -/

variable {κ : ℕ} {W : World κ}

/-- **The guest's obligations**: every function of a compiled program whose core is the guest's
and whose precondition is `guestU` has its obligations, on a memory of `2^κ` words,
`minLogMem ≤ κ ≤ maxLogMem`, given that `exponent_tables` returns the exponent table and B1's
facts in `verify_sub`. -/
theorem guest_obligations_of (hW : W.Compiled) (hcore : W.p.map (·.core) = coreProgram)
    (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) (hU : W.U = guestU W.L.read) (hexp : ExpPost)
    (hvs : VsFacts) : ∀ tf ∈ W.p, W.Obligations tf := by
  have hκ32 : κ ≤ 32 := hκ.2.trans maxLogMem_le
  have hW' : W.core = coreProgram := hcore
  have hU' : W.U = UOf guestTab guestRel guestX W.L.read := hU
  have hlen : coreProgram.length = 1549 := core_length
  have hxp : ∀ f a r, W.core.Rel W.L.read f a r →
      XPost guestRel W.L.read (guestTab.sig f) (a ++ r) := by
    intro f a r h p hp _
    by_cases hx : (guestTab.sig f).xpost = []
    · rw [hx] at hp
      exact absurd hp List.not_mem_nil
    obtain ⟨rfl, he⟩ := sig_xpost hx
    rw [he, List.mem_singleton] at hp
    subst hp
    rw [hW'] at h
    exact ⟨fun _ => hexp _ a r h, fun h1 => absurd h1 (by decide), fun h1 => absurd h1 (by decide),
      fun h1 => absurd h1 (by decide)⟩
  have hP : ∀ fn ∈ W.core, (guestTab.sig fn.name).post ≠ [] → chkFn guestTab fn = true := by
    intro fn hfn hpost
    rw [hW'] at hfn
    obtain ⟨j, hj, rfl⟩ := getD_of_mem hfn
    cases hs : guestSkip j with
    | true => exact absurd (sig_post hpost) (skip_post hs)
    | false => exact guest_chk (hlen ▸ hj) hs
  have hpost := World.post_of_chk hW guestTab_pows hκ32 hU' hP hxp
  have hC : CallsOk W.L.read W.C := fun f a r h => by
    obtain ⟨h1, h2⟩ := World.C_spec hW h
    rw [hU] at h2
    exact ⟨hW' ▸ h1, h2, hpost f a r h⟩
  intro tf htf
  have hmem : tf.core ∈ coreProgram := hcore ▸ List.mem_map_of_mem htf
  obtain ⟨j, hj, hjeq⟩ := getD_of_mem hmem
  by_cases hr : j ∈ guestXIdx
  · intro fp _ hpre
    rw [← World.params_vf hW htf fp, hU] at hpre
    have h := guestX_obl j hr κ W.L hκ.1 hκ.2 W.C (W.vf tf.core.name fp) hC
    rw [hjeq] at h
    rw [hU]
    exact h hpre
  by_cases hv : j = vsIdx
  · subst hv
    refine World.obligations_of_chkF hW guestTab_pows hκ32 hU' hP hxp htf (facts := vsFacts)
      (by rw [← hjeq]; exact evalVs) ?_
    intro σ hpre p hp hl
    rw [← hjeq] at hpre hl
    obtain ⟨hname, hparams⟩ := vs_fn
    have hex : B1.ExpTables W.L.read (σ (.n 4)) ∧ B1.ExpWinTab W.L.read (σ (.n 4)) := by
      have := hpre.1.2.2 (4, 0) (by rw [show coreProgram.getD vsIdx default =
        Data.coreFunctions.getD vsIdx default from rfl, hname, vs_xpre]; exact List.mem_singleton_self _)
        (by rw [show coreProgram.getD vsIdx default = Data.coreFunctions.getD vsIdx default from rfl,
          hparams]; simp)
      rw [show coreProgram.getD vsIdx default = Data.coreFunctions.getD vsIdx default from rfl,
        hparams] at this
      exact this.1 rfl
    exact hvs W.L hκ.1 hκ.2 σ hex p hp (hW' ▸ hl)
  · have hs : guestSkip j = false := by
      simp only [guestSkip, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      refine ⟨hv, ?_⟩
      cases hc : guestXIdx.contains j with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.mp hc) hr
    exact World.obligations_of_chk hW guestTab_pows hκ32 hU' hP hxp htf
      (by rw [← hjeq]; exact guest_chk (hlen ▸ hj) hs)

end
end LeanVM.Guest.Backend.Obl
