/-
  LeanVM.Guest.CoreMode.Fn.column_selector.CsQ

  `column_selector`'s arguments at its instances (`CsQ`), carried down from the terminal's dispatch.
-/

module

public import LeanVM.Guest.CoreMode.Fn.check_opening_terminal.TermQ
public import LeanVM.Guest.CoreMode.Fn.column_selector.ResCs
public import LeanVM.Guest.B1.Terminal.TermFacts
public import LeanVM.Guest.CoreMode.Fam.RefAll
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«check_opening_terminal»
import LeanVM.Guest.StmtsAppend

/-!
# `column_selector`'s arguments

`walk_flat_disp`: a flat body whose walk returns passes each of its dispatches (`B1.DispOk`), so its
events are its statements' (`B1.walk_flat`) and its calls the dispatched ones (`B1.flat_parts`).

`sel_args`: committed column `c`'s selector block holding, its dispatch's argument words are the
offset read from `col_offsets` at `c`, and `g_squares·g^34`; its selector is `kb[src]·g^adj`, a
power of `g` naming an arm. `csQ_all`: at every honest instance of `column_selector__L{κ}`, its
only caller is `check_opening_terminal` (`Res.termCallers_all`), whose calls are its selector blocks'
dispatches (`B1.VerifySub.term_callSF`); with `TermFront` there (`termQ_all`), the block's `g^κ` is
`g` to its column's `κ` (`committedKappas_columnKappas`), the dispatch picks that `κ`, and the offset
is the column's `stackOffsets` entry (`PCtx`), below `2^30` and a multiple of `2^κ`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub (termPre termFound selStart selKap selBlockT selCall kbV colSelNames)
open LeanVM.Guest.Res (TermFront termCallers callersG)
open LeanVM.Protocol.Verifier (gen columnKappas stackOffsets)

@[expose] public section

/-- A dispatch of fewer than `2^64 - 1` ways. -/
def dispSmall : Stmt → Bool
  | .dispatch _ fs _ _ => decide (fs.length < 2 ^ 64 - 1)
  | _ => true

end

public section

theorem dispOk_of_walk1 {σ : Val} {s : Stmt} (hs : dispSmall s = true) (h : walk1 σ s ≠ .stuck) :
    DispOk σ s := by
  cases s with
  | dispatch x fs args rets =>
    simp only [dispSmall, decide_eq_true_eq] at hs
    obtain ⟨e, he, hx⟩ := Res.pick_sel fs 0 (by simpa [walk1] using h)
    exact ⟨e, he, by omega, by simpa using hx⟩
  | _ => trivial

/-- **A flat body whose walk returns passes each of its dispatches.** -/
theorem walk_flat_disp {σ : Val} {vs vs' : List V} : ∀ {pre : List Stmt} {es : List Ev},
    pre.all Stmt.flat = true → pre.all dispSmall = true → walk σ (pre ⧺ [.ret vs]) = .ret es vs' →
    ∀ s ∈ pre, DispOk σ s
  | [], _, _, _, _, s, hs => absurd hs List.not_mem_nil
  | s :: pre, es, hf, hd, hw, s', hs' => by
    simp only [List.all_cons, Bool.and_eq_true] at hf hd
    rw [List.cons_append, walk] at hw
    have hns : walk1 σ s ≠ .stuck := fun h ↦ by rw [h] at hw; simp [Out.seq] at hw
    have hok := dispOk_of_walk1 hd.1 hns
    rw [walk1_flat σ s hf.1 hok] at hw
    simp only [Out.seq] at hw
    cases h2 : walk σ (pre ⧺ [.ret vs]) with
    | fall _ => rw [h2] at hw; simp [Out.pre] at hw
    | ret es2 vs2 =>
      rcases List.mem_cons.mp hs' with rfl | hs'
      · exact hok
      · exact walk_flat_disp hf.2 hd.2 h2 s' hs'
    | stuck => rw [h2] at hw; simp [Out.pre] at hw

theorem term_dispSmall : termPre.all dispSmall = true := by decide +kernel

/-- The other calls of the terminal name no selector. -/
theorem term_other_names : ([(none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "zeta_eq_chain"), .n (val% «check_opening_terminal» "s1#0"), .n (val% «check_opening_terminal» "zeta"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "g_bus_mu")], []),
      (none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "chi_eq_chain"), .n (val% «check_opening_terminal» "s3#0"), .n (val% «check_opening_terminal» "chi"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "g_zc_n")], []),
      (some (.n (val% «check_opening_terminal» "s9#1")), name% «check_opening_terminal_loop0», [.n (val% «check_opening_terminal» "s9#2"), .n (val% «check_opening_terminal» "g_log_mem"), .n (val% «check_opening_terminal» "pi_chain"), .n (val% «check_opening_terminal» "point1")], []),
      (none, "selector_tables", [.n (val% «check_opening_terminal» "point"), .n (val% «check_opening_terminal» "point1")], [.n (val% «check_opening_terminal» "sel_eq")])] ++
    [(none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "out_eq_chain"), .n (val% «check_opening_terminal» "s24#0"), .n (val% «check_opening_terminal» "z_vals"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "s24#2")], []),
      (none, "ring_switch_weight", [.n (val% «check_opening_terminal» "rs_weight~2"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "c_table"), .n (val% «check_opening_terminal» "rs_weight~4")], [.n (val% «check_opening_terminal» "rs_weight")]),
      (none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "ood_chain"), .n (val% «check_opening_terminal» "s28#0"), .n (val% «check_opening_terminal» "ood_z"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "gmv")], [])] :
        List (Option V × String × List V × List V)).all
      (fun t ↦ (List.range 31).all fun κ ↦ t.2.1 != Tables.lName "column_selector" κ) = true := by
  decide +kernel

theorem main_not_cs : (List.range 31).all (fun κ ↦ "main" != Tables.lName "column_selector" κ) = true := by
  decide +kernel

theorem lName_cs_inj : (List.range 31).all (fun a ↦ (List.range 31).all fun b ↦
    Tables.lName "column_selector" a != Tables.lName "column_selector" b || a == b) = true := by
  decide +kernel

theorem cs_not_loop {κ : ℕ} (hκ : κ < 31) {fn : Fn}
    (hf : coreProgram.find? (Tables.lName "column_selector" κ) = some fn) : fn.loop = false := by
  obtain ⟨fn', hf', -, hb⟩ := Tables.csFound hκ
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  simp [Core.Fn.loop, hb, List.reverse_append]

/-- **A selector block's dispatch**: its offset word, its selector `kb[src]·g^adj` naming an arm, and
`sel_g = g_squares·g^34`. -/
theorem sel_args {C : CallRel} {rd : Reader} {σ : Val} {c : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (selBlockT c) True kret) :
    LoadHolds rd (σ (.n (val% «check_opening_terminal» "col_offsets"))) c (σ (.n (selStart c))) ∧
      σ (.n (selKap c).2.1) = σ (.n (kbV (Tables.colKappaSrc c))) * gen ^ Tables.colKappaAdj c ∧
      (∃ j < 31, σ (.n (selKap c).2.1) = ofK (addressOfIndex j)) ∧
      σ (.n ((selKap c).2.2 + 1)) = σ (.n (val% «check_opening_terminal» "g_squares")) * gen ^ 34 := by
  have hadj : Tables.colKappaAdj c < 64 := by unfold Tables.colKappaAdj; split_ifs <;> omega
  simp only [selBlockT, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨loff, h⟩ := h
  obtain ⟨hkv, h⟩ := VerifySub.kapT_sound (src := Tables.colKappaSrc c) (r := selStart c + 1) (rest := [])
    hadj (by rw [List.append_nil]; exact h)
  simp only [Stmt.HoldsList, List.map_cons, List.map_nil] at h
  obtain ⟨c34, m35, ⟨j, hj, hkj, -⟩, -⟩ := h
  refine ⟨loff, hkv, ⟨j, by simpa [colSelNames] using hj, hkj⟩, ?_⟩
  rw [m35, c34, show (17179869184 : ℕ) = 2 ^ 34 from rfl, word_two_pow (by decide)]

variable {r : Ref}

/-- **`column_selector`'s arguments pass down the terminal's dispatch.** -/
theorem csQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (CsQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    f σ bufs kids hJt κ hκ hf fn hfn
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  -- the caller is the terminal
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI)) hw c hc)
    (Tables.lName "column_selector" κ, name% «check_opening_terminal»)
    (CoreMode.FnReg.stCallers_of_column_selector _ (List.mem_map.mpr ⟨κ, List.mem_range.mpr hκ, rfl⟩))
  have hnI := Da.fn_name_of_find hfI
  rw [hcf, hf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hct : fI = name% «check_opening_terminal» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      rw [cs_not_loop hκ hfI] at hl; cases hl
  subst hct
  obtain rfl : fnI = fn% «check_opening_terminal» := Option.some.inj (hfI.symm.trans VerifySub.find_term)
  -- its calls: the selector blocks' dispatches
  have hbody := VerifySub.term_body'
  rw [hbody] at hw
  have hD := walk_flat_disp VerifySub.term_flat term_dispSmall hw
  rw [walk_flat σI [] termPre VerifySub.term_flat hD] at hw
  obtain ⟨rfl, -⟩ := Out.ret.inj hw
  rw [(flat_parts σI termPre VerifySub.term_flat).2.2.2.1, VerifySub.term_callSF] at hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  have htf : t.2.1 = Tables.lName "column_selector" κ := by
    have : (Memory.mkCall σI t).f = t.2.1 := by rcases t with ⟨_ | _, _, _, _⟩ <;> rfl
    rw [← this, hcf, hf]
  rcases List.mem_append.mp ht with ht | ht
  · rcases List.mem_append.mp ht with ht | ht
    · have := List.all_eq_true.mp term_other_names t (List.mem_append_left _ ht)
      have := List.all_eq_true.mp this κ (List.mem_range.mpr hκ)
      rw [htf] at this; simp at this
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp ht
      have hc'n := List.mem_range.mp hc'
      -- the body at its own valuation
      obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
      have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
      obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
      obtain ⟨fn0, hf0, -, hbody0⟩ := termFound
      obtain rfl : fn0 = fn% «check_opening_terminal» := Option.some.inj (hf0.symm.trans VerifySub.find_term)
      rw [hbody0, VerifySub.termT, holdsList_append, holdsList_append, holdsList_append] at hb
      simp only [VerifySub.termHeadT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, k0, k1, k2, k3, k4, k5, k6, k7, -,
        hb⟩ := hb
      change Stmt.HoldsList _ _ σI ((List.range Tables.nCommittedCols).map selBlockT).flatten _ _ at hb
      rw [holdsList_range_flatten Tables.nCommittedCols selBlockT VerifySub.selBlockT_noRet] at hb
      obtain ⟨loff, hkv, ⟨jj, hjj, hkj⟩, hsg⟩ := sel_args (hb.1 c' hc'n)
      -- the terminal's front
      have hT := termQ_all hr I hI _ σI bufsI kidsI hIt rfl _ hfI
      rw [term_fn hfI] at hT
      simp only [VerifySub.termParams, List.map_cons, List.map_nil, TermFront] at hT
      obtain ⟨lm, hs, -, -, -, hl, h31, hm30, -, -, -, hkbR, -, -, hP, -, hst, hG, -⟩ := hT
      set KC := Tables.committedKappas (columnKappas lm Tables.guestLogBytecode hs) with hKCdef
      have hKC := Tables.committedKappas_columnKappas lm hs hl
      have hKClen : KC.length = Tables.nCommittedCols := Tables.committedKappas_length _ hP.1
      -- the selector is `g` to the column's `κ`
      have hsrc8 : Tables.colKappaSrc c' < 8 := by unfold Tables.colKappaSrc; split_ifs <;> omega
      have hadj : Tables.colKappaAdj c' < 64 := by unfold Tables.colKappaAdj; split_ifs <;> omega
      have hkb := VerifySub.kb_loads k0 k1 k2 k3 k4 k5 k6 k7 _ hsrc8
      have hkr := hkbR _ (by simp [hl]; omega)
      rw [VerifySub.kb_words hl hsrc8] at hkr
      have hkbv := loadHolds_unique hkb hkr
      have hKCv : KC.getD c' 0 = ([0, lm] ++ hs).getD (Tables.colKappaSrc c') 0 + Tables.colKappaAdj c' := by
        rw [hKCdef, hKC, List.getD_eq_getElem _ _ (by simpa using hc'n), List.getElem_map, List.getElem_range]
        rfl
      have hes : ([0, lm] ++ hs).getD (Tables.colKappaSrc c') 0 ≤ 30 := by
        rw [List.getD_eq_getElem _ _ (by simp [hl]; omega)]
        have hmem : ∀ x ∈ [0, lm] ++ hs, x ≤ 30 := by
          intro x hx
          simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · omega
          · exact hm30
          · have := h31 x hx; omega
        exact hmem _ (List.getElem_mem _)
      have hsel : σI (.n (selKap c').2.1) = gen ^ KC.getD c' 0 := by
        rw [hkv, hkbv, hKCv, pow_add]
      rw [hsel, ← Value.gen_pow_eq_ofK] at hkj
      have hjκ : KC.getD c' 0 = jj := Value.gen_pow_inj (by omega) (by omega) hkj
      have hnm := htf
      simp only [selCall, hsel, hjκ, Value.gen_pow_eq_ofK, logG_spec (show jj < 2 ^ 64 - 1 by omega),
        colSelNames, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hjj,
        Option.map_some, Option.getD_some] at hnm
      have hinj := List.all_eq_true.mp (List.all_eq_true.mp lName_cs_inj jj (List.mem_range.mpr hjj)) κ
        (List.mem_range.mpr hκ)
      rw [hnm] at hinj
      simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hinj
      subst hinj
      -- the arguments
      have hJv := hval rfl
      rw [hJt] at hJv
      obtain ⟨fn', hfn', hpar, -⟩ := hJv
      obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hfn')
      rw [hpar]
      simp only [selCall, Memory.mkCall, List.map_cons, List.map_nil, CsH]
      set o := (stackOffsets KC).1.getD c' 0 with ho
      have hlo : c' < (stackOffsets KC).1.length := by rw [VerifySub.stackOffsets_length, hKClen]; exact hc'n
      have hoff : LoadHolds r.img.read (σI (.n (val% «check_opening_terminal» "col_offsets"))) c' (gen ^ o) := by
        have := hP.2 c' (by simpa using hlo)
        rw [List.getElem_map] at this
        rw [ho, List.getD_eq_getElem _ _ hlo]; exact this
      refine ⟨o, ?_, ?_, loadHolds_unique loff hoff, by rw [hsg]; exact hG⟩
      · have := VerifySub.stackOffsets_lt KC c'
        calc o < 2 ^ (stackOffsets KC).2 := this
          _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
      · rw [hjκ.symm]; exact VerifySub.stackOffsets_dvd KC c'
  · have := List.all_eq_true.mp term_other_names t (List.mem_append_right _ ht)
    have := List.all_eq_true.mp this κ (List.mem_range.mpr hκ)
    rw [htf] at this; simp at this

/-- **`column_selector`'s arguments at every honest instance.** -/
theorem csQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, CsQ r J := by
  refine insts_all hr (csQ_step hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt κ hκ hf
  have hn := hm _ _ _ _ hJt
  subst hn
  have hmain : "main" ≠ Tables.lName "column_selector" κ := by
    have := List.all_eq_true.mp main_not_cs κ (List.mem_range.mpr hκ)
    simpa using this
  exact absurd hf hmain

end

end LeanVM.Guest.EndExec
