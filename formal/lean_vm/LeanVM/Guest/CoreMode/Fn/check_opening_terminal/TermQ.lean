/-
  LeanVM.Guest.CoreMode.Fn.check_opening_terminal.TermQ

  What `verify_sub` hands `check_opening_terminal` (`Res.TermFront`), carried to every honest
  instance of it (`TermQ`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.column_selector.ResCs
public import LeanVM.Guest.CoreMode.Gen.TermCallers
public import LeanVM.Guest.B1.VerifySub.SoundOf
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# `TermFront` at the terminal's instances

`termFront_of_vs`: `verify_sub`'s front (`B1.VerifySub.vs_front`) gives `TermFront` of the
terminal's call arguments (`termArgsV`): the base `kappa_base` and its words, the placement, the
nibble shares from the carried exponent tables, `verify_tables`' context, the bus point at most
`40` long (its depth, `μ < 34`) and the stack at most `2^30`.

`termQ_all`: at every honest instance of `check_opening_terminal`, by `Res.insts_down`: its only
caller is `verify_sub` (`Res.termCallers_all`), whose only call of it is at `termArgsV`
(`vs_term_sites`), and whose body holds at its own valuation (`Res.holds_of_valid`) with its carried
exponent tables (`carryQ_all`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Res (TermFront termCallers callersG)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The terminal's call arguments in `verify_sub`. -/
def termArgsV : List V :=
  [val% «verify_sub» "g_squares", val% «verify_sub» "zeta", val% «verify_sub» "chi", val% «verify_sub» "rm", val% «verify_sub» "g_bus_mu", val% «verify_sub» "g_zc_n", val% «verify_sub» "g_log_mem", val% «verify_sub» "tau_keccak_g", val% «verify_sub» "kappa_base", val% «verify_sub» "nxt[0]@36", val% «verify_sub» "col_offsets", val% «verify_sub» "z_vals", val% «verify_sub» "c_table", val% «verify_sub» "point", val% «verify_sub» "point1", val% «verify_sub» "inner_total", val% «verify_sub» "yr_at_tail", val% «verify_sub» "sumcheck_target", val% «verify_sub» "ood_z", val% «verify_sub» "gmv"].map .n

end

public section

/-- **`verify_sub` calls the terminal only at `termArgsV`.** -/
theorem vs_term_sites :
    Res.sitesB (fun f args _ ↦ f != name% «check_opening_terminal» || args == termArgsV) VerifySub.vsT = true := by
  decide +kernel

theorem term_not_loop' : (fn% «check_opening_terminal»).loop = false := by decide +kernel

/-- **`TermFront` from `verify_sub`'s front.** -/
theorem termFront_of_vs {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {C : CallRel} {bytecode : List K}
    (hbl : bytecode.length = 2 ^ 23) {σ : Core.Val} (hexp : ExpTables L.read (σ (.n (val% «verify_sub» "g_squares"))))
    (F : VerifySub.VsFront bytecode C L.read σ) : TermFront L.read (termArgsV.map σ) := by
  have hHL := VerifySub.tableHeights_length F.rowsN F.hrowsL
  have hctx := F.hctx
  obtain ⟨chis, hbpR, hgmu, -⟩ := hctx
  have hbusL : F.bus.point.length = VerifySub.busDepth (Tables.layoutOf bytecode F.logMem F.rowsN) :=
    Value.gen_pow_inj (by have := VerifySub.mem_size_le hκ L hbpR; omega) (by have := F.hdep34; omega)
      (hgmu.symm.trans F.h253)
  have hst := F.hst30
  rw [VerifySub.layoutOf_stackLog hbl, VerifySub.placementsOf_snd] at hst
  simp only [termArgsV, List.map_cons, List.map_nil, TermFront]
  exact ⟨F.logMem, Tables.tableHeightsOf F.rowsN, Tables.layoutOf bytecode F.logMem F.rowsN, F.bus, F.claims,
    hHL, F.hh31, F.hm30, rfl, rfl, by rw [hbusL]; have := F.hdep34; omega, F.hkb, F.h72, F.h583, F.hP, F.hKB,
    le_trans (le_max_right _ _) hst, VerifySub.gTabs_of_exp hexp, F.hctx, _, F.hst30, F.h276⟩

variable {r : Ref}

/-- **`TermFront` passes down a call.** -/
theorem termQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (TermQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    f σ bufs kids hJt hf fn hfn
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn', hfn', hpar, -⟩ := hJv
  obtain rfl : fn = fn' := Option.some.inj (hfn.symm.trans hfn')
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  -- the caller is `verify_sub`
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI)) hw c hc)
    _ List.mem_cons_self
  have hnI := Da.fn_name_of_find hfI
  rw [hcf, hf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvs : fI = name% «verify_sub» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn% «check_opening_terminal» :=
        Option.some.inj (hfI.symm.trans VerifySub.find_term)
      rw [term_not_loop'] at hl; cases hl
  subst hvs
  obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans VerifySub.find_vs)
  -- its call of the terminal
  have hs := Res.calls_sites (show Res.sitesB _ (fn% «verify_sub»).body = true by
    rw [VerifySub.vs_body]; exact vs_term_sites) hw c hc
  rw [hcf, hf] at hs
  simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs
  -- its front
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hfI
  rw [VerifySub.vs_body] at hb
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hQ := carryQ_all hr I hI _ σI bufsI kidsI hIt _ hfI (name% «verify_sub», 4, .tab) (by decide) rfl
    (.n 4) (by rw [VerifySub.vs_params]; rfl)
  obtain ⟨hexp, hwin⟩ := hQ
  obtain ⟨⟨F⟩, -⟩ := VerifySub.vs_front (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h)
    (bytecode := List.replicate (2 ^ 23) 0) List.length_replicate hexp hwin hb
  rw [hpar, hs]
  exact termFront_of_vs (by omega) r.img List.length_replicate hexp F

/-- **`TermFront` at every honest instance of the terminal.** -/
theorem termQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, TermQ r J := by
  refine insts_all hr (termQ_step hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt hf
  have hn := hm _ _ _ _ hJt
  subst hn
  exact absurd hf (by decide)

end

end LeanVM.Guest.EndExec
