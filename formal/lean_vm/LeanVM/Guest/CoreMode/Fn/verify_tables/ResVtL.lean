/-
  LeanVM.Guest.CoreMode.Fn.verify_tables.ResVtL

  `verify_tables`' table sumcheck's rounds loop at its honest instances: its cursor in the proof stream
  (`VtLQ`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_tables.ResVt
public import LeanVM.Guest.CoreMode.Fam.LoopCtr
public import LeanVM.Guest.B1.Tables.Vt.Loop10
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»
import LeanVM.Guest.Data.ValNames.«verify_tables_loop0»

/-!
# The table sumcheck's loops

`VtLQ r J`: at an instance of `verify_tables_loop0`, its header names a frame `a` whose cell `22`
(`verify_tables`' stream) holds `st`, its counter is `g^j` below its bound `g^n`, `n < 34`, and its
round record `rounds·g^(7j)` holds the cursor `st·g^q` with room for its `3 (n - j)` words.

`vtLQ_all`: at every honest instance, by `Res.insts_down`. The loop's callers are `verify_tables` and
the loop itself (`Res.termCallers_all`). `verify_tables` calls it at its site (`vt_l10_sites`), with the counter `1`, the bound `g_zc_n` (`VtQ`), and the first
record's cursor `14` words past its own (`vt_zc_front`); a tail call keeps the header and the rest
of the parameters and steps the counter (`Res.loop_path`), and an iteration's round moves the cursor
three words on (`l10_next`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B2C (idxOf fsN fn_of_idx cellJ kidHdr siteOf)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- **The rounds loop's cursor in `verify_tables`' stream.** -/
def VtLQ (r : Ref) (J : Inst) : Prop :=
  ∀ σ bufs kids, J.t = .node name% «verify_tables_loop0» σ bufs kids →
    ∃ a j n q, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 22 < maxCells ∧ σ (.n (val% «verify_tables_loop0» "xk")) = gen ^ j ∧
      σ (.n (val% «verify_tables_loop0» "bound")) = gen ^ n ∧ j < n ∧ n < 34 ∧
      LoadHolds r.img.read (σ (.n (val% «verify_tables_loop0» "zc_rounds")) * σ (.n (val% «verify_tables_loop0» "xk")) ^ 7) 5 (refMem r.img (a + 22) * gen ^ q) ∧
      q + 3 * (n - j) ≤ 8192

def l10ArgsV : List V := [.n (val% «verify_tables» "s73#2"), .n (val% «verify_tables» "g_zc_n"), .n (val% «verify_tables» "zc_rounds"), .n (val% «verify_tables» "tabs"), .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zc_cprod")]

end

public section

/-! ## The loops -/

theorem find_l10 : coreProgram.find? name% «verify_tables_loop0» = some fn% «verify_tables_loop0» :=
  coreProgram_find?_at (j := idx% «verify_tables_loop0») rfl

theorem l10_facts : (fn% «verify_tables_loop0»).params = .n (val% «verify_tables_loop0» "xk") :: .n (val% «verify_tables_loop0» "bound") :: [.n (val% «verify_tables_loop0» "zc_rounds"), .n (val% «verify_tables_loop0» "tabs"), .n (val% «verify_tables_loop0» "zc_rk"), .n (val% «verify_tables_loop0» "zc_cprod")] ∧
    (fn% «verify_tables_loop0»).loop = true ∧ Res.endOfFn fn% «verify_tables_loop0» = some none ∧
    Stmt.blockCallees (loopBody fn% «verify_tables_loop0») = [] := by
  decide +kernel

variable {rd : Reader}

theorem l10_next {x N rounds tabs rkb cprod cur : E} {rets : List E} {j : ℕ}
    (h : coreProgram.Rel rd name% «verify_tables_loop0» [x, N, rounds, tabs, rkb, cprod] rets)
    (hx : x = gen ^ j) (h0 : LoadHolds rd (rounds * x ^ 7) 5 cur) :
    LoadHolds rd (rounds * (gen ^ (j + 1)) ^ 7) 5 (cur * gen ^ 3) := by
  obtain ⟨d, hd⟩ := h
  cases d with
  | zero => exact hd.elim
  | succ d =>
    obtain ⟨fn, hf, σ, hpar, hbody⟩ := hd
    obtain ⟨fn', hf', hp, hb⟩ := Tables.l10Found
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    rw [hp] at hpar
    simp only [List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
      List.cons_append, List.cons.injEq, and_true] at hpar
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
    rw [hb, Tables.l10Body, holdsList_append, holdsList_atoms Tables.l10_atoms] at hbody
    have A : ∀ a, Stmt.atom a ∈ Tables.l10Atoms → a.Holds rd σ := hbody.1
    have m6 := A (.mul (.n 6) (.n 0) (.n 0)) (by simp [Tables.l10Atoms])
    have m7 := A (.mul (.n 7) (.n 6) (.n 0)) (by simp [Tables.l10Atoms])
    have m8 := A (.mul (.n 8) (.n 7) (.n 7)) (by simp [Tables.l10Atoms])
    have m9 := A (.mul (.n 9) (.n 8) (.n 0)) (by simp [Tables.l10Atoms])
    have m10 := A (.mul (.n 10) (.n 2) (.n 9)) (by simp [Tables.l10Atoms])
    have l11 := A (.load (.n 11) (.n 10) 5) (by simp [Tables.l10Atoms])
    have c51 := A (.const (.n 51) (word 8 0)) (by simp [Tables.l10Atoms])
    have m52 := A (.mul (.n 52) (.n 11) (.n 51)) (by simp [Tables.l10Atoms])
    have l13 := A (.load (.n 52) (.n 10) 12) (by simp [Tables.l10Atoms])
    simp only [Atom.Holds] at m6 m7 m8 m9 m10 l11 c51 m52 l13
    have e10 : σ (.n 10) = σ (.n 2) * σ (.n 0) ^ 7 := by rw [m10, m9, m8, m7, m6]; ring
    rw [e10] at l11 l13
    obtain rfl := LeanVM.Guest.B1.loadHolds_unique l11 h0
    rw [m52, c51, word_eight] at l13
    rw [show (gen ^ (j + 1)) ^ 7 = (gen ^ j) ^ 7 * gen ^ 7 by ring, ← mul_assoc,
      LeanVM.Guest.B1.loadHolds_mul_gen_pow, ← hx]
    exact l13

/-! ## `verify_tables`' calls -/

theorem vt_idx : idxOf "verify_tables" = some (fn_idx% «verify_tables») := by decide +kernel

theorem vt_facts : (coreOf (fn_idx% «verify_tables»)).loop = false ∧
    V.n (val% «verify_tables» "stream") ∈ (coreOf (fn_idx% «verify_tables»)).params ∧ cellJ (fn_idx% «verify_tables») (.n (val% «verify_tables» "stream")) = 22 ∧
    22 < fsN (fn_idx% «verify_tables») := by
  decide +kernel

/-- **`verify_tables` calls its loops only at their sites.** -/
theorem vt_l10_sites : Res.sitesB (fun f args rets ↦ f != name% «verify_tables_loop0» ||
    (args == l10ArgsV && rets == [])) (fn% «verify_tables»).body = true := by
  decide +kernel

theorem vt_l10_site {c : Call} (ha : c.args = l10ArgsV) (hr : c.rets = []) :
    ∃ s, siteOf (fn_idx% «verify_tables») c = some s := by
  unfold siteOf
  rw [ha, hr]
  exact Option.isSome_iff_exists.mp (by decide +kernel)

/-! ## Down the honest tree -/

variable {r : Ref}

/-- **The rounds loop's cursor passes down from `verify_tables`, and from one round to the next.** -/
theorem vtLQ_step (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (VtLQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ hhdr hname hval hph hQI
    σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = name% «verify_tables_loop0» := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain rfl : fn = fn% «verify_tables_loop0» := Option.some.inj (hfn.symm.trans find_l10)
  obtain ⟨hpl, hll, hel, hbc⟩ := l10_facts
  rw [hpl] at hpar
  suffices H : ∃ a j n q, J.hdr.2 = ofK (addressOfIndex a) ∧ a + 22 < maxCells ∧ σ (.n 0) = gen ^ j ∧
      σ (.n 1) = gen ^ n ∧ j ≤ n ∧ n < 34 ∧
      LoadHolds r.img.read (σ (.n 2) * σ (.n 0) ^ 7) 5 (refMem r.img (a + 22) * gen ^ q) ∧
      q + 3 * (n - j) ≤ 8192 by
    obtain ⟨a, j, n, q, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
    obtain ⟨j', hj', h0'⟩ := loop_ctr_lt hr hJS hJt find_l10 hll hel hpl h4 h6
    obtain rfl : j = j' := Value.gen_pow_inj (by omega) (by omega) (h3.symm.trans h0')
    exact ⟨a, j, n, q, h1, h2, h3, h4, hj', h6, h7, h8⟩
  -- the caller: `verify_tables`, or the loop's tail
  have hmem : (name% «verify_tables_loop0», name% «verify_tables») ∈ Res.termCallers := by decide
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := Da.fn_name_of_find hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  rcases hcal with hL | ⟨hS, hl⟩
  · -- `verify_tables`' call
    obtain rfl : fI = "verify_tables" := hnI.symm.trans hL
    obtain rfl : fnI = fn% «verify_tables» := Option.some.inj (hfI.symm.trans VerifySub.find_vt)
    obtain ⟨i', hji, hi', -, hfi, hci', -⟩ := fn_of_idx vt_idx
    have hcore : coreOf (fn_idx% «verify_tables») = fn% «verify_tables» := by
      rw [hci']; exact Option.some.inj (hfi.symm.trans VerifySub.find_vt)
    have hw' : walk σI (coreOf (fn_idx% «verify_tables»)).body = .ret es vs := by rw [hcore]; exact hw
    obtain ⟨hloop, hp20, h20, h22⟩ := vt_facts
    -- the site
    have hs := Res.calls_sites vt_l10_sites hw c hc
    rw [hcf] at hs
    simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨hargs, hrets⟩ := hs
    obtain ⟨s, hsite⟩ := vt_l10_site hargs hrets
    have hH := B2C.H_eq_kidHdr hIt vt_idx hw' i
    unfold kidHdr at hH
    rw [hci] at hH
    dsimp only at hH
    rw [ite_eq_right (by rw [hloop]; simp), hsite] at hH
    have hhd : J.hdr.2 = ofK (addressOfIndex I.fp) := by rw [hhdr, hH]
    -- the stream at `verify_tables`' frame
    have hfb := inst_fb hr hI (by rw [hIt]) vt_idx
    have hF0 := inst_frame hr hI hIt vt_idx hw'
    obtain ⟨hlt22, hm22⟩ := ref_read hr (by rw [h20]; omega)
      (hF0.val (.n 20) (List.mem_append_left _ (List.mem_append_left _ hp20)) (by rw [h20]; omega)
        (by rw [h20]; omega))
    rw [h20] at hlt22 hm22
    -- `verify_tables`' cursor and its rounds' setup
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hfI
    obtain ⟨hVt, -⟩ := vt_holds (fun _ _ _ h ↦ Res.KidRel.rel h) hfI hb
    obtain ⟨e2638, hrec0⟩ := vt_zc_front hVt
    obtain ⟨p, n, e5, e2545, hn, hroom⟩ := vtQ_all hr I hI σI bufsI kidsI hIt
    rw [hargs] at hpar
    simp only [l10ArgsV, List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, -, -, -⟩ := hpar
    refine ⟨I.fp, 0, n, p + 14, hhd, hlt22, by rw [p0, e2638, pow_zero], by rw [p1, e2545],
      Nat.zero_le _, hn, ?_, by omega⟩
    rw [p2, p0, e2638, one_pow, mul_one, hm22]
    rw [e5, mul_assoc, ← pow_add] at hrec0
    exact hrec0
  · -- the loop's tail call
    obtain rfl : fI = name% «verify_tables_loop0» := hnI.symm.trans hS
    obtain rfl : fnI = fn% «verify_tables_loop0» := Option.some.inj (hfI.symm.trans find_l10)
    obtain ⟨c0, p0', prest, hps, hca, hi0, hH⟩ :=
      loop_tail_hdr hfI hll (by rw [hbc]; decide) hIt hw hh hci hcf
    rw [hpl] at hps
    obtain ⟨rfl, rfl⟩ := List.cons.inj hps
    rw [hca] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
    obtain ⟨p0, p1, p2, -, -, -⟩ := hpar
    -- the round's cursor
    obtain ⟨a, jI, n, q, hhdI, ha22, h0I, h1I, hjn, hn, hldI, hroomI⟩ := hQI σI bufsI kidsI hIt
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
    have hrel := Tree.Valid.rel _ hv
    unfold Tree.Valid at hv
    obtain ⟨fn', hf'', hp', -⟩ := hv
    obtain rfl : fn' = fn% «verify_tables_loop0» := Option.some.inj (hf''.symm.trans find_l10)
    rw [hpl] at hp'
    simp only [List.map_cons, List.map_nil] at hp'
    rw [← hp'] at hrel
    simp only [Tree.name] at hrel
    have hnext := l10_next hrel h0I hldI
    refine ⟨a, jI + 1, n, q + 3, by rw [hhdr, hH, hhdI], ha22, ?_, by rw [p1, h1I], by omega, hn, ?_, ?_⟩
    · rw [p0, hi0, h0I, ← Value.gen_pow_eq_ofK, ← pow_add]
    · rw [p2, p0, hi0, h0I, ← Value.gen_pow_eq_ofK, ← pow_add, pow_add gen q, ← mul_assoc]
      exact hnext
    · have e : n - jI = n - (jI + 1) + 1 := by omega
      rw [e] at hroomI
      omega

/-- **The rounds loop's cursor at every honest instance.** -/
theorem vtLQ_all (hr : r.Ok) : ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, VtLQ r J := by
  refine insts_all hr (vtLQ_step hr) fun J hm ↦ ?_
  intro σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  exact absurd hn (by decide)

end

end LeanVM.Guest.EndExec
