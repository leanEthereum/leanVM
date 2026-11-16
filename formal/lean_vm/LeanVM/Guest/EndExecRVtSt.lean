/-
  LeanVM.Guest.EndExecRVtSt

  `verify_tables`' reads past its table sumcheck's last record's cursor (`Res.vtStB`), sound at the
  honest frames: they lie inside its stream.
-/

module

public import LeanVM.Guest.EndExecRVt
public import LeanVM.Guest.EndExecRStB
public import LeanVM.Guest.Res.SubDefs

/-!
# The reads past the table sumcheck

`vtSt_read`: at an honest frame of `verify_tables`, cell `2910` holds the last round record's cursor
`σ 2652`, `14 + 3n` words past the frame's cursor (`Tables.vt_zc_run`, `vt_cur13`), which `VtQ` puts
`p` words into the stream with room for `1009`: the `153` evaluations read past it lie inside.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Guest.B2C (idxOf fsN cellJ)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (vtStB stRes topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

theorem vt_idx : idxOf name% «verify_tables» = some (fn_idx% «verify_tables») := by
  decide +kernel

/-- The last record's cursor's load, on every path. -/
theorem vtSt_atom :
    (topAtoms (coreOf (fn_idx% «verify_tables»)).body).contains (.load (.n 2652) (.n 2646) 5) = true := by
  decide +kernel

/-- The cursor's cell and the stream's. -/
theorem vtSt_cells : cellJ (fn_idx% «verify_tables») (.n 2652) = 2910 ∧ 2910 < fsN (fn_idx% «verify_tables») ∧
    cellJ (fn_idx% «verify_tables») (.n 20) = 22 ∧ Res.inFr (fn_idx% «verify_tables») 22 = true := by
  decide +kernel

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **The reads past the table sumcheck's last cursor** lie in `verify_tables`' stream. -/
theorem vtSt_read (t : TopAt A r K i e j) (hr : r.Ok) (hname : (coreOf j).name = name% «verify_tables»)
    {c : ℕ} (hc : c < 153) : RRes (refMem r.img) e.I.fp (stRes 2910 (.fr 22) c) := by
  obtain ⟨f, bufs, kids, hJ, hfj, hfn⟩ := t.found
  rw [hname] at hfn
  subst hfn
  obtain rfl : j = fn_idx% «verify_tables» := by
    have := t.idx
    rw [hJ] at this
    exact Option.some.inj (this.symm.trans vt_idx)
  have hcj : coreOf (fn_idx% «verify_tables») = fn% «verify_tables» :=
    Option.some.inj (hfj.symm.trans VerifySub.find_vt)
  obtain ⟨p, n, e5, hgn, hn, hroom⟩ := vtQ_all hr e.I t.inst e.σ bufs kids hJ
  obtain ⟨args, rets, hv⟩ := inst_valid' hr t.inst hJ
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs_guest hv hfj
  obtain ⟨hH, -⟩ := vt_holds (fun _ _ _ h ↦ Res.KidRel.rel h) hfj hb
  obtain ⟨-, xs, pts, cl, -, -, -, -, e2652, -⟩ := Tables.vt_zc_run hH hn hgn
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  have hl := topAtoms_on_path hw (List.contains_iff_mem.mp vtSt_atom)
  obtain ⟨hc2910, hlt, hc20, hf22⟩ := vtSt_cells
  have hfb := t.fb
  have hm := t.cell hr hF (x := .n 2652) (namedOf_atom hl (by simp [atomUses])) (by rw [hc2910]; omega)
    (by rw [hc2910]; omega)
  rw [hc2910] at hm
  have hs := t.param hr (p := .n 20) (by rw [hcj, vt_params]; decide) (by rw [hc20]; exact hf22)
  rw [hc20] at hs
  refine stRes_of (S := e.σ (.n 20)) (q := p + 14 + 3 * n) (fun v hv ↦ ?_) ?_ (by omega)
  · change refMem r.img (e.I.fp + 22) = v at hv
    rw [← hv, hs]
  · rw [hm, e2652, vt_cur13 hH, e5]
    ring

/-- **`verify_tables`' reads past its table sumcheck at an honest frame.** -/
theorem vtSt_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : vtStB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a bs, hx =>
    simp only [vtStB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
    obtain ⟨⟨hn, hc⟩, hx⟩ := hx
    rw [hx]
    exact vtSt_read t hr hn hc
  | .lt _ _, hx => simp [vtStB] at hx
  | .nz _, hx => simp [vtStB] at hx
  | .name _, hx => simp [vtStB] at hx

end

end

end LeanVM.Guest.EndExec
