/-
  LeanVM.Guest.EndExecRSub

  The certificates' order residuals the exponent facts bound and their `sub` residuals, left open
  by none of the families.
-/

module

public import LeanVM.Guest.EndExecRCq
public import LeanVM.Guest.Res.SubDefs
public import LeanVM.Guest.EndExecRStB
public import LeanVM.Guest.EndExecRBlk
public import LeanVM.Guest.EndExecRVtB
public import LeanVM.Guest.EndExecRLift
public import LeanVM.Guest.EndExecRVkSt
public import LeanVM.Guest.EndExecRRt
public import LeanVM.Guest.EndExecRCld
public import LeanVM.Guest.EndExecRVtSt
public import LeanVM.Guest.EndExecRVs
public import LeanVM.Guest.EndExecRGkr
public import LeanVM.Guest.EndExecRVtP
public import LeanVM.Guest.EndExecRExp
public import LeanVM.Guest.EndExecRVtG

/-!
# The families' residuals at the honest frames

`resOpen_ltExp`: an order residual an exponent fact bounds (`Res.ltExpB`) holds at every honest
frame, the facts there from `TermFront` (`termQ_all`, `expQ_of_termQ`). `resOpen_subOk`: each
certificate's `sub` residuals in the families (`Res.SubOk`) leave none open but the listed
certificates': those read off the function's code (`subFam_top`), and `check_opening_terminal`'s
(`dim_top`, its dimension facts from `TermFront`) and `column_selector`'s (`cs_top`, its arguments
from the terminal's dispatch, `csQ_all`), the proof stream's reads (`st_top`), the runs a split cuts into blocks (`blk_top`),
`verify_tables`' table sumcheck's reads (`vt_top`), the runs of a lift (`lift_top`),
`verify_keccak`'s reads past its layers (`vkSt_top`), the roots' tree's reads (`roots_top`), the
tiles (`tileFam_top`), a lift read back (`liftBack_top`), the same cells named one index up
(`ordShift_top`), `verify_tables`' reads past its table sumcheck (`vtSt_top`), the runs a product's
factors bound (`expFam_top`), and `verify_tables`' groups' bases (`vtGrp_top`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (fn_of_idx entryOf)
open LeanVM.Prover.Exec
open LeanVM.Guest.Res (allV_get subB SubOk resExc splitB anyResB anyLink monoResB ltExpB termFamB)

public section

/-- **The order residuals the exponent facts bound hold at the honest frames.** -/
theorem resOpen_ltExp {Ks : List Mode.Cert} {A : String → Bridge.FnAl} :
    ResOpen Ks A fun j x ↦ ltExpB j x = true := by
  intro r hr K hK i hi e j t x hx hp hin
  simp only [ltExpB, Bool.or_eq_true] at hp
  rcases hp with hp | hp
  swap
  · exact vs_top t hr hp hin
  exact ltExp_top t hr (expQ_of_termQ (termQ_all hr e.I t.inst) (expQv_all hr e.I t.inst)) hp

/-- **`check_opening_terminal`'s and `column_selector`'s families at an honest frame.** -/
theorem termFam_top {A : String → Bridge.FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}
    {w : Res.Wit} (t : TopAt A r K i e j) (hr : r.Ok) (hW : Res.witOk j w = true) {x : Mode.Res}
    (hx : termFamB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  simp only [termFamB, Bool.or_eq_true] at hx
  rcases hx with hx | hx
  · exact dim_top t hr hW (dimQ_of_termQ (termQ_all hr e.I t.inst)) hx
  · exact cs_top t hr (csQ_all hr e.I t.inst) hx

/-- **No `sub` residual outside the families is left open**: each certificate's are in the
families, or the certificate is listed and its residuals given. -/
theorem resOpen_subOk {Ks : List Mode.Cert} {A : String → Bridge.FnAl} (hok : ∀ K ∈ Ks, SubOk resExc K)
    (hexc : ∀ K ∈ resExc, ResCert A K) :
    ResOpen Ks A fun j x ↦ (((∃ a bs, x = .sub a bs) ∧ splitB j x = false) ∧ anyResB anyLink j x = false) ∧
      monoResB j x = false := by
  intro r hr K hK i hi e j t x hx hp hin
  rcases hok K hK with hK' | ⟨j0, w, hj0, hent, hW, hall⟩
  · exact hexc K hK' r hr i hi e j t x hx hin
  obtain rfl : j = j0 := by
    obtain ⟨_, -, -, -, -, -, -, -, -, hj⟩ := fn_of_idx t.idx
    refine fnOf_entry_inj hj hj0 ?_
    have := t.entry
    simp only [entryOf, t.idx] at this
    rw [this, hent]
  obtain ⟨⟨⟨⟨a, bs, rfl⟩, hs⟩, ha⟩, hm⟩ := hp
  cases hg : K.F.res.get i with
  | none => rw [hg] at hx; cases hx
  | some l =>
    rw [hg, Option.getD_some] at hx
    have hf := List.all_eq_true.mp (allV_get hall hg) _ hx
    simp only [subB, hs, ha, hm, Bool.false_or, Bool.or_eq_true] at hf
    rcases hf with (((((((((((((((hf | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf
    · exact subFam_top t hr hW hf
    · exact termFam_top t hr hW hf
    · exact st_top t hr hf
    · exact blk_top t hr hf
    · exact vt_top t hr hf
    · exact lift_top t hr hf
    · exact vkSt_top t hr hf
    · exact roots_top t hr hf
    · exact tileFam_top t hr hW hf
    · exact liftBack_top t hr hf
    · exact ordShift_top t hr hW hf hin
    · exact vtSt_top t hr hf
    · exact expFam_top t hr hW hf
    · exact vtGrp_top t hr hf
    · exact vs_top t hr hf hin
    · exact gkrSt_top t hr hf
    · exact vbgRow_top t hr hf

end

end LeanVM.Guest.EndExec
