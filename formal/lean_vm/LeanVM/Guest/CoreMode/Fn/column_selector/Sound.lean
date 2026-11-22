/-
  LeanVM.Guest.CoreMode.Fn.column_selector.Sound

  `column_selector`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its lowest digit's read.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.CoreMode.Fn.column_selector.ResCs
public import LeanVM.Guest.CoreMode.Fn.column_selector.CsQ
public import LeanVM.Guest.CoreMode.Fn.column_selector.Fam
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«column_selector__L»

/-!
`cs_holds` (`cs`): at an honest instance of `column_selector__L{κ}`, its callers hand it an offset `g^o`, `2^κ ∣ o`, and the nibble shares (`csQ_all`), so its lowest digit is `g^(2^(4-w)·q)`, `q < 2^w` (`cs_digit`), the read `[sel_eq]·[digit₀]·g^off` the `q`-th cell of the strided table.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam idxC baseC vw csSub)

public section

/-- **`column_selector`'s lowest digit at an honest instance** (`cs`): the read lies in its strided
table. -/
theorem cs_holds {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {κ : ℕ} (hκ : κ < 31) (hname : fn.name = B1.Tables.lName "column_selector" κ) :
    (csSub κ).Holds σ := by
  have hκ28 : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hfn : f = B1.Tables.lName "column_selector" κ := by rw [← find_name' hf, hname]
  obtain ⟨fn', hfc, hps, hbody⟩ := B1.Tables.csFound hκ
  rw [← hfn] at hfc
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hfc)
  -- the caller's facts
  have hH := csQ_all hr I hI f σ bufs kids ht κ hκ hfn _ hf
  rw [hps] at hH
  obtain ⟨o, ho, hal, h0, hG⟩ := hH
  -- the body at the instance's valuation
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
  have hfs : ∀ f', 1 ≤ B2C.fs f' := Res.fs_pos
  obtain ⟨-, hb⟩ := Res.holds_of_valid hfs hv hf
  rw [hbody, holdsList_append, holdsList_noRet _ (B1.Tables.csPre_noRet κ)] at hb
  obtain ⟨u, hu, hd, hdv⟩ := cs_digit hκ (by omega) r.img hb.1 hG ho hal h0
  rw [csW_sub] at hdv
  -- the run
  set w := B1.Tables.csW κ 0 with hw'
  have hw4 := B1.Tables.csW_bounds κ 0
  obtain ⟨q, rfl⟩ := hdv
  have hq : q < 2 ^ w := by
    have h16 : 2 ^ (4 - w) * 2 ^ w = 16 := by rw [← pow_add, show 4 - w + w = 4 by omega]; rfl
    by_contra hc
    have := Nat.mul_le_mul_left (2 ^ (4 - w)) (not_lt.mp hc)
    omega
  have hcap : 2 ^ w < capE := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hw4.2) (by decide)
  have hcap0 : 0 < capE := by unfold capE; omega
  rw [csSub]
  show CoreMode.RunSet (vw σ) _ _ _ _ _
  refine ⟨0, 2 ^ w, q, CoreMode.rep_const hcap0, CoreMode.rep_const hcap, Nat.zero_le _, hq, ?_⟩
  have key : ∀ off : ℕ, CoreMode.CCell.valW (vw σ) ⟨[(valf% «column_selector» "sel_eq", 1), (valf% «column_selector» "digits[0]", 1)], off⟩ =
      CoreMode.CCell.valW (vw σ) ⟨[(valf% «column_selector» "sel_eq", 1)], off⟩ * ofK (addressOfIndex (2 ^ (4 - w) * q)) := fun off ↦ by
    simp only [CoreMode.CCell.valW, CoreMode.prodW, vw, hd, Value.gen_pow_eq_ofK, pow_one, mul_one]
    ring
  unfold CoreMode.CCell.addrW
  rw [key]

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.column_selector

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

public section

/-- **Its family** (`cs_holds`). -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  intro c hc
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hc
  intro r hr I hI σ bufs kids ht fn hf x hx
  obtain rfl : x = CoreMode.csSub κ := of_decide_eq_true hx
  exact cs_holds hr hI ht hf (List.mem_range.mp hκ) (find_name' hf)

end

end LeanVM.Guest.CoreMode.Own.column_selector
