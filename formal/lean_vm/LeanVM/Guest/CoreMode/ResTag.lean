/-
  LeanVM.Guest.CoreMode.ResTag

  A heap certificate's residuals checked each against the family the generator names for it
  (`resTagged`), which implies the route's check of them (`resOk`).
-/

module

public import LeanVM.Guest.CoreMode.CoreResG

/-!
# Residuals by their families

`resFamG` is a disjunction of families, tried in order; a family that fails scans the function's
atoms to their end, so the kernel pays every family before the one that holds. The generator knows
which one holds (`scripts/core-mode/callcres.py`) and names it, as a tag: `resFamFrom t` skips the
families before `t`. A tag past every family that holds fails the check (a failed build, never a
wrong one); tag `0`, and a residual past the tags, is checked by `resFamG` itself.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `resFamG`'s families from the `t`-th on: `0` to `4` its ghost-free ones (`resFam`, `resQ`, `rcPts`, `rcTab`,
`ownFam`, with the values below `GB`), `5` to `8` its ghost ones (`mlSub`, `stSub`, `cmSub`, `gwFam`). -/
noncomputable def resFamFrom (fn : Fn) (xc : List ℕ) (gw : List (CCell × ℕ)) (t : ℕ) (r : CRes) : Bool :=
  match t with
  | 0 => resFamG fn xc gw r
  | 1 => ((resQ fn r || rcPts fn r || rcTab fn r || ownFam fn r) && r.vals.all (Nat.blt · GB)) ||
      mlSub fn r || stSub fn r || cmSub fn r || gwFam fn gw r
  | 2 => ((rcPts fn r || rcTab fn r || ownFam fn r) && r.vals.all (Nat.blt · GB)) ||
      mlSub fn r || stSub fn r || cmSub fn r || gwFam fn gw r
  | 3 => ((rcTab fn r || ownFam fn r) && r.vals.all (Nat.blt · GB)) || mlSub fn r || stSub fn r || cmSub fn r ||
      gwFam fn gw r
  | 4 => (ownFam fn r && r.vals.all (Nat.blt · GB)) || mlSub fn r || stSub fn r || cmSub fn r || gwFam fn gw r
  | 5 => mlSub fn r || stSub fn r || cmSub fn r || gwFam fn gw r
  | 6 => stSub fn r || cmSub fn r || gwFam fn gw r
  | 7 => cmSub fn r || gwFam fn gw r
  | _ => gwFam fn gw r

theorem resFamG_of_from {fn : Fn} {xc : List ℕ} {gw : List (CCell × ℕ)} {t : ℕ} {r : CRes}
    (h : resFamFrom fn xc gw t r = true) : resFamG fn xc gw r = true := by
  unfold resFamFrom resFamG at h
  unfold resFamG
  split at h <;> simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢ <;> tauto

/-- Each residual of `l` of its family from its tag on (`ts`, in order; past the tags, tag `0`). -/
noncomputable def resTagged (fn : Fn) (xc : List ℕ) (gw : List (CCell × ℕ)) : List CRes → List ℕ → Bool
  | [], _ => true
  | r :: l, ts => resFamFrom fn xc gw (ts.headD 0) r && resTagged fn xc gw l ts.tail

theorem all_of_tagged {fn : Fn} {xc : List ℕ} {gw : List (CCell × ℕ)} :
    ∀ {l : List CRes} {ts : List ℕ}, resTagged fn xc gw l ts = true → l.all (resFamG fn xc gw) = true
  | [], _, _ => rfl
  | _ :: _, _, h => by
    simp only [resTagged, Bool.and_eq_true] at h
    rw [List.all_cons, resFamG_of_from h.1, all_of_tagged h.2, Bool.true_and]

theorem resOk_of_tagged {Cf : CFun} {ts : List ℕ} (h : resTagged Cf.fn Cf.xc Cf.H.sig.gw Cf.H.res ts = true) :
    resOk Cf = true :=
  all_of_tagged h

end

end LeanVM.Guest.CoreMode
