/-
  LeanVM.Guest.B1.Tables.VtCGlue4

  `verify_tables`' completeness: the push side's padding and the pull side, forward (`VtGlue4`).
-/

module

public import LeanVM.Guest.B1.Tables.VtCGlue

/-!
# The pull side, forward

`vt_glue4`: the pull blocks' log-heights range-checked below `34` (`vtcG4Rc`), the memory's and
the bytecode's final counters read by `fs_next` items and stored with their blocks' `g^κ`; the
window's obligations classified by `vtcG4Ok`, by kernel evaluation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## `2826 ..< 3397` -/

/-- The pull side's range checks: the log-height's value and its block. -/
def vtcG4Rc : List (ℕ × ℕ) :=
  [(3327, 37), (3345, 38), (3395, 39), (3463, 40), (3470, 41), (3477, 42),
    (3484, 43), (3491, 44), (3498, 45), (3505, 46), (3512, 47), (3519, 48),
    (3526, 49), (3533, 50), (3540, 51), (3547, 52), (3554, 53), (3561, 54),
    (3568, 55), (3575, 56), (3582, 57), (3589, 58), (3596, 59), (3603, 60),
    (3610, 61), (3617, 62), (3624, 63), (3631, 64), (3638, 65), (3645, 66),
    (3652, 67), (3659, 68), (3666, 69), (3673, 70), (3680, 71), (3687, 72),
    (3694, 73)]

/-- A range check's definitions: the log-height read, `g^33`, the check. -/
def vtcG4RcEq (p : ℕ × ℕ) : List FEq :=
  [.ld (.n p.1) (.n 9) p.2, .def (.const (.n (p.1 + 1)) (word 8589934592 0 0)),
    .rc (.n p.1) (.n (p.1 + 2)) (.n (p.1 + 3)) (.n (p.1 + 4)) (.n (p.1 + 1))]

/-- The window's obligations: loads of `fp_w`, `block_kappa`, `claim_pool`, `block_index_mle`,
the range checks, the two `fs_next` items and their stores. -/
def vtcG4Ok (o : IOb) : Bool :=
  (List.range 16).any (fun i => iobEqb o (.ob (.ld (.n 11) i))) ||
    ((List.range 102).any (fun b => iobEqb o (.ob (.ld (.n 9) b))) ||
    (vtcG4Rc.any (fun p => iobEqb o (.ob (.rc (.n p.1) (.n (p.1 + 2))))) ||
    ((List.range 3).any (fun j => iobEqb o (.ob (.ld (.n 13) j))) ||
    (iobEqb o (.ob (.ld (.n 1852) 1)) || (iobEqb o (.ob (.ld (.n 1852) 2)) ||
    (iobEqb o (.fs (.n 1986) (.n 1987) (.n 2) 3) || (iobEqb o (.fs (.n 3372) (.n 3373) (.n 2) 4) ||
    (iobEqb o (.ob (.holds (.load (.n 3359) (.n 13) 3))) ||
    (iobEqb o (.ob (.holds (.load (.n 3345) (.n 14) 3))) ||
    (iobEqb o (.ob (.holds (.load (.n 3409) (.n 13) 4))) ||
    iobEqb o (.ob (.holds (.load (.n 3395) (.n 14) 4)))))))))))))

set_option maxRecDepth 100000 in
theorem vtcG4_ok : fOkI 3061 3706 [] vtcG4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcG4_obs : (iObs 3061 [] vtcG4).all vtcG4Ok = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcG4_rcB0 : (vtcG4Rc.take 10).all (fun p => decide (p.2 < 102) &&
    (vtcG4RcEq p).all (fun e => (fEqs 3061 [] vtcG4).any (feqEqb e))) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcG4_rcB1 : ((vtcG4Rc.drop 10).take 10).all (fun p => decide (p.2 < 102) &&
    (vtcG4RcEq p).all (fun e => (fEqs 3061 [] vtcG4).any (feqEqb e))) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcG4_rcB2 : ((vtcG4Rc.drop 20).take 10).all (fun p => decide (p.2 < 102) &&
    (vtcG4RcEq p).all (fun e => (fEqs 3061 [] vtcG4).any (feqEqb e))) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcG4_rcB3 : (vtcG4Rc.drop 30).all (fun p => decide (p.2 < 102) &&
    (vtcG4RcEq p).all (fun e => (fEqs 3061 [] vtcG4).any (feqEqb e))) = true := by decide +kernel

theorem vtcG4_rcB : vtcG4Rc.all (fun p => decide (p.2 < 102) &&
    (vtcG4RcEq p).all (fun e => (fEqs 3061 [] vtcG4).any (feqEqb e))) = true := by
  have h : vtcG4Rc = vtcG4Rc.take 10 ++ (vtcG4Rc.drop 10).take 10 ++ (vtcG4Rc.drop 20).take 10 ++
      vtcG4Rc.drop 30 := by decide
  rw [h, List.all_append, List.all_append, List.all_append, vtcG4_rcB0, vtcG4_rcB1, vtcG4_rcB2, vtcG4_rcB3]
  rfl

set_option maxRecDepth 100000 in
theorem vtcG4_fsB : ((fEqs 3061 [] vtcG4).any (feqEqb (.item (.fs (.n 1986) (.n 1987) (.n 2) 3 3359))) &&
    (fEqs 3061 [] vtcG4).any (feqEqb (.item (.fs (.n 3372) (.n 3373) (.n 2) 4 3409)))) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
/-- **The push side's padding and the pull side complete.** -/
theorem vt_glue4 : VtGlue4 := by
  intro κ hκ rd hlow σ cur bk fpw pool cplen bim mF bF ks cv h2 h9 h11 h13 h14 h1852 hcv hbk hks hfpw
    hmF hbF hpool hpm hpb hc3 hc4 hb1 hb2
  rw [← vtcG4_eq]
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) (fun _ => 0) vtcG4 vtcG4_ok σ
  generalize hσf : fRunI rd 3061 (fun _ => 0) [] σ vtcG4 = σf at Cm
  have hf : ∀ u, fRunI rd 3061 (fun _ => 0) [] σ vtcG4 u = σf u := fun u => by rw [hσf]
  have E := fRunI_eqs rd (fun _ => 0) σf vtcG4 [] σ vtcG4_ok hf
  have FR : ∀ k < 3061, σf (.n k) = σ (.n k) := fun k hk =>
    fRunI_eq_of_def rd _ vtcG4_ok hf (by simp [fDef, vNum, hk])
  have h2k : 64 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
  have e9 : σf (.n 9) = bk := by rw [FR 9 (by omega), h9]
  have RC : ∀ p ∈ vtcG4Rc, p.2 < 102 ∧ σf (.n p.1) = gen ^ ks p.2 ∧
      σf (.n (p.1 + 2)) = gen ^ (33 - ks p.2) := by
    intro p hp
    have h := List.all_eq_true.mp vtcG4_rcB p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨hb, he⟩ := h
    have Ep := fun e (h' : e ∈ vtcG4RcEq p) => E e (mem_of_any feqEqb_sound (he e h'))
    simp only [vtcG4RcEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Ep
    obtain ⟨l, c, r⟩ := Ep
    have ex : σf (.n p.1) = gen ^ ks p.2 := by
      rw [show σf (.n p.1) = memAt rd (σf (.n 9)) p.2 from l, e9, memAt_of_loadHolds (hbk p.2 hb)]
    refine ⟨hb, ex, ?_⟩
    rw [r.1, show σf (.n (p.1 + 1)) = word 8589934592 0 0 from c, ex,
      show (8589934592 : ℕ) = 2 ^ 33 by norm_num, word_two_pow (by norm_num)]
    exact gen_pow_div (by have := hks p.2 hb; omega)
  have hFS := vtcG4_fsB
  simp only [Bool.and_eq_true] at hFS
  have f1 := E _ (mem_of_any feqEqb_sound hFS.1)
  have f2 := E _ (mem_of_any feqEqb_sound hFS.2)
  have e2 : σf (.n 2) = cur := by rw [FR 2 (by omega), h2]
  have hcv' : (σf (.n 1986), σf (.n 1987)) = digestScalars cv := by
    rw [FR 1986 (by omega), FR 1987 (by omega)]; exact hcv
  have cF : LoadHolds rd (σf (.n 2)) 3 mF := by rw [e2]; exact hmF
  have cB : LoadHolds rd (σf (.n 2)) 4 bF := by rw [e2]; exact hbF
  have F1 := vtc_fs_vals f1 hcv' cF
  have F2 := vtc_fs_vals f2 F1.2 cB
  have e13 : σf (.n 13) = pool := by rw [FR 13 (by omega), h13]
  have e14 : σf (.n 14) = cplen := by rw [FR 14 (by omega), h14]
  have r38 := RC (3345, 38) (by simp [vtcG4Rc])
  have r39 := RC (3395, 39) (by simp [vtcG4Rc])
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl fun σ' h => ?_
  · intro o ho
    have h := List.all_eq_true.mp vtcG4_obs o ho
    simp only [vtcG4Ok, Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
    rcases h with ⟨i, hi, he⟩ | ⟨b, hb, he⟩ | ⟨p, hp, he⟩ | ⟨j, hj, he⟩ | he | he | he | he | he | he | he | he <;>
      obtain rfl := iobEqb_sound he
    · exact vtc_fpw_ob (by rw [FR 11 (by omega), h11]) hfpw hi
    · exact vtc_ld_ob (by rw [e9]; exact hbk b hb)
    · obtain ⟨hb, ex, ey⟩ := RC p hp
      simp only [IOb.Holds, Ob.Holds]
      rw [ex, ey]
      have a := low_gen_pow hlow (i := ks p.2) (by have := hks p.2 hb; omega)
      have c := low_gen_pow hlow (i := 33 - ks p.2) (by omega)
      exact ⟨gen_pow_ne_zero _, a.1, a.2, c.1, c.2⟩
    · obtain ⟨w, hw⟩ := hpool j hj
      exact vtc_ld_ob (by rw [e13]; exact hw)
    · obtain ⟨w, hw⟩ := hb1
      exact vtc_ld_ob (by rw [FR 1852 (by omega), h1852]; exact hw)
    · obtain ⟨w, hw⟩ := hb2
      exact vtc_ld_ob (by rw [FR 1852 (by omega), h1852]; exact hw)
    · exact vtc_fs_ob hcv' cF
    · exact vtc_fs_ob F1.2 cB
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]; rw [e13, F1.1]; exact hpm
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]; rw [e14, r38.2.1]; exact hc3
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]; rw [e13, F2.1]; exact hpb
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]; rw [e14, r39.2.1]; exact hc4
  · rw [h]
    exact ⟨F1.1, F2.1, F2.2⟩

end
end LeanVM.Guest.B1.VerifySub
