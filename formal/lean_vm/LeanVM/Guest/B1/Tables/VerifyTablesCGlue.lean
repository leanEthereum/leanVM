/-
  LeanVM.Guest.B1.Tables.VerifyTablesCGlue

  `verify_tables`' completeness: the windows of pure arithmetic between the slices, the
  `block_index_mle` hint and the first table's `g^τ`.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesC0

/-!
# The glue windows

A window of definitions only (`pureOk`: its statements as items, no obligation) completes from
any valuation (`completes_pure`). `vtGaps`: the 63 such windows between the selectors, the glue
slices and the table sumcheck, as (first statement, end, first value, end). `vt_c_bim`: statements
`1574 ..< 1577`, `block_index_mle` hinted. `vt_c_tau`: statement `4374`, the first table's
`g^τ` read from `dims`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- A statement as an item: its hint, or its atom. -/
def pureItem : Stmt → FItem
  | .atom (.hint h) => .hint h
  | .atom a => .atom a
  | _ => .atom (.assertEq (.n 0) (.n 0))

/-- A window of definitions only. -/
def pureOk (lo hi : ℕ) (ss : List Stmt) : Bool :=
  stmtsEqb ((ss.map pureItem).flatMap FItem.stmts) ss && fOkI lo hi [] (ss.map pureItem) &&
    (iObs lo [] (ss.map pureItem)).isEmpty

theorem completes_pure {C : CallRel} {rd : Reader} {lo hi : ℕ} {ss : List Stmt} (h : pureOk lo hi ss = true)
    (σ : Val) : Completes C rd lo hi ss σ (fun _ => True) := by
  simp only [pureOk, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨he, hok⟩, hob⟩ := h
  rw [← stmtsEqb_sound he]
  refine (completes_items (fun _ => 0) _ hok σ (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl fun _ _ => trivial
  rw [hob]; intro o ho; simp at ho

/-- The pure windows: first statement, end, first value, end. -/
def vtGaps : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1836, 1838, 2104, 2106), (1866, 1868, 2133, 2135), (1896, 1898, 2162, 2164), (1926, 1928, 
    2191, 2193), (1956, 1958, 2220, 2222), (1986, 1988, 2249, 2251), (2016, 2018, 2278, 2280), 
    (2046, 2048, 2307, 2309), (2076, 2078, 2336, 2338), (2106, 2108, 2365, 2367), (2136, 2138, 
    2394, 2396), (2166, 2168, 2423, 2425), (2196, 2198, 2452, 2454), (2226, 2228, 2481, 2483), 
    (2256, 2258, 2510, 2512), (2286, 2288, 2539, 2541), (2316, 2318, 2568, 2570), (2346, 2348, 
    2597, 2599), (2376, 2378, 2626, 2628), (2406, 2408, 2655, 2657), (2436, 2438, 2684, 2686), 
    (2466, 2468, 2713, 2715), (2496, 2498, 2742, 2744), (2526, 2528, 2771, 2773), (2556, 2558, 
    2800, 2802), (2586, 2588, 2829, 2831), (2616, 2618, 2858, 2860), (2646, 2648, 2887, 2889), 
    (2676, 2678, 2916, 2918), (2706, 2708, 2945, 2947), (2736, 2738, 2974, 2976), (2766, 2768, 
    3003, 3005), (2796, 2798, 3032, 3034), (3425, 3426, 3733, 3734), (3454, 3456, 3761, 3763), 
    (3484, 3486, 3790, 3792), (3514, 3516, 3819, 3821), (3544, 3546, 3848, 3850), (3574, 3576, 
    3877, 3879), (3604, 3606, 3906, 3908), (3634, 3636, 3935, 3937), (3664, 3666, 3964, 3966), 
    (3694, 3696, 3993, 3995), (3724, 3726, 4022, 4024), (3754, 3756, 4051, 4053), (3784, 3786, 
    4080, 4082), (3814, 3816, 4109, 4111), (3844, 3846, 4138, 4140), (3874, 3876, 4167, 4169), 
    (3904, 3906, 4196, 4198), (3934, 3936, 4225, 4227), (3964, 3966, 4254, 4256), (3994, 3996, 
    4283, 4285), (4024, 4026, 4312, 4314), (4054, 4056, 4341, 4343), (4084, 4086, 4370, 4372), 
    (4114, 4116, 4399, 4401), (4144, 4146, 4428, 4430), (4174, 4176, 4457, 4459), (4204, 4206, 
    4486, 4488), (4234, 4273, 4515, 4554)]

set_option maxRecDepth 100000 in
theorem vtGaps_ok : vtGaps.all (fun g => pureOk g.2.2.1 g.2.2.2 ((vtPre.drop g.1).take (g.2.1 - g.1))) = true := by
  decide +kernel

theorem vt_c_gap {C : CallRel} {rd : Reader} {a b lo hi : ℕ} (hg : (a, b, lo, hi) ∈ vtGaps) (σ : Val) :
    Completes C rd lo hi ((vtPre.drop a).take (b - a)) σ (fun _ => True) :=
  completes_pure (List.all_eq_true.mp vtGaps_ok _ hg) σ

/-! ## `block_index_mle` -/

def vtItBim : List FItem :=
  [.hint (.alloc (.n 1852) 102), .atom (.const (.n 1853) (word 1 0 0)), .atom (.add (.n 1854) (.n 12) (.n 1853))]

theorem vtItBim_eq : vtItBim.flatMap FItem.stmts = (vtPre.drop 1574).take 3 := stmtsEqb_sound (by decide +kernel)

theorem vtItBim_ok : fOkI 1852 1855 [] vtItBim = true := by decide +kernel

theorem vtItBim_obs : iObs 1852 [] vtItBim = [] := listEqb_sound iobEqb_sound (by decide +kernel)

theorem vtItBim_eqB : (fEqs 1852 [] vtItBim).any (feqEqb (.item (.hint (.alloc (.n 1852) 102)))) = true := by
  decide +kernel

/-- **`block_index_mle` is hinted** at `p`. -/
theorem vt_c_bim {rd : Reader} {σ : Val} (p : E) :
    Completes (coreProgram.Rel rd) rd 1852 1855 ((vtPre.drop 1574).take 3) σ (fun σ' => σ' (.n 1852) = p) := by
  rw [← vtItBim_eq]
  set hv : ℕ → E := fun _ => p
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) hv vtItBim vtItBim_ok σ
  generalize hσf : fRunI rd 1852 hv [] σ vtItBim = σf at Cm
  have hf : ∀ v, fRunI rd 1852 hv [] σ vtItBim v = σf v := fun v => by rw [hσf]
  have E := fRunI_eqs rd hv σf vtItBim [] σ vtItBim_ok hf
  have qp := E _ (mem_of_any feqEqb_sound vtItBim_eqB) 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
  simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons, List.map_nil] at qp
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [vtItBim_obs]; intro o ho; simp at ho
  · intro σ' h; rw [h]; exact qp

/-! ## The first table's `g^τ` -/

theorem vtTau_eq : [FItem.atom (.load (.n 4660) (.n 7) 1)].flatMap FItem.stmts = (vtPre.drop 4374).take 1 :=
  stmtsEqb_sound (by decide +kernel)

theorem vtTau_ok : fOkI 4660 4661 [] [FItem.atom (.load (.n 4660) (.n 7) 1)] = true := by decide +kernel

theorem vtTau_obs : iObs 4660 [] [FItem.atom (.load (.n 4660) (.n 7) 1)] = [.ob (.ld (.n 7) 1)] :=
  listEqb_sound iobEqb_sound (by decide +kernel)

theorem vtTau_eqB : (fEqs 4660 [] [FItem.atom (.load (.n 4660) (.n 7) 1)]).any (feqEqb (.ld (.n 4660) (.n 7) 1)) = true := by
  decide +kernel

/-- **The first table's `g^τ`** is read from `dims`. -/
theorem vt_c_tau {rd : Reader} {σ : Val} {dims g : E} (h7 : σ (.n 7) = dims) (hd : LoadHolds rd dims 1 g) :
    Completes (coreProgram.Rel rd) rd 4660 4661 ((vtPre.drop 4374).take 1) σ (fun σ' => σ' (.n 4660) = g) := by
  rw [← vtTau_eq]
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) (fun _ => 0) _ vtTau_ok σ
  generalize hσf : fRunI rd 4660 (fun _ => 0) [] σ [FItem.atom (.load (.n 4660) (.n 7) 1)] = σf at Cm
  have hf : ∀ v, fRunI rd 4660 (fun _ => 0) [] σ [FItem.atom (.load (.n 4660) (.n 7) 1)] v = σf v :=
    fun v => by rw [hσf]
  have E := fRunI_eqs rd (fun _ => 0) σf _ [] σ vtTau_ok hf
  have FR : σf (.n 7) = σ (.n 7) := fRunI_eq_of_def rd (fun _ => 0) vtTau_ok hf (by simp [fDef, vNum])
  have e := E _ (mem_of_any feqEqb_sound vtTau_eqB)
  simp only [FEq.Holds] at e
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [vtTau_obs]; intro o ho
    simp only [List.mem_singleton] at ho; subst ho
    show IsInK (σf (.n 7)) ∧ _
    rw [FR, h7]; exact ⟨hd.1, isSome_of_loadHolds hd⟩
  · intro σ' h; rw [h, e, FR, h7]; exact memAt_of_loadHolds hd

end
end LeanVM.Guest.B1.VerifySub
