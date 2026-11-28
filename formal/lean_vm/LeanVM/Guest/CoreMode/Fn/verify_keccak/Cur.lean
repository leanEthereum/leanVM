/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.Cur

  `verify_keccak`'s returned cursor, from its relation: `cursor·tau_g^24·g^1034`, so `24(h - 3) + 1106` words past its
  cursor at `tau_g = g^h` (`vk_retCur`), from each `keccak_layer` call's `cursor·step_g^32·rem_g^2·g^84`
  (`klRel_cur`) and `keccak_plain_rounds`' `cursor·g^(2n)`.
-/

module

public import LeanVM.Guest.CoreMode.Fn.keccak_layer.SoundA
public import LeanVM.Guest.B1.Whir.Flat
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.KeccakGkr.Plain
public meta import LeanVM.Guest.CoreRef

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.Value (gen_pow_eq_ofK)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## Flat bodies, by their atoms and calls -/

/-- A block's last statement's words, when it is a `ret`. -/
def retOf (ss : List Stmt) : Option (List V) :=
  ss.getLast?.bind fun
    | .ret vs => some vs
    | _ => none

/-- A block's atoms. -/
def atomsOf (ss : List Stmt) : List Atom :=
  ss.filterMap fun
    | .atom a => some a
    | _ => none

/-- A block's calls. -/
def callsOf (ss : List Stmt) : List (String × List V × List V) :=
  ss.filterMap fun
    | .call f args rets => some (f, args, rets)
    | _ => none

end

public section

/-- **A flat block ending in a `ret`** holds: every statement before it, and the returns are its words. -/
theorem flat_ret {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt} {vs : List V} {kret : List E → Prop}
    (hl : retOf ss = some vs) (hf : ss.dropLast.all B1.Whir.Stmt.flat = true)
    (h : Stmt.HoldsList C rd σ ss False kret) : B1.Whir.AllOk C rd σ ss.dropLast ∧ kret (vs.map σ) := by
  have e : ss = ss.dropLast ++ [.ret vs] := by
    unfold retOf at hl
    cases hg : ss.getLast? with
    | none => rw [hg] at hl; cases hl
    | some s =>
      rw [hg] at hl
      cases s <;> simp only [Option.bind_some, reduceCtorEq] at hl
      cases hl
      exact (List.dropLast_append_getLast? _ hg).symm
  rw [e] at h
  exact (B1.Whir.holdsList_flat_ret _ hf vs kret).1 h

theorem atom_of {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt} (h : B1.Whir.AllOk C rd σ ss) {a : Atom}
    (ha : a ∈ atomsOf ss) : a.Holds rd σ := by
  obtain ⟨s, hs, e⟩ := List.mem_filterMap.mp ha
  cases s <;> simp at e
  subst e
  exact h _ hs

theorem call_of {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt} (h : B1.Whir.AllOk C rd σ ss) {f : String}
    {args rets : List V} (hc : (f, args, rets) ∈ callsOf ss) : C f (args.map σ) (rets.map σ) := by
  obtain ⟨s, hs, e⟩ := List.mem_filterMap.mp hc
  cases s <;> simp at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  exact h _ hs

/-! ## `keccak_layer` -/

set_option maxHeartbeats 4000000 in
/-- **`keccak_layer`'s dispatches' cursor** on a run of its body: the dispatch on `rem_g` returns
`cursor·step_g^32·rem_g^2·g^48` (`packT_holds`, `lrCall_cur`; `kl_retCur`'s argument). -/
theorem klBody_cur {rd : Reader} {σ : Val} {first : ℕ} (hf : first < 2) {next : Prop} {kret : List E → Prop}
    (hb : Stmt.HoldsList (coreProgram.Rel rd) rd σ (layerT first) next kret) :
    σ (.n (preOff first + 803)) = σ (.n 7) * σ (.n 9) ^ 32 * σ (.n 10) ^ 2 * gen ^ 48 := by
  rw [layerT] at hb
  rw [holdsList_append, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append, holdsList_append, holdsList_append] at hb
  replace hb := ((holdsList_atoms (allAtoms_of_all (by interval_cases first <;> decide +kernel)) _ _).1 hb).2
  replace hb := ((holdsList_atoms (allAtoms_of_all (rmfeBlock_atoms _)) _ _).1 hb).2
  replace hb := ((holdsList_atoms (allAtoms_of_all (by interval_cases first <;> decide +kernel)) _ _).1 hb).2
  obtain ⟨-, ⟨j1, hj1, hsg, hc1⟩, ⟨j2, hj2, hrg, hc2⟩, -, -⟩ := packT_holds hb
  generalize preOff first = o at hc1 hc2 ⊢
  have hn1 : stepNames.getD j1 "" = lrNames.getD (16 * j1) "" := by interval_cases j1 <;> rfl
  have hn2 : remNames.getD j2 "" = lrNames.getD j2 "" := by interval_cases j2 <;> rfl
  rw [hn1] at hc1
  have e1 := lrCall_cur (by omega) (by simp [cap5]) hc1
  rw [hn2] at hc2
  have e2 := lrCall_cur (by omega) (by simp) hc2
  simp only [cap5, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_succ,
    List.getD_cons_zero] at e1
  rw [List.getD_append _ _ _ _ (by simp), show (List.range 7).map (fun k ↦ σ (.n (o + 785 + k))) =
    [σ (.n (o + 785 + 0)), σ (.n (o + 785 + 1)), σ (.n (o + 785 + 2)), σ (.n (o + 785 + 3)), σ (.n (o + 785 + 4)),
      σ (.n (o + 785 + 5)), σ (.n (o + 785 + 6))] from rfl] at e2
  simp only [List.getD_cons_succ, List.getD_cons_zero] at e2
  rw [show o + 785 + 5 = o + 790 by omega] at e1 e2
  rw [show o + 798 + 5 = o + 803 by omega] at e2
  have hs : σ (.n 9) ^ 32 = gen ^ (2 * (16 * j1)) := by rw [hsg, ← pow_mul]; ring_nf
  have hr : σ (.n 10) ^ 2 = gen ^ (2 * j2) := by rw [hrg, ← pow_mul]; ring_nf
  rw [e2, e1, hs, hr]; ring

theorem word_g36 : word 68719476736 0 = gen ^ 36 := by
  rw [show (68719476736 : ℕ) = 2 ^ 36 by norm_num]; exact word_two_pow (by norm_num)

/-- **A `keccak_layer` call's returned cursor**: its cursor argument times `step_g^32·rem_g^2·g^84` (arguments
`7`, `9`, `10`). -/
theorem klRel_cur {rd : Reader} {first : ℕ} (hf : first < 2) {args rets : List E}
    (h : coreProgram.Rel rd (layerName first) args rets) :
    rets.getD 5 0 = args.getD 7 0 * args.getD 9 0 ^ 32 * args.getD 10 0 ^ 2 * gen ^ 84 := by
  interval_cases first
  · obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_layer265 args rets).mp h
    rw [show (fn% «keccak_layer__L0»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
      .n 11, .n 12, .n 13, .n 14] from rfl] at hpar
    subst hpar
    have hc : σ (.n 803) = σ (.n 7) * σ (.n 9) ^ 32 * σ (.n 10) ^ 2 * gen ^ 48 :=
      klBody_cur (first := 0) (by decide) (by rw [← layer_body265]; exact hb)
    obtain ⟨hok, rfl⟩ := flat_ret (vs := [.n 2208, .n 2209, .n 2210, .n 2211, .n 2212, .n 2215])
      (by decide +kernel) (by decide +kernel) hb
    have a1 := atom_of hok (a := .const (.n 2213) (word 68719476736 0)) (by decide +kernel)
    have a2 := atom_of hok (a := .mul (.n 2214) (.n 803) (.n 2213)) (by decide +kernel)
    have a3 := atom_of hok (a := .copy (.n 2215) (.n 2214)) (by decide +kernel)
    simp only [Atom.Holds] at a1 a2 a3
    simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]
    rw [a3, a2, a1, word_g36, hc]
    ring
  · obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_layer264 args rets).mp h
    rw [show (fn% «keccak_layer__L1»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
      .n 11, .n 12, .n 13, .n 14] from rfl] at hpar
    subst hpar
    have hc : σ (.n 823) = σ (.n 7) * σ (.n 9) ^ 32 * σ (.n 10) ^ 2 * gen ^ 48 :=
      klBody_cur (first := 1) (by decide) (by rw [← layer_body264]; exact hb)
    obtain ⟨hok, rfl⟩ := flat_ret (vs := [.n 1879, .n 1880, .n 1881, .n 1882, .n 1883, .n 1886])
      (by decide +kernel) (by decide +kernel) hb
    have a1 := atom_of hok (a := .const (.n 1884) (word 68719476736 0)) (by decide +kernel)
    have a2 := atom_of hok (a := .mul (.n 1885) (.n 823) (.n 1884)) (by decide +kernel)
    have a3 := atom_of hok (a := .copy (.n 1886) (.n 1885)) (by decide +kernel)
    simp only [Atom.Holds] at a1 a2 a3
    simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]
    rw [a3, a2, a1, word_g36, hc]
    ring

/-! ## `keccak_plain_rounds` -/

/-- **A `keccak_plain_rounds` call's returned cursor**: its cursor argument times `g^(2n)`. -/
theorem getD5 {A : List E} {c d : E} (h : (A ++ [c, d]).length = 7) : (A ++ [c, d]).getD 5 0 = c := by
  simp only [List.length_append, List.length_cons, List.length_nil] at h
  rw [List.getD_append_right _ _ _ _ (by omega), show 5 - A.length = 0 by omega]
  rfl

theorem plain_cur {rd : Reader} {n k0 : ℕ} {f0 f1 f2 f3 f4 p0 p1 cur value point tabs : E} {rets : List E}
    (hm : MeaningPlainRounds n k0 rd [f0, f1, f2, f3, f4, p0, p1, cur, value, point, tabs] rets)
    (hw : ∃ w : E, k0 = 1 → (p0, p1) = Value.Keccak.scalarCells w LeanVM.Protocol.Compile.dsObserve)
    (hr : rets.length = 7) : rets.getD 5 0 = cur * gen ^ (2 * n) := by
  simp only [MeaningPlainRounds] at hm
  obtain ⟨rounds, -, -, H⟩ := hm
  obtain ⟨w, hw⟩ := hw
  obtain ⟨-, rfl⟩ := H w hw
  exact getD5 hr

/-! ## `verify_keccak` -/

theorem find_vkC : coreProgram.find? "verify_keccak" = some fn% «verify_keccak» := B1.VerifySub.find_vk

set_option maxHeartbeats 8000000 in
/-- **`verify_keccak`'s returned cursor** (return `5`): its cursor argument (`5`) times `tau_g^24·g^1034` (`tau_g`
argument `6`), as `·g^72` on both sides. -/
theorem vk_retCur {rd : Reader} {args rets : List E} (h : coreProgram.Rel rd "verify_keccak" args rets) :
    rets.getD 5 0 * gen ^ 72 = args.getD 5 0 * args.getD 6 0 ^ 24 * gen ^ 1106 := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_vkC args rets).mp h
  rw [show (fn% «verify_keccak»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
    .n 11] from rfl] at hpar
  subst hpar
  obtain ⟨hok, rfl⟩ := flat_ret (vs := [.n 3359, .n 3360, .n 3361, .n 3362, .n 3363, .n 3366, .n 3367])
    (by decide +kernel) (by decide +kernel) hb
  have a17 := atom_of hok (a := .const (.n 17) (word 8070450532247928836 0)) (by decide +kernel)
  have a18 := atom_of hok (a := .mul (.n 18) (.n 6) (.n 17)) (by decide +kernel)
  have a49 := atom_of hok (a := .mul (.n 49) (.n 29) (.n 29)) (by decide +kernel)
  have a50 := atom_of hok (a := .mul (.n 50) (.n 49) (.n 49)) (by decide +kernel)
  have a51 := atom_of hok (a := .mul (.n 51) (.n 50) (.n 50)) (by decide +kernel)
  have a52 := atom_of hok (a := .mul (.n 52) (.n 51) (.n 51)) (by decide +kernel)
  have a53 := atom_of hok (a := .mul (.n 53) (.n 52) (.n 48)) (by decide +kernel)
  have a54 := atom_of hok (a := .const (.n 54) (word 2 0)) (by decide +kernel)
  have a55 := atom_of hok (a := .mul (.n 55) (.n 18) (.n 54)) (by decide +kernel)
  have a5355 := atom_of hok (a := .assertEq (.n 53) (.n 55)) (by decide +kernel)
  have a472 := atom_of hok (a := .const (.n 472) (word 2 0)) (by decide +kernel)
  have a473 := atom_of hok (a := .mul (.n 473) (.n 5) (.n 472)) (by decide +kernel)
  have a927 := atom_of hok (a := .copy (.n 927) (.n 926)) (by decide +kernel)
  have a928 := atom_of hok (a := .const (.n 928) (word 0 1)) (by decide +kernel)
  have a1193 := atom_of hok (a := .const (.n 1193) (word 2 0)) (by decide +kernel)
  have a1194 := atom_of hok (a := .mul (.n 1194) (.n 924) (.n 1193)) (by decide +kernel)
  have a3364 := atom_of hok (a := .const (.n 3364) (word 27 0)) (by decide +kernel)
  have a3365 := atom_of hok (a := .mul (.n 3365) (.n 1333) (.n 3364)) (by decide +kernel)
  have a3366 := atom_of hok (a := .copy (.n 3366) (.n 3365)) (by decide +kernel)
  simp only [Atom.Holds] at a17 a18 a49 a50 a51 a52 a53 a54 a55 a5355 a472 a473 a927 a928 a1193 a1194 a3364 a3365 a3366
  -- `step_g^16·rem_g·g^3 = tau_g`, so a layer's `step_g^32·rem_g^2·g^6 = tau_g^2`
  have e1 : σ (.n 29) ^ 16 * σ (.n 48) = σ (.n 6) * σ (.n 17) * gen := by
    calc σ (.n 29) ^ 16 * σ (.n 48) = σ (.n 53) := by rw [a53, a52, a51, a50, a49]; ring
      _ = σ (.n 55) := eq_of_add_eq_zero' a5355
      _ = _ := by rw [a55, a18, a54, word_gen]
  have hA : σ (.n 29) ^ 32 * σ (.n 48) ^ 2 * gen ^ 6 = σ (.n 6) ^ 2 := by
    calc σ (.n 29) ^ 32 * σ (.n 48) ^ 2 * gen ^ 6 = (σ (.n 29) ^ 16 * σ (.n 48)) ^ 2 * gen ^ 6 := by ring
      _ = (σ (.n 6) * (σ (.n 17) * gen ^ 4)) ^ 2 := by rw [e1]; ring
      _ = σ (.n 6) ^ 2 := by rw [a17, word_ginv4_mul]; ring
  -- the calls, in order
  have c0 := klRel_cur (first := 1) (by decide)
    (call_of hok (f := "keccak_layer__L1")
      (args := [.n 148, .n 149, .n 150, .n 151, .n 152, .n 154, .n 155, .n 473, .n 475, .n 29, .n 48, .n 156, .n 477, .n 471, .n 11])
      (rets := [.n 478, .n 479, .n 480, .n 481, .n 482, .n 483]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c0
  have c1 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 478, .n 479, .n 480, .n 481, .n 482, .n 505, .n 506, .n 483, .n 508, .n 29, .n 48, .n 510, .n 512, .n 504, .n 11])
      (rets := [.n 513, .n 514, .n 515, .n 516, .n 517, .n 518]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c1
  have c2 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 513, .n 514, .n 515, .n 516, .n 517, .n 539, .n 540, .n 518, .n 542, .n 29, .n 48, .n 544, .n 546, .n 538, .n 11])
      (rets := [.n 547, .n 548, .n 549, .n 550, .n 551, .n 552]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c2
  have c3 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 547, .n 548, .n 549, .n 550, .n 551, .n 582, .n 583, .n 552, .n 585, .n 29, .n 48, .n 587, .n 589, .n 581, .n 11])
      (rets := [.n 590, .n 591, .n 592, .n 593, .n 594, .n 595]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c3
  have c4 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 590, .n 591, .n 592, .n 593, .n 594, .n 623, .n 624, .n 595, .n 626, .n 29, .n 48, .n 628, .n 630, .n 622, .n 11])
      (rets := [.n 631, .n 632, .n 633, .n 634, .n 635, .n 636]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c4
  have c5 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 631, .n 632, .n 633, .n 634, .n 635, .n 666, .n 667, .n 636, .n 669, .n 29, .n 48, .n 671, .n 673, .n 665, .n 11])
      (rets := [.n 674, .n 675, .n 676, .n 677, .n 678, .n 679]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c5
  have c6 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 674, .n 675, .n 676, .n 677, .n 678, .n 699, .n 700, .n 679, .n 702, .n 29, .n 48, .n 704, .n 706, .n 698, .n 11])
      (rets := [.n 707, .n 708, .n 709, .n 710, .n 711, .n 712]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c6
  have c7 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 707, .n 708, .n 709, .n 710, .n 711, .n 740, .n 741, .n 712, .n 743, .n 29, .n 48, .n 745, .n 747, .n 739, .n 11])
      (rets := [.n 748, .n 749, .n 750, .n 751, .n 752, .n 753]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c7
  have c8 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 748, .n 749, .n 750, .n 751, .n 752, .n 778, .n 779, .n 753, .n 781, .n 29, .n 48, .n 783, .n 785, .n 777, .n 11])
      (rets := [.n 786, .n 787, .n 788, .n 789, .n 790, .n 791]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c8
  have c9 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 786, .n 787, .n 788, .n 789, .n 790, .n 821, .n 822, .n 791, .n 824, .n 29, .n 48, .n 826, .n 828, .n 820, .n 11])
      (rets := [.n 829, .n 830, .n 831, .n 832, .n 833, .n 834]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c9
  have c10 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 829, .n 830, .n 831, .n 832, .n 833, .n 862, .n 863, .n 834, .n 865, .n 29, .n 48, .n 867, .n 869, .n 861, .n 11])
      (rets := [.n 870, .n 871, .n 872, .n 873, .n 874, .n 875]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c10
  have c11 := klRel_cur (first := 0) (by decide)
    (call_of hok (f := "keccak_layer__L0")
      (args := [.n 870, .n 871, .n 872, .n 873, .n 874, .n 902, .n 903, .n 875, .n 905, .n 29, .n 48, .n 907, .n 909, .n 901, .n 11])
      (rets := [.n 910, .n 911, .n 912, .n 913, .n 914, .n 915]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at c11
  have c12 := plain60_sound rd _ _
    (call_of hok (f := "keccak_plain_rounds__L6_L0")
      (args := [.n 910, .n 911, .n 912, .n 913, .n 914, .n 917, .n 918, .n 915, .n 153, .n 916, .n 11])
      (rets := [.n 919, .n 920, .n 921, .n 922, .n 923, .n 924, .n 925]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil] at c12
  replace c12 := plain_cur c12 ⟨0, fun h ↦ absurd h (by decide)⟩ rfl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at c12
  have c13 := plain41_sound rd _ _
    (call_of hok (f := "keccak_plain_rounds__L4_L1")
      (args := [.n 919, .n 920, .n 921, .n 922, .n 923, .n 927, .n 928, .n 1194, .n 1195, .n 1197, .n 11])
      (rets := [.n 1198, .n 1199, .n 1200, .n 1201, .n 1202, .n 1203, .n 1204]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil] at c13
  replace c13 := plain_cur c13 ⟨σ (.n 926), fun _ ↦ by rw [a927, a928]; rfl⟩ rfl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at c13
  have c14 := plain60_sound rd _ _
    (call_of hok (f := "keccak_plain_rounds__L6_L0")
      (args := [.n 1198, .n 1199, .n 1200, .n 1201, .n 1202, .n 1326, .n 1327, .n 1203, .n 1204, .n 1325, .n 11])
      (rets := [.n 1328, .n 1329, .n 1330, .n 1331, .n 1332, .n 1333, .n 1334]) (by decide +kernel))
  simp only [List.map_cons, List.map_nil] at c14
  replace c14 := plain_cur c14 ⟨0, fun h ↦ absurd h (by decide)⟩ rfl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at c14
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]
  rw [a3366, a3365, a3364, c14, c13, a1194, a1193, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0, a473, a472, word_g64, word_gen,
    show σ (.n 6) ^ 24 = (σ (.n 6) ^ 2) ^ 12 by ring, ← hA]
  ring

end

end LeanVM.Guest.EndExec
