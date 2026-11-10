/-
  LeanVM.Guest.B1.Da.ExpAt

  `da_expand` placed (G:4454-4467): its product tree in its frame run, the run returned at its
  leaves, within its frame, by its evaluated valuation.
-/

module

public import LeanVM.Guest.B1.Da.ExpCChk
public import LeanVM.Guest.B1.Da.ExpandChk
public import LeanVM.Guest.B1.Da.HonestDefs
public import LeanVM.Guest.B1.Da.VecFn
public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Memory.LiftPure

/-!
# `da_expand`, placed

The computing atoms are evaluated (`Fwd.ev`) from the four arguments; the run's pointer is the run
at `rb = fp + cert f (.n (expB D + 1))`, its fresh words zero, then the leaves' pointer
`g^(rb + 2^D)`. Node `2^d + y` is `expandLeaf … d y` (`exp_node`), which the run's words hold
(`expRunVals`, `expRun_get`), so the `frameAddr` holds. `exp_completeAtB`: complete, placed, within
its frame, returning the run at its leaves (`expOut`); `exp7_completeAtB`,
`exp8_completeAtB`: the two specializations.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB DisjL Within)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

theorem nodesBelow_get : ∀ (D : ℕ) {d y : ℕ}, d < D → y < 2 ^ d →
    (nodesBelow D)[2 ^ d - 1 + y]? = some (.n (nodeAt d y))
  | 0, _, _, hd, _ => absurd hd (by omega)
  | D + 1, d, y, hd, hy => by
    have hsplit : nodesBelow (D + 1) = nodesBelow D ++ (List.range (2 ^ D)).map (V.n ∘ nodeAt D) := by
      rw [nodesBelow, List.range_succ, List.flatMap_append, ← nodesBelow]
      simp
    rw [hsplit]
    have h1 := length_nodesBelow D
    have hp := Nat.one_le_two_pow (n := d)
    rcases Nat.lt_or_ge d D with h | h
    · have h2 : 2 ^ (d + 1) ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ] at h2
      rw [List.getElem?_append_left (by omega)]
      exact nodesBelow_get D h hy
    · obtain rfl : d = D := by omega
      rw [List.getElem?_append_right (by omega), show 2 ^ d - 1 + y - (nodesBelow d).length = y by
        omega]
      simp [hy]

/-- **The run's words**: a fresh word, node `k` at word `k`, fresh words. -/
theorem expRun_get {D k : ℕ} (hD : D ≤ 8) (hk : k < 512) :
    (expRun D)[k]? = some (if k = 0 then .n (expB D + 1) else if k < 2 ^ (D + 1) then
      .n (nodeAt (Nat.log 2 k) (k - 2 ^ Nat.log 2 k)) else .n (expB D + 2 + (k - 2 ^ (D + 1)))) := by
  have h9 : 2 ^ (D + 1) ≤ 512 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num : 2 ^ 9 ≤ 512)
  have hl := length_nodesBelow (D + 1)
  have hp := Nat.one_le_two_pow (n := D + 1)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [expRun]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [expRun, List.cons_append, List.getElem?_cons_succ, ite_neg' (by omega)]
    by_cases hkD : j + 1 < 2 ^ (D + 1)
    · rw [ite_pos' hkD, List.getElem?_append_left (by omega)]
      have hlog : Nat.log 2 (j + 1) < D + 1 := Nat.log_lt_of_lt_pow (by omega) hkD
      have hy : j + 1 - 2 ^ Nat.log 2 (j + 1) < 2 ^ Nat.log 2 (j + 1) := by
        have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (j + 1)
        rw [pow_succ] at h1
        omega
      have hk' := Nat.pow_log_le_self 2 (show j + 1 ≠ 0 by omega)
      have e : j = 2 ^ Nat.log 2 (j + 1) - 1 + (j + 1 - 2 ^ Nat.log 2 (j + 1)) := by omega
      have := nodesBelow_get (D + 1) hlog hy
      rw [← e] at this
      exact this
    · rw [ite_neg' hkD, List.getElem?_append_right (by omega),
        show j - (nodesBelow (D + 1)).length = j + 1 - 2 ^ (D + 1) by omega]
      simp only [List.getElem?_map, List.getElem?_range (show j + 1 - 2 ^ (D + 1) < 512 - 2 ^ (D + 1) by
        omega), Option.map_some]

/-- The loads of `da_expand`'s computing atoms: a power, a shift, a node's factor. -/
theorem expBodyA_load {top D : ℕ} {d' p : V} {off : ℕ} (h : Atom.load d' p off ∈ expBodyA top D) :
    (∃ d < D, p = .n 2 ∧ off = top - d) ∨ (∃ d < D, p = .n 3 ∧ off = top - d) ∨
      ∃ d < D, ∃ y < 2 ^ d, p = .n 1 ∧ off = 2 ^ d + y := by
  simp only [expBodyA, expDepthA, expNodeA, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false, reduceCtorEq, false_or, Atom.load.injEq] at h
  rcases h with ⟨d, hd, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨y, hy, ⟨-, rfl, rfl⟩⟩⟩
  · exact Or.inl ⟨d, hd, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨d, hd, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨d, hd, y, hy, rfl, rfl⟩)

theorem expRunVals_get {root : E} {F Z S : ℕ → E} {top D k : ℕ} (hk : k < 512) :
    (expRunVals root F Z S top D)[k]'(by simp [expRunVals]; exact hk) =
      if 1 ≤ k ∧ k < 2 ^ (D + 1) then expandLeaf root F Z S top (Nat.log 2 k) (k - 2 ^ Nat.log 2 k)
      else 0 := by
  simp [expRunVals]

theorem tl_mid (x a b : E) {m j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ m) :
    (x :: (List.replicate m 0 ++ [a, b])).getD j 0 = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  simp [show i < m by omega]

theorem tl_a (x a b : E) (m : ℕ) : (x :: (List.replicate m 0 ++ [a, b])).getD (m + 1) 0 = a := by
  rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem tl_b (x a b : E) (m : ℕ) : (x :: (List.replicate m 0 ++ [a, b])).getD (m + 2) 0 = b := by
  rw [show m + 2 = (m + 1) + 1 from rfl, List.getD_cons_succ, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 4000 in
/-- **`da_expand` is complete, placed, within its frame**, its tree in its frame run, returned at
its leaves, the factors `F`, powers `Z` and shifts `S` read at `g^cf`, `g^cz`, `g^cs`. -/
theorem exp_completeAtB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) {top D W : ℕ} (hok : expOk fn top D W = true)
    (hcok : expCOk top D W = true) (hD : D ≤ 8) (hDt : D ≤ top + 1)
    (hfit : cert f (.n (expB D + 1)) + 512 ≤ fs f) {Lin : Layout} {root : E} {cf cz cs : ℕ}
    {F Z S : ℕ → E}
    (hF : ∀ rd, MemL rd Lin → ∀ n, 1 ≤ n → n < 2 ^ D → LoadHolds rd (gen ^ cf) n (F n))
    (hZ : ∀ rd, MemL rd Lin → ∀ d < D, LoadHolds rd (gen ^ cz) (top - d) (Z (top - d)))
    (hS : ∀ rd, MemL rd Lin → ∀ d < D, LoadHolds rd (gen ^ cs) (top - d) (S (top - d)))
    (hFr : ∀ n, 1 ≤ n → n < 2 ^ D → RegionL Lin (cf + n))
    (hZr : ∀ d < D, RegionL Lin (cz + (top - d))) (hSr : ∀ d < D, RegionL Lin (cs + (top - d))) :
    CompleteAtDTB fs cert 16 f Lin [root, gen ^ cf, gen ^ cz, gen ^ cs]
      (expOut root F Z S top D) (fun _ => True) (fs f) := by
  have h9 : 2 ^ (D + 1) ≤ 512 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num : 2 ^ 9 ≤ 512)
  unfold expOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hparams, hW⟩, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨rfl, htm⟩ := hok
    have hA := atomsEqb_sound htm
    subst hA
    have hb := splitBody_eq hsp
    unfold expCOk at hcok
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hcok
    obtain ⟨⟨⟨⟨⟨⟨⟨hchk, hst⟩⟩, hside⟩, hvals⟩, hna⟩, haddr⟩, hrun⟩ := hcok
    intro fp
    set rb := fp + cert f (.n (expB D + 1)) with hrb
    have hlenR : (expRunVals root F Z S top D).length = 512 := by simp [expRunVals]
    refine ⟨fs f, [], [gen ^ (rb + 2 ^ D)], [(rb, expRunVals root F Z S top D)], le_rfl,
      ⟨rb, rfl, List.mem_singleton_self _⟩, ?_, List.pairwise_singleton _ _,
      fun rd _ hm => RelAtIn.relAtInT ?_⟩
    · intro q hq
      simp only [List.append_nil, List.mem_singleton] at hq
      subst hq
      rw [hlenR]
      omega
    simp only [List.append_nil] at hm
    obtain ⟨hmo, hLin⟩ := Main.memL_append.mp hm
    have hrunR : ReadsAt rd (gen ^ rb) (expRunVals root F Z S top D) :=
      reads_of_memL hmo (List.mem_singleton_self _)
    -- the valuation
    let w : ℕ → E := fun _ => 0
    have hchk' : chk [root, gen ^ cf, gen ^ cz, gen ^ cs].length
        ((expBodyA top D).map Stmt.atom) = some (expB D) := hchk
    obtain ⟨hlen, -, hgs⟩ := ev_spec rd w _ _ hchk'
    rw [show [root, gen ^ cf, gen ^ cz, gen ^ cs].length = 4 from rfl, hst] at hgs
    set evl := ev rd w [root, gen ^ cf, gen ^ cz, gen ^ cs] ((expBodyA top D).map Stmt.atom)
      with hevl
    set rbE : E := ofK (addressOfIndex rb) with hrbE
    set tl : List E := rbE :: (List.replicate (expC D - expB D - 1) 0 ++
      [word W 0, rbE * word W 0]) with htl
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (evl ++ tl) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    have hag : ∀ v : V, v.idx < expB D → B1.Val.ofArgs evl v = σ v := fun v hv => by
      rw [hσ]; exact (ofArgs_old (by rw [hlen]; exact hv)).symm
    have hg : ∀ a ∈ expBodyA top D, Good rd [] w σ a := fun a ha =>
      good_congr (fun v hv => hag v (by
        have := List.all_eq_true.mp (List.all_eq_true.mp hvals a ha) v hv
        simpa using this)) (hgs (.atom a) (List.mem_map_of_mem ha))
    have hpar : ∀ i < 4, σ (.n i) = [root, gen ^ cf, gen ^ cz, gen ^ cs].getD i 0 := by
      intro i hi
      have hB : 4 ≤ expB D := by unfold expB; omega
      rw [← hag _ (by show i < expB D; omega), hevl]
      exact ev_params rd w hchk' (by simpa using hi)
    have e0 : σ (.n 0) = root := hpar 0 (by norm_num)
    have e1 : σ (.n 1) = gen ^ cf := hpar 1 (by norm_num)
    have e2 : σ (.n 2) = gen ^ cz := hpar 2 (by norm_num)
    have e3 : σ (.n 3) = gen ^ cs := hpar 3 (by norm_num)
    have htl_at : ∀ j, σ (.n (expB D + j)) = tl.getD j 0 := fun j => by
      rw [hσ, ← hlen]; exact ofArgs_new evl tl j
    have hmC : expC D - expB D - 1 = 1 + (512 - 2 ^ (D + 1)) := by unfold expC; omega
    -- the computing atoms
    have hatB : ∀ a ∈ expBodyA top D, a.Holds rd σ := by
      refine atoms_holds (A := []) hidx hcan hg (by simp) fun a ha hns => Or.inr ?_
      have hld := List.all_eq_true.mp hside a ha
      rw [hns] at hld
      cases a with
      | load d' p off =>
        simp only [Side, List.not_mem_nil, ↓reduceIte]
        rcases expBodyA_load ha with ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, y, hy, rfl, rfl⟩
        · rw [e2]; exact ⟨(hZ rd hLin d hd).1, by rw [(hZ rd hLin d hd).2]; rfl⟩
        · rw [e3]; exact ⟨(hS rd hLin d hd).1, by rw [(hS rd hLin d hd).2]; rfl⟩
        · have h1 : 1 ≤ 2 ^ d + y := by have := Nat.one_le_two_pow (n := d); omega
          have h2 : 2 ^ d + y < 2 ^ D := by
            calc 2 ^ d + y < 2 ^ d + 2 ^ d := by omega
              _ = 2 ^ (d + 1) := by rw [pow_succ]; ring
              _ ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) hd
          rw [e1]; exact ⟨(hF rd hLin _ h1 h2).1, by rw [(hF rd hLin _ h1 h2).2]; rfl⟩
      | _ => simp [atomLoad?] at hld
    -- the loaded words
    have hZv : ∀ d < D, σ (.n (expB d)) = Z (top - d) := by
      intro d hd
      have h := (exp_depth hd (Nat.two_pow_pos d) hatB).1
      rw [e2] at h
      have h' := hZ rd hLin d hd
      exact Option.some.inj (h.2.symm.trans h'.2)
    have hSv : ∀ d < D, σ (.n (expB d + 1)) = S (top - d) := by
      intro d hd
      have h := (exp_depth hd (Nat.two_pow_pos d) hatB).2.1
      rw [e3] at h
      have h' := hS rd hLin d hd
      exact Option.some.inj (h.2.symm.trans h'.2)
    have hFv : ∀ n, 1 ≤ n → n < 2 ^ D → memAt rd (σ (.n 1)) n = F n := by
      intro n h1 h2
      rw [e1, memAt, (hF rd hLin n h1 h2).2]
      rfl
    -- the nodes
    have hnode : ∀ d ≤ D, ∀ y < 2 ^ d, σ (.n (nodeAt d y)) = expandLeaf root F Z S top d y := by
      intro d hd y hy
      rw [exp_node hatB hDt d hd y hy, e0]
      refine expandLeaf_congr hy (fun n h1 h2 => hFv n h1 (lt_of_lt_of_le h2
        (Nat.pow_le_pow_right (by norm_num) hd))) (fun d' hd' => ?_) (fun d' hd' => ?_)
      · rw [show top - (top - d') = d' by omega]
        exact hZv d' (by omega)
      · rw [show top - (top - d') = d' by omega]
        exact hSv d' (by omega)
    -- the run
    have hrv : ∀ k < 512, σ ((expRun D)[k]?.getD (.n 0)) =
        (expRunVals root F Z S top D).getD k 0 := by
      intro k hk
      rw [expRun_get hD hk, Option.getD_some, List.getD_eq_getElem _ _ (by rw [hlenR]; exact hk),
        expRunVals_get hk]
      by_cases h0 : k = 0
      · subst h0
        rw [ite_pos' rfl, htl_at 1, htl, tl_mid _ _ _ le_rfl (by omega)]
        simp
      · rw [ite_neg' h0]
        by_cases hkD : k < 2 ^ (D + 1)
        · rw [ite_pos' hkD, ite_pos' ⟨by omega, hkD⟩]
          have hlog : Nat.log 2 k ≤ D := by
            have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hkD
            omega
          have hy : k - 2 ^ Nat.log 2 k < 2 ^ Nat.log 2 k := by
            have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) k
            rw [pow_succ] at h1
            omega
          exact hnode _ hlog _ hy
        · rw [ite_neg' hkD, ite_neg' (by omega), show expB D + 2 + (k - 2 ^ (D + 1)) =
            expB D + (1 + (1 + (k - 2 ^ (D + 1)))) by omega, htl_at, htl]
          have hjm : 1 + (1 + (k - 2 ^ (D + 1))) ≤ expC D - expB D - 1 := by
            rw [hmC]
            have h2 : 2 ^ (D + 1) ≤ k := by omega
            omega
          exact tl_mid rbE (word W 0) (rbE * word W 0) (by omega) hjm
    have hrunLen : (expRun D).length = 512 := by
      simp only [expRun, List.length_cons, List.length_append, List.length_map, List.length_range,
        length_nodesBelow]
      have := Nat.one_le_two_pow (n := D + 1)
      omega
    have hpE : σ (.n (expB D)) = rbE := by rw [← Nat.add_zero (expB D), htl_at 0]; rfl
    have hcE : σ (.n (expC D)) = word W 0 := by
      rw [show expC D = expB D + (expC D - expB D - 1 + 1) by unfold expC; omega, htl_at, htl,
        tl_a]
    have hmE : σ (.n (expC D + 1)) = rbE * word W 0 := by
      rw [show expC D + 1 = expB D + (expC D - expB D - 1 + 2) by unfold expC; omega, htl_at,
        htl, tl_b]
    have hWv : word W 0 = ofK (addressOfIndex (2 ^ D)) := by rw [word_eOfNat, eOfNat, hW]
    have hat : ∀ a ∈ expT top D W, a.Holds rd σ := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hatB a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · refine ⟨by rw [hpE]; exact ofK_isInK _, fun k hk w' hr => ?_⟩
        rw [hrunLen] at hk
        rw [hpE, hrbE, ← gen_pow_eq_ofK] at hr
        have hl := hrunR k (by rw [hlenR]; exact hk)
        have hw' : w' = (expRunVals root F Z S top D)[k]'(by rw [hlenR]; exact hk) :=
          Option.some.inj (hr.symm.trans hl.2)
        rw [hw', ← List.getD_eq_getElem _ 0, ← hrv k hk, List.getElem?_eq_getElem (by
          rw [hrunLen]; exact hk), Option.getD_some]
      · exact hcE
      · show σ (.n (expC D + 1)) = σ (.n (expB D)) * σ (.n (expC D))
        rw [hmE, hpE, hcE]
    refine relAtIn_atoms hf hb hl hna (by rw [hparams]; simp [e0, e1, e2, e3]) hat ?_ ?_ ?_ ?_
    · show [σ (.n (expC D + 1))] = [gen ^ (rb + 2 ^ D)]
      rw [hmE, hWv, hrbE, ← gen_pow_eq_ofK, ← gen_pow_eq_ofK, ← pow_add]
    · intro q hq
      rw [haddr, List.mem_singleton] at hq
      subst hq
      exact hpE
    · intro q hq
      obtain ⟨a, ha, hq⟩ := List.mem_filterMap.mp hq
      rcases List.mem_append.mp ha with ha | ha
      · cases a with
        | load d' p off =>
          simp only [atomLoad?, Option.some.injEq] at hq
          subst hq
          rcases expBodyA_load ha with ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, y, hy, rfl, rfl⟩
          · exact ⟨cz + (top - d), by rw [e2, limb0_gen_pow_mul], Or.inl (hZr d hd)⟩
          · exact ⟨cs + (top - d), by rw [e3, limb0_gen_pow_mul], Or.inl (hSr d hd)⟩
          · have h1 : 1 ≤ 2 ^ d + y := by have := Nat.one_le_two_pow (n := d); omega
            have h2 : 2 ^ d + y < 2 ^ D := by
              calc 2 ^ d + y < 2 ^ d + 2 ^ d := by omega
                _ = 2 ^ (d + 1) := by rw [pow_succ]; ring
                _ ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) hd
            exact ⟨cf + (2 ^ d + y), by rw [e1, limb0_gen_pow_mul], Or.inl (hFr _ h1 h2)⟩
        | _ => simp [atomLoad?] at hq
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> simp [atomLoad?] at hq
    · intro i hi
      obtain ⟨q, hq, h1, h2⟩ := hi
      rw [List.mem_singleton] at hq
      subst hq
      refine ⟨(.n (expB D + 1), 512), by rw [hrun]; exact List.mem_singleton_self _, ?_, ?_⟩
      · exact h1
      · simpa [hlenR] using h2
  · exact absurd hok (by simp)

theorem blockAtoms_atoms : ∀ (as : List Atom) (vs : List V),
    Lift.blockAtoms (as.map Stmt.atom ++ [.ret vs]) = as
  | [], _ => rfl
  | a :: as, vs => by
    rw [List.map_cons, List.cons_append, Lift.blockAtoms, blockAtoms_atoms as vs]
    rfl

/-- `da_expand`'s run fits its frame, when every run fits its frame. -/
theorem exp_fit {fs : String → ℕ} {cert : String → V → ℕ} (hrf : Lift.RunsFit fs cert)
    {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {top D W : ℕ}
    (hok : expOk fn top D W = true) (hD : D ≤ 8) : cert f (.n (expB D + 1)) + 512 ≤ fs f := by
  unfold expOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨-, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨rfl, htm⟩ := hok
    have hb := splitBody_eq hsp
    rw [atomsEqb_sound htm] at hb
    have hmem : Atom.frameAddr (.n (expB D)) (.n (expB D + 1) :: (nodesBelow (D + 1) ++
        (List.range (512 - 2 ^ (D + 1))).map fun i ↦ .n (expB D + 2 + i))) ∈
        Lift.blockAtoms fn.body := by
      rw [hb, blockAtoms_atoms]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    have h := hrf f fn hf _ _ _ hmem
    have h9 : 2 ^ (D + 1) ≤ 512 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num : 2 ^ 9 ≤ 512)
    have := Nat.one_le_two_pow (n := D + 1)
    simp only [List.length_append, List.length_map, List.length_range, length_nodesBelow] at h
    omega
  · exact absurd hok (by simp)

/-- **`da_expand__L14_L7`**, placed: the tree over the cell index (bits `14 … 8`). -/
theorem exp7_completeAtB (hrf : Lift.RunsFit fs cert) {Lin : Layout} {root : E} {cf cz cs : ℕ}
    {F Z S : ℕ → E}
    (hF : ∀ rd, MemL rd Lin → ∀ n, 1 ≤ n → n < 2 ^ 7 → LoadHolds rd (gen ^ cf) n (F n))
    (hZ : ∀ rd, MemL rd Lin → ∀ d < 7, LoadHolds rd (gen ^ cz) (14 - d) (Z (14 - d)))
    (hS : ∀ rd, MemL rd Lin → ∀ d < 7, LoadHolds rd (gen ^ cs) (14 - d) (S (14 - d)))
    (hFr : ∀ n, 1 ≤ n → n < 2 ^ 7 → RegionL Lin (cf + n))
    (hZr : ∀ d < 7, RegionL Lin (cz + (14 - d))) (hSr : ∀ d < 7, RegionL Lin (cs + (14 - d))) :
    CompleteAtDTB fs cert 16 "da_expand__L14_L7" Lin [root, gen ^ cf, gen ^ cz, gen ^ cs]
      (expOut root F Z S 14 7) (fun _ => True) (fs "da_expand__L14_L7") :=
  exp_completeAtB fs cert find_da_expand_L14_L7
    (by rw [Program.loop_of_find? find_da_expand_L14_L7]; decide +kernel) exp7_ok exp7_cok
    (by norm_num) (by norm_num) (exp_fit hrf find_da_expand_L14_L7 exp7_ok (by norm_num))
    hF hZ hS hFr hZr hSr

/-- **`da_expand__L7_L8`**, placed: the tree inside a cell (bits `7 … 0`). -/
theorem exp8_completeAtB (hrf : Lift.RunsFit fs cert) {Lin : Layout} {root : E} {cf cz cs : ℕ}
    {F Z S : ℕ → E}
    (hF : ∀ rd, MemL rd Lin → ∀ n, 1 ≤ n → n < 2 ^ 8 → LoadHolds rd (gen ^ cf) n (F n))
    (hZ : ∀ rd, MemL rd Lin → ∀ d < 8, LoadHolds rd (gen ^ cz) (7 - d) (Z (7 - d)))
    (hS : ∀ rd, MemL rd Lin → ∀ d < 8, LoadHolds rd (gen ^ cs) (7 - d) (S (7 - d)))
    (hFr : ∀ n, 1 ≤ n → n < 2 ^ 8 → RegionL Lin (cf + n))
    (hZr : ∀ d < 8, RegionL Lin (cz + (7 - d))) (hSr : ∀ d < 8, RegionL Lin (cs + (7 - d))) :
    CompleteAtDTB fs cert 16 "da_expand__L7_L8" Lin [root, gen ^ cf, gen ^ cz, gen ^ cs]
      (expOut root F Z S 7 8) (fun _ => True) (fs "da_expand__L7_L8") :=
  exp_completeAtB fs cert find_da_expand_L7_L8
    (by rw [Program.loop_of_find? find_da_expand_L7_L8]; decide +kernel) exp8_ok exp8_cok
    (by norm_num) (by norm_num) (exp_fit hrf find_da_expand_L7_L8 exp8_ok (by norm_num))
    hF hZ hS hFr hZr hSr

end
end LeanVM.Guest.B1.Da
