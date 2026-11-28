module

public import LeanVM.Guest.Complete.DaFacA
public import LeanVM.Guest.B1.VsC.QwA
public import LeanVM.Guest.B1.Da.ExpandChk
public import LeanVM.Guest.B1.Da.VecFn
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B2C.Table
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_expand__L»

/-!
# `da_expand`, placed

`da_expand(root, factors, zs, shifts)` (`da_expand__L13_L7`, `da_expand__L6_L7`): a leaf placing no
`HeapBuf`, its product tree in its frame run at `rb = fp + cert f (.n (expB 7 + 1))`. The computing
atoms are evaluated forward (`Fwd.ev`) from the four arguments; then the run's pointer `g^rb`, its
fresh words zero, and the leaves' pointer `g^(rb + 128)` (the archive's `ExpAt`). Node `2^d + y` is
`expandLeaf … d y` (`exp_node`), which the run's words hold (`expRunVals`), so the `frameAddr`
holds. `exp_callAtA`: placed at any frame and cursor, ending at the cursor, claiming its run, on
memories reading the factors, powers and shifts. `ExpCert`: the run lies in the frame past its
header, decided by the kernel at the compiled frames (`expTopCert_b2c`, `expCellCert_b2c`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.Value

@[expose] public section

/-- **`da_expand`, evaluated**: its computing atoms defined in order from its four arguments up
to the run's pointer `.n (expB D)`, without a store, only their loads needing a side condition,
their values below it; no `HeapBuf` or hint into the heap; its one `frameAddr` the run's. -/
def expCOk (top D W : ℕ) : Bool :=
  decide (chk 4 ((expBodyA top D).map Stmt.atom) = some (expB D)) &&
  (storesOf 4 ((expBodyA top D).map Stmt.atom)).isEmpty &&
  (expBodyA top D).all (fun a => !needsSide a || (atomLoad? a).isSome) &&
  (expBodyA top D).all (fun a => a.vals.all fun v => decide (v.idx < expB D)) &&
  (expT top D W).all (fun a => !atomAllocB a) &&
  (expT top D W).all (fun a => (atomHeapDest? a).isNone) &&
  decide ((expT top D W).filterMap atomAddr? = [(.n (expB D), .n (expB D + 1))]) &&
  decide ((expT top D W).filterMap atomRun? = [(.n (expB D + 1), 256)])

set_option maxRecDepth 100000 in
theorem expCell_cok : expCOk 6 7 325 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem expTop_cok : expCOk 13 7 325 = true := by decide +kernel

/-- The frame layout `da_expand`'s placed proof needs: its run past the header, in the frame. -/
def ExpCert (fs : String → ℕ) (cert : String → V → ℕ) (f : String) : Prop :=
  2 ≤ cert f (.n (expB 7 + 1)) ∧ cert f (.n (expB 7 + 1)) + 256 ≤ fs f

theorem expTopCert_b2c : ExpCert B2C.fs B2C.cert "da_expand__L13_L7" := by
  unfold ExpCert; decide +kernel

theorem expCellCert_b2c : ExpCert B2C.fs B2C.cert "da_expand__L6_L7" := by
  unfold ExpCert; decide +kernel

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
theorem expRun_get {D k : ℕ} (hD : D ≤ 7) (hk : k < 256) :
    (expRun D)[k]? = some (if k = 0 then .n (expB D + 1) else if k < 2 ^ (D + 1) then
      .n (nodeAt (Nat.log 2 k) (k - 2 ^ Nat.log 2 k)) else .n (expB D + 2 + (k - 2 ^ (D + 1)))) := by
  have h9 : 2 ^ (D + 1) ≤ 256 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num : 2 ^ 8 ≤ 256)
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
      simp only [List.getElem?_map, List.getElem?_range (show j + 1 - 2 ^ (D + 1) < 256 - 2 ^ (D + 1) by
        omega), Option.map_some]

/-- The loads of `da_expand`'s computing atoms: a power, a shift, a node's factor. -/
theorem expBodyA_load {top D : ℕ} {d' p : V} {off : ℕ} (h : Atom.load d' p off ∈ expBodyA top D) :
    (∃ d < D, p = .n (valf% «da_expand» "zs") ∧ off = top - d) ∨
      (∃ d < D, p = .n (valf% «da_expand» "shifts") ∧ off = top - d) ∨
      ∃ d < D, ∃ y < 2 ^ d, p = .n (valf% «da_expand» "factors") ∧ off = 2 ^ d + y := by
  simp only [expBodyA, expDepthA, expNodeA, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false, reduceCtorEq, false_or, Atom.load.injEq] at h
  rcases h with ⟨d, hd, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨y, hy, ⟨-, rfl, rfl⟩⟩⟩
  · exact Or.inl ⟨d, hd, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨d, hd, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨d, hd, y, hy, rfl, rfl⟩)

theorem expRunVals_get {root : E} {F Z S : ℕ → E} {top D k : ℕ} (hk : k < 256) :
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

/-- What `da_expand` reads: the factors at `g^cf`, the powers at `g^cz`, the shifts at `g^cs`. -/
def ExpReads (rd : Reader) (F Z S : ℕ → E) (top cf cz cs : ℕ) : Prop :=
  (∀ n, 1 ≤ n → n < 2 ^ 7 → LoadHolds rd (gen ^ cf) n (F n)) ∧
    (∀ d < 7, LoadHolds rd (gen ^ cz) (top - d) (Z (top - d))) ∧
    ∀ d < 7, LoadHolds rd (gen ^ cs) (top - d) (S (top - d))

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxRecDepth 4000 in
/-- **`da_expand` completes placed** at any frame `fp` and cursor `c`, ending at `c`: its tree in
its frame run at `rb = fp + cert f (.n (expB 7 + 1))`, which it claims, returning the run at its
leaves. -/
theorem exp_callAtA {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) {top W : ℕ} (hok : expOk fn top 7 W = true)
    (hcok : expCOk top 7 W = true) (hDt : 7 ≤ top + 1) (hcert : ExpCert fs cert f) (k : ℕ) (root : E)
    (F Z S : ℕ → E) {cf cz cs : ℕ} {R : ℕ → Prop}
    (hFr : ∀ n, 1 ≤ n → n < 2 ^ 7 → R (cf + n)) (hZr : ∀ d < 7, R (cz + (top - d)))
    (hSr : ∀ d < 7, R (cs + (top - d))) (fp c : ℕ) :
    CallAtA fs al cert k f [root, gen ^ cf, gen ^ cz, gen ^ cs]
      [gen ^ (fp + cert f (.n (expB 7 + 1)) + 128)] R
      (fun i => fp + cert f (.n (expB 7 + 1)) ≤ i ∧ i < fp + cert f (.n (expB 7 + 1)) + 256)
      (fun rd => HoldsWords rd [(fp + cert f (.n (expB 7 + 1)), expRunVals root F Z S top 7)])
      (fun rd => ExpReads rd F Z S top cf cz cs) (fun _ _ => True) (fs f) fp c c := by
  have h9 : 2 ^ (7 + 1) ≤ 256 := by norm_num
  unfold expOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hparams, hW⟩, hok⟩ := hok
  split at hok
  case h_2 => exact absurd hok (by simp)
  rename_i A vs hsp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨rfl, htm⟩ := hok
  have hA := atomsEqb_sound htm
  subst hA
  have hb := splitBody_eq hsp
  unfold expCOk at hcok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨hchk, hst⟩, hside⟩, hvals⟩, hna⟩, hnh⟩, haddr⟩, hrun⟩ := hcok
  set rb := fp + cert f (.n (expB 7 + 1)) with hrb
  have hlenR : (expRunVals root F Z S top 7).length = 256 := by simp [expRunVals]
  have hc := hcert
  unfold ExpCert at hc
  refine VsC.callAtA_leafD (bufs := []) [(rb, expRunVals root F Z S top 7)] hl
    ⟨fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; left; rw [hlenR]; omega,
      List.pairwise_singleton _ _⟩ (fun _ h => h) fun rd _ hm hp => ?_
  obtain ⟨hF, hZ, hS⟩ := hp
  have hrunR : ReadsAt rd (gen ^ rb) (expRunVals root F Z S top 7) := readsAt_gen_pow.mp hm
  -- the valuation
  let w : ℕ → E := fun _ => 0
  have hchk' : chk [root, gen ^ cf, gen ^ cz, gen ^ cs].length
      ((expBodyA top 7).map Stmt.atom) = some (expB 7) := hchk
  obtain ⟨hlen, -, hgs⟩ := ev_spec rd w _ _ hchk'
  rw [show [root, gen ^ cf, gen ^ cz, gen ^ cs].length = 4 from rfl, hst] at hgs
  set evl := ev rd w [root, gen ^ cf, gen ^ cz, gen ^ cs] ((expBodyA top 7).map Stmt.atom) with hevl
  set rbE : E := ofK (addressOfIndex rb) with hrbE
  set tl : List E := rbE :: (List.replicate (expC 7 - expB 7 - 1) 0 ++ [word W 0, rbE * word W 0]) with htl
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (evl ++ tl) := ⟨_, rfl⟩
  have hag : ∀ v : V, v.idx < expB 7 → B1.Val.ofArgs evl v = σ v := fun v hv => by
    rw [hσ]; exact (ofArgs_old (by rw [hlen]; exact hv)).symm
  have hg : ∀ a ∈ expBodyA top 7, Good rd [] w σ a := fun a ha =>
    good_congr (fun v hv => hag v (by
      have := List.all_eq_true.mp (List.all_eq_true.mp hvals a ha) v hv
      simpa using this)) (hgs (.atom a) (List.mem_map_of_mem ha))
  have hpar : ∀ i < (valf% «da_expand» "nodes[1]"), σ (.n i) = [root, gen ^ cf, gen ^ cz, gen ^ cs].getD i 0 := by
    intro i hi
    have hB : 4 ≤ expB 7 := by unfold expB; omega
    rw [← hag _ (by show i < expB 7; omega), hevl]
    exact ev_params rd w hchk' (by simpa using hi)
  have e0 : σ (.n (valf% «da_expand» "root")) = root := hpar 0 (by norm_num)
  have e1 : σ (.n (valf% «da_expand» "factors")) = gen ^ cf := hpar 1 (by norm_num)
  have e2 : σ (.n (valf% «da_expand» "zs")) = gen ^ cz := hpar 2 (by norm_num)
  have e3 : σ (.n (valf% «da_expand» "shifts")) = gen ^ cs := hpar 3 (by norm_num)
  have htl_at : ∀ j, σ (.n (expB 7 + j)) = tl.getD j 0 := fun j => by
    rw [hσ, ← hlen]; exact ofArgs_new evl tl j
  have hmC : expC 7 - expB 7 - 1 = 1 + (256 - 2 ^ (7 + 1)) := by unfold expC; omega
  -- the computing atoms
  have hatB : ∀ a ∈ expBodyA top 7, a.Holds rd σ := by
    refine atoms_holds hg fun a ha hns => Or.inr ?_
    have hld := List.all_eq_true.mp hside a ha
    rw [hns] at hld
    cases a with
    | load d' p off =>
      simp only [Side, List.not_mem_nil, ↓reduceIte]
      rcases expBodyA_load ha with ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, y, hy, rfl, rfl⟩
      · rw [e2]; exact ⟨(hZ d hd).1, by rw [(hZ d hd).2]; rfl⟩
      · rw [e3]; exact ⟨(hS d hd).1, by rw [(hS d hd).2]; rfl⟩
      · have h1 : 1 ≤ 2 ^ d + y := by have := Nat.one_le_two_pow (n := d); omega
        have h2 : 2 ^ d + y < 2 ^ 7 := by
          calc 2 ^ d + y < 2 ^ d + 2 ^ d := by omega
            _ = 2 ^ (d + 1) := by rw [pow_succ]; ring
            _ ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hd
        rw [e1]; exact ⟨(hF _ h1 h2).1, by rw [(hF _ h1 h2).2]; rfl⟩
    | _ => simp [atomLoad?] at hld
  -- the loaded words
  have hZv : ∀ d < 7, σ (.n (expB d)) = Z (top - d) := by
    intro d hd
    have h := (exp_depth hd (Nat.two_pow_pos d) hatB).1
    rw [e2] at h
    exact Option.some.inj (h.2.symm.trans (hZ d hd).2)
  have hSv : ∀ d < 7, σ (.n (expB d + 1)) = S (top - d) := by
    intro d hd
    have h := (exp_depth hd (Nat.two_pow_pos d) hatB).2.1
    rw [e3] at h
    exact Option.some.inj (h.2.symm.trans (hS d hd).2)
  have hFv : ∀ n, 1 ≤ n → n < 2 ^ 7 → memAt rd (σ (.n (valf% «da_expand» "factors"))) n = F n := by
    intro n h1 h2
    rw [e1, memAt, (hF n h1 h2).2]
    rfl
  -- the nodes
  have hnode : ∀ d ≤ 7, ∀ y < 2 ^ d, σ (.n (nodeAt d y)) = expandLeaf root F Z S top d y := by
    intro d hd y hy
    rw [exp_node hatB hDt d hd y hy, e0]
    refine expandLeaf_congr hy (fun n h1 h2 => hFv n h1 (lt_of_lt_of_le h2
      (Nat.pow_le_pow_right (by norm_num) hd))) (fun d' hd' => ?_) (fun d' hd' => ?_)
    · rw [show top - (top - d') = d' by omega]
      exact hZv d' (by omega)
    · rw [show top - (top - d') = d' by omega]
      exact hSv d' (by omega)
  -- the run
  have hrv : ∀ k < 256, σ ((expRun 7)[k]?.getD (.n (valf% «da_expand» "root"))) =
      (expRunVals root F Z S top 7).getD k 0 := by
    intro k hk
    rw [expRun_get (by norm_num) hk, Option.getD_some, List.getD_eq_getElem _ _ (by rw [hlenR]; exact hk),
      expRunVals_get hk]
    by_cases h0 : k = 0
    · subst h0
      rw [ite_pos' rfl, htl_at 1, htl, tl_mid _ _ _ le_rfl (by omega)]
      simp
    · rw [ite_neg' h0]
      by_cases hkD : k < 2 ^ (7 + 1)
      · rw [ite_pos' hkD, ite_pos' ⟨by omega, hkD⟩]
        have hlog : Nat.log 2 k ≤ 7 := by
          have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hkD
          omega
        have hy : k - 2 ^ Nat.log 2 k < 2 ^ Nat.log 2 k := by
          have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) k
          rw [pow_succ] at h1
          omega
        exact hnode _ hlog _ hy
      · rw [ite_neg' hkD, ite_neg' (by omega), show expB 7 + 2 + (k - 2 ^ (7 + 1)) =
          expB 7 + (1 + (1 + (k - 2 ^ (7 + 1)))) by omega, htl_at, htl]
        have hjm : 1 + (1 + (k - 2 ^ (7 + 1))) ≤ expC 7 - expB 7 - 1 := by
          rw [hmC]
          have h2 : 2 ^ (7 + 1) ≤ k := by omega
          omega
        exact tl_mid rbE (word W 0) (rbE * word W 0) (by omega) hjm
  have hrunLen : (expRun 7).length = 256 := by
    simp only [expRun, List.length_cons, List.length_append, List.length_map, List.length_range,
      length_nodesBelow]
    norm_num
  have hpE : σ (.n (expB 7)) = rbE := by rw [← Nat.add_zero (expB 7), htl_at 0]; rfl
  have hcE : σ (.n (expC 7)) = word W 0 := by
    rw [show expC 7 = expB 7 + (expC 7 - expB 7 - 1 + 1) by unfold expC; omega, htl_at, htl, tl_a]
  have hmE : σ (.n (expC 7 + 1)) = rbE * word W 0 := by
    rw [show expC 7 + 1 = expB 7 + (expC 7 - expB 7 - 1 + 2) by unfold expC; omega, htl_at, htl, tl_b]
  have hWv : word W 0 = ofK (addressOfIndex (2 ^ 7)) := by rw [word_eOfNat, eOfNat, hW]
  have hat : ∀ a ∈ expT top 7 W, a.Holds rd σ := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hatB a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · refine ⟨by rw [hpE]; exact ofK_isInK _, fun k hk w' hr => ?_⟩
      rw [hrunLen] at hk
      rw [hpE, hrbE, ← gen_pow_eq_ofK] at hr
      have hl' := hrunR k (by rw [hlenR]; exact hk)
      have hw' : w' = (expRunVals root F Z S top 7)[k]'(by rw [hlenR]; exact hk) :=
        Option.some.inj (hr.symm.trans hl'.2)
      rw [hw', ← List.getD_eq_getElem _ 0, ← hrv k hk, List.getElem?_eq_getElem (by
        rw [hrunLen]; exact hk), Option.getD_some]
    · exact hcE
    · show σ (.n (expC 7 + 1)) = σ (.n (expB 7)) * σ (.n (expC 7))
      rw [hmE, hpE, hcE]
  have hwk : walk σ fn.body = .ret ((expT top 7 W).map Ev.atom) [.n (expC 7 + 1)] := by
    rw [hb]; exact walk_atoms σ _ _
  refine ⟨σ, fn, (expT top 7 W).map Ev.atom, [.n (expC 7 + 1)], hf, by rw [hparams]; simp [e0, e1, e2, e3],
    hwk, ?_, calls_atoms _, allocs_atoms σ hna, ⟨by rw [allocDsts_atoms hna]; rfl, fun q hq => ?_⟩,
    holds_atoms hat, fun A hA => ?_, fun A hA => ?_, fun i hi => ?_, trivial⟩
  · show [σ (.n (expC 7 + 1))] = [gen ^ (rb + 128)]
    rw [hmE, hWv, hrbE, ← gen_pow_eq_ofK, ← gen_pow_eq_ofK, ← pow_add]
    norm_num
  · rw [addrs_atoms, haddr, List.mem_singleton] at hq
    subst hq
    exact hpE
  · rw [loadAddrs_atoms] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨a, ha, hq⟩ := List.mem_filterMap.mp hq
    rcases List.mem_append.mp ha with ha | ha
    · cases a with
      | load d' p off =>
        simp only [atomLoad?, Option.some.injEq] at hq
        subst hq
        rcases expBodyA_load ha with ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, rfl, rfl⟩ | ⟨d, hd, y, hy, rfl, rfl⟩
        · exact ⟨cz + (top - d), by rw [e2, gen_pow_eq_ofK]; exact Main.addr_ofK _ _, Or.inr (hZr d hd)⟩
        · exact ⟨cs + (top - d), by rw [e3, gen_pow_eq_ofK]; exact Main.addr_ofK _ _, Or.inr (hSr d hd)⟩
        · have h1 : 1 ≤ 2 ^ d + y := by have := Nat.one_le_two_pow (n := d); omega
          have h2 : 2 ^ d + y < 2 ^ 7 := by
            calc 2 ^ d + y < 2 ^ d + 2 ^ d := by omega
              _ = 2 ^ (d + 1) := by rw [pow_succ]; ring
              _ ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hd
          exact ⟨cf + (2 ^ d + y), by rw [e1, gen_pow_eq_ofK]; exact Main.addr_ofK _ _, Or.inr (hFr _ h1 h2)⟩
      | _ => simp [atomLoad?] at hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> simp [atomLoad?] at hq
  · rw [VsC.heapHintAddrs_atoms _ hnh] at hA
    simp at hA
  · obtain ⟨h1, h2⟩ := hi
    refine Or.inr ⟨(.n (expB 7 + 1), 256), by rw [runs_atoms, hrun]; exact List.mem_singleton_self _, h1, h2⟩

set_option maxRecDepth 100000 in
/-- **`da_expand__L13_L7`**, placed: the tree over the cell index (bits `13 … 7`). -/
theorem expTop_callAtA (hcert : ExpCert fs cert "da_expand__L13_L7") (k : ℕ) (root : E) (F Z S : ℕ → E)
    {cf cz cs : ℕ} {R : ℕ → Prop}
    (hFr : ∀ n, 1 ≤ n → n < 2 ^ 7 → R (cf + n)) (hZr : ∀ d < 7, R (cz + (13 - d)))
    (hSr : ∀ d < 7, R (cs + (13 - d))) (fp c : ℕ) :
    CallAtA fs al cert k "da_expand__L13_L7" [root, gen ^ cf, gen ^ cz, gen ^ cs]
      [gen ^ (fp + cert "da_expand__L13_L7" (.n (expB 7 + 1)) + 128)] R
      (fun i => fp + cert "da_expand__L13_L7" (.n (expB 7 + 1)) ≤ i ∧
        i < fp + cert "da_expand__L13_L7" (.n (expB 7 + 1)) + 256)
      (fun rd => HoldsWords rd [(fp + cert "da_expand__L13_L7" (.n (expB 7 + 1)), expRunVals root F Z S 13 7)])
      (fun rd => ExpReads rd F Z S 13 cf cz cs) (fun _ _ => True) (fs "da_expand__L13_L7") fp c c :=
  exp_callAtA find_da_expand_L13_L7 (by decide +kernel) expTop_ok expTop_cok (by norm_num) hcert k root F Z S
    hFr hZr hSr fp c

set_option maxRecDepth 100000 in
/-- **`da_expand__L6_L7`**, placed: the tree inside a cell (bits `6 … 0`). -/
theorem expCell_callAtA (hcert : ExpCert fs cert "da_expand__L6_L7") (k : ℕ) (root : E) (F Z S : ℕ → E)
    {cf cz cs : ℕ} {R : ℕ → Prop}
    (hFr : ∀ n, 1 ≤ n → n < 2 ^ 7 → R (cf + n)) (hZr : ∀ d < 7, R (cz + (6 - d)))
    (hSr : ∀ d < 7, R (cs + (6 - d))) (fp c : ℕ) :
    CallAtA fs al cert k "da_expand__L6_L7" [root, gen ^ cf, gen ^ cz, gen ^ cs]
      [gen ^ (fp + cert "da_expand__L6_L7" (.n (expB 7 + 1)) + 128)] R
      (fun i => fp + cert "da_expand__L6_L7" (.n (expB 7 + 1)) ≤ i ∧
        i < fp + cert "da_expand__L6_L7" (.n (expB 7 + 1)) + 256)
      (fun rd => HoldsWords rd [(fp + cert "da_expand__L6_L7" (.n (expB 7 + 1)), expRunVals root F Z S 6 7)])
      (fun rd => ExpReads rd F Z S 6 cf cz cs) (fun _ _ => True) (fs "da_expand__L6_L7") fp c c :=
  exp_callAtA find_da_expand_L6_L7 (by decide +kernel) expCell_ok expCell_cok (by norm_num) hcert k root F Z S
    hFr hZr hSr fp c

end
end LeanVM.Guest.Complete
