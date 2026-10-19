/-
  LeanVM.Guest.B1.Sig.ArmCost

  The cost of the digit groups' dispatches a run of `verify_lean_xmss` takes, against any table of
  per-arm costs: one arm per match, the one the selector picks, summed over the forty matches of
  the two codewords.
-/

module

public import LeanVM.Guest.B1.Sig.XmssData
public import LeanVM.Guest.B1.Sig.XmssIff
public import LeanVM.Guest.Memory.Eval

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value

@[expose] public section

noncomputable section

open Classical

/-! ## Chosen-arm costs -/

mutual
/-- The cost of the arms a walk under `σ` chooses, from the table `tab` of the matches' per-arm
costs (keyed by the selector's index; an unkeyed match costs only its chosen arm's). -/
def cwList (tab : ℕ → Option (List ℕ)) (σ : Val) : List Stmt → ℕ
  | [] => 0
  | s :: ss => cw1 tab σ s + cwList tab σ ss

def cw1 (tab : ℕ → Option (List ℕ)) (σ : Val) : Stmt → ℕ
  | .ite c z n => if σ c = 0 then cwList tab σ z else cwList tab σ n
  | .match_ v arms => cwArms tab σ v (tab v.idx) 0 arms
  | _ => 0

def cwArms (tab : ℕ → Option (List ℕ)) (σ : Val) (v : V) (cs : Option (List ℕ)) :
    ℕ → List (List Stmt) → ℕ
  | _, [] => 0
  | j, a :: as => if σ v = ofK (gpow j) then (cs.map fun l => l.getD j 0).getD 0 + cwList tab σ a
      else cwArms tab σ v cs (j + 1) as
end

/-- The table cost of the arm among `j ..< j + n` the selector picks, the first `j'` with
`σ v = g^j'`. -/
def pickCost (σ : Val) (v : V) (cs : Option (List ℕ)) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | j, n + 1 => if σ v = ofK (gpow j) then (cs.map fun l => l.getD j 0).getD 0 else pickCost σ v cs (j + 1) n

/-! ## Bodies of straight arms -/

/-- Atoms and returns only. -/
def atomsOnly (ss : List Stmt) : Bool :=
  ss.all fun s => match s with
    | .atom _ => true
    | .ret _ => true
    | _ => false

/-- Atoms, returns, and matches over arms of atoms only. -/
def shapeOk (ss : List Stmt) : Bool :=
  ss.all fun s => match s with
    | .atom _ => true
    | .ret _ => true
    | .match_ _ arms => arms.all atomsOnly
    | _ => false

/-- The matches of a block: their selectors and arm counts. -/
def matchesOf (ss : List Stmt) : List (V × ℕ) :=
  ss.filterMap fun s => match s with
    | .match_ v arms => some (v, arms.length)
    | _ => none

theorem cwList_atoms (tab : ℕ → Option (List ℕ)) (σ : Val) :
    ∀ ss : List Stmt, atomsOnly ss = true → cwList tab σ ss = 0
  | [], _ => rfl
  | s :: ss, h => by
      simp only [atomsOnly, List.all_cons, Bool.and_eq_true] at h
      rw [cwList, cwList_atoms tab σ ss h.2]
      match s, h.1 with
      | .atom _, _ => rfl
      | .ret _, _ => rfl

theorem cwArms_atoms (tab : ℕ → Option (List ℕ)) (σ : Val) (v : V) (cs : Option (List ℕ)) :
    ∀ (arms : List (List Stmt)) (j : ℕ), arms.all atomsOnly = true →
      cwArms tab σ v cs j arms = pickCost σ v cs j arms.length
  | [], _, _ => by rw [cwArms]; rfl
  | a :: as, j, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      rw [cwArms, List.length_cons, pickCost, cwList_atoms tab σ a h.1, Nat.add_zero,
        cwArms_atoms tab σ v cs as (j + 1) h.2]

/-- **A shaped block costs its matches' picked arms.** -/
theorem cwList_shaped (tab : ℕ → Option (List ℕ)) (σ : Val) :
    ∀ ss : List Stmt, shapeOk ss = true →
      cwList tab σ ss = ((matchesOf ss).map fun q => pickCost σ q.1 (tab q.1.idx) 0 q.2).sum
  | [], _ => rfl
  | s :: ss, h => by
      simp only [shapeOk, List.all_cons, Bool.and_eq_true] at h
      have ih := cwList_shaped tab σ ss h.2
      rw [cwList, ih]
      match s, h.1 with
      | .atom _, _ => simp [cw1, matchesOf]
      | .ret _, _ => simp [cw1, matchesOf]
      | .match_ v arms, ha =>
          rw [cw1, cwArms_atoms tab σ v _ arms 0 ha]
          simp [matchesOf]

/-! ## The matches of `verify_lean_xmss` -/

/-- The bases of digit groups `p ..< p + m` from `b`, as `cGroups` lays them out. -/
def cgBases (w : Wots) (power : Nat → V) : Nat → Nat → V → V → Nat → List Nat
  | 0, _, _, _, _ => []
  | m + 1, p, prod, enc, b =>
      b :: cgBases w power m (p + 1) (groupProd w.lx (p == 0) 3 b) (groupEnc w.lx (p == 0) 3 b)
        (cGroup w power prod enc (3 * p) 3 (p == 0) b).2

/-- A codeword's matches: its `G` groups of 64 arms, then the last of 4. -/
def ccMatches (w : Wots) (power : Nat → V) (G b : Nat) : List (V × ℕ) :=
  (cgBases w power G 0 (.n 0) (.n 0) b).map (fun c => (.n c, 64)) ++
    [(.n (cGroups w power G 0 (.n 0) (.n 0) b).2.1, 4)]

/-- The matches of `verify_lean_xmss`: the two layers' codewords. -/
def xMatches : List (V × ℕ) :=
  let b1 := (xLayer 0 139 (.n 0)).2.1
  ccMatches (xW (139 + 16) (.n 128)) (fun s => .n (129 + s)) 19 (139 + 16 + 6) ++
    ccMatches (xW (b1 + 10) (.n (b1 + 1))) (fun s => .n (129 + s)) 19 (b1 + 10 + 6)

theorem xBody_shapeOk : shapeOk Data.core16.body = true := by decide +kernel

theorem xBody_matches : matchesOf Data.core16.body = xMatches := by decide +kernel

/-! ## The arms a valid run picks -/

section Sel

variable {C : CallRel} {rd : Reader}

theorem cGroups_sel {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) :
    ∀ (m p : Nat) (prod enc : V) (b : Nat) {next : Prop} {kret : List E → Prop}, (p = 0 → 0 < m) →
      Stmt.HoldsList C rd σ (cGroups w power m p prod enc b).1 next kret →
      (∃ ks : Nat → Nat, (∀ q < m, ks q < 64 ∧
          σ (.n ((cgBases w power m p prod enc b).getD q 0)) = ofK (gpow (ks q))) ∧
        σ (cGroups w power m p prod enc b).2.2.2.1 =
          (if p = 0 then 1 else σ prod) * gen ^ (∑ q ∈ Finset.range m, digitSum (ks q) 3)) ∧ next
  | 0, p, prod, enc, b, next, kret, hm, h => by
      have hp : p ≠ 0 := fun h => absurd (hm h) (by omega)
      exact ⟨⟨fun _ => 0, fun q h => absurd h (by omega), by simp [cGroups, hp]⟩, h⟩
  | m + 1, p, prod, enc, b, next, kret, _, h => by
      simp only [cGroups, cgBases] at h ⊢
      rw [holdsList_append] at h
      obtain ⟨⟨k, hk, hsel, -, hfold⟩, h⟩ := cGroup_sound hmd h
      obtain ⟨⟨ks, hks, hprod⟩, hn⟩ := cGroups_sel hmd hpow m (p + 1) _ _ _ (by omega) h
      refine ⟨⟨fun q => if q = 0 then k else ks (q - 1), fun q hq => ?_, ?_⟩, hn⟩
      · by_cases hq0 : q = 0
        · subst hq0
          exact ⟨by simpa using hk, by simpa using hsel⟩
        · obtain ⟨h1, h2⟩ := hks (q - 1) (by omega)
          refine ⟨by simpa [hq0] using h1, ?_⟩
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          simpa using h2
      · unfold ArmFold groupProd at hfold
        rw [hprod, Finset.sum_range_succ']
        simp only [groupProd, ↓reduceIte, Nat.add_sub_cancel, Nat.add_one_ne_zero]
        rw [hfold.1, hpow _ (pow_digitSum_lt k), pow_add]
        by_cases hp : p = 0 <;> simp [hp] <;> ring

/-- **A codeword's picked arms**: its groups' digit groups and the last digit, adding up to the
target's exponent. -/
theorem cCodeword_sel {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) {G : Nat} (hG : 0 < G) {target : E}
    {d0 : V} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (cCodeword w power G target d0 b).1 next kret) :
    ∃ (ks : Nat → Nat) (kl : Nat), (∀ q < G, ks q < 64 ∧
        σ (.n ((cgBases w power G 0 (.n 0) (.n 0) b).getD q 0)) = ofK (gpow (ks q))) ∧ kl < 4 ∧
      σ (.n (cGroups w power G 0 (.n 0) (.n 0) b).2.1) = ofK (gpow kl) ∧
      target = gen ^ (∑ q ∈ Finset.range G, digitSum (ks q) 3 + kl) ∧ next := by
  simp only [cCodeword] at h
  rw [holdsList_append, holdsList_append] at h
  obtain ⟨⟨ks, hks, hprod⟩, h⟩ := cGroups_sel hmd hpow G 0 _ _ _ (fun _ => hG) h
  obtain ⟨⟨kl, hkl, hsel, -, hfold⟩, h⟩ := cGroup_sound hmd h
  simp only [cst, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
  obtain ⟨hc, hp, -, hn⟩ := h
  rw [e_add_eq_zero_iff] at hp
  simp only [pow_one] at hkl
  refine ⟨ks, kl, hks, hkl, hsel, ?_, hn⟩
  unfold ArmFold at hfold
  rw [← hc, ← hp, hfold.1, hprod, hpow _ (by rw [digitSum_one hkl]; omega), digitSum_one hkl, pow_add]
  simp

/-- Atoms only, no return. -/
def onlyAtoms (ss : List Stmt) : Bool :=
  ss.all fun s => match s with
    | .atom _ => true
    | _ => false

theorem holdsList_onlyAtoms {σ : Val} {next : Prop} {kret : List E → Prop} :
    ∀ ss : List Stmt, onlyAtoms ss = true → Stmt.HoldsList C rd σ ss next kret → next
  | [], _, h => h
  | s :: ss, hs, h => by
      simp only [onlyAtoms, List.all_cons, Bool.and_eq_true] at hs
      match s, hs.1 with
      | .atom a, _ => exact holdsList_onlyAtoms ss hs.2 ((holdsList_cons_atom a ss next kret σ).mp h).2

theorem holdsList_skip {σ : Val} {ss rest : List Stmt} {next : Prop} {kret : List E → Prop}
    (hs : onlyAtoms ss = true) (h : Stmt.HoldsList C rd σ (ss ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret := by
  rw [holdsList_append] at h
  exact holdsList_onlyAtoms ss hs h

/-- **A layer's picked arms**: its 19 groups' digit groups and the last digit, adding up to 106. -/
def LayerSel (σ : Val) (w : Wots) (cb : Nat) : Prop :=
  ∃ (ks : Nat → Nat) (kl : Nat), (∀ q < 19, ks q < 64 ∧
      σ (.n ((cgBases w (fun s => .n (129 + s)) 19 0 (.n 0) (.n 0) cb).getD q 0)) = ofK (gpow (ks q))) ∧
    kl < 4 ∧ σ (.n (cGroups w (fun s => .n (129 + s)) 19 0 (.n 0) (.n 0) cb).2.1) = ofK (gpow kl) ∧
    ∑ q ∈ Finset.range 19, digitSum (ks q) 3 + kl = 106

theorem layerSel_of {σ : Val} {L : Nat} (hpre : XPre σ L) {a : Nat} {idx d0 : V} {next : Prop}
    {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (cCodeword (xW a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6)).1 next kret) :
    LayerSel σ (xW a idx) (a + 6) ∧ next := by
  obtain ⟨ks, kl, hks, hkl, hsel, ht, hn⟩ := cCodeword_sel (w := xW a idx) hpre.md (fun s hs => hpre.pow s hs)
    (by norm_num) h
  refine ⟨⟨ks, kl, hks, hkl, hsel, ?_⟩, hn⟩
  rw [xTarget_eq] at ht
  have hle : ∑ q ∈ Finset.range 19, digitSum (ks q) 3 ≤ 3 * 57 := by
    have := Finset.sum_le_sum fun q (_ : q ∈ Finset.range 19) => digitSum_le (ks q) 3
    simpa using this
  exact (gen_pow_inj (by norm_num) (by omega) ht).symm

/-- **The picked arms of a run of `verify_lean_xmss`**, in both layers. -/
theorem xBody_sel {σ : Val} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ xBody next kret) :
    LayerSel σ (xW (139 + 16) (.n 128)) (139 + 16 + 6) ∧
      LayerSel σ (xW ((xLayer 0 139 (.n 0)).2.1 + 10) (.n ((xLayer 0 139 (.n 0)).2.1 + 1)))
        ((xLayer 0 139 (.n 0)).2.1 + 10 + 6) := by
  rw [xBody_split, holdsList_append, holdsList_append] at h
  obtain ⟨-, ⟨L, hpre⟩, h⟩ := xPrologue_sound h
  have e0 : (xLayer 0 139 (.n 0)).1 = xDigest0 139 ++ (xTail 0 (139 + 16) (.n 128) (.n (139 + 14))).1 := by
    rw [xLayer_zero]
  have e1 : (xLayer 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2).1 =
      xDigest1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2 ++
        (xTail 1 ((xLayer 0 139 (.n 0)).2.1 + 10) (.n ((xLayer 0 139 (.n 0)).2.1 + 1))
          (.n ((xLayer 0 139 (.n 0)).2.1 + 8))).1 := by
    rw [xLayer_one]
  rw [holdsList_append, e0] at h
  have h := holdsList_skip (by decide +kernel) h
  simp only [xTail, List.append_assoc] at h
  have h := holdsList_skip (by decide +kernel) h
  rw [holdsList_append] at h
  obtain ⟨hs0, h⟩ := layerSel_of hpre h
  have h := holdsList_onlyAtoms _ (by decide +kernel) h
  rw [holdsList_append, e1] at h
  have h := holdsList_skip (by decide +kernel) h
  simp only [xTail, List.append_assoc] at h
  have h := holdsList_skip (by decide +kernel) h
  rw [holdsList_append] at h
  exact ⟨hs0, (layerSel_of hpre h).1⟩

/-! ## The bound -/

theorem pickCost_of {σ : Val} {v : V} {cs : Option (List ℕ)} {k : ℕ} (hv : σ v = ofK (gpow k))
    (hk : k < 2 ^ 64 - 1) : ∀ n j, j ≤ k → k < j + n →
      pickCost σ v cs j n = (cs.map fun l => l.getD k 0).getD 0
  | 0, _, _, h2 => absurd h2 (by omega)
  | n + 1, j, h1, h2 => by
      rw [pickCost]
      by_cases hj : σ v = ofK (gpow j)
      · rw [ite_pos' hj]
        have := gpow_injOn (show j ∈ Set.Iio (2 ^ 64 - 1) by simp only [Set.mem_Iio]; omega)
          (show k ∈ Set.Iio (2 ^ 64 - 1) by simp only [Set.mem_Iio]; omega) (ofK_injective (hj.symm.trans hv))
        rw [this]
      · rw [ite_neg' hj]
        have hjk : j ≠ k := fun e => hj (e ▸ hv)
        exact pickCost_of hv hk n (j + 1) (by omega) (by omega)

theorem sum_map_getD (f : ℕ → ℕ) : ∀ L : List ℕ, (L.map f).sum = ∑ q ∈ Finset.range L.length, f (L.getD q 0)
  | [] => by simp
  | c :: L => by
      rw [List.map_cons, List.sum_cons, sum_map_getD f L, List.length_cons, Finset.sum_range_succ']
      simp [add_comm]

theorem cgBases_length (w : Wots) (power : Nat → V) :
    ∀ m p prod enc b, (cgBases w power m p prod enc b).length = m
  | 0, _, _, _, _ => rfl
  | m + 1, p, prod, enc, b => by rw [cgBases, List.length_cons, cgBases_length]

/-- The arms of a match of `len` arms: digit groups of 3 digits for 64, of one for 4. -/
def nOf (len : ℕ) : ℕ := if len = 64 then 3 else 1

/-- The chain steps arm `k` of a match of `len` arms walks. -/
def armSteps (len k : ℕ) : ℕ := 3 * nOf len - digitSum k (nOf len)

/-- **A layer's matches cost their bases plus `68` steps.** -/
theorem layer_cost_le (tab : ℕ → Option (List ℕ)) (A : ℕ → ℕ) (B : ℕ) {σ : Val} {w : Wots} {cb : ℕ}
    (hs : LayerSel σ w cb)
    (hA : ∀ q ∈ ccMatches w (fun s => .n (129 + s)) 19 cb, ∀ k < q.2,
      ((tab q.1.idx).map fun l => l.getD k 0).getD 0 ≤ A q.1.idx + B * armSteps q.2 k) :
    ((ccMatches w (fun s => .n (129 + s)) 19 cb).map fun q => pickCost σ q.1 (tab q.1.idx) 0 q.2).sum ≤
      ((ccMatches w (fun s => .n (129 + s)) 19 cb).map fun q => A q.1.idx).sum + 68 * B := by
  obtain ⟨ks, kl, hks, hkl, hsl, hsum⟩ := hs
  have hlen := cgBases_length w (fun s => .n (129 + s)) 19 0 (.n 0) (.n 0) cb
  unfold ccMatches at hA ⊢
  set L := cgBases w (fun s => .n (129 + s)) 19 0 (.n 0) (.n 0) cb
  set cl := (cGroups w (fun s => .n (129 + s)) 19 0 (.n 0) (.n 0) cb).2.1
  simp only [List.map_append, List.map_map, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Function.comp_def, Nat.add_zero]
  rw [sum_map_getD _ L, sum_map_getD _ L, hlen]
  have hmem : ∀ q < 19, ((V.n (L.getD q 0)), 64) ∈ L.map (fun c => (V.n c, 64)) ++ [(V.n cl, 4)] := fun q hq =>
    List.mem_append_left _ (List.mem_map_of_mem (by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))
  have hg : ∀ q ∈ Finset.range 19, pickCost σ (.n (L.getD q 0)) (tab (L.getD q 0)) 0 64 ≤
      A (L.getD q 0) + B * (9 - digitSum (ks q) 3) := fun q hq => by
    rw [Finset.mem_range] at hq
    rw [pickCost_of (hks q hq).2 (by have := (hks q hq).1; omega) 64 0 (Nat.zero_le _) (by have := (hks q hq).1; omega)]
    exact hA _ (hmem q hq) _ (hks q hq).1
  have hl : pickCost σ (.n cl) (tab cl) 0 4 ≤ A cl + B * (3 - kl) := by
    rw [pickCost_of hsl (by omega) 4 0 (Nat.zero_le _) (by omega)]
    have := hA _ (List.mem_append_right _ (List.mem_singleton_self _)) _ hkl
    simpa [armSteps, nOf, digitSum_one hkl] using this
  have hs1 := Finset.sum_le_sum hg
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs1
  have h9 : ∑ q ∈ Finset.range 19, (9 - digitSum (ks q) 3) + ∑ q ∈ Finset.range 19, digitSum (ks q) 3 = 171 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun q _ => Nat.sub_add_cancel (digitSum_le (ks q) 3)]
    simp
  have h68 : ∑ q ∈ Finset.range 19, (9 - digitSum (ks q) 3) + (3 - kl) = 68 := by omega
  have e : B * ∑ q ∈ Finset.range 19, (9 - digitSum (ks q) 3) + B * (3 - kl) = 68 * B := by
    rw [← Nat.mul_add, h68, Nat.mul_comm]
  omega

/-- **The arms a valid run of `verify_lean_xmss` picks cost the matches' bases plus `136` steps**,
against any table bounded per arm by a base per match and `B` per chain step. -/
theorem xmss_cw_le (tab : ℕ → Option (List ℕ)) (A : ℕ → ℕ) (B : ℕ)
    (hA : ∀ q ∈ xMatches, ∀ k < q.2, ((tab q.1.idx).map fun l => l.getD k 0).getD 0 ≤ A q.1.idx + B * armSteps q.2 k)
    {σ : Val} {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ xBody next kret) :
    cwList tab σ Data.core16.body ≤ (xMatches.map fun q => A q.1.idx).sum + 136 * B := by
  rw [cwList_shaped _ _ _ xBody_shapeOk, xBody_matches]
  obtain ⟨h0, h1⟩ := xBody_sel h
  unfold xMatches at hA ⊢
  simp only [List.map_append, List.sum_append]
  have l0 := layer_cost_le tab A B h0 fun q hq => hA q (List.mem_append_left _ hq)
  have l1 := layer_cost_le tab A B h1 fun q hq => hA q (List.mem_append_right _ hq)
  omega

end Sel

/-- **On a valid instance of `verify_lean_xmss`**, at its valuation. -/
theorem xmss_cw_valid (tab : ℕ → Option (List ℕ)) (A : ℕ → ℕ) (B : ℕ)
    (hA : ∀ q ∈ xMatches, ∀ k < q.2, ((tab q.1.idx).map fun l => l.getD k 0).getD 0 ≤ A q.1.idx + B * armSteps q.2 k)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E}
    (hv : (Memory.Tree.node f σ bufs kids).Valid coreProgram rd args rets) (hf : f = "verify_lean_xmss") :
    cwList tab σ Data.core16.body ≤ (xMatches.map fun q => A q.1.idx).sum + 136 * B := by
  obtain ⟨fn, hfind, -, es, vs, hw, -, hev, -⟩ := hv
  subst hf
  rw [find_verify_lean_xmss, Option.some.injEq] at hfind
  subst hfind
  have hw' : walk σ xBody = .ret es vs := hw
  refine xmss_cw_le (C := fun _ _ _ => True) (rd := rd) (next := False) (kret := fun _ => True) tab A B hA ?_
  apply holdsList_of_walk
  generalize xBody = Bd at hw' ⊢
  rw [hw']
  exact ⟨fun e he => ⟨hev e he, fun _ _ _ _ => trivial⟩, trivial⟩

end
end
end LeanVM.Guest.B1.Sig
