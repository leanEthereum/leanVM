/-
  LeanVM.Guest.B1.Place.ArmLay

  The layouts of `open_stacked`'s placed lift at the merged template: the buffers, the callees'
  words, the levels' window pointers, the named callees.
-/

module

public import LeanVM.Guest.B1.Place.ArmCalls
public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.B1.Place.OsQPlace
public import LeanVM.Guest.B1.Place.Lp

/-!
# The lift's layouts

* `baseA c b j`: buffer `j`'s base, the buffers from `b` (`osSizesL`); `osLkA`: the callees'
  words, the buffers but `query_win_ptrs` and the caller's. `osMemA_of_lk`, `osHA_of_lk`: a memory
  holding them holds the buffers (`OsMemA`) and the dispatch relation satisfies `OsHA`.
* `qbpA c ws`: `query_win_ptrs`' words, level `l`'s window pointers `ws l` at its offset;
  `memL_qbp_slice`: level `l`'s slice of them, at the level's offset.
* `os_calls_of_allOkF`, `os_kid_namedO`: a named frame of a flat body proved at `osCR` on every
  memory holding `Lk`, at a valuation agreeing on the calls (`CallAg`), is complete placed on `Lk`, at
  an optional bound; `os_kid_namedX`: any statement its kind's
  callees satisfy on `Lk`.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-! ## The buffers -/

/-- Buffer `j`'s base, the buffers from `b`. -/
def baseA (c : OsCfg) (b j : ℕ) : ℕ := (bases b (osSizesL c)).getD j 0

theorem osPtrA_eq (c : OsCfg) (b j : ℕ) : osPtrA c b j = ofK (addressOfIndex (baseA c b j)) := rfl

theorem osPtrA_mul (c : OsCfg) (b j o : ℕ) :
    osPtrA c b j * gen ^ o = ofK (addressOfIndex (baseA c b j + o)) :=
  ofK_addr_mul_gen_pow _ _

theorem baseA_eq (c : OsCfg) (b : ℕ) {j : ℕ} (hj : j < (osSizesL c).length) :
    baseA c b j = b + ((osSizesL c).take j).sum :=
  os_bases_getD b _ j hj

theorem forall₂_getD_len {own : List (List E)} {sizes : List ℕ}
    (h : List.Forall₂ (fun w s ↦ w.length = s) own sizes) {j : ℕ} (hj : j < sizes.length) :
    (own.getD j []).length = sizes.getD j 0 := by
  have hl := h.length_eq
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
  exact (List.forall₂_iff_get.mp h).2 j (by omega) hj

theorem forall₂_set {own : List (List E)} {sizes : List ℕ}
    (hf : List.Forall₂ (fun c s ↦ c.length ≤ s) own sizes) {j : ℕ} {q : List E}
    (hq : q.length ≤ sizes.getD j 0) :
    List.Forall₂ (fun c s ↦ c.length ≤ s) (own.set j q) sizes := by
  rw [List.forall₂_iff_get] at hf ⊢
  obtain ⟨hl, hg⟩ := hf
  refine ⟨by rw [List.length_set, hl], fun i h1 h2 ↦ ?_⟩
  simp only [List.get_eq_getElem, List.getElem_set]
  split
  · next he =>
    subst he
    rwa [List.getD_eq_getElem _ _ h2] at hq
  · exact hg i (by rw [List.length_set] at h1; exact h1) h2

/-- The callees' words: the buffers but `query_win_ptrs`, and the caller's. -/
def osLkA (c : OsCfg) (b : ℕ) (own : List (List E)) (Lin : Layout) : Layout :=
  (bufL b (osSizesL c) own).eraseIdx osIxQbpA ++ Lin

theorem lkA_mem {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout}
    (hl : own.length = (osSizesL c).length) {j : ℕ} (hj : j < (osSizesL c).length)
    (hne : j ≠ osIxQbpA) : (baseA c b j, own.getD j []) ∈ osLkA c b own Lin := by
  have hjl : j < (bufL b (osSizesL c) own).length := by
    rw [bufL, List.length_zip, os_length_bases, hl, Nat.min_self]; exact hj
  refine List.mem_append_left _ (List.mem_eraseIdx_iff_getElem.mpr ⟨j, hjl, hne, ?_⟩)
  simp only [bufL, List.getElem_zip, baseA]
  rw [List.getD_eq_getElem _ _ (by rw [os_length_bases]; exact hj),
    List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]

/-- **A memory holding the callees' words holds the buffers** but `query_win_ptrs`. -/
theorem osMemA_of_lk {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout}
    (hl : own.length = (osSizesL c).length) (hm : MemL rd (osLkA c b own Lin)) :
    OsMemA rd c b own := fun _ hj hne ↦ hm _ (lkA_mem (Lin := Lin) hl hj hne)

theorem regionL_lkA_buf {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout}
    (hl : own.length = (osSizesL c).length) {j t : ℕ} (hj : j < (osSizesL c).length)
    (hne : j ≠ osIxQbpA) (ht : t < (own.getD j []).length) :
    RegionL (osLkA c b own Lin) (baseA c b j + t) :=
  ⟨_, lkA_mem hl hj hne, by simp, by simpa using ht⟩

theorem regionL_lkA_lin {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout} {i : ℕ}
    (h : RegionL Lin i) : RegionL (osLkA c b own Lin) i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  exact ⟨q, List.mem_append_right _ hq, h1, h2⟩

theorem memL_lin_of_lkA {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout}
    (hm : MemL rd (osLkA c b own Lin)) : MemL rd Lin :=
  (Main.memL_append.mp hm).2

/-- **The callees' words**, held where the buffers are, whatever `query_win_ptrs` holds. -/
theorem memL_osLkA {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {q : List E}
    {Lin : Layout} (hm : MemL rd (bufL b (osSizesL c) (own.set osIxQbpA q))) (hLin : MemL rd Lin) :
    MemL rd (osLkA c b own Lin) := by
  refine Main.memL_append.mpr ⟨fun x hx ↦ ?_, hLin⟩
  obtain ⟨i, hi, hne, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hx
  have hl : (bufL b (osSizesL c) (own.set osIxQbpA q)).length =
      (bufL b (osSizesL c) own).length := by simp [bufL]
  have hi1 : i < (bufL b (osSizesL c) (own.set osIxQbpA q)).length := by omega
  have e : (bufL b (osSizesL c) own)[i]'hi =
      (bufL b (osSizesL c) (own.set osIxQbpA q))[i]'hi1 := by
    simp only [bufL, List.getElem_zip, List.getElem_set, Ne.symm hne, ↓reduceIte]
  rw [e]
  exact hm _ (List.getElem_mem hi1)

theorem regionL_osLkA {c : OsCfg} {b : ℕ} {own : List (List E)} {q : List E} {Lin : Layout}
    {i : ℕ} (h : RegionL (osLkA c b own Lin) i) :
    RegionL Lin i ∨ RegionL (bufL b (osSizesL c) (own.set osIxQbpA q)) i := by
  obtain ⟨x, hx, h1, h2⟩ := h
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨j, hj, hne, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hx
    refine Or.inr ⟨(bufL b (osSizesL c) (own.set osIxQbpA q))[j]'(by simpa [bufL] using hj),
      List.getElem_mem _, ?_, ?_⟩
    · simpa [bufL, List.getElem_zip] using h1
    · simpa [bufL, List.getElem_zip, List.getElem_set, Ne.symm hne] using h2
  · exact Or.inl ⟨x, hx, h1, h2⟩

/-- **The dispatch relation on a memory holding the callees' words satisfies `OsHA`.** -/
theorem osHA_of_lk {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout} {cur tabs : E}
    {xs : List E} (hl : own.length = (osSizesL c).length)
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) {rd : Reader}
    (hlow : LowDef κ rd) (hm : MemL rd (osLkA c b own Lin)) :
    OsHA (osCR rd (fun _ _ _ ↦ True) (OsXOk κ (osLkA c b own Lin))) rd c b own cur tabs xs := by
  obtain ⟨h1, h2⟩ := hLin rd hlow (memL_lin_of_lkA hm)
  refine ⟨h1, h2, osMemA_of_lk hl hm, fun f K hK a r hp hx ↦ osCR_named hK hp ?_,
    fun f a r hK ↦ osCR_special hK trivial⟩
  intro q hq
  obtain ⟨ws, hw, hr⟩ := hx q hq
  refine ⟨ws, hw, fun rd' hl' hm' ↦ ?_⟩
  obtain ⟨g1, g2⟩ := hLin rd' hl' (memL_lin_of_lkA hm')
  exact hr rd' g1 g2 (osMemA_of_lk hl hm')

/-- A buffer's word, loaded. -/
theorem osMemA_load {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} (hM : OsMemA rd c b own)
    {j : ℕ} (hj : j < (osSizesL c).length) (hne : j ≠ osIxQbpA) {t : ℕ}
    (ht : t < (osOwnA own j).length) : LoadHolds rd (osPtrA c b j) t ((osOwnA own j).getD t 0) := by
  have := hM j hj hne t ht
  rwa [List.getD_eq_getElem _ _ ht]

theorem osMemA_load_mul {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)}
    (hM : OsMemA rd c b own) {j : ℕ} (hj : j < (osSizesL c).length) (hne : j ≠ osIxQbpA) {o t : ℕ}
    (ht : o + t < (osOwnA own j).length) :
    LoadHolds rd (osPtrA c b j * gen ^ o) t ((osOwnA own j).getD (o + t) 0) :=
  (loadHolds_mul_gen_pow rd _ o t _).mpr (osMemA_load hM hj hne ht)

/-! ## `query_win_ptrs` -/

theorem levels_getElem_eq {c : OsCfg} {l : ℕ} (hl : l < c.levels.length) :
    c.levels[l] = osLvA c l := (List.getD_eq_getElem _ _ hl).symm

/-- Level `l`'s positions, its squeezes times the positions a squeezed word carries. -/
abbrev osPosN (c : OsCfg) (l : ℕ) : ℕ := (osLvA c l).squeezes * (128 / (osLvA c l).depth)

/-- `query_win_ptrs`' words: level `l`'s window pointers `ws l`, `osPosN c l` of them, the levels in
order. -/
def qbpA (c : OsCfg) (ws : ℕ → List E) : List E :=
  ((List.range c.levels.length).map fun l ↦ (List.range (osPosN c l)).map ((ws l).getD · 0)).flatten

theorem osPosN_map (c : OsCfg) (n : ℕ) (hn : n ≤ c.levels.length) :
    (List.range n).map (osPosN c) =
      (c.levels.take n).map fun lv ↦ lv.squeezes * (128 / lv.depth) := by
  refine List.ext_getElem (by simp [Nat.min_eq_left hn]) fun i h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  simp only [List.length_map, List.length_range] at h1
  rw [osPosN, osLvA, List.getD_eq_getElem _ _ (by omega)]

theorem qbpA_length (c : OsCfg) (ws : ℕ → List E) : (qbpA c ws).length = osPosTotal c := by
  simp only [qbpA, List.length_flatten, List.map_map]
  have e : ((fun x : List E ↦ x.length) ∘ fun l ↦ (List.range (osPosN c l)).map ((ws l).getD · 0)) =
      osPosN c := by funext l; simp
  rw [e, osPosN_map c _ le_rfl, List.take_length]
  rfl

/-- The levels before `l`, then `l`'s positions, within the total. -/
theorem osPos_take_add_le {c : OsCfg} {l : ℕ} (hl : l < c.levels.length) :
    ((c.levels.take l).map fun lv ↦ lv.squeezes * (128 / lv.depth)).sum + osPosN c l ≤ osPosTotal c := by
  rw [osPosTotal, ← List.take_append_drop l c.levels, List.map_append, List.sum_append,
    List.take_append_drop]
  have hd : osPosN c l ≤ ((c.levels.drop l).map fun lv ↦ lv.squeezes * (128 / lv.depth)).sum := by
    rw [List.drop_eq_getElem_cons hl, List.map_cons, List.sum_cons, levels_getElem_eq hl]
    exact Nat.le_add_right _ _
  omega

/-- **A position of level `l` within `query_positions`**, its offset the levels' before it. -/
theorem posOff_add_lt {c : OsCfg} {l : ℕ} (hl : l < c.levels.length)
    (hpo : (osLvA c l).posOff = ((c.levels.take l).map fun lv ↦ lv.squeezes * (128 / lv.depth)).sum)
    {k : ℕ} (hk : k < osPosN c l) : (osLvA c l).posOff + k < osPosTotal c := by
  have := osPos_take_add_le hl
  omega

theorem flatten_getElem_off {α : Type} : ∀ (L : List (List α)) (l k : ℕ) (hl : l < L.length)
    (hk : k < L[l].length) (h : ((L.take l).map List.length).sum + k < L.flatten.length),
    L.flatten[((L.take l).map List.length).sum + k] = L[l][k]
  | [], _, _, hl, _, _ => absurd hl (by simp)
  | x :: L, 0, k, _, hk, h => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons,
      List.getElem_cons_zero] at h hk ⊢
    exact List.getElem_append_left hk
  | x :: L, l + 1, k, hl, hk, h => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons] at h ⊢
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
    exact flatten_getElem_off L l k (by simpa using hl) hk _

/-- Level `l`'s slice of `query_win_ptrs`, its window pointers `w`, at the level's offset. -/
theorem memL_qbp_slice {rd : Reader} {c : OsCfg} {ws : ℕ → List E} {e : ℕ}
    (hm : ReadsAt rd (ofK (addressOfIndex e)) (qbpA c ws)) {l : ℕ} (hl : l < c.levels.length)
    (hlen : (ws l).length ≤ osPosN c l) :
    MemL rd [(e + ((c.levels.take l).map fun lv ↦ lv.squeezes * (128 / lv.depth)).sum, ws l)] := by
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  intro k hk
  simp only at hk
  set L : List (List E) :=
    (List.range c.levels.length).map fun l ↦ (List.range (osPosN c l)).map ((ws l).getD · 0) with hL
  have hLl : L.length = c.levels.length := by simp [hL]
  have hoff : ((L.take l).map List.length).sum =
      ((c.levels.take l).map fun lv ↦ lv.squeezes * (128 / lv.depth)).sum := by
    rw [← osPosN_map c l hl.le, hL, ← List.map_take, List.map_map, List.take_range,
      Nat.min_eq_left hl.le]
    congr 1
    refine List.map_congr_left fun i _ ↦ ?_
    simp
  have hLk : k < (L[l]'(by omega)).length := by simp [hL]; omega
  have hlt : ((L.take l).map List.length).sum + k < L.flatten.length := by
    have := qbpA_length c ws
    rw [qbpA, ← hL] at this
    rw [this, hoff]
    have := osPos_take_add_le hl
    omega
  have h := hm (((L.take l).map List.length).sum + k) (by rw [qbpA, ← hL]; exact hlt)
  have hv : (qbpA c ws)[((L.take l).map List.length).sum + k]'(by rw [qbpA, ← hL]; exact hlt) =
      (ws l)[k] := by
    simp only [qbpA, ← hL]
    rw [flatten_getElem_off L l k (by omega) hLk hlt]
    simp [hL, List.getElem?_eq_getElem hk]
  rw [hv, hoff] at h
  exact (loadHolds_ofK_iff (by ring)).mp h

/-! ## The named callees -/

/-- **A flat block holding at `C` makes `C` hold of each taken frame**, a dispatch's the callee its
selector names. -/
theorem os_calls_of_allOkF {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ {pre : List Stmt}, Whir.AllOk C rd σ pre → (∀ s ∈ pre, DispOk σ s) →
      (∀ s ∈ pre, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1) →
      ∀ c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ), c.taken = true →
        C c.f (c.args.map σ) (c.rets.map σ)
  | [], _, _, _, c, hc, _ => by simp at hc
  | s :: pre, h, hdo, hfl, c, hc, ht => by
    have h0 : Whir.StmtOk C rd σ s := h s (List.mem_cons_self ..)
    have h1 : Whir.AllOk C rd σ pre := fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
    have hdo1 : ∀ s ∈ pre, DispOk σ s := fun s' hs' ↦ hdo s' (List.mem_cons_of_mem _ hs')
    have hfl1 : ∀ s ∈ pre, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1 :=
      fun s' hs' ↦ hfl s' (List.mem_cons_of_mem _ hs')
    have ih := os_calls_of_allOkF h1 hdo1 hfl1 c
    match s, h0 with
    | .atom _, _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      exact ih hc ht
    | .call f args rets, h0 =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, List.map_cons,
        List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact h0
      · exact ih hc ht
    | .callIf cv f args, h0 =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, List.map_cons,
        List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [Main.mkCall, decide_eq_true_eq] at ht
        exact h0.2 ht
      · exact ih hc ht
    | .ret _, _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      exact ih hc ht
    | .ite .., _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      exact ih hc ht
    | .match_ .., _ =>
      simp only [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS] at hc
      exact ih hc ht
    | .dispatch x fs args rets, h0 =>
      simp only [List.filterMap_cons, Stmt.callSF, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · obtain ⟨j, -, hj64, hx⟩ := hdo _ (List.mem_cons_self ..)
        have hl := hfl _ (List.mem_cons_self ..) x fs args rets rfl
        have := (Whir.stmtOk_dispatch hx hj64 hl h0).2
        simp only [Main.mkCall]
        rw [hx, logG_spec hj64]
        exact this
      · exact ih hc ht

/-- `σ'` agrees with `σ` on every call statement's condition, selector, arguments and returns. -/
def CallAg (pre : List Stmt) (σ' σ : Val) : Prop :=
  ∀ s ∈ pre, ∀ vs, Stmt.callVarsS s = some vs → vs.map σ' = vs.map σ

theorem callAg_of_eq : ∀ {pre : List Stmt} {σ' σ : Val},
    (pre.filterMap Stmt.callVarsS).map (·.map σ') = (pre.filterMap Stmt.callVarsS).map (·.map σ) →
      CallAg pre σ' σ
  | [], _, _, _ => fun _ hs ↦ absurd hs List.not_mem_nil
  | s :: pre, σ', σ, h => by
    intro s' hs' vs hv
    rw [List.filterMap_cons] at h
    rcases List.mem_cons.mp hs' with rfl | hs'
    · rw [hv] at h
      simp only [List.map_cons, List.cons.injEq] at h
      exact h.1
    · cases e : Stmt.callVarsS s with
      | none => rw [e] at h; exact callAg_of_eq h s' hs' vs hv
      | some w =>
        rw [e] at h
        simp only [List.map_cons, List.cons.injEq] at h
        exact callAg_of_eq h.2 s' hs' vs hv

theorem callAg_v {pre : List Stmt} {σ' σ : Val} (h : CallAg pre σ' σ) {s : Stmt} (hs : s ∈ pre) {vs : List V}
    (hv : Stmt.callVarsS s = some vs) {v : V} (hvv : v ∈ vs) : σ' v = σ v :=
  List.map_inj_left.mp (h s hs vs hv) v hvv

/-- **Valuations agreeing on the call statements set up the same frames.** -/
theorem calls_congr : ∀ {pre : List Stmt} {σ' σ : Val}, CallAg pre σ' σ →
    (pre.filterMap (Stmt.callSF σ')).map (Main.mkCall σ') = (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)
  | [], _, _, _ => rfl
  | s :: pre, σ', σ, h => by
    have ih := calls_congr (pre := pre) fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')
    have h0 := h s List.mem_cons_self
    match s, h0 with
    | .atom _, _ => exact ih
    | .ite .., _ => exact ih
    | .match_ .., _ => exact ih
    | .ret _, _ => exact ih
    | .call f a r, _ => simpa [Stmt.callSF, Main.Stmt.callS, Main.mkCall] using ih
    | .callIf cv f a, h0 =>
      have e : σ' cv = σ cv := List.map_inj_left.mp (h0 _ rfl) cv List.mem_cons_self
      simpa [Stmt.callSF, Main.Stmt.callS, Main.mkCall, e] using ih
    | .dispatch x fs a r, h0 =>
      have e : σ' x = σ x := List.map_inj_left.mp (h0 _ rfl) x List.mem_cons_self
      simpa [Stmt.callSF, Main.mkCall, e] using ih

/-- A frame's arguments and returns are among its statement's call values. -/
theorem call_vars_mem {σ : Val} : ∀ {pre : List Stmt} {c : Call},
    c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) →
      ∃ s ∈ pre, ∃ vs, Stmt.callVarsS s = some vs ∧ (∀ v ∈ c.args, v ∈ vs) ∧ ∀ v ∈ c.rets, v ∈ vs
  | [], _, h => by simp at h
  | s :: pre, c, h => by
    rw [List.filterMap_cons] at h
    match s, h with
    | .atom _, h => obtain ⟨s', hs', r⟩ := call_vars_mem (pre := pre) h; exact ⟨s', List.mem_cons_of_mem _ hs', r⟩
    | .ite .., h => obtain ⟨s', hs', r⟩ := call_vars_mem (pre := pre) h; exact ⟨s', List.mem_cons_of_mem _ hs', r⟩
    | .match_ .., h => obtain ⟨s', hs', r⟩ := call_vars_mem (pre := pre) h; exact ⟨s', List.mem_cons_of_mem _ hs', r⟩
    | .ret _, h => obtain ⟨s', hs', r⟩ := call_vars_mem (pre := pre) h; exact ⟨s', List.mem_cons_of_mem _ hs', r⟩
    | .call f a r, h =>
      simp only [Stmt.callSF, Main.Stmt.callS, List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, List.mem_cons_self, _, rfl, fun v hv ↦ List.mem_append_left _ hv,
          fun v hv ↦ List.mem_append_right _ hv⟩
      · obtain ⟨s', hs', r⟩ := call_vars_mem (pre := pre) h; exact ⟨s', List.mem_cons_of_mem _ hs', r⟩
    | .callIf cv f a, h =>
      simp only [Stmt.callSF, Main.Stmt.callS, List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, List.mem_cons_self, _, rfl, fun v hv ↦ List.mem_cons_of_mem _ hv, fun v hv ↦ by
          simp [Main.mkCall] at hv⟩
      · obtain ⟨s', hs', r⟩ := call_vars_mem (pre := pre) h; exact ⟨s', List.mem_cons_of_mem _ hs', r⟩
    | .dispatch x fs a r, h =>
      simp only [Stmt.callSF, List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, List.mem_cons_self, _, rfl,
          fun v hv ↦ List.mem_cons_of_mem _ (List.mem_append_left _ hv),
          fun v hv ↦ List.mem_cons_of_mem _ (List.mem_append_right _ hv)⟩
      · obtain ⟨s', hs', r⟩ := call_vars_mem (pre := pre) h; exact ⟨s', List.mem_cons_of_mem _ hs', r⟩

theorem dispOk_congr {pre : List Stmt} {σ' σ : Val} (h : CallAg pre σ' σ) (hdo : ∀ s ∈ pre, DispOk σ s) :
    ∀ s ∈ pre, DispOk σ' s := fun s hs ↦ by
  match s, hs with
  | .dispatch x fs a r, hs =>
    have e : σ' x = σ x := callAg_v h hs rfl List.mem_cons_self
    obtain ⟨j, h1, h2, h3⟩ := hdo _ hs
    exact ⟨j, h1, h2, e.trans h3⟩
  | .atom _, _ => trivial
  | .call .., _ => trivial
  | .callIf .., _ => trivial
  | .ite .., _ => trivial
  | .match_ .., _ => trivial
  | .ret _, _ => trivial

/-- **A taken frame of a flat block holding at `C` under a valuation agreeing on the calls**: `C`
holds of it at the block's valuation. -/
theorem os_call_of_allOkAg {C : CallRel} {rd : Reader} {σ σ' : Val} {pre : List Stmt}
    (h : Whir.AllOk C rd σ' pre) (hag : CallAg pre σ' σ) (hdo : ∀ s ∈ pre, DispOk σ s)
    (hfl : ∀ s ∈ pre, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1)
    {c : Call} (hc : c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (ht : c.taken = true) :
    C c.f (c.args.map σ) (c.rets.map σ) := by
  obtain ⟨s, hs, vs, hv, ha, hr⟩ := call_vars_mem hc
  have e1 : c.args.map σ' = c.args.map σ := List.map_inj_left.mpr fun v hv' ↦ callAg_v hag hs hv (ha v hv')
  have e2 : c.rets.map σ' = c.rets.map σ := List.map_inj_left.mpr fun v hv' ↦ callAg_v hag hs hv (hr v hv')
  rw [← e1, ← e2]
  exact os_calls_of_allOkF h (dispOk_congr hag hdo) hfl c (by rw [calls_congr hag]; exact hc) ht

/-- **A named frame of a flat body proved at `osCR` on every memory holding `Lk`** is complete
placed on `Lk`, given its kind's placed statement at an optional bound. -/
theorem os_kid_namedX {Lk : Layout} {σ : Val} {pre : List Stmt}
    {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → ∃ σ', AllOk (osCR rd Sp (OsXOk κ Lk)) rd σ' pre ∧ CallAg pre σ' σ)
    (hdo : ∀ s ∈ pre, DispOk σ s)
    (hfl : ∀ s ∈ pre, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk)
    {c : Call} (hc : c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (ht : c.taken = true)
    {K : OsKind} (hK : osKindOf c.f = some K) {X : List E → List E → Prop}
    (hnamed : ∀ (args rets : List E), RegPtrs K.spec args (RegionL Lk) →
      (∀ rd, LowDef κ rd → MemL rd Lk → K.Pre rd args rets) → X args rets) :
    X (c.args.map σ) (c.rets.map σ) := by
  have hpre : ∀ rd, LowDef κ rd → MemL rd Lk → K.Pre rd (c.args.map σ) (c.rets.map σ) ∧
      OsXOk κ Lk K (c.args.map σ) := fun rd hl hm ↦ by
    obtain ⟨σ', hA, hag⟩ := hall rd hl hm
    have h := os_call_of_allOkAg hA hag hdo hfl hc ht
    unfold osCR at h; rw [hK] at h; exact h
  obtain ⟨rd0, hl0, hm0⟩ := hex
  exact hnamed _ _ (fixedReads_region (hpre rd0 hl0 hm0).2 ⟨rd0, hl0, hm0⟩)
    fun rd hl hm ↦ (hpre rd hl hm).1

theorem os_kid_namedO {Lk : Layout} {σ : Val} {pre : List Stmt}
    {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → ∃ σ', AllOk (osCR rd Sp (OsXOk κ Lk)) rd σ' pre ∧ CallAg pre σ' σ)
    (hdo : ∀ s ∈ pre, DispOk σ s)
    (hfl : ∀ s ∈ pre, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk)
    {c : Call} (hc : c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (ht : c.taken = true)
    {K : OsKind} (hK : osKindOf c.f = some K) {Bd : Option ℕ}
    (hnamed : ∀ (args rets : List E), RegPtrs K.spec args (RegionL Lk) →
      (∀ rd, LowDef κ rd → MemL rd Lk → K.Pre rd args rets) →
      CompleteAtO fs cert κ c.f Lk args (Returns rets) Bd) :
    CompleteAtO fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) Bd :=
  os_kid_namedX hall hdo hfl hex hc ht hK hnamed

end
end LeanVM.Guest.B1.Arm
