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
* `qbpA c ws`: `query_win_ptrs`' words, level `l`'s window pointers `ws l` at `l·ligPosCap`;
  `winW … l p`: level `l`'s slice of them, its `level_positions` at `p`; `memL_winW`.
* `os_calls_of_allOkF`, `os_kid_namedO`: a named frame of a flat body proved at `osCR` on every
  memory holding `Lk` is complete placed on `Lk`, at an optional bound; `os_kid_namedX`: any statement its kind's
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

/-- `query_win_ptrs`' words: level `l`'s window pointers `ws l` at `l·ligPosCap`. -/
def qbpA (c : OsCfg) (ws : ℕ → List E) : List E :=
  (List.range (c.levels.length * ligPosCap)).map fun t ↦ (ws (t / ligPosCap)).getD (t % ligPosCap) 0

theorem qbpA_length (c : OsCfg) (ws : ℕ → List E) :
    (qbpA c ws).length = c.levels.length * ligPosCap := by simp [qbpA]

/-- Level `l`'s slice of `query_win_ptrs`, its `ligPosCap`-word window pointers `w`. -/
theorem memL_qbp_slice {rd : Reader} {c : OsCfg} {ws : ℕ → List E} {e : ℕ}
    (hm : ReadsAt rd (ofK (addressOfIndex e)) (qbpA c ws)) {l : ℕ} (hl : l < c.levels.length)
    (hlen : (ws l).length ≤ ligPosCap) : MemL rd [(e + l * ligPosCap, ws l)] := by
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  intro k hk
  have hk' : l * ligPosCap + k < c.levels.length * ligPosCap := by
    have : (l + 1) * ligPosCap ≤ c.levels.length * ligPosCap := Nat.mul_le_mul_right _ hl
    simp only at hk; rw [Nat.add_mul, one_mul] at this; omega
  have h := hm (l * ligPosCap + k) (by rw [qbpA_length]; exact hk')
  have hv : (qbpA c ws)[l * ligPosCap + k]'(by rw [qbpA_length]; exact hk') = (ws l)[k] := by
    simp only [qbpA, List.getElem_map, List.getElem_range]
    have hk2 : k < ligPosCap := by simp only at hk; omega
    rw [show (l * ligPosCap + k) / ligPosCap = l by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hk2, Nat.zero_add],
      show (l * ligPosCap + k) % ligPosCap = k by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk2],
      List.getD_eq_getElem _ _ hk]
  rw [hv] at h
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

/-- **A named frame of a flat body proved at `osCR` on every memory holding `Lk`** is complete
placed on `Lk`, given its kind's placed statement at an optional bound. -/
theorem os_kid_namedX {Lk : Layout} {σ : Val} {pre : List Stmt}
    {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → AllOk (osCR rd Sp (OsXOk κ Lk)) rd σ pre)
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
    have h := os_calls_of_allOkF (hall rd hl hm) hdo hfl c hc ht
    unfold osCR at h; rw [hK] at h; exact h
  obtain ⟨rd0, hl0, hm0⟩ := hex
  exact hnamed _ _ (fixedReads_region (hpre rd0 hl0 hm0).2 ⟨rd0, hl0, hm0⟩)
    fun rd hl hm ↦ (hpre rd hl hm).1

theorem os_kid_namedO {Lk : Layout} {σ : Val} {pre : List Stmt}
    {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → AllOk (osCR rd Sp (OsXOk κ Lk)) rd σ pre)
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
