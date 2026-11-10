/-
  LeanVM.Guest.B1.Place.OsLiftLib

  The pieces of f128's `open_stacked` placed lift: the buffers' words read through the callees'
  layout, their addresses, the named callees and the pure loop helpers.
-/

module

public import LeanVM.Guest.B1.Place.OsCandF
public import LeanVM.Guest.B1.Place.OsKidsC

/-!
# The lift's pieces

* `osPtrF_eq`, `osPtrF_mul`: a buffer's pointer and its shifts as words of `g`'s powers.
* `bufL_get_mem`, `osMemF_of_lk`, `regionL_lk_buf`: the callees' layout `osLkF` holds every
  buffer but `query_win_ptrs` (`OsMemF`), and their words' addresses lie in it.
* `osH_of_lk`: on every memory defined low holding `osLkF` and where the caller's words hold the
  cursor's words and the window table, the dispatch relation `osCR rd (fun _ _ _ ↦ True)
  (OsXOk κ Lk)` satisfies `OsH`.
* `os_pure_completeAtD`: a helper placing nothing and calling only itself is complete placed on
  every memory where its `Rel` holds.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

theorem osPtrF_mul (c : OsCfg) (b j o : ℕ) :
    osPtrF c b j * gen ^ o = ofK (addressOfIndex (osBaseF c b j + o)) :=
  ofK_addr_mul_gen_pow _ _

theorem osBaseF_eq (c : OsCfg) (b : ℕ) {j : ℕ} (hj : j < (osSizesF c).length) :
    osBaseF c b j = b + ((osSizesF c).take j).sum :=
  os_bases_getD b _ j hj

/-- Buffer `j`'s entry of the buffers' layout. -/
theorem bufL_get {b : ℕ} {sizes : List ℕ} {own : List (List E)} (hl : own.length = sizes.length)
    {j : ℕ} (hj : j < sizes.length) :
    (bufL b sizes own)[j]'(by rw [bufL, List.length_zip, os_length_bases, hl, Nat.min_self]; exact hj) =
      ((bases b sizes).getD j 0, own.getD j []) := by
  simp only [bufL, List.getElem_zip]
  rw [List.getD_eq_getElem _ _ (by rw [os_length_bases]; exact hj),
    List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]

/-- **Buffer `j` but `query_win_ptrs` is in the callees' layout.** -/
theorem lk_mem {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout}
    (hl : own.length = (osSizesF c).length) {j : ℕ} (hj : j < (osSizesF c).length)
    (hne : j ≠ osIxQbp) : (osBaseF c b j, own.getD j []) ∈ osLkF c b own Lin := by
  have hjl : j < (bufL b (osSizesF c) own).length := by
    rw [bufL, List.length_zip, os_length_bases, hl, Nat.min_self]; exact hj
  refine List.mem_append_left _ (List.mem_eraseIdx_iff_getElem.mpr ⟨j, hjl, hne, ?_⟩)
  simp only [bufL, List.getElem_zip, osBaseF]
  rw [List.getD_eq_getElem _ _ (by rw [os_length_bases]; exact hj),
    List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]

/-- **A memory holding the callees' layout holds the buffers** but `query_win_ptrs`. -/
theorem osMemF_of_lk {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout}
    (hl : own.length = (osSizesF c).length) (hm : MemL rd (osLkF c b own Lin)) :
    OsMemF rd c b own := by
  intro j hj hne
  have h := hm _ (lk_mem (Lin := Lin) hl hj hne)
  unfold osPtrF
  exact h

theorem regionL_lk_buf {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout}
    (hl : own.length = (osSizesF c).length) {j t : ℕ} (hj : j < (osSizesF c).length)
    (hne : j ≠ osIxQbp) (ht : t < (own.getD j []).length) :
    RegionL (osLkF c b own Lin) (osBaseF c b j + t) :=
  ⟨_, lk_mem hl hj hne, by simp, by simpa using ht⟩

theorem regionL_lk_lin {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout} {i : ℕ}
    (h : RegionL Lin i) : RegionL (osLkF c b own Lin) i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  exact ⟨q, List.mem_append_right _ hq, h1, h2⟩

theorem memL_lin_of_lk {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout}
    (hm : MemL rd (osLkF c b own Lin)) : MemL rd Lin :=
  (Main.memL_append.mp hm).2

/-- **The dispatch relation on a memory holding the callees' layout satisfies `OsH`.** -/
theorem osH_of_lk {c : OsCfg} {b : ℕ} {own : List (List E)} {Lin : Layout} {cur tabs : E}
    {xs : List E} (hl : own.length = (osSizesF c).length)
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) {rd : Reader}
    (hlow : LowDef κ rd) (hm : MemL rd (osLkF c b own Lin)) :
    OsH (osCR rd (fun _ _ _ ↦ True) (OsXOk κ (osLkF c b own Lin))) rd c b own cur tabs xs := by
  obtain ⟨h1, h2⟩ := hLin rd hlow (memL_lin_of_lk hm)
  refine ⟨h1, h2, osMemF_of_lk hl hm, fun f K hK a r hp hx ↦ osCR_named hK hp ?_,
    fun f a r hK ↦ osCR_special hK trivial⟩
  intro q hq
  obtain ⟨ws, hw, hr⟩ := hx q hq
  refine ⟨ws, hw, fun rd' hl' hm' ↦ ?_⟩
  obtain ⟨g1, g2⟩ := hLin rd' hl' (memL_lin_of_lk hm')
  exact hr rd' g1 g2 (osMemF_of_lk hl hm')

/-! ## Pure helpers -/

/-- **A helper placing nothing and calling only itself is complete placed** where its `Rel`
holds. -/
theorem os_pure_completeAtD {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hp : Stmt.pureList [name] fn.body = true) {Lin : Layout} {args rets : List E}
    (h : ∀ rd, MemL rd Lin → coreProgram.Rel rd name args rets) (k : ℕ) :
    CompleteAtD fs cert k name Lin args (Returns rets) := by
  refine completeAt_of_rel_pureD (S := [name]) (fun g hg fn' hf' ↦ ?_) (List.mem_singleton_self _) h k
  rw [List.mem_singleton] at hg
  subst hg
  rw [hf] at hf'
  cases hf'
  exact hp

/-! ## Calls, layouts, regions -/

theorem mkCall_args (σ : Val) (x : Option V × String × List V × List V) :
    (mkCall σ x).args = x.2.2.1 := by obtain ⟨cv, f, a, r⟩ := x; cases cv <;> rfl

theorem mkCall_rets (σ : Val) (x : Option V × String × List V × List V) :
    (mkCall σ x).rets = x.2.2.2 := by obtain ⟨cv, f, a, r⟩ := x; cases cv <;> rfl

theorem mkCall_taken_none (σ : Val) {x : Option V × String × List V × List V} (h : x.1 = none) :
    (mkCall σ x).taken = true := by obtain ⟨cv, f, a, r⟩ := x; subst h; rfl

theorem mkCall_taken_some (σ : Val) {x : Option V × String × List V × List V} {v : E}
    (h : x.1.map σ = some v) : (mkCall σ x).taken = decide (v ≠ 0) := by
  obtain ⟨cv, f, a, r⟩ := x
  cases cv with
  | none => simp at h
  | some w => simp only [Option.map_some, Option.some.injEq] at h; subst h; rfl

/-- `CompleteAtD` on more words read. -/
theorem completeAtD_lin_mono {f : String} {Lin Lin' : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtD fs cert κ f Lin args Out)
    (hsub : ∀ q ∈ Lin, q ∈ Lin') : CompleteAtD fs cert κ f Lin' args Out := fun fp ↦ by
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm ↦ ?_⟩
  obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
  have h3 : Main.MemL rd Lin := fun q hq ↦ h2 q (hsub q hq)
  exact (hr rd hl (Main.memL_append.mpr ⟨h1, h3⟩)).mono fun i ⟨q, hq, hq1, hq2⟩ ↦
    ⟨q, hsub q hq, hq1, hq2⟩

/-- **The window table lies in the caller's words**, some low memory holding them. -/
theorem tabs_region {Lin : Layout} {tabs : E} {rd0 : Reader} (hl0 : LowDef κ rd0)
    (hm0 : MemL rd0 Lin) (hT : ∀ rd, LowDef κ rd → MemL rd Lin → WinTabs rd tabs) {t : ℕ}
    (ht : t < 128) : ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧ RegionL Lin i :=
  os_addr_in_regionL (fun rd hl hm ↦ (hT rd hl hm t (lt_of_lt_of_le ht (by norm_num [winTabBits]))).2) hl0 hm0

/-- A pointer shifted by `g^j`'s powers. -/
theorem ptr_shift_limb (e o j p t : ℕ) :
    (ofK (addressOfIndex e) * gen ^ o * (gen ^ j) ^ p).limb 0 * addressOfIndex t =
      addressOfIndex (e + o + j * p + t) := by
  rw [ofK_addr_shift, limb_ofK_addr]

theorem ptr_pow_limb (e j p t : ℕ) :
    (ofK (addressOfIndex e) * (gen ^ j) ^ p).limb 0 * addressOfIndex t =
      addressOfIndex (e + j * p + t) := by
  rw [← pow_mul, ofK_addr_mul_gen_pow, limb_ofK_addr]

theorem pow_div_lt' {q a b : ℕ} (h : q < 2 ^ (a + b)) : q / 2 ^ a < 2 ^ b :=
  Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact h)

end
end LeanVM.Guest.B1
