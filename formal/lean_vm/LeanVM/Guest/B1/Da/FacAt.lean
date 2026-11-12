/-
  LeanVM.Guest.B1.Da.FacAt

  `da_factors` placed (G:4627-4635): its `HeapBuf` of node factors, returned, within its frame and
  its buffer, by its evaluated valuation.
-/

module

public import LeanVM.Guest.B1.Da.FacCChk
public import LeanVM.Guest.B1.Da.FactorsChk
public import LeanVM.Guest.B1.Da.HonestDefs
public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.B1.Tables.FlatAtT

/-!
# `da_factors`, placed

The honest valuation is the body evaluated (`Fwd.ev`) from the powers' pointer `g^c`, the
`HeapBuf` the oracle's `g^b` at `b = fp + fs f`. Each depth loads its power `Z (top - d)`; each node
computes `Z (top - d) · Ŵ + 1 = factorAt Z top n` (`fac_node_good`), which its store finds in the
buffer holding `facCells Z top D`. `fac_completeAtB`: complete, placed, within `fs f + 256`,
returning the buffer (`facOut`); `fac14_completeAtB`, `fac7_completeAtB`: the two
specializations.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB completeAt_flatOutDTB flatCalls flatMap_loadsEv noLoadIte)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The atoms of `facT`: the `HeapBuf`, the returned copy, a depth's power, a node's atoms. -/
theorem mem_facT {top D : ℕ} {a : Atom} (h : a ∈ facT top D) :
    a = .hint (.alloc (.n 1) 256) ∨ a = .copy (.n (facB D)) (.n 1) ∨
    (∃ d < D, a = .load (.n (facB d)) (.n 0) (top - d)) ∨
    ∃ d < D, ∃ y < 2 ^ d, a ∈ facNodeA top d y := by
  simp only [facT, facDepthA, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_range, List.not_mem_nil, or_false] at h
  rcases h with h | ⟨d, hd, h | ⟨y, hy, h⟩⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl ⟨d, hd, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨d, hd, y, hy, h⟩))
  · exact Or.inr (Or.inl h)

variable {rd : Reader}

/-- **A node's value**, from its equations. -/
theorem fac_node_good {S : List Atom} {w : ℕ → E} {σ : Val} {top d y : ℕ}
    (hg : ∀ a ∈ facNodeA top d y, Good rd S w σ a) :
    σ (.n (facB d + 4 + 4 * y)) =
      σ (.n (facB d)) * ofK (wK (top - d) (y * 2 ^ (top - d + 1))) + 1 := by
  simp only [facNodeA, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Good] at hg
  obtain ⟨c, m, c1, a, -⟩ := hg
  rw [ite_pos' (show facB d < facB d + 1 + 4 * y + 1 ∧ facB d + 1 + 4 * y < facB d + 1 + 4 * y + 1 by
    constructor <;> omega)] at m
  rw [show facB d + 4 + 4 * y = facB d + 1 + 4 * y + 3 by omega, a, m, c, c1, facC_word, word_one]

theorem fac_store_not_mem {D d : ℕ} {top : ℕ} :
    Atom.load (.n (facB d)) (.n 0) (top - d) ∉ facStores D := by
  simp [facStores]

theorem facCells_get {Z : ℕ → E} {top D n : ℕ} (h1 : 1 ≤ n) (h2 : n < 2 ^ D) (hD : 2 ^ D ≤ 256) :
    (facCells Z top D)[n]'(by simp [facCells]; omega) = factorAt Z top n := by
  simp [facCells, h1, h2]

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`da_factors` is complete, placed, within its frame and its buffer**, returning the buffer
of its nodes' factors, the powers `Z` read at `g^c`. -/
theorem fac_completeAtB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) {top D : ℕ} (hok : facOk fn top D = true)
    (hcok : facCOk fn top D = true) (hD : D ≤ 8) {Lin : Layout} {c : ℕ} {Z : ℕ → E}
    (hzs : ∀ rd, MemL rd Lin → ∀ d < D, LoadHolds rd (gen ^ c) (top - d) (Z (top - d)))
    (hzr : ∀ d < D, RegionL Lin (c + (top - d))) :
    CompleteAtDTB fs cert 16 f Lin [gen ^ c] (facOut Z top D) (fun _ => True) (fs f + 256) := by
  have h2D : 2 ^ D ≤ 256 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hD) (by norm_num)
  unfold facOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨rfl, htm⟩ := hok
    have hA := atomsEqb_sound htm
    subst hA
    have hb := splitBody_eq hsp
    unfold facCOk at hcok
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hcok
    obtain ⟨⟨⟨⟨c', hchk⟩, hst⟩, haddr⟩, halloc⟩ := hcok
    have hS := atomsEqb_sound hst
    have hflat : ((facT top D).map Stmt.atom).all Core.Stmt.flat = true :=
      List.all_eq_true.mpr fun s hs => by obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs; rfl
    refine (completeAt_flatOutDTB (fs := fs) (cert := cert) hf hl 16 Lin [gen ^ c]
      (fun fp ↦ [ofK (addressOfIndex (fp + fs f))]) (facOut Z top D) hb hflat haddr [256]
      (fun _ ↦ [facCells Z top D]) (fun _ ↦ by simp [facCells])
      (fun fp ↦ ⟨fp + fs f, by rw [gen_pow_eq_ofK], by simp [bufL, bases]⟩) (fun _ ↦ [])
      (fun _ ↦ True) [] [] 0 (fun _ ↦ trivial) (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)
      (fun _ _ h ↦ absurd h (by simp)) (fun _ _ _ _ _ h ↦ absurd h (by simp)) ?_).mono
      (by simp) fun _ _ ↦ trivial
    intro fp outs ho rd _ hB hLin
    set b := fp + fs f with hbdef
    let w : ℕ → E := fun _ => ofK (addressOfIndex b)
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w [gen ^ c] fn.body) := ⟨_, rfl⟩
    obtain ⟨-, -, hgs⟩ := ev_spec rd w fn.body [gen ^ c] hchk
    rw [show [gen ^ c].length = 1 from rfl, hS, ← hσ] at hgs
    have hg : ∀ a ∈ facT top D, Good rd (facStores D) w σ a := fun a ha =>
      hgs (.atom a) (by rw [hb]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have e0 : σ (.n 0) = gen ^ c := by rw [hσ]; exact ev_params rd w (l := [gen ^ c]) hchk (by simp)
    have e1 : σ (.n 1) = gen ^ b := by
      have := hg _ (List.mem_cons_self ..)
      simp only [Good] at this
      rw [this, gen_pow_eq_ofK]
    have hcopy : σ (.n (facB D)) = σ (.n 1) :=
      hg _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hz : ∀ d < D, σ (.n (facB d)) = Z (top - d) := by
      intro d hd
      have h := hg (.load (.n (facB d)) (.n 0) (top - d)) (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hd,
          List.mem_cons_self ..⟩)))
      simp only [Good] at h
      rcases h with h | h
      · exact absurd h fac_store_not_mem
      · rw [h, e0]
        unfold rdAt
        rw [(hzs rd hLin d hd).2]
        rfl
    have hmemb : (b, facCells Z top D) ∈ bufL b [256] [facCells Z top D] := List.mem_singleton_self _
    have hbuf : ReadsAt rd (gen ^ b) (facCells Z top D) := reads_of_memL hB hmemb
    have hat : ∀ a ∈ facT top D, a.Holds rd σ := by
      refine atoms_holds hg fun a ha hns => ?_
      rcases mem_facT ha with rfl | rfl | ⟨d, hd, rfl⟩ | ⟨d, hd, y, hy, ha'⟩
      · simp [needsSide] at hns
      · simp [needsSide] at hns
      · left
        show LoadHolds rd (σ (.n 0)) (top - d) (σ (.n (facB d)))
        rw [e0, hz d hd]
        exact hzs rd hLin d hd
      · have hgn : ∀ a ∈ facNodeA top d y, Good rd (facStores D) w σ a := fun a' ha'' =>
          hg a' (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.mpr
            ⟨d, List.mem_range.mpr hd, List.mem_cons_of_mem _ (List.mem_flatMap.mpr
              ⟨y, List.mem_range.mpr hy, ha''⟩)⟩)))
        simp only [facNodeA, List.mem_cons, List.not_mem_nil, or_false] at ha'
        rcases ha' with rfl | rfl | rfl | rfl | rfl
        · simp [needsSide] at hns
        · simp only [needsSide, Bool.not_eq_true'] at hns
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hns
          omega
        · simp [needsSide] at hns
        · simp [needsSide] at hns
        · left
          have hn1 : 1 ≤ 2 ^ d + y := by have := Nat.one_le_two_pow (n := d); omega
          have hn2 : 2 ^ d + y < 2 ^ D := by
            calc 2 ^ d + y < 2 ^ d + 2 ^ d := by omega
              _ = 2 ^ (d + 1) := by rw [pow_succ]; ring
              _ ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) hd
          show LoadHolds rd (σ (.n 1)) (2 ^ d + y) (σ (.n (facB d + 1 + 4 * y + 3)))
          rw [show facB d + 1 + 4 * y + 3 = facB d + 4 + 4 * y by omega, fac_node_good hgn,
            hz d hd, ← factorAt_node Z hy, e1, ← facCells_get hn1 hn2 h2D]
          exact hbuf _ _
    refine ⟨σ, by rw [hparams]; simp [e0], fun s hs => ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs
      trivial
    · rw [hb]
      refine holdsList_straight _ _ _ _ (fun s hs => ?_) ?_
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
        exact hat a ha
      · simp [hcopy, e1, gen_pow_eq_ofK]
    · rw [halloc]; rfl
    · rw [halloc]; simp [bases, e1, gen_pow_eq_ofK]
    · have : ((facT top D).map Stmt.atom).filterMap (Stmt.callSF σ) = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro s hs
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs
        rfl
      simp only [flatCalls, this, List.map_nil]
      match outs, ho with
      | [], _ => exact True.intro
    · rw [flatMap_loadsEv _ _ (List.all_eq_true.mpr fun s hs => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs; rfl)]
      intro q hq
      obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
      rcases mem_facT ha with rfl | rfl | ⟨d, hd, rfl⟩ | ⟨d, hd, y, hy, ha'⟩
      · simp [Stmt.loadS] at hq
      · simp [Stmt.loadS] at hq
      · simp only [Stmt.loadS, Option.some.injEq] at hq
        subst hq
        exact ⟨c + (top - d), by rw [e0, limb0_gen_pow_mul], Or.inl (hzr d hd)⟩
      · simp only [facNodeA, List.mem_cons, List.not_mem_nil, or_false] at ha'
        rcases ha' with rfl | rfl | rfl | rfl | rfl
        all_goals simp only [Stmt.loadS, reduceCtorEq, Option.some.injEq] at hq
        subst hq
        have hn2 : 2 ^ d + y < 256 := by
          calc 2 ^ d + y < 2 ^ d + 2 ^ d := by omega
            _ = 2 ^ (d + 1) := by rw [pow_succ]; ring
            _ ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) hd
            _ ≤ 256 := h2D
        exact ⟨b + (2 ^ d + y), by rw [e1, limb0_gen_pow_mul], Or.inr
          (regionL_of_mem hmemb (by simpa [facCells] using hn2))⟩
  · exact absurd hok (by simp)

/-- **`da_factors__L14_L7_L0`**, placed: the tree over the cell index, the bits `14, 13, …, 8`. -/
theorem fac14_completeAtB {Lin : Layout} {c : ℕ} {Z : ℕ → E}
    (hzs : ∀ rd, MemL rd Lin → ∀ d < 7, LoadHolds rd (gen ^ c) (14 - d) (Z (14 - d)))
    (hzr : ∀ d < 7, RegionL Lin (c + (14 - d))) :
    CompleteAtDTB fs cert 16 "da_factors__L14_L7_L0" Lin [gen ^ c] (facOut Z 14 7) (fun _ => True)
      (fs "da_factors__L14_L7_L0" + 256) :=
  fac_completeAtB fs cert find_da_factors_L14_L7_L0
    (by rw [Program.loop_of_find? find_da_factors_L14_L7_L0]; decide +kernel) fac14_ok fac14_cok
    (by norm_num) hzs hzr

/-- **`da_factors__L7_L8_L128`**, placed: the tree inside a cell, the bits `7, 6, …, 0`. -/
theorem fac7_completeAtB {Lin : Layout} {c : ℕ} {Z : ℕ → E}
    (hzs : ∀ rd, MemL rd Lin → ∀ d < 8, LoadHolds rd (gen ^ c) (7 - d) (Z (7 - d)))
    (hzr : ∀ d < 8, RegionL Lin (c + (7 - d))) :
    CompleteAtDTB fs cert 16 "da_factors__L7_L8_L128" Lin [gen ^ c] (facOut Z 7 8)
      (fun _ => True) (fs "da_factors__L7_L8_L128" + 256) :=
  fac_completeAtB fs cert find_da_factors_L7_L8_L128
    (by rw [Program.loop_of_find? find_da_factors_L7_L8_L128]; decide +kernel) fac7_ok fac7_cok
    (by norm_num) hzs hzr

end
end LeanVM.Guest.B1.Da
