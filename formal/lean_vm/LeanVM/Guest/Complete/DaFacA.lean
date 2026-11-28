module

public import LeanVM.Guest.B1.VsC.LeafA
public import LeanVM.Guest.B1.Da.FactorsChk
public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.Complete.DaWords
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_factors__L»

/-!
# `da_factors`, placed

`da_factors(zs)` (`da_factors__L13_L7_L0`, `da_factors__L6_L7_L128`): a straight leaf, its one
`HeapBuf(128)` at the cursor `c`, on its forward evaluation (`callAtA_fwd`). Each depth loads its
power `Z (top - d)` from `zs`; each node `2^d + y` stores `Z (top - d) · Ŵ + 1 = factorAt Z top n`
(`facNode_val`), which the buffer holding `facCells Z top 7` has (`fac_callAtA`, from the
archive's `FacAt`). `facCOk` (the forward checker passes, the stores are the nodes', one `HeapBuf`
of `128` words) is decided by the kernel per specialization.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value

@[expose] public section

/-! ## Bodies of atoms -/

theorem atomsOf_map : ∀ as : List Atom, VsC.atomsOf (as.map Stmt.atom) = as
  | [] => rfl
  | a :: as => by rw [List.map_cons, VsC.atomsOf, atomsOf_map as]

theorem retOf_atoms : ∀ (as : List Atom) (vs : List V), VsC.retOf (as.map Stmt.atom ++ [.ret vs]) = some vs
  | [], _ => rfl
  | a :: as, vs => by rw [List.map_cons, List.cons_append, VsC.retOf, retOf_atoms as vs]

theorem flatMap_slEvs_atoms (σ : Val) : ∀ as : List Atom, (as.map Stmt.atom).flatMap (slEvs σ) = as.map Ev.atom
  | [] => rfl
  | a :: as => by rw [List.map_cons, List.flatMap_cons, flatMap_slEvs_atoms σ as]; rfl

theorem atoms_straight (as : List Atom) : (as.map Stmt.atom).all Stmt.straight = true :=
  List.all_eq_true.mpr fun s hs => by obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs; rfl

/-! ## The check -/

/-- The nodes' stores: node `2^d + y`'s factor into `factors[2^d + y]`. -/
def facStores (D : ℕ) : List Atom :=
  (List.range D).flatMap fun d => (List.range (2 ^ d)).map fun y =>
    .load (.n (facB d + 4 + 4 * y)) (.n (valf% «da_factors» "factors")) (2 ^ d + y)

/-- **`da_factors`, evaluated**: a placed straight leaf on its one parameter, its stores the
nodes', one `HeapBuf` of `128` words. -/
def facCOk (fn : Fn) (top D : ℕ) : Bool :=
  VsC.leafChecks 1 fn.body && atomsEqb (storesOf 1 fn.body) (facStores D) &&
    decide (fn.params = [.n 0]) &&
    decide (((facT top D).map Stmt.atom).filterMap Stmt.allocSz = [(.n (valf% «da_factors» "factors"), .inl 128)])

set_option maxRecDepth 100000 in
theorem facTop_cok : facCOk fn% «da_factors__L13_L7_L0» 13 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem facCell_cok : facCOk fn% «da_factors__L6_L7_L128» 6 7 = true := by decide +kernel

/-- The atoms of `facT`: the `HeapBuf`, the returned copy, a depth's power, a node's atoms. -/
theorem mem_facT {top D : ℕ} {a : Atom} (h : a ∈ facT top D) :
    a = .hint (.alloc (.n (valf% «da_factors» "factors")) 128) ∨
      a = .copy (.n (facB D)) (.n (valf% «da_factors» "factors")) ∨
      (∃ d < D, a = .load (.n (facB d)) (.n (valf% «da_factors» "zs")) (top - d)) ∨
      ∃ d < D, ∃ y < 2 ^ d, a ∈ facNodeA top d y := by
  simp only [facT, facDepthA, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_range, List.not_mem_nil, or_false] at h
  rcases h with h | ⟨d, hd, h | ⟨y, hy, h⟩⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl ⟨d, hd, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨d, hd, y, hy, h⟩))
  · exact Or.inr (Or.inl h)

theorem mem_facStores {D d y : ℕ} (hd : d < D) (hy : y < 2 ^ d) :
    Atom.load (.n (facB d + 4 + 4 * y)) (.n (valf% «da_factors» "factors")) (2 ^ d + y) ∈ facStores D :=
  List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hd, List.mem_map.mpr ⟨y, List.mem_range.mpr hy, rfl⟩⟩

theorem power_not_mem_facStores {D d top : ℕ} :
    Atom.load (.n (facB d)) (.n (valf% «da_factors» "zs")) (top - d) ∉ facStores D := by
  simp [facStores]

/-- **A node's value**, from its equations. -/
theorem facNode_val {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {top d y : ℕ}
    (hg : ∀ a ∈ facNodeA top d y, Good rd S w σ a) :
    σ (.n (facB d + 4 + 4 * y)) = σ (.n (facB d)) * ofK (wK (top - d) (y * 2 ^ (top - d + 1))) + 1 := by
  simp only [facNodeA, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Good] at hg
  obtain ⟨c, m, c1, a, -⟩ := hg
  rw [ite_pos' (show facB d < facB d + 1 + 4 * y + 1 ∧ facB d + 1 + 4 * y < facB d + 1 + 4 * y + 1 by
    constructor <;> omega)] at m
  rw [show facB d + 4 + 4 * y = facB d + 1 + 4 * y + 3 by omega, a, m, c, c1, facC_word, word_one]

theorem facCells_getElem {Z : ℕ → E} {top n : ℕ} (h1 : 1 ≤ n) (h2 : n < 2 ^ 7) :
    (facCells Z top 7)[n]'(by simp [facCells]; omega) = factorAt Z top n := by
  have h2' : n < 128 := by simpa using h2
  simp [facCells, h1, h2']

/-! ## `da_factors` -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxRecDepth 10000 in
/-- **`da_factors` completes placed** at any frame and cursor `c`, its buffer at `c` holding
`facCells Z top 7`, on the powers `Z` read through `g^bz`. -/
theorem fac_callAtA {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hlp : coreProgram.loop f = false) {top : ℕ} (hok : facOk fn top 7 = true)
    (hcok : facCOk fn top 7 = true) (k : ℕ) (Z : ℕ → E) (bz : ℕ) {R : ℕ → Prop}
    (hR : ∀ d < 7, R (bz + (top - d))) (fp c : ℕ) :
    CallAtA fs al cert k f [gen ^ bz] [gen ^ c] R (fun i => c ≤ i ∧ i < c + 128)
      (fun rd => HoldsWords rd [(c, facCells Z top 7)])
      (fun rd => ∀ d < 7, LoadHolds rd (gen ^ bz) (top - d) (Z (top - d))) VsC.PostQuiet (fs f) fp c (c + 128) := by
  simp only [facCOk, Bool.and_eq_true, decide_eq_true_eq] at hcok
  obtain ⟨⟨⟨hck, hst⟩, hpar⟩, halloc⟩ := hcok
  have hS := atomsEqb_sound hst
  unfold facOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨-, hok⟩ := hok
  split at hok
  case h_2 => exact absurd hok (by simp)
  rename_i A vs hsp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨rfl, htm⟩ := hok
  have hA := atomsEqb_sound htm
  subst hA
  have hb := splitBody_eq hsp
  have hck' := hck
  simp only [VsC.leafChecks, Bool.and_eq_true] at hck'
  obtain ⟨⟨hc, -⟩, -⟩ := hck'
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  have hmemT : ∀ a, Stmt.atom a ∈ fn.body → a ∈ facT top 7 := fun a ha => by
    rw [hb] at ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨a', h', he⟩ := List.mem_map.mp ha
      cases he
      exact h'
    · simp at ha
  have hmemB : ∀ a ∈ facT top 7, Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hb]; exact List.mem_append_left _ (List.mem_map_of_mem ha)
  have hat : VsC.atomsOf fn.body = facT top 7 := by rw [hb, VsC.atomsOf_append_ret, atomsOf_map]
  have hpre := atoms_straight (facT top 7)
  set w : ℕ → E := fun _ => ofK (addressOfIndex c) with hw
  refine VsC.callAtA_fwd w [128] [(c, facCells Z top 7)] hf hlp (by rw [hpar]; rfl) hck
    ⟨fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; right; simp [facCells],
      List.pairwise_singleton _ _⟩ (fun _ h => h) (fun i hi => by simpa using hi) ?_
  intro rd _ hW hp σ hσ
  have hG : ∀ a, Stmt.atom a ∈ fn.body → Good rd (storesOf 1 fn.body) w σ a := by
    rw [hσ]; exact VsC.fwd_good hc
  rw [hS] at hG
  have hbuf : ReadsAt rd (gen ^ c) (facCells Z top 7) := readsAt_gen_pow.mp hW
  have e0 : σ (.n (valf% «da_factors» "zs")) = gen ^ bz := by
    rw [hσ]; exact VsC.fwd_param (args := [gen ^ bz]) hc (i := 0) (by simp)
  have e1 : σ (.n (valf% «da_factors» "factors")) = gen ^ c := by
    have := hG _ (hmemB _ (List.mem_cons_self ..))
    simp only [Good] at this
    rw [this, hw, gen_pow_eq_ofK]
  have hz : ∀ d < 7, σ (.n (facB d)) = Z (top - d) := by
    intro d hd
    have h := hG (.load (.n (facB d)) (.n (valf% «da_factors» "zs")) (top - d)) (hmemB _
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hd,
        List.mem_cons_self ..⟩))))
    simp only [Good] at h
    rcases h with h | h
    · exact absurd h power_not_mem_facStores
    · rw [h, e0]
      unfold rdAt
      rw [(hp d hd).2]
      rfl
  have hnode : ∀ d < 7, ∀ y < 2 ^ d, σ (.n (facB d + 4 + 4 * y)) = factorAt Z top (2 ^ d + y) := by
    intro d hd y hy
    have hg : ∀ a ∈ facNodeA top d y, Good rd (facStores 7) w σ a := fun a ha =>
      hG a (hmemB a (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨d, List.mem_range.mpr hd, List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨y, List.mem_range.mpr hy, ha⟩)⟩))))
    rw [facNode_val hg, hz d hd, factorAt_node Z hy]
  have hn2 : ∀ d < 7, ∀ y < 2 ^ d, 2 ^ d + y < 2 ^ 7 := fun d hd y hy =>
    calc 2 ^ d + y < 2 ^ d + 2 ^ d := by omega
      _ = 2 ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hd
  have hevs : (VsC.atomsOf fn.body).map Ev.atom = ((facT top 7).map Stmt.atom).flatMap (slEvs σ) := by
    rw [hat, flatMap_slEvs_atoms]
  obtain ⟨hd1, ha1, -, -⟩ := straight_parts σ _ hpre
  refine ⟨fun a ha hns hn => ?_, fun _ a ha => ?_, fun a ha => ?_, fun vs hvs => ?_, ?_, ?_, ?_⟩
  · -- the side conditions
    have hns' : a ∉ facStores 7 := by rw [← hS]; exact hns
    rcases mem_facT (hmemT a ha) with rfl | rfl | ⟨d, hd, rfl⟩ | ⟨d, hd, y, hy, ha'⟩
    · simp [needsSide] at hn
    · simp [needsSide] at hn
    · simp only [Side, hns, ↓reduceIte]
      rw [e0]
      exact ⟨(hp d hd).1, by rw [(hp d hd).2]; rfl⟩
    · simp only [facNodeA, List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl | rfl | rfl | rfl
      · simp [needsSide] at hn
      · simp only [needsSide, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hn
        omega
      · simp [needsSide] at hn
      · simp [needsSide] at hn
      · exact absurd (by rw [show facB d + 1 + 4 * y + 3 = facB d + 4 + 4 * y by omega]; exact mem_facStores hd hy) hns'
  · -- the stores
    replace ha : a ∈ facStores 7 := by rw [← hS]; exact ha
    obtain ⟨d, hd, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    have hd := List.mem_range.mp hd
    have hy := List.mem_range.mp hy
    show LoadHolds rd (σ (.n (valf% «da_factors» "factors"))) (2 ^ d + y) (σ (.n (facB d + 4 + 4 * y)))
    rw [e1, hnode d hd y hy, ← facCells_getElem (by have := Nat.one_le_two_pow (n := d); omega) (hn2 d hd y hy)]
    exact hbuf _ _
  · -- exact
    rcases mem_facT (hmemT a ha) with rfl | rfl | ⟨d, hd, rfl⟩ | ⟨d, hd, y, hy, ha'⟩
    · trivial
    · trivial
    · trivial
    · simp only [facNodeA, List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl | rfl | rfl | rfl <;> trivial
  · -- the return
    rw [hb, retOf_atoms, Option.some.injEq] at hvs
    subst hvs
    have := hG _ (hmemB _ (List.mem_append_right _ (List.mem_singleton_self _)))
    simp only [Good] at this
    simp [this, e1]
  · rw [hevs, ha1, halloc]; rfl
  · rw [hevs, hd1, halloc]
    simp [bases, e1, gen_pow_eq_ofK]
  · intro A hA
    rw [hevs, loadAddrs_straight σ _ hpre] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
    rcases mem_facT ha with rfl | rfl | ⟨d, hd, rfl⟩ | ⟨d, hd, y, hy, ha'⟩
    · simp [stmtLoad?] at hq
    · simp [stmtLoad?] at hq
    · simp only [stmtLoad?, Option.some.injEq] at hq
      subst hq
      exact ⟨bz + (top - d), by rw [e0, gen_pow_eq_ofK]; exact Main.addr_ofK _ _, Or.inr (hR d hd)⟩
    · simp only [facNodeA, List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl | rfl | rfl | rfl
      all_goals simp only [stmtLoad?, reduceCtorEq, Option.some.injEq] at hq
      subst hq
      have := hn2 d hd y hy
      exact ⟨c + (2 ^ d + y), by rw [e1, gen_pow_eq_ofK]; exact Main.addr_ofK _ _, Or.inl ⟨by omega, by
        simp only [List.sum_cons, List.sum_nil]; omega⟩⟩

set_option maxRecDepth 100000 in
/-- **`da_factors__L13_L7_L0`**, placed: the tree over the cell index, the bits `13, 12, …, 7`. -/
theorem facTop_callAtA (k : ℕ) (Z : ℕ → E) (bz : ℕ) {R : ℕ → Prop} (hR : ∀ d < 7, R (bz + (13 - d)))
    (fp c : ℕ) :
    CallAtA fs al cert k "da_factors__L13_L7_L0" [gen ^ bz] [gen ^ c] R (fun i => c ≤ i ∧ i < c + 128)
      (fun rd => HoldsWords rd [(c, facCells Z 13 7)])
      (fun rd => ∀ d < 7, LoadHolds rd (gen ^ bz) (13 - d) (Z (13 - d))) VsC.PostQuiet
      (fs "da_factors__L13_L7_L0") fp c (c + 128) :=
  fac_callAtA find_da_factors_L13_L7_L0
    (by decide +kernel) facTop_ok facTop_cok k Z bz hR fp c

set_option maxRecDepth 100000 in
/-- **`da_factors__L6_L7_L128`**, placed: the tree inside a cell, the bits `6, 5, …, 0`. -/
theorem facCell_callAtA (k : ℕ) (Z : ℕ → E) (bz : ℕ) {R : ℕ → Prop} (hR : ∀ d < 7, R (bz + (6 - d)))
    (fp c : ℕ) :
    CallAtA fs al cert k "da_factors__L6_L7_L128" [gen ^ bz] [gen ^ c] R (fun i => c ≤ i ∧ i < c + 128)
      (fun rd => HoldsWords rd [(c, facCells Z 6 7)])
      (fun rd => ∀ d < 7, LoadHolds rd (gen ^ bz) (6 - d) (Z (6 - d))) VsC.PostQuiet
      (fs "da_factors__L6_L7_L128") fp c (c + 128) :=
  fac_callAtA find_da_factors_L6_L7_L128
    (by decide +kernel) facCell_ok facCell_cok k Z bz hR fp c

end
end LeanVM.Guest.Complete
