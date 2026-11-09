/-
  LeanVM.Guest.B1.KeccakGkr.LayerCA

  `keccak_layer`'s first sections, completely: the head, the product read and absorbed, the
  projection check and the squeeze of `s`, on the honest valuation.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerSecA
public import LeanVM.Guest.B1.KeccakGkr.LayerCBlock

/-!
# The product and `s`, completely

`layerA_complete`: on a valuation satisfying the equations of `headT ++ prodT ++ checkT ++ sqT`,
with the canonical capacity (and the waiting word's cells) in the arguments, the claim's record
and the product in memory (no store through `claim` or `cur`), and the honest projection check,
the four sections hold. The `KECCAK` inputs' canonicity and the residual atoms (`resid`: the
claim's and the stream's loads, the check, the challenge's `K` test) are kernel-checked lists.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- The head and the product. -/
def secA1 (first : ℕ) : List Stmt := headT first ++ prodT (.n 7) (muB first) (prodTab first)

/-- The check and the squeeze. -/
def secA2 (first : ℕ) : List Stmt := checkT (accL first) ++ sqT first

/-- The canonical arguments: the capacity, and the waiting word's cells. -/
def capA (first : ℕ) : List ℕ := if first = 1 then [0, 1, 2, 3, 4, 5, 6] else [0, 1, 2, 3, 4]

/-- The product's packed cells. -/
def packA (first : ℕ) : List ℕ := (prodTab first).flatMap fun p ↦ [p.fb + 6, p.fb + 8]

/-- The residual atoms of the head and the product: the claim's weights, the stream words. -/
def residA1 (first : ℕ) : List Atom :=
  (List.range 16).map (fun i ↦ .load (.n (muB first + i)) (.n 11) (6 + i)) ++
    (List.range 47).map fun k ↦ .load (.n ((prodTab first).getD k default).a) (.n 7) k

/-- The residual atoms of the check and the squeeze. -/
def residA2 (first : ℕ) : List Atom :=
  [.load (.n (accL first + 1)) (.n 11) 1, .load (.n (accL first + 4)) (.n 11) 0,
    .assertEq (.n (accL first + 3)) (.n (accL first + 4)), .assertInK (.n 871) (.n 874)]

theorem secA_atoms {first : ℕ} (hf : first < 2) :
    (secA1 first).all isAtom = true ∧ (secA2 first).all isAtom = true := by
  interval_cases first
  · exact ⟨by decide +kernel, by decide +kernel⟩
  · exact ⟨by decide +kernel, by decide +kernel⟩

theorem secA_canon1 {first : ℕ} (hf : first < 2) :
    canonChk (capA first ++ packA first) (atomsL ([] ++ secA1 first)) = true := by
  interval_cases first
  · decide +kernel
  · decide +kernel

theorem secA_canon2 {first : ℕ} (hf : first < 2) :
    canonChk (capA first ++ packA first) (atomsL (secA1 first ++ secA2 first)) = true := by
  interval_cases first
  · decide +kernel
  · decide +kernel

theorem secA_resid1 {first : ℕ} (hf : first < 2) : resid (atomsL (secA1 first)) = residA1 first := by
  interval_cases first
  · decide +kernel
  · decide +kernel

theorem secA_resid2 {first : ℕ} (hf : first < 2) : resid (atomsL (secA2 first)) = residA2 first := by
  interval_cases first
  · decide +kernel
  · decide +kernel

theorem prodTFrom_pack_mem {cur : V} {muB : ℕ} : ∀ {ps : List PPos} {k : ℕ} {p : PPos}, p ∈ ps →
    ∀ s ∈ fsPackT (.n p.a) p.fb dsObserve, s ∈ prodTFrom cur muB k ps
  | [], _, _, h, _, _ => absurd h (by simp)
  | q :: ps, k, p, h, s, hs => by
    rw [prodTFrom]
    rcases List.mem_cons.mp h with rfl | h
    · refine List.mem_append_left _ ?_
      simp only [prodPosT, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr hs)))
    · exact List.mem_append_right _ (prodTFrom_pack_mem h s hs)

/-- The product's packed cells are canonical on an evaluated valuation. -/
theorem packA_canonical {first : ℕ}
    (hg : ∀ s ∈ prodT (.n 7) (muB first) (prodTab first), GoodS rd S w σ s) :
    ∀ i ∈ packA first, IsCanonical128 (σ (.n i)) := by
  intro i hi
  simp only [packA, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨p, hp, hi⟩ := hi
  have hv := fsPack_vals_of_good (fun s hs ↦ hg s (prodTFrom_pack_mem hp s hs))
  have hc := fsPackVals_canonical (σ (.n p.a)) dsObserve
  rcases hi with rfl | rfl
  · rw [hv 6 (by norm_num)]; exact hc.1
  · rw [hv 8 (by norm_num)]; exact hc.2

theorem prodTab_a_eq {first : ℕ} (hf : first < 2) {prod : List E} (hpl : prod.length = 47)
    (hr : ReadsAt rd (σ (.n 7)) prod)
    (hr' : ReadsAt rd (σ (.n 7)) ((prodTab first).map fun p ↦ σ (.n p.a))) :
    (prodTab first).map (fun p ↦ σ (.n p.a)) = prod := by
  obtain ⟨hl, -⟩ := prodTab_facts first hf
  apply List.ext_getElem (by simp [hl, hpl])
  intro k h1 h2
  exact loadHolds_unique (hr' k h1) (hr k h2)

/-- **The product and `s`, completely.** -/
theorem layerA_complete {first : ℕ} (hf : first < 2) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ secA1 first ++ secA2 first, GoodS rd S w σ s)
    (hS7 : ∀ d off, Atom.load d (.n 7) off ∉ S) (hS11 : ∀ d off, Atom.load d (.n 11) off ∉ S)
    (hcap : ∀ i < 5, IsCanonical128 (σ (.n i)))
    {w0 : E} (hw : first = 1 → (σ (.n 5), σ (.n 6)) = Keccak.scalarCells w0 dsObserve)
    {c : KeccakClaim} (hmuL : c.mu.length = 16) (hval : LoadHolds rd (σ (.n 11)) 0 c.value)
    (hkap : LoadHolds rd (σ (.n 11)) 1 (sumE c.mu))
    (hmus : ∀ i < 16, LoadHolds rd (σ (.n 11)) (6 + i) (c.mu.getD i 0))
    {prod : List E} (hpl : prod.length = 47) (hprod : ReadsAt rd (σ (.n 7)) prod)
    (hproj : projectedOf c prod + σ (.n 13) * sumE c.mu = c.value) :
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (secA1 first ++ secA2 first) next kret := by
  obtain ⟨hall1, hall2⟩ := secA_atoms hf
  have hk1 := secA_canon1 hf
  have hk2 := secA_canon2 hf
  have hr1 := secA_resid1 hf
  have hr2 := secA_resid2 hf
  obtain ⟨hl, -, hacc, hlast, hallP, -⟩ := prodTab_facts first hf
  have hg1 : ∀ s ∈ secA1 first, GoodS rd S w σ s := fun s hs ↦ hg s (List.mem_append_left _ hs)
  have hg2 : ∀ s ∈ secA2 first, GoodS rd S w σ s := fun s hs ↦ hg s (List.mem_append_right _ hs)
  have hgP : ∀ s ∈ prodT (.n 7) (muB first) (prodTab first), GoodS rd S w σ s :=
    fun s hs ↦ hg1 s (List.mem_append_right _ hs)
  have hA : ∀ i ∈ capA first ++ packA first, IsCanonical128 (σ (.n i)) := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · have h56 : first = 1 → IsCanonical128 (σ (.n 5)) ∧ IsCanonical128 (σ (.n 6)) := by
        intro h1
        rw [show σ (.n 5) = (σ (.n 5), σ (.n 6)).1 from rfl,
          show σ (.n 6) = (σ (.n 5), σ (.n 6)).2 from rfl, hw h1]
        exact scalarCells_canonical w0 dsObserve
      interval_cases first
      · simp only [capA, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.mem_cons,
          List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact hcap _ (by norm_num)
      · simp only [capA, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hcap _ (by norm_num)
        · exact hcap _ (by norm_num)
        · exact hcap _ (by norm_num)
        · exact hcap _ (by norm_num)
        · exact hcap _ (by norm_num)
        · exact (h56 rfl).1
        · exact (h56 rfl).2
    · exact packA_canonical hgP i hi
  -- the head and the product
  have H1 : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (secA1 first) next kret := by
    refine block_holdsP (P := []) hall1 hσ hk1 (by simpa using hg1) hA ?_
    rw [hr1]
    intro a ha
    right
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact side_load (hS11 _ _) (hmus i (List.mem_range.mp hi))
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      exact side_load (hS7 _ _) (hprod k (by rw [hpl]; exact List.mem_range.mp hk))
  -- the projection's value
  have hP := H1 (kret := fun _ ↦ True) trivial
  rw [secA1, holdsList_append] at hP
  obtain ⟨-, hmu, hR, hP⟩ := headT_holds hP
  obtain ⟨H, -⟩ := (holdsList_atoms (allAtoms_of_all hallP) True (fun _ ↦ True)).1 hP
  have hrd : ReadsAt rd (σ (.n 7)) ((prodTab first).map fun p ↦ σ (.n p.a)) := by
    intro k hk
    have := prodTFrom_loads (prodTab first) 0 H k (by simpa using hk)
    simpa using this
  have hprodE := prodTab_a_eq hf hpl hprod hrd
  have hacc' : ov σ (accLast none (prodTab first)) = ((List.range (prodTab first).length).map
      fun j ↦ ((projR j).map fun i ↦ σ (.n (muB first + i))).sum *
        σ (.n ((prodTab first).getD j default).a)).sum := by
    have := accOk_sound (prodTab first) none 0 hacc H
    simpa [ov] using this
  have hμ : ∀ i < 16, σ (.n (muB first + i)) = c.mu.getD i 0 :=
    fun i hi ↦ loadHolds_unique (hmu i hi) (hmus i hi)
  have hp := proj_eq (muB := muB first) hl hmuL hμ
  rw [hlast, hl] at hacc'
  have hacc'' : ov σ (some (accL first)) = ((List.range 47).map fun j ↦
      ((projIdx j).map fun i ↦ σ (.n (muB first + i))).sum *
        σ (.n ((prodTab first).getD j default).a)).sum := by
    rw [hacc']
    refine congrArg List.sum (List.map_congr_left fun j hj ↦ ?_)
    rw [reader_proj hR (List.mem_range.1 hj)]
  rw [hl, ← hacc'', hprodE] at hp
  simp only [ov] at hp
  -- the check and the squeeze
  have H2 : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (secA2 first) next kret := by
    refine block_holdsP hall2 hσ hk2 hg hA ?_
    rw [hr2]
    have gc : ∀ s ∈ checkT (accL first), GoodS rd S w σ s :=
      fun s hs ↦ hg2 s (List.mem_append_left _ hs)
    simp only [checkT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, GoodS] at gc
    obtain ⟨g1, g2, g3, g4, -⟩ := gc
    have e1 := load_val g1 (hS11 _ _) hkap
    have e4 := load_val g4 (hS11 _ _) hval
    simp only [Good, V.n] at g2 g3
    have h13 : 13 < accL first := by unfold accL; split <;> norm_num
    rw [ite_pos' (by simp; omega)] at g2
    have hsq : ∀ s ∈ sqT first, GoodS rd S w σ s := fun s hs ↦ hg2 s (List.mem_append_right _ hs)
    have hch : ∀ s ∈ challengeT (.n 858) (.n 859) 871, GoodS rd S w σ s :=
      fun s hs ↦ hsq s (by simp only [sqT, List.mem_append]; exact Or.inr hs)
    have hkc : Good rd S w σ (.keccak (sqIns first) ((List.range 13).map fun k ↦ .n (858 + k))
        false false) :=
      hsq (.atom (.keccak (sqIns first) ((List.range 13).map fun k ↦ .n (858 + k)) false false))
        (by simp [sqT, keccakA])
    have c859 : IsCanonical128 (σ (.n 859)) := by
      obtain ⟨-, -, hc⟩ := good_keccak13 hkc
      have := hc ⟨1, by norm_num⟩
      simp only [cells13, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by norm_num : 1 < 13), Option.map_some, Option.getD_some,
        Function.comp_apply] at this
      rw [this]; exact canon_cellsOfState _ _ _
    obtain ⟨hok, -⟩ := challenge_complete (C := C) hch c859
    simp only [residA2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    refine ⟨Or.inr (side_load (hS11 _ _) hkap), Or.inr (side_load (hS11 _ _) hval), Or.inl ?_,
      Or.inl ⟨hok.2.2.2.1, hok.2.2.2.2.1⟩⟩
    show σ (.n (accL first + 3)) + σ (.n (accL first + 4)) = 0
    rw [g3, g2, e1, e4, ← hproj, hp]
    exact e_add_self _
  exact fun {next kret} hn ↦ by
    rw [holdsList_append]
    exact H1 (H2 hn)

end
end LeanVM.Guest.B1.VerifySub
