/-
  LeanVM.Guest.B1.KeccakGkr.LayerSecA

  `keccak_layer`'s first sections (G:2694-2726): the head, the readers, the product read and
  absorbed, the projection check, and the squeeze of `s`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT

/-!
# The product and `s`

`layerA_holds`: if `headT ++ prodT ++ checkT ++ sqT` holds, the product (the table's coefficients)
is read at the cursor, its projection plus `ι·κ` is the claim's value (`projectedOf`, V:1985-1996),
and `s` (value `877`) with the capacity after it (values `866 .. 870`) is `layerSq` of the
sponge the layer starts from (V:1997). The readers (`headT`, a straight line of sums over the
instance weights) are, by kernel evaluation of their masks, the projection's (`reader_proj`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The head -/

theorem headT_holds {first : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (headT first) next kret) :
    (∀ i < 5 + 2 * first, σ (.n (14 + i)) = σ (.n i)) ∧
      (∀ i < 16, LoadHolds rd (σ (.n 11)) (6 + i) (σ (.n (muB first + i)))) ∧
      (∀ t < 111, σ (.n (muB first + 16 + t)) =
        σ (.n (muB first + projA.getD t 0)) + σ (.n (muB first + projB.getD t 0))) ∧ next := by
  rw [headT, holdsList_append, holdsList_append, holdsList_map_atoms, holdsList_map_atoms,
    holdsList_map_atoms] at h
  simp only [Atom.Holds] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## The readers -/

/-- The readers' masks over the sixteen instance weights: weight `i` is bit `i`, reader `16 + t`
the `xor` of readers `projA t` and `projB t` (characteristic two). -/
def readerMasks (n : ℕ) : List ℕ :=
  (List.range n).foldl (fun acc t ↦ acc ++ [acc.getD (projA.getD t 0) 0 ^^^
    acc.getD (projB.getD t 0) 0]) ((List.range 16).map (2 ^ ·))

/-- A mask's sum of instance weights. -/
def linE (μ : ℕ → E) (m : ℕ) : E := ∑ j ∈ range 16, if m.testBit j then μ j else 0

theorem linE_xor (μ : ℕ → E) (a b : ℕ) : linE μ (a ^^^ b) = linE μ a + linE μ b := by
  simp only [linE, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp [e_add_self]

theorem linE_pow (μ : ℕ → E) {i : ℕ} (hi : i < 16) : linE μ (2 ^ i) = μ i := by
  unfold linE
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj])
    (fun h ↦ absurd (Finset.mem_range.2 hi) h)]
  simp

theorem readerMasks_succ (n : ℕ) : readerMasks (n + 1) = readerMasks n ++
    [(readerMasks n).getD (projA.getD n 0) 0 ^^^ (readerMasks n).getD (projB.getD n 0) 0] := by
  simp only [readerMasks, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem readerMasks_length : ∀ n, (readerMasks n).length = 16 + n
  | 0 => by simp [readerMasks]
  | n + 1 => by rw [readerMasks_succ, List.length_append, readerMasks_length n]; simp; omega

theorem proj_lt : ∀ t < 111, projA.getD t 0 < 16 + t ∧ projB.getD t 0 < 16 + t := by
  decide +kernel

/-- **The readers' values**: reader `i` is its mask's sum of the instance weights. -/
theorem readers_val {m : ℕ}
    (hR : ∀ t < 111, σ (.n (m + 16 + t)) = σ (.n (m + projA.getD t 0)) + σ (.n (m + projB.getD t 0))) :
    ∀ n ≤ 111, ∀ i < 16 + n,
      σ (.n (m + i)) = linE (fun j ↦ σ (.n (m + j))) ((readerMasks n).getD i 0) := by
  intro n
  induction n with
  | zero =>
    intro _ i hi
    simp only [readerMasks, List.range_zero, List.foldl_nil]
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
      linE_pow _ (by omega)]
  | succ n ih =>
    intro hn i hi
    rw [readerMasks_succ]
    rcases Nat.lt_or_ge i (16 + n) with hi' | hi'
    · rw [List.getD_append _ _ _ _ (by rw [readerMasks_length]; exact hi')]
      exact ih (by omega) i hi'
    · obtain rfl : i = 16 + n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [readerMasks_length]), readerMasks_length,
        Nat.sub_self, List.getD_cons_zero, linE_xor, show m + (16 + n) = m + 16 + n by ring,
        hR n (by omega), ih (by omega) _ (proj_lt n (by omega)).1,
        ih (by omega) _ (proj_lt n (by omega)).2]

theorem readerMasks_proj : ∀ k < 47, ∀ j < 16,
    ((readerMasks 111).getD (projOut.getD k 0) 0).testBit j = (projectLit.getD j 0).testBit k := by
  decide +kernel

theorem projOut_lt : ∀ k < 47, projOut.getD k 0 < 127 := by decide +kernel

/-- **Coefficient `k`'s reader** is the sum of the instance weights whose projection mask has bit
`k` (`projIdx`). -/
theorem reader_proj {m : ℕ}
    (hR : ∀ t < 111, σ (.n (m + 16 + t)) = σ (.n (m + projA.getD t 0)) + σ (.n (m + projB.getD t 0)))
    {k : ℕ} (hk : k < 47) :
    ((projR k).map fun i ↦ σ (.n (m + i))).sum = ((projIdx k).map fun i ↦ σ (.n (m + i))).sum := by
  simp only [projR, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [readers_val hR 111 le_rfl _ (by have := projOut_lt k hk; omega), projIdx,
    sum_filter_range _ _ 16, linE]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [readerMasks_proj k hk j (Finset.mem_range.1 hj)]

/-! ## The tables -/

/-- The waiting cells of a layer's start: the committed outputs' word's (`p0`, `p1`, copied to
`19`, `20`) for the first. -/
def pend0 (first : ℕ) : List (V × V) := if first = 1 then [(.n 19, .n 20)] else []

/-- The capacity cells the product leaves. -/
def capF (first : ℕ) : List V := if first = 1 then cap5 802 else cap5 812

/-- The waiting cells the product leaves. -/
def pendF (first : ℕ) : List (V × V) :=
  if first = 1 then [(.n 813, .n 815), (.n 825, .n 827), (.n 837, .n 839), (.n 849, .n 851)]
  else [(.n 823, .n 825), (.n 835, .n 837), (.n 847, .n 849)]

/-- The zero cells of the squeeze. -/
def sqZs (first : ℕ) : List V := if first = 1 then [] else [.n 856, .n 857]

theorem prodTab_facts (first : ℕ) (hf : first < 2) :
    (prodTab first).length = 47 ∧
    spChain (cap5 14, pend0 first) (prodTab first) = some (capF first, pendF first) ∧
    accOk projR none 0 (prodTab first) = true ∧ accLast none (prodTab first) = some (accL first) ∧
    (prodT (.n 7) (muB first) (prodTab first)).all isAtom = true ∧
    sqIns first = pendCellsV (pendF first) ++ sqZs first ++ capF first := by
  interval_cases first
  · exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩
  · exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

/-! ## The product section -/

/-- **The product section**: the coefficients read, absorbed, and their running projection. -/
theorem prodT_sound {cur : V} {muB : ℕ} {tab : List PPos} {st0 stF : List V × List (V × V)}
    {s : Fs} (hc : spChain st0 tab = some stF) (hacc : accOk projR none 0 tab = true)
    (hall : (prodT cur muB tab).all isAtom = true) (hs : SpOk σ s st0) {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (prodT cur muB tab) next kret) :
    ReadsAt rd (σ cur) (tab.map fun p ↦ σ (.n p.a)) ∧
      SpOk σ (s.absorbAll (tab.map fun p ↦ σ (.n p.a)) dsObserve) stF ∧
      ov σ (accLast none tab) = ((List.range tab.length).map fun j ↦
        ((projR j).map fun i ↦ σ (.n (muB + i))).sum * σ (.n (tab.getD j default).a)).sum ∧
      next := by
  obtain ⟨H, hn⟩ := (holdsList_atoms (allAtoms_of_all hall) next kret).1 h
  refine ⟨fun k hk ↦ ?_, spChain_sound tab 0 st0 stF s hc hs H, ?_, hn⟩
  · have := prodTFrom_loads tab 0 H k (by simpa using hk)
    simpa using this
  · have := accOk_sound tab none 0 hacc H
    simpa [ov] using this

/-- The projection of a table's coefficients, against `projectedOf`. -/
theorem proj_eq {muB : ℕ} {tab : List PPos} (hl : tab.length = 47) {c : KeccakClaim}
    (hmu : c.mu.length = 16) (hμ : ∀ i < 16, σ (.n (muB + i)) = c.mu.getD i 0) :
    ((List.range tab.length).map fun j ↦
        ((projIdx j).map fun i ↦ σ (.n (muB + i))).sum * σ (.n (tab.getD j default).a)).sum =
      projectedOf c (tab.map fun p ↦ σ (.n p.a)) := by
  rw [projectedOf, LeanVM.Protocol.KeccakGkr.sumE_eq_sum, hl, show productBits = 47 from rfl]
  refine congrArg List.sum (List.map_congr_left fun b hb ↦ ?_)
  have hb' : b < 47 := List.mem_range.1 hb
  have hz := sumE_zip_filterMap (fun mask ↦ mask.testBit b = true) c.mu rmfeProject
    (by rw [hmu, rmfeProject_length])
  have hz' : sumE ((List.zip c.mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit b then some m else none) =
      ∑ i ∈ range c.mu.length, if (rmfeProject.getD i 0).testBit b = true then c.mu.getD i 0
        else 0 := hz
  rw [hz', hmu, projIdx, sum_filter_range, rmfeProject_eq,
    List.getD_eq_getElem (tab.map _) _ (by simp [hl, hb']), List.getElem_map,
    List.getD_eq_getElem tab _ (by omega)]
  refine congrArg (· * _) (Finset.sum_congr rfl fun i hi ↦ ?_)
  rw [hμ i (Finset.mem_range.1 hi)]

/-! ## The check and the squeeze -/

theorem sqT_holds {first : ℕ} (hf : first < 2) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (sqT first) next kret) :
    (Atom.keccak (sqIns first) ((List.range 13).map fun k ↦ .n (858 + k)) false false).Holds rd σ ∧
      ChallengeOk σ (.n 858) (.n 859) 871 ∧
      (sqZs first).map σ = List.replicate (8 - 2 * (pendF first).length) 0 ∧ next := by
  interval_cases first
  · simp only [sqT, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, holdsList_append, holds_challengeT,
      keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
    obtain ⟨z0, z1, hk, hch, hn⟩ := h
    refine ⟨hk, hch, ?_, hn⟩
    simp [sqZs, pendF, z0, z1, word_zero]
  · simp only [sqT, ↓reduceIte, holdsList_append, holds_challengeT, keccakA, Stmt.HoldsList,
      Stmt.Holds] at h
    obtain ⟨hk, hch, hn⟩ := h
    exact ⟨hk, hch, by simp [sqZs, pendF], hn⟩

/-- **The product and `s`** (G:2694-2726 against V:1983-1997). -/
theorem layerA_holds {first : ℕ} (hf : first < 2) {y : ℕ} {c : KeccakClaim} {w : E}
    (hcr : ClaimRec rd (first = 1) (σ (.n 11)) c y)
    (hw : first = 1 → IsCanonical128 (σ (.n 5)) → (σ (.n 5), σ (.n 6)) = Keccak.scalarCells w dsObserve)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (headT first ++ prodT (.n 7) (muB first) (prodTab first) ++
      checkT (accL first) ++ sqT first) next kret) :
    ReadsAt rd (σ (.n 7)) ((prodTab first).map fun p ↦ σ (.n p.a)) ∧
      projectedOf c ((prodTab first).map fun p ↦ σ (.n p.a)) + σ (.n 13) * sumE c.mu = c.value ∧
      layerSq (plainStart first [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] w)
        ((prodTab first).map fun p ↦ σ (.n p.a)) = (σ (.n 877), ⟨(cap5 866).map σ, []⟩) ∧
      next := by
  obtain ⟨hl, hch, hacc, hlast, hall, hins⟩ := prodTab_facts first hf
  obtain ⟨hmuL, -, hval, hkap, hmus, -, -⟩ := hcr
  rw [holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨hcp, hmu, hR, h⟩ := headT_holds h
  have hs : SpOk σ (plainStart first [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] w)
      (cap5 14, pend0 first) := by
    refine ⟨?_, ?_⟩
    · simp only [plainStart, cap5, List.map_cons, List.map_nil]
      rw [hcp 0 (by omega), hcp 1 (by omega), hcp 2 (by omega), hcp 3 (by omega),
        hcp 4 (by omega)]
    · interval_cases first
      · simp [plainStart, pend0, PendOk]
      · simp only [plainStart, pend0, ↓reduceIte, PendOk, and_true]
        intro hc
        rw [hcp 5 (by omega), hcp 6 (by omega)]
        rw [hcp 5 (by omega)] at hc
        exact hw rfl hc
  obtain ⟨hrd, hsp, hacc', h⟩ := prodT_sound hch hacc hall hs h
  simp only [checkT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨hk, e2, e3, hv, heq, h⟩ := h
  obtain ⟨hkc, hchal, hz, hn⟩ := sqT_holds hf h
  have hμ : ∀ i < 16, σ (.n (muB first + i)) = c.mu.getD i 0 :=
    fun i hi ↦ loadHolds_unique (hmu i hi) (hmus i hi)
  refine ⟨hrd, ?_, ?_, hn⟩
  · have hp := proj_eq (muB := muB first) hl hmuL hμ
    rw [hlast, hl] at hacc'
    have hacc'' : ov σ (some (accL first)) = ((List.range 47).map fun j ↦
        ((projIdx j).map fun i ↦ σ (.n (muB first + i))).sum *
          σ (.n ((prodTab first).getD j default).a)).sum := by
      rw [hacc']
      refine congrArg List.sum (List.map_congr_left fun j hj ↦ ?_)
      rw [reader_proj hR (List.mem_range.1 hj)]
    rw [hl, ← hacc''] at hp
    simp only [ov] at hp
    rw [← hp, ← loadHolds_unique hk hkap, ← loadHolds_unique hv hval, ← e2, ← e3]
    exact eq_of_add_eq_zero' heq
  · have hpl : (pendF first).length ≤ 4 := by interval_cases first <;> decide
    obtain ⟨hperm, hout⟩ := spOk_perm hsp hkc hins hz hpl
    have h0 := hout 0 (by omega)
    have h1 := hout 1 (by omega)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : 0 < 13),
      List.getElem?_range (by omega : 1 < 13), Option.map_some, Option.getD_some,
      Nat.add_zero] at h0 h1
    have hc := challengeT_value hchal h0 h1
    have hcap := capOf_outs hout
    simp only [layerSq, Fs.squeeze]
    rw [hc, hcap]
    rfl

end
end LeanVM.Guest.B1.VerifySub
