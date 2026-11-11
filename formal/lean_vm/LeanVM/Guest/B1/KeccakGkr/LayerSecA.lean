/-
  LeanVM.Guest.B1.KeccakGkr.LayerSecA

  `keccak_layer`'s first sections (G:2669-2701): the head, the readers, the product read and
  absorbed, the projection check, and the squeeze of `s`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT

/-!
# The product and `s`

`layerA_holds`: if `headT ++ prodT ++ checkT ++ sqT` holds, the product (the table's coefficients)
is read at the cursor, its projection plus `ι·κ` is the claim's value (`projectedOf`, V:1985-1996),
the nonce at the cursor's word `47` passes the grind of `3` bits, and `s` (value
`layOff first + 544`) with the capacity after it (from `layOff first + 539`) is `layerSq` of the
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
    (∀ i < 5 + 2 * first, σ (.n (15 + i)) = σ (.n i)) ∧
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
`20`, `21`) for the first. -/
def pend0 (first : ℕ) : List (V × V) := if first = 1 then [(.n 20, .n 21)] else []

/-- The capacity cells the product leaves. -/
def capF (first : ℕ) : List V := if first = 1 then cap5 502 else cap5 505

/-- The waiting cells the product leaves. -/
def pendF (first : ℕ) : List (V × V) :=
  if first = 1 then [(.n 507, .n 508), (.n 512, .n 513), (.n 517, .n 518), (.n 522, .n 523)]
  else [(.n 510, .n 511), (.n 515, .n 516), (.n 520, .n 521)]

/-- The value the grind's nonce is read into. -/
def nonceV (first : ℕ) : ℕ := if first = 1 then 543 else 528

theorem prodTab_facts (first : ℕ) (hf : first < 2) :
    (prodTab first).length = 47 ∧
    spChain (cap5 15, pend0 first) (prodTab first) = some (capF first, pendF first) ∧
    accOk projR none 0 (prodTab first) = true ∧ accLast none (prodTab first) = some (accL first) ∧
    (prodT (.n 7) (muB first) (prodTab first)).all isAtom = true := by
  interval_cases first
  · exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

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

/-! ## The grind and the squeeze -/

/-- **A grind's permutation, then its challenge**: the permutation of the sponge `s'` that absorbed
the nonce `n` (`nonceState`) writes its outputs from `b`, `grind_check` of `3` bits passes on its
output `1`, and `s` is its output `0` copied to `b + 13`: the grind holds and `s`, with the
capacity cells `b + 8 ..`, is the grind's squeeze. -/
theorem grind_sq {s : Fs} {n : E} {b : ℕ}
    (hout : ∀ k (hk : k < 13), σ (((List.range 13).map fun j ↦ V.n (b + j)).getD k default) =
      cellsOfState (s.nonceState n) false ⟨k, hk⟩)
    (hpow : ((σ (.n (b + 1))).limb 0).lane.toNat % 2 ^ 3 = 0)
    (hch : ChallengeOk σ (.n b) (b + 13)) :
    s.GrindOk sGrindBits n ∧
      s.grindSqueeze sGrindBits n = (σ (.n (b + 13)), ⟨(cap5 (b + 8)).map σ, []⟩) := by
  have h0 := hout 0 (by omega)
  have h1 := hout 1 (by omega)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : 0 < 13),
    List.getElem?_range (by omega : 1 < 13), Option.map_some, Option.getD_some,
    Nat.add_zero] at h0 h1
  rw [sGrindBits_eq]
  obtain ⟨hok, hc, hs⟩ := grindSqueeze_cells (s := s) (by decide : (3 : ℕ) ≠ 0) n _ _ h0 h1 hpow
  have hcap := capOf_outs hout
  refine ⟨hok, Prod.ext ?_ ?_⟩
  · rw [hc, hch]
  · rw [hs, hcap]
    rfl

/-- **The grind and the squeeze** (`sqT`): from the cells the product leaves, the nonce read at
the cursor's word `47`, the grind holds and its squeeze is `s` (`layOff first + 544`) with the
capacity from `layOff first + 539`. -/
theorem sqT_holds {first : ℕ} (hf : first < 2) {s : Fs} (hs : SpOk σ s (capF first, pendF first))
    (hG : ∀ w, C (grindCheckName 3) [w, σ (.n 14)] [] → (w.limb 0).lane.toNat % 2 ^ 3 = 0)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (sqT first) next kret) :
    LoadHolds rd (σ (.n 7)) 47 (σ (.n (nonceV first))) ∧
      s.GrindOk sGrindBits (σ (.n (nonceV first))) ∧
      s.grindSqueeze sGrindBits (σ (.n (nonceV first))) =
        (σ (.n (layOff first + 544)), ⟨(cap5 (layOff first + 539)).map σ, []⟩) ∧ next := by
  interval_cases first
  · simp only [sqT, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, holdsList_append, holds_fsNonceT,
      holds_challengeT, keccakA, grindCallT, Stmt.HoldsList, Stmt.Holds] at h
    obtain ⟨⟨hl, hp⟩, hk, hg, hch, hn⟩ := h
    have hlen := pendOk_length hs.2
    have hs' : SpOk σ (s.absorb (σ (.n 528)) dsPowNonce)
        (capF 0, pendF 0 ++ [(.n 529, .n 530)]) := by
      have hne : s.pend.length ≠ rateScalars := by rw [hlen]; decide
      simp only [Fs.absorb, hne, ↓reduceIte]
      exact ⟨hs.1, pendOk_append hs.2 (fsPackT_cells hp)⟩
    obtain ⟨-, hout⟩ := spOk_perm hs' hk (zs := []) (by decide) rfl (by decide)
    have hg' := hG _ hg
    obtain ⟨hok, hsq⟩ := grind_sq (s := s) (n := σ (.n 528)) (b := 531) hout hg' hch
    exact ⟨hl, hok, hsq, hn⟩
  · simp only [sqT, ↓reduceIte, holdsList_append, holds_fsNonceT, holds_padRunT,
      holds_challengeT, keccakA, grindCallT, Stmt.HoldsList, Stmt.Holds] at h
    obtain ⟨hk1, ⟨hl, hp⟩, ⟨-, z1, z2, z3, z4⟩, hk2, hg, hch, hn⟩ := h
    have hlen := pendOk_length hs.2
    obtain ⟨-, hout1⟩ := spOk_perm hs hk1 (zs := []) (by decide) rfl (by decide)
    have hcap1 := capOf_outs hout1
    have hfull : s.pend.length = rateScalars := by rw [hlen]; decide
    have hs' : SpOk σ (s.absorb (σ (.n 543)) dsPowNonce) (cap5 538, [(.n 544, .n 545)]) := by
      simp only [Fs.absorb, hfull, ↓reduceIte]
      exact ⟨hcap1, fsPackT_cells hp, trivial⟩
    obtain ⟨-, hout⟩ := spOk_perm hs' hk2 (zs := [.n 547, .n 547, .n 547, .n 548, .n 549, .n 550])
      (by decide) (by simp [z1, z2, z3, z4]) (by decide)
    have hg' := hG _ hg
    obtain ⟨hok, hsq⟩ := grind_sq (s := s) (n := σ (.n 543)) (b := 551) hout hg' hch
    exact ⟨hl, hok, hsq, hn⟩

/-- **The product and `s`** (G:2669-2701 against V:1983-1997). -/
theorem layerA_holds {first : ℕ} (hf : first < 2) {y : ℕ} {c : KeccakClaim} {w : E}
    (hcr : ClaimRec rd (first = 1) (σ (.n 11)) c y)
    (hw : first = 1 → (σ (.n 5), σ (.n 6)) = Keccak.scalarCells w dsObserve)
    (hG : ∀ w, C (grindCheckName 3) [w, σ (.n 14)] [] → (w.limb 0).lane.toNat % 2 ^ 3 = 0)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (headT first ++ prodT (.n 7) (muB first) (prodTab first) ++
      checkT (accL first) ++ sqT first) next kret) :
    ReadsAt rd (σ (.n 7)) ((prodTab first).map fun p ↦ σ (.n p.a)) ∧
      projectedOf c ((prodTab first).map fun p ↦ σ (.n p.a)) + σ (.n 13) * sumE c.mu = c.value ∧
      LoadHolds rd (σ (.n 7)) 47 (σ (.n (nonceV first))) ∧
      ((plainStart first [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] w).absorbAll
        ((prodTab first).map fun p ↦ σ (.n p.a)) dsObserve).GrindOk sGrindBits
          (σ (.n (nonceV first))) ∧
      layerSq (plainStart first [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] w)
        ((prodTab first).map fun p ↦ σ (.n p.a)) (σ (.n (nonceV first))) =
        (σ (.n (layOff first + 544)), ⟨(cap5 (layOff first + 539)).map σ, []⟩) ∧
      next := by
  obtain ⟨hl, hch, hacc, hlast, hall⟩ := prodTab_facts first hf
  obtain ⟨hmuL, -, hval, hkap, hmus, -, -⟩ := hcr
  rw [holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨hcp, hmu, hR, h⟩ := headT_holds h
  have hs : SpOk σ (plainStart first [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] w)
      (cap5 15, pend0 first) := by
    refine ⟨?_, ?_⟩
    · simp only [plainStart, cap5, List.map_cons, List.map_nil]
      rw [hcp 0 (by omega), hcp 1 (by omega), hcp 2 (by omega), hcp 3 (by omega),
        hcp 4 (by omega)]
    · interval_cases first
      · simp [plainStart, pend0, PendOk]
      · simp only [plainStart, pend0, ↓reduceIte, PendOk, and_true]
        rw [hcp 5 (by omega), hcp 6 (by omega)]
        exact hw rfl
  obtain ⟨hrd, hsp, hacc', h⟩ := prodT_sound hch hacc hall hs h
  simp only [checkT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨hk, e2, e3, hv, heq, h⟩ := h
  obtain ⟨hnl, hok, hsq, hn⟩ := sqT_holds hf hsp hG h
  have hμ : ∀ i < 16, σ (.n (muB first + i)) = c.mu.getD i 0 :=
    fun i hi ↦ loadHolds_unique (hmu i hi) (hmus i hi)
  refine ⟨hrd, ?_, hnl, hok, hsq, hn⟩
  have hp := proj_eq (muB := muB first) hl hmuL hμ
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

end
end LeanVM.Guest.B1.VerifySub
