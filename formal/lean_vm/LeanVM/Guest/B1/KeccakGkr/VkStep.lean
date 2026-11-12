/-
  LeanVM.Guest.B1.KeccakGkr.VkStep

  A step of `verify_keccak` (G:2950-2980): the claim's segment weights, its `ι` term, the layer.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkFirst
public import LeanVM.Guest.B1.KeccakGkr.KFormMath
public import LeanVM.Guest.B1.KeccakGkr.LayerHolds

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The tables -/

/-- The round constant bits of a step's segment are the positions `2^i - 1` of `iotaIdx`. -/
theorem iota_bits : ∀ s < 12, ∀ m < 2,
    (List.range 64).filter (fun z ↦ (keccakRC.getD (12 * (m + 1) - s - 1) 0).toNat.testBit z) =
      (iotaIdx s m).map (fun i ↦ 2 ^ i - 1) := by decide +kernel

theorem iotaIdx_ne : ∀ s < 12, ∀ m < 2, iotaIdx s m ≠ [] := by decide +kernel

theorem iotaIdx_sub : ∀ s < 12, ∀ m < 2, ∀ i ∈ iotaIdx s m, i ∈ iotaUsed s ∧ i < 7 := by
  decide +kernel

/-- The word of `g^22`, a claim record's size (`KC_SIZE`). -/
theorem word_g22 : word 4194304 0 = gen ^ 22 := by
  rw [show (4194304 : ℕ) = 2 ^ 22 from rfl]; exact word_two_pow (by decide)

/-- The words of `g^(22 s)` (the claim records' offsets; `VerifySub` reads `vkGw 5`). -/
def vkGw : ℕ → ℕ
  | 1 => 4194304
  | 2 => 17592186044416
  | 3 => 108
  | 4 => 452984832
  | 5 => 1899956092796928
  | 6 => 5200
  | 7 => 21810380800
  | 8 => 91479367430963200
  | 9 => 486848
  | 10 => 2041988513792
  | 11 => 8564720591351840768
  | _ => 0

/-- The words of `g^(22 s)`. -/
theorem vkGw_eq : ∀ s, 1 ≤ s → s < 12 → word (vkGw s) 0 = gen ^ (22 * s) := by
  intro s h1 h2
  rw [word_eOfNat, gen_pow_eq_ofK, ← gpowK_eq (by unfold u128Bound; omega)]
  show ofK (K.ofBits (vkGw s)) = ofK (gpowK (22 * s))
  congr 1
  interval_cases s <;> decide +kernel

/-! ## Chains of additions -/

theorem addChainT_holds {vs : List ℕ} (hne : vs ≠ []) {b : ℕ} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (addChainT vs b) next kret) :
    σ (.n (addChainV vs b)) = (vs.map fun v ↦ σ (.n v)).sum ∧ next := by
  rw [addChainT, holdsList_map_atoms] at h
  obtain ⟨hall, hn⟩ := h
  refine ⟨?_, hn⟩
  have step : ∀ k, k + 1 < vs.length →
      σ (.n (b + k)) = ((vs.take (k + 2)).map fun v ↦ σ (.n v)).sum := by
    intro k
    induction k with
    | zero =>
      intro hk
      have := hall 0 (by omega)
      simp only [Atom.Holds, ↓reduceIte, Nat.add_zero] at this
      rw [Nat.add_zero, this]
      rcases vs with _ | ⟨a, _ | ⟨b', rest⟩⟩
      · simp at hk
      · simp at hk
      · simp
    | succ k ih =>
      intro hk
      have := hall (k + 1) (by omega)
      simp only [Atom.Holds, show k + 1 ≠ 0 by omega, ↓reduceIte,
        show b + (k + 1) - 1 = b + k by omega] at this
      rw [show b + (k + 1) = b + (k + 1) from rfl, this, ih (by omega),
        List.take_add_one (i := k + 2), List.map_append, List.sum_append]
      simp [List.getElem?_eq_getElem (show k + 2 < vs.length by omega),
        List.getD_eq_getElem?_getD]
  rcases vs with _ | ⟨a, rest⟩
  · exact absurd rfl hne
  · rcases rest with _ | ⟨a', rest'⟩
    · simp [addChainV]
    · have := step (rest'.length) (by simp)
      rw [show (a :: a' :: rest').take (rest'.length + 2) = a :: a' :: rest' by simp] at this
      simp only [addChainV, List.length_cons, show ¬ (rest'.length + 1 + 1 ≤ 1) by omega,
        ↓reduceIte, show b + (rest'.length + 1 + 1) - 2 = b + rest'.length by omega]
      exact this

/-! ## The `ι` term from the flips -/

/-- **The `ι` term** (G:2971-2976): per segment the flips of its bits summed, times the segment's
weight (the values `w0`, `w1`). -/
theorem iotaSegT_holds {s b c w0 w1 : ℕ} (hs : s < 12) {F : ℕ → E} {g0 g1 : E}
    (hF : ∀ i ∈ iotaUsed s, σ (.n (flipOf s b i)) = F i)
    (hg0 : σ (.n w0) = g0) (hg1 : σ (.n w1) = g1) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (iotaSegT s b c w0 w1) next kret) :
    σ (.n (iotaSegEnd s c - 1)) = g0 * ((iotaIdx s 0).map F).sum +
      g1 * ((iotaIdx s 1).map F).sum ∧ next := by
  have hne0 := iotaIdx_ne s hs 0 (by omega)
  have hne1 := iotaIdx_ne s hs 1 (by omega)
  have hsum : ∀ m < 2, (((iotaIdx s m).map (flipOf s b)).map fun v ↦ σ (.n v)).sum =
      ((iotaIdx s m).map F).sum := by
    intro m hm
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun i hi ↦ ?_
    exact hF i (iotaIdx_sub s hs m hm i hi).1
  simp only [iotaSegT, holdsList_append] at h
  obtain ⟨a0, h⟩ := addChainT_holds (by simpa using hne0) h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨m0, h⟩ := h
  obtain ⟨a1, h⟩ := addChainT_holds (by simpa using hne1) h
  obtain ⟨m1, e, hn⟩ := h
  refine ⟨?_, hn⟩
  simp only [List.length_map] at m0 m1 e a0 a1
  rw [show iotaSegEnd s c - 1 = c + (iotaIdx s 0).length + (iotaIdx s 1).length
    by simp only [iotaSegEnd]; omega, e, m0, m1, hg0, hg1, a0, a1, hsum 0 (by omega),
    hsum 1 (by omega)]

/-! ## The `ι` term as the specification writes it -/

theorem filterMap_ite_eq {p : ℕ → Bool} (f : ℕ → E) (l : List ℕ) :
    l.filterMap (fun z ↦ if p z = true then some (f z) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- **`keccakIota`** (V:1990-1995) through the bit positions `2^i - 1` of the round constants. -/
theorem keccakIota_eq {τ s : ℕ} (hs : s < 12) (hτ : 4 ≤ τ) {c : KeccakClaim}
    (hpt : c.point.length = τ - 3) :
    keccakIota τ s c = (eqKernel [c.point.getD (τ - 4) 0]).getD 0 0 *
        ((iotaIdx s 0).map fun i ↦ c.weights.getD (2 ^ i - 1) 0).sum +
      (eqKernel [c.point.getD (τ - 4) 0]).getD 1 0 *
        ((iotaIdx s 1).map fun i ↦ c.weights.getD (2 ^ i - 1) 0).sum := by
  have hd : c.point.drop (τ - 4) = [c.point.getD (τ - 4) 0] := by
    rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp [show τ - 4 + 1 = c.point.length by omega]
  have hm : ∀ m < 2, sumE ((List.range 64).filterMap fun z ↦
      if (keccakRC.getD (keccakDepth * (m + 1) - s - 1) 0).toNat.testBit z then
        some (c.weights.getD z 0) else none) =
      ((iotaIdx s m).map fun i ↦ c.weights.getD (2 ^ i - 1) 0).sum := by
    intro m hm
    rw [filterMap_ite_eq, show keccakDepth = 12 from rfl, iota_bits s hs m hm, List.map_map,
      LeanVM.Protocol.KeccakGkr.sumE_eq_sum]
    rfl
  simp only [keccakIota, keccakSegments_eq, hd]
  rw [LeanVM.Protocol.KeccakGkr.sumE_eq_sum, listSum_range, Finset.sum_range_succ,
    Finset.sum_range_one]
  rw [hm 0 (by omega), hm 1 (by omega)]

/-! ## The flips -/

theorem flipsT_noRet (s b : ℕ) (j : ℕ) :
    Stmt.noRetList (flipT s ((iotaUsed s).getD j 0) (b + flipSz s * j)) = true := by
  unfold flipT
  split <;> rfl

theorem flipOf_mem {s b i : ℕ} (hi : i ∈ iotaUsed s) :
    flipOf s b i = flipV s b ((iotaUsed s).idxOf i) ∧ (iotaUsed s).idxOf i < (iotaUsed s).length ∧
      (iotaUsed s).getD ((iotaUsed s).idxOf i) 0 = i := by
  refine ⟨rfl, List.idxOf_lt_length_of_mem hi, ?_⟩
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hi), List.getElem_idxOf]

theorem iotaUsed_lt {s i : ℕ} (hi : i ∈ iotaUsed s) : i < 7 :=
  List.mem_range.1 (List.mem_filter.1 hi).1

/-- **The first claim's flips** (G:2966-2967): lane `0`'s weight times `x^(2^i - 1)`. -/
theorem flipsT_holds0 {b : ℕ} {L0 : E} (hL : ∀ v, LoadHolds rd (σ (.n 234)) 30 v → v = L0)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (flipsT 0 b) next kret) :
    (∀ i ∈ iotaUsed 0, σ (.n (flipOf 0 b i)) = L0 * gen ^ (2 ^ i - 1)) ∧ next := by
  rw [flipsT, holdsList_range_flatten _ _ (flipsT_noRet 0 b)] at h
  obtain ⟨hall, hn⟩ := h
  refine ⟨fun i hi ↦ ?_, hn⟩
  obtain ⟨e, hj, hgi⟩ := flipOf_mem (b := b) hi
  have hb := hall _ hj
  simp only [flipT, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, hgi,
    show flipSz 0 = 3 from rfl] at hb
  obtain ⟨l, c, m⟩ := hb
  have hi7 := iotaUsed_lt hi
  have hz : 2 ^ i - 1 < 64 := by
    have : 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [e, flipV, show flipSz 0 = 3 from rfl, show b + 3 * (iotaUsed 0).idxOf i + 3 - 1 =
    b + 3 * (iotaUsed 0).idxOf i + 2 by omega, m, c, hL _ l, word_two_pow hz]

/-- **A later claim's flips** (G:2968-2970): its weights at `2^i - 1`, read from its record's
`KC_FLIPS` table. -/
theorem flipsT_holdsL {s b : ℕ} (hs : s ≠ 0) {fl : E} {ws : List E}
    (hfl : LoadHolds rd (σ (.n 161)) (22 * s + 5) fl) (hws : ReadsAt rd fl (flipsOf ws))
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (flipsT s b) next kret) :
    (∀ i ∈ iotaUsed s, σ (.n (flipOf s b i)) = ws.getD (2 ^ i - 1) 0) ∧ next := by
  rw [flipsT, holdsList_range_flatten _ _ (flipsT_noRet s b)] at h
  obtain ⟨hall, hn⟩ := h
  refine ⟨fun i hi ↦ ?_, hn⟩
  obtain ⟨e, hj, hgi⟩ := flipOf_mem (b := b) hi
  have hb := hall _ hj
  simp only [flipT, hs, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, hgi,
    show flipSz s = 2 by simp [flipSz, hs]] at hb
  obtain ⟨l1, l2⟩ := hb
  rw [loadHolds_unique l1 hfl] at l2
  have hi7 := iotaUsed_lt hi
  have := hws i (by simp [flipsOf]; omega)
  simp only [flipsOf, List.getElem_map, List.getElem_range] at this
  rw [e, flipV, show flipSz s = 2 by simp [flipSz, hs], show b + 2 * (iotaUsed s).idxOf i + 2 - 1 =
    b + 2 * (iotaUsed s).idxOf i + 1 by omega]
  exact loadHolds_unique l2 this

/-! ## A later step -/

theorem claimRec_loads {P : ℕ} {k : ℕ} {v : E} (h : LoadHolds rd (σ (.n 161) * gen ^ (22 * k)) P v) :
    LoadHolds rd (σ (.n 161)) (22 * k + P) v := (loadHolds_mul_gen_pow rd _ _ _ _).1 h

/-- The step's segment weights (`eqtree_frame` of one coordinate, G:2953-2955): the claim's last
coordinate `r` read through `pt·pack_g`, `1 + r` and `r` at `b + 4`, `b + 5`. -/
theorem stepSeg_holds {b off : ℕ} {pp : E} {pt : List E} {τ : ℕ} (hτ : 4 ≤ τ)
    (hptL : pt.length = τ - 3) (hpt : ReadsAt rd pp pt) (h17 : σ (.n 18) = gen ^ (τ - 4))
    (hpp : LoadHolds rd (σ (.n 161)) off pp) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ ([.atom (.load (.n b) (.n 161) off),
      .atom (.mul (.n (b + 1)) (.n b) (.n 18))] ++ eqfLevel0T (.n (b + 1)) 0 (b + 2)) next kret) :
    (σ (.n (b + 4)) = (eqKernel [pt.getD (τ - 4) 0]).getD 0 0 ∧
      σ (.n (b + 5)) = (eqKernel [pt.getD (τ - 4) 0]).getD 1 0) ∧ next := by
  rw [holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨lcp, ecp, h⟩ := h
  obtain ⟨⟨lr, hseg⟩, hn⟩ := eqfLevel0T_holds h
  rw [ecp, loadHolds_unique lcp hpp, h17, loadHolds_mul_gen_pow, Nat.add_zero] at lr
  have hr : σ (.n (b + 2)) = pt.getD (τ - 4) 0 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique lr (hpt _ (by omega))
  refine ⟨⟨?_, ?_⟩, hn⟩
  · have := hseg 0 (by norm_num)
    rw [hr] at this
    rw [eqKernel_getD]
    simpa using this
  · have := hseg 1 (by norm_num)
    rw [hr] at this
    rw [eqKernel_getD]
    simpa using this

/-- **Step `s ≥ 1`** (G:2950-2980): the claim at `claims·g^(22 s)` (`cb·g^22`), its `ι` term, and
`keccak_layer` on it, writing the next claim at `claims·g^(22 (s + 1))` (`pn·g^22`, the value
`stepEnd s b - 7`). -/
theorem stepT_holdsL {s b : ℕ} (hs1 : 1 ≤ s) (hs : s < 12) {c0 c1 c2 c3 c4 cur cb pn : ℕ}
    {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h17 : σ (.n 18) = gen ^ (τ - 4))
    (h33 : σ (.n 34) = gen ^ ((τ - 3) / krStep)) (h47 : σ (.n 48) = gen ^ ((τ - 3) % krStep))
    (hcb : σ (.n cb) = σ (.n 161) * gen ^ (22 * (s - 1)))
    (hpn : σ (.n pn) = σ (.n 161) * gen ^ (22 * s)) {c : KeccakClaim}
    (hcr : ClaimRec rd ((0 : ℕ) = 1) (σ (.n 161) * gen ^ (22 * s)) c (τ - 3))
    (hK : keccak_layer_Spec rd) (htabs : WinTabs rd (σ (.n 11)))
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (stepT s b [c0, c1, c2, c3, c4] cur cb pn)
      next kret) :
    ∃ (xs : List E) (c' : KeccakClaim) (cap' : List E), ReadsAt rd (σ (.n cur)) xs ∧
      RunsTo (verifyKeccakLayer τ s c) ⟨[σ (.n c0), σ (.n c1), σ (.n c2), σ (.n c3), σ (.n c4)], []⟩
        xs c' ⟨cap', []⟩ ∧
      ClaimRec rd ((0 : ℕ) = 1) (σ (.n 161) * gen ^ (22 * (s + 1))) c' (τ - 3) ∧
      σ (.n (stepEnd s b - 7)) = σ (.n 161) * gen ^ (22 * (s + 1)) ∧
      ((List.range 6).map fun j ↦ σ (.n (stepEnd s b - 6 + j))) = cap' ++ [σ (.n cur) * gen ^ xs.length] ∧
      next := by
  have hs0 : s ≠ 0 := by omega
  have hcr0 := hcr
  obtain ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hpt⟩, lp, lanes, hlp, hlen, hlanes, hrest⟩ := hcr
  simp only [show ((0 : ℕ) = 1) = False by decide, decide_false, Bool.false_eq_true,
    ↓reduceIte] at hrest
  obtain ⟨lc, fl, loc, hlc, hlocL, hloc, hfl, hflips, hw⟩ := hrest
  simp only [stepT] at h
  rw [holdsList_append, holdsList_append, holdsList_append] at h
  -- the segment weights
  obtain ⟨⟨hg0, hg1⟩, h⟩ := stepSeg_holds (by omega) hptL hpt h17 (claimRec_loads hpp) h
  -- the flips
  obtain ⟨hfls, h⟩ := flipsT_holdsL hs0 (claimRec_loads hfl) hflips h
  -- the ι term
  obtain ⟨hio, h⟩ := iotaSegT_holds (F := fun i ↦ c.weights.getD (2 ^ i - 1) 0) hs hfls hg0 hg1 h
  rw [← keccakIota_eq hs (by omega) hptL] at hio
  -- the call
  set T := iotaSegEnd s (b + 6 + flipSz s * (iotaUsed s).length) with hT
  simp only [stepTailT, hs0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨z0, z1, e2, e3, e4, e5, e6, e7, hc, hn⟩ := h
  have hyg : σ (.n (T + 3)) = gen ^ (τ - 3) := by
    rw [e3, h17, e2, word_gen, ← pow_succ]; congr 1; omega
  have hcl : σ (.n (T + 5)) = σ (.n 161) * gen ^ (22 * s) := by
    rw [e5, e4, word_g22, hcb, mul_assoc, ← pow_add]; congr 2; omega
  have hout : σ (.n (T + 7)) = σ (.n 161) * gen ^ (22 * (s + 1)) := by
    rw [e7, e6, word_g22, hpn, mul_assoc, ← pow_add, Nat.mul_succ]
  have hm := hK 0 (by norm_num) _ _ hc
  simp only [List.map_cons, List.map_nil, List.map_append, z0, z1, word_zero, hyg, h33, h47, hcl,
    hout, hio] at hm
  simp only [MeaningKeccakLayer] at hm
  obtain ⟨xs, c', cap', hxs, hrun, hcr', hrets⟩ := hm htabs (τ - 3) s c 0 (by omega) (by omega) rfl
    rfl rfl hcr0 (fun h ↦ absurd h (by decide)) rfl
  rw [show τ - 3 + 3 = τ by omega] at hrun
  have hE : stepEnd s b = T + 14 := by simp only [stepEnd, ← hT, stepTailSz, hs0, ↓reduceIte]
  refine ⟨xs, c', cap', hxs, by simpa [plainStart] using hrun, hcr', ?_, ?_, hn⟩
  · rw [hE, show T + 14 - 7 = T + 7 by omega]; exact hout
  rw [← hrets, hE]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.map_append]
  rfl

/-! ## The first step -/

/-- **Step `0`** (G:2950-2980): the first claim, its `ι` term, and `keccak_layer` with the
committed outputs' value waiting in the sponge, writing the next claim at `claims·g^22`. -/
theorem stepT_holds0 {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h17 : σ (.n 18) = gen ^ (τ - 4))
    (h33 : σ (.n 34) = gen ^ ((τ - 3) / krStep)) (h47 : σ (.n 48) = gen ^ ((τ - 3) % krStep))
    {c : KeccakClaim} {L0 : E}
    (hcr : ClaimRec rd ((1 : ℕ) = 1) (σ (.n 161)) c (τ - 3))
    (hL0 : ∀ v, LoadHolds rd (σ (.n 234)) 30 v → v = L0)
    (hw0 : ∀ z < 64, c.weights.getD z 0 = L0 * gen ^ z)
    (hpk : FsPackOk σ (.n 158) (158 + 1) dsObserve)
    (hK : keccak_layer_Spec rd) (htabs : WinTabs rd (σ (.n 11)))
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (stepT 0 448 [152, 153, 154, 155, 156] 0 161 0)
      next kret) :
    ∃ (xs : List E) (c' : KeccakClaim) (cap' : List E), ReadsAt rd (σ (.n 5) * gen) xs ∧
      RunsTo (verifyKeccakLayer τ 0 c)
        ⟨[σ (.n 152), σ (.n 153), σ (.n 154), σ (.n 155), σ (.n 156)], [(σ (.n 158), dsObserve)]⟩
        xs c' ⟨cap', []⟩ ∧
      ClaimRec rd ((0 : ℕ) = 1) (σ (.n 161) * gen ^ (22 * 1)) c' (τ - 3) ∧
      σ (.n (stepEnd 0 448 - 7)) = σ (.n 161) * gen ^ (22 * 1) ∧
      ((List.range 6).map fun j ↦ σ (.n (stepEnd 0 448 - 6 + j))) =
        cap' ++ [σ (.n 5) * gen * gen ^ xs.length] ∧ next := by
  have hcr0 := hcr
  obtain ⟨-, hptL, -, -, -, ⟨pp, hpp, hpt⟩, -⟩ := hcr
  simp only [stepT] at h
  rw [holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨⟨hg0, hg1⟩, h⟩ := stepSeg_holds (b := 448) (off := 22 * 0 + 2) (by omega) hptL hpt h17
    (by simpa using hpp) h
  obtain ⟨hfl, h⟩ := flipsT_holds0 hL0 h
  obtain ⟨hio, h⟩ := iotaSegT_holds (F := fun i ↦ c.weights.getD (2 ^ i - 1) 0) (by norm_num)
    (fun i hi ↦ by
      have hi7 := iotaUsed_lt hi
      have hz : 2 ^ i - 1 < 64 := by
        have : 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [hfl i hi, hw0 _ hz]) hg0 hg1 h
  rw [← keccakIota_eq (by norm_num) (by omega) hptL] at hio
  set T := iotaSegEnd 0 (448 + 6 + flipSz 0 * (iotaUsed 0).length) with hT
  simp only [stepTailT, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, hc, hn⟩ := h
  have hcur : σ (.n (T + 1)) = σ (.n 5) * gen := by rw [e1, e0, word_gen]
  have hyg : σ (.n (T + 3)) = gen ^ (τ - 3) := by
    rw [e3, h17, e2, word_gen, ← pow_succ]; congr 1; omega
  have hout : σ (.n (T + 5)) = σ (.n 161) * gen ^ (22 * 1) := by rw [e5, e4, word_g22]
  have hm := hK 1 (by norm_num) _ _ hc
  simp only [List.map_cons, List.map_nil, List.map_append, hyg, h33, h47, hcur, hout, hio] at hm
  simp only [MeaningKeccakLayer] at hm
  obtain ⟨xs, c', cap', hxs, hrun, hcr', hrets⟩ := hm htabs (τ - 3) 0 c (σ (.n 158))
    (by omega) (by omega) rfl rfl rfl hcr0 (fun _ ↦ fsPackT_cells hpk) rfl
  rw [show τ - 3 + 3 = τ by omega] at hrun
  have hE : stepEnd 0 448 = T + 12 := by simp only [stepEnd, ← hT, stepTailSz, ↓reduceIte]
  refine ⟨xs, c', cap', hxs, by simpa [plainStart] using hrun, hcr', ?_, ?_, hn⟩
  · rw [hE, show T + 12 - 7 = T + 5 by omega]; exact hout
  rw [← hrets, hE]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.map_append]
  rfl

end
end LeanVM.Guest.B1.VerifySub
