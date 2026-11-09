/-
  LeanVM.Guest.B1.Opening.QueriesComplete3

  The completeness of `walk_path`: the Merkle path and the cap leaf of a query, in the walk's own
  frame.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete2

/-!
# `walk_path`, completeness (lean_ethereum.py:1308-1343 at 40f877dc)

The honest nodes are the climb's (`arm_nodes`: each step's pair hash, `level_out`); with the
memory holding the position's windows, the cap leaf and the parent's flag (`WD.MemOk`), at the
frame's honest values (`WD.val`) every statement of the path (`oqPath_complete`: each window's match
takes arm `v`, the window's value) and every atom of the cap leaf (`oqCap_complete`) holds:
`walk_block`. `walk_rel`: a `walk_path` specialization (`WalkFn`) relates the leaf's halves, the
window pointer, the cap and the flags to no returns.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace WD

variable (w : WD) {rd : Reader} {σ : Val}

/-! ## The path's values -/

theorem pc_canonical (k : ℕ) : IsCanonical128 (w.pc k) := by
  unfold pc pathCell
  dsimp only
  split <;> exact canonical_ofLimbs _ _

/-- A level's pair hash is the climb's step. -/
theorem level_out {l : ℕ} (hl : l < w.sibs.length) {o0 o1 : E}
    (h : HashesPair (w.pc (4 * l)) (w.pc (4 * l + 1)) (w.pc (4 * l + 2)) (w.pc (4 * l + 3)) o0 o1) :
    (o0, o1) = digestHalves (climbNode w.leaf w.q w.sibs (l + 1)) := by
  obtain ⟨dl, dr, hl', hr', hp⟩ := hashesPair_digests h
  have hcs : climbNode w.leaf w.q w.sibs (l + 1) =
      if w.q / 2 ^ l % 2 = 0 then hashPair (climbNode w.leaf w.q w.sibs l) (w.sibs.getD l (Vector.replicate 4 0))
      else hashPair (w.sibs.getD l (Vector.replicate 4 0)) (climbNode w.leaf w.q w.sibs l) := by
    rw [climbNode, List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, climbD_snoc,
      List.length_take, min_eq_left (by omega)]
    simp [climbNode, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have i0 : (4 * l) / 4 = l ∧ (4 * l) % 4 = 0 ∧ (4 * l) % 2 = 0 := by omega
  have i1 : (4 * l + 1) / 4 = l ∧ (4 * l + 1) % 4 = 1 ∧ (4 * l + 1) % 2 = 1 := by omega
  have i2 : (4 * l + 2) / 4 = l ∧ (4 * l + 2) % 4 = 2 ∧ (4 * l + 2) % 2 = 0 := by omega
  have i3 : (4 * l + 3) / 4 = l ∧ (4 * l + 3) % 4 = 3 ∧ (4 * l + 3) % 2 = 1 := by omega
  rw [hp, hcs]
  by_cases hb : w.q.testBit l
  · have hb' : w.q / 2 ^ l % 2 = 1 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simpa using hb
    have c0 : w.pc (4 * l) = (digestHalves (w.sibs.getD l (Vector.replicate 4 0))).1 := by
      unfold pc pathCell; simp [i0, hb]
    have c1 : w.pc (4 * l + 1) = (digestHalves (w.sibs.getD l (Vector.replicate 4 0))).2 := by
      unfold pc pathCell; simp [i1, hb]
    have c2 : w.pc (4 * l + 2) = (digestHalves (climbNode w.leaf w.q w.sibs l)).1 := by
      unfold pc pathCell; simp [i2, hb]
    have c3 : w.pc (4 * l + 3) = (digestHalves (climbNode w.leaf w.q w.sibs l)).2 := by
      unfold pc pathCell; simp [i3, hb]
    have edl : dl = w.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hl', c0, c1])
    have edr : dr = climbNode w.leaf w.q w.sibs l :=
      capDigestScalars_injective (by rw [← hr', c2, c3])
    rw [edl, edr]
    simp [hb']
  · have hb' : w.q / 2 ^ l % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simp at hb; omega
    have c0 : w.pc (4 * l) = (digestHalves (climbNode w.leaf w.q w.sibs l)).1 := by
      unfold pc pathCell; simp [i0, hb]
    have c1 : w.pc (4 * l + 1) = (digestHalves (climbNode w.leaf w.q w.sibs l)).2 := by
      unfold pc pathCell; simp [i1, hb]
    have c2 : w.pc (4 * l + 2) = (digestHalves (w.sibs.getD l (Vector.replicate 4 0))).1 := by
      unfold pc pathCell; simp [i2, hb]
    have c3 : w.pc (4 * l + 3) = (digestHalves (w.sibs.getD l (Vector.replicate 4 0))).2 := by
      unfold pc pathCell; simp [i3, hb]
    have edl : dl = climbNode w.leaf w.q w.sibs l :=
      capDigestScalars_injective (by rw [← hl', c0, c1])
    have edr : dr = w.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hr', c2, c3])
    rw [edl, edr]
    simp [hb']

/-! ## The path -/

/-- The children on the walk's side are the node's cells. -/
theorem pc_walk (l : ℕ) :
    w.pc (4 * l + (if w.q.testBit l then 2 else 0)) = (digestHalves (w.node l)).1 ∧
      w.pc (4 * l + (if w.q.testBit l then 2 else 0) + 1) = (digestHalves (w.node l)).2 := by
  unfold pc pathCell node
  cases hb : w.q.testBit l
  · simp [show 4 * l / 4 = l by omega, show (4 * l + 1) / 4 = l by omega, hb,
      show 4 * l % 2 = 0 by omega, show (4 * l + 1) % 2 = 1 by omega]
  · simp [show (4 * l + 2) / 4 = l by omega,
      show (4 * l + 2 + 1) % 4 / 2 = 1 by omega, show (4 * l + 2 + 1) / 4 = l by omega, hb,
      show (4 * l + 2) % 2 = 0 by omega, show (4 * l + 2 + 1) % 2 = 1 by omega]

/-- A step's four cells, either order, are the level's children. -/
theorem step_cells {l n0 n1 : ℕ} {ch : ℕ}
    (hc : ∀ j < 4, σ (.n (ch + 4 * l + j)) = w.pc (4 * l + j))
    (hn : (σ (.n n0), σ (.n n1)) = digestHalves (w.node l)) :
    ((if w.q.testBit l then [V.n (ch + 4 * l), .n (ch + 4 * l + 1), .n n0, .n n1]
      else [.n n0, .n n1, .n (ch + 4 * l + 2), .n (ch + 4 * l + 3)]).map σ) =
      [w.pc (4 * l), w.pc (4 * l + 1), w.pc (4 * l + 2), w.pc (4 * l + 3)] := by
  obtain ⟨w0, w1⟩ := w.pc_walk l
  have e0 := congrArg Prod.fst hn
  have e1 := congrArg Prod.snd hn
  simp only at e0 e1
  have c0 := hc 0 (by omega); have c1 := hc 1 (by omega); have c2 := hc 2 (by omega)
  have c3 := hc 3 (by omega)
  simp only [Nat.add_zero] at c0
  cases hb : w.q.testBit l
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at w0 w1 ⊢
    simp [c2, c3, e0, e1, w0, w1]
  · simp only [hb, ↓reduceIte] at w0 w1 ⊢
    simp [c0, c1, e0, e1, ← w0, ← w1]

/-- The step's permutation holds at the honest values. -/
theorem step_keccak {l K : ℕ} {ins : List V} (hins : ins.map σ = w.levelIns l)
    (hout : ∀ c < 2, σ (.n (K + 1 + c)) = w.stepV l (1 + c)) :
    (Atom.keccak ins [.n (K + 1), .n (K + 2)] false false).Holds rd σ := by
  have hl : ins.length = 13 := by
    have := congrArg List.length hins; simpa [levelIns] using this
  refine keccak_holds_two.mpr ⟨hl, ?_, ?_, ?_⟩
  · rw [hins]
    intro c
    fin_cases c <;> simp [cells13, levelIns] <;> first | exact w.pc_canonical _ | exact canonical_word _ _
  · rw [hins, hout 0 (by omega), stepV]
    rfl
  · rw [hins, show K + 2 = K + 1 + 1 by omega, hout 1 (by omega), stepV]
    rfl

/-- The honest valuation of the walk's frame. -/
abbrev Hv (w : WD) (σ : Val) : Prop := ∀ i, σ (.n i) = w.val i

theorem armOff_bound {ww v r o : ℕ} (hv : v < 2 ^ ww) (hr : r < ww) (ho : o < 3) :
    armOff ww v + 3 * r + o < 4 + 3 * ww * 2 ^ ww ∧ 2 ≤ armOff ww v + 3 * r + o ∧
      armOff ww v + 3 * r + o ≠ 2 + 3 * ww ∧ armOff ww v + 3 * r + o ≠ 3 + 3 * ww := by
  unfold armOff
  have h1 : 1 ≤ 2 ^ ww := Nat.one_le_two_pow
  split
  · have : 3 * ww ≤ 3 * ww * 2 ^ ww := Nat.le_mul_of_pos_right _ h1
    omega
  · have hm : 3 * ww * v + 3 * ww ≤ 3 * ww * 2 ^ ww := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hv
    have hm2 : 3 * ww ≤ 3 * ww * v := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem oqArmK_eq (s : Oq) (ch i a : ℕ) :
    oqArmK s ch i a = oqWk s ch i + (oqWo i + armOff (oqWw s i) a) := by
  unfold oqArmK armOff; split <;> omega

/-- The values of window `i` after its padding run. -/
theorem winA_val (hv : w.Hv σ) {i o : ℕ} (hi : i < oqNpw w.s) (h1 : 1 ≤ o)
    (ho : oqWo i + o < winSz w.s i) :
    σ (.n (oqWk w.s wpCh i + (oqWo i + o))) = w.winA i o := by
  rw [hv, val_win w hi ho, winV]
  simp only [show oqWo i + o ≠ 0 by omega, show ¬ oqWo i + o ≤ oqWo i by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]

/-- The honest values of window `i`'s taken arm: its steps. -/
theorem arm_val (hv : w.Hv σ) {i r o : ℕ} (hi : i < oqNpw w.s) (hr : r < oqWw w.s i) (ho : o < 3) :
    σ (.n (oqArmK w.s wpCh i (w.wv i) + 3 * r + o)) = w.stepV (6 * i + r) o := by
  have hvl : w.wv i < 2 ^ oqWw w.s i := (qwVal_path hi w.q).1
  obtain ⟨b1, b2, b3, b4⟩ := armOff_bound (o := o) hvl hr ho
  rw [oqArmK_eq, show oqWk w.s wpCh i + (oqWo i + armOff (oqWw w.s i) (w.wv i)) + 3 * r + o =
      oqWk w.s wpCh i + (oqWo i + (armOff (oqWw w.s i) (w.wv i) + 3 * r + o)) by omega,
    w.winA_val hv hi (by omega) (by unfold winSz; omega), winA]
  simp only [show armOff (oqWw w.s i) (w.wv i) + 3 * r + o ≠ 1 by omega, b3, b4, ↓reduceIte,
    show armOff (oqWw w.s i) (w.wv i) ≤ armOff (oqWw w.s i) (w.wv i) + 3 * r + o by omega,
    show armOff (oqWw w.s i) (w.wv i) + 3 * r + o < armOff (oqWw w.s i) (w.wv i) + 3 * oqWw w.s i
      by omega, and_self]
  rw [show (armOff (oqWw w.s i) (w.wv i) + 3 * r + o - armOff (oqWw w.s i) (w.wv i)) / 3 = r by
      omega,
    show (armOff (oqWw w.s i) (w.wv i) + 3 * r + o - armOff (oqWw w.s i) (w.wv i)) % 3 = o by
      omega]

/-- The window's targets hold the node after it. -/
theorem target_val (hv : w.Hv σ) {i c : ℕ} (hi : i < oqNpw w.s) (hc : c < 2) :
    σ (.n (oqWT w.s wpCh i + c)) =
      if c = 0 then (digestHalves (w.node (6 * i + oqWw w.s i))).1
      else (digestHalves (w.node (6 * i + oqWw w.s i))).2 := by
  have h1 : 1 ≤ 2 ^ oqWw w.s i := Nat.one_le_two_pow
  have hm : 3 * oqWw w.s i ≤ 3 * oqWw w.s i * 2 ^ oqWw w.s i := Nat.le_mul_of_pos_right _ h1
  rw [oqWT, show oqWk w.s wpCh i + 2 + oqWo i + 3 * oqWw w.s i + c =
      oqWk w.s wpCh i + (oqWo i + (2 + 3 * oqWw w.s i + c)) by omega,
    w.winA_val hv hi (by omega) (by unfold winSz; omega), winA]
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  all_goals split_ifs <;> first | rfl | (exfalso; omega)

/-- The padding run window `0` places, at `wpPr`. -/
theorem pad_val (hpd : 1 ≤ w.s.pd) (hv : w.Hv σ) :
    σ (.n (wpPr w.s)) = word 1 0 0 ∧ ∀ i < 4, σ (.n (wpPr w.s + 1 + i)) = word 0 0 0 := by
  have h0 : 0 < oqNpw w.s := by unfold oqNpw; omega
  have hs : 9 ≤ winSz w.s 0 := by unfold winSz oqWo; simp
  have hpr : wpPr w.s = oqWk w.s wpCh 0 + 1 := by simp [wpPr, oqWk]
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [hpr, hv, val_win w h0 (by omega), winV]
    simp [oqWo, padV]
  · rw [hpr, show oqWk w.s wpCh 0 + 1 + 1 + i = oqWk w.s wpCh 0 + (2 + i) by omega, hv,
      val_win w h0 (by omega), winV]
    simp only [show 2 + i ≠ 0 by omega, oqWo, ↓reduceIte, show 2 + i ≤ 5 by omega,
      show 2 + i - 1 = i + 1 by omega, padV]
    interval_cases i <;> rfl

theorem climbNode_zero (leaf : Digest) (q : ℕ) (sibs : List Digest) :
    climbNode leaf q sibs 0 = leaf := by
  simp [climbNode, climbD_nil]

/-- The node window `i` starts from: the leaf's digest (the parameters), then the previous window's
targets. -/
theorem nd_val (hv : w.Hv σ) {i : ℕ} (hi : i ≤ oqNpw w.s) :
    (σ (.n (oqNd w.s 0 wpCh i 0)), σ (.n (oqNd w.s 0 wpCh i 1))) =
      digestHalves (w.node (min (6 * i) w.s.pd)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp only [oqNd, ↓reduceIte, Nat.mul_zero, Nat.zero_min, Nat.zero_add, node, climbNode_zero]
    rw [hv, hv]; rfl
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have t0 := w.target_val hv (i := j) (c := 0) (by omega) (by omega)
    have t1 := w.target_val hv (i := j) (c := 1) (by omega) (by omega)
    simp only [↓reduceIte, one_ne_zero, Nat.add_zero] at t0 t1
    have hm : 6 * j + oqWw w.s j = min (6 * (j + 1)) w.s.pd := by
      unfold oqWw; unfold oqNpw at hi ⊢; split <;> omega
    simp only [oqNd, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
    rw [t0, t1, hm]

/-- **The taken arm's nodes are the climb's.** -/
theorem arm_nodes (hpd : 1 ≤ w.s.pd) (hsl : w.sibs.length = w.s.pd) (hv : w.Hv σ)
    {i : ℕ} (hi : i < oqNpw w.s)
    (h0 : (σ (.n (oqNd w.s 0 wpCh i 0)), σ (.n (oqNd w.s 0 wpCh i 1))) =
      digestHalves (w.node (6 * i))) :
    ∀ r ≤ oqWw w.s i, (σ (.n (oqArmN w.s 0 wpCh i (w.wv i) r 0)),
      σ (.n (oqArmN w.s 0 wpCh i (w.wv i) r 1))) = digestHalves (w.node (6 * i + r)) := by
  obtain ⟨hpad, hz⟩ := w.pad_val hpd hv
  have hz' : ∀ i < 4, σ (.n (wpPr w.s + 1 + i)) = 0 := fun i hi => by rw [hz i hi, word_zero]
  intro r hr
  induction r with
  | zero => simpa [oqArmN] using h0
  | succ r ih =>
    have hn := ih (by omega)
    have hl : 6 * i + r < w.s.pd := by
      have hi' := hi; have hr' := hr
      unfold oqWw oqNpw at hr'; unfold oqNpw at hi'; split at hr' <;> omega
    set K := oqArmK w.s wpCh i (w.wv i) + 3 * r with hK
    have hk0 : σ (.n K) = word (2 ^ 63) 0 0 := by
      rw [hK, show oqArmK w.s wpCh i (w.wv i) + 3 * r = oqArmK w.s wpCh i (w.wv i) + 3 * r + 0
        from rfl, w.arm_val hv hi (by omega) (by omega), stepV]; rfl
    have hc : ∀ j < 4, σ (.n (wpCh + 4 * (6 * i + r) + j)) = w.pc (4 * (6 * i + r) + j) :=
      fun j hj => by rw [Nat.add_assoc, hv, val_pc w (by omega)]
    have hcells := w.step_cells (l := 6 * i + r) hc hn
    have hout : ∀ c < 2, σ (.n (K + 1 + c)) = w.stepV (6 * i + r) (1 + c) := fun c hc => by
      rw [hK, Nat.add_assoc, w.arm_val hv hi (by omega) (by omega)]
    have hk := w.step_keccak (rd := fun _ => none) (l := 6 * i + r) (K := K)
      (ins := (if w.q.testBit (6 * i + r) then [V.n (wpCh + 4 * (6 * i + r)),
        .n (wpCh + 4 * (6 * i + r) + 1), .n (oqArmN w.s 0 wpCh i (w.wv i) r 0),
        .n (oqArmN w.s 0 wpCh i (w.wv i) r 1)]
        else [.n (oqArmN w.s 0 wpCh i (w.wv i) r 0), .n (oqArmN w.s 0 wpCh i (w.wv i) r 1),
          .n (wpCh + 4 * (6 * i + r) + 2), .n (wpCh + 4 * (6 * i + r) + 3)]) ++
        [.n (wpPr w.s), .n (wpPr w.s + 1), .n (wpPr w.s + 2), .n (wpPr w.s + 3), .n K,
          .n (wpPr w.s + 1), .n (wpPr w.s + 2), .n (wpPr w.s + 3), .n (wpPr w.s + 4)]) (by
      rw [List.map_append, hcells]
      have z1 := hz 0 (by omega); have z2 := hz 1 (by omega); have z3 := hz 2 (by omega)
      have z4 := hz 3 (by omega)
      simp only [Nat.add_zero] at z1
      rw [show wpPr w.s + 1 + 1 = wpPr w.s + 2 by omega] at z2
      rw [show wpPr w.s + 1 + 2 = wpPr w.s + 3 by omega] at z3
      rw [show wpPr w.s + 1 + 3 = wpPr w.s + 4 by omega] at z4
      simp [hpad, z1, z2, z3, z4, hk0, levelIns]) hout
    have hpair : HashesPair (w.pc (4 * (6 * i + r))) (w.pc (4 * (6 * i + r) + 1))
        (w.pc (4 * (6 * i + r) + 2)) (w.pc (4 * (6 * i + r) + 3)) (σ (.n (K + 1)))
        (σ (.n (K + 2))) := by
      have e := hcells
      cases hb : w.q.testBit (6 * i + r)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at hk e
        have := oqPair_hash hpad hz' hk0 hk
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at e
        obtain ⟨e0, e1, e2, e3, -⟩ := e
        rw [e0, e1, e2, e3] at this
        simpa [List.getD_eq_getElem?_getD] using this
      · simp only [hb, ↓reduceIte, List.cons_append, List.nil_append] at hk e
        have := oqPair_hash hpad hz' hk0 hk
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at e
        obtain ⟨e0, e1, e2, e3, -⟩ := e
        rw [e0, e1, e2, e3] at this
        simpa [List.getD_eq_getElem?_getD] using this
    have := w.level_out (l := 6 * i + r) (by omega) hpair
    simp only [oqArmN, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
    rw [← hK, show K + 1 + 1 = K + 2 by omega, this]
    rfl

theorem gen_pow_ofK (v : ℕ) : gen ^ v = ofK (Parameters.addressOfIndex v) := gen_pow_eq_ofK v

/-- **A window holds at the honest values**: its word read, (window `0`) the padding run, `0x80`,
its match taking arm `v`. -/
theorem oqWin_complete (hpd : 1 ≤ w.s.pd) (hsl : w.sibs.length = w.s.pd) (hv : w.Hv σ)
    (hm : w.MemOk rd) {i : ℕ} (hi : i < oqNpw w.s) :
    BlockOk rd σ (oqWinT w.s (.n 2) (wpPr w.s) 0 wpCh i) := by
  obtain ⟨hpad, hz⟩ := w.pad_val hpd hv
  have hbp : σ (.n 2) = w.bpv := hv 2
  have s0 : σ (.n (oqWk w.s wpCh i)) = gen ^ w.wv i := by
    rw [show oqWk w.s wpCh i = oqWk w.s wpCh i + 0 from rfl, hv,
      val_win w hi (by unfold winSz; omega), winV]; simp
  have s1 : σ (.n (oqWk w.s wpCh i + 1 + oqWo i)) = word (2 ^ 63) 0 0 := by
    rw [show oqWk w.s wpCh i + 1 + oqWo i = oqWk w.s wpCh i + (oqWo i + 1) by omega,
      w.winA_val hv hi le_rfl (by unfold winSz; have : 1 ≤ 2 ^ oqWw w.s i := Nat.one_le_two_pow; omega),
      winA]; simp
  have hn0 : (σ (.n (oqNd w.s 0 wpCh i 0)), σ (.n (oqNd w.s 0 wpCh i 1))) =
      digestHalves (w.node (6 * i)) := by
    rw [w.nd_val hv (le_of_lt hi)]
    congr 2; unfold oqNpw at hi; omega
  have hnodes := w.arm_nodes hpd hsl hv hi hn0
  have hvl : w.wv i < 2 ^ oqWw w.s i := (qwVal_path hi w.q).1
  intro st hst
  simp only [oqWinT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with (rfl | hst) | rfl | rfl
  · show LoadHolds _ _ _ _
    rw [s0, hbp]; exact hm.wins i (by rw [qwN_eq]; omega)
  · split at hst
    · subst i
      simp only [oqPadT, List.mem_cons, List.not_mem_nil, or_false] at hst
      have z := fun k (hk : k < 4) ↦ hz k hk
      rcases hst with rfl | rfl | rfl | rfl | rfl
      · exact hpad
      · exact z 0 (by omega)
      · exact (show σ (.n (wpPr w.s + 2)) = _ from z 1 (by omega))
      · exact (show σ (.n (wpPr w.s + 3)) = _ from z 2 (by omega))
      · exact (show σ (.n (wpPr w.s + 4)) = _ from z 3 (by omega))
    · simp at hst
  · exact s1
  · refine ⟨w.wv i, by simpa using hvl, by rw [s0, gen_pow_ofK], fun a ha => ?_⟩
    simp only [List.getElem_map, List.getElem_range] at ha
    simp only [oqArmT, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with ⟨_, ⟨r, hr, rfl⟩, ha⟩ | rfl | rfl
    · simp only [oqStepT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl
      · show σ _ = _
        rw [show oqArmK w.s wpCh i (w.wv i) + 3 * r = oqArmK w.s wpCh i (w.wv i) + 3 * r + 0
          from rfl, w.arm_val hv hi hr (by omega), stepV]; rfl
      · have hn := hnodes r (by omega)
        have hl : 6 * i + r < w.s.pd := by
          have hi' := hi; have hr' := hr
          unfold oqWw oqNpw at hr'; unfold oqNpw at hi'; split at hr' <;> omega
        have hc : ∀ j < 4, σ (.n (wpCh + 4 * (6 * i + r) + j)) = w.pc (4 * (6 * i + r) + j) :=
          fun j hj => by rw [Nat.add_assoc, hv, val_pc w (by omega)]
        have hb : (w.wv i).testBit r = w.q.testBit (6 * i + r) := (qwVal_path hi w.q).2 r hr
        rw [hb]
        exact w.step_keccak (l := 6 * i + r) (by
          rw [List.map_append, w.step_cells hc hn]
          have z1 := hz 0 (by omega); have z2 := hz 1 (by omega); have z3 := hz 2 (by omega)
          have z4 := hz 3 (by omega)
          simp only [Nat.add_zero] at z1
          rw [show wpPr w.s + 1 + 1 = wpPr w.s + 2 by omega] at z2
          rw [show wpPr w.s + 1 + 2 = wpPr w.s + 3 by omega] at z3
          rw [show wpPr w.s + 1 + 3 = wpPr w.s + 4 by omega] at z4
          have hk0 : σ (.n (oqArmK w.s wpCh i (w.wv i) + 3 * r)) = word (2 ^ 63) 0 0 := by
            rw [show oqArmK w.s wpCh i (w.wv i) + 3 * r = oqArmK w.s wpCh i (w.wv i) + 3 * r + 0
              from rfl, w.arm_val hv hi hr (by omega), stepV]; rfl
          simp [hpad, z1, z2, z3, z4, hk0, levelIns]) (fun c hc => by
            rw [Nat.add_assoc, w.arm_val hv hi hr (by omega)])
    · show σ _ = σ _
      have t := w.target_val hv (c := 0) hi (by omega)
      rw [Nat.add_zero] at t
      rw [t, show σ (.n (oqArmN w.s 0 wpCh i (w.wv i) (oqWw w.s i) 0)) =
        (digestHalves (w.node (6 * i + oqWw w.s i))).1 from
        congrArg Prod.fst (hnodes _ le_rfl)]
      rfl
    · show σ _ = σ _
      have t := w.target_val hv (c := 1) hi (by omega)
      rw [t, show σ (.n (oqArmN w.s 0 wpCh i (w.wv i) (oqWw w.s i) 1)) =
        (digestHalves (w.node (6 * i + oqWw w.s i))).2 from
        congrArg Prod.snd (hnodes _ le_rfl)]
      rfl

/-- **The path holds at the honest values.** -/
theorem oqPath_complete (hpd : 1 ≤ w.s.pd) (hsl : w.sibs.length = w.s.pd) (hv : w.Hv σ)
    (hm : w.MemOk rd) :
    BlockOk rd σ (oqPathT w.s (.n 2) (wpPr w.s) 0 wpCh) := by
  intro st hst
  simp only [oqPathT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten, List.mem_map, List.mem_range] at hst
  rcases hst with rfl | ⟨_, ⟨i, hi, rfl⟩, hst⟩
  · trivial
  · exact w.oqWin_complete hpd hsl hv hm hi _ hst

/-! ## The cap leaf -/

theorem climbNode_length (leaf : Digest) (q : ℕ) (sibs : List Digest) :
    climbNode leaf q sibs sibs.length = climbD leaf q sibs := by
  simp [climbNode]

/-- **The cap leaf holds at the honest values.** -/
theorem oqCap_complete (hsl : w.sibs.length = w.s.pd) (hcd : 1 ≤ w.s.cd)
    (hq : w.q < 2 ^ (w.s.pd + w.s.cd)) (hv : w.Hv σ) (hm : w.MemOk rd) :
    ∀ a, Stmt.atom a ∈ oqCapT w.s (.n 2) (.n 3) (.n 4) 0 wpCh → a.Holds rd σ := by
  have hbp : σ (.n 2) = w.bpv := hv 2
  have hcap : σ (.n 3) = w.capv := hv 3
  have hflags : σ (.n 4) = w.flagsv := hv 4
  have hCq : oqCq w.s wpCh = w.Cq := rfl
  have t : ∀ o < 9, σ (.n (w.Cq + o)) = w.capV o := fun o ho => by rw [hv, val_cap w]
  have t0 : σ (.n w.Cq) = w.wbV := by rw [show w.Cq = w.Cq + 0 from rfl, t 0 (by omega)]; rfl
  have t1 : σ (.n (w.Cq + 1)) = w.qV := by rw [t 1 (by omega)]; rfl
  have t2 : σ (.n (w.Cq + 2)) = w.flagsv * w.qV := by rw [t 2 (by omega)]; rfl
  have t3 : σ (.n (w.Cq + 3)) = word 1 0 0 := by rw [t 3 (by omega)]; rfl
  have t4 : σ (.n (w.Cq + 4)) = w.qV * w.qV := by rw [t 4 (by omega)]; rfl
  have t5 : σ (.n (w.Cq + 5)) = w.capv * (w.qV * w.qV) := by rw [t 5 (by omega)]; rfl
  have t6 : σ (.n (w.Cq + 6)) = w.capv * (w.qV * w.qV) * (w.qV * w.qV) := by rw [t 6 (by omega)]; rfl
  have t7 : σ (.n (w.Cq + 7)) = w.wbV * w.wbV := by rw [t 7 (by omega)]; rfl
  have t8 : σ (.n (w.Cq + 8)) = w.capv * (w.qV * w.qV) * (w.qV * w.qV) * (w.wbV * w.wbV) := by
    rw [t 8 (by omega)]; rfl
  have hN : oqNpw w.s + 1 < qwN (w.s.pd + w.s.cd) w.s.cd := by rw [qwN_eq]; omega
  have hwb : gen ^ w.wv (oqNpw w.s) = w.wbV := by
    rw [wbV, wv, oqNpw_eq, qwVal_capBit]
  have hqv : gen ^ w.wv (oqNpw w.s + 1) = w.qV := by
    rw [qV, wv, oqNpw_eq, qwVal_capIdx hcd hq]
  set Q := w.q / 2 ^ (w.s.pd + 1) with hQdef
  set bb : ℕ := if w.q.testBit w.s.pd then 1 else 0 with hbdef
  have h8 : w.capv * (w.qV * w.qV) * (w.qV * w.qV) * (w.wbV * w.wbV) =
      w.capv * gen ^ (4 * Q + 2 * bb) := by
    rw [qV, wbV, ← hQdef, ← hbdef, ← pow_add, ← pow_add, mul_assoc, mul_assoc,
      ← pow_add, ← pow_add]
    congr 2; ring
  have hsplit : w.q / 2 ^ w.s.pd = 2 * Q + bb := by
    rw [hQdef, hbdef, Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    by_cases h : w.q / 2 ^ w.s.pd % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  have hnd := w.nd_val hv (i := oqNpw w.s) le_rfl
  have hmin : min (6 * oqNpw w.s) w.s.pd = w.s.pd := by unfold oqNpw; omega
  rw [hmin, node, ← hsl, climbNode_length] at hnd
  intro a ha
  simp only [oqCapT, hCq, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show LoadHolds _ _ _ _
    rw [t0, hbp, ← hwb]; exact hm.wins _ (by omega)
  · show LoadHolds _ _ _ _
    rw [t1, hbp, ← hqv]; exact hm.wins _ hN
  · show σ _ = σ _ * σ _
    rw [t2, hflags, t1]
  · exact t3
  · show LoadHolds _ _ _ _
    rw [t3, t2, word_one, qV, loadHolds_mul_gen_pow, add_comm]
    exact hm.flag
  · show σ _ = σ _ * σ _
    rw [t4, t1]
  · show σ _ = σ _ * σ _
    rw [t5, hcap, t4]
  · show σ _ = σ _ * σ _
    rw [t6, t5, t4]
  · show σ _ = σ _ * σ _
    rw [t7, t0]
  · show σ _ = σ _ * σ _
    rw [t8, t6, t7]
  · show LoadHolds _ _ _ _
    rw [t8, h8, show σ (.n (oqNd w.s 0 wpCh (oqNpw w.s) 0)) =
      (digestHalves (climbD w.leaf w.q w.sibs)).1 from congrArg Prod.fst hnd, loadHolds_mul_gen_pow]
    have := hm.cap0
    rw [hsplit, show 2 * (2 ^ w.s.cd + (2 * Q + bb)) = 4 * Q + 2 * bb + 2 ^ (w.s.cd + 1) by
      rw [pow_succ]; ring] at this
    exact this
  · show LoadHolds _ _ _ _
    rw [t8, h8, show σ (.n (oqNd w.s 0 wpCh (oqNpw w.s) 1)) =
      (digestHalves (climbD w.leaf w.q w.sibs)).2 from congrArg Prod.snd hnd, loadHolds_mul_gen_pow]
    have := hm.cap1
    rw [hsplit, show 2 * (2 ^ w.s.cd + (2 * Q + bb)) + 1 = 4 * Q + 2 * bb + (2 ^ (w.s.cd + 1) + 1)
      by rw [pow_succ]; ring] at this
    exact this

/-! ## The walk -/

/-- **The walk's body holds at the honest values**, statement by statement. -/
theorem walk_block (hpd : 1 ≤ w.s.pd) (hcd : 1 ≤ w.s.cd) (hsl : w.sibs.length = w.s.pd)
    (hq : w.q < 2 ^ (w.s.pd + w.s.cd)) (hv : w.Hv σ) (hm : w.MemOk rd) :
    BlockOk rd σ (oqPathT w.s (.n 2) (wpPr w.s) 0 wpCh ++ oqCapT w.s (.n 2) (.n 3) (.n 4) 0 wpCh) :=
  blockOk_append.mpr ⟨w.oqPath_complete hpd hsl hv hm,
    blockOk_of_atoms (oqCapT_atoms _ _ _ _ _ _) (w.oqCap_complete hsl hcd hq hv hm)⟩

/-- **`walk_path` is complete**: a specialization (`WalkFn`) on the leaf's halves, the window
pointer, the cap and the flags of an honest walk returns nothing. -/
theorem walk_rel (hpd : 1 ≤ w.s.pd) (hcd : 1 ≤ w.s.cd) (hsl : w.sibs.length = w.s.pd)
    (hq : w.q < 2 ^ (w.s.pd + w.s.cd)) (hm : w.MemOk rd) {walk : String}
    (hW : WalkFn walk w.s.pd w.s.cd) :
    coreProgram.Rel rd walk [(digestHalves w.leaf).1, (digestHalves w.leaf).2, w.bpv, w.capv,
      w.flagsv] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := hW
  rw [rel_iff_sem hf, hb, hp]
  refine ⟨fun v ↦ w.val v.idx, rfl, ?_⟩
  rw [wpBodyT_eq, holdsList_append, holdsList_flat (flat_append (oqPathT_flat _ _ _ _ _)
    (flat_of_atoms (oqCapT_atoms _ _ _ _ _ _)))]
  exact ⟨w.walk_block hpd hcd hsl hq (fun _ ↦ rfl) hm, by simp [Stmt.HoldsList, Stmt.Holds]⟩

end WD

end
end LeanVM.Guest.B1
