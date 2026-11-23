/-
  LeanVM.Guest.B1.Opening.QueriesComplete3

  The completeness of `walk_path`, inline in a query: the Merkle path and the cap leaf.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete2

/-!
# `walk_path`, completeness (lean_ethereum.py)

`WD.At w σ ch kN pr bp cap flags`: the valuation holds an honest walk inline: its values `w.vals`
from the siblings' first cell `ch`, the leaf's halves at `kN`, the padding run `1, 0, 0, 0, 0` at
`pr`, the window pointer, the cap and the flags at `bp`, `cap`, `flags`.

The honest nodes are the climb's (`arm_nodes`: each step's pair hash, `level_out`); with the
memory holding the position's windows, the cap leaf and the parent's flag (`WD.MemOk`), every
statement of the path (`oqPath_complete`: each window's match takes arm `v`, the window's value)
and every atom of the cap leaf (`oqCap_complete`) holds: `walk_block`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace WD

variable (w : WD) {rd : Reader} {σ : Val}

/-- **An honest walk inline**: the walk's values from `ch`, the leaf's halves at `kN`, the padding
run at `pr`, its pointers at `bp`, `cap`, `flags`. -/
structure At (σ : Val) (ch kN pr : ℕ) (bp cap flags : V) : Prop where
  vals : ∀ o < w.vals.length, σ (.n (ch + o)) = w.vals.getD o 0
  leaf : (σ (.n kN), σ (.n (kN + 1))) = digestHalves w.leaf
  pad : σ (.n pr) = word 1 0
  zeros : ∀ i < 4, σ (.n (pr + 1 + i)) = word 0 0
  bp : σ bp = w.bpv
  cap : σ cap = w.capv
  flags : σ flags = w.flagsv

variable {w} {ch kN pr : ℕ} {bp cap flags : V}

/-! ## The values -/

theorem At.sib (hv : w.At σ ch kN pr bp cap flags) {o : ℕ} (ho : o < 2 * w.s.pd) :
    σ (.n (ch + o)) = w.pc o := by
  rw [hv.vals o (by rw [vals_length]; omega), w.vals_sib ho]

theorem At.win (hv : w.At σ ch kN pr bp cap flags) {i o : ℕ} (hi : i < oqNpw w.s)
    (ho : o < winSz w.s i) : σ (.n (oqWk w.s ch i + o)) = w.winV i o := by
  have h1 := winOff_succ_le (s := w.s) hi
  have hp : w.s.pd = w.s.pd := rfl
  rw [oqWk_eq, Nat.add_assoc, Nat.add_assoc, hv.vals _ (by rw [vals_length]; omega),
    w.vals_win hi ho]

theorem At.capv' (hv : w.At σ ch kN pr bp cap flags) {o : ℕ} (ho : o < 9) :
    σ (.n (oqCq w.s ch + o)) = w.capV o := by
  have hp : w.s.pd = w.s.pd := rfl
  rw [oqCq, oqWk_eq, Nat.add_assoc, Nat.add_assoc, hv.vals _ (by rw [vals_length]; omega),
    w.vals_cap ho]

/-! ## The path's values -/

theorem pc_sib (l : ℕ) :
    w.pc (2 * l) = (digestHalves (w.sibs.getD l (Vector.replicate 4 0))).1 ∧
      w.pc (2 * l + 1) = (digestHalves (w.sibs.getD l (Vector.replicate 4 0))).2 := by
  unfold pc pathCell
  simp [show 2 * l / 2 = l by omega, show (2 * l + 1) / 2 = l by omega]

/-- A level's pair hash is the climb's step. -/
theorem level_out {l : ℕ} (hl : l < w.sibs.length) {o0 o1 : E}
    (h : if w.q.testBit l then
        HashesPair (w.pc (2 * l)) (w.pc (2 * l + 1)) (digestHalves (w.node l)).1
          (digestHalves (w.node l)).2 o0 o1
      else HashesPair (digestHalves (w.node l)).1 (digestHalves (w.node l)).2 (w.pc (2 * l))
          (w.pc (2 * l + 1)) o0 o1) :
    (o0, o1) = digestHalves (climbNode w.leaf w.q w.sibs (l + 1)) := by
  have hcs : climbNode w.leaf w.q w.sibs (l + 1) =
      if w.q / 2 ^ l % 2 = 0 then hashPair (climbNode w.leaf w.q w.sibs l) (w.sibs.getD l (Vector.replicate 4 0))
      else hashPair (w.sibs.getD l (Vector.replicate 4 0)) (climbNode w.leaf w.q w.sibs l) := by
    rw [climbNode, List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, climbD_snoc,
      List.length_take, min_eq_left (by omega)]
    simp [climbNode, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  obtain ⟨c0, c1⟩ := w.pc_sib l
  rw [hcs]
  by_cases hb : w.q.testBit l
  · have hb' : w.q / 2 ^ l % 2 = 1 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simpa using hb
    simp only [hb, ↓reduceIte] at h
    obtain ⟨dl, dr, hl', hr', hp⟩ := hashesPair_digests h
    have edl : dl = w.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hl', c0, c1])
    have edr : dr = climbNode w.leaf w.q w.sibs l := capDigestScalars_injective (by rw [← hr']; rfl)
    rw [hp, edl, edr]
    simp [hb']
  · have hb' : w.q / 2 ^ l % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simp at hb; omega
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨dl, dr, hl', hr', hp⟩ := hashesPair_digests h
    have edl : dl = climbNode w.leaf w.q w.sibs l := capDigestScalars_injective (by rw [← hl']; rfl)
    have edr : dr = w.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hr', c0, c1])
    rw [hp, edl, edr]
    simp [hb']

/-! ## The path -/

/-- A step's four cells, the bit's order, are the level's node and sibling. -/
theorem step_cells {l n0 n1 : ℕ} (hc0 : σ (.n (ch + 2 * l)) = w.pc (2 * l))
    (hc1 : σ (.n (ch + 2 * l + 1)) = w.pc (2 * l + 1))
    (hn : (σ (.n n0), σ (.n n1)) = digestHalves (w.node l)) :
    ((if w.q.testBit l then [V.n (ch + 2 * l), .n (ch + 2 * l + 1), .n n0, .n n1]
      else [.n n0, .n n1, .n (ch + 2 * l), .n (ch + 2 * l + 1)]).map σ) =
      (if w.q.testBit l then [w.pc (2 * l), w.pc (2 * l + 1), (digestHalves (w.node l)).1,
        (digestHalves (w.node l)).2]
      else [(digestHalves (w.node l)).1, (digestHalves (w.node l)).2, w.pc (2 * l),
        w.pc (2 * l + 1)]) := by
  have e0 := congrArg Prod.fst hn
  have e1 := congrArg Prod.snd hn
  simp only at e0 e1
  cases hb : w.q.testBit l <;> simp [hc0, hc1, e0, e1]

theorem levelIns_length (l : ℕ) : (w.levelIns l).length = 13 := by
  unfold levelIns; split <;> rfl

/-- The step's permutation holds at the honest values. -/
theorem step_keccak {l K : ℕ} {ins : List V} (hins : ins.map σ = w.levelIns l)
    (hout : ∀ c < 2, σ (.n (K + 1 + c)) = w.stepV l (1 + c)) :
    (Atom.keccak ins [.n (K + 1), .n (K + 2)] false false).Holds rd σ := by
  have hl : ins.length = 13 := by
    have := congrArg List.length hins; rw [List.length_map, levelIns_length] at this; exact this
  refine keccak_holds_two.mpr ⟨hl, ?_, ?_⟩
  · rw [hins, hout 0 (by omega), stepV]
    rfl
  · rw [hins, show K + 2 = K + 1 + 1 by omega, hout 1 (by omega), stepV]
    rfl

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

theorem oqArmK_eq (s : Oq) (ch i a : ℕ) : oqArmK s ch i a = oqWk s ch i + armOff (oqWw s i) a := by
  unfold oqArmK armOff; split <;> omega

/-- The honest values of window `i`'s taken arm: its steps. -/
theorem At.arm_val (hv : w.At σ ch kN pr bp cap flags) {i r o : ℕ} (hi : i < oqNpw w.s)
    (hr : r < oqWw w.s i) (ho : o < 3) :
    σ (.n (oqArmK w.s ch i (w.wv i) + 3 * r + o)) = w.stepV (6 * i + r) o := by
  have hvl : w.wv i < 2 ^ oqWw w.s i := (qwVal_path hi w.q).1
  obtain ⟨b1, b2, b3, b4⟩ := armOff_bound (o := o) hvl hr ho
  rw [oqArmK_eq, show oqWk w.s ch i + armOff (oqWw w.s i) (w.wv i) + 3 * r + o =
      oqWk w.s ch i + (armOff (oqWw w.s i) (w.wv i) + 3 * r + o) by omega,
    hv.win hi (by unfold winSz; omega), winV]
  simp only [show armOff (oqWw w.s i) (w.wv i) + 3 * r + o ≠ 0 by omega,
    show armOff (oqWw w.s i) (w.wv i) + 3 * r + o ≠ 1 by omega, b3, b4, ↓reduceIte,
    show armOff (oqWw w.s i) (w.wv i) ≤ armOff (oqWw w.s i) (w.wv i) + 3 * r + o by omega,
    show armOff (oqWw w.s i) (w.wv i) + 3 * r + o < armOff (oqWw w.s i) (w.wv i) + 3 * oqWw w.s i
      by omega, and_self]
  rw [show (armOff (oqWw w.s i) (w.wv i) + 3 * r + o - armOff (oqWw w.s i) (w.wv i)) / 3 = r by
      omega,
    show (armOff (oqWw w.s i) (w.wv i) + 3 * r + o - armOff (oqWw w.s i) (w.wv i)) % 3 = o by
      omega]

/-- The window's targets hold the node after it. -/
theorem At.target_val (hv : w.At σ ch kN pr bp cap flags) {i c : ℕ} (hi : i < oqNpw w.s) (hc : c < 2) :
    σ (.n (oqWT w.s ch i + c)) =
      if c = 0 then (digestHalves (w.node (6 * i + oqWw w.s i))).1
      else (digestHalves (w.node (6 * i + oqWw w.s i))).2 := by
  have h1 : 1 ≤ 2 ^ oqWw w.s i := Nat.one_le_two_pow
  have hm : 3 * oqWw w.s i ≤ 3 * oqWw w.s i * 2 ^ oqWw w.s i := Nat.le_mul_of_pos_right _ h1
  rw [oqWT, show oqWk w.s ch i + 2 + 3 * oqWw w.s i + c = oqWk w.s ch i + (2 + 3 * oqWw w.s i + c) by
      omega, hv.win hi (by unfold winSz; omega), winV]
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  all_goals split_ifs <;> first | rfl | (exfalso; omega)

theorem climbNode_zero (leaf : Digest) (q : ℕ) (sibs : List Digest) :
    climbNode leaf q sibs 0 = leaf := by
  simp [climbNode, climbD_nil]

/-- The node window `i` starts from: the leaf's digest, then the previous window's targets. -/
theorem At.nd_val (hv : w.At σ ch kN pr bp cap flags) {i : ℕ} (hi : i ≤ oqNpw w.s) :
    (σ (.n (oqNd w.s kN ch i 0)), σ (.n (oqNd w.s kN ch i 1))) =
      digestHalves (w.node (min (6 * i) w.s.pd)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp only [oqNd, ↓reduceIte, Nat.mul_zero, Nat.zero_min, Nat.add_zero, node, climbNode_zero]
    exact hv.leaf
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have t0 := hv.target_val (i := j) (c := 0) (by omega) (by omega)
    have t1 := hv.target_val (i := j) (c := 1) (by omega) (by omega)
    simp only [↓reduceIte, one_ne_zero, Nat.add_zero] at t0 t1
    have hm : 6 * j + oqWw w.s j = min (6 * (j + 1)) w.s.pd := by
      unfold oqWw; unfold oqNpw at hi ⊢; split <;> omega
    simp only [oqNd, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
    rw [t0, t1, hm]

/-- The step `l`'s keccak inputs at the honest values. -/
theorem At.step_ins (hv : w.At σ ch kN pr bp cap flags) {l n0 n1 K : ℕ} (hl : l < w.s.pd)
    (hn : (σ (.n n0), σ (.n n1)) = digestHalves (w.node l)) (hk0 : σ (.n K) = word (2 ^ 63) 0) :
    ((if w.q.testBit l then [V.n (ch + 2 * l), .n (ch + 2 * l + 1), .n n0, .n n1]
      else [.n n0, .n n1, .n (ch + 2 * l), .n (ch + 2 * l + 1)]) ++
      [V.n pr, .n (pr + 1), .n (pr + 2), .n (pr + 3), .n K, .n (pr + 1), .n (pr + 2), .n (pr + 3),
        .n (pr + 4)]).map σ = w.levelIns l := by
  rw [List.map_append, w.step_cells (hv.sib (by omega)) (by rw [Nat.add_assoc]; exact hv.sib (by omega)) hn]
  have z1 := hv.zeros 0 (by omega); have z2 := hv.zeros 1 (by omega)
  have z3 := hv.zeros 2 (by omega); have z4 := hv.zeros 3 (by omega)
  simp only [Nat.add_zero] at z1
  rw [show pr + 1 + 1 = pr + 2 by omega] at z2
  rw [show pr + 1 + 2 = pr + 3 by omega] at z3
  rw [show pr + 1 + 3 = pr + 4 by omega] at z4
  simp [hv.pad, z1, z2, z3, z4, hk0, levelIns]

/-- **The taken arm's nodes are the climb's.** -/
theorem At.arm_nodes (hsl : w.sibs.length = w.s.pd) (hv : w.At σ ch kN pr bp cap flags)
    {i : ℕ} (hi : i < oqNpw w.s)
    (h0 : (σ (.n (oqNd w.s kN ch i 0)), σ (.n (oqNd w.s kN ch i 1))) =
      digestHalves (w.node (6 * i))) :
    ∀ r ≤ oqWw w.s i, (σ (.n (oqArmN w.s kN ch i (w.wv i) r 0)),
      σ (.n (oqArmN w.s kN ch i (w.wv i) r 1))) = digestHalves (w.node (6 * i + r)) := by
  have hz' : ∀ i < 4, σ (.n (pr + 1 + i)) = 0 := fun i hi => by rw [hv.zeros i hi, word_zero]
  intro r hr
  induction r with
  | zero => simpa [oqArmN] using h0
  | succ r ih =>
    have hn := ih (by omega)
    have hl : 6 * i + r < w.s.pd := by
      have hi' := hi; have hr' := hr
      unfold oqWw oqNpw at hr'; unfold oqNpw at hi'; split at hr' <;> omega
    set K := oqArmK w.s ch i (w.wv i) + 3 * r with hK
    have hk0 : σ (.n K) = word (2 ^ 63) 0 := by
      rw [hK, show oqArmK w.s ch i (w.wv i) + 3 * r = oqArmK w.s ch i (w.wv i) + 3 * r + 0
        from rfl, hv.arm_val hi (by omega) (by omega), stepV]; rfl
    have hins := hv.step_ins (n0 := oqArmN w.s kN ch i (w.wv i) r 0)
      (n1 := oqArmN w.s kN ch i (w.wv i) r 1) hl hn hk0
    have hout : ∀ c < 2, σ (.n (K + 1 + c)) = w.stepV (6 * i + r) (1 + c) := fun c hc => by
      rw [hK, Nat.add_assoc, hv.arm_val hi (by omega) (by omega)]
    have hk := w.step_keccak (rd := fun _ => none) hins hout
    have e := w.step_cells (n0 := oqArmN w.s kN ch i (w.wv i) r 0)
      (n1 := oqArmN w.s kN ch i (w.wv i) r 1) (hv.sib (by omega))
      (by rw [Nat.add_assoc]; exact hv.sib (by omega)) hn
    have hpair : if w.q.testBit (6 * i + r) then
        HashesPair (w.pc (2 * (6 * i + r))) (w.pc (2 * (6 * i + r) + 1))
          (digestHalves (w.node (6 * i + r))).1 (digestHalves (w.node (6 * i + r))).2
          (σ (.n (K + 1))) (σ (.n (K + 2)))
      else HashesPair (digestHalves (w.node (6 * i + r))).1 (digestHalves (w.node (6 * i + r))).2
          (w.pc (2 * (6 * i + r))) (w.pc (2 * (6 * i + r) + 1)) (σ (.n (K + 1))) (σ (.n (K + 2))) := by
      cases hb : w.q.testBit (6 * i + r)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at hk e ⊢
        have := oqPair_hash hv.pad hz' hk0 hk
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at e
        obtain ⟨e0, e1, e2, e3, -⟩ := e
        rw [e0, e1, e2, e3] at this
        simpa [List.getD_eq_getElem?_getD] using this
      · simp only [hb, ↓reduceIte, List.cons_append, List.nil_append] at hk e ⊢
        have := oqPair_hash hv.pad hz' hk0 hk
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at e
        obtain ⟨e0, e1, e2, e3, -⟩ := e
        rw [e0, e1, e2, e3] at this
        simpa [List.getD_eq_getElem?_getD] using this
    have := w.level_out (l := 6 * i + r) (by omega) hpair
    simp only [oqArmN, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
    rw [← hK, show K + 1 + 1 = K + 2 by omega, this]
    rfl

theorem gen_pow_ofK (v : ℕ) : gen ^ v = ofK (Parameters.addressOfIndex v) := gen_pow_eq_ofK v

/-- **A window holds at the honest values**: its word read, `0x80`, its match taking arm `v`. -/
theorem At.oqWin_complete (hsl : w.sibs.length = w.s.pd) (hv : w.At σ ch kN pr bp cap flags)
    (hm : w.MemOk rd) {i : ℕ} (hi : i < oqNpw w.s) :
    BlockOk rd σ (oqWinT w.s bp pr kN ch i) := by
  have s0 : σ (.n (oqWk w.s ch i)) = gen ^ w.wv i := by
    rw [show oqWk w.s ch i = oqWk w.s ch i + 0 from rfl, hv.win hi (by unfold winSz; omega), winV]
    simp
  have s1 : σ (.n (oqWk w.s ch i + 1)) = word (2 ^ 63) 0 := by
    rw [hv.win hi (by unfold winSz; omega), winV]; simp
  have hn0 : (σ (.n (oqNd w.s kN ch i 0)), σ (.n (oqNd w.s kN ch i 1))) =
      digestHalves (w.node (6 * i)) := by
    rw [hv.nd_val (le_of_lt hi)]
    congr 2; unfold oqNpw at hi; omega
  have hnodes := hv.arm_nodes hsl hi hn0
  have hvl : w.wv i < 2 ^ oqWw w.s i := (qwVal_path hi w.q).1
  intro st hst
  simp only [oqWinT, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl
  · show LoadHolds _ _ _ _
    rw [s0, hv.bp]; exact hm.wins i (by rw [qwN_eq]; omega)
  · exact s1
  · refine ⟨w.wv i, by simpa using hvl, by rw [s0, gen_pow_ofK], fun a ha => ?_⟩
    simp only [List.getElem_map, List.getElem_range] at ha
    simp only [oqArmT, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with ⟨_, ⟨r, hr, rfl⟩, ha⟩ | rfl | rfl
    · simp only [oqStepT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl
      · show σ _ = _
        rw [show oqArmK w.s ch i (w.wv i) + 3 * r = oqArmK w.s ch i (w.wv i) + 3 * r + 0
          from rfl, hv.arm_val hi hr (by omega), stepV]; rfl
      · have hn := hnodes r (by omega)
        have hl : 6 * i + r < w.s.pd := by
          have hi' := hi; have hr' := hr
          unfold oqWw oqNpw at hr'; unfold oqNpw at hi'; split at hr' <;> omega
        have hb : (w.wv i).testBit r = w.q.testBit (6 * i + r) := (qwVal_path hi w.q).2 r hr
        rw [hb]
        have hk0 : σ (.n (oqArmK w.s ch i (w.wv i) + 3 * r)) = word (2 ^ 63) 0 := by
          rw [show oqArmK w.s ch i (w.wv i) + 3 * r = oqArmK w.s ch i (w.wv i) + 3 * r + 0
            from rfl, hv.arm_val hi hr (by omega), stepV]; rfl
        exact w.step_keccak (hv.step_ins hl hn hk0) (fun c hc => by
          rw [Nat.add_assoc, hv.arm_val hi hr (by omega)])
    · show σ _ = σ _
      have t := hv.target_val (c := 0) hi (by omega)
      rw [Nat.add_zero] at t
      rw [t, show σ (.n (oqArmN w.s kN ch i (w.wv i) (oqWw w.s i) 0)) =
        (digestHalves (w.node (6 * i + oqWw w.s i))).1 from
        congrArg Prod.fst (hnodes _ le_rfl)]
      rfl
    · show σ _ = σ _
      have t := hv.target_val (c := 1) hi (by omega)
      rw [t, show σ (.n (oqArmN w.s kN ch i (w.wv i) (oqWw w.s i) 1)) =
        (digestHalves (w.node (6 * i + oqWw w.s i))).2 from
        congrArg Prod.snd (hnodes _ le_rfl)]
      rfl

/-- **The path holds at the honest values.** -/
theorem At.oqPath_complete (hsl : w.sibs.length = w.s.pd) (hv : w.At σ ch kN pr bp cap flags)
    (hm : w.MemOk rd) : BlockOk rd σ (oqPathT w.s bp pr kN ch) := by
  intro st hst
  simp only [oqPathT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten, List.mem_map, List.mem_range] at hst
  rcases hst with rfl | ⟨_, ⟨i, hi, rfl⟩, hst⟩
  · trivial
  · exact hv.oqWin_complete hsl hm hi _ hst

/-! ## The cap leaf -/

theorem climbNode_length (leaf : Digest) (q : ℕ) (sibs : List Digest) :
    climbNode leaf q sibs sibs.length = climbD leaf q sibs := by
  simp [climbNode]

/-- **The cap leaf holds at the honest values.** -/
theorem At.oqCap_complete (hsl : w.sibs.length = w.s.pd) (hcd : 1 ≤ w.cd)
    (hq : w.q < 2 ^ (w.s.pd + w.cd)) (hv : w.At σ ch kN pr bp cap flags) (hm : w.MemOk rd) :
    ∀ a, Stmt.atom a ∈ oqCapT bp cap flags (oqCq w.s ch) (oqNd w.s kN ch (oqNpw w.s) 0) (oqNpw w.s) →
      a.Holds rd σ := by
  set Cq := oqCq w.s ch with hCq
  have t : ∀ o < 9, σ (.n (Cq + o)) = w.capV o := fun o ho => hv.capv' ho
  have t0 : σ (.n Cq) = w.wbV := by rw [show Cq = Cq + 0 from rfl, t 0 (by omega)]; rfl
  have t1 : σ (.n (Cq + 1)) = w.qV := by rw [t 1 (by omega)]; rfl
  have t2 : σ (.n (Cq + 2)) = w.flagsv * w.qV := by rw [t 2 (by omega)]; rfl
  have t3 : σ (.n (Cq + 3)) = word 1 0 := by rw [t 3 (by omega)]; rfl
  have t4 : σ (.n (Cq + 4)) = w.qV * w.qV := by rw [t 4 (by omega)]; rfl
  have t5 : σ (.n (Cq + 5)) = w.capv * (w.qV * w.qV) := by rw [t 5 (by omega)]; rfl
  have t6 : σ (.n (Cq + 6)) = w.capv * (w.qV * w.qV) * (w.qV * w.qV) := by rw [t 6 (by omega)]; rfl
  have t7 : σ (.n (Cq + 7)) = w.wbV * w.wbV := by rw [t 7 (by omega)]; rfl
  have t8 : σ (.n (Cq + 8)) = w.capv * (w.qV * w.qV) * (w.qV * w.qV) * (w.wbV * w.wbV) := by
    rw [t 8 (by omega)]; rfl
  have hN : oqNpw w.s + 1 < qwN (w.s.pd + w.cd) w.cd := by rw [qwN_eq]; omega
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
  have hnd := hv.nd_val (i := oqNpw w.s) le_rfl
  have hmin : min (6 * oqNpw w.s) w.s.pd = w.s.pd := by unfold oqNpw; omega
  rw [hmin, node, ← hsl, climbNode_length] at hnd
  intro a ha
  simp only [oqCapT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show LoadHolds _ _ _ _
    rw [t0, hv.bp, ← hwb]; exact hm.wins _ (by omega)
  · show LoadHolds _ _ _ _
    rw [t1, hv.bp, ← hqv]; exact hm.wins _ hN
  · show σ _ = σ _ * σ _
    rw [t2, hv.flags, t1]
  · exact t3
  · show LoadHolds _ _ _ _
    rw [t3, t2, word_one, qV, loadHolds_mul_gen_pow, Nat.add_zero]
    exact hm.flag
  · show σ _ = σ _ * σ _
    rw [t4, t1]
  · show σ _ = σ _ * σ _
    rw [t5, hv.cap, t4]
  · show σ _ = σ _ * σ _
    rw [t6, t5, t4]
  · show σ _ = σ _ * σ _
    rw [t7, t0]
  · show σ _ = σ _ * σ _
    rw [t8, t6, t7]
  · show LoadHolds _ _ _ _
    rw [t8, h8, show σ (.n (oqNd w.s kN ch (oqNpw w.s) 0)) =
      (digestHalves (climbD w.leaf w.q w.sibs)).1 from congrArg Prod.fst hnd, loadHolds_mul_gen_pow]
    have := hm.cap0
    rw [hsplit, show 2 * (2 * Q + bb) = 4 * Q + 2 * bb + 0 by ring] at this
    exact this
  · show LoadHolds _ _ _ _
    have e1 : oqNd w.s kN ch (oqNpw w.s) 0 + 1 = oqNd w.s kN ch (oqNpw w.s) 1 := by
      unfold oqNd; split <;> omega
    rw [t8, h8, e1, show σ (.n (oqNd w.s kN ch (oqNpw w.s) 1)) =
      (digestHalves (climbD w.leaf w.q w.sibs)).2 from congrArg Prod.snd hnd, loadHolds_mul_gen_pow]
    have := hm.cap1
    rw [hsplit, show 2 * (2 * Q + bb) + 1 = 4 * Q + 2 * bb + 1 by ring] at this
    exact this

/-! ## The walk -/

/-- **The walk holds at the honest values**, statement by statement. -/
theorem At.walk_block (hcd : 1 ≤ w.cd) (hsl : w.sibs.length = w.s.pd) (hq : w.q < 2 ^ (w.s.pd + w.cd))
    (hv : w.At σ ch kN pr bp cap flags) (hm : w.MemOk rd) :
    BlockOk rd σ (oqWalkT w.s bp cap flags pr kN ch) :=
  blockOk_append.mpr ⟨hv.oqPath_complete hsl hm,
    blockOk_of_atoms (oqCapT_atoms _ _ _ _ _ _) (hv.oqCap_complete hsl hcd hq hm)⟩

end WD

end
end LeanVM.Guest.B1
