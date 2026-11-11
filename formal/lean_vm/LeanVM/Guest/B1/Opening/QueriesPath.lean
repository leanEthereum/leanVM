/-
  LeanVM.Guest.B1.Opening.QueriesPath

  One query's Merkle path below the cap: `walk_path` climbs the leaf by the hinted siblings,
  a window of six levels a dispatch, the arm's order bits the position's.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesLeaf
public import LeanVM.Guest.B1.Merkle.Climb
public import LeanVM.Guest.B1.Opening.QueriesFlat

/-!
# A query's Merkle path (`walk_path`, `walk_window`, lean_ethereum.py:1290-1341 at 40f877dc)

`oqPair_hash`: one `keccak(a, b, out)` of two two-cell digests (the padding run as its tail and
capacity, `0x80` as its cell `8`) is `HashesPair` (G3's `keccak_one`).

`oqStep_sound`: one level of an arm hashes the running node with the hinted pair on the other
side of its order bit (`sibOff`). `oqArm_sound`, `oqWin_sound`: window `i` dispatches on its word
`g^v` to arm `v`, whose order bits are the position's `6i ..`; its levels climb on (`climbD`).
`oqPath_sound`: with each window's word the position's, the hinted pairs off the walk's side are
the cells of siblings `sibs` (`SibAt`) and the node reached is `climbD leaf q sibs` (`climb`,
V:492).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## One pair -/

/-- **A pair hash** (`keccak(path[4l:4l+2], path[4l+2:4l+4], node)`): 64 bytes, the padding run
`1, 0, 0, 0, 0` as tail and capacity, `0x80 << 56` as cell `8`. -/
theorem oqPair_hash {c0 c1 c2 c3 w : V} {pr : ℕ} {outs : List V}
    (hpad : σ (.n pr) = word 1 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0)
    (hw : σ w = word (2 ^ 63) 0)
    (hK : (Atom.keccak [c0, c1, c2, c3, .n pr, .n (pr + 1), .n (pr + 2), .n (pr + 3), w,
      .n (pr + 1), .n (pr + 2), .n (pr + 3), .n (pr + 4)] outs false false).Holds rd σ)
    (ho : 2 ≤ outs.length := by simp) :
    HashesPair (σ c0) (σ c1) (σ c2) (σ c3) (σ (outs.getD 0 (.n 0))) (σ (outs.getD 1 (.n 0))) := by
  obtain ⟨-, -, O, hKC, hO⟩ := keccak_holds_full hK
  have z1 := hz 0 (by omega); have z2 := hz 1 (by omega); have z3 := hz 2 (by omega)
  have z4 := hz 3 (by omega)
  simp only [Nat.add_zero] at z1
  rw [show pr + 1 + 1 = pr + 2 by omega] at z2
  rw [show pr + 1 + 2 = pr + 3 by omega] at z3
  rw [show pr + 1 + 3 = pr + 4 by omega] at z4
  unfold HashesPair
  have h := (keccak_one (cells := [σ c0, σ c1, σ c2, σ c3]) (len := 64) (by simp) (by decide)
    (getD_cellsBytes_of_le (by simp))
    (fun c hc ↦ by
      fin_cases c <;> simp_all [padCells, xorByte, padRead, rate, byteCell, cells13])
    (fun c hc ↦ by fin_cases c <;> simp_all [cells13]) hKC).2
  rw [List.take_of_length_le (by simp)] at h
  have e0 : O 0 = σ (outs.getD 0 (.n 0)) := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact (hO 0 (by simp; omega)).symm
  have e1 : O 1 = σ (outs.getD 1 (.n 0)) := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact (hO 1 (by simp; omega)).symm
  rw [e0, e1] at h
  exact h

/-! ## One level -/

/-- The sibling's first cell at level `l` of the walk to `q`: the pair's left at bit `1`, its
right at bit `0`. -/
def sibOff (q l : ℕ) : ℕ := if q.testBit l then 0 else 2

/-- The hinted pair off the walk's side at level `l` holds the digest `d`. -/
def SibAt (σ : Val) (ch q l : ℕ) (d : Digest) : Prop :=
  (σ (.n (ch + 4 * l + sibOff q l)), σ (.n (ch + 4 * l + sibOff q l + 1))) = digestHalves d

theorem oqStepT_mem_keccak (pr ch l K n0 n1 : ℕ) (bit : Bool) :
    Stmt.atom (.keccak ((if bit then [.n (ch + 4 * l), .n (ch + 4 * l + 1), .n n0, .n n1]
        else [.n n0, .n n1, .n (ch + 4 * l + 2), .n (ch + 4 * l + 3)]) ++
      [.n pr, .n (pr + 1), .n (pr + 2), .n (pr + 3), .n K, .n (pr + 1), .n (pr + 2), .n (pr + 3),
        .n (pr + 4)]) [.n (K + 1), .n (K + 2)] false false) ∈
      oqStepT pr ch l K n0 n1 bit := by
  simp [oqStepT]

/-- **One level of an arm**: the running node `node` at `n0, n1` hashed with the hinted pair on
the other side of the order bit, the pair a digest's cells, the next node at `K + 1, K + 2`. -/
theorem oqStep_sound {pr ch l K n0 n1 : ℕ} {bit : Bool}
    (hA : ∀ a, Stmt.atom a ∈ oqStepT pr ch l K n0 n1 bit → a.Holds rd σ)
    (hpad : σ (.n pr) = word 1 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0) {node : Digest}
    (hnode : (σ (.n n0), σ (.n n1)) = digestHalves node) :
    ∃ sib : Digest,
      (σ (.n (ch + 4 * l + (if bit then 0 else 2))),
        σ (.n (ch + 4 * l + (if bit then 0 else 2) + 1))) = digestHalves sib ∧
      (σ (.n (K + 1)), σ (.n (K + 2))) =
        digestHalves (if bit then hashPair sib node else hashPair node sib) := by
  have a0 := hA _ (by simp [oqStepT] : Stmt.atom (.const (.n K) (word (2 ^ 63) 0)) ∈ _)
  have a1 := hA _ (oqStepT_mem_keccak pr ch l K n0 n1 bit)
  simp only [Atom.Holds] at a0
  have hout : ∀ (x y : E), (x, y) = (σ (([V.n (K + 1), V.n (K + 2)]).getD 0 (.n 0)),
      σ (([V.n (K + 1), V.n (K + 2)]).getD 1 (.n 0))) →
      (x, y) = (σ (.n (K + 1)), σ (.n (K + 2))) := fun x y h ↦ by
    rw [h]; simp [List.getD_eq_getElem?_getD]
  cases bit
  · simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at a1
    obtain ⟨dl, dr, hl, hr, hp⟩ := hashesPair_digests (oqPair_hash hpad hz a0 a1)
    have hdl : dl = node := capDigestScalars_injective (by rw [← hl, ← hnode])
    subst hdl
    refine ⟨dr, by simpa using hr, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact (hout _ _ hp.symm).symm
  · simp only [↓reduceIte, List.cons_append, List.nil_append] at a1
    obtain ⟨dl, dr, hl, hr, hp⟩ := hashesPair_digests (oqPair_hash hpad hz a0 a1)
    have hdr : dr = node := capDigestScalars_injective (by rw [← hr, ← hnode])
    subst hdr
    refine ⟨dl, by simpa using hl, ?_⟩
    simp only [↓reduceIte]
    exact (hout _ _ hp.symm).symm

/-! ## An arm -/

theorem oqArmT_mem_step {s : Oq} {pr kL ch i a r : ℕ} (hr : r < oqWw s i) {x : Atom}
    (hx : Stmt.atom x ∈ oqStepT pr ch (6 * i + r) (oqArmK s ch i a + 3 * r)
      (oqArmN s kL ch i a r 0) (oqArmN s kL ch i a r 1) (a.testBit r)) :
    Stmt.atom x ∈ oqArmT s pr kL ch i a := by
  unfold oqArmT
  exact List.mem_append_left _
    (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, hx⟩)

theorem climbD_step {leaf : Digest} {q : ℕ} {cs : List Digest} {sib : Digest} :
    climbD leaf q (cs ++ [sib]) = if q.testBit cs.length then hashPair sib (climbD leaf q cs)
      else hashPair (climbD leaf q cs) sib := by
  rw [climbD_snoc, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : q / 2 ^ cs.length % 2 = 1
  · simp [h]
  · simp [show q / 2 ^ cs.length % 2 = 0 by omega]

/-- **An arm** (`walk_window`): with its order bits the position's from level `6i` and the node it
starts from `climbD leaf q sibs0` (`6i` siblings), its levels' pairs off the walk's side hold
siblings `sibs` and the node copied into the match's targets is `climbD leaf q (sibs0 ++ sibs)`. -/
theorem oqArm_sound {s : Oq} {pr kL ch i a : ℕ}
    (hA : ∀ x, Stmt.atom x ∈ oqArmT s pr kL ch i a → x.Holds rd σ)
    (hpad : σ (.n pr) = word 1 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0) {q : ℕ}
    (hbits : ∀ r < oqWw s i, a.testBit r = q.testBit (6 * i + r)) {leaf : Digest}
    {sibs0 : List Digest} (hl0 : sibs0.length = 6 * i)
    (hnode : (σ (.n (oqNd s kL ch i 0)), σ (.n (oqNd s kL ch i 1))) =
      digestHalves (climbD leaf q sibs0)) :
    ∃ sibs : List Digest, sibs.length = oqWw s i ∧
      (∀ r < oqWw s i, SibAt σ ch q (6 * i + r) (sibs.getD r default)) ∧
      (σ (.n (oqWT s ch i)), σ (.n (oqWT s ch i + 1))) =
        digestHalves (climbD leaf q (sibs0 ++ sibs)) := by
  suffices h : ∀ m ≤ oqWw s i, ∃ sibs : List Digest, sibs.length = m ∧
      (∀ r < m, SibAt σ ch q (6 * i + r) (sibs.getD r default)) ∧
      (σ (.n (oqArmN s kL ch i a m 0)), σ (.n (oqArmN s kL ch i a m 1))) =
        digestHalves (climbD leaf q (sibs0 ++ sibs)) by
    obtain ⟨sibs, hl, hs, hn⟩ := h _ le_rfl
    have c0 := hA _ (by simp [oqArmT] : Stmt.atom (.copy (.n (oqWT s ch i))
      (.n (oqArmN s kL ch i a (oqWw s i) 0))) ∈ _)
    have c1 := hA _ (by simp [oqArmT] : Stmt.atom (.copy (.n (oqWT s ch i + 1))
      (.n (oqArmN s kL ch i a (oqWw s i) 1))) ∈ _)
    simp only [Atom.Holds] at c0 c1
    exact ⟨sibs, hl, hs, by rw [c0, c1, hn]⟩
  intro m hm
  induction m with
  | zero => exact ⟨[], rfl, fun r hr ↦ absurd hr (by omega), by simpa [oqArmN] using hnode⟩
  | succ m ih =>
    obtain ⟨sibs, hl, hs, hn⟩ := ih (by omega)
    obtain ⟨sib, hsib, hnext⟩ := oqStep_sound (fun x hx ↦ hA x (oqArmT_mem_step (by omega) hx))
      hpad hz hn
    have hb := hbits m (by omega)
    refine ⟨sibs ++ [sib], by simp [hl], fun r hr ↦ ?_, ?_⟩
    · by_cases hr' : r < m
      · have := hs r hr'
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      · obtain rfl : r = m := by omega
        have e : (sibs ++ [sib]).getD r default = sib := by
          simp [List.getD_eq_getElem?_getD, hl]
        rw [e, SibAt, sibOff, ← hb, show ch + 4 * (6 * i + r) = ch + 4 * (6 * i + r) from rfl]
        exact hsib
    · have e0 : oqArmN s kL ch i a (m + 1) 0 = oqArmK s ch i a + 3 * m + 1 := by
        simp [oqArmN]
      have e1 : oqArmN s kL ch i a (m + 1) 1 = oqArmK s ch i a + 3 * m + 2 := by
        simp [oqArmN]
      rw [e0, e1, hnext, ← List.append_assoc, climbD_step, List.length_append, hl0, hl, ← hb]

/-! ## A window -/

theorem oqWw_le (s : Oq) (i : ℕ) : oqWw s i ≤ 6 := by
  unfold oqWw oqNpw; split <;> omega

/-- **Window `i`**: its word `g^v`, `v` below its arms' count, with `v`'s bits the position's
from level `6i`: arm `v` climbs (`oqArm_sound`). -/
theorem oqWin_sound {s : Oq} {bp : V} {pr kL ch i : ℕ}
    (hA : BlockOk rd σ (oqWinT s bp pr kL ch i))
    (hpad : σ (.n pr) = word 1 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0) {q v : ℕ}
    (hw : σ (.n (oqWk s ch i)) = gen ^ v) (hv : v < 2 ^ oqWw s i)
    (hbits : ∀ r < oqWw s i, v.testBit r = q.testBit (6 * i + r)) {leaf : Digest}
    {sibs0 : List Digest} (hl0 : sibs0.length = 6 * i)
    (hnode : (σ (.n (oqNd s kL ch i 0)), σ (.n (oqNd s kL ch i 1))) =
      digestHalves (climbD leaf q sibs0)) :
    ∃ sibs : List Digest, sibs.length = oqWw s i ∧
      (∀ r < oqWw s i, SibAt σ ch q (6 * i + r) (sibs.getD r default)) ∧
      (σ (.n (oqWT s ch i)), σ (.n (oqWT s ch i + 1))) =
        digestHalves (climbD leaf q (sibs0 ++ sibs)) := by
  have hm := hA _ (by simp [oqWinT] : Stmt.match_ (.n (oqWk s ch i))
    ((List.range (2 ^ oqWw s i)).map (oqArmT s pr kL ch i)) ∈ _)
  obtain ⟨j, hj, hx, harm⟩ := hm
  have h64 : 2 ^ oqWw s i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (oqWw_le s i)
  simp only [List.length_map, List.length_range] at hj
  have hjv : j = v := match_arm_of_gen_pow (by omega) (by omega) hx hw
  subst hjv
  simp only [List.getElem_map, List.getElem_range] at harm
  exact oqArm_sound harm hpad hz hbits hl0 hnode

/-! ## The path -/

theorem oqPathT_mem_win {s : Oq} {bp : V} {pr kL ch i : ℕ} (hi : i < oqNpw s) {x : Stmt}
    (hx : x ∈ oqWinT s bp pr kL ch i) : x ∈ oqPathT s bp pr kL ch := by
  unfold oqPathT
  exact List.mem_append_right _
    (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, hx⟩)

theorem oqNd_succ (s : Oq) (kL ch i c : ℕ) : oqNd s kL ch (i + 1) c = oqWT s ch i + c := by
  simp [oqNd]

/-- **The path below the cap** (`walk_path`): with each window's word `g^v`, `v`'s bits the
position's from level `6i`, and the leaf's digest the first node, the hinted pairs off the walk's
side hold siblings `sibs` and the node reached, the cap leaf's, is `climbD leaf q sibs`
(`climb`, V:492). -/
theorem oqPath_sound {s : Oq} {bp : V} {pr kL ch q : ℕ} {leaf : Digest}
    (hA : BlockOk rd σ (oqPathT s bp pr kL ch))
    (hpad : σ (.n pr) = word 1 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0)
    (hwin : ∀ i < oqNpw s, ∃ v < 2 ^ oqWw s i, σ (.n (oqWk s ch i)) = gen ^ v ∧
      ∀ r < oqWw s i, v.testBit r = q.testBit (6 * i + r))
    (hleaf : (σ (.n (oqNd s kL ch 0 0)), σ (.n (oqNd s kL ch 0 1))) = digestHalves leaf) :
    ∃ sibs : List Digest, sibs.length = s.pd ∧
      (∀ l < s.pd, SibAt σ ch q l (sibs.getD l default)) ∧
      (σ (.n (oqNd s kL ch (oqNpw s) 0)), σ (.n (oqNd s kL ch (oqNpw s) 1))) =
        digestHalves (climbD leaf q sibs) := by
  suffices h : ∀ m ≤ oqNpw s, ∃ sibs : List Digest, sibs.length = min (6 * m) s.pd ∧
      (∀ l < min (6 * m) s.pd, SibAt σ ch q l (sibs.getD l default)) ∧
      (σ (.n (oqNd s kL ch m 0)), σ (.n (oqNd s kL ch m 1))) =
        digestHalves (climbD leaf q sibs) by
    obtain ⟨sibs, hl, hs, hn⟩ := h _ le_rfl
    have e : min (6 * oqNpw s) s.pd = s.pd := by unfold oqNpw; omega
    rw [e] at hl hs
    exact ⟨sibs, hl, hs, hn⟩
  intro m hm
  induction m with
  | zero => exact ⟨[], by simp, fun l hl ↦ absurd hl (by omega), by rw [climbD_nil]; exact hleaf⟩
  | succ m ih =>
    obtain ⟨sibs, hl, hs, hn⟩ := ih (by omega)
    have hm6 : min (6 * m) s.pd = 6 * m := by unfold oqNpw at hm; omega
    rw [hm6] at hl hs
    obtain ⟨v, hv, hw, hb⟩ := hwin m (by omega)
    obtain ⟨sw, hsl, hss, hsn⟩ := oqWin_sound (hA.mono fun x hx ↦ oqPathT_mem_win (by omega) hx)
      hpad hz hw hv hb hl hn
    have hww : 6 * m + oqWw s m = min (6 * (m + 1)) s.pd := by
      unfold oqWw; unfold oqNpw at hm ⊢; split <;> omega
    refine ⟨sibs ++ sw, by simp [hl, hsl, hww], fun l hl' ↦ ?_, ?_⟩
    · by_cases h : l < 6 * m
      · have := hs l h
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      · have := hss (l - 6 * m) (by omega)
        rw [show 6 * m + (l - 6 * m) = l by omega] at this
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl,
          ← List.getD_eq_getElem?_getD]
    · rw [oqNd_succ, oqNd_succ, Nat.add_zero]; exact hsn

end
end LeanVM.Guest.B1
