module

public import NativeRustcVmArm.Wire.WriteOpenings.End

/-!
# `write_openings`' scans and copies, both branches

The first position of a query (`pos_some`, `pos_none`); what survives writes apart from the phase
(`Geo.begun_keepW`, `Geo.leaf_keepW`); a leaf's word in memory (`lfw_at`) and one more copied
(`leaf_succ`); the frame's writes (`Geo.frame_apart`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)

@[expose] public section

/-- Opening `j` begun: the first `j` openings, the head, the query's word. -/
def Begun (R : Run) (j : Nat) (d : Mem 64) : Prop := R.Done d j ∧ WordAt d (R.oa (ob j)) (R.qw j)

end

public section

variable {R : Run}

/-! ## Positions -/

theorem pos_some {q : UInt64} {i : Nat} (hi : i < R.np) (he : R.pw i = q)
    (hm : ∀ i' < i, R.pw i' ≠ q) : R.pos q = some i := by
  unfold Run.pos
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨by simpa using hi, by simp [he], fun i' hi' ↦ ?_⟩
  simp only [List.getElem_map, List.getElem_range, beq_iff_eq]
  exact hm i' hi'

theorem pos_none {q : UInt64} (hm : ∀ i < R.np, R.pw i ≠ q) : R.pos q = none := by
  unfold Run.pos
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact beq_eq_false_iff_ne.mpr (hm i hi)

/-- No position holds query `j`: a rejection. -/
theorem bad_of_none {j : Nat} (hj : j < R.nq) (hm : ∀ i < R.np, R.pw i ≠ R.qw j) : R.Bad :=
  .inl ⟨j, hj, pos_none hm⟩

/-! ## Writes apart from the phase -/

/-- Words of the phase survive a write apart from the phase. -/
theorem Geo.wordsAt_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {a : Nat}
    {ws : List UInt64} (h : WordsAt d (R.oa a) ws) (ha : a + 8 * ws.length ≤ phaseBytes) :
    WordsAt d' (R.oa a) ws :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi ↦ by
    rw [NativeRustcVm.length_wordsBytes] at hi
    rw [NativeRustcVm.addr_add_add]
    exact hW _ (NativeRustcVm.inRange_add (by omega) (by
      have := G.outNw; unfold NativeRustcVm.NoWrap at this; omega))

theorem Geo.wordAt_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {a : Nat}
    {w : UInt64} (h : WordAt d (R.oa a) w) (ha : a + 8 ≤ phaseBytes) : WordAt d' (R.oa a) w := by
  rw [← NativeRustcVm.wordsAt_singleton_iff] at h ⊢
  exact G.wordsAt_keepW hs hW h (by simpa using ha)

theorem Geo.done_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {j : Nat}
    (hj : j ≤ R.nq) (h : R.Done d j) : R.Done d' j := by
  obtain ⟨⟨h0, h8, h16⟩, hop⟩ := h
  have hlw := G.lw64
  have hh := G.h32
  refine ⟨⟨G.wordAt_keepW hs hW h0 (by decide), G.wordAt_keepW hs hW h8 (by decide),
    G.wordAt_keepW hs hW h16 (by decide)⟩, fun j' hj' ↦ ?_⟩
  obtain ⟨i, hi, hq, hl, hp⟩ := hop j' hj'
  have hob := ob_le (j := j') (by have := G.nq256; omega)
  refine ⟨i, hi, G.wordAt_keepW hs hW hq (by omega), G.wordsAt_keepW hs hW hl (by simp; omega),
    G.wordsAt_keepW hs hW hp (by rw [path_length]; omega)⟩

theorem Geo.begun_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {j : Nat}
    (hj : j < R.nq) (h : Begun R j d) : Begun R j d' :=
  ⟨G.done_keepW hs hW (by omega) h.1,
    G.wordAt_keepW hs hW h.2 (by have := ob_le (j := j) (by have := G.nq256; omega); omega)⟩

theorem Geo.leaf_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {j i t : Nat}
    (hj : j < R.nq) (ht : t ≤ R.lw) (h : R.LeafPart d j i t) : R.LeafPart d' j i t := by
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  have := G.lw64
  exact G.wordsAt_keepW hs hW h (by simp; omega)

/-- The frame's bytes `o` to `o + n` are apart from the phase. -/
theorem Geo.frame_apart (G : Geo R) {o n : Nat} (hon : o + n ≤ 176) :
    ∀ p, InRange R.out phaseBytes p → ¬InRange (base R.m0 176 + BitVec.ofNat 64 o) n p := by
  intro p hp hq
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; unfold InRange at hq; omega
  have hin : Inside (base R.m0 176 + BitVec.ofNat 64 o) n (R.big 0) :=
    inside_off (A := R.big 0) (G.noWrap (i := 0) (by omega)) hon h0
  exact G.not_in (i := 0) (j := 7) (by omega) (by omega) (by omega) hin hq hp

/-! ## Leaves -/

/-- Word `t` of leaf `i` in the memory of a state of the frame. -/
theorem lfw_at (G : Geo R) {m : MachineData} (hfr : Frm R m) {i t : Nat} (hi : i < R.np)
    (ht : t < 64) : wordOf m.dmem (R.lv + BitVec.ofNat 64 (512 * i + 8 * t)) = R.lfw i t := by
  have hw : R.lv.toNat + 512 * R.np ≤ 2 ^ 64 := G.noWrap (i := 4) (by omega)
  refine G.wordOf_keep hfr (i := 4) (by omega) (by omega) ?_
  show R.lv.toNat ≤ _ ∧ _ ≤ R.lv.toNat + 512 * R.np
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- Leaf `i`'s bytes from word `t` on are in the leaves' region. -/
theorem leaf_inside (G : Geo R) {i t n : Nat} (hi : i < R.np) (htn : 8 * t + n ≤ 512)
    (hn : 0 < n) : Inside (R.lv + BitVec.ofNat 64 (512 * i + 8 * t)) n (R.big 4) := by
  have hw : R.lv.toNat + 512 * R.np ≤ 2 ^ 64 := G.noWrap (i := 4) (by omega)
  show R.lv.toNat ≤ _ ∧ _ ≤ R.lv.toNat + 512 * R.np
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- Opening `j`'s bytes from leaf word `t` on are in the phase. -/
theorem opening_inside (G : Geo R) {j t n : Nat} (hj : j < R.nq) (htn : 8 * t + n ≤ 512)
    (hn : 0 < n) : Inside (R.oa (ob j + 8 + 8 * t)) n (R.big 7) := by
  have := ob_le (j := j) (by have := G.nq256; omega)
  exact inside_off G.outNw (by show _ ≤ phaseBytes; unfold ob at *; omega) hn

/-- One more leaf word copied. -/
theorem leaf_succ {d : Mem 64} {j i t : Nat} (h : R.LeafPart d j i t)
    (hw : WordAt d (R.oa (ob j + 8 + 8 * t)) (R.lfw i t)) : R.LeafPart d j i (t + 1) := by
  unfold Run.LeafPart at *
  rw [List.range_succ, List.map_append, NativeRustcVm.wordsAt_append_iff]
  refine ⟨h, ?_⟩
  rw [List.length_map, List.length_range, NativeRustcVm.addr_add_add]
  simpa [NativeRustcVm.wordsAt_singleton_iff] using hw

theorem leaf_zero {d : Mem 64} {j i : Nat} : R.LeafPart d j i 0 := by
  unfold Run.LeafPart
  simp [NativeRustcVm.WordsAt, NativeRustcVm.BytesAt]

theorem path_zero {d : Mem 64} {j : Nat} : R.PathPart d j 0 := by
  unfold Run.PathPart
  simp [NativeRustcVm.WordsAt, NativeRustcVm.BytesAt]

end

end NativeRustcVmArm.Wire.WriteOpenings
