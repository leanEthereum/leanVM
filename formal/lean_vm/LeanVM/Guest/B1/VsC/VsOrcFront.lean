/-
  LeanVM.Guest.B1.VsC.VsOrcFront

  The front's honest numbers, from an accepted child.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrc
public import LeanVM.Guest.B1.VsC.Shape
public import LeanVM.Guest.B1.VsC.StreamChunks
public import LeanVM.Guest.B1.VsC.Announced
public import LeanVM.Guest.Value.Tower
public import LeanVM.Guest.End

/-!
# The front's numbers

`FrontNum`: the purely numeric fields of `FrontHyp` (the stream's chunk count and words, the rate, the
memory's log, the tables' heights and rows, the tallest height, the pointer width, its flag). An accepted
child (`VsChildOk guestBytecode`) gives them at its announced layout and rate (`frontNum_of_child`), at the
values `Prover.childHints` pushes: `chunksOf` chunks, the stream padded with zeros (`padStream`), the heights'
maximum (`hMax`), the width `widthOf` and its flag `bit (width = bitLength cycles)`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Value
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **The front's numeric hypotheses** (`FrontHyp`'s fields that name no memory and no oracle word). -/
structure FrontNum (p r m n wd : ℕ) (flag : E) (ws : List E) (h Rr : ℕ → ℕ) : Prop where
  hp1 : 1 ≤ p
  hp : p ≤ 32
  hws : ws.length = 256 * p
  hw7r : ws.getD 7 0 = eOfNat r
  hw0m : ws.getD 0 0 = eOfNat m
  hws56 : (ws.drop 1).take 6 = rowsW Rr
  hr1 : 1 ≤ r
  hr4 : r ≤ 4
  hm1 : 1 ≤ m
  h24 : ∀ t < 6, h t ≤ 24
  hR : ∀ t < 6, Rr t ≤ 2 ^ h t
  hl : ∀ t < 5, h t = 0 ∨ 2 ^ (h t - 1) < Rr t
  h9 : 9 ≤ h 5
  hl5 : h 5 ≠ 9 → 2 ^ (h 5 - 1) < Rr 5
  hht : ∀ t < 6, h t ≤ n
  hn : ∃ t < 6, h t = n
  hw19 : 19 ≤ wd
  hw24 : wd ≤ 24
  hmw : m ≤ wd
  hN : Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4 + Rr 5 < 2 ^ wd
  hflag : (flag = 1 ∧ 2 ^ (wd - 1) ≤ Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4 + Rr 5) ∨ (flag = 0 ∧ (wd = m ∨ wd = 19))

/-- The stream padded with zeros to whole chunks, as `Prover.childHints` pushes it. -/
def padStream (s : List E) : List E := s ++ List.replicate (chunksOf s.length * 256 - s.length) 0

/-- The tallest table's log height, `link_shape`'s `rows`. -/
def hMax (layout : Layout) : ℕ := layout.tableLogHeights.foldl max 0

/-- The pointer width's flag, `link_shape`'s third word. -/
def flagOf (layout : Layout) : E := Prover.bit (decide (widthOf layout = bitLength (cyclesOf layout)))

/-! ## Helpers -/

theorem eq_eOfNat_of_limb1 {v : E} (h : v.limb 1 = 0) : v = eOfNat (kToNat (v.limb 0)) := by
  rw [eOfNat_eq_ofLimbs, ofBits_kToNat, ← h]
  exact eq_ofLimbs v

theorem six_eq {l : List ℕ} (h : l.length = 6) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0] := by
  match l, h with
  | [_, _, _, _, _, _], _ => rfl

theorem foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], _ => ⟨le_rfl, by simp⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a y)
    refine ⟨le_trans (le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right _ _) h1
    · exact h2 x hx

theorem foldl_max_mem : ∀ (l : List ℕ) (a : ℕ), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => .inl rfl
  | y :: l, a => by
    rcases foldl_max_mem l (max a y) with h | h
    · simp only [List.foldl_cons, h]
      rcases le_total a y with hy | hy
      · exact .inr (by rw [max_eq_right hy]; exact List.mem_cons_self)
      · exact .inl (max_eq_left hy)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- What `sizesOf` reads of its words. -/
theorem sizesOf_words {bytecode : List K} {a : List E} {layout : Layout} {r : ℕ}
    (h : sizesOf bytecode a = some (layout, r)) :
    (∀ v ∈ a, v.limb 1 = 0) ∧ r = kToNat ((a.getLastD 0).limb 0) ∧
      layout.logMemory = kToNat ((a.headD 0).limb 0) ∧
      layout.tableRows = ((a.drop 1).take nTables).map fun v ↦ kToNat (v.limb 0) := by
  unfold sizesOf at h
  split at h
  · next h1 =>
    simp only at h
    split at h
    · obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hlm, hrows, -⟩ := buildLayout_fields hl
        exact ⟨fun v hv => by simpa using List.all_eq_true.mp h1 v hv, rfl, hlm, hrows⟩
      · cases h
    · cases h
  · cases h

/-- An accepted child's announced words: its stream's first eight. -/
theorem announced_words {bytecode : List K} {stream : List E} {layout : Layout} {r : ℕ}
    (h : announcedLayoutAndRate bytecode stream = some (layout, r)) :
    2 + nTables ≤ stream.length ∧ sizesOf bytecode (stream.take (2 + nTables)) = some (layout, r) := by
  have hs := announced_eq_run (fun _ ↦ default) (fun _ ↦ default) bytecode
    (s := ⟨⟨default, [], none⟩, stream, [], []⟩) rfl
  have e := hs.symm.trans h
  rw [run_readSizes _ _ bytecode rfl] at e
  split at e
  · exact ⟨by assumption, e⟩
  · cases e

theorem guest_logBytecode : guestBytecode.length >>> bytecodeSlotBits = 2 ^ 19 := by
  have h : guestBytecode.length = 2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits) := End.bytecode_length
  rw [h, Nat.shiftRight_eq_div_pow, pow_add, Nat.mul_div_cancel _ (by positivity)]

/-! ## The front's numbers -/

set_option maxHeartbeats 1000000 in
/-- **An accepted child's front numbers.** -/
theorem frontNum_of_child {seed : Digest} {c : Child} (hc : VsChildOk guestBytecode seed c) :
    ∃ layout r, announcedLayoutAndRate guestBytecode c.proof.stream = some (layout, r) ∧
      VsShape guestBytecode layout r ∧
      FrontNum (chunksOf c.proof.stream.length) r layout.logMemory (hMax layout) (widthOf layout) (flagOf layout)
        (padStream c.proof.stream) (fun t => layout.tableLogHeights.getD t 0) (fun t => layout.tableRows.getD t 0) := by
  obtain ⟨layout, r, hann, S⟩ := vsShape_of_verifyDeferred hc.1
  refine ⟨layout, r, hann, S, ?_⟩
  obtain ⟨hlen, hsz⟩ := announced_words hann
  obtain ⟨hl1, hr, hlm, hrows⟩ := sizesOf_words hsz
  have n6 : nTables = 6 := rfl
  rw [n6] at hlen hrows hl1 hr hlm
  simp only [show 2 + 6 = 8 from rfl] at hlen hrows hl1 hr hlm
  set s := c.proof.stream with hs
  have hcap : s.length ≤ guest_const% STREAM_CAP := hc.2.2.1
  obtain ⟨hp32, hpl, hp1, -⟩ := streamChunks_ok hcap
  have hC : guest_const% STREAM_CAP / guest_const% STREAM_CHUNK + 1 = 33 := rfl
  have hK : guest_const% STREAM_CHUNK = 256 := rfl
  rw [hC] at hp32
  rw [hK] at hpl
  -- the padded stream's first words are the stream's
  have hwd : ∀ i < s.length, (padStream s).getD i 0 = s.getD i 0 := fun i hi => by
    unfold padStream; rw [List.getD_append _ _ _ _ hi]
  have htk : ∀ i < 8, s.getD i 0 = (s.take 8).getD i 0 := fun i hi => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true]
  have hmem : ∀ i < 8, (s.take 8).getD i 0 ∈ s.take 8 := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    exact List.getElem_mem _
  have hword : ∀ i < 8, (padStream s).getD i 0 = eOfNat (kToNat (((s.take 8).getD i 0).limb 0)) :=
    fun i hi => by rw [hwd i (by omega), htk i hi]; exact eq_eOfNat_of_limb1 (hl1 _ (hmem i hi))
  -- the layout's facts
  have hrl : layout.tableRows.length = 6 := S.rows_length
  have hhl : layout.tableLogHeights.length = 6 := by rw [S.heights]; simp [hrl, tableLogFloors]
  have hRr : ∀ t < 6, layout.tableRows.getD t 0 = kToNat (((s.take 8).getD (t + 1) 0).limb 0) := fun t ht => by
    rw [hrows]
    simp [List.getD_eq_getElem?_getD, ht, show t + 1 < 8 by omega,
      List.getElem?_eq_getElem (show t + 1 < s.length by omega)]
  have hlb : layout.logBytecode = 19 :=
    Nat.pow_right_injective (le_refl 2) (S.logBytecode_eq.symm.trans guest_logBytecode)
  have hcy : cyclesOf layout = layout.tableRows.getD 0 0 + layout.tableRows.getD 1 0 +
      layout.tableRows.getD 2 0 + layout.tableRows.getD 3 0 + layout.tableRows.getD 4 0 +
      layout.tableRows.getD 5 0 := by
    unfold cyclesOf; rw [foldl_add_eq, six_eq hrl]; simp [List.sum_cons]; omega
  have hwd19 : 19 ≤ widthOf layout := by unfold widthOf pointerWidth; rw [hlb]; omega
  have hfl : ∀ t < 5, tableLogFloors.getD t 0 = 0 := by decide
  refine ⟨hp1, by omega, ?_, ?_, ?_, ?_, S.rate_ge, S.rate_le, S.logMemory_ge, fun t ht => S.height_le ht,
    fun t ht => S.rows_le ht, fun t ht => ?_, ?_, ?_, ?_, ?_, hwd19, S.width_le, ?_, ?_, ?_⟩
  · unfold padStream; simp only [List.length_append, List.length_replicate]; omega
  · rw [hword 7 (by omega), hr]
    congr 2
    simp only [List.getLastD_eq_getLast?, List.getD_eq_getElem?_getD]
    rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hlen]
  · have e : ∀ l : List E, l.getD 0 0 = l.headD 0 := fun l => by cases l <;> rfl
    rw [hword 0 (by omega), hlm, e]
  · apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, rowsW, List.length_cons, List.length_nil]
      unfold padStream; simp only [List.length_append, List.length_replicate]; omega
    · intro i h1 _
      simp only [List.length_take, List.length_drop] at h1
      rw [List.getElem_take, List.getElem_drop]
      have hi : i < 6 := by omega
      rw [← List.getD_eq_getElem (d := 0), hword (1 + i) (by omega), Nat.add_comm 1 i, ← hRr i hi]
      interval_cases i <;> rfl
  · rcases S.height_least (t := t) (by rw [n6]; omega) with h | h
    · exact .inl (h.trans (hfl t ht))
    · exact .inr h
  · have := S.height_ge_floor (t := 5) (by rw [n6]; omega); simpa [tableLogFloors, keccakMinStepsLog] using this
  · intro h5
    rcases S.height_least (t := 5) (by rw [n6]; omega) with h | h
    · exact absurd (h.trans (by decide)) h5
    · exact h
  · intro t ht
    have hm := (foldl_max_ge layout.tableLogHeights 0).2
    exact hm _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _)
  · rcases foldl_max_mem layout.tableLogHeights 0 with h | h
    · exfalso
      have h5 := S.height_ge_floor (t := 5) (by rw [n6]; omega)
      have hm := (foldl_max_ge layout.tableLogHeights 0).2 (layout.tableLogHeights.getD 5 0) (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _)
      have h9' : tableLogFloors.getD 5 0 = 9 := by decide
      omega
    · obtain ⟨t, ht, e⟩ := List.mem_iff_getElem.mp h
      exact ⟨t, by omega, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; exact e⟩
  · unfold widthOf pointerWidth; omega
  · rw [← hcy]; exact cycles_lt layout
  · rw [← hcy]
    unfold flagOf
    by_cases hb : widthOf layout = bitLength (cyclesOf layout)
    · refine .inl ⟨by simp [Prover.bit, hb], ?_⟩
      rw [hb]
      exact pow_pred_bitLength_le (fun h0 => by rw [h0, bitLength] at hb; simp at hb; omega)
    · refine .inr ⟨by simp [Prover.bit, hb], ?_⟩
      rcases width_cases layout with h | h | h | h
      · exact absurd h hb
      · exact .inl h
      · exact .inr (h.trans hlb)
      · omega

end
end LeanVM.Guest.B1.VsC
