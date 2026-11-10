/-
  LeanVM.Guest.B1.VerifySub.H.Lin

  The words `verify_sub`'s callees read on an honest child: slices of the caller's words (the
  exponent tables) and of `verify_sub`'s own buffers (the stream's segments among them).
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Own
public import LeanVM.Guest.B1.Tables.VtC.ADefs

/-!
# The callees' words

`SubOf L q`: `q`'s words are a slice of an entry of `L`; a memory holding `L` reads them
(`subOf_memL`), and they lie in `L`'s region (`subOf_region`). The exponent tables' sections
(`expTableWords`, its squares and rank keys, `Tables.expTableWordsW`, the window table) are slices of the
caller's `expTabAllWords` (`subOf_exp`). `ChildSegs.stream_eq`: the stream buffer's words are the
segments, so each segment the callees read at its cursor is a slice of the own buffers
(`sub_stream`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- `q`'s words are a slice of an entry of `L`. -/
def SubOf (L : Main.Layout) (q : ℕ × List E) : Prop :=
  ∃ q' ∈ L, ∃ off, q.1 = q'.1 + off ∧ off + q.2.length ≤ q'.2.length ∧
    q.2 = (q'.2.drop off).take q.2.length

theorem subOf_self {L : Main.Layout} {q : ℕ × List E} (hq : q ∈ L) : SubOf L q :=
  ⟨q, hq, 0, by simp, by simp, by simp⟩

theorem subOf_memL {rd : Reader} {L : Main.Layout} (hL : Main.MemL rd L) {q : ℕ × List E}
    (h : SubOf L q) : ReadsAt rd (ofK (addressOfIndex q.1)) q.2 := by
  obtain ⟨q', hq', off, h1, h2, h3⟩ := h
  have hr := hL q' hq'
  intro k hk
  have := hr (off + k) (by omega)
  rw [h1, ← ofK_gpow_mul_gen, loadHolds_mul_gen_pow]
  have e : q.2[k] = q'.2[off + k] := by
    have : q.2[k] = ((q'.2.drop off).take q.2.length)[k]'(by rw [← h3]; exact hk) := by
      congr 1
    rw [this, List.getElem_take, List.getElem_drop]
  rw [e]; exact this

theorem subOf_region {L : Main.Layout} {q : ℕ × List E} (h : SubOf L q) {i : ℕ} (h1 : q.1 ≤ i)
    (h2 : i < q.1 + q.2.length) : Main.RegionL L i := by
  obtain ⟨q', hq', off, e1, e2, -⟩ := h
  exact ⟨q', hq', by omega, by omega⟩

/-- A slice of an entry. -/
theorem subOf_slice {L : Main.Layout} {b : ℕ} {xs : List E} (hq : (b, xs) ∈ L) (off : ℕ)
    (ys : List E) (hl : off + ys.length ≤ xs.length) (hy : ys = (xs.drop off).take ys.length) :
    SubOf L (b + off, ys) :=
  ⟨(b, xs), hq, off, rfl, hl, hy⟩

/-- A middle piece of an entry's words. -/
theorem subOf_mid {L : Main.Layout} {b : ℕ} {P X R : List E} (hq : (b, P ++ X ++ R) ∈ L) :
    SubOf L (b + P.length, X) :=
  subOf_slice hq _ _ (by simp) (by rw [List.append_assoc, List.drop_left, List.take_left])

/-! ## The exponent tables -/

theorem expTabAll_prefix : expTabAllWords.take 236 = expTableWords := by
  apply List.ext_getElem (by simp [length_expTabAllWords, expTableWords, length_etWordsN])
  intro k h1 h2
  simp only [List.getElem_take]
  have hk : k < 236 := by simp at h1; omega
  rw [← List.getD_eq_getElem _ 0, expTabAllWords_getD, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
    expTabWord, ite_eq_left_of_eq_true _ _ (eq_true hk), List.getD_eq_getElem _ _ h2]

theorem expTabAll_win : (expTabAllWords.drop 236).take (2 ^ winTabBits) =
    (List.range (2 ^ winTabBits)).map eOfNat := by
  apply List.ext_getElem (by simp [length_expTabAllWords, winTabBits])
  intro k h1 h2
  simp only [List.length_map, List.length_range] at h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  have hk : k < 2048 := by simpa [winTabBits] using h2
  rw [← List.getD_eq_getElem _ 0, expTabAllWords_getD, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
    expTabWord, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel_left]

theorem expTabAll_W : expTabAllWords.take (236 + 2 ^ winTabBits) = Tables.expTableWordsW := by
  have hl : expTableWords.length = 236 := by simp [expTableWords, length_etWordsN]
  apply List.ext_getElem (by rw [Tables.length_expTableWordsW]; simp [length_expTabAllWords, winTabBits])
  intro k h1 h2
  simp only [List.getElem_take]
  have hk2 : k < 2284 := by simp [length_expTabAllWords, winTabBits] at h1; omega
  rw [← List.getD_eq_getElem _ 0, expTabAllWords_getD, ite_eq_left_of_eq_true _ _ (eq_true hk2),
    expTabWord]
  by_cases hk : k < 236
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hk)]
    simp only [Tables.expTableWordsW]
    rw [List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
    simp only [Tables.expTableWordsW]
    rw [List.getElem_append_right (by omega)]
    simp [hl]

/-- A section of the caller's exponent tables at `off`. -/
theorem subOf_exp {Lin : Main.Layout} {sqE : ℕ} (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (off : ℕ)
    (ys : List E) (hl : off + ys.length ≤ 2284)
    (hy : ys = (expTabAllWords.drop off).take ys.length) : SubOf Lin (sqE + off, ys) :=
  subOf_slice (hexp _ List.mem_cons_self) off ys (by rw [length_expTabAllWords]; exact hl) hy

theorem subOf_expTableWords {Lin : Main.Layout} {sqE : ℕ}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) : SubOf Lin (sqE, expTableWords) := by
  have := subOf_exp hexp 0 expTableWords (by simp [expTableWords, length_etWordsN])
    (by rw [List.drop_zero, show expTableWords.length = 236 by
      simp [expTableWords, length_etWordsN], expTabAll_prefix])
  simpa using this

theorem subOf_Tables.expTableWordsW {Lin : Main.Layout} {sqE : ℕ}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) : SubOf Lin (sqE, Tables.expTableWordsW) := by
  have := subOf_exp hexp 0 Tables.expTableWordsW (by rw [Tables.length_expTableWordsW]; simp [winTabBits])
    (by rw [List.drop_zero, Tables.length_expTableWordsW, expTabAll_W])
  simpa using this

theorem subOf_winTab {Lin : Main.Layout} {sqE : ℕ} (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) :
    SubOf Lin (sqE + winTabAt, winTabWords) :=
  subOf_exp hexp 236 winTabWords (by simp [winTabWords, winTabBits])
    (by rw [show winTabWords.length = 2 ^ winTabBits by simp [winTabWords], expTabAll_win]; rfl)

/-! ## The stream -/

/-- The stream buffer's padding. -/
def streamPad (stream : List E) : List E :=
  List.replicate (Coverage.childStreamCap - stream.length) 0

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **The stream buffer's words**: the segments, then the padding. -/
theorem stream_eq (hbl : bytecode.length = 2 ^ 23) : vsStreamW c.proof.stream =
    sizeWords S.logMem S.rowsN S.rate ++ [S.x0, S.x1] ++ [S.oodN, S.oodV] ++ [S.busN] ++ S.xsG ++
      S.xsT ++ S.xsK ++ [S.ringN] ++ S.xsW ++
      List.replicate (Coverage.childStreamCap - c.proof.stream.length) 0 := by
  rw [vsStreamW, S.hstream, S.ood_inv.1, (S.bus_inv hbl).1, S.ring_inv.1]

theorem sizeWords_length : (sizeWords S.logMem S.rowsN S.rate).length = 8 := by
  simp [sizeWords, S.hrowsL]


variable (b : ℕ)

/-- A segment of the stream, at its offset in the stream buffer. -/
theorem sub_stream {P X R : List E} (h : vsStreamW c.proof.stream = P ++ X ++ R) :
    SubOf (bufL b (vsSizes S.d) S.ownW) (vb (bases b (vsSizes S.d)) 1 + P.length, X) := by
  have hm := vs_own_mem S b (i := 1) (by norm_num)
  rw [show S.ownW.getD 1 [] = vsStreamW c.proof.stream from rfl, h] at hm
  exact subOf_mid hm

/-- The out-of-domain value and the bus grind's nonce, at `stream + 11`. -/
theorem sub_omWords (hbl : bytecode.length = 2 ^ 23) :
    SubOf (bufL b (vsSizes S.d) S.ownW) (vb (bases b (vsSizes S.d)) 1 + 11, [S.oodV, S.busN]) := by
  have h := S.sub_stream b (P := sizeWords S.logMem S.rowsN S.rate ++ [S.x0, S.x1] ++ [S.oodN])
    (X := [S.oodV, S.busN]) (R := S.xsG ++ S.xsT ++ S.xsK ++ [S.ringN] ++ S.xsW ++ streamPad c.proof.stream)
    (by rw [S.stream_eq hbl, streamPad]; simp)
  rwa [List.length_append, List.length_append, S.sizeWords_length] at h

/-- The GKR's words at its cursor. -/
theorem sub_xsG (hbl : bytecode.length = 2 ^ 23) :
    SubOf (bufL b (vsSizes S.d) S.ownW) (cG (bases b (vsSizes S.d)), S.xsG) := by
  have h := S.sub_stream b (P := sizeWords S.logMem S.rowsN S.rate ++ [S.x0, S.x1] ++
    [S.oodN, S.oodV] ++ [S.busN]) (X := S.xsG) (R := S.xsT ++ S.xsK ++ [S.ringN] ++ S.xsW ++ streamPad c.proof.stream)
    (by rw [S.stream_eq hbl, streamPad]; simp)
  simp only [List.length_append, S.sizeWords_length, List.length_cons, List.length_nil] at h
  exact h

/-- The tables' words at their cursor. -/
theorem sub_xsT (hbl : bytecode.length = 2 ^ 23) :
    SubOf (bufL b (vsSizes S.d) S.ownW) (S.cT (bases b (vsSizes S.d)), S.xsT) := by
  have h := S.sub_stream b (P := sizeWords S.logMem S.rowsN S.rate ++ [S.x0, S.x1] ++
    [S.oodN, S.oodV] ++ [S.busN] ++ S.xsG) (X := S.xsT) (R := S.xsK ++ [S.ringN] ++ S.xsW ++ streamPad c.proof.stream)
    (by rw [S.stream_eq hbl, streamPad]; simp)
  simp only [List.length_append, S.sizeWords_length, List.length_cons, List.length_nil] at h
  rwa [show vb (bases b (vsSizes S.d)) 1 + (8 + 2 + 2 + 1 + S.xsG.length) =
    S.cT (bases b (vsSizes S.d)) by simp only [ChildSegs.cT, cG]; omega] at h

/-- The Keccak reduction's words at their cursor. -/
theorem sub_xsK (hbl : bytecode.length = 2 ^ 23) :
    SubOf (bufL b (vsSizes S.d) S.ownW) (S.cK (bases b (vsSizes S.d)), S.xsK) := by
  have h := S.sub_stream b (P := sizeWords S.logMem S.rowsN S.rate ++ [S.x0, S.x1] ++
    [S.oodN, S.oodV] ++ [S.busN] ++ S.xsG ++ S.xsT) (X := S.xsK) (R := [S.ringN] ++ S.xsW ++ streamPad c.proof.stream)
    (by rw [S.stream_eq hbl, streamPad]; simp)
  simp only [List.length_append, S.sizeWords_length, List.length_cons, List.length_nil] at h
  rwa [show vb (bases b (vsSizes S.d)) 1 + (8 + 2 + 2 + 1 + S.xsG.length + S.xsT.length) =
    S.cK (bases b (vsSizes S.d)) by simp only [ChildSegs.cK, ChildSegs.cT, cG]; omega] at h

/-- The opening's words at their cursor. -/
theorem sub_xsW (hbl : bytecode.length = 2 ^ 23) :
    SubOf (bufL b (vsSizes S.d) S.ownW) (S.cW (bases b (vsSizes S.d)), S.xsW) := by
  have h := S.sub_stream b (P := sizeWords S.logMem S.rowsN S.rate ++ [S.x0, S.x1] ++
    [S.oodN, S.oodV] ++ [S.busN] ++ S.xsG ++ S.xsT ++ S.xsK ++ [S.ringN]) (X := S.xsW) (R := streamPad c.proof.stream)
    (by rw [S.stream_eq hbl, streamPad])
  simp only [List.length_append, S.sizeWords_length, List.length_cons, List.length_nil] at h
  rwa [show vb (bases b (vsSizes S.d)) 1 + (8 + 2 + 2 + 1 + S.xsG.length + S.xsT.length +
    S.xsK.length + 1) = S.cW (bases b (vsSizes S.d)) by
    simp only [ChildSegs.cW, ChildSegs.cR, ChildSegs.cK, ChildSegs.cT, cG, S.ring_inv.1,
      List.length_cons, List.length_nil]; omega] at h

/-- Own buffer `i`. -/
theorem sub_own {i : ℕ} (hi : i < 15) :
    SubOf (bufL b (vsSizes S.d) S.ownW) (vb (bases b (vsSizes S.d)) i, S.ownW.getD i []) :=
  subOf_self (vs_own_mem S b hi)

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
