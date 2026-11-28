module

public import LeanVM.Guest.Complete.Agg.Lib
public import LeanVM.Guest.B1.Main.AggAbsorb
public import LeanVM.Guest.B1.Main.AggRun

/-!
# `aggregate_claims`' honest rows

A row's thirteen words (`rowW`: the capacity cells, then the rate cells of the waiting scalars), the
absorbing rows' sponges (`absSt`), restored from the archive's `AggCDefs`. `rowRel_of_reads`: a row
of honest words carries its sponge (`RowRel`); `absSt_ok`: the honest sponges' capacity cells are a
state's, their scalars tagged `1`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Node

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-- A row's thirteen words: the capacity cells, then the rate cells of the waiting scalars. -/
def rowW (s : Fs) : List E := s.cap ++ rateOf s.pend

/-- The absorbing row `c`'s sponge: after the count and the first `c` children's words. -/
def absSt (m : ℕ) (cs : List ChildClaims) (c : ℕ) : Fs :=
  aggS0.absorbAll (Batch.childCountCells m ++ (cs.take c).flatMap Batch.childCells) dsObserve

/-- The sponge's capacity cells are a state's, its scalars tagged `1`, at most four. -/
def StOk (s : Fs) : Prop :=
  (∃ S, s.cap = capOf S) ∧ s.pend.length ≤ 4 ∧ ∀ q ∈ s.pend, q.2 = dsObserve

theorem stOk_absorb {s : Fs} (h : StOk s) (x : E) : StOk (s.absorb x dsObserve) := by
  obtain ⟨⟨S, hS⟩, hl, ht⟩ := h
  unfold Fs.absorb
  split
  · refine ⟨⟨_, rfl⟩, by simp, fun q hq => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hq]
  · rename_i hne
    refine ⟨⟨S, hS⟩, ?_, fun q hq => ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      simp only [rateScalars] at hne
      omega
    · rcases List.mem_append.mp hq with hq | hq
      · exact ht q hq
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rw [hq]

theorem stOk_absorbAll : ∀ (xs : List E) {s : Fs}, StOk s → StOk (s.absorbAll xs dsObserve)
  | [], _, h => h
  | x :: xs, _, h => stOk_absorbAll xs (stOk_absorb h x)

theorem stOk_aggS0 : StOk aggS0 := ⟨⟨_, rfl⟩, by simp [aggS0], fun q hq => by simp [aggS0] at hq⟩

theorem absSt_ok (m : ℕ) (cs : List ChildClaims) (c : ℕ) : StOk (absSt m cs c) :=
  stOk_absorbAll _ stOk_aggS0

theorem capOf_length (S : KeccakState) : (capOf S).length = 5 := rfl

theorem rowW_length {s : Fs} (h : StOk s) : (rowW s).length = 13 := by
  obtain ⟨⟨S, hS⟩, -, -⟩ := h
  simp [rowW, hS, capOf_length, rateOf]

theorem rowW_getD_cap {s : Fs} (h : StOk s) {i : ℕ} (hi : i < 5) :
    (rowW s).getD i 0 = s.cap.getD i 0 := by
  obtain ⟨⟨S, hS⟩, -, -⟩ := h
  rw [rowW, List.getD_append _ _ _ _ (by rw [hS, capOf_length]; exact hi)]

theorem rowW_getD_rate {s : Fs} (h : StOk s) {c : ℕ} (hc : c < 8) :
    (rowW s).getD (5 + c) 0 = Keccak.rateCell s.pend c := by
  obtain ⟨⟨S, hS⟩, -, -⟩ := h
  rw [rowW, List.getD_append_right _ _ _ _ (by rw [hS, capOf_length]; omega), hS, capOf_length,
    show 5 + c - 5 = c by omega]
  simp [rateOf, List.getD_eq_getElem?_getD, hc]

/-- **A row of honest words carries its sponge.** -/
theorem rowRel_of_reads {rd : Reader} {p : E} {s : Fs} (hs : StOk s) (h : ReadsAt rd p (rowW s)) :
    RowRel rd p s := by
  have hl := rowW_length hs
  have hm : ∀ k < 13, memAt rd p k = (rowW s).getD k 0 := fun k hk =>
    memAt_of_reads h (by rw [hl]; exact hk)
  obtain ⟨⟨S, hS⟩, hpl, ht⟩ := hs
  refine ⟨?_, hpl, fun k hk => ?_⟩
  · rw [rowCap, hS]
    refine list_eq_of_getD (n := 5) (by rfl) (by simp) fun i hi => ?_
    have e : (List.map (fun i ↦ memAt rd p i) (List.range 5)).getD i 0 = memAt rd p i := by
      simp [List.getD_eq_getElem?_getD, hi]
    rw [e, hm i (by omega), rowW_getD_cap ⟨⟨S, hS⟩, hpl, ht⟩ hi, hS]
  · have e1 := hm (5 + 2 * k) (by omega)
    have e2 := hm (6 + 2 * k) (by omega)
    rw [rowW_getD_rate ⟨⟨S, hS⟩, hpl, ht⟩ (by omega)] at e1
    rw [show 6 + 2 * k = 5 + (2 * k + 1) by omega,
      rowW_getD_rate ⟨⟨S, hS⟩, hpl, ht⟩ (by omega)] at e2
    rw [show 6 + 2 * k = 5 + (2 * k + 1) by omega]
    split
    · rename_i hkl
      refine ⟨ht _ (List.getElem_mem _), ?_⟩
      show (_, _) = _
      rw [e1, e2, Keccak.rateCell_scalar _ k hkl, ht _ (List.getElem_mem _)]
    · rename_i hkl
      rw [e1, e2, Keccak.rateCell_past _ (by omega), Keccak.rateCell_past _ (by omega)]
      exact ⟨rfl, rfl⟩

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- A load (not a store) of a word in memory, evaluated, holds and reads it. -/
theorem load_of_good {d p : V} {o : ℕ} {v : E} (hS : Atom.load d p o ∉ S)
    (hg : Good rd S w σ (.load d p o)) (h : LoadHolds rd (σ p) o v) :
    σ d = v ∧ (Atom.load d p o).Holds rd σ := by
  have e : σ d = v := by rw [good_load_val hS hg, rdAt_of_load h]
  refine ⟨e, ?_⟩
  show LoadHolds rd (σ p) o (σ d)
  rw [e]; exact h

end
end LeanVM.Guest.Complete.Agg
