module

public import NativeRustcVm.Layout.Values
public import NativeRustcVm.MemLemmas

/-!
# The forms of `data.rs` in memory

`FORMS` and `TERMS` (`Data.forms`, `Data.terms`) lay the data's forms (`Data.allForms`) end to
end: form `i`'s span starts after the terms of the forms before it and is as long as its terms
(`forms_getElem`), and the terms there are its own (`terms_window`). Every monomial has at most two
columns, each a global column (`allForms_terms`). So where `TERMS`' bytes are in memory, form `i`'s
terms represent `formAt i` (`termsAt_formAt`).
-/

namespace NativeRustcVm.Layout

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier NativeRustcVm.Data
open NativeRustcVm.Transcript (off)

public section

/-! ## Spans -/

theorem length_spansFrom (s : Nat) (ls : List Nat) : (spansFrom s ls).length = ls.length := by
  induction ls generalizing s with
  | nil => rfl
  | cons n ns ih => simp [spansFrom, ih]

theorem spansFrom_getElem (s : Nat) (ls : List Nat) (i : Nat) (hi : i < ls.length) :
    (spansFrom s ls)[i]'(by rw [length_spansFrom]; exact hi) = ⟨s + (ls.take i).sum, ls[i]⟩ := by
  induction ls generalizing s i with
  | nil => cases hi
  | cons n ns ih =>
    cases i with
    | zero => simp [spansFrom]
    | succ i =>
      simp only [spansFrom, List.getElem_cons_succ, List.take_succ_cons, List.sum_cons]
      rw [ih (s + n) i (by simpa using hi)]
      congr 1
      omega

/-- The window of a flattened list where its `i`th list lies. -/
theorem flatten_window {α : Type} (L : List (List α)) (i : Nat) (hi : i < L.length) :
    ((L.flatten.drop ((L.take i).map List.length).sum).take L[i].length) = L[i] := by
  induction L generalizing i with
  | nil => cases hi
  | cons l L ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.flatten_cons, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.getElem_cons_succ]
      rw [← List.drop_drop, List.drop_left]
      exact ih i (by simpa using hi)

/-! ## `FORMS` and `TERMS` -/

theorem terms_eq : Data.terms = (Data.allForms.map fun f ↦ f.terms.map Term.ofMono).flatten := by
  simp [Data.terms, List.flatMap_def]

theorem length_forms : Data.forms.length = Data.allForms.length := by
  simp [Data.forms, length_spansFrom]

/-- Form `i`'s span. -/
theorem forms_getElem (i : Nat) (hi : i < Data.allForms.length) :
    Data.forms[i]'(by rw [length_forms]; exact hi) =
      ⟨((Data.allForms.take i).map fun f ↦ f.terms.length).sum, Data.allForms[i].terms.length⟩ := by
  simp only [Data.forms]
  rw [spansFrom_getElem _ _ i (by simpa using hi)]
  simp [List.map_take]

/-- Form `i`'s terms, in `TERMS`. -/
theorem terms_window (i : Nat) (hi : i < Data.allForms.length) :
    ((Data.terms.drop ((Data.allForms.take i).map fun f ↦ f.terms.length).sum).take
      Data.allForms[i].terms.length) = Data.allForms[i].terms.map Term.ofMono := by
  have h := flatten_window (Data.allForms.map fun f ↦ f.terms.map Term.ofMono) i (by simpa using hi)
  simp only [List.getElem_map, List.length_map, List.map_take, List.map_map] at h
  rw [terms_eq]
  simpa [Function.comp_def, List.map_take] using h

/-! ## The data's sizes -/

set_option Elab.async false in
theorem allForms_length : Data.allForms.length = 593 := by decide +kernel

set_option Elab.async false in
theorem terms_length : Data.terms.length = 769 := by decide +kernel

set_option Elab.async false in
/-- Every monomial of the data has at most two columns, each below `158`. -/
theorem allForms_terms : ∀ f ∈ Data.allForms, ∀ t ∈ f.terms, t.1.length ≤ 2 ∧ ∀ c ∈ t.1, c < 158 := by
  decide +kernel

/-- Form `i`'s start in `TERMS`. -/
abbrev formStart (i : Nat) : Nat := ((Data.allForms.take i).map fun f ↦ f.terms.length).sum

/-- Form `i`'s span lies in `TERMS`. -/
theorem formStart_add_le (i : Nat) (hi : i < Data.allForms.length) :
    formStart i + Data.allForms[i].terms.length ≤ Data.terms.length := by
  have hlen : Data.terms.length = (Data.allForms.map fun f ↦ f.terms.length).sum := by
    rw [terms_eq, List.length_flatten, List.map_map]
    simp [Function.comp_def]
  rw [hlen, ← List.sum_take_add_sum_drop (Data.allForms.map fun f ↦ f.terms.length) i,
    List.drop_eq_getElem_cons (by simpa using hi), List.sum_cons]
  simp [formStart, List.map_take]

/-- `FORMS`' bytes: `593` spans of `16` bytes. -/
theorem length_forms_bytes : (Data.forms.flatMap Span.bytes).length = 9488 := by
  rw [length_flatMap_const (k := 16) (fun s ↦ by simp [Span.bytes, natBytes, length_wordBytes]),
    length_forms, allForms_length]

/-- Form `i`'s span in `FORMS`' bytes: its start, then its length. -/
theorem forms_words {d : Mem 64} {a : BitVec 64} (h : BytesAt d a (Data.forms.flatMap Span.bytes))
    (i : Nat) (hi : i < Data.allForms.length) :
    WordAt d (a + BitVec.ofNat 64 (16 * i)) (formStart i).toUInt64 ∧
      WordAt d (a + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8)
        Data.allForms[i].terms.length.toUInt64 := by
  have hb := h.flatMap_getElem (k := 16) (fun s ↦ by simp [Span.bytes, natBytes, length_wordBytes])
    (i := i) (by rw [length_forms]; exact hi)
  rw [forms_getElem i hi] at hb
  simp only [Span.bytes, natBytes] at hb
  exact ⟨by simpa [WordAt, formStart, List.map_take] using hb.left,
    by simpa [WordAt, length_wordBytes] using hb.right⟩

/-! ## The terms in memory -/

theorem length_term_bytes (t : Term) : t.bytes.length = termBytes := by
  simp [Term.bytes, natBytes, length_wordBytes, length_ewBytes, termBytes]

/-- A term's bytes represent the model's term of its monomial. -/
theorem termWAt_ofMono {d : Mem 64} {a : BitVec 64} {mc : List Nat × E}
    (h : BytesAt d a (Term.ofMono mc).bytes) (hlen : mc.1.length ≤ 2)
    (hcols : ∀ c ∈ mc.1, c < 158) :
    TermWAt d a ⟨mc.1.toArray, EW.ofE mc.2⟩ := by
  obtain ⟨m, c⟩ := mc
  dsimp only at hlen hcols ⊢
  simp only [Term.bytes, Term.ofMono, natBytes, List.append_assoc] at h
  have h0 := h.left
  have h1 := h.right.left
  have h2 := h.right.right.left
  have h3 := h.right.right.right
  simp only [length_wordBytes, NativeRustcVm.addr_add_add] at h1 h2 h3
  refine ⟨by simpa using hlen, by simpa [NativeRustcVm.WordAt] using h0, fun i hi ↦ ?_,
    fun i hi ↦ ?_, h3⟩
  · simp only [List.size_toArray] at hi
    have := hcols _ (List.getElem_mem hi)
    simp only [List.getElem_toArray]
    omega
  · simp only [List.size_toArray] at hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · simpa [NativeRustcVm.WordAt, off, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        using h1
    · simpa [NativeRustcVm.WordAt, off, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        using h2

/-- **Form `i`'s terms in memory**: where `TERMS`' bytes are at `a`, the span of form `i` holds
`formAt i`. -/
theorem termsAt_formAt {d : Mem 64} {a : BitVec 64} (h : BytesAt d a (Data.terms.flatMap Term.bytes))
    (i : Nat) (hi : i < Data.allForms.length) :
    TermsAt d (off a (termBytes * ((Data.allForms.take i).map fun f ↦ f.terms.length).sum))
      (formAt i) := by
  intro j hj
  have hf : formAt i = FormW.ofForm Data.allForms[i] := by
    simp [formAt, List.getElem?_eq_getElem hi]
  have hj' : j < Data.allForms[i].terms.length := by
    simpa [hf, FormW.ofForm] using hj
  set s := ((Data.allForms.take i).map fun f ↦ f.terms.length).sum
  have hw := terms_window i hi
  have hlt : s + j < Data.terms.length := by
    have := congrArg List.length hw
    simp only [List.length_take, List.length_drop, List.length_map] at this
    omega
  have hb := h.flatMap_getElem length_term_bytes hlt
  have ht : Data.terms[s + j] = Term.ofMono Data.allForms[i].terms[j] := by
    have := congrArg (fun l ↦ l[j]?) hw
    simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_map, hj', ite_true,
      List.getElem?_eq_getElem hj', Option.map_some] at this
    rw [List.getElem?_eq_getElem hlt] at this
    exact Option.some.inj this
  rw [ht] at hb
  have hmem := List.getElem_mem hj'
  obtain ⟨hl, hc⟩ := allForms_terms _ (List.getElem_mem hi) _ hmem
  have := termWAt_ofMono hb hl hc
  simp only [hf, FormW.ofForm, Array.getElem_map, List.getElem_toArray]
  rw [Nat.mul_add] at this
  simp only [off, NativeRustcVm.addr_add_add]
  exact this

end

end NativeRustcVm.Layout
