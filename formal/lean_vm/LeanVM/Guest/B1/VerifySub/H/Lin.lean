/-
  LeanVM.Guest.B1.VerifySub.H.Lin

  The words `verify_sub`'s callees read on an honest child: slices of the caller's words, of
  `verify_sub`'s own buffers, and (the terminal) of `certify_placement`'s and `open_stacked`'s
  results.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermC
public import LeanVM.Guest.AcceptableChild

/-!
# The callees' words

`SubOf L q`: `q`'s words are a slice of an entry of `L`; a memory holding `L` holds them
(`subOf_memL`), and they lie in `L`'s region (`subOf_region`). `vs_own_mem`: the own buffers at
the bump allocator's positions. `kid_lin_sub`: every callee but the terminal reads slices of the
caller's words (`Lin`, holding the exponent tables) and of the own buffers.
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

theorem subOf_memL {rd : Reader} {L : Main.Layout} (hL : Main.MemL rd L) {q : ℕ × List E} (h : SubOf L q) :
    ReadsAt rd (ofK (addressOfIndex q.1)) q.2 := by
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

/-- A slice of a list. -/
theorem subOf_slice {L : Main.Layout} {b : ℕ} {xs : List E} (hq : (b, xs) ∈ L) (off : ℕ) (ys : List E)
    (hl : off + ys.length ≤ xs.length) (hy : ys = (xs.drop off).take ys.length) :
    SubOf L (b + off, ys) :=
  ⟨(b, xs), hq, off, rfl, hl, hy⟩

theorem bases_length : ∀ (b : ℕ) (sizes : List ℕ), (bases b sizes).length = sizes.length
  | _, [] => rfl
  | b, s :: sizes => by simp [bases, bases_length (b + s) sizes]

/-- The own buffers at the bump allocator's positions. -/
theorem vs_own_mem {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (b : ℕ) {i : ℕ} (hi : i < 13) :
    ((bases b (vsSizes S.μ)).getD i 0, S.ownW.getD i []) ∈ bufL b (vsSizes S.μ) S.ownW := by
  have hl : (bases b (vsSizes S.μ)).length = 13 := by rw [bases_length]; rfl
  have ho : S.ownW.length = 13 := rfl
  rw [bufL, List.mem_iff_getElem]
  refine ⟨i, by simp [hl, ho, hi], ?_⟩
  rw [List.getElem_zip, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem seg_take (P X R : List E) (n : ℕ) (hn : n = P.length) :
    ((P ++ (X ++ R)).drop n).take X.length = X := by
  subst hn; rw [List.drop_left, List.take_left]

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem stream_eq : c.proof.stream = S.words ++ [S.x0, S.x1] ++ S.xsG ++ S.xsT ++ S.xsK ++ S.xsW := by
  rw [S.hstream, ChildSegs.words]

/-- The stream's segments, in the padded stream. -/
theorem stream_segs :
    ((vsStreamW c.proof.stream).drop 10).take S.xsG.length = S.xsG ∧
    ((vsStreamW c.proof.stream).drop (10 + S.xsG.length)).take S.xsT.length = S.xsT ∧
    ((vsStreamW c.proof.stream).drop (10 + S.xsG.length + S.xsT.length)).take S.xsK.length =
      S.xsK ∧
    ((vsStreamW c.proof.stream).drop (10 + S.xsG.length + S.xsT.length + S.xsK.length)).take
      S.xsW.length = S.xsW ∧
    10 + S.xsG.length + S.xsT.length + S.xsK.length + S.xsW.length ≤
      (vsStreamW c.proof.stream).length := by
  have hw := S.words_length
  have hz := fun (P X R : List E) (n : ℕ) (hn : n = P.length) ↦ seg_take P X R n hn
  set Z := List.replicate (Coverage.childStreamCap - c.proof.stream.length) (0 : E)
  have e : vsStreamW c.proof.stream = S.words ++ [S.x0, S.x1] ++ S.xsG ++ S.xsT ++ S.xsK ++ S.xsW ++ Z := by
    show c.proof.stream ++ Z = _
    rw [S.stream_eq]
  refine ⟨?_, ?_, ?_, ?_, by rw [e]; simp [hw]; omega⟩
  · rw [show vsStreamW c.proof.stream = (S.words ++ [S.x0, S.x1]) ++ (S.xsG ++ (S.xsT ++ S.xsK ++
      S.xsW ++ Z)) by rw [e]; simp]
    exact hz _ _ _ _ (by simp [hw])
  · rw [show vsStreamW c.proof.stream = (S.words ++ [S.x0, S.x1] ++ S.xsG) ++ (S.xsT ++ (S.xsK ++
      S.xsW ++ Z)) by rw [e]; simp]
    exact hz _ _ _ _ (by simp [hw]; omega)
  · rw [show vsStreamW c.proof.stream = (S.words ++ [S.x0, S.x1] ++ S.xsG ++ S.xsT) ++ (S.xsK ++
      (S.xsW ++ Z)) by rw [e]; simp]
    exact hz _ _ _ _ (by simp [hw]; omega)
  · rw [show vsStreamW c.proof.stream = (S.words ++ [S.x0, S.x1] ++ S.xsG ++ S.xsT ++ S.xsK) ++
      (S.xsW ++ Z) by rw [e]; simp]
    exact hz _ _ _ _ (by simp [hw]; omega)

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
