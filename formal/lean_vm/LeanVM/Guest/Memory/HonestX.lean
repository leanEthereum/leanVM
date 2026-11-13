/-
  LeanVM.Guest.Memory.HonestX

  The honest memory with more writes: the frames and the paths' equations, then a list `X` (the
  words the hints write to the heap, which no load reads), consistent with them. Every read the
  honest memory's consumers make is one of its writes, so they read the same from the extension
  (`Covers`).
-/

module

public import LeanVM.Guest.Memory

/-!
# The honest memory, extended

The executor writes every heap word a hint writes, read later or not, where the honest memory
(`honest`: frames and the paths' equations) holds `0` at a word nothing loads. Its completeness
needs a reference holding those words too: `honestX … X` is the image of the honest writes
(`honestWrites`) followed by `X`, `HonestX` adds to `Honest` that `X` names words of the memory,
is consistent, and agrees with the honest writes where they meet.

`Covers L`: every honest write at a word of the memory reads back from `L`. Both `honest`
(`Honest.covers`) and `honestX` (`HonestX.covers`) cover; on a covering memory every frame cell,
header and certificate cell reads back (`Covers.read_cell`, `read_hdr`, `read_C`), and the
evaluation is valid (`Covers.valid`), which are the only facts of the honest memory B2's
completeness reads.

`xcross_of_reader`: writes read off a reader the tree is valid on agree with the equations; with
their words outside every frame they agree with the honest writes.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (H : Inst → ℕ → E × E) (C : Inst → List (ℕ × E))
  (hdr : E × E) (T : Tree)

/-- The honest memory's writes: the frames, then the paths' equations. -/
noncomputable def honestWrites : List Write := frameWrites C (honestInsts P fs H hdr T) ++ T.eqns P

/-- **The honest memory extended by the writes `X`.** -/
noncomputable def honestX (X : List Write) : MemoryImage (logMem (T.total fs)) :=
  image (logMem (T.total fs)) (honestWrites P fs H C hdr T ++ X)

theorem honestX_nil : honestX P fs H C hdr T [] = honest P fs H C hdr T := by
  unfold honestX honest honestWrites
  rw [List.append_nil]

/-- What the extension needs beyond `Honest`: `X` names words of the memory, is consistent, and
agrees with the honest writes. -/
structure HonestX (rd : Reader) (args rets : List E) (X : List Write) : Prop
    extends Honest P fs H C hdr T rd args rets where
  /-- `X`'s addresses are words of the memory. -/
  xaddr : ∀ q ∈ X, ∃ i : Fin (2 ^ logMem (T.total fs)), q.1 = addressOfIndex i
  /-- `X` is write-once consistent. -/
  xcons : Consistent X
  /-- `X` agrees with the honest writes. -/
  xcross : ∀ a ∈ honestWrites P fs H C hdr T, ∀ b ∈ X, a.1 = b.1 → a.2 = b.2

/-- **A memory covering the honest writes**: each, at a word of the memory, reads back. -/
def Covers {κ : ℕ} (L : MemoryImage κ) : Prop :=
  ∀ q ∈ honestWrites P fs H C hdr T, (∃ i : Fin (2 ^ logMem (T.total fs)), q.1 = addressOfIndex i) →
    L.read q.1 = some q.2

variable {P fs H C hdr T} {rd : Reader} {args rets : List E} {X : List Write}

theorem Honest.consistentW (h : Honest P fs H C hdr T rd args rets) :
    Consistent (honestWrites P fs H C hdr T) :=
  h.consistent

/-- **The honest memory covers itself.** -/
theorem Honest.covers (h : Honest P fs H C hdr T rd args rets) : Covers P fs H C hdr T (honest P fs H C hdr T) :=
  fun _ hq ha => image_read h.lt_64 h.consistent hq ha

theorem HonestX.consistent (h : HonestX P fs H C hdr T rd args rets X) :
    Consistent (honestWrites P fs H C hdr T ++ X) :=
  h.toHonest.consistentW.append h.xcons h.xcross

/-- **The extension covers the honest writes.** -/
theorem HonestX.covers (h : HonestX P fs H C hdr T rd args rets X) :
    Covers P fs H C hdr T (honestX P fs H C hdr T X) :=
  fun _ hq ha => image_read h.lt_64 h.consistent (List.mem_append_left _ hq) ha

/-- **The extension's own words read back.** -/
theorem HonestX.read_X (h : HonestX P fs H C hdr T rd args rets X) {q : Write} (hq : q ∈ X) :
    (honestX P fs H C hdr T X).read q.1 = some q.2 :=
  image_read h.lt_64 h.consistent (List.mem_append_right _ hq) (h.xaddr q hq)

/-- On a covering memory, every frame cell reads back at `fp · g^o`. -/
theorem Covers.read_cell (h : Honest P fs H C hdr T rd args rets) {κ : ℕ} {L : MemoryImage κ}
    (hL : Covers P fs H C hdr T L) {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {q : ℕ × E}
    (hq : q ∈ I.cells C) : L.read (addressOfIndex I.fp * addressOfIndex q.1) = some q.2 := by
  have hlt := h.cells.cell_lt hI hq
  have hw := honest_within hI (by omega)
  have hle := le_two_pow_logMem (T.total fs)
  rw [← pow_add]
  exact hL (addressOfIndex (I.fp + q.1), q.2)
    (List.mem_append_left _ (List.mem_flatMap.mpr ⟨I, hI, List.mem_map.mpr ⟨q, hq, rfl⟩⟩))
    ⟨⟨I.fp + q.1, by omega⟩, rfl⟩

/-- On a covering memory, the header reads back. -/
theorem Covers.read_hdr (h : Honest P fs H C hdr T rd args rets) {κ : ℕ} {L : MemoryImage κ}
    (hL : Covers P fs H C hdr T L) {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) :
    L.read (addressOfIndex I.fp * addressOfIndex 0) = some I.hdr.1 ∧
      L.read (addressOfIndex I.fp * addressOfIndex 1) = some I.hdr.2 :=
  ⟨hL.read_cell h hI (q := (0, I.hdr.1)) List.mem_cons_self,
    hL.read_cell h hI (q := (1, I.hdr.2)) (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- On a covering memory, a cell of `C` reads back. -/
theorem Covers.read_C (h : Honest P fs H C hdr T rd args rets) {κ : ℕ} {L : MemoryImage κ}
    (hL : Covers P fs H C hdr T L) {I : Inst} (hI : I ∈ honestInsts P fs H hdr T) {o : ℕ} {w : E}
    (hq : (o, w) ∈ C I) : L.read (addressOfIndex I.fp * addressOfIndex o) = some w :=
  hL.read_cell h hI (q := (o, w)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))

/-- On a covering memory, every equation reads back. -/
theorem Covers.read_eqn (h : Honest P fs H C hdr T rd args rets) {κ : ℕ} {L : MemoryImage κ}
    (hL : Covers P fs H C hdr T L) {q : Write} (hq : q ∈ T.eqns P) : L.read q.1 = some q.2 :=
  hL q (List.mem_append_right _ hq) (h.addr q hq)

/-- **The evaluation is valid on a covering memory.** -/
theorem Covers.valid (h : Honest P fs H C hdr T rd args rets) {κ : ℕ} {L : MemoryImage κ}
    (hL : Covers P fs H C hdr T L) : T.Valid P L.read args rets :=
  h.valid.transfer T fun _ hq => hL.read_eqn h hq

/-- **The public boundary of the extension**: `main`'s header in words `0`, `1`. -/
theorem HonestX.publicBoundary {input : PublicInput} {prog : Semantics.LeanIsaProgram}
    (h : HonestX P fs H C (input.word0, input.word1) T rd args rets X) :
    HoldsPublicInput input
      (⟨logMem (T.total fs), honestX P fs H C (input.word0, input.word1) T X, 0⟩ : Execution prog) := by
  obtain ⟨I, hI, -, hfp, hh⟩ := root_inst (P := P) (fs := fs) (H := H)
    (hdr := (input.word0, input.word1)) (T := T)
  obtain ⟨h0, h1⟩ := h.covers.read_hdr h.toHonest hI
  rw [hfp, hh, addressOfIndex, pow_zero, one_mul] at h0 h1
  exact ⟨minLogMem_le_logMem _, h.logMem_le, h0, h1⟩

/-! ## Writes read off a reader -/

/-- The words of a reader at the addresses `A`. -/
def readerWrites (rd : Reader) (A : List K) : List Write := A.map fun a => (a, (rd a).getD 0)

/-- **Writes read off a reader are consistent with the equations** of a tree valid on it, and with
the frames where they miss every frame word. -/
theorem xcross_of_reader {κ : ℕ} (hκ : κ < 64) {M : MemoryImage κ} (hv : T.Valid P M.read args rets)
    (ha : ∀ q ∈ T.eqns P, ∃ i : Fin (2 ^ κ), q.1 = addressOfIndex i) {A : List K}
    (hA : ∀ a ∈ A, (M.read a).isSome)
    (hfr : ∀ a ∈ frameWrites C (honestInsts P fs H hdr T), ∀ b ∈ A, a.1 ≠ b) :
    ∀ a ∈ honestWrites P fs H C hdr T, ∀ b ∈ readerWrites M.read A, a.1 = b.1 → a.2 = b.2 := by
  intro a ha' b hb hab
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  rcases List.mem_append.mp ha' with hf | he
  · exact absurd hab (hfr a hf c hc)
  · have h1 := Tree.Valid.eqns_read hκ T hv a he (ha a he)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hA c hc)
    simp only at hab ⊢
    rw [hab] at h1
    rw [hw] at h1 ⊢
    exact (Option.some.inj h1).symm

theorem readerWrites_consistent (rd : Reader) (A : List K) : Consistent (readerWrites rd A) := by
  intro a ha b hb hab
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp hb
  simp only at hab ⊢
  rw [hab]

end
end LeanVM.Guest.Memory
