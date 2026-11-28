/-
  LeanVM.Guest.B1.VsC.RunBufs

  A run window's hypotheses from the buffers its loads read: the uniform part, by the kernel.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh6

/-!
# Runs read through known buffers

A long run of `verify_sub`'s body reads and writes a few buffers through a few pointer values. `bufsOk sp sts S as`
(the kernel's check, written per run by `scripts/vs-windows`) says: no heap hint and no allocation, every load
through a pointer `.n v` with `(v, n) ∈ sp` at an offset below `n`, every store (a load in `S`) among `sts`.
`runHyp_bufs` then gives the run's `RunHyp` from, per buffer, its pointer's value `ptrAt (bs v)`, its words `xs v`
held on the evaluation memory and on every memory with the window's words, its cells in the region; per store, its
word on the evaluation memory; per asking atom (`pureAsks`), its side condition. The fresh loads need nothing more.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

/-- An atom allocating nothing. -/
def noAllocB : Atom → Bool
  | .hint (.alloc ..) => false
  | .hint (.allocDyn ..) => false
  | _ => true

/-- A load's pointer is `.n v` with `(v, n) ∈ sp`, its offset below `n`. -/
def loadFits (sp : List (ℕ × ℕ)) : Atom → Bool
  | .load _ p off => sp.any fun q => decide (p = .n q.1) && decide (off < q.2)
  | _ => true

/-- A heap hint's words lie in `(v, n) ∈ sp`'s first `n`. -/
def heapFits (sp : List (ℕ × ℕ)) (a : Atom) : Bool :=
  match atomHeapDest? a with
  | none => true
  | some (p, off, len) => sp.any fun q => decide (p = .n q.1) && decide (off + len ≤ q.2)

/-- **A run read through known buffers**: no allocation, each load and heap hint through `sp`, each store (a load in
`S`) among `sts`. -/
def bufsOk (sp : List (ℕ × ℕ)) (sts S as : List Atom) : Bool :=
  as.all fun a => heapFits sp a && noAllocB a && loadFits sp a &&
    (!(memAsks a && S.contains a) || sts.contains a)

theorem noAlloc_fields {σ : Val} : ∀ {as : List Atom}, as.all noAllocB = true →
    allocDsts (as.map Ev.atom) = [] ∧ allocs σ (as.map Ev.atom) = []
  | [], _ => ⟨rfl, rfl⟩
  | a :: as, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨i1, i2⟩ := noAlloc_fields (σ := σ) h.2
    have e : Ev.allocDst? (.atom a) = none ∧ Ev.alloc? σ (.atom a) = none := by
      have h1 := h.1
      cases a with
      | hint hh =>
        cases hh with
        | alloc d n => simp [noAllocB] at h1
        | allocDyn d n => simp [noAllocB] at h1
        | _ => exact ⟨rfl, rfl⟩
      | _ => exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [allocDsts, List.map_cons, List.filterMap_cons, e.1] at i1 ⊢; exact i1
    · simp only [allocs, List.map_cons, List.filterMap_cons, e.2] at i2 ⊢; exact i2

theorem loadFits_load {sp : List (ℕ × ℕ)} {d p : V} {off : ℕ} (h : loadFits sp (.load d p off) = true) :
    ∃ q ∈ sp, p = .n q.1 ∧ off < q.2 := by
  simp only [loadFits, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- A heap hint's address. -/
theorem mem_hintAddrs {σ : Val} {x : Atom} {A : K} (h : A ∈ Ev.hintAddrs σ (.atom x)) :
    ∃ p off len, atomHeapDest? x = some (p, off, len) ∧ ∃ j < len, A = (σ p).limb 0 * addressOfIndex (off + j) := by
  cases x with
  | hint hh =>
    cases hd : (hintDest? hh).bind destHeap? with
    | none => simp [Ev.hintAddrs, hd] at h
    | some t =>
      obtain ⟨p, off, len⟩ := t
      simp only [Ev.hintAddrs, hd, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact ⟨p, off, len, hd, j, hj, rfl⟩
  | _ => simp [Ev.hintAddrs] at h

/-- The word a load through a held buffer reads, on the evaluation memory. -/
theorem word_of_reads {rd : Reader} {b off : ℕ} {xs : List E} {v : E} (h : LoadHolds rd (ptrAt b) off v)
    (h0 : ReadsAt rd (ptrAt b) xs) (hoff : off < xs.length) : v = xs[off] := by
  have := (h0 off hoff).2
  rw [h.2] at this
  exact Option.some.inj this

/-- A held word by its index. -/
theorem loadHolds_of_get? {rd : Reader} {b i : ℕ} {xs : List E} {v : E} (h : ReadsAt rd (ptrAt b) xs)
    (hi : xs[i]? = some v) : LoadHolds rd (ptrAt b) i v := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact h i hlt

/-- A fresh load's word, by its index. -/
theorem good_load_get? {rd0 : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {d p : V} {off b : ℕ} {xs : List E}
    {v : E} (hS : Atom.load d p off ∉ S) (hg : Good rd0 S w σ0 (.load d p off)) (hpb : σ0 p = ptrAt b)
    (h0 : ReadsAt rd0 (ptrAt b) xs) (hi : xs[off]? = some v) : σ0 d = v := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact good_loadAt hS hg hpb hlt h0

/-- No `frameAddr` or `touch`. -/
def noFTB : Atom → Bool
  | .frameAddr .. => false
  | .touch .. => false
  | _ => true

section
variable {k : ℕ} {rd0 : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {a : ℕ} {Own R D : ℕ → Prop}
  {Pre O : Reader → Prop} {as : List Atom} {sp : List (ℕ × ℕ)} {sts : List Atom}

/-- **A run's hypotheses from the buffers it reads**: each buffer `(v, n) ∈ sp` at `ptrAt (bs v)`, its words `xs v`
(at least `n`) held on the evaluation memory and on every memory with `Pre` and `O`, its first `n` cells in `Own`,
`R` or `D`; each store's word on the evaluation memory; each asking atom's side condition. -/
theorem runHyp_bufs (hok : bufsOk sp sts S as = true) (hg : ∀ x ∈ as, Good rd0 S w σ0 x) (bs : ℕ → ℕ)
    (xs : ℕ → List E) (hp : ∀ q ∈ sp, σ0 (.n q.1) = ptrAt (bs q.1)) (hn : ∀ q ∈ sp, q.2 ≤ (xs q.1).length)
    (h0 : ∀ q ∈ sp, ReadsAt rd0 (ptrAt (bs q.1)) (xs q.1))
    (hc : ∀ q ∈ sp, ∀ j < q.2, Own (bs q.1 + j) ∨ R (bs q.1 + j) ∨ D (bs q.1 + j))
    (hO : ∀ rd, Pre rd → O rd → ∀ q ∈ sp, ReadsAt rd (ptrAt (bs q.1)) (xs q.1))
    (hst : ∀ x ∈ sts, MemF rd0 σ0 x) (hpure : ∀ x ∈ as.filter pureAsks, PureF k σ0 x) :
    RunHyp k σ0 w a Own R D Pre O as := by
  have hx : ∀ x ∈ as, heapFits sp x = true ∧ noAllocB x = true ∧ loadFits sp x = true ∧
      (!(memAsks x && S.contains x) || sts.contains x) = true := fun x hm => by
    have := List.all_eq_true.mp hok x hm
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  obtain ⟨i1, i2⟩ := noAlloc_fields (σ := σ0) (as := as) (List.all_eq_true.mpr fun x hm => (hx x hm).2.1)
  -- each load's pointer, offset and word
  have hl : ∀ d p off, Atom.load d p off ∈ as → ∃ q ∈ sp, ∃ hlen : off < (xs q.1).length,
      σ0 p = ptrAt (bs q.1) ∧ (Own (bs q.1 + off) ∨ R (bs q.1 + off) ∨ D (bs q.1 + off)) ∧
        σ0 d = (xs q.1)[off] := by
    intro d p off hm
    obtain ⟨q, hq, rfl, hoff⟩ := loadFits_load (hx _ hm).2.2.1
    have hlen : off < (xs q.1).length := lt_of_lt_of_le hoff (hn q hq)
    refine ⟨q, hq, hlen, hp q hq, hc q hq off hoff, ?_⟩
    by_cases hS : Atom.load d (.n q.1) off ∈ S
    · have hs : Atom.load d (.n q.1) off ∈ sts := by
        have := (hx _ hm).2.2.2
        rw [show memAsks (Atom.load d (.n q.1) off) = true from rfl, List.contains_iff_mem.mpr hS] at this
        simpa using this
      have h1 : LoadHolds rd0 (σ0 (.n q.1)) off (σ0 d) := hst _ hs
      rw [hp q hq] at h1
      exact word_of_reads h1 (h0 q hq) hlen
    · exact good_loadAt hS (hg _ hm) (hp q hq) hlen (h0 q hq)
  refine RunHyp.of_asks ?_ ?_ ?_ hpure ?_
  · rw [i1, i2]; rfl
  · intro A hA
    obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA
    obtain ⟨q, -, -, hpq, hcl, -⟩ := hl d p off hm
    exact ⟨bs q.1 + off, by rw [hpq, ptrAt, B1.Main.addr_ofK], hcl⟩
  · intro A hA
    simp only [heapHintAddrs, List.mem_flatMap, List.mem_map] at hA
    obtain ⟨_, ⟨x, hm, rfl⟩, hA⟩ := hA
    obtain ⟨p, off, len, hd, j, hj, rfl⟩ := mem_hintAddrs hA
    have hf := (hx x hm).1
    simp only [heapFits, hd, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨q, hq, rfl, hle⟩ := hf
    exact ⟨bs q.1 + (off + j), by rw [hp q hq, ptrAt, B1.Main.addr_ofK], hc q hq _ (by omega)⟩
  · intro rd _ hpr ho x hm
    obtain ⟨hm, hma⟩ := List.mem_filter.mp hm
    cases x with
    | load d p off =>
      obtain ⟨q, hq, hlen, hpq, -, hd⟩ := hl d p off hm
      show LoadHolds rd (σ0 p) off (σ0 d)
      rw [hpq, hd]
      exact hO rd hpr ho q hq off hlen
    | _ => simp [memAsks] at hma

/-- **An atom of such a run holds on the evaluation memory** when it is not a store and asks nothing. -/
theorem holds_bufs {x : Atom} (hok : bufsOk sp sts S as = true) (hg : ∀ x ∈ as, Good rd0 S w σ0 x) (bs : ℕ → ℕ)
    (xs : ℕ → List E) (hp : ∀ q ∈ sp, σ0 (.n q.1) = ptrAt (bs q.1)) (hn : ∀ q ∈ sp, q.2 ≤ (xs q.1).length)
    (h0 : ∀ q ∈ sp, ReadsAt rd0 (ptrAt (bs q.1)) (xs q.1)) (hx : x ∈ as) (hS : x ∉ S)
    (hpa : pureAsks x = false) (hft : noFTB x = true) : x.Holds rd0 σ0 := by
  have hgx := hg x hx
  cases x with
  | load d p off =>
    have hf : loadFits sp (.load d p off) = true := by
      have := List.all_eq_true.mp hok _ hx
      simp only [Bool.and_eq_true] at this
      exact this.1.2
    obtain ⟨q, hq, rfl, hoff⟩ := loadFits_load hf
    have hlen := lt_of_lt_of_le hoff (hn q hq)
    have h := h0 q hq off hlen
    rw [← hp q hq] at h
    exact holds_of_good hgx (by simp only [Side, hS, ↓reduceIte]; exact ⟨h.1, by rw [h.2]; rfl⟩)
  | mul d a b =>
    have : a.idx < d.idx ∧ b.idx < d.idx := by simpa [pureAsks] using hpa
    exact holds_of_good hgx (by simp only [Side, this, and_self, ↓reduceIte])
  | frameAddr _ _ => simp [noFTB] at hft
  | touch _ _ => simp [noFTB] at hft
  | assertEq _ _ => simp [pureAsks] at hpa
  | assertInK _ _ => simp [pureAsks] at hpa
  | assertNe _ _ _ => simp [pureAsks] at hpa
  | rangeCheck _ _ _ _ _ => simp [pureAsks] at hpa
  | _ => exact holds_of_good hgx (by simp [Side])

/-- **A run window read through known buffers**, its state unchanged (it allocates nothing). -/
theorem winsHyp_run_bufs {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {ws : List W0} {st : St}
    {K : St → Prop} (hok : bufsOk sp sts S as = true) (hg : ∀ x ∈ as, Good rd0 S w σ0 x) (bs : ℕ → ℕ)
    (xs : ℕ → List E) (hp : ∀ q ∈ sp, σ0 (.n q.1) = ptrAt (bs q.1)) (hn : ∀ q ∈ sp, q.2 ≤ (xs q.1).length)
    (h0 : ∀ q ∈ sp, ReadsAt rd0 (ptrAt (bs q.1)) (xs q.1))
    (hc : ∀ q ∈ sp, ∀ j < q.2, Own (bs q.1 + j) ∨ R (bs q.1 + j) ∨ st.D (bs q.1 + j))
    (hO : ∀ rd, Pre rd → st.O rd → ∀ q ∈ sp, ReadsAt rd (ptrAt (bs q.1)) (xs q.1))
    (hst : ∀ x ∈ sts, MemF rd0 σ0 x) (hpure : ∀ x ∈ as.filter pureAsks, PureF k σ0 x)
    (hrest : WinsHyp fs al cert k σ0 w Own R Pre ws st K) :
    WinsHyp fs al cert k σ0 w Own R Pre (.run as :: ws) st K := by
  rw [WinsHyp]
  refine ⟨runHyp_bufs hok hg bs xs hp hn h0 hc hO hst hpure, ?_⟩
  rw [(noAlloc_fields (σ := σ0) (as := as) (List.all_eq_true.mpr fun x hm => by
    have := List.all_eq_true.mp hok x hm
    simp only [Bool.and_eq_true] at this
    exact this.1.1.2)).2, List.sum_nil, Nat.add_zero]
  exact hrest

end

end
end LeanVM.Guest.B1.VsC
