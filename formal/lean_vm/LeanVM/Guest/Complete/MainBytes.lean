/-
  LeanVM.Guest.Complete.MainBytes

  `main`'s byte-table run (`mPre`'s statements `52 ..< 621`): its hypotheses at the honest oracle.
-/

module

public import LeanVM.Guest.Complete.MainRuns

/-!
# The byte-table run

`mPre_w9`: the coverage table's and the byte table's `HeapBuf`s, the coverage table's leanSPHINCS half, the
byte table's `256` stores (`.load (.n (67 + i)) (.n 66) i` of the constant `word i 0`), the carried chain
indices `lx_tags` and a guard. `runHypT_w9`: its `RunHypT` at `main`'s honest oracle from the cursor after
the claim tables (`mBase m 2`), on memories holding `main`'s words: its `HeapBuf`s at `mBase m 2`, `mBase m 3`,
its stores in `main`'s own words (`own_main`), each the byte table's word.

Tools: `noHeapB` (no heap hint, `heapHintAddrs_noHeap`), `own_main` (every index of `main`'s buffers is its
own data), `bases_cover` (an index of `[b, b + Σ)` in one of the regions from `b`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Tools -/

/-- An atom with no heap hint. -/
def noHeapB : Atom → Bool
  | .hint h => ((hintDest? h).bind destHeap?).isNone
  | _ => true

theorem hintAddrs_noHeap {σ : Val} {a : Atom} (h : noHeapB a = true) : Ev.hintAddrs σ (.atom a) = [] := by
  cases a with
  | hint hh =>
    simp only [noHeapB, Option.isNone_iff_eq_none] at h
    simp only [Ev.hintAddrs, h]
  | _ => rfl

theorem heapHintAddrs_noHeap {σ : Val} : ∀ {as : List Atom}, as.all noHeapB = true →
    heapHintAddrs σ (as.map Ev.atom) = []
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := heapHintAddrs_noHeap (σ := σ) h.2
    simp only [heapHintAddrs, List.map_cons, List.flatMap_cons, hintAddrs_noHeap h.1, List.nil_append] at ih ⊢
    exact ih

theorem bases_cover : ∀ (b : ℕ) (L : List ℕ) (i : ℕ), b ≤ i → i < b + L.sum →
    ∃ q ∈ L.zip (bases b L), q.2 ≤ i ∧ i < q.2 + q.1
  | _, [], i, h1, h2 => by simp at h2; omega
  | b, x :: L, i, h1, h2 => by
    simp only [List.sum_cons] at h2
    by_cases hi : i < b + x
    · exact ⟨(x, b), by simp [bases], h1, by omega⟩
    · obtain ⟨q, hq, h⟩ := bases_cover (b + x) L i (by omega) (by omega)
      refine ⟨q, ?_, h⟩
      simp only [bases, List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hq

/-- **Every index of `main`'s buffers is its own data.** -/
theorem own_main {cert : String → V → ℕ} {m : MainCounts} {es : List Ev} {i : ℕ} (h1 : B2C.fs "main" ≤ i)
    (h2 : i < mTop m) : ownData cert 0 (B2C.fs "main") "main" m.bufs es i :=
  Or.inl (bases_cover _ _ i h1 h2)

theorem mBase_two (m : MainCounts) : mBase m 2 = B2C.fs "main" + 4 * m.sx + 4 * m.ss := by
  simp [mBase, MainCounts.bufs, bases]

theorem mBase_three (m : MainCounts) : mBase m 3 = B2C.fs "main" + 4 * m.sx + 4 * m.ss + (m.sx + m.ss) := by
  simp [mBase, MainCounts.bufs, bases]

theorem mBase_three_lt {m : MainCounts} {i : ℕ} (hi : i < 256) : mBase m 3 + i < mTop m := by
  rw [mBase_three]
  simp only [mTop, MainCounts.bufs, List.sum_cons, List.sum_nil]
  omega

theorem mainWords_bytes {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd : Reader}
    (h : HoldsWords rd (mainWords s w cover)) :
    ReadsAt rd (ptrAt (mBase (mainCounts s w) 3)) ((List.range 256).map fun v => word v 0) :=
  h (mBase (mainCounts s w) 3, (List.range 256).map fun v => word v 0)
    (by simp only [mainWords]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-! ## The run -/

/-- A store of byte `i` in the byte table. -/
def isByteStore : Atom → Bool
  | .load (.n d) (.n 66) i => decide (d = 67 + i) && decide (i < 256)
  | _ => false

/-- `mPre`'s byte-table run. -/
noncomputable abbrev as9 : List Atom := atomsOf ((mPre.drop 52).take 569)

set_option maxRecDepth 200000 in
theorem w9_shape : as9.all (fun a => noHeapB a && (trivPM a || isByteStore a)) = true ∧
    allocDsts (as9.map Ev.atom) = [.n 64, .n 66] ∧
    as9.filter isAllocA = [.hint (.allocDyn (.n 64) (.n 24)), .hint (.alloc (.n 66) 256)] := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem w9_consts : (List.range 256).all (fun i => decide (Atom.const (.n (67 + i)) (word i 0) ∈ atomsOf mPre)) = true ∧
    Atom.hint (.allocDyn (.n 64) (.n 24)) ∈ atomsOf mPre ∧ Atom.hint (.alloc (.n 66) 256) ∈ atomsOf mPre := by
  decide +kernel

theorem allocs_atoms (σ : Val) (as : List Atom) :
    allocs σ (as.map Ev.atom) = (as.filter isAllocA).filterMap fun a => Ev.alloc? σ (.atom a) := by
  rw [← filterMap_alloc]
  simp only [allocs, List.filterMap_map]
  rfl

theorem loadAddr_mem {σ : Val} {as : List Atom} {A : K} (h : A ∈ loadAddrs σ (as.map Ev.atom)) :
    ∃ x ∈ as, Ev.loadAddr? σ (.atom x) = some A := by
  simp only [loadAddrs, List.mem_filterMap, List.mem_map] at h
  obtain ⟨_, ⟨x, hx, rfl⟩, h⟩ := h
  exact ⟨x, hx, h⟩

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {rd0 : Reader}

theorem w9_ptr : mVal rd0 (mOrc al s w) (.n 66) = ptrAt (mBase (mainCounts s w) 3) := by
  have h : mVal rd0 (mOrc al s w) (.n 66) = mOrc al s w 66 := mPre_good (rd := rd0) (w := mOrc al s w) w9_consts.2.2
  rw [h]
  exact congrArg ptrAt (Nat.add_zero _)

theorem w9_byte {i : ℕ} (hi : i < 256) : mVal rd0 (mOrc al s w) (.n (67 + i)) = word i 0 := by
  have := List.all_eq_true.mp w9_consts.1 i (List.mem_range.mpr hi)
  simp only [decide_eq_true_eq] at this
  exact mPre_good this

/-- **The byte-table run's hypotheses** at `main`'s honest oracle. -/
theorem runHypT_w9 {k : ℕ} {cover : List E} {R D : ℕ → Prop} {Pre O : Reader → Prop} {es : List Ev}
    (hb : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19) (hO : ∀ rd, O rd → HoldsWords rd (mainWords s w cover)) :
    RunHypT k (mVal rd0 (mOrc al s w)) (mOrc al s w) (mBase (mainCounts s w) 2)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R D Pre O as9 := by
  obtain ⟨hall, hdst, hfil⟩ := w9_shape
  have hm64 := mPre_good (rd := rd0) (w := mOrc al s w) w9_consts.2.1
  obtain ⟨-, -, v24, -⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := rd0)
  have hq : ∀ x ∈ as9, noHeapB x = true ∧ (trivPM x = true ∨ isByteStore x = true) := fun x hx => by
    have := List.all_eq_true.mp hall x hx
    simpa only [Bool.and_eq_true, Bool.or_eq_true] using this
  have hstore : ∀ x, isByteStore x = true → ∃ i, i < 256 ∧ x = .load (.n (67 + i)) (.n 66) i := by
    intro x hx
    match x, hx with
    | .load (.n d) (.n 66) i, hx =>
      simp only [isByteStore, Bool.and_eq_true, decide_eq_true_eq] at hx
      exact ⟨i, hx.2, by rw [hx.1]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdst, allocs_atoms, hfil]
    have l : logG (gen ^ ((mainCounts s w).sx + (mainCounts s w).ss)) = (mainCounts s w).sx + (mainCounts s w).ss :=
      logG_gen_pow (by omega)
    have o64 : mOrc al s w 64 = mPtr (mainCounts s w) 2 0 := rfl
    have o66 : mOrc al s w 66 = mPtr (mainCounts s w) 3 0 := rfl
    simp only [List.filterMap_cons, List.filterMap_nil, Ev.alloc?, v24, l, bases, List.map_cons, List.map_nil,
      o64, o66, mPtr, Nat.add_zero, mBase_three, mBase_two]
  · intro A hA
    obtain ⟨x, hx, hl⟩ := loadAddr_mem hA
    rcases (hq x hx).2 with ht | ht
    · exfalso
      cases x with
      | load d p off => simp [trivPM] at ht
      | _ => simp [Ev.loadAddr?] at hl
    · obtain ⟨i, hi, rfl⟩ := hstore x ht
      simp only [Ev.loadAddr?, Option.some.injEq, w9_ptr] at hl
      rw [Main.addr_ofK] at hl
      exact ⟨_, hl.symm, Or.inl (own_main (by rw [mBase_three]; omega) (mBase_three_lt hi))⟩
  · rw [heapHintAddrs_noHeap (List.all_eq_true.mpr fun x hx => (hq x hx).1)]
    intro A hA; simp at hA
  · intro x hx
    rcases (hq x hx).2 with ht | ht
    · exact pureT_triv ht
    · obtain ⟨i, hi, rfl⟩ := hstore x ht
      trivial
  · intro rd _ _ hOr x hx
    rcases (hq x hx).2 with ht | ht
    · exact memT_triv ht
    · obtain ⟨i, hi, rfl⟩ := hstore x ht
      show LoadHolds rd _ i _
      rw [w9_ptr, w9_byte hi]
      have := mainWords_bytes (hO rd hOr) i (by simp [hi])
      simpa using this

end

end
end LeanVM.Guest.Complete
