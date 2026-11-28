/-
  LeanVM.Guest.Complete.MainRuns

  `main`'s run windows' hypotheses: the generic tools, and the first run (the counts' touches and range checks).
-/

module

public import LeanVM.Guest.Complete.MainHypAt

/-!
# `main`'s runs

* **Plain runs.** A run without `HeapBuf`, load or heap hint (`plainRunB`) allocates nothing, loads nothing
  and writes no heap hint (`plain_fields`); `runHypT_plain`: its `RunHypT` from its pure and memory facts.
* **Trivial atoms.** An atom other than a backward `mul`, an assertion, a range check, a touch or a load
  (`trivPM`) asks nothing (`pureT_triv`, `memT_triv`); `forall_split`: a fact on a run from the trivial atoms
  and a list of the others.
* **The first run** (`mPre`'s statements `0 ..< 39`): the counts' touches, the range checks
  `n_children < 2^16` and `n_direct_da < 2`, the sizes. `runHypT_w0`: its `RunHypT` at `main`'s honest
  oracle, at `17 ≤ k` on a node with `NodeRelation` and the deployed limits, the memory holding `main`'s
  words (each touched count's word below `2^k` or in `main`'s buffers: `count_def`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Plain runs -/

/-- An atom with no `HeapBuf`, load or heap hint. -/
def plainRunB : Atom → Bool
  | .load .. => false
  | .hint (.alloc ..) => false
  | .hint (.allocDyn ..) => false
  | .hint h => ((hintDest? h).bind destHeap?).isNone
  | _ => true

theorem plain_atom {σ : Val} {a : Atom} (h : plainRunB a = true) :
    Ev.allocDst? (.atom a) = none ∧ Ev.alloc? σ (.atom a) = none ∧ Ev.loadAddr? σ (.atom a) = none ∧
      Ev.hintAddrs σ (.atom a) = [] := by
  cases a with
  | load d p off => simp [plainRunB] at h
  | hint hh =>
    cases hh with
    | alloc d n => simp [plainRunB] at h
    | allocDyn d n => simp [plainRunB] at h
    | witness nm d =>
      cases d with
      | heap p off len => simp [plainRunB, hintDest?, destHeap?] at h
      | stack vs => exact ⟨rfl, rfl, rfl, rfl⟩
    | bits v a b d =>
      cases d with
      | heap p off len => simp [plainRunB, hintDest?, destHeap?] at h
      | stack vs => exact ⟨rfl, rfl, rfl, rfl⟩
    | bitsExp v a d =>
      cases d with
      | heap p off len => simp [plainRunB, hintDest?, destHeap?] at h
      | stack vs => exact ⟨rfl, rfl, rfl, rfl⟩
    | digitsExp v a b c e f d =>
      cases d with
      | heap p off len => simp [plainRunB, hintDest?, destHeap?] at h
      | stack vs => exact ⟨rfl, rfl, rfl, rfl⟩
    | windowsExp v a b c d =>
      cases d with
      | heap p off len => simp [plainRunB, hintDest?, destHeap?] at h
      | stack vs => exact ⟨rfl, rfl, rfl, rfl⟩
    | _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | _ => exact ⟨rfl, rfl, rfl, rfl⟩

/-- **A plain run allocates, loads and writes nothing in the heap.** -/
theorem plain_fields {σ : Val} : ∀ {as : List Atom}, as.all plainRunB = true →
    allocDsts (as.map Ev.atom) = [] ∧ allocs σ (as.map Ev.atom) = [] ∧ loadAddrs σ (as.map Ev.atom) = [] ∧
      heapHintAddrs σ (as.map Ev.atom) = []
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | a :: as, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨i1, i2, i3, i4⟩ := plain_fields (σ := σ) h.2
    obtain ⟨e1, e2, e3, e4⟩ := plain_atom (σ := σ) h.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [allocDsts, List.map_cons, List.filterMap_cons, e1] at i1 ⊢; exact i1
    · simp only [allocs, List.map_cons, List.filterMap_cons, e2] at i2 ⊢; exact i2
    · simp only [loadAddrs, List.map_cons, List.filterMap_cons, e3] at i3 ⊢; exact i3
    · simp only [heapHintAddrs, List.map_cons, List.flatMap_cons, e4, List.nil_append] at i4 ⊢; exact i4

/-- **A plain run's hypotheses** from its pure and memory facts. -/
theorem runHypT_plain {k : ℕ} {σ0 : Val} {w : ℕ → E} {a : ℕ} {Own R D : ℕ → Prop} {Pre O : Reader → Prop}
    {as : List Atom} (h : as.all plainRunB = true) (hp : ∀ x ∈ as, PureT σ0 x)
    (hm : ∀ rd, LowDef k rd → Pre rd → O rd → ∀ x ∈ as, MemT rd σ0 x) :
    RunHypT k σ0 w a Own R D Pre O as := by
  obtain ⟨i1, i2, i3, i4⟩ := plain_fields (σ := σ0) h
  refine ⟨?_, ?_, ?_, hp, hm⟩
  · rw [i1, i2]; rfl
  · rw [i3]; intro A hA; simp at hA
  · rw [i4]; intro A hA; simp at hA

/-! ## Trivial atoms -/

/-- An atom asking nothing beyond its equations: not a backward `mul`, an assertion, a range check, a
touch or a load. -/
def trivPM : Atom → Bool
  | .mul d x y => decide (x.idx < d.idx) && decide (y.idx < d.idx)
  | .assertEq .. | .assertInK .. | .rangeCheck .. | .touch .. | .load .. => false
  | _ => true

theorem pureT_triv {σ : Val} {a : Atom} (h : trivPM a = true) : PureT σ a := by
  cases a with
  | mul d x y =>
    simp only [trivPM, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [PureT, h]
  | assertEq x y => simp [trivPM] at h
  | assertInK x y => simp [trivPM] at h
  | rangeCheck x y t1 t2 kk => simp [trivPM] at h
  | touch t p => simp [trivPM] at h
  | load d p off => simp [trivPM] at h
  | _ => trivial

theorem memT_triv {rd : Reader} {σ : Val} {a : Atom} (h : trivPM a = true) : MemT rd σ a := by
  cases a with
  | rangeCheck x y t1 t2 kk => simp [trivPM] at h
  | touch t p => simp [trivPM] at h
  | load d p off => simp [trivPM] at h
  | _ => trivial

/-- **A fact on a run** from the trivial atoms and the others listed. -/
theorem forall_split {P : Atom → Prop} {as sp : List Atom}
    (h : as.all (fun a => trivPM a || decide (a ∈ sp)) = true) (ht : ∀ a, trivPM a = true → P a)
    (hs : ∀ a ∈ sp, P a) : ∀ x ∈ as, P x := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h1 | h1
  · exact ht x h1
  · exact hs x h1

/-! ## Range checks on the forward valuation -/

theorem good_rc_div {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {x y t1 t2 kk : ℕ}
    (h : Good rd S w σ (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n kk))) (hk : kk < y) :
    σ (.n y) = σ (.n kk) * (σ (.n x))⁻¹ := by
  have h3 := h.2.2
  split at h3
  · exact h3
  · rename_i hne
    exact (hne hk).elim

theorem gen_pow_div {a b : ℕ} (h : b ≤ a) : gen ^ a * (gen ^ b)⁻¹ = gen ^ (a - b) :=
  (pow_sub₀ gen Value.gen_ne_zero h).symm

theorem word_65536 : word 65536 0 = gen ^ 16 := by
  rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, Sig.word_two_pow_eq (j := 16) (by norm_num), Value.gen_pow_eq_ofK]

/-! ## The first run -/

/-- The first run's atoms that ask something: the counts' touches and the two range checks. -/
def w0Sp : List Atom :=
  [.touch (.n 8) (.n 0), .touch (.n 9) (.n 1), .touch (.n 10) (.n 2), .touch (.n 11) (.n 3),
    .touch (.n 12) (.n 4), .touch (.n 13) (.n 5), .rangeCheck (.n 6) (.n 15) (.n 16) (.n 17) (.n 14),
    .rangeCheck (.n 7) (.n 19) (.n 20) (.n 21) (.n 18), .touch (.n 25) (.n 24)]

set_option maxRecDepth 200000 in
theorem w0_shape : (atomsOf ((mPre.drop 0).take 39)).all plainRunB = true ∧
    (atomsOf ((mPre.drop 0).take 39)).all (fun a => trivPM a || decide (a ∈ w0Sp)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem w0_mem : Atom.const (.n 14) (word 65536 0) ∈ atomsOf mPre ∧
    Atom.rangeCheck (.n 6) (.n 15) (.n 16) (.n 17) (.n 14) ∈ atomsOf mPre ∧
    Atom.const (.n 18) (word 2 0) ∈ atomsOf mPre ∧
    Atom.rangeCheck (.n 7) (.n 19) (.n 20) (.n 21) (.n 18) ∈ atomsOf mPre := by
  decide +kernel

theorem nd_le (s : NodeStatement) (w : NodeWitness) : (mainCounts s w).nd ≤ 1 := by
  show (w.daMatrix.map fun _ => 1).getD 0 ≤ 1
  cases w.daMatrix <;> simp

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {rd0 : Reader}

/-- **The range checks' quotients** on the honest oracle: `2^16 / g^n_children` and `g / g^n_direct_da`. -/
theorem w0_rcs (hn : (mainCounts s w).nc ≤ 16) :
    mVal rd0 (mOrc al s w) (.n 15) = gen ^ (16 - (mainCounts s w).nc) ∧
      mVal rd0 (mOrc al s w) (.n 19) = gen ^ (1 - (mainCounts s w).nd) := by
  obtain ⟨k14, r15, k18, r19⟩ := w0_mem
  obtain ⟨-, -, -, -, -, -, c6, c7⟩ := mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)
  have e14 : mVal rd0 (mOrc al s w) (.n 14) = word 65536 0 := mPre_good k14
  have e18 : mVal rd0 (mOrc al s w) (.n 18) = word 2 0 := mPre_good k18
  refine ⟨?_, ?_⟩
  · rw [good_rc_div (mPre_good r15) (by norm_num), e14, c6, word_65536, gen_pow_div hn]
  · have hd := gen_pow_div (a := 1) (nd_le s w)
    rw [pow_one] at hd
    rw [good_rc_div (mPre_good r19) (by norm_num), e18, c7, word_gen, hd]

/-- **The first run's hypotheses** at `main`'s honest oracle. -/
theorem runHypT_w0 {k : ℕ} {cover : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}
    (hk : 17 ≤ k) (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) :
    RunHypT k (mVal rd0 (mOrc al s w)) (mOrc al s w) (B2C.fs "main") Own R (fun _ => False) Pre
      (fun rd => HoldsWords rd (mainWords s w cover)) (atomsOf ((mPre.drop 0).take 39)) := by
  obtain ⟨hplain, hsplit⟩ := w0_shape
  have hn := nc_le hlim
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)
  obtain ⟨-, -, v24, -⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := rd0)
  obtain ⟨r15, r19⟩ := w0_rcs (al := al) (rd0 := rd0) hn
  have hraw := raw_le_slots hr
  have hnd := nd_le s w
  have h17 : (2 : ℕ) ^ 17 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  refine runHypT_plain hplain (forall_split hsplit (fun a h => pureT_triv h) ?_) fun rd hL _ hO =>
    forall_split hsplit (fun a h => memT_triv h) ?_
  · intro a ha
    simp only [w0Sp, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show IsInK _; rw [c0]; exact gen_pow_isInK _
    · show IsInK _; rw [c1]; exact gen_pow_isInK _
    · show IsInK _; rw [c2]; exact gen_pow_isInK _
    · show IsInK _; rw [c3]; exact gen_pow_isInK _
    · show IsInK _; rw [c4]; exact gen_pow_isInK _
    · show IsInK _; rw [c5]; exact gen_pow_isInK _
    · exact pureT_rc c6 r15
    · exact pureT_rc c7 r19
    · show IsInK _; rw [v24]; exact gen_pow_isInK _
  · have cd : ∀ c, c ≤ (mainCounts s w).sx + (mainCounts s w).ss → (rd (addressOfIndex c)).isSome :=
      fun c hc => count_def hk hl hc hL hO
    have lo : ∀ c, c < 2 ^ 17 → (rd (addressOfIndex c)).isSome := fun c hc => hL c (lt_of_lt_of_le hc h17)
    intro a ha
    simp only [w0Sp, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact memT_touch c0 (cd _ (by simp only [MainCounts.sx]; omega))
    · exact memT_touch c1 (cd _ (by simp only [MainCounts.sx]; omega))
    · exact memT_touch c2 (cd _ (by omega))
    · exact memT_touch c3 (cd _ (by simp only [MainCounts.ss]; omega))
    · exact memT_touch c4 (cd _ (by simp only [MainCounts.ss]; omega))
    · exact memT_touch c5 (cd _ (by omega))
    · exact memT_rc c6 r15 (lo _ (by omega)) (lo _ (by omega))
    · exact memT_rc c7 r19 (lo _ (by omega)) (lo _ (by omega))
    · exact memT_touch v24 (cd _ le_rfl)

end

end
end LeanVM.Guest.Complete
