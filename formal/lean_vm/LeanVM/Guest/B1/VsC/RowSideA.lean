/-
  LeanVM.Guest.B1.VsC.RowSideA

  `link_row_side` completes placed from its two `link_rounds`'.
-/

module

public import LeanVM.Guest.B1.VsC.LinkCalleesA
public import LeanVM.Guest.Complete.ComposeRd
import LeanVM.Guest.CoreRef

/-!
# `link_row_side`, placed

`lrs_completeA`: `link_row_side__L{d}` completes placed from the placed completeness of its two
`link_rounds` (rows `(d + 1, b1)`, columns `(d, b2)`), by `callAtA_node` on `lrsBody` with
`LinkCallees.lean`'s valuation: no `HeapBuf`, no `frameAddr`, no load, the two calls placed fresh
one after the other from the cursor past its frame, each on its run of stream words. A chain whose
capacity is not five cells long has no `RoundChain`: that case is vacuous.
`VsLinkCalleesA.row_side`: every row side from the link callees' fields.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem ptrRegion_sub {a b : List (E × ℕ)} (h : ∀ q ∈ a, q ∈ b) {i : ℕ} (hi : ptrRegion a i) :
    ptrRegion b i := by
  obtain ⟨q, hq, t, ht, he⟩ := hi
  exact ⟨q, h q hq, t, ht, he⟩

theorem ptrsBelow_sub {a b : List (E × ℕ)} (h : ∀ q ∈ a, q ∈ b) {fp fp' : ℕ} (hb : PtrsBelow b fp)
    (hle : fp ≤ fp') : PtrsBelow a fp' := fun q hq t ht => by
  obtain ⟨i, hi, he⟩ := hb q (h q hq) t ht
  exact ⟨i, by omega, he⟩

/-- **`link_row_side` completes placed from its two `link_rounds`'.** -/
theorem lrs_completeA {k d b1 b2 : ℕ} {rows cols name : String} {f : Fn}
    (hrows : LinkRoundsCompleteA fs al cert k (d + 1) b1 rows)
    (hcols : LinkRoundsCompleteA fs al cert k d b2 cols)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = (List.range 11).map V.n)
    (hbody : f.body = lrsBody rows cols) : LinkRowSideCompleteA fs al cert k d b1 b2 name := by
  intro f0 f1 f2 f3 f4 cur cl chi qp tabs l1 l2 nw1 nw2 fp hl1 hl2 hc0 hn1 hn2 hpb
  have hlp : coreProgram.loop name = false := by
    rw [Program.loop_of_find? hfind, Fn.loop, hbody, lrsBody]; simp
  by_cases h5 : (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cap.length = 5
  swap
  · exact ⟨fp + fs name, [], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ => trivial,
      fun rd _ _ hP => absurd (chainLast_cap_length rfl hP.2.1) h5⟩
  by_cases h5' : (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cap.length = 5
  swap
  · exact ⟨fp + fs name, [], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ => trivial,
      fun rd _ _ hP => absurd (chainLast_cap_length h5 hP.2.2.1) h5'⟩
  obtain ⟨a1, a2, a3, a4, a5, u, v, hc1, hst1⟩ := cells_eq_seven h5
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, hc2, -⟩ := cells_eq_seven h5'
  have hu : (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cur = u := by rw [hst1]
  rw [hc2]
  rw [hu] at hn2 hpb ⊢
  rw [hst1] at hc2 hn2
  let σ : Val := fun x ↦ (lrsVals [f0, f1, f2, f3, f4, cur, cl, chi, qp, gen ^ l1.length, tabs]
    [a1, a2, a3, a4, a5, u, v] [e1, e2, e3, e4, e5, e6, e7]).getD x.idx 0
  have hw : walk σ f.body = .ret (lrsEvs rows cols) [.n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32] := by
    rw [hbody]; exact walk_lrsBody σ rows cols
  have g6 : gen ^ l2.length = word 64 0 := by
    rw [hl2, show (64 : ℕ) = 2 ^ 6 from rfl, word_two_pow (by norm_num)]
  have hal : allocs σ (lrsEvs rows cols) = [] := by simp [allocs, lrsEvs, Ev.alloc?]
  set c := fp + fs name with hc
  -- the rows' chain, at the aligned base of the cursor past the frame
  have hs1 : ∀ q ∈ lrArrays cur chi tabs nw1 l1.length, q ∈ lrsArrays cur u chi qp tabs nw1 nw2 l1.length := by
    simp [lrArrays, lrsArrays]
  have hs2 : ∀ q ∈ lrArrays u qp tabs nw2 l2.length, q ∈ lrsArrays cur u chi qp tabs nw1 nw2 l1.length := by
    simp [lrArrays, lrsArrays, hl2]
  have hb1 := le_allocBase (al rows) c
  have hu0 : u ≠ 0 := by
    rw [← hu, hn1]; exact mul_ne_zero hc0 (LeanVM.Guest.Value.gen_pow_ne_zero _)
  obtain ⟨ec1, hk1⟩ := hrows f0 f1 f2 f3 f4 cur cl chi tabs l1 nw1 (allocBase (al rows) c) hl1 hc0 hn1
    (ptrsBelow_sub hs1 hpb (by omega))
  have hce1 : allocBase (al rows) c + fs rows ≤ ec1 := by obtain ⟨_, _, h, _⟩ := hk1; exact h
  have hb2 := le_allocBase (al cols) ec1
  obtain ⟨ec2, hk2⟩ := hcols a1 a2 a3 a4 a5 u v qp tabs l2 nw2 (allocBase (al cols) ec1) (by omega) hu0 hn2
    (ptrsBelow_sub hs2 hpb (by omega))
  refine ⟨ec2, callAtA_node hlp le_rfl ⟨σ, f, lrsEvs rows cols,
    [.n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32], [], [PostQuiet, PostQuiet], fun _ => True,
    fun _ => False, hfind, by rw [hparams]; rfl, hw, rfl, ?_, ?_, ?_, ?_, fun _ h => h.elim, ?_,
    fun _ _ => trivial, ?_, ?_⟩⟩
  · rw [hal]
    exact ⟨by simp [allocDsts, lrsEvs, Ev.allocDst?, bases], by simp [addrs, lrsEvs, Ev.addr?]⟩
  · rw [hal]; exact ⟨by simp, List.Pairwise.nil⟩
  · intro A hA; simp [loadAddrs, lrsEvs, Ev.loadAddr?] at hA
  · intro A hA; simp [heapHintAddrs, lrsEvs, Ev.hintAddrs] at hA
  · rw [calls_lrsEvs, hal]
    simp only [KidsAtF, ↓reduceIte, List.headD_cons, List.tail_cons, List.sum_nil, Nat.add_zero]
    have ea1 : [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 9, .n 10].map σ =
        [f0, f1, f2, f3, f4, cur, cl, chi, gen ^ l1.length, tabs] := rfl
    have er1 : [V.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17].map σ =
        (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cells := by rw [hst1]; rfl
    have ea2 : [V.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17, .n 8, .n 18, .n 10].map σ =
        [a1, a2, a3, a4, a5, u, v, qp, gen ^ l2.length, tabs] := by rw [g6]; rfl
    have er2 : [V.n 19, .n 20, .n 21, .n 22, .n 23, .n 24, .n 25].map σ =
        (chainLast ⟨[a1, a2, a3, a4, a5], u, v⟩ l2).cells := by rw [hc2]; rfl
    rw [ea1, er1, ea2, er2]
    refine ⟨fs rows, ec1, ptrRegion (lrArrays cur chi tabs nw1 l1.length), fun _ => False, fun _ => True,
      fun i hi => Or.inl (Or.inl (ptrRegion_sub hs1 hi)), ?_, fs cols, ec2,
      ptrRegion (lrArrays u qp tabs nw2 l2.length), fun _ => False, fun _ => True,
      fun i hi => Or.inl (Or.inl (ptrRegion_sub hs2 hi)), ?_, rfl, fun _ _ => trivial, fun _ h => h.elim⟩
    · exact hk1.mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (fun rd ⟨⟨hw', hc', _, hr, _⟩, _⟩ => ⟨fun _ => hw', hc', hr⟩) (fun _ _ _ h => h)
    · refine hk2.mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (fun rd ⟨⟨hw', _, hc', _, hr⟩, _⟩ => ⟨fun _ => hw', ?_, hr⟩) (fun _ _ _ h => h)
      rwa [hst1] at hc'
  · intro rd _ _ _ e he
    simp only [lrsEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · intro rd ts _ _ _ hv hp
    have hq : ∀ a, Ev.atom a ∈ lrsEvs rows cols → atomQuiet a = true := by
      intro a ha
      simp only [lrsEvs, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Ev.atom.injEq,
        false_or] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    have hx : ∀ e ∈ lrsEvs rows cols, e.Exact rd σ := by
      intro e he
      simp only [lrsEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
    exact postQuiet_node hfind hw hq hx hv (by rw [calls_lrsEvs] at hp ⊢; exact hp) _

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem link_row_side_L6_completeA (k : ℕ) (h7 : LinkRoundsCompleteA fs al cert k 7 0 "link_rounds__L7_L0")
    (h6 : LinkRoundsCompleteA fs al cert k 6 0 "link_rounds__L6_L0") :
    LinkRowSideCompleteA fs al cert k 6 0 0 "link_row_side__L6" :=
  lrs_completeA h7 h6 (coreProgram_find?_at (j := idx% «link_row_side__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem link_row_side_L7_completeA (k : ℕ) (h8 : LinkRoundsCompleteA fs al cert k 8 1 "link_rounds__L8_L1")
    (h7 : LinkRoundsCompleteA fs al cert k 7 0 "link_rounds__L7_L0") :
    LinkRowSideCompleteA fs al cert k 7 1 0 "link_row_side__L7" :=
  lrs_completeA h8 h7 (coreProgram_find?_at (j := idx% «link_row_side__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem link_row_side_L8_completeA (k : ℕ) (h9 : LinkRoundsCompleteA fs al cert k 9 1 "link_rounds__L9_L1")
    (h8 : LinkRoundsCompleteA fs al cert k 8 1 "link_rounds__L8_L1") :
    LinkRowSideCompleteA fs al cert k 8 1 1 "link_row_side__L8" :=
  lrs_completeA h9 h8 (coreProgram_find?_at (j := idx% «link_row_side__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem link_row_side_L9_completeA (k : ℕ) (h10 : LinkRoundsCompleteA fs al cert k 10 1 "link_rounds__L10_L1")
    (h9 : LinkRoundsCompleteA fs al cert k 9 1 "link_rounds__L9_L1") :
    LinkRowSideCompleteA fs al cert k 9 1 1 "link_row_side__L9" :=
  lrs_completeA h10 h9 (coreProgram_find?_at (j := idx% «link_row_side__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel))

/-- **Every `link_row_side__L{d}` completes placed**, from the link callees' fields. -/
theorem VsLinkCalleesA.row_side {k : ℕ} (h : VsLinkCalleesA fs al cert k) :
    ∀ d, 6 ≤ d → d ≤ 9 →
      LinkRowSideCompleteA fs al cert k d (lrsGrind d).1 (lrsGrind d).2 (lrsNames.getD (d - 6) "") := by
  intro d h1 h2
  interval_cases d
  exacts [link_row_side_L6_completeA k h.rounds_L7_L0 h.rounds_L6_L0,
    link_row_side_L7_completeA k h.rounds_L8_L1 h.rounds_L7_L0,
    link_row_side_L8_completeA k h.rounds_L9_L1 h.rounds_L8_L1,
    link_row_side_L9_completeA k h.rounds_L10_L1 h.rounds_L9_L1]

end
end LeanVM.Guest.B1.VsC
