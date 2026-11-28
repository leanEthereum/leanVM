module

public import LeanVM.Guest.Complete.Agg.Post
public import LeanVM.Guest.Complete.Agg.W2G
public import LeanVM.Guest.Complete.Claims.Cover
public import LeanVM.Guest.B1.Bits.GrindWin
public import LeanVM.Guest.Exact.Free

/-!
# `aggregate_claims`' exactness

The body's only computed hints are the inlined grind's two window hints (`aggP_computed`, by the
kernel). They write the windows of `nxt[1]` (`aV_win`, the oracle's), which no range check's
temporary touches, so they are exact at the valuation `over aTL` reads from any memory
(`gcInline_exact_of_wins`: `gcInline_exact_of_vals` asking only the windows). Every other atom is no
computed hint (`exact_of_not_computed`).

`aggExactAt`, `aggExactHyp : AggExactHyp al k`, and the field `aggField`: `MainCalleesOpenAt.agg` at
`alW`, `17`, with no open hypothesis; `aggField_honest` at the honest coverage table.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-- **`grind_check` inlined is exact at its honest windows**: `gcInline_exact_of_shape` asking only
the values its two hints write. -/
theorem gcInline_exact_of_wins {σ : Val} {b o : ℕ}
    (hb : 1 ≤ gcTop b ∧ gcTop b ≤ 11 ∧ b + 11 * gcW b + gcTop b = 64) {w tabs : V}
    (hv : ∀ j ≤ gcW b, σ (.n (o + j)) = gcWin b (σ w) j) :
    ∀ s ∈ gcInlineT b o w tabs, ∃ a, s = .atom a ∧ ∀ rd, a.Exact rd σ := by
  obtain ⟨hT1, hT, hsum⟩ := hb
  have hR : ∀ k, 2 ≤ k → k ≤ gcW b + 2 →
      σ (gcRen o w tabs (.n k)) = gcVals (fun _ => none) b (σ w) 0 k := fun k h2 hk ↦ by
    rw [gcRen_own o w tabs h2, show o + k - 2 = o + (k - 2) by omega, hv (k - 2) (by omega), gcWin,
      show 2 + (k - 2) = k by omega]
  intro s hs
  rw [gcInlineT] at hs
  obtain ⟨s0, hs0, e0⟩ := renameList_mem_inv hs
  simp only [gcPre, gcHead, gcTailPre, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_range] at hs0
  rcases hs0 with (hs0 | ⟨l, ⟨i, hi, rfl⟩, hs0⟩) | hs0
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Stmt.rename] at e0 <;> subst e0 <;>
      refine ⟨_, rfl, fun rd ↦ ?_⟩
    · show (((List.range (gcW b)).map fun j => V.n (2 + j)).map (gcRen o w tabs)).map σ =
        (List.range (gcW b)).map fun i ↦
          ofK (g ^ ((LeanVM.Prover.Exec.wordNat (σ (gcRen o w tabs (.n 0))) >>> (b + i * 11)) % 2 ^ 11))
      rw [gcRen_word, List.map_map, List.map_map]
      refine List.map_congr_left fun j hj ↦ ?_
      have hj : j < gcW b := List.mem_range.mp hj
      show σ (gcRen o w tabs (.n (2 + j))) = _
      rw [hR (2 + j) (by omega) (by omega), show 2 + j = gcW b + 2 - (gcW b - j) by omega,
        gv_win (by omega) (by omega), wordNat_window _ (by omega), gen_pow_eq_ofK, gcV,
        show gcW b - (gcW b - j) = j by omega, Nat.mul_comm 11 j]
    · show [σ (gcRen o w tabs (.n (gcW b + 2)))] = (List.range 1).map fun i ↦ ofK (g ^ ((LeanVM.Prover.Exec.wordNat
        (σ (gcRen o w tabs (.n 0))) >>> (b + 11 * gcW b + i * gcTop b)) % 2 ^ gcTop b))
      have hlt : kToNat ((σ w).limb 0) / 2 ^ (b + 11 * gcW b) < 2 ^ gcTop b := gcV_zero_lt hsum (σ w)
      simp only [List.range_one, List.map_cons, List.map_nil, Nat.zero_mul, Nat.add_zero]
      rw [hR (gcW b + 2) (by omega) le_rfl, gv_top, gcRen_word, wordNat_window _ (by omega),
        Nat.mod_eq_of_lt hlt, gen_pow_eq_ofK, gcV, Nat.sub_zero]
    all_goals trivial
  · simp only [gcIterAt, List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Stmt.rename] at e0 <;> subst e0 <;>
      exact ⟨_, rfl, fun _ ↦ trivial⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Stmt.rename] at e0 <;> subst e0 <;>
      exact ⟨_, rfl, fun _ ↦ trivial⟩

set_option maxRecDepth 400000 in
/-- **The body's computed hints are the inlined grind's.** -/
theorem aggP_computed : ∀ a ∈ atomsOf aggP, isComputed a = true → a ∈ aggGrindA := by
  decide +kernel

theorem atom_of_slEvs {σ : Val} {a : Atom} : ∀ {st : Stmt}, Ev.atom a ∈ slEvs σ st → st = .atom a
  | .atom b, h => by simp only [slEvs, List.mem_singleton, Ev.atom.injEq] at h; rw [h]
  | .call .., h => by simp [slEvs] at h
  | .callIf c f args, h => by
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · cases h
    · split at h <;> cases h
  | .ite .., h | .match_ .., h | .dispatch .., h | .ret _, h => by simp [slEvs] at h

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

/-- **The grind's windows** on the honest valuation: the oracle's. -/
theorem aV_win : ∀ j ≤ 5, aV al s w cover c (.n (91 + j)) = gcWin 3 (cellsOfState (aN w) false 1) j := by
  obtain ⟨-, -, -, hw1, hw2, -, -⟩ := grind_split
  intro j hj
  by_cases h5 : j = 5
  · subst h5
    exact (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) (mem_grind hw2)) (.n 96) (by simp)
  · have := (aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) (mem_grind hw1)) (.n (91 + j))
      (by simp; omega)
    rw [this]
    interval_cases j <;> rfl

/-- **`aggregate_claims`' node is exact** on every memory, at the valuation its temporaries read from it. -/
theorem aggExactAt (hr : NodeRelation guestBytecode guestSeed s w) (hd : DeployedLimits s w)
    (hne : w.children ≠ []) (hc : c < 2 ^ 62) : AggExactAt al k s w cover c := by
  intro rd _ _ _
  obtain ⟨h25, hp25, -, -⟩ := aBatched_facts hr hne
  have hl := aLists_length (s := s) h25 hp25
  have hn : w.children.length ≤ 16 := hd.atMostSixteenChildren
  have v79 : aV al s w cover c (.n 79) = cellsOfState (aN w) false 1 := w2_nonce hl hc hn 1
  obtain ⟨-, -, -, -, -, -, hb3⟩ := grind_split
  rw [aV_eq]
  have h79 : over aTL (aV al s w cover c) rd (.n 79) = aV al s w cover c (.n 79) := over_eq (by decide)
  have hv : ∀ j ≤ gcW 3, over aTL (aV al s w cover c) rd (.n (91 + j)) =
      gcWin 3 (over aTL (aV al s w cover c) rd (.n 79)) j := by
    intro j hj
    rw [gcW_3] at hj
    have e : over aTL (aV al s w cover c) rd (.n (91 + j)) = aV al s w cover c (.n (91 + j)) :=
      over_eq (by interval_cases j <;> decide)
    rw [e, h79, v79, aV_win j hj]
  have hgx : ∀ a ∈ aggGrindA, a.Exact rd (over aTL (aV al s w cover c) rd) := by
    intro a ha
    obtain ⟨a', ha', hx⟩ := gcInline_exact_of_wins (gc_shape 3 hb3) (o := 91) (w := .n 79) (tabs := .n 5) hv
      (.atom a) (by rw [← w2_grind]; exact List.mem_map_of_mem ha)
    cases ha'
    exact hx rd
  refine exactAt_of_walk find_agg (walk_agg _) fun e he => ?_
  obtain ⟨st, hst, he⟩ := List.mem_flatMap.mp he
  cases e with
  | atom a =>
    have ha : a ∈ atomsOf aggP := mem_atomsOf' (by rw [← atom_of_slEvs he]; exact hst)
    show a.Exact rd _
    cases hcomp : isComputed a with
    | false => exact exact_of_not_computed hcomp
    | true => exact hgx a (aggP_computed a ha hcomp)
  | _ => trivial

end

theorem aggExactHyp (al : String → Bool) (k : ℕ) : AggExactHyp al k :=
  fun _ _ _ hr hd _ hne _ _ hc => aggExactAt hr hd hne hc

/-- **`MainCalleesOpenAt.agg` at `alW`, `17`**, on every cover of the table's length. -/
theorem aggField {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hr : NodeRelation guestBytecode guestSeed s w) (hd : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w)
    (hcv : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) :
    w.children ≠ [] → AtEveryB alW 17 "aggregate_claims"
      [gen ^ (mainCounts s w).nc, mPtr (mainCounts s w) 5 0, mPtr (mainCounts s w) 6 0, mPtr (mainCounts s w) 7 0,
        mPtr (mainCounts s w) 9 0, ptrAt (mGS alW (mainCounts s w) + winTabAt)] []
      (mainR alW (mainCounts s w)) (MainPreA alW s w cover) (PopsPost (Prover.batchPushes w.batchingHints))
      (B2C.fs "aggregate_claims") (mLo alW (mainCounts s w)) (2 ^ 60) (2 ^ 40) :=
  agg_field_alW_of_exact (aggExactHyp alW 17) hr hd hok hcv

/-- **`MainCalleesOpenAt.agg` at `alW`, `17`, at the honest coverage table.** -/
theorem aggField_honest {s : NodeStatement} {w : NodeWitness} (hr : NodeRelation guestBytecode guestSeed s w)
    (hd : DeployedLimits s w) (hok : ChildrenOk guestBytecode guestSeed w) :
    w.children ≠ [] → AtEveryB alW 17 "aggregate_claims"
      [gen ^ (mainCounts s w).nc, mPtr (mainCounts s w) 5 0, mPtr (mainCounts s w) 6 0, mPtr (mainCounts s w) 7 0,
        mPtr (mainCounts s w) 9 0, ptrAt (mGS alW (mainCounts s w) + winTabAt)] []
      (mainR alW (mainCounts s w)) (MainPreA alW s w (honestCover s w))
      (PopsPost (Prover.batchPushes w.batchingHints)) (B2C.fs "aggregate_claims") (mLo alW (mainCounts s w))
      (2 ^ 60) (2 ^ 40) :=
  aggField hr hd hok (honestCover_length s w)

end
end LeanVM.Guest.Complete.Agg
