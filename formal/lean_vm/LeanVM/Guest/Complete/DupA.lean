module

public import LeanVM.Guest.Complete.MainCalleesA
import LeanVM.Guest.CoreRef

/-!
# The duplicate claims' loops, placed

`main`'s `__loop0_main` and `__loop1_main` hint each duplicate slot's claim (`dup_claims`, `4`
cells) into its table: slot `nl + j` at word `T + 4(nl + j)`, for `j` from the counter `g^j` up
to `g^n`. They allocate nothing and enter no callee but the next iteration (`KidsAtL`).

`dupL_callAtA`: from iteration `j`, at every frame and cursor past its block (`loopBlock L (n - j)`),
the loop completes placed, hinting in the region `R` (which holds the slots' cells), on memories
holding each slot's claim, its pops the claims of slots `j ..< n`, every node exact.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value LeanVM.Guest.B1.VsC
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- A duplicates' loop's body before its `ret`, its recursion naming `L`. -/
def dupPre (L : String) : List Stmt := [
    .atom (.mul (.n 4) (.n 3) (.n 0)),
    .atom (.mul (.n 5) (.n 4) (.n 4)),
    .atom (.mul (.n 6) (.n 5) (.n 5)),
    .atom (.mul (.n 7) (.n 2) (.n 6)),
    .atom (.hint (.witness "dup_claims" (.heap (.n 7) 0 4))),
    .atom (.const (.n 8) (word 2 0)),
    .atom (.mul (.n 9) (.n 0) (.n 8)),
    .atom (.add (.n 10) (.n 9) (.n 1)),
    .atom (.const (.n 11) (word 2 0)),
    .atom (.mul (.n 12) (.n 0) (.n 11)),
    .callIf (.n 10) L [.n 12, .n 1, .n 2, .n 3]
  ]

theorem dup_body0 : (fn% «main_loop0»).body = dupPre "__loop0_main" ++ [.ret []] := rfl

theorem dup_body1 : (fn% «main_loop1»).body = dupPre "__loop1_main" ++ [.ret []] := rfl

set_option maxRecDepth 100000 in
theorem find_dup0 : coreProgram.find? "__loop0_main" = some fn% «main_loop0» :=
  coreProgram_find?_at (j := idx% «main_loop0») rfl

set_option maxRecDepth 100000 in
theorem find_dup1 : coreProgram.find? "__loop1_main" = some fn% «main_loop1» :=
  coreProgram_find?_at (j := idx% «main_loop1») rfl

theorem dup_loop0 : coreProgram.loop "__loop0_main" = true := by decide +kernel

theorem dup_loop1 : coreProgram.loop "__loop1_main" = true := by decide +kernel

theorem dupPre_straight (L : String) : (dupPre L).all Stmt.straight = true := rfl

set_option maxRecDepth 100000 in
theorem dup_pin0 : Stmt.blockNextOk isComputed pinsInverse (fn% «main_loop0»).body = true := by
  rw [dup_body0]; decide +kernel

set_option maxRecDepth 100000 in
theorem dup_pin1 : Stmt.blockNextOk isComputed pinsInverse (fn% «main_loop1»).body = true := by
  rw [dup_body1]; decide +kernel

theorem dup_params0 : (fn% «main_loop0»).params = [.n 0, .n 1, .n 2, .n 3] := rfl

theorem dup_params1 : (fn% «main_loop1»).params = [.n 0, .n 1, .n 2, .n 3] := rfl

/-- The loop's arguments at the counter `g^j`: the count `g^n`, the table `T`, the declared count `g^nl`. -/
def dupArgs (n T nl j : ℕ) : List E := [gen ^ j, gen ^ n, ptrAt T, gen ^ nl]

/-- Iteration `j`'s valuation. -/
noncomputable def dupσ (n T nl j : ℕ) : Val := B1.Val.ofArgs
  (dupArgs n T nl j ++ [gen ^ (nl + j), gen ^ (2 * (nl + j)), gen ^ (4 * (nl + j)), ptrAt (T + 4 * (nl + j)),
    word 2 0, gen ^ (j + 1), gen ^ (j + 1) + gen ^ n, word 2 0, gen ^ (j + 1)])

section Vals
variable (n T nl j : ℕ)

theorem dupσ_args : [V.n 0, .n 1, .n 2, .n 3].map (dupσ n T nl j) = dupArgs n T nl j := by
  simp only [dupσ, dupArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ,
    List.getD_cons_zero, List.map_cons, List.map_nil]

theorem dup_tailArgs : [V.n 12, .n 1, .n 2, .n 3].map (dupσ n T nl j) = dupArgs n T nl (j + 1) := by
  simp only [dupσ, dupArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ,
    List.getD_cons_zero, List.map_cons, List.map_nil]

theorem dup_7 : dupσ n T nl j (.n 7) = ptrAt (T + 4 * (nl + j)) := by
  simp only [dupσ, dupArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ,
    List.getD_cons_zero]

theorem dup_10 : dupσ n T nl j (.n 10) = gen ^ j * word 2 0 + gen ^ n := by
  rw [gen_mul_two]; simp only [dupσ, dupArgs, B1.ofArgs_n, List.cons_append, List.nil_append,
    List.getD_cons_succ, List.getD_cons_zero]

end Vals

theorem dup_guard {n T nl j : ℕ} (hn : n < 2 ^ 34) (hj : j < n) :
    decide (dupσ n T nl j (.n 10) ≠ 0) = decide (j + 1 ≠ n) := by
  rw [dup_10, loopGuard_taken hn (by omega)]

theorem dup_calls (L : String) (σ : Val) : ((dupPre L).filterMap Stmt.callS).map (mkCall σ) =
    [⟨L, [.n 12, .n 1, .n 2, .n 3], [], decide (σ (.n 10) ≠ 0)⟩] := rfl

theorem dup_hints (L : String) (σ : Val) : heapHintAddrs σ ((dupPre L).flatMap (slEvs σ)) =
    (List.range 4).map (fun k => (σ (.n 7)).limb 0 * addressOfIndex (0 + k)) := by
  by_cases h : σ (.n 10) = 0
  · simp only [dupPre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]; rfl
  · simp only [dupPre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]; rfl

theorem dup_splice (L : String) (rd : Reader) (σ : Val) (a : List Pop) :
    splice rd σ ((dupPre L).flatMap (slEvs σ)) [a] = ("dup_claims", (Dest.heap (.n 7) 0 4).words rd σ) :: a := by
  by_cases h : σ (.n 10) = 0
  · simp only [dupPre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]
    simp [splice, Atom.pops, Hint.pops, Dest.words]
  · simp only [dupPre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]
    simp [splice, Atom.pops, Hint.pops, Dest.words]

/-- A duplicates' loop's pops from iteration `j`: the claims of slots `j ..< n`. -/
def dupPops (cells : ℕ → List E) (j n : ℕ) : List Pop := (List.range' j (n - j)).map fun i => ("dup_claims", cells i)

/-- What a duplicates' loop needs: one of the two loops, its count below `2^34`, the slots' cells
in `R`, `Pre` holding each slot's claim. -/
structure DupHyps (L : String) (fn : Fn) (n T nl : ℕ) (cells : ℕ → List E) (R : ℕ → Prop) (Pre : Reader → Prop) :
    Prop where
  find : coreProgram.find? L = some fn
  body : fn.body = dupPre L ++ [.ret []]
  params : fn.params = [.n 0, .n 1, .n 2, .n 3]
  loop : coreProgram.loop L = true
  pin : Stmt.blockNextOk isComputed pinsInverse fn.body = true
  n_lt : n < 2 ^ 34
  len : ∀ j < n, (cells j).length = 4
  region : ∀ j < n, ∀ i < 4, R (T + 4 * (nl + j) + i)
  pre : ∀ rd, Pre rd → ∀ j < n, ReadsAt rd (ptrAt (T + 4 * (nl + j))) (cells j)

theorem dupBlock_succ (L : String) (m : ℕ) : loopBlock L (m + 1) = B2C.fs L + loopBlock L m := by
  unfold loopBlock; ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **One iteration of a duplicates' loop completes placed**, given the next one's completeness. -/
theorem dup_step {al : String → Bool} {k : ℕ} {L : String} {fn : Fn} {n T nl : ℕ} {cells : ℕ → List E}
    {R : ℕ → Prop} {Pre : Reader → Prop} (H : DupHyps L fn n T nl cells R Pre) {j : ℕ} (hj : j < n) {fp c : ℕ}
    (hfc : fp + loopBlock L (n - j) ≤ c)
    (htail : j + 1 < n → ∀ fp' c', fp' + loopBlock L (n - (j + 1)) ≤ c' → ∃ e, e ≤ c' ∧
      CallAtA B2C.fs al B2C.cert k L (dupArgs n T nl (j + 1)) [] R (fun _ => False) (fun _ => True)
        Pre (PopsPost (dupPops cells (j + 1) n)) (loopBlock L (n - (j + 1))) fp' c' e) :
    ∃ e, e ≤ c ∧ CallAtA B2C.fs al B2C.cert k L (dupArgs n T nl j) [] R (fun _ => False) (fun _ => True)
      Pre (PopsPost (dupPops cells j n)) (loopBlock L (n - j)) fp c e := by
  have hblk : loopBlock L (n - j) = B2C.fs L + loopBlock L (n - (j + 1)) := by
    rw [show n - j = n - (j + 1) + 1 by omega, dupBlock_succ]
  rw [hblk] at hfc ⊢
  set σ := dupσ n T nl j with hσ
  set es := (dupPre L).flatMap (slEvs σ) with hes
  have hcalls : calls es = ((dupPre L).filterMap Stmt.callS).map (mkCall σ) :=
    (straight_parts σ (dupPre L) (dupPre_straight L)).2.2.2
  have hal : allocs σ es = [] := by
    rw [(straight_parts σ (dupPre L) (dupPre_straight L)).2.1]; rfl
  have hw : walk σ fn.body = .ret es [] := by
    rw [H.body, walk_straight σ [] (dupPre L) (dupPre_straight L)]
  -- the tail
  obtain ⟨e, hle, hT⟩ : ∃ e, e ≤ c ∧ ∀ (R' : ℕ → Prop), (∀ i, R i → R' i) → ∀ (O : Reader → Prop) (Dacc : ℕ → Prop),
      KidsAtL B2C.fs al B2C.cert k σ R' Pre (fp + B2C.fs L) O Dacc [PopsPost (dupPops cells (j + 1) n)]
        [⟨L, [.n 12, .n 1, .n 2, .n 3], [], decide (σ (.n 10) ≠ 0)⟩] c e (loopBlock L (n - (j + 1)))
        (fun _ => True) (fun _ => False) := by
    by_cases hlt : j + 1 < n
    · obtain ⟨e5, h5le, h5⟩ := htail hlt (fp + B2C.fs L) c (by omega)
      have htk : decide (σ (.n 10) ≠ 0) = true := by
        rw [hσ, dup_guard H.n_lt hj]; exact decide_eq_true (by omega)
      refine ⟨e5, h5le, fun R' hR' O Dacc => ?_⟩
      rw [KidsAtL]; simp only [htk, ↓reduceIte]
      rw [hσ, dup_tailArgs, List.map_nil]
      exact ⟨R, fun _ => False, fun _ => True, fun i hi => Or.inl (hR' i hi),
        h5.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h),
        fun _ _ _ => trivial, fun _ h => h.elim⟩
    · have htk : decide (σ (.n 10) ≠ 0) = false := by
        rw [hσ, dup_guard H.n_lt hj]; exact decide_eq_false (by omega)
      refine ⟨c, le_rfl, fun R' hR' O Dacc => ?_⟩
      rw [KidsAtL, ite_eq_right_of_eq_false _ _ (by simp [htk])]
      refine ⟨⟨dupσ n T nl (j + 1), fn, H.find, ?_⟩, ?_, rfl, fun _ _ => trivial, fun _ h => h.elim⟩
      · rw [H.params]
        show [V.n 0, .n 1, .n 2, .n 3].map (dupσ n T nl (j + 1)) = [V.n 12, .n 1, .n 2, .n 3].map σ
        rw [dupσ_args, hσ, dup_tailArgs]
      · rw [show n - (j + 1) = 0 by omega, loopBlock]; simp
  refine ⟨e, hle, callAtA_nodeLRd H.loop hfc ⟨σ, fn, es, [], [], [PopsPost (dupPops cells (j + 1) n)], fun _ => True,
    fun _ => False, H.find, ?_, fun _ h => h.elim, ?_, fun _ _ => trivial, ?_⟩⟩
  · rw [hal]; exact ⟨by simp, List.Pairwise.nil⟩
  · rw [hcalls, hal, dup_calls, List.sum_nil, Nat.add_zero]
    exact hT _ (fun i h => Or.inl h) _ _
  · intro rd _ hp _
    have hevs : ∀ ev ∈ es, ev.Holds rd σ := by
      rw [hes]
      refine events_straight fun s hs => ?_
      simp only [dupPre, List.mem_cons, List.mem_nil_iff, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [SOk, Atom.Holds, hσ, dupσ, dupArgs, B1.ofArgs_n, List.cons_append, List.nil_append,
        List.getD_cons_succ, List.getD_cons_zero]
      all_goals first
        | with_reducible exact (ptrAt_mul_gen_pow _ _).symm
        | with_reducible exact (gen_mul_two _).symm
        | with_reducible exact gp (by ring)
        | exact B1.Digest.gen_pow_add_isInK _ _
    refine ⟨σ, by rw [H.params, hσ, dupσ_args], hw, rfl, rfl, ?_, ?_, ?_, ?_, hevs, ?_⟩
    · -- placed: no `HeapBuf`, no `frameAddr`
      rw [hal]
      refine ⟨?_, ?_⟩
      · rw [(straight_parts σ (dupPre L) (dupPre_straight L)).1]; rfl
      · rw [(straight_parts σ (dupPre L) (dupPre_straight L)).2.2.1]; simp [dupPre, Stmt.addrS]
    · intro cl hcl
      rw [hcalls, dup_calls] at hcl
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcl
      subst hcl
      simp
    · -- no loads
      intro A hA
      rw [hes, Memory.loadAddrs_straight σ (dupPre L) (dupPre_straight L)] at hA
      simp [dupPre, stmtLoad?] at hA
    · -- the heap hint
      intro A hA
      rw [hes, dup_hints] at hA
      simp only [List.mem_map, List.mem_range] at hA
      obtain ⟨i, hi, rfl⟩ := hA
      rw [hσ, dup_7]
      exact ⟨T + 4 * (nl + j) + (0 + i), Main.addr_ofK _ _, Or.inr (Or.inl (by rw [Nat.zero_add]; exact H.region j hj i hi))⟩
    · -- the tree's pops and exactness
      intro ts hv hq
      rw [hcalls, dup_calls] at hv hq
      obtain ⟨t1, rfl⟩ : ∃ t1, ts = [t1] := by
        have hlen := kidsValid_len hv
        match ts, hlen with
        | [t1], _ => exact ⟨t1, rfl⟩
      rw [kidsPost_cons] at hq
      obtain ⟨q1, -⟩ := hq
      have h1 : PopsPost (dupPops cells (j + 1) n) rd t1 := by
        by_cases hlt : j + 1 < n
        · exact q1 (by
            show decide (σ (.n 10) ≠ 0) = true
            rw [hσ, dup_guard H.n_lt hj]; exact decide_eq_true (by omega))
        · have htk : decide (σ (.n 10) ≠ 0) = false := by
            rw [hσ, dup_guard H.n_lt hj]; exact decide_eq_false (by omega)
          rw [Tree.KidsValid] at hv
          simp only [htk, Bool.false_eq_true, ↓reduceIte] at hv
          obtain ⟨-, ⟨⟨f', σ', rfl⟩, -⟩, -⟩ := hv
          rw [dupPops, show n - (j + 1) = 0 by omega]
          exact ⟨fun _ => rfl, Tree.every_phantom⟩
      refine ⟨?_, Tree.every_node.mpr ⟨exactAt_of_walk H.find hw (exact_of_pinned H.pin hw hevs rd), h1.2, trivial⟩⟩
      have hd7 : (Dest.heap (.n 7) 0 4).words rd σ = cells j := by
        have := heap_words (σ := σ) (p := .n 7) (by rw [hσ, dup_7]; exact H.pre rd hp j hj)
        rwa [H.len j hj] at this
      rw [pops_straight H.find H.body (dupPre_straight L) σ, Tree.popsKids, Tree.popsKids, dup_splice, hd7,
        dupPops, show n - j = n - (j + 1) + 1 by omega, List.range'_succ, List.map_cons]
      exact ss_cons _ h1.1

/-- **A duplicates' loop completes placed** from every iteration `j < n`, at every frame and cursor
past its block: its pops the claims of slots `j ..< n`, every node exact, ending at most at its cursor
(it allocates nothing). -/
theorem dupL_callAtA {al : String → Bool} {k : ℕ} {L : String} {fn : Fn} {n T nl : ℕ} {cells : ℕ → List E}
    {R : ℕ → Prop} {Pre : Reader → Prop} (H : DupHyps L fn n T nl cells R Pre) :
    ∀ j < n, ∀ fp c, fp + loopBlock L (n - j) ≤ c → ∃ e, e ≤ c ∧
      CallAtA B2C.fs al B2C.cert k L (dupArgs n T nl j) [] R (fun _ => False) (fun _ => True)
        Pre (PopsPost (dupPops cells j n)) (loopBlock L (n - j)) fp c e := by
  have key : ∀ t j, j + 1 + t = n → ∀ fp c, fp + loopBlock L (n - j) ≤ c → ∃ e, e ≤ c ∧
      CallAtA B2C.fs al B2C.cert k L (dupArgs n T nl j) [] R (fun _ => False) (fun _ => True)
        Pre (PopsPost (dupPops cells j n)) (loopBlock L (n - j)) fp c e := by
    intro t
    induction t with
    | zero => intro j hj fp c hfc; exact dup_step H (by omega) hfc fun h' => absurd h' (by omega)
    | succ t ih => intro j hj fp c hfc; exact dup_step H (by omega) hfc fun _ => ih (j + 1) (by omega)
  intro j hj
  exact key (n - j - 1) j (by omega)

theorem dupHyps0_static : coreProgram.find? "__loop0_main" = some fn% «main_loop0» ∧
    (fn% «main_loop0»).body = dupPre "__loop0_main" ++ [.ret []] ∧
    (fn% «main_loop0»).params = [.n 0, .n 1, .n 2, .n 3] ∧ coreProgram.loop "__loop0_main" = true ∧
    Stmt.blockNextOk isComputed pinsInverse (fn% «main_loop0»).body = true :=
  ⟨find_dup0, dup_body0, dup_params0, dup_loop0, dup_pin0⟩

theorem dupHyps1_static : coreProgram.find? "__loop1_main" = some fn% «main_loop1» ∧
    (fn% «main_loop1»).body = dupPre "__loop1_main" ++ [.ret []] ∧
    (fn% «main_loop1»).params = [.n 0, .n 1, .n 2, .n 3] ∧ coreProgram.loop "__loop1_main" = true ∧
    Stmt.blockNextOk isComputed pinsInverse (fn% «main_loop1»).body = true :=
  ⟨find_dup1, dup_body1, dup_params1, dup_loop1, dup_pin1⟩

end
end LeanVM.Guest.Complete
