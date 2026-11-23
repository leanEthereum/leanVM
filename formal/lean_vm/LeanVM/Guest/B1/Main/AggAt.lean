/-
  LeanVM.Guest.B1.Main.AggAt

  `aggregate_claims` in the uniform placed form: its buffers after its frame, holding the
  words an honest run leaves, its callees after them; it reads the children's words and writes the
  batching's claim among its caller's words.
-/

module

public import LeanVM.Guest.B1.Main.AggComplete
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Bits.GrindPlaced
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims»

/-!
# `aggregate_claims`, placed

At `fp`, `aggregate_claims` allocates from `b0 = fp + fs "aggregate_claims"` the nonce and the
rounds' words (`47`), the tables of the children's fresh and carried claims (`m` each), the absorbing rows
(`13(m+1)`), the records of `bc_chain` (`2(m+1)`), the sumcheck's point (`23`) and
the weights (`m+1`) (`aggSizes`), holding `aggConts` (`aggOwn`); its callees follow in call order:
`aggregate_claims_loop0`, `aggregate_claims_loop1`, `batch_sumcheck__L23`,
`aggregate_claims_loop2`, the loops and the sumcheck placing nothing (`aggPure`). Its valuation is
`agg_core`'s at the allocator's buffers (`aggPtrsAt`). `AggAtTB` proves it complete, reading the
children's words, the window tables at `tabs` (the inlined `grind_check`'s reads, `AggVals.gptrs`)
and the batching's claim at `g^ds` among the caller's words `Lin`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtD Returns Kid OutsOk CallsMatch RegionsOk outRegion DisjL Within
  disj_append disj_nil kidsFromIn_of_kidsD completeAt_of_rel_pureD regionsOk_of within_append
  bufL bufL_within bufL_disj bufL_region)

@[expose] public section

/-! ## The buffers -/

/-- `aggregate_claims`' `HeapBuf` sizes, in allocation order. -/
def aggSizes (m : ℕ) : List ℕ := [47, m, m, 13 * (m + 1), 2 * (m + 1), 23, 23, m + 1]

/-- The buffers' first words. -/
def axLf (b0 : ℕ) : ℕ := b0 + 47
def axLc (m b0 : ℕ) : ℕ := axLf b0 + m
def axAbs (m b0 : ℕ) : ℕ := axLc m b0 + m
def axChain (m b0 : ℕ) : ℕ := axAbs m b0 + 13 * (m + 1)
def axPt (m b0 : ℕ) : ℕ := axChain m b0 + 2 * (m + 1)
def axPt1 (m b0 : ℕ) : ℕ := axPt m b0 + 23
def axW (m b0 : ℕ) : ℕ := axPt1 m b0 + 23

/-- `aggregate_claims`' pointers at its buffers. -/
def aggPtrsAt (m b0 : ℕ) : AggPtrs :=
  ⟨gen ^ b0, gen ^ axLf b0, gen ^ axLc m b0, gen ^ axAbs m b0, gen ^ axChain m b0,
    gen ^ axPt m b0, gen ^ axPt1 m b0, gen ^ axW m b0⟩

/-- The records of `bc_chain`: record `c` the power `λ^(2c)` and the running claim. -/
def chainRec (cs : List ChildClaims) (h : BatchingHints) (c : ℕ) : List E :=
  [lamA cs h ^ (2 * c), claimAt cs h c]

/-- **The words an honest run leaves in `aggregate_claims`' buffers.** -/
def aggConts (m : ℕ) (cfresh ccarried : E) (cs : List ChildClaims) (h : BatchingHints) :
    List (List E) :=
  [h.lambdaGrindNonce :: h.sumcheckMessages.flatMap (fun g => [g.1, g.2]),
    (List.range m).map (fun c => cfresh * (gen ^ c) ^ 24),
    (List.range m).map (fun c => ccarried * (gen ^ c) ^ 24),
    (List.range (m + 1)).flatMap (fun c => rowW (absSt m cs c)),
    (List.range (m + 1)).flatMap (chainRec cs h),
    (aggRun cs h).1.1,
    (aggRun cs h).1.1.map (1 + ·),
    (List.range (m + 1)).map (weightAt cs h)]

/-- **`aggregate_claims`' own buffers' layout.** -/
def aggOwn (m : ℕ) (cfresh ccarried : E) (cs : List ChildClaims) (h : BatchingHints) (b0 : ℕ) :
    Main.Layout :=
  bufL b0 (aggSizes m) (aggConts m cfresh ccarried cs h)

theorem aggOwn_eq (m : ℕ) (cfresh ccarried : E) (cs : List ChildClaims) (h : BatchingHints) (b0 : ℕ) :
    aggOwn m cfresh ccarried cs h b0 =
      [(b0, h.lambdaGrindNonce :: h.sumcheckMessages.flatMap (fun g => [g.1, g.2])),
        (axLf b0, (List.range m).map (fun c => cfresh * (gen ^ c) ^ 24)),
        (axLc m b0, (List.range m).map (fun c => ccarried * (gen ^ c) ^ 24)),
        (axAbs m b0, (List.range (m + 1)).flatMap (fun c => rowW (absSt m cs c))),
        (axChain m b0, (List.range (m + 1)).flatMap (chainRec cs h)),
        (axPt m b0, (aggRun cs h).1.1),
        (axPt1 m b0, (aggRun cs h).1.1.map (1 + ·)),
        (axW m b0, (List.range (m + 1)).map (weightAt cs h))] := rfl

theorem agg_zip (m b0 : ℕ) : (aggSizes m).zip (bases b0 (aggSizes m)) =
    [(47, b0), (m, axLf b0), (m, axLc m b0), (13 * (m + 1), axAbs m b0),
      (2 * (m + 1), axChain m b0), (23, axPt m b0), (23, axPt1 m b0), (m + 1, axW m b0)] := rfl

theorem len_frange {α : Type} (f : ℕ → List α) (w n : ℕ) (hf : ∀ j, (f j).length = w) :
    ((List.range n).flatMap f).length = n * w := by
  simp [List.length_flatMap, hf]

theorem rowW_abs_len (m : ℕ) (cs : List ChildClaims) (c : ℕ) : (rowW (absSt m cs c)).length = 13 :=
  rowW_length (absSt_ok m cs c)

/-- The buffers' words fit their sizes. -/
theorem aggConts_fit {m : ℕ} {cfresh ccarried : E} {cs : List ChildClaims} {h : BatchingHints}
    (hrl : h.sumcheckMessages.length = 23) :
    List.Forall₂ (fun c s => c.length ≤ s) (aggConts m cfresh ccarried cs h) (aggSizes m) := by
  simp only [aggConts, aggSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨?_, by simp, by simp, ?_, ?_, ?_, ?_, by simp⟩
  · simp [hrl]
  · rw [len_frange _ 13 _ (rowW_abs_len m cs)]; omega
  · rw [len_frange _ 2 _ (fun _ => rfl)]; omega
  · rw [aggRun, bsRun_len, hrl]
  · rw [List.length_map, aggRun, bsRun_len, hrl]

theorem readsAt_rows {rd : Reader} {p : E} {n w : ℕ} {f : ℕ → List E}
    (hw : ∀ c, (f c).length = w) (h : ReadsAt rd p ((List.range n).flatMap f)) :
    ∀ c < n, ReadsAt rd (p * (gen ^ c) ^ w) (f c) := by
  intro c hc
  have := Main.readsAt_flatMap_of (List.range n) (fun c _ => hw c) h c (by simpa using hc)
  simp only [List.getElem_range] at this
  rwa [← pow_mul, Nat.mul_comm c]

theorem loadAt_map {rd : Reader} {p : E} {n : ℕ} {f : ℕ → E}
    (h : ReadsAt rd p ((List.range n).map f)) : ∀ c < n, LoadHolds rd (p * gen ^ c) 0 (f c) := by
  intro c hc
  have := h c (by simpa using hc)
  simp only [List.getElem_map, List.getElem_range] at this
  rw [loadHolds_mul_gen_pow, Nat.add_zero]
  exact this

/-- **`AggMem` off a memory holding `aggregate_claims`' buffers and the claim at `dst`.** -/
theorem aggMem_of_memL {rd : Reader} {cfresh ccarried dst : E} {cs : List ChildClaims}
    {h : BatchingHints} {b0 : ℕ} (hm : MemL rd (aggOwn cs.length cfresh ccarried cs h b0))
    (hdst : ReadsAt rd dst (aggOut cs h).cells) :
    AggMem rd cfresh ccarried dst cs h (aggPtrsAt cs.length b0) := by
  have M : ∀ {b : ℕ} {xs : List E}, (b, xs) ∈ aggOwn cs.length cfresh ccarried cs h b0 →
      ReadsAt rd (gen ^ b) xs := fun hq => reads_of_memL hm hq
  rw [aggOwn_eq] at M
  refine ⟨fun c hc => readsAt_rows (rowW_abs_len _ cs) (M (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) c (by omega),
    loadAt_map (M (List.mem_cons_of_mem _ List.mem_cons_self)),
    loadAt_map (M (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),
    fun c hc => readsAt_rows (f := chainRec cs h) (fun _ => rfl) (M (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))))) c (by omega),
    M List.mem_cons_self,
    M (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))),
    M (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))))),
    fun c hc => loadAt_map (M (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))) c (by omega),
    hdst⟩

/-! ## The callees -/

/-- `aggregate_claims`' callees, which place nothing. -/
def aggPureSet : List String := [name% «aggregate_claims_loop0», name% «aggregate_claims_loop1»,
    name% «aggregate_claims_loop2», "batch_sumcheck__L23"]

/-- Every member's body places nothing and calls members only. -/
noncomputable def aggPureOk : Bool :=
  aggPureSet.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList aggPureSet fn.body
    | none => true

set_option maxRecDepth 100000 in
theorem aggPure_ok : aggPureOk = true := by decide +kernel

theorem aggPure : coreProgram.PureIn aggPureSet := by
  intro g hg fn hf
  have h := List.all_eq_true.mp aggPure_ok g hg
  rw [hf] at h
  exact h

/-! ## The path -/

set_option maxRecDepth 100000 in
theorem aggP_straight : aggP.all Main.Stmt.straight = true := by decide +kernel

/-- `aggregate_claims`' statements: atoms, the sumcheck's call and its guarded loops. -/
def aggKind : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf c _ _ => decide (c ∈ [V.n (val% «aggregate_claims» "s12#1"), .n (val% «aggregate_claims» "s22#1"), .n (val% «aggregate_claims» "s31#1")])
  | _ => false

set_option maxRecDepth 100000 in
theorem aggP_kinds : aggP.all aggKind = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggP_allocs : aggP.filterMap Main.Stmt.allocSz = [(.n (val% «aggregate_claims» "bc_msgs"), .inl 47), (.n (val% «aggregate_claims» "fresh_row"), .inr (.n (val% «aggregate_claims» "n_children_g"))),
    (.n (val% «aggregate_claims» "carried_row"), .inr (.n (val% «aggregate_claims» "n_children_g"))), (.n (val% «aggregate_claims» "absorb"), .inr (.n (val% «aggregate_claims» "absorb~6"))), (.n (val% «aggregate_claims» "bc_chain"), .inr (.n (val% «aggregate_claims» "bc_chain~2"))), (.n (val% «aggregate_claims» "bc_point"), .inl 23),
    (.n (val% «aggregate_claims» "bc_point1"), .inl 23), (.n (val% «aggregate_claims» "bc_wsum"), .inr (.n (val% «aggregate_claims» "bc_wsum~1")))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggP_addrs : aggP.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggP_calls : aggP.filterMap Main.Stmt.callS =
    [(some (.n (val% «aggregate_claims» "s12#1")), name% «aggregate_claims_loop0», [.n (val% «aggregate_claims» "s12#2"), .n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "absorb"), .n (val% «aggregate_claims» "child_fresh"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "child_carried"), .n (val% «aggregate_claims» "carried_row"),
        .n (val% «aggregate_claims» "child_pi")], []),
      (some (.n (val% «aggregate_claims» "s22#1")), name% «aggregate_claims_loop1», [.n (val% «aggregate_claims» "s22#2"), .n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "bc_chain"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "carried_row"), .n (val% «aggregate_claims» "lam_sq"),
          .n (val% «aggregate_claims» "fs_perm.nxt[0]")], []),
      (none, "batch_sumcheck__L23", [.n (val% «aggregate_claims» "fs_perm.nxt[8]"), .n (val% «aggregate_claims» "fs_perm.nxt[9]"), .n (val% «aggregate_claims» "fs_perm.nxt[10]"), .n (val% «aggregate_claims» "fs_perm.nxt[11]"), .n (val% «aggregate_claims» "fs_perm.nxt[12]"), .n (val% «aggregate_claims» "fs0~7"), .n (val% «aggregate_claims» "bc_running@1"), .n (val% «aggregate_claims» "bc_point"), .n (val% «aggregate_claims» "tabs")],
        [.n (val% «aggregate_claims» "fs0"), .n (val% «aggregate_claims» "fs1"), .n (val% «aggregate_claims» "fs2"), .n (val% «aggregate_claims» "fs3"), .n (val% «aggregate_claims» "fs4"), .n (val% «aggregate_claims» "bc_running@2")]),
      (some (.n (val% «aggregate_claims» "s31#1")), name% «aggregate_claims_loop2», [.n (val% «aggregate_claims» "s31#2"), .n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "carried_row"), .n (val% «aggregate_claims» "bc_point1"), .n (val% «aggregate_claims» "bc_chain"),
          .n (val% «aggregate_claims» "bc_wsum"), .n (val% «aggregate_claims» "fs_perm.nxt[0]")], [])] := by
  decide +kernel

/-- The loads `aggregate_claims` may make: its first row and record, first weight, the claim at
`defer_stmt`, its last row, record and weight, the point and `bc_point1`, the nonce, the inlined
grind's table reads. -/
def aggLoadSet : List (V × ℕ) :=
  (List.range 13).map (fun i => (.n (val% «aggregate_claims» "absorb"), i)) ++ [(.n (val% «aggregate_claims» "bc_chain"), 0), (.n (val% «aggregate_claims» "bc_chain"), 1)] ++
    [(.n (val% «aggregate_claims» "bc_wsum"), 0)] ++ (List.range 24).map (fun k => (.n (val% «aggregate_claims» "defer_stmt"), k)) ++
    (List.range 13).map (fun k => (.n (val% «aggregate_claims» "absorbed"), k)) ++ [(.n (val% «aggregate_claims» "bc_end"), 1)] ++
    [(.n (val% «aggregate_claims» "s32#0"), 0)] ++ (List.range 23).map (fun k => (.n (val% «aggregate_claims» "bc_point"), k)) ++
    (List.range 23).map (fun k => (.n (val% «aggregate_claims» "bc_point1"), k)) ++ [(.n (val% «aggregate_claims» "bc_msgs"), 0)] ++
    (gcPtrs 2 aggGo).map fun p => (p, 0)

set_option maxRecDepth 100000 in
theorem aggP_loads : (aggP.filterMap B1.Stmt.loadS).all (fun q => decide (q ∈ aggLoadSet)) = true := by
  decide +kernel

/-- The buffers' sizes' words. -/
noncomputable def aggSizeOk : Bool :=
  let A := atomsIn aggP
  A.any (isConstAt (.n (val% «aggregate_claims» "absorb~0")) 2 0) && isMul A (.n (val% «aggregate_claims» "absorb~1")) (.n (val% «aggregate_claims» "n_children_g")) (.n (val% «aggregate_claims» "absorb~0")) && isMul A (.n (val% «aggregate_claims» "absorb~2")) (.n (val% «aggregate_claims» "absorb~1")) (.n (val% «aggregate_claims» "absorb~1")) &&
  isMul A (.n (val% «aggregate_claims» "absorb~3")) (.n (val% «aggregate_claims» "absorb~2")) (.n (val% «aggregate_claims» "absorb~1")) && isMul A (.n (val% «aggregate_claims» "absorb~4")) (.n (val% «aggregate_claims» "absorb~3")) (.n (val% «aggregate_claims» "absorb~3")) &&
  isMul A (.n (val% «aggregate_claims» "absorb~5")) (.n (val% «aggregate_claims» "absorb~4")) (.n (val% «aggregate_claims» "absorb~4")) && isMul A (.n (val% «aggregate_claims» "absorb~6")) (.n (val% «aggregate_claims» "absorb~5")) (.n (val% «aggregate_claims» "absorb~1")) &&
  A.any (isConstAt (.n (val% «aggregate_claims» "bc_chain~0")) 2 0) && isMul A (.n (val% «aggregate_claims» "bc_chain~1")) (.n (val% «aggregate_claims» "n_children_g")) (.n (val% «aggregate_claims» "bc_chain~0")) &&
  isMul A (.n (val% «aggregate_claims» "bc_chain~2")) (.n (val% «aggregate_claims» "bc_chain~1")) (.n (val% «aggregate_claims» "bc_chain~1")) &&
  A.any (isConstAt (.n (val% «aggregate_claims» "bc_wsum~0")) 2 0) && isMul A (.n (val% «aggregate_claims» "bc_wsum~1")) (.n (val% «aggregate_claims» "n_children_g")) (.n (val% «aggregate_claims» "bc_wsum~0"))

set_option maxRecDepth 100000 in
theorem aggSize_ok : aggSizeOk = true := by decide +kernel

theorem agg_loop : coreProgram.loop "aggregate_claims" = false := by
  rw [Program.loop_of_find? find_aggregate_claims]; decide +kernel

theorem one_add_gen_ne {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

/-- The buffers' sizes, as the valuation computes them. -/
theorem agg_sizes {rd : Reader} {σ : Val} {m : ℕ} (hat : ∀ a ∈ atomsIn aggP, a.Holds rd σ)
    (e0 : σ (.n (val% «aggregate_claims» "n_children_g")) = gen ^ m) :
    σ (.n (val% «aggregate_claims» "absorb~6")) = gen ^ (13 * (m + 1)) ∧ σ (.n (val% «aggregate_claims» "bc_chain~2")) = gen ^ (2 * (m + 1)) ∧
      σ (.n (val% «aggregate_claims» "bc_wsum~1")) = gen ^ (m + 1) := by
  have hok := aggSize_ok
  simp only [aggSizeOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c26, m27⟩, m28⟩, m29⟩, m30⟩, m31⟩, m32⟩, c95⟩, m96⟩, m97⟩, c186⟩, m187⟩ := hok
  have g26 : σ (.n (val% «aggregate_claims» "absorb~0")) = gen := by rw [const_sound c26 hat, word_gen]
  have g95 : σ (.n (val% «aggregate_claims» "bc_chain~0")) = gen := by rw [const_sound c95 hat, word_gen]
  have g186 : σ (.n (val% «aggregate_claims» "bc_wsum~0")) = gen := by rw [const_sound c186 hat, word_gen]
  have s27 : σ (.n (val% «aggregate_claims» "absorb~1")) = gen ^ (m + 1) := by rw [isMul_sound m27 hat, e0, g26, pow_succ]
  have s28 : σ (.n (val% «aggregate_claims» "absorb~2")) = gen ^ (2 * (m + 1)) := by
    rw [isMul_sound m28 hat, s27, ← pow_add, show m + 1 + (m + 1) = 2 * (m + 1) by ring]
  have s29 : σ (.n (val% «aggregate_claims» "absorb~3")) = gen ^ (3 * (m + 1)) := by
    rw [isMul_sound m29 hat, s28, s27, ← pow_add, show 2 * (m + 1) + (m + 1) = 3 * (m + 1) by ring]
  have s30 : σ (.n (val% «aggregate_claims» "absorb~4")) = gen ^ (6 * (m + 1)) := by
    rw [isMul_sound m30 hat, s29, ← pow_add,
      show 3 * (m + 1) + 3 * (m + 1) = 6 * (m + 1) by ring]
  have s31 : σ (.n (val% «aggregate_claims» "absorb~5")) = gen ^ (12 * (m + 1)) := by
    rw [isMul_sound m31 hat, s30, ← pow_add,
      show 6 * (m + 1) + 6 * (m + 1) = 12 * (m + 1) by ring]
  have s96 : σ (.n (val% «aggregate_claims» "bc_chain~1")) = gen ^ (m + 1) := by rw [isMul_sound m96 hat, e0, g95, pow_succ]
  refine ⟨?_, ?_, ?_⟩
  · rw [isMul_sound m32 hat, s31, s27, ← pow_add,
      show 12 * (m + 1) + (m + 1) = 13 * (m + 1) by ring]
  · rw [isMul_sound m97 hat, s96, ← pow_add, show m + 1 + (m + 1) = 2 * (m + 1) by ring]
  · rw [isMul_sound m187 hat, e0, g186, pow_succ]

/-! ## `aggregate_claims` -/

end
end LeanVM.Guest.B1.Main
