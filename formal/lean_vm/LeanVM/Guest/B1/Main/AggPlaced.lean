/-
  LeanVM.Guest.B1.Main.AggPlaced

  `aggregate_claims`' completeness placed by the bump allocator (`RelAt`, Memory/Placed): its
  fifteen `HeapBuf`s right after its frame, its callees after them.
-/

module

public import LeanVM.Guest.B1.Main.AggComplete
public import LeanVM.Guest.B1.Main.Straight
public import LeanVM.Guest.Memory.GuestWf

/-!
# `aggregate_claims`, placed

The body is straight-line (`agBody_eq`, `agPre_straight`), so its path's `HeapBuf` hints and
frames are its statements' (`agPre_allocs`, `agPre_calls`), read by the kernel. At `fp` its
buffers are `aggPtrs fs fp |cs|`, the allocator's bases from `fp + fs "aggregate_claims"` over the
sizes the hints ask (`aggSizes`). Its callees, the five batching loops and the two sumchecks,
place nothing (`aggPure`), so `relAt_of_rel_pure` puts them anywhere; `aggregate_claims_relAt`
composes them by `relAt_of_walk`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-! ## The path -/

/-- `aggregate_claims`' statements before its return. -/
def agPre : List Stmt :=
  agP1 ++ fsCompressT (.n 12) (.n 13) (.n 0) 14 1 ++ agP2 ++ eqtreeT (.n 90) 0 (.n 96) 97 ++
    [.atom (.hint (.alloc (.n 301) 126))] ++ eqtreeT (.n 90) 14 (.n 301) 302 ++ agP3 ++ agStores

theorem agBody_eq : agBody = agPre ++ [.ret []] := by simp [agBody, agPre]

set_option maxRecDepth 100000 in
theorem agPre_straight : agPre.all Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem agPre_allocs : agPre.filterMap Stmt.allocSz =
    [(.n 5, .inl 44), (.n 6, .inl 56), (.n 10, .inr (.n 0)), (.n 11, .inr (.n 0)),
      (.n 31, .inr (.n 30)), (.n 38, .inr (.n 37)), (.n 43, .inr (.n 42)), (.n 56, .inl 22),
      (.n 64, .inr (.n 63)), (.n 74, .inr (.n 73)), (.n 79, .inr (.n 78)), (.n 90, .inl 28),
      (.n 96, .inl 126), (.n 301, .inl 126), (.n 509, .inr (.n 508))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem agPre_addrs : agPre.filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem agPre_calls : agPre.filterMap Stmt.callS =
    [(some (.n 33), "__loop95", [.n 34, .n 0, .n 31, .n 1, .n 2, .n 10, .n 3, .n 11], []),
      (some (.n 48), "__loop96", [.n 49, .n 0, .n 43, .n 38, .n 10, .n 11], []),
      (none, "batch_sumcheck__L22", [.n 53, .n 54, .n 5, .n 55, .n 56], [.n 57, .n 58, .n 59]),
      (some (.n 67), "__loop97", [.n 68, .n 0, .n 10, .n 11, .n 56, .n 64, .n 38], []),
      (some (.n 82), "__loop98", [.n 83, .n 0, .n 79, .n 74, .n 10, .n 11], []),
      (none, "batch_sumcheck__L28", [.n 87, .n 88, .n 6, .n 89, .n 90], [.n 91, .n 92, .n 93]),
      (some (.n 513), "__loop99", [.n 514, .n 0, .n 10, .n 96, .n 90, .n 301, .n 11, .n 74, .n 509],
        [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggregate_claims_not_loop : coreProgram.loop "aggregate_claims" = false := by
  rw [Program.loop_of_find? find_aggregate_claims]; decide +kernel

/-! ## The callees place nothing -/

/-- `aggregate_claims`' callees. -/
abbrev aggCallees : List String :=
  ["__loop95", "__loop96", "__loop97", "__loop98", "__loop99", "batch_sumcheck__L22",
    "batch_sumcheck__L28"]

set_option maxRecDepth 100000 in
theorem find_bs22 : coreProgram.find? "batch_sumcheck__L22" = some Data.core568 :=
  Program.find?_of_indexOf? (j := 568) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_bs28 : coreProgram.find? "batch_sumcheck__L28" = some Data.core571 :=
  Program.find?_of_indexOf? (j := 571) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem aggPure : coreProgram.PureIn aggCallees := by
  intro g hg fn hfn
  simp only [aggCallees, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [find_loop95] at hfn; cases hfn; rw [core566_body]; decide +kernel
  · rw [find_loop96] at hfn; cases hfn; rw [core567_body]; decide +kernel
  · rw [find_loop97] at hfn; cases hfn; rw [core569_body]; decide +kernel
  · rw [find_loop98] at hfn; cases hfn; rw [core570_body]; decide +kernel
  · rw [find_loop99] at hfn; cases hfn; rw [core572_body]; decide +kernel
  · rw [find_bs22] at hfn; cases hfn; rw [core568_body]; decide +kernel
  · rw [find_bs28] at hfn; cases hfn; rw [core571_body]; decide +kernel

/-! ## The buffers -/

/-- The sizes of `aggregate_claims`' `HeapBuf`s for `n` children, in allocation order. -/
def aggSizes (n : ℕ) : List ℕ :=
  [44, 56, n, n, 2 * n + 2, 2 * n, 3 * n + 3, 22, n + 1, 3 * n, 3 * n + 3, 28, 126, 126, 2 * n + 2]

/-- **`aggregate_claims`' `HeapBuf`s at `fp`**: the allocator's bases from the end of its frame. -/
def aggPtrs (fs : String → ℕ) (fp n : ℕ) : AggPtrs :=
  let b := fun i => ofK (Parameters.gpow ((bases (fp + fs "aggregate_claims") (aggSizes n)).getD i 0))
  ⟨b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7, b 8, b 9, b 10, b 11, b 12, b 13, b 14⟩

theorem logG_gen_pow {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gen ^ e) = e := by
  rw [gen_pow_eq_ofK]; exact logG_spec he

/-! ## The callees -/

section Callees

variable {cs : List ChildClaims} {h : BatchHints} {fresh carried : E} {P : AggPtrs}

theorem ag_bs22 (hbr : h.bytecodeRounds.length = 22) (hM : AggMem rd P fresh carried cs h) :
    coreProgram.Rel rd "batch_sumcheck__L22"
      [(digestScalars (sqIt2 (agCvA cs) cs.length)).1, (digestScalars (sqIt2 (agCvA cs) cs.length)).2,
        P.msgB, sumE (List.zipWith bcTerm cs (agLB cs)), P.rs]
      [(digestScalars (agRb cs h).2).1, (digestScalars (agRb cs h).2).2, (agRb cs h).1.2] :=
  (batch_sumcheck_L22_iff rd _ _).mpr ⟨_, h.bytecodeRounds, _, _, _, rfl, hbr,
    fun r hr => by
      have := hM.msgB r (by rwa [hbr] at hr)
      rwa [List.getD_eq_getElem _ _ hr] at this, rfl, hM.rs, rfl⟩

theorem ag_bs28 (hmr : h.matrixRounds.length = 28) (hM : AggMem rd P fresh carried cs h) :
    coreProgram.Rel rd "batch_sumcheck__L28"
      [(digestScalars (sqIt3 (agRb cs h).2 cs.length)).1,
        (digestScalars (sqIt3 (agRb cs h).2 cs.length)).2, P.msgM,
        sumE (List.zipWith mtTerm cs (agLM cs h)), P.rM]
      [(digestScalars (agRm cs h).2).1, (digestScalars (agRm cs h).2).2, (agRm cs h).1.2] :=
  (batch_sumcheck_L28_iff rd _ _).mpr ⟨_, h.matrixRounds, _, _, _, rfl, hmr,
    fun r hr => by
      have := hM.msgM r (by rwa [hmr] at hr)
      rwa [List.getD_eq_getElem _ _ hr] at this, rfl, hM.rM, rfl⟩

end Callees

set_option maxRecDepth 100000 in
/-- **`aggregate_claims`, placed** (G:3319-3486; TRIAGE #77): as `aggregate_claims_complete`, its
`HeapBuf`s where the allocator puts them from `fp` (`aggPtrs`), on a memory holding the honest
words there, `aggregate_claims` holds by a tree placed at `fp`. -/
theorem aggregate_claims_relAt (fs : String → ℕ) (cert : String → V → ℕ) {cs : List ChildClaims}
    {h : BatchHints} {d : DeferredClaim} (hne : cs ≠ []) (hlen : cs.length ≤ 16)
    (hb : batch cs h = some d) (hbr : h.bytecodeRounds.length = 22)
    (hmr : h.matrixRounds.length = 28) {pis fresh carried dp : E}
    (hC : ChildClaimsAt rd pis fresh carried cs) (hd : ReadsAt rd dp d.cells) (fp : ℕ)
    (hM : AggMem rd (aggPtrs fs fp cs.length) fresh carried cs h) :
    ∃ n, RelAt coreProgram fs cert rd fp n "aggregate_claims"
      [gen ^ cs.length, pis, fresh, carried, dp] [] := by
  have hn0 : 0 < cs.length := List.length_pos_iff.mpr hne
  set P := aggPtrs fs fp cs.length with hP
  set σ := agVal cs h P pis fresh carried dp with hσ
  have hH := agBody_holds hne hb hbr hmr hC hd P hM
  have hwf : Stmt.wfList coreProgram agBody = true := by
    have := coreProgram_wf Data.core29 (List.mem_of_find?_eq_some find_aggregate_claims)
    rwa [core29_body] at this
  have hw := walk_straight σ [] agPre agPre_straight
  rw [← agBody_eq] at hw
  have hs := walk_sat agBody hwf hH
  rw [hw] at hs
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ agPre agPre_straight
  rw [agPre_allocs] at e1 e2
  rw [agPre_addrs] at e3
  rw [agPre_calls] at e4
  have hK : 1 + gen ^ cs.length ≠ 0 := one_add_gen_pow_ne_zero hn0 (by unfold ordG; omega)
  have hlt : ∀ e ≤ 3 * cs.length + 3, e < 2 ^ 64 - 1 := fun e he => by
    have : 3 * cs.length + 3 < 2 ^ 64 - 1 := by norm_num; omega
    omega
  -- the callees, anywhere
  obtain ⟨m95, k95⟩ := relAt_of_rel_pure (fs := fs) (cert := cert) coreProgram_wf aggPure
    (g := "__loop95") (by simp) (ag_loop95 hn0 hC hM)
  obtain ⟨m96, k96⟩ := relAt_of_rel_pure (fs := fs) (cert := cert) coreProgram_wf aggPure
    (g := "__loop96") (by simp) (ag_loop96 hn0 hC hM)
  obtain ⟨m22, k22⟩ := relAt_of_rel_pure (fs := fs) (cert := cert) coreProgram_wf aggPure
    (g := "batch_sumcheck__L22") (by simp) (ag_bs22 hbr hM)
  obtain ⟨m97, k97⟩ := relAt_of_rel_pure (fs := fs) (cert := cert) coreProgram_wf aggPure
    (g := "__loop97") (by simp) (ag_loop97 hn0 hbr hC hM)
  obtain ⟨m98, k98⟩ := relAt_of_rel_pure (fs := fs) (cert := cert) coreProgram_wf aggPure
    (g := "__loop98") (by simp) (ag_loop98 hn0 hC hM)
  obtain ⟨m28, k28⟩ := relAt_of_rel_pure (fs := fs) (cert := cert) coreProgram_wf aggPure
    (g := "batch_sumcheck__L28") (by simp) (ag_bs28 hmr hM)
  obtain ⟨m99, k99⟩ := relAt_of_rel_pure (fs := fs) (cert := cert) coreProgram_wf aggPure
    (g := "__loop99") (by simp) (ag_loop99 hn0 hmr hC hM)
  -- the values the path reads
  have t33 : σ (.n 33) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have t48 : σ (.n 48) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have t67 : σ (.n 67) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have t82 : σ (.n 82) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have t513 : σ (.n 513) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have g0 : logG (σ (.n 0)) = cs.length := by
    rw [show σ (.n 0) = gen ^ cs.length by simp only [hσ, agVal]; ag_look]
    exact logG_gen_pow (hlt _ (by omega))
  have g30 : logG (σ (.n 30)) = 2 * cs.length + 2 := by
    rw [show σ (.n 30) = gen ^ (2 * cs.length + 2) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g37 : logG (σ (.n 37)) = 2 * cs.length := by
    rw [show σ (.n 37) = gen ^ (2 * cs.length) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g42 : logG (σ (.n 42)) = 3 * cs.length + 3 := by
    rw [show σ (.n 42) = gen ^ (3 * cs.length + 3) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g63 : logG (σ (.n 63)) = cs.length + 1 := by
    rw [show σ (.n 63) = gen ^ (cs.length + 1) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g73 : logG (σ (.n 73)) = 3 * cs.length := by
    rw [show σ (.n 73) = gen ^ (3 * cs.length) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g78 : logG (σ (.n 78)) = 3 * cs.length + 3 := by
    rw [show σ (.n 78) = gen ^ (3 * cs.length + 3) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g508 : logG (σ (.n 508)) = 2 * cs.length + 2 := by
    rw [show σ (.n 508) = gen ^ (2 * cs.length + 2) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  refine ⟨_, relAt_of_walk (N := m95 + (m96 + (m22 + (m97 + (m98 + (m28 + (m99 + 0)))))))
    coreProgram_wf find_aggregate_claims (Or.inl aggregate_claims_not_loop)
    (by simp only [show Fn.params Data.core29 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
      List.map_cons, List.map_nil, agVal]; ag_look) (by rw [core29_body]; exact hw) rfl
    (fun e he => (hs.1 e he).1) ?_ (by rw [e3]; simp) ?_⟩
  · rw [e1, e2]
    simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, g0, g30, g37, g42, g63,
      g73, g78, g508]
    simp only [agVal]
    ag_look
    simp only [hP, aggPtrs, aggSizes, bases, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ]
  · rw [e4]
    simp only [List.map_cons, List.map_nil, mkCall, KidsFrom, ne_eq, t33, t48, t67, t82, t513,
      not_false_eq_true, decide_true, ↓reduceIte]
    refine ⟨m95, _, rfl, ?_, m96, _, rfl, ?_, m22, _, rfl, ?_, m97, _, rfl, ?_, m98, _, rfl, ?_, m28, _,
      rfl, ?_, m99, _, rfl, ?_, rfl⟩
    all_goals simp only [agVal]
    all_goals ag_look
    exacts [k95 _, k96 _, k22 _, k97 _, k98 _, k28 _, k99 _]

end
end LeanVM.Guest.B1.Main
