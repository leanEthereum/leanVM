/-
  LeanVM.Guest.B1.Main.AggAt

  `aggregate_claims` in the uniform placed form: its buffers after its frame, holding the
  words an honest run leaves, its callees after them; it reads the children's words and writes the
  batching's claim among its caller's words.
-/

module

public import LeanVM.Guest.B1.Main.AggComplete
public import LeanVM.Guest.B1.Da.AtBase

/-!
# `aggregate_claims`, placed

At `fp`, `aggregate_claims` allocates from `b0 = fp + fs "aggregate_claims"` the nonce and the
rounds' words (`47`), the tables of the children's fresh and carried claims (`m` each), the absorbing rows
(`13(m+1)`), the records of `bc_chain` (`2(m+1)`), the sumcheck's point (`23`) and
the weights (`m+1`) (`aggSizes`), holding `aggConts` (`aggOwn`); its callees follow in call order:
`__loop33`, `grind_check__L2`, `__loop34`, `batch_sumcheck__L23`, `__loop35`, the loops and the
sumcheck placing nothing (`aggPure`). Its valuation is `agg_core`'s at the allocator's buffers
(`aggPtrsAt`).
`aggregate_claims_completeAt`: `aggregate_claims` is `CompleteAtD`, reading the children's words,
the window tables at `tabs` and the batching's claim at `g^ds` among the caller's words `Lin`, given
`grind_check__L2`'s completeness (`CompleteRelD` with `aggGrindPre`).
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
def aggPureSet : List String := ["__loop33", "__loop34", "__loop35", "batch_sumcheck__L23"]

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
  | .callIf c _ _ => decide (c ∈ [V.n 35, .n 102, .n 191])
  | _ => false

set_option maxRecDepth 100000 in
theorem aggP_kinds : aggP.all aggKind = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggP_allocs : aggP.filterMap Main.Stmt.allocSz = [(.n 6, .inl 47), (.n 8, .inr (.n 0)),
    (.n 9, .inr (.n 0)), (.n 33, .inr (.n 32)), (.n 98, .inr (.n 97)), (.n 107, .inl 23),
    (.n 116, .inl 23), (.n 188, .inr (.n 187))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggP_addrs : aggP.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggP_calls : aggP.filterMap Main.Stmt.callS =
    [(some (.n 35), "__loop33", [.n 36, .n 0, .n 33, .n 2, .n 8, .n 3, .n 9, .n 1], []),
      (none, "grind_check__L2", [.n 82, .n 5], []),
      (some (.n 102), "__loop34", [.n 103, .n 0, .n 98, .n 8, .n 9, .n 94, .n 81], []),
      (none, "batch_sumcheck__L23", [.n 89, .n 90, .n 91, .n 92, .n 93, .n 109, .n 106, .n 107, .n 5],
        [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115]),
      (some (.n 191), "__loop35", [.n 192, .n 0, .n 8, .n 9, .n 116, .n 98, .n 188, .n 81], [])] := by
  decide +kernel

/-- The loads `aggregate_claims` may make: its first row and record, first weight, the claim at
`defer_stmt`, its last row, record and weight, the point and `bc_point1`, the nonce. -/
def aggLoadSet : List (V × ℕ) :=
  (List.range 13).map (fun i => (.n 33, i)) ++ [(.n 98, 0), (.n 98, 1)] ++
    [(.n 188, 0)] ++ (List.range 24).map (fun k => (.n 4, k)) ++
    (List.range 13).map (fun k => (.n 42, k)) ++ [(.n 105, 1)] ++
    [(.n 193, 0)] ++ (List.range 23).map (fun k => (.n 107, k)) ++
    (List.range 23).map (fun k => (.n 116, k)) ++ [(.n 6, 0)]

set_option maxRecDepth 100000 in
theorem aggP_loads : (aggP.filterMap B1.Stmt.loadS).all (fun q => decide (q ∈ aggLoadSet)) = true := by
  decide +kernel

/-- The buffers' sizes' words. -/
noncomputable def aggSizeOk : Bool :=
  let A := atomsIn aggP
  A.any (isConstAt (.n 26) 2 0) && isMul A (.n 27) (.n 0) (.n 26) && isMul A (.n 28) (.n 27) (.n 27) &&
  isMul A (.n 29) (.n 28) (.n 27) && isMul A (.n 30) (.n 29) (.n 29) &&
  isMul A (.n 31) (.n 30) (.n 30) && isMul A (.n 32) (.n 31) (.n 27) &&
  A.any (isConstAt (.n 95) 2 0) && isMul A (.n 96) (.n 0) (.n 95) &&
  isMul A (.n 97) (.n 96) (.n 96) &&
  A.any (isConstAt (.n 186) 2 0) && isMul A (.n 187) (.n 0) (.n 186)

set_option maxRecDepth 100000 in
theorem aggSize_ok : aggSizeOk = true := by decide +kernel

theorem agg_loop : coreProgram.loop "aggregate_claims" = false := by
  rw [Program.loop_of_find? find_aggregate_claims]; decide +kernel

theorem one_add_gen_ne {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

/-- The buffers' sizes, as the valuation computes them. -/
theorem agg_sizes {rd : Reader} {σ : Val} {m : ℕ} (hat : ∀ a ∈ atomsIn aggP, a.Holds rd σ)
    (e0 : σ (.n 0) = gen ^ m) :
    σ (.n 32) = gen ^ (13 * (m + 1)) ∧ σ (.n 97) = gen ^ (2 * (m + 1)) ∧
      σ (.n 187) = gen ^ (m + 1) := by
  have hok := aggSize_ok
  simp only [aggSizeOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c26, m27⟩, m28⟩, m29⟩, m30⟩, m31⟩, m32⟩, c95⟩, m96⟩, m97⟩, c186⟩, m187⟩ := hok
  have g26 : σ (.n 26) = gen := by rw [const_sound c26 hat, word_gen]
  have g95 : σ (.n 95) = gen := by rw [const_sound c95 hat, word_gen]
  have g186 : σ (.n 186) = gen := by rw [const_sound c186 hat, word_gen]
  have s27 : σ (.n 27) = gen ^ (m + 1) := by rw [isMul_sound m27 hat, e0, g26, pow_succ]
  have s28 : σ (.n 28) = gen ^ (2 * (m + 1)) := by
    rw [isMul_sound m28 hat, s27, ← pow_add, show m + 1 + (m + 1) = 2 * (m + 1) by ring]
  have s29 : σ (.n 29) = gen ^ (3 * (m + 1)) := by
    rw [isMul_sound m29 hat, s28, s27, ← pow_add, show 2 * (m + 1) + (m + 1) = 3 * (m + 1) by ring]
  have s30 : σ (.n 30) = gen ^ (6 * (m + 1)) := by
    rw [isMul_sound m30 hat, s29, ← pow_add,
      show 3 * (m + 1) + 3 * (m + 1) = 6 * (m + 1) by ring]
  have s31 : σ (.n 31) = gen ^ (12 * (m + 1)) := by
    rw [isMul_sound m31 hat, s30, ← pow_add,
      show 6 * (m + 1) + 6 * (m + 1) = 12 * (m + 1) by ring]
  have s96 : σ (.n 96) = gen ^ (m + 1) := by rw [isMul_sound m96 hat, e0, g95, pow_succ]
  refine ⟨?_, ?_, ?_⟩
  · rw [isMul_sound m32 hat, s31, s27, ← pow_add,
      show 12 * (m + 1) + (m + 1) = 13 * (m + 1) by ring]
  · rw [isMul_sound m97 hat, s96, ← pow_add, show m + 1 + (m + 1) = 2 * (m + 1) by ring]
  · rw [isMul_sound m187 hat, e0, g186, pow_succ]

/-! ## `aggregate_claims` -/

/-- What `grind_check__L2`'s completeness asks of its call: nothing returned, the window tables at
its second argument, and its first argument's low limb passing the proof of work. -/
def aggGrindPre (rd : Reader) (args rets : List E) : Prop :=
  rets = [] ∧ ∃ w tabs, args = [w, tabs] ∧ WinTabs rd tabs ∧ (w.limb 0).lane.toNat % 2 ^ 2 = 0

set_option maxRecDepth 20000 in
/-- **`aggregate_claims` is complete, placed**: on `m ≤ 16` children whose words the caller's
words `Lin` hold, the window tables at `tabs`, the hints of an accepting batching, writing the
batching's claim, which `Lin` holds at `g^ds`; given
`grind_check__L2`'s completeness. -/
theorem aggregate_claims_completeAt (fs : String → ℕ) (cert : String → V → ℕ)
    (hGr : CompleteRelD fs cert 16 "grind_check__L2" aggGrindPre) {m : ℕ}
    (hm1 : 1 ≤ m) (hm16 : m ≤ 16) {cs : List ChildClaims} (hcl : cs.length = m) {h : BatchingHints}
    {out : DeferredClaim} (hrl : h.sumcheckMessages.length = 23) (hb : batch cs h = some out)
    {cpi cfresh ccarried tabs : E} {ds : ℕ} {Lin : Main.Layout}
    (hcw : ∀ rd, Main.MemL rd Lin → ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (htabs : ∀ rd, LowDef 16 rd → Main.MemL rd Lin → WinTabs rd tabs)
    (hdst : (ds, out.cells) ∈ Lin) :
    CompleteAtD fs cert 16 "aggregate_claims" Lin [gen ^ m, cpi, cfresh, ccarried, gen ^ ds, tabs]
      (Returns []) := by
  subst hcl
  obtain ⟨hout, hpow, -⟩ := batch_out hb
  subst hout
  intro fp
  set m := cs.length with hmd
  set b0 := fp + fs "aggregate_claims" with hb0
  set P := aggPtrsAt m b0 with hP
  set Own := aggOwn m cfresh ccarried cs h b0 with hOwn
  have hfit := aggConts_fit (m := m) (cfresh := cfresh) (ccarried := ccarried) (cs := cs) hrl
  have hbm : ∀ rd, Main.MemL rd (Own ++ Lin) → AggMem rd cfresh ccarried (gen ^ ds) cs h P :=
    fun rd hm => by
      obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
      exact aggMem_of_memL h1 (reads_of_memL h2 hdst)
  have hcw' : ∀ rd, Main.MemL rd (Own ++ Lin) → ∀ c (hc : c < cs.length),
      ChildWordsAt rd cpi cfresh ccarried c cs[c] :=
    fun rd hm => hcw rd (Main.memL_append.mp hm).2
  have hne : (1 : E) + gen ^ m ≠ 0 := (one_add_gen_ne (by omega)).mpr (by omega)
  -- the callees
  let ks : List Kid :=
    [⟨"__loop33", true, [1, gen ^ m, P.absorb, cfresh, P.lf, ccarried, P.lc, cpi], Own ++ Lin,
        Returns []⟩,
      ⟨"grind_check__L2", true, [cellsOfState (aggN cs h.lambdaGrindNonce) false 1, tabs],
        Own ++ Lin, Returns []⟩,
      ⟨"__loop34", true, [1, gen ^ m, P.chain, P.lf, P.lc, lamA cs h * lamA cs h, lamA cs h],
        Own ++ Lin, Returns []⟩,
      ⟨"batch_sumcheck__L23", true,
        capOf (aggN cs h.lambdaGrindNonce) ++ [P.msgs * gen, claimAt cs h m, P.pt, tabs],
        Own ++ Lin, Returns ((aggRun cs h).2.cap ++ [(aggRun cs h).1.2])⟩,
      ⟨"__loop35", true, [1, gen ^ m, P.lf, P.lc, P.pt1, P.chain, P.w, lamA cs h], Own ++ Lin,
        Returns []⟩]
  have hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert 16 k.f k.Lin k.args k.Out := by
    intro k hk _
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact completeAt_of_rel_pureD aggPure (by simp [aggPureSet]) (fun rd hm =>
        (guard_complete find_l25 l25_shape' (rest := [P.absorb, cfresh, P.lf, ccarried, P.lc, cpi])
          (agg_l25 (hcw' rd hm) (hbm rd hm))).2 hne) 16
    · exact hGr _ _ _ fun rd hl hm =>
        ⟨rfl, _, _, rfl, htabs rd hl (Main.memL_append.mp hm).2, agg_pow hpow⟩
    · exact completeAt_of_rel_pureD aggPure (by simp [aggPureSet]) (fun rd hm =>
        (guard_complete find_l26 l26_shape.1
          (rest := [P.chain, P.lf, P.lc, lamA cs h * lamA cs h, lamA cs h])
          (agg_l26 (hcw' rd hm) (hbm rd hm))).2 hne) 16
    · exact completeAt_of_rel_pureD aggPure (by simp [aggPureSet])
        (fun rd hm => agg_bs tabs hrl (hbm rd hm)) 16
    · exact completeAt_of_rel_pureD aggPure (by simp [aggPureSet]) (fun rd hm =>
        (guard_complete find_l27 l27_shape.1 (rest := [P.lf, P.lc, P.pt1, P.chain, P.w, lamA cs h])
          (agg_l27 (hcw' rd hm) hrl (hbm rd hm))).2 hne) 16
  obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
    kidsFromIn_of_kidsD (fs := fs) (cert := cert) 16 ks hok (b0 + (aggSizes m).sum)
  have hl0 : outs.length = 5 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain ⟨o4, t4, rfl, hl4⟩ := exists_of_length_succ hl3
  obtain ⟨o5, t5, rfl, hl5⟩ := exists_of_length_succ hl4
  obtain rfl := List.eq_nil_of_length_eq_zero hl5
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hoo
  -- the layout
  have hWo : Within Own b0 (aggSizes m).sum := bufL_within _ _ _ hfit
  refine ⟨fs "aggregate_claims" + (aggSizes m).sum + Nk, Own ++ Lk, [], [], ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append (bufL_disj _ _ _ hfit : DisjL Own) hD hWo hW le_rfl,
    fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1', hLin'⟩ := Main.memL_append.mp hm
  obtain ⟨hmO, hLk⟩ := Main.memL_append.mp hm1'
  have hmK : Main.MemL rd (Own ++ Lin) := Main.memL_append.mpr ⟨hmO, hLin'⟩
  have hmem := hbm rd hmK
  -- the valuation and the path
  have hV := agg_core (rd := rd) (cpi := cpi) (tabs := tabs) rfl (hcw' rd hmK) hrl hb hmem
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = aggσ rd m cpi cfresh ccarried (gen ^ ds) tabs P cs h := ⟨_, rfl⟩
  rw [← hσ] at hV
  have hw := Main.walk_straight σ [] aggP aggP_straight
  rw [← agg_shape] at hw
  set es := aggP.flatMap (Main.slEvs σ) with hes
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    refine slEvs_holds fun st hst => ?_
    have hk := List.all_eq_true.mp aggP_kinds st hst
    match st, hk with
    | .atom a, _ => exact hV.atoms a (mem_atomsIn hst)
    | .call .., _ => trivial
    | .ite .., hk => simp [aggKind] at hk
    | .match_ .., hk => simp [aggKind] at hk
    | .dispatch .., hk => simp [aggKind] at hk
    | .ret _, hk => simp [aggKind] at hk
    | .callIf c f args, hk =>
      simp only [aggKind, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at hk
      show IsInK (σ c)
      rcases hk with rfl | rfl | rfl
      · rw [hV.g35, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · rw [hV.g102, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · rw [hV.g191, ← pow_zero gen]; exact gen_pow_add_isInK _ _
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ aggP_straight
  obtain ⟨s32, s97, s187⟩ := agg_sizes hV.atoms hV.e0
  have hal : allocs σ es = aggSizes m := by
    rw [hes, hpa, aggP_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, hV.e0, s32, s97, s187,
      logG_gen_pow (show cs.length < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 13 * (cs.length + 1) < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 2 * (cs.length + 1) < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show cs.length + 1 < 2 ^ 64 - 1 by omega)]
    rfl
  have hT : ∀ {c : V}, σ c = 1 + gen ^ m → decide (σ c ≠ 0) = true :=
    fun h => by rw [h]; exact decide_eq_true hne
  have hcalls : calls es =
      [⟨"__loop33", [.n 36, .n 0, .n 33, .n 2, .n 8, .n 3, .n 9, .n 1], [], true⟩,
        ⟨"grind_check__L2", [.n 82, .n 5], [], true⟩,
        ⟨"__loop34", [.n 103, .n 0, .n 98, .n 8, .n 9, .n 94, .n 81], [], true⟩,
        ⟨"batch_sumcheck__L23", [.n 89, .n 90, .n 91, .n 92, .n 93, .n 109, .n 106, .n 107, .n 5],
          [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115], true⟩,
        ⟨"__loop35", [.n 192, .n 0, .n 8, .n 9, .n 116, .n 98, .n 188, .n 81], [], true⟩] := by
    rw [hes, hpc, aggP_calls]
    simp only [List.map_cons, List.map_nil, Main.mkCall, hT hV.g35, hT hV.g102, hT hV.g191]
  -- the walk
  have hown : ∀ i, Main.RegionL Own i → ownData cert fp b0 "aggregate_claims" (aggSizes m) es i :=
    fun i hi => Or.inl (bufL_region _ _ _ hfit i hi)
  have hz : ∀ {s x j : ℕ}, (s, x) ∈ (aggSizes m).zip (bases b0 (aggSizes m)) → x ≤ j →
      j < x + s → ownData cert fp b0 "aggregate_claims" (aggSizes m) es j :=
    fun hq h1 h2 => Or.inl ⟨_, hq, h1, h2⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := Main.RegionL Lin) (D := Main.RegionL []) (fp := fp) (N := Nk)
    (args := [gen ^ m, cpi, cfresh, ccarried, gen ^ ds, tabs]) (rets := [])
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4, o5] i)
    coreProgram_wf find_aggregate_claims (Or.inl agg_loop) (by
      show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] = _
      rw [hV.e0, hV.e1, hV.e2, hV.e3, hV.e4, hV.e5]) hw rfl hev
    (by
      rw [hal, hes, hpd, aggP_allocs]
      simp only [List.map_cons, List.map_nil, hV.v6, hV.v8, hV.v9, hV.v33, hV.v98, hV.v107,
        hV.v116, hV.v188, hP, aggPtrsAt, gen_pow_eq_ofK]
      rfl)
    (fun q hq => by
      rw [hes, hpad, aggP_addrs] at hq
      simp at hq)
    ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · rw [hal] at h
    exact h
  · rw [hcalls, hal]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩,
        rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 36), σ (.n 0), σ (.n 33), σ (.n 2), σ (.n 8), σ (.n 3), σ (.n 9), σ (.n 1)] = _
        rw [hV.g36, hV.e0, hV.v33, hV.e2, hV.v8, hV.e3, hV.v9, hV.e1]
      · rw [(h1 rfl).1]; rfl
      · exact hV.grArgs
      · rw [(h2 rfl).1]; rfl
      · show [σ (.n 103), σ (.n 0), σ (.n 98), σ (.n 8), σ (.n 9), σ (.n 94), σ (.n 81)] = _
        rw [hV.g103, hV.e0, hV.v98, hV.v8, hV.v9, hV.v94, hV.v81]
      · rw [(h3 rfl).1]; rfl
      · exact hV.bsArgs
      · rw [(h4 rfl).1]; exact hV.bsRets
      · show [σ (.n 192), σ (.n 0), σ (.n 8), σ (.n 9), σ (.n 116), σ (.n 98), σ (.n 188),
          σ (.n 81)] = _
        rw [hV.g192, hV.e0, hV.v8, hV.v9, hV.v116, hV.v98, hV.v188, hV.v81]
      · rw [(h5 rfl).1]; rfl
    · intro q hq
      apply hmK
      simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hq ⊢
      clear * - hq
      tauto
    · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
      have hkL : k.Lin = Own ++ Lin := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
      rw [hkL] at hi
      obtain ⟨q, hq, hq1, hq2⟩ := hi
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (Or.inr (hown i ⟨q, hq, hq1, hq2⟩))
      · exact Or.inl (Or.inl ⟨q, hq, hq1, hq2⟩)
  · intro A hA
    rw [hal]
    rw [hes, B1.loadAddrs_straight σ _ aggP_straight] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    have hq' := of_decide_eq_true (List.all_eq_true.mp aggP_loads q hq)
    have zl := agg_zip m b0
    simp only [aggLoadSet, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hq'
    rcases hq' with ((((((((⟨i, hi, rfl⟩ | (rfl | rfl)) | rfl) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) |
      rfl) | rfl) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | rfl
    · refine ⟨axAbs m b0 + i, ?_, Or.inl (hz (s := 13 * (m + 1)) (x := axAbs m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 33)).limb 0 * addressOfIndex i = _
      rw [hV.v33]; exact limb0_gen_pow_mul _ _
    · refine ⟨axChain m b0 + 0, ?_, Or.inl (hz (s := 2 * (m + 1)) (x := axChain m b0)
        (by rw [zl]; simp) (by omega) (by omega))⟩
      show (σ (.n 98)).limb 0 * addressOfIndex 0 = _
      rw [hV.v98]; exact limb0_gen_pow_mul _ _
    · refine ⟨axChain m b0 + 1, ?_, Or.inl (hz (s := 2 * (m + 1)) (x := axChain m b0)
        (by rw [zl]; simp) (by omega) (by omega))⟩
      show (σ (.n 98)).limb 0 * addressOfIndex 1 = _
      rw [hV.v98]; exact limb0_gen_pow_mul _ _
    · refine ⟨axW m b0 + 0, ?_, Or.inl (hz (s := m + 1) (x := axW m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 188)).limb 0 * addressOfIndex 0 = _
      rw [hV.v188]; exact limb0_gen_pow_mul _ _
    · have hcl2 : (aggOut cs h).cells.length = 24 := by
        simp [aggOut, DeferredClaim.cells, aggRun, bsRun_len, hrl]
      refine ⟨ds + k, ?_, Or.inr (Or.inl (regionL_of_mem hdst (by rw [hcl2]; exact hk)))⟩
      show (σ (.n 4)).limb 0 * addressOfIndex k = _
      rw [hV.e4]; exact limb0_gen_pow_mul _ _
    · refine ⟨axAbs m b0 + 13 * m + k, ?_, Or.inl (hz (s := 13 * (m + 1)) (x := axAbs m b0)
        (by rw [zl]; simp)
        (by omega) (by omega))⟩
      show (σ (.n 42)).limb 0 * addressOfIndex k = _
      rw [hV.p42, show P.absorb = gen ^ axAbs m b0 from rfl, ← pow_mul, ← pow_add,
        limb0_gen_pow_mul, Nat.mul_comm m 13]
    · refine ⟨axChain m b0 + 2 * m + 1, ?_, Or.inl (hz (s := 2 * (m + 1)) (x := axChain m b0)
        (by rw [zl]; simp)
        (by omega) (by omega))⟩
      show (σ (.n 105)).limb 0 * addressOfIndex 1 = _
      rw [hV.p105, show P.chain = gen ^ axChain m b0 from rfl, ← pow_mul, ← pow_add,
        limb0_gen_pow_mul, Nat.mul_comm m 2]
    · refine ⟨axW m b0 + m + 0, ?_, Or.inl (hz (s := m + 1) (x := axW m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 193)).limb 0 * addressOfIndex 0 = _
      rw [hV.p193, show P.w = gen ^ axW m b0 from rfl, ← pow_add, limb0_gen_pow_mul]
    · refine ⟨axPt m b0 + k, ?_, Or.inl (hz (s := 23) (x := axPt m b0) (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 107)).limb 0 * addressOfIndex k = _
      rw [hV.v107]; exact limb0_gen_pow_mul _ _
    · refine ⟨axPt1 m b0 + k, ?_, Or.inl (hz (s := 23) (x := axPt1 m b0) (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 116)).limb 0 * addressOfIndex k = _
      rw [hV.v116]; exact limb0_gen_pow_mul _ _
    · refine ⟨b0 + 0, ?_, Or.inl (hz (s := 47) (x := b0) (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 6)).limb 0 * addressOfIndex 0 = _
      rw [hV.v6]; exact limb0_gen_pow_mul _ _
end
end LeanVM.Guest.B1.Main
