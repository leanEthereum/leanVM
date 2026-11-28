/-
  LeanVM.Guest.B1.VsC.Os.LeftLeaves

  `open_stacked`'s named callees placed, from their meanings on one memory and their fixed loads.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftChain
public import LeanVM.Guest.B1.VsC.Os.KindsA
public import LeanVM.Guest.B1.VsC.Os.IsZeroA
public import LeanVM.Guest.B1.Whir.SqLoop

/-!
# The named callees, placed

The body holds at the callee relation `osCmin`: a named callee `f` of kind `K` satisfies its
meaning `K.Pre rd0 a r` on the memory `rd0` the node's valuation was taken on, and its loads are
fixed (`OsFixedA`): the words at each array `K.spec` names are the same on every memory with the
node's facts (`OsNF`: the cursor's words, the window tables, the buffers). So on every such memory
it reads what it read on `rd0`, and its arrays lie in every cell set `S` whose restriction of `rd0`
keeps the node's facts (`arrIn_of_fixed`, through `restrict`).

`osLeaf_msg`, `osLeaf_spf`, `osLeaf_tail`, `osLeaf_ffm`, `osLeaf_iz`: each kind's `LeafAtA` at `S`
on `OsNF`, by `opening_message_leafA`, `squeeze_point_from_leafA`, `opening_tail_round_leafA`,
`fold_final_msg_leafA`, `is_zero_leafA`. `osKindOf_om`, `osKindOf_spf`, `osKindOf_ffm`,
`osKindOf_tail`: the deployed names' kinds.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The node's memory facts a named callee's loads are fixed on. -/
def OsNF (c : OsCfg) (b : ℕ) (own : List (List E)) (cur tabs : E) (xs : List E) (rd : Reader) : Prop :=
  ReadsAt rd cur xs ∧ WinTabs rd tabs ∧ OsMemA rd c b own

theorem readsAt_uniq {rd : Reader} {p : E} {l1 l2 : List E} (h1 : ReadsAt rd p l1) (h2 : ReadsAt rd p l2)
    (hl : l1.length = l2.length) : l1 = l2 :=
  List.ext_getElem hl fun k hk1 hk2 ↦ loadHolds_unique (h1 k hk1) (h2 k hk2)

/-- **A fixed array lies in every cell set keeping the node's facts.** -/
theorem arrIn_of_fixed {NF : Reader → Prop} {S : ℕ → Prop} {rd0 : Reader} (hS : NF (restrict rd0 S)) {p : E}
    {ws : List E} (h : ∀ rd, NF rd → ReadsAt rd p ws) : ArrIn S p ws.length := fun off ho =>
  restrict_supp (h _ hS off ho).2

/-- **A fixed array holds on every memory what it holds on one.** -/
theorem fixed_eq {NF : Reader → Prop} {rd0 : Reader} (h0 : NF rd0) {p : E} {ws ws' : List E}
    (h : ∀ rd, NF rd → ReadsAt rd p ws) (h' : ReadsAt rd0 p ws') (hl : ws'.length = ws.length) :
    ∀ rd, NF rd → ReadsAt rd p ws' := fun rd hrd => by
  rw [readsAt_uniq h' (h rd0 h0) hl]
  exact h rd hrd

theorem readsAt_snoc {rd : Reader} {p : E} {xs : List E} {v : E} (h : ReadsAt rd p xs)
    (hv : LoadHolds rd p xs.length v) : ReadsAt rd p (xs ++ [v]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < xs.length
  · rw [List.getElem_append_left hk']
    exact h k hk'
  · have e : k = xs.length := by omega
    subst e
    rw [List.getElem_append_right (Nat.le_refl _)]
    simpa using hv

/-- The fixed words of a callee's spec entry, on `OsNF`. -/
theorem fixedA_at {c : OsCfg} {b : ℕ} {own : List (List E)} {cur tabs : E} {xs : List E} {K : OsKind} {a : List E}
    (h : OsFixedA c b own cur tabs xs K a) {q : ℕ × ℕ} (hq : q ∈ K.spec) :
    ∃ ws : List E, ws.length = q.2 ∧ ∀ rd, OsNF c b own cur tabs xs rd → ReadsAt rd (a.getD q.1 0) ws := by
  obtain ⟨ws, hl, hw⟩ := h q hq
  exact ⟨ws, hl, fun rd hrd => hw rd hrd.1 hrd.2.1 hrd.2.2⟩

theorem leafAtA_pre {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {args rets : List E} {R : ℕ → Prop} {Pre Pre' : Reader → Prop} {Post : Reader → Tree → Prop}
    (h : LeafAtA fs al cert k f args rets R (fun _ => True) Pre Post) (hP : ∀ rd, Pre' rd → Pre rd) :
    LeafAtA fs al cert k f args rets R (fun _ => True) Pre' Post := fun fp c hc =>
  (h fp c hc).mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h)

/-! ## The deployed names' kinds -/

set_option maxRecDepth 100000 in
theorem osKindOf_om_all : omDeployed.all (fun p => osKindOf (omName p) == some (.msg p.1 p.2)) = true := by
  decide +kernel

theorem osKindOf_om {p : ℕ × ℕ} (hp : p ∈ omDeployed) : osKindOf (omName p) = some (.msg p.1 p.2) := by
  have := List.all_eq_true.mp osKindOf_om_all p hp
  simpa using this

set_option maxRecDepth 100000 in
theorem osKindOf_spf_all : spfDeployed.all (fun n => osKindOf (spfName n) == some (.spf n)) = true := by
  decide +kernel

theorem osKindOf_spf {n : ℕ} (hn : n ∈ spfDeployed) : osKindOf (spfName n) = some (.spf n) := by
  have := List.all_eq_true.mp osKindOf_spf_all n hn
  simpa using this

set_option maxRecDepth 100000 in
theorem osKindOf_ffm_all : foldFinalMsgNames.all (fun p => osKindOf p.1 == some (.ffm p.2)) = true := by
  decide +kernel

theorem osKindOf_ffm {p : String × ℕ} (hp : p ∈ foldFinalMsgNames) : osKindOf p.1 = some (.ffm p.2) := by
  have := List.all_eq_true.mp osKindOf_ffm_all p hp
  simpa using this

theorem osKindOf_tail : osKindOf "opening_tail_round" = some .tail := by decide +kernel

/-! ## Each kind placed -/

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {c : OsCfg} {b : ℕ}
  {own : List (List E)} {cur tabs : E} {xs : List E} {rd0 : Reader} {S : ℕ → Prop}

/-- **`opening_message__L{n}_L1` placed** from its meaning on `rd0` and its fixed loads. -/
theorem osLeaf_msg (kd : ℕ) {n : ℕ} (hn : (n, 1) ∈ omDeployed) {a r : List E}
    (hpre : MeaningOpeningMessage n 1 rd0 a r) (hfx : OsFixedA c b own cur tabs xs (.msg n 1) a)
    (h0 : OsNF c b own cur tabs xs rd0) (hS : OsNF c b own cur tabs xs (restrict rd0 S)) :
    LeafAtA fs al cert kd (omName (n, 1)) a r S (fun _ => True) (OsNF c b own cur tabs xs) PostQuiet := by
  obtain ⟨f0, f1, f2, f3, f4, cu, out, rfl⟩ : ∃ f0 f1 f2 f3 f4 cu out, a = [f0, f1, f2, f3, f4, cu, out] := by
    rcases a with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, _ | ⟨cu, _ | ⟨out, _ | ⟨x, a⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl⟩ | exact absurd hpre (by unfold MeaningOpeningMessage; simp)
  obtain ⟨ms, hl, hc, ho, nn, hnn, hr⟩ := hpre
  obtain ⟨w1, hl1, hw1⟩ := fixedA_at hfx (q := (5, n + 1)) (by simp [OsKind.spec, msgSpec])
  obtain ⟨w2, hl2, hw2⟩ := fixedA_at hfx (q := (6, n)) (by simp [OsKind.spec, msgSpec])
  have hc' : ReadsAt rd0 cu (ms ++ [nn]) := readsAt_snoc hc (by rw [hl]; exact hnn rfl)
  have hw1' := fixed_eq h0 hw1 hc' (by simp [hl, hl1])
  have hw2' := fixed_eq h0 hw2 ho (by rw [hl, hl2])
  have hr' : r = VsC.omRets f0 f1 f2 f3 f4 cu ms nn := by
    rw [hr, VsC.omRets, hl]
    rfl
  rw [hr']
  refine leafAtA_pre (opening_message_leafA fs al cert kd hn f0 f1 f2 f3 f4 cu out nn ms hl ?_ ?_)
    fun rd hrd => ⟨hw1' rd hrd, hw2' rd hrd⟩
  · have := arrIn_of_fixed hS hw1
    rwa [hl1] at this
  · have := arrIn_of_fixed hS hw2
    rwa [hl2] at this

/-- **`squeeze_point_from__L{n}` placed** from its meaning on `rd0` and its fixed loads. -/
theorem osLeaf_spf (kd : ℕ) {n : ℕ} (hn : n ∈ spfDeployed) {a r : List E}
    (hpre : MeaningSqueezePointFrom n rd0 a r) (hfx : OsFixedA c b own cur tabs xs (.spf n) a)
    (h0 : OsNF c b own cur tabs xs rd0) (hS : OsNF c b own cur tabs xs (restrict rd0 S)) :
    LeafAtA fs al cert kd (spfName n) a r S (fun _ => True) (OsNF c b own cur tabs xs) PostQuiet := by
  obtain ⟨f0, f1, f2, f3, f4, first, point, rfl⟩ : ∃ f0 f1 f2 f3 f4 first point,
      a = [f0, f1, f2, f3, f4, first, point] := by
    rcases a with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, _ | ⟨cu, _ | ⟨out, _ | ⟨x, a⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl⟩ | exact absurd hpre (by unfold MeaningSqueezePointFrom; simp)
  obtain ⟨hp, hr⟩ := hpre
  obtain ⟨w1, hl1, hw1⟩ := fixedA_at hfx (q := (6, n)) (by simp [OsKind.spec, spfSpec])
  have h1 : 1 ≤ n := by
    simp only [spfDeployed, List.mem_map, List.mem_range] at hn
    omega
  have hw1' := fixed_eq h0 hw1 hp (by simp only [List.length_cons, squeezeN_length, hl1]; omega)
  rw [hr]
  refine leafAtA_pre (squeeze_point_from_leafA fs al cert kd hn f0 f1 f2 f3 f4 first point ?_)
    fun rd hrd => hw1' rd hrd
  have := arrIn_of_fixed hS hw1
  rwa [hl1] at this

/-- **`opening_tail_round` placed** from its meaning on `rd0` and its fixed loads. -/
theorem osLeaf_tail (kd : ℕ) {a r : List E}
    (hpre : MeaningOpeningTailRound rd0 a r) (hfx : OsFixedA c b own cur tabs xs .tail a)
    (h0 : OsNF c b own cur tabs xs rd0) (hS : OsNF c b own cur tabs xs (restrict rd0 S)) :
    LeafAtA fs al cert kd "opening_tail_round" a r S (fun _ => True) (OsNF c b own cur tabs xs) PostQuiet := by
  obtain ⟨f0, f1, f2, f3, f4, cu, claim, tb, rfl⟩ : ∃ f0 f1 f2 f3 f4 cu claim tb,
      a = [f0, f1, f2, f3, f4, cu, claim, tb] := by
    rcases a with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, _ | ⟨cu, _ | ⟨cl, _ | ⟨tb, _ | ⟨x, a⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      first | exact ⟨_, _, _, _, _, _, _, _, rfl⟩ | exact absurd hpre (by unfold MeaningOpeningTailRound; simp)
  obtain ⟨c0, c2, hc, hr⟩ := hpre
  obtain ⟨w1, hl1, hw1⟩ := fixedA_at hfx (q := (5, 2)) (by simp [OsKind.spec, tailSpec])
  have hw1' := fixed_eq h0 hw1 hc (by rw [hl1]; rfl)
  rw [hr]
  refine leafAtA_pre (opening_tail_round_leafA fs al cert kd f0 f1 f2 f3 f4 cu claim tb c0 c2 ?_)
    fun rd hrd => hw1' rd hrd
  have := arrIn_of_fixed hS hw1
  rwa [hl1] at this

/-- **`fold_final_msg__L{n}` placed** from its meaning on `rd0` and its fixed loads. -/
theorem osLeaf_ffm (kd : ℕ) {p : String × ℕ} (hp : p ∈ foldFinalMsgNames) {a r : List E}
    (hpre : MeaningFoldFinalMsg p.2 rd0 a r) (hfx : OsFixedA c b own cur tabs xs (.ffm p.2) a)
    (h0 : OsNF c b own cur tabs xs rd0) (hS : OsNF c b own cur tabs xs (restrict rd0 S)) :
    LeafAtA fs al cert kd p.1 a r S (fun _ => True) (OsNF c b own cur tabs xs) PostQuiet := by
  obtain ⟨msg, point, rfl⟩ : ∃ msg point, a = [msg, point] := by
    rcases a with _ | ⟨msg, _ | ⟨point, _ | ⟨x, a⟩⟩⟩ <;>
      first | exact ⟨_, _, rfl⟩ | exact absurd hpre (by unfold MeaningFoldFinalMsg; simp)
  obtain ⟨m, ps, hm, hps, hmr, hpr, hr⟩ := hpre
  obtain ⟨w1, hl1, hw1⟩ := fixedA_at hfx (q := (0, 2 ^ p.2)) (by simp [OsKind.spec, foldFinalSpec])
  obtain ⟨w2, hl2, hw2⟩ := fixedA_at hfx (q := (1, p.2)) (by simp [OsKind.spec, foldFinalSpec])
  have hw1' := fixed_eq h0 hw1 hmr (by rw [hm, hl1])
  have hw2' := fixed_eq h0 hw2 hpr (by rw [hps, hl2])
  rw [hr]
  refine leafAtA_pre (fold_final_msg_leafA fs al cert kd hp msg point m ps hm hps ?_ ?_)
    fun rd hrd => ⟨hw1' rd hrd, hw2' rd hrd⟩
  · have := arrIn_of_fixed hS hw1
    rwa [hl1] at this
  · have := arrIn_of_fixed hS hw2
    rwa [hl2] at this

/-- **`is_zero` placed** from its meaning. -/
theorem osLeaf_iz (kd : ℕ) {a r : List E} (hpre : MeaningIsZero a r) (Pre : Reader → Prop) :
    LeafAtA fs al cert kd "is_zero" a r S (fun _ => True) Pre PostQuiet := by
  obtain ⟨w, rfl⟩ : ∃ w, a = [w] := by
    rcases a with _ | ⟨w, _ | ⟨x, a⟩⟩ <;>
      first | exact ⟨_, rfl⟩ | exact absurd hpre (by unfold MeaningIsZero; simp)
  change r = _ at hpre
  rw [hpre]
  exact is_zero_leafA kd w S Pre

end

end
end LeanVM.Guest.B1.VsC
