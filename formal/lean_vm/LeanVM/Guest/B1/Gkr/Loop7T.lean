/-
  LeanVM.Guest.B1.Gkr.Loop7T

  `verify_bus_gkr_loop0`'s valid trees are chains of honest shape (`Budget.ChainHonest`): each
  iteration's node pins the bounds of the `verify_bus_gkr_loop0_loop0` it calls and which rounds it
  calls.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7In
public import LeanVM.Guest.B1.Gkr.VbgBound
public import LeanVM.Guest.Budget.Chain
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr_loop0`, of honest shape

Iteration `c` of `verify_bus_gkr_loop0` (from `g^c` below `g^M`) calls
`verify_bus_gkr_loop0_loop0` from `1` (`σ 63`) below `g^c`, entered iff `c ≠ 0` (`σ 62`), then
`gkr_rounds__L2`, or `gkr_rounds__L1` when `sh = 1` (`σ 67 = g^sh + 1`), then itself from
`g^(c+1)`, entered iff `c + 1 < M`.

* `ly7Q sh c σ`: those values; `ly7Csb σ`, `ly7Tl σ`: the body's calls and the tail call;
  `ly7Tsb sh c`: one `True` per body call.
* `ly7_calls`: the walk's calls are `ly7Csb σ ++ [ly7Tl σ]`.
* `ly7_chain`: every valid tree of iteration `c < M` is `ChainHonest … (M - c) c`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- What iteration `c`'s node pins: its counter `g^c`, `verify_bus_gkr_loop0_loop0`'s start `1` and
condition, and which last rounds are called. -/
def ly7Q (sh c : ℕ) (σ : Val) : Prop :=
  σ (.n 0) = gen ^ c ∧ σ (.n 63) = 1 ∧ σ (.n 62) = 1 + gen ^ c ∧ (σ (.n 67) = 0 ↔ sh = 0) ∧
    c < 2 ^ 62

/-- The last rounds' calls: `gkr_rounds__L2`, or `gkr_rounds__L1` at an odd depth. -/
noncomputable def ly7Rounds (σ : Val) : List Call :=
  if σ (.n 67) = 0 then (ly72.filterMap Main.Stmt.callS).map (Main.mkCall σ)
  else (ly71.filterMap Main.Stmt.callS).map (Main.mkCall σ)

/-- The body's calls: `verify_bus_gkr_loop0_loop0`, then the last rounds. -/
noncomputable def ly7Csb (σ : Val) : List Call :=
  (lyA.filterMap Main.Stmt.callS).map (Main.mkCall σ) ++ ly7Rounds σ

/-- The tail call. -/
noncomputable def ly7Tl (σ : Val) : Call :=
  Main.mkCall σ (some (.n 234), name% «verify_bus_gkr_loop0»,
    [.n 236, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10], [])

/-- One predicate per body call, none constraining. -/
def ly7Tsb (_sh _c : ℕ) : List (Tree → Prop) :=
  List.replicate 2 fun _ ↦ True

/-- **`verify_bus_gkr_loop0`'s calls**: the body's, then the tail. -/
theorem ly7_calls (σ : Val) {es : List Ev} {vs : List V} (hw : walk σ lyBody = .ret es vs) :
    calls es = ly7Csb σ ++ [ly7Tl σ] := by
  rw [ly_walk σ, Out.ret.injEq] at hw
  rw [← hw.1]
  simp only [calls, List.filterMap_append]
  have hA := (Main.straight_parts σ lyA lyA_straight).2.2.2
  have hB := (Main.straight_parts σ lyB lyB_straight).2.2.2
  have h2 := (Main.straight_parts σ ly72 ly72_straight).2.2.2
  have h1 := (Main.straight_parts σ ly71 ly71_straight).2.2.2
  simp only [calls] at hA hB h2 h1
  rw [hA, hB, lyB_calls]
  simp only [List.filterMap_cons, Ev.call?]
  by_cases e : σ (.n 67) = 0
  · simp only [e, ↓reduceIte, h2]
    simp [ly7Csb, ly7Rounds, ly7Tl, e, List.append_assoc]
  · simp only [e, ↓reduceIte, h1]
    simp [ly7Csb, ly7Rounds, ly7Tl, e, List.append_assoc]

theorem kidsValid_split {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {c : Call} {ks : List Tree}, Tree.KidsValid P rd σ (cs ++ [c]) ks →
      ∃ ks' k, ks = ks' ++ [k] ∧ ks'.length = cs.length ∧
        (c.taken = true → k.Valid P rd (c.args.map σ) (c.rets.map σ)) ∧ k.name = c.f
  | [], c, ks, h => by
    match ks, h with
    | [k], ⟨hn, hk, _⟩ =>
      refine ⟨[], k, rfl, rfl, fun ht ↦ ?_, hn⟩
      rw [ite_eq_left ht] at hk; exact hk
  | a :: cs, c, ks, h => by
    match ks, h with
    | k :: ks, ⟨_, _, hks⟩ =>
      obtain ⟨ks', k', rfl, hl, h1, h2⟩ := kidsValid_split hks
      exact ⟨k :: ks', k', rfl, by simp [hl], h1, h2⟩

theorem bufsOkKids_last {P : Core.Program} : ∀ {ks : List Tree} {k : Tree},
    Tree.BufsOkKids P (ks ++ [k]) → k.BufsOk P
  | [], _, h => h.1
  | _ :: _, _, h => bufsOkKids_last h.2

theorem kidsT_true_last : ∀ {cs : List Call} {Ts : List (Tree → Prop)} {ks : List Tree} {c : Call}
    {T : Tree → Prop} {k : Tree}, cs.length = Ts.length → ks.length = cs.length →
    (∀ T' ∈ Ts, ∀ t, T' t) → (c.taken = true → T k) → KidsT (cs ++ [c]) (Ts ++ [T]) (ks ++ [k])
  | [], [], [], _, _, _, _, _, _, h => ⟨h, trivial⟩
  | _ :: _, _ :: _, _ :: _, _, _, _, hl, hk, hT, h =>
    ⟨fun _ ↦ hT _ List.mem_cons_self _, kidsT_true_last (by simpa using hl) (by simpa using hk)
      (fun T' hT' ↦ hT T' (List.mem_cons_of_mem _ hT')) h⟩
  | [], _ :: _, _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _, _ => by simp at hl
  | [], [], _ :: _, _, _, _, _, hk, _, _ => by simp at hk
  | _ :: _, _ :: _, [], _, _, _, _, hk, _, _ => by simp at hk

theorem tb_gen_pow_add_eq_zero {a b : ℕ} (ha : a < 2 ^ 62) (hb : b < 2 ^ 62) :
    gen ^ a + gen ^ b = 0 ↔ a = b := by
  constructor
  · intro h
    exact gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h)
  · rintro rfl; exact e_add_self _

/-- **`verify_bus_gkr_loop0`'s valid trees are chains of honest shape**: iteration `c < M` runs
`M - c` iterations, each pinning `ly7Q`. -/
theorem ly7_chain {rd : Reader} {layers tabs pts rounds u stream gmu : E} {sh M : ℕ}
    (hsh2 : sh < 2) (hM : 2 * M + 2 < 2 ^ 62) :
    ∀ n c (t : Tree) (rets : List E), c + n = M → 0 < n → t.name = name% «verify_bus_gkr_loop0» →
      t.Valid coreProgram rd [gen ^ c, gen ^ M, gen ^ (2 - sh), layers, tabs, pts, rounds, u,
        gen ^ sh, stream, gmu] rets →
      t.BufsOk coreProgram →
      Budget.ChainHonest coreProgram name% «verify_bus_gkr_loop0» (ly7Q sh) ly7Csb ly7Tl (fun _ ↦
          []) (ly7Tsb sh)
        n c t := by
  obtain ⟨fn, hf, hpar, hbody⟩ := lyFound
  intro n
  induction n with
  | zero => intro _ _ _ _ h; omega
  | succ n ih =>
    intro c t rets hcn _ hname hv hb
    cases t with
    | phantom => exact hv.elim
    | node f σ bufs kids =>
      simp only [Tree.name] at hname
      subst hname
      obtain ⟨fn', hf', hp, es, vs, hw, hr, hes, hk⟩ := hv
      rw [hf, Option.some.injEq] at hf'
      subst hf'
      rw [hpar] at hp
      have hp' : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
          σ (.n 8), σ (.n 9), σ (.n 10)] = [gen ^ c, gen ^ M, gen ^ (2 - sh), layers, tabs, pts,
          rounds, u, gen ^ sh, stream, gmu] := hp
      simp only [List.cons.injEq, and_true] at hp'
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp'
      rw [hbody] at hw
      -- the body holds of `σ`
      have hH : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ lyBody True (fun _ ↦ True) :=
        holdsList_of_walk lyBody (by
          rw [hw]
          exact ⟨fun e he ↦ ⟨hes e he, fun _ _ _ _ ↦ trivial⟩, trivial⟩)
      rw [lyBody_eq, holdsList_append] at hH
      have hP : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ lyPre True (fun _ ↦ True) := hH
      have a := fun n a heq ↦ tb_holds_atom lyPre_noRet hP n a heq
      have c61 := a 45 (.const (.n 61) (word 1 0)) (by decide +kernel)
      have a62 := a 46 (.add (.n 62) (.n 61) (.n 0)) (by decide +kernel)
      have c63 := a 47 (.const (.n 63) (word 1 0)) (by decide +kernel)
      have c66 := a 51 (.const (.n 66) (word 1 0)) (by decide +kernel)
      have a67 := a 52 (.add (.n 67) (.n 8) (.n 66)) (by decide +kernel)
      have c232 := a 179 (.const (.n 232) (word 2 0)) (by decide +kernel)
      have m233 := a 180 (.mul (.n 233) (.n 0) (.n 232)) (by decide +kernel)
      have a234 := a 181 (.add (.n 234) (.n 233) (.n 1)) (by decide +kernel)
      have c235 := a 182 (.const (.n 235) (word 2 0)) (by decide +kernel)
      have m236 := a 183 (.mul (.n 236) (.n 0) (.n 235)) (by decide +kernel)
      simp only [Atom.Holds] at c61 a62 c63 c66 a67 c232 m233 a234 c235 m236
      have hc : c < M := by omega
      have e67 : σ (.n 67) = 0 ↔ sh = 0 := by
        rw [a67, c66, h8, tb_word_one, ← pow_zero gen, tb_gen_pow_add_eq_zero (by omega) (by omega)]
      have e236 : σ (.n 236) = gen ^ (c + 1) := by rw [m236, c235, h0, tb_word_gen, pow_succ]
      have e234 : σ (.n 234) = gen ^ (c + 1) + gen ^ M := by
        rw [a234, m233, c232, h0, h1, tb_word_gen, pow_succ]
      have hQ : ly7Q sh c σ :=
        ⟨h0, by rw [c63, tb_word_one], by rw [a62, c61, tb_word_one, h0], e67, by omega⟩
      have hcalls := ly7_calls σ hw
      rw [hcalls] at hk
      obtain ⟨ks', k, rfl, hkl, hkv, hkn⟩ := kidsValid_split hk
      have hlen : (ly7Csb σ).length = (ly7Tsb sh c).length := by
        have hA : (lyA.filterMap Main.Stmt.callS).length = 1 := by rw [lyA_calls]; rfl
        have h2' : (ly72.filterMap Main.Stmt.callS).length = 1 := by decide +kernel
        have h1' : (ly71.filterMap Main.Stmt.callS).length = 1 := by decide +kernel
        simp only [ly7Csb, ly7Rounds, ly7Tsb, List.length_append, List.length_map, hA,
          List.length_replicate]
        split <;> simp [h2', h1']
      refine ⟨σ, ks' ++ [k], ?_, hQ, fun fn'' es' vs' hf'' hw' ↦ ?_, hlen, ?_⟩
      · have hbufs := hb.1
        rw [hbufs, events_node hf (by rw [hbody]; exact hw)]
        have hal : allocs σ es = [] := by
          rw [ly_walk σ, Out.ret.injEq] at hw
          rw [← hw.1]
          have hA' := (Main.straight_parts σ lyA lyA_straight).2.1
          have hB' := (Main.straight_parts σ lyB lyB_straight).2.1
          have h2' := (Main.straight_parts σ ly72 ly72_straight).2.1
          have h1' := (Main.straight_parts σ ly71 ly71_straight).2.1
          have hA : lyA.filterMap Main.Stmt.allocSz = [] := by decide +kernel
          have hB : lyB.filterMap Main.Stmt.allocSz = [] := by decide +kernel
          have h2 : ly72.filterMap Main.Stmt.allocSz = [] := by decide +kernel
          have h1 : ly71.filterMap Main.Stmt.allocSz = [] := by decide +kernel
          simp only [allocs, hA, hB, h2, h1, List.map_nil] at hA' hB' h2' h1'
          simp only [allocs, List.filterMap_append, hA', hB', List.nil_append, List.append_nil,
            List.filterMap_cons, Ev.alloc?]
          split
          · exact h2'
          · exact h1'
        rw [hal]
      · rw [hf, Option.some.injEq] at hf''
        subst hf''
        rw [hbody] at hw'
        exact ly7_calls σ hw'
      · refine kidsT_true_last (by rw [hlen]) (by rw [hkl, hlen])
          (fun T' hT' t ↦ by simp only [ly7Tsb, List.mem_replicate] at hT'; rw [hT'.2]; trivial)
          (fun ht ↦ ?_)
        have ht' : σ (.n 234) ≠ 0 := by simpa [ly7Tl, Main.mkCall] using ht
        have hc1 : c + 1 ≠ M := fun h ↦ ht' (by rw [e234, h]; exact e_add_self _)
        have hn : 0 < n := by omega
        have hkv' := hkv ht
        simp only [ly7Tl, Main.mkCall, List.map_cons, List.map_nil] at hkv'
        rw [e236, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] at hkv'
        exact ih (c + 1) k _ (by omega) hn (by simpa [ly7Tl, Main.mkCall] using hkn) hkv'
          (bufsOkKids_last hb.2)

/-! ## The chain's words -/

/-- The body calls' bounds, by position: `verify_bus_gkr_loop0_loop0`'s, then `R` for the last
rounds. -/
noncomputable def ly7Wb (fs : String → ℕ) (K29 R : ℕ) (c : ℕ) (_σ : Val) : List ℕ :=
  [ly7W29 fs K29 c, R]

theorem ly7Rounds_eq (σ : Val) : ly7Rounds σ =
    [if σ (.n 67) = 0 then ⟨"gkr_rounds__L2", [.n 64, .n 68, .n 65, .n 4, .n 9], [.n 69], true⟩
      else ⟨"gkr_rounds__L1", [.n 64, .n 70, .n 65, .n 4, .n 9], [.n 71], true⟩] := by
  unfold ly7Rounds
  split <;> rfl

theorem ly7Csb_eq (σ : Val) : ly7Csb σ =
    ⟨name% «verify_bus_gkr_loop0_loop0», [.n 63, .n 0, .n 56, .n 55, .n 4], [],
        decide (σ (.n 62) ≠ 0)⟩ ::
      ly7Rounds σ := by
  simp only [ly7Csb]
  rw [lyA_calls]
  rfl

theorem ly7Rounds_mem {σ : Val} {c : Call} (h : c ∈ ly7Rounds σ) :
    ∃ n ∈ grCounts, c.f = lName "gkr_rounds" n ∧ c.taken = true := by
  rw [ly7Rounds_eq, List.mem_singleton] at h
  subst h
  split
  · exact ⟨2, by simp [grCounts], rfl, rfl⟩
  · exact ⟨1, by simp [grCounts], rfl, rfl⟩

/-- **`verify_bus_gkr_loop0`'s chain's words**: within the iterations' bounds `ly7B` and the last
tail's frame, given `verify_bus_gkr_loop0_loop0`'s run's words (linear in its end's exponent, its
phantom frame once) and the rounds' bound `R`. -/
theorem ly7_total {P : Core.Program} {rd : Reader} (fs : String → ℕ) {sh K29 R : ℕ}
    (h29 : TotalLeOn P fs name% «verify_bus_gkr_loop0_loop0» LoopPre (fun a ↦ logG (a.getD 1 0) *
        K29 + fs name% «verify_bus_gkr_loop0_loop0»))
    (hR : ∀ n ∈ grCounts, TotalLe P fs (lName "gkr_rounds" n) (fun _ ↦ R)) :
    ∀ m c (t : Tree) args rets,
      Budget.ChainHonest P name% «verify_bus_gkr_loop0» (ly7Q sh) ly7Csb ly7Tl (fun _ ↦ []) (ly7Tsb
          sh) m c t →
      t.Valid P rd args rets → t.BufsOk P →
      t.total fs ≤ Budget.iterSum (ly7B fs K29 R) c m + fs name% «verify_bus_gkr_loop0» := by
  refine Budget.ChainHonest.total_le fs (ly7Wb fs K29 R) (ly7B fs K29 R)
    (fun σ ↦ rfl) (fun c σ _ ↦ ?_) (fun c σ hQ ↦ ?_) (fun c σ hQ i hi hW hu ↦ ?_)
    (fun c σ hQ i hi hT hW ht t rets hn hv hb _ ↦ ?_)
  · rw [ly7Wb, ly7Csb_eq, ly7Rounds_eq]; simp
  · simp only [ly7Wb, ly7B, List.sum_cons, List.sum_nil]
    omega
  · -- only `verify_bus_gkr_loop0_loop0`'s call can be skipped
    rcases i with _ | j
    · rw [List.getElem_of_eq (ly7Csb_eq σ) hi, List.getElem_cons_zero]
      simp only [ly7Wb, List.getElem_cons_zero, ly7W29]; omega
    · have e := List.getElem_of_eq (ly7Csb_eq σ) hi
      rw [e, List.getElem_cons_succ] at hu
      have hm := List.getElem_mem (l := ly7Rounds σ) (by rw [ly7Csb_eq] at hi; simpa using hi)
      obtain ⟨-, -, -, htk⟩ := ly7Rounds_mem hm
      rw [htk] at hu; exact absurd hu (by simp)
  · obtain ⟨e0, e63, e62, -, hcb⟩ := hQ
    have e := List.getElem_of_eq (ly7Csb_eq σ) hi
    rcases i with _ | j
    · -- `verify_bus_gkr_loop0_loop0`
      rw [e, List.getElem_cons_zero] at ht hn hv
      simp only [decide_eq_true_eq] at ht
      have hc4 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · exfalso; apply ht; rw [e62, h0, pow_zero, e_add_self]
        · exact h0
      simp only [List.map_cons, List.map_nil, e63, e0] at hv
      have hb' := h29 rd t _ rets hn (loopPre_gen hc4 (by omega) _) hv hb
      simp only [List.getD_cons_succ, List.getD_cons_zero, gen_pow_eq_ofK,
        logG_spec (show c < 2 ^ 64 - 1 by omega)] at hb'
      simp only [ly7Wb, List.getElem_cons_zero, ly7W29]; omega
    · rw [e, List.getElem_cons_succ] at hn hv
      have hW' : (ly7Wb fs K29 R c σ)[j + 1] = R := by
        have hj : j = 0 := by
          rw [ly7Csb_eq, ly7Rounds_eq] at hi
          simp only [List.length_cons, List.length_nil] at hi
          omega
        subst hj; rfl
      rw [hW']
      have hm := List.getElem_mem (l := ly7Rounds σ) (by rw [ly7Csb_eq] at hi; simpa using hi)
      obtain ⟨n', hn', hf, -⟩ := ly7Rounds_mem hm
      rw [hf] at hn; exact hR n' hn' rd t _ rets hn hv hb

end
end LeanVM.Guest.B1.Tables
