/-
  LeanVM.Guest.B1.Gkr.Loop7T

  `verify_bus_gkr_loop0`'s valid trees are chains of honest shape (`Budget.ChainHonest`): each iteration's node
  pins the bounds of the `verify_bus_gkr_loop0_loop0` it calls and which rounds it calls.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7In
public import LeanVM.Guest.B1.Gkr.VbgBound
public import LeanVM.Guest.Budget.Chain
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr_loop0`, of honest shape

Iteration `c` of `verify_bus_gkr_loop0` (from `g^c` below `g^M`, layer `L = 2c + 2 - sh`, layer index
`k = c + 1 - sh`) calls `verify_bus_gkr_loop0_loop0` from `1` (`σ 57`) below `g^(k/4)` (`σ 53`, the slot's `half`),
then `gkr_rounds__L{2r}` at the slot's `parity = g^r`, `r = k % 4` (`σ 54`, a dispatch), and
`gkr_rounds__L1` when `sh = 1` (`σ 65 = g^sh + 1`), then itself from `g^(c+1)`, entered iff
`c + 1 < M`.

* `ly7Q sh c σ`: those values; `ly7Csb σ`, `ly7Tl σ`: the body's calls and the tail call;
  `ly7Tsb sh c`: one `True` per body call.
* `ly7_calls`: the walk's calls are `ly7Csb σ ++ [ly7Tl σ]`.
* `ly7_chain`: on a memory whose slots hold `half` and `parity` (`Ly7Mem`), every valid tree of
  iteration `c < M` is `ChainHonest … (M - c) c`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The dispatch's index at `parity = σ 54`: `r` at `g^r`, `r < 4`. -/
noncomputable def ly7Dr (σ : Val) : ℕ :=
  if σ (.n 54) = gen ^ 1 then 1 else if σ (.n 54) = gen ^ 2 then 2
  else if σ (.n 54) = gen ^ 3 then 3 else 0

theorem ly7Dr_eq {σ : Val} {r : ℕ} (hr : r < 4) (h : σ (.n 54) = gen ^ r) : ly7Dr σ = r := by
  have ne : ∀ a b : ℕ, a < 4 → b < 4 → a ≠ b → (gen ^ a : E) ≠ gen ^ b := fun a b ha hb hab e ↦
    hab (gen_pow_inj (by omega) (by omega) e)
  unfold ly7Dr
  interval_cases r <;> simp only [h, ne 0 1 (by omega) (by omega) (by omega),
    ne 0 2 (by omega) (by omega) (by omega), ne 0 3 (by omega) (by omega) (by omega),
    ne 2 1 (by omega) (by omega) (by omega), ne 3 1 (by omega) (by omega) (by omega),
    ne 3 2 (by omega) (by omega) (by omega), ↓reduceIte]

/-- What iteration `c`'s node pins: `verify_bus_gkr_loop0_loop0`'s end `g^(k/4)`, start `1` and condition, the
parity `g^(k % 4)`, `k = c + 1 - sh`, and whether the odd-depth round is called. -/
def ly7Q (sh c : ℕ) (σ : Val) : Prop :=
  σ (.n 53) = gen ^ ((c + 1 - sh) / 4) ∧ σ (.n 57) = 1 ∧
    σ (.n 56) = 1 + gen ^ ((c + 1 - sh) / 4) ∧ σ (.n 54) = gen ^ ((c + 1 - sh) % 4) ∧
    (σ (.n 65) = 0 ↔ sh = 0) ∧ c < 2 ^ 62

/-- The body's calls: `verify_bus_gkr_loop0_loop0`, the dispatched rounds, then the odd round when taken. -/
noncomputable def ly7Csb (σ : Val) : List Call :=
  (lyA.filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
    [⟨lyRn (ly7Dr σ), [.n 61, .n 62, .n 4], [.n 63], true⟩] ++
    (if σ (.n 65) = 0 then [] else (ly73.filterMap Main.Stmt.callS).map (Main.mkCall σ))

/-- The tail call. -/
noncomputable def ly7Tl (σ : Val) : Call :=
  Main.mkCall σ (some (.n 236), name% «verify_bus_gkr_loop0»,
    [.n 238, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], [])

/-- One predicate per body call, none constraining. -/
def ly7Tsb (sh _c : ℕ) : List (Tree → Prop) :=
  List.replicate (2 + (if sh = 1 then 1 else 0)) fun _ ↦ True

/-- **`verify_bus_gkr_loop0`'s calls**: the body's, then the tail, at `parity = g^r`. -/
theorem ly7_calls (σ : Val) {r : ℕ} (hr : r < 4) (h54 : σ (.n 54) = gen ^ r) {es : List Ev}
    {vs : List V} (hw : walk σ lyBody = .ret es vs) :
    calls es = ly7Csb σ ++ [ly7Tl σ] := by
  rw [ly_walk σ hr (by rw [h54, gen_pow_eq_ofK]), Out.ret.injEq] at hw
  rw [← hw.1]
  simp only [calls, List.filterMap_append]
  have hA := (Main.straight_parts σ lyA lyA_straight).2.2.2
  have hB := (Main.straight_parts σ lyB lyB_straight).2.2.2
  have h65 := calls_lyBr (σ := σ) (c := .n 65) ly73_straight
  simp only [calls] at hA hB h65
  rw [hA, hB, lyB_calls]
  simp only [List.filterMap_cons, Ev.call?]
  rw [show (lyBr σ (.n 65) ly73).filterMap Ev.call? = _ from h65]
  simp [ly7Csb, ly7Tl, List.append_assoc, ly7Dr_eq hr h54]

/-- The memory iteration `c < M` reads its bounds from: the slots' `half` and `parity`. -/
def Ly7Mem (rd : Reader) (layers : E) (sh M : ℕ) : Prop :=
  ∀ j < M, LoadHolds rd layers (13 * (2 * j + 2 - sh) + 11) (gen ^ ((j + 1 - sh) / 4)) ∧
    LoadHolds rd layers (13 * (2 * j + 2 - sh) + 12) (gen ^ ((j + 1 - sh) % 4))

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

/-- **`verify_bus_gkr_loop0`'s valid trees are chains of honest shape**: iteration `c < M`, on a memory holding
its bounds' words, runs `M - c` iterations, each pinning `ly7Q`. -/
theorem ly7_chain {rd : Reader} {layers tabs rounds claim gmu kmn : E} {sh M : ℕ} (hsh2 : sh < 2)
    (hM : 2 * M + 2 < 2 ^ 62) (hmem : Ly7Mem rd layers sh M) :
    ∀ n c (t : Tree) (rets : List E), c + n = M → 0 < n → t.name = name% «verify_bus_gkr_loop0» →
      t.Valid coreProgram rd [gen ^ c, gen ^ M, gen ^ (2 - sh), layers, tabs, rounds, claim,
        gen ^ sh, gmu, kmn] rets →
      t.BufsOk coreProgram →
      Budget.ChainHonest coreProgram name% «verify_bus_gkr_loop0» (ly7Q sh) ly7Csb ly7Tl (fun _ ↦ []) (ly7Tsb sh)
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
          σ (.n 8), σ (.n 9)] = [gen ^ c, gen ^ M, gen ^ (2 - sh), layers, tabs, rounds, claim,
          gen ^ sh, gmu, kmn] := hp
      simp only [List.cons.injEq, and_true] at hp'
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hp'
      rw [hbody] at hw
      -- the body holds of `σ`
      have hH : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ lyBody True (fun _ ↦ True) :=
        holdsList_of_walk lyBody (by
          rw [hw]
          exact ⟨fun e he ↦ ⟨hes e he, fun _ _ _ _ ↦ trivial⟩, trivial⟩)
      rw [lyBody_eq, holdsList_append] at hH
      have hP : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ lyPre True (fun _ ↦ True) := hH
      have a := fun n a heq ↦ tb_holds_atom lyPre_noRet hP n a heq
      have m10 := a 0 (.mul (.n 10) (.n 0) (.n 0)) (by decide +kernel)
      have m11 := a 1 (.mul (.n 11) (.n 10) (.n 2)) (by decide +kernel)
      have m12 := a 2 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)
      have m13 := a 3 (.mul (.n 13) (.n 12) (.n 11)) (by decide +kernel)
      have m14 := a 4 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)
      have m15 := a 5 (.mul (.n 15) (.n 14) (.n 14)) (by decide +kernel)
      have m16 := a 6 (.mul (.n 16) (.n 15) (.n 11)) (by decide +kernel)
      have m17 := a 7 (.mul (.n 17) (.n 3) (.n 16)) (by decide +kernel)
      have l53 := a 38 (.load (.n 53) (.n 17) 11) (by decide +kernel)
      have l54 := a 39 (.load (.n 54) (.n 17) 12) (by decide +kernel)
      have c55 := a 40 (.const (.n 55) (word 1 0)) (by decide +kernel)
      have a56 := a 41 (.add (.n 56) (.n 55) (.n 53)) (by decide +kernel)
      have c57 := a 42 (.const (.n 57) (word 1 0)) (by decide +kernel)
      have c64 := a 50 (.const (.n 64) (word 1 0)) (by decide +kernel)
      have a65 := a 51 (.add (.n 65) (.n 7) (.n 64)) (by decide +kernel)
      have c234 := a 186 (.const (.n 234) (word 2 0)) (by decide +kernel)
      have m235 := a 187 (.mul (.n 235) (.n 0) (.n 234)) (by decide +kernel)
      have a236 := a 188 (.add (.n 236) (.n 235) (.n 1)) (by decide +kernel)
      have c237 := a 189 (.const (.n 237) (word 2 0)) (by decide +kernel)
      have m238 := a 190 (.mul (.n 238) (.n 0) (.n 237)) (by decide +kernel)
      simp only [Atom.Holds] at m10 m11 m12 m13 m14 m15 m16 m17 l53 l54 c55 a56 c57 c64 a65
      simp only [Atom.Holds] at c234 m235 a236 c237 m238
      have hc : c < M := by omega
      obtain ⟨hhalf, hpar'⟩ := hmem c hc
      set L := 2 * c + 2 - sh with hL
      have e10 : σ (.n 10) = gen ^ (2 * c) := by rw [m10, h0, ← pow_add]; ring_nf
      have e11 : σ (.n 11) = gen ^ L := by
        rw [m11, e10, h2, ← pow_add, show 2 * c + (2 - sh) = L by omega]
      have e17 : σ (.n 17) = layers * gen ^ (13 * L) := by
        rw [m17, h3, m16, m15, m14, m13, m12, e11, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
          ← pow_add]
        ring_nf
      rw [e17, tb_loadHolds_mul_gen_pow] at l53 l54
      have e53 := tb_loadHolds_unique l53 hhalf
      have e54 := tb_loadHolds_unique l54 hpar'
      have e65 : σ (.n 65) = 0 ↔ sh = 0 := by
        rw [a65, c64, h7, tb_word_one, ← pow_zero gen, tb_gen_pow_add_eq_zero (by omega) (by omega)]
      have e238 : σ (.n 238) = gen ^ (c + 1) := by rw [m238, c237, h0, tb_word_gen, pow_succ]
      have e236 : σ (.n 236) = gen ^ (c + 1) + gen ^ M := by
        rw [a236, m235, c234, h0, h1, tb_word_gen, pow_succ]
      have hQ : ly7Q sh c σ :=
        ⟨e53, by rw [c57, tb_word_one], by rw [a56, c55, tb_word_one, e53], e54, e65, by omega⟩
      have hr4 : (c + 1 - sh) % 4 < 4 := Nat.mod_lt _ (by omega)
      have hcalls := ly7_calls σ hr4 e54 hw
      rw [hcalls] at hk
      obtain ⟨ks', k, rfl, hkl, hkv, hkn⟩ := kidsValid_split hk
      have hlen : (ly7Csb σ).length = (ly7Tsb sh c).length := by
        have hA : (lyA.filterMap Main.Stmt.callS).length = 1 := by rw [lyA_calls]; rfl
        have h65' : (ly73.filterMap Main.Stmt.callS).length = 1 := by decide +kernel
        simp only [ly7Csb, ly7Tsb, List.length_append, List.length_map, hA, List.length_replicate,
          List.length_singleton]
        by_cases hs : sh = 1
        · have : σ (.n 65) ≠ 0 := fun h ↦ by have := e65.mp h; omega
          simp [hs, this, h65']
        · have : σ (.n 65) = 0 := e65.mpr (by omega)
          simp [hs, this]
      refine ⟨σ, ks' ++ [k], ?_, hQ, fun fn'' es' vs' hf'' hw' ↦ ?_, hlen, ?_⟩
      · have hbufs := hb.1
        rw [hbufs, events_node hf (by rw [hbody]; exact hw)]
        have hal : allocs σ es = [] := by
          rw [ly_walk σ hr4 (by rw [e54, gen_pow_eq_ofK]), Out.ret.injEq] at hw
          rw [← hw.1]
          have hA' := (Main.straight_parts σ lyA lyA_straight).2.1
          have hB' := (Main.straight_parts σ lyB lyB_straight).2.1
          have hA : lyA.filterMap Main.Stmt.allocSz = [] := by decide +kernel
          have hB : lyB.filterMap Main.Stmt.allocSz = [] := by decide +kernel
          simp only [allocs, hA, hB, List.map_nil] at hA' hB'
          simp only [allocs, List.filterMap_append, hA', hB', List.nil_append, List.append_nil]
          by_cases e' : σ (.n 65) = 0 <;>
            simp [lyBr, e', Ev.alloc?, Main.slEvs, ly73]
        rw [hal]
      · rw [hf, Option.some.injEq] at hf''
        subst hf''
        rw [hbody] at hw'
        exact ly7_calls σ hr4 e54 hw'
      · refine kidsT_true_last (by rw [hlen]) (by rw [hkl, hlen])
          (fun T' hT' t ↦ by simp only [ly7Tsb, List.mem_replicate] at hT'; rw [hT'.2]; trivial)
          (fun ht ↦ ?_)
        have ht' : σ (.n 236) ≠ 0 := by simpa [ly7Tl, Main.mkCall] using ht
        have hc1 : c + 1 ≠ M := fun h ↦ ht' (by rw [e236, h]; exact e_add_self _)
        have hn : 0 < n := by omega
        have hkv' := hkv ht
        simp only [ly7Tl, Main.mkCall, List.map_cons, List.map_nil] at hkv'
        rw [e238, h1, h2, h3, h4, h5, h6, h7, h8, h9] at hkv'
        exact ih (c + 1) k _ (by omega) hn (by simpa [ly7Tl, Main.mkCall] using hkn) hkv'
          (bufsOkKids_last hb.2)

/-! ## The chain's words -/

/-- The rounds the body calls: `gkr_rounds__L{2r}` (the dispatch), `gkr_rounds__L1` at an odd
depth. -/
noncomputable def ly7Rounds (σ : Val) : List Call :=
  [⟨lyRn (ly7Dr σ), [.n 61, .n 62, .n 4], [.n 63], true⟩] ++
    (if σ (.n 65) = 0 then [] else [⟨"gkr_rounds__L1", [.n 66, .n 67, .n 4], [.n 68], true⟩])

/-- The body calls' bounds, by position: `verify_bus_gkr_loop0_loop0`'s, then `R` for each round. -/
noncomputable def ly7Wb (fs : String → ℕ) (K29 R sh : ℕ) (c : ℕ) (σ : Val) : List ℕ :=
  ly7W29 fs K29 (c + 1 - sh) :: List.replicate (ly7Rounds σ).length R

theorem ly73_calls (σ : Val) : (ly73.filterMap Main.Stmt.callS).map (Main.mkCall σ) =
    [⟨"gkr_rounds__L1", [.n 66, .n 67, .n 4], [.n 68], true⟩] := rfl

theorem ly7Csb_eq (σ : Val) : ly7Csb σ =
    ⟨name% «verify_bus_gkr_loop0_loop0», [.n 57, .n 53, .n 48, .n 46, .n 4], [], decide (σ (.n 56) ≠ 0)⟩ ::
      ly7Rounds σ := by
  simp only [ly7Csb, ly7Rounds, ly73_calls]
  rw [lyA_calls]
  rfl

theorem ly7Rounds_mem {σ : Val} {c : Call} (h : c ∈ ly7Rounds σ) :
    ∃ n ∈ grCounts, c.f = lName "gkr_rounds" n := by
  unfold ly7Rounds at h
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with rfl | h
  · have hr : ly7Dr σ < 4 := by unfold ly7Dr; split_ifs <;> omega
    exact ⟨2 * ly7Dr σ, (lyRn_eq hr).2, (lyRn_eq hr).1⟩
  · split at h
    · simp at h
    · simp only [List.mem_singleton] at h
      subst h
      exact ⟨1, by simp [grCounts], rfl⟩

theorem ly7Rounds_length {sh c : ℕ} {σ : Val} (hQ : ly7Q sh c σ) (hsh2 : sh < 2) :
    (ly7Rounds σ).length = 1 + (if sh = 1 then 1 else 0) := by
  obtain ⟨-, -, -, -, e65, -⟩ := hQ
  unfold ly7Rounds
  rw [List.length_append]
  congr 1
  by_cases hs : sh = 1
  · have : σ (.n 65) ≠ 0 := fun h ↦ by have := e65.mp h; omega
    simp [this, hs]
  · have : σ (.n 65) = 0 := e65.mpr (by omega)
    simp [this, hs]

/-- **`verify_bus_gkr_loop0`'s chain's words**: within the iterations' bounds `ly7B` and the last tail's
frame, given `verify_bus_gkr_loop0_loop0`'s run's words (linear in its end's exponent, its phantom frame once) and
the rounds' bound `R`. -/
theorem ly7_total {P : Core.Program} {rd : Reader} (fs : String → ℕ) {sh K29 R : ℕ}
    (hsh2 : sh < 2)
    (h29 : TotalLeOn P fs name% «verify_bus_gkr_loop0_loop0» LoopPre (fun a ↦ logG (a.getD 1 0) * K29 + fs name% «verify_bus_gkr_loop0_loop0»))
    (hR : ∀ n ∈ grCounts, TotalLe P fs (lName "gkr_rounds" n) (fun _ ↦ R)) :
    ∀ m c (t : Tree) args rets,
      Budget.ChainHonest P name% «verify_bus_gkr_loop0» (ly7Q sh) ly7Csb ly7Tl (fun _ ↦ []) (ly7Tsb sh) m c t →
      t.Valid P rd args rets → t.BufsOk P →
      t.total fs ≤ Budget.iterSum (ly7B fs K29 R sh) c m + fs name% «verify_bus_gkr_loop0» := by
  refine Budget.ChainHonest.total_le fs (ly7Wb fs K29 R sh) (ly7B fs K29 R sh)
    (fun σ ↦ rfl) (fun c σ _ ↦ ?_) (fun c σ hQ ↦ ?_) (fun c σ hQ i hi hW hu ↦ ?_)
    (fun c σ hQ i hi hT hW ht t rets hn hv hb _ ↦ ?_)
  · rw [ly7Wb, ly7Csb_eq]; simp
  · rw [ly7Wb, ly7B, List.sum_cons, List.sum_replicate, ly7Rounds_length hQ hsh2, smul_eq_mul]
    simp only [List.sum_nil, Nat.add_zero]
    omega
  · -- only `verify_bus_gkr_loop0_loop0`'s call can be skipped
    rcases i with _ | j
    · rw [List.getElem_of_eq (ly7Csb_eq σ) hi, List.getElem_cons_zero]
      simp only [ly7Wb, List.getElem_cons_zero, ly7W29]; omega
    · have e := List.getElem_of_eq (ly7Csb_eq σ) hi
      rw [e, List.getElem_cons_succ] at hu
      have hm := List.getElem_mem (l := ly7Rounds σ) (by rw [ly7Csb_eq] at hi; simpa using hi)
      have : ∀ c ∈ ly7Rounds σ, c.taken = true := by
        intro c hc
        unfold ly7Rounds at hc
        by_cases e' : σ (.n 65) = 0 <;> simp [e'] at hc <;>
          (try rcases hc with rfl | rfl) <;> rfl
      rw [this _ hm] at hu; exact absurd hu (by simp)
  · obtain ⟨e53, e57, e56, -, -, hcb⟩ := hQ
    have e := List.getElem_of_eq (ly7Csb_eq σ) hi
    rcases i with _ | j
    · -- `verify_bus_gkr_loop0_loop0`
      rw [e, List.getElem_cons_zero] at ht hn hv
      simp only [decide_eq_true_eq] at ht
      have hc4 : 0 < (c + 1 - sh) / 4 := by
        rcases Nat.eq_zero_or_pos ((c + 1 - sh) / 4) with h0 | h0
        · exfalso; apply ht; rw [e56, h0, pow_zero, e_add_self]
        · exact h0
      simp only [List.map_cons, List.map_nil, e57, e53] at hv
      have hb' := h29 rd t _ rets hn (loopPre_gen hc4 (by omega) _) hv hb
      simp only [List.getD_cons_succ, List.getD_cons_zero, gen_pow_eq_ofK,
        logG_spec (show (c + 1 - sh) / 4 < 2 ^ 64 - 1 by omega)] at hb'
      simp only [ly7Wb, List.getElem_cons_zero, ly7W29]; omega
    · rw [e, List.getElem_cons_succ] at hn hv
      have hW' : (ly7Wb fs K29 R sh c σ)[j + 1] = R := by simp [ly7Wb]
      rw [hW']
      have hm := List.getElem_mem (l := ly7Rounds σ) (by rw [ly7Csb_eq] at hi; simpa using hi)
      obtain ⟨n', hn', hf⟩ := ly7Rounds_mem hm
      rw [hf] at hn; exact hR n' hn' rd t _ rets hn hv hb

end
end LeanVM.Guest.B1.Tables
