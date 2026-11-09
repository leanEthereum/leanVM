/-
  LeanVM.Guest.B1.Place.OsMean

  open_stacked's callees by name: their meanings, a call relation dispatching on them, and the
  callees' placed completeness from a body proved at it on every memory.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Place.OsKidsC
public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.Lift.OsCallees
public import LeanVM.Guest.B1.Whir.Commit

/-!
# The callees' meanings, by name

`osKindOf f`: the kind of callee `f` names, read from `osKindTable` (the names G7's
`OsCalleesRegD` covers, each with its meaning `OsKind.Pre` and its loads `OsKind.spec`).
`OsCalleesRegD.kindD`: a named callee is complete placed on its meaning, its loads in the caller's
words. `FixedReads`, `fixedReads_region`: loads whose words every memory holding the caller's words
holds the same lie in their region; `kind_fixed`: a named callee's are, by its meaning and `OsXOk`
(the read words its meaning does not fix).

`osCR rd Sp X`: the call relation of the memory `rd`, each named callee's meaning and `X`, the
other callees `Sp` (the squeeze loops, `opening_queries`, the residual loops, placed apart).

`os_calls_of_allOk`: a block holding at a relation `C` makes `C` hold of each taken call's frame.
`os_kid_named`, `os_kid_special`: a body holding at `osCR rd Sp X` on every memory holding `Lk`
(and one such memory existing) makes each taken call with a name complete placed on `Lk`, and
each other one satisfy `Sp`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Whir (AllOk StmtOk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- The kinds of `open_stacked`'s named callees. -/
inductive OsKind where
  | fold
  | can
  | grind (n : ℕ)
  | ood (n : ℕ)
  | fm (n : ℕ)
  | rw (f r : ℕ)
  | cap (d : ℕ)
  | ffm (n : ℕ)
  deriving DecidableEq

/-- A kind's meaning. -/
def OsKind.Pre : OsKind → Reader → List E → List E → Prop
  | .fold => MeaningOpeningFold
  | .can => fun _ a r => MeaningAssertCanonical a r
  | .grind n => fun _ a r => MeaningGrindCheck n a r
  | .ood n => MeaningOpeningOodPoint n
  | .fm n => MeaningOpeningFinalMessage n
  | .rw f r => MeaningOpeningRowWeights f r
  | .cap d => MeaningVerifyMerkleCap d
  | .ffm n => MeaningFoldFinalMsg n

/-- The named callees and their kinds. -/
def osKindTable : List (String × OsKind) :=
  [("opening_fold", .fold), ("assert_canonical", .can), ("grind_check__L17", .grind 17),
    ("opening_row_weights__L4_L0", .rw 4 0), ("opening_row_weights__L6_L1", .rw 6 1)] ++
  oodPointNames.map (fun p ↦ (p.1, .ood p.2)) ++
  finalMessageNames.map (fun p ↦ (p.1, .fm p.2)) ++
  merkleCapNames.map (fun p ↦ (p.1, .cap p.2)) ++
  foldFinalMsgNames.map (fun p ↦ (p.1, .ffm p.2))

/-- The kind a name names. -/
def osKindOf (f : String) : Option OsKind := osKindTable.lookup f

theorem os_mem_of_lookup {f : String} {K : OsKind} :
    ∀ (l : List (String × OsKind)), l.lookup f = some K → (f, K) ∈ l
  | [], h => by simp [List.lookup] at h
  | (a, b) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      have : f = a := by simpa using hb
      subst this
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (os_mem_of_lookup l h)

/-- A kind's loads, as G7's `OsCalleesRegD` states them. -/
def OsKind.spec : OsKind → List (ℕ × ℕ)
  | .fold => foldSpec
  | .can => []
  | .grind _ => []
  | .ood n => oodSpec n
  | .fm n => finalMsgSpec n
  | .rw f _ => rowWeightsSpec f
  | .cap d => merkleCapSpec d
  | .ffm n => foldFinalSpec n

/-- **A named callee is complete placed on its meaning, its loads in the caller's words.** -/
theorem OsCalleesRegD.kindD (h : OsCalleesRegD fs cert κ) {f : String} {K : OsKind}
    (hK : osKindOf f = some K) : CompleteRelRegD fs cert κ f K.Pre (RegPtrs K.spec) := by
  have hm := os_mem_of_lookup osKindTable hK
  simp only [osKindTable, List.mem_append, List.mem_cons, List.mem_map, Prod.mk.injEq,
    List.not_mem_nil, or_false] at hm
  rcases hm with ((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩
  · exact h.fold
  · exact h.canonical
  · exact h.grind
  · exact h.rowWeights4
  · exact h.rowWeights6
  · exact h.ood p hp
  · exact h.finalMsg p hp
  · exact h.merkleCap p hp
  · exact h.foldFinal p hp

theorem osKindOf_ood_pos {f : String} {n : ℕ} (hK : osKindOf f = some (.ood n)) : 1 ≤ n := by
  have hm := os_mem_of_lookup osKindTable hK
  simp only [osKindTable, List.mem_append, List.mem_cons, List.mem_map, Prod.mk.injEq,
    List.not_mem_nil, or_false, reduceCtorEq, and_false, exists_false, false_or,
    or_false] at hm
  obtain ⟨p, hp, -, h2⟩ := hm
  cases h2
  simp only [oodPointNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **Words every defined-low memory holding `M` holds the same** at a callee's loads. -/
def FixedReads (κ : ℕ) (spec : List (ℕ × ℕ)) (a : List E) (M : Layout) : Prop :=
  ∀ q ∈ spec, ∃ ws : List E, ws.length = q.2 ∧
    ∀ rd, LowDef κ rd → MemL rd M → ReadsAt rd (a.getD q.1 0) ws

/-- **Fixed loads lie in the layout's region.** -/
theorem fixedReads_region {spec : List (ℕ × ℕ)} {a : List E} {M : Layout}
    (h : FixedReads κ spec a M) (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 M) :
    RegPtrs spec a (RegionL M) := by
  intro q hq t ht
  obtain ⟨ws, hl, hr⟩ := h q hq
  obtain ⟨rd0, hl0, hm0⟩ := hex
  exact os_addr_in_regionL (v := ws[t]'(by omega))
    (fun rd hl hm ↦ (hr rd hl hm t (by omega)).2) hl0 hm0

/-- Two memory facts at one address agree. -/
theorem readsAt_unique {rd : Reader} {p : E} {xs ys : List E} (hl : xs.length = ys.length)
    (hx : ReadsAt rd p xs) (hy : ReadsAt rd p ys) : xs = ys := by
  refine List.ext_getElem hl fun k h1 h2 ↦ ?_
  have a := (hx k h1).2
  have b := (hy k h2).2
  rw [a] at b
  exact Option.some.inj b

/-- **The call relation of a memory**: a named callee's meaning there, and `X` of its arguments
(the facts of its loads the meaning does not fix); else `Sp`. -/
@[irreducible] def osCR (rd : Reader) (Sp : String → List E → List E → Prop)
    (X : OsKind → List E → Prop) : CallRel := fun f a r ↦
  match osKindOf f with
  | some K => K.Pre rd a r ∧ X K a
  | none => Sp f a r

theorem osCR_named {rd : Reader} {Sp : String → List E → List E → Prop} {X : OsKind → List E → Prop}
    {f : String} {K : OsKind} (hK : osKindOf f = some K) {a r : List E} (h : K.Pre rd a r)
    (hX : X K a) : osCR rd Sp X f a r := by
  unfold osCR; rw [hK]; exact ⟨h, hX⟩

theorem osCR_special {rd : Reader} {Sp : String → List E → List E → Prop}
    {X : OsKind → List E → Prop} {f : String} (hK : osKindOf f = none) {a r : List E}
    (h : Sp f a r) : osCR rd Sp X f a r := by
  unfold osCR; rw [hK]; exact h

/-- **A block holding at `C` makes `C` hold of each taken call's frame.** -/
theorem os_calls_of_allOk {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ {pre : List Stmt}, AllOk C rd σ pre →
      ∀ c ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ), c.taken = true →
        C c.f (c.args.map σ) (c.rets.map σ)
  | [], _, c, hc, _ => by simp at hc
  | s :: pre, h, c, hc, ht => by
    have h0 : StmtOk C rd σ s := h s (List.mem_cons_self ..)
    have h1 : AllOk C rd σ pre := fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
    match s, h0 with
    | .atom _, _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht
    | .call f args rets, h0 =>
      simp only [List.filterMap_cons, Main.Stmt.callS, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact h0
      · exact os_calls_of_allOk h1 c hc ht
    | .callIf cv f args, h0 =>
      simp only [List.filterMap_cons, Main.Stmt.callS, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [Main.mkCall, decide_eq_true_eq] at ht
        exact h0.2 ht
      · exact os_calls_of_allOk h1 c hc ht
    | .ret _, _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht
    | .ite .., _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht
    | .match_ .., _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht
    | .dispatch .., _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht

theorem os_allOk_mono {C C' : CallRel} {rd : Reader} {σ : Val} (hC : ∀ f a r, C f a r → C' f a r) :
    ∀ {ss : List Stmt}, AllOk C rd σ ss → AllOk C' rd σ ss := fun h s hs ↦ by
  have h0 := h s hs
  match s, h0 with
  | .atom _, h0 => exact h0
  | .call .., h0 => exact hC _ _ _ h0
  | .callIf .., h0 => exact ⟨h0.1, fun hc ↦ hC _ _ _ (h0.2 hc)⟩
  | .ret _, h0 => exact h0
  | .ite .., h0 => exact h0
  | .match_ .., h0 => exact h0
  | .dispatch .., h0 => exact h0

/-- The facts of a named callee's loads its meaning does not fix: its read words, fixed on every
memory holding `M` (the row weights, the cap, the folded message; the final message's `out`). -/
def OsXOk (κ : ℕ) (M : Layout) : OsKind → List E → Prop
  | .rw f _, a => FixedReads κ (rowWeightsSpec f) a M
  | .cap d, a => FixedReads κ (merkleCapSpec d) a M
  | .ffm n, a => FixedReads κ (foldFinalSpec n) a M
  | .fm n, a => FixedReads κ [(8, n)] a M
  | _, _ => True

/-- **A named callee's loads are fixed** on every memory holding `M` where its meaning holds. -/
theorem kind_fixed {K : OsKind} {a r : List E} {M : Layout} (hpos : ∀ n, K = .ood n → 1 ≤ n)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 M)
    (h : ∀ rd, LowDef κ rd → MemL rd M → K.Pre rd a r) (hX : OsXOk κ M K a) :
    FixedReads κ K.spec a M := by
  obtain ⟨rd0, hl0, hm0⟩ := hex
  have h0 := h rd0 hl0 hm0
  cases K with
  | fold =>
    simp only [OsKind.Pre] at h h0
    match a, h0, h with
    | [f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2], _, h =>
      intro q hq
      simp only [OsKind.spec, foldSpec, List.mem_singleton] at hq
      subst hq
      refine ⟨[r.getD 7 0, r.getD 8 0], rfl, fun rd hl hm ↦ ?_⟩
      obtain ⟨-, d0, d2, hr, hre⟩ := h rd hl hm
      have e : [r.getD 7 0, r.getD 8 0] = [d0, d2] := by
        rw [hre]; simp [Fs.squeeze, capOf]
      rw [e]; exact hr
  | can => intro q hq; simp [OsKind.spec] at hq
  | grind n => intro q hq; simp [OsKind.spec] at hq
  | ood n =>
    have hn := hpos n rfl
    simp only [OsKind.Pre] at h h0
    match a, h0, h with
    | [f0, f1, f2, f3, f4, r0, r1, r2, r3, r4, r5, r6, r7, point], _, h =>
      intro q hq
      simp only [OsKind.spec, oodSpec, List.mem_singleton] at hq
      subst hq
      refine ⟨_, ?_, fun rd hl hm ↦ (h rd hl hm).2.1⟩
      simp only [List.length_cons, Whir.squeezeN_length]
      omega
  | fm n =>
    simp only [OsKind.Pre] at h h0
    match a, h0, h with
    | [f0, f1, f2, f3, f4, w0, w1, cur, out], _, h =>
      have hX' : FixedReads κ [(8, n)] [f0, f1, f2, f3, f4, w0, w1, cur, out] M := hX
      obtain ⟨W, hWl, hW⟩ := hX' (8, n) (List.mem_singleton_self _)
      intro q hq
      simp only [OsKind.spec, finalMsgSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · refine ⟨W ++ [r.getD 7 0], by simp [hWl], fun rd hl hm ↦ ?_⟩
        obtain ⟨-, ms, nonce, hml, hc, ho, hre⟩ := h rd hl hm
        have e1 : ms = W := readsAt_unique (by rw [hml, hWl]) ho (hW rd hl hm)
        have e2 : r.getD 7 0 = nonce := by rw [hre]; simp [capOf]
        rw [e2, ← e1]; exact hc
      · exact ⟨W, hWl, hW⟩
  | rw f r' => exact hX
  | cap d => exact hX
  | ffm n => exact hX

/-- **A named call of a body proved at `osCR` on every memory holding `Lk`** is complete placed
on `Lk`. -/
theorem os_kid_named (hk : OsCalleesRegD fs cert κ) {Lk : Layout} {σ : Val} {pre : List Stmt}
    {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → AllOk (osCR rd Sp (OsXOk κ Lk)) rd σ pre)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk)
    {c : Call} (hc : c ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) (ht : c.taken = true)
    {K : OsKind} (hK : osKindOf c.f = some K) :
    CompleteAtD fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) := by
  have hpre : ∀ rd, LowDef κ rd → MemL rd Lk → K.Pre rd (c.args.map σ) (c.rets.map σ) ∧
      OsXOk κ Lk K (c.args.map σ) := fun rd hl hm ↦ by
    have h := os_calls_of_allOk (hall rd hl hm) c hc ht
    unfold osCR at h; rw [hK] at h; exact h
  obtain ⟨rd0, hl0, hm0⟩ := hex
  have hfix := kind_fixed (fun n hn ↦ osKindOf_ood_pos (hn ▸ hK)) ⟨rd0, hl0, hm0⟩
    (fun rd hl hm ↦ (hpre rd hl hm).1) (hpre rd0 hl0 hm0).2
  exact hk.kindD hK _ _ Lk (fixedReads_region hfix ⟨rd0, hl0, hm0⟩) fun rd hl hm ↦ (hpre rd hl hm).1

/-- **Another call of such a body** satisfies `Sp`, one memory holding `Lk` existing. -/
theorem os_kid_special {Lk : Layout} {σ : Val} {pre : List Stmt}
    {Sp : String → List E → List E → Prop} {X : OsKind → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → AllOk (osCR rd Sp X) rd σ pre)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk)
    {c : Call} (hc : c ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) (ht : c.taken = true)
    (hK : osKindOf c.f = none) : Sp c.f (c.args.map σ) (c.rets.map σ) := by
  obtain ⟨rd0, hl, hm⟩ := hex
  have h := os_calls_of_allOk (hall rd0 hl hm) c hc ht
  unfold osCR at h; rw [hK] at h; exact h

end
end LeanVM.Guest.B1
