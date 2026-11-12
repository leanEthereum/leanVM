/-
  LeanVM.Guest.B1.Place.OsMean

  open_stacked's callees by name: their meanings, a call relation dispatching on them, and the
  callees' placed completeness from a body proved at it on every memory.
-/

module

public import LeanVM.Guest.Lift.OsCallees
public import LeanVM.Guest.B1.Place.OsRound

/-!
# The callees' meanings, by name

`osKindOf f`: the kind of callee `f` names, read from `osKindTable` (the named callees of
`open_stacked__L{m}` at f128: `opening_round`, `opening_tail_round`, `opening_message`,
`squeeze_point_from`, `grind_check`, `verify_merkle_cap`, `fold_final_msg`; each
with its meaning `OsKind.Pre` and its loads `OsKind.spec`). `decode_query_windows`, the
`opening_queries` specializations and the loop helpers are the other callees, placed apart.
`osKindTable_ok`: every entry names a deployed specialization of its kind (a kernel check), so
`kindD`: a named callee is complete placed on its meaning, its loads in the caller's words.

`FixedReads`, `fixedReads_region`: loads whose words every memory holding the caller's words
holds the same lie in their region. `osCR rd Sp X`: the call relation of the memory `rd`, each
named callee's meaning and `X` (for the body, `OsXOk`: its loads fixed), `Sp` for the others.

`os_calls_of_allOk`: a block holding at a relation `C` makes `C` hold of each taken call's frame.
`os_kid_named`, `os_kid_special`: a body holding at `osCR rd Sp (OsXOk κ Lk)` on every memory
holding `Lk` (and one such memory existing) makes each taken call with a name complete placed on
`Lk`, and each other one satisfy `Sp`.
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
  | round
  | tail
  | msg (n nonce : ℕ)
  | spf (n : ℕ)
  | grind (b : ℕ)
  | cap (d : ℕ)
  | ffm (n : ℕ)
  deriving DecidableEq

/-- A kind's meaning. -/
def OsKind.Pre : OsKind → Reader → List E → List E → Prop
  | .round => fun rd a r => Whir.MeaningOpeningRound rd a r ∧ WinTabs rd (a.getD 7 0)
  | .tail => MeaningOpeningTailRound
  | .msg n nonce => MeaningOpeningMessage n nonce
  | .spf n => MeaningSqueezePointFrom n
  | .grind b => grindPre b
  | .cap d => MeaningVerifyMerkleCap d
  | .ffm n => MeaningFoldFinalMsg n

/-- A kind's loads. -/
def OsKind.spec : OsKind → List (ℕ × ℕ)
  | .round => roundSpec
  | .tail => tailSpec
  | .msg n nonce => msgSpec n nonce
  | .spf n => spfSpec n
  | .grind _ => []
  | .cap d => merkleCapSpec d
  | .ffm n => foldFinalSpec n

/-- The named callees and their kinds. -/
def osKindTable : List (String × OsKind) :=
  [("opening_round", .round), ("opening_tail_round", .tail),
    ("opening_message__L6_L1", .msg 6 1), ("opening_message__L8_L1", .msg 8 1), ("opening_message__L12_L1", .msg 12 1),
    ("opening_message__L20_L1", .msg 20 1), ("opening_message__L36_L1", .msg 36 1),
    ("squeeze_point_from__L6", .spf 6), ("squeeze_point_from__L7", .spf 7),
    ("squeeze_point_from__L8", .spf 8), ("squeeze_point_from__L9", .spf 9),
    ("squeeze_point_from__L10", .spf 10), ("squeeze_point_from__L11", .spf 11),
    ("squeeze_point_from__L12", .spf 12), ("squeeze_point_from__L13", .spf 13),
    ("squeeze_point_from__L14", .spf 14), ("squeeze_point_from__L15", .spf 15),
    ("squeeze_point_from__L16", .spf 16), ("squeeze_point_from__L17", .spf 17),
    ("squeeze_point_from__L18", .spf 18), ("squeeze_point_from__L19", .spf 19),
    ("squeeze_point_from__L20", .spf 20), ("squeeze_point_from__L21", .spf 21),
    ("squeeze_point_from__L22", .spf 22), ("squeeze_point_from__L23", .spf 23),
    ("squeeze_point_from__L24", .spf 24),
    ("grind_check__L17", .grind 17), ("grind_check__L15", .grind 15)] ++
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

/-- An entry names a deployed specialization of its kind. -/
def osKindEntryOk : String × OsKind → Bool
  | (f, .round) => f == "opening_round"
  | (f, .tail) => f == "opening_tail_round"
  | (f, .msg n nonce) => decide ((n, nonce) ∈ omDeployed) && f == omName (n, nonce)
  | (f, .spf n) => decide (n ∈ spfDeployed) && f == spfName n
  | (f, .grind b) => decide (b ∈ grindBitsDeployed) && f == grindCheckName b
  | (f, .cap d) => decide ((f, d) ∈ merkleCapNames)
  | (f, .ffm n) => decide ((f, n) ∈ foldFinalMsgNames)

set_option maxRecDepth 100000 in
theorem osKindTable_ok : osKindTable.all osKindEntryOk = true := by decide +kernel

theorem osKindEntry_ok {f : String} {K : OsKind} (hK : osKindOf f = some K) :
    osKindEntryOk (f, K) = true :=
  List.all_eq_true.mp osKindTable_ok _ (os_mem_of_lookup osKindTable hK)

/-- **A named callee is complete placed on its meaning, its loads in the caller's words**,
`opening_round` by its own placed form. -/
theorem kindD (h : OsCalleesRegD fs cert κ) (hr : OsRoundRegD fs cert κ) {f : String} {K : OsKind}
    (hK : osKindOf f = some K) : CompleteRelRegD fs cert κ f K.Pre (RegPtrs K.spec) := by
  have he := osKindEntry_ok hK
  cases K with
  | round =>
    simp only [osKindEntryOk, beq_iff_eq] at he
    subst he; exact hr
  | tail =>
    simp only [osKindEntryOk, beq_iff_eq] at he
    subst he; exact h.tail
  | msg n nonce =>
    simp only [osKindEntryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
    obtain ⟨hm, rfl⟩ := he
    exact h.msg _ hm
  | spf n =>
    simp only [osKindEntryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
    obtain ⟨hm, rfl⟩ := he
    exact h.spf _ hm
  | grind b =>
    simp only [osKindEntryOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
    obtain ⟨hm, rfl⟩ := he
    exact h.grind _ hm
  | cap d =>
    simp only [osKindEntryOk, decide_eq_true_eq] at he
    exact h.merkleCap _ he
  | ffm n =>
    simp only [osKindEntryOk, decide_eq_true_eq] at he
    exact h.foldFinal _ he

/-- **Every named callee is complete placed on its meaning, its loads in the caller's words**, on
memories defined below `2^κ`, `11 ≤ κ`. -/
theorem kindD_holds (hκ : 11 ≤ κ) {f : String} {K : OsKind} (hK : osKindOf f = some K) :
    CompleteRelRegD fs cert κ f K.Pre (RegPtrs K.spec) :=
  kindD (osCalleesRegD_holds hκ) (osRoundRegD_holds hκ) hK

/-! ## Fixed loads -/

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
  exact forced_load_region (v := ws[t]'(by omega)) hl0 hm0 fun rd hl hm ↦ hr rd hl hm t (by omega)

/-- Two memory facts at one address agree. -/
theorem readsAt_unique {rd : Reader} {p : E} {xs ys : List E} (hl : xs.length = ys.length)
    (hx : ReadsAt rd p xs) (hy : ReadsAt rd p ys) : xs = ys := by
  refine List.ext_getElem hl fun k h1 h2 ↦ ?_
  have a := (hx k h1).2
  have b := (hy k h2).2
  rw [a] at b
  exact Option.some.inj b

/-! ## The call relation -/

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
  | .dispatch .., h0 =>
    obtain ⟨j, hj, hx, hc⟩ := h0
    exact ⟨j, hj, hx, hC _ _ _ hc⟩

/-- The facts of a named callee's loads its meaning does not fix: its read words, fixed on every
memory holding `M`. -/
def OsXOk (κ : ℕ) (M : Layout) (K : OsKind) (a : List E) : Prop := FixedReads κ K.spec a M

/-- **A named call of a body proved at `osCR` on every memory holding `Lk`** is complete placed
on `Lk`. -/
theorem os_kid_named (hk : OsCalleesRegD fs cert κ) (hr : OsRoundRegD fs cert κ) {Lk : Layout}
    {σ : Val} {pre : List Stmt} {Sp : String → List E → List E → Prop}
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
  exact kindD hk hr hK _ _ Lk (fixedReads_region (hpre rd0 hl0 hm0).2 ⟨rd0, hl0, hm0⟩)
    fun rd hl hm ↦ (hpre rd hl hm).1

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
