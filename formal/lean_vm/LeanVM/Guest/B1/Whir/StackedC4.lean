/-
  LeanVM.Guest.B1.Whir.StackedC4

  The completeness of `open_stacked`'s glue blocks.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC3
public import LeanVM.Guest.B1.Uniform

/-!
# `open_stacked`'s glue, honestly (TRIAGE #36)

The out-of-domain claim's glue and the queries' glue at their honest values.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The values of `osGlue` from its first: each product by the scalar, then its sum. -/
def osGlueVals (sc v c0 c1 c2 c b a t : E) : List E :=
  [sc * c0, c + sc * c0, sc * c1, b + sc * c1, sc * c2, a + sc * c2, sc * v, t + sc * v]

/-- **The glue of one claim** at its honest values. -/
theorem osGlue_complete {sc v c0 c1 c2 : ℕ} {s : OsSt} {kret : List E → Prop}
    (hv : ∀ j < 8, σ (.n (s.k + j)) = (osGlueVals (σ (.n sc)) (σ (.n v)) (σ (.n c0)) (σ (.n c1)) (σ (.n c2))
      (σ (.n s.c)) (σ (.n s.b)) (σ (.n s.a)) (σ (.n s.t))).getD j 0) :
    Stmt.HoldsList C rd σ (osGlue sc v c0 c1 c2 s).1 True kret ∧
      σ (.n (osGlue sc v c0 c1 c2 s).2.c) = σ (.n s.c) + σ (.n sc) * σ (.n c0) ∧
      σ (.n (osGlue sc v c0 c1 c2 s).2.b) = σ (.n s.b) + σ (.n sc) * σ (.n c1) ∧
      σ (.n (osGlue sc v c0 c1 c2 s).2.a) = σ (.n s.a) + σ (.n sc) * σ (.n c2) ∧
      σ (.n (osGlue sc v c0 c1 c2 s).2.t) = σ (.n s.t) + σ (.n sc) * σ (.n v) ∧
      (osGlue sc v c0 c1 c2 s).2.k = s.k + 8 ∧ (osGlue sc v c0 c1 c2 s).2.f0 = s.f0 ∧
      (osGlue sc v c0 c1 c2 s).2.f1 = s.f1 ∧ (osGlue sc v c0 c1 c2 s).2.cb = s.cb ∧
      (osGlue sc v c0 c1 c2 s).2.co = s.co := by
  have e := fun j (hj : j < 8) => hv j hj
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
  have e6 := e 6 (by omega); have e7 := e 7 (by omega)
  simp only [osGlueVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7
  refine ⟨?_, e1, e3, e5, e7, rfl, rfl, rfl, rfl, rfl⟩
  simp only [osGlue, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
  exact ⟨e0, by rw [e1, e0], e2, by rw [e3, e2], e4, by rw [e5, e4], e6, by rw [e7, e6]⟩

/-- The values of `osOodGlue` from its first, at the claim's value `y`, intro `c0, c2`, scalar
`sc`, `lam` and the running sums. -/
def osOodGlueVals (y c0 c2 sc lam c b a t : E) : List E :=
  [y, c2, c0, sc * c0, c + sc * c0, y + c2, sc * (y + c2), b + sc * (y + c2), sc * c2, a + sc * c2,
    sc * y, t + sc * y, sc * lam]

/-- **The out-of-domain claim's glue** at its honest values. -/
theorem osOodGlue_complete {so sc lam : ℕ} {s : OsSt} {y c0 c2 : E}
    (hy : LoadHolds rd (σ (.n osOod)) (so + 1) y) (hc0 : LoadHolds rd (σ (.n osOod)) (so + 2) c0)
    (hc2 : LoadHolds rd (σ (.n osOod)) (so + 3) c2) (hsc : LoadHolds rd (σ (.n osOod)) so (σ (.n sc)))
    {kret : List E → Prop}
    (hv : ∀ j < 13, σ (.n (s.k + j)) = (osOodGlueVals y c0 c2 (σ (.n sc)) (σ (.n lam)) (σ (.n s.c))
      (σ (.n s.b)) (σ (.n s.a)) (σ (.n s.t))).getD j 0) :
    Stmt.HoldsList C rd σ (osOodGlue so sc lam s).1 True kret ∧
      σ (.n (osOodGlue so sc lam s).2.c) = σ (.n s.c) + σ (.n sc) * c0 ∧
      σ (.n (osOodGlue so sc lam s).2.b) = σ (.n s.b) + σ (.n sc) * (y + c2) ∧
      σ (.n (osOodGlue so sc lam s).2.a) = σ (.n s.a) + σ (.n sc) * c2 ∧
      σ (.n (osOodGlue so sc lam s).2.t) = σ (.n s.t) + σ (.n sc) * y ∧
      σ (.n ((osOodGlue so sc lam s).2.k - 1)) = σ (.n sc) * σ (.n lam) ∧
      (osOodGlue so sc lam s).2.k = s.k + 13 ∧ (osOodGlue so sc lam s).2.f0 = s.f0 ∧
      (osOodGlue so sc lam s).2.f1 = s.f1 ∧ (osOodGlue so sc lam s).2.cb = s.cb ∧
      (osOodGlue so sc lam s).2.co = s.co := by
  have e := fun j (hj : j < 13) => hv j hj
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
  have e6 := e 6 (by omega); have e7 := e 7 (by omega); have e8 := e 8 (by omega)
  have e9 := e 9 (by omega); have e10 := e 10 (by omega); have e11 := e 11 (by omega)
  have e12 := e 12 (by omega)
  simp only [osOodGlueVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  refine ⟨?_, e4, e7, e9, e11, by
    rw [show (osOodGlue so sc lam s).2.k - 1 = s.k + 12 by simp [osOodGlue]]; exact e12,
    rfl, rfl, rfl, rfl, rfl⟩
  simp only [osOodGlue, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
  refine ⟨by rw [e0]; exact hy, by rw [e1]; exact hc2, hsc, by rw [e2]; exact hc0, by rw [e3, e2],
    by rw [e4, e3], by rw [e5, e0, e1], by rw [e6, e5], by rw [e7, e6], by rw [e8, e1], by rw [e9, e8],
    by rw [e10, e0], by rw [e11, e10], e12⟩

/-- `osOodGlues` of one claim. -/
theorem osOodGlues_one (lvl lam sc : ℕ) (s : OsSt) :
    osOodGlues lvl lam 0 1 sc s = ((osOodGlue ((lvl + 1) * 4) sc lam s).1,
      (osOodGlue ((lvl + 1) * 4) sc lam s).2, (osOodGlue ((lvl + 1) * 4) sc lam s).2.k - 1) := by
  simp [osOodGlues]

/-! ## From the trivial call relation -/

/-- A straight block that holds with every call allowed holds at a call relation every one of
its calls satisfies. -/
theorem os_holdsList_calls {C : CallRel} : ∀ (ss : List Stmt), ss.all Main.Stmt.straight = true →
    ∀ {next : Prop} {kret : List E → Prop}, Stmt.HoldsList osTC rd σ ss next kret →
      (∀ c ∈ (ss.filterMap Main.Stmt.callS).map (Main.mkCall σ), c.taken = true →
        C c.f (c.args.map σ) (c.rets.map σ)) →
      Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, h, _ => h
  | s :: ss, hs, next, kret, h, hc => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    have ih := os_holdsList_calls (C := C) ss hs.2 (next := next) (kret := kret)
    match s, hs.1 with
    | .atom a, _ =>
      rw [List.filterMap_cons_none (show Main.Stmt.callS (.atom a) = none from rfl)] at hc
      simp only [Stmt.HoldsList, Stmt.Holds] at h ⊢
      exact ⟨h.1, ih h.2 hc⟩
    | .call f args rets, _ =>
      rw [List.filterMap_cons_some (show Main.Stmt.callS (.call f args rets) = some (none, f, args, rets) from rfl),
        List.map_cons] at hc
      simp only [Stmt.HoldsList, Stmt.Holds] at h ⊢
      exact ⟨by simpa [Main.mkCall] using hc _ List.mem_cons_self rfl,
        ih h.2 fun c hc' => hc c (List.mem_cons_of_mem _ hc')⟩
    | .callIf c f args, _ =>
      rw [List.filterMap_cons_some (show Main.Stmt.callS (.callIf c f args) = some (some c, f, args, []) from rfl),
        List.map_cons] at hc
      simp only [Stmt.HoldsList, Stmt.Holds] at h ⊢
      exact ⟨h.1, fun hc0 => by simpa [Main.mkCall] using hc _ List.mem_cons_self (by simp [Main.mkCall, hc0]),
        ih h.2.2 fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')⟩

/-! ## The calls of a block -/

/-- Every entered call of a straight block, its argument and return words under `σ`, satisfies `C`. -/
def OsCallsOk (C : CallRel) (σ : Val) (ss : List Stmt) : Prop :=
  ∀ c ∈ (ss.filterMap Main.Stmt.callS).map (Main.mkCall σ), c.taken = true → C c.f (c.args.map σ) (c.rets.map σ)

theorem osCallsOk_append {C : CallRel} {σ : Val} {a b : List Stmt} (ha : OsCallsOk C σ a) (hb : OsCallsOk C σ b) :
    OsCallsOk C σ (a ++ b) := fun c hc ht => by
  rw [List.filterMap_append, List.map_append] at hc
  rcases List.mem_append.mp hc with h | h
  · exact ha c h ht
  · exact hb c h ht

/-- **A straight block's calls** satisfy the call relation it holds at. -/
theorem os_callsOk_of_holdsList {C : CallRel} : ∀ (ss : List Stmt), ss.all Main.Stmt.straight = true →
    ∀ {next : Prop} {kret : List E → Prop}, Stmt.HoldsList C rd σ ss next kret → OsCallsOk C σ ss
  | [], _, _, _, _ => fun c hc => by simp at hc
  | s :: ss, hs, next, kret, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    match s, hs.1 with
    | .atom a, _ =>
      simp only [Stmt.HoldsList, Stmt.Holds] at h
      intro c hc
      rw [List.filterMap_cons_none (show Main.Stmt.callS (.atom a) = none from rfl)] at hc
      exact os_callsOk_of_holdsList ss hs.2 h.2 c hc
    | .call f args rets, _ =>
      simp only [Stmt.HoldsList, Stmt.Holds] at h
      intro c hc ht
      rw [List.filterMap_cons_some (show Main.Stmt.callS (.call f args rets) = some (none, f, args, rets) from rfl),
        List.map_cons] at hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · simpa [Main.mkCall] using h.1
      · exact os_callsOk_of_holdsList ss hs.2 h.2 c hc' ht
    | .callIf cc f args, _ =>
      simp only [Stmt.HoldsList, Stmt.Holds] at h
      intro c hc ht
      rw [List.filterMap_cons_some (show Main.Stmt.callS (.callIf cc f args) = some (some cc, f, args, []) from rfl),
        List.map_cons] at hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · simp only [Main.mkCall, decide_eq_true_eq] at ht
        simpa [Main.mkCall] using h.2.1 ht
      · exact os_callsOk_of_holdsList ss hs.2 h.2.2 c hc' ht

theorem os_holdsList_toTC {C : CallRel} {ss : List Stmt} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ ss next kret) : Stmt.HoldsList osTC rd σ ss next kret :=
  holdsList_mono (fun _ _ _ _ => trivial) ss id (fun _ h => h) h

end
end LeanVM.Guest.B1
