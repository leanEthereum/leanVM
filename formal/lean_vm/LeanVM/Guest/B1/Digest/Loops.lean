/-
  LeanVM.Guest.B1.Digest.Loops

  Loop helpers whose bodies call functions, and range checks found by evaluation.
-/

module

public import LeanVM.Guest.B1.Digest.ChildList

/-!
# Loops with calls; range checks by evaluation

* `splitLoopF`, `loopShapeF`, `loop_stepF`: a `mul_range` helper whose body is a flat block
  (atoms and calls) before the conditional call (`Digest/Steps`' `loop_step` for blocks of atoms);
* `rcBoundOk`, `rcBound_sound`: `x` range-checked against a runtime bound `b · g⁻¹`;
  `rcConstOk`, `rcConst_sound`: against a compile-time `g^c`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Range checks by evaluation -/

/-- `x` is range-checked against `b · g⁻¹` (`assert log x < log b`). -/
def rcBoundOk (atoms : List Atom) (x b : V) : Bool :=
  match rcOf atoms x with
  | some k => (match mulOf atoms k with
      | some (l, gi) => decide (l = b) && atoms.any (isConstAt gi 9223372036854775821 0)
      | none => false)
  | none => false

theorem rcBound_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {x b : V}
    (h : rcBoundOk atoms x b = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ e, σ x = gen ^ e ∧ BelowLog (σ b) e := by
  unfold rcBoundOk at h
  split at h
  · rename_i k hk
    split at h
    · rename_i l gi hlg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, hgi⟩ := h
      obtain ⟨y, t1, t2, h1, h2, h3⟩ := rcOf_sound hk hat
      have hkv : σ k = σ l * ginvW := by rw [mulOf_sound hlg hat, const_sound hgi hat]
      exact rc_below hm hkv ⟨h1, h2, h3⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `x` is range-checked against the constant `word lo 0 0`. -/
def rcConstOk (atoms : List Atom) (x : V) (lo : ℕ) : Bool :=
  match rcOf atoms x with
  | some k => atoms.any (isConstAt k lo 0)
  | none => false

theorem rcConst_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {x : V}
    {lo c : ℕ} (hc : c < 2 ^ 33) (hw : word lo 0 0 = gen ^ c) (h : rcConstOk atoms x lo = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : ∃ e ≤ c, σ x = gen ^ e := by
  unfold rcConstOk at h
  split at h
  · rename_i k hk
    obtain ⟨y, t1, t2, h1, h2, h3⟩ := rcOf_sound hk hat
    exact rc_const hm hc (by rw [const_sound h hat, hw]) ⟨h1, h2, h3⟩
  · exact absurd h (by simp)

theorem word_g1 : word 2 0 0 = gen ^ 1 := by rw [word_gen, pow_one]

/-! ## Loop helpers with calls -/

/-- A `mul_range` helper's body: a flat block, the conditional call, `ret []`. -/
def splitLoopF : List Stmt → Option (List Stmt × V × String × List V)
  | [] => none
  | [_] => none
  | [s, t] => match s, t with
    | .callIf c f args, .ret [] => some ([], c, f, args)
    | _, _ => none
  | s :: t :: u :: rest =>
    if Stmt.flat s then (splitLoopF (t :: u :: rest)).map fun p => (s :: p.1, p.2) else none

theorem splitLoopF_eq : ∀ {body : List Stmt} {pre : List Stmt} {c : V} {f : String}
    {args : List V}, splitLoopF body = some (pre, c, f, args) →
      body = pre ++ [Stmt.callIf c f args, Stmt.ret []] ∧ pre.all Stmt.flat = true
  | [], _, _, _, _, h => by simp [splitLoopF] at h
  | [_], _, _, _, _, h => by simp [splitLoopF] at h
  | [s, t], pre, c, f, args, h => by
    simp only [splitLoopF] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · simp at h
  | s :: t :: u :: rest, pre, c, f, args, h => by
    simp only [splitLoopF] at h
    split at h
    · rename_i hs
      obtain ⟨⟨pre', c', f', a'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h2
      obtain ⟨e1, e2⟩ := splitLoopF_eq h1
      refine ⟨by rw [e1]; rfl, ?_⟩
      simp only [List.all_cons, hs, e2, Bool.and_self]
    · simp at h

theorem holds_loopBodyF {C : CallRel} {rd : Reader} {σ : Val} {pre : List Stmt} {c : V}
    {f : String} {args : List V} (hf : pre.all Stmt.flat = true)
    (h : Stmt.HoldsList C rd σ (pre ++ [Stmt.callIf c f args, Stmt.ret []]) False
      (fun rs => rs = [])) :
    (∀ s ∈ pre, Stmt.Holds C rd σ s True (fun rs => rs = [])) ∧ IsInK (σ c) ∧
      (σ c ≠ 0 → C f (args.map σ) []) := by
  rw [holdsList_append] at h
  obtain ⟨h1, h2⟩ := holdsList_flat pre hf _ _ h
  simp only [Stmt.HoldsList, Stmt.Holds] at h2
  exact ⟨h1, h2.1, h2.2.1⟩

/-- **The shape of a `mul_range` helper with calls** (`loopShape` for a flat block). -/
def loopShapeF (fn : Fn) (f : String) : Bool :=
  decide (2 ≤ fn.params.length) && decide (fn.params = (List.range fn.params.length).map V.n) &&
  match splitLoopF fn.body with
  | some (pre, c, g, args) =>
    g == f && decide (args.length = fn.params.length) && decide (args.tail = fn.params.tail) &&
      genMulOk (atomsIn pre) (args.headD default) (V.n 0) &&
      (match addOf (atomsIn pre) c with
       | some (p, q) => genMulOk (atomsIn pre) p (V.n 0) && decide (q = V.n 1)
       | none => false)
  | none => false

/-- The block of a loop helper's body. -/
def loopPre (fn : Fn) : List Stmt := ((splitLoopF fn.body).map (·.1)).getD []

/-- **A run of a loop helper with calls**: some valuation of its block with the counter `x` and
the other parameters `ps`, and, while `x·g ≠ N`, the run at `x·g`. -/
theorem loop_stepF {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) {x : E} {ps : List E}
    (h : coreProgram.Rel rd f (x :: ps) []) :
    ∃ σ : Val, σ (V.n 0) = x ∧ fn.params.tail.map σ = ps ∧
      (∀ s ∈ loopPre fn, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = [])) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []) := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem hf _ _).mp h
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h2, hpar⟩, hok⟩ := hok
  unfold loopPre
  split at hok
  · rename_i pre c g args hsl
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨rfl, hlen⟩, htail⟩, hg⟩, hc⟩ := hok
    obtain ⟨hbody, hflat⟩ := splitLoopF_eq hsl
    rw [hbody] at hb
    obtain ⟨hall, -, hcall⟩ := holds_loopBodyF hflat hb
    have hat := atoms_of_flat hall
    have hx0 : σ (V.n 0) = x := by
      have := congrArg List.head? hp
      rw [hpar] at this
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map] at this
      simpa using this
    have hps : fn.params.tail.map σ = ps := by
      have := congrArg List.tail hp
      rwa [← List.map_tail] at this
    have hN : ps.headD 0 = σ (V.n 1) := by
      rw [← hps, hpar]
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map, List.range_succ_eq_map]
      simp
    refine ⟨σ, hx0, hps, by simpa [hsl] using hall, fun hne => ?_⟩
    split at hc
    · rename_i p q hpq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hp', rfl⟩ := hc
      have hcv : σ c = x * gen + ps.headD 0 := by
        rw [addOf_sound hpq hat, genMul_sound hp' hat, hx0, hN]
      have := hcall (by rw [hcv]; exact hne)
      have hargs : args.map σ = x * gen :: ps := by
        obtain ⟨a0, rest, rfl⟩ : ∃ a0 rest, args = a0 :: rest := by
          cases args with
          | nil => simp at hlen; omega
          | cons a0 rest => exact ⟨a0, rest, rfl⟩
        simp only [List.headD_cons] at hg
        simp only [List.tail_cons] at htail
        rw [List.map_cons, genMul_sound hg hat, hx0, htail, hps]
      rwa [hargs] at this
    · exact absurd hc (by simp)
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Digest
