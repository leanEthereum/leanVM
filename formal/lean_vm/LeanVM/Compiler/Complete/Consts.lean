/-
  LeanVM.Compiler.Complete.Consts
  A right table of constant parameters (`ConstsOk`) holds of every call of an honest run: what
  completeness reads of a loop helper's closing call.
-/

module

public import LeanVM.Compiler.Sound.Consts
public import LeanVM.Guest.Memory
public import LeanVM.Guest.Memory.Fresh

/-!
# The constant parameters on an honest run

`CallsIn T σ es`: every call the events `es` set up (`calls`, entered or not) passes the words
the table `T` names for its callee's arguments.

* `walk_consts`: where `T` is right of a block (`blockOk`) and the path's events hold, the calls
  of the block's path under `σ` pass the table's words, what the events before each call teach
  (a `const` atom's value holds its word) supplying them;
* `insts_consts`: in a valid run of a program `T` is right of (`ConstsOk`), started with its
  root's entries' words, every instance's parameters hold its entries' words (`ParamsIn`): its
  caller's path passed them.

The twin, for the obligations, is `Sound/Consts.lean`.
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **The calls these events set up pass the table's words.** -/
def CallsIn (T : String → List (ℕ × E)) (σ : Val) (es : List Ev) : Prop :=
  ∀ c ∈ calls es, ∀ x ∈ T c.f, (c.args.map σ)[x.1]? = some x.2

section Walk

variable {T : String → List (ℕ × E)} {rd : Reader} {σ : Val}

theorem callsIn_nil : CallsIn T σ [] := fun c hc => by simp [calls] at hc

theorem callsIn_append {a b : List Ev} (ha : CallsIn T σ a) (hb : CallsIn T σ b) :
    CallsIn T σ (a ++ b) := by
  intro c hc
  simp only [calls, List.filterMap_append, List.mem_append] at hc
  exact hc.elim (ha c) (hb c)

theorem callsIn_cons_noCall {e : Ev} {es : List Ev} (he : e.call? = none) (h : CallsIn T σ es) :
    CallsIn T σ (e :: es) := by
  intro c hc
  simp only [calls, List.filterMap_cons, he] at hc
  exact h c hc

/-- A branch's events after its condition's. -/
theorem callsIn_pre {o : Out} {c : V} (ih : (∀ e ∈ o.evs, e.Holds rd σ) → CallsIn T σ o.evs)
    (he : ∀ e ∈ (o.pre [.inK c]).evs, e.Holds rd σ) : CallsIn T σ (o.pre [.inK c]).evs := by
  cases o with
  | fall es =>
      simp only [Out.pre, Out.evs] at he ⊢
      exact callsIn_cons_noCall rfl (ih fun e h => he e (List.mem_append_right _ h))
  | ret es vs =>
      simp only [Out.pre, Out.evs] at he ⊢
      exact callsIn_cons_noCall rfl (ih fun e h => he e (List.mem_append_right _ h))
  | stuck =>
      simp only [Out.pre, Out.evs]
      exact callsIn_nil

/-- The calls of a fused dispatch: of one of its callees, on its arguments. -/
theorem pick_calls {x : V} {args rets : List V} : ∀ (j : ℕ) (fs : List String),
    ∀ c ∈ calls (pick σ x args rets j fs).evs, c.f ∈ fs ∧ c.args = args
  | _, [], c, hc => by
      rw [pick] at hc
      simp [Out.evs, calls] at hc
  | j, f :: fs, c, hc => by
      rw [pick] at hc
      split at hc
      · simp only [Out.evs, calls, Ev.call?, List.filterMap_cons, List.filterMap_nil,
          List.mem_singleton] at hc
        subst hc
        exact ⟨List.mem_cons_self, rfl⟩
      · obtain ⟨h1, h2⟩ := pick_calls (j + 1) fs c hc
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- What a statement whose path falls through teaches holds. -/
theorem learn_walk1 {s : Stmt} {kn : Known} (hk : KnownHolds σ kn) {es : List Ev}
    (h1 : walk1 σ s = .fall es) (he : ∀ e ∈ es, e.Holds rd σ) : KnownHolds σ (learn kn s) := by
  cases s with
  | atom a =>
      rw [walk1] at h1
      obtain rfl := (Out.fall.inj h1).symm
      exact learn_holds hk (he _ (List.mem_singleton_self _))
  | _ => exact hk

mutual
/-- **The calls of a statement's path pass the table's words.** -/
theorem walk1_consts : ∀ (s : Stmt) {kn : Known}, KnownHolds σ kn → stmtOk T kn s = true →
    (∀ e ∈ (walk1 σ s).evs, e.Holds rd σ) → CallsIn T σ (walk1 σ s).evs
  | .atom _, _, _, _, _ => by
      rw [walk1]
      exact callsIn_cons_noCall rfl callsIn_nil
  | .ite cv z n, _, hk, hs, he => by
      simp only [stmtOk, Bool.and_eq_true] at hs
      rw [walk1] at he ⊢
      by_cases h0 : σ cv = 0
      · simp only [h0, ↓reduceIte] at he ⊢
        exact callsIn_pre (walk_consts z hk hs.1) he
      · simp only [h0, ↓reduceIte] at he ⊢
        exact callsIn_pre (walk_consts n hk hs.2) he
  | .match_ x arms, _, hk, hs, he => by
      rw [walk1] at he ⊢
      exact walkArms_consts x 0 arms hk hs he
  | .call f args rets, _, hk, hs, _ => by
      intro c hc
      simp only [walk1, Out.evs, calls, Ev.call?, List.filterMap_cons, List.filterMap_nil,
        List.mem_singleton] at hc
      subst hc
      exact argsOk_words hk hs
  | .callIf cv f args, _, hk, hs, _ => by
      intro c hc
      by_cases h0 : σ cv = 0 <;>
        simp only [walk1, h0, ↓reduceIte, Out.evs, calls, Ev.call?, List.filterMap_cons,
          List.filterMap_nil, List.mem_singleton] at hc <;>
        (subst hc; exact argsOk_words hk hs)
  | .dispatch x fs args rets, _, hk, hs, _ => by
      intro c hc
      rw [walk1] at hc
      obtain ⟨hf, ha⟩ := pick_calls 0 fs c hc
      rw [ha]
      exact argsOk_words hk (List.all_eq_true.mp hs _ hf)
  | .ret _, _, _, _, _ => by
      rw [walk1]
      exact callsIn_nil

/-- **The calls of a block's path pass the table's words**, each statement knowing what the ones
before it taught. -/
theorem walk_consts : ∀ (ss : List Stmt) {kn : Known}, KnownHolds σ kn → blockOk T kn ss = true →
    (∀ e ∈ (walk σ ss).evs, e.Holds rd σ) → CallsIn T σ (walk σ ss).evs
  | [], _, _, _, _ => by
      rw [walk]
      exact callsIn_nil
  | s :: ss, _, hk, hs, he => by
      simp only [blockOk, Bool.and_eq_true] at hs
      have ih1 := walk1_consts s hk hs.1
      rw [walk] at he ⊢
      revert he ih1
      cases h1 : walk1 σ s with
      | fall es =>
          intro he ih1
          revert he
          cases h2 : walk σ ss with
          | stuck =>
              intro _
              simp only [Out.seq, Out.pre, Out.evs]
              exact callsIn_nil
          | fall es' =>
              intro he
              simp only [Out.seq, Out.pre, Out.evs] at he ⊢
              have he1 : ∀ e ∈ es, e.Holds rd σ := fun e h => he e (List.mem_append_left _ h)
              have ih2 := walk_consts ss (learn_walk1 hk h1 he1) hs.2
              rw [h2] at ih2
              exact callsIn_append (ih1 he1) (ih2 fun e h => he e (List.mem_append_right _ h))
          | ret es' vs =>
              intro he
              simp only [Out.seq, Out.pre, Out.evs] at he ⊢
              have he1 : ∀ e ∈ es, e.Holds rd σ := fun e h => he e (List.mem_append_left _ h)
              have ih2 := walk_consts ss (learn_walk1 hk h1 he1) hs.2
              rw [h2] at ih2
              exact callsIn_append (ih1 he1) (ih2 fun e h => he e (List.mem_append_right _ h))
      | ret es vs =>
          intro he ih1
          simp only [Out.seq, Out.evs] at he ⊢
          exact ih1 he
      | stuck =>
          intro _ _
          simp only [Out.seq, Out.evs]
          exact callsIn_nil

/-- **The calls of the arm the selector picks pass the table's words.** -/
theorem walkArms_consts (x : V) : ∀ (j : ℕ) (arms : List (List Stmt)) {kn : Known},
    KnownHolds σ kn → armsOk T kn arms = true → (∀ e ∈ (walkArms σ x j arms).evs, e.Holds rd σ) →
    CallsIn T σ (walkArms σ x j arms).evs
  | _, [], _, _, _, _ => by
      rw [walkArms]
      exact callsIn_nil
  | j, a :: as, _, hk, hs, he => by
      simp only [armsOk, Bool.and_eq_true] at hs
      rw [walkArms] at he ⊢
      by_cases h : σ x = ofK (addressOfIndex j)
      · simp only [h, ↓reduceIte] at he ⊢
        exact walk_consts a hk hs.1 he
      · simp only [h, ↓reduceIte] at he ⊢
        exact walkArms_consts x (j + 1) as hk hs.2 he
end

end Walk

/-! ## The instances of a run -/

section Insts

variable {T : String → List (ℕ × E)} {rd : Reader} {P : Program} {fs : String → ℕ}
  {lp : String → Bool} {H : Memory.Inst → ℕ → E × E}

/-- **An instance's parameters hold its entries' words.** -/
def ParamsIn (T : String → List (ℕ × E)) (P : Program) (t : Tree) : Prop :=
  ∀ fn, P.find? t.name = some fn → ∀ x ∈ T t.name, (fn.params.map t.val)[x.1]? = some x.2

theorem find?_mem {f : String} {fn : Fn} (h : P.find? f = some fn) : fn ∈ P ∧ fn.name = f := by
  unfold Program.find? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

mutual
/-- **In a valid run started with its entries' words, every instance's parameters hold its
entries' words**, for a table right of the program. -/
theorem insts_consts (hT : ConstsOk T P = true) : ∀ (t : Tree) (fp : ℕ) (hdr : E × E)
    {args rets : List E}, t.Valid P rd args rets → (∀ x ∈ T t.name, args[x.1]? = some x.2) →
    ∀ I ∈ t.insts fs lp H fp hdr, ParamsIn T P I.t
  | .node f σ bufs kids, fp, hdr, args, rets, hv, ha, I, hI => by
      obtain ⟨fn, hf, hp, es, vs, hw, -, hev, hk⟩ := hv
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · intro fn' hf' x hx
        obtain rfl : fn' = fn := Option.some.inj (hf'.symm.trans hf)
        exact (congrArg (fun l => l[x.1]?) hp).trans (ha x hx)
      · have hmem := find?_mem hf
        have hkn : KnownHolds σ (entryKnown T fn) :=
          entryKnown_holds hp (by rw [hmem.2]; exact ha)
        have hcalls := walk_consts (rd := rd) fn.body hkn
          (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hT).2 fn hmem.1) (by rw [hw]; exact hev)
        rw [hw] at hcalls
        exact instsKids_consts hT kids σ (calls es) _ 0 _ hk hcalls I hI
  | .phantom .., _, _, _, _, hv, _, _, _ => hv.elim

/-- `insts_consts` for the callees: each started with the words its call passes. -/
theorem instsKids_consts (hT : ConstsOk T P = true) : ∀ (ks : List Tree) (σ : Val)
    (cs : List Call) (I : Memory.Inst) (j : ℕ) (ps : List ℕ), Tree.KidsValid P rd σ cs ks →
    (∀ c ∈ cs, ∀ x ∈ T c.f, (c.args.map σ)[x.1]? = some x.2) →
    ∀ J ∈ Tree.instsKids fs lp H I j ps ks, ParamsIn T P J.t
  | [], _, _, _, _, _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, _, _, _, _, [], _, _, J, hJ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, σ, c :: cs, I, j, p :: ps, ⟨hn, hc, hks⟩, hm, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · by_cases ht : c.taken = true
        · simp only [ht, ↓reduceIte] at hc
          exact insts_consts hT k p _ hc (by rw [hn]; exact hm c List.mem_cons_self) J hJ
        · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc
          obtain ⟨⟨f, σ', rfl⟩, fn, hf, hp⟩ := hc
          rw [insts_phantom, List.mem_singleton] at hJ
          subst hJ
          intro fn' hf' x hx
          obtain rfl : fn' = fn := Option.some.inj (hf'.symm.trans hf)
          have hx' : x ∈ T c.f := by rw [← hn]; exact hx
          exact (congrArg (fun l => l[x.1]?) hp).trans (hm c List.mem_cons_self x hx')
      · exact instsKids_consts hT ks σ cs I (j + 1) ps hks
          (fun c' hc' => hm c' (List.mem_cons_of_mem _ hc')) J hJ
  | _ :: _, _, [], _, _, _ :: _, h, _, _, _ => h.elim
end

end Insts

end
end LeanVM.Compiler
