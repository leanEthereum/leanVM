/-
  LeanVM.Guest.Memory.SizeTotal

  The words a path allocates, and the functions a block can call.
-/

module

public import LeanVM.Guest.Memory.Size

/-!
# The words of a path, the callees of a block

An instance of `f` allocates its frame `fs f`, its `HeapBuf`s and, for each `callIf` it does
not take, a phantom of the callee's tail: what its path's events add to the frame is
`Ev.words`. `CallsIn P S`: the paths of the functions of `S` call only functions of `S`;
`Stmt.blockCallees` lists the functions a block can call, so `CallsIn` follows from the syntax
(`callsIn_of_callees`). `Stmt.blockWords` bounds the words of a block's paths by
`c + Σ fs (tailKey gs)`, independently of `fs`: a `HeapBuf(n)` costs `n`, a `callIf` its callee's
tail, a branch both sides; a dynamic `HeapBuf` has no bound (`none`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The words an event adds to its instance's frame: a `HeapBuf`'s size, an untaken call's
tail. -/
noncomputable def Ev.words (fs : String → ℕ) (σ : Val) (e : Ev) : ℕ :=
  (e.alloc? σ).getD 0 + match e.call? with
    | some c => if c.taken then 0 else fs (tailKey c.f)
    | none => 0

/-- The tails of the untaken calls. -/
def skipWords (fs : String → ℕ) : List Call → ℕ
  | [] => 0
  | c :: cs => (if c.taken then 0 else fs (tailKey c.f)) + skipWords fs cs

/-- The paths of the functions of `S` call only functions of `S`. -/
def CallsIn (P : Core.Program) (S : String → Prop) : Prop :=
  ∀ f, S f → ∀ fn, P.find? f = some fn → ∀ σ es vs, walk σ fn.body = .ret es vs →
    ∀ c ∈ calls es, S c.f

/-- `TotalLe` on the arguments satisfying `Pre`. -/
def TotalLeOn (P : Core.Program) (fs : String → ℕ) (f : String) (Pre : List E → Prop)
    (B : List E → ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → Pre args → t.Valid P rd args rets →
    t.BufsOk P → t.total fs ≤ B args

/-! ## From the syntax -/

/-- The words an atom's event adds; `none` for a dynamic `HeapBuf`. -/
def atomWords? : Atom → Option ℕ
  | .hint (.alloc _ n) => some n
  | .hint (.allocDyn _ _) => none
  | _ => some 0

/-- Words `c + Σ fs gs` as `(c, gs)`: added, `none` if either is. -/
def Option.addW : Option (ℕ × List String) → Option (ℕ × List String) → Option (ℕ × List String)
  | some a, some b => some (a.1 + b.1, a.2 ++ b.2)
  | _, _ => none

mutual
/-- A bound `(c, gs)` on the words of a statement's paths, `c + Σ fs gs`: the `HeapBuf`s'
sizes, the `callIf`s' callees, both sides of a branch. -/
def Stmt.words : Stmt → Option (ℕ × List String)
  | .atom a => (atomWords? a).map fun n => (n, [])
  | .ite _ z n => Option.addW (Stmt.blockWords z) (Stmt.blockWords n)
  | .match_ _ arms => Stmt.armsWords arms
  | .callIf _ f _ => some (0, [f])
  | _ => some (0, [])

/-- A bound on the words of a block's paths. -/
def Stmt.blockWords : List Stmt → Option (ℕ × List String)
  | [] => some (0, [])
  | s :: ss => Option.addW (Stmt.words s) (Stmt.blockWords ss)

/-- A bound on the words of any arm's paths. -/
def Stmt.armsWords : List (List Stmt) → Option (ℕ × List String)
  | [] => some (0, [])
  | a :: as => Option.addW (Stmt.blockWords a) (Stmt.armsWords as)
end

mutual
/-- The functions a statement can call. -/
def Stmt.callees : Stmt → List String
  | .ite _ z n => Stmt.blockCallees z ++ Stmt.blockCallees n
  | .match_ _ arms => Stmt.armsCallees arms
  | .call f _ _ => [f]
  | .callIf _ f _ => [f]
  | .dispatch _ fs _ _ => fs
  | _ => []

/-- The functions a block can call. -/
def Stmt.blockCallees : List Stmt → List String
  | [] => []
  | s :: ss => Stmt.callees s ++ Stmt.blockCallees ss

/-- The functions any arm can call. -/
def Stmt.armsCallees : List (List Stmt) → List String
  | [] => []
  | a :: as => Stmt.blockCallees a ++ Stmt.armsCallees as
end

section Syntax

variable {fs : String → ℕ} {σ : Val}

/-- The words of an outcome's events. -/
noncomputable def Out.words (fs : String → ℕ) (σ : Val) (o : Out) : ℕ := (o.evs.map (Ev.words fs σ)).sum

theorem Out.calls_seq {o k : Out} {c : Call} (h : c ∈ calls (o.seq k).evs) :
    c ∈ calls o.evs ∨ c ∈ calls k.evs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> rcases k with es' | ⟨es', vs'⟩ | _ <;>
    simp_all [Out.seq, Out.pre, Out.evs, calls, List.filterMap_append]

theorem Out.calls_pre_inK (c : V) (o : Out) : calls (o.pre [.inK c]).evs = calls o.evs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> simp [Out.pre, Out.evs, calls, Ev.call?, List.filterMap_cons]

theorem pick_words {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ),
    (pick σ x args rets j gs).words fs σ = 0 ∧ ∀ c ∈ calls (pick σ x args rets j gs).evs, c.f ∈ gs
  | [], _ => by simp [pick, Out.words, Out.evs, calls]
  | g :: gs, j => by
      unfold pick
      split_ifs
      · simp [Out.words, Out.evs, calls, Ev.words, Ev.alloc?, Ev.call?]
      · obtain ⟨h1, h2⟩ := pick_words gs (j + 1)
        exact ⟨h1, fun c hc => List.mem_cons_of_mem _ (h2 c hc)⟩

mutual
/-- **A statement's path calls its callees.** -/
theorem walk1_callees : ∀ (s : Stmt) {c : Call}, c ∈ calls (walk1 σ s).evs → c.f ∈ Stmt.callees s
  | .atom a, c, h => by simp [walk1, Out.evs, calls, Ev.call?] at h
  | .ite b z m, c, h => by
      rw [walk1, Out.calls_pre_inK] at h
      simp only [Stmt.callees, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_callees z h)
      · exact Or.inr (walk_callees m h)
  | .match_ x arms, c, h => by
      rw [walk1] at h
      exact walkArms_callees x arms 0 h
  | .call f args rets, c, h => by
      simp only [walk1, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; simp [Stmt.callees]
  | .callIf b f args, c, h => by
      rw [walk1] at h
      split_ifs at h <;>
        simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
          List.mem_cons, List.not_mem_nil, or_false] at h <;> subst h <;> simp [Stmt.callees]
  | .dispatch x gs args rets, c, h => by
      rw [walk1] at h
      exact (pick_words (fs := fun _ => 0) gs 0).2 c h
  | .ret _, c, h => by simp [walk1, Out.evs, calls] at h

/-- **A block's path calls its callees.** -/
theorem walk_callees : ∀ (ss : List Stmt) {c : Call}, c ∈ calls (walk σ ss).evs →
    c.f ∈ Stmt.blockCallees ss
  | [], c, h => by simp [walk, Out.evs, calls] at h
  | s :: ss, c, h => by
      rw [walk] at h
      simp only [Stmt.blockCallees, List.mem_append]
      rcases Out.calls_seq h with h | h
      · exact Or.inl (walk1_callees s h)
      · exact Or.inr (walk_callees ss h)

theorem walkArms_callees (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {c : Call},
    c ∈ calls (walkArms σ x j arms).evs → c.f ∈ Stmt.armsCallees arms
  | [], _, c, h => by simp [walkArms, Out.evs, calls] at h
  | a :: as, j, c, h => by
      unfold walkArms at h
      simp only [Stmt.armsCallees, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_callees a h)
      · exact Or.inr (walkArms_callees x as (j + 1) h)
end

end Syntax

/-- **`CallsIn` from the syntax.** -/
theorem callsIn_of_callees {P : Core.Program} {S : String → Prop}
    (h : ∀ f, S f → ∀ fn, P.find? f = some fn → ∀ g ∈ Stmt.blockCallees fn.body, S g) :
    CallsIn P S := by
  intro f hs fn hf σ es vs hw c hc
  have := walk_callees (σ := σ) fn.body (c := c) (by rw [hw]; exact hc)
  exact h f hs fn hf c.f this

end
end LeanVM.Guest.Memory
