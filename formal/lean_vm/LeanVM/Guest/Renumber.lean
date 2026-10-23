/-
  LeanVM.Guest.Renumber

  Renaming the values of a core function, and its dense renumbering: a function's relation and a
  program's call relation are invariant under both.
-/

module

public import LeanVM.Guest.Core
public import Std.Data.HashMap

/-!
# Renumbering a function's values

A value's name only tells two values apart: `Fn.Sem` quantifies over every valuation. So any
renaming with a left inverse (`Fn.sem_rename`) leaves a function's relation unchanged.

`Fn.renumber` is the one the guest's data uses: value `n` of `Fn.numbering` (the parameters
first, then every value in order of first occurrence, `Stmt.valsList`) becomes
`V.n n = ⟨[], 0, n⟩`, a parameter keeping its position. The numbering is computed with a hash
map, and the renaming checks it against the table (`renumberV`), so its left inverse
(`unnumberV`, the table) holds by construction. `Program.rel_map_renumber`: renumbering every
function leaves `Program.Rel` unchanged.
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters

@[expose] public section

/-! ## Renaming -/

def Dest.rename (r : V → V) : Dest → Dest
  | .stack cs => .stack (cs.map r)
  | .heap p off len => .heap (r p) off len

def Hint.rename (r : V → V) : Hint → Hint
  | .witness s d => .witness s (d.rename r)
  | .bits v st n d => .bits (r v) st n (d.rename r)
  | .bitsExp v n d => .bitsExp (r v) n (d.rename r)
  | .limbs v d => .limbs (r v) (d.map r)
  | .log2Ceil b n fl dst => .log2Ceil (b.rename r) n fl (r dst)
  | .inverse x d => .inverse (r x) (r d)
  | .alloc d n => .alloc (r d) n
  | .allocDyn d s => .allocDyn (r d) (r s)

def Atom.rename (r : V → V) : Atom → Atom
  | .const d c => .const (r d) c
  | .add d a b => .add (r d) (r a) (r b)
  | .mul d a b => .mul (r d) (r a) (r b)
  | .copy d s => .copy (r d) (r s)
  | .load d p off => .load (r d) (r p) off
  | .assertEq a b => .assertEq (r a) (r b)
  | .assertNe x inv p => .assertNe (r x) (r inv) (r p)
  | .rangeCheck x y t1 t2 k => .rangeCheck (r x) (r y) (r t1) (r t2) (r k)
  | .assertInK a b => .assertInK (r a) (r b)
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
      .blake2s (r m0) (r m1) (r m2) (r m3) (r cv0) (r cv1) (r o0) (r o1) (r md)
  | .frameAddr p run => .frameAddr (r p) (run.map r)
  | .hint h => .hint (h.rename r)

mutual
def Stmt.rename (r : V → V) : Stmt → Stmt
  | .atom a => .atom (a.rename r)
  | .ite c z n => .ite (r c) (Stmt.renameList r z) (Stmt.renameList r n)
  | .match_ x arms => .match_ (r x) (Stmt.renameArms r arms)
  | .call f args rets => .call f (args.map r) (rets.map r)
  | .callIf c f args => .callIf (r c) f (args.map r)
  | .dispatch x fs args rets => .dispatch (r x) fs (args.map r) (rets.map r)
  | .ret vs => .ret (vs.map r)

def Stmt.renameList (r : V → V) : List Stmt → List Stmt
  | [] => []
  | s :: ss => s.rename r :: Stmt.renameList r ss

def Stmt.renameArms (r : V → V) : List (List Stmt) → List (List Stmt)
  | [] => []
  | a :: as => Stmt.renameList r a :: Stmt.renameArms r as
end

def Fn.rename (r : V → V) (f : Fn) : Fn :=
  { f with params := f.params.map r, body := Stmt.renameList r f.body }

variable {C : CallRel} {rd : Reader}

theorem Atom.holds_rename (r : V → V) (σ : Val) (a : Atom) :
    (a.rename r).Holds rd σ = a.Holds rd (σ ∘ r) := by
  cases a <;> simp [Atom.rename, Atom.Holds]

mutual
theorem Stmt.holds_rename (r : V → V) (σ : Val) : ∀ (s : Stmt) (next : Prop)
    (kret : List E → Prop),
    Stmt.Holds C rd σ (s.rename r) next kret = Stmt.Holds C rd (σ ∘ r) s next kret
  | .atom a, _, _ => by simp only [Stmt.rename, Stmt.Holds, Atom.holds_rename]
  | .ite c z n, _, _ => by
      simp only [Stmt.rename, Stmt.Holds, Stmt.holdsList_rename r σ z,
        Stmt.holdsList_rename r σ n, Function.comp_apply]
  | .match_ x arms, _, _ => by
      simp only [Stmt.rename, Stmt.Holds, Stmt.holdsArms_rename r σ x arms]
  | .call .., _, _ => by simp [Stmt.rename, Stmt.Holds]
  | .callIf .., _, _ => by simp [Stmt.rename, Stmt.Holds]
  | .dispatch .., _, _ => by simp [Stmt.rename, Stmt.Holds]
  | .ret _, _, _ => by simp [Stmt.rename, Stmt.Holds]

theorem Stmt.holdsList_rename (r : V → V) (σ : Val) : ∀ (ss : List Stmt) (next : Prop)
    (kret : List E → Prop),
    Stmt.HoldsList C rd σ (Stmt.renameList r ss) next kret =
      Stmt.HoldsList C rd (σ ∘ r) ss next kret
  | [], _, _ => rfl
  | s :: ss, next, kret => by
      simp only [Stmt.renameList, Stmt.HoldsList]
      rw [Stmt.holds_rename r σ s, Stmt.holdsList_rename r σ ss]

theorem Stmt.holdsArms_rename (r : V → V) (σ : Val) (x : V) : ∀ (arms : List (List Stmt))
    (j : Nat) (next : Prop) (kret : List E → Prop),
    Stmt.HoldsArms C rd σ (r x) j (Stmt.renameArms r arms) next kret =
      Stmt.HoldsArms C rd (σ ∘ r) x j arms next kret
  | [], _, _, _ => rfl
  | a :: as, j, next, kret => by
      simp only [Stmt.renameArms, Stmt.HoldsArms]
      rw [Stmt.holdsList_rename r σ a, Stmt.holdsArms_rename r σ x as]
      rfl
end

/-- A renaming with a left inverse leaves a function's relation unchanged. -/
theorem Fn.sem_rename {r r' : V → V} (h : ∀ v, r' (r v) = v) (f : Fn) (args rets : List E) :
    (f.rename r).Sem C rd args rets ↔ f.Sem C rd args rets := by
  have hc : ∀ σ : Val, (σ ∘ r') ∘ r = σ := fun σ => funext fun v => by simp [h]
  constructor
  · rintro ⟨σ, hp, hb⟩
    refine ⟨σ ∘ r, ?_, ?_⟩
    · simpa [Fn.rename] using hp
    · rwa [Fn.rename, Stmt.holdsList_rename] at hb
  · rintro ⟨σ, hp, hb⟩
    refine ⟨σ ∘ r', ?_, ?_⟩
    · simp only [Fn.rename, List.map_map, hc, hp]
    · rw [Fn.rename, Stmt.holdsList_rename, hc]
      exact hb

/-! ## The dense numbering -/

def Dest.vals : Dest → List V
  | .stack cs => cs
  | .heap p _ _ => [p]

def Hint.vals : Hint → List V
  | .witness _ d => d.vals
  | .bits v _ _ d | .bitsExp v _ d => v :: d.vals
  | .limbs v d => v :: d
  | .log2Ceil b _ _ dst => b.vals ++ [dst]
  | .inverse x d => [x, d]
  | .alloc d _ => [d]
  | .allocDyn d s => [d, s]

def Atom.vals : Atom → List V
  | .const d _ => [d]
  | .add d a b | .mul d a b => [d, a, b]
  | .copy d s => [d, s]
  | .load d p _ => [d, p]
  | .assertEq a b | .assertInK a b => [a, b]
  | .assertNe x inv p => [x, inv, p]
  | .rangeCheck x y t1 t2 k => [x, y, t1, t2, k]
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md => [m0, m1, m2, m3, cv0, cv1, o0, o1, md]
  | .frameAddr p run => p :: run
  | .hint h => h.vals

mutual
/-- The values of a statement, in order. -/
def Stmt.vals : Stmt → List V
  | .atom a => a.vals
  | .ite c z n => c :: Stmt.valsList z ++ Stmt.valsList n
  | .match_ x arms => x :: Stmt.valsArms arms
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: args ++ rets
  | .ret vs => vs

def Stmt.valsList : List Stmt → List V
  | [] => []
  | s :: ss => s.vals ++ Stmt.valsList ss

def Stmt.valsArms : List (List Stmt) → List V
  | [] => []
  | a :: as => Stmt.valsList a ++ Stmt.valsArms as
end

/-- Value `n` of a renumbered function, as the guest's data writes it. -/
abbrev V.n (n : Nat) : V := ⟨[], 0, n⟩

/-- The numbering of a function's values: the parameters, then the other values in order of
first occurrence; the map gives a value's number, the table the value of a number. -/
def Fn.numbering (f : Fn) : Std.HashMap V Nat × Array V :=
  (f.params ++ Stmt.valsList f.body).foldl
    (fun (m, t) v => if m.contains v then (m, t) else (m.insert v t.size, t.push v)) ({}, #[])

/-- Value `v` by its number, when the table agrees; any other value moves off the numbered
ones. -/
def renumberV (m : Std.HashMap V Nat) (t : Array V) (v : V) : V :=
  match m[v]? with
  | some i => if t[i]? = some v then ⟨[], 0, i⟩ else ⟨.e :: v.path, v.tag, v.idx⟩
  | none => ⟨.e :: v.path, v.tag, v.idx⟩

/-- The value a renumbered name stands for. -/
def unnumberV (t : Array V) (w : V) : V :=
  if w.path = [] then t[w.idx]?.getD default else ⟨w.path.tail, w.tag, w.idx⟩

theorem unnumberV_renumberV (m : Std.HashMap V Nat) (t : Array V) (v : V) :
    unnumberV t (renumberV m t v) = v := by
  unfold renumberV
  split
  · split
    · next h => simp [unnumberV, h]
    · simp [unnumberV]
  · simp [unnumberV]

/-- A function with its values numbered densely. -/
def Fn.renumber (f : Fn) : Fn := f.rename (renumberV f.numbering.1 f.numbering.2)

theorem Fn.name_renumber (f : Fn) : f.renumber.name = f.name := rfl

theorem Fn.sem_renumber (f : Fn) (args rets : List E) :
    f.renumber.Sem C rd args rets ↔ f.Sem C rd args rets :=
  Fn.sem_rename (unnumberV_renumberV _ _) f args rets

theorem Program.find?_map_renumber (P : Program) (n : String) :
    Program.find? (P.map Fn.renumber) n = (P.find? n).map Fn.renumber := by
  simp only [Program.find?, List.find?_map]
  rfl

theorem Program.relN_map_renumber (P : Program) (rd : Reader) :
    ∀ n, Program.relN (P.map Fn.renumber) rd n = P.relN rd n
  | 0 => rfl
  | n + 1 => by
      funext f args rets
      simp only [Program.relN, Program.find?_map_renumber, Program.relN_map_renumber P rd n]
      apply propext
      constructor
      · rintro ⟨fn, h, hs⟩
        obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨g, hg, (Fn.sem_renumber g args rets).mp hs⟩
      · rintro ⟨g, hg, hs⟩
        exact ⟨g.renumber, by simp [hg], (Fn.sem_renumber g args rets).mpr hs⟩

/-- Renumbering every function leaves a program's call relation unchanged. -/
theorem Program.rel_map_renumber (P : Program) (rd : Reader) :
    Program.Rel (P.map Fn.renumber) rd = P.Rel rd := by
  funext f args rets
  simp only [Program.Rel, Program.relN_map_renumber]

end
end LeanVM.Guest.Core
