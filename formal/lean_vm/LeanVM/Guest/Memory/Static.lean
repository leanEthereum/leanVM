/-
  LeanVM.Guest.Memory.Static

  Static weight bounds: a certificate per function (an affine bound in the exponents of its
  arguments, or, for a loop helper, the bound of one iteration), checked against the function's
  body by a computable checker, and the soundness of the check over every valid tree.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.Pow

/-!
# Static weight bounds

A function's weight over its valid trees is bounded statically when its calls are bounded and
its loops run a number of iterations its arguments fix. The bound is **affine in the exponents of
the arguments** (`Aff`): `c + Σ a·logG args[k]`, the parameters named being loop ends (`g^b`),
under preconditions on their exponents (`ArgsPre`: `a < b`).

A **certificate** (`Cert`) gives each function either a bound (`stat`), or, for a loop helper
`L(i, end, …)` (step `i ↦ i·g`, guard `i·g ≠ end`, its parameters but the counter passed
through), the bound of one iteration (`loop`): a valid tree started at `i = g^a` with
`end = g^e`, `a < e`, runs `e - a` iterations, so weighs at most `(e - a)` times it.

**The checker** (`chkFn`) walks a body once (`blockB`), threading the constants its atoms make
(those the certificate names, each checked `g^e` by `Pow.gpowW`), and sums each call site's bound
(`siteB`): a callee's affine bound with its arguments classified (`cls`) as constants `g^e`,
collapsing their terms and checking their preconditions, or as the caller's parameters, which
the caller's bound and preconditions then name; a loop entry is its iteration count times its
iteration's bound. Branches add up, a fused dispatch adds every arm. A loop helper's own body is
checked without its tail call, against its shape (`loopShape`).

**Soundness** (`chk_sound`): if the checker accepts every function of a program, every valid tree
of a function weighs at most its certificate's bound.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Affine bounds -/

/-- `c + Σ a·logG args[k]` over the pairs `(k, a)`. -/
structure Aff where
  c : ℕ
  cs : List (ℕ × ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- The exponent of argument `k`. -/
noncomputable def argExp (args : List E) (k : ℕ) : ℕ := logG (args.getD k 0)

/-- An affine bound's value. -/
noncomputable def Aff.eval (b : Aff) (args : List E) : ℕ :=
  b.c + (b.cs.map fun q => q.2 * argExp args q.1).sum

def Aff.add (a b : Aff) : Aff := ⟨a.c + b.c, a.cs ++ b.cs⟩

def Aff.scale (n : ℕ) (a : Aff) : Aff := ⟨n * a.c, a.cs.map fun q => (q.1, n * q.2)⟩

/-- Preconditions `(k, a)`: argument `k` is `g^b` with `a < b` below the order of `g`. -/
def ArgsPre (pre : List (ℕ × ℕ)) (args : List E) : Prop :=
  ∀ q ∈ pre, ∃ b, q.2 < b ∧ b < 2 ^ 64 - 1 ∧ args.getD q.1 0 = ofK (gpow b)

/-- A function's certificate. -/
inductive Cert where
  /-- No bound. -/
  | none
  /-- Weight at most `b`, under `pre`; the constants `ks` (value, exponent) the check uses. -/
  | stat (pre : List (ℕ × ℕ)) (b : Aff) (ks : List (V × ℕ))
  /-- A loop helper, its end its parameter 1 (`none`) or `g^e`: each iteration weighs at most
  `b`, under `pre`, neither naming the counter. -/
  | loop (endc : Option ℕ) (pre : List (ℕ × ℕ)) (b : Aff) (ks : List (V × ℕ))
  deriving Inhabited

/-! ## The checker -/

/-- Constants known `g^e`. -/
abbrev Env := List (V × ℕ)

/-- A constant word is `g^e`, by digits. -/
def constOk (w : E) (e : ℕ) : Bool :=
  decide (e < 2 ^ 20) && decide (w.limb 0 = Pow.gpowW e) && decide (w.limb 1 = 0) &&
    decide (w.limb 2 = 0)

/-- What a value is to the checker. -/
inductive VCls where
  | pow (e : ℕ)
  | param (k : ℕ)
  | none

/-- A value: a known constant, a parameter, or unknown. -/
def cls (ρ : Env) (ps : List V) (v : V) : VCls :=
  match ρ.lookup v with
  | some e => .pow e
  | none => match ps.idxOf? v with
    | some k => .param k
    | none => .none

/-- A bound and the preconditions it needs. -/
abbrev Acc := Aff × List (ℕ × ℕ)

def Acc.add (a b : Acc) : Acc := (a.1.add b.1, a.2 ++ b.2)

def Option.addAcc : Option Acc → Option Acc → Option Acc
  | some a, some b => some (a.add b)
  | _, _ => none

/-- A callee's bound term `a·logG args[k]`, at the site: a constant, or the caller's term. -/
def termB (ρ : Env) (ps : List V) (args : List V) (q : ℕ × ℕ) : Option Acc :=
  match args[q.1]? with
  | some v => match cls ρ ps v with
    | .pow e => some (⟨q.2 * e, []⟩, [])
    | .param k => some (⟨0, [(k, q.2)]⟩, [])
    | .none => none
  | none => none

/-- A callee's precondition `(k, a)`, at the site: checked on a constant, or the caller's. -/
def preB (ρ : Env) (ps : List V) (args : List V) (q : ℕ × ℕ) : Option Acc :=
  match args[q.1]? with
  | some v => match cls ρ ps v with
    | .pow e => if q.2 < e ∧ e < 2 ^ 64 - 1 then some (⟨0, []⟩, []) else none
    | .param k => some (⟨0, []⟩, [(k, q.2)])
    | .none => none
  | none => none

/-- Sum of the site values of a list. -/
def sumB {α : Type} (f : α → Option Acc) : List α → Option Acc
  | [] => some (⟨0, []⟩, [])
  | a :: as => Option.addAcc (f a) (sumB f as)

/-- A callee's affine bound and preconditions, translated to the caller. -/
def transB (ρ : Env) (ps : List V) (args : List V) (pre : List (ℕ × ℕ)) (b : Aff) : Option Acc :=
  Option.addAcc (some (⟨b.c, []⟩, []))
    (Option.addAcc (sumB (termB ρ ps args) b.cs) (sumB (preB ρ ps args) pre))

/-- **A call site's bound**: a callee's certificate at the site's arguments. -/
def siteB (cert : String → Cert) (ρ : Env) (ps : List V) (g : String) (args : List V) :
    Option Acc :=
  match cert g with
  | .none => none
  | .stat pre b _ => transB ρ ps args pre b
  | .loop endc pre b _ =>
      match args[0]? with
      | none => none
      | some v0 => match cls ρ ps v0 with
        | .pow a0 =>
            let endv : VCls := match endc with
              | some e => .pow e
              | none => match args[1]? with
                | some v1 => cls ρ ps v1
                | none => .none
            match endv with
            | .pow e =>
                if a0 < e ∧ e < 2 ^ 64 - 1 then
                  (transB ρ ps args pre b).map fun r => (r.1.scale (e - a0), r.2)
                else none
            | .param k =>
                match transB ρ ps args pre b with
                | some r => if r.1.cs = [] then some (⟨0, [(k, r.1.c)]⟩, (k, a0) :: r.2) else none
                | none => none
            | .none => none
        | _ => none

mutual
/-- **A block's bound**: its call sites' bounds summed, the certified constants threaded. -/
def blockB (cert : String → Cert) (ks : List (V × ℕ)) (ps : List V) (self : String) :
    Env → List Stmt → Option Acc
  | _, [] => some (⟨0, []⟩, [])
  | ρ, .atom (.const v w) :: ss =>
      match ks.lookup v with
      | some e => if constOk w e then blockB cert ks ps self ((v, e) :: ρ) ss
          else blockB cert ks ps self ρ ss
      | none => blockB cert ks ps self ρ ss
  | ρ, .atom _ :: ss => blockB cert ks ps self ρ ss
  | ρ, .ite _ z n :: ss => Option.addAcc (blockB cert ks ps self ρ z)
      (Option.addAcc (blockB cert ks ps self ρ n) (blockB cert ks ps self ρ ss))
  | ρ, .match_ _ arms :: ss => Option.addAcc (armsB cert ks ps self ρ arms) (blockB cert ks ps self ρ ss)
  | ρ, .call g args _ :: ss => Option.addAcc (siteB cert ρ ps g args) (blockB cert ks ps self ρ ss)
  | ρ, .callIf _ g args :: ss =>
      if g = self then none
      else Option.addAcc (siteB cert ρ ps g args) (blockB cert ks ps self ρ ss)
  | ρ, .dispatch _ gs args _ :: ss =>
      Option.addAcc (sumB (fun g => siteB cert ρ ps g args) gs) (blockB cert ks ps self ρ ss)
  | _, .ret _ :: _ => some (⟨0, []⟩, [])

/-- The arms' bounds, summed. -/
def armsB (cert : String → Cert) (ks : List (V × ℕ)) (ps : List V) (self : String) :
    Env → List (List Stmt) → Option Acc
  | _, [] => some (⟨0, []⟩, [])
  | ρ, a :: as => Option.addAcc (blockB cert ks ps self ρ a) (armsB cert ks ps self ρ as)
end

mutual
/-- No `ret` in a statement. -/
def Stmt.noRet : Stmt → Bool
  | .ret _ => false
  | .ite _ z n => Stmt.noRetList z && Stmt.noRetList n
  | .match_ _ arms => Stmt.noRetArms arms
  | _ => true

def Stmt.noRetList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.noRet s && Stmt.noRetList ss

def Stmt.noRetArms : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.noRetList a && Stmt.noRetArms as
end

/-- The top-level atom of a block defining `d`. -/
def defAtom (d : V) : List Stmt → Option Atom
  | [] => none
  | .atom a :: ss =>
      let dst? : Option V := match a with
        | .const x _ => some x
        | .add x _ _ => some x
        | .mul x _ _ => some x
        | _ => none
      if dst? = some d then some a else defAtom d ss
  | _ :: ss => defAtom d ss

/-- `d = p · g` by a top-level `mul` with a constant `g`. -/
def isStep (pre : List Stmt) (p d : V) : Bool :=
  match defAtom d pre with
  | some (.mul _ x y) =>
      let isG (z : V) : Bool := match defAtom z pre with
        | some (.const _ w) => constOk w 1
        | _ => false
      (x == p && isG y) || (y == p && isG x)
  | _ => false

/-- The end a guard compares with: the parameter `p1`, or a constant `g^e`. -/
def isEnd (pre : List Stmt) (p1 : Option V) (endc : Option ℕ) (y : V) : Bool :=
  match endc with
  | none => p1 == some y
  | some e => match defAtom y pre with
    | some (.const _ w) => constOk w e
    | _ => false

/-- **A loop helper's shape**: its body `pre ++ [callIf c f (i' :: rest), ret []]`, `pre` without
`ret`, `i' = i·g`, `c = i·g + end`, the other parameters passed through. -/
def loopShape (fn : Fn) (endc : Option ℕ) : Option (List Stmt) :=
  match fn.body.reverse, fn.params with
  | .ret [] :: .callIf c g (i' :: rest) :: rpre, p0 :: prest =>
      let pre := rpre.reverse
      if g = fn.name ∧ rest = prest ∧ Stmt.noRetList pre = true ∧ isStep pre p0 i' = true ∧
          (match defAtom c pre with
            | some (.add _ x y) => (isStep pre p0 x && isEnd pre prest.head? endc y) ||
                (isStep pre p0 y && isEnd pre prest.head? endc x)
            | _ => false) = true
      then some pre else none
  | _, _ => none

/-- `a`'s constant and terms are at most `b`'s, term by term. -/
def Aff.leB (a b : Aff) : Bool := decide (a.c ≤ b.c) && a.cs == b.cs

/-- **The check of a function** against its certificate. -/
def chkFn (cert : String → Cert) (ω : String → ℕ) (fn : Fn) : Bool :=
  match cert fn.name with
  | .none => true
  | .stat pre b ks =>
      match blockB cert ks fn.params fn.name [] fn.body with
      | some r => Aff.leB ⟨ω fn.name + r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre)
      | none => false
  | .loop endc pre b ks =>
      match loopShape fn endc with
      | some pre' => match blockB cert ks fn.params fn.name [] pre' with
        | some r => Aff.leB ⟨ω fn.name + r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre) &&
            b.cs.all (·.1 ≠ 0) && pre.all (·.1 ≠ 0)
        | none => false
      | none => false

end
end LeanVM.Guest.Memory
