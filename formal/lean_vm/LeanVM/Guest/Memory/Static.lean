/-
  LeanVM.Guest.Memory.Static

  Static weight bounds: a certificate per function (an affine bound in the exponents of its
  arguments, or, for a loop helper, the bound of one iteration), checked against the function's
  body by a computable checker, and the soundness of the check over every valid tree.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.Pow
public import LeanVM.Guest.Memory.SelArm

/-!
# Static weight bounds

A function's weight over its valid trees is bounded statically when its calls are bounded and
its loops run a number of iterations its arguments fix. The bound is **affine in the exponents of
the arguments** (`Aff`): `c + Σ a·logG args[k]`, the parameters named being loop ends (`g^b`),
under preconditions on their exponents (`ArgsPre`: `a < b`).

A **certificate** (`Cert`) gives each function either a bound (`stat`), or, for a loop helper
`L(i, end, …)` (step `i ↦ i·g`, guard `i·g ≠ end`, its parameters but the counter passed
through), the bound of one iteration (`loop`): a valid tree started at `i = g^a` with
`end = g^e`, `a < e`, runs `e - a` iterations, so weighs at most `(e - a)` times it, and,
counting words, its run's one phantom (its last iteration's untaken tail call) more.

**The checker** (`chkFn`) walks a body once (`blockB`), threading the constants its atoms make
(those the certificate names, each checked `g^e` by `Pow.gpowN`, and their copies), and sums each call site's bound
(`siteB`): a callee's affine bound with its arguments classified (`cls`) as constants `g^e`,
collapsing their terms and checking their preconditions, or as the caller's parameters, which
the caller's bound and preconditions then name; a loop entry is its iteration count times its
iteration's bound, and, counting words, its run's one phantom frame. Exclusive branches take the larger bound: an `ite`'s two sides, a `match`'s arms,
a fused dispatch's callees. A loop helper's own body is
checked without its tail call, against its shape (`loopShape`). A `stat` certificate a body's walk misses may
be met by the body at each arm of its first top-level selector (`selSplit`, the path being one of theirs): the values a
`match` binds per arm, constants in each, are then known after it. Counting words (`α`), each
`HeapBuf` adds its size (`atomB`): `n` for `HeapBuf(n)`, a bound on the exponent of a dynamic
one's size (`bnd`): a constant's, a parameter's, or a tracked product `x·g^c`'s, `x`'s bound plus
`c` (`logG_mul_le`), threaded in the environment's bounds (`BEnv`); a `callIf` adds its callee's frame, which an
untaken one leaves as a phantom (`phB`, the weight looked up by `wl`), and a loop's iteration its
own frame once: a run's last iteration leaves its untaken tail call, a phantom of the helper, the
run's only one, which the run's bound, and so a call site, adds once. Counting words at the frame sizes, the cost is then the words a tree
allocates.

**Soundness** (`chk_sound`): if the checker accepts every function of a program but those of a set
`X`, whose trees satisfy their certificates by hypothesis, every valid tree of a function costs at
most its certificate's bound: its weight, and counting words its paths' `HeapBuf`s and its
phantoms' frames (`Tree.cost`).
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

/-- The bound from which a precondition's `a` reads `a - gT ≤ b` (past every exponent). -/
def gT : ℕ := 2 ^ 64

/-- A precondition's order: `a < b`, or `a - gT ≤ b` for `a ≥ gT`. -/
def preLt (a b : ℕ) : Bool := bif Nat.ble gT a then Nat.ble (a - gT) b else Nat.blt a b

/-- Preconditions `(k, a)`: argument `k` is `g^b` with `a < b` (`a - gT ≤ b` for `a ≥ gT`) below the order of
`g`. -/
def ArgsPre (pre : List (ℕ × ℕ)) (args : List E) : Prop :=
  ∀ q ∈ pre, ∃ b, preLt q.2 b = true ∧ b < 2 ^ 64 - 1 ∧ args.getD q.1 0 = ofK (addressOfIndex b)

/-- A function's certificate. -/
inductive Cert where
  /-- No bound. -/
  | none
  /-- Weight at most `b`, under `pre`; the constants `ks` (value, exponent) the check uses, an
  exponent `trackE` marking a value whose exponent bound it tracks instead. -/
  | stat (pre : List (ℕ × ℕ)) (b : Aff) (ks : List (V × ℕ))
  /-- A loop helper, its end its parameter 1 (`none`) or `g^e`: each iteration weighs at most
  `b`, under `pre`, neither naming the counter; counting words, the run's phantom frame more. -/
  | loop (endc : Option ℕ) (pre : List (ℕ × ℕ)) (b : Aff) (ks : List (V × ℕ))
  deriving Inhabited

/-! ## The checker -/

/-- Constants known `g^e`. -/
abbrev Env := List (V × ℕ)

/-- Values whose exponent is bounded: `logG (σ v) ≤ b`. -/
abbrev BEnv := List (V × Aff)

/-- The exponent in a certificate's constants marking a value whose exponent bound the check
tracks (no constant passes `constOk` at it). -/
def trackE : ℕ := 2 ^ 20

/-- The exponent in a certificate's constants marking a loop's guard `d = x + y`, `x` a known constant `g^a`: the
checker keeps it as a bound tagged by `guardOf`. -/
def guardE : ℕ := 2 ^ 20 + 1

/-- A tagged bound `⟨gT + a, [(k, 0)]⟩`: the value is `g^a + [V.n k]` (a loop's entry guard), no exponent bound. -/
def guardOf (b : Aff) : Option (ℕ × ℕ) :=
  bif Nat.ble gT b.c then (match b.cs with
    | [(k, 0)] => some (b.c - gT, k)
    | _ => none) else none

/-- A constant word is `g^e`: the word `2^e` below the first reduction, by digits above. -/
def constOk (w : E) (e : ℕ) : Bool :=
  decide (e < 2 ^ 20) && decide (w.limb 1 = 0) &&
    (if e < 64 then decide (w.limb 0 = K.ofBits (2 ^ e)) else decide (w.limb 0 = K.ofBits (Pow.gpowN e)))

/-- `lookupV`, compiled. -/
def lookupVC {α : Type} (v : V) : List (V × α) → Option α
  | [] => none
  | q :: l => bif Nat.beq v.idx q.1.idx && decide (v = q.1) then some q.2 else lookupVC v l

/-- A value's entry, its index compared first; on the recursor, which the kernel unfolds in fewer steps
than the equation compiler's `brecOn` (`lookupVC` where compiled). -/
noncomputable def lookupV {α : Type} (v : V) (l : List (V × α)) : Option α :=
  l.rec none fun q _ r => bif Nat.beq v.idx q.1.idx && decide (v = q.1) then some q.2 else r

@[csimp] theorem lookupV_eq_lookupVC : @lookupV = @lookupVC := by
  funext α v l
  induction l with
  | nil => rfl
  | cons q l ih => exact congrArg (cond _ _) ih

theorem lookupV_mem {α : Type} {v : V} {a : α} : ∀ {l : List (V × α)}, lookupV v l = some a → (v, a) ∈ l
  | [], h => by cases h
  | q :: l, h => by
      by_cases hq : (Nat.beq v.idx q.1.idx && decide (v = q.1)) = true
      · have hv : v = q.1 := by simp only [Bool.and_eq_true, decide_eq_true_eq] at hq; exact hq.2
        have h' : some q.2 = some a := by
          change (bif _ then some q.2 else _) = some a at h
          rwa [hq] at h
        cases h'; rw [hv]; exact List.mem_cons_self
      · rw [Bool.not_eq_true] at hq
        change (bif _ then some q.2 else lookupV v l) = some a at h
        rw [hq] at h
        exact List.mem_cons_of_mem _ (lookupV_mem h)

/-- `vidx`, compiled. -/
def vidxC (v : V) : List V → ℕ → Option ℕ
  | [], _ => none
  | p :: ps, k => bif Nat.beq v.idx p.idx && decide (v = p) then some k else vidxC v ps (k + 1)

/-- A value's position among the parameters from `k`, its index compared first; on the recursor, as
`lookupV` (`vidxC` where compiled). -/
noncomputable def vidx (v : V) (ps : List V) (k : ℕ) : Option ℕ :=
  List.rec (motive := fun _ ↦ ℕ → Option ℕ) (fun _ ↦ none)
    (fun p _ r k ↦ bif Nat.beq v.idx p.idx && decide (v = p) then some k else r (k + 1)) ps k

@[csimp] theorem vidx_eq_vidxC : @vidx = @vidxC := by
  funext v ps k
  induction ps generalizing k with
  | nil => rfl
  | cons p ps ih => exact congrArg (cond _ _) (ih (k + 1))

/-- What a value is to the checker. -/
inductive VCls where
  | pow (e : ℕ)
  | param (k : ℕ)
  | none

/-- A value: a known constant, a parameter, or unknown. -/
def cls (ρ : Env) (ps : List V) (v : V) : VCls :=
  match lookupV v ρ with
  | some e => .pow e
  | none => match vidx v ps 0 with
    | some k => .param k
    | none => .none

/-- A bound on a value's exponent: tracked, a known constant's, or a parameter's. -/
def bnd (ρ : Env × BEnv) (ps : List V) (v : V) : Option Aff :=
  match lookupV v ρ.2 with
  | some b => bif (guardOf b).isSome then none else some b
  | none => match cls ρ.1 ps v with
    | .pow e => some ⟨e, []⟩
    | .param k => some ⟨0, [(k, 1)]⟩
    | .none => none

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
    | .pow e => if preLt q.2 e = true ∧ e < 2 ^ 64 - 1 then some (⟨0, []⟩, []) else none
    | .param k => some (⟨0, []⟩, [(k, q.2)])
    | .none => none
  | none => none

/-- **The larger of two bounds**: the larger constant, both terms (an upper bound on either, the
terms being nonnegative), both preconditions. -/
def Acc.join (a b : Acc) : Acc := (⟨max a.1.c b.1.c, a.1.cs ++ b.1.cs⟩, a.2 ++ b.2)

def Option.maxAcc : Option Acc → Option Acc → Option Acc
  | some a, some b => some (a.join b)
  | _, _ => none

/-- The larger of the site values of a list, `0` for none. -/
def maxB {α : Type} (f : α → Option Acc) : List α → Option Acc
  | [] => some (⟨0, []⟩, [])
  | a :: as => Option.maxAcc (f a) (maxB f as)

/-- Sum of the site values of a list. -/
def sumB {α : Type} (f : α → Option Acc) : List α → Option Acc
  | [] => some (⟨0, []⟩, [])
  | a :: as => Option.addAcc (f a) (sumB f as)

/-- A callee's affine bound and preconditions, translated to the caller. -/
def transB (ρ : Env) (ps : List V) (args : List V) (pre : List (ℕ × ℕ)) (b : Aff) : Option Acc :=
  Option.addAcc (some (⟨b.c, []⟩, []))
    (Option.addAcc (sumB (termB ρ ps args) b.cs) (sumB (preB ρ ps args) pre))

/-- The zero bound. -/
def Acc.zero : Acc := (⟨0, []⟩, [])

/-- A `callIf`'s phantom, counting words: its callee's frame, by `wl`. -/
def phB (wl : String → Option ℕ) (α : Bool) (g : String) : Option Acc :=
  if α then (wl g).map fun n => (⟨n, []⟩, []) else some Acc.zero

/-- **A call site's bound**: a callee's certificate at the site's arguments; a loop helper's run,
its iterations at its certificate's bound and, counting words, its run's one phantom frame (`phB`)
once. -/
def siteB (cert : String → Cert) (wl : String → Option ℕ) (α : Bool) (ρ : Env) (ps : List V)
    (g : String) (args : List V) : Option Acc :=
  match cert g with
  | .none => none
  | .stat pre b _ => transB ρ ps args pre b
  | .loop endc pre b _ =>
      match phB wl α g with
      | none => none
      | some p =>
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
                    (transB ρ ps args pre b).map fun r => ((r.1.scale (e - a0)).add p.1, r.2)
                  else none
              | .param k =>
                  match transB ρ ps args pre b with
                  | some r => if r.1.cs = [] then some ((⟨0, [(k, r.1.c)]⟩ : Aff).add p.1, (k, a0) :: r.2)
                    else none
                  | none => none
              | .none => none
          | _ => none

/-- **A loop's guard `d = x + y`** marked in the certificate's constants (`guardE`), `x` a known constant `g^a`
and `y` a value `V.n k`: kept as the tagged bound `⟨gT + a, [(k, 0)]⟩`. -/
def guardAtom (ks : List (V × ℕ)) (ρ : Env × BEnv) (d x y : V) : Env × BEnv :=
  if lookupV d ks == some guardE then
    match lookupV x ρ.1 with
    | some a => bif selIs y.idx y then (ρ.1, (d, ⟨gT + a, [(y.idx, 0)]⟩) :: ρ.2) else ρ
    | none => ρ
  else ρ

/-- **A `callIf` site's guard**: its condition a tagged bound (`guardOf`), `g^a + [V.n k]`. -/
def guardB (β : BEnv) (c : V) : Option (ℕ × ℕ) :=
  match lookupV c β with
  | some b => guardOf b
  | none => none

/-- **A loop entered by a `callIf` on its guard** `g^a0 + end` (`guardB`), its start `g^a0`: taken, the end is not
the start, so the run's iterations are `e - a0` for an end `g^e`, `a0 ≤ e` (or a caller's parameter at least
`a0`, the precondition `(k, gT + a0)`); `none` where it does not apply. -/
def siteBL (cert : String → Cert) (wl : String → Option ℕ) (α : Bool) (ρ : Env) (ps : List V)
    (g : String) (args : List V) (a0 k : ℕ) : Option Acc :=
  match cert g, phB wl α g, args[0]?, args[1]? with
  | .loop none pre b _, some p, some v0, some v1 =>
      match cls ρ ps v0 with
      | .pow a => if a = a0 ∧ v1 = V.n k then
          match cls ρ ps v1 with
          | .pow e => if a0 ≤ e ∧ e < 2 ^ 64 - 1 then
              (transB ρ ps args pre b).map fun r => ((r.1.scale (e - a0)).add p.1, r.2)
            else none
          | .param k' => match transB ρ ps args pre b with
            | some r => if r.1.cs = [] then some ((⟨0, [(k', r.1.c)]⟩ : Aff).add p.1, (k', gT + a0) :: r.2)
              else none
            | none => none
          | .none => none
        else none
      | _ => none
  | _, _, _, _ => none

/-- **A `callIf` site's bound**: on its guard (`guardB`), the loop rule `siteBL` where it applies, else `siteB`. -/
def siteBC (cert : String → Cert) (wl : String → Option ℕ) (α : Bool) (ρ : Env × BEnv) (ps : List V)
    (c : V) (g : String) (args : List V) : Option Acc :=
  match guardB ρ.2 c with
  | some (a0, k) => match siteBL cert wl α ρ.1 ps g args a0 k with
    | some r => some r
    | none => siteB cert wl α ρ.1 ps g args
  | none => siteB cert wl α ρ.1 ps g args

/-- The preconditions that the arguments a bound names are powers of `g` (`(k, gT)`: `g^b`, `0 ≤ b`), under
which a value of that bound built from powers and those arguments is a power. -/
def powPre (b : Aff) : List (ℕ × ℕ) := b.cs.map fun q => (q.1, gT)

/-- **An atom's bound and the constants after it**: a certified constant joins them, and a copy of one; counting
words (`α`), a tracked product `d = x·g^c` is bounded by `x`'s bound plus `c`, and `d = x·y` by the sum of their
bounds where the arguments `x`'s names are powers (`powPre`), a `HeapBuf(n)` adds `n` and a dynamic one its size's
exponent bound (`bnd`), or fails. -/
def atomB (α : Bool) (ks : List (V × ℕ)) (ps : List V) (ρ : Env × BEnv) :
    Atom → Option (Acc × (Env × BEnv))
  | .const v w => match lookupV v ks with
      | some e => if constOk w e then some (Acc.zero, ((v, e) :: ρ.1, ρ.2)) else some (Acc.zero, ρ)
      | none => some (Acc.zero, ρ)
  | .copy d s => match cls ρ.1 ps s with
      | .pow e => some (Acc.zero, ((d, e) :: ρ.1, ρ.2))
      | _ => some (Acc.zero, ρ)
  | .mul d x y =>
      if α && lookupV d ks == some trackE then
        match bnd ρ ps x, cls ρ.1 ps y with
        | some b, .pow c => bif (guardOf (b.add ⟨c, []⟩)).isSome then none
            else some (Acc.zero, (ρ.1, (d, b.add ⟨c, []⟩) :: ρ.2))
        | some b, _ => match bnd ρ ps y with
          | some b' => bif (guardOf (b.add b')).isSome then none
              else some ((⟨0, []⟩, powPre b), (ρ.1, (d, b.add b') :: ρ.2))
          | none => none
        | _, _ => none
      else some (Acc.zero, ρ)
  | .add d x y => some (Acc.zero, guardAtom ks ρ d x y)
  | .hint (.alloc _ n) => some (if α then (⟨n, []⟩, []) else Acc.zero, ρ)
  | .hint (.allocDyn _ s) =>
      if α then
        match bnd ρ ps s with
        | some b => some ((b, []), ρ)
        | none => none
      else some (Acc.zero, ρ)
  | _ => some (Acc.zero, ρ)


mutual
/-- **A block's bound**: its call sites' bounds (and, counting words, its `HeapBuf`s) summed, the
certified constants threaded. -/
def blockB (cert : String → Cert) (wl : String → Option ℕ) (α : Bool) (ks : List (V × ℕ)) (ps : List V)
    (self : String) :
    Env × BEnv → List Stmt → Option Acc
  | _, [] => some (⟨0, []⟩, [])
  | ρ, .atom a :: ss =>
      match atomB α ks ps ρ a with
      | some (r, ρ') => Option.addAcc (some r) (blockB cert wl α ks ps self ρ' ss)
      | none => none
  | ρ, .ite _ z n :: ss => Option.addAcc
      (Option.maxAcc (blockB cert wl α ks ps self ρ z) (blockB cert wl α ks ps self ρ n))
      (blockB cert wl α ks ps self ρ ss)
  | ρ, .match_ _ arms :: ss =>
      Option.addAcc (armsB cert wl α ks ps self ρ arms) (blockB cert wl α ks ps self ρ ss)
  | ρ, .call g args _ :: ss => Option.addAcc (siteB cert wl α ρ.1 ps g args) (blockB cert wl α ks ps self ρ ss)
  | ρ, .callIf c g args :: ss =>
      if g = self then none
      else Option.addAcc (siteBC cert wl α ρ ps c g args)
        (Option.addAcc (phB wl α g) (blockB cert wl α ks ps self ρ ss))
  | ρ, .dispatch _ gs args _ :: ss =>
      Option.addAcc (maxB (fun g => siteB cert wl α ρ.1 ps g args) gs) (blockB cert wl α ks ps self ρ ss)
  | _, .ret _ :: _ => some (⟨0, []⟩, [])

/-- The arms' bounds, summed. -/
def armsB (cert : String → Cert) (wl : String → Option ℕ) (α : Bool) (ks : List (V × ℕ)) (ps : List V)
    (self : String) :
    Env × BEnv → List (List Stmt) → Option Acc
  | _, [] => some (⟨0, []⟩, [])
  | ρ, a :: as => Option.maxAcc (blockB cert wl α ks ps self ρ a) (armsB cert wl α ks ps self ρ as)
end

/-- **`blockB` on the recursor**, for the kernel: each statement gives its bound and the
constants after it, or stops the block (`ret`) (`stmtR`, `blockR`, `armsR`, equal to `blockB`
by `blockR_eq`). -/
noncomputable def stmtR (cert : String → Cert) (wl : String → Option ℕ) (α : Bool) (ks : List (V × ℕ))
    (ps : List V) (self : String) :
    Stmt → Env × BEnv → Option (Acc × Option (Env × BEnv)) :=
  @Stmt.rec (fun _ => Env × BEnv → Option (Acc × Option (Env × BEnv))) (fun _ => Env × BEnv → Option Acc)
    (fun _ => Env × BEnv → Option Acc)
    (fun a ρ => (atomB α ks ps ρ a).map fun q => (q.1, some q.2))
    (fun _ _ _ hz hn ρ => (Option.maxAcc (hz ρ) (hn ρ)).map fun r => (r, some ρ))
    (fun _ _ ha ρ => (ha ρ).map fun r => (r, some ρ))
    (fun g args _ ρ => (siteB cert wl α ρ.1 ps g args).map fun r => (r, some ρ))
    (fun c g args ρ => if g = self then none
      else (Option.addAcc (siteBC cert wl α ρ ps c g args) (phB wl α g)).map fun r => (r, some ρ))
    (fun _ gs args _ ρ => (maxB (fun g => siteB cert wl α ρ.1 ps g args) gs).map fun r => (r, some ρ))
    (fun _ _ => some (Acc.zero, none))
    (fun _ => some Acc.zero)
    (fun _ _ hs hss ρ => match hs ρ with
      | none => none
      | some (r, some ρ') => Option.addAcc (some r) (hss ρ')
      | some (r, none) => some r)
    (fun _ => some Acc.zero)
    (fun _ _ ha has ρ => Option.maxAcc (ha ρ) (has ρ))

/-- `stmtR` of a block. -/
noncomputable def blockR (cert : String → Cert) (wl : String → Option ℕ) (α : Bool) (ks : List (V × ℕ))
    (ps : List V) (self : String) :
    List Stmt → Env × BEnv → Option Acc :=
  @Stmt.rec_1 (fun _ => Env × BEnv → Option (Acc × Option (Env × BEnv))) (fun _ => Env × BEnv → Option Acc)
    (fun _ => Env × BEnv → Option Acc)
    (fun a ρ => (atomB α ks ps ρ a).map fun q => (q.1, some q.2))
    (fun _ _ _ hz hn ρ => (Option.maxAcc (hz ρ) (hn ρ)).map fun r => (r, some ρ))
    (fun _ _ ha ρ => (ha ρ).map fun r => (r, some ρ))
    (fun g args _ ρ => (siteB cert wl α ρ.1 ps g args).map fun r => (r, some ρ))
    (fun c g args ρ => if g = self then none
      else (Option.addAcc (siteBC cert wl α ρ ps c g args) (phB wl α g)).map fun r => (r, some ρ))
    (fun _ gs args _ ρ => (maxB (fun g => siteB cert wl α ρ.1 ps g args) gs).map fun r => (r, some ρ))
    (fun _ _ => some (Acc.zero, none))
    (fun _ => some Acc.zero)
    (fun _ _ hs hss ρ => match hs ρ with
      | none => none
      | some (r, some ρ') => Option.addAcc (some r) (hss ρ')
      | some (r, none) => some r)
    (fun _ => some Acc.zero)
    (fun _ _ ha has ρ => Option.maxAcc (ha ρ) (has ρ))

/-- `stmtR` of arms. -/
noncomputable def armsR (cert : String → Cert) (wl : String → Option ℕ) (α : Bool) (ks : List (V × ℕ))
    (ps : List V) (self : String) :
    List (List Stmt) → Env × BEnv → Option Acc :=
  @Stmt.rec_2 (fun _ => Env × BEnv → Option (Acc × Option (Env × BEnv))) (fun _ => Env × BEnv → Option Acc)
    (fun _ => Env × BEnv → Option Acc)
    (fun a ρ => (atomB α ks ps ρ a).map fun q => (q.1, some q.2))
    (fun _ _ _ hz hn ρ => (Option.maxAcc (hz ρ) (hn ρ)).map fun r => (r, some ρ))
    (fun _ _ ha ρ => (ha ρ).map fun r => (r, some ρ))
    (fun g args _ ρ => (siteB cert wl α ρ.1 ps g args).map fun r => (r, some ρ))
    (fun c g args ρ => if g = self then none
      else (Option.addAcc (siteBC cert wl α ρ ps c g args) (phB wl α g)).map fun r => (r, some ρ))
    (fun _ gs args _ ρ => (maxB (fun g => siteB cert wl α ρ.1 ps g args) gs).map fun r => (r, some ρ))
    (fun _ _ => some (Acc.zero, none))
    (fun _ => some Acc.zero)
    (fun _ _ hs hss ρ => match hs ρ with
      | none => none
      | some (r, some ρ') => Option.addAcc (some r) (hss ρ')
      | some (r, none) => some r)
    (fun _ => some Acc.zero)
    (fun _ _ ha has ρ => Option.maxAcc (ha ρ) (has ρ))

mutual
/-- No `ret` in a statement. -/
def Stmt.noRet : Stmt → Bool
  | .ret _ => false
  | .ite _ z n => Stmt.noRetListS z && Stmt.noRetListS n
  | .match_ _ arms => Stmt.noRetArms arms
  | _ => true

def Stmt.noRetListS : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.noRet s && Stmt.noRetListS ss

def Stmt.noRetArms : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.noRetListS a && Stmt.noRetArms as
end

/-- Equality of values, their indices compared first: the derived `DecidableEq V` compares their paths
first, which the kernel walks slowly. -/
def vBeq (a b : V) : Bool := Nat.beq a.idx b.idx && Nat.beq a.tag b.tag && decide (a.path = b.path)

theorem vBeq_iff {a b : V} : vBeq a b = true ↔ a = b := by
  obtain ⟨p, t, i⟩ := a
  obtain ⟨p', t', i'⟩ := b
  simp only [vBeq, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq, V.mk.injEq]
  tauto

/-- Atom `a` defines `d`: a constant, a sum or a product into `d`. -/
def dstIs (d : V) : Atom → Bool
  | .const x _ => vBeq x d
  | .add x _ _ => vBeq x d
  | .mul x _ _ => vBeq x d
  | _ => false

/-- `defAtom`, compiled. -/
def defAtomC (d : V) : List Stmt → Option Atom
  | [] => none
  | .atom a :: ss => bif dstIs d a then some a else defAtomC d ss
  | _ :: ss => defAtomC d ss

/-- The top-level atom of a block defining `d`, on the recursor (`defAtomC` where compiled). -/
noncomputable def defAtom (d : V) (l : List Stmt) : Option Atom :=
  List.rec (motive := fun _ ↦ Option Atom) none
    (fun s _ r ↦ match s with
      | .atom a => bif dstIs d a then some a else r
      | _ => r) l

@[csimp] theorem defAtom_eq_defAtomC : @defAtom = @defAtomC := by
  funext d l
  induction l with
  | nil => rfl
  | cons s l ih => cases s <;> simp only [defAtom, defAtomC] at ih ⊢ <;> rw [ih]

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

/-- A loop helper's shape but its `ret`-freedom (`loopShape`): its body
`pre ++ [callIf c f (i' :: rest), ret []]`, `i' = i·g`, `c = i·g + end`, the other parameters passed
through. -/
def loopTail (fn : Fn) (endc : Option ℕ) : Option (List Stmt) :=
  match fn.body.reverse, fn.params with
  | .ret [] :: .callIf c g (i' :: rest) :: rpre, p0 :: prest =>
      let pre := rpre.reverse
      if g = fn.name ∧ rest = prest ∧ isStep pre p0 i' = true ∧
          (match defAtom c pre with
            | some (.add _ x y) => (isStep pre p0 x && isEnd pre prest.head? endc y) ||
                (isStep pre p0 y && isEnd pre prest.head? endc x)
            | _ => false) = true
      then some pre else none
  | _, _ => none

/-- **A loop helper's shape** (`loopTail`), `pre` without `ret`. -/
def loopShape (fn : Fn) (endc : Option ℕ) : Option (List Stmt) :=
  (loopTail fn endc).filter Stmt.noRetListS

/-- A search tree by index. -/
inductive NTree (α : Type) where
  | leaf
  | node (k : ℕ) (v : α) (l r : NTree α)

/-- The value of an index. -/
def NTree.find {α : Type} : NTree α → ℕ → Option α
  | .leaf, _ => none
  | .node k v l r, i => if Nat.beq i k then some v else if Nat.blt i k then l.find i else r.find i

/-- Every value of the tree satisfies `p`. -/
def NTree.all {α : Type} (p : α → Bool) : NTree α → Bool
  | .leaf => true
  | .node _ v l r => p v && l.all p && r.all p

theorem NTree.find_all {α : Type} {p : α → Bool} : ∀ {t : NTree α} {k : ℕ} {v : α}, t.all p = true →
    t.find k = some v → p v = true
  | .leaf, _, _, _, h => by simp [NTree.find] at h
  | .node k' v' l r, k, v, ha, h => by
      simp only [NTree.all, Bool.and_eq_true] at ha
      simp only [NTree.find] at h
      split_ifs at h
      · cases h; exact ha.1.1
      · exact NTree.find_all ha.1.2 h
      · exact NTree.find_all ha.2 h

/-- `a`'s constant and terms are at most `b`'s, term by term. -/
def Aff.leB (a b : Aff) : Bool := decide (a.c ≤ b.c) && a.cs == b.cs

/-- A `stat` certificate's check of a body of `fn`. -/
noncomputable def statB (look : String → Cert) (wl : String → Option ℕ) (α : Bool) (pre : List (ℕ × ℕ)) (b : Aff)
    (ks : List (V × ℕ)) (w : ℕ) (fn : Fn) (body : List Stmt) : Bool :=
  match blockR look wl α ks fn.params fn.name body ([], []) with
  | some r => Aff.leB ⟨w + r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre)
  | none => false

/-- **The check of a function** against its certificate `own`, its frame weighing `w`, its
callees' certificates by `look`, counting words if `α`. -/
noncomputable def chkFn (look : String → Cert) (wl : String → Option ℕ) (α : Bool) (own : Cert) (w : ℕ)
    (fn : Fn) : Bool :=
  match own with
  | .none => true
  | .stat pre b ks => statB look wl α pre b ks w fn fn.body || selSplit fn.body (statB look wl α pre b ks w fn)
  | .loop endc pre b ks =>
      match loopShape fn endc with
      | some pre' => match blockR look wl α ks fn.params fn.name pre' ([], []) with
        | some r => Aff.leB ⟨w + r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre) &&
            b.cs.all (·.1 ≠ 0) && pre.all (·.1 ≠ 0)
        | none => false
      | none => false

/-- A lookup agreeing with `cert` wherever it gives a certificate. -/
def LookOk (look cert : String → Cert) : Prop := ∀ g, look g ≠ .none → look g = cert g

/-- A weight lookup bounding `ω` wherever it gives a weight. -/
def WlOk (wl : String → Option ℕ) (ω : String → ℕ) : Prop := ∀ g n, wl g = some n → ω g ≤ n

/-- **A program checked but for the functions of `X`**: every other function passes against its
certificate, by some lookups of its callees' certificates and weights agreeing with `cert` and
`ω`. -/
def CheckedExcept (P : Core.Program) (α : Bool) (cert : String → Cert) (ω : String → ℕ)
    (X : String → Prop) : Prop :=
  ∀ fn ∈ P, ¬ X fn.name → ∃ look wl, LookOk look cert ∧ WlOk wl ω ∧
    chkFn look wl α (cert fn.name) (ω fn.name) fn = true

/-- **A checked program**: every function passes. -/
def Checked (P : Core.Program) (α : Bool) (cert : String → Cert) (ω : String → ℕ) : Prop :=
  CheckedExcept P α cert ω fun _ => False

end
end LeanVM.Guest.Memory
