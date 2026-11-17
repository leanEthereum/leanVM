/-
  LeanVM.Compiler.Sound.Spec

  The statements of the back end's correctness: per pass, per function, whole program.
-/

module

public import LeanVM.Compiler.Sound.Lowered
public import LeanVM.Compiler.Sound.Pool
public import LeanVM.Compiler.Sound.Fills
public import LeanVM.Compiler.Compile

/-!
# What the back end's correctness says

The definitions every statement about the back end is made of, and the statements themselves as
propositions. A proposition proved is a theorem of that type in another module of this directory;
one not yet proved stays the named proposition here, never an assumption of a theorem that does
not say so.

**The obligations** (`OblList C U rd σ body True`). The core semantics of a `match` and of a
fused `dispatch` requires the selector in range (`x = g^j`, `j` below the arm count). The
bytecode jumps through a table slot whatever the selector is, so no theorem about the code alone
gives that. `Obl` is the hypothesis in the form today's cut obligations have: at each `match` and
`dispatch` of the body the selector is in range, and at each call the callee's precondition
`U callee args` holds, each *given everything the statements before it on its path establish*.
For a function with no `match`, no `dispatch` and no precondition asked, it is true
(`oblList_of_selFree`).

**A compiled program on a memory** (`World`): the traced functions, their labelled code and jump
table slots (`Compiled`: what `lowerProgram` returned, padded to `2 ^ logSize`), one memory image
and the preconditions `U` the callers are asked for.

* `World.vf g fp` is the valuation by places of function `g` at frame `fp` (`valP`);
* `World.Pre g fp` is `g`'s precondition: `g` is a function other than `main`, the jump tables
  are written (`JTHolds`), a registered loop helper's frame holds its own pointer in the cell
  past its arguments, and `U g` holds of the argument words;
* `World.C` is the located call relation (`Core.Program.RelL`) at frames entered on the run
  (`World.Entered`), and `World.Post g fp` says `g`'s core body holds at `fp`
  (`World.BodyHolds`) and the frame was entered.

**The statements.**

* (a) per pass: assembly is `Compiler.assemble_fetch` and `layout_consecutive`, emission is
  `PStmt.sem_of_run` with `emitFn_ops`, `emitFn_fills`, both proved, composed in
  `lowered_sound`; placement is `PlaceFnSound`.
* (b) per function: `FnSound`, the contract `FunSpecLtReached` of `W.Pre`, `W.Post` for runs
  shorter than `n + 1` from all contracts for runs shorter than `n`.
* (c) whole program: `ProgramSound`, a halting run from `(g^0, 1)` makes `main`'s body hold.
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## The obligations -/

section Obligations

variable (C : CallRel) (U : String → List E → Prop) (rd : Reader) (σ : Val)

mutual
/-- What the statements before a `match`, a `dispatch` or a call must establish, then `next`
after the statement holds. -/
def Obl : Stmt → Prop → Prop
  | .atom a, next => a.Holds rd σ → next
  | .ite c z n, next =>
      IsInK (σ c) → (σ c = 0 → OblList z next) ∧ (σ c ≠ 0 → OblList n next)
  | .match_ x arms, next =>
      (∃ j, j < arms.length ∧ σ x = ofK (addressOfIndex j)) ∧ OblArms x 0 arms next
  | .call f args rets, next =>
      U f (args.map σ) ∧ (C f (args.map σ) (rets.map σ) → next)
  | .callIf c f args, next =>
      IsInK (σ c) → (σ c ≠ 0 → U f (args.map σ)) ∧ ((σ c ≠ 0 → C f (args.map σ) []) → next)
  | .dispatch x fs args rets, next =>
      (∃ j, j < fs.length ∧ σ x = ofK (addressOfIndex j)) ∧
        (∀ (j : Nat) (h : j < fs.length), σ x = ofK (addressOfIndex j) → U fs[j] (args.map σ)) ∧
        ((∃ (j : Nat) (h : j < fs.length), σ x = ofK (addressOfIndex j) ∧
          C fs[j] (args.map σ) (rets.map σ)) → next)
  | .ret _, _ => True

/-- The obligations of a block, then `next`. -/
def OblList : List Stmt → Prop → Prop
  | [], next => next
  | s :: ss, next => Obl s (OblList ss next)

/-- The obligations of each arm, at its selector. -/
def OblArms (x : V) : Nat → List (List Stmt) → Prop → Prop
  | _, [], _ => True
  | j, a :: as, next => (σ x = ofK (addressOfIndex j) → OblList a next) ∧ OblArms x (j + 1) as next
end

mutual
/-- A statement with no `match` and no `dispatch`, at any depth. -/
def selFree : Stmt → Bool
  | .ite _ z n => selFreeList z && selFreeList n
  | .match_ .. => false
  | .dispatch .. => false
  | _ => true

def selFreeList : List Stmt → Bool
  | [] => true
  | s :: ss => selFree s && selFreeList ss
end

variable {C U rd σ}

mutual
theorem obl_of_selFree (hU : ∀ f a, U f a) : ∀ (s : Stmt) (next : Prop), selFree s = true →
    next → Obl C U rd σ s next
  | .atom _, _, _, hn => fun _ => hn
  | .ite _ z n, next, h, hn => by
      simp only [selFree, Bool.and_eq_true] at h
      exact fun _ => ⟨fun _ => oblList_of_selFree hU z next h.1 hn,
        fun _ => oblList_of_selFree hU n next h.2 hn⟩
  | .match_ .., _, h, _ => by simp [selFree] at h
  | .call .., _, _, hn => ⟨hU _ _, fun _ => hn⟩
  | .callIf .., _, _, hn => fun _ => ⟨fun _ => hU _ _, fun _ => hn⟩
  | .dispatch .., _, h, _ => by simp [selFree] at h
  | .ret _, _, _, _ => trivial

/-- **A block with no `match` and no `dispatch`, no precondition asked of its callees, has no
obligations.** -/
theorem oblList_of_selFree (hU : ∀ f a, U f a) : ∀ (ss : List Stmt) (next : Prop),
    selFreeList ss = true → next → OblList C U rd σ ss next
  | [], _, _, hn => hn
  | s :: ss, next, h, hn => by
      simp only [selFreeList, Bool.and_eq_true] at h
      exact obl_of_selFree hU s _ h.1 (oblList_of_selFree hU ss next h.2 hn)
end

end Obligations

/-! ## Jump tables -/

/-- The word a jump table slot is written with: the pc of an arm or of a callee's entry. -/
def SlotWord (l : Layout) : KVal → Option E
  | .at f i => some (OffsetInstruction.immediateWord (l.pow (l.entry.getD f 0 + i)) 0)
  | .entry f => some (OffsetInstruction.immediateWord (l.pow (l.entry.getD f 0)) 0)
  | _ => none

/-- **The jump tables are written**: every slot of `main`'s frame past its cells holds its
word. -/
def JTHolds {κ : ℕ} (L : MemoryImage κ) (l : Layout) (slots : Array KVal) : Prop :=
  ∀ s k w, slots[s]? = some k → SlotWord l k = some w →
    L.read (addressOfIndex (l.tablesBase + s)) = some w

/-- The slots hold these fills. -/
def FillsIn (slots : Array KVal) (fills : List Fill) : Prop :=
  ∀ x ∈ fills, slots[x.1]? = some x.2

/-- The slots hold the callees of these jump tables' shared tables. -/
def SharedIn (slots : Array KVal) (t : Tables) : Prop :=
  ∀ p ∈ t.shared, ∀ j (h : j < p.1.length), slots[p.2 + j]? = some (.entry p.1[j])

/-! ## Placement -/

/-- What a function's code is given of the program around it: the layout's powers and its own
entry, the jump tables, and the contracts of its callees in terms of the core call relation. -/
structure PlaceEnv {κ : ℕ} (Γ : Site κ) (fp : K) (ctx : Ctx) (C : CallRel)
    (U : String → List E → Prop) (slots : Array KVal) (B : ℕ) : Prop where
  pow : Γ.l.PowOk
  jt : JTHolds Γ.L Γ.l slots
  self : Γ.l.entry.getD ctx.name 0 = Γ.pc0
  pcLt : Γ.pc0 + B < 2 ^ 128
  frameLt : Γ.frame < 2 ^ 128
  main : ctx.isMain = true → fp = 1
  entLt : ∀ g a r, isCallee ctx.sigs a r g = true → Γ.ent g < 2 ^ 128
  pre : ∀ g a r fp', isCallee ctx.sigs a r g = true →
    ((ctx.loops[g]?).any (·.registered) = true → wd Γ.L fp' (2 + a) = ofK fp') →
    U g (frameWords Γ.L fp' 2 a) → Γ.Pre g fp'
  post : ∀ g a r fp', isCallee ctx.sigs a r g = true → Γ.Post g fp' →
    C g (frameWords Γ.L fp' 2 a) (frameWords Γ.L fp' (2 + a) r)

/-- **Placement is sound** at one function: whenever `placeFn` succeeds, on any trace, a memory
that has the meaning of the placed body at a frame (`PStmt.SemList`), with the program around as
`PlaceEnv` says and the function's obligations, satisfies the core body under the valuation by
places, and the parameters are the argument words. `kret` receives the return words where the
body returns: the run went on from the frame's return registers (`kretP`), or the function is
`main`. -/
def PlaceFnSound (loops : Loops) (sigs : SMap (Nat × Nat)) (tables : Tables)
    (tf : TracedFn) : Prop :=
  ∀ (pf : Placed) (tables' : Tables), placeFn loops sigs tables tf = .ok (pf, tables') →
    ∀ {κ : ℕ} (Γ : Site κ) (fp : K) (C : CallRel) (U : String → List E → Prop)
      (slots : Array KVal) (N : Prop) (kj : E → E → Prop) (kretP : Prop) (khalt : E → E → Prop)
      (kret : List E → Prop),
      PlaceEnv Γ fp (ctxOf loops sigs tf) C U slots (blockSize pf.fn.body) →
      FillsIn slots (blockFills tf.core.name pf.fn.body 0) → SharedIn slots tables' →
      ((loops[tf.core.name]?).any (·.registered) = true →
        wd Γ.L fp (2 + (sigOf tf).1) = ofK fp) →
      PStmt.SemList Γ fp pf.fn.body 0 N kj kretP khalt →
      OblList C U Γ.L.read (valP Γ.L fp pf.locs) tf.core.body True →
      (tf.core.name = "main" ∨ kretP → kret (frameWords Γ.L fp (2 + (sigOf tf).1) (sigOf tf).2)) →
      tf.core.params.map (valP Γ.L fp pf.locs) = frameWords Γ.L fp 2 (sigOf tf).1 ∧
        Stmt.HoldsList C Γ.L.read (valP Γ.L fp pf.locs) tf.core.body True kret

/-! ## A compiled program on a memory -/

/-- A frame in a memory of `2^κ` words: `fp = g^a`, `a < 2^κ`. -/
def InMem (κ : ℕ) (fp : K) : Prop := ∃ a < 2 ^ κ, fp = addressOfIndex a

/-- A compiled program on a memory: the traced functions, their labelled code and jump table
slots, the padded size, the memory, and the preconditions callers are asked for. -/
structure World (κ : ℕ) where
  p : List TracedFn
  fns : List Lowered
  slots : Array KVal
  logSize : ℕ
  hl : logSize ≤ maxLogBytecode
  L : MemoryImage κ
  U : String → List E → Prop

namespace World

variable {κ : ℕ} (W : World κ)

/-- The code is what the back end compiles the functions to, padded to `2 ^ logSize` slots. -/
def Compiled : Prop :=
  lowerProgram W.p = .ok (W.fns, W.slots) ∧ (assemble W.fns W.slots).size = 2 ^ W.logSize

/-- The program, as the statement reads an assembled program's functions. -/
def prog : LeanIsaProgram := (assemble W.fns W.slots).program W.logSize W.hl

/-- The layout. -/
def layout : Layout := layoutOf W.fns W.slots

/-- A function's entry pc. -/
def ent (g : String) : ℕ := W.layout.entry.getD g 0

/-- The core program. -/
def core : Core.Program := W.p.map (·.core)

/-- The placed functions. -/
def placed : List Placed :=
  match placeProgram W.p with
  | .ok r => r.1
  | .error _ => []

/-- The places of a function's values. -/
def locs (g : String) : VMap Loc :=
  match W.placed.find? (·.fn.name == g) with
  | some pf => pf.locs
  | none => {}

/-- **The valuation of function `g` at frame `fp`**: every value is the word of its place. -/
noncomputable def vf (g : String) (fp : K) : Val := valP W.L fp (W.locs g)

/-- A loop helper whose frames are reserved in one run. -/
def registered (g : String) : Prop := ((loopTable W.p)[g]?).any (·.registered) = true

/-- **A function's precondition** at frame `fp`: it is a function other than `main`, the jump
tables are written, a registered loop helper's frame holds its own pointer past its arguments,
and what its callers are asked for holds of its argument words. -/
def Pre (g : String) (fp : K) : Prop :=
  g ≠ "main" ∧ JTHolds W.L W.layout W.slots ∧ ∃ tf ∈ W.p, tf.core.name = g ∧
    (W.registered g → wd W.L fp (2 + (sigOf tf).1) = ofK fp) ∧
    W.U g (frameWords W.L fp 2 (sigOf tf).1)

/-- **Function `g` was entered at frame `fp` on the run from `(g^0, 1)`**, on these argument and
return words. -/
def Entered (g : String) (fp : K) (args rets : List E) : Prop :=
  InMem κ fp ∧ W.Pre g fp ∧
    Reach W.prog W.L ⟨addressOfIndex 0, 1⟩ ⟨addressOfIndex (W.ent g), fp⟩ ∧
    ∃ tf ∈ W.p, tf.core.name = g ∧ args = frameWords W.L fp 2 (sigOf tf).1 ∧
      rets = frameWords W.L fp (2 + (sigOf tf).1) (sigOf tf).2

/-- **The located call relation**: a callee runs at a frame entered on the run, its values the
words of their places there. -/
noncomputable def C : CallRel := W.core.RelL W.L.read W.vf W.Entered

/-- **The body of a function holds at frame `fp`** on the frame's argument and return words. -/
def BodyHolds (tf : TracedFn) (fp : K) : Prop :=
  tf.core.params.map (W.vf tf.core.name fp) = frameWords W.L fp 2 (sigOf tf).1 ∧
    Stmt.HoldsList W.C W.L.read (W.vf tf.core.name fp) tf.core.body False
      (fun rs => rs = frameWords W.L fp (2 + (sigOf tf).1) (sigOf tf).2)

/-- **A function's postcondition** at frame `fp`: its body holds there and the frame was entered
on the run. -/
def Post (g : String) (fp : K) : Prop :=
  ∃ tf ∈ W.p, tf.core.name = g ∧ W.BodyHolds tf fp ∧
    W.Entered g fp (frameWords W.L fp 2 (sigOf tf).1)
      (frameWords W.L fp (2 + (sigOf tf).1) (sigOf tf).2)

/-- **A function's obligations**: at every frame where its precondition's `U` holds, its
selectors are in range and its callees' `U` hold, each given what precedes it on its path. -/
def Obligations (tf : TracedFn) : Prop :=
  ∀ fp, (tf.core.name = "main" → fp = 1) →
    W.U tf.core.name (frameWords W.L fp 2 (sigOf tf).1) →
    OblList W.C W.U W.L.read (W.vf tf.core.name fp) tf.core.body True

/-- **(b) A function is compiled correctly**: its contract for runs shorter than `n + 1` follows
from every function's contract for runs shorter than `n`. -/
def FnSound (tf : TracedFn) : Prop :=
  ∀ n, (∀ g, FunSpecLtReached W.prog W.L n (W.ent g) (W.Pre g) (W.Post g)) →
    FunSpecLtReached W.prog W.L (n + 1) (W.ent tf.core.name) (W.Pre tf.core.name)
      (W.Post tf.core.name)

/-- **(c) The program is compiled correctly**: `main`'s core body holds at frame `1`. -/
def MainHolds : Prop := ∃ tf ∈ W.p, tf.core.name = "main" ∧ W.BodyHolds tf 1

end World

/-- **(a), placement, for every trace**: `placeFn` is sound whatever the trace (`placeSound`). -/
def PlaceSoundStmt : Prop :=
  ∀ (loops : Loops) (sigs : SMap (Nat × Nat)) (tables : Tables) (tf : TracedFn),
    PlaceFnSound loops sigs tables tf

/-- **(b), for every program**: every function other than `main` of a compiled program whose
obligations hold is compiled correctly. -/
def FnSoundStmt : Prop :=
  ∀ {κ : ℕ} (W : World κ), W.Compiled → κ < 64 → ∀ tf ∈ W.p, tf.core.name ≠ "main" →
    W.Obligations tf → W.FnSound tf

/-- **(c), for every program**: on a memory where a run of the compiled program from `(g^0, 1)`
halts, every function's obligations holding, `main`'s core body holds at frame `1`. -/
def ProgramSoundStmt : Prop :=
  ∀ {κ : ℕ} (W : World κ), W.Compiled → κ < 64 → (∀ tf ∈ W.p, W.Obligations tf) →
    (∀ tf ∈ W.p, tf.core.name = "main" → W.U "main" (frameWords W.L 1 2 (sigOf tf).1)) →
    ∀ k, Safe W.prog W.L k ⟨addressOfIndex 0, 1⟩ → W.MainHolds

end
end LeanVM.Compiler
