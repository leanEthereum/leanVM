/-
  LeanVM.Guest.CoreMode.HeapC

  The core route's heap check with calls and loops: milestone 1's pass, a call meeting its
  callee's preconditions and gaining its guarantees, a return meeting the function's, runs, and a
  loop helper's tail.
-/

module

public import LeanVM.Guest.CoreMode.Heap
public import LeanVM.Guest.Memory.Static

/-!
# The heap check with calls and loops

`heapOkC pows sigOf f H`: milestones 2 and 3 of `formal/notes/core-mode.md`. Milestone 1's pass (`CoreMode/Heap.lean`) extended to every statement; the input format is in the handoff `m2-format.md` and below.

**Slots.** A signature (`HSig`) speaks of slots: slot `b` below the parameter count is parameter `b`, the next ones the returned words. Its cells (`pre`, `post`) are monomials over slots; its runs (`preR`, `postR`, `CRun`) are the cells `base · g^(stride · j)` for `j` from the exponent of `lo` to below that of `hi` (`CIdx`: a constant, or a slot's word read as `g^y`, `y < 2^62`, `rep`). A run also says that both exponents exist. At a site, slots are words (`slotW`): a call's arguments then its returned words, the function's own parameters then, at a `ret`, the words it returns.

**Events.** A path's events (`walk`) write (`EvW`): an atom its `Writes`, an entered call its callee's `post` cells and `postR` runs at its words. `WrittenC` is what the own preconditions and the events so far write. A path is sound (`ReadsOkC`): each atom's reads, and each entered call's callee preconditions at its argument words (with the runs' exponents), are written before; and it returns sound (`PostOkC`): the own guarantees at the words it returns are written by its events.

**The pass** (`chkC`). Milestone 1's state, plus a run scope (pass-level runs, `PRun`, bounds as monomials, by run serial: first the own `preR`, then each call's callee `postR`), and serials for calls and returns, which key the certificate's witnesses (`HCert.calls`, `HCert.rets`). A witness of a cell (`ptOk`): a write event, a precondition, or a run in scope holding it (`ptRun`: at its lower bound, the bounds a fact; or at a constant index, the bounds constants or a fact); of a run (`rnOk`): a run in scope containing it (`runRun`, the lower bound equal, a smaller constant, or one less with the bounds a fact; the upper equal, a larger constant, or past a fact's constant). Facts (`facts`): the own `term` and the residuals a witness lists, as exponents in order (`LtF`, both existing). A call checks its callee's `pre` and `preR` at its arguments and pushes its `post` cells and `postR` runs at its words; a `dispatch` checks every arm's and pushes what every arm guarantees; a `callIf c g args` checks and pushes only the runs whose bounds are the two operands of `c`'s sum (`c = lo + hi`: not entered, `lo = hi` and the run is empty); a `ret` checks the own `post`, `postR` at the parameters and its words. A run in scope asserts only that its cells are written for the exponents its bounds have (`RunF`); the exponents a coverage needs come from the facts and from constants below `2^62`. The parameters are their own bases from the start (`paramEnv`).

**Loops.** A loop helper with `term = [(.val 0, end)]`: its shape (`loopShape`) checked, the pass over its body without the tail, the tail's `callIf` as a call, then its `ret []` (`tailC`): each guarantee written by the path, or, `end` being parameter `1` and the guarantee not over the counter, written by the path at the exit (`i' = end`, `i'` the next counter), the next iteration guaranteeing it otherwise; and a run `[counter, end)` over a base not over the counter is accumulated: the counter's point written by the path, the rest by the next iteration.

Written for the kernel as milestone 1's: tries keyed by `ℕ`, states and cells handed on evaluated.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq)
open LeanVM.Guest.Check (getF setF)

@[expose] public section

/-! ## Words over slots, exponents -/

/-- The product of the bases' powers, each base `b` the word `w b`. -/
def prodW (w : ℕ → E) : List (ℕ × ℕ) → E
  | [] => 1
  | (b, e) :: l => w b ^ e * prodW w l

/-- The word a cell names, each base `b` the word `w b`. -/
def CCell.valW (w : ℕ → E) (c : CCell) : E := prodW w c.bases * ofK (addressOfIndex c.off)

/-- The address of a cell, each base `b` the word `w b`. -/
def CCell.addrW (w : ℕ → E) (c : CCell) : K := (c.valW w).limb 0

/-- Slot `b`'s word. -/
def slotW (ws : List E) (b : ℕ) : E := ws.getD b 0

/-- The words of a valuation's values `V.n k`. -/
def vw (σ : Val) (k : ℕ) : E := σ (V.n k)

/-- The bound `2^62` below which a word `g^y` is read as its exponent `y`. -/
def capE : ℕ := 4611686018427387904

open Classical in
/-- **The exponent of a word**: `y` for the word `g^y`, `y < 2^62`. -/
noncomputable def rep (x : E) : Option ℕ :=
  if h : ∃ y, y < capE ∧ x = ofK (addressOfIndex y) then some (Classical.choose h) else none

/-- An index as a cell: a constant `g^n`, or a base. -/
def idxC : CIdx → CCell
  | .num n => ⟨[], n⟩
  | .val v => baseC v
  | .mono c => c

/-- **The cells of a run** `base · g^(S · j)`, `j` from the exponent of `lo` to below that of `hi`. -/
def RunSet (w : ℕ → E) (base : CCell) (S : ℕ) (lo hi : CCell) (x : K) : Prop :=
  ∃ ylo yhi j, rep (lo.valW w) = some ylo ∧ rep (hi.valW w) = some yhi ∧ ylo ≤ j ∧ j < yhi ∧
    x = (base.valW w * ofK (addressOfIndex (S * j))).limb 0

/-- **A run written**: its cells are in `W` (none when a bound has no exponent). -/
def RunF (W : K → Prop) (w : ℕ → E) (base : CCell) (S : ℕ) (lo hi : CCell) : Prop :=
  ∀ x, RunSet w base S lo hi x → W x

/-- A signature run's cells. -/
def CRun.Set (w : ℕ → E) (r : CRun) : K → Prop := RunSet w r.base r.stride (idxC r.lo) (idxC r.hi)

/-- A signature run written. -/
def CRun.F (W : K → Prop) (w : ℕ → E) (r : CRun) : Prop := RunF W w r.base r.stride (idxC r.lo) (idxC r.hi)

/-- **Exponents in order**: both exist, the first below the second. -/
def LtF (w : ℕ → E) (a b : CCell) : Prop :=
  ∃ ya yb, rep (a.valW w) = some ya ∧ rep (b.valW w) = some yb ∧ ya < yb

/-! ## Signatures at a site, events -/

/-- The addresses of a signature's cells and runs at the slots' words `ws`. -/
def SigSet (cs : List CCell) (rs : List CRun) (ws : List E) (x : K) : Prop :=
  (∃ c ∈ cs, c.addrW (slotW ws) = x) ∨ ∃ r ∈ rs, r.Set (slotW ws) x

/-- **A signature's cells and runs written** in `W`, at the slots' words `ws`. -/
def SigOk (W : K → Prop) (cs : List CCell) (rs : List CRun) (ws : List E) : Prop :=
  (∀ c ∈ cs, W (c.addrW (slotW ws))) ∧ ∀ r ∈ rs, r.F W (slotW ws)

/-- **The addresses an event writes**: an atom's, an entered call's callee guarantees at its words. -/
def EvW (sigOf : String → HSig) (σ : Val) : Ev → K → Prop
  | .atom a, x => Writes σ a x
  | .call f args rets, x => SigSet (sigOf f).post (sigOf f).postR ((args ++ rets).map σ) x
  | _, _ => False

/-- **Written after the events `es`**: the own preconditions at the parameters' words `ws0`, or an
event's write. -/
def WrittenC (sigOf : String → HSig) (H : HCert) (σ : Val) (ws0 : List E) (es : List Ev) (x : K) : Prop :=
  SigSet H.sig.pre H.sig.preR ws0 x ∨ ∃ e ∈ es, EvW sigOf σ e x

/-- What an event needs written in `W`: an atom its reads, an entered call its callee's
preconditions at its argument words. -/
def ReqOk (sigOf : String → HSig) (H : HCert) (σ : Val) (W : K → Prop) : Ev → Prop
  | .atom a => ∀ x, Reads H σ a x → W x
  | .call f args _ => SigOk W (sigOf f).pre (sigOf f).preR (args.map σ)
  | _ => True

/-- **Every event's needs are written before it.** -/
def ReadsOkC (sigOf : String → HSig) (H : HCert) (σ : Val) (ws0 : List E) (es : List Ev) : Prop :=
  ∀ es1 e es2, es = es1 ++ e :: es2 → ReqOk sigOf H σ (WrittenC sigOf H σ ws0 es1) e

/-- **The guarantees at return are written**, at the parameters' words `ws0` and the returned `vs`. -/
def PostOkC (sigOf : String → HSig) (H : HCert) (σ : Val) (ws0 : List E) (es : List Ev) (vs : List V) :
    Prop :=
  SigOk (WrittenC sigOf H σ ws0 es) H.sig.post H.sig.postR (ws0 ++ vs.map σ)

/-- **What an instance is given at entry**: its termination facts. -/
def EntryF (H : HCert) (ws0 : List E) : Prop := ∀ p ∈ H.sig.term, LtF (slotW ws0) (idxC p.1) (idxC p.2)

/-- **The residuals' order facts hold** at the instance. -/
def ResF (H : HCert) (σ : Val) : Prop :=
  ∀ a b, CRes.lt a b ∈ H.res → LtF (vw σ) (idxC a) (idxC b)

/-! ## Monomials at a site -/

/-- A monomial's power. -/
def CCell.pow (c : CCell) (e : ℕ) : CCell := ⟨c.bases.map fun b ↦ (b.1, b.2 * e), c.off * e⟩

/-- Entry `n` of a list. -/
def nth {α : Type} : List α → ℕ → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => nth l n

/-- The bases' powers multiplied into `acc`, base `b` the slot monomial `ms[b]`. -/
def instB (ms : List CCell) : List (ℕ × ℕ) → CCell → Option CCell
  | [], acc => some acc
  | (b, e) :: l, acc => match nth ms b with
    | some m => instB ms l (acc.mul (m.pow e))
    | none => none

/-- **A signature cell at a site**, slot `b` the monomial `ms[b]`. -/
def instC (ms : List CCell) (c : CCell) : Option CCell := instB ms c.bases ⟨[], c.off⟩

/-- A signature index at a site. -/
def instI (ms : List CCell) : CIdx → Option CCell
  | .num n => some ⟨[], n⟩
  | .val v => nth ms v
  | .mono c => instC ms c

/-- **A run of the pass**: the cells `base · g^(stride · j)`, `j` from the exponent of `lo` to
below that of `hi`, bounds as monomials. -/
structure PRun where
  base : CCell
  stride : ℕ
  lo : CCell
  hi : CCell

/-- A signature run at a site. -/
def instR (ms : List CCell) (r : CRun) : Option PRun :=
  match instC ms r.base, instI ms r.lo, instI ms r.hi with
  | some b, some l, some h => some ⟨b, r.stride, l, h⟩
  | _, _, _ => none

/-- Two runs are equal. -/
def PRun.beq (a b : PRun) : Bool :=
  a.base.beq b.base && Nat.beq a.stride b.stride && a.lo.beq b.lo && a.hi.beq b.hi

/-- `k r`, `r` evaluated first. -/
def PRun.seq {β : Type} (r : PRun) (k : PRun → β) : β :=
  r.base.seq fun b ↦ natSeq r.stride fun s ↦ r.lo.seq fun l ↦ r.hi.seq fun h ↦ k ⟨b, s, l, h⟩

/-- The values' monomials. -/
noncomputable def monos (env : Trie CCell) : List V → Option (List CCell)
  | [] => some []
  | v :: vs => match monoOf env v, monos env vs with
    | some m, some ms => some (m :: ms)
    | _, _ => none

/-- A fact's index: a constant, a value's monomial, or a monomial as it is. -/
noncomputable def idxF (env : Trie CCell) : CIdx → CCell
  | .num n => ⟨[], n⟩
  | .val k => (getF env k).getD (baseC k)
  | .mono c => c

/-! ## Coverage -/

/-- The fact `(a, b)`. -/
def hasF (F : List (CCell × CCell)) (a b : CCell) : Bool := F.any fun p ↦ p.1.beq a && p.2.beq b

/-- A fact `(g^k', b)` with `k ≤ k'`. -/
def hasFC (F : List (CCell × CCell)) (k : ℕ) (b : CCell) : Bool :=
  F.any fun p ↦ p.1.bases.isEmpty && Nat.ble k p.1.off && Nat.blt p.1.off capE && p.2.beq b

/-- A base's exponent in sorted bases, `0` if absent. -/
def expOf : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (k, e) :: l, k' => bif Nat.beq k k' then e else expOf l k'

/-- The bases of `c` past those of `b`, divided by `S`. -/
def divB (b : List (ℕ × ℕ)) (S : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (k, e) :: l => bif Nat.blt (expOf b k) e then (k, (e - expOf b k) / S) :: divB b S l else divB b S l

/-- The index `J` with `c = b · J^S` if there is one (`ptIdx` multiplies back). -/
def idxOf (b c : CCell) (S : ℕ) : CCell := ⟨divB b.bases S c.bases, (c.off - b.off) / S⟩

/-- **A cell of a run at any index** `J` (`c = base · J^S`): below the upper bound by a fact
`(J, hi)`, past the lower bound (`g^0`, `J` itself, or a fact `(lo, J·g)`). -/
def ptIdx (F : List (CCell × CCell)) (R : PRun) (c J : CCell) : Bool :=
  c.beq (R.base.mul (J.pow R.stride)) && hasF F J R.hi &&
    ((R.lo.bases.isEmpty && Nat.beq R.lo.off 0) || R.lo.beq J || hasF F R.lo (J.shift 1))

/-- **A cell of a run in scope**: at its lower bound, the bounds a fact; or at a constant index past
a constant lower bound, below a constant upper bound or a fact's; or at any index (`ptIdx`). -/
def ptRun (F : List (CCell × CCell)) (R : PRun) (c : CCell) : Bool :=
  (c.beq (R.base.mul (R.lo.pow R.stride)) && hasF F R.lo R.hi) || ptIdx F R c (idxOf R.base c R.stride) ||
  (basesBeq c.bases R.base.bases && Nat.ble R.base.off c.off && !Nat.beq R.stride 0 &&
    Nat.beq ((c.off - R.base.off) % R.stride) 0 && R.lo.bases.isEmpty && Nat.blt R.lo.off capE &&
    Nat.ble R.lo.off ((c.off - R.base.off) / R.stride) &&
    ((R.hi.bases.isEmpty && Nat.blt R.hi.off capE && Nat.blt ((c.off - R.base.off) / R.stride) R.hi.off) ||
      hasFC F ((c.off - R.base.off) / R.stride) R.hi))

/-- The lower bound of `Q` at or past that of `R`, its exponent existing. -/
def loOk (F : List (CCell × CCell)) (Q R : PRun) : Bool :=
  Q.lo.beq R.lo ||
  (Q.lo.bases.isEmpty && R.lo.bases.isEmpty && Nat.ble R.lo.off Q.lo.off && Nat.blt Q.lo.off capE) ||
  (Q.lo.beq (R.lo.shift 1) && hasF F R.lo R.hi)

/-- The upper bound of `Q` at or below that of `R`, its exponent existing. -/
def hiOk (F : List (CCell × CCell)) (Q R : PRun) : Bool :=
  Q.hi.beq R.hi ||
  (Q.hi.bases.isEmpty && R.hi.bases.isEmpty && Nat.ble Q.hi.off R.hi.off && Nat.blt R.hi.off capE) ||
  (Q.hi.bases.isEmpty && Nat.blt Q.hi.off capE && hasFC F (Q.hi.off - 1) R.hi)

/-- **A run inside a run in scope.** -/
def runRun (F : List (CCell × CCell)) (Q R : PRun) : Bool :=
  Q.base.beq R.base && Nat.beq Q.stride R.stride && loOk F Q R && hiOk F Q R

/-! ## The pass -/

/-- The pass's state: milestone 1's, a run scope, the sums seen (`ad`, a value number to the
monomials of its first `add`'s operands), the next run, call and ret serials. -/
structure CSt where
  env : Trie CCell
  sc : Trie CCell
  rs : Trie PRun
  ad : Trie (CCell × CCell)
  n : ℕ
  nr : ℕ
  nc : ℕ
  nt : ℕ

/-- `k st`, `st` evaluated first. -/
def CSt.seq {β : Type} (st : CSt) (k : CSt → β) : β :=
  st.env.seq fun e ↦ st.sc.seq fun s ↦ st.rs.seq fun r ↦ st.ad.seq fun a ↦ natSeq st.n fun n ↦
    natSeq st.nr fun nr ↦ natSeq st.nc fun nc ↦ natSeq st.nt fun nt ↦ k ⟨e, s, r, a, n, nr, nc, nt⟩

/-- `st`'s scope with `s`'s serials. -/
def CSt.cnt (st s : CSt) : CSt := ⟨st.env, st.sc, st.rs, st.ad, s.n, s.nr, s.nc, s.nt⟩

/-- Milestone 1's part of the state. -/
def CSt.toH (st : CSt) : HSt := ⟨st.env, st.sc, st.n⟩

/-- The state with milestone 1's part `h`. -/
def CSt.ofH (st : CSt) (h : HSt) : CSt := ⟨h.env, h.sc, st.rs, st.ad, h.n, st.nr, st.nc, st.nt⟩

/-- A write event of the cell `c`. -/
noncomputable def CSt.push (st : CSt) (c : CCell) : CSt := st.ofH (st.toH.push c)

/-- A run into the scope, at the next run serial. -/
noncomputable def CSt.pushR (st : CSt) (r : PRun) : CSt :=
  (setF r Exec.indexDepth st.rs st.nr).seq fun rs ↦ ⟨st.env, st.sc, rs, st.ad, st.n, st.nr + 1, st.nc, st.nt⟩

/-- The next call serial. -/
def CSt.nextC (st : CSt) : CSt := ⟨st.env, st.sc, st.rs, st.ad, st.n, st.nr, st.nc + 1, st.nt⟩

/-- The next ret serial. -/
def CSt.nextT (st : CSt) : CSt := ⟨st.env, st.sc, st.rs, st.ad, st.n, st.nr, st.nc, st.nt + 1⟩

/-- The sum `k = a + b` seen, if `k` has none yet. -/
noncomputable def CSt.addS (st : CSt) (k : ℕ) (a b : CCell) : CSt :=
  match getF st.ad k with
  | some _ => st
  | none => (setF (a, b) Exec.indexDepth st.ad k).seq fun ad ↦ ⟨st.env, st.sc, st.rs, ad, st.n, st.nr, st.nc, st.nt⟩

/-- What the pass reads. -/
structure CX where
  pows : PowTree
  R : Trie (List (ℕ × ℕ × Wit))
  pre : Trie CCell
  C : Trie (List Wit)
  T : Trie (List Wit)
  res : Trie CRes
  sigOf : String → HSig
  sig : HSig
  params : List V

/-- Milestone 1's part. -/
def CX.toH (X : CX) : HX := ⟨X.pows, X.R, X.pre⟩

/-- **The facts at a witness**: the own termination facts and the residuals it lists, as monomials. -/
noncomputable def facts (X : CX) (env : Trie CCell) (res : List ℕ) : List (CCell × CCell) :=
  X.sig.term.map (fun p ↦ (idxF env p.1, idxF env p.2)) ++
    res.filterMap fun i ↦ match getF X.res i with
      | some (.lt a b) => some (idxF env a, idxF env b)
      | _ => none

/-- **A witness of the cell `c`.** -/
noncomputable def ptOk (X : CX) (st : CSt) (c : CCell) : Wit → Bool
  | .ev n => match getF st.sc n with
    | some c' => c'.beq c
    | none => false
  | .pre k => match getF X.pre k with
    | some c' => c'.beq c
    | none => false
  | .run r res => match getF st.rs r with
    | some R => ptRun (facts X st.env res) R c
    | none => false
  | .res _ => false

/-- **A witness of the run `Q`.** -/
noncomputable def rnOk (X : CX) (st : CSt) (Q : PRun) : Wit → Bool
  | .run r res => match getF st.rs r with
    | some R => runRun (facts X st.env res) Q R
    | none => false
  | _ => false

/-- Signature cells at the slots `ms`, each with its witness: the witnesses left. -/
noncomputable def reqP (X : CX) (st : CSt) (ms : List CCell) : List CCell → List Wit → Option (List Wit)
  | [], ws => some ws
  | c :: cs, w :: ws => match instC ms c with
    | some c' => bif ptOk X st c' w then reqP X st ms cs ws else none
    | none => none
  | _ :: _, [] => none

/-- Signature runs at the slots `ms`, each with its witness: the witnesses left. -/
noncomputable def reqR (X : CX) (st : CSt) (ms : List CCell) : List CRun → List Wit → Option (List Wit)
  | [], ws => some ws
  | r :: rs, w :: ws => match instR ms r with
    | some q => bif rnOk X st q w then reqR X st ms rs ws else none
    | none => none
  | _ :: _, [] => none

/-- A signature's preconditions at the slots `ms`: the witnesses left. -/
noncomputable def reqS (X : CX) (st : CSt) (ms : List CCell) (G : HSig) (ws : List Wit) :
    Option (List Wit) :=
  match reqP X st ms G.pre ws with
  | some ws' => reqR X st ms G.preR ws'
  | none => none

/-- Each arm's preconditions at the slots `ms`: the witnesses left. -/
noncomputable def reqArms (X : CX) (st : CSt) (ms : List CCell) : List String → List Wit → Option (List Wit)
  | [], ws => some ws
  | g :: gs, ws => match reqS X st ms (X.sigOf g) ws with
    | some ws' => reqArms X st ms gs ws'
    | none => none

/-- Signature cells at the slots `ms`. -/
def instAll (ms : List CCell) : List CCell → Option (List CCell)
  | [] => some []
  | c :: cs => match instC ms c, instAll ms cs with
    | some c', some cs' => some (c' :: cs')
    | _, _ => none

/-- Signature runs at the slots `ms`. -/
def instAllR (ms : List CCell) : List CRun → Option (List PRun)
  | [] => some []
  | r :: rs => match instR ms r, instAllR ms rs with
    | some q, some qs => some (q :: qs)
    | _, _ => none

/-- Write events of the cells, in order. -/
noncomputable def pushL : List CCell → CSt → CSt
  | [], st => st
  | c :: cs, st => c.seq fun c ↦ (st.push c).seq fun st ↦ pushL cs st

/-- Runs into the scope, in order. -/
noncomputable def pushRL : List PRun → CSt → CSt
  | [], st => st
  | r :: rs, st => r.seq fun r ↦ (st.pushR r).seq fun st ↦ pushRL rs st

/-- The cells every list has. -/
def meetC (ls : List (List CCell)) (c : CCell) : Bool := ls.all fun l ↦ l.any fun c' ↦ c'.beq c

/-- The runs every list has. -/
def meetR (ls : List (List PRun)) (r : PRun) : Bool := ls.all fun l ↦ l.any fun r' ↦ r'.beq r

/-- Each callee's guarantees at the slots `ms`. -/
def instArms (sigOf : String → HSig) (ms : List CCell) : List String →
    Option (List (List CCell) × List (List PRun))
  | [] => some ([], [])
  | g :: gs => match instAll ms (sigOf g).post, instAllR ms (sigOf g).postR, instArms sigOf ms gs with
    | some p, some r, some (ps, rs) => some (p :: ps, r :: rs)
    | _, _, _ => none

/-- **A call**: its callee's preconditions at its arguments, its guarantees at its words pushed. -/
noncomputable def callC (X : CX) (st : CSt) (g : String) (args rets : List V) : Option CSt :=
  match monos st.env args, monos st.env rets, getF X.C st.nc with
  | some ma, some mr, some ws => match reqS X st ma (X.sigOf g) ws with
    | some [] => match instAll (ma ++ mr) (X.sigOf g).post, instAllR (ma ++ mr) (X.sigOf g).postR with
      | some ps, some rs => some (pushRL rs (pushL ps st.nextC))
      | _, _ => none
    | _ => none
  | _, _, _ => none

/-- A run whose bounds are the sum's operands, in either order. -/
def boundsOf (p : CCell × CCell) (q : PRun) : Bool :=
  (q.lo.beq p.1 && q.hi.beq p.2) || (q.lo.beq p.2 && q.hi.beq p.1)

/-- The guard's sum, if `c` is a value with one. -/
noncomputable def sumOf (st : CSt) (c : V) : Option (CCell × CCell) :=
  match vnum c with
  | some k => getF st.ad k
  | none => none

/-- **A conditional call** `callIf c g args`: its callee's preconditions; pushed, each of its guarantees'
runs whose bounds are the operands of the guard's sum (not entered, the guard is `0`, the bounds one
word, the run empty). -/
noncomputable def callIfC (X : CX) (st : CSt) (c : V) (g : String) (args : List V) : Option CSt :=
  match monos st.env args, getF X.C st.nc with
  | some ma, some ws => match reqS X st ma (X.sigOf g) ws with
    | some [] => match sumOf st c, instAllR ma (X.sigOf g).postR with
      | some p, some qs => some (pushRL (qs.filter (boundsOf p)) st.nextC)
      | _, _ => some st.nextC
    | _ => none
  | _, _ => none

/-- **A dispatch**: every arm's preconditions, and what every arm guarantees pushed. -/
noncomputable def dispC (X : CX) (st : CSt) (fs : List String) (args rets : List V) : Option CSt :=
  match fs, monos st.env args, monos st.env rets, getF X.C st.nc with
  | g :: gs, some ma, some mr, some ws => match reqArms X st ma (g :: gs) ws with
    | some [] => match instArms X.sigOf (ma ++ mr) (g :: gs) with
      | some (p :: ps, r :: rs) => some (pushRL (r.filter (meetR rs)) (pushL (p.filter (meetC ps)) st.nextC))
      | _ => none
    | _ => none
  | _, _, _, _ => none

/-- **A return**: the own guarantees at the parameters and the returned words. -/
noncomputable def retC (X : CX) (st : CSt) (vs : List V) : Bool :=
  match monos st.env X.params, monos st.env vs, getF X.T st.nt with
  | some mp, some mv, some ws => match reqP X st (mp ++ mv) X.sig.post ws with
    | some ws' => match reqR X st (mp ++ mv) X.sig.postR ws' with
      | some [] => true
      | _ => false
    | none => false
  | _, _, _ => false

/-- **An atom**: milestone 1's, a read's witness any of `ptOk`'s. -/
noncomputable def atomC (X : CX) (st : CSt) : Atom → Option CSt
  | .load d p off => match monoOf st.env p with
    | some m => (m.shift off).seq fun c ↦
        bif (match readWitT X.R d p off with
          | some w => ptOk X st c w
          | none => true) then some (st.push c) else none
    | none => none
  | .add d a b => match vnum d, monoOf st.env a, monoOf st.env b with
    | some k, some ma, some mb => some (st.addS k ma mb)
    | _, _, _ => some st
  | a => (atomH X.toH st.toH a).map st.ofH

mutual
/-- **The pass over a block**: the state at its end, or at its `ret`. -/
noncomputable def chkC (X : CX) : List Stmt → CSt → Option CSt
  | [], st => some st
  | .atom a :: ss, st => match atomC X st a with
    | some st' => st'.seq fun st' ↦ chkC X ss st'
    | none => none
  | .ite _ z n :: ss, st => match chkC X z st with
    | some s1 => match chkC X n (st.cnt s1) with
      | some s2 => (st.cnt s2).seq fun st' ↦ chkC X ss st'
      | none => none
    | none => none
  | .match_ _ arms :: ss, st => match chkArmsC X arms st with
    | some s => (st.cnt s).seq fun st' ↦ chkC X ss st'
    | none => none
  | .call g args rets :: ss, st => match callC X st g args rets with
    | some st' => st'.seq fun st' ↦ chkC X ss st'
    | none => none
  | .callIf c g args :: ss, st => match callIfC X st c g args with
    | some st' => st'.seq fun st' ↦ chkC X ss st'
    | none => none
  | .dispatch _ fs args rets :: ss, st => match dispC X st fs args rets with
    | some st' => st'.seq fun st' ↦ chkC X ss st'
    | none => none
  | .ret vs :: _, st => bif retC X st vs then some st.nextT else none

/-- The pass over each arm, from the state before the `match`: the last arm's serials. -/
noncomputable def chkArmsC (X : CX) : List (List Stmt) → CSt → Option CSt
  | [], st => some st
  | a :: as, st => match chkC X a st with
    | some s1 => chkArmsC X as (st.cnt s1)
    | none => none
end

/-! ## A loop's tail -/

/-- A cell not over slot `0` (the counter). -/
def noSlot0 (c : CCell) : Bool := c.bases.all fun b ↦ !Nat.beq b.1 0

/-- An index not slot `0`. -/
def noSlot0I : CIdx → Bool
  | .val v => !Nat.beq v 0
  | .num _ => true
  | .mono c => noSlot0 c

/-- A run not over slot `0`. -/
def noSlot0R (r : CRun) : Bool := noSlot0 r.base && noSlot0I r.lo && noSlot0I r.hi

/-- Two indices are equal. -/
def CIdx.beq : CIdx → CIdx → Bool
  | .num a, .num b => Nat.beq a b
  | .val a, .val b => Nat.beq a b
  | .mono a, .mono b => a.beq b
  | _, _ => false

/-- A list with entry `n` replaced. -/
def setNth {α : Type} : List α → ℕ → α → List α
  | [], _, _ => []
  | _ :: l, 0, b => b :: l
  | a :: l, n + 1, b => a :: setNth l n b

/-- The tail's `post` cells, at the parameters `mp`, or at the exit's slots `mx`. -/
noncomputable def tailP (X : CX) (st : CSt) (mp mx : List CCell) (ex : Bool) :
    List CCell → List Wit → Option (List Wit)
  | [], ws => some ws
  | c :: cs, w :: ws =>
    bif (match instC mp c with
        | some c' => ptOk X st c' w
        | none => false) ||
      (ex && noSlot0 c && match instC mx c with
        | some c' => ptOk X st c' w
        | none => false)
    then tailP X st mp mx ex cs ws else none
  | _ :: _, [] => none

/-- The tail's `postR` runs, at the parameters `mp`, at the exit's slots `mx`, or accumulated. -/
noncomputable def tailR (X : CX) (st : CSt) (mp mx : List CCell) (ex : Bool) (ei : CIdx) :
    List CRun → List Wit → Option (List Wit)
  | [], ws => some ws
  | r :: rs, w :: ws =>
    bif (match instR mp r with
        | some q => rnOk X st q w
        | none => false) ||
      (ex && noSlot0R r && match instR mx r with
        | some q => rnOk X st q w
        | none => false) ||
      (CIdx.beq r.lo (.val 0) && CIdx.beq r.hi ei && noSlot0 r.base &&
        match instC mp r.base, nth mp 0 with
        | some b, some m0 => ptOk X st (b.mul (m0.pow r.stride)) w
        | _, _ => false)
    then tailR X st mp mx ex ei rs ws else none
  | _ :: _, [] => none

/-- **A loop's `ret []` after its tail call** `callIf c self (i' :: _)`, the loop's end `ei`. -/
noncomputable def tailC (X : CX) (st : CSt) (args : List V) (ei : CIdx) : Bool :=
  match args, monos st.env X.params, getF X.T st.nt with
  | i' :: _, some mp, some ws => match monoOf st.env i' with
    | some mi => match tailP X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) X.sig.post ws with
      | some ws' => match tailR X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) ei X.sig.postR ws' with
        | some [] => true
        | _ => false
      | none => false
    | none => false
  | _, _, _ => false

/-- A loop's end as `loopShape` takes it. -/
def endOf : CIdx → Option (Option ℕ)
  | .val 1 => some none
  | .num e => some (some e)
  | _ => none

/-- **A loop helper**: its shape at the end `ei`, the pass over its body without the tail, the tail
call's preconditions, the tail's guarantees. -/
noncomputable def loopC (X : CX) (f : Fn) (ei : CIdx) (st0 : CSt) : Bool :=
  match endOf ei, f.body.reverse with
  | some endc, .ret [] :: .callIf c g args :: _ => match loopShape f endc with
    | some pre => match chkC X pre st0 with
      | some st1 => match callIfC X st1 c g args with
        | some st2 => tailC X st2 args ei
        | none => false
      | none => false
    | none => false
  | _, _ => false

/-! ## The check -/

/-- An index over the first `m` slots. -/
def idxOver (m : ℕ) : CIdx → Bool
  | .val v => Nat.blt v m
  | .num _ => true
  | .mono c => c.bases.all fun b ↦ Nat.blt b.1 m

/-- The environment naming each of the first `m` parameters `V.n i` by its own base. -/
noncomputable def paramEnv : ℕ → Trie CCell
  | 0 => .nil
  | m + 1 => (paramEnv m).seq fun t ↦ (setF (baseC m) Exec.indexDepth t m).seq id

/-- The entry state: each parameter its own base, the own `preR` at the parameters, run serials
from `0`. -/
noncomputable def initC (X : CX) : Option CSt :=
  (paramEnv X.params.length).seq fun env ↦ match monos env X.params with
  | some mp => (instAllR mp X.sig.preR).map fun rs ↦ pushRL rs ⟨env, .nil, .nil, .nil, 0, 0, 0, 0⟩
  | none => none

/-- **The heap check with calls and loops.** The parameters `V.n i`, the preconditions over them,
the entry state, then the pass over the body, or a loop helper's (`term = [(.val 0, end)]`). -/
noncomputable def heapOkC (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) : Bool :=
  paramsN f.params 0 && preOver f.params.length H.sig.pre &&
    H.sig.term.all (fun p ↦ idxOver f.params.length p.1 && idxOver f.params.length p.2) &&
    H.readT.seq fun R ↦ (trieFrom H.sig.pre 0 .nil).seq fun P ↦ (trieFrom H.calls 0 .nil).seq fun C ↦
      (trieFrom H.rets 0 .nil).seq fun T ↦ (trieFrom H.res 0 .nil).seq fun RS ↦
        match initC ⟨pows, R, P, C, T, RS, sigOf, H.sig, f.params⟩ with
        | some st0 => match H.sig.term with
          | [] => (chkC ⟨pows, R, P, C, T, RS, sigOf, H.sig, f.params⟩ f.body st0).isSome
          | [(.val 0, ei)] => loopC ⟨pows, R, P, C, T, RS, sigOf, H.sig, f.params⟩ f ei st0
          | _ => false
        | none => false

end

end LeanVM.Guest.CoreMode
