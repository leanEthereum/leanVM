/-
  LeanVM.Guest.CoreMode.HeapC

  The core route's heap check with calls and loops: milestone 1's pass, a call meeting its
  callee's preconditions and gaining its guarantees, a return meeting the function's, runs, and a
  loop helper's tail.
-/

module

public import LeanVM.Guest.CoreMode.Heap
public import LeanVM.Guest.Memory.Static
public import LeanVM.Guest.Memory.Fresh

/-!
# The heap check with calls and loops

`heapOkC pows sigOf f H`: milestones 2 and 3 of `formal/notes/core-mode.md`. Milestone 1's pass (`CoreMode/Heap.lean`) extended to every statement; the input format is in the handoff `m2-format.md` and below.

**Slots.** A signature (`HSig`) speaks of slots: slot `b` below the parameter count is parameter `b`, the next ones the returned words. Its cells (`pre`, `post`) are monomials over slots; its runs (`preR`, `postR`, `CRun`) are the cells `base · g^(stride · j)` for `j` from the exponent of `lo` to below that of `hi` (`CIdx`: a constant, or a slot's word read as `g^y`, `y < 2^62`, `rep`). A run also says that both exponents exist. At a site, slots are words (`slotW`): a call's arguments then its returned words, the function's own parameters then, at a `ret`, the words it returns.

**Events.** A path's events (`walk`) write (`EvW`): an atom its `Writes`, an entered call its callee's `post` cells and `postR` runs at its words. `WrittenC` is what the own preconditions and the events so far write. A path is sound (`ReadsOkC`): each atom's reads, and each entered call's callee preconditions at its argument words (with the runs' exponents), are written before; and it returns sound (`PostOkC`): the own guarantees at the words it returns are written by its events.

**The pass** (`chkC`). Milestone 1's state, plus a run scope (pass-level runs, `PRun`, bounds as monomials, by run serial: first the own `preR`, then each call's callee `postR`), and serials for calls and returns, which key the certificate's witnesses (`HCert.calls`, `HCert.rets`). A witness of a cell (`ptOk`): a write event, a precondition, or a run in scope holding it (`ptRun`: at its lower bound, the bounds a fact; or at a constant index, the bounds constants or a fact); of a run (`rnOk`): a run in scope containing it (`runRun`, the lower bound equal, a smaller constant, or one less with the bounds a fact; the upper equal, a larger constant, or past a fact's constant). Facts (`facts`): the own `term` and the residuals a witness lists, as exponents in order (`LtF`, both existing). A call checks its callee's `pre` and `preR` at its arguments and pushes its `post` cells and `postR` runs at its words; a `dispatch` checks every arm's and pushes what every arm guarantees; a `callIf c g args` checks and pushes only the runs whose bounds are the two operands of `c`'s sum (`c = lo + hi`: not entered, `lo = hi` and the run is empty); a `ret` checks the own `post`, `postR` at the parameters and its words. A run in scope asserts only that its cells are written for the exponents its bounds have (`RunF`); the exponents a coverage needs come from the facts and from constants below `2^62`. The parameters are their own bases from the start (`paramEnv`).

**Values.** A call names its returned words by its callee's `retM` (monomials over the arguments; a `dispatch`, those every arm gives), which a `ret` checks of the words it returns (`retMC`, `RetMOk`); a read whose witness is a load event of its very cell takes the word stored there (`hvDef`: memory is written once, `SvOk`); a `mul d q b` listing `q` (`HCert.divs`) with `b` a constant `g^k` names `q = d / g^k` (`divOf`). A function may name the word stored at a `post` cell (`postV`, `RetVOk`: by the load event its witness is, `retVC`); a call stores it at that cell's point serial (`postVE`), so a read of the cell takes it as from a load event.

**Joins.** After an `ite` or a `match`, the scope is the one before it with, in addition, the cells, runs, pointer facts and pointer runs that every block able to fall through (not ending in a top-level `ret`, `endsRet`) added, at the first such block's serials (`joinSt`): whichever falls through wrote them.

**Under a selector.** A `dispatch` on `x` also keeps its arms' guarantees under `x`'s monomial, one entry per dispatch indexed by arm (`condE`, `CSt.cd`: arm `j` ran if `x = g^j`); a later dispatch on the same monomial checks arm `j`'s preconditions in the state with those of every earlier dispatch's arm `j` pushed, from the next serials (`condSt`).

**Ghosts.** A signature with `ghosts = n` has `n` ghost slots after its parameters (`m + j`), in `preR`, `preP`, `prePR` only: words its callers name, no argument (a caller's object, which a cursor parameter points into). In the own pass ghost `j` is the value `V.n (GB + j)`, its own base (`ghostMs`), which the body may not name (`noGhost`): the run does not depend on it. A call of `g` on `args` names `g`'s ghosts by the monomials the certificate lists for that callee and those arguments (`HCert.gargs`, `gargsOf`), as many as `g` has; the semantics evaluates them at the caller's valuation (`gargsW`, `CallPre`), and the tree gives each callee instance those words (`HeapCTree.lean`, `setG`).

**Words at cells.** A caller may name a callee's ghost by the word at a cell it never loads (a record's pointer
field): the certificate lists such cells (`HCert.ders`), value `DB + k` being the word at `ders[k]` (`DerOk`, a
hypothesis of the instance, set from the memory in the tree, `HeapCTree.lean`), and the ghost monomials (`gargs`)
name it. At a call naming `DB + k`, the cell `ders[k]` is witnessed written first (`derWs`, `DerW`), then the
callee's preconditions are checked with `DB + k` loaded from it (`derSt`, `src`), so a pointer fact at the cell
gives the object's cells; the semantics asks those preconditions where the cells are in memory (`DerDef`,
`CallReq`).

**Frame runs at return.** The certificate may list cells of `frameAddr` runs (`HCert.fas`): cell `i` of a
`frameAddr p run` whose `run[i]` an atom defines (`atomDst`), both among the top-level atoms before the body's
first `ret` (`topAtoms`, `faOk`), so on every path that returns. They are pushed as write events at each `ret`,
for its guarantees only (`faCells`): the frame cell holding `run[i]` is written by then (`FAW`, `PostOkC`).

**Runs split.** A run needed may be split at a symbolic index `k` (`catM`: `k·h` the upper bound's word by the
kept equations, both exponents existing), merged from residues whose root is given (`mrgE`), and, after a
dispatch on `x`, a block `⟨q, S, g^0, x·g^d⟩` that every kept arm `j` writes up to `j + d` (`ab`).

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

/-- **The cells a pointer fact names**: past the word at `a`, if there is one, at the offsets. -/
def PtrSet (rd : Reader) (a : K) (offs : List ℕ) (x : K) : Prop :=
  ∃ w, rd a = some w ∧ ∃ o ∈ offs, x = w.limb 0 * addressOfIndex o

/-- The cells a signature's pointer facts and pointer runs name at the slots' words `ws`. -/
def PtrSigSet (rd : Reader) (ps : List (CCell × List ℕ)) (prs : List (CRun × List ℕ)) (ws : List E) (x : K) :
    Prop :=
  (∃ p ∈ ps, PtrSet rd (p.1.addrW (slotW ws)) p.2 x) ∨ ∃ p ∈ prs, ∃ a, p.1.Set (slotW ws) a ∧ PtrSet rd a p.2 x

/-- **A signature's pointer facts and runs written** in `W`, at the slots' words `ws`. -/
def PtrOk (W : K → Prop) (rd : Reader) (ps : List (CCell × List ℕ)) (prs : List (CRun × List ℕ)) (ws : List E) :
    Prop :=
  ∀ x, PtrSigSet rd ps prs ws x → W x

/-- **A signature's preconditions** at the slots' words: its cells, runs, pointer facts and runs. -/
def PreSet (rd : Reader) (G : HSig) (ws : List E) (x : K) : Prop :=
  SigSet G.pre G.preR ws x ∨ PtrSigSet rd G.preP G.prePR ws x

/-- **A signature's guarantees** at the slots' words. -/
def PostSet (rd : Reader) (G : HSig) (ws : List E) (x : K) : Prop :=
  SigSet G.post G.postR ws x ∨ PtrSigSet rd G.postP G.postPR ws x

/-! ## Ghost words -/

/-- The first value number of the ghosts: ghost `j` of a function is the value `V.n (GB + j)`. -/
def GB : ℕ := 1048576

/-- A call's values are the values `V.n a`, `a ∈ ks`. -/
def keyOk : List V → List ℕ → Bool
  | [], [] => true
  | v :: vs, k :: ks => (match vnum v with
    | some k' => Nat.beq k' k
    | none => false) && keyOk vs ks
  | _, _ => false

/-- **A call's ghost monomials**: those the certificate names for a call of `g` on `args`, over the
caller's values. -/
def gargsOf (ga : List (String × List ℕ × List CCell)) (g : String) (args : List V) : List CCell :=
  match ga.find? fun p ↦ decide (p.1 = g) && keyOk args p.2.1 with
  | some p => p.2.2
  | none => []

/-- **A call's ghost words**, at the caller's valuation. -/
def gargsW (H : HCert) (σ : Val) (g : String) (args : List V) : List E :=
  (gargsOf H.gargs g args).map fun c ↦ c.valW (vw σ)

/-- **A function's own ghost words**: its values `V.n (GB + j)`. -/
def ownG (G : HSig) (σ : Val) : List E := (List.range G.ghosts).map fun j ↦ vw σ (GB + j)

/-- The first value number of the words at cells (`HCert.ders`): value `DB + k` (below `GB`) is the word at
the cell `ders[k]`. Past every value a function names (`noGhost`). -/
def DB : ℕ := 524288

/-- The numbers, each at its first occurrence (`acc` reversed, the ones kept so far). -/
def nubN : List ℕ → List ℕ → List ℕ
  | acc, [] => acc.reverse
  | acc, k :: l => nubN (bif acc.any (Nat.beq k) then acc else k :: acc) l

/-- **The words at cells monomials name**: `k` for each base `DB + k` below `GB`, once, in order. -/
def derKs (ms : List CCell) : List ℕ :=
  nubN [] ((ms.flatMap CCell.bases).filterMap fun b ↦
    bif Nat.ble DB b.1 && Nat.blt b.1 GB then some (b.1 - DB) else none)

/-- **The words at cells a call's ghost monomials name** (`derKs`). -/
def callDers (H : HCert) (g : String) (args : List V) : List ℕ := derKs (gargsOf H.gargs g args)

/-- **The addresses an event writes**: an atom's, an entered call's callee guarantees at its words. -/
def EvW (sigOf : String → HSig) (rd : Reader) (σ : Val) : Ev → K → Prop
  | .atom a, x => Writes σ a x
  | .call f args rets, x => PostSet rd (sigOf f) ((args ++ rets).map σ) x
  | _, _ => False

/-- **Written after the events `es`**: the own preconditions at the parameters' words `ws0` and the
own ghost words, or an event's write. -/
def WrittenC (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (es : List Ev) (x : K) :
    Prop :=
  PreSet rd H.sig (ws0 ++ ownG H.sig σ) x ∨ ∃ e ∈ es, EvW sigOf rd σ e x

/-- **A callee's preconditions written in `W`**, at a call of `g` on `args`: its argument words and
the ghost words the caller names (as many as it has ghosts). -/
def CallPre (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (W : K → Prop) (g : String)
    (args : List V) : Prop :=
  (gargsOf H.gargs g args).length = (sigOf g).ghosts ∧
    SigOk W (sigOf g).pre (sigOf g).preR (args.map σ ++ gargsW H σ g args) ∧
    PtrOk W rd (sigOf g).preP (sigOf g).prePR (args.map σ ++ gargsW H σ g args)

/-- **The cells a call's ghost words read are written** in `W`: `ders[k]` for each word at a cell `DB + k` its
ghost monomials name. -/
def DerW (H : HCert) (σ : Val) (W : K → Prop) (g : String) (args : List V) : Prop :=
  ∀ k ∈ callDers H g args, ∀ c, H.ders[k]? = some c → W (c.addrW (vw σ))

/-- **The cells a call's ghost words read are in memory.** -/
def DerDef (H : HCert) (rd : Reader) (σ : Val) (g : String) (args : List V) : Prop :=
  ∀ k ∈ callDers H g args, ∀ c, H.ders[k]? = some c → (rd (c.addrW (vw σ))).isSome

/-- **What a call of `g` on `args` needs written in `W`**: the cells its ghost words read, and, those being in
memory, its callee's preconditions (`CallPre`). -/
def CallReq (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (W : K → Prop) (g : String)
    (args : List V) : Prop :=
  DerW H σ W g args ∧ (DerDef H rd σ g args → CallPre sigOf H rd σ W g args)

/-- **The words at cells are the memory's**: value `DB + k` holds the word at `ders[k]`, where there is one. -/
def DerOk (H : HCert) (rd : Reader) (σ : Val) : Prop :=
  ∀ k c, H.ders[k]? = some c → ∀ w, rd (c.addrW (vw σ)) = some w → vw σ (DB + k) = w

theorem derOk_nil {H : HCert} (h : H.ders = []) (rd : Reader) (σ : Val) : DerOk H rd σ := fun k c hk ↦ by
  rw [h] at hk; cases hk

theorem callDers_nil {H : HCert} (h : H.gargs = []) (g : String) (args : List V) : callDers H g args = [] := by
  simp [callDers, gargsOf, h, derKs, nubN]

/-- A call naming no word at a cell: its callee's preconditions. -/
theorem CallReq.pre {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {W : K → Prop} {g : String}
    {args : List V} (h : CallReq sigOf H rd σ W g args) (hd : callDers H g args = []) : CallPre sigOf H rd σ W g args :=
  h.2 fun k hk ↦ by rw [hd] at hk; cases hk

/-- What an event needs written in `W`: an atom its reads, an entered call the cells its ghost words read and its
callee's preconditions at its argument and ghost words (`CallReq`). -/
def ReqOk (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (W : K → Prop) : Ev → Prop
  | .atom a => ∀ x, Reads H σ a x → W x
  | .call f args _ => CallReq sigOf H rd σ W f args
  | _ => True

/-- **Every event's needs are written before it.** -/
def ReadsOkC (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (es : List Ev) : Prop :=
  ∀ es1 e es2, es = es1 ++ e :: es2 → ReqOk sigOf H rd σ (WrittenC sigOf H rd σ ws0 es1) e

/-- The values a hint's destination names in the frame. -/
def destStack : Dest → List V
  | .stack cs => cs
  | .heap .. => []

/-- **The values an atom defines in its frame**: a constant's, a sum's, a product's, a copy's, and a hint's
frame destinations. -/
def atomDst : Atom → List V
  | .const d _ => [d]
  | .add d _ _ => [d]
  | .mul d _ _ => [d]
  | .copy d _ => [d]
  | .hint (.witness _ dst) => destStack dst
  | .hint (.bits _ _ _ dst) => destStack dst
  | .hint (.bitsExp _ _ dst) => destStack dst
  | .hint (.digitsExp _ _ _ _ _ _ dst) => destStack dst
  | .hint (.windowsExp _ _ _ _ dst) => destStack dst
  | _ => []

/-- **A frame run's cell at return**: the cell `p·g^i` of a `frameAddr p run` on the path, whose value
`run[i]` an atom on the path defines (the frame cell holding it, written by then). -/
def FAW (σ : Val) (es : List Ev) (x : K) : Prop :=
  ∃ p run i v, Ev.atom (.frameAddr p run) ∈ es ∧ run[i]? = some v ∧ (∃ a, Ev.atom a ∈ es ∧ v ∈ atomDst a) ∧
    x = cellAt σ p i

/-- **The guarantees at return are written**, at the parameters' words `ws0` and the returned `vs`: by the
events, or a frame run's cells (`FAW`). -/
def PostOkC (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (es : List Ev)
    (vs : List V) : Prop :=
  SigOk (fun x ↦ WrittenC sigOf H rd σ ws0 es x ∨ FAW σ es x) H.sig.post H.sig.postR (ws0 ++ vs.map σ) ∧
    PtrOk (fun x ↦ WrittenC sigOf H rd σ ws0 es x ∨ FAW σ es x) rd H.sig.postP H.sig.postPR (ws0 ++ vs.map σ)

/-- **Returned words' monomials**: each `(k, c)` of the signature's `retM`, returned word `k` is
`c`'s word at the parameters' words `ws0`. -/
def RetMOk (G : HSig) (ws0 rets : List E) : Prop := ∀ k c, (k, c) ∈ G.retM → rets[k]? = some (c.valW (slotW ws0))

/-- **Words at return**: each `(i, m)` of the signature's `postV`, the final memory holds `m`'s word at
`post` cell `i`, at the slots' words `ws`. -/
def RetVOk (rd : Reader) (G : HSig) (ws : List E) : Prop :=
  ∀ i m, (i, m) ∈ G.postV → ∃ c, G.post[i]? = some c ∧ rd (c.addrW (slotW ws)) = some (m.valW (slotW ws))

/-- **Equations at return**: each `(a, b)` of the signature's `retEq`, `a`'s word is `b`'s at the slots'
words `ws`. -/
def RetEqOk (G : HSig) (ws : List E) : Prop := ∀ p ∈ G.retEq, p.1.valW (slotW ws) = p.2.valW (slotW ws)

/-- **What an event gives beyond its writes**: an entered call, its callee's returned words'
monomials, words at return and equations at return, at its words. -/
def EvM (sigOf : String → HSig) (rd : Reader) (σ : Val) : Ev → Prop
  | .call f args rets => RetMOk (sigOf f) (args.map σ) (rets.map σ) ∧ RetVOk rd (sigOf f) ((args ++ rets).map σ) ∧
      RetEqOk (sigOf f) ((args ++ rets).map σ)
  | _ => True

/-- **What an instance is given at entry**: its termination facts. -/
def EntryF (H : HCert) (ws0 : List E) : Prop := ∀ p ∈ H.sig.term, LtF (slotW ws0) (idxC p.1) (idxC p.2)

/-- **A branch condition holds** at a valuation: the selector's word is `g^j`, the guard's is `0`, or
not. -/
def CCond.Holds (σ : Val) : CCond → Prop
  | .arm x j => σ (V.n x) = ofK (addressOfIndex j)
  | .zero c => σ (V.n c) = 0
  | .nonzero c => σ (V.n c) ≠ 0

/-- **A residual holds** at a valuation, over value numbers: exponents in order (`lt`), a cell in a
run (`sub`), a run in a run (`subR`), a cell among cells (`subP`), and a residual where its branch
conditions hold (`under`). `nz`, which the check does not use, is `True`. -/
def CRes.Holds (σ : Val) : CRes → Prop
  | .lt a b => LtF (vw σ) (idxC a) (idxC b)
  | .nz _ => True
  | .sub c r => r.Set (vw σ) (c.addrW (vw σ))
  | .subR q r => ∀ x, q.Set (vw σ) x → r.Set (vw σ) x
  | .under g r => (∀ c ∈ g, c.Holds σ) → r.Holds σ
  | .subP c cs => ∃ c' ∈ cs, c.addrW (vw σ) = c'.addrW (vw σ)

/-- **The residuals hold** at the instance. -/
def ResF (H : HCert) (σ : Val) : Prop := ∀ r ∈ H.res, r.Holds σ

theorem resF_nil {H : HCert} (h : H.res = []) (σ : Val) : ResF H σ := fun r hr ↦ by rw [h] at hr; cases hr

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

/-- **A dispatch arm's guarantees**: cells, runs, pointer facts, pointer runs. -/
structure CdA where
  cs : List CCell
  rs : List PRun
  ps : List (CCell × List ℕ)
  prs : List (PRun × List ℕ)

/-- **A dispatch's arms' guarantees under its selector** `mx`: if the selector's word is `g^j`, arm `j` ran, and
`arms[j]` holds (one entry per dispatch, so a later dispatch on `mx` looks up its arm `j` by index). -/
structure CdE where
  mx : CCell
  arms : List CdA

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

/-- How many indices below the upper bound the cell `c` is: `k` with `c·g^(S·k) = base·hi^S`. -/
def backK (R : PRun) (c : CCell) : ℕ := ((R.base.mul (R.hi.pow R.stride)).off - c.off) / R.stride

/-- **A cell `k ≥ 1` indices below the upper bound** (`c·g^(S·k) = base·hi^S`): a constant lower bound
`lo` and a fact `(g^k', hi)`, `k' ≥ k - 1 + lo` (so `e(hi) - k` is past `lo`). -/
def ptBack (F : List (CCell × CCell)) (R : PRun) (c : CCell) : Bool :=
  Nat.blt 0 (backK R c) && (c.shift (R.stride * backK R c)).beq (R.base.mul (R.hi.pow R.stride)) &&
    R.lo.bases.isEmpty && Nat.blt R.lo.off capE && hasFC F (backK R c - 1 + R.lo.off) R.hi

/-- **A cell of a run in scope**: at its lower bound, the bounds a fact; or at a constant index past
a constant lower bound, below a constant upper bound or a fact's; or at any index (`ptIdx`); or some
indices below the upper bound (`ptBack`). -/
def ptRun (F : List (CCell × CCell)) (R : PRun) (c : CCell) : Bool :=
  (c.beq (R.base.mul (R.lo.pow R.stride)) && hasF F R.lo R.hi) || ptIdx F R c (idxOf R.base c R.stride) ||
  ptBack F R c ||
  (basesBeq c.bases R.base.bases && Nat.ble R.base.off c.off && !Nat.beq R.stride 0 &&
    Nat.beq ((c.off - R.base.off) % R.stride) 0 && R.lo.bases.isEmpty && Nat.blt R.lo.off capE &&
    Nat.ble R.lo.off ((c.off - R.base.off) / R.stride) &&
    ((R.hi.bases.isEmpty && Nat.blt R.hi.off capE && Nat.blt ((c.off - R.base.off) / R.stride) R.hi.off) ||
      hasFC F ((c.off - R.base.off) / R.stride) R.hi))

/-- The power `k` of `M` that `x` would be (by `M`'s first base, else its offset). -/
def powK (M x : CCell) : ℕ := match M.bases with
  | (b, e) :: _ => expOf x.bases b / e
  | [] => x.off / M.off

/-- `x = M^k` and `y = N^k` for the equation `(M, N)`. -/
def eqR (p : CCell × CCell) (x y : CCell) : Bool :=
  x.beq (p.1.pow (powK p.1 x)) && y.beq (p.2.pow (powK p.1 x))

/-- **Two monomials with one word**: equal, or powers of the two sides of an equation of `E` (`rename`:
a bound `M^k` with `M = g^c` is `g^(c·k)`). -/
def eqV (E : List (CCell × CCell)) (x y : CCell) : Bool :=
  x.beq y || E.any fun p ↦ eqR p x y || eqR (p.2, p.1) x y

/-- The lower bound of `Q` at or past that of `R`, its exponent existing. -/
def loOk (F : List (CCell × CCell)) (E : List (CCell × CCell)) (Q R : PRun) : Bool :=
  eqV E Q.lo R.lo ||
  (Q.lo.bases.isEmpty && R.lo.bases.isEmpty && Nat.ble R.lo.off Q.lo.off && Nat.blt Q.lo.off capE) ||
  (Q.lo.beq (R.lo.shift 1) && hasF F R.lo R.hi)

/-- The upper bound of `Q` at or below that of `R`, its exponent existing. -/
def hiOk (F : List (CCell × CCell)) (E : List (CCell × CCell)) (Q R : PRun) : Bool :=
  eqV E Q.hi R.hi || hasF F Q.hi R.hi ||
  (Nat.blt 0 Q.hi.off && hasF F ⟨Q.hi.bases, Q.hi.off - 1⟩ R.hi) ||
  (Q.hi.bases.isEmpty && R.hi.bases.isEmpty && Nat.ble Q.hi.off R.hi.off && Nat.blt R.hi.off capE) ||
  (Q.hi.bases.isEmpty && Nat.blt Q.hi.off capE && hasFC F (Q.hi.off - 1) R.hi)

/-- **A run inside a run in scope.** -/
def runRun (F : List (CCell × CCell)) (E : List (CCell × CCell)) (Q R : PRun) : Bool :=
  Q.base.beq R.base && Nat.beq Q.stride R.stride && loOk F E Q R && hiOk F E Q R

/-! ## The pass -/

/-- The pass's state: milestone 1's, a run scope, the sums seen (`ad`, a value number to the
monomials of its first `add`'s operands), the words stored (`sv`, a load event's serial to its cell
and its word's monomial), the cells values were loaded from (`src`), the pointer facts (`pf`, by point
serial) and pointer runs (`pr`, by run serial) in scope, the next run, call and ret serials, and the
guarantees of earlier dispatches' arms under their selectors (`cd`). -/
structure CSt where
  env : Trie CCell
  sc : Trie CCell
  rs : Trie PRun
  ad : Trie (CCell × CCell)
  sv : Trie (CCell × CCell)
  src : Trie CCell
  pf : Trie (CCell × List ℕ)
  pr : Trie (PRun × List ℕ)
  n : ℕ
  nr : ℕ
  nc : ℕ
  nt : ℕ
  cd : List CdE
  /-- Equations between monomials (their words equal). -/
  eqs : List (CCell × CCell)

/-- `k st`, `st` evaluated first. -/
def CSt.seq {β : Type} (st : CSt) (k : CSt → β) : β :=
  st.env.seq fun e ↦ st.sc.seq fun s ↦ st.rs.seq fun r ↦ st.ad.seq fun a ↦ st.sv.seq fun v ↦ st.src.seq fun sr ↦
    st.pf.seq fun pf ↦ st.pr.seq fun pr ↦ natSeq st.n fun n ↦ natSeq st.nr fun nr ↦ natSeq st.nc fun nc ↦
      natSeq st.nt fun nt ↦ k ⟨e, s, r, a, v, sr, pf, pr, n, nr, nc, nt, st.cd, st.eqs⟩

/-- `st`'s scope with `s`'s serials. -/
def CSt.cnt (st s : CSt) : CSt := ⟨st.env, st.sc, st.rs, st.ad, st.sv, st.src, st.pf, st.pr, s.n, s.nr, s.nc, s.nt, st.cd, st.eqs⟩

/-- Milestone 1's part of the state. -/
def CSt.toH (st : CSt) : HSt := ⟨st.env, st.sc, st.n⟩

/-- The state with milestone 1's part `h`. -/
def CSt.ofH (st : CSt) (h : HSt) : CSt :=
  ⟨h.env, h.sc, st.rs, st.ad, st.sv, st.src, st.pf, st.pr, h.n, st.nr, st.nc, st.nt, st.cd, st.eqs⟩

/-- A write event of the cell `c`. -/
noncomputable def CSt.push (st : CSt) (c : CCell) : CSt := st.ofH (st.toH.push c)

/-- A value's first monomial. -/
noncomputable def CSt.def (st : CSt) (k : ℕ) (c : CCell) : CSt := st.ofH (st.toH.def k c)

/-- A load's write event of the cell `c`, the word's monomial `m` stored with its serial. -/
noncomputable def CSt.pushV (st : CSt) (c m : CCell) : CSt :=
  m.seq fun m ↦ (setF (c, m) Exec.indexDepth st.sv st.n).seq fun sv ↦
    (st.push c).seq fun s ↦ ⟨s.env, s.sc, s.rs, s.ad, sv, s.src, s.pf, s.pr, s.n, s.nr, s.nc, s.nt, s.cd, s.eqs⟩

/-- `c` the cell the value `d` was loaded from, if it has none. -/
noncomputable def CSt.srcPut (st : CSt) (d : V) (c : CCell) : CSt :=
  match vnum d with
  | some k => match getF st.src k with
    | some _ => st
    | none => (setF c Exec.indexDepth st.src k).seq fun src ↦
        ⟨st.env, st.sc, st.rs, st.ad, st.sv, src, st.pf, st.pr, st.n, st.nr, st.nc, st.nt, st.cd, st.eqs⟩
  | none => st

/-- `c` the cell the value `k` was loaded from (a word at a cell, `DB + k'`). -/
noncomputable def CSt.setSrc (st : CSt) (k : ℕ) (c : CCell) : CSt :=
  (setF c Exec.indexDepth st.src k).seq fun src ↦
    ⟨st.env, st.sc, st.rs, st.ad, st.sv, src, st.pf, st.pr, st.n, st.nr, st.nc, st.nt, st.cd, st.eqs⟩

/-- A pointer fact into the scope, at the next point serial. -/
noncomputable def CSt.pushP (st : CSt) (p : CCell × List ℕ) : CSt :=
  p.1.seq fun c ↦ (setF (c, p.2) Exec.indexDepth st.pf st.n).seq fun pf ↦
    ⟨st.env, st.sc, st.rs, st.ad, st.sv, st.src, pf, st.pr, st.n + 1, st.nr, st.nc, st.nt, st.cd, st.eqs⟩

/-- A pointer run into the scope, at the next run serial. -/
noncomputable def CSt.pushPR (st : CSt) (p : PRun × List ℕ) : CSt :=
  p.1.seq fun r ↦ (setF (r, p.2) Exec.indexDepth st.pr st.nr).seq fun pr ↦
    ⟨st.env, st.sc, st.rs, st.ad, st.sv, st.src, st.pf, pr, st.n, st.nr + 1, st.nc, st.nt, st.cd, st.eqs⟩

/-- A run into the scope, at the next run serial. -/
noncomputable def CSt.pushR (st : CSt) (r : PRun) : CSt :=
  (setF r Exec.indexDepth st.rs st.nr).seq fun rs ↦
    ⟨st.env, st.sc, rs, st.ad, st.sv, st.src, st.pf, st.pr, st.n, st.nr + 1, st.nc, st.nt, st.cd, st.eqs⟩

/-- The next call serial. -/
def CSt.nextC (st : CSt) : CSt := ⟨st.env, st.sc, st.rs, st.ad, st.sv, st.src, st.pf, st.pr, st.n, st.nr, st.nc + 1, st.nt, st.cd, st.eqs⟩

/-- The next ret serial. -/
def CSt.nextT (st : CSt) : CSt := ⟨st.env, st.sc, st.rs, st.ad, st.sv, st.src, st.pf, st.pr, st.n, st.nr, st.nc, st.nt + 1, st.cd, st.eqs⟩

/-- An equation kept. -/
def CSt.addEq (st : CSt) (p : CCell × CCell) : CSt :=
  ⟨st.env, st.sc, st.rs, st.ad, st.sv, st.src, st.pf, st.pr, st.n, st.nr, st.nc, st.nt, st.cd, p :: st.eqs⟩

/-- Equations kept. -/
def CSt.addEqs (st : CSt) (l : List (CCell × CCell)) : CSt :=
  ⟨st.env, st.sc, st.rs, st.ad, st.sv, st.src, st.pf, st.pr, st.n, st.nr, st.nc, st.nt, st.cd, l ++ st.eqs⟩

/-- The sum `k = a + b` seen, if `k` has none yet. -/
noncomputable def CSt.addS (st : CSt) (k : ℕ) (a b : CCell) : CSt :=
  match getF st.ad k with
  | some _ => st
  | none => (setF (a, b) Exec.indexDepth st.ad k).seq fun ad ↦
      ⟨st.env, st.sc, st.rs, ad, st.sv, st.src, st.pf, st.pr, st.n, st.nr, st.nc, st.nt, st.cd, st.eqs⟩

/-- What the pass reads. -/
structure CX where
  pows : PowTree
  R : Trie (List (ℕ × ℕ × Wit))
  pre : Trie CCell
  C : Trie (List Wit)
  T : Trie (List Wit)
  res : Trie CRes
  dv : Trie Unit
  hv : Trie Unit
  ga : List (String × List ℕ × List CCell)
  sigOf : String → HSig
  sig : HSig
  params : List V
  /-- The branch conditions of the blocks enclosing the site. -/
  path : List CCond
  /-- The atoms whose equations are kept (`HCert.eqs`). -/
  eqk : Trie Unit
  /-- The frame run cells guaranteed at return (`HCert.fas`). -/
  fas : List (ℕ × ℕ)
  /-- The cells whose words are the values `DB + k` (`HCert.ders`). -/
  ders : List CCell

/-- Milestone 1's part. -/
def CX.toH (X : CX) : HX := ⟨X.pows, X.R, X.pre⟩

/-- The site under the further branch conditions `l`. -/
def CX.ext (X : CX) (l : List CCond) : CX :=
  ⟨X.pows, X.R, X.pre, X.C, X.T, X.res, X.dv, X.hv, X.ga, X.sigOf, X.sig, X.params, l ++ X.path, X.eqk, X.fas,
    X.ders⟩

/-- Two branch conditions are equal. -/
def CCond.beq : CCond → CCond → Bool
  | .arm x j, .arm x' j' => Nat.beq x x' && Nat.beq j j'
  | .zero c, .zero c' => Nat.beq c c'
  | .nonzero c, .nonzero c' => Nat.beq c c'
  | _, _ => false

/-- The conditions `g` all on the path. -/
def onPath (path g : List CCond) : Bool := g.all fun c ↦ path.any (CCond.beq c)

/-- **A residual on the path**: `under g r` is `r` (on the path) when the path has `g`. -/
def unU (path : List CCond) : CRes → Option CRes
  | .under g r => bif onPath path g then unU path r else none
  | .lt a b => some (.lt a b)
  | .nz v => some (.nz v)
  | .sub c r => some (.sub c r)
  | .subR q r => some (.subR q r)
  | .subP c cs => some (.subP c cs)

/-- The residual `i` at the site. -/
noncomputable def resAt (X : CX) (i : ℕ) : Option CRes :=
  match getF X.res i with
  | some r => unU X.path r
  | none => none

/-- The condition that `c`'s word is `0`, `c` a value. -/
def czero (c : V) : List CCond := match vnum c with
  | some k => [.zero k]
  | none => []

/-- The condition that `c`'s word is not `0`. -/
def cnz (c : V) : List CCond := match vnum c with
  | some k => [.nonzero k]
  | none => []

/-- The condition that `x`'s word is `g^j`. -/
def carm (x : V) (j : ℕ) : List CCond := match vnum x with
  | some k => [.arm k j]
  | none => []

/-- The facts of a monomial of exponent `e` (`e + 1 < 2^62`): `(g^(e-1), m)` if `e > 0`, and `(m, g^(e+1))`. -/
def expFacts (m : CCell) (e : ℕ) : List (CCell × CCell) :=
  bif Nat.blt (e + 1) capE then
    (bif Nat.beq e 0 then [] else [(⟨[], e - 1⟩, m)]) ++ [(m, ⟨[], e + 1⟩)]
  else []

/-- A selector's monomial `b·g^t` of exponent `j`, `t ≤ j`: its base `b`'s facts, of exponent `j - t`. -/
def baseFacts (m : CCell) (j : ℕ) : List (CCell × CCell) :=
  match m.bases with
  | [(b, 1)] => bif Nat.ble m.off j then expFacts (baseC b) (j - m.off) else []
  | _ => []

/-- **The facts a path gives**: under arm `j` of a selector `x`, `x`'s exponent is `j` (`expFacts`), and,
`x`'s monomial being `b·g^t`, `b`'s is `j - t` (`baseFacts`). -/
noncomputable def pathF (env : Trie CCell) : List CCond → List (CCell × CCell)
  | [] => []
  | .arm x j :: l => expFacts (idxF env (.val x)) j ++ baseFacts (idxF env (.val x)) j ++ pathF env l
  | .zero _ :: l => pathF env l
  | .nonzero _ :: l => pathF env l

/-- **The facts at a witness**: the own termination facts, the residuals it lists that hold on the
site's path, and the path's own facts, as monomials. -/
noncomputable def facts (X : CX) (env : Trie CCell) (res : List ℕ) : List (CCell × CCell) :=
  X.sig.term.map (fun p ↦ (idxF env p.1, idxF env p.2)) ++
    res.filterMap (fun i ↦ match resAt X i with
      | some (.lt a b) => some (idxF env a, idxF env b)
      | _ => none) ++ pathF env X.path

/-- A residual's run in the pass's monomials: bounds through the environment, as facts. -/
noncomputable def runF (env : Trie CCell) (r : CRun) : PRun := ⟨r.base, r.stride, idxF env r.lo, idxF env r.hi⟩

/-- **A residual placing the cell `c` in the run `R`**: `sub c R`, or `subR q R` with `c` a cell of `q`. -/
noncomputable def subPt (X : CX) (F : List (CCell × CCell)) (env : Trie CCell) (res : List ℕ) (R : PRun)
    (c : CCell) : Bool :=
  res.any fun i ↦ match resAt X i with
    | some (.sub c' r') => c'.beq c && (runF env r').beq R
    | some (.subR q r') => (runF env r').beq R && ptRun F (runF env q) c
    | _ => false

/-- **A residual placing the run `Q` in the run `R`**: `subR Q R`. -/
noncomputable def subRun (X : CX) (env : Trie CCell) (res : List ℕ) (Q R : PRun) : Bool :=
  res.any fun i ↦ match resAt X i with
    | some (.subR q r') => (runF env q).beq Q && (runF env r').beq R
    | _ => false

/-- The cell the word under the cell `c = b·g^o` was loaded from: `b`'s (`src`). -/
noncomputable def srcOf (st : CSt) (c : CCell) : Option CCell :=
  match c.bases with
  | [(b, e)] => bif Nat.beq e 1 then getF st.src b else none
  | _ => none

/-- A monomial with an exponent: a constant below `2^62`, or one side of a fact. -/
def hasExp (F : List (CCell × CCell)) (m : CCell) : Bool :=
  (m.bases.isEmpty && Nat.blt m.off capE) || F.any fun p ↦ p.1.beq m || p.2.beq m

/-- The cells each the write event in scope of the serial at its position. -/
noncomputable def permW (st : CSt) : List CCell → List ℕ → Bool
  | [], [] => true
  | c :: cs, n :: ns => (match getF st.sc n with
    | some c' => c'.beq c
    | none => false) && permW st cs ns
  | _, _ => false

/-- The point before a run: its base over `g^stride`. -/
def prepQ (R : PRun) : CCell := ⟨R.base.bases, R.base.off - R.stride⟩

/-- **A cell of a run extended by its point before it**: `c = Q·J^S` (`Q = prepQ R`, `S` the stride), the
run from `g^0`, `J` the upper bound up to a constant below `2^62`, the upper bound with an exponent,
and `J` too (it is the upper bound, or by a fact). -/
def prepIdx (F : List (CCell × CCell)) (R : PRun) (c : CCell) : Bool :=
  Nat.ble R.stride R.base.off && R.lo.bases.isEmpty && Nat.beq R.lo.off 0 &&
    c.beq ((prepQ R).mul ((idxOf (prepQ R) c R.stride).pow R.stride)) &&
    basesBeq (idxOf (prepQ R) c R.stride).bases R.hi.bases && Nat.ble (idxOf (prepQ R) c R.stride).off R.hi.off &&
    Nat.blt (R.hi.off - (idxOf (prepQ R) c R.stride).off) capE && hasExp F R.hi &&
    ((idxOf (prepQ R) c R.stride).beq R.hi || hasExp F (idxOf (prepQ R) c R.stride))

/-- **A witness of the cell `c`.** -/
noncomputable def ptOk (X : CX) (st : CSt) (c : CCell) : Wit → Bool
  | .ev n => match getF st.sc n with
    | some c' => c'.beq c
    | none => false
  | .pre k => match getF X.pre k with
    | some c' => c'.beq c
    | none => false
  | .run r res => match getF st.rs r with
    | some R => ptRun (facts X st.env res) R c || subPt X (facts X st.env res) st.env res R c
    | none => false
  | .pf n => match getF st.pf n, srcOf st c with
    | some p, some a => a.beq p.1 && p.2.any (Nat.beq c.off)
    | _, _ => false
  | .pfr r res => match getF st.pr r, srcOf st c with
    | some p, some a => ptRun (facts X st.env res) p.1 a && p.2.any (Nat.beq c.off)
    | _, _ => false
  | .perm k ns => match resAt X k with
    | some (.subP c' cs) => c'.beq c && permW st cs ns
    | _ => false
  | .prep r q res => match getF st.rs r with
    | some R => prepIdx (facts X st.env res) R c && ptOk X st (prepQ R) q
    | none => false
  | _ => false

/-- A run with constant bounds, the upper at most the lower (below `2^62`): it has no cell. -/
def emptyR (Q : PRun) : Bool :=
  Q.lo.bases.isEmpty && Q.hi.bases.isEmpty && Nat.ble Q.hi.off Q.lo.off && Nat.blt Q.lo.off capE

/-- Constant bounds, below `2^62`. -/
def constR (Q : PRun) : Bool :=
  Q.lo.bases.isEmpty && Q.hi.bases.isEmpty && Nat.blt Q.lo.off capE && Nat.blt Q.hi.off capE

/-- **A witness of the run `Q`.** -/
noncomputable def rnOk (X : CX) (st : CSt) (Q : PRun) : Wit → Bool
  | .run r res => match getF st.rs r with
    | some R => runRun (facts X st.env res) st.eqs Q R || subRun X st.env res Q R
    | none => false
  | .empty => emptyR Q
  | _ => false

/-- The offsets all among `o`. -/
def subL (offs o : List ℕ) : Bool := offs.all fun x ↦ o.any (Nat.beq x)

/-- The cells `m·g^o`, `o ∈ offs`, each with a witness: the witnesses left. -/
noncomputable def ptsW (X : CX) (st : CSt) (m : CCell) : List ℕ → List Wit → Option (List Wit)
  | [], ws => some ws
  | o :: os, w :: ws => bif ptOk X st (m.shift o) w then ptsW X st m os ws else none
  | _ :: _, [] => none

/-- **A pointer fact needed**, the word at the cell `c` pointing to written cells at `offs`: a
pointer fact in scope at `c` with them, a pointer run holding `c` with them, or `c`'s word named by a
load event and the cells past it witnessed. The witnesses left. -/
noncomputable def ptrOk (X : CX) (st : CSt) (c : CCell) (offs : List ℕ) : List Wit → Option (List Wit)
  | .pf n :: ws => match getF st.pf n with
    | some p => bif p.1.beq c && subL offs p.2 then some ws else none
    | none => none
  | .pfr r res :: ws => match getF st.pr r with
    | some p => bif ptRun (facts X st.env res) p.1 c && subL offs p.2 then some ws else none
    | none => none
  | .word m :: ws => match getF st.sv m with
    | some p => bif p.1.beq c then ptsW X st p.2 offs ws else none
    | none => none
  | _ => none

/-- Pointer facts needed at the cells `b·g^(S·j)`, `n` of them from `j`: the witnesses left. -/
noncomputable def ptrPts (X : CX) (st : CSt) (b : CCell) (S : ℕ) (offs : List ℕ) :
    ℕ → ℕ → List Wit → Option (List Wit)
  | _, 0, ws => some ws
  | j, n + 1, ws => match ptrOk X st (b.shift (S * j)) offs ws with
    | some ws' => ptrPts X st b S offs (j + 1) n ws'
    | none => none

/-- **A pointer run needed**: inside a pointer run in scope with the offsets, empty, or each of its
cells' pointer facts (constant bounds). The witnesses left. -/
noncomputable def ptrROk (X : CX) (st : CSt) (Q : PRun) (offs : List ℕ) : List Wit → Option (List Wit)
  | .pfr r res :: ws => match getF st.pr r with
    | some p => bif runRun (facts X st.env res) st.eqs Q p.1 && subL offs p.2 then some ws else none
    | none => none
  | .empty :: ws => bif emptyR Q then some ws else none
  | .pts :: ws => bif constR Q
      then ptrPts X st Q.base Q.stride offs Q.lo.off (Q.hi.off - Q.lo.off) ws else none
  | _ => none

/-- Signature cells at the slots `ms`, each with its witness: the witnesses left. -/
noncomputable def reqP (X : CX) (st : CSt) (ms : List CCell) : List CCell → List Wit → Option (List Wit)
  | [], ws => some ws
  | c :: cs, w :: ws => match instC ms c with
    | some c' => bif ptOk X st c' w then reqP X st ms cs ws else none
    | none => none
  | _ :: _, [] => none

/-- Points needed at the cells `b·g^(S·j)`, `n` of them from `j`, one witness each: the witnesses
left. -/
noncomputable def ptsRun (X : CX) (st : CSt) (b : CCell) (S : ℕ) : ℕ → ℕ → List Wit → Option (List Wit)
  | _, 0, ws => some ws
  | j, n + 1, w :: ws => bif ptOk X st (b.shift (S * j)) w then ptsRun X st b S (j + 1) n ws else none
  | _, _ + 1, [] => none

/-- A run needed, one part: its witness, or `pts` and one point witness per cell (constant bounds).
The witnesses left. -/
noncomputable def runOk1 (X : CX) (st : CSt) (Q : PRun) : List Wit → Option (List Wit)
  | .pts :: ws => bif constR Q then ptsRun X st Q.base Q.stride Q.lo.off (Q.hi.off - Q.lo.off) ws else none
  | w :: ws => bif rnOk X st Q w then some ws else none
  | [] => none

/-- A monomial's `S`-th root, if it is an `S`-th power (`pow` checks back). -/
def rootC (c : CCell) (S : ℕ) : CCell := ⟨c.bases.map fun b ↦ (b.1, b.2 / S), c.off / S⟩

/-- Residue `r` of a run of stride `S'` split in `S`: `base·g^(S'·r)`, stride `S'·S`, the bounds given. -/
def mrgPart (Q : PRun) (S r : ℕ) (lo hi : CCell) : PRun := ⟨Q.base.shift (Q.stride * r), Q.stride * S, lo, hi⟩

/-- Residues `r` to `r + n - 1`, one part each: the witnesses left. -/
noncomputable def mrgW (X : CX) (st : CSt) (Q : PRun) (S : ℕ) (lo hi : CCell) : ℕ → ℕ → List Wit →
    Option (List Wit)
  | _, 0, ws => some ws
  | r, n + 1, ws => match runOk1 X st (mrgPart Q S r lo hi) ws with
    | some ws' => mrgW X st Q S lo hi (r + 1) n ws'
    | none => none

/-- **A run needed, one level**: one part (`runOk1`); `cat k` and the parts below and from the constant index
`k` (`k < 2^62`); or `mrg S res` and its `S` residues (`mrgW`; a constant lower bound, a multiple of
`S`, an upper bound an `S`-th power whose root has an exponent), or `mrgE S r res`, the root `r` given (its
`S`-th power the upper bound's word, `eqV`). The witnesses left. -/
noncomputable def runOk0 (X : CX) (st : CSt) (Q : PRun) : List Wit → Option (List Wit)
  | .cat k :: ws => bif Nat.blt k capE then
      (match runOk1 X st ⟨Q.base, Q.stride, Q.lo, ⟨[], k⟩⟩ ws with
      | some ws' => runOk1 X st ⟨Q.base, Q.stride, ⟨[], k⟩, Q.hi⟩ ws'
      | none => none) else none
  | .mrg S res :: ws => bif Nat.blt 0 S && Q.lo.bases.isEmpty && Nat.beq (Q.lo.off % S) 0 && Nat.blt Q.lo.off capE &&
        ((rootC Q.hi S).pow S).beq Q.hi && hasExp (facts X st.env res) (rootC Q.hi S) then
      mrgW X st Q S ⟨[], Q.lo.off / S⟩ (rootC Q.hi S) 0 S ws else none
  | .mrgE S r res :: ws => bif Nat.blt 0 S && Q.lo.bases.isEmpty && Nat.beq (Q.lo.off % S) 0 &&
        Nat.blt Q.lo.off capE && eqV st.eqs (r.pow S) Q.hi && hasExp (facts X st.env res) r then
      mrgW X st Q S ⟨[], Q.lo.off / S⟩ r 0 S ws else none
  | ws => runOk1 X st Q ws

/-- **A run needed, split once**: `runOk0`, or `catM k h res` and its parts below and from the index `k`
(`runOk0` each): `k·h` the upper bound's word (`eqV`), `k`'s and `h`'s exponents existing (constants or sides of
facts), the part from `k` of base `base·k^stride` from `g^0` to `h`. The witnesses left. -/
noncomputable def runOkL (X : CX) (st : CSt) (Q : PRun) : List Wit → Option (List Wit)
  | .catM k h res :: ws => bif eqV st.eqs (k.mul h) Q.hi && hasExp (facts X st.env res) k &&
        hasExp (facts X st.env res) h then
      (match runOk0 X st ⟨Q.base, Q.stride, Q.lo, k⟩ ws with
      | some ws' => runOk0 X st ⟨Q.base.mul (k.pow Q.stride), Q.stride, ⟨[], 0⟩, h⟩ ws'
      | none => none) else none
  | ws => runOk0 X st Q ws

/-- **A run needed**: `runOkL`, but the part from `k` of a `catM` may be split again (`runOkL`). The witnesses
left. -/
noncomputable def runOk (X : CX) (st : CSt) (Q : PRun) : List Wit → Option (List Wit)
  | .catM k h res :: ws => bif eqV st.eqs (k.mul h) Q.hi && hasExp (facts X st.env res) k &&
        hasExp (facts X st.env res) h then
      (match runOk0 X st ⟨Q.base, Q.stride, Q.lo, k⟩ ws with
      | some ws' => runOkL X st ⟨Q.base.mul (k.pow Q.stride), Q.stride, ⟨[], 0⟩, h⟩ ws'
      | none => none) else none
  | ws => runOk0 X st Q ws

/-- Signature runs at the slots `ms`, each with its witnesses: the witnesses left. -/
noncomputable def reqR (X : CX) (st : CSt) (ms : List CCell) : List CRun → List Wit → Option (List Wit)
  | [], ws => some ws
  | r :: rs, ws => match instR ms r with
    | some q => match runOk X st q ws with
      | some ws' => reqR X st ms rs ws'
      | none => none
    | none => none

/-- Signature pointer facts at the slots `ms`, each with its witnesses: the witnesses left. -/
noncomputable def reqPP (X : CX) (st : CSt) (ms : List CCell) : List (CCell × List ℕ) → List Wit →
    Option (List Wit)
  | [], ws => some ws
  | p :: ps, ws => match instC ms p.1 with
    | some c => match ptrOk X st c p.2 ws with
      | some ws' => reqPP X st ms ps ws'
      | none => none
    | none => none

/-- Signature pointer runs at the slots `ms`, each with its witnesses: the witnesses left. -/
noncomputable def reqPR (X : CX) (st : CSt) (ms : List CCell) : List (CRun × List ℕ) → List Wit →
    Option (List Wit)
  | [], ws => some ws
  | p :: ps, ws => match instR ms p.1 with
    | some q => match ptrROk X st q p.2 ws with
      | some ws' => reqPR X st ms ps ws'
      | none => none
    | none => none

/-- A signature's preconditions at the slots `ms`: the witnesses left. -/
noncomputable def reqS (X : CX) (st : CSt) (ms : List CCell) (G : HSig) (ws : List Wit) :
    Option (List Wit) :=
  match reqP X st ms G.pre ws with
  | some ws1 => match reqR X st ms G.preR ws1 with
    | some ws2 => match reqPP X st ms G.preP ws2 with
      | some ws3 => reqPR X st ms G.prePR ws3
      | none => none
    | none => none
  | none => none

/-- The cells `ders[k]`, `k ∈ ks`, each with a point witness: the witnesses left. -/
noncomputable def derWs (X : CX) (st : CSt) : List ℕ → List Wit → Option (List Wit)
  | [], ws => some ws
  | k :: ks, w :: ws => match nth X.ders k with
    | some c => bif ptOk X st c w then derWs X st ks ws else none
    | none => none
  | _ :: _, [] => none

/-- The values `DB + k`, `k ∈ ks`, loaded from the cells `ders[k]` (`src`). -/
noncomputable def derSt (X : CX) : List ℕ → CSt → CSt
  | [], st => st
  | k :: ks, st => match nth X.ders k with
    | some c => (st.setSrc (DB + k) c).seq fun st ↦ derSt X ks st
    | none => derSt X ks st

/-- **A callee's preconditions at a call** of `g` on `args` (monomials `ma`): the ghost monomials the
certificate names, as many as `g` has ghosts, after the arguments; first, the cells of the words at cells they
name (`derKs`) each witnessed, then the preconditions with those words loaded from their cells (`derSt`). The
witnesses left. -/
noncomputable def reqG (X : CX) (st : CSt) (ma : List CCell) (g : String) (args : List V) (ws : List Wit) :
    Option (List Wit) :=
  bif Nat.beq (gargsOf X.ga g args).length (X.sigOf g).ghosts then
    (match derWs X st (derKs (gargsOf X.ga g args)) ws with
    | some ws' => reqS X (derSt X (derKs (gargsOf X.ga g args)) st) (ma ++ gargsOf X.ga g args) (X.sigOf g) ws'
    | none => none) else none

/-- A fact `(a, g^h)` with `h ≤ j`, `h < 2^62`: the exponent of `a` below `j`. -/
def hasFU (F : List (CCell × CCell)) (a : CCell) (j : ℕ) : Bool :=
  F.any fun p ↦ p.1.beq a && p.2.bases.isEmpty && Nat.ble p.2.off j && Nat.blt p.2.off capE

/-- **A dispatch arm left out**, arm `j` of the selector `mx`: `skip res` and a fact of `res` putting
`mx`'s exponent below `j` (`j < 2^62`). The witnesses left. -/
noncomputable def armSkip (X : CX) (st : CSt) (mx : CCell) (j : ℕ) : List Wit → Option (List Wit)
  | .skip res :: ws => bif Nat.blt j capE && hasFU (facts X st.env res) mx j then some ws else none
  | _ => none

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

/-- Signature pointer facts at the slots `ms`. -/
def instPP (ms : List CCell) : List (CCell × List ℕ) → Option (List (CCell × List ℕ))
  | [] => some []
  | p :: ps => match instC ms p.1, instPP ms ps with
    | some c, some l => some ((c, p.2) :: l)
    | _, _ => none

/-- Signature pointer runs at the slots `ms`. -/
def instPRL (ms : List CCell) : List (CRun × List ℕ) → Option (List (PRun × List ℕ))
  | [] => some []
  | p :: ps => match instR ms p.1, instPRL ms ps with
    | some q, some l => some ((q, p.2) :: l)
    | _, _ => none

/-- Pointer facts into the scope, in order. -/
noncomputable def pushPL : List (CCell × List ℕ) → CSt → CSt
  | [], st => st
  | p :: ps, st => (st.pushP p).seq fun st ↦ pushPL ps st

/-- Pointer runs into the scope, in order. -/
noncomputable def pushPRL : List (PRun × List ℕ) → CSt → CSt
  | [], st => st
  | p :: ps, st => (st.pushPR p).seq fun st ↦ pushPRL ps st

/-- **Guarantees under a selector**, for arm `j` of a dispatch on the selector `mx`: those of each
earlier dispatch's arm `j` on the same selector, pushed (its cells, pointer facts, runs, pointer runs). -/
noncomputable def condSt (mx : CCell) (j : ℕ) : List CdE → CSt → CSt
  | [], st => st
  | e :: l, st => bif e.mx.beq mx then
      (match nth e.arms j with
      | some a => (pushPRL a.prs (pushRL a.rs (pushPL a.ps (pushL a.cs st)))).seq fun st ↦ condSt mx j l st
      | none => condSt mx j l st)
    else condSt mx j l st

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

/-- A callee's `retM` at the slots `ms`, the entries that instantiate. -/
def instRM (ms : List CCell) (l : List (ℕ × CCell)) : List (ℕ × CCell) :=
  l.filterMap fun p ↦ (instC ms p.2).map fun c ↦ (p.1, c)

/-- The returned values' monomials, `(k, m)`: `rets[k]` gets `m` if it has none. -/
noncomputable def retDefs (rets : List V) : List (ℕ × CCell) → CSt → CSt
  | [], st => st
  | (k, m) :: l, st => match nth rets k with
    | some r => match vnum r with
      | some kr => (st.def kr m).seq fun st ↦ retDefs rets l st
      | none => retDefs rets l st
    | none => retDefs rets l st

/-- A callee's guarantees at the slots `ms` pushed: its `post` cells, `postP` facts (point serials),
`postR` runs, `postPR` runs (run serials). -/
noncomputable def pushPost (G : HSig) (ms : List CCell) (st : CSt) : Option CSt :=
  match instAll ms G.post, instPP ms G.postP, instAllR ms G.postR, instPRL ms G.postPR with
  | some ps, some pps, some rs, some prs => some (pushPRL prs (pushRL rs (pushPL pps (pushL ps st))))
  | _, _, _, _ => none

/-- A list with entry `n` replaced. -/
def setNth {α : Type} : List α → ℕ → α → List α
  | [], _, _ => []
  | _ :: l, 0, b => b :: l
  | a :: l, n + 1, b => a :: setNth l n b

/-- An arm's returned words' monomials: `mr` with its callee's `retM` entries (instantiated) in place. -/
def setRM (mr : List CCell) : List (ℕ × CCell) → List CCell
  | [] => mr
  | (k, m) :: l => setNth (setRM mr l) k m

/-- The cells `mr[j]·g^o` for each `(j, offs)`, `o ∈ offs`, each with a witness: the witnesses left. -/
noncomputable def vpPts (X : CX) (st : CSt) (mr : List CCell) : List (ℕ × List ℕ) → List Wit → Option (List Wit)
  | [], ws => some ws
  | (j, offs) :: l, ws => match nth mr j with
    | some m => match ptsW X st m offs ws with
      | some ws' => vpPts X st mr l ws'
      | none => none
    | none => none

/-- **A dispatch arm's returned pointers** `vps` (`(j, offs)`: returned word `j`'s cells at `offs`), with
the callee `g` on the arguments `ma`: in the state with the callee's guarantees pushed, its returned
words named by its `retM`, each cell witnessed. The witnesses left. -/
noncomputable def vpArm (X : CX) (st : CSt) (ma : List CCell) (g : String) (rets : List V)
    (vps : List (ℕ × List ℕ)) (ws : List Wit) : Option (List Wit) :=
  match vps with
  | [] => some ws
  | _ :: _ => match monos st.env rets with
    | some mr0 => match pushPost (X.sigOf g) (ma ++ setRM mr0 (instRM ma (X.sigOf g).retM)) st with
      | some S => vpPts X S (setRM mr0 (instRM ma (X.sigOf g).retM)) vps ws
      | none => none
    | none => none

/-- A dispatch's leading `vp` entries, and the witnesses after them. -/
def vpHead : List Wit → List (ℕ × List ℕ) × List Wit
  | .vp j offs :: ws => ((j, offs) :: (vpHead ws).1, (vpHead ws).2)
  | ws => ([], ws)

/-- A dispatch's leading `ab` entries (after its `vp`s), and the witnesses after them. -/
def abHead : List Wit → List (CCell × ℕ × ℕ) × List Wit
  | .ab q S d :: ws => ((q, S, d) :: (abHead ws).1, (abHead ws).2)
  | ws => ([], ws)

/-- The runs `⟨q, S, 0, j + d⟩` of a dispatch arm `j`'s blocks, each with its witnesses: the witnesses left. -/
noncomputable def abRuns (X : CX) (st : CSt) (j : ℕ) : List (CCell × ℕ × ℕ) → List Wit → Option (List Wit)
  | [], ws => some ws
  | (q, S, d) :: l, ws => match runOk X st ⟨q, S, ⟨[], 0⟩, ⟨[], j + d⟩⟩ ws with
    | some ws' => abRuns X st j l ws'
    | none => none

/-- **A dispatch arm `j`'s blocks** `abs` (`(q, S, d)`: the run `⟨q, S, 0, j + d⟩`), with the callee `g` on the
arguments `ma`: in the state with the callee's guarantees pushed (as `vpArm`), each run witnessed. The witnesses
left. -/
noncomputable def abArm (X : CX) (st : CSt) (ma : List CCell) (g : String) (rets : List V) (j : ℕ)
    (abs : List (CCell × ℕ × ℕ)) (ws : List Wit) : Option (List Wit) :=
  match abs with
  | [] => some ws
  | _ :: _ => match monos st.env rets with
    | some mr0 => match pushPost (X.sigOf g) (ma ++ setRM mr0 (instRM ma (X.sigOf g).retM)) st with
      | some S => abRuns X S j abs ws
      | none => none
    | none => none

/-- The runs a dispatch's blocks give, `x`'s monomial `mx`: `⟨q, S, g^0, mx·g^d⟩`. -/
def abPost (mx : CCell) (abs : List (CCell × ℕ × ℕ)) : List PRun :=
  abs.map fun p ↦ ⟨p.1, p.2.1, ⟨[], 0⟩, mx.shift p.2.2⟩

/-- The cells of a dispatch's returned pointers, at the returned words' monomials `mr`. -/
def vpCells (mr : List CCell) (vps : List (ℕ × List ℕ)) : List CCell :=
  vps.flatMap fun p ↦ match nth mr p.1 with
    | some m => p.2.map m.shift
    | none => []

/-- Each arm's preconditions at the slots `ms`, arm indices from `j`, an arm left out by `armSkip`;
arm `j`'s seeing the guarantees of earlier dispatches' arms `j` on the same selector (`condSt`), then its
returned pointers (`vpArm`) and blocks (`abArm`): the witnesses left and the arms kept. -/
noncomputable def reqArmsX (X : CX) (st : CSt) (ms : List CCell) (args rets : List V) (vps : List (ℕ × List ℕ))
    (abs : List (CCell × ℕ × ℕ)) (x : V) (mx : CCell) : ℕ → List String → List Wit → Option (List Wit × List String)
  | _, [], ws => some (ws, [])
  | j, g :: gs, ws => match armSkip X st mx j ws with
    | some ws' => reqArmsX X st ms args rets vps abs x mx (j + 1) gs ws'
    | none => match reqG (X.ext (carm x j)) (condSt mx j st.cd st) ms g args ws with
      | some ws' => match vpArm (X.ext (carm x j)) (condSt mx j st.cd st) ms g rets vps ws' with
        | some ws'' => match abArm (X.ext (carm x j)) (condSt mx j st.cd st) ms g rets j abs ws'' with
          | some ws3 => (reqArmsX X st ms args rets vps abs x mx (j + 1) gs ws3).map fun p ↦ (p.1, g :: p.2)
          | none => none
        | none => none
      | none => none

/-- A signature's equations at the slots `ms`, those that instantiate. -/
def instEq (ms : List CCell) (l : List (CCell × CCell)) : List (CCell × CCell) :=
  l.filterMap fun p ↦ match instC ms p.1, instC ms p.2 with
    | some a, some b => some (a, b)
    | _, _ => none

/-- A callee's words at return, at the slots `ms`, keyed by the point serials its `post` cells get from
`n0`: `(serial, cell, word's monomial)`. -/
def postVE (G : HSig) (ms : List CCell) (n0 : ℕ) : List (ℕ × CCell × CCell) :=
  G.postV.filterMap fun p ↦ match nth G.post p.1 with
    | some c => match instC ms c, instC ms p.2 with
      | some c', some m' => some (n0 + p.1, c', m')
      | _, _ => none
    | none => none

/-- Words stored, by point serial (`sv`). -/
noncomputable def svPut : List (ℕ × CCell × CCell) → CSt → CSt
  | [], st => st
  | p :: l, st => (setF p.2 Exec.indexDepth st.sv p.1).seq fun sv ↦
      svPut l ⟨st.env, st.sc, st.rs, st.ad, sv, st.src, st.pf, st.pr, st.n, st.nr, st.nc, st.nt, st.cd, st.eqs⟩

/-- **A call**: its callee's preconditions at its arguments; its returned words' monomials (`retM`),
then its guarantees at its words pushed, its words at return (`postV`) stored at its `post` cells'
serials. -/
noncomputable def callC (X : CX) (st : CSt) (g : String) (args rets : List V) : Option CSt :=
  match monos st.env args, getF X.C st.nc with
  | some ma, some ws => match reqG X st ma g args ws with
    | some [] => (retDefs rets (instRM ma (X.sigOf g).retM) st.nextC).seq fun st1 ↦
        match monos st1.env rets with
        | some mr => (pushPost (X.sigOf g) (ma ++ mr) st1).map fun st2 ↦
            (svPut (postVE (X.sigOf g) (ma ++ mr) st1.n) st2).addEqs (instEq (ma ++ mr) (X.sigOf g).retEq)
        | none => none
    | _ => none
  | _, _ => none

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
  | some ma, some ws => match reqG (X.ext (cnz c)) st ma g args ws with
    | some [] => match sumOf st c, instAllR ma (X.sigOf g).postR, instPRL ma (X.sigOf g).postPR with
      | some p, some qs, some prs =>
        some (pushPRL (prs.filter fun q ↦ boundsOf p q.1) (pushRL (qs.filter (boundsOf p)) st.nextC))
      | _, _, _ => some st.nextC
    | _ => none
  | _, _ => none

/-- Two pointer facts are equal. -/
def pfBeq (p q : CCell × List ℕ) : Bool := p.1.beq q.1 && p.2 == q.2

/-- Two pointer runs are equal. -/
def prBeq (p q : PRun × List ℕ) : Bool := p.1.beq q.1 && p.2 == q.2

/-- Each callee's pointer guarantees at the slots `ms`. -/
def instArmsP (sigOf : String → HSig) (ms : List CCell) : List String →
    Option (List (List (CCell × List ℕ)) × List (List (PRun × List ℕ)))
  | [] => some ([], [])
  | g :: gs => match instPP ms (sigOf g).postP, instPRL ms (sigOf g).postPR, instArmsP sigOf ms gs with
    | some p, some r, some (ps, rs) => some (p :: ps, r :: rs)
    | _, _, _ => none

/-- The pointer guarantees every arm gives, pushed: the first arm's pointer facts (point serials) and
pointer runs (run serials) every other has; none if one does not instantiate. -/
noncomputable def pushPtrM : Option (List (List (CCell × List ℕ)) × List (List (PRun × List ℕ))) → CSt → CSt
  | some (p :: ps, r :: rs), st =>
    pushPRL (r.filter fun q ↦ rs.all fun l ↦ l.any fun q' ↦ prBeq q' q)
      (pushPL (p.filter fun q ↦ ps.all fun l ↦ l.any fun q' ↦ pfBeq q' q) st)
  | _, st => st

/-- The returned words' monomials every list has. -/
def meetM (ls : List (List (ℕ × CCell))) (p : ℕ × CCell) : Bool :=
  ls.all fun l ↦ l.any fun q ↦ Nat.beq q.1 p.1 && q.2.beq p.2

/-- Each arm's guarantees at the slots `ms`, in arm order (none for an arm whose guarantees do not
instantiate). -/
def condE (sigOf : String → HSig) (ms : List CCell) : List String → List CdA
  | [] => []
  | g :: gs => (match instAll ms (sigOf g).post, instAllR ms (sigOf g).postR, instPP ms (sigOf g).postP,
      instPRL ms (sigOf g).postPR with
    | some cs, some rs, some ps, some prs => ⟨cs, rs, ps, prs⟩
    | _, _, _, _ => ⟨[], [], [], []⟩) :: condE sigOf ms gs

/-- The guarantees under a selector, added. -/
def CSt.addCd (st : CSt) (l : List CdE) : CSt :=
  ⟨st.env, st.sc, st.rs, st.ad, st.sv, st.src, st.pf, st.pr, st.n, st.nr, st.nc, st.nt, st.cd ++ l, st.eqs⟩

/-- The word a signature names at return (`postV`) at the cell `c`, its `post` cell at the slots `ms`. -/
def wordAt (G : HSig) (ms : List CCell) (c : CCell) : Option CCell :=
  match G.postV.find? (fun p ↦ match nth G.post p.1 with
      | some cc => match instC ms cc with
        | some c' => c'.beq c
        | none => false
      | none => false) with
  | some p => instC ms p.2
  | none => none

/-- The word every arm names at return at the cell `c`. -/
def armsV (sigOf : String → HSig) (ms : List CCell) (gs : List String) (c : CCell) : Option CCell :=
  match gs with
  | [] => none
  | g :: gs' => match wordAt (sigOf g) ms c with
    | some m => bif gs'.all (fun g' ↦ match wordAt (sigOf g') ms c with
        | some m' => m'.beq m
        | none => false) then some m else none
    | none => none

/-- **A dispatch's words at return**: of its meet's cells (point serials from `n`), those every arm names
the same word at. -/
def meetVL (sigOf : String → HSig) (ms : List CCell) (gs : List String) : List CCell → ℕ → List (ℕ × CCell × CCell)
  | [], _ => []
  | c :: cs, n => match armsV sigOf ms gs c with
    | some m => (n, c, m) :: meetVL sigOf ms gs cs (n + 1)
    | none => meetVL sigOf ms gs cs (n + 1)

/-- **A dispatch** on `x`: every arm's preconditions but the arms a fact rules out (`armSkip`); the
returned words' monomials every arm kept gives, then what every arm kept guarantees pushed (cells, runs,
pointer facts, pointer runs), its returned pointers' cells (`vp`) and its blocks' runs (`ab`); and each arm's
guarantees kept under the selector (`condE`). -/
noncomputable def dispC (X : CX) (st : CSt) (x : V) (fs : List String) (args rets : List V) : Option CSt :=
  match monos st.env args, monoOf st.env x, getF X.C st.nc with
  | some ma, some mx, some ws => match reqArmsX X st ma args rets (vpHead ws).1 (abHead (vpHead ws).2).1 x mx 0 fs
      (abHead (vpHead ws).2).2 with
    | some ([], []) => some st.nextC
    | some ([], g :: gs) => (retDefs rets ((instRM ma (X.sigOf g).retM).filter
          (meetM (gs.map fun g' ↦ instRM ma (X.sigOf g').retM))) st.nextC).seq fun st1 ↦
        match monos st1.env rets with
        | some mr => match instArms X.sigOf (ma ++ mr) (g :: gs) with
          | some (p :: ps, r :: rs) => some ((pushRL (abPost mx (abHead (vpHead ws).2).1) (pushL (vpCells mr (vpHead ws).1)
              (pushPtrM (instArmsP X.sigOf (ma ++ mr) (g :: gs))
              (pushRL (r.filter (meetR rs)) (svPut (meetVL X.sigOf (ma ++ mr) (g :: gs) (p.filter (meetC ps)) st1.n)
                (pushL (p.filter (meetC ps)) st1)))))).addCd
                (bif Nat.blt fs.length capE then [⟨mx, condE X.sigOf (ma ++ mr) fs⟩] else []))
          | _ => none
        | none => none
    | _ => none
  | _, _, _ => none

/-- The own `retM` at a return: each returned word's monomial (of `mv`) is its cell at the
parameters' monomials `mp`. -/
def retMC (mp mv : List CCell) (l : List (ℕ × CCell)) : Bool :=
  l.all fun p ↦ match nth mv p.1, instC mp p.2 with
    | some m, some c => m.beq c
    | _, _ => false

/-- The own words at return: `post` cell `i`'s witness a load event (`ev n`) that stored `m`'s word. -/
noncomputable def retVC (st : CSt) (ms : List CCell) (post : List CCell) (ws : List Wit) (l : List (ℕ × CCell)) :
    Bool :=
  l.all fun p ↦ match nth ws p.1, nth post p.1 with
    | some (.ev n), some c => match getF st.sv n, instC ms c, instC ms p.2 with
      | some q, some c', some m' => q.1.beq c' && q.2.beq m'
      | _, _, _ => false
    | _, _ => false

/-- The own equations at return, at the slots `ms`: each one's sides one word (`eqV`). -/
def retEqC (E : List (CCell × CCell)) (ms : List CCell) (l : List (CCell × CCell)) : Bool :=
  l.all fun p ↦ match instC ms p.1, instC ms p.2 with
    | some a, some b => eqV E a b
    | _, _ => false

/-- The cells of the frame runs guaranteed at return, `(kp, i)` the cell `V.n kp · g^i`, at the
environment's monomials. -/
noncomputable def faCells (env : Trie CCell) (fas : List (ℕ × ℕ)) : List CCell :=
  fas.map fun p ↦ ((getF env p.1).getD (baseC p.1)).shift p.2

/-- The own guarantees at the parameters and the returned words, the returned words' monomials, and the
words at return. -/
noncomputable def retC1 (X : CX) (st : CSt) (vs : List V) : Bool :=
  match monos st.env X.params, monos st.env vs, getF X.T st.nt with
  | some mp, some mv, some ws => match reqP X st (mp ++ mv) X.sig.post ws with
    | some ws1 => match reqR X st (mp ++ mv) X.sig.postR ws1 with
      | some ws2 => match reqPP X st (mp ++ mv) X.sig.postP ws2 with
        | some ws3 => match reqPR X st (mp ++ mv) X.sig.postPR ws3 with
          | some [] => retMC mp mv X.sig.retM && retVC st (mp ++ mv) X.sig.post ws X.sig.postV &&
              retEqC st.eqs (mp ++ mv) X.sig.retEq
          | _ => false
        | none => false
      | none => false
    | none => false
  | _, _, _ => false

/-- **A return**: the frame run cells guaranteed at return pushed (`faCells`, write events from the next
point serial), then `retC1`. -/
noncomputable def retC (X : CX) (st0 : CSt) (vs : List V) : Bool :=
  (pushL (faCells st0.env X.fas) st0).seq fun st ↦ retC1 X st vs

/-- A read of the cell `c` into `d`, `d` listed (`HCert.hvs`), whose witness is a load event of that
very cell: `d`'s first monomial the word stored there (memory is written once). -/
noncomputable def hvDef (X : CX) (st : CSt) (c : CCell) (d : V) : Wit → CSt
  | .ev n => match vnum d with
    | some k => match getF X.hv k, getF st.sv n with
      | some _, some p => bif p.1.beq c then st.def k p.2 else st
      | _, _ => st
    | none => st
  | _ => st

/-- A load's write event of the cell `c`, with its word's monomial; `c` the cell `d` was loaded
from. -/
noncomputable def loadPush (st : CSt) (c : CCell) (d : V) : CSt :=
  (match monoOf st.env d with
    | some m => st.pushV c m
    | none => st.push c).seq fun st ↦ st.srcPut d c

/-- **The heap bits a `log2Ceil` reads**: the cells `m·g^(off + k)`, `n` of them from `k`, each with its
witness, keyed as a read of the hint's destination `dst` through `p` at `off + k`. -/
noncomputable def bitsOk (X : CX) (st : CSt) (m : CCell) (dst p : V) (off : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | k, n + 1 => (match readWitT X.R dst p (off + k) with
    | some w => ptOk X st (m.shift (off + k)) w
    | none => false) && bitsOk X st m dst p off (k + 1) n

/-- **A division**: the quotient `q = d / b` of a `mul d q b`, `q` listed (`HCert.divs`), `d`'s
monomial known, `b` a constant `g^k` with `k` at most `d`'s offset. -/
noncomputable def divOf (X : CX) (st : CSt) (d q b : V) : Option (ℕ × CCell) :=
  match vnum q with
  | some kq => match getF X.dv kq, vnum d with
    | some _, some kd => match getF st.env kd, monoOf st.env b with
      | some md, some mb => bif mb.bases.isEmpty && Nat.ble mb.off md.off then
          some (kq, ⟨md.bases, md.off - mb.off⟩) else none
      | _, _ => none
    | _, _ => none
  | none => none

/-- **An atom**: milestone 1's, a read's witness any of `ptOk`'s, a read through a load event of its
cell taking the word stored (`hvDef`), a `mul` dividing out a listed quotient (`divOf`). -/
noncomputable def atomC0 (X : CX) (st : CSt) : Atom → Option CSt
  | .load d p off => match monoOf st.env p with
    | some m => (m.shift off).seq fun c ↦ match readWitT X.R d p off with
      | some w => bif ptOk X st c w then (hvDef X st c d w).seq fun st1 ↦ some (loadPush st1 c d) else none
      | none => some (loadPush st c d)
    | none => none
  | .mul d a b => match divOf X st d a b, divOf X st d b a with
    | some p, _ => some (st.def p.1 p.2)
    | none, some p => some (st.def p.1 p.2)
    | none, none => (atomH X.toH st.toH (.mul d a b)).map st.ofH
  | .add d a b => match vnum d, monoOf st.env a, monoOf st.env b with
    | some k, some ma, some mb => some (st.addS k ma mb)
    | _, _, _ => some st
  | .hint (.log2Ceil (.heap p off len) nbits _ dst) => match monoOf st.env p with
    | some m => bif bitsOk X st m dst p off 0 (min nbits len) then some st else none
    | none => none
  | a => (atomH X.toH st.toH a).map st.ofH

/-- An equation `a = b` of two values, `a` listed (`HCert.eqs`): their monomials. -/
noncomputable def eqPair (X : CX) (st : CSt) (a b : V) : CSt :=
  match vnum a with
  | some k => match getF X.eqk k, monoOf st.env a, monoOf st.env b with
    | some _, some ma, some mb => st.addEq (ma, mb)
    | _, _, _ => st
  | none => st

/-- **An atom's equation kept**: a listed `mul d a b` whose `d` has a monomial already (`d = a·b`, e.g. a
quotient without a monomial), a listed `assertEq` or `copy`. -/
noncomputable def eqAt (X : CX) (st : CSt) : Atom → CSt
  | .mul d a b => match vnum d with
    | some k => match getF X.eqk k, getF st.env k, monoOf st.env a, monoOf st.env b with
      | some _, some md, some ma, some mb => st.addEq (ma.mul mb, md)
      | _, _, _, _ => st
    | none => st
  | .assertEq a b => eqPair X st a b
  | .copy d s => eqPair X st d s
  | _ => st

/-- **An atom**: its equation kept (`eqAt`), then `atomC0`. -/
noncomputable def atomC (X : CX) (st : CSt) (a : Atom) : Option CSt := (eqAt X st a).seq fun st ↦ atomC0 X st a

/-! ## Joins -/

/-- A block returning on every path: a `ret` at its top level. -/
def endsRet : List Stmt → Bool
  | [] => false
  | .ret _ :: _ => true
  | _ :: ss => endsRet ss

/-- A trie's entries at the keys `lo`, `lo + 1`, …, `n` keys. -/
noncomputable def rng {α : Type} (t : Trie α) (lo : ℕ) : ℕ → List (ℕ × α)
  | 0 => []
  | n + 1 => match getF t lo with
    | some a => (lo, a) :: rng t (lo + 1) n
    | none => rng t (lo + 1) n

/-- **The entries a join keeps**: of the blocks that can fall through (not returning, `false`), the
first one's entries that every other one has too (`beq`). -/
def joinE {α : Type} (beq : α → α → Bool) (ls : List (Bool × List (ℕ × α))) : List (ℕ × α) :=
  match ls.filter fun l ↦ !l.1 with
  | [] => []
  | l0 :: rest => l0.2.filter fun p ↦ rest.all fun l ↦ l.2.any fun q ↦ beq q.2 p.2

/-- Entries into a trie, by key. -/
noncomputable def insL {α : Type} : List (ℕ × α) → Trie α → Trie α
  | [], t => t
  | p :: l, t => (setF p.2 Exec.indexDepth t p.1).seq fun t ↦ insL l t

/-- **The state after a join**: `st`'s, with the cells, runs, pointer facts and pointer runs that every
block `b = (returns, start, end)` able to fall through added after its start, at the first such block's
serials; `s`'s serials. -/
noncomputable def joinSt (bs : List (Bool × CSt × CSt)) (st s : CSt) : CSt :=
  ⟨st.env, insL (joinE CCell.beq (bs.map fun b ↦ (b.1, rng b.2.2.sc b.2.1.n (b.2.2.n - b.2.1.n)))) st.sc,
    insL (joinE PRun.beq (bs.map fun b ↦ (b.1, rng b.2.2.rs b.2.1.nr (b.2.2.nr - b.2.1.nr)))) st.rs,
    st.ad, st.sv, st.src,
    insL (joinE pfBeq (bs.map fun b ↦ (b.1, rng b.2.2.pf b.2.1.n (b.2.2.n - b.2.1.n)))) st.pf,
    insL (joinE prBeq (bs.map fun b ↦ (b.1, rng b.2.2.pr b.2.1.nr (b.2.2.nr - b.2.1.nr)))) st.pr,
    s.n, s.nr, s.nc, s.nt, st.cd, st.eqs⟩

/-- The last block's end, or `st`. -/
def lastSt : List (Bool × CSt × CSt) → CSt → CSt
  | [], st => st
  | [b], _ => b.2.2
  | _ :: l, st => lastSt l st

mutual
/-- **The pass over a block**: the state at its end, or at its `ret`. -/
noncomputable def chkC (X : CX) : List Stmt → CSt → Option CSt
  | [], st => some st
  | .atom a :: ss, st => match atomC X st a with
    | some st' => st'.seq fun st' ↦ chkC X ss st'
    | none => none
  | .ite c z n :: ss, st => match chkC (X.ext (czero c)) z st with
    | some s1 => match chkC (X.ext (cnz c)) n (st.cnt s1) with
      | some s2 => (joinSt [(endsRet z, st, s1), (endsRet n, st.cnt s1, s2)] st s2).seq fun st' ↦ chkC X ss st'
      | none => none
    | none => none
  | .match_ x arms :: ss, st => match chkArmsC X x 0 arms st with
    | some bs => (joinSt bs st (lastSt bs st)).seq fun st' ↦ chkC X ss st'
    | none => none
  | .call g args rets :: ss, st => match callC X st g args rets with
    | some st' => st'.seq fun st' ↦ chkC X ss st'
    | none => none
  | .callIf c g args :: ss, st => match callIfC X st c g args with
    | some st' => st'.seq fun st' ↦ chkC X ss st'
    | none => none
  | .dispatch x fs args rets :: ss, st => match dispC X st x fs args rets with
    | some st' => st'.seq fun st' ↦ chkC X ss st'
    | none => none
  | .ret vs :: _, st => bif retC X st vs then some st.nextT else none

/-- The pass over each arm of a `match` on `x`, arm `j` under `x = g^j`, from the state before the `match`
with the serials running on: each arm's `(returns, start, end)`. -/
noncomputable def chkArmsC (X : CX) (x : V) : ℕ → List (List Stmt) → CSt → Option (List (Bool × CSt × CSt))
  | _, [], _ => some []
  | j, a :: as, st => match chkC (X.ext (carm x j)) a st with
    | some s1 => match chkArmsC X x (j + 1) as (st.cnt s1) with
      | some l => some ((endsRet a, st, s1) :: l)
      | none => none
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

/-- The tail's `postP` facts, at the parameters `mp`, or at the exit's slots `mx`. -/
noncomputable def tailPP (X : CX) (st : CSt) (mp mx : List CCell) (ex : Bool) :
    List (CCell × List ℕ) → List Wit → Option (List Wit)
  | [], ws => some ws
  | p :: ps, ws => match (match instC mp p.1 with
      | some c => ptrOk X st c p.2 ws
      | none => none) with
    | some ws' => tailPP X st mp mx ex ps ws'
    | none => bif ex && noSlot0 p.1 then
        (match instC mx p.1 with
        | some c => match ptrOk X st c p.2 ws with
          | some ws' => tailPP X st mp mx ex ps ws'
          | none => none
        | none => none) else none

/-- The tail's `postPR` runs, at the parameters `mp`, at the exit's slots `mx`, or accumulated (the
counter's cell's pointer fact). -/
noncomputable def tailPR (X : CX) (st : CSt) (mp mx : List CCell) (ex : Bool) (ei : CIdx) :
    List (CRun × List ℕ) → List Wit → Option (List Wit)
  | [], ws => some ws
  | p :: ps, ws => match (match instR mp p.1 with
      | some q => ptrROk X st q p.2 ws
      | none => none) with
    | some ws' => tailPR X st mp mx ex ei ps ws'
    | none => match (bif ex && noSlot0R p.1 then
        (match instR mx p.1 with
        | some q => ptrROk X st q p.2 ws
        | none => none) else none) with
      | some ws' => tailPR X st mp mx ex ei ps ws'
      | none => bif CIdx.beq p.1.lo (.val 0) && CIdx.beq p.1.hi ei && noSlot0 p.1.base then
          (match instC mp p.1.base, nth mp 0 with
          | some b, some m0 => match ptrOk X st (b.mul (m0.pow p.1.stride)) p.2 ws with
            | some ws' => tailPR X st mp mx ex ei ps ws'
            | none => none
          | _, _ => none) else none

/-- **A loop's `ret []` after its tail call** `callIf c self (i' :: _)`, the loop's end `ei`. -/
noncomputable def tailC (X : CX) (st : CSt) (args : List V) (ei : CIdx) : Bool :=
  match args, monos st.env X.params, getF X.T st.nt with
  | i' :: _, some mp, some ws => match monoOf st.env i' with
    | some mi => match tailP X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) X.sig.post ws with
      | some ws1 => match tailR X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) ei X.sig.postR ws1 with
        | some ws2 => match tailPP X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) X.sig.postP ws2 with
          | some ws3 => match tailPR X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) ei X.sig.postPR ws3 with
            | some [] => true
            | _ => false
          | none => false
        | none => false
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

/-- The own ghosts' monomials: the values `V.n (GB + j)`. -/
def ghostMs (n : ℕ) : List CCell := (List.range n).map fun j ↦ baseC (GB + j)

/-- The words at cells: fewer than `GB - DB`, their cells over no word at a cell. -/
def dersOk (ders : List CCell) : Bool :=
  Nat.blt ders.length (GB - DB) && ders.all fun c ↦ c.bases.all fun b ↦ Nat.blt b.1 DB || Nat.ble GB b.1

/-- The entry state: each parameter its own base; the own `preP` at the parameters and ghosts, point
serials from `0`; the own `preR`, then `prePR`, at the parameters and ghosts, run serials from `0`. The
words at cells checked (`dersOk`). -/
noncomputable def initC (X : CX) : Option CSt :=
  bif !dersOk X.ders then none else
  (paramEnv X.params.length).seq fun env ↦ match monos env X.params with
  | some mp => match instPP (mp ++ ghostMs X.sig.ghosts) X.sig.preP, instAllR (mp ++ ghostMs X.sig.ghosts) X.sig.preR,
      instPRL (mp ++ ghostMs X.sig.ghosts) X.sig.prePR with
    | some pps, some rs, some prs =>
      some (pushPRL prs (pushRL rs (pushPL pps ⟨env, .nil, .nil, .nil, .nil, .nil, .nil, .nil, 0, 0, 0, 0, [], []⟩)))
    | _, _, _ => none
  | none => none

/-- The keys of a list, as a trie. -/
noncomputable def keysT : List ℕ → Trie Unit → Trie Unit
  | [], t => t
  | k :: l, t => (setF () Exec.indexDepth t k).seq fun t ↦ keysT l t

/-- No value the function names is a ghost's or a word at a cell (its index below `DB`): the function's run does
not depend on them. -/
def noGhost (f : Fn) : Bool := (Stmt.usesList f.body ++ Stmt.tmpsList f.body ++ f.params).all fun v ↦ Nat.blt v.idx DB

/-- **The top-level atoms before a block's first `ret`**: on every path through the block that returns. -/
def topAtoms : List Stmt → List Atom
  | [] => []
  | s :: ss => bif Memory.Stmt.noRet s then
      (match s with
        | .atom a => a :: topAtoms ss
        | _ => topAtoms ss) else []

/-- The value numbers the atoms define (`atomDst`), as a trie. -/
noncomputable def dstKeys (as : List Atom) : Trie Unit := keysT ((as.flatMap atomDst).filterMap vnum) .nil

/-- Cell `i` of a `frameAddr (V.n kp) run` among the atoms, `run[i]` among the values `D` (by number). -/
noncomputable def faAt (D : Trie Unit) (kp i : ℕ) : Atom → Bool
  | .frameAddr p run => (match vnum p with
      | some k => Nat.beq k kp
      | none => false) && (match run[i]? with
      | some v => match vnum v with
        | some k => (getF D k).isSome
        | none => false
      | none => false)
  | _ => false

/-- **The frame run cells a certificate guarantees at return** (`HCert.fas`): each `(kp, i)` cell `i` of a
`frameAddr (V.n kp) run` among the atoms `as`, `run[i]` defined by one of them (`D`, `dstKeys as`). -/
noncomputable def faOk (as : List Atom) (D : Trie Unit) : List (ℕ × ℕ) → Bool
  | [] => true
  | (kp, i) :: l => as.any (faAt D kp i) && faOk as D l

/-- **The heap check with calls and loops.** The parameters `V.n i`, the preconditions over them, no
ghost value named, the entry state, then the pass over the body, or a loop helper's
(`term = [(.val 0, end)]`, no returned word). -/
noncomputable def heapOkC (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) : Bool :=
  paramsN f.params 0 && preOver f.params.length H.sig.pre &&
    H.sig.term.all (fun p ↦ idxOver f.params.length p.1 && idxOver f.params.length p.2) && noGhost f &&
    faOk (topAtoms f.body) (dstKeys (topAtoms f.body)) H.fas &&
    H.readT.seq fun R ↦ (trieFrom H.sig.pre 0 .nil).seq fun P ↦ (trieFrom H.calls 0 .nil).seq fun C ↦
      (trieFrom H.rets 0 .nil).seq fun T ↦ (trieFrom H.res 0 .nil).seq fun RS ↦ (keysT H.divs .nil).seq fun DV ↦ (keysT H.hvs .nil).seq fun HV ↦ (keysT H.eqs .nil).seq fun EQ ↦
        match initC ⟨pows, R, P, C, T, RS, DV, HV, H.gargs, sigOf, H.sig, f.params, [], EQ, H.fas, H.ders⟩ with
        | some st0 => match H.sig.term with
          | [] => (chkC ⟨pows, R, P, C, T, RS, DV, HV, H.gargs, sigOf, H.sig, f.params, [], EQ, H.fas, H.ders⟩ f.body st0).isSome
          | [(.val 0, ei)] => H.sig.retM.isEmpty && H.sig.postV.isEmpty && H.sig.retEq.isEmpty && loopC ⟨pows, R, P, C, T, RS, DV, HV, H.gargs, sigOf, H.sig, f.params, [], EQ, H.fas, H.ders⟩ f ei st0
          | _ => false
        | none => false

end

end LeanVM.Guest.CoreMode
