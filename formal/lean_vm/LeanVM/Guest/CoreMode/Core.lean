/-
  LeanVM.Guest.CoreMode.Core

  The core route's frame predicate (`CoreAt`) and its frame interface (`frameSpec_core`), for a
  straight-line function with no call and no loop: the frame walk's facts, the entry
  cells written, and every heap cell the core path has written by the pairing's position written in
  the executor's memory.
-/

module

public import LeanVM.Guest.CoreMode.FrameSound
public import LeanVM.Guest.CoreMode.PairHeap
public import LeanVM.Guest.CoreMode.Post
public import LeanVM.Guest.CoreMode.Spec
public import LeanVM.Guest.CoreMode.HintW
public import LeanVM.Guest.Bridge.JumpCellsSound
public import LeanVM.Guest.Bridge.AlignJump
public import LeanVM.Guest.Mode.HintsCtx

/-!
# The core route's frame interface

`CFun`: what the core route knows of one function: its frame walk (`frame`, with the oracle `O` of
its reads' `DEREF`s and the offsets `S` of its stores'), its alignment's context `X`, its heap
certificate `H`, its core function `fn`, its advice entry `d`, the powers' table and the heap cells
it promises its callers (`post`, with their witnesses).

`HonF img Cf fp σ`: `σ` is the valuation of an honest instance of `Cf.fn` in frame `fp` of the
reference image `img`: its path returns with its events holding, each `load`'s pointer at its cell
(`X.locAt`), each parameter at its cell `2 + k`, each returned value at its cell.

`CoreAt img Cf code i s`: frame `s.fp` at offset `i`: the frame walk's state there holds (`AtF`), the
entry cells are written, and for every honest valuation of the frame, its path splits at the
pairing's position at `i` (`pairAt`), every cell written by the events before it (`Written`) being
written in `s.mem` (`WrK`).

`frameSpec_core`: from the kernel's checks (`CoreOk`: `heapOk`, `postOk`, `pairOk`, `frameOk`, the
signature's translation `sigOk` and the shape `shapeOk`), on the reference `img`, at states `Y` on
its run where each frame of the function has an honest valuation (`CoreHon`), `CoreAt` meets
`FrameSpec`.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (AlignCtx Zip ZOk fwdJ flowAtom isaFlowHint stmtsOf zok_stmts)
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed OnRef)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj opOfOff RefOk HintIn Holds entryAbs
  FrameSpec Out HintsAt ResAt RetAll RetHolds HW RW MonoVal BsVal BaseVal IdxVal stOf CodeOk)

@[expose] public section

variable {κ : ℕ}

/-! ## Data -/

/-- **What the core route knows of a function.** -/
structure CFun where
  frame : FFun
  X : AlignCtx
  H : HCert
  fn : Fn
  d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)
  pows : Exec.PowTree
  post : List (CCell × Wit)

/-- The pairing's context. -/
noncomputable def CFun.P (Cf : CFun) : PairCtx := PairCtx.ofH Cf.X Cf.H Cf.frame.O Cf.frame.S

/-- The address `y` is a cell written in `m`. -/
def WrK (m : Mem) (y : K) : Prop := ∃ x, y = g ^ x ∧ x < maxCells ∧ m.written x = true

theorem WrK.mono {m m' : Mem} (hle : m ≤ m') {y : K} (h : WrK m y) : WrK m' y :=
  let ⟨x, h1, h2, h3⟩ := h
  ⟨x, h1, h2, written_mono hle h3⟩

/-- The pointer an atom dereferences: a `load`'s, a heap hint destination's. -/
def ptrOf : Atom → Option V
  | .load _ p _ => some p
  | .hint h => (hintHeap h).map (·.1)
  | _ => none

/-- **What a frame's jumps read** in the reference image, at the cells the alignment's context `X`
names: a constant `0` or a nonzero one, the frame pointer, a pc, a branch's condition on the path, a
`match`'s target on the arm its selector picks. -/
structure JumpF (img : MemoryImage κ) (X : AlignCtx) (body : List Stmt) (fp : ℕ) (σ : Val) : Prop where
  zero : ∀ o, X.zeroAt o = true → Rd img fp o = some 0
  nz : ∀ o, X.nzAt o = true → ∃ w, Rd img fp o = some w ∧ w ≠ 0
  self : ∀ o, X.selfAt o = true → Rd img fp o = some (ofK (g ^ fp))
  pcw : ∀ o t, X.pcAt o = some t → Rd img fp o = some (ofK (g ^ t))
  cond : ∀ es vs, walk σ body = .ret es vs → ∀ c, Ev.inK c ∈ es → Rd img fp (X.locAt c.idx) = some (σ c)
  arm : ∀ x arms, Stmt.match_ x arms ∈ stmtsOf body → ∀ od a, Check.getF X.arms od = some a → a.1 = x.idx →
    ∀ k t, σ x = ofK (g ^ k) → Check.getF X.jt (a.2 + k) = some t → Rd img fp od = some (ofK (g ^ t))
  sel : ∀ es vs, walk σ body = .ret es vs → ∀ x arms, Stmt.match_ x arms ∈ stmtsOf body →
    Rd img fp (X.locAt x.idx) = some (σ x)

/-- **An honest valuation** of `Cf.fn` in frame `fp` of the reference image. -/
structure HonF (img : MemoryImage κ) (Cf : CFun) (fp : ℕ) (σ : Val) : Prop where
  path : ∃ es vs rd, walk σ Cf.fn.body = .ret es vs ∧ ∀ e ∈ es, e.Holds rd σ
  ptr : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ a p, Ev.atom a ∈ es → ptrOf a = some p →
    Rd img fp (Cf.X.locAt p.idx) = some (σ p)
  par : ∀ k < Cf.fn.params.length, Rd img fp (2 + k) = some (σ (V.n k))
  rets : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ v ∈ vs, Rd img fp (Cf.X.locAt v.idx) = some (σ v)
  jc : JumpF img Cf.X Cf.fn.body fp σ
  holds : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ e ∈ es, e.Holds img.read σ

/-- **The core route's frame predicate.** -/
def CoreAt (img : MemoryImage κ) (Cf : CFun) (code : List OffsetInstruction) (i : ℕ) (s : St) : Prop :=
  AtF img Cf.frame code i s ∧ (∀ o ∈ Cf.frame.sig.entry, s.mem.written (s.fp + o) = true) ∧
    ∀ σ, HonF img Cf s.fp σ → ∃ pos pre es vs, pairAt Cf.P Cf.fn.body code Cf.d i = some pos ∧
      walk σ Cf.fn.body = .ret (pre ++ es) vs ∧ walk σ pos = .ret es vs ∧ ∀ y, Written Cf.H σ pre y → WrK s.mem y

/-- **Each frame of the function has an honest valuation** at the states `Y`. -/
def CoreHon (img : MemoryImage κ) (Y : St → Prop) (K : Mode.Cert) (Cf : CFun) : Prop :=
  ∀ s i, Y s → i < K.code.length → s.pc = K.F.entry + i → ∃ σ, HonF img Cf s.fp σ

theorem atF_mono {img : MemoryImage κ} {Fn : FFun} {code : List OffsetInstruction} {i : ℕ} {s s' : St}
    (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) (h : AtF img Fn code i s) : AtF img Fn code i s' := by
  obtain ⟨cur, pend, h0, hh⟩ := h
  refine ⟨cur, pend, h0, hh.imp (fun ⟨A, hA, hH⟩ ↦ ⟨A, hA, hH.mono hle hfp⟩) fun ⟨g, hg, hj, hH⟩ ↦
    ⟨g, hg, hj, hH.mono hle hfp⟩⟩

theorem CoreAt.mono {img : MemoryImage κ} {Cf : CFun} {code : List OffsetInstruction} {i : ℕ} {s s' : St}
    (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) (h : CoreAt img Cf code i s) : CoreAt img Cf code i s' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨atF_mono hle hfp h1, fun o ho ↦ hfp ▸ written_mono hle (h2 o ho), fun σ hσ ↦ ?_⟩
  obtain ⟨pos, pre, es, vs, h4, h5, h6, h7⟩ := h3 σ (hfp ▸ hσ)
  exact ⟨pos, pre, es, vs, h4, h5, h6, fun y hy ↦ (h7 y hy).mono hle⟩

/-! ## The signature, translated -/

/-- A frame base `[o]^e` as a parameter's power `(o - 2, e)`. -/
def baseOfMono : Mode.Base × ℕ → Option (ℕ × ℕ)
  | (.fr o, e) => if 2 ≤ o then some (o - 2, e) else none
  | _ => none

/-- **A signature's product as a cell**, its bases translated by `f` into powers of core values: no
frame address. -/
def monoF (f : Mode.Base × ℕ → Option (ℕ × ℕ)) (m : Mode.Mono) : Option CCell :=
  if m.fp = 0 then (m.bs.mapM f).map fun bs ↦ ⟨bs, m.k⟩ else none

/-- **A signature's product as a cell** over parameter numbers: no frame address, bases frame cells
`2 + k`. -/
def monoC (m : Mode.Mono) : Option CCell := monoF baseOfMono m

/-- A product's bases are entry cells `2 + k` of parameters. -/
def monoOk (G : Mode.Sig) (np : ℕ) (m : Mode.Mono) : Bool :=
  m.bs.all fun b ↦ match b.1 with
    | .fr o => G.entry.contains o && decide (2 ≤ o) && decide (o - 2 < np) && decide (o < 2 ^ 28)
    | .hp _ _ => false

/-- The value a `load` at the body's top level reads at parameter `k`'s word past `d`, before any `ret`
there: the first. -/
def hpVal : List Stmt → ℕ → ℕ → Option ℕ
  | [], _, _ => none
  | .atom (.load v p off) :: ss, k, d => match vnum p, vnum v with
    | some k', some n => bif Nat.beq k' k && Nat.beq off d then some n else hpVal ss k d
    | _, _ => hpVal ss k d
  | .ret _ :: _, _, _ => none
  | _ :: ss, k, d => hpVal ss k d

/-- The values the body's first top-level `ret` returns. -/
def retVals : List Stmt → Option (List V)
  | [] => none
  | .ret vs :: _ => some vs
  | _ :: ss => retVals ss

/-- The number of the value returned at frame cell `o`. -/
noncomputable def retAtCell (X : AlignCtx) (body : List Stmt) (o : ℕ) : Option ℕ :=
  (retVals body).bind fun vs ↦ (vs.find? fun v ↦ Nat.beq (X.locAt v.idx) o).bind vnum

/-- **A promised product's base as a power of a core value**: a parameter's frame cell `2 + k`, a
return cell's returned value, the word a top-level `load` reads past a parameter's. -/
noncomputable def baseOfP (X : AlignCtx) (body : List Stmt) (np : ℕ) : Mode.Base × ℕ → Option (ℕ × ℕ)
  | (.fr o, e) => if 2 ≤ o ∧ o - 2 < np then some (o - 2, e) else (retAtCell X body o).map fun n ↦ (n, e)
  | (.hp q d, e) => if 2 ≤ q ∧ q - 2 < np then (hpVal body (q - 2) d).map fun n ↦ (n, e) else none

/-- A promised product's bases: entry cells of parameters, return cells, words past parameters'. -/
def monoOkP (G : Mode.Sig) (np : ℕ) (m : Mode.Mono) : Bool :=
  m.bs.all fun b ↦ match b.1 with
    | .fr o => decide (o < 2 ^ 28) && ((G.entry.contains o && decide (2 ≤ o) && decide (o - 2 < np)) ||
        G.ret.contains o)
    | .hp q _ => G.entry.contains q && decide (2 ≤ q) && decide (q - 2 < np) && decide (q < 2 ^ 28)

/-- A cell among cells. -/
def cellIn (c : CCell) (l : List CCell) : Bool := l.any fun c' ↦ c'.beq c

/-- A run's points, its bounds constants. -/
def runPts (c : CCell) (r : Mode.Rng) : Option (List CCell) :=
  match r.lo, r.hi with
  | .num a, .num b => some ((List.range (b - a)).map fun j ↦ ⟨c.bases, c.off + (r.S * (a + j) + r.d)⟩)
  | _, _ => none

/-- A promised cell: a product of the signature, a promised cell's. -/
noncomputable def postIn (X : AlignCtx) (body : List Stmt) (G : Mode.Sig) (np : ℕ) (posts : List CCell)
    (m : Mode.Mono) : Bool :=
  monoOkP G np m && match monoF (baseOfP X body np) m with
    | some c => cellIn c posts
    | none => false

/-- A promised run: each of its points promised. -/
noncomputable def postRIn (X : AlignCtx) (body : List Stmt) (G : Mode.Sig) (np : ℕ) (posts : List CCell)
    (r : Mode.Rng) : Bool :=
  monoOkP G np r.q && match monoF (baseOfP X body np) r.q with
    | some c => match runPts c r with
      | some l => l.all (cellIn · posts)
      | none => false
    | none => false

/-- A heap precondition: a product of the signature's preconditions, or a point of one of its
preconditions' runs. -/
def preIn (G : Mode.Sig) (np : ℕ) (c : CCell) : Bool :=
  G.pre.any (fun m ↦ monoOk G np m && match monoC m with
    | some c' => c'.beq c
    | none => false) ||
  G.preR.any fun r ↦ monoOk G np r.q && match monoC r.q with
    | some c' => match runPts c' r with
      | some l => cellIn c l
      | none => false
    | none => false

/-- **The signature callers know, translated**: no self frame pointer, termination fact, loop run,
pointer run or order (returned products: `retVOk`); each heap precondition one of the signature's
(`preIn`); each heap cell and run it promises (`monoOkP`, `baseOfP`: over parameters, returned values and
words past parameters' a top-level `load` reads) among the promised cells `post`. -/
noncomputable def sigOk (X : AlignCtx) (body : List Stmt) (G : Mode.Sig) (H : HCert) (post : List (CCell × Wit))
    (np : ℕ) : Bool :=
  G.self.isNone && G.term.isEmpty && G.postL.isEmpty && G.postP.isEmpty && G.postLP.isEmpty &&
    G.postT.isEmpty && G.postC.isEmpty && H.sig.pre.all (preIn G np) &&
    G.post.all (postIn X body G np (post.map (·.1))) && G.postR.all (postRIn X body G np (post.map (·.1)))

/-- A returned value at the frame cell `o` whose word is the cell `c`'s. -/
noncomputable def retAt (X : AlignCtx) (env : Exec.Trie CCell) (vs : List V) (o : ℕ) (c : CCell) : Bool :=
  vs.any fun v ↦ Nat.beq (X.locAt v.idx) o && match monoOf env v with
    | some c' => c'.beq c
    | none => false

/-- The heap check's pass to the `ret`, where each returned product of the signature (`retV`) is a
return cell holding a returned value whose monomial is the product's. -/
noncomputable def retVGo (X : AlignCtx) (G : Mode.Sig) (np : ℕ) (hx : HX) : List Stmt → HSt → Bool
  | .atom a :: ss, st => match atomH hx st a with
    | some st' => st'.seq fun st' ↦ retVGo X G np hx ss st'
    | none => false
  | .ret vs :: _, st => G.retV.all fun p ↦ decide (p.1 < 2 ^ 28) && G.ret.contains p.1 && monoOk G np p.2 &&
      match monoC p.2 with
      | some c => retAt X st.env vs p.1 c
      | none => false
  | _, _ => false

/-- **The returned products' check** (`retV`): none, or each a returned value's monomial. -/
noncomputable def retVOk (Cf : CFun) (G : Mode.Sig) : Bool :=
  G.retV.isEmpty || Cf.H.readT.seq fun R ↦ (trieFrom Cf.H.sig.pre 0 .nil).seq fun P ↦
    retVGo Cf.X G Cf.fn.params.length ⟨Cf.pows, R, P⟩ Cf.fn.body ⟨.nil, .nil, 0⟩

/-! ## The shape -/

/-- A straight-line body: atoms and returns. -/
def straight (body : List Stmt) : Bool :=
  body.all fun s ↦ match s with
    | .atom _ => true
    | .ret _ => true
    | _ => false

/-- A statement the core route takes: an atom, a branch, a `match` or a return. -/
def ctrlOk : Stmt → Bool
  | .atom _ | .ite .. | .match_ .. | .ret _ => true
  | _ => false

/-- A top-level statement: a return, or one with no `ret` in it. -/
def topOk : Stmt → Bool
  | .ret _ => true
  | s => Core.Stmt.noRet s

/-- **A body the core route takes**: its statements, nested ones included, atoms, branches, `match`es
and returns, no branch or arm returning. -/
def bodyC (body : List Stmt) : Bool :=
  (stmtsOf body).all ctrlOk && body.all topOk

/-- The `match`es of a body, nested ones included: selector number, number of arms. -/
def matchLens (body : List Stmt) : List (ℕ × ℕ) :=
  (stmtsOf body).filterMap fun s ↦ match s with
    | .match_ x arms => some (x.idx, arms.length)
    | _ => none

/-- The slots of table `a` that every `match` of the selector it reads has, at offsets of `ts` past
the entry `e`. -/
noncomputable def armsCover (X : AlignCtx) (e : ℕ) (ml : List (ℕ × ℕ)) (a : ℕ × ℕ) (ts : List ℕ) : Bool :=
  ml.all fun p ↦ !Nat.beq p.1 a.1 || (List.range p.2).all fun j ↦ match Check.getF X.jt (a.2 + j) with
    | some t => decide (e ≤ t) && decide (t < 2 ^ 30) && ts.contains (t - e)
    | none => false

/-- From offset `i`: each `JUMP` the frame walk reads a table for (`tgt`) is a table jump through a
target cell the alignment's context gives a table (`arms`), no pc and not `0`, the walk's table the
offsets of the slots of every `match` on its selector, no callee's. -/
noncomputable def tgtGo (Cf : CFun) (ml : List (ℕ × ℕ)) : ℕ → List OffsetInstruction → Bool
  | _, [] => true
  | i, ins :: code => (match Cf.frame.tgt.get i with
      | none => true
      | some k => match ins with
        | .jump _ od _ => !Nat.beq od 0 && (Cf.X.pcAt od).isNone && (Cf.frame.calls.get k).isNone &&
            match Check.getF Cf.X.arms od, Cf.frame.arms.get k with
            | some a, some ts => armsCover Cf.X Cf.frame.entry ml a ts
            | _, _ => false
        | _ => true) && tgtGo Cf ml (i + 1) code

/-- **The frame walk's tables are the `match`es' arms.** -/
noncomputable def tgtOk (Cf : CFun) (code : List OffsetInstruction) : Bool :=
  Exec.listSeq (matchLens Cf.fn.body) fun ml ↦ tgtGo Cf ml 0 code

/-- From the instructions `code`: each `DEREF` reading the jump table (`jtd`) is followed by its table
jump, through its word cell, on no constant `0` cell and no pc, and each slot of its table that a
`match` on its selector has lies in the environment's jump table. -/
noncomputable def jtdGo (Cf : CFun) (E : Mode.Env) (ml : List (ℕ × ℕ)) : List OffsetInstruction → Bool
  | [] => true
  | ins :: code => (match ins with
      | .deref o1 o2 o3 .cell => !jtd Cf.X o1 o2 o3 || match code with
        | .jump oc od _ :: _ => Nat.beq od o3 && !Cf.X.zeroAt oc && (Cf.X.pcAt o3).isNone && !Nat.beq o3 0 &&
            match Check.getF Cf.X.arms o3 with
            | some a => ml.all fun p ↦ !Nat.beq p.1 a.1 || (List.range p.2).all fun j ↦
                decide (E.jtLo ≤ a.2 + j) && decide (a.2 + j < E.jtHi) && (E.jt.get (a.2 + j)).isSome
            | none => false
        | _ => false
      | _ => true) && jtdGo Cf E ml code

/-- **The jump table's reads**: `jtdGo` over the code. -/
noncomputable def jtdOk (Cf : CFun) (E : Mode.Env) (code : List OffsetInstruction) : Bool :=
  Exec.listSeq (matchLens Cf.fn.body) fun ml ↦ jtdGo Cf E ml code

/-- An empty trie. -/
def trieNil {α : Type} : Exec.Trie α → Bool
  | .nil => true
  | _ => false

/-- **The shape the core route takes**: a body of atoms, branches, `match`es and returns (`bodyC`), not
`main`, no frame cell `1` its frame pointer's, the walk's tables the `match`es' arms, no call, no
residual, small entry cells. -/
noncomputable def shapeOk (Cf : CFun) (code : List OffsetInstruction) : Bool :=
  bodyC Cf.fn.body && !Cf.X.main && !Cf.X.selfAt 1 && tgtOk Cf code && trieNil Cf.frame.sigs &&
    !Cf.frame.F.fpOne && trieNil Cf.frame.nzr && Cf.frame.sig.entry.all (fun o ↦ decide (o + 1 < 2 ^ Exec.envDepth)) &&
    decide (Cf.frame.entry + Cf.frame.len ≤ 2 ^ 30) && Mode.pcsIncr Cf.frame.hints

/-- **The kernel's checks of a function on the core route**, and its ties to its mode certificate
`K`: the code, entry and signature, the advice's hints at its pcs, its fetches, its operands small,
the powers' tables. -/
structure CoreOk (K : Mode.Cert) (Cf : CFun) : Prop where
  heap : heapOk Cf.pows (fun _ ↦ .empty) Cf.fn Cf.H = true
  post : postOk Cf.pows Cf.H Cf.post Cf.fn.body = true
  pair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body K.code Cf.d = true
  frame : envOk Cf.frame = true ∧ armsOk Cf.frame = true ∧ FrameAcc Cf.frame K.code
  sig : sigOk Cf.X Cf.fn.body K.F.sig Cf.H Cf.post Cf.fn.params.length = true
  retv : retVOk Cf K.F.sig = true
  shape : shapeOk Cf K.code = true
  jtd : jtdOk Cf K.E K.code = true
  fsig : Cf.frame.sig = K.F.sig
  fentry : Cf.frame.entry = K.F.entry
  xentry : Cf.X.entry = K.F.entry
  dhints : Cf.d.2.2 = Cf.frame.hints
  hints : ∀ i < K.code.length, Mode.hintsAt Data.adviceHints (K.F.entry + i) =
    Mode.hintsAt Cf.frame.hints (K.F.entry + i)
  fetch : Exec.Fetches guestProgram K.F.entry K.code
  small : ∀ i (hi : i < K.code.length), SmallOps K.code[i]
  pows : Cf.pows.Ok
  fpows : Cf.frame.F.pows.Ok

end

end LeanVM.Guest.CoreMode
