/-
  LeanVM.Guest.CoreMode.Core

  The core route's frame predicate (`CoreAt`) and its frame interface (`frameSpec_core`), for a
  function of atoms, calls and one return: the frame walk's facts, the entry cells written, and every
  heap cell the core path has written by the pairing's position written in the executor's memory.
-/

module

public import LeanVM.Guest.CoreMode.FrameSound
public import LeanVM.Guest.CoreMode.PairHeap
public import LeanVM.Guest.CoreMode.Post
public import LeanVM.Guest.CoreMode.Spec
public import LeanVM.Guest.CoreMode.HintW
public import LeanVM.Guest.CoreMode.PairC
public import LeanVM.Guest.Mode.InvDefs
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
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed OnRef Agree)
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
  /-- The callees' heap signatures, by name: their mode signatures', translated. -/
  cs : List (String × HSig)

/-- **The heap signatures the heap check reads**: its own at its own name, its callees' (`cs`). -/
def CFun.sigOf (Cf : CFun) (f : String) : HSig :=
  bif f == Cf.fn.name then Cf.H.sig else (Cf.cs.lookup f).getD {}

/-- The heap cells the function promises, over slots (parameters, then returned words). -/
def CFun.posts (Cf : CFun) : List CCell := Cf.post.map (·.1) ++ Cf.H.sig.post

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
  /-- Its returned values at the cells after its parameters. -/
  retc : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ k (hk : k < vs.length),
    Rd img fp (2 + Cf.fn.params.length + k) = some (σ vs[k])
  /-- A call's callee frame, at its site's cell: its header, its arguments and its returns. -/
  kid : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ (i : ℕ) (c : Call) q (s : B2C.Site), (calls es)[i]? = some c →
    c.taken = true → Cf.X.siteAt q c.args c.rets = some s → ∃ kfp, Rd img fp q = some (ofK (g ^ kfp)) ∧
      Rd img kfp 0 = some (ofK (g ^ s.r)) ∧ Rd img kfp 1 = some (ofK (g ^ fp)) ∧
      (∀ k (hk : k < c.args.length), Rd img kfp (2 + k) = some (σ c.args[k])) ∧
      ∀ k (hk : k < c.rets.length), Rd img kfp (2 + c.args.length + k) = some (σ c.rets[k])
  /-- What its jumps read. -/
  jc : JumpF img Cf.X Cf.fn.body fp σ

/-- **The core route's frame predicate, in a memory**: frame `fp` at offset `i` in memory `m`: the
frame walk's state there holds (`AtF`), the entry cells are written, and for every honest valuation
of the frame, its path splits at the pairing's position at `i` (`pairAt`), every cell written by the
events before it (`WrittenC`) being written in `m` (`WrK`). -/
def CoreIn (img : MemoryImage κ) (Cf : CFun) (code : List OffsetInstruction) (i : ℕ) (m : Mem) (fp : ℕ) : Prop :=
  AtF img Cf.frame code i (Mode.stOf m fp) ∧ (∀ o ∈ Cf.frame.sig.entry, m.written (fp + o) = true) ∧
    ∀ σ, HonF img Cf fp σ → ∃ pos pre es vs rd, pairAt Cf.P Cf.fn.body code Cf.d i = some pos ∧
      walk σ Cf.fn.body = .ret (pre ++ es) vs ∧ walk σ pos = .ret es vs ∧ (∀ e ∈ pre ++ es, e.Holds rd σ) ∧
      ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre y → WrK m y

/-- **The core route's frame predicate**: `CoreIn` in every memory past the state's agreeing with the
reference (so a caller resumes from what its callee guarantees, in any memory past the call). -/
def CoreAt (img : MemoryImage κ) (Cf : CFun) (code : List OffsetInstruction) (i : ℕ) (s : St) : Prop :=
  ∀ m, s.mem ≤ m → Agree m (refMem img) → CoreIn img Cf code i m s.fp

/-- **Each frame of the function has an honest valuation** at the states `Y`. -/
def CoreHon (img : MemoryImage κ) (Y : St → Prop) (K : Mode.Cert) (Cf : CFun) : Prop :=
  ∀ s i, Y s → i < K.code.length → s.pc = K.F.entry + i → ∃ σ, HonF img Cf s.fp σ

theorem atF_mono {img : MemoryImage κ} {Fn : FFun} {code : List OffsetInstruction} {i : ℕ} {s s' : St}
    (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) (h : AtF img Fn code i s) : AtF img Fn code i s' := by
  obtain ⟨cur, pend, h0, hh⟩ := h
  refine ⟨cur, pend, h0, hh.imp (fun ⟨A, hA, hH⟩ ↦ ⟨A, hA, hH.mono hle hfp⟩) fun ⟨g, hg, hj, hH⟩ ↦
    ⟨g, hg, hj, hH.mono hle hfp⟩⟩

theorem CoreIn.mono {img : MemoryImage κ} {Cf : CFun} {code : List OffsetInstruction} {i : ℕ} {m m' : Mem}
    {fp : ℕ} (hle : m ≤ m') (h : CoreIn img Cf code i m fp) : CoreIn img Cf code i m' fp := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨atF_mono (s := Mode.stOf m fp) hle rfl h1, fun o ho ↦ written_mono hle (h2 o ho), fun σ hσ ↦ ?_⟩
  obtain ⟨pos, pre, es, vs, rd, h4, h5, h6, h8, h7⟩ := h3 σ hσ
  exact ⟨pos, pre, es, vs, rd, h4, h5, h6, h8, fun y hy ↦ (h7 y hy).mono hle⟩

theorem CoreAt.mono {img : MemoryImage κ} {Cf : CFun} {code : List OffsetInstruction} {i : ℕ} {s s' : St}
    (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) (h : CoreAt img Cf code i s) : CoreAt img Cf code i s' :=
  fun m hm ha ↦ hfp ▸ h m (Mem.le_trans hle hm) ha

/-- `CoreIn` at the state's memory gives `CoreAt`. -/
theorem coreAt_of {img : MemoryImage κ} {Cf : CFun} {code : List OffsetInstruction} {i : ℕ} {s : St}
    (h : CoreIn img Cf code i s.mem s.fp) : CoreAt img Cf code i s :=
  fun _ hm _ ↦ h.mono hm

/-! ## The signature, translated -/

/-- A frame base `[o]^e` as a parameter's power `(o - 2, e)`. -/
def baseOfMono : Mode.Base × ℕ → Option (ℕ × ℕ)
  | (.fr o, e) => if 2 ≤ o then some (o - 2, e) else none
  | _ => none

/-- **A signature's product as a cell** over parameter numbers: no frame address, bases frame cells
`2 + k`. -/
def monoC (m : Mode.Mono) : Option CCell :=
  if m.fp = 0 then (m.bs.mapM baseOfMono).map fun bs ↦ ⟨bs, m.k⟩ else none

/-- **A product over the slots below `n`**: its bases frame cells `2 + b`, `b < n`, and with `ent`
among the entry cells. -/
def monoS (G : Mode.Sig) (n : ℕ) (ent : Bool) (m : Mode.Mono) : Bool :=
  m.bs.all fun b ↦ match b.1 with
    | .fr o => decide (2 ≤ o) && decide (o - 2 < n) && decide (o < 2 ^ 28) && (!ent || G.entry.contains o)
    | .hp _ _ => false

/-- **A product the function's return can name**: its bases entry cells of parameters or return cells
of returned words. -/
def monoR (G : Mode.Sig) (np nr : ℕ) (m : Mode.Mono) : Bool :=
  m.bs.all fun b ↦ match b.1 with
    | .fr o => decide (2 ≤ o) && decide (o < 2 ^ 28) &&
      ((decide (o - 2 < np) && G.entry.contains o) || (decide (np ≤ o - 2) && decide (o - 2 < np + nr) &&
        G.ret.contains o))
    | .hp _ _ => false

/-- A cell among cells. -/
def cellIn (c : CCell) (l : List CCell) : Bool := l.any fun c' ↦ c'.beq c

/-- A run's points, its bounds constants. -/
def runPts (c : CCell) (r : Mode.Rng) : Option (List CCell) :=
  match r.lo, r.hi with
  | .num a, .num b => some ((List.range (b - a)).map fun j ↦ ⟨c.bases, c.off + (r.S * (a + j) + r.d)⟩)
  | _, _ => none

/-- **A run of constant bounds as a heap run** over slots. -/
def rngC (r : Mode.Rng) : Option CRun :=
  match r.lo, r.hi with
  | .num a, .num b => bif decide (a < 2 ^ 62) && decide (b < 2 ^ 62) then
      (monoC r.q).map fun c ↦ ⟨⟨c.bases, c.off + r.d⟩, r.S, .num a, .num b⟩ else none
  | _, _ => none

/-- The cell `c` is a point of the run of constant bounds `r`. -/
def ptIn (c : CCell) (r : Mode.Rng) : Bool :=
  match runPts ⟨[], 0⟩ r, monoC r.q with
  | some l, some q => l.any fun p ↦ (CCell.beq ⟨q.bases, q.off + p.off⟩ c)
  | _, _ => false

/-- A product, translated, is the cell `c`. -/
def monoIs (m : Mode.Mono) (c : CCell) : Bool :=
  match monoC m with
  | some c' => c'.beq c
  | none => false

/-- A run of constant bounds, translated, is the heap run `q`. -/
def rngIs (r : Mode.Rng) (q : CRun) : Bool :=
  match rngC r with
  | some q' => decide (q' = q)
  | none => false

/-- **The signature callers know, translated**: no self frame pointer, termination fact, loop run,
pointer fact or order; its heap preconditions each a cell or run of the signature's (over parameters);
each heap cell and run it promises (over parameters and returned words) among the promised cells
`Cf.posts` or the heap signature's runs. -/
def sigOk (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) : Bool :=
  G.self.isNone && G.term.isEmpty && G.postL.isEmpty && G.postP.isEmpty && G.postLP.isEmpty &&
    G.postT.isEmpty && G.postC.isEmpty && Cf.H.sig.preP.isEmpty && Cf.H.sig.prePR.isEmpty &&
    Cf.H.sig.pre.all (fun c ↦ G.pre.any (fun m ↦ monoS G np false m && monoIs m c) ||
      G.preR.any fun r ↦ monoS G np false r.q && ptIn c r) &&
    Cf.H.sig.preR.all (fun q ↦ G.preR.any fun r ↦ monoS G np false r.q && rngIs r q) &&
    G.post.all (fun m ↦ monoR G np nr m && match monoC m with
      | some c => cellIn c Cf.posts
      | none => false) &&
    G.postR.all fun r ↦ monoR G np nr r.q && ((Cf.H.sig.postR.any fun q ↦ rngIs r q) ||
      match monoC r.q, runPts ⟨[], 0⟩ r with
      | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ Cf.posts
      | _, _ => false)

/-- **A callee's mode signature `G` holds of its heap signature `h`** at a call of `na` arguments
and `nr` returned words: no self frame pointer or pointer precondition, its header cells entry cells;
each of its preconditions over the arguments' entry cells one of `h`'s (a run `h`'s run or its
points `h`'s cells); each guarantee of `h` one of `G`'s (cells or points over the arguments and
returned words, runs `G`'s); `h` with no pointer guarantee or returned word's monomial. -/
def fitB (G : Mode.Sig) (h : HSig) (na nr : ℕ) : Bool :=
  G.self.isNone && G.preP.isEmpty && G.entry.contains 0 && G.entry.contains 1 &&
    h.postP.isEmpty && h.postPR.isEmpty && h.retM.isEmpty &&
    G.pre.all (fun m ↦ monoS G na true m && match monoC m with
      | some c => cellIn c h.pre
      | none => false) &&
    G.preR.all (fun r ↦ monoS G na true r.q && ((h.preR.any fun q ↦ rngIs r q) ||
      match monoC r.q, runPts ⟨[], 0⟩ r with
      | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ h.pre
      | _, _ => false)) &&
    h.post.all (fun c ↦ G.post.any (fun m ↦ monoS G (na + nr) false m && monoIs m c) ||
      G.postR.any fun r ↦ monoS G (na + nr) false r.q && ptIn c r) &&
    h.postR.all fun q ↦ G.postR.any fun r ↦ monoS G (na + nr) false r.q && rngIs r q

/-- **A call's `JUMP`**, its target a callee's entry (`ents`): that entry outside the function, and the
callee's mode signature there holding of its heap signature at the call's site. -/
noncomputable def jumpCallOk (Cf : CFun) : OffsetInstruction → Bool
  | .jump _ od of => match Cf.X.pcAt od with
    | some t => match getF Cf.X.ents t with
      | some f => !(decide (Cf.frame.entry ≤ t) && decide (t < Cf.frame.entry + Cf.frame.len)) &&
        decide (t < 2 ^ 30) && !Cf.X.selfAt of && match Cf.frame.sigs.get t, getF Cf.X.sites of with
        | some G, some s => decide (s.r < 2 ^ 30) && fitB G (Cf.sigOf f) s.args.length s.rets.length
        | _, _ => false
      | none => true
    | none => true
  | _ => true

/-- The returned values' count of a body's first `ret`. -/
def retN (body : List Stmt) : ℕ :=
  (body.findSome? fun s ↦ match s with
    | .ret vs => some vs.length
    | _ => none).getD 0

/-- Every `ret` of the body returns `n` values. -/
def retsN (n : ℕ) (body : List Stmt) : Bool :=
  body.all fun s ↦ match s with
    | .ret vs => vs.length == n
    | _ => true

/-- No call of the body is to `f`, and each callee's heap signature names no returned word's
monomial. -/
def callsB (Cf : CFun) : Bool :=
  (stmtsOf Cf.fn.body).all fun s ↦ match s with
    | .call g _ _ => !(g == Cf.fn.name) && (Cf.sigOf g).retM.isEmpty
    | _ => true

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
  | .ret vs :: _, st => G.retV.all fun p ↦ decide (p.1 < 2 ^ 28) && G.ret.contains p.1 && monoS G np true p.2 &&
      match monoC p.2 with
      | some c => retAt X st.env vs p.1 c
      | none => false
  | _, _ => false

/-- Each returned product of the signature (`retV`) a return cell `2 + np + k` whose word the heap
signature's `retM` names. -/
def retMChk (Cf : CFun) (G : Mode.Sig) (np : ℕ) : Bool :=
  G.retV.all fun p ↦ decide (p.1 < 2 ^ 28) && G.ret.contains p.1 && monoS G np true p.2 && decide (2 + np ≤ p.1) &&
    match monoC p.2 with
    | some c => Cf.H.sig.retM.any fun q ↦ Nat.beq q.1 (p.1 - 2 - np) && q.2.beq c
    | none => false

/-- **The returned products' check** (`retV`): none, each a returned value's monomial by the heap pass
(milestone 1), or each named by the heap signature's `retM`. -/
noncomputable def retVOk (Cf : CFun) (G : Mode.Sig) : Bool :=
  G.retV.isEmpty || retMChk Cf G Cf.fn.params.length || Cf.H.readT.seq fun R ↦ (trieFrom Cf.H.sig.pre 0 .nil).seq fun P ↦
    retVGo Cf.X G Cf.fn.params.length ⟨Cf.pows, R, P⟩ Cf.fn.body ⟨.nil, .nil, 0⟩

/-! ## The shape -/

/-- A straight-line body: atoms and returns. -/
def straight (body : List Stmt) : Bool :=
  body.all fun s ↦ match s with
    | .atom _ => true
    | .ret _ => true
    | _ => false

/-- A statement the core route takes: an atom, a branch, a `match`, a return or a call. -/
def ctrlOk : Stmt → Bool
  | .atom _ | .ite .. | .match_ .. | .ret _ | .call .. => true
  | _ => false

/-- A call. -/
def isCall : Stmt → Bool
  | .call .. => true
  | _ => false

/-- A top-level statement: a return, a call, or one with no `ret` and no call in it. -/
def topOk : Stmt → Bool
  | .ret _ => true
  | .call .. => true
  | s => Core.Stmt.noRet s && !(Bridge.stmtsSub s).any isCall

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

/-- No callee's signature at an offset of the function past its entry. -/
def sigsOut {α : Type} (sigs : Exec.Trie α) (entry len : ℕ) : Bool :=
  (List.range len).all fun o ↦ Nat.beq o 0 || (sigs.get (entry + o)).isNone

/-- **The shape the core route takes**: a body of atoms, branches, `match`es, calls at its top level
and returns, one return count (`bodyC`, `retsN`), not `main`, no frame cell `1` its frame pointer's,
no pc at cell `0`, the walk's tables the `match`es' arms, no callee inside the function, no residual,
small entry cells. -/
noncomputable def shapeOk (Cf : CFun) (code : List OffsetInstruction) : Bool :=
  bodyC Cf.fn.body && !Cf.X.main && !Cf.X.selfAt 1 && (Cf.X.pcAt 0).isNone && retsN (retN Cf.fn.body) (stmtsOf Cf.fn.body) &&
    tgtOk Cf code && sigsOut Cf.frame.sigs Cf.frame.entry Cf.frame.len &&
    !Cf.frame.F.fpOne && trieNil Cf.frame.nzr && Cf.frame.sig.entry.all (fun o ↦ decide (o + 1 < 2 ^ Exec.envDepth)) &&
    decide (Cf.frame.entry + Cf.frame.len ≤ 2 ^ 30) && Mode.pcsIncr Cf.frame.hints

/-- **The heap check of a function on the core route**: milestone 1's (`heapOk`, `postOk`, straight
line, its promised cells over parameters), or the check with calls (`heapOkC`, at its callees'
signatures `Cf.sigOf`, no termination fact or residual, no callee's returned word's monomial). -/
inductive HeapK (Cf : CFun) : Prop
  | m1 : heapOk Cf.pows (fun _ ↦ .empty) Cf.fn Cf.H = true → postOk Cf.pows Cf.H Cf.post Cf.fn.body = true →
      (stmtsOf Cf.fn.body).all (fun s ↦ !isCall s) = true → preOver Cf.fn.params.length (Cf.post.map (·.1)) = true → Cf.H.sig.retM = [] →
      HeapK Cf
  | c : heapOkC Cf.pows Cf.sigOf Cf.fn Cf.H = true → Cf.H.sig.term = [] → Cf.H.res = [] → callsB Cf = true →
      Cf.post = [] → HeapK Cf

/-- **The kernel's checks of a function on the core route**, and its ties to its mode certificate
`K`: the code, entry and signatures, the advice's hints at its pcs, its fetches, its operands small,
the powers' tables. -/
structure CoreOk (K : Mode.Cert) (Cf : CFun) : Prop where
  heap : HeapK Cf
  pair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body K.code Cf.d = true
  frame : envOk Cf.frame = true ∧ armsOk Cf.frame = true ∧ FrameAcc Cf.frame K.code
  sig : sigOk K.F.sig Cf Cf.fn.params.length (retN Cf.fn.body) = true
  retv : retVOk Cf K.F.sig = true
  shape : shapeOk Cf K.code = true
  calls : K.code.all (jumpCallOk Cf) = true
  jtd : jtdOk Cf K.E K.code = true
  fsig : Cf.frame.sig = K.F.sig
  fsigs : Cf.frame.sigs = K.E.sigs
  fentry : Cf.frame.entry = K.F.entry
  flen : Cf.frame.len = K.code.length
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
