/-
  LeanVM.Guest.CoreMode.Core

  The core route's frame predicate (`CoreAt`) and its frame interface (`frameSpec_core`), for a
  straight-line function with no call, no loop and no flow hint: the frame walk's facts, the entry
  cells written, and every heap cell the core path has written by the pairing's position written in
  the executor's memory.
-/

module

public import LeanVM.Guest.CoreMode.FrameSound
public import LeanVM.Guest.CoreMode.PairHeap
public import LeanVM.Guest.CoreMode.Post
public import LeanVM.Guest.CoreMode.Spec
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
(`X.locAt`), each parameter at its cell `2 + k`.

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

/-- **An honest valuation** of `Cf.fn` in frame `fp` of the reference image. -/
structure HonF (img : MemoryImage κ) (Cf : CFun) (fp : ℕ) (σ : Val) : Prop where
  path : ∃ es vs rd, walk σ Cf.fn.body = .ret es vs ∧ ∀ e ∈ es, e.Holds rd σ
  ptr : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ d p off, Ev.atom (.load d p off) ∈ es →
    Rd img fp (Cf.X.locAt p.idx) = some (σ p)
  par : ∀ k < Cf.fn.params.length, Rd img fp (2 + k) = some (σ (V.n k))

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

/-- **A signature's product as a cell** over parameter numbers: no frame address, bases frame cells
`2 + k`. -/
def monoC (m : Mode.Mono) : Option CCell :=
  if m.fp = 0 then (m.bs.mapM baseOfMono).map fun bs ↦ ⟨bs, m.k⟩ else none

/-- A product's bases are entry cells `2 + k` of parameters. -/
def monoOk (G : Mode.Sig) (np : ℕ) (m : Mode.Mono) : Bool :=
  m.bs.all fun b ↦ match b.1 with
    | .fr o => G.entry.contains o && decide (2 ≤ o) && decide (o - 2 < np) && decide (o < 2 ^ 28)
    | .hp _ _ => false

/-- A cell among cells. -/
def cellIn (c : CCell) (l : List CCell) : Bool := l.any fun c' ↦ c'.beq c

/-- A run's points, its bounds constants. -/
def runPts (c : CCell) (r : Mode.Rng) : Option (List CCell) :=
  match r.lo, r.hi with
  | .num a, .num b => some ((List.range (b - a)).map fun j ↦ ⟨c.bases, c.off + (r.S * (a + j) + r.d)⟩)
  | _, _ => none

/-- A promised cell: a product of the signature, a promised cell's. -/
def postIn (G : Mode.Sig) (np : ℕ) (posts : List CCell) (m : Mode.Mono) : Bool :=
  monoOk G np m && match monoC m with
    | some c => cellIn c posts
    | none => false

/-- A promised run: each of its points promised. -/
def postRIn (G : Mode.Sig) (np : ℕ) (posts : List CCell) (r : Mode.Rng) : Bool :=
  monoOk G np r.q && match monoC r.q with
    | some c => match runPts c r with
      | some l => l.all (cellIn · posts)
      | none => false
    | none => false

/-- **The signature callers know, translated**: no self frame pointer, termination fact, loop run,
pointer run, returned product or order; each heap precondition one of the signature's; each heap
cell and run it promises among the promised cells `post`. -/
def sigOk (G : Mode.Sig) (H : HCert) (post : List (CCell × Wit)) (np : ℕ) : Bool :=
  G.self.isNone && G.term.isEmpty && G.postL.isEmpty && G.postP.isEmpty && G.postLP.isEmpty &&
    G.retV.isEmpty && G.postT.isEmpty && G.postC.isEmpty &&
    H.sig.pre.all (fun c ↦ G.pre.any fun m ↦ monoOk G np m && match monoC m with
      | some c' => c'.beq c
      | none => false) &&
    G.post.all (postIn G np (post.map (·.1))) && G.postR.all (postRIn G np (post.map (·.1)))

/-! ## The shape -/

/-- A straight-line body: atoms and returns. -/
def straight (body : List Stmt) : Bool :=
  body.all fun s ↦ match s with
    | .atom _ => true
    | .ret _ => true
    | _ => false

/-- A `JUMP`. -/
def isJumpI : OffsetInstruction → Bool
  | .jump .. => true
  | _ => false

/-- The last instruction: a return the pairing takes by its head statement. -/
noncomputable def retIns (X : AlignCtx) (n : ℕ) : OffsetInstruction → Bool
  | .jump oc od of => Nat.beq od 0 && Nat.beq of 1 && !X.zeroAt oc && !fwdJ X n oc od of
  | _ => false

/-- The only jump is the last instruction, a return the pairing takes by its head statement. -/
noncomputable def retLast (X : AlignCtx) : ℕ → List OffsetInstruction → Bool
  | _, [] => false
  | n, ins :: rest => match rest with
    | [] => retIns X n ins
    | _ :: _ => !isJumpI ins && retLast X (n + 1) rest

/-- No flow hint in the advice entry. -/
def noFlow (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool := d.2.2.all fun p ↦ p.2.all fun h ↦ !isaFlowHint h

/-- An empty trie. -/
def trieNil {α : Type} : Exec.Trie α → Bool
  | .nil => true
  | _ => false

/-- **The shape the core route takes**: a straight-line body, one return jump last, no flow hint,
not `main`, no table jump, no residual, small entry cells. -/
noncomputable def shapeOk (Cf : CFun) (code : List OffsetInstruction) : Bool :=
  straight Cf.fn.body && retLast Cf.X 0 code && noFlow Cf.d && !Cf.frame.F.fpOne &&
    trieNil Cf.frame.tgt && trieNil Cf.frame.nzr && Cf.frame.sig.entry.all (fun o ↦ decide (o + 1 < 2 ^ Exec.envDepth)) &&
    decide (Cf.frame.entry + Cf.frame.len ≤ 2 ^ 30) && Mode.pcsIncr Cf.frame.hints

/-- **The kernel's checks of a function on the core route**, and its ties to its mode certificate
`K`: the code, entry and signature, the advice's hints at its pcs, its fetches, its operands small,
the powers' tables. -/
structure CoreOk (K : Mode.Cert) (Cf : CFun) : Prop where
  heap : heapOk Cf.pows (fun _ ↦ .empty) Cf.fn Cf.H = true
  post : postOk Cf.pows Cf.H Cf.post Cf.fn.body = true
  pair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body K.code Cf.d = true
  frame : frameOk Cf.frame K.code = true
  sig : sigOk K.F.sig Cf.H Cf.post Cf.fn.params.length = true
  shape : shapeOk Cf K.code = true
  fsig : Cf.frame.sig = K.F.sig
  fentry : Cf.frame.entry = K.F.entry
  hints : ∀ i < K.code.length, Mode.hintsAt Data.adviceHints (K.F.entry + i) =
    Mode.hintsAt Cf.frame.hints (K.F.entry + i)
  fetch : Exec.Fetches guestProgram K.F.entry K.code
  small : ∀ i (hi : i < K.code.length), SmallOps K.code[i]
  pows : Cf.pows.Ok
  fpows : Cf.frame.F.pows.Ok

end

end LeanVM.Guest.CoreMode
