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
(`X.locAt`), each parameter at its cell `2 + k`, each returned value at its cell, its heap
certificate's residuals true at it (`res`, from the honest tree).

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
  /-- Each dispatch's callees, by its call site's callee frame cell. -/
  dsp : List (ℕ × List String)
  /-- Its contract is its heap signature's (`heapCtr`), not its mode signature's. -/
  hc : Bool
  /-- The callees whose contract is their heap signature's (`Cf.sigOf f`), by name, with their numbers of
  arguments and returned words. -/
  hcs : List (String × ℕ × ℕ)

/-- **The heap signatures the heap check reads**: its own at its own name, its callees' (`cs`). -/
def CFun.sigOf (Cf : CFun) (f : String) : HSig :=
  bif f == Cf.fn.name then Cf.H.sig else (Cf.cs.lookup f).getD {}

/-- The heap cells the function promises, over slots (parameters, then returned words): milestone 1's
over parameters, the heap signature's. -/
def CFun.posts (Cf : CFun) : List CCell :=
  (Cf.post.map (·.1)).filter (fun c ↦ preOver Cf.fn.params.length [c]) ++ Cf.H.sig.post

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
  /-- A dispatch's target cell: the callee's entry, by the entries its context names. -/
  tgt : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ (i : ℕ) (c : Call) q (s : B2C.Site), (calls es)[i]? = some c →
    c.taken = true → Cf.X.siteAt q c.args c.rets = some s → s.tgt ≠ 0 → ∀ t, Cf.X.entOk t c.f = true →
    Rd img fp s.tgt = some (ofK (g ^ t))
  /-- What its jumps read. -/
  jc : JumpF img Cf.X Cf.fn.body fp σ
  holds : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ e ∈ es, e.Holds img.read σ
  /-- A loop's tail call, its last call, through a next-frame cell `q` (holding `fp·g^S`) of a `JUMP`
  fetched at one of its offsets: that frame `fp + S`, its header this frame's, its arguments. -/
  tail : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ (i : ℕ) (c : Call), (calls es)[i]? = some c →
    i + 1 = (calls es).length → ∀ off oc od q S, off < Cf.X.len → oc < 2 ^ 28 → od < 2 ^ 28 → q < 2 ^ 28 →
    guestProgram.fetch (addressOfIndex (Cf.X.entry + off)) =
      some (OffsetInstruction.jump oc od q).toLeanIsaInstruction →
    Cf.X.statOf q = some (.fpg S) → S ≠ 0 →
    Rd img fp q = some (ofK (g ^ (fp + S))) ∧ Rd img (fp + S) 0 = Rd img fp 0 ∧ Rd img (fp + S) 1 = Rd img fp 1 ∧
      ∀ k (hk : k < c.args.length), Rd img (fp + S) (2 + k) = some (σ c.args[k])
  /-- Its heap certificate's residuals, at it. -/
  res : ResF Cf.H σ

/-- The frame cell a run bound's exponent is of, if any. -/
def boundCells : Mode.Idx → List ℕ
  | .ex (.fr o) _ => [o]
  | _ => []

/-- **The frame cells whose words the signature's entry runs (`preR`, `preP`) bound by exponent.** -/
def expCells (G : Mode.Sig) : List ℕ :=
  (G.preR ++ G.preP.map (·.1)).flatMap fun r ↦ boundCells r.lo ++ boundCells r.hi

/-- **The words of frame `fp`'s cells `os` in the reference are powers of `g`** of exponents below `2 ^ 62`. -/
def ExpW (img : MemoryImage κ) (os : List ℕ) (fp : ℕ) : Prop :=
  ∀ o ∈ os, ∃ e, e < 2 ^ 62 ∧ Rd img fp o = some (ofK (g ^ e))

/-- **The core route's frame predicate, in a memory**: frame `fp` at offset `i` in memory `m`: the
frame walk's state there holds (`AtF`), the entry cells are written, and for every honest valuation
of the frame, its path splits at the pairing's position at `i` (`pairAt`), every cell written by the
events before it (`WrittenC`, pointer facts read on the reference) being written in `m` (`WrK`). -/
def CoreIn (img : MemoryImage κ) (Cf : CFun) (code : List OffsetInstruction) (i : ℕ) (m : Mem) (fp : ℕ) : Prop :=
  AtF img Cf.frame code i (Mode.stOf m fp) ∧ (∀ o ∈ Cf.frame.sig.entry, m.written (fp + o) = true) ∧
    ∀ σ, HonF img Cf fp σ → ∃ pos pre es vs rd, rd = img.read ∧ pairAt Cf.P Cf.fn.body code Cf.d i = some pos ∧
      walk σ Cf.fn.body = .ret (pre ++ es) vs ∧ walk σ pos = .ret es vs ∧ (∀ e ∈ pre ++ es, e.Holds rd σ) ∧
      ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre y → WrK m y

/-- The frame cells whose words the core route knows to be powers of `g`: the mode signature's entry runs'
exponent cells (`expCells`), none for a heap contract. -/
def CFun.xc (Cf : CFun) : List ℕ := bif Cf.hc then [] else expCells Cf.frame.sig

theorem CFun.xc_of {Cf : CFun} (h : Cf.hc = false) : Cf.xc = expCells Cf.frame.sig := by
  simp [CFun.xc, h]

/-- **The core route's frame predicate**: the entry runs' exponent cells powers of `g` (`ExpW`, from
entry, `CFun.xc`), and `CoreIn` in every memory past the state's agreeing with the reference (so a caller resumes
from what its callee guarantees, in any memory past the call). -/
def CoreAt (img : MemoryImage κ) (Cf : CFun) (code : List OffsetInstruction) (i : ℕ) (s : St) : Prop :=
  ExpW img Cf.xc s.fp ∧ ∀ m, s.mem ≤ m → Agree m (refMem img) → CoreIn img Cf code i m s.fp

/-- **The memory after a step stays within the reference's `2 ^ κ` cells**, from the states `Y`. -/
def UsedNext (C : Ctx) (img : MemoryImage κ) (Y : St → Prop) : Prop :=
  ∀ s op s1 s', Y s → C.ops[s.pc]? = some op → ((C.hints[s.pc]?).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 →
    Prover.Exec.Moves (refMem img) s s1 → runOp C s1 op = .ok s' → s'.mem.used ≤ 2 ^ κ

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
  obtain ⟨pos, pre, es, vs, rd, hrd, h4, h5, h6, h8, h7⟩ := h3 σ hσ
  exact ⟨pos, pre, es, vs, rd, hrd, h4, h5, h6, h8, fun y hy ↦ (h7 y hy).mono hle⟩

theorem CoreAt.mono {img : MemoryImage κ} {Cf : CFun} {code : List OffsetInstruction} {i : ℕ} {s s' : St}
    (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) (h : CoreAt img Cf code i s) : CoreAt img Cf code i s' :=
  ⟨hfp ▸ h.1, fun m hm ha ↦ hfp ▸ h.2 m (Mem.le_trans hle hm) ha⟩

/-- `CoreIn` at the state's memory gives `CoreAt`. -/
theorem coreAt_of {img : MemoryImage κ} {Cf : CFun} {code : List OffsetInstruction} {i : ℕ} {s : St}
    (hx : ExpW img Cf.xc s.fp) (h : CoreIn img Cf code i s.mem s.fp) : CoreAt img Cf code i s :=
  ⟨hx, fun _ hm _ ↦ h.mono hm⟩

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

/-! ## Exponent bounds and pointer runs -/

/-- **A run bound as a heap index** over slots: a constant below `2 ^ 62`, or the exponent of the word
of frame cell `2 + b`, slot `b` (no offset). -/
def idxX : Mode.Idx → Option CIdx
  | .num n => bif decide (n < 2 ^ 62) then some (.num n) else none
  | .ex (.fr o) c => bif decide (2 ≤ o) && Nat.beq c 0 then some (.val (o - 2)) else none
  | .ex (.hp _ _) _ => none

/-- A bound's base, as a product's bases. -/
def idxB : Mode.Idx → List (Mode.Base × ℕ)
  | .num _ => []
  | .ex b _ => [(b, 1)]

/-- **A run bound with an exponent at return**: a constant, or the exponent of the word of frame cell
`2 + b`, `b < n`, one of the entry runs' (`expCells`). -/
def expI (G : Mode.Sig) (n : ℕ) : Mode.Idx → Bool
  | .num _ => true
  | .ex (.fr o) _ => decide (2 ≤ o) && decide (o - 2 < n) && (expCells G).contains o
  | .ex (.hp _ _) _ => false

/-- **A run as a heap run over slots**: `rngC` with exponent bounds. -/
def rngX (r : Mode.Rng) : Option CRun :=
  match idxX r.lo, idxX r.hi, monoC r.q with
  | some lo, some hi, some c => some ⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩
  | _, _, _ => none

/-- The bases of a run's product and bounds, as one product's. -/
def rngM (r : Mode.Rng) : Mode.Mono := ⟨0, 0, r.q.bs ++ idxB r.lo ++ idxB r.hi⟩

/-- A run, translated, is the heap run `q`. -/
def rngXIs (r : Mode.Rng) (q : CRun) : Bool :=
  match rngX r with
  | some q' => decide (q' = q)
  | none => false

/-- **A pointer run, translated**, is the heap pointer run `p`: the same run, the same offsets. -/
def prunIs (r : Mode.Rng × List ℕ) (p : CRun × List ℕ) : Bool :=
  rngXIs r.1 p.1 && decide (r.2 = p.2)

/-- The word a top-level `const` atom before any `ret` sets value `n` to. -/
def constOf : List Stmt → ℕ → Option E
  | [], _ => none
  | .ret _ :: _, _ => none
  | .atom (.const d c) :: ss, n => match vnum d with
    | some n' => bif Nat.beq n' n then some c else constOf ss n
    | none => constOf ss n
  | _ :: ss, n => constOf ss n

/-- **A value a top-level `const` sets to a power of `g`** below `2 ^ 62`. -/
noncomputable def constPow (pows : Exec.PowTree) (body : List Stmt) (v : V) : Bool :=
  match vnum v with
  | some n => match constOf body n with
    | some c => match powOf pows c with
      | some e => decide (e < 2 ^ 62)
      | none => false
    | none => false
  | none => false

/-- **A callee's run bound at a call on `args` has an exponent**: a constant, or an argument
`constPow`. -/
noncomputable def idxPow (pows : Exec.PowTree) (body : List Stmt) (args : List V) : CIdx → Bool
  | .num n => decide (n < 2 ^ 62)
  | .val b => match args[b]? with
    | some v => constPow pows body v
    | none => false
  | .mono _ => false

/-- **A callee's run bound at a call on `args` is a parameter's exponent**: argument `b` the parameter
`k < np` whose cell `2 + k` is one of `xs` (the entry runs' exponent cells, `CFun.xc`). -/
def expArg (xs : List ℕ) (np : ℕ) (args : List V) : CIdx → Bool
  | .val b => match args[b]? with
    | some v => match vnum v with
      | some k => decide (k < np) && xs.contains (2 + k)
      | none => false
    | none => false
  | _ => false

/-- A callee's run bound at a call on `args` has an exponent: `idxPow`, or a parameter's (`expArg`). -/
noncomputable def idxPowC (Cf : CFun) (args : List V) (i : CIdx) : Bool :=
  idxPow Cf.pows Cf.fn.body args i || expArg Cf.xc Cf.fn.params.length args i

/-- **A pointer-based product** `g^k · [[q] · g^d]`: its frame cell `q` and offset `d`. -/
def hpOf (m : Mode.Mono) : Option (ℕ × ℕ) :=
  match m.fp, m.bs with
  | 0, [(.hp q d, 1)] => some (q, d)
  | _, _ => none

/-- A frame cell `q` of a slot below `n` (with `ent`, an entry cell). -/
def hpSlot (G : Mode.Sig) (n : ℕ) (ent : Bool) (q : ℕ) : Bool :=
  decide (2 ≤ q) && decide (q - 2 < n) && decide (q < 2 ^ 28) && (!ent || G.entry.contains q)

/-- **A pointer-based product as a pointer fact**: over the slots below `n`, its pointer cell
`⟨[(q - 2, 1)], d⟩` among `cs`, a pointer fact of `ps` there naming its offset. -/
def hpIn (G : Mode.Sig) (n : ℕ) (ent : Bool) (ps : List (CCell × List ℕ)) (cs : List CCell) (m : Mode.Mono) : Bool :=
  match hpOf m with
  | some (q, d) => hpSlot G n ent q && cellIn ⟨[(q - 2, 1)], d⟩ cs &&
      ps.any fun p ↦ p.1.beq ⟨[(q - 2, 1)], d⟩ && p.2.contains m.k
  | none => false

/-- **A pointer fact as pointer-based products**: each offset a product of `ms` over the slots below `n`. -/
def hpAll (G : Mode.Sig) (n : ℕ) (ms : List Mode.Mono) (p : CCell × List ℕ) : Bool :=
  p.2.all fun o ↦ ms.any fun m ↦ match hpOf m with
    | some (q, d) => hpSlot G n false q && p.1.beq ⟨[(q - 2, 1)], d⟩ && Nat.beq m.k o
    | none => false

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
pointer fact or order, no ghost slot; its heap preconditions each a cell or run of the signature's (over parameters);
each heap cell and run it promises (over parameters and returned words) among the promised cells
`Cf.posts` or the heap signature's runs, or (`postIn`, `postRIn`) over parameters, returned values and
words a top-level `load` reads, among milestone 1's promised cells. -/
noncomputable def sigOk (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) : Bool :=
  G.self.isNone && G.term.isEmpty && G.postL.isEmpty &&
    (G.postP.all fun r ↦ monoR G np nr (rngM r.1) && expI G (np + nr) r.1.lo && expI G (np + nr) r.1.hi &&
      Cf.H.sig.postPR.any (prunIs r ·) && Cf.H.sig.postR.any (rngXIs r.1 ·)) && G.postLP.isEmpty &&
    G.postT.isEmpty && G.postC.isEmpty && Cf.H.sig.preP.all (hpAll G np G.pre) &&
    (Cf.H.sig.prePR.all fun p ↦ G.preP.any fun r ↦ monoS G np false (rngM r.1) && prunIs r p) &&
    Cf.H.sig.pre.all (fun c ↦ G.pre.any (fun m ↦ monoS G np false m && monoIs m c) ||
      G.preR.any fun r ↦ monoS G np false r.q && ptIn c r) &&
    Cf.H.sig.preR.all (fun q ↦ G.preR.any fun r ↦ (monoS G np false r.q && rngIs r q) ||
      (monoS G np false (rngM r) && rngXIs r q)) &&
    G.post.all (fun m ↦ (monoR G np nr m && match monoC m with
      | some c => cellIn c Cf.posts
      | none => false) || postIn Cf.X Cf.fn.body G np (Cf.post.map (·.1)) m ||
      hpIn G np true Cf.H.sig.postP Cf.posts m) &&
    (G.postR.all fun r ↦ (monoR G np nr r.q && ((Cf.H.sig.postR.any fun q ↦ rngIs r q) ||
      match monoC r.q, runPts ⟨[], 0⟩ r with
      | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ Cf.posts
      | _, _ => false)) || postRIn Cf.X Cf.fn.body G np (Cf.post.map (·.1)) r ||
      (monoR G np nr (rngM r) && expI G (np + nr) r.lo && expI G (np + nr) r.hi &&
        Cf.H.sig.postR.any (rngXIs r ·))) && Nat.beq Cf.H.sig.ghosts 0

/-- **A callee's mode signature `G` holds of its heap signature `h`** at a call of `na` arguments
and `nr` returned words: its self frame pointer cell (a loop's) small, its header cells entry cells;
each of its preconditions over the arguments' entry cells one of `h`'s (a run `h`'s run or its
points `h`'s cells); each guarantee of `h` one of `G`'s (cells or points over the arguments and
returned words, runs `G`'s or its loop's); `h` with no returned word's monomial or ghost slot. -/
def fitB (G : Mode.Sig) (h : HSig) (na nr : ℕ) : Bool :=
  (match G.self with
    | some o => decide (o < 2 ^ 28)
    | none => true) &&
    (G.preP.all fun r ↦ monoS G na true (rngM r.1) && h.prePR.any (prunIs r ·) && h.preR.any (rngXIs r.1 ·)) &&
    G.entry.contains 0 && G.entry.contains 1 && h.postP.all (hpAll G (na + nr) G.post) &&
    (h.postPR.all fun p ↦ (G.postP ++ G.postLP).any fun r ↦ monoS G (na + nr) false (rngM r.1) && prunIs r p) &&
    h.retM.isEmpty &&
    G.pre.all (fun m ↦ (monoS G na true m && match monoC m with
      | some c => cellIn c h.pre
      | none => false) || hpIn G na true h.preP h.pre m) &&
    G.preR.all (fun r ↦ (monoS G na true r.q && ((h.preR.any fun q ↦ rngIs r q) ||
      match monoC r.q, runPts ⟨[], 0⟩ r with
      | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ h.pre
      | _, _ => false)) || (monoS G na true (rngM r) && h.preR.any (rngXIs r ·))) &&
    h.post.all (fun c ↦ G.post.any (fun m ↦ monoS G (na + nr) false m && monoIs m c) ||
      G.postR.any fun r ↦ monoS G (na + nr) false r.q && ptIn c r) &&
    (h.postR.all fun q ↦ (G.postR ++ G.postL).any fun r ↦ (monoS G (na + nr) false r.q && rngIs r q) ||
      (monoS G (na + nr) false (rngM r) && rngXIs r q)) && Nat.beq h.ghosts 0

/-- **A call's callee** `f` at a site of `na` arguments and `nr` returned words, of mode signature `G`: a
callee whose contract is its heap signature's (`hcs`), its counts the site's, its header cells entry cells; or
its mode signature holding of its heap signature (`fitB`). -/
def callOkC (Cf : CFun) (G : Mode.Sig) (f : String) (na nr : ℕ) : Bool :=
  match Cf.hcs.lookup f with
  | some p => decide (p = (na, nr)) && G.entry.contains 0 && G.entry.contains 1
  | none => fitB G (Cf.sigOf f) na nr

/-- A `JUMP` through the target cell of the call site at its callee frame cell: through no `0`, no pc,
no table target cell, from a cell not the own frame's. -/
noncomputable def dspNo (X : AlignCtx) (od of : ℕ) : Bool :=
  match getF X.sites of with
  | some s => !Nat.beq s.tgt od || (!Nat.beq od 0 && (X.pcAt od).isNone && (getF X.arms od).isNone && !X.selfAt of)
  | none => true

/-- **A call's `JUMP`**, its target a callee's entry (`ents`): that entry outside the function, and the
callee's mode signature there holding of its heap signature at the call's site, through a cell neither
the own frame's nor a next frame's; a dispatch's `JUMP` through its site's target cell (`dspNo`). -/
noncomputable def jumpCallOk (Cf : CFun) : OffsetInstruction → Bool
  | .jump _ od of => dspNo Cf.X od of && match Cf.X.pcAt od with
    | some t => match getF Cf.X.ents t with
      | some f => !(decide (Cf.frame.entry ≤ t) && decide (t < Cf.frame.entry + Cf.frame.len)) &&
        decide (t < 2 ^ 30) && !Cf.X.selfAt of && !Cf.X.nextAt of && match Cf.frame.sigs.get t, getF Cf.X.sites of with
        | some G, some s => decide (s.r < 2 ^ 30) && callOkC Cf G f s.args.length s.rets.length
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

/-- A call of `g` on `args`: not of `f`, the callee's heap signature naming no returned word's monomial,
word at return, equation or ghost, its runs' bounds having exponents at the call (`idxPowC`). -/
noncomputable def callChk (Cf : CFun) (g : String) (args : List V) : Bool :=
  !(g == Cf.fn.name) && (Cf.sigOf g).retM.isEmpty && (Cf.sigOf g).postV.isEmpty &&
    (Cf.sigOf g).retEq.isEmpty && Nat.beq (Cf.sigOf g).ghosts 0 &&
    ((Cf.sigOf g).preR.all fun q ↦ idxPowC Cf args q.lo && idxPowC Cf args q.hi) &&
    (Cf.sigOf g).prePR.all fun p ↦ idxPowC Cf args p.1.lo && idxPowC Cf args p.1.hi

/-- **Each call of the body** (`call`, `callIf`, each callee of a `dispatch`) checked by `callChk`; a
dispatch's callees those `dsp` lists at each of its sites. -/
noncomputable def callsB (Cf : CFun) : Bool :=
  (stmtsOf Cf.fn.body).all fun s ↦ match s with
    | .call g args _ => callChk Cf g args
    | .callIf _ g args => callChk Cf g args
    | .dispatch _ fs args rets => fs.all (callChk Cf · args) &&
        Cf.dsp.all fun p ↦ (Cf.X.siteAt p.1 args rets).isNone || p.2 == fs
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

/-- A statement the core route takes: an atom, a branch, a `match`, a return, a call or a conditional
call. -/
def ctrlOk : Stmt → Bool
  | .atom _ | .ite .. | .match_ .. | .ret _ | .call .. | .callIf .. | .dispatch .. => true

/-- A call, a conditional call or a dispatch. -/
def isCall : Stmt → Bool
  | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

/-- A top-level statement: a return, a call, or one with no `ret` and no call in it (a conditional
call included). -/
def topOk : Stmt → Bool
  | .ret _ => true
  | .call .. => true
  | .dispatch .. => true
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

/-- **A dispatch's `JUMP`**: through a target cell, not `0` and no pc, of a call site at its callee
frame cell. -/
noncomputable def dspSite (X : AlignCtx) (od of : ℕ) : Bool :=
  !Nat.beq od 0 && (X.pcAt od).isNone && match getF X.sites of with
    | some s => Nat.beq s.tgt od
    | none => false

/-- A dispatch callee's entry `t`: a callee's (`ents`), outside the function, its mode signature there
holding of its heap signature at the site. -/
noncomputable def dspPc (Cf : CFun) (s : B2C.Site) (t : ℕ) : Bool :=
  match getF Cf.X.ents t with
  | some f => !(decide (Cf.frame.entry ≤ t) && decide (t < Cf.frame.entry + Cf.frame.len)) && decide (t < 2 ^ 30) &&
      match Cf.frame.sigs.get t with
      | some G => callOkC Cf G f s.args.length s.rets.length
      | none => false
  | none => false

/-- **A dispatch's `JUMP` the frame walk reads callees for** (table `k`): no arms, its callees' entries
`dspPc`, every callee `dsp` lists at its site among them, through a cell neither the own frame's nor a
next frame's. -/
noncomputable def dspJ (Cf : CFun) (k od of : ℕ) : Bool :=
  (Cf.frame.arms.get k).isNone && !Cf.X.selfAt of && !Cf.X.nextAt of &&
    match Cf.frame.calls.get k, getF Cf.X.sites of, Cf.dsp.lookup of with
    | some pcs, some s, some fs => Nat.beq s.tgt od && decide (s.r < 2 ^ 30) && pcs.all (dspPc Cf s) &&
        fs.all fun f ↦ pcs.any fun t ↦ Cf.X.entOk t f
    | _, _, _ => false

/-- From offset `i`: each `JUMP` the frame walk reads a table for (`tgt`) is a table jump through a
target cell the alignment's context gives a table (`arms`), no pc and not `0`, the walk's table the
offsets of the slots of every `match` on its selector, no callee's. -/
noncomputable def tgtGo (Cf : CFun) (ml : List (ℕ × ℕ)) : ℕ → List OffsetInstruction → Bool
  | _, [] => true
  | i, ins :: code => (match Cf.frame.tgt.get i with
      | none => match ins with
        | .jump _ od of => !dspSite Cf.X od of
        | _ => true
      | some k => match ins with
        | .jump _ od of => bif dspSite Cf.X od of then dspJ Cf k od of else
            !Nat.beq od 0 && (Cf.X.pcAt od).isNone && (Cf.frame.calls.get k).isNone &&
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

/-- No `frameAddr` atom in the body (so no frame run's cell is guaranteed at return, `FAW`). -/
def noFA (body : List Stmt) : Bool :=
  (stmtsOf body).all fun s ↦ match s with
    | .atom (.frameAddr ..) => false
    | _ => true

/-- **The heap check of a function on the core route**: milestone 1's (`heapOk`, `postOk`, straight
line, its promised cells over parameters), or the check with calls (`heapOkC`, at its callees'
signatures `Cf.sigOf`, no termination fact, no callee's returned word's monomial; its residuals hold at
the honest valuations, `HonF.res`). -/
inductive HeapK (Cf : CFun) : Prop
  | m1 : heapOk Cf.pows (fun _ ↦ .empty) Cf.fn Cf.H = true → postOk Cf.pows Cf.H Cf.post Cf.fn.body = true →
      ((stmtsOf Cf.fn.body).all (fun s ↦ !isCall s) && Cf.H.sig.postP.isEmpty && Cf.H.sig.postPR.isEmpty) = true →
      Cf.H.sig.retM = [] → HeapK Cf
  | c : heapOkC Cf.pows Cf.sigOf Cf.fn Cf.H = true → Cf.H.sig.term = [] → callsB Cf = true →
      Cf.post = [] → Cf.H.ders = [] → noFA Cf.fn.body = true → HeapK Cf

/-- **A heap contract's own signature**: no self frame pointer, termination fact, loop run or ghost slot. -/
def hcOwn (G : Mode.Sig) (Cf : CFun) : Bool :=
  G.self.isNone && G.term.isEmpty && G.postL.isEmpty && G.postLP.isEmpty && Nat.beq Cf.H.sig.ghosts 0

/-- **The own signature's check**: a heap contract's (`hcOwn`), or the mode signature's translation
(`sigOk`). -/
noncomputable def ownOk (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) : Bool :=
  bif Cf.hc then hcOwn G Cf else sigOk G Cf np nr

/-! ## Heap contracts -/

/-- **The words of frame `fp`'s cells `2, …, 2 + n - 1`** in the reference. -/
noncomputable def wsAt (img : MemoryImage κ) (fp n : ℕ) : List E := (List.range n).map fun b ↦ (Rd img fp (2 + b)).getD 0

/-- **A core function's heap contract**: its heap signature `h` at the words of its frame's slots in the
reference (`np` parameters, `nr` returned words), its mode signature `G` for the frame cells: at entry, its
entry cells written and its preconditions; at return, its return cells written, its guarantees and its
returned words' monomials. -/
noncomputable def heapCtr (img : MemoryImage κ) (h : HSig) (G : Mode.Sig) (np nr : ℕ) : Mode.Ctr where
  pre m fp := (∀ o ∈ G.entry, m.written (fp + o) = true) ∧
    ∀ y, PreSet img.read h (wsAt img fp np) y → WrK m y
  post m fp := (∀ o ∈ G.ret, m.written (fp + o) = true) ∧
    (∀ y, PostSet img.read h (wsAt img fp (np + nr)) y → WrK m y) ∧
    RetMOk h (wsAt img fp np) ((wsAt img fp (np + nr)).drop np)
  mono hle h := ⟨fun o ho ↦ written_mono hle (h.1 o ho), fun y hy ↦ (h.2.1 y hy).mono hle, h.2.2⟩

/-- The contract the core data `Cf` assumes of its callee `f`, of mode signature `G`: its heap contract
(`hcs`), or its mode signature's. -/
noncomputable def hcAt (img : MemoryImage κ) (Cf : CFun) (G : Mode.Sig) (f : String) : Option Mode.Ctr :=
  (Cf.hcs.lookup f).map fun p ↦ heapCtr img (Cf.sigOf f) G p.1 p.2

/-- **The contracts the core data `Cf` of `K` assumes**: its own (its heap contract iff `Cf.hc`), and at each
callee entry of its environment the one `hcAt` names by the callee's name there. -/
def CtOk (img : MemoryImage κ) (Ct : Mode.Cts) (K : Mode.Cert) (Cf : CFun) : Prop :=
  Ct K.F.entry = (bif Cf.hc then some (heapCtr img Cf.H.sig K.F.sig Cf.fn.params.length (retN Cf.fn.body))
    else none) ∧
  ∀ t G, K.E.sigs.get t = some G → Ct t = (getF Cf.X.ents t).bind (hcAt img Cf G)

theorem preAt_own {img : MemoryImage κ} {Ct : Mode.Cts} {K : Mode.Cert} {Cf : CFun} (h : CtOk img Ct K Cf)
    (hc : Cf.hc = false) {s : St} : Mode.PreAt Ct K.E K.F.entry K.F.sig s = Mode.Holds s (entryAbs K.E K.F.sig) := by
  unfold Mode.PreAt; rw [h.1, hc]; rfl

theorem preAt_ownH {img : MemoryImage κ} {Ct : Mode.Cts} {K : Mode.Cert} {Cf : CFun} (h : CtOk img Ct K Cf)
    (hc : Cf.hc = true) {s : St} : Mode.PreAt Ct K.E K.F.entry K.F.sig s =
      (heapCtr img Cf.H.sig K.F.sig Cf.fn.params.length (retN Cf.fn.body)).pre s.mem s.fp := by
  unfold Mode.PreAt; rw [h.1, hc]; rfl

theorem postAt_own {img : MemoryImage κ} {Ct : Mode.Cts} {K : Mode.Cert} {Cf : CFun} (h : CtOk img Ct K Cf)
    (hc : Cf.hc = false) {m : Mem} {fp : ℕ} : Mode.PostAt Ct K.F.entry K.F.sig m fp = RetAll m fp K.F.sig := by
  unfold Mode.PostAt; rw [h.1, hc]; rfl

theorem postAt_ownH {img : MemoryImage κ} {Ct : Mode.Cts} {K : Mode.Cert} {Cf : CFun} (h : CtOk img Ct K Cf)
    (hc : Cf.hc = true) {m : Mem} {fp : ℕ} : Mode.PostAt Ct K.F.entry K.F.sig m fp =
      (heapCtr img Cf.H.sig K.F.sig Cf.fn.params.length (retN Cf.fn.body)).post m fp := by
  unfold Mode.PostAt; rw [h.1, hc]; rfl

/-- A callee's contract, by its name at its entry. -/
theorem ct_callee {img : MemoryImage κ} {Ct : Mode.Cts} {K : Mode.Cert} {Cf : CFun} (h : CtOk img Ct K Cf)
    {t : ℕ} {G : Mode.Sig} {f : String} (hG : K.E.sigs.get t = some G) (hf : getF Cf.X.ents t = some f) :
    Ct t = hcAt img Cf G f := by
  rw [h.2 t G hG, hf]; rfl

/-- Mode contracts everywhere, for core data naming none. -/
theorem ctOk_none {img : MemoryImage κ} {K : Mode.Cert} {Cf : CFun} (hc : Cf.hc = false) (hcs : Cf.hcs = []) :
    CtOk img (fun _ ↦ none) K Cf := by
  refine ⟨by rw [hc]; rfl, fun t G _ ↦ ?_⟩
  cases getF Cf.X.ents t <;> simp [hcAt, hcs]

/-- Mode contracts for core data naming none. -/
theorem modeCts_of {img : MemoryImage κ} {Ct : Mode.Cts} {K : Mode.Cert} {Cf : CFun} (h : CtOk img Ct K Cf)
    (hc : Cf.hc = false) (hcs : Cf.hcs = []) : Mode.ModeCts Ct K := by
  refine ⟨by rw [h.1, hc]; rfl, fun t G hG ↦ ?_⟩
  rw [h.2 t G hG]
  cases getF Cf.X.ents t <;> simp [hcAt, hcs]

/-- **The kernel's checks of a function on the core route**, and its ties to its mode certificate
`K`: the code, entry and signatures, the advice's hints at its pcs, its fetches, its operands small,
the powers' tables. -/
structure CoreOk (K : Mode.Cert) (Cf : CFun) : Prop where
  heap : HeapK Cf
  pair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body K.code Cf.d = true
  frame : envOk Cf.frame = true ∧ armsOk Cf.frame = true ∧ FrameAcc Cf.frame K.code
  sig : ownOk K.F.sig Cf Cf.fn.params.length (retN Cf.fn.body) = true
  retv : (Cf.hc || retVOk Cf K.F.sig) = true
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
