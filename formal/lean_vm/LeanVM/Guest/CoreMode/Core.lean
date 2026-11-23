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
certificate's residuals true at it where its entry runs' exponent cells are powers (`res`, from the honest
tree), the caller's cells its signature names holding the slots' words they are linked to (`gl`, `GlF`); `HonB`
is all of it but those two, the facts its ghost words (`V.n (GB + j)`, never named by its body) do not change.

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
  /-- The caller's frame cells its mode signature names (`.hp 1 d`, through header cell `1`), each linked to a
  slot: `(d, b, k)`, cell `d` of the caller's frame holding slot `b`'s word times `g^k` at every honest frame. -/
  gl : List (ℕ × ℕ × ℕ)

/-- **The heap signatures the heap check reads**: its own at its own name, its callees' (`cs`). -/
def CFun.sigOf (Cf : CFun) (f : String) : HSig :=
  bif f == Cf.fn.name then Cf.H.sig else (Cf.cs.lookup f).getD {}

/-- The heap cells the function promises, over slots (parameters, then returned words): `heapOk`'s
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
`match`'s target on the arm its selector picks, a `match`'s or a dispatch's selector. -/
structure JumpF (img : MemoryImage κ) (X : AlignCtx) (body : List Stmt) (fp : ℕ) (σ : Val) : Prop where
  zero : ∀ o, X.zeroAt o = true → Rd img fp o = some 0
  nz : ∀ o, X.nzAt o = true → ∃ w, Rd img fp o = some w ∧ w ≠ 0
  self : ∀ o, X.selfAt o = true → Rd img fp o = some (ofK (g ^ fp))
  pcw : ∀ o t, X.pcAt o = some t → Rd img fp o = some (ofK (g ^ t))
  cond : ∀ es vs, walk σ body = .ret es vs → ∀ c, Ev.inK c ∈ es → Rd img fp (X.locAt c.idx) = some (σ c)
  arm : ∀ x arms, Stmt.match_ x arms ∈ stmtsOf body → ∀ od a, Check.getF X.arms od = some a → a.1 = x.idx →
    ∀ k t, σ x = ofK (g ^ k) → Check.getF X.jt (a.2 + k) = some t → Rd img fp od = some (ofK (g ^ t))
  /-- A `match` the path reaches, at a cursor `zs` from which the path's events are its last ones: its selector at
  its cell. -/
  sel : ∀ zs x arms ss pre es vs, ZOk body zs → zs.cur = .match_ x arms :: ss → walk σ body = .ret (pre ++ es) vs →
    walk σ zs.pos = .ret es vs → Rd img fp (X.locAt x.idx) = some (σ x)
  /-- A dispatch's selector at its cell. -/
  dsel : ∀ es vs, walk σ body = .ret es vs → ∀ x fs args rets, Stmt.dispatch x fs args rets ∈ stmtsOf body →
    Rd img fp (X.locAt x.idx) = some (σ x)

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

/-- The frame cells whose words the core route knows to be powers of `g`: the mode signature's entry runs'
exponent cells (`expCells`), none for a heap contract. -/
def CFun.xc (Cf : CFun) : List ℕ := bif Cf.hc then [] else expCells Cf.frame.sig

theorem CFun.xc_of {Cf : CFun} (h : Cf.hc = false) : Cf.xc = expCells Cf.frame.sig := by
  simp [CFun.xc, h]

/-- **What a link `(d, b, k)` says of the caller's frame `a`**, slot `b`'s word `w`: cell `d` holds `w·g^k`; for `d = 0`
(a cell no mode signature names), `w·g^k` is the frame's address. -/
def LinkW (img : MemoryImage κ) (a d : ℕ) (w : E) (k : ℕ) : Prop :=
  if d = 0 then w * ofK (g ^ k) = ofK (g ^ a) else refMem img (a + d) = w * ofK (g ^ k)

/-- **The caller's linked cells** (`CFun.gl`) at frame `fp` of the reference, the slots' words `ws`: header cell
`1` names the caller's frame `a`, whose cell `d` holds slot `b`'s word times `g^k` (`LinkW`; `d = 0`, its address). -/
def GlF (img : MemoryImage κ) (gl : List (ℕ × ℕ × ℕ)) (fp : ℕ) (ws : List E) : Prop :=
  ∀ d b k, (d, b, k) ∈ gl → ∃ a, Rd img fp 1 = some (ofK (g ^ a)) ∧ a + d < maxCells ∧ LinkW img a d (slotW ws b) k

/-- **The own parameter words** (`HSig.gw`) at the valuation `σ`: ghost `j` the reference's word at the address of
the cell `c` of each `(c, j)` (`0` past the image). -/
def GwR (img : MemoryImage κ) (G : HSig) (σ : Val) : Prop :=
  ∀ c j, (c, j) ∈ G.gw → vw σ (GB + j) = (img.read (c.addrW (vw σ))).getD 0

theorem GwR.ok {img : MemoryImage κ} {G : HSig} {σ : Val} (h : GwR img G σ) : GwOk G img.read σ :=
  fun c j hc w hw ↦ by rw [h c j hc, hw]; rfl

/-- No `frameAddr` atom in the body (so no frame run's cell is guaranteed at return, `FAW`). -/
def noFA (body : List Stmt) : Bool :=
  (stmtsOf body).all fun s ↦ match s with
    | .atom (.frameAddr ..) => false
    | _ => true

/-- No guarantee at return: no cell, run, pointer fact or pointer run. -/
def noPost (h : HSig) : Bool :=
  h.post.isEmpty && h.postR.isEmpty && h.postP.isEmpty && h.postPR.isEmpty && h.postQ.isEmpty &&
    h.postN.isEmpty && h.postRN.isEmpty

/-- **Frame run cells guaranteed**: a `frameAddr` atom, a guarantee, and frame run cells in the heap certificate
(`HCert.fas`); then the walk's facts at the returns write them (`faRetOk`). -/
def faNeed (Cf : CFun) : Bool := !(noFA Cf.fn.body || noPost Cf.H.sig || Cf.H.fas.isEmpty)

/-- **An honest valuation's path, cells and jumps** of `Cf.fn` in frame `fp` of the reference image (`HonF` but its
residuals and linked cells: what does not depend on its ghost words). -/
structure HonB (img : MemoryImage κ) (Cf : CFun) (fp : ℕ) (σ : Val) : Prop where
  path : ∃ es vs rd, walk σ Cf.fn.body = .ret es vs ∧ ∀ e ∈ es, e.Holds rd σ
  ptr : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ a p, Ev.atom a ∈ es → ptrOf a = some p →
    Rd img fp (Cf.X.locAt p.idx) = some (σ p)
  /-- A frame run's pointer, the address of its first value's cell, where frame run cells are guaranteed
  (`faNeed`). -/
  fa : faNeed Cf = true → ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ p r rs,
    Ev.atom (.frameAddr p (r :: rs)) ∈ es → σ p = ofK (addressOfIndex (fp + Cf.X.locAt r.idx))
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
  /-- A loop's tail call, its last call, through a next-frame cell `q` (`AlignCtx.nextAt`) of a `JUMP`
  fetched at one of its offsets: the frame `fp + S` it holds, its header this frame's, its arguments. -/
  tail : ∀ es vs, walk σ Cf.fn.body = .ret es vs → ∀ (i : ℕ) (c : Call), (calls es)[i]? = some c →
    i + 1 = (calls es).length → ∀ off oc od q, off < Cf.X.len → oc < 2 ^ 28 → od < 2 ^ 28 → q < 2 ^ 28 →
    guestProgram.fetch (addressOfIndex (Cf.X.entry + off)) =
      some (OffsetInstruction.jump oc od q).toLeanIsaInstruction →
    Cf.X.nextAt q = true → ∃ S, S ≠ 0 ∧ S < 2 ^ 30 ∧
    Rd img fp q = some (ofK (g ^ (fp + S))) ∧ Rd img (fp + S) 0 = Rd img fp 0 ∧ Rd img (fp + S) 1 = Rd img fp 1 ∧
      ∀ k (hk : k < c.args.length), Rd img (fp + S) (2 + k) = some (σ c.args[k])
  /-- `main`'s frame is `0`. -/
  main : Cf.X.main = true → fp = 0

/-- **An honest valuation** of `Cf.fn` in frame `fp` of the reference image. -/
structure HonF (img : MemoryImage κ) (Cf : CFun) (fp : ℕ) (σ : Val) : Prop extends HonB img Cf fp σ where
  /-- Its heap certificate's residuals, at it, given the frame's entry runs' exponent cells powers of `g`
  (`ExpW`, which `CoreAt` carries). -/
  res : ExpW img Cf.xc fp → ResF Cf.H σ
  /-- The caller's cells its signature names, linked to its slots (`CFun.gl`). -/
  gl : GlF img Cf.gl fp (Cf.fn.params.map σ ++ ownG Cf.H.sig σ)
  /-- Its own parameter words, its ghost words (`HSig.gw`). -/
  gw : GwR img Cf.H.sig σ

/-- **The core route's frame predicate, in a memory**: frame `fp` at offset `i` in memory `m`: the
frame walk's state there holds (`AtF`), the entry cells are written, and for every honest valuation
of the frame, its path splits at the pairing's position at `i` (`pairAt`), the calls before it having their
callees' returned words (`EvM`), every cell written by the events before it (`WrittenC`, pointer facts read on
the reference) being written in `m` (`WrK`). -/
def CoreIn (img : MemoryImage κ) (Cf : CFun) (code : List OffsetInstruction) (i : ℕ) (m : Mem) (fp : ℕ) : Prop :=
  AtF img Cf.frame code i (Mode.stOf m fp) ∧ (∀ o ∈ Cf.frame.sig.entry, m.written (fp + o) = true) ∧
    ∀ σ, HonF img Cf fp σ → ∃ pos pre es vs rd, rd = img.read ∧ pairAt Cf.P Cf.fn.body code Cf.d i = some pos ∧
      walk σ Cf.fn.body = .ret (pre ++ es) vs ∧ walk σ pos = .ret es vs ∧ (∀ e ∈ pre ++ es, e.Holds rd σ) ∧
      (∀ e ∈ pre, EvM Cf.sigOf rd σ e) ∧ ∀ y, WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre y → WrK m y

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
  obtain ⟨pos, pre, es, vs, rd, hrd, h4, h5, h6, h8, h9, h7⟩ := h3 σ hσ
  exact ⟨pos, pre, es, vs, rd, hrd, h4, h5, h6, h8, h9, fun y hy ↦ (h7 y hy).mono hle⟩

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

/-- **A run of constant bounds `[a, b)` as a heap run** over slots; one whose cell offset is `2^62` or more (a negative
offset, modulo the order of `g`), or a bound `2^62` or more (past the order of `g`), starts at its first cell, over
`[0, b - a)`. -/
def rngC (r : Mode.Rng) : Option CRun :=
  match r.lo, r.hi with
  | .num a, .num b => bif decide (b - a < 2 ^ 62) then
      (monoC r.q).map fun c ↦ bif decide (a < 2 ^ 62) && decide (b < 2 ^ 62) && decide (c.off + r.d < 2 ^ 62) then
        ⟨⟨c.bases, c.off + r.d⟩, r.S, .num a, .num b⟩
        else ⟨⟨c.bases, (c.off + r.d + r.S * a) % (2 ^ 64 - 1)⟩, r.S, .num 0, .num (b - a)⟩ else none
  | _, _ => none

/-- Strand `i` of a stride-one run of `S·n` cells: its cells `i, i + S, …`. -/
def strand (q : CRun) (S n i : ℕ) : CRun := ⟨⟨q.base.bases, q.base.off + i⟩, S, .num 0, .num n⟩


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

/-- **Slot `b`'s exponent plus `c`** as a heap index: the slot itself, or the monomial `[b]·g^c`. -/
def idxO (b c : ℕ) : CIdx := bif Nat.beq c 0 then .val b else .mono ⟨[(b, 1)], c⟩

/-- **A run bound as a heap index** over slots: a constant below `2 ^ 62`, or the exponent of the word
of frame cell `2 + b`, slot `b`, plus a constant offset below `2 ^ 28` (`idxO`). -/
def idxX : Mode.Idx → Option CIdx
  | .num n => bif decide (n < 2 ^ 62) then some (.num n) else none
  | .ex (.fr o) c => bif decide (2 ≤ o) && decide (c < 2 ^ 28) then some (idxO (o - 2) c) else none
  | .ex (.hp _ _) _ => none

/-- A bound's base, as a product's bases. -/
def idxB : Mode.Idx → List (Mode.Base × ℕ)
  | .num _ => []
  | .ex b _ => [(b, 1)]

/-- **A residual bounds slot `b`'s exponent with room for `c`**: `e(b) < m`, `m + c ≤ 2^62`. -/
def expRes (b c : ℕ) : CRes → Bool
  | .lt (.val b') (.num m) => Nat.beq b' b && decide (m + c ≤ 2 ^ 62)
  | _ => false

/-- **A run bound with an exponent at return**: a constant, or the exponent of the word of frame cell
`2 + b`, `b < n`: one of the entry runs' (`expCells`, no offset), or a parameter's, `b < np`, a residual of
`res` bounding it with room for the offset (`expRes`). -/
def expI (G : Mode.Sig) (res : List CRes) (np n : ℕ) : Mode.Idx → Bool
  | .num _ => true
  | .ex (.fr o) c => decide (2 ≤ o) && decide (o - 2 < n) &&
      ((Nat.beq c 0 && (expCells G).contains o) || (decide (o - 2 < np) && res.any (expRes (o - 2) c)))
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

/-! ## Guarantees over the body's values -/

/-- A cell over values as a cell over the slots of the values `nv` (slot `i` the value `nv[i]`). -/
def CCell.mapN (nv : List ℕ) (c : CCell) : CCell := ⟨c.bases.map fun b ↦ (nv.idxOf b.1, b.2), c.off⟩

def CIdx.mapN (nv : List ℕ) : CIdx → CIdx
  | .num n => .num n
  | .val v => .val (nv.idxOf v)
  | .mono c => .mono (c.mapN nv)

def CRun.mapN (nv : List ℕ) (r : CRun) : CRun := ⟨r.base.mapN nv, r.stride, r.lo.mapN nv, r.hi.mapN nv⟩

/-- **A run bound as an index over the body's values**: a constant below `2^62`, or the exponent of a base's
word (`baseOfP`: a parameter's, a returned value's, a word a top-level `load` reads past a parameter's). -/
noncomputable def idxN (X : AlignCtx) (body : List Stmt) (np : ℕ) : Mode.Idx → Option CIdx
  | .num n => if n < 2 ^ 62 then some (.num n) else none
  | .ex b c => if c = 0 then (match baseOfP X body np (b, 1) with
    | some (v, 1) => some (.val v)
    | _ => none) else none

/-- **A promised cell among the guarantees over values** (`HSig.postN`): its product's bases those of `postIn`. -/
noncomputable def postNIn (X : AlignCtx) (body : List Stmt) (G : Mode.Sig) (np : ℕ) (h : HSig) (m : Mode.Mono) :
    Bool :=
  monoOkP G np m && match monoF (baseOfP X body np) m with
    | some c => c.vals.all (h.nv.contains ·) && cellIn (c.mapN h.nv) h.postN
    | none => false

/-- **A residual of `res` bounds the value `v`'s exponent** (`e(v) < m`, `m ≤ 2^62`). -/
def expV (res : List CRes) (v : ℕ) : Bool := res.any fun
  | .lt (.val v') (.num m) => Nat.beq v' v && decide (m ≤ capE)
  | _ => false

/-- A bound over values with an exponent: a constant, a value a residual bounds (`expV`), or a parameter `v < np` whose
cell `2 + v` is one of `xs` (the entry runs' exponent cells, `expCells`). -/
def idxOkN (res : List CRes) (xs : List ℕ) (np : ℕ) : CIdx → Bool
  | .num _ => true
  | .val v => expV res v || (decide (v < np) && xs.contains (2 + v))
  | .mono _ => false

/-- **A promised run among the guarantees over values** (`HSig.postRN`): its product and bounds over the bases of
`postIn`, the bounds constants or exponents (`idxN`) a residual or an entry run bounds (`idxOkN`). -/
noncomputable def postRNIn (X : AlignCtx) (body : List Stmt) (G : Mode.Sig) (np : ℕ) (H : HCert) (r : Mode.Rng) :
    Bool :=
  monoOkP G np (rngM r) && match monoF (baseOfP X body np) r.q, idxN X body np r.lo, idxN X body np r.hi with
    | some c, some lo, some hi => idxOkN H.res (expCells G) np lo && idxOkN H.res (expCells G) np hi &&
        (CRun.vals ⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩).all (H.sig.nv.contains ·) &&
        H.sig.postRN.contains (CRun.mapN H.sig.nv ⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩)
    | _, _, _ => false

/-- **The own parameter words as bases** (`HSig.gw`): `(c, j)`, `c = [p]·g^d`, is the base `.hp (2 + p) d` (cell `d`
past parameter `p`'s word) at ghost slot `np + j`. -/
def gpOf (np : ℕ) (gw : List (CCell × ℕ)) : List ((ℕ × ℕ) × ℕ) :=
  gw.filterMap fun x ↦ match x.1.bases with
    | [(p, 1)] => some ((2 + p, x.1.off), np + x.2)
    | _ => none

/-- **A base as a slot's power, the caller's cells linked** (`CFun.gl`): a frame cell `2 + b`, the caller's
cell `d` (`.hp 1 d`) linked to slot `b` with no power of `g`, or an own parameter word (`gp`, `gpOf`) at its ghost
slot. -/
def baseOfL (gl : List (ℕ × ℕ × ℕ)) (gp : List ((ℕ × ℕ) × ℕ)) : Mode.Base × ℕ → Option (ℕ × ℕ)
  | (.fr o, e) => if 2 ≤ o then some (o - 2, e) else none
  | (.hp q d, e) => if q = 1 then (match gl.lookup d with
    | some (b, 0) => some (b, e)
    | _ => none) else (gp.lookup (q, d)).map fun b ↦ (b, e)

/-- **A run bound as a heap index, the caller's cells linked**: `idxX`, or the exponent of the caller's cell
`d` linked to slot `b` times `g^k`. -/
def idxL (gl : List (ℕ × ℕ × ℕ)) : Mode.Idx → Option CIdx
  | .ex (.hp q d) c => if q = 1 ∧ c = 0 then (gl.lookup d).map fun p ↦
      bif Nat.beq p.2 0 then .val p.1 else .mono ⟨[(p.1, 1)], p.2⟩ else none
  | i => idxX i

/-- **A run as a heap run over slots, the caller's cells linked.** -/
def rngL (gl : List (ℕ × ℕ × ℕ)) (gp : List ((ℕ × ℕ) × ℕ)) (r : Mode.Rng) : Option CRun :=
  match idxL gl r.lo, idxL gl r.hi, monoF (baseOfL gl gp) r.q with
  | some lo, some hi, some c => some ⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩
  | _, _, _ => none

/-- A run, translated with the caller's cells linked, is the heap run `q`. -/
def rngLIs (gl : List (ℕ × ℕ × ℕ)) (gp : List ((ℕ × ℕ) × ℕ)) (r : Mode.Rng) (q : CRun) : Bool :=
  match rngL gl gp r with
  | some q' => decide (q' = q)
  | none => false

/-- **A base the frame knows at entry**: a parameter's frame cell `2 + b`, `b < n`, a linked caller's cell, or an
own parameter word (`gp`). -/
def baseS (gl : List (ℕ × ℕ × ℕ)) (gp : List ((ℕ × ℕ) × ℕ)) (n : ℕ) : Mode.Base → Bool
  | .fr o => decide (2 ≤ o) && decide (o - 2 < n) && decide (o < 2 ^ 28)
  | .hp q d => bif Nat.beq q 1 then !Nat.beq d 0 && (gl.lookup d).isSome else decide (q < 2 ^ 28) && (gp.lookup (q, d)).isSome

/-- **A one-point run at a product, translated** (`baseOfL`): `q` is `⟨c, 1, 0, 1⟩`, `c` the product's cell. -/
def ptLIs (gl : List (ℕ × ℕ × ℕ)) (gp : List ((ℕ × ℕ) × ℕ)) (m : Mode.Mono) (q : CRun) : Bool :=
  match monoF (baseOfL gl gp) m with
  | some c => decide (q = ⟨c, 1, .num 0, .num 1⟩)
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

/-- **A callee's run bound at a call on `args` has an exponent**: a constant, an argument `constPow`, or such
an argument's word times `g^c` (`[b]·g^c`), its exponent plus `c` below `2 ^ 62`. -/
noncomputable def idxPow (pows : Exec.PowTree) (body : List Stmt) (args : List V) : CIdx → Bool
  | .num n => decide (n < 2 ^ 62)
  | .val b => match args[b]? with
    | some v => constPow pows body v
    | none => false
  | .mono c => match c.bases with
    | [(b, 1)] => match args[b]? with
      | some v => match vnum v with
        | some n => match constOf body n with
          | some w => match powOf pows w with
            | some e => decide (e + c.off < 2 ^ 62)
            | none => false
          | none => false
        | none => false
      | none => false
    | _ => false

/-- **A callee's run bound at a call on `args` is a parameter's exponent**: argument `b` the parameter
`k < np` whose cell `2 + k` is one of `xs` (the entry runs' exponent cells, `CFun.xc`). -/
def expArg (xs : List ℕ) (np : ℕ) (args : List V) : CIdx → Bool
  | .val b => match args[b]? with
    | some v => match vnum v with
      | some k => decide (k < np) && xs.contains (2 + k)
      | none => false
    | none => false
  | _ => false

/-- **A callee's run bound at a call on `args` is an argument a residual of `res` bounds** (`e(v) < n`,
`n < 2^62`). -/
def resArg (res : List CRes) (args : List V) : CIdx → Bool
  | .val b => match args[b]? with
    | some v => match vnum v with
      | some k => res.any fun
          | .lt (.val k') (.num n) => Nat.beq k' k && decide (n < capE)
          | _ => false
      | none => false
    | none => false
  | .mono c => match c.bases with
    | [(b, 1)] => match args[b]? with
      | some v => match vnum v with
        | some k => res.any fun
            | .lt (.val k') (.num n) => Nat.beq k' k && decide (n + c.off < capE)
            | _ => false
        | none => false
      | none => false
    | _ => false
  | _ => false

/-- A callee's run bound at a call on `args` has an exponent: `idxPow`, a parameter's (`expArg`), or an argument's a
residual bounds (`resArg`). -/
noncomputable def idxPowC (Cf : CFun) (args : List V) (i : CIdx) : Bool :=
  idxPow Cf.pows Cf.fn.body args i || expArg Cf.xc Cf.fn.params.length args i || resArg Cf.H.res args i

/-- **A callee's run bound at a call on `args` its ghost slot `b`** (`|args| ≤ b`): the word the certificate names there
(`gargsOf`) a parameter's whose entry cell's word has an exponent (`xc`). -/
noncomputable def ghostArg (Cf : CFun) (f : String) (args : List V) : CIdx → Bool
  | .val b => decide (args.length ≤ b) && match (gargsOf Cf.H.gargs f args)[b - args.length]? with
    | some c => match c.bases with
      | [(k, 1)] => Nat.beq c.off 0 && decide (k < Cf.fn.params.length) && Cf.xc.contains (2 + k)
      | _ => false
    | none => false
  | _ => false

/-- A callee's run bound at a call of `f` on `args` has an exponent: `idxPowC`, or its ghost slot's (`ghostArg`). -/
noncomputable def idxPowG (Cf : CFun) (f : String) (args : List V) (i : CIdx) : Bool :=
  idxPowC Cf args i || ghostArg Cf f args i

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

/-- **A stride-one run `[0, S·n)` of constant bounds made of `S` runs of the mode signature** `G` of stride `S`, its
strands (`strand`), each a run of constant bounds over the slots below `np`. -/
def runCov (G : Mode.Sig) (np : ℕ) (q : CRun) : Bool :=
  match q.lo, q.hi with
  | .num 0, .num m => Nat.beq q.stride 1 && decide (m < 2 ^ 62) && G.preR.any fun r0 ↦ decide (0 < r0.S) && Nat.beq (m % r0.S) 0 &&
      (List.range r0.S).all fun i ↦ G.preR.any fun r ↦ monoS G np false r.q && rngIs r (strand q r0.S (m / r0.S) i)
  | _, _ => false

/-- **Cells among the mode preconditions, in order**: `cs` a subsequence of the translations of `ms` over
slots below `np` (`monoS`, `monoIs`), checked in one pass. -/
def preSub (G : Mode.Sig) (np : ℕ) : List CCell → List Mode.Mono → Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: cs, m :: ms => bif monoS G np false m && monoIs m c then preSub G np cs ms else preSub G np (c :: cs) ms

/-- **Each cell a mode precondition's or a point of a mode run's**: in one pass when the cells come in the mode
preconditions' order (`preSub`), else cell by cell. -/
def preCov (G : Mode.Sig) (np : ℕ) (cs : List CCell) : Bool :=
  preSub G np cs G.pre || cs.all fun c ↦ G.pre.any (fun m ↦ monoS G np false m && monoIs m c) ||
    G.preR.any fun r ↦ monoS G np false r.q && ptIn c r

theorem preSub_spec {G : Mode.Sig} {np : ℕ} : ∀ {cs : List CCell} {ms : List Mode.Mono},
    preSub G np cs ms = true → ∀ c ∈ cs, ms.any (fun m ↦ monoS G np false m && monoIs m c) = true
  | [], _, _, c, hc => by cases hc
  | _ :: _, [], h, _, _ => by simp [preSub] at h
  | c0 :: cs, m :: ms, h, c, hc => by
    unfold preSub at h
    cases hm : (monoS G np false m && monoIs m c0)
    · rw [hm, Bool.cond_false] at h
      exact List.any_cons ▸ Bool.or_eq_true_iff.mpr (Or.inr (preSub_spec h c hc))
    · rw [hm, Bool.cond_true] at h
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [hm]
      · exact List.any_cons ▸ Bool.or_eq_true_iff.mpr (Or.inr (preSub_spec h c hc))

theorem preCov_spec {G : Mode.Sig} {np : ℕ} {cs : List CCell} (h : preCov G np cs = true) :
    ∀ c ∈ cs, (G.pre.any (fun m ↦ monoS G np false m && monoIs m c) ||
      G.preR.any fun r ↦ monoS G np false r.q && ptIn c r) = true := by
  intro c hc
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [preSub_spec h c hc, Bool.true_or]
  · exact List.all_eq_true.mp h c hc

/-- A residual `e(n) < m`, `m + c ≤ N + 1`, `m < 2^62`. -/
def resBnd (n c N : ℕ) : CRes → Bool
  | .lt (.val n') (.num m) => Nat.beq n' n && decide (m + c ≤ N + 1) && decide (m < capE)
  | _ => false

/-- **A guaranteed run up to a word past a parameter, inside one up to a constant** (`postRB`): `r`'s upper bound
the exponent of the word at `[q]·g^d` (the value `n` a top-level `load` reads there, `hpVal`) plus `c`, a residual
`e(n) < m`, and a guarantee of `r`'s product, lower bound, stride and offset up to `g^N`, `m + c ≤ N + 1`. -/
noncomputable def postRB (G : Mode.Sig) (Cf : CFun) (np : ℕ) (r : Mode.Rng) : Bool :=
  match r.hi with
  | .ex (.hp q d) c => monoOkP G np ⟨0, 0, [(.hp q d, 1)]⟩ &&
      match hpVal Cf.fn.body (q - 2) d with
      | some n => G.postR.any fun r2 ↦ decide (r2.q = r.q) && decide (r2.lo = r.lo) && decide (r2.S = r.S) &&
          decide (r2.d = r.d) && match r2.hi with
          | .num N => Cf.H.res.any (resBnd n c N)
          | .ex _ _ => false
      | none => false
  | _ => false

/-- `main`'s own precondition at a constant cell `g^o`, `o` an entry cell of its frame `0`. -/
def mainPre (Cf : CFun) (G : Mode.Sig) (c : CCell) : Bool :=
  Cf.X.main && c.bases.isEmpty && G.entry.contains c.off

/-- **The signature callers know, translated**: no self frame pointer, termination fact, loop run,
pointer fact or order, no more ghost slots than linked cells; its heap preconditions each a cell or run of the
signature's (`main`'s also its entry cells, `mainPre`; over parameters; a run also the jump table's `jt`, over the caller's cells linked to parameters or ghost
slots, `rngLIs`, or a stride-one run the signature's runs make up, `runCov`);
each heap cell and run it promises (over parameters and returned words) among the promised cells
`Cf.posts` or the heap signature's runs, or (`postIn`, `postRIn`) over parameters, returned values and
words a top-level `load` reads, among `heapOk`'s promised cells. -/
noncomputable def sigOk (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) (jt : Mode.Rng) : Bool :=
  G.self.isNone && G.term.isEmpty && G.postL.isEmpty &&
    (G.postP.all fun r ↦ monoR G np nr (rngM r.1) && expI G Cf.H.res np (np + nr) r.1.lo &&
      expI G Cf.H.res np (np + nr) r.1.hi &&
      Cf.H.sig.postPR.any (prunIs r ·) && Cf.H.sig.postR.any (rngXIs r.1 ·)) && G.postLP.isEmpty &&
    G.postT.isEmpty && G.postC.isEmpty && Cf.H.sig.preP.all (hpAll G np G.pre) &&
    (Cf.H.sig.prePR.all fun p ↦ G.preP.any fun r ↦ monoS G np false (rngM r.1) && prunIs r p) &&
    preCov G np (Cf.H.sig.pre.filter fun c ↦ !mainPre Cf G c) &&
    Cf.H.sig.preR.all (fun q ↦ ((jt :: G.preR).any fun r ↦ (monoS G np false r.q && rngIs r q) ||
      (monoS G np false (rngM r) && rngXIs r q) || ((rngM r).bs.all (baseS Cf.gl (gpOf np Cf.H.sig.gw) np ·.1) &&
        rngLIs Cf.gl (gpOf np Cf.H.sig.gw) r q)) || runCov G np q ||
      G.pre.any fun m ↦ m.bs.all (baseS Cf.gl (gpOf np Cf.H.sig.gw) np ·.1) && ptLIs Cf.gl (gpOf np Cf.H.sig.gw) m q) &&
    G.post.all (fun m ↦ (monoR G np nr m && match monoC m with
      | some c => cellIn c Cf.posts
      | none => false) || postIn Cf.X Cf.fn.body G np (Cf.post.map (·.1)) m ||
      hpIn G np true Cf.H.sig.postP Cf.posts m || postNIn Cf.X Cf.fn.body G np Cf.H.sig m) &&
    (G.postR.all fun r ↦ (monoR G np nr r.q && ((Cf.H.sig.postR.any fun q ↦ rngIs r q) ||
      match monoC r.q, runPts ⟨[], 0⟩ r with
      | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ Cf.posts
      | _, _ => false)) || postRIn Cf.X Cf.fn.body G np (Cf.post.map (·.1)) r ||
      (monoR G np nr (rngM r) && expI G Cf.H.res np (np + nr) r.lo && expI G Cf.H.res np (np + nr) r.hi &&
        Cf.H.sig.postR.any (rngXIs r ·)) || postRB G Cf np r || postRNIn Cf.X Cf.fn.body G np Cf.H r) &&
    Nat.ble Cf.H.sig.ghosts (Cf.gl.length + Cf.H.sig.gw.length) &&
    Cf.H.sig.gw.all fun x ↦ Nat.blt x.2 Cf.H.sig.ghosts && match x.1.bases with
      | [(p, 1)] => Nat.blt p np
      | _ => false

/-- **A callee's returned word's monomial its mode signature promises** (`retV`): returned word `k < nr` at
the callee's frame cell `2 + na + k`, a product over its argument cells that is the cell `c`. -/
def retMIn (G : Mode.Sig) (na nr : ℕ) (p : ℕ × CCell) : Bool :=
  decide (p.1 < nr) && decide (2 + na + p.1 < 2 ^ 28) &&
    G.retV.any fun q ↦ Nat.beq q.1 (2 + na + p.1) && monoS G na false q.2 && monoIs q.2 p.2

/-- Pairs, once each, in order (`acc` reversed, the ones kept so far). -/
def nubP : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | acc, [] => acc.reverse
  | acc, x :: l => nubP (bif acc.contains x then acc else x :: acc) l

/-- A caller's cell's exponent bound (`.hp 1 d`, no offset) as a base. -/
def hpBnd : Mode.Idx → List (Mode.Base × ℕ)
  | .ex (.hp q d) c => bif Nat.beq q 1 && Nat.beq c 0 then [(.hp q d, 1)] else []
  | _ => []

/-- **A callee's pointer bases** (`.hp q d`) its entry runs' products and its entry products but pointer facts
(`hpOf`) name, once each, in order: its ghost slots at a call, ghost `j` the word of `(hpBs G)[j]`: the caller's cell
`d` for `q = 1`, the word at cell `d` past argument `q - 2`'s word otherwise (`hpArgOk`). -/
def hpBs (G : Mode.Sig) : List (ℕ × ℕ) :=
  nubP [] (((G.preR.flatMap fun r ↦ r.q.bs) ++ (G.pre.filter fun m ↦ (hpOf m).isNone).flatMap (·.bs) ++
    G.preR.flatMap fun r ↦ hpBnd r.lo ++ hpBnd r.hi).filterMap
    fun b ↦ match b.1 with
    | .hp q d => some (q, d)
    | .fr _ => none)

/-- **The caller's cells among a callee's ghost slots** past its `n` arguments: `(d, n + j, 0)` for `(1, d)`. -/
def glOfs : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ × ℕ)
  | _, [] => []
  | n, (q, d) :: l => bif Nat.beq q 1 then (d, n, 0) :: glOfs (n + 1) l else glOfs (n + 1) l

/-- **The words at arguments' cells among a callee's ghost slots** past its `n` arguments: `((q, d), n + j)` for
`q ≠ 1`. -/
def gpOfs : ℕ → List (ℕ × ℕ) → List ((ℕ × ℕ) × ℕ)
  | _, [] => []
  | n, (q, d) :: l => bif Nat.beq q 1 then gpOfs (n + 1) l else ((q, d), n) :: gpOfs (n + 1) l

/-- **A callee's base at a call**: an argument's entry cell `2 + b`, `b < na`, or a pointer base of `ps` (past an
argument's entry cell for `q ≠ 1`). -/
def baseC1 (G : Mode.Sig) (na : ℕ) (ps : List (ℕ × ℕ)) : Mode.Base → Bool
  | .fr o => decide (2 ≤ o) && decide (o - 2 < na) && decide (o < 2 ^ 28) && G.entry.contains o
  | .hp q d => ps.contains (q, d) && (Nat.beq q 1 ||
      (decide (2 ≤ q) && decide (q - 2 < na) && decide (q < 2 ^ 28) && G.entry.contains q))

/-- A bound a caller's cell's exponent (`.hp 1 d`, no offset). -/
def isHp1 : Mode.Idx → Bool
  | .ex (.hp q _) c => Nat.beq q 1 && Nat.beq c 0
  | _ => false

/-- A run bound: a constant or a frame cell's exponent (`idxX`), or a caller's cell's (`isHp1`). -/
def bndX (i : Mode.Idx) : Bool := (idxX i).isSome || isHp1 i

/-- A run whose bounds are constants, frame cells' exponents (`idxX`) or caller's cells' (`isHp1`). -/
def boundsX (r : Mode.Rng) : Bool := bndX r.lo && bndX r.hi

/-- A run of constant bounds. -/
def numB (r : Mode.Rng) : Bool :=
  match r.lo, r.hi with
  | .num _, .num _ => true
  | _, _ => false

/-- **A run's next point**: past a run whose upper bound is slot `b`'s exponent, the cell `base·[b]^S`. -/
def nextPt (q : CRun) : Option CCell :=
  match q.hi with
  | .val b => some (q.base.mul ⟨[(b, q.stride)], 0⟩)
  | _ => none

/-- **A run extended by its next point**: `q` the translation of `r` (`rngX`) with its upper bound `[b]` raised to
`[b]·g`, the cell past `r`'s end (`nextPt`) a product of `ms` over the slots below `n`. -/
def rngXExt (G : Mode.Sig) (n : ℕ) (ms : List Mode.Mono) (r : Mode.Rng) (q : CRun) : Bool :=
  match rngX r with
  | some q' => match q'.hi, nextPt q' with
    | .val b, some c => decide (q = ⟨q'.base, q'.stride, q'.lo, .mono ⟨[(b, 1)], 1⟩⟩) &&
        ms.any fun m ↦ monoS G n false m && monoIs m c
    | _, _ => false
  | none => false

/-- A frame cell base. -/
def isFrB : Mode.Base → Bool
  | .fr _ => true
  | .hp _ _ => false

/-- **A product's one pointer base**: `.hp q d` of power one among frame cell bases, and the bases without it. -/
def hpSplit : List (Mode.Base × ℕ) → Option ((ℕ × ℕ) × List (Mode.Base × ℕ))
  | [] => none
  | (.hp q d, e) :: bs => bif Nat.beq e 1 && bs.all (fun b ↦ isFrB b.1) then some ((q, d), bs) else none
  | (.fr o, e) :: bs => (hpSplit bs).map fun p ↦ (p.1, (.fr o, e) :: p.2)

/-- **A run over one pointer base as a run at its cell's word** (`postQ`): `r`'s product over frame cells and the
word at `[q]·g^d` (`hpSplit`), the cell `⟨[(q - 2, 1)], d⟩` and the run `rngX` gives of `r` without that base. -/
def rngQ (r : Mode.Rng) : Option (CCell × CRun) :=
  match hpSplit r.q.bs with
  | some ((q, d), bs) => bif decide (2 ≤ q) then
      (rngX ⟨⟨r.q.fp, r.q.k, bs⟩, r.lo, r.hi, r.S, r.d⟩).map fun c ↦ (⟨[(q - 2, 1)], d⟩, c) else none
  | none => none

/-- **A callee's run at a cell's word** (`postQ`): one of its guaranteed runs over one pointer base (`rngQ`), its
frame cells (the pointer's among them) slots below `n`. -/
def rngQIn (G : Mode.Sig) (n : ℕ) (p : CCell × CRun) : Bool :=
  G.postR.any fun r ↦ decide (rngQ r = some p) && match hpSplit r.q.bs with
    | some ((q, _), bs) => monoS G n false ⟨0, 0, (.fr q, 1) :: (bs ++ idxB r.lo ++ idxB r.hi)⟩
    | none => false

/-- A run of `[[q]·g^d]` alone (no frame address, power one), of constant bounds `[lo, hi)`: `(q, d, lo, hi)`. -/
def hpRunOf (r : Mode.Rng) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match r.q.fp, r.q.bs, r.lo, r.hi with
  | 0, [(.hp q d, 1)], .num lo, .num hi => some (q, d, lo, hi)
  | _, _, _, _ => none

theorem hpRunOf_spec {r : Mode.Rng} {q d lo hi : ℕ} (h : hpRunOf r = some (q, d, lo, hi)) :
    r.q = ⟨0, r.q.k, [(.hp q d, 1)]⟩ ∧ r.lo = .num lo ∧ r.hi = .num hi := by
  obtain ⟨⟨fp, k, bs⟩, lo0, hi0, S, d0⟩ := r
  unfold hpRunOf at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp_all
  · cases h

/-- **A pointer fact a guaranteed run over one pointer base gives**: a run of `[[q]·g^d]` alone, of constant bounds
`[lo, hi)`, each offset of `p` one of its cells `k + d' + S·j`, `p`'s cell `⟨[(q - 2, 1)], d⟩` over a slot below
`n`. -/
def hpRunIn (G : Mode.Sig) (n : ℕ) (p : CCell × List ℕ) : Bool :=
  G.postR.any fun r ↦ match hpRunOf r with
    | some (q, d, lo, hi) => hpSlot G n false q && p.1.beq ⟨[(q - 2, 1)], d⟩ &&
        p.2.all fun o ↦ (List.range (hi - lo)).any fun t ↦ Nat.beq o (r.q.k + r.d + r.S * (lo + t))
    | none => false

/-- **Each of `hs` satisfies `p` with some element of `gs`**, the element at its own position tried first: linear in
the lists' lengths when they correspond position by position (a callee's heap guarantees, translated in order from its
mode signature's). -/
def allAnyPos {α β : Type} (p : α → β → Bool) (gs : List α) (hs : List β) : Bool :=
  go 0 hs
where
  /-- From position `i`. -/
  go (i : ℕ) : List β → Bool
    | [] => true
    | q :: qs => ((gs[i]?).any (p · q) || gs.any (p · q)) && go (i + 1) qs

theorem allAnyPos_all {α β : Type} {p : α → β → Bool} {gs : List α} {hs : List β} (h : allAnyPos p gs hs = true) :
    ∀ q ∈ hs, gs.any (p · q) = true := by
  suffices ∀ (i : ℕ) (hs : List β), allAnyPos.go p gs i hs = true → ∀ q ∈ hs, gs.any (p · q) = true from
    this 0 hs h
  intro i hs
  induction hs generalizing i with
  | nil => simp
  | cons q qs ih =>
    intro h x hx
    simp only [allAnyPos.go, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · rcases h1 with h1 | h1
      · cases hg : gs[i]? with
        | none => simp [hg] at h1
        | some r =>
          simp only [hg, Option.any_some] at h1
          exact List.any_eq_true.mpr ⟨r, List.mem_of_getElem? hg, h1⟩
      · exact h1
    · exact ih (i + 1) h2 x hx

/-- **A callee's mode signature `G` holds of its heap signature `h`** at a call of `na` arguments
and `nr` returned words: its self frame pointer cell (a loop's) small, its header cells entry cells;
each of its preconditions over the arguments' entry cells one of `h`'s (a run `h`'s run or its
points `h`'s cells; a run of constant bounds over its caller's cells too, `h`'s over its ghost slots, `hp1s`);
each guarantee of `h` one of `G`'s (cells or points over the arguments and returned words, runs `G`'s or its
loop's, or one of them extended by its next point, `rngXExt`; a run at a cell's word one of `G`'s over one pointer base,
`rngQIn`; a pointer fact one such of constant bounds gives, `hpRunIn`); each returned word's monomial of `h` one `G` promises
(`retMIn`); `h` with a ghost slot per caller's cell. -/
def fitB (G : Mode.Sig) (h : HSig) (na nr : ℕ) : Bool :=
  (match G.self with
    | some o => decide (o < 2 ^ 28)
    | none => true) &&
    (G.preP.all fun r ↦ monoS G na true (rngM r.1) && h.prePR.any (prunIs r ·) && h.preR.any (rngXIs r.1 ·)) &&
    G.entry.contains 0 && G.entry.contains 1 &&
    h.postP.all (fun p ↦ hpAll G (na + nr) G.post p || hpRunIn G (na + nr) p) &&
    (h.postPR.all fun p ↦ (G.postP ++ G.postLP).any fun r ↦ monoS G (na + nr) false (rngM r.1) && prunIs r p) &&
    (h.retM.all (retMIn G na nr) && h.postQ.all (rngQIn G (na + nr))) &&
    G.pre.all (fun m ↦ (monoS G na true m && match monoC m with
      | some c => cellIn c h.pre
      | none => false) || hpIn G na true h.preP h.pre m ||
      (m.bs.all (baseC1 G na (hpBs G) ·.1) && h.preR.any (ptLIs (glOfs na (hpBs G)) (gpOfs na (hpBs G)) m ·))) &&
    (hpBs G).all (fun p ↦ Nat.beq p.1 1 || cellIn ⟨[(p.1 - 2, 1)], p.2⟩ h.pre) &&
    G.preR.all (fun r ↦ (monoS G na true r.q && ((h.preR.any fun q ↦ rngIs r q) ||
      match monoC r.q, runPts ⟨[], 0⟩ r with
      | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ h.pre
      | _, _ => false)) || (monoS G na true (rngM r) && h.preR.any (rngXIs r ·)) ||
      (numB r && r.q.bs.all (baseC1 G na (hpBs G) ·.1) &&
        h.preR.any (rngLIs (glOfs na (hpBs G)) (gpOfs na (hpBs G)) r ·)) ||
      (boundsX r && (rngM r).bs.all (baseC1 G na (hpBs G) ·.1) &&
        h.preR.any (rngLIs (glOfs na (hpBs G)) (gpOfs na (hpBs G)) r ·))) &&
    h.post.all (fun c ↦ G.post.any (fun m ↦ monoS G (na + nr) false m && monoIs m c) ||
      G.postR.any fun r ↦ monoS G (na + nr) false r.q && ptIn c r) &&
    allAnyPos (fun r q ↦ (monoS G (na + nr) false r.q && rngIs r q) ||
      (monoS G (na + nr) false (rngM r) && rngXIs r q) ||
      (monoS G (na + nr) false (rngM r) && rngXExt G (na + nr) G.post r q)) (G.postR ++ G.postL) h.postR &&
    Nat.beq h.ghosts (hpBs G).length

/-- The first top-level `const`, `copy` or `mul` defining value `n`, before any `ret`. -/
def defOf : List Stmt → ℕ → Option Atom
  | [], _ => none
  | .ret _ :: _, _ => none
  | .atom a :: ss, n => match a with
    | .const d _ | .copy d _ | .mul d _ _ => bif (vnum d).any (Nat.beq · n) then some a else defOf ss n
    | _ => defOf ss n
  | _ :: ss, n => defOf ss n

/-- **A value's word as a monomial** through the body's top-level atoms, `k` deep: a `const` power of `g`, a
`copy`'s source's, a `mul`'s factors' product, else the value itself. -/
noncomputable def wordNf (pows : Exec.PowTree) (body : List Stmt) : ℕ → ℕ → CCell
  | 0, n => ⟨[(n, 1)], 0⟩
  | k + 1, n => match defOf body n with
    | some (.const _ c) => match powOf pows c with
      | some e => ⟨[], e⟩
      | none => ⟨[(n, 1)], 0⟩
    | some (.copy _ s) => match vnum s with
      | some m => wordNf pows body k m
      | none => ⟨[(n, 1)], 0⟩
    | some (.mul _ a b) => match vnum a, vnum b with
      | some x, some y => (wordNf pows body k x).mul (wordNf pows body k y)
      | _, _ => ⟨[(n, 1)], 0⟩
    | _ => ⟨[(n, 1)], 0⟩

/-- How deep `wordNf` follows the atoms. -/
def wordFuel : ℕ := 4

/-- How deep `hpValS` follows a pointer's word. -/
def baseFuel : ℕ := 16

/-- **The value a top-level `load` reads at a pointer's cell `d`**: `hpVal`, or, the pointer's word the monomial
`[b]·g^k` (`wordNf`, `baseFuel` deep), the value one reads at `b`'s cell `d + k`. -/
noncomputable def hpValS (pows : Exec.PowTree) (body : List Stmt) (a d : ℕ) : Option ℕ :=
  match hpVal body a d with
  | some n => some n
  | none => match wordNf pows body baseFuel a with
    | ⟨[(b, 1)], k⟩ => hpVal body b (d + k)
    | _ => none

/-- **A callee's ghost word at a call on the argument values `as`**, of its pointer base `(q, d)`: the caller's
parameter at its cell `d` for `q = 1`, else the value a top-level `load` names at cell `d` past argument `q - 2`'s word
(`hpValS`), as its word's monomial (`wordNf`). -/
noncomputable def ghostW (Cf : CFun) (as : List ℕ) (p : ℕ × ℕ) : Option CCell :=
  bif Nat.beq p.1 1 then some ⟨[(p.2 - 2, 1)], 0⟩ else
    (as[p.1 - 2]?).bind fun a ↦ (hpValS Cf.pows Cf.fn.body a p.2).map (wordNf Cf.pows Cf.fn.body wordFuel)

/-- **A callee's ghost words** (`hpBs`): each caller cell `d` an entry cell of a parameter, and each ghost list the
certificate gives the callee `f` (`HCert.gargs`) the words `ghostW` names. -/
noncomputable def hpArgOk (Cf : CFun) (G : Mode.Sig) (f : String) : Bool :=
  (hpBs G).all (fun p ↦ !Nat.beq p.1 1 || (decide (2 ≤ p.2) && decide (p.2 - 2 < Cf.fn.params.length) &&
    decide (p.2 < 2 ^ 28) && Cf.frame.sig.entry.contains p.2)) &&
  Cf.H.gargs.all fun x ↦ !(x.1 == f) || decide (x.2.2.map some = (hpBs G).map (ghostW Cf x.2.1))

/-- **A call's callee** `f` at a site of `na` arguments and `nr` returned words, of mode signature `G`: a
callee whose contract is its heap signature's (`hcs`), its counts the site's, its header cells entry cells; or
its mode signature holding of its heap signature (`fitB`). -/
noncomputable def callOkC (Cf : CFun) (G : Mode.Sig) (f : String) (na nr : ℕ) : Bool :=
  match Cf.hcs.lookup f with
  | some p => decide (p = (na, nr)) && G.entry.contains 0 && G.entry.contains 1
  | none => fitB G (Cf.sigOf f) na nr && hpArgOk Cf G f

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

/-- A call of `g` on `args`: not of `f`, a heap contract's callee's heap signature naming no ghost, and no returned word's
monomial, word at return or equation unless its contract is its heap signature's (`hcs`: its guarantees then
give them at the call's resumption), its runs' bounds having exponents at the call (`idxPowC`). -/
noncomputable def callChk (Cf : CFun) (g : String) (args : List V) : Bool :=
  !(g == Cf.fn.name) && ((Cf.hcs.lookup g).isSome || (Cf.sigOf g).retM.isEmpty && (Cf.sigOf g).postV.isEmpty &&
    (Cf.sigOf g).retEq.isEmpty) && ((Cf.hcs.lookup g).isNone || Nat.beq (Cf.sigOf g).ghosts 0) &&
    ((Cf.sigOf g).preR.all fun q ↦ idxPowC Cf args q.lo && idxPowC Cf args q.hi) &&
    (Cf.sigOf g).prePR.all fun p ↦ idxPowC Cf args p.1.lo && idxPowC Cf args p.1.hi

/-- **A call of `g` on `args` in a body checked whole** (`callsB`): `callChk`, a callee on a mode contract
also naming returned words' monomials (its mode signature's `retV`, `fitB`'s `retMIn`). -/
noncomputable def callChkM (Cf : CFun) (g : String) (args : List V) : Bool :=
  !(g == Cf.fn.name) && ((Cf.hcs.lookup g).isSome || (Cf.sigOf g).postV.isEmpty &&
    (Cf.sigOf g).retEq.isEmpty) && ((Cf.hcs.lookup g).isNone || Nat.beq (Cf.sigOf g).ghosts 0) &&
    ((Cf.sigOf g).preR.all fun q ↦ idxPowG Cf g args q.lo && idxPowG Cf g args q.hi) &&
    (Cf.sigOf g).prePR.all fun p ↦ idxPowG Cf g args p.1.lo && idxPowG Cf g args p.1.hi

/-- A checked call of a callee on a mode contract gives nothing beyond its writes. -/
theorem callChk_evM {Cf : CFun} {g : String} {args rets : List V} (h : callChk Cf g args = true)
    (hl : Cf.hcs.lookup g = none) (rd : Reader) (σ : Val) : EvM Cf.sigOf rd σ (.call g args rets) := by
  simp only [callChk, hl, Option.isSome_none, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨-, ⟨⟨h1, h2⟩, h3⟩⟩, -⟩, -⟩, -⟩ := h
  refine ⟨fun k c hkc ↦ ?_, fun i m him ↦ ?_, fun p hp ↦ ?_⟩
  · rw [h1] at hkc; cases hkc
  · rw [h2] at him; cases him
  · rw [h3] at hp; cases hp

/-- **Each call of the body** (`call`, `callIf`, each callee of a `dispatch`) checked by `callChk`; a
dispatch's callees those `dsp` lists at each of its sites. -/
noncomputable def callsB (Cf : CFun) : Bool :=
  (stmtsOf Cf.fn.body).all fun s ↦ match s with
    | .call g args _ => callChkM Cf g args
    | .callIf _ g args => callChkM Cf g args
    | .dispatch _ fs args rets => fs.all (callChkM Cf · args) &&
        Cf.dsp.all fun p ↦ (Cf.X.siteAt p.1 args rets).isNone || p.2 == fs
    | _ => true

/-- **A dispatch checked as `callsB` does**: its callees by `callChkM`, the ones `dsp` lists at its sites. -/
noncomputable def dspB (Cf : CFun) : Stmt → Bool
  | .dispatch _ fs args rets => fs.all (callChkM Cf · args) &&
      Cf.dsp.all fun p ↦ (Cf.X.siteAt p.1 args rets).isNone || p.2 == fs
  | _ => true

theorem dspB_of_callsB {Cf : CFun} (h : callsB Cf = true) : (stmtsOf Cf.fn.body).all (dspB Cf) = true :=
  List.all_eq_true.mpr fun s hs ↦ by
    have := List.all_eq_true.mp h s hs
    cases s <;> simp_all [dspB]

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
(`heapOk`), or each named by the heap signature's `retM`. -/
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

/-- A dispatch. -/
def isDsp : Stmt → Bool
  | .dispatch .. => true
  | _ => false

/-- A top-level statement: a return, a call, or one with no `ret` and no dispatch in it (calls and
conditional calls may sit in its branches). -/
def topOk : Stmt → Bool
  | .ret _ => true
  | .call .. => true
  | .dispatch .. => true
  | s => Core.Stmt.noRet s && !(Bridge.stmtsSub s).any isDsp

/-- **A body the core route takes**: its statements, nested ones included, atoms, branches, `match`es
and returns, no branch or arm returning. -/
def bodyCore (body : List Stmt) : Bool :=
  (stmtsOf body).all ctrlOk && body.all topOk

/-- The `match`es of a body, nested ones included: selector number, number of arms. -/
def matchLens (body : List Stmt) : List (ℕ × ℕ) :=
  (stmtsOf body).filterMap fun s ↦ match s with
    | .match_ x arms => some (x.idx, arms.length)
    | _ => none

/-- The body's `dispatch`es: selector, callee count, arguments' and returned values' indices. -/
def dspLens (body : List Stmt) : List (V × ℕ × List ℕ × List ℕ) :=
  (stmtsOf body).filterMap fun s ↦ match s with
    | .dispatch x fs args rets => some (x, fs.length, args.map (·.idx), rets.map (·.idx))
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

/-- Slots `b + j`, `j < n`, lie in the environment's jump table. -/
noncomputable def slotsIn (E : Mode.Env) (b n : ℕ) : Bool :=
  (List.range n).all fun j ↦ decide (E.jtLo ≤ b + j) && decide (b + j < E.jtHi) && (E.jt.get (b + j)).isSome

/-- A dispatch's table read `DEREF o1 o2 o3` before its `JUMP` through call site `s`: every `dispatch` at
that site (`dl`, `dspLens`) on the value at the pointer cell `o1`, its callees' slots from base `o2` in the
environment's jump table. -/
noncomputable def dspRd (Cf : CFun) (E : Mode.Env) (dl : List (V × ℕ × List ℕ × List ℕ)) (s : B2C.Site)
    (o1 o2 : ℕ) : Bool :=
  dl.all fun q ↦ !(q.2.2.1 == s.args && q.2.2.2 == s.rets) || (Nat.beq (Cf.X.locAt q.1.idx) o1 && slotsIn E o2 q.2.1)

/-- From the instructions `code`: each `DEREF` reading the jump table (`jtd`) is followed by its table
jump, through its word cell, on no constant `0` cell and no pc, and each slot of its table that a
`match` on its selector has lies in the environment's jump table; or, its word cell no table's, by its
dispatch's `JUMP` through that cell (`dspRd`). -/
noncomputable def jtdGo (Cf : CFun) (E : Mode.Env) (ml : List (ℕ × ℕ)) (dl : List (V × ℕ × List ℕ × List ℕ)) :
    List OffsetInstruction → Bool
  | [] => true
  | ins :: code => (match ins with
      | .deref o1 o2 o3 .cell => !jtd Cf.X o1 o2 o3 || match code with
        | .jump oc od of :: _ => Nat.beq od o3 && !Cf.X.zeroAt oc && (Cf.X.pcAt o3).isNone && !Nat.beq o3 0 &&
            match Check.getF Cf.X.arms o3 with
            | some a => ml.all fun p ↦ !Nat.beq p.1 a.1 || slotsIn E a.2 p.2
            | none => match Check.getF Cf.X.sites of with
              | some s => Nat.beq s.tgt o3 && dspRd Cf E dl s o1 o2
              | none => false
        | _ => false
      | _ => true) && jtdGo Cf E ml dl code

/-- **The jump table's reads**: `jtdGo` over the code. -/
noncomputable def jtdOk (Cf : CFun) (E : Mode.Env) (code : List OffsetInstruction) : Bool :=
  Exec.listSeq (matchLens Cf.fn.body) fun ml ↦ Exec.listSeq (dspLens Cf.fn.body) fun dl ↦ jtdGo Cf E ml dl code

/-- An empty trie. -/
def trieNil {α : Type} : Exec.Trie α → Bool
  | .nil => true
  | _ => false

/-- No callee's signature at an offset of the function past its entry. -/
def sigsOut {α : Type} (sigs : Exec.Trie α) (entry len : ℕ) : Bool :=
  (List.range len).all fun o ↦ Nat.beq o 0 || (sigs.get (entry + o)).isNone

/-- `main`'s code before its halting pc (any other function: no condition). -/
def mainOk (Cf : CFun) : Bool :=
  !Cf.X.main || decide (Cf.frame.entry + Cf.frame.len ≤ Cf.X.halt)

/-- **The shape the core route takes**: a body of atoms, branches, `match`es, calls at its top level
and returns, one return count (`bodyCore`, `retsN`), `main`'s code before its halting pc (`mainOk`), its frame
walk's `main` its own (`fpOne`), no frame cell `1` its frame pointer's,
no pc at cell `0`, the walk's tables the `match`es' arms, no callee inside the function,
small entry cells. -/
noncomputable def shapeOk (Cf : CFun) (code : List OffsetInstruction) : Bool :=
  bodyCore Cf.fn.body && mainOk Cf && !Cf.X.selfAt 1 && (Cf.X.pcAt 0).isNone && retsN (retN Cf.fn.body) (stmtsOf Cf.fn.body) &&
    tgtOk Cf code && sigsOut Cf.frame.sigs Cf.frame.entry Cf.frame.len &&
    Cf.frame.F.fpOne == Cf.X.main && Cf.frame.sig.entry.all (fun o ↦ decide (o + 1 < 2 ^ Exec.envDepth)) &&
    decide (Cf.frame.entry + Cf.frame.len ≤ 2 ^ 30) && Mode.pcsIncr Cf.frame.hints

/-- `shapeOk` but for its two longest passes (`bodyCore`, `tgtOk`), which a long body checks apart. -/
noncomputable def shapeRest (Cf : CFun) : Bool :=
  mainOk Cf && !Cf.X.selfAt 1 && (Cf.X.pcAt 0).isNone && retsN (retN Cf.fn.body) (stmtsOf Cf.fn.body) &&
    sigsOut Cf.frame.sigs Cf.frame.entry Cf.frame.len &&
    Cf.frame.F.fpOne == Cf.X.main && Cf.frame.sig.entry.all (fun o ↦ decide (o + 1 < 2 ^ Exec.envDepth)) &&
    decide (Cf.frame.entry + Cf.frame.len ≤ 2 ^ 30) && Mode.pcsIncr Cf.frame.hints

theorem shapeOk_of {Cf : CFun} {code : List OffsetInstruction} (hb : bodyCore Cf.fn.body = true)
    (ht : tgtOk Cf code = true) (hr : shapeRest Cf = true) : shapeOk Cf code = true := by
  simp only [shapeRest, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h8⟩, h9⟩, h10⟩ := hr
  simp only [shapeOk, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, h1⟩, h2⟩, h3⟩, h4⟩, ht⟩, h5⟩, h6⟩, h8⟩, h9⟩, h10⟩

/-- **The frame walk's residual divisors** (`FFun.nzr`): at each offset, each a frame cell the walk's state there
has written and the mode certificate's residuals there (`res`) say nonzero. -/
noncomputable def nzrOk (Cf : CFun) (res : Exec.Trie (List Mode.Res)) (code : List OffsetInstruction) : Bool :=
  (List.range code.length).all fun i ↦ match Cf.frame.nzr.get i with
    | none => true
    | some os => match retSt Cf.frame code i with
      | some A => os.all fun o ↦ (A.w.get o).isSome && ((res.get i).getD []).contains (.nz o)
      | none => false

/-- A value an atom of the body defines. -/
def dstIn (body : List Stmt) (v : V) : Bool :=
  (stmtsOf body).any fun s ↦ match s with
    | .atom a => (atomDst a).contains v
    | _ => false

/-- **A frame run's cells at a return state `A`**: from its first value's cell `c` on, each cell `c + k` whose value an
atom of the body defines is written, and each cell `c + i` past the run the certificate's frame run cells `fas` list
(`(kp, i)`, its pointer `V.n kp`). -/
noncomputable def faRetAt (X : Bridge.AlignCtx) (body : List Stmt) (fas : List (ℕ × ℕ)) (A : FSt) : Stmt → Bool
  | .atom (.frameAddr p (r :: rs)) => ((List.range (rs.length + 1)).all fun k ↦
      !(match (r :: rs)[k]? with
        | some v => dstIn body v
        | none => false) || (A.w.get (X.locAt r.idx + k)).isSome) &&
      fas.all fun q ↦ !(decide (p = V.n q.1) && Nat.ble (rs.length + 1) q.2) || (A.w.get (X.locAt r.idx + q.2)).isSome
  | _ => true

/-- **The frame run cells written at every return** (`faNeed`): at each return offset, the walk's state there
(`retSt`) has them (`faRetAt`). -/
noncomputable def faRetOk (Cf : CFun) (code : List OffsetInstruction) : Bool :=
  !faNeed Cf || (List.range code.length).all fun i ↦ match code[i]? with
    | some (.jump _ 0 1) => match retSt Cf.frame code i with
      | some A => (stmtsOf Cf.fn.body).all (faRetAt Cf.X Cf.fn.body Cf.H.fas A)
      | none => false
    | _ => true

/-- **The heap check of a function on the core route**: the check without calls (`heapOk`, `postOk`, straight
line, its promised cells over parameters), or the check with calls (`heapOkC`, at its callees'
signatures `Cf.sigOf`, no termination fact, no callee's returned word's monomial; its residuals hold at
the honest valuations, `HonF.res`). -/
inductive HeapK (Cf : CFun) : Prop
  | m1 : heapOk Cf.pows (fun _ ↦ .empty) Cf.fn Cf.H = true → postOk Cf.pows Cf.H Cf.post Cf.fn.body = true →
      ((stmtsOf Cf.fn.body).all (fun s ↦ !isCall s) && Cf.H.sig.postP.isEmpty && Cf.H.sig.postPR.isEmpty &&
        Cf.H.sig.postQ.isEmpty && Cf.H.sig.postN.isEmpty && Cf.H.sig.postRN.isEmpty) = true →
      Cf.H.sig.retM = [] → Cf.H.sig.postV = [] → Cf.H.sig.retEq = [] → HeapK Cf
  | c : heapOkC Cf.pows Cf.sigOf Cf.fn Cf.H = true → Cf.H.sig.term = [] → callsB Cf = true →
      Cf.post = [] → Cf.H.ders = [] → HeapK Cf

/-- **A heap contract's own signature**: no self frame pointer, termination fact, loop run or ghost slot. -/
def hcOwn (G : Mode.Sig) (Cf : CFun) : Bool :=
  G.self.isNone && G.term.isEmpty && G.postL.isEmpty && G.postLP.isEmpty && Nat.beq Cf.H.sig.ghosts 0

/-- **The own signature's check**: a heap contract's (`hcOwn`), or the mode signature's translation
(`sigOk`). -/
noncomputable def ownOk (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) (jt : Mode.Rng) : Bool :=
  bif Cf.hc then hcOwn G Cf else sigOk G Cf np nr jt

/-! ## Heap contracts -/

/-- **The words of frame `fp`'s cells `2, …, 2 + n - 1`** in the reference. -/
noncomputable def wsAt (img : MemoryImage κ) (fp n : ℕ) : List E := (List.range n).map fun b ↦ (Rd img fp (2 + b)).getD 0

/-- **A core function's heap contract**: its heap signature `h` at the words of its frame's slots in the
reference (`np` parameters, `nr` returned words), its entry and return frame cells `ent`, `ret`: at entry, its
entry cells written and its preconditions; at return, its return cells written, its guarantees and its
returned words' monomials, words and equations. -/
noncomputable def heapCtrL (img : MemoryImage κ) (h : HSig) (ent ret : List ℕ) (np nr : ℕ) : Mode.Ctr where
  pre m fp := (∀ o ∈ ent, m.written (fp + o) = true) ∧
    ∀ y, PreSet img.read h (wsAt img fp np) y → WrK m y
  post m fp := (∀ o ∈ ret, m.written (fp + o) = true) ∧
    (∀ y, PostSet img.read h (wsAt img fp (np + nr)) y → WrK m y) ∧
    RetMOk h (wsAt img fp np) ((wsAt img fp (np + nr)).drop np) ∧ RetVOk img.read h (wsAt img fp (np + nr)) ∧
    RetEqOk h (wsAt img fp (np + nr))
  mono hle h := ⟨fun o ho ↦ written_mono hle (h.1 o ho), fun y hy ↦ (h.2.1 y hy).mono hle, h.2.2⟩

/-- `heapCtrL` at the frame cells of the mode signature `G`. -/
noncomputable def heapCtr (img : MemoryImage κ) (h : HSig) (G : Mode.Sig) (np nr : ℕ) : Mode.Ctr :=
  heapCtrL img h G.entry G.ret np nr

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
  sig : ownOk K.F.sig Cf Cf.fn.params.length (retN Cf.fn.body) (Mode.jtRng K.E) = true
  retv : (Cf.hc || retVOk Cf K.F.sig) = true
  shape : shapeOk Cf K.code = true
  calls : K.code.all (jumpCallOk Cf) = true
  jtd : jtdOk Cf K.E K.code = true
  fsig : Cf.frame.sig = K.F.sig
  fsigs : Cf.frame.sigs = K.E.sigs
  fmain : K.F.main = Cf.X.main
  fhalt : Cf.frame.halt = K.E.halt
  xhalt : Cf.X.halt = K.E.halt
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
  /-- The frame run cells it guarantees written at its returns. -/
  faret : faRetOk Cf K.code = true
  /-- The frame walk's residual divisors among the mode certificate's nonzero residuals. -/
  nzrc : nzrOk Cf K.F.res K.code = true

end

end LeanVM.Guest.CoreMode
