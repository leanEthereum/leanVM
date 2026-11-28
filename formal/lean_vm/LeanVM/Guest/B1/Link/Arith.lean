/-
  LeanVM.Guest.B1.Link.Arith

  The arithmetic of `verify_sub`'s link section: what the guest computes from the link's
  challenges, the index and row points' values and the sent values, as functions of those
  inputs, and the identities equating each with the Statement's term (`verifyLink`'s `let`s).
-/

module

public import LeanVM.Protocol.Link.Skeleton
public import LeanVM.Protocol.Verifier.Deferred
public import LeanVM.Guest.Word
public import LeanVM.Guest.GuestConst
public import LeanVM.Guest.Data.Consts

/-!
# The link's arithmetic

`verify_sub` (`guests/lean_ethereum.py`, from `# ---- the link's challenges ----` through
`# ---- the summand at the end point ----`) computes, between its callees, the quantities
`link_terminal` checks: the index side's claim, the program side (`program`, `frame_program`),
`y_mem`, `x_bc`, `p_fp`, and from the six tables' sent values the pointer coefficient `coef`, the
twelve shift coefficients `shifts`, the certificates' weight `cert_w` and the base terms `base`
(`rest = eq_q[0]·base`). This module states them and the Statement's terms they meet.

**The guest's side** (`gClaim`, `gProgram`, `gYMem`, `gXBc`, `gPFp`, `gCoef`, `gShifts`, `gCertW`,
`gBase`, `gRest`): each a function of its inputs (`LinkIn`: the challenge buffer `chal`, the
slot weights `slot`, the sent values, the split values, `eq(q_point, ·)`, each table's
`table_point` returns and corner, the index side's returns, the fresh coefficients), written over
the guest's generated constants (`Data.arr_PW_*`, `ACC_*`, `PTR_START`, `STATE_*`, `BC_OP_*`,
`WR_*`, `JUMP_IDS`, `FORM_START`, `TERM_*`) as the guest unrolls its loops; a sum's terms may be
grouped otherwise than in the guest's single pass, which changes no value.

**The Statement's side**: `tailLets`, `tailRowSide` and `linkTailR` are `linkTail`'s `let`s
(`LeanVM.Protocol.Link.Skeleton`, `verifyLink`'s from the memory term on), named, and
`LinkTailEq` says `linkTail` is `linkTailR`. `tailIn` gives the guest's inputs at the Statement's
values.

**The identities** (`ClaimIdentity`, `ProgramIdentity`, `XBcIdentity`, `PFpIdentity`,
`YMemIdentity`, `RowIdentity`): the guest's function at `tailIn` is the Statement's term, the
program side at `freshSplit`'s `Split.ofColumns tables splitv`, for every input of the right
lengths.

Every definition on both sides is generic over `LOps`, the operations `+`, `·`, `0`, `1` and the
field's constants: at `E` it is the computation itself, and at the expressions
`LeanVM.Guest.B1.Link.Arith.Ex` it builds the term the kernel normalizes (`Link/Arith/`).
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Protocol.Compile LeanVM.Guest

@[expose] public section

/-! ## The operations -/

/-- What the link's arithmetic uses: `+`, `·`, `0`, `1` and the field's constants. -/
class LOps (α : Type) extends Add α, Mul α, Zero α, One α where
  /-- A constant of the field. -/
  ofE : E → α

instance : LOps E where ofE x := x

section Generic

variable {α : Type} [LOps α]

/-- `Σ` of a list from zero, left to right (`sumE`). -/
def sumL (l : List α) : α := l.foldl (· + ·) 0

/-- `weights[s] += value` (`addAtSlot`). -/
def addAtG (weights : List α) (s : ℕ) (value : α) : List α :=
  weights.set s (weights.getD s 0 + value)

/-- `Form::evaluate` (`Form.evaluate`). -/
def formEvalG (f : Form) (column : ℕ → α) : α :=
  sumL (f.terms.map fun t ↦ t.1.foldl (fun acc i ↦ acc * column i) (LOps.ofE t.2))

/-! ## The guest's constants -/

/-- Entry `i` of a constant array of indices. -/
def ix (a : List (ℕ × ℕ)) (i : ℕ) : ℕ := (a.getD i (0, 0)).1

/-- Entry `i` of a constant array of words, the word its two limbs spell. -/
def wd (a : List (ℕ × ℕ)) (i : ℕ) : α := LOps.ofE (word (a.getD i (0, 0)).1 (a.getD i (0, 0)).2)

/-- The run `a[i] ..< a[i + 1]` of an array of starts. -/
def runOf (a : List (ℕ × ℕ)) (i : ℕ) : List ℕ := List.range' (ix a i) (ix a (i + 1) - ix a i)

/-- `LINK_NO_POS`: no sent value. -/
abbrev noPos : ℕ := guest_const% LINK_NO_POS

/-- The tables. -/
abbrev nTab : ℕ := guest_const% N_TABLES

/-- `N_ACCESSES`, `N_POINTERS`, `N_WORD_READS`, `N_SPLIT_TERMS`, `LINK_MAX_SHIFT`. -/
abbrev nAcc : ℕ := guest_const% N_ACCESSES

abbrev nPtr : ℕ := guest_const% N_POINTERS

abbrev nWr : ℕ := guest_const% N_WORD_READS

abbrev nPw : ℕ := guest_const% N_SPLIT_TERMS

abbrev nShift : ℕ := guest_const% LINK_MAX_SHIFT

/-- `LINK_JUMP_TABLE`. -/
abbrev jumpTab : ℕ := guest_const% LINK_JUMP_TABLE

/-- The offsets in `chal` (`theta = chal`): `gam`, `mu`, `alpha`, `etas`, `eps`. -/
abbrev oGam : ℕ := nTab

abbrev oMu : ℕ := oGam + 5

abbrev oAlpha : ℕ := oMu + nAcc

abbrev oEta : ℕ := oAlpha + guest_const% LOG2_BYTECODE_COLS

abbrev oEps : ℕ := oEta + 2

/-! ## The guest's inputs -/

/-- The values the link section's arithmetic reads: buffers as functions of the index, and the
returns of its callees. -/
structure LinkIn (α : Type) where
  /-- `chal[k]`: `θ_0`, then the packed challenges (`theta`, `gam`, `mu`, `alpha`, `etas`, `eps`
  at the offsets `oGam`, …). -/
  chal : ℕ → α
  /-- `slot[s]`: `eq(α, s)`, `s < 16`. -/
  slot : ℕ → α
  /-- `sent[k]`: the sent values, `k < 80`. -/
  sent : ℕ → α
  /-- `splitv[k]`: the hinted split values, `k < 36`. -/
  splitv : ℕ → α
  /-- `eq_q[EQ_Q_AT + q]`: `eq(q_point, q)`. -/
  eqQ : ℕ → α
  /-- Table `t`'s `table_point` returns `omega`, `act`, `eq_tau`, and its corner
  `corners[2^h_t]`. -/
  omega : ℕ → α
  act : ℕ → α
  eqTau : ℕ → α
  corner : ℕ → α
  /-- `jump_k`, the four fresh coefficients after `cert`. -/
  jump : ℕ → α
  /-- `state_ends`' returns `e0`, `ec`. -/
  e0 : α
  ec : α
  /-- `index_side`'s returns `idx`, `eqzr`, `shz`. -/
  idx : α
  eqzr : α
  shz : α
  /-- `below[g^log_mem]`, `below[g^BYTECODE_LOG]`, `below[1]`. -/
  belowMem : α
  belowBc : α
  eq0R : α
  /-- The memory term `m1`, and the certificate's fresh coefficient `cert`. -/
  m1 : α
  cert : α
  /-- `x_bc`, `p_fp`, `y_mem`, as the row side reads them. -/
  xBc : α
  pFp : α
  yMem : α

namespace LinkIn

variable (v : LinkIn α)

/-- `gs0`, `gs1` (the state's), `gm0`, `gm1`, `gm3` (the address's, the word's, the presence's). -/
def gs0 : α := v.chal oGam

def gs1 : α := v.chal (oGam + 1)

def gm0 : α := v.chal (oGam + 2)

def gm1 : α := v.chal (oGam + 3)

def gm3 : α := v.chal (oGam + 4)

/-- `mu[a]`, `eta_mem`, `eta_bc`, `eps[q]`. -/
def mu (a : ℕ) : α := v.chal (oMu + a)

def etaMem : α := v.chal oEta

def etaBc : α := v.chal (oEta + 1)

def eps (q : ℕ) : α := v.chal (oEps + q)

end LinkIn

/-! ## The guest's computations -/

/-- `link_form(sent, f)`: form `f`'s terms `TERM_COEF·a·b` over the sent values, a missing factor
one. -/
def gForm (sent : ℕ → α) (f : ℕ) : α :=
  sumL ((runOf Data.arr_FORM_START f).map fun j ↦
    if ix Data.arr_TERM_A j = noPos then wd Data.arr_TERM_COEF j
    else if ix Data.arr_TERM_B j = noPos then wd Data.arr_TERM_COEF j * sent (ix Data.arr_TERM_A j)
    else wd Data.arr_TERM_COEF j * sent (ix Data.arr_TERM_A j) * sent (ix Data.arr_TERM_B j))

/-- The index side's claim, `e0·s_init + ec·s_fin`. -/
def gClaim (v : LinkIn α) : α :=
  v.e0 * (1 + v.gs0 + v.gs1) +
    v.ec * (1 + v.gs0 * LOps.ofE (gpowE (2 ^ guest_const% BYTECODE_LOG - 1)) + v.gs1)

/-- The program side, `(program, frame_program)`: the split terms `PW_COEF·w·splitv[PW_COL]`, `w`
by `PW_KIND` (`eta_bc·slot`, or `eta_mem·gm0·mu`, `eta_mem·gm1·mu` at `PW_ARG`), into `program`
or `frame_program` by `PW_FRAME`. -/
def gProgram (v : LinkIn α) : α × α :=
  let em0 := v.etaMem * v.gm0
  let em1 := v.etaMem * v.gm1
  (List.range nPw).foldl (fun (acc : α × α) i ↦
    let pwf : α :=
      if ix Data.arr_PW_KIND i = 0 then v.etaBc * v.slot (ix Data.arr_PW_ARG i)
      else if ix Data.arr_PW_KIND i = 1 then em0 * v.mu (ix Data.arr_PW_ARG i)
      else em1 * v.mu (ix Data.arr_PW_ARG i)
    let pwt := wd Data.arr_PW_COEF i * pwf * v.splitv (ix Data.arr_PW_COL i)
    if ix Data.arr_PW_FRAME i = 0 then (acc.1 + pwt, acc.2) else (acc.1, acc.2 + pwt)) (0, 0)

/-- `y_mem = gm0·idx + gm3·below_mem + gm1·m1`. -/
def gYMem (v : LinkIn α) : α := v.gm0 * v.idx + v.gm3 * v.belowMem + v.gm1 * v.m1

/-- `x_bc = eta_bc·slot[1]·idx + below_bc·(eta_bc·slot[2] + program)`. -/
def gXBc (v : LinkIn α) : α :=
  v.etaBc * v.slot 1 * v.idx + v.belowBc * (v.etaBc * v.slot 2 + (gProgram v).1)

/-- `p_fp = below_bc·frame_program`. -/
def gPFp (v : LinkIn α) : α := v.belowBc * (gProgram v).2

/-- Access `a`'s `mu·gate` (`acc_gm[a]`). -/
def gGate (v : LinkIn α) (a : ℕ) : α :=
  if ix Data.arr_ACC_GATE a = noPos then v.mu a else v.mu a * v.sent (ix Data.arr_ACC_GATE a)

/-- Access `a`'s committed part, `gm0·address + gm3 + gm1·value`. -/
def gAccess (v : LinkIn α) (a : ℕ) : α :=
  v.gm0 * gForm v.sent (ix Data.arr_ACC_ADDR a) + v.gm3 + v.gm1 * gForm v.sent (ix Data.arr_ACC_VALUE a)

/-- Table `t`'s `memory`. -/
def gMemory (v : LinkIn α) (t : ℕ) : α :=
  sumL ((runOf Data.arr_ACC_START t).map fun a ↦ gGate v a * gAccess v a)

/-- Table `t`'s `r_bc`: `pc`, the opcode `g^t`, its operand equations. -/
def gRBc (v : LinkIn α) (t : ℕ) : α :=
  v.slot 1 * v.sent (ix Data.arr_STATE_PC t) + v.slot 2 + v.slot 3 * LOps.ofE (gpowE t) +
    sumL ((List.range (ix Data.arr_BC_OP_START (t + 1) - ix Data.arr_BC_OP_START t)).map fun i ↦
      v.slot (ix Data.arr_BC_OP_SLOT (ix Data.arr_BC_OP_START t + i)) *
        gForm v.sent (ix Data.arr_BC_OP_FORM (ix Data.arr_BC_OP_START t + i)))

/-- Table `t`'s successor state `nx0`, `nx1`. -/
def gNext0 (v : LinkIn α) (t : ℕ) : α := gForm v.sent (ix Data.arr_STATE_NEXT0 t)

def gNext1 (v : LinkIn α) (t : ℕ) : α := gForm v.sent (ix Data.arr_STATE_NEXT1 t)

/-- Table `t`'s `s_weight`: its state and successor under `eqzr` and `shz`. -/
def gSWeight (v : LinkIn α) (t : ℕ) : α :=
  v.eqzr * (1 + v.gs0 * v.sent (ix Data.arr_STATE_PC t) + v.gs1 * v.sent (ix Data.arr_STATE_FP t)) +
    v.shz * (1 + v.gs0 * gNext0 v t + v.gs1 * gNext1 v t)

/-- `JUMP`'s identities `ids`, from `JUMP_IDS`' sent values and the successor. -/
def gIds (v : LinkIn α) : α :=
  let cnd := v.sent (ix Data.arr_JUMP_IDS 0)
  let inv := v.sent (ix Data.arr_JUMP_IDS 1)
  let flg := v.sent (ix Data.arr_JUMP_IDS 2)
  let dst := v.sent (ix Data.arr_JUMP_IDS 3)
  let frm := v.sent (ix Data.arr_JUMP_IDS 4)
  let pc := v.sent (ix Data.arr_STATE_PC jumpTab)
  let fp := v.sent (ix Data.arr_STATE_FP jumpTab)
  let gpc := LOps.ofE (gpowE 1) * pc
  v.jump 0 * (flg + cnd * inv) + v.jump 1 * cnd * (flg + 1) +
    v.jump 2 * (gNext0 v jumpTab + gpc + flg * (dst + gpc)) +
    v.jump 3 * (gNext1 v jumpTab + fp + flg * (frm + fp))

/-- Table `t`'s `table_base`: `omega·eq0_r·(eta_mem·memory + eta_bc·r_bc)`, and `JUMP`'s
identities under `eq_tau`. -/
def gTableBase (v : LinkIn α) (t : ℕ) : α :=
  let tb := v.omega t * v.eq0R * (v.etaMem * gMemory v t + v.etaBc * gRBc v t)
  if t = jumpTab then tb + v.eqTau t * gIds v else tb

/-- `base = Σ_t corner_t·table_base_t`. -/
def gBase (v : LinkIn α) : α := sumL ((List.range nTab).map fun t ↦ v.corner t * gTableBase v t)

/-- The table of pointer column `q` (`PTR_START`). -/
def gPtrTable (q : ℕ) : ℕ := ((List.range nTab).filter fun t ↦ ix Data.arr_PTR_START (t + 1) ≤ q).length

/-- Pointer `q`'s `e = eq_q[q]·corner`, and `fq[q] = e·omega`. -/
def gE (v : LinkIn α) (q : ℕ) : α := v.eqQ q * v.corner (gPtrTable q)

def gFq (v : LinkIn α) (q : ℕ) : α := gE v q * v.omega (gPtrTable q)

/-- `cert_w = Σ_q fq[q]·eps[q]`. -/
def gCertW (v : LinkIn α) : α := sumL ((List.range nPtr).map fun q ↦ gFq v q * v.eps q)

/-- `ey = eta_mem·y_mem`. -/
def gEy (v : LinkIn α) : α := v.etaMem * v.yMem

/-- `coef`: each table's cycle pointer (`e·act·s_weight`) and program pointer
(`fq·(x_bc + fp·p_fp)`), the word reads (`fq·mu·scale·eta_mem·gm1·m1`), the unshifted accesses
(`fq·acc_gm·ey`). -/
def gCoef (v : LinkIn α) : α :=
  sumL ((List.range nTab).map fun t ↦
      gE v (ix Data.arr_PTR_START t) * v.act t * gSWeight v t +
        gFq v (ix Data.arr_PTR_START t + 1) * (v.xBc + v.sent (ix Data.arr_STATE_FP t) * v.pFp)) +
    sumL ((List.range nWr).map fun w ↦
      gFq v (ix Data.arr_WR_PTR w) * v.mu (ix Data.arr_WR_ACC w) * gForm v.sent (ix Data.arr_WR_SCALE w) *
        (v.etaMem * v.gm1 * v.m1)) +
    sumL ((List.range nAcc).map fun a ↦
      if ix Data.arr_ACC_SHIFT a = 0 then gFq v (ix Data.arr_ACC_PTR a) * gGate v a * gEy v else 0)

/-- `shifts[s]`: the accesses shifted by `s + 1`. -/
def gShift (v : LinkIn α) (s : ℕ) : α :=
  sumL ((List.range nAcc).map fun a ↦
    if ix Data.arr_ACC_SHIFT a = s + 1 then gFq v (ix Data.arr_ACC_PTR a) * gGate v a * gEy v else 0)

def gShifts (v : LinkIn α) : List α := (List.range nShift).map (gShift v)

/-- `rest = eq_q[0]·base`. -/
def gRest (v : LinkIn α) : α := v.eqQ 0 * gBase v

/-! ## The Statement's computations, generic -/

/-- One table's slot weights (`tableSlotWeights`). -/
def tswG (table : Table) (slot : List α) (gamma : α × α) (mu : List α) (etaMem etaBc : α) :
    List α × List α × List α :=
  let zero := List.replicate (2 ^ bytecodeSlotBits) (0 : α)
  let links := table.links
  let omega := zero.set 3 (etaBc * slot.getD 3 0)
  let omega := links.bytecodeLink.operands.foldl (fun omega (slots, _) ↦
    slots.foldl (fun omega s ↦ addAtG omega s (etaBc * slot.getD (slots.headD 0) 0)) omega) omega
  (links.memory.zip mu).foldl (fun (acc : List α × List α × List α) (access, m) ↦
    let m := etaMem * m
    let frame := match access.frame with
      | some (s, e) => addAtG acc.2.2 s (m * gamma.1 * LOps.ofE (gpow e))
      | none => acc.2.2
    access.reads.foldl (fun (acc : List α × List α × List α) read ↦
      match read with
      | .word _ _ => acc
      | .slot s scale => (addAtG acc.1 s (m * gamma.2 * LOps.ofE scale), acc.2.1, acc.2.2)
      | .frame s scale => (acc.1, acc.2.1, addAtG acc.2.2 s (m * gamma.2 * LOps.ofE scale))
      | .pc s scale => (acc.1, addAtG acc.2.1 s (m * gamma.2 * LOps.ofE scale), acc.2.2))
      (acc.1, acc.2.1, frame)) (omega, zero, zero)

/-- `slotWeights`: its `omega`, `pc` and `frame` rows. -/
def swG (tables : List Table) (slot : List α) (gamma : α × α) (mu : List (List α))
    (etaMem etaBc : α) : List (List α) × List (List α) × List (List α) :=
  let rows := tables.zipIdx.map fun (table, t) ↦
    tswG table slot gamma (mu.getD t []) etaMem etaBc
  (rows.map (·.1), rows.map (·.2.1), rows.map (·.2.2))

/-- `Split.ofColumns`: its `count`, `slots` and `pc`. -/
def ofColumnsG (tables : List Table) (values : List α) :
    List α × List (List α) × List (List α) :=
  let columns := splitColumns tables
  let valueOf := fun (c : SplitColumn) ↦ ((columns.idxOf? c).bind (values[·]?)).getD 0
  ((List.range nTables).map fun op ↦ valueOf (.count op),
    (List.range nTables).map fun op ↦ (List.range (2 ^ bytecodeSlotBits)).map fun s ↦
      valueOf (.slot op s),
    (List.range nTables).map fun op ↦ (List.range (2 ^ bytecodeSlotBits)).map fun s ↦
      valueOf (.pc op s))

/-- `programSide`: `(program, frameProgram)`. -/
def programSideG (weights : List (List α) × List (List α) × List (List α))
    (split : List α × List (List α) × List (List α)) : α × α :=
  (List.range nTables).foldl (fun (acc : α × α) t ↦
    let omega := weights.1.getD t []
    let pc := weights.2.1.getD t []
    let frame := weights.2.2.getD t []
    let slots := split.2.1.getD t []
    let pcs := split.2.2.getD t []
    let program := acc.1 + omega.getD 3 0 * LOps.ofE (gpow t) * split.1.getD t 0
    ((List.range (2 ^ bytecodeSlotBits - 4)).map (· + 4)).foldl (fun (acc : α × α) s ↦
      (acc.1 + (omega.getD s 0 * slots.getD s 0 + pc.getD s 0 * pcs.getD s 0),
        acc.2 + frame.getD s 0 * slots.getD s 0)) (program, acc.2)) (0, 0)

/-- The arithmetic fields of `LinkRowSide`. -/
structure RowAcc (α : Type) where
  coef : α
  shifts : List α
  certWeight : α
  base : α
  q : ℕ
  sent : List α

/-- The row side's fold (`verifyLink`'s `rowSide`), its arithmetic fields: each table's row
weight, activity, `eq(τ, χ)` and corner given (`omegaF`, `actF`, `eqTauF`, `cornerF`), and the
constraints `cons` (`Table.constraints`). -/
def rowSideG (tables : List Table) (omegaF actF eqTauF cornerF : ℕ → α)
    (gammaState gammaMem slot jump eps eqQ message : List α) (mu : List (List α))
    (etaMem etaBc eqZetaR shiftZetaR xBc pFp yMem m1 eq0R : α)
    (cons : Table → List α → List α) : RowAcc α :=
  let pointers := tables.map (·.links.pointers)
  let maxShift := tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  let stateGamma := fun (pc fp : α) ↦ 1 + gammaState.getD 0 0 * pc + gammaState.getD 1 0 * fp
  let nonPointer := fun (t : ℕ) (table : Table) ↦
    (List.range table.width).filter fun c ↦ !(pointers.getD t []).contains c
  let nValues := (tables.zipIdx.map fun (table, t) ↦ (nonPointer t table).length).sum
  tables.zipIdx.foldl (fun (acc : RowAcc α) (table, t) ↦
    let corner := cornerF t
    let columns := nonPointer t table
    let sent := columns.zip (acc.sent.take columns.length)
    let values := (List.range table.width).map fun c ↦ (sent.lookup c).getD 0
    let col := fun (c : ℕ) ↦ values.getD c 0
    let links := table.links
    let muT := mu.getD t []
    let omega := omegaF t
    let act := actF t
    let state := links.stateLink
    let sHat := stateGamma (col state.pc) (col state.fp)
    let sNext := stateGamma (formEvalG state.next.1 col) (formEvalG state.next.2 col)
    let accessValue := fun (a : Access) ↦
      gammaMem.getD 0 0 * formEvalG a.address col + gammaMem.getD 3 0 +
        gammaMem.getD 1 0 * formEvalG a.value col
    let bc := links.bytecodeLink
    let rBc := slot.getD 1 0 * col bc.pc + slot.getD 2 0 + slot.getD 3 0 * LOps.ofE (gpow bc.opcode) +
      sumL (bc.operands.map fun (slots, f) ↦ slot.getD (slots.headD 0) 0 * formEvalG f col)
    let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
    let memory := sumL ((links.memory.zip muT).map fun (a, m) ↦ m * gateOf a * accessValue a)
    let tableBase := omega * eq0R * (etaMem * memory + etaBc * rBc)
    let tableBase :=
      if 0 < table.nConstraints then
        let identities := cons table values
        let eqTau := eqTauF t
        tableBase + eqTau * sumL (List.zipWith (· * ·) jump identities)
      else tableBase
    (pointers.getD t []).zipIdx.foldl (fun (acc : RowAcc α) (pointer, k) ↦
      let e := eqQ.getD acc.q 0 * corner
      let (coef, shifts) :=
        match k with
        | 0 => (acc.coef + e * act * (eqZetaR * sHat + shiftZetaR * sNext), acc.shifts)
        | 1 => (acc.coef + e * omega * (xBc + col state.fp * pFp), acc.shifts)
        | _ =>
          let coef := (links.memory.zip muT).foldl (fun coef (access, m) ↦
            access.reads.foldl (fun coef read ↦
              match read with
              | .word p scale =>
                if p = pointer then
                  coef + e * omega * etaMem * m * gammaMem.getD 1 0 * m1 * formEvalG scale col
                else coef
              | _ => coef) coef) acc.coef
          ((links.memory.zip muT).filter (·.1.pointer = pointer)).foldl
            (fun (cs : α × List α) (access, m) ↦
              let c := e * omega * gateOf access * etaMem * m * yMem
              match access.shift with
              | 0 => (cs.1 + c, cs.2)
              | s + 1 => (cs.1, addAtG cs.2 s c)) (coef, acc.shifts)
      { acc with
        coef := coef
        shifts := shifts
        certWeight := acc.certWeight + e * omega * eps.getD acc.q 0
        q := acc.q + 1 })
      { acc with base := acc.base + corner * tableBase, sent := acc.sent.drop columns.length })
    ⟨0, List.replicate maxShift 0, 0, 0, 0, message.take nValues⟩

end Generic

/-! ## `linkTail`'s `let`s, named -/

/-- `linkTail`'s values up to the row side: the challenges as it slices them, the memory term's
`y_mem`, the program side, `x_bc`, `p_fp`, and the index point's weights. -/
structure TailLets where
  theta : List E
  gammaState : List E
  gammaMem : List E
  mu : List (List E)
  etaMem : E
  etaBc : E
  eps : List E
  tau : List E
  zeta : List E
  nu : List E
  slot : List E
  cert : E
  jump : List E
  yMem : E
  program : E
  frameProgram : E
  xBc : E
  pFp : E
  belowMem : E
  belowBc : E
  eq0R : E
  eqZetaR : E
  shiftZetaR : E
  eqQ : List E

/-- `linkTail`'s `let`s, as it computes them (`LeanVM.Protocol.Link.linkTail`). -/
def tailLets (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (qPoint : List E) : TailLets :=
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let width := chunks.width
  let d := chunks.d
  let pointers := tables.map (·.links.pointers)
  let nPointers := (pointers.map List.length).sum
  let nRows := heights.foldl max 0
  let theta := theta0 :: drawn.take (nTables - 1)
  let drawn := drawn.drop (nTables - 1)
  let gammaState := drawn.take 2
  let drawn := drawn.drop 2
  let g := drawn.take 3
  let drawn := drawn.drop 3
  let gammaMem : List E := [g.getD 0 0, g.getD 1 0, g.getD 1 0 * eY, g.getD 2 0]
  let (mu, drawn) := tables.foldl (fun (acc : List (List E) × List E) t ↦
    (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) ([], drawn)
  let alpha := drawn.take bytecodeSlotBits
  let drawn := drawn.drop bytecodeSlotBits
  let etaMem := drawn.getD 0 0
  let etaBc := drawn.getD 1 0
  let drawn := drawn.drop 2
  let eps := drawn.take nPointers
  let drawn := drawn.drop nPointers
  let tau := drawn.take nRows
  let drawn := drawn.drop nRows
  let zeta := drawn.take width
  let nu := (drawn.drop width).take d
  let slot := eqKernel alpha
  let cert := fresh.getD 0 0
  let jump := fresh.drop 1
  let below := fun (k : ℕ) ↦ prodE ((r.drop (min k width)).map (1 + ·))
  let yMem := gammaMem.getD 0 0 * indexMle r + gammaMem.getD 3 0 * below layout.logMemory +
    gammaMem.getD 1 0 * m1
  let weights := slotWeights tables slot (gammaMem.getD 0 0, gammaMem.getD 1 0) mu etaMem etaBc
  let (program, frameProgram) := (List.range nTables).foldl (fun (acc : E × E) t ↦
    let omega := weights.omega.getD t []
    let pc := weights.pc.getD t []
    let frame := weights.frame.getD t []
    let slots := split.slots.getD t []
    let pcs := split.pc.getD t []
    let program := acc.1 + omega.getD 3 0 * gpow t * split.count.getD t 0
    ((List.range (2 ^ bytecodeSlotBits - 4)).map (· + 4)).foldl (fun (acc : E × E) s ↦
      (acc.1 + (omega.getD s 0 * slots.getD s 0 + pc.getD s 0 * pcs.getD s 0),
        acc.2 + frame.getD s 0 * slots.getD s 0)) (program, acc.2)) (0, 0)
  let belowBc := below layout.logBytecode
  let xBc := etaBc * slot.getD 1 0 * indexMle r + belowBc * (etaBc * slot.getD 2 0 + program)
  let pFp := belowBc * frameProgram
  let eq0R := below 0
  let eqZetaR := eqEval zeta r
  let shiftZetaR := linkShiftEq zeta r
  let eqQ := eqKernel qPoint
  { theta := theta, gammaState := gammaState, gammaMem := gammaMem, mu := mu, etaMem := etaMem
    etaBc := etaBc, eps := eps, tau := tau, zeta := zeta, nu := nu, slot := slot, cert := cert
    jump := jump, yMem := yMem, program := program, frameProgram := frameProgram, xBc := xBc
    pFp := pFp, belowMem := below layout.logMemory, belowBc := belowBc, eq0R := eq0R
    eqZetaR := eqZetaR, shiftZetaR := shiftZetaR, eqQ := eqQ }

/-- The values `linkTail` reads at the row point, `nValues` of them (`nonPointer`'s columns). -/
def tailNValues (layout : Layout) : ℕ :=
  let tables := layout.tables
  let pointers := tables.map (·.links.pointers)
  let nonPointer := fun (t : ℕ) (table : Table) ↦
    (List.range table.width).filter fun c ↦ !(pointers.getD t []).contains c
  (tables.zipIdx.map fun (table, t) ↦ (nonPointer t table).length).sum

/-- `linkTail`'s row side (`rowSide`), from the packed message. -/
def tailRowSide (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (chi qPoint message : List E) : LinkRowSide :=
  let L := tailLets layout chunks theta0 drawn r m1 fresh split qPoint
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let rows := layout.tableRows
  let pointers := tables.map (·.links.pointers)
  let maxShift := tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  let stateGamma := fun (pc fp : E) ↦ 1 + L.gammaState.getD 0 0 * pc + L.gammaState.getD 1 0 * fp
  let nonPointer := fun (t : ℕ) (table : Table) ↦
    (List.range table.width).filter fun c ↦ !(pointers.getD t []).contains c
  let nValues := (tables.zipIdx.map fun (table, t) ↦ (nonPointer t table).length).sum
  let eqQ := L.eqQ
  tables.zipIdx.foldl (fun (acc : LinkRowSide) (table, t) ↦
    let height := heights.getD t 0
    let tableRows := rows.getD t 0
    let point := chi.take height
    let corner := prodE ((chi.drop height).map (1 + ·))
    let columns := nonPointer t table
    let sent := columns.zip (acc.sent.take columns.length)
    let values := (List.range table.width).map fun c ↦ (sent.lookup c).getD 0
    let col := fun (c : ℕ) ↦ values.getD c 0
    let links := table.links
    let muT := L.mu.getD t []
    let omega := omegaAt (L.theta.getD t 0) (L.tau.take height) point tableRows
    let act := lessThan point tableRows
    let state := links.stateLink
    let sHat := stateGamma (col state.pc) (col state.fp)
    let sNext := stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)
    let accessValue := fun (a : Access) ↦
      L.gammaMem.getD 0 0 * a.address.evaluate col + L.gammaMem.getD 3 0 +
        L.gammaMem.getD 1 0 * a.value.evaluate col
    let bc := links.bytecodeLink
    let rBc := L.slot.getD 1 0 * col bc.pc + L.slot.getD 2 0 + L.slot.getD 3 0 * gpow bc.opcode +
      sumE (bc.operands.map fun (slots, f) ↦ L.slot.getD (slots.headD 0) 0 * f.evaluate col)
    let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
    let memory := sumE ((links.memory.zip muT).map fun (a, m) ↦ m * gateOf a * accessValue a)
    let tableBase := omega * L.eq0R * (L.etaMem * memory + L.etaBc * rBc)
    let tableBase :=
      if 0 < table.nConstraints then
        let identities := table.constraints values
        let eqTau := eqEval (L.tau.take height) point
        tableBase + eqTau * sumE (List.zipWith (· * ·) L.jump identities)
      else tableBase
    let acc := (pointers.getD t []).zipIdx.foldl (fun (acc : LinkRowSide) (pointer, k) ↦
      let e := eqQ.getD acc.q 0 * corner
      let (coef, shifts) :=
        match k with
        | 0 => (acc.coef + e * act * (L.eqZetaR * sHat + L.shiftZetaR * sNext), acc.shifts)
        | 1 => (acc.coef + e * omega * (L.xBc + col state.fp * L.pFp), acc.shifts)
        | _ =>
          let coef := (links.memory.zip muT).foldl (fun coef (access, m) ↦
            access.reads.foldl (fun coef read ↦
              match read with
              | .word p scale =>
                if p = pointer then
                  coef + e * omega * L.etaMem * m * L.gammaMem.getD 1 0 * m1 * scale.evaluate col
                else coef
              | _ => coef) coef) acc.coef
          ((links.memory.zip muT).filter (·.1.pointer = pointer)).foldl
            (fun (cs : E × List E) (access, m) ↦
              let c := e * omega * gateOf access * L.etaMem * m * L.yMem
              match access.shift with
              | 0 => (cs.1 + c, cs.2)
              | s + 1 => (cs.1, addAtSlot cs.2 s c)) (coef, acc.shifts)
      let piece : RingPiece :=
        { placement :=
            some ((layout.placements.getD (globalColumnBases.getD t 0 + pointer) none).getD default)
          point := point
          scale := eqQ.getD acc.q 0 }
      { acc with
        coef := coef
        shifts := shifts
        certWeight := acc.certWeight + e * omega * L.eps.getD acc.q 0
        pieces := acc.pieces ++ [piece]
        q := acc.q + 1 })
      { acc with base := acc.base + corner * tableBase, sent := acc.sent.drop columns.length }
    { acc with columns := acc.columns ++ [(point, sent)] })
    ⟨0, List.replicate maxShift 0, 0, 0, [], 0, [], message.take nValues⟩

/-- `linkTail`, its `let`s named: the packed message, the row side, the terminal check, the
`LinkEnd`. -/
def linkTailR (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (chi qPoint : List E) (claim : E) :
    VerifierProgram LinkEnd := do
  let L := tailLets layout chunks theta0 drawn r m1 fresh split qPoint
  let maxShift := layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  let nValues := tailNValues layout
  let message ← VerifierProgram.readScalarsPacked (nValues + kBits)
  let slices := message.drop nValues
  let rowSide := tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message
  let functionals := Functionals.new chunks r maxShift
  let values := functionals.values chunks slices
  let eq0Q := prodE (qPoint.map (1 + ·))
  let certs := L.nu.map fun n ↦ L.cert * rowSide.certWeight * n
  let last := functionals.summand rowSide.coef rowSide.shifts values certs + eq0Q * rowSide.base
  VerifierProgram.require (last = claim)
  return {
    memoryPoint := r.take layout.logMemory
    memoryScales := (L.belowMem, eY * L.belowMem)
    memoryValue := m1
    columns := rowSide.columns
    ring := ⟨rowSide.pieces, slices⟩
    bytecodePoint := r.take layout.logBytecode }

/-- **`linkTail` is `linkTailR`**: nothing was changed by naming its `let`s. -/
def LinkTailEq : Prop :=
  ∀ (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E) (fresh : List E)
    (split : Split) (chi qPoint : List E) (claim : E),
    linkTail layout chunks theta0 drawn r m1 fresh split chi qPoint claim =
      linkTailR layout chunks theta0 drawn r m1 fresh split chi qPoint claim

/-! ## The guest's inputs at the Statement's values -/

/-- The guest's inputs as the Statement's values: `chal` the challenges `θ_0 :: drawn`, `slot`
`eq(α, ·)`, the sent values the message's, the split values `splitv`, `eqQ` `eq(q_point, ·)`, each
table's row weight, activity, `eq(τ, χ)` and corner at the row point `chi`, the fresh
coefficients, `e0 = eq(ζ, 0)` and `ec = eq(ζ, T)`, the index side's `indexMle r`,
`eq(ζ, r)`, `linkShiftEq ζ r`, the `below` products, and `y_mem`, `x_bc`, `p_fp`. -/
def tailIn (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh splitv chi qPoint message : List E) : LinkIn E :=
  let L := tailLets layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) qPoint
  let height := fun (t : ℕ) ↦ layout.tableLogHeights.getD t 0
  { chal := fun k ↦ (theta0 :: drawn).getD k 0
    slot := fun s ↦ L.slot.getD s 0
    sent := fun k ↦ message.getD k 0
    splitv := fun k ↦ splitv.getD k 0
    eqQ := fun q ↦ L.eqQ.getD q 0
    omega := fun t ↦ omegaAt (L.theta.getD t 0) (L.tau.take (height t)) (chi.take (height t))
      (layout.tableRows.getD t 0)
    act := fun t ↦ lessThan (chi.take (height t)) (layout.tableRows.getD t 0)
    eqTau := fun t ↦ eqEval (L.tau.take (height t)) (chi.take (height t))
    corner := fun t ↦ prodE ((chi.drop (height t)).map (1 + ·))
    jump := fun k ↦ L.jump.getD k 0
    e0 := linkEqAt L.zeta 0
    ec := linkEqAt L.zeta (linkCycles layout)
    idx := indexMle r
    eqzr := L.eqZetaR
    shz := L.shiftZetaR
    belowMem := L.belowMem
    belowBc := L.belowBc
    eq0R := L.eq0R
    m1 := m1
    cert := L.cert
    xBc := L.xBc
    pFp := L.pFp
    yMem := L.yMem }

/-! ## The identities -/

/-- The lengths the identities ask of the Statement's inputs: the tables are `tables()`, the
challenges cover the fixed-count ones (`LINK_FIXED`), five fresh coefficients, one split value
per split column, the pointer columns' point has `LINK_Q_VARS = log2Ceil 33` coordinates (the
pointer columns' sum-check's rounds), the message covers the sent values. -/
structure TailShape (layout : Layout) (drawn fresh splitv qPoint message : List E) : Prop where
  tablesEq : layout.tables = tables
  drawnLen : guest_const% LINK_FIXED ≤ drawn.length
  freshLen : fresh.length = 5
  splitvLen : splitv.length = (splitColumns tables).length
  qPointLen : qPoint.length = guest_const% LINK_Q_VARS
  messageLen : tailNValues layout ≤ message.length

/-- **The index side's claim**: `e0·(1 + gs0 + gs1) + ec·(1 + gs0·g^(2^BYTECODE_LOG - 1) + gs1)`
is `verify_link`'s `eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin`. -/
def ClaimIdentity : Prop :=
  ∀ (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh splitv chi qPoint message : List E),
    layout.logBytecode = guest_const% BYTECODE_LOG →
    gClaim (tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message) =
      indexClaim layout chunks drawn

/-- **The program side**: the guest's `(program, frame_program)` over the hinted split values is
`verify_link`'s at `freshSplit`'s split, `Split.ofColumns tables splitv`. -/
def ProgramIdentity : Prop :=
  ∀ (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh splitv chi qPoint message : List E),
    TailShape layout drawn fresh splitv qPoint message →
    let L := tailLets layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) qPoint
    gProgram (tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message) =
      (L.program, L.frameProgram)

/-- **`y_mem`, `x_bc`, `p_fp`** are the Statement's `yMem`, `xBc`, `pFp`. -/
def SideIdentity : Prop :=
  ∀ (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh splitv chi qPoint message : List E),
    TailShape layout drawn fresh splitv qPoint message →
    let L := tailLets layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) qPoint
    let v := tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message
    gYMem v = L.yMem ∧ gXBc v = L.xBc ∧ gPFp v = L.pFp

/-- **The row side**: `coef`, `shifts`, `cert_w` and `base` are the row side's `coef`, `shifts`,
`certWeight` and `base` (`linkTail`'s `rowSide`, at the packed message). -/
def RowIdentity : Prop :=
  ∀ (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh splitv chi qPoint message : List E),
    TailShape layout drawn fresh splitv qPoint message →
    let R := tailRowSide layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) chi
      qPoint message
    let v := tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message
    gCoef v = R.coef ∧ gShifts v = R.shifts ∧ gCertW v = R.certWeight ∧ gBase v = R.base

/-- **The terminal's arguments**: `rest = eq_q[0]·base` is `eq0(q_point)·base` and the
certificates `(cert_w·cert)·ν_c` are `cert·cert_weight·ν_c`, at the Statement's values. -/
def TerminalIdentity : Prop :=
  ∀ (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh splitv chi qPoint message : List E),
    TailShape layout drawn fresh splitv qPoint message →
    let L := tailLets layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) qPoint
    let R := tailRowSide layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) chi
      qPoint message
    let v := tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message
    gRest v = prodE (qPoint.map (1 + ·)) * R.base ∧
      L.nu.map (gCertW v * v.cert * ·) = L.nu.map fun n ↦ L.cert * R.certWeight * n

end

end LeanVM.Guest.B1.Link.Arith
