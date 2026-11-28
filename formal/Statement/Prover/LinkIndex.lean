module

public import Statement.Prover.Columns
public import Statement.Prover.Script
public import Statement.Prover.Mle

/-!
# Sums of products of multilinear tables, the link's challenges, and its index side

A sum-check over a sum of products of tables (`Prods`): every term a coefficient times a product of
tables, each the multilinear extension of its entries, all of `2^n` entries, the lowest variable
bound first. A round's polynomial is the sum over the pairs `2k, 2k + 1` of the products of each
factor's line through its two entries (`Prods.round`), and its fold binds every table
(`Prods.fold`). The link's three sum-checks are all of this shape: the index side here, the rows
and the pointer columns in `LinkRow.lean`. The round polynomial of a sum over the cube is unique,
so it is the Rust's however the Rust computes it (`crates/lean_vm_core/src/link/index.rs`,
`row.rs`, `base.rs`, which store tails in closed form and skip the pairs where a factor vanishes).

The challenges are split as `verifyLink` splits them (`LinkChallenges`), and a table's payload is
its links' forms under them (`payloadForms`, `tableBlocks`), which the index side sums over the
executed rows and the row side reads as base terms. The index side (`index.rs`; its arrays in
`prove`, `crates/lean_vm_core/src/link/prove.rs`) runs over the index `j < 2^W` of cycles, memory
cells and instructions: the arrays the rows' pointers scatter (`scatterWords`,
`Scatter::add_words`) and the closed forms they pair with.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## Sums of products of tables -/

/-- A sum of products of tables: each term a coefficient and the tables it multiplies, by
position; every table has the same `2^n` entries. -/
structure Prods where
  /-- The tables. -/
  tables : Array (Array E)
  /-- The terms: a coefficient and its factors. -/
  terms : Array (E × Array ℕ)
  deriving Inhabited

/-- The coefficients of `p·(lo + X·(lo + hi))`, the line through `lo` at `0` and `hi` at `1`,
constant first. -/
def mulLineA (p : Array E) (lo hi : E) : Array E :=
  let slope := lo + hi
  Array.ofFn (n := p.size + 1) fun j ↦
    lo * p.getD j.val 0 + (if j.val = 0 then 0 else slope * p.getD (j.val - 1) 0)

/-- `acc + p`, coefficient by coefficient, over `acc`'s entries. -/
def addInto (acc p : Array E) : Array E :=
  Nat.fold p.size (fun j _ acc ↦ acc.modify j (· + p.getD j 0)) acc

/-- **A round's polynomial**, `count` coefficients, constant first: each term's product of lines
summed over the pairs of entries. -/
def Prods.round (P : Prods) (count : ℕ) : List E :=
  let half := (P.tables.getD 0 #[]).size / 2
  (Nat.fold half (fun k _ acc ↦ P.terms.foldl (fun acc (coef, factors) ↦
      if coef = 0 then acc
      else addInto acc (factors.foldl (fun p f ↦
        let t := P.tables.getD f #[]
        mulLineA p (t.getD (2 * k) 0) (t.getD (2 * k + 1) 0)) #[coef])) acc)
    (Array.replicate count 0)).toList

/-- Every table with its lowest variable bound at `x`. -/
def Prods.fold (P : Prods) (x : E) : Prods := { P with tables := P.tables.map (foldPairsA x) }

/-- Table `f`'s first entry: its value once every variable is bound. -/
def Prods.at (P : Prods) (f : ℕ) : E := (P.tables.getD f #[]).getD 0 0

/-- The sum's value once every variable is bound. -/
def Prods.value (P : Prods) : E :=
  P.terms.foldl (fun acc (coef, factors) ↦ acc + factors.foldl (fun v f ↦ v * P.at f) coef) 0

/-- **A plain-mode sum-check over a sum of products**: per round its `count` coefficients
(`sumcheckBy`, `Script.lean`), `rounds` rounds; the challenges and the tables bound there. -/
def prodsSumcheck (count rounds : ℕ) (P : Prods) : Script (List E × Prods) :=
  sumcheckBy (fun P ↦ P.round count) Prods.fold (List.replicate rounds none) P

/-! ## Scattering -/

/-- `Scatter::add_words(chunks, words, rows, shift, weight)` (`index.rs`): add `weight u` at every
index of row `u`'s word plus `shift`, for the rows `u < rows`, dropping an index whose shift leaves
its window (`Chunks.shifted`); a row of zero weight adds nothing. -/
def scatterWords (chunks : Chunks) (words : Array K) (rows shift : ℕ) (weight : ℕ → E)
    (a : Array E) : Array E :=
  Nat.fold rows (fun u _ a ↦
    let w := weight u
    if w = 0 then a
    else (chunks.indices (kToNat (words.getD u 0))).foldl (fun a j ↦
      match chunks.shifted j shift with
      | some j => a.modify j (· + w)
      | none => a) a) a

/-! ## The challenges (`Challenges::sample`, `prove.rs`) -/

/-- The link's challenges, as `verifyLink` splits them: `θ` per table, `γ_pc, γ_fp`, `γ_mem`
(on the address, the two limbs, `γ_word` and `γ_word·y`, and the presence coordinate), `μ` per
table per access, `α` over the program's slots and its equality table, `η_mem`, `η_bc`, `ε` per
pointer column, `τ` over the tallest table's rows, `ζ` over the pointer width and `ν` over its
chunks. -/
structure LinkChallenges where
  theta : List E
  gammaState : List E
  gammaMem : List E
  mu : List (List E)
  alpha : List E
  slot : List E
  etaMem : E
  etaBc : E
  eps : List E
  tau : List E
  zeta : List E
  nu : List E
  deriving Inhabited

/-- The challenges from `θ_0` and the packed draw, split as `verifyLink` splits them. -/
def LinkChallenges.ofDraw (tables : List Table) (nRows width d : ℕ) (theta0 : E)
    (drawn : List E) : LinkChallenges :=
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
  let nPointers := (tables.map (·.links.pointers.length)).sum
  let eps := drawn.take nPointers
  let drawn := drawn.drop nPointers
  let tau := drawn.take nRows
  let drawn := drawn.drop nRows
  let zeta := drawn.take width
  let nu := (drawn.drop width).take d
  ⟨theta, gammaState, gammaMem, mu, alpha, eqKernel alpha, etaMem, etaBc, eps, tau, zeta, nu⟩

/-! ## A table's rows -/

/-- Row `u` of a table's columns, as `E`, the column `c` read at `ofK`. -/
def rowValue (cols : Array (Array K)) (u : ℕ) (c : ℕ) : E := ofK ((cols.getD c #[]).getD u 0)

/-- A column as a table over `E`. -/
def columnE (cols : Array (Array K)) (c : ℕ) : Array E := (cols.getD c #[]).map ofK

/-- `ω_F = θ_F·eq(τ_F, u)` on a table's executed rows `u < n`, zero on its padding rows, over its
`2^h` rows (`omegas`, `prove.rs`). -/
def omegaTable (theta : E) (tau : List E) (h n : ℕ) : Array E :=
  let e := eqTable (tau.take h)
  Array.ofFn (n := 2 ^ h) fun u ↦ if u.val < n then theta * e.getD u.val 0 else 0

/-- The state `ŝ_γ = 1 + γ_pc·pc + γ_fp·fp` and the successor's `ŝ'_γ` of a row (`state_forms`,
`prove.rs`). -/
def stateValues (ch : LinkChallenges) (links : Links) (col : ℕ → E) : E × E :=
  let s := links.stateLink
  let γ := fun pc fp ↦ 1 + ch.gammaState.getD 0 0 * pc + ch.gammaState.getD 1 0 * fp
  (γ (col s.pc) (col s.fp), γ (s.next.1.evaluate col) (s.next.2.evaluate col))

/-- The columns gating an access, in order of first use (`Plan::gates`, `prove.rs`). -/
def linkGates (links : Links) : List ℕ :=
  links.memory.foldl (fun gs a ↦ match a.gate with
    | some g => if gs.contains g then gs else gs ++ [g]
    | none => gs) []

/-- `payload_forms(table, plan, ch, t)` (`prove.rs`): a table's payload, before the `eq(0, r)`
factor: the ungated form `η_bc·R_bc + η_mem·Σ μ·access` over the ungated accesses, then one form
per gate, `η_mem·Σ μ·access` over the accesses it gates, an access's committed part being
`γ_addr·address + γ_pres + γ_word·value`. -/
def payloadForms (ch : LinkChallenges) (links : Links) (mu : List E) : Form × List (ℕ × Form) :=
  let a := ch.slot
  let bc := links.bytecodeLink
  let ungated : Form := ⟨[([bc.pc], ch.etaBc * a.getD 1 0),
    ([], ch.etaBc * a.getD 2 0 + ch.etaBc * a.getD 3 0 * gpow bc.opcode)]⟩
  let ungated := bc.operands.foldl (fun f (slots, operand) ↦
    f.addScaled operand (ch.etaBc * a.getD (slots.headD 0) 0)) ungated
  let gated := (linkGates links).map fun g ↦ (g, ({} : Form))
  (links.memory.zip mu).foldl (fun (acc : Form × List (ℕ × Form)) (access, m) ↦
    let w := ch.etaMem * m
    let add := fun (f : Form) ↦
      ((f.addScaled access.address (w * ch.gammaMem.getD 0 0)).addScaled (Form.const 1)
        (w * ch.gammaMem.getD 3 0)).addScaled access.value (w * ch.gammaMem.getD 1 0)
    match access.gate with
    | none => (add acc.1, acc.2)
    | some g => (acc.1, acc.2.map fun (g', f) ↦ if g' = g then (g', add f) else (g', f)))
    (ungated, gated)

/-- `JumpTable::constraint(coefs)` (`crates/lean_vm_core/src/tables.rs`): `JUMP`'s identities
(`jumpConstraints`) weighed by `coefs`, as one form of degree two in its columns. -/
def jumpConstraintForm (coefs : List E) : Form :=
  let c := colIndex jumpColumns
  let (pc, fp, cond, dest, frame, pcNext, fpNext, w, b) :=
    (c "pc", c "fp", c "v_cond", c "v_pc", c "v_fp", c "pc_next", c "fp_next", c "w", c "b")
  let k := fun i ↦ coefs.getD i 0
  let gk := k 2 * gpow 1
  ⟨[([b], k 0), ([cond], k 1), ([pcNext], k 2), ([pc], gk), ([fpNext], k 3), ([fp], k 3),
    ([min cond w, max cond w], k 0), ([min cond b, max cond b], k 1),
    ([min b dest, max b dest], k 2), ([min b pc, max b pc], gk), ([min b frame, max b frame], k 3),
    ([min b fp, max b fp], k 3)]⟩

/-- A table's base block (`Block`, `base.rs`): `weight(u)·gate(u)·form(u)`, the weight `ω_F`
(`onEq = false`) or `eq(τ_F, u)` (`onEq = true`). -/
structure Block where
  onEq : Bool
  gate : Option ℕ
  form : Form

/-- `blocks(table, plan, ch, t, scale, jump)` (`prove.rs`): the payload's forms scaled by `scale`
under `ω_F`, and with `jump`, `JUMP`'s identities under `eq(τ_F, ·)`. -/
def tableBlocks (ch : LinkChallenges) (t : ℕ) (scale : E) (jump : Option (List E)) : List Block :=
  let table := tables.getD t default
  let (ungated, gated) := payloadForms ch table.links (ch.mu.getD t [])
  let scaled := fun (f : Form) ↦ ({} : Form).addScaled f scale
  ⟨false, none, scaled ungated⟩ :: gated.map (fun (g, f) ↦ ⟨false, some g, scaled f⟩) ++
    match jump with
    | some coefs => if 0 < table.nConstraints then [⟨true, none, jumpConstraintForm coefs⟩] else []
    | none => []

/-- `Base::payload(omega)` (`base.rs`): `Σ_u ω_F(u)·gate(u)·form(u)` over a table's `ω` blocks at
scale one, the index side's constant term. -/
def tablePayload (ch : LinkChallenges) (t n : ℕ) (cols : Array (Array K)) (omega : Array E) : E :=
  let blocks := (tableBlocks ch t 1 none).filter (!·.onEq)
  sumRange n fun u ↦
    let col := rowValue cols u
    omega.getD u 0 * sumE (blocks.map fun b ↦ (b.gate.map col).getD 1 * b.form.evaluate col)

/-! ## The index side (`prove`, `prove.rs`; `index.rs`) -/

/-- `word_reads(plan, n_cols, mu, weight)` (`prove.rs`): each pointer a table reads words at, in
order of first use, with what it reads there, `Σ weight·μ·scale` over its word reads. -/
def wordReads (links : Links) (mu : List E) (weight : E) : List (ℕ × Form) :=
  (links.memory.zip mu).foldl (fun out (access, m) ↦
    access.reads.foldl (fun out read ↦ match read with
      | .word p scale =>
        if out.any (·.1 = p) then out.map fun (p', f) ↦ (p', if p' = p then f.addScaled scale (weight * m) else f)
        else out ++ [(p, ({} : Form).addScaled scale (weight * m))]
      | _ => out) out) []

/-- The index side's thirteen arrays over `2^W` indices, in `prove`'s order: `A` and `B`, each
executed row's state and successor at its cycle; the memory accesses' weights at their cells
(`w_mem`) and the memory's address table `Y`; the rows' weight at their instructions (`w_bc`) and
the program side's target `X_ω`; `eq(ζ, j)` and `eq(ζ, j + 1)` (zero at the top index); the
payload at index `0`; the word reads' weights (`v_word`) and the memory's words; `ω·fp` at the
instructions (`w_fp`) and the program side's `P_fp`. -/
def indexArrays (W : Witness) (ch : LinkChallenges) : Array (Array E) :=
  let layout := W.layout
  let chunks := W.chunks
  let N := 2 ^ chunks.width
  let logMem := layout.logMemory
  let bytecode := layout.bytecode.toArray
  let nBc := bytecode.size >>> bytecodeSlotBits
  let slot := fun (s j : ℕ) ↦ bytecode.getD (s * nBc + j) 0
  let gm := fun i ↦ ch.gammaMem.getD i 0
  let zero := Array.replicate N (0 : E)
  -- The scattered arrays, table by table.
  let scattered := (List.range nTables).foldl (fun (acc : Vector (Array E) 6) t ↦
    let table := tables.getD t default
    let links := table.links
    let cols := W.tableCols t
    let n := W.rows.getD t 0
    let omega := omegaTable (ch.theta.getD t 0) ch.tau (layout.tableLogHeights.getD t 0) n
    let mu := ch.mu.getD t []
    let state := links.stateLink
    let cyc := cols.getD state.cycle #[]
    let bcw := cols.getD links.bytecodeLink.pointer #[]
    let states := scatterWords chunks cyc n 0 (fun u ↦ (stateValues ch links (rowValue cols u)).1)
      acc[0]
    let nexts := scatterWords chunks cyc n 0 (fun u ↦ (stateValues ch links (rowValue cols u)).2)
      acc[1]
    let wMem := (links.memory.zip mu).foldl (fun a (access, m) ↦
      scatterWords chunks (cols.getD access.pointer #[]) n access.shift (fun u ↦
        let w := m * omega.getD u 0
        match access.gate with
        | some g => w * rowValue cols u g
        | none => w) a) acc[2]
    let vWord := (wordReads links mu (gm 1)).foldl (fun a (p, scale) ↦
      scatterWords chunks (cols.getD p #[]) n 0
        (fun u ↦ scale.evaluate (rowValue cols u) * omega.getD u 0) a) acc[3]
    let wBc := scatterWords chunks bcw n 0 (fun u ↦ omega.getD u 0) acc[4]
    let wFp := scatterWords chunks bcw n 0 (fun u ↦ omega.getD u 0 * rowValue cols u state.fp)
      acc[5]
    #v[states, nexts, wMem, vWord, wBc, wFp]) (Vector.replicate 6 zero)
  let mem0 := W.cols.getD memory0 #[]
  let mem1 := W.cols.getD memory1 #[]
  let gPow := (powers gen N).toArray
  let gj := fun j ↦ gPow.getD j 0
  -- The memory's address table and words; past the memory only `γ_addr·g^j`, and no word.
  let yMem := Array.ofFn (n := N) fun j ↦
    if j.val < 2 ^ logMem then
      gm 0 * gj j + gm 1 * ofK (mem0.getD j 0) + gm 2 * ofK (mem1.getD j 0) + gm 3
    else gm 0 * gj j
  let words := Array.ofFn (n := N) fun j ↦
    if j.val < 2 ^ logMem then ofK (mem0.getD j 0) + eY * ofK (mem1.getD j 0) else 0
  -- The program side's targets, each instruction's slots weighed by its opcode.
  let weights := slotWeights tables ch.slot (gm 0, gm 1) ch.mu ch.etaMem ch.etaBc
  let (xG, xOne) := (ch.etaBc * ch.slot.getD 1 0, ch.etaBc * ch.slot.getD 2 0)
  let xBc := Array.ofFn (n := N) fun j ↦
    if j.val < nBc then
      let op := opcodeOf (slot 3 j)
      let omega := weights.omega.getD op []
      let pc := weights.pc.getD op []
      xG * gj j + xOne + sumE ((List.range (2 ^ bytecodeSlotBits - 3)).map fun i ↦
        let s := i + 3
        omega.getD s 0 * ofK (slot s j) + pc.getD s 0 * (gj j * ofK (slot s j)))
    else xG * gj j
  let pFp := Array.ofFn (n := N) fun j ↦
    if j.val < nBc then
      let frame := weights.frame.getD (opcodeOf (slot 3 j)) []
      sumE ((List.range (2 ^ bytecodeSlotBits - 4)).map fun i ↦ frame.getD (i + 4) 0 * ofK (slot (i + 4) j))
    else 0
  let eqZ := eqTable ch.zeta
  let eqNext := Array.ofFn (n := N) fun j ↦ eqZ.getD (j.val + 1) 0
  let payload := sumE ((List.range nTables).map fun t ↦
    tablePayload ch t (W.rows.getD t 0) (W.tableCols t)
      (omegaTable (ch.theta.getD t 0) ch.tau (layout.tableLogHeights.getD t 0) (W.rows.getD t 0)))
  #[scattered[0], scattered[1], scattered[2], yMem, scattered[4], xBc, eqZ, eqNext,
    zero.set! 0 payload, scattered[3], words, scattered[5], pFp]

/-- The index side's summand (`terms`, `prove.rs`): the state identity
`eq(ζ, j)·A(j) + eq(ζ, j + 1)·B(j)`, the memory `η_mem·w_mem·Y`, the program `w_bc·X_ω`, the
payload, the word reads `η_mem·v_word·words` and the frame reads `w_fp·P_fp`. -/
def indexProds (W : Witness) (ch : LinkChallenges) : Prods :=
  ⟨indexArrays W ch, #[(1, #[6, 0]), (1, #[7, 1]), (ch.etaMem, #[2, 3]), (1, #[4, 5]), (1, #[8]),
    (ch.etaMem, #[9, 10]), (1, #[11, 12])]⟩

end LeanVM.Prover

end
