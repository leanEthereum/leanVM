module

public import Statement.Prover.LinkIndex

/-!
# The link's row side, executable

The row side of `verifyLink` (`crates/lean_vm_core/src/link/row.rs`, `base.rs`; its inputs in
`prove`, `prove.rs`): one sum-check over every table's rows, lowest variable first, then over the
pointer columns `q`. A table of `2^h` rows is a sum of products of its tables (`Prods`): per
pointer column, `ω_F·c_ω·D_0·Π_{i ≥ 1} D_i + act_F·c_act·D_0·Π_{i ≥ 1} D_i`, each shifted read
`ω_F·gate·c·T_s·Π_{i ≥ 1} D_i`, and the mirror certificate `ω_F·e_i·(D_i·D̄_i + π_i)`, where `D_i`,
`D̄_i` and `T_s` are the functionals of the column's words (`Functionals`, the pointer at `r`, at
`1 + r`, read `s` further); then its base terms, the payload under `ω_F·eq(0, r)` and `JUMP`'s
identities under `eq(τ_F, ·)`. Bound after `h` rounds, a table takes the corner factor `1 + x` of
each further round (`round_poly`, `row.rs`). The pointer-column rounds read each column's
coefficients, values and certificate weights at the row point, its table's corner factor in, and
the base terms' total at `q = 0` (`prove_columns`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## A table's sum -/

/-- What the row side reads at the index side's end: the challenges, the index point `r`'s
functionals, the memory term `M_1`, the fresh coefficients (the certificate's, then `JUMP`'s
identities'), the index arrays' values the coefficients take (`Y(r)`, `X_ω(r)`, `P_fp(r)`,
`eq(ζ, r)`, the shift's), and `eq(0, r)`. -/
structure RowInputs where
  ch : LinkChallenges
  functionals : Functionals
  maxShift : ℕ
  m1 : E
  cert : E
  jump : List E
  yMem : E
  xBc : E
  pFp : E
  eqZeta : E
  shiftZeta : E
  eq0 : E

/-- The functional `table` of chunk `i` at a word: the sum of the table over the chunk's set bits
(`eval_chunk`, `pointer.rs`). -/
def evalChunk (chunks : Chunks) (table : List E) (word i : ℕ) : E :=
  let bits := chunks.bits word i
  sumE ((table.zipIdx.filter fun (_, v) ↦ (bits >>> v) % 2 = 1).map (·.1))

/-- The functional `(chunk, table)` of a column's words, as a table over its rows. -/
def functionalTable (chunks : Chunks) (words : Array K) (f : ℕ × List E) : Array E :=
  let table := f.2
  words.map fun w ↦ evalChunk chunks table (kToNat w) f.1

/-- The accesses of table `t` at its pointer column `pointer`, with their `μ`. -/
def accessesAt (links : Links) (mu : List E) (pointer : ℕ) : List (Access × E) :=
  (links.memory.zip mu).filter (·.1.pointer = pointer)

/-- The shifts a pointer column's accesses read past their cells, each once, in order. -/
def shiftsAt (links : Links) (mu : List E) (pointer : ℕ) : List ℕ :=
  (accessesAt links mu pointer).foldl (fun ss (a, _) ↦
    if a.shift = 0 ∨ ss.contains a.shift then ss else ss ++ [a.shift]) []

/-- A pointer column's coefficient on `ω_F` (`c_ω`) and on `act_F` (`c_act`) at a row, for the
column `k` of a table's pointers (`RowColumn`, `prove.rs`): the cycle pointer's `c_act` is the
row's state and successor under the identity's weights at `r`; the program pointer's `c_ω` is
`X_ω(r) + P_fp(r)·fp`; a memory pointer's `c_ω` is its unshifted access's `η_mem·Y(r)·μ·gate` and
its word reads' `η_mem·γ_word·M_1·Σ μ·scale`. -/
def rowCoefs (inp : RowInputs) (links : Links) (mu : List E) (k pointer : ℕ) (col : ℕ → E) :
    E × E :=
  match k with
  | 0 =>
    let (s, s') := stateValues inp.ch links col
    (0, inp.eqZeta * s + inp.shiftZeta * s')
  | 1 => (inp.xBc + inp.pFp * col links.stateLink.fp, 0)
  | _ =>
    let c := inp.ch.etaMem * inp.yMem
    let direct := sumE ((accessesAt links mu pointer).map fun (a, m) ↦
      if a.shift = 0 then c * m * (a.gate.map col).getD 1 else 0)
    let wordCoef := inp.ch.etaMem * inp.ch.gammaMem.getD 1 0 * inp.m1
    let reads := sumE ((wordReads links mu 1).map fun (p, scale) ↦
      if p = pointer then wordCoef * scale.evaluate col else 0)
    (direct + reads, 0)

/-- **Table `t`'s sum over its rows** (`State`, `row.rs`; `Base`, `base.rs`), and the number of
its terms the pointer columns take (the base terms after them). The pointer column `q₀ + k` takes
the certificate weights `ε_{q₀ + k}·ν_i`. -/
def rowProds (W : Witness) (inp : RowInputs) (t q₀ : ℕ) : Prods × ℕ :=
  let ch := inp.ch
  let chunks := W.chunks
  let d := chunks.d
  let table := tables.getD t default
  let links := table.links
  let mu := ch.mu.getD t []
  let h := W.layout.tableLogHeights.getD t 0
  let n := W.rows.getD t 0
  let cols := W.tableCols t
  let width := table.width
  let omega := omegaTable (ch.theta.getD t 0) ch.tau h n
  let act := Array.ofFn (n := 2 ^ h) fun u ↦ if u.val < n then (1 : E) else 0
  let eqTau := eqTable (ch.tau.take h)
  let colTabs := (List.range width).map (columnE cols)
  let fTabs := inp.functionals.tables
  -- Per pointer column: its tables and its terms.
  let (tabs, terms, _) := links.pointers.zipIdx.foldl
    (fun (acc : Array (Array E) × Array (E × Array ℕ) × ℕ) (pointer, k) ↦
      let (tabs, terms, pos) := acc
      let words := cols.getD pointer #[]
      let coefs := Array.ofFn (n := 2 ^ h) fun u ↦ rowCoefs inp links mu k pointer (rowValue cols u)
      let shifts := shiftsAt links mu pointer
      let ds := (List.range (2 * d)).map fun i ↦ functionalTable chunks words (fTabs.getD i (0, []))
      let ts := shifts.map fun s ↦ functionalTable chunks words (fTabs.getD (2 * d + s - 1) (0, []))
      let tabs := tabs ++ #[coefs.map (·.1), coefs.map (·.2)] ++ ds.toArray ++ ts.toArray
      let (cω, cAct, dAt) := (pos, pos + 1, pos + 2)
      let rest := (List.range (d - 1)).map (dAt + 1 + ·)
      let terms := terms.push (1, (#[0, cω, dAt] ++ rest.toArray))
      let terms := terms.push (1, (#[1, cAct, dAt] ++ rest.toArray))
      let terms := (accessesAt links mu pointer).foldl (fun terms (a, m) ↦
        if a.shift = 0 then terms
        else
          let tAt := dAt + 2 * d + shifts.idxOf a.shift
          let gate := (a.gate.map fun g ↦ #[3 + g]).getD #[]
          terms.push (ch.etaMem * inp.yMem * m, #[0] ++ gate ++ #[tAt] ++ rest.toArray)) terms
      let e := inp.cert * ch.eps.getD (q₀ + k) 0
      let terms := (List.range d).foldl (fun terms i ↦
        let w := e * ch.nu.getD i 0
        (terms.push (w, #[0, dAt + i, dAt + d + i])).push
          (w * inp.functionals.mirrors.getD i 0, #[0])) terms
      (tabs, terms, pos + 2 + 2 * d + shifts.length))
    (#[omega, act, eqTau] ++ colTabs.toArray, #[], 3 + width)
  let nColumnTerms := terms.size
  -- The base terms: each block's monomials under its weight and gate.
  let base := (tableBlocks ch t inp.eq0 (some inp.jump)).foldl (fun terms b ↦
    let weight := if b.onEq then 2 else 0
    let gate := (b.gate.map fun g ↦ #[3 + g]).getD #[]
    b.form.terms.foldl (fun terms (vars, c) ↦
      terms.push (c, #[weight] ++ gate ++ (vars.map (3 + ·)).toArray)) terms) terms
  (⟨tabs, base⟩, nColumnTerms)

/-- A table through the row rounds: its sum, its height, the rounds bound so far, the corner factor
`Π (1 + x)` of the rounds past its height, and the number of its sum's column terms. -/
structure RowTable where
  prods : Prods
  height : ℕ
  bound : ℕ
  corner : E
  columnTerms : ℕ
  deriving Inhabited

/-- The row rounds' state: every table's. -/
abbrev RowState := Array RowTable

/-- A row round's polynomial, `count` coefficients (`round_poly`, `row.rs`): each table still bound
over its rows, and each bound table's value times its corner factor and `1 + X`. -/
def rowRound (count : ℕ) (st : RowState) : List E :=
  st.foldl (fun acc rt ↦
    let p := if rt.bound < rt.height then rt.prods.round count
      else
        let v := rt.prods.value * rt.corner
        v :: v :: List.replicate (count - 2) 0
    List.zipWith (· + ·) acc p) (List.replicate count 0)

/-- Bind the lowest row variable at `x`: a bound table only takes its corner factor. -/
def rowFold (st : RowState) (x : E) : RowState :=
  st.map fun rt ↦
    if rt.bound < rt.height then { rt with prods := rt.prods.fold x, bound := rt.bound + 1 }
    else { rt with corner := rt.corner * (1 + x) }

/-! ## The pointer columns -/

/-- A pointer column's 64 bit-slices at its table's row point `point`:
`Σ_u eq(point, u)·[bit b of word u]` (`Column::end`, `row.rs`). -/
def columnSlices (words : Array K) (point : List E) : List E :=
  let eq := eqTable point
  (List.range 64).map fun b ↦
    sumRange words.size fun u ↦ if (kToNat (words.getD u 0) >>> b) % 2 = 1 then eq.getD u 0 else 0

/-- One pointer column at the row point (`ColumnAt`, `row.rs`): its coefficient on `D_0`, on each
shift `s` (at `s - 1`), its values (`Functionals.values` of its slices) and its certificate
weights, each times its table's corner factor; and its slices. -/
structure ColumnAt where
  coef : E
  shifts : List E
  values : List E
  certs : List E
  slices : List E
  deriving Inhabited

/-- Table `t`'s pointer columns at the row point `χ` (`end_coefs`, `row.rs`), its sum bound there:
the coefficients read off its bound tables, the column's `q` from `q₀`. -/
def columnsAt (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable) (chi : List E) :
    List ColumnAt :=
  let ch := inp.ch
  let d := W.chunks.d
  let links := (tables.getD t default).links
  let mu := ch.mu.getD t []
  let cols := W.tableCols t
  let point := chi.take rt.height
  let width := (tables.getD t default).width
  let P := rt.prods
  let omega := P.at 0
  (links.pointers.zipIdx.foldl (fun (acc : List ColumnAt × ℕ) (pointer, k) ↦
    let (out, pos) := acc
    let slices := columnSlices (cols.getD pointer #[]) point
    let coef := omega * P.at pos + P.at 1 * P.at (pos + 1)
    let shifts := (List.range inp.maxShift).map fun s ↦
      sumE ((accessesAt links mu pointer).map fun (a, m) ↦
        if a.shift = s + 1 then
          ch.etaMem * inp.yMem * m * omega * ((a.gate.map fun g ↦ P.at (3 + g)).getD 1)
        else 0)
    let certs := (List.range d).map fun i ↦
      omega * inp.cert * ch.eps.getD (q₀ + k) 0 * ch.nu.getD i 0
    let c := rt.corner
    let column : ColumnAt := ⟨c * coef, shifts.map (c * ·),
      inp.functionals.values W.chunks slices, certs.map (c * ·), slices⟩
    (out ++ [column], pos + 2 + 2 * d + (shiftsAt links mu pointer).length))
    ([], 3 + width)).1

/-- The base terms' value of a bound table, its corner factor in. -/
def baseAt (rt : RowTable) : E :=
  let P := rt.prods
  rt.corner * ((P.terms.extract rt.columnTerms P.terms.size).foldl
    (fun acc (coef, factors) ↦ acc + factors.foldl (fun v f ↦ v * P.at f) coef) 0)

/-- **The pointer-column rounds' sum** (`prove_columns`, `row.rs`) over `2^qVars` columns: per
column `q`, `(c·D_0 + Σ_s c_s·T_s)·Π_{i ≥ 1} D_i + Σ_i e_i·(D_i·D̄_i + π_i)`, a column past the
last zero, and the base terms' total `B` as `eq(0, q)·B`. -/
def columnProds (d maxShift : ℕ) (mirrors : List E) (columns : List ColumnAt) (qVars : ℕ)
    (base : E) : Prods :=
  let Q := 2 ^ qVars
  let tab := fun (f : ColumnAt → E) ↦ Array.ofFn (n := Q) fun q ↦ f (columns.getD q.val default)
  let nValues := 2 * d + maxShift
  let coefT := tab (·.coef)
  let valueT := (List.range nValues).map fun j ↦ tab fun c ↦ c.values.getD j 0
  let shiftT := (List.range maxShift).map fun s ↦ tab fun c ↦ c.shifts.getD s 0
  let certT := (List.range d).map fun i ↦ tab fun c ↦ c.certs.getD i 0
  let baseT := (Array.replicate Q (0 : E)).set! 0 base
  -- Tables: the coefficient, the values, the shifts' coefficients, the certificates', the base.
  let vAt := 1
  let sAt := vAt + nValues
  let cAt := sAt + maxShift
  let bAt := cAt + d
  let rest := ((List.range (d - 1)).map (vAt + 1 + ·)).toArray
  let terms : Array (E × Array ℕ) := #[(1, #[0, vAt] ++ rest)] ++
    ((List.range maxShift).map fun s ↦ ((1 : E), #[sAt + s, vAt + 2 * d + s] ++ rest)).toArray ++
    ((List.range d).flatMap fun i ↦
      [((1 : E), #[cAt + i, vAt + i, vAt + d + i]), (mirrors.getD i 0, #[cAt + i])]).toArray ++
    #[(1, #[bAt])]
  ⟨#[coefT] ++ valueT.toArray ++ shiftT.toArray ++ certT.toArray ++ #[baseT], terms⟩

end LeanVM.Prover

end
