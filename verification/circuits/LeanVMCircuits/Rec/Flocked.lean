module

public import LeanVMCircuits.Rec.BusDraw
public import LeanVMCircuits.Rec.FlockZero
public import LeanVMCircuits.Rec.FlockLin
public import LeanVMCircuits.Rec.RingSwitch
public import LeanVMCircuits.Rec.CrScale
public import LeanVMCircuits.Rec.SideCert
public import LeanVMCircuits.Rec.GkrChain
public import LeanVMCircuits.Rec.HashRows

@[expose] public section

/-!
Flock's reduction over the `HASH` rows named whole on a replay and composed into the hash rows' packed witnesses (`AirLink.Flocked`).

`Bind.LagCert` names the lincheck's Lagrange weights at the skip challenge (`SkipDomain::lagrange_at`): per node `s_i` of `S` its `e_const`, `add(ζ, s_i)` and `inv`, and the scale `mul_const_add(V_S(ζ), D_64, 0, 0, zero)` reading the zerocheck's `V_S(ζ)`. `Bind.FlockCert` is a `ZeroCert`, a `LinCert`, a `RingCert` and a `LagCert`; `FlockCert.ok` checks each and their links: the lincheck's triple and inner point are the zerocheck's (`zeroLink`), the ring switch's slices are the lincheck's, and the Lagrange weights' inverses and scale are the lincheck's, read at the zerocheck's `ζ` and `V_S(ζ)`. `flocksOf` names the passing ones of a replay; `checkbind` asks one for every table sumcheck it names, on that sumcheck's transcript.

The tables on the packed region (`Flocked.ofBlocks`: in each block of `2^(6 + h)` bits, `a = A_0 y`, `b = B_0 y`, `c = y`), its bits `wordBits wd` of the committed words `wd`. `quirky_a`, `quirky_b`, `quirky_c`: at the zerocheck's challenges split into the inner point (the first `h`) and the outer point (the last `no`), the quirky extensions the zerocheck's triple claims are the lincheck's `u^T A_0 Z`, `u^T B_0 Z`, `u^T Z` with `u` the skip's Lagrange basis at `ζ` (`lzOf`) and `Z` the region folded at the outer point. `ring_slice`: the ring switch's slice of the region at `R ++ x_outer` is the lincheck's slice. `SkipCert.van_sem` and `LagCert.sem`: the lincheck's `scale · inv_i` is `L_i(ζ)`.

`Bind.flock_rows`: where the parent's calls hold, `FlockCert.ok` passes, both sumchecks' tests hold at challenges read from the oracle, the opening at the ring switch's target holds (`RingOpening`, the PCS's) and the deferred matrix claim holds (`LinCert.MatrixHolds`, the tree's matrix reduction's), no block of the region breaks a row and every block's pin is one, off the events: both sumchecks' `sumcheckFalse`, `alphaBad`, `pinBad`, `ringDraws`, `skipDraws` and `fixDraws`, each a run's draw event: `skipRun_frac` (`127/|E|`), `fixRun_frac` (`n'/|E|`), `ringRun_frac` (`phiDeg/|E|`, `phiDeg < 2^32`), with FlockLin's `alphaRun_frac` (`3/|E|`) and `pinRun_frac` (`no/|E|`). `Bind.flocked_of_rows`: with the `HASH` matrices the exported artifact's (`HashGates`: a block whose rows hold and whose pin is one has a witness of `Compress.artifact` with its first 14 words as ports and the next four as result) and the hash table's first 18 columns its blocks' first 18 words, those rows give `Flocked`. `Bind.hashGates`: `Hash::circuit`'s rows as flock's `Builder` lays them out (`LeanVMCircuits.Rec.HashRows`: `hashA0`, `hashB0`) are `HashGates` for blocks of at least `2^14` bits, by `HashRows.rows_sound` (the wires' values satisfy the artifact) with the ports bound as `Hash::circuit` binds them; `checkbind` asks each child's lincheck to run `Bind.hashRounds` rounds (`FlockCert.roundsOk`, with mutation tests), so its blocks are `2^14` bits.

`ringDraws` only counts wrong slices, so true slices meet no event. `Edges.flockDeg` adds the run fractions' numerators with the balance's (`allIds.length + 1`) and the two sumchecks' (degree two per round), at most `2^32` (`flockDeg_le`); `Edges.tree_bound_flock` is `tree_bound_deployed` with each child's degrees its other checks' (at most `2^39`) plus `flockDeg`.

`Edges.tableParts_certs`: `tableParts_ok` on the dumps' certificates (`ChildCerts`, passing `checkbind`'s checks, `ChildCerts.Ok`) at a run's outcomes (`RunHeld`: the parent's calls hold, each certified sumcheck's test holds and reads its challenges from the oracle, each GKR top and odd layer's test holds, and each transcript's squeezes answer the oracle). The bus GKR's layers' tests are `ChildCerts.layer_ok`'s off `ChildCerts.layerBad`: stage `j`'s named values (`ChildCerts.vals`) are the trees' levels at stage `j`'s point read from the oracle (`ChildCerts.tvals`, the trees' leaves the sides' stacked layers, `SideCert.stack`) where stage `j + 1`'s are, by `top_step` or `odd_step` for the first layer and `layer_step` past it (`LeanVMCircuits.Rec.GkrChain`), and at the leaves the stages are the chain's leaf claims and the sides' (`ChildCerts.leaves`). The balance's test is `balance_sides`' off `ChildCerts.balBad`, the table sumcheck's `table_part`'s off `tabBad` with its openings `tabOpened`, flock's `flock_rows` with `flocked_of_rows` and `hashGates` off `flBad` with its openings `flOpened` (the region's words on the cube, `RingOpening`, `MatrixHolds` on `Hash::circuit`'s matrices). The witness is the stack's (`Edges.ported`, `ChildCerts.wit`, `RecLayout::sources`): the hash table's first 18 columns are ports of the `HASH` region, word `c` of block `b` at row `b`, so they are the region's words by the layout; the hash rows lie within the region where the committed height holds them, `checkbind` asking the zerocheck to run over the residual's hash term's height (`FlockCert.heightOk`, with mutation tests). What stays a premise there: the openings off `pcsBad`, the residual's terms at the committed heights (whence each side's owned blocks, `ChildCerts.kappa_tau`), the hash table's committed height holding its rows (the layout's, `AirLink.LayoutFits`) and the sides' public coordinates (`SideCert.PubTrue`).
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Finset LeanVMCircuits.Rec.Flock

/-- `SkipDomain::lagrange_at`'s calls at `ζ`: per node `i` of `S` its `e_const`, `add(ζ, s_i)` and `inv`, and the scale's `zero` and `mul_const_add(V_S(ζ), D_64, 0, 0, zero)`. -/
structure LagCert where
  nodeAt : List ℕ := []
  diffAt : List ℕ := []
  invAt : List ℕ := []
  scaleZero : ℕ
  scaleAt : ℕ
  deriving Inhabited, Repr

namespace LagCert

variable (os : Array (List ℕ)) (lg : LagCert)

/-- Node `i`'s calls at `ζ`. -/
def nodeCalls (zeta i : ℕ) : List (ℕ × Call) :=
  [(lg.nodeAt.getD i 0, .eConst (sWords.getD i 0) 0 0), (lg.diffAt.getD i 0, .add zeta (o os (lg.nodeAt.getD i 0))),
    (lg.invAt.getD i 0, .inv (o os (lg.diffAt.getD i 0)))]

/-- The calls at `ζ` and `V_S(ζ)`. -/
def calls (zeta van : ℕ) : List (ℕ × Call) :=
  [(lg.scaleZero, .zero), (lg.scaleAt, .mulConstAdd van d64Word 0 0 (o os lg.scaleZero))] ++
    (List.range 64).flatMap (lg.nodeCalls os zeta)

/-- The calls are in the replay and their outputs are the lincheck's scale and inverses. -/
def okFor (cs : Array Call) (rl : Array Bool) (zeta van : ℕ) (lc : LinCert) : Bool :=
  callsOk cs rl (lg.calls os zeta van) && lc.scale == o os lg.scaleAt &&
    (List.range 64).all fun i => lc.invs.getD i 0 == o os (lg.invAt.getD i 0)

end LagCert

/-- Flock's reduction over the `HASH` rows: its zerocheck, lincheck, ring switch and Lagrange weights. -/
structure FlockCert where
  zero : ZeroCert
  lin : LinCert
  ring : RingCert
  lag : LagCert
  deriving Inhabited, Repr

/-- Each part passes its check and they are linked: the lincheck's triple and inner point are the zerocheck's, the ring switch's slices the lincheck's, and the Lagrange weights the lincheck's at the zerocheck's `ζ` and `V_S(ζ)`. -/
def FlockCert.ok (fc : FlockCert) (os : Array (List ℕ)) (scs : Array SumcheckCert) (cs : Array Call)
    (rl : Array Bool) : Bool :=
  fc.zero.okIn os scs cs rl && fc.lin.okIn os scs cs rl && fc.ring.okIn os cs rl &&
    (match scs[fc.zero.sc]? with
      | some zsc => fc.lin.zeroLink zsc fc.zero.tri
      | none => false) &&
    fc.ring.s == fc.lin.slices && fc.lag.okFor os cs rl fc.zero.skip.zeta (fc.zero.skip.van os) fc.lin

/-- The lincheck's rounds over a `HASH` instance's `64`-bit words: `Hash::circuit`'s instances are `2^14` bits
(`HashRows.rowsOf_slots`), `2^8` words. -/
def hashRounds : ℕ := 8

/-- The lincheck runs `hashRounds` rounds. -/
def FlockCert.roundsOk (fc : FlockCert) (scs : Array SumcheckCert) : Bool :=
  match scs[fc.lin.sc]? with
  | some lsc => lsc.rounds.length == hashRounds
  | none => false

theorem FlockCert.roundsOk_sem {fc : FlockCert} {scs : Array SumcheckCert} {lsc : SumcheckCert}
    (h : fc.roundsOk scs = true) (hl : scs[fc.lin.sc]? = some lsc) : lsc.rounds.length = hashRounds := by
  simpa [FlockCert.roundsOk, hl] using h

/-- Mutation tests of `FlockCert.roundsOk`: a lincheck of eight rounds passes, of seven or nine fails, and a lincheck
outside the certified sumchecks fails. -/
example : ({ (default : FlockCert) with lin := { (default : LinCert) with sc := 0 } } : FlockCert).roundsOk
    #[{ (default : SumcheckCert) with rounds := List.replicate 8 default }] = true := by decide
example : ({ (default : FlockCert) with lin := { (default : LinCert) with sc := 0 } } : FlockCert).roundsOk
    #[{ (default : SumcheckCert) with rounds := List.replicate 7 default }] = false := by decide
example : ({ (default : FlockCert) with lin := { (default : LinCert) with sc := 0 } } : FlockCert).roundsOk
    #[{ (default : SumcheckCert) with rounds := List.replicate 9 default }] = false := by decide
example : ({ (default : FlockCert) with lin := { (default : LinCert) with sc := 1 } } : FlockCert).roundsOk
    #[{ (default : SumcheckCert) with rounds := List.replicate 8 default }] = false := by decide

/-- The zerocheck runs over the hash table's height as the residual names it: `hashRounds` rounds over a block's words
and one per row bit (`Instance::n_blocks_log`, the layout's `τ`). -/
def FlockCert.heightOk (fc : FlockCert) (scs : Array SumcheckCert) (rc : ResidCert) : Bool :=
  match scs[fc.zero.sc]? with
  | some zsc => zsc.rounds.length == (rc.termOf .hash).tau + hashRounds
  | none => false

theorem FlockCert.heightOk_sem {fc : FlockCert} {scs : Array SumcheckCert} {rc : ResidCert} {zsc : SumcheckCert}
    (h : fc.heightOk scs rc = true) (hz : scs[fc.zero.sc]? = some zsc) :
    zsc.rounds.length = (rc.termOf .hash).tau + hashRounds := by
  simpa [FlockCert.heightOk, hz] using h

/-- Mutation tests of `FlockCert.heightOk`: a zerocheck of eleven rounds passes over a hash term of height three, of ten
or twelve fails, a hash term of height four fails, and a zerocheck outside the certified sumchecks fails. -/
example : ({ (default : FlockCert) with zero := { (default : ZeroCert) with sc := 0 } } : FlockCert).heightOk
    #[{ (default : SumcheckCert) with rounds := List.replicate 11 default }]
    { sc := 0, xi := 0, terms := List.replicate 5 { (default : TermCert) with tau := 3 } } = true := by decide
example : ({ (default : FlockCert) with zero := { (default : ZeroCert) with sc := 0 } } : FlockCert).heightOk
    #[{ (default : SumcheckCert) with rounds := List.replicate 10 default }]
    { sc := 0, xi := 0, terms := List.replicate 5 { (default : TermCert) with tau := 3 } } = false := by decide
example : ({ (default : FlockCert) with zero := { (default : ZeroCert) with sc := 0 } } : FlockCert).heightOk
    #[{ (default : SumcheckCert) with rounds := List.replicate 12 default }]
    { sc := 0, xi := 0, terms := List.replicate 5 { (default : TermCert) with tau := 3 } } = false := by decide
example : ({ (default : FlockCert) with zero := { (default : ZeroCert) with sc := 0 } } : FlockCert).heightOk
    #[{ (default : SumcheckCert) with rounds := List.replicate 11 default }]
    { sc := 0, xi := 0, terms := List.replicate 2 { (default : TermCert) with tau := 3 } ++
      [{ (default : TermCert) with tau := 4 }] ++ List.replicate 2 { (default : TermCert) with tau := 3 } } = false := by
  decide
example : ({ (default : FlockCert) with zero := { (default : ZeroCert) with sc := 1 } } : FlockCert).heightOk
    #[{ (default : SumcheckCert) with rounds := List.replicate 11 default }]
    { sc := 0, xi := 0, terms := List.replicate 5 { (default : TermCert) with tau := 3 } } = false := by decide

/-! Naming the reduction on a replay. -/

/-- The Lagrange weights behind a lincheck's inverses and scale, at `ζ`. -/
def lagOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (zeta : ℕ) (lc : LinCert) : Option LagCert := Id.run do
  let mut nodeAt : List ℕ := []
  let mut diffAt : List ℕ := []
  let mut invAt : List ℕ := []
  for i in [0:64] do
    let some (ia, d) := makerBy rp idx (lc.invs.getD i 0) (fun j c => match c with
      | .inv d => some (j, d)
      | _ => none) | return none
    let some (da, nw) := makerBy rp idx d (fun j c => match c with
      | .add z nw => if z = zeta then some (j, nw) else none
      | _ => none) | return none
    let some na := makerBy rp idx nw (fun j c => match c with
      | .eConst .. => some j
      | _ => none) | return none
    nodeAt := nodeAt ++ [na]
    diffAt := diffAt ++ [da]
    invAt := invAt ++ [ia]
  let some (scaleAt, zw) := makerBy rp idx lc.scale (fun j c => match c with
    | .mulConstAdd _ _ 0 0 z => some (j, z)
    | _ => none) | return none
  let some scaleZero := zeroAt rp idx zw | return none
  return some { nodeAt, diffAt, invAt, scaleZero, scaleAt }

/-- The flock reductions of a replay's certified sumchecks `scs`, read with the outputs `os` and the relaxed calls `rl`: each passing zerocheck with the lincheck linked to it, the ring switch of that lincheck's slices and its Lagrange weights, kept where `FlockCert.ok` passes. -/
def flocksOf (rp : Replay) (scs : Array SumcheckCert) (os : Array (List ℕ)) (rl : Array Bool) : Array FlockCert :=
  let idx := outIndex rp
  let rings := RingCert.find rp rl
  let lins := (List.range scs.size).filterMap fun i => match scs[i]? with
    | some sc => if sc.resid.isEmpty && sc.deg == 2 && sc.rounds.all (·.weight.isNone) then linOf rp idx os i sc
        else none
    | none => none
  ((zerosOf rp scs os rl).toList.filterMap fun zc => do
    let zsc ← scs[zc.sc]?
    let lin ← lins.find? (·.zeroLink zsc zc.tri)
    let ring ← rings.find? (·.s == lin.slices)
    let lag ← lagOf rp idx zc.skip.zeta lin
    let fc : FlockCert := { zero := zc, lin, ring, lag }
    if fc.ok os scs rp.calls rl then some fc else none).toArray

end LeanVMCircuits.Rec.Bind

/-! The reduction's tables on the packed region. -/

namespace LeanVMCircuits.Rec.Flocked

open LeanVMCircuits.Rec Model Finset Sumcheck AirLink LeanVMCircuits.Rec.Flock FlockLin

/-- The skip's Lagrange basis at `ζ` by node index, `L_i(ζ)`. -/
noncomputable def lzOf (ζ : E) (i : ℕ) : E := if h : i < 64 then (lagS ⟨i, h⟩).eval ζ else 0

/-- The tables of blocks of `2^k` bits: in each block `a = A_0 y`, `b = B_0 y` and `c = y`, `y` the block's bits. -/
def ofBlocks (k : ℕ) (A0 B0 : ℕ → ℕ → ZMod 2) (z : ℕ → ZMod 2) : Tables where
  a u := ∑ col ∈ range (2 ^ k), A0 (u % 2 ^ k) col * z (col + 2 ^ k * (u / 2 ^ k))
  b u := ∑ col ∈ range (2 ^ k), B0 (u % 2 ^ k) col * z (col + 2 ^ k * (u / 2 ^ k))
  c := z

/-- The `HASH` circuit's base matrices in `E`, with its pin. -/
noncomputable def hashMats (A0 B0 : ℕ → ℕ → ZMod 2) : Mats :=
  ⟨fun r c => bitE (A0 r c), fun r c => bitE (B0 r c), Bind.hashPin⟩

/-- Slice `i` of inner word `J` of block `t` of a table, blocks of `2^h` words. -/
noncomputable def sliceQ (h : ℕ) (t : ℕ → ZMod 2) (i J b : ℕ) : E := bitE (t (i + 64 * J + 2 ^ (6 + h) * b))

/-- The bits of a region of words: bit `u % 64` of word `u / 64`. -/
noncomputable def wordBits (wd : ℕ → K) (u : ℕ) : ZMod 2 := coeff (wd (u / 64)) (u % 64)

/-- The first `h` coordinates of a point of `h + no`. -/
def inPt {n h no : ℕ} (hn : n = h + no) (χ : Fin n → E) : Fin h → E := fun j => χ (Fin.cast hn.symm (Fin.castAdd no j))

/-- The last `no` coordinates. -/
def outPt {n h no : ℕ} (hn : n = h + no) (χ : Fin n → E) : Fin no → E :=
  fun j => χ (Fin.cast hn.symm (Fin.natAdd h j))

theorem nc_eq (h : ℕ) : nc h = 2 ^ (6 + h) := by
  unfold nc
  rw [pow_add]
  ring

theorem split_pt {h no : ℕ} (χ : Fin (h + no) → E) : χ = Fin.append (inPt rfl χ) (outPt rfl χ) :=
  funext fun x => Fin.addCases (fun j => by rw [Fin.append_left]; rfl) (fun j => by rw [Fin.append_right]; rfl) x

theorem pos_split {h : ℕ} (i z : ℕ) : i + 64 * (z % 2 ^ h) + 2 ^ (6 + h) * (z / 2 ^ h) = i + 64 * z := by
  have := Nat.mod_add_div z (2 ^ h)
  rw [pow_add]
  calc i + 64 * (z % 2 ^ h) + 2 ^ 6 * 2 ^ h * (z / 2 ^ h) = i + 64 * (z % 2 ^ h + 2 ^ h * (z / 2 ^ h)) := by ring
    _ = i + 64 * z := by rw [this]

/-- A slice's extension at a point of `h + no` is the outer fold's inner extension. -/
theorem eval_slice {n h no : ℕ} (hn : n = h + no) (χ : Fin n → E) (t : ℕ → ZMod 2) (i : ℕ) :
    MvPolynomial.eval χ (Flock.sliceMle n t i) = mleAt h (inPt hn χ) (outerFold no (outPt hn χ) (sliceQ h t) i) := by
  subst hn
  rw [← slice_mle, ← split_pt]
  simp only [Flock.sliceMle, map_sum, map_mul, MvPolynomial.eval_C, eval_eqPoly_eqv, mleAt, sliceQ, pos_split]

/-- The quirky extension at `(ζ, χ)` as the rows' weights against the outer-folded slices. -/
theorem quirky_eval {n h no : ℕ} (hn : n = h + no) (χ : Fin n → E) (t : ℕ → ZMod 2) (ζ : E) :
    MvPolynomial.eval χ (quirky n t ζ) =
      ∑ row ∈ range (nc h), rowW (lzOf ζ) (inPt hn χ) row * outerFold no (outPt hn χ) (sliceQ h t) (row % 64) (row / 64) := by
  simp only [quirky, map_sum, map_mul, MvPolynomial.eval_C, eval_slice hn, mleAt, mul_sum]
  rw [sum_cols]
  have e : ∀ J ∈ range (2 ^ h), ∀ i ∈ range 64, rowW (lzOf ζ) (inPt hn χ) (64 * J + i) *
      outerFold no (outPt hn χ) (sliceQ h t) ((64 * J + i) % 64) ((64 * J + i) / 64) =
      lzOf ζ i * (eqv (inPt hn χ) (bitPoint h J) * outerFold no (outPt hn χ) (sliceQ h t) i J) := fun J _ i hi => by
    have hi' := mem_range.mp hi
    rw [rowW_split _ _ J hi', show (64 * J + i) % 64 = i by omega, show (64 * J + i) / 64 = J by omega]
    ring
  rw [sum_congr rfl fun J hJ => sum_congr rfl (e J hJ), sum_comm]
  refine sum_congr rfl fun J _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun i =>
    lzOf ζ i * (eqv (inPt hn χ) (bitPoint h J) * outerFold no (outPt hn χ) (sliceQ h t) i J))]
  refine sum_congr rfl fun x _ => ?_
  rw [lzOf, dif_pos x.isLt]

/-- At the inner and outer points, the zerocheck's `c* = z*` is the lincheck's `u^T Z`. -/
theorem quirky_c {n h no : ℕ} (hn : n = h + no) (χ : Fin n → E) (A0 B0 : ℕ → ℕ → ZMod 2) (z : ℕ → ZMod 2) (ζ : E) :
    MvPolynomial.eval χ (quirky n (ofBlocks (6 + h) A0 B0 z).c ζ) =
      triC (lzOf ζ) (inPt hn χ) (outerFold no (outPt hn χ) (sliceQ h z)) := by
  rw [quirky_eval hn]
  rfl

/-- A packed table's `a` on block `b` at row `row`. -/
theorem bitE_a {k : ℕ} (A0 B0 : ℕ → ℕ → ZMod 2) (z : ℕ → ZMod 2) {row : ℕ} (hrow : row < 2 ^ k) (b : ℕ) :
    bitE ((ofBlocks k A0 B0 z).a (row + 2 ^ k * b)) = ∑ col ∈ range (2 ^ k), bitE (A0 row col) * bitE (z (col + 2 ^ k * b)) := by
  have hp : 0 < 2 ^ k := by positivity
  have e1 : (row + 2 ^ k * b) % 2 ^ k = row := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have e2 : (row + 2 ^ k * b) / 2 ^ k = b := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hrow, zero_add]
  simp only [ofBlocks, e1, e2, map_sum, map_mul]

theorem bitE_b {k : ℕ} (A0 B0 : ℕ → ℕ → ZMod 2) (z : ℕ → ZMod 2) {row : ℕ} (hrow : row < 2 ^ k) (b : ℕ) :
    bitE ((ofBlocks k A0 B0 z).b (row + 2 ^ k * b)) = ∑ col ∈ range (2 ^ k), bitE (B0 row col) * bitE (z (col + 2 ^ k * b)) := by
  have hp : 0 < 2 ^ k := by positivity
  have e1 : (row + 2 ^ k * b) % 2 ^ k = row := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have e2 : (row + 2 ^ k * b) / 2 ^ k = b := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hrow, zero_add]
  simp only [ofBlocks, e1, e2, map_sum, map_mul]

/-- A row's outer fold of a matrix's product is the matrix row against the folded witness. -/
theorem fold_mat {h no : ℕ} (xo : Fin no → E) (M0 : ℕ → ℕ → ZMod 2) (t z : ℕ → ZMod 2) {row : ℕ}
    (ht : ∀ b, bitE (t (row + 2 ^ (6 + h) * b)) =
      ∑ col ∈ range (2 ^ (6 + h)), bitE (M0 row col) * bitE (z (col + 2 ^ (6 + h) * b))) :
    outerFold no xo (sliceQ h t) (row % 64) (row / 64) =
      ∑ col ∈ range (nc h), bitE (M0 row col) * colZ (outerFold no xo (sliceQ h z)) col := by
  simp only [outerFold, colZ, sliceQ, mul_sum]
  have hr : row % 64 + 64 * (row / 64) = row := Nat.mod_add_div row 64
  simp only [hr, ht, mul_sum, nc_eq]
  rw [sum_comm]
  refine sum_congr rfl fun col _ => sum_congr rfl fun b _ => ?_
  rw [Nat.mod_add_div col 64]
  ring

/-- At the inner and outer points, the zerocheck's `a*` is the lincheck's `u^T A_0 Z`. -/
theorem quirky_a {n h no : ℕ} (hn : n = h + no) (χ : Fin n → E) (A0 B0 : ℕ → ℕ → ZMod 2) (z : ℕ → ZMod 2) (ζ : E) :
    MvPolynomial.eval χ (quirky n (ofBlocks (6 + h) A0 B0 z).a ζ) =
      triA (hashMats A0 B0) (lzOf ζ) (inPt hn χ) (outerFold no (outPt hn χ) (sliceQ h z)) := by
  rw [quirky_eval hn, triA]
  refine sum_congr rfl fun row hrow => ?_
  have hr := mem_range.mp hrow
  rw [fold_mat (outPt hn χ) A0 _ z fun b => bitE_a A0 B0 z (by rwa [← nc_eq]) b]
  rfl

/-- At the inner and outer points, the zerocheck's `b*` is the lincheck's `u^T B_0 Z`. -/
theorem quirky_b {n h no : ℕ} (hn : n = h + no) (χ : Fin n → E) (A0 B0 : ℕ → ℕ → ZMod 2) (z : ℕ → ZMod 2) (ζ : E) :
    MvPolynomial.eval χ (quirky n (ofBlocks (6 + h) A0 B0 z).b ζ) =
      triB (hashMats A0 B0) (lzOf ζ) (inPt hn χ) (outerFold no (outPt hn χ) (sliceQ h z)) := by
  rw [quirky_eval hn, triB]
  refine sum_congr rfl fun row hrow => ?_
  have hr := mem_range.mp hrow
  rw [fold_mat (outPt hn χ) B0 _ z fun b => bitE_b A0 B0 z (by rwa [← nc_eq]) b]
  rfl

theorem bitE_coeff (w : K) (i : ℕ) : bitE (coeff w i) = RingSwitch.bitE w i := by
  rcases zmod2_cases (coeff w i) with h | h <;> simp [RingSwitch.bitE, h]

/-- The ring switch's slice of a region of words at `R ++ x_outer` is the lincheck's slice: the outer fold's inner extension at `R`. -/
theorem ring_slice {h no : ℕ} (wd : ℕ → K) (q : (Fin (h + no) → E) → K)
    (hq : ∀ v < 2 ^ (h + no), q (bitPoint (h + no) v) = wd v) (R : Fin h → E) (xo : Fin no → E) {i : ℕ}
    (hi : i < 64) :
    RingSwitch.sliceMle q (Fin.append R xo) i = mleAt h R (outerFold no xo (sliceQ h (wordBits wd)) i) := by
  rw [← slice_mle, RingSwitch.sliceMle, sum_cube_bits, mleAt]
  refine sum_congr rfl fun v hv => ?_
  rw [hq v (mem_range.mp hv), sliceQ, pos_split, wordBits, ← bitE_coeff]
  congr 4 <;> omega

end LeanVMCircuits.Rec.Flocked

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Finset Sumcheck AirLink LeanVMCircuits.Rec.Flock FlockLin Flocked LeanVMCircuits.Blake2s

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

/-- The skip's `V_S(ζ)`: where its calls hold, the fold from `ζ^64` is the vanishing polynomial at `ζ`. -/
theorem SkipCert.van_sem (hF : Facts cs rl os st val) {k : SkipCert} (h : k.ok os cs rl = true) :
    Model.ev val (k.van os) = vanS.eval (Model.ev val k.zeta) := by
  simp only [SkipCert.ok, SkipCert.okWith, SkipCert.callsWith, callsOk_append, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hsq, hvan⟩, -⟩, -⟩ := h
  set ζ := Model.ev val k.zeta with hζ
  have hpow : ∀ j ≤ 6, Model.ev val (k.pow os j) = ζ ^ 2 ^ j := by
    intro j hj
    induction j with
    | zero => simp [SkipCert.pow, hζ]
    | succ j ih =>
      have hc := callsOk_mem hsq (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)
      have hj' : Model.ev val (o os (k.sqAt.getD j 0)) = Model.ev val (k.pow os j) * Model.ev val (k.pow os j) :=
        holds_of_mem hF hc (List.mem_singleton_self _)
      have hp : k.pow os (j + 1) = o os (k.sqAt.getD j 0) := by simp [SkipCert.pow]
      rw [hp, hj', ih (by omega), ← sq, ← pow_mul, ← pow_succ]
  have hvacc : ∀ j ≤ 6, Model.ev val (k.vacc os j) = ζ ^ 64 + ∑ i ∈ range j, kw (vc i) * ζ ^ 2 ^ i := by
    intro j hj
    induction j with
    | zero =>
      rw [show k.vacc os 0 = k.pow os 6 from if_pos rfl, hpow 6 le_rfl, sum_range_zero, add_zero]
      norm_num
    | succ j ih =>
      have hc := callsOk_mem hvan (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)
      have hp : k.vacc os (j + 1) = o os (k.vanAt.getD j 0) := by simp [SkipCert.vacc]
      rw [hp, ev_mulConstAdd_K hF hc, ih (by omega), hpow j (by omega), sum_range_succ]
      simp only [vc]
      ring
  rw [SkipCert.van, hvacc 6 le_rfl, vanS_eval]

/-- The lincheck's Lagrange weights: where `LagCert.okFor` passes at the skip's `ζ` and `V_S(ζ)`, the lincheck's `scale · inv_i` is `L_i(ζ)` (`lagS_eval`). -/
theorem LagCert.sem (hF : Facts cs rl os st val) {lg : LagCert} {zeta van : ℕ} {lc : LinCert}
    (h : lg.okFor os cs rl zeta van lc = true) (hvan : Model.ev val van = vanS.eval (Model.ev val zeta)) :
    ∀ i < 64, Model.ev val lc.scale * Model.ev val (lc.invs.getD i 0) = lzOf (Model.ev val zeta) i := by
  simp only [LagCert.okFor, LagCert.calls, callsOk_append, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨hhead, hnodes⟩, hsc⟩, hinv⟩ := h
  intro i hi
  have hm : ∀ x ∈ lg.nodeCalls os zeta i, callsOk cs rl [x] = true := fun x hx =>
    callsOk_mem hnodes (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hx⟩)
  have hn := ev_eConst_K hF (hm (lg.nodeAt.getD i 0, .eConst (sWords.getD i 0) 0 0) (by simp [LagCert.nodeCalls]))
  have hd : Model.ev val (o os (lg.diffAt.getD i 0)) = Model.ev val zeta + Model.ev val (o os (lg.nodeAt.getD i 0)) :=
    holds_of_mem hF (hm (lg.diffAt.getD i 0, .add zeta (o os (lg.nodeAt.getD i 0))) (by simp [LagCert.nodeCalls]))
      (List.mem_singleton_self _)
  have hv : Model.ev val (o os (lg.diffAt.getD i 0)) * Model.ev val (o os (lg.invAt.getD i 0)) = 1 :=
    holds_of_mem hF (hm (lg.invAt.getD i 0, .inv (o os (lg.diffAt.getD i 0))) (by simp [LagCert.nodeCalls]))
      (List.mem_singleton_self _)
  have hz : Model.ev val (o os lg.scaleZero) = 0 :=
    holds_of_mem hF hhead (List.mem_cons_self ..)
  have hs := ev_mulConstAdd_K hF (callsOk_mem hhead
    (show (lg.scaleAt, Call.mulConstAdd van d64Word 0 0 (o os lg.scaleZero)) ∈ _ by simp))
  have hh : (Model.ev val zeta + sNode ⟨i, hi⟩) * Model.ev val (o os (lg.invAt.getD i 0)) = 1 := by
    rw [← hv, hd, hn]
    rfl
  rw [hsc, hinv i hi, hs, hz, add_zero, hvan, lzOf, dif_pos hi, ← lagS_eval ⟨i, hi⟩ hh]
  ring

theorem LinCert.xin_length {lc : LinCert} {scs : Array SumcheckCert} {sc : SumcheckCert}
    (h : lc.okIn os scs cs rl = true) (hsc : scs[lc.sc]? = some sc) : lc.xin.length = sc.rounds.length := by
  unfold LinCert.okIn at h
  rw [hsc] at h
  simp only [LinCert.shapeOk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.2

end Sem

/-- The parts of a passing `FlockCert`. -/
theorem FlockCert.ok_parts {fc : FlockCert} {os : Array (List ℕ)} {scs : Array SumcheckCert} {cs : Array Call}
    {rl : Array Bool} (h : fc.ok os scs cs rl = true) {zsc : SumcheckCert} (hz : scs[fc.zero.sc]? = some zsc) :
    fc.zero.okIn os scs cs rl = true ∧ fc.lin.okIn os scs cs rl = true ∧ fc.ring.okIn os cs rl = true ∧
      fc.lin.zeroLink zsc fc.zero.tri = true ∧ fc.ring.s = fc.lin.slices ∧
      fc.lag.okFor os cs rl fc.zero.skip.zeta (fc.zero.skip.van os) fc.lin = true := by
  simp only [FlockCert.ok, hz, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A word region's bits from block `b` on, blocks of `2^h` words. -/
theorem wordBits_block (wd : ℕ → K) (h u b : ℕ) :
    wordBits wd (u + 2 ^ (6 + h) * b) = wordBits (fun J => wd (J + 2 ^ h * b)) u := by
  have e : u + 2 ^ (6 + h) * b = u + 64 * (2 ^ h * b) := by rw [pow_add]; ring
  simp only [wordBits, e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 64), Nat.add_mul_mod_self_left]

open Classical in
/-- The ring switch's draw event: the claimed slices differ from the true ones by `δ ≠ 0`, yet the map draws cancel the error in the target (`RingSwitch.ringBad`). -/
noncomputable def ringDraws (δ : Fin 64 → E) : Finset (Fin 6 → E) := {f | δ ≠ 0 ∧ f ∈ RingSwitch.ringBad δ}

/-- At most `phiDeg · |E|^5` of the `|E|^6` map draws (`RingSwitch.ringBad_card`, Annex A). -/
theorem ringDraws_card (δ : Fin 64 → E) : #(ringDraws δ) ≤ RingSwitch.phiDeg * Fintype.card E ^ 5 := by
  by_cases hδ : δ = 0
  · have : ringDraws δ = ∅ := by
      ext f
      simp [ringDraws, hδ]
    rw [this, card_empty]
    exact Nat.zero_le _
  · refine le_trans (card_le_card fun f hf => ?_) (RingSwitch.ringBad_card δ hδ)
    simp only [ringDraws, mem_filter, mem_univ, true_and] at hf
    exact hf.2

/-- Non-vacuity: true slices put no draw in the event. -/
example : ringDraws 0 = ∅ := by
  ext f
  simp [ringDraws]

/-- Flock's reduction on the `HASH` rows, composed: where the parent's calls hold and `FlockCert.ok` passes, the zerocheck's and lincheck's tests hold at challenges read from the oracle, the opening of the committed region `wd` at `R ++ x_outer` is the ring switch's target (`RingOpening`, the PCS's) and the deferred matrix claim holds (`LinCert.MatrixHolds`), every block of the region holds its rows (`Viol` of the tables `ofBlocks`, `a = A_0 y`, `b = B_0 y`, `c = y`) and its pin, off the events: the two sumchecks' `sumcheckFalse`, `α`'s `alphaBad`, the pin's `pinBad`, the ring switch's `ringDraws`, the skip's `skipDraws` and the fixed coordinates' `fixDraws`. The inner point is the zerocheck's first `h` challenges (`h` the lincheck's rounds), the outer point its last `no`. -/
theorem flock_rows {c : Cert} {s : State} {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)}
    {st : ℕ → Fin 4 → K} {val : (ℕ → K) → Val} {fc : FlockCert} {zsc lsc : SumcheckCert} {T1 T2 : ℕ → E} {no : ℕ}
    (ρ : ℕ → K) (hF : Facts cs rl os st (val ρ)) (hok : fc.ok os c.sumchecks cs rl = true)
    (hz : c.sumchecks[fc.zero.sc]? = some zsc) (hl : c.sumchecks[fc.lin.sc]? = some lsc)
    (hno : zsc.rounds.length = lsc.rounds.length + no) (A0 B0 : ℕ → ℕ → ZMod 2) (wd : ℕ → K)
    (q : (Fin (lsc.rounds.length + no) → E) → K)
    (hq : ∀ v < 2 ^ (lsc.rounds.length + no), q (bitPoint (lsc.rounds.length + no) v) = wd v)
    (hchalZ : ∀ j : Fin zsc.rounds.length,
      Model.ev (val ρ) (zsc.rounds.getD j default).chal = readR (chalWords c.outs zsc.chals) ρ j)
    (htestZ : ∀ a b, s.unions[zsc.test]? = some (a, b) → val ρ a = val ρ b)
    (hchalL : ∀ j : Fin lsc.rounds.length,
      Model.ev (val ρ) (lsc.rounds.getD j default).chal = readR (chalWords c.outs lsc.chals) ρ j)
    (htestL : ∀ a b, s.unions[lsc.test]? = some (a, b) → val ρ a = val ρ b)
    (hhintL : ∀ w ∈ lsc.hints, Model.ev (val ρ) w = T2 w)
    (hop : RingSwitch.RingOpening q (Fin.append (chi (roundV (val ρ) lsc)) (outPt hno (zsc.chalPt (val ρ))))
      (fc.ring.fV os (val ρ)) (Model.ev (val ρ) (fc.ring.target os)))
    (hmat : fc.lin.MatrixHolds (val ρ) lsc (hashMats A0 B0) (lzOf (fc.zero.zeta (val ρ)))
      (inPt hno (zsc.chalPt (val ρ))))
    (hnotZ : ¬ sumcheckFalse c s zsc (zeroInst zsc.rounds.length (zsc.weightPt (val ρ))
      (ofBlocks (6 + lsc.rounds.length) A0 B0 (wordBits wd)) (fc.zero.zeta (val ρ))) T1 val ρ)
    (hnotL : ¬ sumcheckFalse c s lsc (linInst lsc.rounds.length (hashMats A0 B0) (lzOf (fc.zero.zeta (val ρ)))
      (inPt hno (zsc.chalPt (val ρ))) (outerFold no (outPt hno (zsc.chalPt (val ρ))) (sliceQ lsc.rounds.length
        (wordBits wd))) (Model.ev (val ρ) fc.lin.alpha)) T2 val ρ)
    (hα : Model.ev (val ρ) fc.lin.alpha ∉ alphaBad (diff ![Model.ev (val ρ) fc.lin.a, Model.ev (val ρ) fc.lin.b,
      Model.ev (val ρ) fc.lin.c]
      ![triA (hashMats A0 B0) (lzOf (fc.zero.zeta (val ρ))) (inPt hno (zsc.chalPt (val ρ)))
          (outerFold no (outPt hno (zsc.chalPt (val ρ))) (sliceQ lsc.rounds.length (wordBits wd))),
        triB (hashMats A0 B0) (lzOf (fc.zero.zeta (val ρ))) (inPt hno (zsc.chalPt (val ρ)))
          (outerFold no (outPt hno (zsc.chalPt (val ρ))) (sliceQ lsc.rounds.length (wordBits wd))),
        triC (lzOf (fc.zero.zeta (val ρ))) (inPt hno (zsc.chalPt (val ρ)))
          (outerFold no (outPt hno (zsc.chalPt (val ρ))) (sliceQ lsc.rounds.length (wordBits wd)))]
      (pinV (hashMats A0 B0) (outerFold no (outPt hno (zsc.chalPt (val ρ)))
        (sliceQ lsc.rounds.length (wordBits wd))))))
    (hpinE : outPt hno (zsc.chalPt (val ρ)) ∉
      pinBad no (fun b => sliceQ lsc.rounds.length (wordBits wd) (hashPin % 64) (hashPin / 64) b))
    (hringE : fc.ring.fV os (val ρ) ∉ ringDraws fun i => fc.ring.sV (val ρ) i -
      RingSwitch.sliceMle q (Fin.append (chi (roundV (val ρ) lsc)) (outPt hno (zsc.chalPt (val ρ)))) i)
    (hskip : fc.zero.zeta (val ρ) ∉ skipDraws (phat (fc.zero.msg (val ρ)))
      (honestP zsc.rounds.length (zsc.weightPt (val ρ)) (ofBlocks (6 + lsc.rounds.length) A0 B0 (wordBits wd))))
    (hfix : fc.zero.outerPt (val ρ) ∉ fixDraws fc.zero.outer.length
      (ofBlocks (6 + lsc.rounds.length) A0 B0 (wordBits wd))) :
    ¬ Viol zsc.rounds.length (ofBlocks (6 + lsc.rounds.length) A0 B0 (wordBits wd)) ∧
      ∀ b < 2 ^ no, wordBits wd (hashPin + 2 ^ (6 + lsc.rounds.length) * b) = 1 := by
  obtain ⟨hzok, hlok, hrok, hlink, hslices, hlag⟩ := FlockCert.ok_parts hok hz
  set χ := zsc.chalPt (val ρ)
  set xin := inPt hno χ
  set xo := outPt hno χ
  set Zv := outerFold no xo (sliceQ lsc.rounds.length (wordBits wd))
  set ζ := fc.zero.zeta (val ρ)
  have hlen := LinCert.xin_length hlok hl
  simp only [LinCert.zeroLink, Bool.and_eq_true, beq_iff_eq] at hlink
  obtain ⟨htri, hxin⟩ := hlink
  -- The inner point is the zerocheck's first challenges.
  have hx : ∀ k : Fin lsc.rounds.length, Model.ev (val ρ) (fc.lin.xin.getD k 0) = xin k := by
    intro k
    have hk : (k : ℕ) < zsc.rounds.length := by omega
    have e : fc.lin.xin.getD k 0 = (zsc.rounds.getD k default).chal := by
      rw [hxin, hlen]
      simp [List.getD_eq_getElem?_getD, hk]
    rw [e]
    rfl
  -- The Lagrange weights at `ζ`.
  obtain ⟨-, -, -, -, -, -, -, -, hskipok⟩ := ZeroCert.okIn_parts hzok hz
  have hlz := LagCert.sem hF hlag (SkipCert.van_sem hF hskipok)
  -- The slices, by the ring switch.
  have hs : ∀ i < 64, Model.ev (val ρ) (fc.lin.slices.getD i 0) =
      mleAt lsc.rounds.length (chi (roundV (val ρ) lsc)) (Zv i) := by
    have hall : ∀ i : Fin 64, fc.ring.sV (val ρ) i =
        RingSwitch.sliceMle q (Fin.append (chi (roundV (val ρ) lsc)) xo) i := by
      rcases RingCert.sound hF hrok q _ hop with hall | hbad
      · exact hall
      · by_contra hne
        push Not at hne
        obtain ⟨i, hi⟩ := hne
        refine hringE ?_
        simp only [ringDraws, mem_filter, mem_univ, true_and]
        exact ⟨fun h0 => hi (sub_eq_zero.mp (congrFun h0 i)), hbad⟩
    intro i hi
    have := hall ⟨i, hi⟩
    simp only [RingCert.sV, hslices] at this
    rw [this, ring_slice wd q hq _ xo hi]
  have hpin : (hashMats A0 B0).pin = fc.lin.pin := (LinCert.shape hlok hl).2.2.2.1.symm
  have hin := lin_part ρ hF hlok hl (hashMats A0 B0) (lzOf ζ) xin Zv hpin hlz hx hchalL htestL hhintL hs hmat hnotL
  obtain ⟨ha, hb, hc, hp⟩ := lin_triple hF hlok hl (hashMats A0 B0) (lzOf ζ) xin Zv hpin hin hα
  refine ⟨zero_rows ρ hF hzok hz _ hchalZ htestZ ?_ ?_ ?_ hnotZ hskip hfix, ?_⟩
  · rw [← htri]
    exact ha.trans (quirky_a hno χ A0 B0 (wordBits wd) ζ).symm
  · rw [← htri]
    exact hb.trans (quirky_b hno χ A0 B0 (wordBits wd) ζ).symm
  · rw [← htri]
    exact hc.trans (quirky_c hno χ A0 B0 (wordBits wd) ζ).symm
  · intro b hb'
    have hrows := pin_rows hpinE hp b hb'
    simp only [sliceQ, show hashPin % 64 + 64 * (hashPin / 64) = hashPin by decide] at hrows
    exact (algebraMap (ZMod 2) E).injective (hrows.trans (map_one _).symm)

/-- The `HASH` circuit's base matrices are its exported artifact's rows (`Hash::circuit`'s gate list, `flock::clean::blake2s`, generated from `Compress.artifact`): a block of `2^k` bits, words `W`, whose rows all hold and whose pin bit is one has a witness of the artifact with its first 14 words as ports and its next four as result. -/
def HashGates (k : ℕ) (A0 B0 : ℕ → ℕ → ZMod 2) : Prop :=
  ∀ W : ℕ → K, (∀ row < 2 ^ k, (ofBlocks k A0 B0 (wordBits W)).row row = 0) → wordBits W hashPin = 1 →
    ∃ a, Compress.artifact.Holds a ∧ Export.ports a = (portsOf fun j => columnWord W j) ∧
      Export.result a = resultOf fun j => columnWord W (hashO + j)

/-- A port word's bit `b` is its column's coefficient `b`, bit `64 j + b` of the block. -/
theorem columnWord_bit (W : ℕ → K) (j b : ℕ) (hb : b < 64) :
    (if (columnWord W j).getLsbD b then (1 : Bit) else 0) = wordBits W (64 * j + b) := by
  have e1 : (64 * j + b) / 64 = j := by omega
  have e2 : (64 * j + b) % 64 = b := by omega
  simp only [columnWord, BitVec.getLsbD_ofNat, LeanVMCircuits.Rec.toWord, testBit_num _ _ _ hb, wordBits, e1, e2,
    decide_eq_true_eq, show b < 64 from hb, decide_true, Bool.true_and]
  generalize coeff (W j) b = x
  revert x
  decide

attribute [local irreducible] program in
/-- `Hash::circuit`'s rows (`HashRows.hashA0`, `HashRows.hashB0`) are `HashGates` for blocks of at least `2^14` bits: the
wires' values satisfy the artifact (`HashRows.rows_sound`), its ports the first 14 words' bits as `Hash::circuit` binds
them and its outputs the next four words' bits. -/
theorem hashGates {k : ℕ} (hk : 14 ≤ k) : HashGates k HashRows.hashA0 HashRows.hashB0 := by
  intro W hrow hpin
  have hrow' : ∀ s < 2 ^ k, (∑ col ∈ range (2 ^ k), HashRows.hashA0 s col * wordBits W col) *
      (∑ col ∈ range (2 ^ k), HashRows.hashB0 s col * wordBits W col) + wordBits W s = 0 := fun s hs => by
    simpa [Tables.row, ofBlocks, Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs] using hrow s hs
  obtain ⟨a, hholds, hin, hout⟩ := HashRows.rows_sound k hk (wordBits W) hrow' hpin
  have hp : ∀ v < Compress.inputBits, a v = wordBits W (HashRows.portSlot v) := hin
  refine ⟨a, ?_, ?_, ?_⟩
  · exact hholds
  · simp only [Export.ports, portsOf, Compress.Input.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Vector.ext <;> intro i hi <;>
      simp only [Vector.getElem_ofFn, literal, BitVec.getLsbD_setWidth]
    · rw [hp i (by simp only [Compress.inputBits]; omega), columnWord_bit W _ i hi]
      apply congrArg (wordBits W)
      simp only [HashRows.portSlot, Fin.val_zero, if_pos hi]
      omega
    · rw [hp (64 + i) (by simp only [Compress.inputBits]; omega)]
      simp only [hi, decide_true, Bool.true_and]
      rw [columnWord_bit W _ i (by omega)]
      apply congrArg (wordBits W)
      simp only [HashRows.portSlot, Fin.val_one]
      split_ifs <;> omega
    · rw [hp (96 + i) (by simp only [Compress.inputBits]; omega), columnWord_bit W _ _ (Nat.mod_lt _ (by norm_num))]
      apply congrArg (wordBits W)
      simp only [HashRows.portSlot]
      split_ifs <;> omega
    · rw [hp (352 + i) (by simp only [Compress.inputBits]; omega), columnWord_bit W _ _ (Nat.mod_lt _ (by norm_num))]
      apply congrArg (wordBits W)
      simp only [HashRows.portSlot]
      split_ifs <;> omega
  · apply Vector.ext
    intro j hj
    simp only [Export.result, resultOf, Vector.getElem_ofFn, literal]
    rw [← HashRows.outAff_eq j hj, hout j hj, columnWord_bit W _ _ (Nat.mod_lt _ (by norm_num))]
    apply congrArg (wordBits W)
    simp only [HashRows.outSlot, hashO]

/-- The rows of every block and its pin, with the `HASH` matrices the artifact's (`HashGates`) and the hash table's first 18 columns its blocks' first 18 words, give the hash rows' packed witnesses (`Flocked`). -/
theorem flocked_of_rows {n h no : ℕ} (hn : n = h + no) {A0 B0 : ℕ → ℕ → ZMod 2} (hg : HashGates (6 + h) A0 B0)
    {wd : ℕ → K} {s : State} {w : Witness} (hrows : (AirLink.rowsOf s .hash).size ≤ 2 ^ no)
    (hcol : ∀ b < (AirLink.rowsOf s .hash).size, ∀ j < 18, w.cols .hash b j = wd (j + 2 ^ h * b))
    (hv : ¬ Viol n (ofBlocks (6 + h) A0 B0 (wordBits wd)))
    (hpin : ∀ b < 2 ^ no, wordBits wd (hashPin + 2 ^ (6 + h) * b) = 1) : Flocked s w := by
  subst hn
  intro b hb
  have hb' : b < 2 ^ no := lt_of_lt_of_le hb hrows
  have hrow : ∀ row < 2 ^ (6 + h), (ofBlocks (6 + h) A0 B0 (wordBits fun J => wd (J + 2 ^ h * b))).row row = 0 := by
    intro row hr
    have hu : row + 2 ^ (6 + h) * b < 2 ^ (h + no + 6) := by
      have h1 : row + 2 ^ (6 + h) * b < 2 ^ (6 + h) * (b + 1) := by rw [mul_add, mul_one]; omega
      have h2 : 2 ^ (6 + h) * (b + 1) ≤ 2 ^ (6 + h) * 2 ^ no := Nat.mul_le_mul_left _ hb'
      calc row + 2 ^ (6 + h) * b < 2 ^ (6 + h) * 2 ^ no := lt_of_lt_of_le h1 h2
        _ = 2 ^ (h + no + 6) := by rw [← pow_add]; congr 1; omega
    have h0 : (ofBlocks (6 + h) A0 B0 (wordBits wd)).row (row + 2 ^ (6 + h) * b) = 0 := by
      by_contra hne
      exact hv ⟨_, hu, hne⟩
    have hp : 0 < 2 ^ (6 + h) := by positivity
    have e1 : (row + 2 ^ (6 + h) * b) % 2 ^ (6 + h) = row := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have e2 : (row + 2 ^ (6 + h) * b) / 2 ^ (6 + h) = b := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, zero_add]
    have e3 : row % 2 ^ (6 + h) = row := Nat.mod_eq_of_lt hr
    have e4 : row / 2 ^ (6 + h) = 0 := Nat.div_eq_of_lt hr
    simp only [Tables.row, ofBlocks, e1, e2, wordBits_block] at h0
    simpa [Tables.row, ofBlocks, e3, e4] using h0
  have hpb : wordBits (fun J => wd (J + 2 ^ h * b)) hashPin = 1 := by rw [← wordBits_block]; exact hpin b hb'
  have hw : ∀ j < 18, columnWord (w.cols .hash b) j = columnWord (fun J => wd (J + 2 ^ h * b)) j := fun j hj => by
    simp only [columnWord, hcol b hb j hj]
  have e1 : (portsOf fun j => columnWord (w.cols .hash b) j) = portsOf fun j => columnWord (fun J => wd (J + 2 ^ h * b)) j :=
    congrArg portsOf (funext fun j => hw j (by omega))
  have e2 : (resultOf fun k => columnWord (w.cols .hash b) (hashO + k)) =
      resultOf fun k => columnWord (fun J => wd (J + 2 ^ h * b)) (hashO + k) :=
    congrArg resultOf (funext fun k => hw (hashO + k) (by simp only [hashO]; omega))
  rw [e1, e2]
  exact hg _ hrow hpb


open Classical in
/-- The skip challenge `ζ` as a run's challenge drawn after time `k`: where the message's polynomial and the honest one are committed before `k`, each of degree at most `127`, the oracles at which `ζ` is in the skip's event are at most `127/|E|` of them. -/
theorem skipRun_frac {c : Cert} {s : State} {T : ℕ} {C : (ℕ → K) → Prop} {st : (ℕ → K) → ℕ → Fin 4 → K}
    {val : (ℕ → K) → Val} (hR : Run c s T C st val) {own : Fin 1 → Fin 3 → ℕ} {time : Fin 1 → ℕ}
    (hown : OwnAt s (c.transcripts.getD T default) own time) (hinj : OwnInj own) {k : ℕ} (hk : ∀ i, k ≤ time i)
    (P Q : (ℕ → K) → Polynomial E) (hP : ∀ ρ, (P ρ).natDegree ≤ 127) (hQ : ∀ ρ, (Q ρ).natDegree ≤ 127)
    (hc : CommittedBefore s (c.transcripts.getD T default) val k fun ρ => (P ρ, Q ρ))
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD T default) ⊆ U) :
    (#{ρ : U → K | readR own (extU U ρ) 0 ∈ skipDraws (P (extU U ρ)) (Q (extU U ρ))} : ℚ≥0) /
      Fintype.card (U → K) ≤ ((127 : ℕ) : ℚ≥0) / Fintype.card E := by
  have key := run_frac hinj (fun i j => hU (own_mem_oracleWords hown i j))
    (fun ρ => readR own ρ 0 ∈ skipDraws (P ρ) (Q ρ)) 127 fun ρ => by
      have hf := hR.committed_at hown hinj hk hc ρ
      refine le_trans (Nat.mul_le_mul_right _ (card_le_card
        (t := ({r : Fin 1 → E | r 0 ∈ skipDraws (P ρ) (Q ρ)} : Finset _)) fun r hr => ?_)) ?_
      · simp only [mem_filter, mem_univ, true_and, readR_oracleAt hinj] at hr ⊢
        have e := hf r
        simp only [Prod.mk.injEq] at e
        rwa [e.1, e.2] at hr
      · have hcd : #({r : Fin 1 → E | r 0 ∈ skipDraws (P ρ) (Q ρ)} : Finset _) ≤ #(skipDraws (P ρ) (Q ρ)) :=
          card_le_card_of_injOn (fun r => r 0) (fun r hr => by simpa using hr)
            fun r _ r' _ he => funext fun i => by rw [Subsingleton.elim i 0]; exact he
        rw [pow_one]
        exact Nat.mul_le_mul_right _ (hcd.trans (skipDraws_card (hP ρ) (hQ ρ)))
  convert key

open Classical in
/-- The zerocheck's drawn coordinates as a run's challenges drawn after time `k`: where the tables are committed before `k`, the oracles at which they are in the fixed coordinates' event are at most `n'/|E|` of them. -/
theorem fixRun_frac {c : Cert} {s : State} {T : ℕ} {C : (ℕ → K) → Prop} {st : (ℕ → K) → ℕ → Fin 4 → K}
    {val : (ℕ → K) → Val} (hR : Run c s T C st val) {n' : ℕ} {own : Fin n' → Fin 3 → ℕ} {time : Fin n' → ℕ}
    (hown : OwnAt s (c.transcripts.getD T default) own time) (hinj : OwnInj own) {k : ℕ} (hk : ∀ i, k ≤ time i)
    (tab : (ℕ → K) → Tables) (hc : CommittedBefore s (c.transcripts.getD T default) val k tab)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD T default) ⊆ U) :
    (#{ρ : U → K | readR own (extU U ρ) ∈ fixDraws n' (tab (extU U ρ))} : ℚ≥0) /
      Fintype.card (U → K) ≤ (n' : ℚ≥0) / Fintype.card E := by
  have key := run_frac hinj (fun i j => hU (own_mem_oracleWords hown i j))
    (fun ρ => readR own ρ ∈ fixDraws n' (tab ρ)) n' fun ρ => by
      refine le_trans (Nat.mul_le_mul_right _ (card_le_card
        (t := ({r : Fin n' → E | r ∈ fixDraws n' (tab ρ)} : Finset _)) fun r hr => ?_)) ?_
      · simp only [mem_filter, mem_univ, true_and, readR_oracleAt hinj, hR.committed_at hown hinj hk hc ρ] at hr ⊢
        exact hr
      · have he : ({r : Fin n' → E | r ∈ fixDraws n' (tab ρ)} : Finset _) = fixDraws n' (tab ρ) := by
          ext r
          simp
        rw [he]
        exact fixDraws_card n' (tab ρ)
  convert key

open Classical in
/-- The ring switch's map draws as a run's six challenges drawn after time `k`: where the slices' error is committed before `k`, the oracles at which the draws are in the ring switch's event are at most `phiDeg/|E|` of them. -/
theorem ringRun_frac {c : Cert} {s : State} {T : ℕ} {C : (ℕ → K) → Prop} {st : (ℕ → K) → ℕ → Fin 4 → K}
    {val : (ℕ → K) → Val} (hR : Run c s T C st val) {own : Fin 6 → Fin 3 → ℕ} {time : Fin 6 → ℕ}
    (hown : OwnAt s (c.transcripts.getD T default) own time) (hinj : OwnInj own) {k : ℕ} (hk : ∀ i, k ≤ time i)
    (δ : (ℕ → K) → Fin 64 → E) (hc : CommittedBefore s (c.transcripts.getD T default) val k δ)
    (U : Finset ℕ) (hU : oracleWords s (c.transcripts.getD T default) ⊆ U) :
    (#{ρ : U → K | readR own (extU U ρ) ∈ ringDraws (δ (extU U ρ))} : ℚ≥0) /
      Fintype.card (U → K) ≤ (RingSwitch.phiDeg : ℚ≥0) / Fintype.card E := by
  have key := run_frac hinj (fun i j => hU (own_mem_oracleWords hown i j))
    (fun ρ => readR own ρ ∈ ringDraws (δ ρ)) RingSwitch.phiDeg fun ρ => by
      refine le_trans (Nat.mul_le_mul_right _ (card_le_card
        (t := ({r : Fin 6 → E | r ∈ ringDraws (δ ρ)} : Finset _)) fun r hr => ?_)) ?_
      · simp only [mem_filter, mem_univ, true_and, readR_oracleAt hinj, hR.committed_at hown hinj hk hc ρ] at hr ⊢
        exact hr
      · have he : ({r : Fin 6 → E | r ∈ ringDraws (δ ρ)} : Finset _) = ringDraws (δ ρ) := by
          ext r
          simp
        rw [he, show Fintype.card E ^ 6 = Fintype.card E ^ 5 * Fintype.card E by ring, ← mul_assoc]
        exact Nat.mul_le_mul_right _ (ringDraws_card (δ ρ))
  convert key

/-! Mutation tests of `LagCert`'s rules, on calls whose call `j` outputs wire `100 + j`: the scale's `zero` and `mul_const_add` at calls 0 and 1, then per node its `e_const`, `add(ζ, ·)` and `inv`, `ζ` wire 7 and `V_S(ζ)` wire 9. -/

def mutLagCalls : Array Call := #[.zero, .mulConstAdd 9 d64Word 0 0 100] ++
  ((List.range 64).flatMap fun i => [.eConst (sWords.getD i 0) 0 0, .add 7 (102 + 3 * i), .inv (103 + 3 * i)]).toArray

def mutLag : LagCert := {
  nodeAt := (List.range 64).map (2 + 3 * ·), diffAt := (List.range 64).map (3 + 3 * ·),
  invAt := (List.range 64).map (4 + 3 * ·), scaleZero := 0, scaleAt := 1 }

def mutLagLin : LinCert := { (default : LinCert) with scale := 101, invs := (List.range 64).map (104 + 3 * ·) }

example : mutLag.okFor (mutOuts 194) mutLagCalls #[] 7 9 mutLagLin = true := by decide +kernel

/-- A node of `Λ` in place of node 5 of `S`, the scale by `D_128`, a difference at another wire than `ζ`, or the scale reading another wire than `V_S(ζ)`, fail. -/
example : mutLag.okFor (mutOuts 194) (mutLagCalls.set! 17 (.eConst (lWords.getD 5 0) 0 0)) #[] 7 9 mutLagLin = false := by
  decide +kernel
example : mutLag.okFor (mutOuts 194) (mutLagCalls.set! 1 (.mulConstAdd 9 d128Word 0 0 100)) #[] 7 9 mutLagLin = false := by
  decide +kernel
example : mutLag.okFor (mutOuts 194) (mutLagCalls.set! 3 (.add 8 102)) #[] 7 9 mutLagLin = false := by decide +kernel
example : mutLag.okFor (mutOuts 194) mutLagCalls #[] 7 10 mutLagLin = false := by decide +kernel

/-- The lincheck's inverses out of the nodes' order fail. -/
example : mutLag.okFor (mutOuts 194) mutLagCalls #[] 7 9
    { mutLagLin with invs := (List.range 64).map fun i => 104 + 3 * ((i + 1) % 64) } = false := by decide +kernel

/-- `HashGates` is satisfiable: zero matrices force every bit of a block to zero, so no block passes with its pin. -/
example (k : ℕ) (hk : hashPin < 2 ^ k) : HashGates k (fun _ _ => 0) (fun _ _ => 0) := by
  intro W hrow hpin
  have := hrow hashPin hk
  simp only [Tables.row, ofBlocks, zero_mul, sum_const_zero, mul_zero, zero_add] at this
  rw [this] at hpin
  exact absurd hpin zero_ne_one

end LeanVMCircuits.Rec.Bind

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Finset

/-- A child's draw events between its bus GKR's leaves and the opening, as a numerator over `|E|`: the balance's (`AirLink.balRun_frac`, `allIds.length + 1`), flock's zerocheck (`n` rounds of degree two), skip (`127`, `Bind.skipRun_frac`), fixed coordinates (`n - 7`, `Bind.fixRun_frac`), lincheck (`h` rounds of degree two), `α` (`3`, `FlockLin.alphaRun_frac`), pin (`no`, `FlockLin.pinRun_frac`) and ring switch (`phiDeg`, `Bind.ringRun_frac`). -/
def flockDeg (n h no : ℕ) : ℕ :=
  (AirLink.allIds.length + 1) + 2 * n + 127 + (n - 7) + 2 * h + 3 + no + RingSwitch.phiDeg

/-- At most `2^32` for up to `2^10` rounds each: the ring switch's `phiDeg < 2^31 + 2^16` dominates. -/
theorem flockDeg_le {n h no : ℕ} (hn : n ≤ 2 ^ 10) (hh : h ≤ 2 ^ 10) (hno : no ≤ 2 ^ 10) : flockDeg n h no ≤ 2 ^ 32 := by
  unfold flockDeg
  rw [AirLink.allIds_length, RingSwitch.phiDeg_eq]
  omega

/-- `tree_bound_deployed` with each child's balance and flock events added to its other checks' degrees: at most `2^10` nodes, each child's other degrees at most `2^39` and its flock reduction's round counts at most `2^10`, the bound is below `2^-19` with #551 budgets `2^20` per binding shape and below `2^-7` with `2^32`. -/
theorem tree_bound_flock {ι : Type} (S : Finset ι) (hS : S.card ≤ 2 ^ 10) (D Q B n h no : ι → ℕ)
    (Qp : ι → Fin 4 → ℕ) (hD : ∀ v ∈ S, D v ≤ 2 ^ 39) (hn : ∀ v ∈ S, n v ≤ 2 ^ 10) (hh : ∀ v ∈ S, h v ≤ 2 ^ 10)
    (hno : ∀ v ∈ S, no v ≤ 2 ^ 10) (hQ : ∀ v ∈ S, Q v ≤ 2 ^ 64) (hB : ∀ v ∈ S, B v ≤ 2 ^ 86) :
    ((∀ v ∈ S, ∀ k, Qp v k ≤ 2 ^ 20) → ∑ v ∈ S, ((((D v + flockDeg (n v) (h v) (no v) : ℕ) : ℚ≥0)) /
      Fintype.card E + (∑ k, finalBound (Qp v k)).toNNRat + epsCR K (Q v) + epsLate K (Q v) (B v)) ≤ 1 / 2 ^ 19) ∧
    ((∀ v ∈ S, ∀ k, Qp v k ≤ 2 ^ 32) → ∑ v ∈ S, ((((D v + flockDeg (n v) (h v) (no v) : ℕ) : ℚ≥0)) /
      Fintype.card E + (∑ k, finalBound (Qp v k)).toNNRat + epsCR K (Q v) + epsLate K (Q v) (B v)) ≤ 1 / 2 ^ 7) :=
  tree_bound_deployed S hS (fun v => D v + flockDeg (n v) (h v) (no v)) Q B Qp
    (fun v hv => by have := flockDeg_le (hn v hv) (hh v hv) (hno v hv); have := hD v hv; omega) hQ hB

end LeanVMCircuits.Rec.Edges

namespace LeanVMCircuits.Rec.Bind

/-- Each owned table's residual term reads at most `n` rounds, `n` the table sumcheck's: the sumcheck runs the tallest owned table's `τ` rounds (`constraints::verify`). -/
def ResidCert.tausOk (rc : ResidCert) (n : ℕ) : Bool := ownedList.all fun T => decide ((rc.termOf T).tau ≤ n)

theorem ResidCert.tausOk_sem {rc : ResidCert} {n : ℕ} (h : rc.tausOk n = true) :
    ∀ T ∈ AirLink.owned, (rc.termOf T).tau ≤ n := by
  intro T hT
  simp only [ResidCert.tausOk, List.all_eq_true, decide_eq_true_eq] at h
  refine h T ?_
  simp only [AirLink.owned, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Mutation tests of `ResidCert.tausOk`: five terms of height two pass at two rounds and fail at one; one term of height three among them fails at two. -/
example : ({ sc := 0, xi := 0, terms := List.replicate 5 { (default : TermCert) with tau := 2 } } : ResidCert).tausOk 2 =
    true := by decide

example : ({ sc := 0, xi := 0, terms := List.replicate 5 { (default : TermCert) with tau := 2 } } : ResidCert).tausOk 1 =
    false := by decide

example : ({ sc := 0, xi := 0, terms := List.replicate 4 { (default : TermCert) with tau := 2 } ++
    [{ (default : TermCert) with tau := 3 }] } : ResidCert).tausOk 2 = false := by decide

end LeanVMCircuits.Rec.Bind

/-! The checks from the bus GKR's leaves to the opening on the dumps' certificates, at a run's outcomes. -/

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model Finset LeanVMCircuits.Rec.Bind AirLink LeanVMCircuits.Rec.Flock FlockLin Flocked

variable {ι Ω : Type}

/-- What a parent's run satisfies at an outcome: its calls hold, every certified sumcheck's test holds and reads its challenges from the oracle, every GKR top and odd layer's test holds, and each transcript's squeezes answer the oracle (`Run.ans`). -/
def RunHeld (c : Cert) (s : State) (os : Array (List ℕ)) (st : ℕ → Fin 4 → K) (val : (ℕ → K) → Val)
    (ρ : ℕ → K) : Prop :=
  Facts c.calls c.relax os st (val ρ) ∧ (∀ sc ∈ c.sumchecks, (∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b) ∧
    ∀ j : Fin sc.rounds.length, Model.ev (val ρ) (sc.rounds.getD j default).chal = readR (chalWords c.outs sc.chals) ρ j) ∧
    (∀ tc ∈ c.tops, ∀ a b, s.unions[tc.test]? = some (a, b) → val ρ a = val ρ b) ∧
    (∀ oc ∈ c.odds, ∀ a b, s.unions[oc.test]? = some (a, b) → val ρ a = val ρ b) ∧
    ∀ T, ∀ p ∈ chalSeeds s (c.transcripts.getD T default), nu (val ρ) p.2 = ρ p.2

theorem RunHeld.sc {c : Cert} {s : State} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : (ℕ → K) → Val}
    {ρ : ℕ → K} (h : RunHeld c s os st val ρ) {i : ℕ} {sc : SumcheckCert} (hi : c.sumchecks[i]? = some sc) :
    (∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b) ∧
      ∀ j : Fin sc.rounds.length, Model.ev (val ρ) (sc.rounds.getD j default).chal = readR (chalWords c.outs sc.chals) ρ j :=
  h.2.1 sc (Array.mem_of_getElem? hi)

/-- A child's named checks between its bus GKR's leaves and the opening, on its parent's certificates: the table sumcheck `tc` (its sumcheck `tsc`), its bus GKR `g`, residual `rc` and sides `s0`, `s1`, flock's reduction `fc` (its zerocheck `zsc` and lincheck `lsc`), and the bus's draw `dr`. -/
structure ChildCerts where
  tc : TableCert
  g : GkrCert
  rc : ResidCert
  s0 : SideCert
  s1 : SideCert
  fc : FlockCert
  tsc : SumcheckCert
  zsc : SumcheckCert
  lsc : SumcheckCert
  finalZero : ℕ
  dr : DrawCert

/-- The certificates pass `checkbind`'s checks and are linked: `TableCert.okIn`, `GkrCert.okIn`, `ResidCert.okIn` on the table sumcheck with its `ξ`, `sidesOk`, `FlockCert.ok`, the named sumchecks are the certificate's, the table sumcheck's last side is a `zero` call's output (`sumcheckOf` tests a residual against `zero`), the bus GKR's layers draw their challenges as top layers' (`GkrCert.layersOk`), each owned table's residual term reads at most the table sumcheck's rounds (`ResidCert.tausOk`), the lincheck runs `hashRounds` rounds (`FlockCert.roundsOk`), the zerocheck runs over the hash term's height (`FlockCert.heightOk`), and the sides' fingerprint weights and `β` are the bus draw's (`DrawCert.ok`). -/
def ChildCerts.Ok (cc : ChildCerts) (c : Cert) (s : State) (os : Array (List ℕ)) : Prop :=
  cc.tc.okIn c.sumchecks c.tops c.odds c.calls c.relax os = true ∧
    cc.g.okIn cc.tc c.sumchecks c.tops c.odds c.calls c.relax os = true ∧
    cc.rc.okIn os c.sumchecks c.calls c.relax = true ∧ cc.rc.sc = cc.tc.sc ∧ cc.rc.xi = cc.tc.xi ∧
    sidesOk os c.calls c.relax c.sumchecks c.tops c.odds cc.g cc.rc cc.s0 cc.s1 = true ∧
    cc.fc.ok os c.sumchecks c.calls c.relax = true ∧ c.sumchecks[cc.tc.sc]? = some cc.tsc ∧
    c.sumchecks[cc.fc.zero.sc]? = some cc.zsc ∧ c.sumchecks[cc.fc.lin.sc]? = some cc.lsc ∧
    cc.tsc.rounds.length ≤ cc.rc.zeta.length ∧ callsOk c.calls c.relax [(cc.finalZero, .zero)] = true ∧
    o os cc.finalZero = cc.tsc.final ∧ cc.g.layersOk c s os = true ∧ cc.rc.tausOk cc.tsc.rounds.length = true ∧
    cc.fc.roundsOk c.sumchecks = true ∧ cc.fc.heightOk c.sumchecks cc.rc = true ∧
    cc.dr.ok os s c.calls c.relax c.transcripts cc.s0 = true

/-- The table sumcheck's point `ζ`, its named `rc.zeta` wires' values. -/
noncomputable def ChildCerts.zetaV (cc : ChildCerts) (val : Val) : Fin cc.tsc.rounds.length → E :=
  fun j => Model.ev val (cc.rc.zeta.getD j 0)

/-- The table sumcheck's input claim is its honest instance's sum at the named forms (`table_part`'s conclusion, the balance's input). -/
def ChildCerts.tin (cc : ChildCerts) (val : Val) (w : Witness) : Prop :=
  Model.ev val cc.tsc.claim0 =
    (tableInst cc.tsc.rounds.length w (cc.zetaV val) (cc.rc.formsV val) (Model.ev val cc.tc.xi)).sum

/-- The leaf claims the bus GKR's chain names, as values. -/
noncomputable def ChildCerts.leafV (cc : ChildCerts) (c : Cert) (os : Array (List ℕ)) (val : Val) : Fin 2 → E :=
  fun t => Model.ev val (((LayerCert.chain c.sumchecks c.calls c.relax os cc.g.layers
    (cc.g.start c.tops c.odds os).2.1 (cc.g.start c.tops c.odds os).2.2).getD []).getD t 0)

/-- The sides' true leaf claims. -/
noncomputable def ChildCerts.leafT (cc : ChildCerts) (val : Val) (pubF0 pubF1 : Bool → ℕ → ℕ → E) (w : Witness) :
    Fin 2 → E :=
  ![cc.s0.leafClaim val pubF0 w, cc.s1.leafClaim val pubF1 w]

/-! The bus GKR from the root to the leaves: the trees' leaves are the sides' stacked layers, over the sides' `μ` variables. -/

/-- Tree `t`'s leaves, push then pull: the sides' stacked layers. -/
noncomputable def ChildCerts.leaf (cc : ChildCerts) (val : Val) (pubF0 pubF1 : Bool → ℕ → ℕ → E) (w : Witness) (t : ℕ) :
    ℕ → E :=
  if t = 0 then cc.s0.stack val pubF0 w else cc.s1.stack val pubF1 w

/-- The checks from the root to the leaves: the first layer and each layer past it. -/
def ChildCerts.G (cc : ChildCerts) : ℕ := cc.g.layers.length + 1

/-- Stage `k`'s named values (`GkrCert.outsAt`). -/
noncomputable def ChildCerts.vals (cc : ChildCerts) (c : Cert) (val : Val) (k : ℕ) : Fin 2 → E :=
  fun t => Model.ev val ((cc.g.outsAt c k).getD t 0)

/-- Stage `k`'s true values: each tree's level at stage `k`'s point (`GkrCert.ptR`), as many levels above the leaves as the point is short of `μ`. -/
noncomputable def ChildCerts.tvals (cc : ChildCerts) (c : Cert) (ρ : ℕ → K) (val : Val) (pubF0 pubF1 : Bool → ℕ → ℕ → E)
    (w : Witness) (k : ℕ) : Fin 2 → E :=
  fun t => mleL (cc.g.ptR c ρ k) (level (cc.leaf val pubF0 pubF1 w t) (cc.s0.mu - (cc.g.ptR c ρ k).length))

/-- Check `j`'s event between the root and the leaves: the first layer's `topFalse` or `oddFalse` at the true children; layer `j - 1`'s sumcheck's `sumcheckFalse` against `layerInst` at stage `j`'s point and the oracle's `λ`, or its `λ` or line event (`Bind.layerBad`) against the true values and children. -/
def ChildCerts.layerEv (cc : ChildCerts) (c : Cert) (s : State) (val : (ℕ → K) → Val) (ρ : ℕ → K)
    (pubF0 pubF1 : Bool → ℕ → ℕ → E) (w : Witness) : ℕ → Prop
  | 0 => if cc.g.odd then
      oddFalse c s (c.odds.getD cc.g.first default) (fun t => level (cc.leaf (val ρ) pubF0 pubF1 w t) (cc.s0.mu - 1) 0)
        (fun t => level (cc.leaf (val ρ) pubF0 pubF1 w t) (cc.s0.mu - 1) 1) val ρ
    else topFalse c s (c.tops.getD cc.g.first default) (fun t i => level (cc.leaf (val ρ) pubF0 pubF1 w t) (cc.s0.mu - 2) i)
      val ρ
  | k + 1 =>
    let lc := cc.g.layers.getD k default
    let sc := c.sumchecks.getD lc.sc default
    let p := cc.g.ptR c ρ (k + 1)
    let W : Fin 2 → ℕ → E := fun t => level (cc.leaf (val ρ) pubF0 pubF1 w t) (cc.s0.mu - (sc.rounds.length + 2))
    sumcheckFalse c s sc (layerInst sc.rounds.length (fun j => p.getD j 0) (readR (chalWords c.outs lc.layer.chals) ρ 0) W)
        (fun _ => 0) val ρ ∨
      Bind.layerBad c lc (fun t => mleAt sc.rounds.length (fun j => p.getD j 0) fun z => ∏ i ∈ range 4, W t (4 * z + i))
        (fun t i => MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ) (childMle sc.rounds.length (W t) i)) val ρ

/-- The sides' point has `μ` coordinates, stage `k + 1`'s `k` pairs more than the first layer's, the last stage's being the sides' point. -/
theorem ChildCerts.lengths {cc : ChildCerts} {c : Cert} {s : State} {st : ℕ → Fin 4 → K} {val : Val}
    (hF : Facts c.calls c.relax c.outs st val) (hcc : cc.Ok c s c.outs) :
    (∀ k ≤ cc.g.layers.length, (cc.g.ptAt c (k + 1)).length = (cc.g.ptAt c 1).length + 2 * k) ∧
      cc.s0.mu = (cc.g.ptAt c 1).length + 2 * cc.g.layers.length ∧ cc.s0.zeta = cc.g.ptAt c cc.G ∧
      cc.s1.zeta = cc.s0.zeta ∧ cc.s1.mu = cc.s0.mu ∧ (cc.g.ptAt c 1).length = if cc.g.odd then 1 else 2 := by
  obtain ⟨-, hg, -, -, -, hs, -⟩ := hcc
  obtain ⟨-, v0, v1, hch, -⟩ := GkrCert.sem hF hg
  have hl := GkrCert.ptAt_length hch
  simp only [sidesOk, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hz0⟩, hz1⟩, hmu0⟩, hmu1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs
  rw [GkrCert.point_eq hch] at hz0
  refine ⟨hl, ?_, hz0, hz1, hmu1, ?_⟩
  · rw [hmu0, hz0]
    exact hl _ le_rfl
  · simp only [GkrCert.ptAt, LayerCert.ptN, GkrCert.start]
    cases cc.g.odd <;> simp

/-- Each side's owned blocks are at their residual terms' heights (`sidesOk`), so at the committed heights where the terms are. -/
theorem ChildCerts.kappa_tau {cc : ChildCerts} {c : Cert} {s : State} {os : Array (List ℕ)} (hcc : cc.Ok c s os)
    {w : Witness} (hτ : ∀ T ∈ owned, (cc.rc.termOf T).tau = tauOf w T) :
    (∀ b : Fin cc.s0.blocks.length, ∀ T, cc.s0.blocks[b].owner = some T → cc.s0.blocks[b].kappa = tauOf w T) ∧
      ∀ b : Fin cc.s1.blocks.length, ∀ T, cc.s1.blocks[b].owner = some T → cc.s1.blocks[b].kappa = tauOf w T := by
  obtain ⟨-, -, -, -, -, hs, -⟩ := hcc
  simp only [sidesOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hall⟩ := hs
  have key : ∀ x ∈ cc.s0.blocks ++ cc.s1.blocks, ∀ T, x.owner = some T → T ∈ owned → x.kappa = tauOf w T :=
    fun x hx T hT hTo => by
      have := hall x hx
      rw [hT] at this
      rw [← hτ T hTo]
      exact beq_iff_eq.mp this
  have own : ∀ (sc : SideCert), sc.ok os c.calls c.relax = true → ∀ b : Fin sc.blocks.length, ∀ T,
      sc.blocks[b].owner = some T → T ∈ owned := fun sc hok b T hT => by
    simp only [SideCert.ok, Bool.and_eq_true] at hok
    exact ((SideCert.fits hok.1).1 b).2.1 T hT
  exact ⟨fun b T hT => key _ (List.mem_append_left _ (List.getElem_mem _)) T hT (own _ h0 b T hT),
    fun b T hT => key _ (List.mem_append_right _ (List.getElem_mem _)) T hT (own _ h1 b T hT)⟩

/-- The bus GKR's checks from the root to the leaves meet `RecParts.Ok`'s test on the dumps' certificates at a run's outcomes: check `j`, off its event `layerEv`, makes stage `j`'s values the true ones from stage `j + 1`'s. The first layer is `top_step` or `odd_step`, each layer past it `layer_step`, every layer's challenges read from the oracle (`chal_readR`). -/
theorem ChildCerts.layer_ok {cc : ChildCerts} {c : Cert} {s : State} {st : ℕ → Fin 4 → K} {val : (ℕ → K) → Val}
    {ρ : ℕ → K} (hcc : cc.Ok c s c.outs) (hh : RunHeld c s c.outs st val ρ)
    (pubF0 pubF1 : Bool → ℕ → ℕ → E) (w : Witness) {j : ℕ} (hj : j < cc.G)
    (hb : ¬ cc.layerEv c s val ρ pubF0 pubF1 w j)
    (hnext : cc.vals c (val ρ) (j + 1) = cc.tvals c ρ (val ρ) pubF0 pubF1 w (j + 1)) :
    cc.vals c (val ρ) j = cc.tvals c ρ (val ρ) pubF0 pubF1 w j := by
  have hF := hh.1
  obtain ⟨hlen, hmu, -, -, -, h1⟩ := ChildCerts.lengths hF hcc
  obtain ⟨-, hg, -, -, -, -, -, -, -, -, -, -, -, hlay, -⟩ := hcc
  obtain ⟨hroot, v0, v1, hch, -⟩ := GkrCert.sem hF hg
  obtain ⟨hl, -⟩ := LayerCert.chain_at _ _ _ _ hch
  have hfirst : cc.g.first < if cc.g.odd then c.odds.size else c.tops.size := by
    unfold GkrCert.okIn at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg.1.1
  set leaf := cc.leaf (val ρ) pubF0 pubF1 w with hleaf
  match j with
  | 0 =>
    simp only [ChildCerts.layerEv] at hb
    funext t
    have hn := fun (t : ℕ) (ht : t < 2) => congrFun hnext ⟨t, ht⟩
    simp only [ChildCerts.vals, ChildCerts.tvals, GkrCert.outsAt, LayerCert.outsN, GkrCert.ptR,
      List.length_nil, Nat.sub_zero, ← hleaf] at hn ⊢
    cases hodd : cc.g.odd
    · rw [hodd] at hfirst hb h1
      simp only [Bool.false_eq_true, ↓reduceIte] at hfirst hb h1
      have hm : c.tops.getD cc.g.first default ∈ c.tops := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hfirst, Option.getD_some]
        exact Array.getElem_mem hfirst
      simp only [GkrCert.start, hodd, Bool.false_eq_true, ↓reduceIte] at hroot hn ⊢
      have hm2 : (c.tops.getD cc.g.first default).m = 2 := by
        show (c.tops.getD cc.g.first default).values.length = 2
        rw [hroot]
        rfl
      refine top_step ρ leaf (by omega) hm2 (hh.2.2.1 _ hm) (fun t ht => ?_) hb t t.isLt
      have := hn t ht
      simp only [GkrCert.firstPt, hodd, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil] at this
      rw [List.getD_eq_getElem _ _ (by simpa using ht)] at this
      simpa using this
    · rw [hodd] at hfirst hb h1
      simp only [↓reduceIte] at hfirst hb h1
      have hm : c.odds.getD cc.g.first default ∈ c.odds := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hfirst, Option.getD_some]
        exact Array.getElem_mem hfirst
      simp only [GkrCert.start, hodd, ↓reduceIte] at hroot hn ⊢
      have hm2 : (c.odds.getD cc.g.first default).m = 2 := by
        show (c.odds.getD cc.g.first default).values.length = 2
        rw [hroot]
        rfl
      refine odd_step ρ leaf (by omega) hm2 (hh.2.2.2.1 _ hm) (fun t ht => ?_) hb t t.isLt
      have := hn t ht
      simp only [GkrCert.firstPt, hodd, ↓reduceIte, List.length_cons, List.length_nil] at this
      rw [List.getD_eq_getElem _ _ (by simpa using ht)] at this
      simpa using this
  | k + 1 =>
    have hk : k < cc.g.layers.length := by simp [ChildCerts.G] at hj; omega
    obtain ⟨sc, hsc, hlink, hok, hm⟩ := hl k hk
    have hmem : cc.g.layers.getD k default ∈ cc.g.layers := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact List.getElem_mem _
    have hlc : (cc.g.layers.getD k default).chalOk c s c.outs = true := by
      simp only [GkrCert.layersOk, List.all_eq_true] at hlay
      exact hlay _ hmem
    obtain ⟨-, hc, hokc, -, -⟩ := LayerCert.chal_sem hlc
    have hchal := chal_readR hc hokc hF (hh.2.2.2.2 _)
    have hgd : c.sumchecks.getD (cc.g.layers.getD k default).sc default = sc := by
      rw [Array.getD_eq_getD_getElem?, hsc, Option.getD_some]
    have hw := congrArg List.length (LayerCert.link_sem hlink).2.2.2.2.1
    simp only [List.length_map] at hw
    have hp : (cc.g.ptR c ρ (k + 1)).length = sc.rounds.length := by
      rw [GkrCert.ptR_length, hw]
      rfl
    have hμ : sc.rounds.length + 2 ≤ cc.s0.mu := by
      have e1 : (cc.g.ptAt c (k + 1 + 1)).length = 2 + sc.rounds.length := by
        simp only [GkrCert.ptAt, LayerCert.ptN, hgd, List.length_append, List.length_cons, List.length_nil,
          List.length_map]
      have e2 := hlen (k + 1) (by omega)
      omega
    subst hgd
    funext t
    have := layer_step ρ hF hlink hok hm leaf (cc.g.ptR c ρ (k + 1)) hp hμ (hh.sc hsc).1 hchal
      (fun t ht => ?_) hb t t.isLt
    · simpa [ChildCerts.vals, ChildCerts.tvals, GkrCert.outsAt, ← hleaf] using this
    · have := congrFun hnext ⟨t, ht⟩
      simp only [ChildCerts.vals, ChildCerts.tvals, GkrCert.outsAt, LayerCert.outsN, GkrCert.ptR, LayerCert.nextPt,
        ← hleaf] at this
      rw [List.getD_eq_getElem _ _ (by simpa using ht)] at this
      simpa using this

/-- At the leaves the stages meet the balance: the last stage's named values are the chain's leaf claims (`leafV`), and its true values the sides' leaf claims (`leafT`), the last stage's point being the sides' point read from the oracle. -/
theorem ChildCerts.leaves {cc : ChildCerts} {c : Cert} {s : State} {st : ℕ → Fin 4 → K} {val : (ℕ → K) → Val}
    {ρ : ℕ → K} (hacc : c.accepts s = true) (hcc : cc.Ok c s c.outs) (hh : RunHeld c s c.outs st val ρ)
    (pubF0 pubF1 : Bool → ℕ → ℕ → E) (w : Witness) :
    cc.vals c (val ρ) cc.G = cc.leafV c c.outs (val ρ) ∧
      cc.tvals c ρ (val ρ) pubF0 pubF1 w cc.G = cc.leafT (val ρ) pubF0 pubF1 w := by
  have hF := hh.1
  obtain ⟨hlen, hmu, hz0, hz1, hmu1, -⟩ := ChildCerts.lengths hF hcc
  obtain ⟨-, hg, -, -, -, -, -, -, -, -, -, -, -, hlay, -⟩ := hcc
  obtain ⟨-, v0, v1, hch, -⟩ := GkrCert.sem hF hg
  obtain ⟨-, hlast⟩ := LayerCert.chain_at _ _ _ _ hch
  have hev : (cc.g.ptAt c cc.G).map (Model.ev (val ρ)) = cc.g.ptR c ρ cc.G :=
    GkrCert.ptAt_ev hacc hF hh.2.2.2.2 (fun sc hsc => (hh.2.1 sc hsc).2) hg hlay cc.g.layers.length le_rfl
  have hlA : (cc.g.ptAt c cc.G).length = cc.s0.mu := by
    rw [hmu]
    exact hlen _ le_rfl
  have hlR : (cc.g.ptR c ρ cc.G).length = cc.s0.mu := by rw [GkrCert.ptR_length, hlA]
  have hz : ∀ j : Fin cc.s0.mu, Model.ev (val ρ) (cc.s0.zeta.getD j 0) = (cc.g.ptR c ρ cc.G).getD j 0 := by
    intro j
    have hj : (j : ℕ) < (cc.g.ptAt c cc.G).length := by rw [hlA]; exact j.isLt
    rw [hz0, ← hev, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have hl0 : ∀ f : ℕ → E, level f 0 = f := fun f => funext (level_zero f)
  refine ⟨?_, ?_⟩
  · funext t
    simp only [ChildCerts.vals, ChildCerts.leafV, hch, Option.getD_some, ChildCerts.G, GkrCert.outsAt, ← hlast]
  · funext t
    fin_cases t
    · show mleL (cc.g.ptR c ρ cc.G) (level (cc.leaf (val ρ) pubF0 pubF1 w 0) (cc.s0.mu - (cc.g.ptR c ρ cc.G).length)) =
        cc.s0.leafClaim (val ρ) pubF0 w
      rw [hlR, Nat.sub_self, hl0, SideCert.leafClaim_mleL cc.s0 _ _ _ (cc.g.ptR c ρ cc.G) hlR hz]
      rfl
    · show mleL (cc.g.ptR c ρ cc.G) (level (cc.leaf (val ρ) pubF0 pubF1 w 1) (cc.s0.mu - (cc.g.ptR c ρ cc.G).length)) =
        cc.s1.leafClaim (val ρ) pubF1 w
      rw [hlR, Nat.sub_self, hl0, SideCert.leafClaim_mleL cc.s1 _ _ _ (cc.g.ptR c ρ cc.G) (by rw [hmu1, hlR])
        (fun j => by rw [hz1]; exact hz ⟨j, by rw [← hmu1]; exact j.isLt⟩)]
      rfl

open Classical in
/-- The balance's event at an outcome: `(ζ, ξ)` in `balDraws` at the bus parts the forms' sums less the named totals. -/
noncomputable def ChildCerts.balBad [Fintype Ω] (cc : ChildCerts) (val : Ω → Val) (w : Ω → Witness) : Finset Ω :=
  {ω | (cc.zetaV (val ω), Model.ev (val ω) cc.tc.xi) ∈ balDraws (w ω) fun ζ i =>
    formSums (w ω) ζ (cc.rc.formsV (val ω)) i - Model.ev (val ω) (if i = 0 then cc.tc.tot0 else cc.tc.tot1)}

open Classical in
/-- The table sumcheck's event at an outcome. -/
noncomputable def ChildCerts.tabBad [Fintype Ω] (cc : ChildCerts) (c : Cert) (s : State) (val : (ℕ → K) → Val)
    (ρ : Ω → ℕ → K) (w : Ω → Witness) (T' : Ω → ℕ → E) : Finset Ω :=
  {ω | sumcheckFalse c s cc.tsc (tableInst cc.tsc.rounds.length (w ω) (cc.zetaV (val (ρ ω)))
    (cc.rc.formsV (val (ρ ω))) (Model.ev (val (ρ ω)) cc.rc.xi)) (T' ω) val (ρ ω)}

/-- The committed `HASH` region of a child at an outcome: its words, the outer variables' count and the opened polynomial on the cube. Its matrices are `Hash::circuit`'s (`HashRows.hashA0`, `HashRows.hashB0`). -/
structure HashRegion (cc : ChildCerts) where
  no : ℕ
  hno : cc.zsc.rounds.length = cc.lsc.rounds.length + no
  wd : ℕ → K
  q : (Fin (cc.lsc.rounds.length + no) → E) → K

open Classical in
/-- Flock's events at an outcome (`flock_rows`'s): both sumchecks' `sumcheckFalse`, `alphaBad`, `pinBad`, `ringDraws`, `skipDraws` and `fixDraws`. -/
noncomputable def ChildCerts.flBad [Fintype Ω] (cc : ChildCerts) (c : Cert) (s : State) (os : Array (List ℕ))
    (val : (ℕ → K) → Val) (ρ : Ω → ℕ → K) (hr : Ω → HashRegion cc) (T' : Ω → ℕ → E) : Finset Ω :=
  {ω | let v := val (ρ ω)
    let h := cc.lsc.rounds.length
    let χ := cc.zsc.chalPt v
    let ζ := cc.fc.zero.zeta v
    let R := hr ω
    let z := wordBits R.wd
    let xin := inPt R.hno χ
    let xo := outPt R.hno χ
    let Zv := outerFold R.no xo (sliceQ h z)
    let M := hashMats HashRows.hashA0 HashRows.hashB0
    let tab := ofBlocks (6 + h) HashRows.hashA0 HashRows.hashB0 z
    sumcheckFalse c s cc.zsc (zeroInst cc.zsc.rounds.length (cc.zsc.weightPt v) tab ζ) (T' ω) val (ρ ω) ∨
    sumcheckFalse c s cc.lsc (linInst h M (lzOf ζ) xin Zv (Model.ev v cc.fc.lin.alpha)) (T' ω) val (ρ ω) ∨
    Model.ev v cc.fc.lin.alpha ∈ alphaBad (diff ![Model.ev v cc.fc.lin.a, Model.ev v cc.fc.lin.b,
      Model.ev v cc.fc.lin.c] ![triA M (lzOf ζ) xin Zv, triB M (lzOf ζ) xin Zv, triC (lzOf ζ) xin Zv] (pinV M Zv)) ∨
    xo ∈ pinBad R.no (fun b => sliceQ h z (hashPin % 64) (hashPin / 64) b) ∨
    cc.fc.ring.fV os v ∈ ringDraws (fun i => cc.fc.ring.sV v i -
      RingSwitch.sliceMle R.q (Fin.append (chi (roundV v cc.lsc)) xo) i) ∨
    ζ ∈ skipDraws (phat (cc.fc.zero.msg v)) (honestP cc.zsc.rounds.length (cc.zsc.weightPt v) tab) ∨
    cc.fc.zero.outerPt v ∈ fixDraws cc.fc.zero.outer.length tab}

/-- The openings flock's reduction ends in at an outcome: the region's polynomial on the cube is its words, the opening at the ring switch's target holds (the PCS's) and the deferred matrix claim holds (the tree's matrix reduction's). -/
def ChildCerts.flOpened (cc : ChildCerts) (os : Array (List ℕ)) (v : Val) (R : HashRegion cc) : Prop :=
  (∀ u < 2 ^ (cc.lsc.rounds.length + R.no), R.q (bitPoint (cc.lsc.rounds.length + R.no) u) = R.wd u) ∧
    RingSwitch.RingOpening R.q (Fin.append (chi (roundV v cc.lsc)) (outPt R.hno (cc.zsc.chalPt v)))
      (cc.fc.ring.fV os v) (Model.ev v (cc.fc.ring.target os)) ∧
    cc.fc.lin.MatrixHolds v cc.lsc (hashMats HashRows.hashA0 HashRows.hashB0) (lzOf (cc.fc.zero.zeta v)) (inPt R.hno (cc.zsc.chalPt v))

/-- The openings the table sumcheck ends in at an outcome: its hints true and its column claims the committed columns' extensions at `chi r`. -/
def ChildCerts.tabOpened (cc : ChildCerts) (v : Val) (w : Witness) (T' : ℕ → E) : Prop :=
  (∀ x ∈ cc.tsc.hints, Model.ev v x = T' x) ∧ ∀ T ∈ owned, ∀ c < nCols T, cc.rc.colV v T c =
    MvPolynomial.eval (chi fun j => Model.ev v (cc.tsc.rounds.getD j default).chal) (mle cc.tsc.rounds.length w T c)

open Classical in
/-- The bus GKR's layers' events at an outcome (`layerEv`). -/
noncomputable def ChildCerts.layerBad [Fintype Ω] (cc : ChildCerts) (c : Cert) (s : State) (val : (ℕ → K) → Val)
    (ρ : Ω → ℕ → K) (pubF0 pubF1 : Ω → Bool → ℕ → ℕ → E) (w : Ω → Witness) (j : ℕ) : Finset Ω :=
  {ω | cc.layerEv c s val (ρ ω) (pubF0 ω) (pubF1 ω) (w ω) j}

/-- The checks from the bus GKR's root to the opening meet `RecParts.Ok` on the dumps' certificates at a run's outcomes: the GKR's layers' tests are `ChildCerts.layer_ok`'s off `layerBad`, each stage's named values (`vals`) the trees' levels at its point (`tvals`), the last stage the leaf claims (`ChildCerts.leaves`); the balance's test is `balance_sides`', the table sumcheck's `table_part`'s and flock's `flock_rows` with `flocked_of_rows` on `Hash::circuit`'s rows (`hashGates`, the lincheck's `hashRounds` rounds from `FlockCert.roundsOk`), each off its event (`balBad`, `tabBad`, `flBad`), with the openings `tabOpened` and `flOpened`. What stays: the openings off `pcsBad` (`hopen`), and per outcome the layout facts (`hτ`, the residual's terms at the committed heights, whence the sides' owned blocks, `ChildCerts.kappa_tau`, and each owned table's `τ` within the table sumcheck's rounds, `ResidCert.tausOk`; the region's blocks the hash table's columns), the sides' public coordinates' values (`SideCert.PubTrue`) and the hash rows within the region. -/
theorem tableParts_named [Fintype Ω] (c : ι → Cert) (s : ι → State) (hacc : ∀ v, (c v).accepts (s v) = true)
    (st : ι → Ω → ℕ → Fin 4 → K) (val : ι → (ℕ → K) → Val) (ρ : ι → Ω → ℕ → K) (cc : ι → ChildCerts)
    (hcc : ∀ v, (cc v).Ok (c v) (s v) (c v).outs) (t : ι → State) (w : ι → Ω → Witness)
    (hr : (v : ι) → Ω → HashRegion (cc v)) (T' : ι → Ω → ℕ → E) (pubF0 pubF1 : ι → Ω → Bool → ℕ → ℕ → E)
    (pcsBad crBad : ι → Finset Ω) (opened : ι → Ω → Prop)
    (hpub : ∀ v ω, RunHeld (c v) (s v) (c v).outs (st v ω) (val v) (ρ v ω) →
      (cc v).s0.PubTrue (val v (ρ v ω)) (pubF0 v ω) ∧ (cc v).s1.PubTrue (val v (ρ v ω)) (pubF1 v ω))
    (hτ : ∀ v ω, ∀ T ∈ owned, ((cc v).rc.termOf T).tau = tauOf (w v ω) T)
    (hrows : ∀ v ω, (AirLink.rowsOf (t v) .hash).size ≤ 2 ^ (hr v ω).no)
    (hcolH : ∀ v ω, ∀ b < (AirLink.rowsOf (t v) .hash).size, ∀ j < 18,
      (w v ω).cols .hash b j = (hr v ω).wd (j + 2 ^ (cc v).lsc.rounds.length * b))
    (hopT : ∀ v ω, opened v ω → (cc v).tabOpened (val v (ρ v ω)) (w v ω) (T' v ω))
    (hopF : ∀ v ω, opened v ω → (cc v).flOpened (c v).outs (val v (ρ v ω)) (hr v ω))
    (hhintL : ∀ v ω, opened v ω → ∀ x ∈ (cc v).lsc.hints, Model.ev (val v (ρ v ω)) x = T' v ω x)
    (hopen : ∀ v ω, ω ∉ pcsBad v → opened v ω) :
    (tableParts (fun v => (cc v).G) (fun v k ω => (cc v).vals (c v) (val v (ρ v ω)) k)
      (fun v k ω => (cc v).tvals (c v) (ρ v ω) (val v (ρ v ω)) (pubF0 v ω) (pubF1 v ω) (w v ω) k)
      (fun v ω => (cc v).tin (val v (ρ v ω)) (w v ω)) (fun v ω => Flocked (t v) (w v ω)) opened
      (fun v => (cc v).layerBad (c v) (s v) (val v) (ρ v) (pubF0 v) (pubF1 v) (w v))
      (fun v => (cc v).balBad (fun ω => val v (ρ v ω)) (w v))
      (fun v => (cc v).tabBad (c v) (s v) (val v) (ρ v) (w v) (T' v))
      (fun v => (cc v).flBad (c v) (s v) (c v).outs (val v) (ρ v) (hr v) (T' v)) pcsBad crBad).Ok
      (fun v ω => RunHeld (c v) (s v) (c v).outs (st v ω) (val v) (ρ v ω)) := by
  refine tableParts_ok _ _ _ _ _ opened _ _ _ _ pcsBad crBad _ (fun v j ω hj hh _ hb hnext =>
    ChildCerts.layer_ok (hcc v) hh (pubF0 v ω) (pubF1 v ω) (w v ω) hj
      (by simpa [ChildCerts.layerBad] using hb) hnext) ?_ ?_ ?_ hopen
  · -- The balance.
    intro v ω hh _ hb hin
    obtain ⟨htc, hg, -, -, -, hs, -, htsc, -, -, hNl, -, -, -, htk, -⟩ := hcc v
    have htau : ∀ T ∈ owned, tauOf (w v ω) T ≤ (cc v).tsc.rounds.length := fun T hT => by
      rw [← hτ v ω T hT]
      exact ResidCert.tausOk_sem htk T hT
    obtain ⟨hp0, hp1⟩ := hpub v ω hh
    let aF : (Fin (cc v).tsc.rounds.length → E) → Fin 2 → E := fun ζ i =>
      formSums (w v ω) ζ ((cc v).rc.formsV (val v (ρ v ω))) i -
        Model.ev (val v (ρ v ω)) (if i = 0 then (cc v).tc.tot0 else (cc v).tc.tot1)
    have hx : ((cc v).zetaV (val v (ρ v ω)), Model.ev (val v (ρ v ω)) (cc v).tc.xi) ∉ balDraws (w v ω) aF := by
      intro hm
      exact hb (by simp only [ChildCerts.balBad, mem_filter, mem_univ, true_and]; exact hm)
    obtain ⟨v0, v1, hch, e0, e1⟩ := balance_sides (a := aF) hh.1 htc hg htsc hs (pubF0 v ω) (pubF1 v ω) hp0 hp1
      (w v ω) ((ChildCerts.kappa_tau (hcc v) (hτ v ω)).1) ((ChildCerts.kappa_tau (hcc v) (hτ v ω)).2)
      ((cc v).zetaV (val v (ρ v ω))) hNl (fun j => rfl) htau rfl hin hx
    obtain ⟨hV, hT⟩ := ChildCerts.leaves (hacc v) (hcc v) hh (pubF0 v ω) (pubF1 v ω) (w v ω)
    show (cc v).vals (c v) (val v (ρ v ω)) (cc v).G = (cc v).tvals (c v) (ρ v ω) (val v (ρ v ω)) (pubF0 v ω)
      (pubF1 v ω) (w v ω) (cc v).G
    rw [hV, hT]
    funext i
    fin_cases i
    · simp [ChildCerts.leafV, ChildCerts.leafT, hch, e0]
    · simp [ChildCerts.leafV, ChildCerts.leafT, hch, e1]
  · -- The table sumcheck.
    intro v ω hh _ hb ho
    obtain ⟨-, -, hrc, hrsc, hxi, -, -, htsc, -, -, -, hz0, hzo, -⟩ := hcc v
    have hzero : Model.ev (val v (ρ v ω)) (cc v).tsc.final = 0 := by
      rw [← hzo]
      exact holds_of_mem hh.1 hz0 (List.mem_singleton_self _)
    obtain ⟨hhint, hcol⟩ := hopT v ω ho
    have hsc : (c v).sumchecks[(cc v).rc.sc]? = some (cc v).tsc := by rw [hrsc]; exact htsc
    obtain ⟨htest, hchal⟩ := hh.sc htsc
    have hnot : ¬ sumcheckFalse (c v) (s v) (cc v).tsc (tableInst (cc v).tsc.rounds.length (w v ω)
        ((cc v).zetaV (val v (ρ v ω))) ((cc v).rc.formsV (val v (ρ v ω))) (Model.ev (val v (ρ v ω)) (cc v).rc.xi))
        (T' v ω) (val v) (ρ v ω) := fun hm =>
      hb (by simp only [ChildCerts.tabBad, mem_filter, mem_univ, true_and]; exact hm)
    have := table_part (c := c v) (s := s v) (val := val v) (ρ v ω) hh.1 hrc hsc (w v ω) ((cc v).zetaV (val v (ρ v ω)))
      ((cc v).rc.formsV (val v (ρ v ω))) (fun m => rfl) (hτ v ω) (fun _ _ _ => rfl) hchal htest hzero hhint
      hcol hnot
    rw [ChildCerts.tin, ← hxi]
    exact this
  · -- Flock's reduction.
    intro v ω hh _ hb ho
    obtain ⟨-, -, -, -, -, -, hfc, -, hzsc, hlsc, -, -, -, -, -, hro⟩ := hcc v
    have hk : 14 ≤ 6 + (cc v).lsc.rounds.length := by
      rw [FlockCert.roundsOk_sem hro.1 hlsc, hashRounds]
    obtain ⟨hq, hop, hmat⟩ := hopF v ω ho
    obtain ⟨htestZ, hchalZ⟩ := hh.sc hzsc
    obtain ⟨htestL, hchalL⟩ := hh.sc hlsc
    simp only [ChildCerts.flBad, mem_filter, mem_univ, true_and, not_or] at hb
    obtain ⟨hnZ, hnL, hα, hpE, hrE, hsk, hfx⟩ := hb
    obtain ⟨hv, hp⟩ := flock_rows (c := c v) (s := s v) (val := val v) (ρ v ω) hh.1 hfc hzsc hlsc (hr v ω).hno
      HashRows.hashA0 HashRows.hashB0 (hr v ω).wd (hr v ω).q hq hchalZ htestZ hchalL htestL (hhintL v ω ho) hop hmat
      hnZ hnL hα hpE hrE hsk hfx
    exact flocked_of_rows (hr v ω).hno (hashGates hk) (hrows v ω) (hcolH v ω) hv hp

/-- The witness the stack holds (`RecLayout::sources`): the hash table's first 18 columns are ports of the `HASH` region (`Source::Port`), column `c` at row `b` word `c` of block `b`, blocks of `2^h` words (`stride_log`); every other column is the committed one. -/
def ported (w : Witness) (h : ℕ) (wd : ℕ → K) : Witness where
  height := w.height
  cols T b c := if T = .hash ∧ c < 18 then wd (c + 2 ^ h * b) else w.cols T b c

/-- A child's witness at an outcome: its committed columns `w`, the hash table's ports the region's words, blocks of `2^h` words for the lincheck's `h` rounds. -/
def ChildCerts.wit (cc : ChildCerts) (w : Witness) (R : HashRegion cc) : Witness := ported w cc.lsc.rounds.length R.wd

/-- `tableParts_named` at the stack's witness (`ChildCerts.wit`): the hash table's columns are the region's words by the layout, and its rows lie within the region where its committed height holds them, the zerocheck running over the hash term's height (`FlockCert.heightOk`) and the residual's hash term at the committed height (`hτ`). What stays: the openings off `pcsBad` (`hopen`), the residual's terms at the committed heights (`hτ`), the hash table's height holding its rows (`hfit`, the layout's, `AirLink.LayoutFits`) and the sides' public coordinates' values (`SideCert.PubTrue`). -/
theorem tableParts_certs [Fintype Ω] (c : ι → Cert) (s : ι → State) (hacc : ∀ v, (c v).accepts (s v) = true)
    (st : ι → Ω → ℕ → Fin 4 → K) (val : ι → (ℕ → K) → Val) (ρ : ι → Ω → ℕ → K) (cc : ι → ChildCerts)
    (hcc : ∀ v, (cc v).Ok (c v) (s v) (c v).outs) (t : ι → State) (w : ι → Ω → Witness)
    (hr : (v : ι) → Ω → HashRegion (cc v)) (T' : ι → Ω → ℕ → E) (pubF0 pubF1 : ι → Ω → Bool → ℕ → ℕ → E)
    (pcsBad crBad : ι → Finset Ω) (opened : ι → Ω → Prop)
    (hpub : ∀ v ω, RunHeld (c v) (s v) (c v).outs (st v ω) (val v) (ρ v ω) →
      (cc v).s0.PubTrue (val v (ρ v ω)) (pubF0 v ω) ∧ (cc v).s1.PubTrue (val v (ρ v ω)) (pubF1 v ω))
    (hτ : ∀ v ω, ∀ T ∈ owned, ((cc v).rc.termOf T).tau = tauOf (w v ω) T)
    (hfit : ∀ v ω, (AirLink.rowsOf (t v) .hash).size ≤ (w v ω).height .hash)
    (hopT : ∀ v ω, opened v ω → (cc v).tabOpened (val v (ρ v ω)) ((cc v).wit (w v ω) (hr v ω)) (T' v ω))
    (hopF : ∀ v ω, opened v ω → (cc v).flOpened (c v).outs (val v (ρ v ω)) (hr v ω))
    (hhintL : ∀ v ω, opened v ω → ∀ x ∈ (cc v).lsc.hints, Model.ev (val v (ρ v ω)) x = T' v ω x)
    (hopen : ∀ v ω, ω ∉ pcsBad v → opened v ω) :
    (tableParts (fun v => (cc v).G) (fun v k ω => (cc v).vals (c v) (val v (ρ v ω)) k)
      (fun v k ω => (cc v).tvals (c v) (ρ v ω) (val v (ρ v ω)) (pubF0 v ω) (pubF1 v ω) ((cc v).wit (w v ω) (hr v ω)) k)
      (fun v ω => (cc v).tin (val v (ρ v ω)) ((cc v).wit (w v ω) (hr v ω)))
      (fun v ω => Flocked (t v) ((cc v).wit (w v ω) (hr v ω))) opened
      (fun v => (cc v).layerBad (c v) (s v) (val v) (ρ v) (pubF0 v) (pubF1 v) fun ω => (cc v).wit (w v ω) (hr v ω))
      (fun v => (cc v).balBad (fun ω => val v (ρ v ω)) fun ω => (cc v).wit (w v ω) (hr v ω))
      (fun v => (cc v).tabBad (c v) (s v) (val v) (ρ v) (fun ω => (cc v).wit (w v ω) (hr v ω)) (T' v))
      (fun v => (cc v).flBad (c v) (s v) (c v).outs (val v) (ρ v) (hr v) (T' v)) pcsBad crBad).Ok
      (fun v ω => RunHeld (c v) (s v) (c v).outs (st v ω) (val v) (ρ v ω)) := by
  refine tableParts_named c s hacc st val ρ cc hcc t (fun v ω => (cc v).wit (w v ω) (hr v ω)) hr T' pubF0 pubF1 pcsBad
    crBad opened hpub hτ (fun v ω => ?_) (fun v ω b _ j hj => ?_) hopT hopF hhintL hopen
  · obtain ⟨-, -, -, -, -, -, -, -, hzsc, hlsc, -, -, -, -, -, hro, hho, -⟩ := hcc v
    have e1 := FlockCert.heightOk_sem hho hzsc
    have e2 := FlockCert.roundsOk_sem hro hlsc
    have e3 := (hr v ω).hno
    have e4 := hτ v ω .hash (by simp [owned])
    have hno : (hr v ω).no = tauOf (w v ω) .hash := by omega
    calc (AirLink.rowsOf (t v) .hash).size ≤ (w v ω).height .hash := hfit v ω
      _ ≤ 2 ^ tauOf (w v ω) .hash := Nat.le_pow_clog (by norm_num) _
      _ = 2 ^ (hr v ω).no := by rw [hno]
  · simp [ChildCerts.wit, ported, hj]

end LeanVMCircuits.Rec.Edges
