module

public import LeanVM.Cost.Decoder.Log
public import LeanVM.Guest.B1.Sig.Bytes
public import Statement.Theorems
import all LeanVM.Guest.B1.Sig.Interface
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the cell readers, the seed and the statement

`B1.Main`'s readers of `main`'s frame and the memory, compiled bottom-up, each a function of its
own, under the statement's encodings of their values (`Statement/LeanVmGuest.lean`):

* the cells' digests and claims: `digestOfCells`, `deferOfCells`, `fixedOfCells`, and a
  signature claim's four cells (`Sig.xmssClaimOf`, `Sig.sphincsClaimOf`; a bit vector of cells
  through `cellVal_eq`, `cellPairVal_eq`: its number, a `BitVec.ofFin`);
* the memory's cells (`cellAt`, `readCells`, `slotCells`), the claims of a table's slots
  (`xmssAt`, `sphincsAt`), a DA digest's slot (`daDigestAt`);
* **the seed** (`decSeed`) and **the statement** (`decStmt`; compiled `decStmtD`, the
  logarithm's tables `D` given, `decStmtD_tables`).

The reader `rd` (the memory's index, `Located.readIn`) and `main`'s valuation `σ` are closures,
the logarithm's tables `D` a value: the decoder's top level supplies them.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.B1 LeanVM.Guest.B1.Main

@[expose] public section

/-! ## Cells -/

-- a power in `E` by squaring, under a name of its own (the bounds name it, not an index)
cost_compile powSqEC measure fun _ n ↦ n := LeanVM.Cost.Rewrite.powSq (M := E)
cost_compile digestOfCellsC := Main.digestOfCells
cost_compile deferOfCellsC := deferOfCells
cost_compile fixedOfCellsC := fixedOfCells

/-! ## A signature claim's cells: bit vectors as their numbers -/

theorem kToNat_lane (a : K) : LeanVM.Protocol.Verifier.kToNat a = (K.lane a).toNat := rfl
cost_rewrite kToNat_lane

theorem cellNat_lt (c : E) : Sig.cellNat c < 2 ^ 128 := by
  rw [← Sig.toNat_cellVal]; exact BitVec.isLt _

/-- A cell's `128` bits, as their number (`++` unfolds to `Nat.lor` and shifts). -/
theorem cellVal_eq (c : E) : Sig.cellVal c = BitVec.ofFin ⟨Sig.cellNat c, cellNat_lt c⟩ :=
  BitVec.eq_of_toNat_eq (by rw [Sig.toNat_cellVal]; rfl)
cost_rewrite cellVal_eq

/-- Two cells' `256` bits, as their number. -/
theorem cellPairVal_eq (lo hi : E) : Sig.cellPairVal lo hi =
    BitVec.ofFin ⟨Sig.cellNat lo + 2 ^ 128 * Sig.cellNat hi, by
      have := cellNat_lt lo; have := cellNat_lt hi; omega⟩ := by
  apply BitVec.eq_of_toNat_eq
  rw [Sig.cellPairVal, BitVec.toNat_append, Sig.toNat_cellVal, Sig.toNat_cellVal,
    Nat.shiftLeft_eq, mul_comm, LeanVM.Guest.Value.two_pow_mul_or (cellNat_lt lo)]
  simp only [BitVec.toNat_ofFin]; omega
cost_rewrite cellPairVal_eq

cost_compile cellNatC := Sig.cellNat
cost_compile xmssClaimOfC := Sig.xmssClaimOf
cost_compile sphincsClaimOfC := Sig.sphincsClaimOf

/-! ## The memory's cells -/

cost_compile cellAtC := cellAt
cost_compile readCellsC := readCells
cost_compile slotCellsC := slotCells
cost_compile xmssAtC := xmssAt
cost_compile sphincsAtC := sphincsAt
cost_compile daDigestAtC := daDigestAt

/-! ## The seed and the statement -/

cost_compile decSeedC := decSeed

/-! ## A slot's claim at its address's low limb

A table's slot `s` at `p` is at `p · g^(4s)`, and its cells are read off the address's low limb
(`cellAt`). `p * gen ^ n` compiled multiplies in `E` with the power substituted in each of its
three limbs (three exponentiations); here the power is taken once, in `K`:

* `mulK p x`: `p` times `x ∈ K`, limb by limb (`mulK_gen_pow : mulK p (g^n) = p * gen^n`);
* `readCellsK rd x n`: the `n` cells from the address of low limb `x` (`readCells_mul_gen_pow`);
* `xmssAtK`, `sphincsAtK`: a slot's claim at its address's low limb (`xmssAt_eq_K`);
* `xmssRun rd step x n`: the claims of `n` consecutive slots, the address advanced by `step = g^4`
  (one multiplication per slot; `xmssRun_eq`). -/

open LeanVM.Guest.Core LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Guest.B1.Digest LeanVM.Node

/-- `p · x`, `x ∈ K`, limb by limb. -/
def mulK (p : E) (x : K) : E := E.ofLimbs (p.limb 0 * x) (p.limb 1 * x)

theorem mulK_gen_pow (p : E) (n : ℕ) : mulK p (Parameters.g ^ n) = p * gen ^ n :=
  (LeanVM.Guest.Fast.mul_gen_pow_eq p n).symm

/-- The `n` cells from the address of low limb `x`. -/
noncomputable def readCellsK (rd : Reader) (x : K) (n : ℕ) : List E := readCells rd (E.ofLimbs x 0) n

theorem readCells_mul_gen_pow (rd : Reader) (p : E) (k n : ℕ) :
    readCells rd (p * gen ^ k) n = readCellsK rd (p.limb 0 * Parameters.g ^ k) n := by
  unfold readCellsK readCells cellAt
  rw [LeanVM.Guest.Fast.mul_gen_pow_eq]
  rfl

/-- The leanXMSS claim of the slot at the address of low limb `x` (`xmssAt`). -/
noncomputable def xmssAtK (rd : Reader) (x : K) : LeanXmssClaim :=
  let c := readCellsK rd x 4
  Sig.xmssClaimOf (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) (c.getD 3 0)

/-- The leanSPHINCS claim of the slot at the address of low limb `x` (`sphincsAt`). -/
noncomputable def sphincsAtK (rd : Reader) (x : K) : LeanSphincsClaim :=
  let c := readCellsK rd x 4
  Sig.sphincsClaimOf (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) (c.getD 3 0)

theorem xmssAt_eq_K (rd : Reader) (p : E) (s : ℕ) :
    xmssAt rd p s = xmssAtK rd (p.limb 0 * Parameters.g ^ (4 * s)) := by
  unfold xmssAt xmssAtK slotCells
  rw [readCells_mul_gen_pow]

theorem sphincsAt_eq_K (rd : Reader) (p : E) (s : ℕ) :
    sphincsAt rd p s = sphincsAtK rd (p.limb 0 * Parameters.g ^ (4 * s)) := by
  unfold sphincsAt sphincsAtK slotCells
  rw [readCells_mul_gen_pow]

/-- The leanXMSS claims of `n` consecutive slots from the address of low limb `x`, the address
advanced by `step`. -/
noncomputable def xmssRun (rd : Reader) (step x : K) : ℕ → List LeanXmssClaim
  | 0 => []
  | n + 1 => xmssAtK rd x :: xmssRun rd step (x * step) n

/-- The leanSPHINCS claims of `n` consecutive slots (`xmssRun`). -/
noncomputable def sphincsRun (rd : Reader) (step x : K) : ℕ → List LeanSphincsClaim
  | 0 => []
  | n + 1 => sphincsAtK rd x :: sphincsRun rd step (x * step) n

theorem gpow_four_mul_succ (a : K) (s : ℕ) :
    a * Parameters.g ^ (4 * s) * Parameters.g ^ 4 = a * Parameters.g ^ (4 * (s + 1)) := by
  rw [mul_assoc, ← pow_add]; ring_nf

theorem xmssRun_eq (rd : Reader) (p : E) :
    ∀ n s, xmssRun rd (Parameters.g ^ 4) (p.limb 0 * Parameters.g ^ (4 * s)) n =
      (List.range' s n).map (xmssAt rd p)
  | 0, _ => rfl
  | n + 1, s => by
    rw [xmssRun.eq_2, gpow_four_mul_succ, xmssRun_eq rd p n (s + 1), List.range'_succ, List.map_cons,
      xmssAt_eq_K]

theorem sphincsRun_eq (rd : Reader) (p : E) :
    ∀ n s, sphincsRun rd (Parameters.g ^ 4) (p.limb 0 * Parameters.g ^ (4 * s)) n =
      (List.range' s n).map (sphincsAt rd p)
  | 0, _ => rfl
  | n + 1, s => by
    rw [sphincsRun.eq_2, gpow_four_mul_succ, sphincsRun_eq rd p n (s + 1), List.range'_succ,
      List.map_cons, sphincsAt_eq_K]

/-- The declared claims of a table at `p`, slots `0 … n - 1`. -/
theorem xmssRun_range (rd : Reader) (p : E) (n : ℕ) :
    xmssRun rd (Parameters.g ^ 4) (p.limb 0) n = (List.range n).map (xmssAt rd p) := by
  have := xmssRun_eq rd p n 0
  rwa [Nat.mul_zero, pow_zero, mul_one, ← List.range_eq_range'] at this

theorem sphincsRun_range (rd : Reader) (p : E) (n : ℕ) :
    sphincsRun rd (Parameters.g ^ 4) (p.limb 0) n = (List.range n).map (sphincsAt rd p) := by
  have := sphincsRun_eq rd p n 0
  rwa [Nat.mul_zero, pow_zero, mul_one, ← List.range_eq_range'] at this

/-- The DA digest of slot `k` of the digests at `p` (`daDigestAt`, `p = da_digests`). -/
noncomputable def daDigestAtP (rd : Reader) (p : E) (k : ℕ) : Digest :=
  Main.digestOfCells (cellAt rd p (2 * k)) (cellAt rd p (2 * k + 1))

cost_compile mulKC := mulK
cost_compile readCellsKC := readCellsK
cost_compile xmssAtKC := xmssAtK
cost_compile sphincsAtKC := sphincsAtK
cost_compile xmssRunC measure fun _ _ _ n ↦ n := xmssRun
cost_compile sphincsRunC measure fun _ _ _ n ↦ n := sphincsRun
cost_compile daDigestAtPC := daDigestAtP

/-- The statement, its counts given: `n0` declared leanXMSS claims at `p53`, `n3` leanSPHINCS
claims at `p56` (each table's slots in a run, `xmssRun`), the DA digest of slot `pick` of the
digests at `p334`, the deferred claim at `p402`. -/
noncomputable def decStmtAt (rd : Reader) (p53 p56 p334 p402 : E) (n0 n3 pick : ℕ) :
    NodeStatement :=
  ⟨⟨xmssRun rd (Parameters.g ^ 4) (p53.limb 0) n0, sphincsRun rd (Parameters.g ^ 4) (p56.limb 0) n3,
    daDigestAtP rd p334 pick⟩,
   deferOfCells (readCells rd p402 24)⟩

open LeanVM.Extraction.Fast in
/-- **The statement** (`decStmt`), the logarithm's tables `D` given: the counts (logarithms)
computed here and passed to `decStmtAt`. -/
noncomputable def decStmtD (D : DiscreteLogTables) (σ : Val) (rd : Reader) : NodeStatement :=
  decStmtAt rd (σ (.n 52)) (σ (.n 55)) (σ (.n 385)) (σ (.n 437)) (gLogD D (σ (.n 0)))
    (gLogD D (σ (.n 3))) (gLogD D (σ (.n 426)))

open LeanVM.Extraction.Fast in
theorem decStmtD_tables : decStmtD discreteLogTables = decStmt := by
  funext σ rd
  unfold decStmtD decStmtAt decStmt
  rw [gLogD_tables, xmssRun_range, sphincsRun_range]
  rfl

cost_compile decStmtAtC := decStmtAt

cost_compile decStmtC := decStmtD

end

end LeanVM.Cost.Decoder
