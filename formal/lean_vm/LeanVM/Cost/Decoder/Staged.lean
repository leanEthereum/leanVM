module

public import LeanVM.Cost.Decoder.Raw
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: `decWit`, staged

`decWitStaged`: `B1.Main.decWit`'s fields, each list through a function of one entry by partial
application (`Raw.lean`, `Kids.lean`), the counts (logarithms) computed by the caller and passed to
`decWitAt`, the witness built by `nodeWitnessOf` from values, so that no heavy call sits under a
lambda or a `match` at the function's top level (the kernel does not check `decWit`'s spec compiled
as written: deep recursion, or over 40 GB); `Equations.lean`: `decWitStaged_eq : decWitStaged
discreteLogTables = decWit`. The callees' witness functions are parameters (closures), the
logarithm's tables `D` a value.

The searches over the coverage table read the two regions' tables (`regionTable`), built once
here, by `decWitAt`, and passed to `decWitTab` as values, with `main`'s words the loops read
(`written`, the tables' pointers) and the counts. The children (`kidsT`) and raw signatures
(`xmssRawsT`, `sphincsRawsT`) are those of `kidsAt`, `xmssRawsAt`, `sphincsRawsAt` (`kidsT_eq`,
`xmssRawsT_eq`, `sphincsRawsT_eq`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast LeanVM.Guest.Fast

@[expose] public section

/-- The children `0 … n - 1`. -/
noncomputable def kidsAt (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (n : ℕ) : List Child :=
  (List.range n).map (decKidD D rd σ wV)

/-- The raw leanXMSS signatures of marks `0 … n - 1`. -/
noncomputable def xmssRawsAt (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : List E → LeanXmss.Signature) (n : ℕ) : List (LeanXmssClaim × LeanXmss.Signature) :=
  (List.range n).map (rawXmssD D rd σ wX)

/-- The raw leanSPHINCS signatures `0 … n - 1`. -/
noncomputable def sphincsRawsAt (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (n : ℕ) : List (LeanSphincsClaim × Sphincs.Signature) :=
  (List.range n).map (rawSphincsD D rd σ wS)

/-- A witness of its five fields. Compiled as a function of its own: the compiled caller passes
the fields as values, so the kernel never matches a field (the DA option) that is not a variable
against its encoding (doing so unfolds it, here down to a logarithm by search). -/
def nodeWitnessOf (c : List Child) (x : List (LeanXmssClaim × LeanXmss.Signature))
    (s : List (LeanSphincsClaim × Sphincs.Signature))
    (d : Option (DaClaim × LeanVM.Da.MatrixWitness)) (h : BatchingHints) : NodeWitness :=
  ⟨c, x, s, d, h⟩

/-! ## Off the tables -/

/-- The children `0 … n - 1`, off the regions' tables. -/
noncomputable def kidsT (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ)
    (n : ℕ) : List Child :=
  (List.range n).map (decKidT D rd σ wV w380 p53 p56 tx ts)

/-- The raw leanXMSS signatures `0 … n - 1`, off the leanXMSS region's table, `__loop2`'s other
arguments `args` read once. -/
noncomputable def xmssRawsT (rd : Reader) (p53 : E) (wX : List E → LeanXmss.Signature)
    (args : List E) (tx : Array ℕ × Array ℕ) (n : ℕ) : List (LeanXmssClaim × LeanXmss.Signature) :=
  (List.range n).map (xmssRawT rd p53 wX args tx.1 tx.2)

/-- The raw leanSPHINCS signatures `0 … n - 1`, their marks from `nrx`, off the leanSPHINCS
region's table. -/
noncomputable def sphincsRawsT (rd : Reader) (p56 : E) (wS : E → Sphincs.Signature)
    (ts : Array ℕ × Array ℕ) (nrx n : ℕ) : List (LeanSphincsClaim × Sphincs.Signature) :=
  (List.range n).map (sphincsRawT rd p56 wS ts.1 ts.2 nrx)

theorem kidsT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (n : ℕ) :
    kidsT D rd σ wV (σ (.n 420)) (σ (.n 52)) (σ (.n 55)) (lxTable D rd σ) (lsTable D rd σ) n =
      kidsAt D rd σ wV n :=
  List.map_congr_left fun c _ ↦ decKidT_eq D rd σ wV c

theorem xmssRawsT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : List E → LeanXmss.Signature) (n : ℕ) :
    xmssRawsT rd (σ (.n 52)) wX (l2Args σ) (lxTable D rd σ) n = xmssRawsAt D rd σ wX n :=
  List.map_congr_left fun j _ ↦ xmssRawT_eq D rd σ wX j

theorem sphincsRawsT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (n : ℕ) :
    sphincsRawsT rd (σ (.n 55)) wS (lsTable D rd σ) (nRawXD D σ) n = sphincsRawsAt D rd σ wS n :=
  List.map_congr_left fun j _ ↦ sphincsRawT_eq D rd σ wS j

/-- The witness off the tables: `nk` children, `nrx`, `nrs` raw signatures, `main`'s word
`written` (`w380`), the tables' pointers, the regions' tables `tx`, `ts` and `__loop2`'s other
arguments `args`. -/
noncomputable def decWitTab (D : DiscreteLogTables) (σ : Val) (rd : Reader)
    (wX : List E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints)
    (nk nrx nrs : ℕ) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (args : List E) :
    NodeWitness :=
  nodeWitnessOf (kidsT D rd σ wV w380 p53 p56 tx ts nk) (xmssRawsT rd p53 wX args tx nrx)
    (sphincsRawsT rd p56 wS ts nrx nrs) (daWitness D σ wD) (wA (aggArgs σ))

/-- The witness, the counts given: the tables built here, once. -/
noncomputable def decWitAt (D : DiscreteLogTables) (σ : Val) (rd : Reader)
    (wX : List E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints)
    (nk lx ls nrx nrs : ℕ) : NodeWitness :=
  decWitTab D σ rd wX wS wD wV wA nk nrx nrs (σ (.n 420)) (σ (.n 52)) (σ (.n 55))
    (regionTable D rd (σ (.n 66)) 0 lx) (regionTable D rd (σ (.n 66)) lx ls) (l2ArgsD σ)

/-- **The witness, staged**: `decWit`'s fields through `decWitAt`, the counts (logarithms)
computed here, each list through a function of one entry by partial application, the logarithm's
tables `D` given. -/
noncomputable def decWitStaged (D : DiscreteLogTables) (σ : Val) (rd : Reader)
    (wX : List E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints) : NodeWitness :=
  decWitAt D σ rd wX wS wD wV wA (nKidsD D σ) (lxSlotsD D σ) (lsSlotsD D σ) (nRawXD D σ)
    (nRawSD D σ)

/-- **Off the tables, the witness is the unstaged lists'.** -/
theorem decWitStaged_eq_lists (D : DiscreteLogTables) (σ : Val) (rd : Reader)
    (wX : List E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → LeanVM.Protocol.Compile.Proof) (wA : List E → BatchingHints) :
    decWitStaged D σ rd wX wS wD wV wA =
      nodeWitnessOf (kidsAt D rd σ wV (nKidsD D σ)) (xmssRawsAt D rd σ wX (nRawXD D σ))
        (sphincsRawsAt D rd σ wS (nRawSD D σ)) (daWitness D σ wD) (wA (aggArgs σ)) := by
  unfold decWitStaged decWitAt decWitTab
  rw [kidsT_eq, l2ArgsD_eq, xmssRawsT_eq, sphincsRawsT_eq]

cost_compile kidsTC := kidsT
cost_compile xmssRawsTC := xmssRawsT
cost_compile sphincsRawsTC := sphincsRawsT
cost_compile nodeWitnessOfC := nodeWitnessOf
cost_compile decWitTabC := decWitTab
cost_compile decWitAtC := decWitAt
cost_compile decWitC := decWitStaged
end

end LeanVM.Cost.Decoder
