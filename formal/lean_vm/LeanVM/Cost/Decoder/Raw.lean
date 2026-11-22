module

public import LeanVM.Cost.Decoder.Xmss
import all LeanVM.Guest.B1.Main.Interface
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main»

/-!
# The guest decoder's compiled chain: the raw signatures

`decWit`'s parts of one entry: the raw leanXMSS and leanSPHINCS signature of mark `j`
(`rawXmssD`, `rawSphincsD`: the claim of the slot holding the mark and the signature at the
slot), the DA claim and matrix (`daWitness`), `aggregate_claims`' call words (`aggArgs`). Each
reads its logarithms by `gLogD D`, the logarithm's tables `D` given. Compiled off the regions'
tables (`xmssRawT`, `sphincsRawT`: the slot by one binary search, `slotIn`, then the claim and the
signature at the slot's address, `xmssRawAt`, `sphincsRawAt`), equal to `rawXmssD`, `rawSphincsD`
at the tables built (`xmssRawT_eq`, `sphincsRawT_eq`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast LeanVM.Guest.Fast

@[expose] public section

/-- The numbers of raw leanXMSS and leanSPHINCS signatures, of direct DA checks (`nRawX`,
`nRawS`, `nDirect`), the logarithm's tables `D` given. -/
def nRawXD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n (val% «main» "meta[2]")))
def nRawSD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n (val% «main» "meta[5]")))
def nDirectD (D : DiscreteLogTables) (σ : Val) : ℕ := gLogD D (σ (.n (val% «main» "meta[7]")))

theorem nRawXD_tables : nRawXD discreteLogTables = nRawX := by
  funext σ; unfold nRawXD nRawX; rw [gLogD_tables]
theorem nRawSD_tables : nRawSD discreteLogTables = nRawS := by
  funext σ; unfold nRawSD nRawS; rw [gLogD_tables]
theorem nDirectD_tables : nDirectD discreteLogTables = nDirect := by
  funext σ; unfold nDirectD nDirect; rw [gLogD_tables]

/-- **The raw leanXMSS signature of mark `j`** (`rawXmss`). -/
noncomputable def rawXmssD (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : List E → LeanXmss.Signature) (j : ℕ) : LeanXmssClaim × LeanXmss.Signature :=
  let s := slotOfD D rd σ 0 (lxSlotsD D σ) j
  (xmssAt rd (σ (.n (val% «main» "lx_table"))) s, wX (gen ^ j :: l2Args σ))

/-- **The raw leanSPHINCS signature of mark `n_raw_x + j`** (`rawSphincs`). -/
noncomputable def rawSphincsD (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (j : ℕ) : LeanSphincsClaim × Sphincs.Signature :=
  let s := slotOfD D rd σ (lxSlotsD D σ) (lsSlotsD D σ) (nRawXD D σ + j)
  (sphincsAt rd (σ (.n (val% «main» "lean_sphincs_table"))) s, wS (σ (.n (val% «main» "lean_sphincs_table")) * gen ^ (4 * s)))

theorem rawXmssD_tables : rawXmssD discreteLogTables = rawXmss := by
  funext rd σ wX j; unfold rawXmssD rawXmss; rw [slotOfD_tables, lxSlotsD_tables]
theorem rawSphincsD_tables : rawSphincsD discreteLogTables = rawSphincs := by
  funext rd σ wS j; unfold rawSphincsD rawSphincs
  rw [slotOfD_tables, lxSlotsD_tables, lsSlotsD_tables, nRawXD_tables]

/-- The DA claim and matrix `da_verify` checks, if the node checks one. -/
noncomputable def daWitness (D : DiscreteLogTables) (σ : Val)
    (wD : List E → List E → LeanVM.Da.MatrixWitness) :
    Option (DaClaim × LeanVM.Da.MatrixWitness) :=
  if nDirectD D σ = 1 then
    some (dvClaim σ, wD [σ (.n (val% «main» "byte_bits"))] [σ (.n (val% «main» "root_0")), σ (.n (val% «main» "root_1")), σ (.n (val% «main» "z"))])
  else none

/-- `main_loop2`'s arguments after the counter (`l2Args`), read one by one: `n_raw_x`, `lx_slots`,
`cover`, `lx_table` and the `51` carried chain indices (`main`'s `.n 304` to `.n 354`). -/
def l2ArgsD (σ : Val) : List E :=
  [σ (.n (val% «main» "meta[2]")), σ (.n (val% «main» "lx_slots_g")), σ (.n (val% «main» "cover")), σ (.n (val% «main» "lx_table")), σ (.n (val% «main» "lx_tags[0]")), σ (.n (val% «main» "lx_tags[1]")), σ (.n (val% «main» "lx_tags[2]")), σ (.n (val% «main» "lx_tags[3]")),
    σ (.n (val% «main» "lx_tags[4]")), σ (.n (val% «main» "lx_tags[5]")), σ (.n (val% «main» "lx_tags[6]")), σ (.n (val% «main» "lx_tags[7]")), σ (.n (val% «main» "lx_tags[8]")), σ (.n (val% «main» "lx_tags[9]")), σ (.n (val% «main» "lx_tags[10]")), σ (.n (val% «main» "lx_tags[11]")),
    σ (.n (val% «main» "lx_tags[12]")), σ (.n (val% «main» "lx_tags[13]")), σ (.n (val% «main» "lx_tags[14]")), σ (.n (val% «main» "lx_tags[15]")), σ (.n (val% «main» "lx_tags[16]")), σ (.n (val% «main» "lx_tags[17]")), σ (.n (val% «main» "lx_tags[18]")), σ (.n (val% «main» "lx_tags[19]")),
    σ (.n (val% «main» "lx_tags[20]")), σ (.n (val% «main» "lx_tags[21]")), σ (.n (val% «main» "lx_tags[22]")), σ (.n (val% «main» "lx_tags[23]")), σ (.n (val% «main» "lx_tags[24]")), σ (.n (val% «main» "lx_tags[25]")), σ (.n (val% «main» "lx_tags[26]")), σ (.n (val% «main» "lx_tags[27]")),
    σ (.n (val% «main» "lx_tags[28]")), σ (.n (val% «main» "lx_tags[29]")), σ (.n (val% «main» "lx_tags[30]")), σ (.n (val% «main» "lx_tags[31]")), σ (.n (val% «main» "lx_tags[32]")), σ (.n (val% «main» "lx_tags[33]")), σ (.n (val% «main» "lx_tags[34]")), σ (.n (val% «main» "lx_tags[35]")),
    σ (.n (val% «main» "lx_tags[36]")), σ (.n (val% «main» "lx_tags[37]")), σ (.n (val% «main» "lx_tags[38]")), σ (.n (val% «main» "lx_tags[39]")), σ (.n (val% «main» "lx_tags[40]")), σ (.n (val% «main» "lx_tags[41]")), σ (.n (val% «main» "lx_tags[42]")), σ (.n (val% «main» "lx_tags[43]")),
    σ (.n (val% «main» "lx_tags[44]")), σ (.n (val% «main» "lx_tags[45]")), σ (.n (val% «main» "lx_tags[46]")), σ (.n (val% «main» "lx_tags[47]")), σ (.n (val% «main» "lx_tags[48]")), σ (.n (val% «main» "lx_tags[49]")), σ (.n (val% «main» "lx_tags[50]"))]

theorem l2ArgsD_eq : l2ArgsD = l2Args := by
  funext σ
  simp [l2ArgsD, l2Args, List.range_succ]

/-- The words of `aggregate_claims`' call. -/
def aggArgs (σ : Val) : List E :=
  [σ (.n (val% «main» "meta[6]")), σ (.n (val% «main» "child_pi")), σ (.n (val% «main» "child_fresh")), σ (.n (val% «main» "child_carried")), σ (.n (val% «main» "defer_stmt")), σ (.n (val% «main» "s63.e.s0#1"))]

cost_compile nRawXC := nRawXD
cost_compile nRawSC := nRawSD
cost_compile nDirectC := nDirectD
cost_compile dvClaimC := dvClaim
cost_compile daWitnessC := daWitness
cost_compile aggArgsC := aggArgs
cost_compile l2ArgsDC := l2ArgsD

/-! ## The raw signatures, off the regions' tables

`rawXmssD` and `rawSphincsD` restated for the compiled chain: the slot holding a mark by `slotIn`
of the region's table (`regionTable`, built once by the caller; `slotIn_regionTable`), the slot's
address by a power in `K` (`mulK`), computed once. `xmssRawT_eq`, `sphincsRawT_eq`: at the tables
built they are `rawXmssD`, `rawSphincsD`. -/

/-- The raw leanXMSS signature of mark `j` at the address `p53 · a`: its slot's claim and `wX` at
`main_loop2`'s iteration `j` (its arguments `g^j :: args`, `args` the loop's others, `l2Args`). -/
noncomputable def xmssRawAt (rd : Reader) (p53 : E) (wX : List E → LeanXmss.Signature)
    (args : List E) (a : K) (j : ℕ) : LeanXmssClaim × LeanXmss.Signature :=
  (xmssAtK rd (p53.limb 0 * a), wX (ofK (Parameters.g ^ j) :: args))

/-- **The raw leanXMSS signature of mark `j`** (`rawXmssD`), off the region's table `tm`, `ts`,
`main_loop2`'s other arguments `args` read once. -/
noncomputable def xmssRawT (rd : Reader) (p53 : E) (wX : List E → LeanXmss.Signature)
    (args : List E) (tm ts : Array ℕ) (j : ℕ) : LeanXmssClaim × LeanXmss.Signature :=
  xmssRawAt rd p53 wX args (Parameters.g ^ (4 * slotIn tm ts j)) j

/-- The raw leanSPHINCS signature at the address `p56 · a`. -/
noncomputable def sphincsRawAt (rd : Reader) (p56 : E) (wS : E → Sphincs.Signature) (a : K) :
    LeanSphincsClaim × Sphincs.Signature :=
  (sphincsAtK rd (p56.limb 0 * a), wS (mulK p56 a))

/-- **The raw leanSPHINCS signature of mark `nrx + j`** (`rawSphincsD`), off the region's table. -/
noncomputable def sphincsRawT (rd : Reader) (p56 : E) (wS : E → Sphincs.Signature)
    (tm ts : Array ℕ) (nrx j : ℕ) : LeanSphincsClaim × Sphincs.Signature :=
  sphincsRawAt rd p56 wS (Parameters.g ^ (4 * slotIn tm ts (nrx + j)))

theorem xmssRawT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wX : List E → LeanXmss.Signature) (j : ℕ) :
    xmssRawT rd (σ (.n (val% «main» "lx_table"))) wX (l2Args σ) (lxTable D rd σ).1 (lxTable D rd σ).2 j =
      rawXmssD D rd σ wX j := by
  unfold xmssRawT xmssRawAt rawXmssD
  rw [slotIn_regionTable, ← xmssAt_eq_K, LeanVM.Guest.Value.gen_pow_eq_ofK]

theorem sphincsRawT_eq (D : DiscreteLogTables) (rd : Reader) (σ : Val)
    (wS : E → Sphincs.Signature) (j : ℕ) :
    sphincsRawT rd (σ (.n (val% «main» "lean_sphincs_table"))) wS (lsTable D rd σ).1 (lsTable D rd σ).2 (nRawXD D σ) j =
      rawSphincsD D rd σ wS j := by
  unfold sphincsRawT sphincsRawAt rawSphincsD
  rw [slotIn_regionTable, mulK_gen_pow, ← sphincsAt_eq_K]

cost_compile xmssRawAtC := xmssRawAt
cost_compile xmssRawC := xmssRawT
cost_compile sphincsRawAtC := sphincsRawAt
cost_compile sphincsRawC := sphincsRawT

end

end LeanVM.Cost.Decoder
