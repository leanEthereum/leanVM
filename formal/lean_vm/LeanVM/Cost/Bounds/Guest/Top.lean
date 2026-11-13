module

public import LeanVM.Cost.Bounds.Guest.Raw
public import LeanVM.Cost.Bounds.Guest.Frames
public import LeanVM.Cost.Bounds.Guest.Da
public import LeanVM.Cost.Bounds.Decoder.PreTest
public import LeanVM.Cost.Decoder.Witness

/-!
# Bounds on the guest decoder's prices: the witness

`Cost/Decoder/{Raw,Staged,Witness}.lean`: the witness off the tables (`decWitTabC`), the tables
built once (`decWitAtC`), the counts read (`decWitC`), and `decWitNC`, the callees' witnesses off
their frames; `main`'s valuation (`mainValC`). In the prices of a memory read `R`, of `main`'s
valuation `S`, of the frame map `F`, of a logarithm `G` (`GLogBound`), of the cursor's length `C`
(its value at most `L ≤ 2^32`), and of `da_verify`'s witness at its frame `DW` (`Bounds/Guest/Da.lean`):

* `nDirect_cost`, `dvClaim_cost`, `daWitness_cost`, `aggArgs_cost`, `nodeWitnessOf_cost`;
* `CountsWithin D σ K N X`: the counts read off `main`'s valuation bounded (at most `K` children,
  `N` slots a region, `X` declared claims and raw signatures a scheme);
* `decWitTab_cost` (`decWitTabPrice`), `decWitAt_cost` (`decWitAtPrice`), **`decWitC_cost`**
  (`decWitPrice G R S WX WS WD WV WA K N X`, the callees' witness functions' prices given);
* **`decWitN_cost`**: `decWitNC` at most `decWitNPrice G R S F C L DW K N X`;
* `mainVal_cost`: `main`'s valuation, at most `R + 1521`, for every value.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast

public section

variable (P : MachineProgram) {G : ℕ}

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A count read off `main`'s valuation (`nKidsC`, `lxSlotsC`, …): `S + G + 11`. -/
theorem nDirect_cost (D : DiscreteLogTables) (hP : Includes P Decoder.nDirectC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nDirectC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nDirectC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 7)); have := hS (.n 7); omega

theorem nKids_cost (D : DiscreteLogTables) (hP : Includes P Decoder.nKidsC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nKidsC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nKidsC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 6)); have := hS (.n 6); omega

theorem lxSlots_cost (D : DiscreteLogTables) (hP : Includes P Decoder.lxSlotsC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.lxSlotsC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.lxSlotsC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 22)); have := hS (.n 22); omega

theorem lsSlots_cost (D : DiscreteLogTables) (hP : Includes P Decoder.lsSlotsC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.lsSlotsC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.lsSlotsC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 23)); have := hS (.n 23); omega

theorem nRawX_cost (D : DiscreteLogTables) (hP : Includes P Decoder.nRawXC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nRawXC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nRawXC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 2)); have := hS (.n 2); omega

theorem nRawS_cost (D : DiscreteLogTables) (hP : Includes P Decoder.nRawSC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nRawSC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nRawSC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 5)); have := hS (.n 5); omega

/-- The DA claim (`dvClaimC`): `4·S + 93`. -/
theorem dvClaim_cost (hP : Includes P Decoder.dvClaimC.costDeps) :
    machineCost P Decoder.dvClaimC.costIdx [σV] ≤ 4 * S + 93 := by
  rw [Decoder.dvClaimC.costEq P hP σ σV hσ, digestOfCells_cost P (by includes)]
  cost_facts [hS]
  omega

/-- The words of `aggregate_claims`' call (`aggArgsC`): `6·S + 73`. -/
theorem aggArgs_cost (hP : Includes P Decoder.aggArgsC.costDeps) :
    machineCost P Decoder.aggArgsC.costIdx [σV] ≤ 6 * S + 73 := by
  rw [Decoder.aggArgsC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

/-- **`main_loop2`'s arguments after the counter** (`l2ArgsDC`): `55` reads, `55·S + 675`. -/
theorem l2ArgsD_cost (hP : Includes P Decoder.l2ArgsDC.costDeps) :
    machineCost P Decoder.l2ArgsDC.costIdx [σV] ≤ 55 * S + 675 := by
  rw [Decoder.l2ArgsDC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

/-- **The DA claim and matrix** (`daWitnessC`), the DA witness function's price at most `WD`:
`10·S + G + WD + 181`. -/
theorem daWitness_cost (D : DiscreteLogTables) (hP : Includes P Decoder.daWitnessC.costDeps)
    (hG : GLogBound P D G) {wD : List E → List E → LeanVM.Da.MatrixWitness} {wDV : MachineValue}
    (hwD : ∀ a b : List E, RunsApp P wDV [encodeValue a, encodeValue b] (encodeValue (wD a b)))
    {WD : ℕ} (hWD : ∀ a b : List E, a.length + b.length ≤ 16 →
      appCost P wDV [encodeValue a, encodeValue b] ≤ WD) :
    machineCost P Decoder.daWitnessC.costIdx [encodeValue D, σV, wDV] ≤ 10 * S + G + WD + 181 := by
  rw [Decoder.daWitnessC.costEq P hP D σ σV hσ wD wDV hwD]
  have := nDirect_cost P hσ hS D (by includes) hG
  have := dvClaim_cost P hσ hS (by includes)
  have := hWD [σ (.n 28)] [σ (.n 369), σ (.n 370), σ (.n 371)] (by simp)
  have : Decoder.nDirectD D σ < 2 ^ 34 := gLogD_lt D _
  cost_facts [hS]
  limbs_one
  split_ifs <;> omega

end Val

/-- A witness of its fields (`nodeWitnessOfC`): `11`. -/
theorem nodeWitnessOf_cost (hP : Includes P Decoder.nodeWitnessOfC.costDeps) (c : List LeanVM.Node.Child)
    (x : List (LeanVM.Node.LeanXmssClaim × LeanXmss.Signature))
    (s : List (LeanVM.Node.LeanSphincsClaim × Sphincs.Signature))
    (d : Option (LeanVM.Node.DaClaim × LeanVM.Da.MatrixWitness)) (h : LeanVM.Node.BatchingHints) :
    machineCost P Decoder.nodeWitnessOfC.costIdx
      [encodeValue c, encodeValue x, encodeValue s, encodeValue d, encodeValue h] = 11 := by
  rw [Decoder.nodeWitnessOfC.costEq P hP]

/-! ## The witness, the callees' witness functions given -/

/-- **The counts the witness reads off `main`'s valuation `σ` bounded** (`K`, `N`, `X` at most
`2^34`): at most `K` children, each region at most `N` slots, at most `X` declared claims and
`X` raw signatures of each scheme. Every `σ` meets it at `2^34` (`gLogD_lt`); a valid run at `16`, `65535`, `65535`
(`Bounds/Guest/Valid.lean`). -/
structure CountsWithin (D : DiscreteLogTables) (σ : Val) (K N X : ℕ) : Prop where
  kidsBound : K ≤ 2 ^ 34
  slotsBound : N ≤ 2 ^ 34
  claimsBound : X ≤ 2 ^ 34
  kids : Decoder.nKidsD D σ ≤ K
  xmssSlots : Decoder.lxSlotsD D σ ≤ N
  sphincsSlots : Decoder.lsSlotsD D σ ≤ N
  xmssClaims : Decoder.gLogD D (σ (.n 0)) ≤ X
  sphincsClaims : Decoder.gLogD D (σ (.n 3)) ≤ X
  rawXmss : Decoder.nRawXD D σ ≤ X
  rawSphincs : Decoder.nRawSD D σ ≤ X

section Witness

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {wX : List E → LeanXmss.Signature} {wXV : MachineValue}
  (hwX : ∀ a : List E, RunsApp P wXV [encodeValue a] (encodeValue (wX a)))
  {WX : ℕ} (hWX : ∀ a : List E, a.length ≤ 56 → appCost P wXV [encodeValue a] ≤ WX)
  {wS : E → Sphincs.Signature} {wSV : MachineValue}
  (hwS : ∀ a : E, RunsApp P wSV [encodeValue a] (encodeValue (wS a)))
  {WS : ℕ} (hWS : ∀ a : E, appCost P wSV [encodeValue a] ≤ WS)
  {wD : List E → List E → LeanVM.Da.MatrixWitness} {wDV : MachineValue}
  (hwD : ∀ a b : List E, RunsApp P wDV [encodeValue a, encodeValue b] (encodeValue (wD a b)))
  {WD : ℕ} (hWD : ∀ a b : List E, a.length + b.length ≤ 16 →
      appCost P wDV [encodeValue a, encodeValue b] ≤ WD)
  {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
  {WV : ℕ}
  {wA : List E → LeanVM.Node.BatchingHints} {wAV : MachineValue}
  (hwA : ∀ a : List E, RunsApp P wAV [encodeValue a] (encodeValue (wA a)))
  {WA : ℕ} (hWA : ∀ a : List E, a.length ≤ 16 → appCost P wAV [encodeValue a] ≤ WA)
include hrd hR hσ hS hwX hWX hwS hWS hwD hWD hwV hwA hWA

/-- The witness's price off the tables: at most `K` children, tables of at most `N` marks, at
most `X` raw signatures of each scheme. -/
@[expose] def decWitTabPrice (G R S WX WS WD WV WA K N X : ℕ) : ℕ :=
  kidsTPrice G R S WV N K + xmssRawsTPrice R WX X + sphincsRawsTPrice R WS X +
    (10 * S + G + WD + 181) + (6 * S + 73) + WA + 11 + 60

/-- **The witness off the tables** (`decWitTabC`), the tables good and of at most `N` marks, `nk ≤
K`, `nrx, nrs ≤ X` (`K, N, X ≤ 2^34`): at most `decWitTabPrice G R S WX WS WD WV WA K N X`. -/
theorem decWitTab_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decWitTabC.costDeps)
    (hG : GLogBound P D G) (K N X : ℕ) (hK : K ≤ 2 ^ 34) (hN : N ≤ 2 ^ 34) (hX : X ≤ 2 ^ 34)
    (nk nrx nrs : ℕ) (hnk : nk ≤ K) (hnrx : nrx ≤ X) (hnrs : nrs ≤ X)
    (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx) (hts : TableGood ts)
    (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N) (args : List E) (hargs : args.length ≤ 55)
    (hWV : ∀ c < nk, appCost P wVV [encodeValue (Decoder.subArgsK rd σ c)] ≤ WV) :
    machineCost P Decoder.decWitTabC.costIdx [encodeValue D, σV, rdV, wXV, wSV, wDV, wVV, wAV,
      encodeValue nk, encodeValue nrx, encodeValue nrs, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue args] ≤
      decWitTabPrice G R S WX WS WD WV WA K N X := by
  rw [Decoder.decWitTabC.costEq P hP D σ σV hσ rd rdV hrd wX wXV hwX wS wSV hwS wD wDV hwD wV wVV
    hwV wA wAV hwA]
  have := kidsT_cost P hrd hR hσ hS hwV D (by includes) hG w380 p53 p56 tx ts htx hts N hN htxN
    htsN K hK nk hnk hWV
  have := xmssRawsT_cost P hrd hR hwX hWX (by includes) p53 args hargs tx htx nrx X hX hnrx
  have := sphincsRawsT_cost P hrd hR hwS hWS (by includes) p56 ts hts nrx nrs X (by omega) hX
    hnrs
  have := daWitness_cost P hσ hS D (by includes) hG hwD hWD
  have := aggArgs_cost P hσ hS (by includes)
  have := hWA (Decoder.aggArgs σ) (by simp [Decoder.aggArgs])
  rw [nodeWitnessOf_cost P (by includes)]
  unfold decWitTabPrice
  omega

/-- The witness's price, the tables built. -/
@[expose] def decWitAtPrice (G R S WX WS WD WV WA K N X : ℕ) : ℕ :=
  5 * S + 2 * regionTablePrice G R N + decWitTabPrice G R S WX WS WD WV WA K N X + 92 +
    (55 * S + 675)

/-- **The witness, the counts given** (`decWitAtC`): the two regions' tables built once, then
`decWitTabC`: `nk ≤ K`, `lx, ls ≤ N`, `nrx, nrs ≤ X`, at most
`decWitAtPrice G R S WX WS WD WV WA K N X`. -/
theorem decWitAt_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decWitAtC.costDeps)
    (hG : GLogBound P D G) (K N X : ℕ) (hK : K ≤ 2 ^ 34) (hN : N ≤ 2 ^ 34) (hX : X ≤ 2 ^ 34)
    (nk lx ls nrx nrs : ℕ) (hnk : nk ≤ K) (hlx : lx < 2 ^ 34) (hls : ls ≤ 2 ^ 34) (hlxN : lx ≤ N)
    (hlsN : ls ≤ N) (hnrx : nrx ≤ X) (hnrs : nrs ≤ X)
    (hWV : ∀ c < nk, appCost P wVV [encodeValue (Decoder.subArgsK rd σ c)] ≤ WV) :
    machineCost P Decoder.decWitAtC.costIdx [encodeValue D, σV, rdV, wXV, wSV, wDV, wVV, wAV,
      encodeValue nk, encodeValue lx, encodeValue ls, encodeValue nrx, encodeValue nrs] ≤
      decWitAtPrice G R S WX WS WD WV WA K N X := by
  rw [Decoder.decWitAtC.costEq P hP D σ σV hσ rd rdV hrd wX wXV hwX wS wSV hwS wD wDV hwD wV wVV
    hwV wA wAV hwA]
  have h1 := regionTable_cost P hrd hR D (by includes) hG (σ (.n 45)) 0 lx (by norm_num) hlx.le
  have h2 := regionTable_cost P hrd hR D (by includes) hG (σ (.n 45)) lx ls hlx.le hls
  have := decWitTab_cost P hrd hR hσ hS hwX hWX hwS hWS hwD hWD hwV hwA hWA D (by includes) hG
    K N X hK hN hX nk nrx nrs hnk hnrx hnrs (σ (.n 398)) (σ (.n 31)) (σ (.n 34)) _ _
    (regionTable_good (rd := rd) D (σ (.n 45)) 0 lx hlx.le)
    (regionTable_good (rd := rd) D (σ (.n 45)) lx ls hls)
    ((regionTable_size_le (rd := rd) D (σ (.n 45)) 0 lx).trans hlxN)
    ((regionTable_size_le (rd := rd) D (σ (.n 45)) lx ls).trans hlsN) (Decoder.l2ArgsD σ)
    (by simp [Decoder.l2ArgsD]) hWV
  have := l2ArgsD_cost P hσ hS (by includes)
  have e1 : regionTablePrice G R lx ≤ regionTablePrice G R N := by
    unfold regionTablePrice; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hlxN) _
  have e2 : regionTablePrice G R ls ≤ regionTablePrice G R N := by
    unfold regionTablePrice; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hlsN) _
  cost_facts [hS]
  unfold decWitAtPrice
  omega

/-- The witness's price. -/
@[expose] def decWitPrice (G R S WX WS WD WV WA K N X : ℕ) : ℕ :=
  5 * (S + G + 11) + decWitAtPrice G R S WX WS WD WV WA K N X + 46

/-- **The witness** (`decWitC`), the logarithm's tables `D` given, the callees' witness functions'
prices given, the counts within `K N X` (`CountsWithin`): the counts (five logarithms), then
`decWitAtC`: at most `decWitPrice G R S WX WS WD WV WA K N X`. -/
theorem decWitC_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decWitC.costDeps)
    (hG : GLogBound P D G) {K N X : ℕ} (hc : CountsWithin D σ K N X)
    (hWV : ∀ c < Decoder.nKidsD D σ, appCost P wVV [encodeValue (Decoder.subArgsK rd σ c)] ≤ WV) :
    machineCost P Decoder.decWitC.costIdx [encodeValue D, σV, rdV, wXV, wSV, wDV, wVV, wAV] ≤
      decWitPrice G R S WX WS WD WV WA K N X := by
  rw [Decoder.decWitC.costEq P hP D σ σV hσ rd rdV hrd wX wXV hwX wS wSV hwS wD wDV hwD wV wVV
    hwV wA wAV hwA]
  have := nKids_cost P hσ hS D (by includes) hG
  have := lxSlots_cost P hσ hS D (by includes) hG
  have := lsSlots_cost P hσ hS D (by includes) hG
  have := nRawX_cost P hσ hS D (by includes) hG
  have := nRawS_cost P hσ hS D (by includes) hG
  have := decWitAt_cost P hrd hR hσ hS hwX hWX hwS hWS hwD hWD hwV hwA hWA D (by includes) hG
    K N X hc.kidsBound hc.slotsBound hc.claimsBound
    (Decoder.nKidsD D σ) (Decoder.lxSlotsD D σ) (Decoder.lsSlotsD D σ) (Decoder.nRawXD D σ)
    (Decoder.nRawSD D σ) hc.kids (gLogD_lt D _) (gLogD_lt D _).le hc.xmssSlots
    hc.sphincsSlots hc.rawXmss hc.rawSphincs hWV
  unfold decWitPrice
  omega

end Witness

/-! ## `decWitNC` -/

section Top

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
  {cl : E → E → ℕ} {clV : MachineValue}
  (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
  {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
  {L : ℕ} (hL32 : L ≤ 2 ^ 32)
include hrd hR hσ hS hVn hF hcl hC hL32

/-- **The guest decoder's witness's price**: `decWitC` at the five callees' witness functions'
prices, the signatures' readers' `WX`, `WS` given. -/
@[expose] def decWitNPrice (G R S F C L DW WX WS K N X : ℕ) : ℕ :=
  decWitPrice G R S WX WS (DW + 17)
    (vsPiPrice R (F + 9) F C L + 23) (48 * F + 47 * R + 142056) K N X + 29

/-- **The guest decoder's witness** (`decWitNC`), the logarithm's tables `D` and the readers'
tables `Tb` given, the leanSPHINCS reader `wS` of price at most `WS`, `da_verify`'s witness at its
frame at most `DW` (`dvWitN_cost` at `S = F + 9`), the counts within `K N X`, each child's cursor
length (at `verify_sub`'s frame of its arguments, `subArgsK`) at most `L`: at most
`decWitNPrice G R S F C L DW WS K N X`. -/
theorem decWitN_cost (D : DiscreteLogTables) (Tb : ReaderTabs) (hTb : ReaderTabsOK Tb)
    (hP : Includes P Decoder.decWitNC.costDeps) (hG : GLogBound P D G) (DW : ℕ)
    (hDW : ∀ args rets : List E, args.length + rets.length ≤ 16 → machineCost P Decoder.dvWitNC.costIdx
      [encodeValue D, .closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets],
        VnV] ≤ DW) {wX : List E → LeanXmss.Signature} {wXV : MachineValue}
    (hwX : ∀ a : List E, RunsApp P wXV [encodeValue a] (encodeValue (wX a)))
    {WX : ℕ} (hWX : ∀ a : List E, a.length ≤ 56 → appCost P wXV [encodeValue a] ≤ WX)
    {wS : E → Sphincs.Signature} {wSV : MachineValue}
    (hwS : ∀ a : E, RunsApp P wSV [encodeValue a] (encodeValue (wS a)))
    {WS : ℕ} (hWS : ∀ a : E, appCost P wSV [encodeValue a] ≤ WS) {K N X : ℕ}
    (hc : CountsWithin D σ K N X)
    (hLk : ∀ c < Decoder.nKidsD D σ, cl (Vn (fn_idx% verify_sub) (Decoder.subArgsK rd σ c) [] (.n 25))
      (Vn (fn_idx% verify_sub) (Decoder.subArgsK rd σ c) [] (.n 1919)) ≤ L) :
    machineCost P Decoder.decWitNC.costIdx [encodeValue D, encodeValue Tb, σV, rdV, VnV, wXV, wSV,
      clV] ≤ decWitNPrice G R S F C L DW WX WS K N X := by
  rw [Decoder.decWitNC.costEq P hP D Tb σ σV hσ rd rdV hrd Vn VnV hVn wX wXV hwX wS wSV hwS cl clV
    hcl]
  have h := decWitC_cost P hrd hR hσ hS hwX hWX hwS hWS
    (fun a b ↦ RunsApp.of_spec (Decoder.decWitNC.lam0.costSpec P (by includes) D Vn VnV hVn a b))
    (wD_cost P hVn D (by includes) DW hDW)
    (fun a ↦ RunsApp.of_spec (Decoder.decWitNC.lam1.costSpec P (by includes) Tb rd rdV hrd Vn VnV
      hVn cl clV hcl a))
    (fun a ↦ RunsApp.of_spec (Decoder.decWitNC.lam2.costSpec P (by includes) rd rdV hrd Vn VnV hVn a))
    (wA_cost P hVn hF hrd hR (by includes)) D (by includes) hG hc
    (fun c hc ↦ wV_cost P hVn hF hrd hR hcl hC hL32 (by includes) Tb hTb _
      (by simp [Decoder.subArgsK]) (hLk c hc))
  unfold decWitNPrice
  omega

end Top

/-! ## `main`'s valuation -/

theorem mainLocs_lt : ∀ x ∈ (Decoder.guestLocs.getD 1 #[]).toList, x < 2 ^ 20 := by
  decide +kernel

theorem mainLoc_lt (i : ℕ) : (Decoder.guestLocs.getD 1 #[]).getD i 0 < 2 ^ 20 := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : (Decoder.guestLocs.getD 1 #[])[i]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    exact mainLocs_lt x (Array.mem_toList_iff.2 (Array.mem_of_getElem? h))

/-- **`main`'s valuation** (`mainValC`, the cells' locations a literal of the program): a word of
`main`'s frame, for every value, at most `R + 1521`. -/
theorem mainVal_cost (hP : Includes P Decoder.mainValC.costDeps) {rd : Reader} {rdV : MachineValue}
    (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R) (v : V) :
    machineCost P Decoder.mainValC.costIdx [rdV, encodeValue v] ≤ R + 1521 := by
  rw [Decoder.mainValC.costEq P hP rd rdV hrd]
  have := wordWith_cost (P := P) (rd := rd) (rdVal := rdV) (hrd := hrd) (R := R) (hR := hR)
    (hW := (by norm_num : 0 < 20)) (hW64 := (by norm_num : 20 < 64)) (by includes) 1
    ((Decoder.guestLocs.getD 1 #[]).getD v.idx 0) (mainLoc_lt _)
  unfold psAt at this
  have hT := Decoder.guestLocsTableC.costEq P (by includes)
  omega

end

end LeanVM.Cost.Bounds.Guest
