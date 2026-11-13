module

public import LeanVM.Cost.Bounds.Guest.Kids
public import LeanVM.Cost.Decoder.Staged

/-!
# Bounds on the guest decoder's prices: the children's list and the raw signatures

Off the tables `decWitAt` builds (`Cost/Decoder/Staged.lean`, `Raw.lean`), in the price `G`
of a logarithm, `R` of a read of the memory, `S` of `main`'s valuation and the prices `W`, `WX`,
`WS` of the witness closures `wV`, `wX`, `wS`; every count below `2^34`:

* **`kidsT_cost`** (`kidsTPrice G R S W N K`): the children, at most `K ≤ 2^34`, the regions'
  tables of at most `N ≤ 2^34` marks (`decKid_cost`, `Kids.lean`);
* the raw signature at a slot's address (`xmssRawAt_cost`, `sphincsRawAt_cost`: the slot's claim,
  four reads, and the signature), of a mark (`xmssRaw_cost`, `sphincsRaw_cost`: one search in the
  region's table and a power in `K`), **`xmssRawsT_cost`**, **`sphincsRawsT_cost`**
  (`xmssRawsTPrice R WX X`, …): at most `X ≤ 2^34` raw signatures.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Guest.Fast LeanVM.Cost.Decoder
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram) {G : ℕ}

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

section Xmss

variable {wX : List E → LeanXmss.Signature} {wXV : MachineValue}
  (hwX : ∀ a : List E, RunsApp P wXV [encodeValue a] (encodeValue (wX a)))
  {WX : ℕ} (hWX : ∀ a : List E, a.length ≤ 56 → appCost P wXV [encodeValue a] ≤ WX)
include hwX hWX

/-- **The raw leanXMSS signature of mark `j` at the address `p53 · a`** (`xmssRawAtC`), `j < 2^35`,
`main_loop2`'s other arguments `args` at most `55` words: its slot's claim, `g^j` in `K` and the
signature at the iteration's arguments, at most `4·R + WX + 15100`. -/
theorem xmssRawAt_cost (hP : Includes P xmssRawAtC.costDeps) (p53 : E) (args : List E)
    (hargs : args.length ≤ 55) (a : K) (j : ℕ) (hj : j < 2 ^ 35) :
    machineCost P xmssRawAtC.costIdx [rdV, encodeValue p53, wXV, encodeValue args, encodeValue a,
      encodeValue j] ≤ 4 * R + WX + 15100 := by
  rw [xmssRawAtC.costEq P hP rd rdV hrd p53 wX wXV hwX]
  have h1 := xmssAtK_cost P hrd hR (by includes) (p53.limb 0 * a)
  have h2 := powSqK_cost_lt P (by includes) Parameters.g j 36 (by norm_num) (by norm_num) (by omega)
  have h3 := hWX (ofK (Parameters.g ^ j) :: args) (by simp; omega)
  omega

/-- **The raw leanXMSS signature of mark `j`** (`xmssRawC`) off a good table, `j < 2^35`: one
search, a power in `K`, then `xmssRawAt_cost`: at most `4·R + WX + 18800`. -/
theorem xmssRaw_cost (hP : Includes P xmssRawC.costDeps) (p53 : E) (args : List E)
    (hargs : args.length ≤ 55) (t : Array ℕ × Array ℕ) (ht : TableGood t) (j : ℕ) (hj : j < 2 ^ 35) :
    machineCost P xmssRawC.costIdx [rdV, encodeValue p53, wXV, encodeValue args, encodeValue t.1,
      encodeValue t.2, encodeValue j] ≤ 4 * R + WX + 18800 := by
  rw [xmssRawC.costEq P hP rd rdV hrd p53 wX wXV hwX]
  have h1 := slotIn_cost P (by includes) t.1 t.2 (lt64_of_good ht) ht.2.1 j (by omega)
  have hs := slotIn_lt ht j
  have h2 := powSqK_cost_lt P (by includes) Parameters.g (4 * slotIn t.1 t.2 j) 36 (by norm_num)
    (by norm_num) (by omega)
  have h3 := xmssRawAt_cost P hrd hR hwX hWX (by includes) p53 args hargs
    (Parameters.g ^ (4 * slotIn t.1 t.2 j)) j hj
  limbs_one
  omega

/-- The raw leanXMSS signatures' price, at most `X` of them. -/
@[expose] def xmssRawsTPrice (R WX X : ℕ) : ℕ := (4 * R + WX + 18850) * X + 30

/-- **The raw leanXMSS signatures** (`xmssRawsTC`), off a good table, `n ≤ X ≤ 2^34`, `main_loop2`'s
other arguments at most `55` words: at most `xmssRawsTPrice R WX X`. -/
theorem xmssRawsT_cost (hP : Includes P xmssRawsTC.costDeps) (p53 : E) (args : List E)
    (hargs : args.length ≤ 55) (t : Array ℕ × Array ℕ) (ht : TableGood t) (n X : ℕ)
    (hX : X ≤ 2 ^ 34) (hn : n ≤ X) :
    machineCost P xmssRawsTC.costIdx [rdV, encodeValue p53, wXV, encodeValue args, encodeValue t,
      encodeValue n] ≤ xmssRawsTPrice R WX X := by
  rw [xmssRawsTC.costEq P hP rd rdV hrd p53 wX wXV hwX]
  have h1 := rangeMap_le P (by includes) (by includes) (xmssRawT rd p53 wX args t.1 t.2)
    (.closure xmssRawsTC.lam0.costIdx [rdV, encodeValue p53, wXV, encodeValue args,
      encodeValue t.2, encodeValue t.1])
    (fun j ↦ RunsApp.of_spec (xmssRawsTC.lam0.costSpec P (by includes) rd rdV hrd p53 wX wXV hwX
      args t.2 t.1 j))
    (4 * R + WX + 18820) n X hn (by omega) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.nil_append,
        xmssRawsTC.lam0.costEq P (by includes) rd rdV hrd p53 wX wXV hwX, List.length_cons,
        List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons,
        List.length_nil]
      have := xmssRaw_cost P hrd hR hwX hWX (by includes) p53 args hargs t ht j (by omega)
      omega)
  unfold xmssRawsTPrice
  have : (4 * R + WX + 18820 + 28) * X ≤ (4 * R + WX + 18850) * X :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end Xmss

section Sphincs

variable {wS : E → Sphincs.Signature} {wSV : MachineValue}
  (hwS : ∀ a : E, RunsApp P wSV [encodeValue a] (encodeValue (wS a)))
  {WS : ℕ} (hWS : ∀ a : E, appCost P wSV [encodeValue a] ≤ WS)
include hwS hWS

/-- **The raw leanSPHINCS signature at the address `p56 · a`** (`sphincsRawAtC`), as
`xmssRawAt_cost`: at most `4·R + WS + 12600`. -/
theorem sphincsRawAt_cost (hP : Includes P sphincsRawAtC.costDeps) (p56 : E) (a : K) :
    machineCost P sphincsRawAtC.costIdx [rdV, encodeValue p56, wSV, encodeValue a] ≤
      4 * R + WS + 12600 := by
  rw [sphincsRawAtC.costEq P hP rd rdV hrd p56 wS wSV hwS]
  have h1 := sphincsAtK_cost P hrd hR (by includes) (p56.limb 0 * a)
  have h2 := mulK_cost P (by includes) p56 a
  have h3 := hWS (mulK p56 a)
  omega

/-- **The raw leanSPHINCS signature of mark `nrx + j`** (`sphincsRawC`) off a good table,
`nrx, j < 2^35`: at most `4·R + WS + 16300`. -/
theorem sphincsRaw_cost (hP : Includes P sphincsRawC.costDeps) (p56 : E) (t : Array ℕ × Array ℕ)
    (ht : TableGood t) (nrx j : ℕ) (hnrx : nrx < 2 ^ 35) (hj : j < 2 ^ 35) :
    machineCost P sphincsRawC.costIdx [rdV, encodeValue p56, wSV, encodeValue t.1, encodeValue t.2,
      encodeValue nrx, encodeValue j] ≤ 4 * R + WS + 16300 := by
  rw [sphincsRawC.costEq P hP rd rdV hrd p56 wS wSV hwS]
  have h1 := slotIn_cost P (by includes) t.1 t.2 (lt64_of_good ht) ht.2.1 (nrx + j) (by omega)
  have hs := slotIn_lt ht (nrx + j)
  have h2 := powSqK_cost_lt P (by includes) Parameters.g (4 * slotIn t.1 t.2 (nrx + j)) 36
    (by norm_num) (by norm_num) (by omega)
  have h3 := sphincsRawAt_cost P hrd hR hwS hWS (by includes) p56
    (Parameters.g ^ (4 * slotIn t.1 t.2 (nrx + j)))
  limbs_one
  omega

/-- The raw leanSPHINCS signatures' price, at most `X` of them. -/
@[expose] def sphincsRawsTPrice (R WS X : ℕ) : ℕ := (4 * R + WS + 16350) * X + 30

/-- **The raw leanSPHINCS signatures** (`sphincsRawsTC`), off a good table, `nrx ≤ 2^34`,
`n ≤ X ≤ 2^34`: at most `sphincsRawsTPrice R WS X`. -/
theorem sphincsRawsT_cost (hP : Includes P sphincsRawsTC.costDeps) (p56 : E)
    (t : Array ℕ × Array ℕ) (ht : TableGood t) (nrx n X : ℕ) (hnrx : nrx ≤ 2 ^ 34)
    (hX : X ≤ 2 ^ 34) (hn : n ≤ X) :
    machineCost P sphincsRawsTC.costIdx [rdV, encodeValue p56, wSV, encodeValue t,
      encodeValue nrx, encodeValue n] ≤ sphincsRawsTPrice R WS X := by
  rw [sphincsRawsTC.costEq P hP rd rdV hrd p56 wS wSV hwS]
  have h1 := rangeMap_le P (by includes) (by includes) (sphincsRawT rd p56 wS t.1 t.2 nrx)
    (.closure sphincsRawsTC.lam0.costIdx [rdV, encodeValue p56, wSV, encodeValue nrx,
      encodeValue t.2, encodeValue t.1])
    (fun j ↦ RunsApp.of_spec (sphincsRawsTC.lam0.costSpec P (by includes) rd rdV hrd p56 wS wSV
      hwS nrx t.2 t.1 j))
    (4 * R + WS + 16320) n X hn (by omega) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.nil_append,
        sphincsRawsTC.lam0.costEq P (by includes) rd rdV hrd p56 wS wSV hwS, List.length_cons,
        List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons,
        List.length_nil]
      have := sphincsRaw_cost P hrd hR hwS hWS (by includes) p56 t ht nrx j (by omega) (by omega)
      omega)
  unfold sphincsRawsTPrice
  have : (4 * R + WS + 16320 + 28) * X ≤ (4 * R + WS + 16350) * X :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end Sphincs

/-! ## The children -/

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

section Proof

variable {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
include hwV

/-- The children's price, at most `K` of them, the tables of at most `N` marks. -/
@[expose] def kidsTPrice (G R S W N K : ℕ) : ℕ := (decKidPrice G R S W N + 48) * K + 31

/-- **The children** (`kidsTC`), off good tables of at most `N ≤ 2^34` marks, `n ≤ K ≤ 2^34`, each
child's proof at most `W` (`wV` at its arguments, `subArgsK`): at most
`kidsTPrice G R S W N K = K·(decKidPrice G R S W N + 48) + 31`. -/
theorem kidsT_cost (D : DiscreteLogTables) (hP : Includes P kidsTC.costDeps)
    (hG : GLogBound P D G) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx)
    (hts : TableGood ts) (N : ℕ) (hN : N ≤ 2 ^ 34) (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N)
    (K : ℕ) (hK : K ≤ 2 ^ 34) (n : ℕ) (hn : n ≤ K) {W : ℕ}
    (hW : ∀ c < n, appCost P wVV [encodeValue (subArgsK rd σ c)] ≤ W) :
    machineCost P kidsTC.costIdx [encodeValue D, rdV, σV, wVV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue n] ≤ kidsTPrice G R S W N K := by
  rw [kidsTC.costEq P hP D rd rdV hrd σ σV hσ wV wVV hwV]
  have h1 := rangeMap_le P (by includes) (by includes) (decKidT D rd σ wV w380 p53 p56 tx ts)
    (.closure kidsTC.lam0.costIdx [encodeValue D, rdV, σV, wVV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts])
    (fun c ↦ RunsApp.of_spec (kidsTC.lam0.costSpec P (by includes) D rd rdV hrd σ σV hσ wV wVV hwV
      w380 p53 p56 tx ts c))
    (decKidPrice G R S W N + 20) n K hn (by omega) (fun c hc ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, kidsTC.lam0.costEq P (by includes) D rd rdV hrd σ σV hσ wV wVV hwV, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := decKid_cost P hrd hR hσ hS hwV D (by includes) hG w380 p53 p56 tx ts htx hts N hN
        htxN htsN c (by omega) (hW c hc)
      omega)
  unfold kidsTPrice
  have : (decKidPrice G R S W N + 20 + 28) * K = (decKidPrice G R S W N + 48) * K := by ring
  omega

end Proof

end Val

end Reader

end

end LeanVM.Cost.Bounds.Guest
