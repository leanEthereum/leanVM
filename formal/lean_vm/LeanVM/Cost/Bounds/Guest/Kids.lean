module

public import LeanVM.Cost.Bounds.Guest.Search
public import LeanVM.Cost.Bounds.Guest.Stmt

/-!
# Bounds on the guest decoder's prices: the coverage tables and the children

The tables `decWitAt` builds once and the children off them (`Cost/Decoder/Kids.lean`), in the
price `G` of a logarithm (`GLogBound P D G`), `R` of a read of the memory, `S` of `main`'s
valuation and `W` of the child proofs' reader `wV`; every count, mark and slot below `2^34`
(`gLogD_lt`):

* a mark and its slot (`markPair_cost`), **`regionTable_cost`** (`regionTablePrice G R len`: one
  logarithm and one read per slot, the table sorted, `coverTable_cost`), `regionTable_good`;
* a running count (`countAtW_cost`);
* a child's claim at a slot (`xmssSlotClaim_cost`, `sphincsSlotClaim_cost`: a power in `K`, four
  reads), a child's statement off its lists' slots (`kidStmtAt_cost`), its segment
  (`kidStmtSeg_cost`: the slots off the tables, `kidSlotsIn_cost`, `Search.lean`), **`kidStmt_cost`** (`kidStmtPrice G R S N`), `subArgs_cost`,
  **`decKid_cost`** (`decKidPrice G R S W N`), the regions' tables of at most `N ≤ 2^34` marks
  (`regionTable_size_le`: a region's slots; `2^34` on any memory, `65535` on a valid run), so
  at most `N` claims of each scheme a child. The children's list is `Raw.lean`'s
  `kidsT_cost`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Guest.Fast LeanVM.Cost.Decoder
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram) {G : ℕ}

/-! ## Facts of the tables -/

/-! ## The tables -/

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- **A slot's mark and the slot** (`markPairC`), `lo + s < 2^40`: at most `G + R + 2984`. -/
theorem markPair_cost (D : DiscreteLogTables) (hP : Includes P markPairC.costDeps)
    (hG : GLogBound P D G) (cover : E) (lo s : ℕ) (h : lo + s < 2 ^ 40) :
    machineCost P markPairC.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue lo,
      encodeValue s] ≤ G + R + 2984 := by
  rw [markPairC.costEq P hP D rd rdV hrd, markPairOfC.costEq P (by includes)]
  have := cellAt_cost P hrd hR (by includes) cover (lo + s) h
  have := hG (cellAt rd cover (lo + s))
  limbs_one
  omega

/-- The coverage table's price for a region of `len` slots. -/
@[expose] def regionTablePrice (G R len : ℕ) : ℕ := (G + R + 8427) * len + 835

/-- **The coverage table of the region `[lo, lo + len)`** (`regionTableC`), `lo, len ≤ 2^34`: one
mark per slot, then sorted: at most `regionTablePrice G R len = (G + R + 8427)·len + 835`. -/
theorem regionTable_cost (D : DiscreteLogTables) (hP : Includes P regionTableC.costDeps)
    (hG : GLogBound P D G) (cover : E) (lo len : ℕ) (hlo : lo ≤ 2 ^ 34) (hlen : len ≤ 2 ^ 34) :
    machineCost P regionTableC.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue lo,
      encodeValue len] ≤ regionTablePrice G R len := by
  rw [regionTableC.costEq P hP D rd rdV hrd]
  have h1 := rangeMap_le P (by includes) (by includes) (markPair D rd cover lo)
    (.closure regionTableC.lam0.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue lo])
    (fun s ↦ RunsApp.of_spec (regionTableC.lam0.costSpec P (by includes) D rd rdV hrd cover lo s))
    (G + R + 2994) len len (le_refl _) (by omega) (fun s hs ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, regionTableC.lam0.costEq P (by includes) D rd rdV hrd, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := markPair_cost P hrd hR D (by includes) hG cover lo s (by omega)
      omega)
  have h2 := coverTable_cost P (by includes) ((List.range len).map (markPair D rd cover lo))
    (by simp; omega) (fun p hp ↦ by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
      rw [List.mem_range] at hs
      have := gLogD_lt D (cellAt rd cover (lo + s))
      exact ⟨by simp only [markPair, markPairOf]; omega, by simp only [markPair, markPairOf]; omega⟩)
  simp only [List.length_map, List.length_range] at h2
  unfold regionTablePrice
  unfold coverTablePrice at h2
  nlinarith

omit hrd hR in
/-- **A region's coverage table is good**, `len ≤ 2^34`. -/
theorem regionTable_good (D : DiscreteLogTables) (cover : E) (lo len : ℕ) (hlen : len ≤ 2 ^ 34) :
    TableGood (regionTable D rd cover lo len) :=
  coverTable_good _ (by simp; omega) (fun p hp ↦ by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
    rw [List.mem_range] at hs
    exact ⟨gLogD_lt D _, by simp only [markPair, markPairOf]; omega⟩)

omit hrd hR in
/-- The region's table has at most `len` marks. -/
theorem regionTable_size_le (D : DiscreteLogTables) (cover : E) (lo len : ℕ) :
    (regionTable D rd cover lo len).1.size ≤ len := by
  have hK := length_coverKeys_le ((List.range len).map (markPair D rd cover lo))
  simp only [regionTable, coverTable, List.size_toArray, List.length_map, List.length_range] at hK ⊢
  exact hK

/-- A running count (`countAtWC`), `c < 2^40`: at most `G + R + 2975`. -/
theorem countAtW_cost (D : DiscreteLogTables) (hP : Includes P countAtWC.costDeps)
    (hG : GLogBound P D G) (w : E) (c : ℕ) (hc : c < 2 ^ 40) :
    machineCost P countAtWC.costIdx [encodeValue D, rdV, encodeValue w, encodeValue c] ≤
      G + R + 2975 := by
  rw [countAtWC.costEq P hP D rd rdV hrd]
  have := cellAt_cost P hrd hR (by includes) w c hc
  have := hG (cellAt rd w c)
  omega

/-! ## A child -/

/-- **A child's leanXMSS claim at slot `s`** (`xmssSlotClaimC`), `s < 2^34`: a power in `K` and
four reads, at most `4·R + 14996`. -/
theorem xmssSlotClaim_cost (hP : Includes P xmssSlotClaimC.costDeps) (p52 : E) (s : ℕ)
    (hs : s < 2 ^ 34) :
    machineCost P xmssSlotClaimC.costIdx [rdV, encodeValue p52, encodeValue s] ≤ 4 * R + 14996 := by
  rw [xmssSlotClaimC.costEq P hP rd rdV hrd]
  have h2 := powSqK_cost_lt P (by includes) Parameters.g (4 * s) 36 (by norm_num) (by norm_num)
    (by omega)
  have h3 := xmssAtK_cost P hrd hR (by includes) (p52.limb 0 * Parameters.g ^ (4 * s))
  limbs_one
  omega

/-- **A child's leanSPHINCS claim at slot `s`** (`sphincsSlotClaimC`), as `xmssSlotClaim_cost`. -/
theorem sphincsSlotClaim_cost (hP : Includes P sphincsSlotClaimC.costDeps) (p55 : E) (s : ℕ)
    (hs : s < 2 ^ 34) :
    machineCost P sphincsSlotClaimC.costIdx [rdV, encodeValue p55, encodeValue s] ≤
      4 * R + 14996 := by
  rw [sphincsSlotClaimC.costEq P hP rd rdV hrd]
  have h2 := powSqK_cost_lt P (by includes) Parameters.g (4 * s) 36 (by norm_num) (by norm_num)
    (by omega)
  have h3 := sphincsAtK_cost P hrd hR (by includes) (p55.limb 0 * Parameters.g ^ (4 * s))
  limbs_one
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A child's statement's price off its lists' slots, at most `N` a list. -/
@[expose] def kidStmtAtPrice (R S N : ℕ) : ℕ := (8 * R + 30050) * N + 26 * R + 3 * S + 81877

/-- **A child's statement, its lists' slots given** (`kidStmtAtC`), `c < 2^34`, at most `N` slots
a list, each below `2^34`: a claim a slot (`xmssSlotClaim_cost`), the DA digest and the deferred
claim: at most `kidStmtAtPrice R S N = (8·R + 30050)·N + …`. -/
theorem kidStmtAt_cost (hP : Includes P kidStmtAtC.costDeps) (p52 p55 : E) (c : ℕ)
    (sx ss : List ℕ) (hc : c < 2 ^ 34) (N : ℕ) (hsx : sx.length ≤ N) (hss : ss.length ≤ N)
    (hsx' : ∀ s ∈ sx, s < 2 ^ 34) (hss' : ∀ s ∈ ss, s < 2 ^ 34) :
    machineCost P kidStmtAtC.costIdx [rdV, σV, encodeValue p52, encodeValue p55, encodeValue c,
      encodeValue sx, encodeValue ss] ≤ kidStmtAtPrice R S N := by
  rw [kidStmtAtC.costEq P hP rd rdV hrd σ σV hσ]
  have h1 := map_cost P (by includes) (xmssSlotClaim rd p52)
    (.closure kidStmtAtC.lam0.costIdx [rdV, encodeValue p52])
    (fun s ↦ RunsApp.of_spec (kidStmtAtC.lam0.costSpec P (by includes) rd rdV hrd p52 s))
    (4 * R + 15012) sx (fun s hs ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        kidStmtAtC.lam0.costEq P (by includes) rd rdV hrd, List.length_cons, List.length_cons,
        List.length_nil]
      have := xmssSlotClaim_cost P hrd hR (by includes) p52 s (hsx' s hs)
      omega)
  have h2 := map_cost P (by includes) (sphincsSlotClaim rd p55)
    (.closure kidStmtAtC.lam1.costIdx [rdV, encodeValue p55])
    (fun s ↦ RunsApp.of_spec (kidStmtAtC.lam1.costSpec P (by includes) rd rdV hrd p55 s))
    (4 * R + 15012) ss (fun s hs ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        kidStmtAtC.lam1.costEq P (by includes) rd rdV hrd, List.length_cons, List.length_cons,
        List.length_nil]
      have := sphincsSlotClaim_cost P hrd hR (by includes) p55 s (hss' s hs)
      omega)
  have m1 := Nat.mul_le_mul_left (4 * R + 15012 + 13) hsx
  have m2 := Nat.mul_le_mul_left (4 * R + 15012 + 13) hss
  have h3 := daDigestAt_cost P hrd hR hσ hS (by includes) c (by omega)
  have h4 := hS (.n 395)
  have h5 := powSqK_cost_lt P (by includes) Parameters.g (24 * c) 39 (by norm_num) (by norm_num)
    (by omega)
  have h6 := readCellsK_cost P hrd hR (by includes) ((σ (.n 395)).limb 0 * Parameters.g ^ (24 * c))
    24 (by norm_num)
  have h7 := deferOfCells_cost P (by includes)
    (readCellsK rd ((σ (.n 395)).limb 0 * Parameters.g ^ (24 * c)) 24)
  limbs_one
  unfold kidStmtAtPrice
  have : (4 * R + 15012 + 13) * N + (4 * R + 15012 + 13) * N = (8 * R + 30050) * N := by ring
  omega

/-- **A child's statement, its segment `[a, b)` given** (`kidStmtSegC`), the tables of at most `N`
marks: its lists' slots off the tables (`kidSlotsIn_cost`, a count between), then
`kidStmtAt_cost`. -/
theorem kidStmtSeg_cost (hP : Includes P kidStmtSegC.costDeps) (p52 p55 : E)
    (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx) (hts : TableGood ts) (c a b : ℕ)
    (hc : c < 2 ^ 34) (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) (N : ℕ) (hN : N ≤ 2 ^ 34)
    (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N) :
    machineCost P kidStmtSegC.costIdx [rdV, σV, encodeValue p52, encodeValue p55, encodeValue tx,
      encodeValue ts, encodeValue c, encodeValue a, encodeValue b] ≤
      kidStmtAtPrice R S N + 2 * kidSlotsInPrice N + 1890 := by
  rw [kidStmtSegC.costEq P hP rd rdV hrd σ σV hσ]
  have h0 := countIn_le tx.1 a b
  have h1 := countIn_cost P (by includes) tx.1 (lt64_of_good htx) htx.2.1 a b (by omega) (by omega)
  have h2 := kidSlotsIn_cost P (by includes) htx a b (by omega) (by omega) N htxN
  have h3 := kidSlotsIn_cost P (by includes) hts (a + countIn tx.1 a b) b (by omega) (by omega)
    N htsN
  have h4 := kidStmtAt_cost P hrd hR hσ hS (by includes) p52 p55 c
    (kidSlotsIn tx.1 tx.2 a b) (kidSlotsIn ts.1 ts.2 (a + countIn tx.1 a b) b) hc N
    ((kidSlotsIn_length_le tx.1 tx.2 a b).trans htxN)
    ((kidSlotsIn_length_le ts.1 ts.2 _ b).trans htsN)
    (kidSlotsIn_lt htx a b) (kidSlotsIn_lt hts _ b)
  limbs_one
  omega

/-- A child's statement's price. -/
@[expose] def kidStmtPrice (G R S N : ℕ) : ℕ :=
  2 * G + 2 * R + kidStmtAtPrice R S N + 2 * kidSlotsInPrice N + 9675

/-- **Child `c`'s statement** (`kidStmtC`), off good tables of at most `N` marks, `c < 2^34`: its
segment's ends (two logarithms), then `kidStmtSeg_cost`: at most `kidStmtPrice G R S N`. -/
theorem kidStmt_cost (D : DiscreteLogTables) (hP : Includes P kidStmtC.costDeps)
    (hG : GLogBound P D G) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx)
    (hts : TableGood ts) (N : ℕ) (hN : N ≤ 2 ^ 34) (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N)
    (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P kidStmtC.costIdx [encodeValue D, rdV, σV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue c] ≤ kidStmtPrice G R S N := by
  rw [kidStmtC.costEq P hP D rd rdV hrd σ σV hσ]
  have h1 := countAtW_cost P hrd hR D (by includes) hG w380 c (by omega)
  have h2 := countAtW_cost P hrd hR D (by includes) hG w380 (c + 1) (by omega)
  have h3 := kidStmtSeg_cost P hrd hR hσ hS (by includes) p53 p56 tx ts htx hts c
    (countAtW D rd w380 c) (countAtW D rd w380 (c + 1)) hc (gLogD_lt D _) (gLogD_lt D _) N hN htxN
    htsN
  limbs_one
  unfold kidStmtPrice
  omega

/-- **Child `c`'s `verify_sub` words** (`subArgsC`), `c < 2^34`: at most `7·S + 2·R + 8989`. -/
theorem subArgs_cost (hP : Includes P subArgsC.costDeps) (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P subArgsC.costIdx [rdV, σV, encodeValue c] ≤ 7 * S + 2 * R + 8989 := by
  rw [subArgsC.costEq P hP rd rdV hrd σ σV hσ]
  have h1 := cellAt_cost P hrd hR (by includes) (σ (.n 383)) (2 * c) (by omega)
  have h2 := cellAt_cost P hrd hR (by includes) (σ (.n 383)) (2 * c + 1) (by omega)
  have h3 := powSqK_cost_lt P (by includes) Parameters.g (24 * c) 39 (by norm_num) (by norm_num) (by omega)
  have h4 := mulK_cost P (by includes) (σ (.n 389)) (Parameters.g ^ (24 * c))
  have := hS (.n 383); have := hS (.n 26); have := hS (.n 27); have := hS (.n 28)
  have := hS (.n 389)
  limbs_one
  omega

section Proof

variable {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
include hwV

/-- A child's price. -/
@[expose] def decKidPrice (G R S W N : ℕ) : ℕ := kidStmtPrice G R S N + W + 8 * S + 26 * R + 84828

/-- **Child `c`** (`decKidC`), off good tables of at most `N` marks, `c < 2^34`: its statement, its
proof's claim (24 reads), its proof (`wV` at its `verify_sub` words, at most `W` there): at most
`decKidPrice G R S W N`. -/
theorem decKid_cost (D : DiscreteLogTables) (hP : Includes P decKidC.costDeps)
    (hG : GLogBound P D G) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx)
    (hts : TableGood ts) (N : ℕ) (hN : N ≤ 2 ^ 34) (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N)
    (c : ℕ) (hc : c < 2 ^ 34) {W : ℕ} (hW : appCost P wVV [encodeValue (subArgsK rd σ c)] ≤ W) :
    machineCost P decKidC.costIdx [encodeValue D, rdV, σV, wVV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue c] ≤ decKidPrice G R S W N := by
  rw [decKidC.costEq P hP D rd rdV hrd σ σV hσ wV wVV hwV]
  have h1 := kidStmt_cost P hrd hR hσ hS D (by includes) hG w380 p53 p56 tx ts htx hts N hN htxN htsN c
    hc
  have h2 := powSqK_cost_lt P (by includes) Parameters.g (24 * c) 39 (by norm_num) (by norm_num) (by omega)
  have h3 := readCellsK_cost P hrd hR (by includes) ((σ (.n 389)).limb 0 * Parameters.g ^ (24 * c)) 24
    (by norm_num)
  have h4 := fixedOfCells_cost P (by includes)
    (readCellsK rd ((σ (.n 389)).limb 0 * Parameters.g ^ (24 * c)) 24)
  have h5 := subArgs_cost P hrd hR hσ hS (by includes) c hc
  have := hS (.n 389)
  limbs_one
  unfold decKidPrice
  omega

end Proof

end Val

end Reader

end

end LeanVM.Cost.Bounds.Guest
