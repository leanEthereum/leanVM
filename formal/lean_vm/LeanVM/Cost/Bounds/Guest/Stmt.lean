module

public import LeanVM.Cost.Bounds.Guest.Readers

/-!
# Bounds on the guest decoder's prices: the seed, the statement, the batching's hints

In the price `R` of an application of the memory's reader `rd` and the price `S` of an
application of `main`'s valuation `σ`, the declared claims at most `2^34` of each kind
(`gLogD_lt`):

* **`decSeed_cost`**: `2·S + 45`;
* a slot's claims off its address's low limb (`mulK_cost`, `readCellsK_cost`, `xmssAtK_cost`,
  `sphincsAtK_cost`: `4·R + 12320`), `n` consecutive slots (`xmssRun_cost`, `sphincsRun_cost`:
  `(4·R + 12367)·n + 5`), a DA digest (`daDigestAtP_cost`);
* **`decStmtAt_cost`**: the statement, its counts given, linear in them (`decStmtAtPrice R n0 n3`);
  **`decStmt_cost`** (the logarithm's tables `D` given, `GLogBound P D G`): the two counts at
  most `X` (`2^34` always, `65535` on a valid run), `decStmtPrice G R S X = 7·S + 3·G +
  decStmtAtPrice R X X + 71`;
* `aggRounds_cost`, **`aggHints_cost`**: `47·S + 46·R + 138055`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram) {G : ℕ}


section Readers

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)

omit hrd hR in
/-- `p · x` limb by limb (`mulKC`): `63`. -/
theorem mulK_cost (hP : Includes P Decoder.mulKC.costDeps) (p : E) (x : K) :
    machineCost P Decoder.mulKC.costIdx [encodeValue p, encodeValue x] = 63 :=
  Decoder.mulKC.costEq P hP p x |>.trans (by norm_num)

include hrd hR

/-- `n ≤ 2^40` cells off an address's low limb (`readCellsKC`): `(R + 3003)·n + 27`. -/
theorem readCellsK_cost (hP : Includes P Decoder.readCellsKC.costDeps) (x : K) (n : ℕ)
    (hn : n ≤ 2 ^ 40) :
    machineCost P Decoder.readCellsKC.costIdx [rdV, encodeValue x, encodeValue n] ≤
      (R + 3003) * n + 27 := by
  rw [Decoder.readCellsKC.costEq P hP rd rdV hrd]
  have := readCells_cost P hrd hR (by includes) (E.ofLimbs x 0) n hn
  omega

/-- **A leanXMSS claim off its slot's address** (`xmssAtKC`): `4·R + 12320`. -/
theorem xmssAtK_cost (hP : Includes P Decoder.xmssAtKC.costDeps) (x : K) :
    machineCost P Decoder.xmssAtKC.costIdx [rdV, encodeValue x] ≤ 4 * R + 12320 := by
  rw [Decoder.xmssAtKC.costEq P hP rd rdV hrd]
  have := readCellsK_cost P hrd hR (by includes) x 4 (by norm_num)
  have := getD_cost_idx P (by includes) (Decoder.readCellsK rd x 4) 0 0 (by norm_num)
  have := getD_cost_idx P (by includes) (Decoder.readCellsK rd x 4) 1 0 (by norm_num)
  have := getD_cost_idx P (by includes) (Decoder.readCellsK rd x 4) 2 0 (by norm_num)
  have := getD_cost_idx P (by includes) (Decoder.readCellsK rd x 4) 3 0 (by norm_num)
  cost_facts [xmssClaimOf_cost P]
  omega

/-- **A leanSPHINCS claim off its slot's address** (`sphincsAtKC`): `4·R + 12320`. -/
theorem sphincsAtK_cost (hP : Includes P Decoder.sphincsAtKC.costDeps) (x : K) :
    machineCost P Decoder.sphincsAtKC.costIdx [rdV, encodeValue x] ≤ 4 * R + 12320 := by
  rw [Decoder.sphincsAtKC.costEq P hP rd rdV hrd]
  have := readCellsK_cost P hrd hR (by includes) x 4 (by norm_num)
  have := getD_cost_idx P (by includes) (Decoder.readCellsK rd x 4) 0 0 (by norm_num)
  have := getD_cost_idx P (by includes) (Decoder.readCellsK rd x 4) 1 0 (by norm_num)
  have := getD_cost_idx P (by includes) (Decoder.readCellsK rd x 4) 2 0 (by norm_num)
  have := getD_cost_idx P (by includes) (Decoder.readCellsK rd x 4) 3 0 (by norm_num)
  cost_facts [sphincsClaimOf_cost P]
  omega

/-- **`n` consecutive leanXMSS claims** (`xmssRunC`):
`(4·R + 12367)·n + 5`. -/
theorem xmssRun_cost (hP : Includes P Decoder.xmssRunC.costDeps) (step : K) :
    ∀ (n : ℕ) (x : K), n < 2 ^ 64 →
      machineCost P Decoder.xmssRunC.costIdx [rdV, encodeValue step, encodeValue x,
        encodeValue n] ≤ (4 * R + 12367) * n + 5
  | 0, x, _ => by rw [Decoder.xmssRunC.costEq_zero P hP rd rdV hrd]; omega
  | n + 1, x, h => by
    rw [Decoder.xmssRunC.costEq_succ P hP rd rdV hrd, limbs_of_lt h]
    have := xmssRun_cost hP step n (x * step) (by omega)
    have := xmssAtK_cost P hrd hR (by includes) x
    nlinarith

/-- **`n` consecutive leanSPHINCS claims** (`sphincsRunC`): `(4·R + 12367)·n + 5`. -/
theorem sphincsRun_cost (hP : Includes P Decoder.sphincsRunC.costDeps) (step : K) :
    ∀ (n : ℕ) (x : K), n < 2 ^ 64 →
      machineCost P Decoder.sphincsRunC.costIdx [rdV, encodeValue step, encodeValue x,
        encodeValue n] ≤ (4 * R + 12367) * n + 5
  | 0, x, _ => by rw [Decoder.sphincsRunC.costEq_zero P hP rd rdV hrd]; omega
  | n + 1, x, h => by
    rw [Decoder.sphincsRunC.costEq_succ P hP rd rdV hrd, limbs_of_lt h]
    have := sphincsRun_cost hP step n (x * step) (by omega)
    have := sphincsAtK_cost P hrd hR (by includes) x
    nlinarith

/-- A DA digest off the digests' address (`daDigestAtPC`), `2·k + 1 < 2^40`: `2·R + 5979`. -/
theorem daDigestAtP_cost (hP : Includes P Decoder.daDigestAtPC.costDeps) (p : E) (k : ℕ)
    (hk : 2 * k + 1 < 2 ^ 40) :
    machineCost P Decoder.daDigestAtPC.costIdx [rdV, encodeValue p, encodeValue k] ≤
      2 * R + 5979 := by
  rw [Decoder.daDigestAtPC.costEq P hP rd rdV hrd, digestOfCells_cost P (by includes)]
  have := cellAt_cost P hrd hR (by includes) p (2 * k) (by omega)
  have := cellAt_cost P hrd hR (by includes) p (2 * k + 1) hk
  limbs_one
  omega

/-- The statement's price at `n0`, `n3` declared claims. -/
@[expose] def decStmtAtPrice (R n0 n3 : ℕ) : ℕ :=
  2 * 224 + ((4 * R + 12367) * n0 + 5) + ((4 * R + 12367) * n3 + 5) + (2 * R + 5979) +
    ((R + 3003) * 24 + 17) + 820 + 36

/-- **The statement, its counts given** (`decStmtAtC`): linear in the declared claims,
`decStmtAtPrice R n0 n3`, the DA digest's slot `pick < 2^39`. -/
theorem decStmtAt_cost (hP : Includes P Decoder.decStmtAtC.costDeps) (p53 p56 p334 p402 : E)
    (n0 n3 pick : ℕ) (h0 : n0 < 2 ^ 64) (h3 : n3 < 2 ^ 64) (hpick : pick < 2 ^ 39) :
    machineCost P Decoder.decStmtAtC.costIdx [rdV, encodeValue p53, encodeValue p56,
      encodeValue p334, encodeValue p402, encodeValue n0, encodeValue n3, encodeValue pick] ≤
        decStmtAtPrice R n0 n3 := by
  rw [Decoder.decStmtAtC.costEq P hP rd rdV hrd]
  have := powSqK_cost_lt P (by includes) LeanVM.Parameters.g 4 3 (by norm_num) (by norm_num) (by norm_num)
  have := xmssRun_cost P hrd hR (by includes) (LeanVM.Parameters.g ^ 4) n0 (p53.limb 0) h0
  have := sphincsRun_cost P hrd hR (by includes) (LeanVM.Parameters.g ^ 4) n3 (p56.limb 0) h3
  have := daDigestAtP_cost P hrd hR (by includes) p334 pick (by omega)
  have := readCells_cost P hrd hR (by includes) p402 24 (by norm_num)
  have := deferOfCells_cost P (by includes) (readCells rd p402 24)
  unfold decStmtAtPrice
  omega

end Readers

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- **The seed** (`decSeedC`): `2·S + 45` at most. -/
theorem decSeed_cost (hP : Includes P Decoder.decSeedC.costDeps) :
    machineCost P Decoder.decSeedC.costIdx [σV] ≤ 2 * S + 45 := by
  rw [Decoder.decSeedC.costEq P hP σ σV hσ, digestOfCells_cost P (by includes)]
  have := hS (.n 26)
  have := hS (.n 27)
  omega

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- The statement's price: `7·S + 3·G` and the two counts at their bound `X`. -/
@[expose] def decStmtPrice (G R S X : ℕ) : ℕ := 7 * S + 3 * G + decStmtAtPrice R X X + 71

/-- **The statement** (`decStmtC`), the logarithm's tables `D` given: the counts (three
logarithms, the leanXMSS and leanSPHINCS counts at most `X`) and `decStmtAtC`: at most
`decStmtPrice G R S X = 8·R·X + 24734·X + 3·G + 7·S + …`. -/
theorem decStmt_cost (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.decStmtC.costDeps) (hG : GLogBound P D G) (X : ℕ)
    (hX0 : Decoder.gLogD D (σ (.n 0)) ≤ X) (hX3 : Decoder.gLogD D (σ (.n 3)) ≤ X) :
    machineCost P Decoder.decStmtC.costIdx [encodeValue D, σV, rdV] ≤ decStmtPrice G R S X := by
  rw [Decoder.decStmtC.costEq P hP D σ σV hσ rd rdV hrd]
  have := hG (σ (.n 0)); have := hG (σ (.n 3)); have := hG (σ (.n 405))
  have n0 := gLogD_lt D (σ (.n 0))
  have n3 := gLogD_lt D (σ (.n 3))
  have n405 := gLogD_lt D (σ (.n 405))
  have h := decStmtAt_cost P hrd hR (by includes) (σ (.n 31)) (σ (.n 34)) (σ (.n 364)) (σ (.n 416))
    (Decoder.gLogD D (σ (.n 0))) (Decoder.gLogD D (σ (.n 3))) (Decoder.gLogD D (σ (.n 405)))
    (by omega) (by omega) (by omega)
  have : decStmtAtPrice R (Decoder.gLogD D (σ (.n 0))) (Decoder.gLogD D (σ (.n 3))) ≤
      decStmtAtPrice R X X := by
    unfold decStmtAtPrice
    have := Nat.mul_le_mul_left (4 * R + 12367) hX0
    have := Nat.mul_le_mul_left (4 * R + 12367) hX3
    omega
  cost_facts [hS]
  unfold decStmtPrice
  omega

/-- The sumcheck's rounds the batching hints (`aggRoundsC`): at most `46·S + 46·R + 138500`. -/
theorem aggRounds_cost (hP : Includes P Decoder.aggRoundsC.costDeps) :
    machineCost P Decoder.aggRoundsC.costIdx [rdV, σV] ≤ 46 * S + 46 * R + 138500 := by
  rw [Decoder.aggRoundsC.costEq P hP rd rdV hrd σ σV hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.aggRoundsC.lam0.costIdx [rdV, σV])
    (fun k ↦ RunsApp.of_spec (Decoder.aggRoundsC.lam0.costSpec P (by includes) rd rdV hrd σ σV hσ k))
    (2 * S + 2 * R + 5993) 23 23 le_rfl (by norm_num) (fun k hk ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.aggRoundsC.lam0.costEq P (by includes) rd rdV hrd σ σV hσ, List.length_cons,
        List.length_cons, List.length_nil]
      have := memAt_cost P hrd hR (by includes) (σ (.n 6)) (1 + 2 * k) (by omega)
      have := memAt_cost P hrd hR (by includes) (σ (.n 6)) (2 + 2 * k) (by omega)
      have := hS (.n 6)
      limbs_one
      omega)
  omega

/-- **The batching's hints** (`aggHintsC`): the nonce, the rounds, the bytecode's value: at most
`48·S + 47·R + 141600`. -/
theorem aggHints_cost (hP : Includes P Decoder.aggHintsC.costDeps) :
    machineCost P Decoder.aggHintsC.costIdx [rdV, σV] ≤ 48 * S + 47 * R + 141600 := by
  rw [Decoder.aggHintsC.costEq P hP rd rdV hrd σ σV hσ]
  have := aggRounds_cost P hσ hS hrd hR (by includes)
  have := memAt_cost P hrd hR (by includes) (σ (.n 6)) 0 (by norm_num)
  have := hS (.n 6); have := hS (.n 7)
  omega

end Reader

end Val

end

end LeanVM.Cost.Bounds.Guest
