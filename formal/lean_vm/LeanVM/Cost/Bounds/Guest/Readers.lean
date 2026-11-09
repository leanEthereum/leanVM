module

public import LeanVM.Cost.Bounds.Guest.Log
public import LeanVM.Cost.Decoder.Hints

/-!
# Bounds on the guest decoder's prices: the cell readers, the seed and the statement

The readers of `B1.Main` (`Cost/Decoder/Readers.lean`, `Hints.lean`), each bounded in the price `R`
of an application of the memory's reader `rd` and the price `S` of an application of the
valuation `σ`, at positions below `2^40` (the decoder's counts are below `2^34`):

* a cell (`cellAt_cost`, `memAt_cost`: `R + 2969`), `n` cells
  (`readCells_cost`), a DA digest (`daDigestAt_cost`), the cells' digests and claims;
* **the seed** (`decSeed_cost`) and **the statement** (`decStmt_cost`: its declared claims, at most
  `2^34` of each kind, the DA digest, the deferred claim);
* the batching's hints (`aggRounds_cost`, `aggHints_cost`).
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram)

/-! ## Counts and limbs -/

/-- `List.range n` and a `List.map` over it (`range.loop.c75`, `map.c30`), the closure's price at
most `B` on `k < n`, `n ≤ M`: at most `(B + 28)·M + 8`. -/
theorem rangeMap_le {β : Type} [MachineEncoding β]
    (hr : Includes P Auto.List.range.loop.c75.costDeps) (hm : Includes P Auto.List.map.c30.costDeps)
    (f : ℕ → β) (fV : MachineValue) (hf : ∀ a, RunsApp P fV [encodeValue a] (encodeValue (f a)))
    (B n M : ℕ) (hn : n ≤ M) (hM : M < 2 ^ 64) (hB : ∀ k < n, appCost P fV [encodeValue k] ≤ B) :
    machineCost P Auto.List.range.loop.c75.costIdx [encodeValue n, encodeValue ([] : List ℕ)] +
      machineCost P Auto.List.map.c30.costIdx [fV, encodeValue (List.range n)] ≤
        (B + 28) * M + 8 := by
  have h1 := rangeLoop_cost P hr n [] (by omega)
  have h2 := map_cost P hm f fV hf B (List.range n) (fun k hk ↦ hB k (List.mem_range.1 hk))
  rw [List.length_range] at h2
  have := Nat.mul_le_mul_left (B + 13) hn
  nlinarith


/-- A natural below `2^(64·k)` has at most `k` limbs. -/
theorem limbs_le_of_lt {x k : ℕ} (hk : 0 < k) (h : x < 2 ^ (64 * k)) : limbCount x ≤ k := by
  unfold limbCount
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp; omega
  · have := (Nat.log2_lt (by omega)).2 h
    omega

theorem kToNat_lt (a : K) : LeanVM.Protocol.Verifier.kToNat a < 2 ^ 64 := by
  rw [Decoder.kToNat_lane]; exact UInt64.toNat_lt _

/-! ## Cells' digests and claims -/

/-- A cell's number (`cellNatC`): at most `12`. -/
theorem cellNat_cost (hP : Includes P Decoder.cellNatC.costDeps) (x : E) :
    machineCost P Decoder.cellNatC.costIdx [encodeValue x] ≤ 12 := by
  rw [Decoder.cellNatC.costEq P hP]
  have h0 := kToNat_lt (x.limb 0)
  have h1 := kToNat_lt (x.limb 1)
  have : (1 : ℕ) <<< 64 = 2 ^ 64 := by norm_num
  rw [this, limbs_of_lt h1]
  have l1 := limbs_le_of_lt (x := 2 ^ 64) (k := 2) (by norm_num) (by norm_num)
  have l2 := limbs_le_of_lt (x := 2 ^ 64 * LeanVM.Protocol.Verifier.kToNat (x.limb 1)) (k := 2)
    (by norm_num) (by rw [show 64 * 2 = 64 + 64 by rfl, pow_add]; exact Nat.mul_lt_mul_of_pos_left h1 (by norm_num))
  rw [limbs_of_lt h0]
  have l3 := limbs_le_two (x := LeanVM.Protocol.Verifier.kToNat (x.limb 0) +
    2 ^ 64 * LeanVM.Protocol.Verifier.kToNat (x.limb 1)) (by omega)
  omega

/-- The digest of two cells (`digestOfCellsC`): `26`. -/
theorem digestOfCells_cost (hP : Includes P Decoder.digestOfCellsC.costDeps) (a b : E) :
    machineCost P Decoder.digestOfCellsC.costIdx [encodeValue a, encodeValue b] = 26 :=
  Decoder.digestOfCellsC.costEq P hP a b

/-- A deferred claim of its cells (`deferOfCellsC`): at most `820`. -/
theorem deferOfCells_cost (hP : Includes P Decoder.deferOfCellsC.costDeps) (cs : List E) :
    machineCost P Decoder.deferOfCellsC.costIdx [encodeValue cs] ≤ 820 := by
  rw [Decoder.deferOfCellsC.costEq P hP]
  have := take_cost P (by includes) bytecodeVars cs (by norm_num [bytecodeVars])
  have := getD_cost_idx P (by includes) cs bytecodeVars 0 (by norm_num [bytecodeVars])
  simp only [bytecodeVars] at *
  omega

/-- A claim on the bytecode of its cells (`fixedOfCellsC`): at most `820`. -/
theorem fixedOfCells_cost (hP : Includes P Decoder.fixedOfCellsC.costDeps) (cs : List E) :
    machineCost P Decoder.fixedOfCellsC.costIdx [encodeValue cs] ≤ 820 := by
  rw [Decoder.fixedOfCellsC.costEq P hP]
  have := take_cost P (by includes) bytecodeVars cs (by norm_num [bytecodeVars])
  have := getD_cost_idx P (by includes) cs bytecodeVars 0 (by norm_num [bytecodeVars])
  simp only [bytecodeVars] at *
  omega

theorem claimLimbs (c d : E) :
    limbCount (1 <<< 128) + max (limbCount (2 ^ 128 * Sig.cellNat d))
        (limbCount (2 ^ 128) * limbCount (Sig.cellNat d)) +
      max (limbCount (Sig.cellNat c + 2 ^ 128 * Sig.cellNat d))
        (max (limbCount (Sig.cellNat c)) (limbCount (2 ^ 128 * Sig.cellNat d))) ≤ 13 := by
  have hc := Decoder.cellNat_lt c
  have hd := Decoder.cellNat_lt d
  have : (1 : ℕ) <<< 128 = 2 ^ 128 := by norm_num
  rw [this]
  have l1 := limbs_le_of_lt (x := 2 ^ 128) (k := 3) (by norm_num) (by norm_num)
  have l2 := limbs_le_of_lt (x := Sig.cellNat d) (k := 2) (by norm_num) hd
  have l3 := limbs_le_of_lt (x := Sig.cellNat c) (k := 2) (by norm_num) hc
  have l4 := limbs_le_of_lt (x := 2 ^ 128 * Sig.cellNat d) (k := 4) (by norm_num)
    (by rw [show 64 * 4 = 128 + 128 by rfl, pow_add]; exact Nat.mul_lt_mul_of_pos_left hd (by norm_num))
  have l5 := limbs_le_of_lt (x := Sig.cellNat c + 2 ^ 128 * Sig.cellNat d) (k := 4) (by norm_num)
    (by rw [show 64 * 4 = 128 + 128 by rfl, pow_add]; nlinarith)
  have := Nat.mul_le_mul l1 l2
  omega

/-- A leanXMSS claim of its four cells (`xmssClaimOfC`): at most `77`. -/
theorem xmssClaimOf_cost (hP : Includes P Decoder.xmssClaimOfC.costDeps) (a b c d : E) :
    machineCost P Decoder.xmssClaimOfC.costIdx
      [encodeValue a, encodeValue b, encodeValue c, encodeValue d] ≤ 77 := by
  rw [Decoder.xmssClaimOfC.costEq P hP]
  have := claimLimbs c d
  cost_facts [cellNat_cost P]
  omega

/-- A leanSPHINCS claim of its four cells (`sphincsClaimOfC`): at most `77`. -/
theorem sphincsClaimOf_cost (hP : Includes P Decoder.sphincsClaimOfC.costDeps) (a b c d : E) :
    machineCost P Decoder.sphincsClaimOfC.costIdx
      [encodeValue a, encodeValue b, encodeValue c, encodeValue d] ≤ 77 := by
  rw [Decoder.sphincsClaimOfC.costEq P hP]
  have := claimLimbs c d
  cost_facts [cellNat_cost P]
  omega

/-! ## The memory's cells -/

theorem length_readCells (rd : Reader) (p : E) (n : ℕ) : (readCells rd p n).length = n := by
  simp [readCells]

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- **A cell** (`cellAtC`), at a position below `2^40`: at most `R + 2969`. -/
theorem cellAt_cost (hP : Includes P Decoder.cellAtC.costDeps) (p : E) (k : ℕ) (hk : k < 2 ^ 40) :
    machineCost P Decoder.cellAtC.costIdx [rdV, encodeValue p, encodeValue k] ≤ R + 2969 := by
  rw [Decoder.cellAtC.costEq P hP rd rdV hrd]
  have := powSqK_cost_lt P (by includes) g k 40 (by norm_num) (by norm_num) hk
  have := hR (p.limb 0 * addressOfIndex k)
  cases rd (p.limb 0 * addressOfIndex k) <;> dsimp only <;> omega

/-- A cell (`digestMemAtC`), as `cellAt`. -/
theorem memAt_cost (hP : Includes P Decoder.digestMemAtC.costDeps) (p : E)
    (k : ℕ) (hk : k < 2 ^ 40) :
    machineCost P Decoder.digestMemAtC.costIdx
      [rdV, encodeValue p, encodeValue k] ≤ R + 2969 := by
  rw [Decoder.digestMemAtC.costEq P hP rd rdV hrd]
  have := powSqK_cost_lt P (by includes) g k 40 (by norm_num) (by norm_num) hk
  have := hR (p.limb 0 * addressOfIndex k)
  cases rd (p.limb 0 * addressOfIndex k) <;> dsimp only <;> omega

/-- **`n` cells** (`readCellsC`), `n ≤ 2^40`: at most `(R + 3003)·n + 17`. -/
theorem readCells_cost (hP : Includes P Decoder.readCellsC.costDeps) (p : E) (n : ℕ)
    (hn : n ≤ 2 ^ 40) :
    machineCost P Decoder.readCellsC.costIdx [rdV, encodeValue p, encodeValue n] ≤
      (R + 3003) * n + 17 := by
  rw [Decoder.readCellsC.costEq P hP rd rdV hrd]
  have h1 := rangeLoop_cost P (by includes) n [] (by omega)
  have h2 := map_cost P (by includes) (cellAt rd p)
    (.closure Decoder.readCellsC.lam0.costIdx [rdV, encodeValue p])
    (fun k ↦ RunsApp.of_spec (Decoder.readCellsC.lam0.costSpec P (by includes) rd rdV hrd p k))
    (R + 2975) (List.range n) (fun k hk ↦ by
      rw [List.mem_range] at hk
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.readCellsC.lam0.costEq P (by includes) rd rdV hrd, List.length_cons, List.length_cons,
        List.length_nil]
      have := cellAt_cost P hrd hR (by includes) p k (by omega)
      omega)
  rw [List.length_range] at h2
  nlinarith

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- **A DA digest** (`daDigestAtC`), `2·k + 1 < 2^40`: at most `2·S + 2·R + 5995`. -/
theorem daDigestAt_cost (hP : Includes P Decoder.daDigestAtC.costDeps) (k : ℕ)
    (hk : 2 * k + 1 < 2 ^ 40) :
    machineCost P Decoder.daDigestAtC.costIdx [rdV, σV, encodeValue k] ≤ 2 * S + 2 * R + 5995 := by
  rw [Decoder.daDigestAtC.costEq P hP rd rdV hrd σ σV hσ]
  have := hS (.n 385)
  have := cellAt_cost P hrd hR (by includes) (σ (.n 385)) (2 * k) (by omega)
  have := cellAt_cost P hrd hR (by includes) (σ (.n 385)) (2 * k + 1) hk
  rw [digestOfCells_cost P (by includes)]
  limbs_one
  omega

end Val

end Reader

end

end LeanVM.Cost.Bounds.Guest
