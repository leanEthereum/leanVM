module

public import LeanVM.Cost.AS.Bounds.Newton
import all LeanVM.Protocol.Whir.Sound.DescentT
import all LeanVM.Protocol.Whir.Sound.LowMsgC
import all LeanVM.Protocol.Whir.Sound.StackA
import all Statement.Prover.Ntt
import all Statement.LeanVmVerifier
import all LeanVM.Protocol.Whir.Sound.State
import all LeanVM.Protocol.Whir.Sound.DescentC
import all LeanVM.Protocol.Whir.Params.Check
import all LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDeployedTable
import all LeanVM.Protocol.Extraction.Extractor
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.AS.Lite
import LeanVM.Protocol.Extraction.Merkle

/-!
# Bounds: the step up a level, level 0's stack and the roots' words

* `hatAt_cost`: `Ŵ_c(x_n)` from the table of `Ŵ_c` on the basis, which the compiled `hatAt`
  rebuilds on every call, at most `hatPrice`; `novelAtH_cost` (`64·hatPrice + 3800`),
  **`polyOfAtH_cost`** (`polyPrice L` for at most `L` coefficients);
* `novelInvE_cost`: the inverse transform over `E`; **`msgA_cost`** (`msgPrice κ κ' m`);
* `nttStageAt_cost`, `nttStage_cost`, `nttGo_cost`, `ntt_cost`: the additive NTT of `2^κ` entries
  on `2^(κ+R)` positions, `κ·(110·2^(κ+R) + 100) + 28·2^(κ+R) + 35`; `stageTwiddles_cost`;
* **`upAtA_cost`** (`upPrice κ κ' m R L`), **`stackA_cost`**;
* `lanesOf_cost`, `laneRow_cost`, `laneRows_cost`, `leavesInC_cost` and `leavesAt_cost`
  (`leavesPrice`), `lvC_cost` (the levels' shapes from the fold table, `lvC_small`),
  **`wordArrOf_cost`** (`wordPrice`), **`wordsGoWorker_cost`** (`wordsPrice`).
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Prover

public section

variable (P : MachineProgram)

/-! ## The table of the normalized subspace polynomials -/

theorem vanRow_cost (hP : Includes P Auto.LeanVM.Prover.vanRow.c309.costDeps) :
    ∀ c, c < 2 ^ 64 →
      machineCost P Auto.LeanVM.Prover.vanRow.c309.costIdx [encodeValue c] ≤ 5020 * c + 1422
  | 0, _ => by
    rw [Auto.LeanVM.Prover.vanRow.c309.costEq_zero P hP, ofFnFrom_length]
    have := ofFnFrom_cost P (by includes) (n := 64) (by norm_num) _
      (.closure Auto.LeanVM.Prover.vanRow.c309.lam0.costIdx [])
      (fun i ↦ RunsApp.of_spec (Auto.LeanVM.Prover.vanRow.c309.lam0.costSpec P
        (by includes) i)) 5
      (fun i ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Prover.vanRow.c309.lam0.costEq P (by includes),
          limbs_shift i.isLt, limbs_two_pow i.isLt, limbs_of_lt (by omega : (i : ℕ) < 2 ^ 64)]
        rfl) 0 (Nat.zero_le _)
    omega
  | c + 1, hc => by
    rw [Auto.LeanVM.Prover.vanRow.c309.costEq_succ P hP, limbs_of_lt hc, Prover.Enc.size_vanRow]
    have ih := vanRow_cost hP c (by omega)
    have hm := map_cost P (by includes) _
      (.closure Auto.LeanVM.Prover.vanRow.c309.lam1.costIdx
        [encodeValue ((vanRow c).getD c 0), encodeValue (vanRow c)])
      (fun v ↦ RunsApp.of_spec (Auto.LeanVM.Prover.vanRow.c309.lam1.costSpec P (by includes) _ _ v))
      61 (vanRow c).toList
      (fun v _ ↦ by
        rw [appCost_fn]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [Auto.LeanVM.Prover.vanRow.c309.lam1.costEq P (by includes)])
    simp only [List.length_map, Array.length_toList, Prover.Enc.size_vanRow] at hm ⊢
    rw [show Auto.LeanVM.Prover.vanRow.c309.lam1.costIdx = 311 from rfl] at hm
    omega

theorem hatRow_cost (hP : Includes P Auto.LeanVM.Prover.hatRow.c308.costDeps) (c : ℕ) (hc : c < 64) :
    machineCost P Auto.LeanVM.Prover.hatRow.c308.costIdx [encodeValue c] ≤ 323598 := by
  rw [Auto.LeanVM.Prover.hatRow.c308.costEq P hP, Prover.Enc.size_vanRow]
  have h1 := vanRow_cost P (by includes) c (by omega)
  have h2 := invK_cost P (by includes) ((vanRow c).getD c 0)
  have hm := map_cost P (by includes) _
    (.closure Auto.LeanVM.Prover.hatRow.c308.lam0.costIdx
      [encodeValue ((vanRow c).getD c 0)⁻¹, encodeValue (vanRow c)])
    (fun v ↦ RunsApp.of_spec (Auto.LeanVM.Prover.hatRow.c308.lam0.costSpec P (by includes) _ _ v))
    31 (vanRow c).toList
    (fun v _ ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Prover.hatRow.c308.lam0.costEq P (by includes)])
  simp only [List.length_map, Array.length_toList, Prover.Enc.size_vanRow] at hm ⊢
  omega

theorem hatTable_cost (hP : Includes P Auto.LeanVM.Prover.hatTable.c306.costDeps) :
    machineCost P Auto.LeanVM.Prover.hatTable.c306.costIdx [] ≤ 20711498 := by
  rw [Auto.LeanVM.Prover.hatTable.c306.costEq P hP, ofFnFrom_length]
  have := ofFnFrom_cost P (by includes) (n := 64) (by norm_num) _
    (.closure Auto.LeanVM.Prover.hatTable.c306.lam0.costIdx [])
    (fun c ↦ RunsApp.of_spec (Auto.LeanVM.Prover.hatTable.c306.lam0.costSpec P (by includes) c))
    323600
    (fun c ↦ by
      rw [appCost_fn, List.nil_append, Auto.LeanVM.Prover.hatTable.c306.lam0.costEq P (by includes)]
      have := hatRow_cost P (by includes) c c.isLt
      simp only [List.length_nil]
      omega) 0 (Nat.zero_le _)
  omega

/-- The price bound of one `hatAt`: the table rebuilt, then `64` bits read. -/
@[expose] def hatPrice : ℕ := 20714600

/-- **`Ŵ_c(x_n)`** (`hatAt.c305`): the table of `Ŵ_c` on the basis, rebuilt on every call, then the
`64` bits of `n`. -/
theorem hatAt_cost (hP : Includes P Auto.LeanVM.Prover.hatAt.c305.costDeps) (c n : ℕ)
    (hn : n < 2 ^ 64) :
    machineCost P Auto.LeanVM.Prover.hatAt.c305.costIdx [encodeValue c, encodeValue n] ≤ hatPrice := by
  rw [Auto.LeanVM.Prover.hatAt.c305.costEq P hP]
  have h1 := hatTable_cost P (by includes)
  have h2 := rangeLoop_cost P (by includes) 64 [] (by norm_num)
  have h3 := listFoldl_le P (by includes) _
    (.closure Auto.LeanVM.Prover.hatAt.c305.lam0.costIdx [encodeValue n, encodeValue (hatTable.getD c #[])])
    (fun acc m ↦ RunsApp.of_spec (Auto.LeanVM.Prover.hatAt.c305.lam0.costSpec P (by includes) n _ acc m))
    21 (fun _ ↦ True) (List.range 64) 0 trivial
    (fun acc _ m hm ↦ ⟨trivial, by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Prover.hatAt.c305.lam0.costEq P (by includes)]
      have := testBit_cost P (by includes) n m hn (by have := List.mem_range.1 hm; omega)
      split_ifs <;> omega⟩)
  simp only [List.length_range] at h3
  unfold hatPrice
  omega

/-! ## The novel basis and a polynomial at a point -/

/-- **`X_c(x_x)` from the table** (`novelAtHC`): `64` bits of `c`, a `hatAt` for each set bit. -/
theorem novelAtH_cost (hP : Includes P novelAtHC.costDeps) (c x : ℕ) (hc : c < 2 ^ 64)
    (hx : x < 2 ^ 64) :
    machineCost P novelAtHC.costIdx [encodeValue c, encodeValue x] ≤ 64 * hatPrice + 3800 := by
  rw [novelAtHC.costEq P hP]
  have := prodRange_cost P (by includes) _ (.closure novelAtHC.lam0.costIdx [encodeValue c, encodeValue x])
    (fun v ↦ RunsApp.of_spec (novelAtHC.lam0.costSpec P (by includes) c x v)) (hatPrice + 18)
    (fun v hv ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [novelAtHC.lam0.costEq P (by includes)]
      have h1 := testBit_cost P (by includes) c v hc hv
      have h2 := hatAt_cost P (by includes) v x hx
      split_ifs <;> omega) 64 (by norm_num)
  omega

/-- The price bound of `polyOfAtH` on at most `L` coefficients. -/
@[expose] def polyPrice (L : ℕ) : ℕ := (64 * hatPrice + 15 * L + 4100) * L + 40

/-- **A polynomial of at most `L` novel coefficients at `x_x`** (`polyOfAtHC`). -/
theorem polyOfAtH_cost (hP : Includes P polyOfAtHC.costDeps) (cs : List E) (x L : ℕ)
    (hL : cs.length ≤ L) (hL' : L < 2 ^ 32) (hx : x < 2 ^ 64) :
    machineCost P polyOfAtHC.costIdx [encodeValue cs, encodeValue x] ≤ polyPrice L := by
  rw [polyOfAtHC.costEq P hP]
  have h1 := length_cost P (by includes) cs (by omega)
  have h2 := rangeLoop_cost P (by includes) cs.length [] (by omega)
  have h3 := map_cost P (by includes) _ (.closure polyOfAtHC.lam0.costIdx [encodeValue cs, encodeValue x])
    (fun c ↦ RunsApp.of_spec (polyOfAtHC.lam0.costSpec P (by includes) cs x c))
    (15 * L + 64 * hatPrice + 3999) (List.range cs.length)
    (fun c hc ↦ by
      have hc' := List.mem_range.1 hc
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [polyOfAtHC.lam0.costEq P (by includes)]
      have g := getD_cost P (by includes) cs c 0 (by omega)
      have n := novelAtH_cost P (by includes) c x (by omega) hx
      omega)
  have h4 := foldr_cost P (by includes) (· + ·) (.closure Auto.List.sum.c315.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (Auto.List.sum.c315.lam0.costSpec P (by includes) a b)) 13 0
    ((List.range cs.length).map fun c ↦ cs.getD c 0 * ofK (novelAtH c x))
    (fun a _ b ↦ by
      rw [appCost_fn, List.nil_append, Auto.List.sum.c315.lam0.costEq P (by includes)]
      rfl)
  rw [Auto.List.sum.c315.costEq P (by includes)]
  simp only [List.length_map, List.length_range] at h3 h4
  have h5 : (15 * L + 64 * hatPrice + 3999 + 13) * cs.length ≤ (15 * L + 64 * hatPrice + 4012) * L :=
    Nat.mul_le_mul_left _ hL
  unfold polyPrice
  nlinarith

/-! ## The inverse transform over `E` and the message -/

/-- **The inverse transform over `E`** (`novelInvE.c320`): both limbs' inverse transforms. -/
theorem novelInvE_cost (hP : Includes P Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.costDeps)
    (κ : ℕ) (hκ : κ ≤ 62) (y : Array E) :
    machineCost P Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.costIdx [encodeValue κ, encodeValue y] ≤
      38 * y.size + κ * (348 * 2 ^ κ + 5872) + 31 * 2 ^ κ + 100 := by
  rw [Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.costEq P hP, ofFnFrom_length,
    limbs_shift (by omega : κ < 64), limbs_of_lt (by omega : κ < 2 ^ 64)]
  have hm0 := map_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.lam0.costSpec P
      (by includes) x)) 2 y.toList
    (fun x _ ↦ by
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.lam0.costEq P (by includes)]
      rfl)
  have hm1 := map_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.lam1.costIdx [])
    (fun x ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.lam1.costSpec P
      (by includes) x)) 2 y.toList
    (fun x _ ↦ by
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.lam1.costEq P (by includes)]
      rfl)
  have hr := rangeLoop_cost P (by includes) κ [] (by omega)
  have hi0 := novelInv_cost P (by includes) κ hκ (limbArr 0 y)
  have hi1 := novelInv_cost P (by includes) κ hκ (limbArr 1 y)
  have hN : 2 ^ κ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hof := ofFnFrom_cost P (by includes) hN _
    (.closure Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.lam2.costIdx
      [encodeValue κ, encodeValue (LeanVM.Extraction.novelInv κ (limbArr 0 y)),
        encodeValue (LeanVM.Extraction.novelInv κ (limbArr 1 y))])
    (fun j ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.lam2.costSpec P
      (by includes) κ _ _ j)) 14
    (fun j ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Protocol.Whir.Sound.novelInvE.c320.lam2.costEq P (by includes)]) 0
    (Nat.zero_le _)
  simp only [List.length_map, Array.length_toList, Nat.sub_zero, max_self] at hm0 hm1 hof ⊢
  have e : κ * (348 * 2 ^ κ + 5872) = 2 * (κ * (174 * 2 ^ κ + 2906)) + 60 * κ := by ring
  omega

/-- The price bound of the message of the step up. -/
@[expose] def msgPrice (κ κ' m : ℕ) : ℕ :=
  (κ' * (348 * 2 ^ κ' + 5872) + 102 * 2 ^ κ' + 142) * 2 ^ m + 40 * 2 ^ κ + 40

theorem size_msgA (κ κ' m : ℕ) (VA' : AV) : (msgA κ κ' m VA').size = 2 ^ κ := by
  simp [msgA]

/-- **The message of the step up** (`msgAC`): `2^m` inverse transforms over `2^κ'`, then `2^κ`
entries. -/
theorem msgA_cost (hP : Includes P msgAC.costDeps) (κ κ' m : ℕ) (VA' : AV) (hκ : κ ≤ 62)
    (hκ' : κ' ≤ 62) (hm : m ≤ 62) :
    machineCost P msgAC.costIdx [encodeValue κ, encodeValue κ', encodeValue m, encodeValue VA'] ≤
      msgPrice κ κ' m := by
  rw [msgAC.costEq P hP, ofFnFrom_length, ofFnFrom_length, limbs_shift (by omega : m < 64),
    limbs_of_lt (by omega : m < 2 ^ 64), limbs_shift (by omega : κ < 64),
    limbs_of_lt (by omega : κ < 2 ^ 64)]
  have hm2 : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hκ2 : 2 ^ κ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hκ'2 : 2 ^ κ' < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 := ofFnFrom_cost P (by includes) hm2 _
    (.closure msgAC.lam0.costIdx [encodeValue κ', encodeValue m, encodeValue VA'])
    (fun u ↦ RunsApp.of_spec (msgAC.lam0.costSpec P (by includes) κ' m VA' u))
    (κ' * (348 * 2 ^ κ' + 5872) + 102 * 2 ^ κ' + 125)
    (fun u ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [msgAC.lam0.costEq P (by includes), ofFnFrom_length, limbs_shift (by omega : κ' < 64),
        limbs_of_lt (by omega : κ' < 2 ^ 64)]
      have a := ofFnFrom_cost P (by includes) hκ'2 _
        (.closure msgAC.lam0.lam0.costIdx [encodeValue κ', encodeValue m, encodeValue VA', encodeValue u])
        (fun v ↦ RunsApp.of_spec (msgAC.lam0.lam0.costSpec P (by includes) κ' m VA' u v)) 16
        (fun v ↦ by
          rw [appCost_fn]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [msgAC.lam0.lam0.costEq P (by includes)]) 0 (Nat.zero_le _)
      have b := novelInvE_cost P (by includes) κ' hκ'
        (Array.ofFn fun v : Fin (2 ^ κ') ↦ (VA'.getD v #[]).getD u 0)
      rw [Array.size_ofFn] at b
      simp only [Nat.sub_zero, max_self] at a ⊢
      omega) 0 (Nat.zero_le _)
  have h2 := ofFnFrom_cost P (by includes) hκ2 _
    (.closure msgAC.lam1.costIdx [encodeValue κ, encodeValue m, encodeValue
      (Array.ofFn fun u : Fin (2 ^ m) ↦ novelInvE κ' (Array.ofFn fun v : Fin (2 ^ κ') ↦
        (VA'.getD v #[]).getD u 0))])
    (fun j ↦ RunsApp.of_spec (msgAC.lam1.costSpec P (by includes) κ m _ j)) 23
    (fun j ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [msgAC.lam1.costEq P (by includes), limbs_shift (by omega : m < 64),
        limbs_of_lt (by omega : m < 2 ^ 64), limbs_two_pow (by omega : m < 64),
        limbs_of_lt (by have := j.isLt; omega : (j : ℕ) < 2 ^ 64)]
      simp) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero, max_self] at h1 h2 ⊢
  have e : (κ' * (348 * 2 ^ κ' + 5872) + 102 * 2 ^ κ' + 125 + 16) * 2 ^ m + 2 ^ m =
      (κ' * (348 * 2 ^ κ' + 5872) + 102 * 2 ^ κ' + 142) * 2 ^ m := by ring
  unfold msgPrice
  omega

/-! ## The additive NTT -/

/-- **A stage's butterflies** (`nttStageAt.c333`) on `2^N` positions, `pi1 = 2·pi ≤ 2^N`. -/
theorem nttStageAt_cost (hP : Includes P Auto.LeanVM.Prover.nttStage.nttStageAt.c333.costDeps)
    (N pi pi1 : ℕ) (tw a : Array K) (hN : 1 ≤ N) (hN' : N ≤ 62) (hpi : 0 < pi) (hpi1 : pi1 = 2 * pi)
    (hpiN : pi1 ≤ 2 ^ N) :
    machineCost P Auto.LeanVM.Prover.nttStage.nttStageAt.c333.costIdx [encodeValue N, encodeValue pi,
      encodeValue pi1, encodeValue tw, encodeValue a] ≤ 110 * 2 ^ N + 60 := by
  rw [Auto.LeanVM.Prover.nttStage.nttStageAt.c333.costEq P hP, ofFnFrom_length, ofFnFrom_length,
    limbs_of_lt (by omega : N < 2 ^ 64), limbs_shift (by omega : N - 1 < 64),
    limbs_of_lt (by omega : N - 1 < 2 ^ 64), limbs_shift (by omega : N < 64)]
  have hNp : 2 ^ N ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hN'
  have hsplit : 2 ^ N = 2 * 2 ^ (N - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h1 := ofFnFrom_cost P (by includes) (n := 2 ^ (N - 1)) (by omega) _
    (.closure Auto.LeanVM.Prover.nttStage.nttStageAt.c333.lam0.costIdx [encodeValue N, encodeValue pi,
      encodeValue pi1, encodeValue tw, encodeValue a])
    (fun q ↦ RunsApp.of_spec (Auto.LeanVM.Prover.nttStage.nttStageAt.c333.lam0.costSpec P
      (by includes) N pi pi1 tw a q)) 52
    (fun q ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Prover.nttStage.nttStageAt.c333.lam0.costEq P (by includes)]
      have hq := q.isLt
      have d1 : (q : ℕ) / pi * pi ≤ q := Nat.div_mul_le_self _ _
      have d2 : (q : ℕ) / pi * pi1 = 2 * ((q : ℕ) / pi * pi) := by rw [hpi1]; ring
      have d3 : (q : ℕ) % pi < pi := Nat.mod_lt _ hpi
      have d4 : (q : ℕ) / pi ≤ q := Nat.div_le_self _ _
      rw [limbs_of_lt (by omega : (q : ℕ) < 2 ^ 64), limbs_of_lt (by omega : pi < 2 ^ 64),
        limbs_of_lt (by omega : (q : ℕ) / pi * pi1 < 2 ^ 64),
        limbs_of_lt (by omega : (q : ℕ) / pi < 2 ^ 64), limbs_of_lt (by omega : pi1 < 2 ^ 64),
        limbs_of_lt (by omega : (q : ℕ) / pi * pi1 + pi < 2 ^ 64),
        limbs_of_lt (by omega : (q : ℕ) / pi * pi1 + pi + (q : ℕ) % pi < 2 ^ 64),
        limbs_of_lt (by omega : (q : ℕ) % pi < 2 ^ 64)]
      simp) 0 (Nat.zero_le _)
  have h2 := ofFnFrom_cost P (by includes) (n := 2 ^ N) (by omega) _
    (.closure Auto.LeanVM.Prover.nttStage.nttStageAt.c333.lam1.costIdx [encodeValue N, encodeValue pi,
      encodeValue pi1, encodeValue a, encodeValue (Array.ofFn fun q : Fin (2 ^ (N - 1)) ↦
        tw.getD ((q : ℕ) / pi) 0 * a.getD ((q : ℕ) / pi * pi1 + pi + (q : ℕ) % pi) 0)])
    (fun p ↦ RunsApp.of_spec (Auto.LeanVM.Prover.nttStage.nttStageAt.c333.lam1.costSpec P
      (by includes) N pi pi1 a _ p)) 49
    (fun p ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Prover.nttStage.nttStageAt.c333.lam1.costEq P (by includes)]
      have hp := p.isLt
      have hpi1' : 0 < pi1 := by omega
      have d1 : (p : ℕ) / pi1 * pi1 ≤ p := Nat.div_mul_le_self _ _
      have d2 : (p : ℕ) / pi1 * pi1 = 2 * ((p : ℕ) / pi1 * pi) := by rw [hpi1]; ring
      have d3 : (p : ℕ) % pi1 < pi1 := Nat.mod_lt _ hpi1'
      have d4 : (p : ℕ) % pi1 % pi < pi := Nat.mod_lt _ hpi
      have d5 : (p : ℕ) / pi1 ≤ p := Nat.div_le_self _ _
      rw [limbs_of_lt (by omega : (p : ℕ) < 2 ^ 64), limbs_of_lt (by omega : pi1 < 2 ^ 64),
        limbs_of_lt (by omega : (p : ℕ) % pi1 < 2 ^ 64), limbs_of_lt (by omega : pi < 2 ^ 64),
        limbs_of_lt (by omega : (p : ℕ) / pi1 * pi1 < 2 ^ 64),
        limbs_of_lt (by omega : (p : ℕ) / pi1 < 2 ^ 64),
        limbs_of_lt (by omega : (p : ℕ) / pi1 * pi1 + (p : ℕ) % pi1 % pi < 2 ^ 64),
        limbs_of_lt (by omega : (p : ℕ) % pi1 % pi < 2 ^ 64),
        limbs_of_lt (by omega : (p : ℕ) / pi1 * pi < 2 ^ 64),
        limbs_of_lt (by omega : (p : ℕ) / pi1 * pi + (p : ℕ) % pi1 % pi < 2 ^ 64),
        limbs_of_lt (by omega : (p : ℕ) / pi1 * pi1 + (p : ℕ) % pi1 % pi + pi < 2 ^ 64)]
      split_ifs <;> simp) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero, max_self] at h1 h2 ⊢
  omega

/-- **A stage of the additive NTT** (`nttStage.c332`). -/
theorem nttStage_cost (hP : Includes P Auto.LeanVM.Prover.nttStage.c332.costDeps) (N i : ℕ) (tw a : Array K)
    (hi : i < N) (hN : N ≤ 62) :
    machineCost P Auto.LeanVM.Prover.nttStage.c332.costIdx [encodeValue N, encodeValue i, encodeValue tw,
      encodeValue a] ≤ 110 * 2 ^ N + 72 := by
  rw [Auto.LeanVM.Prover.nttStage.c332.costEq P hP, limbs_shift (by omega : i < 64),
    limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : i + 1 < 2 ^ 64),
    limbs_shift (by omega : i + 1 < 64)]
  have := nttStageAt_cost P (by includes) N (2 ^ i) (2 ^ (i + 1)) tw a (by omega) hN (by positivity)
    (by ring) (Nat.pow_le_pow_right (by norm_num) hi)
  simp only [max_self]
  omega

/-- **The stages of the additive NTT** (`ntt.go.c331`), `a` stages on `2^(κ+R)` positions. -/
theorem nttGo_cost (hP : Includes P Auto.LeanVM.Prover.ntt.go.c331.costDeps) (tws : Array (Array K))
    (κ R : ℕ) (hN : κ + R ≤ 62) : ∀ a, a ≤ κ + R → ∀ arr : Array K,
      machineCost P Auto.LeanVM.Prover.ntt.go.c331.costIdx [encodeValue tws, encodeValue κ, encodeValue R,
        encodeValue a, encodeValue arr] ≤ a * (110 * 2 ^ (κ + R) + 100) + 5
  | 0, _, arr => by rw [Auto.LeanVM.Prover.ntt.go.c331.costEq_zero P hP]; omega
  | n + 1, hn, arr => by
    rw [Auto.LeanVM.Prover.ntt.go.c331.costEq_succ P hP, limbs_of_lt (by omega : n + 1 < 2 ^ 64),
      limbs_of_lt (by omega : κ + R < 2 ^ 64), limbs_of_lt (by omega : κ < 2 ^ 64),
      limbs_of_lt (by omega : R < 2 ^ 64)]
    have h1 := nttStage_cost P (by includes) (κ + R) n (tws.getD n #[]) arr (by omega) hN
    have h2 := nttGo_cost hP tws κ R hN n (by omega) (nttStage (κ + R) n (tws.getD n #[]) arr)
    have e : (n + 1) * (110 * 2 ^ (κ + R) + 100) = n * (110 * 2 ^ (κ + R) + 100) +
        (110 * 2 ^ (κ + R) + 100) := by ring
    simp only [max_self]
    omega

/-- **The additive NTT** (`ntt.c330`) of `2^κ` entries on `2^(κ+R)` positions. -/
theorem ntt_cost (hP : Includes P Auto.LeanVM.Prover.ntt.c330.costDeps) (tws : Array (Array K))
    (κ R : ℕ) (msg : Array K) (hN : κ + R ≤ 62) :
    machineCost P Auto.LeanVM.Prover.ntt.c330.costIdx [encodeValue tws, encodeValue κ, encodeValue R,
      encodeValue msg] ≤ κ * (110 * 2 ^ (κ + R) + 100) + 28 * 2 ^ (κ + R) + 35 := by
  rw [Auto.LeanVM.Prover.ntt.c330.costEq P hP, ofFnFrom_length, limbs_of_lt (by omega : κ + R < 2 ^ 64),
    limbs_of_lt (by omega : κ < 2 ^ 64), limbs_of_lt (by omega : R < 2 ^ 64),
    limbs_shift (by omega : κ + R < 64)]
  have hN2 : 2 ^ (κ + R) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 := ofFnFrom_cost P (by includes) hN2 _
    (.closure Auto.LeanVM.Prover.ntt.c330.lam0.costIdx [encodeValue κ, encodeValue R, encodeValue msg])
    (fun p ↦ RunsApp.of_spec (Auto.LeanVM.Prover.ntt.c330.lam0.costSpec P (by includes) κ R msg p)) 11
    (fun p ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Prover.ntt.c330.lam0.costEq P (by includes), limbs_shift (by omega : κ < 64),
        limbs_of_lt (by omega : κ < 2 ^ 64), limbs_two_pow (by omega : κ < 64),
        limbs_of_lt (by have := p.isLt; omega : (p : ℕ) < 2 ^ 64)]
      simp) 0 (Nat.zero_le _)
  have h2 := nttGo_cost P (by includes) tws κ R hN κ (by omega)
    (Array.ofFn fun p : Fin (2 ^ (κ + R)) ↦ msg.getD (p % 2 ^ κ) 0)
  simp only [Nat.sub_zero, max_self] at h1 ⊢
  omega

/-- **A stage's twiddles** (`stageTwiddles.c328`): one `hatAt` per block. -/
theorem stageTwiddles_cost (hP : Includes P Auto.LeanVM.Prover.stageTwiddles.c328.costDeps) (N i : ℕ)
    (hi : i < N) (hN : N ≤ 62) :
    machineCost P Auto.LeanVM.Prover.stageTwiddles.c328.costIdx [encodeValue N, encodeValue i] ≤
      (hatPrice + 28) * 2 ^ N + 20 := by
  rw [Auto.LeanVM.Prover.stageTwiddles.c328.costEq P hP, ofFnFrom_length,
    limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_of_lt (by omega : i < 2 ^ 64),
    limbs_of_lt (by omega : N < 2 ^ 64), limbs_shift (by omega : N - (i + 1) < 64),
    limbs_of_lt (by omega : N - (i + 1) < 2 ^ 64)]
  have hNp : 2 ^ N ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hN
  have hle : 2 ^ (N - (i + 1)) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsp : 2 ^ (N - (i + 1)) * 2 ^ (i + 1) = 2 ^ N := by rw [← pow_add]; congr 1; omega
  have h1 := ofFnFrom_cost P (by includes) (n := 2 ^ (N - (i + 1))) (by omega) _
    (.closure Auto.LeanVM.Prover.stageTwiddles.c328.lam0.costIdx [encodeValue N, encodeValue i])
    (fun b ↦ RunsApp.of_spec (Auto.LeanVM.Prover.stageTwiddles.c328.lam0.costSpec P (by includes) N i b))
    (hatPrice + 11)
    (fun b ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Prover.stageTwiddles.c328.lam0.costEq P (by includes)]
      have hb : (b : ℕ) * 2 ^ (i + 1) < 2 ^ N := by
        rw [← hsp]; exact Nat.mul_lt_mul_of_pos_right b.isLt (by positivity)
      have := hatAt_cost P (by includes) i ((b : ℕ) * 2 ^ (i + 1)) (by omega)
      rw [limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_of_lt (by omega : i < 2 ^ 64),
        limbs_shift (by omega : i + 1 < 64), limbs_of_lt (by omega : (b : ℕ) * 2 ^ (i + 1) < 2 ^ 64),
        limbs_of_lt (by have := b.isLt; omega : (b : ℕ) < 2 ^ 64), limbs_two_pow (by omega : i + 1 < 64)]
      simp only [max_self, Nat.mul_one]
      omega) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero, max_self] at h1 ⊢
  have : (hatPrice + 11 + 16) * 2 ^ (N - (i + 1)) ≤ (hatPrice + 27) * 2 ^ N := Nat.mul_le_mul_left _ hle
  have : (hatPrice + 28) * 2 ^ N = (hatPrice + 27) * 2 ^ N + 2 ^ N := by ring
  omega

/-! ## The step up a level -/

/-- The price bound of the step up a level, `high` of at most `L` coefficients. -/
@[expose] def upPrice (κ κ' m R L : ℕ) : ℕ :=
  msgPrice κ κ' m + (κ * (hatPrice + 300) + hatPrice + polyPrice L + 400) * 2 ^ (κ + R) +
    1000 * κ + 1000

/-- **The step up a level over arrays** (`upAtAC`): the message, the twiddles, two additive NTTs
of `2^κ` entries on `2^(κ+R)` positions, then each column's `hatAt` and `polyOfAtH high`. The
price does not depend on `VA'`, whose entries are read in constant time. -/
theorem upAtA_cost (hP : Includes P upAtAC.costDeps) (κ κ' m R : ℕ) (VA' : AV) (high : List E) (L : ℕ)
    (hN : κ + R ≤ 62) (hκ' : κ' ≤ 62) (hm : m ≤ 62) (hL : high.length ≤ L) (hL' : L < 2 ^ 32) :
    machineCost P upAtAC.costIdx [encodeValue κ, encodeValue κ', encodeValue m, encodeValue R,
      encodeValue VA', encodeValue high] ≤ upPrice κ κ' m R L := by
  rw [upAtAC.costEq P hP, ofFnFrom_length, ofFnFrom_length, limbs_of_lt (by omega : κ + R < 2 ^ 64),
    limbs_of_lt (by omega : κ < 2 ^ 64), limbs_of_lt (by omega : R < 2 ^ 64),
    limbs_shift (by omega : κ + R < 64)]
  simp only [List.length_map, Array.length_toList, size_msgA, max_self]
  have hNp : 2 ^ (κ + R) ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hN
  have hκN : 2 ^ κ ≤ 2 ^ (κ + R) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM := msgA_cost P (by includes) κ κ' m VA' (by omega) hκ' hm
  have hT := ofFnFrom_cost P (by includes) (n := κ) (by omega) _
    (.closure upAtAC.lam0.costIdx [encodeValue κ, encodeValue R])
    (fun i ↦ RunsApp.of_spec (upAtAC.lam0.costSpec P (by includes) κ R i))
    ((hatPrice + 28) * 2 ^ (κ + R) + 27)
    (fun i ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [upAtAC.lam0.costEq P (by includes), limbs_of_lt (by omega : κ + R < 2 ^ 64),
        limbs_of_lt (by omega : κ < 2 ^ 64), limbs_of_lt (by omega : R < 2 ^ 64)]
      have := stageTwiddles_cost P (by includes) (κ + R) i (by have := i.isLt; omega) hN
      simp only [max_self]
      omega) 0 (Nat.zero_le _)
  have hm0 := map_cost P (by includes) _ (.closure upAtAC.lam1.costIdx [])
    (fun e ↦ RunsApp.of_spec (upAtAC.lam1.costSpec P (by includes) e)) 2 (msgA κ κ' m VA').toList
    (fun e _ ↦ by rw [appCost_fn, List.nil_append, upAtAC.lam1.costEq P (by includes)]; rfl)
  have hm1 := map_cost P (by includes) _ (.closure upAtAC.lam2.costIdx [])
    (fun e ↦ RunsApp.of_spec (upAtAC.lam2.costSpec P (by includes) e)) 2 (msgA κ κ' m VA').toList
    (fun e _ ↦ by rw [appCost_fn, List.nil_append, upAtAC.lam2.costEq P (by includes)]; rfl)
  have hn0 := ntt_cost P (by includes) (nttTwiddles (κ + R) κ) κ R
    ((msgA κ κ' m VA').map fun e ↦ e.limb 0) hN
  have hn1 := ntt_cost P (by includes) (nttTwiddles (κ + R) κ) κ R
    ((msgA κ κ' m VA').map fun e ↦ e.limb 1) hN
  have hF := ofFnFrom_cost P (by includes) (n := 2 ^ (κ + R)) (by omega) _
    (.closure upAtAC.lam3.costIdx [encodeValue κ, encodeValue R, encodeValue high,
      encodeValue (ntt (nttTwiddles (κ + R) κ) κ R ((msgA κ κ' m VA').map fun e ↦ e.limb 0)),
      encodeValue (ntt (nttTwiddles (κ + R) κ) κ R ((msgA κ κ' m VA').map fun e ↦ e.limb 1)),
      encodeValue (nttTwiddles (κ + R) κ), encodeValue (msgA κ κ' m VA')])
    (fun x ↦ RunsApp.of_spec (upAtAC.lam3.costSpec P (by includes) κ R high _ _ _ _ x))
    (hatPrice + polyPrice L + 218)
    (fun x ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [upAtAC.lam3.costEq P (by includes)]
      have hx : (x : ℕ) < 2 ^ 64 := by have := x.isLt; omega
      have := hatAt_cost P (by includes) κ x hx
      have := polyOfAtH_cost P (by includes) high x L hL hL' hx
      omega) 0 (Nat.zero_le _)
  simp only [Array.length_toList, size_msgA, Nat.sub_zero] at hm0 hm1 hT hF
  have e : ((hatPrice + 28) * 2 ^ (κ + R) + 27 + 16) * κ + 2 * (κ * (110 * 2 ^ (κ + R) + 100)) +
      (hatPrice + polyPrice L + 218 + 16) * 2 ^ (κ + R) + 2 ^ (κ + R) + 52 * (κ * 2 ^ (κ + R)) +
      165 * 2 ^ (κ + R) =
      (κ * (hatPrice + 300) + hatPrice + polyPrice L + 400) * 2 ^ (κ + R) + 243 * κ := by ring
  unfold upPrice
  omega

/-! ## Level 0's stack -/

/-- **Level 0's stack** (`stackAC`): `64` lanes' inverse transforms over `2^(μ−6)`, then `2^μ`
cells. -/
theorem stackA_cost (hP : Includes P stackAC.costDeps) (μ : ℕ) (VA : AV) (hμ : 6 ≤ μ) (hμ' : μ ≤ 62) :
    machineCost P stackAC.costIdx [encodeValue μ, encodeValue VA] ≤
      μ * (174 * 2 ^ μ + 186944) + 90 * 2 ^ μ + 4000 := by
  rw [stackAC.costEq P hP, ofFnFrom_length, ofFnFrom_length]
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = μ - Protocol.EndToEnd.laneBits := ⟨_, rfl⟩
  rw [← hκ]
  have hl : Protocol.EndToEnd.laneBits = 6 := rfl
  have hμe : μ = κ + 6 := by omega
  subst hμe
  rw [limbs_of_lt (by omega : κ + 6 < 2 ^ 64), limbs_of_lt (by norm_num : Protocol.EndToEnd.laneBits < 2 ^ 64),
    limbs_shift (by norm_num : Protocol.EndToEnd.laneBits < 64), limbs_shift (by omega : κ + 6 < 64)]
  have h2 : 2 ^ (κ + 6) = 64 * 2 ^ κ := by rw [pow_add]; ring
  have hNp : 2 ^ (κ + 6) ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hμ'
  have h1 := ofFnFrom_cost P (by includes) (n := 2 ^ Protocol.EndToEnd.laneBits) (by norm_num) _
    (.closure stackAC.lam0.costIdx [encodeValue VA, encodeValue κ])
    (fun u ↦ RunsApp.of_spec (stackAC.lam0.costSpec P (by includes) VA κ u))
    (κ * (174 * 2 ^ κ + 2906) + 51 * 2 ^ κ + 15 * κ + 50)
    (fun u ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [stackAC.lam0.costEq P (by includes), ofFnFrom_length, limbs_shift (by omega : κ < 64),
        limbs_of_lt (by omega : κ < 2 ^ 64)]
      simp only [List.length_map, Array.length_toList, Array.size_ofFn, max_self]
      have a := ofFnFrom_cost P (by includes) (n := 2 ^ κ) (by omega) _
        (.closure stackAC.lam0.lam1.costIdx [encodeValue VA, encodeValue κ, encodeValue u])
        (fun v ↦ RunsApp.of_spec (stackAC.lam0.lam1.costSpec P (by includes) VA κ u v)) 15
        (fun v ↦ by
          rw [appCost_fn]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [stackAC.lam0.lam1.costEq P (by includes)]) 0 (Nat.zero_le _)
      have b := map_cost P (by includes) _ (.closure stackAC.lam0.lam0.costIdx [])
        (fun x ↦ RunsApp.of_spec (stackAC.lam0.lam0.costSpec P (by includes) x)) 2
        (Array.ofFn fun v : Fin (2 ^ κ) ↦ (VA.getD v #[]).getD u 0).toList
        (fun x _ ↦ by rw [appCost_fn, List.nil_append, stackAC.lam0.lam0.costEq P (by includes)]; rfl)
      have c := rangeLoop_cost P (by includes) κ [] (by omega)
      have d := novelInv_cost P (by includes) κ (by omega)
        (limbArr 0 (Array.ofFn fun v : Fin (2 ^ κ) ↦ (VA.getD v #[]).getD u 0))
      simp only [Array.length_toList, Array.size_ofFn, Nat.sub_zero] at a b
      omega) 0 (Nat.zero_le _)
  have h3 := ofFnFrom_cost P (by includes) (n := 2 ^ (κ + 6)) (by omega) _
    (.closure stackAC.lam1.costIdx [encodeValue (κ + 6), encodeValue (Array.ofFn fun u :
      Fin (2 ^ Protocol.EndToEnd.laneBits) ↦ LeanVM.Extraction.novelInv κ
        (limbArr 0 (Array.ofFn fun v : Fin (2 ^ κ) ↦ (VA.getD v #[]).getD u 0))), encodeValue κ])
    (fun i ↦ RunsApp.of_spec (stackAC.lam1.costSpec P (by includes) (κ + 6) _ κ i)) 19
    (fun i ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [stackAC.lam1.costEq P (by includes), limbs_shift (by omega : κ < 64),
        limbs_of_lt (by omega : κ < 2 ^ 64), limbs_two_pow (by omega : κ < 64),
        limbs_of_lt (by have := i.isLt; omega : (i : ℕ) < 2 ^ 64)]
      simp) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero, show (2 : ℕ) ^ Protocol.EndToEnd.laneBits = 64 from rfl] at h1 h3 ⊢
  have e3 : 64 * (κ * (174 * 2 ^ κ + 2906)) = 11136 * (κ * 2 ^ κ) + 185984 * κ := by ring
  have e4 : (κ + 6) * (174 * 2 ^ (κ + 6) + 186944) =
      11136 * (κ * 2 ^ κ) + 66816 * 2 ^ κ + 186944 * κ + 1121664 := by rw [h2]; ring
  simp only [max_self]
  omega

/-! ## A commitment's lanes from its leaves -/

theorem extRow_cost (hP : Includes P Auto.LeanVM.Protocol.Verifier.extRow.c498.costDeps) :
    ∀ l : List K, machineCost P Auto.LeanVM.Protocol.Verifier.extRow.c498.costIdx [encodeValue l] ≤
      9 * l.length + 7
  | [] => by rw [Auto.LeanVM.Protocol.Verifier.extRow.c498.costEq P hP]; simp
  | [a] => by rw [Auto.LeanVM.Protocol.Verifier.extRow.c498.costEq P hP]; simp
  | a :: b :: t => by
    rw [Auto.LeanVM.Protocol.Verifier.extRow.c498.costEq P hP]
    have := extRow_cost hP t
    simp only [List.length_cons]
    omega

theorem length_extRow_le : ∀ l : List K, (Protocol.Verifier.extRow l).length ≤ l.length
  | [] => by simp [Protocol.Verifier.extRow]
  | [a] => by simp [Protocol.Verifier.extRow]
  | a :: b :: t => by
    have := length_extRow_le t
    simp only [Protocol.Verifier.extRow, List.length_cons]
    omega

theorem length_lanesOf_le (i : ℕ) (row : List K) : (lanesOf i row).length ≤ row.length := by
  unfold lanesOf
  split_ifs
  · simp
  · exact length_extRow_le row

/-- **A leaf's lanes** (`lanesOf.c496`). -/
theorem lanesOf_cost (hP : Includes P Auto.LeanVM.Protocol.Whir.Sound.lanesOf.c496.costDeps) (i : ℕ)
    (row : List K) (hi : i < 2 ^ 64) :
    machineCost P Auto.LeanVM.Protocol.Whir.Sound.lanesOf.c496.costIdx [encodeValue i, encodeValue row] ≤
      29 * row.length + 15 := by
  rw [Auto.LeanVM.Protocol.Whir.Sound.lanesOf.c496.costEq P hP, limbs_of_lt hi]
  split_ifs
  · have h1 := reverseAux_cost P (by includes) row []
    have h2 := map_cost P (by includes) _
      (.closure Auto.LeanVM.Protocol.Whir.Sound.lanesOf.c496.lam0.costIdx [])
      (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Whir.Sound.lanesOf.c496.lam0.costSpec P
        (by includes) a)) 5 row.reverse
      (fun a _ ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Protocol.Whir.Sound.lanesOf.c496.lam0.costEq P (by includes)]
        rfl)
    rw [List.length_reverse] at h2
    omega
  · have := extRow_cost P (by includes) row
    omega

theorem length_leafAt_le (lv : Array (List K)) (h w v W : ℕ) (hlv : ∀ l ∈ lv, l.length ≤ W)
    (hw : w ≤ W) : (LeanVM.Extraction.leafAt lv h w v).length ≤ W := by
  unfold LeanVM.Extraction.leafAt
  rw [Array.getD]
  split
  · exact hlv _ (Array.getElem_mem _)
  · simpa using hw

/-- **Column `v`'s lanes of commitment `i`** (`laneRowC`), leaves of at most `W` words. -/
theorem laneRow_cost (hP : Includes P laneRowC.costDeps) (i : ℕ) (lv : Array (List K)) (h w v W : ℕ)
    (hlv : ∀ l ∈ lv, l.length ≤ W) (hw : w ≤ W) (hW : W < 2 ^ 62) (hh : h < 64) (hv : v < 2 ^ 64)
    (hi : i < 2 ^ 64) :
    machineCost P laneRowC.costIdx [encodeValue i, encodeValue lv, encodeValue h, encodeValue w,
      encodeValue v] ≤ 45 * W + 40 := by
  rw [laneRowC.costEq P hP]
  have hl := length_leafAt_le lv h w v W hlv hw
  have h1 := leafAt_cost P (by includes) lv h w v hh hv (by omega)
  have h2 := lanesOf_cost P (by includes) i (LeanVM.Extraction.leafAt lv h w v) hi
  have h3 := length_lanesOf_le i (LeanVM.Extraction.leafAt lv h w v)
  omega

/-- **The `n` columns' lanes of commitment `i`** (`laneRowsC`). -/
theorem laneRows_cost (hP : Includes P laneRowsC.costDeps) (n i : ℕ) (lv : Array (List K)) (h w W : ℕ)
    (hlv : ∀ l ∈ lv, l.length ≤ W) (hw : w ≤ W) (hW : W < 2 ^ 62) (hh : h < 64) (hn : n < 2 ^ 64)
    (hi : i < 2 ^ 64) :
    machineCost P laneRowsC.costIdx [encodeValue n, encodeValue i, encodeValue lv, encodeValue h,
      encodeValue w] ≤ (45 * W + 68) * n + 20 := by
  rw [laneRowsC.costEq P hP, ofFnFrom_length]
  have := ofFnFrom_cost P (by includes) hn _
    (.closure laneRowsC.lam0.costIdx [encodeValue n, encodeValue i, encodeValue lv, encodeValue h,
      encodeValue w])
    (fun v ↦ RunsApp.of_spec (laneRowsC.lam0.costSpec P (by includes) n i lv h w v)) (45 * W + 51)
    (fun v ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [laneRowsC.lam0.costEq P (by includes)]
      have := laneRow_cost P (by includes) i lv h w v W hlv hw hW hh (by have := v.isLt; omega) hi
      omega) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero] at this
  have e : (45 * W + 68) * n = (45 * W + 51 + 16) * n + n := by ring
  omega

/-! ## A root's leaves -/

/-- The price bound of a root's leaves through the roots' index: the subtree of height `h`, leaves
of `w` words. -/
@[expose] def leavesPrice (D Wl w h : ℕ) : ℕ :=
  19 + 2 ^ h * (2 * (D * (20 + (162 + 9 * Wl) * (D + 2)) + 42) + 468 * w + 30760 + 5 * h)

/-- **The committed leaves through the transcript's index at `L`** (`leavesInC`). -/
theorem leavesInC_cost (hP : Includes P Extractor.leavesInC.costDeps)
    (qs : List (Common.PermutationQuery Semantics.KeccakState × Semantics.KeccakState)) (L D Wl : ℕ)
    (hL : L < 2 ^ 64) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ Wl) (hN : qs.length + 2 ≤ 2 ^ D)
    (w h : ℕ) (hw : w < 2 ^ 57) (root : LeanVM.Protocol.Digest) :
    machineCost P Extractor.leavesInC.costIdx [encodeValue (Extraction.Fast.transcriptIndex qs L),
      encodeValue w, encodeValue h, encodeValue root] ≤ leavesPrice D Wl w h := by
  rw [Extractor.leavesInC.costEq P hP]
  have hS := subtreeLeavesWithC_cost P (by includes) _
    (.closure Extractor.leavesInC.lam0.costIdx [encodeValue (Extraction.Fast.transcriptIndex qs L)])
    (fun d n ↦ RunsApp.of_spec (Extractor.leavesInC.lam0.costSpec P (by includes) _ d n))
    (D * (20 + (162 + 9 * Wl) * (D + 2)) + 42)
    (fun d n hn ↦ preimageLookup_cost P (by includes) qs L D Wl hL hW hN d n hn)
    w (by omega) h root
  have e : D * (20 + (162 + 9 * Wl) * (D + 2)) + 42 + 15 * w + 30725 +
      (D * (20 + (162 + 9 * Wl) * (D + 2)) + 42 + 453 * w + 35) + 5 * h =
      2 * (D * (20 + (162 + 9 * Wl) * (D + 2)) + 42) + 468 * w + 30760 + 5 * h := by ring
  rw [e] at hS
  unfold leavesPrice
  omega

/-- **A root's leaves** (`leavesAtC`). -/
theorem leavesAt_cost (hP : Includes P leavesAtC.costDeps)
    (qs : List (Common.PermutationQuery Semantics.KeccakState × Semantics.KeccakState)) (L D Wl : ℕ)
    (hL : L < 2 ^ 64) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ Wl) (hN : qs.length + 2 ≤ 2 ^ D)
    (x : LeanVM.Protocol.Digest × ℕ × ℕ) (hw : x.2.2 < 2 ^ 57) :
    machineCost P leavesAtC.costIdx [encodeValue (Extraction.Fast.transcriptIndex qs L), encodeValue x] ≤
      leavesPrice D Wl x.2.2 x.2.1 + 10 := by
  rw [leavesAtC.costEq P hP]
  have := leavesInC_cost P (by includes) qs L D Wl hL hW hN x.2.2 x.2.1 hw x.1
  omega

/-! ## The levels' shapes -/

/-- Every level of the fold table spans at most `2^34` columns. -/
theorem foldTable_small : (Protocol.Whir.AffineCombiner.foldTable.all fun row ↦ row.all fun lvs ↦
    lvs.all fun lv ↦ decide (lv.1 + lv.2.1 ≤ 34)) = true := by
  decide +kernel

theorem levels_small (μ R i : ℕ) :
    ((Protocol.Whir.Params.levelsOf μ R).getD i Protocol.Whir.Params.junkLv).1 +
      ((Protocol.Whir.Params.levelsOf μ R).getD i Protocol.Whir.Params.junkLv).2.1 ≤ 34 := by
  have hT := foldTable_small
  simp only [List.all_eq_true, decide_eq_true_eq] at hT
  rw [List.getD_eq_getElem?_getD]
  cases h : (Protocol.Whir.Params.levelsOf μ R)[i]? with
  | none => simp [Protocol.Whir.Params.junkLv]
  | some lv =>
    simp only [Option.getD_some]
    have hm := List.mem_of_getElem? h
    unfold Protocol.Whir.Params.levelsOf at hm
    rw [List.getD_eq_getElem?_getD] at hm
    cases h2 : (Protocol.Whir.AffineCombiner.foldTable.getD (R - 1) [])[μ - 16]? with
    | none => rw [h2] at hm; simp at hm
    | some lvs =>
      rw [h2, Option.getD_some] at hm
      have hm2 := List.mem_of_getElem? h2
      rw [List.getD_eq_getElem?_getD] at hm2
      cases h3 : Protocol.Whir.AffineCombiner.foldTable[R - 1]? with
      | none => rw [h3] at hm2; simp at hm2
      | some row =>
        rw [h3, Option.getD_some] at hm2
        exact hT row (List.mem_of_getElem? h3) lvs hm2 lv hm

theorem lvC_small (μ R i : ℕ) : (lvC μ R i).1 + (lvC μ R i).2.1 ≤ 34 := by
  have := levels_small μ R i
  unfold lvC
  dsimp only
  split_ifs <;> simp only <;> omega

theorem foldTable_cost (hP : Includes P Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable.c343.costDeps) :
    machineCost P Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable.c343.costIdx [] = 19709 := by
  rw [Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable.c343.costEq P hP,
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_16.c344.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_17.c345.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_18.c346.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_19.c347.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_20.c348.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_21.c349.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_22.c350.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_23.c351.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_24.c352.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_25.c353.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_26.c354.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_27.c355.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_28.c356.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_29.c357.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_30.c358.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_16.c359.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_17.c360.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_18.c361.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_19.c362.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_20.c363.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_21.c364.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_22.c365.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_23.c366.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_24.c367.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_25.c368.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_26.c369.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_27.c370.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_28.c371.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_29.c372.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_30.c373.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_16.c374.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_17.c375.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_18.c376.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_19.c377.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_20.c378.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_21.c379.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_22.c380.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_23.c381.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_24.c382.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_25.c383.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_26.c384.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_27.c385.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_28.c386.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_29.c387.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_30.c388.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_16.c389.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_17.c390.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_18.c391.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_19.c392.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_20.c393.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_21.c394.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_22.c395.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_23.c396.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_24.c397.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_25.c398.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_26.c399.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_27.c400.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_28.c401.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_29.c402.costEq P (by includes),
    Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_30.c403.costEq P (by includes)]

theorem levelsOf_cost (hP : Includes P Auto.LeanVM.Protocol.Whir.Params.levelsOf.c342.costDeps) (μ R : ℕ)
    (hμ : μ < 2 ^ 60) (hR : R < 2 ^ 60) :
    machineCost P Auto.LeanVM.Protocol.Whir.Params.levelsOf.c342.costIdx [encodeValue μ, encodeValue R] ≤
      15 * (μ + R) + 19760 := by
  rw [Auto.LeanVM.Protocol.Whir.Params.levelsOf.c342.costEq P hP, foldTable_cost P (by includes),
    limbs_of_lt (by omega : R < 2 ^ 64), limbs_of_lt (by omega : μ < 2 ^ 64)]
  have h1 := getD_cost_idx P (by includes) Protocol.Whir.AffineCombiner.foldTable (R - 1) [] (by omega)
  have h2 := getD_cost_idx P (by includes) (Protocol.Whir.AffineCombiner.foldTable.getD (R - 1) []) (μ - 16) []
    (by omega)
  omega

/-- **A level's shape** (`lvC.c341`). -/
theorem lvC_cost (hP : Includes P Auto.LeanVM.Protocol.Whir.Sound.lvC.c341.costDeps) (μ R i : ℕ)
    (hμ : μ < 2 ^ 60) (hR : R < 2 ^ 60) (hi : i < 2 ^ 60) :
    machineCost P Auto.LeanVM.Protocol.Whir.Sound.lvC.c341.costIdx [encodeValue μ, encodeValue R,
      encodeValue i] ≤ 15 * (μ + R + i) + 20000 := by
  rw [Auto.LeanVM.Protocol.Whir.Sound.lvC.c341.costEq P hP,
    Auto.LeanVM.Protocol.Whir.Params.junkLv.c404.costEq P (by includes)]
  have h1 := levelsOf_cost P (by includes) μ R hμ hR
  have h2 := getD_cost_idx P (by includes) (Protocol.Whir.Params.levelsOf μ R) i Protocol.Whir.Params.junkLv (by omega)
  have hs := levels_small μ R i
  generalize (Protocol.Whir.Params.levelsOf μ R).getD i Protocol.Whir.Params.junkLv = lv at hs ⊢
  rw [limbs_of_lt (by omega : lv.1 + lv.2.1 < 2 ^ 64), limbs_of_lt (by omega : lv.1 < 2 ^ 64),
    limbs_of_lt (by omega : lv.2.1 < 2 ^ 64)]
  split_ifs <;> simp only [max_self] <;> omega

/-! ## The roots' words -/

/-- The price bound of root `i`'s word. -/
@[expose] def wordPrice (D Wl μ R i : ℕ) (x : LeanVM.Protocol.Digest × ℕ × ℕ) : ℕ :=
  2 * (15 * (μ + R + i) + 20000) + leavesPrice D Wl x.2.2 x.2.1 +
    (45 * x.2.2 + 68) * 2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) + 60

/-- **Root `i`'s word** (`wordArrOfC`): its level's shape, its leaves, its columns' lanes. -/
theorem wordArrOf_cost (hP : Includes P wordArrOfC.costDeps) (μ R : ℕ)
    (qs : List (Common.PermutationQuery Semantics.KeccakState × Semantics.KeccakState)) (L : ℕ) (i : ℕ)
    (x : LeanVM.Protocol.Digest × ℕ × ℕ) (D Wl : ℕ) (hL : L < 2 ^ 64)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ Wl)
    (hN : qs.length + 2 ≤ 2 ^ D) (hw : x.2.2 < 2 ^ 57) (hh : x.2.1 < 64)
    (hμ : μ < 2 ^ 60) (hR : R < 2 ^ 60) (hi : i < 2 ^ 60) :
    machineCost P wordArrOfC.costIdx [encodeValue μ, encodeValue R,
      encodeValue (Extraction.Fast.transcriptIndex qs L), encodeValue i, encodeValue x] ≤
      wordPrice D Wl μ R i x := by
  rw [wordArrOfC.costEq P hP]
  have hs := lvC_small μ R i
  have hN2 : 2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hs
  rw [limbs_of_lt (by omega : (lvC μ R i).1 + (lvC μ R i).2.1 < 2 ^ 64),
    limbs_of_lt (by omega : (lvC μ R i).1 < 2 ^ 64), limbs_of_lt (by omega : (lvC μ R i).2.1 < 2 ^ 64),
    limbs_shift (by omega : (lvC μ R i).1 + (lvC μ R i).2.1 < 64)]
  have h1 := lvC_cost P (by includes) μ R i hμ hR hi
  have h2 := leavesAt_cost P (by includes) qs L D Wl hL hW hN x hw
  have h3 := laneRows_cost P (by includes) (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) i
    (LeanVM.Extraction.AS.leavesAt (Extraction.Fast.transcriptIndex qs L) x) x.2.1 x.2.2 x.2.2
    (fun l hl ↦ (subtreeLeavesWith_mem_length _ _ _ _ l hl).le) le_rfl (by omega) hh (by omega) (by omega)
  unfold wordPrice
  simp only [max_self]
  omega

/-- The price bound of the roots' words from root `i` on. -/
@[expose] def wordsPrice (D Wl μ R : ℕ) : ℕ → List (LeanVM.Protocol.Digest × ℕ × ℕ) → ℕ
  | _, [] => 3
  | i, x :: xs => wordPrice D Wl μ R i x + 21 + wordsPrice D Wl μ R (i + 1) xs

/-- **Every root's word from root `a` on, the recursive worker** (`wordsGo.c506`), through the
transcript's index at `L`. -/
theorem wordsGoWorker_cost (hP : Includes P Auto.LeanVM.Extraction.AS.wordsGo.c506.costDeps) (μ R : ℕ)
    (qs : List (Common.PermutationQuery Semantics.KeccakState × Semantics.KeccakState)) (L D Wl : ℕ)
    (hL : L < 2 ^ 64) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ Wl) (hN : qs.length + 2 ≤ 2 ^ D)
    (hμ : μ < 2 ^ 60) (hR : R < 2 ^ 60) :
    ∀ (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)) (a : ℕ),
      (∀ x ∈ roots, x.2.2 < 2 ^ 57 ∧ x.2.1 < 64) → a + roots.length < 2 ^ 60 →
      machineCost P Auto.LeanVM.Extraction.AS.wordsGo.c506.costIdx [encodeValue μ, encodeValue R,
        encodeValue (Extraction.Fast.transcriptIndex qs L), encodeValue a, encodeValue roots] ≤
        wordsPrice D Wl μ R a roots
  | [], a, _, _ => by
    rw [Auto.LeanVM.Extraction.AS.wordsGo.c506.costEq_nil P hP]
    simp [wordsPrice]
  | x :: xs, a, hx, ha => by
    rw [Auto.LeanVM.Extraction.AS.wordsGo.c506.costEq_cons P hP]
    simp only [List.length_cons] at ha
    obtain ⟨h2, h3⟩ := hx x List.mem_cons_self
    have c1 := wordArrOf_cost P (by includes) μ R qs L a x D Wl hL hW hN h2 h3 hμ hR (by omega)
    have c2 := wordsGoWorker_cost hP μ R qs L D Wl hL hW hN hμ hR xs (a + 1)
      (fun y hy ↦ hx y (List.mem_cons_of_mem _ hy)) (by omega)
    rw [limbs_of_lt (by omega : a + 1 < 2 ^ 64), limbs_of_lt (by omega : a < 2 ^ 64)]
    simp only [wordsPrice, max_self]
    omega

end

end LeanVM.Cost.Bounds.AS
