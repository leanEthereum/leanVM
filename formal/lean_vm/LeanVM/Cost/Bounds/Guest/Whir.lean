module

public import LeanVM.Cost.Bounds.Guest.Signatures

/-!
# Bounds on the guest decoder's prices: a child's proof

`verify_sub`'s witness, the child proof, off `open_stacked`'s tables as arrays
(`Cost/Decoder/Signatures.lean`: `vsPiOfNC` is `vsPiOfA`, `Guest/Fast/Whir.lean`): its stream words
and, per level of the opening's candidate (`WhirTabs.calls`), the queries of `opening_queries` and
their openings, in the price `R` of a memory read, `S` of the valuation, `F` of the frame map, the
cursor's length at most `L` and its price at most `C`:

* the levels' shapes (`OqOK`, `callOK_osCallsTab`: the table's every call, by kernel evaluation),
  the tables as arrays (`WhirTabsOK`, `whirTabs_ok`), a call's shape (`osCallShape_cost`: the
  table of shapes built, `shapePrice`), the shape's numbers (`Oq.I`, `Oq.B`, the fold's values,
  `oqE1`, …: constants);
* consecutive words, the address stepped by `g` (`wordsFrom_cost`: `R + 56` a word), a query's
  windows' exponents off the lanes (`winLogsFrom_cost`: `R + 3050` a window), its position from
  them (`winBit_cost`, `bitsB_cost`, `winPosAt_cost`, `winPosOfW_cost`: at most `6` windows and
  `32` bits), row
  (`oqRow_cost`) and siblings (`oqSibsOf_cost`), a query, its position read once
  (`oqQueryAt_cost`, `oqQueryA_cost`), an iteration (`oqIterA_cost`), the loop, its frames at the
  next power of `g` (`oqItersFrom_cost`), the queries (`oqsOfA_cost`), a query's opening
  (`toOpening_cost`, `capSibsOf_cost`), the `opening_queries` call's words (`oqCallArgs_cost`), a
  level (`levelOsAt_cost`, `levelOsQ_cost`, `levelOsF_cost`, `levelOsA_cost`);
* **`vsPiOfN_cost`**: a child's proof (`vsPiOfAt_cost`, `vsPiOfM_cost`, `vsPiOfS_cost`), at most
  `vsPiPrice R S F C L`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram)

theorem listCasesOn_le {α : Type} (l : List α) (a : ℕ) (f : α → List α → ℕ)
    (hf : ∀ x y, f x y ≤ a) : (List.casesOn (motive := fun _ ↦ ℕ) l a f) ≤ a := by
  cases l
  · exact le_rfl
  · exact hf _ _

/-! ## The levels' shapes -/

/-- A level's shape, all small: level 0 (`base = 1`) is never the final level, a deeper level
folds at most `4` rounds. -/
@[expose] def OqOK (s : Oq) : Prop :=
  s.base ≤ 1 ∧ s.folds ≤ 6 ∧ s.pd ≤ 24 ∧ s.cd ≤ 8 ∧ s.final ≤ 1 ∧ (s.base = 1 → s.final = 0) ∧
    (s.base = 1 ∨ s.folds ≤ 4) ∧ s.B ≤ 8 ∧ oqE1 s < 2 ^ 20

instance (s : Oq) : Decidable (OqOK s) := by unfold OqOK; infer_instance

/-- A `level_queries` dispatch of the table and the `opening_queries` call in its callee: its
shape's, its loop's and its words' bounds. -/
@[expose] def CallOK (c : OsCall) : Prop :=
  OqOK c.shape.oq ∧ c.shape.odd ≤ 1 ∧ c.N ≤ 112 ∧ c.fn < 2 ^ 20 ∧ c.loop < 2 ^ 20 ∧
    c.walk < 2 ^ 20 ∧ c.depth ≤ 28 ∧ c.args.length ≤ 6 ∧ c.rets.length ≤ 4 ∧ c.cd ≤ 8 ∧
    c.sh < 2 ^ 20 ∧ c.shape.depth ≤ 28 ∧ c.shape.cd ≤ 8 ∧ c.lq < 2 ^ 20

instance (c : OsCall) : Decidable (CallOK c) := by unfold CallOK; infer_instance

theorem callOK_osCallsTab : osCallsTab.length = 44 ∧ (∀ cs ∈ osCallsTab, cs.length ≤ 6) ∧
    ∀ cs ∈ osCallsTab, ∀ c ∈ cs, CallOK c := by decide +kernel

theorem osWordsTab_ok : osWordsTab.length = 44 ∧ ∀ x ∈ osWordsTab, x ≤ 206 := by decide +kernel

/-- `open_stacked`'s tables as arrays: the lanes below `2^64`, each size and rate's words at most
`206`, its dispatches at most `6`, each of the table's shapes (`whirTabs_ok`). -/
structure WhirTabsOK (T : WhirTabs) : Prop where
  lanes : ∀ x ∈ T.lanes, x < 2 ^ 64
  words : ∀ m, T.words.getD m 0 ≤ 206
  calls : ∀ m, (T.calls.getD m []).length ≤ 6 ∧ ∀ c ∈ T.calls.getD m [], CallOK c

theorem callOK_getD (m : ℕ) :
    (osCallsTab.getD m []).length ≤ 6 ∧ ∀ c ∈ osCallsTab.getD m [], CallOK c := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : osCallsTab[m]? with
  | none => simp
  | some cs =>
    have := List.mem_of_getElem? hk
    exact ⟨callOK_osCallsTab.2.1 cs this, callOK_osCallsTab.2.2 cs this⟩

theorem whirTabs_ok : WhirTabsOK whirTabs := by
  refine ⟨gLanes_ok.2, fun m ↦ ?_, fun m ↦ ?_⟩
  · show osWordsTab.toArray.getD m 0 ≤ 206
    rw [getD_toArray, List.getD_eq_getElem?_getD]
    cases hk : osWordsTab[m]? with
    | none => simp
    | some x => exact osWordsTab_ok.2 x (List.mem_of_getElem? hk)
  · show (osCallsTab.toArray.getD m []).length ≤ 6 ∧ ∀ c ∈ osCallsTab.toArray.getD m [], CallOK c
    rw [getD_toArray]
    exact callOK_getD m

/-- **`open_stacked`'s tables, built** (`whirTabsC`): at most `15454`. -/
theorem whirTabs_cost (hP : Includes P Decoder.whirTabsC.costDeps) :
    machineCost P Decoder.whirTabsC.costIdx [] ≤ 15454 := by
  rw [Decoder.whirTabsC.costEq P hP, Decoder.gLanesC.costEq P (by includes),
    Decoder.osWordsTabC.costEq P (by includes), Decoder.osCallsTabC.costEq P (by includes),
    osWordsTab_ok.1, callOK_osCallsTab.1]

/-- A call's shape's price: the table of shapes built, its entry looked up. -/
@[expose] def shapePrice : ℕ := 2659 + 25 + (15 * 76 + 9) + 5

theorem oqShapeTab_length : Decoder.oqShapeTab.length = 76 := rfl

/-- **A call's shape** (`OsCallShapeC`): at most `shapePrice`. -/
theorem osCallShape_cost (hP : Includes P Decoder.OsCallShapeC.costDeps) (c : OsCall)
    (hc : c.sh < 2 ^ 64) :
    machineCost P Decoder.OsCallShapeC.costIdx [encodeValue c] ≤ shapePrice := by
  rw [Decoder.OsCallShapeC.costEq P hP, Decoder.oqShapeTabC.costEq P (by includes),
    Decoder.oqShapeZeroC.costEq P (by includes)]
  have := getD_cost P (by includes) Decoder.oqShapeTab c.sh LeanVM.Guest.B1.Whir.oqShapeZero hc
  rw [oqShapeTab_length] at this
  unfold shapePrice
  omega

/-- A shape's template shape (`OqShapeOqC`), its depths small: `28`. -/
theorem oqShapeOq_cost (hP : Includes P Decoder.OqShapeOqC.costDeps) (sh : OqShape)
    (hd : sh.depth ≤ 28) (hcd : sh.cd ≤ 8) :
    machineCost P Decoder.OqShapeOqC.costIdx [encodeValue sh] ≤ 28 := by
  rw [Decoder.OqShapeOqC.costEq P hP]
  limbs_one; omega

/-! ## The shape's numbers -/

theorem two_pow_le_64 {k : ℕ} (hk : k ≤ 6) : 2 ^ k ≤ 64 :=
  (Nat.pow_le_pow_right (by norm_num) hk).trans (by norm_num)

theorem shift_le_64 {k : ℕ} (hk : k ≤ 6) : 1 <<< k ≤ 64 := by
  rw [Nat.one_shiftLeft]; exact two_pow_le_64 hk

section Shape

variable {s : Oq} (hs : OqOK s)
include hs

theorem oqI_le : s.I ≤ 64 := two_pow_le_64 hs.2.1

theorem oqNcells_le : s.ncells ≤ 64 := by
  have := oqI_le hs
  unfold Oq.ncells; split_ifs <;> omega

theorem oqChainLen_le : s.chainLen ≤ 157 := by
  have := hs.2.2.2.2.2.2.2.1
  unfold Oq.chainLen; omega

theorem Oq_I_cost (hP : Includes P Decoder.OqIC.costDeps) :
    machineCost P Decoder.OqIC.costIdx [encodeValue s] ≤ 4 := by
  have := shift_le_64 hs.2.1
  have := hs.2.1
  rw [Decoder.OqIC.costEq P hP]
  limbs_one; omega

theorem Oq_ncells_cost (hP : Includes P Decoder.OqNcellsC.costDeps) :
    machineCost P Decoder.OqNcellsC.costIdx [encodeValue s] ≤ 13 := by
  have := Oq_I_cost P hs (by includes)
  have := oqI_le hs
  have := hs.1
  rw [Decoder.OqNcellsC.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem Oq_B_cost (hP : Includes P Decoder.OqBC.costDeps) :
    machineCost P Decoder.OqBC.costIdx [encodeValue s] ≤ 21 := by
  have := Oq_ncells_cost P hs (by includes)
  have := oqNcells_le hs
  have hr : LeanVM.Protocol.KeccakHash.rate = 136 := rfl
  rw [Decoder.OqBC.costEq P hP, hr]
  limbs_one; omega

theorem Oq_chainLen_cost (hP : Includes P Decoder.OqChainLenC.costDeps) :
    machineCost P Decoder.OqChainLenC.costIdx [encodeValue s] ≤ 31 := by
  have := Oq_B_cost P hs (by includes)
  have := hs.2.2.2.2.2.2.2.1
  rw [Decoder.OqChainLenC.costEq P hP]
  limbs_one; omega

theorem oqK1_lt (b : ℕ) (hb : b < 2 ^ 21) : oqK1 s b < 2 ^ 22 := by
  have := oqI_le hs
  unfold oqK1; split_ifs <;> omega

theorem oqK1_cost (hP : Includes P Decoder.oqK1C.costDeps) (b : ℕ) (hb : b < 2 ^ 21) :
    machineCost P Decoder.oqK1C.costIdx [encodeValue s, encodeValue b] ≤ 24 := by
  have := Oq_I_cost P hs (by includes)
  have := oqI_le hs
  have := hs.1
  rw [Decoder.oqK1C.costEq P hP]
  limbs_one; split_ifs <;> limbs_one <;> omega

theorem oqKL_lt (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) : oqKL s b emit < 2 ^ 23 := by
  have := oqK1_lt hs b hb
  unfold oqKL; split_ifs <;> omega

theorem oqCh_lt (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) : oqCh s b emit < 2 ^ 24 := by
  have := oqKL_lt hs b hb emit
  have := oqChainLen_le hs
  unfold oqCh; omega

theorem oqKL_cost (hP : Includes P Decoder.oqKLC.costDeps) (b : ℕ)
    (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Decoder.oqKLC.costIdx
      [encodeValue s, encodeValue b, encodeValue emit] ≤ 31 := by
  have := oqK1_cost P hs (by includes) b hb
  have := oqK1_lt hs b hb
  rw [Decoder.oqKLC.costEq P hP]
  limbs_one; split_ifs <;> limbs_one <;> omega

theorem oqCh_cost (hP : Includes P Decoder.oqChC.costDeps) (b : ℕ)
    (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Decoder.oqChC.costIdx
      [encodeValue s, encodeValue b, encodeValue emit] ≤ 69 := by
  have := oqKL_cost P hs (by includes) b hb emit
  have := Oq_chainLen_cost P hs (by includes)
  have := oqKL_lt hs b hb emit
  have := oqChainLen_le hs
  rw [Decoder.oqChC.costEq P hP]
  limbs_one; omega

theorem two_pow_fold_le (j : ℕ) : 2 ^ (s.folds - 1 - j) ≤ 32 :=
  (Nat.pow_le_pow_right (by norm_num) (by have := hs.2.1; omega :
    s.folds - 1 - j ≤ 5)).trans (by norm_num)

/-- A fold round's first value, `j` rounds in: at most `73` a round. -/
theorem oqRK_le (F : ℕ) : ∀ j, oqRK s F j ≤ F + 73 * j
  | 0 => by simp [oqRK]
  | j + 1 => by
    have := oqRK_le F j
    have := two_pow_fold_le hs j
    simp only [oqRK]; omega

/-- The fold's rounds' first values (`oqRKC`), from `F < 2^24`, `j ≤ 6` rounds: `31·j + 5`. -/
theorem oqRK_cost (hP : Includes P Decoder.oqRKC.costDeps) (F : ℕ) (hF : F < 2 ^ 24) :
    ∀ j, j ≤ 6 →
      machineCost P Decoder.oqRKC.costIdx [encodeValue s, encodeValue F, encodeValue j] ≤ 31 * j + 5
  | 0, _ => by rw [Decoder.oqRKC.costEq_zero P hP]
  | j + 1, hj => by
    rw [Decoder.oqRKC.costEq_succ P hP]
    have := oqRK_cost hP F hF j (by omega)
    have := oqRK_le hs F j
    have h2 := two_pow_fold_le hs j
    have : 1 <<< (s.folds - 1 - j) ≤ 32 := by rw [Nat.one_shiftLeft]; exact h2
    have := hs.2.1
    limbs_one; omega

theorem oqVal_le (F : ℕ) : oqVal s F ≤ F + 438 := by
  have := oqRK_le hs F (s.folds - 1)
  have := hs.2.1
  unfold oqVal oqAcc oqRO; omega

theorem oqVal_cost (hP : Includes P Decoder.oqValC.costDeps) (F : ℕ) (hF : F < 2 ^ 24) :
    machineCost P Decoder.oqValC.costIdx [encodeValue s, encodeValue F] ≤ 196 := by
  have := oqRK_cost P hs (by includes) F hF (s.folds - 1) (by have := hs.2.1; omega)
  have := oqRK_le hs F (s.folds - 1)
  have := hs.2.1
  rw [Decoder.oqValC.costEq P hP, Auto.LeanVM.Guest.B1.oqAcc.c865.costEq P (by includes)]
  unfold oqRO
  limbs_one; omega

theorem oqRes_le (hf : s.final = 0) (b : ℕ) (emit : Bool) :
    oqRes s b emit ≤ oqCh s b emit + 438 := by
  unfold oqRes
  simp only [hf, Nat.zero_ne_one, ↓reduceIte]
  exact oqVal_le hs _

/-- A query's result (`oqResNC`), below the final level: at most `276`. -/
theorem oqResN_cost (hP : Includes P Decoder.oqResNC.costDeps) (hf : s.final = 0) (b : ℕ)
    (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Decoder.oqResNC.costIdx [encodeValue s, encodeValue b, encodeValue emit] ≤ 276 := by
  have := oqCh_cost P hs (by includes) b hb emit
  have := oqVal_cost P hs (by includes) (oqCh s b emit) (oqCh_lt hs b hb emit)
  rw [Decoder.oqResNC.costEq P hP]
  simp only [hf, Nat.zero_ne_one, ↓reduceIte]
  limbs_one; omega

theorem oqEnd_cost (hP : Includes P Decoder.oqEndC.costDeps) (hf : s.final = 0) (b : ℕ)
    (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Decoder.oqEndC.costIdx
      [encodeValue s, encodeValue b, encodeValue emit] ≤ 282 := by
  have := oqResN_cost P hs (by includes) hf b hb emit
  have := oqRes_le hs hf b emit
  have := oqCh_lt hs b hb emit
  rw [Decoder.oqEndC.costEq P hP]
  limbs_one; omega

theorem oqE1_lt : oqE1 s < 2 ^ 20 := hs.2.2.2.2.2.2.2.2

/-- The second query's first value at level 0 (`oqE1C`): at most `286`. -/
theorem oqE1_cost (hP : Includes P Decoder.oqE1C.costDeps) (hb : s.base = 1) :
    machineCost P Decoder.oqE1C.costIdx [encodeValue s] ≤ 286 := by
  have := oqEnd_cost P hs (by includes) (hs.2.2.2.2.2.1 hb) 16 (by norm_num) true
  rw [Decoder.oqE1C.costEq P hP]
  omega

theorem oqBs_cost (hP : Includes P Decoder.oqBsC.costDeps) (kL : ℕ) (hkL : kL < 2 ^ 23) :
    machineCost P Decoder.oqBsC.costIdx [encodeValue kL, encodeValue (s.B - 1)] ≤ 13 := by
  have := hs.2.2.2.2.2.2.2.1
  rw [Decoder.oqBsC.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem oqBs_lt (kL : ℕ) (hkL : kL < 2 ^ 23) : oqBs kL (s.B - 1) < 2 ^ 24 := by
  have := hs.2.2.2.2.2.2.2.1
  unfold oqBs; split_ifs <;> omega

theorem oqOut_lt (kL : ℕ) (hkL : kL < 2 ^ 23) (c : ℕ) (hc : c ≤ 1) :
    oqOut s kL (s.B - 1) c < 2 ^ 25 := by
  have := oqBs_lt hs kL hkL
  unfold oqOut; split_ifs <;> omega

theorem oqOut_cost (hP : Includes P Decoder.oqOutC.costDeps) (kL : ℕ) (hkL : kL < 2 ^ 23) (c : ℕ)
    (hc : c ≤ 1) :
    machineCost P Decoder.oqOutC.costIdx
      [encodeValue s, encodeValue kL, encodeValue (s.B - 1), encodeValue c] ≤ 60 := by
  have hb := oqBs_cost P hs (by includes) kL hkL
  have hbl := oqBs_lt hs kL hkL
  have hB := Oq_B_cost P hs (by includes)
  have := hs.2.2.2.2.2.2.2.1
  rw [Decoder.oqOutC.costEq P hP]
  limbs_one; split_ifs <;> omega

end Shape

/-! ## Consecutive words -/

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- A cell (`memReadC`), as `cellAt`. -/
theorem memRead_cost (hP : Includes P Decoder.memReadC.costDeps) (p : E)
    (k : ℕ) (hk : k < 2 ^ 40) :
    machineCost P Decoder.memReadC.costIdx
      [rdV, encodeValue p, encodeValue k] ≤ R + 2969 := by
  rw [Decoder.memReadC.costEq P hP rd rdV hrd]
  have := powSqK_cost_lt P (by includes) g k 40 (by norm_num) (by norm_num) hk
  have := hR (p.limb 0 * addressOfIndex k)
  cases rd (p.limb 0 * addressOfIndex k) <;> dsimp only <;> omega

/-- **`n` consecutive words** (`wordsFromC`), the address stepped by `g`: `(R + 56)·n + 5`. -/
theorem wordsFrom_cost (hP : Includes P Decoder.wordsFromC.costDeps) :
    ∀ (n : ℕ) (a : K), n < 2 ^ 64 →
      machineCost P Decoder.wordsFromC.costIdx [rdV, encodeValue a, encodeValue n] ≤
        (R + 56) * n + 5
  | 0, a, _ => by rw [Decoder.wordsFromC.costEq_zero P hP rd rdV hrd]; omega
  | n + 1, a, hn => by
    rw [Decoder.wordsFromC.costEq_succ P hP rd rdV hrd, limbs_of_lt hn]
    have := wordsFrom_cost hP n (a * Parameters.g) (by omega)
    have := hR a
    have : (Option.casesOn (motive := fun _ ↦ ℕ) (rd a) 5 fun _ ↦ 2) ≤ 5 := by
      cases rd a <;> simp
    rw [Nat.mul_succ]
    omega

omit hrd hR in
theorem length_wordsFrom (a : K) : ∀ n, (wordsFrom rd a n).length = n
  | 0 => rfl
  | n + 1 => by rw [wordsFrom, List.length_cons, length_wordsFrom (a * Parameters.g) n]

/-- **`n` windows' exponents** (`winLogsFromC`), the address stepped by `g`, each off the lanes
below `128` (`logGTWith`): `(R + 3050)·n + 5`. -/
theorem winLogsFrom_cost (hP : Includes P Decoder.winLogsFromC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) :
    ∀ (n : ℕ) (a : K), n < 2 ^ 64 →
      machineCost P Decoder.winLogsFromC.costIdx
        [encodeValue lanes, rdV, encodeValue a, encodeValue n] ≤ (R + 3050) * n + 5
  | 0, a, _ => by rw [Decoder.winLogsFromC.costEq_zero P hP lanes rd rdV hrd]; omega
  | n + 1, a, hn => by
    rw [Decoder.winLogsFromC.costEq_succ P hP lanes rd rdV hrd, limbs_of_lt hn]
    have := winLogsFrom_cost hP lanes hl n (a * Parameters.g) (by omega)
    have := hR a
    have := logGTWith_cost P (by includes) lanes hl ((rd a).getD 0) 128 (by norm_num)
    have : (Option.casesOn (motive := fun _ ↦ ℕ) (rd a) 7 fun _ ↦ 2) ≤ 7 := by
      cases rd a <;> simp
    have : (Option.casesOn (motive := fun _ ↦ ℕ) (rd a) 5 fun _ ↦ 2) ≤ 5 := by
      cases rd a <;> simp
    rw [Nat.mul_succ]
    omega

omit hrd hR in
theorem length_winLogsFrom (lanes : List ℕ) : ∀ (a : K) (n : ℕ),
    (winLogsFrom lanes rd a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by rw [winLogsFrom, List.length_cons, length_winLogsFrom lanes (a * Parameters.g) n]

omit hrd hR in
theorem winLogsFrom_le (lanes : List ℕ) : ∀ (a : K) (n : ℕ), ∀ x ∈ winLogsFrom lanes rd a n,
    x ≤ 128
  | _, 0, _, h => by simp [winLogsFrom] at h
  | a, n + 1, x, h => by
    rw [winLogsFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact logGTWith_le _ _ _
    · exact winLogsFrom_le lanes (a * Parameters.g) n x h

omit hrd hR in
theorem qwNp_cost (hP : Includes P Decoder.qwNpC.costDeps) (d cd : ℕ) (hd : d ≤ 32) (hcd : cd ≤ 8) :
    machineCost P Decoder.qwNpC.costIdx [encodeValue d, encodeValue cd] ≤ 12 := by
  rw [Decoder.qwNpC.costEq P hP]
  limbs_one; omega

omit hrd hR in
theorem qwN_cost (hP : Includes P Decoder.qwNC.costDeps) (d cd : ℕ) (hd : d ≤ 32) (hcd : cd ≤ 8) :
    machineCost P Decoder.qwNC.costIdx [encodeValue d, encodeValue cd] ≤ 20 := by
  have := qwNp_cost P (by includes) d cd hd hcd
  rw [Decoder.qwNC.costEq P hP]
  unfold qwNp
  limbs_one; omega

omit hrd hR in
theorem qwWin_cost (hP : Includes P Decoder.qwWinC.costDeps) (d cd i : ℕ) (hd : d ≤ 32)
    (hcd : cd ≤ 8) (hi : i ≤ 32) :
    machineCost P Decoder.qwWinC.costIdx [encodeValue d, encodeValue cd, encodeValue i] ≤ 90 := by
  have := qwNp_cost P (by includes) d cd hd hcd
  rw [Decoder.qwWinC.costEq P hP]
  unfold qwNp
  limbs_one; split_ifs <;> omega

omit hrd hR in
theorem qwAt_cost (hP : Includes P Decoder.qwAtC.costDeps) (d cd l : ℕ) (hd : d ≤ 32)
    (hcd : cd ≤ 8) (hl : l < 32) :
    machineCost P Decoder.qwAtC.costIdx [encodeValue d, encodeValue cd, encodeValue l] ≤ 60 := by
  have := qwNp_cost P (by includes) d cd hd hcd
  rw [Decoder.qwAtC.costEq P hP]
  unfold qwNp
  limbs_one; split_ifs <;> omega

omit hrd hR in
theorem qwWin_fst_le (d cd i : ℕ) : (qwWin d cd i).1 ≤ d + 6 * i := by
  unfold qwWin
  by_cases h1 : i = qwNp d cd <;> by_cases h2 : i = qwNp d cd + 1 <;>
    by_cases h3 : i + 1 = qwNp d cd <;> simp [h1, h2, h3] <;> omega

omit hrd hR in
theorem getD_le_of_le (logs : List ℕ) (hv : ∀ x ∈ logs, x ≤ 128) (k : ℕ) : logs.getD k 0 ≤ 128 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : logs[k]? with
  | none => simp
  | some x => exact hv x (List.mem_of_getElem? h)

omit hrd hR in
/-- A position's bit off its windows' exponents (`winBitC`): at most `400`. -/
theorem winBit_cost (hP : Includes P Decoder.winBitC.costDeps) (logs : List ℕ)
    (hlogs : logs.length ≤ 6) (hv : ∀ x ∈ logs, x ≤ 128) (d cd l : ℕ) (hd : d ≤ 32) (hcd : cd ≤ 8)
    (hl : l < 32) :
    machineCost P Decoder.winBitC.costIdx
      [encodeValue logs, encodeValue d, encodeValue cd, encodeValue l] ≤ 400 := by
  have ha := qwAt_cost P (by includes) d cd l hd hcd hl
  have hat : qwAt d cd l ≤ 32 := by
    have := qwAt_lt_qwN d cd l
    have : qwN d cd ≤ 8 := by simp only [qwN, qwNp]; omega
    omega
  have hw := qwWin_cost P (by includes) d cd (qwAt d cd l) hd hcd hat
  have hg := getD_cost P (by includes) logs (qwAt d cd l) 0
  have hgl := getD_le_of_le logs hv (qwAt d cd l)
  have hwl : (qwWin d cd (qwAt d cd l)).1 ≤ d + 6 * qwAt d cd l := qwWin_fst_le d cd _
  have ht := testBit_cost P (by includes) (logs.getD (qwAt d cd l) 0)
    (l - (qwWin d cd (qwAt d cd l)).1) (by omega) (by omega)
  rw [Decoder.winBitC.costEq P hP]
  limbs_one; omega

omit hrd hR in
theorem bitsB_lt : ∀ l : List Bool, bitsB l < 2 ^ l.length
  | [] => by simp [bitsB]
  | b :: l => by
    have := bitsB_lt l
    rw [bitsB, List.length_cons, pow_succ]
    split_ifs <;> omega

omit hrd hR in
/-- The number of `n ≤ 62` bits (`bitsBC`): `46·n + 3`. -/
theorem bitsB_cost (hP : Includes P Decoder.bitsBC.costDeps) :
    ∀ l : List Bool, l.length ≤ 62 →
      machineCost P Decoder.bitsBC.costIdx [encodeValue l] ≤ 46 * l.length + 3
  | [], _ => by rw [Decoder.bitsBC.costEq_nil P hP]; simp
  | b :: l, hl => by
    rw [Decoder.bitsBC.costEq_cons P hP]
    have := bitsB_cost hP l (by simp at hl; omega)
    have hb := bitsB_lt l
    have h62 : 2 ^ l.length ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by simp at hl; omega)
    rw [limbs_of_lt (by omega : bitsB l < 2 ^ 64), limbs_of_lt (by omega : 2 * bitsB l < 2 ^ 64),
      List.length_cons]
    split_ifs <;> limbs_one <;> omega

omit hrd hR in
/-- A position of depth `d ≤ 32` off its windows' exponents (`winPosAtC`): `d` bits. -/
theorem winPosAt_cost (hP : Includes P Decoder.winPosAtC.costDeps) (logs : List ℕ)
    (hlogs : logs.length ≤ 6) (hv : ∀ x ∈ logs, x ≤ 128) (d cd : ℕ) (hd : d ≤ 32) (hcd : cd ≤ 8) :
    machineCost P Decoder.winPosAtC.costIdx [encodeValue logs, encodeValue d, encodeValue cd] ≤
      (410 + 28) * 32 + 17 + 46 * 32 + 3 + 9 := by
  rw [Decoder.winPosAtC.costEq P hP]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.winPosAtC.lam0.costIdx [encodeValue logs, encodeValue d, encodeValue cd])
    (fun l ↦ RunsApp.of_spec (Decoder.winPosAtC.lam0.costSpec P (by includes) logs d cd l))
    410 d 32 hd (by norm_num) (fun l hl ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.winPosAtC.lam0.costEq P (by includes), List.length_cons, List.length_cons,
        List.length_cons, List.length_nil]
      have := winBit_cost P (by includes) logs hlogs hv d cd l hd hcd (by omega)
      omega)
  have := bitsB_cost P (by includes) ((List.range d).map (winBit logs d cd)) (by simp; omega)
  simp only [List.length_map, List.length_range] at this
  omega

/-- The position price: `6` windows read in a row, their exponents, `32` bits. -/
@[expose] def posPrice (R : ℕ) : ℕ :=
  ((R + 3050) * 6 + 5) + ((410 + 28) * 32 + 17 + 46 * 32 + 3 + 9) + 20 + 20

/-- **A query's position** (`winPosOfWC`), of depth `d ≤ 32`, at most `6` windows (`cd ≥ 1`,
`d - cd ≤ 24`): at most `posPrice R`. -/
theorem winPosOfW_cost (hP : Includes P Decoder.winPosOfWC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (bp : E) (d cd : ℕ) (hd : d ≤ 32) (hcd : cd ≤ 8)
    (hw : qwN d cd ≤ 6) :
    machineCost P Decoder.winPosOfWC.costIdx
      [encodeValue lanes, rdV, encodeValue bp, encodeValue d, encodeValue cd] ≤ posPrice R := by
  rw [Decoder.winPosOfWC.costEq P hP lanes rd rdV hrd]
  have hn := qwN_cost P (by includes) d cd hd hcd
  have := winLogsFrom_cost P hrd hR (by includes) lanes hl (qwN d cd) (bp.limb 0) (by omega)
  have := Nat.mul_le_mul_left (R + 3050) hw
  have := winPosAt_cost P (by includes) (winLogsFrom lanes rd (bp.limb 0) (qwN d cd))
    (by rw [length_winLogsFrom]; exact hw) (winLogsFrom_le lanes _ _) d cd hd hcd
  unfold posPrice
  omega

omit hrd hR in
theorem winPosAt_lt (logs : List ℕ) (d cd : ℕ) : winPosAt logs d cd < 2 ^ d := by
  have := bitsB_lt ((List.range d).map (winBit logs d cd))
  simpa [winPosAt] using this

omit hrd hR in
/-- The digest of two cells (`digestOfCellsC`): at most `58`. -/
theorem digestOfCells640_cost (hP : Includes P Decoder.digestOfCellsWC.costDeps)
    (a b : E) :
    machineCost P Decoder.digestOfCellsWC.costIdx [encodeValue a, encodeValue b] ≤
      58 := by
  rw [Decoder.digestOfCellsWC.costEq P hP,
    Extractor.digestOfScalarsC.costEq P (by includes)]
  omega

omit hrd hR in
/-- A bit (`testBit.c211`), of a word: at most `9`. -/
theorem testBit_cost (hP : Includes P Auto.Nat.testBit.c211.costDeps) (q l : ℕ) (hq : q < 2 ^ 64)
    (hl : l < 2 ^ 64) :
    machineCost P Auto.Nat.testBit.c211.costIdx [encodeValue q, encodeValue l] ≤ 9 := by
  rw [Auto.Nat.testBit.c211.costEq P hP]
  have h1 : q >>> l ≤ q := Nat.shiftRight_le q l
  have h2 : 1 &&& q >>> l ≤ 1 := Nat.and_le_left
  limbs_one
  omega

/-! ## A query -/

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

omit hrd hR in
/-- A query's row (`oqRowC`), of a level's shape: `(S + 42)·64 + 25`. -/
theorem oqRow_cost (hP : Includes P Decoder.oqRowC.costDeps) (s : Oq) (hs : OqOK s) (b : ℕ)
    (hb : b < 2 ^ 21) :
    machineCost P Decoder.oqRowC.costIdx [encodeValue s, encodeValue b, σV] ≤ (S + 42) * 64 + 25 := by
  rw [Decoder.oqRowC.costEq P hP s b σ σV hσ]
  have hI := oqI_le hs
  have hf := hs.2.1
  have := shift_le_64 hf
  have := hs.1
  have h0 := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.oqRowC.lam0.costIdx [encodeValue b, σV])
    (fun i ↦ RunsApp.of_spec (Decoder.oqRowC.lam0.costSpec P (by includes) b σ σV hσ i))
    (S + 14) s.I 64 hI (by norm_num) (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.oqRowC.lam0.costEq P (by includes) b σ σV hσ, List.length_cons, List.length_cons,
        List.length_nil]
      have := hS (.n (b + i))
      limbs_one
      omega)
  limbs_one
  split_ifs with h1
  · omega
  · have h4 : s.I ≤ 16 := by
      rcases hs.2.2.2.2.2.2.1 with h | h
      · exact absurd h h1
      · unfold Oq.I; exact (Nat.pow_le_pow_right (by norm_num) h).trans (by norm_num)
    have h1' := rangeMap_le P (by includes) (by includes) _
      (.closure Decoder.oqRowC.lam1.costIdx [encodeValue b, σV])
      (fun i ↦ RunsApp.of_spec (Decoder.oqRowC.lam1.costSpec P (by includes) b σ σV hσ i))
      (2 * S + 33) s.I 16 h4 (by norm_num) (fun i hi ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
          Decoder.oqRowC.lam1.costEq P (by includes) b σ σV hσ, List.length_cons, List.length_cons,
          List.length_nil]
        have := hS (.n (b + i))
        limbs_one
        omega)
    have hfl := flatten_map_cost P (by includes) 2
      (fun j ↦ [(σ (.n (b + j))).limb 0, (σ (.n (b + j))).limb 1]) (List.range s.I) (by simp)
    rw [List.length_range] at hfl
    omega

omit hrd hR in
/-- A query's siblings (`oqSibsOfC`), `pd ≤ 24` levels: `(2·S + 120 + 28)·24 + 19`. -/
theorem oqSibsOf_cost (hP : Includes P Decoder.oqSibsOfC.costDeps) (pd ch q : ℕ)
    (hpd : pd ≤ 24) (hch : ch < 2 ^ 24) (hq : q < 2 ^ 64) :
    machineCost P Decoder.oqSibsOfC.costIdx
      [encodeValue pd, encodeValue ch, encodeValue q, σV] ≤ (2 * S + 120 + 28) * 24 + 19 := by
  rw [Decoder.oqSibsOfC.costEq P hP pd ch q σ σV hσ]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.oqSibsOfC.lam0.costIdx [encodeValue ch, encodeValue q, σV])
    (fun l ↦ RunsApp.of_spec (Decoder.oqSibsOfC.lam0.costSpec P (by includes) ch q
      σ σV hσ l))
    (2 * S + 120) pd 24 hpd (by norm_num) (fun l hl ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.oqSibsOfC.lam0.costEq P (by includes) ch q σ σV hσ, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := testBit_cost P (by includes) q l hq (by omega)
      split_ifs <;> limbs_one <;> cost_facts [digestOfCells640_cost P, hS] <;> omega)
  omega

omit hrd hR in
/-- A query's `walk_path` call's words (`oqWalkArgsC`): the leaf digest's two cells, the window
pointer, the cap and the flags: `2·S + 500`. -/
theorem oqWalkArgs_cost (hP : Includes P Decoder.oqWalkArgsC.costDeps) (s : Oq) (hs : OqOK s)
    (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) (bp cap flags : E) :
    machineCost P Decoder.oqWalkArgsC.costIdx [encodeValue s, encodeValue b, encodeValue emit,
      encodeValue bp, encodeValue cap, encodeValue flags, σV] ≤ 2 * S + 500 := by
  rw [Decoder.oqWalkArgsC.costEq P hP s b emit bp cap flags σ σV hσ]
  have hkl := oqKL_cost P hs (by includes) b hb emit
  have hkl' := oqKL_lt hs b hb emit
  have hB := Oq_B_cost P hs (by includes)
  have h0 := oqOut_cost P hs (by includes) (oqKL s b emit) hkl' 0 (by norm_num)
  have h1 := oqOut_cost P hs (by includes) (oqKL s b emit) hkl' 1 (by norm_num)
  have := hS (.n (oqOut s (oqKL s b emit) (s.B - 1) 0))
  have := hS (.n (oqOut s (oqKL s b emit) (s.B - 1) 1))
  have := hs.2.2.2.2.2.2.2.1
  limbs_one
  omega

omit hrd hR in
/-- The loop's arguments (`oqLoopArgsC`): `9·S + 109`. -/
theorem oqLoopArgs_cost (hP : Includes P Decoder.oqLoopArgsC.costDeps) :
    machineCost P Decoder.oqLoopArgsC.costIdx [σV] ≤ 9 * S + 109 := by
  rw [Decoder.oqLoopArgsC.costEq P hP σ σV hσ]
  have := hS (.n 7); have := hS (.n 5); have := hS (.n 6); have := hS (.n 0); have := hS (.n 1)
  have := hS (.n 3); have := hS (.n 4); have := hS (.n 10); have := hS (.n 2)
  omega

end Val

omit hrd hR in
theorem length_oqIterA (s : Oq) (lanes : List ℕ) (walk : ℕ) (rd : Reader) (σ : Val)
    (Vn : NFrames) : (oqIterA s lanes walk rd σ Vn).length ≤ 2 := by
  unfold oqIterA; split_ifs <;> simp

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

omit hrd hR hF in
/-- **A frame of the map, read a cell at a time** (the closure `oqQueryAtC.lam0` of the call
`k`, `a`, `r`): its value. -/
theorem frameAt_runs (hP : Includes P Decoder.oqQueryAtC.lam0.costDeps) (k : ℕ) (a r : List E)
    (v : V) :
    RunsApp P (.closure Decoder.oqQueryAtC.lam0.costIdx [encodeValue k, VnV, encodeValue a,
      encodeValue r]) [encodeValue v] (encodeValue (Vn k a r v)) :=
  RunsApp.of_spec (Decoder.oqQueryAtC.lam0.costSpec P hP k Vn VnV hVn _ _ v)

omit hrd hR in
/-- **A frame of the map, read a cell at a time**: at most `F + 10` a cell. -/
theorem frameAt_cost (hP : Includes P Decoder.oqQueryAtC.lam0.costDeps) (k : ℕ) (hk : k < 2 ^ 64) (a r : List E) (ha : a.length + r.length ≤ 16)
    (v : V) :
    appCost P (.closure Decoder.oqQueryAtC.lam0.costIdx [encodeValue k, VnV, encodeValue a,
      encodeValue r]) [encodeValue v] ≤ F + 10 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append, Decoder.oqQueryAtC.lam0.costEq P hP k Vn VnV hVn, List.length_cons,
    List.length_cons, List.length_cons, List.length_cons, List.length_nil]
  have := hF k a r v hk ha
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A query's price, its position given: its row off its frame, its siblings off its walk's. -/
@[expose] def queryAtPrice (S F : ℕ) : ℕ :=
  ((S + 42) * 64 + 25) + 1 + (2 * S + 500) + ((2 * (F + 10) + 120 + 28) * 24 + 19) + 32

omit hrd hR in
/-- **A query, its position `pos < 2^32` given** (`oqQueryAtC`), of a level's shape, from a value
below `2^21`, its walk `walk < 2^64`: at most `queryAtPrice S F`. -/
theorem oqQueryAt_cost (hP : Includes P Decoder.oqQueryAtC.costDeps) (s : Oq) (hs : OqOK s)
    (walk : ℕ) (hw : walk < 2 ^ 64) (bp cap flags : E) (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool)
    (pos : ℕ) (hpos : pos < 2 ^ 32) :
    machineCost P Decoder.oqQueryAtC.costIdx
      [encodeValue s, encodeValue walk, encodeValue bp, encodeValue cap, encodeValue flags, σV, VnV,
        encodeValue b, encodeValue emit, encodeValue pos] ≤ queryAtPrice S F := by
  rw [Decoder.oqQueryAtC.costEq P hP s walk bp cap flags σ σV hσ Vn VnV hVn]
  have hrow := oqRow_cost P hσ hS (by includes) s hs b hb
  have hwc := Decoder.wpChC.costEq P (by includes)
  have hwa := oqWalkArgs_cost P hσ hS (by includes) s hs b hb emit bp cap flags
  have hsib := oqSibsOf_cost P (frameAt_runs P hVn (by includes) walk (oqWalkArgs s b emit bp cap flags σ) [])
    (frameAt_cost P hVn hF (by includes) walk hw (oqWalkArgs s b emit bp cap flags σ) [] (by simp [oqWalkArgs]))
    (by includes) s.pd wpCh pos hs.2.2.1 (by unfold wpCh; norm_num) (by omega)
  unfold queryAtPrice
  omega

/-- A query's price. -/
@[expose] def queryPrice (R S F : ℕ) : ℕ := posPrice R + queryAtPrice S F + 40

/-- **A query** (`oqQueryAC`), its position read once off its windows: at most
`queryPrice R S F`. -/
theorem oqQueryA_cost (hP : Includes P Decoder.oqQueryAC.costDeps) (s : Oq) (hs : OqOK s)
    (lanes : List ℕ) (hl : ∀ x ∈ lanes, x < 2 ^ 64) (walk : ℕ) (hw : walk < 2 ^ 64)
    (bp cap flags : E) (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Decoder.oqQueryAC.costIdx
      [encodeValue s, encodeValue lanes, encodeValue walk, rdV, encodeValue bp, encodeValue cap,
        encodeValue flags, encodeValue b, encodeValue emit, σV, VnV] ≤ queryPrice R S F := by
  rw [Decoder.oqQueryAC.costEq P hP s lanes walk rd rdV hrd bp cap flags b emit σ σV hσ Vn VnV hVn]
  have h3 : s.pd ≤ 24 := hs.2.2.1
  have h4 : s.cd ≤ 8 := hs.2.2.2.1
  have hw' : qwN (s.pd + s.cd) s.cd ≤ 6 := by unfold qwN qwNp; omega
  have hp := winPosOfW_cost P hrd hR (by includes) lanes hl bp (s.pd + s.cd) s.cd (by omega) h4 hw'
  have hlt := winPosAt_lt (winLogsFrom lanes rd (bp.limb 0) (qwN (s.pd + s.cd) s.cd))
    (s.pd + s.cd) s.cd
  have : 2 ^ (s.pd + s.cd) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq := oqQueryAt_cost P hVn hF hσ hS (by includes) s hs walk hw bp cap flags b hb emit
    (winPosOfW lanes rd bp (s.pd + s.cd) s.cd) (by unfold winPosOfW; omega)
  rw [limbs_of_lt (by omega : s.pd < 2 ^ 64), limbs_of_lt (by omega : s.cd < 2 ^ 64),
    limbs_of_lt (by omega : s.pd + s.cd < 2 ^ 64)]
  unfold queryPrice
  omega

/-- An iteration's price. -/
@[expose] def iterPrice (R S F : ℕ) : ℕ := 2 * queryPrice R S F + 6 * S + 2080

/-- **A loop iteration's queries** (`oqIterAC`): at most `iterPrice R S F`. -/
theorem oqIterA_cost (hP : Includes P Decoder.oqIterAC.costDeps) (s : Oq) (hs : OqOK s)
    (lanes : List ℕ) (hl : ∀ x ∈ lanes, x < 2 ^ 64) (walk : ℕ) (hw : walk < 2 ^ 64) :
    machineCost P Decoder.oqIterAC.costIdx
      [encodeValue s, encodeValue lanes, encodeValue walk, rdV, σV, VnV] ≤ iterPrice R S F := by
  rw [Decoder.oqIterAC.costEq P hP s lanes walk rd rdV hrd σ σV hσ Vn VnV hVn]
  have hE := oqE1_lt hs
  have q1 := oqQueryA_cost P hrd hR hVn hF hσ hS (by includes) s hs lanes hl walk hw (σ (.n 15))
    (σ (.n 4)) (σ (.n 5)) 16 (by norm_num) true
  have q2 := oqQueryA_cost P hrd hR hVn hF hσ hS (by includes) s hs lanes hl walk hw
    (σ (.n (oqE1 s + 1))) (σ (.n 4)) (σ (.n 5)) (oqE1 s + 2) (by omega) false
  have q3 := oqQueryA_cost P hrd hR hVn hF hσ hS (by includes) s hs lanes hl walk hw (σ (.n 13))
    (σ (.n 4)) (σ (.n 5)) 14 (by norm_num) true
  have := hS (.n 15); have := hS (.n 13); have := hS (.n (oqE1 s + 1)); have := hS (.n 4)
  have := hS (.n 5)
  have hb := hs.1
  unfold iterPrice
  limbs_one
  split_ifs with h1
  · have e1 := oqE1_cost P hs (by includes) h1
    omega
  · omega

end Val

/-- An iteration of the loop, its frame stepped: its price. -/
@[expose] def stepPrice (R F : ℕ) : ℕ := iterPrice R (F + 10) F + 420

/-- **The loop's `N` iterations from the frame at `x`** (`oqItersFromC`), each the next at
`x·g`: at most `stepPrice R F · N + 5`. -/
theorem oqItersFrom_cost (hP : Includes P Decoder.oqItersFromC.costDeps) (s : Oq) (hs : OqOK s)
    (lanes : List ℕ) (hl : ∀ x ∈ lanes, x < 2 ^ 64)
    (loop : ℕ) (hloop : loop < 2 ^ 64) (walk : ℕ) (hw : walk < 2 ^ 64) (la : List E)
    (hla : la.length ≤ 15) :
    ∀ (N : ℕ) (x : E), N < 2 ^ 64 →
      machineCost P Decoder.oqItersFromC.costIdx [encodeValue s, encodeValue lanes,
        encodeValue loop, encodeValue walk, rdV, VnV, encodeValue la, encodeValue N, encodeValue x] ≤
          stepPrice R F * N + 5
  | 0, x, _ => by
    rw [Decoder.oqItersFromC.costEq_zero P hP s lanes loop walk rd rdV hrd Vn VnV hVn]; omega
  | N + 1, x, hN => by
    rw [Decoder.oqItersFromC.costEq_succ P hP s lanes loop walk rd rdV hrd Vn VnV hVn,
      limbs_of_lt hN]
    have hi := oqIterA_cost P hrd hR hVn hF (frameAt_runs P hVn (by includes) loop (x :: la) [])
      (frameAt_cost P hVn hF (by includes) loop hloop (x :: la) [] (by simp; omega)) (by includes) s hs lanes hl
      walk hw
    have := oqItersFrom_cost hP s hs lanes hl loop hloop walk hw la hla N
      (x * LeanVM.Protocol.Verifier.gen) (by omega)
    have ha := append_cost P (by includes) (oqIterA s lanes walk rd (Vn loop (x :: la) []) Vn)
      (oqItersFrom s lanes loop walk rd Vn la N (x * LeanVM.Protocol.Verifier.gen))
    have := length_oqIterA s lanes walk rd (Vn loop (x :: la) []) Vn
    unfold stepPrice at *
    rw [Nat.mul_succ]
    omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- The queries' price. -/
@[expose] def oqsPrice (R S F : ℕ) : ℕ :=
  1 + (3 * S + queryPrice R S F + 19) + (9 * S + 109) + (stepPrice R F * 112 + 5) + 14 + 140

/-- **The queries of `opening_queries`** (`oqsOfNC`, `oqsOfA`), its odd query and `N ≤ 112`
iterations: at most `oqsPrice R S F`. -/
theorem oqsOfA_cost (hP : Includes P Decoder.oqsOfNC.costDeps) (s : Oq) (hs : OqOK s)
    (lanes : List ℕ) (hl : ∀ x ∈ lanes, x < 2 ^ 64)
    (odd loop walk N : ℕ) (hodd : odd ≤ 1) (hN : N ≤ 112) (hloop : loop < 2 ^ 64)
    (hw : walk < 2 ^ 64) :
    machineCost P Decoder.oqsOfNC.costIdx [encodeValue s, encodeValue lanes, encodeValue odd,
      encodeValue loop, encodeValue walk, encodeValue N, rdV, σV, VnV] ≤ oqsPrice R S F := by
  rw [Decoder.oqsOfNC.costEq P hP s lanes odd loop walk N rd rdV hrd σ σV hσ Vn VnV hVn]
  have q := oqQueryA_cost P hrd hR hVn hF hσ hS (by includes) s hs lanes hl walk hw (σ (.n 12))
    (σ (.n 0)) (σ (.n 1)) 13 (by norm_num) true
  have := hS (.n 12); have := hS (.n 0); have := hS (.n 1)
  have := oqLoopArgs_cost P hσ hS (by includes)
  have hi := oqItersFrom_cost P hrd hR hVn hF (by includes) s hs lanes hl loop hloop walk hw
    (oqLoopArgs σ) (by simp [oqLoopArgs]) N 1 (by omega)
  have := Nat.mul_le_mul_left (stepPrice R F) hN
  unfold oqsPrice
  rw [limbs_of_lt (by omega : odd < 2 ^ 64)]
  split_ifs
  · have ha := append_cost P (by includes)
      [oqQueryA s lanes walk rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ Vn]
      (oqItersFrom s lanes loop walk rd Vn (oqLoopArgs σ) N 1)
    simp only [List.length_cons, List.length_nil] at ha
    omega
  · have ha := append_cost P (by includes) ([] : List QW)
      (oqItersFrom s lanes loop walk rd Vn (oqLoopArgs σ) N 1)
    simp only [List.length_nil] at ha
    omega

end Val

end Frames

/-! ## The queries' values -/

omit hrd hR in
theorem oqQueryA_facts (s : Oq) (lanes : List ℕ) (walk : ℕ) (bp cap flags : E) (b : ℕ)
    (emit : Bool) (σ : Val) (Vn : NFrames) :
    (oqQueryA s lanes walk rd bp cap flags b emit σ Vn).1 < 2 ^ (s.pd + s.cd) ∧
      (oqQueryA s lanes walk rd bp cap flags b emit σ Vn).2.2.length = s.pd := by
  unfold oqQueryA oqQueryAt oqSibsOf winPosOfW
  exact ⟨winPosAt_lt _ _ _, by simp⟩

omit hrd hR in
theorem mem_oqItersFrom {s : Oq} {lanes : List ℕ} {loop walk : ℕ} {Vn : NFrames} {la : List E}
    {w : QW} : ∀ {N : ℕ} {x : E}, w ∈ oqItersFrom s lanes loop walk rd Vn la N x →
      w.1 < 2 ^ (s.pd + s.cd) ∧ w.2.2.length = s.pd
  | 0, _, h => by simp [oqItersFrom] at h
  | N + 1, x, h => by
    rw [oqItersFrom, List.mem_append] at h
    rcases h with h | h
    · unfold oqIterA at h
      split_ifs at h
      · rcases List.mem_pair.1 h with rfl | rfl <;> exact oqQueryA_facts _ _ _ _ _ _ _ _ _ _
      · rw [List.mem_singleton] at h; subst h; exact oqQueryA_facts _ _ _ _ _ _ _ _ _ _
    · exact mem_oqItersFrom h

omit hrd hR in
theorem mem_oqsOfA {s : Oq} {lanes : List ℕ} {odd loop walk N : ℕ} {σ : Val} {Vn : NFrames}
    {w : QW} (h : w ∈ oqsOfA s lanes odd loop walk N rd σ Vn) :
    w.1 < 2 ^ (s.pd + s.cd) ∧ w.2.2.length = s.pd := by
  unfold oqsOfA at h
  rcases List.mem_append.1 h with h | h
  · split_ifs at h
    · rw [List.mem_singleton] at h; subst h; exact oqQueryA_facts _ _ _ _ _ _ _ _ _ _
    · simp at h
  · exact mem_oqItersFrom h

omit hrd hR in
theorem length_oqItersFrom (s : Oq) (lanes : List ℕ) (loop walk : ℕ) (Vn : NFrames)
    (la : List E) :
    ∀ (N : ℕ) (x : E), (oqItersFrom s lanes loop walk rd Vn la N x).length ≤ 2 * N
  | 0, _ => by simp [oqItersFrom]
  | N + 1, x => by
    rw [oqItersFrom, List.length_append]
    have := length_oqIterA s lanes walk rd (Vn loop (x :: la) []) Vn
    have := length_oqItersFrom s lanes loop walk Vn la N (x * LeanVM.Protocol.Verifier.gen)
    omega

omit hrd hR in
theorem length_oqsOfA (s : Oq) (lanes : List ℕ) (odd loop walk N : ℕ) (σ : Val) (Vn : NFrames) :
    (oqsOfA s lanes odd loop walk N rd σ Vn).length ≤ 1 + 2 * N := by
  unfold oqsOfA
  rw [List.length_append]
  have := length_oqItersFrom (rd := rd) s lanes loop walk Vn (oqLoopArgs σ) N 1
  split_ifs <;> simp only [List.length_cons, List.length_nil] <;> omega

omit hrd hR in
theorem length_flatMap_le {α β : Type} (f : α → List β) (M : ℕ) (hf : ∀ a, (f a).length ≤ M) :
    ∀ l : List α, (l.flatMap f).length ≤ M * l.length
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have := length_flatMap_le f M hf l
    have := hf a
    omega

/-! ## A query's opening -/

omit hrd hR in
theorem capSib_le (D p j : ℕ) (hD : D ≤ 8) : Whir.capSib D p j ≤ 2 ^ 8 + p + 1 := by
  unfold Whir.capSib
  have : 2 ^ (D - j) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : p / 2 ^ j ≤ p := Nat.div_le_self _ _
  split_ifs <;> omega

omit hrd hR in
/-- A cap sibling's index (`capSibC`), `D ≤ 8`, `p < 2^32`: at most `23`. -/
theorem capSib_cost (hP : Includes P Decoder.capSibC.costDeps) (D p j : ℕ)
    (hD : D ≤ 8) (hj : j < 8) (hp : p < 2 ^ 32) :
    machineCost P Decoder.capSibC.costIdx
      [encodeValue D, encodeValue p, encodeValue j] ≤ 23 := by
  rw [Decoder.capSibC.costEq P hP]
  simp only [Nat.one_shiftLeft]
  have : 2 ^ (D - j) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ j ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : p / 2 ^ j ≤ p := Nat.div_le_self _ _
  limbs_one
  split_ifs <;> omega

/-- The cap's siblings (`capSibsOfC`), `D ≤ 8` levels, `p < 2^32`: `(2·R + 6095)·8 + 21`. -/
theorem capSibsOf_cost (hP : Includes P Decoder.capSibsOfC.costDeps) (cap : E)
    (D p : ℕ) (hD : D ≤ 8) (hp : p < 2 ^ 32) :
    machineCost P Decoder.capSibsOfC.costIdx
      [rdV, encodeValue cap, encodeValue D, encodeValue p] ≤ (2 * R + 6067 + 28) * 8 + 21 := by
  rw [Decoder.capSibsOfC.costEq P hP rd rdV hrd]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.capSibsOfC.lam0.costIdx
      [rdV, encodeValue cap, encodeValue D, encodeValue p])
    (fun j ↦ RunsApp.of_spec (Decoder.capSibsOfC.lam0.costSpec P
      (by includes) rd rdV hrd cap D p j))
    (2 * R + 6067) D 8 hD (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append,
        Decoder.capSibsOfC.lam0.costEq P (by includes) rd rdV hrd, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := capSib_cost P (by includes) D p j hD (by omega) hp
      have := capSib_le D p j hD
      have := memRead_cost P hrd hR (by includes) cap (2 * Whir.capSib D p j) (by omega)
      have := memRead_cost P hrd hR (by includes) cap (2 * Whir.capSib D p j + 1) (by omega)
      have := digestOfCells640_cost P (by includes) (memRead rd cap (2 * Whir.capSib D p j))
        (memRead rd cap (2 * Whir.capSib D p j + 1))
      limbs_one
      omega)
  omega

/-- A query's opening's price. -/
@[expose] def openingPrice (R : ℕ) : ℕ := (2 * R + 6067 + 28) * 8 + 21 + 297

/-- **A query's opening** (`toOpeningC`), of a level of depth at most `32`, cap depth at most
`8`, the query's position below `2^32` and its siblings at most `24`: `openingPrice R`. -/
theorem toOpening_cost (hP : Includes P Decoder.toOpeningC.costDeps) (cap : E)
    (cd depth : ℕ) (w : QW) (hcd : cd ≤ 8) (hdepth : depth ≤ 32) (hw : w.1 < 2 ^ 32)
    (hw2 : w.2.2.length ≤ 24) :
    machineCost P Decoder.toOpeningC.costIdx
      [rdV, encodeValue cap, encodeValue cd, encodeValue depth, encodeValue w] ≤ openingPrice R := by
  rw [Decoder.toOpeningC.costEq P hP rd rdV hrd]
  simp only [Nat.one_shiftLeft]
  have : 2 ^ (depth - cd) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd : w.1 / 2 ^ (depth - cd) ≤ w.1 := Nat.div_le_self _ _
  have := capSibsOf_cost P hrd hR (by includes) cap cd (w.1 / 2 ^ (depth - cd)) hcd (by omega)
  have := append_cost P (by includes) w.2.2 (Whir.capSibsOf rd cap cd (w.1 / 2 ^ (depth - cd)))
  unfold openingPrice
  limbs_one
  omega

section Val2

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hσ hS hVn hF

/-- A level's price, the `level_queries` callee's frame `fr` (at most `S` a word) and its
`opening_queries` call's argument words given. -/
@[expose] def levelAtPrice (R S F : ℕ) : ℕ :=
  2 * S + 2 * shapePrice + 28 + oqsPrice R (F + 10) F + ((openingPrice R + 10 + 13) * 225 + 3) +
    100

/-- **A level's openings, the `level_queries` callee's frame `fr` (here `σ`) and its
`opening_queries` call's words `a` given** (`levelOsAtC`), from a dispatch of the table: at most
`levelAtPrice R S F`. -/
theorem levelOsAt_cost (hP : Includes P Decoder.levelOsAtC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (c : OsCall) (hc : CallOK c) (a : List E) (ha : a.length ≤ 8) :
    machineCost P Decoder.levelOsAtC.costIdx
      [encodeValue lanes, rdV, σV, VnV, encodeValue c, encodeValue a] ≤ levelAtPrice R S F := by
  obtain ⟨hs, hodd, hN, hfn, hloop, hwalk, hdepth, -, -, hccd, hsh, hshd, hshcd, -⟩ := hc
  rw [Decoder.levelOsAtC.costEq P hP lanes rd rdV hrd σ σV hσ Vn VnV hVn]
  have := osCallShape_cost P (by includes) c (by omega)
  have := oqShapeOq_cost P (by includes) c.shape hshd hshcd
  have := hS (.n 13)
  have := hS (.n 7)
  have hσ'' : ∀ v : V, RunsApp P (.closure Decoder.levelOsAtC.lam1.costIdx
      [VnV, encodeValue a, encodeValue [σ (.n 13)], encodeValue c.fn])
      [encodeValue v] (encodeValue (Vn c.fn a [σ (.n 13)] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.levelOsAtC.lam1.costSpec P (by includes) Vn VnV hVn _ _ _ v)
  have hS'' : ∀ v : V, appCost P (.closure Decoder.levelOsAtC.lam1.costIdx
      [VnV, encodeValue a, encodeValue [σ (.n 13)], encodeValue c.fn])
      [encodeValue v] ≤ F + 10 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.levelOsAtC.lam1.costEq P (by includes) Vn VnV hVn, List.length_cons,
      List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := hF c.fn a [σ (.n 13)] v (by omega) (by simp; omega)
    omega
  have ho := oqsOfA_cost P hrd hR hVn hF hσ'' hS'' (by includes) _ hs lanes hl c.shape.odd c.loop
    c.walk c.N hodd (by omega) (by omega) (by omega)
  have hlen := length_oqsOfA (rd := rd) c.shape.oq lanes c.shape.odd c.loop c.walk c.N
    (Vn c.fn a [σ (.n 13)]) Vn
  have m3 := map_cost P (by includes) _
    (.closure Decoder.levelOsAtC.lam0.costIdx [rdV, encodeValue (σ (.n 7)), encodeValue c.depth,
      encodeValue c.cd])
    (fun w ↦ RunsApp.of_spec (Decoder.levelOsAtC.lam0.costSpec P (by includes) rd rdV hrd _ _ _ w))
    (openingPrice R + 10) (oqsOfA c.shape.oq lanes c.shape.odd c.loop c.walk c.N rd
      (Vn c.fn a [σ (.n 13)]) Vn) (fun w hw ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.levelOsAtC.lam0.costEq P (by includes) rd rdV hrd, List.length_cons,
        List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      obtain ⟨hw1, hw2⟩ := mem_oqsOfA hw
      have h4 : c.shape.oq.cd ≤ 8 := hs.2.2.2.1
      have h3 : c.shape.oq.pd ≤ 24 := hs.2.2.1
      have : 2 ^ (c.shape.oq.pd + c.shape.oq.cd) ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have := toOpening_cost P hrd hR (by includes) (σ (.n 7)) c.cd c.depth w hccd (by omega)
        (lt_of_lt_of_le hw1 this) (by rw [hw2]; exact h3)
      omega)
  have := Nat.mul_le_mul_left (openingPrice R + 10 + 13) (hlen.trans (by omega : 1 + 2 * c.N ≤ 225))
  unfold levelAtPrice
  omega

/-- The price of the `opening_queries` call's argument words (`oqCallArgsC`): the callee's two
words, the dispatch's five, `g^N` in `K`. -/
@[expose] def oqCallArgsPrice (S : ℕ) : ℕ := 2 * S + 5 * 99 + (5 + 73 * 7) + 92

omit hrd hR hVn hF in
/-- **The `opening_queries` call's argument words** (`oqCallArgsC`), the dispatch's words `A` at
most `6`, `N < 2^7`: at most `oqCallArgsPrice S`. -/
theorem oqCallArgs_cost (hP : Includes P Decoder.oqCallArgsC.costDeps) (A : List E)
    (hA : A.length ≤ 6) (N : ℕ) (hN : N < 2 ^ 7) :
    machineCost P Decoder.oqCallArgsC.costIdx [σV, encodeValue A, encodeValue N] ≤
      oqCallArgsPrice S := by
  rw [Decoder.oqCallArgsC.costEq P hP σ σV hσ]
  have := hS (.n 7)
  have := hS (.n 9)
  have := powSqK_cost_lt P (by includes) Parameters.g N 7 (by norm_num) (by norm_num) hN
  have := getD_cost P (by includes) A 1 (0 : E) (by norm_num)
  have := getD_cost P (by includes) A 2 (0 : E) (by norm_num)
  have := getD_cost P (by includes) A 3 (0 : E) (by norm_num)
  have := getD_cost P (by includes) A 4 (0 : E) (by norm_num)
  have := getD_cost P (by includes) A 5 (0 : E) (by norm_num)
  unfold oqCallArgsPrice
  omega

omit hrd hR hσ hS hVn hF in
theorem length_oqCallArgs (fr : Val) (A : List E) (N : ℕ) : (oqCallArgs fr A N).length = 8 := rfl

/-- A level's price, the dispatch's words and the `level_queries` callee's frame given. -/
@[expose] def levelQPrice (R S F : ℕ) : ℕ := oqCallArgsPrice S + levelAtPrice R S F + 30

/-- **A level's openings, the dispatch's words `A` and the `level_queries` callee's frame `fr`
(here `σ`) given** (`levelOsQC`): the `opening_queries` call's words, then `levelOsAtC`: at most
`levelQPrice R S F`. -/
theorem levelOsQ_cost (hP : Includes P Decoder.levelOsQC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (A : List E) (hA : A.length ≤ 6) (c : OsCall) (hc : CallOK c) :
    machineCost P Decoder.levelOsQC.costIdx
      [encodeValue lanes, rdV, encodeValue A, σV, VnV, encodeValue c] ≤ levelQPrice R S F := by
  rw [Decoder.levelOsQC.costEq P hP lanes rd rdV hrd A σ σV hσ Vn VnV hVn]
  have := oqCallArgs_cost P hσ hS (by includes) A hA c.N (by have := hc.2.2.1; omega)
  have := levelOsAt_cost P hrd hR hσ hS hVn hF (by includes) lanes hl c hc (oqCallArgs σ A c.N)
    (by rw [length_oqCallArgs])
  unfold levelQPrice
  omega

end Val2

section Val3

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hσ hS hVn hF

/-- A level's price, the dispatch's words given. -/
@[expose] def levelFPrice (R S F : ℕ) : ℕ := ((S + 10 + 13) * 4 + 3) + levelQPrice R (F + 10) F + 30

/-- **A level's openings, the dispatch's words `A` given** (`levelOsFC`): the `level_queries`
callee's frame read once, then `levelOsQC`: at most `levelFPrice R S F`. -/
theorem levelOsF_cost (hP : Includes P Decoder.levelOsFC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (c : OsCall) (hc : CallOK c) (A : List E) (hA : A.length ≤ 6) :
    machineCost P Decoder.levelOsFC.costIdx
      [encodeValue lanes, rdV, σV, VnV, encodeValue c, encodeValue A] ≤ levelFPrice R S F := by
  rw [Decoder.levelOsFC.costEq P hP lanes rd rdV hrd σ σV hσ Vn VnV hVn]
  have hrets : c.rets.length ≤ 4 := hc.2.2.2.2.2.2.2.2.1
  have hlq : c.lq < 2 ^ 20 := hc.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hl0 : ∀ k : ℕ, appCost P (.closure Decoder.levelOsFC.lam0.costIdx [σV]) [encodeValue k] ≤
      S + 10 := fun k ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.levelOsFC.lam0.costEq P (by includes) σ σV hσ, List.length_cons, List.length_nil]
    have := hS (.n k); omega
  have hr0 : ∀ k : ℕ, RunsApp P (.closure Decoder.levelOsFC.lam0.costIdx [σV]) [encodeValue k]
      (encodeValue (σ (.n k))) :=
    fun k ↦ RunsApp.of_spec (Decoder.levelOsFC.lam0.costSpec P (by includes) σ σV hσ k)
  have m1 := map_cost P (by includes) _ _ hr0 (S + 10) c.rets (fun k _ ↦ hl0 k)
  have := Nat.mul_le_mul_left (S + 10 + 13) hrets
  have hfr : ∀ v : V, RunsApp P (.closure Decoder.levelOsAtC.lam1.costIdx
      [VnV, encodeValue A, encodeValue (c.rets.map fun k ↦ σ (.n k)), encodeValue c.lq])
      [encodeValue v] (encodeValue (Vn c.lq A (c.rets.map fun k ↦ σ (.n k)) v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.levelOsAtC.lam1.costSpec P (by includes) Vn VnV hVn _ _ _ v)
  have hfrS : ∀ v : V, appCost P (.closure Decoder.levelOsAtC.lam1.costIdx
      [VnV, encodeValue A, encodeValue (c.rets.map fun k ↦ σ (.n k)), encodeValue c.lq])
      [encodeValue v] ≤ F + 10 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.levelOsAtC.lam1.costEq P (by includes) Vn VnV hVn, List.length_cons,
      List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := hF c.lq A (c.rets.map fun k ↦ σ (.n k)) v (by omega)
      (by simp only [List.length_map]; omega)
    omega
  have := levelOsQ_cost P hrd hR hfr hfrS hVn hF (by includes) lanes hl A hA c hc
  unfold levelFPrice
  omega

/-- A level's price. -/
@[expose] def levelPrice (R S F : ℕ) : ℕ := ((S + 10 + 13) * 6 + 3) + levelFPrice R S F + 20

/-- **A level's openings** (`levelOsNC`, `levelOsA`), its dispatch's words read once: at most
`levelPrice R S F`. -/
theorem levelOsA_cost (hP : Includes P Decoder.levelOsNC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (c : OsCall) (hc : CallOK c) :
    machineCost P Decoder.levelOsNC.costIdx [encodeValue lanes, rdV, σV, VnV, encodeValue c] ≤
      levelPrice R S F := by
  rw [Decoder.levelOsNC.costEq P hP lanes rd rdV hrd σ σV hσ Vn VnV hVn]
  have hargs : c.args.length ≤ 6 := hc.2.2.2.2.2.2.2.1
  have hl0 : ∀ k : ℕ, appCost P (.closure Decoder.levelOsFC.lam0.costIdx [σV]) [encodeValue k] ≤
      S + 10 := fun k ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.levelOsFC.lam0.costEq P (by includes) σ σV hσ, List.length_cons, List.length_nil]
    have := hS (.n k); omega
  have hr0 : ∀ k : ℕ, RunsApp P (.closure Decoder.levelOsFC.lam0.costIdx [σV]) [encodeValue k]
      (encodeValue (σ (.n k))) :=
    fun k ↦ RunsApp.of_spec (Decoder.levelOsFC.lam0.costSpec P (by includes) σ σV hσ k)
  have m := map_cost P (by includes) _ _ hr0 (S + 10) c.args (fun k _ ↦ hl0 k)
  have := Nat.mul_le_mul_left (S + 10 + 13) hargs
  have := levelOsF_cost P hrd hR hσ hS hVn hF (by includes) lanes hl c hc
    (c.args.map fun k ↦ σ (.n k)) (by rw [List.length_map]; exact hargs)
  unfold levelPrice
  omega

end Val3

omit hrd hR in
theorem length_levelOsA (lanes : List ℕ) (σ : Val) (Vn : NFrames) (c : OsCall) (hc : CallOK c) :
    (levelOsA lanes rd σ Vn c).length ≤ 225 := by
  unfold levelOsA levelOsF levelOsQ levelOsAt
  rw [List.length_map]
  have := length_oqsOfA (rd := rd) c.shape.oq lanes c.shape.odd c.loop c.walk c.N
    (Vn c.fn (oqCallArgs (Vn c.lq (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k)))
      (c.args.map fun k ↦ σ (.n k)) c.N)
      [Vn c.lq (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k)) (.n 13)]) Vn
  have := hc.2.2.1
  omega

section Proof

variable {σ : Val} {σV : MachineValue}
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
  {L : ℕ} (hL : cl (σ (.n 25)) (σ (.n 1919)) ≤ L) (hL32 : L ≤ 2 ^ 32)
include hσ hS hVn hF hcl hC hL hL32

omit hrd hR hVn hF hcl hC hL hL32 in
theorem vsOsArgs_cost (hP : Includes P Decoder.vsOsArgsC.costDeps) :
    machineCost P Decoder.vsOsArgsC.costIdx [σV] ≤ 11 * S + 133 := by
  rw [Decoder.vsOsArgsC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

omit hrd hR hVn hF hcl hC hL hL32 in
theorem vsOsRets_cost (hP : Includes P Decoder.vsOsRetsC.costDeps) :
    machineCost P Decoder.vsOsRetsC.costIdx [σV] ≤ 5 * S + 61 := by
  rw [Decoder.vsOsRetsC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

/-- A child proof's price, the index of its size and rate and `open_stacked`'s frame given. -/
@[expose] def vsAtPrice (R S F C L : ℕ) : ℕ :=
  3 * S + C + ((R + 56) * L + 5) + (F + 10) + ((R + 56) * 206 + 5) + (11 * L + 3) +
    ((levelPrice R (F + 10) F + 20 + 13) * 6 + 3) + 70

/-- **A child's proof, the index `j` of its size and rate and the frame `fr` of its
`open_stacked` call given** (`vsPiOfAtC`), the frame of price at most `F + 10`: at most
`vsAtPrice R S F C L`. -/
theorem vsPiOfAt_cost (hP : Includes P Decoder.vsPiOfAtC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOK T) (j : ℕ) {fr : Val} {frV : MachineValue}
    (hfr : ∀ v : V, RunsApp P frV [encodeValue v] (encodeValue (fr v)))
    (hfrS : ∀ v : V, appCost P frV [encodeValue v] ≤ F + 10) :
    machineCost P Decoder.vsPiOfAtC.costIdx
      [encodeValue T, rdV, σV, VnV, clV, encodeValue j, frV] ≤ vsAtPrice R S F C L := by
  rw [Decoder.vsPiOfAtC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl j fr frV hfr]
  have := hS (.n 25); have := hS (.n 1919); have := hfrS (.n 9)
  have := hC (σ (.n 25)) (σ (.n 1919))
  have hl := hL
  have hw1 := wordsFrom_cost P hrd hR (by includes) (cl (σ (.n 25)) (σ (.n 1919)))
    ((σ (.n 25)).limb 0) (by omega)
  have := Nat.mul_le_mul_left (R + 56) hl
  have hwd := hT.words j
  have hw2 := wordsFrom_cost P hrd hR (by includes) (T.words.getD j 0) ((fr (.n 9)).limb 0)
    (by omega)
  have := Nat.mul_le_mul_left (R + 56) hwd
  have ha := append_cost P (by includes)
    (wordsFrom rd ((σ (.n 25)).limb 0) (cl (σ (.n 25)) (σ (.n 1919))))
    (wordsFrom rd ((fr (.n 9)).limb 0) (T.words.getD j 0))
  rw [length_wordsFrom] at ha
  obtain ⟨hcl7, hcok⟩ := hT.calls j
  have hm := map_cost P (by includes) _
    (.closure Decoder.vsPiOfAtC.lam0.costIdx [rdV, VnV, frV, encodeValue T.lanes])
    (fun c ↦ RunsApp.of_spec (Decoder.vsPiOfAtC.lam0.costSpec P (by includes) rd rdV hrd Vn VnV hVn
      fr frV hfr T.lanes c))
    (levelPrice R (F + 10) F + 20) (T.calls.getD j []) (fun c hc ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.vsPiOfAtC.lam0.costEq P (by includes) rd rdV hrd Vn VnV hVn fr frV
        hfr, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := levelOsA_cost P hrd hR hfr hfrS hVn hF (by includes) T.lanes hT.lanes c (hcok c hc)
      omega)
  have := Nat.mul_le_mul_left (levelPrice R (F + 10) F + 20 + 13) hcl7
  unfold vsAtPrice
  omega

/-- A child proof's price, its size and the index of its size and rate given. -/
@[expose] def vsMPrice (R S F C L : ℕ) : ℕ :=
  (5 * S + 61) + 1 + (11 * S + 133) + vsAtPrice R S F C L + 19

/-- **A child's proof, its size `m` and the index `j` of its size and rate given**
(`vsPiOfMC`): the frame of `open_stacked__L{m}`'s call read once: at most
`vsMPrice R S F C L`. -/
theorem vsPiOfM_cost (hP : Includes P Decoder.vsPiOfMC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOK T) (m : ℕ) (j : ℕ) (hm : m < 2 ^ 32) :
    machineCost P Decoder.vsPiOfMC.costIdx
      [encodeValue T, rdV, σV, VnV, clV, encodeValue m, encodeValue j] ≤ vsMPrice R S F C L := by
  rw [Decoder.vsPiOfMC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl m j,
    limbs_of_lt (by omega : m < 2 ^ 64), limbs_of_lt (by omega : 336 + m < 2 ^ 64)]
  have hfr : ∀ v : V, RunsApp P (.closure Decoder.vsPiOfMC.lam0.costIdx
      [VnV, encodeValue (VerifySub.vsOsRets σ), encodeValue (openStackedIdx m),
        encodeValue (VerifySub.vsOsArgs σ)]) [encodeValue v]
      (encodeValue (Vn (openStackedIdx m) (VerifySub.vsOsArgs σ) (VerifySub.vsOsRets σ) v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.vsPiOfMC.lam0.costSpec P (by includes) Vn VnV hVn _ _ _ v)
  have hfrS : ∀ v : V, appCost P (.closure Decoder.vsPiOfMC.lam0.costIdx
      [VnV, encodeValue (VerifySub.vsOsRets σ), encodeValue (openStackedIdx m),
        encodeValue (VerifySub.vsOsArgs σ)]) [encodeValue v] ≤ F + 10 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.vsPiOfMC.lam0.costEq P (by includes) Vn VnV hVn, List.length_cons,
      List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := hF (openStackedIdx m) (VerifySub.vsOsArgs σ) (VerifySub.vsOsRets σ) v
      (by unfold openStackedIdx; omega) (by simp [VerifySub.vsOsArgs, VerifySub.vsOsRets])
    omega
  have := vsPiOfAt_cost P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) T hT j hfr hfrS
  have := vsOsArgs_cost P hσ hS (by includes)
  have := vsOsRets_cost P hσ hS (by includes)
  unfold vsMPrice
  omega

/-- A child proof's price, its size given. -/
@[expose] def vsSPrice (R S F C L : ℕ) : ℕ := S + 117 + 2 + vsMPrice R S F C L + 22

/-- **A child's proof, its size `m < 2^32` given** (`vsPiOfSC`): the rate read once, then
`vsPiOfMC` at the index of the size and rate: at most `vsSPrice R S F C L`. -/
theorem vsPiOfS_cost (hP : Includes P Decoder.vsPiOfSC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOK T) (m : ℕ) (hm : m < 2 ^ 32) :
    machineCost P Decoder.vsPiOfSC.costIdx [encodeValue T, rdV, σV, VnV, clV, encodeValue m] ≤
      vsSPrice R S F C L := by
  rw [Decoder.vsPiOfSC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl m]
  have := hS (.n 66)
  have := logGTWith_cost P (by includes) T.lanes hT.lanes (σ (.n 66)) 4 (by norm_num)
  have hr := logGTWith_le T.lanes (σ (.n 66)) 4
  have := vsPiOfM_cost P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) T hT m
    (logGTWith T.lanes (σ (.n 66)) 4 * 11 + m) hm
  rw [limbs_of_lt (by omega : logGTWith T.lanes (σ (.n 66)) 4 * 11 < 2 ^ 64),
    limbs_of_lt (by omega : logGTWith T.lanes (σ (.n 66)) 4 < 2 ^ 64),
    limbs_of_lt (by omega : logGTWith T.lanes (σ (.n 66)) 4 * 11 + m < 2 ^ 64),
    limbs_of_lt (by omega : m < 2 ^ 64)]
  unfold vsSPrice
  omega

/-- A child proof's price. -/
@[expose] def vsPiPrice (R S F C L : ℕ) : ℕ := S + 347 + vsSPrice R S F C L + 19

/-- **A child's proof** (`vsPiOfNC`, `vsPiOfA`) at `verify_sub`'s valuation, off `open_stacked`'s
tables `T`: its stream (the cursor's length at most `L`), the opening's words, the selected size
and rate's levels' openings: at most `vsPiPrice R S F C L`. -/
theorem vsPiOfN_cost (hP : Includes P Decoder.vsPiOfNC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOK T) :
    machineCost P Decoder.vsPiOfNC.costIdx [encodeValue T, rdV, σV, VnV, clV] ≤
      vsPiPrice R S F C L := by
  rw [Decoder.vsPiOfNC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl]
  have := hS (.n 278)
  have := logGTWith_cost P (by includes) T.lanes hT.lanes (σ (.n 278)) 11 (by norm_num)
  have := logGTWith_le T.lanes (σ (.n 278)) 11
  have := vsPiOfS_cost P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) T hT
    (logGTWith T.lanes (σ (.n 278)) 11) (by omega)
  unfold vsPiPrice
  omega

end Proof

end Reader

end

end LeanVM.Cost.Bounds.Guest
