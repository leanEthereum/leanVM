module

public import LeanVM.Cost.Bounds.Guest.DecTop
public import LeanVM.Cost.Bounds.Decoder.EntryArray
public import LeanVM.Cost.Bounds.Decoder.PcTable
public import LeanVM.Cost.Bounds.Decoder.PreTable
public import LeanVM.Cost.Bounds.Decoder.PreTableShape
public import LeanVM.Cost.Bounds.Decoder.Cursor
public import LeanVM.Cost.Bounds.Decoder.ReplayLength
public import LeanVM.Cost.DecoderSpec
public import LeanVM.Cost.Bounds.Guest.BudgetIncludes
public import LeanVM.Cost.Bounds.Guest.Valid
public import LeanVM.Cost.Prices

/-!
# Bounds on the guest decoder's prices: within the budget

**`decoderPriceWithinBudget : DecoderPriceWithinBudget`**: on every valid execution of the guest,
the decoder program's price is within `guestDecoderPrice` (`Cost/Prices.lean`,
`decoderPrice_le_exact`), within the statement's `guestWitnessDecoderBudget` (`Statement/LeanVmGuest.lean`;
`guestDecoderPrice_le_budget`). The composition (`decTop_cost`, `Bounds/Guest/DecTop.lean`) at:

* the reader at `1271` (`readerClosure_cost`), the replay of at most `steps + 1` states
  (`replayStatesOf_length`);
* the counts `main`'s range checks bound (`valid_counts`, `Bounds/Guest/Valid.lean`): at most `16`
  children, `65535` slots in the two regions together, `65535` declared claims and raw signatures
  a scheme (`CountsWithin`), and `da_verify`'s rows at most `1024` (`dvWitN_cost_1024`, on every input);
* the entry table, one sorted array (`entryArrayT_cost`) at the key exponent
  `guestDecoderEntryTableKeyExponent steps`, the precondition test (`preTestAt_cost_deployed`, its
  logarithms' bounds by the lanes' scan, `powBelow_cost`, its powers read off the powers table:
  `guestDecoderPreconditionPrice = 436638 ≈ 2^18.74`), the pc table
  (`pcTableT_get_cost`, `pcTableT_getD_length`): per state
  `guestDecoderStateFilingPrice` (`entryArrayStatePrice_eq`);
* the frame map (`frameAtA_cost`, one binary search, calls of at most `16` words): within
  `guestDecoderFramePrice` (`frameAtAPrice_le`); the cursor's length (`cursorLength_cost`, value
  at most `8192` at each child's frame on a valid run, `valid_cursor`), the witness
  (`frameWit_cost`);
* the tables: preconditions `12880` (`preTable_cost`), entries `8112592` (`pcTableT_cost`); the
  address tables at the execution's `κ` and the guest's `ℓ`, `addressTablesPrice κ ℓ =
  (74κ + 121)·2^κ + (74ℓ + 121)·2^ℓ + 42` (`decoderTables_cost`),
  `guestDecoderAddressTablesPrice` (`addressTablesPrice_eq`), and the rest of the constant,
  `topConstPrice`, at most `426293589240 + 40774872·F` (`2^38.63 + 2^25.28·F`,
  `topConst_valid_le`, each child's cursor at most `8192` words by `valid_cursor`), the
  `guestDecoderWitnessPriceAtValidCounts + guestDecoderFrameLookupCountAtValidCounts·F`
  (`topConst_le`).
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast LeanVM.Guest.Located
open LeanVM.Node

public section

attribute [local instance] lexOrd

/-- The constant's linear form in the frame map's price, the address tables apart, at a valid
run's counts (`16` children, `65535` slots in the two regions together, `65535` declared claims
and raw signatures a scheme, each child's cursor at most `8192` words): `426293589240 + 40774872·F`. -/
theorem topConst_valid_le (F : ℕ) :
    topConstPrice 65535 (decWitNPrice gLogPrice 1271 (1271 + 1525) (F + 9) (125634 + 5)
      8192 (dvFramePrice gLogPrice (F + 9)) (xmssReaderPrice 1271 (4 * F))
      (sphincsReaderPrice 1271 (1271 + 1525) F) 16 65535
        65535) ≤
      426293589240 + 40774872 * F := by
  unfold topConstPrice framesPrice decStmtPrice decStmtAtPrice decWitNPrice sphincsReaderPrice
    xmssReaderPrice xmssPrice xPartPrice decWitPrice
    decWitAtPrice decWitTabPrice kidsTPrice decKidPrice kidStmtPrice kidStmtAtPrice kidSlotsInPrice
    xmssRawsTPrice sphincsRawsTPrice regionTablePrice vsPiPrice vsMPrice
    vsAtPrice levelPrice levelAtPrice oqsPrice stepPrice iterPrice queryPrice posPrice
    queryAtPrice openingPrice dvFramePrice dvWitNRowsPrice gLogPrice
  omega

/-- The address tables' price is the statement's. -/
theorem addressTablesPrice_eq (κ ℓ : ℕ) :
    addressTablesPrice κ ℓ = guestDecoderAddressTablesPrice κ ℓ := rfl

/-- The constant is the statement's linear form. -/
theorem topConst_le (F : ℕ) :
    topConstPrice 65535 (decWitNPrice gLogPrice 1271 (1271 + 1525) (F + 9) (125634 + 5)
      8192 (dvFramePrice gLogPrice (F + 9)) (xmssReaderPrice 1271 (4 * F))
      (sphincsReaderPrice 1271 (1271 + 1525) F) 16 65535
        65535) ≤
      guestDecoderWitnessPriceAtValidCounts + guestDecoderFrameLookupCountAtValidCounts * F :=
  topConst_valid_le F

/-- **Filing a state**: the sorted entry array's price per state (`entryArrayStatePrice`) at the
deployed pc table's lookup (`5969`), two functions a pc, the precondition test and the reader, is
the statement's filing price. -/
theorem entryArrayStatePrice_eq (e : ℕ) :
    entryArrayStatePrice 5969 2 guestDecoderPreconditionPrice 1271 e =
      guestDecoderStateFilingPrice e := by
  unfold entryArrayStatePrice pairsStatePrice guestDecoderStateFilingPrice
    guestDecoderEntryTablePositionLimbs wl
  ring

/-- A frame lookup of at most `16` words on the sorted array, within the statement's (equal at
`16` words). -/
theorem frameAtAPrice_le (e n : ℕ) (hn : n ≤ 16) :
    (64 * n + 78 + 9 * wl e) * (e + 2) + 27 * n + 1271 + 1584 ≤ guestDecoderFramePrice e := by
  have hw : wl e = limbsBelowTwoPow (e + 1) := rfl
  rw [hw]
  unfold guestDecoderFramePrice guestDecoderEntryTablePositionLimbs
  have h1 : (64 * n + 78 + 9 * limbsBelowTwoPow (e + 1)) * (e + 2) ≤
      (64 * 16 + 78 + 9 * limbsBelowTwoPow (e + 1)) * (e + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- A frame search of at most `16` words on the sorted array (`frameFpA_cost`), within the
statement's frame lookup. -/
theorem frameFpAPrice_le64 (e n : ℕ) (hn : n ≤ 64) :
    (64 * n + 78 + 9 * wl e) * (e + 2) + 27 * n + 49 ≤ 4 * guestDecoderFramePrice e := by
  have hw : wl e = limbsBelowTwoPow (e + 1) := rfl
  rw [hw]
  unfold guestDecoderFramePrice guestDecoderEntryTablePositionLimbs
  have h1 : (64 * n + 78 + 9 * limbsBelowTwoPow (e + 1)) * (e + 2) ≤
      4 * ((64 * 16 + 78 + 9 * limbsBelowTwoPow (e + 1)) * (e + 2)) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- A frame search of at most `16` words on the sorted array (`frameFpA_cost`), within the
statement's frame lookup. -/
theorem frameFpAPrice_le (e n : ℕ) (hn : n ≤ 16) :
    (64 * n + 78 + 9 * wl e) * (e + 2) + 27 * n + 49 ≤ guestDecoderFramePrice e := by
  have hw : wl e = limbsBelowTwoPow (e + 1) := rfl
  rw [hw]
  unfold guestDecoderFramePrice guestDecoderEntryTablePositionLimbs
  have h1 : (64 * n + 78 + 9 * limbsBelowTwoPow (e + 1)) * (e + 2) ≤
      (64 * 16 + 78 + 9 * limbsBelowTwoPow (e + 1)) * (e + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- The replay lists the initial state at least. -/
theorem replayStatesOf_length_pos (memT codeT : Array (ℕ × ℕ)) (prog :
    LeanVM.Semantics.LeanIsaProgram)
    {κ : ℕ} (mem : Vector E (2 ^ κ)) : 1 ≤ (Decoder.replayStatesOf memT codeT prog mem).length := by
  unfold Decoder.replayStatesOf replayFuel
  rw [show (2 : ℕ) ^ 128 = (2 ^ 128 - 1) + 1 by norm_num, Decoder.statesVec]
  simp

theorem keyExponent_pos (steps : ℕ) : 1 ≤ guestDecoderEntryTableKeyExponent steps := by
  unfold guestDecoderEntryTableKeyExponent; omega

theorem tableExponent_spec (steps : ℕ) : 2 * (steps + 1) < 2 ^ guestDecoderEntryTableKeyExponent steps := by
  unfold guestDecoderEntryTableKeyExponent
  exact Nat.lt_log2_self

variable (P : MachineProgram)

/-- **On every valid execution of the guest, the decoder program's price is within its exact
price** (`guestDecoderPrice`, `Cost/Prices.lean`). -/
theorem decoderPrice_le_exact (input : PublicInput) (t : Execution LeanVM.Guest.guestProgram)
    (hv : ValidExecution LeanVM.Guest.guestProgram input t) :
    decoderProgramPrice LeanVM.Guest.guestProgram t ≤
      guestDecoderPrice t.logMemorySize LeanVM.Guest.guestProgram.logSize t.stepCount := by
  unfold decoderProgramPrice guestDecoderPrice
  have hP := decoderProgram_includes
  have hκ : t.logMemorySize ≤ 32 := hv.1.2.1
  have hlen := replayStatesOf_length hv
  have hcv := valid_counts hv
  have hc : CountsWithin discreteLogTables (Decoder.mainVal
      (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)))
      16 65535 65535 :=
    ⟨by norm_num, by norm_num, by norm_num, hcv.kids, by have := hcv.slots; omega,
      by have := hcv.slots; omega, hcv.xClaims, hcv.sClaims, hcv.rawX, hcv.rawS⟩
  set states := Decoder.replayStatesOf (powTable t.logMemorySize) (powTable LeanVM.Guest.guestProgram.logSize)
    LeanVM.Guest.guestProgram (Decoder.memoryVector t.memory) with hstates
  set e := guestDecoderEntryTableKeyExponent t.stepCount
  have hn : 2 * states.length < 2 ^ e :=
    lt_of_le_of_lt (by omega) (tableExponent_spec t.stepCount)
  have hrd := readerClosure_runs compiledGuestWitnessDecoder includes_budget_readerClosure (Decoder.memoryVector t.memory)
  have hR := readerClosure_cost compiledGuestWitnessDecoder includes_budget_readerClosure hκ (Decoder.memoryVector t.memory)
  have hLg : ∀ x : K, machineCost compiledGuestWitnessDecoder Decoder.discreteLogWithC.costIdx
      [encodeValue discreteLogTables, encodeValue x] ≤ 122420 :=
    fun x ↦ discreteLogWith_cost compiledGuestWitnessDecoder includes_budget_discreteLogWith x
  have hB : ∀ (w : E) (n : ℕ), n ≤ 34 → machineCost compiledGuestWitnessDecoder
      Decoder.powBelowC.costIdx
      [encodeValue discreteLogTables, encodeValue w, encodeValue n] ≤ 706 :=
    fun w n hn ↦ powBelow_cost compiledGuestWitnessDecoder includes_budget_powBelow
        discreteLogTables w n hn
  have hpre : ∀ (j : ℕ) (fp : K), RunsApp compiledGuestWitnessDecoder
      (.closure Decoder.decTopStatesC.lam1.costIdx [encodeValue discreteLogTables,
        encodeValue preTable, encodeValue genPows, readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue j, encodeValue fp]
      (encodeValue (preTestAt discreteLogTables preTable genPows
        (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)) j fp)) := fun j fp ↦
    RunsApp.of_spec (Decoder.decTopStatesC.lam1.costSpec compiledGuestWitnessDecoder
        includes_budget_preTestLam
      discreteLogTables preTable genPows _ _ hrd j fp)
  have hPr : ∀ (j : ℕ) (fp : K), j < 2 ^ 64 → appCost compiledGuestWitnessDecoder
      (.closure Decoder.decTopStatesC.lam1.costIdx [encodeValue discreteLogTables,
        encodeValue preTable, encodeValue genPows, readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue j, encodeValue fp] ≤
      guestDecoderPreconditionPrice := fun j fp hj ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.decTopStatesC.lam1.costEq compiledGuestWitnessDecoder includes_budget_preTestLam _ _ _ _ _ hrd, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := preTestAt_cost_deployed compiledGuestWitnessDecoder includes_budget_preTestAt discreteLogTables _ _ hrd 1271 hR
      706 hB preTable preTable_shape genPows j hj fp
    unfold guestDecoderPreconditionPrice
    omega
  have he1 := keyExponent_pos t.stepCount
  have hpos := replayStatesOf_length_pos (powTable t.logMemorySize)
    (powTable LeanVM.Guest.guestProgram.logSize) LeanVM.Guest.guestProgram (Decoder.memoryVector t.memory)
  rw [← hstates] at hpos
  have hE := entryArrayT_cost compiledGuestWitnessDecoder _ _ hrd 1271 hR _ _ hpre _ hPr
    includes_budget_entryArrayT Decoder.pcTableT 2 5969 e pcTableT_getD_lt pcTableT_getD_length
    (fun k hk ↦ pcTableT_get_cost compiledGuestWitnessDecoder includes_budget_getPc k hk) states hn
  obtain ⟨hok, hsz⟩ := entryArrayT_ok (Decoder.memReader (powTable t.logMemorySize)
    (Decoder.memoryVector t.memory)) (preTestAt discreteLogTables preTable genPows
    (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)))
    Decoder.pcTableT 2 pcTableT_getD_lt pcTableT_getD_length states
  have hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
      machineCost compiledGuestWitnessDecoder Decoder.frameAtAC.costIdx
        [encodeValue (Decoder.entryArrayT Decoder.pcTableT
          (preTestAt discreteLogTables preTable genPows (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)))
          states (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory))), readerV t.logMemorySize (Decoder.memoryVector t.memory), encodeValue k,
          encodeValue a, encodeValue r, encodeValue v] ≤ guestDecoderFramePrice e :=
    fun k a r v hk hl ↦ (frameAtA_cost compiledGuestWitnessDecoder _ _ hrd 1271 hR
        includes_budget_frameAtA e _
      hok (by omega) k hk a r v).trans (frameAtAPrice_le e _ hl)
  have hFp : ∀ (j : ℕ) (args rets : List E), j < 2 ^ 64 → args.length + rets.length ≤ 16 →
      machineCost compiledGuestWitnessDecoder Decoder.frameFpAC.costIdx
        [encodeValue (Decoder.entryArrayT Decoder.pcTableT
          (preTestAt discreteLogTables preTable genPows (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)))
          states (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory))),
          encodeValue j, encodeValue args, encodeValue rets] ≤ guestDecoderFramePrice e :=
    fun j args rets hj hl ↦ (frameFpA_cost compiledGuestWitnessDecoder includes_budget_frameFpA e _
      hok (by omega) j hj args rets).trans (frameFpAPrice_le e _ hl)
  have hFp4 : ∀ (args rets : List E), args.length + rets.length ≤ 64 →
      machineCost compiledGuestWitnessDecoder Decoder.frameFpAC.costIdx
        [encodeValue (Decoder.entryArrayT Decoder.pcTableT
          (preTestAt discreteLogTables preTable genPows (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)))
          states (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory))),
          encodeValue 37, encodeValue args, encodeValue rets] ≤ 4 * guestDecoderFramePrice e :=
    fun args rets hl ↦ (frameFpA_cost compiledGuestWitnessDecoder includes_budget_frameFpA e _
      hok (by omega) 37 (by norm_num) args rets).trans (frameFpAPrice_le64 e _ hl)
  have hσ : ∀ v : V, RunsApp compiledGuestWitnessDecoder
      (.closure Decoder.decTopStatesC.lam0.costIdx [readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue v]
      (encodeValue (Decoder.mainVal (Decoder.memReader (powTable t.logMemorySize) (Decoder.memoryVector t.memory)) v)) := fun v ↦
    RunsApp.of_spec (Decoder.decTopStatesC.lam0.costSpec compiledGuestWitnessDecoder includes_budget_mainValLam _ _ hrd v)
  have hS : ∀ v : V, appCost compiledGuestWitnessDecoder
      (.closure Decoder.decTopStatesC.lam0.costIdx [readerV t.logMemorySize (Decoder.memoryVector t.memory)]) [encodeValue v] ≤
        1271 + 1525 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.decTopStatesC.lam0.costEq compiledGuestWitnessDecoder includes_budget_mainValLam _ _ hrd, List.length_cons, List.length_nil]
    have := mainVal_cost compiledGuestWitnessDecoder includes_budget_mainVal hrd hR v; omega
  have hW := frameWit_cost compiledGuestWitnessDecoder discreteLogTables includes_budget_decWitN includes_budget_frameLam
    includes_budget_xmssLam includes_budget_sphincsLam includes_budget_cursorLam
    (gLog_bound compiledGuestWitnessDecoder includes_budget_gLogD) readerTabs readerTabs_ok hrd hR hσ hS
    _ (guestDecoderFramePrice e) hF hFp (4 * guestDecoderFramePrice e) hFp4 125634
    (fun p q ↦ cursorLength_cost compiledGuestWitnessDecoder includes_budget_cursorLength discreteLogTables 122420 hLg
      discreteLogWith_lt p q)
    hc 8192 (by norm_num) (fun c hck ↦ valid_cursor hv c hck)
  have hT := decTop_cost compiledGuestWitnessDecoder hP LeanVM.Guest.guestProgram hκ (Decoder.memoryVector t.memory) 12880 8112592 _ _
    (preTable_cost compiledGuestWitnessDecoder includes_budget_preTable).le (pcTableT_cost compiledGuestWitnessDecoder includes_budget_pcTableT)
    hE hW hc
  have hk := topConst_le (guestDecoderFramePrice e)
  rw [addressTablesPrice_eq] at hT
  rw [entryArrayStatePrice_eq] at hT
  rw [← hstates] at hT
  have h1 := Nat.mul_le_mul_left (runnerStepPrice t.logMemorySize LeanVM.Guest.guestProgram.logSize + 46) hlen
  have h2 := Nat.mul_le_mul_left (guestDecoderStateFilingPrice e) hlen
  rw [Nat.add_mul]
  omega


/-- The entry table's key exponent is `log₂(steps + 1) + 2`. -/
theorem keyExponent_eq (steps : ℕ) :
    guestDecoderEntryTableKeyExponent steps = Nat.log2 (steps + 1) + 2 := by
  unfold guestDecoderEntryTableKeyExponent
  rw [Nat.log2_two_mul (by omega)]

/-- **The exact price within the statement's budget**, at the guest's `ℓ = 19`, a memory of at
most `2^32` words and fewer than `2^128` steps: per step `2^21 + 2^13·log₂(steps + 1)` (the
memory read at `κ ≤ 32`, the positions of at most `3` limbs), the frame lookups at
`1129·log₂(steps + 1) + 7803` each. -/
theorem guestDecoderPrice_le_budget {κ steps : ℕ} (hκ : κ ≤ 32) (hs : steps < 2 ^ 128) :
    guestDecoderPrice κ 19 steps ≤ (steps + 1) * (2 ^ 21 + 2 ^ 13 * Nat.log2 (steps + 1)) +
      (70 * κ + 374) * 2 ^ κ + 2 ^ 37 * (Nat.log2 (steps + 1) + 16) := by
  have hlg : Nat.log2 (steps + 1) < 129 :=
    (Nat.log2_lt (by omega)).2 (lt_of_le_of_lt (Nat.succ_le_of_lt hs) (by norm_num))
  unfold guestDecoderPrice
  rw [keyExponent_eq]
  generalize Nat.log2 (steps + 1) = lg at hlg ⊢
  have hL : guestDecoderEntryTablePositionLimbs (lg + 2) ≤ 3 := by
    unfold guestDecoderEntryTablePositionLimbs limbsBelowTwoPow; omega
  have hstep : runnerStepPrice κ 19 + 46 + guestDecoderStateFilingPrice (lg + 2) ≤
      2 ^ 21 + 2 ^ 13 * lg := by
    unfold runnerStepPrice guestDecoderStateFilingPrice guestDecoderPreconditionPrice
    generalize guestDecoderEntryTablePositionLimbs (lg + 2) = L at hL ⊢
    nlinarith [Nat.mul_le_mul_right (lg + 2) hL]
  have hframe : guestDecoderFramePrice (lg + 2) ≤ 1129 * lg + 7803 := by
    unfold guestDecoderFramePrice
    generalize guestDecoderEntryTablePositionLimbs (lg + 2) = L at hL ⊢
    nlinarith [Nat.mul_le_mul_right (lg + 2 + 2) hL]
  calc _ ≤ (2 ^ 21 + 2 ^ 13 * lg) * (steps + 1) + 12880 + 8112592 +
          guestDecoderAddressTablesPrice κ 19 + guestDecoderWitnessPriceAtValidCounts +
          guestDecoderFrameLookupCountAtValidCounts * (1129 * lg + 7803) + 39 := by gcongr
    _ ≤ _ := by
      have hκ' : (74 * κ + 121) * 2 ^ κ ≤ (70 * κ + 374) * 2 ^ κ :=
        Nat.mul_le_mul_right _ (by omega)
      unfold guestDecoderAddressTablesPrice guestDecoderWitnessPriceAtValidCounts
        guestDecoderFrameLookupCountAtValidCounts
      rw [Nat.mul_comm _ (steps + 1)]
      omega

/-- **On every valid execution of the guest, the decoder program's price is within its
budget**: within the exact price (`decoderPrice_le_exact`), within the budget
(`guestDecoderPrice_le_budget`: `κ ≤ 32` and fewer than `2^128` steps on a valid execution). -/
theorem decoderPriceWithinBudget : DecoderPriceWithinBudget := fun input t hv ↦ by
  have h := decoderPrice_le_exact input t hv
  rw [LeanVM.Guest.guest_logSize] at h
  unfold guestWitnessDecoderBudget
  exact h.trans (guestDecoderPrice_le_budget hv.1.2.1 (steps_lt_of_valid hv))

end

end LeanVM.Cost.Bounds.Guest
