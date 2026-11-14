module

public import LeanVM.Guest.EndFinal
public import LeanVM.Guest.B1.Main.Facts
public import LeanVM.Cost.Decoder.Equations
public import LeanVM.Cost.Decoder.TopEq
public import LeanVM.Guest.Child.Reads

/-!
# The guest decoder's counts on a valid execution

On a valid execution of the leanISA guest, the counts the compiled decoder reads off `main`'s
valuation (`mainVal rd`, `rd` the reader of the memory vector through the table of its addresses,
as the decoder's top `decTop` reads it) are the ones `main`'s checks bound (`B1.Main.main_facts`):
at most `16` children (a range check), and the claims of each list, the raw signatures of each
scheme and the slots of both regions together below the memory's size `2^κ` (`assert_gpow`: each
is the exponent of an address of the memory).

* `mainVal_valid`: the decoder's valuation is `main`'s at its frame (`valG t.memory 1 (certOf 1)`);
* `mainFacts_valid`: `main`'s facts (`MainFacts`) at that valuation;
* **`valid_counts`**: `ValidCounts discreteLogTables σ`, the counts read by `gLogD` in the tables
  built;
* **`valid_cursor`**: each child's cursor length, the words of its proof's stream before the
  opening (`cursorLength`, at `verify_sub`'s frame of the child's arguments, `subArgsK`), is at
  most `8192`: the decoded witness explains the input (`guest_knowledge`, `decTop_eq`), so the
  deferring verifier accepts the child's proof, whose stream has at most `childStreamCap = 8192`
  scalars (`Child.stream_le_of_verifyDeferred`) and begins with those words.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1 LeanVM.Guest.B1.Main LeanVM.Extraction.Fast LeanVM.Cost.Decoder

public section

/-- **The counts the decoder reads off `main`'s valuation `σ`**, in the logarithm's tables `D`:
at most `16` children, at most `M` declared claims and raw signatures of each scheme and `M` slots
of both regions together. -/
structure ValidCounts (D : DiscreteLogTables) (σ : Val) (M : ℕ) : Prop where
  kids : nKidsD D σ ≤ 16
  xClaims : gLogD D (σ (.n 0)) ≤ M
  sClaims : gLogD D (σ (.n 3)) ≤ M
  rawX : nRawXD D σ ≤ M
  rawS : nRawSD D σ ≤ M
  slots : lxSlotsD D σ + lsSlotsD D σ ≤ M

/-- The decoder's reader of a valid execution's memory is the memory's. -/
theorem memReader_valid {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) :
    memReader (powTable t.logMemorySize) (memoryVector t.memory) = t.memory.read := by
  have hκ : t.logMemorySize < 64 := by
    have := hv.1.2.1
    unfold maxLogMem at this
    omega
  rw [memReader_memoryVector, Located.readTable_powTable hκ]

/-- **The decoder's valuation is `main`'s at its frame** (`fp = 1`, `main`'s certificate). -/
theorem mainVal_valid {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) :
    mainVal (memReader (powTable t.logMemorySize) (memoryVector t.memory)) =
      valG t.memory 1 (certOf 1) := by
  rw [memReader_valid hv, mainVal_eq]
  rfl

/-- **`main`'s facts on a valid execution**, at the decoder's valuation. -/
theorem mainFacts_valid {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) :
    MainFacts (Located.RLg t.memory) t.memory.read
      (mainVal (memReader (powTable t.logMemorySize) (memoryVector t.memory))) := by
  rw [mainVal_valid hv]
  have hm : Digest.MemOk t.memory.read := ⟨t.logMemorySize, hv.1.1,
    (by have := hv.1.2.1; unfold maxLogMem at this; omega), t.memory, rfl⟩
  have hU := unfolds_of_V (Located.unfoldsV_replay (End.b2SoundL End.endPending_proved) hv)
  refine main_facts hU (Located.rlg_le_rel t.memory) hm exponent_tables_holds (fun args h ↦ ?_)
    (End.mainBodyL_of (End.b2SoundL End.endPending_proved) hv).1
  obtain ⟨fn, σ, hf, hp, hb⟩ := hU _ _ _ h
  rw [find_loop2] at hf
  cases hf
  exact ⟨_, loop2Out_of_body Sig.verify_lean_xmss_sound_holds hp hb⟩

open LeanVM.Protocol.Verifier LeanVM.Guest.Value in
/-- A word read at offset `0` through a pointer of a memory of `2^κ` words is `g^e`, `e < 2^κ`. -/
theorem load_gpow_lt {κ : ℕ} (hκ : κ ≤ 30) (L : MemoryImage κ) {x w : E}
    (h : LoadHolds L.read x 0 w) : ∃ e < 2 ^ κ, x = gen ^ e := by
  obtain ⟨hx, hr⟩ := h
  rw [Parameters.addressOfIndex, pow_zero, mul_one] at hr
  obtain ⟨i, hi, -⟩ := (read_some_iff (by omega) L _ _).mp hr
  exact ⟨i, i.2, by rw [eq_ofK_limb hx, hi, gen_pow_eq_ofK]⟩

open LeanVM.Protocol.Verifier LeanVM.Guest.Value in
/-- The counts of `main`'s facts, read by `gLog`, on a memory of `2^κ` words: each below `2^κ`. -/
theorem validCounts_of {C : CallRel} {κ : ℕ} (hκ : κ ≤ 30) {L : MemoryImage κ} {σ : Val}
    (MF : MainFacts C L.read σ) : ValidCounts discreteLogTables σ (2 ^ κ) := by
  have hpow : 2 ^ κ ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hκ
  have hlt : ∀ v ∈ [0, 1, 2, 3, 4, 5, 24], ∀ e, e < 2 ^ 32 → σ (.n v) = gen ^ e → e < 2 ^ κ := by
    intro v hv e he hve
    obtain ⟨w, hw⟩ := MF.addr v hv
    obtain ⟨e', he', h'⟩ := load_gpow_lt hκ L hw
    have := gen_pow_inj (a := e) (b := e') (by omega) (by omega) (hve.symm.trans h')
    omega
  have hc : ∀ v ∈ [0, 1, 2, 3, 4, 5], gLog (σ (.n v)) ≤ 2 ^ κ := fun v hv ↦ by
    rw [← lg_eq_gLog]
    have := hlt v (by simp only [List.mem_cons] at hv ⊢; tauto) _ (MF.counts v hv).2
      (MF.counts v hv).1
    omega
  have hk : gLog (σ (.n 6)) ≤ 16 := by rw [← lg_eq_gLog]; exact MF.kids.2
  have ht := MF.total.2
  have ht' := hlt 24 (by simp) _ ht MF.total.1
  have hx : gLog (σ (.n 22)) = lg σ 0 + lg σ 1 := by
    rw [MF.lxs, gLog_gen_pow (by
      have := (MF.counts 0 (by simp)).2; have := (MF.counts 1 (by simp)).2; omega)]
  have hs : gLog (σ (.n 23)) = lg σ 3 + lg σ 4 := by
    rw [MF.lss, gLog_gen_pow (by
      have := (MF.counts 3 (by simp)).2; have := (MF.counts 4 (by simp)).2; omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold nKidsD; rw [gLogD_tables]; exact hk
  · rw [gLogD_tables]; exact hc 0 (by simp)
  · rw [gLogD_tables]; exact hc 3 (by simp)
  · unfold nRawXD; rw [gLogD_tables]; exact hc 2 (by simp)
  · unfold nRawSD; rw [gLogD_tables]; exact hc 5 (by simp)
  · unfold lxSlotsD lsSlotsD; rw [gLogD_tables, hx, hs]; omega

/-- **On a valid execution of the guest, the counts the decoder reads are small**: at its
valuation `mainVal rd` of `main`'s frame, `rd` the reader of the memory vector (`decTop`'s), in
the logarithm's tables built. -/
theorem valid_counts {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) :
    ValidCounts discreteLogTables
      (mainVal (memReader (powTable t.logMemorySize) (memoryVector t.memory)))
      (2 ^ t.logMemorySize) :=
  validCounts_of hv.1.2.1 (mainFacts_valid hv)


/-- A child proof's stream begins with its cursor's words. -/
theorem cursor_le_stream (T : Fast.WhirTabs) (rd : Reader) (σ : Val) (Vn : Fast.NFrames)
    (cl : E → E → ℕ) :
    cl (σ (.n 25)) (σ (.n 1919)) ≤ (Fast.vsPiOfA T rd σ Vn cl).stream.length := by
  have hw : ∀ (a : K) (n : ℕ), (Fast.wordsFrom rd a n).length = n := by
    intro a n
    induction n generalizing a with
    | zero => rfl
    | succ n ih => rw [Fast.wordsFrom, List.length_cons, ih]
  simp only [Fast.vsPiOfA, Fast.vsPiOfS, Fast.vsPiOfM, Fast.vsPiOfAt, List.length_append, hw]
  omega

/-- **On a valid execution of the guest, each child's cursor length is at most `8192`**: at the
decoder's reader, valuation and table of entries (`decTop`'s), for every child `c` below the
count it reads. -/
theorem valid_cursor {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) (c : ℕ)
    (hc : c < nKidsD discreteLogTables
      (mainVal (memReader (powTable t.logMemorySize) (memoryVector t.memory)))) :
    let rd := memReader (powTable t.logMemorySize) (memoryVector t.memory)
    let σ := mainVal rd
    let fr := frameAtA (entryArrayT pcTableT (Fast.preTestAt discreteLogTables Fast.preTable Fast.genPows rd)
      (replayStatesOf (powTable t.logMemorySize) (powTable guestProgram.logSize) guestProgram
        (memoryVector t.memory)) rd) rd 19 (subArgsK rd σ c) []
    cursorLength discreteLogTables (fr (.n 25)) (fr (.n 1919)) ≤ 8192 := by
  intro rd σ fr
  have hk : Node.ExplainsPublicInput guestProgram input (End.decode t.memory) := End.guest_knowledge input t hv
  rw [← decTop_eq] at hk
  have hrel := hk.2.2.2.1
  let w := decWitNStaged discreteLogTables Fast.readerTabs σ rd
    (frameAtA (entryArrayT pcTableT (Fast.preTestAt discreteLogTables Fast.preTable Fast.genPows rd)
      (replayStatesOf (powTable t.logMemorySize) (powTable guestProgram.logSize) guestProgram
        (memoryVector t.memory)) rd) rd)
    (xmssAtFrameT Fast.readerTabs (entryArrayT pcTableT
      (Fast.preTestAt discreteLogTables Fast.preTable Fast.genPows rd)
      (replayStatesOf (powTable t.logMemorySize) (powTable guestProgram.logSize) guestProgram
        (memoryVector t.memory)) rd) rd)
    (sphincsAtFrameT Fast.readerTabs (entryArrayT pcTableT
      (Fast.preTestAt discreteLogTables Fast.preTable Fast.genPows rd)
      (replayStatesOf (powTable t.logMemorySize) (powTable guestProgram.logSize) guestProgram
        (memoryVector t.memory)) rd) rd σ) (cursorLength discreteLogTables)
  have hw : (decTop guestProgram t.logMemorySize (memoryVector t.memory)).witness = w := rfl
  rw [hw] at hrel
  have hmem : decKidT discreteLogTables rd σ (proofAtFrame Fast.readerTabs rd
      (frameAtA (entryArrayT pcTableT (Fast.preTestAt discreteLogTables Fast.preTable Fast.genPows rd)
        (replayStatesOf (powTable t.logMemorySize) (powTable guestProgram.logSize) guestProgram
          (memoryVector t.memory)) rd) rd) (cursorLength discreteLogTables))
      (σ (.n 398)) (σ (.n 31)) (σ (.n 34)) (lxTable discreteLogTables rd σ)
      (lsTable discreteLogTables rd σ) c ∈ w.children := by
    simp only [w, decWitNStaged, decWitStaged, decWitAt, decWitTab, nodeWitnessOf, kidsT]
    exact List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩
  have hacc := (hrel _ hmem).2
  have hs := LeanVM.Guest.Child.stream_le_of_verifyDeferred hacc
  have hl := cursor_le_stream Fast.readerTabs.whir rd fr
    (frameAtA (entryArrayT pcTableT (Fast.preTestAt discreteLogTables Fast.preTable Fast.genPows rd)
      (replayStatesOf (powTable t.logMemorySize) (powTable guestProgram.logSize) guestProgram
        (memoryVector t.memory)) rd) rd) (cursorLength discreteLogTables)
  exact hl.trans hs

end

end LeanVM.Cost.Bounds.Guest
