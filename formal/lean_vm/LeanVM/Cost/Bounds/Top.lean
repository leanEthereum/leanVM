module

public import LeanVM.Cost.Bounds.Assembly
public import LeanVM.Cost.Bounds.TopIncludes
public import LeanVM.Cost.Bounds.Decoder.Decode
public import LeanVM.Cost.Bounds.PMLane.Decode
public import LeanVM.Cost.Bounds.PMLane.Shapes
public import LeanVM.Cost.Extractor.Top
import all Statement.LeanIsa
import all LeanVM.Protocol.Extraction.Extractor
import all LeanVM.Protocol.Extraction.Fast.Compiled
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.SortedMap
public import LeanVM.Cost.Prices

/-!
# Bounds: the compiled extractor

`extractorC` (`Cost/Extractor/Top.lean`) is `extractorTop`, point-free: the bytecode's words
(`bytecodeWordsC`), the replay (`afterRootLiteC`), then `Option.bind` with `afterRootStageC`: the
first root, then `stageTC`: the committed leaves (`leavesOfC`), then `runFromLeavesC`: the fast
path's stacks (`fastOfC`), and `runBothC`: the runner's tables, a run per fast stack, else the
decoder's stacks (`decOfC`) and a run per decoded stack. Bounded from their price equations:

* the committed leaves on the chain: `bytesWordC_cost` (`296`),
  `bytesLanesC_cost` (`439` per word), `leafOfWithC_cost`, `bytesDigestC_cost` (`7428`: its four
  words each through `bytesLanes 4`), `subtreeLeavesWithC_cost` (by doubling), a lookup in the
  transcript's index `preimageLookup_cost` (`D·(20 + (162 + 9W)·(D + 2)) + 42`, its keys `PreKey`:
  `transcriptIndex_keys`), **`leavesOfC_cost`** (`transcriptIndexPrice` and `committedLeavesPrice`);
* the bytecode's words: **`bytecodeWordsC_cost`** (`bytecodeWordsPrice ℓ = 5712·2^ℓ + 947`);
* **`fastOfC_cost`** (`fastPathPrice`), **`decOfC_cost`** (`PMLane.decodeStacksPMC_cost_worst`, at every
  admissible shape of a stack of `2^μ`: `1751·2^30 + listDecoderWorstPrice μ`), **`runBothC_cost`**, **`runFromLeavesC_cost`**,
  **`stageTC_cost`** (`afterRootStagePrice`), **`afterRootStageC_cost`**;
* **`extractorC_cost`**: on every input, at most `extractorPrice μ R κ ℓ N` at the shape
  `afterRootLite` announces (`replayPrice ℓ` if it fails), `N` the permutation queries, any number:
  the sorted maps' positions and weights priced by their limbs (`limbsBelowTwoPow (D + 1)`,
  `D = log₂(N + 2) + 1`), so the price grows like `N·D²·(D/64 + 1)`; the closed forms
  (`extractorPrice`, `afterRootStagePrice`, …) are `Cost/Prices.lean`'s;
* **`extractorC_within`**: the price and the entry's `14` within the statement's
  `leanVmKnowledgeExtractorBudget` at the announced stack size wherever `afterRoot` announces a
  shape (`hcost` of `extractorTop_output`), through `extractorPrice_le_budget`: the decoder's part
  (`listDecoderWorstPrice μ`) and `2^75` are the budget's first term, and the rest is at most the
  worst admissible shape's, `(32, 4)` (`extractorRest_le_worst`, `extractorRest_worst_le`);
* **`extractorPrice_32_4`**: at `(32, 4)`, `κ = ℓ = 32`, at most `2^40` queries:
  `77333585604662706796546663 ≈ 2^86`, the decoder's part (`listDecoderWorstPrice 32`) all
  but `≈ 2^66.6` of it (the `1 + 2^12` runs `≈ 2^65.60`, the transcript's index `≈ 2^65.61`);
  **`extractorPrice_32_4_2_128`**: at most `2^128` queries, `≈ 2^156.86`, the transcript's index
  dominating.

The `includes` between the top functions' lists of about `500` bodies takes seconds each: those
are lemmas of their own (`includes_stageTC`, …, `Bounds/TopIncludes.lean`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

public section

attribute [local instance] lexOrd

variable (P : LeanVM.Cost.MachineProgram)

/-! ## Lists on bytes -/

theorem foldr_bytes_lt' (l : List UInt8) :
    l.foldr (fun x acc ↦ x.toNat + 256 * acc) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have := x.toNat_lt
    simp only [List.foldr_cons, List.length_cons, pow_succ]
    nlinarith

/-- **A word of bytes** (`bytesWord.c702`): at most `296`. -/
theorem bytesWordC_cost (hP : Includes P Auto.LeanVM.Extraction.bytesWord.c702.costDeps)
    (b : List UInt8) :
    machineCost P Auto.LeanVM.Extraction.bytesWord.c702.costIdx [encodeValue b] ≤ 296 := by
  rw [Auto.LeanVM.Extraction.bytesWord.c702.costEq P hP]
  have ht := take_cost P (by includes) 8 b (by norm_num)
  have hl : (b.take 8).length ≤ 8 := List.length_take_le _ _
  have hf := foldrSuffix_cost P (by includes) _
    (.closure Auto.LeanVM.Extraction.bytesWord.c702.lam0.costIdx [])
    (fun a acc ↦ RunsApp.of_spec
      (Auto.LeanVM.Extraction.bytesWord.c702.lam0.costSpec P (by includes) a acc)) 5 0 (b.take 8)
    (fun x tl h ↦ by
      have hlen : tl.length ≤ 7 := by have := h.length_le; simp at this; omega
      have hacc := foldr_bytes_lt' tl
      have : 256 ^ tl.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) hlen
      have hx := x.toNat_lt
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Extraction.bytesWord.c702.lam0.costEq P (by includes),
        limbs_of_lt (by omega), limbs_of_lt (by omega), limbs_of_lt (by omega),
        limbs_of_lt (by omega : x.toNat < 2 ^ 64), List.length_nil]
      omega)
  have hv := foldr_bytes_lt' (b.take 8)
  have h8 : 256 ^ (b.take 8).length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
  rw [limbs_of_lt (lt_of_lt_of_le hv (h8.trans (by norm_num)))]
  nlinarith

/-- **The first `n` words of bytes** (`bytesLanes.c701`): at most `439·n + 5`. -/
theorem bytesLanesC_cost (hP : Includes P Auto.LeanVM.Extraction.bytesLanes.c701.costDeps) :
    ∀ (n : ℕ) (b : List UInt8), n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Extraction.bytesLanes.c701.costIdx [encodeValue n, encodeValue b] ≤ 439 * n + 5 := by
  intro n
  induction n with
  | zero => intro b _; rw [Auto.LeanVM.Extraction.bytesLanes.c701.costEq P hP]; simp [limbs_of_lt]
  | succ k ih =>
    intro b hk
    rw [Auto.LeanVM.Extraction.bytesLanes.c701.costEq P hP, limbs_of_lt hk]
    have := ih (b.drop 8) (by omega)
    have := bytesWordC_cost P (by includes) b
    have := drop_cost P (by includes) 8 b (by norm_num)
    dsimp only
    omega

/-- **A leaf** (`leafOfWith.c699`): at most `L + 453·w + 21`, `L` the lookup's price. -/
theorem leafOfWithC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.leafOfWith.c699.costDeps)
    (pre : LeanVM.Protocol.Digest → ℕ → Option (List UInt8)) (preVal : MachineValue)
    (hpre : ∀ d n, RunsApp P preVal [encodeValue d, encodeValue n] (encodeValue (pre d n))) (L : ℕ)
    (hL : ∀ (d : LeanVM.Protocol.Digest) (n : ℕ), n < 2 ^ 64 → appCost P preVal [encodeValue d, encodeValue n] ≤ L)
    (w : ℕ) (hw : w < 2 ^ 61) (d : LeanVM.Protocol.Digest) :
    machineCost P Auto.LeanVM.Extraction.Fast.leafOfWith.c699.costIdx [preVal, encodeValue w, encodeValue d] ≤
      L + 453 * w + 21 := by
  rw [Auto.LeanVM.Extraction.Fast.leafOfWith.c699.costEq P hP pre preVal hpre,
    limbs_of_lt (by omega : w < 2 ^ 64), limbs_of_lt (by omega : 8 * w < 2 ^ 64), max_self]
  have := hL d (8 * w) (by omega)
  have := replicate_cost P (by includes) (0 : K) w (by omega)
  generalize pre d (8 * w) = o
  cases o with
  | none => dsimp only; omega
  | some val =>
    have := bytesLanesC_cost P (by includes) w val (by omega)
    have := map_cost P (by includes) _
      (.closure Auto.LeanVM.Extraction.Fast.leafOfWith.c699.lam0.costIdx [])
      (fun a ↦ RunsApp.of_spec
        (Auto.LeanVM.Extraction.Fast.leafOfWith.c699.lam0.costSpec P (by includes) a)) 1
      (LeanVM.Extraction.bytesLanes w val)
      (fun a _ ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Extraction.Fast.leafOfWith.c699.lam0.costEq P (by includes), List.length_nil])
    rw [bytesLanes_length] at this
    dsimp only
    omega

/-- **A digest of bytes** (`bytesDigest.c704`, its four words each through `bytesLanes 4`): at
most `7428`. -/
theorem bytesDigestC_cost (hP : Includes P Auto.LeanVM.Extraction.bytesDigest.c704.costDeps)
    (b : List UInt8) :
    machineCost P Auto.LeanVM.Extraction.bytesDigest.c704.costIdx [encodeValue b] ≤ 7428 := by
  rw [Auto.LeanVM.Extraction.bytesDigest.c704.costEq P hP]
  have hof := ofFnFrom_cost P (by includes) (n := 4) (by norm_num) _
    (.closure Auto.LeanVM.Extraction.bytesDigest.c704.lam0.costIdx [encodeValue b])
    (fun i ↦ RunsApp.of_spec
      (Auto.LeanVM.Extraction.bytesDigest.c704.lam0.costSpec P (by includes) b i)) 1837
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Extraction.bytesDigest.c704.lam0.costEq P (by includes)]
      have := bytesLanesC_cost P (by includes) 4 b (by norm_num)
      have := getD_cost P (by includes) (LeanVM.Extraction.bytesLanes 4 b) i 0 (by omega)
      rw [bytesLanes_length] at this
      omega) 0 (by norm_num)
  rw [ofFnFrom_length]
  omega

/-- **The subtree's leaves** (`subtreeLeavesWith.c698`): with `T` its price,
`T + a ≤ 2^h·(a + b + 5·h)`, `a = L + 15·w + 30725` (an inner node) and `b = L + 453·w + 35` (a
leaf), `L` the lookup's price. -/
theorem subtreeLeavesWithC_cost
    (hP : Includes P Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c698.costDeps)
    (pre : LeanVM.Protocol.Digest → ℕ → Option (List UInt8)) (preVal : MachineValue)
    (hpre : ∀ d n, RunsApp P preVal [encodeValue d, encodeValue n] (encodeValue (pre d n))) (L : ℕ)
    (hL : ∀ (d : LeanVM.Protocol.Digest) (n : ℕ), n < 2 ^ 64 → appCost P preVal [encodeValue d, encodeValue n] ≤ L)
    (w : ℕ) (hw : w < 2 ^ 61) :
    ∀ (h : ℕ) (d : LeanVM.Protocol.Digest),
      machineCost P Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c698.costIdx
          [preVal, encodeValue w, encodeValue h, encodeValue d] + (L + 15 * w + 30725) ≤
        2 ^ h * ((L + 15 * w + 30725) + (L + 453 * w + 35) + 5 * h) := by
  have hleaf := leafOfWithC_cost P (by includes) pre preVal hpre L hL w hw
  have hrep := replicate_cost P (by includes) (0 : K) w (by omega)
  have hdig := fun (b : List UInt8) ↦ bytesDigestC_cost P (by includes) b
  have hd32 := fun (b : List UInt8) ↦ drop_cost P (by includes) 32 b (by norm_num)
  apply le_of_doubling (fun (h : ℕ) (d : LeanVM.Protocol.Digest) ↦
    machineCost P Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c698.costIdx
      [preVal, encodeValue w, encodeValue h, encodeValue d])
  · intro d
    rw [Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c698.costEq_zero P hP pre preVal hpre]
    have := hleaf d
    omega
  · intro k d
    rw [Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c698.costEq_succ P hP pre preVal hpre]
    have := hL d 64 (by norm_num)
    have hk1 := Nat.lt_two_pow_self (n := k + 1)
    have hk2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hsh : limbCount (1 <<< (k + 1)) ≤ 2 ^ (k + 1) + 1 := by
      rw [Nat.shiftLeft_eq, one_mul]; exact limbs_le_add_one _
    have := limbs_le_add_one (k + 1)
    have := limbs_le_add_one k
    simp only [subtreeLeavesWith_size]
    generalize pre d 64 = o
    cases o with
    | none =>
      refine ⟨d, d, ?_⟩
      dsimp only
      omega
    | some val =>
      refine ⟨(splitNode val).1, (splitNode val).2, ?_⟩
      have := hdig val
      have := hdig (val.drop 32)
      have := hd32 val
      dsimp only
      omega

/-! ## The committed leaves -/

/-- The transcript's index holds keys `PreKey`. -/
theorem transcriptIndex_keys (T : List (Common.PermutationQuery KeccakState × KeccakState)) (L : ℕ)
    (hL : L < 2 ^ 64) : KeysIn PreKey (transcriptIndex T L).levels := by
  rw [transcriptIndex, preimageIndex]
  have hgen : ∀ (l : List (List UInt8 × LeanVM.Protocol.Digest))
      (m : SortedMap (List UInt64 × ℕ) Hits), KeysIn PreKey m.levels →
      (∀ p ∈ l, p.1.length < 2 ^ 64) →
      KeysIn PreKey (l.foldl (fun m p ↦
        m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) m).levels := by
    intro l
    induction l with
    | nil => intro m hm _; exact hm
    | cons x l ih =>
      intro m hm hl
      rw [List.foldl_cons]
      exact ih _ (keysIn_insert hm (preKey_hitKey x (hl x (by simp))) _)
        (fun p hp ↦ hl p (by simp [hp]))
  refine hgen _ _ (fun _ h ↦ by simp [SortedMap.empty] at h) (fun p hp ↦ ?_)
  obtain ⟨e, he, h⟩ := List.mem_map.1 (mem_answerPairs_fst hp)
  rw [← h]
  have := keccakEvaluationsFast_mem_length_le he
  omega

/-- **A preimage lookup** in the transcript's index (`leavesOfC.lam0`, `preimageIn.c707`): a
binary search per level, at most `D·(20 + (162 + 9·W)·(D + 2)) + 42`. -/
theorem preimageLookup_cost (hP : Includes P leavesOfC.lam0.costDeps)
    (qs : List (Common.PermutationQuery KeccakState × KeccakState)) (L D W : ℕ) (hL : L < 2 ^ 64)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hN : qs.length + 2 ≤ 2 ^ D)
    (d : LeanVM.Protocol.Digest) (len : ℕ) (hlen : len < 2 ^ 64) :
    appCost P (.closure leavesOfC.lam0.costIdx [encodeValue (transcriptIndex qs L)]) [encodeValue d, encodeValue len] ≤
      D * (20 + (162 + 9 * W) * (D + 2)) + 42 := by
  simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
  rw [leavesOfC.lam0.costEq P hP,
    Auto.LeanVM.Extraction.Fast.preimageIn.c707.costEq P (by includes)]
  obtain ⟨hg, hw⟩ := transcriptIndex_bounds qs L
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg (D := D)
    (lt_of_le_of_lt hw (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hN))
  have hget := getPre_cost P (by includes) (transcriptIndex qs L) (2 ^ D) W hW
    (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) (transcriptIndex_keys qs L hL)
    (d.toList, len) ⟨by simp, hlen⟩
  rw [Nat.log2_two_pow] at hget
  have hlv : (transcriptIndex qs L).levels.length * (20 + (162 + 9 * W) * (D + 2)) ≤
      D * (20 + (162 + 9 * W) * (D + 2)) := Nat.mul_le_mul_right _ hlev
  simp only [Vector.size_toArray]
  generalize (transcriptIndex qs L).get? (d.toList, len) = o1
  generalize (transcriptIndex qs L).getD (d.toList, len) Hits.none = o2
  cases o1 <;> cases o2 <;> dsimp only <;> omega

/-- **The committed leaves** (`leavesOfC`, width `64`): the transcript's index, then the subtree. -/
theorem leavesOfC_cost (hP : Includes P leavesOfC.costDeps)
    (qs : List (Common.PermutationQuery KeccakState × KeccakState)) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (hN : qs.length + 2 ≤ 2 ^ D) (h : ℕ) (root : LeanVM.Protocol.Digest) :
    machineCost P leavesOfC.costIdx [encodeValue qs, encodeValue 64, encodeValue h, encodeValue root] ≤
      19 + transcriptIndexPrice D 512 qs.length W + committedLeavesPrice D h W := by
  rw [leavesOfC.costEq P hP]
  rw [show max 64 (8 * 64) = 512 by norm_num]
  have hT := transcriptIndex_cost P (by includes) D 512 W hW (by norm_num) qs hN
  have hS := subtreeLeavesWithC_cost P (by includes) _
    (.closure leavesOfC.lam0.costIdx [encodeValue (transcriptIndex qs 512)])
    (fun d n ↦ RunsApp.of_spec (leavesOfC.lam0.costSpec P (by includes) _ d n))
    (D * (20 + (162 + 9 * W) * (D + 2)) + 42)
    (fun d n hn ↦ preimageLookup_cost P (by includes) qs 512 D W (by norm_num) hW hN d n hn)
    64 (by norm_num) h root
  rw [limbs_of_lt (by norm_num : (64 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : 8 * 64 < 2 ^ 64)]
  have e : D * (20 + (162 + 9 * W) * (D + 2)) + 42 + 15 * 64 + 30725 +
      (D * (20 + (162 + 9 * W) * (D + 2)) + 42 + 453 * 64 + 35) + 5 * h =
      2 * (D * (20 + (162 + 9 * W) * (D + 2)) + 42) + 60712 + 5 * h := by ring
  rw [e] at hS
  unfold transcriptIndexPrice committedLeavesPrice
  simp only [show (64 : ℕ) ≤ 8 * 64 from by norm_num, ↓reduceIte]
  omega

/-! ## The bytecode's words -/

/-- An instruction's entry (`busEntry.c687`): at most `145`. -/
theorem entryC_cost (hP : Includes P Auto.LeanVM.Arithmetization.busEntry.c687.costDeps) (i :
    LeanIsaInstruction) :
    machineCost P Auto.LeanVM.Arithmetization.busEntry.c687.costIdx [encodeValue i] ≤ 145 := by
  rw [Auto.LeanVM.Arithmetization.busEntry.c687.costEq P hP]
  cases i with
  | deref o1 o2 o3 mode =>
    dsimp only
    rw [Auto.LeanVM.Arithmetization.derefFlags.c688.costEq P (by includes)]
    cases mode <;> dsimp only <;> omega
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    dsimp only
    rw [Auto.Fin.ofNat.c252.costEq P (by includes), Auto.Fin.ofNat.c252.costEq P (by includes),
      Auto.Fin.ofNat.c252.costEq P (by includes), Auto.Fin.ofNat.c252.costEq P (by includes)]
    simp only [Auto.LeanVM.Arithmetization.layoutFlagWord.c689.costEq P (by includes),
      limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (1 : ℕ) < 2 ^ 64),
      limbs_of_lt (by norm_num : (2 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (3 : ℕ) < 2 ^ 64)]
    cases outCells <;> simp only [ite_self] <;> omega
  | _ => dsimp only; omega

/-- **The bytecode's words** (`bytecodeWordsC`): at most `5712·2^ℓ + 947`. -/
theorem bytecodeWordsC_cost (hP : Includes P bytecodeWordsC.costDeps) (prog :
    Semantics.LeanIsaProgram) :
    machineCost P bytecodeWordsC.costIdx [encodeValue prog] ≤ bytecodeWordsPrice prog.logSize := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have h2 : 2 ^ prog.logSize < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [bytecodeWordsC.costEq P hP]
  have h1 := finRangeFrom_cost P (by includes) 16 (by norm_num) 0 (by norm_num)
  have hin : ∀ s : Fin 16, appCost P (.closure bytecodeWordsC.lam0.costIdx [encodeValue prog]) [encodeValue s] ≤
      346 * 2 ^ prog.logSize + 21 := by
    intro s
    simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    rw [bytecodeWordsC.lam0.costEq P (by includes), Nat.one_shiftLeft, limbs_of_lt h2,
      limbs_of_lt (lt_of_le_of_lt hls (by norm_num) : prog.logSize < 2 ^ 64)]
    have hf := finRangeFrom_cost P (by includes) (2 ^ prog.logSize) h2 0 (Nat.zero_le _)
    have hm := map_cost P (by includes) _ (.closure bytecodeWordsC.lam0.lam0.costIdx [encodeValue prog, encodeValue s])
      (fun i ↦ RunsApp.of_spec (bytecodeWordsC.lam0.lam0.costSpec P (by includes) prog s i)) 320
      (List.finRange (2 ^ prog.logSize)) (fun i _ ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [bytecodeWordsC.lam0.lam0.costEq P (by includes),
          Auto.LeanVM.Arithmetization.instructionSlots.c686.costEq P (by includes)]
        have := entryC_cost P (by includes) (prog.instructions i)
        omega)
    rw [List.length_finRange] at hm
    simp only [Nat.sub_zero] at hf
    omega
  have hm := map_cost P (by includes) _ (.closure bytecodeWordsC.lam0.costIdx [encodeValue prog])
    (fun s ↦ RunsApp.of_spec (bytecodeWordsC.lam0.costSpec P (by includes) prog s))
    (346 * 2 ^ prog.logSize + 21) (List.finRange 16) (fun s _ ↦ hin s)
  have hfl := flatten_cost P (by includes) (2 ^ prog.logSize)
    ((List.finRange 16).map fun s ↦ (List.finRange (2 ^ prog.logSize)).map fun i ↦
      (LeanVM.Arithmetization.instructionSlots (prog.instructions i))[s])
    (fun l hl ↦ by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hl
      simp)
  simp only [List.length_finRange, List.length_map] at hm hfl
  unfold bytecodeWordsPrice
  omega

/-! ## The stacks -/

/-- **The fast path** on the committed leaves (`fastOfC`, width `64`). -/
theorem fastOfC_cost (hP : Includes P fastOfC.costDeps) (μ R : ℕ) (hμ : μ ≤ 40) (hR : R ≤ 8)
    (leaves : Array (List K)) (h : ℕ) (hh : h < 64) (hl : ∀ l ∈ leaves, l.length ≤ 64) :
    machineCost P fastOfC.costIdx [encodeValue μ, encodeValue R, encodeValue leaves, encodeValue h, encodeValue 64] ≤
      fastPathPrice μ R 64 23 + 10 := by
  rw [fastOfC.costEq P hP]
  have := fastStacksFast_cost P (by includes) μ R hμ hR _
    (.closure fastOfC.lam0.costIdx [encodeValue leaves, encodeValue h, encodeValue 64])
    (fun a ↦ RunsApp.of_spec (fastOfC.lam0.costSpec P (by includes) leaves h 64 a))
    (15 * 64 + 23) 64
    (fun v hv ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [fastOfC.lam0.costEq P (by includes)]
      have := leafAt_cost P (by includes) leaves h 64 v hh hv (by norm_num)
      omega)
    (fun v ↦ leafAt_length_le leaves h 64 v hl)
  unfold fastPathPrice
  simp only [show Whir.initialFold = 6 from rfl] at this
  omega

/-- A stack's run on `afterRootLite`'s layouts: at most `stackRunPrice κ ℓ`. -/
theorem runWithTables_le (hP : Includes P runWithTablesC.costDeps) (prog : Semantics.LeanIsaProgram)
    (input : PublicInput) (L : LayoutLite) (hf : LayoutFacts L) (q : Vector K (2 ^ L.stackLog)) :
    machineCost P runWithTablesC.costIdx
        [encodeValue (runnerTables prog L), encodeValue prog, encodeValue input, encodeValue L, encodeValue q] ≤
      stackRunPrice L.logMemory prog.logSize := by
  have h2 := runWithTables_cost P hP prog input L hf.logMemory_le hf.logBytecode_le
    hf.heights_le hf.heights_length hf.index_lt_word q
  have h3 := stepCapLite_le L hf.logMemory_le hf.logBytecode_le hf.heights_le hf.heights_length
  have h4 := Nat.mul_le_mul_left (runnerStepPrice L.logMemory prog.logSize + 41) h3
  unfold stackRunPrice
  omega

/-- **The candidate runs** (`runBothC`): the tables, at most one fast stack, then the decoder's
stacks (`S` their price, at most `2^12` of them). -/
theorem runBothC_cost (hP : Includes P runBothC.costDeps) (prog : Semantics.LeanIsaProgram)
    (input : PublicInput) (L : LayoutLite) (hf : LayoutFacts L)
    (fastSts : List (Vector K (2 ^ L.stackLog))) (hfs : fastSts.length ≤ 1)
    (slow : Unit → List (Vector K (2 ^ L.stackLog))) (slowVal : MachineValue)
    (hslow : ∀ a, RunsApp P slowVal [encodeValue a] (encodeValue (slow a))) (S : ℕ)
    (hS : appCost P slowVal [encodeValue ()] ≤ S) (hsl : (slow ()).length ≤ 2 ^ 12) :
    machineCost P runBothC.costIdx [encodeValue prog, encodeValue input, encodeValue L, encodeValue fastSts, slowVal] ≤
      runnerTablesPrice L.logMemory prog.logSize + (stackRunPrice L.logMemory prog.logSize + 21) * (2 ^ 12 + 1) +
        S + 56 := by
  rw [runBothC.costEq P hP prog input L fastSts slow slowVal hslow]
  have hT : machineCost P runnerTablesC.costIdx [encodeValue prog, encodeValue L] ≤
      runnerTablesPrice L.logMemory prog.logSize :=
    runnerTables_cost P (by includes) prog L hf.logMemory_le hf.logBytecode_le hf.heights_le
      hf.heights_length
  have hspec : ∀ q : Vector K (2 ^ L.stackLog), RunsApp P (.closure runBothC.lam0.lam0.costIdx
      [encodeValue prog, encodeValue input, encodeValue L, encodeValue (runnerTables prog L)]) [encodeValue q]
      (encodeValue (runWithTables (runnerTables prog L) prog input L q)) := fun q ↦ RunsApp.of_spec
    (us := [encodeValue prog, encodeValue input, encodeValue L, encodeValue (runnerTables prog L)]) (vs := [encodeValue q])
    (runBothC.lam0.lam0.costSpec P (by includes) prog input L (runnerTables prog L) q)
  have hrun : ∀ q : Vector K (2 ^ L.stackLog), appCost P (.closure runBothC.lam0.lam0.costIdx
      [encodeValue prog, encodeValue input, encodeValue L, encodeValue (runnerTables prog L)]) [encodeValue q] ≤
      stackRunPrice L.logMemory prog.logSize + 10 := by
    intro q
    simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    rw [runBothC.lam0.lam0.costEq P (by includes)]
    have := runWithTables_le P (by includes) prog input L hf q
    omega
  have hF1 := findSome_cost P (by includes) _ _ hspec _ fastSts (fun q _ ↦ hrun q)
  have hF2 := findSome_cost P (by includes) _ _ hspec _ (slow ()) (fun q _ ↦ hrun q)
  have hm1 := Nat.mul_le_mul_left (stackRunPrice L.logMemory prog.logSize + 10 + 11) hfs
  have hm2 := Nat.mul_le_mul_left (stackRunPrice L.logMemory prog.logSize + 10 + 11) hsl
  rw [Auto.Option.orElse.c691.costEq P (by includes) _
    (fun _ ↦ (slow ()).findSome? (runWithTables (runnerTables prog L) prog input L))
    (.closure runBothC.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue L, slowVal, encodeValue (runnerTables prog L)])
    (fun x ↦ RunsApp.of_spec (runBothC.lam0.costSpec P (by includes) prog input L slow slowVal hslow
      (runnerTables prog L) x))]
  have hlam : appCost P (.closure runBothC.lam0.costIdx
      [encodeValue prog, encodeValue input, encodeValue L, slowVal, encodeValue (runnerTables prog L)]) [encodeValue ()] ≤
      S + (stackRunPrice L.logMemory prog.logSize + 10 + 11) * 2 ^ 12 + 21 := by
    simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    rw [runBothC.lam0.costEq P (by includes) prog input L slow slowVal hslow]
    omega
  generalize List.findSome? (runWithTables (runnerTables prog L) prog input L) fastSts = o
  cases o <;> dsimp only <;> nlinarith

/-- **The decoder** on the committed leaves (`decOfC`, width `64`), at every admissible shape: the
lanes interpolated on `pmSolver` (`PMLane.decodeStacksPMC_cost_worst`, at most
`pmDecoderBudget μ` beyond the word's reads), `listDecoderWorstPrice μ`. -/
theorem decOfC_cost (hP : Includes P decOfC.costDeps) {μ R : ℕ} (hadm : Whir.Admissible μ R)
    (leaves : Array (List K)) (h : ℕ) (hh : h < 64) (hl : ∀ l ∈ leaves, l.length ≤ 64) :
    machineCost P decOfC.costIdx [encodeValue μ, encodeValue R, encodeValue leaves, encodeValue h, encodeValue 64] ≤
      1751 * 2 ^ 30 + listDecoderWorstPrice μ + 10 := by
  rw [decOfC.costEq P hP]
  have := PMLane.decodeStacksPMC_cost_worst P (by includes_sub) hadm _
    (.closure fastOfC.lam0.costIdx [encodeValue leaves, encodeValue h, encodeValue 64])
    (fun a ↦ RunsApp.of_spec (fastOfC.lam0.costSpec P (by includes_sub) leaves h 64 a))
    (BW := 15 * 64 + 23) (Lw := 64)
    (fun v hv ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [fastOfC.lam0.costEq P (by includes_sub)]
      have := leafAt_cost P (by includes_sub) leaves h 64 v hh hv (by norm_num)
      omega)
    (fun v ↦ leafAt_length_le leaves h 64 v hl)
  unfold listDecoderWorstPrice
  unfold PMLane.pmDecoderBudget at this
  omega

/-! ## The stages -/

/-- **The candidate runs from the committed leaves** (`runFromLeavesC`, width `64`). -/
theorem runFromLeavesC_cost (hP : Includes P runFromLeavesC.costDeps) (prog :
    Semantics.LeanIsaProgram)
    (input : PublicInput) (L : LayoutLite) (R : ℕ) (hf : LayoutFacts L)
    (hadm : Whir.Admissible L.stackLog R) (leaves : Array (List K)) (h : ℕ) (hh : h < 64)
    (hl : ∀ l ∈ leaves, l.length ≤ 64) :
    machineCost P runFromLeavesC.costIdx [encodeValue prog, encodeValue input, encodeValue L, encodeValue R, encodeValue leaves, encodeValue h, encodeValue 64] ≤
      fastPathPrice L.stackLog R 64 23 + runnerTablesPrice L.logMemory prog.logSize +
        (stackRunPrice L.logMemory prog.logSize + 21) * (2 ^ 12 + 1) + listDecoderPrice L.stackLog + 92 := by
  have hadm' := hadm
  obtain ⟨-, h2, -, h4⟩ := hadm'
  simp only [Whir.maxLogStack] at h2
  rw [runFromLeavesC.costEq P hP]
  have hF := fastOfC_cost P (by includes_sub) L.stackLog R (by omega) (by omega) leaves h hh hl
  have hslow : ∀ x : Unit, RunsApp P (.closure runFromLeavesC.lam0.costIdx
      [encodeValue L, encodeValue R, encodeValue leaves, encodeValue h, encodeValue 64]) [encodeValue x]
      (encodeValue ((fun _ : Unit ↦ decOf L.stackLog R leaves h 64) x)) := fun x ↦
    RunsApp.of_spec (runFromLeavesC.lam0.costSpec P (by includes_sub) L R leaves h 64 x)
  have hB := runBothC_cost P (by includes_sub) prog input L hf (fastOf L.stackLog R leaves h 64)
    (fastStacksFast_length_le _ _ _) (fun _ ↦ decOf L.stackLog R leaves h 64) _ hslow
    (1751 * 2 ^ 30 + listDecoderWorstPrice L.stackLog + 22)
    (by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [runFromLeavesC.lam0.costEq P (by includes_sub)]
      have := decOfC_cost P (by includes_sub) hadm leaves h hh hl
      omega)
    (by
      show (decodeStacksDistinctPM L.stackLog R (leafAt leaves h 64)).length ≤ 2 ^ 12
      rw [decodeStacksDistinctPM_eq hadm]
      exact decodeStacksDistinct_length_le_johnson hadm _)
  unfold listDecoderPrice
  omega

/-- **A stage** (`stageTC`) at the root `afterRootLite` returns: the committed leaves, the runs. -/
theorem stageTC_cost (hP : Includes P stageTC.costDeps) (prog : Semantics.LeanIsaProgram)
    (input : PublicInput) (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hN : qs.length + 2 ≤ 2 ^ D)
    {bytecode : List K} {π : Proof}
    {L : LayoutLite} {R : ℕ} {st : VerifierProgramState} (har : afterRootLite bytecode π = some ((L,
        R), st))
    (root : LeanVM.Protocol.Digest) :
    machineCost P stageTC.costIdx [encodeValue prog, encodeValue input, encodeValue L, encodeValue R, encodeValue qs,
        encodeValue (root, L.stackLog - 6 + R, 64)] ≤
      afterRootStagePrice L.stackLog R L.logMemory prog.logSize D qs.length (L.stackLog - 6 + R) W := by
  obtain ⟨hf, hμ1, hμ2, hR1, hR2, -⟩ := afterRootLite_facts har
  have hadm := admissible_of_afterRootLite har
  rw [stageTC.costEq P hP]
  dsimp only
  have hL := leavesOfC_cost P (by includes_sub) qs D W hW hN (L.stackLog - 6 + R) root
  have hR := runFromLeavesC_cost P (by includes_sub) prog input L R hf hadm
    (leavesOf qs 64 (L.stackLog - 6 + R) root) (L.stackLog - 6 + R) (by omega)
    (fun l hl ↦ (subtreeLeavesWith_mem_length _ _ _ _ l hl).le)
  unfold afterRootStagePrice
  omega

/-- **After the replay** (`afterRootStageC`): the root, then the stage. -/
theorem afterRootStageC_cost (hP : Includes P afterRootStageC.costDeps) (prog :
    Semantics.LeanIsaProgram)
    (input : PublicInput) (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hN : qs.length + 2 ≤ 2 ^ D)
    {bytecode : List K} {π : Proof}
    {L : LayoutLite} {R : ℕ} {st : VerifierProgramState} (har : afterRootLite bytecode π = some ((L,
        R), st)) :
    machineCost P afterRootStageC.costIdx [encodeValue prog, encodeValue input, encodeValue qs, encodeValue ((L, R), st)] ≤
      afterRootStagePrice L.stackLog R L.logMemory prog.logSize D qs.length (L.stackLog - 6 + R) W + 43 := by
  obtain ⟨root, hroots⟩ := afterRootLite_roots har
  have hI := includes_afterRootStageLam P hP
  have hI2 := includes_stageTC P hP
  have hk : ∀ t : LeanVM.Protocol.Digest × ℕ × ℕ, RunsApp P
      (.closure afterRootStageC.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue qs, encodeValue R, encodeValue L]) [encodeValue t]
      (encodeValue (stageT prog input L R qs t)) := fun t ↦
    RunsApp.of_spec (us := [encodeValue prog, encodeValue input, encodeValue qs, encodeValue R, encodeValue L]) (vs := [encodeValue t])
      (afterRootStageC.lam0.costSpec P hI prog input qs R L t)
  have hb := Auto.Option.bind.c154.costEq P (by includes) st.roots.head? (stageT prog input L R qs)
    _ hk
  have hlam := afterRootStageC.lam0.costEq P hI prog input qs R L
    (root, L.stackLog - 6 + R, 64)
  have hst := stageTC_cost P hI2 prog input qs D W hW hN har root
  rw [afterRootStageC.costEq P hP]
  simp only [hroots, List.head?_cons] at hb ⊢
  simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hb
  omega

/-! ## The extractor -/

/-- The price where the replay fails: the bytecode's words and the replay. -/
@[expose] def replayPrice (ℓ : ℕ) : ℕ := bytecodeWordsPrice ℓ + (128 * 2 ^ ℓ + 977131026) + 15

/-- **The compiled extractor's price** (`extractorC`), on every input: at most `extractorPrice` at the shape `afterRootLite` announces, or
`replayPrice` when the replay fails. -/
theorem extractorC_cost (hP : Includes P extractorC.costDeps) (prog : Semantics.LeanIsaProgram)
    (input : PublicInput) (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (π : Proof) :
    machineCost P extractorC.costIdx [encodeValue prog, encodeValue input, encodeValue qs, encodeValue π] ≤
      match afterRootLite (bytecodeWords prog) π with
      | none => replayPrice prog.logSize
      | some ((L, R), _) => extractorPrice L.stackLog R L.logMemory prog.logSize qs.length := by
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have hbc := bytecodeWords_length prog
  have hW := bytecodeWordsC_cost P (includes_bytecodeWordsC P hP) prog
  have hA := afterRootLite_cost P (includes_afterRootLiteC P hP) (bytecodeWords prog) π (by
    rw [hbc]
    have : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hls
    omega)
  rw [hbc] at hA
  have hI0 := includes_extractorLam P hP
  have hk : ∀ r : (LayoutLite × ℕ) × VerifierProgramState, RunsApp P
      (.closure extractorC.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue qs]) [encodeValue r]
      (encodeValue (afterRootStage prog input qs r)) := fun r ↦
    RunsApp.of_spec (us := [encodeValue prog, encodeValue input, encodeValue qs]) (vs := [encodeValue r])
      (extractorC.lam0.costSpec P hI0 prog input qs r)
  rw [extractorC.costEq P hP, Auto.Option.bind.c154.costEq P (includes_bindC P hP)
    (afterRootLite (bytecodeWords prog) π) (afterRootStage prog input qs) _ hk]
  cases har : afterRootLite (bytecodeWords prog) π with
  | none =>
    show _ ≤ bytecodeWordsPrice prog.logSize + (128 * 2 ^ prog.logSize + 977131026) + 15
    dsimp only
    omega
  | some r =>
    obtain ⟨⟨L, R⟩, st⟩ := r
    show _ ≤ bytecodeWordsPrice prog.logSize + (128 * 2 ^ prog.logSize + 977131026) +
      afterRootStagePrice L.stackLog R L.logMemory prog.logSize (Nat.log2 (qs.length + 2) + 1) qs.length
        (L.stackLog - 6 + R) (limbsBelowTwoPow (Nat.log2 (qs.length + 2) + 1 + 1)) + 69
    simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    have hl := extractorC.lam0.costEq P hI0 prog input qs ((L, R), st)
    have hN : qs.length + 2 ≤ 2 ^ (Nat.log2 (qs.length + 2) + 1) := Nat.le_of_lt Nat.lt_log2_self
    have hs := afterRootStageC_cost P (includes_afterRootStageC P hP) prog input qs _ _
      limbs_le_wl_two hN har
    omega

/-! ## The statement's budget -/

/-- The extractor's price but its list decoder's part (`listDecoderWorstPrice`), the part the
statement's budget pays for with its constant `2^75`. -/
def extractorRest (μ R κ ℓ N : ℕ) : ℕ :=
  bytecodeWordsPrice ℓ + (128 * 2 ^ ℓ + 977131026) +
    (transcriptIndexPrice (extractorSortedMapLevels N) 512 N
        (limbsBelowTwoPow (extractorSortedMapLevels N + 1)) +
      committedLeavesPrice (extractorSortedMapLevels N) (μ - 6 + R)
        (limbsBelowTwoPow (extractorSortedMapLevels N + 1)) +
      fastPathPrice μ R 64 23 + runnerTablesPrice κ ℓ + (stackRunPrice κ ℓ + 21) * (2 ^ 12 + 1) +
      (1751 * 2 ^ 30 + 22) + 133) + 69

theorem extractorPrice_split (μ R κ ℓ N : ℕ) :
    extractorPrice μ R κ ℓ N = extractorRest μ R κ ℓ N + listDecoderWorstPrice μ := by
  unfold extractorPrice extractorRest afterRootStagePrice listDecoderPrice
  omega

/-- The rest grows with the shape: at most the worst admissible one's, `(32, 4)` with
`κ = ℓ = 32`. -/
theorem extractorRest_le_worst {μ R κ ℓ N : ℕ} (hμ : μ ≤ 32) (hR : R ≤ 4) (hκ : κ ≤ 32)
    (hℓ : ℓ ≤ 32) : extractorRest μ R κ ℓ N ≤ extractorRest 32 4 32 32 N := by
  unfold extractorRest fastPathPrice runnerTablesPrice stackRunPrice runnerStepPrice
    committedLeavesPrice bytecodeWordsPrice
  gcongr

/-- **The worst shape's rest within `2^75` and the budget's second term**, the entry's `14`
included, for every number of queries: monomial by monomial in `N` and the levels `D`, the
positions' limbs `W` at most `(D + 65)/64`. -/
theorem extractorRest_worst_le (N : ℕ) : extractorRest 32 4 32 32 N + 14 ≤
    2 ^ 75 + (N + 2 ^ 30) * (Nat.log2 (N + 2) + 3) ^ 2 * (2 ^ 15 + 2 * (Nat.log2 (N + 2) + 1)) := by
  unfold extractorRest extractorSortedMapLevels
  have hW : 64 * limbsBelowTwoPow (Nat.log2 (N + 2) + 1 + 1) ≤ Nat.log2 (N + 2) + 1 + 65 := by
    unfold limbsBelowTwoPow; omega
  generalize limbsBelowTwoPow (Nat.log2 (N + 2) + 1 + 1) = W at hW ⊢
  generalize Nat.log2 (N + 2) = D at hW ⊢
  unfold transcriptIndexPrice committedLeavesPrice replayStepPrice
    firstAnswersStepPrice preimageStepPrice fastPathPrice runnerTablesPrice stackRunPrice
    runnerStepPrice bytecodeWordsPrice
  norm_num
  nlinarith [Nat.mul_le_mul_right (N * (D + 1) ^ 2) hW, Nat.mul_le_mul_right (N * (D + 1)) hW,
    Nat.mul_le_mul_right N hW, Nat.mul_le_mul_right ((D + 1) ^ 2) hW,
    Nat.mul_le_mul_right (D + 1) hW, Nat.zero_le (N * D ^ 3), Nat.zero_le (N * D ^ 2),
    Nat.zero_le (N * D), Nat.zero_le (D ^ 3), Nat.zero_le (D ^ 2)]

/-- The decoder's part and `2^75` are the budget's first term. -/
theorem listDecoderWorstPrice_add (μ : ℕ) :
    listDecoderWorstPrice μ + 2 ^ 75 = 2 ^ max 81 (2 * μ + 22) := by
  unfold listDecoderWorstPrice
  have : 2 ^ 75 ≤ 2 ^ max 81 (2 * μ + 22) :=
    Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num) (le_max_left _ _))
  omega

/-- **Every admissible shape's price within the statement's budget at its stack size**
(`leanVmKnowledgeExtractorBudget`), the entry's `14` included, for every number of queries. -/
theorem extractorPrice_le_budget {μ R κ ℓ : ℕ} (N : ℕ) (hμ : μ ≤ 32) (hR : R ≤ 4) (hκ : κ ≤ 32)
    (hℓ : ℓ ≤ 32) : extractorPrice μ R κ ℓ N + 14 ≤ leanVmKnowledgeExtractorBudget μ N := by
  rw [extractorPrice_split]
  have h1 := extractorRest_le_worst (N := N) hμ hR hκ hℓ
  have h2 := extractorRest_worst_le N
  have h3 := listDecoderWorstPrice_add μ
  unfold leanVmKnowledgeExtractorBudget
  omega

/-- The stack size the statement's budget reads is the one `afterRoot` announces. -/
theorem announcedStackLog_of_afterRoot {prog : Semantics.LeanIsaProgram} {π : Proof} {layout : Layout}
    {R : ℕ} {st : VerifierProgramState}
    (ha : afterRoot (bytecodeWords prog) π = some ((layout, R), st)) :
    announcedStackLog prog π = layout.stackLog := by
  unfold announcedStackLog
  rw [Extraction.Fast.announced_of_afterRoot ha]
  rfl

/-- **The price within the budget** (the hypothesis `hcost` of `extractorTop_output`,
`Cost/Efficient.lean`): wherever `afterRoot` announces a shape, the compiled extractor's price and the
entry's `14` are within `leanVmKnowledgeExtractorBudget` at the announced stack size, on every
transcript (`extractorC_cost` at the shape `afterRootLite_facts` bounds, `extractorPrice_le_budget`). -/
theorem extractorC_within (hP : Includes P extractorC.costDeps) (prog : Semantics.LeanIsaProgram)
    (input : PublicInput) (T : Common.OracleQueryLog) (π : Proof) (layout : Layout)
    (logInverseRate : ℕ) (st : VerifierProgramState)
    (ha : afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st)) :
    machineCost P extractorC.costIdx [encodeValue prog, encodeValue input, encodeValue (permutationQueries T), encodeValue π] + 14 ≤
      leanVmKnowledgeExtractorBudget (announcedStackLog prog π) (permutationQueries T).length := by
  have h := extractorC_cost P hP prog input (permutationQueries T) π
  have hl : afterRootLite (bytecodeWords prog) π = some ((layoutLite layout, logInverseRate), st) := by
    rw [afterRootLite_eq, ha]; rfl
  rw [hl] at h
  dsimp only at h
  obtain ⟨hf, -, hμ, -, hR, -⟩ := afterRootLite_facts hl
  have hb := extractorPrice_le_budget (permutationQueries T).length hμ hR hf.logMemory_le
    prog.logSize_le
  rw [announcedStackLog_of_afterRoot ha]
  exact le_trans (Nat.add_le_add_right h _) hb

/-! ## At `(32, 4)` -/

theorem stageBound_mono {μ R κ ℓ D D' N N' h W W' : ℕ} (hD : D ≤ D') (hN : N ≤ N') (hW : W ≤ W') :
    afterRootStagePrice μ R κ ℓ D N h W ≤ afterRootStagePrice μ R κ ℓ D' N' h W' := by
  unfold afterRootStagePrice transcriptIndexPrice committedLeavesPrice replayStepPrice firstAnswersStepPrice preimageStepPrice
  gcongr

/-- **The extractor's price at `(μ, R) = (32, 4)`**, `κ = ℓ = 32`, at most `2^40` queries: at
most `77333585604662706796546663 ≈ 2^86`, the decoder's part dominating. -/
theorem extractorPrice_32_4 (N : ℕ) (hN : N ≤ 2 ^ 40) :
    extractorPrice 32 4 32 32 N ≤ 77333585604662706796546663 := by
  have hD : Nat.log2 (N + 2) + 1 ≤ 41 := by
    have := (Nat.log2_lt (n := N + 2) (k := 41) (by omega)).2 (by omega)
    omega
  have hW : limbsBelowTwoPow (Nat.log2 (N + 2) + 1 + 1) ≤ 1 := by unfold limbsBelowTwoPow; omega
  have h := stageBound_mono (μ := 32) (R := 4) (κ := 32) (ℓ := 32) (h := 32 - 6 + 4) hD hN hW
  unfold extractorPrice
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left h _) _) ?_
  unfold afterRootStagePrice transcriptIndexPrice committedLeavesPrice replayStepPrice firstAnswersStepPrice preimageStepPrice
    fastPathPrice runnerTablesPrice stackRunPrice runnerStepPrice listDecoderPrice listDecoderWorstPrice bytecodeWordsPrice
  norm_num

/-- **The extractor's price at `(32, 4)` for up to `2^128` queries** (the soundness statement's
adversaries), `κ = ℓ = 32`: at most `165504966199035608965569201228165011834261241857 ≈ 2^156.86`,
the transcript's index dominating (`D = 129` levels of binary searches, positions of `3` limbs). -/
theorem extractorPrice_32_4_2_128 (N : ℕ) (hN : N ≤ 2 ^ 128) :
    extractorPrice 32 4 32 32 N ≤ 165504966199035608965569201228165011834261241857 := by
  have hD : Nat.log2 (N + 2) + 1 ≤ 129 := by
    have := (Nat.log2_lt (n := N + 2) (k := 129) (by omega)).2 (by omega)
    omega
  have hW : limbsBelowTwoPow (Nat.log2 (N + 2) + 1 + 1) ≤ 3 := by unfold limbsBelowTwoPow; omega
  have h := stageBound_mono (μ := 32) (R := 4) (κ := 32) (ℓ := 32) (h := 32 - 6 + 4) hD hN hW
  unfold extractorPrice
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_left h _) _) ?_
  unfold afterRootStagePrice transcriptIndexPrice committedLeavesPrice replayStepPrice firstAnswersStepPrice preimageStepPrice
    fastPathPrice runnerTablesPrice stackRunPrice runnerStepPrice listDecoderPrice listDecoderWorstPrice bytecodeWordsPrice
  norm_num

end

end LeanVM.Cost.Bounds
