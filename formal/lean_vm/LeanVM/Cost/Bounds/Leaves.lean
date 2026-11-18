module

public import LeanVM.Cost.Bounds.TranscriptReplay
public import LeanVM.Cost.Bounds.Step
public import LeanVM.Cost.Extractor.Top
import all Statement.LeanIsa
import all LeanVM.Protocol.Extraction.Extractor
import all LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.SortedMap
public import LeanVM.Cost.Prices

/-!
# Bounds: a root's committed leaves and the bytecode's words

* the committed leaves on the chain: `bytesWordC_cost` (`296`), `bytesLanesC_cost` (`439` per
  word), `leafOfWithC_cost`, `bytesDigestC_cost` (`7428`: its four words each through
  `bytesLanes 4`), `subtreeLeavesWithC_cost` (by doubling), a lookup in the transcript's index
  `preimageLookup_cost` (`D·(20 + (162 + 9W)·(D + 2)) + 42`, its keys `PreKey`:
  `transcriptIndex_keys`);
* the bytecode's words: `bytecodeWords_length` (`16·2^ℓ`), **`bytecodeWordsC_cost`**
  (`bytecodeWordsPrice ℓ = 5712·2^ℓ + 947`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

public section

attribute [local instance] lexOrd

variable (P : LeanVM.Cost.MachineProgram)

theorem bytecodeWords_length (prog : Semantics.LeanIsaProgram) :
    (LeanVM.bytecodeWords prog).length = 16 * 2 ^ prog.logSize := by
  simp [LeanVM.bytecodeWords, List.length_flatMap]
  omega

/-! ## Lists on bytes -/

theorem foldr_bytes_lt' (l : List UInt8) :
    l.foldr (fun x acc ↦ x.toNat + 256 * acc) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have := x.toNat_lt
    simp only [List.foldr_cons, List.length_cons, pow_succ]
    nlinarith

/-- **A word of bytes** (`bytesWord.c257`): at most `296`. -/
theorem bytesWordC_cost (hP : Includes P Auto.LeanVM.Extraction.bytesWord.c257.costDeps)
    (b : List UInt8) :
    machineCost P Auto.LeanVM.Extraction.bytesWord.c257.costIdx [encodeValue b] ≤ 296 := by
  rw [Auto.LeanVM.Extraction.bytesWord.c257.costEq P hP]
  have ht := take_cost P (by includes) 8 b (by norm_num)
  have hl : (b.take 8).length ≤ 8 := List.length_take_le _ _
  have hf := foldrSuffix_cost P (by includes) _
    (.closure Auto.LeanVM.Extraction.bytesWord.c257.lam0.costIdx [])
    (fun a acc ↦ RunsApp.of_spec
      (Auto.LeanVM.Extraction.bytesWord.c257.lam0.costSpec P (by includes) a acc)) 5 0 (b.take 8)
    (fun x tl h ↦ by
      have hlen : tl.length ≤ 7 := by have := h.length_le; simp at this; omega
      have hacc := foldr_bytes_lt' tl
      have : 256 ^ tl.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) hlen
      have hx := x.toNat_lt
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Extraction.bytesWord.c257.lam0.costEq P (by includes),
        limbs_of_lt (by omega), limbs_of_lt (by omega), limbs_of_lt (by omega),
        limbs_of_lt (by omega : x.toNat < 2 ^ 64), List.length_nil]
      omega)
  have hv := foldr_bytes_lt' (b.take 8)
  have h8 : 256 ^ (b.take 8).length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
  rw [limbs_of_lt (lt_of_lt_of_le hv (h8.trans (by norm_num)))]
  nlinarith

/-- **The first `n` words of bytes** (`bytesLanes.c256`): at most `439·n + 5`. -/
theorem bytesLanesC_cost (hP : Includes P Auto.LeanVM.Extraction.bytesLanes.c256.costDeps) :
    ∀ (n : ℕ) (b : List UInt8), n < 2 ^ 64 →
      machineCost P Auto.LeanVM.Extraction.bytesLanes.c256.costIdx [encodeValue n, encodeValue b] ≤ 439 * n + 5 := by
  intro n
  induction n with
  | zero => intro b _; rw [Auto.LeanVM.Extraction.bytesLanes.c256.costEq P hP]; simp [limbs_of_lt]
  | succ k ih =>
    intro b hk
    rw [Auto.LeanVM.Extraction.bytesLanes.c256.costEq P hP, limbs_of_lt hk]
    have := ih (b.drop 8) (by omega)
    have := bytesWordC_cost P (by includes) b
    have := drop_cost P (by includes) 8 b (by norm_num)
    dsimp only
    omega

/-- **A leaf** (`leafOfWith.c254`): at most `L + 453·w + 21`, `L` the lookup's price. -/
theorem leafOfWithC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.leafOfWith.c254.costDeps)
    (pre : LeanVM.Protocol.Digest → ℕ → Option (List UInt8)) (preVal : MachineValue)
    (hpre : ∀ d n, RunsApp P preVal [encodeValue d, encodeValue n] (encodeValue (pre d n))) (L : ℕ)
    (hL : ∀ (d : LeanVM.Protocol.Digest) (n : ℕ), n < 2 ^ 64 → appCost P preVal [encodeValue d, encodeValue n] ≤ L)
    (w : ℕ) (hw : w < 2 ^ 61) (d : LeanVM.Protocol.Digest) :
    machineCost P Auto.LeanVM.Extraction.Fast.leafOfWith.c254.costIdx [preVal, encodeValue w, encodeValue d] ≤
      L + 453 * w + 21 := by
  rw [Auto.LeanVM.Extraction.Fast.leafOfWith.c254.costEq P hP pre preVal hpre,
    limbs_of_lt (by omega : w < 2 ^ 64), limbs_of_lt (by omega : 8 * w < 2 ^ 64), max_self]
  have := hL d (8 * w) (by omega)
  have := replicate_cost P (by includes) (0 : K) w (by omega)
  generalize pre d (8 * w) = o
  cases o with
  | none => dsimp only; omega
  | some val =>
    have := bytesLanesC_cost P (by includes) w val (by omega)
    have := map_cost P (by includes) _
      (.closure Auto.LeanVM.Extraction.Fast.leafOfWith.c254.lam0.costIdx [])
      (fun a ↦ RunsApp.of_spec
        (Auto.LeanVM.Extraction.Fast.leafOfWith.c254.lam0.costSpec P (by includes) a)) 1
      (LeanVM.Extraction.bytesLanes w val)
      (fun a _ ↦ by
        rw [appCost_fn, List.nil_append,
          Auto.LeanVM.Extraction.Fast.leafOfWith.c254.lam0.costEq P (by includes), List.length_nil])
    rw [bytesLanes_length] at this
    dsimp only
    omega

/-- **A digest of bytes** (`bytesDigest.c259`, its four words each through `bytesLanes 4`): at
most `7428`. -/
theorem bytesDigestC_cost (hP : Includes P Auto.LeanVM.Extraction.bytesDigest.c259.costDeps)
    (b : List UInt8) :
    machineCost P Auto.LeanVM.Extraction.bytesDigest.c259.costIdx [encodeValue b] ≤ 7428 := by
  rw [Auto.LeanVM.Extraction.bytesDigest.c259.costEq P hP]
  have hof := ofFnFrom_cost P (by includes) (n := 4) (by norm_num) _
    (.closure Auto.LeanVM.Extraction.bytesDigest.c259.lam0.costIdx [encodeValue b])
    (fun i ↦ RunsApp.of_spec
      (Auto.LeanVM.Extraction.bytesDigest.c259.lam0.costSpec P (by includes) b i)) 1837
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Extraction.bytesDigest.c259.lam0.costEq P (by includes)]
      have := bytesLanesC_cost P (by includes) 4 b (by norm_num)
      have := getD_cost P (by includes) (LeanVM.Extraction.bytesLanes 4 b) i 0 (by omega)
      rw [bytesLanes_length] at this
      omega) 0 (by norm_num)
  rw [ofFnFrom_length]
  omega

/-- **The subtree's leaves** (`subtreeLeavesWith.c253`): with `T` its price,
`T + a ≤ 2^h·(a + b + 5·h)`, `a = L + 15·w + 30725` (an inner node) and `b = L + 453·w + 35` (a
leaf), `L` the lookup's price. -/
theorem subtreeLeavesWithC_cost
    (hP : Includes P Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c253.costDeps)
    (pre : LeanVM.Protocol.Digest → ℕ → Option (List UInt8)) (preVal : MachineValue)
    (hpre : ∀ d n, RunsApp P preVal [encodeValue d, encodeValue n] (encodeValue (pre d n))) (L : ℕ)
    (hL : ∀ (d : LeanVM.Protocol.Digest) (n : ℕ), n < 2 ^ 64 → appCost P preVal [encodeValue d, encodeValue n] ≤ L)
    (w : ℕ) (hw : w < 2 ^ 61) :
    ∀ (h : ℕ) (d : LeanVM.Protocol.Digest),
      machineCost P Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c253.costIdx
          [preVal, encodeValue w, encodeValue h, encodeValue d] + (L + 15 * w + 30725) ≤
        2 ^ h * ((L + 15 * w + 30725) + (L + 453 * w + 35) + 5 * h) := by
  have hleaf := leafOfWithC_cost P (by includes) pre preVal hpre L hL w hw
  have hrep := replicate_cost P (by includes) (0 : K) w (by omega)
  have hdig := fun (b : List UInt8) ↦ bytesDigestC_cost P (by includes) b
  have hd32 := fun (b : List UInt8) ↦ drop_cost P (by includes) 32 b (by norm_num)
  apply le_of_doubling (fun (h : ℕ) (d : LeanVM.Protocol.Digest) ↦
    machineCost P Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c253.costIdx
      [preVal, encodeValue w, encodeValue h, encodeValue d])
  · intro d
    rw [Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c253.costEq_zero P hP pre preVal hpre]
    have := hleaf d
    omega
  · intro k d
    rw [Auto.LeanVM.Extraction.Fast.subtreeLeavesWith.c253.costEq_succ P hP pre preVal hpre]
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

/-- **A preimage lookup** in the transcript's index (`leavesInC.lam0`, `preimageIn.c262`): a
binary search per level, at most `D·(20 + (162 + 9·W)·(D + 2)) + 42`. -/
theorem preimageLookup_cost (hP : Includes P leavesInC.lam0.costDeps)
    (qs : List (Common.PermutationQuery KeccakState × KeccakState)) (L D W : ℕ) (hL : L < 2 ^ 64)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hN : qs.length + 2 ≤ 2 ^ D)
    (d : LeanVM.Protocol.Digest) (len : ℕ) (hlen : len < 2 ^ 64) :
    appCost P (.closure leavesInC.lam0.costIdx [encodeValue (transcriptIndex qs L)]) [encodeValue d, encodeValue len] ≤
      D * (20 + (162 + 9 * W) * (D + 2)) + 42 := by
  simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
  rw [leavesInC.lam0.costEq P hP,
    Auto.LeanVM.Extraction.Fast.preimageIn.c262.costEq P (by includes)]
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

/-! ## The bytecode's words -/

/-- An instruction's entry (`busEntry.c249`): at most `145`. -/
theorem entryC_cost (hP : Includes P Auto.LeanVM.Arithmetization.busEntry.c249.costDeps) (i :
    LeanIsaInstruction) :
    machineCost P Auto.LeanVM.Arithmetization.busEntry.c249.costIdx [encodeValue i] ≤ 145 := by
  rw [Auto.LeanVM.Arithmetization.busEntry.c249.costEq P hP]
  cases i with
  | deref o1 o2 o3 mode =>
    dsimp only
    rw [Auto.LeanVM.Arithmetization.derefFlags.c250.costEq P (by includes)]
    cases mode <;> dsimp only <;> omega
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    dsimp only
    rw [Auto.Fin.ofNat.c129.costEq P (by includes), Auto.Fin.ofNat.c129.costEq P (by includes),
      Auto.Fin.ofNat.c129.costEq P (by includes), Auto.Fin.ofNat.c129.costEq P (by includes)]
    simp only [Auto.LeanVM.Arithmetization.layoutFlagWord.c251.costEq P (by includes),
      limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (1 : ℕ) < 2 ^ 64),
      limbs_of_lt (by norm_num : (2 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (3 : ℕ) < 2 ^ 64)]
    cases outCells <;> simp only [ite_self] <;> omega
  | _ => dsimp only; omega

/-- **The bytecode's words** (`bytecodeWordsC`): at most `5712·2^ℓ + 947`. -/
theorem bytecodeWordsC_cost (hP : Includes P bytecodeWordsC.costDeps) (prog :
    Semantics.LeanIsaProgram) :
    machineCost P bytecodeWordsC.costIdx [encodeValue prog] ≤ bytecodeWordsPrice prog.logSize := by
  have hls : prog.logSize ≤ 30 := prog.logSize_le
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
          Auto.LeanVM.Arithmetization.instructionSlots.c248.costEq P (by includes)]
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

end

end LeanVM.Cost.Bounds
