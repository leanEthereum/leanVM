module

public import LeanVM.Cost.Bounds.FastPath
public import LeanVM.Cost.Bounds.Transcript
import all LeanVM.Protocol.Extraction.Fast.SortedMap
public import LeanVM.Cost.Prices

/-!
# Bounds: the transcript's replay and its evaluations

* the byte-string helpers (`drop`, `take`, `dropWhile`, `modifyHead`, `modifyTailIdx`), the padding
  (`padBlock_cost`, `keccakPadded_cost`), `stripPad_cost` and **`keccakUnpadded_cost`**: a path's
  bytes read as a padded message, `112·|bs| + 9260`, linear (no Keccak-f: the digest is the path's
  state);
* the replay's block bytes (`blockBytes_cost`) and the cut (`cut_cost`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction
open LeanVM.Extraction.Fast LeanVM.Protocol.KeccakHash LeanVM.Semantics Common

public section

variable (P : MachineProgram)

/-! ## Byte-string helpers -/

/-- `List.dropWhile` (`dropWhile.c170`): `B + 11` per element, `B + 13` at the end. -/
theorem dropWhile336_cost (hP : Includes P Auto.List.dropWhile.c170.costDeps) {α : Type} [MachineEncoding α]
    (p : α → Bool) (pVal : MachineValue) (hp : ∀ a : α, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : ℕ)
    (hB : ∀ a : α, appCost P pVal [encodeValue a] ≤ B) :
    ∀ l : List α, machineCost P Auto.List.dropWhile.c170.costIdx [pVal, encodeValue l] ≤
      (B + 11) * l.length + B + 13 := by
  intro l
  induction l with
  | nil => rw [Auto.List.dropWhile.c170.costEq_nil P hP p pVal hp]; omega
  | cons x l ih =>
    rw [Auto.List.dropWhile.c170.costEq_cons P hP p pVal hp]
    have := hB x
    simp only [List.length_cons]
    cases p x <;> dsimp only <;> nlinarith

/-- `List.modifyHead` (`modifyHead.c177`) with a closure of price `B`: at most `B + 11`. -/
theorem modifyHead342_cost (hP : Includes P Auto.List.modifyHead.c177.costDeps) {α : Type} [MachineEncoding α]
    (f : α → α) (fVal : MachineValue) (hf : ∀ a : α, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ)
    (hB : ∀ a : α, appCost P fVal [encodeValue a] ≤ B) (l : List α) :
    machineCost P Auto.List.modifyHead.c177.costIdx [fVal, encodeValue l] ≤ B + 11 := by
  rw [Auto.List.modifyHead.c177.costEq P hP f fVal hf]
  cases l with
  | nil => dsimp only; omega
  | cons x l => have := hB x; dsimp only; omega

/-- `List.modifyTailIdx.go` (`modifyTailIdx.go.c175`): `20` per position and the closure's price. -/
theorem modifyTailIdx340_cost (hP : Includes P Auto.List.modifyTailIdx.go.c175.costDeps)
    {α : Type} [MachineEncoding α] (f : List α → List α) (fVal : MachineValue)
    (hf : ∀ a : List α, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ)
    (hB : ∀ a : List α, appCost P fVal [encodeValue a] ≤ B) :
    ∀ (n : ℕ) (l : List α), n < 2 ^ 64 →
      machineCost P Auto.List.modifyTailIdx.go.c175.costIdx [fVal, encodeValue n, encodeValue l] ≤ 20 * n + B + 7 := by
  intro n
  induction n with
  | zero =>
    intro l _
    rw [Auto.List.modifyTailIdx.go.c175.costEq P hP f fVal hf]
    have := hB l
    simp only [Nat.rec_zero, limbs_zero]
    omega
  | succ n ih =>
    intro l hn
    rw [Auto.List.modifyTailIdx.go.c175.costEq P hP f fVal hf, limbs_of_lt hn]
    cases l with
    | nil => dsimp only; omega
    | cons x l => have := ih l (by omega); dsimp only; omega

/-! ## The padding -/

theorem rate_eq : rate = 136 := rfl

/-- **The padded last block** (`padBlock.c174`) of at most `136` bytes: at most `9171`. -/
theorem padBlock_cost (hP : Includes P Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.costDeps)
    (rest : List UInt8) (hr : rest.length ≤ 136) :
    machineCost P Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.costIdx [encodeValue rest] ≤ 9171 := by
  rw [Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.costEq P hP]
  have hl := length_cost P (by includes) rest (by omega)
  have hrep := replicate_cost P (by includes) (0 : UInt8) (rate - rest.length) (by rw [rate_eq]; omega)
  have hap := append_cost P (by includes) rest (List.replicate (rate - rest.length) 0)
  have hmh : ∀ (g : UInt8 → UInt8) (gVal : MachineValue), (∀ a, RunsApp P gVal [encodeValue a] (encodeValue (g a))) →
      (∀ a, appCost P gVal [encodeValue a] ≤ 3) → ∀ l : List UInt8,
      machineCost P Auto.List.modifyHead.c177.costIdx [gVal, encodeValue l] ≤ 14 :=
    fun g gVal hg hB l ↦ modifyHead342_cost P (by includes) g gVal hg 3 hB l
  have h1 := modifyTailIdx340_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam1.costIdx [])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam1.costSpec P
      (by includes) a)) 17
    (fun a ↦ by
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam1.costEq P (by includes), List.length_nil]
      have := hmh _ (.closure Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam1.lam0.costIdx [])
        (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam1.lam0.costSpec P
          (by includes) a))
        (fun a ↦ by
          rw [appCost_fn, List.nil_append,
            Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam1.lam0.costEq P (by includes),
            List.length_nil]) a
      omega) rest.length (rest ++ List.replicate (rate - rest.length) 0) (by omega)
  have h2 := modifyTailIdx340_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam0.costSpec P
      (by includes) a)) 17
    (fun a ↦ by
      rw [appCost_fn, List.nil_append,
        Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam0.costEq P (by includes), List.length_nil]
      have := hmh _ (.closure Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam0.lam0.costIdx [])
        (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam0.lam0.costSpec P
          (by includes) a))
        (fun a ↦ by
          rw [appCost_fn, List.nil_append,
            Auto.LeanVM.Protocol.KeccakHash.padBlock.c174.lam0.lam0.costEq P (by includes),
            List.length_nil]) a
      omega) (rate - 1)
    ((rest ++ List.replicate (rate - rest.length) 0).modify rest.length fun x ↦ x ^^^ padFirst)
    (by rw [rate_eq]; omega)
  rw [limbs_of_lt (by rw [rate_eq]; omega : rate < 2 ^ 64),
    limbs_of_lt (by omega : rest.length < 2 ^ 64)]
  simp only [rate_eq, max_self] at *
  omega

/-- **The Keccak padding** (`keccakPadded.c172`) of `m`: at most `61·|m| + 9208`. -/
theorem keccakPadded_cost (hP : Includes P Auto.LeanVM.keccakPadded.c172.costDeps)
    (m : List UInt8) (hm : m.length < 2 ^ 62) :
    machineCost P Auto.LeanVM.keccakPadded.c172.costIdx [encodeValue m] ≤ 61 * m.length + 9208 := by
  rw [Auto.LeanVM.keccakPadded.c172.costEq P hP]
  have hl := length_cost P (by includes) m (by omega)
  have hk : rate * (m.length / rate) ≤ m.length := by rw [rate_eq]; exact Nat.mul_div_le _ _
  have ht := take_cost P (by includes) (rate * (m.length / rate)) m (by omega)
  have hd := drop_cost P (by includes) (rate * (m.length / rate)) m (by omega)
  have hpb := padBlock_cost P (by includes) (m.drop (rate * (m.length / rate))) (by
    rw [List.length_drop, rate_eq]
    have := Nat.mod_lt m.length (show 136 > 0 by norm_num)
    have := Nat.div_add_mod m.length 136
    omega)
  have hap := append_cost P (by includes) (m.take (rate * (m.length / rate)))
    (padBlock (m.drop (rate * (m.length / rate))))
  have htl : (m.take (rate * (m.length / rate))).length ≤ m.length := by
    rw [List.length_take]; omega
  rw [limbs_of_lt (by omega : m.length < 2 ^ 64), limbs_of_lt (by rw [rate_eq]; omega : rate < 2 ^ 64),
    limbs_of_lt (by have := Nat.div_le_self m.length rate; omega : m.length / rate < 2 ^ 64),
    limbs_of_lt (by omega : rate * (m.length / rate) < 2 ^ 64)]
  omega

theorem stripPad_length_le (bs : List UInt8) : (Common.stripPad bs).length ≤ bs.length := by
  unfold Common.stripPad
  have hr := List.length_reverse (as := bs)
  generalize bs.reverse = r at hr
  rcases r with _ | ⟨x, rest⟩
  · simp
  · simp only [List.length_cons] at hr
    split
    · rename_i h; simp only [List.cons.injEq] at h; obtain ⟨-, rfl⟩ := h; simp; omega
    · rename_i h; simp only [List.cons.injEq] at h; obtain ⟨-, rfl⟩ := h
      simp only [List.length_reverse, List.length_drop]
      have := (List.dropWhile_suffix (fun x ↦ decide (x = 0)) (l := rest)).length_le
      omega
    · simp at *

/-- `Common.stripPad` (`stripPad.c168`): at most `36·|bs| + 34`. -/
theorem stripPad_cost (hP : Includes P Auto.Common.stripPad.c168.costDeps) (bs : List UInt8)
    (hb : bs.length < 2 ^ 62) :
    machineCost P Auto.Common.stripPad.c168.costIdx [encodeValue bs] ≤ 36 * bs.length + 34 := by
  rw [Auto.Common.stripPad.c168.costEq P hP]
  have h0 := reverseAux_cost P (by includes) bs []
  have hr := List.length_reverse (as := bs)
  generalize bs.reverse = r at hr
  rcases r with _ | ⟨x, tail⟩
  · dsimp only; omega
  · simp only [List.length_cons] at hr
    dsimp only
    have h1 := reverseAux_cost P (by includes) tail []
    have h2 := dropWhile336_cost P (by includes) _ (.closure Auto.Common.stripPad.c168.lam0.costIdx [])
      (fun a ↦ RunsApp.of_spec (Auto.Common.stripPad.c168.lam0.costSpec P (by includes) a)) 3
      (fun a ↦ by rw [appCost_fn, List.nil_append, Auto.Common.stripPad.c168.lam0.costEq P
        (by includes), List.length_nil]) tail
    have h3 := drop_cost P (by includes) 1 (tail.dropWhile fun x ↦ decide (x = 0)) (by norm_num)
    have hdl := (List.dropWhile_suffix (fun x ↦ decide (x = 0)) (l := tail)).length_le
    have h4 := reverseAux_cost P (by includes) ((tail.dropWhile fun x ↦ decide (x = 0)).drop 1) []
    have : ((tail.dropWhile fun x ↦ decide (x = 0)).drop 1).length ≤ tail.length := by
      simp only [List.length_drop]; omega
    split_ifs <;> omega

/-- **A path's bytes read as a padded message** (`keccakUnpaddedFast`, `keccakUnpaddedC`): strip
the padding, pad again, compare: at most `112·|bs| + 9260`. -/
theorem keccakUnpadded_cost (hP : Includes P keccakUnpaddedC.costDeps) (bs : List UInt8)
    (hb : bs.length < 2 ^ 62) :
    machineCost P keccakUnpaddedC.costIdx [encodeValue bs] ≤ 112 * bs.length + 9260 := by
  rw [keccakUnpaddedC.costEq P hP]
  have h1 := stripPad_cost P (by includes) bs hb
  have hs := stripPad_length_le bs
  have h2 := keccakPadded_cost P (by includes) (Common.stripPad bs) (by omega)
  have h3 := bytesBeq_cost P (by includes) (LeanVM.keccakPadded (Common.stripPad bs)) bs
  split_ifs <;> omega

/-! ## The replay's block bytes and cut -/

theorem wordBytes_length (w : UInt64) : (wordBytes w).length = 8 := by
  unfold wordBytes; simp

/-- A word's bytes (`wordBytes.c161`): at most `335`. -/
theorem wordBytes_cost (hP : Includes P Auto.LeanVM.Protocol.KeccakHash.wordBytes.c161.costDeps)
    (w : UInt64) :
    machineCost P Auto.LeanVM.Protocol.KeccakHash.wordBytes.c161.costIdx [encodeValue w] ≤ 335 := by
  rw [Auto.LeanVM.Protocol.KeccakHash.wordBytes.c161.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) 8 [] (by norm_num)
  have h2 := map_cost P (by includes) _
    (.closure Auto.LeanVM.Protocol.KeccakHash.wordBytes.c161.lam0.costIdx [encodeValue w])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.KeccakHash.wordBytes.c161.lam0.costSpec P
      (by includes) w a)) 12 (List.range 8) (fun k hk ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Protocol.KeccakHash.wordBytes.c161.lam0.costEq P (by includes),
        limbs_of_lt (by have := List.mem_range.1 hk; omega : k < 2 ^ 64),
        limbs_of_lt (by have := List.mem_range.1 hk; omega : 8 * k < 2 ^ 64)]
      rfl)
  simp only [List.length_range] at h2
  omega

/-- **A block's bytes** (`blockBytes.c158`): `17` words of `8` bytes, at most `8079`. -/
theorem blockBytes_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.blockBytes.c158.costDeps) (s x : Semantics.KeccakState) :
    machineCost P Auto.LeanVM.Extraction.Fast.blockBytes.c158.costIdx [encodeValue s, encodeValue x] ≤ 8079 := by
  rw [Auto.LeanVM.Extraction.Fast.blockBytes.c158.costEq P hP]
  have h1 := rangeLoop_cost P (by includes) 17 [] (by norm_num)
  have h2 := map_cost P (by includes) _ (.closure Auto.LeanVM.Extraction.Fast.blockBytes.c158.lam0.costIdx [encodeValue s, encodeValue x])
    (fun a ↦ RunsApp.of_spec (Auto.LeanVM.Extraction.Fast.blockBytes.c158.lam0.costSpec P (by includes) s x a)) 347
    (List.range 17) (fun k _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.LeanVM.Extraction.Fast.blockBytes.c158.lam0.costEq P (by includes)]
      have := wordBytes_cost P (by includes) (Semantics.Keccak.lane s k ^^^ Semantics.Keccak.lane x k)
      omega)
  have h3 := flatten_map_cost P (by includes) 8
    (fun i ↦ wordBytes (Semantics.Keccak.lane s i ^^^ Semantics.Keccak.lane x i)) (List.range 17)
    (fun i _ ↦ (wordBytes_length _).le)
  simp only [List.length_range] at h2 h3
  omega

theorem blockBytes_length (s x : Semantics.KeccakState) : (blockBytes s x).length = 136 := by
  simp [blockBytes, wordBytes, List.length_flatMap]

/-- The cut (`cut.c156`): at most `8·|bs| + 13`. -/
theorem cut_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.cut.c156.costDeps) (B : ℕ) (hB : B < 2 ^ 64) (bs : List UInt8)
    (hb : bs.length < 2 ^ 64) : machineCost P Auto.LeanVM.Extraction.Fast.cut.c156.costIdx [encodeValue B, encodeValue bs] ≤ 8 * bs.length + 13 := by
  rw [Auto.LeanVM.Extraction.Fast.cut.c156.costEq P hP, limbs_of_lt hb, limbs_of_lt hB]
  have := length_cost P (by includes) bs hb
  simp only [max_self]
  split_ifs <;> omega

/-! ## The replay, amortized -/

section Maps

variable {α β : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]

/-- A value a lookup returns is an entry's. -/
theorem get?_some_mem {m : SortedMap α β} {k : α} {v : β} (h : m.get? k = some v) :
    ∃ l ∈ m.levels, ∃ e ∈ l.entries, e.2 = v := by
  rw [SortedMap.get?_eq] at h
  obtain ⟨l, hl, hv⟩ := List.exists_of_findSome?_eq_some h
  simp only [lookup, Option.map_eq_some_iff] at hv
  obtain ⟨e, he, rfl⟩ := hv
  exact ⟨l, hl, e, by simpa using List.mem_of_find?_eq_some he, rfl⟩

/-- An insertion keeps the values in `Q`. -/
theorem valsIn_insert {Q : β → Prop} {m : SortedMap α β}
    (hQ : ∀ l ∈ m.levels, ∀ e ∈ l.entries, Q e.2) (k : α) {v : β} (hv : Q v) :
    ∀ l ∈ (m.insert k v).levels, ∀ e ∈ l.entries, Q e.2 := by
  unfold SortedMap.insert
  have : ∀ (ls : List (Level α β)) (l0 : Level α β), (∀ l ∈ l0 :: ls, ∀ e ∈ l.entries, Q e.2) →
      ∀ l ∈ carry l0 ls, ∀ e ∈ l.entries, Q e.2 := by
    intro ls
    induction ls with
    | nil => intro l h; simpa [carry] using h
    | cons l' ls ih =>
      intro l h
      rw [carry]
      split
      · refine ih _ fun x hx ↦ ?_
        rcases List.mem_cons.1 hx with rfl | hx
        · intro e he
          simp only [Level.merge, List.mem_toArray] at he
          rcases mem_mergeNewer he with h1 | h1
          · exact h l (by simp) e (by simpa using h1)
          · exact h l' (by simp) e (by simpa using h1)
        · exact h x (by simp [hx])
      · exact h
  refine this _ _ fun l hl e he ↦ ?_
  rcases List.mem_cons.1 hl with rfl | hl
  · simp at he; rw [he]; exact hv
  · exact hQ l hl e he

end Maps

/-- A path's bytes are at most `B`. -/
@[expose] def PathOk (B : ℕ) (p : KeccakState × Option (List UInt8)) : Prop :=
  ∀ bs, p.2 = some bs → bs.length ≤ B

/-- **The replay's invariant**, `r` queries left: three good maps of word-list keys (`25` words for
the edges, `8` for the capacities), the paths' bytes at most `B`, room for `r` more insertions
below `2^D`. -/
@[expose] def ReplayInv (B D : ℕ) (τ : ReplayFast) (r : ℕ) : Prop :=
  smGood τ.fwd ∧ smGood τ.inv ∧ smGood τ.caps ∧
    KeysIn (WordsKey 25) τ.fwd.levels ∧ KeysIn (WordsKey 25) τ.inv.levels ∧
    KeysIn (WordsKey 8) τ.caps.levels ∧ (∀ l ∈ τ.caps.levels, ∀ e ∈ l.entries, PathOk B e.2) ∧
    (∀ p ∈ τ.paths, PathOk B p) ∧ smWeightSum τ.fwd + r ≤ 2 ^ D ∧ smWeightSum τ.inv + r ≤ 2 ^ D ∧
    smWeightSum τ.caps + r ≤ 2 ^ D

/-- The replay's potential: its three maps', each at its merge price per entry. -/
@[expose] def replayPot (D : ℕ) (τ : ReplayFast) : ℕ :=
  (26 * 25 + 37) * potential D τ.fwd.levels + (26 * 25 + 37) * potential D τ.inv.levels +
    (26 * 8 + 37) * potential D τ.caps.levels

/-- **One replay step, amortized** (`replayStepC`). -/
theorem replayStep_amortized (hP : Includes P replayStepC.costDeps) (B D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (hB : B < 2 ^ 62) (τ : ReplayFast) (r : ℕ) (hτ : ReplayInv B D τ (r + 1))
    (q : PermutationQuery KeccakState × KeccakState) :
    ReplayInv B D (ReplayFast.step B τ q) r ∧
      machineCost P replayStepC.costIdx [encodeValue B, encodeValue τ, encodeValue q] + replayPot D (ReplayFast.step B τ q) ≤
        replayPot D τ + replayStepPrice B D W := by
  obtain ⟨g1, g2, g3, k1, k2, k3, vc, vp, w1, w2, w3⟩ := hτ
  obtain ⟨lv1, sz1⟩ := smGood_levels_le g1 (by omega : smWeightSum τ.fwd < 2 ^ D)
  obtain ⟨lv2, sz2⟩ := smGood_levels_le g2 (by omega : smWeightSum τ.inv < 2 ^ D)
  obtain ⟨lv3, sz3⟩ := smGood_levels_le g3 (by omega : smWeightSum τ.caps < 2 ^ D)
  have hU : ∀ k : List UInt64, k.length = 25 → ∀ m : SortedMap (List UInt64) Unit,
      m.levels.length ≤ D → (∀ l ∈ m.levels, l.entries.size ≤ l.weight ∧ l.weight ≤ 2 ^ D) →
      machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.get?.c143.costIdx [encodeValue m, encodeValue k] ≤
        D * (20 + (40 + 26 * 25 + 9 * W) * (D + 2)) + 9 := by
    intro k hk m hl hs
    have := getU_cost P (by includes) m (2 ^ D) W hW (fun l hl' ↦ (hs l hl').1.trans (hs l hl').2) k
    rw [Nat.log2_two_pow, hk] at this
    exact this.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 9)
  have hC : ∀ k : List UInt64, k.length = 8 →
      machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.get?.c146.costIdx [encodeValue τ.caps, encodeValue k] ≤
        D * (20 + (40 + 26 * 8 + 9 * W) * (D + 2)) + 9 := by
    intro k hk
    have := getC_cost P (by includes) τ.caps (2 ^ D) W hW
      (fun l hl' ↦ (sz3 l hl').1.trans (sz3 l hl').2) k
    rw [Nat.log2_two_pow, hk] at this
    exact this.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ lv3) 9)
  -- an insertion into an edge map, amortized
  have hInsU : ∀ (m : SortedMap (List UInt64) Unit), smGood m → KeysIn (WordsKey 25) m.levels →
      smWeightSum m < 2 ^ D → m.levels.length ≤ D → ∀ k : List UInt64, k.length = 25 →
      machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.insert.c150.costIdx [encodeValue m, encodeValue k, encodeValue ()] +
          (26 * 25 + 37) * potential D (m.insert k ()).levels ≤
        (26 * 25 + 37) * potential D m.levels + (26 * 25 + 37) * D + (32 + 2 * W) * D + 52 + 2 * W := by
    intro m hm hk hN hl k hkl
    rw [Auto.LeanVM.Extraction.Fast.SortedMap.insert.c150.costEq P (by includes)]
    have hc1 := Nat.mul_le_mul_left (32 + 2 * W) (show m.levels.length + 1 ≤ D + 1 by omega)
    have hc2 : (32 + 2 * W) * (D + 1) = (32 + 2 * W) * D + 32 + 2 * W := by ring
    have := carryU_amortized P (by includes) 25 D W hW m hm hk hN
      ⟨1, #[(k, ())], by simp [Ascending]⟩ rfl rfl (fun e he ↦ by
        simp at he; rw [he]; show k.length ≤ 25; omega)
    have hins : (m.insert k ()).levels = carry ⟨1, #[(k, ())], by simp [Ascending]⟩ m.levels := rfl
    rw [hins]
    omega
  have hInsC : ∀ (k : List UInt64), k.length = 8 → ∀ v : KeccakState × Option (List UInt8),
      machineCost P Auto.LeanVM.Extraction.Fast.SortedMap.insert.c163.costIdx
          [encodeValue τ.caps, encodeValue k, encodeValue v] + (26 * 8 + 37) * potential D (τ.caps.insert k v).levels ≤
        (26 * 8 + 37) * potential D τ.caps.levels + (26 * 8 + 37) * D + (32 + 2 * W) * D + 52 + 2 * W := by
    intro k hkl v
    rw [Auto.LeanVM.Extraction.Fast.SortedMap.insert.c163.costEq P (by includes)]
    have hc1 := Nat.mul_le_mul_left (32 + 2 * W) (show τ.caps.levels.length + 1 ≤ D + 1 by omega)
    have hc2 : (32 + 2 * W) * (D + 1) = (32 + 2 * W) * D + 32 + 2 * W := by ring
    have := carryC_amortized P (by includes) 8 D W hW τ.caps g3 k3 (by omega)
      ⟨1, #[(k, v)], by simp [Ascending]⟩ rfl rfl (fun e he ↦ by
        simp at he; rw [he]; show k.length ≤ 8; omega)
    have hins : (τ.caps.insert k v).levels = carry ⟨1, #[(k, v)], by simp [Ascending]⟩ τ.caps.levels :=
      rfl
    rw [hins]
    omega
  have hd : ∀ z : KeccakState, machineCost P Auto.List.drop.c149.costIdx [encodeValue 17, encodeValue z.toList] ≤ 260 :=
    fun z ↦ (drop_cost P (by includes) 17 z.toList (by norm_num)).trans (by norm_num)
  have hk25 : ∀ z : KeccakState, WordsKey 25 z.toList := fun z ↦ by simp [WordsKey]
  have hk8 : ∀ z : KeccakState, WordsKey 8 (z.toList.drop 17) := fun z ↦ by simp [WordsKey]
  have hl25 : ∀ z : KeccakState, z.toList.length = 25 := fun z ↦ by simp
  have hl8 : ∀ z : KeccakState, (z.toList.drop 17).length = 8 := fun z ↦ by simp
  obtain ⟨fst, y⟩ := q
  rw [replayStepC.costEq_mk P hP]
  unfold replayStepPrice replayPot
  generalize hGU : D * (20 + (40 + 26 * 25 + 9 * W) * (D + 2)) = GU at hU
  generalize hGC : D * (20 + (40 + 26 * 8 + 9 * W) * (D + 2)) = GC at hC
  generalize hWD : (32 + 2 * W) * D = WD at hInsU hInsC
  cases fst with
  | forward x =>
    simp only [Vector.size_toArray]
    have hgf := hU x.toList (hl25 x) τ.fwd lv1 sz1
    by_cases hc : τ.fwd.contains x.toList = true
    · simp only [ReplayFast.step, hc, ↓reduceIte]
      refine ⟨⟨g1, g2, g3, k1, k2, k3, vc, vp, by omega, by omega, by omega⟩, ?_⟩
      generalize τ.fwd.get? x.toList = o
      cases o <;> dsimp only <;> omega
    · simp only [ReplayFast.step, hc, Bool.false_eq_true, ↓reduceIte]
      have hgc := hC (x.toList.drop 17) (hl8 x)
      have hf := hInsU τ.fwd g1 k1 (by omega) lv1 x.toList (hl25 x)
      have hi := hInsU τ.inv g2 k2 (by omega) lv2 y.toList (hl25 y)
      have hdx := hd x
      have hdy := hd y
      obtain ⟨gf, wf⟩ := smGood_insert g1 x.toList ()
      obtain ⟨gi, wi⟩ := smGood_insert g2 y.toList ()
      cases hg : τ.caps.get? (x.toList.drop 17) with
      | none =>
        dsimp only
        refine ⟨⟨gf, gi, g3, keysIn_insert k1 (hk25 x) (), keysIn_insert k2 (hk25 y) (), k3, vc, vp,
          by (try dsimp only); omega, by (try dsimp only); omega, by (try dsimp only); omega⟩, ?_⟩
        generalize τ.fwd.get? x.toList = o
        cases o <;> dsimp only <;> omega
      | some sv =>
        obtain ⟨s, obs⟩ := sv
        dsimp only
        have hobs : PathOk B (s, obs) := by
          obtain ⟨l, hl, e, he, he2⟩ := get?_some_mem hg
          exact he2 ▸ vc l hl e he
        have hp : PathOk B (y, obs.bind fun bs ↦ cut B (bs ++ blockBytes s x)) := by
          intro bs' h
          simp only [Option.bind_eq_some_iff, cut] at h
          obtain ⟨bs, -, h⟩ := h
          split_ifs at h with hle
          · cases h; exact hle
        have hcI := hInsC (y.toList.drop 17) (hl8 y) (y, obs.bind fun bs ↦ cut B (bs ++ blockBytes s x))
        obtain ⟨gc, wc⟩ := smGood_insert g3 (y.toList.drop 17)
          (y, obs.bind fun bs ↦ cut B (bs ++ blockBytes s x))
        refine ⟨⟨gf, gi, gc, keysIn_insert k1 (hk25 x) (), keysIn_insert k2 (hk25 y) (),
          keysIn_insert k3 (hk8 y) _, valsIn_insert vc _ hp, ?_, by (try dsimp only); omega, by (try dsimp only); omega, by (try dsimp only); omega⟩, ?_⟩
        · intro p hp'
          rcases List.mem_cons.1 hp' with rfl | hp'
          · exact hp
          · exact vp p hp'
        · have hbind : machineCost P Auto.Option.bind.c154.costIdx
              [encodeValue obs, MachineValue.closure replayStepC.lam0.costIdx [encodeValue s, encodeValue x, encodeValue B]] ≤ 19 * B + 9199 := by
            cases obs with
            | none =>
              rw [Auto.Option.bind.c154.costEq_none P (by includes)
                (fun bs ↦ cut B (bs ++ blockBytes s x)) (.closure replayStepC.lam0.costIdx [encodeValue s, encodeValue x, encodeValue B])
                (fun bs ↦ RunsApp.of_spec (replayStepC.lam0.costSpec P (by includes) s x B bs))]; omega
            | some bs =>
              have hbs := hobs bs rfl
              rw [Auto.Option.bind.c154.costEq_some P (by includes) bs
                (fun bs ↦ cut B (bs ++ blockBytes s x)) (.closure replayStepC.lam0.costIdx [encodeValue s, encodeValue x, encodeValue B])
                (fun bs ↦ RunsApp.of_spec (replayStepC.lam0.costSpec P (by includes) s x B bs))]
              simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              rw [replayStepC.lam0.costEq P (by includes)]
              have := blockBytes_cost P (by includes) s x
              have := append_cost P (by includes) bs (blockBytes s x)
              have := cut_cost P (by includes) B (by omega) (bs ++ blockBytes s x)
                (by simp [blockBytes_length]; omega)
              simp only [List.length_append, blockBytes_length] at this
              omega
          generalize τ.fwd.get? x.toList = o
          cases o <;> dsimp only <;> omega
  | inverse y' =>
    simp only [Vector.size_toArray]
    have hgi := hU y'.toList (hl25 y') τ.inv lv2 sz2
    by_cases hc : τ.inv.contains y'.toList = true
    · simp only [ReplayFast.step, hc, ↓reduceIte]
      refine ⟨⟨g1, g2, g3, k1, k2, k3, vc, vp, by omega, by omega, by omega⟩, ?_⟩
      generalize τ.inv.get? y'.toList = o
      cases o <;> dsimp only <;> omega
    · simp only [ReplayFast.step, hc, Bool.false_eq_true, ↓reduceIte]
      have hf := hInsU τ.fwd g1 k1 (by omega) lv1 y.toList (hl25 y)
      have hi := hInsU τ.inv g2 k2 (by omega) lv2 y'.toList (hl25 y')
      obtain ⟨gf, wf⟩ := smGood_insert g1 y.toList ()
      obtain ⟨gi, wi⟩ := smGood_insert g2 y'.toList ()
      refine ⟨⟨gf, gi, g3, keysIn_insert k1 (hk25 y) (), keysIn_insert k2 (hk25 y') (), k3, vc, vp,
        by (try dsimp only); omega, by (try dsimp only); omega, by (try dsimp only); omega⟩, ?_⟩
      generalize τ.inv.get? y'.toList = o
      cases o <;> dsimp only <;> omega

/-! ## The evaluations and the index -/

theorem keccakUnpaddedFast_length {bs m : List UInt8} (h : keccakUnpaddedFast bs = some m) :
    m.length ≤ bs.length := by
  rw [keccakUnpaddedFast] at h
  split at h
  · cases h; exact stripPad_length_le bs
  · cases h

/-- The replay's start (`ReplayFast.init.c187`): at most `423`. -/
theorem replayInit_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.ReplayFast.init.c187.costDeps) :
    machineCost P Auto.LeanVM.Extraction.Fast.ReplayFast.init.c187.costIdx [] ≤ 423 := by
  rw [Auto.LeanVM.Extraction.Fast.ReplayFast.init.c187.costEq P hP,
    Auto.LeanVM.Extraction.Fast.SortedMap.insert.c163.costEq P (by includes)]
  have h1 := drop_cost P (by includes) 17 (Vector.replicate 25 (0 : UInt64)).toList (by norm_num)
  simp only [SortedMap.empty, Vector.size_toArray]
  rw [Auto.LeanVM.Extraction.Fast.carry.c164.costEq_nil P (by includes)]
  omega

theorem replayInv_init (B D N : ℕ) (hN : N + 1 ≤ 2 ^ D) : ReplayInv B D ReplayFast.init N := by
  refine ⟨smGood_empty, smGood_empty, (smGood_insert smGood_empty _ _).1, fun _ h ↦ by
    simp [ReplayFast.init, SortedMap.empty] at h, fun _ h ↦ by
    simp [ReplayFast.init, SortedMap.empty] at h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact keysIn_insert (fun _ h ↦ by simp [SortedMap.empty] at h) (by simp [WordsKey]) _
  · exact valsIn_insert (fun _ h ↦ by simp [SortedMap.empty] at h) _ (by simp [PathOk])
  · intro p hp; simp [ReplayFast.init] at hp; subst hp; simp [PathOk]
  · simp [ReplayFast.init, smWeightSum_empty]; omega
  · simp [ReplayFast.init, smWeightSum_empty]; omega
  · rw [show ReplayFast.init.caps = (SortedMap.empty : SortedMap (List UInt64)
      (KeccakState × Option (List UInt8))).insert _ _ from rfl, (smGood_insert smGood_empty _ _).2,
      smWeightSum_empty]
    omega

theorem replayPot_init (D : ℕ) : replayPot D ReplayFast.init = (26 * 8 + 37) * D := by
  have h1 : Nat.log2 1 = 0 := Nat.log2_two_pow (n := 0)
  simp [replayPot, ReplayFast.init, SortedMap.insert, SortedMap.empty, carry, potential, h1]

theorem replayInv_foldl (P : MachineProgram) (hP : Includes P replayStepC.costDeps) (B D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (hB : B < 2 ^ 62) : ∀ (T : List (PermutationQuery KeccakState × KeccakState)) (τ : ReplayFast),
      ReplayInv B D τ T.length → ReplayInv B D (T.foldl (ReplayFast.step B) τ) 0 := by
  intro T
  induction T with
  | nil => intro τ h; simpa using h
  | cons q T ih =>
    intro τ h
    exact ih _ (replayStep_amortized P hP B D W hW hB τ T.length h q).1

/-- **The evaluations a transcript holds** (`keccakEvaluationsFast T L`, compiled as
`keccakEvaluationsC`): the replay over the `N` queries (`replayStepPrice` each, amortized) and a
padding check per path (`N + 1` paths of at most `B = L + 136` bytes). -/
theorem keccakEvaluations_cost (hP : Includes P keccakEvaluationsC.costDeps) (D L W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (hL : L < 2 ^ 61) (T : List (PermutationQuery KeccakState × KeccakState))
    (hN : T.length + 1 ≤ 2 ^ D) :
    machineCost P keccakEvaluationsC.costIdx [encodeValue T, encodeValue L] ≤
      (26 * 8 + 37) * D + (replayStepPrice (L + 136) D W + 16) * T.length +
        (120 * (L + 136) + 9363) * (T.length + 1) + 442 := by
  rw [keccakEvaluationsC.costEq P hP]
  have hrate : rate = 136 := rfl
  have hinit := replayInit_cost P (by includes)
  have hfold := listFoldl_amortized P (by includes) _
    (.closure keccakEvaluationsC.lam1.costIdx [encodeValue (L + rate)])
    (fun a b ↦ RunsApp.of_spec (keccakEvaluationsC.lam1.costSpec P (by includes) (L + rate) a b))
    (replayStepPrice (L + 136) D W + 5) (replayPot D) (ReplayInv (L + 136) D) T ReplayFast.init
    (replayInv_init _ D _ hN)
    (fun τ r hτ q _ ↦ by
      have h := replayStep_amortized P (by includes) (L + 136) D W hW (by omega) τ r hτ q
      refine ⟨h.1, ?_⟩
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [keccakEvaluationsC.lam1.costEq P (by includes), hrate]
      omega)
  rw [replayPot_init] at hfold
  have hinv := replayInv_foldl P (by includes) (L + 136) D W hW (by omega) T ReplayFast.init
    (replayInv_init _ D _ hN)
  have hlen := replay_paths_length_le (L + rate) T ReplayFast.init
  have hfm := filterMap_cost P (by includes) _ (.closure keccakEvaluationsC.lam0.costIdx [encodeValue L])
    (fun a ↦ RunsApp.of_spec (keccakEvaluationsC.lam0.costSpec P (by includes) L a))
    (120 * (L + 136) + 9347) _ (fun p hp ↦ by
      have hp' : PathOk (L + 136) p := hinv.2.2.2.2.2.2.2.1 p (by rw [← hrate]; exact hp)
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [keccakEvaluationsC.lam0.costEq P (by includes)]
      obtain ⟨st, obs⟩ := p
      cases obs with
      | none =>
        rw [Auto.Option.bind.c154.costEq_none P (by includes) _
          (.closure keccakEvaluationsC.lam0.lam0.costIdx [encodeValue L, encodeValue (st, (none : Option (List UInt8)))])
          (fun bs ↦ RunsApp.of_spec (keccakEvaluationsC.lam0.lam0.costSpec P (by includes) L _ bs))]
        omega
      | some bs =>
        have hbs : bs.length ≤ L + 136 := hp' bs rfl
        rw [Auto.Option.bind.c154.costEq_some P (by includes) bs _
          (.closure keccakEvaluationsC.lam0.lam0.costIdx [encodeValue L, encodeValue (st, some bs)])
          (fun bs ↦ RunsApp.of_spec (keccakEvaluationsC.lam0.lam0.costSpec P (by includes) L _ bs))]
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [keccakEvaluationsC.lam0.lam0.costEq P (by includes)]
        have hku := keccakUnpadded_cost P (by includes) bs (by omega)
        have hmb : ∀ m, keccakUnpaddedFast bs = some m → m.length ≤ bs.length :=
          fun m h ↦ keccakUnpaddedFast_length h
        generalize hk : keccakUnpaddedFast bs = om at hmb
        cases om with
        | none =>
          rw [Auto.Option.bind.c154.costEq_none P (by includes) _
            (.closure keccakEvaluationsC.lam0.lam0.lam0.costIdx [encodeValue L, encodeValue (st, some bs)])
            (fun m ↦ RunsApp.of_spec (keccakEvaluationsC.lam0.lam0.lam0.costSpec P (by includes)
              L _ m))]
          omega
        | some m =>
          have hm := hmb m rfl
          rw [Auto.Option.bind.c154.costEq_some P (by includes) m _
            (.closure keccakEvaluationsC.lam0.lam0.lam0.costIdx [encodeValue L, encodeValue (st, some bs)])
            (fun m ↦ RunsApp.of_spec (keccakEvaluationsC.lam0.lam0.lam0.costSpec P (by includes)
              L _ m))]
          simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [keccakEvaluationsC.lam0.lam0.lam0.costEq P (by includes),
            limbs_of_lt (by omega : m.length < 2 ^ 64), limbs_of_lt (by omega : L < 2 ^ 64)]
          have := length_cost P (by includes) m (by omega)
          simp only [max_self]
          split_ifs <;> omega)
  rw [limbs_of_lt (by rw [hrate]; omega : L + rate < 2 ^ 64), limbs_of_lt (by omega : L < 2 ^ 64),
    limbs_of_lt (by rw [hrate]; norm_num : rate < 2 ^ 64), max_self, max_self]
  rw [hrate] at hfm hfold hlen
  have : (120 * (L + 136) + 9347 + 16) * (List.foldl (ReplayFast.step (L + 136)) ReplayFast.init T).paths.length ≤
      (120 * (L + 136) + 9363) * (T.length + 1) := Nat.mul_le_mul_left _ (by
        have : ReplayFast.init.paths.length = 1 := rfl
        omega)
  have e1 : (replayStepPrice (L + 136) D W + 5 + 11) * T.length =
      (replayStepPrice (L + 136) D W + 16) * T.length := by ring
  rw [hrate]
  omega

theorem bytesInv_firstAnswers (P : MachineProgram) (hP : Includes P firstAnswersC.lam0.costDeps) (L D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (k : ℕ) : ∀ (pairs : List (List UInt8 × Protocol.Digest))
      (m : SortedMap (List UInt8) Protocol.Digest),
      (∀ p ∈ pairs, p.1.length ≤ L) → BytesInv L D m (pairs.length + k) →
      BytesInv L D (pairs.foldl (fun m p ↦ insertIfNew m p.1 p.2) m) k := by
  intro pairs
  induction pairs with
  | nil => intro m _ h; simpa using h
  | cons p pairs ih =>
    intro m hp h
    exact ih _ (fun q hq ↦ hp q (by simp [hq]))
      (firstAnswersStep_amortized P hP L D W hW m (pairs.length + k)
        (by simpa [Nat.add_right_comm] using h) p (hp p (by simp))).1

theorem answerPairs_length_le (f : List UInt8 → Option Protocol.Digest) (keys : List (List UInt8)) :
    (answerPairs f keys).length ≤ keys.length := by
  unfold answerPairs; exact List.length_filterMap_le _ _

theorem mem_answerPairs_fst {f : List UInt8 → Option Protocol.Digest} {keys : List (List UInt8)}
    {p : List UInt8 × Protocol.Digest} (h : p ∈ answerPairs f keys) : p.1 ∈ keys := by
  unfold answerPairs at h
  obtain ⟨x, hx, hp⟩ := List.mem_filterMap.1 h
  obtain ⟨d, -, rfl⟩ := Option.map_eq_some_iff.1 hp
  exact hx

/-- **The transcript's index** (`transcriptIndex T L`, compiled as `transcriptIndexC`), `N` queries
below `2^D`, byte strings of at most `L` bytes: the evaluations (`keccakEvaluations_cost`), then per
evaluation an amortized first-answer insertion (`firstAnswers_cost`), a lookup in the first answers
(`D` binary searches of `D + 2` probes of `40 + 26·L + 9·W`) and an amortized preimage-index insertion
(`preimageIndex_cost`). -/
theorem transcriptIndex_cost (hP : Includes P transcriptIndexC.costDeps) (D L W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (hL : L < 2 ^ 61) (T : List (PermutationQuery KeccakState × KeccakState))
    (hN : T.length + 2 ≤ 2 ^ D) :
    machineCost P transcriptIndexC.costIdx [encodeValue T, encodeValue L] ≤
      (26 * 8 + 37) * D + (replayStepPrice (L + 136) D W + 16) * T.length +
        (120 * (L + 136) + 9363) * (T.length + 1) + 442 +
        (T.length + 1) * ((firstAnswersStepPrice L D W + 11) + (preimageStepPrice L D W + 11) +
          D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) + 67) + 44 := by
  rw [transcriptIndexC.costEq P hP]
  set Ev := keccakEvaluationsFast T L with hEv
  have hlen : Ev.length ≤ T.length + 1 := keccakEvaluationsFast_length_le T L
  have hmem : ∀ e ∈ Ev, e.1.length ≤ L := fun e he ↦ keccakEvaluationsFast_mem_length_le he
  have hKE := keccakEvaluations_cost P (by includes) D L W hW hL T (by omega)
  have hFA := firstAnswers_cost P (by includes) L D W hW Ev (by omega) hmem
  have hmap := map_cost P (by includes) _ (.closure transcriptIndexC.lam1.costIdx [])
    (fun a ↦ RunsApp.of_spec (transcriptIndexC.lam1.costSpec P (by includes) a)) 2 Ev
    (fun a _ ↦ by rw [appCost_fn, List.nil_append, transcriptIndexC.lam1.costEq P (by includes),
      List.length_nil])
  -- the first answers' map
  have hinv : BytesInv L D (firstAnswers Ev) 1 := bytesInv_firstAnswers P (by includes) L D W hW 1 Ev
    SortedMap.empty hmem
    ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h, by simp [smWeightSum_empty]; omega⟩
  obtain ⟨hg, -, hw⟩ := hinv
  obtain ⟨hlv, hsz⟩ := smGood_levels_le hg (by omega : smWeightSum (firstAnswers Ev) < 2 ^ D)
  set G := D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) with hG
  have hget : ∀ x : List UInt8, x.length ≤ L →
      machineCost P getBytesC.costIdx [encodeValue (firstAnswers Ev), encodeValue x] ≤ G + 9 := by
    intro x hx
    have := getBytes_cost P (by includes) (firstAnswers Ev) (2 ^ D) W hW
      (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) x
    rw [Nat.log2_two_pow] at this
    have h1 : (firstAnswers Ev).levels.length * (20 + (40 + 26 * x.length + 9 * W) * (D + 2)) ≤ G :=
      Nat.mul_le_mul hlv (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
    omega
  have hAP : machineCost P answerPairsC.costIdx
      [.closure transcriptIndexC.lam0.costIdx [encodeValue (firstAnswers Ev), encodeValue Ev], encodeValue (Ev.map (·.1))] ≤
      (G + 52) * (T.length + 1) + 8 := by
    rw [answerPairsC.costEq P (by includes) (firstAnswers Ev).get? _
      (fun a ↦ RunsApp.of_spec (transcriptIndexC.lam0.costSpec P (by includes) _ _ a))]
    have := filterMap_cost P (by includes) _
      (.closure answerPairsC.lam0.costIdx [.closure transcriptIndexC.lam0.costIdx [encodeValue (firstAnswers Ev), encodeValue Ev]])
      (fun a ↦ RunsApp.of_spec (answerPairsC.lam0.costSpec P (by includes) (firstAnswers Ev).get? _
        (fun a ↦ RunsApp.of_spec (transcriptIndexC.lam0.costSpec P (by includes) _ _ a)) a))
      (G + 36) (Ev.map (·.1)) (fun x hx ↦ by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [answerPairsC.lam0.costEq P (by includes) (firstAnswers Ev).get? _
          (fun a ↦ RunsApp.of_spec (transcriptIndexC.lam0.costSpec P (by includes) _ _ a)),
          appCost_fn, List.cons_append, List.cons_append, List.nil_append,
          transcriptIndexC.lam0.costEq P (by includes)]
        simp only [List.length_cons, List.length_nil]
        have := hget e.1 (hmem e he)
        generalize (firstAnswers Ev).get? e.1 = o
        cases o with
        | none =>
          rw [Auto.Option.map.c194.costEq_none P (by includes) _
            (.closure answerPairsC.lam0.lam0.costIdx [encodeValue e.1])
            (fun a ↦ RunsApp.of_spec (answerPairsC.lam0.lam0.costSpec P (by includes) e.1 a))]
          omega
        | some d =>
          rw [Auto.Option.map.c194.costEq_some P (by includes) _
            (.closure answerPairsC.lam0.lam0.costIdx [encodeValue e.1])
            (fun a ↦ RunsApp.of_spec (answerPairsC.lam0.lam0.costSpec P (by includes) e.1 a)),
            appCost_fn, List.cons_append, List.nil_append, answerPairsC.lam0.lam0.costEq P (by includes)]
          simp only [List.length_cons, List.length_nil]
          omega)
    rw [List.length_map] at this
    have : (G + 36 + 16) * Ev.length ≤ (G + 52) * (T.length + 1) := Nat.mul_le_mul_left _ hlen
    omega
  have hPI := preimageIndex_cost P (by includes) D L W hW (by omega)
    (answerPairs (firstAnswers Ev).get? (Ev.map (·.1)))
    (by have := answerPairs_length_le (firstAnswers Ev).get? (Ev.map (·.1))
        simp only [List.length_map] at this; omega)
    (fun p hp ↦ by
      obtain ⟨e, he, h⟩ := List.mem_map.1 (mem_answerPairs_fst hp)
      rw [← h]; exact hmem e he)
  have hPl : (answerPairs (firstAnswers Ev).get? (Ev.map (·.1))).length ≤ T.length + 1 := by
    have := answerPairs_length_le (firstAnswers Ev).get? (Ev.map (·.1))
    simp only [List.length_map] at this; omega
  have e1 : (T.length + 1) * ((firstAnswersStepPrice L D W + 11) + (preimageStepPrice L D W + 11) + G + 67) =
      (T.length + 1) * (firstAnswersStepPrice L D W + 11) + (T.length + 1) * (preimageStepPrice L D W + 11) +
        (T.length + 1) * G + 67 * (T.length + 1) := by
    ring
  have e2 : (G + 52) * (T.length + 1) = (T.length + 1) * G + 52 * (T.length + 1) := by ring
  have f1 : Ev.length * (firstAnswersStepPrice L D W + 11) ≤ (T.length + 1) * (firstAnswersStepPrice L D W + 11) :=
    Nat.mul_le_mul_right _ hlen
  have f2 : (answerPairs (firstAnswers Ev).get? (Ev.map (·.1))).length * (preimageStepPrice L D W + 11) ≤
      (T.length + 1) * (preimageStepPrice L D W + 11) := Nat.mul_le_mul_right _ hPl
  omega

end

end LeanVM.Cost.Bounds
