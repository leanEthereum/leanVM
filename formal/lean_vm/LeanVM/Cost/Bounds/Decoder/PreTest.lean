module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.FieldLib
public import LeanVM.Cost.Bounds.Decoder.PreTestDefs
public import LeanVM.Cost.Decoder.PreTest

/-!
# Bound: the decoder's precondition test, compiled

The prices of `Guest.Fast.preTestAt D T rd j fp` (`Cost/Decoder/PreTest.lean`), function `j`'s
precondition at the frame `fp` from the table `T` of the functions' preconditions, the
logarithm's baby-step tables `D` given. Parametric in what the test calls:

* a memory read: the reader closure `rdVal` at most `R` (the decoder's `memReaderC`,
  `Bounds/Decoder/DecoderEnds.lean`);
* a logarithm's bound: `powBelowC` at most `B` at a bound `n ≤ 34` (every bound of the deployed
  table, `preTable_shape`). `powBelow_cost` gives `B = 706`: the word's lane compared with the
  lanes `2^0, …, 2^(n-1)` of `g^0, …, g^(n-1)` (`twoPowScanC`), no logarithm (the logarithm
  serves only bounds above `34`, `powBelowLogC`);
* the exponents of an entry within `W ≤ 7` bits (`FnPreWithin`): a power `g^o`, `o < 128`, read
  off the powers table `Pw` (`gpowAt_cost`, `17`; `psAt W = 5 + 73·W` by squaring, `516` at
  `W = 7`, before the table held them).

The bounds, bottom-up: `readIs_cost` (`20`), `gpowAt_cost` (`17`),
`symValAt_cost`, `envOne_cost`,
`readPowBelow_cost`, `bndOne_cost`, `memAt_cost`, `memCell_cost`, `memOne_cost`, `wordAt_cost`
(`wordWith_cost`, by squaring, for the entry table),
`powSqE_cost` (a power in `E` by squaring, `11 + 606·(log₂ n + 1)`), then

* **`fnPreTest_cost`**: an entry's test at most `fnPrePrice R B t` (`PreTestDefs.lean`);
* **`preTestAt_cost`**: function `j`'s test at most `fnPrePrice R B (T.getD j none) + 19`;
* **`preTestAt_cost_deployed`**: on the deployed table (`preTable`, its shape evaluated in
  `PreTableShape.lean`: exponents below `2^7`, at most one check of each kind, at most `99`
  bounds and memory cells, their logarithms' bounds at most `34`), at most
  `269R + 99B + 24834` (`99B = 69894` at `B = 706`, `powBelow_cost`);
* **`genPows_cost`**: the powers table, built once (`genPowsC`: `34` squarings for `gen^(2^j)`,
  `128` products for `g^o`), at most `17565`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Fast LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.MachineProgram)

/-! ## Powers and the logarithm's bound -/

/-- A power `g^o` by squaring, `o < 2^W`: at most `psAt W`. -/
theorem powSqW_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c101.costDeps) {W o : ℕ}
    (hW : 0 < W) (hW64 : W < 64) (ho : o < 2 ^ W) :
    machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c101.costIdx [encodeValue LeanVM.Parameters.g, encodeValue o] ≤
      psAt W := by
  have h64 : 2 ^ W ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hW64.le
  have h1 := powSq_cost P hP LeanVM.Parameters.g o (by omega)
  have h2 := log2_lt_of hW ho
  unfold psAt
  omega

/-- A power in `E` by squaring (`powSqEC`): at most `11 + 606·(log₂ n + 1)`. -/
theorem powSqE_cost (hP : Includes P powSqEC.costDeps) (a : E) (n : ℕ)
    (hn : n < 2 ^ 64) :
    machineCost P powSqEC.costIdx [encodeValue a, encodeValue n] ≤
      11 + 606 * (Nat.log2 n + 1) := by
  have := le_of_halving (fun x : E × ℕ ↦ x.2 < 2 ^ 64) (fun x ↦ x.2)
    (fun x ↦ machineCost P powSqEC.costIdx
      [encodeValue x.1, encodeValue x.2]) 606 11
    (fun x hx h0 ↦ by
      rw [powSqEC.costEq P hP, h0]
      simp)
    (fun x hx hpos ↦ by
      right
      refine ⟨(x.1 * x.1, x.2 / 2), by dsimp only; omega, le_refl _, ?_⟩
      rw [powSqEC.costEq P hP, limbs_of_lt hx,
        limbs_of_lt (by omega : x.2 % 2 < 2 ^ 64)]
      simp only [show x.2 ≠ 0 by omega, ↓reduceIte]
      split_ifs <;> omega)
    (a, n) hn
  simpa using this

/-- The lanes' scan (`twoPowScanC`) over `m` shifts from `e`, `e + m ≤ 63`: `20` per shift and
`5`, on words. -/
theorem twoPowScan_cost (hP : Includes P twoPowScanC.costDeps) (w : ℕ) (hw : w < 2 ^ 64) :
    ∀ (m e : ℕ), e + m ≤ 63 →
      machineCost P twoPowScanC.costIdx [encodeValue w, encodeValue e, encodeValue m] ≤ 20 * m + 5
  | 0, e, _ => by rw [twoPowScanC.costEq_zero P hP]
  | m + 1, e, he => by
    have hs : 1 <<< e < 2 ^ 64 := by
      rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [twoPowScanC.costEq_succ P hP, limbs_of_lt (by omega : m + 1 < 2 ^ 64), limbs_of_lt hs,
      limbs_of_lt (by omega : e < 2 ^ 64), limbs_of_lt (by omega : e + 1 < 2 ^ 64), limbs_of_lt hw]
    have := twoPowScan_cost hP w hw m (e + 1) (by omega)
    simp only [max_self]
    split_ifs <;> omega

/-- **A logarithm's bound** (`powBelowC`) at a bound `n ≤ 34`: the word's lane compared with the
lanes `2^0, …, 2^(n-1)` of `g^0, …, g^(n-1)` (`twoPowScanC`), at most `20·n + 26 ≤ 706`; no
logarithm. -/
theorem powBelow_cost (hP : Includes P powBelowC.costDeps) (D : DiscreteLogTables) (w : E)
    (n : ℕ) (hn : n ≤ 34) :
    machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ 706 := by
  rw [powBelowC.costEq P hP, limbs_of_lt (by omega : n < 2 ^ 64),
    limbs_of_lt (by unfold scanBound; norm_num : scanBound < 2 ^ 64)]
  have := twoPowScan_cost P (by includes) (w.limb 0).lane.toNat (UInt64.toNat_lt _) n 0
    (by omega)
  have hs : n ≤ scanBound := hn
  simp only [hs, ↓reduceIte, max_self]
  split_ifs <;> omega

/-- Whether the word read is `x` (`readIsC`): at most `20`. -/
theorem readIs_cost (hP : Includes P readIsC.costDeps) (o : Option E) (x : E) :
    machineCost P readIsC.costIdx [encodeValue o, encodeValue x] ≤ 20 := by
  rw [readIsC.costEq P hP]
  cases o with
  | none => dsimp only; omega
  | some w => dsimp only; split_ifs <;> omega

/-- An exponent of `W ≤ 7` bits is below `128`: the powers table holds its power. -/
theorem lt_smallPowBound {W o : ℕ} (hW7 : W ≤ 7) (ho : o < 2 ^ W) : o < smallPowBound := by
  have : 2 ^ W ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hW7
  unfold smallPowBound
  omega

/-- **A power `g^o`, `o < 128`, read off the powers table** (`gpowAtC`): `17`. -/
theorem gpowAt_cost (hP : Includes P gpowAtC.costDeps) (Pw : Array E) (o : ℕ)
    (ho : o < smallPowBound) :
    machineCost P gpowAtC.costIdx [encodeValue Pw, encodeValue o] ≤ 17 := by
  have h128 : smallPowBound < 2 ^ 64 := by unfold smallPowBound; norm_num
  have h34 : LeanVM.Guest.B1.sizeBits = 34 := rfl
  rw [gpowAtC.costEq P hP, limbs_of_lt (by omega : o < 2 ^ 64), limbs_of_lt h128,
    limbs_of_lt (by norm_num [LeanVM.Guest.B1.sizeBits] : LeanVM.Guest.B1.sizeBits < 2 ^ 64),
    limbs_of_lt (by unfold smallPowBound at h128 ho; omega : LeanVM.Guest.B1.sizeBits + o < 2 ^ 64)]
  simp only [ho, ↓reduceIte, max_self]
  omega

/-- A known word's value (`symValAtC`), its power read off the table: at most `57`. -/
theorem symValAt_cost (hP : Includes P symValAtC.costDeps) (Pw : Array E) (fp : K) (a : Sym)
    (ha : symExp a < smallPowBound) :
    machineCost P symValAtC.costIdx [encodeValue Pw, encodeValue fp, encodeValue a] ≤ 57 := by
  rw [symValAtC.costEq P hP]
  cases a with
  | zero => dsimp only; omega
  | gp e => have := gpowAt_cost P (by includes) Pw e ha; dsimp only; omega
  | fpg e => have := gpowAt_cost P (by includes) Pw e ha; dsimp only; omega

/-- The sum of an affine price over a list. -/
theorem sum_map_affine {α : Type} (f : α → ℕ) (a b : ℕ) :
    ∀ l : List α, (l.map fun x ↦ a * f x + b).sum = a * (l.map f).sum + b * l.length
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_affine f a b l]
    ring

/-- `List.all` (`all.c296`), the predicate's price depending on the element: its prices and `11`
per element, `3`. -/
theorem all_cost_sum (hP : Includes P Auto.List.all.c296.costDeps) {β : Type} [MachineEncoding β]
    (p : β → Bool) (pVal : MachineValue)
    (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : β → ℕ) :
    ∀ l : List β, (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B a) →
      machineCost P Auto.List.all.c296.costIdx [encodeValue l, pVal] ≤
        (l.map fun a ↦ B a + 11).sum + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.all.c296.costEq_nil P hP p pVal hp]; simp
  | cons a l ih =>
    intro hB
    rw [Auto.List.all.c296.costEq_cons P hP a l p pVal hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.map_cons, List.sum_cons]
    split_ifs <;> omega

/-- The squarings (`squaresFromC`): `308` per squaring, `5`. -/
theorem squaresFrom_cost (hP : Includes P squaresFromC.costDeps) :
    ∀ (n : ℕ) (x : E), n < 2 ^ 64 →
      machineCost P squaresFromC.costIdx [encodeValue x, encodeValue n] ≤ 308 * n + 5 := by
  intro n
  induction n with
  | zero => intro x _; rw [squaresFromC.costEq_zero P hP]
  | succ n ih =>
    intro x hn
    rw [squaresFromC.costEq_succ P hP, limbs_of_lt hn]
    have := ih (x * x) (by omega)
    omega

/-- The products (`powsFromC`): `51` per product, `5`. -/
theorem powsFrom_cost (hP : Includes P powsFromC.costDeps) :
    ∀ (n : ℕ) (y : K), n < 2 ^ 64 →
      machineCost P powsFromC.costIdx [encodeValue y, encodeValue n] ≤ 51 * n + 5 := by
  intro n
  induction n with
  | zero => intro y _; rw [powsFromC.costEq_zero P hP]
  | succ n ih =>
    intro y hn
    rw [powsFromC.costEq_succ P hP, limbs_of_lt hn]
    have := ih (y * LeanVM.Parameters.g) (by omega)
    omega

/-- **The powers table** (`genPowsC`: `gen^(2^j)` for `j < 34` by squarings, `g^o` for `o < 128`
by products), built once: at most `17565`. -/
theorem genPows_cost (hP : Includes P genPowsC.costDeps) :
    machineCost P genPowsC.costIdx [] ≤ 17565 := by
  rw [genPowsC.costEq P hP, List.length_append, length_squaresFrom]
  have hs : LeanVM.Guest.B1.sizeBits = 34 := rfl
  have hp : smallPowBound = 128 := rfl
  have h1 := squaresFrom_cost P (by includes) LeanVM.Guest.B1.sizeBits LeanVM.Protocol.Verifier.gen
    (by norm_num [hs])
  have h2 := powsFrom_cost P (by includes) smallPowBound 1 (by norm_num [hp])
  have h3 := append_cost P (by includes)
    (squaresFrom LeanVM.Protocol.Verifier.gen LeanVM.Guest.B1.sizeBits) (powsFrom 1 smallPowBound)
  have h4 : (powsFrom 1 smallPowBound).length = 128 := by
    rw [hp]; exact length_powsFrom 128 1
  rw [length_squaresFrom] at h3
  rw [hs, hp] at *
  omega

/-! ## The checks, one by one -/

section Checks

variable (D : DiscreteLogTables) (rd : Reader) (rdVal : MachineValue)
  (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
  (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
  (B : ℕ) (hB : ∀ (w : E) (n : ℕ), n ≤ 34 →
    machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ B)
  {W : ℕ} (hW : 0 < W) (hW64 : W < 64)

include hrd

include hR in
/-- An entry-environment check (`envOneC`): a power off the table, a read, the known word's value
and `60`: `R + 134`. -/
theorem envOne_cost (hP : Includes P envOneC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (p : ℕ × Sym) (h1 : p.1 < 2 ^ W) (h2 : symExp p.2 < 2 ^ W) :
    machineCost P envOneC.costIdx [encodeValue Pw, rdVal, encodeValue fp, encodeValue p] ≤
      R + 134 := by
  rw [envOneC.costEq P hP Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw p.1 (lt_smallPowBound hW7 h1)
  have := hR (fp * gpowAt Pw p.1)
  have := symValAt_cost P (by includes) Pw fp p.2 (lt_smallPowBound hW7 h2)
  have := readIs_cost P (by includes) (rd (fp * gpowAt Pw p.1)) (symValAt Pw fp p.2)
  omega

omit hrd in
include hB in
/-- A read's logarithm's bound (`readPowBelowC`): `B + 7`. -/
theorem readPowBelow_cost (hP : Includes P readPowBelowC.costDeps) (o : Option E) (n : ℕ)
    (hn : n ≤ 34) :
    machineCost P readPowBelowC.costIdx [encodeValue D, encodeValue o, encodeValue n] ≤ B + 7 := by
  rw [readPowBelowC.costEq P hP]
  cases o with
  | none => dsimp only; omega
  | some w => have := hB w n hn; dsimp only; omega

include hR hB in
/-- A bound on a frame cell (`bndOneC`): a power off the table, a read, a logarithm's bound and
`38`: `R + B + 62`. -/
theorem bndOne_cost (hP : Includes P bndOneC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (p : ℕ × ℕ) (h1 : p.1 < 2 ^ W) (h2 : p.2 ≤ 34) :
    machineCost P bndOneC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp,
      encodeValue p] ≤ R + B + 62 := by
  rw [bndOneC.costEq P hP D Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw p.1 (lt_smallPowBound hW7 h1)
  have := hR (fp * gpowAt Pw p.1)
  have := readPowBelow_cost P D B hB (by includes) (rd (fp * gpowAt Pw p.1)) p.2 h2
  omega

include hR hB in
/-- A memory bound at one cell (`memAtC`): a power off the table, a read, a logarithm's bound and
`47`: `R + B + 71`. -/
theorem memAt_cost (hP : Includes P memAtC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (n c : ℕ)
    (p : E) (hn : n ≤ 34) (hc : c < 2 ^ W) :
    machineCost P memAtC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue n,
      encodeValue c, encodeValue p] ≤ R + B + 71 := by
  rw [memAtC.costEq P hP D Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw c (lt_smallPowBound hW7 hc)
  have := hR (p.limb 0 * gpowAt Pw c)
  have := readPowBelow_cost P D B hB (by includes) (rd (p.limb 0 * gpowAt Pw c)) n hn
  split_ifs <;> omega

include hR hB in
/-- A memory bound at one cell of the address in a frame cell (`memCellC`): two powers off the
table, two reads, a logarithm's bound: `2R + B + 130`. -/
theorem memCell_cost (hP : Includes P memCellC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (o n c : ℕ) (ho : o < 2 ^ W) (hn : n ≤ 34) (hc : c < 2 ^ W) :
    machineCost P memCellC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp,
      encodeValue o, encodeValue n, encodeValue c] ≤ 2 * R + B + 130 := by
  rw [memCellC.costEq P hP D Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw o (lt_smallPowBound hW7 ho)
  have := hR (fp * gpowAt Pw o)
  generalize rd (fp * gpowAt Pw o) = r
  cases r with
  | none => dsimp only; omega
  | some p =>
    have := memAt_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 n c p hn hc
    dsimp only; omega

include hR hB in
/-- A memory bound (`memOneC`): one cell, `2R + B + 159`. -/
theorem memOne_cost (hP : Includes P memOneC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (m : ℕ × ℕ × ℕ) (h1 : m.1 < 2 ^ W) (h2 : m.2.1 < 2 ^ W) (h3 : m.2.2 ≤ 34) :
    machineCost P memOneC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp,
      encodeValue m] ≤ 2 * R + B + 159 := by
  rw [memOneC.costEq P hP D Pw rd rdVal hrd]
  have := memCell_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 fp m.1 m.2.2 m.2.1 h1 h3 h2
  omega

include hR hW hW64 in
/-- A frame cell's word (`wordWithC`): a power, a read and `43`. -/
theorem wordWith_cost (hP : Includes P wordWithC.costDeps) (fp : K)
    (o : ℕ) (ho : o < 2 ^ W) :
    machineCost P wordWithC.costIdx
      [rdVal, encodeValue fp, encodeValue o] ≤ psAt W + R + 43 := by
  rw [wordWithC.costEq P hP rd rdVal hrd]
  have := powSqW_cost P (by includes) hW hW64 ho
  have := hR (fp * addressOfIndex o)
  generalize rd (fp * addressOfIndex o) = r
  cases r <;> dsimp only <;> omega

include hR in
/-- A frame cell's word (`wordAtC`), its power read off the table: `R + 58`. -/
theorem wordAt_cost (hP : Includes P wordAtC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (o : ℕ) (ho : o < 2 ^ W) :
    machineCost P wordAtC.costIdx [encodeValue Pw, rdVal, encodeValue fp, encodeValue o] ≤
      R + 58 := by
  rw [wordAtC.costEq P hP Pw rd rdVal hrd]
  have := gpowAt_cost P (by includes) Pw o (lt_smallPowBound hW7 ho)
  have := hR (fp * gpowAt Pw o)
  generalize rd (fp * gpowAt Pw o) = r
  cases r <;> dsimp only <;> omega

include hR hB in
/-- **An entry's test** (`fnPreTestC`), its exponents within `W ≤ 7` bits: at most
`fnPrePrice R B t`. -/
theorem fnPreTest_cost (hP : Includes P fnPreTestC.costDeps) (Pw : Array E) (hW7 : W ≤ 7) (fp : K)
    (t : Option FnPre) (ht : ∀ s, t = some s → FnPreWithin W s) :
    machineCost P fnPreTestC.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp,
      encodeValue t] ≤ fnPrePrice R B t := by
  rw [fnPreTestC.costEq P hP D Pw rd rdVal hrd]
  cases t with
  | none => dsimp only; simp [fnPrePrice]
  | some s =>
    obtain ⟨he, hpre, hm⟩ := ht s rfl
    dsimp only
    have h1 := all_cost P (by includes) _
      (.closure fnPreTestC.lam0.costIdx [encodeValue Pw, rdVal, encodeValue fp])
      (fun p ↦ RunsApp.of_spec (fnPreTestC.lam0.costSpec P (by includes) Pw rd rdVal hrd fp p))
      (R + 142) s.env (fun p hp ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [fnPreTestC.lam0.costEq P (by includes) Pw rd rdVal hrd]
        have := envOne_cost P rd rdVal hrd R hR (by includes) Pw hW7 fp p (he p hp).1
          (he p hp).2
        omega)
    have h2 := all_cost P (by includes) _
      (.closure fnPreTestC.lam1.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp])
      (fun p ↦ RunsApp.of_spec (fnPreTestC.lam1.costSpec P (by includes) D Pw rd rdVal hrd fp p))
      (R + B + 72) s.pre (fun p hp ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [fnPreTestC.lam1.costEq P (by includes) D Pw rd rdVal hrd]
        have := bndOne_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 fp p
          (hpre p hp).1 (hpre p hp).2
        omega)
    have h3 := all_cost P (by includes) _
      (.closure fnPreTestC.lam2.costIdx [encodeValue D, encodeValue Pw, rdVal, encodeValue fp])
      (fun m ↦ RunsApp.of_spec (fnPreTestC.lam2.costSpec P (by includes) D Pw rd rdVal hrd fp m))
      (2 * R + B + 170) s.mem (fun m hm' ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [fnPreTestC.lam2.costEq P (by includes) D Pw rd rdVal hrd]
        have := memOne_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 fp m
          (hm m hm').1 (hm m hm').2.1 (hm m hm').2.2
        omega)
    simp only [fnPrePrice, memCells]
    split_ifs <;> nlinarith

include hR hB in
/-- **Function `j`'s precondition test** (`preTestAtC`), its entry's exponents within `W ≤ 7`
bits: at most `fnPrePrice R B (T.getD j none) + 19`. -/
theorem preTestAt_cost (hP : Includes P preTestAtC.costDeps) (T : Array (Option FnPre))
    (Pw : Array E) (hW7 : W ≤ 7) (j : ℕ) (hj : j < 2 ^ 64) (fp : K)
    (hT : ∀ s, T.getD j none = some s → FnPreWithin W s) :
    machineCost P preTestAtC.costIdx [encodeValue D, encodeValue T, encodeValue Pw, rdVal,
      encodeValue j, encodeValue fp] ≤ fnPrePrice R B (T.getD j none) + 19 := by
  rw [preTestAtC.costEq P hP D T Pw rd rdVal hrd, limbs_of_lt hj,
    limbs_of_lt (by unfold LeanVM.Guest.nFns; norm_num : LeanVM.Guest.nFns < 2 ^ 64)]
  have := fnPreTest_cost P D rd rdVal hrd R hR B hB (by includes) Pw hW7 fp
    (T.getD j none) hT
  simp only [max_self]
  split_ifs <;> omega

end Checks

/-! ## The deployed table -/

/-- An entry of the deployed shape has its exponents within `7` bits. -/
theorem fnPreWithin_of_shape {t : FnPre} (h : fnPreShape t = true) : FnPreWithin 7 t := by
  simp only [fnPreShape, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, he⟩, hp⟩, hm⟩ := h
  exact ⟨fun p hp' ↦ he p hp', fun p hp' ↦ hp p hp', fun m hm' ↦ ⟨(hm m hm').1.1, (hm m hm').1.2, (hm m hm').2⟩⟩

/-- **An entry of the deployed shape**: its test's price at most `269R + 99B + 24815`. -/
theorem fnPrePrice_of_shape {t : FnPre} (h : fnPreShape t = true) (R B : ℕ) :
    fnPrePrice R B (some t) ≤ 269 * R + 99 * B + 24815 := by
  simp only [fnPreShape, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨he, hp⟩, hpc⟩, -⟩, -⟩, -⟩ := h
  simp only [fnPrePrice]
  generalize t.env.length = e at *
  generalize t.pre.length = p at *
  generalize t.mem.length = m at *
  generalize memCells t = c at *
  have h1 : (R + 153) * e ≤ (R + 153) * 1 := Nat.mul_le_mul_left _ he
  have h2 : (R + B + 83) * p + (2 * R + B + 181) * c ≤ (2 * R + B + 181) * (p + c) := by
    nlinarith
  have h3 : (2 * R + B + 181) * (p + c) ≤ (2 * R + B + 181) * 99 := Nat.mul_le_mul_left _ hpc
  nlinarith

/-- An entry of a table of the deployed shape has that shape. -/
theorem fnPreShape_of_getD {T : Array (Option FnPre)} (hT : tableShape T = true) {j : ℕ}
    {s : FnPre} (hs : T.getD j none = some s) : fnPreShape s = true := by
  unfold tableShape at hT
  rw [List.all_eq_true] at hT
  by_cases hj : j < T.size
  · have hmem : T[j] ∈ T.toList := Array.getElem_mem_toList hj
    have h2 : Option.all fnPreShape (T.getInternal j hj) = true := hT _ hmem
    simp only [Array.getD, hj, ↓reduceDIte] at hs
    rw [hs] at h2
    simpa using h2
  · simp [Array.getD, hj] at hs

/-- **Function `j`'s precondition test on a table of the deployed shape** (`preTable`:
`preTable_shape`, `PreTableShape.lean`), the powers `Pw` any table: at most
`269R + 99B + 24834`. -/
theorem preTestAt_cost_deployed (hP : Includes P preTestAtC.costDeps) (D : DiscreteLogTables)
    (rd : Reader) (rdVal : MachineValue)
    (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
    (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
    (B : ℕ) (hB : ∀ (w : E) (n : ℕ), n ≤ 34 →
      machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ B)
    (T : Array (Option FnPre)) (hT : tableShape T = true) (Pw : Array E) (j : ℕ)
    (hj : j < 2 ^ 64) (fp : K) :
    machineCost P preTestAtC.costIdx [encodeValue D, encodeValue T, encodeValue Pw, rdVal,
      encodeValue j, encodeValue fp] ≤ 269 * R + 99 * B + 24834 := by
  have := preTestAt_cost P D rd rdVal hrd R hR B hB (W := 7) hP T Pw le_rfl j hj fp
    (fun s hs ↦ fnPreWithin_of_shape (fnPreShape_of_getD hT hs))
  cases hg : T.getD j none with
  | none => rw [hg] at this; simp only [fnPrePrice] at this; omega
  | some s =>
    rw [hg] at this
    have := fnPrePrice_of_shape (fnPreShape_of_getD hT hg) R B
    omega

end

end LeanVM.Cost.Bounds
