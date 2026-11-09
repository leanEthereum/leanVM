module

public import LeanVM.Guest.Fast.PreTable
public import LeanVM.Guest.Fast.DiscreteLog
public import LeanVM.Guest.Fast.LogG

/-!
# The precondition's test, from the table

`Located.preTestWith discreteLog rd j fp` decides function `j`'s precondition at the frame `fp`
(the replayed frame map's test, `Located/ReplayFast.lean`) from what a caller knows of `j`
(`glob.sig j`). `preTestAt D T Pw rd j fp` decides it from a table `T` of the functions'
preconditions (`FnPre`, `Fast/PreSig.lean`), the logarithm's baby-step tables `D`
(`discreteLogWith D`) and the powers `gen^(2^j)`, `j < 34`, of the exponent tables (`Pw`:
`genPows`, `34` squarings), all built once by the caller: one entry by its own function
(`fnPreTest`), each list of checks through a function of one check (`envOne`, `bndOne`, `memOne`)
by partial application, the logarithm passed as a value to `powBelowAt`, so that it
compiles to the cost machine (`Cost/Decoder/PreTest.lean`). (`discreteLog x` builds its tables at
every call, `7.8·10^7` on the cost machine.)

**`preTestWith_eq_preTable`**: `preTestWith discreteLog = preTestAt discreteLogTables preTable
genPows`, the table the kernel wrote out (`Fast/PreTable.lean`); with `preTest_eq_discreteLog`,
`preTest_eq_preTable`.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Exec LeanVM.Guest.Check
open LeanVM.Guest.Located LeanVM.Extraction.Fast

@[expose] public section

/-! ## The checks, one by one -/

/-- Whether the logarithm `o` of a word is below `n`. -/
def powBelowAt (o : Option ℕ) (n : ℕ) : Bool :=
  match o with
  | some m => decide (m < n)
  | none => false

/-- Whether `w = 2^k` for some `e ≤ k < e + m`: `m` shifts and comparisons. (The lane of `g^k` is
`2^k` for `k < 64`, `g` being `X`: `lane_gpow`.) -/
def twoPowScan (w e : ℕ) : ℕ → Bool
  | 0 => false
  | m + 1 => decide (w = 1 <<< e) || twoPowScan w (e + 1) m

/-- Whether the logarithm of `x` (`discreteLogWith D`) is below `n`. -/
def powBelowLog (D : DiscreteLogTables) (x : K) (n : ℕ) : Bool :=
  powBelowAt (discreteLogWith D x) n

/-- The bounds the lanes' scan serves: at most `34`, every bound of the preconditions' table
(`Bounds/Decoder/PreTableShape.lean`). -/
def scanBound : ℕ := 34

/-- `w` is `g^e` for some `e < n` (`isPowBelow discreteLog`), the logarithm's baby-step tables
`D` given: for `n ≤ 34` by comparing `w`'s lane with the lanes `2^0, …, 2^(n-1)` of
`g^0, …, g^(n-1)` (`twoPowScan`), else by its logarithm (`discreteLogWith D`, `powBelowLog`).
`powBelow_eq`: at `D = discreteLogTables` it is `isPowBelow discreteLog`, on every input. -/
def powBelow (D : DiscreteLogTables) (w : E) (n : ℕ) : Bool :=
  decide (IsInK w) &&
    (if n ≤ scanBound then twoPowScan (w.limb 0).lane.toNat 0 n
    else powBelowLog D (w.limb 0) n)

/-- The word read, if any, is `g^e` for some `e < n`. -/
def readPowBelow (D : DiscreteLogTables) (o : Option E) (n : ℕ) : Bool :=
  match o with
  | some w => powBelow D w n
  | none => false

/-- The word read, if any, is `x` (`decide (o = some x)`). -/
def readIs (o : Option E) (x : E) : Bool :=
  match o with
  | some w => decide (w = x)
  | none => false

/-! ## The powers `g^o`, `o < 128`, read off the powers table

The powers table `Pw` (`genPows`, built once by the caller) holds the powers `gen^(2^j)`,
`j < 34`, then the powers `g^o`, `o < 128` (as words, at `34 + o`): a check reads `g^o` off it
(`gpowAt`), not by squaring; above `128` (no entry of the deployed table) by squaring. -/

/-- The powers `g^o` the table holds: `o < 128`. -/
def smallPowBound : ℕ := 128

/-- **`g^o`, read off the powers table `Pw`** at `34 + o` for `o < 128`, else by squaring
(`gpowAt_genPows`: at `Pw = genPows` it is `gpow o`, on every input). -/
def gpowAt (Pw : Array E) (o : ℕ) : K :=
  if o < smallPowBound then (Pw.getD (B1.sizeBits + o) 0).limb 0 else addressOfIndex o

/-- A known word's value (`Sym.val`), the powers read off `Pw`. -/
def symValAt (Pw : Array E) (fp : K) : Sym → E
  | .zero => 0
  | .gp e => ofK (gpowAt Pw e)
  | .fpg e => ofK (fp * gpowAt Pw e)

/-- The word in cell `o` of the frame `fp` (`wordWith`), the power read off `Pw`. -/
def wordAt (Pw : Array E) (rd : Reader) (fp : K) (o : ℕ) : E := (rd (fp * gpowAt Pw o)).getD 0

/-- The entry environment's check `(o, v)`: cell `o` of the frame holds `v`. -/
def envOne (Pw : Array E) (rd : Reader) (fp : K) (p : ℕ × Sym) : Bool :=
  readIs (rd (fp * gpowAt Pw p.1)) (symValAt Pw fp p.2)

/-- The bound `(o, n)`: cell `o` of the frame holds `g^e`, `e < n`. -/
def bndOne (D : DiscreteLogTables) (Pw : Array E) (rd : Reader) (fp : K) (p : ℕ × ℕ) : Bool :=
  readPowBelow D (rd (fp * gpowAt Pw p.1)) p.2

/-- The memory bound at the address `p`'s cell `c`: it holds `g^e`, `e < n`. -/
def memAt (D : DiscreteLogTables) (Pw : Array E) (rd : Reader) (n c : ℕ) (p : E) : Bool :=
  decide (IsInK p) && readPowBelow D (rd (p.limb 0 * gpowAt Pw c)) n

/-- The memory bound at cell `c` of the address in the frame's cell `o`. -/
def memCell (D : DiscreteLogTables) (Pw : Array E) (rd : Reader) (fp : K) (o n c : ℕ) : Bool :=
  match rd (fp * gpowAt Pw o) with
  | some p => memAt D Pw rd n c p
  | none => false

/-- The memory bound `(o, c, n)`: the word at cell `c` of the address in cell `o`. -/
def memOne (D : DiscreteLogTables) (Pw : Array E) (rd : Reader) (fp : K) (m : ℕ × ℕ × ℕ) : Bool :=
  memCell D Pw rd fp m.1 m.2.2 m.2.1

/-! ## The powers table, built once -/

/-- `x, x^2, x^4, …`: `n` squarings. -/
def squaresFrom (x : E) : ℕ → List E
  | 0 => []
  | n + 1 => x :: squaresFrom (x * x) n

/-- `ofK y, ofK (y·g), …`: `n` products by `g`. -/
def powsFrom (y : K) : ℕ → List E
  | 0 => []
  | n + 1 => ofK y :: powsFrom (y * Parameters.g) n

/-- **The powers table**, built once by the caller and passed down (`Pw`): the powers
`gen^(2^j)`, `j < 34`, by `34` squarings (the exponent tables' right column), then the powers
`g^o`, `o < 128`, by `128` products (`gpowAt`). -/
def genPows : Array E :=
  (squaresFrom Protocol.Verifier.gen B1.sizeBits ++ powsFrom 1 smallPowBound).toArray

/-- **A function's precondition at the frame `fp`**, from its entry of the table. -/
def fnPreTest (D : DiscreteLogTables) (Pw : Array E) (rd : Reader) (fp : K) (t : Option FnPre) :
    Bool :=
  match t with
  | none => true
  | some t => t.env.all (envOne Pw rd fp) && t.pre.all (bndOne D Pw rd fp) &&
      t.mem.all (memOne D Pw rd fp)

/-- **Function `j`'s precondition at the frame `fp`**, from the table `T` of the functions'
preconditions, the logarithm's baby-step tables `D` and the powers `Pw` (`genPows`) given (but
for the jump table, `preTest`). -/
def preTestAt (D : DiscreteLogTables) (T : Array (Option FnPre)) (Pw : Array E) (rd : Reader)
    (j : ℕ) (fp : K) : Bool :=
  decide (2 ≤ j) && decide (j < nFns) && fnPreTest D Pw rd fp (T.getD j none)

/-! ## They are the precondition's test -/

theorem readIs_eq (o : Option E) (x : E) : readIs o x = decide (o = some x) := by
  cases o <;> simp [readIs]

theorem length_squaresFrom : ∀ (n : ℕ) (x : E), (squaresFrom x n).length = n
  | 0, _ => rfl
  | n + 1, x => by rw [squaresFrom, List.length_cons, length_squaresFrom n]

theorem length_powsFrom : ∀ (n : ℕ) (y : K), (powsFrom y n).length = n
  | 0, _ => rfl
  | n + 1, y => by rw [powsFrom, List.length_cons, length_powsFrom n]

/-- The products are the powers `y·g^o`. -/
theorem powsFrom_getD : ∀ (n : ℕ) (y : K) (o : ℕ), o < n →
    (powsFrom y n).getD o 0 = ofK (y * Parameters.g ^ o)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, y, 0, _ => by simp [powsFrom]
  | n + 1, y, o + 1, h => by
    rw [powsFrom, List.getD_cons_succ, powsFrom_getD n (y * Parameters.g) o (by omega), mul_assoc,
      ← pow_succ']

/-- **Entry `34 + o`, `o < 128`, of the powers table is `g^o`.** -/
theorem genPows_getD_small {o : ℕ} (ho : o < smallPowBound) :
    genPows.getD (B1.sizeBits + o) 0 = ofK (addressOfIndex o) := by
  rw [genPows, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    List.getD_append_right _ _ _ _ (by rw [length_squaresFrom]; omega), length_squaresFrom,
    Nat.add_sub_cancel_left, powsFrom_getD _ _ _ ho, one_mul]

/-- **The power read off the powers table is `g^o`**, on every input. -/
theorem gpowAt_genPows (o : ℕ) : gpowAt genPows o = addressOfIndex o := by
  unfold gpowAt
  split_ifs with ho
  · rw [genPows_getD_small ho]; simp [limb_ofK]
  · rfl

theorem symValAt_genPows (fp : K) (v : Sym) : symValAt genPows fp v = v.val fp := by
  cases v <;> simp [symValAt, Sym.val, gpowAt_genPows]

theorem wordAt_genPows : wordAt genPows = wordWith := by
  funext rd fp o
  simp [wordAt, wordWith, gpowAt_genPows]

theorem envOne_eq (rd : Reader) (fp : K) (p : ℕ × Sym) :
    envOne genPows rd fp p = decide (rd (fp * addressOfIndex p.1) = some (p.2.val fp)) := by
  rw [envOne, gpowAt_genPows, symValAt_genPows]
  exact readIs_eq _ _

theorem envTest_eq (rd : Reader) (fp : K) (env : List (ℕ × Sym)) :
    envTest rd fp env = (envChecks env).all (envOne genPows rd fp) := by
  unfold envTest envChecks
  rw [List.all_filterMap]
  congr 1
  funext p
  cases (envOf env).get p.1 <;> simp [envOne_eq]

theorem twoPowScan_iff (w : ℕ) : ∀ (e m : ℕ), twoPowScan w e m = true ↔ ∃ k < m, w = 2 ^ (e + k)
  | e, 0 => by simp [twoPowScan]
  | e, m + 1 => by
    rw [twoPowScan, Bool.or_eq_true, decide_eq_true_iff, twoPowScan_iff w (e + 1) m,
      Nat.one_shiftLeft]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨0, by omega, by rw [h, Nat.add_zero]⟩
      · exact ⟨k + 1, by omega, by rw [h]; ring_nf⟩
    · rintro ⟨k, hk, h⟩
      rcases k with _ | k
      · left; rw [h, Nat.add_zero]
      · right; exact ⟨k, by omega, by rw [h]; ring_nf⟩

theorem gLanes_take : gLanes.take 34 = (List.range 34).map (2 ^ ·) := by decide +kernel

/-- **The lane of `g^k` is `2^k`**, `k < 34`. -/
theorem lane_gpow {k : ℕ} (hk : k < 34) : (addressOfIndex k).lane.toNat = 2 ^ k := by
  have h : (gLanes.take 34)[k]? = some (2 ^ k) := by rw [gLanes_take]; simp [hk]
  rw [gLanes_eq] at h
  simp [hk] at h
  rw [← gpowK_eq (by unfold u128Bound; omega)]
  exact h

/-- The lanes' scan finds `x` among `g^e`, `e < n ≤ 34`. -/
theorem twoPowScan_iff_gpow (x : K) {n : ℕ} (hn : n ≤ 34) :
    twoPowScan x.lane.toNat 0 n = true ↔ ∃ e < n, addressOfIndex e = x := by
  rw [twoPowScan_iff]
  refine exists_congr fun e ↦ and_congr_right fun he ↦ ?_
  rw [Nat.zero_add, ← lane_gpow (by omega), lane_toNat_inj]
  exact eq_comm

/-- **The fast logarithm's bound is the logarithm's**, on every input. -/
theorem powBelow_eq_isPowBelow (w : E) (n : ℕ) :
    powBelow discreteLogTables w n = isPowBelow discreteLog w n := by
  unfold powBelow
  split_ifs with hn
  · apply Bool.eq_iff_iff.mpr
    rw [isPowBelow_iff discreteLog_discreteLogSpec, Bool.and_eq_true, decide_eq_true_iff,
      twoPowScan_iff_gpow _ hn]
    constructor
    · rintro ⟨hK, e, he, h⟩
      refine ⟨e, he, ?_⟩
      rw [eq_ofK_limb hK, ← h]
    · rintro ⟨e, he, rfl⟩
      refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, e, he, ?_⟩
      simp [limb_ofK]
  · unfold isPowBelow powBelowLog powBelowAt
    rfl

theorem powBelow_eq : isPowBelow discreteLog = powBelow discreteLogTables := by
  funext w n
  rw [powBelow_eq_isPowBelow]

theorem bndTestWith_eq_all (rd : Reader) (fp : K) (bnd : List (ℕ × ℕ)) :
    bndTestWith discreteLog rd fp bnd = bnd.all (bndOne discreteLogTables genPows rd fp) := by
  unfold bndTestWith bndOne readPowBelow
  simp only [gpowAt_genPows]
  rw [powBelow_eq]
  rfl

theorem memTestWith_eq_all (rd : Reader) (fp : K) (mem : List (ℕ × ℕ × ℕ)) :
    memTestWith discreteLog rd fp mem = mem.all (memOne discreteLogTables genPows rd fp) := by
  unfold memTestWith memOne memCell memAt readPowBelow
  simp only [gpowAt_genPows]
  rw [powBelow_eq]
  rfl

/-- The squarings are the powers `x^(2^j)`. -/
theorem squaresFrom_getD : ∀ (n : ℕ) (x : E) (j : ℕ), j < n → (squaresFrom x n).getD j 0 = x ^ 2 ^ j
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, 0, _ => by simp [squaresFrom]
  | n + 1, x, j + 1, h => by
    rw [squaresFrom, List.getD_cons_succ, squaresFrom_getD n (x * x) j (by omega), ← sq, ← pow_mul,
      pow_succ, mul_comm 2]

/-- **Entry `j < 34` of the powers table is `gen^(2^j)`.** -/
theorem genPows_getD {j : ℕ} (hj : j < B1.sizeBits) :
    genPows.getD j 0 = Protocol.Verifier.gen ^ 2 ^ j := by
  rw [genPows, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    List.getD_append _ _ _ _ (by rw [length_squaresFrom]; exact hj), squaresFrom_getD _ _ _ hj]

/-- **The test of an entry `fnPreOf s` is the three tests of `s`.** -/
theorem fnPreTest_fnPreOf (rd : Reader) (fp : K) (s : Sig) :
    fnPreTest discreteLogTables genPows rd fp (fnPreOf s) =
      (envTest rd fp s.env && bndTestWith discreteLog rd fp s.pre &&
        memTestWith discreteLog rd fp s.mem) := by
  rw [envTest_eq, bndTestWith_eq_all, memTestWith_eq_all]
  unfold fnPreOf
  cases h : (envChecks s.env).isEmpty && s.pre.isEmpty && s.mem.isEmpty
  · rfl
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp [fnPreTest, h1, h2, h3]

/-- **From the table, the test is `preTestWith discreteLog`.** -/
theorem preTestWith_eq_preTable :
    preTestWith discreteLog = preTestAt discreteLogTables preTable genPows := by
  funext rd j fp
  unfold preTestWith preTestAt
  have hg : glob.good j = (decide (2 ≤ j) && decide (j < nFns)) := by
    show (Nat.ble 2 j && Nat.blt j nFns) = _
    exact Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq, Nat.blt_eq])
  rw [hg]
  by_cases hj : 2 ≤ j ∧ j < nFns
  · rw [preTable_getD hj.2, fnPreTest_fnPreOf]
    simp [hj.1, hj.2, Bool.and_assoc]
  · rcases not_and_or.mp hj with h | h <;> simp [h]

/-- **The precondition's test is `preTestAt discreteLogTables preTable genPows`.** -/
theorem preTest_eq_preTable : preTest = preTestAt discreteLogTables preTable genPows :=
  preTest_eq_discreteLog.trans preTestWith_eq_preTable

end

end LeanVM.Guest.Fast
