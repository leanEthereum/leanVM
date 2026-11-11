/-
  LeanVM.Guest.Located.ReplayFast

  The replayed frame map, indexed: the run's entries in a sorted table built once, and the
  precondition's and B1's exponents by a discrete logarithm, each proved equal to the definition
  it replaces.
-/

module

public import LeanVM.Guest.Located.Replay
public import LeanVM.Guest.B1.Main.Facts
public import LeanVM.Protocol.Extraction.Fast.Lookup
public import LeanVM.Protocol.Extraction.Fast.Address

/-!
# The replayed frame map, indexed

`frameVWith states rd` finds a call's frame by scanning the replayed states, each against every
function (`firstEntered`); `preTest` decides a bound `∃ e < n, w = g^e` by trying every `e`, and
B1's `gLog` searches the `2^34` powers. Here:

* **The address tables.** `readTable`, `statesTable`: the memory read and the run stepped
  through the extractor's sorted address tables (`Extraction.Fast.powTable`, binary search,
  `gLogTable`; its step `stepTable`, whose compiled form `stepVec` the extractor's runner uses),
  equal to `readIn (powIndex κ)` and `statesIn` on at most `2^63` words (`readTable_powTable`,
  `statesTable_eq`).
* **The entries, indexed once.** `pcTable`: each entry pc to the functions entered there.
  `entryTable pre states rd`: from the call key `(j, args, rets)` (the callee by its index,
  `nameIndex`, the words by their limbs, `callKey`) to the frame of the first state at which
  function `j` was entered on those words with `pre` holding, a sorted map
  (`Extraction.Fast.SortedMap`, the extractor's) built in one pass over the states.
  `entryTable_get?`: with `pre = preTest rd` it answers as `firstEntered`. `frameVFast`, the frame
  map reading the table, and **`frameVWith_eq_frameVFast`**: it is `frameVWith`.
* **A discrete logarithm.** `DiscreteLogSpec dl`: `dl x = some n` exactly when `x = g^n`,
  `n < 2^64 − 1` (the order of `g`). Given one, `∃ e < n, g^e = x` is `dl x < n`
  (`exists_lt_gpow_iff`), so `preTestWith dl` (`preTestWith_eq`) and `gLogWith dl`
  (`gLogWith_eq`) are `preTest` and `B1.Main.gLog`. The proved `discreteLog` plugs in by these
  equations (`Guest/Fast/DiscreteLog.lean`).
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.Exec LeanVM.Guest.B1 LeanVM.Extraction LeanVM.Extraction.Fast

@[expose] public section

/-! ## The memory and the run, through the address tables -/

section Tables

/-- The word at address `a`, its index found by binary search in the address table `t`
(`Extraction.Fast.gLogTable`, the extractor's). -/
def readTable (t : Array (ℕ × ℕ)) {κ : ℕ} (L : MemoryImage κ) (a : K) : Option E :=
  (gLogTable t κ a).map L

/-- Through the table of the `2^κ` addresses, `κ < 64`, the read is the memory's. -/
theorem readTable_powTable {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    readTable (powTable κ) L = L.read := by
  funext a
  rw [readTable, gLogTable_eq hκ]
  exact congrFun (readIn_powIndex hκ L) a

/-- **The states of the run from `r`, through the address tables** (`statesIn`): each step the
extractor's `stepTable` (its compiled `stepVec` on the memory's vector). -/
def statesTable (memT codeT : Array (ℕ × ℕ)) (prog : Semantics.LeanIsaProgram) {κ : ℕ}
    (L : MemoryImage κ) : ℕ → Registers K → List (Registers K)
  | 0, r => [r]
  | n + 1, r => r :: if r = Registers.final prog then [] else
      match stepTable memT codeT prog L r with
      | some r' => statesTable memT codeT prog L n r'
      | none => []

/-- Through the tables, on at most `2^63` words, the replay is `statesIn`'s. -/
theorem statesTable_eq {prog : Semantics.LeanIsaProgram} {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    ∀ fuel r, statesTable (powTable κ) (powTable prog.logSize) prog L fuel r =
      statesIn (powIndex κ) (powIndex prog.logSize) prog L fuel r
  | 0, r => rfl
  | fuel + 1, r => by
    rw [statesTable, statesIn, stepTable_eq hκ]
    congr 1
    split
    · rfl
    · cases stepIn (powIndex κ) (powIndex prog.logSize) prog L r with
      | none => rfl
      | some r' => exact statesTable_eq hκ L fuel r'

end Tables

/-! ## Discrete logarithms -/

/-- **A discrete logarithm of `K*`**: `dl x = some n` exactly when `x = g^n` with `n` below the
order `2^64 − 1` of `g`. -/
def DiscreteLogSpec (dl : K → Option ℕ) : Prop :=
  ∀ x n, dl x = some n ↔ addressOfIndex n = x ∧ n < 2 ^ 64 - 1

theorem gpow_mod_order (e : ℕ) : addressOfIndex (e % (2 ^ 64 - 1)) = addressOfIndex e := by
  show Parameters.g ^ _ = Parameters.g ^ _
  rw [← orderOf_g, pow_mod_orderOf]

section Log

variable {dl : K → Option ℕ}

/-- With a discrete logarithm, `x` is a power `g^e` with `e < n` exactly when its logarithm is
below `n`. -/
theorem exists_lt_gpow_iff (hdl : DiscreteLogSpec dl) (x : K) (n : ℕ) :
    (∃ e < n, addressOfIndex e = x) ↔ ∃ m, dl x = some m ∧ m < n := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e % (2 ^ 64 - 1), (hdl _ _).mpr ⟨gpow_mod_order e, Nat.mod_lt _ (by norm_num)⟩,
      lt_of_le_of_lt (Nat.mod_le _ _) he⟩
  · rintro ⟨m, hm, hmn⟩
    exact ⟨m, hmn, ((hdl _ _).mp hm).1⟩

/-- `w` is the word `g^e` of some `e < n`, by the logarithm. -/
def isPowBelow (dl : K → Option ℕ) (w : E) (n : ℕ) : Bool :=
  decide (IsInK w) && match dl (w.limb 0) with
    | some m => decide (m < n)
    | none => false

theorem isPowBelow_iff (hdl : DiscreteLogSpec dl) (w : E) (n : ℕ) :
    isPowBelow dl w n = true ↔ ∃ e < n, w = ofK (addressOfIndex e) := by
  unfold isPowBelow
  rw [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨hK, h⟩
    rcases hm : dl (w.limb 0) with _ | m
    · rw [hm] at h; cases h
    · rw [hm, decide_eq_true_iff] at h
      refine ⟨m, h, ?_⟩
      rw [eq_ofK_limb hK, ((hdl _ _).mp hm).1]
  · rintro ⟨e, he, rfl⟩
    refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
    obtain ⟨m, hm, hmn⟩ := (exists_lt_gpow_iff hdl (addressOfIndex e) n).mp ⟨e, he, rfl⟩
    have h0 : (ofK (addressOfIndex e)).limb 0 = addressOfIndex e := by simp [limb_ofK]
    rw [h0, hm]
    exact decide_eq_true hmn

theorem any_range_pow_iff (hdl : DiscreteLogSpec dl) (o : Option E) (n : ℕ) :
    ((List.range n).any fun e ↦ decide (o = some (ofK (addressOfIndex e)))) =
      match o with
      | some w => isPowBelow dl w n
      | none => false := by
  rcases o with _ | w
  · simp
  · apply Bool.eq_iff_iff.mpr
    rw [isPowBelow_iff hdl, List.any_eq_true]
    simp only [List.mem_range, decide_eq_true_eq, Option.some.injEq]

/-- The bounds hold (`bndTest`), by the logarithm. -/
def bndTestWith (dl : K → Option ℕ) (rd : Reader) (fp : K) (bnd : List (ℕ × ℕ)) : Bool :=
  bnd.all fun p ↦ match rd (fp * addressOfIndex p.1) with
    | some w => isPowBelow dl w p.2
    | none => false

/-- The memory bounds hold (`memTest`), by the logarithm. -/
def memTestWith (dl : K → Option ℕ) (rd : Reader) (fp : K) (mem : List (ℕ × ℕ × ℕ)) : Bool :=
  mem.all fun m ↦ match rd (fp * addressOfIndex m.1) with
    | some p => decide (IsInK p) && match rd (p.limb 0 * addressOfIndex m.2.1) with
      | some w => isPowBelow dl w m.2.2
      | none => false
    | none => false

/-- **Function `j`'s precondition, decided by the logarithm** (`preTest`). -/
noncomputable def preTestWith (dl : K → Option ℕ) (rd : Reader) (j : ℕ) (fp : K) : Bool :=
  glob.good j && envTest rd fp (glob.sig j).env && bndTestWith dl rd fp (glob.sig j).pre &&
    memTestWith dl rd fp (glob.sig j).mem

theorem bndTestWith_eq (hdl : DiscreteLogSpec dl) : bndTestWith dl = bndTest := by
  funext rd fp bnd
  unfold bndTestWith bndTest
  congr 1
  funext p
  rw [any_range_pow_iff hdl]

theorem memTestWith_eq (hdl : DiscreteLogSpec dl) : memTestWith dl = memTest := by
  funext rd fp mem
  unfold memTestWith memTest
  congr 1
  funext m
  cases rd (fp * addressOfIndex m.1) with
  | none => rfl
  | some p =>
    show (decide (IsInK p) && _) = (decide (IsInK p) && _)
    rw [any_range_pow_iff hdl]

/-- **By the logarithm, the precondition's test is `preTest`.** -/
theorem preTestWith_eq (hdl : DiscreteLogSpec dl) : preTestWith dl = preTest := by
  funext rd j fp
  rw [preTestWith, preTest, bndTestWith_eq hdl, memTestWith_eq hdl]

/-- B1's exponent of a power of `g` below `2^34` (`B1.Main.gLog`), by the logarithm. -/
def gLogWith (dl : K → Option ℕ) (x : E) : ℕ :=
  match dl (x.limb 0) with
  | some n => if n < 2 ^ 34 then n else 0
  | none => 0

/-- **By the logarithm, the exponent is `B1.Main.gLog`.** -/
theorem gLogWith_eq (hdl : DiscreteLogSpec dl) : gLogWith dl = B1.Main.gLog := by
  funext x
  unfold B1.Main.gLog gLogWith
  rw [B1.Main.indexSearch_eq (by norm_num)]
  rcases hm : dl (x.limb 0) with _ | n
  · have : addressIndex? 34 (x.limb 0) = none := by
      refine gLog?_eq_none_iff.mpr fun i hi ↦ ?_
      have := (hdl _ i).mpr ⟨hi.symm, by have := i.isLt; omega⟩
      rw [hm] at this
      cases this
    rw [this]
    rfl
  · obtain ⟨hn, hlt⟩ := (hdl _ _).mp hm
    show (if n < 2 ^ 34 then n else 0) = _
    by_cases h34 : n < 2 ^ 34
    · rw [ite_eq_left h34, (gLog?_spec (κ := 34) (by norm_num) (i := ⟨n, h34⟩)).mpr hn.symm]
      rfl
    · rw [ite_eq_right h34]
      have : addressIndex? 34 (x.limb 0) = none := by
        refine gLog?_eq_none_iff.mpr fun i hi ↦ h34 ?_
        have hi' : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
        have := gpow_injOn hlt hi' (hn.trans hi)
        rw [this]
        exact i.isLt
      rw [this]
      rfl

end Log

/-! ## The entries, indexed -/

section Index

attribute [local instance] lexOrd

/-- The code of a word of `K`: its lane. -/
def laneCode (a : K) : ℕ := a.lane.toNat

theorem laneCode_injective : Function.Injective laneCode :=
  fun _ _ h ↦ K.lane_injective (UInt64.toNat_inj.mp h)

/-- The code of a word: its limbs' lanes. -/
def wordCode (x : E) : ℕ × ℕ × ℕ := (laneCode (x.limb 0), laneCode (x.limb 1), laneCode (x.limb 2))

theorem wordCode_injective : Function.Injective wordCode := by
  intro x y h
  simp only [wordCode, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  rw [← ofLimbs_limb x, ← ofLimbs_limb y, laneCode_injective h0, laneCode_injective h1,
    laneCode_injective h2]

/-- The key of a call: the callee's index and the codes of its words. -/
abbrev CallKey : Type := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)

/-- The key of a call of function `j` on `args`, `rets`. -/
def callKey (j : ℕ) (args rets : List E) : CallKey := (j, args.map wordCode, rets.map wordCode)

theorem callKey_eq_iff {j j' : ℕ} {args args' rets rets' : List E} :
    callKey j args rets = callKey j' args' rets' ↔ j = j' ∧ args = args' ∧ rets = rets' := by
  simp only [callKey, Prod.mk.injEq, (List.map_injective_iff.mpr wordCode_injective).eq_iff]

/-- A callee's name is `f` exactly when its index is `f`'s (the names are distinct). -/
theorem name_eq_iff {j : ℕ} (hj : glob.good j = true) (f : String) :
    (glob.sig j).name = f ↔ j = nameIndex f := by
  have hj' : 2 ≤ j ∧ j < nFns := by simpa [glob, good] using hj
  have hl : j - 1 < coreProgram.length := by
    have := coreProgram_length; simp only [nFns] at hj'; omega
  have hname : (glob.sig j).name = coreProgram[j - 1].name := by
    show (coreOf j).name = _
    rw [coreOf, nth_eq hl]
  rw [hname, nameIndex]
  constructor
  · rintro rfl
    rw [findIdx_name_of_nodup coreProgram_names_nodup hl]
    omega
  · intro h
    have hi : coreProgram.findIdx (fun g ↦ g.name == f) = j - 1 := by omega
    have hlt : coreProgram.findIdx (fun g ↦ g.name == f) < coreProgram.length := hi ▸ hl
    have := List.findIdx_getElem (w := hlt)
    simp only [hi, beq_iff_eq] at this
    exact this

/-- `m` with `j` added to the functions at key `k`. -/
def addAt (m : SortedMap ℕ (List ℕ)) (k j : ℕ) : SortedMap ℕ (List ℕ) := m.insert k (j :: m.getD k [])

/-- **The functions entered at each pc**: the code of function `j`'s entry to `j`, `j < nFns`. -/
noncomputable def pcTable : SortedMap ℕ (List ℕ) :=
  (List.range nFns).foldl (fun m j ↦ addAt m (laneCode (addressOfIndex (glob.sig j).entry))
      j) .empty

theorem mem_foldl_addAt (c : ℕ → ℕ) (k j : ℕ) :
    ∀ (js : List ℕ) (m : SortedMap ℕ (List ℕ)),
      j ∈ (js.foldl (fun m j ↦ addAt m (c j) j) m).getD k [] ↔ j ∈ m.getD k [] ∨ (j ∈ js ∧ c j = k)
  | [], m => by simp
  | j' :: js, m => by
    rw [List.foldl_cons, mem_foldl_addAt c k j js, addAt, SortedMap.getD_insert]
    by_cases hk : c j' = k
    · rw [ite_eq_left hk]
      constructor
      · rintro (h | ⟨h, hc⟩)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr ⟨List.mem_cons_self, hk⟩
          · exact Or.inl (hk ▸ h)
        · exact Or.inr ⟨List.mem_cons_of_mem _ h, hc⟩
      · rintro (h | ⟨h, hc⟩)
        · exact Or.inl (List.mem_cons_of_mem _ (hk ▸ h))
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl List.mem_cons_self
          · exact Or.inr ⟨h, hc⟩
    · rw [ite_eq_right hk]
      constructor
      · rintro (h | ⟨h, hc⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem _ h, hc⟩
      · rintro (h | ⟨h, hc⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact absurd hc hk
          · exact Or.inr ⟨h, hc⟩

/-- The functions the table gives at a pc are those entered there. -/
theorem mem_pcTable {pc : K} {j : ℕ} :
    j ∈ pcTable.getD (laneCode pc) [] ↔ j < nFns ∧ pc = addressOfIndex (glob.sig j).entry := by
  rw [pcTable, mem_foldl_addAt, SortedMap.getD_empty, List.mem_range]
  simp only [List.not_mem_nil, false_or]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ (laneCode_injective h).symm, fun h ↦ h ▸ rfl⟩

/-- The key under which state `r`, at function `j`'s entry, files its frame. -/
noncomputable def entryKey (rd : Reader) (r : Registers K) (j : ℕ) : CallKey :=
  callKey j (wordsWith rd r.fp 2 (glob.sig j).nargs)
    (wordsWith rd r.fp (2 + (glob.sig j).nargs) (glob.sig j).nret)

/-- The table with state `r` filed: under the key of each function entered at `r` whose test `pre`
holds there, `r`'s frame, unless the key has one. -/
noncomputable def fileState (pre : ℕ → K → Bool) (rd : Reader) (m : SortedMap CallKey K)
    (r : Registers K) : SortedMap CallKey K :=
  (pcTable.getD (laneCode r.pc) []).foldl
    (fun m j ↦ if pre j r.fp then insertIfNew m (entryKey rd r j) r.fp else m) m

/-- **The entries of the states, indexed**: from a call's key to the frame of the first state at
which a function of that key was entered, `pre` holding. -/
noncomputable def entryTable (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    SortedMap CallKey K :=
  states.foldl (fileState pre rd) .empty

theorem get?_insertIfNew (m : SortedMap CallKey K) (k k' : CallKey) (v : K) :
    (insertIfNew m k v).get? k' = (m.get? k').or (if k = k' then some v else none) := by
  unfold insertIfNew
  by_cases hm : m.contains k = true
  · rw [ite_eq_left hm]
    by_cases hx : k = k'
    · subst hx
      obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp hm
      simp [hv']
    · simp [hx]
  · rw [ite_eq_right hm, SortedMap.get?_insert]
    by_cases hx : k = k'
    · subst hx
      have hn : m.get? k = none := by simpa [SortedMap.contains] using hm
      simp [hn]
    · simp [hx]

/-- What state `r` files under `k`. -/
noncomputable def stateHit (pre : ℕ → K → Bool) (rd : Reader) (r : Registers K) (k : CallKey) :
    Option K :=
  if (pcTable.getD (laneCode r.pc) []).any (fun j ↦ pre j r.fp && decide (entryKey rd r j = k))
  then some r.fp else none

theorem get?_fileState (pre : ℕ → K → Bool) (rd : Reader) (r : Registers K) (k : CallKey) :
    ∀ (js : List ℕ) (m : SortedMap CallKey K),
      (js.foldl (fun m j ↦ if pre j r.fp then insertIfNew m (entryKey rd r j) r.fp else m) m).get? k =
        (m.get? k).or (if js.any (fun j ↦ pre j r.fp && decide (entryKey rd r j = k))
          then some r.fp else none)
  | [], m => by simp
  | j :: js, m => by
    rw [List.foldl_cons, get?_fileState pre rd r k js]
    by_cases hp : pre j r.fp = true
    · rw [ite_eq_left hp, get?_insertIfNew]
      by_cases hk : entryKey rd r j = k
      · simp only [hk, ↓reduceIte, List.any_cons, hp, decide_true, Bool.and_self, Bool.true_or]
        cases m.get? k <;> simp
      · simp only [hk, ↓reduceIte, Option.or_none, List.any_cons, hp, decide_false, Bool.and_false,
          Bool.false_or]
    · rw [ite_eq_right hp]
      simp [hp]

set_option maxRecDepth 100000 in
theorem get?_entryTable_foldl (pre : ℕ → K → Bool) (rd : Reader) (k : CallKey) :
    ∀ (states : List (Registers K)) (m : SortedMap CallKey K),
      (states.foldl (fileState pre rd) m).get? k =
        (m.get? k).or (states.findSome? fun r ↦ stateHit pre rd r k)
  | [], m => by simp
  | r :: states, m => by
    rw [List.foldl_cons, get?_entryTable_foldl pre rd k states, fileState, get?_fileState,
      List.findSome?_cons, stateHit]
    by_cases hA : (pcTable.getD (laneCode r.pc) []).any
        (fun j ↦ pre j r.fp && decide (entryKey rd r j = k)) = true
    · rw [ite_eq_left hA]
      cases m.get? k <;> rfl
    · rw [ite_eq_right hA]
      cases m.get? k <;> rfl

theorem any_entry_eq (rd : Reader) (r : Registers K) (f : String) (args rets : List E) :
    ((pcTable.getD (laneCode r.pc) []).any fun j ↦
        preTest rd j r.fp && decide (entryKey rd r j = callKey (nameIndex f) args rets)) =
      (List.range nFns).any (enteredTest rd f args rets r) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, h⟩
    obtain ⟨hj, hpc⟩ := mem_pcTable.mp hj
    rw [Bool.and_eq_true, decide_eq_true_iff, entryKey, callKey_eq_iff] at h
    obtain ⟨hp, hn, ha, hr⟩ := h
    have hgood : glob.good j = true := by
      simp only [preTest, Bool.and_eq_true] at hp; exact hp.1.1.1
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    simp only [enteredTest, Bool.and_eq_true]
    exact ⟨⟨⟨⟨decide_eq_true hpc, decide_eq_true ((name_eq_iff hgood f).mpr hn)⟩, hp⟩,
      decide_eq_true ha⟩, decide_eq_true hr⟩
  · rintro ⟨j, hj, h⟩
    simp only [enteredTest, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hpc, hn⟩, hp⟩, ha⟩, hr⟩ := h
    have hgood : glob.good j = true := by
      simp only [preTest, Bool.and_eq_true] at hp; exact hp.1.1.1
    refine ⟨j, mem_pcTable.mpr ⟨List.mem_range.mp hj, of_decide_eq_true hpc⟩, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, entryKey, callKey_eq_iff]
    exact ⟨hp, (name_eq_iff hgood f).mp (of_decide_eq_true hn), of_decide_eq_true ha,
      of_decide_eq_true hr⟩

/-- **The table answers as `firstEntered`**, its test the precondition's. -/
theorem entryTable_get? (states : List (Registers K)) (rd : Reader) (f : String) (args rets : List E) :
    (entryTable (preTest rd) states rd).get? (callKey (nameIndex f) args rets) =
      firstEntered states rd f args rets := by
  unfold entryTable firstEntered
  rw [get?_entryTable_foldl, SortedMap.get?_empty, Option.none_or]
  refine congrArg (fun F ↦ List.findSome? F states) (funext fun r ↦ ?_)
  show stateHit (preTest rd) rd r (callKey (nameIndex f) args rets) = _
  unfold stateHit
  rw [any_entry_eq]

/-- **The replayed frame map, read off the table** built once from the states, with the test
`pre`. -/
noncomputable def frameVFast (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    FrameMap :=
  let table := entryTable pre states rd
  fun f args rets ↦ match table.get? (callKey (nameIndex f) args rets) with
    | some fp => fun v ↦ wordWith rd fp ((certByName f).locs.getD v.idx 0)
    | none => fun _ ↦ 0

/-- **The frame map reads the table**, built once from the states. -/
theorem frameVWith_eq_frameVFast (states : List (Registers K)) (rd : Reader) :
    frameVWith states rd = frameVFast (preTest rd) states rd := by
  funext f args rets
  simp only [frameVFast, frameVWith, entryTable_get?]
  rfl

end Index

end
end LeanVM.Guest.Located
