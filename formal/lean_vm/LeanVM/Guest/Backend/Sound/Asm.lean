/-
  LeanVM.Guest.Backend.Sound.Asm

  Assembly is sound: the assembled program holds, at a function's entry plus `i`, the resolved
  form of the function's instruction `i`.
-/

module

public import LeanVM.Guest.Backend.Assemble
public import LeanVM.Guest.Code

/-!
# The assembled program holds each function's resolved code

For functions with distinct names:

* `layout_consecutive`: a function's entry is the sum of the lengths before it
  (`Layout.Consecutive`, stated in `Assemble`);
* `assembleAt_fetch`: fetching `entry_f + i` from `LeanVM.Guest.assemble a.toFunctions logSize`
  gives `resolveOp l entry_f frameSize_f` of instruction `i` of `f`, for every layout `l` that
  gives `f` its entry, and `assemble_fetch` for the layout `assemble` computes;
* `gpowTable_getElem?`, `Layout.ofBits_pow`: the layout's limb of `g^k` is `g^k`'s, for
  `k < 2^128`. `GpowTableSpec` as `Assemble` states it, for every `k`, is false past `2^128`,
  where `gpowK` reads the low 128 bits of its exponent: `gpowTable_spec` is the true form;
* `le_nextPow2`, `nextPow2_isPow`: the padded size is a power of two past the code, so the
  halting slot is past every function.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

/-! ## The g-power table -/

theorem gpowTable_go (n : ℕ) (x : K) (acc : Array ℕ) :
    (gpowTable.go n x acc).toList =
      acc.toList ++ (List.range n).map fun i => (x * g ^ i).toBitVec.toNat := by
  induction n generalizing x acc with
  | zero => simp [gpowTable.go]
  | succ n ih =>
      rw [gpowTable.go, ih, List.range_succ_eq_map]
      simp only [Array.toList_push, List.append_assoc, List.singleton_append, List.map_cons,
        List.map_map, pow_zero, mul_one, Function.comp_def, pow_succ', mul_assoc]

theorem gpowTable_toList (n : ℕ) :
    (gpowTable n).toList = (List.range n).map fun i => (addressOfIndex i).toBitVec.toNat := by
  simp [gpowTable, gpowTable_go, addressOfIndex]

theorem gpowTable_size (n : ℕ) : (gpowTable n).size = n := by
  rw [← Array.length_toList, gpowTable_toList]
  simp

theorem gpowTable_getElem? {n k : ℕ} (h : k < n) :
    (gpowTable n)[k]? = some (addressOfIndex k).toBitVec.toNat := by
  rw [← Array.getElem?_toList, gpowTable_toList]
  simp [h]

/-- `GpowTableSpec` for exponents below `2^128`, where `gpowK` is `g^k`. -/
theorem gpowTable_spec {n k : ℕ} (h : k < n) (hk : k < u128Bound) :
    (gpowTable n)[k]? = some (gpowK k).toBitVec.toNat := by
  rw [gpowTable_getElem? h, gpowK_eq hk]

theorem ofBits_toNat (a : K) : K.ofBits a.toBitVec.toNat = a := by
  simp [K.ofBits, BitVec.ofNat_toNat]

/-- The layout's powers are a g-power table. -/
def Layout.PowOk (l : Layout) : Prop := ∃ n, l.gpow = gpowTable n

/-- The layout's limb of `g^k` is `g^k`'s. -/
theorem Layout.ofBits_pow {l : Layout} (hl : l.PowOk) {k : ℕ} (hk : k < u128Bound) :
    K.ofBits (l.pow k) = addressOfIndex k := by
  obtain ⟨n, hn⟩ := hl
  unfold Layout.pow
  by_cases h : k < n
  · rw [hn, gpowTable_getElem? h]
    exact ofBits_toNat _
  · have hnone : (gpowTable n)[k]? = none := by
      rw [Array.getElem?_eq_none_iff, gpowTable_size]
      omega
    rw [hn, hnone]
    simp only [ofBits_toNat]
    exact gpowK_eq hk

/-- A `SET` of `g^k`'s limb writes the word `g^k`. -/
theorem Layout.immediateWord_pow {l : Layout} (hl : l.PowOk) {k : ℕ} (hk : k < u128Bound) :
    OffsetInstruction.immediateWord (l.pow k) 0 = ofK (addressOfIndex k) := by
  rw [OffsetInstruction.immediateWord, l.ofBits_pow hl hk, ofK_eq_ofLimbs]
  rfl

/-! ## The padded size -/

theorem nextPow2_go_le (n : ℕ) : ∀ (fuel p : ℕ), n ≤ p * 2 ^ fuel → n ≤ nextPow2.go n fuel p
  | 0, p, h => by simpa [nextPow2.go] using h
  | fuel + 1, p, h => by
      rw [nextPow2.go]
      split
      · assumption
      · refine nextPow2_go_le n fuel (2 * p) ?_
        have : p * 2 ^ (fuel + 1) = 2 * p * 2 ^ fuel := by ring
        omega

/-- The padded size is at least what it pads. -/
theorem le_nextPow2 (n : ℕ) : n ≤ nextPow2 n :=
  nextPow2_go_le n n 1 (by simpa using Nat.lt_two_pow_self.le)

theorem nextPow2_go_pow (n : ℕ) : ∀ (fuel i : ℕ), ∃ e, nextPow2.go n fuel (2 ^ i) = 2 ^ e
  | 0, i => ⟨i, rfl⟩
  | fuel + 1, i => by
      rw [nextPow2.go]
      split
      · exact ⟨i, rfl⟩
      · have := nextPow2_go_pow n fuel (i + 1)
        rwa [pow_succ'] at this

/-- The padded size is a power of two. -/
theorem nextPow2_isPow (n : ℕ) : ∃ e, nextPow2 n = 2 ^ e := by
  simpa [nextPow2] using nextPow2_go_pow n n 0

/-! ## Layout -/

/-- The instructions of the functions. -/
def totalSize (fns : List Lowered) : ℕ := (fns.map (·.code.size)).sum

@[simp] theorem totalSize_nil : totalSize [] = 0 := rfl

@[simp] theorem totalSize_cons (f : Lowered) (fs : List Lowered) :
    totalSize (f :: fs) = f.code.size + totalSize fs := by simp [totalSize]

@[simp] theorem totalSize_append (a b : List Lowered) :
    totalSize (a ++ b) = totalSize a + totalSize b := by simp [totalSize]

theorem foldl_size (fns : List Lowered) (a : ℕ) :
    fns.foldl (fun n g => n + g.code.size) a = a + totalSize fns := by
  induction fns generalizing a with
  | nil => simp
  | cons f fs ih => simp [ih, Nat.add_assoc]

/-- One step of `layout`'s fold. -/
def layoutStep (x : SMap Nat × SMap Nat × Nat) (f : Lowered) :
    SMap Nat × SMap Nat × Nat :=
  (x.1.insert f.name x.2.2, x.2.1.insert f.name f.frameSize, x.2.2 + f.code.size)

theorem layout_eq (fns : List Lowered) (tb : ℕ) :
    layout fns tb =
      (let r := fns.foldl layoutStep ({}, {}, 0)
       ({ entry := r.1, frame := r.2.1, tablesBase := tb,
          sentinel := nextPow2 (r.2.2 + 1) - 1, gpow := gpowTable (nextPow2 (r.2.2 + 1)) },
        nextPow2 (r.2.2 + 1))) := rfl

theorem layout_fold : ∀ (fns : List Lowered) (e fr : SMap Nat) (pc : ℕ),
    (fns.foldl layoutStep (e, fr, pc)).2.2 = pc + totalSize fns ∧
    (∀ n, n ∉ fns.map (·.name) →
      (fns.foldl layoutStep (e, fr, pc)).1[n]? = e[n]? ∧
        (fns.foldl layoutStep (e, fr, pc)).2.1[n]? = fr[n]?) ∧
    (∀ pre f post, fns = pre ++ f :: post → f.name ∉ post.map (·.name) →
      (fns.foldl layoutStep (e, fr, pc)).1[f.name]? = some (pc + totalSize pre) ∧
        (fns.foldl layoutStep (e, fr, pc)).2.1[f.name]? = some f.frameSize)
  | [], e, fr, pc => by simp
  | g :: gs, e, fr, pc => by
      obtain ⟨h1, h2, h3⟩ := layout_fold gs (e.insert g.name pc) (fr.insert g.name g.frameSize)
        (pc + g.code.size)
      rw [List.foldl_cons]
      refine ⟨by rw [layoutStep, h1]; simp; omega, fun n hn => ?_, fun pre f post hsplit hf => ?_⟩
      · simp only [List.map_cons, List.mem_cons, not_or] at hn
        obtain ⟨hne, hn⟩ := hn
        rw [layoutStep, (h2 n hn).1, (h2 n hn).2]
        simp [hne]
      · cases pre with
        | nil =>
            obtain ⟨rfl, rfl⟩ := List.cons.inj hsplit
            rw [layoutStep, (h2 _ hf).1, (h2 _ hf).2]
            simp
        | cons p pre =>
            obtain ⟨rfl, rfl⟩ := List.cons.inj hsplit
            obtain ⟨ha, hb⟩ := h3 pre f post rfl hf
            rw [layoutStep, ha, hb]
            simp; omega

theorem layout_size (fns : List Lowered) (tb : ℕ) :
    (layout fns tb).2 = nextPow2 (totalSize fns + 1) := by
  rw [layout_eq]
  simp [(layout_fold fns {} {} 0).1]

theorem layout_gpow (fns : List Lowered) (tb : ℕ) : (layout fns tb).1.PowOk :=
  ⟨_, rfl⟩

theorem layout_tablesBase (fns : List Lowered) (tb : ℕ) : (layout fns tb).1.tablesBase = tb := rfl

theorem layout_sentinel (fns : List Lowered) (tb : ℕ) :
    (layout fns tb).1.sentinel = (layout fns tb).2 - 1 := rfl

theorem nodup_split {fns pre post : List Lowered} {f : Lowered}
    (hnd : (fns.map (·.name)).Nodup) (hsplit : fns = pre ++ f :: post) :
    f.name ∉ post.map (·.name) := by
  subst hsplit
  simp only [List.map_append, List.map_cons] at hnd
  exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1

/-- A function's entry in the layout is the sum of the lengths before it. -/
theorem layout_entry {fns pre post : List Lowered} {f : Lowered} (tb : ℕ)
    (hnd : (fns.map (·.name)).Nodup) (hsplit : fns = pre ++ f :: post) :
    (layout fns tb).1.entry[f.name]? = some (totalSize pre) := by
  have := ((layout_fold fns {} {} 0).2.2 pre f post hsplit (nodup_split hnd hsplit)).1
  rw [layout_eq]
  simpa using this

/-- A function's frame size in the layout is its own. -/
theorem layout_frame {fns pre post : List Lowered} {f : Lowered} (tb : ℕ)
    (hnd : (fns.map (·.name)).Nodup) (hsplit : fns = pre ++ f :: post) :
    (layout fns tb).1.frame[f.name]? = some f.frameSize := by
  have := ((layout_fold fns {} {} 0).2.2 pre f post hsplit (nodup_split hnd hsplit)).2
  rw [layout_eq]
  simpa using this

/-- **`Layout.Consecutive`**: with distinct names, every function's entry is the end of the one
before it. -/
theorem layout_consecutive (fns : List Lowered) (tb : ℕ) (hnd : (fns.map (·.name)).Nodup) :
    (layout fns tb).1.Consecutive fns := by
  intro pre f post hsplit
  rw [layout_entry tb hnd hsplit, foldl_size]
  simp

/-! ## The assembled code -/

/-- A function's resolved code. -/
def resolvedFn (l : Layout) (pc0 : ℕ) (f : Lowered) : List OffsetInstruction :=
  f.code.toList.map fun ins => resolveOp l pc0 f.frameSize ins.op

/-- The resolved code of the functions laid out from `pc`. -/
def resolvedFrom (l : Layout) : List Lowered → ℕ → List OffsetInstruction
  | [], _ => []
  | f :: fs, pc => resolvedFn l (l.entry.getD f.name pc) f ++ resolvedFrom l fs (pc + f.code.size)

/-- The functions' ranges laid out from `pc`. -/
def rangesFrom : List Lowered → ℕ → List (String × ℕ × ℕ)
  | [], _ => []
  | f :: fs, pc => (f.name, pc, f.code.size) :: rangesFrom fs (pc + f.code.size)

theorem resolvedFn_length (l : Layout) (pc0 : ℕ) (f : Lowered) :
    (resolvedFn l pc0 f).length = f.code.size := by simp [resolvedFn]

theorem resolvedFrom_length (l : Layout) : ∀ (fns : List Lowered) (pc : ℕ),
    (resolvedFrom l fns pc).length = totalSize fns
  | [], _ => rfl
  | f :: fs, pc => by simp [resolvedFrom, resolvedFn_length, resolvedFrom_length l fs]

theorem resolvedFrom_append (l : Layout) : ∀ (a b : List Lowered) (pc : ℕ),
    resolvedFrom l (a ++ b) pc = resolvedFrom l a pc ++ resolvedFrom l b (pc + totalSize a)
  | [], b, pc => by simp [resolvedFrom]
  | f :: fs, b, pc => by
      simp [resolvedFrom, resolvedFrom_append l fs b, Nat.add_assoc]

theorem rangesFrom_append : ∀ (a b : List Lowered) (pc : ℕ),
    rangesFrom (a ++ b) pc = rangesFrom a pc ++ rangesFrom b (pc + totalSize a)
  | [], b, pc => by simp [rangesFrom]
  | f :: fs, b, pc => by simp [rangesFrom, rangesFrom_append fs b, Nat.add_assoc]

/-- One function of `assembleAt`'s fold. -/
def asmStep (l : Layout)
    (x : Array OffsetInstruction × Array (Nat × List RHint) × Array (String × Nat × Nat))
    (f : Lowered) :
    Array OffsetInstruction × Array (Nat × List RHint) × Array (String × Nat × Nat) :=
  let r := f.code.foldl (init := (x.1, x.2.1)) fun y ins =>
    (y.1.push (resolveOp l (l.entry.getD f.name x.1.size) f.frameSize ins.op),
      if ins.hints.isEmpty then y.2
      else y.2.push (y.1.size, ins.hints.map (resolveHint l f.frameSize)))
  (r.1, r.2, x.2.2.push (f.name, x.1.size, f.code.size))

theorem assembleAt_eq (l : Layout) (size : ℕ) (fns : List Lowered) :
    assembleAt l size fns =
      (let r := fns.foldl (asmStep l) (#[], #[], #[])
       { size, code := r.1, hints := r.2.1, mainFrame := l.frame.getD "main" 0, fns := r.2.2 }) :=
  rfl

theorem inner_fold (l : Layout) (pc0 S : ℕ) : ∀ (is : List LInstr)
    (code : Array OffsetInstruction) (hints : Array (Nat × List RHint)),
    (is.foldl (fun (y : Array OffsetInstruction × Array (Nat × List RHint)) ins =>
      (y.1.push (resolveOp l pc0 S ins.op),
        if ins.hints.isEmpty then y.2 else y.2.push (y.1.size, ins.hints.map (resolveHint l S))))
      (code, hints)).1.toList = code.toList ++ is.map fun ins => resolveOp l pc0 S ins.op
  | [], _, _ => by simp
  | i :: is, code, hints => by
      rw [List.foldl_cons, inner_fold l pc0 S is]
      simp

theorem asmStep_code (l : Layout)
    (x : Array OffsetInstruction × Array (Nat × List RHint) × Array (String × Nat × Nat))
    (f : Lowered) :
    (asmStep l x f).1.toList = x.1.toList ++ resolvedFn l (l.entry.getD f.name x.1.size) f := by
  simp only [asmStep, resolvedFn]
  rw [← Array.foldl_toList]
  exact inner_fold l _ _ _ _ _

theorem asmStep_ranges (l : Layout)
    (x : Array OffsetInstruction × Array (Nat × List RHint) × Array (String × Nat × Nat))
    (f : Lowered) :
    (asmStep l x f).2.2.toList = x.2.2.toList ++ [(f.name, x.1.size, f.code.size)] := by
  simp [asmStep]

theorem asm_fold (l : Layout) : ∀ (fns : List Lowered)
    (x : Array OffsetInstruction × Array (Nat × List RHint) × Array (String × Nat × Nat)),
    (fns.foldl (asmStep l) x).1.toList = x.1.toList ++ resolvedFrom l fns x.1.size ∧
      (fns.foldl (asmStep l) x).2.2.toList = x.2.2.toList ++ rangesFrom fns x.1.size
  | [], x => by simp [resolvedFrom, rangesFrom]
  | f :: fs, x => by
      obtain ⟨h1, h2⟩ := asm_fold l fs (asmStep l x f)
      have hsz : (asmStep l x f).1.size = x.1.size + f.code.size := by
        rw [← Array.length_toList, asmStep_code]
        simp [resolvedFn_length]
      rw [List.foldl_cons, h1, h2, asmStep_code, asmStep_ranges, hsz]
      simp [resolvedFrom, rangesFrom]

theorem assembleAt_code (l : Layout) (size : ℕ) (fns : List Lowered) :
    (assembleAt l size fns).code.toList = resolvedFrom l fns 0 := by
  rw [assembleAt_eq]
  simpa using (asm_fold l fns (#[], #[], #[])).1

theorem assembleAt_fns (l : Layout) (size : ℕ) (fns : List Lowered) :
    (assembleAt l size fns).fns.toList = rangesFrom fns 0 := by
  rw [assembleAt_eq]
  simpa using (asm_fold l fns (#[], #[], #[])).2

theorem assembleAt_size (l : Layout) (size : ℕ) (fns : List Lowered) :
    (assembleAt l size fns).size = size := rfl

/-! ## Chunks -/

theorem chunked_go : ∀ (fuel : ℕ) (c : List OffsetInstruction), c.length / chunkSize < fuel →
    Guest.chunked chunkSize (Backend.chunked.go fuel c) c.length = true ∧
      (Backend.chunked.go fuel c).flatten = c
  | 0, c, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, c, h => by
      rw [Backend.chunked.go]
      split
      · next he =>
        have : c = [] := by simpa using he
        subst this
        simp [Guest.chunked]
      · next he =>
        by_cases hle : c.length ≤ chunkSize
        · have hgo : Backend.chunked.go fuel [] = [] := by
            cases fuel <;> simp [Backend.chunked.go]
          rw [List.drop_eq_nil_of_le hle, hgo, List.take_of_length_le hle]
          simp [Guest.chunked, hle]
        · have hC : 0 < chunkSize := by decide
          obtain ⟨h1, h2⟩ := chunked_go fuel (c.drop chunkSize) (by
            rw [List.length_drop]
            have := Nat.div_eq_sub_div hC (by omega : chunkSize ≤ c.length)
            omega)
          rw [List.length_drop] at h1
          refine ⟨?_, by rw [List.flatten_cons, h2, List.take_append_drop]⟩
          rw [Guest.chunked]
          simp [hle, h1]
          omega

/-- The chunks of code are well formed and hold the code. -/
theorem chunked_ok (c : List OffsetInstruction) :
    Guest.chunked chunkSize (Backend.chunked c) c.length = true ∧ (Backend.chunked c).flatten = c :=
  chunked_go _ c (Nat.lt_succ_self _)

/-! ## The functions of the assembled program -/

/-- A range as the statement's compiled function. -/
def Assembled.fnOf (a : Assembled) (r : String × ℕ × ℕ) : CompiledFunction :=
  ⟨r.1, r.2.1, r.2.2, chunked (a.code.extract r.2.1 (r.2.1 + r.2.2)).toList⟩

theorem toFunctions_eq (a : Assembled) : a.toFunctions = a.fns.toList.map a.fnOf := rfl

theorem consecutive_ranges (a : Assembled) : ∀ (fns : List Lowered) (s : ℕ),
    consecutive s ((rangesFrom fns s).map a.fnOf) (s + totalSize fns) = true
  | [], s => by simp [rangesFrom, consecutive]
  | f :: fs, s => by
      have := consecutive_ranges a fs (s + f.code.size)
      simpa [rangesFrom, consecutive, Assembled.fnOf, Nat.add_assoc] using this

/-- **The fetch lemma at a layout**: when the layout gives `f` its entry, the assembled program
holds at `entry + i` the resolved instruction `i` of `f`. -/
theorem assembleAt_fetch {l : Layout} {size : ℕ} {fns pre post : List Lowered} {f : Lowered}
    (hsplit : fns = pre ++ f :: post) (hent : l.entry[f.name]? = some (totalSize pre))
    {logSize : ℕ} (hl : logSize ≤ maxLogBytecode) (hfit : totalSize fns ≤ 2 ^ logSize) {i : ℕ}
    (hi : i < f.code.size) :
    (Guest.assemble (assembleAt l size fns).toFunctions logSize hl).fetch
        (addressOfIndex (totalSize pre + i)) =
      some (resolveOp l (totalSize pre) f.frameSize f.code[i].op).toLeanIsaInstruction := by
  generalize ha : assembleAt l size fns = a
  have hfns : a.fns.toList = rangesFrom fns 0 := by rw [← ha, assembleAt_fns]
  have hacode : a.code.toList = resolvedFrom l fns 0 := by rw [← ha, assembleAt_code]
  have hmem : a.fnOf (f.name, totalSize pre, f.code.size) ∈ a.toFunctions := by
    rw [toFunctions_eq, hfns, hsplit, rangesFrom_append]
    simp [rangesFrom]
  have hcons : consecutive 0 a.toFunctions (totalSize fns) = true := by
    rw [toFunctions_eq, hfns]
    simpa using consecutive_ranges a fns 0
  have hgetD : l.entry.getD f.name (totalSize pre) = totalSize pre := by
    rw [KMap.getD_eq_getD_getElem?, hent]
    rfl
  have hcode : (a.code.extract (totalSize pre) (totalSize pre + f.code.size)).toList =
      resolvedFn l (totalSize pre) f := by
    rw [Array.toList_extract, hacode, hsplit, resolvedFrom_append, resolvedFrom, Nat.zero_add, hgetD,
      List.extract_eq_take_drop, List.drop_left' (resolvedFrom_length l pre 0),
      Nat.add_sub_cancel_left, List.take_left' (resolvedFn_length l _ f)]
  have hfetch := Guest.assemble_fetch (hl := hl) hcons hfit hmem (i := i) hi
  have hwc : (a.fnOf (f.name, totalSize pre, f.code.size)).WellChunked := by
    have := (chunked_ok (resolvedFn l (totalSize pre) f)).1
    rw [resolvedFn_length] at this
    show Guest.chunked chunkSize
      (chunked (a.code.extract (totalSize pre) (totalSize pre + f.code.size)).toList) f.code.size = true
    rw [hcode]
    exact this
  have hget := CompiledFunction.getElem?_code hwc hi
  have hc : (a.fnOf (f.name, totalSize pre, f.code.size)).code = resolvedFn l (totalSize pre) f := by
    show (chunked (a.code.extract (totalSize pre) (totalSize pre + f.code.size)).toList).flatten = _
    rw [hcode]
    exact (chunked_ok _).2
  rw [hc] at hget
  have hins : (a.fnOf (f.name, totalSize pre, f.code.size)).instructionAt i =
      resolveOp l (totalSize pre) f.frameSize f.code[i].op := by
    have : (resolvedFn l (totalSize pre) f)[i]? =
        some (resolveOp l (totalSize pre) f.frameSize f.code[i].op) := by
      simp [resolvedFn, hi]
    exact (Option.some.inj (hget.symm.trans this))
  rw [← hins]
  exact hfetch

theorem assemble_def (fns : List Lowered) (slots : Array KVal) :
    assemble fns slots =
      assembleAt (layout (withTables fns slots).1 (withTables fns slots).2).1
        (layout (withTables fns slots).1 (withTables fns slots).2).2 (withTables fns slots).1 := rfl

/-- The layout `assemble` computes. -/
def layoutOf (fns : List Lowered) (slots : Array KVal) : Layout :=
  (layout (withTables fns slots).1 (withTables fns slots).2).1

/-- The padded size leaves the halting slot past the code. -/
theorem assemble_size_gt (fns : List Lowered) (slots : Array KVal) :
    totalSize (withTables fns slots).1 < (assemble fns slots).size := by
  rw [assemble_def, assembleAt_size, layout_size]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_nextPow2 _)

/-- The padded size is a power of two: some `logSize` has `2 ^ logSize` slots. -/
theorem assemble_size_isPow (fns : List Lowered) (slots : Array KVal) :
    ∃ e, (assemble fns slots).size = 2 ^ e := by
  rw [assemble_def, assembleAt_size, layout_size]
  exact nextPow2_isPow _

/-- **The fetch lemma of the back end's assembly**: for functions with distinct names, the
assembled program, as the statement's `LeanVM.Guest.assemble` reads it, holds at `entry + i`
the resolved instruction `i` of each function, and every function ends before the halting
slot. -/
theorem assemble_fetch {fns : List Lowered} {slots : Array KVal} {pre post : List Lowered}
    {f : Lowered} (hnd : ((withTables fns slots).1.map (·.name)).Nodup)
    (hsplit : (withTables fns slots).1 = pre ++ f :: post) {logSize : ℕ}
    (hl : logSize ≤ maxLogBytecode) (hsize : (assemble fns slots).size = 2 ^ logSize) :
    (∀ i (hi : i < f.code.size),
      (Guest.assemble (assemble fns slots).toFunctions logSize hl).fetch
          (addressOfIndex (totalSize pre + i)) =
        some (resolveOp (layoutOf fns slots) (totalSize pre) f.frameSize
          f.code[i].op).toLeanIsaInstruction) ∧
      totalSize pre + f.code.size ≤ 2 ^ logSize - 1 := by
  have hgt := assemble_size_gt fns slots
  rw [hsize] at hgt
  have hle : totalSize pre + f.code.size ≤ totalSize (withTables fns slots).1 := by
    rw [hsplit]
    simp
  refine ⟨fun i hi => ?_, by omega⟩
  rw [assemble_def]
  exact assembleAt_fetch hsplit (layout_entry _ hnd hsplit) hl (by omega) hi

end
end LeanVM.Guest.Backend
