module

public import NativeRustcVmX64.Layout.ReadAnnouncedSizes.Exec
public import NativeRustcVmX64.Layout.Common
public import NativeRustcVm.Transcript.Update
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeVm.Math.Layout

/-!
# `read_announced_sizes`: the model and the blocks' tests (x86-64)

After the scalars and their high limbs' checks the run is `tailP`'s (`run_tail`, `tailP_of`): the
rate's check, `build_layout`, the stack's log-size check. The rows `b10` copied are `rowsA`
(`natsOf_rows`). The blocks' tests: AL zero (`c1_eval`, `c12_eval`), a high limb nonzero
(`cnz_eval`), the rate (`c10_eval`), the stack's log-size (`ax13_eval`).
-/

namespace NativeRustcVmX64.Layout.ReadAnnouncedSizes

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model
open NativeRustcVm.Layout NativeRustcVm.Transcript LeanVM.Parameters
open NativeRustcVm (wordOf wordsOf WordAt WordsAt EWsAt wordOf_of_wordAt)
open NativeVm.Math.Layout (tailP readAnnouncedSizes_run lmA rowsA rateA rowsA_size rowsA_getD
  rateA_eq)

public section

/-- After the scalars, the run is `tailP`'s. -/
theorem run_tail (bc : Array UInt64) {s s1 : TState} {xs : Array EW}
    (hrs : (readScalars 8).run s = some (xs, s1)) :
    (readAnnouncedSizes bc).run s = (tailP bc xs).map (·, s1) := by
  rw [readAnnouncedSizes_run, show 2 + nTables = 8 from rfl, hrs]
  rfl

/-- `tailP` with the high limbs zero: the rate's check, `build_layout`, the stack's check. -/
theorem tailP_of (bc : Array UInt64) {xs : Array EW} (hall : (xs.all fun x ↦ x.c1 == 0) = true) :
    tailP bc xs = if 1 ≤ rateA xs ∧ rateA xs ≤ 4 then
      (buildLayout bc (lmA xs) (rowsA xs)).bind fun L ↦
        if 16 ≤ L.stackLog ∧ L.stackLog ≤ 30 then some (L, rateA xs) else none
    else none := by
  have e1 : (xs.getD 0 0).c0.toNat = lmA xs := rfl
  have e2 : (xs.extract 1 (1 + nTables)).map (·.c0.toNat) = rowsA xs := rfl
  have e3 : (xs.back?.getD 0).c0.toNat = rateA xs := rfl
  unfold tailP
  simp only [e1, e2, e3, hall, ↓reduceIte]
  by_cases h : 1 ≤ rateA xs ∧ rateA xs ≤ 4
  · simp only [h]
    cases buildLayout bc (lmA xs) (rowsA xs) with
    | none => rfl
    | some L =>
      simp only [Option.bind_some, show Whir.minLogStack = 16 from rfl,
        show Whir.maxLogStack = 30 from rfl, Bool.and_eq_true, decide_eq_true_eq]
  · have h' : (decide (1 ≤ rateA xs) && decide (rateA xs ≤ 4)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [h', h, Bool.false_eq_true, ↓reduceIte]

/-- The high limbs zero, as `tailP` tests them. -/
theorem all_c1 {xs : Array EW} (h : ∀ i (hi : i < xs.size), xs[i].c1 = 0) :
    (xs.all fun x ↦ x.c1 == 0) = true :=
  Array.all_eq_true.mpr fun i hi ↦ by simp [h i hi]

/-- A nonzero high limb: `None`. -/
theorem run_none_c1 {bc : Array UInt64} {s s1 : TState} {xs : Array EW}
    (hrs : (readScalars 8).run s = some (xs, s1)) {i : Nat} (hi : i < xs.size)
    (h : xs[i].c1 ≠ 0) : (readAnnouncedSizes bc).run s = none := by
  rw [readAnnouncedSizes_run, show 2 + nTables = 8 from rfl, hrs]
  have : (xs.all fun x ↦ x.c1 == 0) = false := by
    rw [Bool.eq_false_iff]
    intro ha
    rw [Array.all_eq_true] at ha
    exact h (by simpa using ha i hi)
  simp only [Option.bind_some, tailP, this, Bool.false_eq_true, ↓reduceIte,
    Option.map_none]

/-- **The rows** `b10` copied, read back by `build_layout`. -/
theorem natsOf_rows {m : MachineData} {xs : Array EW} (hsz : xs.size = 8) {p : BitVec 64}
    (h : ∀ t (ht : t < 6), WordAt m.dmem (p + BitVec.ofNat 64 (8 * t))
      (xs[1 + t]'(by omega)).c0) :
    natsOf m p nTables = rowsA xs := by
  have hs1 : (natsOf m p nTables).size = 6 := by
    simp [natsOf, NativeRustcVm.wordsOf, nTables]
  have hs2 := rowsA_size hsz
  refine Array.ext (by rw [hs1, hs2]) fun i h1 h2 ↦ ?_
  have hi : i < 6 := by rw [hs1] at h1; exact h1
  have e1 := natsOf_getD m p (n := nTables) (t := i) (by simp only [nTables]; omega)
  have e2 := rowsA_getD hsz hi
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some,
    Array.getElem?_eq_getElem (show 1 + i < xs.size by omega)] at e1 e2
  rw [e1, e2, wordOf_of_wordAt (h i hi)]

theorem rateA_get {xs : Array EW} (hsz : xs.size = 8) :
    rateA xs = (xs[7]'(by omega)).c0.toNat := by
  rw [rateA_eq hsz, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
    Option.getD_some]

theorem lmA_get {xs : Array EW} (hsz : xs.size = 8) :
    lmA xs = (xs[0]'(by omega)).c0.toNat := by
  show (xs.getD 0 0).c0.toNat = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]

variable [Labels]

/-- `b1`'s test: AL (of EAX) zero. -/
theorem c1_eval (env : Env) : c1.eval env = decide ((env.regs .rax).toNat % 256 = 0) := by
  simp only [c1, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, UnOp.apply]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj]
  simp only [toNat_low, toNat_ext, BitVec.toNat_and, Nat.and_self, BitVec.toNat_ofNat,
    show Width.W8.bits = 8 from rfl, show Width.W32.bits = 32 from rfl]
  omega

/-- `b12`'s test: AL zero. -/
theorem c12_eval (env : Env) : c12.eval env = decide ((env.regs .rax).toNat % 256 = 0) := by
  simp only [c12, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj]
  simp only [toNat_low, toNat_ext, BitVec.toNat_and, Nat.and_self, BitVec.toNat_ofNat,
    show Width.W8.bits = 8 from rfl]
  omega

/-- A high limb's test. -/
theorem cnz_eval (env : Env) {o : Nat} {v : UInt64} (h : env.load 0 o 8 = v.toBitVec) :
    (cnz o).eval env = decide (v ≠ 0) := by
  simp only [cnz, SBool.eval, Sym.eval, CmpOp.apply, low_W64, h]
  by_cases hv : v = 0
  · subst hv; rfl
  · have : v.toBitVec ≠ BitVec.ofNat 64 0 := fun h' ↦ hv (UInt64.toBitVec_inj.mp h')
    simp [this, hv]

omit [Labels] in
/-- The rate's test: `rate - 1 > 3` (unsigned). -/
theorem rate_cond (x : BitVec 64) :
    ((!(x + BitVec.ofNat 64 18446744073709551615).ult (BitVec.ofNat 64 3) &&
      !((x + BitVec.ofNat 64 18446744073709551615) == BitVec.ofNat 64 3)) = true) ↔
      ¬(1 ≤ x.toNat ∧ x.toNat ≤ 4) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
    beq_eq_false_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩; bv_omega
  · intro h; constructor <;> bv_omega

/-- `b10`'s test: the rate out of `1..=4`. -/
theorem c10_eval (env : Env) : c10.eval env = true ↔
    ¬(1 ≤ (env.load 0 120 8).toNat ∧ (env.load 0 120 8).toNat ≤ 4) := by
  simp only [c10, r10S, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  exact rate_cond _

/-- `b13`'s RAX: `1` for a stack log-size in `16..=30`, else `0`. -/
theorem ax13_eval (env : Env) {n : Nat} (hn : n < 2 ^ 64)
    (h : env.load 1 16 8 = n.toUInt64.toBitVec) :
    ax13.eval env = if 16 ≤ n ∧ n ≤ 30 then 1#64 else 0#64 := by
  have e : n.toUInt64.toBitVec.toNat = n := by simp; omega
  simp only [ax13, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h,
    BitVec.ult]
  by_cases hc : 16 ≤ n ∧ n ≤ 30
  · have : decide ((BitVec.ofNat 64 18446744073709551600 + n.toUInt64.toBitVec).toNat <
        (BitVec.ofNat 64 15).toNat) = true := by
      rw [decide_eq_true_eq]; bv_omega
    rw [this, NativeVm.Math.Layout.ite_true_of hc]
    rfl
  · have : decide ((BitVec.ofNat 64 18446744073709551600 + n.toUInt64.toBitVec).toNat <
        (BitVec.ofNat 64 15).toNat) = false := by
      rw [decide_eq_false_iff_not]; bv_omega
    rw [this, NativeVm.Math.Layout.ite_false_of hc]
    rfl

end

end NativeRustcVmX64.Layout.ReadAnnouncedSizes
