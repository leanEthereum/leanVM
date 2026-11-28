module

public import NativeRustcVmArm.Layout.ReadAnnouncedSizes.Checks

/-!
# `read_announced_sizes`: the model after the scalars, the footprints

After the scalars and their high limbs' checks the run is `tailP`'s (`run_tail`, `tailP_of`): the
rate's check, `build_layout`, the stack's log-size check. The rows `b10` copied are `rowsA`
(`natsOf_rows`). Where the body may write (`Rout`, the stack) is apart from the round constants and
the read-only data (`rc_out`, `rodata_out`); a body's memory is the entry's outside them
(`Fr.sameOut`).
-/

namespace NativeRustcVmArm.Layout.ReadAnnouncedSizes

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReadAnnouncedSizes NativeVm.Model
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

/-- **The rows** `b10` copied, read back by `build_layout`. -/
theorem natsOf_rows {m : MachineData} {xs : Array EW} (hsz : xs.size = 8) {p : UInt64}
    (h : ∀ t (ht : t < 6), WordAt m.dmem (p.toBitVec + BitVec.ofNat 64 (8 * t))
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

/-- The rate's test in `b10`: `rate - 1 > 3` (unsigned). -/
theorem rate_cond (x : BitVec 64) :
    ((!(x - 1#64).ult 3#64 && !((x - 1#64) == 3#64)) = true) ↔ ¬(1 ≤ x.toNat ∧ x.toNat ≤ 4) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
    beq_eq_false_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩; bv_omega
  · intro h; constructor <;> bv_omega

/-- The stack's test in `b13`: `stack_log - 16 < 15` (unsigned). -/
theorem stack_cond {n : Nat} (hn : n < 2 ^ 64) :
    ((n.toUInt64.toBitVec - 16#64).ult 15#64 = true) ↔ (16 ≤ n ∧ n ≤ 30) := by
  have e : n.toUInt64.toBitVec.toNat = n := by simp; omega
  simp only [BitVec.ult, decide_eq_true_eq]
  constructor
  · intro h; bv_omega
  · intro h; bv_omega

variable [Labels]

/-- Where a body writes is apart from the round constants. -/
theorem rc_out {bc : Array UInt64} {a : DecArea} {s : TState} {m0 : MachineData}
    (hpre : ReadAnnouncedSizesPre bc a s m0) (q : BitVec 64)
    (hq : Rout m0 q ∨ InRange (stackBelow m0 N) N q) : ¬InRange rcAddr 192 q := by
  obtain ⟨hst, hrc, -, hts, htok, -, -, hlr, -, -, hlrc, -, -⟩ := hpre
  have hTn := hts.footprint.1.2
  intro h
  rcases hq with (hq | hq) | hq
  · exact not_inRange_of_apart hlrc hlr.2 hrc.2.1 hq h
  · exact not_inRange_of_apart htok.2.2 hTn hrc.2.1 hq h
  · exact not_inRange_of_apart hrc.2.2 hrc.2.1 (stack_noWrap hst) h hq

/-- Where a body writes is apart from the read-only data. -/
theorem rodata_out {bc : Array UInt64} {a : DecArea} {s : TState} {m0 : MachineData}
    (hpre : ReadAnnouncedSizesPre bc a s m0) (q : BitVec 64)
    (hq : Rout m0 q ∨ InRange (stackBelow m0 N) N q) (t : NativeRustcVm.Data.Item) :
    ¬InRange (rodataAddr t) t.bytes.length q := by
  obtain ⟨hst, -, hrod, hts, -, htrod, -, hlr, -, hlrod, -, -, -⟩ := hpre
  have hTn := hts.footprint.1.2
  intro h
  rcases hq with (hq | hq) | hq
  · exact not_inRange_of_apart (hlrod t) hlr.2 (hrod t).2.1 hq h
  · exact not_inRange_of_apart (htrod t) hTn (hrod t).2.1 hq h
  · exact not_inRange_of_apart (hrod t).2.2 (hrod t).2.1 (stack_noWrap hst) h hq

/-- The frame is apart from the `TState` and its decoded area. -/
theorem frame_tstate {bc : Array UInt64} {a : DecArea} {s : TState} {m0 : MachineData}
    (hpre : ReadAnnouncedSizesPre bc a s m0) (q : BitVec 64) (hq : InRange (fbase m0 208) 208 q) :
    ¬InRange (tt m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  obtain ⟨hst, -, -, hts, htok, -⟩ := hpre
  have hF : 208 ≤ N := by have := le_rs; omega
  have hfn := (Arrays.frame_ok hst hF).2.1
  obtain ⟨⟨-, hTn⟩, ⟨-, hAn⟩, -⟩ := hts.footprint
  exact ⟨not_inRange_of_apart (apart_frame hst hF htok.1) hfn hTn hq,
    not_inRange_of_apart (apart_frame hst hF htok.2.1) hfn hAn hq⟩

omit [Labels] in
/-- **A body's memory**: the entry's outside the outputs and the stack. -/
theorem Fr.sameOut {m0 st : MachineData} (hb : Fr m0 st) :
    SameOutside m0.dmem st.dmem (fun q ↦ InRange (ll m0) layoutBytes q ∨
      InRange (tt m0) tstateBytes q ∨ InRange (stackBelow m0 N) N q) :=
  fun q hq ↦ hb.same q fun h ↦ hq (by
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h))

end

end NativeRustcVmArm.Layout.ReadAnnouncedSizes
