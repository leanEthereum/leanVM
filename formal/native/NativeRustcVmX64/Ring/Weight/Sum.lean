module

public import NativeRustcVmX64.Ring.Weight.Vals
public import NativeRustcVmX64.Ring.Weight.Exit
public import NativeRustcVmX64.Ring.Weight.FactsA
public import NativeRustcVmX64.Ring.Weight.Sw

/-!
# `ring_weight` with `r` empty (x86-64)

`b3` clears the total; `b4` adds four coefficients a turn (16 turns, the coefficients the window
`rsC`, `sumTurn`, `sumLoop`); `b5` jumps to the epilogue with the coefficients' sum, `ringWeight`
of an empty `r` (`csum_eq`).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingWeight

@[expose] public section

/-- The coefficients' window. -/
abbrev rsC (m0 : MachineData) : List (BitVec 64 × Nat) := [(reg m0 .r9 + BitVec.ofNat 64 0, 1024)]

/-- The first `n` coefficients' sum. -/
def csum (m0 : MachineData) (n : Nat) : EW := ((cL m0).toList.take n).foldl (· + ·) 0

end

public section

variable {m0 : MachineData}

theorem layC (h : RingWeightPre m0) : Lay m0 672 NW (rsC m0) :=
  lay1 h.1 h.2.2.2.2.1.1 h.2.2.2.2.1.2 (by decide)

theorem csum_succ {n : Nat} (hn : n < 64) : csum m0 (n + 1) = csum m0 n + ce m0 n := by
  unfold csum
  have hs : n < (cL m0).toList.length := by simp [arr, coeffCount]; omega
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hs]
  simp [arr]

theorem csum4 {t : Nat} (ht : t < 16) : csum m0 (4 * (t + 1)) =
    csum m0 (4 * t) + ce m0 (4 * t) + ce m0 (4 * t + 1) + ce m0 (4 * t + 2) + ce m0 (4 * t + 3) := by
  rw [show 4 * (t + 1) = 4 * t + 3 + 1 by omega, csum_succ (by omega), csum_succ (by omega),
    csum_succ (by omega), csum_succ (by omega)]

/-- With `r` empty, `ringWeight` is the coefficients' sum. -/
theorem csum_eq (h0 : nR m0 = 0) : csum m0 64 = ringWeight (rL m0) (qL m0) (cL m0) := by
  have hr : rL m0 = #[] := by
    rw [← Array.size_eq_zero_iff, size_rL, h0]
  rw [ringWeight_eq, hr, accW_nil (by rw [size_cL]), size_cL]
  rfl

theorem sumX0 [Labels] (h : RingWeightPre m0) {T : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 672 NW (rsC m0) noWr T vals m) {t : Nat} (ht : t < 16)
    (h20 : vals 20 = c0 (csum m0 (4 * t))) {ret : BitVec 64} :
    (sumX 20 (64 * t)).eval (envS m0 m 672 (rsC m0) vals ret) = c0 (csum m0 (4 * (t + 1))) := by
  have ld := fun (j i : Nat) (hji : 0 + j = 16 * i) (hi : i < 64) ↦
    win_c0 (ret := ret) h.1 h.2.2.2.2.1.1 h.2.2.2.2.1.2 hB hji (show 16 * i + 16 ≤ 16 * coeffCount by
      simp only [coeffCount]; omega)
  simp only [sumX, ev_xor]
  rw [ld _ (4 * t) (by omega) (by omega), ld _ (4 * t + 1) (by omega) (by omega),
    ld _ (4 * t + 2) (by omega) (by omega), ld _ (4 * t + 3) (by omega) (by omega), csum4 ht]
  show vals 20 ^^^ _ ^^^ _ ^^^ _ ^^^ _ = _
  rw [h20]
  rfl

theorem sumX1 [Labels] (h : RingWeightPre m0) {T : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 672 NW (rsC m0) noWr T vals m) {t : Nat} (ht : t < 16)
    (h21 : vals 21 = c1 (csum m0 (4 * t))) {ret : BitVec 64} :
    (sumX 21 (64 * t + 8)).eval (envS m0 m 672 (rsC m0) vals ret) = c1 (csum m0 (4 * (t + 1))) := by
  have ld := fun (j i : Nat) (hji : 0 + j = 16 * i + 8) (hi : i < 64) ↦
    win_c1 (ret := ret) h.1 h.2.2.2.2.1.1 h.2.2.2.2.1.2 hB hji (show 16 * i + 16 ≤ 16 * coeffCount by
      simp only [coeffCount]; omega)
  simp only [sumX, ev_xor]
  rw [ld _ (4 * t) (by omega) (by omega), ld _ (4 * t + 1) (by omega) (by omega),
    ld _ (4 * t + 2) (by omega) (by omega), ld _ (4 * t + 3) (by omega) (by omega), csum4 ht]
  show vals 21 ^^^ _ ^^^ _ ^^^ _ ^^^ _ = _
  rw [h21]
  rfl

variable [Host] {k : Nat}

/-- **A turn of the sum.** -/
theorem sumTurn (hp : Placed code k) (h : RingWeightPre m0) {t : Nat} (ht : t < 16)
    {st : MachineState}
    (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b4Offset (rsC m0) noWr (tZ (sz1 1024) cAl t) (vv m0 0 0 (csum m0 (4 * t)) 0)
      (fun _ ↦ True) st) :
    Eventually (step1 Host.exe) (At m0 k (if decide (t < 15) then 96 else 108) (rsC m0) noWr
      (tZ (sz1 1024) cAl (t + 1)) (vv m0 0 0 (csum m0 (4 * (t + 1))) 0) (fun _ ↦ True)) st :=
  jcond hp (layC h) b4_in_code (by simp [b4]) rfl (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_2_at) (f_b4 t ht)
    (fun _ _ _ ↦ rfl) (fun m hB _ ret ↦ by
      wv
      · exact sumX0 h hB ht rfl
      · exact sumX1 h hB ht rfl)
    rfl rfl rfl (fun _ _ ↦ oneAl rfl (al0 _)) rfl (fun _ _ _ _ _ ↦ trivial) hA

/-- **The sum**, from turn `t`. -/
theorem sumLoop (hp : Placed code k) (h : RingWeightPre m0) :
    ∀ n t, t + n = 15 → ∀ {st : MachineState},
      At m0 k NativeRustcVmX64.Vm.RingWeight.b4Offset (rsC m0) noWr (tZ (sz1 1024) cAl t) (vv m0 0 0 (csum m0 (4 * t)) 0)
        (fun _ ↦ True) st →
      Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingWeight.b5Offset (rsC m0) noWr (tZ (sz1 1024) cAl 16)
        (vv m0 0 0 (csum m0 64) 0) (fun _ ↦ True)) st := by
  intro n
  induction n with
  | zero =>
    intro t ht st hA
    obtain rfl : t = 15 := by omega
    have h' := sumTurn hp h (t := 15) (by decide) hA
    rw [ite_eq_right (by decide)] at h'
    exact h'
  | succ n ih =>
    intro t ht st hA
    refine Eventually.bind (sumTurn hp h (by omega) hA) fun st' h' ↦ ?_
    rw [ite_eq_left (decide_eq_true (by omega))] at h'
    exact ih (t + 1) (by omega) h'

/-- **`ring_weight` with `r` empty.** -/
theorem sumPath (hp : Placed code k) (h : RingWeightPre m0) (h0 : nR m0 = 0)
    {I : MachineData → Prop} {st : MachineState}
    (hA : At m0 k NativeRustcVmX64.Vm.RingWeight.b3Offset [] noWr (tA sz0 []) (vv m0 0 0 0 0) I st) :
    Eventually (step1 Host.exe) (Goal m0) st := by
  refine Eventually.bind (jfall hp (lay0 h.1) b3_in_code (by simp [b3]) (next := 96) rfl f_b3
    (vals' := vv m0 0 0 (csum m0 (4 * 0)) 0) (I' := fun _ ↦ True) (fun _ _ _ _ ↦ by wv <;> rfl) rfl rfl rfl
    (fun _ _ ↦ noAl rfl) rfl (fun _ _ _ _ _ ↦ trivial) hA) fun st hA ↦ ?_
  have hA := hA.sw sw_sum.1 (rs' := rsC m0) (wr' := noWr) rfl (fun _ _ ↦ oneAl rfl (al0 _)) outs_noWr
  refine Eventually.bind (sumLoop hp h 15 0 rfl hA) fun st hA ↦ ?_
  refine Eventually.bind (jjump hp (layC h) b5_in_code (by simp [b5])
    (by exact hp.label NativeRustcVmX64.Vm.RingWeight.label_13_at) f_b5 (vals' := vv m0 0 0 (csum m0 64) 0)
    (I' := fun _ ↦ True) (fun _ _ _ _ ↦ by wv) rfl rfl rfl (fun _ _ ↦ noAl rfl) rfl
    (fun _ _ _ _ _ ↦ trivial) hA) fun st hA ↦ ?_
  have hA := hA.sw sw_sum.2 (rs' := rsO m0) (wr' := oWr) rfl (fun _ _ ↦ oneAl rfl (al0 _))
    outs_noWr
  exact exitW hp h (fun i hi ↦ by interval_cases i <;> simp only [vv]) rfl rfl (csum_eq h0) hA

end

end NativeRustcVmX64.Ring.Weight
