module

public import NativeVm.Code.Phase3.Imle

/-!
# The fingerprints

Phase 3's constants (`constOps`: `1`, `g`, `g²`, `0` into slots `0`, `1`, `2`, `12`) and the
framework fingerprints of a side (`fpOps pc mc bc dst`, `fingerprints`' three dot products, into
words `dst`, `dst + 2`, `dst + 4`), as straight-line programs (`EOp`) whose values are the model's
expressions (`fpOps_run`, `fingerprints_eq`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

/-- Word of weight `i`. -/
def wsl (i : Nat) : Nat := 52670 + 2 * i

theorem wR_off : wR.off = 52670 := by decide
theorem memR_off : memR.off = 52840 := by decide
theorem shareR_off : shareR.off = 52848 := by decide

/-- The slots' names. -/
abbrev sOne : Nat := sl 0
abbrev sGen : Nat := sl 1
abbrev sG2 : Nat := sl 2
abbrev sIm : Nat := sl 3
abbrev sIb : Nat := sl 4
abbrev sPc : Nat := sl 5
abbrev sT6 : Nat := sl 6
abbrev sT7 : Nat := sl 7
abbrev sZero : Nat := sl 12

/-- `1`, `g`, `g²`, `0`. -/
def constOps : List EOp := [.set sOne 1, .set sGen gen, .mul sGen sGen sG2, .set sZero 0]

/-- A side's fingerprints into `dst`, `dst + 2`, `dst + 4`, from the slots of `pc`, the memory's
and the bytecode's counters. -/
def fpOps (pc mc bc dst : Nat) : List EOp :=
  [.mul (wsl 0) sOne sT6, .add sZero sT6 sT6, .mul (wsl 1) pc sT7, .add sT6 sT7 sT6,
    .mul (wsl 2) sOne sT7, .add sT6 sT7 dst,
    .mul (wsl 0) sGen sT6, .add sZero sT6 sT6, .mul (wsl 1) sIm sT7, .add sT6 sT7 sT6,
    .mul (wsl 2) mc sT7, .add sT6 sT7 sT6, .mul (wsl 3) 52840 sT7, .add sT6 sT7 sT6,
    .mul (wsl 4) 52842 sT7, .add sT6 sT7 (dst + 2),
    .mul (wsl 0) sG2 sT6, .add sZero sT6 sT6, .mul (wsl 1) sIb sT7, .add sT6 sT7 sT6,
    .mul (wsl 2) bc sT7, .add sT6 sT7 sT6, .add sT6 52848 (dst + 4)]

theorem dot3 (a b c x y z : EW) : dot #[a, b, c] #[x, y, z] = 0 + a * x + b * y + c * z := by
  simp only [dot, ← Array.foldl_toList, Array.toList_zipWith]
  rfl

theorem dot5 (a b c d e x y z u v : EW) :
    dot #[a, b, c, d, e] (#[x, y, z] ++ #[u, v]) = 0 + a * x + b * y + c * z + d * u + e * v := by
  simp only [dot, ← Array.foldl_toList, Array.toList_zipWith]
  rfl

theorem extract3 (w : Array EW) (h : 5 ≤ w.size) :
    w.extract 0 3 = #[w[0], w[1], w[2]] := by
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp only [Array.size_extract] at h1
    rcases i with _ | _ | _ | i <;> simp
    omega

theorem extract5 (w : Array EW) (h : 5 ≤ w.size) :
    w.extract 0 5 = #[w[0], w[1], w[2], w[3], w[4]] := by
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp only [Array.size_extract] at h1
    rcases i with _ | _ | _ | _ | _ | i <;> simp
    omega

theorem gpow_zero' : gpow 0 = 1 := by
  apply Equiv.EW.toE_injective
  rw [Equiv.toE_gpow, Equiv.EW.toE_one, LeanVM.Protocol.Verifier.gpow, pow_zero]

theorem gpow_two' : gpow 2 = gen * gen := by
  apply Equiv.EW.toE_injective
  rw [Equiv.toE_gpow, Equiv.EW.toE_mul, Equiv.toE_gen, LeanVM.Protocol.Verifier.gpow, pow_two]

/-- **The fingerprints** as the programs compute them. -/
theorem fingerprints_eq (w : Array EW) (h : 5 ≤ w.size) (m0 m1 : EW) (ml bl : Array EW)
    (share pc mc bc : EW) :
    fingerprints w #[m0, m1] ml bl share pc mc bc =
      #[(0 : EW) + w[0] * (1 : EW) + w[1] * pc + w[2] * (1 : EW),
        (0 : EW) + w[0] * gen + w[1] * indexMle ml + w[2] * mc + w[3] * m0 + w[4] * m1,
        (0 : EW) + w[0] * (gen * gen) + w[1] * indexMle bl + w[2] * bc + share] := by
  rw [fingerprints, extract3 w h, extract5 w h, dot3, dot3,
    show (#[sepMemW, indexMle ml, mc] ++ #[m0, m1] : Array EW) = #[sepMemW, indexMle ml, mc] ++ #[m0, m1]
      from rfl, dot5, gpow_zero', sepBytecodeW, gpow_two']
  rfl

theorem constOps_run (v : Nat → EW) :
    opsRun constOps v sOne = 1 ∧ opsRun constOps v sGen = gen ∧
      opsRun constOps v sG2 = gen * gen ∧ opsRun constOps v sZero = 0 := by
  simp [opsRun, constOps, EOp.eval, EOp.dst, sl]

/-- The push side's fingerprints' words. -/
abbrev fpPush : Nat := 52860
/-- The pull side's. -/
abbrev fpPull : Nat := 52866

theorem fpR_off : fpR.off = fpPush := by decide

theorem fpOps_run (v : Nat → EW) (pc mc bc dst : Nat) (hd : dst = fpPush ∨ dst = fpPull)
    (hpc : pc = sOne ∨ pc = sPc) (hmc : mc = sOne ∨ mc = 52844)
    (hbc : bc = sOne ∨ bc = 52846) :
    opsRun (fpOps pc mc bc dst) v dst = v sZero + v (wsl 0) * v sOne + v (wsl 1) * v pc + v (wsl 2) * v sOne ∧
    opsRun (fpOps pc mc bc dst) v (dst + 2) = v sZero + v (wsl 0) * v sGen + v (wsl 1) * v sIm +
      v (wsl 2) * v mc + v (wsl 3) * v 52840 + v (wsl 4) * v 52842 ∧
    opsRun (fpOps pc mc bc dst) v (dst + 4) = v sZero + v (wsl 0) * v sG2 + v (wsl 1) * v sIb +
      v (wsl 2) * v bc + v 52848 := by
  rcases hd with rfl | rfl <;> rcases hpc with rfl | rfl <;> rcases hmc with rfl | rfl <;>
    rcases hbc with rfl | rfl <;> simp [opsRun, fpOps, EOp.eval, EOp.dst, sl, wsl]

end NativeVm.Code.P3
