module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldRow

/-!
# `keccak_open`'s fold: a row of a looped round

Rounds 0 and 1 loop over their rows: row `i`'s two copies and its counter as in an unrolled round
(`rowHead`), its inner loop storing through X24, row `i` of the rows (`innerL_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

public section

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData}

/-- **A row of a looped round**. -/
theorem rowL (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    {rows : Array (Array EW)} (hsz : rows.size = 64)
    (hrow : ∀ r < 64, (rows.getD r #[]).size = 64) {t i : Nat} (ht : t < 6) (hi : i < half t)
    {vars : Nat → BitVec 64} (hv0 : vars 0 = (c.sl.getD t 0).c0.toBitVec)
    (hv1 : vars 1 = (c.sl.getD t 0).c1.toBitVec) (hv3 : vars 3 = BitVec.ofNat 64 (1024 * i))
    {ks : List (XReg × Sym)}
    {ksA ksA' : List (XReg × Sym)} (hsA : subK ksA ks = true) (hwA : wfK ksA = true)
    {bA : List Directive} {kA : Nat} (hinA : bA.IsInfixAt code kA) (hneA : bA ≠ [])
    {SA : SState} (hxA : exec bA (pS ksA) = some (SA, .call NativeRustcVmArm.Vm.Memcpy.entryLabel)) {vA : Sym}
    (hokA : CopyOk t ksA' 80 vA SA = true)
    (hvA : vA.eval (Env.ofMachine m0 (envR m0) vars) = rwA m0 + BitVec.ofNat 64 (1024 * (2 * i)))
    {ksB ksB' : List (XReg × Sym)} (hsB : subK ksB ksA' = true) (hwB : wfK ksB = true)
    {bB : List Directive} {kB : Nat} (hkB : kA + bA.length = kB) (hinB : bB.IsInfixAt code kB)
    (hneB : bB ≠ []) {SB : SState} (hxB : exec bB (pS ksB) = some (SB, .call NativeRustcVmArm.Vm.Memcpy.entryLabel))
    {vB : Sym} (hokB : CopyOk t ksB' 1104 vB SB = true)
    (hvB : vB.eval (Env.ofMachine m0 (envR m0) vars) =
      rwA m0 + BitVec.ofNat 64 (1024 * (2 * i + 1)))
    {ksZ ksZ' : List (XReg × Sym)} (hsZ : subK ksZ ksB' = true) (hwZ : wfK ksZ = true)
    {bZ : List Directive} {kZ : Nat} (hkZ : kB + bB.length = kZ) (hinZ : bZ.IsInfixAt code kZ)
    (hneZ : bZ ≠ []) {SZ : SState} (hxZ : exec bZ (pS ksZ) = some (SZ, .fall))
    (hZm : SZ.mem = []) (hokZ : regsOk t SZ ksZ' = true)
    {kI : List (XReg × Sym)} (hsI : subK kI ksZ' = true) (hwI : wfK kI = true)
    {A B CT OC : XReg} (hct0 : inK CT (.lit 0) ksZ' = true) (hA : inK A A0 kI = true)
    (hB : inK B B0 kI = true) (h22 : inK .X22 V0 kI = true) (h23 : inK .X23 V1 kI = true)
    (h24 : inK .X24 (.bin .add .W64 P (.var 3)) kI = true)
    {bL : List Directive} {kL : Nat} (hkL : kZ + bZ.length = kL) (hinL : bL.IsInfixAt code kL)
    (hneL : bL ≠ []) {SL : SState} (hxL : exec bL (loS A B CT) = some (SL, .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    (hshL : LSh .X22 .X23 .X20 .X21 (loS A B CT) SL = true)
    (hLx : SL.reg OC = some (.reg CT))
    (hLct : SL.reg CT = some (.bin .add .W64 (.reg CT) (.lit 16)))
    (hLk : keepK kI SL = true) (hco : calleeSaved OC = true) (hcc : calleeSaved CT = true)
    {bS : List Directive} {kS kE : Nat} (hkS : kL + bL.length = kS)
    (hinS : bS.IsInfixAt code kS) (hneS : bS ≠ []) {SS : SState} {lbl : Label}
    (hxS : exec bS (lstS OC) = some (SS, .cond (notEnd CT) lbl))
    (hlbl : Labels.label lbl = Host.addrOf (k + kL)) (hkE : kS + bS.length = kE)
    (hmem : SS.mem = stW .X20 .X21 0) (hsp : SS.sp = .sp)
    (hSk : keepK kI SS = true) (hSct : SS.reg CT = some (.reg CT))
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + kA)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 vars ks s.data) (hrw : ElemsAt s.data.dmem (rwA m0) (F c.sl rows t i 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + kE) ∧ Mid c m0 s'.data ∧
      KAt m0 vars kI s'.data ∧ ElemsAt s'.data.dmem (rwA m0) (F c.sl rows t (i + 1) 0) 4096) s := by
  have hsl : t < c.sl.size := by rw [hmid.sl_size]; exact ht
  have hh := half_le t
  refine (rowHead hp hmemcpy ok ht hi hv0 hv1 hsA hwA hinA hneA hxA hokA hvA hsB hwB hkB hinB
    hneB hxB hokB hvB hsZ hwZ hkZ hinZ hneZ hxZ hZm hokZ hsI hct0 hkL hpc hmid hk hrw).bind
    fun s3 ⟨hpc3, hI⟩ ↦ ?_
  refine (innerL_run hp hmul ok hwI (memK hA) (memK hB) (memK h22) (memK h23) (memK h24) hv0 hv1
    hv3 hinL hneL hxL hshL hLx hLct hLk hco hcc
    hkS hinS hneS hxS hlbl hkE hmem hsp hSk hSct (by omega)
    (G := F c.sl rows t i) (fun j hj ↦ F_succ_fun hsz hrow hsl hi hj) hpc3 hI).mono
    fun s' ⟨hpc', hI'⟩ ↦ ⟨hpc', hI'.mid, hI'.kat, ?_⟩
  have := hI'.rows
  rwa [F_row] at this

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
