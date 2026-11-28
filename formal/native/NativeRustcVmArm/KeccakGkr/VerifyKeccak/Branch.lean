module

public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Fin

/-!
# `verify_keccak`'s branches to the failure exit

A block without writes ending in a branch to `.LVerifyKeccak_31` taken exactly when a flag `b`
is false (`failBranch`): on `false` the failure exit (the model's `none`), on `true` on. The
flags: an `Option<EW>`'s tag in the frame, loaded as a word or its low half (`cond8`, `cond4`);
`Option<()>` in X0 (`condX0`, `condW0`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak

public section

section
variable [Labels] {env : Env} {r : Option EW} {o : Nat}

theorem cond8 (ht : OptEWAt env.mem0 (env.base 0 + BitVec.ofNat 64 o) r) :
    (SBool.cmp .eq .W64 (.load 0 o 8) (.lit 0)).eval env = !r.isSome := by
  cases r with
  | none =>
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Sumcheck.load_word ht]; rfl
  | some x =>
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Sumcheck.load_word ht.1]; rfl

theorem cond4 (ht : OptEWAt env.mem0 (env.base 0 + BitVec.ofNat 64 o) r) :
    (SBool.not (.bit .W32 (.load 0 o 4) 0)).eval env = !r.isSome := by
  have key : ∀ v : UInt64, NativeRustcVm.WordAt env.mem0 (env.base 0 + BitVec.ofNat 64 o) v →
      env.load 0 o 4 = BitVec.ofInt 64 (Int.ofBytes ((NativeRustcVm.wordBytes v).take 4)) :=
    fun v hv ↦ Env.load_of_bytesAt (by simp [NativeRustcVm.length_wordBytes])
      (NativeRustcVm.BytesAt.take hv 4)
  cases r with
  | none => simp only [SBool.eval, Sym.eval, key 0 ht]; decide
  | some x => simp only [SBool.eval, Sym.eval, key 1 ht.1, Option.isSome_some]; decide

theorem condX0 {b : Bool} (hx : (env.regs .X0) = (okWord b).toBitVec) :
    (SBool.not (.bit .W32 (.reg .X0) 0)).eval env = !b := by
  simp only [SBool.eval, Sym.eval, hx]; cases b <;> decide

theorem condW0 {b : Bool} (hx : (env.regs .X0) = (okWord b).toBitVec) :
    (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval env = !b := by
  simp only [SBool.eval, Sym.eval, hx]; cases b <;> decide

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **A branch to the failure exit**, taken when `b` is false. -/
theorem failBranch (hp : Placed code k) (hn : Nums a inst m0) {ds : List Directive} {i : Nat}
    {S' : SState} {c : SBool} {m : MachineData} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .cond c NativeRustcVmArm.Vm.VerifyKeccak.label_31)) (hmid : Mid m0 m)
    (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    (hrk : regsL.all (fun r ↦ (midS.reg r).isSome && S'.reg r == midS.reg r) = true)
    (hck : csL.all (fun r ↦ (midS.reg r).isSome && S'.reg r == midS.reg r) = true)
    {b : Bool} (hc : c.eval (envM m0 m) = !b) (hfail : b = false → run0 s inst output m0 = none)
    (cont : b = true → ∀ m', Mid m0 m' → m'.dmem = m.dmem →
      (∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r) →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf i⟩ := by
  refine blockStep hn hk hrun hmid.fr hmem hsp fun st hm1 hfr1 hd hpc ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only [PcOk, hc] at hpc
  cases b
  · simp only [Bool.not_false, ↓reduceIte] at hpc
    subst hpc
    exact goal_fail hp hn hfr1 (hfail rfl)
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    subst hpc
    exact cont rfl d ⟨hfr1, hmid.regs.block (matchM hn hmid.fr) hm1 hrk, by rw [hd]; exact hmid.pk⟩
      hd (cs_block (matchM hn hmid.fr) hm1 hck)

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
