module

public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.LinearTranspose.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.WeightsB
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontG

/-!
# `verify_layer`: the weights loop

From `AtLoop` at `.LVerifyLayer_30` (`k + NativeRustcVmArm.Vm.VerifyLayer.b57Offset`, no weight written): the `1600` iterations
(`wloop`, by induction on the weights left), each `phaseA` then `phaseB`, and after the last one
the tail (`weights_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)

public section

theorem layerWeights_size (eq : Array EW) (beta : EW) : (layerWeights eq beta).size = 1600 := by
  rw [layerWeights, Array.size_map, Array.size_range]
  rfl

/-- **The layer's weights in memory**, from each one's. -/
theorem lw_ewsAt {m0 : MachineData} {eq : Array EW} {beta : EW} {d : DataMem}
    (h : ∀ i < 1600, NativeRustcVm.EWAt d (sA m0 + BitVec.ofNat 64 (51200 + 16 * i))
      (lwF eq beta i)) :
    NativeRustcVm.EWsAt d (sA m0 + BitVec.ofNat 64 51200) (layerWeights eq beta).toList := by
  rw [NativeRustcVm.ewsAt_iff]
  intro i hi
  have hi' : i < 1600 := by
    rw [Array.length_toList, layerWeights_size] at hi
    exact hi
  rw [NativeRustcVm.addr_add_add]
  have e : (layerWeights eq beta).toList[i] = lwF eq beta i := by
    simp [layerWeights, lwF]
  rw [e]
  exact h i hi'

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {s' : TState} {t0 t1 t2 beta : EW} {mu point eq : Array EW}

/-- **The loop from head `j`**, by induction on the weights left. -/
theorem wloop (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hlt : ∀ ws, Spec (label NativeRustcVmArm.Vm.LinearTranspose.entryLabel) (LinearTransposePre ws) (LinearTransposePost ws))
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hext : Spec (label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hps : point.size ≤ 30) (heq : eq.size = 2048)
    (hrun : runL s c m0 = some (⟨t0 + beta * (t1 + beta * t2), mu, point,
      keccakLinearTranspose (layerWeights eq beta)⟩, s')) :
    ∀ n j (st : MachineState), 1600 - j = n → WHead k m0 a s' t0 t1 t2 beta mu point eq j st →
      Eventually (step1 Host.exe) (Goal a s c m0) st := by
  intro n
  induction n with
  | zero =>
    intro j st hn hh
    have := hh.lt
    omega
  | succ n ih =>
    intro j st hn hh
    refine phaseA hp hpre hmul hps heq hh fun st1 hpc1 hmid h0 h1 ↦ ?_
    refine phaseB hp hpre hmul hps heq hpc1 hmid h0 h1
      (fun st2 _ hh2 ↦ ih (j + 1) st2 (by omega) hh2) ?_
    intro st2 _ hpc2 hb2 r23 r25 r24 hmem
    exact tail hp hpre hlt hmul hmemcpy hext hpc2 hb2 hrun hmem.fw r23 r25 r24 hps
      (layerWeights_size eq beta) (lw_ewsAt hmem.lw) hmem.mu hmem.pt hmem.ts

/-- **From the weights loop's head to the goal.** -/
theorem weights_run (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hlt : ∀ ws, Spec (label NativeRustcVmArm.Vm.LinearTranspose.entryLabel) (LinearTransposePre ws) (LinearTransposePost ws))
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hext : Spec (label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b57Offset))
    (h : AtLoop m0 a s c t0 t1 t2 beta mu point eq s' st.data) :
    Eventually (step1 Host.exe) (Goal a s c m0) st :=
  wloop hp hpre hlt hmul hmemcpy hext h.hps h.heq h.run 1600 0 st rfl
    ⟨by decide, hpc, FB.body hpre h.fb, h.x19, h.x26, h.x29, h.x20, h.x23, h.x25, h.x24,
      ⟨h.fw, h.f144, h.hmu, h.hpt, h.ts, h.heqw, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩,
      h.f96⟩

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
