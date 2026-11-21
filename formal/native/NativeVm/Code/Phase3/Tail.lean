module

public import NativeVm.Code.Phase3.TailCode
public import NativeVm.Code.Phase3.TailRest

/-!
# Phase 3 after the transcript

`busOut`: what `verifyBusBalance` returns from the values it read (its body after
`computedBytecodeValue`, the same `let`s); `tail_spec`: `tailCode` stores it, the bus at `busR`,
its claims at `claimsR`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters
  LeanVM.Protocol.Verifier

/-- **The bus's result** from the slot weights, `β`, the GKR point and trees' values, the memory's
limbs and final counter, the bytecode's final counter, share and point: `verifyBusBalance`'s body
after the transcript. -/
def busOut (layout : LayoutW) (weights : Array EW) (beta : EW) (point treeValues memory : Array EW)
    (memoryFinal bytecodeFinal share : EW) (bytecodePoint : Array EW) : BusResultW :=
  let frameworkLogRows := #[0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout #[] layout.count
  let memoryLow := point.extract 0 layout.logMemory
  let bytecodeLow := point.extract 0 layout.logBytecode
  let claims : Array ColumnClaimW :=
    #[⟨memory0, memoryLow, memory.getD 0 0⟩, ⟨memory1, memoryLow, memory.getD 1 0⟩,
      ⟨memoryFinalCounters, memoryLow, memoryFinal⟩,
      ⟨bytecodeFinalCounters, bytecodeLow, bytecodeFinal⟩]
  let fp := fingerprints weights memory memoryLow bytecodeLow share
  let pcFinal := Model.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : Array (Array FormW) := tablesW.map fun _ ↦ #[#[], #[], #[]]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (Model.gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout #[] #[1] 0 point
    (treeValues.getD 2 0)
  ⟨claims, bytecodePoint, point, forms3, #[total0, total1, total2]⟩

variable {env : Env} {inp : Input} {s : QState}

/-- `busOut` by sides. -/
theorem tl_busOut (layout : LayoutW) (weights : Array EW) (beta : EW) (point trees memory : Array EW)
    (mf bf share : EW) (bp : Array EW) :
    busOut layout weights beta point trees memory mf bf share bp =
      tlBus layout weights beta point trees memory mf bf share bp := rfl

/-- **Phase 3 after the transcript**: from the values read, at their parts of the scratch, the bus
at `busR` and its claims at `claimsR`. -/
theorem tail_spec {layout : LayoutW} {rate : Nat} {weights point trees memory bytecodePoint : Array EW}
    {beta mf bf share : EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hi : Inputs env inp s.mem) (hl : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hsa : SidesAt s.mem env.work layout)
    (hdw : NatAt s.mem (depthR.at env.work) point.size) (hps : point.size < 64)
    (hp : EWArr s.mem (pointR.at env.work) point)
    (hw : EWArr s.mem (wR.at env.work) weights) (hws : weights.size = 2 ^ busBits)
    (hb : EWAt s.mem (betaR.at env.work) beta)
    (ht : EWArr s.mem (treeR.at env.work) trees) (hts : trees.size = 3)
    (hm : EWArr s.mem (memR.at env.work) memory) (hms : memory.size = 2)
    (hmf : EWAt s.mem (memFinalR.at env.work) mf) (hbf : EWAt s.mem (bcFinalR.at env.work) bf)
    (hsh : EWAt s.mem (shareR.at env.work) share) :
    WP tailCode s (fun s' ↦
        BusAt s'.mem (busR.at env.work)
          (busOut layout weights beta point trees memory mf bf share bytecodePoint) ∧
        ClaimsAt s'.mem (claimsR.at env.work)
          (busOut layout weights beta point trees memory mf bf share bytecodePoint).claims ∧
        Wrote env rs3 s s')
      (fun _ ↦ False) := by
  have hT : TlIn env inp layout rate point weights trees memory beta mf bf share s :=
    ⟨hrdi, hwp, hi, hl, hsa, by rwa [Region.at, pc_depthR_off] at hdw,
      by rwa [Region.at, pc_pointR_off] at hp, by rwa [Region.at, wR_off] at hw,
      by rwa [Region.at, betaR_off] at hb, by rwa [Region.at, show treeR.off = 52832 by show scratchR.off + 162 = _; rw [scratchR_off]] at ht,
      by rwa [Region.at, memR_off] at hm, by rwa [tl_memFinalAt] at hmf,
      by rwa [tl_bcFinalAt] at hbf, by rwa [Region.at, shareR_off] at hsh⟩
  have hws' : weights.size = 16 := hws
  rw [tl_busOut]
  unfold tailCode imleAt ldWork sideCode
  refine tl_vals1 hT hps hws' hts hms fun s1 w1 v1 ↦ ?_
  refine tl_vals2 (hT.keep hps hws' hts hms w1) hps hws' hts hms v1 fun s2 w2 v2 ↦ ?_
  refine WP.mono (tl_rest (bp := bytecodePoint) (hT.keep hps hws' hts hms (w1.trans w2)) hps hws'
    hts hms v2) ?_ fun _ h ↦ h
  rintro s' ⟨hb', hc', w3⟩
  exact ⟨hb', hc', ((w1.trans w2).trans w3).widen tl_within⟩

end NativeVm.Code.P3
