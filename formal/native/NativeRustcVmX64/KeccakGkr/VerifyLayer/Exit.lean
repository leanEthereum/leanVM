module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Mem
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Exec
public import NativeRustcVmX64.Field.W32

/-!
# `verify_layer` on x86-64: the exit

At `NativeRustcVmX64.Vm.VerifyLayer.label_50` (`b87`) with BL the verdict (`exit50`), at `NativeRustcVmX64.Vm.VerifyLayer.label_49` (`b86`, BL
cleared) on a rejected run (`exit49`): the epilogue restores the entry's registers and returns,
AL the verdict (`Goal`). The labels' addresses (`lbl`), a block of the code placed (`blk`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

@[expose] public section

/-- The layer's run. -/
abbrev runL (s : TState) (c : KeccakClaimW) (m0 : MachineData) :
    Option (KeccakClaimW × TState) :=
  (verifyKeccakLayer (reg m0 .rsi).toNat (reg m0 .rdx).toNat c).run s

/-- **The goal**: back at the caller with the postcondition. -/
def Goal [Labels] (a : DecArea) (s : TState) (c : KeccakClaimW) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ VerifyLayerPost a s c m0 st.data

/-- What a run's success leaves in memory. -/
def Done (a : DecArea) (m0 : MachineData) (r : Option (KeccakClaimW × TState)) (d : DataMem) :
    Prop :=
  ∀ c' s', r = some (c', s') → TStateAt d (tA m0) a s' ∧ ClaimAt d (cA m0) c' ∧
    WeightsAt d (lA m0) c'

end

public section

/-- An element of an infix. -/
theorem getElem?_of_infix {α : Type} {b l : List α} {o i : Nat} (h : b.IsInfixAt l o)
    (hi : i < b.length) : l[o + i]? = b[i]? := by
  obtain ⟨t, ht⟩ := h
  rw [show l[o + i]? = (l.drop o)[i]? by simp [List.getElem?_drop], ← ht,
    List.getElem?_append_left hi]

variable [Host] {k : Nat}

/-- A block of the code, placed. -/
theorem blk {b : List Directive} {o : Nat} (hp : Placed code k) (h : b.IsInfixAt code o)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + o) :=
  h.trans hp.1 hne

/-- A label of the code at the start of a block placed at `o`. -/
theorem lbl {b : List Directive} {o : Nat} {l : Label} (hp : Placed code k)
    (h : b.IsInfixAt code o) (hb : b[0]? = some (.label l)) :
    Labels.label l = Host.addrOf (k + o) :=
  hp.label (j := o) (by
    have hl : 0 < b.length := by
      cases b with
      | nil => cases hb
      | cons _ _ => simp
    have := getElem?_of_infix h hl
    rw [Nat.add_zero] at this
    rw [this, hb])

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The epilogue** at `NativeRustcVmX64.Vm.VerifyLayer.label_50`: BL's verdict returned in AL. -/
theorem exit50 (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {d : MachineData} (hb : Body m0 W 24 d)
    (hbx : (reg d .rbx).toNat % 256 = (okWord (runL s c m0).isSome).toNat)
    (hdone : Done a m0 (runL s c m0) d.dmem) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b87Offset)⟩ := by
  have g := geo_of hpre
  have hS := pre_stack hpre
  have hwf := wf0 hS hb (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial trivial
  refine exec_then (blk hp b87_in_code (by simp [b87])) e87 hwf nofun hm fun st hm' hpc ↦
    .done _ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hb.fr hwf hm' (by decide +kernel)
  have hdm : st.data.dmem = d.dmem := hm'.dmem_eq hwf rfl
  refine ⟨?_, hrsp, ?_, ?_, ?_, hsv⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact Frame.load_ret hb.fr hS (by decide)
  · show (reg st.data .rax).toNat % 256 = _
    rw [show reg st.data .rax = _ from hm'.regs .rax _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [Field.trunc32_toNat, Nat.mod_mod_of_dvd _ (by decide)]
    exact hbx
  · intro c' s' hr
    rw [hdm]
    exact hdone c' s' hr
  · intro q hq
    rw [hdm]
    refine hb.same q fun hc ↦ hq ?_
    rcases hc with hc | hc
    · exact ⟨_, List.mem_cons_self, by rw [stack_eq]; exact hc⟩
    · rcases hWo q hc with h | h | h
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)), h⟩

/-- **A rejected run** at `NativeRustcVmX64.Vm.VerifyLayer.label_49`: BL cleared, then the epilogue. -/
theorem exit49 (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {d : MachineData} (hb : Body m0 W 24 d)
    (hr : runL s c m0 = none) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b86Offset)⟩ := by
  have g := geo_of hpre
  have hS := pre_stack hpre
  have hwf := wf0 hS hb (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hb hwf (blk hp b86_in_code (by simp [b86])) e86 nofun hm (by decide +kernel)
    (hex0 (by decide +kernel)) fun st hm' hpc hb' _ ↦ ?_
  simp only [PcOk] at hpc
  obtain ⟨d', pc⟩ := st
  simp only at hpc hm' hb'
  subst hpc
  refine exit50 hp hpre hWo hb' ?_ (fun c' s' h ↦ by rw [hr] at h; cases h)
  rw [show reg d' .rbx = _ from hm'.regs .rbx _ rfl, hr]
  rfl

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
