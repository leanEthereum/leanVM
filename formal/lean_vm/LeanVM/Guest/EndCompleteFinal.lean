/-
  LeanVM.Guest.EndCompleteFinal

  Completeness within a budget at the deployed frame sizes, certificates, cells and headers
  (`B2C`), from what is still open.
-/

module

public import LeanVM.Guest.EndCompleteCounts
public import LeanVM.Guest.DeferredCaps
public import LeanVM.Guest.B2C.CalleesHyps
public import LeanVM.Guest.B2C.KTemps
public import LeanVM.Guest.B2C.ArmsFresh
public import LeanVM.Guest.B2C.CntWeight
public import LeanVM.Guest.B2C.Table
public import LeanVM.Guest.Count.Main

/-!
# Completeness at the deployed instance

`guest_complete_b2c`: `GuestCompleteWithin (b2cBudget Wt)`, `ea_guest_complete` at `B2C.fs`,
`B2C.cert`, `B2C.H`, `B2C.C` and the counts `B2C.cnt` (each instance's path count plus the jump
table's `jtSets`), the callees' hypotheses `calleesHyps_b2c`, `__loop86`'s bound `loop86_bound_le`,
`deferredCaps`, the instruction budget `eaInstrs` (`ea_hinstrs`), checker K's `cnt_le_weight_arm`
at `verify_lean_xmss`'s arms (`B1.Sig.xmssArmC_spec`), `cntRetemp` and certificate facts
(`b2c_kfactsAll`), and the jump table's cells (`tableC_node`). Still assumed, by name: `main`'s
weight hypotheses per opcode (`MainWeightHyps` at `ωArm B1.Sig.xmssArmC op`), checker K's `run`
(`B2cRun`), and the run reaching the end (`B2cB2`) within the counts (`B2cCount`).
`guest_complete_b2c'`: the same at k4's weights `Count.kcWt`, within `b2cBudget'`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Guest.End (GuestCompleteWithin KFactsAll CntRetemp Budget bytecode mainEntry)

@[expose] public section

/-- **Checker K's `run`**: each `frameAddr` buffer's words are among its instance's cells, off the
temporaries. -/
def B2cRun : Prop :=
  ∀ hdr (T : Tree), T.name = "main" →
    ∀ I ∈ honestInsts coreProgram fs H hdr T, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
      ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events coreProgram →
        ∀ (k : ℕ) (hk : k < (r :: rs).length), (cert f r + k, σ (r :: rs)[k]) ∈ C I ∧
          ∀ t ∈ coreProgram.temps f, cert f r + k ≠ cert f t

/-- **The certificate's facts**, from checker K's (`cellsOk_C`, `kfacts_cert_lt`,
`kfacts_cert_inj`, `kfacts_tmp`, `kfacts_keep_all`) and `run`. -/
theorem b2c_kfactsAll (hrun : B2cRun) : KFactsAll fs H C cert := fun hdr T hn =>
  { cells := cellsOk_C _
    cells' := fun _ => cellsOk_C _
    cert_lt := kfacts_cert_lt
    cert_inj := kfacts_cert_inj
    run := hrun hdr T hn
    tmp := kfacts_tmp hdr T
    keep := kfacts_keep_all hdr T }

/-- **Checker K's `b2`**: the honest memory runs from `main`'s entry to the end. -/
def B2cB2 : Prop :=
  ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] →
      Reach guest (honest coreProgram fs H C hdr T) ⟨gpow mainEntry, 1⟩ (Regs.final guest)

/-- **Checker K's `count`**: a run of the honest memory to the end is within the counts. -/
def B2cCount : Prop :=
  ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      run guest (honest coreProgram fs H C hdr T) n Regs.initial = some (Regs.final guest) →
        ∀ op, (⟨_, honest coreProgram fs H C hdr T, n⟩ : Trace guest).count op ≤ cnt T op

/-- `main`'s weight hypotheses at each opcode's path maxima, `verify_lean_xmss`'s arms counted separately. -/
abbrev B2cWeightHyps : Type := ∀ op, MainWeightHyps fs (ωArm B1.Sig.xmssArmC op)

/-- **The budget**: the words `eaWords` and the instruction counts `eaInstrs` at the deployed
callees, `__loop86`'s slope `482`. -/
noncomputable def b2cBudget (Wt : B2cWeightHyps) : Budget :=
  eaBudget fs cert calleesHyps_b2c 482 0 (eaInstrs calleesHyps_b2c 482 0 Wt jtSets)

/-- **Completeness within the budget at the deployed instance**, from `main`'s weight hypotheses,
checker K's `run` and the run's end within the counts. -/
theorem guest_complete_b2c (Wt : B2cWeightHyps) (hrun : B2cRun) (hb2 : B2cB2) (hcount : B2cCount) :
    GuestCompleteWithin (b2cBudget Wt) :=
  ea_guest_complete fs cert cnt calleesHyps_b2c _ H C (fun q => loop86_bound_le q) (two_le_fs _)
    deferredCaps (fun op f => ωArm B1.Sig.xmssArmC op f) Wt jtSets
    (cnt_le_weight_arm B1.Sig.xmssArmC B1.Sig.xmssArmC_spec)
    (ea_hinstrs calleesHyps_b2c (fun q => loop86_bound_le q) Wt jtSets)
    (b2c_kfactsAll hrun) cntRetemp (fun _ _ _ _ ht => tableC_node ht) hb2 hcount

/-- **The deployed budget**: `b2cBudget` at k4's weights `Count.kcWt`. -/
noncomputable def b2cBudget' : Budget := b2cBudget Count.kcWt

/-- **Completeness within the deployed budget**, from checker K's `run`, `b2` and `count`. -/
theorem guest_complete_b2c' (hrun : B2cRun) (hb2 : B2cB2) (hcount : B2cCount) :
    GuestCompleteWithin b2cBudget' :=
  guest_complete_b2c Count.kcWt hrun hb2 hcount

end
end LeanVM.Guest.B2C
