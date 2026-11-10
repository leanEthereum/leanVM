import Rv64Verifier.Proofs.Bus.TsRowsStage
import Rv64Verifier.Proofs.Bus.TsTerminalStage

/-!
# `table_sumcheck`, the stages composed

`table_sumcheck_of`: the prologue (`stageP`), `vec![None; n_rounds]` (`stageA`), `sumcheck`
(`stageB`), `point` (`stageC`), the weights (`stageD`), then the rows and the terminal, taken as
hypotheses of the shapes `stageE` and `stageF` prove; `table_sumcheck_spec` from the callees'
contracts.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.MultilinearContracts
  Rv64Verifier.Contracts

/-- The rows loop, as `stageE` proves it. -/
def RowsStage : Prop :=
  ∀ {s u : MachineState} {ch : List E} {cl : E} {P W : Word}, TableSumcheckPre s →
    AtRows s u ch cl P W → u.pc = 0x80008384 → ∃ t, Reaches Image.code u t ∧
      ((∃ rows, t.pc = 0x80008520 ∧ AtTerminal s t ch cl P W rows) ∨ Done s t)

/-- The terminal, as `stageF` proves it. -/
def TerminalStage : Prop :=
  ∀ {s u : MachineState} {ch : List E} {cl : E} {P W : Word} {rows : List (List E × List E)},
    TableSumcheckPre s → AtTerminal s u ch cl P W rows → u.pc = 0x80008520 →
      ∃ t, Reaches Image.code u t ∧ Done s t

theorem table_sumcheck_of (hOF : OptFromElemBelowSpec) (hS : SumcheckSpec)
    (hTA : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8) (hFE : FromElemSpec)
    (hMul : MulSpec) (hE : RowsStage) (hF : TerminalStage) : TableSumcheckSpec := by
  intro s hpc hpre
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  obtain ⟨u, hru, I, hpcu, R, A, h12, hfu⟩ := stageP hpc hpre
  obtain ⟨v, hrv, ⟨Iv, hpcv, hcs, hLv, -, hlen, hel, hnb, hbelow, hAv⟩ | hd⟩ :=
    stageA hOF hpre I hpcu h12
  swap
  · exact ⟨v, hru.trans hrv, Or.inr hd⟩
  have hm := I.mono
  have tg := hpre.target
  have tf := hpre.targetFree
  have tst := hpre.targetStack
  have hhi := Iv.heap.hi
  simp only [stack_eq, Outside, heapEnd] at tst tf hhi
  have hAt : AtSumcheck s v := {
    inv := Iv
    regs := R.call hcs
    args := hAv A
    len := hlen
    buf := by simp only [NewBuf] at hnb ⊢; omega
    elems := hel
    below := hbelow
    target := by
      rw [hLv.eAt fun i hi hw ↦ by
          rcases hw with hw | hw | hw
          · addr_omega [hw, hi, tst, tg, hb1]
          · addr_omega [hw, hi, tf, tg]
          · simp only [Fresh] at hw; addr_omega [hw, hi, tf, tg, hm, hhi],
        hfu.eAt fun i hi hw ↦ by addr_omega [hw, hi, tst, tg, hb1]]
    tr := fun T hT ↦ I.transcript hpre Iv.heap hLv
      (transcript_of_stack hpre hfu (by addr_omega [hb1]) (by addr_omega [hb1]) hT) }
  obtain ⟨w, hrw, ⟨ch, cl, hpcw, hw⟩ | hdone⟩ := stageB hS hpre hAt hpcv
  swap
  · exact ⟨w, hru.trans (hrv.trans hrw), hdone⟩
  obtain ⟨x, hrx, ⟨P, hpcx, hx⟩ | hd⟩ := stageC hTA hR hpre hw hpcw
  swap
  · exact ⟨x, hru.trans (hrv.trans (hrw.trans hrx)), Or.inr hd⟩
  obtain ⟨y, hry, ⟨W, hpcy, hy⟩ | hd⟩ := stageD hFE hMul hpre hx hpcx
  swap
  · exact ⟨y, hru.trans (hrv.trans (hrw.trans (hrx.trans hry))), Or.inr hd⟩
  obtain ⟨z, hrz, ⟨rows, hpcz, hz⟩ | hdone⟩ := hE hpre hy hpcy
  swap
  · exact ⟨z, hru.trans (hrv.trans (hrw.trans (hrx.trans (hry.trans hrz)))), hdone⟩
  obtain ⟨t, hrt, hdone⟩ := hF hpre hz hpcz
  exact ⟨t, hru.trans (hrv.trans (hrw.trans (hrx.trans (hry.trans (hrz.trans hrt))))), hdone⟩

/-- `table_sumcheck`'s contract from its callees'. `FormEvaluateSpecE` is `FormEvaluateSpec` with
empty slices allowed anywhere; `OptFromElemBelowSpec` adds that the buffer lies below `NEXT`. -/
theorem table_sumcheck_spec (hOF : OptFromElemBelowSpec) (hS : SumcheckSpec)
    (hTA : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8) (hFE : FromElemSpec)
    (hMul : MulSpec) (hMC : MemcpySpec 0x800126e4) (hNS : NextScalarsSpec) (hA : AllocSpec)
    (hDot : DotSpec) (hFEv : FormEvaluateSpecE) : TableSumcheckSpec :=
  table_sumcheck_of hOF hS hTA hR hFE hMul (fun hpre h hpc ↦ stageE hTA hMC hNS hpre h hpc)
    (fun hpre h hpc ↦ stageF hMul hDot hA hTA hR hFEv hpre h hpc)

end Rv64Verifier.Proofs.Bus.TableSumcheck
