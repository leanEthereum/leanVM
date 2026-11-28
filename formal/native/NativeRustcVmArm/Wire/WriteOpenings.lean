module

public import NativeRustcVmArm.Code.Vm.Find.Names
public import NativeRustcVmArm.Code.Vm.WriteOpenings.Names
public import NativeRustcVmArm.Wire.WriteOpenings.Start

/-!
# `write_openings` meets its contract

`writeOpenings_spec`, `find`'s contract a hypothesis: the places from the precondition
(`geo_of`), then the run from the entry (`entry_spec`): the prologue, the queries' loop with
levels (`query_loop`), or without, with a leaf (`queryB_loop`) or none (`queryZ_loop`), the
epilogue (`end_spec`) or a rejection (`fail_spec`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (base)
open NativeRustcVm (WordAt)
open NativeRustcVmArm.Vm.WriteOpenings

public section

/-- **The places** from the precondition. -/
theorem geo_of {m0 : MachineData} {k : Nat} (h : WriteOpeningsPre m0) {cnt out : BitVec 64}
    (hc : WordAt m0.dmem m0.regs.SP.toBitVec (UInt64.ofBitVec cnt))
    (ho : WordAt m0.dmem (m0.regs.SP.toBitVec + 8#64) (UInt64.ofBitVec out)) :
    Geo ⟨m0, k, cnt, out⟩ := by
  obtain ⟨hst, h1, h3, h5, h6, hnq0, hnp0, cnt', out', hc', ho', hok, hd⟩ := h
  have ec : cnt' = cnt := congrArg UInt64.toBitVec (NativeRustcVm.WordAt.unique hc' hc)
  have eo : out' = out := congrArg UInt64.toBitVec (NativeRustcVm.WordAt.unique ho' ho)
  subst ec eo
  have hst' : StackOk m0 176 := hst
  have hN := hst'.2.1
  have hal := hst'.1
  have hlt := m0.regs.SP.toNat_lt
  refine ⟨hst', fun i hi ↦ ?_, hd, hnq0, h1, hnp0, h3, h5, h6, hc, ho⟩
  match i, hi with
  | 0, _ => exact ⟨Ring.frame_mapped hst' (le_refl _), Ring.base_noWrap hN⟩
  | 1, _ =>
    refine ⟨fun t ht ↦ ?_, ?_⟩
    · by_cases h8 : t < 8
      · exact hc.mapped t h8
      · have := ho.mapped (t - 8) (by show t - 8 < 8; have : t < 16 := ht; omega)
        rwa [NativeRustcVm.addr_add_add, show 8 + (t - 8) = t by omega] at this
    · show m0.regs.SP.toBitVec.toNat + 16 ≤ 2 ^ 64
      rw [UInt64.toNat_toBitVec]
      omega
  | 2, _ => exact hok _ (.head _)
  | 3, _ => exact hok _ (.tail _ (.head _))
  | 4, _ => exact hok _ (.tail _ (.tail _ (.head _)))
  | 5, _ => exact hok _ (.tail _ (.tail _ (.tail _ (.head _))))
  | 6, _ => exact hok _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  | 7, _ => exact hok _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  | n + 8, h => exact absurd h (by omega)

variable [Host] {k : Nat}

/-- **`write_openings` meets its contract**, given `find`'s. -/
theorem writeOpenings_spec (hp : Placed code k)
    (hfind : Spec (Labels.label NativeRustcVmArm.Vm.Find.entryLabel) FindPre FindPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost := by
  intro m0 hpre
  obtain ⟨-, -, -, -, -, -, -, cnt, out, hc, ho, -, -⟩ := id hpre
  rw [hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.entryOffset) NativeRustcVmArm.Vm.WriteOpenings.entry_at]
  exact entry_spec (R := ⟨m0, k, cnt, out⟩) hp (geo_of hpre hc ho) hfind

end

end NativeRustcVmArm.Wire.WriteOpenings
