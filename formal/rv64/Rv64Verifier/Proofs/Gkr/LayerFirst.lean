import Rv64Verifier.Proofs.Gkr.Layer
import Rv64Verifier.Proofs.Gkr.LayerR8c
import Rv64Verifier.Proofs.Gkr.LayerR10e

/-!
# `keccak::verify_layer`: from the entry to the second check

`FirstHalf` from its regions: the product's coefficients (`to_scalars`), the projection
(`to_proj`, `proj`), the segments' iota (`to_iota`, `iota_loop`), the first check (`check`), the
powers, the instance weights, the pack rounds' start and rounds (`powers`, `weights`,
`pack_start`, `pack`), and from there to the second check (`second_check`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr

theorem first_half (hNS : NextScalarsSpec) (hM : MulSpec) (hEK : EqKernelSpec)
    (hSum : FieldContracts.SumSpec) (hD : DuplexSpec) (hA : AllocSpec)
    (hR : ReserveFreshSpec 0x80008a10 24 8) (hPE : MultilinearContracts.PolyEvalSpec)
    (hT : TryAllocZeroedSpec) (hRP : RoundPolySpec) (hG : GrowOneFreshSpec 0x80011c78 24 8)
    (hSC : SumcheckSpec) (hDt : MultilinearContracts.DotSpec) : FirstHalf := by
  intro s hpc hpre
  obtain ⟨u, hr, N | hd⟩ := to_scalars hNS hpre hpc
  swap
  · exact ⟨u, hr, Or.inr (Or.inr hd)⟩
  by_cases herr : vecCap u (s.getReg .x2 - 752) = errNiche
  · obtain ⟨t, hr', pc, pres, post⟩ := scalars_err hpre N herr
    exact ⟨t, hr.trans hr', Or.inr (Or.inl ⟨pc, pres, post⟩)⟩
  obtain ⟨o, hr₁, Z⟩ := to_proj hpre N herr
  have r1 := hr.trans hr₁
  obtain ⟨v, hr₂, J | hd⟩ := proj hM hpre Z
  swap
  · exact ⟨v, r1.trans hr₂, Or.inr (Or.inr hd)⟩
  have r2 := r1.trans hr₂
  obtain ⟨o', sg, hr₃, I | hd⟩ := to_iota hEK hpre J
  swap
  · exact ⟨o', r2.trans hr₃, Or.inr (Or.inr hd)⟩
  have r3 := r2.trans hr₃
  obtain ⟨w, hr₄, ⟨X, hpcX⟩ | hd⟩ := iota_loop hM hpre I.ok 2 0 o' rfl I.q I.pc
  swap
  · exact ⟨w, r3.trans hr₄, Or.inr (Or.inr hd)⟩
  have r4 := r3.trans hr₄
  obtain ⟨t₃, hr₅, J₃ | hret | hd⟩ := check hM hSum hpre I X hpcX
  rotate_left
  · exact ⟨t₃, r4.trans hr₅, Or.inr (Or.inl hret)⟩
  · exact ⟨t₃, r4.trans hr₅, Or.inr (Or.inr hd)⟩
  have r5 := r4.trans hr₅
  obtain ⟨t₅, c, hr₆, J₅ | hd⟩ := powers hD hM hpre J₃
  swap
  · exact ⟨t₅, r5.trans hr₆, Or.inr (Or.inr hd)⟩
  have r6 := r5.trans hr₆
  obtain ⟨t₆, ip, hr₇, J₆ | hd⟩ := weights hA hR hpre J₅
  swap
  · exact ⟨t₆, r6.trans hr₇, Or.inr (Or.inr hd)⟩
  have r7 := r6.trans hr₇
  obtain ⟨t₇, hr₈, J₇ | hd⟩ := pack_start hSum hPE hT hpre J₆
  swap
  · exact ⟨t₇, r7.trans hr₈, Or.inr (Or.inr hd)⟩
  have r8 := r7.trans hr₈
  obtain ⟨t₈, acc, hr₉, J₈ | hret | hd⟩ := pack hRP hD hPE hM hG hpre J₇
  rotate_left
  · exact ⟨t₈, r8.trans hr₉, Or.inr (Or.inl hret)⟩
  · exact ⟨t₈, r8.trans hr₉, Or.inr (Or.inr hd)⟩
  obtain ⟨u', hr₁₀, h⟩ := second_check hSC hNS hEK hDt hM hpre J₈
  exact ⟨u', r8.trans (hr₉.trans hr₁₀), h⟩

end Rv64Verifier.Gkr.Layer
