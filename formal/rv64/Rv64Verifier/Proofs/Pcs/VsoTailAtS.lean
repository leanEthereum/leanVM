import Rv64Verifier.Proofs.Pcs.VsoTailAtK

/-!
# `verify_stacked_opening`'s level tail: slots read at the rows' end

The frame's doublewords as the head, the fold rounds' end, the opening, `lam`'s end or the Merkle
checks' end left them (`Merkled.kH`, `kT`, `kU`, `kW`, `kM`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

section
variable {s : MachineState} {x : LCtx} {h t u v w m t' k r : MachineState} {ℓ : ℕ}
  {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
  {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
  {rows : List E}

theorem Merkled.kU (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) {o : ℕ}
    (ho : zuFree o) :
    r.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
  (hm.yu hpre hsl hk hr).1 _ (Zu.slot hpre hr.heap ho)

theorem Merkled.kT (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) {o : ℕ}
    (ho : ztFree o) :
    r.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = t.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
  (hm.yt hpre hsl hk hr).1 _ (Zt.slot hpre hr.heap ho)

theorem Merkled.kH (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) {o : ℕ}
    (ho : zhFree o) :
    r.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = h.getMem (s.getReg .x2 - BitVec.ofNat 64 o) := by
  obtain ⟨Fh, mh⟩ := hm.yh hpre hsl hk hr
  refine Fh _ (Zh.slot hpre hr.heap ?_ ho)
  have hF := hm.op.fo.head.folds.vec.raw
  simp only [RawVecOk, Buf] at hF
  rcases hF.2 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by omega)

theorem Merkled.kM (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) {o : ℕ}
    (ho : zmFree o) :
    r.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = m.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
  (hm.ym hpre hsl hk hr).1 _ (Zm.slot hpre hr.heap ho)

theorem Merkled.kW (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) {o : ℕ}
    (ho : x1Free o) :
    r.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = w.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
  (hm.frW hpre hsl hk hr).1 _ (X1.slot hpre hr.heap ho)

end

end Rv64Verifier.Proofs.Pcs.Vso
