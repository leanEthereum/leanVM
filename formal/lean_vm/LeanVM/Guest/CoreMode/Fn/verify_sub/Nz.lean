/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Nz

  `verify_sub`'s divisors the frame walk leaves as residuals (`Own.verify_sub.nzs`), nonzero at its honest instances:
  the link's cycle count `g^cycles` (value `240`, `ShapeOk.gCyc`) and the vanishing count `g^(88 + n + w + d)` (value
  `652`, whose multiple `648 = g_p^8` is a power of `g`).
-/

module

public import LeanVM.Guest.EndExecResNz
public import LeanVM.Guest.CoreMode.Fn.verify_sub.StreamRun
public import LeanVM.Guest.CoreMode.Fn.verify_sub.ChalA

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

public section

variable {al : String → Bool} {D : Ref → RefD}

/-- **The link's cycle count** (value `240`) is nonzero at every honest instance of `verify_sub`. -/
theorem nzValA_vs240 : NzValA al D name% «verify_sub» (.n 240) := by
  intro r hR hr I hI σ bufs kids ht
  obtain ⟨rets, R⟩ := vsRun_honest hR hr hI ht
  rw [R.shapeOk.gCyc]
  exact Value.gen_pow_ne_zero _

/-- **The vanishing count** (value `652`) is nonzero at every honest instance of `verify_sub`: `648 = 653·652` and
`648 = g_p^8` a power of `g`. -/
theorem nzValA_vs652 : NzValA al D name% «verify_sub» (.n 652) := by
  intro r hR hr I hI σ bufs kids ht
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hV := vs_slice hpre B1.VerifySub.vsLkVanishT_eq
  simp only [B1.VerifySub.vsLkVanishT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hV
  obtain ⟨-, v538, v539, v540, -, -, -, -, v545, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hsq, -⟩ := hV
  have M := B1.Link.squeeze_packed_sound _ _ _ (Res.KidRel.rel hsq)
  simp only [B1.Link.MeaningSP] at M
  obtain ⟨p, -, hcg, -⟩ := M
  have h648 : σ (.n 648) = gen ^ (8 * p) := by
    rw [v540, v539, v538]
    exact B1.VerifySub.pow8 _ p hcg
  intro h0
  rw [v545, h0, mul_zero] at h648
  exact Value.gen_pow_ne_zero _ h648.symm

end

end LeanVM.Guest.EndExec
