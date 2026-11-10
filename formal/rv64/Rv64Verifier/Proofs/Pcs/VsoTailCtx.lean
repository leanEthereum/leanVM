import Rv64Verifier.Proofs.Pcs.VsoTailCalls

/-!
# `verify_stacked_opening`'s level tail: what the level wrote since its opening

From the opening `u` to `lam`'s end `w` (`X0`) and from `w` to the rows' end `r` (`X1`): two
coarse frames, so that a slot or a buffer outside them is read at `r` as the opening or `lam` left
it.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- From the opening to `lam`'s end. -/
def X0 (s u w : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10 + 8) 352 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a (s.getReg .x2 - 968) 16 ∨ Within a (s.getReg .x2 - 832) 16 ∨
    Within a (s.getReg .x2 - 488) 24 ∨ Within a (s.getReg .x2 - 464) 24 ∨
    Within a (s.getReg .x2 - 384) 32 ∨ Within a nextAddr 8 ∨ Fresh u w a

/-- From `lam`'s end to the rows' end. -/
def X1 (s w r : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10 + 352) 8 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a (s.getReg .x2 - 1008) 40 ∨ Within a (s.getReg .x2 - 904) 8 ∨
    Within a (s.getReg .x2 - 832) 8 ∨ Within a (s.getReg .x2 - 784) 8 ∨
    Within a (s.getReg .x2 - 536) 24 ∨ Within a (s.getReg .x2 - 464) 32 ∨
    Within a (s.getReg .x2 - 384) 64 ∨ Within a (s.getReg .x2 - 160) 32 ∨
    Within a nextAddr 8 ∨ Fresh w r a

theorem Merkled.frU {s : MachineState} {x : LCtx} {h t u v w m : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs) :
    DFrame u w (X0 s u w) ∧ heapNext u ≤ heapNext w := by
  have hb := bounds hpre
  obtain ⟨T0, hl⟩ := hm.lo
  have m2 := hm.qo.mono
  have m3 := hl.mono
  have hhv := (hm.qo.inv.heap hpre.heap).hi
  refine ⟨(hm.qo.fr.mono fun a ha ↦ ?_).trans (hl.fr.mono fun a ha ↦ ?_) fun _ h ↦ h, by omega⟩
  · rcases ha with (ha | ha | ha | ha) | (ha | ha | ha | ha | ha | ha | ha)
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))))
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha.1, by omega⟩)))))))
  · rcases ha with ha | ha | ha | ha | ha | ha | ha
    · exact Or.inl (by addr_omega [ha])
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩)))))))

/-- From `lam`'s end through the Merkle checks, the slices, `eq_kernel` and the rows. -/
theorem Merkled.frW {s : MachineState} {x : LCtx} {h t u v w m t' k r : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    {rows : List E} (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) (hr : Rowed s k r rows) :
    DFrame w r (X1 s w r) ∧ heapNext w ≤ heapNext r := by
  have hb := bounds hpre
  have m1 := hm.mo.mono
  have m2 := hsl.mono
  have m3 := hk.mono
  have m4 := hr.mono
  have hm' : heapNext t' ≤ heapNext k := m3
  refine ⟨(((hm.mo.fr.mono fun a ha ↦ ?_).trans (hsl.fr.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
    (hk.fr.mono fun a ha ↦ ?_) fun _ h ↦ h).trans (hr.fr.mono fun a ha ↦ ?_) fun _ h ↦ h,
    by omega⟩
  · rcases ha with (ha | ha | ha) | ((ha | ha | ha | ha) | ha | ha | ha)
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ha)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ha))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨ha.1, by omega⟩))))))))))
  · rcases ha with ha | ha | ha | ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by addr_omega [ha, hb])))))))))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ha))))))))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨by omega, by omega⟩))))))))))
  · rcases ha with ha | ha | ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ha))))))))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨by omega, by omega⟩))))))))))
  · rcases ha with ha | ha | ha | ha | ha | ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by addr_omega [ha, hb]))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by addr_omega [ha, hb])))))))))
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ha))))))))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨by omega, by omega⟩))))))))))

/-- **At the rows' end `r`**, what the level's tail reads, from the level's head `h`, the fold
rounds' end `t`, the opening `u` and `lam`'s end `w`. -/
structure AtR (s : MachineState) (x : LCtx) (h t u w r : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q res : List E)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (d : Digest) (qs : List Word) : Prop where
  head : Head s x h ℓ Wl
  fo : Folded s x h t ℓ Wl lf q
  pc : r.pc = 0x8000b42c
  sp : r.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s r (r.getMem nextAddr)
  heap : HeapOk r
  /-- The heap's marks: `h`, `t`, `u`, `w`, `r` in order. -/
  ht : heapNext h ≤ heapNext t
  tu : heapNext t ≤ heapNext u
  uw : heapNext u ≤ heapNext w
  wr : heapNext w ≤ heapNext r
  /-- `dot`'s operands. -/
  rows : HS s r (r.getReg .x25) (24 * (r.getReg .x27).toNat)
  pw : VecOk r (s.getReg .x2 - 488) 24 8 ∧
    vecEs r (s.getReg .x2 - 488) = Verifier.powers (eAt w (s.getReg .x2 - 384)) qs.length ∧
    vecLen r (s.getReg .x2 - 488) = BitVec.ofNat 64 qs.length ∧
    ((vecLen r (s.getReg .x2 - 488)).toNat = 0 ∨
      heapNext u ≤ (vecPtr r (s.getReg .x2 - 488)).toNat ∧
      (vecPtr r (s.getReg .x2 - 488)).toNat + (vecCap r (s.getReg .x2 - 488)).toNat * 24 ≤
        heapNext w)
  m816 : r.getMem (s.getReg .x2 - 816) = s.getReg .x10
  /-- The pending claims, as the opening left them. -/
  pnd : PendOk r t (s.getReg .x2 - 616) pend
  pu : ∀ y, PBufs r (s.getReg .x2 - 616) y → y.toNat < heapNext u
  /-- The queries' `Vec`: its capacity at `S - 1000`, buffer at `S - 824`, count in `x26`. -/
  m1000 : r.getMem (s.getReg .x2 - 1000) = BitVec.ofNat 64 qs.length
  qbuf : r.readWords (r.getMem (s.getReg .x2 - 824)) qs.length = qs ∧
    (r.getMem (s.getReg .x2 - 824)).toNat % 8 = 0 ∧ (qs.length = 0 ∨
      heapNext u ≤ (r.getMem (s.getReg .x2 - 824)).toNat ∧
      (r.getMem (s.getReg .x2 - 824)).toNat + 8 * qs.length ≤ heapNext w)
  x26 : r.getReg .x26 = BitVec.ofNat 64 qs.length
  m872 : r.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 (mlOf s Wl lf)
  /-- `lam`'s limbs at `S - 976`, `S - 984`, `S - 992`. -/
  lam : (r.getMem (s.getReg .x2 - 976), r.getMem (s.getReg .x2 - 984),
    r.getMem (s.getReg .x2 - 992)) = Model.limbs (eAt w (s.getReg .x2 - 384))
  /-- The running quadratic, the fold rounds' `q`. -/
  quad : r.getMem (s.getReg .x2 - 896) = t.getReg .x22 ∧ r.getReg .x23 = t.getReg .x23 ∧
    r.getMem (s.getReg .x2 - 808) = t.getReg .x23 ∧ eListAt r (t.getReg .x22) (t.getReg .x23).toNat = q
  /-- The folds, `Wl.folds ++ lf`. -/
  folds : VecOk r (s.getReg .x2 - 688) 24 8 ∧ vecEs r (s.getReg .x2 - 688) = Wl.folds ++ lf ∧
    vecPtr r (s.getReg .x2 - 688) = vecPtr t (s.getReg .x2 - 688) ∧
    vecCap r (s.getReg .x2 - 688) = vecCap t (s.getReg .x2 - 688)
  /-- What the level wrote from its head on, all but the glued claims' header at `S - 664`. -/
  gfr : DFrame h r fun a ↦ Within a (s.getReg .x2 - 2464) 1800 ∨ Within a (s.getReg .x2 - 640) 640 ∨
    Within a (s.getReg .x10 + 8) 352 ∨ Within a nextAddr 8 ∨
    (heapNext h ≤ a.toNat ∧ a.toNat < heapNext r) ∨
    Within a (vecPtr h (s.getReg .x2 - 688)) ((vecCap h (s.getReg .x2 - 688)).toNat * 24)
  /-- The head's slots. -/
  m152 : r.getMem (s.getReg .x2 - 888) = BitVec.ofNat 64 (K0 s + 1)
  m160 : r.getMem (s.getReg .x2 - 880) = 0xffffffffaaaaaaab
  m176 : r.getMem (s.getReg .x2 - 864) = x.RP
  m184 : r.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ
  m32 : r.getMem (s.getReg .x2 - 1008) = BitVec.ofNat 64 ℓ + 1
  m248 : r.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8
  m128 : r.getMem (s.getReg .x2 - 912) = s.getReg .x12
  m200 : r.getMem (s.getReg .x2 - 840) = s.getReg .x11
  m112 : r.getMem (s.getReg .x2 - 928) = BitVec.ofNat 64 (Wl.folds ++ lf).length
  /-- The residual (the final level's), spilled at `S - 968`, `S - 960`. -/
  rsd : eListAt r (r.getMem (s.getReg .x2 - 968)) (r.getMem (s.getReg .x2 - 960)).toNat = res ∧
    (r.getMem (s.getReg .x2 - 968)).toNat % 8 = 0 ∧
    ((r.getMem (s.getReg .x2 - 960)).toNat = 0 ∨
      heapNext t ≤ (r.getMem (s.getReg .x2 - 968)).toNat ∧
      (r.getMem (s.getReg .x2 - 968)).toNat + 24 * (r.getMem (s.getReg .x2 - 960)).toNat ≤
        heapNext u)
  rsdp : (r.getMem (s.getReg .x2 - 960)).toNat = 0 ∨ vecCap r (s.getReg .x2 - 616) = 0
  root : NR r (s.getReg .x2) d
  last : ℓ = K0 s + 1 → d = digestAt r (s.getReg .x11)
  rlen : ℓ = K0 s + 1 → res.length = 2 ^ (((s.getReg .x12).toNat - (Wl.folds ++ lf).length) % 64)
  x9 : r.getReg .x9 = x.FP
  /-- What the level wrote since the configured state, `LM`. -/
  fr : DFrame x.c r (LM s x.L (r.getMem nextAddr))
  /-- The mirror, after the Merkle checks. -/
  value : RunsK s r ℓ 1 (Model.Pcs.afterWords (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ
    (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf res pend (eAt w (s.getReg .x2 - 384)) qs
    (wordsAt s w)) (nextRoots s ℓ d)

end Rv64Verifier.Proofs.Pcs.Vso
