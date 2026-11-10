import Rv64Verifier.Proofs.Pcs.VsoGlueStep

/-!
# `verify_stacked_opening`'s final level: the glued claims' loop

From `TB` with claims to glue: `0x8000bab0` and `0x8000bab8` set the claims' end at `S - 880`
and the first claim in `s0`; each claim (`claimOne`, `claimAdd`) adds its scaled value to the
weight; past the last, `0x8000bfe0` goes on to the terminal check (`tExit`, `TC`). `gluedSpec`
is `GluedSpec` from the callees' contracts and the queries weight's pieces.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- One claim, to its value at `0x8000baf8`. -/
theorem claimOne (hEq : FunSpec Image.code 0x8000da88 Proofs.EqEval.Pre Proofs.EqEval.Post)
    (hRS : RootsSpec) (hIS : InvsSpec) (hPS : ProdsSpec)
    {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v w : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 : E} {j : ℕ}
    {acc : E} (hpre : VsoPre s) (h : GLI OA s x u v w Wl residual tf rt w0 j acc) :
    ∃ w', Reaches Image.code w w' ∧
      (FailR s w' ∨ ∃ val, GV OA s x u v w' Wl residual tf rt w0 j (gAddr u s j) acc val) := by
  obtain ⟨w₁, r₁, hd | hh⟩ := claimHead hpre h
  · exact ⟨w₁, r₁, Or.inl (Or.inl hd)⟩
  by_cases ht : u.getMem (gAddr u s j) = 0xffffffffffffffff
  · obtain ⟨w₂, r₂, hd | hv⟩ := claimOod hEq hpre hh ht
    · exact ⟨w₂, r₁.trans r₂, Or.inl (Or.inl hd)⟩
    · exact ⟨w₂, r₁.trans r₂, Or.inr hv⟩
  · obtain ⟨w₂, r₂, hv⟩ := claimQueries hRS hIS hPS hpre hh ht
    exact ⟨w₂, r₁.trans r₂, hv⟩

/-- **Past the last claim**: `0x8000bfe0` to the terminal check. -/
theorem tExit {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v w : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 wf : E}
    (hpre : VsoPre s) (h : TB OA s x u v Wl residual tf rt w0) (G : GS s v w)
    (hpc : w.pc = 0x8000bfe0) (hf : gluedFold Wl.glued (Wl.folds ++ tf) w0 = some wf)
    (hw : eAt w (s.getReg .x2 - 184) = wf) :
    ∃ w', Reaches Image.code w w' ∧ TC OA s w' (mlF s Wl) residual tf wf rt := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := G.sp
  have hfin := h.toTI.fin
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bfe0_spec hpc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000bfe0_keeps h₁
  have hm₁ := b8000bfe0_mem_same h₁
  have G₁ := G.same hpre hm₁ (k₁ .x2 (by decide))
  have T₁ := GS.ti hpre h G₁
  have hml := logN_le hfin.cfg
  obtain ⟨hTv, hTe, hTn⟩ := h.tail
  have hTl := TailV.len h.tail
  rw [h.tfl] at hTl
  have hTc := hTv.len
  have hT8 := hTv.raw.1
  have hres := hfin.res
  have hsu := hfin.su
  have hvm := h.mono
  have hvw := G₁.mono
  have hhw := G₁.heap.hi
  simp only [heapEnd] at hhw
  have ks (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 888).toNat ∨ (s.getReg .x2 - 864).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 856).toNat ∨ (s.getReg .x2 - 352).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 256).toNat) : t₁.getMem y = v.getMem y := by
    rcases hy with hy | hy | hy
    · exact G₁.keepStk hpre (Or.inl hy)
    · exact G₁.keepStk hpre (Or.inr (Or.inl hy))
    · exact G₁.keepStk hpre (Or.inr (Or.inr (Or.inr (Or.inl hy))))
  have x8₁ : t₁.getReg .x8 = vecPtr v (s.getReg .x2 - 304) := by
    rw [b8000bfe0_x8 h₁, hsp, show s.getReg .x2 - BitVec.ofNat 64 1040 + 744 = s.getReg .x2 - 304 + 8
      by addr_omega [hb], ← hm₁]
    exact ks _ (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩))
  have x19₁ : t₁.getReg .x19 = vecLen v (s.getReg .x2 - 304) := by
    rw [b8000bfe0_x19 h₁, hsp, show s.getReg .x2 - BitVec.ofNat 64 1040 + 752 = s.getReg .x2 - 304 + 16
      by addr_omega [hb], ← hm₁]
    exact ks _ (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩))
  have hrb : (u.getMem (s.getReg .x2 - 960)).toNat = 0 ∨
      heapNext s ≤ (u.getMem (s.getReg .x2 - 968)).toNat ∧
      (u.getMem (s.getReg .x2 - 968)).toNat + 24 * (u.getMem (s.getReg .x2 - 960)).toNat ≤
        heapNext u := by
    rcases hres.2.2 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨by have := hfin.hs; omega, h0.2⟩
  have k968 : t₁.getMem (s.getReg .x2 - 968) = u.getMem (s.getReg .x2 - 968) :=
    T₁.keepStk hpre (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)
  have k960 : t₁.getMem (s.getReg .x2 - 960) = u.getMem (s.getReg .x2 - 960) :=
    T₁.keepStk hpre (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)
  refine ⟨t₁, r₁, {
    inv := G₁.inv
    heap := G₁.heap
    pc := b8000bfe0_pc h₁
    ml64 := by simp only [mlF]; omega
    x19 := by
      rw [x19₁]
      apply BitVec.eq_of_toNat_eq
      rw [hTl, BitVec.toNat_ofNat]; simp only [mlF]; omega
    tail := by
      rw [x8₁]
      have hl : (vecLen v (s.getReg .x2 - 304)).toNat = mlF s Wl := hTl
      refine ⟨?_, hT8, ?_⟩
      · rw [← hTe, vecEs, hl]
        exact G₁.eListLow hpre (by
          rcases hTn.2 with h0 | h0
          · left; omega
          · right; exact ⟨by omega, by omega⟩)
      · rcases hTn.2 with h0 | h0
        · left; omega
        · right; exact ⟨by omega, by omega⟩
    res := by
      rw [k968, k960, T₁.eList hpre hrb]
      refine ⟨hres.1, hres.2.1, ?_⟩
      rcases hrb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by omega⟩
    rlen := hfin.rlen
    wt := by
      rw [← hw]; simp only [eAt, hm₁]
    trg := by
      rw [ks _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        ks _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
        ks _ (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))]
      exact h.trg
    value := by
      have hv := h.value
      rw [afterTail_basis s _ _ _ _ _ _ h.six h.basis, hf,
        show Model.TM.ofOption (some wf) = (pure wf : Model.TM E) from rfl, pure_bind] at hv
      exact hv.keep hpre (h.toTI.inv hpre) G₁.fr fun a ha ↦
        GLW.ns hpre (Nat.le_trans hfin.su h.mono) G₁.heap.hi ha }⟩

/-- The loop from claim `j` on, `k` claims left. -/
theorem gLoop (hEq : FunSpec Image.code 0x8000da88 Proofs.EqEval.Pre Proofs.EqEval.Post)
    (hRS : RootsSpec) (hIS : InvsSpec) (hPS : ProdsSpec) (hM : MulSpec)
    {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 : E}
    (hpre : VsoPre s) (k : ℕ) :
    ∀ j acc w, (vecLen u (s.getReg .x2 - 664)).toNat - j = k →
      GLI OA s x u v w Wl residual tf rt w0 j acc →
      ∃ w', Reaches Image.code w w' ∧ (FailR s w' ∨ ∃ wf, TC OA s w' (mlF s Wl) residual tf wf rt) := by
  induction k with
  | zero => intro j acc w hk hg; exact absurd hg.jlt (by omega)
  | succ k ih =>
    intro j acc w hk hg
    obtain ⟨w₁, r₁, hf | ⟨val, hv⟩⟩ := claimOne hEq hRS hIS hPS hpre hg
    · exact ⟨w₁, r₁, Or.inl hf⟩
    obtain ⟨w₂, r₂, hd | ⟨acc', hfo, hwt, G₂, h880, hnx⟩⟩ := claimAdd hM hpre hv
    · exact ⟨w₂, r₁.trans r₂, Or.inl (Or.inl hd)⟩
    rcases hnx with ⟨hlt, hpc, hx8⟩ | ⟨heq, hpc⟩
    · obtain ⟨w₃, r₃, hw₃⟩ := ih (j + 1) acc' w₂ (by omega)
        ⟨hg.tb, G₂, hpc, hlt, hx8, h880, hfo, hwt⟩
      exact ⟨w₃, r₁.trans (r₂.trans r₃), hw₃⟩
    · have hall : Wl.glued.take (j + 1) = Wl.glued := by
        rw [heq, ← hg.tb.toTI.fin.glen]; exact List.take_length
      rw [hall] at hfo
      obtain ⟨w₃, r₃, hc⟩ := tExit hpre hg.tb G₂ hpc hfo hwt
      exact ⟨w₃, r₁.trans (r₂.trans r₃), Or.inr ⟨_, hc⟩⟩

/-- **The glued claims' loop**, from `0x8000bab0` with claims to glue to the terminal check. -/
theorem gluedSpec (hEq : FunSpec Image.code 0x8000da88 Proofs.EqEval.Pre Proofs.EqEval.Post)
    (hRS : RootsSpec) (hIS : InvsSpec) (hPS : ProdsSpec) (hM : MulSpec)
    {OA : MachineState → Word → Model.TState → Prop} : GluedSpec OA := by
  intro s x u v Wl residual tf rt w0 hpre h h0
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.sp
  have G₀ := GS.init hpre h
  have kv (y : Word) (hy : (s.getReg .x2 - 776).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat) :
      v.getMem y = u.getMem y := h.toTI.keepStk hpre (Or.inr hy)
  have eP : vecPtr v (s.getReg .x2 - 664) = vecPtr u (s.getReg .x2 - 664) := by
    simp only [vecPtr]; exact kv _ ⟨by addr_omega [hb], by addr_omega [hb]⟩
  have eL : vecLen v (s.getReg .x2 - 664) = vecLen u (s.getReg .x2 - 664) := by
    simp only [vecLen]; exact kv _ ⟨by addr_omega [hb], by addr_omega [hb]⟩
  -- `0x8000bab0`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bab0_spec h.pc (by
    rv_eval [hsp]; valid_access hst.valid [hb])
  have hm₁ := b8000bab0_mem_same h₁
  have k₁ := b8000bab0_keeps h₁
  have G₁ := G₀.same hpre hm₁ (k₁ .x2 (by decide))
  have e392 : v.getMem (v.getReg .x2 + 392) = vecLen v (s.getReg .x2 - 664) := by
    rw [hsp]; simp only [vecLen]; rv_eval []
  have e384 : v.getMem (v.getReg .x2 + 384) = vecPtr v (s.getReg .x2 - 664) := by
    rw [hsp]; simp only [vecPtr]; rv_eval []
  have pc₁ : t₁.pc = 0x8000bab8 := b8000bab0_pc_not_taken h₁ (by
    rw [e392]; intro he; apply h0; rw [he]; rfl)
  -- `0x8000bab8`
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₁.sp
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000bab8_spec pc₁ (by
    rv_eval [sp₁]; and_intros <;> valid_access hst.valid [hb])
  have k₂ := b8000bab8_keeps h₂
  have F₂ : DFrame t₁ t₂ fun y ↦ Within y (s.getReg .x2 - 880) 8 := by
    have := DFrame.of_memFrame (b8000bab8_frame h₂ (by rw [sp₁]; addr_omega [hb]))
    rw [sp₁] at this
    exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  obtain ⟨G₂, -⟩ := G₁.stepS hpre F₂ (fun y hy ↦ Or.inl (by addr_omega [hy, hb]))
    (k₂ .x2 (by decide))
  have x10₁ : t₁.getReg .x10 = vecLen v (s.getReg .x2 - 664) := by rw [b8000bab0_x10 h₁, e392]
  have hg : GLI OA s x u v t₂ Wl residual tf rt w0 0 w0 := {
    tb := h
    gs := G₂
    pc := b8000bab8_pc h₂
    jlt := by rw [← eL]; omega
    x8 := by
      rw [b8000bab8_x8 h₂, sp₁, hm₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 384 =
        v.getReg .x2 + 384 by rw [hsp], e384, eP]
      simp only [gAddr, Nat.mul_zero, add_ofNat_zero]
    m880 := by
      have := b8000bab8_m_x2_160 h₂
      rw [sp₁, x10₁, hm₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 384 =
        v.getReg .x2 + 384 by rw [hsp], e384, eP, eL] at this
      rw [← this]; congr 1; addr_omega [hb]
    fold := by simp only [List.take_zero, gluedFold, List.foldlM_nil]; rfl
    wt := by
      rw [← h.wt, F₂.eAt fun i hi hw ↦ by addr_omega [hw, hi, hb]]
      simp only [eAt, hm₁] }
  obtain ⟨w', r', hw'⟩ := gLoop hEq hRS hIS hPS hM hpre _ 0 w0 t₂ rfl hg
  refine ⟨w', r₁.trans (r₂.trans r'), ?_⟩
  rcases hw' with hf | ⟨wf, hc⟩
  · exact Or.inl hf
  · exact Or.inr ⟨_, _, _, _, _, hc⟩

end Rv64Verifier.Proofs.Pcs.Vso
