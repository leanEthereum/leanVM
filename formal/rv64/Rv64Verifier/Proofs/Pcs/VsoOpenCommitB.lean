import Rv64Verifier.Proofs.Pcs.VsoOpenCommitA

/-!
# `verify_stacked_opening`'s level loop: reading the commitment

`0x8000a534` calls `next_scalars(2)` into `S - 384`; `0x8000a548` returns its `Err`, `0x8000a55c`
and `0x8000a564` trap on fewer than two scalars, `0x8000a574` returns `Err` (`0x8000b874`) when a
half's top limb is nonzero: then the halves make the root `dOf`, and the mirror's `TM.commit` has
run (`CommitH`, at `0x8000a588`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem eListAt_getD' (u : MachineState) (P : Word) {n i : ℕ} (hi : i < n) :
    (eListAt u P n).getD i 0 = eAt u (P + BitVec.ofNat 64 (24 * i)) := by
  simp [eListAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- At `0x8000a588`, from `u` at `0x8000a534`: the root's halves at `p` (from `t` on), the mirror
after `TM.commit`. -/
structure CommitH (s : MachineState) (x : LCtx) (h t u w : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q : List E) (p : Word) : Prop where
  at304 : At304 s x h t u ℓ Wl lf q
  pc : w.pc = 0x8000a588
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s w (w.getMem nextAddr)
  heap : HeapOk w
  mono : heapNext t ≤ heapNext w
  fr : DFrame u w fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
    Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a nextAddr 8 ∨ (heapNext t ≤ a.toNat ∧ a.toNat < heapNext w)
  x1 : w.getReg .x1 = p
  x8 : w.getReg .x8 = 0xffffffffffffffff
  x9 : w.getReg .x9 = x.FP
  x12 : w.getReg .x12 = BitVec.ofNat 64 ((s.getReg .x12).toNat - (Wl.folds ++ lf).length)
  x27 : w.getReg .x27 = s.getReg .x10
  buf : p.toNat % 8 = 0 ∧ heapNext t ≤ p.toNat ∧ p.toNat + 48 ≤ heapNext w
  top : w.getMem (p + 16) = 0 ∧ w.getMem (p + 24 + 16) = 0
  dig : digestAt w (s.getReg .x11) = digestAt u (s.getReg .x11)
  value : RunsC s w ℓ
    (Model.TM.samples ((s.getReg .x12).toNat - (Wl.folds ++ lf).length) >>= fun pt ↦
      Model.TM.nextScalar >>= fun v ↦ Model.TM.sumcheckRoundPoly 3 v none >>= fun i ↦
      Model.Pcs.afterCommit (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (fcOf s ℓ)
        (rtOf s ℓ) (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf
        ([], [(i, Model.Pcs.GluedWeightRust.ood pt)]))
    [(dOf w p, rootShape s (ℓ + 1))]

/-- **`0x8000a534`**: the commitment read, or an `Err`, or a trap. -/
theorem commitRead (hNS : NextScalarsSpec) {s : MachineState} {x : LCtx} {h t u : MachineState}
    {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q : List E} (hpre : VsoPre s) (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (ha : At304 s x h t u ℓ Wl lf q) (hl : ℓ ≠ K0 s + 1) (hpc : u.pc = 0x8000a534) :
    ∃ w, Reaches Image.code u w ∧ (FailR s w ∨ ∃ p, CommitH s x h t u w ℓ Wl lf q p) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hf := ha.fo
  have hsp : u.getReg .x2 = s.getReg .x2 - 1040 := (ha.regs .x2 (by decide)).trans hf.sp
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hrs := hpre.rootSponge
  have hlvl := hf.head.lvl
  have hlen : (Wl.folds ++ lf).length = ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum := by
    rw [List.length_append, hnf, hf.lfl, take_succ_sum]; rfl
  have hle := folds_le hc hlvl
  rw [← hlen] at hle
  have inv₀ : InvR s t (t.getMem nextAddr) :=
    FW.inv hpre hf.head hf.fr hf.heap hf.mono (hf.sp.trans hf.head.sp.symm)
  have hX₁ (a : Word) (hw : Within a (s.getReg .x2 - 928) 8 ∨ Within a (s.getReg .x2 - 912) 8 ∨
      Within a (s.getReg .x2 - 896) 8 ∨ Within a (s.getReg .x2 - 872) 8 ∨
      Within a (s.getReg .x2 - 808) 8 ∨ Within a (s.getReg .x2 - 792) 8 ∨
      Within a (s.getReg .x2 - 616) 32) : Within a (s.getReg .x2 - 1040) 936 := by
    rcases hw with hw | hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hb]
  obtain ⟨nx₁, inv₁⟩ := InvR.stk hpre inv₀ ha.fr hX₁ (ha.regs .x2 (by decide))
  have V₁ := hf.value.toC
  rw [afk_commit s x hl hlvl] at V₁
  have V₁ := V₁.keep hpre inv₀ ha.fr (fun a ha' ↦ Or.inl (by have := hX₁ a ha'; addr_omega [this, hb]))
    fun y hy hw ↦ by have := hX₁ y hw; addr_omega [hy, this, hrst, hb]
  -- `next_scalars(2)`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a534_spec hpc trivial
  have k₁ := b8000a534_keeps h₁
  have hm₁ := b8000a534_mem_same h₁
  have inv₁' : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [hm₁]; exact Inv.same' inv₁ hm₁ (k₁ .x2 (by decide))
  have hn₁ : heapNext t₁ = heapNext t := by simp only [heapNext, hm₁, nx₁]
  have hheap₁ : HeapOk t₁ := ⟨by have := hf.heap.lo; omega, by have := hf.heap.hi; omega⟩
  have x11₁ : t₁.getReg .x11 = s.getReg .x10 := by
    rw [b8000a534_x11 h₁, ha.regs .x27 (by decide), hf.x27]
  obtain ⟨t₂, hr₂, hv₂⟩ := callNextScalars (o := s.getReg .x2 - 384) hNS hpre inv₁' hheap₁
    (b8000a534_pc h₁) (by rw [b8000a534_x10 h₁, hsp]; addr_omega [hb]) x11₁
    (by simp only [Slot24]; addr_omega [hb])
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, herr₂, hok₂, hval₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl (Or.inl hd)⟩
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [hpres₂ .x2 (by decide), k₁ .x2 (by decide), hsp]
  have inv₂ := InvR.callT hpre inv₁' X₂ (by simp only [Slot24]; addr_omega [hb]) hheap₂ hmono₂
    ((hpres₂ .x2 (by decide)))
  have x8₂ : t₂.getReg .x8 = 0xffffffffffffffff := by
    rw [hpres₂ .x8 (by decide), k₁ .x8 (by decide), ha.regs .x8 (by decide), hf.x8]
  have e656 : t₂.getReg .x2 + 656 = s.getReg .x2 - 384 := by addr_omega [hb, sp₂]
  have e664 : t₂.getReg .x2 + 664 = s.getReg .x2 - 384 + 8 := by addr_omega [hb, sp₂]
  have e672 : t₂.getReg .x2 + 672 = s.getReg .x2 - 384 + 16 := by addr_omega [hb, sp₂]
  -- `0x8000a548`: the `Err` check
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a548_spec
    (by rw [hpc₂, returnAddress_eq, b8000a534_x1 h₁]; decide) (by
      rv_eval [sp₂]
      and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000a548_keeps h₃
  have hm₃ := b8000a548_mem_same h₃
  have inv₃ : InvR s t₃ (t₃.getMem nextAddr) := by
    rw [hm₃]; exact Inv.same' inv₂ hm₃ (k₃ .x2 (by decide))
  have hr₁₃ := hr₁.trans (hr₂.trans hr₃)
  by_cases herr : vecCap t₂ (s.getReg .x2 - 384) = errNiche
  · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a558_spec
      (b8000a548_pc_not_taken h₃ (by rw [e656, x8₂]; exact herr)) trivial
    have inv₄ : InvR s t₄ (t₃.getMem nextAddr) :=
      Inv.same' inv₃ (b8000a558_mem_same h₄) (b8000a558_keeps h₄ .x2 (by decide))
    obtain ⟨w, hw, hfw⟩ := fail844 inv₄ (b8000a558_pc h₄) (by
      rw [b8000a558_keeps h₄ .x1 (by decide), b8000a548_x1 h₃, e664]
      simpa only [okTag, errNiche] using herr₂ herr)
    exact ⟨w, hr₁₃.trans (hr₄.trans hw), Or.inl hfw⟩
  obtain ⟨hvo, hnb⟩ := hok₂ herr
  have hpc₃ := b8000a548_pc_taken h₃ (by rw [e656, x8₂]; exact herr)
  set P := vecPtr t₂ (s.getReg .x2 - 384) with hP
  set n := vecLen t₂ (s.getReg .x2 - 384) with hn
  have x1₃ : t₃.getReg .x1 = P := by rw [b8000a548_x1 h₃, e664]; rfl
  have x26₃ : t₃.getReg .x26 = n := by rw [b8000a548_x26 h₃, e672]; rfl
  -- at least two scalars
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a55c_spec hpc₃ trivial
  by_cases hz : n = 0
  · obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000a560_spec
      (b8000a55c_pc_not_taken h₄ (by rw [x26₃, hz])) trivial
    exact ⟨t₅, hr₁₃.trans (hr₄.trans hr₅), Or.inl (Or.inl (dead_of_fetch (by
      rw [b8000a560_pc h₅]; exact trap)))⟩
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000a564_spec
    (b8000a55c_pc_taken h₄ (by rw [x26₃]; exact hz)) (by
      rv_eval [(b8000a55c_keeps h₄ .x2 (by decide)).trans ((k₃ .x2 (by decide)).trans sp₂)]
      valid_access hst.valid [hb])
  have k₄ := b8000a55c_keeps h₄
  have k₅ := b8000a564_keeps h₅
  by_cases h1 : n = 1
  · obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000a570_spec
      (b8000a564_pc_not_taken h₅ (by rw [k₄ .x26 (by decide), x26₃, h1])) trivial
    exact ⟨t₆, hr₁₃.trans (hr₄.trans (hr₅.trans hr₆)), Or.inl (Or.inl (dead_of_fetch (by
      rw [b8000a570_pc h₆]; exact trap)))⟩
  have hpc₅ := b8000a564_pc_taken h₅ (by rw [k₄ .x26 (by decide), x26₃]; exact h1)
  have hn2 : 2 ≤ n.toNat := by
    have h0 : n.toNat ≠ 0 := fun e ↦ hz (by addr_omega [e])
    have h1' : n.toNat ≠ 1 := fun e ↦ h1 (by addr_omega [e])
    omega
  have hraw := hvo.raw
  simp only [RawVecOk, Buf] at hraw
  have hlc := hvo.len
  simp only [NewBuf] at hnb
  have hhi₂ := hheap₂.hi
  have hc2 : 2 ≤ (vecCap t₂ (s.getReg .x2 - 384)).toNat := le_trans hn2 hlc
  have hbuf : P.toNat % 8 = 0 ∧ heapNext t₁ ≤ P.toNat ∧ P.toNat + 48 ≤ heapNext t₂ := by
    rcases hnb.2 with h0 | h0
    · omega
    · exact ⟨hraw.1, h0.1, by omega⟩
  have hRP : Region P 48 := heap_region (by have := hheap₁.lo; simp only [heapStart] at this; omega)
    (by omega) hbuf.1
  have x1₅ : t₅.getReg .x1 = P := by rw [k₅ .x1 (by decide), k₄ .x1 (by decide), x1₃]
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000a574_spec hpc₅ (by
    rv_eval [x1₅]
    and_intros <;> exact Region.valid hRP (by addr_omega [hbuf]) (by addr_omega [hbuf])
      (by addr_omega [hbuf]))
  have k₆ := b8000a574_keeps h₆
  have hm₆ := b8000a574_mem_same h₆
  have hm₄ := b8000a55c_mem_same h₄
  have hm₅ := b8000a564_mem_same h₅
  have hm₂₆ (a : Word) : t₆.getMem a = t₂.getMem a := by rw [hm₆, hm₅, hm₄, hm₃]
  have inv₆ : InvR s t₆ (t₆.getMem nextAddr) := by
    rw [hm₆, hm₅, hm₄]
    exact Inv.same' inv₃ (fun a ↦ by rw [hm₆, hm₅, hm₄])
      (by rw [k₆ .x2 (by decide), k₅ .x2 (by decide), k₄ .x2 (by decide)])
  have sp₆ : t₆.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [k₆ .x2 (by decide), k₅ .x2 (by decide), k₄ .x2 (by decide), k₃ .x2 (by decide), sp₂]
  have hr₁₆ := hr₁₃.trans (hr₄.trans (hr₅.trans hr₆))
  by_cases htop : t₅.getMem (P + 16) ||| t₅.getMem (P + 40) = 0
  swap
  · obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000a584_spec
      (b8000a574_pc_not_taken h₆ (by rw [x1₅]; exact htop)) trivial
    obtain ⟨t₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000b874_spec (b8000a584_pc h₇) (by
      rv_eval [(b8000a584_keeps h₇ .x2 (by decide)).trans sp₆]
      and_intros <;> first
        | addr_omega [hb]
        | (refine validAccess_one ?_; addr_omega [stack_mapped hpre, hb]))
    have inv₈ : InvR s t₈ (t₆.getMem nextAddr) := Inv.same' inv₆
      (fun a ↦ by rw [b8000b874_mem_same h₈, b8000a584_mem_same h₇])
      (by rw [b8000b874_keeps h₈ .x2 (by decide), b8000a584_keeps h₇ .x2 (by decide)])
    obtain ⟨w, hw, hfw⟩ := fail844 inv₈ (b8000b874_pc h₈) (by rw [b8000b874_x1 h₈]; decide)
    exact ⟨w, hr₁₆.trans (hr₇.trans (hr₈.trans hw)), Or.inl hfw⟩
  -- the halves' top limbs are zero: the root
  have e40 : P + 40 = P + 24 + 16 := by addr_omega [hbuf]
  have hpc₆ := b8000a574_pc_taken h₆ (by rw [x1₅]; exact htop)
  simp only [hm₅, hm₄, hm₃] at htop
  have htop' := BitVec.or_eq_zero_iff.mp htop
  have z0 : t₂.getMem (P + 16) = 0 := htop'.1
  have z1 : t₂.getMem (P + 24 + 16) = 0 := by rw [← e40]; exact htop'.2
  have hdOf : dOf t₆ P = dOf t₂ P := by simp only [dOf, eAt, hm₂₆]
  have hn₂ : heapNext t₆ = heapNext t₂ := by simp only [heapNext, hm₂₆]
  have hhi₂ := hheap₂.hi
  have hrs₀ : heapNext s ≤ heapNext t₁ := inv₁'.mono
  have Xu : DFrame u t₆ fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
      Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
      Within a nextAddr 8 ∨ (heapNext t ≤ a.toNat ∧ a.toNat < heapNext t₆) :=
    ((DFrame.of_same hm₁ _).trans X₂ fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))).trans
      (DFrame.of_same hm₂₆ _) fun _ h ↦ h
  have hdig : digestAt t₆ (s.getReg .x11) = digestAt u (s.getReg .x11) :=
    digest_keep Xu (root_bound hpre) fun y hy hw ↦ by
      rcases hw with hw | hw | hw | hw | hw
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrs]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrf.2]
      · rcases hrf.1 with h1 | h1
        · have hs₀ : heapNext s ≤ heapNext t := inv₀.mono
          addr_omega [hy, hw.1, h1, hs₀]
        · addr_omega [hy, hw.2, h1, hhi₂, hn₂]
  -- the mirror's `TM.commit`
  have hsh := rootShape_next s (ℓ := ℓ) hlen
  have hfl : (Model.Pcs.foldSt Wl lf q).1.folds.length = (Wl.folds ++ lf).length := rfl
  rw [hfl] at V₁
  have V₂ := V₁.bind (v := t₆) (nx' := [(dOf t₆ P, rootShape s (ℓ + 1))]) (dOf t₆ P) hdig
    fun T hT ↦ by
      have hT₁ : TranscriptAt t₁ (s.getReg .x10) T :=
        tr_keep hpre inv₁ hT (DFrame.of_same hm₁ fun _ ↦ False) fun _ h ↦ h.elim
      have hv := hval₂ T hT₁
      have h2 : (t₁.getReg .x12).toNat = 2 := by rw [b8000a534_x12 h₁]; rfl
      rw [h2] at hv
      cases hrun : (Model.TM.nextScalars 2).run T with
      | none => rw [hrun] at hv; exact absurd hv herr
      | some r =>
        obtain ⟨xs, T₁⟩ := r
        rw [hrun] at hv
        obtain ⟨-, hnew, hT₂⟩ := hv
        have hk := Model.Pcs.Keeps.nextScalars _ T xs T₁ hrun
        have hxs : xs = eListAt t₂ P n.toNat := hnew.elems.symm
        have g0 : xs.getD 0 0 = eAt t₂ P := by
          rw [hxs, eListAt_getD' _ _ (by omega)]; exact congrArg _ (add_ofNat_zero _)
        have g1 : xs.getD 1 0 = eAt t₂ (P + 24) := by
          rw [hxs, eListAt_getD' _ _ (by omega)]; rfl
        have h6 := tr_keep hpre inv₂ hT₂ (DFrame.of_same hm₂₆ fun _ ↦ False) fun _ h ↦ h.elim
        refine ⟨{ T₁ with roots := T.roots ++ [(dOf t₆ P, rootShape s (ℓ + 1))] }, ?_,
          ⟨h6.stream, h6.sponge, h6.streamOffset, h6.openingOffset⟩, hk.1, hk.2.2, rfl⟩
        rw [Model.Pcs.commit_run, hrun]
        simp only [Option.bind_some, g0, g1, fromHalves_eAt t₂ P z0 z1, Option.map_some, hdOf,
          hsh]
  have hmo₂ := hmono₂
  have e168 : t₄.getReg .x2 + 168 = s.getReg .x2 - 872 := by
    addr_omega [hb, (k₄ .x2 (by decide)).trans ((k₃ .x2 (by decide)).trans sp₂)]
  have m168 : t₄.getMem (s.getReg .x2 - 872) = u.getMem (s.getReg .x2 - 872) := by
    rw [hm₄, hm₃, ← hm₂₆ _]
    exact Xu _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw | hw
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb, hIs, hS]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb, hnx]
      · addr_omega [hw.2, hi, hb, hhi₂, hn₂]
  refine ⟨t₆, hr₁₆, Or.inr ⟨P, {
    at304 := ha
    pc := hpc₆
    sp := sp₆
    inv := inv₆
    heap := ⟨by have := hheap₂.lo; omega, by omega⟩
    mono := by omega
    fr := Xu
    x1 := by rw [k₆ .x1 (by decide), x1₅]
    x8 := by
      rw [k₆ .x8 (by decide), k₅ .x8 (by decide), k₄ .x8 (by decide), k₃ .x8 (by decide), x8₂]
    x9 := by
      rw [k₆ .x9 (by decide), k₅ .x9 (by decide), k₄ .x9 (by decide), k₃ .x9 (by decide),
        hpres₂ .x9 (by decide), k₁ .x9 (by decide), ha.regs .x9 (by decide), hf.x9]
    x12 := by
      rw [k₆ .x12 (by decide), b8000a564_x12 h₅, e168, m168, ha.m168]; addr_omega [hle]
    x27 := by
      rw [k₆ .x27 (by decide), k₅ .x27 (by decide), k₄ .x27 (by decide), k₃ .x27 (by decide),
        hpres₂ .x27 (by decide), k₁ .x27 (by decide), ha.regs .x27 (by decide), hf.x27]
    buf := ⟨hbuf.1, by omega, by omega⟩
    top := ⟨by rw [hm₂₆]; exact z0, by rw [hm₂₆]; exact z1⟩
    dig := hdig
    value := V₂ }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
