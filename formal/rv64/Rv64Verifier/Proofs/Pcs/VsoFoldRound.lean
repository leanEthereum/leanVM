import Rv64Verifier.Proofs.Pcs.VsoFoldEval

/-!
# `verify_stacked_opening`'s level loop: a fold round's polynomial

`0x8000a2ac` calls `sumcheck_round_poly(S - 160, transcript, 3, S - 464, None)`; `0x8000a2cc`
takes its `Err` to `0x8000b84c`, which returns it, or the new quadratic into `s6`/`s7`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000a2e4`, round `n` done: `lf` drawn (`n + 1` of them), the quadratic `q`. -/
structure Rd (s : MachineState) (x : LCtx) (h u : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (n : ℕ) (lf q : List E) : Prop
    extends RB s x h u ℓ Wl (Wl.folds ++ lf) lf q where
  pc : u.pc = 0x8000a2e4
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 640)
  x20 : u.getReg .x20 = BitVec.ofNat 64 (24 * n)
  x21 : u.getReg .x21 = BitVec.ofNat 64 (n + 1)
  x24 : u.getReg .x24 = BitVec.ofNat 64 Wl.folds.length
  x8 : u.getReg .x8 = 0xffffffffffffffff
  jlt : n < fcOf s ℓ
  lfl : lf.length = n + 1
  value : Runs s u ℓ (Model.Pcs.TM.loopN Model.Pcs.foldRoundRust (fcOf s ℓ - (n + 1))
    (Model.Pcs.foldSt Wl lf q) >>= AFk s x ℓ)

theorem roundStep (hRP : RoundPolyErrSpec) {s : MachineState} {x : LCtx} {h u : MachineState}
    {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {j : ℕ} {lf q : List E} {c : E}
    (hpre : VsoPre s) (hs : PL s x h u ℓ Wl j lf q c) :
    ∃ v, Reaches Image.code u v ∧ (FailR s v ∨ ∃ q', Rd s x h v ℓ Wl j (lf ++ [c]) q') := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hs.sp
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hfree := hI.free
  simp only [Outside] at hfree
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hrsp := hpre.rootSponge
  have hf := hs.head.facts
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a2ac_spec hs.pc (by
    rv_eval [hsp]; valid_access hst.valid [hb])
  have k₁ := b8000a2ac_keeps h₁
  have X₁ : DFrame u t₁ fun a ↦ Within a (s.getReg .x2 - 384) 8 := by
    have := DFrame.of_memFrame (b8000a2ac_frame h₁ (by rw [hsp]; addr_omega [hb]))
    rw [hsp] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, hb]
  have nx₁ : t₁.getMem nextAddr = u.getMem nextAddr := X₁ _ fun i hi hw ↦ by
    addr_omega [hw, hi, hb, hnx]
  have hRB₁ := RB.carry hpre hs.toRB X₁
    (fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))))
    (fun a ha ↦ by
      have hB := hs.bufs
      have hhu := hs.heap.hi
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · simp only [RSlots] at hw
        rcases hw with hw | hw | hw | hw | hw <;> addr_omega [ha, hw, hb]
      · simp only [RBufs] at hw
        rcases hw with hw | hw | hw
        · rcases hB.F with h0 | h0
          · simp only [Within] at hw; omega
          · addr_omega [ha, hw, hb, h0.2, hhu]
        · rcases hB.LF with h0 | h0
          · simp only [Within] at hw; omega
          · addr_omega [ha, hw, hb, h0.2, hhu]
        · rcases hB.Q with h0 | h0
          · simp only [Within] at hw; omega
          · addr_omega [ha, hw, hb, h0.2, hhu])
    ⟨by simp only [heapNext, nx₁]; exact hs.heap.lo, by simp only [heapNext, nx₁]; exact hs.heap.hi⟩
    (by simp only [heapNext, nx₁]; exact Nat.le_refl _)
    (fun r hr' ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₁ _ (by decide))
  have inv := FW.inv hpre hs.head hs.fr hs.heap hs.mono (hsp.trans hs.head.sp.symm)
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := hRB₁.sp
  have inv₁ := FW.inv hpre hs.head hRB₁.fr hRB₁.heap hRB₁.mono (sp₁.trans hs.head.sp.symm)
  have v₁ := hs.value.keepStk hpre inv X₁ fun a ha ↦ by addr_omega [ha, hb]
  have pe₁ : eAt t₁ (s.getReg .x2 - 464) = Model.polyEvalRust q c := by
    rw [← hs.pe]; exact X₁.eAt' (fun y hy hw ↦ by addr_omega [hy, hw, hb]) (by addr_omega [hb])
  obtain ⟨t₂, hr₂, hv₂⟩ := callRoundPoly (o := s.getReg .x2 - 160) (cl := s.getReg .x2 - 464) hRP
    hpre inv₁ hRB₁.heap (b8000a2ac_pc h₁) (by rw [b8000a2ac_x10 h₁, hsp]; addr_omega [hb])
    (by rw [b8000a2ac_x11 h₁, hs.x27]) (b8000a2ac_x12 h₁)
    (by rw [b8000a2ac_x13 h₁, hsp]; addr_omega [hb]) (by rw [b8000a2ac_x14 h₁, hsp]; addr_omega [hb])
    (by have := b8000a2ac_m_x2_656 h₁; rw [hsp] at this; rv_eval [] at this; exact this)
    (by addr_omega [hb]) (by addr_omega [hb])
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, herr, hok, hval⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl (Or.inl hd)⟩
  have hhi₂ := hheap₂.hi
  have hX₂s (a : Word) (ha : Within a (s.getReg .x2 - 160) 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
      Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t₁ t₂ a) :
      Wr s vsoStack (WR s) (t₂.getMem nextAddr) a := by
    rcases ha with ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hS]))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr ⟨by
        have := hRB₁.mono; have := hs.mono; have := hf.hs; have := hf.hL; omega, ha.2⟩))
  have inv₂ : InvR s t₂ (t₂.getMem nextAddr) :=
    Inv.step' hpre inv₁ X₂ hX₂s (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · addr_omega [ha, hb]
      · addr_omega [ha, hIs, hS, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx]
      · simp only [Fresh] at ha; addr_omega [ha.2, hhi₂, hb])
      rfl hmono₂ hhi₂ (hpres₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := by
    rw [hpres₂ .x2 (by decide), sp₁]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a2cc_spec
    (by rw [hpc₂, returnAddress_eq, b8000a2ac_x1 h₁]; decide) (by
      rv_eval [sp₂]; and_intros <;> valid_access hst.valid [hb])
  have hm₃ := b8000a2cc_mem_same h₃
  have k₃ := b8000a2cc_keeps h₃
  have hcap : t₂.getMem (t₂.getReg .x2 + 880) = vecCap t₂ (s.getReg .x2 - 160) := by
    rw [sp₂]; simp only [vecCap]; rv_eval []
  by_cases he : vecCap t₂ (s.getReg .x2 - 160) = errNiche
  · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a2e0_spec
      (b8000a2cc_pc_not_taken h₃ (by rw [hcap]; exact he)) trivial
    obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000b84c_spec (b8000a2e0_pc h₄) trivial
    have hm₅ (a : Word) : t₅.getMem a = t₂.getMem a := by
      rw [b8000b84c_mem_same h₅, b8000a2e0_mem_same h₄, hm₃]
    refine ⟨t₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl (Or.inr
      ⟨b8000b84c_pc h₅, ?_, _, Inv.same' inv₂ hm₅ (by
        rw [b8000b84c_keeps h₅ .x2 (by decide), b8000a2e0_keeps h₄ .x2 (by decide),
          k₃ .x2 (by decide)])⟩)⟩
    rw [b8000b84c_x10 h₅, b8000a2e0_keeps h₄ .x22 (by decide), b8000a2cc_x22 h₃, sp₂]
    have := herr he
    rv_eval [] at this ⊢
    exact this
  obtain ⟨hvo, hnb⟩ := hok he
  have X : DFrame t₁ t₃ fun a ↦ Within a (s.getReg .x2 - 160) 24 ∨
      Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
      Within a nextAddr 8 ∨ Fresh t₁ t₂ a :=
    X₂.trans (DFrame.of_same hm₃ (fun _ ↦ False)) fun _ h ↦ h.elim
  have hn₃ : heapNext t₃ = heapNext t₂ := by simp only [heapNext, hm₃]
  have hheap₃ : HeapOk t₃ := ⟨by rw [hn₃]; exact hheap₂.lo, by rw [hn₃]; exact hhi₂⟩
  have hmono₃ : heapNext t₁ ≤ heapNext t₃ := by rw [hn₃]; exact hmono₂
  have hB₁ := hRB₁.bufs
  have hm1 := hRB₁.mono
  have hm0 := hs.mono
  have hLs := hf.hs
  have hLh := hf.hL
  have hhu₁ := hRB₁.heap.hi
  -- a buffer of the round, from the mark below `NEXT` at `t₁`, misses the call's writes
  have mb {p : Word} {n : ℕ} (h0 : n = 0 ∨ x.L ≤ p.toNat ∧ p.toNat + n ≤ heapNext t₁) :
      ∀ a, (Within a (s.getReg .x2 - 160) 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
        Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t₁ t₂ a) →
        ¬ Within a p n := fun a ha hw ↦ by
    rcases h0 with h0 | h0
    · simp only [Within] at hw; omega
    rcases ha with ha | ha | ha | ha | ha
    · addr_omega [ha, hw, hb, h0.2, hhu₁]
    · rcases hfree.1 with h1 | h1
      · addr_omega [ha, hw, h1, h0.1, hLs, hS]
      · addr_omega [ha, hw, h1, h0.2, hhu₁, hS]
    · addr_omega [ha, hw, hb, h0.2, hhu₁]
    · addr_omega [ha, hw, hnx, h0.2, hhu₁]
    · simp only [Fresh] at ha; addr_omega [ha.1, hw, h0.2]
  have mh (a : Word) (ha : Within a (s.getReg .x2 - 160) 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
      Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t₁ t₂ a)
      (A : Word) (hA : (s.getReg .x2 - 856).toNat ≤ A.toNat ∧ A.toNat + 24 ≤ (s.getReg .x2 - 616).toNat) :
      ¬ Within a A 24 := fun hw ↦ by
    rcases ha with ha | ha | ha | ha | ha
    · addr_omega [ha, hw, hA, hb]
    · addr_omega [ha, hw, hA, hIs, hS, hb]
    · addr_omega [ha, hw, hA, hb]
    · addr_omega [ha, hw, hA, hb, hnx]
    · simp only [Fresh] at ha; addr_omega [ha.2, hw, hA, hhi₂, hb]
  have hFk := vecE_keep X hRB₁.F.1 (fun a ha ↦ ⟨mh a ha _ (by addr_omega [hb]),
    mb (by rcases hB₁.F with h0 | h0; exact Or.inl h0; exact Or.inr h0) a ha⟩)
    (by addr_omega [hb]) hmono₃ hRB₁.heap
  have hLk := vecE_keep X hRB₁.LF.1 (fun a ha ↦ ⟨mh a ha _ (by addr_omega [hb]),
    mb (by rcases hB₁.LF with h0 | h0; exact Or.inl h0; exact Or.inr h0) a ha⟩)
    (by addr_omega [hb]) hmono₃ hRB₁.heap
  have e22 : t₃.getReg .x22 = vecPtr t₂ (s.getReg .x2 - 160) := by
    rw [b8000a2cc_x22 h₃, sp₂]; simp only [vecPtr]; rv_eval []
  have e23 : t₃.getReg .x23 = vecLen t₂ (s.getReg .x2 - 160) := by
    rw [b8000a2cc_x23 h₃, sp₂]; simp only [vecLen]; rv_eval []
  have hql := hvo.len
  have hsmq := vec_small hvo hheap₂
  have hRB₃ := RB.carryQ (fl' := Wl.folds ++ (lf ++ [c])) (lfs' := lf ++ [c])
    (q' := vecEs t₂ (s.getReg .x2 - 160)) hpre hRB₁ X
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by simp only [W]; addr_omega [ha, hS])))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨by omega, by rw [show (t₃.getMem nextAddr).toNat = heapNext t₃ from rfl, hn₃]
                        exact ha.2⟩))))))))
    (fun a ha hw ↦ by
      rcases hw with hw | hw | hw <;> rcases ha with ha | ha | ha | ha | ha
      all_goals first
        | addr_omega [ha, hw, hb]
        | addr_omega [ha, hw, hIs, hS, hb]
        | addr_omega [ha, hw, hb, hnx]
        | (simp only [Fresh] at ha; addr_omega [ha.2, hw, hhi₂, hb]))
    hheap₃ hmono₃
    (fun r hr' ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [k₃ _ (by decide), hpres₂ _ (by decide)])
    ⟨hFk.1, by rw [hFk.2.1, hRB₁.F.2.1, List.append_assoc], by
      rw [hFk.2.2.1, hFk.2.2.2.1]
      rcases hRB₁.F.2.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (NewBuf.grow h0 hmono₃)⟩
    ⟨hLk.1, by rw [hLk.2.1]; exact hRB₁.LF.2.1, by
      rw [hLk.2.2.1, hLk.2.2.2.1]; exact NewBuf.grow hRB₁.LF.2.2 hmono₃⟩
    ⟨by rw [e22, e23]; simp only [vecEs, eListAt, eAt, hm₃], by rw [e22]; exact hnb.1, by
      rw [e22, e23]
      rcases hnb.2 with h0 | h0
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr ⟨by omega, by rw [hn₃]; omega⟩)⟩
    (by
      rw [hFk.2.2.1, hFk.2.2.2.1, hLk.2.2.1, hLk.2.2.2.1, e22, e23]
      refine ⟨hRB₁.ap.1, ?_, ?_⟩
      · rcases hnb.2 with h0 | h0
        · exact Or.inr (Or.inl (by omega))
        · rcases hB₁.F with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inr (Or.inl (by omega)))
      · rcases hnb.2 with h0 | h0
        · exact Or.inr (Or.inl (by omega))
        · rcases hB₁.LF with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inr (Or.inl (by omega))))
  have hLp₁ : vecPtr t₁ (s.getReg .x2 - 640) = vecPtr u (s.getReg .x2 - 640) :=
    X₁ _ fun i hi hw ↦ by addr_omega [hw, hi, hb]
  have hdig : digestAt t₃ (s.getReg .x11) = digestAt t₁ (s.getReg .x11) :=
    digest_keep X (root_bound hpre) fun y hy hw ↦ by
      rcases hw with hw | hw | hw | hw | hw
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrsp]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrf.2]
      · simp only [Fresh] at hw
        rcases hrf.1 with h0 | h0
        · addr_omega [hy, hw.1, h0, hm1, hm0, hLs, hLh]
        · addr_omega [hy, hw.2, h0, hhi₂]
  refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨vecEs t₂ (s.getReg .x2 - 160), {
    toRB := hRB₃
    pc := b8000a2cc_pc_taken h₃ (by rw [hcap]; exact he)
    x19 := by
      rw [k₃ .x19 (by decide), hpres₂ .x19 (by decide), k₁ .x19 (by decide), hs.x19,
        hLk.2.2.1, hLp₁]
    x20 := by rw [k₃ .x20 (by decide), hpres₂ .x20 (by decide), k₁ .x20 (by decide), hs.x20]
    x21 := by rw [k₃ .x21 (by decide), hpres₂ .x21 (by decide), k₁ .x21 (by decide), hs.x21]
    x24 := by rw [k₃ .x24 (by decide), hpres₂ .x24 (by decide), k₁ .x24 (by decide), hs.x24]
    x8 := b8000a2cc_x8 h₃
    jlt := hs.jlt
    lfl := by rw [List.length_append, hs.lfl]; rfl
    value := v₁.step hdig fun T hT ↦ by
      have hv := hval T hT
      rw [pe₁] at hv
      unfold Model.Pcs.roundK
      cases hrun : (Model.TM.sumcheckRoundPoly 3 (Model.polyEvalRust q c) none).run T with
      | none => rw [hrun] at hv; exact absurd hv he
      | some p =>
        obtain ⟨q2, T2⟩ := p
        rw [hrun] at hv
        obtain ⟨-, hnew, hT2⟩ := hv
        have hk := Model.Pcs.Keeps.roundPoly _ _ _ T q2 T2 hrun
        refine ⟨T2, by rw [run_bind_of hrun, hnew.elems], tr_keep hpre inv₂ hT2
          (DFrame.of_same hm₃ (fun _ ↦ False)) (fun _ h ↦ h.elim), hk.1, hk.2.1, hk.2.2⟩ }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
