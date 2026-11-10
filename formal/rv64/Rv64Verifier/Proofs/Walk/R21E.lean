import Rv64Verifier.Proofs.Walk.R21D
import Rv64Verifier.Proofs.Walk.R22C
import Rv64Verifier.Proofs.Walk.OpenA

/-!
# `walk` R21: `verify_stacked_opening`

`r21vso`: from `VsoR21`, `0x80004104` calls `verify_stacked_opening` on the transcript, the root
at `S - 1800`, `stack_log`, the rate and the stack claims; `Ok` (`a0 = -1`) reaches `0x80004144`
(`AtR22`, the mirror left with `finish`), an `Err` the error block `0x800041cc` (`Err41cc`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.PcsContracts Rv64Verifier.Pcs Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A step writing frame bytes outside `KeepN` (the root among them) keeps `RestN`. -/
theorem RestN.stepW {s u₀ v w : MachineState} (hpre : WalkPre s) (h : RestN s u₀ v)
    {W : Word → Prop} {T : Prop} (hW : ∀ a, W a → InF s a ∧ ¬ KeepN s u₀ a)
    (st : StepW s v w W T) : RestN s u₀ w := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hx := hpre.stack.next
  have hab := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hx
  rw [stackLo_eq] at hab
  have hh := st.heap.hi
  have m₀ := h.inv.mono
  have m₁ := h.mono
  have hv := h.inv.heap.hi
  have kept : ∀ a, (W a ∨ Within a (s.getReg .x2 - 11392) 8736 ∨ Within a nextAddr 8 ∨
      Fresh v w a ∨ (T ∧ Within a (tp s + 8) 352)) →
      (WalkW s w a ∧ ¬ Within a (s.getReg .x2 - 104) 104) := by
    intro a ha
    simp only [WalkW, Fresh, stackLo_eq, heapNext, heapEnd, InF] at ha hab hh m₀ hW ⊢
    rcases ha with ha | ha | ha | ⟨f1, f2⟩ | ⟨-, ha⟩
    · obtain ⟨⟨i1, i2⟩, -⟩ := hW a ha
      exact ⟨Or.inr (Or.inl (by addr_omega [i1, i2, hb1])), by addr_omega [i1, i2, hb1]⟩
    · exact ⟨Or.inr (Or.inl (by addr_omega [ha, hb1])), by addr_omega [ha, hb1]⟩
    · exact ⟨Or.inr (Or.inr (Or.inl ha)), by addr_omega [ha, hx, hb1]⟩
    · exact ⟨Or.inr (Or.inr (Or.inr ⟨by omega, f2⟩)), by addr_omega [f1, f2, hh, hab, hb1]⟩
    · rw [tp] at ha
      exact ⟨Or.inr (Or.inl (by addr_omega [ha, hb1])), by addr_omega [ha, hb1]⟩
  refine ⟨h.inv.step hpre st.frame kept st.heap st.mono st.sp, h.mono.trans st.mono,
    h.keep.trans st.frame fun a ha hK ↦ ?_⟩
  have hK1 := hK.1
  simp only [KeepR, Fresh, tp, heapNext, heapEnd] at hK1 ha hab hv m₁ hh
  rcases ha with ha | ha | ha | ⟨f1, f2⟩ | ⟨-, ha⟩
  · exact (hW a ha).2 hK
  all_goals
    rcases hK1 with (k | k | k | k | k | k) | ⟨-, k, -⟩ <;>
      first | addr_omega [ha, k, hb1, hab, hv, m₁, hx] | addr_omega [f1, f2, k, hb1, hab, hv, m₁, hh]

section Vso
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ f : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {cl : List ColumnClaim} {ks ke : ℕ} {tg : E} {rw : Pcs.RingWeightRust}

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- `verify_stacked_opening`: `Ok` to `0x80004144`, an `Err` to `0x800041cc`, or a dead end. -/
theorem r21vso {OA : MachineState → Word → TState → Prop} (hV : VsoSpec OA)
    (hB : OpenBridge OI OA) (hpre : WalkPre s) (hO : OpenPre s) (h : AtR17 OI s u₀ layout rows lir bus)
    (X : VsoR21 OI s u₀ f layout rows lir bus cl ks ke tg rw) :
    ∃ g, Reaches Image.code f g ∧
      (AtR22 OI s u₀ g (summaryOf layout rows lir bus ks ke) ∨ Err41cc s u₀ g ∨
        Dead Image.code g) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := X.rest.inv
  have sp := I.sp
  have hh := I.heap.hi
  have hs0 := hpre.heap.lo
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd, heapStart] at hh hs0 hab
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004104_spec X.pc (by
    rv_eval [sp, X.x24]
    and_intros <;> valid_access hval [hb1])
  have m₁ := b80004104_mem_same h₁
  have k₁ := b80004104_keeps h₁
  have I₁ : Inv s u₁ := I.same m₁ (k₁ .x2 (by decide))
  have R₁ := X.rest.same m₁ (k₁ .x2 (by decide))
  have ptr₁ : u₁.getMem (tp s) = s.getReg .x13 := by rw [m₁]; exact X.proofPtr
  have ea (c d : Word) (hc : c.toNat + d.toNat = 2656) : f.getReg .x2 + c = s.getReg .x2 - d := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have x10₁ : u₁.getReg .x10 = tp s := by rw [b80004104_x10 h₁, ea 208 2448 rfl]; rfl
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 1800 := by rw [b80004104_x11 h₁, ea 856 1800 rfl]
  have x12₁ : (u₁.getReg .x12).toNat = layout.stackLog := by
    rw [b80004104_x12 h₁, ea 760 1896 rfl, show (1896 : Word) = BitVec.ofNat 64 1896 from rfl,
      X.rest.get (keep_slot hpre (by omega))]
    exact h.layoutIn.stackLog
  have x13₁ : u₁.getReg .x13 = lir := by rw [b80004104_x13 h₁, X.x22]
  have x14₁ : u₁.getReg .x14 = vecPtr f (s.getReg .x2 - 512) := by
    rw [b80004104_x14 h₁, X.x24]; rfl
  have x15₁ : u₁.getReg .x15 = vecLen f (s.getReg .x2 - 512) := by
    rw [b80004104_x15 h₁, X.x24]; rfl
  have hk : vsoStack ≤ 8736 := by decide
  have hEnd : heapEnd ≤ (stackLo u₁ vsoStack).toNat := by
    rw [stackLo_callee I₁]; simp only [heapEnd]; addr_omega [hab, hb1, hk]
  -- the claims' buffer
  have vo := X.vec
  obtain ⟨⟨pa, pb⟩, pl⟩ := vo
  have hcl0 := X.claims
  have hw0 := X.weights
  simp only [stackClaimsAt] at hcl0
  obtain ⟨p, hp⟩ : ∃ p, vecPtr f (s.getReg .x2 - 512) = p := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, (vecLen f (s.getReg .x2 - 512)).toNat = n := ⟨_, rfl⟩
  rw [hp] at x14₁ pa pb hcl0 hw0
  rw [hn] at hcl0 hw0 pl
  have hn1 : 1 ≤ n := by
    have := congrArg List.length hcl0
    simp only [claimsAt, List.length_map, List.length_range, List.length_cons] at this; omega
  have pb' : heapStart ≤ p.toNat ∧ p.toNat + 88 * n ≤ heapNext f := by
    rcases pb with h0 | h0
    · omega
    · exact ⟨h0.1, by have := h0.2; omega⟩
  have hn₁ : heapNext u₁ = heapNext f := by simp only [heapNext, m₁]
  have hcb : HeapBuf u₁ p (88 * n) := ⟨pa, by rw [hn₁]; exact pb'.2, Or.inr pb'.1⟩
  have hwi (i : Nat) (hi : i < n) : WeightIn u₁ (p + BitVec.ofNat 64 (88 * i)) := by
    have := hw0 i hi
    unfold WeightIn RingIn HeapBuf at this ⊢
    simp only [vecPtr, vecLen, m₁, heapNext] at this ⊢
    exact this
  have hsub (i : Nat) (hi : i < n) : HeapBuf u₁ (p + BitVec.ofNat 64 (88 * i)) 64 ∧
      heapStart ≤ (p + BitVec.ofNat 64 (88 * i)).toNat := by
    have := hcb.sub I₁.heap pb'.1 (off := 88 * i) (m := 64) (by omega) (by omega)
    refine ⟨this, ?_⟩
    have := this.2.2; simp only [heapStart] at this ⊢; omega
  have fo (c : Word) (k m : Nat) (hc : c.toNat = k) (hk1 : 104 + m ≤ k) (hk2 : k ≤ 2656) :=
    fr_ok hpre I₁ (c := c) (k := k) (n := m) (m := vsoStack) hc hk1 hk2 hk
  have ofs (k : Nat) (hk1 : k ≤ 2656) : heapEnd ≤ (s.getReg .x2 - BitVec.ofNat 64 k).toNat := by
    simp only [heapEnd]; addr_omega [hab, hb1, hk1]
  have otp : heapEnd ≤ (tp s + 8).toNat := by
    rw [tp]; simp only [heapEnd]; addr_omega [hab, hb1]
  have pre : VsoPre u₁ := {
    heap := I₁.heap
    stack := hpre.stack.sub 2656 I₁.sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    rodata := I₁.rodata hpre
    self := by rw [x10₁]; exact tin hpre I₁ ptr₁ hk
    root := by
      rw [x11₁]
      obtain ⟨o1, o2, -⟩ := fo 1800 1800 32 rfl (by omega) (by omega)
      exact ⟨Or.inr (by addr_omega [hb1, hb2, hb3]), o2, o1⟩
    claims := by rw [x14₁, x15₁, hn]; exact hcb.src I₁.heap hEnd
    weights := fun i hi ↦ by
      rw [x15₁, hn] at hi; rw [x14₁]
      exact (hwi i hi).src I₁.heap hEnd (hsub i hi).1 (hsub i hi).2
    rootSponge := by rw [x11₁, x10₁, tp]; addr_omega [hb1]
    claimsSponge := by rw [x14₁, x15₁, hn, x10₁]; exact hcb.apart I₁.heap otp
    weightsSponge := fun i hi ↦ by
      rw [x15₁, hn] at hi; rw [x14₁, x10₁]; exact (hwi i hi).apart I₁.heap otp
    proofSponge := by
      rw [x10₁]
      have := proofApart_fr hpre I₁ ptr₁ (k := 2440) (n := 352) (by omega) (by omega)
      rwa [show s.getReg .x2 - BitVec.ofNat 64 2440 = tp s + 8 by rw [tp]; bv_omega] at this
    checked := by
      rw [x10₁, byteAt_congr (u := u₀) (by rw [tp]; addr_omega [hb1, hb3]) (by
        rw [m₁, show tp s + 360 = s.getReg .x2 - BitVec.ofNat 64 2088 by rw [tp]; bv_omega]
        exact X.rest.get (keep_slot hpre (by omega))), h.checked]
    rootSelf := by rw [x11₁, x10₁, tp]; addr_omega [hb1]
    rootRodata := by rw [x11₁]; exact (fo 1800 1800 32 rfl (by omega) (by omega)).2.2
    rootProof := by
      rw [x10₁, x11₁]; exact proofApart_fr hpre I₁ ptr₁ (k := 1800) (n := 32) (by omega) (by omega)
    rootClaims := by
      rw [x11₁, x14₁, x15₁, hn]; exact apart_comm (hcb.apart I₁.heap (ofs 1800 (by omega)))
    rootWeights := fun i hi ↦ by
      rw [x15₁, hn] at hi; rw [x14₁, x11₁]; exact (hwi i hi).apart I₁.heap (ofs 1800 (by omega))
    openMem := openMem_vso hpre hO I₁ ptr₁ x10₁ x11₁ }
  obtain ⟨g, hr, ⟨hpc, hp', post⟩ | hd⟩ := hV.call (Reaches.refl u₁) (b80004104_pc h₁) pre
  swap
  · exact ⟨g, hr₁.trans hr, Or.inr (Or.inr hd)⟩
  have fr := post.frame
  rw [x10₁, x11₁] at fr
  have st : StepW s u₁ g (Within · (s.getReg .x2 - 1800) 32) True := by
    refine ⟨fr.mono fun a ha ↦ ?_, post.heap, post.mono, hp' .x2 (by decide)⟩
    rcases ha with ha | ha | ha | ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, ha⟩)))
    · exact Or.inl ha
    · rw [stackLo_callee I₁] at ha
      exact Or.inr (Or.inl (by addr_omega [ha, hb1, hk]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  have RN := R₁.toN.stepW hpre (fun a ha ↦ ⟨by simp only [InF, Within] at ha ⊢; addr_omega [ha, hb1],
    fun hK ↦ hK.2 ha⟩) st
  have ptrg : g.getMem (tp s) = s.getReg .x13 := by
    rw [st.getF hpre (by rw [tp]; addr_omega [hb1])
      (fun i hi hw ↦ by rw [tp] at hw; simp only [Within] at hw; addr_omega [hw, hi, hb1])
      (fun _ ↦ by rw [tp]; addr_omega [hb1])]
    exact ptr₁
  obtain ⟨g₁, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000412c_spec
    (by rw [hpc, returnAddress_eq, b80004104_x1 h₁]; decide) (by rv_eval [])
  have m₂ := b8000412c_mem_same h₂
  have k₂ := b8000412c_keeps h₂
  have RN₂ := RN.same m₂ (k₂ .x2 (by decide))
  have x23₂ : g₁.getReg .x23 = s.getReg .x10 := by
    rw [k₂ .x23 (by decide), hp' .x23 (by decide), k₁ .x23 (by decide), X.x23]
  by_cases hok : g.getReg .x10 = 0xffffffffffffffff
  swap
  · have pc₂ := b8000412c_pc_not_taken h₂ hok
    have hR := hpre.out
    have hRb := hR.1
    have hRa := hR.2
    simp only [Mapped] at hRb
    obtain ⟨g₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004134_spec pc₂ (by
      rv_eval [x23₂]
      exact Region.valid hR (by addr_omega [hRb]) (by addr_omega [hRb]) (by addr_omega [hRb, hRa]))
    have fr₃ : DFrame g₁ g₂ (Within · (s.getReg .x10) 16) := by
      have := DFrame.of_memFrame (b80004134_frame h₃ (by rw [x23₂]; addr_omega [hRb]))
      rw [x23₂] at this
      exact this.mono fun a ha ↦ by simp only [Within] at ha ⊢; addr_omega [ha, hRb]
    refine ⟨g₂, hr₁.trans (hr.trans (hr₂.trans hr₃)), Or.inr (Or.inl ⟨b80004134_pc h₃,
      RN₂.result hpre (by omega) fr₃ (b80004134_keeps h₃ .x2 (by decide)), ?_, ?_⟩)⟩
    · rw [b80004134_keeps h₃ .x23 (by decide), x23₂]
    · right; exact b80004134_x10 h₃
  have pc₂ := b8000412c_pc_taken h₂ hok
  have hdig : digestAt u₁ (s.getReg .x2 - 1800) = digestAt u₀ (s.getReg .x2 - 1800) := by
    simp only [digestAt]
    congr 1
    funext i
    congr 1
    have hi := i.isLt
    rw [m₁, show s.getReg .x2 - 1800 + BitVec.ofNat 64 (8 * i.val) =
      s.getReg .x2 - BitVec.ofNat 64 (1800 - 8 * i.val) by addr_omega [hb1, hi]]
    exact X.rest.get (keep_slot hpre (by omega))
  have hcl₁ : claimsAt u₁ p n = ⟨.placedRing layout.qkeccak rw, tg⟩ :: cl.filterMap (onStackRust layout) := by
    rw [← hcl0]
    simp only [claimsAt, stackClaimAt, stackWeightAt, ringWeightAt, vecEs, eListAt, eAt, vecPtr,
      vecLen, m₁]
  refine ⟨g₁, hr₁.trans (hr.trans hr₂), Or.inl {
    pc := pc₂
    rest := RN₂
    proofPtr := by rw [m₂]; exact ptrg
    x23 := x23₂
    x24 := by rw [k₂ .x24 (by decide), hp' .x24 (by decide), k₁ .x24 (by decide), X.x24]
    tracks := fun proof hpf ↦ ?_ }⟩
  obtain ⟨T, eT, eR, hT, hrun⟩ := X.tracks proof hpf
  have hT₁ : TranscriptAt u₁ (tp s) T := TranscriptAt.same hpre I X.proofPtr m₁ hT
  have hOA : OA u₁ (tp s) T := hB s u₁ T hpre hO I₁ ptr₁ x10₁ x11₁ (by rw [eT]; exact hpf.openings)
  obtain ⟨T', hrun', hT'⟩ := post.value hok T (by rw [x10₁]; exact hT₁) (by rw [x10₁]; exact hOA)
    (by rw [eR, x11₁, hdig, x12₁, x13₁])
  rw [x12₁, x13₁, x14₁, x15₁, hn, hcl₁] at hrun'
  rw [x10₁] at hT'
  refine ⟨T', (kp_verifyStackedOpening _ _ _ T () T' hrun').trans eT,
    TranscriptAt.same hpre RN.inv ptrg m₂ hT', ?_⟩
  rw [hrun]
  unfold afterRing
  rw [StateT.run_bind]
  erw [hrun']
  rfl

end Vso

end Rv64Verifier.Proofs.Walk
