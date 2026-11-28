module

public import NativeRustcVmX64.Ring.Target.Loop
public import NativeRustcVmX64.Ring.Target.ChainA
public import NativeRustcVmX64.Ring.Target.ChainB
public import NativeRustcVmX64.Ring.Target.ChainC
public import NativeRustcVmX64.Ring.Target.ChainD
public import NativeRustcVmX64.Ring.Target.Model
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.RingPsi.Names
public import NativeRustcVmX64.Code.Vm.RingTarget.Names

/-!
# `ring_target` on x86-64

**`ringTarget_spec`**: rustc's `ring_target(s, f, g)`, placed anywhere in the program, given the
contracts of `ring_psi`, `memcpy`, `EW::sq_iter`, `poly_eval` and `EW::mul`, returns
`ringTarget s f g`. The prologue (`b0`), the images loop (`b1`, `b2`: `Ψ(s_i)` stored at the frame's
offset `256`), their copy to the offset `1280` (`b3`, `memcpy`), then the layout of the turns
(`switch`), the turns `p = 7 … 0` and the products (`b4` to `b35`, `chainA` to `chainD`, over the
table `tab`), the sum returned (`b36`, `final`).
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingTarget
open NativeRustcVmX64.Transcript (after)

public section

variable {m0 : MachineData}

/-- A contract with a fact of the entry carried to the end. -/
theorem spec_and [Host] {e : Int64} {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (h : Spec e P Q) (R : MachineData → Prop) :
    Spec e (fun m ↦ P m ∧ R m) (fun m m' ↦ Q m m' ∧ R m) :=
  fun m ⟨hp, hr⟩ ↦ (h m hp).mono fun _ h ↦ ⟨h.1, h.2.1, h.2.2, hr⟩

/-- The links' values, evaluated: what `rfl` closes. -/
macro "ltac" : tactic => `(tactic|
  (simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval, pushL]
   and_intros
   all_goals (first | rfl | exact fun _ h ↦ nomatch h)))

/-- **The turns' layout**, after the copy. -/
theorem switch [Labels] {E : Nat → EW} {d : MachineData}
    (hB : Bnd m0 2352 NT (rsL m0) noWr t4L (vL m0) d) :
    Bnd m0 2352 NT (rsC m0) noWr t4 (v4 m0 E) d :=
  ⟨fun ret ↦ match_links (hB.mt 0) (by decide) rfl rfl (fun _ ↦ rfl) rfl rfl rfl (by ltac) rfl
      (regions_envS rfl) rfl (fun _ _ h ↦ by cases h) (keyOk rfl rfl),
    fun q hq ↦ hB.same q fun h ↦ hq (h.elim .inl fun ⟨_, _, hw, _⟩ ↦ by cases hw),
    hB.kept⟩

theorem eval_ptr0n [Labels] {m : MachineData} {F : Nat} {rs : List (BitVec 64 × Nat)}
    {vals : Nat → BitVec 64} {ret : BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (envS m0 m F rs vals ret) = stackBelow m0 F + BitVec.ofNat 64 o := by
  show stackBelow m0 F + BitVec.ofInt 64 (o : Int) = _
  rw [BitVec.ofInt_natCast]

variable [Host] {k : Nat}

/-- **`ring_target` meets its contract.** -/
theorem ringTarget_spec (hp : Placed code k)
    (hpsi : Spec (Labels.label NativeRustcVmX64.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (hpoly : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.RingTarget.entryLabel) RingTargetPre RingTargetPost := by
  intro m0 hpre
  have g := geoT hpre
  have hb := g.base
  have hs : 2576 ≤ (rspOf m0).toNat := g.sp
  have ht := g.top
  set fb := stackBelow m0 2352 with hfb
  rw [show Labels.label NativeRustcVmX64.Vm.RingTarget.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.RingTarget.b0Offset) from hp.label NativeRustcVmX64.Vm.RingTarget.entry_at]
  -- `b0`: the prologue.
  have h0 : Bnd m0 2352 NT (rsL m0) noWr t0L (vL m0) m0 :=
    start rfl fun ret ↦ ⟨(Field.frame_rsp 2352 0).trans (BitVec.add_zero _) |>.symm, by
      show reg m0 .rdi = sA m0 + BitVec.ofInt 64 0
      simp, trivial⟩
  refine jumpStep (layL hpre) h0 (b0_in_code.trans hp.1 (by simp [b0])) run_b0
    (fun _ h ↦ by cases h) rfl (T' := H 0) rfl rfl (vals' := vL m0) (fun ret ↦ by ltac) rfl rfl rfl
    (fun _ _ ↦ noKeys rfl) (fun _ _ _ _ h ↦ by cases h) fun st hpc hB _ ↦ ?_
  -- The images loop.
  refine Eventually.bind (loop hp hpre hpsi 63 0 rfl ⟨hpc, hB, NativeRustcVm.ewsAt_nil _ _⟩)
    fun st ⟨hpc1, hB1, hLI⟩ ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc1 hB1 hLI
  subst hpc1
  let rsG := rsL m0 ++ [(gotAddr "memcpy", 8)]
  have hgot := hpre.2.2.2.2
  have hgotL : GotAt m0 NT (rsL m0) ["memcpy"] :=
    hgot.areas (by
      intro a ha
      simp only [rsL, List.mem_singleton] at ha
      subst a
      exact List.mem_cons_self)
  have hlayG : Lay m0 2352 NT rsG := (layL hpre).withGot hgotL
  have hcopyBase : Bnd m0 2352 NT rsG noWr copyBase (vL m0) d :=
    hB1.relayout (by decide) rfl rfl (fun ret => by ltac) rfl rfl rfl
      (fun _ _ _ h => by cases h)
      (fun _ x r o hx => by
        change [(.gotSlot "memcpy", 2, (0 : Int))].lookup x = some (r, o) at hx
        simp only [List.lookup] at hx
        split at hx
        · rename_i heq
          rw [beq_iff_eq] at heq
          subst heq
          cases hx
          simp [Sym.eval, Env.base, envS, rsG, gotAddr]
        · cases hx)
      (fun _ ⟨_, _, hw, _⟩ => by cases hw)
  have hcopy : Bnd m0 2352 NT rsG noWr copyS (vL m0) d := by
    apply hcopyBase.withKnownBytes
    intro ret i hi
    have hsame := hgotL.unchanged hpre.1
      (by intro a ha; simp only [rsL, List.mem_singleton] at ha; subst a; exact hpre.2.1.1.2)
      (fun q hq => hB1.same q (fun h => hq (h.elim Or.inl
        (fun ⟨_, _, hw, _⟩ => by cases hw))))
    simpa [envS, rsG, rsL, Env.base, Sym.eval, Nat.zero_add] using
      (hsame "memcpy" (by simp) i hi).trans (hgotL.byte (by simp) hi)
  -- `b3`: their copy.
  let R : MachineData → Prop := fun m ↦ reg m .rdi = fb + BitVec.ofNat 64 1280 ∧
    reg m .rsi = fb + BitVec.ofNat 64 256 ∧ reg m .rdx = BitVec.ofNat 64 1024
  have hmiss3 : missOk 8 2304 (after b3 copyS) = true := by
    rw [NativeRustcVmX64.Transcript.after_eq run_b3]; decide
  have hW : ∀ q, NativeRustcVm.InRange (fb + BitVec.ofNat 64 1280) 1024 q →
      NativeRustcVm.InRange fb 2352 q := fun q h ↦ by
    have hq : (fb + BitVec.ofNat 64 1280).toNat = (rspOf m0).toNat - 2352 + 1280 :=
      g.addr (by omega)
    rw [NativeRustcVm.Transcript.inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hq]; omega), hq] at h
    rw [NativeRustcVm.Transcript.inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hb]; omega), hb]
    omega
  refine callStep hlayG hcopy (b3_in_code.trans hp.1 (by simp [b3])) run_b3 rfl rfl
    (spec_and hmemcpy R) (S := 0) (by decide) (fun mc hm hk hst ↦ ?_)
    (W := NativeRustcVm.InRange (fb + BitVec.ofNat 64 1280) 1024)
    (fun m m' ⟨hq, hr⟩ ↦ ⟨fun q hq' ↦ hq.2.2.1 q fun h ↦ hq' (.inr (by
      rw [hr.1, hr.2.2] at h; exact h)), hq.2.2.2⟩)
    (fun q h ↦ .inl (frame_in hpre.1 (by decide) (hW q h))) (T' := copiedS) (vals' := vL m0) rfl rfl
    (fun ret ↦ by ltac) (fun _ hi ↦ by cases hi) (fun _ hi ↦ by cases hi)
    (fun mc ret r b sz j v t hb' hj hf h' ↦ ?_) rfl rfl rfl (fun _ _ ↦ noKeys rfl)
    (fun _ _ _ _ h ↦ by cases h) fun st hpc hB2 ⟨mc, hm, hsp, hq, hr⟩ ↦ ?_
  · -- `memcpy`'s precondition.
    have hsp : rspOf mc = fb := by
      show mc.regs.get64 .rsp = _
      rw [hm.regs .rsp _ rfl]
      show stackBelow m0 2352 + BitVec.ofInt 64 0 = stackBelow m0 2352
      simp
    have r1 : reg mc .rdi = fb + BitVec.ofNat 64 1280 := regv hm rfl (eval_ptr0n 1280)
    have r2 : reg mc .rsi = fb + BitVec.ofNat 64 256 := regv hm rfl (eval_ptr0n 256)
    have r3 : reg mc .rdx = BitVec.ofNat 64 1024 := regv hm rfl rfl
    have hq1 : (fb + BitVec.ofNat 64 1280).toNat = (rspOf m0).toNat - 2352 + 1280 := g.addr (by omega)
    have hq2 : (fb + BitVec.ofNat 64 256).toNat = (rspOf m0).toNat - 2352 + 256 := g.addr (by omega)
    have hfm := NativeRustcVmX64.Transcript.frame_mapped (F := 2352) hpre.1 (by decide)
    refine ⟨⟨hst, ?_, ?_, ?_, ?_, ?_, ?_⟩, r1, r2, r3⟩ <;>
      simp only [r1, r2, r3, show (BitVec.ofNat 64 1024).toNat = 1024 from rfl]
    · exact fun i hi ↦ hk _ (by rw [NativeRustcVm.addr_add]; exact hfm _ (by omega))
    · exact fun i hi ↦ hk _ (by rw [NativeRustcVm.addr_add]; exact hfm _ (by omega))
    · unfold NoWrap; rw [hq1]; omega
    · unfold NoWrap; rw [hq2]; omega
    · unfold Apart; rw [hq1, hq2]; omega
    · unfold Apart; rw [hq1, hsp, hb]; omega
  · -- The pushes are not in the copy.
    obtain ⟨w, hwm, hwr, h1, h2, -, -⟩ := findWrite_spec hf
    simp only [copiedS, tpl, pushW, List.mem_cons, List.not_mem_nil, or_false] at hwm
    have hr0 : r = 0 := by
      rcases hwm with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hwr.symm
    subst hr0
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    have hj' : 2304 ≤ j := by rcases hwm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h1 <;> omega
    have hq1 : (fb + BitVec.ofNat 64 1280).toNat = (rspOf m0).toNat - 2352 + 1280 := g.addr (by omega)
    rw [NativeRustcVm.Transcript.inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hq1]; omega), hq1, g.addr (by omega)] at h'
    omega
  -- The copy, the turns' layout.
  obtain ⟨d', pc'⟩ := st
  simp only at hpc hB2
  subst hpc
  have hmc : NativeRustcVm.EWsAt mc.dmem (fb + BitVec.ofNat 64 256) (imgs m0).toList := by
    have := bytes_block g (hlayG.wf hB1.kept) hmiss3 (by decide) hm hLI (a := 256) (by decide)
      (by rw [NativeRustcVm.length_ewsBytes, List.length_take, Array.length_toList, imgs_size]; omega)
    rwa [List.take_of_length_le (by rw [Array.length_toList, imgs_size])] at this
  have hC : CAt m0 d' := by
    have h := hq.2.1
    rw [hr.1, hr.2.1, hr.2.2, show (BitVec.ofNat 64 1024).toNat =
      ((imgs m0).toList.flatMap NativeRustcVm.ewBytes).length by
        rw [NativeRustcVm.length_ewsBytes, Array.length_toList, imgs_size]; rfl,
      bytesOf_eq hmc] at h
    exact h
  have hB2' : Bnd m0 2352 NT (rsL m0) noWr t4L (vL m0) d' :=
    hB2.relayout (by decide) rfl rfl (fun ret => by ltac) rfl rfl rfl
      (fun _ _ _ h => by cases h) (fun _ => noKeys rfl)
      (fun _ ⟨_, _, hw, _⟩ => by cases hw)
  have h4 : At m0 k NativeRustcVmX64.Vm.RingTarget.b4Offset (rsC m0) t4 (v4 m0 (tab m0)) (CAt m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.RingTarget.b4Offset)⟩ :=
    ⟨rfl, switch hB2', hC⟩
  -- The turns.
  refine Eventually.bind (chainA hp hpre hsq hpoly hmul tab_good h4) fun st h ↦ ?_
  refine Eventually.bind (chainB hp hpre hsq hpoly hmul tab_good h) fun st h ↦ ?_
  refine Eventually.bind (chainC hp hpre hsq hpoly hmul tab_good h) fun st h ↦ ?_
  refine Eventually.bind (chainD hp hpre hsq hpoly hmul tab_good h) fun st h ↦ ?_
  -- `b36`: the sum returned.
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB, -⟩ := h
  simp only at hpc hB
  subst hpc
  refine exitStep (layC hpre) hB (b36_in_code.trans hp.1 (by simp [b36])) run_b36 rfl rfl
    (fun r hr ↦ by cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr <;>
      exact ⟨_, rfl, rfl⟩) fun st hm hret hrsp hso hsv ↦ .done _ ⟨hret, hrsp, ?_, ?_, hsv⟩
  · have e0 : reg st.data .rax = c0 (tab m0 40) ^^^ X0 (tab m0) := by
      rw [show reg st.data .rax = _ from hm.regs .rax _ rfl]
      simp only [Sym.eval, Field.Lin.xor_apply]
      rfl
    have e1 : reg st.data .rdx = c1 (tab m0 40) ^^^ X1 (tab m0) := by
      rw [show reg st.data .rdx = _ from hm.regs .rdx _ rfl]
      simp only [Sym.eval, Field.Lin.xor_apply]
      rfl
    show ewArg (reg st.data .rax) (reg st.data .rdx) = ringTarget (sl m0) (fl m0) (gl m0)
    rw [e0, e1]
    exact final tab_good
  · intro q hq
    exact hso q fun h ↦ hq (h.elim .inr fun ⟨_, _, hw, _⟩ ↦ by cases hw)

end

end NativeRustcVmX64.Ring.Target
