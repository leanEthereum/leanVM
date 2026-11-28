module

public import NativeRustcVmX64.KeccakGkr.LinearTranspose.Outs

/-!
# `linear_transpose`: an output element (x86-64)

A turn of the output loop (`b17`, `out_step`): region 0 `g`'s element `64 l + z`, region 1 column
`ca l`'s element `z`, region 2 column `cb l` (its element `(z + 1) % 64` loaded at R10's
position), region 3 the output's element `64 l + z`.
-/

namespace NativeRustcVmX64.KeccakGkr.LinearTranspose

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' inRange_off_iff
  Mapped.keeps bytesAt_congr inRange_off_self)

public section

variable {ws : Array EW} {m0 : MachineData} [Host] {k : Nat}

/-- **A turn of the output loop**. -/
theorem out_step (hp : Placed code k) (h : PreOk m0 ws) {l z : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b17Offset)) (hI : OutHead m0 ws l z st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (z + 1 < 64 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b17Offset) ∧
      OutHead m0 ws l (z + 1) s'.data) ∨ (z + 1 = 64 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b18Offset) ∧
      OutLane m0 ws l s'.data ∧ ElemsAt s'.data.dmem (oA m0) (oF ws) (64 * l + 64))) st := by
  have hl := hI.lane.regs.l_lt
  have hz := hI.z_lt
  have hca := ca_lt l
  have hcb := cb_lt l
  have hab := ca_ne_cb l
  have hgn := h.gn; have hcn := h.cn; have hon := h.on
  have hgc := h.gc; have hgo := h.go; have hco := h.co
  set ge := off (gA m0) (1024 * l + 16 * z) with hge
  set ae := off (cA m0) (1024 * ca l + 16 * z) with hae
  set bc := off (cA m0) (1024 * cb l) with hbc
  set oe := off (oA m0) (1024 * l + 16 * z) with hoe
  have hgen : ge.toNat = (gA m0).toNat + (1024 * l + 16 * z) := toNat_off (by omega)
  have haen : ae.toNat = (cA m0).toNat + (1024 * ca l + 16 * z) := toNat_off (by omega)
  have hbcn : bc.toNat = (cA m0).toNat + 1024 * cb l := toNat_off (by omega)
  have hoen : oe.toNat = (oA m0).toNat + (1024 * l + 16 * z) := toNat_off (by omega)
  have hk := hI.lane.regs.ctx.frame.kept
  have hwf : (Env.ofMachine st.data [(ge, 16), (ae, 16), (bc, 1024), (oe, 16)] (fun _ ↦ 0) 0).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (mapped_off h.gM (by omega)) hk, by show ge.toNat + 16 ≤ _; omega⟩,
      ⟨Mapped.keeps (mapped_off h.cM (by omega)) hk, by show ae.toNat + 16 ≤ _; omega⟩,
      ⟨Mapped.keeps (mapped_off h.cM (by omega)) hk, by show bc.toNat + 1024 ≤ _; omega⟩,
      ⟨Mapped.keeps (mapped_off h.oM (by omega)) hk, by show oe.toNat + 16 ≤ _; omega⟩, trivial⟩
      (by
        refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_pair.mpr ?_))
        · intro b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl
          · show ge.toNat + 16 ≤ ae.toNat ∨ ae.toNat + 16 ≤ ge.toNat; omega
          · show ge.toNat + 16 ≤ bc.toNat ∨ bc.toNat + 1024 ≤ ge.toNat; omega
          · show ge.toNat + 16 ≤ oe.toNat ∨ oe.toNat + 16 ≤ ge.toNat; omega
        · intro b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · show ae.toNat + 16 ≤ bc.toNat ∨ bc.toNat + 1024 ≤ ae.toNat; omega
          · show ae.toNat + 16 ≤ oe.toNat ∨ oe.toNat + 16 ≤ ae.toNat; omega
        · show bc.toNat + 1024 ≤ oe.toNat ∨ oe.toNat + 16 ≤ bc.toNat; omega)
  set env := Env.ofMachine st.data [(ge, 16), (ae, 16), (bc, 1024), (oe, 16)] (fun _ ↦ 0) 0
    with henv
  have hr10 : ((Sym.reg .r10).eval env).toNat = z + 1 := by
    show (reg st.data .r10).toNat = _; rw [hI.r10, toNat_ofNat_lt (by omega)]
  have hp3 := posS_eval env (.reg .r10) (by rw [hr10]; omega)
  rw [hr10] at hp3
  have hr11 : reg st.data .r11 = BitVec.ofNat 64 (16 * z) := hI.r11
  have hm : Match env outS st.data :=
    match_ofMachine ⟨rfl, rfl, rfl, rfl, trivial⟩
      ⟨by show reg st.data .rdx = bc + BitVec.ofInt 64 0
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; exact hI.rdx, trivial⟩
      trivial ⟨by show ((posS (.reg .r10)).eval env).toNat < 1009; rw [hp3]; omega, trivial⟩
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [show env.regs .r15 = _ from hI.lane.regs.r15, show env.regs .r11 = _ from hr11,
          show env.base 0 = ge from rfl, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, hge,
          NativeRustcVm.Transcript.off_add, NativeRustcVm.Transcript.off_add]
        congr 1; omega,
       by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [show env.regs .rax = _ from hI.rax, show env.regs .r11 = _ from hr11,
          show env.base 1 = ae from rfl, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, hae,
          NativeRustcVm.Transcript.off_add, NativeRustcVm.Transcript.off_add]
        congr 1; omega,
       by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [show env.regs .rbx = _ from hI.lane.regs.rbx, show env.regs .r11 = _ from hr11,
          show env.base 3 = oe from rfl, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, hoe,
          NativeRustcVm.Transcript.off_add, NativeRustcVm.Transcript.off_add]
        congr 1; omega, trivial⟩
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) exit_b17 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hrsp, hat, hrdx', hr11', hr10', hws, hw⟩ := ok_b17
  have hso : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange oe 16) :=
    sameOutside_region hwf hm' (r := 3) rfl hws
  have hoeo : ∀ q, NativeRustcVm.InRange oe 16 q → NativeRustcVm.InRange (oA m0) 25600 q :=
    fun q hq ↦ off_in (by unfold NativeRustcVm.NoWrap; omega) (by omega) hq
  have hc : OCtx m0 st'.data :=
    ⟨Frame.keep hI.lane.regs.ctx.frame (hm'.kept hwf) (hm'.regs .rsp _ hrsp) hso
      (fun q hq ↦ not_frame h.st h.on h.oS (le_refl _) (hoeo q hq)) (frame_nw h),
      fun q hq ↦ by
        rw [hso q fun h' ↦ hq (Or.inr (Or.inr (Or.inl (hoeo q h'))))]
        exact hI.lane.regs.ctx.same q hq,
      (atoms_eq hm' hat (by simp)).trans hI.lane.regs.ctx.r14⟩
  -- the element
  have eg := NativeRustcVm.ewAt_iff.mp (hI.lane.g (64 * l + z) (by omega))
  have ea := NativeRustcVm.ewAt_iff.mp (hI.lane.c (64 * ca l + z) (by omega))
  have eb := NativeRustcVm.ewAt_iff.mp (hI.lane.c (64 * cb l + (z + 1) % 64)
    (by have := Nat.mod_lt (z + 1) (show 64 > 0 by decide); omega))
  have l0 : ∀ d < 2, env.load 0 (8 * d) 8 = (if d = 0 then (gF ws (64 * l + z)).c0
      else (gF ws (64 * l + z)).c1).toBitVec := by
    intro d hd
    refine load_of_wordAt ?_
    show NativeRustcVm.WordAt st.data.dmem (off ge (8 * d)) _
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · rw [hge, off_off, show 1024 * l + 16 * z + 8 * 0 = 16 * (64 * l + z) by omega]; exact eg.1
    · rw [hge, off_off, show 1024 * l + 16 * z + 8 * 1 = 16 * (64 * l + z) + 8 by omega, ← off_off]
      exact eg.2
  have l1 : ∀ d < 2, env.load 1 (8 * d) 8 = (if d = 0 then (cF ws (64 * ca l + z)).c0
      else (cF ws (64 * ca l + z)).c1).toBitVec := by
    intro d hd
    refine load_of_wordAt ?_
    show NativeRustcVm.WordAt st.data.dmem (off ae (8 * d)) _
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · rw [hae, off_off, show 1024 * ca l + 16 * z + 8 * 0 = 16 * (64 * ca l + z) by omega]; exact ea.1
    · rw [hae, off_off, show 1024 * ca l + 16 * z + 8 * 1 = 16 * (64 * ca l + z) + 8 by omega,
        ← off_off]
      exact ea.2
  have l2 : ∀ d < 2, env.load 2 (8 * d + 16 * ((z + 1) % 64)) 8 =
      (if d = 0 then (cF ws (64 * cb l + (z + 1) % 64)).c0
        else (cF ws (64 * cb l + (z + 1) % 64)).c1).toBitVec := by
    intro d hd
    refine load_of_wordAt ?_
    show NativeRustcVm.WordAt st.data.dmem (off bc (8 * d + 16 * ((z + 1) % 64))) _
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · rw [hbc, off_off, show 1024 * cb l + (8 * 0 + 16 * ((z + 1) % 64)) =
        16 * (64 * cb l + (z + 1) % 64) by omega]; exact eb.1
    · rw [hbc, off_off, show 1024 * cb l + (8 * 1 + 16 * ((z + 1) % 64)) =
        16 * (64 * cb l + (z + 1) % 64) + 8 by omega, ← off_off]; exact eb.2
  have hel := Match.ewAt_write hm' (r := 3) (o := 0) (v0 := outW 0) (v1 := outW 8) rfl (by decide)
    (fun t ht ↦ by rw [Nat.zero_add]; exact (hw t ht).1) (fun t ht ↦ by
      rw [show 0 + 8 + t = 8 + t by omega]; exact (hw t ht).2)
  rw [off_zero] at hel
  simp only [outW, Sym.eval, BinOp.apply, low_W64, ext_W64] at hel
  have hi3 : (Sym.eval env i3S).toNat = 16 * ((z + 1) % 64) := hp3
  have l00 := l0 0 (by decide); have l01 := l0 1 (by decide)
  have l10 := l1 0 (by decide); have l11 := l1 1 (by decide)
  have l20 := l2 0 (by decide); have l21 := l2 1 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add] at l00 l01 l10 l11 l20 l21
  rw [hi3, Nat.zero_add, l00, l01, l10, l11, l20, l21] at hel
  simp only [ite_true, show (1 : Nat) = 0 ↔ False by decide, ite_false] at hel
  rw [out_ew, ← oF_eq ws hz] at hel
  have ho' : ElemsAt st'.data.dmem (oA m0) (oF ws) (64 * l + (z + 1)) := by
    rw [show 64 * l + (z + 1) = (64 * l + z) + 1 by omega]
    refine ElemsAt.grow hI.o (by omega) (by
      rw [show 16 * (64 * l + z) = 1024 * l + 16 * z by omega, show 16 * 1 = 16 from rfl]
      exact hso) fun j hj ↦ ?_
    rw [show j = 0 by omega, Nat.add_zero, show 16 * (64 * l + z) = 1024 * l + 16 * z by omega]
    exact hel
  have hkeep : ∀ {a : BitVec 64} {N : Nat} {f : Nat → EW} {n : Nat},
      ElemsAt st.data.dmem a f n → a.toNat + 16 * n ≤ 2 ^ 64 →
      (a.toNat + 16 * n ≤ (oA m0).toNat ∨ (oA m0).toNat + 25600 ≤ a.toNat) →
      ElemsAt st'.data.dmem a f n := fun he han hap ↦
    he.keep hso (fun q hq hq' ↦ by
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hoen] at hq'
      omega) (by unfold NativeRustcVm.NoWrap; omega)
  have hg' := hkeep (N := 0) hI.lane.g (by omega) (by omega)
  have hc' := hkeep (N := 0) hI.lane.c (by omega) (by omega)
  have hregs : OutRegs m0 l st'.data := hI.lane.regs.keep hc fun r hr ↦ atoms_eq hm' hat (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have hol : ElemsAt st'.data.dmem (oA m0) (oF ws) (64 * l) := fun i hi ↦ ho' i (by omega)
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64] at hpc'
  rw [show env.regs .r11 = _ from hr11, add_ofNat', beq_ofNat (by omega) (by omega)] at hpc'
  by_cases hlast : z + 1 = 64
  · rw [decide_eq_true (show 16 + 16 * z = 1024 by omega)] at hpc'
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    refine .done _ (Or.inr ⟨hlast, hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LinearTranspose.b17_next),
      ⟨hregs, hg', hc', hol⟩, ?_⟩)
    rw [show 64 * l + 64 = 64 * l + (z + 1) by omega]; exact ho'
  · rw [decide_eq_false (show ¬16 + 16 * z = 1024 by omega)] at hpc'
    simp only [Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨by omega, hpc'.trans (label_of_infix hp b17_in_code rfl),
      ⟨⟨hregs, hg', hc', hol⟩, by omega, ?_, ?_, (atoms_eq hm' hat (by simp)).trans hI.rax,
        (hm'.regs .rdx _ hrdx').trans (by
          show bc + BitVec.ofInt 64 0 = _
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]), ho'⟩⟩)
    · rw [show reg st'.data .r10 = _ from hm'.regs .r10 _ hr10']
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [show env.regs .r10 = _ from hI.r10, add_ofNat']
    · rw [show reg st'.data .r11 = _ from hm'.regs .r11 _ hr11']
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [show env.regs .r11 = _ from hr11, add_ofNat']
      congr 1; omega

end

end NativeRustcVmX64.KeccakGkr.LinearTranspose
