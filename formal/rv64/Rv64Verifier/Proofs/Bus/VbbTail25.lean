import Rv64Verifier.Proofs.Bus.VbbTail24

/-!
# `verify_bus_balance` past the GKR loop: the sides' array

From `0x8000737c` one block writes the three sides' tuples, 88 bytes apart from `S - 592` (the
framework fingerprints' `Vec`, the blocks' pointer and length, the `BusLayout`'s address, the
weights' pointer and length, `beta`'s limbs; the count side's fingerprints empty, its weights the
`ONE` at `0xa00000b0`, its `beta` zero), the sides' range `0..3` at `S - 608`, `layout.tables`'
buffer at `S - 1240` and the forms' count at `S - 1232`, then enters the side loop at `0x800074e0`
with the side `0` in `s6` (`setupStep`, `Setup`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the block writes in the frame. -/
def SetupW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 608) 288 ∨ Within a (s.getReg .x2 - 1240) 16

theorem SetupW.frameW {s : MachineState} (hpre : BusBalancePre s) : FrameW s (SetupW s) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha
  rcases ha with ha | ha <;> addr_omega [ha, hb1]

/-- The words the block writes, at `S - K`, from `v`'s. -/
def setupWords (s v : MachineState) : List (Nat × Word) :=
  [(608, 0), (600, 3), (592, v.getMem (s.getReg .x2 - 656)), (584, v.getMem (s.getReg .x2 - 648)),
    (576, v.getMem (s.getReg .x2 - 640)), (568, v.getMem (s.getReg .x2 - 1272)),
    (560, v.getMem (s.getReg .x2 - 1264)), (552, s.getReg .x2 - 1080), (544, v.getReg .x20),
    (536, v.getReg .x21), (528, v.getMem (s.getReg .x2 - 1192)),
    (520, v.getMem (s.getReg .x2 - 1200)), (512, v.getMem (s.getReg .x2 - 1184)),
    (504, v.getMem (s.getReg .x2 - 680)), (496, v.getMem (s.getReg .x2 - 672)),
    (488, v.getMem (s.getReg .x2 - 664)), (480, v.getMem (s.getReg .x2 - 1168)),
    (472, v.getMem (s.getReg .x2 - 1176)), (464, s.getReg .x2 - 1024), (456, v.getReg .x8),
    (448, v.getReg .x22), (440, v.getMem (s.getReg .x2 - 1192)),
    (432, v.getMem (s.getReg .x2 - 1200)), (424, v.getMem (s.getReg .x2 - 1184)), (416, 0),
    (408, 8), (400, 0), (392, v.getMem (s.getReg .x2 - 1160)),
    (384, v.getMem (s.getReg .x2 - 1248)), (376, s.getReg .x2 - 968), (368, 0xa00000b0), (360, 1),
    (352, 0), (344, 0), (336, 0), (328, 0), (1232, v.getReg .x25),
    (1240, v.getMem (v.getMem (s.getReg .x2 - 1240) + 8))]

/-- At the side loop's head for the first side. -/
structure Setup (s v h : MachineState) : Prop where
  inv : Inv s h
  step : StepS s v h (SetupW s)
  regs : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27] : List Reg),
    h.getReg r = v.getReg r
  x22 : h.getReg .x22 = 0
  words : ∀ p ∈ setupWords s v, h.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = p.2

theorem setupStep {s v : MachineState} (hpre : BusBalancePre s) (I : Inv s v)
    (hlay : v.getMem (s.getReg .x2 - 1240) = s.getReg .x11) (hpc : v.pc = 0x8000737c) :
    ∃ h, Reaches Image.code v h ∧ h.pc = 0x800074e0 ∧ Setup s v h := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have spv : v.getReg .x2 = s.getReg .x2 - 1344 := I.sp
  have rd (j : Nat) (hj : j + 8 ≤ 1344) : v.getMem (v.getReg .x2 + BitVec.ofNat 64 j) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 (1344 - j)) :=
    congrArg v.getMem (by rw [spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj])
  have hl := hpre.layout
  have hR' : Region (s.getReg .x11) 168 := by
    rcases hl.region with h0 | h0
    · exact absurd h0 (by decide)
    · exact h0
  have hRm := hR'
  simp only [Region, Mapped] at hRm
  have hls := hl.stack
  rw [stackLo_eq, stack_eq] at hls
  have hlay' : v.getMem (v.getReg .x2 + 104) = s.getReg .x11 := (rd 104 (by omega)).trans hlay
  obtain ⟨h, hrh, hh⟩ := Sym.BlockSpec.reaches b8000737c_spec hpc (by
    rv_eval [spv, hlay', hlay]
    and_intros <;> first
      | valid_access hval [hb1]
      | exact Region.valid hR' (by addr_omega [hRm]) (by addr_omega [hRm]) (by addr_omega [hRm])
      | addr_omega [hRm, hls, hb1])
  have k₁ := b8000737c_keeps hh
  have fr : DFrame v h (SetupW s) := fun a ha ↦ hh.frame a (by
    rv_eval [spv, hlay', hlay]
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]
      first | exact Or.inl (by addr_omega [hb1]) | exact Or.inr (by addr_omega [hb1])))
  have st : StepS s v h (SetupW s) :=
    StepS.ofDFrame I.heap fr (fun _ ha ↦ ha)
      (fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1])
      (k₁ .x2 (by decide))
  refine ⟨h, hrh, b8000737c_pc hh, I.afterR hpre (SetupW.frameW hpre) st.toR, st,
    fun r hr ↦ k₁ r (mem_of_mem hr _), b8000737c_x22 hh, ?_⟩
  intro p hp
  simp only [setupWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slotOf hpre spv (j := 736) (by omega) (b8000737c_m_x2_736 hh)
  · exact slotOf hpre spv (j := 744) (by omega) (b8000737c_m_x2_744 hh)
  · exact (slotOf hpre spv (j := 752) (by omega) (b8000737c_m_x2_752 hh)).trans (rd 688 (by omega))
  · exact (slotOf hpre spv (j := 760) (by omega) (b8000737c_m_x2_760 hh)).trans (rd 696 (by omega))
  · exact (slotOf hpre spv (j := 768) (by omega) (b8000737c_m_x2_768 hh)).trans (rd 704 (by omega))
  · exact (slotOf hpre spv (j := 776) (by omega) (b8000737c_m_x2_776 hh)).trans (rd 72 (by omega))
  · exact (slotOf hpre spv (j := 784) (by omega) (b8000737c_m_x2_784 hh)).trans (rd 80 (by omega))
  · rw [slotOf hpre spv (j := 792) (by omega) (b8000737c_m_x2_792 hh), spv]
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · exact slotOf hpre spv (j := 800) (by omega) (b8000737c_m_x2_800 hh)
  · exact slotOf hpre spv (j := 808) (by omega) (b8000737c_m_x2_808 hh)
  · exact (slotOf hpre spv (j := 816) (by omega) (b8000737c_m_x2_816 hh)).trans (rd 152 (by omega))
  · exact (slotOf hpre spv (j := 824) (by omega) (b8000737c_m_x2_824 hh)).trans (rd 144 (by omega))
  · exact (slotOf hpre spv (j := 832) (by omega) (b8000737c_m_x2_832 hh)).trans (rd 160 (by omega))
  · exact (slotOf hpre spv (j := 840) (by omega) (b8000737c_m_x2_840 hh)).trans (rd 664 (by omega))
  · exact (slotOf hpre spv (j := 848) (by omega) (b8000737c_m_x2_848 hh)).trans (rd 672 (by omega))
  · exact (slotOf hpre spv (j := 856) (by omega) (b8000737c_m_x2_856 hh)).trans (rd 680 (by omega))
  · exact (slotOf hpre spv (j := 864) (by omega) (b8000737c_m_x2_864 hh)).trans (rd 176 (by omega))
  · exact (slotOf hpre spv (j := 872) (by omega) (b8000737c_m_x2_872 hh)).trans (rd 168 (by omega))
  · rw [slotOf hpre spv (j := 880) (by omega) (b8000737c_m_x2_880 hh), spv]
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · exact slotOf hpre spv (j := 888) (by omega) (b8000737c_m_x2_888 hh)
  · exact slotOf hpre spv (j := 896) (by omega) (b8000737c_m_x2_896 hh)
  · exact (slotOf hpre spv (j := 904) (by omega) (b8000737c_m_x2_904 hh)).trans (rd 152 (by omega))
  · exact (slotOf hpre spv (j := 912) (by omega) (b8000737c_m_x2_912 hh)).trans (rd 144 (by omega))
  · exact (slotOf hpre spv (j := 920) (by omega) (b8000737c_m_x2_920 hh)).trans (rd 160 (by omega))
  · exact slotOf hpre spv (j := 928) (by omega) (b8000737c_m_x2_928 hh)
  · exact slotOf hpre spv (j := 936) (by omega) (b8000737c_m_x2_936 hh)
  · exact slotOf hpre spv (j := 944) (by omega) (b8000737c_m_x2_944 hh)
  · exact (slotOf hpre spv (j := 952) (by omega) (b8000737c_m_x2_952 hh)).trans (rd 184 (by omega))
  · exact (slotOf hpre spv (j := 960) (by omega) (b8000737c_m_x2_960 hh)).trans (rd 96 (by omega))
  · rw [slotOf hpre spv (j := 968) (by omega) (b8000737c_m_x2_968 hh), spv]
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · exact slotOf hpre spv (j := 976) (by omega) (b8000737c_m_x2_976 hh)
  · exact slotOf hpre spv (j := 984) (by omega) (b8000737c_m_x2_984 hh)
  · exact slotOf hpre spv (j := 992) (by omega) (b8000737c_m_x2_992 hh)
  · exact slotOf hpre spv (j := 1000) (by omega) (b8000737c_m_x2_1000 hh)
  · exact slotOf hpre spv (j := 1008) (by omega) (b8000737c_m_x2_1008 hh)
  · exact slotOf hpre spv (j := 1016) (by omega) (b8000737c_m_x2_1016 hh)
  · exact slotOf hpre spv (j := 112) (by omega) (b8000737c_m_x2_112 hh)
  · rw [slotOf hpre spv (j := 104) (by omega) (b8000737c_m_x2_104 hh), hlay', ← hlay]

/-- From `0x80006ca0` to the side loop's head: the rest's stages, the forms' rows, the sides. -/
theorem restToSides (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) (hA : AllocSpec)
    (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hI : IndexMleSpec) (hC : SliceConcatSpec)
    {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E}
    (hB : Vbb.BytecodeEvalSpec BcOk bev) (hBT : BcTransfer BcOk bev)
    (hP : PowSpec) (hF : FingerprintsSpec)
    (hR : ReserveFreshSpec 0x80004aec 24 8) (hCl : Layout.Clone.CloneCapsSpec) {s q : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf : E} (hpre : BusBalancePre s)
    (hbc : BcOk s busBalanceStack (bytecodeOf s (s.getReg .x11)))
    (Sc : Scalars bev s q k state mem mf bf) (hpc : q.pc = 0x80006ca0) :
    ∃ h, Reaches Image.code q h ∧ (Done bev s h ∨ Dead Image.code h ∨
      ∃ z w v bv, Fps bev s z k state mem mf bf bv ∧ Rows0 s z w ∧ Rows1 s z w v ∧
        Kept2 s v k ∧ h.pc = 0x800074e0 ∧ Setup s v h) := by
  obtain ⟨v, hrv, hdone | hd | ⟨z, w, bv, F, R, R1⟩⟩ :=
    restToRows1 hT hM hA hG hI hC hB hBT hP hF hR hCl hpre hbc Sc hpc
  · exact ⟨v, hrv, Or.inl hdone⟩
  · exact ⟨v, hrv, Or.inr (Or.inl hd)⟩
  have K : Kept2 s v k :=
    F.kept.toKept2.step hpre (R1.step.toR.weaken fun _ ha ↦ RowsW.free2 hpre ha)
  obtain ⟨h, hrh, hpch, S⟩ := setupStep hpre R1.inv K.layout R1.pc
  exact ⟨h, hrv.trans hrh, Or.inr (Or.inr ⟨z, w, v, bv, F, R, R1, K, hpch, S⟩)⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
