module

public import NativeRustcX64.WotsLeaf.Chain.Basic
public import NativeRustcX64.SphincsVerify.InlineTh.Final

/-!
# A chain step, part C: the final block and `keccak_f`

From `b42` (directive 448) with hasher B's zero state at `704` and its 64 buffered bytes `T` at
`904`: B's state copied into A's at `112` (`b42`), the block at `472` zeroed (`b44`) and `T`
copied there (`b45`), the padded block XORed into A's state and `keccak_f` (`b46`, by
`InlineTh.xorFinal`), A's first 16 bytes the chain's new value at `80` (`b47`); then the next step
`b17` (directive 191) or, after position 2, `b48` (directive 515) (`seg_b42`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Chain
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **At a chain step** (`b17`): chain `i` at position `p`, its value `cur` at `80`. -/
def Run.AtStep [Labels] (r : Run) (i p : Nat) (cur : List UInt8) (m : MachineData) : Prop :=
  Keep r (r.stepSlots i) m ∧ BytesAt m.dmem (r.off 80) cur ∧
    Run.RegIs m .r14 (BitVec.ofNat 64 p) ∧ Run.RegIs m .rdx (BitVec.ofNat 64 i) ∧
    Run.RegIs m .r12 (r.off 112) ∧
    Run.RegIs m .r13 (Labels.label "memcpy").toBitVec ∧
    Run.RegIs m .rbx (Labels.label "memset").toBitVec

/-- The value a step leaves: `keccak_f` of the padded `T` XORed into the zero state, its first
16 bytes. -/
def stepOut (T : List UInt8) : List UInt8 :=
  (Keccak.keccakF (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T))).take 16

/-- What follows a step of chain `i` from position `p` hashing `T`: from the state after `b47`,
at `b17` for the next step or `b48` after position 2. -/
def StepCont [Host] (r : Run) (i p : Nat) (T : List UInt8) (R : MachineState → Prop) : Prop :=
  ∀ m', r.AtStep i (p + 1) (stepOut T) m' →
    Eventually (step1 Host.exe) R ⟨m', if p + 1 = 3 then r.pc NativeRustcX64.Xmss.WotsLeaf.b48Offset else r.pc NativeRustcX64.Xmss.WotsLeaf.b17Offset⟩

end

public section

/-- The step's slots: `16 i` at `456`, `i` at `464`. -/
theorem stepSlots_words {r : Run} {i : Nat} {m : MachineData} {L : List Slot}
    (h : SlotsAt r m (r.stepSlots i ++ L)) :
    BytesAt m.dmem (r.off 456) (regBytes (BitVec.ofNat 64 (16 * i))) ∧
      BytesAt m.dmem (r.off 464) (regBytes (BitVec.ofNat 64 i)) :=
  ⟨(allOf_right (allOf_left (allOf_left h))).1.2.2, (allOf_right (allOf_left h)).1.2.2⟩

/-- The chains' slots among the step's. -/
theorem stepSlots_chain {r : Run} {i : Nat} {m : MachineData} {L : List Slot}
    (h : SlotsAt r m (r.stepSlots i ++ L)) : SlotsAt r m r.chainSlots :=
  allOf_left (allOf_left (allOf_left (allOf_left h)))

variable [Host] {r : Run}

/-- **`b47`**: A's first 16 bytes the chain's value; the position and the chain reloaded; on to
the next step or, after position 2, `b48`. -/
theorem seg_b47 (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) {i p : Nat} (hp3 : p < 3)
    {A : List UInt8} (hA : A.length = 200) {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))), (112, 200, A)]) m)
    (h12 : Run.RegIs m .r12 (r.off 112))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec)
    (hbx : Run.RegIs m .rbx (Labels.label "memset").toBitVec)
    (cont : ∀ m', r.AtStep i (p + 1) (A.take 16) m' →
      Eventually (step1 Host.exe) R ⟨m', if p + 1 = 3 then r.pc NativeRustcX64.Xmss.WotsLeaf.b48Offset else r.pc NativeRustcX64.Xmss.WotsLeaf.b17Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b47Offset⟩ := by
  obtain ⟨⟨-, -, h56⟩, ⟨-, -, hA112⟩, -⟩ := allOf_right hK.2
  have h464 := (stepSlots_words hK.2).2
  refine frameStep r hp hpre b47_in_code (List.cons_ne_nil _ _) run_b47 (by decide) rfl hK
    trivial extraOK_nil trivial trivial trivial fun st hm hK1 _ hpc ↦ ?_
  have hcur := frame_copy16 hm (o := 80) (o' := 112) (by decide) (by decide +kernel)
    (by decide +kernel) (bs := A.take 16) (by simp [hA]) (take_of_bytesAt hA112 16)
  have h14 : Run.RegIs st.data .r14 (BitVec.ofNat 64 (p + 1)) :=
    regIs_eval hm (v := .load 0 56 8) rfl (r.load_word h56)
  have hdx : Run.RegIs st.data .rdx (BitVec.ofNat 64 i) :=
    regIs_eval hm (v := .load 0 464 8) rfl (r.load_word h464)
  refine pc_at ?_ (cont _ ⟨hK1.left, hcur, h14, hdx, regIs_reg hm rfl h12,
    regIs_reg hm rfl h13, regIs_reg hm rfl hbx⟩)
  rw [pc_cond hpc (b := decide (p + 1 ≠ 3)) ?_, Run.label_of_block r hp b17_in_code rfl]
  · obtain rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    all_goals rfl
  · show (!(CmpOp.apply .eq .W64 ((r.envR m [] _).load 0 56 8) (BitVec.ofNat 64 3))) = _
    rw [r.load_word h56]
    obtain rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    all_goals decide

/-- **`b46`**: the padded block XORed into A's zero state, `keccak_f`; then `b47`. -/
theorem seg_b46 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData}
    (hK : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))),
      (112, 200, List.replicate 200 0), (472, 136, T ++ List.replicate 72 0)]) m)
    (h15 : Run.RegIs m .r15 (BitVec.ofNat 64 64)) (h12 : Run.RegIs m .r12 (r.off 112))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec)
    (hbx : Run.RegIs m .rbx (Labels.label "memset").toBitVec)
    (cont : StepCont r i p T R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b46Offset⟩ := by
  obtain ⟨s56, ⟨-, -, hA0⟩, ⟨-, -, hblk⟩, -⟩ := allOf_right hK.2
  have hK' : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1)))]) m :=
    hK.left.add ⟨s56, trivial⟩
  have hwf := envR_wf hpre hK.1.2.2.2 extraOK_nil (r.pc (NativeRustcX64.Xmss.WotsLeaf.b46Offset + b46.length)).toBitVec
  refine frameCall r hp hpre b46_in_code (List.cons_ne_nil _ _) run_b46 (by decide +kernel) rfl
    hK' trivial extraOK_nil ⟨known_lit h15, known_ptr h12, trivial⟩ trivial trivial hc.2.2.2.2
    fun m₁ hm₁ hK₁ _ ↦ ?_
  have hblk' : BytesAt (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b46Offset + b46.length)).toBitVec).mem0
      (r.base + BitVec.ofNat 64 472) (T ++ List.replicate (136 - 64) 0) := hblk
  have hxor := SphincsVerifyProof.InlineTh.xorFinal hm₁ hwf (r := 0) (b := r.base) (sz := 2784)
    rfl (oA := 112) (oK := 472) (L := 64) (by decide) (by decide +kernel) hT (by decide) hblk'
  have hz : bytesOf m.dmem (r.off 112) 200 = List.replicate 200 0 := by
    have := bytesOf_of_bytesAt hA0
    rwa [List.length_replicate] at this
  have hst : BytesAt m₁.dmem (r.off 112)
      (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)) := by
    have h : BytesAt m₁.dmem (r.off 112) (Keccak.xorBlock (bytesOf m.dmem (r.off 112) 200)
      (Keccak.finalBlock T)) := hxor
    rwa [hz] at h
  have h12' : Run.RegIs m₁ .r12 (r.off 112) := regIs_ptr hm₁ rfl
  have hl : (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)).length = 200 :=
    Keccak.length_stateBytes _
  obtain ⟨hpre₁, hpost₁⟩ := keccakFrame hpre hK₁ (regIs_ptr hm₁ rfl) (by decide) rfl hl hst
  refine ⟨hpre₁, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hK₂, hS, -, hB⟩ := hpost₁ m₂ hsp hQ
  generalize hA : Keccak.keccakF (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)) = A
    at hB
  have hl' : A.length = 200 := by rw [← hA, Keccak.keccakF, Keccak.length_stateBytes]
  exact seg_b47 hp hpre hp3 hl' (hK₂.add ⟨⟨hl', by norm_num, hB⟩, trivial⟩)
    (RegIs.of_saved hS rfl h12')
    (RegIs.of_saved hS rfl (regIs_reg hm₁ rfl h13))
    (RegIs.of_saved hS rfl (regIs_reg hm₁ rfl hbx))
    fun m' h ↦ cont m' (by rw [stepOut, hA]; exact h)

/-- **`b45`**: B's 64 buffered bytes copied to the zeroed block; then `b46`. -/
theorem seg_b45 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData}
    (hK : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))),
      (112, 200, List.replicate 200 0), (472, 136, List.replicate 136 0), (904, 64, T)]) m)
    (h15 : Run.RegIs m .r15 (BitVec.ofNat 64 64)) (h14 : Run.RegIs m .r14 (r.off 472))
    (h12 : Run.RegIs m .r12 (r.off 112))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec)
    (hbx : Run.RegIs m .rbx (Labels.label "memset").toBitVec) (cont : StepCont r i p T R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b45Offset⟩ := by
  obtain ⟨s56, s112, ⟨-, -, hK0⟩, ⟨-, -, hT904⟩, -⟩ := allOf_right hK.2
  have hz : BytesAt m.dmem (r.off 536) (List.replicate 72 0) := by
    have := BytesAt.sub hK0 64 72
    rwa [List.drop_replicate, List.take_replicate] at this
  have hK' : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))),
      (112, 200, List.replicate 200 0), (536, 72, List.replicate 72 0), (904, 64, T)]) m :=
    hK.left.add ⟨s56, s112, ⟨by simp only [List.length_replicate], by norm_num, hz⟩, ⟨hT, by norm_num, hT904⟩,
      trivial⟩
  refine frameCall r hp hpre b45_in_code (List.cons_ne_nil _ _) run_b45 (by decide) rfl hK'
    trivial extraOK_nil ⟨known_lit h15, known_ptr h14, h13, trivial⟩ trivial trivial hc.1
    fun m₁ hm₁ hK₁ _ ↦ ?_
  obtain ⟨⟨-, -, hT₁⟩, -⟩ := (allOf_right hK₁.2).2.2.2
  obtain ⟨hpre₁, hpost₁⟩ := memcpyFrame hpre hK₁ (regIs_ptr hm₁ rfl) (regIs_ptr hm₁ rfl)
    (toNat_of_lit hm₁ rfl (by decide)) (by decide) (by decide) (by decide) rfl hT hT₁
  refine ⟨hpre₁, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hK₂, hS, -, hB⟩ := hpost₁ m₂ hsp hQ
  obtain ⟨t56, t112, ⟨-, -, hz₂⟩, -⟩ := allOf_right hK₂.2
  exact seg_b46 hp hc hpre hp3 hT
    (hK₂.left.add ⟨t56, t112, ⟨by simp only [List.length_append, List.length_replicate, hT],
      by norm_num, BytesAt.cat hB hz₂ (by rw [hT])⟩, trivial⟩)
    (RegIs.of_saved hS rfl (regIs_lit hm₁ rfl)) (RegIs.of_saved hS rfl (regIs_reg hm₁ rfl h12))
    (RegIs.of_saved hS rfl (hm₁.regs .r13 _ rfl))
    (RegIs.of_saved hS rfl (regIs_reg hm₁ rfl hbx)) cont

/-- **`b42 .. b44`**: B's zero state copied into A, the bound check, the block zeroed; then
`b45`. -/
theorem seg_b42 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData}
    (hK : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))),
      (704, 200, List.replicate 200 0), (904, 64, T)]) m)
    (h15 : Run.RegIs m .r15 (BitVec.ofNat 64 64))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec) (cont : StepCont r i p T R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b42Offset⟩ := by
  -- `b42`: `memcpy` of B's state into A.
  refine frameCall r hp hpre b42_in_code (List.cons_ne_nil _ _) run_b42 (by decide) rfl hK
    trivial extraOK_nil ⟨h13, trivial⟩ trivial trivial hc.1 fun m₁ hm₁ hK₁ _ ↦ ?_
  obtain ⟨s56, ⟨-, -, hB0⟩, s904, -⟩ := allOf_right hK₁.2
  obtain ⟨hpre₁, hpost₁⟩ := memcpyFrame hpre hK₁ (regIs_ptr hm₁ rfl) (regIs_ptr hm₁ rfl)
    (toNat_of_lit hm₁ rfl (by decide)) (by decide) (by decide) (by decide) rfl
    (by simp only [List.length_replicate]) hB0
  refine ⟨hpre₁, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hK₂, hS₂, -, hA0⟩ := hpost₁ m₂ hsp hQ
  obtain ⟨t56, -, t904, -⟩ := allOf_right hK₂.2
  have h12 : Run.RegIs m₂ .r12 (r.off 112) := RegIs.of_saved hS₂ rfl (regIs_ptr hm₁ rfl)
  have h15₂ : Run.RegIs m₂ .r15 (BitVec.ofNat 64 64) :=
    RegIs.of_saved hS₂ rfl (regIs_reg hm₁ rfl h15)
  have h13₂ : Run.RegIs m₂ .r13 (Labels.label "memcpy").toBitVec :=
    RegIs.of_saved hS₂ rfl (hm₁.regs .r13 _ rfl)
  have hK₂' : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))),
      (112, 200, List.replicate 200 0), (904, 64, T)]) m₂ :=
    hK₂.left.add ⟨t56, ⟨by simp only [List.length_replicate], by norm_num, hA0⟩, t904, trivial⟩
  -- `b43`: the bound check.
  refine frameStep r hp hpre b43_in_code (List.cons_ne_nil _ _) run_b43 (by decide) rfl hK₂'
    trivial extraOK_nil ⟨known_lit h15₂, trivial⟩ trivial trivial fun st3 hm3 hK3 _ hpc3 ↦ ?_
  refine pc_at (pc_false hpc3) ?_
  -- `b44`: `memset` of the block.
  refine frameCall r hp hpre b44_in_code (List.cons_ne_nil _ _) run_b44 (by decide) rfl hK3
    trivial extraOK_nil ⟨known_lit (regIs_lit hm3 rfl), known_lit (regIs_lit hm3 rfl), trivial⟩
    trivial trivial hc.2.1
    fun m₄ hm₄ hK₄ _ ↦ ?_
  obtain ⟨hpre₄, hpost₄⟩ := memsetFrame hpre hK₄ (regIs_ptr hm₄ rfl) (byte_zero hm₄ rfl)
    (toNat_of_lit hm₄ rfl (by decide)) (by decide) rfl
  refine ⟨hpre₄, fun m₅ hsp₅ hQ₅ ↦ ?_⟩
  obtain ⟨hK₅, hS₅, -, hZ⟩ := hpost₄ m₅ hsp₅ hQ₅
  obtain ⟨u56, u112, u904, -⟩ := allOf_right hK₅.2
  exact seg_b45 hp hc hpre hp3 hT
    (hK₅.left.add ⟨u56, u112, ⟨by simp only [List.length_replicate], by norm_num, hZ⟩, u904,
      trivial⟩)
    (RegIs.of_saved hS₅ rfl (regIs_lit hm₄ rfl)) (RegIs.of_saved hS₅ rfl (regIs_ptr hm₄ rfl))
    (RegIs.of_saved hS₅ rfl (regIs_reg hm₄ rfl (regIs_reg hm3 rfl h12)))
    (RegIs.of_saved hS₅ rfl (regIs_reg hm₄ rfl (regIs_reg hm3 rfl h13₂)))
    (RegIs.of_saved hS₅ rfl (hm₄.regs .rbx _ rfl)) cont

end

end NativeRustcX64.WotsLeafProof
