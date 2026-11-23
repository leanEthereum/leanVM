module

public import NativeRustcVmX64.Whir.SubspaceAtTable.Exec
public import NativeRustcVmX64.Whir.SubspaceAtTable.Leaf
public import NativeRustcVm.Whir.MathSubspace
public import NativeRustcVmX64.Code.Vm.Kmul.Names
public import NativeRustcVmX64.Code.Vm.SubspaceAtTable.Names

/-!
# `subspace_at_table`'s loop (x86-64)

At the loop's head (`b3`) after `i` table entries (`Inv`): `W` (R12) is `atAfter`'s, the `What`s
so far in the frame from offset 40, R14 `8·i`, RBX `8·n`, R15 the table; the count and the output
pointer spilled at offsets 16, 24. A turn (`step`): `b3` loads the pair and calls `kmul`
(`What_i`), `b4a` stores it, `b4b` calls `kmul` (`W²`), `b5` calls `kmul` (`root·W`), `b6` takes
the sum as the next `W` and counts; after the last entry it falls through to `b7` (`Done`).
-/

namespace NativeRustcVmX64.Whir.SubspaceAtTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceAtTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region wordOf ewOf)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (elem_mapped elem_apart_frame wf_two stackOk_mono load8_eq
  wordAt_of_write eval_reg eval_lit eval_not eval_cmp_eq eval_add eval_load)

@[expose] public section

/-- The frame's base. -/
def fbOf (m0 : MachineData) : BitVec 64 := stackBelow m0 336
/-- The table's entries. -/
def nOf (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
/-- The point. -/
def xOf (m0 : MachineData) : UInt64 := .ofBitVec (reg m0 .rcx)
/-- The table. -/
def tbOf (m0 : MachineData) : Array (UInt64 × UInt64) :=
  (pairsOf m0.dmem (reg m0 .rsi) (nOf m0)).toArray
/-- The output. -/
def outsOf (m0 : MachineData) : List Region := [⟨reg m0 .rdi, whatBytes⟩]

/-- A body of `subspace_at_table`. -/
abbrev Fr (m0 st : MachineData) : Prop :=
  Frame m0 336 subspaceAtTableStack slots (outsOf m0) st

/-- The loop's head after `i` entries. -/
structure Inv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  rbx : reg st .rbx = BitVec.ofNat 64 (8 * nOf m0)
  r12 : reg st .r12 = (atAfter (tbOf m0) (xOf m0) i).2.toBitVec
  r14 : reg st .r14 = BitVec.ofNat 64 (8 * i)
  r15 : reg st .r15 = reg m0 .rsi
  cnt : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (.ofBitVec (reg m0 .rdx))
  out : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofBitVec (reg m0 .rdi))
  what : NativeRustcVm.WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 40)
    (atAfter (tbOf m0) (xOf m0) i).1.toList

/-- After the loop. -/
structure Done (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  cnt : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (.ofBitVec (reg m0 .rdx))
  out : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofBitVec (reg m0 .rdi))
  what : NativeRustcVm.WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 40)
    (subspaceAtTable (tbOf m0) (xOf m0)).toList

end

public section

theorem tbOf_size (m0 : MachineData) : (tbOf m0).size = nOf m0 := by simp [tbOf, pairsOf]

theorem tbOf_get (m0 : MachineData) {i : Nat} (hi : i < (tbOf m0).size) :
    (tbOf m0)[i] = (wordOf m0.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * i)),
      wordOf m0.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * i) + 8#64)) := by
  simp [tbOf, pairsOf, ewOf]

theorem mul2 (i : Nat) : BitVec.ofNat 64 (8 * i) * BitVec.ofNat 64 2 = BitVec.ofNat 64 (16 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- The loop's test: `8·n = 8 + 8·i`. -/
theorem cnt_beq {n i : Nat} (hn : n ≤ 31) (hi : i < n) :
    (BitVec.ofNat 64 (8 * n) == BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * i)) = decide (n = i + 1) := by
  rw [bv_beq_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, decide_eq_decide]
  constructor <;> intro h <;> omega

/-- The item's address: `rsp + 8·i + 32`. -/
theorem st_addr (fb : BitVec 64) (i : Nat) :
    fb + BitVec.ofInt 64 8 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 32 =
      fb + BitVec.ofNat 64 (40 + 8 * i) + BitVec.ofInt 64 0 := by
  rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
    show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, addr_add, addr_add, addr_add]
  congr 2
  omega

variable [Host] {k : Nat}

theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b4Offset) ∧
    b4b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b4Offset + b4a.length) := by
  have h := b4_in_code.trans hp.1 (by simp [b4])
  rw [← List.take_append_drop 1 b4] at h
  exact h.append
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceAtTable.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])

/-- **A turn of the loop.** -/
theorem step (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : SubspaceAtTablePre m0) {i : Nat} (hi : i < nOf m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b3Offset)) (hI : Inv m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b7Offset) ∧ Done m0 s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b3Offset) ∧ Inv m0 (i + 1) s.data ∧ i + 1 < nOf m0)) st := by
  obtain ⟨hS, hn31, htin, houtin, hap, _⟩ := hpre
  have hF : 336 ≤ subspaceAtTableStack := by decide
  have hle : 336 + kmulStack ≤ subspaceAtTableStack := by decide
  have hn : nOf m0 ≤ 31 := hn31
  have hnn : nOf m0 = (reg m0 .rdx).toNat := rfl
  have hout := out_one houtin
  have hsl := slots_ok
  have hsize := tbOf_size m0
  have hi' : i < (tbOf m0).size := by omega
  have hfr := hI.fr
  obtain ⟨hfmap, hfnw, -⟩ := frame_ok hS hF
  have hL : 288 ≤ 336 := by decide
  -- the words in the frame, kept by a block writing below offset 8 and a callee
  have keep : ∀ {d d1 d2 : MachineData} {env : Env} {S₁ : SState} {o : Nat} {bs : List UInt8},
      Match env S₁ d1 → env.WF → env.regions[0]? = some (stackBelow m0 336, 336 + 8) →
      env.mem0 = d.dmem → (∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ 8) →
      rspOf d1 = stackBelow m0 336 →
      SameOutside d1.dmem d2.dmem (InRange (stackBelow d1 kmulStack) kmulStack) →
      8 ≤ o → o + bs.length ≤ 344 →
      NativeRustcVm.BytesAt d.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt d2.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs := by
    intro d d1 d2 env S₁ o bs hm hwf hr0 hd hw hsp hso h8 hlen h
    refine bytesAt_callee hS hsp hle hso hlen (bytesAt_block hm hwf hr0 hlen (fun w hw' ↦
      ⟨(hw w hw').1, .inl (by have := (hw w hw').2; omega)⟩) (hd ▸ h))
  have hwl : ∀ j ≤ (tbOf m0).size,
      ((atAfter (tbOf m0) (xOf m0) j).1.toList.flatMap NativeRustcVm.wordBytes).length = 8 * j :=
    fun j hj ↦ by
      rw [NativeRustcVm.length_wordsBytes, Array.length_toList, atAfter_size _ _ _ hj]
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  -- `b3`: the pair, `kmul(W, inverse)`
  have hwf3 := wf_two (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b4Offset)).toBitVec)
    (stackOk_mono hS hF) hfr.kept (elem_mapped htin.1 hfr.kept hi)
    (elem_apart_frame hS hF htin.1 htin.2 hi)
  have hm3 : Match (Env.ofMachine st.data [(stackBelow m0 336, 336 + 8),
      (reg m0 .rsi + BitVec.ofNat 64 (16 * i), 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b4Offset)).toBitVec) ldS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr.rsp, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st.data .r15)
          (BinOp.apply .mul .W64 (reg st.data .r14) (BitVec.ofNat 64 2)) =
            reg m0 .rsi + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 0
        rw [add64, mul64, hI.r15, hI.r14, mul2,
          show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine exec_at (hb3 hp) run_b3 hwf3 (fun _ _ ↦ rfl) hpc hm3 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk1, hsp1, hw1⟩ := after_eq run_b3 ▸ b3_call
  have hrsp1 := rsp_call hm1 hsp1
  have harg := hfr.get?_arg hS htin fun r hr ↦ by
    simp only [outsOf, List.mem_singleton] at hr
    subst hr
    exact ⟨Arrays.apart_symm hap, houtin.1.2⟩
  have hroot : reg st1.data .r13 = ((tbOf m0)[i]'hi').1.toBitVec := by
    refine (hm1.regs .r13 _ rfl).trans ?_
    rw [eval_load, load8_eq]
    show (wordOf st.data.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * i) +
      BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, tbOf_get m0 hi']
    refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
    rw [addr_add]
    exact harg _ (by omega)
  have hinv : reg st1.data .rsi = ((tbOf m0)[i]'hi').2.toBitVec := by
    refine (hm1.regs .rsi _ rfl).trans ?_
    rw [eval_load, load8_eq]
    show (wordOf st.data.dmem (reg m0 .rsi + BitVec.ofNat 64 (16 * i) +
      BitVec.ofNat 64 8)).toBitVec = _
    rw [tbOf_get m0 hi']
    refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
    rw [addr_add, addr_add]
    exact harg _ (by omega)
  have hw1' : reg st1.data .rdi = reg st.data .r12 := hm1.regs .rdi _ rfl
  refine Frame.call hkmul hfr hS hle hL hsl hout hwf3 hm3 hm1 hpc1 hk1 hsp1
    (fun w hw ↦ ⟨(hw1 w hw).1, by have := (hw1 w hw).2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm1.kept hwf3 p (hfr.kept p h)) hrsp1 hle)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st2 hpc2 hfr2 ⟨hax2, hso2, hsv2⟩ ↦ ?_
  have k2 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 344 →
      NativeRustcVm.BytesAt st.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st2.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs :=
    fun h8 hlen h ↦ keep hm1 hwf3 rfl rfl hw1 hrsp1 hso2 h8 hlen h
  have r2 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg st2.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (hsv2.1 _ rfl).trans (Match.reg_eq hm3 hm1 rfl rfl)
  -- `b4a`: store `What_i`
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b4Offset) := hpc2
  have hrd4 : Readable st2.data (stackBelow m0 336 + BitVec.ofNat 64 (40 + 8 * i)) 8 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (o := 40 + 8 * i) (n := 8) (by omega))
      hfr2.kept
  have hwf4 : (Env.ofMachine st2.data
      [(stackBelow m0 336 + BitVec.ofNat 64 (40 + 8 * i), 8)]).WF :=
    Env.wf_of ⟨⟨hrd4.1, hrd4.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm4 : Match (Env.ofMachine st2.data
      [(stackBelow m0 336 + BitVec.ofNat 64 (40 + 8 * i), 8)]) stS st2.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      show BinOp.apply .add .W64 (BinOp.apply .add .W64 (reg st2.data .rsp) (reg st2.data .r14))
        (BitVec.ofNat 64 32) = stackBelow m0 336 + BitVec.ofNat 64 (40 + 8 * i) + BitVec.ofInt 64 0
      rw [add64, add64, show reg st2.data .rsp = _ from hfr2.rsp, r2 .r14 (by simp),
        hI.r14]
      exact st_addr _ i, trivial⟩
  refine exec_at (hb4 hp).1 run_b4a hwf4 (by intro l h; cases h) hpc2' hm4 fun st3 hm5 hpc3 ↦ ?_
  obtain ⟨hk5, hw5⟩ := after_eq run_b4a ▸ b4a_write
  have hfr3 := hfr2.of_write hm4 hm5 hwf4 rfl hk5 (r := 0) rfl le_rfl hw5
    (fun p h ↦ .inr (inRange_stack_of hS hF (L := 288) (by decide) (by omega) h))
    (slot_not_in hS hF (by omega) (by omega) hsl)
  have hso3 := same_region_le hm5 hwf4 (r := 0) rfl le_rfl hw5
  have hv : NativeRustcVm.WordAt st3.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 (40 + 8 * i))
      (kmul (atAfter (tbOf m0) (xOf m0) i).2 ((tbOf m0)[i]'hi').2) := by
    have := wordAt_of_write hm5 (r := 0) (o := 0) rfl (by decide) (v := .reg .rax) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    have e : UInt64.ofBitVec ((Sym.reg .rax).eval (Env.ofMachine st2.data
        [(stackBelow m0 336 + BitVec.ofNat 64 (40 + 8 * i), 8)])) =
        kmul (atAfter (tbOf m0) (xOf m0) i).2 ((tbOf m0)[i]'hi').2 := by
      show UInt64.ofBitVec (reg st2.data .rax) = _
      rw [hax2, hw1', hinv, hI.r12]
    rw [e] at this
    exact this
  have r3 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st3.data r = reg st2.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm4 hm5 rfl rfl
  have keep3 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 40 →
      NativeRustcVm.BytesAt st2.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs :=
    fun hlen h ↦ NativeRustcVm.BytesAt.of_sameOutside h hso3 fun j hj ↦ by
      rw [addr_add, inRange_fb_iff hS hF (by omega) (by omega) (by omega)]
      omega
  have hwhat3 : NativeRustcVm.WordsAt st3.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 40)
      (atAfter (tbOf m0) (xOf m0) (i + 1)).1.toList := by
    rw [atAfter_succ _ _ hi', atStep, Array.toList_push, NativeRustcVm.wordsAt_append,
      NativeRustcVm.wordsAt_singleton, Array.length_toList, atAfter_size _ _ _ hi'.le, addr_add]
    refine ⟨NativeRustcVm.BytesAt.of_sameOutside (k2 (by omega) (by rw [hwl i hi'.le]; omega)
      hI.what) hso3 fun j hj ↦ ?_, hv⟩
    rw [hwl i hi'.le] at hj
    rw [addr_add, inRange_fb_iff hS hF (by omega) (by omega) (by omega)]
    omega
  -- `b4b`: `kmul(W, W)`
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b4Offset + b4a.length) := hpc3
  have hwf5 := hfr3.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b5Offset)).toBitVec) hS hF
  refine exec_at (hb4 hp).2 run_b4b hwf5 (fun _ _ ↦ rfl) hpc3' hfr3.mid_match
    fun st4 hm6 hpc4 ↦ ?_
  obtain ⟨hk6, hsp6, hw6⟩ := after_eq run_b4b ▸ b4b_call
  have hrsp4 := rsp_call hm6 hsp6
  refine Frame.call hkmul hfr3 hS hle hL hsl hout hwf5 hfr3.mid_match hm6 hpc4 hk6 hsp6
    (fun w hw ↦ ⟨(hw6 w hw).1, by have := (hw6 w hw).2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm6.kept hwf5 p (hfr3.kept p h)) hrsp4 hle)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st5 hpc5 hfr5 ⟨hax5, hso5, hsv5⟩ ↦ ?_
  have k5 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 344 →
      NativeRustcVm.BytesAt st3.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st5.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs :=
    fun h8 hlen h ↦ keep hm6 hwf5 rfl rfl hw6 hrsp4 hso5 h8 hlen h
  have r5 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st5.data r = reg st3.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (hsv5.1 _ rfl).trans (Match.reg_eq hfr3.mid_match hm6 rfl rfl)
  have hww : reg st5.data .rax = (kmul (atAfter (tbOf m0) (xOf m0) i).2
      (atAfter (tbOf m0) (xOf m0) i).2).toBitVec := by
    rw [hax5, show reg st4.data .rdi = reg st3.data .r12 from hm6.regs .rdi _ rfl,
      show reg st4.data .rsi = reg st3.data .r12 from hm6.regs .rsi _ rfl,
      r3 .r12 (by simp), r2 .r12 (by simp), hI.r12, UInt64.ofBitVec_toBitVec]
  -- `b5`: `kmul(root, W)`
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b5Offset) := hpc5
  have hwf7 := hfr5.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b6Offset)).toBitVec) hS hF
  refine exec_at (hb5 hp) run_b5 hwf7 (fun _ _ ↦ rfl) hpc5' hfr5.mid_match fun st6 hm7 hpc6 ↦ ?_
  obtain ⟨hk7, hsp7, hw7⟩ := after_eq run_b5 ▸ b5_call
  have hrsp6 := rsp_call hm7 hsp7
  refine Frame.call hkmul hfr5 hS hle hL hsl hout hwf7 hfr5.mid_match hm7 hpc6 hk7 hsp7
    (fun w hw ↦ ⟨(hw7 w hw).1, by have := (hw7 w hw).2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm7.kept hwf7 p (hfr5.kept p h)) hrsp6 hle)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st7 hpc7 hfr7 ⟨hax7, hso7, hsv7⟩ ↦ ?_
  have k7 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 344 →
      NativeRustcVm.BytesAt st5.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st7.data.dmem (stackBelow m0 336 + BitVec.ofNat 64 o) bs :=
    fun h8 hlen h ↦ keep hm7 hwf7 rfl rfl hw7 hrsp6 hso7 h8 hlen h
  have r7 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg st7.data r = reg st5.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv7.1 _ rfl).trans (Match.reg_eq hfr5.mid_match hm7 rfl rfl)
  have hrw : reg st7.data .rax = (kmul ((tbOf m0)[i]'hi').1
      (atAfter (tbOf m0) (xOf m0) i).2).toBitVec := by
    rw [hax7, show reg st6.data .rdi = reg st5.data .r13 from hm7.regs .rdi _ rfl,
      show reg st6.data .rsi = reg st5.data .r12 from hm7.regs .rsi _ rfl,
      r5 .r13 (by simp), r5 .r12 (by simp), r3 .r13 (by simp), r3 .r12 (by simp),
      show reg st2.data .r13 = reg st1.data .r13 from hsv2.1 .r13 rfl, r2 .r12 (by simp), hroot,
      hI.r12, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
  have hrbp : reg st7.data .rbp = (kmul (atAfter (tbOf m0) (xOf m0) i).2
      (atAfter (tbOf m0) (xOf m0) i).2).toBitVec := by
    rw [show reg st7.data .rbp = reg st6.data .rbp from hsv7.1 .rbp rfl,
      show reg st6.data .rbp = reg st5.data .rax from hm7.regs .rbp _ rfl, hww]
  -- `b6`: the next `W`, the count
  have hpc7' : st7.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b6Offset) := hpc7
  refine exec_at (hb6 hp) run_b6 (Env.wf_nil _) (by intro l h; cases h) hpc7' (match_nil _)
    fun st8 hm8 hpc8 ↦ ?_
  have hfr8 := hfr7.of_block (match_nil _) hm8 (Env.wf_nil _) rfl (after_eq run_b6 ▸ b6_keeps)
  have hd8 : st8.data.dmem = st7.data.dmem := hm8.dmem_eq (Env.wf_nil _) rfl
  have e7 : ∀ r ∈ [Reg64.rbx, .r14, .r15], reg st7.data r = reg st.data r := by
    intro r hr
    rw [r7 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (r5 _ (by simp)).trans ((r3 _ (by simp)).trans (r2 _ (by simp)))
  have hrbx7 : (Env.ofMachine st7.data []).regs .rbx = BitVec.ofNat 64 (8 * nOf m0) :=
    (e7 .rbx (by simp)).trans hI.rbx
  have hr147 : (Env.ofMachine st7.data []).regs .r14 = BitVec.ofNat 64 (8 * i) :=
    (e7 .r14 (by simp)).trans hI.r14
  have hcnt8 : NativeRustcVm.WordAt st8.data.dmem (fbOf m0 + BitVec.ofNat 64 16)
      (.ofBitVec (reg m0 .rdx)) := by
    rw [hd8]
    refine k7 (by omega) (by rw [hlw]; omega) (k5 (by omega) (by rw [hlw]; omega) ?_)
    exact keep3 (by rw [hlw]; omega) (k2 (by omega) (by rw [hlw]; omega) hI.cnt)
  have hout8 : NativeRustcVm.WordAt st8.data.dmem (fbOf m0 + BitVec.ofNat 64 24)
      (.ofBitVec (reg m0 .rdi)) := by
    rw [hd8]
    refine k7 (by omega) (by rw [hlw]; omega) (k5 (by omega) (by rw [hlw]; omega) ?_)
    exact keep3 (by rw [hlw]; omega) (k2 (by omega) (by rw [hlw]; omega) hI.out)
  have hwhat8 : NativeRustcVm.WordsAt st8.data.dmem (fbOf m0 + BitVec.ofNat 64 40)
      (atAfter (tbOf m0) (xOf m0) (i + 1)).1.toList := by
    rw [hd8]
    exact k7 (by omega) (by rw [hwl _ (by omega)]; omega)
      (k5 (by omega) (by rw [hwl _ (by omega)]; omega) hwhat3)
  simp only [PcOk] at hpc8
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg, hrbx7, hr147,
    cnt_beq hn hi] at hpc8
  obtain ⟨hT, hF8⟩ := Arrays.pc_cond hpc8
  by_cases hlast : nOf m0 = i + 1
  · have hpc8' := hF8 (by simp [hlast])
    refine .done _ (.inl ⟨hpc8', hfr8, hcnt8, hout8, ?_⟩)
    rw [subspaceAtTable_eq, hsize, hlast]
    exact hwhat8
  · have hl2 : Labels.label NativeRustcVmX64.Vm.SubspaceAtTable.label_2 = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceAtTable.b3Offset) := hp.label NativeRustcVmX64.Vm.SubspaceAtTable.label_2_at
    refine .done _ (.inr ⟨(hT (by simp [hlast])).trans hl2, ⟨hfr8, ?_, ?_, ?_, ?_, hcnt8, hout8,
      hwhat8⟩, by omega⟩)
    · exact (Match.reg_eq (match_nil _) hm8 rfl rfl).trans hrbx7
    · refine (hm8.regs .r12 _ rfl).trans ?_
      rw [atAfter_succ _ _ hi']
      show BinOp.apply .xor .W64 (reg st7.data .rax) (reg st7.data .rbp) =
        (kmul (atAfter (tbOf m0) (xOf m0) i).2 (atAfter (tbOf m0) (xOf m0) i).2 ^^^
          kmul ((tbOf m0)[i]'hi').1 (atAfter (tbOf m0) (xOf m0) i).2).toBitVec
      rw [xor64, hrw, hrbp, ← UInt64.toBitVec_xor, UInt64.xor_comm]
    · refine (hm8.regs .r14 _ rfl).trans ?_
      rw [eval_add, eval_lit, eval_reg, hr147]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · exact (Match.reg_eq (match_nil _) hm8 rfl rfl).trans ((e7 .r15 (by simp)).trans hI.r15)

end

end NativeRustcVmX64.Whir.SubspaceAtTable
