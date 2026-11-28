module

public import NativeRustcVmX64.Whir.FoldRow.Turn
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `fold_row`'s rounds (x86-64)

`round`: from a round's head (`RInv r`, `b4`): `b4`, `b5` load the round and compute `β·x` (two
`kmul`s), `b6` halves the size; none left: to `b3` (`EInv r`); else `b7` takes the factor `α + β·x`
and the turns (`turn`, by `Sym.loop`) fold the lanes, to `b3` (`EInv r`). `next`: `b3` goes to the
next round's head (`RInv (r + 1)`) or, the rounds done, to `b13` (`Done`).
-/

namespace NativeRustcVmX64.Whir.FoldRow

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FoldRow NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt EWAt ewOf wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add eval_cmp_eq eval_xor wf_two apart_symm not_inRange_of_apart beq_add_left
  written_region0)

public section

theorem shr1 (x : BitVec 64) : BinOp.apply .shr .W64 x (BitVec.ofNat 64 1) = x >>> 1 := by
  simp only [BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask]
  congr 1

theorem shr_succ (n r : Nat) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 (n >>> r) >>> 1 = BitVec.ofNat 64 (n >>> (r + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : n >>> r < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) h
  have h2 : n >>> (r + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) h
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2, Nat.shiftRight_succ n r, Nat.shiftRight_eq_div_pow _ 1, Nat.pow_one]

theorem fac_c0 (m0 : MachineData) (r : Nat) :
    (facOf m0 r).c0 = (rdOf m0 r).alpha.c0 ^^^ kmul (xOf m0) (rdOf m0 r).beta.c0 := rfl
theorem fac_c1 (m0 : MachineData) (r : Nat) :
    (facOf m0 r).c1 = (rdOf m0 r).alpha.c1 ^^^ kmul (xOf m0) (rdOf m0 r).beta.c1 := rfl

variable [Host] {k : Nat}

theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.FoldRow.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])

/-- **The turns of a round**, from the first. -/
theorem turns (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : FoldRowPre m0) {r : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b10Offset)) (hI : TInv m0 r 0 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b3Offset) ∧ EInv m0 r s.data) st := by
  refine Sym.loop (fun n s ↦ ∃ i, n = nOf m0 >>> (r + 1) - i ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b10Offset) ∧
    TInv m0 r i s.data) (fun n s ⟨i, hn, hpc, hI⟩ ↦ ?_) ⟨0, rfl, hpc, hI⟩
  have hi := hI.hi
  refine (turn hp hmul hpre hpc hI).mono fun s' h ↦ ?_
  rcases h with ⟨hpc', hI'⟩ | h
  · exact .inr ⟨_, by have := hI'.hi; omega, i + 1, rfl, hpc', hI'⟩
  · exact .inl h

/-- **A round** from its head. -/
theorem round (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : FoldRowPre m0) {r : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b4Offset)) (hI : RInv m0 r st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b3Offset) ∧ EInv m0 r s.data) st := by
  have hpre' := hpre
  obtain ⟨hS, hlanes, hrin, hap, hR6⟩ := hpre'
  obtain ⟨hF, hlek, -⟩ := stack_le
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hlb : lanesBytes = 1024 := rfl
  have hrb : roundBytes = 32 := rfl
  have hout := out_one hlanes
  have hsl := slots_ok
  have hfr := hI.base.fr
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have hr := hI.hr
  have hRn : rnOf m0 = (reg m0 .r8).toNat := rfl
  have hn64 := (reg m0 .rsi).isLt
  -- `b4`: the round, `kmul(x, β.c0)`
  have hrd : Readable st.data (rpOf m0 + BitVec.ofNat 64 (32 * r)) 32 :=
    Readable.keep (Readable.sub hrin.1 (by rw [hrb]; unfold rnOf at hr; omega)) hfr.kept
  have hap1 : Apart (stackBelow m0 96) (96 + 8) (rpOf m0 + BitVec.ofNat 64 (32 * r)) 32 :=
    apart_symm (apart_frame' hS hF (OffStack.sub hrin.2 hrin.1.2
      (by rw [hrb]; unfold rnOf at hr; omega)))
  have hwf : (Env.ofMachine st.data [(stackBelow m0 96, 96 + 8),
      (rpOf m0 + BitVec.ofNat 64 (32 * r), 32)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b5Offset)).toBitVec).WF :=
    wf_two (stackOk_mono hS hF) hfr.kept hrd hap1
  have hm : Match (Env.ofMachine st.data [(stackBelow m0 96, 96 + 8),
      (rpOf m0 + BitVec.ofNat 64 (32 * r), 32)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b5Offset)).toBitVec) rdS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hfr.rsp, show reg st.data .rcx = _ + BitVec.ofInt 64 0 by
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; exact hI.rcx, trivial⟩
      trivial trivial trivial
  refine exec_at (hb4 hp) run_b4 hwf (fun _ _ ↦ rfl) hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk1, hsp1, hw1, hrd1⟩ := after_eq run_b4 ▸ b4_call
  have hrsp1 := rsp_call hm1 hsp1
  have harg := hfr.get?_arg hS hrin fun q hq ↦ by
    simp only [outsOf, List.mem_singleton] at hq
    subst hq
    exact ⟨apart_symm hap, hlanes.1.2⟩
  have hword : ∀ o, o + 8 ≤ 32 →
      wordOf st.data.dmem (rpOf m0 + BitVec.ofNat 64 (32 * r) + BitVec.ofNat 64 o) =
        wordOf m0.dmem (rpOf m0 + BitVec.ofNat 64 (32 * r) + BitVec.ofNat 64 o) := fun o ho ↦
    NativeRustcVm.wordOf_congr fun j hj ↦ by
      rw [addr_add, addr_add]
      exact harg _ (by rw [hrb]; unfold rnOf at hr; omega)
  have hrdr := rdOf_eq m0 hr
  have hload1 : ∀ o, o + 8 ≤ 32 → (Env.ofMachine st.data [(stackBelow m0 96, 96 + 8),
      (rpOf m0 + BitVec.ofNat 64 (32 * r), 32)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b5Offset)).toBitVec).load 1 o 8 =
        (wordOf m0.dmem (rpOf m0 + BitVec.ofNat 64 (32 * r) + BitVec.ofNat 64 o)).toBitVec :=
    fun o ho ↦ by rw [load8_eq]; exact congrArg UInt64.toBitVec (hword o ho)
  have ha0 : reg st1.data .r13 = (rdOf m0 r).alpha.c0.toBitVec := by
    refine (hm1.regs .r13 _ rfl).trans ?_
    rw [eval_load, hload1 0 (by omega), hrdr, NativeRustcVm.addr_add_zero]
    rfl
  have ha1 : reg st1.data .r12 = (rdOf m0 r).alpha.c1.toBitVec := by
    refine (hm1.regs .r12 _ rfl).trans ?_
    rw [eval_load, hload1 8 (by omega), hrdr]
    rfl
  have hb0 : reg st1.data .rsi = (rdOf m0 r).beta.c0.toBitVec := by
    refine (hm1.regs .rsi _ rfl).trans ?_
    rw [eval_load, hload1 16 (by omega), hrdr, addr_add]
    rfl
  have hb1 : reg st1.data .r15 = (rdOf m0 r).beta.c1.toBitVec := by
    refine (hm1.regs .r15 _ rfl).trans ?_
    rw [eval_load, hload1 24 (by omega), hrdr, addr_add]
    show _ = (wordOf m0.dmem (rpOf m0 + BitVec.ofNat 64 (32 * r + 16) + 8#64)).toBitVec
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add]
  have hx1 : ∀ R ∈ [Reg64.rdi, .rbp], reg st1.data R = (xOf m0).toBitVec := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl <;>
    · refine (hm1.regs _ _ rfl).trans ?_
      rw [eval_load, load_word (show WordAt st.data.dmem (stackBelow m0 96 + BitVec.ofNat 64 32) _
        from hI.base.x)]
  have hrdw : WordAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 40)
      (.ofBitVec (rpOf m0 + BitVec.ofNat 64 (32 * r))) := by
    have := wordAt_of_write hm1 (r := 0) (o := 40) rfl (by decide) (v := .ptr 1 0) hrd1
    rw [show (Sym.ptr 1 0).eval (Env.ofMachine st.data [(stackBelow m0 96, 96 + 8),
      (rpOf m0 + BitVec.ofNat 64 (32 * r), 32)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b5Offset)).toBitVec) =
        rpOf m0 + BitVec.ofNat 64 (32 * r) from by
          show _ + BitVec.ofInt 64 0 = _
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
          rfl] at this
    exact this
  have e1 : ∀ R ∈ [Reg64.rbx, .r14], reg st1.data R = reg st.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have hkw1 : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 40 → 8 ≤ o →
      WordAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w →
      WordAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w := fun h8 h' h ↦
    bytesAt_block hm1 hwf rfl (by rw [hlw]; omega)
      (fun w hw ↦ ⟨(hw1 w hw).1, by have := (hw1 w hw).2; rw [hlw]; omega⟩) h
  refine Frame.call hkmul hfr hS hlek (L := 48) (by decide) (fun q hq ↦ hsl q hq) hout hwf hm hm1
    hpc1 hk1 hsp1 (fun w hw ↦ ⟨(hw1 w hw).1, (hw1 w hw).2.2⟩)
    (stackOk_callee hS (fun p h ↦ hm1.kept hwf p (hfr.kept p h)) hrsp1 hlek)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st2 hpc2 hfr2 ⟨hax2, hso2, hsv2⟩ ↦ ?_
  have hsr : ∀ {p : BitVec 64}, InRange (stackBelow st1.data kmulStack) kmulStack p →
      InRange (stackBelow m0 foldRowStack) foldRowStack p := fun h ↦ inRange_callee hS hrsp1 hlek h
  have hlanes2 : LanesAt m0 st2.data.dmem (lanesAt m0 r) :=
    lanes_stack hS hlanes (lanes_stack hS hlanes hI.lanes (Match.sameOutside hm1 hwf)
      fun p h ↦ inRange_frame hS hF (L := 48) (by omega)
        (written_region0 rfl hwf (k := 48) (by omega) (fun w hw ↦ ⟨(hw1 w hw).1, (hw1 w hw).2.2⟩)
          h)) hso2 fun p h ↦ hsr h
  have hkw2 : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 104 →
      WordAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w →
      WordAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w := fun ho h ↦
    bytesAt_callee hS hrsp1 hlek hso2 (by rw [hlw]; omega) h
  have e2 : ∀ R ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st2.data R = reg st1.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hsv2.1 _ rfl
  have hk1v : reg st2.data .rax = (kmul (xOf m0) (rdOf m0 r).beta.c0).toBitVec := by
    rw [hax2, hx1 .rdi (by simp), hb0, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
  -- `b5`: `kmul(x, β.c1)`
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b5Offset) := hpc2
  have hwf3 := hfr2.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b6Offset)).toBitVec) hS hF
  refine exec_at (hb5 hp) run_b5 hwf3 (fun _ _ ↦ rfl) hpc2' hfr2.mid_match fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hsp3, hw3, hv3⟩ := after_eq run_b5 ▸ b5_call
  have hrsp3 := rsp_call hm3 hsp3
  refine Frame.call hkmul hfr2 hS hlek (L := 48) (by decide) (fun q hq ↦ hsl q hq) hout hwf3
    hfr2.mid_match hm3 hpc3 hk3 hsp3 (fun w hw ↦ ⟨(hw3 w hw).1, by have := (hw3 w hw).2.2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm3.kept hwf3 p (hfr2.kept p h)) hrsp3 hlek)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st4 hpc4 hfr4 ⟨hax4, hso4, hsv4⟩ ↦ ?_
  have hlanes4 : LanesAt m0 st4.data.dmem (lanesAt m0 r) :=
    lanes_stack hS hlanes (lanes_stack hS hlanes hlanes2 (Match.sameOutside hm3 hwf3)
      fun p h ↦ inRange_frame hS hF (L := 48) (by omega)
        (written_region0 rfl hwf3 (k := 48) (by omega)
          (fun w hw ↦ ⟨(hw3 w hw).1, by have := (hw3 w hw).2.2; omega⟩) h)) hso4
      fun p h ↦ inRange_callee hS hrsp3 hlek h
  have hkw4 : ∀ {o : Nat} {w : UInt64}, 24 ≤ o → o + 8 ≤ 104 →
      WordAt st2.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w →
      WordAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w := fun h24 ho h ↦
    bytesAt_callee hS hrsp3 hlek hso4 (by rw [hlw]; omega)
      (bytesAt_block hm3 hwf3 rfl (by rw [hlw]; omega)
        (fun w hw ↦ ⟨(hw3 w hw).1, .inl (by have := (hw3 w hw).2.2; omega)⟩) h)
  have hk1w : WordAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (kmul (xOf m0) (rdOf m0 r).beta.c0) := by
    have := wordAt_of_write hm3 (r := 0) (o := 16) rfl (by decide) (v := .reg .rax) hv3
    rw [eval_reg, Env.ofMachine_regs, show st2.data.regs.get64 .rax = _ from hk1v,
      UInt64.ofBitVec_toBitVec] at this
    exact bytesAt_callee hS hrsp3 hlek hso4 (by rw [hlw]; omega) this
  have e4 : ∀ R ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st4.data R = reg st1.data R := by
    intro R hR
    rw [← e2 R hR]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hsv4.1 _ rfl).trans (Match.reg_eq hfr2.mid_match hm3 rfl rfl)
  have hk2v : reg st4.data .rax = (kmul (xOf m0) (rdOf m0 r).beta.c1).toBitVec := by
    rw [hax4, show reg st3.data .rdi = reg st2.data .rbp from hm3.regs .rdi _ rfl,
      show reg st3.data .rsi = reg st2.data .r15 from hm3.regs .rsi _ rfl,
      e2 .rbp (by simp), e2 .r15 (by simp), hx1 .rbp (by simp), hb1,
      UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
  -- `b6`: `β·x`'s second limb, the size halved
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b6Offset) := hpc4
  have hwf5 := hfr4.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb6 hp) run_b6 hwf5 (by intro l h; cases h) hpc4' hfr4.mid_match
    fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hk5, hw5, hv5⟩ := after_eq run_b6 ▸ b6_write
  have hfr5 : Fr m0 st5.data := hfr4.of_write hfr4.mid_match hm5 hwf5 rfl hk5 (r := 0) rfl
    (len := 16) (by omega) (fun w hw ↦ ⟨(hw5 w hw).1, (hw5 w hw).2.2⟩)
    (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have hkw5 : ∀ {o : Nat} {w : UInt64}, 16 ≤ o → o + 8 ≤ 104 →
      WordAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w →
      WordAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w := fun h16 ho h ↦
    bytesAt_block hm5 hwf5 rfl (by rw [hlw]; omega)
      (fun w hw ↦ ⟨(hw5 w hw).1, .inl (by have := (hw5 w hw).2.2; omega)⟩) h
  have hlanes5 : LanesAt m0 st5.data.dmem (lanesAt m0 r) :=
    lanes_stack hS hlanes hlanes4 (Match.sameOutside hm5 hwf5) fun p h ↦
      inRange_frame hS hF (L := 16) (by omega)
        (written_region0 rfl hwf5 (k := 16) (by omega)
          (fun w hw ↦ ⟨(hw5 w hw).1, (hw5 w hw).2.2⟩) h)
  have hk2w : WordAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 8) (kmul (xOf m0) (rdOf m0 r).beta.c1) := by
    have := wordAt_of_write hm5 (r := 0) (o := 8) rfl (by decide) (v := .reg .rax) hv5
    rwa [eval_reg, Env.ofMachine_regs, show st4.data.regs.get64 .rax = _ from hk2v,
      UInt64.ofBitVec_toBitVec] at this
  have hrbx4 : reg st4.data .rbx = BitVec.ofNat 64 (nOf m0 >>> r) :=
    (e4 .rbx (by simp)).trans ((e1 .rbx (by simp)).trans hI.rbx)
  have hrbx5 : reg st5.data .rbx = BitVec.ofNat 64 (nOf m0 >>> (r + 1)) := by
    refine (hm5.regs .rbx _ rfl).trans ?_
    show BinOp.apply .shr .W64 (reg st4.data .rbx) (BitVec.ofNat 64 1) = _
    rw [shr1, hrbx4, shr_succ (nOf m0) _ hn64]
  have hbase5 : Base m0 st5.data := ⟨hfr5,
    hkw5 (by omega) (by omega) (hkw4 (by omega) (by omega) (hkw2 (by omega)
      (hkw1 (by omega) (by omega) hI.base.x))),
    hkw5 (by omega) (by omega) (hkw4 (by omega) (by omega) (hkw2 (by omega)
      (hkw1 (by omega) (by omega) hI.base.ed))),
    (Match.reg_eq (r := .r14) hfr4.mid_match hm5 rfl rfl).trans ((e4 .r14 (by simp)).trans
      ((e1 .r14 (by simp)).trans hI.base.r14))⟩
  have hrd5 : WordAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 40)
      (.ofBitVec (rpOf m0 + BitVec.ofNat 64 (32 * r))) :=
    hkw5 (by omega) (by omega) (hkw4 (by omega) (by omega) (hkw2 (by omega) hrdw))
  have hsh64 : nOf m0 >>> (r + 1) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by unfold nOf; exact hn64)
  simp only [PcOk] at hpc5
  rw [eval_cmp_eq, eval_lit, show (Sym.bin .shr .W64 (.reg .rbx) (.lit 1)).eval
      (frameEnv m0 st4.data 96 (fun _ ↦ 0) 0) = reg st4.data .rbx >>> 1 from shr1 _,
    hrbx4, shr_succ (nOf m0) _ hn64, ofNat_beq hsh64 (by decide)] at hpc5
  obtain ⟨hT, hF5⟩ := Arrays.pc_cond hpc5
  by_cases h0 : nOf m0 >>> (r + 1) = 0
  · refine .done _ ⟨(hT (by rw [decide_eq_true_eq]; exact h0)).trans (hp.label NativeRustcVmX64.Vm.FoldRow.label_2_at),
      hbase5, hr, hrd5, hrbx5, ?_⟩
    rw [lanesAt_succ, h0, foldPart_zero]
    exact hlanes5
  -- `b7`: the factor
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRow.b7Offset) := hF5 (by rw [decide_eq_true_eq]; exact h0)
  have hwf6 := hfr5.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb7 hp) run_b7 hwf6 (by intro l h; cases h) hpc5' hfr5.mid_match
    fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hk6, hw6, hv68, hv616⟩ := after_eq run_b7 ▸ b7_write
  have hfr6 : Fr m0 st6.data := hfr5.of_write hfr5.mid_match hm6 hwf6 rfl hk6 (r := 0) rfl
    (len := 24) (by omega) (fun w hw ↦ ⟨(hw6 w hw).1, (hw6 w hw).2.2⟩)
    (fun p h ↦ .inr (inRange_frame hS hF (by omega) h))
    (fun q hq i hi ↦ by
      rw [addr_add]
      exact Arrays.not_inRange_above (by have := hsl q hq; omega)
        (by rw [hfe]; have := hsl q hq; omega))
  have hkw6 : ∀ {o : Nat} {w : UInt64}, 24 ≤ o → o + 8 ≤ 104 →
      WordAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w →
      WordAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 o) w := fun h24 ho h ↦
    bytesAt_block hm6 hwf6 rfl (by rw [hlw]; omega)
      (fun w hw ↦ ⟨(hw6 w hw).1, .inl (by have := (hw6 w hw).2.2; omega)⟩) h
  have e5 : ∀ R ∈ [Reg64.r12, .r13], reg st5.data R = reg st1.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl <;>
      exact (Match.reg_eq hfr4.mid_match hm5 rfl rfl).trans (e4 _ (by simp))
  have hk16 : WordAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 16)
      (kmul (xOf m0) (rdOf m0 r).beta.c0) :=
    hkw5 (by omega) (by omega) hk1w
  have hf0 : WordAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (facOf m0 r).c0 := by
    have := wordAt_of_write hm6 (r := 0) (o := 16) rfl (by decide)
      (v := .bin .xor .W64 (.load 0 16 8) (.reg .r13)) hv616
    rwa [eval_xor, eval_load, eval_reg, Env.ofMachine_regs, load_word hk16,
      show st5.data.regs.get64 .r13 = _ from (e5 .r13 (by simp)).trans ha0, ← UInt64.toBitVec_xor,
      UInt64.ofBitVec_toBitVec, UInt64.xor_comm, ← fac_c0] at this
  have hf1 : WordAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 8) (facOf m0 r).c1 := by
    have := wordAt_of_write hm6 (r := 0) (o := 8) rfl (by decide)
      (v := .bin .xor .W64 (.load 0 8 8) (.reg .r12)) hv68
    rwa [eval_xor, eval_load, eval_reg, Env.ofMachine_regs, load_word hk2w,
      show st5.data.regs.get64 .r12 = _ from (e5 .r12 (by simp)).trans ha1, ← UInt64.toBitVec_xor,
      UInt64.ofBitVec_toBitVec, UInt64.xor_comm, ← fac_c1] at this
  have hlanes6 : LanesAt m0 st6.data.dmem (lanesAt m0 r) :=
    lanes_stack hS hlanes hlanes5 (Match.sameOutside hm6 hwf6) fun p h ↦
      inRange_frame hS hF (L := 24) (by omega)
        (written_region0 rfl hwf6 (k := 24) (by omega)
          (fun w hw ↦ ⟨(hw6 w hw).1, (hw6 w hw).2.2⟩) h)
  simp only [PcOk] at hpc6
  refine turns hp hmul hpre (hpc6.trans (hp.label NativeRustcVmX64.Vm.FoldRow.label_5_at)) ⟨⟨hfr6,
    hkw6 (by omega) (by omega) hbase5.x, hkw6 (by omega) (by omega) hbase5.ed,
    (Match.reg_eq (r := .r14) hfr5.mid_match hm6 rfl rfl).trans hbase5.r14⟩, hr,
    hkw6 (by omega) (by omega) hrd5, hf0, hf1, Nat.pos_of_ne_zero h0,
    (Match.reg_eq (r := .rbx) hfr5.mid_match hm6 rfl rfl).trans hrbx5,
    (hm6.regs .r12 _ rfl).trans rfl, (hm6.regs .r13 _ rfl).trans rfl, ?_⟩
  rw [foldPart_zero]
  exact hlanes6

end

end NativeRustcVmX64.Whir.FoldRow
