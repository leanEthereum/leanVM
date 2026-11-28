module

public import NativeRustcVmX64.Layout.StackOffsets.Loop
public import NativeRustcVmX64.Arrays.Common

/-!
# `stack_offsets` on x86-64: a turn of the main loop (`b17` to `b21`)

From the head `b18` (`Loop m0 j`): with `j = n` to `b23` (`End`); else `b19` loads
`i = order[j]` (below `n`, so below `offsets`' length), `b20` stores the total at `offsets[i]`,
`b21` loads `sizes[i]` and fails past `63` (`Fail`), `b17` adds `2 ^ size`, failing on a carry,
and returns to the head with `j + 1` blocks placed (`step`, `loop`).
-/

namespace NativeRustcVmX64.Layout.StackOffsets

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.StackOffsets NativeRustcVmX64.Layout.BuildFrame
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVm.Layout (OffsetsFit)

public section

theorem or63 (s : Nat) : (decide (s < 63) || decide (s = 63)) = decide (s ≤ 63) := by
  by_cases h : s ≤ 63
  · rw [decide_eq_true h]
    by_cases h' : s < 63
    · rw [decide_eq_true h']; rfl
    · rw [decide_eq_false h', decide_eq_true (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_false (by omega), decide_eq_false (by omega)]; rfl

theorem not_inRange_zero' {a q : BitVec 64} : ¬ NativeRustcVm.InRange a 0 q := by
  unfold NativeRustcVm.InRange; omega

theorem sub1 (a : Reg64) : ∀ r ∈ cs, r ∈ a :: cs := fun _ h ↦ List.mem_cons_of_mem _ h
theorem sub3 (a b c : Reg64) : ∀ r ∈ cs, r ∈ a :: b :: c :: cs := fun _ h ↦
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
theorem sub4 (a b c e : Reg64) : ∀ r ∈ cs, r ∈ a :: b :: c :: e :: cs := fun _ h ↦
  List.mem_cons_of_mem _ (sub3 b c e _ h)

/-- A register a block keeps (`Keeps`). -/
theorem kreg [Labels] {d d' : MachineData} {rs0 : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {Sy : SState} (hm : Match (Env.ofMachine d rs0 vs ret) Sy d')
    {rs : List Reg64} (h : Keeps Sy rs = true) {r : Reg64} (hr : r ∈ rs) : reg d' r = reg d r :=
  keeps_reg hm h hr

/-- The registers `Regs` reads, kept by a block keeping the callee-saved registers. -/
theorem Regs.keep [Labels] {m0 d d' : MachineData} {rs0 : List (BitVec 64 × Nat)}
    {vs : Nat → BitVec 64} {ret : BitVec 64} {Sy : SState} (h : Regs m0 d)
    (hm : Match (Env.ofMachine d rs0 vs ret) Sy d') {rs : List Reg64} (hK : Keeps Sy rs = true)
    (hs : ∀ r ∈ cs, r ∈ rs) : Regs m0 d' :=
  ⟨(kreg hm hK (hs _ (by simp [cs]))).trans h.rbx, (kreg hm hK (hs _ (by simp [cs]))).trans h.r12,
    (kreg hm hK (hs _ (by simp [cs]))).trans h.r14, (kreg hm hK (hs _ (by simp [cs]))).trans h.r15⟩

variable {m0 : MachineData}

/-- **The offsets placed, kept** by a change outside the output. -/
theorem OutAt.keep {j : Nat} {d d' : Mem 64} (h : OutAt m0 j d) (hcap : n m0 ≤ cap m0)
    (hno : NativeRustcVm.NoWrap (out m0) (8 * cap m0)) {X : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' X) (hX : ∀ q, X q → ¬ R m0 q) : OutAt m0 j d' :=
  fun i hi ↦ by
    have hin : i < n m0 := ord_mem (List.mem_of_mem_take hi)
    refine NativeRustcVm.Transcript.bytesAt_congr (h i hi) fun t ht ↦ hs _ fun hx ↦ hX _ hx ?_
    have ht8 : t < 8 := by simpa [NativeRustcVm.length_wordBytes] using ht
    rw [NativeRustcVm.addr_add]
    exact inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hno; omega)

/-- **The order array, kept** by a change outside the frame. -/
theorem ordw_keep (hst : StackOk m0 1344) (hn : n m0 ≤ 158) {d d' : Mem 64}
    (h : WordsAt d (ob m0) (natWords (ord m0))) {X : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' X)
    (hX : ∀ q, X q → ¬ NativeRustcVm.InRange (stackBelow m0 1328) (1328 + 8) q) :
    WordsAt d' (ob m0) (natWords (ord m0)) :=
  NativeRustcVm.Transcript.bytesAt_congr h fun t ht ↦ hs _ fun hx ↦ hX _ hx (by
    have : t < 8 * (natWords (ord m0)).length := by rwa [NativeRustcVm.length_wordsBytes] at ht
    simp only [natWords, List.length_map, Array.length_toList, ord_size] at this
    rw [ob_add]
    exact fb_in hst (by decide) (by omega))

variable [Host] {k : Nat}

/-- `b22`: a failure's jump to the epilogue. -/
theorem fail_end (hp : Placed code k) (hpre : StackOffsetsPre m0) {st : MachineState}
    (h : Fail k m0 st) : Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hpc, hb, hrax, hfit⟩ := h
  have hst : StackOk m0 1344 := hpre.1
  obtain ⟨hok, hmem, hK⟩ := ok_b22
  refine step0 hst (b22_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b22 nofun hpc hb hok hmem
    fun st1 hm1 hpc1 hb1 hd1 ↦ ?_
  obtain ⟨hok25, hmem25, hK25⟩ := ok_b25
  have hrax1 : reg st1.data .rax = 0#64 :=
    (kp hm1 hK (rs' := [Reg64.rax]) (by simp) .rax (by simp)).trans hrax
  refine hb1.done hst (by decide) (b25_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b25
    (hpc1.trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_21_at)) (match0 hb1) hok25 hmem25
    fun st2 hm2 hpc2 hrsp2 hsv2 hd2 ↦ ⟨hpc2, hrsp2, ?_, fun q hq ↦ by
      rw [hd2]; exact hb1.same q hq, hsv2⟩
  split
  · rename_i h; exact absurd h.2 hfit
  · exact (kp hm2 hK25 (rs' := [Reg64.rax]) (by simp) .rax (by simp)).trans hrax1

/-- **A turn of the main loop** from its head: the end, a failure or one more block placed. -/
theorem step (hp : Placed code k) (hpre : StackOffsetsPre m0) (hcap : n m0 ≤ cap m0) {j : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b18Offset)) (hL : Loop m0 j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ Fail k m0 s ∨ End k m0 s ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b18Offset) ∧ Loop m0 (j + 1) s.data)) st := by
  have hst : StackOk m0 1344 := hpre.1
  have hn : n m0 ≤ 158 := hpre.2.1
  have hoff : OffStack m0 (out m0) (8 * cap m0) 1344 := hpre.2.2.2.2.2.1
  have hno : NativeRustcVm.NoWrap (out m0) (8 * cap m0) := hpre.2.2.2.2.1.2
  have hsoff : OffStack m0 (reg m0 .rdi) (8 * n m0) 1344 := hpre.2.2.2.1
  have hsno : NativeRustcVm.NoWrap (reg m0 .rdi) (8 * n m0) := hpre.2.2.1.2
  have hfnw := fb_noWrap hst
  have hno' := hno
  have hsno' := hsno
  unfold NativeRustcVm.NoWrap at hfnw hno' hsno'
  -- `b18`: the end?
  obtain ⟨hok18, hmem18, hK18⟩ := ok_b18
  refine step0 hst (b18_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b18 nofun hpc hL.b hok18
    hmem18 fun st1 hm1 hpc1 hb1 hd1 ↦ ?_
  have hR1 : Regs m0 st1.data := hL.regs.keep hm1 hK18 (sub3 _ _ _)
  have hsi1 : (reg st1.data .rsi).toNat = 8 * j := by rw [kreg hm1 hK18 (by simp)]; exact hL.rsi
  have hdx1 : (reg st1.data .rdx).toNat = (P m0 j).2 := by
    rw [kreg hm1 hK18 (by simp)]; exact hL.rdx
  have hax1 : reg st1.data .rax = 0#64 := (kreg hm1 hK18 (by simp)).trans hL.rax
  have hbp1 : reg st1.data .rbp = BitVec.ofNat 64 (8 * n m0) :=
    (kreg hm1 hK18 (by simp [cs])).trans hL.rbp
  have hordw1 : WordsAt st1.data.dmem (ob m0) (natWords (ord m0)) := by rw [hd1]; exact hL.ordw
  have hout1 : OutAt m0 j st1.data.dmem := by rw [hd1]; exact hL.out
  simp only [PcOk] at hpc1
  obtain ⟨hy, hno1⟩ := pc_of (P := 8 * n m0 = 8 * j) hpc1 (by
    rw [eq_eval]
    have e1 : ((Sym.reg .rbp).eval (frameEnv m0 st.data 1328 [] (fun _ ↦ 0) 0)).toNat =
        8 * n m0 := by
      show (reg st.data .rbp).toNat = _
      rw [hL.rbp, lit_toNat (by omega)]
    have e2 : ((Sym.reg .rsi).eval (frameEnv m0 st.data 1328 [] (fun _ ↦ 0) 0)).toNat =
        8 * j := hL.rsi
    rw [e1, e2])
  by_cases hj : j = n m0
  · subst hj
    exact .done _ (Or.inr (Or.inl ⟨(hy rfl).trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_22_at),
      ⟨hb1, hR1, hL.le, hsi1, hbp1, hdx1, hax1, hordw1, hout1⟩⟩))
  have hjn : j < n m0 := by have := hL.le; omega
  have hjo : j < (ord m0).size := by rw [ord_size]; exact hjn
  have hi : (ord m0)[j] < n m0 := ord_lt hjo
  generalize hidef : (ord m0)[j] = i at hi
  -- `b19`: `i = order[j]`
  have hm19 : Match (frameEnv m0 st1.data 1328 [] (fun _ ↦ 0) 0) ordS st1.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb1.fr.rsp_eval, trivial⟩ trivial
      ⟨by show (reg st1.data .rsi).toNat < 1264; rw [hsi1]; omega, trivial⟩ trivial
  obtain ⟨hok19, hmem19, hcx19, hK19⟩ := ok_b19
  refine run0 hst (b19_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b19 nofun
    (hno1 (by omega)) hb1 hm19 hok19 fun st2 hm2 hpc2 hb2 ↦ ?_
  have hwf19 := fr_wf0 (vars := fun _ ↦ 0) (ret := 0) hb1 hst (by decide)
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf19 hmem19
  have hld : (Sym.loadx 0 16 (.reg .rsi) 8).eval (frameEnv m0 st1.data 1328 [] (fun _ ↦ 0) 0) =
      i.toUInt64.toBitVec := by
    show (frameEnv m0 st1.data 1328 [] (fun _ ↦ 0) 0).load 0 (16 + (reg st1.data .rsi).toNat)
      8 = _
    have hw := ord_word hordw1 hjo
    rw [ob_add, hidef] at hw
    rw [hsi1]
    exact load_ofMachine rfl hw
  have hi64 : i.toUInt64.toBitVec.toNat = i := toNat_toUInt64 (by omega)
  have hcx2 : (reg st2.data .rcx).toNat = i := by
    show (st2.data.regs.get64 .rcx).toNat = _
    rw [hm2.regs .rcx _ hcx19, hld, hi64]
  have hR2 : Regs m0 st2.data := hR1.keep hm2 hK19 (sub3 _ _ _)
  have hsi2 : (reg st2.data .rsi).toNat = 8 * j := by rw [kreg hm2 hK19 (by simp)]; exact hsi1
  have hdx2 : (reg st2.data .rdx).toNat = (P m0 j).2 := by
    rw [kreg hm2 hK19 (by simp)]; exact hdx1
  have hax2 : reg st2.data .rax = 0#64 := (kreg hm2 hK19 (by simp)).trans hax1
  have hbp2 : reg st2.data .rbp = BitVec.ofNat 64 (8 * n m0) :=
    (kreg hm2 hK19 (by simp [cs])).trans hbp1
  simp only [PcOk] at hpc2
  obtain ⟨-, hno2⟩ := pc_of (P := ¬ i < cap m0) hpc2 (by
    rw [SBool.eval, ult_eval, decide_not]
    have e1 : ((Sym.reg .rbx).eval (frameEnv m0 st1.data 1328 [] (fun _ ↦ 0) 0)).toNat =
        cap m0 := congrArg BitVec.toNat hR1.rbx
    rw [hld, hi64, e1])
  -- `b20`: `offsets[i] = total`
  have hma : NativeRustcVm.Mapped m0.dmem (out m0 + BitVec.ofNat 64 (8 * i)) 8 :=
    mapped_off (N := 8 * cap m0) hpre.2.2.2.2.1.1 (by omega)
  have hna : NativeRustcVm.NoWrap (out m0 + BitVec.ofNat 64 (8 * i)) 8 := by
    unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega
  have hfo := apart_fr hst hoff
  unfold NativeRustcVm.Apart at hfo
  have hapf : NativeRustcVm.Apart (stackBelow m0 1328) (1328 + 8)
      (out m0 + BitVec.ofNat 64 (8 * i)) 8 := by
    unfold NativeRustcVm.Apart; rw [toNat_off (by omega)]; omega
  have hm20 : Match (frameEnv m0 st2.data 1328 [(out m0 + BitVec.ofNat 64 (8 * i), 8)]
      (fun _ ↦ 0) 0) (oneS .r14 .rcx) st2.data := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb2.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨?_, trivial⟩
    beta_reduce
    rw [idx_eval]
    show reg st2.data .r14 + BitVec.ofNat 64 (8 * (reg st2.data .rcx).toNat) =
      out m0 + BitVec.ofNat 64 (8 * i) + BitVec.ofInt 64 0
    rw [ofInt_zero64, BitVec.add_zero, hcx2, hR2.r14]
  obtain ⟨hok20, hws20, hw20, hK20⟩ := ok_b20
  refine run1 hst (b20_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b20 nofun
    (hno2 (by omega)) hb2 hma hna hapf (fun q h ↦ Or.inl (R_sub hno (by omega) h)) hm20 hok20
    fun st3 hm3 hpc3 hwf3 hb3 ↦ ?_
  have hs3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
      (NativeRustcVm.InRange (out m0 + BitVec.ofNat 64 (8 * i)) 8) :=
    sameOutside_region hwf3 hm3 (r := 1) rfl hws20
  have hw3 := wordAt_write hm3 (r := 1) (o := 0) rfl (by decide)
    (fun t ht ↦ by simpa using hw20 t ht)
  have hv3 : ((Sym.reg .rdx).eval (frameEnv m0 st2.data 1328
      [(out m0 + BitVec.ofNat 64 (8 * i), 8)] (fun _ ↦ 0) 0)).toNat = (P m0 j).2 := hdx2
  rw [off_zero, u64_of hv3] at hw3
  have hout3 : OutAt m0 (j + 1) st3.data.dmem := by
    rw [hd2] at hs3
    exact hout1.step hjo hno hcap (hidef ▸ hw3) (hidef ▸ hs3)
  have hX3 : ∀ q, NativeRustcVm.InRange (out m0 + BitVec.ofNat 64 (8 * i)) 8 q →
      ¬ NativeRustcVm.InRange (stackBelow m0 1328) (1328 + 8) q := fun q h ↦
    R_not_frame hst hoff hno (R_sub hno (by omega) h)
  have hordw3 : WordsAt st3.data.dmem (ob m0) (natWords (ord m0)) := by
    rw [hd2] at hs3
    exact ordw_keep hst hn hordw1 hs3 hX3
  have hR3 : Regs m0 st3.data := hR2.keep hm3 hK20 (sub4 _ _ _ _)
  have hcx3 : (reg st3.data .rcx).toNat = i := by rw [kreg hm3 hK20 (by simp)]; exact hcx2
  have hsi3 : (reg st3.data .rsi).toNat = 8 * j := by rw [kreg hm3 hK20 (by simp)]; exact hsi2
  have hdx3 : (reg st3.data .rdx).toNat = (P m0 j).2 := by
    rw [kreg hm3 hK20 (by simp)]; exact hdx2
  have hax3 : reg st3.data .rax = 0#64 := (kreg hm3 hK20 (by simp)).trans hax2
  have hbp3 : reg st3.data .rbp = BitVec.ofNat 64 (8 * n m0) :=
    (kreg hm3 hK20 (by simp [cs])).trans hbp2
  simp only [PcOk] at hpc3
  obtain ⟨-, hno3⟩ := pc_of (P := ¬ i < n m0) hpc3 (by
    rw [SBool.eval, ult_eval, decide_not]
    have e1 : ((Sym.reg .rcx).eval (frameEnv m0 st2.data 1328
        [(out m0 + BitVec.ofNat 64 (8 * i), 8)] (fun _ ↦ 0) 0)).toNat = i := hcx2
    have e2 : ((Sym.reg .r15).eval (frameEnv m0 st2.data 1328
        [(out m0 + BitVec.ofNat 64 (8 * i), 8)] (fun _ ↦ 0) 0)).toNat = n m0 :=
      congrArg BitVec.toNat hR2.r15
    rw [e1, e2])
  -- `b21`: `sizes[i]`
  have hsa : NativeRustcVm.Mapped m0.dmem (reg m0 .rdi + BitVec.ofNat 64 (8 * i)) 8 :=
    mapped_off (N := 8 * n m0) hpre.2.2.1.1 (by omega)
  have hsn : NativeRustcVm.NoWrap (reg m0 .rdi + BitVec.ofNat 64 (8 * i)) 8 := by
    unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega
  have hfs := apart_fr hst hsoff
  unfold NativeRustcVm.Apart at hfs
  have hsf : NativeRustcVm.Apart (stackBelow m0 1328) (1328 + 8)
      (reg m0 .rdi + BitVec.ofNat 64 (8 * i)) 8 := by
    unfold NativeRustcVm.Apart; rw [toNat_off (by omega)]; omega
  have hwf21 := fr_wf1 (vars := fun _ ↦ 0) (ret := 0) hb3 hst (by decide) hsa hsn hsf
  have hm21 : Match (frameEnv m0 st3.data 1328 [(reg m0 .rdi + BitVec.ofNat 64 (8 * i), 8)]
      (fun _ ↦ 0) 0) (oneS .r12 .rcx) st3.data := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb3.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨?_, trivial⟩
    beta_reduce
    rw [idx_eval]
    show reg st3.data .r12 + BitVec.ofNat 64 (8 * (reg st3.data .rcx).toNat) =
      reg m0 .rdi + BitVec.ofNat 64 (8 * i) + BitVec.ofInt 64 0
    rw [ofInt_zero64, BitVec.add_zero, hcx3, hR3.r12]
  obtain ⟨hok21, hmem21, hcx21, hK21⟩ := ok_b21
  refine exec_at (b21_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b21 hwf21 nofun
    (hno3 (by omega)) hm21 fun st4 hm4 hpc4 ↦ ?_
  have hb4 : B m0 8 st4.data := hb3.of_read hwf21 hm4 hok21 slots_le hmem21
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf21 hmem21
  have hsz : ((Sym.load 1 0 8).eval (frameEnv m0 st3.data 1328
      [(reg m0 .rdi + BitVec.ofNat 64 (8 * i), 8)] (fun _ ↦ 0) 0)).toNat = size m0 i := by
    show ((frameEnv m0 st3.data 1328 [(reg m0 .rdi + BitVec.ofNat 64 (8 * i), 8)]
      (fun _ ↦ 0) 0).load 1 0 8).toNat = _
    rw [Arrays.load8_eq]
    show (wordOf st3.data.dmem (reg m0 .rdi + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 0)).toNat
      = _
    rw [NativeRustcVm.addr_add_zero, show size m0 i = _ from natsOf_getD m0 (reg m0 .rdi) hi]
    refine congrArg UInt64.toNat (NativeRustcVm.wordOf_congr fun t ht ↦ ?_)
    rw [NativeRustcVm.addr_add]
    exact hb3.same _ (sizes_out hpre (inRange_off_self (by omega) (by omega)))
  have hR4 : Regs m0 st4.data := hR3.keep hm4 hK21 (sub3 _ _ _)
  have hcx4 : (reg st4.data .rcx).toNat = size m0 i := by
    show (st4.data.regs.get64 .rcx).toNat = _
    rw [hm4.regs .rcx _ hcx21]; exact hsz
  have hsi4 : (reg st4.data .rsi).toNat = 8 * j := by rw [kreg hm4 hK21 (by simp)]; exact hsi3
  have hdx4 : (reg st4.data .rdx).toNat = (P m0 j).2 := by
    rw [kreg hm4 hK21 (by simp)]; exact hdx3
  have hax4 : reg st4.data .rax = 0#64 := (kreg hm4 hK21 (by simp)).trans hax3
  have hbp4 : reg st4.data .rbp = BitVec.ofNat 64 (8 * n m0) :=
    (kreg hm4 hK21 (by simp [cs])).trans hbp3
  simp only [PcOk] at hpc4
  obtain ⟨hy4, hno4⟩ := pc_of (P := size m0 i ≤ 63) hpc4 (by
    rw [SBool.eval, ult_eval, eq_eval, hsz]
    exact or63 _)
  have hsi : size m0 i = size m0 (ord m0)[j] := by rw [hidef]
  by_cases h63 : size m0 i ≤ 63
  swap
  · exact .done _ (Or.inl ⟨hno4 h63, hb4, hax4, not_fit_size hi (by omega)⟩)
  -- `b17`: the total plus `2 ^ size`
  obtain ⟨hok17, hmem17, hsx17, hdx17, hK17⟩ := ok_b17
  refine step0 hst (b17_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b17 nofun
    ((hy4 h63).trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_19_at)) hb4 hok17 hmem17 fun st5 hm5 hpc5 hb5 hd5 ↦ ?_
  have hshl : ((Sym.bin .shl .W64 (.lit 1) (.reg .rcx)).eval
      (frameEnv m0 st4.data 1328 [] (fun _ ↦ 0) 0)).toNat = 2 ^ size m0 i := by
    show (BinOp.apply .shl .W64 (BitVec.ofNat 64 1) (reg st4.data .rcx)).toNat = _
    rw [shl1 _ (by rw [hcx4]; omega), hcx4]
  have hdx4' : ((Sym.reg .rdx).eval (frameEnv m0 st4.data 1328 [] (fun _ ↦ 0) 0)).toNat =
      (P m0 j).2 := hdx4
  simp only [PcOk] at hpc5
  obtain ⟨hy5, hno5⟩ := pc_of (P := 2 ^ 64 ≤ 2 ^ size m0 i + (P m0 j).2) hpc5 (by
    rw [addC_eval, hshl, hdx4'])
  have hax5 : reg st5.data .rax = 0#64 := (kreg hm5 hK17 (by simp)).trans hax4
  by_cases hc : 2 ^ 64 ≤ 2 ^ size m0 i + (P m0 j).2
  · exact .done _ (Or.inl ⟨(hy5 hc).trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_20_at), hb5, hax5,
      not_fit_sum hjo (by rw [← hsi]; omega)⟩)
  refine .done _ (Or.inr (Or.inr ⟨hno5 hc, ⟨hb5, hR4.keep hm5 hK17 (sub1 _),
    by omega, ?_, (kreg hm5 hK17 (by simp [cs])).trans hbp4, ?_, hax5,
    (by rw [hd5, hd4]; exact hordw3), (by rw [hd5, hd4]; exact hout3)⟩⟩))
  · show (st5.data.regs.get64 .rsi).toNat = _
    rw [hm5.regs .rsi _ hsx17, litAdd_eval (r := .rsi) hsi4 (by omega) (by decide)]
    omega
  · show (st5.data.regs.get64 .rdx).toNat = _
    rw [hm5.regs .rdx _ hdx17]
    show (BinOp.apply .add .W64 _ _).toNat = _
    rw [add_eval (by rw [hshl, hdx4']; omega), hshl, hdx4', P_succ_snd hjo, ← hsi]
    omega

end

end NativeRustcVmX64.Layout.StackOffsets
