module

public import NativeRustcVmX64.Bus.GkrStep.Head
public import NativeRustcVmX64.Code.Vm.SumcheckOfGkrStep.Names

/-!
# `gkr_step`'s sumcheck (x86-64)

From `AtPE` (`b5`): the claim's limb `1` in R10, the loop `b6` zeroes the challenges' slots
`352` to `1360` (`zero_spec`); `b7` passes the point (`|point|` the stack arguments `0`, `2`, the
slots at `352` the stack argument `1`), `2^step + 1` and the claim to the sumcheck, its
`Option<EW>` at `112`; `b8` checks it (`sc_spec`, to `AtCh`).
-/

namespace NativeRustcVmX64.Bus.GkrStep

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Sumcheck (sumcheckFn)

public section

/-- An address with a negative offset: the alias of a region placed `c` above. -/
theorem add_ofInt_neg (x : BitVec 64) (c : Nat) :
    x = x + BitVec.ofNat 64 c + BitVec.ofInt 64 (-(c : Int)) := by
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast, ← BitVec.sub_eq_add_neg, BitVec.add_sub_cancel]

theorem ult64_all : ∀ n < 64,
    CmpOp.apply .ult .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 64) = true := by
  decide +kernel

theorem ult64 {n : Nat} (hn : n < 64) :
    CmpOp.apply .ult .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 64) = true := ult64_all n hn

theorem pow_step (x : BitVec 64) (h : x.toNat = 1 ∨ x.toNat = 2) :
    (BinOp.apply .shl .W64 (BitVec.ofNat 64 1) (UnOp.apply .trunc .W32 x)).toNat = 2 ^ x.toNat ∧
      (BinOp.apply .bts .W64 (BitVec.ofNat 64 1) x).toNat = 2 ^ x.toNat + 1 := by
  rcases h with h | h
  · obtain rfl : x = 1#64 := BitVec.eq_of_toNat_eq h
    decide
  · obtain rfl : x = 2#64 := BitVec.eq_of_toNat_eq h
    decide

theorem eq64 (x : BitVec 64) (v : Nat) (hv : v < 2 ^ 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 v) = decide (x.toNat = v) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv]

/-- The registers the zeroing loop keeps. -/
abbrev zkeep : List Reg64 := .rsp :: .rax :: .r10 :: cs6

/-- **The zeroing loop's invariant**, `i` rounds done from `d0`. -/
structure ZInv [Labels] (m0 d0 : MachineData) (i : Nat) (d : MachineData) : Prop where
  fr : FR m0 40 d
  rcx : (reg d .rcx).toNat = 40 + 48 * i
  keep : ∀ r ∈ zkeep, reg d r = reg d0 r
  kept : Kept d0.dmem d.dmem
  same : NativeRustcVm.SameOutside d0.dmem d.dmem (NativeRustcVm.InRange (off (fb m0) 352) 1008)

variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- **A round of the zeroing loop** (`b6`). -/
theorem zero_step (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {d0 : MachineData} {i : Nat}
    (hi : i ≤ 20) {d : MachineData} (inv : ZInv m0 d0 i d) :
    Eventually (step1 Host.exe) (fun st ↦ (i = 20 ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b7Offset) ∧
      ZInv m0 d0 (i + 1) st.data) ∨ (i < 20 ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b6Offset) ∧
        ZInv m0 d0 (i + 1) st.data)) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b6Offset)⟩ := by
  have hS := pre_stack h
  have hN := N_ge
  have e1 := hS.1
  have e2 := hS.2.1
  have cx := ctxF h 1408 N_ge
  have hfb : (fb m0).toNat = (rspOf m0).toNat - 1408 := stackBelow_toNat (by omega)
  have hrcx : reg d .rcx = BitVec.ofNat 64 (40 + 48 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [inv.rcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbase : reg d .rsp + reg d .rcx + BitVec.ofNat 64 272 = off (fb m0) (352 + 48 * i) := by
    rw [show reg d .rsp = rspOf d from rfl, inv.fr.frame.sp, hrcx, off_add, off_off]
    congr 1
    omega
  have hmp := cx.mapped_frame inv.fr.frame.kept
  have hwf : (Env.ofMachine d [(off (fb m0) (352 + 48 * i), 48)]).WF :=
    Env.wf_of ⟨⟨mapped_off hmp (by omega), by
      show (off (fb m0) (352 + 48 * i)).toNat + 48 ≤ 2 ^ 64
      rw [toNat_off (by omega)]; omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine d [(off (fb m0) (352 + 48 * i), 48)]) zS d := by
    refine match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨?_, trivial⟩
    show BinOp.apply .add .W64 (reg d .rsp) (reg d .rcx) =
      off (fb m0) (352 + 48 * i) + BitVec.ofInt 64 (-272)
    rw [← hbase]
    simp only [BinOp.apply, low_W64, ext_W64]
    exact add_ofInt_neg _ 272
  refine exec_then (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf nofun hm
    fun st hm' hpc ↦ ?_
  obtain ⟨hw, hrc, hk⟩ := ok_b6
  have hs : NativeRustcVm.SameOutside d.dmem st.data.dmem
      (NativeRustcVm.InRange (off (fb m0) (352 + 48 * i)) 48) :=
    sameOutside_region hwf hm' (r := 0) rfl fun w hw' ↦ ⟨(hw w hw').1, Nat.zero_le _, (hw w hw').2⟩
  have hs'' : NativeRustcVm.SameOutside d.dmem st.data.dmem
      (NativeRustcVm.InRange (off (fb m0) 352) 1008) :=
    NativeRustcVm.SameOutside.mono hs fun q hq ↦ by
      rw [inRange_toNat (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)] at hq
      rw [inRange_toNat (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)]
      omega
  have hs' : NativeRustcVm.SameOutside d.dmem st.data.dmem (NativeRustcVm.InRange (fb m0) 1360) :=
    NativeRustcVm.SameOutside.mono hs'' fun q hq ↦ by
      rw [inRange_toNat (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)] at hq
      rw [inRange_toNat (by omega)]
      omega
  have hkept : Kept d.dmem st.data.dmem := hm'.kept hwf
  have hkr : ∀ r ∈ zkeep, reg st.data r = reg d r := fun r hr ↦ kr hm' hk hr
  have fr' : FR m0 40 st.data :=
    FR.local h inv.fr (hkr .rsp (by simp)) (fun r hr ↦ hkr r (by
      cases r <;> simp_all [calleeSaved])) hkept hs'
  have hrcx' : (reg st.data .rcx).toNat = 40 + 48 * (i + 1) := by
    rw [rv hm' hrc]
    show (BinOp.apply .add .W64 (BitVec.ofNat 64 48) (reg d .rcx)).toNat = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, inv.rcx]
    omega
  have inv' : ZInv m0 d0 (i + 1) st.data :=
    ⟨fr', hrcx', fun r hr ↦ (hkr r hr).trans (inv.keep r hr), kept_trans inv.kept hkept,
      NativeRustcVm.SameOutside.mono (inv.same.trans hs'') fun q hq ↦ hq.elim id id⟩
  have hc : SBool.eval (Env.ofMachine d [(off (fb m0) (352 + 48 * i), 48)])
      (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 48) (.reg .rcx)) (.lit 1048)).not =
        decide (i ≠ 20) := by
    show (!CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 48) (reg d .rcx))
      (BitVec.ofNat 64 1048)) = _
    rw [eq64 _ _ (by decide)]
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, inv.rcx]
    by_cases h20 : i = 20
    · subst h20; decide
    · simp only [h20, ne_eq, not_false_eq_true, decide_true]
      rw [Nat.mod_eq_of_lt (by omega)]
      simp; omega
  simp only [PcOk, hc] at hpc
  by_cases h20 : i = 20
  · simp only [h20, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc
    exact .done _ (.inl ⟨h20, hpc.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b6_next), by subst h20; exact inv'⟩)
  · simp only [h20, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hpc
    exact .done _ (.inr ⟨by omega, hpc.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_2_at), inv'⟩)

/-- **The zeroing loop** from its first round. -/
theorem zero_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {d0 : MachineData}
    (inv : ZInv m0 d0 0 d0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b7Offset) ∧
      ZInv m0 d0 21 st.data) ⟨d0, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b6Offset)⟩ := by
  refine loop (I := fun n st ↦ ∃ i, n = 20 - i ∧ i ≤ 20 ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b6Offset) ∧
    ZInv m0 d0 i st.data)
    (fun n st ⟨i, hn, hi, hpc, hinv⟩ ↦ at_pc hpc (Eventually.mono (zero_step hp h hi hinv)
      fun st' hs ↦ ?_)) ⟨0, rfl, by omega, rfl, inv⟩
  rcases hs with ⟨h20, hpc', hinv'⟩ | ⟨hlt, hpc', hinv'⟩
  · subst h20; exact .inl ⟨hpc', hinv'⟩
  · exact .inr ⟨20 - (i + 1), by omega, i + 1, rfl, by omega, hpc', hinv'⟩

/-- **The sumcheck** (`b5` to `b8`), from `AtPE`. -/
theorem sc_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hsc : ∀ s pt n, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfGkrStep.entryLabel) (SumcheckGkrPre a s pt n)
      (SumcheckGkrPost a s pt n))
    (hch : ∀ c cl xs s2 d, AtCh a s0 g0 m0 c cl xs s2 d →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b9Offset)⟩)
    {d : MachineData} (at5 : AtPE a s0 g0 m0 d) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b5Offset)⟩ := by
  have hS := pre_stack h
  have hN := N_ge
  have e1 := hS.1
  have e2 := hS.2.1
  have cx := ctxF h 1408 N_ge
  have c0 := ctxF h (1408 - 0) (by omega)
  have hfb : (fb m0).toNat = (rspOf m0).toNat - 1408 := stackBelow_toNat (by omega)
  set t := reg m0 .rdi with ht
  set p := reg m0 .rcx with hpdef
  set c := s0.sponge.squeeze.1 with hc
  set s1 : TState := { s0 with sponge := s0.sponge.squeeze.2 } with hs1
  set L := g0.point.size with hL
  have hstep := pre_step h
  have hLle : L + (reg m0 .rsi).toNat ≤ 63 := pre_size h
  have hgb : gkrStateBytes = 1064 := rfl
  have hgnw : p.toNat + 1064 ≤ 2 ^ 64 := (pre_gk h).2.1
  -- `b5`
  have hwf5 := wf0 h at5.fr.frame.kept 0
  obtain ⟨hmid5, hmem5, hr105, hcx5, hk5⟩ := ok_b5
  refine exec_then (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf5 nofun
    (match_head at5.fr 0) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨fr5, hd5⟩ := FR.block_nil h at5.fr hwf5 hm5 hmid5 hmem5
  simp only [PcOk] at hpc5
  have inv0 : ZInv m0 st5.data 0 st5.data :=
    ⟨fr5, by rw [rv hm5 hcx5]; rfl, fun _ _ ↦ rfl, fun _ h ↦ h, fun _ _ ↦ rfl⟩
  refine at_pc (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b5_next))
    (Eventually.bind (zero_spec hp h inv0) fun st6 ⟨hpc6, inv6⟩ ↦ ?_)
  have hd6 : ∀ {bs : List UInt8} {o : Nat}, o + bs.length ≤ 352 →
      NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st6.data.dmem (off (fb m0) o) bs := by
    intro bs o ho hb
    rw [← hd5] at hb
    refine NativeRustcVm.BytesAt.of_sameOutside hb inv6.same fun i hi hq ↦ ?_
    rw [off_add, inRange_toNat (by rw [fb_off_toNat hS hN (by omega)]; omega),
      fb_off_toNat hS hN (by omega), fb_off_toNat hS hN (by omega)] at hq
    omega
  have hkeep6 : ∀ r, r ∈ zkeep → r ∈ (Reg64.rax :: cs6) → reg st6.data r = reg d r :=
    fun r h1 h2 ↦ (inv6.keep r h1).trans (kr hm5 hk5 h2)
  have hts6 : TStateAt st6.data.dmem t a s1 :=
    tsKeep h inv6.kept inv6.same (fun q hq ↦ .inl (fbo_stack h (by omega) hq))
      (by rw [hd5]; exact at5.ts)
  have hgs6 : GkrStateWAt st6.data.dmem p g0 :=
    gsKeep h inv6.same (fun q hq ↦ .inl (fbo_stack h (by omega) hq))
      (by rw [hd5]; exact at5.gs)
  -- `b7`: the sumcheck's arguments.
  have hwf7 := wfS h inv6.fr.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b7Offset + b7.length)).toBitVec
  obtain ⟨hmid7, hw7, w8, w16, w24, w96, hdi7, hsi7, hdx7, hcx7, hr87, hr97, hr127, hr137, hr147,
    hk7⟩ := ok_b7
  have e14 : reg st6.data .r14 = p := (hkeep6 .r14 (by simp) (by simp)).trans at5.r14
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf7 (fun _ _ ↦ rfl) hpc6
    (match_sS inv6.fr e14 _) fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨fr7, hs7⟩ := FR.block h inv6.fr hwf7 hm7 hmid7 (.inr rfl) (W01_of_W0 hw7) (by decide)
    (by omega)
  have hs7' : NativeRustcVm.SameOutside st6.data.dmem st7.data.dmem
      (NativeRustcVm.InRange (fb m0) 1360) :=
    NativeRustcVm.SameOutside.mono hs7 fun q hq ↦ hq.elim id fun hq ↦
      absurd hq (by unfold NativeRustcVm.InRange; omega)
  have hts7 : TStateAt st7.data.dmem t a s1 :=
    tsKeep h (hm7.kept hwf7) hs7' (fun q hq ↦ .inl (fb_stack h (inRange_mono hq (by omega)))) hts6
  have hgs7 : GkrStateWAt st7.data.dmem p g0 :=
    gsKeep h hs7' (fun q hq ↦ .inl (fb_stack h (inRange_mono hq (by omega)))) hgs6
  have hw7' := W0_spec hw7
  have keep7 : ∀ {bs : List UInt8} {o : Nat}, 104 ≤ o → o + bs.length ≤ 1408 →
      NativeRustcVm.BytesAt st6.data.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st7.data.dmem (off (fb m0) o) bs := fun ho hob hb ↦
    keepB hwf7 hm7 (.inr (.inr hmid7)) hob (fun w hw _ ↦ by
      obtain ⟨-, q, hq, h1, h2⟩ := hw7' w hw
      simp at hq; rcases hq with rfl | rfl <;> omega) hb
  have keep7' : ∀ {bs : List UInt8}, 44 + bs.length ≤ 96 →
      NativeRustcVm.BytesAt st6.data.dmem (off (fb m0) 44) bs →
      NativeRustcVm.BytesAt st7.data.dmem (off (fb m0) 44) bs := fun hob hb ↦
    keepB hwf7 hm7 (.inr (.inr hmid7)) (by omega) (fun w hw _ ↦ by
      obtain ⟨-, q, hq, h1, h2⟩ := hw7' w hw
      simp at hq; rcases hq with rfl | rfl <;> omega) hb
  -- the values in `b7`'s environment
  set E7 := frameEnv m0 st6.data 1408 [(p, 1064)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b7Offset + b7.length)).toBitVec with hE7
  have hlw : NativeRustcVm.WordAt st6.data.dmem (off p 48) L.toUInt64 := by
    have := hgs6.point.2.1
    rwa [Array.length_toList] at this
  have hld : E7.load 1 48 8 = BitVec.ofNat 64 L := load_ofMachine (r := 1) rfl hlw
  have hlen : lenS.eval E7 = BitVec.ofNat 64 L := by
    show (if CmpOp.apply .ult .W64 (E7.load 1 48 8) (BitVec.ofNat 64 64) then E7.load 1 48 8
      else BitVec.ofNat 64 0) = _
    rw [hld, ult64 (by omega)]
    rfl
  have hr9 : (Sym.ite (.cmp .ult .W64 (.load 1 48 8) (.lit 64)) (.ptr 1 56) (.lit 8)).eval E7 =
      off p 56 := by
    show (if CmpOp.apply .ult .W64 (E7.load 1 48 8) (BitVec.ofNat 64 64) then
      E7.base 1 + BitVec.ofInt 64 56 else BitVec.ofNat 64 8) = _
    rw [hld, ult64 (by omega)]
    rfl
  have ebx6 : reg st6.data .rbx = reg m0 .rsi := (hkeep6 .rbx (by simp) (by simp)).trans at5.rbx
  have hpw : (powS.eval E7).toNat = 2 ^ (reg m0 .rsi).toNat := by
    have := (pow_step (reg m0 .rsi) hstep).1
    rw [← ebx6] at this ⊢
    exact this
  have hcnt : ((Sym.bin .bts .W64 (.lit 1) (.reg .rbx)).eval E7).toNat = 2 ^ (reg m0 .rsi).toNat + 1 := by
    have := (pow_step (reg m0 .rsi) hstep).2
    rw [← ebx6] at this ⊢
    exact this
  have hsp7 : rspOf st7.data = off (fb m0) 0 := fr7.frame.sp
  have W8 := wordAt_write hm7 (r := 0) (o := 8) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
    (by omega) w8
  have W16 := wordAt_write hm7 (r := 0) (o := 16) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
    (by omega) w16
  have W24 := wordAt_write hm7 (r := 0) (o := 24) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
    (by omega) w24
  rw [hlen] at W8 W24
  have a0 : stackArg st7.data 0 = BitVec.ofNat 64 L :=
    stackArg_of (c := 0) hsp7 (i := 0) W8
  have a1 : stackArg st7.data 1 = off (fb m0) 352 := by
    rw [stackArg_of (c := 0) hsp7 (i := 1) W16]
    show (Sym.ptr 0 352).eval E7 = _
    exact eval_ptr0 352
  have a2 : stackArg st7.data 2 = BitVec.ofNat 64 L :=
    stackArg_of (c := 0) hsp7 (i := 2) W24
  have hLt : (BitVec.ofNat 64 L).toNat = L := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have edi7 : reg st7.data .rdi = off (fb m0) 112 := (rv hm7 hdi7).trans (eval_ptr0 112)
  have esi7 : reg st7.data .rsi = t :=
    (rv hm7 hsi7).trans ((hkeep6 .r15 (by simp) (by simp)).trans at5.r15)
  have edx7 : reg st7.data .rdx = (polyEval g0.values c).c0.toBitVec :=
    (rv hm7 hdx7).trans ((hkeep6 .rax (by simp) (by simp)).trans
      (at5.rax : reg d .rax = (polyEval g0.values c).c0.toBitVec))
  have ecx7 : reg st7.data .rcx = (polyEval g0.values c).c1.toBitVec :=
    (rv hm7 hcx7).trans ((inv6.keep .r10 (by simp)).trans ((rv hm5 hr105).trans
      (at5.rdx : reg d .rdx = (polyEval g0.values c).c1.toBitVec)))
  have er87 : (reg st7.data .r8).toNat = 2 ^ (reg m0 .rsi).toNat + 1 := by rw [rv hm7 hr87]; exact hcnt
  have er97 : reg st7.data .r9 = off p 56 := (rv hm7 hr97).trans hr9
  -- the sumcheck's precondition
  have hat7 := atC h (by omega) fr7
  have hle7 := le0
  have hgo7 := c0.outOk hat7 hle7 (pre_gk h)
  have hpow2 : 2 ≤ 2 ^ (reg m0 .rsi).toNat + 1 ∧ 2 ^ (reg m0 .rsi).toNat + 1 ≤ maxCount := by
    rcases hstep with e | e <;> rw [e] <;> decide
  have hptw : NativeRustcVm.EWsAt st7.data.dmem (off p 56) g0.point.toList := by
    have := hgs7.point.2.2
    rwa [show off p 48 + 8#64 = off p 56 from off_add _ _ _] at this
  have hfbo : ∀ {o n : Nat}, o + n ≤ 1408 → (off (fb m0) o).toNat = (fb m0).toNat + o := by
    intro o n hon; exact toNat_off (by omega)
  have hpapart : NativeRustcVm.Apart p 1064 (stackBelow m0 1408) (1408 + 8) :=
    apart_frame (pre_gk h).2.2.2.2.1 cx.spN N_ge
  have hrsp8 : (rspOf st7.data + 8#64).toNat = (fb m0).toNat + 8 := by
    rw [hsp7, off_zero, BitVec.toNat_add, show (8#64).toNat = 8 from rfl]; omega
  have hpre7 : SumcheckGkrPre a s1 g0.point L st7.data := by
    unfold SumcheckGkrPre SumcheckOk
    rw [esi7, edi7, a0, a1, a2, er87, er97, hLt]
    have hpa : NativeRustcVm.Apart p 1064 t tstateBytes := (pre_gk h).2.2.1
    have hpS := hgo7.2.2.2.2.1
    have htp : NativeRustcVm.Apart t tstateBytes (stackBelow m0 1408) (1408 + 8) :=
      apart_frame cx.tok.1 cx.spN N_ge
    rw [hgb] at hpS
    unfold NativeRustcVm.Apart at hpa htp hpapart
    unfold NativeRustcX64.Apart at hpS
    rw [← hpdef] at hpS
    have h56 : (off p 56).toNat = p.toNat + 56 := toNat_off (by omega)
    have h112 := hfbo (o := 112) (n := 24) (by omega)
    have h352 := hfbo (o := 352) (n := 16 * L) (by omega)
    have hfb' : (stackBelow m0 1408).toNat = (fb m0).toNat := rfl
    have hra : rspOf st7.data + 8#64 = off (fb m0) 8 := by rw [hsp7]; exact off_add _ _ _
    refine ⟨⟨by rw [hra]; exact mapped_off (cx.mapped_frame fr7.frame.kept) (by omega), ?_⟩,
      ⟨c0.stackOk hat7 hle7, c0.rcAt hat7 hle7, hts7,
      c0.tstateOk hat7 hle7, hpow2.1, hpow2.2, outFb h fr7 hle7 (by omega) (by omega),
      outFb h fr7 hle7 (by omega) (by omega), ?_, got_atC h (by omega) fr7 hle7 ?_⟩,
      rfl, hptw, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · rw [hsp7, off_zero]; omega
    · unfold NativeRustcX64.Apart; rw [h112, h352]; omega
    · intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · rw [ht]
        exact ((pre_got h).1 l hl).2.2.2 (reg m0 .rdi, tstateBytes) (by simp)
      · exact ((pre_got h).1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
      · exact got_apart_frame (pre_got h) h.1 hl N_ge (by omega)
      · exact got_apart_frame (pre_got h) h.1 hl N_ge (by omega)
      · exact ((pre_got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)
    · unfold NativeRustcX64.NoWrap; rw [h56]; omega
    · unfold NativeRustcX64.Apart; rw [h56]; omega
    · unfold NativeRustcX64.Apart; rw [h56]; omega
    · unfold NativeRustcX64.Apart; rw [h56, h352]; omega
    · unfold NativeRustcX64.Apart; rw [hrsp8]; omega
    · unfold NativeRustcX64.Apart; rw [hrsp8, h352]; omega
  -- the sumcheck
  have fbin : ∀ {o n o' n' : Nat}, o ≤ o' → o' + n' ≤ o + n → o + n ≤ 1408 → ∀ q,
      NativeRustcVm.InRange (off (fb m0) o') n' q → NativeRustcVm.InRange (off (fb m0) o) n q := by
    intro o n o' n' h1 h2 h3 q hq
    rcases Nat.eq_zero_or_pos n' with h0 | h0
    · subst h0; exact absurd hq (by unfold NativeRustcVm.InRange; omega)
    rw [inRange_toNat (by rw [fb_off_toNat hS hN (by omega)]; omega),
      fb_off_toNat hS hN (by omega)] at hq
    rw [inRange_toNat (by rw [fb_off_toNat hS hN (by omega)]; omega),
      fb_off_toNat hS hN (by omega)]
    omega
  simp only [PcOk] at hpc7
  refine Fr.call (c := 0) (Nc := sumcheckGkrStack) (lo := 112) (len := 1248)
    (X := fun q ↦ NativeRustcVm.InRange (off (fb m0) 112) 24 q ∨
      NativeRustcVm.InRange (off (fb m0) 352) (16 * L) q ∨ NativeRustcVm.InRange t tstateBytes q)
    hS hN (by omega) hle7 (slots_call (by omega) (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (fbin (by omega) (by omega) (by omega) q hq)
      · exact .inr (fbin (by omega) (by omega) (by omega) q hq)
      · exact .inl (.inl hq))
    (hsc s1 g0.point L) fr7 hpc7 hpre7 (fun m' hq ↦ ⟨?_, hq.2.2⟩)
    fun m8 fr8 hq8 hs8 hcs8 ↦ ?_
  · have := hq.2.1
    rw [edi7, a1, esi7] at this
    exact NativeRustcVm.SameOutside.mono this fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inr (.inl hq)
      · exact .inr (.inr (.inl hq))
      · exact .inr (.inr (.inr hq))
      · exact .inl hq
  obtain ⟨⟨hopt, hslw, hnext⟩, -, hsv8⟩ := hq8
  have hcl : claimArg st7.data = polyEval g0.values c := by
    unfold claimArg; rw [edx7, ecx7]
  rw [edi7, hcl, er87] at hopt
  rw [a1, hcl, er87] at hslw
  rw [esi7, hcl, er87] at hnext
  have hrun : run0 s0 g0 m0 = ((sumcheckFn (polyEval g0.values c) (2 ^ (reg m0 .rsi).toNat + 1)
      (fun i ↦ g0.point[i]?) L).run s1).bind fun x ↦
        gkrChildren (reg m0 .rsi).toNat c x.1.2 x.1.1 x.2 := by
    unfold run0
    rw [gkrStep_run' _ _ _ _ (by omega)]
    rfl
  -- `b8`: the sumcheck's tag.
  have hwf8 := wf0 h fr8.frame.kept 0
  obtain ⟨hmid8, hmem8, hk8⟩ := ok_b8
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf8 nofun
    (show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b7Offset + b7.length) = _ by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b7_next)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨fr8.frame.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨fr9, hd9⟩ := FR.block_nil h fr8 hwf8 hm9 hmid8 hmem8
  simp only [PcOk] at hpc9
  have hcal8 : ∀ q, NativeRustcVm.InRange (stackBelow st7.data sumcheckGkrStack)
      sumcheckGkrStack q → NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q :=
    fun q hq ↦ calleeStack h (by omega) fr7 hle7 hq
  have hXf : ∀ {o n : Nat}, (o + n ≤ 112) → ∀ i < n, ¬ (NativeRustcVm.InRange (off (fb m0) 112) 24
      (off (fb m0) (o + i)) ∨ NativeRustcVm.InRange (off (fb m0) 352) (16 * L) (off (fb m0) (o + i)) ∨
      NativeRustcVm.InRange t tstateBytes (off (fb m0) (o + i))) := by
    intro o n hon i hi hq
    rcases hq with hq | hq | hq
    · exact fbo_apart h (o := 112) (n := 24) (o' := o + i) (n' := 1) (by omega) (by omega)
        (by omega) hq (NativeRustcVm.inRange_self (by omega))
    · exact fbo_apart h (o := 352) (n := 16 * L) (o' := o + i) (n' := 1) (by omega) (by omega)
        (by omega) hq (NativeRustcVm.inRange_self (by omega))
    · exact fb_not_outs h (by omega) (.inl hq)
  have ebx7 : reg st7.data .rbx = reg m0 .rsi := (kr hm7 hk7 (by simp)).trans ebx6
  have e157 : reg st7.data .r15 = t := (kr hm7 hk7 (by simp)).trans
    ((hkeep6 .r15 (by simp) (by simp)).trans at5.r15)
  have ebp7 : reg st7.data .rbp = c.c1.toBitVec := (kr hm7 hk7 (by simp)).trans
    ((hkeep6 .rbp (by simp) (by simp)).trans at5.rbp)
  have e127 : (reg st7.data .r12).toNat = 2 ^ (reg m0 .rsi).toNat := by rw [rv hm7 hr127]; exact hpw
  have e137 : reg st7.data .r13 = BitVec.ofNat 64 L := (rv hm7 hr137).trans hlen
  have e147 : reg st7.data .r14 = p := (rv hm7 hr147).trans (eval_ptr rfl)
  have r9 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st9.data r = reg st7.data r := by
    intro r hr
    have hcs : calleeSaved r = true := by
      simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    exact (kr hm9 hk8 (by simp at hr ⊢; tauto)).trans (hcs8 r hcs)
  have l44 : NativeRustcVm.BytesAt st9.data.dmem (off (fb m0) 44)
      ((List.range 4).map (byteOf (reg m0 .rdx))) := by
    rw [hd9]
    exact keepCall h fr7 hle7 hs8 (by omega) (by simp) (hXf (by simp))
      (keep7' (by simp) (hd6 (by simp) at5.l44))
  have c104 : NativeRustcVm.WordAt st9.data.dmem (off (fb m0) 104) c.c0 := by
    rw [hd9]
    exact keepCallW h fr7 hle7 hs8 (by omega) (by omega) (hXf (by omega))
      (keep7 (by omega) (by rw [NativeRustcVm.length_wordBytes]; omega)
        (hd6 (by rw [NativeRustcVm.length_wordBytes]; omega) at5.c104))
  have pa9 : NativeRustcVm.WordAt st9.data.dmem (off (fb m0) 96) (UInt64.ofBitVec (off p 56)) := by
    have W96 := wordAt_write hm7 (r := 0) (o := 96) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
      (by omega) w96
    rw [show (Sym.ptr 1 56).eval E7 = off p 56 from rfl] at W96
    rw [hd9]
    exact keepCallW h fr7 hle7 hs8 (by omega) (by omega) (hXf (by omega)) W96
  have hgs9 : GkrStateWAt st9.data.dmem p g0 := by
    rw [hd9]
    refine gsKeep h hs8 (fun q hq ↦ ?_) hgs7
    rcases hq with hq | hq | hq | hq
    · exact .inl (hcal8 q hq)
    · exact .inl (fbo_stack h (by omega) hq)
    · exact .inl (fbo_stack h (by omega) hq)
    · exact .inr hq
  cases hres : (sumcheckFn (polyEval g0.values c) (2 ^ (reg m0 .rsi).toNat + 1)
      (fun i ↦ g0.point[i]?) L).run s1 with
  | none =>
    rw [hres] at hopt
    have hl : (frameEnv m0 m8 1408 [] (fun _ ↦ 0) 0).load 0 112 4 = BitVec.ofNat 64 0 :=
      load4_of_tag (w := 0) (.inl rfl) hopt
    have hc : SBool.eval (frameEnv m0 m8 1408 [] (fun _ ↦ 0) 0)
        (SBool.cmp .eq .W32 (.load 0 112 4) (.lit 1)).not = true := by
      show (!CmpOp.apply .eq .W32 ((frameEnv m0 m8 1408 [] (fun _ ↦ 0) 0).load 0 112 4)
        (BitVec.ofNat 64 1)) = true
      rw [hl]; rfl
    simp only [hc, ↓reduceIte] at hpc9
    exact at_pc (hpc9.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_17_at))
      (fail_spec hp h fr9 (by rw [hrun, hres]; rfl))
  | some r =>
    obtain ⟨⟨xs, cl⟩, s2⟩ := r
    rw [hres] at hopt hnext
    obtain ⟨ht1, hcw⟩ := (hopt : OptEWAt m8.dmem (off (fb m0) 112) (some cl))
    have hl : (frameEnv m0 m8 1408 [] (fun _ ↦ 0) 0).load 0 112 4 = BitVec.ofNat 64 1 :=
      load4_of_tag (w := 1) (.inr rfl) ht1
    have hc : SBool.eval (frameEnv m0 m8 1408 [] (fun _ ↦ 0) 0)
        (SBool.cmp .eq .W32 (.load 0 112 4) (.lit 1)).not = false := by
      show (!CmpOp.apply .eq .W32 ((frameEnv m0 m8 1408 [] (fun _ ↦ 0) 0).load 0 112 4)
        (BitVec.ofNat 64 1)) = false
      rw [hl]; rfl
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc9
    have hxs : xs.size = L := sumcheckFn_size _ _ _ L (by simp only [StateT.run] at hres; exact hres)
    rw [off_off] at hcw
    refine at_pc (hpc9.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b8_next)) (hch c cl xs s2 st9.data
      ⟨fr9, ?_, ?_, ?_, ?_, ?_, ?_, l44, c104, by rw [hd9]; exact hcw, pa9,
        by rw [hd9]; exact hslw xs cl s2 hres, by rw [hxs]; exact hLle,
        by rw [hd9]; exact hnext (xs, cl) s2 rfl, hgs9, by rw [hrun, hres]; rfl⟩)
    · rw [r9 .rbx (by simp)]; exact ebx7
    · rw [r9 .r12 (by simp)]; exact e127
    · rw [r9 .r13 (by simp), e137, hxs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [r9 .r14 (by simp)]; exact e147
    · rw [r9 .r15 (by simp)]; exact e157
    · rw [r9 .rbp (by simp)]; exact ebp7

end

end NativeRustcVmX64.Bus.GkrStep
