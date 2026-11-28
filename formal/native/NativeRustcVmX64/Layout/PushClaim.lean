module

public import NativeRustcVmX64.Layout.PushClaim.Exec
public import NativeRustcVm.Layout.RepLemmas
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names

/-!
# `push_claim` on x86-64

No room (`cs.size = 160`): `b0` branches to `b4`, which returns AL = `0` (`full`). Room (`room`):
one environment of the entry state for `b0`, `b1` (the frame, the count word, the next claim
`slot c n`), up to the call of `Buf<EW, 36>::extend` on the point; one of the state it returns
in for `b2` and `b3` (pushed, AL = `1`) or `b5` (the point too long, AL = `0`), then `b6`, the
epilogue.
-/

namespace NativeRustcVmX64.Layout.PushClaim

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PushClaim NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Layout
open NativeRustcVmX64.Layout.Stack (and8_eval le_false wordAt_writesW eval_ptr_off)

public section

/-- The next claim's address. -/
abbrev slot (c : BitVec 64) (n : Nat) : BitVec 64 := off c (8 + 608 * n)

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide

theorem stack_eq : pushClaimStack = 56 := rfl

theorem ofInt_neg8 : (BitVec.ofInt 64 (-8)).toNat = 2 ^ 64 - 8 := by
  rw [BitVec.toNat_ofInt]; omega

/-- `rdi + count · 608`: the next claim less `8`. -/
theorem alias_eq (c : BitVec 64) (n : Nat) :
    c + BitVec.ofNat 64 n * BitVec.ofNat 64 608 =
      c + BitVec.ofNat 64 (8 + 608 * n) + BitVec.ofInt 64 (-8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_add, ofInt_neg8,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `16 + (count · 608 + rdi)`: the point's buffer. -/
theorem rdi_eq (c : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 16 + (BitVec.ofNat 64 n * BitVec.ofNat 64 608 + c) = off (slot c n) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- `8 + (r15 + r12)`: the claim. -/
theorem ret_eq (c : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 8 + (c + BitVec.ofNat 64 n * BitVec.ofNat 64 608) =
      slot c n + BitVec.ofInt 64 0 := by
  rw [ofInt_zero64, BitVec.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

variable [Host] {k : Nat}

/-- **No room**: `b0` branches to `b4`, which returns AL = `0`. -/
theorem full (hp : Placed code k) (cs : Array ColumnClaimW) {m0 : MachineData}
    (hpre : PushClaimPre cs m0) (hn : ¬cs.size < claimCap) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
      PushClaimPost cs m0 st.data) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.PushClaim.b0Offset)⟩ := by
  obtain ⟨hst, hC, ⟨hcm, hcn⟩, hcs, -, -⟩ := hpre
  rw [stack_eq] at hst hcs
  set c := reg m0 .rdi with hcdef
  have hn160 : cs.size = 160 := by have := hC.len_le; unfold claimCap at *; omega
  have hR := hst.1
  have h8 := hst.2.1
  have hsb := stackBelow_toNat (m := m0) (n := 56) hR
  have hsb0 := stackBelow_toNat (m := m0) (n := 0) (by omega)
  have hcN : c.toNat + 97288 ≤ 2 ^ 64 := hcn
  have hcs' : c.toNat + 97288 ≤ (stackBelow m0 56).toNat ∨
      (stackBelow m0 56).toNat + (56 + 8) ≤ c.toNat := hcs
  have hwf := frame_wf (m0 := m0) (d := m0) (F := 0) (rest := [(c, 8)]) (vars := fun _ ↦ 0)
    (ret := 0) ⟨frame_mapped hst (by decide), frame_noWrap hst (by decide)⟩
    (fun x hx ↦ by
      obtain rfl := List.mem_singleton.mp hx
      exact ⟨fun i hi ↦ hcm i (by unfold claimsBytes columnClaimBytes claimCap; omega),
        by show c.toNat + 8 ≤ 2 ^ 64; omega⟩)
    (List.pairwise_pair.mpr (by
      show (stackBelow m0 0).toNat + (0 + 8) ≤ c.toNat ∨ c.toNat + 8 ≤ (stackBelow m0 0).toNat
      omega))
  have hm : Match (frameEnv m0 m0 0 [(c, 8)] (fun _ ↦ 0) 0) fullS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  have hl : (frameEnv m0 m0 0 [(c, 8)] (fun _ ↦ 0) 0).load 1 0 8 = BitVec.ofNat 64 160 := by
    have := load_ofMachine (m := m0) (rs := (stackBelow m0 0, 0 + 8) :: [(c, 8)]) (vs := fun _ ↦ 0)
      (ret := 0) (r := 1) (o := 0) rfl (by rw [off_zero]; exact hC.len)
    rw [this, hn160]; rfl
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_full hwf nofun hm
    fun st1 hm1 hpc1 ↦ ?_
  have hc : fullSym.eval (frameEnv m0 m0 0 [(c, 8)] (fun _ ↦ 0) 0) = true := by
    simp only [fullSym, SBool.eval, Sym.eval, hl]; decide
  simp only [PcOk] at hpc1
  rw [hc] at hpc1
  simp (config := { decide := true }) only [↓reduceIte] at hpc1
  rw [hp.label NativeRustcVmX64.Vm.PushClaim.label_1_at] at hpc1
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf nofun hpc1 hm1
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := ok_b4
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue Frame.entry hwf hm2 hepi
  have hd : st2.data.dmem = m0.dmem := hm2.dmem_eq hwf hmem
  simp only [PcOk] at hpc2
  refine .done _ ⟨by rw [hpc2]; exact Frame.entry.load_ret hst (by decide), hrsp, ?_, ?_, hsv⟩
  · simp only [hn, false_and, ↓reduceIte]
    show (reg st2.data .rax).toNat % 256 = 0
    rw [show reg st2.data .rax = _ from hm2.regs .rax _ hrax]; rfl
  · intro q _; rw [hd]

/-- **Room**: `b0`, `b1`, the call, then `b2` and `b3` or `b5`, and `b6`. -/
theorem room (hp : Placed code k) (cs : Array ColumnClaimW)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {m0 : MachineData} (hpre : PushClaimPre cs m0) (hn : cs.size < claimCap) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
      PushClaimPost cs m0 st.data) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.PushClaim.b0Offset)⟩ := by
  obtain ⟨hst, hC, ⟨hcm, hcn⟩, hcs, ⟨⟨hpm, hpn⟩, hps⟩, hcp⟩ := hpre
  rw [stack_eq] at hst hcs hps
  set c := reg m0 .rdi with hcdef
  set p := reg m0 .rdx with hpdef
  set n := cs.size with hndef
  set fb := stackBelow m0 48 with hfbdef
  have hn' : n < 160 := hn
  have hR := hst.1
  have h8 := hst.2.1
  have hsbN := stackBelow_toNat (m := m0) (n := 56) hR
  have hfbN : fb.toNat = (rspOf m0).toNat - 48 := stackBelow_toNat (by omega)
  have hcN : c.toNat + 97288 ≤ 2 ^ 64 := hcn
  have hcs' : c.toNat + 97288 ≤ (stackBelow m0 56).toNat ∨
      (stackBelow m0 56).toNat + (56 + 8) ≤ c.toNat := hcs
  have hpN : p.toNat + 16 * (reg m0 .rcx).toNat ≤ 2 ^ 64 := hpn
  have hps' : p.toNat + 16 * (reg m0 .rcx).toNat ≤ (stackBelow m0 56).toNat ∨
      (stackBelow m0 56).toNat + (56 + 8) ≤ p.toNat := hps
  have hcp' : c.toNat + 97288 ≤ p.toNat ∨ p.toNat + 16 * (reg m0 .rcx).toNat ≤ c.toNat := hcp
  rw [hsbN] at hcs' hps'
  have hsN : (slot c n).toNat = c.toNat + 8 + 608 * n := by
    rw [toNat_off (by omega)]; omega
  have hs8N : (off (slot c n) 8).toNat = c.toNat + 16 + 608 * n := by
    rw [toNat_off (by omega), hsN]; omega
  have hfnw : NativeRustcVm.NoWrap fb (48 + 8) := frame_noWrap hst (by decide)
  have hcnw : NativeRustcVm.NoWrap c 97288 := hcn
  -- The claims are apart from the frame and the stack; the point from both.
  have hClF : ∀ q, NativeRustcVm.InRange c 97288 q → ¬ NativeRustcVm.InRange fb (48 + 8) q :=
    fun q h1 h2 ↦ not_inRange_of_apart (by unfold NativeRustcVm.Apart; omega) hcnw hfnw h1 h2
  have hClS : ∀ q, NativeRustcVm.InRange c 97288 q →
      ¬ NativeRustcVm.InRange (stackBelow m0 56) (56 + 8) q :=
    fun q h1 h2 ↦ not_inRange_of_apart hcs hcnw (noWrap_stackBelow hst) h1 h2
  have hinC : ∀ {o l : Nat} {q : BitVec 64}, o + l ≤ 97288 →
      NativeRustcVm.InRange (off c o) l q → NativeRustcVm.InRange c 97288 q :=
    fun hle h ↦ inRange_of_off hcnw hle h
  have hinS : ∀ {o l : Nat} {q : BitVec 64}, 8 + 608 * n + o + l ≤ 97288 →
      NativeRustcVm.InRange (off (slot c n) o) l q → NativeRustcVm.InRange c 97288 q :=
    fun hle h ↦ by rw [off_off] at h; exact hinC (by omega) h
  have hcm8 : NativeRustcVm.Mapped m0.dmem c 8 := fun i hi ↦ hcm i (by
    unfold claimsBytes columnClaimBytes claimCap; omega)
  have hsm : NativeRustcVm.Mapped m0.dmem (slot c n) 608 :=
    mapped_off hcm (by unfold claimsBytes columnClaimBytes claimCap; omega)
  have hok1 : NativeRustcVm.Mapped m0.dmem c 8 ∧ NativeRustcVm.NoWrap c 8 :=
    ⟨hcm8, by unfold NativeRustcVm.NoWrap; omega⟩
  have hok2 : NativeRustcVm.Mapped m0.dmem (slot c n) 608 ∧ NativeRustcVm.NoWrap (slot c n) 608 :=
    ⟨hsm, by unfold NativeRustcVm.NoWrap; rw [hsN]; omega⟩
  have hap : [(fb, 48 + 8), (c, 8), (slot c n, 608)].Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2 :=
    pairwise3 (by unfold NativeRustcVm.Apart; dsimp only; omega)
      (by unfold NativeRustcVm.Apart; dsimp only; rw [hsN]; omega)
      (by unfold NativeRustcVm.Apart; dsimp only; rw [hsN]; omega)
  -- `b0`, `b1`: the entry's environment.
  set env0 := frameEnv m0 m0 48 [(c, 8), (slot c n, 608)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.PushClaim.b1Offset + b1.length)).toBitVec with henv0
  have hwf0 : env0.WF := frame_wf ⟨frame_mapped hst (by decide), hfnw⟩
    (rest2_ok hok1 hok2 fun _ h ↦ h) hap
  have hcnt0 : env0.load 1 0 8 = BitVec.ofNat 64 n :=
    load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hC.len)
  have e1 : (Sym.ptr 1 0).eval env0 = c := eval_ptr rfl
  have halias : slotX.eval env0 = env0.base 2 + BitVec.ofInt 64 (-8) := by
    show BinOp.apply .add .W64 ((Sym.ptr 1 0).eval env0)
      (BinOp.apply .mul .W64 (env0.load 1 0 8) (BitVec.ofNat 64 608)) = slot c n + _
    rw [e1, hcnt0]
    simp only [BinOp.apply, low_W64, ext_W64]
    exact alias_eq c n
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial
      trivial ⟨halias, trivial⟩
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st0 hm1 hpc1 ↦ ?_
  have hc0 : fullSym.eval env0 = false := by
    simp only [fullSym, SBool.eval, Sym.eval, hcnt0]
    exact le_false _ 159 (by decide) (by rw [BitVec.toNat_ofNat]; omega)
  simp only [PcOk] at hpc1
  rw [hc0] at hpc1
  simp (config := { decide := true }) only [↓reduceIte] at hpc1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf0 (fun _ _ ↦ rfl)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PushClaim.b0_next)) hm1 fun st1 hm2 hpc2 ↦ ?_
  obtain ⟨hpro, hws1, hW1, hrdi, hrsi, hrdx, hr15, hr12, hr14, hrbx⟩ := ok_b1
  have hf1 : Frame m0 48 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm2 hpro slots_le (by decide)
  have hsp1 : rspOf st1.data = fb := by rw [hf1.sp, off_zero]
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (fun q ↦ NativeRustcVm.InRange fb 48 q ∨ NativeRustcVm.InRange (slot c n) 16 q) := by
    have h := sameOutside_W2 hwf0 hm2 (r := 0) (r' := 2) rfl rfl
      (W := fun j ↦ j < 48) (W' := fun j ↦ j < 16) fun w hw ↦ by
        rcases hws1 w hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact .inl ⟨h1, by omega, fun j _ hj ↦ by omega⟩
        · exact .inr ⟨h1, by omega, fun j _ hj ↦ by omega⟩
    refine NativeRustcVm.Transcript.SameOutside.mono h fun q hq ↦ ?_
    rcases hq with ⟨j, -, hj, rfl⟩ | ⟨j, -, hj, rfl⟩
    · exact .inl (inRange_off_self hj (by omega))
    · exact .inr (inRange_off_self hj (by omega))
  have hX7 : reg st1.data .rdi = off (slot c n) 8 := by
    refine (hm2.regs .rdi _ hrdi).trans ?_
    show BinOp.apply .add .W64 (BitVec.ofNat 64 16) (BinOp.apply .add .W64
      (BinOp.apply .mul .W64 (env0.load 1 0 8) (BitVec.ofNat 64 608)) ((Sym.ptr 1 0).eval env0)) = _
    rw [hcnt0, e1]
    simp only [BinOp.apply, low_W64, ext_W64]
    exact rdi_eq c n
  have hX6 : reg st1.data .rsi = p := hm2.regs .rsi _ hrsi
  have hX2 : reg st1.data .rdx = reg m0 .rcx := hm2.regs .rdx _ hrdx
  have hX15 : reg st1.data .r15 = c := (hm2.regs .r15 _ hr15).trans e1
  have hX12 : reg st1.data .r12 = BitVec.ofNat 64 n * BitVec.ofNat 64 608 := by
    refine (hm2.regs .r12 _ hr12).trans ?_
    show BinOp.apply .mul .W64 (env0.load 1 0 8) (BitVec.ofNat 64 608) = _
    rw [hcnt0]
    simp only [BinOp.apply, low_W64, ext_W64]
  have hX14 : reg st1.data .r14 = reg m0 .r8 := hm2.regs .r14 _ hr14
  have hX3 : reg st1.data .rbx = reg m0 .r9 := hm2.regs .rbx _ hrbx
  have hcol1 := wordAt_writesW hm2 (r := 2) rfl hW1 (o := 0) (v := .reg .rsi) (by simp)
    (by decide)
  have hbuf1 := wordAt_writesW hm2 (r := 2) rfl hW1 (o := 8) (v := .lit 0) (by simp) (by decide)
  have hw0 : (NativeRustcVm.wordOf st1.data.dmem (off (slot c n) 8)).toNat = 0 := by
    rw [NativeRustcVm.wordOf_of_wordAt hbuf1]; rfl
  -- Bytes of the claims before the next one, and the point, untouched by `b1`.
  have hcnt1 : NativeRustcVm.WordAt st1.data.dmem c n.toUInt64 :=
    NativeRustcVm.BytesAt.of_sameOutside hC.len hs1 fun i hi h ↦ by
      have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
      have hq : (c + BitVec.ofNat 64 i).toNat = c.toNat + i := toNat_off (by omega)
      rcases h with h | h
      · exact hClF _ (inRange_off_self (b := c) (j := i) (by omega) (by omega))
          (inRange_mono h (by omega))
      · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hsN]; omega), hsN, hq] at h
        omega
  have hpF : ∀ i < 16 * (reg m0 .rcx).toNat,
      (p + BitVec.ofNat 64 i).toNat = p.toNat + i := fun i hi ↦ toNat_off (by omega)
  have hptS : ∀ i < 16 * (reg m0 .rcx).toNat,
      ¬ NativeRustcVm.InRange (stackBelow m0 56) (56 + 8) (p + BitVec.ofNat 64 i) := fun i hi h ↦ by
    rw [inRange_iff' (noWrap_stackBelow hst), hsbN, hpF i hi] at h; omega
  have hptF : ∀ i < 16 * (reg m0 .rcx).toNat,
      ¬ NativeRustcVm.InRange fb (48 + 8) (p + BitVec.ofNat 64 i) := fun i hi h ↦ by
    rw [inRange_iff' hfnw, hfbN, hpF i hi] at h; omega
  have hptC : ∀ i < 16 * (reg m0 .rcx).toNat,
      ¬ NativeRustcVm.InRange c 97288 (p + BitVec.ofNat 64 i) := fun i hi h ↦ by
    rw [inRange_iff' hcnw, hpF i hi] at h; omega
  have hslice : slice st1.data p (reg m0 .rcx) = slice m0 p (reg m0 .rcx) := by
    unfold slice
    exact congrArg List.toArray (NativeRustcVm.ewsOf_congr fun i hi ↦ hs1 _ fun h ↦ h.elim
      (fun h' ↦ hptF i hi (inRange_mono h' (by omega)))
      fun h' ↦ hptC i hi (hinC (o := 8 + 608 * n) (by omega) h'))
  -- `Buf<EW, 36>::extend` on the point.
  have hpreE : BufEWExtendPre 36 st1.data := by
    show StackOk _ 8 ∧ (NativeRustcVm.wordOf st1.data.dmem (reg st1.data .rdi)).toNat ≤ 36 ∧
      Readable _ (reg st1.data .rdi) (8 + 16 * 36) ∧
      Readable _ (reg st1.data .rsi) (16 * (reg st1.data .rdx).toNat) ∧
      Apart (reg st1.data .rdi) (8 + 16 * 36) (reg st1.data .rsi) (16 * (reg st1.data .rdx).toNat) ∧
      OffStack _ (reg st1.data .rdi) (8 + 16 * 36) 8 ∧
      OffStack _ (reg st1.data .rsi) (16 * (reg st1.data .rdx).toNat) 8
    rw [hX7, hX6, hX2, hw0]
    have hcb : (stackBelow st1.data 8).toNat = (rspOf m0).toNat - 56 := by
      rw [stackBelow_callee hsp1 (by omega), stackBelow_toNat (by omega)]
    refine ⟨stackOk_callee hst hf1.kept hsp1 (by decide), by decide, ⟨fun i hi ↦ ?_, ?_⟩,
      ⟨Mapped.keeps hpm hf1.kept, hpn⟩, ?_, ?_, ?_⟩
    · rw [off_add, off_off]
      exact hf1.kept _ (hcm _ (by unfold claimsBytes columnClaimBytes claimCap; omega))
    · show (off (slot c n) 8).toNat + _ ≤ _; rw [hs8N]; omega
    · show _ + _ ≤ p.toNat ∨ p.toNat + _ ≤ _; rw [hs8N]; omega
    · show _ + _ ≤ (stackBelow st1.data 8).toNat ∨ (stackBelow st1.data 8).toNat + _ ≤ _
      rw [hs8N, hcb]; omega
    · show _ + _ ≤ (stackBelow st1.data 8).toNat ∨ (stackBelow st1.data 8).toNat + _ ≤ _
      rw [hcb]; omega
  refine call_then hpc2 hext hpreE fun st2 hpc3 hrsp3 ⟨hres, hch, hsv⟩ ↦ ?_
  rw [hX7, hX6, hX2, hw0, Nat.zero_add, hslice] at hres
  rw [hX7] at hch
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st1.data bufEWExtendStack) bufEWExtendStack q →
      NativeRustcVm.InRange (stackBelow m0 56) 56 q ∧ ¬ NativeRustcVm.InRange fb (48 + 8) q :=
    fun q hq ↦ inRange_callee hsp1 h8 hR (by decide) hq
  have hchC : ∀ q, (NativeRustcVm.InRange (off (slot c n) 8) (8 + 16 * 36) q ∨
      NativeRustcVm.InRange (stackBelow st1.data bufEWExtendStack) bufEWExtendStack q) →
      (NativeRustcVm.InRange c 97288 q ∨ NativeRustcVm.InRange (stackBelow m0 56) 56 q) := by
    rintro q (h | h)
    · exact .inl (hinS (by omega) h)
    · exact .inr (hcal q h).1
  have hf2 : Frame m0 48 slots 8 st2.data :=
    Frame.call hf1 hsv hrsp3 hch (fun q hq ↦ by
      rcases hq with h | h
      · exact hClF q (hinS (by omega) h)
      · exact (hcal q h).2) hfnw slots_le
  have hso2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem
      (fun q ↦ NativeRustcVm.InRange c claimsBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 pushClaimStack) pushClaimStack q) := fun q hq ↦ by
    rw [hch q fun h ↦ hq (hchC q h)]
    exact hs1 q fun h ↦ hq (h.elim (fun h' ↦ .inr (inRange_frame_stack h8 hR (by decide) h'))
      fun h' ↦ .inl (hinC (o := 8 + 608 * n) (by omega) h'))
  have hkeepC : ∀ {a : BitVec 64} {bs : List UInt8}, NativeRustcVm.BytesAt st1.data.dmem a bs →
      (∀ i < bs.length, NativeRustcVm.InRange c 97288 (a + BitVec.ofNat 64 i) ∧
        ¬ NativeRustcVm.InRange (off (slot c n) 8) (8 + 16 * 36) (a + BitVec.ofNat 64 i)) →
      NativeRustcVm.BytesAt st2.data.dmem a bs := fun h hin ↦
    NativeRustcVm.BytesAt.of_sameOutside h hch fun i hi h' ↦ h'.elim (hin i hi).2
      fun h'' ↦ hClS _ (hin i hi).1 (inRange_mono (hcal _ h'').1 (by omega))
  have hcnt2 : NativeRustcVm.WordAt st2.data.dmem c n.toUInt64 := hkeepC hcnt1 fun i hi ↦ by
    have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
    have hq : (c + BitVec.ofNat 64 i).toNat = c.toNat + i := toNat_off (by omega)
    refine ⟨inRange_off_self (b := c) (j := i) (by omega) (by omega), fun h ↦ ?_⟩
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hs8N]; omega), hs8N, hq] at h; omega
  have hcol2 : NativeRustcVm.WordAt st2.data.dmem (slot c n) (UInt64.ofBitVec (reg m0 .rsi)) := by
    have hcol1' : NativeRustcVm.WordAt st1.data.dmem (slot c n) (UInt64.ofBitVec (reg m0 .rsi)) := by
      rw [off_zero] at hcol1; exact hcol1
    refine hkeepC hcol1' fun i hi ↦ ?_
    have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
    have hq : (slot c n + BitVec.ofNat 64 i).toNat = c.toNat + 8 + 608 * n + i := by
      rw [toNat_off (by omega), hsN]
    refine ⟨?_, fun h ↦ ?_⟩
    · rw [show slot c n + BitVec.ofNat 64 i = off c (8 + 608 * n + i) from off_add c _ i]
      exact inRange_off_self (b := c) (by omega) (by omega)
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hs8N]; omega), hs8N, hq] at h; omega
  have hX15₂ : reg st2.data .r15 = c := (hsv.1 .r15 rfl).trans hX15
  have hX12₂ : reg st2.data .r12 = BitVec.ofNat 64 n * BitVec.ofNat 64 608 :=
    (hsv.1 .r12 rfl).trans hX12
  have hX14₂ : reg st2.data .r14 = reg m0 .r8 := (hsv.1 .r14 rfl).trans hX14
  have hX3₂ : reg st2.data .rbx = reg m0 .r9 := (hsv.1 .rbx rfl).trans hX3
  -- From the return: `b2`.
  set envC := frameEnv m0 st2.data 48 [(c, 8), (slot c n, 608)] (fun _ ↦ 0) 0 with henvC
  have hwfC : envC.WF := frame_wf ⟨Mapped.keeps (frame_mapped hst (by decide)) hf2.kept, hfnw⟩
    (rest2_ok hok1 hok2 hf2.kept) hap
  have hcntC : envC.load 1 0 8 = BitVec.ofNat 64 n :=
    load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hcnt2)
  have e1C : (Sym.ptr 1 0).eval envC = c := eval_ptr rfl
  have haliasC : retX.eval envC = envC.base 2 + BitVec.ofInt 64 0 := by
    show BinOp.apply .add .W64 (BitVec.ofNat 64 8) (BinOp.apply .add .W64 ((Sym.ptr 1 0).eval envC)
      (st2.data.regs.get64 .r12)) = slot c n + _
    rw [e1C, show st2.data.regs.get64 .r12 = _ from hX12₂]
    simp only [BinOp.apply, low_W64, ext_W64]
    exact ret_eq c n
  have hmC : Match envC retS st2.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, known_ptr rfl hX15₂, trivial⟩ trivial
      trivial ⟨haliasC, trivial⟩
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwfC nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PushClaim.b1_next)) hmC fun st3 hm3 hpc4 ↦ ?_
  have hc2 : failSym.eval envC = decide ((reg st2.data .rax).toNat % 256 = 0) := by
    simp only [failSym, SBool.eval, Sym.eval]
    exact and8_eval _
  simp only [PcOk] at hpc4
  rw [hc2] at hpc4
  have hchanges : ∀ {d : MachineData}, NativeRustcVm.SameOutside st2.data.dmem d.dmem
      (fun q ↦ NativeRustcVm.InRange c 8 q ∨ NativeRustcVm.InRange (off (slot c n) 592) 16 q) →
      Changes m0 d pushClaimStack c claimsBytes := fun hd q hq ↦ by
    rw [hd q fun h ↦ hq (.inl (h.elim (fun h' ↦ inRange_mono h' (by decide))
      fun h' ↦ hinS (by omega) h'))]
    exact hso2 q hq
  by_cases hlenp : (reg m0 .rcx).toNat ≤ 36
  · -- Pushed: `b3`, `b6`.
    simp only [hlenp, ↓reduceIte] at hres
    obtain ⟨hb1, hbufw⟩ := hres
    rw [show (reg st2.data .rax).toNat % 256 = 1 from hb1] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwfC nofun
      (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PushClaim.b2_next)) hm3 fun st4 hm4 hpc5 ↦ ?_
    simp only [PcOk] at hpc5
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6a hwfC nofun
      (hpc5.trans (hp.label NativeRustcVmX64.Vm.PushClaim.label_6_at)) hm4 fun st5 hm5 hpc6 ↦ ?_
    obtain ⟨hepi, hws6, hW61, hW62, hrax6⟩ := end_b6a
    obtain ⟨hsv5, hrsp5⟩ := Frame.epilogue hf2 hwfC hm5 hepi
    have hs5 : NativeRustcVm.SameOutside st2.data.dmem st5.data.dmem
        (fun q ↦ NativeRustcVm.InRange c 8 q ∨ NativeRustcVm.InRange (off (slot c n) 592) 16 q) := by
      have h := sameOutside_W2 hwfC hm5 (r := 1) (r' := 2) rfl rfl
        (W := fun j ↦ j < 8) (W' := fun j ↦ 592 ≤ j ∧ j < 608) fun w hw ↦ by
          rcases hws6 w hw with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
          · exact .inl ⟨h1, by omega, fun j _ hj ↦ by omega⟩
          · exact .inr ⟨h1, by omega, fun j hj hj' ↦ ⟨by omega, by omega⟩⟩
      refine NativeRustcVm.Transcript.SameOutside.mono h fun q hq ↦ ?_
      rcases hq with ⟨j, -, hj, rfl⟩ | ⟨j, -, hj, rfl⟩
      · exact .inl (inRange_off_self hj (by omega))
      · exact .inr ((inRange_off_iff (by omega) (by omega)).mpr ⟨hj.1, by omega⟩)
    simp only [PcOk] at hpc6
    refine .done _ ⟨by rw [hpc6]; exact hf2.load_ret hst (by decide), hrsp5, ?_, hchanges hs5,
      hsv5⟩
    have hlenp' : (reg m0 .rcx).toNat ≤ pointCap := hlenp
    have hcond : cs.size < claimCap ∧ (reg m0 .rcx).toNat ≤ pointCap := ⟨hn, hlenp'⟩
    simp only [hcond]
    refine ⟨?_, ?_⟩
    · show (reg st5.data .rax).toNat % 256 = 1
      rw [show reg st5.data .rax = _ from hm5.regs .rax _ hrax6]
      exact merge_one_mod _
    -- The count word, one more.
    have hcnt5 : NativeRustcVm.WordAt st5.data.dmem c (n + 1).toUInt64 := by
      have h := wordAt_writesW hm5 (r := 1) rfl hW61 (List.mem_singleton_self _) (by decide)
      rw [off_zero] at h
      refine (congrArg (NativeRustcVm.WordAt st5.data.dmem c) ?_).mp h
      apply UInt64.toBitVec_inj.mp
      show BinOp.apply .add .W64 (envC.load 1 0 8) (BitVec.ofNat 64 1) = BitVec.ofNat 64 (n + 1)
      rw [hcntC, BitVec.ofNat_add]
      simp only [BinOp.apply, low_W64, ext_W64]
    -- The earlier claims: apart from every write.
    have hold : ∀ i < cs.size, Same m0.dmem st5.data.dmem (off c (8 + columnClaimBytes * i))
        columnClaimBytes := by
      intro i hi
      have hq : ∀ j < 608, (off c (8 + columnClaimBytes * i) + BitVec.ofNat 64 j).toNat =
          c.toNat + 8 + 608 * i + j := fun j hj ↦ by
        rw [off_add, toNat_off (by unfold columnClaimBytes; omega)]
        unfold columnClaimBytes; omega
      have hinq : ∀ j < 608, NativeRustcVm.InRange c 97288
          (off c (8 + columnClaimBytes * i) + BitVec.ofNat 64 j) := fun j hj ↦ by
        rw [off_add]; exact inRange_off_self (by unfold columnClaimBytes; omega) (by omega)
      have hns : ∀ {o l : Nat}, 8 + 608 * n + o + l ≤ 97288 → 0 < l → ∀ j < 608,
          ¬ NativeRustcVm.InRange (off (slot c n) o) l
            (off c (8 + columnClaimBytes * i) + BitVec.ofNat 64 j) := by
        intro o l hle hl0 j hj h
        have ho : (off (slot c n) o).toNat = c.toNat + 8 + 608 * n + o := by
          rw [off_off, toNat_off (b := c) (j := 8 + 608 * n + o) (by omega)]; omega
        rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [ho]; omega), ho, hq j hj] at h
        omega
      refine ((Same.of_sameOutside hs1 fun j hj h ↦ ?_).trans
        (Same.of_sameOutside hch fun j hj h ↦ ?_)).trans (Same.of_sameOutside hs5 fun j hj h ↦ ?_)
      · rcases h with h | h
        · exact hClF _ (hinq j hj) (inRange_mono h (by omega))
        · exact hns (o := 0) (l := 16) (by omega) (by decide) j hj (by rw [off_zero]; exact h)
      · rcases h with h | h
        · exact hns (by omega) (by decide) j hj h
        · exact hClS _ (hinq j hj) (inRange_mono (hcal _ h).1 (by omega))
      · rcases h with h | h
        · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq j hj] at h; omega
        · exact hns (by omega) (by decide) j hj h
    -- The new claim.
    have hkeep5 : ∀ {o l : Nat}, 8 ≤ o → o + l ≤ 592 →
        Same st2.data.dmem st5.data.dmem (off (slot c n) o) l := by
      intro o l ho hl
      refine Same.of_sameOutside hs5 fun j hj h ↦ ?_
      have hq : (off (slot c n) o + BitVec.ofNat 64 j).toNat = c.toNat + 8 + 608 * n + o + j := by
        rw [off_add, off_off, toNat_off (b := c) (j := 8 + 608 * n + (o + j)) (by omega)]; omega
      have h592 : (off (slot c n) 592).toNat = c.toNat + 8 + 608 * n + 592 := by
        rw [off_off, toNat_off (b := c) (j := 8 + 608 * n + 592) (by omega)]; omega
      rcases h with h | h
      · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq] at h; omega
      · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [h592]; omega), h592, hq] at h
        omega
    have hcol5 : NativeRustcVm.WordAt st5.data.dmem (slot c n) (UInt64.ofBitVec (reg m0 .rsi)) := by
      refine NativeRustcVm.BytesAt.of_sameOutside hcol2 hs5 fun i hi h ↦ ?_
      have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
      have hq : (slot c n + BitVec.ofNat 64 i).toNat = c.toNat + 8 + 608 * n + i := by
        rw [toNat_off (by omega), hsN]
      rcases h with h | h
      · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hq] at h; omega
      · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega), hsN]; omega),
          toNat_off (by omega), hsN, hq] at h
        omega
    have hbufE : NativeRustcVm.bufEWOf st1.data.dmem (off (slot c n) 8) = [] := by
      unfold NativeRustcVm.bufEWOf; rw [hw0]; rfl
    rw [hbufE, List.nil_append] at hbufw
    have hpt5 : NativeRustcVm.BufEWAt st5.data.dmem (off (slot c n) 8) pointCap
        (slice m0 p (reg m0 .rcx)).toList :=
      NativeRustcVm.Layout.BufEWAt.of_same hbufw (hkeep5 (o := 8) (l := 584) le_rfl le_rfl)
        (by decide)
    have w592 := wordAt_writesW hm5 (r := 2) rfl hW62 (o := 592) (v := .reg .r14) (by simp)
      (by decide)
    have w600 := wordAt_writesW hm5 (r := 2) rfl hW62 (o := 600) (v := .reg .rbx) (by simp)
      (by decide)
    rw [show (Sym.reg .r14).eval envC = reg m0 .r8 from hX14₂] at w592
    rw [show (Sym.reg .rbx).eval envC = reg m0 .r9 from hX3₂] at w600
    exact ClaimsWAt.push hC hn hcnt5 hold
      ⟨(reg m0 .rsi).isLt, Stack.wordAt_nat hcol5 rfl, hpt5,
        NativeRustcVm.Transcript.ewAt_iff.mpr ⟨w592, by rw [off_off]; exact w600⟩⟩
  · -- Too long: `b5`, `b6`.
    simp only [hlenp, ↓reduceIte] at hres
    rw [show (reg st2.data .rax).toNat % 256 = 0 from hres] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwfC nofun
      (hpc4.trans (hp.label NativeRustcVmX64.Vm.PushClaim.label_4_at)) hm3 fun st4 hm4 hpc5 ↦ ?_
    simp only [PcOk] at hpc5
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6b hwfC nofun
      (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PushClaim.b5_next)) hm4 fun st5 hm5 hpc6 ↦ ?_
    obtain ⟨hepi, hmem6, hrax6⟩ := end_b6b
    obtain ⟨hsv5, hrsp5⟩ := Frame.epilogue hf2 hwfC hm5 hepi
    have hd5 : st5.data.dmem = st2.data.dmem := hm5.dmem_eq hwfC hmem6
    simp only [PcOk] at hpc6
    refine .done _ ⟨by rw [hpc6]; exact hf2.load_ret hst (by decide), hrsp5, ?_,
      hchanges fun q _ ↦ by rw [hd5], hsv5⟩
    have hlenp' : ¬(reg m0 .rcx).toNat ≤ pointCap := hlenp
    have hcond : ¬(cs.size < claimCap ∧ (reg m0 .rcx).toNat ≤ pointCap) := fun h ↦ hlenp' h.2
    simp only [hcond, ↓reduceIte]
    show (reg st5.data .rax).toNat % 256 = 0
    rw [show reg st5.data .rax = _ from hm5.regs .rax _ hrax6]; rfl

/-- **`push_claim`'s contract.** -/
theorem pushClaim_spec (hp : Placed code k)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    (cs : Array ColumnClaimW) :
    Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs) := by
  intro m0 hpre
  unfold NativeRustcVmX64.Vm.PushClaim.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.PushClaim.entry_at]
  by_cases hn : cs.size < claimCap
  · exact room hp cs hext hpre hn
  · exact full hp cs hpre hn

end

end NativeRustcVmX64.Layout.PushClaim
