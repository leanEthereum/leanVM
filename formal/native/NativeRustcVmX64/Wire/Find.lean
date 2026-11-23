module

public import NativeRustcVmX64.Wire.Find.Exec
public import NativeRustcVmX64.Wire.Common
public import NativeRustcVmX64.Spec.Wire
public import NativeRustcVm.Wire.WordsFacts
public import NativeRustcVmX64.Code.Vm.Find.Names

/-!
# `find` meets its contract (x86-64)

`find_spec`: no node (`b0`): `None` (`b5`); else the loop (`b1`, then `b2`, `b3` per node,
`HInv`) reads node `i`'s key at `a + 40 i` (RDI plus R8); the key found, `Some` with the index in
RDX (`b6`); past the last node, `None` (`b4`, RAX still `0`). The keys are any words the caller
names at those addresses (`Miss`: no word there is the key).
-/

namespace NativeRustcVmX64.Wire.Find

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmX64.Vm.Find

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    (match exec ds S with | some (S', _) => S' | none => S) = S₁ := by
  rw [h]

/-- `x << 3` plus four times it: `40 x`. -/
theorem times40 {x : BitVec 64} (h : 40 * x.toNat < 2 ^ 64) :
    (BinOp.apply .add .W64 (BinOp.apply .shl .W64 x (BitVec.ofNat 64 3))
      (BinOp.apply .mul .W64 (BinOp.apply .shl .W64 x (BitVec.ofNat 64 3))
        (BitVec.ofNat 64 4))).toNat = 40 * x.toNat := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 3) = 3 := by decide
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

variable {m : MachineData}

/-- The nodes' address. -/
abbrev arr (m : MachineData) : BitVec 64 := reg m .rdi

/-- Node `i`'s address, its key's. -/
abbrev nd (m : MachineData) (i : Nat) : BitVec 64 := arr m + BitVec.ofNat 64 (40 * i)

/-- The nodes' count. -/
abbrev cnt (m : MachineData) : Nat := (reg m .rsi).toNat

/-- The key. -/
abbrev key (m : MachineData) : UInt64 := UInt64.ofBitVec (reg m .rdx)

/-- The keys before node `i` are not the key. -/
def Miss (m : MachineData) (i : Nat) : Prop := ∀ j < i, ∀ w, WordAt m.dmem (nd m j) w → w ≠ key m

/-- What `find` reaches: its postcondition at the return address. -/
abbrev Post (m : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧ FindPost m st.data

/-- **The postcondition**, the key at node `i` (`some i`) or at none of the nodes (`none`). -/
theorem post_of {m' : MachineData} {o : Option Nat} (hsv : Saved m m') (hd : m'.dmem = m.dmem)
    (ho : match o with
      | some i => i < cnt m ∧ Miss m i ∧ (∀ w, WordAt m.dmem (nd m i) w → w = key m) ∧
          reg m' .rax = 1 ∧ (reg m' .rdx).toNat = i
      | none => Miss m (cnt m) ∧ reg m' .rax = 0) :
    FindPost m m' := by
  refine ⟨fun ks hl hw ↦ ?_, hd, hsv⟩
  have hl' : ks.length = cnt m := hl
  have hne : ∀ j (hj : j < ks.length), Miss m (j + 1) → (ks[j] == key m) = false :=
    fun j hj hM ↦ by simpa using hM j (by omega) _ (hw j hj)
  cases o with
  | some i =>
    obtain ⟨hi, hM, hk, h0, h1⟩ := ho
    have hi' : i < ks.length := by omega
    rw [(List.findIdx?_eq_some_iff_getElem).mpr ⟨hi', by simpa using hk _ (hw i hi'),
      fun j hj ↦ by simpa using hM j hj _ (hw j (by omega))⟩]
    exact ⟨h0, h1⟩
  | none =>
    obtain ⟨hM, h0⟩ := ho
    rw [List.findIdx?_eq_none_iff.mpr fun x hx ↦ by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      exact hne j hj fun j' hj' ↦ hM j' (by omega)]
    exact h0

theorem saved_trans {a b c : MachineData} (h1 : Saved a b) (h2 : Saved b c) : Saved a c :=
  ⟨fun r hr ↦ (h2.1 r hr).trans (h1.1 r hr), fun p h ↦ h2.2 p (h1.2 p h)⟩

variable [Host] (k : Nat) (m)

/-- The loop's head (`b2`) at node `i < n`. -/
structure HInv (i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Find.b2Offset)
  sv : Saved m st.data
  d : st.data.dmem = m.dmem
  rsp : reg st.data .rsp = rspOf m
  rdi : reg st.data .rdi = reg m .rdi
  rcx : reg st.data .rcx = reg m .rdx
  rax : reg st.data .rax = 0
  rsi : (reg st.data .rsi).toNat = 40 * cnt m
  r8 : (reg st.data .r8).toNat = 40 * i
  rdx : (reg st.data .rdx).toNat = i
  lt : i < cnt m
  miss : Miss m i

variable {k m}

section
variable (hp : Placed code k) (hstk : StackOk m 0)
  (hok : NativeRustcVm.Region.Ok m.dmem ⟨arr m, 40 * cnt m⟩)
include hp hstk

/-- **A return** (`b4`, `b5`, `b6`, at `j`) from a state with the entry's RSP, memory and
callee-saved registers. -/
theorem fin {bj : List Directive} {j : Nat} (hb : bj.IsInfixAt code j) (hne : bj ≠ [])
    {S' : SState} (hx : exec bj sRet = some (S', .ret (.load 0 0 8)))
    (hrsp : S'.reg .rsp = some (.ptr 0 8)) (hmem : S'.mem = []) (hkeeps : keeps sRet S' = true)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hsp : reg st.data .rsp = rspOf m)
    (hd : st.data.dmem = m.dmem) (hsv : Saved m st.data) {o : Option Nat}
    (ho : ∀ m', (∀ r v, S'.reg r = some v →
        reg m' r = v.eval (Env.ofMachine st.data [(rspOf m, 8)])) →
      match o with
      | some i => i < cnt m ∧ Miss m i ∧ (∀ w, WordAt m.dmem (nd m i) w → w = key m) ∧
          reg m' .rax = 1 ∧ (reg m' .rdx).toNat = i
      | none => Miss m (cnt m) ∧ reg m' .rax = 0) :
    Eventually (step1 Host.exe) (Post m) st :=
  Eventually.mono (Wire.ret_keep (Wire.infix_of hb hne hp) hx hrsp hmem hkeeps hpc hstk hsp
    fun i _ ↦ by rw [hd]) fun _ ⟨hpc', hrsp', hd', hr', hsv'⟩ ↦
      ⟨hpc', hrsp', post_of (saved_trans hsv hsv') (hd'.trans hd) (ho _ hr')⟩

include hok

/-- **One node**: from the loop's head at node `i`, the key found (`Some i`), past the last node
(`None`), or the head at node `i + 1`. -/
theorem step {i : Nat} {st : MachineState} (hI : HInv m k i st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m st' ∨ HInv m k (i + 1) st') st := by
  have hn := hI.lt
  have hnw : (arr m).toNat + 40 * cnt m ≤ 2 ^ 64 := hok.2
  have hto : (nd m i).toNat = (arr m).toNat + 40 * i := NativeRustcVm.toNat_add_ofNat (by omega)
  have hmap : NativeRustcVm.Mapped m.dmem (nd m i) 8 := fun j hj ↦ by
    rw [NativeRustcVm.addr_add_add]; exact hok.1 _ (show 40 * i + j < 40 * cnt m by omega)
  let env := Env.ofMachine st.data [(nd m i, 8)]
  have hwf : env.WF := Env.wf_of ⟨⟨show NativeRustcVm.Mapped st.data.dmem (nd m i) 8 by
    rw [hI.d]; exact hmap, show (nd m i).toNat + 8 ≤ 2 ^ 64 by omega⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hr8 : reg st.data .r8 = BitVec.ofNat 64 (40 * i) := BitVec.eq_of_toNat_eq (by
    rw [hI.r8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hm : Match env headS st.data := match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial
    ⟨by
      show BinOp.apply .add .W64 (reg st.data .rdi) (reg st.data .r8) = nd m i + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      simp only [BinOp.apply, low_W64, ext_W64, hI.rdi, hr8], trivial⟩
  obtain ⟨w, hw⟩ := exists_wordAt hmap
  have hload : env.load 0 0 8 = w.toBitVec :=
    Wire.load_word (by
      show NativeRustcVm.WordAt st.data.dmem (nd m i + BitVec.ofNat 64 0) w
      rw [NativeRustcVm.addr_add_zero, hI.d]
      exact hw)
  refine exec_at (Wire.infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf nofun hI.pc hm
    fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = m.dmem := (hm1.dmem_eq hwf rfl).trans hI.d
  have hr1 : ∀ r, reg st1.data r = reg st.data r := fun r ↦
    Match.reg_eq hm hm1 (v := .reg r) (by cases r <;> rfl) (by cases r <;> rfl)
  have hsv1 : Saved m st1.data := saved_trans hI.sv (Match.saved hm hm1 hwf rfl (by decide))
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hload] at hpc1
  change st1.pc = if (w.toBitVec == reg st.data .rcx) = true then _ else _ at hpc1
  rw [hI.rcx, hp.label NativeRustcVmX64.Vm.Find.label_4_at, show k + NativeRustcVmX64.Vm.Find.b2Offset + b2.length = k + NativeRustcVmX64.Vm.Find.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Find.b2_next]] at hpc1
  by_cases hk : w = key m
  · -- `b6`: `Some i`.
    have he : (w.toBitVec == reg m .rdx) = true := by rw [hk]; exact beq_self_eq_true _
    rw [he] at hpc1
    simp only [↓reduceIte] at hpc1
    refine .mono (fin hp hstk b6_in_code (by simp [b6]) run_b6 rfl rfl (by decide) hpc1
      ((hr1 .rsp).trans hI.rsp) hd1 hsv1 (o := some i) fun m' hr' ↦ ?_) fun _ h ↦ .inl h
    refine ⟨hn, hI.miss, fun w' hw' ↦ (hw.unique hw').symm.trans hk, hr' .rax _ rfl, ?_⟩
    rw [hr' .rdx _ rfl]
    exact (congrArg BitVec.toNat (hr1 .rdx)).trans hI.rdx
  · have he : (w.toBitVec == reg m .rdx) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun h ↦ hk (by rw [key, ← h])
    rw [he] at hpc1
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
    have hmiss : Miss m (i + 1) := fun j hj w' hw' ↦ by
      rcases Nat.lt_or_ge j i with h | h
      · exact hI.miss j h w' hw'
      · obtain rfl : j = i := by omega
        rw [hw'.unique hw]
        exact hk
    -- `b3`: the count.
    let env' := Env.ofMachine st1.data []
    have hwf' : env'.WF := Env.wf_of trivial List.Pairwise.nil
    have hm' : Match env' regS st1.data := match_ofMachine trivial trivial trivial trivial trivial
    refine exec_at (Wire.infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf' nofun hpc1 hm'
      fun st2 hm2 hpc2 ↦ ?_
    have hd2 : st2.data.dmem = m.dmem := (hm2.dmem_eq hwf' rfl).trans hd1
    have hsv2 : Saved m st2.data := saved_trans hsv1 (Match.saved hm' hm2 hwf' rfl (by decide))
    have hk2 : ∀ r ∈ [Reg64.rsp, .rdi, .rcx, .rax, .rsi], reg st2.data r = reg st.data r :=
      fun r hr ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          exact (Match.reg_eq hm' hm2 rfl rfl).trans (hr1 _)
    have h8 : (reg st2.data .r8).toNat = 40 * (i + 1) := by
      rw [show reg st2.data .r8 = BinOp.apply .add .W64 (BitVec.ofNat 64 40) (reg st1.data .r8)
        from hm2.regs .r8 _ rfl, hr1]
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, hI.r8]
      omega
    have hdx : (reg st2.data .rdx).toNat = i + 1 := by
      rw [show reg st2.data .rdx = BinOp.apply .add .W64 (reg st1.data .rdx) (BitVec.ofNat 64 1)
        from hm2.regs .rdx _ rfl, hr1]
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, hI.rdx]
      omega
    simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64] at hpc2
    change st2.pc = if (!(reg st1.data .rsi == BinOp.apply .add .W64 (BitVec.ofNat 64 40)
      (reg st1.data .r8))) = true then _ else _ at hpc2
    rw [hp.label NativeRustcVmX64.Vm.Find.label_3_at, show k + NativeRustcVmX64.Vm.Find.b3Offset + b3.length = k + NativeRustcVmX64.Vm.Find.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Find.b3_next]] at hpc2
    have hsum : (BinOp.apply .add .W64 (BitVec.ofNat 64 40) (reg st1.data .r8)).toNat =
        40 * (i + 1) := by
      rw [hr1]
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, hI.r8]
      omega
    have hsi : (reg st1.data .rsi).toNat = 40 * cnt m := (congrArg BitVec.toNat (hr1 .rsi)).trans
      hI.rsi
    by_cases hlast : i + 1 = cnt m
    · have he : (reg st1.data .rsi == BinOp.apply .add .W64 (BitVec.ofNat 64 40)
          (reg st1.data .r8)) = true := by
        rw [beq_iff_eq]
        apply BitVec.eq_of_toNat_eq
        rw [hsi, hsum, hlast]
      rw [he] at hpc2
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
      -- `b4`: `None`.
      refine .mono (fin hp hstk b4_in_code (by simp [b4]) run_b4 rfl rfl (by decide) hpc2
        ((hk2 .rsp (by simp)).trans hI.rsp) hd2 hsv2 (o := none) fun m' hr' ↦ ?_)
        fun _ h ↦ .inl h
      refine ⟨by rw [← hlast]; exact hmiss, ?_⟩
      rw [hr' .rax _ rfl]
      exact (hk2 .rax (by simp)).trans hI.rax
    · have he : (reg st1.data .rsi == BinOp.apply .add .W64 (BitVec.ofNat 64 40)
          (reg st1.data .r8)) = false := by
        rw [beq_eq_false_iff_ne]
        intro h
        have := congrArg BitVec.toNat h
        rw [hsi, hsum] at this
        omega
      rw [he] at hpc2
      simp only [Bool.not_false, ↓reduceIte] at hpc2
      exact .done _ (.inr ⟨hpc2, hsv2, hd2, (hk2 .rsp (by simp)).trans hI.rsp,
        (hk2 .rdi (by simp)).trans hI.rdi, (hk2 .rcx (by simp)).trans hI.rcx,
        (hk2 .rax (by simp)).trans hI.rax, by rw [hk2 .rsi (by simp)]; exact hI.rsi, h8, hdx,
        by omega, hmiss⟩)

end

/-- **`find` meets its contract.** -/
theorem find_spec (hp : Placed code k) : Spec (Labels.label NativeRustcVmX64.Vm.Find.entryLabel) FindPre FindPost := by
  intro m ⟨hstk, hok⟩
  rw [show Labels.label NativeRustcVmX64.Vm.Find.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Find.b0Offset) from hp.label NativeRustcVmX64.Vm.Find.entry_at]
  have hnw : (arr m).toNat + 40 * cnt m ≤ 2 ^ 64 := hok.2
  let env := Env.ofMachine m []
  have hwf : env.WF := Env.wf_of trivial List.Pairwise.nil
  have hm : Match env regS m := match_ofMachine trivial trivial trivial trivial trivial
  refine exec_then (Wire.infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm
    fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have hr1 : ∀ r, reg st1.data r = reg m r := fun r ↦
    Match.reg_eq hm hm1 (v := .reg r) (by cases r <;> rfl) (by cases r <;> rfl)
  have hsv1 : Saved m st1.data := Match.saved hm hm1 hwf rfl (by decide)
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, BinOp.apply, ext_W64,
    BitVec.and_self] at hpc1
  change st1.pc = if (reg m .rsi == BitVec.ofNat 64 0) = true then _ else _ at hpc1
  rw [hp.label NativeRustcVmX64.Vm.Find.label_1_at, show k + NativeRustcVmX64.Vm.Find.b0Offset + b0.length = k + NativeRustcVmX64.Vm.Find.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Find.b0_next]] at hpc1
  by_cases h0 : cnt m = 0
  · have he : (reg m .rsi == BitVec.ofNat 64 0) = true := by
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; exact h0
    rw [he] at hpc1
    simp only [↓reduceIte] at hpc1
    -- `b5`: `None`.
    refine fin hp hstk b5_in_code (by simp [b5]) run_b5 rfl rfl (by decide) hpc1
      (hr1 .rsp) hd1 hsv1 (o := none) fun m' hr' ↦ ⟨fun j hj ↦ by omega, hr' .rax _ rfl⟩
  have he : (reg m .rsi == BitVec.ofNat 64 0) = false := by
    rw [beq_eq_false_iff_ne]; intro h; apply h0; show (reg m .rsi).toNat = 0; rw [h]; rfl
  rw [he] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b1`: the loop's set-up.
  let env' := Env.ofMachine st1.data []
  have hwf' : env'.WF := Env.wf_of trivial List.Pairwise.nil
  have hm' : Match env' regS st1.data := match_ofMachine trivial trivial trivial trivial trivial
  refine exec_at (Wire.infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf' nofun hpc1 hm'
    fun st2 hm2 hpc2 ↦ ?_
  have h40 : 40 * cnt m < 2 ^ 64 := by omega
  have hI : HInv m k 0 st2 := by
    refine ⟨hpc2, saved_trans hsv1 (Match.saved hm' hm2 hwf' rfl (by decide)),
      (hm2.dmem_eq hwf' rfl).trans hd1, (Match.reg_eq hm' hm2 rfl rfl).trans (hr1 .rsp),
      (Match.reg_eq hm' hm2 rfl rfl).trans (hr1 .rdi), (hm2.regs .rcx _ rfl).trans (hr1 .rdx),
      hm2.regs .rax _ rfl, ?_, by rw [show reg st2.data .r8 = _ from hm2.regs .r8 _ rfl]; rfl,
      by rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ rfl]; rfl, by omega,
      fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
    rw [show reg st2.data .rsi = _ from hm2.regs .rsi _ rfl]
    show (BinOp.apply .add .W64 (BinOp.apply .shl .W64 (reg st1.data .rsi) (BitVec.ofNat 64 3))
      (BinOp.apply .mul .W64 (BinOp.apply .shl .W64 (reg st1.data .rsi) (BitVec.ofNat 64 3))
        (BitVec.ofNat 64 4))).toNat = _
    rw [hr1, times40 h40]
  refine Sym.loop (I := fun j st ↦ ∃ i, j = cnt m - i ∧ HInv m k i st)
    (fun j st ⟨i, hj, hI⟩ ↦ Eventually.bind (step hp hstk hok hI) fun st' h ↦ ?_) ⟨0, rfl, hI⟩
  rcases h with h | h
  · exact .done _ (.inl h)
  · exact .done _ (.inr ⟨cnt m - (i + 1), by have := hI.lt; omega, i + 1, rfl, h⟩)

end

end NativeRustcVmX64.Wire.Find
