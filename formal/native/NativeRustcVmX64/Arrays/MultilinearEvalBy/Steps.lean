module

public import NativeRustcVmX64.Arrays.MultilinearEvalBy.Frame

/-!
# `multilinear_eval_by`'s steps, for both instances (x86-64)

Both instances run the same blocks up to their registers (`Regs`). Each step is proved here once,
from its blocks' runs (hypotheses `exec ds S = some (S', x)`) and decidable facts about the
symbolic states they end in (`TestOk`, `PushOk`, `EndOk`, `ZeroOk`, ...), which each instance
checks by `decide +kernel`:

- `zero_step`: a turn of the loop zeroing the pending entries;
- `test_step`: `full[k]`'s test;
- `push_step`: the value waits at level `k`, entry `i + 1` next or the end;
- `jump_end`: a jump to the epilogue;
- `finish_step`: the epilogue returns the value;
- `innerLoop`: the inner loop, from its turns.
-/

namespace NativeRustcVmX64.Arrays.MleFrame

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Field
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (setP stream cont)

@[expose] public section

/-- A turn of the zeroing loop: writes in its 64 bytes only, RAX advanced by `64`, RSP and the
arguments' registers kept. -/
abbrev ZeroOk (S : SState) : Prop :=
  (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    S.reg .rax = some (.bin .add .W64 (.lit 64) (.reg .rax)) ∧
    keepsRegs zS S [.rsp, .rdi, .rsi, .rdx, .rcx, .r8] = true

/-- `full[k]`'s test: no writes, RSP and the loop's registers kept. -/
abbrev TestOk (R : Regs) (S : SState) : Prop :=
  keepsAll (flagS R.rf) S [R.rf, R.ri, R.vlo, R.vhi] = true

/-- A pending entry's store: the flag set, the value stored, the value zeroed, RSP kept. -/
abbrev PushOk (R : Regs) (S : SState) : Prop :=
  (∀ w ∈ S.mem, (w.r = 1 ∧ w.off = 0 ∧ w.n = 1) ∨ (w.r = 2 ∧ w.off + w.n ≤ 16)) ∧
    findWrite 1 0 S.mem = some (.lit 1, 0) ∧
    (∀ i < 8, findWrite 2 (0 + i) S.mem = some (.reg R.vlo, i)) ∧
    (∀ i < 8, findWrite 2 (0 + 8 + i) S.mem = some (.reg R.vhi, i)) ∧
    S.reg R.vlo = some (.lit 0) ∧ S.reg R.vhi = some (.lit 0) ∧ S.reg .rsp = some (.ptr 0 8)

/-- A jump: no writes, RSP and the value kept. -/
abbrev JumpOk (R : Regs) (S : SState) : Prop := keepsAll regsS S [R.vlo, R.vhi] = true

/-- The epilogue: the value in RAX, RDX, the pushed registers restored, no writes. -/
abbrev EndOk (R : Regs) (S : SState) : Prop :=
  S.reg .rax = some (.reg R.vlo) ∧ S.reg .rdx = some (.reg R.vhi) ∧
    restores mleSlots 1216 S = true ∧ S.mem = []

end

public section

variable [Host]

/-! ## The zeroing loop -/

/-- The zeroing loop's head: the body, `point` at `56`, the arguments' registers the entry's,
RAX `64 t`. -/
structure ZInv (m0 : MachineData) (t : Nat) (s : MachineData) : Prop where
  body : Body m0 1216 mleStack mleSlots 0 0 s
  w56 : ValsAt s.dmem (fbOf m0) [(56, reg m0 .rcx)]
  regs : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], reg s r = reg m0 r
  rax : reg s .rax = BitVec.ofNat 64 (64 * t)
  lt : t < 16

/-- **The zeroing loop**: from its head at `t = 0`, its exit with the body, `point` at `56`, the
arguments' registers. -/
theorem zero_loop {ds : List Directive} {kz : Nat} {S : SState} {l : Label}
    (hk : ds.IsInfixAt Host.prog kz)
    (hx : exec ds zS = some (S, .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 64) (.reg .rax))
      (.lit 1024))) l))
    (hc : ZeroOk S) (hl : Labels.label l = Host.addrOf kz) {m0 : MachineData}
    (hS : StackOk m0 mleStack) {s : MachineState} (hpc : s.pc = Host.addrOf kz)
    (hZ : ZInv m0 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (kz + ds.length) ∧
      Body m0 1216 mleStack mleSlots 0 0 s'.data ∧
      ValsAt s'.data.dmem (fbOf m0) [(56, reg m0 .rcx)] ∧
      ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], reg s'.data r = reg m0 r) s := by
  obtain ⟨hw, hrax, hkp⟩ := hc
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf kz ∧ ∃ t, 16 - t = n ∧ ZInv m0 t s.data)
    (fun n s ⟨hpc, t, hn, hZ⟩ ↦ ?_) ⟨hpc, 0, rfl, hZ⟩
  have hlt := hZ.lt
  have ef := fb_toNat hS
  have e := fb_add_toNat hS (o := 144 + 64 * t) (by omega)
  have hr := frame_piece hS hZ.body.kept (o := 144 + 64 * t) (n := 64) (by omega)
  have hwf := wf1 hr (st := s.data)
  have hm : Match (Env.ofMachine s.data [(fbOf m0 + BitVec.ofNat 64 (144 + 64 * t), 64)]) zS
      s.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      dsimp only
      rw [eval_add]
      show rspOf s.data + reg s.data .rax = _
      rw [hZ.body.rsp, hZ.rax]
      exact pend_alias _ _, trivial⟩
  refine exec_at hk hx hwf (by intro l h; cases h) hpc hm fun s2 hm2 hpc2 ↦ ?_
  have he := regs_eq_of hm hm2 hkp
  have hW : ∀ p, Written (Env.ofMachine s.data [(fbOf m0 + BitVec.ofNat 64 (144 + 64 * t), 64)])
      S p → (fbOf m0).toNat + (144 + 64 * t) ≤ p.toNat ∧
        p.toNat < (fbOf m0).toNat + (144 + 64 * t) + 64 := fun p hp ↦ by
    have h := written_region0 rfl hwf le_rfl hw hp
    rw [Sym.inRange_iff (by rw [e]; omega), e] at h
    omega
  have bd2 := body_of_local hZ.body hS hm2 hwf rfl (he .rsp (by simp))
    fun p hp ↦ frame_addr hS (lo := 16) (hi := 1168) (by have := hW p hp; omega)
      (by have := hW p hp; omega) (by omega)
  have h56 : ValsAt s2.data.dmem (fbOf m0) [(56, reg m0 .rcx)] :=
    vals_congr hZ.w56 fun p hp j hj ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      dsimp only
      refine hm2.get?_mem0 hwf fun h ↦ ?_
      have h' := hW _ h
      rw [fb_add_toNat hS (by omega)] at h'
      omega
  have hregs : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], reg s2.data r = reg m0 r := fun r hr ↦ by
    rw [he r (List.mem_cons_of_mem _ hr)]
    exact hZ.regs r hr
  have hrax2 : reg s2.data .rax = BitVec.ofNat 64 (64 * (t + 1)) := by
    show s2.data.regs.get64 .rax = _
    rw [hm2.regs .rax _ hrax, eval_add, eval_lit, eval_reg, Env.ofMachine_regs]
    show BitVec.ofNat 64 64 + reg s.data .rax = _
    rw [hZ.rax, ← BitVec.ofNat_add, show 64 + 64 * t = 64 * (t + 1) by omega]
  simp only [PcOk] at hpc2
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_lit, eval_reg, Env.ofMachine_regs] at hpc2
  rw [show s.data.regs.get64 .rax = reg s.data .rax from rfl, hZ.rax, ← BitVec.ofNat_add,
    ofNat_beq (by omega) (by decide)] at hpc2
  obtain ⟨hT, hF⟩ := pc_cond hpc2
  by_cases hend : 64 + 64 * t = 1024
  · exact .done _ (Or.inl ⟨hF (by simp [hend]), bd2, h56, hregs⟩)
  · exact .done _ (Or.inr ⟨16 - (t + 1), by omega, (hT (by simp [hend])).trans hl, t + 1, rfl,
      ⟨bd2, h56, hregs, hrax2, by omega⟩⟩)

/-! ## The inner loop -/

/-- **`full[k]`'s test**: on to `push` (nothing pending) or `pair`. -/
theorem test_step (R : Regs) {es : List EW} {m0 : MachineData} (hS : StackOk m0 mleStack)
    {ds : List Directive} {kI kP : Nat} {S : SState} {lP : Label}
    (hk : ds.IsInfixAt Host.prog kI)
    (hx : exec ds (flagS R.rf) = some (S, .cond (.cmp .eq .W8 (.load 0 0 1) (.lit 0)) lP))
    (hc : TestOk R S) (hlP : Labels.label lP = Host.addrOf kP) {Q : MachineState → Prop}
    {i kk : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf kI) (hI : Inner es R m0 i kk s.data)
    (hpush : ∀ s' : MachineState, s'.pc = Host.addrOf kP → Inner es R m0 i kk s'.data →
      pendOf s'.data.dmem (fbOf m0) kk = none → Eventually (step1 Host.exe) Q s')
    (hpair : ∀ s' : MachineState, s'.pc = Host.addrOf (kI + ds.length) →
      Inner es R m0 i kk s'.data → pendOf s'.data.dmem (fbOf m0) kk =
        some (ewOf s'.data.dmem (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk))) →
      Eventually (step1 Host.exe) Q s') :
    Eventually (step1 Host.exe) Q s := by
  have hk64 : kk < 64 := by have := hI.hk; have := hI.lt; omega
  have hfl := frame_piece hS hI.fr.body.kept (o := 80 + kk) (n := 1) (by omega)
  have hwf := wf1 hfl (st := s.data)
  have hm : Match (Env.ofMachine s.data [(fbOf m0 + BitVec.ofNat 64 (80 + kk), 1)]) (flagS R.rf)
      s.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hI.rf.trans (eval_ptr0 rfl).symm, trivial⟩ trivial trivial
      trivial
  refine exec_at hk hx hwf (by intro l h; cases h) hpc hm fun s2 hm2 hpc2 ↦ ?_
  obtain ⟨bd2, hd2, hr2⟩ := body_of_keeps hI.fr.body hS hm hm2 hwf rfl hc
  have hI2 : Inner es R m0 i kk s2.data := by
    obtain ⟨fr, hi, hkk, hlt, hwi, hrf, hri, hval⟩ := hI
    refine ⟨⟨bd2, ?_, ?_⟩, hi, hkk, hlt, ?_, ?_, ?_, ?_⟩
    · rw [hd2]; exact fr.args
    · rw [hd2]; exact fr.flags
    · rw [hd2]; exact hwi
    · rw [hr2 R.rf (by simp)]; exact hrf
    · rw [hr2 R.ri (by simp)]; exact hri
    · rw [hd2, hr2 R.vlo (by simp), hr2 R.vhi (by simp)]; exact hval
  simp only [PcOk] at hpc2
  have hc2 := pc_cond hpc2
  rcases flag_cases hk64 hI.fr.flags with ⟨hb, hn⟩ | ⟨hb, hs⟩
  · have hl := load_byte (env := Env.ofMachine s.data [(fbOf m0 + BitVec.ofNat 64 (80 + kk), 1)])
      (r := 0) hb
    refine hpush s2 ((hc2.1 ?_).trans hlP) hI2 (by rw [hd2]; exact hn)
    show CmpOp.apply .eq .W8 (Env.load _ 0 0 1) (BitVec.ofNat 64 0) = true
    rw [hl]; decide
  · have hl := load_byte (env := Env.ofMachine s.data [(fbOf m0 + BitVec.ofNat 64 (80 + kk), 1)])
      (r := 0) hb
    refine hpair s2 (hc2.2 ?_) hI2 (by rw [hd2]; exact hs)
    show ¬CmpOp.apply .eq .W8 (Env.load _ 0 0 1) (BitVec.ofNat 64 0) = true
    rw [hl]; decide

/-- **A jump to the epilogue.** -/
theorem jump_end (R : Regs) {es : List EW} {m0 : MachineData} (hS : StackOk m0 mleStack)
    {e : List Directive} {ke kEnd : Nat} {Se : SState} {lE : Label}
    (hke : e.IsInfixAt Host.prog ke) (hxe : exec e regsS = some (Se, .jump lE))
    (hce : JumpOk R Se) (hlE : Labels.label lE = Host.addrOf kEnd) {s : MachineState}
    (hpc : s.pc = Host.addrOf ke) (hE : AtEnd es R m0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf kEnd ∧ AtEnd es R m0 s'.data) s := by
  refine exec_at hke hxe (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun s2 hm2 hpc2 ↦ .done _ ⟨hpc2.trans hlE, ?_⟩
  obtain ⟨bd2, -, hr2⟩ := body_of_keeps hE.body hS (match_nil _) hm2 (Env.wf_nil _) rfl hce
  exact ⟨bd2, by rw [hr2 R.vlo (by simp), hr2 R.vhi (by simp)]; exact hE.val⟩

/-- **A value waits at level `kk`**: stored, flagged; on to entry `i + 1`, or, after the last
entry, to the epilogue with `0`. -/
theorem push_step (R : Regs) {es : List EW} {m0 : MachineData} (hS : StackOk m0 mleStack)
    (h02 : reg m0 .rdi = reg m0 .rdx) (hes : es.length = nn m0)
    {ds e : List Directive} {kP kO ke kEnd : Nat} {S Se : SState} {lO lE : Label}
    (hk : ds.IsInfixAt Host.prog kP)
    (hx : exec ds (pushS R.rf R.ri) =
      some (S, .cond (.not (.cmp .eq .W64 (.load 0 16 8) (.load 0 32 8))) lO))
    (hc : PushOk R S) (hlO : Labels.label lO = Host.addrOf kO)
    (hke : e.IsInfixAt Host.prog ke) (hde : kP + ds.length = ke)
    (hxe : exec e regsS = some (Se, .jump lE)) (hce : JumpOk R Se)
    (hlE : Labels.label lE = Host.addrOf kEnd)
    {i kk : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf kP) (hI : Inner es R m0 i kk s.data)
    (hnone : pendOf s.data.dmem (fbOf m0) kk = none) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf kEnd ∧ AtEnd es R m0 s'.data) ∨
      (s'.pc = Host.addrOf kO ∧ Outer es m0 (i + 1) s'.data)) s := by
  have hk64 : kk < 64 := by have := hI.hk; have := hI.lt; omega
  have ef := fb_toNat hS
  obtain ⟨hw, hf1, hu, hv, hlo0, hhi0, hsp⟩ := hc
  have h0 := frame_piece hS hI.fr.body.kept (o := 0) (n := 80) (by omega)
  rw [add_ofNat_zero] at h0
  have h1 := frame_piece hS hI.fr.body.kept (o := 80 + kk) (n := 1) (by omega)
  have h2 := frame_piece hS hI.fr.body.kept (o := 144 + 16 * kk) (n := 16) (by omega)
  have a01 := frame_apart hS (o := 0) (n := 80) (o' := 80 + kk) (n' := 1) (by omega) (by omega)
    (by omega)
  have a02 := frame_apart hS (o := 0) (n := 80) (o' := 144 + 16 * kk) (n' := 16) (by omega)
    (by omega) (by omega)
  have a12 := frame_apart hS (o := 80 + kk) (n := 1) (o' := 144 + 16 * kk) (n' := 16) (by omega)
    (by omega) (by omega)
  rw [add_ofNat_zero] at a01 a02
  have hwf := wf3 (st := s.data) h0 h1 h2 a01 a02 a12
  have hm : Match (Env.ofMachine s.data [(fbOf m0, 80), (fbOf m0 + BitVec.ofNat 64 (80 + kk), 1),
      (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk), 16)]) (pushS R.rf R.ri) s.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hI.fr.body.rsp, hI.rf.trans (eval_ptr0 rfl).symm,
      trivial⟩ trivial trivial ⟨by
        dsimp only
        rw [eval_add]
        show fbOf m0 + BitVec.ofInt 64 8 + reg s.data R.ri = _
        rw [hI.ri]
        exact pend_alias _ _, trivial⟩
  refine exec_at hk hx hwf (by intro l h; cases h) hpc hm fun s2 hm2 hpc2 ↦ ?_
  -- the bytes written: the flag, the pending entry
  have hW : ∀ p, Written (Env.ofMachine s.data [(fbOf m0, 80),
      (fbOf m0 + BitVec.ofNat 64 (80 + kk), 1), (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk), 16)])
      S p → p.toNat = (fbOf m0).toNat + (80 + kk) ∨
        ((fbOf m0).toNat + (144 + 16 * kk) ≤ p.toNat ∧ p.toNat < (fbOf m0).toNat + (160 + 16 * kk)) := by
    intro p hp
    obtain ⟨w, hw', b, sz, hb, hlo, hhi⟩ := written_bounds hp
    have e1 := fb_add_toNat hS (o := 80 + kk) (by omega)
    have e2 := fb_add_toNat hS (o := 144 + 16 * kk) (by omega)
    rcases hw w hw' with ⟨hr, ho, hn⟩ | ⟨hr, hn⟩
    · rw [hr] at hb
      simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      left; omega
    · rw [hr] at hb
      simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      right; omega
  have hnw : ∀ j, j < 1224 → j ≠ 80 + kk → (j < 144 + 16 * kk ∨ 160 + 16 * kk ≤ j) →
      s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
        s.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := by
    intro j hj h1 h2
    refine hm2.get?_mem0 hwf fun hw' ↦ ?_
    have := hW _ hw'
    rw [fb_add_toNat hS (by omega)] at this
    omega
  have hflag : s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 (80 + kk)) = some 1 := by
    have := hm2.mem 1 (fbOf m0 + BitVec.ofNat 64 (80 + kk)) 1 rfl 0 (by decide)
    rw [add_ofNat_zero] at this
    rw [this]
    unfold memByte
    rw [hf1]
    simp [Sym.eval, byteOf]
  have hvs : ewOf s2.data.dmem (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk)) =
      ewArg (reg s.data R.vlo) (reg s.data R.vhi) := by
    have := ewAt_of_writes hm2 (r := 2) (o := 0) rfl (by decide) hu hv
    rw [add_ofNat_zero] at this
    exact NativeRustcVm.ewOf_of_ewAt this
  have hP : pendOf s2.data.dmem (fbOf m0) = setP (pendOf s.data.dmem (fbOf m0)) kk
      (some (ewArg (reg s.data R.vlo) (reg s.data R.vhi))) :=
    pendOf_set hk64 hflag hvs fun j _ hj h1 h2 ↦ hnw j (by omega) h1 h2
  have hkP : kk < (pts m0).length := by
    simp only [pts, NativeRustcVm.length_ewsOf]; exact hI.hk
  have hval : stream (pts m0) (es.drop (i + 1)) (pendOf s2.data.dmem (fbOf m0)) =
      stream (pts m0) es fun _ ↦ none := by
    rw [hP, ← NativeRustcVm.Mle.cont_none _ hkP hnone]; exact hI.val
  have bd2 : Body m0 1216 mleStack mleSlots 0 0 s2.data :=
    body_of_local hI.fr.body hS hm2 hwf rfl
      (Match.reg_eq hm hm2 (show (pushS R.rf R.ri).reg .rsp = some (.ptr 0 8) from rfl) hsp)
      (fun p hp ↦ by
        rcases hW p hp with h1 | ⟨h1, h2⟩
        · exact frame_addr hS (lo := 16) (hi := 1168) (by omega) (by omega) (by omega)
        · exact frame_addr hS (lo := 16) (hi := 1168) (by omega) (by omega) (by omega))
  have hwi : ValsAt s2.data.dmem (fbOf m0) [(16, BitVec.ofNat 64 (i + 1))] :=
    wi_congr hI.wi fun j h1 h2 ↦ hnw j (by omega) (by omega) (by omega)
  -- the test `i + 1 = n`
  simp only [PcOk] at hpc2
  rw [eval_not, eval_cmp_eq, eval_load, eval_load,
    val_load (env := Env.ofMachine s.data [(fbOf m0, 80), (fbOf m0 + BitVec.ofNat 64 (80 + kk), 1),
      (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk), 16)]) (r := 0) hI.wi
      (o := 16) (v := BitVec.ofNat 64 (i + 1)) (by simp),
    val_load (env := Env.ofMachine s.data [(fbOf m0, 80), (fbOf m0 + BitVec.ofNat 64 (80 + kk), 1),
      (fbOf m0 + BitVec.ofNat 64 (144 + 16 * kk), 16)]) (r := 0) hI.fr.args
      (o := 32) (v := reg m0 .rdi) (by simp [argVals]),
    h02, show reg m0 .rdx = BitVec.ofNat 64 (nn m0) by simp [nn],
    ofNat_beq (by have := hI.hi; have := (reg m0 .rdx).isLt; simp only [nn] at *; omega)
      (by simp only [nn]; exact (reg m0 .rdx).isLt)] at hpc2
  obtain ⟨hT, hF⟩ := pc_cond hpc2
  by_cases hlast : i + 1 = nn m0
  · have hpc3 : s2.pc = Host.addrOf ke := (hF (by simp [hlast])).trans (by rw [hde])
    refine Eventually.mono (jump_end R hS hke hxe hce hlE hpc3 ⟨bd2, ?_⟩) fun _ h ↦ Or.inl h
    rw [← hval, List.drop_of_length_le (by omega)]
    show ewArg (s2.data.regs.get64 R.vlo) (s2.data.regs.get64 R.vhi) = 0
    rw [hm2.regs R.vlo _ hlo0, hm2.regs R.vhi _ hhi0]
    rfl
  · refine .done _ (Or.inr ⟨(hT (by simp [hlast])).trans hlO, ⟨⟨bd2, ?_, ?_⟩, by
      have := hI.hi; omega, by have := hI.hk; omega, hI.lt, hwi, hval⟩⟩)
    · exact args_congr hI.fr.args fun j h1 h2 ↦ hnw j (by omega) (by omega) (by omega)
    · exact flagsOk_set hI.fr.flags hflag fun j _ hj h1 ↦ hnw j (by omega) h1 (by omega)

/-- **The epilogue**: the value returned, the pushed registers restored. -/
theorem finish_step (R : Regs) {es : List EW} {m0 : MachineData} (hS : StackOk m0 mleStack)
    {ds : List Directive} {kEnd : Nat} {S : SState} (hk : ds.IsInfixAt Host.prog kEnd)
    (hx : exec ds (midS 1216) = some (S, .ret (.load 0 1216 8))) (hc : EndOk R S)
    {s : MachineState} (hpc : s.pc = Host.addrOf kEnd) (hE : AtEnd es R m0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = retOf m0 ∧ rspOf s'.data = rspOf m0 + 8#64 ∧
      ewRet s'.data = stream (pts m0) es (fun _ ↦ none) ∧ Changes m0 s'.data mleStack 0 0 ∧
      Saved m0 s'.data) s := by
  obtain ⟨hax, hdx, hres, hmem⟩ := hc
  have h1216 : 1216 ≤ mleStack := by decide
  refine exec_at hk hx (hE.body.wf (vars := fun _ ↦ 0) (ret := 0) hS h1216)
    (by intro l h; cases h) hpc hE.body.mid_match fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ :=
    hE.body.done hS h1216 hm' hpc' hres hmem (fun j _ ↦ not_inRange_zero _)
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hE.body.same p hp', hsaved⟩
  rw [← hE.val, ← ewRet_eq]
  show ewArg (st'.data.regs.get64 .rax) (st'.data.regs.get64 .rdx) = _
  rw [hm'.regs .rax _ hax, hm'.regs .rdx _ hdx]
  rfl

/-- **The inner loop**, from its turns: entry `i` carried from level `0` until it waits or
reaches the last level. -/
theorem innerLoop (R : Regs) {es : List EW} {m0 : MachineData} {i kI : Nat}
    {Q : MachineState → Prop}
    (step : ∀ kk (s : MachineState), s.pc = Host.addrOf kI → Inner es R m0 i kk s.data →
      Eventually (step1 Host.exe)
        (fun s' ↦ Q s' ∨ (s'.pc = Host.addrOf kI ∧ Inner es R m0 i (kk + 1) s'.data)) s)
    {s : MachineState} (hpc : s.pc = Host.addrOf kI) (hI : Inner es R m0 i 0 s.data) :
    Eventually (step1 Host.exe) Q s := by
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf kI ∧ ∃ kk, 64 - kk = n ∧ Inner es R m0 i kk s.data)
    (fun n s ⟨hpc, kk, hn, hI⟩ ↦ ?_) ⟨hpc, 0, rfl, hI⟩
  refine Eventually.mono (step kk s hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · have h1 := hI'.hk
    have h2 := hI'.lt
    exact Or.inr ⟨64 - (kk + 1), by omega, hpc', kk + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.MleFrame
