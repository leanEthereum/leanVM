module

public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVmX64.Transcript.ReadCommitment.Exec
public import NativeRustcVmX64.Transcript.Arith
public import NativeVm.Equiv.Transcript
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names

/-!
# `TState::read_commitment` on x86-64

**`readCommitment_spec`**: AL becomes `readCommitment height width`'s `Some`/`None` and the
`TState` at RDI its state, given `read_scalar`'s contract. `b0` pushes R15 to RBX and reads a
scalar into the frame (`call_read`); `b1` tests its tag (`0`: `b6`, `b7` return `0`); `b2` keeps it
in R12, R13 and reads a second (`b3`: its tag); `b4` compares the roots' count with `8` (below, by
the precondition); `b5` stores the root (the two elements, the height, the width), advances the
count and sets AL = `1`; `b7` returns.
-/

namespace NativeRustcVmX64.Transcript.ReadCommitment

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateReadCommitment
open NativeRustcVm.Transcript NativeVm.Model

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide

theorem readScalar_roots {s s' : TState} {x : EW} (h : readScalar.run s = some (x, s')) :
    s'.roots = s.roots := by
  rw [NativeVm.Equiv.readScalar_run, NativeVm.Equiv.nextScalar_run] at h
  split at h
  · cases h
  · cases hx : s.stream[s.cursor]? with
    | none => rw [hx] at h; cases h
    | some y => rw [hx] at h; cases h; rfl

theorem run_eq (h w : Nat) (s : TState) :
    (readCommitment h w).run s = (readScalar.run s).bind fun p ↦
      (readScalar.run p.2).bind fun q ↦
        some ((), { q.2 with roots := q.2.roots.push ⟨#v[p.1.c0, p.1.c1, q.1.c0, q.1.c1], h, w⟩ }) :=
  NativeVm.Equiv.readCommitment_run h w s

theorem ofInt_neg368 : (BitVec.ofInt 64 (-368)).toNat = 2 ^ 64 - 368 := by
  rw [BitVec.toNat_ofInt]; rfl

theorem ofInt_neg752 : (BitVec.ofInt 64 (-752)).toNat = 2 ^ 64 - 752 := by
  rw [BitVec.toNat_ofInt]; rfl

theorem toUInt64_succ {n : Nat} (h : n + 1 < 2 ^ 64) :
    UInt64.ofBitVec (n.toUInt64.toBitVec + BitVec.ofNat 64 1) = (n + 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have e : ∀ m, m < 2 ^ 64 → m.toUInt64.toNat = m := fun m hm ↦ by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hm
  rw [e _ h]
  show (n.toUInt64.toBitVec + BitVec.ofNat 64 1).toNat = _
  rw [BitVec.toNat_add, UInt64.toNat_toBitVec, e _ (by omega), BitVec.toNat_ofNat]
  omega

theorem toUInt64_toNat (x : BitVec 64) : x.toNat.toUInt64 = UInt64.ofBitVec x :=
  UInt64.toNat_inj.mp (by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt x.isLt)

/-- An interval of the `TState` is at its offsets. -/
theorem touch_sub {t q : BitVec 64} {o n : Nat} (hT : NativeRustcVm.NoWrap t 760) (hle : o + n ≤ 760)
    (h : NativeRustcVm.InRange (off t o) n q) {W : Nat → Prop} (hW : ∀ j, o ≤ j → j < o + n → W j) :
    Touch t 760 W q := by
  obtain ⟨j, hj, ⟨h1, h2⟩, rfl⟩ := touch_of_inRange hT hle h
  exact ⟨j, hj, hW j h1 h2, rfl⟩

variable [Host] {k : Nat}

/-- What the transcript function may change: the `TState` and its stack. -/
abbrev Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
    NativeRustcVm.InRange (stackBelow m0 readCommitmentStack) readCommitmentStack q

/-- **A call of `read_scalar`** from the frame, its output at `fb + 16`. -/
theorem call_read
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {a : DecArea} {m0 : MachineData} (hst : StackOk m0 readCommitmentStack)
    (hrc : RcAt m0 readCommitmentStack) (htok : TStateOk m0 (reg m0 .rdi) a readCommitmentStack)
    (hgot : GotAt m0 readCommitmentStack [(reg m0 .rdi, tstateBytes),
      (a.words, 8 * a.len), (rcAddr, 192)] ["memcpy"])
    {s' : TState} {st : MachineState} {env : Env} {next : Int64}
    (hpc : PcOk env (.call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) next st) (hf : Frame m0 80 slots 0 st.data)
    (hX7 : reg st.data .rdi = off (stackBelow m0 80) 16) (hX6 : reg st.data .rsi = reg m0 .rdi)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s')
    (hso : NativeRustcVm.SameOutside m0.dmem st.data.dmem (Out m0)) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → Frame m0 80 slots 8 st'.data →
      OptEWAt st'.data.dmem (off (stackBelow m0 80) 16) ((readScalar.run s').map (·.1)) →
      NextAt st'.data.dmem (reg m0 .rdi) a (readScalar.run s') →
      NativeRustcVm.SameOutside m0.dmem st'.data.dmem (Out m0) → Saved st.data st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  set t := reg m0 .rdi
  set fb := stackBelow m0 80
  have hn : readCommitmentStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (80 + 8) := frame_noWrap hst (by decide)
  have hfnw80 : NativeRustcVm.NoWrap fb 80 := by unfold NativeRustcVm.NoWrap at hfnw ⊢; omega
  have hTn := hts.footprint.1.2
  have hTF : NativeRustcVm.Apart t 760 fb (80 + 8) := apart_frame htok.1 hn (by decide)
  have hsnw := noWrap_stackBelow hst
  have hrcOut : ∀ q, Out m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h (inRange_mono hq (by omega))
  have hsp : rspOf st.data = fb := by rw [hf.sp, off_zero]
  have hpre : ReadScalarPre a s' st.data := by
    unfold ReadScalarPre
    rw [hX6, hX7]
    refine ⟨stackOk_callee hst hf.kept hsp (by decide),
      RcAt.callee hrc (rc_keep hso hrcOut) hsp hn (by decide), hts,
      TStateOk.callee htok hsp hn (by decide),
      OutOk.frame hst (by decide) hsp hf.kept (by decide) (by decide) htok hrc, ?_⟩
    refine got_callee hgot (got_keep hgot hst (writes := [(t, tstateBytes)])
      (by simp [t]) (by simpa using hTn) (by simpa using hso))
      hsp hn (by decide) ?_
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact (hgot.1 l hl).2.2.2 (t, tstateBytes) (by simp [t])
    · exact (hgot.1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
    · exact got_apart_frame hgot hst hl (ob := 16) (len := 24) (by decide) (by decide)
    · exact (hgot.1 l hl).2.2.2 (rcAddr, 192) (by simp)
  refine call_then hpc (hrs a s') hpre fun st' hpc' hrsp' ⟨hout, hnext, hs, hsv⟩ => ?_
  rw [hX7] at hout
  rw [hX6] at hnext
  rw [hX7, hX6] at hs
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st.data readScalarStack) readScalarStack q →
      NativeRustcVm.InRange (stackBelow m0 readCommitmentStack) readCommitmentStack q ∧
        ¬ NativeRustcVm.InRange fb (80 + 8) q :=
    fun q hq ↦ inRange_callee hsp h8 hn (by decide) hq
  have hslot : ∀ j, 16 + 24 ≤ j → j < 80 + 8 → ∀ q, q = off fb j →
      ¬ (NativeRustcVm.InRange (off fb 16) 24 q ∨ NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow st.data readScalarStack) readScalarStack q) := by
    rintro j hj1 hj2 q rfl (h | h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h; omega
    · exact not_inRange_of_apart hTF hTn hfnw h (inRange_off_self hj2 (by omega))
    · exact (hcal _ h).2 (inRange_off_self hj2 (by omega))
  have hf' : Frame m0 80 slots 8 st'.data :=
    Frame.call_slots hf hsv hrsp' hs
      (fun p hp i hi ↦ hslot _ (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega)
        (by have := slots_le p hp; omega) _ rfl)
      (fun j hj ↦ hslot _ (by omega) (by omega) _ rfl)
  refine cont st' hpc' hf' hout hnext (fun q hq ↦ ?_) hsv
  simp only [Out, not_or] at hq
  have hqf : ¬ NativeRustcVm.InRange fb 80 q :=
    fun h ↦ hq.2 (inRange_frame_stack h8 hn (by decide) h)
  rw [hs q (by
    rintro (h | h | h)
    · exact hqf (inRange_of_off hfnw80 (by decide) h)
    · exact hq.1 h
    · exact hq.2 (hcal q h).1)]
  exact hso q (by simp only [Out, not_or]; exact hq)

/-- A failure (`b6`, `b7`): `0`, the epilogue. -/
theorem finish_fail (hp : Placed code k) {m0 d : MachineData} (hst : StackOk m0 readCommitmentStack)
    (hf : Frame m0 80 slots 8 d) {S : SState}
    (h6 : exec b6 S = some (after b6 S, .fall))
    (h7 : exec b7 (after b6 S) = some (after b7 (after b6 S), .ret (.load 0 80 8)))
    (hok : FailOk (after b7 (after b6 S))) {st : MachineState} {ret : BitVec 64}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadCommitment.b6Offset)) (hm : Match (frameEnv m0 d 80 [] (fun _ ↦ 0) ret) S st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
      reg st'.data .rax = 0 ∧ st'.data.dmem = d.dmem ∧ Saved m0 st'.data) st := by
  obtain ⟨hepi, hmem, hrax⟩ := hok
  have hwf := frame_wf (m0 := m0) (d := d) (F := 80) (rest := []) (vars := fun _ ↦ 0) (ret := ret)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, frame_noWrap hst (by decide)⟩
    (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) h6 hwf nofun hpc hm
    fun st1 hm1 hpc1 => ?_
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) h7 hwf nofun
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadCommitment.b6_next)) hm1 fun st2 hm2 hpc2 => ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm2 hepi
  simp only [PcOk] at hpc2
  exact .done _ ⟨by rw [hpc2]; exact hf.load_ret hst (by decide), hrsp, hm2.regs .rax _ hrax,
    hm2.dmem_eq hwf hmem, hsv⟩

/-- R14 = the count's address minus `752`. -/
theorem r14_push {env : Env} {d : MachineData} {t : BitVec 64}
    (hTn : t.toNat + 760 ≤ 2 ^ 64) (hb2 : env.base 2 = off t 752)
    (hr14 : d.regs.get64 .r14 = t) : d.regs.get64 .r14 = (Sym.ptr 2 (-752)).eval env := by
  rw [Sym.eval, hr14, hb2]
  apply BitVec.eq_of_toNat_eq
  have hcw : (off t 752).toNat = t.toNat + 752 := toNat_off (by omega)
  rw [BitVec.toNat_add, hcw, ofInt_neg752]
  omega

omit [Host] in
theorem add64' (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp [BinOp.apply, low_W64, ext_W64]

/-- `48 · count`, for each count below `8`. -/
theorem offSym_eval {env : Env} {nr : Nat} (hnr8 : nr < 8)
    (hrax : env.regs .rax = nr.toUInt64.toBitVec) : offSym.eval env = BitVec.ofNat 64 (48 * nr) := by
  simp only [offSym, Sym.eval, hrax]
  interval_cases nr <;> decide

/-- `rootAddr` = the root's address minus `368`. -/
theorem alias_push {env : Env} {t : BitVec 64} {nr : Nat} (hnr8 : nr < 8)
    (hTn : t.toNat + 760 ≤ 2 ^ 64) (hb1 : env.base 1 = off t (368 + 48 * nr))
    (hb2 : env.base 2 = off t 752) (hrax : env.regs .rax = nr.toUInt64.toBitVec) :
    rootAddr.eval env = env.base 1 + BitVec.ofInt 64 (-368) := by
  have hrb : (off t (368 + 48 * nr)).toNat = t.toNat + (368 + 48 * nr) := toNat_off (by omega)
  have hcw : (off t 752).toNat = t.toNat + 752 := toNat_off (by omega)
  rw [rootAddr, Sym.eval, Sym.eval, offSym_eval hnr8 hrax, add64', hb1, hb2]
  generalize off t 752 = cw at hcw ⊢
  generalize off t (368 + 48 * nr) = rb at hrb ⊢
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, hcw, hrb, ofInt_neg752, ofInt_neg368,
    BitVec.toNat_ofNat]
  omega

/-- `b5`'s start: region 1 the root `n`, region 2 the count, R14 the `TState`. -/
theorem match_push {m0 d : MachineData} {t : BitVec 64} {nr : Nat} (hnr8 : nr < 8)
    (hTn : t.toNat + 760 ≤ 2 ^ 64) (hf : Frame m0 80 slots 8 d)
    (hrax : d.regs.get64 .rax = nr.toUInt64.toBitVec) (hr14 : d.regs.get64 .r14 = t) :
    Match (frameEnv m0 d 80 [(off t (368 + 48 * nr), 48), (off t 752, 8)] (fun _ ↦ 0) 0)
      pushS d :=
  match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
    ⟨hf.rsp_eval, r14_push hTn (Env.base_ofMachine _ _ _ _ rfl) hr14, trivial⟩ trivial trivial
    ⟨alias_push hnr8 hTn (Env.base_ofMachine _ _ _ _ rfl) (Env.base_ofMachine _ _ _ _ rfl) hrax,
      trivial⟩

/-- **The push** (`b5`, `b7`): the root of the two elements in R12, R13 and in the frame, the
height R15 and the width RBX stored at the `TState`'s root `n`, the count advanced, AL = `1`, the
epilogue. -/
theorem push_run (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 readCommitmentStack)
    {a : DecArea} {s2 : TState} {st : MachineState} (hf : Frame m0 80 slots 8 st.data)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s2) (hlt : s2.roots.size < maxRoots)
    (hTF : NativeRustcVm.Apart (reg m0 .rdi) 760 (stackBelow m0 80) (80 + 8))
    (hrax : st.data.regs.get64 .rax = s2.roots.size.toUInt64.toBitVec)
    (hr14 : st.data.regs.get64 .r14 = reg m0 .rdi) {x0 x1 : EW}
    (h12 : reg st.data .r12 = x0.c0.toBitVec) (h13 : reg st.data .r13 = x0.c1.toBitVec)
    (h15 : reg st.data .r15 = reg m0 .rsi) (h3 : reg st.data .rbx = reg m0 .rdx)
    (hel : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 80) 24) x1.c0 ∧
      NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 80) 32) x1.c1)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadCommitment.b5Offset)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ (reg st'.data .rax).toNat % 256 = 1 ∧
      TStateAt st'.data.dmem (reg m0 .rdi) a { s2 with roots := (s2.roots.push
        ⟨#v[x0.c0, x0.c1, x1.c0, x1.c1], (reg m0 .rsi).toNat, (reg m0 .rdx).toNat⟩) } ∧
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (NativeRustcVm.InRange (reg m0 .rdi) tstateBytes) ∧
      Saved m0 st'.data) st := by
  set t := reg m0 .rdi
  set fb := stackBelow m0 80
  set nr := s2.roots.size with hnr
  have hnr8 : nr < 8 := hlt
  have hfnw : NativeRustcVm.NoWrap fb (80 + 8) := frame_noWrap hst (by decide)
  obtain ⟨⟨hTm, hTn⟩, -, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  set rb := off t (368 + 48 * nr)
  set cw := off t 752
  have hrb : rb.toNat = t.toNat + (368 + 48 * nr) := toNat_off (by omega)
  have hcw : cw.toNat = t.toNat + 752 := toNat_off (by omega)
  have hTF' : t.toNat + 760 ≤ fb.toNat ∨ fb.toNat + (80 + 8) ≤ t.toNat := hTF
  have hap1 : NativeRustcVm.Apart fb (80 + 8) rb 48 := by
    show fb.toNat + (80 + 8) ≤ rb.toNat ∨ rb.toNat + 48 ≤ fb.toNat; omega
  have hap2 : NativeRustcVm.Apart fb (80 + 8) cw 8 := by
    show fb.toNat + (80 + 8) ≤ cw.toNat ∨ cw.toNat + 8 ≤ fb.toNat; omega
  have hap3 : NativeRustcVm.Apart rb 48 cw 8 := by
    show rb.toNat + 48 ≤ cw.toNat ∨ cw.toNat + 8 ≤ rb.toNat; omega
  set env7 := frameEnv m0 st.data 80 [(rb, 48), (cw, 8)] (fun _ ↦ 0) 0
  have hwf7 : env7.WF := frame_wf (m0 := m0) (d := st.data) (F := 80)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩
    (rest2_ok ⟨mapped_off hTm (by show 368 + 48 * nr + 48 ≤ 760; omega),
        by show rb.toNat + 48 ≤ 2 ^ 64; omega⟩
      ⟨mapped_off hTm (by show 752 + 8 ≤ 760; omega), by show cw.toNat + 8 ≤ 2 ^ 64; omega⟩
      fun _ h ↦ h)
    (pairwise3 hap1 hap2 hap3)
  have hm7 : Match env7 pushS st.data := match_push hnr8 hTn' hf hrax hr14
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf7 nofun hpc hm7
    fun st8 hm8 hpc8 => ?_
  simp only [PcOk] at hpc8
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7c hwf7 nofun
    (hpc8.trans (hp.label NativeRustcVmX64.Vm.TStateReadCommitment.label_6_at)) hm8 fun st9 hm9 hpc9 => ?_
  obtain ⟨hepi, hrax9, hw0, hw1, hw2, hw3, hw4, hw5, hwc, hws9⟩ := push_c
  obtain ⟨hsv9, hrsp9⟩ := Frame.epilogue hf hwf7 hm9 hepi
  simp only [PcOk] at hpc9
  have hv0 := wordAt_write hm9 (r := 1) (o := 0) (b := rb) (sz := 48) rfl (by decide)
    (fun j hj ↦ by rw [Nat.zero_add]; exact hw0 j hj)
  rw [show (Sym.reg .r12).eval env7 = _ from h12, off_zero] at hv0
  have hv1 := wordAt_write hm9 (r := 1) (o := 8) (b := rb) (sz := 48) rfl (by decide) hw1
  rw [show (Sym.reg .r13).eval env7 = _ from h13] at hv1
  have hv2 := wordAt_write hm9 (r := 1) (o := 16) (b := rb) (sz := 48) rfl (by decide) hw2
  rw [show (Sym.load 0 24 8).eval env7 = _ from load_ofMachine (o := 24) rfl hel.1] at hv2
  have hv3 := wordAt_write hm9 (r := 1) (o := 24) (b := rb) (sz := 48) rfl (by decide) hw3
  rw [show (Sym.load 0 32 8).eval env7 = _ from load_ofMachine (o := 32) rfl hel.2] at hv3
  have hv4 := wordAt_write hm9 (r := 1) (o := 32) (b := rb) (sz := 48) rfl (by decide) hw4
  rw [show (Sym.reg .r15).eval env7 = _ from h15] at hv4
  have hv5 := wordAt_write hm9 (r := 1) (o := 40) (b := rb) (sz := 48) rfl (by decide) hw5
  rw [show (Sym.reg .rbx).eval env7 = _ from h3] at hv5
  have hvc := wordAt_write hm9 (r := 2) (o := 0) (b := cw) (sz := 8) rfl (by decide)
    (fun j hj ↦ by rw [Nat.zero_add]; exact hwc j hj)
  have hcnt' : (Sym.bin .add .W64 (.load 2 0 8) (.lit 1)).eval env7 =
      nr.toUInt64.toBitVec + BitVec.ofNat 64 1 := by
    sym_simp
    rw [load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hts.n_roots)]
  rw [hcnt', toUInt64_succ (by omega), off_zero] at hvc
  have hroot : RootAt st9.data.dmem rb
      ⟨#v[x0.c0, x0.c1, x1.c0, x1.c1], (reg m0 .rsi).toNat, (reg m0 .rdx).toNat⟩ := by
    refine ⟨(reg m0 .rsi).isLt, (reg m0 .rdx).isLt, ?_, ?_, ?_⟩
    · show NativeRustcVm.WordsAt _ rb [x0.c0, x0.c1, x1.c0, x1.c1]
      refine wordsAt_cons.mpr ⟨hv0, wordsAt_cons.mpr ⟨hv1, ?_⟩⟩
      rw [off_off]
      refine wordsAt_cons.mpr ⟨hv2, wordsAt_cons.mpr ⟨?_, wordsAt_nil _ _⟩⟩
      rw [off_off]; exact hv3
    · show NativeRustcVm.WordAt _ (off rb 32) (reg m0 .rsi).toNat.toUInt64
      rw [toUInt64_toNat]; exact hv4
    · show NativeRustcVm.WordAt _ (off rb 40) (reg m0 .rdx).toNat.toUInt64
      rw [toUInt64_toNat]; exact hv5
  have hs9 : NativeRustcVm.SameOutside st.data.dmem st9.data.dmem (fun q ↦ Touch t tstateBytes
      (fun j ↦ (368 + 48 * nr ≤ j ∧ j < 416 + 48 * nr) ∨ 752 ≤ j) q ∨ False) := by
    intro q hq
    refine hm9.get?_mem0 hwf7 fun hW ↦ hq (Or.inl ?_)
    rcases touch_of_written2 hwf7 (r := 1) (r' := 2) (W := fun _ ↦ True) (W' := fun _ ↦ True)
      rfl rfl (fun w hw ↦ (hws9 w hw).imp (fun h ↦ ⟨h.1, h.2, fun _ _ _ ↦ trivial⟩)
        (fun h ↦ ⟨h.1, h.2, fun _ _ _ ↦ trivial⟩)) hW with h | h
    · exact touch_sub hTn (by omega) (inRange_of_touch (by show rb.toNat + 48 ≤ 2 ^ 64; omega) h)
        fun j h1 h2 ↦ Or.inl ⟨by omega, by omega⟩
    · exact touch_sub hTn (by omega) (inRange_of_touch (by show cw.toNat + 8 ≤ 2 ^ 64; omega) h)
        fun j h1 _ ↦ Or.inr h1
  refine .done _ ⟨by rw [hpc9]; exact hf.load_ret hst (by decide), hrsp9, ?_,
    hts.with_root (hm9.kept hwf7) (fun _ h ↦ h.elim) hs9 hlt hroot hvc, fun q hq ↦ ?_, hsv9⟩
  · rw [show reg st9.data .rax = _ from hm9.regs .rax _ hrax9]
    exact merge_one_mod _
  · refine hs9 q ?_
    rintro (⟨j, hj, -, rfl⟩ | h)
    · exact hq (inRange_off_self hj (by simp only [tstateBytes]; omega))
    · exact h

/-- **`TState::read_commitment` meets its contract.** -/
theorem readCommitment_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s) (ReadCommitmentPost a s) := by
  rintro m0 ⟨hst, hrc, hts, htok, hroots, hgot⟩
  set t := reg m0 .rdi
  set fb := stackBelow m0 80
  have hn : readCommitmentStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (80 + 8) := frame_noWrap hst (by decide)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hTF : NativeRustcVm.Apart t 760 fb (80 + 8) := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb (80 + 8) :=
    apart_frame htok.2.1 hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb (80 + 8) q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hfr : ∀ {d : MachineData} {o : Nat} {sl : Slots} (ret : BitVec 64), Frame m0 80 sl o d →
      (frameEnv m0 d 80 [] (fun _ ↦ 0) ret).WF := fun ret hf ↦
    frame_wf ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩ (by simp)
      (List.pairwise_singleton _ _)
  -- `b0`: the prologue, `call read_scalar`.
  have hwf0 := hfr (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadCommitment.b0Offset + b0.length)).toBitVec (Frame.entry (F := 80) (m0 := m0))
  unfold NativeRustcVmX64.Vm.TStateReadCommitment.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.TStateReadCommitment.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hx7, hx6, hx3, hx14, hx15⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 80 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 80) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0) :=
    SameOutside.mono hs1 fun q hq ↦ Or.inr (inRange_frame_stack h8 hn (by decide) hq)
  have hX3 : reg st1.data .rbx = reg m0 .rdx := hm1.regs .rbx _ hx3
  have hX14 : reg st1.data .r14 = t := hm1.regs .r14 _ hx14
  have hX15 : reg st1.data .r15 = reg m0 .rsi := hm1.regs .r15 _ hx15
  refine call_read hrs hst hrc htok hgot hpc1 hf1 ((hm1.regs .rdi _ hx7).trans (eval_ptr0 16))
    (hm1.regs .rsi _ hx6) (hts.frame hf1.kept (fun q hq ↦ hRF q (inRange_mono hq (by omega))) hs1)
    hso1 fun st2 hpc2 hf2 hout2 hnext2 hso2 hsv2 => ?_
  have h3₂ : reg st2.data .rbx = reg m0 .rdx := (hsv2.1 .rbx rfl).trans hX3
  have h14₂ : reg st2.data .r14 = t := (hsv2.1 .r14 rfl).trans hX14
  have h15₂ : reg st2.data .r15 = reg m0 .rsi := (hsv2.1 .r15 rfl).trans hX15
  -- `b1`: the first tag; `b2` runs on in the same environment.
  have hwf2 := hfr (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadCommitment.b2Offset + b2.length)).toBitVec hf2
  have hm2 : Match (frameEnv m0 st2.data 80 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadCommitment.b2Offset + b2.length)).toBitVec)
      doneS st2.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadCommitment.b0_next)) hm2 fun st3 hm3 hpc3 => ?_
  simp only [PcOk] at hpc3
  sym_simp_at hpc3
  cases hr1 : readScalar.run s with
  | none =>
    rw [hr1] at hout2
    have h0 : NativeRustcVm.WordAt st2.data.dmem (off fb 16) 0 := hout2
    have ht0 : (frameEnv m0 st2.data 80 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadCommitment.b2Offset + b2.length)).toBitVec).load 0 16 4 = BitVec.ofNat 64 0 :=
      load4_of_tag (Or.inl rfl) h0
    simp only [ht0] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    have hnone : (readCommitment (reg m0 .rsi).toNat (reg m0 .rdx).toNat).run s = none := by
      rw [run_eq, hr1]; rfl
    refine Eventually.mono (finish_fail hp hst hf2 exit_b6a exit_b7a fail_a
      (hpc3.trans (hp.label NativeRustcVmX64.Vm.TStateReadCommitment.label_5_at)) hm3)
      fun st' ⟨hpc', hrsp', hrax', hd', hsv'⟩ ↦ ⟨hpc', hrsp', ?_, ?_, ?_, hsv'⟩
    · show (reg st'.data .rax).toNat % 256 =
        (okWord ((readCommitment (reg m0 .rsi).toNat (reg m0 .rdx).toNat).run s).isSome).toNat
      rw [hnone, hrax']; rfl
    · intro u s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd']; exact hso2 q hq
  | some p =>
  obtain ⟨x0, s1⟩ := p
  rw [hr1] at hout2
  obtain ⟨ht1, hel1⟩ := (hout2 : OptEWAt st2.data.dmem (off fb 16) (some x0))
  rw [ewAt_iff, off_off, off_off] at hel1
  have hts1 : TStateAt st2.data.dmem t a s1 := hnext2 x0 s1 hr1
  have ht1' : (frameEnv m0 st2.data 80 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadCommitment.b2Offset + b2.length)).toBitVec).load 0 16 4 = BitVec.ofNat 64 1 :=
    load4_of_tag (Or.inr rfl) ht1
  simp only [ht1'] at hpc3
  simp (config := { decide := true }) only [↓reduceIte] at hpc3
  -- `b2`: the first element kept in R12, R13, `call read_scalar`.
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf2 (fun _ _ ↦ rfl)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadCommitment.b1_next)) hm3 fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hws4, hx7₄, hx6₄, hx12₄, hx13₄, hcs4⟩ := after_eq run_b2 ▸ ok_b2
  have hf4 : Frame m0 80 slots 0 st4.data := Frame.of_block hf2 hwf2 hm4 hmid4 slots_le
  have hs4 : NativeRustcVm.SameOutside st2.data.dmem st4.data.dmem (NativeRustcVm.InRange fb 8) :=
    sameOutside_low hwf2 hm4 (r := 0) rfl (by decide) hws4
  have hX12₄ : reg st4.data .r12 = x0.c0.toBitVec :=
    (hm4.regs .r12 _ hx12₄).trans (load_ofMachine (o := 24) rfl hel1.1)
  have hX13₄ : reg st4.data .r13 = x0.c1.toBitVec :=
    (hm4.regs .r13 _ hx13₄).trans (load_ofMachine (o := 32) rfl hel1.2)
  have hk4 : ∀ r, calleeSaved r = true → r ≠ .r12 → r ≠ .r13 → reg st4.data r = reg st2.data r :=
    fun r hr h1 h2 ↦ hm4.regs r _ (hcs4 r (mem_allRegs r) hr h1 h2)
  have h3₄ : reg st4.data .rbx = reg m0 .rdx := (hk4 .rbx rfl (by decide) (by decide)).trans h3₂
  have h14₄ : reg st4.data .r14 = t := (hk4 .r14 rfl (by decide) (by decide)).trans h14₂
  have h15₄ : reg st4.data .r15 = reg m0 .rsi :=
    (hk4 .r15 rfl (by decide) (by decide)).trans h15₂
  have hso4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs4 q fun h ↦ hq (Or.inr (inRange_frame_stack h8 hn (by decide)
      (inRange_mono h (by decide))))]
    exact hso2 q hq
  have hts4 : TStateAt st4.data.dmem t a s1 :=
    hts1.frame (hm4.kept hwf2) (fun q hq ↦ hRF q (inRange_mono hq (by decide))) hs4
  refine call_read hrs hst hrc htok hgot hpc4 hf4 ((hm4.regs .rdi _ hx7₄).trans (eval_ptr0 16))
    ((hm4.regs .rsi _ hx6₄).trans h14₂) hts4 hso4
    fun st5 hpc5 hf5 hout5 hnext5 hso5 hsv5 => ?_
  have h12₅ : reg st5.data .r12 = x0.c0.toBitVec := (hsv5.1 .r12 rfl).trans hX12₄
  have h13₅ : reg st5.data .r13 = x0.c1.toBitVec := (hsv5.1 .r13 rfl).trans hX13₄
  have h3₅ : reg st5.data .rbx = reg m0 .rdx := (hsv5.1 .rbx rfl).trans h3₄
  have h14₅ : reg st5.data .r14 = t := (hsv5.1 .r14 rfl).trans h14₄
  have h15₅ : reg st5.data .r15 = reg m0 .rsi := (hsv5.1 .r15 rfl).trans h15₄
  -- `b3`: the second tag.
  have hwf5 := hfr 0 hf5
  have hm5 : Match (frameEnv m0 st5.data 80 [] (fun _ ↦ 0) 0) doneS st5.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf5.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf5 nofun
    (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadCommitment.b2_next)) hm5 fun st6 hm6 hpc6 => ?_
  obtain ⟨hmid6, hmem6, hcs6⟩ := ok_b3
  simp only [PcOk] at hpc6
  sym_simp_at hpc6
  cases hr2 : readScalar.run s1 with
  | none =>
    rw [hr2] at hout5
    have h0 : NativeRustcVm.WordAt st5.data.dmem (off fb 16) 0 := hout5
    have ht0 : (frameEnv m0 st5.data 80 [] (fun _ ↦ 0) 0).load 0 16 1 = BitVec.ofNat 64 0 :=
      load1_of_tag (Or.inl rfl) h0
    simp only [ht0] at hpc6
    simp (config := { decide := true }) only [↓reduceIte] at hpc6
    have hnone : (readCommitment (reg m0 .rsi).toNat (reg m0 .rdx).toNat).run s = none := by
      rw [run_eq, hr1]; show (readScalar.run s1).bind _ = none; rw [hr2]; rfl
    refine Eventually.mono (finish_fail hp hst hf5 exit_b6b exit_b7b fail_b
      (hpc6.trans (hp.label NativeRustcVmX64.Vm.TStateReadCommitment.label_5_at)) hm6)
      fun st' ⟨hpc', hrsp', hrax', hd', hsv'⟩ ↦ ⟨hpc', hrsp', ?_, ?_, ?_, hsv'⟩
    · show (reg st'.data .rax).toNat % 256 =
        (okWord ((readCommitment (reg m0 .rsi).toNat (reg m0 .rdx).toNat).run s).isSome).toNat
      rw [hnone, hrax']; rfl
    · intro u s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd']; exact hso5 q hq
  | some p =>
  obtain ⟨x1, s2⟩ := p
  rw [hr2] at hout5
  obtain ⟨ht2, hel2⟩ := (hout5 : OptEWAt st5.data.dmem (off fb 16) (some x1))
  rw [ewAt_iff, off_off, off_off] at hel2
  have hts2 : TStateAt st5.data.dmem t a s2 := hnext5 x1 s2 hr2
  have ht2' : (frameEnv m0 st5.data 80 [] (fun _ ↦ 0) 0).load 0 16 1 = BitVec.ofNat 64 1 :=
    load1_of_tag (Or.inr rfl) ht2
  simp only [ht2'] at hpc6
  simp (config := { decide := true }) only [↓reduceIte] at hpc6
  have hroots2 : s2.roots = s.roots := (readScalar_roots hr2).trans (readScalar_roots hr1)
  set nr := s2.roots.size with hnr
  have hnr8 : nr < 8 := by rw [hnr, hroots2]; exact hroots
  -- `b4`: the count against `8`.
  have hf6 : Frame m0 80 slots 8 st6.data := Frame.of_block hf5 hwf5 hm6 hmid6 slots_le
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq hwf5 hmem6
  have hk6 : ∀ r, calleeSaved r = true → reg st6.data r = reg st5.data r :=
    fun r hr ↦ hm6.regs r _ (hcs6 r (mem_allRegs r) hr)
  have hso6 : NativeRustcVm.SameOutside m0.dmem st6.data.dmem (Out m0) := by rw [hd6]; exact hso5
  have hts6 : TStateAt st6.data.dmem t a s2 := by rw [hd6]; exact hts2
  have hwf6 := frame_wf (m0 := m0) (d := st6.data) (F := 80) (rest := [(t, 760)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf6.kept, hfnw⟩
    (fun y hy ↦ by
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨Mapped.keeps hTm hf6.kept, hTn⟩)
    (List.pairwise_pair.mpr (Apart.symm' hTF))
  have hm6' : Match (frameEnv m0 st6.data 80 [(t, 760)] (fun _ ↦ 0) 0) countS st6.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hf6.rsp_eval, known_ptr rfl ((hk6 .r14 rfl).trans h14₅), trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf6 nofun
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadCommitment.b3_next)) hm6' fun st7 hm7 hpc7 => ?_
  obtain ⟨hmid7, hmem7, hx0₇, hx14₇, hcs7⟩ := ok_b4
  have hf7 : Frame m0 80 slots 8 st7.data := Frame.of_block hf6 hwf6 hm7 hmid7 slots_le
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq hwf6 hmem7
  have hk7 : ∀ r, calleeSaved r = true → r ≠ .r14 → reg st7.data r = reg st6.data r :=
    fun r hr h ↦ hm7.regs r _ (hcs7 r (mem_allRegs r) hr h)
  have hcnt : (frameEnv m0 st6.data 80 [(t, 760)] (fun _ ↦ 0) 0).load 1 752 8 =
      nr.toUInt64.toBitVec :=
    load_ofMachine (o := 752) rfl hts6.n_roots
  have hnr64 : nr.toUInt64.toBitVec.toNat = nr := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hc7 : (SBool.cmp .ult .W64 (.load 1 752 8) (.lit 8)).not.eval
      (frameEnv m0 st6.data 80 [(t, 760)] (fun _ ↦ 0) 0) = false := by
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, hcnt, BitVec.ult, hnr64,
      BitVec.toNat_ofNat]
    simp [show nr < 8 from hnr8]
  simp only [PcOk] at hpc7
  rw [hc7] at hpc7
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc7
  have h12₇ : reg st7.data .r12 = x0.c0.toBitVec :=
    (hk7 .r12 rfl (by decide)).trans ((hk6 .r12 rfl).trans h12₅)
  have h13₇ : reg st7.data .r13 = x0.c1.toBitVec :=
    (hk7 .r13 rfl (by decide)).trans ((hk6 .r13 rfl).trans h13₅)
  have h15₇ : reg st7.data .r15 = reg m0 .rsi :=
    (hk7 .r15 rfl (by decide)).trans ((hk6 .r15 rfl).trans h15₅)
  have h3₇ : reg st7.data .rbx = reg m0 .rdx :=
    (hk7 .rbx rfl (by decide)).trans ((hk6 .rbx rfl).trans h3₅)
  have hel7 : NativeRustcVm.WordAt st7.data.dmem (off fb 24) x1.c0 ∧
      NativeRustcVm.WordAt st7.data.dmem (off fb 32) x1.c1 := by
    rw [hd7, hd6]; exact hel2
  have hrun : (readCommitment (reg m0 .rsi).toNat (reg m0 .rdx).toNat).run s = some ((),
      { s2 with roots := (s2.roots.push
        ⟨#v[x0.c0, x0.c1, x1.c0, x1.c1], (reg m0 .rsi).toNat, (reg m0 .rdx).toNat⟩) }) := by
    rw [run_eq, hr1]; show (readScalar.run s1).bind _ = _; rw [hr2]; rfl
  refine Eventually.mono (push_run (a := a) hp hst hf7 (by rw [hd7]; exact hts6)
    (by rw [hroots2]; exact hroots) hTF ((hm7.regs .rax _ hx0₇).trans hcnt)
    ((hm7.regs .r14 _ hx14₇).trans (eval_ptr rfl)) h12₇ h13₇ h15₇ h3₇ hel7
    (hpc7.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadCommitment.b4_next)))
    fun st' ⟨hpc', hrsp', hal, hts', hs', hsv'⟩ ↦ ⟨hpc', hrsp', ?_, ?_, ?_, hsv'⟩
  · show (reg st'.data .rax).toNat % 256 =
      (okWord ((readCommitment (reg m0 .rsi).toNat (reg m0 .rdx).toNat).run s).isSome).toNat
    rw [hrun]; exact hal
  · intro u s' h
    rw [hrun] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hts'
  · intro q hq
    rw [hs' q fun h ↦ hq (Or.inl h), hd7]
    exact hso6 q hq

end

end NativeRustcVmX64.Transcript.ReadCommitment
