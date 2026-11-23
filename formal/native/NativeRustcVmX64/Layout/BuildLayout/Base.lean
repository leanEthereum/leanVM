module

public import NativeRustcVmX64.Layout.BuildLayout.Exec
public import NativeRustcVmX64.Layout.BuildLayout.Model
public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.BitLength.Names

/-!
# `build_layout` on x86-64: the body, words, conditions, the epilogue

The body (`B m0 o`): `BuildFrame.Bd` with the 1360-byte frame, `build_layout`'s stack and the
layout as output. Words of a region kept by a block missing them (`Ws.keep`) or written by it
(`wordAt_write`); the conditions the executor states (`c0_eval`, `flag_or`, `cRow_eval`); the
epilogue (`epi`, `fail`); a call of `bit_length` (`callBL`).
-/

namespace NativeRustcVmX64.Layout.BuildLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BuildLayout NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

@[expose] public section

/-- The output: the layout. -/
abbrev R (m0 : MachineData) : BitVec 64 → Prop := NativeRustcVm.InRange (ll m0) layoutBytes
/-- **The body**, RSP at the frame's offset `o`. -/
abbrev B (m0 : MachineData) (o : Nat) (d : MachineData) : Prop := Bd m0 1360 7824 slots (R m0) o d
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 1360

section
variable [Labels]

/-- The facts of the precondition the blocks use. -/
structure Facts (bc : Array UInt64) (m0 : MachineData) : Prop where
  stack : StackOk m0 7824
  rod : RodataAt m0 7824
  size : nN m0 = bc.size
  rr : Readable m0 (rp m0) 48
  ro : OffStack m0 (rp m0) 48 7824
  lr : Readable m0 (ll m0) layoutBytes
  lo : OffStack m0 (ll m0) layoutBytes 7824
  lrod : RodataApart (ll m0) layoutBytes
  ap : Apart (rp m0) 48 (ll m0) layoutBytes
  got : GotAt m0 buildLayoutStack [(rp m0, 48), (ll m0, layoutBytes)] ["memset"]

/-- `build_layout`'s postcondition, reached. -/
abbrev Post (bc : Array UInt64) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ BuildLayoutPost bc m0 st.data

end

end

public section

theorem SS_eq : buildLayoutStack = 7824 := rfl
theorem layoutBytes_eq : layoutBytes = 3912 := rfl
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1360 := by decide
theorem slots_ge : ∀ p ∈ slots, 1312 ≤ p.1 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

theorem cs_callee : ∀ r ∈ cs, calleeSaved r = true := by
  intro r hr
  simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A register a block keeps (`Keeps`). -/
theorem kreg [Labels] {d d' : MachineData} {rs0 : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {Sy : SState} (hm : Match (Env.ofMachine d rs0 vs ret) Sy d')
    {rs : List Reg64} (h : Keeps Sy rs = true) {r : Reg64} (hr : r ∈ rs) : reg d' r = reg d r :=
  keeps_reg hm h hr

theorem lit_toNat {c : Nat} (h : c < 2 ^ 64) : (BitVec.ofNat 64 c).toNat = c :=
  NativeRustcVm.toNat_ofNat_of_lt h

/-- A branch on a condition the executor evaluates to `decide P`. -/
theorem pc_of {pc a b : Int64} {c : Bool} {P : Prop} [Decidable P]
    (h : pc = if c = true then a else b) (hc : c = decide P) : (P → pc = a) ∧ (¬P → pc = b) := by
  subst hc
  exact ⟨fun hp ↦ by simpa [hp] using h, fun hp ↦ by simpa [hp] using h⟩

section
variable [Labels] (env : Env)

theorem ult_eval (a b : Sym) :
    (SBool.cmp .ult .W64 a b).eval env = decide ((a.eval env).toNat < (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, BitVec.ult]

theorem eq_eval (a b : Sym) :
    (SBool.cmp .eq .W64 a b).eval env = decide ((a.eval env).toNat = (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64]
  by_cases h : a.eval env = b.eval env
  · simp [h]
  · simp only [beq_eq_false_iff_ne.mpr h]
    exact (decide_eq_false fun h' ↦ h (BitVec.eq_of_toNat_eq h')).symm

/-- **`b0`'s test**: the length not a power of two. -/
theorem c0_eval : c0.eval env = decide ¬Pow2 (env.regs .rdi).toNat := by
  have hd : (dec (.reg .rdi)).eval env = env.regs .rdi + BitVec.ofNat 64 18446744073709551615 := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
  have hx : (Sym.bin .xor .W64 (.reg .rdi) (dec (.reg .rdi))).eval env =
      env.regs .rdi ^^^ (env.regs .rdi + BitVec.ofNat 64 18446744073709551615) := by
    show BinOp.apply .xor .W64 (env.regs .rdi) ((dec (.reg .rdi)).eval env) = _
    rw [hd]; simp only [BinOp.apply, low_W64, ext_W64]
  show ((SBool.cmp .ult .W64 _ _).eval env || (SBool.cmp .eq .W64 _ _).eval env) = _
  rw [ult_eval, eq_eval, hx, hd]
  exact Bool.eq_iff_iff.mpr ⟨fun h ↦ decide_eq_true ((pow2_test _).mp h),
    fun h ↦ (pow2_test _).mpr (of_decide_eq_true h)⟩

/-- Two flags or-ed (`setae`, `orb`, `jne`). -/
theorem flag_or (a c : Sym) (b1 b2 : SBool) :
    (SBool.cmp .eq .W8 (.bin .or .W8 (.bin .merge .W8 a (flag b1)) (.bin .merge .W8 c (flag b2)))
      (.lit 0)).not.eval env = (!b1.eval env || !b2.eval env) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply]
  rw [Arrays.low8_replaceLow, Arrays.low8_replaceLow]
  rcases Bool.eq_false_or_eq_true (SBool.eval env b1) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (SBool.eval env b2) with h2 | h2 <;>
    simp only [h1, h2] <;> decide

/-- A row count past `2 ^ 30`. -/
theorem cRow_eval (o : Nat) : (cRow o).eval env = decide (2 ^ 30 < (env.load 1 o 8).toNat) := by
  show (!(SBool.cmp .ult .W64 (.load 1 o 8) (.lit 1073741824)).eval env &&
    !(SBool.cmp .eq .W64 (.load 1 o 8) (.lit 1073741824)).eval env) = _
  rw [ult_eval, eq_eval]
  show (!decide ((env.load 1 o 8).toNat < 1073741824) && !decide ((env.load 1 o 8).toNat =
    1073741824)) = _
  by_cases h : 2 ^ 30 < (env.load 1 o 8).toNat
  · rw [decide_eq_true h, decide_eq_false (by omega), decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h]
    by_cases h' : (env.load 1 o 8).toNat < 1073741824
    · rw [decide_eq_true h']; rfl
    · rw [decide_eq_false h', decide_eq_true (by omega)]; rfl

/-- `x - 1`, saturating. -/
theorem sat_eval (x z : Sym) (hz : (z.eval env).toNat = 0) :
    ((sat x z).eval env).toNat = (x.eval env).toNat - 1 := by
  show (if (SBool.cmp .ult .W64 x (.lit 1)).eval env = true then z.eval env else
    BinOp.apply .sub .W64 (x.eval env) (BitVec.ofNat 64 1)).toNat = _
  rw [ult_eval]
  have h1 : ((Sym.lit 1).eval env).toNat = 1 := rfl
  rw [h1]
  by_cases h : (x.eval env).toNat < 1
  · rw [decide_eq_true h]; simp only [↓reduceIte]; omega
  · rw [decide_eq_false h]
    simp only [Bool.false_eq_true, ↓reduceIte, BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_sub, show (BitVec.ofNat 64 1).toNat = 1 from rfl]
    have := (x.eval env).isLt
    omega

end

variable {m0 : MachineData}

/-! ## Words -/

section
variable [Labels]

/-- **Words a block missed**: of region `r`, at offsets its writes in `r` miss. -/
theorem Ws.keep {d d' : MachineData} {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {Sy : SState} (hwf : (Env.ofMachine d rs vs ret).WF)
    (hm : Match (Env.ofMachine d rs vs ret) Sy d') (hin : writesIn Sy = true) {r : Nat}
    {b : BitVec 64} {n : Nat} (hb : rs[r]? = some (b, n)) {ws : List (Nat × UInt64)}
    (hle : ∀ p ∈ ws, p.1 + 8 ≤ n)
    (hmiss : ∀ w ∈ Sy.mem, w.r = r → ∀ p ∈ ws, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off)
    (h : Ws d.dmem b ws) : Ws d'.dmem b ws := by
  intro p hp
  have hnw := hwf.noWrap r b n hb
  have hpl := hle p hp
  refine bytesAt_congr (h p hp) fun j hj ↦ ?_
  have hj8 : j < 8 := by simpa [NativeRustcVm.length_wordBytes] using hj
  rw [off_add]
  refine hm.get?_mem0 hwf fun hw ↦ ?_
  obtain ⟨w, hw', b', sz, hb', i, hi1, hi2, he⟩ := written_off hwf hw
  have hwin : w.off + w.n ≤ sz := by
    have := List.all_eq_true.mp hin w hw'
    revert this
    cases hS : Sy.regions[w.r]? with
    | none => simp
    | some sz' =>
      intro this
      simp only [decide_eq_true_eq] at this
      obtain ⟨b'', hb''⟩ := hm.regions _ _ hS
      rw [hb'] at hb''
      cases hb''
      omega
  have hnw' := hwf.noWrap _ b' sz hb'
  have e1 : (off b (p.1 + j)).toNat = b.toNat + (p.1 + j) := toNat_off (by omega)
  have e2 : (off b' i).toNat = b'.toNat + i := toNat_off (by omega)
  rw [he] at e1
  by_cases hr : w.r = r
  · rw [hr] at hb'
    change rs[r]? = _ at hb'
    rw [hb] at hb'
    simp only [Option.some.injEq, Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    have := hmiss w hw' hr p hp
    omega
  · have := hwf.disjoint _ _ _ _ _ _ hr hb' hb
    omega

omit [Labels] in
/-- Writes a `Misses` check clears. -/
theorem misses_of {Sy : SState} {r : Nat} {os : List Nat} (h : Misses r os Sy = true)
    {ws : List (Nat × UInt64)} (hos : ws.map (·.1) = os) :
    ∀ w ∈ Sy.mem, w.r = r → ∀ p ∈ ws, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off := by
  intro w hw hr p hp
  have := List.all_eq_true.mp h w hw
  simp only [hr, bne_self_eq_false, Bool.false_or, List.all_eq_true, decide_eq_true_eq] at this
  exact this p.1 (hos ▸ List.mem_map_of_mem hp)

omit [Labels] in
/-- Writes below `lo` miss words from `lo`. -/
theorem below_of {Sy : SState} {r lo : Nat} (h : ∀ w ∈ Sy.mem, w.r = r → w.off + w.n ≤ lo)
    {ws : List (Nat × UInt64)} (hws : ∀ p ∈ ws, lo ≤ p.1) :
    ∀ w ∈ Sy.mem, w.r = r → ∀ p ∈ ws, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off :=
  fun w hw hr p hp ↦ .inl ((h w hw hr).trans (hws p hp))

/-- The new word `v` at offset `o` of region `r`. -/
theorem w_write {d d' : MachineData} {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {Sy : SState} (hm : Match (Env.ofMachine d rs vs ret) Sy d') {r : Nat}
    {b : BitVec 64} {n : Nat} (hb : rs[r]? = some (b, n)) {o : Nat} (ho : o + 8 ≤ n) {v : Sym}
    (hw : ∀ t < 8, findWrite r (o + t) Sy.mem = some (v, t)) {u : UInt64}
    (hu : (v.eval (Env.ofMachine d rs vs ret)).toNat = u.toNat) : WordAt d'.dmem (off b o) u := by
  have := wordAt_write hm (r := r) (o := o) (b := b) (sz := n) hb ho hw
  rwa [show UInt64.ofBitVec (v.eval (Env.ofMachine d rs vs ret)) = u from
    UInt64.toNat.inj (by rw [UInt64.toNat_ofBitVec, hu])] at this

end

theorem Ws.cons {d : Mem 64} {b : BitVec 64} {o : Nat} {v : UInt64} {ws : List (Nat × UInt64)}
    (h : WordAt d (off b o) v) (hs : Ws d b ws) : Ws d b ((o, v) :: ws) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h
  · exact hs p hp

theorem Ws.of_eq {d d' : Mem 64} {b : BitVec 64} {ws : List (Nat × UInt64)} (h : Ws d b ws)
    (hd : d' = d) : Ws d' b ws := hd ▸ h

/-! ## The geometry -/

section
variable [Labels] {bc : Array UInt64}

theorem Facts.of_pre (h : BuildLayoutPre bc m0) : Facts bc m0 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

theorem Facts.rsp (hF : Facts bc m0) : 7824 ≤ (rspOf m0).toNat ∧ (rspOf m0).toNat + 8 ≤ 2 ^ 64 :=
  ⟨hF.stack.1, hF.stack.2.1⟩

theorem Facts.fb_toNat (hF : Facts bc m0) : (fb m0).toNat = (rspOf m0).toNat - 1360 :=
  stackBelow_toNat (by have := hF.rsp; omega)

theorem Facts.off_toNat (hF : Facts bc m0) {o : Nat} (ho : o < 1368) :
    (off (fb m0) o).toNat = (rspOf m0).toNat - 1360 + o := by
  have := hF.rsp
  rw [toNat_off (by rw [hF.fb_toNat]; omega), hF.fb_toNat]

theorem Facts.sb_toNat (hF : Facts bc m0) : (stackBelow m0 7824).toNat = (rspOf m0).toNat - 7824 :=
  stackBelow_toNat hF.rsp.1

theorem Facts.lnw (hF : Facts bc m0) : (ll m0).toNat + 3912 ≤ 2 ^ 64 := hF.lr.2

/-- The layout's first `120` bytes, mapped and not wrapping in a body. -/
theorem Facts.lay (hF : Facts bc m0) {o : Nat} {d : MachineData} (hb : B m0 o d) :
    NativeRustcVm.Mapped d.dmem (ll m0) 120 ∧ NativeRustcVm.NoWrap (ll m0) 120 :=
  ⟨Mapped.keeps (fun i hi ↦ hF.lr.1 i (by rw [layoutBytes_eq]; omega)) hb.fr.kept,
    by have := hF.lnw; unfold NativeRustcVm.NoWrap; omega⟩

/-- The layout apart from the frame. -/
theorem Facts.lay_apart (hF : Facts bc m0) {n : Nat} (hn : n ≤ 3912) :
    NativeRustcVm.Apart (fb m0) (1360 + 8) (ll m0) n := by
  show NativeRustcVm.Apart (stackBelow m0 1360) (1360 + 8) (ll m0) n
  have := apart_frame hF.lo hF.rsp.1 (show 1360 ≤ 7824 by decide)
  unfold NativeRustcVm.Apart at this ⊢
  rw [layoutBytes_eq] at this
  omega

/-- Part of the layout is in the output. -/
theorem Facts.lay_R (hF : Facts bc m0) {o n : Nat} (h : o + n ≤ 3912) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (ll m0) o) n q) : R m0 q :=
  NativeRustcVm.InRange.of_sub hq (by unfold NativeRustcVm.NoWrap; rw [layoutBytes_eq]; exact hF.lnw)
    (by rw [layoutBytes_eq]; exact h)

/-- The output apart from the frame. -/
theorem Facts.R_frame (hF : Facts bc m0) {q : BitVec 64} (h : R m0 q) :
    ¬ NativeRustcVm.InRange (fb m0) (1360 + 8) q :=
  not_inRange_of_apart (apart_frame hF.lo hF.rsp.1 (by decide)) hF.lr.2
    (frame_noWrap hF.stack (by decide)) h

end

/-! ## Blocks -/

variable [Host] {k : Nat} {bc : Array UInt64}

/-- A body in the frame's environment, RSP at offset `8`. -/
theorem match0 {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} (hb : B m0 8 d)
    (hr : RegionsOk [] rest) :
    Match (frameEnv m0 d 1360 rest (fun _ ↦ 0) ret) bodyS d :=
  match_ofMachine ⟨rfl, hr⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial trivial

/-- **A block of the frame alone** keeps the body. -/
theorem run0 (hF : Facts bc m0) {ds : List Directive} {kk : Nat} {Sy1 : SState} {x : Exit}
    {st : MachineState} {o' : Nat} {ret : BitVec 64} {Q : MachineState → Prop}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds bodyS = some (Sy1, x))
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (kk + ds.length)).toBitVec)
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 8 st.data) (hok : MidOk 1360 o' slots Sy1 = true)
    (cont : ∀ st', Match (frameEnv m0 st.data 1360 [] (fun _ ↦ 0) ret) Sy1 st'.data →
      PcOk (frameEnv m0 st.data 1360 [] (fun _ ↦ 0) ret) x (Host.addrOf (kk + ds.length)) st' →
      B m0 o' st'.data → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hwf := fr_wf0 (vars := fun _ ↦ 0) (ret := ret) hb hF.stack (by decide)
  exact exec_at hk hx hwf hret hpc (match0 hb trivial) fun st' hm' hpc' ↦
    cont st' hm' hpc' (hb.of_block0 hF.stack (by decide) hm' hok slots_le)

/-- **A block of registers only**: the body, memory kept. -/
theorem step0 (hF : Facts bc m0) {ds : List Directive} {kk : Nat} {Sy1 : SState} {x : Exit}
    {st : MachineState} {Q : MachineState → Prop} (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds bodyS = some (Sy1, x))
    (hret : ∀ l, x = .call l → (0 : BitVec 64) = (Host.addrOf (kk + ds.length)).toBitVec)
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 8 st.data)
    (hok : MidOk 1360 8 slots Sy1 = true) (hmem : Sy1.mem = [])
    (cont : ∀ st', Match (frameEnv m0 st.data 1360 [] (fun _ ↦ 0) 0) Sy1 st'.data →
      PcOk (frameEnv m0 st.data 1360 [] (fun _ ↦ 0) 0) x (Host.addrOf (kk + ds.length)) st' →
      B m0 8 st'.data → st'.data.dmem = st.data.dmem → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st :=
  run0 hF hk hx hret hpc hb hok fun st' hm' hpc' hb' ↦
    cont st' hm' hpc' hb' (hm'.dmem_eq (fr_wf0 hb hF.stack (by decide)) hmem)

/-- **A call of `bit_length`**: memory and the callee-saved registers kept, its result in RAX. -/
theorem callBL (hbl : Spec (label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) (hF : Facts bc m0)
    {st : MachineState} {next : Int64} {env : Env} (hpc : PcOk env (.call NativeRustcVmX64.Vm.BitLength.entryLabel) next st)
    (hb : B m0 0 st.data) {Q : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → B m0 8 st'.data → st'.data.dmem = st.data.dmem →
      (∀ r, calleeSaved r = true → reg st'.data r = reg st.data r) →
      (reg st'.data .rax).toNat = bitLength (reg st.data .rdi).toNat →
      Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  refine call_then hpc hbl (hb.stackOk hF.stack (by decide)) fun st' hpc' hrsp' hpost ↦ ?_
  obtain ⟨hax, hso, hsv⟩ := hpost
  rw [show bitLengthStack = 0 from rfl] at hso
  have hnot : ∀ q, ¬ NativeRustcVm.InRange (stackBelow st.data 0) 0 q := fun q h ↦ by
    unfold NativeRustcVm.InRange at h; omega
  have hd : st'.data.dmem = st.data.dmem := Std.ExtHashMap.ext_getElem? fun a ↦ by
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    exact hso a (hnot a)
  exact cont st' hpc' (hb.call hsv hrsp' hso (fun q h ↦ absurd h (hnot q))
    (fun _ _ _ _ h ↦ hnot _ h) (fun _ _ h ↦ hnot _ h)) hd hsv.1 hax

omit [Host] in
/-- `andb $1, %al`: AL the low bit. -/
theorem al_bit (x : BitVec 64) :
    (BinOp.apply .merge .W8 x (BinOp.apply .and .W8 x (BitVec.ofNat 64 1))).toNat % 256 =
      x.toNat % 2 := by
  have h := congrArg BitVec.toNat (Arrays.low8_replaceLow x
    (low .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 1))))
  rw [toNat_low, toNat_low] at h
  simp only [Width.bits] at h
  show (x.replaceLow (low .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 1)))).toNat % 256 = _
  rw [show (256 : Nat) = 2 ^ 8 from rfl, h]
  have h1 : (1 : Nat) % 2 ^ 64 % 2 ^ 8 = 1 := by decide
  simp only [BinOp.apply, toNat_ext, BitVec.toNat_and, toNat_low, Width.bits, BitVec.toNat_ofNat, h1,
    Nat.and_one_is_mod]
  omega

/-- **The epilogue** `b20`: AL the low bit of RAX. -/
theorem epi (hp : Placed code k) (hF : Facts bc m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b20Offset)) (hb : B m0 8 st.data) {b : Bool}
    (hax : (reg st.data .rax).toNat % 2 = (okWord b).toNat) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧
      OkAl s.data b ∧ Changes m0 s.data buildLayoutStack (ll m0) layoutBytes ∧ Saved m0 s.data ∧
      s.data.dmem = st.data.dmem) st := by
  obtain ⟨hepi, hmem, hrax⟩ := ok_b20
  refine hb.done hF.stack (by decide) (b20_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b20 hpc
    (match0 hb trivial) hepi hmem fun st' hm' hpc' hrsp' hsv' hd' ↦
      ⟨hpc', hrsp', ?_, fun q hq ↦ by rw [hd']; exact hb.same q hq, hsv', hd'⟩
  show (reg st'.data .rax).toNat % 256 = _
  rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
  show (BinOp.apply .merge .W8 (reg st.data .rax)
    (BinOp.apply .and .W8 (reg st.data .rax) (BitVec.ofNat 64 1))).toNat % 256 = _
  rw [al_bit]; exact hax

/-- **A failed check** (`b19`): `0` returned. -/
theorem fail (hp : Placed code k) (hF : Facts bc m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b19Offset)) (hb : B m0 8 st.data)
    (hr : buildLayout bc (lmN m0) (rowsOf m0) = none) :
    Eventually (step1 Host.exe) (Post bc m0) st := by
  obtain ⟨hok, hmem, hrax⟩ := ok_b19
  refine step0 hF (b19_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b19 nofun hpc hb hok hmem
    fun st1 hm1 hpc1 hb1 hd1 ↦ Eventually.mono (epi (b := false) hp hF hpc1 hb1 ?_)
      fun s ⟨h1, h2, h3, h4, h5, _⟩ ↦ ⟨h1, h2, ?_, fun L hL ↦ absurd hL (by rw [hr]; nofun), h4, h5⟩
  · rw [show reg st1.data .rax = _ from hm1.regs .rax _ hrax]; rfl
  · rw [hr]; exact h3

end

end NativeRustcVmX64.Layout.BuildLayout
