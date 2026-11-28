module

public import NativeRustcVmX64.Layout.StackOffsets.Body
public import NativeRustcX64.Spec.Mem
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.StackOffsets.Names

/-!
# `stack_offsets` on x86-64: the entry and the order array `0, 1, …, n - 1` (`b0` to `b12`)

`b0` tests `offsets`' length: shorter than `sizes`, `b1` returns `None` (`entry`). Else the
prologue `b2` pushes six registers and zeroes the order array (`memset`). `b3` keeps `8 n` in RBP;
with no block (`b6`) straight to the sort. `b4`: below eight blocks one word at a time (`b5`, then
`b10`, the loop `b11`, `Inv11`); from eight on, `b7` and the loop `b8` (`Inv8`) eight words a turn
up to `n / 8 * 8`, then `b9`, `b10`, `b11` the rest. `b12` sets the sort's arguments: `Ready` at
`b13` (`init_spec`).
-/

namespace NativeRustcVmX64.Layout.StackOffsets


open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.StackOffsets NativeRustcVmX64.Layout.BuildFrame
open NativeRustcVm (WordAt)

@[expose] public section

/-- **The order array being written**: `j` words. -/
structure Init (m0 : MachineData) (j : Nat) (d : MachineData) : Prop where
  b : B m0 8 d
  regs : Regs m0 d
  rbp : reg d .rbp = BitVec.ofNat 64 (8 * n m0)
  ords : Ords m0 j d.dmem
  le : j ≤ n m0

/-- **At `b13`**: the order array written, the sort's arguments set. -/
structure Ready (m0 d : MachineData) : Prop where
  init : Init m0 (n m0) d
  rdi : reg d .rdi = ob m0
  rsi : (reg d .rsi).toNat = n m0
  rdx : reg d .rdx = reg m0 .rdi
  rcx : (reg d .rcx).toNat = n m0

/-- **The eight-word loop's head** (`b8`). -/
structure Inv8 (m0 : MachineData) (q : Nat) (d : MachineData) : Prop where
  init : Init m0 (8 * q) d
  lt : 8 * q + 8 ≤ n m0 / 8 * 8
  rcx : (reg d .rcx).toNat = 8 * q
  r13 : reg d .r13 = ob m0 + BitVec.ofNat 64 (64 * q)
  rdx : (reg d .rdx).toNat = n m0 / 8 * 8
  rax : (reg d .rax).toNat = n m0 % 8

/-- **The one-word loop** (`b10`, `b11`): `c + j` words, `c` before it. -/
structure Inv11 (m0 : MachineData) (c j : Nat) (d : MachineData) : Prop where
  init : Init m0 (c + j) d
  lt : c + j < n m0
  rcx : (reg d .rcx).toNat = c
  r13 : reg d .r13 = ob m0 + BitVec.ofNat 64 (8 * c)
  rax : (reg d .rax).toNat = n m0 - c
  rdx : (reg d .rdx).toNat = j

/-- `stack_offsets`' postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ StackOffsetsPost m0 s.data

end

public section

/-! ## Values -/

theorem and7 : ∀ x : Fin 159, x.val &&& 7 = x.val % 8 := by decide +kernel

theorem andM8 : ∀ x : Fin 159, x.val &&& 18446744073709551608 = x.val / 8 * 8 := by
  decide +kernel

/-- Adding `2 ^ 64 - 8`: subtracting `8`. -/
theorem addM8 {x : BitVec 64} (h : 8 ≤ x.toNat) :
    (x + BitVec.ofNat 64 18446744073709551608).toNat = x.toNat - 8 := by
  have hb : (BitVec.ofNat 64 18446744073709551608).toNat = 18446744073709551608 := rfl
  have := x.isLt
  rw [BitVec.toNat_add, hb]
  omega

theorem shiftCount3 : shiftCount .W64 (BitVec.ofNat 64 3) = 3 := rfl

/-- `x >> 3 + 1` of `x = 8 n - 8`. -/
theorem shr_add (x : BitVec 64) (n : Nat) (hm : x.toNat = 8 * n - 8) (h1 : 1 ≤ n) (hn : n ≤ 158) :
    (BinOp.apply .add .W64 (BinOp.apply .shr .W64 x (BitVec.ofNat 64 3))
      (BitVec.ofNat 64 1)).toNat = n := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add]
  have hs : (x.ushiftRight 3).toNat = (8 * n - 8) / 8 := by
    show (x >>> 3).toNat = _
    rw [BitVec.toNat_ushiftRight, hm, Nat.shiftRight_eq_div_pow]
  rw [shiftCount3, hs, show (1#64).toNat = 1 from rfl]
  omega

section
variable [Labels] {env : Env}

theorem eN_def : eN.eval env = BinOp.apply .add .W64
    (BinOp.apply .shr .W64 (eM8.eval env) (BitVec.ofNat 64 3)) (BitVec.ofNat 64 1) := rfl

theorem e8n_eval {n : Nat} (h : (env.regs .r15).toNat = n) :
    e8n.eval env = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, h, BitVec.toNat_ofNat]
  omega

theorem eM8_eval {n : Nat} (h : env.regs .rbp = BitVec.ofNat 64 (8 * n)) (h1 : 1 ≤ n)
    (hn : n ≤ 158) : (eM8.eval env).toNat = 8 * n - 8 := by
  have hr : (env.regs .rbp).toNat = 8 * n := by rw [h, lit_toNat (by omega)]
  show (BinOp.apply .add .W64 (env.regs .rbp) (BitVec.ofNat 64 18446744073709551608)).toNat = _
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [addM8 (by omega), hr]

theorem eN_eval {n : Nat} (h : env.regs .rbp = BitVec.ofNat 64 (8 * n)) (h1 : 1 ≤ n)
    (hn : n ≤ 158) : (eN.eval env).toNat = n := by
  rw [eN_def]
  exact shr_add _ n (eM8_eval h h1 hn) h1 hn

theorem rax4_eval {n : Nat} (h : env.regs .rbp = BitVec.ofNat 64 (8 * n)) (h1 : 1 ≤ n)
    (hn : n ≤ 158) :
    ((Sym.bin .and .W32 (.un .trunc .W32 eN) (.lit 7)).eval env).toNat = n % 8 := by
  have he := eN_eval h h1 hn
  show (BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (eN.eval env)) (BitVec.ofNat 64 7)).toNat = _
  simp only [BinOp.apply, UnOp.apply, toNat_ext, toNat_low, BitVec.toNat_and, Width.bits, he,
    lit_toNat (show 7 < 2 ^ 64 by decide)]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega),
    show 7 % 2 ^ 32 = 7 from rfl]
  exact and7 ⟨n, by omega⟩

theorem rdx7_eval {n : Nat} (h : (env.regs .rdx).toNat = n) (hn : n ≤ 158) :
    ((Sym.bin .and .W64 (.reg .rdx) (.lit 18446744073709551608)).eval env).toNat =
      n / 8 * 8 := by
  show (BinOp.apply .and .W64 (env.regs .rdx) (BitVec.ofNat 64 18446744073709551608)).toNat = _
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_and, h]
  rw [show (BitVec.ofNat 64 18446744073709551608).toNat = 18446744073709551608 from rfl]
  exact andM8 ⟨n, by omega⟩

theorem addLit_eval {r : Reg64} {c k : Nat} (h : (env.regs r).toNat = c) (hc : c + k < 2 ^ 64)
    (hk : k < 2 ^ 64) : ((Sym.bin .add .W64 (.reg r) (.lit k)).eval env).toNat = c + k := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, h]
  omega

theorem litAdd_eval {r : Reg64} {c k : Nat} (h : (env.regs r).toNat = c) (hc : c + k < 2 ^ 64)
    (hk : k < 2 ^ 64) : ((Sym.bin .add .W64 (.lit k) (.reg r)).eval env).toNat = c + k := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, h]
  omega

theorem addReg_eval {c j : Nat} (h1 : (env.regs .rcx).toNat = c) (h2 : (env.regs .rdx).toNat = j)
    (hc : c + j < 2 ^ 64) :
    ((Sym.bin .add .W64 (.reg .rcx) (.reg .rdx)).eval env).toNat = c + j := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, h1, h2]
  omega

end

theorem u64_of {v : BitVec 64} {t : Nat} (h : v.toNat = t) : UInt64.ofBitVec v = t.toUInt64 := by
  have := v.isLt
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofBitVec, toNat_toUInt64 (by omega), h]

/-! ## The order array -/

variable {m0 : MachineData}

theorem ob_add (m0 : MachineData) (x : Nat) :
    ob m0 + BitVec.ofNat 64 x = off (stackBelow m0 1328) (16 + x) := by
  rw [ob_eq, off_add]

/-- **`c` words written** into the order array from word `j`. -/
theorem Ords.write {j c : Nat} {d d' : Mem 64} (hst : StackOk m0 1344) (h : Ords m0 j d)
    (hle : 8 * (j + c) ≤ 1264)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (ob m0 + BitVec.ofNat 64 (8 * j))
      (8 * c)))
    (hw : ∀ i < c, WordAt d' (ob m0 + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (8 * i))
      (j + i).toUInt64) : Ords m0 (j + c) d' :=
  h.step (by unfold NativeRustcVm.NoWrap; rw [ob_toNat hst]; have := hst.2.1; omega) hle
    (fun p hp ↦ hs p hp) fun t h1 h2 ↦ by
      have := hw (t - j) (by omega)
      rwa [NativeRustcVm.addr_add, show 8 * j + 8 * (t - j) = 8 * t by omega,
        show j + (t - j) = t by omega] at this

theorem Init.of {j : Nat} {d d' : MachineData} (h : Init m0 j d) (hb : B m0 8 d')
    (he : ∀ r ∈ [Reg64.rbp, .rbx, .r12, .r14, .r15], reg d' r = reg d r)
    (hd : d'.dmem = d.dmem) : Init m0 j d' where
  b := hb
  regs := h.regs.of fun r hr ↦ he r (List.mem_cons_of_mem _ hr)
  rbp := (he .rbp (by simp)).trans h.rbp
  ords := hd ▸ h.ords
  le := h.le

/-- An environment of one region, mapped and not wrapping. -/
theorem wf_one {d : MachineData} {a : BitVec 64} {l : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hm : NativeRustcVm.Mapped d.dmem a l) (hn : NativeRustcVm.NoWrap a l) :
    (Env.ofMachine d [(a, l)] vars ret).WF :=
  Env.wf_of ⟨⟨hm, hn⟩, trivial⟩ (List.pairwise_singleton _ _)

/-- The order array's bytes from word `j`, mapped and not wrapping, in a body. -/
theorem ord_ok {d : MachineData} {oo : Nat} (hst : StackOk m0 1344) (hb : B m0 oo d) {o l : Nat}
    (hl : 16 + o + l ≤ 1328) :
    NativeRustcVm.Mapped d.dmem (off (stackBelow m0 1328) (16 + o)) l ∧
      NativeRustcVm.NoWrap (off (stackBelow m0 1328) (16 + o)) l := by
  have hnw := fb_noWrap hst
  unfold NativeRustcVm.NoWrap at hnw
  refine ⟨Mapped.keeps (mapped_off (frame_mapped hst (by decide)) (by omega)) hb.fr.kept, ?_⟩
  unfold NativeRustcVm.NoWrap
  rw [toNat_off (by omega)]
  omega

variable [Host] {k : Nat}

/-! ## The entry -/

/-- **The entry** (`b0`, `b1` or `b2` and `memset`): `None` when `offsets` is shorter than
`sizes`, else the body at `b3`, R13 the order array. -/
theorem entry (hp : Placed code k) (hms : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hpre : StackOffsetsPre m0) :
    Eventually (step1 Host.exe) (fun s ↦ Post m0 s ∨ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b3Offset) ∧
      n m0 ≤ cap m0 ∧ B m0 8 s.data ∧ Regs m0 s.data ∧ reg s.data .r13 = ob m0))
      ⟨m0, label NativeRustcVmX64.Vm.StackOffsets.entryLabel⟩ := by
  have hst : StackOk m0 1344 := hpre.1
  have hfnw := fb_noWrap hst
  unfold NativeRustcVm.NoWrap at hfnw
  have hfb := fb_toNat hst
  have hob := ob_toNat hst
  have hs1 := hst.1
  have hs2 := hst.2.1
  rw [show Labels.label NativeRustcVmX64.Vm.StackOffsets.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b0Offset) from hp.label NativeRustcVmX64.Vm.StackOffsets.entry_at]
  have hg := hpre.2.2.2.2.2.2.2
  have hslot := hg.1 "memset" (by simp)
  have hap := apart_frame hslot.2.2.1 hst.1 (show 1328 ≤ stackOffsetsStack by decide)
  have hwf0 : (frameEnv m0 m0 1328 [(gotAddr "memset", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b3Offset)).toBitVec).WF :=
    frame_wf ⟨frame_mapped hst (by decide), frame_noWrap hst (by decide)⟩
      (by intro x hx; simp only [List.mem_singleton] at hx; subst x
          exact ⟨hg.mapped (by simp), hslot.2.1⟩)
      (List.pairwise_pair.mpr hap.symm)
  have hm0 : Match (frameEnv m0 m0 1328 [(gotAddr "memset", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b3Offset)).toBitVec) entryS m0 := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial
        ⟨by simp [Sym.eval, Env.base, gotAddr], trivial⟩
    · intro i hi
      simpa [Sym.eval, Env.base, frameEnv] using hg.byte (by simp : "memset" ∈ ["memset"]) hi
  refine exec_then (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  obtain ⟨hy, hno⟩ := pc_of (P := ¬ cap m0 < n m0) hpc1 (by
    rw [SBool.eval, ult_eval, decide_not]; rfl)
  by_cases hc : n m0 ≤ cap m0
  · -- `b2`: the prologue, `memset`
    refine exec_at (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b2 hwf0 (fun _ _ ↦ rfl)
      ((hy (by omega)).trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_3_at)) hm1 fun st2 hm2 hpc2 ↦ ?_
    obtain ⟨hpro, hx7, hx6, hx2, hx3, hx12, hx13, hx14, hx15, -⟩ := ok_b2
    have hb2 : B m0 0 st2.data :=
      Bd.entry_frame hst (by decide) hwf0 hm2 hpro slots_le slots_cs (by decide +kernel)
    have hrdi : reg st2.data .rdi = ob m0 := (hm2.regs .rdi _ hx7).trans (eval_ptr0 16)
    have hrdx : (reg st2.data .rdx).toNat = 1264 := by
      show (st2.data.regs.get64 .rdx).toNat = _
      rw [hm2.regs .rdx _ hx2]; rfl
    have hrsp2 : rspOf st2.data = stackBelow m0 1328 := hb2.rsp0
    have hpre2 : MemsetPre st2.data := by
      unfold MemsetPre
      rw [hrdi, hrdx]
      have hok := ord_ok (o := 0) (l := 1264) hst hb2 (by decide)
      rw [show 16 + 0 = 16 from rfl, ← ob_eq] at hok
      refine ⟨hb2.stackOk hst (by decide), hok.1, hok.2, ?_⟩
      · show (ob m0).toNat + 1264 ≤ (rspOf st2.data).toNat ∨
          (rspOf st2.data).toNat + 8 ≤ (ob m0).toNat
        rw [hrsp2, hfb, hob]; omega
    refine call_then hpc2 hms hpre2 fun st3 hpc3 hrsp3 hpost ↦ ?_
    obtain ⟨-, -, hso3, hsv3⟩ := hpost
    rw [hrdi, hrdx] at hso3
    have hR : ∀ j, 1280 ≤ j → j < 1336 →
        ¬ NativeRustcVm.InRange (ob m0) 1264 (off (stackBelow m0 1328) j) := fun j h1 h2 h ↦ by
      rw [ob_eq, inRange_off_iff (by omega) (by omega)] at h
      omega
    have hb3 : B m0 8 st3.data := hb2.call hsv3 hrsp3 hso3
      (fun q h ↦ Or.inr (off_in_stack hst (o := 16) (l := 1264) (by decide) h))
      (fun p hp i hi ↦ hR _ (by have := slots_ge p hp; omega) (by have := slots_le p hp; omega))
      (fun j hj ↦ hR _ (by omega) (by omega))
    refine .done _ (Or.inr ⟨by rw [hpc3]; rfl, hc, hb3, ?_, ?_⟩)
    · exact Regs.saved ⟨hm2.regs .rbx _ hx3, hm2.regs .r12 _ hx12, hm2.regs .r14 _ hx14,
        hm2.regs .r15 _ hx15⟩ hsv3
    · exact (hsv3.1 .r13 rfl).trans ((hm2.regs .r13 _ hx13).trans (eval_ptr0 16))
  · -- `b1`: `None`
    refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b1 hwf0 nofun (hno (by omega)) hm1
      fun st2 hm2 hpc2 ↦ ?_
    obtain ⟨hepi, hmem, hrax⟩ := ok_b1
    obtain ⟨hsv, hrsp⟩ := Frame.epilogue Frame.entry hwf0 hm2 hepi
    have hd : st2.data.dmem = m0.dmem := hm2.dmem_eq hwf0 hmem
    simp only [PcOk] at hpc2
    refine .done _ (Or.inl ⟨by rw [hpc2]; exact Frame.entry.load_ret hst (by decide), hrsp, ?_,
      fun p _ ↦ by rw [hd], hsv⟩)
    split
    · rename_i h; exact absurd h.1 hc
    · exact hm2.regs .rax _ hrax

end

end NativeRustcVmX64.Layout.StackOffsets
