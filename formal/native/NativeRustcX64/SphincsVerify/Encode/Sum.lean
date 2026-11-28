module

public import NativeRustcX64.Code.Sphincs.SphincsVerify.Names

public import NativeRustcX64.SphincsVerify.Encode.Loop
public import NativeRustcX64.SphincsVerify.Epilogue
meta import NativeRustcX64.Code.Sphincs.SphincsVerify.Part2
meta import NativeRustcX64.Code.Sphincs.SphincsVerify.Part3
meta import NativeRustcX64.SphincsVerify.Frame

/-!
# The digits' sum and the codeword's copy: `b114`, `b115`

`b114` loads the 64 digits, spills them, adds them up and jumps to `b195`
(`return 0`) when the sum is not 128; `b115` stores the digits at `3080` (the
codeword `x` the chains read), RAX `0`, R12 hasher A, R13 `base + 8328`, and jumps to `b117`. The
sum the executor builds is a tree of additions of the digits' loads: `sumOf` reads its loads off
it, `sumOf_eval` evaluates it; the kernel checks both blocks' results once (`sumOk`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym

@[expose] public section

set_option Elab.async false

/-- The offsets of a sum of one-byte loads of the frame (`movzbl`). -/
def sumOf : Sym → Option (List Nat)
  | .bin .add .W64 a b => (sumOf a).bind fun x ↦ (sumOf b).map fun y ↦ x ++ y
  | .un (.zext .W8) .W32 (.load 0 o 1) => some [o]
  | .load 0 o 1 => some [o]
  | _ => none

theorem zext8_toNat (x : BitVec 64) : (UnOp.apply (.zext .W8) .W32 x).toNat = x.toNat % 256 := by
  simp only [UnOp.apply, toNat_ext, BitVec.toNat_setWidth, toNat_low, Width.bits]
  omega

/-- **A sum's value**: the sum of its loads, modulo `2⁶⁴`. -/
theorem sumOf_eval [Labels] (env : Env) (e : Sym) :
    ∀ os, sumOf e = some os →
      (e.eval env).toNat = (os.map fun o ↦ (env.load 0 o 1).toNat).sum % 2 ^ 64 := by
  fun_induction sumOf e with
  | case1 a b iha ihb =>
    intro os h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, iha x hx, ihb y hy,
      List.map_append, List.sum_append]
    omega
  | case2 o =>
    intro os h
    simp only [Option.some.injEq] at h
    subst h
    simp only [Sym.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [zext8_toNat]
    have := Sym.natOfBytes_lt ((List.range 1).map fun i ↦
      (env.mem0.get? (env.base 0 + BitVec.ofNat 64 (o + i))).getD 0)
    simp only [Env.load, Sym.ofBytes_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
      List.length_map, List.length_range] at this ⊢
    omega
  | case3 o =>
    intro os h
    simp only [Option.some.injEq] at h
    subst h
    simp only [Sym.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
  | case4 => intro os h; cases h

/-- `b114`'s start. -/
def s114 : SState := Run.frameState []

/-- The codeword's byte `j`, as `b115` stores it. -/
def cwS (j : Nat) : Sym := .un .trunc .W8 (.un (.zext .W8) .W32 (.load 0 (560 + j) 1))

/-- The layer's spills and inputs a block keeps. -/
def spillsKept (S : SState) : Bool :=
  Run.noWriteIn S 68 4 && Run.noWriteIn S 88 8 && Run.noWriteIn S 96 8 &&
    Run.noWriteIn S 104 4 && Run.noWriteIn S 112 32 && Run.noWriteIn S 168 8 &&
    Run.noWriteIn S 184 8 && Run.noWriteIn S 192 8 && Run.noWriteIn S 200 8 &&
    Run.noWriteIn S 208 8 && Run.noWriteIn S 552 8 && Run.noWriteIn S 20556 7740

/-- `b115`'s result. -/
def b115Ok (S : SState) : Bool :=
  match exec Sphincs.SphincsVerify.b115 S with
  | some (S', x) =>
    x == .jump NativeRustcX64.Sphincs.SphincsVerify.label_42 && S'.reg .rax == some (.lit 0) &&
      S'.reg .r12 == some (.ptr 0 4104) && S'.reg .r13 == some (.ptr 0 8328) &&
      S'.reg .rsp == some (.ptr 0 0) && Run.frameWrites S' &&
      spillsKept S' && S'.reg .rbx == some (.label "memset") &&
      S'.reg .r14 == some (.reg .r14) &&
      (List.range 64).all fun j ↦ findWrite 0 (3080 + j) S'.mem == some (cwS j, 0)
  | none => false

/-- `b114`'s and `b115`'s results. -/
def sumOk : Bool :=
  match exec Sphincs.SphincsVerify.b114 s114 with
  | some (S, .cond (.not (.cmp .eq .W64 e (.lit 128))) l) =>
    l == NativeRustcX64.Sphincs.SphincsVerify.label_84 && ((sumOf e).map isort) == some (List.range' 560 64) &&
      S.reg .rsp == some (.ptr 0 0) && Run.frameWrites S && b115Ok S
  | _ => false

theorem sumOk_eq : sumOk = true := by decide +kernel

/-! ## The digits' sum -/

namespace Run

variable (r : Run) [Labels]

/-- A one-byte load of the frame. -/
theorem load1 {m : MachineData} (vars : Nat → BitVec 64) (ret : BitVec 64) {o : Nat} {b : UInt8}
    (h : m.dmem.get? (r.off o) = some b) : ((r.env m vars ret).load 0 o 1).toNat = b.toNat := by
  rw [Sym.Env.load_of_bytesAt (r := 0) (off := o) (n := 1) (bs := [b]) rfl (fun i hi ↦ by
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    exact h)]
  show (BitVec.ofInt 64 ((0 : Int) * 256 + (b.toNat : Int))).toNat = b.toNat
  rw [Int.zero_mul, Int.zero_add, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  have := b.toNat_lt
  omega

/-- **The sum's value**: the digits' sum. -/
theorem sum_value {m : MachineData} (vars : Nat → BitVec 64) (ret : BitVec 64) {V : Nat}
    (hd : ∀ t < 64, m.dmem.get? (r.off (560 + t)) = some (digitByte V t)) {e : Sym}
    {os : List Nat} (he : sumOf e = some os) (hs : isort os = List.range' 560 64) :
    (e.eval (r.env m vars ret)).toNat = ((digits V).map UInt8.toNat).sum := by
  rw [sumOf_eval _ e os he]
  have hp : (os.map fun o ↦ ((r.env m vars ret).load 0 o 1).toNat).Perm
      ((List.range' 560 64).map fun o ↦ ((r.env m vars ret).load 0 o 1).toNat) := by
    rw [← hs]
    exact ((perm_isort os).map _).symm
  rw [hp.sum_eq, List.range'_eq_map_range, List.map_map, digits_eq, List.map_map]
  have hsum : ((List.range 64).map ((fun o ↦ ((r.env m vars ret).load 0 o 1).toNat) ∘
      (560 + ·))).sum = ((List.range 64).map (UInt8.toNat ∘ digitByte V)).sum := by
    congr 1
    apply List.map_congr_left
    intro t ht
    exact r.load1 vars ret (hd t (List.mem_range.mp ht))
  rw [hsum]
  have := sum_digits_le V
  rw [digits_eq, List.map_map] at this
  omega

end Run


theorem byteOf_cw (x : BitVec 64) :
    byteOf (UnOp.apply .trunc .W8 (UnOp.apply (.zext .W8) .W32 x)) 0 = byteOf x 0 := by
  unfold byteOf
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat', Nat.mul_zero, Nat.pow_zero, Nat.div_one, UnOp.apply, toNat_ext,
    toNat_low, Width.bits, BitVec.toNat_setWidth]
  omega

variable [Host]

theorem label_84 {k : Nat} (hp : Placed Sphincs.SphincsVerify.code k) :
    Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_84 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b195Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_84_at

theorem label_42 {k : Nat} (hp : Placed Sphincs.SphincsVerify.code k) :
    Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_42 = Host.addrOf (k + NativeRustcX64.Sphincs.SphincsVerify.b117Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_42_at

/-- **The sum and the codeword's copy**: from `b114` with the 64 digits of `V` at `560`, the
machine returns 0 if they do not sum to 128, else reaches the chains (`b117`) with the codeword
at `3080`. -/
theorem sum_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {l : Nat} {V : Nat} {m : MachineData} (hl : l < 3) (hF : r.Frame m) (hI : r.Inputs m)
    (hL : r.LayerSpills l m)
    (h14 : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec)
    (hd : ∀ t < 64, m.dmem.get? (r.off (560 + t)) = some (digitByte V t)) :
    Eventually (step1 Host.exe) (fun st ↦
      (((digits V).map UInt8.toNat).sum ≠ 128 ∧ r.Done false st) ∨
      (((digits V).map UInt8.toNat).sum = 128 ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b117Offset ∧
        r.AtChains l (digits V) st.data)) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b114Offset⟩ := by
  have hok := sumOk_eq
  unfold sumOk at hok
  have hwf := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) 0
  have hm := r.match_frame hpre hF (vars := fun _ ↦ 0) (ret := 0) (known := []) (labels := [])
    (bounds := []) (aliases := []) trivial trivial trivial trivial
  have hk := Sphincs.SphincsVerify.b114_in_code.trans hp.1 (List.cons_ne_nil _ _)
  rcases hx : exec Sphincs.SphincsVerify.b114 s114 with _ | ⟨S, x⟩
  · rw [hx] at hok
    exact absurd hok Bool.false_ne_true
  rw [hx] at hok
  split at hok
  · rename_i S' e l' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
    obtain ⟨rfl, hsum, hsp, hfw, h115⟩ := hok
    obtain ⟨os, he, hs⟩ := Option.map_eq_some_iff.mp hsum
    refine Sym.exec_then hk hx hwf (fun _ h ↦ by cases h) hm fun st hm1 hpc1 ↦ ?_
    have hval := r.sum_value (fun _ ↦ 0) 0 hd he hs
    have hF1 := Run.Frame.of_match r hpre hF hm1 hwf hsp hfw
    simp only [Sym.PcOk, SBool.eval, CmpOp.apply, low_W64, Sym.eval] at hpc1
    by_cases h128 : ((digits V).map UInt8.toNat).sum = 128
    · have hc : (Sym.eval (r.env m (fun _ ↦ 0) 0) e == BitVec.ofNat 64 128) = true := by
        rw [beq_iff_eq]
        apply BitVec.eq_of_toNat_eq
        rw [hval, h128]
        rfl
      rw [hc] at hpc1
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc, NativeRustcX64.Sphincs.SphincsVerify.b114_next] at hpc1
      -- b115
      unfold b115Ok at h115
      have hk2 := Sphincs.SphincsVerify.b115_in_code.trans hp.1 (List.cons_ne_nil _ _)
      rcases hx2 : exec Sphincs.SphincsVerify.b115 S with _ | ⟨S2, x2⟩
      · rw [hx2] at h115
        exact absurd h115 Bool.false_ne_true
      rw [hx2] at h115
      simp only [spillsKept, Bool.and_eq_true, beq_iff_eq, and_assoc] at h115
      obtain ⟨rfl, hX0, hX12, hX13, hsp2, hfw2, k60, k88, k96, k104, k112, k160, k176, k200,
        k208, k216, k568, ksig, hXbx, hX14, hw⟩ := h115
      refine Sym.exec_at hk2 hx2 hwf (fun _ h ↦ by cases h) hpc1 hm1 fun st2 hm2 hpc2 ↦
        .done _ (.inr ⟨h128, ?_, ?_⟩)
      · simp only [Sym.PcOk] at hpc2
        rw [hpc2, label_42 hp]
        rfl
      have kept := fun {o : Nat} {bs : List UInt8} ho hb hn ↦
        r.bytesAt_kept (m := m) (m' := st2.data) hpre hm2 hwf (o := o) (bs := bs) ho hb hn
      obtain ⟨s96, s200, s208, s160, s216, s104, s88, s60, s568, s176⟩ := hL
      refine ⟨hl, length_digits V, Run.Frame.of_match r hpre hF hm2 hwf hsp2 hfw2,
        ⟨kept (by rw [r.length_pkBytes]; omega) hI.1 (by rw [r.length_pkBytes]; exact k112),
          kept (by rw [r.length_sigMem]; omega) hI.2 (by rw [r.length_sigMem]; exact ksig)⟩,
        ⟨kept (by rw [length_wordBytes]; omega) s96 (by rw [length_wordBytes]; exact k96),
          kept (by rw [length_wordBytes]; omega) s200 (by rw [length_wordBytes]; exact k200),
          kept (by rw [length_wordBytes]; omega) s208 (by rw [length_wordBytes]; exact k208),
          kept (by rw [length_wordBytes]; omega) s160 (by rw [length_wordBytes]; exact k160),
          kept (by rw [length_wordBytes]; omega) s216 (by rw [length_wordBytes]; exact k216),
          kept (by rw [Run.length_be32]; omega) s104 (by rw [Run.length_be32]; exact k104),
          kept (by rw [Run.length_be64]; omega) s88 (by rw [Run.length_be64]; exact k88),
          kept (by rw [Run.length_be32]; omega) s60 (by rw [Run.length_be32]; exact k60),
          kept (by rw [length_wordBytes]; omega) s568 (by rw [length_wordBytes]; exact k568),
          kept (by rw [length_wordBytes]; omega) s176 (by rw [length_wordBytes]; exact k176)⟩,
        hm2.regs .rax _ hX0, (hm2.regs .r12 _ hX12).trans (r.ptr_eval _ _ _ 4104),
        (hm2.regs .r13 _ hX13).trans (r.ptr_eval _ _ _ 8328),
        ?_, hm2.regs .rbx _ hXbx, (hm2.regs .r14 _ hX14).trans h14⟩
      intro i hi
      rw [length_digits] at hi
      rw [Run.off_add, show r.off (3080 + i) = r.base + BitVec.ofNat 64 (3080 + i) from rfl,
        hm2.mem 0 r.base frameRegion rfl (3080 + i) (by rw [Run.frameRegion_eq]; omega)]
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hw
      simp only [Sym.memByte, hw i hi, cwS, Sym.eval]
      rw [byteOf_cw, Sym.byteOf_load (by decide) (by decide), Nat.add_zero]
      have := hd i hi
      rw [show r.off (560 + i) = (r.env m (fun _ ↦ 0) 0).base 0 + BitVec.ofNat 64 (560 + i)
        from rfl] at this
      simp only [Env.ofMachine_mem0, this, Option.getD_some, getElem_digits V hi]
    · have hc : (Sym.eval (r.env m (fun _ ↦ 0) 0) e == BitVec.ofNat 64 128) = false := by
        rw [beq_eq_false_iff_ne]
        intro h
        apply h128
        rw [← hval, h]
        rfl
      rw [hc] at hpc1
      simp only [Bool.not_false, ↓reduceIte] at hpc1
      exact Eventually.mono (goto (hpc1.trans (label_84 hp)) (fail_return r hp hpre st.data hF1))
        fun st' h' ↦ .inl ⟨h128, h'⟩
  · exact absurd hok Bool.false_ne_true

end

end NativeRustcX64.SphincsVerifyProof
