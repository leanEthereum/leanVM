module

public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.Encode.Loop
public import NativeRustcArm.SphincsVerify.Encode.State
public import NativeRustcArm.SphincsVerify.Encode.Hash
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify.Part3
public meta import NativeRustcArm.Sym.Exec

/-!
# The digits' sum and the codeword's copy: `b111`, `b112`

`b111` (directive 1441) loads the 64 digits, spills them, adds them up and branches to `b187`
(`return 0`) when the sum is not 128; `b112` (directive 1596) stores the digits at `23696` (the
codeword `x` the chains read), X0 `0`, X8 the layer's chain values, and jumps to `b114`. The sum
the executor builds is a tree of additions of the digits' loads: `sumOf` reads its loads off it,
`sumOf_eval` evaluates it; the kernel checks both blocks' results once (`sumOk`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

@[expose] public section

set_option Elab.async false

/-- The offsets of a sum of one-byte loads of the frame. -/
def sumOf : Sym → Option (List Nat)
  | .bin .add .W64 a b => (sumOf a).bind fun x ↦ (sumOf b).map fun y ↦ x ++ y
  | .load 0 o 1 => some [o]
  | _ => none

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
    exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
  | case3 => intro os h; cases h

/-- `b111`'s start: X29 the saved registers. -/
def s111 : SState := init [(29376, true)] (.ptr 0 0) [(.X29, .ptr 0 29280)]

/-- `b112`'s result. -/
def b112Ok (S : SState) : Bool :=
  match exec Sphincs.SphincsVerify.b112 S with
  | some (S', x) =>
    x == .jump NativeRustcArm.Sphincs.SphincsVerify.label_45 && S'.reg .X0 == some (.lit 0) &&
      S'.reg .X8 == some (.load 0 392 8) && S'.reg .X21 == some (.reg .X21) &&
      S'.reg .X25 == some (.reg .X25) && S'.reg .X26 == some (.reg .X26) && S'.sp == .ptr 0 0 &&
      S'.reg .X29 == some (.ptr 0 29280) && Run.frameWrites S' && Run.noWriteIn S' 0 48 &&
      Run.noWriteIn S' 376 24 && Run.noWriteIn S' 408 24 && Run.noWriteIn S' 8208 7776 &&
      (List.range 64).all fun j ↦ findWrite 0 (23696 + j) S'.mem == some (.load 0 (26768 + j) 1, 0)
  | none => false

/-- `b111`'s and `b112`'s results. -/
def sumOk : Bool :=
  match exec Sphincs.SphincsVerify.b111 s111 with
  | some (S, .cond (.not (.cmp .eq .W64 e (.lit 128))) l) =>
    l == NativeRustcArm.Sphincs.SphincsVerify.label_91 && ((sumOf e).map isort) == some (List.range' 26768 64) &&
      S.sp == .ptr 0 0 && S.reg .X29 == some (.ptr 0 29280) && Run.frameWrites S && b112Ok S
  | _ => false

theorem sumOk_eq : sumOk = true := by decide +kernel

/-! ## The digits' sum -/

namespace Run

variable (r : Run) [Labels]

omit [Labels] in
/-- A one-byte load of the frame. -/
theorem load1 {m : MachineData} (vars : Nat → BitVec 64) {o : Nat} {b : UInt8}
    (h : m.dmem.get? (r.off o) = some b) : ((r.env m vars).load 0 o 1).toNat = b.toNat := by
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
theorem sum_value {m : MachineData} (vars : Nat → BitVec 64) {V : Nat}
    (hd : ∀ t < 64, m.dmem.get? (r.off (26768 + t)) = some (digitByte V t)) {e : Sym}
    {os : List Nat} (he : sumOf e = some os) (hs : isort os = List.range' 26768 64) :
    (e.eval (r.env m vars)).toNat = ((digits V).map UInt8.toNat).sum := by
  rw [sumOf_eval _ e os he]
  have hp : (os.map fun o ↦ ((r.env m vars).load 0 o 1).toNat).Perm
      ((List.range' 26768 64).map fun o ↦ ((r.env m vars).load 0 o 1).toNat) := by
    rw [← hs]
    exact ((perm_isort os).map _).symm
  rw [hp.sum_eq, List.range'_eq_map_range, List.map_map, digits_eq, List.map_map]
  have hsum : ((List.range 64).map ((fun o ↦ ((r.env m vars).load 0 o 1).toNat) ∘
      (26768 + ·))).sum = ((List.range 64).map (UInt8.toNat ∘ digitByte V)).sum := by
    congr 1
    apply List.map_congr_left
    intro t ht
    exact r.load1 vars (hd t (List.mem_range.mp ht))
  rw [hsum]
  have := sum_digits_le V
  rw [digits_eq, List.map_map] at this
  omega

end Run


variable [NativeRustcArm.Host]

theorem label_91 {k : Nat} (hp : Placed Sphincs.SphincsVerify.code k) :
    Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_91 = NativeRustcArm.Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b187Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_91_at

theorem label_45 {k : Nat} (hp : Placed Sphincs.SphincsVerify.code k) :
    Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_45 = NativeRustcArm.Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b114Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_45_at

/-- **The sum and the codeword's copy**: from `b111` with the 64 digits of `V` at `26768`, the
machine returns 0 if they do not sum to 128, else reaches the chains (`b114`) with the codeword
at `23696`. -/
theorem sum_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {l : Nat} {V : Nat} {m : MachineData} (hl : l < 3) (hF : r.Frame m) (hI : r.Inputs m)
    (hL : r.LayerSpills l m) (h21 : Run.RegIs m .X21 (r.off 26968))
    (h25 : Run.RegIs m .X25 (r.off 16600)) (h26 : Run.RegIs m .X26 136)
    (hd : ∀ t < 64, m.dmem.get? (r.off (26768 + t)) = some (digitByte V t)) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦
      (((digits V).map UInt8.toNat).sum ≠ 128 ∧ r.Done false st) ∨
      (((digits V).map UInt8.toNat).sum = 128 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b114Offset ∧
        r.AtChains l (digits V) st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b111Offset⟩ := by
  have hok := sumOk_eq
  unfold sumOk at hok
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  have hm := r.match_frame hpre hF (vars := fun _ ↦ 0) (known := [(.X29, .ptr 0 29280)])
    (labels := []) (bounds := []) (aliases := [])
    ⟨hF.2.1.trans (r.ptr_eval0 m _ 29280).symm, trivial⟩ trivial trivial trivial
  have hk := Sphincs.SphincsVerify.b111_in_code.trans hp.1 (List.cons_ne_nil _ _)
  rcases hx : exec Sphincs.SphincsVerify.b111 s111 with _ | ⟨S, x⟩
  · rw [hx] at hok
    exact absurd hok Bool.false_ne_true
  rw [hx] at hok
  split at hok
  · rename_i S' e l' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
    obtain ⟨rfl, hsum, hsp, h29, hfw, h112⟩ := hok
    obtain ⟨os, he, hs⟩ := Option.map_eq_some_iff.mp hsum
    refine Sym.exec_then hk hx hwf hm fun st hm1 hpc1 ↦ ?_
    have hval := r.sum_value (fun _ ↦ 0) hd he hs
    have hF1 := Run.Frame.of_match r hpre hF hm1 hwf hsp h29 hfw
    simp only [Sym.PcOk, SBool.eval, CmpOp.apply, low_W64, Sym.eval] at hpc1
    by_cases h128 : ((digits V).map UInt8.toNat).sum = 128
    · have hc : (Sym.eval (r.env m) e == BitVec.ofNat 64 128) = true := by
        rw [beq_iff_eq]
        apply BitVec.eq_of_toNat_eq
        rw [hval, h128]
        rfl
      rw [hc] at hpc1
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc, NativeRustcArm.Sphincs.SphincsVerify.b111_next] at hpc1
      -- b112
      unfold b112Ok at h112
      have hk2 := Sphincs.SphincsVerify.b112_in_code.trans hp.1 (List.cons_ne_nil _ _)
      rcases hx2 : exec Sphincs.SphincsVerify.b112 S with _ | ⟨S2, x2⟩
      · rw [hx2] at h112
        exact absurd h112 Bool.false_ne_true
      rw [hx2] at h112
      simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h112
      obtain ⟨rfl, hX0, hX8, hX21, hX25, hX26, hsp2, h292, hfw2, k0, k376, k408, k8208, hw⟩ := h112
      refine Sym.exec_at hk2 hx2 hwf hpc1 hm1 fun st2 hm2 hpc2 ↦ .done _ (.inr ⟨h128, ?_, ?_⟩)
      · simp only [Sym.PcOk] at hpc2
        rw [hpc2, label_45 hp]
        rfl
      have kept := fun {o : Nat} {bs : List UInt8} ho hb hn ↦
        r.bytesAt_kept (m := m) (m' := st2.data) hpre hm2 hwf (o := o) (bs := bs) ho hb hn
      obtain ⟨s0, s8, s16, s24, s32, s40, s384, s392, s408, s416, s424⟩ := hL
      refine ⟨hl, length_digits V, Run.Frame.of_match r hpre hF hm2 hwf hsp2 h292 hfw2,
        ⟨kept (by rw [r.length_pkBytes]; omega) hI.1
          (noWriteIn_mono k8208 (by omega) (by rw [r.length_pkBytes]; omega)),
        kept (by rw [r.length_sigMem']; omega) hI.2.1
          (noWriteIn_mono k8208 (by omega) (by rw [r.length_sigMem'])),
        kept (by rw [length_wordBytes]; omega) hI.2.2
          (noWriteIn_mono k376 (by omega) (by rw [length_wordBytes]; omega))⟩,
        ⟨kept (by rw [length_wordBytes]; omega) s0
            (noWriteIn_mono k0 (by omega) (by rw [length_wordBytes]; omega)),
          kept (by rw [length_wordBytes]; omega) s8
            (noWriteIn_mono k0 (by omega) (by rw [length_wordBytes]; omega)),
          kept (by rw [length_wordBytes]; omega) s16
            (noWriteIn_mono k0 (by omega) (by rw [length_wordBytes]; omega)),
          kept (by rw [length_wordBytes]; omega) s24
            (noWriteIn_mono k0 (by omega) (by rw [length_wordBytes]; omega)),
          kept (by rw [length_wordBytes]; omega) s32
            (noWriteIn_mono k0 (by omega) (by rw [length_wordBytes]; omega)),
          kept (by rw [length_wordBytes]; omega) s40
            (noWriteIn_mono k0 (by omega) (by rw [length_wordBytes])),
          kept (by rw [length_wordBytes]; omega) s384
            (noWriteIn_mono k376 (by omega) (by rw [length_wordBytes]; omega)),
          kept (by rw [length_wordBytes]; omega) s392
            (noWriteIn_mono k376 (by omega) (by rw [length_wordBytes])),
          kept (by rw [Run.length_be32]; omega) s408
            (noWriteIn_mono k408 (by omega) (by rw [Run.length_be32]; omega)),
          kept (by rw [Run.length_be32]; omega) s416
            (noWriteIn_mono k408 (by omega) (by rw [Run.length_be32]; omega)),
          kept (by rw [Run.length_be64]; omega) s424
            (noWriteIn_mono k408 (by omega) (by rw [Run.length_be64]))⟩,
        hm2.regs .X0 _ hX0, ?_, (hm2.regs .X21 _ hX21).trans h21,
        (hm2.regs .X25 _ hX25).trans h25, (hm2.regs .X26 _ hX26).trans h26, ?_⟩
      · rw [Run.RegIs, hm2.regs .X8 _ hX8]
        exact r.load_word rfl rfl s392
      · intro i hi
        rw [length_digits] at hi
        rw [r.off_add, show r.off (23696 + i) = r.base + BitVec.ofNat 64 (23696 + i) from rfl,
          hm2.mem 0 r.base 29376 rfl (23696 + i) (by omega)]
        simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hw
        simp only [Sym.memByte, hw i hi, Sym.eval]
        rw [Sym.byteOf_load (by decide) (by decide), Nat.add_zero]
        have := hd i hi
        rw [show r.off (26768 + i) = (r.env m fun _ ↦ 0).base 0 + BitVec.ofNat 64 (26768 + i)
          from rfl] at this
        simp only [Env.ofMachine_mem0, this, Option.getD_some, getElem_digits V hi, digitByte]
    · have hc : (Sym.eval (r.env m) e == BitVec.ofNat 64 128) = false := by
        rw [beq_eq_false_iff_ne]
        intro h
        apply h128
        rw [← hval, h]
        rfl
      rw [hc] at hpc1
      simp only [Bool.not_false, ↓reduceIte] at hpc1
      refine Eventually.mono (goto (hpc1.trans (label_91 hp)) (fail_return r hp hpre st.data hF1))
        fun st' h' ↦ .inl ⟨h128, h'⟩
  · exact absurd hok Bool.false_ne_true

end

end NativeRustcArm.SphincsVerifyProof
