module

public import NativeVm.Code.Phase6.LayerC

/-!
# Lookups by lane and position

For `m = 64 lane + z` in `r15`: `lk T o inc d0 d1` loads the element `o + T[lane] + z'` into `d0`,
`d1`, `T[lane]` the word of the table element `T + lane` and `z' = (z + [inc]) mod 64`
(`lk_spec`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec eOf_zero)

variable {s : QState} {g : Nat → EW} {p : UInt64}

theorem shr6 {m : Nat} (hm : m < 2 ^ 64) :
    (m.toUInt64 >>> (6 : Nat).toUInt64) <<< (4 : Nat).toUInt64 = (8 * (2 * (m / 64))).toUInt64 := by
  rw [← rax16]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, toNat_toUInt64' hm, toNat_toUInt64' (by omega)]
  simp [Nat.shiftRight_eq_div_pow]
  omega

theorem and63 {m : Nat} (hm : m < 2 ^ 64) : m.toUInt64 &&& (63 : Int64).toUInt64 = (m % 64).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, toNat_toUInt64' hm, toNat_toUInt64' (by omega)]
  show m &&& 63 = m % 64
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The position, `r15 + [inc]` modulo `64`, into `rdx`. -/
def zpos (inc : Bool) : List Stmt :=
  [I (.mov .rdx .r15)] ++ (if inc then [I (.addi .rdx 1)] else []) ++ [I (.andi .rdx 63)]

/-- The element `o + T[lane] + z'` into `d0`, `d1`. -/
def lk (T o : Nat) (inc : Bool) (d0 d1 : Reg64) : List Stmt :=
  [I (.mov .rax .r15), I (.shri .rax 6), I (.shli .rax 4), I (.load .rcx (ix (2 * T)))] ++ zpos inc ++
  [I (.add .rcx .rdx), I (.shli .rcx 4), I (.mov .rax .rcx), I (.load d0 (ix (2 * o))),
    I (.load d1 (ix (2 * o + 1)))]

theorem zpos_spec {inc : Bool} {m : Nat} (hm : m < 2 ^ 20) (h15 : s.reg .r15 = m.toUInt64)
    {xs : List Stmt} {P E : QState → Prop}
    (k : ∀ s', s'.mem = s.mem → RegsFrame [.rdx] s s' →
      s'.reg .rdx = ((m + if inc then 1 else 0) % 64).toUInt64 → WP (blk xs) s' P E) :
    WP (blk (zpos inc ++ xs)) s P E := by
  unfold zpos
  cases inc
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
    refine k _ rfl (by rf_tac) ?_
    simp only [QState.setReg_reg, ↓reduceIte, h15, Bool.false_eq_true, Nat.add_zero]
    exact and63 (by omega)
  · simp only [List.cons_append, List.nil_append, ite_true]
    refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
      (NativeVm.Transcript.wp_reg (by rfl) ?_))
    refine k _ rfl (by rf_tac) ?_
    simp only [QState.setReg_reg, ↓reduceIte, h15]
    rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl, NativeVm.Transcript.toUInt64_add]
    exact and63 (by omega)

theorem lk_spec {T o w : Nat} {inc : Bool} {d0 d1 : Reg64} {m : Nat} (hm : m < 2 ^ 20)
    (hd0 : d0 ≠ .rax ∧ d0 ≠ .rcx ∧ d0 ≠ .rdx ∧ d0 ≠ .rbp ∧ d0 ≠ .r15)
    (hd1 : d1 ≠ .rax ∧ d1 ≠ .rcx ∧ d1 ≠ .rdx ∧ d1 ≠ .rbp ∧ d1 ≠ .r15 ∧ d1 ≠ d0)
    (hp : s.reg .rbp = p) (hs : Scr s.mem p g) (h15 : s.reg .r15 = m.toUInt64)
    (hT : T + m / 64 < scrN) (hw : (g (T + m / 64)).c0 = w.toUInt64)
    (ho : o + w + (m + if inc then 1 else 0) % 64 < scrN)
    {xs : List Stmt} {P E : QState → Prop}
    (k : ∀ s', s'.mem = s.mem → RegsFrame [.rax, .rcx, .rdx, d0, d1] s s' →
      s'.reg d0 = (g (o + (w + (m + if inc then 1 else 0) % 64))).c0 →
      s'.reg d1 = (g (o + (w + (m + if inc then 1 else 0) % 64))).c1 → WP (blk xs) s' P E) :
    WP (blk (lk T o inc d0 d1 ++ xs)) s P E := by
  unfold lk
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
    (NativeVm.Transcript.wp_reg (by rfl) ?_))
  refine ldi0 (o := T) (i := m / 64) (by simpa using hp)
    (by simp only [QState.setReg_reg, ↓reduceIte, h15]; exact shr6 (by omega)) hs hT ?_
  rw [hw]
  refine zpos_spec hm (by simpa using h15) fun s1 m1 f1 r1 ↦ ?_
  have r1c : s1.reg .rcx = w.toUInt64 := by rw [f1 .rcx (by decide)]; simp
  have r1p : s1.reg .rbp = p := by rw [f1 .rbp (by decide)]; simpa using hp
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
    (NativeVm.Transcript.wp_reg (by rfl) ?_))
  have hix : (s1.reg .rcx + s1.reg .rdx) <<< (4 : Nat).toUInt64 =
      (8 * (2 * (w + (m + if inc then 1 else 0) % 64))).toUInt64 := by
    rw [r1c, r1, NativeVm.Transcript.toUInt64_add]; exact rax16 _
  have hs1 : Scr s1.mem p g := hs.congr fun a _ ↦ by rw [m1]; rfl
  refine ldi0 (o := o) (i := w + (m + if inc then 1 else 0) % 64) (by simpa using r1p)
    (by simp only [QState.setReg_reg, ↓reduceIte]; exact hix) hs1 (by omega) ?_
  refine ldi1 (o := o) (i := w + (m + if inc then 1 else 0) % 64)
    (by simp [r1p, Ne.symm hd0.2.2.2.1])
    (by simp only [QState.setReg_reg, ↓reduceIte, Ne.symm hd0.1]; exact hix) hs1 (by omega) ?_
  refine k _ (by simp [m1]) ?_ (by simp [hd1.2.2.2.2.2.symm]) (by simp)
  exact rf_trans (l := [.rax, .rcx]) (l'' := [.rax, .rcx, .rdx, d0, d1]) (by rf_tac)
    (rf_trans (l := [.rdx]) (l' := [.rcx, .rax, d0, d1]) (l'' := [.rax, .rcx, .rdx, d0, d1]) f1
      (by rf_tac))

end NativeVm.Code.P6
