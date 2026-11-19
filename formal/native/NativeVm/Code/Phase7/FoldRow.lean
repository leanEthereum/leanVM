module

public import NativeVm.Code.Data
public import NativeVm.Field.Arrays
public import NativeVm.Equiv.Field

/-!
# Folding a query row

`foldRowC` computes `foldRow (lanesW index row) x rs`, the value a WHIR query row folds to: the
row's lanes (`lanesW`: level 0's words reversed as `K` elements, a later level's pairs of words)
go into a buffer of `foldBufWords` words at `A`, element `k` in words `2 k`, `2 k + 1` (`BufAt`),
`x` into its last word; then each round folds the buffer in place (`foldPass`: element `i` becomes
`v[2i+1] + f·v[2i]`, read before it is written, its factor `f = α + x·β` computed once, by
`escale`), and the result is element `0`, or `0` when the lanes ran out.

Registers: `r13` the row, `r15` its size, `rdx` the index, `rsi` `x`, `r14` the rounds
(`RoundsAt`), `rbx` the buffer; the result in `r9`, `r10`. In the rounds' loop `rbp` holds
`A - 16`, `r13` eight times the elements' count, `r14` the current round, `r15` the rounds left
and `rsi` the pass's offset `16 i + 8`, so that `rbp + 2 rsi` is the pair `i` reads and
`rbp + rsi + 8` the element it writes.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd wd_zero wd_inj wd_ne_of_disj Fits Disj wp_load wp_store wp_storei
  wdisp wdisp_toUInt64 toNat_toUInt64 toUInt64_lt)
open NativeVm.Field (eOf eOf_add emul escale emul_spec escale_spec eRegs sqRegs isSome_setMem)

/-! ## The model -/

/-- The lanes a query row folds: level 0's words reversed as `K` elements, later levels' pairs. -/
def lanesW (index : Nat) (row : Array UInt64) : Array EW :=
  if index = 0 then row.reverse.map EW.ofK else extRow row

/-- The buffer's words: the lanes (at most `128` words), then `x` in the last. -/
def foldBufWords : Nat := 256

/-! The kernel's pieces and facts, in `FR` (apart from the other kernels' helpers). -/

namespace FR

/-- `foldLanes` by its factor. -/
def foldWith (f : EW) (v : Array EW) : Array EW :=
  (Array.range (v.size / 2)).map fun i ↦ v.getD (2 * i + 1) 0 + f * v.getD (2 * i) 0

theorem foldLanes_eq (x : UInt64) (r : FoldRoundW) (v : Array EW) :
    foldLanes x r v = foldWith (r.alpha + EW.scale x r.beta) v := rfl

theorem foldWith_size (f : EW) (v : Array EW) : (foldWith f v).size = v.size / 2 := by
  simp [foldWith]

theorem foldWith_getD (f : EW) (v : Array EW) {i : Nat} (hi : i < v.size / 2) :
    (foldWith f v).getD i 0 = v.getD (2 * i + 1) 0 + f * v.getD (2 * i) 0 := by
  simp [foldWith, hi]

theorem lanes0_getD (row : Array UInt64) {j : Nat} (hj : j < row.size) :
    (row.reverse.map EW.ofK).getD j 0 = EW.ofK (row.getD (row.size - 1 - j) 0) := by
  simp [hj, show row.size - 1 - j < row.size by omega]

theorem extRow_size (row : Array UInt64) : (extRow row).size = row.size / 2 := by
  simp [extRow]

theorem extRow_getD (row : Array UInt64) {j : Nat} (hj : j < row.size / 2) :
    (extRow row).getD j 0 = ⟨row.getD (2 * j) 0, row.getD (2 * j + 1) 0⟩ := by
  simp [extRow, hj]

/-- The values after the first `r` rounds. -/
def foldsTo (x : UInt64) (rs : Array FoldRoundW) (v : Array EW) (r : Nat) : Array EW :=
  (rs.toList.take r).foldl (fun v r ↦ foldLanes x r v) v

theorem foldsTo_succ (x : UInt64) (rs : Array FoldRoundW) (v : Array EW) {r : Nat}
    (hr : r < rs.size) : foldsTo x rs v (r + 1) = foldLanes x rs[r] (foldsTo x rs v r) := by
  rw [foldsTo, List.take_add_one, List.getElem?_eq_getElem (by simpa using hr), List.foldl_append]
  simp [foldsTo]

theorem foldsTo_size (x : UInt64) (rs : Array FoldRoundW) (v : Array EW) :
    foldsTo x rs v rs.size = rs.foldl (fun v r ↦ foldLanes x r v) v := by
  simp [foldsTo, List.take_of_length_le]

/-! ## Words -/

theorem toE_eOf (y : EW) : y.toE = eOf y.c0 y.c1 := rfl

theorem wd_ne {A : UInt64} {a b : Nat} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (h : a ≠ b) :
    wd A a ≠ wd A b := fun e ↦ h ((wd_inj ha hb).mp e)

/-- The elements `v` in the buffer at `A`: element `k` in words `2 k`, `2 k + 1`. -/
def BufAt (mem : UInt64 → Option UInt64) (A : UInt64) (v : Array EW) : Prop :=
  ∀ k < v.size, mem (wd A (2 * k)) = some (v.getD k 0).c0 ∧
    mem (wd A (2 * k + 1)) = some (v.getD k 0).c1

/-- `m'` is `m` but for the buffer's first `128` words, which hold the lanes. -/
def Low (A : UInt64) (m m' : UInt64 → Option UInt64) : Prop :=
  ∀ a, (∀ k < 128, a ≠ wd A k) → m' a = m a

/-- The buffer's words are there. -/
def Dom (A : UInt64) (m : UInt64 → Option UInt64) : Prop :=
  ∀ k < foldBufWords, (m (wd A k)).isSome

theorem Low.refl (A : UInt64) (m : UInt64 → Option UInt64) : Low A m m := fun _ _ ↦ rfl

theorem Low.trans {A : UInt64} {m₁ m₂ m₃ : UInt64 → Option UInt64} (h : Low A m₁ m₂)
    (h' : Low A m₂ m₃) : Low A m₁ m₃ := fun a ha ↦ (h' a ha).trans (h a ha)

theorem Low.setMem {A : UInt64} {m : UInt64 → Option UInt64} {t : QState} (h : Low A m t.mem)
    {k : Nat} (hk : k < 128) (v : UInt64) : Low A m (t.setMem (wd A k) v).mem := fun a ha ↦ by
  simp only [QState.setMem_mem, ha k hk, ite_false]
  exact h a ha

/-- A word of the buffer past the lanes is kept. -/
theorem Low.high {A : UInt64} {m m' : UInt64 → Option UInt64} (h : Low A m m') {k : Nat}
    (hk : 128 ≤ k) (hk' : k < 2 ^ 61) : m' (wd A k) = m (wd A k) :=
  h _ fun j hj ↦ wd_ne hk' (by omega) (by omega)

/-- A word outside the buffer is kept. -/
theorem Low.out {A p : UInt64} {n : Nat} {m m' : UInt64 → Option UInt64} (h : Low A m m')
    (hfA : Fits A foldBufWords) (hfp : Fits p n) (hd : Disj A foldBufWords p n) {j : Nat}
    (hj : j < n) : m' (wd p j) = m (wd p j) :=
  h _ fun k hk ↦ (wd_ne_of_disj hfA hfp hd (by unfold foldBufWords; omega) hj).symm

theorem Dom.setMem {A : UInt64} {t : QState} (h : Dom A t.mem) (a v : UInt64) :
    Dom A (t.setMem a v).mem := fun k hk ↦ isSome_setMem (h k hk) a v

theorem Dom.get {A : UInt64} {m : UInt64 → Option UInt64} (h : Dom A m) {k : Nat}
    (hk : k < foldBufWords) : ∃ w, m (wd A k) = some w :=
  Option.isSome_iff_exists.mp (h k hk)

/-! ## Numbers -/

theorem shl_toUInt64 (n k : Nat) (hk : k < 64) :
    n.toUInt64 <<< (k.toUInt64) = (2 ^ k * n).toUInt64 :=
  NativeVm.Transcript.toUInt64_shl n k hk

theorem shr_toUInt64 {n : Nat} (k : Nat) (hn : n < 2 ^ 64) (hk : k < 64) :
    n.toUInt64 >>> (k.toUInt64) = (n / 2 ^ k).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, toNat_toUInt64 hn, toNat_toUInt64 (by omega),
    toNat_toUInt64 (lt_of_le_of_lt (Nat.div_le_self _ _) hn), Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]

theorem cond_test_true {r : Reg64} {t : QState}
    (h : (Cond.test false r (.reg r)).eval t = true) : t.reg r ≠ 0 := by
  simpa [Cond.eval, Rhs.eval] using h

theorem cond_test_false {r : Reg64} {t : QState}
    (h : (Cond.test false r (.reg r)).eval t = false) : t.reg r = 0 := by
  simpa [Cond.eval, Rhs.eval] using h

theorem cnt_ne {n i : Nat} (h : (n - i).toUInt64 ≠ 0) : i < n := by
  by_contra hc
  exact h (by rw [show n - i = 0 by omega]; rfl)

theorem cnt_eq {n i : Nat} (hn : n < 2 ^ 64) (hi : i ≤ n) (h : (n - i).toUInt64 = 0) : i = n := by
  have := (NativeVm.Transcript.toUInt64_inj (a := n - i) (b := 0) (by omega) (by norm_num)).mp h
  omega

theorem cnt_succ {n i : Nat} (hi : i < n) : (n - i).toUInt64 - 1 = (n - (i + 1)).toUInt64 := by
  rw [show n - i = n - (i + 1) + 1 by omega, NativeVm.Field.toUInt64_succ_sub]

theorem cnt_dec {n i : Nat} (hn : n < 2 ^ 64) (hi : i < n) :
    (n - (i + 1)).toUInt64.toNat < (n - i).toUInt64.toNat := by
  rw [toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
  omega

/-- Arithmetic on addresses, as a commutative ring. -/
macro "wring" : tactic => `(tactic| (
  open scoped UInt64.CommRing in
  (simp only [wd, Nat.toUInt64_eq, UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.reduceOfNat] <;>
    ring)))

theorem eval_atw {t : QState} {r : Reg64} {p : UInt64} {j k m : Nat} (h : t.reg r = wd p j)
    (hm : j + k = m) : (at_ r (wdisp k)).eval t = wd p m := by
  rw [NativeVm.Transcript.eval_wd h, hm]

theorem eval_bp {t : QState} {A : UInt64} {k m : Nat} (h : t.reg .rbp = A - 16)
    (hm : k = m + 2) : (at_ .rbp (wdisp k)).eval t = wd A m := by
  rw [NativeVm.Transcript.eval_at, h, wdisp_toUInt64, hm]
  wring

/-! ## One pass -/

/-- Word `k` of the pair a pass reads: `rbp + 2 rsi + 8 k`. -/
def srcW (k : Nat) : Addr := { base := .rbp, idx := some (.rsi, .W16), disp := wdisp k }

/-- Word `k - 1` of the element a pass writes: `rbp + rsi + 8 k`. -/
def dstW (k : Nat) : Addr := { base := .rbp, idx := some (.rsi, .W8), disp := wdisp k }

theorem srcW_eval {t : QState} {A : UInt64} {i k m : Nat} (hb : t.reg .rbp = A - 16)
    (hs : t.reg .rsi = (16 * i + 8).toUInt64) (hm : 4 * i + k = m) :
    (srcW k).eval t = wd A m := by
  simp only [srcW, Addr.eval, hb, hs, wdisp_toUInt64, Width.bytes]
  rw [← hm]
  wring

theorem dstW_eval {t : QState} {A : UInt64} {i k m : Nat} (hb : t.reg .rbp = A - 16)
    (hs : t.reg .rsi = (16 * i + 8).toUInt64) (hm : 2 * i + k = m + 1) :
    (dstW k).eval t = wd A m := by
  simp only [dstW, Addr.eval, hb, hs, wdisp_toUInt64, Width.bytes]
  have : k = m + 1 - 2 * i := by omega
  subst this
  have e : (8 * (m + 1 - 2 * i)).toUInt64 + 16 * i.toUInt64 = 8 * m.toUInt64 + 8 := by
    have := congrArg Nat.toUInt64 (show 8 * (m + 1 - 2 * i) + 16 * i = 8 * m + 8 by omega)
    simp only [Nat.toUInt64_eq, UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.reduceOfNat] at this ⊢
    exact this
  open scoped UInt64.CommRing in
  simp only [wd, Nat.toUInt64_eq, UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.reduceOfNat] at e ⊢
  linear_combination e

/-- One round's pass, in place: element `i` (`i < n / 2`, `8 n` in `r13`) becomes
`v[2i+1] + f·v[2i]`, `f` in `B`. -/
def foldPass : Stmt := .loop (.cmp .ltu .rsi (.reg .r13)) (blk [
  I (.load .r9 (srcW 0)), I (.load .r10 (srcW 1)), emul,
  I (.load .rdx (srcW 2)), I (.xor .r9 .rdx), I (.load .rdx (srcW 3)), I (.xor .r10 .rdx),
  I (.store (dstW 1) .r9), I (.store (dstW 2) .r10), I (.addi .rsi 16)])

/-- The registers `foldPass` writes. -/
abbrev passRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .rsi]

variable {F : QState → Prop}

/-- **`foldPass` folds the buffer once.** -/
theorem foldPass_spec {t : QState} {A : UInt64} {f : EW} {v : Array EW}
    (hb : t.reg .rbp = A - 16) (hsi : t.reg .rsi = 8) (h13 : t.reg .r13 = (8 * v.size).toUInt64)
    (h11 : t.reg .r11 = f.c0) (h12 : t.reg .r12 = f.c1) (hv : BufAt t.mem A v)
    (hn : v.size ≤ 64) (hd : Dom A t.mem) :
    WP foldPass t (fun t' ↦ BufAt t'.mem A (foldWith f v) ∧ Low A t.mem t'.mem ∧ Dom A t'.mem ∧
      RegsFrame passRegs t t') F := by
  set n := v.size with hn_def
  set w := foldWith f v with hw_def
  unfold foldPass
  apply WP.loop (fun t' ↦ ∃ i ≤ n / 2, t'.reg .rsi = (16 * i + 8).toUInt64 ∧
      (∀ k < i, t'.mem (wd A (2 * k)) = some (w.getD k 0).c0 ∧
        t'.mem (wd A (2 * k + 1)) = some (w.getD k 0).c1) ∧
      (∀ j, 2 * i ≤ j → j < n → t'.mem (wd A (2 * j)) = some (v.getD j 0).c0 ∧
        t'.mem (wd A (2 * j + 1)) = some (v.getD j 0).c1) ∧
      Low A t.mem t'.mem ∧ Dom A t'.mem ∧ RegsFrame passRegs t t')
    (fun t' ↦ 2 ^ 64 - (t'.reg .rsi).toNat)
  · exact ⟨0, Nat.zero_le _, by rw [hsi]; rfl, fun k hk ↦ absurd hk (Nat.not_lt_zero _),
      fun j _ hj ↦ hv j hj, Low.refl _ _, hd, NativeVm.Field.RegsFrame.refl _ _⟩
  · intro t' ⟨i, hi, hs, hW, hV, hL, hD, hf⟩ hc
    have r13' : t'.reg .r13 = (8 * n).toUInt64 := by rw [hf .r13 (by decide)]; exact h13
    have rb : t'.reg .rbp = A - 16 := by rw [hf .rbp (by decide)]; exact hb
    have hin : i < n / 2 := by
      have hc' : t'.reg .rsi < t'.reg .r13 := of_decide_eq_true hc
      rw [hs, r13', toUInt64_lt (by omega) (by omega)] at hc'
      omega
    obtain ⟨a0, a1⟩ := hV (2 * i) le_rfl (by omega)
    obtain ⟨b0, b1⟩ := hV (2 * i + 1) (by omega) (by omega)
    refine wp_load (srcW_eval rb hs (k := 0) (m := 2 * (2 * i)) (by omega)) a0 ?_
    refine wp_load (srcW_eval (by rsimp; exact rb) (by rsimp; exact hs) (k := 1)
      (m := 2 * (2 * i) + 1) (by omega)) a1 ?_
    refine NativeVm.Field.WP.then (emul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1 e2
    have k : ∀ q ∉ eRegs, t₁.reg q = t'.reg q := fun q hq ↦ by
      rw [e3 q hq]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp [hq.2.2.2.2.2.1, hq.2.2.2.2.2.2]
    have rb₁ : t₁.reg .rbp = A - 16 := by rw [k .rbp (by decide)]; exact rb
    have hs₁ : t₁.reg .rsi = (16 * i + 8).toUInt64 := by rw [k .rsi (by decide)]; exact hs
    refine wp_load (srcW_eval rb₁ hs₁ (k := 2) (m := 2 * (2 * i + 1)) (by omega))
      (by rw [e2]; exact b0) ?_
    fstep
    refine wp_load (srcW_eval (by rsimp; exact rb₁) (by rsimp; exact hs₁) (k := 3)
      (m := 2 * (2 * i + 1) + 1) (by omega)) (by rsimp; rw [e2]; exact b1) ?_
    fstep
    refine wp_store (dstW_eval (by rsimp; exact rb₁) (by rsimp; exact hs₁) (k := 1) (m := 2 * i)
      (by omega)) (by rsimp; rw [e2]; exact hD _ (by unfold foldBufWords; omega)) ?_
    refine wp_store (dstW_eval (by rsimp; exact rb₁) (by rsimp; exact hs₁) (k := 2)
      (m := 2 * i + 1) (by omega))
      (isSome_setMem (by rsimp; rw [e2]; exact hD _ (by unfold foldBufWords; omega)) _ _) ?_
    fstep
    fdone
    -- The element written.
    have key : (⟨t₁.reg .r9 ^^^ (v.getD (2 * i + 1) 0).c0,
        t₁.reg .r10 ^^^ (v.getD (2 * i + 1) 0).c1⟩ : EW) = w.getD i 0 := by
      rw [hw_def, foldWith_getD f v hin]
      apply NativeVm.Equiv.EW.toE_injective
      rw [NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_mul]
      simp only [toE_eOf]
      rw [eOf_add, e1, hf .r11 (by decide), hf .r12 (by decide), h11, h12]
      ring
    have v0 := congrArg EW.c0 key
    have v1 := congrArg EW.c1 key
    simp only at v0 v1
    have n01 : wd A (2 * i) ≠ wd A (2 * i + 1) := wd_ne (by omega) (by omega) (by omega)
    refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hs₁]
      wring
    · intro q hq
      simp only [QState.setMem_mem, QState.setReg_mem, e2]
      by_cases hqi : q < i
      · have m0 : wd A (2 * q) ≠ wd A (2 * i) := wd_ne (by omega) (by omega) (by omega)
        have m1 : wd A (2 * q) ≠ wd A (2 * i + 1) := wd_ne (by omega) (by omega) (by omega)
        have m2 : wd A (2 * q + 1) ≠ wd A (2 * i) := wd_ne (by omega) (by omega) (by omega)
        have m3 : wd A (2 * q + 1) ≠ wd A (2 * i + 1) := wd_ne (by omega) (by omega) (by omega)
        simp only [m0, m1, m2, m3, ite_false]
        exact hW q hqi
      · obtain rfl : q = i := by omega
        simp only [n01, ite_false, ite_true, v0, v1]
        exact ⟨trivial, trivial⟩
    · intro j hj hjn
      have m0 : wd A (2 * j) ≠ wd A (2 * i) := wd_ne (by omega) (by omega) (by omega)
      have m1 : wd A (2 * j) ≠ wd A (2 * i + 1) := wd_ne (by omega) (by omega) (by omega)
      have m2 : wd A (2 * j + 1) ≠ wd A (2 * i) := wd_ne (by omega) (by omega) (by omega)
      have m3 : wd A (2 * j + 1) ≠ wd A (2 * i + 1) := wd_ne (by omega) (by omega) (by omega)
      simp only [QState.setMem_mem, QState.setReg_mem, e2, m0, m1, m2, m3, ite_false]
      exact hV j (by omega) hjn
    · refine Low.setMem (Low.setMem ?_ (by omega) _) (by omega) _
      simp only [QState.setReg_mem, e2]
      exact hL
    · refine Dom.setMem (Dom.setMem ?_ _ _) _ _
      simp only [QState.setReg_mem, e2]
      exact hD
    · intro q hq
      have hq' := hq
      simp only [passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq'
      obtain ⟨_, _, _, hdx, _, h9, h10, hsi'⟩ := hq'
      have hk : q ∉ eRegs := by simp [eRegs, *]
      simp only [QState.setMem_reg, QState.setReg_reg, hdx, h9, h10, hsi', ↓reduceIte, k q hk]
      exact hf q hq
    · rw [hs₁, hs, show (16 : UInt64) = (16 : Nat).toUInt64 from rfl,
        NativeVm.Transcript.toUInt64_add, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t' ⟨i, hi, hs, hW, _, hL, hD, hf⟩ hc
    have r13' : t'.reg .r13 = (8 * n).toUInt64 := by rw [hf .r13 (by decide)]; exact h13
    have hin : n / 2 ≤ i := by
      have hc' : ¬ t'.reg .rsi < t'.reg .r13 := of_decide_eq_false hc
      rw [hs, r13', toUInt64_lt (by omega) (by omega)] at hc'
      omega
    refine ⟨fun k hk ↦ ?_, hL, hD, hf⟩
    rw [foldWith_size] at hk
    exact hW k (by omega)

/-! ## The rounds -/

theorem shr4 {n : Nat} (hn : n < 2 ^ 64) : n.toUInt64 >>> (4 : UInt64) = (n / 16).toUInt64 := by
  have h := shr_toUInt64 4 hn (by norm_num)
  rw [show (2 : Nat) ^ 4 = 16 by norm_num] at h
  exact h

theorem shl3 (n : Nat) : n.toUInt64 <<< (3 : UInt64) = (8 * n).toUInt64 := by
  have h := shl_toUInt64 n 3 (by norm_num)
  rw [show (2 : Nat) ^ 3 = 8 by norm_num] at h
  exact h

theorem shl2 (n : Nat) : n.toUInt64 <<< (2 : UInt64) = (4 * n).toUInt64 := by
  have h := shl_toUInt64 n 2 (by norm_num)
  rw [show (2 : Nat) ^ 2 = 4 by norm_num] at h
  exact h

theorem shl1 (n : Nat) : n.toUInt64 <<< (1 : UInt64) = (2 * n).toUInt64 := by
  have h := shl_toUInt64 n 1 (by norm_num)
  rw [show (2 : Nat) ^ 1 = 2 by norm_num] at h
  exact h

theorem shr1 {n : Nat} (hn : n < 2 ^ 64) : n.toUInt64 >>> (1 : UInt64) = (n / 2).toUInt64 := by
  have h := shr_toUInt64 1 hn (by norm_num)
  rw [show (2 : Nat) ^ 1 = 2 by norm_num] at h
  exact h

theorem roundsWords_val : roundsWords = 25 := rfl

/-- The rounds' words decide `RoundsAt`. -/
theorem RoundsAt.congr' {m m' : UInt64 → Option UInt64} {Rd : UInt64} {rs : Array FoldRoundW}
    (h : Same m m' Rd roundsWords) (hx : RoundsAt m Rd rs) : RoundsAt m' Rd rs := by
  obtain ⟨h1, h2, h3⟩ := hx
  have h6 : rs.size ≤ 6 := h1
  refine ⟨h1, h2.congr (h.base (by rw [roundsWords_val]; omega) rfl), fun i hi ↦
    ⟨(h3 i hi).1.congr (h.sub ?_), (h3 i hi).2.congr (h.sub ?_)⟩⟩ <;> rw [roundsWords_val] <;> omega

/-- One round: its factor `α + x·β` in `B`, then a pass; `r13 := 8 (n / 2)`; the next round. -/
def roundStep : Stmt := blk [
  I (.load .r9 (at_ .r14 (wdisp 3))), I (.load .r10 (at_ .r14 (wdisp 4))),
  I (.load .r11 (at_ .rbp (wdisp 257))), escale,
  I (.load .rdx (at_ .r14 (wdisp 1))), I (.xor .r9 .rdx),
  I (.load .rdx (at_ .r14 (wdisp 2))), I (.xor .r10 .rdx),
  I (.mov .r11 .r9), I (.mov .r12 .r10), I (.movi .rsi 8), foldPass,
  I (.shri .r13 4), I (.shli .r13 3), I (.addi .r14 32), I (.subi .r15 1)]

/-- The rounds, `r15` of them from `r14`. -/
def roundsLoop : Stmt := .loop (.test false .r15 (.reg .r15)) roundStep

/-- **`roundsLoop` runs the rounds.** -/
theorem roundsLoop_spec {t : QState} {A Rd x : UInt64} {rs : Array FoldRoundW} {v : Array EW}
    (hb : t.reg .rbp = A - 16) (h14 : t.reg .r14 = Rd) (h15 : t.reg .r15 = rs.size.toUInt64)
    (h13 : t.reg .r13 = (8 * v.size).toUInt64) (hv : BufAt t.mem A v) (hn : v.size ≤ 64)
    (hx : t.mem (wd A 255) = some x) (hRd : RoundsAt t.mem Rd rs) (hd : Dom A t.mem)
    (hfA : Fits A foldBufWords) (hfRd : Fits Rd roundsWords)
    (hARd : Disj A foldBufWords Rd roundsWords) :
    WP roundsLoop t (fun t' ↦ BufAt t'.mem A (foldsTo x rs v rs.size) ∧
      t'.reg .r13 = (8 * (foldsTo x rs v rs.size).size).toUInt64 ∧ t'.reg .rbp = A - 16 ∧
      Low A t.mem t'.mem ∧ Dom A t'.mem ∧ (foldsTo x rs v rs.size).size ≤ 64) F := by
  have h6 : rs.size ≤ 6 := hRd.1
  have f0 : foldsTo x rs v 0 = v := rfl
  unfold roundsLoop
  apply WP.loop (fun t' ↦ ∃ r ≤ rs.size, t'.reg .rbp = A - 16 ∧ t'.reg .r14 = wd Rd (4 * r) ∧
      t'.reg .r15 = (rs.size - r).toUInt64 ∧
      t'.reg .r13 = (8 * (foldsTo x rs v r).size).toUInt64 ∧ BufAt t'.mem A (foldsTo x rs v r) ∧
      (foldsTo x rs v r).size ≤ 64 ∧ Low A t.mem t'.mem ∧ Dom A t'.mem)
    (fun t' ↦ (t'.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, hb, ?_, ?_, ?_, ?_, ?_, Low.refl _ _, hd⟩
    · rw [h14, Nat.mul_zero, wd_zero]
    · rw [h15, Nat.sub_zero]
    · rw [f0]; exact h13
    · rw [f0]; exact hv
    · rw [f0]; exact hn
  · intro t' ⟨r, hr, rb, r14', r15', r13', hB, hsz, hL, hD⟩ hc
    have hrs : r < rs.size := cnt_ne (by rw [← r15']; exact cond_test_true hc)
    have get : ∀ j < roundsWords, t'.mem (wd Rd j) = t.mem (wd Rd j) :=
      fun j hj ↦ hL.out hfA hfRd hARd hj
    obtain ⟨⟨α0, α1⟩, ⟨β0, β1⟩⟩ := hRd.2.2 r hrs
    rw [Code.wd_wd] at α1 β1
    have ma0 : t'.mem (wd Rd (4 * r + 1)) = some rs[r].alpha.c0 := by
      rw [get _ (by rw [roundsWords_val]; omega), show 4 * r + 1 = 1 + 4 * r by omega]; exact α0
    have ma1 : t'.mem (wd Rd (4 * r + 2)) = some rs[r].alpha.c1 := by
      rw [get _ (by rw [roundsWords_val]; omega), show 4 * r + 2 = 1 + 4 * r + 1 by omega]
      exact α1
    have mb0 : t'.mem (wd Rd (4 * r + 3)) = some rs[r].beta.c0 := by
      rw [get _ (by rw [roundsWords_val]; omega), show 4 * r + 3 = 3 + 4 * r by omega]; exact β0
    have mb1 : t'.mem (wd Rd (4 * r + 4)) = some rs[r].beta.c1 := by
      rw [get _ (by rw [roundsWords_val]; omega), show 4 * r + 4 = 3 + 4 * r + 1 by omega]
      exact β1
    have mx : t'.mem (wd A 255) = some x := (hL.high (by norm_num) (by norm_num)).trans hx
    refine wp_load (eval_atw r14' (k := 3) (m := 4 * r + 3) rfl) mb0 ?_
    refine wp_load (eval_atw (by rsimp; exact r14') (k := 4) (m := 4 * r + 4) rfl) mb1 ?_
    refine wp_load (eval_bp (by rsimp; exact rb) (k := 257) (m := 255) rfl) mx ?_
    refine NativeVm.Field.WP.then (escale_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
    rsimp at e1 e2
    have k : ∀ q ∉ sqRegs, q ≠ .r11 → t₁.reg q = t'.reg q := fun q hq h11 ↦ by
      rw [e3 q hq]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp [hq.2.2.2.2.1, hq.2.2.2.2.2, h11]
    have r14₁ : t₁.reg .r14 = wd Rd (4 * r) := by rw [k .r14 (by decide) (by decide)]; exact r14'
    refine wp_load (eval_atw r14₁ (k := 1) (m := 4 * r + 1) rfl) (by rw [e2]; exact ma0) ?_
    fstep
    refine wp_load (eval_atw (by rsimp; exact r14₁) (k := 2) (m := 4 * r + 2) rfl)
      (by rsimp; rw [e2]; exact ma1) ?_
    fstep; fstep; fstep; fstep
    have hfe : (⟨t₁.reg .r9 ^^^ rs[r].alpha.c0, t₁.reg .r10 ^^^ rs[r].alpha.c1⟩ : EW) =
        rs[r].alpha + EW.scale x rs[r].beta := by
      apply NativeVm.Equiv.EW.toE_injective
      rw [NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_scale]
      simp only [toE_eOf]
      rw [eOf_add, e1]
      ring
    refine NativeVm.Field.WP.then (foldPass_spec (A := A) (v := foldsTo x rs v r)
      (f := ⟨t₁.reg .r9 ^^^ rs[r].alpha.c0, t₁.reg .r10 ^^^ rs[r].alpha.c1⟩)
      (by rsimp; rw [k .rbp (by decide) (by decide)]; exact rb) (by rsimp)
      (by rsimp; rw [k .r13 (by decide) (by decide)]; exact r13') (by rsimp) (by rsimp)
      (by rsimp; rw [e2]; exact hB) hsz (by rsimp; rw [e2]; exact hD))
      fun t₂ ⟨p1, p2, p3, p4⟩ ↦ ?_
    rsimp at p2
    rw [e2] at p2
    have k₂ : ∀ q ∉ passRegs, q ≠ .r11 → q ≠ .r12 → t₂.reg q = t'.reg q := fun q hq h11 h12 ↦ by
      rw [p4 q hq]
      have hq' := hq
      simp only [passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq'
      rsimp
      simp only [hq'.2.2.2.2.2.2.2, hq'.2.2.2.2.2.1, hq'.2.2.2.2.2.2.1, hq'.2.2.2.1, h11, h12,
        ↓reduceIte]
      exact k q (by simp [sqRegs, hq'.1, hq'.2.1, hq'.2.2.1, hq'.2.2.2.2.1, hq'.2.2.2.2.2.1,
        hq'.2.2.2.2.2.2.1]) h11
    fstep; fstep; fstep; fstep
    fdone
    have hstep := foldsTo_succ x rs v hrs
    rw [foldLanes_eq, ← hfe] at hstep
    have hsz' : (foldsTo x rs v (r + 1)).size = (foldsTo x rs v r).size / 2 := by
      rw [hstep, foldWith_size]
    refine ⟨⟨r + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, hL.trans p2, p3⟩, ?_⟩
    · rw [k₂ .rbp (by decide) (by decide) (by decide)]; exact rb
    · rw [k₂ .r14 (by decide) (by decide) (by decide), r14']
      wring
    · rw [k₂ .r15 (by decide) (by decide) (by decide), r15', cnt_succ hrs]
    · rw [k₂ .r13 (by decide) (by decide) (by decide), r13', shr4 (by omega), shl3, hsz']
      congr 2
      omega
    · rw [hstep]; exact p1
    · rw [hsz']; omega
    · rw [k₂ .r15 (by decide) (by decide) (by decide), r15', cnt_succ hrs]
      exact cnt_dec (by omega) hrs
  · intro t' ⟨r, hr, rb, _, r15', r13', hB, hsz, hL, hD⟩ hc
    have hre : r = rs.size := cnt_eq (by omega) hr (by rw [← r15']; exact cond_test_false hc)
    subst hre
    exact ⟨hB, r13', rb, hL, hD, hsz⟩

/-! ## The lanes -/

/-- Level 0's lanes: word `n - 1 - k` of the row at `r13` to element `k` at `r8`, limb `1` zero,
`rcx` counting down from `n`. -/
def copyRev : Stmt := .loop (.test false .rcx (.reg .rcx)) (blk [
  I (.subi .rcx 1), I (.load .rax { base := .r13, idx := some (.rcx, .W64), disp := wdisp 0 }),
  I (.store (at_ .r8 (wdisp 0)) .rax), I (.storei (at_ .r8 (wdisp 1)) 0), I (.addi .r8 16)])

/-- **`copyRev` writes level 0's lanes.** -/
theorem copyRev_spec {t : QState} {A R : UInt64} {row : Array UInt64}
    (h13 : t.reg .r13 = R) (hcx : t.reg .rcx = row.size.toUInt64) (h8 : t.reg .r8 = A)
    (hR : ∀ j < row.size, t.mem (wd R j) = some (row.getD j 0)) (hrow : row.size ≤ 64)
    (hd : Dom A t.mem) (hfA : Fits A foldBufWords) (hfR : Fits R row.size)
    (hAR : Disj A foldBufWords R row.size) :
    WP copyRev t (fun t' ↦ BufAt t'.mem A (row.reverse.map EW.ofK) ∧ Low A t.mem t'.mem ∧
      Dom A t'.mem ∧ RegsFrame [.rax, .rcx, .r8] t t') F := by
  set n := row.size with hn_def
  unfold copyRev
  apply WP.loop (fun t' ↦ ∃ k ≤ n, t'.reg .rcx = (n - k).toUInt64 ∧ t'.reg .r8 = wd A (2 * k) ∧
      (∀ j < k, t'.mem (wd A (2 * j)) = some (row.getD (n - 1 - j) 0) ∧
        t'.mem (wd A (2 * j + 1)) = some 0) ∧
      Low A t.mem t'.mem ∧ Dom A t'.mem ∧ RegsFrame [.rax, .rcx, .r8] t t')
    (fun t' ↦ (t'.reg .rcx).toNat)
  · exact ⟨0, Nat.zero_le _, by rw [hcx, Nat.sub_zero], by rw [h8, Nat.mul_zero, wd_zero],
      fun j hj ↦ absurd hj (Nat.not_lt_zero _), Low.refl _ _, hd, NativeVm.Field.RegsFrame.refl _ _⟩
  · intro t' ⟨k, hk, hc', h8', hW, hL, hD, hf⟩ hc
    have hkn : k < n := cnt_ne (by rw [← hc']; exact cond_test_true hc)
    have r13' : t'.reg .r13 = R := by rw [hf .r13 (by decide)]; exact h13
    fstep
    refine wp_load (v := row.getD (n - 1 - k) 0) (NativeVm.Transcript.eval_idx64 (j := 0)
      (by rsimp; rw [r13', wd_zero]) (by rsimp; rw [hc', cnt_succ hkn]) 0) ?_ ?_
    · rsimp
      rw [show 0 + (n - (k + 1)) + 0 = n - 1 - k by omega, hL.out hfA hfR hAR (by omega)]
      exact hR _ (by omega)
    refine wp_store (eval_atw (by rsimp; exact h8') (k := 0) (m := 2 * k) rfl)
      (by rsimp; exact hD _ (by unfold foldBufWords; omega)) ?_
    refine wp_storei (eval_atw (by rsimp; exact h8') (k := 1) (m := 2 * k + 1) rfl)
      (isSome_setMem (hD _ (by unfold foldBufWords; omega)) _ _) ?_
    fstep
    fdone
    have n01 : wd A (2 * k) ≠ wd A (2 * k + 1) := wd_ne (by omega) (by omega) (by omega)
    refine ⟨⟨k + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hc', cnt_succ hkn]
    · rw [h8']
      wring
    · intro q hq
      simp only [QState.setMem_mem, QState.setReg_mem]
      by_cases hqk : q < k
      · have m0 : wd A (2 * q) ≠ wd A (2 * k) := wd_ne (by omega) (by omega) (by omega)
        have m1 : wd A (2 * q) ≠ wd A (2 * k + 1) := wd_ne (by omega) (by omega) (by omega)
        have m2 : wd A (2 * q + 1) ≠ wd A (2 * k) := wd_ne (by omega) (by omega) (by omega)
        have m3 : wd A (2 * q + 1) ≠ wd A (2 * k + 1) := wd_ne (by omega) (by omega) (by omega)
        simp only [m0, m1, m2, m3, ite_false]
        exact hW q hqk
      · obtain rfl : q = k := by omega
        simp only [n01, ite_false, ite_true, show n - 1 - q = 0 + (n - (q + 1)) + 0 by omega]
        exact ⟨trivial, trivial⟩
    · exact Low.setMem (Low.setMem hL (by omega) _) (by omega) _
    · exact Dom.setMem (Dom.setMem hD _ _) _ _
    · intro q hq
      have hq' := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq'
      simp only [QState.setMem_reg, QState.setReg_reg, hq'.1, hq'.2.1, hq'.2.2, ↓reduceIte]
      exact hf q hq
    · rw [hc', cnt_succ hkn]
      exact cnt_dec (by omega) hkn
  · intro t' ⟨k, hk, hc', _, hW, hL, hD, hf⟩ hc
    have hkn : k = n := cnt_eq (by omega) hk (by rw [← hc']; exact cond_test_false hc)
    subst hkn
    refine ⟨fun j hj ↦ ?_, hL, hD, hf⟩
    simp only [Array.size_map, Array.size_reverse] at hj
    rw [lanes0_getD row hj]
    exact hW j hj

/-- A later level's lanes: words `j < rcx` of the row at `r13` to the buffer at `rbx`, from the
last. -/
def copyPairs : Stmt := .loop (.test false .rcx (.reg .rcx)) (blk [
  I (.subi .rcx 1), I (.load .rax { base := .r13, idx := some (.rcx, .W64), disp := wdisp 0 }),
  I (.store { base := .rbx, idx := some (.rcx, .W64), disp := wdisp 0 } .rax)])

/-- **`copyPairs` writes a later level's lanes.** -/
theorem copyPairs_spec {t : QState} {A R : UInt64} {row : Array UInt64}
    (h13 : t.reg .r13 = R) (hbx : t.reg .rbx = A)
    (hcx : t.reg .rcx = (2 * (row.size / 2)).toUInt64)
    (hR : ∀ j < row.size, t.mem (wd R j) = some (row.getD j 0)) (hrow : row.size ≤ 64)
    (hd : Dom A t.mem) (hfA : Fits A foldBufWords) (hfR : Fits R row.size)
    (hAR : Disj A foldBufWords R row.size) :
    WP copyPairs t (fun t' ↦ BufAt t'.mem A (extRow row) ∧ Low A t.mem t'.mem ∧
      Dom A t'.mem ∧ RegsFrame [.rax, .rcx] t t') F := by
  set m := 2 * (row.size / 2) with hm_def
  unfold copyPairs
  apply WP.loop (fun t' ↦ ∃ c ≤ m, t'.reg .rcx = c.toUInt64 ∧
      (∀ j, c ≤ j → j < m → t'.mem (wd A j) = some (row.getD j 0)) ∧
      Low A t.mem t'.mem ∧ Dom A t'.mem ∧ RegsFrame [.rax, .rcx] t t')
    (fun t' ↦ (t'.reg .rcx).toNat)
  · exact ⟨m, le_rfl, hcx, fun j hj hjm ↦ absurd hjm (by omega), Low.refl _ _, hd,
      NativeVm.Field.RegsFrame.refl _ _⟩
  · intro t' ⟨c, hc, hc', hW, hL, hD, hf⟩ hcnd
    have hc0 : c ≠ 0 := fun e ↦ cond_test_true hcnd (by rw [hc', e]; rfl)
    have hcx1 : t'.reg .rcx - 1 = (c - 1).toUInt64 := by
      rw [hc', show c = c - 1 + 1 by omega, NativeVm.Field.toUInt64_succ_sub, Nat.add_sub_cancel]
    have r13' : t'.reg .r13 = R := by rw [hf .r13 (by decide)]; exact h13
    have rbx' : t'.reg .rbx = A := by rw [hf .rbx (by decide)]; exact hbx
    fstep
    refine wp_load (v := row.getD (c - 1) 0) (NativeVm.Transcript.eval_idx64 (j := 0)
      (by rsimp; rw [r13', wd_zero]) (by rsimp; exact hcx1) 0) ?_ ?_
    · rsimp
      rw [show 0 + (c - 1) + 0 = c - 1 by omega, hL.out hfA hfR hAR (by omega)]
      exact hR _ (by omega)
    refine wp_store (NativeVm.Transcript.eval_idx64 (j := 0) (by rsimp; rw [rbx', wd_zero])
      (by rsimp; exact hcx1) 0)
      (by rsimp; rw [show 0 + (c - 1) + 0 = c - 1 by omega]
          exact hD _ (by unfold foldBufWords; omega)) ?_
    fdone
    refine ⟨⟨c - 1, by omega, hcx1, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro j hj hjm
      simp only [QState.setMem_mem, QState.setReg_mem]
      by_cases hjc : j = c - 1
      · subst hjc
        simp only [show 0 + (c - 1) + 0 = c - 1 by omega, ite_true]
      · have m0 : wd A j ≠ wd A (0 + (c - 1) + 0) := wd_ne (by omega) (by omega) (by omega)
        simp only [m0, ite_false]
        exact hW j (by omega) hjm
    · exact Low.setMem hL (by omega) _
    · exact Dom.setMem hD _ _
    · intro q hq
      have hq' := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq'
      simp only [QState.setMem_reg, QState.setReg_reg, hq'.1, hq'.2, ↓reduceIte]
      exact hf q hq
    · rw [hcx1, hc', toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t' ⟨c, hc, hc', hW, hL, hD, hf⟩ hcnd
    have hc0 : c = 0 := by
      have := cond_test_false hcnd
      rw [hc'] at this
      exact (NativeVm.Transcript.toUInt64_inj (b := 0) (by omega) (by norm_num)).mp this
    subst hc0
    refine ⟨fun j hj ↦ ?_, hL, hD, hf⟩
    rw [extRow_size] at hj
    rw [extRow_getD row hj]
    exact ⟨hW _ (by omega) (by omega), hW _ (by omega) (by omega)⟩

end FR

open FR

/-! ## The row -/

/-- `foldRow`: the lanes into the buffer, `x` into its last word, the rounds, element `0`. -/
def foldRowC : Stmt := blk [
  I (.store (at_ .rbx (wdisp 255)) .rsi),
  .ite (.cmp .eq .rdx (.imm 0))
    (blk [I (.mov .rcx .r15), I (.mov .r8 .rbx), copyRev, I (.mov .r12 .r15), I (.shli .r12 3)])
    (blk [I (.mov .rcx .r15), I (.shri .rcx 1), I (.shli .rcx 1), I (.mov .r12 .rcx), copyPairs,
      I (.shli .r12 2)]),
  I (.mov .r13 .r12), I (.mov .rbp .rbx), I (.subi .rbp 16),
  I (.load .r15 (at_ .r14 (wdisp 0))), roundsLoop,
  I (.load .r9 (at_ .rbp (wdisp 2))), I (.load .r10 (at_ .rbp (wdisp 3))),
  .ite (.cmp .eq .r13 (.imm 0)) (blk [I (.movi .r9 0), I (.movi .r10 0)]) .skip]

theorem lanesW_size (index : Nat) (row : Array UInt64) :
    (lanesW index row).size = if index = 0 then row.size else row.size / 2 := by
  unfold lanesW
  split <;> simp [extRow_size]

theorem foldRow_eq (x : UInt64) (rs : Array FoldRoundW) (v : Array EW) :
    foldRow v x rs = (foldsTo x rs v rs.size).getD 0 0 := by
  rw [foldsTo_size]
  rfl

/-- **`foldRowC` folds a query row.** -/
theorem foldRowC_spec {s : QState} {F : QState → Prop} {row : Array UInt64}
    {rs : Array FoldRoundW} {index : Nat} {R Rd A x : UInt64}
    (hR : WordArr s.mem R row) (h13 : s.reg .r13 = R) (h15 : s.reg .r15 = row.size.toUInt64)
    (hrow : row.size ≤ 64) (hdx : s.reg .rdx = index.toUInt64) (hidx : index < 2 ^ 64)
    (hsi : s.reg .rsi = x) (hRd : RoundsAt s.mem Rd rs) (h14 : s.reg .r14 = Rd)
    (hbx : s.reg .rbx = A) (hA : ∀ k < foldBufWords, (s.mem (wd A k)).isSome)
    (hfA : Fits A foldBufWords) (hfR : Fits R row.size) (hfRd : Fits Rd roundsWords)
    (hAR : Disj A foldBufWords R row.size) (hARd : Disj A foldBufWords Rd roundsWords) :
    WP foldRowC s (fun s' ↦ s'.reg .r9 = (foldRow (lanesW index row) x rs).c0 ∧
      s'.reg .r10 = (foldRow (lanesW index row) x rs).c1 ∧
      ∀ a, (∀ k < foldBufWords, a ≠ wd A k) → s'.mem a = s.mem a) F := by
  have hR' : ∀ j < row.size, s.mem (wd R j) = some (row.getD j 0) := fun j hj ↦ by
    rw [hR j hj]
    simp [hj]
  have hlen : (lanesW index row).size ≤ 64 := by
    rw [lanesW_size]
    split <;> omega
  unfold foldRowC
  refine wp_store (eval_atw (by rw [hbx, wd_zero]) (j := 0) (k := 255) (m := 255) rfl)
    (hA 255 (by unfold foldBufWords; omega)) ?_
  have r1 : (s.setMem (wd A 255) (s.reg .rsi)).reg = s.reg := rfl
  have x1 : (s.setMem (wd A 255) (s.reg .rsi)).mem (wd A 255) = some x := by
    simp only [QState.setMem_mem, ↓reduceIte, hsi]
  have o1 : ∀ a, a ≠ wd A 255 → (s.setMem (wd A 255) (s.reg .rsi)).mem a = s.mem a :=
    fun a ha ↦ by simp only [QState.setMem_mem, ha, ite_false]
  have d1 : Dom A (s.setMem (wd A 255) (s.reg .rsi)).mem := Dom.setMem hA _ _
  generalize s.setMem (wd A 255) (s.reg .rsi) = s₁ at r1 x1 o1 d1 ⊢
  have hR1 : ∀ j < row.size, s₁.mem (wd R j) = some (row.getD j 0) := fun j hj ↦ by
    rw [o1 _ (wd_ne_of_disj hfA hfR hAR (by unfold foldBufWords; omega) hj).symm]
    exact hR' j hj
  have hRd1 : RoundsAt s₁.mem Rd rs := RoundsAt.congr' (fun j hj ↦
    o1 _ (wd_ne_of_disj hfA hfRd hARd (by unfold foldBufWords; omega) hj).symm) hRd
  refine NativeVm.Field.WP.then (Q := fun t ↦ BufAt t.mem A (lanesW index row) ∧
      t.reg .r12 = (8 * (lanesW index row).size).toUInt64 ∧ Low A s₁.mem t.mem ∧ Dom A t.mem ∧
      t.reg .rbx = A ∧ t.reg .r14 = Rd) ?_ ?_
  · by_cases hi0 : index = 0
    · subst hi0
      refine NativeVm.Transcript.wp_ite_true
        (by simp [Cond.eval, Rhs.eval, r1, hdx, NativeVm.Field.int64Zero_toUInt64]) ?_
      fstep; fstep
      refine NativeVm.Field.WP.then (copyRev_spec (A := A) (R := R) (row := row)
        (by rsimp; rw [r1]; exact h13) (by rsimp; rw [r1]; exact h15)
        (by rsimp; rw [r1]; exact hbx) hR1 hrow d1 hfA hfR hAR) fun t ⟨c1, c2, c3, c4⟩ ↦ ?_
      have k : ∀ q ∉ [Reg64.rax, .rcx, .r8], t.reg q = s.reg q := fun q hq ↦ by
        rw [c4 q hq]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
        simp [hq.2.1, hq.2.2, r1]
      fstep; fstep
      fdone
      refine ⟨?_, ?_, c2, c3, k .rbx (by decide) ▸ hbx, k .r14 (by decide) ▸ h14⟩
      · simpa [lanesW] using c1
      · rw [k .r15 (by decide), h15, shl3, lanesW_size]
        simp only [↓reduceIte]
    · have hc : (Cond.cmp .eq .rdx (.imm 0)).eval s₁ = false := by
        simp only [Cond.eval, Rhs.eval, r1, hdx, NativeVm.Field.int64Zero_toUInt64]
        simp only [ne_eq, beq_eq_false_iff_ne]
        intro e
        exact hi0 ((NativeVm.Transcript.toUInt64_inj (b := 0) hidx (by norm_num)).mp e)
      refine NativeVm.Transcript.wp_ite_false hc ?_
      fstep; fstep [shr1 (n := row.size) (by omega)]; fstep [shl1]; fstep
      refine NativeVm.Field.WP.then (copyPairs_spec (A := A) (R := R) (row := row)
        (by rsimp; rw [r1]; exact h13) (by rsimp; rw [r1]; exact hbx)
        (by rsimp; rw [r1, h15, shr1 (by omega), shl1]) hR1 hrow d1 hfA hfR hAR)
        fun t ⟨c1, c2, c3, c4⟩ ↦ ?_
      have k : ∀ q ∉ [Reg64.rax, .rcx], q ≠ .r12 → t.reg q = s.reg q := fun q hq h12 ↦ by
        rw [c4 q hq]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
        simp [hq.2, h12, r1]
      have r12t : t.reg .r12 = (2 * (row.size / 2)).toUInt64 := by
        rw [c4 .r12 (by decide)]
        rsimp
        rw [r1, h15, shr1 (by omega), shl1]
      fstep
      fdone
      refine ⟨?_, ?_, c2, c3, k .rbx (by decide) (by decide) ▸ hbx,
        k .r14 (by decide) (by decide) ▸ h14⟩
      · simpa [lanesW, hi0] using c1
      · rw [r12t, shl2, lanesW_size]
        simp only [hi0, ↓reduceIte]
        congr 1
        omega
  · intro t ⟨q1, q2, q3, q4, q5, q6⟩
    have hRdt : RoundsAt t.mem Rd rs := RoundsAt.congr' (fun j hj ↦ q3.out hfA hfRd hARd hj) hRd1
    fstep; fstep; fstep
    refine wp_load (eval_atw (by rsimp; rw [q6, wd_zero]) (k := 0) (m := 0) rfl)
      (by rw [wd_zero]; exact hRdt.2.1.2) ?_
    refine NativeVm.Field.WP.then (roundsLoop_spec (x := x) (rs := rs) (v := lanesW index row)
      (by rsimp; rw [q5]) (by rsimp; exact q6) (by rsimp) (by rsimp; exact q2) q1 hlen
      ((q3.high (by norm_num) (by norm_num)).trans x1) hRdt q4 hfA hfRd hARd)
      fun t₂ ⟨g1, g2, g3, g4, g5, g6⟩ ↦ ?_
    rsimp at g4
    obtain ⟨w0, hw0⟩ := g5.get (k := 0) (by unfold foldBufWords; omega)
    obtain ⟨w1, hw1⟩ := g5.get (k := 1) (by unfold foldBufWords; omega)
    refine wp_load (eval_bp g3 (k := 2) (m := 0) rfl) hw0 ?_
    refine wp_load (eval_bp (by rsimp; exact g3) (k := 3) (m := 1) rfl) hw1 ?_
    have hmem : ∀ a, (∀ k < foldBufWords, a ≠ wd A k) → t₂.mem a = s.mem a := fun a ha ↦ by
      rw [g4 a fun k hk ↦ ha k (by unfold foldBufWords; omega),
        q3 a fun k hk ↦ ha k (by unfold foldBufWords; omega),
        o1 a (ha 255 (by unfold foldBufWords; omega))]
    rw [foldRow_eq]
    set V := foldsTo x rs (lanesW index row) rs.size with hV
    apply WP.ite
    by_cases hz : V.size = 0
    · have hc : (Cond.cmp .eq .r13 (.imm 0)).eval
          ((t₂.setReg .r9 w0).setReg .r10 w1) = true := by
        simp [Cond.eval, Rhs.eval, g2, hz, NativeVm.Field.int64Zero_toUInt64]
      rw [hc]
      simp only [ite_true]
      fstep; fstep
      fdone
      have hV0 : V.getD 0 0 = 0 := by simp [hz]
      rw [hV0]
      exact ⟨rfl, rfl, hmem⟩
    · have hc : (Cond.cmp .eq .r13 (.imm 0)).eval
          ((t₂.setReg .r9 w0).setReg .r10 w1) = false := by
        simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ite_false, g2,
          NativeVm.Field.int64Zero_toUInt64, beq_eq_false_iff_ne, ne_eq]
        intro e
        have := (NativeVm.Transcript.toUInt64_inj (a := 8 * V.size) (b := 0) (by omega)
          (by norm_num)).mp e
        omega
      rw [hc]
      simp only [Bool.false_eq_true, ite_false]
      refine WP.skip ⟨?_, ?_, hmem⟩
      · obtain ⟨b0, _⟩ := g1 0 (by omega)
        rsimp
        rw [hw0] at b0
        exact Option.some.inj b0
      · obtain ⟨_, b1⟩ := g1 0 (by omega)
        rsimp
        rw [hw1] at b1
        exact Option.some.inj b1

end NativeVm.Code.P7
