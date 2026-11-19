module

public import NativeVm.Code.Phase1.Math
public import NativeVm.Field.Basic
public import NativeVm.Transcript.Mem

/-!
# Phase 1's blocks

The pieces of phase 1's code, each proved once:

* `bitLen`: `rdx := bitLength rax`;
* `kapC`: `rax := κ(rsi)`, a global column's log-size (`kapF`), read from the layout's words at
  `r14` (the memory's and the bytecode's log-sizes, the heights: `KapMem`);
* `blockFlag`: `rdx := 1` if the column `rsi` is stacked (`isBlockF`), else `0`;
* `sumC`: `r10 := sumF κ r8`, the sizes `2^κ` of the stacked columns whose key (`keyF`) exceeds
  `r8`: a block's offset in the stack, or with `r8 = 0` the stack's size.

None stores; each writes the registers its spec names.
-/

@[expose] public section

namespace NativeVm.Code.Phase1

open Native NativeVm.Model LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wdisp eval_wd toNat_toUInt64 toUInt64_add toUInt64_succ wd_zero rf_trans)
open NativeVm.Field (RegsFrame.refl RegsFrame.trans RegsFrame.setReg)

variable {s : QState} {E : QState → Prop}

/-! ## Small facts -/

/-- Layout word `k`, at `r14`. -/
abbrev L (k : Nat) : Addr := at_ .r14 (wdisp k)

theorem eval_L {p : UInt64} (h : s.reg .r14 = p) (k : Nat) : (L k).eval s = wd p k := by
  rw [eval_wd (j := 0) (by rw [h, wd_zero]), Nat.zero_add]

theorem wp_ite_of {c : Cond} {t e : Stmt} {P : QState → Prop} {b : Bool} (hc : c.eval s = b)
    (ht : b = true → WP t s P E) (he : b = false → WP e s P E) : WP (.ite c t e) s P E := by
  cases b
  · exact WP.ite (by rw [hc]; exact he rfl)
  · exact WP.ite (by rw [hc]; exact ht rfl)

theorem lit_toNat (k : Nat) (hk : k < 2 ^ 63) : (Int64.ofNat k).toUInt64.toNat = k := by
  simp
  omega

theorem cmp_ltu_imm {r : Reg64} {c : Nat} (k : Nat) (hc : c < 2 ^ 64) (hk : k < 2 ^ 63)
    (h : s.reg r = c.toUInt64) : (Cond.cmp .ltu r (.imm (Int64.ofNat k))).eval s = decide (c < k) := by
  simp only [Cond.eval, Rhs.eval, h, UInt64.lt_iff_toNat_lt, toNat_toUInt64 hc, lit_toNat k hk]

theorem cmp_ltu_reg {r r' : Reg64} {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : s.reg r = a.toUInt64) (h' : s.reg r' = b.toUInt64) :
    (Cond.cmp .ltu r (.reg r')).eval s = decide (a < b) := by
  simp only [Cond.eval, Rhs.eval, h, h', UInt64.lt_iff_toNat_lt, toNat_toUInt64 ha, toNat_toUInt64 hb]

theorem cmp_eq_imm {r : Reg64} {c : Nat} (k : Nat) (hc : c < 2 ^ 64) (hk : k < 2 ^ 63)
    (h : s.reg r = c.toUInt64) : (Cond.cmp .eq r (.imm (Int64.ofNat k))).eval s = decide (c = k) := by
  simp only [Cond.eval, Rhs.eval, h]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, toNat_toUInt64 hc,
    lit_toNat k hk]

theorem cmp_geu_imm {r : Reg64} {c : Nat} (k : Nat) (hc : c < 2 ^ 64) (hk : k < 2 ^ 63)
    (h : s.reg r = c.toUInt64) : (Cond.cmp .geu r (.imm (Int64.ofNat k))).eval s = decide (k ≤ c) := by
  simp only [Cond.eval, Rhs.eval, h, UInt64.le_iff_toNat_le, toNat_toUInt64 hc, lit_toNat k hk]

/-! ## `bitLen` -/

/-- `rdx := bitLength rax`; writes `rax`, `rdx`. -/
def bitLen : Stmt := blk [I (.movi .rdx 0),
  .loop (.cmp .ne .rax (.imm 0)) (blk [I (.shri .rax 1), I (.addi .rdx 1)])]

theorem bitLen_spec (s : QState) :
    WP bitLen s (fun s' ↦ s'.reg .rdx = (bitLength (s.reg .rax).toNat).toUInt64 ∧ s'.mem = s.mem ∧
      RegsFrame [.rax, .rdx] s s') E := by
  unfold bitLen
  fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ d, t.reg .rdx = d.toUInt64 ∧
      d + bitLength (t.reg .rax).toNat = bitLength (s.reg .rax).toNat ∧ t.mem = s.mem ∧
      RegsFrame [.rax, .rdx] s t) (fun t ↦ (t.reg .rax).toNat)
  · exact ⟨0, by simp, by simp, rfl, by rf_tac⟩
  · intro t ⟨d, hd, hb, hm, hf⟩ hc
    have hne : t.reg .rax ≠ 0 := by simpa [Cond.eval, Rhs.eval, NativeVm.Field.int64Zero_toUInt64] using hc
    have hne' : (t.reg .rax).toNat ≠ 0 := fun h ↦ hne (UInt64.toNat_inj.mp (by simpa using h))
    have hs : ((t.reg .rax) >>> 1).toNat = (t.reg .rax).toNat / 2 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    fstep; fstep
    fdone
    refine ⟨⟨d + 1, by rw [hd, toUInt64_succ], ?_, hm, by rf_tac; exact hf⟩, ?_⟩
    · rw [← hb, bitLength_succ_div _ hne', hs]
      omega
    · rw [hs]
      omega
  · intro t ⟨d, hd, hb, hm, hf⟩ hc
    have h0 : t.reg .rax = 0 := by simpa [Cond.eval, Rhs.eval, NativeVm.Field.int64Zero_toUInt64] using hc
    fdone
    refine ⟨?_, hm, hf⟩
    rw [hd, ← hb, h0]
    simp [bitLength]

/-! ## Word arithmetic -/

theorem toUInt64_sub {a b : Nat} (ha : a < 2 ^ 64) (hb : b ≤ a) :
    a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  have hle : b.toUInt64 ≤ a.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, toNat_toUInt64 ha, toNat_toUInt64 (by omega)]; exact hb
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ hle, toNat_toUInt64 ha, toNat_toUInt64 (by omega),
    toNat_toUInt64 (by omega)]

/-- The key `κ · 256 + (255 - c)` as `kapC`'s caller computes it. -/
theorem key_u {k c : Nat} (hk : k ≤ 36) (hc : c < 158) :
    k.toUInt64 <<< (8 : UInt64) + 255 - c.toUInt64 = (k * 256 + (255 - c)).toUInt64 := by
  rw [show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, NativeVm.Transcript.toUInt64_shl _ _ (by omega),
    show (255 : UInt64) = (255 : Nat).toUInt64 from rfl, toUInt64_add,
    toUInt64_sub (by omega) (by omega)]
  congr 1
  omega

/-- `1 << (k & 63)` is `2^k`. -/
theorem pow_u {k : Nat} (hk : k < 64) : (1 : UInt64) <<< (k.toUInt64 &&& 63) = (2 ^ k).toUInt64 := by
  have : k.toUInt64 &&& 63 = k.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, toNat_toUInt64 (by omega), show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [this, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl,
    NativeVm.Transcript.toUInt64_shl _ _ hk, Nat.mul_one]

/-! ## `kapC` -/

/-- The layout's words `kapC` reads, at `p`: the memory's log-size (word `0`), the bytecode's
(word `1`), the heights (words `4 ..`), each at most `30`. -/
structure KapMem (mem : UInt64 → Option UInt64) (p : UInt64) (lm lb : Nat) (hs : Array Nat) :
    Prop where
  lmW : mem (wd p 0) = some lm.toUInt64
  lbW : mem (wd p 1) = some lb.toUInt64
  hsW : ∀ i < 6, mem (wd p (4 + i)) = some (hs.getD i 0).toUInt64
  lmB : lm ≤ 30
  lbB : lb ≤ 30
  hsB : ∀ i < 6, hs.getD i 0 ≤ 30

theorem KapMem.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {lm lb : Nat}
    {hs : Array Nat} (h : KapMem mem p lm lb hs) (hm : mem' = mem) : KapMem mem' p lm lb hs :=
  hm ▸ h

theorem kapF_le {lm lb : Nat} {hs : Array Nat} (hlm : lm ≤ 30) (hlb : lb ≤ 30)
    (hhs : ∀ i < 6, hs.getD i 0 ≤ 30) (c : Nat) : kapF lm lb hs c ≤ 36 := by
  have := hhs 0 (by omega); have := hhs 1 (by omega); have := hhs 2 (by omega)
  have := hhs 3 (by omega); have := hhs 4 (by omega); have := hhs 5 (by omega)
  unfold kapF
  split_ifs <;> omega

theorem KapMem.kap_le {mem : UInt64 → Option UInt64} {p : UInt64} {lm lb : Nat} {hs : Array Nat}
    (h : KapMem mem p lm lb hs) (c : Nat) : kapF lm lb hs c ≤ 36 :=
  kapF_le h.lmB h.lbB h.hsB c

/-- `rax := κ(rsi)`, the log-size of the global column `rsi`. -/
def kapC : Stmt :=
  .ite (.cmp .ltu .rsi (.imm 3)) (I (.load .rax (L 0)))
  (.ite (.cmp .eq .rsi (.imm 3)) (I (.load .rax (L 1)))
  (.ite (.cmp .eq .rsi (.imm 4)) (blk [I (.load .rax (L 9)), I (.addi .rax 6)])
  (.ite (.cmp .ltu .rsi (.imm 18)) (I (.load .rax (L 4)))
  (.ite (.cmp .ltu .rsi (.imm 31)) (I (.load .rax (L 5)))
  (.ite (.cmp .ltu .rsi (.imm 38)) (I (.load .rax (L 6)))
  (.ite (.cmp .ltu .rsi (.imm 52)) (I (.load .rax (L 7)))
  (.ite (.cmp .ltu .rsi (.imm 66)) (I (.load .rax (L 8))) (I (.load .rax (L 9))))))))))

theorem wp_loadL {p : UInt64} {k v : Nat} (hr : s.reg .r14 = p) (hv : s.mem (wd p k) = some v.toUInt64) :
    WP (I (.load .rax (L k))) s
      (fun s' ↦ s'.reg .rax = v.toUInt64 ∧ s'.mem = s.mem ∧ RegsFrame [.rax] s s') E :=
  WP.ins (s' := s.setReg .rax v.toUInt64) (by simp [QInstr.step, eval_L hr, hv])
    ⟨by simp, rfl, by rf_tac⟩

theorem kapC_spec {p : UInt64} {lm lb c : Nat} {hs : Array Nat} (hr : s.reg .r14 = p)
    (hm : KapMem s.mem p lm lb hs) (hc : c < 2 ^ 64) (hrsi : s.reg .rsi = c.toUInt64) :
    WP kapC s (fun s' ↦ s'.reg .rax = (kapF lm lb hs c).toUInt64 ∧ s'.mem = s.mem ∧
      RegsFrame [.rax] s s') E := by
  unfold kapC kapF
  refine wp_ite_of (cmp_ltu_imm 3 hc (by omega) hrsi) (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [decide_eq_true_eq] at h; simp only [h, ↓reduceIte]
    exact wp_loadL hr hm.lmW
  simp only [decide_eq_false_iff_not] at h; simp only [h, ↓reduceIte]
  refine wp_ite_of (cmp_eq_imm 3 hc (by omega) hrsi) (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [decide_eq_true_eq] at h; simp only [h, ↓reduceIte]
    exact wp_loadL hr hm.lbW
  simp only [decide_eq_false_iff_not] at h; simp only [h, ↓reduceIte]
  refine wp_ite_of (cmp_eq_imm 4 hc (by omega) hrsi) (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [decide_eq_true_eq] at h; simp only [h, ↓reduceIte]
    refine NativeVm.Transcript.wp_load (eval_L hr 9) (hm.hsW 5 (by omega)) ?_
    fstep
    fdone
    refine ⟨?_, trivial, by rf_tac⟩
    rw [show (6 : UInt64) = (6 : Nat).toUInt64 from rfl, toUInt64_add]
  simp only [decide_eq_false_iff_not] at h; simp only [h, ↓reduceIte]
  refine wp_ite_of (cmp_ltu_imm 18 hc (by omega) hrsi) (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [decide_eq_true_eq] at h; simp only [h, ↓reduceIte]
    exact wp_loadL hr (hm.hsW 0 (by omega))
  simp only [decide_eq_false_iff_not] at h; simp only [h, ↓reduceIte]
  refine wp_ite_of (cmp_ltu_imm 31 hc (by omega) hrsi) (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [decide_eq_true_eq] at h; simp only [h, ↓reduceIte]
    exact wp_loadL hr (hm.hsW 1 (by omega))
  simp only [decide_eq_false_iff_not] at h; simp only [h, ↓reduceIte]
  refine wp_ite_of (cmp_ltu_imm 38 hc (by omega) hrsi) (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [decide_eq_true_eq] at h; simp only [h, ↓reduceIte]
    exact wp_loadL hr (hm.hsW 2 (by omega))
  simp only [decide_eq_false_iff_not] at h; simp only [h, ↓reduceIte]
  refine wp_ite_of (cmp_ltu_imm 52 hc (by omega) hrsi) (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [decide_eq_true_eq] at h; simp only [h, ↓reduceIte]
    exact wp_loadL hr (hm.hsW 3 (by omega))
  simp only [decide_eq_false_iff_not] at h; simp only [h, ↓reduceIte]
  refine wp_ite_of (cmp_ltu_imm 66 hc (by omega) hrsi) (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [decide_eq_true_eq] at h; simp only [h, ↓reduceIte]
    exact wp_loadL hr (hm.hsW 4 (by omega))
  simp only [decide_eq_false_iff_not] at h; simp only [h, ↓reduceIte]
  exact wp_loadL hr (hm.hsW 5 (by omega))

/-! ## `blockFlag` -/

/-- `rdx := 1` if the global column `rsi` is stacked, else `0`. -/
def blockFlag : Stmt := blk [I (.movi .rdx 1),
  .ite (.cmp .ltu .rsi (.imm 66)) .skip (.ite (.cmp .eq .rsi (.imm 80)) .skip
    (.ite (.cmp .geu .rsi (.imm 131)) .skip (I (.movi .rdx 0))))]

theorem blockFlag_spec {c : Nat} (hc : c < 2 ^ 64) (hrsi : s.reg .rsi = c.toUInt64) :
    WP blockFlag s (fun s' ↦ s'.reg .rdx = (if isBlockF c then 1 else 0) ∧ s'.mem = s.mem ∧
      RegsFrame [.rdx] s s') E := by
  unfold blockFlag
  fstep
  have hrsi' : (s.setReg .rdx 1).reg .rsi = c.toUInt64 := by rsimp; exact hrsi
  have hb : isBlockF c = (decide (c < 66) || decide (c = 80) || decide (131 ≤ c)) := rfl
  refine wp_ite_of (cmp_ltu_imm 66 hc (by omega) hrsi') (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [decide_eq_true_eq] at h
    refine WP.skip ⟨?_, rfl, by rf_tac⟩
    simp [hb, h]
  simp only [decide_eq_false_iff_not] at h
  refine wp_ite_of (cmp_eq_imm 80 hc (by omega) hrsi') (fun h' ↦ ?_) (fun h' ↦ ?_)
  · simp only [decide_eq_true_eq] at h'
    refine WP.skip ⟨?_, rfl, by rf_tac⟩
    subst h'; rfl
  simp only [decide_eq_false_iff_not] at h'
  refine wp_ite_of (cmp_geu_imm 131 hc (by omega) hrsi') (fun h'' ↦ ?_) (fun h'' ↦ ?_)
  · simp only [decide_eq_true_eq] at h''
    refine WP.skip ⟨?_, rfl, by rf_tac⟩
    simp [hb, h'']
  simp only [decide_eq_false_iff_not] at h''
  refine WP.ins (s' := (s.setReg .rdx 1).setReg .rdx 0) rfl ⟨?_, rfl, by rf_tac⟩
  simp [hb, h, h', h'']

/-! ## `sumC` -/

/-- `r10 += 2^rax`. -/
def addC : Stmt := blk [I (.mov .rcx .rax), I (.movi .r11 1), I (.shlcl .r11), I (.add .r10 .r11)]

/-- One column of `sumC`. -/
def sumBody : Stmt := blk [blockFlag,
  .ite (.cmp .eq .rdx (.imm 1)) (blk [kapC, I (.mov .r9 .rax), I (.shli .r9 8), I (.addi .r9 255),
      I (.sub .r9 .rsi), .ite (.cmp .ltu .r8 (.reg .r9)) addC .skip]) .skip,
  I (.addi .rsi 1)]

/-- `r10 := sumF κ r8`. -/
def sumC : Stmt := blk [I (.movi .r10 0), I (.movi .rsi 0), .loop (.cmp .ltu .rsi (.imm 158)) sumBody]

/-- The registers `sumC` writes. -/
abbrev sumRegs : List Reg64 := [.rax, .rcx, .rdx, .rsi, .r9, .r10, .r11]

theorem sumBody_spec {p : UInt64} {lm lb j acc kr : Nat} {hs : Array Nat} (hr : s.reg .r14 = p)
    (hm : KapMem s.mem p lm lb hs) (hj : j < 158) (hrsi : s.reg .rsi = j.toUInt64)
    (hacc : s.reg .r10 = acc.toUInt64) (hkr : kr < 2 ^ 64) (hr8 : s.reg .r8 = kr.toUInt64) :
    WP sumBody s (fun s' ↦ s'.reg .rsi = (j + 1).toUInt64 ∧
      s'.reg .r10 = (sumStep (kapF lm lb hs) kr acc j).toUInt64 ∧ s'.mem = s.mem ∧
      RegsFrame sumRegs s s') E := by
  unfold sumBody
  refine NativeVm.Transcript.wp_then (blockFlag_spec (by omega) hrsi) fun s₁ ⟨h1, m1, f1⟩ ↦ ?_
  have hrdx : (Cond.cmp .eq .rdx (.imm 1)).eval s₁ = isBlockF j := by
    simp only [Cond.eval, Rhs.eval, h1]
    cases isBlockF j <;> rfl
  have k1 := hm.kap_le j
  apply WP.blk_cons
  refine wp_ite_of hrdx (fun hb ↦ ?_) (fun hb ↦ ?_)
  · have hr1 : s₁.reg .r14 = p := by rw [f1 _ (by simp)]; exact hr
    have hrsi1 : s₁.reg .rsi = j.toUInt64 := by rw [f1 _ (by simp)]; exact hrsi
    refine NativeVm.Transcript.wp_then (kapC_spec hr1 (hm.congr m1) (by omega) hrsi1)
      fun s₂ ⟨h2, m2, f2⟩ ↦ ?_
    have hrsi2 : s₂.reg .rsi = j.toUInt64 := by rw [f2 _ (by simp)]; exact hrsi1
    have hr82 : s₂.reg .r8 = kr.toUInt64 := by
      rw [f2 _ (by simp), f1 _ (by simp)]; exact hr8
    fstep; fstep; fstep; fstep
    rw [h2, hrsi2, key_u k1 hj]
    apply WP.blk_cons
    refine wp_ite_of (cmp_ltu_reg (b := kapF lm lb hs j * 256 + (255 - j)) hkr (by omega)
      (by rsimp; exact hr82) (by rsimp))
      (fun hk ↦ ?_) (fun hk ↦ ?_)
    · simp only [decide_eq_true_eq] at hk
      unfold addC
      fstep; fstep; fstep; fstep
      fdone; fdone
      fstep
      fdone
      refine ⟨by rw [hrsi2, toUInt64_succ], ?_, by rw [m2, m1],
        rf_trans (l'' := sumRegs) f1
        (rf_trans (l'' := sumRegs) f2 (show RegsFrame sumRegs _ _ by rf_tac))⟩
      rw [h2, pow_u (by omega), f2 _ (by simp), f1 _ (by simp), hacc, toUInt64_add, sumStep,
        keyF, hb, Bool.true_and, decide_eq_true hk]
      rfl
    · simp only [decide_eq_false_iff_not] at hk
      refine WP.skip ?_
      fdone
      fstep
      fdone
      refine ⟨by rw [hrsi2, toUInt64_succ], ?_, by rw [m2, m1],
        rf_trans (l'' := sumRegs) f1
        (rf_trans (l'' := sumRegs) f2 (show RegsFrame sumRegs _ _ by rf_tac))⟩
      rw [f2 _ (by simp), f1 _ (by simp), hacc, sumStep, keyF, hb, Bool.true_and,
        decide_eq_false hk]
      rfl
  · refine WP.skip ?_
    fstep
    fdone
    refine ⟨by rw [f1 _ (by simp), hrsi, toUInt64_succ], ?_, m1, rf_trans (l'' := sumRegs) f1
      (show RegsFrame sumRegs _ _ by rf_tac)⟩
    rw [f1 _ (by simp), hacc, sumStep, hb, Bool.false_and]
    rfl

theorem sumC_spec {p : UInt64} {lm lb kr : Nat} {hs : Array Nat} (hr : s.reg .r14 = p)
    (hm : KapMem s.mem p lm lb hs) (hkr : kr < 2 ^ 64) (hr8 : s.reg .r8 = kr.toUInt64) :
    WP sumC s (fun s' ↦ s'.reg .r10 = (sumF (kapF lm lb hs) kr).toUInt64 ∧ s'.mem = s.mem ∧
      RegsFrame sumRegs s s') E := by
  unfold sumC
  fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ j ≤ 158, t.reg .rsi = j.toUInt64 ∧
      t.reg .r10 = ((List.range j).foldl (sumStep (kapF lm lb hs) kr) 0).toUInt64 ∧
      t.mem = s.mem ∧ RegsFrame sumRegs s t) (fun t ↦ 158 - (t.reg .rsi).toNat)
  · exact ⟨0, by omega, by rsimp; rfl, by rsimp; rfl, rfl,
      show RegsFrame sumRegs _ _ by rf_tac⟩
  · intro t ⟨j, hj, hrsi, hacc, hm', hf⟩ hc
    have hc' : decide (j < 158) = true := (cmp_ltu_imm 158 (by omega) (by omega) hrsi).symm.trans hc
    rw [decide_eq_true_eq] at hc'
    refine WP.mono (sumBody_spec (hr.symm ▸ hf _ (by simp)) (hm.congr hm') hc' hrsi hacc hkr
      (by rw [hf _ (by simp)]; exact hr8)) (fun t' ⟨h1, h2, h3, h4⟩ ↦ ?_) (fun _ h ↦ h)
    refine ⟨⟨j + 1, hc', h1, ?_, h3.trans hm', rf_trans (l'' := sumRegs) hf h4⟩, ?_⟩
    · rw [h2, List.range_succ, List.foldl_append]; rfl
    · rw [h1, hrsi, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]; omega
  · intro t ⟨j, hj, hrsi, hacc, hm', hf⟩ hc
    have hc' : decide (j < 158) = false := (cmp_ltu_imm 158 (by omega) (by omega) hrsi).symm.trans hc
    rw [decide_eq_false_iff_not] at hc'
    have : j = 158 := by omega
    subst this
    unfold sumF
    exact WP.blk_nil ⟨hacc, hm', hf⟩

/-- A word below `2^44` of `sumF`, every `κ` at most `36`. -/
theorem sumF_lt {κ : Nat → Nat} (hκ : ∀ c, κ c ≤ 36) (kr : Nat) : sumF κ kr < 2 ^ 44 := by
  have : ∀ n, (List.range n).foldl (sumStep κ kr) 0 ≤ n * 2 ^ 36 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sumStep]
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) (hκ n)
      rw [Nat.succ_mul]
      generalize 2 ^ 36 = B at *
      split <;> omega
  have h := this 158
  unfold sumF
  have : 158 * 2 ^ 36 < 2 ^ 44 := by norm_num
  omega

end NativeVm.Code.Phase1
