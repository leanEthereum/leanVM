module

public import X86.Keccak.Absorb

/-!
# `Keccak.hash`'s proof: the last block

The loop over the remaining words (`tail_spec`), which XORs the words of the last block into the
lanes, and the padding (`pad_spec`), which XORs `PAD_FIRST` after the last byte and `PAD_LAST`
into the block's last byte.
-/

@[expose] public section

namespace X86.Keccak.Proof

open LeanVM.Semantics LeanVM.Protocol.KeccakHash

variable {E : QState → Prop}

/-! ## The remaining words -/

/-- The loop over the remaining words, `rcx` their byte offset. -/
def tailLoop : Stmt := .loop (.cmp .ltu .rcx (.reg .rbx)) (blk [
    I (.load .rax { base := .rsi, idx := some (.rcx, .W8) }),
    I (.load .r8 { base := .rdi, idx := some (.rcx, .W8), disp := sA }),
    I (.xor .r8 .rax),
    I (.store { base := .rdi, idx := some (.rcx, .W8), disp := sA } .r8),
    I (.addi .rcx 8)])

/-- The lanes `A` with the remaining words XORed into lanes `0, …, t - 1`. -/
def tailLanes (ws : List UInt64) (len : Nat) (A : KeccakState) (t i : Nat) : UInt64 :=
  if i < t then Keccak.lane A i ^^^ ws.getD (17 * (len / 136) + i) 0 else Keccak.lane A i

/-- After `t` remaining words. -/
def TailInv (s0 : QState) (ws : List UInt64) (len : Nat) (A : KeccakState) (s : QState) : Prop :=
  ∃ t, 8 * t < len % 136 + 8 ∧ s.reg .rcx = (8 * t).toUInt64 ∧
    s.reg .rsi = s0.reg .rsi + (136 * (len / 136)).toUInt64 ∧
    s.reg .rbx = (len % 136).toUInt64 ∧ Run s0 s ∧
    Words s.mem (s0.reg .rdi) 0 25 (tailLanes ws len A t)

/-- **The remaining words**, XORed into the lanes. -/
theorem tail_spec {s0 s : QState} {ws : List UInt64} {len : Nat} {A : KeccakState}
    (hb : HoldsBytes ws len) (hin : WordsAt s0.mem (s0.reg .rsi) ws)
    (hdisj : ∀ i < ws.length, ∀ k < scratchWords,
      s0.reg .rsi + (8 * i).toUInt64 ≠ scratchAddr (s0.reg .rdi) k)
    (h0 : TailInv s0 ws len A s) :
    WP tailLoop s (fun s' ↦ s'.reg .rbx = (len % 136).toUInt64 ∧ Run s0 s' ∧
      Words s'.mem (s0.reg .rdi) 0 25
        (fun i ↦ Keccak.lane A i ^^^ ws.getD (17 * (len / 136) + i) 0)) E := by
  refine WP.loop (TailInv s0 ws len A) (fun s ↦ (s.reg .rbx).toNat - (s.reg .rcx).toNat) h0
    ?_ ?_
  · rintro s ⟨t, ht, hrcx, hrsi, hrbx, hrun, hW⟩ hc
    have hc' : 8 * t < len % 136 := by
      simp only [Cond.eval, Rhs.eval, hrcx, hrbx, decide_eq_true_eq] at hc
      rwa [UInt64.lt_iff_toNat_lt, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at hc
    have hlen := hb.1
    have hrdi := hrun.rdi
    have hWt : s.mem (scratchAddr (s0.reg .rdi) t) = some (Keccak.lane A t) := by
      simpa [tailLanes] using hW t (by omega)
    have haddr : { base := .rdi, idx := some (.rcx, .W8), disp := sA : Addr }.eval s =
        scratchAddr (s0.reg .rdi) t := by
      simp only [Addr.eval, hrdi, hrcx, Width.bytes, scratchAddr, sA]
      uarith
    refine wp_load (a := s0.reg .rsi + (8 * (17 * (len / 136) + t)).toUInt64) ?_
      (hrun.input hin hdisj (by omega)) ?_
    · simp only [Addr.eval, hrsi, hrcx, Width.bytes]
      uarith
    refine wp_load (a := scratchAddr (s0.reg .rdi) t) haddr hWt ?_
    refine wp_op rfl ?_
    refine wp_store (a := scratchAddr (s0.reg .rdi) t) haddr (by simp [hWt]) ?_
    refine wp_op rfl (WP.blk_nil ⟨⟨t + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    · simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ↓reduceIte, hrcx]
      uarith
    · simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ↓reduceIte, hrsi]
    · simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ↓reduceIte, hrbx]
    · exact (((((hrun.setReg (by simp) _).setReg (by simp) _).setReg (by simp) _).setMem
        (by omega) _).setReg (by simp) _)
    · intro i hi
      simp only [QState.setReg_mem, QState.setMem_mem, QState.setReg_reg, reduceCtorEq,
        ↓reduceIte, Nat.zero_add]
      by_cases e : i = t
      · subst e
        simp [tailLanes]
      · rw [ite_eq_right (fun h ↦ e (scratchAddr_inj (by omega) (by omega) h))]
        have := hW i hi
        simp only [Nat.zero_add, tailLanes] at this ⊢
        rw [this]
        by_cases h : i < t
        · simp [h, show i < t + 1 by omega]
        · simp [h, show ¬ i < t + 1 by omega]
    · simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ↓reduceIte, hrcx, hrbx]
      rw [show (8 * t).toUInt64 + Int64.toUInt64 8 = (8 * (t + 1)).toUInt64 by uarith,
        toNat_toUInt64 (by omega), toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · rintro s ⟨t, ht, hrcx, hrsi, hrbx, hrun, hW⟩ hc
    have hc' : len % 136 ≤ 8 * t := by
      simp only [Cond.eval, Rhs.eval, hrcx, hrbx, decide_eq_false_iff_not] at hc
      rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at hc
      omega
    refine ⟨hrbx, hrun, fun i hi ↦ ?_⟩
    rw [hW i hi]
    beta_reduce
    rw [tailLanes]
    split
    · rfl
    · rw [getD_words_of_le hb (show len ≤ 8 * (17 * (len / 136) + i) by omega), UInt64.xor_zero]

/-! ## The padding -/

/-- `PAD_FIRST` after the last byte: lane `rbx / 8` XOR `1 << 8 (rbx % 8)`. -/
def padP1 : List Stmt := [
  I (.mov .rcx .rbx), I (.andi .rcx 7), I (.shli .rcx 3),
  I (.movi .rax 1), I (.shlcl .rax),
  I (.mov .rdx .rbx), I (.andi .rdx (-8)),
  I (.load .r8 { base := .rdi, idx := some (.rdx, .W8), disp := sA }),
  I (.xor .r8 .rax),
  I (.store { base := .rdi, idx := some (.rdx, .W8), disp := sA } .r8)]

/-- `PAD_LAST` in the block's last byte: lane `16` XOR `0x80 << 56`. -/
def padP2 : List Stmt := [
  I (.movi .rax (-0x8000000000000000)),
  I (.load .r8 (atDi (sA + 128))), I (.xor .r8 .rax), I (.store (atDi (sA + 128)) .r8)]

/-- The lane holding byte `r`: `r & -8` is `8 (r / 8)`. -/
theorem pad_rdx : ∀ r < 136, (r.toUInt64 &&& (-8 : Int64).toUInt64) = (8 * (r / 8)).toUInt64 := by
  decide +kernel

/-- The word of `PAD_FIRST` in its lane: `1 << ((r & 7) << 3)` is `1 << 8 (r % 8)`. -/
theorem pad_rax : ∀ r < 136, (1 : Int64).toUInt64 <<<
    (((r.toUInt64 &&& (7 : Int64).toUInt64) <<< (3 : Nat).toUInt64) &&& 63) =
      (1 : UInt64) <<< (8 * (r % 8)).toUInt64 := by
  decide +kernel

theorem pad_last : (-0x8000000000000000 : Int64).toUInt64 = 0x8000000000000000 := by decide

theorem setMem_mem' (s : QState) (a v : UInt64) :
    (s.setMem a v).mem = Function.update s.mem a (some v) := (rfl)

theorem pad1_spec {base : UInt64} {r : Nat} (hr : r < 136) {s : QState} {l : UInt64}
    (hrdi : s.reg .rdi = base) (hrbx : s.reg .rbx = r.toUInt64)
    (hl : s.mem (scratchAddr base (r / 8)) = some l) :
    WP (blk padP1) s (fun s' ↦ s'.mem = Function.update s.mem (scratchAddr base (r / 8))
      (some (l ^^^ (1 <<< (8 * (r % 8)).toUInt64))) ∧
      RegsFrame [.rax, .rcx, .rdx, .r8] s s') E := by
  refine wp_op rfl (wp_op rfl (wp_op rfl (wp_op rfl (wp_op rfl (wp_op rfl (wp_op rfl ?_))))))
  refine wp_load (a := scratchAddr base (r / 8)) ?_ hl ?_
  · simp only [Addr.eval, QState.setReg_reg, reduceCtorEq, ↓reduceIte, hrdi, hrbx, Width.bytes]
    rw [pad_rdx r hr]
    simp only [scratchAddr, sA]
    uarith
  refine wp_op rfl ?_
  refine wp_store (a := scratchAddr base (r / 8)) ?_ (by simp [hl]) ?_
  · simp only [Addr.eval, QState.setReg_reg, reduceCtorEq, ↓reduceIte, hrdi, hrbx, Width.bytes]
    rw [pad_rdx r hr]
    simp only [scratchAddr, sA]
    uarith
  refine WP.blk_nil ⟨?_, ?_⟩
  · rw [setMem_mem']
    simp only [QState.setReg_mem, QState.setReg_reg, reduceCtorEq, ↓reduceIte, hrbx]
    rw [pad_rax r hr]
  · intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp [hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2]

theorem pad2_spec {base : UInt64} {s : QState} {v : UInt64} (hrdi : s.reg .rdi = base)
    (hv : s.mem (scratchAddr base 16) = some v) :
    WP (blk padP2) s (fun s' ↦ s'.mem = Function.update s.mem (scratchAddr base 16)
      (some (v ^^^ 0x8000000000000000)) ∧ RegsFrame [.rax, .r8] s s') E := by
  refine wp_op rfl ?_
  refine wp_load_scr (k := 16) (by simp [hrdi]) (by decide) hv ?_
  refine wp_op rfl ?_
  refine wp_store_scr (base := base) (k := 16) (by simp [hrdi]) (by decide)
    (by simp only [QState.setReg_mem, hv]; rfl) ?_
  refine WP.blk_nil ⟨?_, fun r hr ↦ regs_rax_r8 hr fun r h1 h2 ↦ by simp [h1, h2]⟩
  rw [setMem_mem']
  simp only [QState.setReg_mem, QState.setReg_reg, reduceCtorEq, ↓reduceIte, pad_last]

/-- **The padding**: lane `r / 8` XOR `PAD_FIRST`'s word, lane `16` XOR `PAD_LAST`'s. -/
theorem pad_spec {base : UInt64} {r : Nat} (hr : r < 136) {f : Nat → UInt64} {s : QState}
    (hrdi : s.reg .rdi = base) (hrbx : s.reg .rbx = r.toUInt64) (hok : ScrOk s.mem base)
    (hW : Words s.mem base 0 25 f) :
    WP (blk (padP1 ++ padP2)) s (fun s' ↦ ScrOk s'.mem base ∧
      RegsFrame [.rax, .rcx, .rdx, .r8] s s' ∧ ScrFrame base 0 84 s.mem s'.mem ∧
      Words s'.mem base 0 25 (fun i ↦ f i ^^^
        (if i = r / 8 then 1 <<< (8 * (r % 8)).toUInt64 else 0) ^^^
        (if i = 16 then 0x8000000000000000 else 0))) E := by
  have hW' : ∀ i < 25, s.mem (scratchAddr base i) = some (f i) := fun i hi ↦ by
    simpa using hW i hi
  refine wp_blk_append (WP.mono (pad1_spec hr hrdi hrbx (hW' _ (by omega))) ?_ (fun _ h ↦ h))
  rintro s1 ⟨hm1, hR1⟩
  have hv : s1.mem (scratchAddr base 16) =
      some (if r / 8 = 16 then f 16 ^^^ (1 <<< (8 * (r % 8)).toUInt64) else f 16) := by
    rw [hm1]
    by_cases h : r / 8 = 16
    · rw [h]
      simp
    · rw [Function.update_of_ne (scratchAddr_ne (by omega) (by omega) (Ne.symm h)), hW' 16
        (by omega), ite_eq_right h]
  refine WP.mono (pad2_spec ((hR1 _ (by simp)).trans hrdi) hv) ?_ (fun _ h ↦ h)
  rintro s2 ⟨hm2, hR2⟩
  refine ⟨?_, RegsFrame.trans hR1 (RegsFrame.mono hR2 (by simp)), ?_, fun i hi ↦ ?_⟩
  · rw [hm2, hm1]
    exact (hok.update _ _).update _ _
  · rw [hm2, hm1]
    exact (ScrFrame.update (k := r / 8) (by omega) (by omega)).trans
      (ScrFrame.update (k := 16) (by omega) (by omega)) le_rfl le_rfl
  · rw [hm2, hm1, Nat.zero_add]
    by_cases h16 : i = 16
    · subst h16
      by_cases h : r / 8 = 16
      · simp [h]
      · simp [h, Ne.symm h]
    · rw [Function.update_of_ne (scratchAddr_ne (by omega) (by omega) h16)]
      by_cases h : i = r / 8
      · subst h
        simp [h16]
      · rw [Function.update_of_ne (scratchAddr_ne (by omega) (by omega) h), hW' i hi]
        simp [h, h16]

end X86.Keccak.Proof
