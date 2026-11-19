module

public import X86.Keccak.Permute
public import X86.Keccak.Lanes

/-!
# `Keccak.hash`'s proof: zeroing and the whole blocks

What a run of `Keccak.hash` keeps (`Run`); the zeroing of the lanes (`zero_spec`); `xorBlock`,
which XORs seventeen words into the rate (`xorBlock_spec`); and the loop over the whole blocks
(`absorb_spec`), whose invariant `BlockInv` says that what is left to absorb from the lanes gives
`keccak256`'s final state.
-/

@[expose] public section

namespace X86.Keccak.Proof

open LeanVM.Semantics LeanVM.Protocol.KeccakHash

variable {E : QState → Prop}

/-- Arithmetic on addresses: `Nat.toUInt64` of sums and products, as a commutative ring. -/
macro "uarith" : tactic => `(tactic| (
  open scoped UInt64.CommRing in
  (simp only [Nat.toUInt64_eq, UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.reduceOfNat, i64_lit,
    Int64.toUInt64_add, Int64.toUInt64_mul, Int64.toUInt64_ofNat'] <;> ring)))

/-! ## What a run keeps -/

/-- The registers `Keccak.hash` writes. -/
abbrev hashRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .rsi, .r8]

/-- What a run of `Keccak.hash` from `s0` keeps at `s`: every scratch word, the registers but
`hashRegs`, the words outside the scratch area. -/
structure Run (s0 s : QState) : Prop where
  ok : ScrOk s.mem (s0.reg .rdi)
  regs : RegsFrame hashRegs s0 s
  frame : ScrFrame (s0.reg .rdi) 0 84 s0.mem s.mem

theorem Run.rdi {s0 s : QState} (h : Run s0 s) : s.reg .rdi = s0.reg .rdi := h.regs _ (by simp)

theorem Run.next {s0 s s' : QState} (h : Run s0 s) {rs : List Reg64} (hR : RegsFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∈ hashRegs) (hF : ScrFrame (s0.reg .rdi) 0 84 s.mem s'.mem)
    (hok : ScrOk s'.mem (s0.reg .rdi)) : Run s0 s' :=
  ⟨hok, RegsFrame.trans h.regs (RegsFrame.mono hR hrs), h.frame.trans hF le_rfl le_rfl⟩

theorem Run.setReg {s0 s : QState} (h : Run s0 s) {r : Reg64} (hr : r ∈ hashRegs) (v : UInt64) :
    Run s0 (s.setReg r v) := ⟨h.ok, RegsFrame.setReg h.regs hr v, h.frame⟩

theorem Run.setMem {s0 s : QState} (h : Run s0 s) {k : Nat} (hk : k < 84) (v : UInt64) :
    Run s0 (s.setMem (scratchAddr (s0.reg .rdi) k) v) :=
  ⟨h.ok.update _ _, h.regs,
    h.frame.trans (ScrFrame.update (k := k) (Nat.zero_le _) hk) le_rfl le_rfl⟩

/-- An input word, read during a run. -/
theorem Run.input {s0 s : QState} {ws : List UInt64} (h : Run s0 s)
    (hin : WordsAt s0.mem (s0.reg .rsi) ws)
    (hdisj : ∀ i < ws.length, ∀ k < scratchWords,
      s0.reg .rsi + (8 * i).toUInt64 ≠ scratchAddr (s0.reg .rdi) k)
    {i : Nat} (hi : i < ws.length) :
    s.mem (s0.reg .rsi + (8 * i).toUInt64) = some (ws.getD i 0) := by
  rw [h.frame _ fun k _ hk ↦ hdisj i hi k hk, hin i hi]
  simp [hi]

/-! ## Zeroing the lanes -/

/-- A store of a constant to scratch word `k`. -/
theorem wp_storei_scr {P : QState → Prop} {s : QState} {d c : Int64} {base : UInt64} {k : Nat}
    {rest : List Stmt} (hrdi : s.reg .rdi = base) (hd : d.toUInt64 = (8 * k).toUInt64)
    (hm : (s.mem (scratchAddr base k)).isSome)
    (h : WP (blk rest) (s.setMem (scratchAddr base k) c.toUInt64) P E) :
    WP (blk (I (.storei (at_ .rdi d) c) :: rest)) s P E := by
  apply WP.blk_cons
  apply WP.ins'
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hm
  have ha : (at_ .rdi d).eval s = scratchAddr base k := by rw [eval_at, hrdi, hd]; rfl
  simp only [QInstr.step, ha, hw, Option.map_some]
  exact h

theorem zero_spec {base : UInt64} {s : QState} (hrdi : s.reg .rdi = base)
    (hok : ScrOk s.mem base) :
    WP (blk ((List.range 25).map fun k ↦ I (.storei (atDi (sA + 8 * k.toInt64)) 0))) s
      (fun s' ↦ ScrOk s'.mem base ∧ RegsFrame [] s s' ∧ ScrFrame base 0 25 s.mem s'.mem ∧
        Words s'.mem base 0 25 (fun _ ↦ 0)) E := by
  rw [List.map_eq_flatMap]
  refine phase_run (fun k ↦ [I (.storei (atDi (sA + 8 * k.toInt64)) 0)]) 0 25 (fun _ ↦ 0) []
    (by omega) (by simp) (fun j hj s' h1 _ h3 _ ↦ ?_) hrdi hok
  refine wp_storei_scr (k := 0 + j) h1 (by addr_tac) (h3.isSome (by omega))
    (WP.blk_nil ⟨?_, fun _ _ ↦ rfl⟩)
  simp [QState.setMem]
  rfl

/-! ## One block -/

/-- `xorBlock`'s piece `k`. -/
def xbP (k : Nat) : List Stmt :=
  [I (.load .rax (at_ .rsi (8 * k.toInt64))), I (.load .r8 (atDi (sA + 8 * k.toInt64))),
    I (.xor .r8 .rax), I (.store (atDi (sA + 8 * k.toInt64)) .r8)]

theorem xorBlock_eq : xorBlock = blk ((List.range 17).flatMap xbP) := (rfl)

theorem xbP_spec {base a : UInt64} {k : Nat} {s : QState} {l g : UInt64}
    (hrdi : s.reg .rdi = base) (hrsi : s.reg .rsi = a)
    (hg : s.mem (a + (8 * k).toUInt64) = some g)
    (hl : s.mem (scratchAddr base (0 + k)) = some l) :
    WP (blk (xbP k)) s (fun s' ↦
      s'.mem = Function.update s.mem (scratchAddr base (0 + k)) (some (l ^^^ g)) ∧
      RegsFrame [.rax, .r8] s s') E := by
  refine wp_load (a := a + (8 * k).toUInt64) (by rw [eval_at, hrsi]; congr 1; addr_tac) hg ?_
  refine wp_load_scr (k := 0 + k) (by simp [hrdi]) (by addr_tac) hl ?_
  refine wp_op rfl ?_
  refine wp_store_scr (base := base) (k := 0 + k) (by simp [hrdi]) (by addr_tac)
    (by simp only [QState.setReg_mem, hl]; rfl) ?_
  refine WP.blk_nil ⟨?_, fun r hr ↦ regs_rax_r8 hr fun r h1 h2 ↦ by simp [h1, h2]⟩
  simp [QState.setMem]

/-- **One block**: the words `g 0, …, g 16` at `rsi` XORed into the rate. -/
theorem xorBlock_spec {base a : UInt64} {A : KeccakState} {g : Nat → UInt64} {s : QState}
    (hrdi : s.reg .rdi = base) (hrsi : s.reg .rsi = a) (hok : ScrOk s.mem base)
    (hA : Words s.mem base 0 25 (Keccak.lane A))
    (hin : ∀ k < 17, s.mem (a + (8 * k).toUInt64) = some (g k))
    (hdisj : ∀ k < 17, ∀ k' < 84, a + (8 * k).toUInt64 ≠ scratchAddr base k') :
    WP xorBlock s (fun s' ↦ ScrOk s'.mem base ∧ RegsFrame [.rax, .r8] s s' ∧
      ScrFrame base 0 84 s.mem s'.mem ∧ Words s'.mem base 0 25 (Keccak.lane (xorRate A g))) E := by
  rw [xorBlock_eq]
  refine WP.mono (phase_run xbP 0 17 (fun k ↦ Keccak.lane A k ^^^ g k) [.rax, .r8] (by omega)
    (by simp) (fun j hj s' h1 h2 h3 h4 ↦ xbP_spec h1 ((h4 _ (by simp)).trans hrsi)
      (by rw [h2 _ fun k _ hk ↦ hdisj j hj k (by omega)]; exact hin j hj)
      (by rw [h2.word (by omega) (by omega) (by omega)]; exact hA j (by omega))) hrdi hok) ?_
    (fun _ h ↦ h)
  rintro s' ⟨hok', hR', hF', hW'⟩
  refine ⟨hok', hR', hF'.widen le_rfl (by omega), fun t ht ↦ ?_⟩
  rw [lane_xorRate _ _ ht]
  split
  · exact hW' t ‹_›
  · rw [hF'.word (by omega) (by omega) (by omega)]
    exact hA t ht

/-! ## The whole blocks -/

theorem i64_136 : (136 : Int64).toUInt64 = (136 : Nat).toUInt64 := (rfl)

theorem toUInt64_sub {m n : Nat} (h : n ≤ m) (hm : m < 2 ^ 64) :
    m.toUInt64 - n.toUInt64 = (m - n).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [toNat_toUInt64 hm, toNat_toUInt64 (by omega)]; omega)),
    toNat_toUInt64 hm, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]

/-- The loop over the whole blocks. -/
def absorbLoop : Stmt := .loop (.cmp .geu .rbx (.imm 136)) (blk [
    xorBlock, permute, I (.addi .rsi 136), I (.subi .rbx 136)])

/-- After `j` blocks: `rsi` and `rbx` moved by `136 j`, and absorbing the rest of the held bytes
into the lanes gives `keccak256`'s final state. -/
def BlockInv (s0 : QState) (ws : List UInt64) (len : Nat) (s : QState) : Prop :=
  ∃ j A, 136 * j ≤ len ∧ s.reg .rsi = s0.reg .rsi + (136 * j).toUInt64 ∧
    s.reg .rbx = (len - 136 * j).toUInt64 ∧ Run s0 s ∧
    Words s.mem (s0.reg .rdi) 0 25 (Keccak.lane A) ∧
    absorbWith perm (len / 136 - j) A (((wordsBytes ws).take len).drop (136 * j)) =
      absorbWith perm (len / 136) (Vector.replicate 25 0) ((wordsBytes ws).take len)

/-- **The whole blocks**: the loop keeps `BlockInv` and leaves fewer than `136` bytes. -/
theorem absorb_spec {s0 s : QState} {ws : List UInt64} {len : Nat} (hb : HoldsBytes ws len)
    (hlen32 : len < 2 ^ 32) (hin : WordsAt s0.mem (s0.reg .rsi) ws)
    (hdisj : ∀ i < ws.length, ∀ k < scratchWords,
      s0.reg .rsi + (8 * i).toUInt64 ≠ scratchAddr (s0.reg .rdi) k)
    (h0 : BlockInv s0 ws len s) :
    WP absorbLoop s (fun s' ↦ BlockInv s0 ws len s' ∧ (s'.reg .rbx).toNat < 136) E := by
  refine WP.loop (BlockInv s0 ws len) (fun s ↦ (s.reg .rbx).toNat) h0 ?_ ?_
  · rintro s ⟨j, A, hj, hrsi, hrbx, hrun, hA, hab⟩ hc
    have hc' : 136 ≤ len - 136 * j := by
      simp only [Cond.eval, Rhs.eval, hrbx, decide_eq_true_eq, i64_136] at hc
      rwa [UInt64.le_iff_toNat_le, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at hc
    have haddr : ∀ k, s0.reg .rsi + (136 * j).toUInt64 + (8 * k).toUInt64 =
        s0.reg .rsi + (8 * (17 * j + k)).toUInt64 := fun k ↦ by uarith
    have hlen := hb.1
    apply WP.blk_cons
    refine WP.mono (xorBlock_spec (g := fun k ↦ ws.getD (17 * j + k) 0) hrun.rdi hrsi hrun.ok hA
      (fun k hk ↦ by rw [haddr]; exact hrun.input hin hdisj (by omega))
      (fun k hk k' hk' ↦ by rw [haddr]; exact hdisj _ (by omega) k' hk')) ?_ (fun _ h ↦ h)
    rintro s1 ⟨hok1, hR1, hF1, hA1⟩
    apply WP.blk_cons
    refine WP.mono (permute_spec ((hR1 _ (by simp)).trans hrun.rdi) hok1 hA1) ?_ (fun _ h ↦ h)
    rintro s2 ⟨hok2, hR2, hF2, hA2⟩
    have hrun2 : Run s0 s2 :=
      (hrun.next hR1 (by simp) (hF1.widen le_rfl le_rfl) hok1).next hR2 (by simp) hF2 hok2
    have hrsi2 : s2.reg .rsi = s0.reg .rsi + (136 * j).toUInt64 := by
      rw [hR2 _ (by simp), hR1 _ (by simp), hrsi]
    have hrbx2 : s2.reg .rbx = (len - 136 * j).toUInt64 := by
      rw [hR2 _ (by simp), hR1 _ (by simp), hrbx]
    refine wp_op rfl (wp_op rfl (WP.blk_nil ⟨⟨j + 1, keccakF1600
      (xorRate A fun k ↦ ws.getD (17 * j + k) 0), by omega, ?_, ?_,
      (hrun2.setReg (by simp) _).setReg (by simp) _, hA2, ?_⟩, ?_⟩))
    · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, hrsi2]
      uarith
    · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, hrbx2, i64_136]
      rw [toUInt64_sub hc' (by omega)]
      congr 1
    · rw [show len / 136 - j = len / 136 - (j + 1) + 1 by omega, absorbWith_succ,
        xorRate_congr A fun i hi ↦ lane_block hb j hi, List.drop_drop,
        show 136 * j + 136 = 136 * (j + 1) by omega] at hab
      exact hab
    · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, hrbx2, hrbx, i64_136]
      rw [toUInt64_sub hc' (by omega), toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro s hI hc
    refine ⟨hI, ?_⟩
    simp only [Cond.eval, Rhs.eval, decide_eq_false_iff_not, i64_136] at hc
    rw [UInt64.le_iff_toNat_le, toNat_toUInt64 (by omega)] at hc
    omega

end X86.Keccak.Proof
