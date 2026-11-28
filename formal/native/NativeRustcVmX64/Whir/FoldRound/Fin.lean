module

public import NativeRustcVmX64.Whir.FoldRound.Mid2

/-!
# `fold_round` on x86-64: the claim, the push, the output

`foldW_claim`: the folded claim as the code sums the products. `tail`: from `b18` with the
products, `b18` writes the claim and loads the `α`s' count (below `30`: no jump), `b19` pushes `α`,
bumps the count and writes `α`, `β` to the output, `b21` writes the tag `1` and returns; the state
is `foldW`'s (`WhirStateAt.fold`), the `TState` the round's.
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn miss_of_wr0)
open NativeRustcVm (WordAt EWAt EWsAt)

public section

/-- **The folded claim**, as the code sums the products. -/
theorem foldW_claim (w : WhirStateW) (s5 : TState) (u0 v c0 c1 : EW) :
    (foldW w u0 v c0 c1 (alA s5) (beA s5)).claim =
      ⟨u0.c0 ^^^ (p1 w s5 u0).c0 ^^^ (p3 s5 v).c0 ^^^ (p4 s5 c0).c0 ^^^ (p6 s5 c0 c1).c0,
        u0.c1 ^^^ (p1 w s5 u0).c1 ^^^ (p3 s5 v).c1 ^^^ (p4 s5 c0).c1 ^^^ (p6 s5 c0 c1).c1⟩ := by
  have e1 : alA s5 * (u0 + w.claim) = p1 w s5 u0 := by
    show EW.mul _ ⟨u0.c0 ^^^ w.claim.c0, u0.c1 ^^^ w.claim.c1⟩ = _
    rw [UInt64.xor_comm u0.c0, UInt64.xor_comm u0.c1]; rfl
  have e6 : alA s5 * beA s5 * (c0 + c1) = p6 s5 c0 c1 := by
    show EW.mul _ ⟨c0.c0 ^^^ c1.c0, c0.c1 ^^^ c1.c1⟩ = _
    rw [UInt64.xor_comm c0.c0, UInt64.xor_comm c0.c1]; rfl
  simp only [foldW]
  rw [e1, e6]
  rfl

theorem xor_lc (a b c : UInt64) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← UInt64.xor_assoc, UInt64.xor_comm a b, UInt64.xor_assoc]

/-- The code's order of the claim's sum. -/
theorem xor5 (a b c d e : UInt64) : (e ^^^ a) ^^^ ((d ^^^ c) ^^^ b) = a ^^^ b ^^^ c ^^^ d ^^^ e := by
  simp only [UInt64.xor_comm, xor_lc]

/-- A word kept across a change missing its bytes. -/
theorem wkeep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : SameOutside d d' R) {b : BitVec 64}
    {o : Nat} (hR : ∀ i < 8, ¬ R (off b (o + i))) {v : UInt64} (h : WordAt d (off b o) v) :
    WordAt d' (off b o) v := fun i hi ↦ by
  have hi' : i < 8 := by rw [NativeRustcVm.length_wordBytes] at hi; exact hi
  rw [off_add, hs _ (hR i hi'), ← off_add]
  exact h i hi

/-- An element kept across a change missing its bytes. -/
theorem ekeep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : SameOutside d d' R) {b : BitVec 64}
    {o : Nat} (hR : ∀ i < 16, ¬ R (off b (o + i))) {x : EW} (h : EWAt d (off b o) x) :
    EWAt d' (off b o) x := by
  rw [ewAt_iff, off_off] at h ⊢
  exact ⟨wkeep hs (fun i hi ↦ hR i (by omega)) h.1,
    wkeep hs (fun i hi ↦ by rw [Nat.add_assoc]; exact hR (8 + i) (by omega)) h.2⟩

theorem in_off {b : BitVec 64} {N o n j : Nat} (hN : b.toNat + N ≤ 2 ^ 64) (hj : j < N)
    (hle : o + n ≤ N) : InRange (off b o) n (off b j) ↔ o ≤ j ∧ j < o + n :=
  inRange_off_iff (by omega) (by omega)

/-- The `α`s' count's test: no jump below `30`. -/
theorem cnt_test [Labels] (env : Env) {c : Nat} (hc : c < 30)
    (hl : env.load 1 16 8 = BitVec.ofNat 64 c) :
    (SBool.and (.not (.cmp .ult .W64 (.load 1 16 8) (.lit 29)))
      (.not (.cmp .eq .W64 (.load 1 16 8) (.lit 29)))).eval env = false := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hl]
  rcases Nat.lt_or_ge c 29 with h | h
  · have : (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 29) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    simp [this]
  · have : c = 29 := by omega
    subst this
    simp

/-- Bytes of `b` from `n` on are not its first `n`. -/
theorem not_lo {b : BitVec 64} {N x n : Nat} (hN : b.toNat + N ≤ 2 ^ 64) (hx : n ≤ x) (hxN : x < N)
    (hn : n ≤ N) : ¬ InRange b n (off b x) := fun hq ↦ by
  have := (in_off (o := 0) (n := n) hN hxN (by omega)).mp (by rwa [off_zero])
  omega

section
variable [Labels] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- The state's bytes are not the output's. -/
theorem p_not_o (h : FoldRoundPre a s0 w m0) {j : Nat} (hj : j < stateBytes) :
    ¬ InRange (oA m0) 40 (off (pA m0) j) := fun hq ↦
  not_inRange_of_apart (Transcript.Apart.symm' (pre_op h)) (pre_p h).2.1 (pre_o h).2.1
    (inRange_off_self hj (by have : stateBytes = 61152 := rfl; omega)) hq

/-- The frame's bytes are not the state's nor the output's. -/
theorem fb_not (h : FoldRoundPre a s0 w m0) {x : Nat} (hx : x < 184) :
    ¬ InRange (pA m0) stateBytes (off (fb m0) x) ∧ ¬ InRange (oA m0) 40 (off (fb m0) x) := by
  obtain ⟨g1, g2, g3, g4, -, g6⟩ := geo h
  exact ⟨fun hq ↦ not_inRange_of_apart g3 g1 g6 hq (inRange_off_self hx (by omega)),
    fun hq ↦ not_inRange_of_apart g4 g2 g6 hq (inRange_off_self hx (by omega))⟩

/-- The state's and the output's bytes are not the `TState`'s nor the decoded area's. -/
theorem po_not_t (h : FoldRoundPre a s0 w m0) {q : BitVec 64}
    (hq : InRange (pA m0) stateBytes q ∨ InRange (oA m0) 40 q) :
    ¬ InRange (tA m0) tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q := by
  have hfp := h.2.1.footprint
  rcases hq with hq | hq
  · exact ⟨not_inRange_of_apart (pre_p h).2.2.1 (pre_p h).2.1 hfp.1.2 hq,
      not_inRange_of_apart (pre_p h).2.2.2.1 (pre_p h).2.1 hfp.2.1.2 hq⟩
  · exact ⟨not_inRange_of_apart (pre_o h).2.2.1 (pre_o h).2.1 hfp.1.2 hq,
      not_inRange_of_apart (pre_o h).2.2.2.1 (pre_o h).2.1 hfp.2.1.2 hq⟩

end

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}
  {x1 x2 x3 x4 : EW} {s5 : TState}

/-- A body state after a block whose changes are in the outputs. -/
theorem fr_of_low {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hw : Fr m0 d) (hwf : (frameEnv m0 d 176 rest vars ret).WF)
    (hm : Match (frameEnv m0 d 176 rest vars ret) S d') (hmid : MidOk 176 8 slots S = true)
    {R : BitVec 64 → Prop} (hs : SameOutside d.dmem d'.dmem R) (hR : ∀ q, R q → outs m0 q) :
    Fr m0 d' :=
  ⟨Frame.of_block hw.fr hwf hm hmid slots_le, fun q hq ↦
    (hs q fun h ↦ hq (.inl (hR q h))).trans (hw.same q hq)⟩

end

end NativeRustcVmX64.Whir.FoldRound
