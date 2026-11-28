module

public import NativeRustcVmArm.Wire.PhaseM.RowsRun

/-!
# `phase_m`: what memory keeps

Nodes, leaves and levels of siblings kept by a change of memory outside them (`nodes_keep`,
`leaves_keep`, `sibs_keep`), one node more (`nodes_snoc`), one level more (`sibs_snoc`). `Chg`:
what a step of the body may change (the stack, the reader's cursor, the phase, parts `L` of the
working area); `Geo.not_chg`: a part of the working area apart from those `L` misses it.
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- What a step of the body may change: the stack, the reader's cursor, the phase, the parts `L`
of the working area. -/
def Chg (m0 : MachineData) (L : List (Nat × Nat)) (q : BitVec 64) : Prop :=
  InRange (base m0 1184) 1184 q ∨ InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨
    InRange (outA m0) phaseBytes q ∨ ∃ p ∈ L, InRange (wa m0 p.1) p.2 q

end

public section

theorem node_keep {d d' : Mem 64} {a : BitVec 64} {x : Nat × Digest}
    {R : BitVec 64 → Prop} (h : NodeAt d a x) (hs : SameOutside d d' R)
    (hR : ∀ i < 40, ¬R (a + BitVec.ofNat 64 i)) : NodeAt d' a x := by
  refine ⟨h.1, h.2.1.of_sameOutside hs fun i hi ↦ hR i (by
      rw [NativeRustcVm.length_wordBytes] at hi; omega),
    h.2.2.of_sameOutside hs fun i hi ↦ ?_⟩
  have : i < 32 := by rw [NativeRustcVm.length_wordsBytes] at hi; simpa using hi
  rw [NativeRustcVm.addr_add_add]
  exact hR _ (by omega)

/-- **Nodes kept** by a change outside them. -/
theorem nodes_keep {d d' : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)}
    {R : BitVec 64 → Prop} (h : NodesAt d a l) (hs : SameOutside d d' R)
    (hR : ∀ i < 40 * l.length, ¬R (a + BitVec.ofNat 64 i)) : NodesAt d' a l := fun j hj ↦
  node_keep (h j hj) hs fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]; exact hR _ (by omega)

/-- **One node more**, written after them. -/
theorem nodes_snoc {d d' : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)} {x : Nat × Digest}
    (h : NodesAt d a l) (hx : NodeAt d' (a + BitVec.ofNat 64 (40 * l.length)) x)
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 (40 * l.length)) 40))
    (hnw : NoWrap a (40 * (l.length + 1))) : NodesAt d' a (l ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]
    refine node_keep (h j hj) hs fun i hi ↦ ?_
    rw [NativeRustcVm.addr_add_add]
    exact NativeRustcVm.not_inRange_sub hnw (by omega) (by omega) (.inl (by omega))
  · rw [List.getElem_append_right (le_refl _)]
    simpa using hx

/-- **Leaves kept** by a change outside them. -/
theorem leaves_keep {d d' : Mem 64} {a : BitVec 64} {l : List (List K)} {R : BitVec 64 → Prop}
    (h : LeavesAt d a l) (hs : SameOutside d d' R) (hw : ∀ x ∈ l, x.length ≤ 64)
    (hR : ∀ i < 512 * l.length, ¬R (a + BitVec.ofNat 64 i)) : LeavesAt d' a l := fun j hj ↦
  (h j hj).of_sameOutside hs fun i hi ↦ by
    have := hw _ (List.getElem_mem hj)
    rw [NativeRustcVm.length_wordsBytes, List.length_map] at hi
    rw [NativeRustcVm.addr_add_add]; exact hR _ (by omega)

/-- **Levels of siblings kept** by a change outside them. -/
theorem sibs_keep {d d' : Mem 64} {a cnt : BitVec 64} {l : List (List (Nat × Digest))}
    {R : BitVec 64 → Prop} (h : SibsAt d a cnt l) (hs : SameOutside d d' R)
    (hR : ∀ i < nodesBytes * l.length, ¬R (a + BitVec.ofNat 64 i))
    (hC : ∀ i < 8 * l.length, ¬R (cnt + BitVec.ofNat 64 i)) : SibsAt d' a cnt l := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h j hj
  refine ⟨h1, h2.of_sameOutside hs fun i hi ↦ ?_, nodes_keep h3 hs fun i hi ↦ ?_⟩
  · rw [NativeRustcVm.length_wordBytes] at hi
    rw [NativeRustcVm.addr_add_add]; exact hC _ (by omega)
  · rw [NativeRustcVm.addr_add_add]
    have : 40 * l[j].length ≤ nodesBytes := by rw [nodesBytes_eq]; omega
    have : nodesBytes * j + i < nodesBytes * l.length := by
      have := Nat.mul_le_mul_left nodesBytes (show j + 1 ≤ l.length by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    exact hR _ this

/-- **One level more** of siblings. -/
theorem sibs_snoc {d : Mem 64} {a cnt : BitVec 64} {l : List (List (Nat × Digest))}
    {x : List (Nat × Digest)} (h : SibsAt d a cnt l) (hx : x.length ≤ 256)
    (hc : WordAt d (cnt + BitVec.ofNat 64 (8 * l.length)) x.length.toUInt64)
    (hn : NodesAt d (a + BitVec.ofNat 64 (nodesBytes * l.length)) x) :
    SibsAt d a cnt (l ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]; exact h j hj
  · rw [List.getElem_append_right (le_refl _)]
    simpa using ⟨hx, hc, hn⟩

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8}

/-- **A part of the working area apart from the parts `L`** misses what a step changes. -/
theorem Geo.not_chg [Labels] (G : Geo m0 bp B) {L : List (Nat × Nat)} {o n : Nat}
    (hon : o + n ≤ workBytes)
    (hL : ∀ p ∈ L, p.1 + p.2 ≤ workBytes ∧ (p.1 + p.2 ≤ o ∨ o + n ≤ p.1)) :
    ∀ i < n, ¬Chg m0 L (wa m0 o + BitVec.ofNat 64 i) := by
  intro i hi hq
  have hw := G.wa_toNat (o := o) (by omega)
  have hnw : NoWrap (wa m0 o) n := by
    unfold NoWrap; rw [hw]; have := G.wNw; omega
  have hin : InRange (wa m0 o) n (wa m0 o + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi (by unfold NoWrap at hnw; omega)
  rcases hq with h | h | h | ⟨p, hp, h⟩
  · exact NativeRustcVm.Apart.not_inRange (G.wa_apart hon (by omega) G.sW.symm) hnw
      (Ring.base_noWrap G.sp) hin h
  · exact NativeRustcVm.Apart.not_inRange (G.wa_apart hon (by omega) G.rW.symm) hnw G.rNw hin
      (NativeRustcVm.InRange.of_sub (o := 16) (m := 8) h G.rNw (by omega))
  · exact NativeRustcVm.Apart.not_inRange (G.wa_apart hon (by omega) G.oW.symm) hnw G.oOk.2 hin h
  · obtain ⟨h1, h2⟩ := hL p hp
    have hpn : NoWrap (wa m0 p.1) p.2 := by
      by_cases hn : p.2 = 0
      · rw [hn] at h; unfold InRange at h; omega
      unfold NoWrap; rw [G.wa_toNat (by omega)]; have := G.wNw; omega
    exact NativeRustcVm.Apart.not_inRange (G.wa_wa hon h1 (by omega)) hnw hpn hin h

/-- The frame is in the stack. -/
theorem frame_chg (hst : StackOk m0 1184) {o n : Nat} (hon : o + n ≤ 192) {L : List (Nat × Nat)}
    {q : BitVec 64} (h : InRange (base m0 192 + BitVec.ofNat 64 o) n q) : Chg m0 L q :=
  .inl (frame_sub hst hon h)

end

end NativeRustcVmArm.Wire.PhaseM
