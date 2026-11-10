import Rv64Verifier.Proofs.Walk.AtJump

/-!
# `walk`: `tables()`, the tables copied into their buffer (R9)

`M8` across a step writing only the tables' buffer and a callee's stack (`M8.stepBb`); a `Table`
copied doubleword by doubleword (`TableAt.moveB`); the copies made so far and the opcodes stored
(`Cp`), kept by a step writing past them (`Cp.frame`); `table_rows`' length (`rows_len`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

/-- `M8` across a step that writes only the tables' buffer and a callee's stack. -/
theorem M8.stepBb {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {w : Word → Prop} {m : Nat} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W L) (fr : Rv64Verifier.Layout.DFrame u v w)
    (hw : ∀ a, w a → Within a Bb 480 ∨ Within a (stackLo u m) m) (hm : m ≤ 8736) (hv : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) : M8 OI s v A k R Q B Bb W L := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨b1, b2, b3, b4⟩ := h.bb
  have I := h.m.inv
  have hu := I.heap.hi
  simp only [heapEnd, heapNext] at hu b4
  have far : ∀ a, w a → a.toNat < (s.getReg .x2 - 2656).toNat := fun a ha ↦ by
    rcases hw a ha with ha | ha
    · simp only [Within] at ha; addr_omega [ha, hb1, hu, b3, b4]
    · rw [stackLo_callee I] at ha; simp only [Within] at ha; addr_omega [ha, hb1, hm]
  have keep (c : Word) (hc : (s.getReg .x2 - 2656).toNat ≤ c.toNat) (hc' : c.toNat + 8 ≤ 2 ^ 64) :
      v.getMem c = u.getMem c :=
    fr c (fun x hx hwx ↦ by have := far x hwx; simp only [Within] at hx; omega) hc'
  exact {
    m := h.m.step hpre (fr.mono fun a ha ↦ by
        rcases hw a ha with ha | ha
        · simp only [Within] at ha
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapNext] at mono ⊢; omega⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre I hm ha)))))
      hv mono sp
    lens := ⟨by rw [keep _ (by addr_omega [hb1]) (by addr_omega [hb1])]; exact h.lens.1,
      by rw [keep _ (by addr_omega [hb1]) (by addr_omega [hb1])]; exact h.lens.2⟩
    bb := ⟨b1, b2, b3, by simp only [heapNext]; simp only [heapNext] at mono; omega⟩
    slot := by rw [keep _ (by addr_omega [hb1]) (by addr_omega [hb1])]; exact h.slot
    tabs := fun e he ↦ by
      obtain ⟨hs, ht, hd⟩ := h.tabs e he
      obtain ⟨o1, o2, o3⟩ := hs
      have T := ht.frame fr (fun x hx hwx ↦ by
          have := far x hwx; simp only [Within] at hx; addr_omega [hx, this, o1, hb1])
        (fun x hx hwx ↦ by
          have d := hd x hx
          rcases hw x hwx with hx' | hx'
          · exact d.2.2 hx'
          · rw [stackLo_callee I] at hx'; simp only [Within] at hx'
            addr_omega [hx', d.2.1, hb1, hm, hu, b4])
        (by addr_omega [hb1, o2]) I.heap mono
      exact ⟨⟨o1, o2, o3⟩, T.1, fun x hx ↦ hd x (by rw [← T.2]; exact hx)⟩ }

/-- A `Table` whose nine doublewords were copied from `o` to `a`. -/
theorem TableAt.moveB {u v : MachineState} {o a : Word} {t : LayoutMirror.TableRust} {w : Word → Prop}
    (h : TableAt u o t) (fr : Rv64Verifier.Layout.DFrame u v w)
    (g : ∀ j < 9, v.getMem (a + BitVec.ofNat 64 (8 * j)) = u.getMem (o + BitVec.ofNat 64 (8 * j)))
    (hd : ∀ x, tableDeep u o x → ¬ w x) (hh : ∀ x, Within x a 72 → ¬ tableDeep u o x)
    (ha : a.toNat + 72 ≤ 2 ^ 64) (hheap : HeapOk u) (mono : heapNext u ≤ heapNext v) :
    TableAt v a t ∧ tableDeep v a = tableDeep u o := by
  have g0 : v.getMem a = u.getMem o := by simpa using g 0 (by omega)
  have g8 : v.getMem (a + 8) = u.getMem (o + 8) := g 1 (by omega)
  have g16 : v.getMem (a + 16) = u.getMem (o + 16) := g 2 (by omega)
  have g24 : v.getMem (a + 24) = u.getMem (o + 24) := g 3 (by omega)
  have e (x : Word) (p q r : Word) (hr : p + q = r) : x + p + q = x + r := by rw [BitVec.add_assoc, hr]
  have g32 : v.getMem (a + 24 + 8) = u.getMem (o + 24 + 8) := by
    rw [e a 24 8 (BitVec.ofNat 64 (8 * 4)) (by decide), e o 24 8 (BitVec.ofNat 64 (8 * 4)) (by decide)]
    exact g 4 (by omega)
  have g40 : v.getMem (a + 24 + 16) = u.getMem (o + 24 + 16) := by
    rw [e a 24 16 (BitVec.ofNat 64 (8 * 5)) (by decide), e o 24 16 (BitVec.ofNat 64 (8 * 5)) (by decide)]
    exact g 5 (by omega)
  have g48 : v.getMem (a + 24 + 24) = u.getMem (o + 24 + 24) := by
    rw [e a 24 24 (BitVec.ofNat 64 (8 * 6)) (by decide), e o 24 24 (BitVec.ofNat 64 (8 * 6)) (by decide)]
    exact g 6 (by omega)
  have g56 : v.getMem (a + 24 + 24 + 8) = u.getMem (o + 24 + 24 + 8) := by
    rw [e a 24 24 48 (by decide), e o 24 24 48 (by decide), e a 48 8 (BitVec.ofNat 64 (8 * 7)) (by decide),
      e o 48 8 (BitVec.ofNat 64 (8 * 7)) (by decide)]
    exact g 7 (by omega)
  have g64 : v.getMem (a + 24 + 24 + 16) = u.getMem (o + 24 + 24 + 16) := by
    rw [e a 24 24 48 (by decide), e o 24 24 48 (by decide), e a 48 16 (BitVec.ofNat 64 (8 * 8)) (by decide),
      e o 48 16 (BitVec.ofNat 64 (8 * 8)) (by decide)]
    exact g 8 (by omega)
  have hr := h.padVec.raw
  have hl := h.padVec.len
  simp only [RawVecOk, Buf, vecPtr, vecCap, vecLen] at hr hl
  have hes : vecEs v a = vecEs u o := by
    simp only [vecEs, vecPtr, vecLen, g8, g16]
    refine Bus.eListAt_congr fun i hi ↦ ?_
    have k (c : Nat) (hc : c ≤ 16) :
        v.getMem (u.getMem (o + 8) + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c) =
          u.getMem (u.getMem (o + 8) + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c) :=
      fr _ (fun x hx hw ↦ by
        refine hd x ?_ hw
        left; simp only [Within, vecPtr, vecCap]
        simp only [Within] at hx
        rcases hr.2 with h0' | h0' <;> addr_omega [hi, hl, hc, h0', hx]) (by
          rcases hr.2 with h0' | h0' <;> addr_omega [hi, hl, hc, h0'])
    apply eAt_congr
    · have := k 0 (by omega); rwa [add_ofNat_zero] at this
    · exact k 8 (by omega)
    · exact k 16 (by omega)
  have G := Rv64Verifier.Layout.Arith.flushesOf_move fr h.ok g24 g32 g40 g48 g56 g64
    (fun x hx ↦ hd x (Or.inr hx))
    (fun x hx hd' ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ha]) (Or.inr hd')) hheap mono
  have hdeep : tableDeep v a = tableDeep u o := by
    funext x; simp only [tableDeep, vecPtr, vecCap, g0, g8, G.2.2]
  exact ⟨⟨vecOk_move g0 g8 g16 mono h.padVec, by rw [hes]; exact h.pad, G.2.1,
    by rw [G.1]; exact h.flushes⟩, hdeep⟩

/-- `table_rows` holds six counts, the rate being read past them. -/
theorem rows_len {A : List E} (h : 1#64 ≤ rateOf A) : (rowsOf A).length = 6 := by
  by_contra hne
  have hl : A.length ≤ 7 := by
    simp only [rowsOf, List.length_map, List.length_take, List.length_drop,
      LayoutMirror.nTablesRust] at hne
    omega
  have h0 : rateOf A = 0 := by
    simp only [rateOf, LayoutMirror.nTablesRust]
    rw [List.getD_eq_default _ _ (by omega)]
    decide
  rw [h0] at h
  exact absurd h (by decide)

/-- The table with opcode `i`. -/
def tl (i : Nat) : LayoutMirror.TableRust := (LayoutMirror.tablesRust[i]?).getD xorT

/-- The first `n` tables copied to `Bb + 80 i`, all they reach in `[B, W)` and apart from `Bb`; the
first `m` opcodes stored at `Bb + 80 i + 72`. -/
structure Cp (u : MachineState) (B W : Nat) (Bb : Word) (n m : Nat) : Prop where
  tab : ∀ i < n, TableAt u (Bb + BitVec.ofNat 64 (80 * i)) (tl i) ∧
    ∀ x, tableDeep u (Bb + BitVec.ofNat 64 (80 * i)) x → B ≤ x.toNat ∧ x.toNat < W ∧ ¬ Within x Bb 480
  op : ∀ i < m, u.getMem (Bb + BitVec.ofNat 64 (80 * i + 72)) = BitVec.ofNat 64 i

theorem Cp.zero (u : MachineState) (B W : Nat) (Bb : Word) : Cp u B W Bb 0 0 :=
  ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩

theorem bb_off {Bb : Word} {i : Nat} (hb : Bb.toNat + 480 < 2 ^ 64) (c : Nat) (hc : 80 * i + c ≤ 480) :
    (Bb + BitVec.ofNat 64 (80 * i + c)).toNat = Bb.toNat + 80 * i + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : 80 * i + c < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bb_off0 {Bb : Word} {i : Nat} (hb : Bb.toNat + 480 < 2 ^ 64) (hi : i ≤ 6) :
    (Bb + BitVec.ofNat 64 (80 * i)).toNat = Bb.toNat + 80 * i := by
  have := bb_off hb 0 (by omega : 80 * i + 0 ≤ 480); simpa using this

/-- The copies and opcodes across a step writing past them, within `Bb`, or above the heap. -/
theorem Cp.frame {u v : MachineState} {B W : Nat} {Bb : Word} {n m : Nat} {w : Word → Prop}
    (h : Cp u B W Bb n m) (fr : Rv64Verifier.Layout.DFrame u v w) (hn : n ≤ 6) (hm : m ≤ 6)
    (hw : ∀ a, w a → (Bb.toNat + 80 * n ≤ a.toNat + 8 ∧ Bb.toNat + 80 * m ≤ a.toNat ∧
      a.toNat < Bb.toNat + 480) ∨ heapEnd ≤ a.toNat)
    (hW : W ≤ heapEnd) (hb : Bb.toNat + 480 ≤ heapEnd) (hheap : HeapOk u)
    (mono : heapNext u ≤ heapNext v) : Cp v B W Bb n m := by
  simp only [heapEnd] at hW hb
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · obtain ⟨T, hd⟩ := h.tab i hi
    have ho := bb_off0 (Bb := Bb) (i := i) (by omega) (by omega)
    have T' := T.frame fr (fun x hx hwx ↦ by
        simp only [Within] at hx
        rcases hw x hwx with hx' | hx' <;> (try simp only [heapEnd] at hx') <;> omega)
      (fun x hx hwx ↦ by
        have d := hd x hx
        rcases hw x hwx with hx' | hx'
        · exact d.2.2 (by simp only [Within]; omega)
        · simp only [heapEnd] at hx'; omega)
      (by omega) hheap mono
    exact ⟨T'.1, fun x hx ↦ hd x (by rw [← T'.2]; exact hx)⟩
  · have ho := bb_off (Bb := Bb) (i := i) (by omega) 72 (by omega)
    rw [fr _ (fun x hx hwx ↦ by
        simp only [Within] at hx
        rcases hw x hwx with hx' | hx' <;> (try simp only [heapEnd] at hx') <;> omega) (by omega)]
    exact h.op i hi

end Rv64Verifier.Proofs.Walk
