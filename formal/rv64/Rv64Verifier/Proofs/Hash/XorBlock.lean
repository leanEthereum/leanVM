import Rv64Verifier.Proofs.Hash.XorBlockChecks
import Rv64Verifier.Proofs.Hash.Bytes

/-!
# `verifier::hash::xor_block`

```rust
fn xor_block(state: &mut [u64; STATE_LANES], block: &[u8; RATE]) {
    for (lane, word) in state.iter_mut().zip(block.as_chunks::<8>().0) {
        *lane ^= u64::from_le_bytes(*word);
    }
}
```

compiled at `0x8000e5c8` (`Blocks/F71.lean`) as 567 instructions without a branch: 136 `lbu`s,
the words assembled and spilled, the 17 lanes XORed, the frame restored. The block may have any
alignment `r`: the machine at entry is `xsig r` of the state whose `a1` is the block's aligned
doubleword (`s'`), and `XorBlockChecks.lean` checks the run once per `r < 8`.
-/

namespace Rv64Verifier.Hash.XorBlock
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Contracts Rv64Verifier.Model

/-! ## Bytes of the block -/

theorem alignToDword_add_aligned {b c : Word} (hb : b.toNat % 8 = 0)
    (hw : b.toNat + c.toNat < 2 ^ 64) : alignToDword (b + c) = b + alignToDword c := by
  apply BitVec.eq_of_toNat_eq
  have h1 := alignToDword_toNat (b + c)
  have h2 := alignToDword_toNat c
  have h3 : (b + c).toNat = b.toNat + c.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hw
  have h4 : (b + alignToDword c).toNat = b.toNat + (alignToDword c).toNat := by
    rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
  omega

theorem byteOffset_add_aligned {b c : Word} (hb : b.toNat % 8 = 0)
    (hw : b.toNat + c.toNat < 2 ^ 64) : byteOffset (b + c) = byteOffset c := by
  rw [byteOffset_eq, byteOffset_eq, BitVec.toNat_add, Nat.mod_eq_of_lt hw]
  omega

theorem byteE_eval {s : MachineState} {r j : Nat} (hb : (s.getReg .x11).toNat % 8 = 0)
    (hw : (s.getReg .x11).toNat + r + j < 2 ^ 64) :
    (byteE r j).eval s = (s.getByte (s.getReg .x11 + BitVec.ofNat 64 (r + j))).setWidth 64 := by
  have hc : (BitVec.ofNat 64 (r + j)).toNat = r + j := by rw [BitVec.toNat_ofNat]; omega
  have h1 := alignToDword_add_aligned hb (c := BitVec.ofNat 64 (r + j)) (by rw [hc]; omega)
  have h2 := byteOffset_add_aligned hb (c := BitVec.ofNat 64 (r + j)) (by rw [hc]; omega)
  simp only [byteE, E.eval, UnOp.eval, LoadKind.fromWord, Addr.toE_eval, Addr.eval,
    MachineState.getByte, h1, h2, BitVec.zeroExtend_eq_setWidth]

theorem fromLeBytes8 (x : Nat → BitVec 8) : fromLeBytes ((List.range 8).map x) =
    (x 0).setWidth 64 ||| (x 1).setWidth 64 <<< 8 ||| (x 2).setWidth 64 <<< 16 |||
      (x 3).setWidth 64 <<< 24 ||| (x 4).setWidth 64 <<< 32 ||| (x 5).setWidth 64 <<< 40 |||
      (x 6).setWidth 64 <<< 48 ||| (x 7).setWidth 64 <<< 56 := by
  simp only [fromLeBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.mul_zero, BitVec.shiftLeft_zero, Nat.reduceMul]
  have hz : ∀ y : Word, (0 : Word) ||| y = y := fun y ↦ by simp
  rw [hz]

theorem wordE_eval (s : MachineState) (b : Nat → E) (x : Nat → BitVec 8)
    (h : ∀ k < 8, (b k).eval s = (x k).setWidth 64) :
    (wordE b).eval s = fromLeBytes ((List.range 8).map x) := by
  simp only [wordE, halfE, E.eval, BinOp.eval, h 0 (by decide), h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
    fromLeBytes8]
  rw [show (24 : Word).toNat % 64 = 24 from rfl, show (16 : Word).toNat % 64 = 16 from rfl,
    show (8 : Word).toNat % 64 = 8 from rfl, show (32 : Word).toNat % 64 = 32 from rfl]
  simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  generalize (x 0).setWidth 64 = a0
  generalize (x 1).setWidth 64 <<< 8 = a1
  generalize (x 2).setWidth 64 <<< 16 = a2
  generalize (x 3).setWidth 64 <<< 24 = a3
  generalize (x 4).setWidth 64 <<< 32 = a4
  generalize (x 5).setWidth 64 <<< 40 = a5
  generalize (x 6).setWidth 64 <<< 48 = a6
  generalize (x 7).setWidth 64 <<< 56 = a7
  ac_rfl

theorem laneE_eval {s : MachineState} {r i : Nat} (hi : i < 17)
    (hb : (s.getReg .x11).toNat % 8 = 0) (hw : (s.getReg .x11).toNat + r + 136 ≤ 2 ^ 64) :
    (laneE r i).eval s = s.getMem (s.getReg .x10 + BitVec.ofNat 64 (8 * i)) ^^^
      fromLeBytes ((List.range 8).map fun k ↦
        s.getByte (s.getReg .x11 + BitVec.ofNat 64 (r + (8 * i + k)))) := by
  simp only [laneE, E.eval, BinOp.eval, Addr.toE_eval, key, Addr.eval]
  rw [wordE_eval s _ _ fun k hk ↦ byteE_eval hb (by omega)]

theorem bytesAt_drop_take (s : MachineState) (a : Word) {i : Nat} (hi : i < 17) :
    ((bytesAt s a 136).drop (8 * i)).take 8 =
      (List.range 8).map fun k ↦ s.getByte (a + BitVec.ofNat 64 (8 * i + k)) := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp [bytesAt]

theorem length_xorBlockRust (L : List Word) (B : List (BitVec 8)) :
    (xorBlockRust L B).length = L.length := by
  unfold xorBlockRust
  generalize List.range 17 = l
  induction l generalizing L with
  | nil => rfl
  | cons i l ih => rw [List.foldl_cons, ih, List.length_set]

theorem xorBlockRust_getD (L : List Word) (B : List (BitVec 8)) {j : Nat} (hj : j < L.length) :
    (xorBlockRust L B).getD j 0 =
      if j < 17 then L.getD j 0 ^^^ fromLeBytes ((B.drop (8 * j)).take 8) else L.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, xorBlockRust, getElem?_foldl_xor, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj]
  rfl

/-- A doubleword holding a valid byte is valid: the zones of memory start at multiples of 8. -/
theorem dword_valid {a d : Word} (ha : isValidMemAddr a = true) (hd : d.toNat % 8 = 0)
    (h₁ : d.toNat ≤ a.toNat) (h₂ : a.toNat < d.toNat + 8) : isValidDwordAccess d = true := by
  simp only [isValidMemAddr, MEM_START, MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START,
    RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
  simp only [isValidDwordAccess, isValidMemAddr, isAligned8, MEM_START, MEM_END, INPUT_MEM_START,
    INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

theorem add_zero_sub (x y : Word) : x + (0 - y) = x - y := by bv_omega

/-! ## `xor_block` -/

/-- **`xor_block` meets its contract.** -/
theorem xor_block_spec : XorBlockSpec := by
  intro s hpc hpre
  have hbv := hpre.block
  have hbv1 := hbv.1
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hst := ValidMemRange.bounds hpre.state (by decide)
  have hss := hpre.stateStack
  have hbs := hpre.blockStack
  have hsk := hpre.stateBlock
  simp only [xorBlockStack, stackLo] at hsb hss hbs
  obtain ⟨r, hr⟩ : ∃ r, r = (s.getReg .x11).toNat % 8 := ⟨_, rfl⟩
  have hr8 : r < 8 := by omega
  obtain ⟨base, hbase⟩ : ∃ b, b = s.getReg .x11 - BitVec.ofNat 64 r := ⟨_, rfl⟩
  have hbaseN : base.toNat = (s.getReg .x11).toNat - r := by
    rw [hbase, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : r < 2 ^ 64)]
    omega
  have hal : base.toNat % 8 = 0 := by omega
  have hblk : s.getReg .x11 = base + BitVec.ofNat 64 r := by
    rw [hbase, BitVec.sub_add_cancel]
  set s' := s.setReg .x11 base with hs'
  have h11 : s'.getReg .x11 = base := by simp [s', MachineState.setReg, MachineState.getReg]
  have hreg (q : Reg) (hq : q ≠ .x11) : s'.getReg q = s.getReg q := by
    cases q <;> simp_all [s', MachineState.setReg, MachineState.getReg]
  have hmem : ∀ a, s'.getMem a = s.getMem a := fun _ ↦ rfl
  have hu : (xsig r).toState s' s.code 0x8000e5c8 = s := by
    rw [← hpc]
    apply Sym.MachineState.ext' <;> try rfl
    funext q
    simp only [SymState.toState, xsig]
    by_cases hq : q = .x11
    · subst hq
      split
      · rename_i h0; cases h0
      · rw [RegFile.get_set_self _ _ (by decide), mkAdd_eval]
        simp only [E.eval, h11, ← hblk]
        rfl
    · split
      · rename_i h0; subst h0; rfl
      · rename_i h0
        rw [RegFile.get_set_ne _ _ hq, show SymState.init.regs = RegFile.init from rfl,
          RegFile.init_get_eval, hreg q hq]
        cases q <;> first | exact absurd rfl h0 | rfl
  have hok : RegionsOk s' [stateR, stackR, blockR r] := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · show ValidMemRange (s'.getReg .x10 + 0) 25
      rw [Sym.add_zero_lit, hreg .x10 (by decide)]; exact hpre.state
    · show ValidMemRange (s'.getReg .x2 + (0 - 512)) 64
      rw [add_zero_sub, hreg .x2 (by decide)]; exact hpre.stack.valid
    · show ValidMemRange (s'.getReg .x11 + 0) ((r + 143) / 8)
      rw [Sym.add_zero_lit, h11]
      intro q hq
      have hj : (if 8 * q ≥ r then 8 * q - r else 0) < 136 := by split <;> omega
      apply dword_valid (hbv.2 _ hj) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) <;>
        · rw [hblk, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
            BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          split <;> omega
  have hap : RegionsApart s' [stateR, stackR, blockR r] := by
    refine List.pairwise_cons.mpr ⟨fun R hR ↦ ?_, List.pairwise_cons.mpr ⟨fun R hR ↦ ?_,
      List.pairwise_singleton _ _⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · show Apart (s'.getReg .x10 + 0) 200 (s'.getReg .x2 + (0 - 512)) 512
        rw [Sym.add_zero_lit, add_zero_sub, hreg .x10 (by decide), hreg .x2 (by decide)]
        exact hss
      · show Apart (s'.getReg .x10 + 0) 200 (s'.getReg .x11 + 0) (8 * ((r + 143) / 8))
        simp only [Sym.add_zero_lit]
        rw [ hreg .x10 (by decide), h11]
        addr_omega [hsk, hst, hbaseN, hal, hbv.1, hr]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      subst hR
      show Apart (s'.getReg .x2 + (0 - 512)) 512 (s'.getReg .x11 + 0) (8 * ((r + 143) / 8))
      rw [add_zero_sub, Sym.add_zero_lit, hreg .x2 (by decide), h11]
      addr_omega [hbs, hsb, hbaseN, hal, hbv.1, hr]
  have hbok : BRegionsOk s' [bytesR r] := by
    intro B hB i hi
    simp only [List.mem_singleton] at hB
    subst hB
    show isValidMemAddr (s'.getReg .x11 + BitVec.ofNat 64 r + BitVec.ofNat 64 i) = true
    rw [h11, ← hblk]
    exact hbv.2 i hi
  obtain ⟨t, hstp, h⟩ := run_spec (xor_run hr8) (codeWindow_sub _ _ _ (by decide)) hu hok hap hbok
    (by show (s'.getReg .x11).toNat % 8 = 0; rw [h11]; exact hal)
  have hsaved (q : Reg) (hq : q ∈ saved) : t.getReg q = s'.getReg q :=
    h.2.1 (q, .reg q) (List.mem_map.mpr ⟨q, hq, rfl⟩)
  have hfrw (a : Word) (ha : ∀ k ∈ (xorX 0).writes, a ≠ k.eval s') : t.getMem a = s.getMem a :=
    h.frame a ha
  refine ⟨t, ⟨_, hstp⟩, Or.inl ⟨?_, fun q hq ↦ ?_, ?_, fun a h₁ h₂ ↦ ?_⟩⟩
  · rw [h.1]
    simp only [xorX, E.eval, BinOp.eval, returnAddress_eq, hreg .x1 (by decide)]
  · have hcs : ∀ q ∈ calleeSaved, q ∈ saved := by decide
    rw [hsaved q (hcs q hq)]
    exact hreg q (by intro h; subst h; simp [calleeSaved] at hq)
  · apply readWords_eq (by rw [length_xorBlockRust, readWords_length])
    intro j hj
    rw [xorBlockRust_getD _ _ (by rw [readWords_length]; exact hj), readWords_getD _ _ _ _ hj]
    split
    · rename_i h17
      have hm := h.2.2.1 (key .x10 (8 * j), laneE r j)
        (List.mem_map.mpr ⟨j, List.mem_range.mpr h17, rfl⟩)
      rw [laneE_eval (s := s') (r := r) h17 (by rw [h11]; exact hal) (by rw [h11]; omega),
        hreg .x10 (by decide),
        h11, hmem] at hm
      simp only [key, Addr.eval, E.eval, hreg .x10 (by decide)] at hm
      rw [hm, bytesAt_drop_take _ _ h17]
      congr 2
      apply List.map_congr_left
      intro k _
      rw [hblk, ofNat_add_ofNat]
      rfl
    · rename_i h17
      apply hfrw
      intro k hk
      simp only [xorX, List.mem_append, List.mem_map, List.mem_range] at hk
      rcases hk with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · simp only [key, Addr.eval, E.eval, hreg .x10 (by decide)]
        addr_omega [hst, hi, hj, h17]
      · simp only [Addr.eval, E.eval, hreg .x2 (by decide)]
        rw [show s.getReg .x2 + (0 - 512 + BitVec.ofNat 64 (8 * i)) =
          s.getReg .x2 - 512 + BitVec.ofNat 64 (8 * i) by bv_omega]
        addr_omega [hst, hss, hsb, hi, hj]
  · apply h.frame_regions (rs := [stateR, stackR]) (fun R hR ↦ hok R (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢; tauto)) xor_writes a
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · show ¬ Within a (s'.getReg .x10 + 0) (8 * 25)
      rw [show s'.getReg .x10 + 0 = s.getReg .x10 from
        (Sym.add_zero_lit _).trans (hreg .x10 (by decide))]
      exact h₁
    · show ¬ Within a (s'.getReg .x2 + (0 - 512)) (8 * 64)
      rw [add_zero_sub, hreg .x2 (by decide)]
      simpa [stackLo, xorBlockStack] using h₂

end Rv64Verifier.Hash.XorBlock
