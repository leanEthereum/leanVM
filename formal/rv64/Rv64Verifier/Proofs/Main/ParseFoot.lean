import Rv64Verifier.Proofs.Main.ParseFrame

/-!
# The `Proof`'s parts by footprint

`PathIn t a op lo hi`: the `MerklePath` at `a` holds `op`, its two buffers in `[lo, hi)`;
`PhaseIn t a ph lo hi`: the `Vec<MerklePath>` at `a` holds `ph`, its buffer and its paths' in
`[lo, hi)`. Writes that miss the header and `[lo, hi)` keep them (`PathIn.frame`,
`PhaseIn.frame`); in the heap below `NEXT` they are what `walk` needs (`PathIn.mem`,
`PhaseIn.mem`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End

/-- `n` bytes from `p`, aligned to `al`, within `[lo, hi)`, or none and `p` at most `hi`. -/
@[rv_addr] def InR (p : Word) (n al lo hi : Nat) : Prop :=
  p.toNat % al = 0 ∧ ((n = 0 ∧ p.toNat ≤ hi) ∨ lo ≤ p.toNat ∧ p.toNat + n ≤ hi)

theorem InR.mono {p : Word} {n al lo hi lo' hi' : Nat} (h : InR p n al lo hi) (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') : InR p n al lo' hi' :=
  ⟨h.1, h.2.imp (fun h' ↦ ⟨h'.1, le_trans h'.2 h2⟩) fun h' ↦ ⟨le_trans h1 h'.1, le_trans h'.2 h2⟩⟩

theorem InR.le {p : Word} {n al lo hi : Nat} (h : InR p n al lo hi) : p.toNat ≤ hi := by
  rcases h.2 with h' | h' <;> omega

/-- A buffer of the heap whose pointer lies below `NEXT`. -/
theorem inR_of_buf {s : MachineState} {p : Word} {n al : Nat} (h : Buf s p n al)
    (hp : p.toNat ≤ heapNext s) : InR p n al heapStart (heapNext s) :=
  ⟨h.1, h.2.imp_left fun h0 ↦ ⟨h0, hp⟩⟩

/-- The `MerklePath` at `a`'s buffers lie in `[lo, hi)`. -/
structure PathFoot (t : MachineState) (a : Word) (lo hi : Nat) : Prop where
  leaf : InR (vecPtr t a) (8 * (vecLen t a).toNat) 8 lo hi
  sibs : InR (vecPtr t (a + 24)) (32 * (vecLen t (a + 24)).toNat) 1 lo hi

/-- The `MerklePath` at `a` holds `op`, its buffers in `[lo, hi)`. -/
structure PathIn (t : MachineState) (a : Word) (op : Opening) (lo hi : Nat) : Prop where
  val : pathAt t a = op
  foot : PathFoot t a lo hi

/-- The `Vec<MerklePath>` at `a` holds `ph`, its buffer and its paths' in `[lo, hi)`. -/
structure PhaseIn (t : MachineState) (a : Word) (ph : List Opening) (lo hi : Nat) : Prop where
  buf : InR (vecPtr t a) (56 * (vecLen t a).toNat) 8 lo hi
  len : (vecLen t a).toNat = ph.length
  paths : ∀ j (hj : j < ph.length),
    PathIn t (vecPtr t a + BitVec.ofNat 64 (56 * j)) ph[j] lo hi

theorem PathIn.mono {t : MachineState} {a : Word} {op : Opening} {lo hi lo' hi' : Nat}
    (h : PathIn t a op lo hi) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : PathIn t a op lo' hi' :=
  ⟨h.val, ⟨h.foot.leaf.mono h1 h2, h.foot.sibs.mono h1 h2⟩⟩

theorem PhaseIn.mono {t : MachineState} {a : Word} {ph : List Opening} {lo hi lo' hi' : Nat}
    (h : PhaseIn t a ph lo hi) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : PhaseIn t a ph lo' hi' :=
  ⟨h.buf.mono h1 h2, h.len, fun j hj ↦ (h.paths j hj).mono h1 h2⟩

theorem PhaseIn.val {t : MachineState} {a : Word} {ph : List Opening} {lo hi : Nat}
    (h : PhaseIn t a ph lo hi) : phaseAt t a = ph := by
  apply List.ext_getElem
  · simp only [phaseAt, List.length_map, List.length_range, h.len]
  · intro j h1 h2
    simp only [phaseAt, List.getElem_map, List.getElem_range]
    exact (h.paths j h2).val

/-- Writes that miss the header and `[lo, hi)` keep a `MerklePath`. -/
theorem PathIn.frame {t t' : MachineState} {a : Word} {op : Opening} {lo hi : Nat}
    {W : Word → Prop} (h : PathIn t a op lo hi) (hf : BFrame t t' W)
    (hW : ∀ x, W x → ¬ Within x a 56 ∧ ¬ (lo ≤ x.toNat ∧ x.toNat < hi))
    (ha : a.toNat + 56 ≤ 2 ^ 64) (ha8 : a.toNat % 8 = 0) (hhi : hi ≤ 2 ^ 64) :
    PathIn t' a op lo hi := by
  have p0 : vecPtr t' a = vecPtr t a :=
    hf.getMem (by addr_omega [ha, ha8]) fun i hi hw ↦ (hW _ hw).1 (by addr_omega [ha, hi])
  have l0 : vecLen t' a = vecLen t a :=
    hf.getMem (by addr_omega [ha, ha8]) fun i hi hw ↦ (hW _ hw).1 (by addr_omega [ha, hi])
  have p1 : vecPtr t' (a + 24) = vecPtr t (a + 24) :=
    hf.getMem (by addr_omega [ha, ha8]) fun i hi hw ↦ (hW _ hw).1 (by addr_omega [ha, hi])
  have l1 : vecLen t' (a + 24) = vecLen t (a + 24) :=
    hf.getMem (by addr_omega [ha, ha8]) fun i hi hw ↦ (hW _ hw).1 (by addr_omega [ha, hi])
  have d48 : t'.getMem (a + 48) = t.getMem (a + 48) :=
    hf.getMem (by addr_omega [ha, ha8]) fun i hi hw ↦ (hW _ hw).1 (by addr_omega [ha, hi])
  have hl := h.foot.leaf
  have hs := h.foot.sibs
  have hleaf : vecWords t' a = vecWords t a := by
    unfold vecWords
    rw [p0, l0, readWords_eq_map, readWords_eq_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    rcases hl.2 with h0 | ⟨h1, h2⟩
    · omega
    · exact hf.getMem (by addr_omega [h1, h2, hi, hhi, hl.1]) fun j hj hw ↦
        (hW _ hw).2 ⟨by addr_omega [h1, h2, hi, hj, hhi],
        by addr_omega [h1, h2, hi, hj, hhi]⟩
  have hsib : ∀ k ∈ List.range (vecLen t (a + 24)).toNat,
      bytesAt t' (vecPtr t (a + 24) + BitVec.ofNat 64 (32 * k)) 32 =
        bytesAt t (vecPtr t (a + 24) + BitVec.ofNat 64 (32 * k)) 32 := by
    intro k hk
    simp only [List.mem_range] at hk
    rcases hs.2 with h0 | ⟨h1, h2⟩
    · omega
    · exact hf.bytesAt fun j hj hw ↦ (hW _ hw).2 ⟨by addr_omega [h1, h2, hk, hj, hhi],
        by addr_omega [h1, h2, hk, hj, hhi]⟩
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rw [← h.val]
    unfold pathAt
    rw [d48, hleaf, l1, p1, List.map_congr_left fun k hk ↦ congrArg digestOfBytes (hsib k hk)]
  · rw [p0, l0]; exact hl
  · rw [p1, l1]; exact hs

/-- Writes that miss the header and `[lo, hi)` keep a `Vec<MerklePath>` whose paths lie there. -/
theorem PhaseIn.frame {t t' : MachineState} {a : Word} {ph : List Opening} {lo hi : Nat}
    {W : Word → Prop} (h : PhaseIn t a ph lo hi) (hf : BFrame t t' W)
    (hW : ∀ x, W x → ¬ Within x a 24 ∧ ¬ (lo ≤ x.toNat ∧ x.toNat < hi))
    (ha : a.toNat + 24 ≤ 2 ^ 64) (ha8 : a.toNat % 8 = 0) (hhi : hi ≤ 2 ^ 64) :
    PhaseIn t' a ph lo hi := by
  have p0 : vecPtr t' a = vecPtr t a :=
    hf.getMem (by addr_omega [ha, ha8]) fun i hi hw ↦ (hW _ hw).1 (by addr_omega [ha, hi])
  have l0 : vecLen t' a = vecLen t a :=
    hf.getMem (by addr_omega [ha, ha8]) fun i hi hw ↦ (hW _ hw).1 (by addr_omega [ha, hi])
  have hb := h.buf
  refine ⟨by rw [p0, l0]; exact hb, by rw [l0]; exact h.len, fun j hj ↦ ?_⟩
  rw [p0]
  have hj' : j < (vecLen t a).toNat := by rw [h.len]; exact hj
  rcases hb.2 with h0 | ⟨h1, h2⟩
  · omega
  · exact (h.paths j hj).frame hf (fun x hx ↦ ⟨fun hw ↦ (hW x hx).2
      ⟨by addr_omega [hw, h1, h2, hj', hhi], by addr_omega [hw, h1, h2, hj', hhi]⟩, (hW x hx).2⟩)
      (by addr_omega [h1, h2, hj', hhi]) (by addr_omega [h1, h2, hj', hhi, hb.1]) hhi

/-! ## What `walk` needs of them -/

/-- A part in the heap below `NEXT`. -/
theorem part_of_inR {s : MachineState} {p : Word} {n al lo hi : Nat} (h : InR p n al lo hi)
    (hlo : heapStart ≤ lo) (hhi : hi ≤ heapNext s) (hheap : HeapOk s) (hsp : s.getReg .x2 = msp) :
    Part s (msp + 320) p n al := by
  rcases h with ⟨hal, ⟨h0, hp⟩ | ⟨h1, h2⟩⟩
  · exact ⟨hal, Or.inl ⟨h0, le_trans hp hhi⟩⟩
  · have he := hheap.hi
    simp only [heapStart, heapNext, heapEnd] at hlo hhi he
    refine ⟨hal, Or.inr ⟨?_, ⟨Or.inl (by simp only [heapNext]; omega), ?_⟩, ?_, ?_, ?_⟩⟩
    · simp only [Mapped]; omega
    · addr_omega [h1, h2, hlo, hhi, he]
    · simp only [stackLo, hsp]; addr_omega [h1, h2, hlo, hhi, he]
    · addr_omega [h1, h2, hlo, hhi, he]
    · simp only [rodataBase, rodataSize]; addr_omega [h1, h2, hlo, hhi, he]

theorem PathIn.mem {s : MachineState} {a : Word} {op : Opening} {lo hi : Nat}
    (h : PathIn s a op lo hi) (hlo : heapStart ≤ lo) (hhi : hi ≤ heapNext s) (hheap : HeapOk s)
    (hsp : s.getReg .x2 = msp) : PathMem s (msp + 320) a :=
  ⟨part_of_inR h.foot.leaf hlo hhi hheap hsp, part_of_inR h.foot.sibs hlo hhi hheap hsp⟩

theorem PhaseIn.mem {s : MachineState} {a : Word} {ph : List Opening} {lo hi : Nat}
    (h : PhaseIn s a ph lo hi) (hlo : heapStart ≤ lo) (hhi : hi ≤ heapNext s) (hheap : HeapOk s)
    (hsp : s.getReg .x2 = msp) : PhaseMem s (msp + 320) a :=
  ⟨part_of_inR h.buf hlo hhi hheap hsp, fun j hj ↦
    (h.paths j (by rw [← h.len]; exact hj)).mem hlo hhi hheap hsp⟩

end Rv64Verifier.Proofs.Main
