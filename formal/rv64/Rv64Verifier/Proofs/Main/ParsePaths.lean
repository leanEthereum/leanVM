import Rv64Verifier.Proofs.Main.ParsePathEnd

/-!
# A phase's paths

The loop at `0x80000c7c` (`path_loop`): after `j` paths, `rep readOpening j` read, each path held
at `P + 56 j'` with its buffers past the phase's buffer, memory changed only in `Wph`, `main`'s
scratch slots below the input slice untouched.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-- What a phase writes: `main`'s scratch slots, its result slots, the stack, `NEXT`, the heap from
`B` on, and the phase's 24 bytes at `q`. -/
def Wph (B : Nat) (q a : Word) : Prop :=
  Within a (msp + 24) 80 ∨ Within a (msp + 272) 80 ∨ Within a (msp - 4096) 4096 ∨
    Within a nextAddr 8 ∨ (B ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a q 24

/-- The paths' loop at `e`, `j` paths of the phase at `P` read from word `k` on; `ti` where the
phase started, `tp` where the loop started. -/
structure PaI (u₀ : MachineState) (words : List Word) (P : Word) (npi k : Nat)
    (ti tp : MachineState) (q e : Word) (t : MachineState) (j kj : Nat) (ops : List Opening) :
    Prop where
  pas : PaS u₀ words P npi j kj e t
  read : (rep readOpening j).run (words.drop k) = some (ops, words.drop kj)
  paths : ∀ j' (h : j' < ops.length),
    PathIn t (P + BitVec.ofNat 64 (56 * j')) ops[j'] (P.toNat + 56 * npi) (heapNext t)
  frame : BFrame ti t (Wph (heapNext ti) q)
  slots : ∀ c : Nat, c % 8 = 0 → 24 ≤ c → c + 8 ≤ 88 →
    t.getMem (msp + BitVec.ofNat 64 c) = tp.getMem (msp + BitVec.ofNat 64 c)
  low : heapNext ti ≤ P.toNat

section
variable {s u₀ t : MachineState} {words : List Word}

/-- One path. -/
theorem paths_body (h0 : ParseA s words u₀) {P q : Word} {npi k j kj : Nat} {ti tp : MachineState}
    {ops : List Opening} (h : PaI u₀ words P npi k ti tp q 0x80000c7c t j kj ops) (hj : j < npi) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ kj' ops',
      (j + 1 < npi ∧ PaI u₀ words P npi k ti tp q 0x80000c7c v (j + 1) kj' ops') ∨
      (j + 1 = npi ∧ PaI u₀ words P npi k ti tp q 0x80000bb0 v (j + 1) kj' ops')) := by
  obtain ⟨v, rv, hd | hp⟩ := path_body h0 h.pas hj
  · exact ⟨v, rv, Or.inl hd⟩
  obtain ⟨⟨op, k', hread, hpin, hor⟩, hfr, hmono⟩ := hp
  have hhi := h.pas.pg.heap.hi
  obtain ⟨hP8, hP0, hPn⟩ := h.pas.buf
  simp only [heapNext, heapEnd] at hhi hPn
  have hlen := rep_length h.read
  have hread' := rep_step h.read hread
  have hlow := h.low
  have hpaths : ∀ j' (hj' : j' < (ops ++ [op]).length), PathIn v (P + BitVec.ofNat 64 (56 * j'))
      (ops ++ [op])[j'] (P.toNat + 56 * npi) (heapNext v) := by
    intro j' hj'
    simp only [List.length_append, List.length_singleton] at hj'
    rcases Nat.lt_or_ge j' ops.length with h1 | h1
    · rw [List.getElem_append_left h1]
      refine ((h.paths j' h1).frame hfr (fun x hx ↦ ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩)
        (by addr_omega [hj, hPn, hhi, h1, hlen]) (by addr_omega [hP8, hj, hPn, hhi, h1, hlen])
        (by simp only [heapNext]; omega)).mono (le_refl _) hmono
      · rcases hx with hx | hx | hx | hx | ⟨hx1, hx2⟩ | hx
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
        · simp only [heapNext] at hx1; addr_omega [hx1, hw, hj, hPn, hhi, h1, hlen]
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
      · rcases hx with hx | hx | hx | hx | ⟨hx1, hx2⟩ | hx
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
        · simp only [heapNext] at hx1 hw; omega
        · addr_omega [hx, hw, hj, hPn, hhi, h1, hlen]
    · have e : j' = ops.length := by omega
      subst e
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      rw [hlen]
      exact hpin.mono (by simp only [heapNext]; omega) (le_refl _)
  have hfr' : BFrame ti v (Wph (heapNext ti) q) := h.frame.trans hfr fun x hx ↦ by
    rcases hx with hx | hx | hx | hx | ⟨hx1, hx2⟩ | hx
    · exact Or.inl (by addr_omega [hx])
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
    · have := h.pas.pg.heap.lo
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp only [heapNext] at hx1 hlow ⊢; omega,
        hx2⟩))))
    · simp only [heapNext] at hlow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp only [heapNext]; addr_omega [hx, hlow, hj, hPn, hhi],
        by simp only [heapEnd]; addr_omega [hx, hj, hPn, hhi]⟩))))
  have hslots : ∀ c : Nat, c % 8 = 0 → 24 ≤ c → c + 8 ≤ 88 →
      v.getMem (msp + BitVec.ofNat 64 c) = tp.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 h1 h2
    rw [← h.slots c h8 h1 h2]
    refine hfr.getMem (by addr_omega [h8, h1, h2]) fun i hi hw ↦ ?_
    rcases hw with hw | hw | hw | hw | ⟨hw1, hw2⟩ | hw
    · addr_omega [hw, h1, h2, hi]
    · addr_omega [hw, h1, h2, hi]
    · addr_omega [hw, h1, h2, hi]
    · addr_omega [hw, h1, h2, hi]
    · simp only [heapEnd] at hw2; addr_omega [hw2, h1, h2, hi]
    · addr_omega [hw, h1, h2, hi, hj, hPn, hhi]
  rcases hor with ⟨h1, hs⟩ | ⟨h1, hs⟩
  · exact ⟨v, rv, Or.inr ⟨k', ops ++ [op], Or.inl ⟨h1, hs, hread', hpaths, hfr', hslots, hlow⟩⟩⟩
  · exact ⟨v, rv, Or.inr ⟨k', ops ++ [op], Or.inr ⟨h1, hs, hread', hpaths, hfr', hslots, hlow⟩⟩⟩

/-- **The paths' loop.** -/
theorem path_loop (h0 : ParseA s words u₀) {P q : Word} {npi k kj : Nat} {ti tp : MachineState}
    (h : PaI u₀ words P npi k ti tp q 0x80000c7c t 0 kj []) (hn : 0 < npi) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ kj' ops',
      PaI u₀ words P npi k ti tp q 0x80000bb0 v npi kj' ops') := by
  refine Reaches.loop (fun t ↦ ∃ j kj ops, j < npi ∧ PaI u₀ words P npi k ti tp q 0x80000c7c t j kj ops)
    (fun t ↦ npi - (t.getReg .x24).toNat) _ ?_ t ⟨0, kj, [], hn, h⟩
  rintro t ⟨j, kj, ops, hj, hs⟩
  obtain ⟨v, hv, hd | ⟨kj', ops', ⟨hl, hsv⟩ | ⟨he, hsv⟩⟩⟩ := paths_body h0 hs hj
  · exact Or.inl ⟨v, hv, Or.inl hd⟩
  · refine Or.inr ⟨v, hv, ⟨j + 1, kj', ops', hl, hsv⟩, ?_⟩
    have b := hs.pas.buf.2.2
    have hhi := hs.pas.pg.heap.hi
    simp only [heapNext, heapEnd] at b hhi
    rw [hsv.pas.x24, hs.pas.x24, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · exact Or.inl ⟨v, hv, Or.inr ⟨kj', ops', he ▸ hsv⟩⟩

end

end Rv64Verifier.Proofs.Main
