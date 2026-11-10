import Rv64Verifier.Proofs.Main.ParsePathMid

/-!
# A path, stored

`0x80000c44` writes the `MerklePath` (leaf `Vec`, siblings `Vec`, leaf index) to slot `j` of the
phase's buffer at `P` and counts `j` up (`path_c44`); `path_body` is a whole path, from `0x80000c7c`
to the next or to `0x80000bb0`, reading one `readOpening`.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

theorem add24_8 (a : Word) : a + 24 + 8 = a + 32 := by rw [BitVec.add_assoc]; rfl

theorem add24_16 (a : Word) : a + 24 + 16 = a + 40 := by rw [BitVec.add_assoc]; rfl

/-- What a path ends with: it read `op` from word `k` to `k'`, holds it at `P + 56 j`, wrote only
`Wpath`, and is at `e`. -/
structure PathDone (u₀ : MachineState) (words : List Word) (P : Word) (npi j k : Nat)
    (t₀ : MachineState) (v : MachineState) : Prop where
  out : ∃ op k', readOpening.run (words.drop k) = some (op, words.drop k') ∧
    PathIn v (P + BitVec.ofNat 64 (56 * j)) op (heapNext t₀) (heapNext v) ∧
    ((j + 1 < npi ∧ PaS u₀ words P npi (j + 1) k' 0x80000c7c v) ∨
      (j + 1 = npi ∧ PaS u₀ words P npi (j + 1) k' 0x80000bb0 v))
  frame : BFrame t₀ v (Wpath (heapNext t₀) (P + BitVec.ofNat 64 (56 * j)))
  mono : heapNext t₀ ≤ heapNext v

theorem mul56 (j : Nat) :
    BitVec.ofNat 64 j * 64 - BitVec.ofNat 64 j * 8 = BitVec.ofNat 64 (56 * j) := by
  apply BitVec.eq_of_toNat_eq
  have h64 : (64 : Word).toNat = 64 := rfl
  have h8 : (8 : Word).toNat = 8 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    h64, h8]
  omega

section
variable {s u₀ t : MachineState} {words : List Word}

/-- **The path stored.** -/
theorem path_c44 (h0 : ParseA s words u₀) {P L Q : Word} {npi j k l h : Nat} {t₀ : MachineState}
    (hc : AtC44 u₀ words P npi j k t₀ L l Q h t) :
    ∃ v, Reaches Image.code t v ∧ PathDone u₀ words P npi j k t₀ v := by
  have hg := hc.pg
  have hsp := hg.sp
  have hhi := hg.heap.hi
  obtain ⟨hP8, hP0, hPn⟩ := hc.start.buf
  have hm0 := hc.mono
  have hj := hc.lt
  have hk : k < words.length := by have := hc.room; omega
  simp only [heapNext, heapEnd] at hhi hP0 hPn hm0
  have hPm : Mapped P (56 * npi) := by
    have := h0.inv.heap.lo; simp only [heapStart, heapNext] at this; simp only [Mapped]; omega
  set a := P + BitVec.ofNat 64 (56 * j) with ha
  have hA : P + (BitVec.ofNat 64 j * 64 - BitVec.ofNat 64 j * 8) = a := by rw [mul56 j]
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b80000c44_spec hc.pc (by
    rv_eval [hc.x23, hc.x24, mul56 j]
    and_intros <;> valid_in hPm [hP8, hj, hPn, hhi, hm0])
  have hfr : MemFrame t v a 56 := hv.memFrame (by
    rv_eval [hc.x23, hc.x24, mul56 j]; and_intros <;> addr_omega [hP8, hj, hPn, hhi, hm0, ha])
  have kv := b80000c44_keeps hv
  have hspv : v.getReg .x2 = msp := by rw [kv .x2 (by decide), hsp]
  have hgv : PG u₀ v := hg.heapWrite hfr (by addr_omega [hP8, hj, hPn, hhi, hm0, ha]) (by decide)
    (by addr_omega [hP0, hj, hPn, hhi, hm0, ha]) (by simp only [heapNext]; addr_omega [hj, hPn, hhi, hm0, ha])
    hspv
  have hnv : heapNext v = heapNext t := by
    simp only [heapNext]; rw [hfr _ (by addr_omega [hj, hPn, hhi, hm0, ha])]
  have e48 : v.getMem (a + 48) = words[k] := by
    have e := b80000c44_m0 hv
    rw [hc.x23, hc.x24, hA, hc.x8] at e
    rw [e, List.getD_eq_getElem _ _ hk]
  have e8 : vecPtr v a = L := by
    have e := b80000c44_m5 hv
    rw [hc.x23, hc.x24, hA, hc.x25] at e
    exact e
  have e16 : vecLen v a = BitVec.ofNat 64 l := by
    have e := b80000c44_m4 hv
    rw [hc.x23, hc.x24, hA, hc.x19] at e
    exact e
  have e32 : vecPtr v (a + 24) = Q := by
    have e := b80000c44_m2 hv
    rw [hc.x23, hc.x24, hA, hc.x27] at e
    unfold vecPtr; rw [add24_8]; exact e
  have e40 : vecLen v (a + 24) = BitVec.ofNat 64 h := by
    have e := b80000c44_m1 hv
    rw [hc.x23, hc.x24, hA, hc.x26] at e
    unfold vecLen; rw [add24_16]; exact e
  obtain ⟨hL8, hLb⟩ := hc.lbuf
  obtain ⟨-, hQb⟩ := hc.qbuf
  have hl64 : l < 2 ^ 64 := by
    rcases hLb with h' | h' <;> (try simp only [heapNext] at h') <;> omega
  have hh64 : h < 2 ^ 64 := by
    rcases hQb with h' | h' <;> (try simp only [heapNext] at h') <;> omega
  have hbf : BFrame t v (Within · a 56) :=
    BFrame.of_memFrame hfr (by addr_omega [hP8, hj, hPn, hhi, hm0, ha]) (by decide)
  have hleaf : v.readWords L l = (words.drop (k + 2)).take l := by
    rw [← hc.leaf]
    rcases hLb with h' | h'
    · rw [show l = 0 by omega]; rfl
    · simp only [heapNext] at h'
      exact readWords_bframe hbf hL8 (fun x hx hw ↦ by addr_omega [hx, hw, h', hj, hPn, hhi, hm0, ha])
        (by omega)
  have hsib : ∀ c ∈ List.range h, bytesAt v (Q + BitVec.ofNat 64 (32 * c)) 32 =
      bytesAt t (Q + BitVec.ofNat 64 (32 * c)) 32 := by
    intro c hc'
    simp only [List.mem_range] at hc'
    rcases hQb with h' | h'
    · omega
    · simp only [heapNext] at h'
      exact hbf.bytesAt fun i hi hw ↦ by addr_omega [hw, hi, hc', h', hj, hPn, hhi, hm0, ha]
  set op : Opening := ⟨words[k].toNat, ((words.drop (k + 2)).take l).map BF64.ofBitVec,
    (List.range h).map fun c ↦ digestOfBytes (bytesAt t (Q + BitVec.ofNat 64 (32 * c)) 32)⟩
    with hop
  have hread : readOpening.run (words.drop k) = some (op, words.drop (k + 3 + l + 4 * h)) := by
    rw [drop_cons hk, readOpening_run hc.lread hc.sread]
  have hval : pathAt v a = op := by
    simp only [pathAt, vecWords, hop, e48, e8, e16, e32, e40, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hh64, hleaf]
    congr 1
    exact List.map_congr_left fun c hc' ↦ congrArg digestOfBytes (hsib c hc')
  have hpin : PathIn v a op (heapNext t₀) (heapNext v) := ⟨hval, ⟨?_, ?_⟩⟩
  rotate_left
  · rw [e8, e16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64, hnv]; exact ⟨hL8, hLb⟩
  · rw [e32, e40, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh64, hnv]; exact ⟨Nat.mod_one _, hQb⟩
  have m88 : v.getMem (msp + 88) = t.getMem (msp + 88) := hfr _ (by addr_omega [hj, hPn, hhi, hm0, ha])
  have m96 : v.getMem (msp + 96) = t.getMem (msp + 96) := hfr _ (by addr_omega [hj, hPn, hhi, hm0, ha])
  have hS : ∀ e, v.pc = e → PaS u₀ words P npi (j + 1) (k + 3 + l + 4 * h) e v := fun e he ↦
    { pg := hgv
      pc := he
      x18 := by rw [kv .x18 (by decide), hc.x18]
      x23 := by rw [kv .x23 (by decide), hc.x23]
      x24 := by rw [b80000c44_x24 hv, hc.x24]; addr_omega [hj, hPn, hhi, hm0]
      room := hc.room
      ptr := by rw [m88, hc.ptr]
      rest := by rw [m96, hc.rest]
      buf := ⟨hP8, by simp only [heapNext]; omega, by rw [hnv]; simp only [heapNext]; omega⟩ }
  have hdone : ∀ e, v.pc = e → (j + 1 < npi ∧ e = 0x80000c7c) ∨ (j + 1 = npi ∧ e = 0x80000bb0) →
      PathDone u₀ words P npi j k t₀ v := by
    intro e he hor
    refine ⟨⟨op, _, hread, hpin, ?_⟩, hc.frame.trans hbf fun x hx ↦ Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hx)))), by rw [hnv]; exact hc.mono⟩
    rcases hor with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · exact Or.inl ⟨h1, hS _ he⟩
    · exact Or.inr ⟨h1, hS _ he⟩
  by_cases he : j + 1 = npi
  · exact ⟨v, rv, hdone _ (b80000c44_pc_taken hv (by rw [hc.x24, hc.x18]; addr_omega [he, hPn, hhi, hm0]))
      (Or.inr ⟨he, rfl⟩)⟩
  · exact ⟨v, rv, hdone _ (b80000c44_pc_not_taken hv (by
      rw [hc.x24, hc.x18]; addr_omega [he, hj, hPn, hhi, hm0])) (Or.inl ⟨by omega, rfl⟩)⟩

/-- **A path**, from `0x80000c7c`. -/
theorem path_body (h0 : ParseA s words u₀) {P : Word} {npi j k : Nat}
    (hs : PaS u₀ words P npi j k 0x80000c7c t) (hj : j < npi) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ PathDone u₀ words P npi j k t v) := by
  obtain ⟨v₁, r₁, hd | ⟨L, l, h₁⟩⟩ := path_head h0 hs hj
  · exact ⟨v₁, r₁, Or.inl hd⟩
  obtain ⟨v₂, r₂, hd | ⟨Q, h, h₂⟩⟩ := path_mid h0 h₁
  · exact ⟨v₂, r₁.trans r₂, Or.inl hd⟩
  obtain ⟨v₃, r₃, h₃⟩ := path_c44 h0 h₂
  exact ⟨v₃, r₁.trans (r₂.trans r₃), Or.inr h₃⟩

end

end Rv64Verifier.Proofs.Main
