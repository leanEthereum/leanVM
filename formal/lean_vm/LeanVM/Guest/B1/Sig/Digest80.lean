/-
  LeanVM.Guest.B1.Sig.Digest80

  The 80-byte message digest both verifiers hash in one block (`keccak(…, tail=[ρ, 0, 0, 0],
  len=80)`): its output's first cells are the hash of the five cells.
-/

module

public import LeanVM.Guest.B1.Sig.Merkle

/-!
# The 80-byte digest

`kec80_sound`: a `KECCAK` atom reading `P`, the address, the message's two cells, the randomizer,
then the padding (`0x01` at byte 80, `0x80` at byte 135) and zero capacity cells writes the first
half of `hcell [P, A, m0, m1, ρ]` into its one output cell.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash

@[expose] public section

variable {rd : Reader} {σ : Val}

theorem padCells_five (a b c d e : E) :
    padCells [a, b, c, d, e] 80 = [a, b, c, d, e, word 1 0, 0, 0, word (2 ^ 63) 0] := by
  simp [padCells, xorByte, padRead, rate, byteCell]

/-- **The 80-byte digest**, into a one-cell `out`. -/
theorem kec80_sound {pp adr m0 m1 r t1 t2 t3 t4 z1 z2 z3 z4 : V} {o : Nat}
    (hK : AtomsHold rd σ [kecS [pp, adr, m0, m1, r, t1, t2, t3, t4, z1, z2, z3, z4] (runV o 1) false false])
    (h1 : σ t1 = word 1 0) (h2 : σ t2 = 0) (h3 : σ t3 = 0) (h4 : σ t4 = word (2 ^ 63) 0)
    (hz1 : σ z1 = 0) (hz2 : σ z2 = 0) (hz3 : σ z3 = 0) (hz4 : σ z4 = 0) :
    σ (.n o) = (hcell [σ pp, σ adr, σ m0, σ m1, σ r]).1 := by
  have hk := hK.atom (List.mem_singleton_self _)
  obtain ⟨-, -, O, hk, hw⟩ := keccak_holds_full hk
  have := keccak_one (cells := [σ pp, σ adr, σ m0, σ m1, σ r]) (len := 80) (by simp) (by simp [rate])
    (fun j hj => by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp [cellsBytes]; omega)]
      rfl)
    (fun c hc => by
      rw [padCells_five]
      fin_cases c <;> simp_all [cells13, List.getD_eq_getElem?_getD]) (fun c hc => by
      fin_cases c <;> simp_all [cells13, List.getD_eq_getElem?_getD]) hk
  rw [hcell, ← cellsBytes_eq_flatMap]
  have h80 : (cellsBytes [σ pp, σ adr, σ m0, σ m1, σ r]).take 80 = cellsBytes [σ pp, σ adr, σ m0, σ m1, σ r] := by
    rw [List.take_of_length_le (by simp [cellsBytes])]
  rw [← h80, ← this.2]
  simpa [runV] using hw 0 (by simp [runV])

end
end LeanVM.Guest.B1.Sig
