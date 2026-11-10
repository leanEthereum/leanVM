import Rv64Verifier.Proofs.Main.ParseHead
import Rv64Verifier.Proofs.Main.IvAlloc
import Rv64Verifier.Proofs.Bytecode.Bits

/-!
# What `ParseRest` shares

* The input's pieces as `main` reads them: words, scalars, digests and openings
  (`readWords_run`, `readScalar_run`, `readDigest_run`, `readOpening_run`), and the bytes of a
  digest (`digestBytes_ofWords`, `digestOfBytes_eq`).
* What stays put (`PG`): from `ParseA`'s state `u₀` on, `main` writes only its scratch slots
  (`msp + 24` to `msp + 104`, `msp + 272` to `msp + 352`), its callees' stacks, `NEXT` and the heap
  allocated since (`Wf`). The frame, the input, the `Bytecode` and the public input are then
  `u₀`'s (`PG.minv`, `PG.bc`, `PG.pi`).
* The `Proof`'s parts by footprint: a `MerklePath` (`PathIn`) or a `Vec<MerklePath>` (`PhaseIn`)
  whose buffers lie in `[lo, hi)` reads the same after writes that miss its header and `[lo, hi)`.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End

/-! ## Reading the input -/

theorem readWords_run : ∀ (n : Nat) (ws : List Word), n ≤ ws.length →
    (readWords n).run ws = some (ws.take n, ws.drop n)
  | 0, _, _ => rfl
  | n + 1, w :: ws, h => by
    have ih := readWords_run n ws (by simp only [List.length_cons] at h; omega)
    have e : (readWords (n + 1)).run (w :: ws) =
        ((readWords n).run ws).bind fun q ↦ some (w :: q.1, q.2) := rfl
    rw [e, ih]
    rfl

/-- A digest from its four words. -/
def digestOfWords (w : List Word) : Digest := Vector.ofFn fun i : Fin 4 ↦ ⟨w.getD i.val 0⟩

theorem readDigest_run {ws : List Word} (h : 4 ≤ ws.length) :
    readDigest.run ws = some (digestOfWords (ws.take 4), ws.drop 4) := by
  have e : readDigest.run ws =
      ((readWords 4).run ws).bind fun q ↦ some (digestOfWords q.1, q.2) := rfl
  rw [e, readWords_run 4 ws h]
  rfl

/-- A scalar from three words. -/
def scalarOfWords (w : List Word) : E :=
  E.ofLimbs (BF64.ofBitVec (w.getD 0 0)) (BF64.ofBitVec (w.getD 1 0)) (BF64.ofBitVec (w.getD 2 0))

theorem readScalar_run : ∀ {ws : List Word}, 3 ≤ ws.length →
    readScalar.run ws = some (scalarOfWords ws, ws.drop 3)
  | _ :: _ :: _ :: _, _ => rfl

theorem readOpening_run {idx : Word} {ws w₁ w₂ : List Word} {leaf : List K} {path : List Digest}
    (h₁ : (readList (BF64.ofBitVec <$> readWord)).run ws = some (leaf, w₁))
    (h₂ : (readList readDigest).run w₁ = some (path, w₂)) :
    readOpening.run (idx :: ws) = some ({ leafIndex := idx.toNat, leaf, path }, w₂) := by
  have e : readOpening.run (idx :: ws) =
      ((readList (BF64.ofBitVec <$> readWord)).run ws).bind fun p ↦
        ((readList readDigest).run p.2).bind fun q ↦
          some ({ leafIndex := idx.toNat, leaf := p.1, path := q.1 }, q.2) := rfl
  rw [e, h₁]
  show ((readList readDigest).run w₁).bind _ = _
  rw [h₂]
  rfl

/-- What `rep` reads has its length. -/
theorem rep_length {α : Type} {item : Reader α} :
    ∀ {n : Nat} {ws rest : List Word} {xs : List α}, (rep item n).run ws = some (xs, rest) →
      xs.length = n
  | 0, ws, rest, xs, h => by
    rw [rep_zero] at h
    cases h
    rfl
  | n + 1, ws, rest, xs, h => by
    rw [rep_run_bind] at h
    rcases h1 : item.run ws with _ | p
    · rw [h1] at h; cases h
    · rw [h1] at h
      simp only [Option.bind_some] at h
      rcases h2 : (rep item n).run p.2 with _ | q
      · rw [h2] at h; cases h
      · rw [h2] at h
        simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [List.length_cons, rep_length h2]

theorem digestBytes_ofWords : ∀ (w : List Word), w.length = 4 →
    Model.byteBits (KeccakHash.digestBytes (digestOfWords w)) = w.flatMap Model.toLeBytes
  | [a, b, c, d], _ => by
    have h (x : Word) : Model.byteBits (KeccakHash.wordBytes ⟨x⟩) = Model.toLeBytes x :=
      (Model.toLeBytes_toBitVec ⟨x⟩).symm
    simp only [KeccakHash.digestBytes, digestOfWords, Model.byteBits] at h ⊢
    simp [Vector.toList_ofFn, List.ofFn_succ, List.flatMap_cons, List.map_append, h]

/-- The words of 32 aligned bytes in memory are its doublewords. -/
theorem digestWords_at (s : MachineState) {a : Word} (ha : a.toNat % 8 = 0) {j : Nat}
    (hj : j < 4) :
    (Model.digestWordsRust (bytesAt s a 32)).getD j 0 = s.getMem (a + BitVec.ofNat 64 (8 * j)) := by
  have hb : (a + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e : ((bytesAt s a 32).drop (8 * j)).take 8 =
      (List.range 8).map (extractByte (s.getMem (a + BitVec.ofNat 64 (8 * j)))) := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, bytesAt_length, List.length_map,
        List.length_range]
      omega
    · intro k h1 h2
      simp only [List.length_map, List.length_range] at h2
      rw [List.getElem_take, List.getElem_drop, bytesAt_getElem, List.getElem_map,
        List.getElem_range, ← byteAt_add hb h2, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hf : Model.fromLeBytes ((List.range 8).map (extractByte (s.getMem (a + BitVec.ofNat 64 (8 * j))))) =
      s.getMem (a + BitVec.ofNat 64 (8 * j)) := by
    rw [← toLeBytes_eq]; exact Model.fromLeBytes_toLeBytes _
  rw [Model.digestWordsRust, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, e, hf]

/-- A digest read as bytes from aligned memory is the digest of its four doublewords. -/
theorem digestOfBytes_eq (s : MachineState) {a : Word} (ha : a.toNat % 8 = 0) :
    digestOfBytes (bytesAt s a 32) = digestOfWords (s.readWords a 4) := by
  apply Vector.ext
  intro i hi
  simp only [digestOfBytes, digestOfWords, Vector.getElem_ofFn]
  rw [digestWords_at s ha hi, readWords_eq_map]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

end Rv64Verifier.Proofs.Main
