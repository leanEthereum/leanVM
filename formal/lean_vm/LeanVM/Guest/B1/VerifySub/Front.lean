/-
  LeanVM.Guest.B1.VerifySub.Front

  The sponge's atoms at `verify_sub`'s front: the seed's permutation.
-/

module

public import LeanVM.Guest.B1.VerifySub.Flat
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.Value.KeccakSponge
public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Protocol.KeccakHash

/-!
# The front's atoms

`seed_cap`: the seed's `KECCAK` (`keccak_cells([seed_0, seed_1, pi_0, pi_1], sp, final=0)`), on
the four cells and nine zeros, writes the capacity of `keccakF (seedInput seed pi)`, the digests
read off the four cells.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- **The seed's permutation**: its capacity is the seed state's. -/
theorem seed_cap {a b c d z1 z2 z3 z4 o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 : V}
    (hk : (Atom.keccak [a, b, c, d, z1, z2, z3, z4, z1, z1, z2, z3, z4]
      [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12] false false).Holds rd σ)
    (h1 : σ z1 = 0) (h2 : σ z2 = 0) (h3 : σ z3 = 0) (h4 : σ z4 = 0) :
    [σ o8, σ o9, σ o10, σ o11, σ o12] =
      capOf (keccakF1600 (seedInput (digestFromHalves (σ a, σ b)) (digestFromHalves (σ c, σ d)))) := by
  obtain ⟨-, -, hK⟩ := (keccak_holds_13 (by rfl)).mp hk
  have hch := Keccak.keccak_chain (P := [σ a, σ b, σ c, σ d])
    (S0 := Keccak.zeroState) (B := 1)
    (I := fun _ ↦ cells13 ([a, b, c, d, z1, z2, z3, z4, z1, z1, z2, z3, z4].map σ))
    (O := fun k ↦ if k = 0 then cellsOfState Keccak.zeroState false
      else cells13 ([o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12].map σ))
    (by simp)
    (fun k hk c hc ↦ by
      obtain rfl : k = 0 := by omega
      fin_cases c <;> simp_all [cells13, Keccak.cellsOfState_zero])
    (fun k hk c hc ↦ by
      obtain rfl : k = 0 := by omega
      fin_cases c <;> simp_all [cells13, Keccak.cellsOfState_zero])
    (fun k hk ↦ by
      obtain rfl : k = 0 := by omega
      exact hK)
  simp only [one_ne_zero, ↓reduceIte] at hch
  rw [show [σ a, σ b, σ c, σ d] =
      [(digestHalves (digestFromHalves (σ a, σ b))).1, (digestHalves (digestFromHalves (σ a, σ b))).2,
        (digestHalves (digestFromHalves (σ c, σ d))).1, (digestHalves (digestFromHalves (σ c, σ d))).2] by
      simp only [digestScalars_digestOfScalars],
    Keccak.absorbChunks_seed] at hch
  simp only [capOf]
  rw [← congrFun hch 8, ← congrFun hch 9, ← congrFun hch 10, ← congrFun hch 11, ← congrFun hch 12]
  rfl

/-- **A permutation of a carried sponge writes its capacity.** -/
theorem fs_perm_cap {ins : List V} {o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 : V} {s : Fs}
    (hk : (Atom.keccak ins [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12] false false).Holds
      rd σ) (hs : s.pend.length ≤ 4)
    (hins : ins.map σ = pendCells s.pend ++ List.replicate (8 - 2 * s.pend.length) 0 ++ s.cap) :
    [σ o8, σ o9, σ o10, σ o11, σ o12] = capOf s.perm := by
  have h := keccakA_fs hk hs hins
  simp only [capOf]
  rw [← congrFun h 8, ← congrFun h 9, ← congrFun h 10, ← congrFun h 11, ← congrFun h 12]
  rfl

end
end LeanVM.Guest.B1.VerifySub
