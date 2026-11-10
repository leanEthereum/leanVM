/-
  LeanVM.Guest.B1.VerifySub.Proof

  The child proof `verify_sub` checks, read off its valuation, the memory and the frame map.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Whir.Witness
public import LeanVM.Guest.B1.Main.Frames

/-!
# The child proof, decoded

`vsPiOf rd σ V` reads the child proof off `verify_sub`'s valuation `σ`, the memory `rd` and the
frame map `V`, choosing nothing and computing no hash: the stream is the memory's words at
`stream` (`σ 25`) up to the cursor handed to `open_stacked` (`σ 1928`, found by comparing
`g`-powers, `cursorLen`), then `open_stacked`'s words, and the openings are `open_stacked`'s
(`open_stacked_osW` at its frame, the specialization read off the dispatch's selector `σ 1922`).

`wordsAt_eq`, `cursorLen_eq`, `dispatchIdx_eq`: the decoding gives what a run read.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The `n` memory words at `p`, `p·g^k` for `k < n` (`0` where there is none). -/
def wordsAt (rd : Reader) (p : E) (n : ℕ) : List E :=
  (List.range n).map fun k ↦ (rd (p.limb 0 * Parameters.addressOfIndex k)).getD 0

/-- The `n ≤ 2^32` with `q = p·g^n`, the first one (`0` if there is none). -/
def cursorLen (p q : E) : ℕ :=
  ((List.range (2 ^ 32 + 1)).find? fun n ↦ decide (q = p * gen ^ n)).getD 0

/-- The `j < 28` with `x = g^j`, the first one (`0` if there is none). -/
def dispatchIdx (x : E) : ℕ :=
  ((List.range 28).find? fun j ↦ decide (x = ofK (Parameters.addressOfIndex j))).getD 0

/-- `open_stacked`'s argument words in `verify_sub`. -/
def vsOsArgs (σ : Val) : List E :=
  [σ (.n 1370), σ (.n 1371), σ (.n 1372), σ (.n 1373), σ (.n 1374), σ (.n 1917), σ (.n 268),
    σ (.n 271), σ (.n 1928), σ (.n 1930)]

/-- `open_stacked`'s return words in `verify_sub`. -/
def vsOsRets (σ : Val) : List E := [σ (.n 1931), σ (.n 1932), σ (.n 1933), σ (.n 1934), σ (.n 1935)]

/-- The child proof, given `open_stacked`'s witness function `osW` (candidate, arguments,
returns ↦ stream words, openings). -/
def piOfW (osW : ℕ → List E → List E → List E × List (List Opening)) (rd : Reader) (σ : Val) :
    Proof :=
  let w := osW (dispatchIdx (σ (.n 1922))) (vsOsArgs σ) (vsOsRets σ)
  ⟨wordsAt rd (σ (.n 25)) (cursorLen (σ (.n 25)) (σ (.n 1928))) ++ w.1, w.2⟩

/-- `open_stacked`'s witness function at the frame map `V`. -/
def vsOsW (rd : Reader) (V : FrameMap) : ℕ → List E → List E → List E × List (List Opening) :=
  fun m args rets ↦ B1.Whir.open_stacked_osW rd m (V (B1.Whir.openNames.getD m "") args rets) V

/-- **The child proof `verify_sub` checks**, read off its valuation, the memory and the frame
map. -/
def vsPiOf (rd : Reader) (σ : Val) (V : FrameMap) : Proof := piOfW (vsOsW rd V) rd σ

/-! ## The decoding gives what a run read -/

theorem wordsAt_eq {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) :
    wordsAt rd p xs.length = xs := by
  apply List.ext_getElem (by simp [wordsAt])
  intro k h1 h2
  simp only [wordsAt, List.getElem_map, List.getElem_range]
  rw [(h k h2).2]
  rfl

theorem find?_range_unique {N : ℕ} {P : ℕ → Bool} {n : ℕ} (hn : n < N) (hP : P n = true)
    (huniq : ∀ m < N, P m = true → m = n) : (List.range N).find? P = some n := by
  obtain ⟨m, hm⟩ : ∃ m, (List.range N).find? P = some m := by
    refine Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨n, List.mem_range.2 hn, hP⟩)
  have hmP := List.find?_some hm
  have hmN := List.mem_range.1 (List.mem_of_find?_eq_some hm)
  rw [hm, huniq m hmN hmP]

theorem ne_zero_of_load {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) {p : E} {k : ℕ} {v : E}
    (h : LoadHolds L.read p k v) : p ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi, -⟩ := (read_some_iff hκ L _ _).mp h.2
  have : (0 : E).limb 0 = 0 := by simp [limb_zero]
  rw [this, zero_mul] at hi
  exact Parameters.gpow_ne_zero _ hi.symm

theorem cursorLen_eq {p q : E} {n : ℕ} (hp : p ≠ 0) (hq : q = p * gen ^ n) (hn : n ≤ 2 ^ 32) :
    cursorLen p q = n := by
  unfold cursorLen
  rw [find?_range_unique (n := n) (by omega) (by simp [hq]) (fun m hm hP ↦ by
    have e := of_decide_eq_true hP
    rw [hq] at e
    exact gen_pow_inj (by omega) (by omega) (mul_left_cancel₀ hp e).symm)]
  rfl

theorem dispatchIdx_eq {x : E} {j : ℕ} (hj : j < 28) (hx : x = ofK (Parameters.addressOfIndex j)) :
    dispatchIdx x = j := by
  unfold dispatchIdx
  rw [find?_range_unique (n := j) hj (by simp [hx]) (fun m hm hP ↦ by
    have e := of_decide_eq_true hP
    rw [hx] at e
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective e)).symm)]
  rfl

end
end LeanVM.Guest.B1.VerifySub
