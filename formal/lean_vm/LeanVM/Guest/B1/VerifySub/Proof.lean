/-
  LeanVM.Guest.B1.VerifySub.Proof

  The child proof `verify_sub` checks, read off its valuation, the memory and the frame map.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Whir.Witness
public import LeanVM.Guest.B1.Main.FramesP
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The child proof, decoded

`vsPiOf rd σ V` reads the child proof off `verify_sub`'s valuation `σ`, the memory `rd` and the
frame map `V`, choosing nothing and computing no hash. Hotwire's `verify_sub` reads one stream,
hinted whole at `stream`, through a cursor; its last section, `open_stacked`, reads on from the
cursor it is handed and returns the cursor past what it read. The proof's stream is the memory's
words at `stream` up to the cursor handed to `open_stacked` (`sumcheck_target~2`, the dispatch's
tenth argument, its length found by comparing `g`-powers, `cursorLen`), then `open_stacked`'s
words, and its openings are `open_stacked`'s (`open_stacked_osW` at its frame: the specialization
`μ - 16` read off the dispatch's selector `size_sel = g^(μ - 16)`, the rate off its selector
`rate_sel = g^(r - 1)`). The words past `open_stacked`'s are not the proof's: its returned cursor
(`cursor@5`) only bounds the stream.

The value numbers cite `verify_sub`'s core IR: the dispatch on `size_sel` over
`open_stacked__L0` to `__L14`, its arguments `rate_sel`, `nxt[8]@7` to `nxt[12]@7` (the sponge's
capacity), `target@2`, `x@9`, `x@10` (the stack's root), `sumcheck_target~2` (the cursor),
`sumcheck_target~4` (the window tables), its returns `sumcheck_target`, `point`, `point1`,
`inner_total`, `yr_at_tail`, `cursor@5`.

`wordsAt_eq`, `cursorLen_eq`, `gIdx_eq`, `dispatchIdx_eq`, `rateOf_eq`: the decoding gives what a
run read.
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

/-- The `j < N` with `x = g^j`, the first one (`0` if there is none). -/
def gIdx (N : ℕ) (x : E) : ℕ :=
  ((List.range N).find? fun j ↦ decide (x = ofK (Parameters.addressOfIndex j))).getD 0

/-- The specialization the dispatch selects: the `j < 15` (`Whir.openArms`) with `x = g^j`. -/
def dispatchIdx (x : E) : ℕ := gIdx Whir.openArms x

/-- The rate whose selector is `x`: one plus the `j < 4` with `x = g^j`. -/
def rateOf (x : E) : ℕ := gIdx 4 x + 1

/-- The cursor `verify_sub` hands `open_stacked`. -/
def vsCursor (σ : Val) : E := σ (.n (val% «verify_sub» "sumcheck_target~2"))

/-- `open_stacked`'s argument words in `verify_sub`. -/
def vsOsArgs (σ : Val) : List E :=
  [σ (.n (val% «verify_sub» "rate_sel")), σ (.n (val% «verify_sub» "nxt[8]@7")),
    σ (.n (val% «verify_sub» "nxt[9]@7")), σ (.n (val% «verify_sub» "nxt[10]@7")),
    σ (.n (val% «verify_sub» "nxt[11]@7")), σ (.n (val% «verify_sub» "nxt[12]@7")),
    σ (.n (val% «verify_sub» "target@2")), σ (.n (val% «verify_sub» "x@9")),
    σ (.n (val% «verify_sub» "x@10")), vsCursor σ, σ (.n (val% «verify_sub» "sumcheck_target~4"))]

/-- `open_stacked`'s return words in `verify_sub`. -/
def vsOsRets (σ : Val) : List E :=
  [σ (.n (val% «verify_sub» "sumcheck_target")), σ (.n (val% «verify_sub» "point")),
    σ (.n (val% «verify_sub» "point1")), σ (.n (val% «verify_sub» "inner_total")),
    σ (.n (val% «verify_sub» "yr_at_tail")), σ (.n (val% «verify_sub» "cursor@5"))]

/-- The child proof, given `open_stacked`'s witness function `osW` (specialization, rate,
arguments, returns ↦ stream words, openings). -/
def piOfW (osW : ℕ → ℕ → List E → List E → List E × List (List Opening)) (rd : Reader) (σ : Val) :
    Proof :=
  let w := osW (dispatchIdx (σ (.n (val% «verify_sub» "size_sel"))))
    (rateOf (σ (.n (val% «verify_sub» "rate_sel")))) (vsOsArgs σ) (vsOsRets σ)
  ⟨wordsAt rd (σ (.n (val% «verify_sub» "stream")))
      (cursorLen (σ (.n (val% «verify_sub» "stream"))) (vsCursor σ)) ++ w.1, w.2⟩

/-- `open_stacked`'s witness function at the frame map `V`: specialization `m`'s frame. -/
def vsOsW (rd : Reader) (V : FrameMap) : ℕ → ℕ → List E → List E → List E × List (List Opening) :=
  fun m r args rets ↦ Whir.open_stacked_osW rd m r (V (Whir.openNames.getD m "") args rets) V

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

theorem gIdx_eq {N : ℕ} (hN : N ≤ 2 ^ 32) {x : E} {j : ℕ} (hj : j < N)
    (hx : x = ofK (Parameters.addressOfIndex j)) : gIdx N x = j := by
  unfold gIdx
  rw [find?_range_unique (n := j) hj (by simp [hx]) (fun m hm hP ↦ by
    have e := of_decide_eq_true hP
    rw [hx] at e
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective e)).symm)]
  rfl

theorem dispatchIdx_eq {x : E} {j : ℕ} (hj : j < Whir.openArms)
    (hx : x = ofK (Parameters.addressOfIndex j)) : dispatchIdx x = j :=
  gIdx_eq (by norm_num) hj hx

theorem rateOf_eq {r : ℕ} (h1 : 1 ≤ r) (h4 : r ≤ 4) : rateOf (Whir.rateSel r) = r := by
  unfold rateOf
  rw [gIdx_eq (x := Whir.rateSel r) (j := r - 1) (by norm_num) (by omega) rfl]
  omega

end
end LeanVM.Guest.B1.VerifySub
