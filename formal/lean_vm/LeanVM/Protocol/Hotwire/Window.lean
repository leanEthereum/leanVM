/-
  LeanVM.Protocol.Hotwire.Window

  A one-hot pointer read at its index, and `s` cells further inside its window.
-/

module

public import LeanVM.Protocol.Hotwire.Eq

/-!
# The window read

A pointer `σ` of `W` bits is committed as chunks of widths `w_0, …, w_{d−1}` (the index's bits
lowest first, chunk 0 the lowest: the verifier's `Chunks`, `crates/verifier/src/link.rs`), chunk
`i` a one-hot table `e_i` over `2^{w_i}` values. The index point `r` splits likewise into parts
`r_i`, so here a chunk layout is the list of parts `rs`, `r = rs.flatten`. Over a commutative ring
`F`, for any layout:

* `chunksEval_eq`: `Π_i ẽ_i(r_i) = eq(r, σ)`, for `ẽ_i(r_i) = Σ_v eq(r_i, v)·e_i(v)` (the
  verifier's `D_i`, `Functionals`), whenever the chunks encode `σ` (`Encodes`, which every
  `σ < 2^W` meets with its chunks `oneHotChunks`, `encodes_oneHotChunks`);
* `window_read`: chunk 0 read `s` cells further, `T_s(e_0) = Σ_v e_0(v)·eq(r_0, v + s)·[v + s <
  2^{w_0}]` (`window_shift`), times the other chunks, is `eq(r, σ + s)` when
  `(σ mod 2^{w_0}) + s < 2^{w_0}`, and zero past the window;
* `sum_window_read`: the block sum `Σ_s ξ_s·T_s(e_0)·Π_{i ≥ 1} ẽ_i(r_i)` the verifier's
  `Functionals::summand` forms is `Σ_s ξ_s·eq(r, σ + s)` over the shifts inside the window
  (`T_0 = D_0`, `windowShift_zero`, so the pointer's own read is the shift `0`).

The prover's side is `window_shift` and `Chunks::shifted`
(`crates/lean_vm_core/src/link/pointer.rs`).
-/

namespace LeanVM.Protocol.Hotwire

open Finset

@[expose] public section

variable {F : Type*} [CommRing F]

/-- `ẽ(r_i) = Σ_{v < 2^{w_i}} eq(r_i, v)·e(v)`, a chunk's table `e` read at its part `r_i` of the
index point, `w_i = |r_i|`: the verifier's `D_i` (`Functionals::values` on the table
`eq_kernel(r_i)`). -/
def chunkEval (ri : List F) (e : ℕ → F) : F := ∑ v ∈ range (2 ^ ri.length), eqAt ri v * e v

/-- A chunk's read is the table's multilinear extension at its part of the point. -/
theorem chunkEval_eq_mle (ri : List F) (e : ℕ → F) : chunkEval ri e = mle ri e := rfl

/-- `T_s(e_0) = Σ_{v < 2^{w_0}} e_0(v)·eq(r_0, v + s)·[v + s < 2^{w_0}]`: chunk 0 read `s` cells
further inside its window (the verifier's `window_shift(eq_kernel(r_0), s)`, read by
`Functionals::values`). -/
def windowShift (r0 : List F) (e0 : ℕ → F) (s : ℕ) : F :=
  ∑ v ∈ range (2 ^ r0.length), e0 v * if v + s < 2 ^ r0.length then eqAt r0 (v + s) else 0

/-- `e` is one-hot at `σ` over its `2^w` values (what it holds elsewhere is never read). -/
def OneHot (w : ℕ) (e : ℕ → F) (σ : ℕ) : Prop := ∀ v < 2 ^ w, e v = if v = σ then 1 else 0

/-- The one-hot chunks `es` encode `σ` in the layout `rs`: chunk `i` is one-hot at `σ`'s bits
`w_0 + … + w_{i−1}` to `w_0 + … + w_i − 1`, and `σ < 2^{w_0 + … + w_{d−1}}`. -/
def Encodes : List (List F) → List (ℕ → F) → ℕ → Prop
  | [], [], σ => σ = 0
  | r :: rs, e :: es, σ => OneHot r.length e (σ % 2 ^ r.length) ∧ Encodes rs es (σ / 2 ^ r.length)
  | _, _, _ => False

/-- The one-hot chunks of `σ` in the layout `rs`, as the prover commits a pointer. -/
def oneHotChunks : List (List F) → ℕ → List (ℕ → F)
  | [], _ => []
  | r :: rs, σ => (fun v => if v = σ % 2 ^ r.length then 1 else 0) :: oneHotChunks rs (σ / 2 ^ r.length)

/-- Every `σ < 2^W`, `W = w_0 + … + w_{d−1}`, has its one-hot chunks. -/
theorem encodes_oneHotChunks : ∀ (rs : List (List F)) (σ : ℕ), σ < 2 ^ (rs.map List.length).sum →
    Encodes rs (oneHotChunks rs σ) σ
  | [], σ, h => by simpa [Encodes, oneHotChunks] using h
  | r :: rs, σ, h => by
    refine ⟨fun _ _ => rfl, encodes_oneHotChunks rs _ ?_⟩
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    simpa [add_comm] using h

/-- `Π_i ẽ_i(r_i)` over the chunks. -/
def chunksEval : List (List F) → List (ℕ → F) → F
  | r :: rs, e :: es => chunkEval r e * chunksEval rs es
  | _, _ => 1

/-- A one-hot chunk reads the equality weight at its hot value. -/
theorem chunkEval_oneHot (ri : List F) (e : ℕ → F) (σ : ℕ) (he : OneHot ri.length e σ)
    (hσ : σ < 2 ^ ri.length) : chunkEval ri e = eqAt ri σ := by
  rw [chunkEval, ← sum_eqAt_mul_ite ri σ hσ]
  exact sum_congr rfl fun v hv => by rw [he v (mem_range.mp hv)]

/-- **One-hot chunks read at the index point**: `Π_i ẽ_i(r_i) = eq(r, σ)`. -/
theorem chunksEval_eq : ∀ (rs : List (List F)) (es : List (ℕ → F)) (σ : ℕ),
    Encodes rs es σ → chunksEval rs es = eqAt rs.flatten σ
  | [], [], _, _ => by simp [chunksEval]
  | r :: rs, e :: es, σ, ⟨he, hes⟩ => by
    rw [chunksEval, chunkEval_oneHot r e _ he (Nat.mod_lt _ (Nat.two_pow_pos _)),
      chunksEval_eq rs es _ hes, List.flatten_cons, eqAt_append, ← eqAt_mod]
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- `T_s` of a one-hot chunk: `eq(r_0, σ_0 + s)` inside the window, zero past it. -/
theorem windowShift_oneHot (r0 : List F) (e0 : ℕ → F) (σ0 s : ℕ) (he : OneHot r0.length e0 σ0)
    (hσ : σ0 < 2 ^ r0.length) :
    windowShift r0 e0 s = if σ0 + s < 2 ^ r0.length then eqAt r0 (σ0 + s) else 0 := by
  rw [windowShift, sum_congr rfl fun v hv => by rw [he v (mem_range.mp hv), ite_mul, one_mul, zero_mul],
    sum_ite_eq', ite_eq_left (mem_range.mpr hσ)]

/-- The shift `0` is the plain read: `T_0 = D_0`. -/
theorem windowShift_zero (r0 : List F) (e0 : ℕ → F) : windowShift r0 e0 0 = chunkEval r0 e0 := by
  rw [windowShift, chunkEval]
  refine sum_congr rfl fun v hv => ?_
  rw [Nat.add_zero, ite_eq_left (mem_range.mp hv), mul_comm]

/-- **The window read**: for one-hot chunks encoding `σ`, `T_s(e_0)·Π_{i ≥ 1} ẽ_i(r_i)` is
`eq(r, σ + s)` when `(σ mod 2^{w_0}) + s < 2^{w_0}`, and `0` otherwise: a read past the window is
zero, as `Functionals` documents. The index read is the prover's `Chunks::shifted(σ, s)`: `σ + s`,
`None` past the window. -/
theorem window_read (r0 : List F) (rs : List (List F)) (e0 : ℕ → F) (es : List (ℕ → F)) (σ s : ℕ)
    (h : Encodes (r0 :: rs) (e0 :: es) σ) :
    windowShift r0 e0 s * chunksEval rs es =
      if σ % 2 ^ r0.length + s < 2 ^ r0.length then eqAt (r0 :: rs).flatten (σ + s) else 0 := by
  obtain ⟨he, hes⟩ := h
  have hpos : 0 < 2 ^ r0.length := Nat.two_pow_pos _
  rw [windowShift_oneHot r0 e0 _ s he (Nat.mod_lt _ hpos), chunksEval_eq rs es _ hes]
  split_ifs with hw
  · have hσ : σ + s = (σ % 2 ^ r0.length + s) + 2 ^ r0.length * (σ / 2 ^ r0.length) := by
      have := Nat.mod_add_div σ (2 ^ r0.length); omega
    rw [List.flatten_cons, eqAt_append, hσ, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hw,
      Nat.zero_add, eqAt_mod r0 (_ + 2 ^ r0.length * _), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]
  · rw [zero_mul]

/-- **The block sum**: over any set `S` of shifts and coefficients `ξ`,
`Σ_{s ∈ S} ξ_s·T_s(e_0)·Π_{i ≥ 1} ẽ_i(r_i) = Σ_{s ∈ S, (σ mod 2^{w_0}) + s < 2^{w_0}} ξ_s·eq(r, σ + s)`,
the low factor of `Functionals::summand` (`c·D_0 + Σ_s c_s·T_s`, `D_0 = T_0`) times its product
over the other chunks. -/
theorem sum_window_read (r0 : List F) (rs : List (List F)) (e0 : ℕ → F) (es : List (ℕ → F))
    (σ : ℕ) (h : Encodes (r0 :: rs) (e0 :: es) σ) (S : Finset ℕ) (ξ : ℕ → F) :
    ∑ s ∈ S, ξ s * windowShift r0 e0 s * chunksEval rs es =
      ∑ s ∈ S with σ % 2 ^ r0.length + s < 2 ^ r0.length, ξ s * eqAt (r0 :: rs).flatten (σ + s) := by
  rw [sum_filter]
  refine sum_congr rfl fun s _ => ?_
  rw [mul_assoc, window_read r0 rs e0 es σ s h, mul_ite, mul_zero]

end

end LeanVM.Protocol.Hotwire
