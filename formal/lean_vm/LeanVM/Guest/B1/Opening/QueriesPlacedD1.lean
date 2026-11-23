/-
  LeanVM.Guest.B1.Opening.QueriesPlacedD1

  The honest data of a call of `opening_queries`, as the caller's words.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedL
public import LeanVM.Guest.B1.Opening.QueriesMainW
public import LeanVM.Guest.AcceptableChild

/-!
# A call's honest data

The honest data of a call at a level of cap depth `cd`: the iterations `N`, the rounds'
challenges `rounds`, the final coefficients `hsv` (final level), the queries' positions `qs`, rows
`rows` and siblings below the cap `sibs` (`oqW`), the window runs at `g^(eb k)`; the caller's
buffers at `g^ecap` (the cap, offset to its leaves), `g^eflags` (the flags, offset likewise),
`g^ecoefs` (the challenges), `g^ehs` (the final coefficients), `g^epos` (the points), `g^eqp` (the
window pointers).

* `OqLinMem`: what every memory holding the caller's words `Lin` holds: the challenges, the final
  coefficients, the points, the window pointers and windows, each query's cap leaf (its path's
  top) and its flag;
* `OqLinReg`: those words lie in `Lin`'s region;
* `OqStatic`: the opening's facts of each query: the position's range, the lengths, at the final
  level the fold the final polynomial at the point.

`oqQReg_of`, `qdOk_of_lin`: a query's region and `QD.Ok` from them; `oqRet_eq`: the returned chain
of the queries' results is that of their folds.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- A query's witness from the call's data: its position, its row, its siblings below the cap. -/
def oqW (qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest) (k : ℕ) : QW :=
  (qs k, rows k, sibs k)

/-- **What the memory holds of `opening_queries`' caller's words**: the rounds' challenges at
`coefs`, (final level) the final coefficients at `hs`, and for each query `k < Q` its point
`positions[k] = eOfNat (qs k)`, its window pointer `qptrs[k] = g^(eb k)`, its position's windows
there (`g^qwVal`), its cap leaf (its path's top, at `cap` offset to the cap's leaves) and its
parent's flag (at `flags` offset likewise). -/
def OqLinMem (rd : Reader) (s : Oq) (cd : ℕ) (cap flags coefs hs positions qptrs : E)
    (rounds : List FoldRound) (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K)
    (sibs : ℕ → List Digest) (Q : ℕ) : Prop :=
  RoundsAt rd coefs rounds ∧ (s.final = 1 → WordsAt rd hs hsv) ∧
    ∀ k < Q, LoadHolds rd positions k (eOfNat (qs k)) ∧
      LoadHolds rd qptrs k (ofK (Parameters.addressOfIndex (eb k))) ∧
      (∀ i < qwN (s.pd + cd) cd, LoadHolds rd (ofK (Parameters.addressOfIndex (eb k))) i
        (gen ^ qwVal (s.pd + cd) cd (qs k) i)) ∧
      LoadHolds rd cap (2 * (qs k / 2 ^ s.pd))
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).1 ∧
      LoadHolds rd cap (2 * (qs k / 2 ^ s.pd) + 1)
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).2 ∧
      LoadHolds rd flags (qs k / 2 ^ (s.pd + 1)) 1

/-- **Where those words lie**: in the region `R`. -/
def OqLinReg (R : ℕ → Prop) (s : Oq) (cd : ℕ) (ecap eflags ecoefs ehs epos eqp : ℕ) (eb qs : ℕ → ℕ)
    (Q : ℕ) : Prop :=
  (∀ l < 2 * s.folds, R (ecoefs + l)) ∧ (s.final = 1 → ∀ l < s.nHs, R (ehs + l)) ∧
    ∀ k < Q, R (epos + k) ∧ R (eqp + k) ∧ (∀ i < qwN (s.pd + cd) cd, R (eb k + i)) ∧
      R (eflags + qs k / 2 ^ (s.pd + 1)) ∧ ∀ e < 2, R (ecap + (2 * (qs k / 2 ^ s.pd) + e))

/-- **The opening's static facts** of the queries `k < Q`: the position below `2^(pd + cd)`, the
row's and the siblings' lengths, and (final level) the fold the final polynomial at the point. -/
def OqStatic (s : Oq) (cd : ℕ) (rounds : List FoldRound) (hsv : List E) (qs : ℕ → ℕ)
    (rows : ℕ → List K) (sibs : ℕ → List Digest) (Q : ℕ) : Prop :=
  ∀ k < Q, qs k < 2 ^ (s.pd + cd) ∧ (rows k).length = rowLen s.base s.folds ∧
    (sibs k).length = s.pd ∧
    (s.final = 1 → foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds =
      novelSum hsv (wsChain (s.vs.map K.ofBits) (eOfNat (qs k))) s.nHs s.hsBits)

theorem cap_index (q pd e : ℕ) :
    4 * (q / 2 ^ (pd + 1)) + (if q.testBit pd then 2 else 0) + e = 2 * (q / 2 ^ pd) + e := by
  have hsplit : q / 2 ^ pd = 2 * (q / 2 ^ (pd + 1)) + (if q.testBit pd then 1 else 0) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    by_cases h : q / 2 ^ pd % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  rw [hsplit]
  split <;> ring

theorem limb_addr (b k : ℕ) : (ofK (Parameters.addressOfIndex b)).limb 0 *
    Parameters.addressOfIndex k =
    Parameters.addressOfIndex (b + k) := Main.addr_ofK b k

/-- The query region `OqQReg` from `OqLinReg`. -/
theorem oqQReg_of {R : ℕ → Prop} {s : Oq} {cd ecap eflags ecoefs ehs epos eqp : ℕ}
    {eb qs : ℕ → ℕ} {Q : ℕ} (h : OqLinReg R s cd ecap eflags ecoefs ehs epos eqp eb qs Q) {k : ℕ}
    (hk : k < Q) :
    OqQReg R s (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
      (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
      (ofK (Parameters.addressOfIndex (eb k))) (qs k) := by
  obtain ⟨-, -, b, f, c⟩ := h.2.2 k hk
  refine ⟨fun off ho ↦ ⟨_, limb_addr _ _, h.1 off ho⟩,
    fun hf off ho ↦ ⟨_, limb_addr _ _, h.2.1 hf off ho⟩,
    fun off ho ↦ ⟨_, limb_addr _ _, b off (by rw [qwN_eq]; exact ho)⟩,
    ⟨_, by rw [addr_gpow, Nat.add_zero], f⟩, fun e he ↦ ⟨_, by rw [addr_gpow], ?_⟩⟩
  rw [Nat.add_assoc, cap_index _ _ _]
  exact c e he

theorem regionL_nil (i : ℕ) : ¬ RegionL [] i := by simp [RegionL]

/-- Query `k`'s `QD.Ok` from the memory and the static facts. -/
theorem qdOk_of_lin {rd : Reader} {s : Oq} {cd : ℕ} (hcd : 1 ≤ cd)
    {cap flags coefs hsp positions qptrs : E}
    {rounds : List FoldRound} {hsv : List E} {eb qs : ℕ → ℕ} {rows : ℕ → List K}
    {sibs : ℕ → List Digest} {Q : ℕ} (hrl : rounds.length = s.folds)
    (hhl : s.final = 1 → hsv.length = s.nHs) (hst : OqStatic s cd rounds hsv qs rows sibs Q)
    (hm : OqLinMem rd s cd cap flags coefs hsp positions qptrs rounds hsv eb qs rows sibs Q)
    {k : ℕ} (hk : k < Q) (b : ℕ) (emit : Bool) (pr : ℕ) :
    (oqQD s cd b emit pr (ofK (Parameters.addressOfIndex (eb k))) cap flags rounds hsv
      (oqW qs rows sibs k)).Ok rd coefs hsp := by
  obtain ⟨hR, hW, hk'⟩ := hm
  obtain ⟨-, -, a2, a3, a4, a5⟩ := hk' k hk
  obtain ⟨qa, ra, sa, fa⟩ := hst k hk
  exact qdOk_of_mem hcd ra sa qa a2 a3 a4 a5 hR hrl fun hf ↦ ⟨hW hf, hhl hf, fa hf⟩

/-- The chain's words: the queries' results. -/
theorem oqResV_W {s : Oq} {rounds : List FoldRound} {qs : ℕ → ℕ} {rows : ℕ → List K}
    {sibs : ℕ → List Digest} (hf : s.final ≠ 1) (k : ℕ) :
    oqResV s rounds (oqW qs rows sibs k) = foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds := by
  simp only [oqResV, hf, ↓reduceIte]
  rfl

/-- The returned word: at a non-final level the chain of the queries' results is that of their
folds. -/
theorem oqRet_eq (s : Oq) (odd : ℕ) (lamInv : E) (rounds : List FoldRound) (qs : ℕ → ℕ)
    (rows : ℕ → List K) (sibs : ℕ → List Digest) (N : ℕ) :
    (if s.final = 1 then 0 else
      oqChain odd s.base lamInv (fun k ↦ oqResV s rounds (oqW qs rows sibs k)) N) =
    (if s.final = 1 then 0 else
      oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N) := by
  by_cases hf : s.final = 1
  · simp only [hf, ↓reduceIte]
  · simp only [hf, ↓reduceIte]
    congr 1
    funext k
    exact oqResV_W hf k

end
end LeanVM.Guest.B1
