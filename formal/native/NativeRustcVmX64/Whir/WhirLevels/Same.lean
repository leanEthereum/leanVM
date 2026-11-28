module

public import NativeRustcVm.Whir.Basis
public import NativeRustcVm.Tables.Same

/-!
# WHIR's representations over bytes that stayed the same

A representation `whir_levels` carries across a block or a call holds in a memory whose bytes over
it are the same (`NativeRustcVm.Layout.Same`): the state (`WhirStateAt.of_same`), the phase-7
state with its rounds (`WhirAt.of_same`), the levels (`LevelAt.of_same`), the basis and the areas
it names (`basisWAt_of_same`, as the AArch64 proof's, restated here).
-/

namespace NativeRustcVmX64.Whir.Levels

open NativeVm.Model NativeRustcVm NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr
open NativeRustcVm.Transcript (off)

public section

variable {d d' : Mem 64}

theorem bufWordsAt_of_same {a : BitVec 64} {N : Nat} {xs : List UInt64} {n : Nat}
    (h : BufWordsAt d a N xs) (hs : Same d d' a n) (hl : 8 + 8 * N ≤ n) : BufWordsAt d' a N xs := by
  obtain ⟨hle, hw, he⟩ := h
  refine ⟨hle, WordAt.of_same hw hs (by omega), Tables.WordsAt.of_same he
    (hs.sub (o := 8) (k := 8 * N) (by omega)) (by omega)⟩

theorem gluedAt_of_same {a : BitVec 64} {g : GluedClaimW} (h : GluedAt d a g)
    (hs : Same d d' a gluedBytes) : GluedAt d' a g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨EWAt.of_same h1 hs (by decide), h2,
    WordAt.of_same h3 (hs.sub (o := 16) (k := 8) (by decide)) le_rfl, ?_⟩
  cases hg : g.weight with
  | eq z =>
    rw [hg] at h4
    exact ⟨WordAt.of_same h4.1 (hs.sub (o := 24) (k := 8) (by decide)) le_rfl,
      BufEWAt.of_same h4.2 (hs.sub (o := 40) (k := 488) (by decide)) (by decide)⟩
  | induced mu qs ws =>
    rw [hg] at h4
    obtain ⟨k1, k2, k3, k4, k5⟩ := h4
    exact ⟨WordAt.of_same k1 (hs.sub (o := 24) (k := 8) (by decide)) le_rfl, k2,
      WordAt.of_same k3 (hs.sub (o := 32) (k := 8) (by decide)) le_rfl,
      bufWordsAt_of_same k4 (hs.sub (o := 528) (k := 1848) (by decide)) (by decide),
      BufEWAt.of_same k5 (hs.sub (o := 2376) (k := 3688) (by decide)) (by decide)⟩

/-- **WHIR's state** over bytes that stayed the same. -/
theorem WhirStateAt.of_same {p : BitVec 64} {w : WhirStateW} (h : WhirStateAt d p w)
    (hs : Same d d' p stateBytes) : WhirStateAt d' p w where
  claim := EWAt.of_same h.claim hs (by decide)
  alphas := BufEWAt.of_same h.alphas (hs.sub (o := 16) (k := 488) (by decide)) (by decide)
  glued_le := h.glued_le
  glued_len := WordAt.of_same h.glued_len (hs.sub (o := 504) (k := 8) (by decide)) le_rfl
  glued i hi := gluedAt_of_same (h.glued i hi) (hs.sub (o := 504 + 8 + 6064 * i) (k := 6064) (by
    have := h.glued_le
    have hi' : i < w.glued.size := hi
    show 504 + 8 + 6064 * i + 6064 ≤ 61152
    unfold gluedCap at this
    omega))

theorem bufRoundsAt_of_same {a : BitVec 64} {rs : List FoldRoundW} (h : BufRoundsAt d a rs)
    (hs : Same d d' a (8 + roundBytes * roundCap)) : BufRoundsAt d' a rs := by
  obtain ⟨hle, hw, he⟩ := h
  refine ⟨hle, WordAt.of_same hw hs (by decide), Tables.EWsAt.of_same he
    (hs.sub (o := 8) (k := roundBytes * roundCap) (by decide)) ?_⟩
  have : (roundEWs rs).length = 2 * rs.length := by
    unfold roundEWs
    rw [List.length_flatMap]
    simp [Nat.mul_comm]
  rw [this]
  unfold roundCap at hle
  unfold roundBytes roundCap
  omega

/-- **The phase-7 state** over bytes that stayed the same. -/
theorem WhirAt.of_same {p : BitVec 64} {w : WhirStateW} {rs : Array FoldRoundW}
    (h : WhirAt d p w rs) (hs : Same d d' p whirBytes) : WhirAt d' p w rs :=
  ⟨WhirStateAt.of_same h.1 fun j hj ↦ hs j (by unfold stateBytes at hj; unfold whirBytes; omega),
    bufRoundsAt_of_same h.2 (hs.sub (o := roundsOff) (k := 8 + roundBytes * roundCap) (by decide))⟩

theorem LevelAt.of_same {p : BitVec 64} {l : LeanVM.Parameters.Whir.Level} (h : LevelAt d p l)
    (hs : Same d d' p levelBytes) : LevelAt d' p l :=
  ⟨h.1, h.2.1, h.2.2.1, Tables.WordsAt.of_same h.2.2.2 hs (by simp [levelBytes])⟩

theorem ringWAt_of_same {p : BitVec 64} {target : EW} {cs : Array EW} (h : RingWAt d p target cs)
    (hs : Same d d' p ringWBytes) : RingWAt d' p target cs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨EWAt.of_same h1 hs (by decide), h2,
    Tables.EWsAt.of_same h3 (hs.sub (o := 16) (k := 16 * coeffCount) (by decide)) ?_⟩
  rw [Array.length_toList, h2]

theorem keccakOutAt_of_same {p : BitVec 64} {point slices : Array EW}
    (h : KeccakOutAt d p point slices) (hs : Same d d' p outBytes) :
    KeccakOutAt d' p point slices := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨BufEWAt.of_same h1 hs (by decide), h2,
    Tables.EWsAt.of_same h3 (hs.sub (o := slicesOff) (k := 16 * 64) (by decide)) ?_⟩
  rw [Array.length_toList, h2]

theorem eqClaimAt_of_same {p : BitVec 64} {z : Array EW} {v : EW} (h : EqClaimAt d p z v)
    (hs : Same d d' p eqClaimBytes) : EqClaimAt d' p z v :=
  ⟨BufEWAt.of_same h.1 hs (by decide),
    EWAt.of_same h.2 (hs.sub (o := 488) (k := 16) (by decide)) le_rfl⟩

/-- **The basis** over bytes that stayed the same. -/
theorem basisWAt_of_same {p : BitVec 64} {ba : BasisAddrs} {b : BasisW} (h : BasisWAt d p ba b)
    (hp : Same d d' p basisBytes) (hr : ∀ r ∈ ba.regions, Same d d' r.addr r.size) :
    BasisWAt d' p ba b := by
  have h0 := hr ⟨ba.scales, 16 * ba.count⟩ (by simp [BasisAddrs.regions])
  have h1 := hr ⟨ba.layout, layoutBytes⟩ (by simp [BasisAddrs.regions])
  have h2 := hr ⟨ba.ring, ringWBytes⟩ (by simp [BasisAddrs.regions])
  have h3 := hr ⟨ba.keccak, outBytes⟩ (by simp [BasisAddrs.regions])
  have h4 := hr ⟨ba.claims, claimsBytes⟩ (by simp [BasisAddrs.regions])
  have h5 := hr ⟨ba.ood, eqClaimBytes⟩ (by simp [BasisAddrs.regions])
  obtain ⟨hlt, hw, hsz, hsc, ⟨L, t, cs, pt, sl, ccs, z, v, hL, hLa, hR, hK, hC, hE, heq⟩⟩ := h
  refine ⟨hlt, Tables.WordsAt.of_same hw hp (by simp [basisBytes]), hsz,
    Tables.EWsAt.of_same hsc h0 (by simp [hsz]),
    ⟨L, t, cs, pt, sl, ccs, z, v, hL, Tables.LayoutWAt.of_same hLa h1, ringWAt_of_same hR h2,
      keccakOutAt_of_same hK h3, Tables.ClaimsWAt.of_same hC h4, eqClaimAt_of_same hE h5, heq⟩⟩

end

end NativeRustcVmX64.Whir.Levels
