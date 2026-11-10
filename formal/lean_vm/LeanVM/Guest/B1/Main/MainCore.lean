/-
  LeanVM.Guest.B1.Main.MainCore

  `main`'s honest valuation: its body evaluated on the honest hints, `HeapBuf`s and calls' returns
  (`mOrc`), and what holds of it on a memory holding `main`'s honest words.
-/

module

public import LeanVM.Guest.B1.Main.MainLocChk
public import LeanVM.Guest.B1.Digest.ChainFilter
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Digest.Range
public import LeanVM.Guest.B1.Digest.CoverComplete

/-!
# `main`'s honest valuation

`MainIn`: what `main`'s oracle supplies (the counts of `meta`, the seed, the exponent table's
pointer, its `HeapBuf`s, the digests its callees return, the picked DA slot, the leaf's deferred
value); `mσ rd m` is `mFlatE` evaluated on it (`Fwd.ev`). `main_core`: on a memory defined below
`2^16` (the range checks) holding `main`'s stored and read words (`MainMem`: the byte table, the
first and last running counts, the own and the published DA digests, the leaf's deferred claim,
the header), for counts within their bounds (`MainBounds`), every atom of the executed blocks
holds and the words `main` passes to its callees are the honest ones (`MVals`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The oracle -/

/-- **What `main`'s oracle supplies.** -/
structure MainIn where
  nlx : ℕ
  nxd : ℕ
  nrx : ℕ
  nls : ℕ
  nsd : ℕ
  nrs : ℕ
  nc : ℕ
  nd : ℕ
  pick : ℕ
  seed : Digest
  et : E
  a77 : E
  a80 : E
  a117 : E
  a119 : E
  aDa : E
  a394 : E
  a400 : E
  a406 : E
  a409 : E
  a417 : E
  xd : Digest
  sd : Digest
  sdg : Digest
  daR : List E
  dap : Digest
  leaf : E

/-- The counts of `meta`. -/
def MainIn.cnt (m : MainIn) : List ℕ := [m.nlx, m.nxd, m.nrx, m.nls, m.nsd, m.nrs, m.nc, m.nd]

/-- The coverage table's slots. -/
def MainIn.total (m : MainIn) : ℕ := m.nlx + m.nxd + (m.nls + m.nsd)

/-- The own DA digest's cells: the checked claim's digest, or zeros. -/
noncomputable def MainIn.ownDa (m : MainIn) : List E :=
  if m.nd = 1 then digestCells (keccak256 (cellsBytes m.daR)) else [0, 0]

/-- **`main`'s oracle**: hints, `HeapBuf`s, calls' returns. -/
noncomputable def mOrc (m : MainIn) (j : ℕ) : E :=
  if j < 8 then gen ^ m.cnt.getD j 0
  else if j = 47 then (digestHalves m.seed).1 else if j = 48 then (digestHalves m.seed).2
  else if j = 49 then m.et
  else if j = 52 then m.a77 else if j = 55 then m.a80
  else if j = 56 then (digestHalves m.xd).1 else if j = 57 then (digestHalves m.xd).2
  else if j = 58 then (digestHalves m.sd).1 else if j = 59 then (digestHalves m.sd).2
  else if j = 66 then m.a117 else if j = 68 then m.a119 else if j = 385 then m.aDa
  else if 390 ≤ j ∧ j < 394 then m.daR.getD (j - 390) 0
  else if j = 405 then m.a394 else if j = 411 then m.a400 else if j = 417 then m.a406
  else if j = 420 then m.a409 else if j = 427 then gen ^ m.pick else if j = 438 then m.a417
  else if j = 441 then m.leaf
  else if j = 467 then (digestHalves m.sdg).1 else if j = 468 then (digestHalves m.sdg).2
  else 0

/-- **`main`'s honest valuation.** -/
noncomputable def mσ (rd : Reader) (m : MainIn) : Val := B1.Val.ofArgs (ev rd (mOrc m) [] mFlatE)

/-- The counts' bounds (the range checks'), the picked DA slot, the checked claim's cells. -/
structure MainBounds (m : MainIn) : Prop where
  lx : m.nlx ≤ 65535
  xd : m.nxd ≤ 65535
  rx : m.nrx ≤ 65535
  ls : m.nls ≤ 65535
  sd : m.nsd ≤ 65535
  rs : m.nrs ≤ 65535
  nc : m.nc ≤ 16
  nd : m.nd ≤ 1
  total : m.total ≤ 65535
  pick : m.pick ≤ m.nc
  pickD : m.nd = 1 → m.pick = m.nc
  daR : m.nd = 1 → m.daR.length = 4

/-- **The words `main` stores or reads in its buffers and its header.** -/
structure MainMem (rd : Reader) (m : MainIn) : Prop where
  bytes : ReadsAt rd m.a119 ((List.range 256).map fun v => word v 0)
  w0 : LoadHolds rd m.a409 0 (gen ^ (m.nrx + m.nrs))
  wN : LoadHolds rd (m.a409 * gen ^ m.nc) 0 (gen ^ m.total)
  own : ReadsAt rd (m.aDa * gen ^ (2 * m.nc)) m.ownDa
  dap : ReadsAt rd (m.aDa * gen ^ (2 * m.pick)) (digestCells m.dap)
  leaf : m.nc = 0 → ReadsAt rd m.a417 (List.replicate 23 0 ++ [m.leaf])
  h0 : LoadHolds rd 1 0 (digestHalves m.sdg).1
  h1 : LoadHolds rd gen 0 (digestHalves m.sdg).2

/-- **What holds of `main`'s honest valuation.** -/
structure MVals (rd : Reader) (σ : Val) (m : MainIn) : Prop where
  pre : ∀ a ∈ atomsIn mPre, a.Holds rd σ
  mid : ∀ a ∈ atomsIn mMid, a.Holds rd σ
  post : ∀ a ∈ atomsIn mPost, a.Holds rd σ
  da : m.nd = 1 → ∀ a ∈ atomsIn mDa, a.Holds rd σ
  daZ : m.nd ≠ 1 → ∀ a ∈ atomsIn mDaZ, a.Holds rd σ
  leaf : m.nc = 0 → ∀ a ∈ atomsIn mLeaf, a.Holds rd σ
  orc : ∀ j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 47, 48, 49, 52, 55, 56, 57, 58, 59, 66, 68, 385, 390,
    391, 392, 393, 405, 411, 417, 420, 427, 438, 441, 467, 468], σ (.n j) = mOrc m j
  v40 : σ (.n 40) = gen ^ (m.nlx + m.nxd)
  v41 : σ (.n 41) = gen ^ (m.nls + m.nsd)
  v42 : σ (.n 42) = gen ^ m.total
  v51 : σ (.n 51) = gen ^ (4 * (m.nlx + m.nxd))
  v54 : σ (.n 54) = gen ^ (4 * (m.nls + m.nsd))
  g61 : σ (.n 61) = 1 + gen ^ m.nxd
  g62 : σ (.n 62) = 1
  g64 : σ (.n 64) = 1 + gen ^ m.nsd
  g65 : σ (.n 65) = 1
  v67 : σ (.n 67) = m.a117 * gen ^ (m.nlx + m.nxd)
  g377 : σ (.n 377) = 1 + gen ^ m.nrx
  g378 : σ (.n 378) = 1
  g380 : σ (.n 380) = 1 + gen ^ m.nrs
  g381 : σ (.n 381) = 1
  v384 : σ (.n 384) = gen ^ (2 * (m.nc + 1))
  v387 : σ (.n 387) = m.aDa * gen ^ (2 * m.nc)
  v389 : σ (.n 389) = gen ^ m.nd + gen
  v415 : σ (.n 404) = gen ^ (2 * m.nc)
  v421 : σ (.n 410) = gen ^ (24 * m.nc)
  v427 : σ (.n 416) = gen ^ (24 * m.nc)
  v430 : σ (.n 419) = gen ^ (m.nc + 1)
  v432 : σ (.n 421) = gen ^ (m.nrx + m.nrs)
  g434 : σ (.n 423) = 1 + gen ^ m.nc
  g435 : σ (.n 424) = 1
  v436 : σ (.n 425) = m.a409 * gen ^ m.nc
  v448 : σ (.n 437) = m.aDa * gen ^ (2 * m.pick)
  v451 : σ (.n 440) = gen ^ m.nc + 1
  r476 : σ (.n 465) = (digestHalves m.dap).1
  r477 : σ (.n 466) = (digestHalves m.dap).2
  v480 : σ (.n 469) = 1
  v484 : σ (.n 473) = gen
  tags : lxTagsV.map σ = lxTagWords

/-! ## Helpers -/

theorem mem_atomsIn' {ss : List Stmt} {a : Atom} (h : Stmt.atom a ∈ ss) : a ∈ atomsIn ss :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem atom_mem_of_atomsIn' {ss : List Stmt} {a : Atom} (h : a ∈ atomsIn ss) : Stmt.atom a ∈ ss := by
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp h
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact hs

theorem gpow_mul_zero (e : ℕ) : (gen ^ e).limb 0 * Parameters.addressOfIndex 0 =
    Parameters.addressOfIndex e := by
  rw [gen_pow_eq_ofK]; simp [Parameters.addressOfIndex]

/-- A range check of `g^e` against `g^K` passes on a memory defined below `2^16`. -/
theorem rc_side {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} (hl : Sig.MemOK rd (2 ^ 16))
    {x y t1 t2 k : V} {e K : ℕ} (hx : σ x = gen ^ e) (hk : σ k = gen ^ K) (heK : e ≤ K)
    (hK : K < 2 ^ 16) (hlt : k.idx < y.idx) (hg : Good rd S w σ (.rangeCheck x y t1 t2 k)) :
    Side rd S σ (.rangeCheck x y t1 t2 k) := by
  simp only [Good] at hg
  rw [ite_pos' hlt] at hg
  have hy : σ y = gen ^ (K - e) := by
    rw [hg.2.2, hk, hx, show K = (K - e) + e by omega, pow_add, mul_inv_cancel_right₀
      (pow_ne_zero _ gen_ne_zero), Nat.add_sub_cancel]
  simp only [Side]
  rw [ite_pos' hlt, hx, hy, gpow_mul_zero, gpow_mul_zero]
  exact ⟨gen_pow_isInK _, hl _ (by omega), gen_pow_isInK _, hl _ (by omega),
    pow_ne_zero _ gen_ne_zero⟩

theorem good_mul' {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : ℕ} (hx : x < d)
    (hy : y < d) (h : Good rd S w σ (.mul (.n d) (.n x) (.n y))) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

theorem one_add_ne' {a : ℕ} (ha : a < 2 ^ 64 - 1) (h0 : a ≠ 0) : (1 : E) + gen ^ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]; exact h0

/-- The values a statement defines from the oracle. -/
def defsOf : Stmt → List V
  | .atom (.hint (.witness _ (.stack vs))) => vs
  | .atom (.hint (.alloc d _)) => [d]
  | .atom (.hint (.allocDyn d _)) => [d]
  | .call _ _ rets => rets
  | _ => []

theorem goodS_defs {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {s : Stmt}
    (h : GoodS rd S w σ s) : ∀ v ∈ defsOf s, σ v = w v.idx := by
  intro v hv
  cases s with
  | atom a =>
    cases a with
    | hint hh =>
      cases hh with
      | witness n sp =>
        cases sp with
        | stack vs => exact h v hv
        | heap => simp [defsOf] at hv
      | alloc d n =>
        simp only [defsOf, List.mem_singleton] at hv
        subst hv
        exact h
      | allocDyn d n =>
        simp only [defsOf, List.mem_singleton] at hv
        subst hv
        exact h
      | _ => simp [defsOf] at hv
    | _ => simp [defsOf] at hv
  | call f args rets => exact h v hv
  | _ => simp [defsOf] at hv

/-- The oracle's values, as `MVals.orc` lists them. -/
def mOrcIdx : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 47, 48, 49, 52, 55, 56, 57, 58, 59, 66, 68, 385,
  390, 391, 392, 393, 405, 411, 417, 420, 427, 438, 441, 467, 468]

set_option maxRecDepth 100000 in
theorem mOrcIdx_defs : ∀ j ∈ mOrcIdx, ∃ s ∈ mOrcStmts, V.n j ∈ defsOf s := by decide +kernel

end
end LeanVM.Guest.B1.Main
