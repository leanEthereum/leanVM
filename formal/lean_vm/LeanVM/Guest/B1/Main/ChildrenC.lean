/-
  LeanVM.Guest.B1.Main.ChildrenC

  `main`'s loop over its children (`__loop5`, G:3248-3290) backward: per child, its claim lists'
  digests, its signer set, its DA roots, its statement's digest and its proof's verification, from
  its callees' relations and the honest words in memory.
-/

module

public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.B1.Main.Children

/-!
# The children, backward

`loop5_back`: at `x = g^c`, the running count `base` at `written[c]`, the two claim lists'
digests (`child_claim_list_digest`), their signer set's compression stored in a fresh pair, the
child's DA roots (`__loop100`, entered when it has some) and their digest, the statement's digest
stored at `child_pi·g^(2c)`, `verify_sub` on it, and the next count `base·g^(n_x + n_s + n_da)` at
`written[c + 1]` give the iteration, its callees at one depth. `loop5_complete`: every child.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-- The words one child's iteration reads and writes. -/
structure ChildRun where
  /-- The running count at `written[c]`. -/
  base : E
  /-- The child's leanXMSS claims. -/
  nx : ℕ
  /-- Its leanSPHINCS claims. -/
  ns : ℕ
  /-- Its DA claims. -/
  nda : ℕ
  /-- The leanXMSS list's digest cells. -/
  dx0 : E
  dx1 : E
  /-- The leanSPHINCS list's digest cells. -/
  ds0 : E
  ds1 : E
  /-- The signer set's digest cells. -/
  o0 : E
  o1 : E
  /-- The fresh pair holding them. -/
  sigp : E
  /-- The child's DA roots' buffer. -/
  cda : E
  /-- The DA list's digest cells. -/
  r0 : E
  r1 : E
  /-- The statement's digest cells. -/
  p0 : E
  p1 : E

/-- **What iteration `c` of `__loop5` needs**, its callees at depth `d`. -/
structure ChildOk (rd : Reader) (d c : ℕ) (r : ChildRun) (written lxT cover lxS gsq spT spS carried daR
    daC daS seed0 seed1 cpi glp cfresh : E) : Prop where
  base : LoadHolds rd written c r.base
  nx : r.nx < 2 ^ 16
  ns : r.ns < 2 ^ 16
  nda : r.nda ≤ 16
  ccx : coreProgram.relN rd d "child_claim_list_digest"
    [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq] [r.dx0, r.dx1]
  ccs : coreProgram.relN rd d "child_claim_list_digest"
    [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq] [r.ds0, r.ds1]
  sig : CompressCells ![r.dx0, r.dx1, r.ds0, r.ds1] ivCells.1 ivCells.2 r.o0 r.o1
    (metadataCell 64 true)
  sigp : ReadsAt rd r.sigp [r.o0, r.o1]
  das : r.nda ≠ 0 → coreProgram.relN rd d "__loop100"
    [1, gen ^ r.nda, r.cda, daR, daC, daS, r.base, gen ^ r.nx * gen ^ r.ns] []
  dl : coreProgram.relN rd d "da_list_digest" [r.cda, gen ^ r.nda] [r.r0, r.r1]
  sd : coreProgram.relN rd d "statement_digest"
    [seed0, seed1, r.sigp, r.r0, r.r1, carried * gen ^ (53 * c)] [r.p0, r.p1]
  pi0 : LoadHolds rd cpi (2 * c) r.p0
  pi1 : LoadHolds rd cpi (2 * c + 1) r.p1
  vs : coreProgram.relN rd d "verify_sub" [r.p0, r.p1, seed0, seed1, glp, gsq, cfresh * gen ^ (106 * c)] []
  next : LoadHolds rd written (c + 1) (r.base * (gen ^ r.nx * gen ^ r.ns) * gen ^ r.nda)

theorem gen_pow_mul_gmax {e : ℕ} (he : e ≤ 65535) : gen ^ 65535 = gen ^ e * gen ^ (65535 - e) := by
  rw [← pow_add]; congr 1; omega

/-- **`__loop5` at `x = g^c`, backward.** -/
theorem loop5_back (hm : MemOk rd) {N written lxT cover lxS gsq spT spS carried daR daC daS seed0 seed1
    cpi glp cfresh : E} (d c : ℕ) (r : ChildRun)
    (h : ChildOk rd d c r written lxT cover lxS gsq spT spS carried daR daC daS seed0 seed1 cpi glp
      cfresh)
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 → coreProgram.relN rd d "__loop5" [gen ^ c * gen, N, written, lxT,
      cover, lxS, gsq, spT, spS, carried, daR, daC, daS, seed0, seed1, cpi, glp, cfresh] []) :
    coreProgram.relN rd (d + 1) "__loop5" [gen ^ c, N, written, lxT, cover, lxS, gsq, spT, spS, carried,
      daR, daC, daS, seed0, seed1, cpi, glp, cfresh] [] := by
  set x := gen ^ c with hx
  obtain ⟨a1, a2, l1, k1, l2⟩ := LeanVM.Guest.B1.Digest.rangeCheck_complete (rd := rd) hm (e := r.nx)
    (e' := 65535 - r.nx) h.nx (by omega)
  obtain ⟨b1, b2, m1, k2, m2⟩ := LeanVM.Guest.B1.Digest.rangeCheck_complete (rd := rd) hm (e := r.ns)
    (e' := 65535 - r.ns) h.ns (by omega)
  obtain ⟨c1, c2, n1, k3, n2⟩ := LeanVM.Guest.B1.Digest.rangeCheck_complete (rd := rd) hm (e := r.nda)
    (e' := 16 - r.nda) (by have := h.nda; omega) (by omega)
  rw [relN_succ_iff find_loop5]
  refine ⟨setl (Val.ofArgs [x, N, written, lxT, cover, lxS, gsq, spT, spS, carried, daR, daC, daS,
      seed0, seed1, cpi, glp, cfresh]) 18
    [written * x, r.base, gen ^ r.nx, gen ^ r.ns, gen ^ 65535, gen ^ (65535 - r.nx), a1, a2,
      gen ^ 65535, gen ^ (65535 - r.ns), b1, b2, gen ^ r.nx * gen ^ r.ns, 1, r.dx0, r.dx1,
      r.base * gen ^ r.nx, r.ds0, r.ds1, ivCells.1, ivCells.2, metadataCell 64 true, r.o0, r.o1,
      r.sigp, gen ^ (2 * c), gen ^ (3 * c), gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c),
      gen ^ (26 * c), gen ^ (52 * c), gen ^ (53 * c), carried * gen ^ (53 * c), gen ^ r.nda,
      gen ^ 16, gen ^ (16 - r.nda), c1, c2, gen ^ r.nda * gen ^ r.nda,
      gen ^ r.nda * gen ^ r.nda * (gen ^ r.nda * gen ^ r.nda), r.cda, 1, 1 + gen ^ r.nda, 1, r.r0,
      r.r1, r.p0, r.p1, gen ^ (2 * c), cpi * gen ^ (2 * c), cpi * gen ^ (2 * c), gen ^ (2 * c),
      gen ^ (3 * c), gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c), gen ^ (26 * c), gen ^ (52 * c),
      gen ^ (53 * c), gen ^ (106 * c), cfresh * gen ^ (106 * c), r.base * (gen ^ r.nx * gen ^ r.ns),
      r.base * (gen ^ r.nx * gen ^ r.ns) * gen ^ r.nda, written * x, gen, x * gen, x * gen + N, gen,
      x * gen], by
      simp only [show Fn.params Data.core35 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8,
        .n 9, .n 10, .n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17] from rfl, List.map_cons,
        List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core35 = Data.core35.body from rfl, Data.core35.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen, word_one,
    word_iv0, word_iv1, word_md64, word_gmax, word_g16]
  b1_look
  simp only [true_and, and_true]
  have hKd : IsInK (1 + gen ^ r.nda) :=
    isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK _)
  exact ⟨loadHolds_of_mul0 rfl h.base, ⟨l1, gen_pow_mul_gmax (by have := h.nx; omega), l2⟩,
    ⟨m1, gen_pow_mul_gmax (by have := h.ns; omega), m2⟩, h.ccx, h.ccs, rfl, rfl, h.sig,
    by simpa using h.sigp 0 (by simp), by simpa using h.sigp 1 (by simp), by ring, by ring, by ring,
    by ring, by ring, by ring, by ring, by ring,
    ⟨n1, by rw [← pow_add]; congr 1; have := h.nda; omega, n2⟩, hKd,
    fun hne => h.das fun h0 => hne (by rw [h0, pow_zero]; exact e_add_eq_zero_iff.mpr rfl), h.dl,
    h.sd, by ring, loadHolds_of_mul0 rfl h.pi0, loadHolds_of_mul rfl h.pi1, by ring, by ring, by ring,
    by ring, by ring, by ring, by ring, by ring, by ring, h.vs, loadHolds_of_mul rfl h.next, hK,
    hnext⟩

/-- Finitely many relations, each under its condition, hold at one depth. -/
theorem rel_uniform_if {F : ℕ → String} {A R : ℕ → List E} {Q : ℕ → Prop} :
    ∀ m : ℕ, (∀ j < m, Q j → coreProgram.Rel rd (F j) (A j) (R j)) →
      ∃ D, ∀ j < m, Q j → coreProgram.relN rd D (F j) (A j) (R j)
  | 0, _ => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, h => by
    classical
    obtain ⟨D, hD⟩ := rel_uniform_if m fun j hj => h j (by omega)
    by_cases hq : Q m
    · obtain ⟨D', hD'⟩ := h m (by omega) hq
      refine ⟨max D D', fun j hj hqj => ?_⟩
      rcases Nat.lt_or_ge j m with hj' | hj'
      · exact relN_mono coreProgram (le_max_left _ _) _ _ _ (hD j hj' hqj)
      · rw [show j = m by omega]; exact relN_mono coreProgram (le_max_right _ _) _ _ _ hD'
    · refine ⟨D, fun j hj hqj => ?_⟩
      rcases Nat.lt_or_ge j m with hj' | hj'
      · exact hD j hj' hqj
      · exact absurd (show j = m by omega ▸ hqj) hq

/-- **What iteration `c` of `__loop5` needs**, its callees' relations at any depth. -/
structure ChildOkR (rd : Reader) (c : ℕ) (r : ChildRun) (written lxT cover lxS gsq spT spS carried daR
    daC daS seed0 seed1 cpi glp cfresh : E) : Prop where
  base : LoadHolds rd written c r.base
  nx : r.nx < 2 ^ 16
  ns : r.ns < 2 ^ 16
  nda : r.nda ≤ 16
  ccx : coreProgram.Rel rd "child_claim_list_digest"
    [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq] [r.dx0, r.dx1]
  ccs : coreProgram.Rel rd "child_claim_list_digest"
    [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq] [r.ds0, r.ds1]
  sig : CompressCells ![r.dx0, r.dx1, r.ds0, r.ds1] ivCells.1 ivCells.2 r.o0 r.o1
    (metadataCell 64 true)
  sigp : ReadsAt rd r.sigp [r.o0, r.o1]
  das : r.nda ≠ 0 → coreProgram.Rel rd "__loop100"
    [1, gen ^ r.nda, r.cda, daR, daC, daS, r.base, gen ^ r.nx * gen ^ r.ns] []
  dl : coreProgram.Rel rd "da_list_digest" [r.cda, gen ^ r.nda] [r.r0, r.r1]
  sd : coreProgram.Rel rd "statement_digest"
    [seed0, seed1, r.sigp, r.r0, r.r1, carried * gen ^ (53 * c)] [r.p0, r.p1]
  pi0 : LoadHolds rd cpi (2 * c) r.p0
  pi1 : LoadHolds rd cpi (2 * c + 1) r.p1
  vs : coreProgram.Rel rd "verify_sub" [r.p0, r.p1, seed0, seed1, glp, gsq, cfresh * gen ^ (106 * c)] []
  next : LoadHolds rd written (c + 1) (r.base * (gen ^ r.nx * gen ^ r.ns) * gen ^ r.nda)

/-- **`__loop5`, backward**: its `m` iterations, child `c` read by `rs c`. -/
theorem loop5_complete (hm : MemOk rd) {written lxT cover lxS gsq spT spS carried daR daC daS seed0
    seed1 cpi glp cfresh : E} {m : ℕ} (hm0 : 0 < m) (rs : ℕ → ChildRun)
    (hok : ∀ c < m, ChildOkR rd c (rs c) written lxT cover lxS gsq spT spS carried daR daC daS seed0
      seed1 cpi glp cfresh) :
    coreProgram.Rel rd "__loop5" [1, gen ^ m, written, lxT, cover, lxS, gsq, spT, spS, carried, daR,
      daC, daS, seed0, seed1, cpi, glp, cfresh] [] := by
  obtain ⟨D1, h1⟩ := rel_uniform (rd := rd) m fun c hc => (hok c hc).ccx
  obtain ⟨D2, h2⟩ := rel_uniform (rd := rd) m fun c hc => (hok c hc).ccs
  obtain ⟨D3, h3⟩ := rel_uniform_if (rd := rd) (Q := fun c => (rs c).nda ≠ 0) m
    fun c hc => (hok c hc).das
  obtain ⟨D4, h4⟩ := rel_uniform (rd := rd) m fun c hc => (hok c hc).dl
  obtain ⟨D5, h5⟩ := rel_uniform (rd := rd) m fun c hc => (hok c hc).sd
  obtain ⟨D6, h6⟩ := rel_uniform (rd := rd) m fun c hc => (hok c hc).vs
  set D := max D1 (max D2 (max D3 (max D4 (max D5 D6))))
  have up : ∀ {d d' f a r}, d ≤ d' → coreProgram.relN rd d f a r → coreProgram.relN rd d' f a r :=
    fun hd h => relN_mono coreProgram hd _ _ _ h
  refine loop_complete_from (D := D) (B := fun j => j < m) hm0 rfl (fun j hj => hj)
    fun d j hd hj hK hnext => loop5_back hm d j (rs j) ?_ hK hnext
  have o := hok j hj
  exact ⟨o.base, o.nx, o.ns, o.nda, up (by omega) (h1 j hj), up (by omega) (h2 j hj), o.sig, o.sigp,
    fun hne => up (by omega) (h3 j hj hne), up (by omega) (h4 j hj), up (by omega) (h5 j hj), o.pi0,
    o.pi1, up (by omega) (h6 j hj), o.next⟩

end
end LeanVM.Guest.B1.Main
