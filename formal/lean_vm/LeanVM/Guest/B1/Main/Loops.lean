/-
  LeanVM.Guest.B1.Main.Loops

  The loops of `main` over its raw signatures (`__loop3`, `__loop4`) and of each child over its
  DA roots (`__loop100`), read forward.
-/

module

public import LeanVM.Guest.B1.Main.Callees

/-!
# The writer loops

Each iteration of these loops writes one mark into the coverage table and checks the claim of
the slot it writes:

* `__loop3` (G:3218-3228), at `x`: a hinted index `g^s`, `s` below the leanXMSS region, the mark
  `x` in slot `s`, and a leanXMSS signature on the table's claim `s`;
* `__loop4` (G:3229-3233), at `x`: a hinted offset `g^s` below the leanSPHINCS region, the mark
  `g^(n_raw_x)·x` in slot `L_x + s`, and a leanSPHINCS signature on its claim `s`;
* `__loop100` (G:3277-3283), at `x = g^j`: `cover_da_root` writes the mark `base·g^(n_sub)·x` in
  DA slot `i` and returns that slot's claim, stored as the child's DA claim `j`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {bytecode : List K} {rd : Reader}

theorem find_loop3 : coreProgram.find? "__loop3" = some Data.core33 :=
  Program.find?_of_indexOf? (j := 33) (by decide +kernel) rfl

theorem find_loop4 : coreProgram.find? "__loop4" = some Data.core34 :=
  Program.find?_of_indexOf? (j := 34) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_loop100 : coreProgram.find? "__loop100" = some Data.core573 :=
  Program.find?_of_indexOf? (j := 573) (by decide +kernel) rfl

theorem gen_pow_four (s : ℕ) : gen ^ s * gen ^ s * (gen ^ s * gen ^ s) = gen ^ (4 * s) := by
  ring

/-- **`__loop3` at `x`**, the leanXMSS region `g^M`: the hinted index `g^s`, `s < M`, the mark
`x` in coverage slot `s`, a leanXMSS signature on the table's claim `s`; then the next
iteration, while `x·g ≠ N`. -/
theorem loop3_step (hm : MemOk rd) (H : Callees bytecode rd) {N lxS cover table : E} {M : ℕ}
    (hM : M < 2 ^ 33) (hL : lxS = gen ^ M) (x : E)
    (h : coreProgram.Rel rd "__loop3" [x, N, lxS, cover, table] []) :
    (∃ s < M, LoadHolds rd cover s x ∧ XmssSigned rd (table * gen ^ (4 * s))) ∧
      (x * gen + N ≠ 0 → coreProgram.Rel rd "__loop3" [x * gen, N, lxS, cover, table] []) := by
  rw [rel_iff_sem find_loop3] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core33 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4⟩ := hp
  simp only [show Fn.body Data.core33 = Data.core33.body from rfl, Data.core33.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨-, h6, h7, hrc, h11, hl, h12, h13, h14, hv, h15, h16, h17, h18, h19, -, hcall, -⟩ := h
  obtain ⟨s, hs, hx⟩ := rc_bound hm hM hL (by rw [h7, h2, h6]) hrc
  refine ⟨⟨s, hs, ?_, ?_⟩, fun hne => ?_⟩
  · rw [h11, h3, hx, h0, loadHolds_mul_gen_pow] at hl
    exact hl
  · have := H.verify_lean_xmss _ hv
    rwa [h14, h13, h12, h4, hx, gen_pow_four] at this
  · have := hcall (by rw [h17, h16, h15, h0, h1]; exact hne)
    rwa [h19, h18, h0, h1, h2, h3, h4] at this

/-- **`__loop4` at `x`**, the leanSPHINCS region `g^M` after the leanXMSS region `g^Lx`: the
hinted offset `g^s`, `s < M`, the mark `w·x` in coverage slot `Lx + s`, a leanSPHINCS signature
on the table's claim `s`; then the next iteration, while `x·g ≠ N`. -/
theorem loop4_step (hm : MemOk rd) (H : Callees bytecode rd) {N spS cover lxS w table : E}
    {M Lx : ℕ} (hM : M < 2 ^ 33) (hL : spS = gen ^ M) (hLx : lxS = gen ^ Lx) (x : E)
    (h : coreProgram.Rel rd "__loop4" [x, N, spS, cover, lxS, w, table] []) :
    (∃ s < M, LoadHolds rd cover (Lx + s) (w * x) ∧ SphincsSigned rd (table * gen ^ (4 * s))) ∧
      (x * gen + N ≠ 0 →
        coreProgram.Rel rd "__loop4" [x * gen, N, spS, cover, lxS, w, table] []) := by
  rw [rel_iff_sem find_loop4] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core34 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  simp only [show Fn.body Data.core34 = Data.core34.body from rfl, Data.core34.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨-, h8, h9, hrc, h13, h14, h15, hl, h16, h17, h18, hv, h19, h20, h21, h22, h23,
    -, hcall, -⟩ := h
  obtain ⟨s, hs, hx⟩ := rc_bound hm hM hL (by rw [h9, h2, h8]) hrc
  refine ⟨⟨s, hs, ?_, ?_⟩, fun hne => ?_⟩
  · rw [h15, h14, h13, h3, h4, hx, h5, h0, hLx, ← pow_add, loadHolds_mul_gen_pow] at hl
    exact hl
  · have := H.verify_sig_lean_sphincs _ hv
    rwa [h18, h17, h16, h6, hx, gen_pow_four] at this
  · have := hcall (by rw [h21, h20, h19, h0, h1]; exact hne)
    rwa [h23, h22, h0, h1, h2, h3, h4, h5, h6] at this

/-- **`__loop100` at `x`** (a child's DA roots), the DA region `g^M`: `cover_da_root` writes the
mark `base·n·x` in DA slot `i < M` and the slot's four cells are stored at `child_da·x⁴`; then the
next iteration, while `x·g ≠ N`. -/
theorem loop100_step (H : Callees bytecode rd) {N cda roots dcov dslots base nsub : E} {M : ℕ}
    (hM : M < 2 ^ 33) (hL : dslots = gen ^ M) (x : E)
    (h : coreProgram.Rel rd "__loop100" [x, N, cda, roots, dcov, dslots, base, nsub] []) :
    (∃ i < M, LoadHolds rd dcov i (base * nsub * x) ∧ ∃ r0 r1 r2 r3,
        ReadsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3] ∧
        ReadsAt rd (cda * (x * x * (x * x))) [r0, r1, r2, r3]) ∧
      (x * gen + N ≠ 0 →
        coreProgram.Rel rd "__loop100" [x * gen, N, cda, roots, dcov, dslots, base, nsub] []) := by
  rw [rel_iff_sem find_loop100] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core573 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hp
  simp only [show Fn.body Data.core573 = Data.core573.body from rfl, Data.core573.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h8, h9, h10, h11, h12, hc, l0, l1, l2, l3, h17, h18, h19, h20, h21, -, hcall, -⟩ := h
  obtain ⟨i, M', hM', hi, hsl, hmk, hr⟩ := H.cover_da_root _ _ _ _ _ _ _ _ hc
  have hMM : M' = M := gen_pow_inj' (by omega) (by omega) (hsl.symm.trans (h5 ▸ hL))
  subst hMM
  refine ⟨⟨i, hi, ?_, σ (.n 13), σ (.n 14), σ (.n 15), σ (.n 16), ?_, ?_⟩, fun hne => ?_⟩
  · rw [h4, h12, h11, h6, h7, h0, loadHolds_mul_gen_pow, Nat.add_zero] at hmk
    exact hmk
  · rwa [h3] at hr
  · rw [← h0, ← h2, ← h8, ← h9, ← h10]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3
  · have := hcall (by rw [h19, h18, h17, h0, h1]; exact hne)
    rwa [h21, h20, h0, h1, h2, h3, h4, h5, h6, h7] at this

end
end LeanVM.Guest.B1.Main
