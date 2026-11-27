/-
  LeanVM.Guest.B1.Gkr.GlTail

  The tail of a radix-four layer (`glTail`, canonically numbered): the twelve children read and
  absorbed, their check, the two new coordinates squeezed and the next slot's stores, soundly.
-/

module

public import LeanVM.Guest.B1.Gkr.GlT
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L0_L0»
import LeanVM.Guest.B1.Tables.Basic

/-!
# A layer's tail, soundly

On the canonical numbering (`glTail`; `gkr_layer__L{p}_L{o}`'s is it renamed by `glRho p o`):

* `gl_kids`: the children's reads (`chT` at the tail cursor `80`, `off` words on) and the two
  permutations among them;
* `gl_tail`: the twelve words at `80·g^off` are the three trees' children (`glCh`), their
  products check the last claim `159` at the combiner `27`, the sponge after them from the last
  capacity `141 ..` (`glSponge`) squeezes the two new coordinates (`250`, `263`, stored at
  `pt[40]`, `pt[41]` of the row `52`), and the next slot at `15·g^20` gets the capacity, the
  cursor `80·g^(off + 12)`, the trees' values at the new coordinates and the position
  `43·(3·g)^7`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The children of tree `m` (canonical numbering). -/
abbrev glCh (τ : Val) (m : ℕ) : List E := chWords τ (val% «gkr_layer__L0_L0» "x@9") m

/-- The sponge after the twelve children, from the last round's capacity `137 ..`. -/
def glSponge (τ : Val) : Fs :=
  (((⟨(glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")).map τ, []⟩ : Fs).absorbAll (glCh τ 0) dsObserve).absorbAll (glCh τ 1)
    dsObserve).absorbAll (glCh τ 2) dsObserve

theorem chT_noRet (cur : V) (o b0 i : ℕ) : Stmt.noRetList (chT cur o b0 i) = true := rfl

theorem glChs_noRet (off a : ℕ) :
    Stmt.noRetList ((List.range 4).map fun i ↦ chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") (a + i)).flatten = true :=
  tb_noRetList_flatten_range 4 _ fun _ => chT_noRet _ _ _ _

theorem glKids_noRet (off : ℕ) : Stmt.noRetList (glKids off) = true := by
  have h0 := glChs_noRet off 0
  simp only [Nat.zero_add] at h0
  simp only [glKids, tb_noRetList_append, h0, glChs_noRet]
  rfl

section Sem

variable {C : CallRel} {rd : Reader} {τ : Val} {kret : List E → Prop}

theorem gl_flat4 {f : ℕ → List Stmt} (hf : ∀ i, Stmt.noRetList (f i) = true)
    (h : Stmt.HoldsList C rd τ ((List.range 4).map f).flatten True kret) :
    ∀ i < 4, Stmt.HoldsList C rd τ (f i) True kret :=
  ((holdsList_range_flatten 4 f hf True kret).mp h).1

/-- **The children's reads** and the permutations of the first eight. -/
theorem gl_kids {off : ℕ} (h : Stmt.HoldsList C rd τ (glKids off) True kret) :
    (∀ i < 12, Stmt.HoldsList C rd τ (chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") i) True kret) ∧
      (Atom.keccak (chRate (val% «gkr_layer__L0_L0» "x@9") 0 ++ glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")) (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@4")) false false).Holds rd τ ∧
      (Atom.keccak (chRate (val% «gkr_layer__L0_L0» "x@9") 1 ++ lyCap (val% «gkr_layer__L0_L0» "nxt[0]@4")) (lyOuts (val% «gkr_layer__L0_L0» "nxt[0]@5")) false false).Holds rd τ := by
  unfold glKids at h
  simp only [List.append_assoc] at h
  have n0 := glChs_noRet off 0
  simp only [Nat.zero_add] at n0
  rw [tb_holdsList_append_noRet n0, tb_holdsList_append_noRet rfl,
    tb_holdsList_append_noRet (glChs_noRet off 4), tb_holdsList_append_noRet rfl] at h
  obtain ⟨h0, k1, h1, k2, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, and_true] at k1 k2
  have e0 := gl_flat4 (fun i => chT_noRet _ _ _ _) h0
  have e1 := gl_flat4 (f := fun i ↦ chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") (4 + i)) (fun i => chT_noRet _ _ _ _) h1
  have e2 := gl_flat4 (f := fun i ↦ chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") (8 + i)) (fun i => chT_noRet _ _ _ _) h2
  refine ⟨fun i hi => ?_, k1, k2⟩
  rcases (by omega : i < 4 ∨ (4 ≤ i ∧ i < 8) ∨ 8 ≤ i) with hi4 | ⟨hi4, hi8⟩ | hi8
  · exact e0 i hi4
  · have := e1 (i - 4) (by omega); rwa [show 4 + (i - 4) = i by omega] at this
  · have := e2 (i - 8) (by omega); rwa [show 8 + (i - 8) = i by omega] at this

theorem glCheck_noRet : Stmt.noRetList glCheck = true := by decide

theorem glY_noRet : Stmt.noRetList glY = true := by decide

/-- **A layer's tail.** -/
theorem gl_tail {off : ℕ} (hoff : off ≤ 8)
    (h : Stmt.HoldsList C rd τ (glKids off ++ glCheck ++ glY ++ glNext (off + 12)) True kret)
    (z23 : τ (.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) = 0) (z24 : τ (.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) = 0) (z25 : τ (.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) = 0) (z26 : τ (.n (val% «gkr_layer__L0_L0» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) = 0) :
    ReadsAt rd (τ (.n (val% «gkr_layer__L0_L0» "tcur")) * gen ^ off) (glCh τ 0 ++ (glCh τ 1 ++ glCh τ 2)) ∧
      τ (.n (val% «gkr_layer__L0_L0» "nclaim@2")) = polyEval [prodE (glCh τ 0), prodE (glCh τ 1), prodE (glCh τ 2)] (τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@1"))) ∧
      ((glSponge τ).squeezeN 2).1 = [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))] ∧
      ((glSponge τ).squeezeN 2).2 = ⟨(glCap (val% «gkr_layer__L0_L0» "nxt[8]@7")).map τ, []⟩ ∧
      (∀ t < 3, LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "layer"))) (26 + t)
        (multilinearEval (glCh τ t) [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))])) ∧
      (∀ k < 5, LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "layer"))) (20 + k) (τ (.n ((val% «gkr_layer__L0_L0» "nxt[8]@7") + k)))) ∧
      LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "layer"))) 25 (τ (.n (val% «gkr_layer__L0_L0» "tcur")) * gen ^ (off + 12)) ∧
      LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "point_row"))) 40 (τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6"))) ∧ LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "point_row"))) 41 (τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))) ∧
      LoadHolds rd (τ (.n (val% «gkr_layer__L0_L0» "layer"))) 29 (τ (.n (val% «gkr_layer__L0_L0» "round_pos")) * (τ (.n (val% «gkr_layer__L0_L0» "x_m")) * gen) ^ 7) := by
  simp only [List.append_assoc] at h
  rw [tb_holdsList_append_noRet (glKids_noRet off), tb_holdsList_append_noRet glCheck_noRet,
    tb_holdsList_append_noRet glY_noRet] at h
  obtain ⟨hK, hC, hY, hN⟩ := h
  obtain ⟨EVh, k1, k2⟩ := gl_kids hK
  have EV : ∀ i < 12, _ := fun i hi => ch_ev (EVh i hi)
  have cp : ∀ i < 12, τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i + 3)) = τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)) := fun i hi => (EV i hi).2.2
  have hp : ∀ m < 3, ∀ i < 4,
      FsPackOk τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * m + i))) (chB (val% «gkr_layer__L0_L0» "x@9") (4 * m + i) + 1) dsObserve :=
    fun m hm i hi => (EV (4 * m + i) (by omega)).2.1
  -- the reads
  have hreads : ReadsAt rd (τ (.n (val% «gkr_layer__L0_L0» "tcur")) * gen ^ off) (glCh τ 0 ++ (glCh τ 1 ++ glCh τ 2)) := by
    intro k hk
    have hk12 : k < 12 := by simpa [chWords_length] using hk
    rw [loadHolds_mul_gen_pow]
    convert (EV k hk12).1 using 1
    simp only [chWords_eq]
    interval_cases k <;> rfl
  -- the sponge
  have A0 : (⟨(glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")).map τ, []⟩ : Fs).absorbAll (glCh τ 0) dsObserve =
      ⟨(glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")).map τ, (glCh τ 0).map (·, dsObserve)⟩ := by
    rw [absorbAll_short _ _ _ (by simp [chWords_length])]
    simp
  obtain ⟨-, B0⟩ := ch_perm_block (hp 0 (by omega)) k1
  obtain ⟨-, B1⟩ := ch_perm_block (hp 1 (by omega)) k2
  have hY' := hY
  simp only [glY, Stmt.HoldsList, Stmt.Holds, and_true] at hY'
  obtain ⟨k3, k4, l262, l276⟩ := hY'
  obtain ⟨P2, B2⟩ := ch_perm_block (hp 2 (by omega)) k3
  have hA : glSponge τ = ⟨(lyCap (val% «gkr_layer__L0_L0» "nxt[0]@5")).map τ, (glCh τ 2).map (·, dsObserve)⟩ := by
    unfold glSponge
    rw [A0, tb_absorbAll_full _ (by simp [chWords_length]) _ (chWords_length τ (val% «gkr_layer__L0_L0» "x@9") 1), ← B0,
      tb_absorbAll_full _ (by simp [chWords_length]) _ (chWords_length τ (val% «gkr_layer__L0_L0» "x@9") 2), ← B1]
  rw [← hA] at P2 B2
  simp only [Atom.Holds] at l262 l276
  have e262 : τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")) = challengeOf (glSponge τ).perm := by
    rw [P2 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
  obtain ⟨P3, B3⟩ := ly_keccak k4
  rw [ly_zero_rate z23 z24 z25 z26, B2] at P3 B3
  have e276 : τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7")) = challengeOf (permOf (rateOf [] ++ capOf (glSponge τ).perm)) := by
    rw [P3 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
  have hsq : ((glSponge τ).squeezeN 2).1 = [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))] := by
    rw [e262, e276]; rfl
  -- the next slot
  have hN' := hN
  simp only [glNext, chValT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
    List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append] at hN'
  obtain ⟨s0, s1, s2, s3, s4, c277, m278, l278, v0, v1, v2, v3, v4, v5, v6, v7, v8, l0,
    w0, w1, w2, w3, w4, w5, w6, w7, w8, l1, u0, u1, u2, u3, u4, u5, u6, u7, u8, l2,
    c305, m306, m307, m308, m309, m310, m311, l311⟩ := hN'
  rw [word_two_pow (by omega)] at c277
  rw [word_gen] at c305
  have hw : ∀ m < 3, glCh τ m = [τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * m) + 3)), τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * m + 1) + 3)),
      τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * m + 2) + 3)), τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") (4 * m + 3) + 3))] := by
    intro m hm
    rw [glCh, chWords_eq, cp _ (by omega), cp _ (by omega), cp _ (by omega), cp _ (by omega)]
  refine ⟨hreads, ?_, hsq, ?_, fun t ht => ?_, fun k hk => ?_, ?_, l262, l276, ?_⟩
  · -- the check (`gkr_product_check`, Horner in the combiner from the top tree)
    have hC' := hC
    simp only [glCheck, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_zero] at hC'
    obtain ⟨m233, m234, m235, c236, m237, a238, m239, m240, m241, m242, a243, m244, m245, m246,
      m247, a248, q⟩ := hC'
    rw [e_add_eq_zero_iff.mp q, a248, m247, a243, m242, a238, m237, c236, m235, m234, m233, m241,
      m240, m239, m246, m245, m244, hw 0 (by omega), hw 1 (by omega), hw 2 (by omega)]
    simp only [polyEval, prodE, List.foldr, List.foldl, chB]
    ring
  · show (⟨capOf (permOf (rateOf [] ++ capOf (glSponge τ).perm)), []⟩ : Fs) = _
    rw [← B3]
    simp [lyCap, glCap]
  · interval_cases t
    · rw [hw 0 (by omega)]
      convert l0 using 1
      rw [v8, v7, v6, v5, v4, v3, v2, v1, v0]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD, chB]
      ring
    · rw [hw 1 (by omega)]
      convert l1 using 1
      rw [w8, w7, w6, w5, w4, w3, w2, w1, w0]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD, chB]
      ring
    · rw [hw 2 (by omega)]
      convert l2 using 1
      rw [u8, u7, u6, u5, u4, u3, u2, u1, u0]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD, chB]
      ring
  · interval_cases k
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
  · rw [← c277, ← m278]; exact l278
  · rw [show τ (.n (val% «gkr_layer__L0_L0» "round_pos")) * (τ (.n (val% «gkr_layer__L0_L0» "x_m")) * gen) ^ 7 =
        τ (.n (val% «gkr_layer__L0_L0» "s44#6")) by rw [m311, m310, m309, m308, m307, m306, c305]; ring]
    exact l311

end Sem

end
end LeanVM.Guest.B1.Tables
