/-
  LeanVM.Guest.B1.VsC.VsOrcCtxEnd

  `vsKEndW` on an honest context, the own witness entries from the buffers' words.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcCtxBuf

/-!
# The end on an honest context

**`VsCtx.words_at`**: a fixed own buffer's heap destination reads its words `x.Lw.getD j []` on every memory with
`Bnd`'s `O`. **`VsCtx.kEndW_bw`**: `VsCtx.kEndW` with `h6`, `h9`, `h14`, `h240` from the buffers' words: `.n 6`'s
the table log heights' counts, `.n 9`'s `link_shape`'s words, `.n 14`'s the fresh claim's values, `.n 8`'s the bits of
the exponent at `.n 240`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (wordNat bitWord)

@[expose] public section

namespace VsCtx

variable {x : VsCtx}

/-- **A fixed own buffer's words through its heap destination.** -/
theorem words_at (h : x.Hon) {st : St} (hb : x.Bnd st) {j : ℕ} (hj : j < 18) {rd : Reader} (ho : st.O rd)
    {σ : Val} (hσ : σ (.n (j + 6)) = x.σ0 (.n (j + 6))) :
    (Dest.heap (.n (j + 6)) 0 ((vsAllocSz x.p).getD j 0)).words rd σ = x.Lw.getD j [] := by
  have hR : ReadsAt rd (σ (.n (j + 6))) (x.Lw.getD j []) := by
    rw [hσ]
    have e : x.σ0 (.n (j + 6)) = ptrAt (x.base j) := ptrL h hj
    rw [e]
    exact hb.hO rd ho _ (mem_Wo h (by omega))
  rw [← Lw_length h (by omega)]
  exact heap_words hR

theorem rc6 : vsRcs.lookup (.n 6) = none := by decide +kernel
theorem rc9 : vsRcs.lookup (.n 9) = none := by decide +kernel
theorem rc14 : vsRcs.lookup (.n 14) = none := by decide +kernel

set_option linter.constructorNameAsVariable false in
/-- **`vsKEndW` at the end of the honest phases, the own entries from the buffers' words.** -/
theorem kEndW_bw (hx : x.Hon) {st : St} (hb : x.Bnd st) (hc : x.Carry11 st) {layout : Layout} {rate : ℕ}
    (hann : announcedLayoutAndRate guestBytecode x.c.proof.stream = some (layout, rate))
    (hf : VsFresh x.rd1 x.rd0 x.w x.args) {a kc : ℕ} {O : Reader → Prop} {D : ℕ → Prop}
    {Qo : Reader → Tree → Prop} (hO : ∀ rd, O rd → st.O rd)
    (ho : ∀ rd, LowDef 17 rd → x.Pre rd → O rd → ∀ t, Qo rd t →
      PopsPost (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings) rd t)
    (b0 : x.bw.getD 0 [] = layout.tableLogHeights.map Prover.count)
    (b3 : x.bw.getD 3 [] = vsLinkShape layout)
    (b8 : x.bw.getD 8 [] = x.c.freshClaim.values)
    (b2 : ∃ n, n < 2 ^ 24 ∧ x.σ0 (.n 240) = ofK (g ^ n) ∧
      x.bw.getD 2 [] = (List.range 24).map fun j => bitWord (n.testBit j)) :
    vsKEndW 17 guestBytecode x.seed x.c x.qt x.qo x.σ0
      ⟨a, kc, O, D, st.Qs ++ List.replicate 5 PostQuiet ++ [PostQuiet] ++ [PostQuiet, PostQuiet] ++ [Qo, PostQuiet]⟩ := by
  have L : ∀ j, j < 18 → j ≠ 13 → x.Lw.getD j [] = x.bw.getD j [] := fun j hj hn => by
    simp only [Lw_getD hx (show j < 24 by omega), hn, ↓reduceIte]
  refine kEndW hx hb hc hann hf hO ho (fun rd _ _ h => ?_) (fun rd _ _ h => ?_) (fun rd _ _ h => ?_)
    (fun rd _ _ h => ?_)
  · exact (words_at hx hb (j := 0) (by omega) (hO rd h) (rdOver_eq rc6)).trans ((L 0 (by omega) (by omega)).trans b0)
  · exact (words_at hx hb (j := 3) (by omega) (hO rd h) (rdOver_eq rc9)).trans ((L 3 (by omega) (by omega)).trans b3)
  · exact (words_at hx hb (j := 8) (by omega) (hO rd h) (rdOver_eq rc14)).trans
      ((L 8 (by omega) (by omega)).trans b8)
  · obtain ⟨n, hn, e240, e2⟩ := b2
    unfold Hint.Exact
    exact ⟨n, hn, e240, (words_at hx hb (j := 2) (by omega) (hO rd h) rfl).trans ((L 2 (by omega) (by omega)).trans e2)⟩

end VsCtx

end
end LeanVM.Guest.B1.VsC
