/-
  LeanVM.Guest.B1.VerifySub.Keccak

  `verify_sub`'s `KECCAK` phase: `verify_keccak`'s call runs `keccakValidity` on the link's end.
-/

module

public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The Keccak phase

`vsKeccakT` (statements `2920 .. 2928`, checked by the kernel) calls `verify_keccak` on the
`KECCAK` table's height `kb[7]`, the link's row point `chi`, the output lanes the link sent and the
window tables `g_squares·g^WIN_TAB_AT`. `phKeccak`: by its meaning (`keccak_section_sound`), its
words run `keccakValidity` on the link's end (`VsLinkFacts`: the table's point is `chi`'s first `τ`
coordinates, its output lanes the words at `fs0@7~10`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_sub`'s statements 2920 to 2928. -/
def vsKeccakT : List Stmt := (
  .atom (.mul (.n 2907) (.n 1287) (.n 2906)) ::
  .atom (.add (.n 2908) (.n 2898) (.n 2907)) ::
  .atom (.const (.n 2909) (word 21299200 0)) ::
  .atom (.mul (.n 2910) (.n 1076) (.n 2909)) ::
  .atom (.const (.n 2911) (word 36028797018963968 0)) ::
  .atom (.mul (.n 2912) (.n 1076) (.n 2911)) ::
  .atom (.const (.n 2913) (word 365917469723852800 0)) ::
  .atom (.mul (.n 2914) (.n 4) (.n 2913)) ::
  .call "verify_keccak" [.n 1288, .n 1289, .n 1290, .n 1291, .n 1292, .n 2910, .n 120, .n 15, .n 2912, .n 20, .n 21, .n 2914] [.n 2915, .n 2916, .n 2917, .n 2918, .n 2919, .n 2920, .n 2921] ::
  [])

theorem vsKeccakT_eq : (vsPre.drop 2920).take 9 = vsKeccakT := stmtsEqb_sound (by decide +kernel)


set_option maxRecDepth 100000 in
theorem word_winTab : word 365917469723852800 0 = gen ^ winTabAt := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound winTabAt; omega)]
  congr 1

/-- **The Keccak phase**, sound. -/
theorem phKeccak : PhKeccak := by
  intro bytecode κ L C V σ rets R link hLF
  have S := R.sizesOk
  obtain ⟨-, hwin, h11⟩ := R.pre
  have h := R.slice vsKeccakT_eq
  simp only [vsKeccakT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨-, -, -, -, -, -, k2913, k2914, kcall, -⟩ := h
  have hwt : WinTabs L.read (σ (.n 2914)) := by
    have e : σ (.n 2914) = σ (.n 4) * gen ^ winTabAt := by
      rw [show σ (.n 2914) = σ (.n 4) * σ (.n 2913) from k2914, show σ (.n 2913) = _ from k2913,
        word_winTab]
    rw [e]; exact winTabs_of_expWinTab hwin
  have hM := keccak_section_sound R.hκ h11 L _ _ (R.hle _ _ _ kcall)
  obtain ⟨r, chis, qPoint, -, -, -, hchi, -, hhc, -, -, -, -, -, -, -, -, -, -, hkcol, outs, hmap, hout,
    houtl⟩ := hLF
  set τ := (vsLayout bytecode σ).tableLogHeights.getD opKeccak 0 with hτ
  have hτ9 : 9 ≤ τ := by
    obtain ⟨-, -, -, hth, -⟩ := Stack.buildLayout_some S.build
    rw [hτ, hth, show opKeccak = 5 from rfl]
    have hl : 5 < (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) (vsRows σ)
        tableLogFloors).length := by
      rw [List.length_zipWith]; simp [vsRows, vsAnnounced, tableLogFloors, nTables]
    rw [List.getD_eq_getElem _ _ hl, List.getElem_zipWith]
    exact le_max_right _ _
  have hτ24 : τ ≤ 24 := S.heights24 5 (by decide)
  have htg : σ (.n 120) = gen ^ τ := by
    have hlen : (vsLayout bytecode σ).tableLogHeights.length = 6 := by
      obtain ⟨-, -, -, hth, -⟩ := Stack.buildLayout_some S.build
      rw [hth, List.length_zipWith]; simp [vsRows, vsAnnounced, tableLogFloors, nTables]
    obtain ⟨h5, hh5⟩ : ∃ h, (vsLayout bytecode σ).tableLogHeights[5]? = some h :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have := congrArg (fun l ↦ l.getD 5 0) S.heights
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, nTables, hh5] at this
    rw [show σ (.n 120) = σ (.n (115 + 5)) from rfl, hτ, show opKeccak = 5 from rfl,
      List.getD_eq_getElem?_getD, hh5]
    simpa [List.getElem?_range] using this
  obtain ⟨xs, op, point, slices, word, s', hxs, hrun, hpend, hop, hpt, hsl, hopl, hptl, hsll, hrets⟩ :=
    hM hwt τ chis outs hτ9 hτ24 htg (hhc 5 (by decide)) hchi houtl hout
  simp only [capOf, List.cons_append, List.nil_append,
    List.cons.injEq] at hrets
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, -⟩ := hrets
  refine ⟨xs, [⟨qkeccak, op, word⟩], point, slices, s', hxs, e5, ?_, hpend, ?_,
    ⟨op, by rw [← e6], hop, hpt, hsl, hsll, ?_, by rw [hptl, hopl]⟩⟩
  · have e : keccakValidity (vsLayout bytecode σ) link = verifyKeccak τ (chis.take τ) outs := by
      unfold keccakValidity
      rcases hc : link.columns.getD opKeccak ([], []) with ⟨pt, vals⟩
      rw [hc] at hkcol hmap
      simp only at hkcol hmap ⊢
      rw [hmap, hkcol]
      rfl
    rw [e]
    exact hrun
  · simp only [vsCapK, capOf, e0, e1, e2, e3, e4]
  · rw [show σ (.n (val% «verify_sub» "kb[7]")) = σ (.n 120) from rfl, htg, hopl, ← pow_add]

end
end LeanVM.Guest.B1.VerifySub
