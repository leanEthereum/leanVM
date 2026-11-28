/-
  LeanVM.Guest.B1.VsC.VsOrcExport

  `PhExportHyp` at the honest oracle: the export of the fresh claim into `defer_out`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcBuf
public import LeanVM.Guest.B1.VsC.VsOrcTail

/-!
# The export at the honest oracle

`verify_sub`'s last window copies `r_pt`'s first `19` words (`.n 12`) and `splitv`'s `36` (`.n 14`) into `defer_out`
(`.n 5`, the argument `ptrAt qo`). **`phExportOk_honest`**: `PhExportOk` at any state from
* the two buffers at their honest bases (`vsBase cur p 6`, `vsBase cur p 8`), inside the own cells `[cur, cur + Σ)`;
* their words on the evaluation memory and on every memory with `Pre` and the state's words (`VsBufWords`);
* the fresh claim's cells read on the evaluation memory at `qo`, and its point and values being `r_pt`'s first `19`
  words and `splitv`'s `36` (the export's converse: what the deferring verifier's fresh claim is).
The memories with `Pre` read the fresh claim at `qo` (`vsPreA`), which lies in `vsRegion`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- A buffer's words `xs` at `ptrAt b`, read on the evaluation memory `rd0` and on every memory with `Pre` and `O`. -/
def VsBufWords (rd0 : Reader) (Pre O : Reader → Prop) (b : ℕ) (xs : List E) : Prop :=
  ReadsAt rd0 (ptrAt b) xs ∧ ∀ rd, Pre rd → O rd → ReadsAt rd (ptrAt b) xs

/-- **The export at the honest oracle.** -/
theorem phExportOk_honest {k : ℕ} {al : String → Bool} {seed : Digest} {c : Child} {qt qo cur p : ℕ}
    {rd0 : Reader} {w : ℕ → E} {Own : ℕ → Prop} {st : St} {K : St → Prop} {xs12 xs14 : List E}
    (hOwn : ∀ i, cur ≤ i → i < cur + (vsAllocSz p).sum → Own i)
    (hw12 : w 12 = ptrAt (vsBase cur p 6)) (hw14 : w 14 = ptrAt (vsBase cur p 8))
    (hl12 : 19 ≤ xs12.length) (hl14 : 36 ≤ xs14.length)
    (B12 : VsBufWords rd0 (vsPreA seed c qt qo) st.O (vsBase cur p 6) xs12)
    (B14 : VsBufWords rd0 (vsPreA seed c qt qo) st.O (vsBase cur p 8) xs14)
    (r5 : ReadsAt rd0 (ptrAt qo) c.freshClaim.cells)
    (hpt : c.freshClaim.point = xs12.take 19) (hval : c.freshClaim.values = xs14.take 36)
    (hK : K st) :
    PhExportOk B2C.fs al B2C.cert k rd0 w (vsArgs seed c (ptrAt qt) (ptrAt qo))
      Own (vsRegion qt qo c.freshClaim.cells.length) (vsPreA seed c qt qo)
      st K := by
  have ha : (vsArgs seed c (ptrAt qt) (ptrAt qo)).length = 6 := rfl
  have hcells : c.freshClaim.cells = xs12.take 19 ++ xs14.take 36 := by
    rw [FreshClaim.cells, hpt, hval]
  have hlen : c.freshClaim.cells.length = 55 := by
    rw [hcells, List.length_append, List.length_take, List.length_take]; omega
  refine ⟨qo, vsBase cur p 6, vsBase cur p 8, c.freshClaim.cells, xs12, xs14, ?_, hK⟩
  exact {
    h12 := (vsVal_fixed ha (by omega)).trans hw12
    hl12 := hl12
    r12 := B12.1
    hO12 := B12.2
    hc12 := fun j hj => Or.inl (hOwn _ (by rw [vsBase_12]; omega) (by rw [vsBase_12, vsAllocSz_total]; omega))
    h14 := (vsVal_fixed ha (by omega)).trans hw14
    hl14 := hl14
    r14 := B14.1
    hO14 := B14.2
    hc14 := fun j hj => Or.inl (hOwn _ (by rw [vsBase_14]; omega) (by rw [vsBase_14, vsAllocSz_total]; omega))
    h5 := vsVal_param ha (i := 5) (by omega)
    hx5 := hcells
    r5 := r5
    hO5 := fun rd hp _ => hp.2
    hc5 := fun j hj => Or.inr (Or.inl (Or.inr ⟨Nat.le_add_right _ _, by omega⟩)) }

end
end LeanVM.Guest.B1.VsC
