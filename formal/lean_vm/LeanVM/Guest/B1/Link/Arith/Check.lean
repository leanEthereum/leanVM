/-
  LeanVM.Guest.B1.Link.Arith.Check

  The link's terminal check: `link_terminal`'s meaning at the section's values is `linkTailR`'s
  check (`terminalOfFacts`).
-/

module

public import LeanVM.Guest.B1.Link.Arith.Reads

/-!
# The terminal check

`link_terminal_sound` at the dispatch gives `LtHolds` at the chunking: for the index point's words,
the message's `64` bit-slices, the twelve shift coefficients stored at `shifts` and `ν`'s words
at `ζ·g^w`, the summand plus `rest` is the claim. At the section's values (`linkSecStatement`,
from `readsOfFacts`), `coef`, `shifts`, `cert_w·cert` and `rest` are the row side's, so the
equation is `linkTailR`'s (`TailCheck`), `cert·cert_weight·ν` against `(cert_w·cert)·ν`.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Guest.B1.Link LeanVM.Guest.B1

@[expose] public section

theorem tailNValues_layoutOf (lm lb : ℕ) (bc : List K) (rows : List ℕ) (pl : List (Option Placement))
    (sl : ℕ) (hts : List ℕ) : tailNValues (layoutOf lm lb bc rows pl sl hts) = 80 := by kernel_eq

theorem maxShift_tables : tables.foldl (fun m t ↦ max m t.links.maxShift) 0 = 12 := by decide +kernel

section

variable {rd : Reader} {σ : Val} {lm lb : ℕ} {bc : List K} {rows : List ℕ}
  {pl : List (Option Placement)} {sl : ℕ} {hts : List ℕ} {chunks : Chunks} {theta0 : E}
  {drawn r : List E} {m1 : E} {fresh splitv chi qPoint message : List E} {p : ℕ}
  (hA : ∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ)
  (F : LinkFacts rd σ (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh splitv chi
    qPoint message p)

include hA F in
/-- `ν`'s words: the drawn challenges from `88 + n_rows + w`. -/
theorem nuAt (hc : Chunks.new chunks.width = some chunks) : ∀ i < chunks.d,
    LoadHolds rd (σ (.n 695)) i (drawn.getD (88 + hts.foldl max 0 + chunks.width + i) 0) := by
  intro i hi
  obtain ⟨h694, h692, h695⟩ := zetaAtoms hA
  have hlen : 88 + hts.foldl max 0 + chunks.width + chunks.d ≤
      linkDrawn (layoutOf lm lb bc rows pl sl hts) chunks := by
    rw [linkDrawn_eq, hc]; simp
  have hd := drawnAt F (88 + hts.foldl max 0 + chunks.width + i) (by omega)
  rw [h695, h694, h692, word_g88, F.gN, F.gW, mul_assoc, mul_assoc, ← pow_add, ← pow_add,
    loadHolds_mul_gen_pow]
  simpa [linkRows, Nat.add_assoc] using hd

end

/-- **The terminal check holds.** -/
theorem terminalOfFacts : TerminalOfFacts := by
  intro rd σ layout chunks theta0 drawn r m1 fresh splitv chi qPoint message p claim hA hs hlb F T
  have hreads := readsOfFacts rd σ layout chunks theta0 drawn r m1 fresh splitv chi qPoint message p hA hs
    hlb F
  have hst := linkSecStatement rd σ layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hA
    hreads hs hlb
  have hrow := rowIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  obtain ⟨htab, hd, -, -, -, -⟩ := hs
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab hlb
  subst htab hlb
  change LinkFacts rd σ (layoutOf lm 19 bc rows pl sl hts) chunks theta0 drawn r m1 fresh splitv chi
    qPoint message p at F
  dsimp only at hst hrow
  obtain ⟨-, -, -, -, -, -, hcoef, -, hrest, -, hcert, hshifts⟩ := hst
  obtain ⟨-, hsh, -, -⟩ := hrow
  have hd' : 88 ≤ drawn.length := hd
  have hw1 := F.widthGe
  have hw2 := F.widthLe
  have hlt := link_terminal_sound chunks.width hw1 hw2 rd _ _ T.terminal
  simp only [MeaningLinkTerminal] at hlt
  have hlt := hlt.2 chunks T.chunksEq
  set L := tailLets (layoutOf lm 19 bc rows pl sl hts) chunks theta0 drawn r m1 fresh
    (Split.ofColumns tables splitv) qPoint with hL
  set R := tailRowSide (layoutOf lm 19 bc rows pl sl hts) chunks theta0 drawn r m1 fresh
    (Split.ofColumns tables splitv) chi qPoint message with hR
  -- the shift coefficients' words
  have hshl : R.shifts.length = 12 := by rw [← hsh, gShifts, List.length_map, List.length_range]
  have hshR : ReadsAt rd (σ (.n 19)) R.shifts := by
    intro s hs
    obtain ⟨hat, -⟩ := secR_shifts s (by omega)
    have hl : LoadHolds rd (σ (.n 19)) s (σ (.n (shiftStores.getD s (0, 0)).2)) := hA _ (mem_of_atomAt hat)
    have e := hshifts s (by omega)
    rw [rdw_of_load hl, getD_eq_getElem' hs] at e
    rwa [e] at hl
  -- `ν`'s words
  have hnu : L.nu = (List.range chunks.d).map fun i ↦
      drawn.getD (88 + hts.foldl max 0 + chunks.width + i) 0 := by
    have hlen : 88 + hts.foldl max 0 + chunks.width + chunks.d ≤ drawn.length := by
      have hdl : drawn.length = linkDrawn (layoutOf lm 19 bc rows pl sl hts) chunks := by
        rw [F.drawnEq, List.length_take, pkSqueeze_length]
        exact Nat.min_eq_left F.drawnLe
      rw [hdl, linkDrawn_eq, T.chunksEq]; simp
    rw [hL, lets_nu hd', List.drop_drop, List.drop_drop, dt_eq _ _ _ (by omega)]
    refine List.map_congr_left fun i _ ↦ ?_
    congr 1; omega
  have hnuR : ReadsAt rd (σ (.n 695)) L.nu := by
    rw [hnu]; exact readsAt_range_map (nuAt hA F T.chunksEq)
  have hml : message.length = 144 := T.messageLen
  have h := hlt r (message.drop 80) R.shifts L.nu F.pointLen (by rw [List.length_drop, hml]) hshl
    (by rw [hnu, List.length_map, List.length_range]) F.point (fun k hk ↦ by
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
      exact T.slices k hk) hshR hnuR
  rw [hcoef, hcert, hrest, T.claimEq] at h
  unfold TailCheck
  dsimp only
  rw [tailNValues_layoutOf]
  show (Functionals.new chunks r (tables.foldl (fun m t ↦ max m t.links.maxShift) 0)).summand R.coef R.shifts
      ((Functionals.new chunks r (tables.foldl (fun m t ↦ max m t.links.maxShift) 0)).values chunks
        (message.drop 80)) (L.nu.map fun n ↦ L.cert * R.certWeight * n) +
      prodE (qPoint.map (1 + ·)) * R.base = claim
  rw [maxShift_tables, show L.nu.map (fun n ↦ L.cert * R.certWeight * n) = L.nu.map
    ((R.certWeight * L.cert) * ·) from List.map_congr_left fun n _ ↦ by rw [mul_comm L.cert]]
  exact h

end

end LeanVM.Guest.B1.Link.Arith
