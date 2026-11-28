/-
  LeanVM.Prover.Complete.Keccak

  The Keccak phase of the honest script wins step 5 of `verifyExecution`, and leaves claims that
  hold of the witness's columns.
-/

module

public import LeanVM.Prover.Complete.Keccak.Exec.Reduction
public import LeanVM.Prover.Complete.Keccak.Witness

/-!
# The Keccak phase

Step 5 of `verifyExecution` is `keccakValidity layout link`: the `KECCAK` table's output lanes'
values the link left at its row point, then the Keccak reduction (`verifyKeccak`). The honest
script plays `KeccakGkr.keccakPhaseProve` beside it (`Script.alongside`).

`wins_keccak`: on the honest witness, where the link's values of the output lanes are the
extensions of the witness's output columns at its point, this wins (from a clear sponge, every
grind at most `3` bits) and the program returns the column claims on `q_keccak`, which hold of the
witness's columns, and the `64` slices of `q_keccak` at a point, which hold of its column.

The proof: the honest prover makes the moves of the specification `hKeccak`
(`corr_keccak`, `Keccak/Exec/`), which wins `verifyKeccak` (`wins_keccak_spec`, `Keccak/Gkr`) on
a column whose middle state is twelve rounds of its input (`midAgree_witness`) and whose output
claims are twelve rounds from it (`outClaimsTrueMid_witness`), both from the witness's rows
(`Keccak/Witness`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Extraction Finset

/-- A list's `mapM` in `Option` where every value is some. -/
theorem mapM_some {α β : Type} (f : α → Option β) (d : β) :
    ∀ l : List α, (∀ x ∈ l, (f x).isSome) → l.mapM f = some (l.map fun x ↦ (f x).getD d)
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h x (by simp))
    rw [List.mapM_cons, hb, mapM_some f d l (fun y hy ↦ h y (by simp [hy]))]
    simp [hb]

/-- The `KECCAK` table's log-height is at least its floor. -/
theorem keccakHeight_ge {bytecode : List K} {logMemory : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode logMemory rows = some layout) :
    keccakMinStepsLog ≤ layout.tableLogHeights.getD opKeccak 0 := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · rename_i hc
      cases h
      have h5 : 5 < rows.length := by rw [hc.2.2.2.2.2]; decide
      simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith, opKeccak,
        List.getElem?_eq_getElem h5, tableLogFloors]
      simp
    · cases h

/-- **The Keccak phase wins.** On the honest witness, where the link's values of the `KECCAK`
output lanes at its row point (one per lane, `hmem`) are the extensions of the witness's columns
(`hlink`) at a point of the table's log-height (`hpt`), the honest Keccak phase beside
`keccakValidity` wins from a clear sponge, and the program returns the column claims on
`q_keccak` (one), holding of the witness's columns, and `64` slices of `q_keccak` at a point,
holding of its column. -/
theorem wins_keccak {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {W : Witness} (hW : witness? prog input t = some W) (link : LinkEnd)
    (hpt : (link.columns.getD opKeccak ([], [])).1.length =
      W.layout.tableLogHeights.getD opKeccak 0)
    (hmem : ∀ lane < keccakStateLanes,
      ∃ v, (keccakOut + lane, v) ∈ (link.columns.getD opKeccak ([], [])).2)
    (hlink : ∀ cv ∈ (link.columns.getD opKeccak ([], [])).2,
      cv.2 = mleK (W.cols.getD (globalColumnBases.getD opKeccak 0 + cv.1) #[])
        (link.columns.getD opKeccak ([], [])).1)
    (cs : List Committed) :
    Wins 17 (fun a b g' cs' ↦ a = b ∧ g' = false ∧ cs' = cs ∧
        (∀ c ∈ a.1, c.HoldsIn W.cols ∧ c.column = qkeccak ∧
          c.point.length = W.layout.tableLogHeights.getD opKeccak 0 + qkeccakSlotBits) ∧
        SlicesHoldIn (W.cols.getD qkeccak #[]) a.2.1 a.2.2 ∧
        a.2.1.length = W.layout.tableLogHeights.getD opKeccak 0 + qkeccakSlotBits ∧
        a.2.2.length = kBits ∧ a.1.length = 1)
      (keccakValidity W.layout link)
      (Script.alongside (keccakValidity W.layout link)
        (KeccakGkr.keccakPhaseProve (W.layout.tableLogHeights.getD opKeccak 0) W.cols link))
      false cs := by
  obtain ⟨-, steps, -, -, hlay, -, -, hcols, -⟩ := witness?_spec hW
  have hτ9 := keccakHeight_ge hlay
  obtain ⟨P, hP⟩ : ∃ P, W.layout.tableLogHeights.getD opKeccak 0 = P + 4 :=
    ⟨_, (Nat.sub_add_cancel (le_trans (by decide) hτ9)).symm⟩
  set tabs := rowsOf ⟨powIndex t.logMemorySize, t.memory, W.chunks⟩ steps with htabs
  set R := tabs.getD opKeccak #[] with hR
  rcases hpv : link.columns.getD opKeccak ([], []) with ⟨point, values⟩
  rw [hpv] at hpt hmem hlink
  dsimp only at hpt hmem hlink
  rw [hP] at hpt
  -- the output lanes' values
  have hsome : ∀ lane ∈ List.range keccakStateLanes,
      ((values.find? fun v ↦ v.1 = keccakOut + lane).map (·.2)).isSome := by
    intro lane hl
    obtain ⟨v, hv⟩ := hmem lane (List.mem_range.1 hl)
    rw [Option.isSome_map]
    exact List.find?_isSome.2 ⟨_, hv, by simp⟩
  set output := (List.range keccakStateLanes).map fun lane ↦
    ((values.find? fun v ↦ v.1 = keccakOut + lane).map (·.2)).getD 0 with houtput
  have hmap := mapM_some (fun lane ↦ (values.find? fun v ↦ v.1 = keccakOut + lane).map (·.2)) 0
    _ hsome
  have hprog : keccakValidity W.layout link = verifyKeccak (P + 4) point output := by
    unfold keccakValidity
    rw [hpv]
    simp only [hmap, hP]
    rfl
  have hqk : W.cols.getD qkeccak #[] = qkeccakColumn R (P + 4) := by
    rw [hcols, colsOf_qkeccak, hP]
  have hscript : KeccakGkr.keccakPhaseProve (W.layout.tableLogHeights.getD opKeccak 0) W.cols link =
      KeccakGkr.keccakProve (qkCol R (P + 4)) P point output := by
    unfold KeccakGkr.keccakPhaseProve
    rw [hpv, hqk, hP, Nat.add_sub_cancel]
    rfl
  rw [hscript, hprog]
  -- the statements the reduction starts from
  have ho : ∀ l < 25, output.getD l 0 =
      mleK (tableColumn R (paddingRow opKeccak) (P + 4) (keccakOut + l)) point := by
    intro l hl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 (by
      obtain ⟨v, hv⟩ := hmem l hl
      exact ⟨_, hv, by simp⟩) : (values.find? fun v ↦ v.1 = keccakOut + l).isSome)
    have hvm := List.mem_of_find?_eq_some hv
    have hv1 : v.1 = keccakOut + l := by simpa using List.find?_some hv
    rw [houtput, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by simpa [keccakStateLanes] using hl)]
    simp only [Option.map_some, Option.getD_some, hv]
    rw [hlink v hvm, hv1, hcols, colsOf_keccakOut _ _ _ hl, hP]
  have hlen : output.length = 25 := by simp [houtput, keccakStateLanes]
  have hmid := outClaimsTrueMid_witness R (kRow_rowsOf _ steps) (P + 4) hpt ho
  have hagree := midAgree_witness R (P + 4) point
  have hspec := wins_keccak_spec (B := 17) P (by norm_num) (qkCol R (P + 4)) hpt hlen hmid hagree
    cs
  have hcorr := LeanVM.Prover.KeccakGkr.corr_keccak (P := P) (col' := qkCol R (P + 4))
    (col := qkCol R (P + 4)) (fun _ _ ↦ rfl) hpt output
  have h3 := Wins.alongside _ _ _ _ (Wins.corr _ _ _ _ _ hcorr hspec)
  refine LeanVM.Prover.Wins.mono (fun a a' g' cs' h ↦ ?_) _ _ _ _ h3
  obtain ⟨rfl, -, b, -, rfl, hcol, hsl, hl1, hg, hcs⟩ := h
  have hsize : (W.cols.getD qkeccak #[]).size = 2 ^ (P + 4 + 6) := by
    rw [hqk, qkeccakColumn_size]
  have hslot : qkeccakSlotBits = 6 := qkeccakSlotBits_six
  refine ⟨rfl, hg, hcs, fun c hc ↦ ?_, ⟨hsl.2.1, fun i hi ↦ ?_⟩, ?_, hsl.2.1, hl1⟩
  · obtain ⟨hcc, hcp, hcv⟩ := hcol c hc
    refine ⟨?_, hcc, by rw [hcp, hP, hslot]⟩
    rw [ColumnClaim.HoldsIn, hcc, mleK_eq_sum _ _ (by rw [hsize, hcp]), hcp, hcv, hqk]
    rfl
  · rw [hsl.2.2 i hi, mleA_bitSlice _ _ (by rw [hsize, hsl.1]), hsl.1, hqk]
    rfl
  · rw [hsl.1, hP, hslot]

end LeanVM.Prover.Complete.Keccak

end
