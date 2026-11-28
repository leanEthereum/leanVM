module

public import LeanVM.Guest.Complete.DaVerifyNodeA
public import LeanVM.Guest.Complete.MainCalleesA
public import LeanVM.Guest.Complete.DaWsA
public import LeanVM.Guest.Complete.FsSmall

/-!
# The field `da` of `MainCalleesAt`

`da_verify(byte_bits)` placed at `main`'s honest arguments (`da_field`): the count table is
`main`'s byte table (`mBase m 3`, inside `mainR`), the witness opens the claim (`DaDigestHeld`),
and its pops are the honest pushes' DA hints stream by stream (`sameStreams_da`: the count and the
challenge in the other order, the blobs' cells the rows' cells). Given `da_vector` and `da_weights`
placed (`DaVectorCompleteA`, `DaWeightsCompleteA`), which hold at the compiled frames (`DaVecA`,
`DaWsA`): `da_field_b2c`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

theorem flatMap_range_getD {α β : Type} (l : List α) (d : α) (f : α → List β) :
    l.flatMap f = (List.range l.length).flatMap fun i => f (l.getD i d) := by
  have h : (List.range l.length).map (fun i => f (l.getD i d)) = l.map f :=
    List.ext_getElem (by simp) fun i h1 h2 => by
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  simp only [List.flatMap_def, h]

/-- **`da_verify`'s pops are the honest DA hints, stream by stream.** -/
theorem sameStreams_da (c : DaClaim) (mw : LeanVM.Da.MatrixWitness) :
    SameStreams (dvPops' c.membershipChallenge mw.rows.length (wSyms mw)) (Prover.daHints c mw) := by
  have ht : dvPops (wSyms mw) 0 mw.rows.length = mw.rows.flatMap fun row =>
      (List.range LeanDa.cellsPerRow).map fun j =>
        (("da_symbols" : String), (row.drop (j * LeanDa.cellSymbols)).take LeanDa.cellSymbols) := by
    rw [flatMap_range_getD _ [], dvPops, ← List.range_eq_range', List.flatMap_def, List.flatMap_def]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [show LeanDa.cellsPerRow = 128 from rfl]
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    simp [wSyms, hi', hj', LeanDa.listCell]
  intro s
  rw [dvPops', Prover.daHints, ht]
  by_cases h1 : "da_n_blobs" = s
  · subst h1; simp [Prover.count, LeanVM.Protocol.Verifier.gpow]
  · by_cases h2 : "da_challenge" = s
    · subst h2; simp
    · simp [h1, h2]

theorem mBase3_eq (m : MainCounts) :
    mBase m 3 = B2C.fs "main" + 4 * m.sx + 4 * m.ss + (m.sx + m.ss) := by
  simp [mBase, MainCounts.bufs, bases]

theorem mTop_eq (m : MainCounts) :
    mTop m = B2C.fs "main" + (4 * m.sx + (4 * m.ss + (m.sx + m.ss + (256 + (2 * (m.nc + 1) + (2 * m.nc +
      (55 * m.nc + (26 * m.nc + (m.nc + 1 + 26))))))))) := by
  simp [mTop, MainCounts.bufs]

/-- **The field `da` of `MainCalleesAt`**, given the dual codeword's builders placed. -/
theorem da_field (hwf : coreProgram.Wf) {al : String → Bool} {k : ℕ} (hk : 16 ≤ k)
    (hV : DaVectorCompleteA B2C.fs al B2C.cert k) (hWs : DaWeightsCompleteA B2C.fs al B2C.cert k)
    {s : NodeStatement} {w : NodeWitness} {cover : List E} (hda : DaDigestHeld s w) :
    ∀ c mw, w.daMatrix = some (c, mw) → AtEveryB al k "da_verify" [mPtr (mainCounts s w) 3 0]
      (Prover.digestCells c.daRoot ++ [c.membershipChallenge]) (mainR al (mainCounts s w))
      (MainPreA al s w cover) (PopsPost (Prover.daHints c mw)) (B2C.fs "da_verify") (mLo al (mainCounts s w))
      (2 ^ 60) (2 ^ 40) := by
  intro c mw hm fp cur _ hfc
  have hop : mw.Opens c.daRoot c.membershipChallenge := by
    unfold DaDigestHeld at hda; rw [hm] at hda; exact hda.2
  set m := mainCounts s w
  have hR : ∀ j ≤ LeanDa.maxRows, mainR al m (mBase m 3 + 0 + j) := by
    intro j hj
    have h1 := mBase3_eq m
    have h2 := mTop_eq m
    have : LeanDa.maxRows = 32 := rfl
    exact Or.inl ⟨by omega, by omega⟩
  obtain ⟨e, he, h⟩ := dv_callAtA (fs := B2C.fs) (al := al) (cert := B2C.cert) fs_lt16 hwf hk hV hWs hop
    (qb := mBase m 3 + 0) (R := mainR al m) hR hfc
  refine ⟨e, fun _ => he.trans (by omega), h.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd hp => ?_)
    (fun rd t _ hq => ⟨by rw [hq.1]; exact sameStreams_da c mw, hq.2⟩)⟩
  intro v hv
  have hW := hp.1 (mBase m 3, (List.range 256).map fun v => word v 0) (by simp [mainWords, m])
  have hv' : v < 256 := by have : LeanDa.maxRows = 32 := rfl; omega
  have := loadHolds_of_readsAt hW (i := v) (by simp; omega)
  have e : ((List.range 256).map fun v => word v 0).getD v 0 = word v 0 := by
    rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
  rw [e] at this
  rw [Nat.add_zero]
  exact this

/-- **The field `da` of `MainCalleesAt`**, the dual codeword's builders placed at the compiled frames. -/
theorem da_field_b2c (hwf : coreProgram.Wf) {al : String → Bool} {k : ℕ} (hk : 16 ≤ k)
    {s : NodeStatement} {w : NodeWitness} {cover : List E} (hda : DaDigestHeld s w) :
    ∀ c mw, w.daMatrix = some (c, mw) → AtEveryB al k "da_verify" [mPtr (mainCounts s w) 3 0]
      (Prover.digestCells c.daRoot ++ [c.membershipChallenge]) (mainR al (mainCounts s w))
      (MainPreA al s w cover) (PopsPost (Prover.daHints c mw)) (B2C.fs "da_verify") (mLo al (mainCounts s w))
      (2 ^ 60) (2 ^ 40) :=
  da_field hwf hk (daVectorCompleteA_b2c al k) (daWeightsCompleteA_b2c al k) hda

end
end LeanVM.Guest.Complete
