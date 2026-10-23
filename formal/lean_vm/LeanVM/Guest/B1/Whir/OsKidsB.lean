/-
  LeanVM.Guest.B1.Whir.OsKidsB

  `open_stacked`'s callees after each level's positions, complete on the caller's words.
-/

module

public import LeanVM.Guest.B1.Whir.OsKidsA
public import LeanVM.Guest.B1.Whir.CapAt
public import LeanVM.Guest.B1.Whir.QueriesAt

/-!
# The callees after the positions (TRIAGE #36)

On the caller's words, at their honest arguments and returns: the row weights (the level's fold
challenges and its buffer of weights), the cap (`OsCap`'s cells and flags), the queries (on every
memory holding them, their words `OqTopMem`; where they lie follows, `os_oqTopReg_of`), the query
sum the level's enforced sum (`os_oqSum_eq`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **The row weights**, the challenges read at `point`, the weights stored at `out`. -/
theorem os_kid_rw {name : String} {folds rev : ℕ} (hr : OsRowWeightsAtD fs cert κ name folds rev) {Lk : Main.Layout}
    {point out : E} {rs : List E} (hl : rs.length = folds)
    (hM : ∀ rd, MemL rd Lk → ReadsAt rd point rs ∧
      ReadsAt rd out ((List.range (2 ^ folds)).map fun i => (eqKernel rs).getD (orwSlot folds rev i) 0)) :
    osKC fs cert κ Lk name [point, out] [] :=
  hr _ _ Lk fun rd hm => ⟨rfl, rs, hl, (hM rd hm).1, fun i hi => by
    have := os_readsAt_getD (hM rd hm).2 (k := i) (by simpa using hi)
    rwa [os_getD_map_range _ hi] at this⟩

/-- **The cap**, its cells and flags the level's openings fill. -/
theorem os_kid_cap {name : String} {cd depth : ℕ} (hv : VmcCompleteAt fs cert κ cd name) {Lk : Main.Layout}
    {rt : Digest} {qs : List (ℕ × Opening)} (hok : OsCapOk depth cd rt qs) {cap flags : E}
    (hM : ∀ rd, MemL rd Lk → ReadsAt rd cap (osCapCells depth cd qs) ∧ ReadsAt rd flags (osCapFlags depth cd qs)) :
    osKC fs cert κ Lk name [cap, flags] [(digestScalars rt).1, (digestScalars rt).2] :=
  hv Lk cap flags _ fun rd hm => osCap_meaning hok (hM rd hm).1 (hM rd hm).2

/-- A callee complete on every memory holding its words some defined-low memory holds. -/
theorem os_completeAt_of_nonempty {f : String} {Lin : Main.Layout} {args rets : List E}
    (h : ∀ rd0, LowDef κ rd0 → MemL rd0 Lin → CompleteAtD fs cert κ f Lin args (Returns rets)) :
    CompleteAtD fs cert κ f Lin args (Returns rets) := by
  classical
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  · obtain ⟨rd0, h1, h2⟩ := hex; exact h rd0 h1 h2
  · intro fp
    exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- **Where the queries' words lie**, from what every memory holding them reads. -/
theorem os_oqTopReg_of {Lin : Main.Layout} {I pd cd : ℕ} {rew qw qbp flags cap : E} {wts qwV dbpV : ℕ → E}
    {leaf : ℕ → List K} {pos : ℕ → ℕ} {sibs : ℕ → List Digest} {n : ℕ}
    (h : ∀ rd, LowDef κ rd → MemL rd Lin → OqTopMem rd I pd cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n)
    {rd0 : Reader} (h1 : LowDef κ rd0) (h2 : MemL rd0 Lin) :
    OqTopReg (RegionL Lin) I pd cd rew qw qbp flags cap dbpV pos n := by
  refine ⟨fun jw hjw => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj l hl => ?_, fun j hj => ?_, fun j hj => ⟨?_, ?_⟩⟩
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).1 jw hjw).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.1 j hj).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.1 j hj).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.2.1 j hj l hl).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.2.2.1 j hj).2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.2.2.2 j hj).1.2) h1 h2
  · exact os_addr_in_regionL (fun rd hlw hm => ((h rd hlw hm).2.2.2.2.2 j hj).2.2) h1 h2

/-- **The queries**, on every memory holding their words. -/
theorem os_kid_queries {base I depth cd : ℕ} {name : String} (hq : OqCompleteAt fs cert κ base I depth cd name)
    {Lin : Main.Layout} {cap flags qw qbp rew : E} {n : ℕ} (hn : n + 1 < ordG) {leaf : ℕ → List K} {pos : ℕ → ℕ}
    {sibs : ℕ → List Digest} {wts qwV dbpV : ℕ → E} (hleaf : ∀ j < n, (leaf j).length = oqR base I)
    (hpos : ∀ j < n, pos j < 2 ^ depth) (hsl : ∀ j < n, (sibs j).length = depth - cd)
    (hlin : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqTopMem rd I (depth - cd) cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n) :
    CompleteAtD fs cert κ name Lin [cap, flags, qw, qbp, rew, gen ^ n] (Returns [oqSum base I wts qwV leaf n]) :=
  os_completeAt_of_nonempty fun _ h1 h2 =>
    hq n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hpos hsl hlin (os_oqTopReg_of hlin h1 h2)

/-- **The query sum is the level's enforced sum.** -/
theorem os_oqSum_eq {l folds : ℕ} {chs : List E} (hchs : chs.length = folds) (lam : E) {os1 : List Opening}
    (hlen : ∀ j (hj : j < os1.length), (os1[j]).leaf.length = oqR (if l = 0 then 1 else 0) (2 ^ folds)) :
    oqSum (if l = 0 then 1 else 0) (2 ^ folds) (fun jw => (eqKernel chs).getD (orwSlot folds (if l = 0 then 1 else 0) jw) 0)
      (fun i => lam ^ i) (fun i => (os1.getD i ⟨[], []⟩).leaf) os1.length =
      enforcedSum (osRowsOf l (os1.map (·.leaf))) chs (powers lam os1.length) := by
  have hrl : (osRowsOf l (os1.map (·.leaf))).length = os1.length := by unfold osRowsOf; split <;> simp
  rw [os_enforcedSum_eq _ _ _ (by rw [hrl]; simp [powers, os_length_powersFrom]), hrl]
  unfold oqSum
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [os_powers_getD hi']
  congr 1
  have hrow : (osRowsOf l (os1.map (·.leaf))).getD i [] =
      if l = 0 then (os1[i]).leaf.reverse.map ofK else extRow (os1[i]).leaf := by
    unfold osRowsOf; split <;> simp [List.getD_eq_getElem?_getD, hi']
  rw [hrow]
  show ∑ jw ∈ Finset.range (2 ^ folds), leafRowWord _ (os1.getD i ⟨[], []⟩).leaf jw * _ = _
  rw [List.getD_eq_getElem _ _ hi']
  have hl := hlen i hi'
  by_cases h0 : l = 0
  · simp only [h0, ↓reduceIte] at hl ⊢
    exact (os_dot_row0 (by rw [hl]; simp [oqR]) hchs).symm
  · simp only [h0, ↓reduceIte] at hl ⊢
    exact (os_dot_rowExt (by rw [hl]; simp [oqR]) hchs).symm

end
end LeanVM.Guest.B1
