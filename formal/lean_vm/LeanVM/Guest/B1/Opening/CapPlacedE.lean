/-
  LeanVM.Guest.B1.Opening.CapPlacedE

  Leaf callees, `verify_merkle_cap` among them, complete by a tree of exactly their frame.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedE
public import LeanVM.Guest.B1.Fs.LeafPlaced
public import LeanVM.Guest.B1.Merkle.CapAll
public import LeanVM.Guest.Lift.OsCallees
public import LeanVM.Guest.B1.Place.OsMean

/-!
# Leaves, exact trees

`total_leaf_eq`: a leaf's valid trees are exactly its frame (`totalLe_leaf`, as an equality).
`completeAtE_of_relIn`: a pure function loading the caller's words is `CompleteAtE` by exactly the
words every valid tree of it takes (`completeAtDTB_of_relIn`, exact). `completeAtE_of_leaf`: a leaf
whose relation is its meaning, its loads in the caller's regions, is `CompleteAtE … (fs f)`
(`completeRelRegDB_of_iff`, exact). `verify_merkle_cap_completeAtE`: the deployed
`verify_merkle_cap__L{d}`, its placed tree exactly its frame; `verify_merkle_cap_completeAtE_of_kind`:
at a cap depth `osKindOf` names.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (natStr)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A leaf's trees are exactly its frame.** -/
theorem total_leaf_eq {f : String} {spec : List (ℕ × ℕ)} (hok : LeafSpecOk f spec) :
    ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.total fs = fs f := by
  obtain ⟨fn, hf, -, hleaf⟩ := hok
  intro rd t args rets hn hv hb
  cases t with
  | phantom => exact hv.elim
  | node g σ bufs kids =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hf', -, es, vs, hw, -, -, hkv⟩ := hv
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    have hall := Lift.walk_leafOk (σ := σ) _ hleaf
    rw [hw] at hall
    have hpure : ∀ e ∈ es, e.pure [g] := by
      have := walk_pure (σ := σ) fn.body
        (Lift.pureIn_of_leafOk hf hleaf g (List.mem_singleton_self _) fn hf)
      rwa [hw] at this
    rw [Lift.calls_nil_of_leafOk hall] at hkv
    rw [Tree.BufsOk, events_node hf hw, allocs_pure hpure] at hb
    obtain ⟨rfl, -⟩ := hb
    match kids, hkv with
    | [], _ => simp [total_node, Tree.totalKids]

/-- **A pure function loading the caller's words, by exactly `B` words**, every valid tree of it
at `args` taking exactly `B`. -/
theorem completeAtE_of_relIn {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) {κ : ℕ} {Lin : Layout} {args rets : List E} {B : ℕ}
    (hB : ∀ (rd : Reader) (t : Tree) (rets' : List E), t.name = g →
      t.Valid coreProgram rd args rets' → t.BufsOk coreProgram → t.total fs = B)
    (h : ∀ rd, LowDef κ rd → MemL rd Lin → coreProgram.RelIn rd (RegionL Lin) g args rets) :
    CompleteAtE fs cert κ g Lin args (Returns rets) B := by
  refine CompleteAtE.of_eq fun fp ↦ ?_
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨B, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, rfl,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨t, hn, hv, hb, hlr⟩ := h _ (Lift.lowLin_low (Lin := Lin) hl1) (Lift.lowLin_memL hL1)
  refine ⟨t.total fs, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, hB _ t rets hn hv hb,
    fun rd hl hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  have hr := relAtIn_transfer (fs := fs) (cert := cert) (D := fun _ => False) (fp := fp)
    coreProgram_fresh hn hv hb (placed_of_pure hS t hv hb (hn ▸ hg) _)
    (loadsIn_of_loadsR t _ _ hlr) (fun _ h => h.elim) rd
    (fun i hi => hi.elim (fun hi => ?_) fun hd => (not_data_of_pure hS t hv hb (hn ▸ hg) _ i hd).elim)
    (fun A hA => ?_)
  · refine relAtIn_dmono hr fun i hi => ?_
    obtain ⟨q, hq, _⟩ := hi; simp at hq
  · rw [Lift.lowLin, B1.Main.restrict_of ⟨i, rfl, Or.inl hi⟩, B1.Main.memL_agree hL' hL1 i hi]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi | hi⟩ := B1.Main.restrict_supp' rd1 _ _ _ hv
    · rw [B1.Main.memL_agree hL' hL1 i hi, ← B1.Main.restrict_of (rd := rd1)
        (S := fun i => RegionL Lin i ∨ i < 2 ^ κ) ⟨i, rfl, Or.inl hi⟩]
      exact Option.isSome_iff_exists.mpr ⟨v, hv⟩
    · exact hl i hi

/-- **A leaf callee whose relation is its meaning, placed on its regions, by exactly its frame.** -/
theorem completeAtE_of_leaf {f : String} {spec : List (ℕ × ℕ)}
    {Pre : Reader → List E → List E → Prop} (hok : LeafSpecOk f spec)
    (hiff : ∀ rd args rets, coreProgram.Rel rd f args rets ↔ Pre rd args rets) (κ : ℕ)
    {args rets : List E} {Lin : Layout} (hreg : RegPtrs spec args (RegionL Lin))
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → Pre rd args rets) :
    CompleteAtE fs cert κ f Lin args (Returns rets) (fs f) := by
  have hT := total_leaf_eq (fs := fs) hok
  obtain ⟨fn, hf, hpar, hleaf⟩ := hok
  refine completeAtE_of_relIn (Lift.pureIn_of_leafOk hf hleaf) (List.mem_singleton_self _)
    (fun rd t rets' hn hv hb ↦ hT rd t args rets' hn hv hb)
    fun rd hl hL => Lift.relIn_of_leaf hf hleaf (fun σ es vs hp hw A hA => ?_)
      ((hiff rd args rets).mpr (hpre rd hl hL))
  have hall := Lift.walk_leafOk (σ := σ) fn.body hleaf
  rw [hw] at hall
  obtain ⟨q, hq, off, hoff, rfl⟩ := loads_spec hall A hA
  have hσ : σ (.n q.1) = args.getD q.1 0 := by
    have h1 := hpar q hq
    have h2 : (fn.params.map σ)[q.1]? = args[q.1]? := by rw [hp]
    rw [List.getElem?_map, h1] at h2
    simp only [Option.map_some] at h2
    rw [List.getD_eq_getElem?_getD, ← h2]
    rfl
  rw [hσ]
  exact hreg q hq off hoff

/-- **The deployed `verify_merkle_cap`, by exactly its frame**: on a cap and flags buffer in the
caller's regions holding a cap that checks to the root, its placed tree is its frame. -/
theorem verify_merkle_cap_completeAtE {p : String × ℕ} (hp : p ∈ merkleCapNames) (κ : ℕ)
    {args rets : List E} {Lin : Layout} (hreg : RegPtrs (merkleCapSpec p.2) args (RegionL Lin))
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → MeaningVerifyMerkleCap p.2 rd args rets) :
    CompleteAtE fs cert κ p.1 Lin args (Returns rets) (fs p.1) :=
  completeAtE_of_leaf (leafSpecOk_all merkleCap_leafSpec p hp) (verify_merkle_cap_holds p hp) κ hreg hpre

/-- **`verify_merkle_cap__L{cd}`, by exactly its frame**, at a cap depth `osKindOf` names. -/
theorem verify_merkle_cap_completeAtE_of_kind {cd : ℕ}
    (hK : osKindOf ("verify_merkle_cap__L" ++ natStr cd) = some (.cap cd)) (κ : ℕ) :
    ∀ (args rets : List E) (Lin : Layout), RegPtrs (merkleCapSpec cd) args (RegionL Lin) →
      (∀ rd, LowDef κ rd → MemL rd Lin → MeaningVerifyMerkleCap cd rd args rets) →
      CompleteAtE fs cert κ ("verify_merkle_cap__L" ++ natStr cd) Lin args (Returns rets)
        (fs ("verify_merkle_cap__L" ++ natStr cd)) := by
  intro args rets Lin hreg hpre
  have he := osKindEntry_ok hK
  simp only [osKindEntryOk, decide_eq_true_eq] at he
  exact verify_merkle_cap_completeAtE (p := ("verify_merkle_cap__L" ++ natStr cd, cd)) he κ hreg hpre

end
end LeanVM.Guest.B1
