/-
  LeanVM.Guest.B1.Digest.SmallAt

  `statement_digest`, `da_list_digest` and `cover_da_root` complete in the uniform placed form
  (`CompleteRel`), at pinned memory witnesses.
-/

module

public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Da.ListDigest
public import LeanVM.Guest.B1.Digest.NodeAt
public import LeanVM.Guest.Memory.Size

/-!
# The small callees of `main`, uniformly placed

Each precondition pins the words the function reads (`SdPreAt sig cells`, `DaListPreAt claims`,
`CoverPreAt i`), so every read is a word of the caller's layout (`forced_load`), the same in every
memory holding it (`load_agree`). `statement_digest` and `da_list_digest` range check nothing and
are pure: `completeAt_of_rel_pure`. `cover_da_root` range checks its slot: `completeAt_leaf` on its
honest run.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.Node
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAt CompleteAtD CompleteAtB CompleteRel CompleteRelD DisjL disj_nil Within Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- A load every memory of the class makes, the same in every memory holding the caller's words. -/
theorem forced_agree {κ : ℕ} {Lin : Layout} {p : E} {k : ℕ} {v : E}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin → LoadHolds rd p k v) {rd1 : Reader} (h1 : LowDef κ rd1)
    (h1' : MemL rd1 Lin) {rd : Reader} (h : MemL rd Lin) : LoadHolds rd p k v := by
  obtain ⟨i, hi, hR⟩ := forced_load hall h1 h1'
  exact load_agree h h1' hi hR (hall rd1 h1 h1')

/-- The class is empty, or a memory of it exists. -/
theorem completeRel_cases {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Pre : Reader → List E → List E → Prop}
    (h : ∀ args rets Lin, (∀ rd, LowDef κ rd → MemL rd Lin → Pre rd args rets) →
      ∀ rd1, LowDef κ rd1 → MemL rd1 Lin → CompleteAt fs cert κ f Lin args (Returns rets)) :
    CompleteRel fs cert κ f Pre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    exact h args rets Lin hpre rd1 hl1 hL1 fp
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL

/-- The class is empty, or a memory of it exists. -/
theorem completeRel_casesD {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Pre : Reader → List E → List E → Prop}
    (h : ∀ args rets Lin, (∀ rd, LowDef κ rd → MemL rd Lin → Pre rd args rets) →
      ∀ rd1, LowDef κ rd1 → MemL rd1 Lin → CompleteAtD fs cert κ f Lin args (Returns rets)) :
    CompleteRelD fs cert κ f Pre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    exact h args rets Lin hpre rd1 hl1 hL1 fp
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL

theorem completeRel_casesB {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Pre : Reader → List E → List E → Prop} {B : List E → ℕ}
    (h : ∀ args rets Lin, (∀ rd, LowDef κ rd → MemL rd Lin → Pre rd args rets) →
      ∀ rd1, LowDef κ rd1 → MemL rd1 Lin → CompleteAtB fs cert κ f Lin args (Returns rets) (B args)) :
    ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → Pre rd args rets) →
      CompleteAtB fs cert κ f Lin args (Returns rets) (B args) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    exact h args rets Lin hpre rd1 hl1 hL1 fp
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL

/-! ## `statement_digest` -/

/-- `statement_digest`'s precondition at the signers' digest `sig` and the deferred cells. -/
def SdPreAt (sig : Digest) (cells : List E) (rd : Reader) : List E → List E → Prop
  | [seed0, seed1, sigp, da0, da1, dp], [d0, d1] => ∃ seed da : Digest, cells.length = deferStmtCells ∧
      (seed0, seed1) = digestScalars seed ∧ LoadHolds rd sigp 0 (digestScalars sig).1 ∧
      LoadHolds rd sigp 1 (digestScalars sig).2 ∧ (da0, da1) = digestScalars da ∧ CellsAt rd dp cells ∧
      (d0, d1) = digestScalars (stmtDigestOf seed sig da cells)
  | _, _ => False

theorem sdPreAt_shape {sig : Digest} {cells : List E} {rd : Reader} {args rets : List E}
    (h : SdPreAt sig cells rd args rets) :
    ∃ seed0 seed1 sigp da0 da1 dp d0 d1, args = [seed0, seed1, sigp, da0, da1, dp] ∧ rets = [d0, d1] := by
  unfold SdPreAt at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩
  · exact h.elim

theorem pure_single {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hb : Stmt.pureList [f] fn.body = true) : coreProgram.PureIn [f] := by
  intro g hg fn' hf'
  rw [List.mem_singleton] at hg
  subst hg
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  exact hb

set_option maxRecDepth 100000 in
theorem sd_pure : coreProgram.PureIn ["statement_digest"] := pure_single find_statement_digest (by decide +kernel)

/-- **`statement_digest` is complete, uniformly placed**, at pinned reads. -/
theorem sd_completeRelAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (sig : Digest) (cells : List E) :
    CompleteRel fs cert κ "statement_digest" (SdPreAt sig cells) := by
  refine completeRel_cases fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨seed0, seed1, sigp, da0, da1, dp, d0, d1, rfl, rfl⟩ := sdPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨seed, da, hlen, hs, -, -, hda, -, hd⟩ := hpre rd1 hl1 hL1
  have g0 := fun rd (hL : MemL rd Lin) =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.1) hl1 hL1 hL
  have g1 := fun rd (hL : MemL rd Lin) =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.2.1) hl1 hL1 hL
  have gc : ∀ k (hk : k < cells.length) rd, MemL rd Lin → LoadHolds rd dp k cells[k] := fun k hk _ hL =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.2.2.2.1 k hk) hl1 hL1 hL
  exact LeanVM.Guest.B1.completeAt_of_rel_pure sd_pure (List.mem_singleton_self _) (fun rd hL =>
    (statement_digest_iff rd _ _).mpr ⟨_, _, _, _, _, _, _, _, rfl, rfl, seed, sig, da, cells, hlen, hs,
      g0 rd hL, g1 rd hL, hda, fun k hk => gc k hk rd hL, hd⟩) κ

/-- **`statement_digest` is complete, uniformly placed**, at pinned reads. -/
theorem sd_completeRelAtD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (sig : Digest) (cells : List E) :
    CompleteRelD fs cert κ "statement_digest" (SdPreAt sig cells) := by
  refine completeRel_casesD fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨seed0, seed1, sigp, da0, da1, dp, d0, d1, rfl, rfl⟩ := sdPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨seed, da, hlen, hs, -, -, hda, -, hd⟩ := hpre rd1 hl1 hL1
  have g0 := fun rd (hL : MemL rd Lin) =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.1) hl1 hL1 hL
  have g1 := fun rd (hL : MemL rd Lin) =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.2.1) hl1 hL1 hL
  have gc : ∀ k (hk : k < cells.length) rd, MemL rd Lin → LoadHolds rd dp k cells[k] := fun k hk _ hL =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.2.2.2.1 k hk) hl1 hL1 hL
  exact LeanVM.Guest.B1.completeAt_of_rel_pureD sd_pure (List.mem_singleton_self _) (fun rd hL =>
    (statement_digest_iff rd _ _).mpr ⟨_, _, _, _, _, _, _, _, rfl, rfl, seed, sig, da, cells, hlen, hs,
      g0 rd hL, g1 rd hL, hda, fun k hk => gc k hk rd hL, hd⟩) κ

/-- **`statement_digest` is complete, uniformly placed**, at pinned reads. -/
theorem sd_completeRelAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (sig : Digest) (cells : List E) (B : List E → ℕ) (hB : TotalLe coreProgram fs "statement_digest" B) :
    ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → SdPreAt sig cells rd args rets) →
      CompleteAtB fs cert κ "statement_digest" Lin args (Returns rets) (B args) := by
  refine completeRel_casesB fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨seed0, seed1, sigp, da0, da1, dp, d0, d1, rfl, rfl⟩ := sdPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨seed, da, hlen, hs, -, -, hda, -, hd⟩ := hpre rd1 hl1 hL1
  have g0 := fun rd (hL : MemL rd Lin) =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.1) hl1 hL1 hL
  have g1 := fun rd (hL : MemL rd Lin) =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.2.1) hl1 hL1 hL
  have gc : ∀ k (hk : k < cells.length) rd, MemL rd Lin → LoadHolds rd dp k cells[k] := fun k hk _ hL =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.2.2.2.1 k hk) hl1 hL1 hL
  exact LeanVM.Guest.B1.completeAt_of_rel_pureB sd_pure (List.mem_singleton_self _) (fun rd hL =>
    (statement_digest_iff rd _ _).mpr ⟨_, _, _, _, _, _, _, _, rfl, rfl, seed, sig, da, cells, hlen, hs,
      g0 rd hL, g1 rd hL, hda, fun k hk => gc k hk rd hL, hd⟩) κ hB

/-! ## `da_list_digest` -/

/-- `da_list_digest`'s precondition at the claims. -/
def DaListPreAt (claims : List DaClaim) (rd : Reader) : List E → List E → Prop
  | [roots, ng], [d0, d1] => claims.length ≤ 16 ∧ ng = gen ^ claims.length ∧ DaClaimsAt rd roots claims ∧
      (d0, d1) = digestScalars (daListDigest claims)
  | _, _ => False

theorem daListPreAt_shape {claims : List DaClaim} {rd : Reader} {args rets : List E}
    (h : DaListPreAt claims rd args rets) : ∃ roots ng d0 d1, args = [roots, ng] ∧ rets = [d0, d1] := by
  unfold DaListPreAt at h
  split at h
  · exact ⟨_, _, _, _, rfl, rfl⟩
  · exact h.elim

set_option maxRecDepth 100000 in
theorem dl_pure : coreProgram.PureIn ("da_list_digest" :: hrNames) := by
  intro g hg fn hf
  rcases List.mem_cons.mp hg with rfl | hg
  · rw [find_da_list_digest, Option.some.injEq] at hf; subst hf; decide +kernel
  · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hg
    have hn' : n ≤ 16 := by simp [hrNames] at hn; omega
    rw [← List.getD_eq_getElem _ "" hn, find_da_hash_roots n hn', Option.some.injEq] at hf
    subst hf
    interval_cases n <;> decide +kernel

/-- **`da_list_digest` is complete, uniformly placed**, at pinned claims. -/
theorem dl_completeRelAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (claims : List DaClaim) :
    CompleteRel fs cert κ "da_list_digest" (DaListPreAt claims) := by
  refine completeRel_cases fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨roots, ng, d0, d1, rfl, rfl⟩ := daListPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨hlen, hng, -, hd⟩ := hpre rd1 hl1 hL1
  have g : ∀ i (h : i < claims.length) rd, MemL rd Lin → (LoadHolds rd roots (4 * i) (digestScalars claims[i].1).1 ∧
      LoadHolds rd roots (4 * i + 1) (digestScalars claims[i].1).2 ∧
      LoadHolds rd roots (4 * i + 2) (digestScalars claims[i].2).1 ∧
      LoadHolds rd roots (4 * i + 3) (digestScalars claims[i].2).2) := fun i h rd hL =>
    ⟨forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.2.1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.2.2) hl1 hL1 hL⟩
  exact LeanVM.Guest.B1.completeAt_of_rel_pure dl_pure (List.mem_cons_self) (fun rd hL =>
    (da_list_digest_iff rd _ _).mpr ⟨_, _, _, _, rfl, rfl, claims, hlen, hng, fun i h => g i h rd hL, hd⟩) κ

/-- **`da_list_digest` is complete, uniformly placed**, at pinned claims. -/
theorem dl_completeRelAtD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (claims : List DaClaim) :
    CompleteRelD fs cert κ "da_list_digest" (DaListPreAt claims) := by
  refine completeRel_casesD fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨roots, ng, d0, d1, rfl, rfl⟩ := daListPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨hlen, hng, -, hd⟩ := hpre rd1 hl1 hL1
  have g : ∀ i (h : i < claims.length) rd, MemL rd Lin → (LoadHolds rd roots (4 * i) (digestScalars claims[i].1).1 ∧
      LoadHolds rd roots (4 * i + 1) (digestScalars claims[i].1).2 ∧
      LoadHolds rd roots (4 * i + 2) (digestScalars claims[i].2).1 ∧
      LoadHolds rd roots (4 * i + 3) (digestScalars claims[i].2).2) := fun i h rd hL =>
    ⟨forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.2.1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.2.2) hl1 hL1 hL⟩
  exact LeanVM.Guest.B1.completeAt_of_rel_pureD dl_pure (List.mem_cons_self) (fun rd hL =>
    (da_list_digest_iff rd _ _).mpr ⟨_, _, _, _, rfl, rfl, claims, hlen, hng, fun i h => g i h rd hL, hd⟩) κ

/-- **`da_list_digest` is complete, uniformly placed**, at pinned claims. -/
theorem dl_completeRelAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (claims : List DaClaim) (B : List E → ℕ) (hB : TotalLe coreProgram fs "da_list_digest" B) :
    ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → DaListPreAt claims rd args rets) →
      CompleteAtB fs cert κ "da_list_digest" Lin args (Returns rets) (B args) := by
  refine completeRel_casesB fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨roots, ng, d0, d1, rfl, rfl⟩ := daListPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨hlen, hng, -, hd⟩ := hpre rd1 hl1 hL1
  have g : ∀ i (h : i < claims.length) rd, MemL rd Lin → (LoadHolds rd roots (4 * i) (digestScalars claims[i].1).1 ∧
      LoadHolds rd roots (4 * i + 1) (digestScalars claims[i].1).2 ∧
      LoadHolds rd roots (4 * i + 2) (digestScalars claims[i].2).1 ∧
      LoadHolds rd roots (4 * i + 3) (digestScalars claims[i].2).2) := fun i h rd hL =>
    ⟨forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.2.1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.2.2) hl1 hL1 hL⟩
  exact LeanVM.Guest.B1.completeAt_of_rel_pureB dl_pure (List.mem_cons_self) (fun rd hL =>
    (da_list_digest_iff rd _ _).mpr ⟨_, _, _, _, rfl, rfl, claims, hlen, hng, fun i h => g i h rd hL, hd⟩) κ hB

/-! ## `cover_da_root` -/

/-- `cover_da_root`'s precondition at the slot `i`. -/
def CoverPreAt (i : ℕ) (rd : Reader) : List E → List E → Prop
  | [roots, cover, nslots, mark], [r0, r1, r2, r3] => ∃ M, M ≤ 2 ^ 16 ∧ i < M ∧ nslots = gen ^ M ∧
      LoadHolds rd (cover * gen ^ i) 0 mark ∧ CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3]
  | _, _ => False

theorem coverPreAt_shape {i : ℕ} {rd : Reader} {args rets : List E} (h : CoverPreAt i rd args rets) :
    ∃ roots cover nslots mark r0 r1 r2 r3, args = [roots, cover, nslots, mark] ∧ rets = [r0, r1, r2, r3] := by
  unfold CoverPreAt at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩
  · exact h.elim

def coverAtoms : List Atom :=
  [.hint (.witness "da_index" (.stack [.n 4])), .const (.n 5) (word 9223372036854775821 0 0),
   .mul (.n 6) (.n 2) (.n 5), .rangeCheck (.n 4) (.n 7) (.n 8) (.n 9) (.n 6), .mul (.n 10) (.n 1) (.n 4),
   .load (.n 3) (.n 10) 0, .mul (.n 11) (.n 4) (.n 4), .mul (.n 12) (.n 11) (.n 11), .mul (.n 13) (.n 0) (.n 12),
   .load (.n 14) (.n 13) 0, .load (.n 15) (.n 13) 1, .load (.n 16) (.n 13) 2, .load (.n 17) (.n 13) 3]

theorem coverBody_eq : coverBody = coverAtoms.map .atom ++ [.ret [.n 14, .n 15, .n 16, .n 17]] := rfl

/-- **`cover_da_root` is complete, uniformly placed**, at the slot `i`, on a memory defined below
`2^κ`, `κ ≥ 16`. -/
theorem cover_completeRelAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (i : ℕ) :
    CompleteRel fs cert κ "cover_da_root" (CoverPreAt i) := by
  refine completeRel_cases fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨roots, cover, nslots, mark, r0, r1, r2, r3, rfl, rfl⟩ := coverPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨M, hM, hi, rfl, -, -⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      LoadHolds rd (cover * gen ^ i) 0 mark ∧ CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3] := by
    intro rd hl hL
    obtain ⟨M', -, -, -, h1, h2⟩ := hpre rd hl hL
    exact ⟨h1, h2⟩
  obtain ⟨im, him, hRm⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1) hl1 hL1
  have hFc : ∀ r, ∃ ic, r < 4 → (roots * gen ^ (4 * i)).limb 0 * gpow r = gpow ic ∧ RegionL Lin ic := by
    intro r
    by_cases hr : r < 4
    · obtain ⟨ic, h⟩ := forced_load (p := roots * gen ^ (4 * i)) (k := r) (v := [r0, r1, r2, r3][r]'(by simp; omega))
        (fun rd hl hL => (hpre' rd hl hL).2 r (by simp; omega)) hl1 hL1
      exact ⟨ic, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose cidx hcidx using hFc
  refine LeanVM.Guest.B1.completeAt_leaf find_cover_da_root (by
      rw [Program.loop_of_find? find_cover_da_root]; decide +kernel) κ Lin _ _ [] (fun _ => [])
    (fun _ => List.Forall₂.nil) (fun fp rd hl _ hL => ?_)
  obtain ⟨hmark, hroot⟩ := hpre' rd hl hL
  obtain ⟨t1, t2, l1, hk, l2⟩ := rangeCheck_complete_low (fun j hj => hl j (lt_of_lt_of_le hj
    (Nat.pow_le_pow_right (by norm_num) hκ))) (e := i) (e' := M - 1 - i) (by omega) (by omega)
  rw [cellsAt_four] at hroot
  have hk' : gen ^ M * word 9223372036854775821 0 0 = gen ^ i * gen ^ (M - 1 - i) := by
    rw [← hk, show i + (M - 1 - i) = M - 1 by omega,
      show gen ^ M = gen ^ (M - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc,
      mul_comm gen, ginv_mul_gen, mul_one]
  set σ := listVal [roots, cover, gen ^ M, mark, gen ^ i, word 9223372036854775821 0 0,
    gen ^ M * word 9223372036854775821 0 0, gen ^ (M - 1 - i), t1, t2, cover * gen ^ i,
    gen ^ i * gen ^ i, gen ^ i * gen ^ i * (gen ^ i * gen ^ i),
    roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)), r0, r1, r2, r3] with hσ
  have hroot' := hroot
  rw [pow_mul', ← gen_pow_four_mul] at hroot'
  have hH : ∀ a ∈ coverAtoms, a.Holds rd σ := by
    simp only [coverAtoms, List.forall_mem_cons, forall_mem_nil_iff, Atom.Holds, hσ, listVal,
      List.getD_cons_succ, List.getD_cons_zero, true_and, and_true]
    exact ⟨⟨l1, hk', l2⟩, hmark, hroot'.1, hroot'.2.1, hroot'.2.2.1, hroot'.2.2.2⟩
  refine ⟨σ, _, [.n 14, .n 15, .n 16, .n 17], rfl, by rw [coverBody_eq]; exact walk_atoms _ _ _, rfl,
    fun e he => ?_, calls_atoms _, by rw [addrs_atoms]; rfl, allocs_atoms _ (by decide),
    by rw [allocDsts_atoms (by decide)]; rfl, fun A hA => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact hH a ha
  · rw [loadAddrs_atoms, show coverAtoms.filterMap atomLoad? = [(.n 10, 0), (.n 13, 0), (.n 13, 1), (.n 13, 2),
      (.n 13, 3)] from rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g13 : σ (.n 13) = roots * gen ^ (4 * i) := by
      show roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)) = _
      rw [pow4_eq _ _ rfl]
    rcases hA with rfl | rfl | rfl | rfl | rfl
    · exact ⟨im, him, Or.inr hRm⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 0 (by omega)).1, Or.inr (hcidx 0 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 1 (by omega)).1, Or.inr (hcidx 1 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 2 (by omega)).1, Or.inr (hcidx 2 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 3 (by omega)).1, Or.inr (hcidx 3 (by omega)).2⟩

/-- **`cover_da_root` is complete, uniformly placed**, at the slot `i`, on a memory defined below
`2^κ`, `κ ≥ 16`. -/
theorem cover_completeRelAtD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (i : ℕ) :
    CompleteRelD fs cert κ "cover_da_root" (CoverPreAt i) := by
  refine completeRel_casesD fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨roots, cover, nslots, mark, r0, r1, r2, r3, rfl, rfl⟩ := coverPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨M, hM, hi, rfl, -, -⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      LoadHolds rd (cover * gen ^ i) 0 mark ∧ CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3] := by
    intro rd hl hL
    obtain ⟨M', -, -, -, h1, h2⟩ := hpre rd hl hL
    exact ⟨h1, h2⟩
  obtain ⟨im, him, hRm⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1) hl1 hL1
  have hFc : ∀ r, ∃ ic, r < 4 → (roots * gen ^ (4 * i)).limb 0 * gpow r = gpow ic ∧ RegionL Lin ic := by
    intro r
    by_cases hr : r < 4
    · obtain ⟨ic, h⟩ := forced_load (p := roots * gen ^ (4 * i)) (k := r) (v := [r0, r1, r2, r3][r]'(by simp; omega))
        (fun rd hl hL => (hpre' rd hl hL).2 r (by simp; omega)) hl1 hL1
      exact ⟨ic, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose cidx hcidx using hFc
  refine LeanVM.Guest.B1.completeAt_leafD find_cover_da_root (by
      rw [Program.loop_of_find? find_cover_da_root]; decide +kernel) κ Lin _ _ [] (fun _ => [])
    (fun _ => List.Forall₂.nil) (fun fp rd hl _ hL => ?_)
  obtain ⟨hmark, hroot⟩ := hpre' rd hl hL
  obtain ⟨t1, t2, l1, hk, l2⟩ := rangeCheck_complete_low (fun j hj => hl j (lt_of_lt_of_le hj
    (Nat.pow_le_pow_right (by norm_num) hκ))) (e := i) (e' := M - 1 - i) (by omega) (by omega)
  rw [cellsAt_four] at hroot
  have hk' : gen ^ M * word 9223372036854775821 0 0 = gen ^ i * gen ^ (M - 1 - i) := by
    rw [← hk, show i + (M - 1 - i) = M - 1 by omega,
      show gen ^ M = gen ^ (M - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc,
      mul_comm gen, ginv_mul_gen, mul_one]
  set σ := listVal [roots, cover, gen ^ M, mark, gen ^ i, word 9223372036854775821 0 0,
    gen ^ M * word 9223372036854775821 0 0, gen ^ (M - 1 - i), t1, t2, cover * gen ^ i,
    gen ^ i * gen ^ i, gen ^ i * gen ^ i * (gen ^ i * gen ^ i),
    roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)), r0, r1, r2, r3] with hσ
  have hroot' := hroot
  rw [pow_mul', ← gen_pow_four_mul] at hroot'
  have hH : ∀ a ∈ coverAtoms, a.Holds rd σ := by
    simp only [coverAtoms, List.forall_mem_cons, forall_mem_nil_iff, Atom.Holds, hσ, listVal,
      List.getD_cons_succ, List.getD_cons_zero, true_and, and_true]
    exact ⟨⟨l1, hk', l2⟩, hmark, hroot'.1, hroot'.2.1, hroot'.2.2.1, hroot'.2.2.2⟩
  refine ⟨σ, _, [.n 14, .n 15, .n 16, .n 17], rfl, by rw [coverBody_eq]; exact walk_atoms _ _ _, rfl,
    fun e he => ?_, calls_atoms _, by rw [addrs_atoms]; rfl, allocs_atoms _ (by decide),
    by rw [allocDsts_atoms (by decide)]; rfl, fun A hA => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact hH a ha
  · rw [loadAddrs_atoms, show coverAtoms.filterMap atomLoad? = [(.n 10, 0), (.n 13, 0), (.n 13, 1), (.n 13, 2),
      (.n 13, 3)] from rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g13 : σ (.n 13) = roots * gen ^ (4 * i) := by
      show roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)) = _
      rw [pow4_eq _ _ rfl]
    rcases hA with rfl | rfl | rfl | rfl | rfl
    · exact ⟨im, him, Or.inr hRm⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 0 (by omega)).1, Or.inr (hcidx 0 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 1 (by omega)).1, Or.inr (hcidx 1 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 2 (by omega)).1, Or.inr (hcidx 2 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 3 (by omega)).1, Or.inr (hcidx 3 (by omega)).2⟩

/-- **`cover_da_root` is complete, uniformly placed**, at the slot `i`, on a memory defined below
`2^κ`, `κ ≥ 16`. -/
theorem cover_completeRelAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (i : ℕ) :
    ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → CoverPreAt i rd args rets) →
      CompleteAtB fs cert κ "cover_da_root" Lin args (Returns rets) (fs "cover_da_root") := by
  refine completeRel_casesB fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨roots, cover, nslots, mark, r0, r1, r2, r3, rfl, rfl⟩ := coverPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨M, hM, hi, rfl, -, -⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      LoadHolds rd (cover * gen ^ i) 0 mark ∧ CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3] := by
    intro rd hl hL
    obtain ⟨M', -, -, -, h1, h2⟩ := hpre rd hl hL
    exact ⟨h1, h2⟩
  obtain ⟨im, him, hRm⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1) hl1 hL1
  have hFc : ∀ r, ∃ ic, r < 4 → (roots * gen ^ (4 * i)).limb 0 * gpow r = gpow ic ∧ RegionL Lin ic := by
    intro r
    by_cases hr : r < 4
    · obtain ⟨ic, h⟩ := forced_load (p := roots * gen ^ (4 * i)) (k := r) (v := [r0, r1, r2, r3][r]'(by simp; omega))
        (fun rd hl hL => (hpre' rd hl hL).2 r (by simp; omega)) hl1 hL1
      exact ⟨ic, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose cidx hcidx using hFc
  refine LeanVM.Guest.B1.completeAt_leafB find_cover_da_root (by
      rw [Program.loop_of_find? find_cover_da_root]; decide +kernel) κ Lin _ _ [] (fun _ => [])
    (fun _ => List.Forall₂.nil) (fun fp rd hl _ hL => ?_)
  obtain ⟨hmark, hroot⟩ := hpre' rd hl hL
  obtain ⟨t1, t2, l1, hk, l2⟩ := rangeCheck_complete_low (fun j hj => hl j (lt_of_lt_of_le hj
    (Nat.pow_le_pow_right (by norm_num) hκ))) (e := i) (e' := M - 1 - i) (by omega) (by omega)
  rw [cellsAt_four] at hroot
  have hk' : gen ^ M * word 9223372036854775821 0 0 = gen ^ i * gen ^ (M - 1 - i) := by
    rw [← hk, show i + (M - 1 - i) = M - 1 by omega,
      show gen ^ M = gen ^ (M - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc,
      mul_comm gen, ginv_mul_gen, mul_one]
  set σ := listVal [roots, cover, gen ^ M, mark, gen ^ i, word 9223372036854775821 0 0,
    gen ^ M * word 9223372036854775821 0 0, gen ^ (M - 1 - i), t1, t2, cover * gen ^ i,
    gen ^ i * gen ^ i, gen ^ i * gen ^ i * (gen ^ i * gen ^ i),
    roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)), r0, r1, r2, r3] with hσ
  have hroot' := hroot
  rw [pow_mul', ← gen_pow_four_mul] at hroot'
  have hH : ∀ a ∈ coverAtoms, a.Holds rd σ := by
    simp only [coverAtoms, List.forall_mem_cons, forall_mem_nil_iff, Atom.Holds, hσ, listVal,
      List.getD_cons_succ, List.getD_cons_zero, true_and, and_true]
    exact ⟨⟨l1, hk', l2⟩, hmark, hroot'.1, hroot'.2.1, hroot'.2.2.1, hroot'.2.2.2⟩
  refine ⟨σ, _, [.n 14, .n 15, .n 16, .n 17], rfl, by rw [coverBody_eq]; exact walk_atoms _ _ _, rfl,
    fun e he => ?_, calls_atoms _, by rw [addrs_atoms]; rfl, allocs_atoms _ (by decide),
    by rw [allocDsts_atoms (by decide)]; rfl, fun A hA => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact hH a ha
  · rw [loadAddrs_atoms, show coverAtoms.filterMap atomLoad? = [(.n 10, 0), (.n 13, 0), (.n 13, 1), (.n 13, 2),
      (.n 13, 3)] from rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g13 : σ (.n 13) = roots * gen ^ (4 * i) := by
      show roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)) = _
      rw [pow4_eq _ _ rfl]
    rcases hA with rfl | rfl | rfl | rfl | rfl
    · exact ⟨im, him, Or.inr hRm⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 0 (by omega)).1, Or.inr (hcidx 0 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 1 (by omega)).1, Or.inr (hcidx 1 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 2 (by omega)).1, Or.inr (hcidx 2 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 3 (by omega)).1, Or.inr (hcidx 3 (by omega)).2⟩

end
end LeanVM.Guest.B1.Digest
