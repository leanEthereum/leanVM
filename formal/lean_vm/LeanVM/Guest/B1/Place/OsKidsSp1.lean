/-
  LeanVM.Guest.B1.Place.OsKidsSp1

  open_stacked's residual loops, placed on the honest trace; a callee's words widened.
-/

module

public import LeanVM.Guest.B1.Place.OsLkMem6
public import LeanVM.Guest.B1.Place.ResAt
public import LeanVM.Guest.B1.Whir.BrFin2
public import LeanVM.Guest.Memory.Size

/-!
# The residual loops, placed

* `completeAtD_lin_mono`: a callee complete on the words `Lin` is complete on any layout
  containing them.
* `osLk_fixed`: a memory holding `osLk` holds the fixed buffers' honest words (`FixedMem`).
* `qpos_all`: every decoded position, by level.
* `os_res_mem`: a memory holding `osLk` holds level `l`'s row words and every iteration's meaning
  (eight positions, the chain `finChain` before and after, `μ = λ⁻¹`).
* **`os_res_completeAtD`**: level `l`'s residual loop (`c.resLoop l`), at its honest arguments
  (`ResCallOk`'s, the pointers `osAtOf c b`), is `CompleteAtD` on `osLk c tr b Lin`;
  **`os_res_completeAtB`**: `CompleteAtB`, by a tree of at most `B` words, `B` bounding the loop's
  valid trees at those arguments (`os_res_completeAtB_of_totalLe`: from its `TotalLe`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A callee's words widened**: complete on `Lin`, complete on any layout containing it. -/
theorem completeAtD_lin_mono {κ : ℕ} {f : String} {Lin Lin' : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtD fs cert κ f Lin args Out)
    (hsub : ∀ q ∈ Lin, q ∈ Lin') : CompleteAtD fs cert κ f Lin' args Out := fun fp ↦ by
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm ↦ ?_⟩
  obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
  have h3 : MemL rd Lin := fun q hq ↦ h2 q (hsub q hq)
  exact (hr rd hl (Main.memL_append.mpr ⟨h1, h3⟩)).mono fun i ⟨q, hq, hq1, hq2⟩ ↦
    ⟨q, hsub q hq, hq1, hq2⟩

theorem osOwnL_getD_fixed (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) :
    (osOwnL c tr bp).getD 2 [] = fmsgC c tr ∧ (osOwnL c tr bp).getD 3 [] = rootsC c tr ∧
      (osOwnL c tr bp).getD 4 [] = fchC c tr ∧ (osOwnL c tr bp).getD 5 [] = betasC c tr ∧
      (osOwnL c tr bp).getD 10 [] = oodzC c tr ∧ (osOwnL c tr bp).getD 11 [] = oodC c tr := by
  rw [osOwnL_eq6]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The fixed buffers' honest words** on every memory holding `osLk`. -/
theorem osLk_fixed {c : OsCfg} {tr : OsTr} {b : ℕ} {Lin : Layout} {rd : Reader}
    (hm : MemL rd (osLk c tr b Lin)) : FixedMem rd (osAtOf c b).P c tr := by
  have r : ∀ j, j < 12 → j ≠ 8 → ReadsAt rd (osPtrAt c b j) ((osOwnL c tr fun _ _ ↦ 0).getD j []) :=
    fun j hj h8 ↦ osLk_reads hm _ (by omega) h8
  obtain ⟨g2, g3, g4, g5, g10, g11⟩ := osOwnL_getD_fixed c tr fun _ _ ↦ 0
  obtain ⟨-, -, g6, g7, -, g9⟩ := osOwnL_getD_head6 c tr fun _ _ ↦ 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := r 4 (by omega) (by omega); rwa [g4] at this
  · have := r 3 (by omega) (by omega); rwa [g3] at this
  · have := r 5 (by omega) (by omega); rwa [g5] at this
  · have := r 6 (by omega) (by omega); rwa [g6] at this
  · have := r 9 (by omega) (by omega); rwa [g9] at this
  · have := r 7 (by omega) (by omega); rwa [g7] at this
  · have := r 10 (by omega) (by omega); rwa [g10] at this
  · have := r 11 (by omega) (by omega); rwa [g11] at this
  · have := r 2 (by omega) (by omega); rwa [g2] at this

section Honest

variable {c : OsCfg} {tr : OsTr}

/-- **Every decoded position of level `i`.** -/
theorem qpos_all (hs : OsSizes c) {rd : Reader} {P : OsPtrs}
    (hm : FixedMem rd P c tr) {i : ℕ} (hi : i < c.levels.length) {j : ℕ}
    (hj : j < (lvAt c i).squeezes * (192 / (lvAt c i).depth)) :
    LoadHolds rd P.qpos ((lvAt c i).posOff + j) (posAt c tr i j) := by
  have hpos := hs.pos
  have hend := off_end (off := fun i ↦ (lvAt c i).posOff)
    (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (c.levels.length - 1 - i) i
    (by omega)
  have hown : ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length ((lvAt c i).posOff + j) = i := by
    have := ownerOf_eq (off := fun i ↦ (lvAt c i).posOff)
      (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (i := i)
      (k := (lvAt c i).posOff + j) (by omega) (by
      show (lvAt c i).posOff + j < (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth)
      omega) (c.levels.length - 1 - i) (by omega)
    rwa [show i + 1 + (c.levels.length - 1 - i) = c.levels.length by omega] at this
  have := readsAt_map_range hm.qpos (k := (lvAt c i).posOff + j) (by
    show (lvAt c i).posOff + j < c.posLen
    have : (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth) ≤ c.posLen := hend
    omega)
  simp only [hown, Nat.add_sub_cancel_left, hj, ↓reduceIte] at this
  exact this

theorem loadHolds_x8 {rd : Reader} {p : E} {po j k : ℕ} {w : E} :
    LoadHolds rd (p * gen ^ po * (gen ^ j) ^ resBatch) k w ↔
      LoadHolds rd p (po + (resBatch * j + k)) w := by
  rw [← pow_mul, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow, Nat.mul_comm j resBatch]

theorem loadHolds_x1 {rd : Reader} {p : E} {j k : ℕ} {w : E} :
    LoadHolds rd (p * gen ^ j) k w ↔ LoadHolds rd p (j + k) w := loadHolds_mul_gen_pow _ _ _ _ _

theorem finChain_succ (c : OsCfg) (tr : OsTr) (i m : ℕ) :
    finChain c tr i (m + 1) = resFold (finD c tr i) (lvAt c i).vanish (lvAt c i).logCols (finM tr i)
      (finChain c tr i m) ((List.range resBatch).map fun t ↦ Pof tr.rs i (resBatch * m + t)) := by
  unfold finChain
  rw [← resFold_append, show resBatch * (m + 1) = resBatch * m + resBatch by ring, List.range_add,
    List.map_append, List.map_map]
  rfl

/-- **Level `l`'s residual loop's memory**: every memory holding `osLk` holds the row's `d` words
and every iteration's meaning: the batch's eight positions, `chain[j]` and `chain[j + 1]`. -/
theorem os_res_mem (h : TrFit c tr) (hs : OsSizes c) {l : ℕ} (hl : l < c.levels.length) (b : ℕ)
    (Lin : Layout) : ∀ rd, MemL rd (osLk c tr b Lin) →
      (∀ s < (lvAt c l).logCols,
        LoadHolds rd (osAtOf c b).BD (l * ligColsCap + s) (finD c tr l s)) ∧
      ∀ j < (lvAt c l).queries / resBatch, ResIter rd (finD c tr l) (lvAt c l).vanish
        (lvAt c l).logCols (lvAt c l).posOff (osAtOf c b).P.qpos ((osAtOf c b).rc l) (finM tr l)
        (gen ^ j) := by
  refine fun rd hm ↦ ⟨fun s hs' ↦ ?_, fun j hj ↦ ?_⟩
  · -- the row's `d` words
    obtain ⟨hBD, -⟩ := osOwnL_getD_fin6 c tr (fun _ _ ↦ 0) hl
    have hr := osLk_reads hm (fun _ _ ↦ 0) (j := osIxBD c) (by unfold osIxBD; omega)
      (by unfold osIxBD; omega)
    rw [hBD] at hr
    have hc : (lvAt c l).logCols ≤ 22 := hs.cols l hl
    have := readsAt_map_range hr (k := l * ligColsCap + s) (by simp only [ligColsCap]; nlinarith)
    simp only [ligColsCap] at this
    simp only [show (l * 22 + s) / 22 = l by omega, show (l * 22 + s) % 22 = s by omega] at this
    exact this
  · -- iteration `j`
    have hfix := osLk_fixed hm
    obtain ⟨-, hRC⟩ := osOwnL_getD_fin6 c tr (fun _ _ ↦ 0) hl
    have hr := osLk_reads hm (fun _ _ ↦ 0) (j := osIxRC c l) (by unfold osIxRC; omega)
      (by unfold osIxRC; omega)
    rw [hRC] at hr
    have hrc : ∀ m ≤ (lvAt c l).queries / resBatch, LoadHolds rd ((osAtOf c b).rc l) m
        (finChain c tr l m) := fun m hm' ↦ readsAt_map_range hr (k := m) (by omega)
    have hq : resBatch * ((lvAt c l).queries / resBatch) ≤ (lvAt c l).queries :=
      Nat.mul_div_le _ _
    refine ⟨finChain c tr l j, (List.range resBatch).map fun t ↦ Pof tr.rs l (resBatch * j + t),
      by simp, fun t ht ↦ ?_, ?_, ?_⟩
    · rw [loadHolds_x8]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
        Option.map_some, Option.getD_some]
      exact qpos_get h hs hfix hl (by
        have : resBatch * (j + 1) ≤ resBatch * ((lvAt c l).queries / resBatch) :=
          Nat.mul_le_mul_left _ hj
        rw [Nat.mul_add, Nat.mul_one] at this; omega)
    · rw [loadHolds_x1, Nat.add_zero]
      exact hrc j (by omega)
    · rw [loadHolds_x1, ← finChain_succ]
      exact hrc (j + 1) (by omega)

/-- **Level `l`'s residual loop, placed**, at its honest arguments. -/
theorem os_res_completeAtD (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {μ r : ℕ}
    {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr) (hs : OsSizes c)
    {l : ℕ} (hl : l < c.levels.length) {fn : Fn} (hf : coreProgram.find? (c.resLoop l) = some fn)
    (hps : fn.params = osParams 6) (hb : fn.body = resLoopBody l (lvAt c l) (c.resLoop l))
    (hq8 : resBatch ≤ (lvAt c l).queries)
    (hne : 1 + gen ^ ((lvAt c l).queries / resBatch) ≠ 0) (b : ℕ) (Lin : Layout) :
    CompleteAtD fs cert κ (c.resLoop l) (osLk c tr b Lin)
      [1, gen ^ ((lvAt c l).queries / resBatch), (osAtOf c b).P.qpos, (osAtOf c b).BD,
        (osAtOf c b).rc l, finM tr l] (Returns []) := by
  have hst := hF.lv l hl
  exact resLoop_completeAtD fs cert κ hf l (lvAt c l) hps hb hst.ml1 hst.posOff
    (Nat.div_pos hq8 (by decide)) hne (os_res_mem h hs hl b Lin)

/-- **Level `l`'s residual loop, placed, by a bounded tree**, at its honest arguments: by a tree of
at most `B` words, `B` bounding the loop's valid trees there (`TotalLe` at the call's arguments;
`os_res_completeAtB_of_totalLe`). -/
theorem os_res_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {μ r : ℕ}
    {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr) (hs : OsSizes c)
    {l : ℕ} (hl : l < c.levels.length) {fn : Fn} (hf : coreProgram.find? (c.resLoop l) = some fn)
    (hps : fn.params = osParams 6) (hb : fn.body = resLoopBody l (lvAt c l) (c.resLoop l))
    (hq8 : resBatch ≤ (lvAt c l).queries)
    (hne : 1 + gen ^ ((lvAt c l).queries / resBatch) ≠ 0) (b : ℕ) (Lin : Layout) {B : ℕ}
    (hB : ∀ rd (t : Tree), t.name = c.resLoop l →
      t.Valid coreProgram rd [1, gen ^ ((lvAt c l).queries / resBatch), (osAtOf c b).P.qpos,
        (osAtOf c b).BD, (osAtOf c b).rc l, finM tr l] [] →
      t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtB fs cert κ (c.resLoop l) (osLk c tr b Lin)
      [1, gen ^ ((lvAt c l).queries / resBatch), (osAtOf c b).P.qpos, (osAtOf c b).BD,
        (osAtOf c b).rc l, finM tr l] (Returns []) B := by
  have hst := hF.lv l hl
  exact resLoop_completeAtB fs cert κ hf l (lvAt c l) hps hb hst.ml1 hst.posOff
    (Nat.div_pos hq8 (by decide)) hne (os_res_mem h hs hl b Lin) hB

end Honest

end
end LeanVM.Guest.B1
