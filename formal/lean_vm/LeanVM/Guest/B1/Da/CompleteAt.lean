/-
  LeanVM.Guest.B1.Da.CompleteAt

  `da_verify` complete in the uniform placed form (`CompleteRel`): its honest memory as a layout of
  its own words, and the squares-table word it loads within the caller's words.
-/

module

public import LeanVM.Guest.B1.Da.VerifyAt
public import LeanVM.Guest.B1.Uniform

/-!
# `da_verify`, uniformly placed

* `forced_load`: a load every memory holding the caller's words `Lin` (and defined below `2^κ`)
  satisfies reads a word of `Lin`: elsewhere a memory could hold another word.
* `dvLayout`: `da_verify`'s own words at `fp`, `DaMem` as a layout (`daMem_of_memL`), within its
  `dvTot` words (`dvLayout_within`) when the certificate's frame runs fit their frames.
* `da_verify_completeRel`: `CompleteRel` on `DaPre`, the squares table and a witness opening the
  returned claim.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.Node
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAt CompleteRel Within Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## Loads every memory holding a layout satisfies -/

/-- **A forced load reads the layout**: if every memory defined below `2^κ` and holding `Lin` holds
`v` at `p·g^k`, and one such memory exists, the address is a word of `Lin`. -/
theorem forced_load {κ : ℕ} {Lin : Layout} {p : E} {k : ℕ} {v : E}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin → LoadHolds rd p k v) {rd1 : Reader} (h1 : LowDef κ rd1)
    (h1' : MemL rd1 Lin) : ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i := by
  classical
  by_contra hne
  have hne' : ∀ i, p.limb 0 * gpow k = gpow i → ¬ RegionL Lin i := fun i h hr => hne ⟨i, h, hr⟩
  let rd' : Reader := Function.update rd1 (p.limb 0 * gpow k) (some (v + 1))
  have hl' : LowDef κ rd' := fun i hi => by
    by_cases h : gpow i = p.limb 0 * gpow k
    · simp only [rd', h, Function.update_self, Option.isSome_some]
    · simp only [rd', Function.update_of_ne h]; exact h1 i hi
  have hL' : MemL rd' Lin := fun q hq k' hk' => by
    have h0 := h1' q hq k' hk'
    refine ⟨h0.1, ?_⟩
    have hA : (ofK (gpow q.1)).limb 0 * gpow k' ≠ p.limb 0 * gpow k := by
      rw [Main.addr_ofK]
      exact fun h => hne' _ h.symm ⟨q, hq, by omega, by omega⟩
    simp only [rd', Function.update_of_ne hA]
    exact h0.2
  have h2 := (hall rd' hl' hL').2
  simp only [rd', Function.update_self, Option.some.injEq] at h2
  exact one_ne_zero (add_eq_left.mp h2)

/-! ## Layout entries -/

theorem cells_of_memL {rd : Reader} {L : Layout} (h : MemL rd L) {x : ℕ} {cs : List E} (hq : (x, cs) ∈ L) :
    CellsAt rd (gen ^ x) cs := by
  rw [gen_pow_eq_ofK]; exact h _ hq

theorem load_of_memL {rd : Reader} {L : Layout} (h : MemL rd L) {x : ℕ} {v : E} (hq : (x, [v]) ∈ L) :
    LoadHolds rd (gen ^ x) 0 v :=
  cells_of_memL h hq 0 (by simp)

/-- A tree's nodes from `base`, as `TreeAt` reads them. -/
def treeL (base k : ℕ) (leaf : ℕ → Digest) : Layout :=
  (List.range (k + 1)).flatMap fun l => (List.range (2 ^ (k - l))).map fun j =>
    (base + (lvOff k l + 2 * j), [(digestScalars (nodeD leaf l j)).1, (digestScalars (nodeD leaf l j)).2])

theorem treeAt_of_memL {rd : Reader} {L : Layout} (h : MemL rd L) {base k : ℕ} {leaf : ℕ → Digest}
    (hs : ∀ q ∈ treeL base k leaf, q ∈ L) : TreeAt rd (gen ^ base) k leaf := fun l hl j hj => by
  rw [← pow_add]
  exact cells_of_memL h (hs _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩))

theorem lvOff_add {k l j : ℕ} (hl : l ≤ k) (hj : j < 2 ^ (k - l)) : lvOff k l + 2 * j + 2 ≤ 4 * 2 ^ k := by
  have : 2 ^ (k - l) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold lvOff; omega

theorem treeL_within {base k : ℕ} {leaf : ℕ → Digest} :
    ∀ q ∈ treeL base k leaf, base ≤ q.1 ∧ q.1 + q.2.length ≤ base + 4 * 2 ^ k := by
  intro q hq
  obtain ⟨l, hl, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  have := lvOff_add (Nat.lt_succ_iff.mp (List.mem_range.mp hl)) (List.mem_range.mp hj)
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## `da_verify`'s own words -/

section Layout
variable (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness) (fp : ℕ)

/-- The exponents of `dvPtrs`' buffers and runs. -/
def dvDx : ℕ := fp + fs "da_verify"
def dvPx : ℕ := dvDx fs fp + 128 * LeanDa.nPad w.rows.length
def dvHx : ℕ := dvPx fs w fp + w.rows.length
def dvAx : ℕ := dvHx fs w fp + 258
def dvBx : ℕ := dvAx fs w fp + 129 * w.rows.length
def dvTx : ℕ := dvBx fs w fp + w.rows.length
def dvWx : ℕ := dvTx fs w fp + 512
def dvCx : ℕ := fp + cert "da_verify" (.n 20)
def dvNode (b : ℕ) : ℕ :=
  dvColPos fs fp w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) b +
    fs (colName (decide (b < 64)))
def dvLv (b : ℕ) : ℕ :=
  dvNode fs w fp b + 4 * LeanDa.nPad w.rows.length + fs "da_vector_dispatch" +
    cert (vxName (decide (b = 127))) (.n 4)

/-- **`da_verify`'s honest words at `fp`**: `DaMem` at `dvPtrs`, entry by entry. -/
def dvLayout : Layout :=
  let r := w.rows.length
  let lp := LeanDa.logPad r
  (List.range r).map (fun i => (dvPx fs w fp + i, [gen ^ dvDx fs fp * gen ^ (128 * i)])) ++
  (List.range r).flatMap (fun i => (List.range 64).map fun b => (dvDx fs fp + (128 * i + 2 * b),
    [(digestScalars (cellDOf (daSym w) b i)).1, (digestScalars (cellDOf (daSym w) b i)).2])) ++
  (List.range 129).map (fun b => (dvHx fs w fp + 2 * b, [(digestScalars (daS w b)).1, (digestScalars (daS w b)).2])) ++
  [(dvCx cert fp, (List.range 385).map fun k => word (k * 2048) 0 0)] ++
  (List.range r).map (fun i => (dvBx fs w fp + i, [gen ^ dvAx fs w fp * gen ^ (129 * i)])) ++
  (List.range r).map (fun i => (dvAx fs w fp + 129 * i, (List.range 129).map (daA w i))) ++
  treeL (dvTx fs w fp) 7 (fun b => nodeD (colLeafOf r (daSym w) b) lp 0) ++
  treeL (dvWx fs w fp) lp (rowLeafOf r (daSym w)) ++
  (List.range 128).flatMap (fun b => treeL (dvNode fs w fp b) lp (colLeafOf r (daSym w) b)) ++
  (List.range 128).map (fun b => (dvLv fs cert w fp b, daWs w b))

end Layout

theorem dvPtrs_eq (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness) (fp : ℕ) :
    dvPtrs fs cert w.rows.length fp = ⟨gen ^ dvPx fs w fp, gen ^ dvDx fs fp, gen ^ dvHx fs w fp,
      gen ^ dvCx cert fp, gen ^ dvAx fs w fp, gen ^ dvBx fs w fp, gen ^ dvTx fs w fp, gen ^ dvWx fs w fp,
      fun b => gen ^ dvNode fs w fp b, fun b => gen ^ dvLv fs cert w fp b⟩ := rfl

/-- **The layout is the honest memory.** -/
theorem daMem_of_memL {fs : String → ℕ} {cert : String → V → ℕ} {w : Da.Witness} {fp : ℕ} {rd : Reader}
    {L : Layout} (h : MemL rd L) (hs : ∀ q ∈ dvLayout fs cert w fp, q ∈ L) :
    DaMem rd (dvPtrs fs cert w.rows.length fp) w := by
  rw [dvPtrs_eq]
  have m : ∀ {q}, q ∈ dvLayout fs cert w fp → q ∈ L := fun hq => hs _ hq
  simp only [dvLayout, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at m
  refine ⟨fun i hi => ?_, fun i hi b hb => ?_, fun b hb => ?_, ?_, fun i hi => ?_, fun i hi b hb => ?_,
    treeAt_of_memL h fun q hq => m (Or.inl (Or.inl (Or.inl (Or.inr (hq))))),
    treeAt_of_memL h fun q hq => m (Or.inl (Or.inl (Or.inr (hq)))),
    fun b hb => treeAt_of_memL h fun q hq => m (Or.inl (Or.inr (⟨b, hb, hq⟩))), fun b hb => ?_⟩
  · rw [← pow_add]
    exact load_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨i, hi, rfl⟩)))))))))))
  · rw [← pow_add]
    exact cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨i, hi, b, hb, rfl⟩)))))))))))
  · rw [← pow_add]
    exact cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨b, by omega, rfl⟩))))))))))
  · exact cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (rfl)))))))))
  · rw [← pow_add]
    exact load_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨i, hi, rfl⟩))))))))
  · rw [← pow_add]
    have := cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨i, hi, rfl⟩))))))) b (by simp; omega)
    simpa using this
  · exact cells_of_memL h (m (Or.inr (⟨b, hb, rfl⟩)))

/-! ## Within `da_verify`'s words -/

theorem clTot_ge (fs : String → ℕ) (store : Bool) (r N lp : ℕ) :
    ∀ d j, j = clLo store + d → j < clHi store →
      (j - clLo store) * fs (colLoopName store) + clTot fs store r N lp j ≤ clTot fs store r N lp (clLo store)
  | 0, j, hj, _ => by subst hj; simp
  | d + 1, j, hj, hlt => by
    have ih := clTot_ge fs store r N lp d (clLo store + d) rfl (by omega)
    have h := clTot_succ fs store r N lp (clLo store + d) (by omega)
    rw [ite_pos' (show clLo store + d + 1 < clHi store by omega), show clLo store + d + 1 = j by omega] at h
    rw [show j - clLo store = (clLo store + d - clLo store) + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega

theorem colPos_add_le (fs : String → ℕ) (store : Bool) (r N lp fp0 b : ℕ) (h1 : clLo store ≤ b)
    (h2 : b < clHi store) :
    colPos fs store r N lp fp0 b + colTot fs store b r N lp ≤ fp0 + clTot fs store r N lp (clLo store) := by
  have h := clTot_succ fs store r N lp b h2
  have hg := clTot_ge fs store r N lp (b - clLo store) b (by omega) h2
  unfold colPos
  omega

/-- **`da_verify`'s words lie in its `dvTot` words**, when its counters' run and the vector cells'
weight runs fit their frames. -/
theorem dvLayout_within (fs : String → ℕ) (cert : String → V → ℕ) {w : Da.Witness} (fp : ℕ)
    (hr1 : 1 ≤ w.rows.length) (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) :
    Within (dvLayout fs cert w fp) fp (dvTot fs w.rows.length) := by
  have hrN : w.rows.length ≤ LeanDa.nPad w.rows.length := ((logPad_iff hr1).mp rfl).1
  have hN2 : 2 ^ LeanDa.logPad w.rows.length = LeanDa.nPad w.rows.length := rfl
  have h7 : 4 * 2 ^ 7 = 512 := by norm_num
  have hT : fs "da_verify" + (dvSizes w.rows.length (LeanDa.nPad w.rows.length)).sum ≤
      dvTot fs w.rows.length := by unfold dvTot; omega
  simp only [dvSizes, List.sum_cons, List.sum_nil] at hT
  have hcol : ∀ b < 128, dvColPos fs fp w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) b +
      colTot fs (decide (b < 64)) b w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) ≤
      fp + dvTot fs w.rows.length := by
    intro b hb
    have hk : dvPos91 fs fp w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) +
        clTot fs false w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) 64 ≤
        fp + dvTot fs w.rows.length := by
      simp only [dvTot, dvKids, dvPos91, dvPos90, dvK0, List.foldr]; omega
    by_cases h64 : b < 64
    · have := colPos_add_le fs true w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length)
        (dvPos90 fs fp w.rows.length (LeanDa.nPad w.rows.length)) b (Nat.zero_le _) h64
      simp only [dvColPos, h64, decide_true, ↓reduceIte]
      simp only [clLo, ↓reduceIte] at this
      unfold dvPos91 at hk; omega
    · have := colPos_add_le fs false w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length)
        (dvPos91 fs fp w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length)) b
        (by simp [clLo]; omega) (by simp [clHi]; omega)
      simp only [dvColPos, h64, decide_false, ↓reduceIte]
      simp only [clLo, Bool.false_eq_true, ↓reduceIte] at this
      omega
  have hcol' : ∀ b < 128, fp ≤ dvColPos fs fp w.rows.length (LeanDa.nPad w.rows.length)
      (LeanDa.logPad w.rows.length) b := fun b _ => by
    unfold dvColPos colPos dvPos91 dvPos90 dvK0; split <;> omega
  intro q hq
  simp only [dvLayout, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at hq
  rcases hq with ((((((((⟨i, hi, rfl⟩ | ⟨i, hi, b, hb, rfl⟩) | ⟨b, hb, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) |
    ⟨i, hi, rfl⟩) | hq) | hq) | ⟨b, hb, hq⟩) | ⟨b, hb, rfl⟩
  · simp only [dvPx, dvDx, List.length_cons, List.length_nil]; omega
  · simp only [dvDx, List.length_cons, List.length_nil]
    have : 128 * i + 2 * b + 2 ≤ 128 * LeanDa.nPad w.rows.length := by nlinarith
    omega
  · simp only [dvHx, dvPx, dvDx, List.length_cons, List.length_nil]; omega
  · simp only [dvCx, List.length_map, List.length_range]; omega
  · simp only [dvBx, dvAx, dvHx, dvPx, dvDx, List.length_cons, List.length_nil]; omega
  · simp only [dvAx, dvHx, dvPx, dvDx, List.length_map, List.length_range]
    have : 129 * i + 129 ≤ 129 * w.rows.length := by nlinarith
    omega
  · have := treeL_within q hq
    simp only [dvTx, dvBx, dvAx, dvHx, dvPx, dvDx] at this
    omega
  · have := treeL_within q hq
    rw [hN2] at this
    simp only [dvWx, dvTx, dvBx, dvAx, dvHx, dvPx, dvDx] at this
    omega
  · have := treeL_within q hq
    have := hcol b hb
    have := hcol' b hb
    rw [hN2] at *
    unfold dvNode colTot at *
    omega
  · have := hcol b hb
    have := hcol' b hb
    have := hc4 (decide (b = 127))
    have hl : (daWs w b).length ≤ 256 := by unfold daWs; simp
    dsimp only
    unfold dvLv dvNode colTot at *
    omega

/-! ## `da_verify`, complete uniformly -/

/-- `da_verify`'s precondition: the squares table, and a witness opening the returned claim. -/
def DaPre (rd : Reader) : List E → List E → Prop
  | [gsq], [r0, r1, v0, v1] => SquaresAt rd gsq ∧ ∃ (root vd : Digest) (w : Da.Witness),
      w.Opens root vd ∧ (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd
  | _, _ => False

theorem daPre_shape {rd : Reader} {args rets : List E} (h : DaPre rd args rets) :
    ∃ gsq r0 r1 v0 v1, args = [gsq] ∧ rets = [r0, r1, v0, v1] := by
  unfold DaPre at h
  split at h
  · exact ⟨_, _, _, _, _, rfl, rfl⟩
  · exact h.elim

/-- **`da_verify` is complete, uniformly placed**, on a memory defined below `2^κ`, `κ ≥ 16`, when
its counters' run and the vector cells' weight runs fit their frames. -/
theorem da_verify_completeRel (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) :
    CompleteRel fs cert κ "da_verify" DaPre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨gsq, r0, r1, v0, v1, rfl, rfl⟩ := daPre_shape (hpre rd1 hl1 hL1)
  obtain ⟨-, root, vd, w, hw, hr, hv⟩ := hpre rd1 hl1 hL1
  have hlp : LeanDa.logPad w.rows.length < 16 := by have := logPad_le hw.2.1; omega
  have hR := forced_load (p := gsq * gen ^ LeanDa.logPad w.rows.length) (k := 0)
    (v := gen ^ 2 ^ LeanDa.logPad w.rows.length) (fun rd hl hL => by
      have := (hpre rd hl hL).1 _ hlp
      exact (LeanVM.Guest.B1.Digest.loadHolds_mul_gen_pow _ _ _ _).mpr (by rwa [Nat.add_zero])) hl1 hL1
  refine ⟨dvTot fs w.rows.length, dvLayout fs cert w fp, _, [], ⟨rfl, rfl⟩,
    by rw [List.nil_append]; exact dvLayout_within fs cert fp hw.1 hc20 hc4, fun rd hl hL => ?_⟩
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLi⟩ := Main.memL_append.mp hL
  have hlow : Low16 rd := fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  have h := dv_relAtIn fs cert hlow (hpre rd hl hLi).1 hw hR fp (daMem_of_memL hLo fun q hq => hq)
  rw [show r0 = (digestScalars root).1 from congrArg Prod.fst hr,
    show r1 = (digestScalars root).2 from congrArg Prod.snd hr,
    show v0 = (digestScalars vd).1 from congrArg Prod.fst hv,
    show v1 = (digestScalars vd).2 from congrArg Prod.snd hv]
  exact LeanVM.Guest.B1.relAtIn_dmono h fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq

end
end LeanVM.Guest.B1.Digest
