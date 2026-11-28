/-
  LeanVM.Guest.B1.VsC.StateEndsC

  `state_ends__L{w}` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Atoms
public import LeanVM.Guest.B1.Link.Ends
import LeanVM.Guest.CoreRef

/-!
# `state_ends`, complete

`state_ends(zeta, cbits, w)` loads `zeta[k]` and `cbits[k]` and multiplies `1 + zeta[k]` into
`e0`, `1 + cbits[k] + zeta[k]` into `ec`. Its body is `seBody w` (`Link/Ends.lean`), atoms only.
`seVal`: the honest valuation, from the words `zs`, `cs` the caller holds at `zeta`, `cbits`.
`state_ends_complete`: at every width `19 ≤ w ≤ 24`, on every memory holding them, the call returns
`[Π (1 + z_k), endsProd cs zs]` by a tree that pops nothing, exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Protocol.Verifier

@[expose] public section

/-- Block `k` of `seBody`, as atoms. -/
def seBlkA (k : ℕ) : List Atom :=
  if k = 0 then
    [.load (.n 2) (.n 0) 0, .const (.n 3) (word 1 0), .add (.n 4) (.n 3) (.n 2),
      .const (.n 5) (word 1 0), .load (.n 6) (.n 1) 0, .add (.n 7) (.n 5) (.n 6),
      .add (.n 8) (.n 7) (.n 2)]
  else
    [.load (.n (9 * k)) (.n 0) k, .const (.n (9 * k + 1)) (word 1 0),
      .add (.n (9 * k + 2)) (.n (9 * k + 1)) (.n (9 * k)),
      .mul (.n (9 * k + 3)) (.n (seE0 (k - 1))) (.n (9 * k + 2)),
      .const (.n (9 * k + 4)) (word 1 0), .load (.n (9 * k + 5)) (.n 1) k,
      .add (.n (9 * k + 6)) (.n (9 * k + 4)) (.n (9 * k + 5)),
      .add (.n (9 * k + 7)) (.n (9 * k + 6)) (.n (9 * k)),
      .mul (.n (9 * k + 8)) (.n (seEc (k - 1))) (.n (9 * k + 7))]

theorem seBlk_eq (k : ℕ) : seBlk k = (seBlkA k).map Stmt.atom := by
  unfold seBlk seBlkA; split <;> rfl

/-- `seBody`'s atoms. -/
def seAtoms (w : ℕ) : List Atom :=
  ((List.range w).map seBlkA).flatten ++
    [.copy (.n (9 * w)) (.n (seE0 (w - 1))), .copy (.n (9 * w + 1)) (.n (seEc (w - 1)))]

theorem seBody_eq (w : ℕ) :
    seBody w = (seAtoms w).map Stmt.atom ++ [.ret [.n (9 * w), .n (9 * w + 1)]] := by
  unfold seBody seAtoms
  simp only [List.map_append, List.map_flatten, List.map_map, List.append_assoc, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append]
  congr 2
  exact List.map_congr_left fun k _ ↦ seBlk_eq k

theorem seAtoms_quiet (w : ℕ) : (seAtoms w).all noHint = true := by
  unfold seAtoms
  simp only [List.all_append, List.all_flatten, List.all_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, Function.comp_apply]
  refine ⟨fun k _ ↦ ?_, by simp [noHint]⟩
  unfold seBlkA; split <;> simp [noHint]

section Val

variable (zeta cbits : E) (zs cs : List E) (w : ℕ)

/-- `1 + zeta[0..k]` multiplied. -/
def seE0V (k : ℕ) : E := prodE ((List.range (k + 1)).map fun j ↦ 1 + zs.getD j 0)

/-- `1 + cbits[j] + zeta[j]` over `j ≤ k` multiplied. -/
def seEcV (k : ℕ) : E := prodE ((List.range (k + 1)).map fun j ↦ 1 + cs.getD j 0 + zs.getD j 0)

/-- **The honest word of value `i`.** -/
def seVal (i : ℕ) : E :=
  if i = 9 * w then seE0V zs (w - 1) else if i = 9 * w + 1 then seEcV zs cs (w - 1) else
  if i = 0 then zeta else if i = 1 then cbits else if i = 2 then zs.getD 0 0 else
  if i = 3 then 1 else if i = 4 then seE0V zs 0 else if i = 5 then 1 else
  if i = 6 then cs.getD 0 0 else if i = 7 then 1 + cs.getD 0 0 else if i = 8 then seEcV zs cs 0 else
  if i % 9 = 0 then zs.getD (i / 9) 0 else if i % 9 = 1 then 1 else
  if i % 9 = 2 then 1 + zs.getD (i / 9) 0 else if i % 9 = 3 then seE0V zs (i / 9) else
  if i % 9 = 4 then 1 else if i % 9 = 5 then cs.getD (i / 9) 0 else
  if i % 9 = 6 then 1 + cs.getD (i / 9) 0 else if i % 9 = 7 then 1 + cs.getD (i / 9) 0 + zs.getD (i / 9) 0
  else seEcV zs cs (i / 9)

/-- The honest valuation. -/
def seSigma : Val := fun v ↦ seVal zeta cbits zs cs w v.idx

end Val

theorem seE0V_succ (zs : List E) (k : ℕ) : seE0V zs (k + 1) = seE0V zs k * (1 + zs.getD (k + 1) 0) := by
  unfold seE0V
  rw [List.range_succ, List.map_append, prodE_append]
  simp [prodE_cons, prodE_nil]

theorem seEcV_succ (zs cs : List E) (k : ℕ) :
    seEcV zs cs (k + 1) = seEcV zs cs k * (1 + cs.getD (k + 1) 0 + zs.getD (k + 1) 0) := by
  unfold seEcV
  rw [List.range_succ, List.map_append, prodE_append]
  simp [prodE_cons, prodE_nil]

theorem seE0V_zero (zs : List E) : seE0V zs 0 = 1 + zs.getD 0 0 := by
  simp [seE0V, prodE_cons, prodE_nil]

theorem seEcV_zero (zs cs : List E) : seEcV zs cs 0 = 1 + cs.getD 0 0 + zs.getD 0 0 := by
  simp [seEcV, prodE_cons, prodE_nil]

section Holds

variable {zeta cbits : E} {zs cs : List E} {w : ℕ}

theorem seVal_blk {k j : ℕ} (hk : 1 ≤ k) (hkw : k < w) (hj : j < 9) :
    seVal zeta cbits zs cs w (9 * k + j) =
      if j = 0 then zs.getD k 0 else if j = 1 then 1 else if j = 2 then 1 + zs.getD k 0 else
      if j = 3 then seE0V zs k else if j = 4 then 1 else if j = 5 then cs.getD k 0 else
      if j = 6 then 1 + cs.getD k 0 else if j = 7 then 1 + cs.getD k 0 + zs.getD k 0
      else seEcV zs cs k := by
  have h1 : (9 * k + j) / 9 = k := by omega
  have h2 : (9 * k + j) % 9 = j := by omega
  unfold seVal
  have n : ∀ m, 9 * k + j ≠ m → (9 * k + j = m) = False := fun m h ↦ eq_false h
  rw [ite_eq_right_of_eq_false _ _ (n _ (by omega)), ite_eq_right_of_eq_false _ _ (n _ (by omega)),
    ite_eq_right_of_eq_false _ _ (n _ (by omega)), ite_eq_right_of_eq_false _ _ (n _ (by omega)),
    ite_eq_right_of_eq_false _ _ (n _ (by omega)), ite_eq_right_of_eq_false _ _ (n _ (by omega)),
    ite_eq_right_of_eq_false _ _ (n _ (by omega)), ite_eq_right_of_eq_false _ _ (n _ (by omega)),
    ite_eq_right_of_eq_false _ _ (n _ (by omega)), ite_eq_right_of_eq_false _ _ (n _ (by omega)),
    ite_eq_right_of_eq_false _ _ (n _ (by omega)), h1, h2]

theorem seVal_E0 {j : ℕ} (hj : j < w) : seVal zeta cbits zs cs w (seE0 j) = seE0V zs j := by
  unfold seE0
  split
  · next h => subst h; unfold seVal; simp only [show ¬ 4 = 9 * w by omega, show ¬ 4 = 9 * w + 1 by omega]; rfl
  · next h => rw [seVal_blk (by omega) hj (by omega)]; rfl

theorem seVal_Ec {j : ℕ} (hj : j < w) : seVal zeta cbits zs cs w (seEc j) = seEcV zs cs j := by
  unfold seEc
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; unfold seVal; simp only [show ¬ 9 * 0 + 8 = 9 * w by omega, show ¬ 9 * 0 + 8 = 9 * w + 1 by omega]; rfl
  · rw [seVal_blk h hj (by omega)]; rfl

theorem seVal_small {i : ℕ} (hi : i < 9) (hw : 1 ≤ w) :
    seVal zeta cbits zs cs w i =
      [zeta, cbits, zs.getD 0 0, 1, seE0V zs 0, 1, cs.getD 0 0, 1 + cs.getD 0 0, seEcV zs cs 0].getD i 0 := by
  unfold seVal
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  interval_cases i <;> rfl

theorem list_eq_range (l : List E) : l = (List.range l.length).map fun j ↦ l.getD j 0 := by
  refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem seE0V_eq (hzl : zs.length = w) (hw : 1 ≤ w) : seE0V zs (w - 1) = prodE (zs.map (1 + ·)) := by
  unfold seE0V
  rw [Nat.sub_add_cancel hw]
  conv_rhs => rw [list_eq_range zs, List.map_map, hzl]
  rfl

theorem seEcV_eq (hzl : zs.length = w) (hcl : cs.length = w) (hw : 1 ≤ w) :
    seEcV zs cs (w - 1) = endsProd cs zs := by
  unfold seEcV endsProd
  rw [Nat.sub_add_cancel hw]
  conv_rhs => rw [list_eq_range zs, list_eq_range cs, hzl, hcl, zipWith_range_map]

/-- **Block `k`'s atoms hold** on a memory holding `zs` at `zeta` and `cs` at `cbits`. -/
theorem seBlkA_holds {rd : Reader} (hz : ReadsAt rd zeta zs) (hc : ReadsAt rd cbits cs)
    (hzl : zs.length = w) (hcl : cs.length = w) {k : ℕ} (hk : k < w) :
    ∀ a ∈ seBlkA k, a.Holds rd (seSigma zeta cbits zs cs w) := by
  have hzk : ∀ j < w, LoadHolds rd zeta j (zs.getD j 0) := fun j hj ↦ by
    have := hz j (by omega)
    rwa [List.getD_eq_getElem _ _ (by omega)]
  have hck : ∀ j < w, LoadHolds rd cbits j (cs.getD j 0) := fun j hj ↦ by
    have := hc j (by omega)
    rwa [List.getD_eq_getElem _ _ (by omega)]
  have hw : 1 ≤ w := by omega
  have sv : ∀ i, seSigma zeta cbits zs cs w (.n i) = seVal zeta cbits zs cs w i := fun _ ↦ rfl
  unfold seBlkA
  split
  · next h0 =>
    subst h0
    have v : ∀ i (hi : i < 9), seSigma zeta cbits zs cs w (.n i) =
        [zeta, cbits, zs.getD 0 0, 1, seE0V zs 0, 1, cs.getD 0 0, 1 + cs.getD 0 0,
          seEcV zs cs 0].getD i 0 := fun i hi ↦ by rw [sv, seVal_small hi hw]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Atom.Holds, v _ (by norm_num : (0 : ℕ) < 9), v _ (by norm_num : (1 : ℕ) < 9),
        v _ (by norm_num : (2 : ℕ) < 9), v _ (by norm_num : (3 : ℕ) < 9), v _ (by norm_num : (4 : ℕ) < 9),
        v _ (by norm_num : (5 : ℕ) < 9), v _ (by norm_num : (6 : ℕ) < 9), v _ (by norm_num : (7 : ℕ) < 9),
        v _ (by norm_num : (8 : ℕ) < 9), List.getD_cons_zero, List.getD_cons_succ, word_one,
        seE0V_zero, seEcV_zero]
    all_goals first | exact hzk 0 hk | exact hck 0 hk
  · next h0 =>
    have vb : ∀ j (hj : j < 9), seSigma zeta cbits zs cs w (.n (9 * k + j)) =
        seVal zeta cbits zs cs w (9 * k + j) := fun _ _ ↦ rfl
    have v0 : seSigma zeta cbits zs cs w (.n (9 * k)) = zs.getD k 0 := by
      rw [sv, show 9 * k = 9 * k + 0 from rfl, seVal_blk (by omega) hk (by norm_num)]; rfl
    have v1 : seSigma zeta cbits zs cs w (.n (9 * k + 1)) = 1 := by
      rw [vb 1 (by norm_num), seVal_blk (by omega) hk (by norm_num)]; rfl
    have v2 : seSigma zeta cbits zs cs w (.n (9 * k + 2)) = 1 + zs.getD k 0 := by
      rw [vb 2 (by norm_num), seVal_blk (by omega) hk (by norm_num)]; rfl
    have v3 : seSigma zeta cbits zs cs w (.n (9 * k + 3)) = seE0V zs k := by
      rw [vb 3 (by norm_num), seVal_blk (by omega) hk (by norm_num)]; rfl
    have v4 : seSigma zeta cbits zs cs w (.n (9 * k + 4)) = 1 := by
      rw [vb 4 (by norm_num), seVal_blk (by omega) hk (by norm_num)]; rfl
    have v5 : seSigma zeta cbits zs cs w (.n (9 * k + 5)) = cs.getD k 0 := by
      rw [vb 5 (by norm_num), seVal_blk (by omega) hk (by norm_num)]; rfl
    have v6 : seSigma zeta cbits zs cs w (.n (9 * k + 6)) = 1 + cs.getD k 0 := by
      rw [vb 6 (by norm_num), seVal_blk (by omega) hk (by norm_num)]; rfl
    have v7 : seSigma zeta cbits zs cs w (.n (9 * k + 7)) = 1 + cs.getD k 0 + zs.getD k 0 := by
      rw [vb 7 (by norm_num), seVal_blk (by omega) hk (by norm_num)]; rfl
    have v8 : seSigma zeta cbits zs cs w (.n (9 * k + 8)) = seEcV zs cs k := by
      rw [vb 8 (by norm_num), seVal_blk (by omega) hk (by norm_num)]; rfl
    have e0 : seSigma zeta cbits zs cs w (.n (seE0 (k - 1))) = seE0V zs (k - 1) := by
      rw [sv, seVal_E0 (by omega)]
    have ec : seSigma zeta cbits zs cs w (.n (seEc (k - 1))) = seEcV zs cs (k - 1) := by
      rw [sv, seVal_Ec (by omega)]
    have hs0 : seSigma zeta cbits zs cs w (.n 0) = zeta := by rw [sv, seVal_small (by norm_num) hw]; rfl
    have hs1 : seSigma zeta cbits zs cs w (.n 1) = cbits := by rw [sv, seVal_small (by norm_num) hw]; rfl
    have s0 : seE0V zs k = seE0V zs (k - 1) * (1 + zs.getD k 0) := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [seE0V_succ, Nat.add_sub_cancel]
    have sc : seEcV zs cs k = seEcV zs cs (k - 1) * (1 + cs.getD k 0 + zs.getD k 0) := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [seEcV_succ, Nat.add_sub_cancel]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Atom.Holds, v0, v1, v2, v3, v4, v5, v6, v7, v8, e0, ec, hs0, hs1, word_one]
    all_goals first | exact hzk _ hk | exact hck _ hk | exact s0 | exact sc

/-- **`state_ends`' template completes** on a memory holding the `w` words `zs` at `zeta` and
`cs` at `cbits`, returning `[Π (1 + z_k), endsProd cs zs]`. -/
theorem se_complete {kd : ℕ} (w : ℕ) (hw : 1 ≤ w) {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = seBody w) (zeta cbits : E) (zs cs : List E) (hzl : zs.length = w)
    (hcl : cs.length = w) :
    CallCompletes0 kd name [zeta, cbits] [prodE (zs.map (1 + ·)), endsProd cs zs]
      (fun rd ↦ ReadsAt rd zeta zs ∧ ReadsAt rd cbits cs) PostQuiet := by
  have sv : ∀ i, seSigma zeta cbits zs cs w (.n i) = seVal zeta cbits zs cs w i := fun _ ↦ rfl
  refine callCompletes0_atoms (seSigma zeta cbits zs cs w) hfind (by rw [hbody, seBody_eq]) ?_ ?_
    (seAtoms_quiet w) ?_
  · rw [hparams]
    simp only [List.map_cons, List.map_nil, sv, seVal_small (by norm_num : (0 : ℕ) < 9) hw,
      seVal_small (by norm_num : (1 : ℕ) < 9) hw]
    rfl
  · simp only [List.map_cons, List.map_nil, sv]
    unfold seVal
    simp only [↓reduceIte, show 9 * w + 1 ≠ 9 * w by omega]
    rw [seE0V_eq hzl hw, seEcV_eq hzl hcl hw]
  · intro rd _ ⟨hz, hc⟩ a ha
    unfold seAtoms at ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
      exact seBlkA_holds hz hc hzl hcl (List.mem_range.mp hk) a hal
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> simp only [Atom.Holds, sv]
      · rw [seVal_E0 (by omega)]; unfold seVal; simp only [↓reduceIte]
      · rw [seVal_Ec (by omega)]; unfold seVal; simp only [↓reduceIte, show 9 * w + 1 ≠ 9 * w by omega]

end Holds


/-! ## The specializations -/

/-- What `state_ends__L{w}`'s completeness gives, its arguments and memory. -/
def StateEndsComplete (kd w : ℕ) (name : String) : Prop :=
  ∀ (zeta cbits : E) (zs cs : List E), zs.length = w → cs.length = w →
    CallCompletes0 kd name [zeta, cbits] [prodE (zs.map (1 + ·)), endsProd cs zs]
      (fun rd ↦ ReadsAt rd zeta zs ∧ ReadsAt rd cbits cs) PostQuiet

set_option maxRecDepth 100000 in
theorem state_ends_L19_complete (kd : ℕ) : StateEndsComplete kd 19 "state_ends__L19" :=
  fun zeta cbits zs cs hzl hcl ↦ se_complete (kd := kd) 19 (by omega) (f := fn% «state_ends__L19»)
    (coreProgram_find?_at (j := idx% «state_ends__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) zeta cbits zs cs hzl hcl

set_option maxRecDepth 100000 in
theorem state_ends_L20_complete (kd : ℕ) : StateEndsComplete kd 20 "state_ends__L20" :=
  fun zeta cbits zs cs hzl hcl ↦ se_complete (kd := kd) 20 (by omega) (f := fn% «state_ends__L20»)
    (coreProgram_find?_at (j := idx% «state_ends__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) zeta cbits zs cs hzl hcl

set_option maxRecDepth 100000 in
theorem state_ends_L21_complete (kd : ℕ) : StateEndsComplete kd 21 "state_ends__L21" :=
  fun zeta cbits zs cs hzl hcl ↦ se_complete (kd := kd) 21 (by omega) (f := fn% «state_ends__L21»)
    (coreProgram_find?_at (j := idx% «state_ends__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) zeta cbits zs cs hzl hcl

set_option maxRecDepth 100000 in
theorem state_ends_L22_complete (kd : ℕ) : StateEndsComplete kd 22 "state_ends__L22" :=
  fun zeta cbits zs cs hzl hcl ↦ se_complete (kd := kd) 22 (by omega) (f := fn% «state_ends__L22»)
    (coreProgram_find?_at (j := idx% «state_ends__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) zeta cbits zs cs hzl hcl

set_option maxRecDepth 100000 in
theorem state_ends_L23_complete (kd : ℕ) : StateEndsComplete kd 23 "state_ends__L23" :=
  fun zeta cbits zs cs hzl hcl ↦ se_complete (kd := kd) 23 (by omega) (f := fn% «state_ends__L23»)
    (coreProgram_find?_at (j := idx% «state_ends__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) zeta cbits zs cs hzl hcl

set_option maxRecDepth 100000 in
theorem state_ends_L24_complete (kd : ℕ) : StateEndsComplete kd 24 "state_ends__L24" :=
  fun zeta cbits zs cs hzl hcl ↦ se_complete (kd := kd) 24 (by omega) (f := fn% «state_ends__L24»)
    (coreProgram_find?_at (j := idx% «state_ends__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) zeta cbits zs cs hzl hcl

/-- **Every `state_ends__L{w}` completes**, `19 ≤ w ≤ 24`. -/
theorem state_ends_complete (kd : ℕ) : ∀ w, 19 ≤ w → w ≤ 24 →
    StateEndsComplete kd w (seNames.getD (w - 19) "") := by
  intro w h1 h2
  interval_cases w
  · exact state_ends_L19_complete kd
  · exact state_ends_L20_complete kd
  · exact state_ends_L21_complete kd
  · exact state_ends_L22_complete kd
  · exact state_ends_L23_complete kd
  · exact state_ends_L24_complete kd

end
end LeanVM.Guest.B1.VsC
