/-
  LeanVM.Guest.B1.Place.OsValsBody

  open_stacked's body valuation at its allocation hints: the buffers' pointers and sizes.
-/

module

public import LeanVM.Guest.B1.Place.OsVals

/-!
# The body's buffers, its pointers and sizes

`body_alloc_vals`: the valuation holding the body's values on the honest trace with the buffers
from `b0` (`osAtOf c b0`) holds, at its allocation hints, the buffers' pointers
(`osPtrAt c b0 j`) and size words (`gw` of `osSizesL c`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## Lists by segments -/

theorem range_map_add {α : Type} (f : ℕ → α) (a b : ℕ) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map (fun j ↦ f (a + j)) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem range_map_pairs {α : Type} (f : ℕ → α) (a : ℕ) : ∀ n : ℕ,
    (List.range (2 * n)).map (fun j ↦ f (a + j)) =
      (List.range n).flatMap (fun j ↦ [f (a + 2 * j), f (a + 2 * j + 1)])
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, range_map_add, range_map_pairs f a n,
      List.range_succ (n := n), List.flatMap_append]
    congr 1

/-- **The pointers' list by segments**: the head's, the levels' pairs, the tail's, the finish's
five, the residual chains'. -/
theorem range_map_os {α : Type} (f : ℕ → α) (n : ℕ) :
    (List.range (18 + 3 * n)).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11] ++
      (List.range n).flatMap (fun j ↦ [f (12 + 2 * j), f (13 + 2 * j)]) ++
      [f (12 + 2 * n)] ++ ([f (13 + 2 * n), f (14 + 2 * n), f (15 + 2 * n), f (16 + 2 * n),
        f (17 + 2 * n)] ++ (List.range n).map (fun j ↦ f (18 + 2 * n + j))) := by
  rw [show 18 + 3 * n = 12 + (2 * n + (1 + (5 + n))) by ring, range_map_add, range_map_add,
    range_map_pairs f 12, range_map_add, range_map_add]
  have e12 : (List.range 12).map f =
      [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11] := rfl
  have eP : ((List.range n).flatMap fun j ↦ [f (12 + 2 * j), f (12 + 2 * j + 1)]) =
      (List.range n).flatMap fun j ↦ [f (12 + 2 * j), f (13 + 2 * j)] :=
    List.flatMap_congr fun j _ ↦ by rw [show 12 + 2 * j + 1 = 13 + 2 * j by ring]
  have e1 : (List.range 1).map (fun j ↦ f (12 + (2 * n + j))) = [f (12 + 2 * n)] := by simp
  have e5 : (List.range 5).map (fun j ↦ f (12 + (2 * n + (1 + j)))) =
      [f (13 + 2 * n), f (14 + 2 * n), f (15 + 2 * n), f (16 + 2 * n), f (17 + 2 * n)] := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append, List.cons.injEq, and_true]
    exact ⟨by congr 1; omega, by congr 1; omega, by congr 1; omega, by congr 1; omega,
      by congr 1; omega⟩
  have er : (List.range n).map (fun j ↦ f (12 + (2 * n + (1 + (5 + j))))) =
      (List.range n).map (fun j ↦ f (18 + 2 * n + j)) :=
    List.map_congr_left fun j _ ↦ by congr 1; omega
  rw [e12, eP, e1, e5, er]
  simp only [List.append_assoc]

theorem levels_map_lvAt {α : Type} (c : OsCfg) (f : OsLv → α) :
    c.levels.map f = (List.range c.levels.length).map fun i ↦ f (lvAt c i) := by
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range, lvAt]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem flatMap_const_len {α β γ : Type} (K : List γ) : ∀ (l : List α) (l' : List β),
    l.length = l'.length → (l.flatMap fun _ ↦ K) = (l'.flatMap fun _ ↦ K)
  | [], [], _ => rfl
  | _ :: l, _ :: l', h => by
    rw [List.flatMap_cons, List.flatMap_cons, flatMap_const_len K l l' (by simpa using h)]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

theorem spDats_len (sq wp : ℕ → E) : ∀ (Ls : List SpLv) (i : ℕ), (spDats Ls i sq wp).length = Ls.length
  | [], _ => rfl
  | _ :: Ls, i => by rw [spDats, List.length_cons, spDats_len sq wp Ls (i + 1), List.length_cons]

/-! ## The head -/

theorem head_alloc_vals (c : OsCfg) (σ : Val) (tgt : E) (P : OsPtrs) (c0 c2 : E)
    (h : ∀ i, 9 ≤ i → i < 164 → σ (.n i) = (headVals c tgt P c0 c2).getD (i - 9) 0) :
    (headAllocs.map Prod.fst).map σ = [P.caps, P.flags, P.fmsg, P.roots, P.fch, P.betas, P.mus,
      P.qpos, P.qbp, P.win, P.oodz, P.ood] ∧
    headAllocs.map (vSz σ) = [gw (4 * c.capLen), gw c.capLen, gw c.yrLen, gw (2 * c.levels.length),
      gw c.nFolds, gw c.levels.length, gw c.levels.length, gw c.posLen, gw c.posLen, gw 128,
      gw (c.levels.length * ligColsCap), gw (c.levels.length * oodSlots)] := by
  have e : headAllocs = [osHeapA 12, osHeapA 14, osHeapA 16, osHeapA 18, osHeapA 20, osHeapA 22,
    osHeapA 24, osHeapA 26, osHeapA 28, osHeapA 30, osHeapA 160, osHeapA 162] := rfl
  have t1 : (headVals c tgt P c0 c2).getD (161 - 9) 0 = P.oodz := by
    have := headVals_end c tgt P c0 c2 1; simpa using this
  have t0 : (headVals c tgt P c0 c2).getD (160 - 9) 0 = gw (c.levels.length * ligColsCap) := by
    have := headVals_end c tgt P c0 c2 0; simpa using this
  have t3 : (headVals c tgt P c0 c2).getD (163 - 9) 0 = P.ood := by
    have := headVals_end c tgt P c0 c2 3; simpa using this
  have t2 : (headVals c tgt P c0 c2).getD (162 - 9) 0 = gw (c.levels.length * oodSlots) := by
    have := headVals_end c tgt P c0 c2 2; simpa using this
  rw [e]
  simp only [List.map_cons, List.map_nil, osHeapA, vSz, Sum.elim_inr]
  rw [h 13 (by omega) (by omega), h 15 (by omega) (by omega), h 17 (by omega) (by omega),
    h 19 (by omega) (by omega), h 21 (by omega) (by omega), h 23 (by omega) (by omega),
    h 25 (by omega) (by omega), h 27 (by omega) (by omega), h 29 (by omega) (by omega),
    h 31 (by omega) (by omega), h 161 (by omega) (by omega), h 163 (by omega) (by omega),
    h 12 (by omega) (by omega), h 14 (by omega) (by omega), h 16 (by omega) (by omega),
    h 18 (by omega) (by omega), h 20 (by omega) (by omega), h 22 (by omega) (by omega),
    h 24 (by omega) (by omega), h 26 (by omega) (by omega), h 28 (by omega) (by omega),
    h 30 (by omega) (by omega), h 160 (by omega) (by omega), h 162 (by omega) (by omega),
    t0, t1, t2, t3]
  exact ⟨rfl, rfl⟩

/-! ## The body -/

/-- **The body's valuation at its allocation hints.** -/
theorem body_alloc_vals (c : OsCfg) (tr : OsTr) (σ0 : Val) (c0 c2 : E) (b0 : ℕ)
    (hlen : tr.Ls.length = c.levels.length) :
    ((osAllocsOf c).map Prod.fst).map
        (fill σ0 9 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2) (osBodyF c tr σ0 c0 c2 (osAtOf c b0))) =
      (List.range (18 + 3 * c.levels.length)).map (osPtrAt c b0) ∧
    (osAllocsOf c).map
        (vSz (fill σ0 9 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2) (osBodyF c tr σ0 c0 c2 (osAtOf c b0)))) =
      (osSizesL c).map gw := by
  generalize hA : osAtOf c b0 = A
  generalize hE : osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2 = E
  generalize hσ : fill σ0 9 E (osBodyF c tr σ0 c0 c2 A) = σ
  have hk : 164 ≤ (osLvSt c).k := osLevels_k_ge c 0 c.levels (osHead c).2
  have hk' : (osLvSt c).k = (osLevels c 0 c.levels (osHead c).2).2.k := rfl
  have h34 : (osHead c).2.k = 164 := rfl
  have ht : (osLvSt c).k + 2 ≤ (osTlSt c).2.1.k := osTail_k2 c (osLvSt c)
  have hfe : (osTlSt c).2.1.k + 6 ≤ E := by rw [← hE]; exact osFinEnd_ge c _ _
  have V : ∀ i, 9 ≤ i → i < E → σ (.n i) = osBodyF c tr σ0 c0 c2 A i := fun i h1 h2 ↦ by
    rw [← hσ]; exact fill_in h1 h2
  -- the head
  have eH := head_alloc_vals c σ (σ0 (.n 5)) A.P c0 c2 fun i h1 h2 ↦ by
    rw [V i h1 (by omega)]
    exact bodyF_head h2
  -- the levels
  have hL := lvs_alloc_vals c σ c.levels (tr.Ds A) 0 (osHead c).2
    (fill σ0 9 164 (headF c σ0 A.P c0 c2)) (by rw [OsTr.Ds, spDats_len, hlen])
    (fun i h1 h2 ↦ by
      rw [V i (by omega) (by omega)]
      exact bodyF_lvs (by omega) (by rw [hk']; exact h2))
  rw [OsTr.Ds, spDats_pairs, hlen] at hL
  -- the tail
  have VT : σ (.n ((osLvSt c).k + 1)) = A.T ∧ σ (.n (osLvSt c).k) = gw yrLogCap := by
    constructor
    · rw [V _ (by omega) (by omega)]
      obtain ⟨σ2, h2⟩ := bodyF_tail (c := c) (σ := σ0) (P := A.P) (c0 := c0) (c2 := c2)
        (Ds := tr.Ds A) (T := A.T) (xs := tr.tailWords c) (Y := multilinearEval tr.Lf.ms tr.Tc)
        (PT := A.PT) (PT1 := A.PT1) (BD := A.BD) (LS := A.LS) (ICH := A.ICH)
        (In := finI c tr c.levels.length)
        (Pp := fun j ↦ (ptC tr (c.levels.headD default).folds).getD j 0) (β := finB c tr)
        (X := Xof tr.rs tr.Fall tr.Tc) (RC := A.rc) (acc := finAcc c tr) (M := finM tr)
        (Pq := finPq c tr) (I := finI c tr) (L := finL c tr) (D := finD c tr) (Λ := Λof tr.rs)
        (Z := Zof tr.rs) (Yo := Yof tr.rs tr.Fall tr.Tc) (i := (osLvSt c).k + 1) (by omega)
        (by omega) hk
      exact h2.trans (tailF_buf c _ σ2 _ _).2
    · rw [V _ (by omega) (by omega)]
      obtain ⟨σ2, h2⟩ := bodyF_tail (c := c) (σ := σ0) (P := A.P) (c0 := c0) (c2 := c2)
        (Ds := tr.Ds A) (T := A.T) (xs := tr.tailWords c) (Y := multilinearEval tr.Lf.ms tr.Tc)
        (PT := A.PT) (PT1 := A.PT1) (BD := A.BD) (LS := A.LS) (ICH := A.ICH)
        (In := finI c tr c.levels.length)
        (Pp := fun j ↦ (ptC tr (c.levels.headD default).folds).getD j 0) (β := finB c tr)
        (X := Xof tr.rs tr.Fall tr.Tc) (RC := A.rc) (acc := finAcc c tr) (M := finM tr)
        (Pq := finPq c tr) (I := finI c tr) (L := finL c tr) (D := finD c tr) (Λ := Λof tr.rs)
        (Z := Zof tr.rs) (Yo := Yof tr.rs tr.Fall tr.Tc) (i := (osLvSt c).k) le_rfl (by omega) hk
      exact h2.trans (tailF_buf c _ σ2 _ _).1
  -- the finish
  have hFv := fin_alloc_vals c σ (osTlSt c).2.1 (osTlSt c).2.2 (multilinearEval tr.Lf.ms tr.Tc) A.PT
    A.PT1 A.BD A.LS A.ICH (finI c tr c.levels.length)
    (fun j ↦ (ptC tr (c.levels.headD default).folds).getD j 0) (finB c tr) (Xof tr.rs tr.Fall tr.Tc)
    A.rc (finAcc c tr) (finM tr) (finI c tr) (finL c tr) (finPq c tr) (finD c tr) (Λof tr.rs)
    (Zof tr.rs) (Yof tr.rs tr.Fall tr.Tc) (fun i h1 h2 ↦ by
      rw [V i (by omega) (by rw [← hE]; exact h2)]
      exact bodyF_fin h1 hk (by omega))
  -- together
  have eT : ([osHeapA (osLvSt c).k].map Prod.fst).map σ = [A.T] := by
    simp only [List.map_cons, List.map_nil, osHeapA, VT.1]
  have eT2 : [osHeapA (osLvSt c).k].map (vSz σ) = [gw yrLogCap] := by
    simp only [List.map_cons, List.map_nil, osHeapA, vSz, Sum.elim_inr, VT.2]
  have eA : osAllocsOf c = headAllocs ++ lvsAllocs c 0 c.levels (osHead c).2 ++
      [osHeapA (osLvSt c).k] ++ finAllocs c (osTlSt c).2.1 (osTlSt c).2.2 := rfl
  rw [eA]
  refine ⟨?_, ?_⟩
  · rw [List.map_append, List.map_append, List.map_append, List.map_append, List.map_append,
      List.map_append, eH.1, hL.1, eT, hFv.1, range_map_os, ← hA]
    simp only [osAtOf, osIxT, osIxPT, osIxPT1, osIxBD, osIxLS, osIxICH, osIxSqz, osIxWp, osIxRC,
      Nat.zero_add, List.append_assoc]
  · rw [List.map_append, List.map_append, List.map_append, eH.2, hL.2, eT2, hFv.2,
      flatMap_const_len _ c.levels (List.range c.levels.length) (by simp),
      levels_map_lvAt c fun lv ↦ gw (lv.queries / resBatch + 1)]
    simp only [osSizesL, List.map_append, List.map_cons, List.map_nil, List.map_flatMap,
      List.map_map, List.append_assoc, List.cons_append, List.nil_append]
    rfl


/-! ## In the placed lift's form -/

theorem logG_gw {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gw e) = e := by
  rw [Whir.gw_eq (by unfold u128Bound; omega), logG_gen_pow he]

theorem lvsAllocs_heap (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    ∀ x ∈ lvsAllocs c lvl lvs s, ∃ k, x = osHeapA k
  | _, [], _, x, hx => by simp [lvsAllocs] at hx
  | lvl, lv :: rest, s, x, hx => by
    simp only [lvsAllocs, lvAllocs, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact lvsAllocs_heap c (lvl + 1) rest _ x hx

theorem resAllocs_heap (c : OsCfg) (ich bd ls : ℕ) : ∀ (lvl : ℕ) (levels : List OsLv) (k : ℕ),
    ∀ x ∈ resAllocs c ich bd ls lvl levels k, ∃ k', x = osHeapA k'
  | _, [], _, x, hx => by simp [resAllocs] at hx
  | lvl, lv :: rest, k, x, hx => by
    simp only [resAllocs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨_, rfl⟩
    · exact resAllocs_heap c ich bd ls (lvl + 1) rest _ x hx

/-- The hints sized by a constant are the point's buffers. -/
theorem osAllocsOf_inl (c : OsCfg) : ∀ x ∈ osAllocsOf c, ∀ n, x.2 = .inl n → n = pointCap := by
  intro x hx n hn
  have hh : ∀ k, (osHeapA k).2 ≠ .inl n := fun k h ↦ by simp [osHeapA] at h
  simp only [osAllocsOf, finAllocs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · simp only [headAllocs, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with ⟨t, -, rfl⟩ | rfl | rfl <;> exact absurd hn (hh _)
  · obtain ⟨k, rfl⟩ := lvsAllocs_heap c 0 c.levels _ x hx; exact absurd hn (hh _)
  · subst hx; exact absurd hn (hh _)
  · rcases hx with (rfl | rfl | rfl | rfl | rfl) | hx
    · simpa using hn.symm
    · simpa using hn.symm
    · exact absurd hn (hh _)
    · exact absurd hn (hh _)
    · exact absurd hn (hh _)
    · obtain ⟨k, rfl⟩ := resAllocs_heap c _ _ _ 0 c.levels _ x hx; exact absurd hn (hh _)

/-- **The two facts the placed lift asks of the body's allocation hints.** -/
theorem body_allocs_placed (c : OsCfg) (tr : OsTr) (σ0 : Val) (c0 c2 : E) (b0 : ℕ)
    (hlen : tr.Ls.length = c.levels.length) (hsz : ∀ e ∈ osSizesL c, e < 2 ^ 64 - 1) :
    ((osBodyA c).filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG
        (fill σ0 9 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2) (osBodyF c tr σ0 c0 c2 (osAtOf c b0)) s)) =
      osSizesL c ∧
    (((osBodyA c).filterMap Main.Stmt.allocSz).map Prod.fst).map
        (fill σ0 9 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2) (osBodyF c tr σ0 c0 c2 (osAtOf c b0))) =
      (bases b0 (osSizesL c)).map (fun b ↦ ofK (addressOfIndex b)) := by
  obtain ⟨h1, h2⟩ := body_alloc_vals c tr σ0 c0 c2 b0 hlen
  rw [osBodyA_allocs]
  generalize fill σ0 9 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2) (osBodyF c tr σ0 c0 c2 (osAtOf c b0)) = σ
    at h1 h2 ⊢
  refine ⟨?_, ?_⟩
  · have e : (osAllocsOf c).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) =
        ((osAllocsOf c).map (vSz σ)).map logG := by
      rw [List.map_map]
      refine List.map_congr_left fun x hx ↦ ?_
      rcases hx2 : x.2 with n | s
      · have := osAllocsOf_inl c x hx n hx2
        subst this
        simp only [Function.comp_apply, vSz, hx2, Sum.elim_inl, id]
        rw [logG_gw (by unfold pointCap; omega)]
      · simp [vSz, hx2]
    rw [e, h2, List.map_map]
    conv_rhs => rw [← List.map_id (osSizesL c)]
    exact List.map_congr_left fun e he ↦ logG_gw (hsz e he)
  · rw [h1]
    refine List.ext_getElem (by simp [os_length_bases, osSizesL_length]) fun j hj1 hj2 ↦ ?_
    simp only [List.getElem_map, List.getElem_range, osPtrAt, osBase]
    rw [List.getD_eq_getElem _ _ (by simpa [os_length_bases, osSizesL_length] using hj1)]

end
end LeanVM.Guest.B1
