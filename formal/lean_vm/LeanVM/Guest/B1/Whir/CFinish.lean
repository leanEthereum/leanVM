/-
  LeanVM.Guest.B1.Whir.CFinish

  The body after the tail, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinMem

/-!
# The finish, honestly

`osFinA_complete`: on honest memory (the final message's value `Y`, the point and `point1` at
`PT`, `PT1`, the basis rows' buffer `BD`, the scales' `LS`, the inner sums' `ICH`, every level's
basis, residual and out-of-domain data), `osFinA` holds at the values `finishF`, and its returns
are `[t, PT, PT1, inner + ood sum, Y]`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- `PtSrcOk` with its pointers named. -/
def PtSrcP (rd : Reader) (P : OsPtrs) (T : E) (c : OsCfg) (i : ℕ) (v : E) : Prop :=
  if i < c.nFolds - (c.levels.headD default).folds then
    LoadHolds rd P.fch ((c.levels.headD default).folds + i) v
  else if i < c.nFolds - (c.levels.headD default).folds + c.yrLog then
    LoadHolds rd T (i - (c.nFolds - (c.levels.headD default).folds)) v
  else if i < c.nFolds + c.yrLog then
    LoadHolds rd P.fch (i - (c.nFolds - (c.levels.headD default).folds) - c.yrLog) v
  else v = 0

theorem ptSrc_of_P {σ : Val} {c : OsCfg} {tch i : ℕ} {v : E}
    (h : PtSrcP rd (ptrsOf σ) (σ (.n tch)) c i v) : PtSrcOk rd σ (osPtSrc c tch i) v := by
  unfold PtSrcP at h
  unfold osPtSrc
  dsimp only
  split_ifs at h ⊢ <;> exact h

/-- The final message's value and the point's two buffers. -/
theorem finHead_complete {k a b : ℕ} {f : String} (σ : Val) (ha : a < k) (hb : b < k)
    {Y PT PT1 : E} (hC : C f [σ (.n a), σ (.n b)] [Y]) :
    BlkF C rd σ k (k + 1 + 2) (fun i ↦ [Y, PT, PT1].getD (i - k) 0)
      [.call f [.n a, .n b] [.n k], .atom (.hint (.alloc (.n (k + 1)) pointCap)),
        .atom (.hint (.alloc (.n (k + 1 + 1)) pointCap))]
      (fun σ' ↦ σ' (.n k) = Y ∧ σ' (.n (k + 1)) = PT ∧ σ' (.n (k + 1 + 1)) = PT1 ∧
        AgreeBelow k σ σ') := by
  intro σ' hg hr
  have v0 := hr k le_rfl (by omega)
  have v1 := hr (k + 1) (by omega) (by omega)
  have v2 := hr (k + 1 + 1) (by omega) (by omega)
  simp only [Nat.sub_self, List.getD_cons_zero, Nat.add_sub_cancel_left, List.getD_cons_succ,
    show k + 1 + 1 - k = 2 by omega] at v0 v1 v2
  refine ⟨?_, v0, v1, v2, hg⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil]
  rw [hg a ha, hg b hb, v0]; exact hC

/-- `inner[0] = 0`. -/
theorem finIch0_complete {k ich : ℕ} (σ : Val) (hich : ich < k) (h0 : LoadHolds rd (σ (.n ich)) 0 0) :
    BlkF C rd σ k (k + 1) (fun _ ↦ 0)
      [.atom (.const (.n k) (word 0 0 0)), .atom (.load (.n k) (.n ich) 0)]
      (fun σ' ↦ AgreeBelow k σ σ') := by
  intro σ' hg hr
  have v0 := hr k le_rfl (by omega)
  refine ⟨?_, hg⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  exact ⟨by rw [v0, word_zero], by rw [v0, hg ich hich]; exact h0⟩

/-- The returns' copies and the inner sum plus the out-of-domain sum. -/
theorem finEnd_complete {k t pt ich acc yat n : ℕ} (σ : Val) (ht : t < k) (hpt : pt + 1 < k)
    (hich : ich < k) (hacc : acc < k) (hy : yat < k) {In : E}
    (hIn : LoadHolds rd (σ (.n ich)) n In) :
    BlkF C rd σ k (k + 6)
      (fun i ↦ [σ (.n t), σ (.n pt), σ (.n (pt + 1)), In, In + σ (.n acc), σ (.n yat)].getD (i - k) 0)
      [.atom (.copy (.n k) (.n t)), .atom (.copy (.n (k + 1)) (.n pt)),
        .atom (.copy (.n (k + 2)) (.n (pt + 1))), .atom (.load (.n (k + 3)) (.n ich) n),
        .atom (.add (.n (k + 4)) (.n (k + 3)) (.n acc)), .atom (.copy (.n (k + 5)) (.n yat))]
      (fun σ' ↦ σ' (.n k) = σ (.n t) ∧ σ' (.n (k + 1)) = σ (.n pt) ∧
        σ' (.n (k + 2)) = σ (.n (pt + 1)) ∧ σ' (.n (k + 4)) = In + σ (.n acc) ∧
        σ' (.n (k + 5)) = σ (.n yat) ∧ AgreeBelow k σ σ') := by
  intro σ' hg hr
  have V : ∀ j < 6, σ' (.n (k + j)) =
      [σ (.n t), σ (.n pt), σ (.n (pt + 1)), In, In + σ (.n acc), σ (.n yat)].getD j 0 :=
    fun j hj ↦ by rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
  have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
  have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5
  refine ⟨?_, v0, v1, v2, v4, v5, hg⟩
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  exact ⟨by rw [v0, hg t ht], by rw [v1, hg pt (by omega)], by rw [v2, hg (pt + 1) hpt],
    by rw [v3, hg ich hich]; exact hIn, by rw [v4, v3, hg acc hacc], by rw [v5, hg yat hy]⟩

theorem osOodWeights_acc_lt (c : OsCfg) (tch : ℕ) : ∀ (levels : List OsLv) (prevCols ol : ℕ)
    (acc : Option ℕ) (k : ℕ), (∀ x, acc = some x → x < k) →
      ∀ y, (osOodWeights c tch prevCols ol levels acc k).2.1 = some y →
        y < (osOodWeights c tch prevCols ol levels acc k).2.2
  | [], _, _, _, _, h => h
  | lv :: rest, prevCols, ol, acc, k, h => by
    have hw := osOodWeight_k c tch prevCols ol lv k
    have hs := accStep_k acc (osOodWeight c tch prevCols ol lv k).2 hw.2
    have e : osOodWeights c tch prevCols ol (lv :: rest) acc k =
        ((osOodWeight c tch prevCols ol lv k).1 ++
          (match acc with
            | none => []
            | some x => [.atom (.add (.n (osOodWeight c tch prevCols ol lv k).2.2) (.n x)
                (.n (osOodWeight c tch prevCols ol lv k).2.1))]) ++
          (osOodWeights c tch lv.logCols (ol + 1) rest
            (accStep acc (osOodWeight c tch prevCols ol lv k).2).1
            (accStep acc (osOodWeight c tch prevCols ol lv k).2).2).1,
          (osOodWeights c tch lv.logCols (ol + 1) rest
            (accStep acc (osOodWeight c tch prevCols ol lv k).2).1
            (accStep acc (osOodWeight c tch prevCols ol lv k).2).2).2) := by
      rcases acc with _ | x <;> rfl
    rw [e]
    exact osOodWeights_acc_lt c tch rest _ _ _ _ hs.2

/-- The values of the body after the tail. -/
def finishF (c : OsCfg) (st : OsSt) (tch : ℕ) (Y PT PT1 BD LS ICH In : E) (Pp β : ℕ → E)
    (X : ℕ → ℕ → E) (M h I L : ℕ → E) (Λ : ℕ → E) (Z Yo : ℕ → ℕ → E)
    (σ : Val) : ℕ → E :=
  let pts := osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)
  let bs := osBases c tch (pts.2 + 1) (pts.2 + 3) 0 c.levels (pts.2 + 4)
  let rs := osResiduals c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) 0 c.levels st.mats (bs.2 + 3)
  let od := osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2
  seqF σ st.k (st.k + 1 + 2) (fun i ↦ [Y, PT, PT1].getD (i - st.k) 0) fun σ1 ↦
  seqF σ1 (st.k + 1 + 2) pts.2 (ptsF c (st.k + 1) (st.k + 1 + 1) tch Pp 0 pointCap (st.k + 1 + 2) σ1)
    fun σ2 ↦
  seqF σ2 pts.2 (pts.2 + 2) (fun i ↦ [gw (c.levels.length * ligColsCap), BD].getD (i - pts.2) 0)
    fun σ3 ↦
  seqF σ3 (pts.2 + 2) (pts.2 + 2 + 2) (fun i ↦ [gw c.levels.length, LS].getD (i - (pts.2 + 2)) 0)
    fun σ4 ↦
  seqF σ4 (pts.2 + 4) bs.2 (basesF c tch (pts.2 + 1) β X 0 c.levels (pts.2 + 4) σ4) fun σ5 ↦
  seqF σ5 bs.2 (bs.2 + 2) (fun i ↦ [gw (c.levels.length + 1), ICH].getD (i - bs.2) 0) fun σ6 ↦
  seqF σ6 (bs.2 + 2) (bs.2 + 2 + 1) (fun _ ↦ 0) fun σ7 ↦
  seqF σ7 (bs.2 + 3) rs.2
    (residualsF c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) M h I L 0 c.levels st.mats (bs.2 + 3) σ7)
    fun σ8 ↦
  seqF σ8 rs.2 od.2.2
    (oodWeightsF c tch Λ Z Yo ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2 σ8)
    fun σ9 ↦
  fun i ↦ [σ9 (.n st.t), σ9 (.n (st.k + 1)), σ9 (.n (st.k + 1 + 1)), In,
    In + σ9 (.n (od.2.1.getD 0)), σ9 (.n st.k)].getD (i - od.2.2) 0

/-- The value after the body's last. -/
def osFinEnd (c : OsCfg) (st : OsSt) (tch : ℕ) : ℕ :=
  let pts := osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)
  let bs := osBases c tch (pts.2 + 1) (pts.2 + 3) 0 c.levels (pts.2 + 4)
  let rs := osResiduals c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) 0 c.levels st.mats (bs.2 + 3)
  (osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2).2.2 + 6

theorem osFinEnd_ge (c : OsCfg) (st : OsSt) (tch : ℕ) : st.k + 6 ≤ osFinEnd c st tch := by
  unfold osFinEnd
  dsimp only
  have o1 : st.k + 1 + 2 ≤ (osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)).2 :=
    osPtBlks_k _ _ _ _ _ _ _
  have o2 := osBases_k c tch ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 1) ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 3) 0 c.levels ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 4)
  have o3 := osResiduals_k c ((osBases c tch ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 1) ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 3) 0 c.levels ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 4)).2 + 1) ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 1) ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 3) 0 c.levels st.mats ((osBases c tch ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0
    pointCap (st.k + 1 + 2)).2 + 1) ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 3) 0 c.levels ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 4)).2 + 3)
  have o4 := osOodWeights_k c tch c.levels.tail ((c.levels.headD default).logCols) 1 none
    (osResiduals c ((osBases c tch ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 1) ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 3) 0 c.levels ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 4)).2 + 1) ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 1) ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 3) 0 c.levels st.mats ((osBases c tch ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0
    pointCap (st.k + 1 + 2)).2 + 1) ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 3) 0 c.levels ((osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap
    (st.k + 1 + 2)).2 + 4)).2 + 3)).2
  omega

/-- **The body after the tail, honestly.** -/
theorem osFinA_complete {c : OsCfg} {st : OsSt} {tch : ℕ} (σ : Val) (hk : 161 ≤ st.k)
    (htch : tch < st.k) (ht : st.t < st.k) (htail : c.levels.tail ≠ []) {R : E}
    (hR : σ (.n osRate) = R) (hmo : MatsOk σ st.mats) (hmob : MatsBelow st.k st.mats)
    {Y PT PT1 BD LS ICH In : E} {Pp β : ℕ → E} {X : ℕ → ℕ → E} {M h I L : ℕ → E}
    {Λ : ℕ → E} {Z Yo : ℕ → ℕ → E}
    (hC : C ("fold_final_msg__L" ++ natStr c.yrLog) [σ (.n osFmsg), σ (.n tch)] [Y])
    (hpt : ∀ j < pointCap, PtSrcP rd (ptrsOf σ) (σ (.n tch)) c j (Pp j) ∧ LoadHolds rd PT j (Pp j) ∧
      LoadHolds rd PT1 j (1 + Pp j))
    (hbs : ∀ i (hi : i < c.levels.length),
      BasisMemP rd (ptrsOf σ) (σ (.n tch)) BD LS c i c.levels[i] (β i) (X i))
    (hich0 : LoadHolds rd ICH 0 0)
    (hrs : ∀ i (hi : i < c.levels.length), ResMemP C rd (ptrsOf σ) R BD ICH LS c i c.levels[i]
      (M i) (h i) (I i) (L i))
    (hIn : LoadHolds rd ICH c.levels.length In)
    (hood : OodAllP rd (ptrsOf σ) (σ (.n tch)) c Λ Z Yo ((c.levels.headD default).logCols) 1
      c.levels.tail) :
    BlkF C rd σ st.k (osFinEnd c st tch)
      (finishF c st tch Y PT PT1 BD LS ICH In Pp β X M h I L Λ Z Yo σ)
      (osFinA c st tch)
      (fun σ' ↦ (osFinRet c st tch).map σ' = [σ (.n st.t), PT, PT1,
        In + oodSum c Λ Z Yo ((c.levels.headD default).logCols) 1 c.levels.tail, Y] ∧
        AgreeBelow st.k σ σ') := by
  unfold osFinEnd
  dsimp only
  set pts := osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2) with hpts
  set bs := osBases c tch (pts.2 + 1) (pts.2 + 3) 0 c.levels (pts.2 + 4) with hbsd
  set rs := osResiduals c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) 0 c.levels st.mats (bs.2 + 3) with hrsd
  set od := osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2 with hod
  have eA : osFinA c st tch =
      [.call ("fold_final_msg__L" ++ natStr c.yrLog) [.n osFmsg, .n tch] [.n st.k],
        .atom (.hint (.alloc (.n (st.k + 1)) pointCap)),
        .atom (.hint (.alloc (.n (st.k + 1 + 1)) pointCap))] ++ (pts.1 ++
      (osHeap (c.levels.length * ligColsCap) pts.2 ++ (osHeap c.levels.length (pts.2 + 2) ++
      (bs.1 ++ (osHeap (c.levels.length + 1) bs.2 ++
      ([.atom (.const (.n (bs.2 + 2)) (word 0 0 0)), .atom (.load (.n (bs.2 + 2)) (.n (bs.2 + 1)) 0)] ++
      (rs.1 ++ (od.1 ++
      [.atom (.copy (.n od.2.2) (.n st.t)), .atom (.copy (.n (od.2.2 + 1)) (.n (st.k + 1))),
        .atom (.copy (.n (od.2.2 + 2)) (.n (st.k + 1 + 1))),
        .atom (.load (.n (od.2.2 + 3)) (.n (bs.2 + 1)) c.levels.length),
        .atom (.add (.n (od.2.2 + 4)) (.n (od.2.2 + 3)) (.n (od.2.1.getD 0))),
        .atom (.copy (.n (od.2.2 + 5)) (.n st.k))])))))))) := by
    simp only [osFinA, List.append_assoc]; rfl
  have eR : osFinRet c st tch =
      [.n od.2.2, .n (od.2.2 + 1), .n (od.2.2 + 2), .n (od.2.2 + 4), .n (od.2.2 + 5)] := rfl
  rw [eA, eR]
  have o1 : st.k + 1 + 2 ≤ pts.2 := osPtBlks_k c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap _
  have o2 : pts.2 + 4 ≤ bs.2 := osBases_k c tch (pts.2 + 1) (pts.2 + 3) 0 c.levels _
  have o3 : bs.2 + 3 ≤ rs.2 := osResiduals_k c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) 0 c.levels _ _
  have o4 : rs.2 ≤ od.2.2 := osOodWeights_k c tch c.levels.tail _ 1 none _
  have o5 : od.2.1.getD 0 < od.2.2 := by
    rcases h : od.2.1 with _ | y
    · simp only [Option.getD_none]; omega
    · exact osOodWeights_acc_lt c tch c.levels.tail _ 1 none rs.2 (fun _ h ↦ by simp at h) y h
  have hF : osFch < st.k := by unfold osFch; omega
  have hM : osFmsg < st.k := by unfold osFmsg; omega
  unfold finishF
  -- the final message, the point's buffers
  refine BlkF.then (k1 := st.k + 1 + 2) (by omega) (by omega)
    (finHead_complete (Y := Y) (PT := PT) (PT1 := PT1) σ hM htch hC) fun σ1 ha1 hO1 ↦ ?_
  obtain ⟨hy1, hp1, hq1, -⟩ := hO1
  have hP1 := ptrsOf_agree hk ha1
  have ht1 : σ1 (.n tch) = σ (.n tch) := ha1 _ htch
  -- the point
  refine BlkF.then (k1 := pts.2) o1 (by omega)
    (osPtBlks_complete (C := C) (rd := rd) Pp 0 pointCap (st.k + 1 + 2) σ1 (by omega) (by omega)
      (by omega) (by omega) fun j _ hj ↦ ?_) fun σ2 ha2 _ ↦ ?_
  · obtain ⟨g1, g2, g3⟩ := hpt j (by omega)
    rw [← hP1, ← ht1] at g1
    exact ⟨ptSrc_of_P g1, by rw [hp1]; exact g2, by rw [hq1]; exact g3⟩
  have A2 : AgreeBelow st.k σ σ2 := ha1.trans (ha2.mono (by omega))
  -- the basis rows' buffer and the scales'
  refine BlkF.then (k1 := pts.2 + 2) (by omega) (by omega) (osHeap_complete σ2 BD)
    fun σ3 ha3 hO3 ↦ ?_
  refine BlkF.then (k1 := pts.2 + 2 + 2) (by omega) (by omega) (osHeap_complete σ3 LS)
    fun σ4 ha4 hO4 ↦ ?_
  have A4 : AgreeBelow st.k σ σ4 := (A2.trans (ha3.mono (by omega))).trans (ha4.mono (by omega))
  have hbd4 : σ4 (.n (pts.2 + 1)) = BD := (ha4 _ (by omega)).trans hO3.1
  have hls4 : σ4 (.n (pts.2 + 3)) = LS := hO4.1
  have hP4 := ptrsOf_agree hk A4
  have ht4 : σ4 (.n tch) = σ (.n tch) := A4 _ htch
  -- the basis rows
  refine BlkF.then (k1 := bs.2) o2 (by omega)
    (osBases_complete (C := C) (rd := rd) β X c.levels 0 (pts.2 + 4) σ4 (by omega) (by omega)
      (by omega) (by omega) fun i hi ↦ ?_) fun σ5 ha5 _ ↦ ?_
  · have g := hbs i hi
    rw [← hP4, ← ht4, ← hbd4, ← hls4] at g
    rw [Nat.zero_add]; exact basisMem_of_P g
  -- the inner sums' buffer and `inner[0] = 0`
  refine BlkF.then (k1 := bs.2 + 2) (by omega) (by omega) (osHeap_complete σ5 ICH)
    fun σ6 ha6 hO6 ↦ ?_
  refine BlkF.then (k1 := bs.2 + 2 + 1) (by omega) (by omega)
    (finIch0_complete σ6 (by omega) (by rw [hO6.1]; exact hich0)) fun σ7 ha7 _ ↦ ?_
  have A7 : AgreeBelow st.k σ σ7 :=
    ((A4.trans (ha5.mono (by omega))).trans (ha6.mono (by omega))).trans (ha7.mono (by omega))
  have hich7 : σ7 (.n (bs.2 + 1)) = ICH := (ha7 _ (by omega)).trans hO6.1
  have hbd7 : σ7 (.n (pts.2 + 1)) = BD :=
    (ha7 _ (by omega)).trans ((ha6 _ (by omega)).trans ((ha5 _ (by omega)).trans hbd4))
  have hls7 : σ7 (.n (pts.2 + 3)) = LS :=
    (ha7 _ (by omega)).trans ((ha6 _ (by omega)).trans ((ha5 _ (by omega)).trans hls4))
  have hP7 := ptrsOf_agree hk A7
  -- the residual sums
  refine BlkF.then (k1 := rs.2) o3 (by omega)
    (osResiduals_complete (C := C) (rd := rd) M h I L c.levels 0 st.mats (bs.2 + 3) σ7
      (by rw [A7 _ (by unfold osRate; omega), hR]) (by omega)
      (by omega) (by omega) (by omega) (matsOk_agree hmo hmob A7) (matsBelow_mono hmob (by omega))
      fun i hi ↦ ?_) fun σ8 ha8 _ ↦ ?_
  · have g := hrs i hi
    rw [← hP7, ← hbd7, ← hich7, ← hls7] at g
    rw [Nat.zero_add]; exact resMem_of_P g
  have A8 : AgreeBelow st.k σ σ8 := A7.trans (ha8.mono (by omega))
  have hP8 := ptrsOf_agree hk A8
  have ht8 : σ8 (.n tch) = σ (.n tch) := A8 _ htch
  -- the out-of-domain weights
  have hood8 := hood
  rw [← hP8, ← ht8] at hood8
  refine BlkF.then (k1 := od.2.2) o4 (by omega)
    (osOodWeights_complete (C := C) (rd := rd) Λ Z Yo c.levels.tail _ 1 none rs.2 σ8 (by omega)
      (by omega) (fun _ h ↦ by simp at h) (oodAll_of_P _ _ _ hood8)) fun σ9 ha9 hO9 ↦ ?_
  have A9 : AgreeBelow st.k σ σ9 := A8.trans (ha9.mono (by omega))
  have hacc9 := hO9.1 (Or.inr htail)
  simp only [accVal, zero_add] at hacc9
  have B9 : AgreeBelow (st.k + 1 + 2) σ1 σ9 := by
    have b3 := ha2.trans (ha3.mono (by omega))
    have b4 := b3.trans (ha4.mono (by omega))
    have b5 := b4.trans (ha5.mono (by omega))
    have b6 := b5.trans (ha6.mono (by omega))
    have b7 := b6.trans (ha7.mono (by omega))
    have b8 := b7.trans (ha8.mono (by omega))
    exact b8.trans (ha9.mono (by omega))
  have hich9 : σ9 (.n (bs.2 + 1)) = ICH :=
    (ha9 _ (by omega)).trans ((ha8 _ (by omega)).trans hich7)
  -- the returns
  refine BlkF.mono (finEnd_complete (C := C) (rd := rd) (k := od.2.2) (t := st.t) (pt := st.k + 1)
    (ich := bs.2 + 1) (acc := od.2.1.getD 0) (yat := st.k) (n := c.levels.length) σ9 (by omega)
    (by omega) (by omega) o5 (by omega) (by rw [hich9]; exact hIn)) fun σ' hO ↦ ?_
  obtain ⟨r0, r1, r2, r4, r5, ha⟩ := hO
  refine ⟨?_, A9.trans (ha.mono (by omega))⟩
  simp only [List.map_cons, List.map_nil]
  rw [r0, r1, r2, r4, r5, hacc9, A9 _ ht, B9 _ (by omega), B9 _ (by omega), B9 _ (by omega), hp1,
    hq1, hy1]

end
end LeanVM.Guest.B1.Whir
