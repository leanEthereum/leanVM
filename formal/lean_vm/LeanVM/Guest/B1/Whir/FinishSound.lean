/-
  LeanVM.Guest.B1.Whir.FinishSound

  The body after the closing rounds returns the Spec's terminal.
-/

module

public import LeanVM.Guest.B1.Whir.Finish

/-!
# The finish, soundly (G:1706-1806)

`osFinish_sound`: from `FinishIn` (the non-final levels' records in memory, every `α` in
`fold_challenges`, the tail challenges, the final lane, the static facts), the statements of
`osFinish` before its return give the returned values: the guest's closing claim plus the
deficit times the closing challenges, the point buffers, the glued weight at the terminal point,
and the final lane's low part at the tail challenges.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

instance : Inhabited OsRec := ⟨⟨0, 0, 0, [], [], []⟩⟩

/-- What the finish reads. -/
structure FinishIn (rd : Reader) (C : CallRel) (σ : Val) (c : OsCfg) (tch : ℕ)
    (G T fold : List E) (recs : List OsRec) : Prop where
  n2 : 2 ≤ c.levels.length
  yr : c.yrLevel = c.levels.length - 1
  ylog : 1 ≤ c.yrLog
  ylen : 2 ^ c.yrLog = c.yrLen
  recl : recs.length = c.yrLevel
  stored : ∀ i < c.yrLevel, RecStored rd σ i (c.levels.getD i default) (recs.getD i default)
  lv : ∀ i < c.yrLevel, LvFin c (c.levels.getD i default) (c.levels.getD (i + 1) default)
  rate : ∀ i < c.yrLevel, LvRate σ c i (c.levels.getD i default)
  res : ∀ i < c.yrLevel, ∀ a r, C (osResidualName (c.levels.getD i default)) a r →
    MeaningLevelResidual (c.levels.getD i default).queries (c.levels.getD i default).logCols
      (c.levels.getD i default).folds (c.levels.getD i default).highBits rd a r
  nlen : c.levels.length ≤ 64
  Gl : G.length = c.nFolds
  fch : ∀ j (h : j < G.length), LoadHolds rd (σ (.n osFch)) j G[j]
  Tl : T.length = c.yrLog
  tch : ReadsAt rd (σ (.n tch)) T
  fmsg : ReadsAt rd (σ (.n osFmsg)) fold
  foldl : c.yrLen ≤ fold.length
  lane : (c.levels.headD default).folds ≤ c.nFolds
  mu40 : c.nFolds + c.yrLog ≤ pointCap
  ffm : ∀ a r, C ("fold_final_msg__L" ++ natStr c.yrLog) a r → MeaningFoldFinalMsg c.yrLog rd a r

theorem osOodWeights_some {c : OsCfg} {tch : ℕ} : ∀ (lvs : List OsLv) (pc ol : ℕ) (acc : Option ℕ)
    (k : ℕ), lvs ≠ [] → ∃ x, (osOodWeights c tch pc ol lvs acc k).2.1 = some x
  | [], _, _, _, _, h => absurd rfl h
  | lv :: [], pc, ol, acc, k, _ => by
    simp only [osOodWeights]
    exact osAcc_some
  | lv :: lv' :: rest, pc, ol, acc, k, _ => by
    simp only [osOodWeights]
    exact osOodWeights_some (lv' :: rest) _ _ _ _ (by simp)

theorem sum_list_range {α : Type} [Inhabited α] (f : α → E) :
    ∀ l : List α, (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i default)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_list_range f l, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem sum_flatMap' {α : Type} (g : α → List E) :
    ∀ l : List α, (l.flatMap g).sum = (l.map fun a ↦ (g a).sum).sum
  | [] => by simp
  | a :: l => by rw [List.flatMap_cons, List.sum_append, sum_flatMap' g l, List.map_cons, List.sum_cons]

/-- **The glued weight**, level by level. -/
theorem inner_sum (recs : List OsRec) (P : List E) :
    (recs.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt (P.drop g.foldStart)) 0 =
      ∑ i ∈ Finset.range recs.length,
        ((recs.getD i default).lam * eqEval (recs.getD i default).z0 (P.drop (recs.getD i default).F) +
          (recs.getD i default).lam * (recs.getD i default).lam *
            inducedWeight (recs.getD i default).mu (recs.getD i default).qs
              (powers (recs.getD i default).lam (recs.getD i default).qs.length)
              (P.drop (recs.getD i default).F)) := by
  rw [foldl_add_map, zero_add, List.map_flatMap, sum_flatMap', sum_list_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [recGlued]

/-- **The finish, soundly.** -/
theorem osFinish_sound {c : OsCfg} {st : OsSt} {tch : ℕ}
    {G T fold : List E} {recs : List OsRec} (hF : FinishIn rd C σ c tch G T fold recs)
    (hmats : MatsOk σ st.mats) (hok : AllOk C rd σ (osFinishA c st tch).1) :
    ∃ pt pt1 : E, (osFinishA c st tch).2.map σ =
      [σ (.n st.claim) + T.prod * recsDeficit recs G, pt, pt1,
        (recs.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt ((G ++ T).drop g.foldStart)) 0,
        multilinearEval (fold.take c.yrLen) T] ∧
      ReadsAt rd pt (rotPt G T (c.levels.headD default).folds ++
        List.replicate (pointCap - (c.nFolds + c.yrLog)) 0) ∧
      ReadsAt rd pt1 ((rotPt G T (c.levels.headD default).folds).map (1 + ·) ++
        List.replicate (pointCap - (c.nFolds + c.yrLog)) 1) := by
  set y := c.yrLevel with hy
  set r : ℕ → OsRec := fun i ↦ recs.getD i default with hr
  set lvA : ℕ → OsLv := fun i ↦ c.levels.getD i default with hlvA
  set X : ℕ → ℕ → E := fun i t ↦ (ptFrom G T (r i).F).getD t 0 with hX
  have hRS : ∀ i < y, RecStored rd σ i (lvA i) (r i) := hF.stored
  have hLF : ∀ i < y, LvFin c (lvA i) (lvA (i + 1)) := hF.lv
  choose! li hli1 hli2 using fun i (hi : i < y) ↦ (hRS i hi).mus
  have hmid : ∀ i < y, (c.levels.take y).getD i default = lvA i := fun i hi ↦ by
    simp only [lvA, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ↓reduceIte]
  have hmidl : (c.levels.take y).length = y := by
    rw [List.length_take]; have := hF.n2; rw [hy, hF.yr]; omega
  -- the coordinates
  have hXsrc : ∀ i < y, ∀ t < (lvA i).prefixLen + c.yrLog,
      LoadHolds rd (σ (.n (coordSrc tch (lvA i) t).1)) (coordSrc tch (lvA i) t).2 (X i t) := by
    intro i hi t ht
    have hL := hLF i hi
    have hrF := (hRS i hi).F
    have hlenG := hF.Gl
    have hp1 := hL.pre
    have hp2 := hL.cols
    have hp3 := hL.le
    simp only [X, ptFrom, coordSrc]
    rw [hrF]
    by_cases h1 : t < (lvA i).prefixLen
    · simp only [h1, ↓reduceIte, hL.rfo]
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact hF.fch _ (by have := hL.pre; have := hL.cols; omega)
    · simp only [h1, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_append_right (by
          have := hL.pre; have := hL.cols; omega),
        List.getElem?_eq_getElem (by rw [hF.Tl]; have := hL.pre; have := hL.cols; omega),
        Option.getD_some]
      have := hF.tch (t - (lvA i).prefixLen) (by rw [hF.Tl]; have := hL.pre; omega)
      convert this using 2
      have := hL.pre; have := hL.cols; omega
  -- unfold the finish
  unfold osFinishA at hok ⊢
  simp only at hok ⊢
  set pts := osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2) with hpts
  set P2 := pts.2 with hP2
  set bs := osBases c tch (P2 + 1) (P2 + 3) (P2 + 5) 0 (c.levels.take c.yrLevel) (P2 + 6) with hbs
  set rs := osResiduals c (bs.2 + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 (c.levels.take c.yrLevel) st.mats
    (bs.2 + 3) with hrs
  set od := osOodWeights c tch (c.levels.headD default).logCols 1 c.levels.tail none rs.2 with hod
  set kk := od.2.2 with hkk
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hpt⟩, -⟩, -⟩, -⟩, hB⟩, -⟩, hI⟩, hR⟩, hO⟩, hE⟩ := hok
  -- the final lane at the tail challenges
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, List.map_cons, List.map_nil] at hA
  obtain ⟨hcall, -, -⟩ := hA
  have hM := hF.ffm _ _ hcall
  simp only [MeaningFoldFinalMsg] at hM
  obtain ⟨m, ps, hml, hpsl, hm, hps, hyat⟩ := hM
  have em : m = fold.take c.yrLen := by
    have := readsAt_take hm hF.fmsg (by rw [hml, hF.ylen]; exact hF.foldl)
    rw [this, hml, hF.ylen]
  have eps : ps = T := by
    have := readsAt_take hps hF.tch (by rw [hpsl, hF.Tl])
    rw [this, hpsl, ← hF.Tl, List.take_length]
  -- the point
  have hPl : (rotPt G T (c.levels.headD default).folds).length = c.nFolds + c.yrLog := by
    simp [rotPt, hF.Gl, hF.Tl]; have := hF.lane; omega
  have hpt' := osPtBlks_sound (C := C) (pt := st.k + 1) (pt1 := st.k + 1 + 1) _
    (ptSrc_ok hF.Gl hF.Tl hF.lane hF.fch hF.tch) pointCap 0 _ hpt
  have hrd1 := readsAt_padded (rd := rd) (p := σ (.n (st.k + 1))) (n := pointCap - (c.nFolds + c.yrLog)) id
    (fun i hi ↦ by
      have := (hpt' i (by rw [hPl] at hi; have := hF.mu40; omega)).1
      simpa using this)
  have hrd2 := readsAt_padded (rd := rd) (p := σ (.n (st.k + 1 + 1)))
    (n := pointCap - (c.nFolds + c.yrLog)) (fun x ↦ 1 + x)
    (fun i hi ↦ by
      have := (hpt' i (by rw [hPl] at hi; have := hF.mu40; omega)).2
      simpa using this)
  simp only [List.map_id, id, add_zero] at hrd1 hrd2
  -- the basis rows
  set β : ℕ → E := fun i ↦ (r i).lam ^ 2 * (r i).lam ^ (lvA i).queries with hβ
  have hBin : ∀ i (hi : i < (c.levels.take c.yrLevel).length), BasisIn rd σ c tch (0 + i)
      (c.levels.take c.yrLevel)[i] (β (0 + i)) (X (0 + i)) := by
    intro i hi
    rw [hmidl] at hi
    have e : (c.levels.take c.yrLevel)[i]'(by rw [hmidl]; exact hi) = lvA i := by
      rw [← hmid i hi, List.getD_eq_getElem]
    rw [e, Nat.zero_add]
    refine ⟨(hRS i hi).beta, fun t ht ↦ ⟨invW_ne (hLF i hi).mu64 (hLF i hi).inv t
      (by rw [← (hLF i hi).pre]; exact ht), hXsrc i hi t ht⟩⟩
  have hBout := osBases_sound (C := C) (rd := rd) (σ := σ) (c := c) (tch := tch) (bd := P2 + 1)
    (ls := P2 + 3) (la := P2 + 5) β X (fun _ ↦ by have := hF.ylog; omega) (c.levels.take c.yrLevel) 0
    (P2 + 6) hBin hB
  have hBo : ∀ i < y, BasisOut rd σ c (P2 + 1) (P2 + 3) (P2 + 5) i (lvA i) (β i) (X i) := by
    intro i hi
    have := hBout i (by rw [hmidl]; exact hi)
    have e : (c.levels.take c.yrLevel)[i]'(by rw [hmidl]; exact hi) = lvA i := by
      rw [← hmid i hi, List.getD_eq_getElem]
    rwa [e, Nat.zero_add] at this
  -- the inner chain's start
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, holds_load, osCst, osLd] at hI
  obtain ⟨z0, l0, l1⟩ := hI
  rw [z0, word_zero] at l0
  -- the residuals
  set D : ℕ → ℕ → E := fun i ↦ dOf (lvA i) (X i) with hD
  set hsv : ℕ → List E := fun i ↦ hsvOf (lvA i) (r i) with hhsv
  set Pos : ℕ → ℕ → E := fun i k ↦ eOfNat ((r i).qs.getD k 0) with hPos
  have hRin : ∀ i (hi : i < (c.levels.take c.yrLevel).length), ResIn rd C σ c (P2 + 1) (0 + i)
      (c.levels.take c.yrLevel)[i] (D (0 + i)) (hsv (0 + i)) (Pos (0 + i)) (li (0 + i)) := by
    intro i hi
    rw [hmidl] at hi
    have e : (c.levels.take c.yrLevel)[i]'(by rw [hmidl]; exact hi) = lvA i := by
      rw [← hmid i hi, List.getD_eq_getElem]
    rw [e, Nat.zero_add]
    have hL := hLF i hi
    have hS := hRS i hi
    have hn : i < c.levels.length := by have := hF.yr; omega
    have h64 := hF.nlen
    refine ⟨hF.rate i hi, hF.res i hi, hL.van, ⟨hL.ml1, hL.nhs, hL.b3, hL.bn, fun s hs ↦ ?_,
      by simp [hsv, hsvOf], fun c' hc ↦ ?_⟩, hL.posOff,
      lt_of_le_of_lt (Nat.mul_le_mul_right ligColsCap (show i ≤ 64 by omega)) (by decide),
      lt_of_le_of_lt (Nat.mul_le_mul_right hsStride (show i ≤ 64 by omega)) (by decide),
      fun k hk ↦ hS.pos k hk, hli1 i hi⟩
    · have := ((hBo i hi).1 s (by rw [hL.pre]; exact hs)).2
      exact this
    · rw [show (hsv i).getD c' 0 = (r i).high.getD c' 0 *
          word (hsScale (lvA i).vanish (lvA i).highBits c' (vanishInv ((lvA i).vanish + (lvA i).logCols))) 0 by
        simp only [hsv, hsvOf]
        rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]]
      exact hS.hs c' hc
  have hRout := osResiduals_sound D hsv Pos li (c.levels.take c.yrLevel) 0 st.mats (bs.2 + 3) hmats hRin hR
  have hch := ich_chain (σ := σ) (ich := bs.2 + 1) (ls := P2 + 3) (la := P2 + 5)
    (claim := σ (.n st.claim)) y
    (fun i ↦ (resAll (lvA i) (D i) (hsv i) (Pos i) (li i)).1)
    (fun i ↦ (resAll (lvA i) (D i) (hsv i) (Pos i) (li i)).2)
    (fun i ↦ β i * ∏ t ∈ Finset.range ((lvA i).prefixLen + c.yrLog), (X i t * invW (lvA i) t))
    β (fun i ↦ ∏ t ∈ Finset.range ((lvA i).prefixLen + c.yrLog), X i t) (by simpa using l0) l1
    (fun i hi ↦ (hBo i hi).2.1) (fun i hi ↦ (hRS i hi).beta) (fun i hi ↦ (hBo i hi).2.2)
    (fun i hi ↦ by
      have := hRout i (by rw [hmidl]; exact hi)
      have e : (c.levels.take c.yrLevel)[i]'(by rw [hmidl]; exact hi) = lvA i := by
        rw [← hmid i hi, List.getD_eq_getElem]
      simp only [e, Nat.zero_add] at this
      exact this) y le_rfl
  obtain ⟨hc0, hc1⟩ := hch
  -- the out-of-domain weights
  have htl : c.levels.tail.length = y := by simp [hy, hF.yr]
  have htail : ∀ i, c.levels.tail.getD i default = lvA (i + 1) := fun i ↦ by
    simp only [lvA, List.getD_eq_getElem?_getD, List.getElem?_tail]
  set W : ℕ → E := fun i ↦ (r i).lam *
    ∏ t ∈ Finset.range (lvA i).logCols, (1 + (r i).z0.getD t 0 + X i t) with hW
  have hhead : (c.levels.headD default).logCols = (fun i ↦ (lvA i).logCols) 0 := by
    simp only [lvA, List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getD_eq_getElem?_getD]
  have hodd : od = osOodWeights c tch ((fun i ↦ (lvA i).logCols) 0) 1 c.levels.tail none rs.2 := by
    rw [hod, hhead]
  rw [hodd] at hO
  have hOd := osOodWeights_val (C := C) (rd := rd) (σ := σ) (c := c) (tch := tch) c.levels.tail
    (fun i ↦ (lvA i).logCols) 1 none rs.2 W (fun i hi k hok' ↦ by
      rw [htl] at hi
      have hL := hLF i hi
      have hS := hRS i hi
      rw [htail] at hok' ⊢
      have hcl : (lvA i).logCols - c.yrLog + c.yrLog = (lvA i).logCols := by
        have := hL.pre; omega
      have hv := osOodWeight_val (lam := (r i).lam) (z := fun t ↦ (r i).z0.getD t 0)
        (p := X i) (C := C) ?_ ?_ ?_ hok'
      · rw [hv, hcl]
      · simpa [add_comm 1 i] using hS.lam1
      · intro t ht
        rw [hcl] at ht
        have := hS.z0 t (by rw [hS.z0len]; exact ht)
        rw [loadHolds_mul_gen_pow] at this
        simp only [List.getD_eq_getElem _ _ (show t < (r i).z0.length by rw [hS.z0len]; exact ht)]
        convert this using 2
        ring
      · intro t ht
        rw [hcl] at ht
        have hx := hXsrc i hi t (by rw [hL.pre]; exact ht)
        have hpre : (lvA i).logCols - c.yrLog = (lvA i).prefixLen := by have := hL.pre; omega
        simp only [coordSrc] at hx
        rw [hpre, hL.next, ← hL.rfo]
        split_ifs at hx ⊢ <;> exact hx)
    (fun i hi ↦ by rw [htail])
    hO
  -- the returns
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_copy, holds_add, osLd,
    osCp, osAdd] at hE
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hE
  obtain ⟨x, hx⟩ := osOodWeights_some (c := c) (tch := tch) c.levels.tail ((fun i ↦ (lvA i).logCols) 0) 1
    none rs.2 (by intro h; rw [h] at htl; have := hF.n2; rw [hy, hF.yr] at htl; simp at htl; omega)
  have hacc : σ (.n (od.2.1.getD 0)) = ∑ i ∈ Finset.range y, W i := by
    have := hOd
    rw [hodd, hx]
    rw [hx] at this
    simp only [accVal, zero_add, htl] at this
    exact this
  -- each level's terms
  have hterms : ∀ i < y,
      β i * (∏ t ∈ Finset.range ((lvA i).prefixLen + c.yrLog), (X i t * invW (lvA i) t)) *
          (resAll (lvA i) (D i) (hsv i) (Pos i) (li i)).1 =
        (r i).lam * (r i).lam *
          inducedWeight (r i).mu (r i).qs (powers (r i).lam (r i).qs.length) (ptFrom G T (r i).F) ∧
      β i * (∏ t ∈ Finset.range ((lvA i).prefixLen + c.yrLog), X i t) *
          (resAll (lvA i) (D i) (hsv i) (Pos i) (li i)).2 =
        T.prod * ((r i).lam ^ 2 * recH (r i) * (G.drop (r i).F).prod) ∧
      W i = (r i).lam * eqEval (r i).z0 (ptFrom G T (r i).F) := by
    intro i hi
    have hL := hLF i hi
    have hS := hRS i hi
    have h := lvl_terms hL hF.Gl hF.Tl hS.F hS.mu hS.qlen hS.hlen hS.z0len (hli2 i hi)
      (fun t ht ↦ ((hBo i hi).1 t (by rw [hL.pre]; exact ht)).1)
    rw [hL.pre]
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hrl : recs.length = y := hF.recl
  refine ⟨σ (.n (st.k + 1)), σ (.n (st.k + 1 + 1)), ?_, hrd1, hrd2⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, e1, e2, ?_, ?_⟩
  · rw [loadHolds_unique e0 hc1, recsDeficit, sum_list_range, hrl, Finset.mul_sum]
    exact congrArg (_ + ·) (Finset.sum_congr rfl fun i hi ↦ (hterms i (Finset.mem_range.mp hi)).2.1)
  · rw [e4, loadHolds_unique e3 hc0, hacc, inner_sum, hrl, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain ⟨t1, -, t3⟩ := hterms i (Finset.mem_range.mp hi)
    rw [t1, t3]
    ring
  · rw [e5]
    have := hyat
    simp only [List.cons.injEq, and_true] at this
    rw [this, em, eps]

end
end LeanVM.Guest.B1.Whir
