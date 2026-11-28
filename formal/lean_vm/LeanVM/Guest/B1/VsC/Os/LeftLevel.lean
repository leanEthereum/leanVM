/-
  LeanVM.Guest.B1.VsC.Os.LeftLevel

  One level's callees of `open_stacked`, placed in order at the node's valuation (`KidsAtF`).
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftLeaves
public import LeanVM.Guest.B1.VsC.Os.LeftCalls
public import LeanVM.Guest.Complete.SegA

/-!
# A level's callees, placed

`osLvSpec c l`: level `l`'s entries of `osCallSpec` (`osCallSpec_eq`: the levels' then the tail's,
`osTailSpec`). `osLvQs`: the posts `KidsAtF` takes for them, `PostQuiet` but `level_queries`',
whose pops are the level's Merkle hints.

`kidsAtF_callStep`, `kidsAtF_leafStep`, `kidsAtF_nilStep`: `KidsAtF` one call at a time, a leaf
ending where it starts (`osLeafEnd`), the words held and data claimed kept.

`HonRun.kidsAtF_lvl`: at the node's valuation `σ0` (the helpers' honest values `OsHelperVals`, the
named callees' meanings on `rd0` and their fixed loads), level `l`'s calls, matching `osLvSpec`,
complete in order from the level's cursor `c0` to the next's `e` (`LvStep`, chosen by
`HonRun.osChain`), on every memory holding the node's words with `query_win_ptrs` the chain's
`osWq`: `opening_message`, `squeeze_point_from` and `is_zero` by `osLeaf_*` in the node's cells
`S`, `level_positions` and `level_queries` by the step's `LpAtOs` and `LqAtOs`, `level_queries`
reading the windows `level_positions` claimed and holds.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Level `l`'s entries of `osCallSpec`. -/
def osLvSpec (c : OsCfg) (l : ℕ) : List (String × Option (List V × List V)) :=
  if l = c.yrLevel then
    [("opening_message__L" ++ natStr (c.yrLen + (osLvA c l).folds) ++ "_L1", none),
      (osPositionsName (osLvA c l), some (osLpCallOf c l)),
      (osQueriesName c l (osLvA c l), some (osLqCallOf c l))]
  else
    [("opening_message__L" ++ natStr (2 + (osLvA c l).folds) ++ "_L1", none),
      ("squeeze_point_from__L" ++ natStr (osLvA c l).logCols, none),
      (osPositionsName (osLvA c l), some (osLpCallOf c l)), ("is_zero", none),
      (osQueriesName c l (osLvA c l), some (osLqCallOf c l))]

/-- The tail's entries of `osCallSpec`. -/
def osTailSpec (c : OsCfg) : List (String × Option (List V × List V)) :=
  List.replicate c.yrLog ("opening_tail_round", none) ++
  [("fold_final_msg__L" ++ natStr c.yrLog, none)] ++
  List.replicate c.yrLevel ("is_zero", none) ++
  (List.range c.yrLevel).flatMap fun l ↦
    [(osResidualName (osLvA c l), some ((osLrCalls c).getD l ([], []))), ("is_zero", none),
      (osSlowName c (osLvA c l), some ((osSlowCalls c).getD l ([], [])))]

theorem osCallSpec_eq (c : OsCfg) :
    osCallSpec c = (List.range c.levels.length).flatMap (osLvSpec c) ++ osTailSpec c := by
  simp only [osCallSpec, osTailSpec, List.append_assoc]
  rfl

/-- `level_queries`' post at level `l`: its pops the level's Merkle hints, every node exact. -/
def osLqPost (c : OsCfg) (os : List (List Opening)) (l : ℕ) (rd : Reader) (t : Tree) : Prop :=
  SameStreams (t.pops coreProgram rd)
      (Hints.levelHints (l == 0) (osLvA c l).depth (os.getD l []).length (os.getD l [])) ∧
    t.Every (ExactAt coreProgram rd)

/-- The posts of level `l`'s callees. -/
def osLvQs (c : OsCfg) (os : List (List Opening)) (l : ℕ) : List (Reader → Tree → Prop) :=
  if l = c.yrLevel then [PostQuiet, PostQuiet, osLqPost c os l]
  else [PostQuiet, PostQuiet, PostQuiet, PostQuiet, osLqPost c os l]

section
variable {al : String → Bool} {k : ℕ} {σ : Val} {Rn : ℕ → Prop} {Pre : Reader → Prop}

/-- **One entered call, then the rest.** -/
theorem kidsAtF_callStep {O : Reader → Prop} {Dacc : ℕ → Prop} {Q : Reader → Tree → Prop}
    {Qs : List (Reader → Tree → Prop)} {cl : Call} {cs : List Call} {cur e : ℕ} {Oend : Reader → Prop}
    {Dend : ℕ → Prop} (ht : cl.taken = true) {as rs : List E} (has : cl.args.map σ = as)
    (hrs : cl.rets.map σ = rs) {B ec : ℕ} {Rc Dc : ℕ → Prop} {Oc P : Reader → Prop}
    (hc : CallAtA B2C.fs al B2C.cert k cl.f as rs Rc Dc Oc P Q B (allocBase (al cl.f) cur)
      (allocBase (al cl.f) cur + B) ec)
    (hR : ∀ i, Rc i → Rn i ∨ Dacc i) (hP : ∀ rd, Pre rd → O rd → P rd)
    (hrest : KidsAtF B2C.fs al B2C.cert k σ Rn Pre (fun rd => O rd ∧ Oc rd) (fun i => Dacc i ∨ Dc i) Qs cs ec e
      Oend Dend) :
    KidsAtF B2C.fs al B2C.cert k σ Rn Pre O Dacc (Q :: Qs) (cl :: cs) cur e Oend Dend := by
  rw [KidsAtF]
  simp only [ht, ↓reduceIte]
  rw [has, hrs]
  exact ⟨B, ec, Rc, Dc, Oc, hR, hc.mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
    (fun rd h => hP rd h.1 h.2) (fun _ _ _ h => h), hrest⟩

/-- **One leaf, then the rest**, the rest from where the leaf ends. -/
theorem kidsAtF_leafStep {O : Reader → Prop} {Dacc : ℕ → Prop} {Qs : List (Reader → Tree → Prop)} {cl : Call}
    {cs : List Call} {cur e : ℕ} {Oend : Reader → Prop} {Dend : ℕ → Prop} (ht : cl.taken = true) {f : String}
    (hf : cl.f = f) {S : ℕ → Prop} {P : Reader → Prop}
    (hL : LeafAtA B2C.fs al B2C.cert k f (cl.args.map σ) (cl.rets.map σ) S (fun _ => True) P PostQuiet)
    (hS : ∀ i, S i → Rn i) (hP : ∀ rd, Pre rd → O rd → P rd)
    (hrest : KidsAtF B2C.fs al B2C.cert k σ Rn Pre O Dacc Qs cs (osLeafEnd al f cur) e Oend Dend) :
    KidsAtF B2C.fs al B2C.cert k σ Rn Pre O Dacc (PostQuiet :: Qs) (cl :: cs) cur e Oend Dend := by
  obtain ⟨f', a, r, t⟩ := cl
  simp only at hf ht
  subst hf ht
  exact kidsAtF_callStep (cl := ⟨f', a, r, true⟩) rfl rfl rfl (hL (allocBase (al f') cur) _ le_rfl)
    (fun i h => Or.inl (hS i h)) hP
    (kidsAtF_mono _ _ _ _ _ _ _ _ _ _ hrest (fun _ h => h.1) (fun _ h => Or.inl h))

theorem forall₂_three {α β : Type _} {R : α → β → Prop} {cs : List α} {a b c : β}
    (h : List.Forall₂ R cs [a, b, c]) : ∃ x y z, cs = [x, y, z] ∧ R x a ∧ R y b ∧ R z c := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩
  exact ⟨_, _, _, rfl, h1, h2, h3⟩

theorem forall₂_five {α β : Type _} {R : α → β → Prop} {cs : List α} {a b c d e : β}
    (h : List.Forall₂ R cs [a, b, c, d, e]) :
    ∃ x y z u v, cs = [x, y, z, u, v] ∧ R x a ∧ R y b ∧ R z c ∧ R u d ∧ R v e := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, _ | _⟩⟩⟩⟩⟩
  exact ⟨_, _, _, _, _, rfl, h1, h2, h3, h4, h5⟩

/-- **No call left.** -/
theorem kidsAtF_nilStep {O Oend : Reader → Prop} {Dacc Dend : ℕ → Prop} {cur : ℕ} (hO : ∀ rd, O rd → Oend rd)
    (hD : ∀ i, Dend i → Dacc i) :
    KidsAtF B2C.fs al B2C.cert k σ Rn Pre O Dacc [] [] cur cur Oend Dend := by
  rw [KidsAtF]
  exact ⟨rfl, hO, hD⟩

end

end
end LeanVM.Guest.B1.VsC

namespace LeanVM.Guest.B1.Whir.HonRun

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.B1.VsC
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

set_option hygiene false in
local notation "CC" => osCfgR (μ - minOpenLog) (r - 1)

set_option hygiene false in
local notation "LV" => osLvA (osCfgR (μ - minOpenLog) (r - 1)) l

set_option hygiene false in
local notation "HH" => hR.osHonest (cur := cur) (tabs := tabs)

/-- **Level `l`'s `opening_message` is deployed.** -/
theorem omOk_os {l : ℕ} (hl : l < (CC).levels.length) :
    ∃ n, (n, 1) ∈ omDeployed ∧ omName (n, 1) = osOmName CC l := by
  have hy := hR.yr
  by_cases hlt : l < (CC).yrLevel
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, hn, -⟩ := hR.mid hlt
    refine ⟨_, hd, ?_⟩
    rw [hn]
    simp only [osOmName, Nat.ne_of_lt hlt, ↓reduceIte]
  · have he : l = (CC).yrLevel := by omega
    subst he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, hn, -⟩ := hR.fin
    refine ⟨_, hd, ?_⟩
    rw [hn]
    simp only [osOmName, ↓reduceIte]

/-- **A non-final level's `squeeze_point_from` is deployed.** -/
theorem spfOk_os {l : ℕ} (hlt : l < (CC).yrLevel) :
    (LV).logCols ∈ spfDeployed ∧ spfName (LV).logCols = osSpfName CC l := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, hn, -⟩ := hR.mid hlt
  exact ⟨hd, hn⟩

/-- **Level `l`'s callees complete in order**, from the level's cursor `c0` to the next level's `e`,
at the node's valuation `σ0`, on every memory holding the node's words. -/
theorem kidsAtF_lvl {cur tabs : E} (al : String → Bool) (k : ℕ) {l : ℕ}
    (hl : l < (CC).levels.length) (σ0 : Val) (rd0 : Reader) (b it : ℕ) (htabs : tabs = ptrAt it)
    (R Rn Sc : ℕ → Prop) (Pre : Reader → Prop)
    (hRR : ∀ i, R i → Rn i) (hRb : ∀ i, osBufCells CC b i → Rn i) (hRS : ∀ i, Sc i → Rn i)
    (hPre : ∀ rd, Pre rd → ReadsAt rd cur xs ∧ WinTabs rd tabs)
    (lpcF : ℕ → ℕ) (O : Reader → Prop) (Dacc : ℕ → Prop)
    (hO : ∀ rd, O rd → HoldsWords rd (osWords CC b (HH).own (osWq al CC lpcF)))
    (hv : OsHelperVals CC b tabs (HH).own (HH).D σ0)
    (h0 : OsNF CC b (HH).own cur tabs xs rd0) (hS0 : OsNF CC b (HH).own cur tabs xs (restrict rd0 Sc))
    {cs : List Call} (hcs : List.Forall₂ (fun c s => callMatches c s = true) cs (osLvSpec CC l))
    (hcall : ∀ c ∈ cs, osCmin CC b (HH).own cur tabs xs rd0 c.f (c.args.map σ0) (c.rets.map σ0))
    {c0 e : ℕ} (hlpc : lpcF l = osLpC al CC l c0) (hstep : LvStep hR cur tabs al k b it R l c0 e) :
    KidsAtF B2C.fs al B2C.cert k σ0 Rn Pre O Dacc (osLvQs CC os l) cs c0 e O Dacc := by
  have hm := hR.m11
  have hr := hR.r4
  have hSt := honStatic_all _ _ hm hr
  obtain ⟨-, -, -, -, -, -, -, hqbpl⟩ := osLqReg hm hr hl
  obtain ⟨-, hqS, -⟩ := osPos_le hm hr hl
  obtain ⟨e1, hlp, hlq⟩ := hstep hl
  have hNF : ∀ rd, Pre rd → O rd → OsNF CC b (HH).own cur tabs xs rd := fun rd hp ho =>
    ⟨(hPre rd hp).1, (hPre rd hp).2, osWords_mem (hO rd ho)⟩
  have hptr : ∀ rd, O rd → ∀ k < (LV).squeezes * sqPer (LV),
      LoadHolds rd (osPtrA CC b osIxQbpA * gen ^ (LV).posOff) k
        (ptrAt (osLpF al CC l (osLpC al CC l c0) (k / sqPer (LV)) + k % sqPer (LV) * qwN (LV).depth (LV).capDepth)) :=
    fun rd ho => by
      have h := osWq_loads (al := al) hSt lpcF (osWords_qbp (HH).own_len hqbpl (hO rd ho)) hl
      rw [hlpc] at h
      exact h
  have hlpP : ∀ fp, fp = osLpFp al CC l c0 → ∀ rd, Pre rd → O rd → WinTabs rd tabs ∧ OsMemA rd CC b (HH).own ∧
      ∀ k < (LV).squeezes * sqPer (LV), LoadHolds rd (osPtrA CC b osIxQbpA * gen ^ (LV).posOff) k
        (ptrAt (osLpF al CC l (fp + B2C.fs (osPositionsName (LV))) (k / sqPer (LV)) +
          k % sqPer (LV) * qwN (LV).depth (LV).capDepth)) := fun fp hfp rd hp ho => by
    rw [hfp]
    exact ⟨(hPre rd hp).2, osWords_mem (hO rd ho), hptr rd ho⟩
  obtain ⟨n, hnd, hnn⟩ := hR.omOk_os hl
  have hlqP : ∀ cc, cc = osLpC al CC l c0 → ∀ rd, Pre rd → (O rd ∧ ∀ j < (LV).squeezes, ReadsAt rd
      (ptrAt (osLpF al CC l cc j))
      (qwRunList (LV).depth (LV).capDepth (sqSample ((HH).D l).w0 ((HH).D l).capL j))) →
      OsMemA rd CC b (HH).own ∧
        (∀ k < (LV).queries, LoadHolds rd (osPtrA CC b osIxQbpA * gen ^ (LV).posOff) k
          (ptrAt (lqWp (LV).depth (LV).capDepth (osLpF al CC l cc) k))) ∧
        ∀ j < (LV).squeezes, ReadsAt rd (ptrAt (osLpF al CC l cc j))
          (qwRunList (LV).depth (LV).capDepth (sqSample ((HH).D l).w0 ((HH).D l).capL j)) :=
    fun cc hcc rd _ ho => by
      rw [hcc] at ho ⊢
      refine ⟨osWords_mem (hO rd ho.1), fun k hk => ?_, ho.2⟩
      have h := hptr rd ho.1 k (lt_of_lt_of_le hk hqS)
      unfold lqWp
      exact h
  by_cases hy : l = (CC).yrLevel
  · -- the final level: `opening_message`, `level_positions`, `level_queries`
    have hsp : osLvSpec CC l = [("opening_message__L" ++ natStr ((CC).yrLen + (LV).folds) ++ "_L1", none),
        (osPositionsName (LV), some (osLpCallOf CC l)), (osQueriesName CC l (LV), some (osLqCallOf CC l))] := by
      simp only [osLvSpec, hy, ↓reduceIte]
    rw [hsp] at hcs
    obtain ⟨c1, c2, c3, rfl, h1, h2, h3⟩ := forall₂_three hcs
    have hq : osLvQs CC os l = [PostQuiet, PostQuiet, osLqPost CC os l] := by simp only [osLvQs, hy, ↓reduceIte]
    rw [hq]
    obtain ⟨hf1, ht1⟩ := callMatches_none h1
    have hc2 := callMatches_some h2
    have hc3 := callMatches_some h3
    subst hc2 hc3
    have hom : c1.f = osOmName CC l := by rw [hf1]; simp only [osOmName, hy, ↓reduceIte]
    obtain ⟨hpre1, hfx1⟩ := hcall c1 (by simp) (.msg n 1) (by rw [hom, ← hnn, osKindOf_om hnd])
    have hL1 := osLeaf_msg (fs := B2C.fs) (al := al) (cert := B2C.cert) k hnd hpre1 hfx1 h0 hS0
    rw [hnn] at hL1
    refine kidsAtF_leafStep ht1 hom hL1 hRS hNF ?_
    have hfp : allocBase (al (osPositionsName (LV))) (osLeafEnd al (osOmName CC l) c0) = osLpFp al CC l c0 := by
      simp only [osLpFp, hy, ↓reduceIte]
    have hcc : allocBase (al (osPositionsName (LV))) (osLeafEnd al (osOmName CC l) c0) +
        B2C.fs (osPositionsName (LV)) = osLpC al CC l c0 := by rw [hfp]; rfl
    have hfq : allocBase (al (osQueriesName CC l (LV))) e1 = osLqFp al CC l e1 := by simp only [osLqFp, hy, ↓reduceIte]
    rw [← hfp] at hlp
    rw [← hcc, ← hfq] at hlq
    unfold LpAtOs at hlp
    rw [← htabs] at hlp
    unfold LqAtOs at hlq
    refine kidsAtF_callStep (cl := ⟨osPositionsName (LV), (osLpCallOf CC l).1, (osLpCallOf CC l).2, true⟩) rfl
      (hv l hl).1 (hv l hl).2.1 hlp (fun i h => Or.inl (h.elim (hRR i) (hRb i))) (hlpP _ hfp) ?_
    refine kidsAtF_callStep (cl := ⟨osQueriesName CC l (LV), (osLqCallOf CC l).1, (osLqCallOf CC l).2, true⟩) rfl
      (hv l hl).2.2.1 (hv l hl).2.2.2.1 hlq
      (fun i h => h.elim (fun h => Or.inl (hRR i h)) fun h => h.elim (fun h => Or.inl (hRb i h)) fun h => Or.inr (Or.inr h))
      (hlqP _ hcc) ?_
    exact kidsAtF_nilStep (fun _ h => h.1.1) (fun _ h => Or.inl (Or.inl h))
  · -- a non-final level: `opening_message`, `squeeze_point_from`, `level_positions`, `is_zero`, `level_queries`
    have hlt : l < (CC).yrLevel := by have := hR.yr; omega
    have hsp : osLvSpec CC l = [("opening_message__L" ++ natStr (2 + (LV).folds) ++ "_L1", none),
        ("squeeze_point_from__L" ++ natStr (LV).logCols, none),
        (osPositionsName (LV), some (osLpCallOf CC l)), ("is_zero", none),
        (osQueriesName CC l (LV), some (osLqCallOf CC l))] := by
      simp only [osLvSpec, hy, ↓reduceIte]
    rw [hsp] at hcs
    obtain ⟨c1, c2, c3, c4, c5, rfl, h1, h2, h3, h4, h5⟩ := forall₂_five hcs
    have hq : osLvQs CC os l = [PostQuiet, PostQuiet, PostQuiet, PostQuiet, osLqPost CC os l] := by
      simp only [osLvQs, hy, ↓reduceIte]
    rw [hq]
    obtain ⟨hf1, ht1⟩ := callMatches_none h1
    obtain ⟨hf2, ht2⟩ := callMatches_none h2
    obtain ⟨hf4, ht4⟩ := callMatches_none h4
    have hc3 := callMatches_some h3
    have hc5 := callMatches_some h5
    subst hc3 hc5
    have hom : c1.f = osOmName CC l := by rw [hf1]; simp only [osOmName, hy, ↓reduceIte]
    obtain ⟨hpre1, hfx1⟩ := hcall c1 (by simp) (.msg n 1) (by rw [hom, ← hnn, osKindOf_om hnd])
    have hL1 := osLeaf_msg (fs := B2C.fs) (al := al) (cert := B2C.cert) k hnd hpre1 hfx1 h0 hS0
    rw [hnn] at hL1
    refine kidsAtF_leafStep ht1 hom hL1 hRS hNF ?_
    obtain ⟨hsd, hsn⟩ := hR.spfOk_os hlt
    have hsf : c2.f = osSpfName CC l := hf2
    obtain ⟨hpre2, hfx2⟩ := hcall c2 (by simp) (.spf (LV).logCols) (by rw [hsf, ← hsn, osKindOf_spf hsd])
    have hL2 := osLeaf_spf (fs := B2C.fs) (al := al) (cert := B2C.cert) k hsd hpre2 hfx2 h0 hS0
    rw [hsn] at hL2
    refine kidsAtF_leafStep ht2 hsf hL2 hRS hNF ?_
    have hfp : allocBase (al (osPositionsName (LV)))
        (osLeafEnd al (osSpfName CC l) (osLeafEnd al (osOmName CC l) c0)) = osLpFp al CC l c0 := by
      simp only [osLpFp, hy, ↓reduceIte]
    have hcc : allocBase (al (osPositionsName (LV))) (osLeafEnd al (osSpfName CC l) (osLeafEnd al (osOmName CC l) c0)) +
        B2C.fs (osPositionsName (LV)) = osLpC al CC l c0 := by rw [hfp]; rfl
    have hfq : allocBase (al (osQueriesName CC l (LV))) (osLeafEnd al "is_zero" e1) = osLqFp al CC l e1 := by
      simp only [osLqFp, hy, ↓reduceIte]
    rw [← hfp] at hlp
    rw [← hcc, ← hfq] at hlq
    unfold LpAtOs at hlp
    rw [← htabs] at hlp
    unfold LqAtOs at hlq
    refine kidsAtF_callStep (cl := ⟨osPositionsName (LV), (osLpCallOf CC l).1, (osLpCallOf CC l).2, true⟩) rfl
      (hv l hl).1 (hv l hl).2.1 hlp (fun i h => Or.inl (h.elim (hRR i) (hRb i))) (hlpP _ hfp) ?_
    obtain ⟨hpre4, -⟩ := hcall c4 (by simp) .iz (by rw [hf4]; exact osKindOf_isZero)
    have hL4 := osLeaf_iz (fs := B2C.fs) (al := al) (cert := B2C.cert) (S := Sc) k hpre4 (fun _ => True)
    refine kidsAtF_leafStep ht4 hf4 hL4 hRS (fun _ _ _ => trivial) ?_
    refine kidsAtF_callStep (cl := ⟨osQueriesName CC l (LV), (osLqCallOf CC l).1, (osLqCallOf CC l).2, true⟩) rfl
      (hv l hl).2.2.1 (hv l hl).2.2.2.1 hlq
      (fun i h => h.elim (fun h => Or.inl (hRR i h)) fun h => h.elim (fun h => Or.inl (hRb i h)) fun h => Or.inr (Or.inr h))
      (hlqP _ hcc) ?_
    exact kidsAtF_nilStep (fun _ h => h.1.1) (fun _ h => Or.inl (Or.inl h))

end
end LeanVM.Guest.B1.Whir.HonRun
