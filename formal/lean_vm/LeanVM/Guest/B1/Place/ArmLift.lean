/-
  LeanVM.Guest.B1.Place.ArmLift

  An arm of `open_stacked` at the merged template is complete placed, at an optional words bound,
  from the body's completeness at honest values and its callees' placed statements.
-/

module

public import LeanVM.Guest.B1.Place.ArmKids
public import LeanVM.Guest.B1.Place.OsPlaceR
import LeanVM.Guest.StmtsAppend

/-!
# An arm, placed

**`arm_completeAtO`**: a function whose body is `osBody (osCfgR m ri)`, called on arguments whose
first is the rate's selector `g^ri`, with the body's honest data (`OsHonestA`) and the caller's
words holding the cursor's words and the window table, is `CompleteAtOT` returning the claim, the
point buffers' pointers, the glued weight and the residual's value, the buffers `pt`, `pt1`, within
`osBos` words at a bound: from the named callees' placed statements (`hnamed`, and within a bound by trees
satisfying `armXT`, `hnamedT`) and the helpers' (`LpAtOE`, `LqAtOP`, `LrAtO`). Its tree is its node (`FlatNodeT`)
at a valuation on the rate's selector with the body's window hints exact (`WinEx`), the callees' trees satisfying
`armTs`: within each bound, every one `armXT` (`armTs_xt`) and level `l`'s `level_queries` popping `osLvPops`.

The proof (`os_completeAt_placeR`, the body at the rate's arm, a valuation per memory): the buffers at `osSizesL`
after the frame; on each memory holding the callees' words its own honest valuation from `OsHonestA.body`, all of
them agreeing on the call statements (`CallAg`, from `CV`) and loading words the caller's memory facts fix
(`OsLoadsIn`); the callees placed once at one of them, after the buffers, the levels' by `os_levels_kidsOT`
(`arm_lv_ok`), then the rest by `os_kids_blockOT` (`arm_rest_ok`, `arm_rest_okT`), and moved to each memory's
valuation (`kidsFromInT_congr`, `armTs_congr`); `query_win_ptrs` then holds the window pointers into the decoders
where each `level_positions` was placed (`qbpA`). When no memory holds the callees' words, every obligation on a
memory is void.

`kidsT_mono`, `lvTs_forall₂`: callees' trees of stronger predicates satisfy weaker ones.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **The body's statements are selected at the rate**: atoms, calls, the rate's dispatches and
`match`es of quiet arms, four arms each. -/
theorem selOk_body {c : OsCfg} {ri : ℕ} (hri : ri < 4)
    (hB : (osBodyA c).all (fun s ↦ bodyOkS s || isLrCall s) = true) :
    (osBodyA c).all (SelOk osRate ri 4) = true := by
  refine List.all_eq_true.mpr fun s hs ↦ ?_
  have hf := List.all_eq_true.mp (osBodyA_flat c) s hs
  have hb := List.all_eq_true.mp hB s hs
  match s, hf, hb with
  | .atom _, _, _ => rfl
  | .call .., _, _ => rfl
  | .callIf .., _, _ => rfl
  | .dispatch x fs' a r, _, hb =>
    have hb' : bodyOkS (.dispatch x fs' a r) = true := by simpa [isLrCall] using hb
    obtain ⟨rfl, h4⟩ := bodyOkS_dispatch hb'
    simp [SelOk, selIs, h4, hri]
  | .match_ x arms, _, hb =>
    have hb' : bodyOkS (.match_ x arms) = true := by simpa [isLrCall] using hb
    obtain ⟨rfl, h4, hq⟩ := bodyOkS_match hb'
    simp [SelOk, selIs, h4, hq, hri]

/-- **Callees' trees by level don't depend on the valuation**, only on how many frames each level sets up. -/
theorem lvTs_osLvKOf (TA TS : Reader → Tree → Prop) (TB : ℕ → Reader → Tree → Prop) (rd : Reader) (σ σ' : Val)
    (c : OsCfg) : ∀ (l : ℕ) (lvs : List OsLv) (st : OsSt),
      lvTs TA TS TB rd l (osLvKOf σ' c l lvs st) = lvTs TA TS TB rd l (osLvKOf σ c l lvs st)
  | _, [], _ => rfl
  | l, lv :: rest, st => by
    simp only [osLvKOf, lvTs, lvK, List.map_map, List.map_append, List.map_cons, List.map_nil, Function.comp_def]
    rw [lvTs_osLvKOf TA TS TB rd σ σ' c (l + 1) rest]

theorem filterMap_callSF_length (σ σ' : Val) : ∀ l : List Stmt,
    (l.filterMap (Stmt.callSF σ')).length = (l.filterMap (Stmt.callSF σ)).length
  | [] => rfl
  | s :: l => by
    have ih := filterMap_callSF_length σ σ' l
    cases s <;> simp [List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, ih]

/-- **A dispatch on the rate's selector `g^ri`** enters the rate's row's callee. -/
theorem selName_rate {σ : Val} {m ri : ℕ} (hri : ri < 4)
    (hR : σ (.n osRate) = ofK (addressOfIndex ri)) (l : ℕ) (f : OsLv → String) :
    selName σ (osCfgR m ri) l f = f (osLvA (osCfgR m ri) l) := by
  have h4 : ri < ((osCfgR m ri).lvAt l).length := by rw [osCfgR_lvAt_length]; exact hri
  unfold selName
  rw [hR, logG_spec (by omega), List.getD_eq_getElem _ _ (by simpa using h4), List.getElem_map,
    ← List.getD_eq_getElem _ default h4, osCfgR_lvAt_getD l hri]

theorem bufL_mem_getD {b : ℕ} {sizes : List ℕ} {own : List (List E)}
    (hl : own.length = sizes.length) {j : ℕ} (hj : j < sizes.length) :
    ((bases b sizes).getD j 0, own.getD j []) ∈ bufL b sizes own := by
  have hjl : j < (bufL b sizes own).length := by
    rw [bufL, List.length_zip, os_length_bases, hl, Nat.min_self]; exact hj
  have e : (bufL b sizes own)[j] = ((bases b sizes).getD j 0, own.getD j []) := by
    simp only [bufL, List.getElem_zip]
    rw [List.getD_eq_getElem _ _ (by rw [os_length_bases]; exact hj),
      List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]
  rw [← e]
  exact List.getElem_mem hjl

/-- The frames after the levels: the closing rounds' and the finish's. -/
noncomputable def armRest (σ : Val) (c : OsCfg) : List Call :=
  ((osTlA c).filterMap Main.Stmt.callS).map (Main.mkCall σ) ++ (finFrames σ c).map (Main.mkCall σ)

/-- The arm's callees' predicates: within each bound, every callee's tree satisfying `armXT`, level `l`'s
`level_queries`' popping its honest entries (`osLvPops`), but `is_zero`'s. -/
noncomputable def armTs {Bd : Option (String → ℕ)} {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E}
    {tgt inn res : E} {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (σ : Val)
    (rd : Reader) : List (Tree → Prop) :=
  lvTs (bdT Bd armXT) (bdT Bd armXT)
    (lvTB Bd fun l rd t ↦ (t.name ≠ "is_zero" → t.pops coreProgram rd = osLvPops H l) ∧ armXT rd t) rd 0
    (osLvKOf σ c 0 c.levels (osHead c).2) ++ (armRest σ c).map fun _ ↦ bdT Bd armXT rd

/-- **The arm's callees' predicates don't depend on the valuation.** -/
theorem armTs_congr {Bd : Option (String → ℕ)} {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E}
    {tgt inn res : E} {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (σ σ' : Val)
    (rd : Reader) : armTs (Bd := Bd) H σ' rd = armTs (Bd := Bd) H σ rd := by
  unfold armTs
  rw [lvTs_osLvKOf _ _ _ rd σ σ' c 0 c.levels (osHead c).2, List.map_const', List.map_const']
  congr 2
  simp only [armRest, finFrames, List.length_append, List.length_map, filterMap_callSF_length σ σ']

/-- **The callees at a valuation agreeing on their arguments and returns.** -/
theorem kidsFromInT_congr {rd : Reader} {σ σ' : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (Dacc : ℕ → Prop) (b n : ℕ) (D : ℕ → Prop),
      (∀ c ∈ cs, c.args.map σ' = c.args.map σ ∧ c.rets.map σ' = c.rets.map σ) →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs Ts b n D → KidsFromInT coreProgram fs cert rd σ' R Dacc cs Ts b n D
  | [], _, _, _, _, _, _, h => h
  | c :: cs, Ts, _, _, _, _, hag, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ => by
    refine ⟨m, n', Rk, Dk, hn, hR, ?_, kidsFromInT_congr cs Ts.tail _ _ _ _
      (fun c' hc' ↦ hag c' (List.mem_cons_of_mem _ hc')) hk⟩
    obtain ⟨e1, e2⟩ := hag c List.mem_cons_self
    rw [e1, e2]
    exact hc

theorem lvTs_length (TA TS : Reader → Tree → Prop) (TB : ℕ → Reader → Tree → Prop) (rd : Reader) :
    ∀ (l : ℕ) (ks : List OsLvK), (lvTs TA TS TB rd l ks).length = (ks.flatMap OsLvK.calls).length
  | _, [] => rfl
  | l, k :: ks => by
    simp only [lvTs, List.flatMap_cons, OsLvK.calls, List.length_append, List.length_map, List.length_cons,
      lvTs_length TA TS TB rd (l + 1) ks]

/-- **Every predicate of `lvTs` implies `X`** when each of its three does. -/
theorem lvTs_imp {TA TS : Reader → Tree → Prop} {TB : ℕ → Reader → Tree → Prop} {rd : Reader} {X : Tree → Prop}
    (hA : ∀ t, TA rd t → X t) (hS : ∀ t, TS rd t → X t) (hB : ∀ l t, TB l rd t → X t) :
    ∀ (l : ℕ) (ks : List OsLvK), ∀ T ∈ lvTs TA TS TB rd l ks, ∀ t, T t → X t
  | _, [] => fun _ h' => by simp [lvTs] at h'
  | l, k :: ks => fun T hT t => by
    simp only [lvTs, List.mem_append, List.mem_map, List.mem_cons] at hT
    rcases hT with (⟨_, -, rfl⟩ | rfl | ⟨_, -, rfl⟩) | hT
    · exact hA t
    · exact hS t
    · exact hB l t
    · exact lvTs_imp hA hS hB (l + 1) ks T hT t

/-- **Within a bound, the arm's callees' trees satisfy `armXT`.** -/
theorem armTs_xt {Bk : String → ℕ} {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E}
    {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (σ : Val) (rd : Reader) :
    ∀ T ∈ armTs (Bd := some Bk) H σ rd, ∀ t, T t → armXT rd t := by
  intro T hT t ht
  rcases List.mem_append.mp hT with hT | hT
  · exact lvTs_imp (fun _ h ↦ h Bk rfl) (fun _ h ↦ h Bk rfl) (fun _ _ h ↦ (h Bk rfl).2) 0 _ T hT t ht
  · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hT
    exact ht Bk rfl

/-- **Callees' trees satisfying stronger predicates satisfy weaker ones.** -/
theorem kidsT_mono : ∀ {cs : List Call} {Ts Ts' : List (Tree → Prop)} {ks : List Tree},
    List.Forall₂ (fun T T' : Tree → Prop ↦ ∀ t, T t → T' t) Ts Ts' → KidsT cs Ts ks → KidsT cs Ts' ks
  | [], _, _, _, _, _ => trivial
  | _ :: _, _, _, [], .nil, _ => trivial
  | _ :: _, _, _, _ :: _, .nil, _ => trivial
  | _ :: _, _, _, [], .cons _ _, _ => trivial
  | _ :: _, _, _, _ :: _, .cons h hs, ⟨h1, h2⟩ => ⟨fun ht ↦ h _ (h1 ht), kidsT_mono hs h2⟩

theorem forall₂_map_same {α : Type} {R : (Tree → Prop) → (Tree → Prop) → Prop} {f g : α → Tree → Prop} :
    ∀ (l : List α), (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | x :: l, h => .cons (h x List.mem_cons_self) (forall₂_map_same l fun y hy ↦ h y (List.mem_cons_of_mem _ hy))

/-- **`lvTs` at stronger predicates is pointwise stronger.** -/
theorem lvTs_forall₂ {TA TS TA' TS' : Reader → Tree → Prop} {TB TB' : ℕ → Reader → Tree → Prop} {rd : Reader}
    (hA : ∀ t, TA rd t → TA' rd t) (hS : ∀ t, TS rd t → TS' rd t) (hB : ∀ l t, TB l rd t → TB' l rd t) :
    ∀ (l : ℕ) (ks : List OsLvK), List.Forall₂ (fun T T' : Tree → Prop ↦ ∀ t, T t → T' t)
      (lvTs TA TS TB rd l ks) (lvTs TA' TS' TB' rd l ks)
  | _, [] => .nil
  | l, k :: ks => by
    simp only [lvTs]
    exact List.rel_append (List.rel_append (forall₂_map_same _ fun _ _ ↦ hA)
      (.cons hS (forall₂_map_same _ fun _ _ ↦ hB l))) (lvTs_forall₂ hA hS hB (l + 1) ks)

/-- **An arm at a configuration and rate is complete placed**, at an optional words bound, by its node,
within each bound its levels' `level_queries` popping their honest entries. -/
theorem arm_completeAtO {Bd : Option (String → ℕ)} {m ri : ℕ} (hm : m < 11) (hri : ri < 4) (hκ : 11 ≤ κ)
    (htl : ∀ Bk ∈ Bd, ∀ f, fs (tailKey f) ≤ fs f)
    {name : String} {fn : Fn} (hfind : coreProgram.find? name = some fn)
    (hp : fn.params = osParams 11) (hb : fn.body = osBody (osCfgR m ri))
    (hnamed : ∀ f ∈ osCalleeNames (osCfgR m ri), ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)))
    (hnamedT : ∀ Bk ∈ Bd, ∀ f ∈ osCalleeNames (osCfgR m ri), ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtDTBR fs cert κ f L' args (Returns rets) armXT (Bk f))
    (hlp : ∀ l < (osCfgR m ri).levels.length, osPositionsName (osLvA (osCfgR m ri) l) ∈ osCalleeNames (osCfgR m ri) →
      LpAtOE fs cert κ (osPositionsName (osLvA (osCfgR m ri) l))
      (lpLoopA (osCfgR m ri) l) (osLvA (osCfgR m ri) l).squeezes (osLvA (osCfgR m ri) l).depth
      (osLvA (osCfgR m ri) l).capDepth (Bd.map (· (osPositionsName (osLvA (osCfgR m ri) l)))))
    (hlq : ∀ e ∈ lqTable, e.1 ∈ osCalleeNames (osCfgR m ri) →
      LqAtOP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1
      e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.2.2 (Bd.map (· e.1)))
    (hlr : ∀ j < (osCfgR m ri).yrLevel, osResidualName (osLvA (osCfgR m ri) j) ∈ osCalleeNames (osCfgR m ri) →
      LrAtOq fs cert κ (osResidualName (osLvA (osCfgR m ri) j))
      (osLvA (osCfgR m ri) j).logCols (osLvA (osCfgR m ri) j).folds (osLvA (osCfgR m ri) j).highBits
      (osLvA (osCfgR m ri) j).queries (Bd.map (· (osResidualName (osLvA (osCfgR m ri) j)))))
    (hls : ∀ j < (osCfgR m ri).yrLevel,
      osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) j) ∈ osCalleeNames (osCfgR m ri) →
      LsAtO fs cert κ (osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) j)) (osLvA (osCfgR m ri) j).queries
        (osLvA (osCfgR m ri) j).prefixLen (osCfgR m ri).yrLog (osLvA (osCfgR m ri) j).vanish
        (Bd.map (· (osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) j)))))
    {args : List E} (hargs : args.length = 11) (hsel0 : args.getD 0 0 = ofK (addressOfIndex ri))
    {cur tabs : E} {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA (osCfgR m ri) args cur tabs xs tgt inn res pt pt1) {Lin : Layout}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) :
    CompleteAtOT fs cert κ name Lin args
      (fun rets Lout ↦ ∃ b b1 : ℕ,
        rets = [tgt, ofK (addressOfIndex b), ofK (addressOfIndex b1), inn, res] ∧
          Lout = [(b, pt), (b1, pt1)])
      (Bd.map fun Bk ↦ osBos fs Bk name (osCfgR m ri))
      (FlatNodeT name fn (osBodyA (osCfgR m ri))
        (fun σ ↦ σ (.n osRate) = ofK (addressOfIndex ri) ∧ WinEx (osBodyA (osCfgR m ri)) σ)
        (armTs (Bd := Bd) H)) := by
  revert H
  set c := osCfgR m ri with hc
  intro H
  obtain ⟨hBall, hB, hffm, haddrs, hyr⟩ := armBody_ok ri hm
  have hLv : ∀ l < c.levels.length, LvFacts c l := armLv_ok hm hri
  have hsf : SlowFacts c := armSlow_ok hm hri
  have hl : H.own.length = (osSizesL c).length := H.own_len.length_eq
  have hSL := osSizesL_length (c := c) hyr.le
  have hbA : fn.body = osBodyA c ⧺ [.ret (osBodyRet c)] := hb.trans (osBody_eq c)
  have hloop : coreProgram.loop name = false := by
    obtain ⟨a, l, he⟩ : ∃ a l, osBodyRet c = a :: l := ⟨_, _, rfl⟩
    rw [Program.loop_of_find? hfind, Fn.loop, hbA, he]
    simp [List.reverse_append]
  have hjs : [osIxPtA c, osIxPt1A c].Nodup := by simp [osIxPtA, osIxPt1A]
  have hjl : ∀ j ∈ [osIxPtA c, osIxPt1A c], j < (osSizesL c).length := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp only [osIxPtA, osIxPt1A] <;> omega
  have hselB := selOk_body (c := c) hri hBall
  refine os_completeAt_placeR hfind hloop κ Lin args _ (Bd.map fun Bk ↦ osBos fs Bk name c) hbA osRate ri 4 hri
    (by norm_num) hselB haddrs (osSizesL c) [osIxPtA c, osIxPt1A c] hjs hjl (C := fun _ _ _ ↦ True) _ _
    fun fp ↦ ?_
  set b0 := fp + fs name with hb0
  obtain ⟨CV, hbody⟩ := H.body b0
  set Lk := osLkA c b0 H.own Lin with hLk
  -- the valuation on each memory holding the callees' words
  have hfl : ∀ s ∈ osBodyA c, ∀ x fs' a r, s = .dispatch x fs' a r → fs'.length < 2 ^ 64 - 1 := by
    intro s hs x fs' a r he
    subst he
    have hb' : bodyOkS (.dispatch x fs' a r) = true := by
      simpa [isLrCall] using List.all_eq_true.mp hBall _ hs
    have := (bodyOkS_dispatch hb').2
    omega
  have hσ : ∀ rd, LowDef κ rd → MemL rd Lk → ∃ σ : Val,
      σ (.n osRate) = ofK (addressOfIndex ri) ∧ fn.params.map σ = args ∧ (∀ s ∈ osBodyA c, DispOk σ s) ∧
      Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ Lk)) rd σ (osBodyA c) ∧
      OsOutA c b0 tabs tgt inn res H.own H.D σ ∧
      ((osBodyA c).filterMap Stmt.callVarsS).map (·.map σ) = CV ∧ OsLoadsIn c b0 H.own cur tabs xs σ ∧
      WinEx (osBodyA c) σ := by
    intro rd hlow hm
    obtain ⟨kEnd, f, hf⟩ := hbody rd (hlow.mono hκ)
    set σ := fill (Val.ofArgs args) 11 kEnd f with hσd
    obtain ⟨hA, hO, hCV, hLd, hWx⟩ := hf _ rd (osHA_of_lk hl hLin hlow hm) (fun _ _ ↦ rfl) σ (agree_fill _ _ _ _)
      (range_fill _ _ _ _)
    have hR : σ (.n osRate) = ofK (addressOfIndex ri) := by
      rw [hσd, fill_lt (by decide), ofArgs_n]; exact hsel0
    refine ⟨σ, hR, ?_, fun s hs ↦ ?_, hA, hO, hCV, hLd, hWx⟩
    · rw [hp]
      refine List.ext_getElem (by simp [osParams, hargs]) fun j h1 h2 ↦ ?_
      have hj : j < 11 := by simpa [osParams] using h1
      simp only [osParams, List.getElem_map, List.getElem_range]
      rw [hσd, fill_lt hj, ofArgs_n, List.getD_eq_getElem _ _ h2]
    · match s, hs with
      | .dispatch x fs' a r, hs =>
        have hb' : bodyOkS (.dispatch x fs' a r) = true := by
          simpa [isLrCall] using List.all_eq_true.mp hBall _ hs
        obtain ⟨hx, hl4⟩ := bodyOkS_dispatch hb'
        subst hx
        exact ⟨ri, by omega, by omega, hR⟩
      | .atom _, _ => trivial
      | .call .., _ => trivial
      | .callIf .., _ => trivial
      | .ite .., _ => trivial
      | .match_ .., _ => trivial
      | .ret _, _ => trivial
  -- `query_win_ptrs`, the levels' `level_positions` placed at `ps`
  set own' : List ℕ → List (List E) := fun ps ↦
    H.own.set osIxQbpA (qbpA c fun l ↦ winPtrsA fs cert c l (ps.getD l 0)) with hown'
  have hqb : (osSizesL c).getD osIxQbpA 0 = osPosTotal c := rfl
  have hfit : ∀ ps, List.Forall₂ (fun w s ↦ w.length ≤ s) (own' ps) (osSizesL c) := fun ps ↦
    forall₂_set (H.own_len.imp fun _ _ h ↦ le_of_eq h) (by rw [hqb, qbpA_length])
  have hgetD : ∀ ps j, j ≠ osIxQbpA → (own' ps).getD j [] = H.own.getD j [] := fun ps j hj ↦ by
    simp only [hown', List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]
  have hpt : H.own.getD (osIxPtA c) [] = pt := H.own_pt
  have hpt1 : H.own.getD (osIxPt1A c) [] = pt1 := H.own_pt1
  have hOut : ∀ ps, ∃ b b1 : ℕ,
      [tgt, osPtrA c b0 (osIxPtA c), osPtrA c b0 (osIxPt1A c), inn, res] =
        [tgt, ofK (addressOfIndex b), ofK (addressOfIndex b1), inn, res] ∧
      osLoutJ b0 (osSizesL c) (own' ps) [osIxPtA c, osIxPt1A c] = [(b, pt), (b1, pt1)] := fun ps ↦ by
    refine ⟨b0 + ((osSizesL c).take (osIxPtA c)).sum, b0 + ((osSizesL c).take (osIxPt1A c)).sum,
      ?_, ?_⟩
    · rw [osPtrA_eq, osPtrA_eq, baseA_eq c b0 (hjl _ (by simp)), baseA_eq c b0 (hjl _ (by simp))]
    · simp only [osLoutJ, List.map_cons, List.map_nil]
      rw [hgetD ps _ (by simp only [osIxPtA, osIxQbpA]; omega),
        hgetD ps _ (by simp only [osIxPt1A, osIxQbpA]; omega), hpt, hpt1]
  -- the body's statements on a memory, from its valuation there
  have hbodyAt : ∀ rd σ, Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ Lk)) rd σ (osBodyA c) →
      OsOutA c b0 tabs tgt inn res H.own H.D σ →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ fn.body False
        (fun r ↦ r = [tgt, osPtrA c b0 (osIxPtA c), osPtrA c b0 (osIxPt1A c), inn, res]) := by
    intro rd σ hA hO
    rw [hbA, holdsList_flat_ret _ (osBodyA_flat c)]
    exact ⟨os_allOk_mono (fun _ _ _ _ ↦ trivial) hA, hO.1⟩
  -- the loads, in the caller's words or the buffers
  have hloads : ∀ ps rd σ, LowDef κ rd → MemL rd Lk → OsLoadsIn c b0 H.own cur tabs xs σ →
      ∀ q ∈ (osBodyA c).filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧
        (RegionL Lin i ∨ RegionL (bufL b0 (osSizesL c) (own' ps)) i) := by
    intro ps rd σ hlow hm hLd q hq
    obtain ⟨v, hv⟩ := hLd q hq
    have hall : ∀ rd', LowDef κ rd' → MemL rd' Lk → rd' ((σ q.1).limb 0 * addressOfIndex q.2) = some v :=
      fun rd' hl' hm' ↦ by
        obtain ⟨g1, g2⟩ := hLin rd' hl' (memL_lin_of_lkA hm')
        exact (hv rd' g1 g2 (osMemA_of_lk hl hm')).2
    obtain ⟨i, hi, hR⟩ := os_addr_in_regionL hall hlow hm
    exact ⟨i, hi, regionL_osLkA hR⟩
  have hcalls := osBodyA_calls
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk
  swap
  · -- no memory holds the callees' words: every obligation on a memory is void
    refine ⟨own' [], [tgt, osPtrA c b0 (osIxPtA c), osPtrA c b0 (osIxPt1A c), inn, res], 0, [],
      fun _ ↦ False, [], hfit _, hOut _, fun q hq ↦ by simp at hq, disj_nil, ?_,
      fun rd hlow hBm hLin' ↦ absurd ⟨rd, hlow, memL_osLkA hBm hLin'⟩ hex⟩
    intro B hB'
    obtain ⟨Bk, -, rfl⟩ := Option.mem_map.mp hB'
    unfold osBos
    omega
  obtain ⟨rd0, hl0, hm0⟩ := hex
  obtain ⟨σ, hR, hparams, hdo, -, hO0, hCV0, -, -⟩ := hσ rd0 hl0 hm0
  have hHV : OsHelperVals c b0 tabs H.own H.D σ := hO0.2.2.2
  have hag : ∀ σ', ((osBodyA c).filterMap Stmt.callVarsS).map (·.map σ') = CV → CallAg (osBodyA c) σ' σ :=
    fun σ' h ↦ callAg_of_eq (h.trans hCV0.symm)
  have hall : ∀ rd, LowDef κ rd → MemL rd Lk → ∃ σ',
      Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ Lk)) rd σ' (osBodyA c) ∧ CallAg (osBodyA c) σ' σ :=
    fun rd hlow hm ↦
      let ⟨σ', _, _, _, hA, _, hCV, _, _⟩ := hσ rd hlow hm
      ⟨σ', hA, hag σ' hCV⟩
  have hsel : ∀ l (g : OsLv → String), selName σ c l g = g (osLvA c l) := selName_rate hri hR
  set ks := osLvKOf σ c 0 c.levels (osHead c).2 with hks
  set rest := ((osTlA c).filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
    (finFrames σ c).map (Main.mkCall σ) with hrest
  have hbound : ∀ N1 N2 : ℕ,
      (∀ Bk ∈ Bd, N1 ≤ ((ks.flatMap OsLvK.calls).map fun c' ↦ max (fs (tailKey c'.f)) (Bk c'.f)).sum) →
      (∀ Bk ∈ Bd, N2 ≤ (rest.map fun c' ↦ max (fs (tailKey c'.f)) (Bk c'.f)).sum) →
      ∀ B ∈ Bd.map (fun Bk ↦ osBos fs Bk name c), fs name + (osSizesL c).sum + (N1 + N2) ≤ B := by
    intro N1 N2 h1 h2 B hB'
    obtain ⟨Bk, hBk, rfl⟩ := Option.mem_map.mp hB'
    have hk := osKids_bound fs Bk hdo (σ := σ)
    have ht := sum_max_tailKey_le (htl Bk hBk) Bk (((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
    rw [hcalls] at hk ht
    simp only [← hks, ← hrest] at hk ht
    simp only [List.map_append, List.sum_append] at hk ht
    have := h1 Bk hBk
    have := h2 Bk hBk
    unfold osBos
    omega
  have hksl : ks.length = c.levels.length := osLvKOf_length σ c 0 c.levels _
  have hks_get : ∀ i (h : i < ks.length), ks[i] = lvK σ c i (osLvA c i) (osLvSt c i) := fun i h ↦ by
    have hi : i < c.levels.length := hksl ▸ h
    have e := osLvKOf_get σ c 0 c.levels (osHead c).2 i hi
    rw [Nat.zero_add, levels_getElem_eq hi] at e
    exact e
  -- the levels
  obtain ⟨N1, L1, ps, hps, hW1, hD1, hB1, hK1⟩ := os_levels_kidsOT (fs := fs) (cert := cert)
    (κ := κ) σ Lk (winW fs cert c b0) (runsS fs cert c H.D) Bd armXT armXT
    (fun l rd t ↦ (t.name ≠ "is_zero" → t.pops coreProgram rd = osLvPops H l) ∧ armXT rd t) ks 0
    (fun i hi ↦ by
      have hi' : i < c.levels.length := hksl ▸ hi
      rw [hks_get i hi, Nat.zero_add]
      exact arm_lv_ok H hLin hall hdo hfl hB ⟨rd0, hl0, hm0⟩ hHV hsel hyr hnamed hnamedT hlp hlq hi'
        (hLv i hi') fun c' hc' ↦ by
          rw [hcalls]
          refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem hi, ?_⟩)
          rw [hks_get i hi]
          exact hc')
    (b0 + (osSizesL c).sum)
  -- the closing rounds, `fold_final_msg`, the residuals
  obtain ⟨N2, L2, hW2, hD2, hB2, hK2⟩ := os_kids_blockOT (fs := fs) (cert := cert) (κ := κ) Lk σ
    rest Bd armXT (fun c' hc' ht ↦ arm_rest_ok H hall hdo hfl hB ⟨rd0, hl0, hm0⟩ hHV hsel hyr hLv hnamed
      hlr hffm hsf hls hc' (by rw [hcalls]; exact List.mem_append_right _ hc') ht)
    (fun Bk hBk c' hc' ht ↦ arm_rest_okT H hall hdo hfl hB ⟨rd0, hl0, hm0⟩ hHV hsel hyr hLv hnamed hnamedT
      hlr hffm hsf hls hBk hc' (by rw [hcalls]; exact List.mem_append_right _ hc') ht)
    (b0 + (osSizesL c).sum + N1)
  have hfit' := hfit ps
  refine ⟨own' ps, [tgt, osPtrA c b0 (osIxPtA c), osPtrA c b0 (osIxPt1A c), inn, res], N1 + N2,
    L1 ++ L2, fun _ ↦ False, ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ), hfit', hOut _, ?_,
    disj_append hD1 hD2 hW1 hW2 le_rfl, hbound N1 N2 hB1 hB2, fun rd hlow hBm hLin' ↦ ?_⟩
  · rw [within_append]
    exact ⟨hW1.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
  have hmk : MemL rd Lk := memL_osLkA hBm hLin'
  obtain ⟨σ', hR', hparams', hdo', hA', hO', hCV', hLd', hWx'⟩ := hσ rd hlow hmk
  have hag' := hag σ' hCV'
  refine ⟨σ', hR', ⟨hR', hWx'⟩, hparams', hdo', calls_congr hag', hbodyAt rd σ' hA' hO', hO'.2.1, hO'.2.2.1,
    hloads ps rd σ' hlow hmk hLd', fun hL ↦ ?_⟩
  -- the callees, at the memory's valuation
  have hcs : ∀ c' ∈ ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ),
      c'.args.map σ' = c'.args.map σ ∧ c'.rets.map σ' = c'.rets.map σ := fun c' hc' ↦ by
    obtain ⟨s, hs, vs, hv, ha, hr⟩ := call_vars_mem hc'
    exact ⟨List.map_inj_left.mpr fun v hv' ↦ callAg_v hag' hs hv (ha v hv'),
      List.map_inj_left.mpr fun v hv' ↦ callAg_v hag' hs hv (hr v hv')⟩
  rw [armTs_congr H σ σ' rd]
  -- the calls opaque, or unifying with the goal unfolds `KidsFromInT` over the body's calls
  generalize hcs0 : ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ) = cs at hcs ⊢
  refine kidsFromInT_congr _ _ _ _ _ _ hcs ?_
  subst hcs0
  have hL1 := (Main.memL_append.mp hL).1
  have hL2 := (Main.memL_append.mp hL).2
  have hRk : ∀ i, RegionL Lk i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs name) (osSizesL c) (own' ps)) i :=
    fun i hi ↦ regionL_osLkA hi
  have hl' : (own' ps).length = (osSizesL c).length := hfit'.length_eq
  have hqbW : (own' ps).getD osIxQbpA [] = qbpA c fun l ↦ winPtrsA fs cert c l (ps.getD l 0) := by
    have h10 : osIxQbpA < H.own.length := by rw [hl]; simp only [osIxQbpA]; omega
    simp [hown', List.getD_eq_getElem?_getD, h10]
  have hqbE : (baseA c b0 osIxQbpA, qbpA c fun l ↦ winPtrsA fs cert c l (ps.getD l 0)) ∈
      bufL b0 (osSizesL c) (own' ps) := by
    rw [← hqbW]
    exact bufL_mem_getD hl' (by simp only [osIxQbpA]; omega)
  rw [hcalls]
  unfold armTs
  refine kidsFromInT_append _ _ _ _ _ _ _ _ _ _ (lvTs_length _ _ _ rd 0 ks) (hK1 rd _ (fun _ ↦ False) hlow hL1
    hmk (fun i hi ↦ ?_) hRk (fun l _ hl2 p i hi ↦ ?_)) fun D1 _ ↦
      hK2 rd _ D1 hlow hL2 hmk fun i hi ↦ Or.inl (hRk i hi)
  · -- the window pointers, where `level_positions` was placed
    have hi' : i < c.levels.length := by rw [hps, hksl] at hi; exact hi
    have hrd := hBm _ hqbE
    dsimp only at hrd
    have := memL_qbp_slice (ws := fun l ↦ winPtrsA fs cert c l (ps.getD l 0)) hrd hi' (by
      show (winPtrsA fs cert c i (ps.getD i 0)).length ≤ osPosN c i
      rw [winPtrsA_length fs cert])
    rw [← (hLv i hi').2.2.2.1] at this
    rw [Nat.zero_add, winW_eq, ← List.getD_eq_getElem _ 0 hi]
    exact this
  · -- their region, wherever placed
    have hl3 : l < c.levels.length := by rw [hksl] at hl2; omega
    rw [winW_eq] at hi
    obtain ⟨x, hx, h1, h2⟩ := hi
    rw [List.mem_singleton] at hx
    subst hx
    simp only [winPtrsA_length] at h2
    have hS := posOff_add_lt (k := 0) hl3 (hLv l hl3).2.2.2.1
    have hS' := osPos_take_add_le hl3
    rw [← (hLv l hl3).2.2.2.1] at hS'
    refine Or.inr ⟨_, hqbE, ?_, ?_⟩
    · simp only at h1 ⊢; omega
    · simp only [qbpA_length] at h2 ⊢
      simp only [osPosN] at hS'
      omega

end
end LeanVM.Guest.B1.Arm
