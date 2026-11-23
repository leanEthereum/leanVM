/-
  LeanVM.Guest.B1.Place.ArmPops

  An arm of `open_stacked`'s node pops, within a bound, its levels' `level_queries` entries in order.
-/

module

public import LeanVM.Guest.B1.Place.ArmLift
public import LeanVM.Guest.B1.Place.ArmMuteAll

/-!
# An arm's pops

* `PopsBy rd cs Ts ps`: each entered callee's valid tree satisfying its predicate pops its entries, a skipped one's are `[]`; `popsKids_of_popsBy`: callees `KidsT` pop them;
* `popsBy_mute`: callees with no witness hint in their subtrees pop nothing; `popsBy_lvs`: the levels' callees pop, level by level, their `level_queries`' entries (`lvPss`), `is_zero` nothing;
* `armTsP`: `armTs`' part on the pops (`armTs_armTsP`); `arm_popsBy`: the arm's callees, classified by name (`armMute_all`, `lqNameB_of_kind`, `lqNameB_of_lp`, `lqNameB_of_lr`);
* `arm_pops`: the arm's node (`FlatNodeT`, its callees' trees of `armTs`), its body mute but for its calls (`splice_mute`), pops its levels' `osLvPops` in order.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **Callees' entries by their trees' predicates**: an entered callee's valid tree satisfying its predicate pops
its entries, a skipped one's are `[]`. -/
def PopsBy (rd : Reader) : List Call → List (Tree → Prop) → List (List Pop) → Prop
  | c :: cs, T :: Ts, p :: ps => (c.taken = true → ∀ t args rets, t.name = c.f →
      t.Valid coreProgram rd args rets → T t → t.pops coreProgram rd = p) ∧ (c.taken = false → p = []) ∧
      PopsBy rd cs Ts ps
  | [], [], [] => True
  | _, _, _ => False

theorem popsKids_of_popsBy {rd : Reader} {σ : Val} : ∀ {cs : List Call} {ks : List Tree}
    {Ts : List (Tree → Prop)} {ps : List (List Pop)}, Tree.KidsValid coreProgram rd σ cs ks → KidsT cs Ts ks →
    PopsBy rd cs Ts ps → Tree.popsKids coreProgram rd ks = ps
  | [], [], [], [], _, _, _ => rfl
  | c :: cs, k :: ks, T :: Ts, p :: ps, ⟨hn, hc, hks⟩, ⟨hT, hKT⟩, ⟨h1, h2, h3⟩ => by
    rw [Tree.popsKids, popsKids_of_popsBy hks hKT h3]
    refine congrArg (· :: ps) ?_
    by_cases ht : c.taken = true
    · rw [ite_eq_left ht] at hc
      exact h1 ht k _ _ hn hc (hT ht)
    · rw [ite_eq_right ht] at hc
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
      rw [Tree.pops, h2 (by simpa using ht)]
  | [], [], [], _ :: _, _, _, h | [], [], _ :: _, _, _, _, h => h.elim
  | _ :: _, _ :: _, [], _, _, _, h => h.elim
  | _ :: _, _ :: _, _ :: _, [], _, _, h => h.elim
  | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _ => h.elim

theorem popsBy_append {rd : Reader} : ∀ {cs1 cs2 : List Call} {Ts1 Ts2 : List (Tree → Prop)}
    {ps1 ps2 : List (List Pop)}, PopsBy rd cs1 Ts1 ps1 → PopsBy rd cs2 Ts2 ps2 →
    PopsBy rd (cs1 ++ cs2) (Ts1 ++ Ts2) (ps1 ++ ps2)
  | [], _, [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, _ :: _, _, ⟨a, b, h⟩, h2 => ⟨a, b, popsBy_append h h2⟩
  | [], _, [], _, _ :: _, _, h, _ | [], _, _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, _, [], _, _, _, h, _ | _ :: _, _, _ :: _, _, [], _, h, _ => h.elim

/-- **Callees with no witness hint in their subtrees pop nothing.** -/
theorem popsBy_mute {rd : Reader} : ∀ (cs : List Call), (∀ c ∈ cs, NoWitG c.f) →
    PopsBy rd cs (cs.map fun _ _ ↦ True) (cs.map fun _ ↦ [])
  | [], _ => trivial
  | c :: cs, h => ⟨fun _ _ _ _ hn hv _ ↦ pops_nil_of_noWitness (h c List.mem_cons_self) hv hn rd, fun _ ↦ rfl,
      popsBy_mute cs fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')⟩

/-- The levels' entries: level `l`'s calls before its positions and its positions nothing, its calls after them
`P l` each, but those not of `lqTable`, nothing. -/
def lvPss (P : ℕ → List Pop) : ℕ → List OsLvK → List (List Pop)
  | _, [] => []
  | l, k :: ks => (k.A.map fun _ ↦ []) ++ ([] :: k.B.map fun c ↦ if lqNameB c.f then P l else []) ++
      lvPss P (l + 1) ks

/-- A level's callees pop: those before its positions and its positions nothing, those after them of `lqTable`
`p` by `T`, the others nothing. -/
def LvPopsOk (rd : Reader) (T : Tree → Prop) (p : List Pop) (k : OsLvK) : Prop :=
  (∀ c ∈ k.A, NoWitG c.f) ∧ NoWitG k.sq.f ∧
    ∀ c ∈ k.B, (lqNameB c.f = false → NoWitG c.f) ∧
      (lqNameB c.f = true → c.taken = true ∧ ∀ t, t.name = c.f → T t → t.pops coreProgram rd = p)

theorem popsBy_after {rd : Reader} {T : Tree → Prop} {p : List Pop} : ∀ (cs : List Call),
    (∀ c ∈ cs, (lqNameB c.f = false → NoWitG c.f) ∧
      (lqNameB c.f = true → c.taken = true ∧ ∀ t, t.name = c.f → T t → t.pops coreProgram rd = p)) →
    PopsBy rd cs (cs.map fun _ ↦ T) (cs.map fun c ↦ if lqNameB c.f then p else [])
  | [], _ => trivial
  | c :: cs, h => by
    obtain ⟨hz, hp⟩ := h c List.mem_cons_self
    refine ⟨fun _ t _ _ hn hv hT ↦ ?_, fun hf ↦ ?_, popsBy_after cs fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')⟩
    · show t.pops coreProgram rd = if lqNameB c.f = true then p else []
      cases hq : lqNameB c.f
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact pops_nil_of_noWitness (hz hq) hv hn rd
      · simp only [↓reduceIte]
        exact (hp hq).2 t hn hT
    · show (if lqNameB c.f = true then p else []) = []
      cases hq : lqNameB c.f
      · simp
      · rw [(hp hq).1] at hf
        cases hf

/-- **The levels' callees pop their `level_queries`' entries**, level by level. -/
theorem popsBy_lvs {rd : Reader} (TB : ℕ → Reader → Tree → Prop) (P : ℕ → List Pop) :
    ∀ (ks : List OsLvK) (l : ℕ), (∀ i (h : i < ks.length), LvPopsOk rd (TB (l + i) rd) (P (l + i)) ks[i]) →
      PopsBy rd (ks.flatMap OsLvK.calls) (lvTs (fun _ _ ↦ True) (fun _ _ ↦ True) TB rd l ks) (lvPss P l ks)
  | [], _, _ => trivial
  | k :: ks, l, h => by
    obtain ⟨hA, hsq, hB⟩ := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hA hsq hB
    rw [List.flatMap_cons]
    refine popsBy_append (popsBy_append (popsBy_mute k.A hA)
      ⟨fun _ _ _ _ hn hv _ ↦ pops_nil_of_noWitness hsq hv hn rd, fun _ ↦ rfl, popsBy_after k.B hB⟩)
      (popsBy_lvs TB P ks (l + 1) fun i hi ↦ ?_)
    have := h (i + 1) (by simp; omega)
    simp only [List.getElem_cons_succ, show l + (i + 1) = l + 1 + i by omega] at this
    exact this

theorem flatten_map_ite (p : List Pop) (f : Call → Bool) : ∀ (B : List Call),
    (B.map fun c ↦ if f c then p else []).flatten = ((B.filter f).map fun _ ↦ p).flatten
  | [] => rfl
  | c :: B => by
    cases h : f c <;> simp [h, flatten_map_ite p f B]

theorem lvPss_flatten (P : ℕ → List Pop) : ∀ (ks : List OsLvK) (l : ℕ),
    (∀ k ∈ ks, (k.B.filter fun c ↦ lqNameB c.f).length = 1) →
    (lvPss P l ks).flatten = (List.range' l ks.length).flatMap P
  | [], _, _ => rfl
  | k :: ks, l, h => by
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (h k List.mem_cons_self)
    have e : (k.B.map fun c ↦ if lqNameB c.f then P l else []).flatten =
        ((k.B.filter fun c ↦ lqNameB c.f).map fun _ ↦ P l).flatten :=
      flatten_map_ite (P l) (fun c ↦ lqNameB c.f) k.B
    rw [hb] at e
    rw [lvPss, List.flatten_append, List.flatten_append, lvPss_flatten P ks (l + 1)
      fun k' hk' ↦ h k' (List.mem_cons_of_mem _ hk'), List.flatten_cons, e, List.length_cons, List.range'_succ,
      List.flatMap_cons]
    simp

/-- The arm's callees' entries: its levels' `level_queries`' honest entries, nothing else. -/
noncomputable def armPss {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E}
    {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (σ : Val) : List (List Pop) :=
  lvPss (osLvPops H) 0 (osLvKOf σ c 0 c.levels (osHead c).2) ++ (armRest σ c).map fun _ ↦ []

/-- **An arm's levels have one frame of `lqTable` after their positions**, at a valuation on the rate's selector:
`level_queries`', `is_zero`'s not. -/
theorem osLvKOf_B {m ri : ℕ} (hm : m < 11) (hri : ri < 4) {σ : Val}
    (hR : σ (.n osRate) = ofK (addressOfIndex ri)) :
    ∀ k ∈ osLvKOf σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2,
      (k.B.filter fun c ↦ lqNameB c.f).length = 1 := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  have hi' : i < (osCfgR m ri).levels.length := by rwa [osLvKOf_length] at hi
  have e := osLvKOf_get σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2 i hi'
  rw [Nat.zero_add, levels_getElem_eq hi'] at e
  rw [e]
  have hq : lqNameB (osQueriesName (osCfgR m ri) i (osLvA (osCfgR m ri) i)) = true :=
    List.any_eq_true.mpr ⟨_, (armLv_ok hm hri i hi').2.1, by simp⟩
  have h1 : ∀ s, ((lvIzF (osCfgR m ri) i (osLvA (osCfgR m ri) i) s).map
      (Main.mkCall σ)).filter (fun c ↦ lqNameB c.f) = [] := fun s ↦
    List.filter_eq_nil_iff.mpr fun c hc ↦ by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      rw [mkCall_f', lvIzF_f hx, lqNameB_of_kind osKindOf_isZero]
      simp
  simp only [lvK, List.filter_append, h1, List.nil_append, List.filter_cons, mkCall_f',
    selName_rate hri hR, hq, ↓reduceIte, List.filter_nil, List.length_singleton]

theorem armPss_flatten {m ri : ℕ} (hm : m < 11) (hri : ri < 4) {σ : Val}
    (hR : σ (.n osRate) = ofK (addressOfIndex ri)) {args : List E} {cur tabs : E} {xs : List E}
    {tgt inn res : E} {pt pt1 : List E} (H : OsHonestA (osCfgR m ri) args cur tabs xs tgt inn res pt pt1) :
    (armPss H σ).flatten = (List.range (osCfgR m ri).levels.length).flatMap (osLvPops H) := by
  rw [armPss, List.flatten_append, lvPss_flatten _ _ _ (osLvKOf_B hm hri hR), osLvKOf_length,
    ← List.range_eq_range']
  simp

/-- The arm's callees' predicates for their pops: within the bound `Bk`, level `l`'s `level_queries` popping its
honest entries. -/
noncomputable def armTsP (Bk : String → ℕ) {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E}
    {tgt inn res : E} {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (σ : Val)
    (rd : Reader) : List (Tree → Prop) :=
  lvTs (fun _ _ ↦ True) (fun _ _ ↦ True)
    (lvTB (some Bk) fun l rd t ↦ lqNameB t.name = true → t.pops coreProgram rd = osLvPops H l) rd 0
    (osLvKOf σ c 0 c.levels (osHead c).2) ++ (armRest σ c).map fun _ _ ↦ True

theorem armTs_armTsP {Bk : String → ℕ} {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E}
    {tgt inn res : E} {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (σ : Val)
    (rd : Reader) :
    List.Forall₂ (fun T T' : Tree → Prop ↦ ∀ t, T t → T' t) (armTs (Bd := some Bk) H σ rd) (armTsP Bk H σ rd) :=
  List.rel_append (lvTs_forall₂ (fun _ _ ↦ trivial) (fun _ _ ↦ trivial) (fun _ _ h B hB hq ↦ (h B hB).1
    fun he ↦ by rw [he, lqNameB_of_kind osKindOf_isZero] at hq; cases hq) 0 _)
    (forall₂_map_same _ fun _ _ _ _ ↦ trivial)

/-- **The arm's callees pop their levels' `level_queries`' honest entries**, at a valuation on the rate's
selector, classified by name. -/
theorem arm_popsBy {m ri : ℕ} (hm : m < 11) (hri : ri < 4) {σ : Val}
    (hR : σ (.n osRate) = ofK (addressOfIndex ri)) {Bk : String → ℕ} {args : List E} {cur tabs : E}
    {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA (osCfgR m ri) args cur tabs xs tgt inn res pt pt1) (rd : Reader) {cs : List Call}
    (hcs : cs = (osLvKOf σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2).flatMap OsLvK.calls ++
      armRest σ (osCfgR m ri))
    (hS : ∀ c' ∈ cs, armS c'.f = true) :
    PopsBy rd cs (armTsP Bk H σ rd) (armPss H σ) := by
  obtain ⟨-, hB, hffm, -, hyr⟩ := armBody_ok hm hri
  have hLv := armLv_ok hm hri
  subst hcs
  have hnw : ∀ c' ∈ (osLvKOf σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2).flatMap
      OsLvK.calls ++ armRest σ (osCfgR m ri), lqNameB c'.f = false → NoWitG c'.f := fun c' hc' hq ↦ by
    have := hS c' hc'
    simp only [armS, hq, Bool.false_or] at this
    exact noWitS_iff.mp this
  have hksl := osLvKOf_length σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2
  unfold armTsP armPss
  refine popsBy_append (popsBy_lvs _ _ _ 0 fun i hi ↦ ?_) (popsBy_mute _ fun c' hc' ↦
    hnw c' (List.mem_append_right _ hc') ?_)
  · have hi' : i < (osCfgR m ri).levels.length := hksl ▸ hi
    have hk : (osLvKOf σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2)[i] =
        lvK σ (osCfgR m ri) i (osLvA (osCfgR m ri) i) (osLvSt (osCfgR m ri) i) := by
      have e := osLvKOf_get σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2 i hi'
      rw [Nat.zero_add, levels_getElem_eq hi'] at e
      exact e
    have hmem : ∀ c' ∈ (lvK σ (osCfgR m ri) i (osLvA (osCfgR m ri) i) (osLvSt (osCfgR m ri) i)).calls,
        c' ∈ (osLvKOf σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2).flatMap OsLvK.calls ++
          armRest σ (osCfgR m ri) := fun c' h ↦
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hk ▸ List.getElem_mem hi, h⟩)
    rw [hk, Nat.zero_add]
    refine ⟨fun c' hc' ↦ hnw c' (hmem c' (List.mem_append_left _ hc')) ?_,
      hnw _ (hmem _ (List.mem_append_right _ List.mem_cons_self)) ?_, fun c' hc' ↦ ?_⟩
    · obtain ⟨K, hK⟩ := named_of_plain hB (fun s hs ↦ lvPre_sub_body hi' hs) hc'
      exact lqNameB_of_kind hK
    · show lqNameB (selName σ (osCfgR m ri) i osPositionsName) = false
      rw [selName_rate hri hR]
      exact lqNameB_of_lp (hLv i hi').1
    · refine ⟨hnw c' (hmem c' (List.mem_append_right _ (List.mem_cons_of_mem _ hc'))),
        fun hq ↦ ⟨?_, fun t hn ht ↦ ht Bk rfl (by rw [hn]; exact hq)⟩⟩
      rcases mem_lvK_B hc' with h | rfl
      · rw [h, lqNameB_of_kind osKindOf_isZero] at hq
        cases hq
      · rfl
  · rcases List.mem_append.mp hc' with hc | hc
    · obtain ⟨K, hK⟩ := named_of_plain hB (fun s hs ↦ tl_sub_body hs) hc
      exact lqNameB_of_kind hK
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    rcases mem_finFrames hx with rfl | hiz | ⟨j, hj, rfl | rfl⟩
    · obtain ⟨K, hK⟩ := Option.isSome_iff_exists.mp hffm
      exact lqNameB_of_kind hK
    · rw [mkCall_f', hiz]
      exact lqNameB_of_kind osKindOf_isZero
    · have hjy : j < (osCfgR m ri).yrLevel := by simpa [Nat.min_eq_left hyr.le] using hj
      show lqNameB (osResidualName (osLvA (osCfgR m ri) j)) = false
      exact lqNameB_of_lr ((hLv j (by omega)).2.2.1 hjy).1
    · have hjy : j < (osCfgR m ri).yrLevel := by simpa [Nat.min_eq_left hyr.le] using hj
      show lqNameB (selName σ (osCfgR m ri) j (osSlowName (osCfgR m ri))) = false
      rw [selName_rate hri hR]
      exact ((armSlow_ok hm hri).2 j hjy).2.2

/-- **An arm's node pops its levels' `level_queries`' honest entries in order**, within a bound. -/
theorem arm_pops {m ri : ℕ} (hm : m < 11) (hri : ri < 4) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hmu : Stmt.muteList armS fn.body = true) {Bk : String → ℕ}
    {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    {H : OsHonestA (osCfgR m ri) args cur tabs xs tgt inn res pt pt1} {rd : Reader} {t : Tree} {a r : List E}
    (hv : t.Valid coreProgram rd a r)
    (hT : FlatNodeT f fn (osBodyA (osCfgR m ri))
      (fun σ ↦ σ (.n osRate) = ofK (addressOfIndex ri) ∧ WinEx (osBodyA (osCfgR m ri)) σ) (armTs (Bd := some Bk) H) rd t) :
    t.pops coreProgram rd = (List.range (osCfgR m ri).levels.length).flatMap (osLvPops H) := by
  obtain ⟨σ, bufs, kids, es, vs, rfl, hw, hces, ⟨hR, -⟩, hK⟩ := hT
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := hv
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  rw [hw, Out.ret.injEq] at hw'
  obtain ⟨rfl, -⟩ := hw'
  have hm' : ∀ e ∈ es, Ev.Mute rd σ armS e := by
    have := walk_mute (rd := rd) (σ := σ) fn.body hmu
    rwa [hw] at this
  rw [Tree.pops_node hf hw, splice_mute es _ (fun e he ↦ (hm' e he).1)
    (by rw [length_popsKids, kidsValid_len hkv]),
    popsKids_of_popsBy hkv (kidsT_mono (armTs_armTsP H σ rd) hK)
      (arm_popsBy hm hri hR H rd (hces.trans (osBodyA_calls σ _)) (calls_mem_of_mute hm')),
    armPss_flatten hm hri hR]

end
end LeanVM.Guest.B1.Arm
