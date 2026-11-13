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
* `popsBy_mute`: callees with no witness hint in their subtrees pop nothing; `popsBy_lvs`: the levels' callees pop, level by level, their `level_queries`' entries (`lvPss`);
* `arm_popsBy`: the arm's callees, classified by name (`armMute_all`, `lqNameB_of_kind`, `lqNameB_of_lp`, `lqNameB_of_lr`);
* `arm_pops`: the arm's node (`FlatNodeT`), its body mute but for its calls (`splice_mute`), pops its levels' `osLvPops` in order.
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
`P l` each. -/
def lvPss (P : ℕ → List Pop) : ℕ → List OsLvK → List (List Pop)
  | _, [] => []
  | l, k :: ks => (k.A.map fun _ ↦ []) ++ ([] :: k.B.map fun _ ↦ P l) ++ lvPss P (l + 1) ks

/-- A level's callees pop: those before its positions and its positions nothing, those after them `p` by `T`. -/
def LvPopsOk (rd : Reader) (T : Tree → Prop) (p : List Pop) (k : OsLvK) : Prop :=
  (∀ c ∈ k.A, NoWitG c.f) ∧ NoWitG k.sq.f ∧
    ∀ c ∈ k.B, c.taken = true ∧ ∀ t, T t → t.pops coreProgram rd = p

theorem popsBy_after {rd : Reader} {T : Tree → Prop} {p : List Pop} : ∀ (cs : List Call),
    (∀ c ∈ cs, c.taken = true ∧ ∀ t, T t → t.pops coreProgram rd = p) →
    PopsBy rd cs (cs.map fun _ ↦ T) (cs.map fun _ ↦ p)
  | [], _ => trivial
  | c :: cs, h => by
    obtain ⟨ht, hp⟩ := h c List.mem_cons_self
    refine ⟨fun _ t _ _ _ _ hT ↦ hp t hT, fun hf ↦ ?_, popsBy_after cs fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')⟩
    rw [ht] at hf
    cases hf

/-- **The levels' callees pop their `level_queries`' entries**, level by level. -/
theorem popsBy_lvs {rd : Reader} (TB : ℕ → Reader → Tree → Prop) (P : ℕ → List Pop) :
    ∀ (ks : List OsLvK) (l : ℕ), (∀ i (h : i < ks.length), LvPopsOk rd (TB (l + i) rd) (P (l + i)) ks[i]) →
      PopsBy rd (ks.flatMap OsLvK.calls) (lvTs TB rd l ks) (lvPss P l ks)
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

theorem lvPss_flatten (P : ℕ → List Pop) : ∀ (ks : List OsLvK) (l : ℕ), (∀ k ∈ ks, k.B.length = 1) →
    (lvPss P l ks).flatten = (List.range' l ks.length).flatMap P
  | [], _, _ => rfl
  | k :: ks, l, h => by
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (h k List.mem_cons_self)
    rw [lvPss, List.flatten_append, List.flatten_append, lvPss_flatten P ks (l + 1)
      fun k' hk' ↦ h k' (List.mem_cons_of_mem _ hk'), hb, List.length_cons, List.range'_succ, List.flatMap_cons]
    simp

theorem osLvKOf_B (σ : Val) (c : OsCfg) : ∀ (l : ℕ) (lvs : List OsLv) (s : OsSt),
    ∀ k ∈ osLvKOf σ c l lvs s, k.B.length = 1
  | _, [], _ => fun _ h ↦ by simp [osLvKOf] at h
  | l, lv :: rest, s => fun k hk ↦ by
    rw [osLvKOf, List.mem_cons] at hk
    rcases hk with rfl | hk
    · rfl
    · exact osLvKOf_B σ c (l + 1) rest _ k hk

/-- The arm's callees' entries: its levels' `level_queries`' honest entries, nothing else. -/
noncomputable def armPss {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E}
    {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (σ : Val) : List (List Pop) :=
  lvPss (osLvPops H) 0 (osLvKOf σ c 0 c.levels (osHead c).2) ++ (armRest σ c).map fun _ ↦ []

theorem armPss_flatten {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E}
    {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (σ : Val) :
    (armPss H σ).flatten = (List.range c.levels.length).flatMap (osLvPops H) := by
  rw [armPss, List.flatten_append, lvPss_flatten _ _ _ (osLvKOf_B σ c 0 _ _), osLvKOf_length,
    ← List.range_eq_range']
  simp

/-- **The arm's callees pop their levels' `level_queries`' honest entries**, at a valuation on the rate's
selector, classified by name. -/
theorem arm_popsBy {m ri : ℕ} (hm : m < 11) (hri : ri < 4) {σ : Val}
    (hR : σ (.n osRate) = ofK (addressOfIndex ri)) {Bk : String → ℕ} {args : List E} {cur tabs : E}
    {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA (osCfgR m ri) args cur tabs xs tgt inn res pt pt1) (rd : Reader) {cs : List Call}
    (hcs : cs = (osLvKOf σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2).flatMap OsLvK.calls ++
      armRest σ (osCfgR m ri))
    (hS : ∀ c' ∈ cs, armS c'.f = true) :
    PopsBy rd cs (armTs (Bd := some Bk) H σ rd) (armPss H σ) := by
  obtain ⟨hB, -, hyr⟩ := armBody_ok ri hm
  have hLv := armLv_ok hm hri
  subst hcs
  have hnw : ∀ c' ∈ (osLvKOf σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2).flatMap
      OsLvK.calls ++ armRest σ (osCfgR m ri), lqNameB c'.f = false → NoWitG c'.f := fun c' hc' hq ↦ by
    have := hS c' hc'
    simp only [armS, hq, Bool.false_or] at this
    exact noWitS_iff.mp this
  have hksl := osLvKOf_length σ (osCfgR m ri) 0 (osCfgR m ri).levels (osHead (osCfgR m ri)).2
  unfold armTs armPss
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
    · simp only [lvK, List.mem_singleton] at hc'
      subst hc'
      exact ⟨rfl, fun t ht ↦ ht Bk rfl⟩
  · rcases List.mem_append.mp hc' with hc | hc
    · obtain ⟨K, hK⟩ := named_of_plain hB (fun s hs ↦ tl_sub_body hs) hc
      exact lqNameB_of_kind hK
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    rcases mem_finFrames hx with rfl | ⟨j, hj, rfl⟩
    · obtain ⟨K, hK⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hB _ (ffm_mem_body (osCfgR m ri)))
      exact lqNameB_of_kind hK
    · have hjy : j < (osCfgR m ri).yrLevel := by simpa [Nat.min_eq_left hyr.le] using hj
      show lqNameB (selName σ (osCfgR m ri) j osResidualName) = false
      rw [selName_rate hri hR]
      exact lqNameB_of_lr ((hLv j (by omega)).2.2.1 hjy)

/-- **An arm's node pops its levels' `level_queries`' honest entries in order**, within a bound. -/
theorem arm_pops {m ri : ℕ} (hm : m < 11) (hri : ri < 4) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hmu : Stmt.muteList armS fn.body = true) {Bk : String → ℕ}
    {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    {H : OsHonestA (osCfgR m ri) args cur tabs xs tgt inn res pt pt1} {rd : Reader} {t : Tree} {a r : List E}
    (hv : t.Valid coreProgram rd a r)
    (hT : FlatNodeT f fn (osBodyA (osCfgR m ri)) (fun σ ↦ σ (.n osRate) = ofK (addressOfIndex ri))
      (armTs (Bd := some Bk) H) rd t) :
    t.pops coreProgram rd = (List.range (osCfgR m ri).levels.length).flatMap (osLvPops H) := by
  obtain ⟨σ, bufs, kids, es, vs, rfl, hw, hces, hR, hK⟩ := hT
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
    popsKids_of_popsBy hkv hK (arm_popsBy hm hri hR H rd (hces.trans (osBodyA_calls σ _)) (calls_mem_of_mute hm')),
    armPss_flatten]

end
end LeanVM.Guest.B1.Arm
