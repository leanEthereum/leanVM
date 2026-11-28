/-
  LeanVM.Guest.B1.VsC.Os.LeftPost

  `open_stacked`'s post: `OsPostHyp`, so `OpenStackedCompleteA` at every arm.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftAssembly
public import LeanVM.Guest.B1.VsC.Os.LeftQx
public import LeanVM.Guest.Complete.PopSkel
public import LeanVM.Guest.Memory.GuestWordsA

/-!
# `open_stacked`'s post

The node's path (`osBody_walk`, the same events as the node valuation's by `osBody_evs_congr`) pops
nothing itself (`osEvs_quiet`), so its entries are its callees' in call order
(`splice_quiet_flatten`). Every call is entered (`osBody_calls`), so `KidsPost` gives each callee's
post: `level_queries`' (`osLqPost`) pops its level's Merkle hints, every other pops nothing
(`PostQuiet`). Matched against `osLvPs` (the levels' lists) by `kOk_kids`, the concatenation is the
levels' hints, which `merkleHints true qs os` is level by level. Exactness: the path's by `WinEx`
(`osEvs_exact`), the callees' from their posts.

`osPostHyp : OsPostHyp k` for every `k`; `openStackedCompleteA_all`, `openStackedCompleteA_17`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

@[expose] public section

/-- **Events whose atoms pop nothing** splice their callees' entries in turn. -/
theorem splice_quiet_flatten {rd : Reader} {σ : Val} : ∀ (es : List Memory.Ev) (ks : List (List Pop)),
    (∀ a, Memory.Ev.atom a ∈ es → atomQuiet a = true) → ks.length = (calls es).length → splice rd σ es ks = ks.flatten
  | [], ks, _, h => by
    cases ks with
    | nil => rfl
    | cons k ks => simp [calls] at h
  | .atom a :: es, ks, ha, h => by
    rw [splice, splice_quiet_flatten es ks (fun b hb => ha b (List.mem_cons_of_mem _ hb)) (h.trans rfl)]
    have := ha a List.mem_cons_self
    cases a with
    | hint hh => cases hh <;> simp_all [atomQuiet, Atom.pops, Hint.pops]
    | _ => rfl
  | .inK _ :: es, ks, ha, h => by
    rw [splice]
    exact splice_quiet_flatten es ks (fun b hb => ha b (List.mem_cons_of_mem _ hb)) (h.trans rfl)
  | .call .. :: es, ks, ha, h | .skip .. :: es, ks, ha, h => by
    cases ks with
    | nil => simp [calls, Memory.Ev.call?] at h
    | cons k ks =>
      rw [splice, List.headD_cons, List.tail_cons, splice_quiet_flatten es ks
        (fun b hb => ha b (List.mem_cons_of_mem _ hb)) (by simpa [calls, Memory.Ev.call?] using h), List.flatten_cons]

theorem sameStreams_flatten : ∀ {ks Ps : List (List Pop)}, List.Forall₂ SameStreams ks Ps →
    SameStreams ks.flatten Ps.flatten
  | _, _, .nil => fun _ => rfl
  | _, _, .cons h hs => by
    rw [List.flatten_cons, List.flatten_cons]
    exact SameStreams.append h (sameStreams_flatten hs)

theorem osForall₂_append {α β : Type _} {R : α → β → Prop} {a c : List α} {b d : List β}
    (h : List.Forall₂ R a b) (h' : List.Forall₂ R c d) : List.Forall₂ R (a ++ c) (b ++ d) := by
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact .cons hab ih

theorem osForall₂_flatMap {α β γ : Type _} {R : β → γ → Prop} {f : α → List β} {g : α → List γ} :
    ∀ (l : List α), (∀ x ∈ l, List.Forall₂ R (f x) (g x)) → List.Forall₂ R (l.flatMap f) (l.flatMap g)
  | [], _ => .nil
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact osForall₂_append (h x List.mem_cons_self) (osForall₂_flatMap l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem osForall₂_map {α β γ : Type _} {R : β → γ → Prop} {f : α → β} {g : α → γ} (h : ∀ x, R (f x) (g x)) :
    ∀ (l : List α), List.Forall₂ R (l.map f) (l.map g)
  | [] => .nil
  | x :: l => .cons (h x) (osForall₂_map h l)

theorem flatten_flatMap' {α β : Type _} (f : α → List (List β)) :
    ∀ l : List α, (l.flatMap f).flatten = l.flatMap fun x => (f x).flatten
  | [] => rfl
  | x :: l => by rw [List.flatMap_cons, List.flatten_append, flatten_flatMap' f l, List.flatMap_cons]

/-- **Callees all entered**, each post giving its list: `KOk`. -/
theorem kOk_taken {rd : Reader} {Qs : List (Reader → Tree → Prop)} {Ps : List (List Pop)}
    (h : List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) Qs Ps) :
    ∀ {cs : List Call}, Qs.length = cs.length → (∀ c ∈ cs, c.taken = true) → KOk rd Qs (cs.map Call.taken) Ps := by
  induction h with
  | nil =>
    intro cs hl _
    cases cs with
    | nil => simp [KOk]
    | cons => simp at hl
  | cons hQ _ ih =>
    intro cs hl ht
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      rw [List.map_cons]
      exact ⟨fun _ => hQ, fun hf => absurd (ht c List.mem_cons_self) (by rw [hf]; simp),
        ih (by simpa using hl) fun c' hc' => ht c' (List.mem_cons_of_mem _ hc')⟩

/-- Level `l`'s callees' lists: `level_queries`' the level's Merkle hints, the others' empty. -/
def osLvPs (c : OsCfg) (os : List (List Opening)) (l : ℕ) : List (List Pop) :=
  if l = c.yrLevel then [[], [], Hints.levelHints (l == 0) (osLvA c l).depth (os.getD l []).length (os.getD l [])]
  else [[], [], [], [], Hints.levelHints (l == 0) (osLvA c l).depth (os.getD l []).length (os.getD l [])]

theorem osLvPs_flatten (c : OsCfg) (os : List (List Opening)) (l : ℕ) :
    (osLvPs c os l).flatten = Hints.levelHints (l == 0) (osLvA c l).depth (os.getD l []).length (os.getD l []) := by
  unfold osLvPs
  split_ifs <;> simp

theorem postQuiet_pops {rd : Reader} {t : Tree} (h : PostQuiet rd t) : PopsPost [] rd t :=
  ⟨by rw [h.1]; exact fun _ => rfl, h.2⟩

theorem osLv_forall₂ (rd : Reader) (c : OsCfg) (os : List (List Opening)) (l : ℕ) :
    List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) (osLvQs c os l) (osLvPs c os l) := by
  unfold osLvQs osLvPs
  split_ifs
  · exact .cons (fun _ => postQuiet_pops) (.cons (fun _ => postQuiet_pops) (.cons (fun _ h => h) .nil))
  · exact .cons (fun _ => postQuiet_pops) (.cons (fun _ => postQuiet_pops) (.cons (fun _ => postQuiet_pops)
      (.cons (fun _ => postQuiet_pops) (.cons (fun _ h => h) .nil))))

theorem callMatches_taken {c : Call} {s : String × Option (List V × List V)} (h : callMatches c s = true) :
    c.taken = true := by
  obtain ⟨f, o⟩ := s
  cases o with
  | none => exact (callMatches_none h).2
  | some p => obtain ⟨a, r⟩ := p; rw [callMatches_some h]

set_option linter.constructorNameAsVariable false in
/-- **The node's post at the arm `m` and rate index `ri`**, from its valuation's walk and windows and
its callees' posts `osNodeQs`. -/
theorem osNode_post {m ri : ℕ} (hm : m < 15) (hri : ri < 4) {C : CallRel} {os : List (List Opening)}
    {rd : Reader} {σ0 σ : Val} {ts : List Memory.Tree} (bufs : List ℕ)
    (h0 : logG (σ0 (.n osRate)) = ri) (hsel : σ (.n osRate) = σ0 (.n osRate))
    (hok : AllOk C rd σ (osBodyA (osCfgR m ri))) (hwx : WinEx (osBodyA (osCfgR m ri)) σ)
    (hkv : Tree.KidsValid coreProgram rd σ (calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ0))) ts)
    (hkp : KidsPost rd (osNodeQs (osCfgR m ri) os (calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ0))))
      (calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ0))) ts) :
    SameStreams ((Memory.Tree.node (openName (minOpenLog + m)) σ bufs ts).pops coreProgram rd)
        ((List.range (osCfgR m ri).levels.length).flatMap fun l =>
          Hints.levelHints (l == 0) (osLvA (osCfgR m ri) l).depth (os.getD l []).length (os.getD l [])) ∧
      (Memory.Tree.node (openName (minOpenLog + m)) σ bufs ts).Every (ExactAt coreProgram rd) := by
  obtain ⟨fn, hfind, -, hbody, -⟩ := os_fn hm
  have hes := osBody_evs_congr (ri := ri) hm hsel
  have hx := osEvs_exact hm hwx rd
  have hwk := (osBody_walk hm hok).1
  rw [hes] at hwk hx
  rw [← hbody] at hwk
  have hcm := osBody_calls hm hri h0
  have htk : ∀ c' ∈ calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ0)), c'.taken = true :=
    forall₂_mem_left hcm fun _ _ _ _ h => callMatches_taken h
  rw [osCallSpec_eq] at hcm
  obtain ⟨cl1, cl2, hcl, f1, f2⟩ := forall₂_append_split _ _ hcm
  have hq : osNodeQs (osCfgR m ri) os (calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ0))) =
      (List.range (osCfgR m ri).levels.length).flatMap (osLvQs (osCfgR m ri) os) ++ cl2.map fun _ => PostQuiet := by
    rw [osNodeQs, hcl, List.drop_left' f1.length_eq]
  have hF : List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t)
      (osNodeQs (osCfgR m ri) os (calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ0))))
      ((List.range (osCfgR m ri).levels.length).flatMap (osLvPs (osCfgR m ri) os) ++ cl2.map fun _ => []) := by
    rw [hq]
    exact osForall₂_append (osForall₂_flatMap _ fun l _ => osLv_forall₂ rd _ os l)
      (osForall₂_map (fun _ _ => postQuiet_pops) cl2)
  have hlen : (osNodeQs (osCfgR m ri) os (calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ0)))).length =
      (calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ0))).length := by
    rw [hq, hcl, List.length_append, List.length_append, osLvsQs_length, List.length_map, f1.length_eq]
  have hK := kOk_taken hF hlen htk
  -- `hkv`'s and `hkp`'s types only match reducibly: at default transparency the check unfolds too far.
  have h2 := by with_reducible exact kOk_kids hK hkv hkp
  obtain ⟨hFS, hEv⟩ := h2
  have hsp : (Memory.Tree.node (openName (minOpenLog + m)) σ bufs ts).pops coreProgram rd =
      (Tree.popsKids coreProgram rd ts).flatten := by
    rw [Tree.pops_node (P := coreProgram) hfind hwk]
    exact splice_quiet_flatten _ _ (osEvs_quiet hm) (by rw [hFS.length_eq, ← hF.length_eq, hlen])
  have hPs : ((List.range (osCfgR m ri).levels.length).flatMap (osLvPs (osCfgR m ri) os) ++
      cl2.map fun _ => ([] : List Pop)).flatten =
      (List.range (osCfgR m ri).levels.length).flatMap fun l =>
        Hints.levelHints (l == 0) (osLvA (osCfgR m ri) l).depth (os.getD l []).length (os.getD l []) := by
    have h2 : (cl2.map fun _ => ([] : List Pop)).flatten = [] := by simp
    rw [List.flatten_append, flatten_flatMap', h2, List.append_nil]
    simp only [osLvPs_flatten]
  refine ⟨?_, ?_⟩
  · rw [hsp, ← hPs]
    exact sameStreams_flatten hFS
  · rw [Tree.every_node]
    exact ⟨exactAt_of_walk hfind hwk hx, hEv⟩

set_option linter.constructorNameAsVariable false in
/-- **`open_stacked`'s post.** -/
theorem osPostHyp (k : ℕ) : OsPostHyp k := by
  intro μ r target S root xs os w cfg Ls hR qs hmh ic it c σ0 rd0 hb0 rd σ ts _ _ hb _ hkv hkp
  have hm := hR.m11
  have hr := hR.r4
  have hri : logG (σ0 (.n osRate)) = r - 1 := by
    have h1 := hb0.1 0 (by omega)
    have e : Val.ofArgs (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, ptrAt ic,
        ptrAt it]) (.n 0) = rateSel r := rfl
    have h0 : σ0 (.n 0) = rateSel r := h1.trans e
    show logG (σ0 (.n 0)) = r - 1
    rw [h0]
    exact logG_spec (by omega)
  have hsel : σ (.n osRate) = σ0 (.n osRate) := by
    show σ (.n 0) = σ0 (.n 0)
    rw [hb.1 0 (by omega), hb0.1 0 (by omega)]
  have hok := hb.2.1
  have hwx := hb.2.2.2.2
  rw [hmh]
  with_reducible exact osNode_post hm hr _ hri hsel hok hwx hkv hkp

/-- **`open_stacked` completes placed at every arm**, at every allocator flag and `11 ≤ k`. -/
theorem openStackedCompleteA_all (al : String → Bool) {k : ℕ} (hk : 11 ≤ k) :
    ∀ m, m ≤ 14 → OpenStackedCompleteA B2C.fs al B2C.cert k m :=
  openStackedCompleteA_of_post hk (osPostHyp k)

/-- **`GuestLeft.openStacked`.** -/
theorem openStackedCompleteA_17 : ∀ m, m ≤ 14 → OpenStackedCompleteA B2C.fs alW B2C.cert 17 m :=
  openStackedCompleteA_all alW (by norm_num)

end
end LeanVM.Guest.B1.VsC
