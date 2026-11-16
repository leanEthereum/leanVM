/-
  LeanVM.Guest.Backend.Complete.ProgFrames

  Every running instance's frame of the honest memory at the back end's data holds what its
  function's frame family asks (`FrameOK`), its callees' frames included.
-/

module

public import LeanVM.Guest.Backend.Complete.ProgJt
public import LeanVM.Guest.Backend.Complete.PathRun
public import LeanVM.Guest.Backend.Complete.FrameWordsDone

/-!
# The frames of the honest memory

`FHB W`: an instance of `f` at frame `fp` holds the frame its placement's frame family `famB`
asks (`FrameOK`), and its `frameAddr`s point at their cells. `famB_ok`: under the per-function
conditions, `famB` is a frame family `FrameConsistentStmt` gives (`frameConsistent_of_words
frameWords`). `frame_honestB`: on the honest memory at the back end's data, every running
instance holds `FHB`: its own cells are the family's words, its header the caller's `hdrB` (of
`K` but for `main`), each callee's frame its header, its arguments (a running callee's family
words at its parameters' cells, a phantom's written ones) and a registered loop helper's own
pointer, and a loop helper's last callee frame right after its own.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **What an instance's frame holds** at the back end's data. -/
def FHB {κ₀ : ℕ} (W : World κ₀) : FrameP := fun L f fp σ es _vs kfps hdr =>
  ∃ tf pf, W.fnOf f = some (tf, pf) ∧
    FrameOK L (loopTable W.p) tf pf.fn.frameSize fp (W.famB tf pf fp kfps hdr σ) σ es kfps hdr ∧
    (∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0)))

section

variable {κ₀ : ℕ} {W : World κ₀}

/-- **The frame family of the back end's data is one `FrameConsistentStmt` gives.** -/
theorem famB_ok (hW : W.Compiled) {tf : TracedFn} (htf : tf ∈ W.p) (hC : FnConds W tf)
    {pf : Placed} (hpa : World.PlacedAs W tf pf) {fp : ℕ} (hfp : tf.core.name = "main" → fp = 0)
    (kfps : List ℕ) (hdr : E × E) : FSOk W tf pf fp kfps hdr (W.famB tf pf fp kfps hdr) := by
  have hex : ∃ FS, FSOk W tf pf fp kfps hdr FS :=
    frameConsistent_of_words frameWords W hW tf htf hC.isScoped pf hpa (hC.tmps pf hpa) hC.noSelf
      fp hfp kfps hdr
  unfold World.famB
  split
  · next h => exact Classical.choose_spec h
  · next h => exact absurd hex h

theorem addr_add (a b : ℕ) : addressOfIndex (a + b) = addressOfIndex a * addressOfIndex b := by
  simp only [addressOfIndex, pow_add]

/-- The events of a running instance are its path's. -/
theorem events_node {I : Memory.Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {fn : Fn} (hf : W.core.find? f = some fn) {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) : I.t.events W.core = es := by
  unfold Tree.events
  rw [ht]
  simp only [Tree.name, Tree.val, hf, hw]

mutual
theorem insts_hdrB : ∀ (t : Tree) (fp : ℕ) (h : E × E),
    ∀ J ∈ t.insts W.fsB W.core.loop W.hdrB fp h, J.hdr = h ∨ (IsInK J.hdr.1 ∧ IsInK J.hdr.2)
  | .node f σ bufs kids, fp, h, J, hJ => by
      rw [insts_node, List.mem_cons] at hJ
      rcases hJ with rfl | hJ
      · exact Or.inl rfl
      · exact Or.inr (instsKids_hdrB kids _ _ 0 J hJ)
  | .phantom .., fp, h, J, hJ => by
      rw [insts_phantom, List.mem_singleton] at hJ
      subst hJ; exact Or.inl rfl

theorem instsKids_hdrB : ∀ (ks : List Tree) (ps : List ℕ) (I : Memory.Inst) (i : ℕ),
    ∀ J ∈ Tree.instsKids W.fsB W.core.loop W.hdrB I i ps ks, IsInK J.hdr.1 ∧ IsInK J.hdr.2
  | [], _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, [], _, _, J, hJ => by rw [instsKids_nil_left] at hJ; exact absurd hJ List.not_mem_nil
  | k :: ks, p :: ps, I, i, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · rcases insts_hdrB k p (W.hdrB I i) J hJ with he | hk
        · rw [he]; exact hdrB_K I i
        · exact hk
      · exact instsKids_hdrB ks ps I (i + 1) J hJ
end

/-- **Every instance but `main`'s has a header of `K`.** -/
theorem honest_hdrB {hdr : E × E} {T : Tree} (hT : T.name = "main") {J : Memory.Inst}
    (hJ : J ∈ honestInsts W.core W.fsB W.hdrB hdr T) (hn : J.t.name ≠ "main") :
    IsInK J.hdr.1 ∧ IsInK J.hdr.2 := by
  unfold honestInsts at hJ
  cases T with
  | phantom f σ =>
    rw [insts_phantom, List.mem_singleton] at hJ
    subst hJ; exact absurd hT hn
  | node f σ bufs kids =>
    rw [insts_node, List.mem_cons] at hJ
    rcases hJ with rfl | hJ
    · exact absurd hT hn
    · exact instsKids_hdrB kids _ _ 0 J hJ

/-- A placed frame fits the layout's. -/
theorem frame_le_fsB (hW : W.Compiled) {tf : TracedFn} {pf : Placed} (htf : tf ∈ W.p)
    (hpa : World.PlacedAs W tf pf) : pf.fn.frameSize ≤ W.fsB tf.core.name := by
  by_cases hm : tf.core.name = "main"
  · have := (fsB_main hW hpa hm).2
    rw [hm, this]
    omega
  · rw [fsB_fn hW htf hpa hm]

/-- **A running instance's own cells hold its frame family's words.** -/
theorem own_cell (hW : W.Compiled) {hdr : E × E} {rd : Reader} {T : Tree}
    (hH : HonestAt W.core W.fsB W.hdrB W.cellsB hdr T W.cellB rd [] [])
    {I : Memory.Inst} (hI : I ∈ honestInsts W.core W.fsB W.hdrB hdr T) {σ : Val} {bufs : List ℕ}
    {kids : List Tree} {tf : TracedFn} {pf : Placed} (htf : tf ∈ W.p)
    (ht : I.t = .node tf.core.name σ bufs kids) (hfo : W.fnOf tf.core.name = some (tf, pf))
    (hpa : World.PlacedAs W tf pf) {n : ℕ} (h2 : 2 ≤ n) (hn : n < pf.fn.frameSize) :
    (W.honestB hdr T).read (addressOfIndex (I.fp + n)) =
      some ((W.famB tf pf I.fp I.kidFps I.hdr σ).Ψ n) := by
  have hle := frame_le_fsB hW htf hpa
  have hc : (n, (W.famB tf pf I.fp I.kidFps I.hdr σ).Ψ n) ∈ W.cellsB I := by
    rw [cellsB_node ht hfo]
    refine mem_frameB (List.mem_append_left _ (List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩))
      h2 (by simp only; omega) fun q' hq' he => ?_
    rcases List.mem_append.mp hq' with hq' | hq'
    · obtain ⟨n', -, rfl⟩ := List.mem_map.mp hq'
      simp only at he
      subst he
      rfl
    · split at hq'
      · next hm =>
        obtain ⟨s, -, hs, -⟩ := tableB_off hq'
        have := (fsB_main hW hpa hm).1
        simp only at he
        omega
      · exact absurd hq' List.not_mem_nil
  have := hH.toHonest.read_C hI hc
  rwa [← addr_add] at this

/-- A phantom's written cells. -/
theorem phantom_cell {hdr : E × E} {rd : Reader} {T : Tree}
    (hH : HonestAt W.core W.fsB W.hdrB W.cellsB hdr T W.cellB rd [] [])
    {J : Memory.Inst} (hJ : J ∈ honestInsts W.core W.fsB W.hdrB hdr T) {f : String} {σ : Val}
    (ht : J.t = .phantom f σ) {tf : TracedFn} {pf : Placed} (hfo : W.fnOf f = some (tf, pf))
    (hsz : 2 + tf.core.params.length ≤ W.fsB f)
    (hreg : registered (loopTable W.p) f → 2 + tf.core.params.length < W.fsB f) :
    (∀ k (hk : k < tf.core.params.length), (W.honestB hdr T).read
      (addressOfIndex (J.fp + (2 + k))) = some (σ tf.core.params[k])) ∧
    (registered (loopTable W.p) f → (W.honestB hdr T).read
      (addressOfIndex (J.fp + (2 + tf.core.params.length))) = some (ofK (addressOfIndex J.fp))) := by
  have hmem : ∀ q ∈ (tf.core.params.mapIdx (fun k v => (2 + k, σ v)) ++
      (if ((loopTable W.p)[f]?).any (·.registered) then
        [(2 + tf.core.params.length, ofK (addressOfIndex J.fp))] else [])),
      2 ≤ q.1 → q.1 < W.fsB f → (∀ q' ∈ (tf.core.params.mapIdx (fun k v => (2 + k, σ v)) ++
      (if ((loopTable W.p)[f]?).any (·.registered) then
        [(2 + tf.core.params.length, ofK (addressOfIndex J.fp))] else [])), q'.1 = q.1 → q' = q) →
      (W.honestB hdr T).read (addressOfIndex (J.fp + q.1)) = some q.2 := by
    intro q hq h2 hlt hu
    have hc : q ∈ W.cellsB J := by
      rw [cellsB_phantom ht hfo]
      exact mem_frameB hq h2 hlt hu
    have := hH.toHonest.read_C hJ hc
    rwa [← addr_add] at this
  have hparam : ∀ q' ∈ tf.core.params.mapIdx (fun k v => (2 + k, σ v)),
      ∃ (k : ℕ) (hk : k < tf.core.params.length), q' = (2 + k, σ tf.core.params[k]) := by
    intro q' hq'
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq'
    simp only [List.length_mapIdx] at hk
    exact ⟨k, hk, by simp⟩
  refine ⟨fun k hk => ?_, fun hr => ?_⟩
  · have hq : (2 + k, σ tf.core.params[k]) ∈ tf.core.params.mapIdx (fun k v => (2 + k, σ v)) :=
      List.mem_iff_getElem.mpr ⟨k, by simpa using hk, by simp⟩
    exact hmem _ (List.mem_append_left _ hq) (by simp only; omega) (by simp only; omega)
      fun q' hq' he => by
        rcases List.mem_append.mp hq' with hq' | hq'
        · obtain ⟨k', hk', rfl⟩ := hparam q' hq'
          simp only at he
          obtain rfl : k' = k := by omega
          rfl
        · split at hq'
          · simp only [List.mem_singleton] at hq'
            subst hq'
            simp only at he
            omega
          · exact absurd hq' List.not_mem_nil
  · have hr' : ((loopTable W.p)[f]?).any (·.registered) = true := hr
    have hlt := hreg hr
    refine hmem _ (List.mem_append_right _ (by simp only [hr', ↓reduceIte]; exact List.mem_singleton_self _))
      (by simp only; omega) (by simp only; omega) fun q' hq' he => ?_
    rcases List.mem_append.mp hq' with hq' | hq'
    · obtain ⟨k', hk', rfl⟩ := hparam q' hq'
      simp only at he
      omega
    · simp only [hr', ↓reduceIte] at hq'
      exact List.mem_singleton.mp hq'

/-- The callees of the frames set up: one per call, of its function, valid when entered, a
phantom on the words written when not. -/
theorem kidsValid_full {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {ks : List Tree},
    Tree.KidsValid P rd σ cs ks → ∀ (i : ℕ) (c : Call), cs[i]? = some c →
      ∃ k, ks[i]? = some k ∧ k.name = c.f ∧
        (c.taken = true → k.Valid P rd (c.args.map σ) (c.rets.map σ)) ∧
        (c.taken = false → (∃ f σ', k = .phantom f σ') ∧ Phantom P k (c.args.map σ))
  | [], [], _ => fun i c h => by simp at h
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | c :: cs, k :: ks, ⟨hn, hk, h⟩ => fun i c' hc => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      refine ⟨k, rfl, hn, fun ht => ?_, fun ht => ?_⟩
      · simp only [ht, ↓reduceIte] at hk
        exact hk
      · simp only [ht] at hk
        exact hk
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact kidsValid_full h i c' hc

/-- **Every running instance's frame of the honest memory holds `FHB`.** -/
theorem frame_honestB (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) :
    ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt W.core W.fsB W.hdrB W.cellsB hdr T W.cellB rd [] [] →
    ∀ I ∈ honestInsts W.core W.fsB W.hdrB hdr T,
    ∀ f σ bufs kids, I.t = .node f σ bufs kids → (f = "main" → I.fp = 0) → ∀ tf ∈ W.p,
    tf.core.name = f → ∀ es vs, walk σ tf.core.body = .ret es vs →
      FHB W (W.honestB hdr T) f I.fp σ es vs I.kidFps I.hdr := by
  intro hdr rd T hT hH I hI f σ bufs kids ht hm tf htf hnm es vs hw
  subst hnm
  obtain ⟨pf, hfo, hpa⟩ := fnOf_of_mem hW htf
  have hnd := (placed_names hW).2
  have hval : ∀ {J : Memory.Inst}, J ∈ honestInsts W.core W.fsB W.hdrB hdr T →
      ∀ {g : String} {σ' : Val} {bufs' : List ℕ} {kids' : List Tree},
      J.t = .node g σ' bufs' kids' → ∃ args rets, J.t.Valid W.core (W.honestB hdr T).read args rets := by
    intro J hJ g σ' bufs' kids' hJt
    rcases hH.toHonest.inst_good hJ with h | ⟨f', σ'', h⟩
    · exact h
    · rw [hJt] at h; cases h
  -- the instance's facts, at any running instance
  have inst : ∀ {J : Memory.Inst}, J ∈ honestInsts W.core W.fsB W.hdrB hdr T →
      ∀ {σ' : Val} {bufs' : List ℕ} {kids' : List Tree} {tf' : TracedFn}, tf' ∈ W.p →
      J.t = .node tf'.core.name σ' bufs' kids' → tf'.core.name ≠ "main" ∨ J.fp = 0 →
      ∀ {pf' : Placed}, W.fnOf tf'.core.name = some (tf', pf') → World.PlacedAs W tf' pf' →
      ∃ es' vs', walk σ' tf'.core.body = .ret es' vs' ∧ (∀ e ∈ es', e.Holds (W.honestB hdr T).read σ') ∧
        Tree.KidsValid W.core (W.honestB hdr T).read σ' (calls es') kids' ∧
        (∀ q ∈ addrs es', σ' q.1 = ofK (addressOfIndex (J.fp + (cellP pf'.locs q.2).getD 0))) ∧
        FrameClauses (loopTable W.p) tf' pf' J.fp σ' es' vs' J.hdr
          (W.famB tf' pf' J.fp J.kidFps J.hdr σ') := by
    intro J hJ σ' bufs' kids' tf' htf' hJt hmJ pf' hfo' hpa'
    obtain ⟨args, rets, hv⟩ := hval hJ hJt
    rw [hJt] at hv
    obtain ⟨fn, hf, -, es', vs', hw', -, hev, hk⟩ := hv
    obtain ⟨tf'', htf'', hcore, hfn⟩ := core_find hf
    have htt : tf' = tf'' := (eq_of_name hnd htf'' htf' (by rw [hcore, hfn])).symm
    subst htt
    rw [← hcore] at hw'
    have hevs : J.t.events W.core = es' := events_node hJt hf (hcore ▸ hw')
    have hadd : ∀ q ∈ addrs es', σ' q.1 = ofK (addressOfIndex (J.fp + (cellP pf'.locs q.2).getD 0)) := by
      intro q hq
      have := (hH.nodeAt hJ hJt).2 q (by rw [hevs]; exact hq)
      rw [this]
      unfold World.cellB
      rw [(fnOf_spec hfo').2.2.2]
    have hok := famB_ok hW htf' (hC tf' htf') hpa'
      (fun h => hmJ.resolve_left (fun h' => h' h)) J.kidFps J.hdr
    exact ⟨es', vs', hw', hev, hk, hadd, (hok.2 σ' es' vs' hw' hadd).1 _ hev⟩
  obtain ⟨es', vs', hw', hev, hk, hadd, hcl⟩ := inst hI htf ht
    (by by_cases h : tf.core.name = "main"; exact Or.inr (hm h); exact Or.inl h) hfo hpa
  rw [hw] at hw'
  simp only [Out.ret.injEq] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  have hkv := kidsValid_full hk
  have hkids : I.t.kids = kids := by rw [ht]; rfl
  have hlen : I.kidFps.length = (calls es).length := by
    rw [honest_kidFps hI, length_kidPos, List.length_map, hkids]
    exact (kidsValid_getW hk).1
  have hhK : tf.core.name ≠ "main" → IsInK I.hdr.1 ∧ IsInK I.hdr.2 := fun hn =>
    honest_hdrB hT hI (by rw [ht]; exact hn)
  refine ⟨tf, pf, hfo, ⟨?_, ?_, hhK, fun n h2 hn => own_cell hW hH hI htf ht hfo hpa h2 hn, hlen,
    ?_, ?_⟩, hadd⟩
  · have := (hH.toHonest.read_hdr hI).1
    rwa [← addr_add] at this
  · have := (hH.toHonest.read_hdr hI).2
    rwa [← addr_add] at this
  · intro i c kfp hc hkfp
    obtain ⟨k, hk', hkn, hkval, hkph⟩ := hkv i c hc
    obtain ⟨J, hJ, hJt, hJfp, hJh⟩ := honest_kid hI (k := k) (by rw [hkids]; exact hk')
    obtain rfl : kfp = J.fp := Option.some.inj (hkfp.symm.trans hJfp)
    have hne : c.f ≠ "main" := no_main_call hW htf hw c (List.mem_of_getElem? hc)
    have hKI := hcl.khK i c hc hhK
    have hJhdr : J.hdr = (W.famB tf pf I.fp I.kidFps I.hdr σ).kh i := by
      rw [hJh]; exact hdrB_node ht hfo i hKI
    have hJh0 := (hH.toHonest.read_hdr hJ)
    rw [← addr_add, ← addr_add, hJhdr] at hJh0
    refine ⟨hJh0.1, hJh0.2, ?_⟩
    cases htk : c.taken with
    | true =>
      have hv := hkval htk
      rw [← hJt] at hv
      rcases hJt' : J.t with ⟨g, σ', bufs', kids'⟩ | ⟨g, σ'⟩
      · rw [hJt'] at hv
        obtain ⟨fn', hf', hpar', -⟩ := hv
        obtain ⟨tf', htf', hcore', hfn'⟩ := core_find hf'
        have hg : g = c.f := by rw [← hkn, ← hJt, hJt']; rfl
        subst hg
        obtain ⟨pf', hfo', hpa'⟩ := fnOf_of_mem hW htf'
        rw [← hfn', ← hcore'] at hJt'
        obtain ⟨es'', vs'', hw'', -, -, -, hclJ⟩ := inst hJ htf' hJt'
          (Or.inl (by rw [hcore', hfn']; exact hne)) hfo' hpa'
        rw [← hcore'] at hpar'
        have hal : c.args.length = tf'.core.params.length := by
          simpa using (congrArg List.length hpar').symm
        have hsz := placed_size hW htf' hpa'
        refine ⟨fun k' hk'' => ?_, fun hreg => ?_⟩
        · have hk3 : k' < tf'.core.params.length := hal ▸ hk''
          rw [own_cell hW hH hJ htf' hJt' hfo' hpa' (by omega) (by omega)]
          have hcell := (hclJ.cell tf'.core.params[k'] (by simp [readsP])
            (2 + k') (placed_params hW htf' hpa' k' hk3)).2.2
          rw [hcell]
          have := congrArg (·[k']?) hpar'
          simp only [List.getElem?_map] at this
          rw [List.getElem?_eq_getElem hk3, List.getElem?_eq_getElem hk''] at this
          simpa using this
        · have hreg' : registered (loopTable W.p) tf'.core.name := by
            rw [hcore', hfn']; exact hreg
          rw [hal, own_cell hW hH hJ htf' hJt' hfo' hpa' (by omega) (hsz.2 hreg')]
          rw [hclJ.self hreg']
      · rw [hJt'] at hv
        exact hv.elim
    | false =>
      obtain ⟨⟨gf, σ', hkp⟩, fn', hf', hpar'⟩ := hkph htk
      subst hkp
      have hg : gf = c.f := hkn
      subst hg
      simp only [Tree.name, Tree.val] at hf' hpar'
      obtain ⟨tf', htf', hcore', hfn'⟩ := core_find hf'
      obtain ⟨pf', hfo', hpa'⟩ := fnOf_of_mem hW htf'
      have hname : tf'.core.name = c.f := by rw [hcore', hfn']
      rw [hname] at hfo'
      have hsz := placed_size hW htf' hpa'
      have hle := frame_le_fsB hW htf' hpa'
      rw [hname] at hle
      obtain ⟨hpc, hsc⟩ := phantom_cell hH hJ hJt hfo' (by omega)
        (fun hreg => by rw [← hname] at hreg; have := hsz.2 hreg; omega)
      rw [← hcore'] at hpar'
      have hal : c.args.length = tf'.core.params.length := by
        simpa using (congrArg List.length hpar').symm
      refine ⟨fun k' hk'' => ?_, fun hreg => ?_⟩
      · have hk3 : k' < tf'.core.params.length := hal ▸ hk''
        rw [hpc k' hk3]
        have := congrArg (·[k']?) hpar'
        simp only [List.getElem?_map] at this
        rw [List.getElem?_eq_getElem hk3, List.getElem?_eq_getElem hk''] at this
        simpa using this
      · rw [hal]
        exact hsc hreg
  · intro hloop kfp hlast
    have hmn : tf.core.name ≠ "main" := by
      intro h; rw [h] at hloop; exact absurd hloop (by decide)
    have hl : W.core.loop I.t.name = true := by
      obtain ⟨args, rets, hv⟩ := hval hI ht
      rw [ht] at hv
      obtain ⟨fn, hf, -⟩ := hv
      obtain ⟨tf'', htf'', hcore, hfn⟩ := core_find hf
      have htt : tf = tf'' := (eq_of_name hnd htf'' htf (by rw [hcore, hfn])).symm
      subst htt
      rw [ht]
      simp only [Tree.name]
      rw [Program.loop_of_find? hf, ← hcore, ← (hC tf htf).loopNamed]
      exact hloop
    have hkne : I.t.kids ≠ [] := by
      intro he
      rw [hkids] at he
      subst he
      have : I.kidFps.length = 0 := by
        rw [honest_kidFps hI, length_kidPos, List.length_map, hkids]; rfl
      rw [List.length_eq_zero_iff] at this
      rw [this] at hlast
      cases hlast
    have := honest_kidFps_getLast? hI hl hkne
    rw [hlast] at this
    rw [Option.some.inj this, ht]
    simp only [Tree.name]
    rw [fsB_fn hW htf hpa hmn]

end

end
end LeanVM.Guest.Backend.Complete
