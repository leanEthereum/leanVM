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

end

end
end LeanVM.Guest.Backend.Complete
