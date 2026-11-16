/-
  LeanVM.Guest.Backend.Complete.ProgCompose

  The composition of the functions' counted runs into one run of `main`, at any compiled
  program, any honest memory and any cost per instance.
-/

module

public import LeanVM.Guest.Backend.Complete.Program

/-!
# The composition at any program

`Guest/Cpl/Compose.lean` composes the guest's per-function runs into one run of `main`; this is
its proof at any `World`. `CplRunW W FH ω tf`: function `tf` runs, counted by `ω` besides its
callees, on any memory holding the jump tables and a frame holding what `FH` asks. `ComposeHyps`
asks it of every function, `FH` of every running instance of the honest memory
`honest W.core fs H C hdr T`, the jump tables in that memory, and no path calling `main`. Then
`main_runW`: on the honest memory, `main` runs from its entry at frame `g^0` to the final
registers within the call tree's cost.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (RunC)

@[expose] public section

/-- What an instance's frame holds, as a predicate: memory, function, frame, valuation, path,
returned values, callee frames, header. -/
abbrev FrameP : Type :=
  ∀ {κ : ℕ}, MemoryImage κ → String → ℕ → Val → List Ev → List V → List ℕ → E × E → Prop

/-- **Function `tf` runs, counted**, on any memory holding the jump tables and a frame holding
what `FH` asks: from its entry at its frame to its return registers (`main`: the final ones), at
most `ω` instructions of each opcode besides its callees', its returned values left after its
arguments. -/
def CplRunW {κ₀ : ℕ} (W : World κ₀) (FH : FrameP) (ω : String → Val → Opcode → ℕ)
    (tf : TracedFn) : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), JTHolds L W.layout W.slots → ∀ (fp : ℕ),
    (tf.core.name = "main" → fp = 0) →
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ tf.core.body = .ret es vs →
    (∀ e ∈ es, e.Holds L.read σ) → ∀ (kfps : List ℕ) (hdr : E × E),
    FH L tf.core.name fp σ es vs kfps hdr → ∀ ck : List (Opcode → ℕ),
    World.KidsRunP (World.withL W L) σ es kfps ck →
    ∃ (r : Registers K) (c : Opcode → ℕ),
      (if tf.core.name = "main" then r = Registers.final W.prog
        else retRegs L (addressOfIndex fp) = some r) ∧
      RunC W.prog L ⟨addressOfIndex (W.ent tf.core.name), addressOfIndex fp⟩ r c ∧
      (∀ op, c op ≤ ω tf.core.name σ op + (ck.map (· op)).sum) ∧
      ∀ k (hk : k < vs.length),
        L.read (addressOfIndex (fp + (2 + tf.core.params.length + k))) = some (σ vs[k])

/-- **What the composition rests on**: every function runs on a frame holding `FH`, every
running instance's frame of the honest memory holds it, the honest memory holds the jump
tables, and no path calls `main`. -/
structure ComposeHyps {κ₀ : ℕ} (W : World κ₀) (FH : FrameP) (ω : String → Val → Opcode → ℕ)
    (fs : String → ℕ) (H : Inst → ℕ → E × E) (C : Inst → List (ℕ × E))
    (cert : String → V → ℕ) : Prop where
  run : ∀ tf ∈ W.p, CplRunW W FH ω tf
  frame : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt W.core fs H C hdr T cert rd [] [] → ∀ I ∈ honestInsts W.core fs H hdr T,
    ∀ f σ bufs kids, I.t = .node f σ bufs kids → ∀ tf ∈ W.p, tf.core.name = f →
    ∀ es vs, walk σ tf.core.body = .ret es vs →
      FH (honest W.core fs H C hdr T) f I.fp σ es vs I.kidFps I.hdr
  jt : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt W.core fs H C hdr T cert rd [] [] →
    JTHolds (honest W.core fs H C hdr T) W.layout W.slots
  noMain : ∀ tf ∈ W.p, ∀ σ es vs, walk σ tf.core.body = .ret es vs → ∀ c ∈ calls es,
    c.f ≠ "main"

/-! ## Lemmas -/

/-- A core function of the program is a traced function's core. -/
theorem core_find {κ₀ : ℕ} {W : World κ₀} {f : String} {fn : Fn} (h : W.core.find? f = some fn) :
    ∃ tf ∈ W.p, tf.core = fn ∧ fn.name = f := by
  unfold World.core Program.find? at h
  rw [List.find?_map] at h
  obtain ⟨tf, htf, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨tf, List.mem_of_find?_eq_some htf, rfl, ?_⟩
  simpa using List.find?_some htf

/-- The callees of the frames set up: one per call, of its function, valid when entered. -/
theorem kidsValid_getW {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {ks : List Tree},
    Tree.KidsValid P rd σ cs ks → ks.length = cs.length ∧ ∀ (i : ℕ) (c : Call), cs[i]? = some c →
      ∃ k, ks[i]? = some k ∧ k.name = c.f ∧
        (c.taken = true → k.Valid P rd (c.args.map σ) (c.rets.map σ))
  | [], [], _ => ⟨rfl, fun i c h => by simp at h⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | c :: cs, k :: ks, ⟨hn, hk, h⟩ => by
    obtain ⟨hl, ih⟩ := kidsValid_getW h
    refine ⟨by simp [hl], fun i c' hc => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      refine ⟨k, rfl, hn, fun ht => ?_⟩
      simp only [ht, ↓reduceIte] at hk
      exact hk
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact ih i c' hc

theorem treeCostKids_eq_sum (ω : String → Val → ℕ) : ∀ ks : List Tree,
    treeCostKids ω ks = (ks.map (treeCost ω)).sum
  | [] => by rw [treeCostKids]; rfl
  | k :: ks => by rw [treeCostKids, treeCostKids_eq_sum ω ks, List.map_cons, List.sum_cons]

theorem sum_range_getDW {α : Type} (g : α → ℕ) : ∀ ks : List α,
    ((List.range ks.length).map fun i => ((ks[i]?).map g).getD 0).sum = (ks.map g).sum
  | [] => rfl
  | k :: ks => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.map_cons, List.sum_cons, ← sum_range_getDW g ks]
    simp [Function.comp_def]

theorem total_lt_of_kidW {fs : String → ℕ} {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} {i : ℕ} {k : Tree} (h2 : 1 ≤ fs f) (hk : kids[i]? = some k) :
    k.total fs < (Memory.Tree.node f σ bufs kids).total fs := by
  rw [total_node, totalKids_eq_sum]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := Tree.total fs) (List.mem_of_getElem? hk))
  omega

private theorem ite_intro_posW {p : Prop} [Decidable p] {a b : Prop} (hp : p) (ha : a) :
    if p then a else b := by
  split
  · exact ha
  · contradiction

private theorem ite_intro_negW {p : Prop} [Decidable p] {a b : Prop} (hp : ¬p) (hb : b) :
    if p then a else b := by
  split
  · contradiction
  · exact hb

private theorem ite_elim_posW {p : Prop} [Decidable p] {a b : Prop} (hp : p) (h : if p then a else b) :
    a := by
  split at h
  · exact h
  · contradiction

private theorem ite_elim_negW {p : Prop} [Decidable p] {a b : Prop} (hp : ¬p) (h : if p then a else b) :
    b := by
  split at h
  · contradiction
  · exact h

/-- What an instance's run gives: its return registers (`main`: the final ones), a counted run
there from its entry at its frame within its subtree's cost, and its returns after its
arguments. -/
def InstRunsW {κ₀ : ℕ} (W : World κ₀) (ω : String → Val → Opcode → ℕ) {κ : ℕ} (L : MemoryImage κ)
    (I : Inst) (args rets : List E) : Prop :=
  ∃ (r : Registers K) (c : Opcode → ℕ),
    (if I.t.name = "main" then r = Registers.final W.prog
      else retRegs L (addressOfIndex I.fp) = some r) ∧
    RunC W.prog L ⟨addressOfIndex (W.ent I.t.name), addressOfIndex I.fp⟩ r c ∧
    (∀ op, c op ≤ treeCost (fun f σ => ω f σ op) I.t) ∧
    ∀ k (hk : k < rets.length), L.read (addressOfIndex (I.fp + (2 + args.length + k))) = some rets[k]

section Insts

variable {κ₀ : ℕ} {W : World κ₀} {FH : FrameP} {ω : String → Val → Opcode → ℕ} {fs : String → ℕ}
  {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)} {cert : String → V → ℕ}
  (h : ComposeHyps W FH ω fs H C cert) {hdr : E × E} {rd : Reader} {T : Tree}
  (hname : T.name = "main") (hH : HonestAt W.core fs H C hdr T cert rd [] [])
include h hname hH

/-- **Every instance that runs runs**, by induction on the words its subtree allocates. -/
theorem inst_runsW : ∀ n, ∀ I ∈ honestInsts W.core fs H hdr T, I.t.total fs < n →
    (I.t.name = "main" → I.fp = 0) → ∀ args rets,
      I.t.Valid W.core (honest W.core fs H C hdr T).read args rets →
        InstRunsW W ω (honest W.core fs H C hdr T) I args rets
  | 0, _, _, hn, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, I, hI, hn, hm, args, rets, hv => by
    set L := honest W.core fs H C hdr T with hL
    rcases hti : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hti] at hv
      obtain ⟨fn, hf, hpar, es, vs, hw, hrets, hev, hk⟩ := hv
      obtain ⟨tf, htf, rfl, hnm⟩ := core_find hf
      have hF := h.frame hdr rd T hname hH I hI f σ bufs kids hti tf htf hnm es vs hw
      have hkv := kidsValid_getW hk
      have hkids : I.t.kids = kids := by rw [hti]; rfl
      have h2 : 2 ≤ fs f := by
        have := hH.toHonest.cells.two_le I hI
        rwa [hti] at this
      have hex : ∀ i' : ℕ, ∃ ci : Opcode → ℕ, (∀ (c : Call) (kfp : ℕ), (calls es)[i']? = some c →
          I.kidFps[i']? = some kfp → c.taken = true →
            (∃ r, retRegs L (addressOfIndex kfp) = some r ∧
              RunC W.prog L ⟨addressOfIndex (W.ent c.f), addressOfIndex kfp⟩ r ci) ∧
            ∀ k (hk : k < c.rets.length),
              L.read (addressOfIndex (kfp + (2 + c.args.length + k))) = some (σ c.rets[k])) ∧
          ∀ op, ci op ≤ ((kids[i']?).map (treeCost (fun f σ => ω f σ op))).getD 0 := by
        intro i'
        cases hc : (calls es)[i']? with
        | none => exact ⟨0, fun c _ h' => absurd h' (by simp), fun _ => Nat.zero_le _⟩
        | some c =>
          obtain ⟨k, hk', hkn, hkval⟩ := hkv.2 i' c hc
          by_cases htk : c.taken = true
          · obtain ⟨J, hJ, hJt, hJfp, -⟩ := honest_kid hI (k := k) (by rw [hkids]; exact hk')
            have hlt' : J.t.total fs < n := by
              have := total_lt_of_kidW (σ := σ) (bufs := bufs) (by omega : 1 ≤ fs f) hk'
              rw [hti] at hn
              rw [hJt]
              omega
            have hne : c.f ≠ "main" := h.noMain tf htf σ es vs hw c (List.mem_of_getElem? hc)
            have hJn : J.t.name = c.f := by rw [hJt, hkn]
            obtain ⟨r, ci, hr, hrun, hle, hrets'⟩ := inst_runsW n J hJ hlt'
              (fun hm' => absurd (hJn ▸ hm') hne) _ _ (hJt ▸ hkval htk)
            refine ⟨ci, fun c' kfp hc' hkfp _ => ?_, fun op => ?_⟩
            · obtain rfl : c' = c := (Option.some.inj hc').symm
              obtain rfl : kfp = J.fp := Option.some.inj (hkfp.symm.trans hJfp)
              rw [hJn] at hr hrun
              simp only [hne, ↓reduceIte] at hr
              refine ⟨⟨r, hr, hrun⟩, fun k' hk'' => ?_⟩
              have := hrets' k' (by simpa using hk'')
              simpa using this
            · rw [hk']
              simpa [hJt] using hle op
          · refine ⟨0, fun c' kfp hc' _ ht' => ?_, fun _ => Nat.zero_le _⟩
            obtain rfl : c' = c := (Option.some.inj hc').symm
            exact absurd ht' htk
      choose cf hcf using hex
      set ck := (List.range (calls es).length).map cf with hck
      have hK : World.KidsRunP (World.withL W L) σ es I.kidFps ck := by
        refine ⟨by simp [hck], fun i' c kfp hc hkfp ht => ?_⟩
        have hi' : i' < (calls es).length := (List.getElem?_eq_some_iff.mp hc).1
        have hget : ck.getD i' 0 = cf i' := by simp [hck, hi']
        rw [hget]
        exact (hcf i').1 c kfp hc hkfp ht
      have hjt : JTHolds L W.layout W.slots := h.jt hdr rd T hname hH
      have hmain : tf.core.name = "main" → I.fp = 0 := fun h1 =>
        hm (by rw [hti]; exact hnm ▸ h1)
      obtain ⟨r, c, hr, hrun, hle, hrets'⟩ := h.run tf htf L hjt I.fp hmain σ es vs hw hev
        I.kidFps I.hdr (hnm ▸ hF) ck hK
      refine ⟨r, c, ?_, ?_, fun op => ?_, fun k hk' => ?_⟩
      · rw [hti]
        by_cases hfm : f = "main"
        · exact ite_intro_posW (p := (Memory.Tree.node f σ bufs kids).name = "main") hfm
            (ite_elim_posW (hnm ▸ hfm) hr)
        · exact ite_intro_negW (p := (Memory.Tree.node f σ bufs kids).name = "main") hfm
            (ite_elim_negW (fun h1 => hfm (hnm ▸ h1)) hr)
      · rw [hti]
        simpa only [Tree.name, hnm] using hrun
      · rw [hti, treeCost, treeCostKids_eq_sum, ← sum_range_getDW _ kids, hkv.1]
        have hs : (ck.map (· op)).sum ≤
            ((List.range (calls es).length).map fun i' =>
              ((kids[i']?).map (treeCost (fun f σ => ω f σ op))).getD 0).sum := by
          rw [hck, List.map_map]
          exact List.sum_le_sum fun i' _ => (hcf i').2 op
        have := hle op
        rw [hnm] at this
        omega
      · subst hrets hpar
        have hk'' : k < vs.length := by simpa using hk'
        have := hrets' k hk''
        simpa using this
    · rw [hti] at hv
      exact hv.elim

end Insts

/-- **The composition**: on the honest memory, `main` runs from its entry at frame `g^0` to the
final registers, within the call tree's cost. -/
theorem main_runW {κ₀ : ℕ} {W : World κ₀} {FH : FrameP} {ω : String → Val → Opcode → ℕ}
    {fs : String → ℕ} {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)} {cert : String → V → ℕ}
    (h : ComposeHyps W FH ω fs H C cert) : ∀ (hdr : E × E) (rd : Reader) (T : Tree),
    T.name = "main" → HonestAt W.core fs H C hdr T cert rd [] [] →
    ∃ c : Opcode → ℕ, RunC W.prog (honest W.core fs H C hdr T)
      ⟨addressOfIndex (W.ent "main"), 1⟩ (Registers.final W.prog) c ∧
      ∀ op, c op ≤ treeCost (fun f σ => ω f σ op) T := by
  intro hdr rd T hname hH
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := W.core) (fs := fs) (H := H) (hdr := hdr) (T := T)
  have hv : I.t.Valid W.core (honest W.core fs H C hdr T).read [] [] := by
    rw [hIt]; exact hH.toHonest.valid_image
  obtain ⟨r, c, hr, hrun, hle, -⟩ :=
    inst_runsW h hname hH _ I hI (Nat.lt_succ_self _) (fun _ => hfp) [] [] hv
  rw [hIt] at hr hrun hle
  rw [hname] at hr hrun
  simp only [↓reduceIte] at hr
  subst hr
  rw [hfp, show (addressOfIndex 0 : K) = 1 by rw [addressOfIndex, pow_zero]] at hrun
  exact ⟨c, hrun, hle⟩

end
end LeanVM.Guest.Backend.Complete
