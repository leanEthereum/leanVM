module

public import LeanVM.Guest.Complete.ComposeL
public import LeanVM.Guest.B1.VsC.Quiet

/-!
# Composing placed completeness on a valuation per memory

`callAtA_node` and `callAtA_nodeL` take one valuation before the memory. A range check's touched
words (the words at `x` and `k / x`, low addresses `LowDef` only says are defined) are read from the
memory, so a node with a range check and callees or a `HeapBuf` has no such valuation. The twins
here (`callAtA_nodeRd`, `callAtA_nodeLRd`, as `callCompletes_nodeRd` is `callCompletes_node`'s) fix
`σ0` before the memory, for the node's allocations, callees (`KidsAtF`, `KidsAtL`) and own words,
and take on each memory a valuation `σ` that walks the same path, agrees with `σ0` on the calls'
arguments and returns (`CallsAgree`), has the same allocations, is placed (`NodeAt`) and loads and
hints in the region, and makes the events hold.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **A node completes placed on a valuation per memory**, not a loop helper: `callAtA_node` with
the valuation `σ0` fixing the allocations, the callees and the own words, and on each memory a
valuation `σ` taking the same path, agreeing with `σ0` on the calls' words, placed as `σ0` places
the node, its events holding. -/
theorem callAtA_nodeRd {k : ℕ} {f : String} {args rets : List E} {R D : ℕ → Prop} {Out Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fp c e : ℕ} (hlp : coreProgram.loop f = false) (hfc : fp + fs f ≤ c)
    (h : ∃ (σ0 : Val) (fn : Fn) (es : List Ev) (vs : List V) (Wo : Words) (Qs : List (Reader → Tree → Prop))
        (Oend : Reader → Prop) (Dend : ℕ → Prop),
      coreProgram.find? f = some fn ∧
      WordsInA Wo (fp + 2) (fp + fs f) c (c + (allocs σ0 es).sum) ∧
      (∀ i, D i → ownData cert fp c f (allocs σ0 es) es i ∨ Dend i) ∧
      KidsAtF fs al cert k σ0 (fun i => R i ∨ ownData cert fp c f (allocs σ0 es) es i) Pre
        (fun rd => HoldsWords rd Wo) (fun _ => False) Qs (calls es) (c + (allocs σ0 es).sum) e Oend Dend ∧
      (∀ rd, Oend rd → Out rd) ∧
      ∀ rd, LowDef k rd → Pre rd → Oend rd → ∃ σ : Val,
        fn.params.map σ = args ∧ walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧
        allocs σ es = allocs σ0 es ∧ NodeAt cert (fp, c) f σ (allocs σ0 es) es ∧ VsC.CallsAgree σ0 σ (calls es) ∧
        (∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
          (ownData cert fp c f (allocs σ0 es) es i ∨ R i ∨ Dend i)) ∧
        (∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧
          (ownData cert fp c f (allocs σ0 es) es i ∨ R i ∨ Dend i)) ∧
        (∀ ev ∈ es, ev.Holds rd σ) ∧
        ∀ ts, Tree.KidsValid coreProgram rd σ (calls es) ts → KidsPost rd Qs (calls es) ts →
          Post rd (.node f σ (allocs σ0 es) ts)) :
    CallAtA fs al cert k f args rets R D Out Pre Post (fs f) fp c e := by
  obtain ⟨σ0, fn, es, vs, Wo, Qs, Oend, Dend, hf, hWo, hD, hk, hout, hrd⟩ := h
  set bufs := allocs σ0 es with hbufs
  obtain ⟨Wk, hle, hin, hdisj, hO, hr⟩ := kidsAtF_words _ _ _ _ _ _ _ _ hk
  refine ⟨Wo ++ Wk, ⟨fun q hq => ?_, ?_⟩, by omega, fun rd hW => ?_, fun rd hl hW hp => ?_⟩
  · rcases List.mem_append.mp hq with hq | hq
    · rcases hWo.1 q hq with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · have := hin q hq; exact Or.inr ⟨by omega, this.2⟩
  · refine List.pairwise_append.mpr ⟨hWo.2, hdisj, fun q hq q' hq' => Or.inl ?_⟩
    have := hin q' hq'
    rcases hWo.1 q hq with h' | h' <;> omega
  · obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hW
    exact hout rd (hO rd hw1 hw2)
  · obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hW
    have hOe := hO rd hw1 hw2
    obtain ⟨ts, hvs0, hbs, hqs, hends, hpls, hlos, hhis, hDs⟩ := hr rd hl hp hw1 hw2
    obtain ⟨σ, hpar, hw, hret, hal, hnode, hag, hlo, hhi, hev, hpost⟩ := hrd rd hl hp hOe
    have hvs := VsC.kidsValid_congr _ _ hag hvs0
    have hev' : (Memory.Tree.node f σ bufs ts).events coreProgram = es := Complete.events_node hf hw
    have hkp : kidPosA fs coreProgram.loop al (fp, c) f bufs ts = posF fs coreProgram.loop al (c + bufs.sum) ts := by
      simp only [kidPosA, hlp, Bool.false_eq_true, ↓reduceIte]
    have hdat : ∀ i, (ownData cert fp c f bufs es i ∨
        Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al (c + bufs.sum) ts) ts i) →
        (Memory.Tree.node f σ bufs ts).DataA coreProgram fs al cert (fp, c) i := fun i hi => by
      rw [dataA_node, hev', hkp]; exact hi
    have hreg : ∀ i, ((R i ∨ ownData cert fp c f bufs es i) ∨ False ∨
        Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al (c + bufs.sum) ts) ts i) →
        (Memory.Tree.node f σ bufs ts).DataA coreProgram fs al cert (fp, c) i ∨ R i := fun i hi => by
      rcases hi with (hi | hi) | hi | hi
      · exact Or.inr hi
      · exact Or.inl (hdat i (Or.inl hi))
      · exact hi.elim
      · exact Or.inl (hdat i (Or.inr hi))
    have hown : ∀ i, (ownData cert fp c f bufs es i ∨ R i ∨ Dend i) →
        (Memory.Tree.node f σ bufs ts).DataA coreProgram fs al cert (fp, c) i ∨ R i := fun i hi => by
      rcases hi with hi | hi | hi
      · exact Or.inl (hdat i (Or.inl hi))
      · exact Or.inr hi
      · rcases hDs i hi with hi | hi
        · exact hi.elim
        · exact Or.inl (hdat i (Or.inr hi))
    refine ⟨.node f σ bufs ts, rfl, ⟨fn, hf, hpar, es, vs, hw, hret, hev, hvs⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, fun i hi => ?_, hpost ts hvs hqs⟩
    · rw [Tree.BufsOk, hev']; exact ⟨by rw [hal], hbs⟩
    · rw [Tree.block, hlp]; simp
    · rw [endA_node, hlp]; simpa using hends
    · rw [placedA_node, hev', hkp]; exact ⟨hnode, hpls⟩
    · rw [loadsInA_node, hev', hkp]
      refine ⟨fun A hA => ?_, loadsInKidsA_mono ts _ (fun i hi => ?_) hlos⟩
      · obtain ⟨i, hi, hm⟩ := hlo A hA
        exact ⟨i, hi, hown i hm⟩
      · exact hreg i hi
    · rw [hintsIn_node, hev', hkp]
      refine ⟨fun A hA => ?_, hintsInKids_mono ts _ (fun i hi => ?_) hhis⟩
      · obtain ⟨i, hi, hm⟩ := hhi A hA
        exact ⟨i, hi, hown i hm⟩
      · exact hreg i hi
    · rcases hD i hi with hi | hi
      · exact hdat i (Or.inl hi)
      · rcases hDs i hi with hi | hi
        · exact hi.elim
        · exact hdat i (Or.inr hi)

/-- **A loop helper's node completes placed on a valuation per memory**: `callAtA_nodeL` as
`callAtA_nodeRd` is `callAtA_node`. -/
theorem callAtA_nodeLRd {k : ℕ} {f : String} {args rets : List E} {R D : ℕ → Prop} {Out Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fp c e Bt : ℕ} (hlp : coreProgram.loop f = true) (hfc : fp + (fs f + Bt) ≤ c)
    (h : ∃ (σ0 : Val) (fn : Fn) (es : List Ev) (vs : List V) (Wo : Words) (Qs : List (Reader → Tree → Prop))
        (Oend : Reader → Prop) (Dend : ℕ → Prop),
      coreProgram.find? f = some fn ∧
      WordsInA Wo (fp + 2) (fp + fs f) c (c + (allocs σ0 es).sum) ∧
      (∀ i, D i → ownData cert fp c f (allocs σ0 es) es i ∨ Dend i) ∧
      KidsAtL fs al cert k σ0 (fun i => R i ∨ ownData cert fp c f (allocs σ0 es) es i) Pre (fp + fs f)
        (fun rd => HoldsWords rd Wo) (fun _ => False) Qs (calls es) (c + (allocs σ0 es).sum) e Bt Oend Dend ∧
      (∀ rd, Oend rd → Out rd) ∧
      ∀ rd, LowDef k rd → Pre rd → Oend rd → ∃ σ : Val,
        fn.params.map σ = args ∧ walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧
        allocs σ es = allocs σ0 es ∧ NodeAt cert (fp, c) f σ (allocs σ0 es) es ∧ VsC.CallsAgree σ0 σ (calls es) ∧
        (∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
          (ownData cert fp c f (allocs σ0 es) es i ∨ R i ∨ Dend i)) ∧
        (∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧
          (ownData cert fp c f (allocs σ0 es) es i ∨ R i ∨ Dend i)) ∧
        (∀ ev ∈ es, ev.Holds rd σ) ∧
        ∀ ts, Tree.KidsValid coreProgram rd σ (calls es) ts → KidsPost rd Qs (calls es) ts →
          Post rd (.node f σ (allocs σ0 es) ts)) :
    CallAtA fs al cert k f args rets R D Out Pre Post (fs f + Bt) fp c e := by
  obtain ⟨σ0, fn, es, vs, Wo, Qs, Oend, Dend, hf, hWo, hD, hk, hout, hrd⟩ := h
  set bufs := allocs σ0 es with hbufs
  obtain ⟨Wk, hle, hin, hdisj, hO, hr⟩ := kidsAtL_words _ _ _ _ _ _ _ _ _ (by omega) hk
  refine ⟨Wo ++ Wk, ⟨fun q hq => ?_, ?_⟩, by omega, fun rd hW => ?_, fun rd hl hW hp => ?_⟩
  · rcases List.mem_append.mp hq with hq | hq
    · rcases hWo.1 q hq with h' | h'
      · exact Or.inl ⟨h'.1, by omega⟩
      · exact Or.inr ⟨h'.1, by omega⟩
    · rcases hin q hq with h' | h'
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, h'.2⟩
  · refine List.pairwise_append.mpr ⟨hWo.2, hdisj, fun q hq q' hq' => ?_⟩
    rcases hWo.1 q hq with h' | h' <;> rcases hin q' hq' with h'' | h'' <;> omega
  · obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hW
    exact hout rd (hO rd hw1 hw2)
  · obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hW
    have hOe := hO rd hw1 hw2
    obtain ⟨ts, hvs0, hbs, hqs, hends, hblks, hpls, hlos, hhis, hDs⟩ := hr rd hl hp hw1 hw2
    obtain ⟨σ, hpar, hw, hret, hal, hnode, hag, hlo, hhi, hev, hpost⟩ := hrd rd hl hp hOe
    have hvs := VsC.kidsValid_congr _ _ hag hvs0
    have hev' : (Memory.Tree.node f σ bufs ts).events coreProgram = es := Complete.events_node hf hw
    have hkp : kidPosA fs coreProgram.loop al (fp, c) f bufs ts =
        posL fs coreProgram.loop al (fp + fs f) (c + bufs.sum) ts := by
      simp only [kidPosA, hlp, ↓reduceIte]
    have hdat : ∀ i, (ownData cert fp c f bufs es i ∨
        Tree.DataKidsA coreProgram fs al cert (posL fs coreProgram.loop al (fp + fs f) (c + bufs.sum) ts) ts i) →
        (Memory.Tree.node f σ bufs ts).DataA coreProgram fs al cert (fp, c) i := fun i hi => by
      rw [dataA_node, hev', hkp]; exact hi
    have hreg : ∀ i, KRegL (fs := fs) (al := al) (cert := cert) (fun i => R i ∨ ownData cert fp c f bufs es i)
        (fun _ => False) (fp + fs f) (c + bufs.sum) ts i →
        (Memory.Tree.node f σ bufs ts).DataA coreProgram fs al cert (fp, c) i ∨ R i := fun i hi => by
      rcases hi with (hi | hi) | hi | hi
      · exact Or.inr hi
      · exact Or.inl (hdat i (Or.inl hi))
      · exact hi.elim
      · exact Or.inl (hdat i (Or.inr hi))
    have hown : ∀ i, (ownData cert fp c f bufs es i ∨ R i ∨ Dend i) →
        (Memory.Tree.node f σ bufs ts).DataA coreProgram fs al cert (fp, c) i ∨ R i := fun i hi => by
      rcases hi with hi | hi | hi
      · exact Or.inl (hdat i (Or.inl hi))
      · exact Or.inr hi
      · rcases hDs i hi with hi | hi
        · exact hi.elim
        · exact Or.inl (hdat i (Or.inr hi))
    refine ⟨.node f σ bufs ts, rfl, ⟨fn, hf, hpar, es, vs, hw, hret, hev, hvs⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, fun i hi => ?_, hpost ts hvs hqs⟩
    · rw [Tree.BufsOk, hev']; exact ⟨by rw [hal], hbs⟩
    · rw [Tree.block, hlp]; simp [hblks]
    · rw [endA_node, hlp]; simpa using hends
    · rw [placedA_node, hev', hkp]; exact ⟨hnode, hpls⟩
    · rw [loadsInA_node, hev', hkp]
      refine ⟨fun A hA => ?_, loadsInKidsA_mono ts _ (fun i hi => hreg i hi) hlos⟩
      obtain ⟨i, hi, hm⟩ := hlo A hA
      exact ⟨i, hi, hown i hm⟩
    · rw [hintsIn_node, hev', hkp]
      refine ⟨fun A hA => ?_, hintsInKids_mono ts _ (fun i hi => hreg i hi) hhis⟩
      obtain ⟨i, hi, hm⟩ := hhi A hA
      exact ⟨i, hi, hown i hm⟩
    · rcases hD i hi with hi | hi
      · exact hdat i (Or.inl hi)
      · rcases hDs i hi with hi | hi
        · exact hi.elim
        · exact hdat i (Or.inr hi)

end
end LeanVM.Guest.Complete
