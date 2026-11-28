module

public import LeanVM.Guest.Complete.CallCompleteA
public import LeanVM.Guest.Complete.Compose
public import LeanVM.Guest.Complete.Call0

/-!
# Composing placed completeness

`callCompletes_node`'s placed twin. A node of `f`, not a loop helper, placed at frame `fp` and
cursor `c`: its valuation places its `HeapBuf`s and `frameAddr`s (`NodeAt`), its own words lie in
its frame past the header or its `HeapBuf`s, and its callees follow one another from the end of its
`HeapBuf`s as `posF` places them (`KidsAtF`): each entered call by `CallAtA` at the aligned base
`allocBase (al c.f) cur`, its cursor after its block, the next from its end; each skipped one a
phantom of its tail's frame. A callee loads from the region it is handed, which lies in the node's
region `R`, the node's own data and the data the earlier callees claim; its `Pre` is the node's and
what the memory holding the node's and the earlier callees' words satisfies (`O`, grown by each
callee's `Out`).

`kidsAtF_words` puts the callees together; `callAtA_node` the node.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- **The callees placed fresh from the cursor `cur`**, the last ending at `e`: each entered call
completes at the aligned base (`CallAtA`), loading from `R` and the data `Dacc` earlier callees
claimed, on memories satisfying `Pre` and `O` (the words held so far), adding its `Out` to `O` and
its claimed data to `Dacc`; each skipped one a phantom. At the end, `O` gives `Oend` and the data
claimed contains `Dend`. -/
def KidsAtF (k : ℕ) (σ : Val) (R : ℕ → Prop) (Pre : Reader → Prop) :
    (Reader → Prop) → (ℕ → Prop) → List (Reader → Tree → Prop) → List Call → ℕ → ℕ →
      (Reader → Prop) → (ℕ → Prop) → Prop
  | O, Dacc, _, [], cur, e, Oend, Dend => e = cur ∧ (∀ rd, O rd → Oend rd) ∧ ∀ i, Dend i → Dacc i
  | O, Dacc, Qs, c :: cs, cur, e, Oend, Dend =>
    if c.taken then
      ∃ (Bc ec : ℕ) (Rc Dc : ℕ → Prop) (Oc : Reader → Prop), (∀ i, Rc i → R i ∨ Dacc i) ∧
        CallAtA fs al cert k c.f (c.args.map σ) (c.rets.map σ) Rc Dc Oc (fun rd => Pre rd ∧ O rd)
          (Qs.headD fun _ _ => True) Bc (allocBase (al c.f) cur) (allocBase (al c.f) cur + Bc) ec ∧
        KidsAtF k σ R Pre (fun rd => O rd ∧ Oc rd) (fun i => Dacc i ∨ Dc i) Qs.tail cs ec e Oend Dend
    else
      (∃ σ', Phantom coreProgram (.phantom c.f σ') (c.args.map σ)) ∧
        KidsAtF k σ R Pre O Dacc Qs.tail cs (allocBase (al c.f) cur + fs (tailKey c.f)) e Oend Dend

variable {fs al cert}

theorem posF_cons {c : ℕ} {t : Tree} {ts : List Tree} :
    posF fs coreProgram.loop al c (t :: ts) =
      (allocBase (al t.name) c, allocBase (al t.name) c + t.block fs coreProgram.loop) ::
        posF fs coreProgram.loop al (t.endA fs coreProgram.loop al (allocBase (al t.name) c +
          t.block fs coreProgram.loop)) ts := by
  rw [posF]

/-- **The callees complete together**: their words in `[cur, e)`, disjoint; a memory holding them
and satisfying `O` satisfies `Oend`; on every memory holding them with `Pre` and `O`, their trees
are valid, placed at `posF`, ending at `e`, loading and hinting in `R`, `Dacc` and their data, their
data with `Dacc` containing `Dend`. -/
theorem kidsAtF_words {k : ℕ} {σ : Val} {R : ℕ → Prop} {Pre : Reader → Prop} :
    ∀ (cs : List Call) (O : Reader → Prop) (Dacc : ℕ → Prop) (Qs : List (Reader → Tree → Prop))
      (cur e : ℕ) (Oend : Reader → Prop) (Dend : ℕ → Prop),
    KidsAtF fs al cert k σ R Pre O Dacc Qs cs cur e Oend Dend →
    ∃ Wk : Words, cur ≤ e ∧ (∀ q ∈ Wk, cur ≤ q.1 ∧ q.1 + q.2.length ≤ e) ∧ Wk.Pairwise (fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1) ∧
      (∀ rd, O rd → HoldsWords rd Wk → Oend rd) ∧
      ∀ rd, LowDef k rd → Pre rd → O rd → HoldsWords rd Wk →
        ∃ ts : List Tree, Tree.KidsValid coreProgram rd σ cs ts ∧ Tree.BufsOkKids coreProgram ts ∧
          KidsPost rd Qs cs ts ∧ Tree.endF fs coreProgram.loop al cur ts = e ∧
          Tree.PlacedKidsA coreProgram fs al cert (posF fs coreProgram.loop al cur ts) ts ∧
          Tree.LoadsInKidsA coreProgram fs al cert
            (fun i => R i ∨ Dacc i ∨ Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al cur ts) ts i)
            (posF fs coreProgram.loop al cur ts) ts ∧
          Tree.HintsInKids coreProgram fs al cert
            (fun i => R i ∨ Dacc i ∨ Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al cur ts) ts i)
            (posF fs coreProgram.loop al cur ts) ts ∧
          ∀ i, Dend i → Dacc i ∨ Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al cur ts) ts i
  | [], O, Dacc, Qs, cur, e, Oend, Dend, h => by
    rw [KidsAtF] at h
    obtain ⟨rfl, hO, hD⟩ := h
    refine ⟨[], le_rfl, by simp, List.Pairwise.nil, fun rd ho _ => hO rd ho, fun rd _ _ _ _ => ?_⟩
    refine ⟨[], by rw [Tree.KidsValid]; trivial, by rw [Tree.BufsOkKids]; trivial,
      by cases Qs <;> simp [KidsPost], by rw [endF_nil], placedKidsA_nil, loadsInKidsA_nil, hintsInKids_nil,
      fun i hi => Or.inl (hD i hi)⟩
  | c :: cs, O, Dacc, Qs, cur, e, Oend, Dend, h => by
    rw [KidsAtF] at h
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at h
      obtain ⟨Bc, ec, Rc, Dc, Oc, hR, ⟨Wc, hWc, hce, hOc, hrc⟩, hrest⟩ := h
      obtain ⟨Wr, hle, hin, hdisj, hO, hr⟩ := kidsAtF_words cs _ _ _ ec e Oend Dend hrest
      have hb := le_allocBase (al c.f) cur
      refine ⟨Wc ++ Wr, by omega, fun q hq => ?_, ?_, fun rd ho hw => ?_, fun rd hl hp ho hw => ?_⟩
      · rcases List.mem_append.mp hq with hq | hq
        · rcases hWc.1 q hq with h' | h' <;> omega
        · have := hin q hq; omega
      · refine List.pairwise_append.mpr ⟨hWc.2, hdisj, fun q hq q' hq' => Or.inl ?_⟩
        have := hin q' hq'
        rcases hWc.1 q hq with h' | h' <;> omega
      · obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hw
        exact hO rd ⟨ho, hOc rd hw1⟩ hw2
      · obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hw
        obtain ⟨t, hn, hv, hbt, hbl, hend, hpl, hlo, hhi, hd, hq⟩ := hrc rd hl hw1 ⟨hp, ho⟩
        obtain ⟨ts, hvs, hbs, hqs, hends, hpls, hlos, hhis, hDs⟩ := hr rd hl hp ⟨ho, hOc rd hw1⟩ hw2
        have hpos : posF fs coreProgram.loop al cur (t :: ts) =
            (allocBase (al c.f) cur, allocBase (al c.f) cur + Bc) :: posF fs coreProgram.loop al ec ts := by
          rw [posF_cons, hn, hbl, hend]
        have hdat : ∀ i, Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al cur (t :: ts)) (t :: ts) i ↔
            t.DataA coreProgram fs al cert (allocBase (al c.f) cur, allocBase (al c.f) cur + Bc) i ∨
              Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al ec ts) ts i := fun i => by
          rw [hpos, dataKidsA_cons]
        have hreg : ∀ i, (R i ∨ (Dacc i ∨ Dc i) ∨ Tree.DataKidsA coreProgram fs al cert
            (posF fs coreProgram.loop al ec ts) ts i) →
            R i ∨ Dacc i ∨ Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al cur (t :: ts)) (t :: ts) i :=
          fun i hi => by
            rw [hdat]
            rcases hi with hi | (hi | hi) | hi
            · exact Or.inl hi
            · exact Or.inr (Or.inl hi)
            · exact Or.inr (Or.inr (Or.inl (hd i hi)))
            · exact Or.inr (Or.inr (Or.inr hi))
        have hregc : ∀ i, Rc i →
            R i ∨ Dacc i ∨ Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al cur (t :: ts)) (t :: ts) i :=
          fun i hi => (hR i hi).elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
        refine ⟨t :: ts, ?_, ⟨hbt, hbs⟩, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
        · rw [Tree.KidsValid]; simp only [ht, ↓reduceIte]; exact ⟨hn, hv, hvs⟩
        · cases Qs with
          | nil => simp [KidsPost]
          | cons Q Qs => exact kidsPost_cons.mpr ⟨fun _ => hq, hqs⟩
        · rw [endF_cons, hn, hbl, hend]; exact hends
        · rw [hpos, placedKidsA_cons]; exact ⟨hpl, hpls⟩
        · rw [hpos, loadsInKidsA_cons]
          refine ⟨loadsInA_mono t _ (fun i hi => by have := hregc i hi; rwa [hpos] at this) hlo, loadsInKidsA_mono ts _ (fun i hi => ?_) hlos⟩
          have := hreg i hi; rwa [hpos] at this
        · rw [hpos, hintsInKids_cons]
          refine ⟨hintsIn_mono t _ (fun i hi => by have := hregc i hi; rwa [hpos] at this) hhi, hintsInKids_mono ts _ (fun i hi => ?_) hhis⟩
          have := hreg i hi; rwa [hpos] at this
        · rw [hdat]
          rcases hDs i hi with (hi | hi) | hi
          · exact Or.inl hi
          · exact Or.inr (Or.inl (hd i hi))
          · exact Or.inr (Or.inr hi)
    · have ht' : c.taken = false := by simpa using ht
      simp only [ht', Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨σ', hph⟩, hrest⟩ := h
      set cur' := allocBase (al c.f) cur + fs (tailKey c.f) with hcur'
      obtain ⟨Wr, hle, hin, hdisj, hO, hr⟩ := kidsAtF_words cs _ _ _ cur' e Oend Dend hrest
      have hb := le_allocBase (al c.f) cur
      refine ⟨Wr, by omega, fun q hq => by have := hin q hq; omega, hdisj, hO, fun rd hl hp ho hw => ?_⟩
      obtain ⟨ts, hvs, hbs, hqs, hends, hpls, hlos, hhis, hDs⟩ := hr rd hl hp ho hw
      have hblk : (Tree.phantom c.f σ').block fs coreProgram.loop = fs (tailKey c.f) := by rw [Tree.block]
      have hpos : posF fs coreProgram.loop al cur (.phantom c.f σ' :: ts) =
          (allocBase (al c.f) cur, cur') :: posF fs coreProgram.loop al cur' ts := by
        rw [posF_cons, Tree.name, hblk, endA_phantom]
      have hdat : ∀ i, Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al cur (.phantom c.f σ' :: ts))
          (.phantom c.f σ' :: ts) i ↔ Tree.DataKidsA coreProgram fs al cert (posF fs coreProgram.loop al cur' ts) ts i :=
        fun i => by rw [hpos, dataKidsA_cons]; simp [dataA_phantom]
      refine ⟨.phantom c.f σ' :: ts, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
      · rw [Tree.KidsValid]; simp only [ht', Bool.false_eq_true, ↓reduceIte]
        exact ⟨rfl, ⟨⟨c.f, σ', rfl⟩, hph⟩, hvs⟩
      · rw [Tree.BufsOkKids, Tree.BufsOk]; exact ⟨trivial, hbs⟩
      · cases Qs with
        | nil => simp [KidsPost]
        | cons Q Qs => exact kidsPost_cons.mpr ⟨fun h => absurd h ht, hqs⟩
      · rw [endF_cons, Tree.name, hblk, endA_phantom]; exact hends
      · rw [hpos, placedKidsA_cons]; exact ⟨placedA_phantom, hpls⟩
      · rw [hpos, loadsInKidsA_cons]
        refine ⟨loadsInA_phantom, loadsInKidsA_mono ts _ (fun i hi => ?_) hlos⟩
        rw [← hpos, hdat]; exact hi
      · rw [hpos, hintsInKids_cons]
        refine ⟨hintsIn_phantom, hintsInKids_mono ts _ (fun i hi => ?_) hhis⟩
        rw [← hpos, hdat]; exact hi
      · rw [hdat]; exact hDs i hi

/-- **A node completes placed**, not a loop helper, from its own part at `(fp, c)` and its callees
chained from the end of its `HeapBuf`s. -/
theorem callAtA_node {k : ℕ} {f : String} {args rets : List E} {R D : ℕ → Prop} {Out Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fp c e : ℕ} (hlp : coreProgram.loop f = false) (hfc : fp + fs f ≤ c)
    (h : ∃ (σ : Val) (fn : Fn) (es : List Ev) (vs : List V) (Wo : Words) (Qs : List (Reader → Tree → Prop))
        (Oend : Reader → Prop) (Dend : ℕ → Prop),
      coreProgram.find? f = some fn ∧ fn.params.map σ = args ∧ walk σ fn.body = .ret es vs ∧
      vs.map σ = rets ∧ NodeAt cert (fp, c) f σ (allocs σ es) es ∧
      WordsInA Wo (fp + 2) (fp + fs f) c (c + (allocs σ es).sum) ∧
      (∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
        (ownData cert fp c f (allocs σ es) es i ∨ R i ∨ Dend i)) ∧
      (∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧
        (ownData cert fp c f (allocs σ es) es i ∨ R i ∨ Dend i)) ∧
      (∀ i, D i → ownData cert fp c f (allocs σ es) es i ∨ Dend i) ∧
      KidsAtF fs al cert k σ (fun i => R i ∨ ownData cert fp c f (allocs σ es) es i) Pre
        (fun rd => HoldsWords rd Wo) (fun _ => False) Qs (calls es) (c + (allocs σ es).sum) e Oend Dend ∧
      (∀ rd, Oend rd → Out rd) ∧
      (∀ rd, LowDef k rd → Pre rd → Oend rd → ∀ ev ∈ es, ev.Holds rd σ) ∧
      ∀ rd ts, LowDef k rd → Pre rd → Oend rd → Tree.KidsValid coreProgram rd σ (calls es) ts →
        KidsPost rd Qs (calls es) ts → Post rd (.node f σ (allocs σ es) ts)) :
    CallAtA fs al cert k f args rets R D Out Pre Post (fs f) fp c e := by
  obtain ⟨σ, fn, es, vs, Wo, Qs, Oend, Dend, hf, hpar, hw, hret, hnode, hWo, hlo, hhi, hD, hk, hout, hev,
    hpost⟩ := h
  set bufs := allocs σ es with hbufs
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
    obtain ⟨ts, hvs, hbs, hqs, hends, hpls, hlos, hhis, hDs⟩ := hr rd hl hp hw1 hw2
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
    refine ⟨.node f σ bufs ts, rfl, ⟨fn, hf, hpar, es, vs, hw, hret, hev rd hl hp hOe, hvs⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, fun i hi => ?_, hpost rd ts hl hp hOe hvs hqs⟩
    · rw [Tree.BufsOk, hev']; exact ⟨rfl, hbs⟩
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

end
end LeanVM.Guest.Complete
