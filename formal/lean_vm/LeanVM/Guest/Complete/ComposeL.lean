module

public import LeanVM.Guest.Complete.ComposeA

/-!
# Composing placed completeness: loop helpers

A loop helper's last callee is its tail call, placed at the next frame `tl = fp + fs f` (inside its
block, which is its frame and the tail's block) with its cursor after the other callees (`posL`).
`KidsAtL`: `KidsAtF` but the last call at `(tl, cur)`, its block `Bt` the node's `blockLast`;
`kidsAtL_words` puts the callees together, `callAtA_nodeL` the loop helper's node.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- **A loop helper's callees from the cursor `cur`**: fresh as `KidsAtF`, the last at `(tl, cur)`,
of block `Bt`, ending at `e`. -/
def KidsAtL (k : ℕ) (σ : Val) (R : ℕ → Prop) (Pre : Reader → Prop) (tl : ℕ) :
    (Reader → Prop) → (ℕ → Prop) → List (Reader → Tree → Prop) → List Call → ℕ → ℕ → ℕ →
      (Reader → Prop) → (ℕ → Prop) → Prop
  | O, Dacc, _, [], cur, e, Bt, Oend, Dend =>
    e = cur ∧ Bt = 0 ∧ (∀ rd, O rd → Oend rd) ∧ ∀ i, Dend i → Dacc i
  | O, Dacc, Qs, [c], cur, e, Bt, Oend, Dend =>
    if c.taken then
      ∃ (Rc Dc : ℕ → Prop) (Oc : Reader → Prop), (∀ i, Rc i → R i ∨ Dacc i) ∧
        CallAtA fs al cert k c.f (c.args.map σ) (c.rets.map σ) Rc Dc Oc (fun rd => Pre rd ∧ O rd)
          (Qs.headD fun _ _ => True) Bt tl cur e ∧
        (∀ rd, O rd → Oc rd → Oend rd) ∧ ∀ i, Dend i → Dacc i ∨ Dc i
    else
      (∃ σ', Phantom coreProgram (.phantom c.f σ') (c.args.map σ)) ∧ Bt = fs (tailKey c.f) ∧ e = cur ∧
        (∀ rd, O rd → Oend rd) ∧ ∀ i, Dend i → Dacc i
  | O, Dacc, Qs, c :: c' :: cs, cur, e, Bt, Oend, Dend =>
    if c.taken then
      ∃ (Bc ec : ℕ) (Rc Dc : ℕ → Prop) (Oc : Reader → Prop), (∀ i, Rc i → R i ∨ Dacc i) ∧
        CallAtA fs al cert k c.f (c.args.map σ) (c.rets.map σ) Rc Dc Oc (fun rd => Pre rd ∧ O rd)
          (Qs.headD fun _ _ => True) Bc (allocBase (al c.f) cur) (allocBase (al c.f) cur + Bc) ec ∧
        KidsAtL k σ R Pre tl (fun rd => O rd ∧ Oc rd) (fun i => Dacc i ∨ Dc i) Qs.tail (c' :: cs) ec e Bt Oend Dend
    else
      (∃ σ', Phantom coreProgram (.phantom c.f σ') (c.args.map σ)) ∧
        KidsAtL k σ R Pre tl O Dacc Qs.tail (c' :: cs) (allocBase (al c.f) cur + fs (tailKey c.f)) e Bt Oend Dend

variable {fs al cert}

theorem posL_one {tl c : ℕ} {t : Tree} : posL fs coreProgram.loop al tl c [t] = [(tl, c)] := by rw [posL]

theorem posL_cons {tl c : ℕ} {t t' : Tree} {ts : List Tree} :
    posL fs coreProgram.loop al tl c (t :: t' :: ts) =
      (allocBase (al t.name) c, allocBase (al t.name) c + t.block fs coreProgram.loop) ::
        posL fs coreProgram.loop al tl (t.endA fs coreProgram.loop al (allocBase (al t.name) c +
          t.block fs coreProgram.loop)) (t' :: ts) := by
  rw [posL]

/-- The region a callee may read: `R`, the earlier callees' claims, the callees' data. -/
abbrev KRegL (R Dacc : ℕ → Prop) (tl cur : ℕ) (ts : List Tree) (i : ℕ) : Prop :=
  R i ∨ Dacc i ∨ Tree.DataKidsA coreProgram fs al cert (posL fs coreProgram.loop al tl cur ts) ts i

/-- **A loop helper's callees complete together**: their words in the tail's frame past its header
or in `[cur, e)`, disjoint, as `kidsAtF_words`. -/
theorem kidsAtL_words {k : ℕ} {σ : Val} {R : ℕ → Prop} {Pre : Reader → Prop} {tl : ℕ} :
    ∀ (cs : List Call) (O : Reader → Prop) (Dacc : ℕ → Prop) (Qs : List (Reader → Tree → Prop))
      (cur e Bt : ℕ) (Oend : Reader → Prop) (Dend : ℕ → Prop), tl + Bt ≤ cur →
    KidsAtL fs al cert k σ R Pre tl O Dacc Qs cs cur e Bt Oend Dend →
    ∃ Wk : Words, cur ≤ e ∧
      (∀ q ∈ Wk, (tl + 2 ≤ q.1 ∧ q.1 + q.2.length ≤ tl + Bt) ∨ (cur ≤ q.1 ∧ q.1 + q.2.length ≤ e)) ∧
      Wk.Pairwise (fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1) ∧
      (∀ rd, O rd → HoldsWords rd Wk → Oend rd) ∧
      ∀ rd, LowDef k rd → Pre rd → O rd → HoldsWords rd Wk →
        ∃ ts : List Tree, Tree.KidsValid coreProgram rd σ cs ts ∧ Tree.BufsOkKids coreProgram ts ∧
          KidsPost rd Qs cs ts ∧ Tree.endL fs coreProgram.loop al cur ts = e ∧
          Tree.blockLast fs coreProgram.loop ts = Bt ∧
          Tree.PlacedKidsA coreProgram fs al cert (posL fs coreProgram.loop al tl cur ts) ts ∧
          Tree.LoadsInKidsA coreProgram fs al cert (KRegL (fs := fs) (al := al) (cert := cert) R Dacc tl cur ts)
            (posL fs coreProgram.loop al tl cur ts) ts ∧
          Tree.HintsInKids coreProgram fs al cert (KRegL (fs := fs) (al := al) (cert := cert) R Dacc tl cur ts)
            (posL fs coreProgram.loop al tl cur ts) ts ∧
          ∀ i, Dend i → Dacc i ∨ Tree.DataKidsA coreProgram fs al cert (posL fs coreProgram.loop al tl cur ts) ts i
  | [], O, Dacc, Qs, cur, e, Bt, Oend, Dend, _, h => by
    rw [KidsAtL] at h
    obtain ⟨rfl, rfl, hO, hD⟩ := h
    refine ⟨[], le_rfl, by simp, List.Pairwise.nil, fun rd ho _ => hO rd ho, fun rd _ _ _ _ => ?_⟩
    refine ⟨[], by rw [Tree.KidsValid]; trivial, by rw [Tree.BufsOkKids]; trivial,
      by cases Qs <;> simp [KidsPost], by rw [endL_nil], by rw [Tree.blockLast], placedKidsA_nil,
      loadsInKidsA_nil, hintsInKids_nil, fun i hi => Or.inl (hD i hi)⟩
  | [c], O, Dacc, Qs, cur, e, Bt, Oend, Dend, htl, h => by
    rw [KidsAtL] at h
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at h
      obtain ⟨Rc, Dc, Oc, hR, ⟨Wc, hWc, hce, hOc, hrc⟩, hO, hD⟩ := h
      refine ⟨Wc, hce, fun q hq => hWc.1 q hq, hWc.2, fun rd ho hw => hO rd ho (hOc rd hw),
        fun rd hl hp ho hw => ?_⟩
      obtain ⟨t, hn, hv, hbt, hbl, hend, hpl, hlo, hhi, hd, hq⟩ := hrc rd hl hw ⟨hp, ho⟩
      have hdat : ∀ i, Tree.DataKidsA coreProgram fs al cert (posL fs coreProgram.loop al tl cur [t]) [t] i ↔
          t.DataA coreProgram fs al cert (tl, cur) i := fun i => by
        rw [posL_one, dataKidsA_cons]; simp [not_dataKidsA_nil]
      refine ⟨[t], ?_, ⟨hbt, by rw [Tree.BufsOkKids]; trivial⟩, ?_, by rw [endL_one]; exact hend,
        by rw [Tree.blockLast]; exact hbl, by rw [posL_one, placedKidsA_cons]; exact ⟨hpl, placedKidsA_nil⟩,
        ?_, ?_, fun i hi => ?_⟩
      · rw [Tree.KidsValid]; simp only [ht, ↓reduceIte]; exact ⟨hn, hv, by rw [Tree.KidsValid]; trivial⟩
      · cases Qs with
        | nil => simp [KidsPost]
        | cons Q Qs => exact kidsPost_cons.mpr ⟨fun _ => hq, by cases Qs <;> simp [KidsPost]⟩
      · rw [posL_one, loadsInKidsA_cons]
        refine ⟨loadsInA_mono t _ (fun i hi => ?_) hlo, loadsInKidsA_nil⟩
        rcases hR i hi with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · rw [posL_one, hintsInKids_cons]
        refine ⟨hintsIn_mono t _ (fun i hi => ?_) hhi, hintsInKids_nil⟩
        rcases hR i hi with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · rw [hdat]
        rcases hD i hi with h' | h'
        · exact Or.inl h'
        · exact Or.inr (hd i h')
    · have ht' : c.taken = false := by simpa using ht
      simp only [ht', Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨σ', hph⟩, rfl, rfl, hO, hD⟩ := h
      refine ⟨[], le_rfl, by simp, List.Pairwise.nil, fun rd ho _ => hO rd ho, fun rd _ _ _ _ => ?_⟩
      refine ⟨[.phantom c.f σ'], ?_, by rw [Tree.BufsOkKids, Tree.BufsOk]; exact ⟨trivial, by rw [Tree.BufsOkKids]; trivial⟩,
        ?_, by rw [endL_one, endA_phantom], by rw [Tree.blockLast, Tree.block],
        by rw [posL_one, placedKidsA_cons]; exact ⟨placedA_phantom, placedKidsA_nil⟩,
        by rw [posL_one, loadsInKidsA_cons]; exact ⟨loadsInA_phantom, loadsInKidsA_nil⟩,
        by rw [posL_one, hintsInKids_cons]; exact ⟨hintsIn_phantom, hintsInKids_nil⟩,
        fun i hi => Or.inl (hD i hi)⟩
      · rw [Tree.KidsValid]; simp only [ht', Bool.false_eq_true, ↓reduceIte]
        exact ⟨rfl, ⟨⟨c.f, σ', rfl⟩, hph⟩, by rw [Tree.KidsValid]; trivial⟩
      · cases Qs with
        | nil => simp [KidsPost]
        | cons Q Qs => exact kidsPost_cons.mpr ⟨fun h => absurd h ht, by cases Qs <;> simp [KidsPost]⟩
  | c :: c' :: cs, O, Dacc, Qs, cur, e, Bt, Oend, Dend, htl, h => by
    rw [KidsAtL] at h
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at h
      obtain ⟨Bc, ec, Rc, Dc, Oc, hR, ⟨Wc, hWc, hce, hOc, hrc⟩, hrest⟩ := h
      have hb := le_allocBase (al c.f) cur
      obtain ⟨Wr, hle, hin, hdisj, hO, hr⟩ := kidsAtL_words (c' :: cs) _ _ _ ec e Bt Oend Dend (by omega) hrest
      refine ⟨Wc ++ Wr, by omega, fun q hq => ?_, ?_, fun rd ho hw => ?_, fun rd hl hp ho hw => ?_⟩
      · rcases List.mem_append.mp hq with hq | hq
        · rcases hWc.1 q hq with h' | h'
          · exact Or.inr ⟨by omega, by omega⟩
          · exact Or.inr ⟨by omega, by omega⟩
        · rcases hin q hq with h' | h'
          · exact Or.inl h'
          · exact Or.inr ⟨by omega, h'.2⟩
      · refine List.pairwise_append.mpr ⟨hWc.2, hdisj, fun q hq q' hq' => ?_⟩
        rcases hWc.1 q hq with h' | h' <;> rcases hin q' hq' with h'' | h'' <;> omega
      · obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hw
        exact hO rd ⟨ho, hOc rd hw1⟩ hw2
      · obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hw
        obtain ⟨t, hn, hv, hbt, hbl, hend, hpl, hlo, hhi, hd, hq⟩ := hrc rd hl hw1 ⟨hp, ho⟩
        obtain ⟨ts, hvs, hbs, hqs, hends, hblks, hpls, hlos, hhis, hDs⟩ := hr rd hl hp ⟨ho, hOc rd hw1⟩ hw2
        have hpos : posL fs coreProgram.loop al tl cur (t :: ts) =
            (allocBase (al c.f) cur, allocBase (al c.f) cur + Bc) :: posL fs coreProgram.loop al tl ec ts := by
          obtain ⟨t', ts', rfl⟩ : ∃ t' ts', ts = t' :: ts' := by
            cases ts with
            | nil => simp [Tree.KidsValid] at hvs
            | cons t' ts' => exact ⟨t', ts', rfl⟩
          rw [posL_cons, hn, hbl, hend]
        have hne : ts ≠ [] := by
          rintro rfl; simp [Tree.KidsValid] at hvs
        have hdat : ∀ i, Tree.DataKidsA coreProgram fs al cert (posL fs coreProgram.loop al tl cur (t :: ts)) (t :: ts) i ↔
            t.DataA coreProgram fs al cert (allocBase (al c.f) cur, allocBase (al c.f) cur + Bc) i ∨
              Tree.DataKidsA coreProgram fs al cert (posL fs coreProgram.loop al tl ec ts) ts i := fun i => by
          rw [hpos, dataKidsA_cons]
        have hreg : ∀ i, KRegL (fs := fs) (al := al) (cert := cert) R (fun i => Dacc i ∨ Dc i) tl ec ts i →
            KRegL (fs := fs) (al := al) (cert := cert) R Dacc tl cur (t :: ts) i := fun i hi => by
          unfold KRegL at hi ⊢
          rw [hdat]
          rcases hi with hi | (hi | hi) | hi
          · exact Or.inl hi
          · exact Or.inr (Or.inl hi)
          · exact Or.inr (Or.inr (Or.inl (hd i hi)))
          · exact Or.inr (Or.inr (Or.inr hi))
        have hregc : ∀ i, Rc i → KRegL (fs := fs) (al := al) (cert := cert) R Dacc tl cur (t :: ts) i :=
          fun i hi => (hR i hi).elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
        obtain ⟨t', ts', rfl⟩ : ∃ t' ts', ts = t' :: ts' := by
          cases ts with
          | nil => exact absurd rfl hne
          | cons t' ts' => exact ⟨t', ts', rfl⟩
        refine ⟨t :: t' :: ts', ?_, ⟨hbt, hbs⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
        · rw [Tree.KidsValid]; simp only [ht, ↓reduceIte]; exact ⟨hn, hv, hvs⟩
        · cases Qs with
          | nil => simp [KidsPost]
          | cons Q Qs => exact kidsPost_cons.mpr ⟨fun _ => hq, hqs⟩
        · rw [endL_cons, hn, hbl, hend]; exact hends
        · rw [Tree.blockLast]; exact hblks
        · rw [hpos, placedKidsA_cons]; exact ⟨hpl, hpls⟩
        · have hl' := loadsInKidsA_mono _ _ hreg hlos
          rw [hpos, loadsInKidsA_cons]
          exact ⟨loadsInA_mono t _ (fun i hi => hregc i hi) hlo, hl'⟩
        · have hh' := hintsInKids_mono _ _ hreg hhis
          rw [hpos, hintsInKids_cons]
          exact ⟨hintsIn_mono t _ (fun i hi => hregc i hi) hhi, hh'⟩
        · rw [hdat]
          rcases hDs i hi with (hi | hi) | hi
          · exact Or.inl hi
          · exact Or.inr (Or.inl (hd i hi))
          · exact Or.inr (Or.inr hi)
    · have ht' : c.taken = false := by simpa using ht
      simp only [ht', Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨σ', hph⟩, hrest⟩ := h
      have hb := le_allocBase (al c.f) cur
      obtain ⟨Wr, hle, hin, hdisj, hO, hr⟩ :=
        kidsAtL_words (c' :: cs) _ _ _ (allocBase (al c.f) cur + fs (tailKey c.f)) e Bt Oend Dend (by omega) hrest
      refine ⟨Wr, by omega, fun q hq => ?_, hdisj, hO, fun rd hl hp ho hw => ?_⟩
      · rcases hin q hq with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨by omega, h'.2⟩
      obtain ⟨ts, hvs, hbs, hqs, hends, hblks, hpls, hlos, hhis, hDs⟩ := hr rd hl hp ho hw
      obtain ⟨t', ts', rfl⟩ : ∃ t' ts', ts = t' :: ts' := by
        cases ts with
        | nil => simp [Tree.KidsValid] at hvs
        | cons t' ts' => exact ⟨t', ts', rfl⟩
      have hblk : (Tree.phantom c.f σ').block fs coreProgram.loop = fs (tailKey c.f) := by rw [Tree.block]
      have hpos : posL fs coreProgram.loop al tl cur (.phantom c.f σ' :: t' :: ts') =
          (allocBase (al c.f) cur, allocBase (al c.f) cur + fs (tailKey c.f)) ::
            posL fs coreProgram.loop al tl (allocBase (al c.f) cur + fs (tailKey c.f)) (t' :: ts') := by
        rw [posL_cons, Tree.name, hblk, endA_phantom]
      have hdat : ∀ i, Tree.DataKidsA coreProgram fs al cert (posL fs coreProgram.loop al tl cur (.phantom c.f σ' :: t' :: ts'))
          (.phantom c.f σ' :: t' :: ts') i ↔ Tree.DataKidsA coreProgram fs al cert
            (posL fs coreProgram.loop al tl (allocBase (al c.f) cur + fs (tailKey c.f)) (t' :: ts')) (t' :: ts') i :=
        fun i => by rw [hpos, dataKidsA_cons]; simp [dataA_phantom]
      refine ⟨.phantom c.f σ' :: t' :: ts', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
      · rw [Tree.KidsValid]; simp only [ht', Bool.false_eq_true, ↓reduceIte]
        exact ⟨rfl, ⟨⟨c.f, σ', rfl⟩, hph⟩, hvs⟩
      · rw [Tree.BufsOkKids, Tree.BufsOk]; exact ⟨trivial, hbs⟩
      · cases Qs with
        | nil => simp [KidsPost]
        | cons Q Qs => exact kidsPost_cons.mpr ⟨fun h => absurd h ht, hqs⟩
      · rw [endL_cons, Tree.name, hblk, endA_phantom]; exact hends
      · rw [Tree.blockLast]; exact hblks
      · rw [hpos, placedKidsA_cons]; exact ⟨placedA_phantom, hpls⟩
      · rw [hpos, loadsInKidsA_cons]
        refine ⟨loadsInA_phantom, loadsInKidsA_mono _ _ (fun i hi => ?_) hlos⟩
        unfold KRegL at hi ⊢; rw [hdat]; exact hi
      · rw [hpos, hintsInKids_cons]
        refine ⟨hintsIn_phantom, hintsInKids_mono _ _ (fun i hi => ?_) hhis⟩
        unfold KRegL at hi ⊢; rw [hdat]; exact hi
      · rw [hdat]; exact hDs i hi

/-- **A loop helper's node completes placed**: `callAtA_node` with its last callee, its tail call,
at the next frame `fp + fs f`, its block `fs f + Bt`. -/
theorem callAtA_nodeL {k : ℕ} {f : String} {args rets : List E} {R D : ℕ → Prop} {Out Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fp c e Bt : ℕ} (hlp : coreProgram.loop f = true) (hfc : fp + (fs f + Bt) ≤ c)
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
      KidsAtL fs al cert k σ (fun i => R i ∨ ownData cert fp c f (allocs σ es) es i) Pre (fp + fs f)
        (fun rd => HoldsWords rd Wo) (fun _ => False) Qs (calls es) (c + (allocs σ es).sum) e Bt Oend Dend ∧
      (∀ rd, Oend rd → Out rd) ∧
      (∀ rd, LowDef k rd → Pre rd → Oend rd → ∀ ev ∈ es, ev.Holds rd σ) ∧
      ∀ rd ts, LowDef k rd → Pre rd → Oend rd → Tree.KidsValid coreProgram rd σ (calls es) ts →
        KidsPost rd Qs (calls es) ts → Post rd (.node f σ (allocs σ es) ts)) :
    CallAtA fs al cert k f args rets R D Out Pre Post (fs f + Bt) fp c e := by
  obtain ⟨σ, fn, es, vs, Wo, Qs, Oend, Dend, hf, hpar, hw, hret, hnode, hWo, hlo, hhi, hD, hk, hout, hev,
    hpost⟩ := h
  set bufs := allocs σ es with hbufs
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
    obtain ⟨ts, hvs, hbs, hqs, hends, hblks, hpls, hlos, hhis, hDs⟩ := hr rd hl hp hw1 hw2
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
    refine ⟨.node f σ bufs ts, rfl, ⟨fn, hf, hpar, es, vs, hw, hret, hev rd hl hp hOe, hvs⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, fun i hi => ?_, hpost rd ts hl hp hOe hvs hqs⟩
    · rw [Tree.BufsOk, hev']; exact ⟨rfl, hbs⟩
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
