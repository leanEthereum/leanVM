/-
  LeanVM.Guest.Backend.Complete.FrameInst

  What the walk's instance takes of a compiled program's scoped function with temporaries apart:
  the facts of `Inst.Ok` that do not depend on the path, and `OpOK` from them.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameOp
public import LeanVM.Guest.Backend.Complete.Tmps
public import LeanVM.Guest.Backend.Complete.InFrameFn
public import LeanVM.Guest.Backend.Complete.Fn

/-!
# The walk's instance of a compiled program's function

For `tf` placed as `pf` in a compiled program, scoped and with temporaries apart: a `SET`
constant's word is its word (`instOf_kconst`); an instruction of the placement naming a
temporary's cell is that temporary's `DEREF` (`instOf_tops`, from `TmpsApart.ops`); a temporary's
`DEREF` reads through no temporary's cell (`instOf_tptr`); every cell is past the header and the
instructions' cells are in the frame (`placeFn_inFrame`, `placeFn_ops_inFrame`). Hence `OpOK` with
the path's facts only (`opOK_of`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable {κ₀ : ℕ} {W : World κ₀} {tf : TracedFn} {pf : Placed} {fp : ℕ} {hdr : E × E}
  {σ : Val} {es : List Ev}

/-- **A `SET` constant's word is its word.** -/
theorem instOf_kconst (x y : ℕ) :
    (instOf W tf pf fp hdr σ es).kw (.const x y) = Guest.word x y := rfl

/-- **An instruction of the placement naming a temporary's cell is a `DEREF` into it at offset
`0`, through a cell through which no `DEREF` stores the frame pointer.** -/
theorem instOf_tops (hta : TmpsApart tf pf) :
    ∀ c, (instOf W tf pf fp hdr σ es).tc c → ∀ o ∈ (instOf W tf pf fp hdr σ es).ops,
      c ∈ opCells o → ∃ p, o = .deref p 0 c .cell ∧
        ∀ q off d, LOp.deref q off d .fp ∈ (instOf W tf pf fp hdr σ es).ops → q ≠ p := by
  rintro c ⟨t, ht, hc⟩ o ho hco
  obtain ⟨p, rfl, -, hq⟩ := hta.ops ht hc ho hco
  exact ⟨p, rfl, hq⟩

/-- **A temporary's `DEREF` reads through no temporary's cell.** -/
theorem instOf_tptr (hta : TmpsApart tf pf) :
    ∀ o ∈ blockOps pf.fn.body 0, ∀ p off d, o = .deref p off d .cell →
      (instOf W tf pf fp hdr σ es).tc d → ¬ (instOf W tf pf fp hdr σ es).tc p := by
  rintro o ho p off d rfl ⟨t, ht, hc⟩ ⟨t', ht', hc'⟩
  obtain ⟨p', he, hnt, -⟩ := hta.ops ht hc ho (by simp [opCells])
  simp only [LOp.deref.injEq] at he
  obtain ⟨rfl, -, -, -⟩ := he
  exact hnt t' ht' hc'

/-- **A value the body names or takes, placed at a temporary's cell, is a temporary**: none is. -/
theorem instOf_tsep (hta : TmpsApart tf pf) :
    ∀ v n, v ∈ (instOf W tf pf fp hdr σ es).named → cellP pf.locs v = some n →
      (instOf W tf pf fp hdr σ es).tc n → v ∈ (instOf W tf pf fp hdr σ es).tmps := by
  intro v n hv hn htc
  obtain ⟨t, ht, hc⟩ := htc
  have hl : pf.locs[v]? = some (.cell n) := by
    unfold cellP at hn
    split at hn
    · next m hm => cases hn; exact hm
    · cases hn
  exact absurd hc (hta.apart hv hl ht)

/-- A function past the first keeps its frame size when `main`'s frame takes the tables. -/
theorem withTables_keep {fns pre post : List Lowered} {f : Lowered} (slots : Array KVal)
    (h : fns = pre ++ f :: post) (hpre : pre ≠ []) :
    ∃ pre', (withTables fns slots).1 = pre' ++ f :: post := by
  subst h
  cases pre with
  | nil => exact absurd rfl hpre
  | cons m pre =>
      simp only [List.cons_append, withTables]
      split
      · exact ⟨m :: pre, rfl⟩
      · exact ⟨_ :: _ :: pre, rfl⟩

/-- **A registered loop helper's frame in the layout is its placed frame**: `main` comes first
and is no loop helper, so its frame alone takes the tables. -/
theorem frame_of_loopH (hW : W.Compiled) (htf : tf ∈ W.p) (hpa : World.PlacedAs W tf pf)
    (hreg : ((loopTable W.p)[tf.core.name]?).any (·.registered) = true) :
    (World.cplSite W tf.core.name).frame = pf.fn.frameSize := by
  obtain ⟨placed, tables, hpp, hfns, -, -⟩ := lowerProgram_ok hW.1
  obtain ⟨hmain, -, hnd, hml, hpf⟩ := placeProgram_ok hpp
  obtain ⟨-, hall⟩ := placeFns_spec _ _ hpf
  obtain ⟨hlen, hget⟩ := forall₂_getElem hall
  have hplaced : W.placed = placed := by simp [World.placed, hpp]
  obtain ⟨hmem, hname⟩ := hpa
  rw [hplaced] at hmem
  obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hmem
  have hi : i < W.p.length := hlen ▸ hi'
  obtain ⟨ti, ti', hplace, -⟩ := hget i hi hi'
  have hpn := placeFn_name hplace
  obtain rfl : W.p[i] = tf :=
    eq_of_name hnd (List.getElem_mem hi) htf (by rw [← hpn.1, hname])
  have hi0 : i ≠ 0 := by
    rintro rfl
    have h0 : W.p[0].core.name = "main" := by
      rw [List.head?_map, List.head?_eq_getElem?, List.getElem?_eq_getElem hi] at hmain
      simpa using hmain
    rw [h0, hml] at hreg
    cases hreg
  have hsplit : W.fns = (placed.take i).map (fun pf => (emitFn pf.fn).1) ++
      (emitFn placed[i].fn).1 :: (placed.drop (i + 1)).map (fun pf => (emitFn pf.fn).1) := by
    have e : placed = placed.take i ++ placed[i] :: placed.drop (i + 1) := by
      rw [← List.drop_eq_getElem_cons hi', List.take_append_drop]
    rw [hfns]
    conv_lhs => rw [e]
    rw [List.map_append, List.map_cons]
  have hpre : (placed.take i).map (fun pf => (emitFn pf.fn).1) ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff, List.take_eq_nil_iff, not_or]
    exact ⟨hi0, List.ne_nil_of_length_pos (by omega)⟩
  obtain ⟨pre', hs'⟩ := withTables_keep W.slots hsplit hpre
  have hfr := layout_frame (withTables W.fns W.slots).2 (World.nodup hW) hs'
  have hn : (emitFn placed[i].fn).1.name = W.p[i].core.name := hpn.1
  show W.layout.frame.getD W.p[i].core.name 0 = placed[i].fn.frameSize
  rw [World.layout, layoutOf, KMap.getD_eq_getD_getElem?, ← hn, hfr]
  rfl

/-- **The walk's instance of a compiled program's function**, temporaries apart, on a path whose
events hold on some reader, is good. -/
theorem instOf_ok (hW : W.Compiled) (htf : tf ∈ W.p) (hpa : World.PlacedAs W tf pf)
    (hta : TmpsApart tf pf) (hrd : ∃ rd, (instOf W tf pf fp hdr σ es).Rd rd) :
    (instOf W tf pf fp hdr σ es).Ok where
  rd := hrd
  kconst := instOf_kconst
  ksize := fun hreg => by
    have hfr := frame_of_loopH hW htf hpa hreg
    obtain ⟨pre, post, f, hat⟩ := fnAt_of_placedAs hW htf hpa
    obtain ⟨ti, ti', hpl, -⟩ := hat.placed
    have hlt : pf.fn.frameSize < u128Bound := by
      have := (placeFn_name hpl).2
      unfold u128Bound
      omega
    show OffsetInstruction.immediateWord (W.layout.pow (World.cplSite W tf.core.name).frame) 0 =
      ofK (addressOfIndex pf.fn.frameSize)
    rw [hfr]
    have hp : W.layout.PowOk := layout_gpow _ _
    exact Layout.immediateWord_pow hp hlt
  tsep := instOf_tsep hta
  tops := instOf_tops hta
  kend := by
    have hsize : W.layout.sentinel = 2 ^ W.logSize - 1 := by
      have h2 := hW.2
      rw [assemble_def, assembleAt_size] at h2
      rw [World.layout, layoutOf, layout_sentinel, h2]
    have hlt : 2 ^ W.logSize - 1 < u128Bound := by
      have := W.logSize_le
      unfold u128Bound
      omega
    have hp : W.layout.PowOk := layout_gpow _ _
    show IsInK (OffsetInstruction.immediateWord (W.layout.pow W.layout.sentinel) 0)
    rw [hsize, Layout.immediateWord_pow hp hlt]
    exact (isInK_iff _).mpr ⟨_, rfl⟩

/-- **The placement of a function of a compiled program**, scoped: every cell past the header,
the instructions' cells in the frame. -/
theorem placed_cells (hW : W.Compiled) (htf : tf ∈ W.p) (hpa : World.PlacedAs W tf pf)
    (hsc : Scoped tf) :
    (∀ v n, cellP pf.locs v = some n → 2 ≤ n) ∧
      OpsBelow pf.fn.frameSize (blockOps pf.fn.body 0) := by
  obtain ⟨pre, post, f, hat⟩ := fnAt_of_placedAs hW htf hpa
  obtain ⟨ti, ti', hpl, -⟩ := hat.placed
  exact ⟨fun v n h => (placeFn_inFrame _ _ _ _ _ _ hpl hsc v n h).1, placeFn_ops_inFrame hpl hsc⟩

/-- **The walk's instance gives its straight-line instructions' words**, for a scoped function of
a compiled program with temporaries apart, on a path. -/
theorem opOK_of (hW : W.Compiled) (htf : tf ∈ W.p) (hpa : World.PlacedAs W tf pf)
    (hsc : Scoped tf) (hta : TmpsApart tf pf) {vs : List V} (hw : walk σ tf.core.body = .ret es vs)
    (hok : (instOf W tf pf fp hdr σ es).Ok) (kfps : List ℕ) :
    OpOK (World.cplSite W tf.core.name) (instOf W tf pf fp hdr σ es)
      (fun σ' Ψ kh => AgOf W tf fp σ' es kfps hdr ⟨patchT (instOf W tf pf fp hdr σ es) Ψ σ', kh⟩
        pf.fn.frameSize) (calls es) :=
  have hc := placed_cells hW htf hpa hsc
  opOK_instOf kfps hok hta hw hc.2 hc.1 (instOf_tptr hta) hta.inj

end
end LeanVM.Guest.Backend.Complete
