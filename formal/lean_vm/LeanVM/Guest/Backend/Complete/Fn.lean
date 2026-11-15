/-
  LeanVM.Guest.Backend.Complete.Fn

  The emitted code of every function of a compiled program runs where its path's instructions
  hold: `fnComplete`, `FnCompleteStmt`.
-/

module

public import LeanVM.Guest.Backend.Complete.Run
public import LeanVM.Guest.Backend.Sound.Main

/-!
# The run of a function

`fnComplete` closes emission's completeness over a compiled program: a function's placement is
one of the program's (`fnAt_of_placedAs`), its code is loaded at its entry in the program's own
site (`cplSite_eq`, `loaded_of_assemble`), its body's instructions are its placed body's
(`FnAt.code`), so `block_runs` runs it; the body ends at the frame's return or, for `main`, at
the closing jump, whose target is the final registers (`halt_final`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (RunC)

@[expose] public section

variable {κ : ℕ} {W : World κ}

/-- **The program's placement of a function is a function of the compiled program**, its code
and slots as `FnAt` says. -/
theorem fnAt_of_placedAs (hW : W.Compiled) {tf : TracedFn} {pf : Placed} (htf : tf ∈ W.p)
    (hpa : World.PlacedAs W tf pf) : ∃ pre post f, FnAt W tf pf pre post f := by
  obtain ⟨placed, tables, hpp, hfns, hfill, hshared⟩ := lowerProgram_ok hW.1
  obtain ⟨-, -, hnd, -, hpf⟩ := placeProgram_ok hpp
  obtain ⟨-, hall⟩ := placeFns_spec _ _ hpf
  obtain ⟨hlen, hget⟩ := forall₂_getElem hall
  have hplaced : W.placed = placed := by simp [World.placed, hpp]
  obtain ⟨hmem, hname⟩ := hpa
  rw [hplaced] at hmem
  obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hmem
  have hi : i < W.p.length := hlen ▸ hi'
  obtain ⟨ti, ti', hplace, hle⟩ := hget i hi hi'
  have hpn := placeFn_name hplace
  obtain rfl : W.p[i] = tf :=
    eq_of_name hnd (List.getElem_mem hi) htf (by rw [← hpn.1, hname])
  have hsplit : W.fns = (placed.take i).map (fun pf => (emitFn pf.fn).1) ++
      (emitFn placed[i].fn).1 :: (placed.drop (i + 1)).map (fun pf => (emitFn pf.fn).1) := by
    have e : placed = placed.take i ++ placed[i] :: placed.drop (i + 1) := by
      rw [← List.drop_eq_getElem_cons hi', List.take_append_drop]
    rw [hfns]
    conv_lhs => rw [e]
    rw [List.map_append, List.map_cons]
  obtain ⟨pre', f', hs', hname', hcode, -, hframe⟩ := withTables_split W.slots hsplit
  refine ⟨pre', _, f', List.getElem_mem hi, ⟨ti, ti', hplace, hshared.of_le hle⟩, hs', ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hname']
    exact hpn.1
  · rw [hcode]
    exact emitFn_ops _
  · intro x hx
    refine hfill x ?_
    simp only [fillsOf, List.mem_flatMap]
    refine ⟨placed[i], List.getElem_mem hi', ?_⟩
    rw [emitFn_fills, hpn.1]
    exact hx
  · have : (emitFn placed[i].fn).1.frameSize = placed[i].fn.frameSize := rfl
    have := hpn.2
    omega
  · have hnd' : (placed.map (·.fn.name)).Nodup := by rw [forall₂_names hall]; exact hnd
    have := find?_of_nodup (fun pf : Placed => pf.fn.name) placed placed[i] hnd'
      (List.getElem_mem hi')
    simp only [World.locs, hplaced]
    rw [← hpn.1, this]

/-- A function's site in the program is the one its code is loaded at. -/
theorem cplSite_eq (hW : W.Compiled) {tf : TracedFn} {pf : Placed} {pre post : List Lowered}
    {f : Lowered} (hat : FnAt W tf pf pre post f) :
    World.cplSite W tf.core.name =
      siteOf W.L W.fns W.slots pre f (fun _ _ => True) (fun _ _ => True) := by
  obtain ⟨hent, -, -⟩ := hat.entry hW
  have hfr : W.layout.frame.getD tf.core.name 0 = f.frameSize := by
    have := layout_frame (withTables W.fns W.slots).2 (World.nodup hW) hat.split
    rw [World.layout, layoutOf, KMap.getD_eq_getD_getElem?, ← hat.name, this]
    rfl
  unfold World.cplSite siteOf
  rw [hent, hfr]
  rfl

/-- `main`'s closing jump goes to the halting slot. -/
theorem halt_final (hW : W.Compiled) {d : E}
    (hd : d = OffsetInstruction.immediateWord (W.layout.pow W.layout.sentinel) 0) :
    d.limb 0 = W.prog.pcFinal := by
  have hsize : W.layout.sentinel = 2 ^ W.logSize - 1 := by
    have h2 := hW.2
    rw [assemble_def, assembleAt_size] at h2
    rw [World.layout, layoutOf, layout_sentinel, h2]
  have hlt : 2 ^ W.logSize - 1 < u128Bound := by
    have := W.logSize_le
    unfold u128Bound
    omega
  have hp : W.layout.PowOk := layout_gpow _ _
  rw [hd, hsize, Layout.immediateWord_pow hp hlt, limb_ofK]
  rfl

/-- **The emitted code of a function runs**, counted, where its path's instructions hold. -/
theorem fnComplete (hW : W.Compiled) {tf : TracedFn} (htf : tf ∈ W.p) : World.FnComplete W tf := by
  intro pf hpa fp hmain σ kids hcb
  obtain ⟨pre, post, f, hat⟩ := fnAt_of_placedAs hW htf hpa
  have hL := loaded_of_assemble W.L (World.nodup hW) hat.split W.hl hW.2 (fun _ _ => True)
    (fun _ _ => True)
  rw [← cplSite_eq hW hat] at hL
  have hcode : CodeAt (opsOf f.code) 0 (blockOps pf.fn.body 0) := by
    rw [hat.code]
    exact codeAt_self _
  obtain ⟨c, ks', hc, halt⟩ := block_runs (σ := σ) (fp := addressOfIndex fp) hL pf.fn.body
    tf.core.body 0 kids _ _ _ _ hcode hcb
  have hcnt : ∀ op, c op ≤ pathOps σ tf pf op + (kids.map (·.2 op)).sum := fun op => by
    have := hc op
    unfold ksum at this
    unfold pathOps
    omega
  rcases halt with ⟨-, -, hn⟩ | ⟨-, -, -, -, hk⟩ | ⟨r, hr, hrr, hk⟩ | ⟨d, f', hr, hd, hf, hk⟩
  · exact hn.elim
  · exact hk.elim
  · refine ⟨r, c, ?_, hr, hcnt⟩
    simp only [hk, ↓reduceIte]
    exact hrr
  · refine ⟨_, c, ?_, hr, hcnt⟩
    simp only [hk, ↓reduceIte]
    obtain rfl := hmain hk
    rw [hf]
    simp only [Registers.final, halt_final hW hd, limb_ofK, fpFinal]
    simp

/-- **`fnComplete`, for every function of every compiled program.** -/
theorem fnCompleteStmt : FnCompleteStmt := fun _ hW _ htf => fnComplete hW htf

end

/-- info: 'LeanVM.Guest.Backend.Complete.fnCompleteStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Complete.fnCompleteStmt

end LeanVM.Guest.Backend.Complete
