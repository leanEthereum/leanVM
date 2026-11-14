/-
  LeanVM.Guest.Backend.Sound.Main

  The back end is correct: per function and for the whole program.
-/

module

public import LeanVM.Guest.Backend.Sound.Program

/-!
# The back end's correctness
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {W : World κ}

/-! ## A compiled program's layout -/

theorem World.names (hW : W.Compiled) :
    W.fns.map (·.name) = W.p.map (·.core.name) ∧ (W.p.map (·.core.name)).Nodup ∧
      "__jump_tables" ∉ W.p.map (·.core.name) ∧ (W.p.map (·.core.name)).head? = some "main" := by
  obtain ⟨placed, tables, hpp, hfns, -, -⟩ := lowerProgram_ok hW.1
  obtain ⟨hmain, hjt, hnd, hpf⟩ := placeProgram_ok hpp
  obtain ⟨-, hall⟩ := placeFns_spec _ _ hpf
  refine ⟨?_, hnd, hjt, hmain⟩
  rw [hfns, ← forall₂_names hall, List.map_map]
  rfl

theorem World.nodup (hW : W.Compiled) : ((withTables W.fns W.slots).1.map (·.name)).Nodup := by
  obtain ⟨hn, hnd, hjt, -⟩ := World.names hW
  exact withTables_nodup W.slots (hn ▸ hnd) (hn ▸ hjt)

/-- A function's entry is the code before it, and its code ends before the halting slot. -/
theorem FnAt.entry (hW : W.Compiled) {tf : TracedFn} {pf : Placed} {pre post : List Lowered}
    {f : Lowered} (hat : FnAt W tf pf pre post f) :
    W.ent tf.core.name = totalSize pre ∧ totalSize pre + f.code.size ≤ 2 ^ W.logSize - 1 ∧
      f.code.size = blockSize pf.fn.body := by
  have hnd := World.nodup hW
  refine ⟨?_, (assemble_fetch hnd hat.split W.hl hW.2).2, ?_⟩
  · have := layout_entry (withTables W.fns W.slots).2 hnd hat.split
    rw [World.ent, World.layout, layoutOf, Std.HashMap.getD_eq_getD_getElem?, ← hat.name, this]
    rfl
  · have := congrArg List.length hat.code
    simpa only [opsOf_length, blockOps_length] using this

theorem World.logSize_le (W : World κ) : 2 ^ W.logSize ≤ 2 ^ 30 :=
  Nat.pow_le_pow_right (by decide) W.hl

/-- Two functions of one name are one. -/
theorem eq_of_name {p : List TracedFn} (hnd : (p.map (·.core.name)).Nodup) {tf tf' : TracedFn}
    (h : tf ∈ p) (h' : tf' ∈ p) (he : tf.core.name = tf'.core.name) : tf = tf' :=
  List.inj_on_of_nodup_map hnd h h' he

/-- The jump tables' slots are fewer than the bytecode's. -/
theorem World.slots_lt (hW : W.Compiled) (hne : W.fns ≠ []) : W.slots.size < 2 ^ 30 := by
  have h1 := slots_le_total W.slots hne
  have h2 := assemble_size_gt W.fns W.slots
  rw [hW.2] at h2
  have h3 := W.logSize_le
  split at h1
  · next he =>
    have : W.slots.size = 0 := by simpa using he
    omega
  · omega

/-- **What a function's code is given of the program around it** (`PlaceEnv`), the jump tables
written. -/
theorem placeEnv_of (hW : W.Compiled) {tf : TracedFn} {pf : Placed} {pre post : List Lowered}
    {f : Lowered} (hat : FnAt W tf pf pre post f) (hjt : JTHolds W.L W.layout W.slots) {fp : K}
    (hfp : tf.core.name = "main" → fp = 1) :
    PlaceEnv (siteOf W.L W.fns W.slots pre f W.Pre W.Post) fp
      (ctxOf (loopTable W.p) (sigTable W.p) tf) W.C W.U W.slots (blockSize pf.fn.body) := by
  obtain ⟨hn, hnd, -, -⟩ := World.names hW
  obtain ⟨hent, hfit, hsize⟩ := hat.entry hW
  have h30 := W.logSize_le
  have hne : W.fns ≠ [] := by
    intro h0
    have := hat.split
    simp [h0, withTables] at this
  refine ⟨layout_gpow _ _, hjt, hent, ?_, ?_, fun hm => hfp (eq_of_beq hm), ?_, ?_, ?_⟩
  · show totalSize pre + blockSize pf.fn.body < 2 ^ 128
    omega
  · show f.frameSize < 2 ^ 128
    have := hat.frame
    have := World.slots_lt hW hne
    omega
  · intro g a r hcal
    obtain ⟨-, tf', htf', hname, -⟩ := isCallee_get hcal
    obtain ⟨pf', pre', post', f', hat'⟩ := fnAt_of_mem hW htf'
    have := hat'.entry hW
    show W.ent g < 2 ^ 128
    rw [← hname, this.1]
    omega
  · intro g a r fp' hcal hself hU
    obtain ⟨hgm, tf', htf', hname, hsig⟩ := isCallee_get hcal
    refine ⟨hgm, hjt, tf', htf', hname, ?_, ?_⟩
    · rw [hsig]
      exact hself
    · rw [hsig]
      exact hU
  · intro g a r fp' hcal hpost
    obtain ⟨-, tf', htf', hname', hsig⟩ := isCallee_get hcal
    obtain ⟨tf'', htf'', hname'', hbody, hent'⟩ := hpost
    obtain rfl := eq_of_name hnd htf' htf'' (hname'.trans hname''.symm)
    rw [hsig] at hent'
    subst hname'
    refine (relL_iff W.core tf'.core.name _ _).mpr ⟨tf'.core, fp', ?_, hent', ?_, ?_⟩
    · have := find?_of_nodup (fun c : Core.Fn => c.name) (W.p.map (·.core)) tf'.core
        (by rw [List.map_map]; exact hnd) (List.mem_map_of_mem htf')
      exact this
    · have := hbody.1
      rw [hsig] at this
      exact this
    · have := hbody.2
      rw [hsig] at this
      exact this

/-! ## A function's body from a run -/

/-- **A run entering a function makes its core body hold**: with every contract for runs no
longer than it, the jump tables written and the function's obligations, a halting run from the
function's entry at a frame satisfies the core body under the valuation by places; where the
body returns, the frame's return cells hold the returned words and (but in `main`) the run went
on from the frame's return registers. -/
theorem body_of_run (hW : W.Compiled) {tf : TracedFn} (htf : tf ∈ W.p) (hnc : NoChain tf)
    (hobl : W.Obligations tf) (hjt : JTHolds W.L W.layout W.slots) {fp : K}
    (hfp : tf.core.name = "main" → fp = 1)
    (hself : W.registered tf.core.name → wd W.L fp (2 + (sigOf tf).1) = ofK fp)
    (hU : W.U tf.core.name (frameWords W.L fp 2 (sigOf tf).1)) {n : ℕ}
    (hC : ∀ g, FunSpecLtReached W.prog W.L n (W.ent g) (W.Pre g) (W.Post g)) {k : ℕ} (hk : k ≤ n)
    (hs : SafeReached W.prog W.L k ⟨addressOfIndex (W.ent tf.core.name), fp⟩) :
    tf.core.params.map (W.vf tf.core.name fp) = frameWords W.L fp 2 (sigOf tf).1 ∧
      Stmt.HoldsList W.C W.L.read (W.vf tf.core.name fp) tf.core.body False
        (fun rs => rs = frameWords W.L fp (2 + (sigOf tf).1) (sigOf tf).2 ∧
          (tf.core.name = "main" ∨ ∃ k' < k, ∃ rg, retRegs W.L fp = some rg ∧
            SafeReached W.prog W.L k' rg)) := by
  obtain ⟨pf, pre, post, f, hat⟩ := fnAt_of_mem hW htf
  obtain ⟨ti, ti', hplace, hshared⟩ := hat.placed
  obtain ⟨hent, -, -⟩ := hat.entry hW
  rw [hent] at hs
  have env := placeEnv_of hW hat hjt hfp
  have hsem := lowered_sound W.L (World.nodup hW) hat.split hat.code W.hl hW.2 W.Pre W.Post hC hk hs
    (next := True) (kj := fun _ _ => True)
    (kret := ∃ k' < k, ∃ rg, retRegs W.L fp = some rg ∧ SafeReached W.prog W.L k' rg)
    (khalt := fun _ _ => True) (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun k' hk' rg hr hs' => ⟨k', hk', rg, hr, hs'⟩) (fun _ _ _ _ _ => trivial)
  have hvf : W.vf tf.core.name fp = valP W.L fp pf.locs := by rw [World.vf, hat.locs]
  rw [hvf]
  obtain ⟨hparams, hbody⟩ := placeFn_sound hnc pf ti' hplace _ fp W.C W.U W.slots True
    (fun _ _ => True) _ (fun _ _ => True)
    (fun rs => rs = frameWords W.L fp (2 + (sigOf tf).1) (sigOf tf).2 ∧
      (tf.core.name = "main" ∨ ∃ k' < k, ∃ rg, retRegs W.L fp = some rg ∧
        SafeReached W.prog W.L k' rg)) env hat.fills hshared hself hsem
    (hvf ▸ hobl fp hfp hU) (fun h => ⟨rfl, h⟩)
  obtain ⟨-, -, -, -, -, -, vs, hvs⟩ := placeFn_ok hplace
  exact ⟨hparams, holdsList_ret_any hvs hbody⟩

/-- A frame whose return registers are read is in the memory. -/
theorem inMem_of_retRegs (hκ : κ < 64) {L : MemoryImage κ} {fp : K} {r : Registers K}
    (h : retRegs L fp = some r) : InMem κ fp := by
  obtain ⟨d, _, hd, -, -⟩ := retRegs_eq_some_iff.mp h
  obtain ⟨i, hi, -⟩ := (MemoryImage.read_eq_some_iff hκ L).mp hd
  exact ⟨i, i.isLt, by simpa [addressOfIndex] using hi⟩

/-- **(b) A function is compiled correctly**: for every function other than `main` of a compiled
program, on a trace with no `chain` event, its obligations holding. -/
theorem fn_sound (hW : W.Compiled) (hκ : κ < 64) {tf : TracedFn} (htf : tf ∈ W.p)
    (hne : tf.core.name ≠ "main") (hnc : NoChain tf) (hobl : W.Obligations tf) : W.FnSound tf := by
  intro n hC fp k hk hpre hs
  have hpre' := hpre
  obtain ⟨-, hjt, tf', htf', hname, hself, hU⟩ := hpre
  obtain rfl := eq_of_name (World.names hW).2.1 htf' htf hname
  obtain ⟨hparams, hbody⟩ := body_of_run hW htf hnc hobl hjt (fun h => absurd h hne) hself hU hC
    (Nat.le_of_lt_succ hk) hs
  obtain ⟨rs, -, hback⟩ := (holdsList_reach _ hbody).resolve_left id
  obtain ⟨k', hk', rg, hr, hs'⟩ := hback.resolve_left hne
  exact ⟨k', hk', rg, hr, ⟨tf', htf, rfl, ⟨hparams, holdsList_mono (fun _ _ _ h => h) _ id
    (fun _ h => h.1) hbody⟩, inMem_of_retRegs hκ hr, hpre', hs.2, tf', htf, rfl, rfl, rfl⟩, hs'⟩

end
end LeanVM.Guest.Backend
