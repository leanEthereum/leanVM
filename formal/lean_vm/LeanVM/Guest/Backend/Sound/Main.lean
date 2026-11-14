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
  obtain ⟨hmain, hjt, hnd, -, hpf⟩ := placeProgram_ok hpp
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

/-- **Parameter `k` of a function is the word of its frame's cell `2 + k`**, at every frame. -/
theorem World.params_vf (hW : W.Compiled) {tf : TracedFn} (htf : tf ∈ W.p) (fp : K) :
    tf.core.params.map (W.vf tf.core.name fp) = frameWords W.L fp 2 (sigOf tf).1 := by
  obtain ⟨pf, pre, post, f, hat⟩ := fnAt_of_mem hW htf
  obtain ⟨ti, ti', hplace, -⟩ := hat.placed
  obtain ⟨st', hrun, rfl, -, -, -, -⟩ := placeFn_ok hplace
  have hp := placeBody_params W.L rfl hrun
  rw [World.vf, hat.locs]
  apply List.ext_getElem (by simp [frameWords, sigOf])
  intro k h1 _
  have hk : k < tf.core.params.length := by simpa using h1
  simp only [List.getElem_map, frameWords, List.getElem_range]
  exact valP_of_cell (hp k hk)

/-! ## A function's body from a run -/

/-- **A run entering a function makes its core body hold**: with every contract for runs no
longer than it, the jump tables written and the function's obligations, a halting run from the
function's entry at a frame satisfies the core body under the valuation by places; where the
body returns, the frame's return cells hold the returned words and (but in `main`) the run went
on from the frame's return registers. -/
theorem body_of_run (hW : W.Compiled) {tf : TracedFn} (htf : tf ∈ W.p)
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
  obtain ⟨hparams, hbody⟩ := placeFn_sound pf ti' hplace _ fp W.C W.U W.slots True
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
program, its obligations holding. -/
theorem fn_sound (hW : W.Compiled) (hκ : κ < 64) {tf : TracedFn} (htf : tf ∈ W.p)
    (hne : tf.core.name ≠ "main") (hobl : W.Obligations tf) : W.FnSound tf := by
  intro n hC fp k hk hpre hs
  have hpre' := hpre
  obtain ⟨-, hjt, tf', htf', hname, hself, hU⟩ := hpre
  obtain rfl := eq_of_name (World.names hW).2.1 htf' htf hname
  obtain ⟨hparams, hbody⟩ := body_of_run hW htf hobl hjt (fun h => absurd h hne) hself hU hC
    (Nat.le_of_lt_succ hk) hs
  obtain ⟨rs, -, hback⟩ := (holdsList_reach _ hbody).resolve_left id
  obtain ⟨k', hk', rg, hr, hs'⟩ := hback.resolve_left hne
  exact ⟨k', hk', rg, hr, ⟨tf', htf, rfl, ⟨hparams, holdsList_mono (fun _ _ _ h => h) _ id
    (fun _ h => h.1) hbody⟩, inMem_of_retRegs hκ hr, hpre', hs.2, tf', htf, rfl, rfl, rfl⟩, hs'⟩

/-- A function with no `match` and no `dispatch`, nothing asked of the callers (`U` true), is
compiled correctly with no obligation: the hypotheses of `fn_sound` are met. -/
theorem fn_sound_plain (hW : W.Compiled) (hκ : κ < 64) {tf : TracedFn} (htf : tf ∈ W.p)
    (hne : tf.core.name ≠ "main") (hU : ∀ f a, W.U f a)
    (hsel : selFreeList tf.core.body = true) : W.FnSound tf :=
  fn_sound hW hκ htf hne fun _ _ _ => oblList_of_selFree hU _ _ hsel trivial

/-! ## The whole program -/

/-- `main` is no loop helper. -/
theorem main_not_registered (hW : W.Compiled) : ¬W.registered "main" := by
  obtain ⟨placed, tables, hpp, -⟩ := lowerProgram_ok hW.1
  have := (placeProgram_ok hpp).2.2.2.1
  rw [World.registered, this]
  exact Bool.false_ne_true

/-- **`__jump_tables` writes the jump tables**: a run from `(g^0, 1)` reaches `main`'s entry at
frame `1` with every slot of the tables written. -/
theorem jt_of_run (hW : W.Compiled) {k : ℕ}
    (hs : SafeReached W.prog W.L k ⟨addressOfIndex 0, 1⟩) :
    ∃ k' ≤ k, JTHolds W.L W.layout W.slots ∧
      SafeReached W.prog W.L k' ⟨addressOfIndex (W.ent "main"), 1⟩ := by
  obtain ⟨hn, hnd, -, hmain⟩ := World.names hW
  obtain ⟨m, rest, hfns⟩ : ∃ m rest, W.fns = m :: rest := by
    cases hf : W.fns with
    | nil =>
        rw [← hn, hf] at hmain
        cases hmain
    | cons m rest => exact ⟨m, rest, rfl⟩
  have hmname : m.name = "main" := by
    rw [← hn, hfns] at hmain
    simpa using hmain
  have hndw := World.nodup hW
  by_cases he : W.slots.isEmpty = true
  · have hsplit : (withTables W.fns W.slots).1 = [] ++ m :: rest := by
      rw [hfns]
      simp [withTables, he]
    have hentry := layout_entry (withTables W.fns W.slots).2 hndw hsplit
    have hent : W.ent "main" = 0 := by
      rw [World.ent, World.layout, layoutOf, Std.HashMap.getD_eq_getD_getElem?, ← hmname, hentry]
      rfl
    refine ⟨k, Nat.le_refl _, fun s kv w hsk _ => ?_, by rw [hent]; exact hs⟩
    have hsz : W.slots.size = 0 := by simpa using he
    have := (Array.getElem?_eq_some_iff.mp hsk).1
    omega
  · have hsplit0 : (withTables W.fns W.slots).1 = [] ++
        (⟨"__jump_tables", W.slots.zipIdx.map fun (kv, j) => (⟨.set (m.frameSize + j) kv, []⟩ : LInstr),
          m.frameSize + W.slots.size⟩ : Lowered) ::
          ({ m with frameSize := m.frameSize + W.slots.size } :: rest) := by
      rw [hfns]
      simp [withTables, he]
    have hbase : W.layout.tablesBase = m.frameSize := by
      rw [World.layout, layoutOf, layout_tablesBase, hfns]
      simp [withTables, he]
    have hentry := layout_entry (withTables W.fns W.slots).2 hndw
      (pre := [_]) (f := { m with frameSize := m.frameSize + W.slots.size }) (post := rest) hsplit0
    have hent : W.ent "main" = W.slots.size := by
      rw [World.ent, World.layout, layoutOf, Std.HashMap.getD_eq_getD_getElem?, ← hmname]
      rw [show m.name = ({ m with frameSize := m.frameSize + W.slots.size } : Lowered).name from rfl,
        hentry]
      simp [totalSize]
    have hL := loaded_of_assemble W.L hndw hsplit0 W.hl hW.2 W.Pre W.Post
    obtain ⟨k', hk', hseg, hs'⟩ := seg_run hL _ 0 k (fun o ho => by
      simp only [opsOf, List.mem_map, Array.mem_toList_iff, Array.mem_map] at ho
      obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := ho
      rfl) (codeAt_self _) (by simpa [SafeAt, siteOf, World.prog] using hs)
    refine ⟨k', by omega, fun s kv w hsk hw => ?_, ?_⟩
    · obtain ⟨hslt, rfl⟩ := Array.getElem?_eq_some_iff.mp hsk
      have := hseg s (by simpa [opsOf] using hslt)
      simp only [opsOf, List.getElem_map, Array.getElem_toList, Array.getElem_map,
        Array.getElem_zipIdx, siteOf, Nat.zero_add] at this
      rw [hbase]
      cases hkv : W.slots[s] with
      | «at» f i =>
          rw [hkv] at hw this
          cases hw
          simpa [Site.R, resolveOp, resolveK, Holds, World.layout] using this
      | entry f =>
          rw [hkv] at hw this
          cases hw
          simpa [Site.R, resolveOp, resolveK, Holds, World.layout] using this
      | _ =>
          rw [hkv] at hw
          cases hw
    · rw [hent]
      simpa [SafeAt, siteOf, opsOf, World.prog] using hs'

/-- **Every function's contract**, by induction on the steps left, every function's obligations
holding. -/
theorem contracts (hW : W.Compiled) (hκ : κ < 64) (hobl : ∀ tf ∈ W.p, W.Obligations tf)
    (g : String) : FunSpecReached W.prog W.L (W.ent g) (W.Pre g) (W.Post g) :=
  funSpecReached_induction (ι := String) (entry := W.ent) (P := W.Pre) (Q := W.Post)
    (fun n hn g fp k hk hpre hs => by
      have hpre' := hpre
      obtain ⟨hne, -, tf, htf, rfl, -⟩ := hpre
      exact fn_sound hW hκ htf hne (hobl tf htf) n hn fp k hk hpre' hs) g

/-- **(c) The program is compiled correctly**: on a memory where a run of the compiled program
from `(g^0, 1)` halts, every function's obligations holding, `main`'s core body holds at frame
`1` under the valuation by places, its calls located. -/
theorem program_sound (hW : W.Compiled) (hκ : κ < 64) (hobl : ∀ tf ∈ W.p, W.Obligations tf)
    (hU : ∀ tf ∈ W.p, tf.core.name = "main" → W.U "main" (frameWords W.L 1 2 (sigOf tf).1))
    {k : ℕ} (hs : Safe W.prog W.L k ⟨addressOfIndex 0, 1⟩) : W.MainHolds := by
  obtain ⟨-, -, -, hmain⟩ := World.names hW
  obtain ⟨tf, htf, hname⟩ : ∃ tf ∈ W.p, tf.core.name = "main" := by
    cases hp : W.p with
    | nil =>
        rw [hp] at hmain
        cases hmain
    | cons tf rest =>
        rw [hp] at hmain
        exact ⟨tf, List.mem_cons_self, by simpa using hmain⟩
  obtain ⟨k', -, hjt, hs'⟩ := jt_of_run hW ⟨hs, Reach.refl _⟩
  rw [← hname] at hs'
  obtain ⟨hparams, hbody⟩ := body_of_run hW htf (hobl tf htf) hjt (fun _ => rfl)
    (fun hreg => absurd (hname ▸ hreg) (main_not_registered hW)) (hname ▸ hU tf htf hname)
    (fun g => (contracts hW hκ hobl g).lt k') (Nat.le_refl _) hs'
  exact ⟨tf, htf, hname, hparams,
    holdsList_mono (fun _ _ _ h => h) _ id (fun _ h => h.1) hbody⟩

/-- **The whole program's relation**: a halting run makes `main`'s core relation hold of the
argument and return words of its frame, in the core IR's own semantics (`Core.Program.Rel`). -/
theorem program_rel (hW : W.Compiled) (h : W.MainHolds) :
    ∃ tf ∈ W.p, tf.core.name = "main" ∧ W.core.Rel W.L.read "main"
      (frameWords W.L 1 2 (sigOf tf).1) (frameWords W.L 1 (2 + (sigOf tf).1) (sigOf tf).2) := by
  obtain ⟨tf, htf, hname, hparams, hbody⟩ := h
  refine ⟨tf, htf, hname, ?_⟩
  have hfind : W.core.find? "main" = some tf.core := by
    have := find?_of_nodup (fun c : Core.Fn => c.name) (W.p.map (·.core)) tf.core
      (by rw [List.map_map]; exact (World.names hW).2.1) (List.mem_map_of_mem htf)
    rw [hname] at this
    exact this
  exact (rel_iff W.core "main" _ _).mpr ⟨tf.core, hfind, W.vf tf.core.name 1, hparams,
    holdsList_mono (relL_le_rel W.core) _ id (fun _ h => h) hbody⟩

/-- (c) for a valid execution of the compiled program. -/
theorem program_sound_valid (hW : W.Compiled) (hκ : κ < 64)
    (hobl : ∀ tf ∈ W.p, W.Obligations tf)
    (hU : ∀ tf ∈ W.p, tf.core.name = "main" → W.U "main" (frameWords W.L 1 2 (sigOf tf).1))
    {input : PublicInput} {steps : ℕ}
    (h : ValidExecution W.prog input ⟨κ, W.L, steps⟩) : W.MainHolds :=
  program_sound hW hκ hobl hU (safe_of_validExecution h)

/-! ## The statements -/

/-- **(b), for every program.** -/
theorem fnSound : FnSoundStmt :=
  fun _ hW hκ _ htf hne hobl => fn_sound hW hκ htf hne hobl

/-- **(c), for every program.** -/
theorem programSound : ProgramSoundStmt :=
  fun _ hW hκ hobl hU _ hs => program_sound hW hκ hobl hU hs

end
end LeanVM.Guest.Backend
