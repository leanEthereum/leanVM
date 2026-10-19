/-
  LeanVM.Guest.B2C.B2

  B2's completeness: the compiled guest runs on the honest memory from `main`'s entry to the final
  registers, and a halting run executes at most the tree's instructions of each opcode.
-/

module

public import LeanVM.Guest.B2C.CplAll
public import LeanVM.Guest.B2C.Table
public import LeanVM.Guest.Sound
public import LeanVM.Guest.Memory.GuestMainFree

/-!
# B2's completeness

From each function's completeness check (`CplRun`, k5's) and what the honest memory's frames hold
(`FrameHolds`, k2's), by induction on the words a subtree allocates: every instance that runs
runs from its entry at its frame to its return registers (`main`: to the final registers), within
its subtree's weight at `pathMax · op`, leaving its returns after its arguments (`inst_runs`).
The callees' runs (`KidsRun`) are the induction's, each callee an instance at its callee frame
(`honest_kid`), never `main` (`calls_ne_main`). With the jump table's prologue
(`runC_jumpTables`, `jtSets`'s `SET`s), `b2_complete` and `b2_count` are `End`'s `b2` and
`count`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.End (mainEntry JumpTables)

@[expose] public section

/-- **What B2's completeness rests on**: each function's completeness check (`cplRun_of_ok`) and
the frames of the honest memory. -/
structure B2Hyps : Prop where
  run : ∀ j, 1 ≤ j → j < nFns → CplRun j
  frame : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ I ∈ honestInsts coreProgram fs H hdr T,
      ∀ f σ bufs kids, I.t = .node f σ bufs kids → ∀ j, idxOf f = some j → ∀ es vs,
        walk σ (coreOf j).body = .ret es vs →
          FrameHolds (honest coreProgram fs H C hdr T) j I.fp σ es vs I.kidFps I.hdr

/-- Each function's completeness check gives its run (`cplRun_of`). -/
theorem cplRun_of_ok (hok : ∀ j, 1 ≤ j → j < nFns → CplOk j) : ∀ j, 1 ≤ j → j < nFns → CplRun j :=
  fun j h1 h2 => cplRun_of h1 h2 (hok j h1 h2)

/-! ## Functions and their callees -/

/-- **No path calls `main`.** -/
theorem calls_ne_main {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {σ : Val}
    {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs) {c : Memory.Call} (hc : c ∈ calls es) :
    c.f ≠ "main" := by
  have hcc := walk_callees (σ := σ) fn.body (c := c) (by rw [hw]; exact hc)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hf)
  have h := mainFree_all j (by rw [coreProgram_length] at hj; exact hj)
  unfold mainFreeJ at h
  rw [List.getElem?_eq_getElem hj] at h
  simpa using List.all_eq_true.mp h c.f hcc

private theorem idxOf_main : idxOf "main" = some 1 := by decide +kernel

theorem idx_one_iff {f : String} {j : ℕ} (hj : idxOf f = some j) : j = 1 ↔ f = "main" := by
  constructor
  · rintro rfl
    obtain ⟨i, hi1, hi, hn, -⟩ := fn_of_idx hj
    obtain rfl : i = 0 := by omega
    subst hn
    exact (by decide +kernel : ∀ h : 0 < coreProgram.length, (coreProgram[0]'h).name = "main") hi
  · rintro rfl
    rw [idxOf_main] at hj
    exact (Option.some.inj hj).symm

theorem entryOf_of {f : String} {j : ℕ} (hj : idxOf f = some j) : entryOf f = (fnOf j).entry := by
  unfold entryOf
  rw [hj]

theorem entryOf_main : entryOf "main" = mainEntry := by
  rw [entryOf_of idxOf_main]
  rfl

private theorem idxOf_of_find {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) :
    ∃ j, idxOf f = some j := by
  cases hj : idxOf f with
  | none =>
    unfold idxOf at hj
    rw [Option.map_eq_none_iff] at hj
    rw [find?_none hj] at hf
    cases hf
  | some j => exact ⟨j, rfl⟩

/-- The callees of the frames set up: one per call, of its function, valid when entered. -/
theorem kidsValid_get {P : Core.Program} {rd : Reader} {σ : Val} : ∀ {cs : List Memory.Call} {ks : List Memory.Tree},
    Tree.KidsValid P rd σ cs ks → ks.length = cs.length ∧ ∀ (i : ℕ) (c : Memory.Call), cs[i]? = some c →
      ∃ k, ks[i]? = some k ∧ k.name = c.f ∧ (c.taken = true → k.Valid P rd (c.args.map σ) (c.rets.map σ))
  | [], [], _ => ⟨rfl, fun i c h => by simp at h⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | c :: cs, k :: ks, ⟨hn, hk, h⟩ => by
    obtain ⟨hl, ih⟩ := kidsValid_get h
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

theorem total_lt_of_kid {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {i : ℕ} {k : Memory.Tree}
    (hk : kids[i]? = some k) : k.total fs < (Memory.Tree.node f σ bufs kids).total fs := by
  rw [total_node, totalKids_eq_sum]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := Tree.total fs) (List.mem_of_getElem? hk))
  have := two_le_fs f
  omega

theorem weightKids_eq_sumB (ω : String → ℕ) : ∀ ks : List Tree,
    Tree.weightKids ω ks = (ks.map (Tree.weight ω)).sum
  | [] => by rw [Tree.weightKids]; rfl
  | k :: ks => by rw [Tree.weightKids, weightKids_eq_sumB ω ks, List.map_cons, List.sum_cons]

theorem weightVKids_eq_sumB (ω : String → Val → ℕ) : ∀ ks : List Tree,
    weightVKids ω ks = (ks.map (weightV ω)).sum
  | [] => by rw [weightVKids]; rfl
  | k :: ks => by rw [weightVKids, weightVKids_eq_sumB ω ks, List.map_cons, List.sum_cons]

theorem sum_range_getD {α : Type} (g : α → ℕ) : ∀ ks : List α,
    ((List.range ks.length).map fun i => ((ks[i]?).map g).getD 0).sum = (ks.map g).sum
  | [] => rfl
  | k :: ks => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.map_cons, List.sum_cons, ← sum_range_getD g ks]
    simp [Function.comp_def]

private theorem ite_intro_pos {p : Prop} [Decidable p] {a b : Prop} (hp : p) (ha : a) :
    if p then a else b := by
  split
  · exact ha
  · contradiction

private theorem ite_intro_neg {p : Prop} [Decidable p] {a b : Prop} (hp : ¬p) (hb : b) :
    if p then a else b := by
  split
  · contradiction
  · exact hb

private theorem ite_elim_pos {p : Prop} [Decidable p] {a b : Prop} (hp : p) (h : if p then a else b) : a := by
  split at h
  · exact h
  · contradiction

private theorem ite_elim_neg {p : Prop} [Decidable p] {a b : Prop} (hp : ¬p) (h : if p then a else b) : b := by
  split at h
  · contradiction
  · exact h

/-! ## The prologue -/

/-- **The jump table's prologue, counted**: `__jump_tables`' `SET`s from `(g^0, 1)` to `main`'s
entry. -/
theorem runC_jumpTables {κ : ℕ} {L : MemImage κ} (h : JumpTables L) :
    RunC guest L ⟨gpow 0, 1⟩ ⟨gpow mainEntry, 1⟩ jtSets := by
  have hwalk : ∀ i ≤ Data.f0.len, RunC guest L ⟨gpow 0, 1⟩ ⟨gpow i, 1⟩
      (fun op => if op = .setConstant then i else 0) := by
    intro i
    induction i with
    | zero =>
      intro _
      have e : (fun op : Opcode => if op = .setConstant then 0 else 0) = 0 := by
        funext op; split <;> rfl
      rw [e]
      exact RunC.refl _
    | succ i ih =>
      intro hi
      obtain ⟨o, k0, k1, k2, hins, hq⟩ := End.f0_instr (show i < Data.f0.len by omega)
      have hf := End.f0_fetch (show i < Data.f0.len by omega)
      rw [hins] at hf
      have hH : Holds L i 1 (.set o k0 k1 k2) := by
        show L.read (1 * gpow o) = some (OInstr.imm k0 k1 k2)
        rw [End.gpow_mul_one]
        exact h _ hq
      have := (ih (by omega)).trans (runC_fallThrough hf (End.f0_pc_lt (by omega)) rfl hH)
      have e : (fun op : Opcode => if op = .setConstant then i + 1 else 0) =
          (fun op : Opcode => if op = .setConstant then i else 0) +
            (fun op ↦ if op = (OInstr.set o k0 k1 k2).toInstr.opcode then 1 else 0) := by
        funext op
        by_cases hop : op = .setConstant <;> simp [hop, OInstr.toInstr, Instr.opcode]
      rw [e]
      exact this
  have := hwalk _ le_rfl
  have e : (fun op : Opcode => if op = .setConstant then Data.f0.len else 0) = jtSets := by
    funext op
    unfold jtSets
    rfl
  rw [e] at this
  exact this

/-! ## The instances -/

/-- What an instance's run gives: its return registers (`main`: the final ones), a counted run
there from its entry at its frame within its subtree's weight, and its returns after its
arguments. -/
def InstRuns {κ : ℕ} (L : MemImage κ) (I : Inst) (args rets : List E) : Prop :=
  ∃ (r : Regs K) (c : Opcode → ℕ),
    (if I.t.name = "main" then r = Regs.final guest else retRegs L (gpow I.fp) = some r) ∧
    RunC guest L ⟨gpow (entryOf I.t.name), gpow I.fp⟩ r c ∧ (∀ op, c op ≤ weightV (fun f σ ↦ pathCountN f σ op) I.t) ∧
    ∀ k (hk : k < rets.length), L.read (gpow (I.fp + (2 + args.length + k))) = some rets[k]

section Insts

variable (h : B2Hyps) {hdr : E × E} {rd : Reader} {T : Memory.Tree} (hname : T.name = "main")
  (hH : HonestAt coreProgram fs H C hdr T cert rd [] [])
include h hname hH

/-- **Every instance that runs runs**, by induction on the words its subtree allocates. -/
theorem inst_runs : ∀ n, ∀ I ∈ honestInsts coreProgram fs H hdr T, I.t.total fs < n →
    (I.t.name = "main" → I.fp = 0) → ∀ args rets,
      I.t.Valid coreProgram (honest coreProgram fs H C hdr T).read args rets →
        InstRuns (honest coreProgram fs H C hdr T) I args rets
  | 0, _, _, hn, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, I, hI, hn, hm, args, rets, hv => by
    set L := honest coreProgram fs H C hdr T with hL
    rcases hti : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hti] at hv
      obtain ⟨fn, hf, hpar, es, vs, hw, hrets, hev, hk⟩ := hv
      obtain ⟨j, hj⟩ := idxOf_of_find hf
      obtain ⟨i, rfl, hi, hn', hfind, hcore, -, -, h1, hlt⟩ := fn_of_idx hj
      obtain rfl : fn = coreProgram[i] := Option.some.inj (hf.symm.trans hfind)
      have hw' : walk σ (coreOf (i + 1)).body = .ret es vs := by rw [hcore]; exact hw
      have hF := h.frame hdr rd T hname hH I hI f σ bufs kids hti (i + 1) hj es vs hw'
      have hkv := kidsValid_get hk
      have hkids : I.t.kids = kids := by rw [hti]; rfl
      have hex : ∀ i' : ℕ, ∃ ci : Opcode → ℕ, (∀ (c : Memory.Call) (kfp : ℕ), (calls es)[i']? = some c →
          I.kidFps[i']? = some kfp → c.taken = true → (∃ r, retRegs L (gpow kfp) = some r ∧
            RunC guest L ⟨gpow (entryOf c.f), gpow kfp⟩ r ci) ∧
            ∀ k (hk : k < c.rets.length),
              L.read (gpow (kfp + (2 + c.args.length + k))) = some (σ c.rets[k])) ∧
          ∀ op, ci op ≤ ((kids[i']?).map (weightV (fun f σ ↦ pathCountN f σ op))).getD 0 := by
        intro i'
        cases hc : (calls es)[i']? with
        | none => exact ⟨0, fun c _ h' => absurd h' (by simp), fun _ => Nat.zero_le _⟩
        | some c =>
          obtain ⟨k, hk', hkn, hkval⟩ := hkv.2 i' c hc
          by_cases htk : c.taken = true
          · obtain ⟨J, hJ, hJt, hJfp, -⟩ := honest_kid hI (k := k) (by rw [hkids]; exact hk')
            have hlt' : J.t.total fs < n := by
              have := total_lt_of_kid (f := f) (σ := σ) (bufs := bufs) hk'
              rw [hti] at hn
              rw [hJt]
              omega
            have hne : c.f ≠ "main" := calls_ne_main hfind hw (List.mem_of_getElem? hc)
            have hJn : J.t.name = c.f := by rw [hJt, hkn]
            obtain ⟨r, ci, hr, hrun, hle, hrets'⟩ := inst_runs n J hJ hlt'
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
      have hK : KidsRun L σ es I.kidFps ck := by
        refine ⟨by simp [hck], fun i' c kfp hc hkfp ht => ?_⟩
        have hi' : i' < (calls es).length := (List.getElem?_eq_some_iff.mp hc).1
        have hget : ck.getD i' 0 = cf i' := by simp [hck, hi']
        rw [hget]
        exact (hcf i').1 c kfp hc hkfp ht
      have hjt : JumpTables L := jumpTables_honestC hH.toHonest hname
      have hκ : logMem (T.total fs) ≤ 32 := hH.toHonest.logMem_le
      have hmain : i + 1 = 1 → I.fp = 0 := fun h1' =>
        hm (by rw [hti]; exact (idx_one_iff hj).mp h1')
      obtain ⟨r, c, hr, hrun, hle, hrets'⟩ := h.run (i + 1) (by omega) hlt L hκ (End.jtHolds_of hjt) hjt
        I.fp hmain σ es vs hw' hev I.kidFps I.hdr hF ck hK
      have hname' : (coreOf (i + 1)).name = f := by rw [hcore]; exact hn'
      refine ⟨r, c, ?_, ?_, fun op => ?_, fun k hk' => ?_⟩
      · have key := idx_one_iff hj
        rw [hti]
        simp only [Tree.name]
        by_cases hfm : f = "main"
        · exact ite_intro_pos hfm (ite_elim_pos (key.mpr hfm) hr)
        · exact ite_intro_neg hfm (ite_elim_neg (fun h1' => hfm (key.mp h1')) hr)
      · rw [hti]
        simp only [Tree.name]
        rw [entryOf_of hj]
        exact hrun
      · rw [hti, weightV, weightVKids_eq_sumB, ← sum_range_getD _ kids, hkv.1]
        have hs : (ck.map (· op)).sum ≤
            ((List.range (calls es).length).map fun i' =>
              ((kids[i']?).map (weightV (fun f σ ↦ pathCountN f σ op))).getD 0).sum := by
          rw [hck, List.map_map]
          exact List.sum_le_sum fun i' _ => (hcf i').2 op
        have := hle op
        have hpc : pathCountN f σ op = pathCount (i + 1) σ op := by unfold pathCountN; rw [hj]
        rw [hpc]
        omega
      · subst hrets hpar
        have hk'' : k < vs.length := by simpa using hk'
        have := hrets' k hk''
        rw [hcore] at this
        simpa using this
    · rw [hti] at hv
      exact hv.elim

end Insts

/-! ## B2 -/

/-- `main` runs from its entry at frame `1` to the final registers, within the tree's weight. -/
theorem main_runC (h : B2Hyps) {hdr : E × E} {rd : Reader} {T : Memory.Tree} (hname : T.name = "main")
    (hH : HonestAt coreProgram fs H C hdr T cert rd [] []) :
    ∃ c : Opcode → ℕ, RunC guest (honest coreProgram fs H C hdr T) ⟨gpow mainEntry, 1⟩ (Regs.final guest) c ∧
      ∀ op, c op ≤ weightV (fun f σ ↦ pathCountN f σ op) T := by
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := coreProgram) (fs := fs) (H := H) (hdr := hdr) (T := T)
  have hv : I.t.Valid coreProgram (honest coreProgram fs H C hdr T).read [] [] := by
    rw [hIt]; exact hH.toHonest.valid_image
  obtain ⟨r, c, hr, hrun, hle, -⟩ := inst_runs h hname hH _ I hI (Nat.lt_succ_self _) (fun _ => hfp) [] [] hv
  rw [hIt] at hr hrun hle
  rw [hname] at hr hrun
  simp only [↓reduceIte] at hr
  subst hr
  rw [entryOf_main, hfp, show (gpow 0 : K) = 1 by rw [gpow, pow_zero]] at hrun
  exact ⟨c, hrun, hle⟩

/-- **B2**: on the honest memory, `main` runs from its entry to the final registers (`End`'s
`b2`). -/
theorem b2_complete (h : B2Hyps) : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] →
      Reach guest (honest coreProgram fs H C hdr T) ⟨gpow mainEntry, 1⟩ (Regs.final guest) := by
  intro hdr rd T hname hH
  obtain ⟨c, hc, -⟩ := main_runC h hname hH
  exact hc.reach

/-- **B2, counted**: a halting run on the honest memory executes at most `cnt T op` instructions
of each opcode (`End`'s `count`). -/
theorem b2_count (h : B2Hyps) : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      run guest (honest coreProgram fs H C hdr T) n Regs.initial = some (Regs.final guest) →
        ∀ op, (⟨_, honest coreProgram fs H C hdr T, n⟩ : Trace guest).count op ≤ cnt T op := by
  intro hdr rd T hname hH n hn op
  obtain ⟨c, hc, hle⟩ := main_runC h hname hH
  have hjt : JumpTables (honest coreProgram fs H C hdr T) :=
    jumpTables_honestC hH.toHonest hname
  have hpro := runC_jumpTables hjt
  rw [show (⟨gpow 0, 1⟩ : Regs K) = Regs.initial by rw [gpow, pow_zero]; rfl] at hpro
  rw [count_eq_of_runC (hpro.trans hc) hn op, Pi.add_apply]
  have := hle op
  unfold cnt
  omega

end
end LeanVM.Guest.B2C
