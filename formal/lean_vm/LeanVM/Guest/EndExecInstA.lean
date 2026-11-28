/-
  LeanVM.Guest.EndExecInstA

  What the families' proofs read of an honest instance on b2c's aligned tree: it is valid on the
  reference, its frame holds what B2's completeness check reads, and a fact passed from each caller to
  its callees holds at every instance.
-/

module

public import LeanVM.Guest.EndExecCoreA
public import LeanVM.Guest.CoreMode.Fam.DownA
public import LeanVM.Guest.B1.Digest.Interface

/-!
# The honest instances, aligned

The bus era's `EndExecW.inst_valid'`, `Fam/RefAll.{root_main, insts_all}` and `Fam/ResA.{inst_fb,
ref_read, inst_frame, ref_memOk}` at b2c's layout `layB al`, on a reference run `r` of the honest tree
`(D r).T` (`RefH`): `inst_validA` (a `node` instance is valid on the reference memory), `insts_allA`
(down the aligned tree, `Res.insts_downA`, from `main`'s root), `inst_frameA` (`B2C.b2Hyps.frame`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx)
open LeanVM.Prover.Exec

public section

theorem find_name' {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : fn.name = f := by
  unfold Program.find? at h
  have := List.find?_some h
  simpa using this

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- The honest instances of a reference run's tree, aligned. -/
noncomputable abbrev instsR (al : String → Bool) (D : Ref → RefD) (r : Ref) : List Inst :=
  honestInstsA coreProgram B2C.fs al B2C.H r.hdr (D r).T

/-- **An honest `node` instance is valid on the reference memory.** -/
theorem inst_validA (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r) {f : String} {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    ∃ args rets, (Memory.Tree.node f σ bufs kids).Valid coreProgram r.img.read args rets := by
  obtain ⟨rd, hHa, -, hcov⟩ := hR.coversR
  rcases instsA_good (P := coreProgram) _ _ _ (Covers.valid hHa.toHonestA hcov) I hI with
    ⟨args, rets, hval⟩ | ⟨_, _, hph⟩
  · rw [ht] at hval; exact ⟨args, rets, hval⟩
  · rw [ht] at hph; cases hph

/-- **The root's instance is `main`'s.** -/
theorem root_mainA (hR : RefH (layB al) (D r) r) {J : Inst} {rest : List Inst}
    (he : (D r).T.instsA B2C.fs coreProgram.loop al B2C.H (0, (D r).T.block B2C.fs coreProgram.loop) r.hdr =
      J :: rest)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (hJt : J.t = .node f σ bufs kids) : f = "main" := by
  obtain ⟨J', rest', he', ht, -⟩ := head_instsA (fs := B2C.fs) (lp := coreProgram.loop) (al := al) (H := B2C.H)
    (D r).T (0, (D r).T.block B2C.fs coreProgram.loop) r.hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  have hn := hR.name
  rw [← ht, hJt] at hn
  simpa only [Tree.name] using hn

/-- **A fact carried down to every honest instance**: passed from each instance to its callees, and had
by an instance of `main`. -/
theorem insts_allA (hR : RefH (layB al) (D r) r) {Q : Inst → Prop}
    (hs : Res.KidStep coreProgram r.img.read B2C.H (instsR al D r) Q)
    (hroot : ∀ J, (∀ f σ bufs kids, J.t = .node f σ bufs kids → f = "main") → Q J) :
    ∀ J ∈ instsR al D r, Q J := by
  obtain ⟨rd, hHa, -, hcov⟩ := hR.coversR
  have hv := Covers.valid hHa.toHonestA hcov
  exact Res.insts_downA hs (D r).T _ r.hdr hv (fun J h ↦ h) fun J rest he ↦
    hroot J fun _ _ _ _ hJt ↦ root_mainA hR he hJt

/-- **An honest node's frame holds what the completeness check reads.** -/
theorem inst_frameA (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r) {f : String}
    {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {j : ℕ}
    (hj : idxOf f = some j) {es : List Ev} {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs) :
    FrameHolds r.img j I.fp σ es vs I.kidFps I.hdr := by
  obtain ⟨rd, hHa, -, hcov⟩ := hR.coversR
  exact B2C.b2Hyps.frame al r.hdr rd (D r).T hR.name hHa r.img hcov I hI f σ bufs kids ht j hj es vs hw

/-- **An honest node's frame within `2^28` words.** -/
theorem inst_fbA (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r) {f : String}
    {σ : Val} {bufs : List ℕ} {kids : List Tree} {j : ℕ} (ht : I.t = .node f σ bufs kids)
    (hj : idxOf f = some j) : I.fp + fsN j ≤ 2 ^ 28 := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  obtain ⟨_, -, -, -, -, -, hfs, -⟩ := fn_of_idx hj
  have h2 := hH.cells.two_le I hI
  have hwi := honestA_within_node hI ht (lt_of_lt_of_le (by norm_num : 0 < 2) h2)
  have hn : I.t.name = f := by rw [ht]; rfl
  have hle := le_two_pow_logMem ((D r).T.wordsA B2C.fs coreProgram.loop al)
  have h28 : 2 ^ logMem ((D r).T.wordsA B2C.fs coreProgram.loop al) ≤ 2 ^ 28 :=
    Nat.pow_le_pow_right (by norm_num) (hR.log hr)
  rw [hn, hfs] at hwi
  omega

/-- A word the reference image holds at a cell below `2^62`, as `refMem`. -/
theorem ref_readA (hr : r.Ok) {c : ℕ} {v : E} (hc : c < 2 ^ 62) (h : r.img.read (addressOfIndex c) = some v) :
    c < maxCells ∧ refMem r.img c = v :=
  (refRd_img hr.log r.img) c v hc h

/-- The reference memory is a memory image of at most `2^32` words. -/
theorem ref_memOkA (hR : RefH (layB al) (D r) r) (hr : r.Ok) : B1.Digest.MemOk r.img.read :=
  ⟨r.κ, by rw [hR.κ]; exact le_trans (by decide) (twentyThree_le_logMem _), le_trans hr.log (by decide), r.img, rfl⟩

end

end LeanVM.Guest.EndExec
