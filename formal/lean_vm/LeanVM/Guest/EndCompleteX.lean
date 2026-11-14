/-
  LeanVM.Guest.EndCompleteX

  The reference memory of the executor: the honest memory extended by the words the honest tree's
  hints write to the heap, a valid execution of the guest within the budget's size.
-/

module

public import LeanVM.Guest.EndComplete
public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.Memory.DischargeX

/-!
# Completeness on the extended honest memory

The executor writes every heap word a hint writes, which the honest memory lacks where nothing
loads it. `MainCompleteX` is `MainComplete` with every heap hint word of the tree in its data
(`Tree.HintsIn`, the region empty). Under it, `honest_of_mainX` gives, beside `honest_of_main`'s
tree, the extension `honestX` of its honest memory by the hints' words read off the memory B1's
tree is valid on (`honestX_retemp`), holding each of them. B2 runs on any memory covering the
honest writes (`b2_completeL`, `b2_countL`), so on the extension too: `refX_valid`, at the
deployed instance, is a valid execution of the guest on the statement's digest, within the
committed size, on the extension.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Main (KFacts imageOf LConsistent Layout MemL)

@[expose] public section

variable (fs : String → ℕ) (H : Inst → ℕ → E × E) (C : Inst → List (ℕ × E))
  (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ) (b : Budget)

/-- **`main`'s completeness within the budget, its heap hints placed**: `MainComplete` with every
heap word the tree's hints write in its data. -/
def MainCompleteX : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w → b.size (work s w) ≤ 2 ^ 30 →
    ∃ (N : ℕ) (L : Layout), LConsistent L ∧ (∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ N) ∧
      N ≤ 2 ^ 30 ∧ N ≤ b.words.eval (work s w) ∧
      ∀ rd, LowDef (logMem N) rd → MemL rd L → rd 1 = some (hdrOf (statementDigest seed s)).1 →
        rd g = some (hdrOf (statementDigest seed s)).2 →
          ∃ t : Tree, t.name = "main" ∧ t.Valid coreProgram rd [] [] ∧ t.BufsOk coreProgram ∧
            t.Placed coreProgram fs cert (0, t.block fs coreProgram.loop) ∧ t.total fs = N ∧
            t.LoadsIn coreProgram fs cert (fun i => i < 2) (0, t.block fs coreProgram.loop) ∧
            t.HintsIn coreProgram fs cert (fun _ => False) (0, t.block fs coreProgram.loop) ∧
            ∀ op, cnt t op ≤ (b.instrs op).eval (work s w)

variable {fs H C cert cnt b}

theorem MainCompleteX.mainComplete (h : MainCompleteX fs cert cnt b) : MainComplete fs cert cnt b :=
  fun seed s w hrel hlim hok hbs => by
    obtain ⟨N, L, hc, hin, hN, hNb, hrel'⟩ := h seed s w hrel hlim hok hbs
    refine ⟨N, L, hc, hin, hN, hNb, fun rd hlow hL h0 h1 => ?_⟩
    obtain ⟨t, hn, hv, hb, hp, ht, hl, -, hcnt⟩ := hrel' rd hlow hL h0 h1
    exact ⟨t, hn, hv, hb, hp, ht, hl, hcnt⟩

/-- **The `honest` piece on the extended memory**: `honest_of_main`'s tree `T`, a re-choice of
the temporaries of a tree valid on a memory `rd0`, is `HonestX` with the words its hints write to
the heap, read off `rd0`, which the extension holds. -/
theorem honest_of_mainX (hm : MainCompleteX fs cert cnt b) (hk : KFactsAll fs H C cert)
    (hc : CntRetemp fs cnt) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w → b.size (work s w) ≤ 2 ^ 30 →
      ∃ (rd rd0 : Reader) (T : Tree) (X : List Write),
        (∃ (t : Tree) (ν : ℕ → String → Val → V → E), t.Valid coreProgram rd0 [] [] ∧ T = t.retemp coreProgram fs ν (0, t.block fs coreProgram.loop)) ∧
        T.name = "main" ∧
        HonestAt coreProgram fs H C (hdrOf (statementDigest seed s)) T cert rd [] [] ∧
        HonestX coreProgram fs H C (hdrOf (statementDigest seed s)) T rd [] [] X ∧
        T.total fs ≤ b.words.eval (work s w) ∧ (∀ op, cnt T op ≤ (b.instrs op).eval (work s w)) ∧
        ∀ a ∈ hintWords coreProgram fs H (hdrOf (statementDigest seed s)) T, ∃ v, rd0 a = some v ∧
          (honestX coreProgram fs H C (hdrOf (statementDigest seed s)) T X).read a = some v := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨N, L, hcons, hin, hN, hNb, hrelL⟩ := hm seed s w hrel hlim hok hbs
  set hdr := hdrOf (statementDigest seed s) with hhdr
  have h64 : logMem N < 64 := by have := logMem_le_maxLogMem hN; unfold maxLogMem at this; omega
  set M := imageOf (logMem N) L hdr with hM
  have hlow : LowDef (logMem N) M.read := fun i hi => by
    rw [MemoryImage.read_gpow h64 M ⟨i, hi⟩]; rfl
  have hL := B1.Main.memL_imageOf h64 hcons (fun q hq => ⟨(hin q hq).1,
    le_trans (hin q hq).2 (le_two_pow_logMem N)⟩) hdr
  obtain ⟨hh0, hh1⟩ := B1.Main.imageOf_hdr h64 (le_trans (by decide) (twentyThree_le_logMem N)) L hdr
  have e0 : (1 : K) = Parameters.addressOfIndex 0 := by simp [Parameters.addressOfIndex]
  have e1 : Parameters.g = Parameters.addressOfIndex 1 := by simp [Parameters.addressOfIndex]
  obtain ⟨t, hn, hv, hb, hp, ht, hl, hhint, hcntT⟩ := hrelL M.read hlow hL (by rw [e0]; exact hh0)
    (by rw [e1]; exact hh1)
  subst ht
  have hkf := hk hdr t hn
  have hd : DischargeHyps coreProgram fs cert H C hdr t (fun i => i < 2) M [] [] :=
    { fresh := coreProgram_fresh
      valid := hv
      bufsOk := hb
      placed := hp
      loads := hl
      region := fun i hi => Or.inl hi
      hdr_read := ⟨hh0, hh1⟩
      size := hN
      addr := B1.Main.dischargeAddr h64 hv hp fun I hI f σ bufs kids hIt p r rs ha k hk' => by
        have hcl := (hkf.run I hI f σ bufs kids hIt p r rs ha k hk').1
        have hoff := (hkf.cells.off I hI _ hcl).2
        have hw := honest_within (P := coreProgram) hI (by have := hkf.cells.two_le I hI; omega)
        have := le_two_pow_logMem (t.total fs)
        omega
      cells := hkf.cells
      cells' := hkf.cells'
      cert_lt := hkf.cert_lt
      cert_inj := hkf.cert_inj
      run := hkf.run
      tmp := hkf.tmp
      keep := hkf.keep }
  obtain ⟨ν, hν, hX, hsub, hrd⟩ := honestX_retemp hd hhint
  refine ⟨_, M.read, _, _, ⟨t, ν, hv, rfl⟩, by rw [name_retemp]; exact hn, hν, hX,
    by rw [total_retemp]; exact hNb, fun op => ?_, fun a ha => ?_⟩
  · rw [hc]
    exact hcntT op
  · obtain ⟨v, hrv⟩ := hrd a (hsub ha)
    refine ⟨v, hrv, ?_⟩
    have := hX.read_X (List.mem_map_of_mem (f := fun a => (a, (M.read a).getD 0)) (hsub ha))
    rw [hrv, Option.getD_some] at this
    exact this

section Deployed

open B2C

/-- **The reference memory is a valid execution** at the deployed instance: under `main`'s
completeness with its heap hints placed, the honest memory of the honest tree extended by the
words its hints write (read off the memory `rd0` B1's tree is valid on) is a valid execution of
the guest on the statement's digest, within the committed size `2^30`, and holds each of those
words. -/
theorem refX_valid {b : Budget} (hm : MainCompleteX B2C.fs B2C.cert B2C.cnt b) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w → b.size (work s w) ≤ 2 ^ 30 →
      ∃ (rd0 : Reader) (T : Tree) (X : List Write) (n : ℕ),
        (∃ (t : Tree) (ν : ℕ → String → Val → V → E), t.Valid coreProgram rd0 [] [] ∧ T = t.retemp coreProgram B2C.fs ν (0, t.block B2C.fs coreProgram.loop)) ∧
        T.name = "main" ∧
        ValidExecution guestProgram (publicInputOf (statementDigest seed s))
          ⟨_, honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X, n⟩ ∧
        (⟨_, honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X, n⟩ :
          Execution guestProgram).committedSize ≤ 2 ^ 30 ∧
        ∀ a ∈ hintWords coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T, ∃ v, rd0 a = some v ∧
          (honestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T X).read a = some v := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨rd, rd0, T, X, ht, hname, hH, hX, hw, hc, hhw⟩ :=
    honest_of_mainX hm kFactsAll (cntRetemp coreProgram_fresh) seed s w hrel hlim hok hbs
  have hb := hX.publicBoundary (prog := guestProgram)
  have hreach := (reach_jumpTables (jumpTables_cover hH.toHonest hX.covers hname)).trans
    (b2_completeL b2Hyps _ rd T hname hH _ hX.covers)
  obtain ⟨n, hv⟩ := validExecution_of_reach hb hreach
  refine ⟨rd0, T, X, n, ht, hname, hv, ?_, hhw⟩
  rw [committedSize_eq_sizeOf]
  exact (sizeOf_mono hw fun op =>
    (b2_countL b2Hyps _ rd T hname hH _ hX.covers n hv.2 op).trans (hc op)).trans hbs

end Deployed

end
end LeanVM.Guest.End
