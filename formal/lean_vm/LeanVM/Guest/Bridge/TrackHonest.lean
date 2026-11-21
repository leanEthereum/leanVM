/-
  LeanVM.Guest.Bridge.TrackHonest

  The tree track on the honest tree of the deployed guest: `main`'s frame at its body to start, the callees and buffers where the honest memory places them, and the tree's pops agreeing with the honest pushes stream by stream.
-/

module

public import LeanVM.Guest.Bridge.RetempPops
public import LeanVM.Guest.EndCompleteX
public import LeanVM.Guest.Budget.FinalP

/-!
# The tree track on the honest tree

`honest_of_mainP`: `End.honest_of_mainH` under `MainCompleteP`, which also gives the tree's pops on the memory B1's tree is valid on (`rd0`) agreeing with the honest pushes, other than the advised sizes, stream by stream; the honest memory's tree, its temporaries re-chosen, pops the same (`pops_retemp`). `track_deployed`: at the deployed instance, the track starts at `main`'s instance, at frame `0`, at its body, nothing done (`trackOk_init`). `honest_closed`: each instance's callees are instances at its callee frames, what a call's move needs (`EntOk.callee`); `honest_alloc`: every frame's allocations land at its instance's bases (`EntOk.alloc_at`).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.End (MainComplete Budget work hdrOf bytecode KFactsAll CntRetemp)
open LeanVM.Guest.Budget (MainCompleteP)
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Main (KFacts imageOf LConsistent Layout MemL)

public section

variable {fs : String → ℕ} {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)} {cert : String → V → ℕ}
  {cnt : Tree → Opcode → ℕ} {b : Budget}

/-- **The honest memory's tree, with its pops**: `End.honest_of_mainH` under `MainCompleteP`, the
tree's pops on `rd0` agreeing with the honest pushes, but the advised sizes, stream by stream. -/
theorem honest_of_mainP (hm : MainCompleteP fs cert cnt b) (hk : KFactsAll fs H C cert)
    (hc : CntRetemp fs cnt) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      b.size (work s w) ≤ 2 ^ 30 →
      ∃ (rd rd0 : Reader) (T : Tree) (X : List Write),
        (∃ (t : Tree) (ν : ℕ → String → Val → V → E), t.Valid coreProgram rd0 [] [] ∧
          T = t.retemp coreProgram fs ν (0, t.block fs coreProgram.loop)) ∧
        T.name = "main" ∧
        HonestAt coreProgram fs H C (hdrOf (statementDigest seed s)) T cert rd [] [] ∧
        HonestX coreProgram fs H C (hdrOf (statementDigest seed s)) T rd [] [] X ∧
        T.total fs ≤ b.words.eval (work s w) ∧ (∀ op, cnt T op ≤ (b.instrs op).eval (work s w)) ∧
        (∀ a ∈ hintWords coreProgram fs H (hdrOf (statementDigest seed s)) T, ∃ v, rd0 a = some v ∧
          (honestX coreProgram fs H C (hdrOf (statementDigest seed s)) T X).read a = some v) ∧
        SameStreams (T.pops coreProgram rd0)
          ((Hints.honestPushes bytecode seed s w).filter (·.1 != Hints.heapSizeStream)) := by
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
  obtain ⟨t, hn, hv, hb, hp, ht, hl, hcntT, hss⟩ := hrelL M.read hlow hL (by rw [e0]; exact hh0)
    (by rw [e1]; exact hh1)
  have hhint := B1.Main.main_hintsIn (logMem_le_maxLogMem hN) hn hv hb hp hl
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
  obtain ⟨ν, hν, hX, hsub, hrd⟩ := honestX_retempH hd hhint
  refine ⟨_, M.read, _, _, ⟨t, ν, hv, rfl⟩, by rw [name_retemp]; exact hn, hν, hX,
    by rw [total_retemp]; exact hNb, fun op => ?_, fun a ha => ?_, ?_⟩
  · rw [hc]
    exact hcntT op
  · obtain ⟨v, hrv⟩ := hrd a (hsub ha)
    refine ⟨v, hrv, ?_⟩
    have := hX.read_X (List.mem_map_of_mem (f := fun a => (a, (M.read a).getD 0)) (hsub ha))
    rw [hrv, Option.getD_some] at this
    exact this
  · rw [pops_retemp coreProgram_fresh]
    exact hss

variable {hdr : E × E} {T : Tree} {rd : Reader}

/-- **The honest instances are closed under callees**, each at its callee frame. -/
theorem honest_closed : ∀ I ∈ honestInsts coreProgram fs H hdr T, ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k →
    ∃ J ∈ honestInsts coreProgram fs H hdr T, J.t = k ∧ I.kidFps[i]? = some J.fp := fun _ hI _ _ hk ↦
  let ⟨J, hJ, h1, h2, _⟩ := honest_kid hI hk
  ⟨J, hJ, h1, h2⟩

/-- **A frame's allocations land at its instance's bases** on the honest tree placed from word `0`. -/
theorem honest_alloc (h : HonestAt coreProgram fs H C hdr T cert rd [] []) {e : Ent}
    (he : EntOk coreProgram (honestInsts coreProgram fs H hdr T) e) {d : V}
    (hd : (allocDsts (e.pre ++ e.es))[e.nb]? = some d) :
    e.σ d = ofK (addressOfIndex (e.I.cur + (e.I.t.bufs.take e.nb).sum)) ∧ e.nb < e.I.t.bufs.length :=
  he.alloc_at (insts_placedAt T _ hdr h.placed e.I he.mem)
    (insts_placed T _ hdr (Nat.zero_add _).le e.I he.mem) hd

/-- **The track on the deployed guest's honest tree**: under `MainCompleteP`, the honest memory's
tree `T` (as `honest_of_mainP`), whose pops on `rd0` agree with the honest pushes stream by stream,
and the track at `main`'s instance, at frame `0`, at its body, nothing done. -/
theorem track_deployed (hm : MainCompleteP B2C.fs B2C.cert B2C.cnt b) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      b.size (work s w) ≤ 2 ^ 30 →
      ∃ (rd rd0 : Reader) (T : Tree) (X : List Write) (I : Inst) (fn : Fn),
        HonestAt coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T B2C.cert rd [] [] ∧
        HonestX coreProgram B2C.fs B2C.H B2C.C (hdrOf (statementDigest seed s)) T rd [] [] X ∧
        T.name = "main" ∧ I.t = T ∧ I.fp = 0 ∧ I.hdr = hdrOf (statementDigest seed s) ∧
        TrackOk coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H (hdrOf (statementDigest seed s)) T) T []
          [Ent.enter coreProgram I fn] ∧
        SameStreams (T.pops coreProgram rd0)
          ((Hints.honestPushes bytecode seed s w).filter (·.1 != Hints.heapSizeStream)) := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨rd, rd0, T, X, -, hname, hH, hX, -, -, -, hss⟩ :=
    honest_of_mainP hm B2C.kFactsAll (B2C.cntRetemp coreProgram_fresh) seed s w hrel hlim hok hbs
  obtain ⟨I, hI, hIt, hfp, hhdr⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H)
    (hdr := hdrOf (statementDigest seed s)) (T := T)
  have hv := hH.valid
  rw [← hIt] at hv
  obtain ⟨fn, hf⟩ : ∃ fn, coreProgram.find? I.t.name = some fn := by
    rcases hIt' : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hIt'] at hv
      obtain ⟨fn, hf, -⟩ := hv
      exact ⟨fn, hf⟩
    · rw [hIt'] at hv; exact hv.elim
  refine ⟨rd, rd0, T, X, I, fn, hH, hX, hname, hIt, hfp, hhdr, ?_, hss⟩
  have := trackOk_init (rd := rd0) hI hf hv
  rwa [hIt] at this

end

end LeanVM.Guest.Bridge
