/-
  LeanVM.Guest.B2C.RefX

  B2's completeness at the reference memory: from B1's facts about `main`'s tree, its honest memory
  extended by its hints' heap words and its hint-only values carries a valid execution of the guest
  that reaches the end, its opcode counts the tree's.
-/

module

public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.Memory.GuestExtra

/-!
# The reference run's ISA side

The reference memory is laid out as Hotwire's executor allocates (`Memory/AllocA`: `al f` says
whether `f`'s frames are allocated at the next multiple of `16`); `refX_exists` holds for every `al`.

`MainB1 al hdr t M` is what B1's completeness of `main` is to give of the tree `t` it builds on a
memory image `M` of `2^logMem (t.wordsA ..)` words (the bus era's `Budget.mainCompletePE_deployed`
and `B1.Main.main_hintsIn`, tag `formal-bus-archive`, over the unaligned layout): `t` is `main`'s,
valid on `M`, its buffers well formed, placed at `0` by the aligned allocator, its loads and its
heap hints in its own data or the header cells, `M` holding the header, within `2^30` words.

`refX_exists`: under `MainB1` and `ExtraOk exOf` (the hint-only cells of the core route's data
fresh), the temporaries re-chosen (`Tree.retempA`), the tree `T` is `HonestAtA` and `HonestX` with
`X` the hints' heap words read off `M` followed by the hint-only values, and the extension
`honestX … T X` carries a valid execution of `guestProgram` on `input` (whose words are the
header), of `n` steps for some `n`, its count at each opcode at most `cnt T`, which is `cnt t`;
`T` uses `t`'s words, and its hints' heap words and hint-only values read back from the extension.
These are `Ref.Ok`'s `honest`, `valid`, `hintWords` and `extra` (tag `formal-bus-archive`,
`CoreMode/Fam/Ref.lean`), and its size from the counts.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable (al : String → Bool)

/-- **What B1's completeness of `main` gives** of its tree `t` on the memory image `M`, with the
header `hdr`. -/
structure MainB1 (hdr : E × E) (t : Tree) (M : MemoryImage (logMem (t.wordsA fs coreProgram.loop al))) : Prop where
  name : t.name = "main"
  valid : t.Valid coreProgram M.read [] []
  bufsOk : t.BufsOk coreProgram
  placed : t.PlacedA coreProgram fs al cert (0, t.block fs coreProgram.loop)
  loads : t.LoadsInA coreProgram fs al cert (fun i => i < 2) (0, t.block fs coreProgram.loop)
  hints : t.HintsIn coreProgram fs al cert (fun i => i < 2) (0, t.block fs coreProgram.loop)
  hdr_read : M.read (addressOfIndex 0) = some hdr.1 ∧ M.read (addressOfIndex 1) = some hdr.2
  size : t.wordsA fs coreProgram.loop al ≤ 2 ^ 30

/-- The re-chosen tree. -/
noncomputable abbrev reTree (ν : ℕ → String → Val → V → E) (t : Tree) : Tree :=
  t.retempA coreProgram fs al ν (0, t.block fs coreProgram.loop)

/-- The extension's words: the hints' heap words read off `M`, then the hint-only values. -/
noncomputable abbrev refWrites (exOf : ℕ → List (ℕ × ℕ)) (hdr : E × E) (t : Tree) {κ : ℕ}
    (M : MemoryImage κ) : List Write :=
  readerWrites M.read (hintWords coreProgram fs al H hdr t) ++
    extraWrites coreProgram fs al H hdr t (refExtra exOf)

/-- **The reference run's ISA side.** -/
theorem refX_exists {exOf : ℕ → List (ℕ × ℕ)} (hx : ExtraOk exOf) (input : PublicInput) (t : Tree)
    (M : MemoryImage (logMem (t.wordsA fs coreProgram.loop al))) (hb : MainB1 al (input.word0, input.word1) t M) :
    ∃ (ν : ℕ → String → Val → V → E) (n : ℕ),
      (reTree al ν t).name = "main" ∧
      (∃ rd, HonestAtA coreProgram fs al H C (input.word0, input.word1) (reTree al ν t) cert rd [] [] ∧
        HonestX coreProgram fs al H C (input.word0, input.word1) (reTree al ν t) rd [] []
          (refWrites al exOf (input.word0, input.word1) t M)) ∧
      ValidExecution guestProgram input
        ⟨logMem ((reTree al ν t).wordsA fs coreProgram.loop al),
          honestX coreProgram fs al H C (input.word0, input.word1) (reTree al ν t)
            (refWrites al exOf (input.word0, input.word1) t M), n⟩ ∧
      (∀ op, (⟨_, honestX coreProgram fs al H C (input.word0, input.word1) (reTree al ν t)
          (refWrites al exOf (input.word0, input.word1) t M), n⟩ : Execution guestProgram).opcodeCount op ≤
        cnt (reTree al ν t) op) ∧
      cnt (reTree al ν t) = cnt t ∧ (reTree al ν t).wordsA fs coreProgram.loop al = t.wordsA fs coreProgram.loop al ∧
      (∀ a ∈ hintWords coreProgram fs al H (input.word0, input.word1) (reTree al ν t), ∃ v, M.read a = some v ∧
        (honestX coreProgram fs al H C (input.word0, input.word1) (reTree al ν t)
          (refWrites al exOf (input.word0, input.word1) t M)).read a = some v) ∧
      (∀ I ∈ honestInstsA coreProgram fs al H (input.word0, input.word1) (reTree al ν t), ∀ f σ bufs kids,
        I.t = .node f σ bufs kids → ∀ v ∈ (I.t.events coreProgram).flatMap Ev.uses, ∀ c,
          (refExtra exOf f).lookup v.idx = some c → I.fp + c < 2 ^ 30 ∧
            (honestX coreProgram fs al H C (input.word0, input.word1) (reTree al ν t)
              (refWrites al exOf (input.word0, input.word1) t M)).read
                (Parameters.addressOfIndex (I.fp + c)) = some (σ v)) := by
  set hdr : E × E := (input.word0, input.word1) with hhdr
  have h64 : logMem (t.wordsA fs coreProgram.loop al) < 64 := by
    have := logMem_le_maxLogMem hb.size; unfold maxLogMem at this; omega
  have hkf := kFactsAll al hdr t hb.name
  have hd : DischargeHyps coreProgram fs al cert H C hdr t (fun i => i < 2) M [] [] :=
    { fresh := coreProgram_fresh
      valid := hb.valid
      bufsOk := hb.bufsOk
      placed := hb.placed
      loads := hb.loads
      region := fun i hi => Or.inl hi
      hdr_read := hb.hdr_read
      size := hb.size
      addr := B1.Main.dischargeAddr h64 hb.valid hb.placed fun I hI f σ bufs kids hIt p r rs ha k hk' => by
        have hcl := (hkf.run I hI f σ bufs kids hIt p r rs ha k hk').1
        have hoff := (hkf.cells.off I hI _ hcl).2
        have hw := honestA_within (P := coreProgram) hI (by have := hkf.cells.two_le I hI; omega)
        have := le_two_pow_logMem (t.wordsA fs coreProgram.loop al)
        omega
      cells := hkf.cells
      cells' := hkf.cells'
      cert_lt := hkf.cert_lt
      cert_inj := hkf.cert_inj
      run := hkf.run
      tmp := hkf.tmp
      keep := hkf.keep }
  obtain ⟨ν, hν, hX, hsub, hrd⟩ := honestX_retempE hd (extraFresh_guest hx hdr t) hb.hints
  have hname : (reTree al ν t).name = "main" := by rw [name_retempA]; exact hb.name
  have hb' := hX.publicBoundary (prog := guestProgram)
  have hreach := (End.reach_jumpTables (jumpTables_cover hν.toHonestA hX.covers hname)).trans
    (b2_completeL b2Hyps _ _ _ hname hν _ hX.covers)
  obtain ⟨n, hvx⟩ := validExecution_of_reach hb' hreach
  refine ⟨ν, n, hname, ⟨_, hν, hX⟩, hvx, fun op => b2_countL b2Hyps _ _ _ hname hν _ hX.covers n hvx.2 op,
    cntRetemp coreProgram_fresh ν t, wordsA_retempA t _, fun a ha => ?_,
    extra_read hd (extraFresh_guest hx hdr t) hX (extraUses_guest hx)⟩
  obtain ⟨v, hrv⟩ := hrd a (hsub ha)
  refine ⟨v, hrv, ?_⟩
  have := hX.read_X (List.mem_append_left _
    (List.mem_map_of_mem (f := fun a => (a, (M.read a).getD 0)) (hsub ha)))
  rw [hrv, Option.getD_some] at this
  exact this

end

end LeanVM.Guest.B2C
