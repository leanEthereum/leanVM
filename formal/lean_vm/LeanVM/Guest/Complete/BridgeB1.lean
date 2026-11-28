module

public import LeanVM.Guest.Complete.CallCompleteA
public import LeanVM.Guest.Complete.MainB1
public import LeanVM.Guest.B2C.RefX

/-!
# From `main`'s placed completeness to B2's premise

B2's reference run (`B2C.refX_exists`) starts from `B2C.MainB1 al hdr t M`: `main`'s tree `t`,
valid on a memory image `M` of `2^logMem (t.wordsA ..)` words holding the header, placed at
`(0, block)` by the aligned allocator, its loads and heap hints in its data or the header cells,
within `2^30` words. Layout-free completeness (`CallCompletes`) does not give
the placement; the placed form `CallAtA` (`Complete/CallCompleteA.lean`) does.

`mainB1_of_callAtA`: from `main`'s `CallAtA` at the root (frame `0`, cursor its block `B`, end
`e ≤ 2^30`), loading from the header cells (`· < 2`), on memories holding the header at `g^0`,
the memory `rootImage` (the header at words `0`, `1`, each own word at its index, `0` elsewhere)
carries a tree with `MainB1`. `refX_of_callAtA` composes it with `refX_exists`.

`MainCompleteA al k`: `main` completes at the root on every node `GuestExecutionComplete` covers,
within `2^30` words, its pops the honest pushes and every node exact. `mainB1_of_mainCompleteA` gives `MainB1` on each node, the header the
statement digest's halves.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## The root memory -/

/-- Disjoint runs. -/
abbrev RunsDisjoint (W : Words) : Prop :=
  W.Pairwise fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1

/-- The word at index `j` of runs: of the first run holding `j`, `0` if none. -/
def wordOf (W : Words) (j : ℕ) : E :=
  match W.find? (fun q => decide (q.1 ≤ j ∧ j < q.1 + q.2.length)) with
  | some q => q.2.getD (j - q.1) 0
  | none => 0

theorem wordOf_of_mem : ∀ {W : Words}, RunsDisjoint W → ∀ {q : ℕ × List E} {j : ℕ}, q ∈ W → q.1 ≤ j →
    j < q.1 + q.2.length → wordOf W j = q.2.getD (j - q.1) 0
  | [], _, _, _, hq, _, _ => absurd hq List.not_mem_nil
  | a :: W, hp, q, j, hq, h1, h2 => by
    simp only [RunsDisjoint, List.pairwise_cons] at hp
    unfold wordOf
    rw [List.find?_cons]
    by_cases ha : a.1 ≤ j ∧ j < a.1 + a.2.length
    · rw [decide_eq_true ha]
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · have := hp.1 q hq; omega
    · rw [decide_eq_false ha]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd ⟨h1, h2⟩ ha
      · exact wordOf_of_mem hp.2 hq h1 h2

/-- **The root memory**: `2^κ` words, the header at words `0` and `1`, each run's word at its
index, `0` elsewhere. -/
noncomputable def rootImage (κ : ℕ) (hdr : E × E) (W : Words) : MemoryImage κ := fun j =>
  if j.val = 0 then hdr.1 else if j.val = 1 then hdr.2 else wordOf W j.val

theorem rootImage_read {κ : ℕ} (hκ : κ < 64) (hdr : E × E) (W : Words) {j : ℕ} (hj : j < 2 ^ κ) :
    (rootImage κ hdr W).read (addressOfIndex j) =
      some (if j = 0 then hdr.1 else if j = 1 then hdr.2 else wordOf W j) :=
  MemoryImage.read_gpow hκ _ ⟨j, hj⟩

theorem one_eq_ofK : (1 : E) = ofK (addressOfIndex 0) := by
  rw [addressOfIndex, pow_zero]; exact (map_one (algebraMap K E)).symm

/-! ## `MainB1` from the placed completeness -/

variable (al : String → Bool)

/-- **`main` placed at the root gives `MainB1`.** -/
theorem mainB1_of_callAtA {k : ℕ} (hk : k ≤ 23) {hdr : E × E} {D : ℕ → Prop} {Out : Reader → Prop}
    {Post : Reader → Tree → Prop} {B e : ℕ} (hB : 2 ≤ B) (he : e ≤ 2 ^ 30)
    (h : CallAtA B2C.fs al B2C.cert k "main" [] [] (· < 2) D Out
      (fun rd => ReadsAt rd 1 [hdr.1, hdr.2]) Post B 0 B e) :
    ∃ (t : Tree) (M : MemoryImage (logMem (t.wordsA B2C.fs coreProgram.loop al))),
      B2C.MainB1 al hdr t M ∧ Post M.read t := by
  obtain ⟨W, hW, hce, -, hr⟩ := h
  have hκ : logMem e < 64 := by
    have := logMem_le_maxLogMem he; unfold maxLogMem at this; omega
  have hle : e ≤ 2 ^ logMem e := le_two_pow_logMem e
  have h4 : 4 ≤ 2 ^ logMem e :=
    Nat.le_trans (by decide : 4 ≤ 2 ^ 23) (Nat.pow_le_pow_right (by decide) (twentyThree_le_logMem e))
  have hread := fun {j : ℕ} (hj : j < 2 ^ logMem e) => rootImage_read hκ hdr W hj
  have hl : LowDef k (rootImage (logMem e) hdr W).read := fun i hi => by
    have : 2 ^ k ≤ 2 ^ logMem e := Nat.pow_le_pow_right (by decide) (hk.trans (twentyThree_le_logMem e))
    rw [hread (by omega)]; rfl
  have hw : HoldsWords (rootImage (logMem e) hdr W).read W := by
    intro q hq j hj
    refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
    rw [Main.addr_ofK]
    have hb := hW.1 q hq
    have h2 : 2 ≤ q.1 + j := by omega
    rw [hread (by omega)]
    simp only [show q.1 + j ≠ 0 by omega, show q.1 + j ≠ 1 by omega, ↓reduceIte]
    rw [wordOf_of_mem hW.2 hq (by omega) (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem]
  have hpre : ReadsAt (rootImage (logMem e) hdr W).read 1 [hdr.1, hdr.2] := by
    intro j hj
    refine ⟨(isInK_iff _).mpr ⟨_, one_eq_ofK⟩, ?_⟩
    rw [one_eq_ofK, Main.addr_ofK, Nat.zero_add]
    have hj2 : j < 2 := by simpa using hj
    rw [hread (by omega)]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  obtain ⟨t, hn, hv, hb, hbl, hend, hpl, hlo, hhi, -, hq⟩ := hr _ hl hw hpre
  have hwA : t.wordsA B2C.fs coreProgram.loop al = e := by
    unfold Tree.wordsA; rw [hbl, hend]
  have hMM : (rootImage (logMem (t.wordsA B2C.fs coreProgram.loop al)) hdr W).read =
      (rootImage (logMem e) hdr W).read := by rw [hwA]
  refine ⟨t, rootImage _ hdr W, ⟨hn, by rw [hMM]; exact hv, hb, by rw [hbl]; exact hpl,
    by rw [hbl]; exact hlo, by rw [hbl]; exact hhi, ?_, by rw [hwA]; exact he⟩, by rw [hMM]; exact hq⟩
  rw [hMM, hread (by omega), hread (by omega)]
  exact ⟨rfl, rfl⟩

/-- **`main`'s placed completeness, composed with B2's**: the reference run's ISA side from
`main`'s `CallAtA` at the root and the hint-only cells' freshness. -/
theorem refX_of_callAtA {exOf : ℕ → List (ℕ × ℕ)} (hx : ExtraOk exOf) (input : PublicInput) {k : ℕ}
    (hk : k ≤ 23) {D : ℕ → Prop} {Out : Reader → Prop} {Post : Reader → Tree → Prop} {B e : ℕ} (hB : 2 ≤ B)
    (he : e ≤ 2 ^ 30)
    (h : CallAtA B2C.fs al B2C.cert k "main" [] [] (· < 2) D Out
      (fun rd => ReadsAt rd 1 [input.word0, input.word1]) Post B 0 B e) :
    ∃ (t : Tree) (M : MemoryImage (logMem (t.wordsA B2C.fs coreProgram.loop al))),
      B2C.MainB1 al (input.word0, input.word1) t M ∧ Post M.read t ∧
      ∃ (ν : ℕ → String → Val → V → E) (n : ℕ),
      (B2C.reTree al ν t).name = "main" ∧
      (∃ rd, HonestAtA coreProgram B2C.fs al B2C.H B2C.C (input.word0, input.word1) (B2C.reTree al ν t) B2C.cert rd [] [] ∧
        HonestX coreProgram B2C.fs al B2C.H B2C.C (input.word0, input.word1) (B2C.reTree al ν t) rd [] []
          (B2C.refWrites al exOf (input.word0, input.word1) t M)) ∧
      ValidExecution guestProgram input
        ⟨logMem ((B2C.reTree al ν t).wordsA B2C.fs coreProgram.loop al),
          honestX coreProgram B2C.fs al B2C.H B2C.C (input.word0, input.word1) (B2C.reTree al ν t)
            (B2C.refWrites al exOf (input.word0, input.word1) t M), n⟩ ∧
      (∀ op, (⟨_, honestX coreProgram B2C.fs al B2C.H B2C.C (input.word0, input.word1) (B2C.reTree al ν t)
          (B2C.refWrites al exOf (input.word0, input.word1) t M), n⟩ : Execution guestProgram).opcodeCount op ≤
        B2C.cnt (B2C.reTree al ν t) op) ∧
      B2C.cnt (B2C.reTree al ν t) = B2C.cnt t ∧
      (B2C.reTree al ν t).wordsA B2C.fs coreProgram.loop al = t.wordsA B2C.fs coreProgram.loop al ∧
      (∀ a ∈ hintWords coreProgram B2C.fs al B2C.H (input.word0, input.word1) (B2C.reTree al ν t), ∃ v, M.read a = some v ∧
        (honestX coreProgram B2C.fs al B2C.H B2C.C (input.word0, input.word1) (B2C.reTree al ν t)
          (B2C.refWrites al exOf (input.word0, input.word1) t M)).read a = some v) ∧
      (∀ I ∈ honestInstsA coreProgram B2C.fs al B2C.H (input.word0, input.word1) (B2C.reTree al ν t), ∀ f σ bufs kids,
        I.t = .node f σ bufs kids → ∀ v ∈ (I.t.events coreProgram).flatMap Ev.uses, ∀ c,
          (refExtra exOf f).lookup v.idx = some c → I.fp + c < 2 ^ 30 ∧
            (honestX coreProgram B2C.fs al B2C.H B2C.C (input.word0, input.word1) (B2C.reTree al ν t)
              (B2C.refWrites al exOf (input.word0, input.word1) t M)).read
                (Parameters.addressOfIndex (I.fp + c)) = some (σ v)) := by
  obtain ⟨t, M, hb, hq⟩ := mainB1_of_callAtA al (hdr := (input.word0, input.word1)) hk hB he h
  exact ⟨t, M, hb, hq, B2C.refX_exists al hx input t M hb⟩

/-! ## `main`, placed, on every node -/

/-- **`main` is complete at the core IR, placed at the root**: on every node with `NodeRelation`
under the deployed seed, within the deployed limits, every child one the guest accepts, `main`
completes at frame `0` and cursor its frame's end, within `2^30` words, loading from its data and
the header, on memories holding the statement's digest at cells `1` and `g`, its pops the honest
pushes, every node exact. -/
def MainCompleteA (k : ℕ) : Prop :=
  ∀ (s : NodeStatement) (w : NodeWitness), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    ∃ (D : ℕ → Prop) (Out : Reader → Prop) (e : ℕ), e ≤ 2 ^ 30 ∧
      CallAtA B2C.fs al B2C.cert k "main" [] [] (· < 2) D Out
        (fun rd => ReadsAt rd 1 (Prover.digestCells (statementDigest guestSeed s)))
        (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.honestPushes guestBytecode guestSeed s w) ∧
          t.Every (ExactAt coreProgram rd))
        (B2C.fs "main") 0 (B2C.fs "main") e

/-- **`MainB1` on every node**, from `main`'s placed completeness, the header the statement
digest's halves, the tree popping the honest pushes and exact at every node. -/
theorem mainB1_of_mainCompleteA {k : ℕ} (hk : k ≤ 23) (h : MainCompleteA al k) (s : NodeStatement)
    (w : NodeWitness) (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w) :
    ∃ (t : Tree) (M : MemoryImage (logMem (t.wordsA B2C.fs coreProgram.loop al))),
      B2C.MainB1 al (digestHalves (statementDigest guestSeed s)) t M ∧
      SameStreams (t.pops coreProgram M.read) (Prover.honestPushes guestBytecode guestSeed s w) ∧
      t.Every (ExactAt coreProgram M.read) := by
  obtain ⟨D, Out, e, he, hc⟩ := h s w hr hl hok
  obtain ⟨t, M, hb, hq⟩ := mainB1_of_callAtA al (hdr := digestHalves (statementDigest guestSeed s)) hk
    (B2C.two_le_fs "main") he hc
  exact ⟨t, M, hb, hq⟩

end
end LeanVM.Guest.Complete
