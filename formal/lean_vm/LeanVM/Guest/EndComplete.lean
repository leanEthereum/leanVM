/-
  LeanVM.Guest.EndComplete

  The completeness end theorem's `honest` piece from its owners' forms: B1's uniform placed
  relation of `main` on a layout within the budget, the checker's certificate facts, and the
  instruction counts' invariance under the re-choice of temporaries.
-/

module

public import LeanVM.Guest.Complete
public import LeanVM.Guest.Memory.HonestMain
public import LeanVM.Guest.AcceptableChild

/-!
# Completeness, the `honest` piece

`MainComplete cert cnt b` is what the completeness of `main` (B1) gives for `NodeRelation` within the
limits, the caps agreeing and no zero challenge where the guest divides: a consistent layout `L`
in `[2, N)`, `N ≤ 2^30` words within the budget's words, on every memory holding which and the statement's digest at words `0`, `1` `main` holds by
a tree placed at `0` (`RelAtIn`'s tree, as `honest_of_relAtIn` takes it) within the budget's
instruction counts. The counts are bounded on that tree, the one completeness builds, not on every
valid tree: `main`'s and its children's counts are hints, which a valid tree pins only up to
Keccak-256 collisions. `KFactsAll` is the checker's certificate facts for every tree of `main` (`B1.Main.KFacts`), and `CntRetemp cnt` that the counts do not
see the temporaries' values (`Tree.retemp`). `honest_of_main` gives
`CompletePiecesWithin.honest`, by `honestAt_retemp` as in `honest_of_relAtIn`, keeping the tree
the counts are bounded on.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Main (KFacts imageOf LConsistent Layout MemL)

@[expose] public section

variable (fs : String → ℕ) (H : Inst → ℕ → E × E) (C : Inst → List (ℕ × E))
  (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ) (b : Budget)

/-- **`main`'s completeness within the budget** (B1, `main` last): for `NodeRelation` within the
limits, the caps and no zero challenge, the budget's size within `2^30`, a consistent layout of
`N` words, `N` within the budget, on every memory of `2^logMem N` words holding which with the
statement's digest as its header `main` holds by a tree placed at `0`, of `N` words, loading from
its own data or its header, within the budget's instruction counts. -/
def MainComplete : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w → b.size (work s w) ≤ 2 ^ 30 →
    ∃ (N : ℕ) (L : Layout), LConsistent L ∧ (∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ N) ∧
      N ≤ 2 ^ 30 ∧ N ≤ b.words.eval (work s w) ∧
      ∀ rd, LowDef (logMem N) rd → MemL rd L → rd 1 = some (hdrOf (statementDigest seed s)).1 →
        rd g = some (hdrOf (statementDigest seed s)).2 →
          ∃ t : Tree, t.name = "main" ∧ t.Valid coreProgram rd [] [] ∧ t.BufsOk coreProgram ∧
            t.Placed coreProgram fs cert 0 ∧ t.total fs = N ∧
            t.LoadsIn coreProgram fs cert (fun i => i < 2) 0 ∧
            ∀ op, cnt t op ≤ (b.instrs op).eval (work s w)

/-- **The certificate's facts for every tree of `main`** (the checker). -/
def KFactsAll : Prop :=
  ∀ hdr (T : Tree), T.name = "main" → KFacts coreProgram fs cert H C hdr T

/-- **The instruction counts do not see the temporaries' values.** -/
def CntRetemp : Prop :=
  ∀ (ν : ℕ → String → Val → V → E) (t : Tree), cnt (t.retemp coreProgram fs ν 0) = cnt t

/-- **What completeness within the budget `b` rests on, in its owners' forms.** -/
structure CompleteParts : Prop where
  /-- B1: `main`'s completeness within the budget. -/
  main : MainComplete fs cert cnt b
  /-- The checker: the certificate's facts. -/
  kfacts : KFactsAll fs H C cert
  /-- The checker: the counts do not see the temporaries. -/
  cntRetemp : CntRetemp fs cnt
  /-- `main`'s cells hold its jump table. -/
  table : ∀ (I : Inst) σ bufs kids, I.t = .node "main" σ bufs kids → tableCells ⊆ C I
  /-- The checker: `CompletePiecesWithin.b2`. -/
  b2 : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] →
      Reach guestProgram (honest coreProgram fs H C hdr T) ⟨addressOfIndex mainEntry, 1⟩ (Registers.final guestProgram)
  /-- The checker: `CompletePiecesWithin.count`. -/
  count : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      run guestProgram (honest coreProgram fs H C hdr T) n Registers.initial = some (Registers.final guestProgram) →
        ∀ op, (⟨_, honest coreProgram fs H C hdr T, n⟩ : Execution guestProgram).opcodeCount op ≤
            cnt T op

variable {fs H C cert cnt b}

/-- **The `honest` piece**, from `main`'s completeness, the certificate's facts and the counts'
invariance. -/
theorem honest_of_main (hm : MainComplete fs cert cnt b) (hk : KFactsAll fs H C cert)
    (hc : CntRetemp fs cnt) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w → b.size (work s w) ≤ 2 ^ 30 →
      ∃ (rd : Reader) (T : Tree), T.name = "main" ∧
        HonestAt coreProgram fs H C (hdrOf (statementDigest seed s)) T cert rd [] [] ∧
        T.total fs ≤ b.words.eval (work s w) ∧ ∀ op, cnt T op ≤ (b.instrs op).eval (work s w) := by
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
  obtain ⟨t, hn, hv, hb, hp, ht, hl, hcntT⟩ := hrelL M.read hlow hL (by rw [e0]; exact hh0)
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
  obtain ⟨ν, hν⟩ := honestAt_retemp hd
  refine ⟨_, _, by rw [name_retemp]; exact hn, hν, by rw [total_retemp]; exact hNb, fun op => ?_⟩
  rw [hc]
  exact hcntT op

/-- **Completeness within the budget `b`, from its owners' forms.** -/
theorem guest_complete_of_parts (h : CompleteParts fs H C cert cnt b) : GuestCompleteWithin b :=
  guest_complete_within
    { honest := honest_of_main h.main h.kfacts h.cntRetemp
      table := h.table
      b2 := h.b2
      count := h.count }

end
end LeanVM.Guest.End
