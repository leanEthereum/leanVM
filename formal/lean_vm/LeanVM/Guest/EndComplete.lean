/-
  LeanVM.Guest.EndComplete

  The completeness end theorem's `honest` piece from its owners' forms: group 7's uniform placed
  relation of `main` on a layout within the budget, checker K's certificate facts, and the
  instruction counts' invariance under the re-choice of temporaries.
-/

module

public import LeanVM.Guest.End
public import LeanVM.Guest.B1.Main.HonestPiece

/-!
# Completeness, the `honest` piece

`MainComplete cert cnt b` is what group 7's completeness of `main` gives for `NodeRel` within the
limits and the caps: a consistent layout `L` in `[2, N)`, `N ≤ 2^32` words within the budget's
words, on every memory holding which and the statement's digest at words `0`, `1` `main` holds by
a tree placed at `0` (`RelAtIn`'s tree, as `honest_of_relAtIn` takes it) within the budget's
instruction counts. The counts are bounded on that tree, the one completeness builds, not on every
valid tree: `main`'s and its children's counts are hints, which a valid tree pins only up to
BLAKE2s collisions. `KFactsAll` is checker K's certificate
facts for every tree of `main` (`B1.Main.KFacts`), and `CntRetemp cnt` that the counts do not
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

/-- **`main`'s completeness within the budget** (group 7): for `NodeRel` within the limits and
the caps, the budget's size within `2^28`, a consistent layout of `N` words, `N` within the budget,
on every memory holding which with the statement's digest as its header `main` holds by a tree
placed at `0`, of `N` words, loading from its own data or its header, within the budget's
instruction counts. -/
def MainComplete : Prop :=
  ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w → b.size (work s w) ≤ 2 ^ 28 →
    ∃ (N : ℕ) (L : Layout), LConsistent L ∧ (∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ N) ∧
      N ≤ 2 ^ 32 ∧ N ≤ b.words.eval (work s w) ∧
      ∀ rd, LowDef 16 rd → MemL rd L → rd 1 = some (hdrOf (statementDigest seed s)).1 →
        rd g = some (hdrOf (statementDigest seed s)).2 →
          ∃ t : Tree, t.name = "main" ∧ t.Valid coreProgram rd [] [] ∧ t.BufsOk coreProgram ∧
            t.Placed coreProgram fs cert 0 ∧ t.total fs = N ∧
            t.LoadsIn coreProgram fs cert (fun i => i < 2) 0 ∧
            ∀ op, cnt t op ≤ (b.instrs op).eval (work s w)

/-- **The certificate's facts for every tree of `main`** (checker K). -/
def KFactsAll : Prop :=
  ∀ hdr (T : Tree), T.name = "main" → KFacts coreProgram fs cert H C hdr T

/-- **The instruction counts do not see the temporaries' values.** -/
def CntRetemp : Prop :=
  ∀ (ν : ℕ → String → Val → V → E) (t : Tree), cnt (t.retemp coreProgram fs ν 0) = cnt t

/-- **What completeness within the budget `b` rests on, in its owners' forms.** -/
structure CompleteParts : Prop where
  /-- Group 7: `main`'s completeness within the budget. -/
  main : MainComplete fs cert cnt b
  /-- Checker K: the certificate's facts. -/
  kfacts : KFactsAll fs H C cert
  /-- Checker K: the counts do not see the temporaries. -/
  cntRetemp : CntRetemp fs cnt
  /-- Agent T: `main`'s cells hold its jump table. -/
  table : ∀ (I : Inst) σ bufs kids, I.t = .node "main" σ bufs kids → tableCells ⊆ C I
  /-- Checker K: `CompletePiecesWithin.b2`. -/
  b2 : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] →
      Reach guest (honest coreProgram fs H C hdr T) ⟨gpow mainEntry, 1⟩ (Regs.final guest)
  /-- Checker K: `CompletePiecesWithin.count`. -/
  count : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      run guest (honest coreProgram fs H C hdr T) n Regs.initial = some (Regs.final guest) →
        ∀ op, (⟨_, honest coreProgram fs H C hdr T, n⟩ : Trace guest).count op ≤ cnt T op

variable {fs H C cert cnt b}

/-- **The `honest` piece**, from `main`'s completeness, the certificate's facts and the counts'
invariance. -/
theorem honest_of_main (hm : MainComplete fs cert cnt b) (hk : KFactsAll fs H C cert)
    (hc : CntRetemp fs cnt) :
    ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w → b.size (work s w) ≤ 2 ^ 28 →
      ∃ (rd : Reader) (T : Tree), T.name = "main" ∧
        HonestAt coreProgram fs H C (hdrOf (statementDigest seed s)) T cert rd [] [] ∧
        T.total fs ≤ b.words.eval (work s w) ∧ ∀ op, cnt T op ≤ (b.instrs op).eval (work s w) := by
  intro seed s w hrel hlim hcap hbs
  obtain ⟨N, L, hcons, hin, hN, hNb, hrelL⟩ := hm seed s w hrel hlim hcap hbs
  set hdr := hdrOf (statementDigest seed s) with hhdr
  have h16 : 16 ≤ logMem N := minLogMem_le_logMem N
  have h64 : logMem N < 64 := by have := logMem_le_maxLogMem hN; unfold maxLogMem at this; omega
  set M := imageOf (logMem N) L hdr with hM
  have hlow : LowDef 16 M.read := fun i hi => by
    have hi' : i < 2 ^ logMem N :=
      lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) h16)
    rw [MemImage.read_gpow h64 M ⟨i, hi'⟩]; rfl
  have hL := B1.Main.memL_imageOf h64 hcons (fun q hq => ⟨(hin q hq).1,
    le_trans (hin q hq).2 (le_two_pow_logMem N)⟩) hdr
  obtain ⟨hh0, hh1⟩ := B1.Main.imageOf_hdr h64 (by omega) L hdr
  have e0 : (1 : K) = Parameters.gpow 0 := by simp [Parameters.gpow]
  have e1 : g = Parameters.gpow 1 := by simp [Parameters.gpow]
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
