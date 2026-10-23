/-
  LeanVM.Guest.EndCompleteAssembly

  s's `MainComplete` from group 7's `mainComplete_of`, at the callees' bounded theorems
  (`calleesAt_proved`), the children's runs (group 6's `vs_inversion`) and the words budget
  (`eaWords`).
-/

module

public import LeanVM.Guest.EndCompleteWords
public import LeanVM.Guest.B1.VerifySub.Inv6
public import LeanVM.Guest.B1.VerifySub.CTail

/-!
# `main` within the budget, assembled

`ea_mainComplete`: `MainComplete fs cert cnt (eaBudget fs cert H a86 b86 instrs)`, the budget's words
`eaWords` and its instruction counts `instrs`. Each child's run is `vs_inversion`'s of its accepted
proof (within the limits' stack log and stream), of the fresh shape (`ea_freshShaped`), its
openings agreeing in the caps by `DeferredCaps`. Still assumed: `CalleesHyps` (the pure callees'
bounds, `da_verify`'s certificate inequalities, the pending `CompleteTablesAtB` and
`CompleteOpenAtB`), `__loop86`'s affine bound, `DeferredCaps`, the callees' weights `Wt` and the
instruction counts (`hcnt`, `hinstrs`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.End (MainComplete Limits CapsAgree Budget Linear work hdrOf bytecode bytecode_length)

@[expose] public section

/-- **A run's openings agree in its opening's caps when they agree in its whole run's**: the
query steps of the deferring verifier's run include its stacked opening's (group 4 / group 6). -/
def DeferredCaps : Prop :=
  ∀ D : VerifySub.VsData, D.Ok bytecode →
    (∀ b ∈ B1.queriesOf (Verifier.deferredProgram D.fresh bytecode D.pi)
        ⟨Blake2sHash.blake2sBytes (Blake2sHash.digestBytes D.seed ++ Blake2sHash.digestBytes D.pi),
          D.proof.stream, D.proof.openings, []⟩,
      B1.BatchAgrees b.1 b.2) →
    CapAgrees (VerifySub.layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os D.target

/-- An accepted run's fixed claims have the guest's shape. -/
theorem ea_freshShaped {D : VerifySub.VsData} (hok : D.Ok bytecode) : FreshShaped D.fresh := by
  have hd := VerifySub.depth_ge bytecode_length hok
  have hc := hok.chi_length
  have hr := hok.rcs_length
  have hs := hok.s_length
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (D.gr.2.1.take 18 ++ D.alphas).length = 22
    simp only [List.length_append, List.length_take, VerifySub.VsData.alphas, length_sqAll]
    omega
  · show (D.chi.take 8).length = 8
    simp only [List.length_take]; omega
  · show D.rcs.reverse.length = 8
    simp only [List.length_reverse]; omega
  · exact hs

variable (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
  (H : CalleesHyps fs cert bytecode)

/-- **The budget**: the words `eaWords`, the instruction counts `instrs`. -/
def eaBudget (a86 b86 : ℕ) (instrs : Opcode → Linear) : Budget := ⟨eaWords fs H a86 b86, instrs⟩

/-- **`main` is complete within the budget**: group 7's `mainComplete_of` at the callees' bounded
theorems, the children's runs and the words budget. -/
theorem ea_mainComplete {a86 b86 : ℕ} (instrs : Opcode → Linear)
    (h86 : ∀ q, H.B86 (gen ^ q) ≤ a86 * q + b86) (hfs : 2 ≤ fs "main") (hcaps : DeferredCaps)
    (ω : Opcode → String → ℕ) (Wt : ∀ op, MainWeightHyps fs (ω op)) (jt : Opcode → ℕ)
    (hcnt : ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op, cnt t op ≤ t.weight (ω op) + jt op)
    (hinstrs : ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w → ∀ op,
      mainWeight (ω op) (calleeBd fs H) (Wt op) (honestWords seed s w) + jt op ≤ (instrs op).eval (work s w)) :
    MainComplete fs cert cnt (eaBudget fs cert H a86 b86 instrs) := by
  refine mainComplete_of fs cert cnt (eaBudget fs cert H a86 b86 instrs) (calleesAt_proved fs cert H bytecode_length)
    ω Wt jt hfs ?_ ?_ hcnt hinstrs
  · intro seed s w hN hlim hcw c hc
    obtain ⟨-, hdef⟩ := hN.2.1 c hc
    obtain ⟨D, hok, htok, hseed, hpi, hfr, hpf⟩ := VerifySub.vs_inversion bytecode_length hdef
      (fun layout r h => (hlim.stackLog c hc layout r h).1) (hlim.stream c hc)
    refine ⟨hfr ▸ ea_freshShaped hok, D, ⟨hok, htok, hcaps D hok ?_⟩, hpi, hseed, hfr⟩
    rw [hfr, hpi, hseed, hpf]
    exact hcw c hc
  · intro seed s w hN hlim hcw
    exact ea_words fs H h86 (seed := seed) hlim

/-- **Completeness within the budget**, from `ea_mainComplete` and checker K's and agent T's parts
(`CompleteParts`' other fields). -/
theorem ea_guest_complete {a86 b86 : ℕ} (instrs : Opcode → Linear) (Hh : Inst → ℕ → E × E)
    (C : Inst → List (ℕ × E))
    (h86 : ∀ q, H.B86 (gen ^ q) ≤ a86 * q + b86) (hfs : 2 ≤ fs "main") (hcaps : DeferredCaps)
    (ω : Opcode → String → ℕ) (Wt : ∀ op, MainWeightHyps fs (ω op)) (jt : Opcode → ℕ)
    (hcnt : ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op, cnt t op ≤ t.weight (ω op) + jt op)
    (hinstrs : ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w → ∀ op,
      mainWeight (ω op) (calleeBd fs H) (Wt op) (honestWords seed s w) + jt op ≤ (instrs op).eval (work s w))
    (hk : LeanVM.Guest.End.KFactsAll fs Hh C cert) (hrt : LeanVM.Guest.End.CntRetemp fs cnt)
    (htab : ∀ (I : Inst) σ bufs kids, I.t = .node "main" σ bufs kids → tableCells ⊆ C I)
    (hb2 : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
      HonestAt coreProgram fs Hh C hdr T cert rd [] [] →
        Reach guest (honest coreProgram fs Hh C hdr T) ⟨gpow LeanVM.Guest.End.mainEntry, 1⟩ (Regs.final guest))
    (hcount : ∀ hdr (rd : Reader) (T : Tree), T.name = "main" →
      HonestAt coreProgram fs Hh C hdr T cert rd [] [] → ∀ n,
        run guest (honest coreProgram fs Hh C hdr T) n Regs.initial = some (Regs.final guest) →
          ∀ op, (⟨_, honest coreProgram fs Hh C hdr T, n⟩ : Trace guest).count op ≤ cnt T op) :
    LeanVM.Guest.End.GuestCompleteWithin (eaBudget fs cert H a86 b86 instrs) :=
  LeanVM.Guest.End.guest_complete_of_parts
    ⟨ea_mainComplete fs cert cnt H instrs h86 hfs hcaps ω Wt jt hcnt hinstrs, hk, hrt, htab, hb2, hcount⟩

end
end LeanVM.Guest.B1.Main
