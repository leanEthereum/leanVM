module

public import LeanVM.Cost.AS.Bounds.Budget
public import LeanVM.Cost.AS.Glue
import all LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.Extraction.AS.TraceShape
import all LeanVM.Protocol.EndToEnd.Sound.SkelPairs
import all LeanVM.Protocol.EndToEnd.Sound.SkelWhir
import all LeanVM.Protocol.EndToEnd.Sound.Avail

/-!
# Bounds: the agreement-set extractor's price

* `extractL_steps`: a successful extraction's intermediate values;
* `extract_roots`, `extract_trace`: its roots' shapes (`RootsOk`) and its trace's (`TraceSmall`,
  `traceDepth`).
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Verifier LeanVM.Extraction.AS LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Semantics LeanVM.Protocol.EndToEnd.Sound

public section

/-- **A successful extraction's steps.** -/
theorem extractL_steps {prog : LeanIsaProgram} {input : PublicInput}
    {qs : List (Common.PermutationQuery KeccakState × KeccakState)} {π : Proof} {t : Execution prog}
    (h : extractL prog input qs π = some t) :
    ∃ seed r₁ a r₂ tr,
      seedWithHash (Protocol.KeccakHash.keccak256With (fwdF (fwdIndex qs))) (fwdF (fwdIndex qs))
          (bytecodeWords prog) (publicInputDigest input) = some seed ∧
        skelReplayP (fwdF (fwdIndex qs)) skSizes (startState π seed) = some r₁ ∧
        decSizesL (bytecodeWords prog) r₁.1 = some a ∧
        skelReplayP (fwdF (fwdIndex qs)) (skBodyL a.1 a.2) r₁.2 = some r₂ ∧
        decBodyL a.1 a.2 r₂.1 = some tr ∧ finishL prog input qs ((true, (a, tr)), r₂.2) = some t := by
  unfold extractL at h
  obtain ⟨seed, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r₁, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r₂, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tr, h5, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨seed, r₁, a, r₂, tr, h1, h2, h3, h4, h5, h⟩

/-- **The roots a successful replay records**: the body's commits, within `RootsOk`. -/
theorem extract_roots {F : KeccakState → Option KeccakState} {π : Proof} {seed : KeccakState}
    {bc : List K} {r₁ r₂ : List EvP × VerifierProgramState} {lay : LayoutLite} {ρ : ℕ}
    (h2 : skelReplayP F skSizes (startState π seed) = some r₁) (h3 : decSizesL bc r₁.1 = some (lay, ρ))
    (h4 : skelReplayP F (skBodyL lay ρ) r₁.2 = some r₂) :
    RootsOk lay.stackLog ρ (r₂.2.roots.map Prod.snd) := by
  obtain ⟨-, hρ1, hρ2, hs1, hs2⟩ := decSizesL_facts h3
  have e1 := roots_skelReplayP F skSizes _ r₁ h2
  have e2 := roots_skelReplayP F (skBodyL lay ρ) _ r₂ h4
  have e0 : commitsOf skSizes = [] := commitsOf_replicate_read _
  simp only [startState, List.map_nil, List.nil_append, e0] at e1
  rw [e2, e1, List.nil_append, commitsOf_skBodyL]
  exact rootsOk_bodyCommits hs1 hs2 hρ1 hρ2

/-- **A successfully decoded trace is small**, of depth below six. -/
theorem extract_trace {bc : List K} {h₁ : List EvP} {lay : LayoutLite} {ρ : ℕ} {h : List EvP}
    {tr : WhirTrace} (h3 : decSizesL bc h₁ = some (lay, ρ)) (h5 : decBodyL lay ρ h = some tr) :
    TraceSmall tr ∧ traceDepth tr < 6 ∧ TraceShape lay.stackLog 0
      ((Whir.ladder lay.stackLog ρ).getD []) tr := by
  obtain ⟨-, hρ1, hρ2, hs1, hs2⟩ := decSizesL_facts h3
  obtain ⟨cfg, hc, hsh⟩ := decBodyL_shape h5
  obtain ⟨hl, hf⟩ := ladder_small hc hs1 hs2 hρ1 hρ2
  have hm : Whir.maxLogStack = 30 := rfl
  obtain ⟨h1, h2⟩ := traceSmall_of_shape lay.stackLog (by omega) 0 cfg tr hsh hf
  rw [hc, Option.getD_some]
  exact ⟨h1, by omega, hsh⟩

end

end LeanVM.Cost.Bounds.AS
