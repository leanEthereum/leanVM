/-
  LeanVM.Guest.B1.VsC.OpeningMessageC

  `opening_message__L{n}_L1` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.B1.Fs.MessageComplete
import LeanVM.Guest.CoreRef

/-!
# `opening_message`, complete

`opening_message(fs0..fs4, cursor, out, n, 1)` copies `n` stream words to `out`, absorbs them and
the grinding nonce after them, and permutes. Its body is straight with no hint, and the guest
stream's `opening_message_holds` is its relation's completeness at every deployed `n`; so
`opening_message_complete`: on every memory holding the words `xs` then the nonce `nn` at the
cursor and `xs` at `out`, the call returns its meaning's words, popping nothing, exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fs LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak

@[expose] public section

/-- `opening_message`'s returns on the words `xs` and the nonce `nn`. -/
noncomputable def omRets (f0 f1 f2 f3 f4 cur : E) (xs : List E) (nn : E) : List E :=
  [cellsOfState (omState [f0, f1, f2, f3, f4] xs (some nn)) false 0,
    cellsOfState (omState [f0, f1, f2, f3, f4] xs (some nn)) false 1] ++
    capOf (omState [f0, f1, f2, f3, f4] xs (some nn)) ++ [cur * gen ^ (xs.length + 1)]

/-- What `opening_message__L{n}_L1`'s completeness gives. -/
def OpeningMessageComplete (kd n : ℕ) (name : String) : Prop :=
  ∀ (f0 f1 f2 f3 f4 cur out nn : E) (xs : List E), xs.length = n →
    CallCompletes0 kd name [f0, f1, f2, f3, f4, cur, out] (omRets f0 f1 f2 f3 f4 cur xs nn)
      (fun rd ↦ ReadsAt rd cur (xs ++ [nn]) ∧ ReadsAt rd out xs) PostQuiet

theorem om_complete' {kd n : ℕ} (hp : (n, 1) ∈ omDeployed) {f : Fn}
    (hfind : coreProgram.find? (omName (n, 1)) = some f) (hck : straightChecks f.body = true) :
    OpeningMessageComplete kd n (omName (n, 1)) := by
  intro f0 f1 f2 f3 f4 cur out nn xs hxs
  refine callCompletes0_of_rel_straight hfind hck fun rd _ ⟨hc, ho⟩ ↦ ?_
  refine (opening_message_holds (n, 1) hp rd _ _).mpr ⟨xs, hxs, readsAt_prefix hc, ho, nn,
    fun _ ↦ hxs ▸ readsAt_last hc, ?_⟩
  simp [omRets, hxs]

set_option maxRecDepth 100000 in
theorem opening_message_L1_complete (kd : ℕ) : OpeningMessageComplete kd 1 (omName (1, 1)) :=
  om_complete' (by decide) (coreProgram_find?_at (j := idx% «opening_message__L1_L1») rfl) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem opening_message_L6_complete (kd : ℕ) : OpeningMessageComplete kd 6 (omName (6, 1)) :=
  om_complete' (by decide) (coreProgram_find?_at (j := idx% «opening_message__L6_L1») rfl) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem opening_message_L8_complete (kd : ℕ) : OpeningMessageComplete kd 8 (omName (8, 1)) :=
  om_complete' (by decide) (coreProgram_find?_at (j := idx% «opening_message__L8_L1») rfl) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem opening_message_L12_complete (kd : ℕ) : OpeningMessageComplete kd 12 (omName (12, 1)) :=
  om_complete' (by decide) (coreProgram_find?_at (j := idx% «opening_message__L12_L1») rfl) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem opening_message_L20_complete (kd : ℕ) : OpeningMessageComplete kd 20 (omName (20, 1)) :=
  om_complete' (by decide) (coreProgram_find?_at (j := idx% «opening_message__L20_L1») rfl) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem opening_message_L36_complete (kd : ℕ) : OpeningMessageComplete kd 36 (omName (36, 1)) :=
  om_complete' (by decide) (coreProgram_find?_at (j := idx% «opening_message__L36_L1») rfl) (by decide +kernel)

/-- **Every deployed `opening_message__L{n}_L1` completes.** -/
theorem opening_message_complete (kd : ℕ) : ∀ n, (n, 1) ∈ omDeployed → OpeningMessageComplete kd n (omName (n, 1)) := by
  intro n hn
  simp only [omDeployed, List.mem_cons, Prod.mk.injEq, and_true, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [opening_message_L1_complete kd, opening_message_L6_complete kd, opening_message_L8_complete kd,
    opening_message_L12_complete kd, opening_message_L20_complete kd, opening_message_L36_complete kd]

end
end LeanVM.Guest.B1.VsC
