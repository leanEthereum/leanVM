/-
  LeanVM.Guest.B1.Fs.MessagePlaced

  `opening_message__L{n}_L{nonce}`, placed and bounded, for every deployed message.
-/

module

public import LeanVM.Guest.B1.Fs.LeafPlaced
public import LeanVM.Guest.B1.Fs.MessageComplete

/-!
# `opening_message`, placed

A leaf (`om_leafSpec`, a kernel check) loading the `n + nonce` words at the cursor and the `n` at
`out` (`omSpec`). Its meaning leaves the words free, so its precondition names them: `omPre n nonce
ws`, the stream words `ws` (the nonce last when `nonce = 1`) at the cursor, their first `n` at
`out`, and the meaning. Then `completeRelB_of_leaf` with `opening_message_holds`.

`opening_message_completeB` (its frame), `opening_message_completeB_of` (any bound of its trees),
`opening_message_completeD`, and `verify_sub`'s `opening_message__L1_L1`
(`opening_message_L1_L1_completeB`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- `opening_message__L{n}_L{nonce}`'s loads: `n + nonce` words at the cursor (argument 5), `n` at
`out` (argument 6). -/
def omSpec (n nonce : ℕ) : List (ℕ × ℕ) := [(5, n + nonce), (6, n)]

/-- What `opening_message__L{n}_L{nonce}`'s completeness asks of its call: the stream words `ws`
(`n` words, then the nonce when `nonce = 1`) at the cursor, the first `n` at `out`, and its
meaning. -/
def omPre (n nonce : ℕ) (ws : List E) (rd : Reader) (args rets : List E) : Prop :=
  ws.length = n + nonce ∧ ReadsAt rd (args.getD 5 0) ws ∧ ReadsAt rd (args.getD 6 0) (ws.take n) ∧
    MeaningOpeningMessage n nonce rd args rets

set_option maxRecDepth 100000 in
theorem om_leafSpec : (omDeployed.all fun p => leafSpecB (omName p) (omSpec p.1 p.2)) = true := by
  decide +kernel

theorem om_leafSpecOk : ∀ p ∈ omDeployed, LeafSpecOk (omName p) (omSpec p.1 p.2) := fun p hp =>
  leafSpecOk_of (List.all_eq_true.mp om_leafSpec p hp)

/-- The precondition fixes the words the message loads. -/
theorem om_pin (n nonce : ℕ) (ws : List E) : ∀ args rets, ∀ q ∈ omSpec n nonce, ∀ t < q.2, ∃ w,
    ∀ rd, omPre n nonce ws rd args rets → LoadHolds rd (args.getD q.1 0) t w := by
  intro args rets q hq t ht
  by_cases hl : ws.length = n + nonce
  · simp only [omSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · have ht' : t < ws.length := by rw [hl]; exact ht
      exact ⟨_, fun rd h => h.2.1 t ht'⟩
    · have ht' : t < (ws.take n).length := by
        simp only [List.length_take]
        simp only at ht
        omega
      exact ⟨_, fun rd h => h.2.2.1 t ht'⟩
  · exact ⟨0, fun rd h => absurd h.1 hl⟩

/-- **`opening_message__L{n}_L{nonce}`, placed, within any bound on its trees.** -/
theorem opening_message_completeB_of {p : ℕ × ℕ} (hp : p ∈ omDeployed) (ws : List E) (κ : ℕ)
    {B : ℕ} (hT : TotalLe coreProgram fs (omName p) fun _ => B) :
    CompleteRelB fs cert κ (omName p) (omPre p.1 p.2 ws) B :=
  completeRelB_of_leaf (om_leafSpecOk p hp) (opening_message_holds p hp)
    (fun _ _ _ h => h.2.2.2) (om_pin p.1 p.2 ws) κ hT

/-- **`opening_message__L{n}_L{nonce}`, placed, within its frame.** -/
theorem opening_message_completeB {p : ℕ × ℕ} (hp : p ∈ omDeployed) (ws : List E) (κ : ℕ) :
    CompleteRelB fs cert κ (omName p) (omPre p.1 p.2 ws) (fs (omName p)) :=
  completeRelB_of_leaf' (om_leafSpecOk p hp) (opening_message_holds p hp)
    (fun _ _ _ h => h.2.2.2) (om_pin p.1 p.2 ws) κ

/-- **`opening_message__L{n}_L{nonce}`, placed.** -/
theorem opening_message_completeD {p : ℕ × ℕ} (hp : p ∈ omDeployed) (ws : List E) (κ : ℕ) :
    CompleteRelD fs cert κ (omName p) (omPre p.1 p.2 ws) :=
  (opening_message_completeB hp ws κ).toCompleteRelD

/-- **`opening_message__L1_L1`** (`verify_sub`'s), placed within its frame. -/
theorem opening_message_L1_L1_completeB (ws : List E) (κ : ℕ) :
    CompleteRelB fs cert κ "opening_message__L1_L1" (omPre 1 1 ws) (fs "opening_message__L1_L1") :=
  opening_message_completeB (p := (1, 1)) (by simp [omDeployed]) ws κ

end
end LeanVM.Guest.B1
