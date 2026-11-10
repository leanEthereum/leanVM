import Rv64Verifier.Proofs.Transcript.Repr

/-!
# `TM.samples` as `n` squeezes appended in order

`sqs d sp`: the first `d` challenges squeezed from `sp`, and the sponge after them, built by
appending, as the machine's loop fills its `Vec` (`samples_run`).
-/

namespace Rv64Verifier.Transcript
open LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Model

def sqs : ℕ → Sponge → List E × Sponge
  | 0, sp => ([], sp)
  | d + 1, sp => ((sqs d sp).1 ++ [(spSqueeze (sqs d sp).2).1], (spSqueeze (sqs d sp).2).2)

theorem sqs_cons : ∀ (d : ℕ) (sp : Sponge), sqs (d + 1) sp =
    ((spSqueeze sp).1 :: (sqs d (spSqueeze sp).2).1, (sqs d (spSqueeze sp).2).2)
  | 0, _ => rfl
  | d + 1, sp => by
    rw [sqs, sqs_cons d sp]
    simp [sqs]

theorem sqs_length : ∀ (d : ℕ) (sp : Sponge), (sqs d sp).1.length = d
  | 0, _ => rfl
  | d + 1, sp => by simp [sqs, sqs_length d sp]

theorem samples_run : ∀ (n : ℕ) (T : TState), (TM.samples n).run T =
    some ((sqs n T.sponge).1, { T with sponge := (sqs n T.sponge).2 })
  | 0, T => rfl
  | n + 1, T => by
    have h1 : TM.sample.run T =
        some ((spSqueeze T.sponge).1, { T with sponge := (spSqueeze T.sponge).2 }) := rfl
    simp only [TM.samples, StateT.run_bind, h1, Option.bind_eq_bind, Option.bind_some,
      samples_run n, StateT.run_pure, sqs_cons]
    rfl

end Rv64Verifier.Transcript
