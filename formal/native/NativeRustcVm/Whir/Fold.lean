module

public import NativeRustcVm.Whir.Sample

/-!
# `foldRound` step by step

`foldRound_run`: the four scalars read, the grind, the two squeezes, the folded state `foldW`.
-/

namespace NativeRustcVm.Whir

open NativeVm.Model

@[expose] public section

/-- The state after a fold round with scalars `u0 v c0 c1` and challenges `α β`. -/
def foldW (w : WhirStateW) (u0 v c0 c1 α β : EW) : WhirStateW :=
  { w with claim := u0 + α * (u0 + w.claim) + α * α * v + β * c0 + α * β * (c0 + c1),
           alphas := w.alphas.push α }

theorem foldRound_run (w : WhirStateW) (s : TState) : (foldRound w).run s =
    (readScalar.run s).bind fun r1 ↦ (readScalar.run r1.2).bind fun r2 ↦
      (readScalar.run r2.2).bind fun r3 ↦ (readScalar.run r3.2).bind fun r4 ↦
      ((grind 7).run r4.2).bind fun r5 ↦
        some ((foldW w r1.1 r2.1 r3.1 r4.1 (sq r5.2).1 (sq (sq r5.2).2).1,
          ⟨(sq r5.2).1, (sq (sq r5.2).2).1⟩), (sq (sq r5.2).2).2) := rfl

end

end NativeRustcVm.Whir
