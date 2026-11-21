/-
  LeanVM.Guest.B1.Main.MainAtR

  `main` placed within its words, its callees' trees satisfying predicates of the memory.
-/

module

public import LeanVM.Guest.B1.Main.MainAt
public import LeanVM.Guest.Budget.BoundedR

/-!
# `main`, placed, its callees' predicates of the memory

`main_relAtInTBR`: `main_relAtInTB` with the callees `KidsDTBR`, their trees satisfying `Ts rd` on each memory `rd`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Guest.B1 (KidsDTBR kidsFromInT_of_kidsDTBR DisjL Within LowDef bufL)

@[expose] public section

/-- **`main` at `fp` within its words, its callees' trees satisfying `Ts rd` on each memory `rd`.** -/
theorem main_relAtInTBR (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (d : MainData)
    (own : List (List E)) (hfit : List.Forall₂ (fun c s => c.length ≤ s) own (mSizes d))
    (hb : MainBounds (2 ^ 23) (d.toIn fs fp))
    (Ts : Reader → List (Tree → Prop)) (Bs : List ℕ)
    (hok : KidsDTBR fs cert 23 (mKids (d.toIn fs fp) (bufL (fp + fs "main") (mSizes d) own ++ etL d fs fp)) Ts Bs)
    (hmm : ∀ rd, B1.Main.MemL rd (bufL (fp + fs "main") (mSizes d) own) →
      LoadHolds rd 1 0 (digestHalves d.sdg).1 → LoadHolds rd gen 0 (digestHalves d.sdg).2 →
        MainMem rd (d.toIn fs fp)) :
    ∃ (n : ℕ) (L : B1.Main.Layout), n ≤ mainB fs d (mKids (d.toIn fs fp)
        (bufL (fp + fs "main") (mSizes d) own ++ etL d fs fp)) Bs ∧ Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧
      DisjL L ∧ (∀ q ∈ bufL (fp + fs "main") (mSizes d) own ++ etL d fs fp, q ∈ L) ∧
      ∀ rd, LowDef 23 rd → B1.Main.MemL rd L → LoadHolds rd 1 0 (digestHalves d.sdg).1 →
        LoadHolds rd gen 0 (digestHalves d.sdg).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (d.toIn fs fp) ∧
            KidsT (mCalls σ (d.toIn fs fp)) ((fun _ => True) :: Ts rd) ks ∧
            calls (mEvs σ) = mCalls σ (d.toIn fs fp) ∧ bufs = mSizes d) := by
  obtain ⟨Nk, Lk, outs, hNk, hoo, hW, hD, -, hKids⟩ :=
    kidsFromInT_of_kidsDTBR (fs := fs) (cert := cert) 23 _ Ts Bs hok (etB fs (mK0 d fs fp) + 2284)
  obtain ⟨L, h⟩ := main_relAtInT_core fs cert fp d own hfit hb Ts Nk Lk outs hoo hW hD hKids hmm
  exact ⟨_, L, by unfold mainB; omega, h⟩

end
end LeanVM.Guest.B1.Main
