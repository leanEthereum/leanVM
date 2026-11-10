/-
  LeanVM.Guest.B1.Fs.SqueezePlaced

  `squeeze_point_from__L{n}`, placed and bounded, for every deployed `n`.
-/

module

public import LeanVM.Guest.B1.Fs.LeafPlaced
public import LeanVM.Guest.B1.Fs.SqueezePoint

/-!
# `squeeze_point_from`, placed

A leaf (`spf_leafSpec`, a kernel check) loading only the `n` coordinates at `point` (`spfSpec`),
which its meaning fixes (`spf_pin`): `completeRelB_of_leaf` with `squeeze_point_from_holds`, on the
meaning itself (`MeaningSqueezePointFrom n`).

`squeeze_point_from_completeB` (its frame), `squeeze_point_from_completeB_of` (any bound of its
trees), `squeeze_point_from_completeD`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- `squeeze_point_from__L{n}`'s loads: the `n` coordinates at `point` (argument 6). -/
def spfSpec (n : ℕ) : List (ℕ × ℕ) := [(6, n)]

set_option maxRecDepth 100000 in
theorem spf_leafSpec : (spfDeployed.all fun n => leafSpecB (spfName n) (spfSpec n)) = true := by
  decide +kernel

theorem spf_leafSpecOk : ∀ n ∈ spfDeployed, LeafSpecOk (spfName n) (spfSpec n) := fun n hn =>
  leafSpecOk_of (List.all_eq_true.mp spf_leafSpec n hn)

theorem spf_squeezeN_length : ∀ (m : ℕ) (s : Fs), (s.squeezeN m).1.length = m
  | 0, _ => rfl
  | m + 1, s => by simp only [Fs.squeezeN, List.length_cons, spf_squeezeN_length m]

/-- The meaning fixes the words at `point`. -/
theorem spf_pin (n : ℕ) : ∀ args rets, ∀ q ∈ spfSpec n, ∀ t < q.2, ∃ w, ∀ rd,
    MeaningSqueezePointFrom n rd args rets → LoadHolds rd (args.getD q.1 0) t w := by
  intro args rets q hq t ht
  simp only [spfSpec, List.mem_singleton] at hq
  subst hq
  by_cases hex : ∃ rd, MeaningSqueezePointFrom n rd args rets
  · obtain ⟨rd0, h0⟩ := hex
    obtain ⟨f0, f1, f2, f3, f4, first, point, rfl⟩ : ∃ f0 f1 f2 f3 f4 first point,
        args = [f0, f1, f2, f3, f4, first, point] := by
      match args, h0 with
      | [a, b, c, d, e, g, k], _ => exact ⟨a, b, c, d, e, g, k, rfl⟩
    have hl : t < (first :: ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).squeezeN (n - 1)).1).length := by
      simp only [List.length_cons, spf_squeezeN_length]
      simp only at ht
      omega
    exact ⟨_, fun rd h => h.1 t hl⟩
  · exact ⟨0, fun rd h => absurd ⟨rd, h⟩ hex⟩

/-- **`squeeze_point_from__L{n}`, placed, within any bound on its trees.** -/
theorem squeeze_point_from_completeB_of {n : ℕ} (hn : n ∈ spfDeployed) (κ : ℕ) {B : ℕ}
    (hT : TotalLe coreProgram fs (spfName n) fun _ => B) :
    CompleteRelB fs cert κ (spfName n) (MeaningSqueezePointFrom n) B :=
  completeRelB_of_leaf (spf_leafSpecOk n hn) (squeeze_point_from_holds n hn) (fun _ _ _ h => h)
    (spf_pin n) κ hT

/-- **`squeeze_point_from__L{n}`, placed, within its frame.** -/
theorem squeeze_point_from_completeB {n : ℕ} (hn : n ∈ spfDeployed) (κ : ℕ) :
    CompleteRelB fs cert κ (spfName n) (MeaningSqueezePointFrom n) (fs (spfName n)) :=
  completeRelB_of_leaf' (spf_leafSpecOk n hn) (squeeze_point_from_holds n hn) (fun _ _ _ h => h)
    (spf_pin n) κ

/-- **`squeeze_point_from__L{n}`, placed.** -/
theorem squeeze_point_from_completeD {n : ℕ} (hn : n ∈ spfDeployed) (κ : ℕ) :
    CompleteRelD fs cert κ (spfName n) (MeaningSqueezePointFrom n) :=
  (squeeze_point_from_completeB hn κ).toCompleteRelD

end
end LeanVM.Guest.B1
