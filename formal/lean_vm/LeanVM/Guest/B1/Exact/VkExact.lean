/-
  LeanVM.Guest.B1.Exact.VkExact

  `verify_keccak`'s and `keccak_layer`'s paths are exact on every memory they hold on.
-/

module

public import LeanVM.Guest.Exact.Ok
public import LeanVM.Guest.B1.KeccakGkr.VkCA
public import LeanVM.Guest.B1.KeccakGkr.VkCJ
public import LeanVM.Guest.B1.KeccakGkr.VkBody
public import LeanVM.Guest.B1.KeccakGkr.LayerCLift1

/-!
# `verify_keccak`'s and `keccak_layer`'s own hints

`keccak_layer` has no computed hint (`layer_pinned`), so its paths are exact (`pathExact_of_pinned`).
`verify_keccak`'s one computed hint, the bits of `y` (`vkBitsA`), is pinned by squaring each bit and rebuilding
`g^y` from them (`vkBitsT`): on a path that holds, the bits are Boolean and their factors' product is the hint's word,
so it is exact (`bitsExp_exact_of_prod`); its other computed hints are pinned by the next atom (`vk_pinned`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **A body whose computed hints are pinned by the next atom has exact paths.** -/
theorem pathExact_of_pinned {fn : Fn} (h : Stmt.blockNextOk isComputed pinsInverse fn.body = true) :
    PathExactFn fn :=
  fun rd _ _ _ hw hes => exact_of_pinned h hw hes rd

theorem layer_pinned : ∀ first < 2, Stmt.blockNextOk isComputed pinsInverse (layerT first) = true := by
  decide +kernel

theorem layer_pathExact {first : ℕ} (hf : first < 2) {fn : Fn} (hb : fn.body = layerT first) : PathExactFn fn :=
  pathExact_of_pinned (by rw [hb]; exact layer_pinned first hf)

/-- `verify_keccak`'s one computed hint: the bits of `y = τ - 3`. -/
def vkBitsA : Atom := .hint (.bitsExp (.n 21) 5 (.stack [.n 22, .n 23, .n 24, .n 25, .n 26]))

theorem vk_pinned : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ [vkBitsA])) pinsInverse
    (fn% «verify_keccak»).body = true := by
  decide +kernel

theorem vkBits_mem {s : Stmt} (h : s ∈ vkBitsT) : s ∈ vkPre := by
  unfold vkPre vkHeadT
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ h)))))))))

/-- The rebuilt word of `vkBitsT`: the low bits' factors times the eighth power of the high bits'. -/
theorem vkBits_prod {b : ℕ → E} (h3 : b 3 * b 3 = b 3) (h4 : b 4 * b 4 = b 4) {x34 x48 : E}
    (e34 : x34 = (1 + b 3 * (gen ^ 2 ^ 0 + 1)) * (1 + b 4 * (gen ^ 2 ^ 1 + 1)))
    (e48 : x48 = (1 + b 0 * (gen ^ 2 ^ 0 + 1)) * (1 + b 1 * (gen ^ 2 ^ 1 + 1)) * (1 + b 2 * (gen ^ 2 ^ 2 + 1))) :
    x34 * x34 * (x34 * x34) * (x34 * x34 * (x34 * x34)) * x48 =
      ∏ j ∈ Finset.range 5, (1 + b j * (gen ^ 2 ^ j + 1)) := by
  have e8 : x34 * x34 * (x34 * x34) * (x34 * x34 * (x34 * x34)) =
      (1 + b 3 * (gen ^ 2 ^ 3 + 1)) * (1 + b 4 * (gen ^ 2 ^ 4 + 1)) := by
    have e : x34 * x34 * (x34 * x34) * (x34 * x34 * (x34 * x34)) = ((x34 ^ 2) ^ 2) ^ 2 := by ring
    rw [e, e34, mul_pow, mul_pow, mul_pow, bitFactor_pow8 h3 0, bitFactor_pow8 h4 1]
  rw [e8, e48, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_one, mul_comm]
  simp only [mul_assoc]

/-- On a path of `verify_keccak` that holds, the atoms of `vkBitsT` hold. -/
theorem vkBits_pathHolds {rd : Reader} {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ (fn% «verify_keccak»).body = .ret es vs) (hes : ∀ e ∈ es, e.Holds rd σ) :
    ∀ s ∈ vkBitsT, ∀ a, s = .atom a → a.Holds rd σ := by
  rw [vk_body, vkT_pre, walk_flat σ _ vkPre vkPre_kernel.1 (vkPre_disp σ), Out.ret.injEq] at hw
  obtain ⟨rfl, -⟩ := hw
  rintro s hs a rfl
  exact hes (.atom a) (List.mem_flatMap.mpr ⟨_, vkBits_mem hs, by simp [flEvs, Main.slEvs]⟩)

/-- **`verify_keccak`'s paths are exact.** -/
theorem vk_pathExact : PathExactFn (fn% «verify_keccak») := by
  refine pathExact_of_sites vk_pinned fun rd σ es vs hw hes a ha _ => ?_
  rw [List.mem_singleton] at ha
  subst ha
  have H := vkBits_pathHolds hw hes
  simp only [vkBitsT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Stmt.atom.injEq, forall_eq',
    forall_eq, Atom.Holds] at H
  obtain ⟨-, -, c18, m19, -, s0, s1, s2, s3, s4, c25, c26, m27, a28, c29, c30, m31, a32, m33, c34, c35, m36, a37,
    c38, c39, m40, a41, m42, c43, c44, m45, a46, m47, m48, m49, m50, m51, c52, m53, q⟩ := H
  have hb : ∀ j < 5, σ (.n (22 + j)) * σ (.n (22 + j)) = σ (.n (22 + j)) := by
    intro j hj
    interval_cases j
    · exact s0.symm
    · exact s1.symm
    · exact s2.symm
    · exact s3.symm
    · exact s4.symm
  refine bitsExp_exact_of_prod (fun j => σ (.n (22 + j))) rfl hb ?_
  have h20 : σ (.n 21) = σ (.n 53) := by
    rw [m19, e_add_eq_zero_iff.mp q, m53, c18, c52]
  rw [h20, m51, m50, m49, m48]
  exact vkBits_prod (b := fun j => σ (.n (22 + j))) s3.symm s4.symm
    (by rw [m33, a28, a32, m27, m31, c25, c26, c29, c30, word_one, word3, word5])
    (by rw [m47, a46, m45, c44, c43, m42, a41, m40, c39, c38, a37, m36, c35, c34, word_one, word3, word5, word17])

end
end LeanVM.Guest.B1.VerifySub
