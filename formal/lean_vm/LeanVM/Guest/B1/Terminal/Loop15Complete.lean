/-
  LeanVM.Guest.B1.Terminal.Loop15Complete

  `__loop14`, completely: over the public input's honest chain, the loop runs from `g^k` to its
  end `g^m`, loading only the chain and the point.
-/

module

public import LeanVM.Guest.B1.Terminal.PiChain
public import LeanVM.Guest.Memory.Uniform

/-!
# `__loop14`, completely

The honest memory: the chain `cs` (`m + 1` words) at `g^bc` and the point `ps` (`m` words) at
`g^bp`, each step `cs[k+1] = cs[k]·ps[k]`, `1 ≤ k < m`. `l15_iter`: at `g^k`, `1 ≤ k < m`, the
evident valuation walks the body, its loads in the chain's and the point's regions, its call the
next iteration's. `l15_relIn`: the loop's relation from every `g^k`, `1 ≤ k < m`, by a tree
loading only those regions.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- `__loop14`'s statements before its `ret`. -/
def l15Pre : List Stmt :=
  [.atom (.mul (.n 4) (.n 2) (.n 0)), .atom (.load (.n 5) (.n 4) 0),
    .atom (.mul (.n 6) (.n 3) (.n 0)), .atom (.load (.n 7) (.n 6) 0),
    .atom (.mul (.n 8) (.n 5) (.n 7)), .atom (.mul (.n 9) (.n 2) (.n 0)),
    .atom (.load (.n 8) (.n 9) 1), .atom (.const (.n 10) (word 2 0 0)),
    .atom (.mul (.n 11) (.n 0) (.n 10)), .atom (.add (.n 12) (.n 11) (.n 1)),
    .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 0) (.n 13)),
    .callIf (.n 12) "__loop14" [.n 14, .n 1, .n 2, .n 3]]

theorem find_loop15 : coreProgram.find? "__loop14" = some Data.core270 :=
  Program.find?_of_indexOf? (j := 270) (by decide +kernel) rfl

theorem l15_body : Fn.body Data.core270 = l15Pre ++ [.ret []] := by
  obtain ⟨fn, hf, -, hb⟩ := loop15Found
  rw [find_loop15, Option.some.injEq] at hf
  subst hf
  rw [hb]; rfl

theorem l15_straight : l15Pre.all Main.Stmt.straight = true := by decide +kernel

theorem l15_loads : l15Pre.filterMap Stmt.loadS = [(.n 4, 0), (.n 6, 0), (.n 9, 1)] := by
  decide +kernel

theorem l15_callS : l15Pre.filterMap Main.Stmt.callS =
    [(some (.n 12), "__loop14", [.n 14, .n 1, .n 2, .n 3], [])] := by decide +kernel

/-- `__loop14`'s evident valuation at `x`, the chain's word `a` and the point's `b`. -/
noncomputable def l15σ (x N ch p a b : E) : Val :=
  B1.Val.ofArgs [x, N, ch, p, ch * x, a, p * x, b, a * b, ch * x, word 2 0 0, x * word 2 0 0,
    x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0]

theorem l15_addr (b c k : ℕ) : (ofK (addressOfIndex b) * gen ^ c).limb 0 * addressOfIndex k =
    addressOfIndex (b + c + k) := by
  have e : ofK (addressOfIndex b) * gen ^ c = ofK (addressOfIndex (b + c)) := by
    rw [gen_pow_eq_ofK, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]
  rw [e, Main.addr_ofK]

/-- **One iteration of `__loop14`, loading the chain and the point.** -/
theorem l15_iter {rd : Reader} {bc bp m : ℕ} {cs ps : List E} (hcl : cs.length = m + 1)
    (hpl : ps.length = m) (hc : ReadsAt rd (ofK (addressOfIndex bc)) cs) (hp : ReadsAt rd (ofK
        (addressOfIndex bp)) ps)
    (hstep : ∀ k, 1 ≤ k → k < m → cs.getD (k + 1) 0 = cs.getD k 0 * ps.getD k 0) {R : ℕ → Prop}
    (hR : ∀ i, (bc ≤ i ∧ i ≤ bc + m) ∨ (bp ≤ i ∧ i < bp + m) → R i) {k : ℕ} (hk1 : 1 ≤ k)
    (hkm : k < m)
    (hnext : k + 1 < m → coreProgram.RelIn rd R "__loop14"
      [gen ^ (k + 1), gen ^ m, ofK (addressOfIndex bc), ofK (addressOfIndex bp)] []) :
    coreProgram.RelIn rd R "__loop14" [gen ^ k, gen ^ m, ofK (addressOfIndex bc), ofK
        (addressOfIndex bp)] [] := by
  set σ := l15σ (gen ^ k) (gen ^ m) (ofK (addressOfIndex bc)) (ofK (addressOfIndex bp)) (cs.getD k
      0) (ps.getD k 0)
    with hσ
  have hw := Main.walk_straight σ [] l15Pre l15_straight
  rw [← l15_body] at hw
  have lc : ∀ j (hj : j ≤ m), LoadHolds rd (ofK (addressOfIndex bc)) j (cs.getD j 0) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hc j (by omega)
  have lp : LoadHolds rd (ofK (addressOfIndex bp)) k (ps.getD k 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hp k (by omega)
  have hw2 : word 2 0 0 = gen := word_gen
  refine relIn_of_walk coreProgram_wf find_loop15 rfl hw rfl ?_ ?_ ?_
  · intro e he
    obtain ⟨st, hst, he⟩ := List.mem_flatMap.mp he
    simp only [l15Pre, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Main.slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    all_goals try (subst he)
    · rfl
    · show LoadHolds rd (ofK (addressOfIndex bc) * gen ^ k) 0 (cs.getD k 0)
      rw [loadHolds_mul_gen_pow]; exact lc k (by omega)
    · rfl
    · show LoadHolds rd (ofK (addressOfIndex bp) * gen ^ k) 0 (ps.getD k 0)
      rw [loadHolds_mul_gen_pow]; exact lp
    · rfl
    · rfl
    · show LoadHolds rd (ofK (addressOfIndex bc) * gen ^ k) 1 (cs.getD k 0 * ps.getD k 0)
      rw [loadHolds_mul_gen_pow, ← hstep k hk1 hkm]; exact lc (k + 1) (by omega)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rcases he with rfl | he
      · show IsInK (gen ^ k * word 2 0 0 + gen ^ m)
        rw [hw2]
        exact isInK_add (isInK_mul (gen_pow_isInK k) (by simpa using gen_pow_isInK 1))
          (gen_pow_isInK m)
      · split at he <;> subst he <;> trivial
  · intro A hA
    rw [loadAddrs_straight σ l15Pre l15_straight, l15_loads] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl
    · refine ⟨bc + k + 0, l15_addr bc k 0, hR _ (Or.inl ⟨by omega, by omega⟩)⟩
    · refine ⟨bp + k + 0, l15_addr bp k 0, hR _ (Or.inr ⟨by omega, by omega⟩)⟩
    · refine ⟨bc + k + 1, l15_addr bc k 1, hR _ (Or.inl ⟨by omega, by omega⟩)⟩
  · intro c hc htaken
    rw [(Main.straight_parts σ l15Pre l15_straight).2.2.2, l15_callS] at hc
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc
    simp only [Main.mkCall, decide_eq_true_eq] at htaken ⊢
    have hk' : k + 1 < m := by
      by_contra hc'
      have : k + 1 = m := by omega
      subst this
      apply htaken
      show gen ^ k * word 2 0 0 + gen ^ (k + 1) = 0
      rw [hw2, gen_pow_mul_gen]; exact e_add_self _
    show coreProgram.RelIn rd R "__loop14"
      [gen ^ k * word 2 0 0, gen ^ m, ofK (addressOfIndex bc), ofK (addressOfIndex bp)] []
    rw [hw2, gen_pow_mul_gen]
    exact hnext hk'

/-- **`__loop14`, completely, loading the chain and the point**: from every `g^k`, `1 ≤ k < m`. -/
theorem l15_relIn {rd : Reader} {bc bp m : ℕ} {cs ps : List E} (hcl : cs.length = m + 1)
    (hpl : ps.length = m) (hc : ReadsAt rd (ofK (addressOfIndex bc)) cs) (hp : ReadsAt rd (ofK
        (addressOfIndex bp)) ps)
    (hstep : ∀ k, 1 ≤ k → k < m → cs.getD (k + 1) 0 = cs.getD k 0 * ps.getD k 0) {R : ℕ → Prop}
    (hR : ∀ i, (bc ≤ i ∧ i ≤ bc + m) ∨ (bp ≤ i ∧ i < bp + m) → R i) :
    ∀ t k, k + 1 + t = m → 1 ≤ k →
      coreProgram.RelIn rd R "__loop14" [gen ^ k, gen ^ m, ofK (addressOfIndex bc), ofK
          (addressOfIndex bp)] [] := by
  intro t
  induction t with
  | zero =>
    exact fun k hk hk1 ↦ l15_iter hcl hpl hc hp hstep hR hk1 (by omega) fun h ↦ absurd h (by omega)
  | succ t ih =>
    exact fun k hk hk1 ↦ l15_iter hcl hpl hc hp hstep hR hk1 (by omega)
      fun _ ↦ ih (k + 1) (by omega) (by omega)

end
end LeanVM.Guest.B1.VerifySub
