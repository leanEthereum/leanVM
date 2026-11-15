/-
  LeanVM.Guest.Memory.HeapOne

  Callees popping advised sizes through one function only, called at most once: they pop that call's.
-/

module

public import LeanVM.Guest.Memory.HeapSlots

/-!
# One callee with advised sizes

`heapPopsKids_one`: callees each in a call-closed set `S` of functions without advised buffers or of `g`, at most
one call of `g`, each valid tree of `g` among them popping `H`, and one such tree among them: the callees pop `H`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {rd : Reader} {σ : Val} {g : String} {H : List (List E)} {S : String → Prop}

/-- **A callee of `S` pops no advised size**, entered or not. -/
theorem heapPops_kid_of (hS : CallsIn coreProgram S) (hs : ∀ f, S f → heapSlots f = []) {c : Call} {k : Tree}
    (hn : k.name = c.f) (hg : S c.f)
    (hv : if c.taken then k.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
      else (∃ f σ', k = .phantom f σ') ∧ Phantom coreProgram k (c.args.map σ)) : k.heapPops heapSlots = [] := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at hv
    exact heapPops_nil hS hs k (hn ▸ hg) hv
  · rw [ite_eq_right ht] at hv
    obtain ⟨⟨f, σ', rfl⟩, -⟩ := hv
    rw [Tree.heapPops]

theorem kidsValid_mem_name : ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid coreProgram rd σ cs ks →
    ∀ k ∈ ks, ∃ c ∈ cs, c.f = k.name
  | c :: cs, k' :: ks, ⟨hn, _, hks⟩, k, hk => by
      rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨c, List.mem_cons_self, hn.symm⟩
      · obtain ⟨c', hc', e⟩ := kidsValid_mem_name hks k hk
        exact ⟨c', List.mem_cons_of_mem _ hc', e⟩
  | [], [], _, _, hk => by simp at hk
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

/-- Callees of no call of `g` pop no advised size. -/
theorem heapPopsKids_zero (hS : CallsIn coreProgram S) (hs : ∀ f, S f → heapSlots f = []) :
    ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid coreProgram rd σ cs ks → (∀ c ∈ cs, S c.f ∨ c.f = g) → (cs.filter (·.f == g)).length = 0 → Tree.heapPopsKids heapSlots ks = []
  | c :: cs, k :: ks, ⟨hn, hv, hks⟩, hcs, h0 => by
      have hc : c.f ≠ g := fun e => by simp [e] at h0
      have h0' : (cs.filter (·.f == g)).length = 0 := by
        simpa [List.filter_cons, hc] using h0
      rw [heapPopsKids_cons, heapPopsKids_zero hS hs hks (fun c' h => hcs c' (List.mem_cons_of_mem _ h)) h0',
        heapPops_kid_of hS hs hn ((hcs c List.mem_cons_self).resolve_right hc) hv]
      rfl
  | [], [], _, _, _ => by rw [Tree.heapPopsKids]
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

/-- **Callees with one call of `g` whose valid trees pop `H`, one among them, pop `H`.** -/
theorem heapPopsKids_one (hS : CallsIn coreProgram S) (hs : ∀ f, S f → heapSlots f = []) {t0 : Tree} :
    ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid coreProgram rd σ cs ks → (∀ c ∈ cs, S c.f ∨ c.f = g) → (cs.filter (·.f == g)).length ≤ 1 →
    (∀ k ∈ ks, k.name = g → (∃ a r, k.Valid coreProgram rd a r) → k.heapPops heapSlots = H) →
    t0 ∈ ks → t0.name = g → (∃ a r, t0.Valid coreProgram rd a r) → Tree.heapPopsKids heapSlots ks = H
  | c :: cs, k :: ks, ⟨hn, hv, hks⟩, hcs, h1, hH, h0, h0n, h0v => by
      have hcs' : ∀ c' ∈ cs, S c'.f ∨ c'.f = g := fun c' h => hcs c' (List.mem_cons_of_mem _ h)
      have hH' : ∀ k' ∈ ks, k'.name = g → (∃ a r, k'.Valid coreProgram rd a r) → k'.heapPops heapSlots = H :=
        fun k' h => hH k' (List.mem_cons_of_mem _ h)
      rw [heapPopsKids_cons]
      by_cases hc : c.f = g
      · have hz : (cs.filter (·.f == g)).length = 0 := by
          simp only [List.filter_cons, hc, beq_self_eq_true, ↓reduceIte, List.length_cons] at h1
          omega
        rw [heapPopsKids_zero hS hs hks hcs' hz, List.append_nil]
        rcases List.mem_cons.mp h0 with rfl | h0
        · exact hH _ List.mem_cons_self h0n h0v
        · obtain ⟨c', hc', e⟩ := kidsValid_mem_name hks t0 h0
          have : (cs.filter (·.f == g)).length ≠ 0 :=
            List.length_pos_iff.mpr (List.ne_nil_of_mem (List.mem_filter.mpr ⟨hc', by simp [e, h0n]⟩)) |>.ne'
          exact absurd hz this
      · rw [heapPops_kid_of hS hs hn ((hcs c List.mem_cons_self).resolve_right hc) hv, List.nil_append]
        have h1' : (cs.filter (·.f == g)).length ≤ 1 := by simpa [List.filter_cons, hc] using h1
        rcases List.mem_cons.mp h0 with rfl | h0
        · exact absurd (hn.symm.trans h0n) hc
        · exact heapPopsKids_one hS hs hks hcs' h1' hH' h0 h0n h0v
  | [], [], _, _, _, _, h0, _, _ => by simp at h0
  | [], _ :: _, h, _, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _, _ => h.elim

end

end LeanVM.Guest.Memory
