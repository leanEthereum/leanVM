/-
  LeanVM.Guest.EndExecExpW

  The exponent facts on words (`Res.expFacts` with an offset), sound at the honest instances of b2c's aligned tree:
  `check_stack_terminal`'s kappa source, carried from `verify_sub`'s certified heights.
-/

module

public import LeanVM.Guest.EndExecExpCA
public import LeanVM.Guest.CoreMode.Fn.column_selector.CsChain
public import LeanVM.Guest.CoreMode.Fn.check_stack_terminal.Data
public import LeanVM.Guest.CoreMode.Fn.hint_stream.HsCarry

/-!
`expOkA_cst`: at every honest instance of `check_stack_terminal`, the word at `kappa_base·g^7` (its parameter `1`) is
`g^e`, `e < 25`: its only caller `verify_sub` passes the kappa sources it certifies, the Keccak table's log height at
most `24` (`CsQ`, `vs_kappa`), and its `gmv`, `g_n`, `g_log_mem` (`CstQ`, `vs_cst`). `expFacts_okW`: every listed
exponent fact, a carried bound's (`expOkA_of_carry`), these, or `hint_stream`'s chunk count (`expOkA_hs`).
`dimFacts_okW`: every listed dimension fact, `check_stack_terminal`'s (`CstQ`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

public section

variable {al : String → Bool} {D : Ref → RefD}

/-- **`check_stack_terminal`'s kappa source at `kappa_base·g^7`**: `g^e`, `e < 25` (`CsQ`). -/
theorem expOkA_cst : ExpOkA al D (name% «check_stack_terminal», 1, some 7, 25) := by
  intro r hR hr J hJ σ bufs kids hJt fn hf v hv
  obtain ⟨-, -, h, -⟩ := (csQ_allA hR hr J hJ _ σ bufs kids hJt).2.2.1 rfl
  obtain rfl := Option.some.inj (hf.symm.trans find_cst)
  rw [cst_facts.1] at hv
  obtain rfl : v = .n 1 := by simpa using hv.symm
  exact h

/-- `check_stack_terminal`'s sizes at an honest instance (`CsQ`, `vs_cst`). -/
theorem cst_sizes {r : Ref} (hR : RefH (layB al) (D r) r) (hr : r.Ok) {J : Inst} (hJ : J ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (hJt : J.t = .node name% «check_stack_terminal» σ bufs kids) :
    CstQ r.img.read σ :=
  ((csQ_allA hR hr J hJ _ σ bufs kids hJt).2.2.1 rfl).2.2.2

/-- **`check_stack_terminal`'s `gmv`, `g_n`, `g_log_mem`**: `g^e`, `e < 31`, `e < 25`, `e < 31` (`CstQ`). -/
theorem expOkA_cstP {c : String × ℕ × Option ℕ × ℕ}
    (hc : c = (name% «check_stack_terminal», 4, none, 31) ∨ c = (name% «check_stack_terminal», 6, none, 25) ∨
      c = (name% «check_stack_terminal», 8, none, 31)) : ExpOkA al D c := by
  intro r hR hr J hJ σ bufs kids hJt fn hf v hv
  have hcn : c.1 = name% «check_stack_terminal» := by rcases hc with rfl | rfl | rfl <;> rfl
  rw [hcn] at hJt hf
  obtain ⟨⟨s, hs, gs⟩, ⟨l, hl, gl⟩, n, hn, gn, -⟩ := cst_sizes hR hr hJ hJt
  obtain rfl := Option.some.inj (hf.symm.trans find_cst)
  rw [cst_facts.1] at hv
  rcases hc with rfl | rfl | rfl
  · obtain rfl : v = .n 4 := by simpa using hv.symm
    exact ⟨s, by show s < 31; omega, gs⟩
  · obtain rfl : v = .n 6 := by simpa using hv.symm
    exact ⟨n, by show n < 25; omega, gn⟩
  · obtain rfl : v = .n 8 := by simpa using hv.symm
    exact ⟨l, by show l < 31; omega, gl⟩

/-- **Every listed exponent fact holds**, aligned: a carried bound's (`expOkA_of_carry`), or `check_stack_terminal`'s
kappa source (`expOkA_cst`), or `hint_stream`'s chunk count (`expOkA_hs`). -/
theorem expFacts_okW : ∀ c ∈ CoreMode.FnReg.expFacts, ExpOkA al D c := by
  have h : ∀ c ∈ CoreMode.FnReg.expFacts,
      c ∈ CoreMode.FnReg.expCarry.map (fun c ↦ (c.1, c.2.1, (none : Option ℕ), c.2.2.2)) ∨
        c ∈ CoreMode.Own.check_stack_terminal.expFacts ∨ c ∈ CoreMode.Own.hint_stream.expFacts := by decide +kernel
  intro c hc
  rcases h c hc with h | h | h
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp h
    exact expOkA_of_carry hc'
  · simp only [CoreMode.Own.check_stack_terminal.expFacts, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | h
    · exact expOkA_cst
    · exact expOkA_cstP h
  · simp only [CoreMode.Own.hint_stream.expFacts, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact expOkA_hs

/-- **Every listed dimension fact holds**, aligned: `check_stack_terminal`'s, by `verify_sub`'s certified sizes
(`CstQ`, `vs_cst`). -/
theorem dimFacts_okW : ∀ c ∈ CoreMode.FnReg.dimFacts, DimOkA al D c := by
  have h : ∀ c ∈ CoreMode.FnReg.dimFacts, c ∈ CoreMode.Own.check_stack_terminal.dimFacts := by decide +kernel
  have hs : (CoreMode.Own.check_stack_terminal.dimFacts.getD 1 default).2.2.2 =
      CoreMode.Own.check_stack_terminal.sentBlocks.map fun b ↦ (b, 0) := by decide +kernel
  intro c hc r hR hr J hJ σ bufs kids hJt fn hf vk vb hk hb
  have hc' := h c hc
  have hcn : c.1 = name% «check_stack_terminal» := by
    simp only [CoreMode.Own.check_stack_terminal.dimFacts, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl <;> rfl
  rw [hcn] at hJt hf
  obtain ⟨-, -, n, hn, gn, hkb, hkp⟩ := cst_sizes hR hr hJ hJt
  obtain rfl := Option.some.inj (hf.symm.trans find_cst)
  simp only [CoreMode.Own.check_stack_terminal.dimFacts, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rw [cst_facts.1] at hk hb
  rcases hc' with rfl | rfl
  · obtain rfl : vk = .n 1 := by simpa using hk.symm
    obtain rfl : vb = .n 6 := by simpa using hb.symm
    refine ⟨n, by omega, gn, fun p hp ↦ ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have key : ∀ t < 6, p = (2 + t, 0) → ∃ e, LoadHolds r.img.read (σ (.n 1)) p.1 (gen ^ e) ∧ e + p.2 ≤ n := by
      intro t ht hpt
      obtain ⟨e, he, hl⟩ := hkb t ht
      subst hpt
      exact ⟨e, hl, by simpa using he⟩
    rcases hp with h | h | h | h | h | h
    · exact key 0 (by decide) h
    · exact key 1 (by decide) h
    · exact key 2 (by decide) h
    · exact key 3 (by decide) h
    · exact key 4 (by decide) h
    · exact key 5 (by decide) h
  · obtain rfl : vk = .n 3 := by simpa using hk.symm
    obtain rfl : vb = .n 6 := by simpa using hb.symm
    refine ⟨n, by omega, gn, fun p hp ↦ ?_⟩
    have hp' : p ∈ CoreMode.Own.check_stack_terminal.sentBlocks.map fun b ↦ (b, 0) := by
      rw [← hs]; exact hp
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hp'
    obtain ⟨e, he, hl⟩ := hkp b hbm
    exact ⟨e, hl, by simpa using he⟩

end

end LeanVM.Guest.EndExec
