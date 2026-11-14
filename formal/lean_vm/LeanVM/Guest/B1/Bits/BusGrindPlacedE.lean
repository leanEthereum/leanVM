/-
  LeanVM.Guest.B1.Bits.BusGrindPlacedE

  `bus_grind_check__L{d}`, placed and bounded, by a tree of honest shape exact at every node.
-/

module

public import LeanVM.Guest.B1.Bits.BusGrindPlaced
public import LeanVM.Guest.B1.Tables.FlatAtTE

/-!
# `bus_grind_check`, placed and exact

`bus_grind_check_completeDTBRE`: `bus_grind_check_completeB_of`'s statement within its frame and any bound `Bg` of
its `grind_check`'s trees, by a tree of honest shape (`busGrindHonest`) whose every node is exact on the memory: its
callee by `grind_check_completeDTBR_of` (`completeAt_flatDTBRR`), its own body without a computed hint
(`bgBody_pinned`), so `CompleteAtDTBR.nodeEvery`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem bgBody_pinned (d : ℕ) : Stmt.blockNextOk isComputed pinsInverse (bgBody d) = true := by
  simp [bgBody, Stmt.blockNextOk, Stmt.headOk, isComputed]

/-- `bus_grind_check__L{d}`'s statements before its return. -/
def bgPre (d : ℕ) : List Stmt :=
  [.call (grindCheckName (busGrindBits d)) [.n 0, .n 1] [], .atom (.const (.n 2) (word 0 0))]

/-- **`bus_grind_check__L{d}`'s honest shape** on the memory `rd`: its callee exact at every node. -/
def busGrindHonest (d : ℕ) (rd : Reader) : Tree → Prop :=
  Budget.NodeHonest coreProgram (busGrindName d) (fun _ => True) (flatCalls (bgPre d)) (fun _ => [])
    [fun t => t.Every (ExactAt coreProgram rd)]

/-- **`bus_grind_check__L{d}`, placed, within its frame and a bound `Bg` of its callee's trees, exact at every
node.** -/
theorem bus_grind_check_completeDTBRE {d : ℕ} (hd : d ∈ busGrindDeployed) {κ : ℕ} (hκ : 11 ≤ κ) {Bg : ℕ}
    (hT : TotalLe coreProgram fs (grindCheckName (busGrindBits d)) fun _ => Bg) {args rets : List E}
    {Lin : Layout} (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → busGrindPre d rd args rets) :
    CompleteAtDTBR fs cert κ (busGrindName d) Lin args (Returns rets)
      (fun rd t => busGrindHonest d rd t ∧ t.Every (ExactAt coreProgram rd)) (fs (busGrindName d) + Bg) := by
  obtain ⟨fn, hf, hpar, hbody⟩ := bus_grind_check_found d hd
  have hl : coreProgram.loop (busGrindName d) = false := by
    rw [Program.loop_of_find? hf, Fn.loop, hbody]
    rfl
  by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd Lin
  swap
  · intro fp
    exact ⟨0, [], rets, [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd0, h0, hL0⟩ := hex
  obtain ⟨rfl, w, tabs, rfl, -, -⟩ := hpre rd0 h0 hL0
  have hgp : ∀ rd, LowDef κ rd → MemL rd Lin → grindPre (busGrindBits d) rd [w, tabs] [] :=
    fun rd hl hL => by
      obtain ⟨-, w', tabs', he, ht, hpow⟩ := hpre rd hl hL
      simp only [List.cons.injEq, and_true] at he
      exact ⟨rfl, w', tabs', by rw [he.1, he.2], ht, hpow⟩
  let kid : Kid := ⟨grindCheckName (busGrindBits d), true, [w, tabs], Lin, Returns []⟩
  have h := completeAt_flatDTBRR (fs := fs) (cert := cert) hf hl κ Lin [w, tabs] [0]
    (pre := bgPre d) (vs := [.n 2]) (by rw [hbody]; rfl) rfl rfl [] (fun _ => [])
    (fun _ => List.Forall₂.nil) (fun _ => [kid]) (fun _ _ => True)
    (fun rd => [fun t => t.Every (ExactAt coreProgram rd)]) [Bg] Bg
    (fun _ => ⟨fun _ => (grind_check_completeDTBR_of (busGrindBits_mem d hd) hκ hT hgp).mono le_rfl
      fun _ _ h => h.2, trivial⟩)
    (fun _ => by simp [kidsBoundL, kid]) (fun _ _ => le_rfl)
    (fun _ k hk _ i hi => by
      rw [List.mem_singleton] at hk
      subst hk
      exact Or.inl hi)
    (fun _ rd _ hL k hk => by
      rw [List.mem_singleton] at hk
      subst hk
      exact hL)
    (fun fp outs ho rd hl hB hL => ?_)
  · refine (CompleteAtDTBR.nodeEvery hf (by rw [hbody]; exact bgBody_pinned d) h ?_).mono (by simp) fun _ _ h => h
    intro rd σ _ c T hc _ t _ _ hTt
    obtain ⟨-, hT'⟩ := List.of_mem_zip hc
    rw [List.mem_singleton] at hT'
    subst hT'
    exact hTt
  obtain ⟨o, rfl⟩ : ∃ o, outs = [o] := by
    rcases outs with _ | ⟨o, _ | ⟨o', os⟩⟩
    · exact (ho : False).elim
    · exact ⟨o, rfl⟩
    · exact (ho.2 : False).elim
  obtain ⟨ho1, -⟩ := ho.1 rfl
  refine ⟨fun v => [w, tabs, 0].getD v.idx 0, by rw [hpar]; rfl, ?_, ?_, rfl, rfl, ?_, ?_, trivial⟩
  · intro s hs
    simp only [bgPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> trivial
  · rw [hbody]
    simp only [bgBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    refine ⟨?_, ?_, rfl⟩
    · obtain ⟨t, hn, hv, -⟩ := (grind_relAtIn (fs := fs) (cert := cert)
        (busGrindBits_mem d hd) hκ hgp 0 hl hL).relAt
      exact hn ▸ hv.rel t
    · show (0 : E) = word 0 0
      rw [word_zero]
  · refine ⟨rfl, rfl, fun _ => ⟨rfl, ?_⟩, trivial⟩
    rw [ho1]
    rfl
  · intro q hq
    simp [bgPre, loadsEv, Stmt.loadS] at hq

end
end LeanVM.Guest.B1
