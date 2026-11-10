/-
  LeanVM.Guest.B1.Bits.BusGrindPlaced

  `bus_grind_check__L{d}`, placed and bounded: its frame and its `grind_check`'s bound.
-/

module

public import LeanVM.Guest.B1.Bits.BusGrind
public import LeanVM.Guest.B1.Bits.GrindPlaced
public import LeanVM.Guest.B1.Tables.FlatAtT

/-!
# `bus_grind_check`, placed

`busGrindPre d`: what a call asks, `grindPre` at `busGrindBits d` but `0` returned. The body is
flat (`bgBody`): one callee, `grind_check__L{busGrindBits d}` on the caller's words, entered
within any bound its `CompleteRelB` gives (`completeAt_flatDTB`); its relation, which the body's
holding needs, from `grind_relAtIn`.

`bus_grind_check_completeB_of` (the frame and a bound of the callee), `bus_grind_check_completeB`
(the frame and the callee's frame), `bus_grind_check_completeD`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- What `bus_grind_check__L{d}`'s completeness asks of its call: `0` returned, the window tables
at its second argument, and its first argument's low limb passing the proof of work. -/
def busGrindPre (d : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  rets = [0] ∧ ∃ w tabs, args = [w, tabs] ∧ WinTabs rd tabs ∧
    (w.limb 0).lane.toNat % 2 ^ busGrindBits d = 0

/-- **`bus_grind_check__L{d}`, placed, within its frame and a bound `Bg` of its callee.** -/
theorem bus_grind_check_completeB_of {d : ℕ} (hd : d ∈ busGrindDeployed) {κ : ℕ} (hκ : 11 ≤ κ)
    {Bg : ℕ}
    (hg : CompleteRelB fs cert κ (grindCheckName (busGrindBits d)) (grindPre (busGrindBits d)) Bg) :
    CompleteRelB fs cert κ (busGrindName d) (busGrindPre d) (fs (busGrindName d) + Bg) := by
  intro args rets Lin hpre
  obtain ⟨fn, hf, hpar, hbody⟩ := bus_grind_check_found d hd
  have hl : coreProgram.loop (busGrindName d) = false := by
    rw [Program.loop_of_find? hf, Fn.loop, hbody]
    rfl
  -- the arguments, fixed by the call
  by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd Lin
  swap
  · intro fp
    exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd0, h0, hL0⟩ := hex
  obtain ⟨rfl, w, tabs, rfl, -, -⟩ := hpre rd0 h0 hL0
  have hgp : ∀ rd, LowDef κ rd → MemL rd Lin → grindPre (busGrindBits d) rd [w, tabs] [] :=
    fun rd hl hL => by
      obtain ⟨-, w', tabs', he, ht, hpow⟩ := hpre rd hl hL
      simp only [List.cons.injEq, and_true] at he
      exact ⟨rfl, w', tabs', by rw [he.1, he.2], ht, hpow⟩
  let kid : Kid := ⟨grindCheckName (busGrindBits d), true, [w, tabs], Lin, Returns []⟩
  have h := completeAt_flatDTB (fs := fs) (cert := cert) hf hl κ Lin [w, tabs] [0]
    (pre := [.call (grindCheckName (busGrindBits d)) [.n 0, .n 1] [],
      .atom (.const (.n 2) (word 0 0))]) (vs := [.n 2]) (by rw [hbody]; rfl) rfl rfl [] (fun _ => [])
    (fun _ => List.Forall₂.nil) (fun _ => [kid]) (fun _ => True) [fun _ => True] [Bg] Bg
    (fun _ => ⟨fun _ => (hg [w, tabs] [] Lin hgp).toDTB, trivial⟩)
    (fun _ => by simp [kidsBoundL, kid]) (fun _ => le_rfl)
    (fun _ k hk _ i hi => by
      rw [List.mem_singleton] at hk
      subst hk
      exact Or.inl hi)
    (fun _ rd _ hL k hk => by
      rw [List.mem_singleton] at hk
      subst hk
      exact hL)
    (fun fp outs ho rd hl hB hL => ?_)
  · exact h.toCompleteAtB
  obtain ⟨o, rfl⟩ : ∃ o, outs = [o] := by
    rcases outs with _ | ⟨o, _ | ⟨o', os⟩⟩
    · exact (ho : False).elim
    · exact ⟨o, rfl⟩
    · exact (ho.2 : False).elim
  obtain ⟨ho1, -⟩ := ho.1 rfl
  refine ⟨fun v => [w, tabs, 0].getD v.idx 0, by rw [hpar]; rfl, ?_, ?_, rfl, rfl, ?_, ?_, trivial⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
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
    simp [loadsEv, Stmt.loadS] at hq

/-- **`bus_grind_check__L{d}`, placed, within its frame and its callee's.** -/
theorem bus_grind_check_completeB {d : ℕ} (hd : d ∈ busGrindDeployed) {κ : ℕ} (hκ : 11 ≤ κ) :
    CompleteRelB fs cert κ (busGrindName d) (busGrindPre d)
      (fs (busGrindName d) + fs (grindCheckName (busGrindBits d))) :=
  bus_grind_check_completeB_of hd hκ (grind_check_completeB (busGrindBits_mem d hd) hκ)

/-- **`bus_grind_check__L{d}`, placed.** -/
theorem bus_grind_check_completeD {d : ℕ} (hd : d ∈ busGrindDeployed) {κ : ℕ} (hκ : 11 ≤ κ) :
    CompleteRelD fs cert κ (busGrindName d) (busGrindPre d) :=
  (bus_grind_check_completeB hd hκ).toCompleteRelD

end
end LeanVM.Guest.B1
