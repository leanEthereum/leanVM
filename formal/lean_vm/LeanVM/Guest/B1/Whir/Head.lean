/-
  LeanVM.Guest.B1.Whir.Head

  The head of `open_stacked`: the first round polynomial read, the root stored.
-/

module

public import LeanVM.Guest.B1.Whir.Level
public import LeanVM.Guest.B1.Bits.QueryWindows

/-!
# The head (G:1443-1484)

From the parameters (the capacity, the claim, the root's two halves, the cursor), the head reads
the first round polynomial's two words at the cursor (`sumcheckRoundPoly 3 target`), stores the
root in `level_roots`, writes the window table `win_tabs[g^n] = n` (`osWinTabs_sound`, what
`decode_query_windows` reads) and starts the first level (`osHead_sound`, `LvIn` at level `0`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- **The window table**: `win_tabs[g^n] = n`, `n < 128`. -/
theorem osWinTabs_sound {C : CallRel} (hok : AllOk C rd σ osWinTabs) : WinTabs rd (σ (.n osWin)) := by
  intro n hn
  simp only [osWinTabs, allOk_flatten, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hok
  obtain ⟨hc, hl⟩ := hok n hn
  rw [hc, word_eOfNat] at hl
  exact hl

/-- **The head**: the two words read at the cursor run the first round polynomial; the first
level starts from the guest's state. -/
theorem osHead_sound {c : OsCfg} {fs : List E} {target root0 root1 cur : E} {root : Digest}
    {shape : ℕ × ℕ} (hfs : fs.length = 5)
    (hp : (osParams 9).map σ = fs ++ [target, root0, root1, cur])
    (hroot : (root0, root1) = digestHalves root)
    (hshape : shape = ((c.levels.headD default).depth, lvWidth 0 (c.levels.headD default)))
    (hoff : (c.levels.headD default).foldsOff = 0)
    (hok : AllOk (coreProgram.Rel rd) rd σ (osHead c).1) :
    ∃ c0 c2 : E, ReadsAt rd cur [c0, c2] ∧
      RunsTo (sumcheckRoundPoly 3 target none) ⟨fs, []⟩ [c0, c2] [c0, target + c2, c2]
        ((osHead c).2.F σ) ∧
      LvIn rd σ 0 (c.levels.headD default) (osHead c).2 ⟨target, [c0, target + c2, c2], [], []⟩
        [(root, shape)] root ∧
      (osHead c).2.cur σ = cur * gen ^ 2 ∧ WinTabs rd (σ (.n osWin)) := by
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ : ∃ f0 f1 f2 f3 f4, fs = [f0, f1, f2, f3, f4] := by
    match fs, hfs with
    | [f0, f1, f2, f3, f4], _ => exact ⟨f0, f1, f2, f3, f4, rfl⟩
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := hp
  have hwin : AllOk (coreProgram.Rel rd) rd σ osWinTabs := fun s hs ↦ hok s (by
    simp only [osHead, List.mem_append]; tauto)
  simp only [osHead, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds,
    osHeap, and_assoc] at hok
  obtain ⟨l9, l10, a11, -, -, -, -, s6, s7, -⟩ := hok
  have hF : (OsSt.F σ (osHead c).2) = ⟨[f0, f1, f2, f3, f4], [(σ (.n 9), dsObserve),
      (σ (.n 10), dsObserve)]⟩ := by
    simp [OsSt.F, OsSt.fsv, osHead, e0, e1, e2, e3, e4]
  refine ⟨σ (.n 9), σ (.n 10), ?_, ?_, ?_, ?_, osWinTabs_sound hwin⟩
  · intro i hi
    rw [← e8]
    rcases i with _ | _ | i
    · exact l9
    · exact l10
    · simp at hi
  · rw [hF]
    have := runsTo_round3 ⟨[f0, f1, f2, f3, f4], []⟩ target (σ (.n 9)) (σ (.n 10))
    refine RunsTo.of_eq this rfl rfl rfl ?_
    simp [Fs.absorbAll, Fs.absorb, rateScalars]
  · refine ⟨rfl, by simp [osHead], trivial, ?_, by simp [osHead, e5], by rw [hoff]; rfl,
      fun j hj ↦ by simp at hj, rfl, by simp [hshape, lvWidth], ?_, ?_, ?_⟩
    · simp [OsSt.quad, osHead, a11, e5]
    · rw [← hroot]; simpa [e6] using s6
    · rw [← hroot]; simpa [e7] using s7
    · exact matsOk_nil σ
  · simp [OsSt.cur, osHead, e8]

end
end LeanVM.Guest.B1.Whir
