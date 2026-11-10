/-
  LeanVM.Guest.B1.Tables.VtC.BGlue

  Tools for the bus sides' statements between the selectors: a constant's word, a stream read
  (`fs_next`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BBase
public import LeanVM.Guest.B1.Fs.Templates

/-!
# Between the selectors

`vtB_const`: a constant's word. `vtc_fsNext`: a
stream read `fsNextT` of a word the memory holds holds, its word the memory's and its cells
`fsPackVals`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

/-- A constant's word. -/
theorem vtB_const (hl : args.length = 20) {d : V} {c : E} (hm : Stmt.atom (.const d c) ∈ vtPre) :
    vtσ rd wo args d = c :=
  vt_goodS (rd := rd) (w := wo) hl hm

/-- **A stream read, complete.** -/
theorem vtc_fsNext (hl : args.length = 20) {cur : V} {off b pos : ℕ}
    (hcheck : tbStmtsEqb (fsNextT cur off b) ((vtPre.drop pos).take (fsNextT cur off b).length) =
      true) (hS : Atom.load (.n b) cur off ∉ vtSL) {x : E}
    (hx : LoadHolds rd (vtσ rd wo args cur) off x) :
    (∀ s ∈ fsNextT cur off b, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      vtσ rd wo args (.n b) = x ∧
      ∀ i < 9, vtσ rd wo args (.n (b + 1 + i)) = fsPackVals x dsObserve i := by
  have hmem : ∀ s ∈ fsNextT cur off b, s ∈ vtPre := fun s hs ↦ vt_mem_slice hcheck hs
  have r := vtB_readM hl (hmem _ (by simp [fsNextT])) hS hx
  have hG : ∀ s ∈ fsNextT cur off b, GoodS rd vtSL wo (vtσ rd wo args) (fixNe s) :=
    fun s hs ↦ vt_goodS hl (hmem s hs)
  have gl := hG (.atom (.hint (.limbs (.n b) [.n (b + 1), .n (b + 1 + 1), .n (b + 1 + 2)])))
    (by simp [fsNextT, fsPackT])
  have g3 := hG (.atom (.const (.n (b + 1 + 3)) (word dsObserve 0))) (by simp [fsNextT, fsPackT])
  have g4 := hG (.atom (.const (.n (b + 1 + 4)) (word 0 0 1))) (by simp [fsNextT, fsPackT])
  have g5 := hG (.atom (.mul (.n (b + 1 + 5)) (.n (b + 1 + 4)) (.n (b + 1 + 2))))
    (by simp [fsNextT, fsPackT])
  have g6 := hG (.atom (.add (.n (b + 1 + 6)) (.n b) (.n (b + 1 + 5)))) (by simp [fsNextT, fsPackT])
  have g7 := hG (.atom (.const (.n (b + 1 + 7)) (word 0 dsObserve 0))) (by simp [fsNextT, fsPackT])
  have g8 := hG (.atom (.add (.n (b + 1 + 8)) (.n (b + 1 + 2)) (.n (b + 1 + 7))))
    (by simp [fsNextT, fsPackT])
  simp only [fixNe, GoodS, Good] at gl g3 g4 g5 g6 g7 g8
  rw [ite_pos' (by simp)] at g5
  have l : ∀ j < 3, vtσ rd wo args (.n (b + 1 + j)) = fsPackVals x dsObserve j := by
    intro j hj
    have := gl j (by simpa using hj)
    interval_cases j <;> simpa [limbAt, r.1, fsPackVals] using this
  have hv : ∀ i < 9, vtσ rd wo args (.n (b + 1 + i)) = fsPackVals x dsObserve i := by
    intro i hi
    interval_cases i
    · exact l 0 (by norm_num)
    · exact l 1 (by norm_num)
    · exact l 2 (by norm_num)
    · exact g3
    · exact g4
    · rw [g5, g4, l 2 (by norm_num)]; rfl
    · rw [g6, r.1, g5, g4, l 2 (by norm_num)]; rfl
    · exact g7
    · rw [g8, l 2 (by norm_num), g7]; rfl
  refine ⟨vtB_blockA hl pos _ hcheck fun s hs ha ↦ ?_, r.1, hv⟩
  simp only [fsNextT, fsPackT, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r.2
  · simp [autoB, pureB, hintB] at ha
  · simp [autoB, pureB, hintB] at ha
  · show IsInK _ ∧ IsInK _
    rw [hv 2 (by norm_num), hv 3 (by norm_num)]
    refine ⟨ofK_isInK _, ?_⟩
    show IsInK (word dsObserve 0); rw [word_eOfNat]; exact eOfNat_isInK _
  all_goals simp [autoB, pureB, hintB] at ha

end

end
end LeanVM.Guest.B1.Tables
