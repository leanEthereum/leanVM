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

/-- A `KECCAK` holds by evaluation: its outputs are the permutation of its inputs. -/
theorem vtB_keccakAt (hl : args.length = 20) (n : ℕ) {ins outs : List V} {i o : Bool}
    (heq : tbStmtsEqb [.atom (.keccak ins outs i o)] ((vtAt n).take 1) = true) :
    VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.keccak ins outs i o)) := by
  have hg := vt_goodAt (rd := rd) (w := wo) hl n _ heq
  exact holds_of_good (S := vtSL) (show Good rd vtSL wo _ (.keccak ins outs i o) from hg) trivial

/-- **A stream read, complete.** -/
theorem vtc_fsNext (hl : args.length = 20) {cur : V} {off b pos : ℕ}
    (hcheck : tbStmtsEqb (fsNextT cur off b) ((vtPre.drop pos).take (fsNextT cur off b).length) =
      true) (hS : Atom.load (.n b) cur off ∉ vtSL) {x : E}
    (hx : LoadHolds rd (vtσ rd wo args cur) off x) :
    (∀ s ∈ fsNextT cur off b, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s) ∧
      vtσ rd wo args (.n b) = x ∧
      ∀ i < 2, vtσ rd wo args (.n (b + 1 + i)) = fsPackVals x dsObserve i := by
  have hmem : ∀ s ∈ fsNextT cur off b, s ∈ vtPre := fun s hs ↦ vt_mem_slice hcheck hs
  have r := vtB_readM hl (hmem _ (by simp [fsNextT])) hS hx
  have hG : ∀ s ∈ fsNextT cur off b, GoodS rd vtSL wo (vtσ rd wo args) (fixNe s) :=
    fun s hs ↦ vt_goodS hl (hmem s hs)
  have g0 := hG (.atom (.copy (.n (b + 1)) (.n b))) (by simp [fsNextT, fsPackT])
  have g1 := hG (.atom (.const (.n (b + 1 + 1)) (word 0 dsObserve))) (by simp [fsNextT, fsPackT])
  simp only [fixNe, GoodS, Good] at g0 g1
  have hv : ∀ i < 2, vtσ rd wo args (.n (b + 1 + i)) = fsPackVals x dsObserve i := by
    intro i hi
    interval_cases i
    · rw [show b + 1 + 0 = b + 1 by rfl, g0, r.1]; rfl
    · exact g1
  refine ⟨vtB_blockA hl pos _ hcheck fun s hs ha ↦ ?_, r.1, hv⟩
  simp only [fsNextT, fsPackT, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact r.2
  all_goals simp [autoB, pureB, hintB] at ha

end

end
end LeanVM.Guest.B1.Tables
