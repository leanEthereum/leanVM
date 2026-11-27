/-
  LeanVM.Guest.CoreMode.Fam.CallersWit

  The callers' checks (`Res.callersG`, `Res.callersM`, `Res.callersB`) with their lists of names read through tables
  by the names' codes, built by the kernel once a check.
-/

module

public import LeanVM.Guest.CoreMode.Fam.LinkDefs
public import LeanVM.Guest.CoreMode.Fam.Wit

/-!
# The callers' checks, by tables

`callersG R fn` compares each call site's callee with every callee of `R`, as a string, and `fn`'s name with each
caller. `callersGW R fn` reads the callers' codes under the callee's code in `R`'s table (`NTab.ofNamed`, which the
kernel builds once) and compares codes as numbers; `callersG_of_wit` gives the check (`encS` is injective). Likewise
`callersMW` (`callersM`, a list of callers per callee) and `callersBW` (`callersB`, a link's callees).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (natSeq natSeq_eq)

@[expose] public section

/-- **`callersG`, by its table**: the code of a caller of the callee is `fn`'s, or `fn` is the callee, a loop. -/
noncomputable def callersGW (R : List (String × String)) (fn : Fn) : Bool :=
  natSeq (encS fn.name) fun k ↦ sitesB (fun f _ _ ↦ ((NTab.ofNamed encS R).at (encS f)).all fun c ↦
    Nat.beq c k || (fn.name == f && fn.loop)) fn.body

/-- **`callersM`, by its table**: `fn`'s code among the callee's callers' codes, or `fn` the callee, a loop. -/
noncomputable def callersMW (R : List (String × List String)) (fn : Fn) : Bool :=
  natSeq (encS fn.name) fun k ↦ sitesB (fun f _ _ ↦
    ((NTab.ofNamed (fun cs : List String ↦ cs.map encS) R).at (encS f)).all fun cs ↦
      cs.contains k || (fn.name == f && fn.loop)) fn.body

/-- **`callersB`, by its table**: a callee of the link is called by the caller, or by itself, a loop. -/
noncomputable def callersBW (L : Link) (fn : Fn) : Bool :=
  natSeq (encS fn.name) fun k ↦ sitesB (fun f _ _ ↦ ((NTab.ofNamed (fun _ ↦ ()) L.fams).at (encS f)).isEmpty ||
    Nat.beq k (encS L.oName) || (fn.name == f && fn.loop)) fn.body

end

public section

theorem callersG_of_wit {R : List (String × String)} {fn : Fn} (h : callersGW R fn = true) :
    callersG R fn = true := by
  unfold callersGW at h
  rw [natSeq_eq] at h
  unfold callersG
  refine sitesB_imp (fun f args rets hq ↦ ?_) fn.body h
  have := tab_all (ofNamed_all encS R) (φ := encS) (P := fun c ↦ fn.name == c || (fn.name == f && fn.loop))
    (fun c hc ↦ ?_) hq
  · simpa only [Bool.or_assoc] using this
  simp only [Bool.or_eq_true] at hc ⊢
  refine hc.imp (fun h ↦ ?_) id
  rw [encS_inj (Nat.eq_of_beq_eq_true h)]
  exact beq_self_eq_true _

theorem callersM_of_wit {R : List (String × List String)} {fn : Fn} (h : callersMW R fn = true) :
    callersM R fn = true := by
  unfold callersMW at h
  rw [natSeq_eq] at h
  unfold callersM
  refine sitesB_imp (fun f args rets hq ↦ ?_) fn.body h
  have := tab_all (ofNamed_all (fun cs : List String ↦ cs.map encS) R) (φ := fun cs : List String ↦ cs.map encS)
    (P := fun cs : List String ↦ cs.contains fn.name || (fn.name == f && fn.loop)) (fun cs hc ↦ ?_) hq
  · simpa only [Bool.or_assoc] using this
  simp only [Bool.or_eq_true] at hc ⊢
  refine hc.imp (fun h ↦ ?_) id
  obtain ⟨s, hs, he⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
  rw [List.contains_iff_mem, ← encS_inj he]
  exact hs

theorem callersB_of_wit {L : Link} {fn : Fn} (h : callersBW L fn = true) : callersB L fn = true := by
  unfold callersBW at h
  rw [natSeq_eq] at h
  unfold callersB
  refine sitesB_imp (fun f args rets hq ↦ ?_) fn.body h
  simp only [Bool.or_eq_true] at hq ⊢
  rcases hq with (he | hk) | hl
  · refine .inl (.inl ?_)
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro ha
    obtain ⟨c, hc, hcf⟩ := List.any_eq_true.mp ha
    have hm := List.all_eq_true.mp (ofNamed_all (fun _ ↦ ()) L.fams) c hc
    rw [beq_iff_eq.mp hcf, List.contains_iff_mem] at hm
    rw [List.isEmpty_iff] at he
    rw [he] at hm
    exact List.not_mem_nil hm
  · exact .inl (.inr (by rw [encS_inj (Nat.eq_of_beq_eq_true hk)]; exact beq_self_eq_true _))
  · exact .inr hl

end

end LeanVM.Guest.Res
