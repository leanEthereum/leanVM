/-
  LeanVM.Guest.B2C.CplExec

  The executor's completeness, counted, along a path whose branches fall through but at most
  the one it leaves by: the exit it leaves by is the one the path names.
-/

module

public import LeanVM.Guest.B2C.Count

/-!
# Segments along a path

`Exec.exec_complete` and `B2C.exec_completeC` reach the registers a path's exit names but say
only that some exit of the segment holds its environment there. B2's completeness walk knows
which branch the path takes: `Fall` says every item of a path holds with every branch falling
through, `Taken` that a branch is taken. Then a segment's run reaches its exit's registers, or a
branch's, with that exit's environment holding (`segZ_fall`, `segZ_taken`), each opcode counted
at most as often as the path's items run it.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

section Defs

variable {κ : ℕ} (L : MemImage κ) (fp : K)

/-- **Every item of a path holds**, every branch falling through. -/
def Fall : List Item → Prop
  | [] => True
  | .ins a :: its => a.Holds L fp ∧ Fall its
  | .fact _ :: its => Fall its
  | .branch oc od of _ :: its =>
      (Atom.jump oc od of).Holds L fp ∧ L.read (fp * gpow oc) = some 0 ∧ Fall its

/-- **A branch is taken**: its cells hold words of `K`, its condition is not `0`. -/
def Taken (oc od of : ℕ) : Prop :=
  (Atom.jump oc od of).Holds L fp ∧ ∃ v, L.read (fp * gpow oc) = some v ∧ v ≠ 0

/-- A counted run from `s` to `r` within the instructions of `its`, the exit `x`'s environment
holding. -/
def ToC (prog : Program) (s r : Regs K) (its : List Item) (x : Exit) : Prop :=
  ∃ c, RunC prog L s r c ∧ (∀ op, c op ≤ itemOps its op) ∧ EnvHolds L fp x.env

end Defs

section

variable {κ : ℕ} {L : MemImage κ} {fp : K}

theorem fall_append : ∀ (l₁ l₂ : List Item), Fall L fp (l₁ ++ l₂) ↔ Fall L fp l₁ ∧ Fall L fp l₂
  | [], _ => by simp [Fall]
  | .ins a :: l₁, l₂ => by simp only [List.cons_append, Fall, fall_append l₁ l₂, and_assoc]
  | .fact _ :: l₁, l₂ => by simp only [List.cons_append, Fall, fall_append l₁ l₂]
  | .branch .. :: l₁, l₂ => by simp only [List.cons_append, Fall, fall_append l₁ l₂, and_assoc]

theorem fall_facts (fs : List Atom) : Fall L fp (fs.map .fact) := by
  induction fs with
  | nil => trivial
  | cons a fs ih => exact ih

theorem branch_not_facts {fs : List Atom} {pre post : List Item} {oc od of : ℕ} {x : Exit} :
    fs.map .fact ≠ pre ++ .branch oc od of x :: post := by
  intro h
  have : Item.branch oc od of x ∈ fs.map .fact := by rw [h]; simp
  simp at this

end

section Pass

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {entry len : ℕ}

theorem reachC_trans {s t u : Regs K} {l₁ l₂ : List Item} (h₁ : ReachC L prog s t l₁)
    (h₂ : ReachC L prog t u l₂) : ReachC L prog s u (l₁ ++ l₂) := by
  obtain ⟨c₁, hc₁, hle₁⟩ := h₁
  obtain ⟨c₂, hc₂, hle₂⟩ := h₂
  refine ⟨c₁ + c₂, hc₁.trans hc₂, fun op ↦ ?_⟩
  rw [Pi.add_apply, itemOps_append]
  exact Nat.add_le_add (hle₁ op) (hle₂ op)

theorem toC_after {s t r : Regs K} {l₁ l₂ : List Item} {x : Exit} (h₁ : ReachC L prog s t l₁)
    (h : ToC L fp prog t r l₂ x) : ToC L fp prog s r (l₁ ++ l₂) x := by
  obtain ⟨c₁, hc₁, hle₁⟩ := h₁
  obtain ⟨c, hc, hle, he⟩ := h
  refine ⟨c₁ + c, hc₁.trans hc, fun op ↦ ?_, he⟩
  rw [Pi.add_apply, itemOps_append]
  exact Nat.add_le_add (hle₁ op) (hle op)

/-- What an instruction's result gives along a path. -/
def ResZ (L : MemImage κ) (fp : K) (prog : Program) (entry i : ℕ) : Res → Prop
  | .go its st =>
    (Fall L fp its → St.Holds L fp st ∧
      ReachC L prog ⟨gpow (entry + i), fp⟩ ⟨gpow (entry + i + 1), fp⟩ its) ∧
    ∀ pre oc od of x post, its = pre ++ .branch oc od of x :: post → Fall L fp pre →
      Taken L fp oc od of → ∀ r, x.kind.Regs L fp entry r →
        ToC L fp prog ⟨gpow (entry + i), fp⟩ r (pre ++ [.branch oc od of x]) x
  | .stop its x => Fall L fp its → ∀ r, x.kind.Regs L fp entry r →
      ToC L fp prog ⟨gpow (entry + i), fp⟩ r its x

/-- **One instruction along a path.** -/
theorem stepI_z (hctx : Ctx F κ fp) {i : ℕ} {st : St} {ins : OInstr}
    (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) (hst : St.Holds L fp st) :
    ResZ L fp prog entry i (stepI F entry len i st ins) := by
  cases hj : ins.isJump with
  | false =>
    rw [stepI_of_nonJump hj]
    refine ⟨fun ⟨hh, _⟩ ↦ ?_, fun pre oc od of x post he ↦ ?_⟩
    · obtain ⟨-, he, hm⟩ := nonJump_holds hctx.le hctx.pows hst hh
      refine ⟨hst.push he hm hh, _, runC_fallThrough hf hpc hj hh, fun op ↦ ?_⟩
      rw [itemOps_cons]
      exact Nat.le_add_right _ _
    · exfalso
      cases pre with
      | nil => simp at he
      | cons a pre =>
        simp only [List.cons_append, List.cons.injEq] at he
        exact branch_not_facts he.2
  | true =>
    cases ins with
    | jump oc od of =>
      have hone : ∀ (a : Item), (∀ op, itemOp a op = if op = .jump then 1 else 0) →
          ∀ op, (if op = Opcode.jump then 1 else 0) ≤ itemOps [a] op := by
        intro a ha op
        rw [itemOps_cons, itemOps_nil, ha]
        exact Nat.le_add_right _ _
      have hgo : ∀ {c d f : E} {r : Regs K}, L.read (fp * gpow oc) = some c →
          L.read (fp * gpow od) = some d → L.read (fp * gpow of) = some f → IsInK c → IsInK d →
          IsInK f → c ≠ 0 → (jumpExit F entry len i st od of).kind.Regs L fp entry r →
          RunC prog L ⟨gpow (entry + i), fp⟩ r (fun op ↦ if op = .jump then 1 else 0) ∧
            EnvHolds L fp (jumpExit F entry len i st od of).env := by
        intro c d f r hc hd hf' hcK hdK hfK hc0 hr
        obtain ⟨hreg, -⟩ := jumpKind_holds (entry := entry) (len := len) (i := i) hctx.fpOne hst
          hd hdK hf' hfK
        rw [jumpExit_eq] at hr ⊢
        obtain rfl := Kind.regs_unique hr hreg
        exact ⟨runC_jump hf hpc ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, by rw [ite_eq_right hc0]⟩,
          hst.1⟩
      have hnext : ∀ {d f : E}, L.read (fp * gpow oc) = some 0 → L.read (fp * gpow od) = some d →
          L.read (fp * gpow of) = some f → IsInK d → IsInK f →
          RunC prog L ⟨gpow (entry + i), fp⟩ ⟨gpow (entry + i + 1), fp⟩
            (fun op ↦ if op = .jump then 1 else 0) := by
        intro d f hc hd hf' hdK hfK
        exact runC_jump hf hpc ⟨0, d, f, hc, hd, hf', (isInK_iff _).mpr ⟨0, ofK_zero.symm⟩, hdK,
          hfK, by rw [ite_eq_left rfl]⟩
      simp only [stepI, optSeq_eq]
      split_ifs with hz hnz
      · refine ⟨fun ⟨⟨c, d, f, hc, hd, hf', _, hdK, hfK⟩, _⟩ ↦ ?_, fun pre _ _ _ _ post he ↦ ?_⟩
        · have h0 := (hst.1 oc _ (isZero_eq hz)).symm.trans hc
          obtain rfl : c = 0 := (Option.some.inj h0).symm
          exact ⟨hst, _, hnext hc hd hf' hdK hfK, hone _ fun _ ↦ rfl⟩
        · exfalso
          cases pre with
          | nil => simp at he
          | cons a pre => simp at he
      · rintro ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, -⟩ r hr
        obtain ⟨w, hw, hw0⟩ := isNonzero_val hnz fp
        have hcw : c = w.val fp := Option.some.inj (hc.symm.trans (hst.1 oc w hw))
        obtain ⟨hrun, he⟩ := hgo hc hd hf' hcK hdK hfK (hcw ▸ hw0) hr
        exact ⟨_, hrun, hone _ fun _ ↦ rfl, he⟩
      · refine ⟨fun ⟨⟨c, d, f, hc, hd, hf', _, hdK, hfK⟩, h0, _⟩ ↦ ?_,
          fun pre oc' od' of' x post he hpre ht r hr ↦ ?_⟩
        · obtain rfl : c = 0 := Option.some.inj (hc.symm.trans h0)
          exact ⟨hst, _, hnext hc hd hf' hdK hfK, hone _ fun _ ↦ rfl⟩
        · cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, Item.branch.injEq] at he
            obtain ⟨⟨rfl, rfl, rfl, rfl⟩, -⟩ := he
            obtain ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, v, hv, hv0⟩ := ht
            obtain rfl := Option.some.inj (hv.symm.trans hc)
            obtain ⟨hrun, he⟩ := hgo hc hd hf' hcK hdK hfK hv0 hr
            exact ⟨_, hrun, hone _ fun _ ↦ rfl, he⟩
          | cons a pre =>
            exfalso
            simp only [List.cons_append, List.cons.injEq] at he
            simp at he
    | _ => simp [OInstr.isJump] at hj

/-- A segment being walked, at offset `i`, along a path. -/
def CurZ (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (c : Cur) (i : ℕ) : Prop :=
  EnvHolds L fp c.env →
    (Fall L fp c.acc.reverse → St.Holds L fp c.st ∧
      ReachC L prog ⟨gpow (entry + c.start), fp⟩ ⟨gpow (entry + i), fp⟩ c.acc.reverse) ∧
    ∀ pre oc od of x post, c.acc.reverse = pre ++ .branch oc od of x :: post → Fall L fp pre →
      Taken L fp oc od of → ∀ r, x.kind.Regs L fp entry r →
        ToC L fp prog ⟨gpow (entry + c.start), fp⟩ r (pre ++ [.branch oc od of x]) x

/-- **A segment along a path**: all its items holding, it reaches its exit's registers; leaving
by a taken branch, that branch's, each with that exit's environment holding. -/
def SegZ (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (s : Seg) : Prop :=
  EnvHolds L fp s.env →
    (Fall L fp s.items → ∀ r, s.exit.kind.Regs L fp entry r →
      ToC L fp prog ⟨gpow (entry + s.start), fp⟩ r s.items s.exit) ∧
    ∀ pre oc od of x post, s.items = pre ++ .branch oc od of x :: post → Fall L fp pre →
      Taken L fp oc od of → ∀ r, x.kind.Regs L fp entry r →
        ToC L fp prog ⟨gpow (entry + s.start), fp⟩ r (pre ++ [.branch oc od of x]) x

theorem curZ_init (i : ℕ) (env : Trie Sym) : CurZ L fp prog entry (Cur.init i env) i := by
  intro he
  refine ⟨fun _ ↦ ⟨stHolds_init he, 0, RunC.refl _, fun _ ↦ Nat.zero_le _⟩,
    fun pre _ _ _ _ post h ↦ ?_⟩
  simp [Cur.init] at h

theorem segZ_close {c : Cur} {i : ℕ} (hc : CurZ L fp prog entry c i) (succ : List ℕ) :
    SegZ L fp prog entry (c.close [] ⟨.next i, c.st.env, succ⟩) := by
  intro he
  have hc := hc he
  simp only [Cur.close, items_close, List.append_nil]
  refine ⟨fun hf r hr ↦ ?_, hc.2⟩
  obtain ⟨hst, n, hn, hle⟩ := hc.1 hf
  simp only [Kind.Regs] at hr
  subst hr
  exact ⟨n, hn, hle, hst.1⟩

/-- `A ++ B` split at a branch: the branch in `A`, or in `B`. -/
theorem split_branch {A B pre post : List Item} {it : Item} (h : A ++ B = pre ++ it :: post) :
    (∃ post', A = pre ++ it :: post') ∨ ∃ pre', pre = A ++ pre' ∧ B = pre' ++ it :: post := by
  rcases List.append_eq_append_iff.mp h with ⟨a', rfl, hB⟩ | ⟨c', hA, hB⟩
  · exact Or.inr ⟨a', rfl, hB⟩
  · cases c' with
    | nil => exact Or.inr ⟨[], by simp [hA], by simpa using hB.symm⟩
    | cons x c' =>
      simp only [List.cons_append, List.cons.injEq] at hB
      obtain ⟨rfl, rfl⟩ := hB
      exact Or.inl ⟨c', hA⟩

theorem curZ_go (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurZ L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {st : St}
    (hs : stepI F entry len i c.st ins = .go its st) :
    CurZ L fp prog entry
      ⟨c.start, c.env, its.reverseAux c.acc, (branchExits its).reverseAux c.xs, st⟩ (i + 1) := by
  intro he
  have hc := hc he
  simp only [List.reverseAux_eq, List.reverse_append, List.reverse_reverse]
  refine ⟨fun hfall ↦ ?_, fun pre oc od of x post hsp hpre ht r hr ↦ ?_⟩
  · obtain ⟨hA, hB⟩ := (fall_append _ _).mp hfall
    obtain ⟨hst, h⟩ := hc.1 hA
    have := stepI_z (len := len) hctx hf hpc hst
    rw [hs] at this
    obtain ⟨hst', h'⟩ := this.1 hB
    refine ⟨hst', ?_⟩
    have e : entry + i + 1 = entry + (i + 1) := by omega
    rw [e] at h'
    exact reachC_trans h h'
  · rcases split_branch hsp with ⟨post', hA⟩ | ⟨pre', rfl, hB⟩
    · exact hc.2 pre oc od of x post' hA hpre ht r hr
    · obtain ⟨hA, hpre'⟩ := (fall_append _ _).mp hpre
      obtain ⟨hst, h⟩ := hc.1 hA
      have := stepI_z (len := len) hctx hf hpc hst
      rw [hs] at this
      have h' := this.2 pre' oc od of x post hB hpre' ht r hr
      rw [List.append_assoc]
      exact toC_after h h'

theorem segZ_stop (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurZ L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {x : Exit}
    (hs : stepI F entry len i c.st ins = .stop its x) : SegZ L fp prog entry (c.close its x) := by
  intro he
  have hc := hc he
  have hits : ∃ oc od of, its = [.ins (.jump oc od of)] := by
    cases ins with
    | jump oc od of =>
      simp only [stepI, optSeq_eq] at hs
      split_ifs at hs
      cases hs
      exact ⟨_, _, _, rfl⟩
    | _ => rw [stepI_of_nonJump rfl] at hs; cases hs
  simp only [Cur.close, items_close]
  refine ⟨fun hfall r hr ↦ ?_, fun pre oc od of x' post hsp hpre ht r hr ↦ ?_⟩
  · obtain ⟨hA, hB⟩ := (fall_append _ _).mp hfall
    obtain ⟨hst, h⟩ := hc.1 hA
    have := stepI_z (len := len) hctx hf hpc hst
    rw [hs] at this
    exact toC_after h (this hB r hr)
  · rcases split_branch hsp with ⟨post', hA⟩ | ⟨pre', rfl, hB⟩
    · exact hc.2 pre oc od of x' post' hA hpre ht r hr
    · exfalso
      obtain ⟨_, _, _, h⟩ := hits
      rw [h] at hB
      cases pre' with
      | nil => simp at hB
      | cons a pre' => simp at hB

theorem atJoinZ_good {i : ℕ} {cur : Option Cur} {pend : Pend} {out : List Seg}
    (hcur : ∀ c, cur = some c → CurZ L fp prog entry c i)
    (hout : ∀ s ∈ out, SegZ L fp prog entry s) :
    (∀ c, (atJoin i cur pend out).1 = some c → CurZ L fp prog entry c i) ∧
      ∀ s ∈ (atJoin i cur pend out).2.2, SegZ L fp prog entry s := by
  unfold atJoin
  split
  · rename_i t a ps
    split_ifs with ht
    · cases cur with
      | some c =>
        simp only [Trie.seq_eq]
        split_ifs with hlt
        · refine ⟨fun c' hc' ↦ ?_, fun s hs ↦ ?_⟩
          · obtain rfl := Option.some.inj hc'
            exact curZ_init i _
          · rcases List.mem_cons.mp hs with rfl | hs
            · exact segZ_close (hcur c rfl) [i]
            · exact hout s hs
        · refine ⟨fun c' hc' ↦ ?_, hout⟩
          obtain rfl := Option.some.inj hc'
          exact curZ_init i _
      | none =>
        simp only [Trie.seq_eq]
        refine ⟨fun c' hc' ↦ ?_, hout⟩
        obtain rfl := Option.some.inj hc'
        exact curZ_init i _
    · exact ⟨hcur, hout⟩
  · exact ⟨hcur, hout⟩

/-- **The walk produces segments complete along every path.** -/
theorem passZ_good (hctx : Ctx F κ fp) : ∀ (code : List OInstr) (i : ℕ) (cur : Option Cur)
    (pend : Pend) (out : List Seg) (dead : ℕ), Fetches prog (entry + i) code →
    (∀ c, cur = some c → CurZ L fp prog entry c i) →
    (∀ s ∈ out, SegZ L fp prog entry s) →
    ∀ s ∈ (pass F entry len code i cur pend out dead).segs, SegZ L fp prog entry s
  | [], i, cur, pend, out, dead, _, hcur, hout => by
    show ∀ s ∈ (passEnd len i cur out dead).segs, _
    unfold passEnd
    cases cur with
    | none => exact hout
    | some c =>
      simp only
      by_cases hlt : c.start < i
      · rw [ite_eq_left hlt]
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact segZ_close (hcur c rfl) _
        · exact hout s hs
      · rw [ite_eq_right hlt]
        exact hout
  | ins :: rest, i, cur, pend, out, dead, hf, hcur, hout => by
    show ∀ s ∈ (passStep F entry len ins (pass F entry len rest) i cur pend out dead).segs, _
    obtain ⟨hcur', hout'⟩ := atJoinZ_good (pend := pend) hcur hout
    have hrest : Fetches prog (entry + (i + 1)) rest := by
      simpa [Nat.add_assoc] using hf.tail
    obtain ⟨hfi, hpc⟩ := hf.head
    unfold passStep
    rcases hj : atJoin i cur pend out with ⟨cur', pend', out'⟩
    rw [hj] at hcur' hout'
    cases cur' with
    | none =>
      simp only [natSeq_eq]
      exact passZ_good hctx rest (i + 1) none pend' out' (dead + 1) hrest (fun _ h ↦ by cases h)
        hout'
    | some c =>
      have hc := hcur' c rfl
      simp only
      rcases hs : stepI F entry len i c.st ins with ⟨its, st⟩ | ⟨its, x⟩
      · simp only [St.seq_eq, headSeq_eq, natSeq_eq]
        exact passZ_good hctx rest (i + 1) _ _ out' dead hrest
          (fun c' h ↦ Option.some.inj h ▸ curZ_go hctx hc hfi hpc hs) hout'
      · simp only [headSeq_eq, natSeq_eq]
        refine passZ_good hctx rest (i + 1) none _ _ dead hrest (fun _ h ↦ by cases h) ?_
        intro s hs'
        rcases List.mem_cons.mp hs' with rfl | hs'
        · exact segZ_stop hctx hc hfi hpc hs
        · exact hout' s hs'

/-- **Every segment of a window is complete along every path.** -/
theorem execWin_z (hctx : Ctx F κ fp) {f : CompiledFn} (hf : Fetches prog f.entry f.code)
    {a b : ℕ} {env : List (ℕ × Sym)} {s : Seg} (hs : s ∈ (execWin F f a env b).segs) :
    SegZ L fp prog f.entry s :=
  passZ_good hctx _ a _ [] [] 0 (hf.window a (b - a))
    (fun _ h ↦ Option.some.inj h ▸ curZ_init a _) (fun _ h ↦ by cases h) s hs

end Pass

end
end LeanVM.Guest.B2C
