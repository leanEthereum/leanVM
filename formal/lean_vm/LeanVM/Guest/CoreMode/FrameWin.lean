module

public import LeanVM.Guest.CoreMode.FramePass

/-!
# A long function's frame walk, from its windows

A long function's walk is checked in windows (`frameWin`), from the cut at each inner bound to the
next; `framePass_of_wins` chains them into the whole pass (`FramePassOk`), and `frameAcc_of_wins`
adds the oracle, checked once (`FrameAcc`). At a cut the pass goes on from the cut's state whatever
it had (`cutF`), so the windows' runs are the pass's (`frameRunH_cut`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Exec
open LeanVM.Prover.Exec (Hint)

@[expose] public section

theorem trie_sub_refl {α : Type} {eq : α → α → Bool} (h : ∀ x, eq x x = true) :
    ∀ t : Trie α, t.sub eq t = true
  | .nil => rfl
  | .node v l r => by
    rw [Trie.sub_eq]
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, trie_sub_refl h l⟩, trie_sub_refl h r⟩
    cases v with
    | none => rfl
    | some x => exact h x

theorem sym_beq_refl : ∀ x : Sym, Sym.beq x x = true
  | .zero => rfl
  | .gp e => by simp [Sym.beq]
  | .fpg e => by simp [Sym.beq]

theorem fst_sub_reset (S : FSt) : S.sub S.reset = true := by
  simp only [FSt.sub, FSt.reset, Exec.St.init, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨trie_sub_refl sym_beq_refl _, Bits.sub_refl _⟩, Bits.sub_refl _⟩,
    trie_sub_refl (fun _ ↦ rfl) _⟩, trie_sub_refl (fun _ ↦ rfl) _⟩, trie_sub_refl Nat.beq_refl _⟩,
    trie_sub_refl Nat.beq_refl _⟩

theorem pendSub_reset : ∀ P : FPend, pendSub P (P.map fun g ↦ (g.1, g.2.1, g.2.2.reset)) = true
  | [] => rfl
  | (k, ts, S) :: P => by
    simp only [List.map_cons, pendSub, beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
    exact ⟨fst_sub_reset S, pendSub_reset P⟩

theorem cutF_cutSt {Fn : FFun} {a : ℕ} {c : Option FSt × FPend} (hc : Fn.cutAt a = some c) :
    cutF Fn a (cutSt c).1 (cutSt c).2 = some (cutSt c) := by
  unfold cutF
  rw [hc]
  simp only
  have h1 : curSub c.1 (c.1.map FSt.reset) = true := by
    rcases c with ⟨_ | S, P⟩
    · rfl
    · exact fst_sub_reset S
  rw [show (cutSt c).1 = c.1.map FSt.reset from rfl, show (cutSt c).2 = c.2.map fun g ↦ (g.1, g.2.1, g.2.2.reset)
    from rfl, h1, pendSub_reset c.2]
  rfl

/-- **At a cut** the pass goes on from the cut's state. -/
theorem frameRunH_cut {Fn : FFun} {a : ℕ} {c : Option FSt × FPend} (hc : Fn.cutAt a = some c)
    {cur : Option FSt} {pend : FPend} (h : cutF Fn a cur pend = some (cutSt c)) (ins : OffsetInstruction)
    (l : List OffsetInstruction) :
    frameRunH Fn (ins :: l) a cur pend = frameRunH Fn (ins :: l) a (cutSt c).1 (cutSt c).2 := by
  show passH Fn ins (frameRunH Fn l) a cur pend = passH Fn ins (frameRunH Fn l) a (cutSt c).1 (cutSt c).2
  unfold passH
  rw [h, cutF_cutSt hc]

/-- Where a window starts: its cut's state, or the entry state at offset `0`. -/
noncomputable def winStart (Fn : FFun) (a : ℕ) : Option (Option FSt × FPend) :=
  match Fn.cutAt a with
  | some c => some (cutSt c)
  | none => if a = 0 then some (some (entryF Fn), []) else none

theorem frameWin_spec {Fn : FFun} {code : List OffsetInstruction} (hd : Mode.pcsIncr Fn.hints = true)
    {a b : ℕ} (h : frameWin Fn code a b = true) :
    ∃ S R, winStart Fn a = some S ∧
      frameRunH Fn ((code.drop a).take (b - a)) a S.1 S.2 = some R ∧
      (b < Fn.len → (cutF Fn b R.1 R.2).isSome = true) ∧ (Fn.len ≤ b → R = (none, [])) := by
  unfold frameWin at h
  have hst : ∀ S, winStart Fn a = some S →
      (match frameRun Fn ((code.drop a).take (b - a)) a Fn.hints S.1 S.2 with
        | some (cur, pend) =>
          if b < Fn.len then (cutF Fn b cur pend).isSome
          else match cur, pend with
            | none, [] => true
            | _, _ => false
        | none => false) = true →
      ∃ S R, winStart Fn a = some S ∧ frameRunH Fn ((code.drop a).take (b - a)) a S.1 S.2 = some R ∧
        (b < Fn.len → (cutF Fn b R.1 R.2).isSome = true) ∧ (Fn.len ≤ b → R = (none, [])) := by
    intro S hS hm
    rw [frameRun_eq hd _ a Fn.hints _ _ ⟨hd, fun _ hx ↦ hx, fun _ hx _ ↦ hx⟩] at hm
    rcases e : frameRunH Fn ((code.drop a).take (b - a)) a S.1 S.2 with _ | ⟨cur, pend⟩
    · rw [e] at hm; cases hm
    rw [e] at hm
    simp only at hm
    refine ⟨S, (cur, pend), hS, e, fun hb ↦ ?_, fun hb ↦ ?_⟩
    · rw [ite_eq_left hb] at hm; exact hm
    · rw [ite_eq_right (show ¬ b < Fn.len by omega)] at hm
      rcases cur with _ | A <;> rcases pend with _ | ⟨g, gs⟩ <;> simp_all
  replace h : (winStart Fn a).elim false (fun S ↦
      match frameRun Fn ((code.drop a).take (b - a)) a Fn.hints S.1 S.2 with
      | some (cur, pend) =>
        if b < Fn.len then (cutF Fn b cur pend).isSome
        else match cur, pend with
          | none, [] => true
          | _, _ => false
      | none => false) = true := h
  rcases hw : winStart Fn a with _ | S
  · rw [hw] at h; cases h
  · rw [hw] at h
    obtain ⟨S', R, h1, h2⟩ := hst S hw h
    exact ⟨S', R, by rw [← hw]; exact h1, h2⟩

theorem take_append_slice {α : Type} (l : List α) {a b : ℕ} (hab : a ≤ b) :
    l.take b = l.take a ++ (l.drop a).take (b - a) := by
  have := List.take_add (l := l) (i := a) (j := b - a)
  rwa [Nat.add_sub_cancel' hab] at this

/-- **The windows give the pass**: from `0` through the inner bounds `bs`, each a cut, to the code's
end, each window accepted. -/
theorem framePass_of_wins {Fn : FFun} {code : List OffsetInstruction} (hd : Mode.pcsIncr Fn.hints = true)
    (hlen : Fn.len = code.length) :
    ∀ (bs : List ℕ) (a : ℕ) (R : Option FSt × FPend),
      incrF (a :: bs ++ [code.length]) = true →
      frameRunH Fn (code.take a) 0 (some (entryF Fn)) [] = some R →
      (∃ S, winStart Fn a = some S ∧ ∀ ins l, frameRunH Fn (ins :: l) a R.1 R.2 = frameRunH Fn (ins :: l) a S.1 S.2) →
      (∀ p ∈ List.zip (a :: bs) (bs ++ [code.length]), frameWin Fn code p.1 p.2 = true) →
      FramePassOk Fn code
  | [], a, R, hinc, hR, ⟨S, hS, hRS⟩, hw => by
    have hal : a < code.length := by simpa [incrF] using hinc
    obtain ⟨S', R', hS', hrun, -, hend⟩ := frameWin_spec hd (hw (a, code.length) (by simp))
    rw [hS] at hS'; cases hS'
    have hR' := hend (by omega)
    subst hR'
    unfold FramePassOk
    rw [← List.take_length (l := code), take_append_slice code hal.le, frameRunH_append, hR, Option.bind_some,
      List.length_take, Nat.min_eq_left hal.le, Nat.zero_add]
    rcases e : (code.drop a).take (code.length - a) with _ | ⟨ins, l⟩
    · have := congrArg List.length e
      simp at this; omega
    · rw [e] at hrun; rw [hRS, hrun]
  | b :: bs, a, R, hinc, hR, ⟨S, hS, hRS⟩, hw => by
    have hab : a < b := by simp only [List.cons_append, incrF, Bool.and_eq_true, decide_eq_true_eq] at hinc; exact hinc.1
    have hinc' : incrF (b :: bs ++ [code.length]) = true := by
      simp only [List.cons_append, incrF, Bool.and_eq_true] at hinc; exact hinc.2
    have hbl : b < code.length := by
      have := incrF_lt (t := b) (ts := bs ++ [code.length]) (by simpa using hinc') code.length (by simp)
      exact this
    obtain ⟨S', R', hS', hrun, hcut, -⟩ := frameWin_spec hd (hw (a, b) (by simp))
    rw [hS] at hS'; cases hS'
    have hR' : frameRunH Fn (code.take b) 0 (some (entryF Fn)) [] = some R' := by
      rw [take_append_slice code hab.le, frameRunH_append, hR, Option.bind_some, List.length_take,
        Nat.min_eq_left (by omega), Nat.zero_add]
      rcases e : (code.drop a).take (b - a) with _ | ⟨ins, l⟩
      · have := congrArg List.length e
        simp at this; omega
      · rw [e] at hrun; rw [hRS, hrun]
    refine framePass_of_wins hd hlen bs b R' hinc' hR' ?_ (fun p hp ↦ hw p (List.mem_cons_of_mem _ hp))
    obtain ⟨Sb, -, hSb, -⟩ := frameWin_spec hd (hw (b, (bs ++ [code.length]).head (by simp)) (by
      rcases bs with _ | ⟨b', bs⟩ <;> simp))
    unfold winStart at hSb
    rcases hcb : Fn.cutAt b with _ | c
    · rw [hcb] at hSb; simp only at hSb; split_ifs at hSb; omega
    rw [hcb] at hSb
    cases hSb
    have hc' := hcut (by omega)
    unfold cutF at hc'
    rw [hcb] at hc'
    simp only at hc'
    split_ifs at hc' with hsub
    · refine ⟨cutSt c, by unfold winStart; rw [hcb], fun ins l ↦ frameRunH_cut hcb ?_ ins l⟩
      unfold cutF; rw [hcb]; simp only; rw [ite_eq_left hsub]
    · cases hc'

/-- **The windows give the walk's acceptance**: the oracle checked once, and the windows (`framePass_of_wins`). -/
theorem frameAcc_of_wins {Fn : FFun} {code : List OffsetInstruction} (ho : oracleChk Fn = true)
    (hd : Mode.pcsIncr Fn.hints = true) (hlen : Fn.len = code.length) (bs : List ℕ) (a : ℕ)
    (R : Option FSt × FPend) (hinc : incrF (a :: bs ++ [code.length]) = true)
    (hR : frameRunH Fn (code.take a) 0 (some (entryF Fn)) [] = some R)
    (hS : ∃ S, winStart Fn a = some S ∧ ∀ ins l, frameRunH Fn (ins :: l) a R.1 R.2 = frameRunH Fn (ins :: l) a S.1 S.2)
    (hw : ∀ p ∈ List.zip (a :: bs) (bs ++ [code.length]), frameWin Fn code p.1 p.2 = true) :
    FrameAcc Fn code :=
  ⟨oracleOk_of ho, framePass_of_wins hd hlen bs a R hinc hR hS hw⟩

end

end LeanVM.Guest.CoreMode
