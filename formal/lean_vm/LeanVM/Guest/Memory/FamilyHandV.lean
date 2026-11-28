/-
  LeanVM.Guest.Memory.FamilyHandV

  A vector family with hand functions (`chkHJV`), `FamilyHand`'s `chkHJ` by coordinate: each
  coordinate of a vector check is the scalar check of the coordinates, not counting words
  (`chkHJV_proj`, `rangeOk_proj`), so `FamilyHand` and `HandNode` apply to each opcode's count.
-/

module

public import LeanVM.Guest.Memory.FamilyHand

/-!
# Vector families with hand functions

The vector checker (`Memory/StaticVec.lean`) checks a certificate per coordinate in one walk; here
with hand functions (`HandV`: virtual parameters and an inner vector certificate), loop hands and
absent functions, as `Memory/FamilyHand.lean`'s `chkHJ`. A vector check passes only if each
coordinate's scalar check does, not counting words (`chkHandV_proj`, `chkHandLV_proj`,
`chkHJV_proj`), so a vector family whose ranges pass gives, at each coordinate, a scalar family whose
ranges pass (`rangeOk_proj`), and `checkedH_of_chkHJ`, `loopHand_checked` and `HandNode`'s
`mainCost_le` apply to it. `chkHJV_of_*` give the check from a walk cut into ranges (`StaticCut`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- A hand function by coordinate: its virtual parameters and its inner vector certificate. -/
structure HandV where
  vps : List V
  pre : List (ℕ × ℕ)
  b : AffV
  ks : List (V × ℕ)

/-- Coordinate `i` of a hand. -/
def HandV.proj (i : ℕ) (h : HandV) : Hand := ⟨h.vps, h.pre, h.b.proj i, h.ks⟩

/-- The hand of no virtual parameter and no bound. -/
def HandV.zero : HandV := ⟨[], [], ⟨[], []⟩, []⟩

/-- A hand function's inner check by coordinate (`chkHand`'s). -/
noncomputable def chkHandV (look : String → CertV) (h : HandV) (w : Vec) (fn : Fn) : Bool :=
  statBV look h.pre h.b h.ks w (fn.withVps h.vps) fn.body ||
    selSplit fn.body (statBV look h.pre h.b h.ks w (fn.withVps h.vps))

/-- A loop hand's check by coordinate (`chkHandL`'s). -/
noncomputable def chkHandLV (look : String → CertV) (h : HandV) (endc : Option ℕ) (w : Vec) (fn : Fn) : Bool :=
  match loopShape fn endc with
  | some pre => match blockRV look h.ks (fn.params ++ h.vps) fn.name pre ([], []) with
    | some r => AffV.leB ⟨w.add r.1.c, r.1.cs⟩ h.b && r.2.all (· ∈ h.pre)
    | none => false
  | none => false

/-- **The check of function `j` in a vector family with hand functions** (`chkHJ`'s). -/
noncomputable def chkHJV (cert : ℕ → CertV) (hand : ℕ → Option HandV) (lh : ℕ → Option (HandV × Option ℕ))
    (abs : ℕ → Bool) (om : ℕ → Vec) (j : ℕ) (fn : Fn) : Bool :=
  abs j || match lh j with
    | some (h, endc) => chkHandLV (lookV cert j) h endc (om j) fn
    | none => match hand j with
      | some h => chkHandV (lookV cert j) h (om j) fn
      | none => chkV cert om j fn

/-! ## Coordinates -/

/-- Coordinate `i` of the certificates. -/
def certP (cert : ℕ → CertV) (i j : ℕ) : Cert := (cert j).proj i
/-- Coordinate `i` of the hands. -/
def handP (hand : ℕ → Option HandV) (i j : ℕ) : Option Hand := (hand j).map (HandV.proj i)
/-- Coordinate `i` of the loop hands. -/
def lhP (lh : ℕ → Option (HandV × Option ℕ)) (i j : ℕ) : Option (Hand × Option ℕ) :=
  (lh j).map fun p => (p.1.proj i, p.2)
/-- Coordinate `i` of the frame weights. -/
def omP (om : ℕ → Vec) (i j : ℕ) : ℕ := (om j).getD i 0

variable (i : ℕ)

theorem statBV_proj {look : String → CertV} {pre : List (ℕ × ℕ)} {b : AffV} {ks : List (V × ℕ)} {w : Vec}
    {fn : Fn} {body : List Stmt} (wl : String → Option ℕ) (h : statBV look pre b ks w fn body = true) :
    statB (fun g => (look g).proj i) wl false pre (b.proj i) ks (w.getD i 0) fn body = true := by
  unfold statBV at h
  unfold statB
  rw [← blockRV_proj (cert := look)]
  rcases hb : blockRV look ks fn.params fn.name body ([], []) with _ | r
  · rw [hb] at h; cases h
  · rw [hb] at h
    simp only [Bool.and_eq_true] at h
    simp only [Option.map_some, Bool.and_eq_true]
    exact ⟨leB_proj i h.1, h.2⟩

/-- **A hand's vector check passes only if each coordinate's does.** -/
theorem chkHandV_proj {look : String → CertV} {h : HandV} {w : Vec} {fn : Fn}
    (hc : chkHandV look h w fn = true) (wl : String → Option ℕ) :
    chkHand (fun g => (look g).proj i) wl false (h.proj i) (w.getD i 0) fn = true := by
  unfold chkHandV at hc
  unfold chkHand
  rw [Bool.or_eq_true]
  rcases Bool.or_eq_true_iff.mp hc with hc | hc
  · exact Or.inl (statBV_proj i wl hc)
  · exact Or.inr (selSplit_mono (fun b hb => statBV_proj i wl hb) hc)

/-- **A loop hand's vector check passes only if each coordinate's does.** -/
theorem chkHandLV_proj {look : String → CertV} {h : HandV} {endc : Option ℕ} {w : Vec} {fn : Fn}
    (hc : chkHandLV look h endc w fn = true) (wl : String → Option ℕ) :
    chkHandL (fun g => (look g).proj i) wl false (h.proj i) endc (w.getD i 0) fn = true := by
  unfold chkHandLV at hc
  unfold chkHandL
  rcases hs : loopShape fn endc with _ | pre
  · rw [hs] at hc; cases hc
  · rw [hs] at hc
    dsimp only at hc ⊢
    simp only [HandV.proj]
    rw [← blockRV_proj (cert := look)]
    rcases hb : blockRV look h.ks (fn.params ++ h.vps) fn.name pre ([], []) with _ | r
    · rw [hb] at hc; cases hc
    · rw [hb] at hc
      simp only [Bool.and_eq_true] at hc
      simp only [Option.map_some, Bool.and_eq_true]
      exact ⟨leB_proj i hc.1, hc.2⟩

theorem lookS_certP (cert : ℕ → CertV) (j : ℕ) : lookS (certP cert i) j = fun g => (lookV cert j g).proj i := by
  funext g
  unfold lookS lookV certP
  cases calleeIdx j g <;> rfl

variable {cert : ℕ → CertV} {hand : ℕ → Option HandV} {lh : ℕ → Option (HandV × Option ℕ)}
  {abs : ℕ → Bool} {om : ℕ → Vec} {j : ℕ} {fn : Fn}

/-- **A family's vector check passes only if each coordinate's scalar check does**, not counting
words. -/
theorem chkHJV_proj (hc : chkHJV cert hand lh abs om j fn = true) :
    chkHJ false (certP cert i) (handP hand i) (lhP lh i) abs (omP om i) j fn = true := by
  unfold chkHJV at hc
  unfold chkHJ
  cases ha : abs j
  · rw [ha, Bool.false_or] at hc
    rw [Bool.false_or]
    unfold lhP handP
    rcases hl : lh j with _ | ⟨h, endc⟩
    · rw [hl] at hc
      simp only [Option.map_none]
      rcases hh : hand j with _ | h
      · rw [hh] at hc
        simp only [Option.map_none]
        unfold chkS
        unfold chkV at hc
        rw [lookS_certP]
        exact chkFnV_proj i hc _
      · rw [hh] at hc
        simp only [Option.map_some]
        rw [lookS_certP]
        exact chkHandV_proj i hc _
    · rw [hl] at hc
      simp only [Option.map_some]
      rw [lookS_certP]
      exact chkHandLV_proj i hc _
  · rfl

theorem walkOk_mono {α : Type} {c c' : ℕ → α → Bool} (h : ∀ j x, c j x = true → c' j x = true) :
    ∀ (j : ℕ) (l : List α), walkOk c j l = true → walkOk c' j l = true
  | _, [], _ => rfl
  | j, x :: xs, hw => by
      simp only [walkOk, Bool.and_eq_true] at hw ⊢
      exact ⟨h j x hw.1, walkOk_mono h (j + 1) xs hw.2⟩

theorem RangeOk.mono {c c' : ℕ → Fn → Bool} (h : ∀ j x, c j x = true → c' j x = true) {a n : ℕ}
    (hr : RangeOk c a n) : RangeOk c' a n :=
  walkOk_mono h _ _ hr

/-- **Coordinate `i` of a vector family with hand functions whose ranges pass** is a scalar family
whose ranges pass. -/
theorem rangeOk_proj (hr : RangeOk (chkHJV cert hand lh abs om) 0 coreProgram.length) :
    RangeOk (chkHJ false (certP cert i) (handP hand i) (lhP lh i) abs (omP om i)) 0 coreProgram.length :=
  hr.mono fun _ _ h => chkHJV_proj i h

/-! ## The check from a walk -/

/-- The step of hand function `j`'s inner vector check. -/
noncomputable def stepHJV (cert : ℕ → CertV) (hand : ℕ → Option HandV) (j : ℕ) (fn : Fn) :
    Stmt → Env × BEnv → Option (AccV × Option (Env × BEnv)) :=
  stmtRV (lookV cert j) ((hand j).getD .zero).ks (fn.params ++ ((hand j).getD .zero).vps) fn.name

/-- The step of loop hand `j`'s vector iteration check. -/
noncomputable def stepLJV (cert : ℕ → CertV) (lh : ℕ → Option (HandV × Option ℕ)) (j : ℕ) (fn : Fn) :
    Stmt → Env × BEnv → Option (AccV × Option (Env × BEnv)) :=
  stmtRV (lookV cert j) ((lh j).getD (.zero, none)).1.ks (fn.params ++ ((lh j).getD (.zero, none)).1.vps) fn.name

/-- A certified function's vector check is its family check. -/
theorem chkHJV_of_chkV (habs : abs j = false) (hlh : lh j = none) (hh : hand j = none)
    (hc : chkV cert om j fn = true) : chkHJV cert hand lh abs om j fn = true := by
  unfold chkHJV; rw [habs, hlh, hh]; exact hc

/-- **A hand function's vector check from its walk.** -/
theorem chkHJV_of_hand_run {r : AccV} (habs : abs j = false) (hlh : lh j = none)
    (hh : (hand j).isSome = true)
    (hb : runB AccV.add AccV.zero (stepHJV cert hand j fn) fn.body ([], []) = some r)
    (hc : (CertV.stat ((hand j).getD .zero).pre ((hand j).getD .zero).b ((hand j).getD .zero).ks).final (om j) r = true) :
    chkHJV cert hand lh abs om j fn = true := by
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hh
  unfold chkHJV; rw [habs, hlh, hh]
  simp only [Bool.false_or]
  unfold chkHandV
  rw [Bool.or_eq_true]; left
  simp only [stepHJV, hh, Option.getD_some] at hb hc
  rw [← blockRV_run] at hb
  unfold statBV
  simp only [Fn.withVps]
  rw [hb]
  exact hc

/-- **A hand function's vector check split at its first top-level selector.** -/
theorem chkHJV_of_hand_split {x n : ℕ} (habs : abs j = false) (hlh : lh j = none)
    (hh : (hand j).isSome = true) (hs : topSel fn.body = some (x, n))
    (hc : (Nat.blt 0 n && Nat.blt n 4611686018427387904 && armLeL x n fn.body) = true)
    (harms : ∀ r < n, ∃ acc, runB AccV.add AccV.zero (stepHJV cert hand j fn) (selL x r fn.body) ([], []) =
      some acc ∧ (CertV.stat ((hand j).getD .zero).pre ((hand j).getD .zero).b
        ((hand j).getD .zero).ks).final (om j) acc = true) :
    chkHJV cert hand lh abs om j fn = true := by
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hh
  unfold chkHJV; rw [habs, hlh, hh]
  simp only [Bool.false_or]
  unfold chkHandV
  rw [Bool.or_eq_true]; right
  unfold selSplit
  rw [hs]
  dsimp only
  rw [hc, Bool.true_and, List.all_eq_true]
  intro r hr
  obtain ⟨acc, hrun, hfin⟩ := harms r (List.mem_range.mp hr)
  simp only [stepHJV, hh, Option.getD_some] at hrun hfin
  unfold statBV
  rw [blockRV_run]
  simp only [Fn.withVps]
  rw [hrun]
  exact hfin

/-- **A loop hand's vector check from its iteration's walk**, guarded against `ret`. -/
theorem chkHJV_of_loop_run {h : HandV} {endc : Option ℕ} {r : AccV} (habs : abs j = false)
    (hlh : lh j = some (h, endc)) (ht : (loopTail fn endc).isSome = true)
    (hb : runB AccV.add AccV.zero (guardRet (stepLJV cert lh j fn)) (loopBody fn) ([], []) = some r)
    (hc : (CertV.stat h.pre h.b h.ks).final (om j) r = true) : chkHJV cert hand lh abs om j fn = true := by
  unfold chkHJV; rw [habs, hlh]
  simp only [Bool.false_or]
  simp only [stepLJV, hlh, Option.getD_some] at hb
  obtain ⟨hn, hb⟩ := runB_guard (stmtRV_stops _ _ _ _) hb
  rw [← blockRV_run] at hb
  unfold chkHandLV
  rw [loopShape_of ht hn]
  simp only
  rw [hb]
  exact hc

end
end LeanVM.Guest.Memory
