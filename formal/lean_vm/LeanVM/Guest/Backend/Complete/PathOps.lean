/-
  LeanVM.Guest.Backend.Complete.PathOps

  The counts of a path: what a path to a return runs is within the placed body's path maxima and
  the separately counted arms it passes (`pathOpsStmt`).
-/

module

public import LeanVM.Guest.Backend.Complete.Spec

/-!
# A path's count within the path maxima

`opsL` follows `σ`'s path through a placed block, `pmL` takes the most over every path, both
read with the core block through `ctrlSplit`. On an aligned placement (`alL`), a path that falls
through a block is within the block's falling maximum and one that returns within its returning
maximum (`l_bound`); a path that falls through a block is one on which the core block falls
through too, so a path on which the core body returns is a returning path of the placed body
(`pathOps_le_ret`). For a separately counted function, the arms of its top-level chains are not in
`pmaxP`: the arm a path takes adds its own count through `armsCost` (`top_bound`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Counts within maxima -/

/-- A count within a maximum (`none`: no path, so none is). -/
def cle (c : Opcode → ℕ) : Option (Opcode → ℕ) → Prop
  | some m => ∀ op, c op ≤ m op
  | none => False

theorem cle_refl (c : Opcode → ℕ) : cle c (some c) := fun _ => le_rfl

theorem cle_omax_left {c : Opcode → ℕ} {a : Option (Opcode → ℕ)} (b : Option (Opcode → ℕ))
    (h : cle c a) : cle c (omax a b) := by
  cases a with
  | none => exact h.elim
  | some m =>
      cases b with
      | none => exact h
      | some m' => exact fun op => (h op).trans (le_max_left _ _)

theorem cle_omax_right {c : Opcode → ℕ} (a : Option (Opcode → ℕ)) {b : Option (Opcode → ℕ)}
    (h : cle c b) : cle c (omax a b) := by
  cases b with
  | none => exact h.elim
  | some m' =>
      cases a with
      | none => exact h
      | some m => exact fun op => (h op).trans (le_max_right _ _)

theorem cle_after {c : Opcode → ℕ} (d : Opcode → ℕ) {a : Option (Opcode → ℕ)} (h : cle c a) :
    cle (d + c) (a.map (d + ·)) := by
  cases a with
  | none => exact h.elim
  | some m => exact fun op => by simp only [cle, Pi.add_apply] at h ⊢; have := h op; omega

theorem cle_add {c₁ c₂ : Opcode → ℕ} {a b : Option (Opcode → ℕ)} (h₁ : cle c₁ a) (h₂ : cle c₂ b) :
    cle (c₁ + c₂) (a.bind fun x => b.map (x + ·)) := by
  cases a with
  | none => exact h₁.elim
  | some m =>
      cases b with
      | none => exact h₂.elim
      | some m' =>
          intro op
          have := h₁ op
          have := h₂ op
          simp only [Pi.add_apply]
          omega

theorem cle_mono {c c' : Opcode → ℕ} {a : Option (Opcode → ℕ)} (hc : ∀ op, c op ≤ c' op)
    (h : cle c' a) : cle c a := by
  cases a with
  | none => exact h.elim
  | some m => exact fun op => (hc op).trans (h op)

/-! ## Paths of the core -/

/-- An outcome that is not stuck. -/
def NS : Out → Prop
  | .stuck => False
  | _ => True

theorem ns_pre {es : List Ev} : ∀ {o : Out}, NS (o.pre es) ↔ NS o
  | .fall _ => Iff.rfl
  | .ret _ _ => Iff.rfl
  | .stuck => Iff.rfl

theorem ns_seq {k : Out} : ∀ {o : Out}, NS (o.seq k) → NS o
  | .fall _, _ => trivial
  | .ret _ _, _ => trivial
  | .stuck, h => h

theorem pre_pre {a b : List Ev} : ∀ o : Out, (o.pre a).pre b = o.pre (b ++ a)
  | .fall _ => by simp [Out.pre]
  | .ret _ _ => by simp [Out.pre]
  | .stuck => rfl

theorem pre_nil : ∀ o : Out, o.pre [] = o
  | .fall _ => by simp [Out.pre]
  | .ret _ _ => by simp [Out.pre]
  | .stuck => rfl

theorem walk_cons (σ : Val) (s : Stmt) (ss : List Stmt) :
    walk σ (s :: ss) = (walk1 σ s).seq (walk σ ss) := by
  rw [walk]

/-- A block with no control statement falls through. -/
theorem walk_ctrlSplit_none (σ : Val) : ∀ {cs : List Stmt}, ctrlSplit cs = none →
    ∃ es, walk σ cs = .fall es
  | [], _ => ⟨[], by rw [walk]⟩
  | s :: cs, h => by
      cases s
      case atom a =>
        simp only [ctrlSplit] at h
        obtain ⟨es, hes⟩ := walk_ctrlSplit_none σ h
        refine ⟨.atom a :: es, ?_⟩
        rw [walk_cons, walk1, hes]
        rfl
      all_goals simp [ctrlSplit] at h

/-- Up to the next control statement, a block's path is that statement's on. -/
theorem walk_ctrlSplit_some (σ : Val) : ∀ {cs : List Stmt} {s : Stmt} {rest : List Stmt},
    ctrlSplit cs = some (s, rest) → ∃ es, walk σ cs = (walk σ (s :: rest)).pre es
  | [], _, _, h => by simp [ctrlSplit] at h
  | c :: cs, s, rest, h => by
      cases c
      case atom a =>
        simp only [ctrlSplit] at h
        obtain ⟨es, hes⟩ := walk_ctrlSplit_some σ h
        refine ⟨.atom a :: es, ?_⟩
        rw [walk_cons, walk1, hes]
        show ((walk σ (s :: rest)).pre es).pre [.atom a] = _
        rw [pre_pre]
        rfl
      all_goals
        simp only [ctrlSplit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], (pre_nil _).symm⟩

/-- A fused dispatch falls through or is stuck. -/
theorem pick_fall (σ : Val) (x : V) (args rets : List V) :
    ∀ (fs : List String) (j : ℕ), NS (pick σ x args rets j fs) →
      ∃ es, pick σ x args rets j fs = .fall es
  | [], _, h => h.elim
  | f :: fs, j, h => by
      unfold pick at h ⊢
      split
      · exact ⟨_, rfl⟩
      · next hx =>
        simp only [hx, ↓reduceIte] at h
        exact pick_fall σ x args rets fs (j + 1) h

theorem seq_assoc : ∀ (o k l : Out), (o.seq k).seq l = o.seq (k.seq l)
  | .fall es, .fall es', l => by cases l <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .fall es, .ret es' vs, l => by simp [Out.seq, Out.pre]
  | .fall es, .stuck, l => by simp [Out.seq, Out.pre]
  | .ret es vs, k, l => by simp [Out.seq]
  | .stuck, k, l => by simp [Out.seq]

theorem walk_append' (σ : Val) : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by rw [List.cons_append, walk, walk, walk_append' σ l l', seq_assoc]

theorem walk_fall_cons {σ : Val} {s : Stmt} {rest : List Stmt} {e : List Ev}
    (h : walk1 σ s = .fall e) : walk σ (s :: rest) = (walk σ rest).pre e := by
  rw [walk_cons, h]
  rfl

theorem ns_head {σ : Val} {s : Stmt} {rest : List Stmt} (h : NS (walk σ (s :: rest))) :
    NS (walk1 σ s) := by
  rw [walk_cons] at h
  exact ns_seq h

theorem cle_ite {c : Opcode → ℕ} {a : Option (Opcode → ℕ)} (d e : Opcode → ℕ) (h : cle c a) :
    cle (d + c + e) ((a.map (· + e)).map (d + ·)) := by
  cases a with
  | none => exact h.elim
  | some m => intro op; have := h op; simp only [Pi.add_apply] at this ⊢; omega

theorem ft {P : Prop} : false = true → P := fun h => nomatch h

theorem tf {P : Prop} : true = false → P := fun h => nomatch h

section A

variable (keyed : Bool) (σ : Val)

/-- A placed statement's path count is within its maxima, its path the core's. -/
def SOk (s : PStmt) : Prop :=
  ∀ (cs : List Stmt) (k : List Stmt → Bool), alS s cs k = true → NS (walk σ cs) →
    ((opsS σ s cs).2.2 = true → k (opsS σ s cs).2.1 = true ∧
      (∃ es, walk σ cs = (walk σ (opsS σ s cs).2.1).pre es) ∧
      cle (opsS σ s cs).1 (pmS keyed false s).fall) ∧
    ((opsS σ s cs).2.2 = false → cle (opsS σ s cs).1 (pmS keyed false s).ret)

/-- A placed block's. -/
def LOk (ps : List PStmt) : Prop :=
  ∀ cs : List Stmt, alL ps cs = true → NS (walk σ cs) →
    ((opsL σ ps cs).2 = true → (∃ es, walk σ cs = .fall es) ∧
      cle (opsL σ ps cs).1 (pmL keyed false ps).fall) ∧
    ((opsL σ ps cs).2 = false → cle (opsL σ ps cs).1 (pmL keyed false ps).ret)

/-- A chain's stages'. -/
def StOk (sts : List (List (List PStmt))) : Prop :=
  ∀ cms : List Stmt, alStages sts cms = true → NS (walk σ cms) →
    ((opsStages σ sts cms).2 = true → (∃ es, walk σ cms = .fall es) ∧
      cle (opsStages σ sts cms).1 (pmStages keyed false sts).fall) ∧
    ((opsStages σ sts cms).2 = false → cle (opsStages σ sts cms).1 (pmStages keyed false sts).ret)

/-- A stage's arms'. -/
def ArOk (xv : V) (pas : List (List PStmt)) : Prop :=
  ∀ (arms : List (List Stmt)) (j : ℕ), alArms pas arms = true → NS (walkArms σ xv j arms) →
    ((opsArms σ xv pas arms j).2 = true → (∃ es, walkArms σ xv j arms = .fall es) ∧
      cle (opsArms σ xv pas arms j).1 (pmArms keyed false pas).fall) ∧
    ((opsArms σ xv pas arms j).2 = false → cle (opsArms σ xv pas arms j).1 (pmArms keyed false pas).ret)

variable {keyed σ}

theorem op_ok (h : List LHint) (o : LOp) : SOk keyed σ (.op h o) := by
  intro cs k hal _
  simp only [alS] at hal
  simp only [opsS, pmS]
  exact ⟨fun _ => ⟨hal, ⟨[], (pre_nil _).symm⟩, cle_refl _⟩, tf⟩

theorem ret_ok (h : List LHint) (one : Cell) : SOk keyed σ (.ret h one) := by
  intro cs k _ _
  simp only [opsS, pmS]
  exact ⟨ft, fun _ => cle_refl _⟩

theorem halt_ok (h : List LHint) (one dest : Cell) : SOk keyed σ (.halt h one dest) := by
  intro cs k _ _
  simp only [opsS, pmS]
  exact ⟨ft, fun _ => cle_refl _⟩

/-- A control statement stands for a core control statement. -/
theorem ctrl_of {s : PStmt} {cs : List Stmt} {k : List Stmt → Bool} (hal : alS s cs k = true)
    (hs : ∀ h o, s ≠ .op h o) : ∃ c rest, ctrlSplit cs = some (c, rest) := by
  rcases hcs : ctrlSplit cs with _ | ⟨c, rest⟩
  · cases s with
    | op h o => exact absurd rfl (hs h o)
    | _ => simp [alS, hcs] at hal
  · exact ⟨c, rest, rfl⟩

theorem call_ok (h : List LHint) (c : CallSite) : SOk keyed σ (.call h c) := by
  intro cs k hal hns
  obtain ⟨s, rest, hcs⟩ := ctrl_of hal (fun _ _ => nofun)
  obtain ⟨es0, hw⟩ := walk_ctrlSplit_some σ hcs
  simp only [alS, hcs] at hal
  have hfall : ∃ e, walk1 σ s = .fall e ∧ k rest = true := by
    cases s <;> simp_all [walk1]
  obtain ⟨e, he, hk⟩ := hfall
  simp only [opsS, hcs, pmS]
  split
  · next htc =>
    refine ⟨ft, fun _ => ?_⟩
    simp only [htc.1, ↓reduceIte]
    exact cle_refl _
  · exact ⟨fun _ => ⟨hk, ⟨es0 ++ e, by rw [hw, walk_fall_cons he, pre_pre]⟩, cle_refl _⟩, tf⟩

theorem loopNext_ok (h : List LHint) (callee : String) (nfp entry oc one : Cell)
    (args : List Cell) : SOk keyed σ (.loopNext h callee nfp entry oc one args) := by
  intro cs k hal hns
  obtain ⟨s, rest, hcs⟩ := ctrl_of hal (fun _ _ => nofun)
  obtain ⟨es0, hw⟩ := walk_ctrlSplit_some σ hcs
  simp only [alS, hcs] at hal
  cases s
  case callIf cv f a =>
    simp only [opsS, hcs, pmS]
    split
    · exact ⟨ft, fun _ => cle_refl _⟩
    · exact ⟨fun _ => ⟨hal, ⟨es0 ++ _, by rw [hw, walk_fall_cons (by rw [walk1]), pre_pre]⟩,
        cle_refl _⟩, tf⟩
  all_goals simp at hal

theorem dispatch_ok (h : List LHint) (callees : List String) (nfp joinCell x entry one : Cell)
    (first : ℕ) (args rets : List Cell) :
    SOk keyed σ (.dispatch h callees nfp joinCell x entry one first args rets) := by
  intro cs k hal hns
  obtain ⟨s, rest, hcs⟩ := ctrl_of hal (fun _ _ => nofun)
  obtain ⟨es0, hw⟩ := walk_ctrlSplit_some σ hcs
  simp only [alS, hcs] at hal
  cases s
  case dispatch xv fs a r =>
    simp only [opsS, hcs, pmS]
    rw [hw] at hns
    have h1 := ns_head ((ns_pre).mp hns)
    rw [walk1] at h1
    obtain ⟨e, he⟩ := pick_fall σ xv a r fs 0 h1
    exact ⟨fun _ => ⟨hal, ⟨es0 ++ e, by rw [hw, walk_fall_cons (by rw [walk1]; exact he), pre_pre]⟩,
      cle_refl _⟩, tf⟩
  all_goals simp at hal

theorem ite_ok {h : List LHint} {c bdest sfp : Cell} {zero : List PStmt} {hasElse : Bool}
    {edest one : Cell} {nonzero : List PStmt} (hz : LOk keyed σ zero) (hn : LOk keyed σ nonzero) :
    SOk keyed σ (.ite h c bdest sfp zero hasElse edest one nonzero) := by
  intro cs k hal hns
  obtain ⟨s, rest, hcs⟩ := ctrl_of hal (fun _ _ => nofun)
  obtain ⟨es0, hw⟩ := walk_ctrlSplit_some σ hcs
  simp only [alS, hcs] at hal
  cases s
  case ite cv z n =>
    simp only [Bool.and_eq_true] at hal
    obtain ⟨⟨hzal, hnal⟩, hk⟩ := hal
    rw [hw] at hns
    have h1 := ns_head ((ns_pre).mp hns)
    rw [walk1] at h1
    have h1' := (ns_pre).mp h1
    simp only [opsS, hcs, pmS, PM.alt, PM.after]
    by_cases h0 : σ cv = 0
    · simp only [h0, ↓reduceIte] at h1' ⊢
      obtain ⟨hzt, hzf⟩ := hz z hzal h1'
      cases hb : (opsL σ zero z).2
      · refine ⟨ft, fun _ => cle_omax_left _ ?_⟩
        have := cle_after setJump (hzf hb)
        exact cle_mono (fun op => by simp) this
      · obtain ⟨⟨esz, hesz⟩, hcz⟩ := hzt hb
        refine ⟨fun _ => ⟨hk, ⟨es0 ++ ([.inK cv] ++ esz), ?_⟩, cle_omax_left _ ?_⟩, tf⟩
        · rw [hw, walk_fall_cons (by simp only [walk1, h0, ↓reduceIte, hesz]; rfl), pre_pre]
        · have := cle_ite setJump (if hasElse then setJump else 0) hcz
          simpa using this
    · simp only [h0, ↓reduceIte] at h1' ⊢
      cases hasElse
      · simp only [Bool.false_eq_true, ↓reduceIte] at hnal ⊢
        obtain ⟨esn, hesn⟩ := walk_ctrlSplit_none σ (Option.isNone_iff_eq_none.mp hnal)
        refine ⟨fun _ => ⟨hk, ⟨es0 ++ ([.inK cv] ++ esn), ?_⟩, cle_omax_right _ (cle_refl _)⟩, tf⟩
        rw [hw, walk_fall_cons (by simp only [walk1, h0, ↓reduceIte, hesn]; rfl), pre_pre]
      · simp only [↓reduceIte] at hnal ⊢
        obtain ⟨hnt, hnf⟩ := hn n hnal h1'
        cases hb : (opsL σ nonzero n).2
        · exact ⟨ft, fun _ => cle_omax_right _ (cle_after setJump (hnf hb))⟩
        · obtain ⟨⟨esn, hesn⟩, hcn⟩ := hnt hb
          refine ⟨fun _ => ⟨hk, ⟨es0 ++ ([.inK cv] ++ esn), ?_⟩,
            cle_omax_right _ (cle_after setJump hcn)⟩, tf⟩
          rw [hw, walk_fall_cons (by simp only [walk1, h0, ↓reduceIte, hesn]; rfl), pre_pre]
  all_goals simp at hal

theorem chain_ok {h : List LHint} {join x entry one sfp : Cell} {firsts : List ℕ}
    {stages : List (List (List PStmt))} (hst : StOk keyed σ stages) :
    SOk keyed σ (.chain h join x entry one sfp firsts stages) := by
  intro cs k hal hns
  obtain ⟨s, rest, hcs⟩ := ctrl_of hal (fun _ _ => nofun)
  obtain ⟨es0, hw⟩ := walk_ctrlSplit_some σ hcs
  simp only [alS, hcs, Bool.and_eq_true, decide_eq_true_eq] at hal
  obtain ⟨⟨-, hsal⟩, hk⟩ := hal
  have hsplit := walk_append' σ ((s :: rest).take stages.length) ((s :: rest).drop stages.length)
  rw [List.take_append_drop] at hsplit
  rw [hw, hsplit] at hns
  have h1 := ns_seq ((ns_pre).mp hns)
  obtain ⟨hstt, hstf⟩ := hst _ hsal h1
  have hap : (keyed && false) = false := Bool.and_false keyed
  simp only [opsS, hcs, pmS, hap]
  cases hb : (opsStages σ stages ((s :: rest).take stages.length)).2
  · exact ⟨ft, fun _ => cle_after chainHead (hstf hb)⟩
  · obtain ⟨⟨est, hest⟩, hcst⟩ := hstt hb
    refine ⟨fun _ => ⟨hk, ⟨es0 ++ est, ?_⟩, cle_after chainHead hcst⟩, tf⟩
    rw [hw, hsplit, hest]
    show ((walk σ _).pre est).pre es0 = _
    rw [pre_pre]

theorem lnil_ok : LOk keyed σ [] := by
  intro cs hal _
  simp only [alL] at hal
  obtain ⟨es, hes⟩ := walk_ctrlSplit_none σ (Option.isNone_iff_eq_none.mp hal)
  simp only [opsL, pmL]
  exact ⟨fun _ => ⟨⟨es, hes⟩, cle_refl _⟩, tf⟩

theorem lcons_ok {s : PStmt} {ss : List PStmt} (hs : SOk keyed σ s) (hss : LOk keyed σ ss) :
    LOk keyed σ (s :: ss) := by
  intro cs hal hns
  simp only [alL] at hal
  obtain ⟨hst, hsf⟩ := hs cs _ hal hns
  simp only [opsL, pmL, PM.seq]
  cases hb : (opsS σ s cs).2.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by simp, fun _ => cle_omax_left _ (hsf hb)⟩
  · obtain ⟨hk, ⟨es, hes⟩, hcs⟩ := hst hb
    rw [hes] at hns
    obtain ⟨hlt, hlf⟩ := hss _ hk ((ns_pre).mp hns)
    simp only [↓reduceIte]
    refine ⟨fun hb' => ?_, fun hb' => cle_omax_right _ (cle_add hcs (hlf hb'))⟩
    obtain ⟨⟨es', hes'⟩, hc⟩ := hlt hb'
    exact ⟨⟨es ++ es', by rw [hes, hes']; rfl⟩, cle_add hcs hc⟩

theorem anil_ok (xv : V) : ArOk keyed σ xv [] := by
  intro arms j hal hns
  cases arms with
  | nil =>
      rw [walkArms] at hns
      exact hns.elim
  | cons => simp [alArms] at hal

theorem acons_ok {xv : V} {pa : List PStmt} {pas : List (List PStmt)} (hpa : LOk keyed σ pa)
    (hpas : ArOk keyed σ xv pas) : ArOk keyed σ xv (pa :: pas) := by
  intro arms j hal hns
  cases arms with
  | nil => simp [alArms] at hal
  | cons a as =>
      simp only [alArms, Bool.and_eq_true] at hal
      rw [walkArms] at hns
      simp only [opsArms, pmArms, Bool.false_eq_true, ↓reduceIte, PM.alt]
      by_cases hx : σ xv = ofK (addressOfIndex j)
      · simp only [hx, ↓reduceIte] at hns ⊢
        obtain ⟨ht, hf⟩ := hpa a hal.1 hns
        refine ⟨fun hb => ⟨?_, cle_omax_left _ (ht hb).2⟩, fun hb => cle_omax_left _ (hf hb)⟩
        rw [walkArms]
        simpa [hx] using (ht hb).1
      · simp only [hx, ↓reduceIte] at hns ⊢
        obtain ⟨ht, hf⟩ := hpas as (j + 1) hal.2 hns
        refine ⟨fun hb => ⟨?_, cle_omax_right _ (ht hb).2⟩, fun hb => cle_omax_right _ (hf hb)⟩
        rw [walkArms]
        simpa [hx] using (ht hb).1

theorem snil_ok : StOk keyed σ [] := by
  intro cms hal _
  cases cms with
  | cons => simp [alStages] at hal
  | nil =>
  simp only [opsStages, pmStages]
  exact ⟨fun _ => ⟨⟨[], by rw [walk]⟩, cle_refl _⟩, tf⟩

theorem scons_ok {st : List (List PStmt)} {sts : List (List (List PStmt))}
    (har : ∀ xv, ArOk keyed σ xv st) (hsts : StOk keyed σ sts) : StOk keyed σ (st :: sts) := by
  intro cms hal hns
  cases cms with
  | nil => simp [alStages] at hal
  | cons m cms' =>
      cases m
      case match_ xv arms =>
        simp only [alStages, Bool.and_eq_true] at hal
        rw [walk_cons, walk1] at hns
        obtain ⟨hat, haf⟩ := har xv arms 0 hal.1 (ns_seq hns)
        simp only [opsStages, pmStages, PM.seq]
        cases hb : (opsArms σ xv st arms 0).2
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨by simp, fun _ => cle_omax_left _ (haf hb)⟩
        · obtain ⟨⟨es, hes⟩, hca⟩ := hat hb
          rw [hes] at hns
          obtain ⟨hrt, hrf⟩ := hsts cms' hal.2 ((ns_pre (es := es)).mp hns)
          simp only [↓reduceIte]
          refine ⟨fun hb' => ?_, fun hb' => cle_omax_right _ (cle_add hca (hrf hb'))⟩
          obtain ⟨⟨es', hes'⟩, hc⟩ := hrt hb'
          exact ⟨⟨es ++ es', by rw [walk_cons, walk1, hes, hes']; rfl⟩, cle_add hca hc⟩
      all_goals simp [alStages] at hal

mutual
theorem stmt_ok : ∀ s : PStmt, SOk keyed σ s
  | .op h o => op_ok h o
  | .ite _ _ _ _ zero _ _ _ nonzero => ite_ok (block_ok zero) (block_ok nonzero)
  | .chain _ _ _ _ _ _ _ stages => chain_ok (stages_ok stages)
  | .call h c => call_ok h c
  | .loopNext h callee nfp entry oc one args => loopNext_ok h callee nfp entry oc one args
  | .dispatch h callees nfp joinCell x entry one first args rets =>
      dispatch_ok h callees nfp joinCell x entry one first args rets
  | .ret h one => ret_ok h one
  | .halt h one dest => halt_ok h one dest

theorem block_ok : ∀ ps : List PStmt, LOk keyed σ ps
  | [] => lnil_ok
  | s :: ss => lcons_ok (stmt_ok s) (block_ok ss)

theorem stages_ok : ∀ sts : List (List (List PStmt)), StOk keyed σ sts
  | [] => snil_ok
  | st :: sts => scons_ok (fun xv => arms_ok st xv) (stages_ok sts)

theorem arms_ok : ∀ (pas : List (List PStmt)) (xv : V), ArOk keyed σ xv pas
  | [], xv => anil_ok xv
  | pa :: pas, xv => acons_ok (block_ok pa) (arms_ok pas xv)
end

end A
/-! ## Counts within maxima and the separately counted arms -/

/-- A count within a maximum and some slack. -/
def cleA (c s : Opcode → ℕ) : Option (Opcode → ℕ) → Prop
  | some m => ∀ op, c op ≤ m op + s op
  | none => False

theorem cleA_of_cle {c : Opcode → ℕ} (s : Opcode → ℕ) {a : Option (Opcode → ℕ)} (h : cle c a) :
    cleA c s a := by
  cases a with
  | none => exact h.elim
  | some m => exact fun op => (h op).trans (Nat.le_add_right _ _)

theorem cleA_mono {c s s' : Opcode → ℕ} {a : Option (Opcode → ℕ)} (hs : ∀ op, s op ≤ s' op)
    (h : cleA c s a) : cleA c s' a := by
  cases a with
  | none => exact h.elim
  | some m => exact fun op => (h op).trans (by have := hs op; omega)

theorem cleA_omax_left {c s : Opcode → ℕ} {a : Option (Opcode → ℕ)} (b : Option (Opcode → ℕ))
    (h : cleA c s a) : cleA c s (omax a b) := by
  cases a with
  | none => exact h.elim
  | some m =>
      cases b with
      | none => exact h
      | some m' =>
          show ∀ op, c op ≤ max (m op) (m' op) + s op
          intro op
          have h1 := h op
          have := le_max_left (m op) (m' op)
          omega

theorem cleA_omax_right {c s : Opcode → ℕ} (a : Option (Opcode → ℕ)) {b : Option (Opcode → ℕ)}
    (h : cleA c s b) : cleA c s (omax a b) := by
  cases b with
  | none => exact h.elim
  | some m' =>
      cases a with
      | none => exact h
      | some m =>
          show ∀ op, c op ≤ max (m op) (m' op) + s op
          intro op
          have h1 := h op
          have := le_max_right (m op) (m' op)
          omega

theorem cleA_after {c s : Opcode → ℕ} (d : Opcode → ℕ) {a : Option (Opcode → ℕ)} (h : cleA c s a) :
    cleA (d + c) s (a.map (d + ·)) := by
  cases a with
  | none => exact h.elim
  | some m => intro op; have := h op; simp only [Pi.add_apply]; omega

theorem cleA_add {c₁ c₂ s₁ s₂ : Opcode → ℕ} {a b : Option (Opcode → ℕ)} (h₁ : cleA c₁ s₁ a)
    (h₂ : cleA c₂ s₂ b) : cleA (c₁ + c₂) (s₁ + s₂) (a.bind fun x => b.map (x + ·)) := by
  cases a with
  | none => exact h₁.elim
  | some m =>
      cases b with
      | none => exact h₂.elim
      | some m' =>
          intro op
          have := h₁ op
          have := h₂ op
          simp only [Pi.add_apply]
          omega

theorem led_listElementOrDefault {α : Type} : ∀ (l : List α) (i : ℕ) (d : α) (h : i < l.length),
    listElementOrDefault l i d = l[i]
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => rfl
  | _ :: l, i + 1, d, h => led_listElementOrDefault l i d (Nat.lt_of_succ_lt_succ h)

theorem ofCnt_getD (c : Opcode → ℕ) (op : Opcode) : (ofCnt c).getD (opIx op) 0 = c op := by
  cases op <;> rfl

theorem armsCost_cons (acs : List (ℕ × List (List ℕ))) (σ : Val) (s : Stmt) (ss : List Stmt) :
    armsCost acs σ (s :: ss) = cost1 acs σ s + armsCost acs σ ss := by
  rw [armsCost]

theorem armsCost_nil (acs : List (ℕ × List (List ℕ))) (σ : Val) : armsCost acs σ [] = 0 := by
  rw [armsCost]

theorem armsCost_append (acs : List (ℕ × List (List ℕ))) (σ : Val) :
    ∀ a b : List Stmt, armsCost acs σ (a ++ b) = armsCost acs σ a + armsCost acs σ b
  | [], b => by rw [List.nil_append, armsCost_nil, zero_add]
  | s :: a, b => by
      rw [List.cons_append, armsCost_cons, armsCost_cons, armsCost_append acs σ a b, add_assoc]

theorem armsCost_ctrlSplit (acs : List (ℕ × List (List ℕ))) (σ : Val) :
    ∀ {cs : List Stmt} {s : Stmt} {rest : List Stmt}, ctrlSplit cs = some (s, rest) →
      armsCost acs σ cs = armsCost acs σ (s :: rest)
  | [], _, _, h => by simp [ctrlSplit] at h
  | c :: cs, s, rest, h => by
      cases c
      case atom a =>
        simp only [ctrlSplit] at h
        rw [armsCost_cons, armsCost_ctrlSplit acs σ h]
        have : cost1 acs σ (.atom a) = 0 := by simp [cost1]
        rw [this, zero_add]
      all_goals
        simp only [ctrlSplit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl

theorem armsCost_le_rest (acs : List (ℕ × List (List ℕ))) (σ : Val) {cs : List Stmt} {s : Stmt}
    {rest : List Stmt} (h : ctrlSplit cs = some (s, rest)) (op : Opcode) :
    armsCost acs σ rest op ≤ armsCost acs σ cs op := by
  rw [armsCost_ctrlSplit acs σ h, armsCost_cons]
  simp only [Pi.add_apply]
  omega

theorem pmS_false_top (s : PStmt) : pmS false true s = pmS false false s := by
  cases s <;> rfl

theorem pmL_false_top : ∀ ps : List PStmt, pmL false true ps = pmL false false ps
  | [] => rfl
  | s :: ss => by rw [pmL, pmL, pmS_false_top, pmL_false_top ss]

theorem find?_key {acs : List (ℕ × List (List ℕ))} (hnd : (acs.map (·.1)).Nodup) :
    ∀ p ∈ acs, B2C.armRaw acs p.1 = some p.2 := by
  induction acs with
  | nil => intro p hp; exact absurd hp (List.not_mem_nil)
  | cons q acs ih =>
      intro p hp
      rw [List.map_cons, List.nodup_cons] at hnd
      unfold B2C.armRaw
      rcases List.mem_cons.mp hp with rfl | hp'
      · simp
      · have hne : q.1 ≠ p.1 := fun e => hnd.1 (e ▸ List.mem_map_of_mem hp')
        have := ih hnd.2 p hp'
        unfold B2C.armRaw at this
        rw [List.find?_cons_of_neg (by simpa [Nat.beq_eq] using hne)]
        exact this

section B

variable {σ : Val} (acs : List (ℕ × List (List ℕ)))

/-- The arms of a separately counted stage: the arm `σ` picks counts its own table entry. -/
def ArA (xv : V) (pas : List (List PStmt)) : Prop :=
  ∀ (arms : List (List Stmt)) (j : ℕ) (cnts : List (List ℕ)), alArms pas arms = true →
    NS (walkArms σ xv j arms) →
    (∀ i (h : i < pas.length),
      listElementOrDefault cnts (j + i) [] = ofCnt (((pmL true false pas[i]).fall).getD 0)) →
    ((opsArms σ xv pas arms j).2 = true → (∃ es, walkArms σ xv j arms = .fall es) ∧
      cleA (opsArms σ xv pas arms j).1 (costArms acs σ xv (some cnts) j arms)
        (pmArms true true pas).fall) ∧
    ((opsArms σ xv pas arms j).2 = false → cleA (opsArms σ xv pas arms j).1
      (costArms acs σ xv (some cnts) j arms) (pmArms true true pas).ret)

theorem arA : ∀ (xv : V) (pas : List (List PStmt)), ArA (σ := σ) acs xv pas
  | _, [], arms, j, _, hal, hns, _ => by
      cases arms with
      | nil => rw [walkArms] at hns; exact hns.elim
      | cons => simp [alArms] at hal
  | xv, pa :: pas, arms, j, cnts, hal, hns, hcn => by
      cases arms with
      | nil => simp [alArms] at hal
      | cons a as =>
          simp only [alArms, Bool.and_eq_true] at hal
          rw [walkArms] at hns
          simp only [opsArms, pmArms, ↓reduceIte, PM.alt]
          by_cases hx : σ xv = ofK (addressOfIndex j)
          · simp only [hx, ↓reduceIte] at hns ⊢
            rw [costArms, ite_eq_left_of_eq_true _ _ (eq_true hx)]
            obtain ⟨ht, hf⟩ := block_ok (keyed := true) pa a hal.1 hns
            have h0 := hcn 0 (by simp)
            simp only [Nat.add_zero, List.getElem_cons_zero] at h0
            refine ⟨fun hb => ⟨?_, ?_⟩, fun hb => ?_⟩
            · rw [walkArms]
              simpa [hx] using (ht hb).1
            · have hc := (ht hb).2
              refine cleA_omax_left _ ?_
              revert hc h0
              cases (pmL true false pa).fall with
              | none => exact fun _ h => h.elim
              | some m =>
                  intro h0 hc op
                  have h1 := hc op
                  have h2 : (listElementOrDefault cnts j []).getD (opIx op) 0 = m op := by
                    rw [h0, Option.getD_some]
                    exact ofCnt_getD m op
                  show _ ≤ 0 + ((listElementOrDefault cnts j []).getD (opIx op) 0 +
                    armsCost acs σ a op)
                  omega
            · exact cleA_omax_left _ (cleA_of_cle _ (hf hb))
          · simp only [hx, ↓reduceIte] at hns ⊢
            rw [costArms, ite_eq_right_of_eq_false _ _ (eq_false hx)]
            obtain ⟨ht, hf⟩ := arA xv pas as (j + 1) cnts hal.2 hns (fun i hi => by
              have := hcn (i + 1) (by simp; omega)
              simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
            refine ⟨fun hb => ⟨?_, cleA_omax_right _ (ht hb).2⟩, fun hb => cleA_omax_right _ (hf hb)⟩
            rw [walkArms]
            simpa [hx] using (ht hb).1

/-- The stages of a top-level chain of a separately counted function. -/
def StA (sts : List (List (List PStmt))) : Prop :=
  ∀ cms : List Stmt, alStages sts cms = true → NS (walk σ cms) →
    (∀ p ∈ stageCnts true cms sts, B2C.armRaw acs p.1 = some p.2) →
    ((opsStages σ sts cms).2 = true → (∃ es, walk σ cms = .fall es) ∧
      cleA (opsStages σ sts cms).1 (armsCost acs σ cms) (pmStages true true sts).fall) ∧
    ((opsStages σ sts cms).2 = false →
      cleA (opsStages σ sts cms).1 (armsCost acs σ cms) (pmStages true true sts).ret)

theorem stA : ∀ sts : List (List (List PStmt)), StA (σ := σ) acs sts
  | [], cms, hal, _, _ => by
      cases cms with
      | cons => simp [alStages] at hal
      | nil =>
          simp only [opsStages, pmStages, armsCost_nil]
          exact ⟨fun _ => ⟨⟨[], by rw [walk]⟩, fun op => by simp⟩, tf⟩
  | st :: sts, cms, hal, hns, hH => by
      cases cms with
      | nil => simp [alStages] at hal
      | cons m cms' =>
          cases m
          case match_ xv arms =>
            simp only [alStages, Bool.and_eq_true] at hal
            simp only [stageCnts, List.mem_cons, forall_eq_or_imp] at hH
            rw [walk_cons, walk1] at hns
            have hkey : B2C.armRaw acs xv.idx = some (armCnts true st) := hH.1
            obtain ⟨hat, haf⟩ := arA acs xv st arms 0 (armCnts true st) hal.1 (ns_seq hns)
              (fun i hi => by
                rw [Nat.zero_add, armCnts, led_listElementOrDefault _ _ _ (by simpa using hi)]
                simp)
            have hcost : armsCost acs σ (.match_ xv arms :: cms') =
                costArms acs σ xv (some (armCnts true st)) 0 arms + armsCost acs σ cms' := by
              rw [armsCost_cons, cost1, hkey]
            simp only [opsStages, pmStages, PM.seq, hcost]
            cases hb : (opsArms σ xv st arms 0).2
            · simp only [Bool.false_eq_true, ↓reduceIte]
              refine ⟨by simp, fun _ => cleA_omax_left _ (cleA_mono (fun op => ?_) (haf hb))⟩
              simp only [Pi.add_apply]
              omega
            · obtain ⟨⟨es, hes⟩, hca⟩ := hat hb
              rw [hes] at hns
              obtain ⟨hrt, hrf⟩ := stA sts cms' hal.2 ((ns_pre (es := es)).mp hns) hH.2
              simp only [↓reduceIte]
              refine ⟨fun hb' => ?_, fun hb' => cleA_omax_right _ (cleA_add hca (hrf hb'))⟩
              obtain ⟨⟨es', hes'⟩, hc⟩ := hrt hb'
              exact ⟨⟨es ++ es', by rw [walk_cons, walk1, hes, hes']; rfl⟩, cleA_add hca hc⟩
          all_goals simp [alStages] at hal

/-- A non-chain statement's maxima do not depend on whether it is at the top. -/
theorem pmS_true_top {s : PStmt} (hs : ∀ h j x e o sf f st, s ≠ .chain h j x e o sf f st) :
    pmS true true s = pmS true false s := by
  cases s
  case chain h j x e o sf f st => exact absurd rfl (hs h j x e o sf f st)
  all_goals rfl

/-- A control statement other than a chain passes exactly one core control statement. -/
theorem opsS_rest {s : PStmt} {cs : List Stmt} {c0 : Stmt} {rest : List Stmt}
    (hs : ∀ h j x e o sf f st, s ≠ .chain h j x e o sf f st) (hop : ∀ h o, s ≠ .op h o)
    (hcs : ctrlSplit cs = some (c0, rest)) (hb : (opsS σ s cs).2.2 = true) :
    (opsS σ s cs).2.1 = rest := by
  cases s
  case op h o => exact absurd rfl (hop h o)
  case chain h j x e o sf f st => exact absurd rfl (hs h j x e o sf f st)
  case ite _ _ _ _ _ hasElse _ _ _ =>
    cases c0
    case ite cv z n =>
      by_cases h0 : σ cv = 0
      · simp [opsS, hcs, h0]
      · cases hasElse <;> simp [opsS, hcs, h0]
    all_goals simp [opsS, hcs] at hb
  case call =>
    simp only [opsS, hcs]
    split <;> rfl
  case loopNext => simp [opsS, hcs]
  case dispatch => simp [opsS, hcs]
  case ret => simp [opsS] at hb
  case halt => simp [opsS] at hb

theorem armsGo_cons_ctrl {s : PStmt} {ss : List PStmt} {cs : List Stmt} {c : Stmt} {rest : List Stmt}
    (hs : ∀ h j x e o sf f st, s ≠ .chain h j x e o sf f st) (hop : ∀ h o, s ≠ .op h o)
    (hcs : ctrlSplit cs = some (c, rest)) : armsGo true (s :: ss) cs = armsGo true ss rest := by
  cases s
  case op h o => exact absurd rfl (hop h o)
  case chain h j x e o sf f st => exact absurd rfl (hs h j x e o sf f st)
  all_goals simp [armsGo, hcs]

/-- A top-level block of a separately counted function. -/
def TOk (ps : List PStmt) : Prop :=
  ∀ cs : List Stmt, alL ps cs = true → NS (walk σ cs) →
    (∀ p ∈ armsGo true ps cs, B2C.armRaw acs p.1 = some p.2) →
    ((opsL σ ps cs).2 = true → (∃ es, walk σ cs = .fall es) ∧
      cleA (opsL σ ps cs).1 (armsCost acs σ cs) (pmL true true ps).fall) ∧
    ((opsL σ ps cs).2 = false → cleA (opsL σ ps cs).1 (armsCost acs σ cs) (pmL true true ps).ret)

/-- One statement then the block, given the statement's part. -/
theorem tcons {s : PStmt} {ss : List PStmt} (hss : TOk (σ := σ) acs ss)
    (hstep : ∀ cs, alS s cs (fun cs' => alL ss cs') = true → NS (walk σ cs) →
      (∀ p ∈ armsGo true (s :: ss) cs, B2C.armRaw acs p.1 = some p.2) →
      ((opsS σ s cs).2.2 = true → alL ss (opsS σ s cs).2.1 = true ∧
        (∃ es, walk σ cs = (walk σ (opsS σ s cs).2.1).pre es) ∧
        (∀ p ∈ armsGo true ss (opsS σ s cs).2.1, B2C.armRaw acs p.1 = some p.2) ∧
        ∃ sl, (∀ op, sl op + armsCost acs σ (opsS σ s cs).2.1 op ≤ armsCost acs σ cs op) ∧
          cleA (opsS σ s cs).1 sl (pmS true true s).fall) ∧
      ((opsS σ s cs).2.2 = false → cleA (opsS σ s cs).1 (armsCost acs σ cs) (pmS true true s).ret)) :
    TOk (σ := σ) acs (s :: ss) := by
  intro cs hal hns hH
  simp only [alL] at hal
  obtain ⟨hst, hsf⟩ := hstep cs hal hns hH
  simp only [opsL, pmL, PM.seq]
  cases hb : (opsS σ s cs).2.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by simp, fun _ => cleA_omax_left _ (hsf hb)⟩
  · obtain ⟨hk, ⟨es, hes⟩, hH', sl, hsl, hcs⟩ := hst hb
    rw [hes] at hns
    obtain ⟨hlt, hlf⟩ := hss _ hk ((ns_pre).mp hns) hH'
    simp only [↓reduceIte]
    have hslack : ∀ op, (sl + armsCost acs σ (opsS σ s cs).2.1) op ≤ armsCost acs σ cs op :=
      fun op => by simpa using hsl op
    refine ⟨fun hb' => ?_, fun hb' => cleA_omax_right _ (cleA_mono hslack (cleA_add hcs (hlf hb')))⟩
    obtain ⟨⟨es', hes'⟩, hc⟩ := hlt hb'
    exact ⟨⟨es ++ es', by rw [hes, hes']; rfl⟩, cleA_mono hslack (cleA_add hcs hc)⟩

theorem tOk : ∀ ps : List PStmt, TOk (σ := σ) acs ps
  | [], cs, hal, _, _ => by
      simp only [alL] at hal
      obtain ⟨es, hes⟩ := walk_ctrlSplit_none σ (Option.isNone_iff_eq_none.mp hal)
      simp only [opsL, pmL]
      exact ⟨fun _ => ⟨⟨es, hes⟩, cleA_of_cle _ (cle_refl _)⟩, tf⟩
  | s :: ss, cs, hal, hns, hH => by
      refine tcons acs (tOk ss) (fun cs hal hns hH => ?_) cs hal hns hH
      by_cases hch : ∃ h j x e o sf f st, s = .chain h j x e o sf f st
      · obtain ⟨h, j, x, e, o, sf, f, stages, rfl⟩ := hch
        obtain ⟨c0, rest, hcs⟩ := ctrl_of hal (fun _ _ => nofun)
        obtain ⟨es0, hw⟩ := walk_ctrlSplit_some σ hcs
        simp only [alS, hcs, Bool.and_eq_true, decide_eq_true_eq] at hal
        obtain ⟨⟨-, hsal⟩, hk⟩ := hal
        have hsplit := walk_append' σ ((c0 :: rest).take stages.length)
          ((c0 :: rest).drop stages.length)
        rw [List.take_append_drop] at hsplit
        rw [hw, hsplit] at hns
        have h1 := ns_seq ((ns_pre).mp hns)
        simp only [armsGo, hcs, List.mem_append] at hH
        obtain ⟨hstt, hstf⟩ := stA acs stages _ hsal h1 (fun p hp => hH p (Or.inl hp))
        have hcost : armsCost acs σ cs = armsCost acs σ ((c0 :: rest).take stages.length) +
            armsCost acs σ ((c0 :: rest).drop stages.length) := by
          rw [armsCost_ctrlSplit acs σ hcs, ← armsCost_append, List.take_append_drop]
        simp only [opsS, hcs, pmS, Bool.and_self]
        cases hb : (opsStages σ stages ((c0 :: rest).take stages.length)).2
        · refine ⟨ft, fun _ => cleA_after chainHead (cleA_mono (fun op => ?_) (hstf hb))⟩
          rw [hcost]
          simp only [Pi.add_apply]
          omega
        · obtain ⟨⟨est, hest⟩, hcst⟩ := hstt hb
          refine ⟨fun _ => ⟨hk, ⟨es0 ++ est, ?_⟩, fun p hp => hH p (Or.inr hp), _,
            fun op => by rw [hcost]; simp only [Pi.add_apply]; exact le_rfl,
            cleA_after chainHead hcst⟩, tf⟩
          rw [hw, hsplit, hest]
          show ((walk σ _).pre est).pre es0 = _
          rw [pre_pre]
      · have hnc : ∀ h j x e o sf f st, s ≠ .chain h j x e o sf f st :=
          fun h j x e o sf f st he => hch ⟨h, j, x, e, o, sf, f, st, he⟩
        rw [pmS_true_top hnc]
        obtain ⟨hst, hsf⟩ := stmt_ok (keyed := true) s cs _ hal hns
        refine ⟨fun hb => ?_, fun hb => cleA_of_cle _ (hsf hb)⟩
        obtain ⟨hk, hw, hc⟩ := hst hb
        refine ⟨hk, hw, ?_, 0, fun op => ?_, cleA_of_cle _ hc⟩
        · by_cases hop : ∃ h o, s = .op h o
          · obtain ⟨h, o, rfl⟩ := hop
            simpa [armsGo, opsS] using hH
          · have hop' : ∀ h o, s ≠ .op h o := fun h o he => hop ⟨h, o, he⟩
            obtain ⟨c0, rest, hcs⟩ := ctrl_of hal hop'
            rw [armsGo_cons_ctrl hnc hop' hcs] at hH
            rw [opsS_rest hnc hop' hcs hb]
            exact hH
        · by_cases hop : ∃ h o, s = .op h o
          · obtain ⟨h, o, rfl⟩ := hop
            simp [opsS]
          · have hop' : ∀ h o, s ≠ .op h o := fun h o he => hop ⟨h, o, he⟩
            obtain ⟨c0, rest, hcs⟩ := ctrl_of hal hop'
            rw [opsS_rest hnc hop' hcs hb]
            simpa using armsCost_le_rest acs σ hcs op

end B

/-- **(The counts)** `pathOps_le`. -/
theorem pathOpsStmt : PathOpsStmt := by
  intro tf pf hal keyed hnd σ es vs hw op
  have hns : NS (walk σ tf.core.body) := by rw [hw]; trivial
  unfold pathOps pmaxP
  cases keyed
  · rw [pmL_false_top]
    obtain ⟨ht, hf⟩ := block_ok (keyed := false) pf.fn.body tf.core.body hal hns
    cases hb : (opsL σ pf.fn.body tf.core.body).2
    · have hc := hf hb
      revert hc
      cases (pmL false false pf.fn.body).ret with
      | none => exact fun h => h.elim
      | some m => intro hc; have := hc op; simp only [Option.getD_some]; omega
    · obtain ⟨⟨es', hes'⟩, -⟩ := ht hb
      rw [hw] at hes'
      exact absurd hes' (by simp)
  · have hH := find?_key hnd
    simp only [armsP, ↓reduceIte] at hH ⊢
    obtain ⟨ht, hf⟩ := tOk (σ := σ) (armsGo true pf.fn.body tf.core.body) pf.fn.body
      tf.core.body hal hns hH
    cases hb : (opsL σ pf.fn.body tf.core.body).2
    · have hc := hf hb
      revert hc
      cases (pmL true true pf.fn.body).ret with
      | none => exact fun h => h.elim
      | some m => intro hc; have := hc op; simp only [Option.getD_some]; omega
    · obtain ⟨⟨es', hes'⟩, -⟩ := ht hb
      rw [hw] at hes'
      exact absurd hes' (by simp)

/-- info: 'LeanVM.Guest.Backend.Complete.pathOpsStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Complete.pathOpsStmt

end
end LeanVM.Guest.Backend.Complete
