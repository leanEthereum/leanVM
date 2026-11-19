module

public import X86.Compile.Code
public import X86.Bridge
public import Kraken.X64.WP

/-!
# The compiler is correct

In any layout of a compiled program (`Host`), the machine run from the entry label inevitably
reaches the body's `ret` in a state related to the one `Exec` ends with, or, when the body fails,
the failure handler's `ret` after the handler's run (`Compile.program_correct`).

The proof follows `Exec`: a compiled statement placed anywhere in the program (`code_correct`) ends
at the address after its code, or at `qm_fail` when it fails. Each step is one directive
(`step_at`, from Kraken's `Host.eventually_of_interp`); labels take no space, and every label of the
program is distinct, so a jump to a label lands at the index of its directive (`label_eq`).
-/

namespace X86.Compile

public section

variable [Host]

/-! ## Labels -/

omit [Host] in
theorem findSome?_of_getElem? {α β : Type} {f : α → Option β} :
    ∀ {L : List α} {j : Nat} {x : α} {y : β}, L[j]? = some x → f x = some y →
      (∀ i < j, ∀ z, L[i]? = some z → f z = none) → L.findSome? f = some y
  | [], _, _, _, hj, _, _ => by simp at hj
  | a :: L, 0, x, y, hj, hf, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    simp [hf]
  | a :: L, j + 1, x, y, hj, hf, hb => by
    rw [List.findSome?_cons, hb 0 (by omega) a rfl]
    exact findSome?_of_getElem? hj hf fun i hi z hz => hb (i + 1) (by omega) z hz

omit [Host] in
theorem eq_of_labelOf {L : List Directive} (hD : (L.filterMap labelOf).Nodup) :
    ∀ {i j : Nat} {l : Label}, L[i]? = some (.label l) → L[j]? = some (.label l) → i = j := by
  induction L with
  | nil => simp
  | cons d L ih =>
    intro i j l hi hj
    cases d with
    | label l' =>
      simp only [List.filterMap_cons, labelOf, List.nodup_cons] at hD
      match i, j with
      | 0, 0 => rfl
      | 0, j + 1 =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
          Kraken.Directive.label.injEq] at hi hj
        subst hi
        exact (hD.1 (List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hj, rfl⟩)).elim
      | i + 1, 0 =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
          Kraken.Directive.label.injEq] at hi hj
        subst hj
        exact (hD.1 (List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hi, rfl⟩)).elim
      | i + 1, j + 1 => exact congrArg (· + 1) (ih hD.2 hi hj)
    | _ =>
      simp only [List.filterMap_cons, labelOf] at hD
      match i, j with
      | 0, _ => simp at hi
      | _ + 1, 0 => simp at hj
      | i + 1, j + 1 => exact congrArg (· + 1) (ih hD hi hj)

/-- A label of a program whose labels are distinct is the address of its directive. -/
theorem label_eq (hD : (Host.prog.filterMap labelOf).Nodup) {j : Nat} {l : Label}
    (hj : Host.prog[j]? = some (.label l)) : label l = Host.addrOf j := by
  show (Host.exe.withAddresses.findSome? _).getD (-1) = _
  have hw : ∀ i, Host.exe.withAddresses[i]? = Host.prog[i]?.map fun d =>
      ({ directive := d, size := Host.layout.size d i, addr := Host.addrOf i } :
        Kraken.Addressable Directive) := by
    intro i
    rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?, Option.map_map]
    rfl
  rw [findSome?_of_getElem? (j := j) (y := Host.addrOf j) (by rw [hw, hj]; rfl) (by simp)]
  · rfl
  · intro i hi z hz
    rw [hw] at hz
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hz
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false]
    rintro rfl
    exact absurd (eq_of_labelOf hD hd hj) (by omega)

/-- A label takes no space. -/
theorem addrOf_label {k : Nat} {l : Label} (hk : Host.prog[k]? = some (.label l)) :
    Host.addrOf (k + 1) = Host.addrOf k := by
  rw [Host.addrOf_succ hk]
  simp [Kraken.Layout.size]

/-! ## Steps -/

/-- One directive. -/
theorem step_at {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) {post : @Post MachineState}
    {m : MachineData}
    (h : (d.interp m ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
      (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 Host.exe) post ⟨m, Host.addrOf k⟩ :=
  Host.eventually_of_interp (p := []) (List.isInfixAt_iff_getElem?.mpr (by simpa using hd)) h

theorem step_ins {k : Nat} {i : QInstr} (hd : Host.prog[k]? = some (.instr i.toInstr))
    {s s' : QState} {m : MachineData} (h : i.step s = some s') (hr : StateRel s m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf (k + 1) ∧ StateRel s' st.data)
      ⟨m, Host.addrOf k⟩ :=
  step_at hd (QInstr.toInstr_correct i h hr _ _)

theorem step_cond {k : Nat} {c : Cond} (hd : Host.prog[k]? = some (.instr c.toInstr))
    {s : QState} {m : MachineData} (hr : StateRel s m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf (k + 1) ∧ StateRel s st.data ∧
      c.cc.interp st.data.status = c.eval s) ⟨m, Host.addrOf k⟩ :=
  step_at hd (Cond.toInstr_correct c hr _ _)

theorem step_jcc {k : Nat} {cc : CondCode} {l : Label} (hd : Host.prog[k]? = some (jcc cc l))
    {m : MachineData} :
    Eventually (step1 Host.exe) (fun st => st =
      ⟨m, if cc.interp m.status then label l else Host.addrOf (k + 1)⟩) ⟨m, Host.addrOf k⟩ := by
  refine step_at hd ?_
  simp only [jcc, Directive.interp, Instr.interp, Operation.interp, Effects.All]
  split <;> simp [Effects.All, *]

theorem step_jmp {k : Nat} {l : Label} (hd : Host.prog[k]? = some (jmp l)) {m : MachineData} :
    Eventually (step1 Host.exe) (fun st => st = ⟨m, label l⟩) ⟨m, Host.addrOf k⟩ := by
  refine step_at hd ?_
  simp only [jmp, Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, Effects.All]
  rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]

omit [Host] in
theorem CondCode.not_interp (cc : CondCode) (st : StatusFlags) :
    (CondCode.not cc).interp st = !cc.interp st := by
  obtain ⟨cf, pf, af, zf, sf, of⟩ := st
  cases cc <;> cases cf <;> cases pf <;> cases zf <;> cases sf <;> cases of <;> rfl

/-! ## Compiled statements -/

/-- Where a run lands: at `okPc` related to the final state, or at `failPc` when it fails. -/
def Lands (o : Outcome) (okPc failPc : Int64) (st : MachineState) : Prop :=
  match o with
  | .ok s => StateRel s st.data ∧ st.pc = okPc
  | .err s => StateRel s st.data ∧ st.pc = failPc

omit [Host] in
theorem Lands.congr {o : Outcome} {a b f : Int64} {st : MachineState} (h : a = b)
    (hl : Lands o a f st) : Lands o b f st := h ▸ hl

omit [Host] in
theorem Lands.err_any {s : QState} {a b f : Int64} {st : MachineState}
    (hl : Lands (.err s) a f st) : Lands (.err s) b f st := hl

omit [Host] in
theorem infixGet {L P : List Directive} {k i j : Nat} {d : Directive} (h : L.IsInfixAt P k)
    (hi : L[i]? = some d) (hj : k + i = j) : P[j]? = some d := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact hj ▸ List.isInfixAt_iff_getElem?.mp h i hlt

omit [Host] in
theorem infixAt {L P : List Directive} {k j : Nat} (h : L.IsInfixAt P k) (hj : k = j) :
    L.IsInfixAt P j := hj ▸ h

/-- A compiled statement placed anywhere in a program whose labels are distinct runs as `Exec` says:
it ends after its code, or at `qm_fail` when it fails. -/
theorem code_correct (hD : (Host.prog.filterMap labelOf).Nodup) {c : Stmt} {s : QState}
    {o : Outcome} (hE : Exec c s o) :
    ∀ {n k : Nat} {m : MachineData}, (code c n).1.IsInfixAt Host.prog k → StateRel s m →
      Eventually (step1 Host.exe)
        (Lands o (Host.addrOf (k + (code c n).1.length)) (label "qm_fail"))
        ⟨m, Host.addrOf k⟩ := by
  induction hE with
  | skip s => exact fun _ hr => .done _ ⟨hr, by simp [code]⟩
  | ins h =>
    intro n k m hc hr
    refine eventually_weaken _ _ _ _ ?_ (step_ins (infixGet hc (i := 0) rfl rfl) h hr)
    rintro ⟨d, pc⟩ ⟨rfl, hr'⟩
    exact ⟨hr', by simp [code]⟩
  | seqOk _ _ iha ihb =>
    intro n k m hc hr
    simp only [code] at hc
    obtain ⟨hca, hcb⟩ := hc.append
    refine eventually_trans _ _ _ _ (iha hca hr) ?_
    rintro ⟨d, pc⟩ ⟨hr1, rfl⟩
    exact eventually_weaken _ _ _ _ (fun _ => Lands.congr (by congr 1; simp [code]; omega))
      (ihb hcb hr1)
  | seqErr _ iha =>
    intro n k m hc hr
    simp only [code] at hc
    exact eventually_weaken _ _ _ _ (fun _ => Lands.err_any) (iha hc.append.1 hr)
  | @iteTrue c t e s o hcv _ iht =>
    intro n k m hc hr
    simp only [code] at hc
    obtain ⟨h1, hLend⟩ := hc.append
    obtain ⟨h2, -⟩ := h1.append
    obtain ⟨h3, hmid⟩ := h2.append
    obtain ⟨hpre, hct⟩ := h3.append
    refine eventually_trans _ _ _ _ (step_cond (infixGet hpre (i := 0) rfl rfl) hr) ?_
    rintro ⟨d, pc⟩ ⟨rfl, hr1, hcc⟩
    refine eventually_trans _ _ _ _ (step_jcc (infixGet hpre (i := 1) rfl rfl)) ?_
    rintro _ rfl
    simp only [CondCode.not_interp, hcc, hcv, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    refine eventually_trans _ _ _ _ (iht (infixAt hct (by simp)) hr1) ?_
    rintro ⟨d', pc'⟩ hl
    cases o with
    | err s₁ => exact .done _ (Lands.err_any hl)
    | ok s₁ =>
      obtain ⟨hr2, rfl⟩ := hl
      have hJm : Host.prog[k + 2 + (code t (n + 2)).1.length]? = some (jmp (lbl (n + 1))) :=
        infixGet hmid (i := 0) rfl (by simp; omega)
      have hL : Host.prog[k + 2 + (code t (n + 2)).1.length + 2 +
          (code e (code t (n + 2)).2).1.length]? = some (.label (lbl (n + 1))) :=
        infixGet hLend (i := 0) rfl (by simp; omega)
      refine eventually_trans _ _ _ _ (step_jmp hJm) ?_
      rintro _ rfl
      refine .done _ ⟨hr2, ?_⟩
      show label _ = _
      rw [label_eq hD hL, ← addrOf_label hL]
      congr 1; simp [code]; omega
  | @iteFalse c t e s o hcv _ ihe =>
    intro n k m hc hr
    simp only [code] at hc
    obtain ⟨h1, hLend⟩ := hc.append
    obtain ⟨h2, hce⟩ := h1.append
    obtain ⟨h3, hmid⟩ := h2.append
    obtain ⟨hpre, -⟩ := h3.append
    refine eventually_trans _ _ _ _ (step_cond (infixGet hpre (i := 0) rfl rfl) hr) ?_
    rintro ⟨d, pc⟩ ⟨rfl, hr1, hcc⟩
    refine eventually_trans _ _ _ _ (step_jcc (infixGet hpre (i := 1) rfl rfl)) ?_
    rintro _ rfl
    simp only [CondCode.not_interp, hcc, hcv, Bool.not_false,
      ↓reduceIte]
    have hLe : Host.prog[k + 3 + (code t (n + 2)).1.length]? = some (.label (lbl n)) :=
      infixGet hmid (i := 1) rfl (by simp; omega)
    have hL : Host.prog[k + 3 + (code t (n + 2)).1.length + 1 +
        (code e (code t (n + 2)).2).1.length]? = some (.label (lbl (n + 1))) :=
      infixGet hLend (i := 0) rfl (by simp; omega)
    rw [label_eq hD hLe, ← addrOf_label hLe]
    refine eventually_weaken _ _ _ _ (fun _ => Lands.congr ?_)
      (ihe (infixAt hce (by simp; omega)) hr1)
    rw [← addrOf_label hL]
    congr 1; simp [code]; omega
  | @loopTrue c b s s₁ o hcv _ _ ihb ihl =>
    intro n k m hc hr
    have hc' := hc
    simp only [code] at hc'
    obtain ⟨h1, hmid⟩ := hc'.append
    obtain ⟨hpre, hcb⟩ := h1.append
    have hLtop : Host.prog[k]? = some (.label (lbl n)) := infixGet hpre (i := 0) rfl rfl
    rw [← addrOf_label hLtop]
    refine eventually_trans _ _ _ _ (step_cond (infixGet hpre (i := 1) rfl rfl) hr) ?_
    rintro ⟨d, pc⟩ ⟨rfl, hr1, hcc⟩
    refine eventually_trans _ _ _ _ (step_jcc (infixGet hpre (i := 2) rfl rfl)) ?_
    rintro _ rfl
    simp only [CondCode.not_interp, hcc, hcv, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    refine eventually_trans _ _ _ _ (ihb (infixAt hcb (by simp)) hr1) ?_
    rintro ⟨d', pc'⟩ ⟨hr2, rfl⟩
    have hJm : Host.prog[k + 1 + 1 + 1 + (code b (n + 2)).1.length]? = some (jmp (lbl n)) :=
      infixGet hmid (i := 0) rfl (by simp; omega)
    refine eventually_trans _ _ _ _ (step_jmp hJm) ?_
    rintro _ rfl
    rw [label_eq hD hLtop]
    exact ihl hc hr2
  | @loopErr c b s s₁ hcv _ ihb =>
    intro n k m hc hr
    simp only [code] at hc
    obtain ⟨h1, -⟩ := hc.append
    obtain ⟨hpre, hcb⟩ := h1.append
    have hLtop : Host.prog[k]? = some (.label (lbl n)) := infixGet hpre (i := 0) rfl rfl
    rw [← addrOf_label hLtop]
    refine eventually_trans _ _ _ _ (step_cond (infixGet hpre (i := 1) rfl rfl) hr) ?_
    rintro ⟨d, pc⟩ ⟨rfl, hr1, hcc⟩
    refine eventually_trans _ _ _ _ (step_jcc (infixGet hpre (i := 2) rfl rfl)) ?_
    rintro _ rfl
    simp only [CondCode.not_interp, hcc, hcv, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    exact eventually_weaken _ _ _ _ (fun _ => Lands.err_any) (ihb (infixAt hcb (by simp)) hr1)
  | @loopFalse c b s hcv =>
    intro n k m hc hr
    simp only [code] at hc
    obtain ⟨h1, hmid⟩ := hc.append
    obtain ⟨hpre, -⟩ := h1.append
    have hLtop : Host.prog[k]? = some (.label (lbl n)) := infixGet hpre (i := 0) rfl rfl
    rw [← addrOf_label hLtop]
    refine eventually_trans _ _ _ _ (step_cond (infixGet hpre (i := 1) rfl rfl) hr) ?_
    rintro ⟨d, pc⟩ ⟨rfl, hr1, hcc⟩
    refine eventually_trans _ _ _ _ (step_jcc (infixGet hpre (i := 2) rfl rfl)) ?_
    rintro _ rfl
    simp only [CondCode.not_interp, hcc, hcv, Bool.not_false,
      ↓reduceIte]
    have hL : Host.prog[k + 1 + 1 + 1 + (code b (n + 2)).1.length + 1]? =
        some (.label (lbl (n + 1))) :=
      infixGet hmid (i := 1) rfl (by simp; omega)
    refine .done _ ⟨hr1, ?_⟩
    show label _ = _
    rw [label_eq hD hL, ← addrOf_label hL]
    congr 1; simp [code]; omega
  | fail s =>
    intro n k m hc hr
    refine eventually_trans _ _ _ _ (step_jmp (infixGet hc (i := 0) rfl rfl)) ?_
    rintro _ rfl
    exact .done _ ⟨hr, rfl⟩

/-! ## The program -/

/-- From the entry of a compiled program, in any layout, the machine inevitably reaches the body's
`ret` in a state related to the one `Exec` ends with, or, when the body fails, the failure
handler's `ret` in a state related to the one the handler ends with. -/
theorem program_correct {body onFail : Stmt} (hP : Host.prog = program body onFail)
    {s : QState} {o : Outcome} {m : MachineData} (hE : Exec body s o) (hR : StateRel s m)
    (hFail : ∀ s₁, o = .err s₁ → ∃ s₂, Exec onFail s₁ (.ok s₂)) :
    Eventually (step1 Host.exe)
      (fun st => (∃ s₁, o = .ok s₁ ∧ StateRel s₁ st.data ∧ st.pc = Host.addrOf (retOkIndex body)) ∨
        (∃ s₁ s₂, o = .err s₁ ∧ Exec onFail s₁ (.ok s₂) ∧ StateRel s₂ st.data ∧
          st.pc = Host.addrOf (retFailIndex body onFail)))
      ⟨m, Host.addrOf 0⟩ := by
  have hD : (Host.prog.filterMap labelOf).Nodup := hP ▸ program_labels_nodup body onFail
  have hprog : (program body onFail).IsInfixAt Host.prog 0 := hP ▸ ⟨[], by simp⟩
  simp only [program] at hprog
  obtain ⟨h1, -⟩ := hprog.append
  obtain ⟨h2, hcf⟩ := h1.append
  obtain ⟨h3, hfl⟩ := h2.append
  obtain ⟨h4, -⟩ := h3.append
  obtain ⟨hrun, hcb⟩ := h4.append
  have hL0 : Host.prog[0]? = some (.label "qm_entry") := infixGet hrun (i := 0) rfl rfl
  have hLf : Host.prog[2 + (code body 0).1.length]? = some (.label "qm_fail") :=
    infixGet hfl (i := 0) rfl (by simp; omega)
  rw [← addrOf_label hL0]
  refine eventually_trans _ _ _ _ (code_correct hD hE (infixAt hcb (by simp)) hR) ?_
  rintro ⟨d, pc⟩ hl
  cases o with
  | ok s₁ =>
    obtain ⟨hr1, rfl⟩ := hl
    exact .done _ (Or.inl ⟨s₁, rfl, hr1, by simp only [retOkIndex]⟩)
  | err s₁ =>
    obtain ⟨hr1, rfl⟩ := hl
    obtain ⟨s₂, hE₂⟩ := hFail s₁ rfl
    rw [label_eq hD hLf, ← addrOf_label hLf]
    refine eventually_weaken _ _ _ _ ?_ (code_correct hD hE₂ (infixAt hcf (by simp; omega)) hr1)
    rintro ⟨d', pc'⟩ ⟨hr2, rfl⟩
    exact Or.inr ⟨s₁, s₂, rfl, hE₂, hr2, by simp only [retFailIndex]; congr 1; omega⟩

end

end X86.Compile
