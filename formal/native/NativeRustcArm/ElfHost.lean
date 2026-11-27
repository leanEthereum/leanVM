module

public import NativeRustcArm.Host
public import NativeRustc.MultiLayout

/-!
# Multi-section ELF host for AArch64

Generalizes `NativeRustcArm.Host` to a multi-section `ElfHost` whose sections sit at independent,
pairwise-disjoint 64-bit addresses with independent instruction sizes, and whose `elfStep1` takes
`[Labels]` explicitly. Real multi-section Linux AArch64 ELF binaries instantiate `ElfHost` directly.

`Host.toElfHost` embeds every single-section `NativeRustcArm.Host` into a 1-section `ElfHost` with
identical label resolution (`toElfHost_labels`) and step relation (`elfStep1_toElfHost`).
-/

namespace NativeRustcArm

open NativeRustc.MultiLayout

private theorem takeWhile_eq_take_of {α : Type _} {p : α → Bool} {l : List α} {n : Nat}
    (hprior : ∀ k, k < n → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[n]? = some c → p c = false) :
    l.takeWhile p = l.take n := by
  rw [List.takeWhile_eq_take_findIdx_not]
  by_cases hn : n < l.length
  · rw [(List.findIdx_eq hn).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hn)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by omega))]⟩]
  · rw [(List.take_of_length_le (Nat.le_of_not_lt hn) : l.take n = l), List.take_of_length_le]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by omega) _ (List.getElem?_eq_getElem hi)]

private theorem exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn with
  | ind n ih => grind

@[expose] public section

/-- A multi-section AArch64 executable. -/
abbrev ElfExecutable := MultiExecutable Instr ConstExpr

/-- Per-section AArch64 layout. -/
abbrev ElfSectionLayout := SectionLayout Instr ConstExpr

/-- Label lookup across all sections of an AArch64 `ElfExecutable`. -/
@[reducible]
def ElfExecutable.labels (me : ElfExecutable) : Labels :=
  { label l := (me.withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label l then .some addr else .none)).getD (-1) }

/-- One step of a multi-section AArch64 executable using Kraken's `Directives.interp`. -/
def ElfExecutable.step (me : ElfExecutable) (s : MachineState) (ret : MachineState → Effects)
    (labels : Labels) : Effects :=
  let := labels
  Directives.interp (me.directivesAtAddress s.pc) s.data s.pc (fun pc s => ret ⟨s, pc⟩)

/-- Omni-semantics single step for a multi-section AArch64 executable. -/
def elfStep1 [labels : Labels] (me : ElfExecutable) (s : MachineState)
    (post : @Post MachineState) : Prop :=
  (ElfExecutable.step me s .done labels).All post

/-- A multi-section AArch64 program and its ELF-compatible layout. -/
class ElfHost where
  /-- Each placed section: its directive list and per-section layout (`start` + `instrSize`). -/
  sections : List (Program × ElfSectionLayout)
  /-- Within each section, two directives at the same address have the same offset. -/
  addr_determines_offset : ∀ sec (hs : sec < sections.length) j k,
    let s := sections[sec].2.apply sections[sec].1
    s.addrOf j = s.addrOf k → s.sizeBefore j = s.sizeBefore k
  /-- Distinct sections never place any directive at the same virtual address. -/
  sections_disjoint : ∀ s₁ (h₁ : s₁ < sections.length) s₂ (h₂ : s₂ < sections.length),
    s₁ ≠ s₂ → ∀ j₁ < sections[s₁].1.length, ∀ j₂ < sections[s₂].1.length,
    (sections[s₁].2.apply sections[s₁].1).addrOf j₁ ≠
      (sections[s₂].2.apply sections[s₂].1).addrOf j₂

/-- The laid-out multi-section executable of an `ElfHost`. -/
def ElfHost.exe [ElfHost] : ElfExecutable :=
  { sections := ElfHost.sections.map fun (p, l) => l.apply p }

/-- The directive list of section `sec` (empty if out of bounds). -/
def ElfHost.sectionProg [ElfHost] (sec : Nat) : Program :=
  (ElfHost.sections[sec]?).map (·.1) |>.getD []

/-- The placed section `sec` (empty section at 0 if out of bounds). -/
def ElfHost.sectionAt [ElfHost] (sec : Nat) : Section Instr ConstExpr :=
  (ElfHost.exe.sections[sec]?).getD ⟨0, []⟩

/-- The address of directive `k` within section `sec` (`k = prog.length` gives the section end). -/
def ElfHost.addrOf [ElfHost] (sec k : Nat) : Int64 :=
  (ElfHost.sectionAt sec).addrOf k

/-- Label resolution for an AArch64 `ElfHost`. -/
instance instLabelsElfHost [ElfHost] : Labels := ElfExecutable.labels ElfHost.exe

/-- Embed a single-section `NativeRustcArm.Host` into a 1-section `ElfHost`. -/
@[instance_reducible]
def Host.toElfHost (h : NativeRustcArm.Host) : ElfHost where
  sections := [(h.prog, ⟨h.layout.start, h.layout.instrSize, h.layout.instrSize_pos⟩)]
  addr_determines_offset := by
    intro sec hs j k
    have hsec0 : sec = 0 := by simpa using hs
    subst hsec0
    dsimp only
    intro haddr
    have h1 := h.addr_determines_offset j k (by
      simpa [Section.addrOf, SectionLayout.apply_toExecutable, SectionLayout.toKrakenLayout]
        using haddr)
    simpa [Section.sizeBefore, SectionLayout.apply_toExecutable, SectionLayout.toKrakenLayout]
      using h1
  sections_disjoint := by
    intro s₁ h₁ s₂ h₂ hne
    simp at h₁ h₂
    omega

end

public section

theorem ElfHost.exe_sections_length [ElfHost] :
    ElfHost.exe.sections.length = ElfHost.sections.length := by
  simp [ElfHost.exe]

theorem ElfHost.sectionProg_eq [ElfHost] {sec : Nat} (hs : sec < ElfHost.sections.length) :
    ElfHost.sectionProg sec = ElfHost.sections[sec].1 := by
  simp [ElfHost.sectionProg, List.getElem?_eq_getElem hs]

theorem ElfHost.sectionAt_eq [ElfHost] {sec : Nat} (hs : sec < ElfHost.sections.length) :
    ElfHost.sectionAt sec = ElfHost.sections[sec].2.apply ElfHost.sections[sec].1 := by
  simp [ElfHost.sectionAt, ElfHost.exe, List.getElem?_eq_getElem hs]

theorem ElfHost.section_getElem? [ElfHost] {sec : Nat} (hs : sec < ElfHost.sections.length) (i : Nat) :
    (ElfHost.sectionAt sec).program[i]? =
      (ElfHost.sectionProg sec)[i]?.map fun d =>
        { directive := d, size := ElfHost.sections[sec].2.size d i } := by
  rw [ElfHost.sectionAt_eq hs, ElfHost.sectionProg_eq hs]
  exact SectionLayout.apply_getElem? _ _ _

theorem ElfHost.addrOf_succ [ElfHost] {sec k : Nat} (hs : sec < ElfHost.sections.length)
    {d : Directive} (hd : (ElfHost.sectionProg sec)[k]? = some d) :
    ElfHost.addrOf sec (k + 1) =
      ElfHost.addrOf sec k + .ofNat (ElfHost.sections[sec].2.size d k) := by
  rw [ElfHost.addrOf, ElfHost.addrOf, ElfHost.sectionAt_eq hs]
  rw [ElfHost.sectionProg_eq hs] at hd
  exact Section.addrOf_succ hd

private theorem inert_of_size_zero_sec [Labels] (l : ElfSectionLayout) {i : Nat} {d : Directive}
    (hz : l.size d i = 0) (s : MachineData) (p : Std.Rco Int64)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    d.interp s p next jmp = next s := by
  have hz' : l.toKrakenLayout.size d i = 0 := by cases d <;> exact hz
  exact @inert_of_size_zero l.toKrakenLayout _ i d hz' s p next jmp

theorem ElfHost.directivesAtAddress_addrOf [ElfHost] {sec k : Nat}
    (hs : sec < ElfHost.sections.length) {c : Kraken.Sized Directive}
    (hc : (ElfHost.sectionAt sec).program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre : List (Kraken.Sized Directive),
      ElfHost.exe.directivesAtAddress (ElfHost.addrOf sec k) = pre ++ [c] ∧
      ∀ c' ∈ pre, c'.size = 0 := by
  have hk_lt : k < ElfHost.sections[sec].1.length := by
    have hlt : k < (ElfHost.sectionAt sec).program.length := (List.getElem?_eq_some_iff.mp hc).1
    rw [ElfHost.sectionAt_eq hs, SectionLayout.apply, List.length_mapIdx] at hlt
    exact hlt
  have hsec_exe : sec < ElfHost.exe.sections.length := by rw [ElfHost.exe_sections_length]; exact hs
  have hme : ElfHost.exe.directivesAtAddress (ElfHost.addrOf sec k) =
      (ElfHost.sectionAt sec).directivesAtAddress (ElfHost.addrOf sec k) := by
    have h1 := MultiExecutable.directivesAtAddress_eq_section ElfHost.exe hsec_exe (ElfHost.addrOf sec k)
      (by
        intro s' hs' hne j hj
        have hs'_lt : s' < ElfHost.sections.length := by rwa [ElfHost.exe_sections_length] at hs'
        have hj_lt : j < ElfHost.sections[s'].1.length := by
          simpa [ElfHost.exe, SectionLayout.apply] using hj
        have hdisj := ElfHost.sections_disjoint s' hs'_lt sec hs hne j hj_lt k hk_lt
        simpa [ElfHost.exe, ElfHost.addrOf, ElfHost.sectionAt_eq hs] using hdisj)
    simpa [ElfHost.sectionAt, List.getElem?_eq_getElem hsec_exe] using h1
  rw [hme]
  let e := (ElfHost.sectionAt sec).toExecutable
  have hdet : ∀ a b, e.addrOf a = e.addrOf b → e.sizeBefore a = e.sizeBefore b := by
    intro a b hab
    have := ElfHost.addr_determines_offset sec hs a b
    simpa [e, ElfHost.sectionAt_eq hs, Section.addrOf, Section.sizeBefore] using this (by
      simpa [e, ElfHost.sectionAt_eq hs, Section.addrOf] using hab)
  obtain ⟨j, hjk, hj, hmin⟩ := exists_least_le (P := fun i => e.addrOf i = e.addrOf k) rfl
  have hsize := hdet j k hj
  have hpre : ∀ c' ∈ (e.program.drop j).take (k - j), c'.size = 0 := by
    have := e.sizeBefore_add j (k - j)
    rw [Nat.add_sub_cancel' hjk] at this
    have hsum : (((e.program.drop j).take (k - j)).map (·.size)).sum = 0 := by omega
    exact fun c' hc' => List.sum_eq_zero_iff_forall_eq_nat.mp hsum _ (List.mem_map_of_mem hc')
  have haddr : ∀ m, j ≤ m → m ≤ k → e.addrOf m = e.addrOf k := fun m hjm hmk => by
    grind [Kraken.Executable.addrOf, e.sizeBefore_mono hjm, e.sizeBefore_mono hmk]
  have hnext : e.addrOf (k + 1) ≠ e.addrOf k := fun h => by
    have := hdet (k + 1) k h
    have hsucc : e.sizeBefore (k + 1) = e.sizeBefore k + c.size :=
      Kraken.Executable.sizeBefore_succ e hc
    omega
  refine ⟨(e.program.drop j).take (k - j), ?_, hpre⟩
  show ((e.withAddresses.dropWhile
    (·.addr ≠ e.addrOf k)).takeWhile (·.addr = e.addrOf k)).map (·.toSized) = _
  rw [Kraken.Executable.withAddresses_dropWhile_addrOf e j k hj hmin,
    takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Kraken.Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk]
    change (e.program.drop j).take (k - j) ++ e.program[k]?.toList = _
    have hce : e.program[k]? = some c := hc
    rw [hce]
    rfl
  · intro m hm c' hc'
    have := haddr (j + m) (by omega) (by omega)
    grind [Kraken.Executable.getElem?_withAddresses_eq]
  · intro c' hc'
    grind [Kraken.Executable.getElem?_withAddresses_eq]

/-- One directive of section `sec` in an AArch64 `ElfHost`, run from its address. -/
theorem ElfHost.eventually_of_interp [ElfHost] {sec k : Nat} {d : Directive} {p : Program}
    (hdp : (d :: p).IsInfixAt (ElfHost.sectionProg sec) k) {post : @Post MachineState}
    {s : MachineData}
    (h : (d.interp s ⟨ElfHost.addrOf sec k, ElfHost.addrOf sec (k + 1)⟩
      (fun s' => .done ⟨s', ElfHost.addrOf sec (k + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (elfStep1 ElfHost.exe) post ⟨s, ElfHost.addrOf sec k⟩ := by
  have hs : sec < ElfHost.sections.length := by
    cases Nat.lt_or_ge sec ElfHost.sections.length with
    | inl hlt => exact hlt
    | inr hge =>
      have hnil : ElfHost.sectionProg sec = [] := by
        simp [ElfHost.sectionProg, List.getElem?_eq_none hge]
      have hcons := hdp.cons.1
      rw [hnil] at hcons
      simp at hcons
  have hd : (ElfHost.sectionAt sec).program[k]? =
      some { directive := d, size := ElfHost.sections[sec].2.size d k : Kraken.Sized Directive } := by
    rw [ElfHost.section_getElem? hs, hdp.cons.1]
    rfl
  rw [ElfHost.addrOf_succ hs hdp.cons.1] at h
  match hsize : ElfHost.sections[sec].2.size d k with
  | 0 =>
    apply Eventually.done
    simpa [hsize, inert_of_size_zero_sec (ElfHost.sections[sec].2) hsize, Effects.All] using h
  | _ + 1 =>
    refine Eventually.step _ post ?_ fun _ hb => Eventually.done _ hb
    obtain ⟨pre, hat, hpre⟩ := ElfHost.directivesAtAddress_addrOf hs hd (by simp [hsize])
    have hmem : ∀ c' ∈ pre, c' ∈ (ElfHost.sectionAt sec).program := by
      intro c' hc'
      have hsec_exe : sec < ElfHost.exe.sections.length := by rw [ElfHost.exe_sections_length]; exact hs
      have hme : ElfHost.exe.directivesAtAddress (ElfHost.addrOf sec k) =
          (ElfHost.sectionAt sec).directivesAtAddress (ElfHost.addrOf sec k) := by
        have hk_lt : k < ElfHost.sections[sec].1.length := by
          have hlt := (List.getElem?_eq_some_iff.mp hdp.cons.1).1
          rwa [ElfHost.sectionProg_eq hs] at hlt
        have h1 := MultiExecutable.directivesAtAddress_eq_section ElfHost.exe hsec_exe
          (ElfHost.addrOf sec k) (by
            intro s' hs' hne j hj
            have hs'_lt : s' < ElfHost.sections.length := by rwa [ElfHost.exe_sections_length] at hs'
            have hj_lt : j < ElfHost.sections[s'].1.length := by
              simpa [ElfHost.exe, SectionLayout.apply] using hj
            have hdisj := ElfHost.sections_disjoint s' hs'_lt sec hs hne j hj_lt k hk_lt
            simpa [ElfHost.exe, ElfHost.addrOf, ElfHost.sectionAt_eq hs] using hdisj)
        simpa [ElfHost.sectionAt, List.getElem?_eq_getElem hsec_exe] using h1
      rw [hme] at hat
      exact Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc')
    unfold elfStep1 ElfExecutable.step
    change (Directives.interp (ElfHost.exe.directivesAtAddress (ElfHost.addrOf sec k))
      s (ElfHost.addrOf sec k) _).All post
    rw [hat]
    clear hat
    induction pre with
    | nil => simpa [Directives.interp] using h
    | cons c' pre ih =>
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp (hmem c' List.mem_cons_self)
      obtain ⟨d', _, rfl⟩ := Option.map_eq_some_iff.mp (ElfHost.section_getElem? hs m ▸ hm)
      have hz0 : ElfHost.sections[sec].2.size d' m = 0 := hpre _ List.mem_cons_self
      simp only [hz0, List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
        inert_of_size_zero_sec (ElfHost.sections[sec].2) hz0]
      exact ih (fun c'' hc'' => hpre c'' (List.mem_cons_of_mem _ hc''))
        (fun c'' hc'' => hmem c'' (List.mem_cons_of_mem _ hc''))

theorem toElfHost_exe (h : NativeRustcArm.Host) :
    @ElfHost.exe (Host.toElfHost h) = toMultiExecutable (@NativeRustcArm.Host.exe h) := by
  have h1 : SectionLayout.apply
      (⟨h.layout.start, h.layout.instrSize, h.layout.instrSize_pos⟩ : ElfSectionLayout) h.prog =
      ⟨(@NativeRustcArm.Host.exe h).startAddr, (@NativeRustcArm.Host.exe h).program⟩ := by
    have he := SectionLayout.apply_toExecutable
      (⟨h.layout.start, h.layout.instrSize, h.layout.instrSize_pos⟩ : ElfSectionLayout) h.prog
    cases he
    rfl
  change MultiExecutable.mk [SectionLayout.apply _ h.prog] =
    MultiExecutable.mk [⟨(@NativeRustcArm.Host.exe h).startAddr, (@NativeRustcArm.Host.exe h).program⟩]
  rw [h1]

theorem toElfHost_labels (h : NativeRustcArm.Host) :
    @instLabelsElfHost (Host.toElfHost h) = Executable.labels (@NativeRustcArm.Host.exe h) := by
  change ElfExecutable.labels (@ElfHost.exe (Host.toElfHost h)) =
    Executable.labels (@NativeRustcArm.Host.exe h)
  rw [toElfHost_exe, ElfExecutable.labels, Executable.labels, toMultiExecutable_withAddresses]

theorem toElfHost_addrOf (h : NativeRustcArm.Host) (k : Nat) :
    @ElfHost.addrOf (Host.toElfHost h) 0 k = @NativeRustcArm.Host.addrOf h k := by
  simp only [ElfHost.addrOf, ElfHost.sectionAt, toElfHost_exe, toMultiExecutable,
    List.getElem?_cons_zero, Option.getD_some, Section.addrOf, Section.toExecutable,
    NativeRustcArm.Host.addrOf]

theorem elfStep1_toElfHost (h : NativeRustcArm.Host) :
    @elfStep1 (@instLabelsElfHost (Host.toElfHost h)) (@ElfHost.exe (Host.toElfHost h)) =
      @step1 h.layout (@NativeRustcArm.Host.exe h) := by
  funext s post
  rw [toElfHost_labels, toElfHost_exe]
  simp only [elfStep1, step1, ElfExecutable.step, Executable.step,
    toMultiExecutable_directivesAtAddress]

end

end NativeRustcArm
