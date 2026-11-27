module

public import Kraken.Layout

/-!
# Multi-section ELF-compatible executable layout

Generalizes Kraken's single-list `Executable` to a `MultiExecutable` consisting of independently
placed `Section`s, each with its own 64-bit `startAddr` and `SectionLayout`. Real multi-section ELF
binaries with separate `.text` and `.rodata` segments, section reordering, and inter-symbol
alignment padding instantiate `MultiExecutable` directly without forcing a flat directive list.
-/

namespace NativeRustc.MultiLayout

open Kraken

@[expose] public section

/-- One contiguous section (for example, a function in `.text` or a symbol in `.rodata`)
placed at an independent 64-bit base address. -/
structure Section (Instr Const : Type) where
  startAddr : Int64
  program : List (Sized (Directive Instr Const))

/-- View a single section as a Kraken `Executable` so all `Kraken.Executable` lemmas apply. -/
def Section.toExecutable {Instr Const : Type} (s : Section Instr Const) : Executable Instr Const :=
  ⟨s.startAddr, s.program⟩

/-- Per-section instruction size assignment (same contract as `Kraken.Layout`). -/
structure SectionLayout (Instr Const : Type) where
  start : Int64
  instrSize : Nat → Nat
  instrSize_pos : ∀ i, 0 < instrSize i

/-- Size of directive `d` at index `idx` within a section. -/
def SectionLayout.size {Instr Const : Type} (l : SectionLayout Instr Const) :
    Directive Instr Const → Nat → Nat
  | .instr _, idx => l.instrSize idx
  | .label _, _ => 0
  | .byteArray arr, _ => arr.size
  | .word bytes _, _ => bytes

/-- Apply a `SectionLayout` to a section's directive list. -/
def SectionLayout.apply {Instr Const : Type} (l : SectionLayout Instr Const)
    (prog : Program Instr Const) : Section Instr Const :=
  { startAddr := l.start
    program := prog.mapIdx fun idx d => { directive := d, size := l.size d idx } }

/-- Convert a `SectionLayout` to a `Kraken.Layout`. -/
@[instance_reducible]
def SectionLayout.toKrakenLayout {Instr Const : Type} (l : SectionLayout Instr Const) :
    Layout Instr Const :=
  { start := l.start, instrSize := l.instrSize, instrSize_pos := l.instrSize_pos }

/-- Sum of sizes of the first `n` directives in section `s`. -/
def Section.sizeBefore {Instr Const : Type} (s : Section Instr Const) (n : Nat) : Nat :=
  s.toExecutable.sizeBefore n

/-- Address of the `n`-th directive in section `s` (for `n = s.program.length`, the section end). -/
def Section.addrOf {Instr Const : Type} (s : Section Instr Const) (n : Nat) : Int64 :=
  s.toExecutable.addrOf n

/-- Each directive of section `s` paired with its start address. -/
def Section.withAddresses {Instr Const : Type} (s : Section Instr Const) :
    List (Addressable (Directive Instr Const)) :=
  s.toExecutable.withAddresses

/-- Directives of section `s` starting at address `a`. -/
def Section.directivesAtAddress {Instr Const : Type} (s : Section Instr Const) (a : Int64) :
    List (Sized (Directive Instr Const)) :=
  s.toExecutable.directivesAtAddress a

/-- A multi-section executable whose sections sit at independent 64-bit addresses. -/
structure MultiExecutable (Instr Const : Type) where
  sections : List (Section Instr Const)

/-- All directives of a `MultiExecutable` paired with their section-computed addresses. -/
def MultiExecutable.withAddresses {Instr Const : Type} (me : MultiExecutable Instr Const) :
    List (Addressable (Directive Instr Const)) :=
  me.sections.flatMap Section.withAddresses

/-- All directives of a `MultiExecutable` starting at address `a`. -/
def MultiExecutable.directivesAtAddress {Instr Const : Type} (me : MultiExecutable Instr Const)
    (a : Int64) : List (Sized (Directive Instr Const)) :=
  me.sections.flatMap (·.directivesAtAddress a)

/-- Embed a single-section Kraken `Executable` into a 1-section `MultiExecutable`. -/
def toMultiExecutable {Instr Const : Type} (e : Executable Instr Const) :
    MultiExecutable Instr Const :=
  { sections := [⟨e.startAddr, e.program⟩] }

end

public section

theorem SectionLayout.apply_toExecutable {Instr Const : Type} (l : SectionLayout Instr Const)
    (prog : Program Instr Const) :
    (l.apply prog).toExecutable = l.toKrakenLayout.apply prog := by
  simp only [Section.toExecutable, SectionLayout.apply, Layout.apply]
  congr 1

theorem SectionLayout.apply_getElem? {Instr Const : Type} (l : SectionLayout Instr Const)
    (prog : Program Instr Const) (i : Nat) :
    (l.apply prog).program[i]? = prog[i]?.map fun d => { directive := d, size := l.size d i } := by
  simp [SectionLayout.apply, List.getElem?_mapIdx]

theorem Section.addrOf_succ {Instr Const : Type} {l : SectionLayout Instr Const}
    {prog : Program Instr Const} {k : Nat} {d : Directive Instr Const} (hd : prog[k]? = some d) :
    (l.apply prog).addrOf (k + 1) = (l.apply prog).addrOf k + .ofNat (l.size d k) :=
  Executable.addrOf_succ _ (c := { directive := d, size := l.size d k })
    (by rw [Section.toExecutable, SectionLayout.apply_getElem?, hd]; rfl)

private theorem dropWhile_eq_nil_of_all {α : Type _} {p : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = true) → l.dropWhile p = []
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.dropWhile_cons, h x List.mem_cons_self, ↓reduceIte]
    exact dropWhile_eq_nil_of_all l fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem Section.directivesAtAddress_eq_nil_of_ne {Instr Const : Type}
    (s : Section Instr Const) (a : Int64)
    (hne : ∀ j < s.program.length, s.addrOf j ≠ a) :
    s.directivesAtAddress a = [] := by
  unfold Section.directivesAtAddress Executable.directivesAtAddress
  have hdrop : s.toExecutable.withAddresses.dropWhile (·.addr ≠ a) = [] := by
    apply dropWhile_eq_nil_of_all
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hget := Executable.getElem?_withAddresses_eq s.toExecutable j
    rw [List.getElem?_eq_getElem hj] at hget
    have hj' : j < s.toExecutable.program.length := by
      have hlen : s.toExecutable.withAddresses.length = s.toExecutable.program.length := by
        simpa [Section.toExecutable] using congrArg List.length
          (Executable.withAddresses_map_snd s.program s.startAddr)
      omega
    rw [List.getElem?_eq_getElem hj'] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    rw [hget]
    simpa [Section.addrOf] using hne j (by simpa [Section.toExecutable] using hj')
  rw [hdrop]
  rfl

theorem MultiExecutable.directivesAtAddress_eq_section {Instr Const : Type}
    (me : MultiExecutable Instr Const) {sec : Nat} (hsec : sec < me.sections.length) (a : Int64)
    (hdisj : ∀ s' (hs' : s' < me.sections.length), s' ≠ sec →
      ∀ j < me.sections[s'].program.length, me.sections[s'].addrOf j ≠ a) :
    me.directivesAtAddress a = me.sections[sec].directivesAtAddress a := by
  unfold MultiExecutable.directivesAtAddress
  have hsplit : me.sections =
      me.sections.take sec ++ [me.sections[sec]] ++ me.sections.drop (sec + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
  rw [congrArg (List.flatMap (·.directivesAtAddress a)) hsplit,
    List.flatMap_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hpre : (me.sections.take sec).flatMap (·.directivesAtAddress a) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    have hjlt : j < sec := by simp only [List.length_take] at hj; omega
    have hjlen : j < me.sections.length := by omega
    rw [List.getElem_take]
    exact Section.directivesAtAddress_eq_nil_of_ne _ a (hdisj j hjlen (by omega))
  have hsuf : (me.sections.drop (sec + 1)).flatMap (·.directivesAtAddress a) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    have hjlen : sec + 1 + j < me.sections.length := by simp only [List.length_drop] at hj; omega
    rw [List.getElem_drop]
    exact Section.directivesAtAddress_eq_nil_of_ne _ a (hdisj (sec + 1 + j) hjlen (by omega))
  rw [hpre, hsuf, List.nil_append, List.append_nil]

theorem toMultiExecutable_withAddresses {Instr Const : Type} (e : Executable Instr Const) :
    (toMultiExecutable e).withAddresses = e.withAddresses := by
  simp [toMultiExecutable, MultiExecutable.withAddresses, Section.withAddresses, Section.toExecutable]

theorem toMultiExecutable_directivesAtAddress {Instr Const : Type} (e : Executable Instr Const)
    (a : Int64) :
    (toMultiExecutable e).directivesAtAddress a = e.directivesAtAddress a := by
  simp [toMultiExecutable, MultiExecutable.directivesAtAddress, Section.directivesAtAddress,
    Section.toExecutable]

end

end NativeRustc.MultiLayout
