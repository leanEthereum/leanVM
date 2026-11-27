module

public import NativeRustc.MultiLayout

/-!
# Generic helpers for instantiating `ElfHost` on real linked ELF binaries

Provides arch-independent lemmas that discharge the three structural obligations of a concrete
multi-section `ElfHost` witness:
1. `section_addr_determines_offset_of_noWrap`: no-wrap interval bound implies `addr_determines_offset`.
2. `sections_disjoint_of_intervals`: pairwise-disjoint `[base, base + totalSize)` intervals with
   positive-size trailing directives imply `sections_disjoint` (even with 0-byte gaps between
   adjacent sections).
3. `findSome?_label_of_nodup`: distinct label names across all sections imply every `.label l`
   resolves to its exact section-computed address `sec.addrOf j` (giving `PlacedIn` and `.rodata`
   label equations in one kernel `Nodup` check).
-/

namespace NativeRustc.ElfWitness

open Kraken NativeRustc.MultiLayout

@[expose] public section

/-- Extract the label name if a directive is `.label`. -/
def labelOf {Instr Const : Type} : Directive Instr Const → Option Label
  | .label l => some l
  | _ => none

/-- All label names across a list of section programs, in section order. -/
def allLabels {Instr Const : Type} (progs : List (Program Instr Const)) : List Label :=
  (progs.flatMap id).filterMap labelOf

/-- Injective encoding of bytes as a `Nat` (base 257, digits `b + 1`) for fast kernel `Nodup`. -/
def encBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 1 + 257 * encBytes bs

/-- Injective encoding of a `Label` as a `Nat`. -/
def labelKey (s : Label) : Nat := encBytes s.toByteArray.data.toList

/-- Balanced radix-2 tree of `Nat`s for O(log N) kernel instruction-size lookup. -/
inductive NatTree where
  | leaf (v : Nat)
  | node (l r : NatTree)

/-- Lookup index `n` in a `NatTree` (O(log N) steps in the Lean kernel). -/
def NatTree.get : NatTree → Nat → Nat
  | .leaf v, _ => v
  | .node l r, n => if n % 2 == 0 then l.get (n / 2) else r.get (n / 2)

/-- Split a list into even-indexed and odd-indexed elements in one linear pass. -/
def splitEvenOdd {α : Type _} (xs : List α) : List α × List α :=
  xs.foldr (fun x (e, o) => (x :: o, e)) ([], [])

/-- Build a `NatTree` of depth at most `fuel` from a list of `Nat`s (pure `List`, no `Array`). -/
def NatTree.ofListAux : Nat → List Nat → NatTree
  | 0, xs => .leaf (xs.headD 1)
  | _ + 1, [] => .leaf 1
  | _ + 1, [v] => .leaf v
  | fuel + 1, xs =>
    let (evens, odds) := splitEvenOdd xs
    .node (ofListAux fuel evens) (ofListAux fuel odds)

/-- Build a `NatTree` supporting up to `2^16` directives. -/
def NatTree.ofList (xs : List Nat) : NatTree :=
  NatTree.ofListAux 16 xs

/-- Align a list of per-instruction byte sizes to directive indices (pure `List`, no `Array`). -/
def instrSizeList {Instr Const : Type} : Program Instr Const → List Nat → List Nat
  | [], _ => []
  | .instr _ :: ds, s :: ss => max 1 s :: instrSizeList ds ss
  | .instr _ :: ds, [] => 1 :: instrSizeList ds []
  | _ :: ds, ss => 1 :: instrSizeList ds ss

/-- Linear-time indexed sum over a list (avoids `List.mapIdx` / `Array.push` in the kernel). -/
def sumIdx {α : Type _} (g : Nat → α → Nat) : List α → Nat → Nat → Nat
  | [], _, acc => acc
  | a :: as, i, acc => sumIdx g as (i + 1) (acc + g i a)

/-- Total byte size of a laid-out section. -/
def sectionTotalSize {Instr Const : Type} (s : Section Instr Const) : Nat :=
  s.sizeBefore s.program.length

/-- Whether the last directive of a non-empty section has positive size. -/
def sectionEndsPositive {Instr Const : Type} (s : Section Instr Const) : Bool :=
  match s.program.getLast? with
  | some c => decide (0 < c.size)
  | none => false

/-- Whether the last directive of `prog` under layout `l` has positive size (no `List.mapIdx`). -/
def progEndsPositive {Instr Const : Type} (l : SectionLayout Instr Const)
    (prog : Program Instr Const) : Bool :=
  match prog.getLast? with
  | some d => decide (0 < l.size d (prog.length - 1))
  | none => false

/-- Precompute `(baseAddr, totalByteSize, endsPositive)` once per section in linear time. -/
def sectionBounds {Instr Const : Type}
    (secs : List (Program Instr Const × SectionLayout Instr Const)) :
    List (Nat × Nat × Bool) :=
  secs.map fun (p, l) =>
    (l.start.toBitVec.toNat, sumIdx (fun i d => l.size d i) p 0 0, progEndsPositive l p)

/-- Check no-wrap, positive-size end, and pairwise disjoint `[base, base + total)` on precomputed bounds. -/
def boundsOk (bs : List (Nat × Nat × Bool)) : Bool :=
  bs.all (fun (b, t, ep) => decide (b + t < 2 ^ 64) && ep) &&
  (List.range bs.length).all fun i =>
    (List.range bs.length).all fun j =>
      if i == j then true
      else
        match bs[i]?, bs[j]? with
        | some (b₁, t₁, _), some (b₂, t₂, _) => decide (b₁ + t₁ ≤ b₂ ∨ b₂ + t₂ ≤ b₁)
        | _, _ => true

/-- Check that every section's `[base, base + total)` fits strictly below `2^64` and ends positive. -/
def sectionsNoWrap {Instr Const : Type} (secs : List (Section Instr Const)) : Bool :=
  secs.all fun s =>
    decide (s.startAddr.toBitVec.toNat + sectionTotalSize s < 2 ^ 64) && sectionEndsPositive s

/-- Check that distinct sections have pairwise disjoint `[base, base + total)` intervals. -/
def intervalsDisjoint {Instr Const : Type} (secs : List (Section Instr Const)) : Bool :=
  (List.range secs.length).all fun i =>
    (List.range secs.length).all fun j =>
      if i == j then true
      else
        match secs[i]?, secs[j]? with
        | some s₁, some s₂ =>
          let b₁ := s₁.startAddr.toBitVec.toNat
          let t₁ := sectionTotalSize s₁
          let b₂ := s₂.startAddr.toBitVec.toNat
          let t₂ := sectionTotalSize s₂
          decide (b₁ + t₁ ≤ b₂ ∨ b₂ + t₂ ≤ b₁)
        | _, _ => true

end

public section

theorem encBytes_inj : ∀ {l l' : List UInt8}, encBytes l = encBytes l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [encBytes] at h; omega
  | _ :: _, [], h => by simp only [encBytes] at h; omega
  | b :: bs, b' :: bs', h => by
    simp only [encBytes] at h
    have hb := b.toNat_lt
    have hb' := b'.toNat_lt
    have h1 : b.toNat = b'.toNat := by omega
    have h2 : encBytes bs = encBytes bs' := by omega
    rw [UInt8.toNat_inj.mp h1, encBytes_inj h2]

theorem labelKey_inj {s t : Label} (h : labelKey s = labelKey t) : s = t := by
  have hd : s.toByteArray.data = t.toByteArray.data := Array.toList_inj.mp (encBytes_inj h)
  apply String.toByteArray_inj.mp
  calc s.toByteArray = ⟨s.toByteArray.data⟩ := rfl
    _ = ⟨t.toByteArray.data⟩ := by rw [hd]
    _ = t.toByteArray := rfl

theorem nodup_of_labelKeys {L : List Label} (h : (L.map labelKey).Nodup) : L.Nodup :=
  List.Pairwise.of_map labelKey (fun _ _ hk he => hk (congrArg labelKey he)) h

theorem sizeBefore_le_total {Instr Const : Type} (s : Section Instr Const) (j : Nat) :
    s.sizeBefore j ≤ sectionTotalSize s := by
  by_cases h : j ≤ s.program.length
  · exact Executable.sizeBefore_mono s.toExecutable h
  · have hge : s.program.length ≤ j := Nat.le_of_not_le h
    unfold sectionTotalSize Section.sizeBefore Executable.sizeBefore Section.toExecutable
    simp only [List.take_of_length_le hge, List.take_length]
    exact Nat.le_refl _

theorem sizeBefore_lt_total_of_endsPositive {Instr Const : Type} (s : Section Instr Const)
    (hend : sectionEndsPositive s = true) {j : Nat} (hj : j < s.program.length) :
    s.sizeBefore j < sectionTotalSize s := by
  unfold sectionEndsPositive at hend
  cases hlast : s.program.getLast? with
  | none => simp [hlast] at hend
  | some c =>
    simp only [hlast, decide_eq_true_eq] at hend
    have hne : s.program ≠ [] := by
      intro heq; simp [heq] at hlast
    have hlen : 0 < s.program.length := by
      cases hp : s.program with
      | nil => exact (hne hp).elim
      | cons _ _ => simp
    have hgetLast : s.program[s.program.length - 1]? = some c := by
      rw [List.getElem?_eq_getElem (by omega)]
      have hl := List.getLast?_eq_some_getLast hne
      rw [hlast, Option.some.injEq] at hl
      rw [hl, List.getLast_eq_getElem]
    have hsucc : s.sizeBefore s.program.length = s.sizeBefore (s.program.length - 1) + c.size := by
      have := Executable.sizeBefore_succ s.toExecutable (n := s.program.length - 1) hgetLast
      have heq : s.program.length - 1 + 1 = s.program.length := by omega
      simpa [Section.sizeBefore, heq] using this
    have hmono : s.sizeBefore j ≤ s.sizeBefore (s.program.length - 1) :=
      Executable.sizeBefore_mono s.toExecutable (by omega)
    unfold sectionTotalSize
    omega

theorem int64_add_ofNat_toNat_eq {a : Int64} {n : Nat}
    (hlt : a.toBitVec.toNat + n < 2 ^ 64) :
    (a + Int64.ofNat n).toBitVec.toNat = a.toBitVec.toNat + n := by
  have h1 : (a + Int64.ofNat n).toBitVec = a.toBitVec + BitVec.ofNat 64 n := rfl
  rw [h1, BitVec.toNat_add, BitVec.toNat_ofNat]
  have hn : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hlt]

/-- If `start + totalSize < 2^64`, then addresses inside section `s` uniquely determine offsets. -/
theorem section_addr_determines_offset_of_noWrap {Instr Const : Type} (s : Section Instr Const)
    (hno : s.startAddr.toBitVec.toNat + sectionTotalSize s < 2 ^ 64) (j k : Nat)
    (haddr : s.addrOf j = s.addrOf k) : s.sizeBefore j = s.sizeBefore k := by
  have hj := sizeBefore_le_total s j
  have hk := sizeBefore_le_total s k
  have h1 := congrArg (fun x : Int64 => x.toBitVec.toNat) haddr
  change (s.startAddr + Int64.ofNat (s.sizeBefore j)).toBitVec.toNat =
    (s.startAddr + Int64.ofNat (s.sizeBefore k)).toBitVec.toNat at h1
  rw [int64_add_ofNat_toNat_eq (by omega), int64_add_ofNat_toNat_eq (by omega)] at h1
  omega

/-- Disjoint `[base, base + total)` intervals with no-wrap and positive-size ends imply
`sections_disjoint`. -/
theorem sections_disjoint_of_intervals {Instr Const : Type} (secs : List (Section Instr Const))
    (hno : sectionsNoWrap secs = true) (hdisj : intervalsDisjoint secs = true)
    {s₁ : Nat} (h₁ : s₁ < secs.length) {s₂ : Nat} (h₂ : s₂ < secs.length) (hne : s₁ ≠ s₂)
    {j₁ : Nat} (hj₁ : j₁ < secs[s₁].program.length)
    {j₂ : Nat} (hj₂ : j₂ < secs[s₂].program.length) :
    secs[s₁].addrOf j₁ ≠ secs[s₂].addrOf j₂ := by
  have hall := List.all_eq_true.mp hno
  have hno₁ := hall secs[s₁] (List.getElem_mem h₁)
  have hno₂ := hall secs[s₂] (List.getElem_mem h₂)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hno₁ hno₂
  have hd1 := List.all_eq_true.mp hdisj s₁ (List.mem_range.mpr h₁)
  have hd2 := List.all_eq_true.mp hd1 s₂ (List.mem_range.mpr h₂)
  have hbeq : (s₁ == s₂) = false := beq_false_of_ne hne
  simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂, decide_eq_true_eq] at hd2
  have hlt₁ := sizeBefore_lt_total_of_endsPositive secs[s₁] hno₁.2 hj₁
  have hlt₂ := sizeBefore_lt_total_of_endsPositive secs[s₂] hno₂.2 hj₂
  intro heq
  have hnat := congrArg (fun x : Int64 => x.toBitVec.toNat) heq
  change (secs[s₁].startAddr + Int64.ofNat (secs[s₁].sizeBefore j₁)).toBitVec.toNat =
    (secs[s₂].startAddr + Int64.ofNat (secs[s₂].sizeBefore j₂)).toBitVec.toNat at hnat
  rw [int64_add_ofNat_toNat_eq (by omega), int64_add_ofNat_toNat_eq (by omega)] at hnat
  omega

private theorem findSome?_label_eq_of_mem_nodup {Instr Const : Type}
    [DecidableEq Instr] [DecidableEq Const]
    (L : List (Addressable (Directive Instr Const)))
    (hnodup : (L.filterMap (fun x => labelOf x.directive)).Nodup)
    {x : Addressable (Directive Instr Const)} (hx : x ∈ L) {l : Label}
    (hl : x.directive = .label l) :
    L.findSome? (fun y => if y.directive = .label l then some y.addr else none) = some x.addr := by
  induction L with
  | nil => cases hx
  | cons y rest ih =>
    simp only [List.findSome?_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · simp [hl]
    · cases hyd : y.directive with
      | label ly =>
        simp only [List.filterMap_cons, hyd, labelOf, List.nodup_cons] at hnodup
        have hmemL : l ∈ rest.filterMap (fun z => labelOf z.directive) :=
          List.mem_filterMap.mpr ⟨x, hmem, by rw [hl]; rfl⟩
        have hne : ly ≠ l := fun heq => hnodup.1 (heq ▸ hmemL)
        have hfalse : ¬ (Directive.label (Instr := Instr) (Const := Const) ly = .label l) :=
          fun h => hne (Directive.label.inj h)
        simp only [hfalse, ↓reduceIte]
        exact ih hnodup.2 hmem
      | instr _ =>
        simp only [List.filterMap_cons, hyd, labelOf] at hnodup
        simp only [reduceCtorEq, ↓reduceIte]
        exact ih hnodup hmem
      | byteArray _ =>
        simp only [List.filterMap_cons, hyd, labelOf] at hnodup
        simp only [reduceCtorEq, ↓reduceIte]
        exact ih hnodup hmem
      | word _ _ =>
        simp only [List.filterMap_cons, hyd, labelOf] at hnodup
        simp only [reduceCtorEq, ↓reduceIte]
        exact ih hnodup hmem

theorem section_withAddresses_filterMap_labelOf {Instr Const : Type}
    (l : SectionLayout Instr Const) (prog : Program Instr Const) :
    (l.apply prog).withAddresses.filterMap (fun x => labelOf x.directive) =
      prog.filterMap labelOf := by
  have hmap : (l.apply prog).withAddresses.map (·.directive) = prog := by
    apply List.ext_getElem
    · have hlen := congrArg List.length
        (Executable.withAddresses_map_snd (l.apply prog).program (l.apply prog).startAddr)
      simp only [Section.withAddresses, Section.toExecutable, List.length_map] at hlen ⊢
      rw [hlen, SectionLayout.apply, List.length_mapIdx]
    · intro i h1 h2
      simp only [List.getElem_map]
      have h1' : i < (l.apply prog).toExecutable.withAddresses.length := by
        simpa [List.length_map, Section.withAddresses] using h1
      have hget := Executable.getElem?_withAddresses_eq (l.apply prog).toExecutable i
      rw [List.getElem?_eq_getElem h1'] at hget
      have hprog : (l.apply prog).toExecutable.program[i]? = some ⟨prog[i], l.size prog[i] i⟩ := by
        change (l.apply prog).program[i]? = _
        rw [SectionLayout.apply_getElem?, List.getElem?_eq_getElem h2]; rfl
      rw [hprog] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      change ((l.apply prog).toExecutable.withAddresses[i]).directive = prog[i]
      rw [hget]
  calc (l.apply prog).withAddresses.filterMap (fun x => labelOf x.directive)
      = ((l.apply prog).withAddresses.map (·.directive)).filterMap labelOf := by
        rw [List.filterMap_map]; rfl
    _ = prog.filterMap labelOf := by rw [hmap]

theorem multi_withAddresses_filterMap_labelOf {Instr Const : Type}
    (secs : List (Program Instr Const × SectionLayout Instr Const)) :
    (MultiExecutable.mk (secs.map fun (p, l) => l.apply p)).withAddresses.filterMap
        (fun x => labelOf x.directive) =
      allLabels (secs.map Prod.fst) := by
  unfold MultiExecutable.withAddresses allLabels
  rw [List.filterMap_flatMap, List.flatMap_map, List.flatMap_map, List.filterMap_flatMap]
  simp only [id_eq]
  congr 1
  funext ⟨p, l⟩
  exact section_withAddresses_filterMap_labelOf l p

/-- When all labels across `secs` are distinct (`Nodup`), every `.label l` in section `sec` at
offset `j` resolves to `sec.addrOf j`. -/
theorem findSome?_label_of_nodup {Instr Const : Type}
    [DecidableEq Instr] [DecidableEq Const]
    (secs : List (Program Instr Const × SectionLayout Instr Const))
    (hnodup : (allLabels (secs.map Prod.fst)).Nodup)
    {sec j : Nat} (hsec : sec < secs.length) (hj : j < secs[sec].1.length) {l : Label}
    (hl : secs[sec].1[j] = .label l) :
    let me : MultiExecutable Instr Const := ⟨secs.map fun (p, l) => l.apply p⟩
    (me.withAddresses.findSome? (fun y => if y.directive = .label l then some y.addr else none)).getD (-1) =
      (secs[sec].2.apply secs[sec].1).addrOf j := by
  dsimp only
  let me : MultiExecutable Instr Const := ⟨secs.map fun (p, l) => l.apply p⟩
  have hnodup' : (me.withAddresses.filterMap (fun x => labelOf x.directive)).Nodup := by
    rw [multi_withAddresses_filterMap_labelOf]; exact hnodup
  let s := secs[sec].2.apply secs[sec].1
  have hj_prog : j < s.program.length := by
    simp only [s, SectionLayout.apply, List.length_mapIdx]; exact hj
  have hlen : s.withAddresses.length = s.program.length := by
    have := congrArg List.length (Executable.withAddresses_map_snd s.program s.startAddr)
    simpa [Section.withAddresses, Section.toExecutable] using this
  have hj_wa : j < s.withAddresses.length := by rw [hlen]; exact hj_prog
  have hj_wa' : j < s.toExecutable.withAddresses.length := hj_wa
  have hget := Executable.getElem?_withAddresses_eq s.toExecutable j
  rw [List.getElem?_eq_getElem hj_wa'] at hget
  have hprog : s.toExecutable.program[j]? = some ⟨.label l, secs[sec].2.size (.label l) j⟩ := by
    change (secs[sec].2.apply secs[sec].1).program[j]? = _
    rw [SectionLayout.apply_getElem?, List.getElem?_eq_getElem hj, hl]; rfl
  rw [hprog] at hget
  simp only [Option.map_some, Option.some.injEq] at hget
  have hmem_s : s ∈ me.sections := List.mem_map.mpr ⟨secs[sec], List.getElem_mem hsec, rfl⟩
  have hmem_x : s.withAddresses[j] ∈ me.withAddresses :=
    List.mem_flatMap.mpr ⟨s, hmem_s, List.getElem_mem hj_wa⟩
  have hdir : s.withAddresses[j].directive = .label l := by
    change (s.toExecutable.withAddresses[j]).directive = .label l
    rw [hget]
  have haddr : s.withAddresses[j].addr = s.addrOf j := by
    change (s.toExecutable.withAddresses[j]).addr = s.addrOf j
    rw [hget]; rfl
  rw [findSome?_label_eq_of_mem_nodup me.withAddresses hnodup' hmem_x hdir, Option.getD_some, haddr]

theorem sumIdx_eq {α : Type _} (g : Nat → α → Nat) (l : List α) (i acc : Nat) :
    sumIdx g l i acc = acc + (l.mapIdx (fun j a => g (i + j) a)).sum := by
  induction l generalizing i acc with
  | nil => simp [sumIdx]
  | cons a as ih =>
    simp only [sumIdx, List.mapIdx_cons, List.sum_cons, Nat.add_zero]
    rw [ih (i + 1) (acc + g i a)]
    have hfn : (fun j x => g (i + 1 + j) x) = (fun j x => g (i + (j + 1)) x) := by
      funext j x; congr 1; omega
    rw [hfn]
    omega

theorem sectionTotalSize_apply {Instr Const : Type} (l : SectionLayout Instr Const)
    (prog : Program Instr Const) :
    sectionTotalSize (l.apply prog) = sumIdx (fun i d => l.size d i) prog 0 0 := by
  rw [sumIdx_eq, Nat.zero_add]
  unfold sectionTotalSize Section.sizeBefore Executable.sizeBefore Section.toExecutable SectionLayout.apply
  rw [List.take_length]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem sectionEndsPositive_apply {Instr Const : Type} (l : SectionLayout Instr Const)
    (prog : Program Instr Const) :
    sectionEndsPositive (l.apply prog) = progEndsPositive l prog := by
  unfold sectionEndsPositive progEndsPositive
  cases hp : prog with
  | nil => simp [SectionLayout.apply]
  | cons d ds =>
    have hne : (d :: ds) ≠ [] := List.cons_ne_nil d ds
    have hne' : (l.apply (d :: ds)).program ≠ [] := by
      simp [SectionLayout.apply]
    rw [List.getLast?_eq_some_getLast hne, List.getLast?_eq_some_getLast hne']
    have hlast : (l.apply (d :: ds)).program.getLast hne' =
        ⟨(d :: ds).getLast hne, l.size ((d :: ds).getLast hne) ((d :: ds).length - 1)⟩ := by
      rw [List.getLast_eq_getElem, List.getLast_eq_getElem]
      have hlen : (l.apply (d :: ds)).program.length = (d :: ds).length := by
        simp [SectionLayout.apply]
      have hidx : (d :: ds).length - 1 < (d :: ds).length := by simp
      have hget := SectionLayout.apply_getElem? l (d :: ds) ((d :: ds).length - 1)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hidx] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      simpa [hlen] using hget
    rw [hlast]

/-- `boundsOk` on `sectionBounds secs` implies `addr_determines_offset` for every section. -/
theorem boundsOk_addr_determines_offset {Instr Const : Type}
    (secs : List (Program Instr Const × SectionLayout Instr Const))
    (hok : boundsOk (sectionBounds secs) = true)
    (sec : Nat) (hs : sec < secs.length) (j k : Nat) :
    let s := secs[sec].2.apply secs[sec].1
    s.addrOf j = s.addrOf k → s.sizeBefore j = s.sizeBefore k := by
  dsimp only
  simp only [boundsOk, Bool.and_eq_true] at hok
  have hall := List.all_eq_true.mp hok.1
  have hmem : (secs[sec].2.start.toBitVec.toNat,
      sumIdx (fun i d => secs[sec].2.size d i) secs[sec].1 0 0,
      progEndsPositive secs[sec].2 secs[sec].1) ∈ sectionBounds secs :=
    List.mem_map.mpr ⟨secs[sec], List.getElem_mem hs, rfl⟩
  have hsecOk := hall _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsecOk
  have hno : (secs[sec].2.apply secs[sec].1).startAddr.toBitVec.toNat +
      sectionTotalSize (secs[sec].2.apply secs[sec].1) < 2 ^ 64 := by
    rw [sectionTotalSize_apply]
    exact hsecOk.1
  exact section_addr_determines_offset_of_noWrap _ hno j k

/-- `boundsOk` on `sectionBounds secs` implies `sections_disjoint`. -/
theorem boundsOk_disjoint {Instr Const : Type}
    (secs : List (Program Instr Const × SectionLayout Instr Const))
    (hok : boundsOk (sectionBounds secs) = true)
    (s₁ : Nat) (h₁ : s₁ < secs.length) (s₂ : Nat) (h₂ : s₂ < secs.length) (hne : s₁ ≠ s₂)
    (j₁ : Nat) (hj₁ : j₁ < secs[s₁].1.length) (j₂ : Nat) (hj₂ : j₂ < secs[s₂].1.length) :
    (secs[s₁].2.apply secs[s₁].1).addrOf j₁ ≠ (secs[s₂].2.apply secs[s₂].1).addrOf j₂ := by
  simp only [boundsOk, Bool.and_eq_true] at hok
  have hall := List.all_eq_true.mp hok.1
  have hb₁ := hall _ (List.mem_map.mpr ⟨secs[s₁], List.getElem_mem h₁, rfl⟩)
  have hb₂ := hall _ (List.mem_map.mpr ⟨secs[s₂], List.getElem_mem h₂, rfl⟩)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb₁ hb₂
  have hlenB : (sectionBounds secs).length = secs.length := by simp [sectionBounds]
  have hd1 := List.all_eq_true.mp hok.2 s₁ (List.mem_range.mpr (by omega))
  have hd2 := List.all_eq_true.mp hd1 s₂ (List.mem_range.mpr (by omega))
  have hbeq : (s₁ == s₂) = false := beq_false_of_ne hne
  have hg₁ : (sectionBounds secs)[s₁]? = some (secs[s₁].2.start.toBitVec.toNat,
      sumIdx (fun i d => secs[s₁].2.size d i) secs[s₁].1 0 0,
      progEndsPositive secs[s₁].2 secs[s₁].1) := by
    rw [List.getElem?_eq_getElem (by omega)]; simp [sectionBounds]
  have hg₂ : (sectionBounds secs)[s₂]? = some (secs[s₂].2.start.toBitVec.toNat,
      sumIdx (fun i d => secs[s₂].2.size d i) secs[s₂].1 0 0,
      progEndsPositive secs[s₂].2 secs[s₂].1) := by
    rw [List.getElem?_eq_getElem (by omega)]; simp [sectionBounds]
  simp only [hbeq, Bool.false_eq_true, ↓reduceIte, hg₁, hg₂, decide_eq_true_eq] at hd2
  let sec₁ := secs[s₁].2.apply secs[s₁].1
  let sec₂ := secs[s₂].2.apply secs[s₂].1
  have ht₁ : sectionTotalSize sec₁ = sumIdx (fun i d => secs[s₁].2.size d i) secs[s₁].1 0 0 :=
    sectionTotalSize_apply _ _
  have ht₂ : sectionTotalSize sec₂ = sumIdx (fun i d => secs[s₂].2.size d i) secs[s₂].1 0 0 :=
    sectionTotalSize_apply _ _
  have hep₁ : sectionEndsPositive sec₁ = true := by rw [sectionEndsPositive_apply]; exact hb₁.2
  have hep₂ : sectionEndsPositive sec₂ = true := by rw [sectionEndsPositive_apply]; exact hb₂.2
  have hlt₁ := sizeBefore_lt_total_of_endsPositive sec₁ hep₁ (by simpa [sec₁, SectionLayout.apply] using hj₁)
  have hlt₂ := sizeBefore_lt_total_of_endsPositive sec₂ hep₂ (by simpa [sec₂, SectionLayout.apply] using hj₂)
  intro heq
  have hnat := congrArg (fun x : Int64 => x.toBitVec.toNat) heq
  change (sec₁.startAddr + Int64.ofNat (sec₁.sizeBefore j₁)).toBitVec.toNat =
    (sec₂.startAddr + Int64.ofNat (sec₂.sizeBefore j₂)).toBitVec.toNat at hnat
  have hstart₁ : sec₁.startAddr = secs[s₁].2.start := rfl
  have hstart₂ : sec₂.startAddr = secs[s₂].2.start := rfl
  rw [hstart₁, hstart₂] at hnat
  rw [int64_add_ofNat_toNat_eq (by omega), int64_add_ofNat_toNat_eq (by omega)] at hnat
  omega

end

end NativeRustc.ElfWitness
