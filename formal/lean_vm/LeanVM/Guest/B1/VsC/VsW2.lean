/-
  LeanVM.Guest.B1.VsC.VsW2

  `verify_sub`'s window 2: the stream's first eight words, the announced sizes' buffer, the
  permutation absorbing them.
-/

module

public import LeanVM.Guest.B1.VsC.VsRun
public import LeanVM.Guest.B1.VsC.VsW1
public import LeanVM.Guest.B1.VsC.LeafA

/-!
# Window `2`

Statements `37 ..< 69` of `verify_sub` (`vsW2`): a `HeapBuf` of six words at `.n 56`, the stream's
words `0 ..< 8` loaded from its buffer at `.n 55`, words `1 ..< 7` stored into the new buffer, one
permutation over words `0 ..< 4`. `vsW2_segA`: on `vsVal rd0 w args`, the stream's buffer at `s`
and the new one at the cursor `a` (`hw55`, `hw56`), on the stream's words `ws` (`8 ≤ ws.length`)
that `rd0` and every memory of the window read at `s`, the latter holding words `1 ..< 7` at `a`,
the run is a window placing six words, its loads in `verify_sub`'s own data.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- Statements `37 ..< 69`. -/
def vsW2 : List Atom := [
    .hint (.alloc (.n 56) 6),
    .load (.n 57) (.n 55) 0,
    .copy (.n 58) (.n 57),
    .const (.n 59) (word 0 1),
    .load (.n 60) (.n 55) 1,
    .copy (.n 61) (.n 60),
    .const (.n 62) (word 0 1),
    .load (.n 60) (.n 56) 0,
    .load (.n 63) (.n 55) 2,
    .copy (.n 64) (.n 63),
    .const (.n 65) (word 0 1),
    .load (.n 63) (.n 56) 1,
    .load (.n 66) (.n 55) 3,
    .copy (.n 67) (.n 66),
    .const (.n 68) (word 0 1),
    .load (.n 66) (.n 56) 2,
    .keccak [.n 58, .n 59, .n 61, .n 62, .n 64, .n 65, .n 67, .n 68, .n 37, .n 38, .n 39, .n 40, .n 41] [.n 69, .n 70, .n 71, .n 72, .n 73, .n 74, .n 75, .n 76, .n 77, .n 78, .n 79, .n 80, .n 81] false false,
    .load (.n 82) (.n 55) 4,
    .copy (.n 83) (.n 82),
    .const (.n 84) (word 0 1),
    .load (.n 82) (.n 56) 3,
    .load (.n 85) (.n 55) 5,
    .copy (.n 86) (.n 85),
    .const (.n 87) (word 0 1),
    .load (.n 85) (.n 56) 4,
    .load (.n 88) (.n 55) 6,
    .copy (.n 89) (.n 88),
    .const (.n 90) (word 0 1),
    .load (.n 88) (.n 56) 5,
    .load (.n 91) (.n 55) 7,
    .copy (.n 92) (.n 91),
    .const (.n 93) (word 0 1)]

/-- The stream's words loaded: `(value, offset)`. -/
def vsW2ld : List (ℕ × ℕ) := [(57, 0), (60, 1), (63, 2), (66, 3), (82, 4), (85, 5), (88, 6), (91, 7)]

/-- The non-plain atoms: the loads from the stream, the stores into the new buffer. -/
def vsW2x : List Atom :=
  vsW2ld.map (fun q => .load (.n q.1) (.n 55) q.2) ++
    (vsW2ld.take 7).tail.map (fun q => .load (.n q.1) (.n 56) (q.2 - 1))

set_option maxRecDepth 100000 in
theorem vsW2_eq : (vsA.drop 37).take 32 = vsW2.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

theorem vsW2_ne : vsW2.all neB = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsW2_filter : ((vsW2.filter fun a => !plainOk a).all fun a => vsW2x.contains a) = true := by decide +kernel

theorem vsW2_offs : (vsW2ld.all fun q => decide (q.2 < 8)) = true ∧
    ((vsW2ld.take 7).tail.all fun q => decide (1 ≤ q.2 ∧ q.2 < 7)) = true ∧
    (vsW2ld.all fun q => vsW2.contains (.load (.n q.1) (.n 55) q.2)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsW2_facts : (vsW2ld.all fun q => (vsRcs.lookup (.n q.1)).isNone) = true ∧
    (vsRcs.lookup (.n 55)).isNone = true ∧ (vsRcs.lookup (.n 56)).isNone = true ∧
    (vsW2ld.all fun q => !(storesOf 6 vsAf).contains (.load (.n q.1) (.n 55) q.2)) = true := by
  decide +kernel

theorem vsW2_allocs (σ : Val) : allocs σ (vsW2.map Ev.atom) = [6] := rfl

theorem vsW2_allocDsts : allocDsts (vsW2.map Ev.atom) = [.n 56] := rfl

theorem vsW2_addrs : addrs (vsW2.map Ev.atom) = [] := rfl

theorem vsW2_hintAddrs (σ : Val) : heapHintAddrs σ (vsW2.map Ev.atom) = [] := rfl

/-- The loads' pointers and offsets. -/
theorem vsW2_loads : vsW2.all (fun a => match a with
    | .load _ p o => (p == .n 55 && decide (o < 8)) || (p == .n 56 && decide (o < 6))
    | _ => true) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **Window `2`**: statements `37 ..< 69`. -/
theorem vsW2_segA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader}
    {w : ℕ → E} {args : List E} (ha : args.length = 6) {s a fp kc : ℕ} (hw55 : w 55 = ptrAt s)
    (hw56 : w 56 = ptrAt a) (ws : List E) (hws : 8 ≤ ws.length) (h0 : ReadsAt rd0 (ptrAt s) ws)
    {Own R : ℕ → Prop} {Pre O : Reader → Prop} {D : ℕ → Prop} (hOs : ∀ j < 8, Own (s + j))
    (hOb : ∀ j < 6, Own (a + j))
    (hrd : ∀ rd, LowDef k rd → Pre rd → O rd →
      ReadsAt rd (ptrAt s) ws ∧ ReadsAt rd (ptrAt a) ((ws.drop 1).take 6)) :
    SegA (fs := fs) (al := al) (cert := cert) k "verify_sub" fp (vsVal rd0 w args) (rdOver (vsVal rd0 w args))
      Own R Pre (vsW2.map Stmt.atom) (vsW2.map Ev.atom) a (a + 6) kc kc O O D D [] := by
  set σ0 := vsVal rd0 w args with hσ0
  obtain ⟨fl, f55, f56, fS⟩ := vsW2_facts
  have r55 : vsRcs.lookup (.n 55) = none := Option.isNone_iff_eq_none.mp f55
  have r56 : vsRcs.lookup (.n 56) = none := Option.isNone_iff_eq_none.mp f56
  have rl : ∀ q ∈ vsW2ld, vsRcs.lookup (.n q.1) = none := fun q hq =>
    Option.isNone_iff_eq_none.mp (List.all_eq_true.mp fl q hq)
  have sl : ∀ q ∈ vsW2ld, Atom.load (.n q.1) (.n 55) q.2 ∉ storesOf 6 vsAf := fun q hq h => by
    have := List.all_eq_true.mp fS q hq
    rw [List.contains_iff_mem.mpr h] at this
    exact absurd this (by decide)
  have hg := vsA_run_good (rd0 := rd0) (w := w) ha vsW2_eq vsW2_ne
  have p55 : σ0 (.n 55) = ptrAt s := by rw [hσ0, vsVal_55 ha, hw55]
  have p56 : σ0 (.n 56) = ptrAt a := by
    rw [hσ0]; exact (hg (.hint (.alloc (.n 56) 6)) (by simp [vsW2])).trans hw56
  obtain ⟨o8, o7, om⟩ := vsW2_offs
  have hmem : ∀ q ∈ vsW2ld, Atom.load (.n q.1) (.n 55) q.2 ∈ vsW2 := fun q hq =>
    List.contains_iff_mem.mp (List.all_eq_true.mp om q hq)
  have hoff : ∀ q ∈ vsW2ld, q.2 < ws.length := fun q hq => by
    have := List.all_eq_true.mp o8 q hq; simp only [decide_eq_true_eq] at this; omega
  have val : ∀ q ∈ vsW2ld, ∀ h : q.2 < ws.length, σ0 (.n q.1) = ws[q.2] := fun q hq h =>
    good_loadAt (sl q hq) (hg _ (hmem q hq)) p55 h h0
  have hb : ((ws.drop 1).take 6).length = 6 := by simp; omega
  have hst : ∀ q ∈ (vsW2ld.take 7).tail, ∀ rd, ReadsAt rd (ptrAt a) ((ws.drop 1).take 6) →
      (Atom.load (.n q.1) (.n 56) (q.2 - 1)).Holds rd (rdOver σ0 rd) := by
    intro q hq rd h1
    have hq' : q ∈ vsW2ld := List.mem_of_mem_take (List.mem_of_mem_tail hq)
    have hq1 : 1 ≤ q.2 ∧ q.2 < 7 := by
      have := List.all_eq_true.mp o7 q hq; simpa only [decide_eq_true_eq] using this
    refine holds_storeAt (rl q hq') r56 p56 (by rw [hb]; omega) ?_ h1
    rw [val q hq' (hoff q hq')]
    have e : 1 + (q.2 - 1) = q.2 := by omega
    simp only [List.getElem_take, List.getElem_drop, e]
  refine segA_atoms fun rd hl hp ho => ⟨by rw [vsW2_allocs, vsW2_allocs], ?_,
    by intro q hq; rw [vsW2_addrs] at hq; simp at hq, ?_,
    by intro A hA; rw [vsW2_hintAddrs] at hA; simp at hA, ?_⟩
  · rw [vsW2_allocDsts, vsW2_allocs]
    simp only [List.map_cons, List.map_nil, rdOver_eq r56, p56, bases]
  · intro A hA
    obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA
    have hc := List.all_eq_true.mp vsW2_loads _ hm
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    rcases hc with ⟨rfl, ho'⟩ | ⟨rfl, ho'⟩
    · exact ⟨s + off, by rw [rdOver_eq r55, p55, ptrAt, B1.Main.addr_ofK], Or.inl (hOs off ho')⟩
    · exact ⟨a + off, by rw [rdOver_eq r56, p56, ptrAt, B1.Main.addr_ofK], Or.inl (hOb off ho')⟩
  · obtain ⟨h1s, h1b⟩ := hrd rd hl hp ho
    refine holds_run hg fun x hx => ?_
    have hx' := List.contains_iff_mem.mp (List.all_eq_true.mp vsW2_filter x hx)
    rw [vsW2x, List.mem_append, List.mem_map, List.mem_map] at hx'
    rcases hx' with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact holds_loadAt (rl q hq) r55 (sl q hq) (hg _ (hmem q hq)) p55 (hoff q hq) h0 h1s
    · exact hst q hq rd h1b

end
end LeanVM.Guest.B1.VsC
