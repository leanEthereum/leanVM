/-
  LeanVM.Guest.Bridge.ProgAlSlice

  A long function's alignment pass checked in windows over slices of its code chunks and hint parts, with its cells packed ahead: no window walks the whole code, advice or cell list.
-/

module

public import LeanVM.Guest.Bridge.AlignRun

/-!
# Windows over slices

`winOk` (`AlignDefs.lean`) hands each window the whole code, the whole advice and the context built from the whole cell list, which the kernel walks every time; for `main_loop2` that walk outweighs the window. Here a list of parts `L` (the code's chunks, the advice's parts) is cut at **cuts** `(p, r)`, offset `r` of part `p`: `restL L c` is what is left from the cut, `slice L a b` what lies between two cuts, built from the parts it touches only (`slice_rest`: a slice then the rest from its end is the rest from its start).

`winOkS`: from the named state `a.K`, the window's hints the slice between the hint cuts, all at the window's pcs, the pass over the code slice consumes them and reaches `b.K`. A window's pass does not read the hints past it (`alignGo_hs`), so a chain of such windows (`ChainS`) from the start to the parts' ends is the whole pass (`alignOk_of_chainS`).

`AlignCtx.ofPacked`: the context from the cells packed ahead (`ofData_eq_ofPacked`), so a window builds the cell trie from the packed chunks, and one check equates them with the certificate's.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (PowTree Trie natSeq natSeq_eq)

@[expose] public section

/-- A position in a list of parts: part `p`, offset `r` in it. -/
abbrev PCut := ℕ × ℕ

/-- What is left of the parts from a cut. -/
def restL {α : Type} (L : List (List α)) (c : PCut) : List α := (L.drop c.1).flatten.drop c.2

/-- **The slice between two cuts**, from the parts it touches. -/
def slice {α : Type} (L : List (List α)) (a b : PCut) : List α :=
  (((L.drop a.1).take (b.1 - a.1)).flatten ++ (L.getD b.1 []).take b.2).drop a.2

/-- The slice's cuts are in order and within their parts. -/
def sliceOk {α : Type} (L : List (List α)) (a b : PCut) : Bool :=
  Nat.ble a.1 b.1 && Nat.ble a.2 (lenTR (((L.drop a.1).take (b.1 - a.1)).flatten ++ (L.getD b.1 []).take b.2) 0) &&
    Nat.ble b.2 (lenTR (L.getD b.1 []) 0)

/-- The hints are at the pcs of offsets `a` to `b` of the function at `e`. -/
def hintsIn (e a b : ℕ) (hs : List (ℕ × List Prover.Exec.Hint)) : Bool :=
  hs.all fun p ↦ Nat.ble (e + a) p.1 && Nat.blt p.1 (e + b)

/-- A window's ends: its code cut, its hint cut and the pass's named state, which consumed nothing
(`nd = 0`). -/
structure Cut where
  c : PCut
  h : PCut
  K : KSt

/-- **A window over slices**: from the state `a.K` with the hints between the hint cuts, all at the
window's pcs, the pass over the code between the code cuts consumes them and reaches `b.K`. -/
noncomputable def winOkS (X : AlignCtx) (body : List Stmt) (C : List (List OffsetInstruction))
    (H : List (List (ℕ × List Prover.Exec.Hint))) (a b : Cut) : Bool :=
  sliceOk C a.c b.c && sliceOk H a.h b.h && Nat.beq a.K.nd 0 && hintsIn X.entry a.K.i b.K.i (slice H a.h b.h) &&
    X.seq fun X ↦ decide ((alignGo X (slice C a.c b.c) (stOfK body (slice H a.h b.h) a.K) []).map
      (fun p ↦ (p.1.hs.isEmpty, keyOfSt [] p.1)) = some (true, b.K))

/-- The last cut: at the parts' ends, no fall-through past the code, nothing pending. -/
def cutEnd {α β : Type} (C : List (List α)) (H : List (List β)) (a : Cut) : Bool :=
  Nat.beq a.c.1 (lenTR C 0) && Nat.beq a.c.2 0 && Nat.beq a.h.1 (lenTR H 0) && Nat.beq a.h.2 0 &&
    a.K.cur.isNone && a.K.pend.isEmpty

/-- **A chain of windows over slices**, the last cut at the end. -/
def ChainS (X : AlignCtx) (body : List Stmt) (C : List (List OffsetInstruction))
    (H : List (List (ℕ × List Prover.Exec.Hint))) : Cut → List Cut → Prop
  | a, [] => cutEnd C H a = true
  | a, b :: cs => winOkS X body C H a b = true ∧ ChainS X body C H b cs

/-- The first cut: the parts' starts, the body's start. -/
def cut0 : Cut := ⟨(0, 0), (0, 0), ⟨0, 0, some ([], 0), [], []⟩⟩

/-- **The context from the cells packed ahead**, with whether each cell fits. -/
noncomputable def AlignCtx.ofPacked (pl : List ℕ) (locOk : Bool) (extra : List (ℕ × ℕ)) (entry : ℕ) (main : Bool)
    (p : B2C.Plumb) (pows : PowTree) (jt : Trie ℕ) (ents : List (String × ℕ)) (halt len : ℕ) : AlignCtx :=
  ⟨buildT 32 pl, locOk, extra, entry, main, trieOf p.stat, trieOf (p.sites.map fun s ↦ (s.q, s)), trieOf (armsOf p),
    pows, jt, trieOf (ents.map fun e ↦ (e.2, e.1)), halt, len, 1048576⟩

/-! ## Packing in pieces -/

/-- The chunks `packGo` completes over `l` from digit `j` of the chunk `acc`, and where it stops. -/
def packSt : List ℕ → ℕ → ℕ → List ℕ × ℕ × ℕ
  | [], j, acc => ([], j, acc)
  | c :: cs, j, acc => bif Nat.beq j 63 then (fun r ↦ (Nat.add acc (Nat.shiftLeft c (Nat.mul cellBits j)) :: r.1, r.2)) (packSt cs 0 0)
      else packSt cs (Nat.succ j) (Nat.add acc (Nat.shiftLeft c (Nat.mul cellBits j)))

/-- The packing in pieces, each from where the one before stopped: piece `g` from the state `s`
completes the chunks `o` and stops at `s'`. -/
def PackOk : ℕ × ℕ → List (List ℕ × List ℕ × (ℕ × ℕ)) → Prop
  | _, [] => True
  | s, (g, o, s') :: r => packSt g s.1 s.2 = (o, s'.1, s'.2) ∧ PackOk s' r

/-- Where the pieces stop. -/
def packEnd : ℕ × ℕ → List (List ℕ × List ℕ × (ℕ × ℕ)) → ℕ × ℕ
  | s, [] => s
  | _, (_, _, s') :: r => packEnd s' r

end

public section

theorem packGo_append : ∀ (l1 l2 : List ℕ) (j acc : ℕ),
    packGo (l1 ++ l2) j acc = (packSt l1 j acc).1 ++ packGo l2 (packSt l1 j acc).2.1 (packSt l1 j acc).2.2
  | [], _, _, _ => rfl
  | c :: cs, l2, j, acc => by
    simp only [List.cons_append, packGo, packSt, natSeq_eq]
    cases Nat.beq j 63
    · simp only [Bool.cond_false]; exact packGo_append cs l2 _ _
    · simp only [Bool.cond_true, List.cons_append]; rw [packGo_append cs l2 0 0]

/-- **The pieces pack the whole.** -/
theorem packGo_of : ∀ (s : ℕ × ℕ) (r : List (List ℕ × List ℕ × (ℕ × ℕ))), PackOk s r →
    packGo (r.map (·.1)).flatten s.1 s.2 = (r.map (·.2.1)).flatten ++ [(packEnd s r).2]
  | s, [], _ => by simp [packGo, packEnd]
  | s, (g, o, s') :: r, ⟨h, hr⟩ => by
    simp only [List.map_cons, List.flatten_cons, packEnd, List.append_assoc]
    rw [packGo_append, h]
    exact congrArg (o ++ ·) (packGo_of s' r hr)

theorem ofData_eq_ofPacked (locs : List ℕ) (extra : List (ℕ × ℕ)) (entry : ℕ) (main : Bool) (p : B2C.Plumb)
    (pows : PowTree) (jt : Trie ℕ) (ents : List (String × ℕ)) (halt len : ℕ) :
    AlignCtx.ofData locs extra entry main p pows jt ents halt len =
      AlignCtx.ofPacked (packGo locs 0 0) (locs.all fun c ↦ Nat.blt c (2 ^ cellBits)) extra entry main p pows jt
        ents halt len := rfl

/-! ## Slices -/

theorem drop_flatten_getD {α : Type} : ∀ (L : List (List α)) (n : ℕ),
    (L.drop n).flatten = L.getD n [] ++ (L.drop (n + 1)).flatten
  | [], _ => by simp
  | x :: L, 0 => by simp
  | x :: L, n + 1 => by simpa using drop_flatten_getD L n

/-- **A slice then the rest from its end is the rest from its start.** -/
theorem slice_rest {α : Type} {L : List (List α)} {a b : PCut} (h : sliceOk L a b = true) :
    slice L a b ++ restL L b = restL L a := by
  simp only [sliceOk, Bool.and_eq_true, Nat.ble_eq, lenTR_eq, Nat.add_zero] at h
  obtain ⟨⟨hab, hr⟩, hs⟩ := h
  have hd : L.drop a.1 = (L.drop a.1).take (b.1 - a.1) ++ L.drop b.1 := by
    conv_lhs => rw [← List.take_append_drop (b.1 - a.1) (L.drop a.1)]
    rw [List.drop_drop, show a.1 + (b.1 - a.1) = b.1 by omega]
  simp only [slice, restL]
  rw [drop_flatten_getD L b.1]
  generalize hA : ((L.drop a.1).take (b.1 - a.1)).flatten = A at hr ⊢
  conv_rhs => rw [hd, List.flatten_append, hA, drop_flatten_getD L b.1]
  generalize L.getD b.1 [] = B at hs hr ⊢
  generalize (L.drop (b.1 + 1)).flatten = R
  rw [List.drop_append_of_le_length hs]
  conv_rhs => rw [← List.take_append_drop b.2 B, List.append_assoc, ← List.append_assoc A,
    List.drop_append_of_le_length hr]

/-! ## The hints past a window -/

/-- The state with hints `rest` after its own. -/
def St.addHs (st : St) (rest : List (ℕ × List Prover.Exec.Hint)) : St := { st with hs := st.hs ++ rest }

theorem hintsAt_append (pc : ℕ) {rest : List (ℕ × List Prover.Exec.Hint)} (hr : ∀ q ∈ rest, pc < q.1) :
    ∀ l : List (ℕ × List Prover.Exec.Hint), hintsAt pc (l ++ rest) = ((hintsAt pc l).1, (hintsAt pc l).2 ++ rest)
  | [] => by
    cases rest with
    | nil => rfl
    | cons q t =>
      have := hr q (by simp)
      have hb : Nat.beq q.1 pc = false := by
        cases h : Nat.beq q.1 pc
        · rfl
        · have := Nat.eq_of_beq_eq_true h; omega
      simp [hintsAt, hb]
  | (p, x) :: t => by
    simp only [List.cons_append, hintsAt]
    cases Nat.beq p pc <;> rfl

theorem visit_hs (X : AlignCtx) (ins : OffsetInstruction) (i i' : ℕ) (h1 : List Prover.Exec.Hint)
    (hs rest : List (ℕ × List Prover.Exec.Hint)) (pend : List (ℕ × Zip)) (tabs : List (ℕ × Zip × ℕ)) (c : Zip) :
    visit X ins i i' h1 (hs ++ rest) pend tabs c =
      (visit X ins i i' h1 hs pend tabs c).map fun p ↦ (p.1.addHs rest, p.2) := by
  simp only [visit]
  cases ((normZ X.fuel c).bind (hintsStep X h1)) with
  | none => rfl
  | some z =>
    simp only [Option.bind_some]
    cases insStep X i ins tabs z <;> rfl

theorem stepI_i (X : AlignCtx) (ins : OffsetInstruction) {st : St} {p : St × Option (ℕ × Zip)}
    (h : stepI X ins st = some p) : p.1.i = st.i + 1 := by
  unfold stepI at h
  rw [natSeq_eq] at h
  generalize spanP st.i st.pend = S at h
  generalize hintsAt (Nat.add X.entry st.i) st.hs = H at h
  obtain ⟨here, rest⟩ := S
  obtain ⟨h1, hs'⟩ := H
  simp only [Bool.cond_eq_ite] at h
  have hv : ∀ c, visit X ins st.i st.i.succ h1 hs' rest st.tabs c = some p → p.1.i = st.i + 1 := by
    intro c hc
    simp only [visit] at hc
    obtain ⟨z, -, hc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hc
    rfl
  split at h
  · split at h
    · exact hv _ h
    · cases h
  · cases h; rfl
  · split at h
    · exact hv _ h
    · cases h

theorem stepI_hs (X : AlignCtx) (ins : OffsetInstruction) (st : St) {rest : List (ℕ × List Prover.Exec.Hint)}
    (hr : ∀ q ∈ rest, X.entry + st.i < q.1) :
    stepI X ins (st.addHs rest) = (stepI X ins st).map fun p ↦ (p.1.addHs rest, p.2) := by
  unfold stepI
  simp only [natSeq_eq]
  have hh : hintsAt (Nat.add X.entry (st.addHs rest).i) (st.addHs rest).hs =
      ((hintsAt (Nat.add X.entry st.i) st.hs).1, (hintsAt (Nat.add X.entry st.i) st.hs).2 ++ rest) :=
    hintsAt_append _ hr st.hs
  rw [hh]
  obtain ⟨i, hs, cur, pend, tabs⟩ := st
  simp only [St.addHs]
  generalize spanP i pend = S
  generalize hintsAt (Nat.add X.entry i) hs = H
  obtain ⟨here, rest'⟩ := S
  obtain ⟨h1, hs'⟩ := H
  simp only
  split
  · simp only [Bool.cond_eq_ite]; split <;> simp [visit_hs, St.addHs]
  · rfl
  · simp only [Bool.cond_eq_ite]; split <;> simp [visit_hs, St.addHs]

/-- **A window's pass does not read the hints past it.** -/
theorem alignGo_hs (X : AlignCtx) {rest : List (ℕ × List Prover.Exec.Hint)} :
    ∀ (c : List OffsetInstruction) (st : St) (acc : List (ℕ × Zip)),
      (∀ q ∈ rest, X.entry + st.i + c.length ≤ q.1) →
      alignGo X c (st.addHs rest) acc = (alignGo X c st acc).map fun p ↦ (p.1.addHs rest, p.2)
  | [], _, _, _ => rfl
  | ins :: c, st, acc, hr => by
    rw [alignGo_cons, alignGo_cons, stepI_hs X ins st (fun q hq ↦ by have := hr q hq; simp at this; omega)]
    cases hp : stepI X ins st with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.bind_some]
      have hi := stepI_i X ins hp
      exact alignGo_hs X c p.1 _ fun q hq ↦ by have := hr q hq; simp at this; rw [hi]; omega

/-! ## Chains over slices -/

theorem stOfK_addHs (body : List Stmt) (hw rest : List (ℕ × List Prover.Exec.Hint)) {K : KSt} (hK : K.nd = 0) :
    stOfK body (hw ++ rest) K = (stOfK body hw K).addHs rest := by
  simp [stOfK, St.addHs, hK]

/-- **A window over slices**: the pass from the named state, the hints past the window after its
own, reaches the end state named, those hints left. -/
theorem winOkS_go {X : AlignCtx} {body : List Stmt} {C : List (List OffsetInstruction)}
    {H : List (List (ℕ × List Prover.Exec.Hint))} {a b : Cut} (h : winOkS X body C H a b = true)
    {rest : List (ℕ × List Prover.Exec.Hint)} (hr : ∀ q ∈ rest, X.entry + b.K.i ≤ q.1) :
    slice C a.c b.c ++ restL C b.c = restL C a.c ∧ slice H a.h b.h ++ restL H b.h = restL H a.h ∧
      a.K.i ≤ b.K.i ∧ (∀ q ∈ slice H a.h b.h, X.entry + a.K.i ≤ q.1) ∧
      ∃ acc', alignGo X (slice C a.c b.c) (stOfK body (slice H a.h b.h ++ rest) a.K) [] =
        some ((stOfK body [] b.K).addHs rest, acc') := by
  simp only [winOkS, Bool.and_eq_true, Nat.beq_eq, AlignCtx.seq_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc, hh⟩, hnd⟩, hin⟩, hgo⟩ := h
  obtain ⟨⟨st', acc'⟩, hgo, hk⟩ := Option.map_eq_some_iff.mp hgo
  simp only [Prod.mk.injEq] at hk
  obtain ⟨hemp, hk⟩ := hk
  have hst0 : StOk body (slice H a.h b.h) (stOfK body (slice H a.h b.h) a.K) :=
    ⟨⟨a.K.nd, rfl⟩, fun z hz ↦ by
        simp only [stOfK, Option.mem_def, Option.map_eq_some_iff] at hz
        obtain ⟨c, -, rfl⟩ := hz; exact zOk_zipOf _ _ _,
      fun p hp ↦ by
        simp only [stOfK, List.mem_map] at hp
        obtain ⟨q, -, rfl⟩ := hp; exact zOk_zipOf _ _ _,
      fun t ht ↦ by
        simp only [stOfK, List.mem_map] at ht
        obtain ⟨q, -, rfl⟩ := ht; exact zOk_zipOf _ _ _⟩
  obtain ⟨hst', hi'⟩ := alignGo_ok X _ hst0 hgo
  have hhs : st'.hs = [] := List.isEmpty_iff.mp hemp
  have hst'' : StOk body [] st' := ⟨⟨0, by simp [hhs]⟩, hst'.cur, hst'.pend, hst'.tabs⟩
  have heq : stOfK body [] b.K = st' := by rw [← hk]; exact stOfK_keyOfSt hst''
  have hbi : b.K.i = a.K.i + (slice C a.c b.c).length := by
    rw [← hk]; simpa [keyOfSt, stOfK] using hi'
  refine ⟨slice_rest hc, slice_rest hh, by omega, fun q hq ↦ ?_, acc', ?_⟩
  · simp only [hintsIn, List.all_eq_true, Bool.and_eq_true, Nat.ble_eq] at hin
    exact (hin q hq).1
  · rw [stOfK_addHs body _ _ hnd, alignGo_hs X _ _ _ (fun q hq ↦ by have := hr q hq; simp [stOfK]; omega), hgo, heq]
    rfl

theorem restL_end {α : Type} (L : List (List α)) : restL L (L.length, 0) = [] := by simp [restL]

/-- The hints left at a cut of a chain are past its offset. -/
theorem chainS_hints {X : AlignCtx} {body : List Stmt} {C : List (List OffsetInstruction)}
    {H : List (List (ℕ × List Prover.Exec.Hint))} :
    ∀ (cs : List Cut) (a : Cut), ChainS X body C H a cs → ∀ q ∈ restL H a.h, X.entry + a.K.i ≤ q.1
  | [], a, hc => by
    simp only [ChainS, cutEnd, Bool.and_eq_true, Nat.beq_eq, lenTR_eq, Nat.add_zero] at hc
    obtain ⟨⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, -⟩, -⟩ := hc
    have : a.h = (H.length, 0) := Prod.ext h1 h2
    rw [this, restL_end]; simp
  | b :: cs, a, ⟨hw, hc⟩ => by
    have ih := chainS_hints cs b hc
    obtain ⟨-, hh, hab, hin, -⟩ := winOkS_go hw (rest := []) (by simp)
    intro q hq
    rw [← hh] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hin q hq
    · have := ih q hq; omega

theorem chainS_go {X : AlignCtx} {body : List Stmt} {C : List (List OffsetInstruction)}
    {H : List (List (ℕ × List Prover.Exec.Hint))} :
    ∀ (cs : List Cut) (a : Cut) (st : St) (acc : List (ℕ × Zip)), ChainS X body C H a cs →
      { st with hs := [] } = stOfK body [] a.K → st.hs = restL H a.h →
      ((alignGo X (restL C a.c) st acc).bind fun p ↦ alignEnd p.1 p.2).isSome
  | [], a, st, acc, hc, hst, _ => by
    simp only [ChainS, cutEnd, Bool.and_eq_true, Nat.beq_eq, lenTR_eq, Nat.add_zero, Option.isNone_iff_eq_none,
      List.isEmpty_iff] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, hcur⟩, hpend⟩ := hc
    have : a.c = (C.length, 0) := Prod.ext h1 h2
    have hc' : st.cur = none ∧ st.pend = [] := by
      have := congrArg (fun s : St ↦ (s.cur, s.pend)) hst
      simp only [stOfK, hcur, hpend] at this
      simpa using this
    rw [this, restL_end]
    simp [alignGo, alignEnd, hc'.1, hc'.2]
  | b :: cs, a, st, acc, ⟨hw, hc⟩, hst, hhs => by
    obtain ⟨hcs, hhh, -, -, acc', hgo⟩ := winOkS_go hw (chainS_hints cs b hc)
    have hst' : st = stOfK body (slice H a.h b.h ++ restL H b.h) a.K := by
      have hnd : a.K.nd = 0 := by
        simp only [winOkS, Bool.and_eq_true, Nat.beq_eq] at hw; exact hw.1.1.2
      obtain ⟨i, hs, cur, pend, tabs⟩ := st
      simp only [stOfK, St.mk.injEq] at hst hhs ⊢
      rw [hnd, List.drop_zero, hhh, hhs]
      exact ⟨hst.1, rfl, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2⟩
    rw [← hcs, alignGo_append, alignGo_acc, hst', hgo]
    simp only [Option.map_some, Option.bind_some]
    refine chainS_go cs b _ _ hc ?_ ?_
    · simp [St.addHs, stOfK]
    · simp [St.addHs, stOfK]

/-- **A chain of windows over slices is the whole pass.** -/
theorem alignOk_of_chainS {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {C : List (List OffsetInstruction)}
    {H : List (List (ℕ × List Prover.Exec.Hint))} (hpre : alignPre X d = true) (hcode : code = C.flatten)
    (hd : d.2.2 = H.flatten) {cs : List Cut} (hc : ChainS X body C H cut0 cs) : alignOk X body code d = true := by
  rw [alignOk, AlignCtx.seq_eq]
  change (alignPre X d && (alignRun X body code d).isSome) = true
  rw [hpre, Bool.true_and]
  have := chainS_go cs cut0 ⟨0, d.2.2, some (Zip.init body), [], []⟩ [] hc
    (by simp [stOfK, cut0, zipOf, zUp, blockAt, Zip.init]) (by simp [restL, cut0, hd])
  simpa [alignRun, restL, cut0, hcode] using this

end

end LeanVM.Guest.Bridge
