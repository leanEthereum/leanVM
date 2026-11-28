/-
  LeanVM.Guest.B1.VsC.VsPostE

  `vsPostA_of`'s three inputs at `verify_sub`'s honest run: the callees' lists, the witness entries against
  `childHints`, every event exact.
-/

module

public import LeanVM.Guest.B1.VsC.VsPost
public import LeanVM.Guest.B1.VsC.VsPh7
public import LeanVM.Guest.B1.VsC.VsW1
public import LeanVM.Guest.B1.VsC.ChunkDC
public import LeanVM.Guest.Complete.Free

/-!
# `verify_sub`'s final condition, its inputs

* **The callees' lists** (`vsPs σ ch stk mk`): `hint_stream`'s chunks `ch`, `certify_stack`'s `stk`,
  `open_stacked`'s `mk`, every other callee's `[]`, in the skeleton's order (the pointer width's branch has a
  callee only when its selector `.n 471` is zero). `vs_kOk`: `KOk` from each post giving its list (`PopsPost`).
* **The entries** (`vs_skelPops`): the skeleton's entries on those lists are `stream_chunks`, the chunks,
  `table_logs`, `link_shape`, `stk`, `split_values`, `mk`; `vs_sameStreams`: they are `childHints`' when the
  four own witness entries hold the honest words.
* **Exactness** (`vs_exact`): every computed hint of the body but nine is an `inverse` pinned by the next
  `assertNe`; the nine (`vsXs`: `bitsExp` of `.n 240`, two `limbs`, six `windowsExp`) are hypotheses.
  `vsXs_exact`: on the honest valuation the `limbs` are exact by the forward evaluation, the `windowsExp` from
  the oracle's words (`vsWinL`), the `bitsExp` from the bits buffer's words.
* `vsPostA_final`: `vsPostA` from all of these, the form `VsWinHypW`'s final condition asks.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (wordNat bitWord)

@[expose] public section

/-! ## (a) The callees' lists -/

/-- **`KOk` when every callee is entered** and each post gives its list. -/
theorem kOk_of_forall₂ {rd : Reader} {Qs : List (Reader → Tree → Prop)} {Ps : List (List Pop)}
    (h : List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) Qs Ps) :
    ∀ {bs : List Bool}, bs.length = Qs.length → (∀ b ∈ bs, b = true) → KOk rd Qs bs Ps := by
  induction h with
  | nil =>
    intro bs hl _
    cases bs with
    | nil => simp [KOk]
    | cons _ _ => simp at hl
  | cons hQ _ ih =>
    intro bs hl hb
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      have hb0 : b = true := hb b (by simp)
      refine ⟨fun _ => hQ, fun hf => Bool.noConfusion (hb0.symm.trans hf), ?_⟩
      exact ih (by simpa using hl) (fun b' h' => hb b' (by simp [h']))

theorem popsPost_quiet {rd : Reader} {t : Tree} (h : PostQuiet rd t) : PopsPost [] rd t :=
  ⟨by rw [h.1]; exact fun _ => rfl, h.2⟩

theorem popsPost_free {rd : Reader} {t : Tree} (h : FreePost rd t) : PopsPost [] rd t :=
  ⟨by rw [h.1]; exact fun _ => rfl, h.2⟩

theorem popsPost_eq {rd : Reader} {t : Tree} {P : List Pop}
    (h : t.pops coreProgram rd = P ∧ t.Every (ExactAt coreProgram rd)) : PopsPost P rd t :=
  ⟨sameStreams_of_eq h.1, h.2⟩

theorem popsPost_hsQ {rd : Reader} {t : Tree} {ws : List E} {n : ℕ} (h : hsQ ws n rd t) :
    PopsPost ((List.range n).map fun j => ("stream", chunkOf ws j)) rd t :=
  popsPost_eq h

/-- `verify_sub`'s callees' lists, in its skeleton's order: `hint_stream`'s `ch`, eight quiet callees, the
pointer width's branch's (when `.n 471` is zero), `chunk_d`, `certify_stack`'s `stk`, eighteen quiet callees,
`open_stacked`'s `mk`, `check_stack_terminal`. -/
def vsPs (σ : Val) (ch stk mk : List Pop) : List (List Pop) :=
  ch :: List.replicate 8 [] ++ [[]] ++ (if σ (.n 471) = 0 then [[]] else []) ++ [[], stk] ++
    List.replicate 18 [] ++ [mk, []]

theorem atomSkel_kids (a : Atom) : (atomSkel a).filter (· == PItem.kid) = [] := by
  unfold atomSkel
  split <;> simp

/-- A walk's frames are its skeleton's callees. -/
theorem calls_length_skel : ∀ es : List Ev, (calls es).length = ((es.flatMap evSkel).filter (· == PItem.kid)).length
  | [] => rfl
  | .atom a :: es => by
    have e : (Ev.atom a :: es).flatMap evSkel = atomSkel a ++ es.flatMap evSkel := rfl
    rw [show calls (Ev.atom a :: es) = calls es from rfl, e, List.filter_append, atomSkel_kids, List.nil_append]
    exact calls_length_skel es
  | .inK _ :: es => calls_length_skel es
  | .call .. :: es => by
    show (calls es).length + 1 = ((es.flatMap evSkel).filter (· == PItem.kid)).length + 1
    rw [calls_length_skel es]
  | .skip .. :: es => by
    show (calls es).length + 1 = ((es.flatMap evSkel).filter (· == PItem.kid)).length + 1
    rw [calls_length_skel es]

theorem vsSkel_kids (σ : Val) (ch stk mk : List Pop) :
    ((vsSkel σ).filter (· == PItem.kid)).length = (vsPs σ ch stk mk).length := by
  obtain ⟨hA, hI1, hB, hI2z, hI2n, hC⟩ := vs_skel_parts
  have h1 : (if σ (.n 234) = 0 then [] else vsI1n).flatMap skD = [] := by split <;> simp [hI1]
  unfold vsSkel vsPs
  rw [hA, h1, hB, hC]
  by_cases h : σ (.n 471) = 0
  · simp only [ite_eq_left h, hI2z]; rfl
  · simp only [ite_eq_right h, hI2n]; rfl

/-- **(a) The callees' lists**: on a walk of the body, every frame entered, `KOk` from each callee's post
giving its list. -/
theorem vs_kOk {rd : Reader} {σ : Val} {es : List Ev} {Qs : List (Reader → Tree → Prop)} {ch stk mk : List Pop}
    (hw : walk σ vsSS = .fall es)
    (hQ : List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) Qs (vsPs σ ch stk mk)) :
    KOk rd Qs ((calls es).map Call.taken) (vsPs σ ch stk mk) := by
  obtain ⟨hk, ht⟩ := vs_skel hw
  refine kOk_of_forall₂ hQ ?_ ?_
  · rw [List.length_map, calls_length_skel, hk, vsSkel_kids σ ch stk mk, hQ.length_eq]
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact ht c hc

/-! ## (b) The entries -/

/-- **The skeleton's entries** on the callees' lists `vsPs`. -/
theorem vs_skelPops (rd : Reader) (σ : Val) (ch stk mk : List Pop) :
    skelPops rd σ (vsSkel σ) (vsPs σ ch stk mk) =
      ("stream_chunks", [σ (.n 42)]) :: (ch ++ (("table_logs", (Dest.heap (.n 6) 0 6).words rd σ) ::
        ("link_shape", (Dest.heap (.n 9) 0 4).words rd σ) ::
        (stk ++ (("split_values", (Dest.heap (.n 14) 0 36).words rd σ) :: mk)))) := by
  obtain ⟨hA, hI1, hB, hI2z, hI2n, hC⟩ := vs_skel_parts
  have h1 : (if σ (.n 234) = 0 then [] else vsI1n).flatMap skD = [] := by split <;> simp [hI1]
  unfold vsSkel vsPs
  rw [hA, h1, hB, hC]
  by_cases h : σ (.n 471) = 0
  · simp only [ite_eq_left h, hI2z]
    conv_rhs => rw [← List.append_nil mk]
    rfl
  · simp only [ite_eq_right h, hI2n]
    conv_rhs => rw [← List.append_nil mk]
    rfl

/-- The stream's chunk count (`childHints`' `padded`). -/
def vsPadded (s : List E) : ℕ := max ((s.length + Prover.streamChunk - 1) / Prover.streamChunk) 1

/-- The stream zero-padded to whole chunks. -/
def vsStream (s : List E) : List E := s ++ List.replicate (vsPadded s * Prover.streamChunk - s.length) 0

/-- `hint_stream`'s list: the padded stream's chunks. -/
def vsChunks (s : List E) : List Pop := (List.range (vsPadded s)).map fun j => ("stream", chunkOf (vsStream s) j)

theorem vsStream_length (s : List E) : (vsStream s).length = 256 * vsPadded s := by
  have h : s.length ≤ vsPadded s * 256 := by
    unfold vsPadded Prover.streamChunk
    have := Nat.le_max_left ((s.length + 256 - 1) / 256) 1
    have h2 : s.length ≤ (s.length + 256 - 1) / 256 * 256 := by omega
    exact h2.trans (Nat.mul_le_mul_right 256 this)
  unfold vsStream
  rw [List.length_append, List.length_replicate, show Prover.streamChunk = 256 from rfl]
  omega

theorem chunkOf_eq {ws : List E} {p j : ℕ} (hl : ws.length = 256 * p) (hj : j < p) :
    chunkOf ws j = (ws.drop (j * 256)).take 256 := by
  apply List.ext_getElem
  · simp [chunkOf, List.length_take, List.length_drop]; omega
  · intro i h1 h2
    simp only [chunkOf, List.length_map, List.length_range] at h1
    simp only [chunkOf, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [show 256 * j + i = j * 256 + i by ring, List.getD_eq_getElem _ _ (by omega)]

/-- The link's shape as `childHints` writes it. -/
def vsLinkShape (layout : Layout) : List E :=
  [Prover.count (layout.tableLogHeights.foldl max 0),
    Prover.count (pointerWidth layout.logMemory layout.logBytecode layout.tableRows.sum),
    Prover.bit (pointerWidth layout.logMemory layout.logBytecode layout.tableRows.sum =
      bitLength layout.tableRows.sum),
    Prover.count ((packedChallenges tables (layout.tableLogHeights.foldl max 0)
      (pointerWidth layout.logMemory layout.logBytecode layout.tableRows.sum) + 7) / 8)]

/-- **(b) The entries are `childHints`'** when the four own witness entries hold the honest words. -/
theorem vs_sameStreams {bytecode : List K} {seed : Digest} {c : Child} {layout : Layout} {rate : ℕ}
    {rd : Reader} {σ : Val} (hann : announcedLayoutAndRate bytecode c.proof.stream = some (layout, rate))
    (h42 : σ (.n 42) = Prover.count (vsPadded c.proof.stream))
    (h6 : (Dest.heap (.n 6) 0 6).words rd σ = layout.tableLogHeights.map Prover.count)
    (h9 : (Dest.heap (.n 9) 0 4).words rd σ = vsLinkShape layout)
    (h14 : (Dest.heap (.n 14) 0 36).words rd σ = c.freshClaim.values) :
    SameStreams (skelPops rd σ (vsSkel σ) (vsPs σ (vsChunks c.proof.stream) (Prover.stackHints (stackKappas layout))
      (Prover.merkleHints true (Prover.childQueries bytecode seed c) c.proof.openings)))
      (Prover.childHints bytecode seed c) := by
  refine sameStreams_of_eq ?_
  rw [vs_skelPops, h42, h6, h9, h14]
  have hch : vsChunks c.proof.stream = (List.range (vsPadded c.proof.stream)).map (fun i ↦
      ("stream", ((vsStream c.proof.stream).drop (i * Prover.streamChunk)).take Prover.streamChunk)) := by
    unfold vsChunks
    refine List.map_congr_left fun j hj => ?_
    rw [chunkOf_eq (vsStream_length _) (List.mem_range.mp hj)]
    rfl
  rw [hch]
  simp only [Prover.childHints, hann, List.cons_append, List.nil_append, List.append_assoc]
  rfl

/-! ## (c) Exactness -/

/-- A `windowsExp` hint of `count` windows into `.n o … .n (o + count - 1)`. -/
def winAtom (v start width count o : ℕ) : Atom :=
  .hint (.windowsExp (.n v) start width count (.stack ((List.range count).map fun i => .n (o + i))))

/-- `verify_sub`'s six `windowsExp` hints: the grinds' windows. -/
def vsWinL : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(500, 15, 11, 4, 512), (500, 59, 5, 1, 516), (574, 2, 11, 5, 581), (574, 57, 7, 1, 586),
    (2931, 13, 11, 4, 2943), (2931, 57, 7, 1, 2947)]

/-- `verify_sub`'s computed hints no `assertNe` pins: the bits of `.n 240`, the limbs of its first two
arguments, the windows. -/
def vsXs : List Atom :=
  .hint (.bitsExp (.n 240) 24 (.heap (.n 8) 0 24)) :: .hint (.limbs (.n 0) [.n 2895]) ::
    .hint (.limbs (.n 1) [.n 2899]) :: vsWinL.map fun q => winAtom q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2

set_option maxRecDepth 200000 in
/-- Every other computed hint of `verify_sub`'s body is an `inverse` its next atom pins. -/
theorem vs_pinned : Stmt.blockNextOk (fun a => isComputed a && !vsXs.contains a) pinsInverse
    (fn% «verify_sub»).body = true := by
  decide +kernel

theorem vs_walk_ret {σ : Val} {es : List Ev} (hw : walk σ vsSS = .fall es) :
    walk σ (fn% «verify_sub»).body = .ret es [] := by
  rw [show (fn% «verify_sub»).body = vsSS ++ [.ret []] from vsBody_ss, Memory.walk_append, hw]
  simp [walk, walk1, Out.seq, Out.pre]

/-- **(c) Every event exact** once the nine unpinned hints are. -/
theorem vs_exact {rd : Reader} {σ : Val} {es : List Ev} (hw : walk σ vsSS = .fall es)
    (hh : ∀ e ∈ es, e.Holds rd σ) (hx : ∀ a ∈ vsXs, a.Exact rd σ) : ∀ e ∈ es, e.Exact rd σ :=
  exact_of_pinned_except (p2 := fun a => vsXs.contains a) vs_pinned (vs_walk_ret hw) hh
    fun a _ h => hx a (List.contains_iff_mem.mp h)

set_option maxRecDepth 200000 in
/-- The nine hints' values are no range check's temporaries. -/
theorem vsXs_rc : [240, 8, 0, 1, 2895, 2899, 500, 574, 2931, 512, 513, 514, 515, 516, 581, 582, 583, 584, 585, 586,
    2943, 2944, 2945, 2946, 2947].all (fun i => (vsRcL.lookup (.n i)).isNone) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem vsXs_memC : ∀ a ∈ vsXs.tail, a ∈ atomsOf ((vsC.drop 0).take 3794) := by
  decide +kernel

theorem winAtom_exact {rd : Reader} {σ : Val} {w : ℕ → E} {v start width count o : ℕ}
    (hds : ∀ i < count, σ (.n (o + i)) = w (o + i))
    (hw : ∀ i < count, w (o + i) = ofK (g ^ ((wordNat (σ (.n v)) >>> (start + i * width)) % 2 ^ width))) :
    (winAtom v start width count o).Exact rd σ := by
  show List.map σ ((List.range count).map fun i => V.n (o + i)) = _
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  dsimp only [Function.comp_apply]
  rw [hds i hi', hw i hi']

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

/-- **The nine unpinned hints on the honest run**: the `limbs` by the forward evaluation, the windows from the
oracle's words, the bits from the bits buffer's. -/
theorem vsXs_exact (ha : args.length = 6) {rd : Reader}
    (h240 : (Hint.bitsExp (.n 240) 24 (.heap (.n 8) 0 24)).Exact rd (vsVal rd0 w args))
    (hW : ∀ q ∈ vsWinL, ∀ i < q.2.2.2.1, w (q.2.2.2.2 + i) =
      ofK (g ^ ((wordNat (vsVal rd0 w args (.n q.1)) >>> (q.2.1 + i * q.2.2.1)) % 2 ^ q.2.2.1))) :
    ∀ a ∈ vsXs, a.Exact rd (rdOver (vsVal rd0 w args) rd) := by
  have hrc : ∀ i, (i = 240 ∨ i = 8 ∨ i = 0 ∨ i = 1 ∨ i = 2895 ∨ i = 2899 ∨ i = 500 ∨ i = 574 ∨ i = 2931 ∨
      (512 ≤ i ∧ i < 517) ∨ (581 ≤ i ∧ i < 587) ∨ (2943 ≤ i ∧ i < 2948)) →
      rdOver (vsVal rd0 w args) rd (.n i) = vsVal rd0 w args (.n i) := by
    intro i hi
    refine rdOver_eq ?_
    rw [vsRcs_eq]
    refine Option.isNone_iff_eq_none.mp (List.all_eq_true.mp vsXs_rc i ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hgood : ∀ a ∈ vsXs.tail, Good rd0 vsSL w (vsVal rd0 w args) a := fun a h =>
    vsC_atoms_good ha 0 3794 a (vsXs_memC a h)
  have hwin : ∀ v s wd n o, (v, s, wd, n, o) ∈ vsWinL →
      (winAtom v s wd n o).Exact rd (rdOver (vsVal rd0 w args) rd) := by
    intro v s wd n o hm
    have hv : v = 500 ∨ v = 574 ∨ v = 2931 := by simp [vsWinL] at hm; omega
    have hoi : ∀ i < n, (512 ≤ o + i ∧ o + i < 517) ∨ (581 ≤ o + i ∧ o + i < 587) ∨
        (2943 ≤ o + i ∧ o + i < 2948) := by
      intro i hi
      simp [vsWinL] at hm
      omega
    have hg := hgood (winAtom v s wd n o)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hm, rfl⟩)))
    simp only [winAtom, Good] at hg
    refine winAtom_exact (w := w) (fun i hi => ?_) (fun i hi => ?_)
    · rw [hrc (o + i) (by have := hoi i hi; omega)]
      exact hg _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    · rw [hrc v (by omega)]
      exact hW _ hm i hi
  intro a ha'
  unfold vsXs at ha'
  rcases List.mem_cons.mp ha' with rfl | ha'
  · show ∃ n, _
    obtain ⟨n, hn, h1, h2⟩ := h240
    refine ⟨n, hn, by rw [hrc 240 (by omega)]; exact h1, ?_⟩
    rw [← h2]
    simp only [Dest.words, hrc 8 (by omega)]
  rcases List.mem_cons.mp ha' with rfl | ha'
  · have hg := hgood (.hint (.limbs (.n 0) [.n 2895])) (by decide)
    simp only [Good] at hg
    have h0 : vsVal rd0 w args (.n 2895) = limbAt (vsVal rd0 w args (.n 0)) 0 := hg 0 (by simp)
    show [rdOver (vsVal rd0 w args) rd (.n 2895)] = _
    rw [hrc 2895 (by omega), hrc 0 (by omega), h0]
    simp [limbAt]
  rcases List.mem_cons.mp ha' with rfl | ha'
  · have hg := hgood (.hint (.limbs (.n 1) [.n 2899])) (by decide)
    simp only [Good] at hg
    have h0 : vsVal rd0 w args (.n 2899) = limbAt (vsVal rd0 w args (.n 1)) 0 := hg 0 (by simp)
    show [rdOver (vsVal rd0 w args) rd (.n 2899)] = _
    rw [hrc 2899 (by omega), hrc 1 (by omega), h0]
    simp [limbAt]
  obtain ⟨⟨v, s, wd, n, o⟩, hm, rfl⟩ := List.mem_map.mp ha'
  exact hwin v s wd n o hm

end

/-! ## The final condition -/

/-- **`verify_sub`'s final condition on its honest run** (`σ = rdOver (vsVal rd0 w args) rd`): its walk and events
holding, its callees' posts giving `vsPs`' lists, the four own witness entries' honest words, the bits buffer's
words and the oracle's windows. -/
theorem vsPostA_final {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {bytecode : List K}
    {seed : Digest} {c : Child} {layout : Layout} {rate : ℕ} {rd : Reader} {es : List Ev} {bufs : List ℕ}
    {ts : List Tree} {Qs : List (Reader → Tree → Prop)}
    (hw : walk (rdOver (vsVal rd0 w args) rd) vsSS = .fall es)
    (hh : ∀ e ∈ es, e.Holds rd (rdOver (vsVal rd0 w args) rd))
    (hv : Tree.KidsValid coreProgram rd (rdOver (vsVal rd0 w args) rd) (calls es) ts)
    (hq : KidsPost rd Qs (calls es) ts)
    (hQ : List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) Qs
      (vsPs (rdOver (vsVal rd0 w args) rd) (vsChunks c.proof.stream) (Prover.stackHints (stackKappas layout))
        (Prover.merkleHints true (Prover.childQueries bytecode seed c) c.proof.openings)))
    (hann : announcedLayoutAndRate bytecode c.proof.stream = some (layout, rate))
    (h42 : rdOver (vsVal rd0 w args) rd (.n 42) = Prover.count (vsPadded c.proof.stream))
    (h6 : (Dest.heap (.n 6) 0 6).words rd (rdOver (vsVal rd0 w args) rd) = layout.tableLogHeights.map Prover.count)
    (h9 : (Dest.heap (.n 9) 0 4).words rd (rdOver (vsVal rd0 w args) rd) = vsLinkShape layout)
    (h14 : (Dest.heap (.n 14) 0 36).words rd (rdOver (vsVal rd0 w args) rd) = c.freshClaim.values)
    (h240 : (Hint.bitsExp (.n 240) 24 (.heap (.n 8) 0 24)).Exact rd (vsVal rd0 w args))
    (hW : ∀ q ∈ vsWinL, ∀ i < q.2.2.2.1, w (q.2.2.2.2 + i) =
      ofK (g ^ ((wordNat (vsVal rd0 w args (.n q.1)) >>> (q.2.1 + i * q.2.2.1)) % 2 ^ q.2.2.1))) :
    vsPostA bytecode seed c rd (.node "verify_sub" (rdOver (vsVal rd0 w args) rd) bufs ts) :=
  vsPostA_of hw (vs_kOk hw hQ) hv hq (by rw [(vs_skel hw).1]; exact vs_sameStreams hann h42 h6 h9 h14)
    (vs_exact hw hh (vsXs_exact ha h240 hW))

end
end LeanVM.Guest.B1.VsC
