/-
  LeanVM.Guest.EndExecYWit

  Each witness hint pops the next entry of its stream, the reference's words at its destination.
-/

module

public import LeanVM.Guest.EndExecY
public import LeanVM.Guest.EndExecCUsed

/-!
# The witness hints

`hintWitness_cur`: at a state of the tracks, a witness hint, after the hints of its pc before it,
meets `HintOk`. The state's track frame (`YCur`) moves past the atoms its offset's hints consume
(`alignAt_step`); the hint is the `j`-th flow hint of its pc, so it compiles the `j`-th flow atom
(`forall₂_split`), and the frame past the atoms before it (`moves_atoms`) has that atom at its
position. Its entry is then the next of its stream after the entries done (`TrackOk.witness_next`),
the honest pushes' at the cursor, which the hints before it moved by the entries those atoms pop
(`cursor_past`). Its words: a stack run's are the frame's values at their cells (`WitCells`), a heap
run's the reference's own words at the buffer (`Ref.Ok.hintWords`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

public section

/-! ## Lists -/

theorem forall₂_split {α β : Type} {R : α → β → Prop} {b : β} {m2 : List β} :
    ∀ {l : List α} {m1 : List β}, List.Forall₂ R l (m1 ++ b :: m2) →
      ∃ l1 a l2, l = l1 ++ a :: l2 ∧ List.Forall₂ R l1 m1 ∧ R a b
  | [], [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | _ :: l, [], .cons h _ => ⟨[], _, l, rfl, .nil, h⟩
  | x :: l, _ :: m1, .cons h hr => by
    obtain ⟨l1, a, l2, rfl, h1, h2⟩ := forall₂_split (m1 := m1) hr
    exact ⟨x :: l1, a, l2, rfl, .cons h h1, h2⟩

/-- The `j`-th of a filtered list's entries, with what comes before it. -/
theorem filter_split {α : Type} {p : α → Bool} {l : List α} {l1 l2 : List α} {a : α}
    (h : l.filter p = l1 ++ a :: l2) : ∃ x y, l = x ++ a :: y ∧ x.filter p = l1 := by
  obtain ⟨x1, x2, rfl, h1, h2⟩ := List.filter_eq_append_iff.mp h
  obtain ⟨y1, y2, rfl, hy, -, -⟩ := List.filter_eq_cons_iff.mp h2
  refine ⟨x1 ++ y1, y2, by simp, ?_⟩
  rw [List.filter_append, h1, List.filter_eq_nil_iff.mpr (fun z hz ↦ by simpa using hy z hz), List.append_nil]

/-! ## The executor's hints -/

/-- A pc with hints is in the program. -/
theorem pc_lt_of_hints {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) {pc : ℕ}
    (h : (C.hints[pc]?).getD [] ≠ []) : pc < 2 ^ guestProgram.logSize := by
  by_contra hpc
  have hsz : C.hints.size = 2 ^ guestProgram.logSize := by
    simp only [Ctx.of, bind_ok, pure_ok] at hC
    obtain ⟨ops, -, rfl⟩ := hC
    exact (foldl_set_size _ _).trans (Array.size_replicate ..)
  rw [Array.getElem?_eq_none (by omega)] at h
  exact h rfl

theorem compiles_wStack {loc : ℕ → ℕ} {hc : Core.Hint} {S : String} {base len : ℕ}
    (h : compiles loc hc (.witnessStack S base len) = true) : ∃ vs, hc = .witness S (.stack vs) := by
  cases hc with
  | witness s d =>
    cases d with
    | stack vs =>
      simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨vs, by rw [h.1.1]⟩
    | heap => simp [compiles] at h
  | _ => simp [compiles] at h

theorem compiles_wHeap {loc : ℕ → ℕ} {hc : Core.Hint} {S : String} {ptr lo len : ℕ}
    (h : compiles loc hc (.witnessHeap S ptr lo len) = true) :
    ∃ p, hc = .witness S (.heap p lo len) ∧ ptr = loc p.idx := by
  cases hc with
  | witness s d =>
    cases d with
    | heap p off len' =>
      simp only [compiles, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
      exact ⟨p, rfl, rfl⟩
    | stack => simp [compiles] at h
  | _ => simp [compiles] at h

/-! ## The frame at the hint -/

variable {P : Core.Program} {rd : Reader} {Is : List Inst}

/-- An atom at a frame's position is an event of its path. -/
theorem atom_on_path {e : Ent} (h : EntOk P Is e) {a : Atom} {ps : List Stmt} (hp : e.pos = .atom a :: ps) :
    ∃ vs, walk e.σ e.fn.body = .ret (e.pre ++ e.es) vs ∧ Ev.atom a ∈ e.pre ++ e.es := by
  obtain ⟨vs, h1, h2⟩ := h.path
  rw [hp, walk_atom_cons] at h2
  obtain ⟨es', -, he⟩ := pre_eq_ret h2
  exact ⟨vs, h1, List.mem_append_right _ (by rw [he]; exact List.mem_cons_self)⟩

/-- **The cursor at a hint**: the hints before it moved the cursor of a stream by the entries of the
atoms the frame moved past, the flow ones paired with the flow hints before it. -/
theorem cursor_past {X : AlignCtx} {S : String} {C : Ctx} {s s1 : St}
    {pre : List Hint} (e1 : pre.foldlM (runHint C) s = .ok s1)
    {done : List Pop} (hcur : CurOk s done) {rd : Reader} {σ : Val} {as0 as1 bs : List Atom}
    (h0 : ∀ a ∈ as0, ∀ rd σ, a.pops rd σ = []) (hb : ∀ a ∈ bs, flowAtom a = false)
    (hpair : List.Forall₂ (Pairs X) (as1.filter flowAtom) (pre.filter isaFlowHint)) :
    s1.cursor.getD S 0 =
      ((done ++ (as0 ++ as1 ++ bs).flatMap (fun a ↦ a.pops rd σ)).filter (·.1 == S)).length := by
  rw [hints_cursor S pre s s1 e1, hcur S, List.filter_append, List.length_append, List.flatMap_append,
    List.flatMap_append, List.flatMap_eq_nil_iff.mpr (fun a ha ↦ h0 a ha rd σ),
    List.flatMap_eq_nil_iff.mpr (fun a ha ↦ flowAtom_pops (hb a ha) rd σ), List.nil_append, List.append_nil,
    flatMap_flow rd σ as1, count_pairs rd σ S hpair, filter_flow]

/-! ## The witness hints -/

/-- A stream's next entry, read off the honest pushes: where they have `(S, w)` at the cursor among those
of `S`, it is the executor's stream's next. -/
theorem streamNext_of {r : Ref} {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C) (hSh : PushShape) {s1 : St}
    {S : String} {w : List E}
    (h : ((Hints.honestPushes End.bytecode r.seed r.s r.w).filter (·.1 == S))[s1.cursor.getD S 0]? = some (S, w)) :
    StreamNext C s1 S w := by
  rw [hSh] at h
  have hmem := List.mem_of_getElem? h
  rw [List.mem_filter] at hmem
  refine ⟨_, streams_guest hC ⟨_, hmem.1, rfl⟩, ?_⟩
  rw [List.getElem?_toArray, List.getElem?_map, h]
  rfl

/-- **Each witness hint pops the next entry of its stream, the reference's words at its
destination**, after the hints of its pc before it, a buffer's below `2^κ`. -/
theorem witness_core {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A) (hAd : AdvAl A)
    (hW : WitCells A) (hSh : PushShape) {Y : Ref → St → Prop} (hY : ∀ r s, Y r s → YCur A r s) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      MovesW (refMem r.img) s s1 → isWitnessHint h = true →
        HeapB (2 ^ r.κ) s1 h ∧ (Mode.HintIn s1 h → HintOk C (refMem r.img) s1 h) := by
  intro r hr C hC s hon pre h post hL s1 ef hm hw
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hne : (C.hints[s.pc]?).getD [] ≠ [] := by rw [hL]; simp
  have hge : proLen ≤ s.steps := by
    by_contra hlt
    rcases hon.1.1 with ⟨-, hpc, -⟩ | ⟨hge, -⟩
    · exact hne (hints_pro hC rfl (by omega))
    · omega
  obtain ⟨done, st, htr, hcur⟩ := (hY r s hon.1.2.2).2 hge hon.2.2.1
  obtain ⟨e, st', rfl, hE, hfp, hat⟩ := htr.top
  obtain ⟨off, hpc, p, hal', as0, hpops, hpos0⟩ := hat
  obtain ⟨ins, z, tabs, rr, as, hins, -, hpos, hpair, -⟩ := alignAt_step (hP.ok _ _ hE.find) hal'
  have hpcE : s.pc = (A e.I.t.name).X.entry + off := hpc
  have hh : (C.hints[s.pc]?).getD [] = Mode.hintsAt Data.adviceHints s.pc :=
    Mode.ctx_hints hC Mode.adviceHints_incr (pc_lt_of_hints hC hne)
  rw [hAd _ _ hE.find off ins hins, ← hpcE, ← hh, hL, List.filter_append,
    List.filter_cons_of_pos (by cases h <;> simp_all [isWitnessHint, isaFlowHint])] at hpair
  obtain ⟨A1, a, A2, hA, hp1, ha⟩ := forall₂_split hpair
  obtain ⟨as1, as2, rfl, has1⟩ := filter_split hA
  have hb2 : ∀ x ∈ ([] : List Atom), flowAtom x = false := fun _ h ↦ nomatch h
  have hposE : e.pos = (as0 ++ as1 ++ []).map Stmt.atom ++ (.atom a :: (as2.map Stmt.atom ++ z.pos)) := by
    rw [hpos0, hpos]; simp
  obtain ⟨e1, hm1, hI1, hfn1, hp1', -⟩ := moves_atoms (P := coreProgram) (rd := r.rd0)
    (Is := honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) (as0 ++ as1 ++ []) (done := done) (st := st') hposE
  have htr1 := htr.track.moves hm1
  have hE1 := htr1.ents e1 List.mem_cons_self
  have hσ1 : e1.σ = e.σ := by simp only [Ent.σ, hI1]
  obtain ⟨hc, rfl, hcomp⟩ := ha
  have hhadv : advHintOk h = true := hints_adv hC rfl s.pc h (by rw [hL]; simp)
  have hhpos : posHintOk h = true := hints_pos hC rfl (pc_lt_of_hints hC hne) h (by rw [hL]; simp)
  obtain ⟨vs0, hwalk, hon1⟩ := atom_on_path hE1 hp1'
  rw [hσ1, hfn1] at hwalk
  have hfp1 : s1.fp = e.I.fp := hm.1.trans hfp.symm
  cases h with
  | witnessStack S base len =>
    obtain ⟨vs, rfl⟩ := compiles_wStack hcomp
    have hn := htr1.witness_next hp1' hr.pops
    rw [← cursor_past ef hcur hpops hb2 (by rw [has1]; exact hp1)] at hn
    have hnext := streamNext_of hC hSh hn
    obtain ⟨-, rfl, hloc⟩ := compiles_stack hcomp
    have hcells := hW r hr s.pc s.fp done e st' htr _ _ hwalk S (.stack vs) hon1
    refine ⟨trivial, fun _ ↦ ⟨_, hnext, by simp [Dest.words], by simpa [posHintOk] using hhpos,
      fun k hk ↦ ?_⟩⟩
    simp only [Dest.words, List.length_map] at hk
    obtain ⟨h1, h2⟩ := hcells vs[k] (List.getElem_mem hk)
    rw [hloc k hk] at h1 h2
    rw [hfp1, Nat.add_assoc]
    refine ⟨h1, ?_⟩
    simp only [Dest.words, List.getElem_map, hσ1]
    exact h2
  | witnessHeap S ptr lo len =>
    obtain ⟨pv, rfl, rfl⟩ := compiles_wHeap hcomp
    have hn := htr1.witness_next hp1' hr.pops
    rw [← cursor_past ef hcur hpops hb2 (by rw [has1]; exact hp1)] at hn
    have hnext := streamNext_of hC hSh hn
    obtain ⟨b, hb, hσp, -, hc2⟩ := hW r hr s.pc s.fp done e st' htr _ _ hwalk S (.heap pv lo len) hon1
    have hlo : lo + len < 2 ^ 30 := by simpa [advHintOk] using hhadv
    have hwords : (Dest.heap pv lo len).words r.rd0 e1.σ =
        (List.range len).map fun k ↦ (r.rd0 (Parameters.g ^ (b + lo + k))).getD 0 := by
      rw [hσ1]; exact words_heap hσp
    have hcell : ∀ k < len, b + lo + k < 2 ^ r.κ ∧
        refMem r.img (b + lo + k) = (r.rd0 (Parameters.g ^ (b + lo + k))).getD 0 := by
      intro k hk
      obtain ⟨f, bufs, kids, hIt⟩ := hE.node
      have hA : Parameters.g ^ (b + lo + k) ∈ hintWords coreProgram B2C.fs B2C.H r.hdr r.T := by
        refine List.mem_flatMap.mpr ⟨e.I, hE.mem, ?_⟩
        have hf : coreProgram.find? f = some e.fn := by have := hE.find; rwa [hIt] at this
        simp only [Inst.hintAddrs, hIt, events_node hf hwalk, heapHintAddrs]
        refine List.mem_flatMap.mpr ⟨_, hon1, ?_⟩
        simp only [Ev.hintAddrs, hintDest?, destHeap?, Option.bind_some, hσp, Parameters.limb_ofK]
        exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, by simp [addressOfIndex, ← pow_add, Nat.add_assoc]⟩
      obtain ⟨v, hv1, hv2⟩ := hr.hintWords _ hA
      have hb' : b < 2 ^ 28 := hb
      obtain ⟨hc, hM⟩ := refRd_imgK hκ r.img (by omega) hv2
      exact ⟨hc, by rw [hM, hv1]; rfl⟩
    have h2k : 2 ^ r.κ ≤ maxCells := Nat.pow_le_pow_right (by norm_num) hκ
    refine ⟨fun b' hpt k hk ↦ ?_, fun hin ↦ ⟨b, (Dest.heap pv lo len).words r.rd0 e1.σ, ⟨?_, hb⟩, hnext,
      by rw [hwords]; simp, by simpa [posHintOk] using hhpos, ?_⟩⟩
    · obtain ⟨v, hv, rfl⟩ := get_of_ptrAt hpt
      have hMv := hm.2 _ _ hv
      rw [hfp1, hc2, hσp] at hMv
      obtain rfl : b' = b := gpow_inj (by have := hpt.2; unfold maxCells at this; omega)
        (by unfold maxCells at hb; omega) (ofK_injective hMv).symm
      exact (hcell k hk).1
    · rw [hfp1]
      have hw' : s1.mem.written (e.I.fp + (A e.I.t.name).X.locAt pv.idx) = true := by rw [← hfp1]; exact hin
      obtain ⟨v, hv⟩ := Mem.get_of_written hw'
      rw [Mem.peek_of_get hv, ← hm.2 _ _ hv, hc2, hσp]
    · rw [hwords]
      intro k hk
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨h1, h2⟩ := hcell k hk
      exact ⟨by omega, h2⟩
  | _ => simp [isWitnessHint] at hw

/-- **Each witness hint pops the next entry of its stream, the reference's words at its
destination**, after the hints of its pc before it. -/
theorem hintWitness_cur {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A) (hAd : AdvAl A)
    (hW : WitCells A) (hSh : PushShape) {Y : Ref → St → Prop} (hY : ∀ r s, Y r s → YCur A r s) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isWitnessHint h = true → Mode.HintIn s1 h → HintOk C (refMem r.img) s1 h :=
  fun r hr C hC s hon pre h post hL s1 ef hm hw hin ↦
    (witness_core hP hAd hW hSh hY r hr C hC s hon pre h post hL s1 ef hm.w hw).2 hin

end

end LeanVM.Guest.EndExec
