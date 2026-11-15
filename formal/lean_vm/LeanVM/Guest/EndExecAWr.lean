/-
  LeanVM.Guest.EndExecAWr

  The advised pointer cells along the run: each `allocAdvice` whose buffer exists writes its
  pointer cell, which stays written.
-/

module

public import LeanVM.Guest.EndExecAHeap

/-!
# The advised pointer cells written

* `advWrites_alignA : AdvWrites alignA`: an `allocAdvice` whose buffer exists pops its size
  (`advNext_alignA`) and allocates it, writing its pointer cell (`adv_written`); the advised buffer
  hints at an offset are its hints of their buffer index (`bufsOf_inv`).
* `wrArith_alignA : WrArith alignA`: past a step of the tree track the cells stay written: within the
  frame, those before the offset and at it; at a jump, every advised cell of the frame, all its
  advice being before its first jump (`Bridge.advChk`); a callee entered has written none.
* `keepY_allocA_of`: each step keeps `YAlloc alignA`, from `SizesAt` and `HeapPops`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

public section

/-! ## An advised buffer's hint -/

theorem popEntry_val {C : Ctx} {s s' : St} {name : String} {v e : List E}
    (h : popEntry C s name = .ok (v, s')) (hn : StreamNext C s name e) : v = e := by
  obtain ⟨es, h1, h2⟩ := hn
  unfold popEntry at h
  simp only [h1, h2, pure_ok, Prod.mk.injEq] at h
  exact h.1.symm

/-- **An `allocAdvice` popping a size writes its pointer cell.** -/
theorem adv_written {C : Ctx} {s s' : St} {p : ℕ} {S : String} {w : E} (hs : s.Good)
    (h : runHint C s (.allocAdvice p S) = .ok s') (hn : StreamNext C s S [w]) :
    s'.mem.written (s.fp + p) = true := by
  simp only [runHint, bind_ok] at h
  obtain ⟨⟨v, s1⟩, h1, h⟩ := h
  have f1 := popEntry_follows hs h1
  obtain rfl := popEntry_val h1 hn
  dsimp only at h
  simp only [bind_ok] at h
  obtain ⟨sz, -, ⟨n, s2⟩, h2, h⟩ := h
  have f2 := (St.logOr_ok f1.good h2).1
  obtain ⟨-, hw⟩ := Mode.allocate_written f2.good h
  rwa [f2.fp, f1.fp] at hw

theorem lookupN_of_mem : ∀ {l : List (ℕ × List Hint)}, pcsUp l = true → ∀ {q}, q ∈ l → l.lookup q.1 = some q.2
  | [], _, _, hq => by simp at hq
  | ⟨a1, a2⟩ :: l, hu, q, hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [List.lookup]
    · have h1 : a1 < q.1 := pcsUp_lt hu q hq
      have h2 : (q.1 == a1) = false := by simp; omega
      simp only [List.lookup, h2]
      exact lookupN_of_mem (pcsUp_tail hu) hq

theorem filter_idx_inv {α : Type} (p : α → Bool) :
    ∀ (l : List α) (m : ℕ) {x : α}, (l.filter p)[m]? = some x → ∃ i, l[i]? = some x ∧ (l.take i).countP p = m
  | [], _, _, h => by simp at h
  | a :: l, m, x, h => by
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha] at h
      cases m with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        exact ⟨0, by simp [h], by simp⟩
      | succ m =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨i, h1, h2⟩ := filter_idx_inv p l m h
        exact ⟨i + 1, by simpa using h1, by simp [List.take_succ_cons, ha, h2]⟩
    · rw [List.filter_cons_of_neg ha] at h
      obtain ⟨i, h1, h2⟩ := filter_idx_inv p l m h
      exact ⟨i + 1, by simpa using h1, by simp [List.take_succ_cons, ha, h2]⟩

/-- **The buffer hint of index `k`, at offset `off`, is a hint there**, its index `nbAt` plus the
buffer hints before it there (the converse of `Bridge.bufsOf_idx`). -/
theorem bufsOf_inv {X : AlignCtx} {d : ℕ × ℕ × List (ℕ × List Hint)} {entry : ℕ} (hU : HintsUp d entry) {k off : ℕ}
    {h : Hint} (hk : (bufsOf X d)[k]? = some (off, h)) :
    ∃ i, (hintsAtD d entry off)[i]? = some h ∧ nbAt X d off + ((hintsAtD d entry off).take i).countP (isBuf X) = k := by
  have hm : (off, h) ∈ hintsOff d := by
    rw [bufsOf_eq] at hk; exact (List.mem_filter.mp (List.mem_of_getElem? hk)).1
  obtain ⟨q, hq, hqh⟩ := List.mem_flatMap.mp (by unfold hintsOff at hm; exact hm)
  obtain ⟨h', hh', hqe⟩ := List.mem_map.mp hqh
  simp only [Prod.mk.injEq] at hqe
  obtain ⟨hqo, rfl⟩ := hqe
  obtain ⟨h1, h2, h3⟩ := hU
  have hq1 : q.1 = entry + off := by have := h3 q hq; rw [h1] at hqo; omega
  have hl : d.2.2.lookup (entry + off) = some q.2 := by
    rw [← hq1]; exact lookupN_of_mem h2 hq
  have hat : hintsAtD d entry off = q.2 := by unfold hintsAtD; rw [hl]; rfl
  obtain ⟨P, S, he, hP, hS⟩ := hintsOff_split ⟨h1, h2, h3⟩ hl
  set M := q.2.map fun h ↦ (off, h)
  have hb : bufsOf X d = P.filter (fun q ↦ isBuf X q.2) ++ M.filter (fun q ↦ isBuf X q.2) ++
      S.filter (fun q ↦ isBuf X q.2) := by rw [bufsOf_eq, he, List.filter_append, List.filter_append]
  have hnb : nbAt X d off = (P.filter fun q ↦ isBuf X q.2).length := by
    rw [nbAt_eq, hb, List.countP_append, List.countP_append]
    have e1 : (P.filter fun q ↦ isBuf X q.2).countP (fun q ↦ decide (q.1 < off)) = (P.filter fun q ↦ isBuf X q.2).length :=
      List.countP_eq_length.mpr fun q hq ↦ by simpa using hP q (List.mem_filter.mp hq).1
    have e2 : (M.filter fun q ↦ isBuf X q.2).countP (fun q ↦ decide (q.1 < off)) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        obtain ⟨h', -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq).1
        simp
    have e3 : (S.filter fun q ↦ isBuf X q.2).countP (fun q ↦ decide (q.1 < off)) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        have := hS q (List.mem_filter.mp hq).1
        simp only [decide_eq_true_eq]
        omega
    rw [e1, e2, e3]; rfl
  rw [hb] at hk
  set lP := (P.filter fun q ↦ isBuf X q.2).length
  have hge : lP ≤ k := by
    by_contra hlt
    rw [List.append_assoc, List.getElem?_append_left (by omega)] at hk
    have := hP _ (List.mem_filter.mp (List.mem_of_getElem? hk)).1
    simp at this
  rw [List.append_assoc, List.getElem?_append_right hge] at hk
  have hlt : k - lP < (M.filter fun q ↦ isBuf X q.2).length := by
    by_contra hge'
    rw [List.getElem?_append_right (by omega)] at hk
    have := hS _ (List.mem_filter.mp (List.mem_of_getElem? hk)).1
    simp at this
  rw [List.getElem?_append_left hlt] at hk
  obtain ⟨i, hi1, hi2⟩ := filter_idx_inv _ M (k - lP) hk
  refine ⟨i, ?_, ?_⟩
  · rw [hat]
    simp only [M, List.getElem?_map] at hi1
    cases hqi : q.2[i]? with
    | none => rw [hqi] at hi1; cases hi1
    | some h'' => rw [hqi] at hi1; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hi1; rw [hi1.2]
  · rw [hnb, hat]
    have hc : (M.take i).countP (fun q ↦ isBuf X q.2) = (q.2.take i).countP (isBuf X) := by
      simp only [M]; rw [← List.map_take, List.countP_map]; rfl
    rw [← hc, hi2]
    omega

/-- **An advised buffer hint is before its function's first jump.** -/
theorem adv_lt {F : FnAl} (hA : advChk F = true) {k o p : ℕ} {S : String}
    (hk : (bufsOf F.X F.d)[k]? = some (o, .allocAdvice p S)) : o < nextJump F.code 0 :=
  (adv_spec hA (List.mem_filter.mp (List.mem_of_getElem? hk)).1 rfl).1

theorem foldlM_split {C : Ctx} {l : List Hint} {s s1 : St} {i : ℕ} {h : Hint} (hi : l[i]? = some h)
    (e : l.foldlM (runHint C) s = .ok s1) :
    ∃ sx s2, (l.take i).foldlM (runHint C) s = .ok sx ∧ runHint C sx h = .ok s2 ∧
      (l.drop (i + 1)).foldlM (runHint C) s2 = .ok s1 := by
  have hlt := (List.getElem?_eq_some_iff.mp hi).1
  rw [← List.take_append_drop i l, List.foldlM_append, List.drop_eq_getElem_cons hlt,
    (List.getElem?_eq_some_iff.mp hi).2, bind_ok] at e
  obtain ⟨sx, hx, e⟩ := e
  rw [List.foldlM_cons, bind_ok] at e
  obtain ⟨s2, h2, e⟩ := e
  exact ⟨sx, s2, hx, h2, e⟩

/-- **The hints at a frame's offset write its advised pointer cells there**, those whose buffers
exist. -/
theorem advWrites_alignA : AdvWrites alignA := by
  intro r hr C hC done e st s htr hch hnc hha hfine hon hpcS s1 e1 hm k p S hk hb
  have hE := htr.track.ents e List.mem_cons_self
  have hU := hintsUp_frame hE.find
  obtain ⟨-, hat⟩ := htr.linked.top
  obtain ⟨off, hpc, q, hal', -, -, -⟩ := hat
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (progAl.ok _ _ hE.find) hal'
  have hsize := (ctx_of_spec hC).1
  have hh : (C.hints[s.pc]?).getD [] = Mode.hintsAt Data.adviceHints s.pc :=
    Mode.ctx_hints hC Mode.adviceHints_incr (by rw [← hsize]; exact hpcS)
  have hhs : (C.hints[s.pc]?).getD [] = hintsAtOff (alignA e.I.t.name) off := by
    rw [hh, hintsAtOff, advAl_alignA _ _ hE.find off ins hins]
    rw [hpc]
    rfl
  have hoff : s.pc - entOf alignA e.I.t.name = off := by
    show s.pc - (alignA e.I.t.name).X.entry = off
    have : s.pc = (alignA e.I.t.name).X.entry + off := hpc
    omega
  rw [hoff] at hk
  obtain ⟨i, hi, hik⟩ := bufsOf_inv hU hk
  have hget : ((C.hints[s.pc]?).getD [])[i]? = some (.allocAdvice p S) := by rw [hhs]; exact hi
  obtain ⟨sx, s2, hx, h2, hrest⟩ := foldlM_split hget e1
  have hfx := hints_follows _ s sx ⟨hfine.agree.wf, hfine.dl⟩ hx
  have hf2 := runHint_follows hfx.good h2
  have hf1 := hints_follows _ s2 s1 hf2.good hrest
  have hat : HintAt alignA r C e s sx i (.allocAdvice p S) :=
    ⟨hr, hC, ⟨done, st, htr, hch, hha⟩, hnc, hfine, hon, hget, hx,
      fun c v hv ↦ hm.fine.agree.get c v ((Mem.le_trans hf2.le hf1.le).get _ _ hv)⟩
  have hnx := advNext_alignA r C e s sx i p S hat
  have hbi : bufIdx alignA e (s.pc - entOf alignA e.I.t.name) i = k := by
    rw [hoff]; unfold bufIdx; rw [hintsAtOff_eq]; exact hik
  rw [hbi] at hnx
  obtain ⟨n, hn⟩ : ∃ n, e.I.t.bufs[k]? = some n := ⟨_, List.getElem?_eq_getElem hb⟩
  rw [hn] at hnx
  have hw := adv_written hfx.good h2 hnx
  rw [hfx.fp, ← htr.linked.top.1] at hw
  exact Mode.written_mono hf1.le hw

/-! ## The step -/

/-- **The advised pointer cells stay written past each step of the tree track.** -/
theorem wrArith_alignA : WrArith alignA := by
  intro r hr pc fp done e st off pc' fp' st'' done' m htr hpc hk hts hW hnew
  have hA := advChk_alignA e.I.t.name
  have hall : ∀ {oc od of}, (alignA e.I.t.name).code[off]? = some (.jump oc od of) → ∀ o',
      AdvWrTop alignA m e o' := fun h o' k o p S hk _ hb ↦
    hW.1 k o p S hk (lt_of_lt_of_le (adv_lt hA hk) (nextJump_le h rfl (Nat.zero_le _))) hb
  have htop : ∀ {e' : Ent}, e'.I = e.I → ∀ o', AdvWrTop alignA m e o' → AdvWrTop alignA m e' o' :=
    fun hI o' h k o p S hk ho hb ↦ by
      rw [hI] at hk hb ⊢; exact h k o p S hk ho hb
  have hnil : ∀ (J : Inst) (fn : Fn), AdvWrTop alignA m (Ent.enter coreProgram J fn)
      (entOf alignA J.t.name - entOf alignA J.t.name) := fun _ _ _ _ _ _ _ ho _ ↦
    absurd ho (by rw [Nat.sub_self]; exact Nat.not_lt_zero _)
  cases hk with
  | @fall e' ins hI' hnc' hins hjk =>
    show AdvWr alignA m (e' :: st) _
    rw [hI', show entOf alignA e.I.t.name + off + 1 - entOf alignA e.I.t.name = off + 1 by omega]
    refine ⟨htop hI' _ fun k o p S hk ho hb ↦ ?_, hW.2⟩
    rcases Nat.lt_or_ge o off with hlt | hge
    · exact hW.1 k o p S hk hlt hb
    · obtain rfl : o = off := by omega
      exact hnew k p S hk hb
  | @fwd e' oc od of t hI' hnc' hins hz0 hself htgt hlt =>
    exact ⟨htop hI' _ (hall hins _), hW.2⟩
  | @skip e' oc od of c f σ' hI' hnc' hins hc hkp hwhy =>
    exact ⟨htop hI' _ (hall hins _), hW.2⟩
  | @push e' J fn oc od of c s hI' hnc' hins hc hsite hsr hat hJ hkJ hkf hfind hhdr =>
    refine ⟨hnil J fn, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact fun o' ↦ htop hI' o' (hall hins o')
    · exact hW.2 x hx
  | @tail J fn oc od of hins hz0 hnext hlen hJ hkJ hkf hfind hhdr =>
    exact ⟨hnil J fn, hW.2⟩
  | @ret e2 st2 oc _ hins hz0 hmain hst hlen hhdr =>
    subst hst
    exact ⟨hW.2 e2 List.mem_cons_self _, fun x hx ↦ hW.2 x (List.mem_cons_of_mem _ hx)⟩

/-- **Each step keeps `YAlloc alignA`**, from `SizesAt` and the advised sizes' stream the tree's. -/
theorem keepY_allocA_of (hS : SizesAt alignA) (hHP : HeapPops) : KeepY (YAlloc alignA) :=
  keepY_allocA hS curArith_alignA heapArith_alignA (fun r hr ↦ hHP r hr) advWrites_alignA wrArith_alignA

end

end LeanVM.Guest.EndExec
