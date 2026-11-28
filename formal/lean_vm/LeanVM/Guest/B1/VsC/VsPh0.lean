/-
  LeanVM.Guest.B1.VsC.VsPh0

  `verify_sub`'s first three generated windows' hypotheses (`WinsHyp`): the seed, the stream's
  chunk count and buffer, `hint_stream`, the announced sizes' buffer.
-/

module

public import LeanVM.Guest.B1.VsC.VsWinData
public import LeanVM.Guest.B1.VsC.VsW2
public import LeanVM.Guest.B1.VsC.VsWord

/-!
# Phase 0: the seed and the stream

The windows `vsA_w0` (statements `0 ..< 36`), `vsA_w1` (statement `36`, `hint_stream`) and `vsA_w2`
(statements `37 ..< 69`) of `wA`. `vsPh0_wins`: on `vsVal rd0 w args`, with the oracle placing the
`HeapBuf`s from `st.a` (`hwA`, `hw56`), the stream `p ≤ 32` chunks (`hw42`) of the words `ws` that `rd0`
and every memory holding `st.O` read at the stream's buffer, the next six words at the sizes' buffer,
the windows' hypotheses hold, their `K` at the state after them: the `HeapBuf` cursor past the
`830 + 256 p` words, the callees' cursor past `hint_stream`, its pops `hsQ ws p` appended.

`atomsOf_map`: a list of atom statements' atoms.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

theorem atomsOf_map : ∀ (as : List Atom), atomsOf (as.map Stmt.atom) = as
  | [] => rfl
  | a :: as => by rw [List.map_cons, atomsOf, atomsOf_map as]

theorem lowW_pow {k m : ℕ} (h : m < 2 ^ k) : LowW k (gen ^ m) := ⟨m, h, rfl⟩

theorem vsA_w0_eq : vsA_w0 = .run vsW0 := by
  rw [vsA_w0, List.drop_zero, vsW0_eq, atomsOf_map]

theorem vsA_w1_eq : vsA_w1 = .call vsW1s := by
  rw [vsA_w1]
  have h := vsW1_eq
  cases e : vsA.drop 36 with
  | nil => rw [e] at h; simp at h
  | cons s ss => rw [e] at h; simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at h; rw [h.1]; rfl

theorem vsA_w2_eq : vsA_w2 = .run vsW2 := by
  rw [vsA_w2, vsW2_eq, atomsOf_map]

theorem vsW0_pure : vsW0.filter pureAsks = [vsW0rc] := by decide +kernel

theorem vsW0_mem : vsW0.filter memAsks = [] := by decide +kernel

theorem vsW2_pure : vsW2.filter pureAsks = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsW2_memx : ((vsW2.filter memAsks).all fun a => vsW2x.contains a) = true := by decide +kernel

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

/-- The stream's chunk count's range check's quotient: `g^(32 - p)`. -/
theorem vsW0_44 (ha : args.length = 6) {p : ℕ} (hp : p ≤ 32) (hw42 : w 42 = gen ^ p) :
    vsVal rd0 w args (.n 42) = gen ^ p ∧ vsVal rd0 w args (.n 44) = gen ^ (32 - p) := by
  have h42 : vsVal rd0 w args (.n 42) = gen ^ p := (vsVal_42 ha).trans hw42
  have h43 : (vsVal rd0 w args) (.n 43) = gen ^ 32 := by
    have := vsW0_good (rd0 := rd0) (w := w) ha (a := .const (.n 43) (word 4294967296 0))
      (by simp [vsW0, vsW0a])
    simp only [Good] at this
    rw [this]; exact wordG (j := 32) (by norm_num)
  have hg := vsW0_good (rd0 := rd0) (w := w) (args := args) ha (a := vsW0rc) (by simp [vsW0])
  have := hg.2.2
  simp only [show (V.n 43).idx < (V.n 44).idx from by decide, ↓reduceIte] at this
  exact ⟨h42, by rw [this, h43, h42, pow_sub₀ _ Value.gen_ne_zero hp]⟩

end

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **Window `0`'s hypotheses**: the `HeapBuf` bases, the range check `p ≤ 32`. -/
theorem vsW0_runHyp (hk : 6 ≤ k) (ha : args.length = 6) {p a : ℕ} (hp : p ≤ 32) (hw42 : w 42 = gen ^ p)
    (hwA : [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55].map w =
      (bases a (vsSz0 ++ [256 * p])).map (fun b => ofK (addressOfIndex b)))
    {D : ℕ → Prop} {O : Reader → Prop} :
    RunHyp k (vsVal rd0 w args) w a Own R D Pre O vsW0 ∧
      (allocs (vsVal rd0 w args) (vsW0.map Ev.atom)).sum = 824 + 256 * p := by
  have h54 := vsW0_54 (rd0 := rd0) (w := w) ha hw42
  have hlog : logG ((vsVal rd0 w args) (.n 54)) = 256 * p := by
    rw [h54, Value.gen_pow_eq_ofK, logG_spec (by omega)]
  have hal : allocs (vsVal rd0 w args) (vsW0.map Ev.atom) = vsSz0 ++ [256 * p] := by rw [vsW0_allocs, hlog]
  have hk2 : ∀ m, m ≤ 32 → m < 2 ^ k := fun m hm =>
    lt_of_le_of_lt hm (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk))
  obtain ⟨h42, h44⟩ := vsW0_44 (rd0 := rd0) ha hp hw42
  refine ⟨RunHyp.of_asks ?_ (by intro A hA; rw [vsW0_loadAddrs] at hA; simp at hA)
    (by intro A hA; rw [vsW0_hintAddrs] at hA; simp at hA) ?_ (fun rd _ _ _ x hx => by
      rw [vsW0_mem] at hx; simp at hx), by rw [hal, List.sum_append, List.sum_singleton]; rfl⟩
  · rw [hal]
    have e : (allocDsts (vsW0.map Ev.atom)).map (fun v => w v.idx) =
        [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55].map w := by
      rw [← vsW0_allocDsts, List.map_map]; rfl
    rw [e, hwA]
  · intro x hx
    rw [vsW0_pure, List.mem_singleton] at hx
    subst hx
    exact ⟨by rw [h42]; exact lowW_pow (hk2 p hp), by rw [h44]; exact lowW_pow (hk2 _ (by omega))⟩

/-- **Window `2`'s hypotheses**: the sizes' buffer at the cursor, the stream's words `0 ..< 8` loaded,
words `1 ..< 7` stored into it. -/
theorem vsW2_runHyp (ha : args.length = 6) {s a : ℕ} (hw55 : w 55 = ptrAt s) (hw56 : w 56 = ptrAt a)
    (ws : List E) (hws : 8 ≤ ws.length) (h0 : ReadsAt rd0 (ptrAt s) ws) {D : ℕ → Prop} {O : Reader → Prop}
    (hOs : ∀ j < 8, Own (s + j)) (hOb : ∀ j < 6, Own (a + j))
    (hrd : ∀ rd, O rd → ReadsAt rd (ptrAt s) ws ∧ ReadsAt rd (ptrAt a) ((ws.drop 1).take 6)) :
    RunHyp k (vsVal rd0 w args) w a Own R D Pre O vsW2 := by
  set σ0 := vsVal rd0 w args with hσ0
  obtain ⟨fl, -, -, fS⟩ := vsW2_facts
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
  refine RunHyp.of_asks ?_ ?_ (by intro A hA; rw [vsW2_hintAddrs] at hA; simp at hA)
    (by intro x hx; rw [vsW2_pure] at hx; simp at hx) ?_
  · rw [vsW2_allocDsts, vsW2_allocs]
    simp only [List.map_cons, List.map_nil, bases, hw56]
  · intro A hA
    obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA
    have hc := List.all_eq_true.mp vsW2_loads _ hm
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    rcases hc with ⟨rfl, ho'⟩ | ⟨rfl, ho'⟩
    · exact ⟨s + off, by rw [p55, ptrAt, B1.Main.addr_ofK], Or.inl (hOs off ho')⟩
    · exact ⟨a + off, by rw [p56, ptrAt, B1.Main.addr_ofK], Or.inl (hOb off ho')⟩
  · intro rd _ _ ho x hx
    obtain ⟨h1s, h1b⟩ := hrd rd ho
    have hx' := List.contains_iff_mem.mp (List.all_eq_true.mp vsW2_memx x hx)
    rw [vsW2x, List.mem_append, List.mem_map, List.mem_map] at hx'
    rcases hx' with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · show LoadHolds rd (σ0 (.n 55)) q.2 (σ0 (.n q.1))
      rw [p55, val q hq (hoff q hq)]
      exact h1s q.2 (hoff q hq)
    · have hq' : q ∈ vsW2ld := List.mem_of_mem_take (List.mem_of_mem_tail hq)
      have hq1 : 1 ≤ q.2 ∧ q.2 < 7 := by
        have := List.all_eq_true.mp o7 q hq; simpa only [decide_eq_true_eq] using this
      show LoadHolds rd (σ0 (.n 56)) (q.2 - 1) (σ0 (.n q.1))
      have hl : q.2 - 1 < ((ws.drop 1).take 6).length := by rw [hb]; omega
      have e : ((ws.drop 1).take 6)[q.2 - 1] = ws[q.2]'(hoff q hq') := by
        have e1 : 1 + (q.2 - 1) = q.2 := by omega
        simp only [List.getElem_take, List.getElem_drop, e1]
      rw [p56, val q hq' (hoff q hq'), ← e]
      exact h1b (q.2 - 1) hl

/-- **Phase 0's windows' hypotheses** (`vsA_w0`, `vsA_w1`, `vsA_w2`): the static `HeapBuf`s and the
stream's from `st.a`, its `p ≤ 32` chunks of the words `ws`, `hint_stream` at the callees' cursor, the
sizes' buffer after the stream's; `K` at the state after them. -/
theorem vsPh0_wins (hk : 6 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop} {p : ℕ} (hp : p ≤ 32)
    (hw42 : w 42 = gen ^ p)
    (hwA : [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 55].map w =
      (bases st.a (vsSz0 ++ [256 * p])).map (fun b => ofK (addressOfIndex b)))
    (hw55 : w 55 = ptrAt (st.a + 824)) (hw56 : w 56 = ptrAt (st.a + (824 + 256 * p)))
    (ws : List E) (hws : ws.length = 256 * p) (h8 : 8 ≤ ws.length) (h0 : ReadsAt rd0 (ptrAt (st.a + 824)) ws)
    (hOs : ∀ j < 256 * p, Own (st.a + 824 + j)) (hOb : ∀ j < 6, Own (st.a + (824 + 256 * p) + j))
    (hO : ∀ rd, st.O rd → ReadsAt rd (ptrAt (st.a + 824)) ws ∧
      ReadsAt rd (ptrAt (st.a + (824 + 256 * p))) ((ws.drop 1).take 6))
    (hK : K ⟨st.a + (824 + 256 * p) + 6,
      allocBase (al hsLoopName) (allocBase (al "hint_stream") st.kc + fs "hint_stream") + hsB fs p,
      fun rd => st.O rd ∧ True, fun i => st.D i ∨ False, st.Qs ++ [hsQ ws p]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsA_w0, vsA_w1, vsA_w2] st K := by
  obtain ⟨h0r, hsum⟩ := vsW0_runHyp (Own := Own) (R := R) (Pre := Pre) (D := st.D) (O := st.O) hk ha hp hw42 hwA
  rw [vsA_w0_eq, vsA_w1_eq, vsA_w2_eq, WinsHyp]
  refine ⟨h0r, ?_⟩
  rw [hsum, WinsHyp]
  have hargs : (argsOf vsW1s).map (vsVal rd0 w args) = [ptrAt (st.a + 824), gen ^ p] := by
    simp only [vsW1s, argsOf, List.map_cons, List.map_nil, vsVal_55 ha, vsVal_42 ha, hw55, hw42]
  refine ⟨"hint_stream", hsQ ws p, fs "hint_stream",
    allocBase (al hsLoopName) (allocBase (al "hint_stream") st.kc + fs "hint_stream") + hsB fs p, fun i => (R i ∨ Own i) ∨ st.D i, fun _ => False,
    fun _ => True, rfl, fun i h => h, ?_, ?_⟩
  · rw [hargs]
    exact (hint_stream_completeA fs al cert k (st.a + 824) ws p _ (by omega)
      (fun j hj => Or.inl (Or.inr (hOs j hj))) _ _ le_rfl).mono (fun _ h => h) (fun _ h => h)
      (fun _ h => h) (fun rd h => ⟨(hO rd h.2).1, hws⟩) (fun _ _ _ h => h)
  · rw [WinsHyp]
    refine ⟨vsW2_runHyp ha hw55 hw56 ws h8 h0 (fun j hj => hOs j (by omega)) hOb
      (fun rd ho => hO rd ho.1), ?_⟩
    rw [WinsHyp, vsW2_allocs]
    exact hK

end

end
end LeanVM.Guest.B1.VsC
