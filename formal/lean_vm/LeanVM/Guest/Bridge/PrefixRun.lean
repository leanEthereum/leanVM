/-
  LeanVM.Guest.Bridge.PrefixRun

  The prefix class against the run: a frame of a prefix function at offset `off` up to its first jump is at its body position past the ISA flow hints at offsets below `off`, and the reference's fall-through step keeps it so, the hints at `off` each compiling the core hint whose entry the track pops.
-/

module

public import LeanVM.Guest.Bridge.RefTrace
public import LeanVM.Guest.Bridge.PrefixTrack

/-!
# The prefix class against the run

`flowBelow d off`: the number of ISA flow hints of the advice `d` at offsets below `off`. On a function passing `prefixOk`, the advice's pcs increase from its entry, so its flow hints are sorted by offset (`isaFlow_sorted`) and the `j`-th is at an offset below `off` exactly when `j < flowBelow d off` (`lt_flowBelow_iff`): the hints at offset `off` are those of indices `flowBelow d off ≤ j < flowBelow d (off + 1)` (`flow_at_off`).

`prefixPos body d off`, the body position at offset `off` of a frame of a prefix function, is `flowPos body (flowBelow d off)`: past its leading flow hints at offsets below `off`. At offset `0` it is the body (`prefixPos_zero`). `TrackOk.flow_run`: moves take the frame from `flowPos body m` to `flowPos body m'`, popping the entries of core hints the ISA flow hints `m ≤ j < m'` compile, in order (`prefix_track`, iterated); `TrackOk.prefix_hints`: those of offset `off`.

`prefix_fall`: for an alignment `al` placing the prefix function `f` at `prefixPos` up to its first jump, a frame of `f` at offset `off` below its first jump, at the registers, steps by the reference to `pc + 1` in the same frame (every instruction before the first jump falls through: `execute_iff_holds`), and moves through the hints at `off`, each compiling the hint whose entry it pops, keep the track against the run (`RefOk`) at `pc + 1`.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The ISA flow hints of `d` at offsets below `off`. -/
def flowBelow (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (off : ℕ) : ℕ :=
  (isaFlow d).countP fun p ↦ decide (p.1 < off)

/-- **A prefix function's body position at offset `off`**: past its flow hints at offsets below. -/
def prefixPos (body : List Stmt) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (off : ℕ) : List Stmt :=
  flowPos body (flowBelow d off)

end

public section

/-! ## The flow hints by offset -/

theorem pcsUp_head : ∀ {a : ℕ × List Prover.Exec.Hint} {l : List (ℕ × List Prover.Exec.Hint)},
    pcsUp (a :: l) = true → ∀ x ∈ l, a.1 < x.1
  | _, [], _, _, hx => absurd hx List.not_mem_nil
  | a, b :: l, h, x, hx => by
    simp only [pcsUp, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (pcsUp_head h.2 x hx)

theorem pcsUp_pairwise : ∀ {l : List (ℕ × List Prover.Exec.Hint)}, pcsUp l = true →
    l.Pairwise fun a b ↦ a.1 < b.1
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    refine List.Pairwise.cons (pcsUp_head h) (pcsUp_pairwise ?_)
    simp only [pcsUp, Bool.and_eq_true] at h
    exact h.2

/-- **The flow hints are sorted by offset**, the advice's pcs increasing from the entry. -/
theorem isaFlow_sorted {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hup : pcsUp d.2.2 = true)
    (hge : ∀ p ∈ d.2.2, d.1 ≤ p.1) : (isaFlow d).Pairwise fun a b ↦ a.1 ≤ b.1 := by
  rw [isaFlow, List.pairwise_flatMap]
  refine ⟨fun p _ ↦ ?_, ?_⟩
  · rw [flowAt, List.pairwise_map]
    exact List.Pairwise.imp (fun _ ↦ le_refl _) (List.pairwise_of_forall (fun _ _ ↦ trivial))
  · refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab x hx y hy ↦ ?_) (pcsUp_pairwise hup)
    simp only [flowAt, List.mem_map] at hx hy
    obtain ⟨_, -, rfl⟩ := hx
    obtain ⟨_, -, rfl⟩ := hy
    have := hge a ha
    have := hge b hb
    dsimp only
    omega

/-- In a list sorted by offset, the `i`-th is below `off` exactly when `i` is below the count of
those below `off`. -/
theorem lt_countP_iff {α : Type} : ∀ {L : List (ℕ × α)}, (L.Pairwise fun a b ↦ a.1 ≤ b.1) → ∀ (off i : ℕ)
    (hi : i < L.length), L[i].1 < off ↔ i < L.countP fun p ↦ decide (p.1 < off)
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | a :: l, h, off, i, hi => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
    by_cases hao : a.1 < off
    · rw [List.countP_cons_of_pos (by simpa using hao)]
      cases i with
      | zero => simp [hao]
      | succ i =>
        rw [List.getElem_cons_succ, lt_countP_iff hl off i (by simpa using hi)]
        omega
    · have h0 : l.countP (fun p ↦ decide (p.1 < off)) = 0 := by
        rw [List.countP_eq_zero]
        intro x hx
        have := ha x hx
        simp only [decide_eq_true_eq]
        omega
      rw [List.countP_cons_of_neg (by simpa using hao), h0]
      cases i with
      | zero => simpa using hao
      | succ i =>
        rw [List.getElem_cons_succ]
        have := ha _ (List.getElem_mem (l := l) (n := i) (by simpa using hi))
        simp only [Nat.not_lt_zero, iff_false, not_lt]
        omega

theorem lt_flowBelow_iff {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hup : pcsUp d.2.2 = true)
    (hge : ∀ p ∈ d.2.2, d.1 ≤ p.1) (off j : ℕ) (hj : j < (isaFlow d).length) :
    (isaFlow d)[j].1 < off ↔ j < flowBelow d off :=
  lt_countP_iff (isaFlow_sorted hup hge) off j hj

theorem flowBelow_le_length (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (off : ℕ) :
    flowBelow d off ≤ (isaFlow d).length :=
  List.countP_le_length

theorem flowBelow_mono (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) {a b : ℕ} (h : a ≤ b) :
    flowBelow d a ≤ flowBelow d b :=
  List.countP_mono_left fun x _ hx ↦ by simp only [decide_eq_true_eq] at hx ⊢; omega

/-- **The hints at offset `off`**: the flow hints of indices from `flowBelow d off` to
`flowBelow d (off + 1)`. -/
theorem flow_at_off {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hup : pcsUp d.2.2 = true)
    (hge : ∀ p ∈ d.2.2, d.1 ≤ p.1) (off j : ℕ) (hj : j < (isaFlow d).length) :
    (isaFlow d)[j].1 = off ↔ flowBelow d off ≤ j ∧ j < flowBelow d (off + 1) := by
  have h1 := lt_flowBelow_iff hup hge off j hj
  have h2 := lt_flowBelow_iff hup hge (off + 1) j hj
  omega

theorem flowBelow_zero {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} : flowBelow d 0 = 0 := by
  simp [flowBelow]

theorem prefixPos_zero (body : List Stmt) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) :
    prefixPos body d 0 = body := by
  rw [prefixPos, flowBelow_zero, flowPos_zero]

theorem prefixOk_up {loc : ℕ → ℕ} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : prefixOk loc body code d = true) :
    pcsUp d.2.2 = true ∧ ∀ p ∈ d.2.2, d.1 ≤ p.1 := by
  simp only [prefixOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2, h.1.1.2⟩

/-! ## Moves over the flow hints -/

variable {P : Core.Program} {rd : Reader} {Is : List Inst} {T : Tree}

/-- **From flow position `m` to `m'`**: moves pop the entries of core hints the ISA flow hints
`m ≤ j < m'` compile, in order. -/
theorem TrackOk.flow_run {loc : ℕ → ℕ} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : prefixOk loc body code d = true) :
    ∀ (k m : ℕ), m + k ≤ (isaFlow d).length → ∀ {done : List Pop} {e : Ent} {st : List Ent},
      TrackOk P rd Is T done (e :: st) → e.pos = flowPos body m →
      ∃ hcs : List Core.Hint, hcs.length = k ∧
        (∀ i, i < k → ∀ (hi' : m + i < (isaFlow d).length) (hc : i < hcs.length),
          compiles loc hcs[i] (isaFlow d)[m + i].2 = true) ∧
        ∃ e', Relation.ReflTransGen (Move P rd Is) (done, e :: st)
            (done ++ hcs.flatMap (Core.Hint.pops rd e.σ), e' :: st) ∧
          e'.pos = flowPos body (m + k) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.nb = e.nb
  | 0, m, _, done, e, st, _, hpos =>
    ⟨[], rfl, fun _ hi ↦ absurd hi (Nat.not_lt_zero _), e, by simpa using Relation.ReflTransGen.refl,
      hpos, rfl, rfl, rfl⟩
  | k + 1, m, hk, done, e, st, h, hpos => by
    obtain ⟨hc, hcomp, -, e1, hr1, hpos1, hI1, hfn1, hnb1⟩ := prefix_track hpre (m := m) (by omega) h hpos
    obtain ⟨hcs, hl, hcs', e', hr', hpos', hI', hfn', hnb'⟩ :=
      TrackOk.flow_run hpre k (m + 1) (by omega) (h.moves hr1) hpos1
    have hσ : e1.σ = e.σ := by simp only [Ent.σ, hI1]
    refine ⟨hc :: hcs, by simp [hl], fun i hi hi' hci ↦ ?_, e', hr1.trans ?_, by rw [hpos']; congr 1; omega,
      hI'.trans hI1, hfn'.trans hfn1, hnb'.trans hnb1⟩
    · cases i with
      | zero => exact hcomp
      | succ i =>
        have := hcs' i (by omega) (by omega) (by simpa using hci)
        simp only [List.getElem_cons_succ, show m + (i + 1) = m + 1 + i by omega]
        exact this
    · rw [hσ] at hr'
      simpa [List.append_assoc] using hr'

/-- **The hints at offset `off`**: from the position at `off`, moves pop the entries of core hints
the ISA flow hints at `off` compile, in order, to the position at `off + 1`. -/
theorem TrackOk.prefix_hints {loc : ℕ → ℕ} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : prefixOk loc body code d = true) (off : ℕ)
    {done : List Pop} {e : Ent} {st : List Ent} (h : TrackOk P rd Is T done (e :: st))
    (hpos : e.pos = prefixPos body d off) :
    ∃ hcs : List Core.Hint, hcs.length = flowBelow d (off + 1) - flowBelow d off ∧
      (∀ i (hi : i < hcs.length) (hi' : flowBelow d off + i < (isaFlow d).length),
        (isaFlow d)[flowBelow d off + i].1 = off ∧ compiles loc hcs[i] (isaFlow d)[flowBelow d off + i].2 = true) ∧
      ∃ e', Relation.ReflTransGen (Move P rd Is) (done, e :: st)
          (done ++ hcs.flatMap (Core.Hint.pops rd e.σ), e' :: st) ∧
        e'.pos = prefixPos body d (off + 1) ∧ e'.I = e.I ∧ e'.fn = e.fn ∧ e'.nb = e.nb := by
  obtain ⟨hup, hge⟩ := prefixOk_up hpre
  have hm := flowBelow_mono d (Nat.le_add_right off 1)
  have hl := flowBelow_le_length d (off + 1)
  obtain ⟨hcs, hlen, hcomp, e', hr, hpos', hI, hfn, hnb⟩ :=
    h.flow_run hpre (flowBelow d (off + 1) - flowBelow d off) (flowBelow d off) (by omega) hpos
  refine ⟨hcs, hlen, fun i hi hi' ↦ ⟨(flow_at_off hup hge off _ hi').mpr ⟨by omega, by omega⟩,
    hcomp i (by omega) hi' hi⟩, e', hr, ?_, hI, hfn, hnb⟩
  rw [hpos', prefixPos]
  congr 1
  omega

/-! ## The fall-through against the run -/

variable {M : ℕ → E} {ent : String → ℕ} {al : String → ℕ → Option (List Stmt)}

/-- **A prefix function's fall-through against the run**: a frame of the prefix function `f`, at the
registers at offset `off` below its first jump, where the alignment places `f` at `prefixPos` up to
its first jump: the reference steps to `pc + 1` in the same frame, and moves through the hints at
`off`, each compiling the core hint whose entry they pop, keep the track against the run there. -/
theorem prefix_fall {loc : ℕ → ℕ} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : prefixOk loc body code d = true) {f : String}
    (hal : ∀ off ≤ firstJump code, al f off = some (prefixPos body d off))
    {prog : LeanIsaProgram} {κ : ℕ} {img : MemoryImage κ} {pc fp off : ℕ} {done : List Pop} {e : Ent}
    {st : List Ent} (h : RefOk P rd Is T M ent al pc fp (done, e :: st)) (hname : e.I.t.name = f)
    (hpc : pc = ent f + off) (hj : off < firstJump code)
    (hfetch : prog.fetch (addressOfIndex pc) =
      some (code[off]'(Nat.lt_of_lt_of_le hj List.findIdx_le_length)).toLeanIsaInstruction)
    {r' : Registers K} (hstep : step prog img (regs pc fp) = some r') :
    r' = regs (pc + 1) fp ∧ ∃ hcs : List Core.Hint,
      hcs.length = flowBelow d (off + 1) - flowBelow d off ∧
      (∀ i (hi : i < hcs.length) (hi' : flowBelow d off + i < (isaFlow d).length),
        (isaFlow d)[flowBelow d off + i].1 = off ∧ compiles loc hcs[i] (isaFlow d)[flowBelow d off + i].2 = true) ∧
      ∃ e', Relation.ReflTransGen (Move P rd Is) (done, e :: st)
          (done ++ hcs.flatMap (Core.Hint.pops rd e.σ), e' :: st) ∧
        RefOk P rd Is T M ent al (pc + 1) fp (done ++ hcs.flatMap (Core.Hint.pops rd e.σ), e' :: st) := by
  have hjmp : (code[off]'(Nat.lt_of_lt_of_le hj List.findIdx_le_length)).isJump = false :=
    List.not_of_lt_findIdx hj
  rw [step_of_fetch_eq_some hfetch] at hstep
  have hr' := ((execute_iff_holds hjmp).mp hstep).2
  refine ⟨hr', ?_⟩
  obtain ⟨-, off0, hpc0, hal0⟩ := h.linked.top
  rw [hname] at hpc0 hal0
  have h0 : off0 = off := by omega
  rw [h0, hal off hj.le] at hal0
  obtain ⟨hcs, hlen, hcomp, e', hr, hpos', hI, -, -⟩ := h.track.prefix_hints hpre off (Option.some.inj hal0).symm
  refine ⟨hcs, hlen, hcomp, e', hr, h.within hr hI ⟨off + 1, ?_, ?_⟩⟩
  · rw [hI, hname, hpc]; rfl
  · rw [hI, hname, hal (off + 1) hj, hpos']

end

end LeanVM.Guest.Bridge
