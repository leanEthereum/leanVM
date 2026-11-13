module

public import LeanVM.Guest.Mode.SoundCall

/-!
# Calls, returns and tail calls

`entryOk_sound`: what a caller knows at a call gives the state the callee's walk starts from
(`entryAbs`), given the callee's termination facts and the jump table's run. `atCall_sound`,
`afterCall_sound`: the callee's termination facts and its guarantees at return (`RetHolds`, and its
accumulated runs) moved out to the caller. `retOk_sound`: what a walk knows at a return gives the
function's guarantees and its loop points. `tailOk_sound`: a loop's tail call, its entry and the
steps of its counters and runs.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- What a function guarantees at a return, over its frame. -/
def RetHolds (s : St) (G : Sig) : Prop :=
  (∀ o ∈ G.ret, s.mem.written (s.fp + o) = true) ∧ (∀ m ∈ G.post, HW s m) ∧ ∀ r ∈ G.postR, RW s r

theorem Holds.foldl {s : St} {α : Type} (f : Abs → α → Abs) :
    ∀ (l : List α) {A : Abs}, Holds s A → (∀ A a, a ∈ l → Holds s A → Holds s (f A a)) →
      Holds s (l.foldl f A)
  | [], _, h, _ => h
  | a :: l, A, h, hf => Holds.foldl f l (hf A a (List.mem_cons_self ..) h)
      fun A' a' hm h' ↦ hf A' a' (List.mem_cons_of_mem _ hm) h'

theorem Holds.addH_cell {s : St} {A : Abs} (h : Holds s A) (hfp : s.fp < maxCells) {k : Mono} {v : E}
    {x : ℕ} (hk : MonoVal s k v) (hx : Names v x) (hw : s.mem.written x = true) : Holds s (A.addH k) :=
  h.addH ⟨v, x, hk, hx, hw⟩ fun _ hd ↦ by rw [← own_names hfp hd hk hx]; exact hw

/-! ## A cell the walk knows written has a word -/

theorem BsVal.remove_inv {s : St} {b : Base} {e : ℕ} {u : E} (hu : BaseVal s b u) :
    ∀ {bs rest : List (Base × ℕ)} {w : E}, removeBs (b, e) bs = some rest → BsVal s rest w →
      BsVal s bs (u ^ e * w)
  | [], _, _, h, _ => by simp [removeBs] at h
  | (b', e') :: bs, rest, w, h, hw => by
    unfold removeBs at h
    by_cases hq : b.beq b' = true
    · rw [ite_eq_left hq] at h
      by_cases he : (e == e') = true
      · rw [ite_eq_left he] at h
        cases h
        obtain rfl := Base.beq_eq hq
        obtain rfl := beq_iff_eq.mp he
        exact ⟨u, w, hu, hw, rfl⟩
      · rw [ite_eq_right he] at h; cases h
    · rw [ite_eq_right hq] at h
      obtain ⟨rest', hr, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨u', w', h1, h2, rfl⟩ := hw
      exact ⟨u', u ^ e * w', h1, BsVal.remove_inv hu hr h2, by ring⟩

/-- A product a run names at an exponent with a value has a word. -/
theorem Rng.idxOf_val {s : St} {r : Rng} {k : Mono} {i : Idx} (h : r.idxOf k = some i) {vq : E}
    (hq : MonoVal s r.q vq) {xi : ℕ} (hi : IdxVal s i xi) : ∃ vk, MonoVal s k vk := by
  unfold Rng.idxOf at h
  by_cases hc : (k.fp == r.q.fp && decide (r.q.k + r.d ≤ k.k) && (k.k - r.q.k - r.d) % r.S == 0 &&
      decide (0 < r.S)) = true
  swap
  · rw [ite_eq_right hc] at h; cases h
  rw [ite_eq_left hc] at h
  obtain ⟨wq, hwq, -⟩ := hq
  by_cases hb : bsBeq k.bs r.q.bs = true
  · exact ⟨_, wq, by rw [bsBeq_eq hb]; exact hwq, rfl⟩
  · rw [ite_eq_right hb] at h
    split at h
    · rename_i x e _
      split at h
      · rename_i rest hr
        by_cases hrq : bsBeq rest r.q.bs = true
        · rw [ite_eq_left hrq] at h
          cases h
          obtain ⟨v, ex, hv, -, -, -⟩ := hi
          rw [bsBeq_eq hrq] at hr
          exact ⟨_, _, BsVal.remove_inv hv hr hwq, rfl⟩
        · rw [ite_eq_right hrq] at h; cases h
      · cases h
    · cases h

theorem inRng1_val {s : St} {A : Abs} (hA : Holds s A) {k : Mono} {r : Rng} (hr : RW s r)
    (h : (match r.idxOf k with
      | some i => A.le r.lo i && A.ltI i r.hi
      | none => false) = true) : ∃ vk, MonoVal s k vk := by
  split at h
  · rename_i i hi
    simp only [Bool.and_eq_true] at h
    obtain ⟨vq, xlo, xhi, h1, -, h3, -⟩ := hr
    obtain ⟨xi, hxi, -⟩ := Abs.ltI_sound hA h.2 h3
    exact Rng.idxOf_val hi h1 hxi
  · simp at h

/-- **A heap cell the walk knows written has a word.** -/
theorem Abs.covered_val {s : St} {A : Abs} (hA : Holds s A) {k : Mono} (h : A.covered k = true) :
    ∃ vk, MonoVal s k vk := by
  unfold Abs.covered at h
  split at h
  · rename_i d hd
    obtain ⟨rfl, -⟩ := Mono.ownCell_eq hd
    exact ⟨_, MonoVal.own d⟩
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain ⟨k', hm, hb⟩ := List.any_eq_true.mp h
      obtain rfl := Mono.beq_eq hb
      obtain ⟨v, -, h1, -⟩ := hA.h _ hm
      exact ⟨v, h1⟩
    · obtain ⟨r, hm, hb⟩ := List.any_eq_true.mp h
      unfold Abs.inRng at hb
      rcases Bool.or_eq_true_iff.mp hb with hb | hb
      · exact inRng1_val hA (hA.r r hm) hb
      · simp only [Bool.and_eq_true] at hb
        exact inRng1_val hA (hA.r r hm).down hb.2

/-- A heap cell the walk knows written: its word, and the written cell it names. -/
theorem Abs.covered_cell {s : St} {A : Abs} (hA : Holds s A) (hwf : s.mem.WF)
    (hu : s.mem.used ≤ maxCells) {k : Mono} (h : A.covered k = true) :
    ∃ vk x, MonoVal s k vk ∧ Names vk x ∧ s.mem.written x = true := by
  obtain ⟨vk, hk⟩ := Abs.covered_val hA h
  obtain ⟨x, hx, hw⟩ := Abs.covered_ex hA hwf hu h hk
  exact ⟨vk, x, hk, hx, hw⟩

/-! ## Entry -/

theorem entry_w {l : List ℕ} : ∀ {t : Exec.Trie Unit} {o : ℕ},
    (l.foldl (fun t o ↦ t.set () Exec.envDepth o) t).get o = some () → o ∈ l ∨ t.get o = some () := by
  induction l with
  | nil => intro t o h; exact Or.inr h
  | cons a l ih =>
    intro t o h
    rcases ih h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases Exec.Trie.get_set h with ⟨rfl, -⟩ | h
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr h

/-- **A call's entry**: what the caller knows, its callee's frame named by `mq`, gives the state the
callee's walk starts from. -/
theorem entryOk_sound {En : Env} {sC sE : St} {A : Abs} {mq : Mono} {G : Sig} (F : Frames sC sE mq)
    (hA : Holds sC A) (h : entryOk A mq G = true) (hjt : RW sE (jtRng En))
    (hT : ∀ p ∈ G.term, LTF sE p.1 p.2) : Holds sE (entryAbs En G) := by
  unfold entryOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hent, hself⟩, hpre⟩, hpreR⟩ := h
  have h0 : Holds sE ⟨G.entry.foldl (fun t o ↦ t.set () Exec.envDepth o) .nil, .nil, .nil, [], G.pre,
      jtRng En :: G.preR, G.term, [], .nil⟩ := {
    w := fun o ho ↦ by
      rcases entry_w ho with ho | ho
      · obtain ⟨ho1, ho2⟩ := hent o ho
        obtain ⟨x, hx, hw⟩ := Abs.covered_ex hA F.wf F.used ho2 (F.mq.shift o)
        rw [← F.names ho1 (F.mq.shift o) hx, F.mem]
        exact hw
      · simp at ho
    v := fun o x ho ↦ by simp at ho
    nz := fun o ho ↦ by simp at ho
    hv := fun p hp ↦ by simp at hp
    h := fun m hm ↦ by
      have := hpre m hm
      split at this
      · rename_i k hk
        simp only [Bool.and_eq_true] at this
        obtain ⟨v, x, hv, hx, hw⟩ := Abs.covered_cell hA F.wf F.used this.2
        exact ⟨v, x, (trMono_iff F hA hk v).mpr hv, hx, by rw [F.mem]; exact hw⟩
      · cases this
    r := fun r hr ↦ by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hjt
      · have := hpreR r hr
        split at this
        · rename_i r' hr'
          exact RW.trDown F hA hr' (Abs.coveredR_sound hA F.wf F.used this)
        · cases this
    lt := hT
    pr := fun p hp ↦ by simp at hp
    xs := fun c a b hc ↦ by simp at hc }
  unfold entryAbs
  dsimp only
  split
  · rename_i o ho
    rw [ho] at hself
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hself
    obtain ⟨ho1, hself⟩ := hself
    split at hself
    · rename_i x hx
      obtain rfl := Val.beq_eq hself
      obtain ⟨w, hw, hmw⟩ := hvGet_cell F hA ho1 hx
      obtain rfl := hmw.unique F.mq
      have hown : MonoVal sE (.own 0) (ofK (g ^ sE.fp)) := by
        have := MonoVal.own (s := sE) 0; rwa [Nat.add_zero] at this
      exact ((h0.addW (written_of_get hw)).addV (x := .m (.own 0)) ⟨_, hw, hown⟩).addNz
        ⟨_, hw, ofK_gpow_ne_zero _⟩
    · cases hself
  · exact h0

/-! ## Calls and returns -/

/-- **A callee's termination facts**, holding at its entry, moved out to the caller. -/
theorem atCall_sound {sC sE : St} {A : Abs} {mq : Mono} {G : Sig} (F : Frames sC sE mq)
    (hA : Holds sC A) (hT : ∀ p ∈ G.term, LTF sE p.1 p.2) : Holds sC (atCall A mq G) := by
  unfold atCall
  refine Holds.foldl _ _ hA fun A p hp hA ↦ ?_
  split
  · rename_i a b ha hb
    obtain ⟨xa, xb, h1, h2, h3⟩ := hT p hp
    exact hA.addLt ⟨xa, xb, idxUp_val F hA ha h1, idxUp_val F hA hb h2, h3⟩
  · exact hA

/-- **After a call**: the caller's state `sC` once the callee, its frame named by `mq` and its state
at return `sR`, guarantees what it does at return, its accumulated runs and its termination facts. -/
theorem afterCall_sound {sC sR : St} {A : Abs} {mq : Mono} {G : Sig} (F : Frames sC sR mq)
    (hA : Holds sC A) (hR : RetHolds sR G) (hL : ∀ r ∈ G.postL, RW sR r)
    (hT : ∀ p ∈ G.term, LTF sR p.1 p.2) : Holds sC (afterCall A mq G) := by
  unfold afterCall
  dsimp only
  refine atCall_sound F (Holds.foldl _ _ (Holds.foldl _ _ (Holds.foldl _ _ hA ?_) ?_) ?_) hT
  · intro A o ho hA
    have hw := hR.1 o ho
    obtain ⟨u, hu⟩ := Mem.get_of_written hw
    have hlt := F.get_lt hu
    rw [F.mem] at hw
    exact hA.addH_cell F.fpC (F.mq.shift o) (names_shift (by simp) hlt) hw
  · intro A m hm hA
    split
    · rename_i k hk
      obtain ⟨v, x, h1, h2, h3⟩ := hR.2.1 m hm
      exact hA.addH_cell F.fpC ((trMono_iff F hA hk v).mp h1) h2 (F.mem ▸ h3)
    · exact hA
  · intro A r hr hA
    split
    · rename_i r' hr'
      have hrw : RW sC r' := RW.trUp F hA hr' (by
        rcases List.mem_append.mp hr with h | h
        exacts [hR.2.2 r h, hL r h])
      exact { hA with
        r := fun r'' hm ↦ by
          rcases List.mem_cons.mp hm with rfl | hm
          exacts [hrw, hA.r r'' hm] }
    · exact hA

/-- A loop's points: each run's point at its counter's start is written. -/
theorem loopOk_sound {s : St} {A : Abs} {G : Sig} (hA : Holds s A) (hfp : s.fp < maxCells)
    (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) (h : loopOk A G = true) :
    ∀ r ∈ G.postL, HW s r.first := by
  have F := Frames.own hfp hwf hu rfl (Nat.add_zero _).symm hfp
  intro r hr
  have := List.all_eq_true.mp h r hr
  split at this
  · rename_i k hk
    obtain ⟨v, x, hv, hx, hw⟩ := Abs.covered_cell hA hwf hu this
    exact ⟨v, x, (trMono_iff F hA hk v).mpr hv, hx, hw⟩
  · cases this

/-- **A return**: what the walk knows gives the function's guarantees and its loop points. -/
theorem retOk_sound {s : St} {A : Abs} {G : Sig} (hA : Holds s A) (hfp : s.fp < maxCells)
    (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) (h : retOk A G = true) :
    RetHolds s G ∧ ∀ r ∈ G.postL, HW s r.first := by
  have F := Frames.own hfp hwf hu rfl (Nat.add_zero _).symm hfp
  unfold retOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hL, hret⟩, hpost⟩, hpostR⟩ := h
  refine ⟨⟨fun o ho ↦ hA.written (hret o ho), fun m hm ↦ ?_, fun r hr ↦ ?_⟩,
    loopOk_sound hA hfp hwf hu hL⟩
  · have := hpost m hm
    split at this
    · rename_i k hk
      obtain ⟨v, x, hv, hx, hw⟩ := Abs.covered_cell hA hwf hu this
      exact ⟨v, x, (trMono_iff F hA hk v).mpr hv, hx, hw⟩
    · cases this
  · have := hpostR r hr
    split at this
    · rename_i r' hr'
      exact RW.trDown F hA hr' (Abs.coveredR_sound hA hwf hu this)
    · cases this

/-- **A loop's tail call** into the frame `fp·g^e`: the next iteration's entry state holds, its
counters are this one's moved up (`termStep`), and each run it accumulates, moved out, is this one's
from one further. -/
theorem tailOk_sound {En : Env} {s sE : St} {A : Abs} {e : ℕ} {G : Sig} (hA : Holds s A)
    (hfp : s.fp < maxCells) (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) (hm : sE.mem = s.mem)
    (hE : sE.fp = s.fp + e) (hEfp : sE.fp < maxCells) (h : tailOk A e G = true)
    (hjt : RW sE (jtRng En)) (hT : ∀ p ∈ G.term, LTF sE p.1 p.2) :
    Holds sE (entryAbs En G) ∧ termStep A e G = true ∧
      ∀ r ∈ G.postL, ∃ r', trRngUp A (.own e) r = some r' ∧ r' = ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩ := by
  unfold tailOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hent, hts⟩, hL⟩ := h
  refine ⟨entryOk_sound (Frames.own hfp hwf hu hm hE hEfp) hA hent hjt hT, hts, fun r hr ↦ ?_⟩
  have := hL r hr
  split at this
  · rename_i r' hr'
    exact ⟨r', hr', Rng.beq_eq this⟩
  · cases this

end

end LeanVM.Guest.Mode
