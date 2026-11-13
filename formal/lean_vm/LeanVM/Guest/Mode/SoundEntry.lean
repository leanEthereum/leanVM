module

public import LeanVM.Guest.Mode.SoundCall

/-!
# Calls, returns and tail calls

`entryOk_sound`: what a caller knows at a call gives the state the callee's walk starts from
(`entryAbs`), given the callee's termination facts and the jump table's run. `atCall_sound`,
`afterCall_sound`: the callee's termination facts and its guarantees at return (`RetHolds`, and its
accumulated runs) moved out to the caller. `retOk_sound`: what a walk knows at a return gives the
function's guarantees and its loop points. `tailOk_sound`: a loop's tail call, its entry and the
steps of its counters and runs. `coveredP_sound`: a run of pointers the walk knows is.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- What a function guarantees at a return, over its frame. -/
def RetHolds (s : St) (G : Sig) : Prop :=
  (∀ o ∈ G.ret, s.mem.written (s.fp + o) = true) ∧ (∀ m ∈ G.post, HW s m) ∧
    (∀ r ∈ G.postR, RW s r) ∧ (∀ q ∈ G.postP, PW s q.1 q.2) ∧
    ∀ p ∈ G.retV, ∃ u, s.mem.get (s.fp + p.1) = some u ∧ MonoVal s p.2 u

/-- The heap cell `k` names holds a pointer with the cells `os` past it written. -/
def HP (s : St) (k : Mono) (os : List ℕ) : Prop :=
  ∃ v x, MonoVal s k v ∧ Names v x ∧ PtrW s.mem x os

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

/-- A run's point at its counter's start names its cell at the counter's exponent. -/
theorem Rng.first_val {s : St} {r : Rng} {y : ℕ} (hy : IdxVal s r.lo y) {vq : E}
    (hq : MonoVal s r.q vq) : MonoVal s r.first (vq * ofK (g ^ (r.S * y + r.d))) := by
  unfold Rng.first
  split
  · rename_i c hc
    rw [hc] at hy
    rw [show y = c from hy]
    exact hq.shift _
  · rename_i x c hc
    rw [hc] at hy
    obtain ⟨u, e, hu, rfl, -, rfl⟩ := hy
    have hx : MonoVal s ⟨0, 0, [(x, r.S)]⟩ (ofK (g ^ e) ^ r.S) :=
      ⟨_, ⟨_, 1, hu, rfl, rfl⟩, by simp⟩
    have := (hq.mul hx).shift (r.S * c + r.d)
    rw [show r.S * (e + c) + r.d = e * r.S + (r.S * c + r.d) by ring, pow_add, ofK_mul, pow_mul,
      ofK_pow]
    rw [← mul_assoc]
    exact this

theorem Rng.first_q {s : St} {r : Rng} {v : E} (h : MonoVal s r.first v) : ∃ vq, MonoVal s r.q vq := by
  unfold Rng.first at h
  split at h
  · obtain ⟨u, hu, -⟩ := h.unshift
    exact ⟨u, hu⟩
  · obtain ⟨u, hu, -⟩ := h.unshift
    obtain ⟨va, -, ha, -, -⟩ := MonoVal.mul_inv hu
    exact ⟨va, ha⟩

/-- **A pointer the walk knows**: the heap cell holds a word whose cells `os` past it are written. -/
theorem Abs.ptrAt_sound {s : St} {A : Abs} (hA : Holds s A) (hfp : s.fp < maxCells) (hwf : s.mem.WF)
    (hu : s.mem.used ≤ maxCells) {k : Mono} {os : List ℕ} (h : A.ptrAt k os = true) : HP s k os := by
  unfold Abs.ptrAt at h
  split at h
  · rename_i m hm
    obtain ⟨⟨vk, X, w, hk, hX, hw, hmw⟩, -⟩ := hvGet_gen hA hfp hwf hu hm
    refine ⟨vk, X, hk, hX, w, hw, fun o ho ↦ ?_⟩
    obtain ⟨v, y, hv, hy, hwy⟩ := Abs.covered_cell hA hwf hu (List.all_eq_true.mp h o ho)
    rw [hv.unique (hmw.shift o)] at hy
    exact ⟨y, hy, hwy⟩
  · cases h

theorem PtrW.sub {m : Mem} {x : ℕ} {os os' : List ℕ} (h : PtrW m x os') (hs : ∀ o ∈ os, o ∈ os') :
    PtrW m x os := by
  obtain ⟨p, h1, h2⟩ := h
  exact ⟨p, h1, fun o ho ↦ h2 o (hs o ho)⟩

/-- **A run of pointers the walk knows is.** -/
theorem Abs.coveredP_sound {s : St} {A : Abs} (hA : Holds s A) (hfp : s.fp < maxCells)
    (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) {r : Rng} {os : List ℕ}
    (h : A.coveredP r os = true) : PW s r os := by
  unfold Abs.coveredP at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain ⟨⟨r', os'⟩, hm, hh⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hh
      obtain ⟨⟨⟨⟨⟨⟨⟨hq, hS⟩, hd⟩, hlo⟩, hhi⟩, hklo⟩, hkhi⟩, hos⟩ := hh
      obtain ⟨vq, xlo', xhi', h1, h2, h3, h4⟩ := hA.p _ hm
      obtain ⟨xlo, hxlo⟩ := Abs.hasIdx_sound hA hklo
      obtain ⟨xhi, hxhi⟩ := Abs.hasIdx_sound hA hkhi
      obtain ⟨y, hy, hyle⟩ := Abs.le_sound hA hlo hxlo
      have hy' := hy.unique h2
      obtain ⟨z, hz, hzle⟩ := Abs.le_sound hA hhi h3
      have hz' := hz.unique hxhi
      rw [Mono.beq_eq hq] at h1
      exact ⟨vq, xlo, xhi, h1, hxlo, hxhi, fun j hj1 hj2 ↦ by
        rw [← hS, ← hd]
        obtain ⟨x, hx, hp⟩ := h4 j (by omega) (by omega)
        exact ⟨x, hx, hp.sub fun o ho ↦ by simpa using hos o ho⟩⟩
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hhi, hlo⟩, hp⟩ := h
      obtain ⟨y, hy⟩ := Abs.hasIdx_sound hA hlo
      obtain ⟨v, x, hv, hx, hpx⟩ := Abs.ptrAt_sound hA hfp hwf hu hp
      obtain ⟨vq, hq⟩ := Rng.first_q hv
      refine ⟨vq, y, y + 1, hq, hy, by rw [Idx.beq_eq hhi]; exact Idx.succ_val' hy,
        fun j hj1 hj2 ↦ ?_⟩
      obtain rfl : j = y := by omega
      rw [hv.unique (Rng.first_val hy hq)] at hx
      exact ⟨x, hx, hpx⟩
  · split at h
    · rename_i a b hlo hhi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨-, hbs⟩, hall⟩ := h
      obtain ⟨w, hw⟩ := BsVal.exists_fr hA hbs
      refine ⟨_, a, b, ⟨w, hw, rfl⟩, by rw [hlo]; rfl, by rw [hhi]; rfl, fun j hj1 hj2 ↦ ?_⟩
      have hc := List.all_eq_true.mp hall (j - a) (List.mem_range.mpr (by omega))
      obtain ⟨v, x, hv, hx, hpx⟩ := Abs.ptrAt_sound hA hfp hwf hu hc
      rw [hv.unique (MonoVal.shift ⟨w, hw, rfl⟩ _),
        show r.S * (a + (j - a)) + r.d = r.S * j + r.d by congr 2; omega] at hx
      exact ⟨x, hx, hpx⟩
    · simp at h

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
  obtain ⟨⟨⟨⟨hent, hself⟩, hpre⟩, hpreR⟩, hpreP⟩ := h
  have h0 : Holds sE ⟨G.entry.foldl (fun t o ↦ t.set () Exec.envDepth o) .nil, .nil, .nil, [], G.pre,
      jtRng En :: G.preR, G.term, [], .nil, G.preP⟩ := {
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
    xs := fun c a b hc ↦ by simp at hc
    p := fun q hq ↦ by
      have := hpreP q hq
      split at this
      · rename_i r' hr'
        exact PW.trDown F hA hr' (Abs.coveredP_sound hA F.fpC F.wf F.used this)
      · cases this }
  unfold entryAbs
  rw [foldlT_eq]
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
  refine Holds.foldlA _ _ hA fun A p hp hA ↦ ?_
  split
  · rename_i a b ha hb
    obtain ⟨xa, xb, h1, h2, h3⟩ := hT p hp
    exact hA.addLt ⟨xa, xb, idxUp_val F hA ha h1, idxUp_val F hA hb h2, h3⟩
  · exact hA

/-- **After a call**: the caller's state `sC` once the callee, its frame named by `mq` and its state
at return `sR`, guarantees what it does at return, its accumulated runs and its termination facts. -/
theorem afterCall_sound {sC sR : St} {A : Abs} {mq : Mono} {G : Sig} (F : Frames sC sR mq)
    (hA : Holds sC A) (hR : RetHolds sR G) (hL : ∀ r ∈ G.postL, RW sR r)
    (hLP : ∀ q ∈ G.postLP, PW sR q.1 q.2) (hT : ∀ p ∈ G.term, LTF sR p.1 p.2) :
    Holds sC (afterCall A mq G) := by
  unfold afterCall
  dsimp only
  refine atCall_sound F (Holds.foldlA _ _ (Holds.foldlA _ _ (Holds.foldlA _ _ (Holds.foldlA _ _
    (Holds.foldlA _ _ hA ?_) ?_) ?_) ?_) ?_) hT
  · intro A o ho hA
    have hw := hR.1 o ho
    obtain ⟨u, hu⟩ := Mem.get_of_written hw
    have hlt := F.get_lt hu
    rw [F.mem] at hw
    exact hA.addH_cell F.fpC (F.mq.shift o) (names_shift (by simp) hlt) hw
  · intro A p hp hA
    split
    · rename_i x hx
      split
      · obtain ⟨u, hu, hmu⟩ := hR.2.2.2.2 p hp
        have hlt := F.get_lt hu
        rw [F.mem] at hu
        have hX : Names (ofK (g ^ sR.fp) * ofK (g ^ p.1)) (sR.fp + p.1) := names_shift (by simp) hlt
        have hv := (trMono_iff F hA hx u).mp hmu
        refine hA.addHv ⟨_, _, _, F.mq.shift p.1, hX, hu, hv⟩ fun d hd ↦ ?_
        rw [← own_names F.fpC hd (F.mq.shift p.1) hX]
        exact ⟨u, hu, hv⟩
      · exact hA
    · exact hA
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
        exacts [hR.2.2.1 r h, hL r h])
      exact { hA with
        r := fun r'' hm ↦ by
          rcases List.mem_cons.mp hm with rfl | hm
          exacts [hrw, hA.r r'' hm] }
    · exact hA
  · intro A q hq hA
    split
    · rename_i r' hr'
      have hpw : PW sC r' q.2 := PW.trUp F hA hr' (by
        rcases List.mem_append.mp hq with h | h
        exacts [hR.2.2.2.1 q h, hLP q h])
      exact { hA with
        p := fun q' hm ↦ by
          rcases List.mem_cons.mp hm with rfl | hm
          exacts [hpw, hA.p q' hm] }
    · exact hA

/-- A loop's points: each run's point at its counter's start is written. -/
theorem loopOk_sound {s : St} {A : Abs} {G : Sig} (hA : Holds s A) (hfp : s.fp < maxCells)
    (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) (h : loopOk A G = true) :
    (∀ r ∈ G.postL, HW s r.first) ∧ ∀ q ∈ G.postLP, HP s q.1.first q.2 := by
  have F := Frames.own hfp hwf hu rfl (Nat.add_zero _).symm hfp
  unfold loopOk at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun r hr ↦ ?_, fun q hq ↦ ?_⟩
  · have := List.all_eq_true.mp h.1 r hr
    split at this
    · rename_i k hk
      obtain ⟨v, x, hv, hx, hw⟩ := Abs.covered_cell hA hwf hu this
      exact ⟨v, x, (trMono_iff F hA hk v).mpr hv, hx, hw⟩
    · cases this
  · have := List.all_eq_true.mp h.2 q hq
    split at this
    · rename_i k hk
      obtain ⟨v, x, hv, hx, hw⟩ := Abs.ptrAt_sound hA hfp hwf hu this
      exact ⟨v, x, (trMono_iff F hA hk v).mpr hv, hx, hw⟩
    · cases this

/-- **A return**: what the walk knows gives the function's guarantees and its loop points. -/
theorem retOk_sound {s : St} {A : Abs} {G : Sig} (hA : Holds s A) (hfp : s.fp < maxCells)
    (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) (h : retOk A G = true) :
    RetHolds s G ∧ (∀ r ∈ G.postL, HW s r.first) ∧ ∀ q ∈ G.postLP, HP s q.1.first q.2 := by
  have F := Frames.own hfp hwf hu rfl (Nat.add_zero _).symm hfp
  unfold retOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hL, hret⟩, hretV⟩, hpost⟩, hpostR⟩, hpostP⟩ := h
  refine ⟨⟨fun o ho ↦ hA.written (hret o ho), fun m hm ↦ ?_, fun r hr ↦ ?_, fun q hq ↦ ?_,
    fun p hp ↦ ?_⟩, loopOk_sound hA hfp hwf hu hL⟩
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
  · have := hpostP q hq
    split at this
    · rename_i r' hr'
      exact PW.trDown F hA hr' (Abs.coveredP_sound hA hfp hwf hu this)
    · cases this
  · obtain ⟨hw, this⟩ := hretV p hp
    split at this
    · rename_i x y hx hy
      obtain rfl := Mono.beq_eq this
      obtain ⟨u, hu, hmu⟩ := hA.mono_val hx (hA.written hw)
      exact ⟨u, hu, (trMono_iff F hA hy u).mpr hmu⟩
    · cases this

/-- **A loop's tail call** into the frame `fp·g^e`: the next iteration's entry state holds, its
counters are this one's moved up (`termStep`), and each run it accumulates, moved out, is this one's
from one further. -/
theorem tailOk_sound {En : Env} {s sE : St} {A : Abs} {e : ℕ} {G : Sig} (hA : Holds s A)
    (hfp : s.fp < maxCells) (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) (hm : sE.mem = s.mem)
    (hE : sE.fp = s.fp + e) (hEfp : sE.fp < maxCells) (h : tailOk A e G = true)
    (hjt : RW sE (jtRng En)) (hT : ∀ p ∈ G.term, LTF sE p.1 p.2) :
    Holds sE (entryAbs En G) ∧ termStep A e G = true ∧
      ∀ r ∈ G.postL ++ G.postLP.map (·.1),
        ∃ r', trRngUp A (.own e) r = some r' ∧ r' = ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩ := by
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
