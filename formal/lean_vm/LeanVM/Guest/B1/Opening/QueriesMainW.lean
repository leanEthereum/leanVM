/-
  LeanVM.Guest.B1.Opening.QueriesMainW

  `opening_queries` is sound with its queries named: the witness `oqsOf`, read off its frame and
  its loop's frames.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesW

/-!
# `opening_queries`, its queries named

`oqMain1_sound_w` (level 0) and `oqMain0_sound_w` (deeper): under a call relation `C ≤ Rel`
unfolding at `V`, a valuation holding the function's body (its loop called at `1`, the bound
`g^N`), the bit pointers pointing to bits, gives `MeaningOpeningQueriesW` at `oqsOf … σ V`: the
odd first query from the function's own frame, then iteration `j`'s from the loop's frame
`V loop (g^j :: oqLoopArgs σ) []` (`loopV_frames`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Lists of iterations -/

theorem oqLength_flatMap_range {α : Type} (f : ℕ → List α) (n : ℕ) (hf : ∀ j, (f j).length = n) :
    ∀ N, ((List.range N).flatMap f).length = n * N
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, oqLength_flatMap_range f n hf N]
    simp [hf, Nat.mul_succ]

theorem oqGetD_flatMap_range {α : Type} (f : ℕ → List α) (n : ℕ) (hf : ∀ j, (f j).length = n)
    (d : α) : ∀ (N j e : ℕ), j < N → e < n →
      ((List.range N).flatMap f).getD (n * j + e) d = (f j).getD e d
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | N + 1, j, e, hj, he => by
    rw [List.range_succ, List.flatMap_append]
    have hl := oqLength_flatMap_range f n hf N
    rcases Nat.lt_or_ge j N with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hl]; nlinarith)]
      exact oqGetD_flatMap_range f n hf d N j e h he
    · obtain rfl : j = N := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega)]
      simp [hl]

/-! ## The loops' guards -/

theorem oqLoop1_hc {C : CallRel} {s : Oq} {odd : ℕ} {walk : String} {fl : Fn} (hpl : fl.params = oqLoopParams) {Nv : E}
    {rest : List E} (τ : Val) (x : E) (hp : fl.params.map τ = x :: Nv :: rest)
    (hA : BlockOkC C rd τ (oqLoop1A s odd walk)) :
    τ (.n (oqC1 s + 9)) = x * gen + Nv ∧
      ([.n (oqC1 s + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map τ =
        x * gen :: Nv :: rest := by
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil] at hp
  set c := oqC1 s with hc
  have a7 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.const (.n (c + 7)) (word 2 0)) ∈ _)
  have a8 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 8)) (.n 0) (.n (c + 7))) ∈ _)
  have a9 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.add (.n (c + 9)) (.n (c + 8)) (.n 1)) ∈ _)
  have a10 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.const (.n (c + 10)) (word 2 0)) ∈ _)
  have a11 := hA.atom (by simp [oqLoop1A, ← hc] :
    Stmt.atom (.mul (.n (c + 11)) (.n 0) (.n (c + 10))) ∈ _)
  simp only [Atom.Holds] at a7 a8 a9 a10 a11
  simp only [List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  refine ⟨by rw [a9, a8, a7, word_gen, h0, h1], ?_⟩
  simp [a11, a10, word_gen, h0, h1]

theorem oqLoop0_hc {C : CallRel} {s : Oq} {walk : String} {fl : Fn} (hpl : fl.params = oqLoopParams) {Nv : E}
    {rest : List E} (τ : Val) (x : E) (hp : fl.params.map τ = x :: Nv :: rest)
    (hA : BlockOkC C rd τ (oqLoop0A s walk)) :
    τ (.n (oqC0 s + 7)) = x * gen + Nv ∧
      ([.n (oqC0 s + 9), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map τ =
        x * gen :: Nv :: rest := by
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil] at hp
  set c := oqC0 s with hc
  have a5 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.const (.n (c + 5)) (word 2 0)) ∈ _)
  have a6 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n (c + 6)) (.n 0) (.n (c + 5))) ∈ _)
  have a7 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.add (.n (c + 7)) (.n (c + 6)) (.n 1)) ∈ _)
  have a8 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.const (.n (c + 8)) (word 2 0)) ∈ _)
  have a9 := hA.atom (by simp [oqLoop0A, ← hc] :
    Stmt.atom (.mul (.n (c + 9)) (.n 0) (.n (c + 8))) ∈ _)
  simp only [Atom.Holds] at a5 a6 a7 a8 a9
  simp only [List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  refine ⟨by rw [a7, a6, a5, word_gen, h0, h1], ?_⟩
  simp [a9, a8, word_gen, h0, h1]

/-- An iteration's parameters, from the loop's parameters. -/
theorem loop_params {fl : Fn} (hpl : fl.params = oqLoopParams) {τ : Val} {x : E} {ps : List E}
    (hp : fl.params.map τ = x :: ps) :
    τ (.n 0) = x ∧ ps = [τ (.n 1), τ (.n 2), τ (.n 3), τ (.n 4), τ (.n 5), τ (.n 6), τ (.n 7)] := by
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil, List.cons.injEq] at hp
  exact ⟨hp.1, hp.2.symm⟩

/-! ## The odd first query -/

theorem oqMainA_odd_w {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V) {s : Oq}
    (hs : s.RowShape) (hpd : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8)
    (hW : WalkFn (oqWalkOf s) s.pd s.cd) (hA : BlockOkC C rd σ (oqMainA s 1 (oqWalkOf s)))
    (hbool : ∀ bp, LoadHolds rd (σ (.n 4)) 0 bp → WinRun rd bp (s.pd + s.cd) s.cd) :
    LoadHolds rd (σ (.n 4)) 0 (σ (.n 12)) ∧
      QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (σ (.n 12)) (oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V)
        (σ (.n (oqDot s 13))) ∧
      LoadHolds rd (σ (.n 11)) 0 (σ (.n (oqDot s 13)) * σ (.n 8)) := by
  have mem : BlockOkC C rd σ (oqQueryT s (.n 12) (.n 0) (.n 1) (.n 5) 13 true 0 (oqWalkOf s)) :=
    hA.mono fun a ha => by simp only [oqMainA, ↓reduceIte, List.mem_append]; simp_all
  have l12 := hA.atom (by simp [oqMainA] : Stmt.atom (.load (.n 12) (.n 4) 0) ∈ _)
  have c1 := hA.atom (by simp [oqMainA] :
    Stmt.atom (.mul (.n (oqMK s 1 - 1)) (.n (oqDot s 13)) (.n 8)) ∈ _)
  have c2 := hA.atom (by simp [oqMainA] : Stmt.atom (.load (.n (oqMK s 1 - 1)) (.n 11) 0) ∈ _)
  simp only [Atom.Holds] at c1 l12
  obtain ⟨-, -, hpd', -, -⟩ := oqQuery_pieces mem
  obtain ⟨e1, z⟩ := oqPad_values (hpd' rfl)
  refine ⟨l12, oqQuery_sound_w hU hs hpd hcd hcd8 hW mem e1 z (hbool _ l12), ?_⟩
  have := c2
  simp only [Atom.Holds, c1] at this
  exact this

/-! ## The function -/

theorem oqChain_succ_one {odd base : ℕ} (hb : base = 1) (mu : E) (ds : ℕ → E) (i : ℕ) :
    oqChain odd base mu ds (i + 1) =
      ((oqChain odd base mu ds i + ds (odd + 2 * i)) * mu + ds (odd + 2 * i + 1)) * mu := by
  simp [oqChain, hb]

theorem oqChain_succ_zero {base : ℕ} (hb : base = 0) (mu : E) (ds : ℕ → E) (i : ℕ) :
    oqChain 0 base mu ds (i + 1) = (oqChain 0 base mu ds i + ds i) * mu := by
  simp [oqChain, hb]

theorem oqsOf_length_one {s : Oq} (hb1 : s.base = 1) {odd : ℕ} (hodd : odd ≤ 1) (loop : String)
    (N : ℕ) (rd : Reader) (σ : Val) (V : FrameMap) :
    (oqsOf s odd loop N rd σ V).length = odd + 2 * N := by
  unfold oqsOf
  rw [List.length_append, oqLength_flatMap_range _ 2 (fun j => by simp [oqIterOf, hb1])]
  split_ifs with h <;> simp <;> omega

/-- **`opening_queries` at level 0 is sound with its queries named.** -/
theorem oqMain1_sound_w {s : Oq} (hs : s.RowShape) (hb1 : s.base = 1) (hpd : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {odd : ℕ} (hodd : odd ≤ 1) {name loop : String}
    (hW : WalkFn (oqWalkOf s) s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd (oqWalkOf s) loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd (oqWalkOf s) loop) :
    opening_queries_sound_w_Spec name loop s odd := by
  intro rd C V hU _ fm' σ args rets N hfm' hp hh hN hNo hbits
  rw [hfm] at hfm'
  cases hfm'
  rw [hpm] at hp
  simp only [List.map_cons, List.map_nil] at hp
  subst hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hN hbits
  rw [hbm, oqMainT, holdsList_append, holdsList_flatC (oqMainA_flatC s odd (oqWalkOf s))] at hh
  obtain ⟨hA, h⟩ := hh
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨-, hcall, e3, e4, e5, hret⟩ := h
  obtain ⟨hmu, hg, hst, h0even⟩ := oqMainA_basic hA
  have hlam : σ (.n 2) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hmu; exact zero_ne_one hmu
  have hmuinv : σ (.n 8) = (σ (.n 2))⁻¹ := eq_inv_of_mul_eq_one_left hmu
  rw [hb1] at hbits
  simp only [oqCount, ↓reduceIte] at hbits
  -- the iterations' frames
  have hfr := loopV_frames (rd := rd) hU hfl (by rw [hbl]; rfl) (oqLoop1A_flatC s odd (oqWalkOf s))
    (Nv := σ (.n 6)) (rest := [σ (.n 4), σ (.n 0), σ (.n 1), σ (.n 5), σ (.n 11), σ (.n 8)])
    (fun τ x hp hA => oqLoop1_hc hpl τ x hp hA) hN hNo (fun hN0 => by
      have hne : σ (.n (oqMK s odd + 1)) ≠ 0 := by
        rw [hg, hN]
        intro h0
        have := (gen_pow_eq_one_iff hNo).mp (e_add_eq_zero_iff.mp h0).symm
        omega
      have := hcall hne
      rwa [hst] at this)
  set τ : ℕ → Val := fun j =>
    V loop (gen ^ j :: oqLoopArgs σ) [] with hτ
  have hit : ∀ j < N, ∃ v : E,
      LoadHolds rd (σ (.n 4)) (2 * j + odd) (τ j (.n 10)) ∧
      QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (τ j (.n 10))
        (oqQueryW s rd (τ j (.n 10)) (τ j (.n 3)) (τ j (.n 4)) 11 true (τ j) V) (τ j (.n (oqDot s 11))) ∧
      LoadHolds rd (σ (.n 4)) (2 * j + odd + 1) (τ j (.n (oqE1 s))) ∧
      QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (τ j (.n (oqE1 s)))
        (oqQueryW s rd (τ j (.n (oqE1 s))) (τ j (.n 3)) (τ j (.n 4)) (oqE1 s + 1) false (τ j) V)
        (τ j (.n (oqDot s (oqE1 s + 1)))) ∧
      LoadHolds rd (σ (.n 11)) j v ∧
      LoadHolds rd (σ (.n 11)) (j + 1) (((v + τ j (.n (oqDot s 11))) * σ (.n 8) +
        τ j (.n (oqDot s (oqE1 s + 1)))) * σ (.n 8)) := by
    intro j hj
    obtain ⟨hp, hA⟩ := hfr j hj
    obtain ⟨t0, hps⟩ := loop_params hpl hp
    simp only [List.cons.injEq] at hps
    obtain ⟨-, t2, t3, t4, t5, t6, t7, -⟩ := hps
    have := oqIter1_sound_w hU hs hpd hcd hcd8 hW (odd := odd) (i := j) hA t0 (fun k hk bp hbp => by
      rw [← t2] at hbp
      exact hbits k (by omega) bp hbp)
    rw [← t2, ← t5, ← t6, ← t7] at this
    obtain ⟨v, a1, a2, a3, a4, a5, a6⟩ := this
    exact ⟨v, a1, by convert a2 using 2 <;> rfl, a3, by convert a4 using 2 <;> rfl, a5, a6⟩
  choose! v hit using hit
  -- the main query
  have hM : odd = 1 → LoadHolds rd (σ (.n 4)) 0 (σ (.n 12)) ∧
      QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (σ (.n 12))
        (oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V) (σ (.n (oqDot s 13))) ∧
      LoadHolds rd (σ (.n 11)) 0 (σ (.n (oqDot s 13)) * σ (.n 8)) := by
    intro h1
    subst h1
    exact oqMainA_odd_w hU hs hpd hcd hcd8 hW hA (fun bp hbp => hbits 0 (by omega) bp hbp)
  -- the queries' functions
  let fsel : ∀ {α : Type}, α → (ℕ → α) → (ℕ → α) → ℕ → α := fun a f g k =>
    if k < odd then a else if (k - odd) % 2 = 0 then f ((k - odd) / 2) else g ((k - odd) / 2)
  have fsel0 : ∀ {α : Type} (a : α) (f g : ℕ → α) (j : ℕ), fsel a f g (odd + 2 * j) = f j :=
    fun a f g j => by simp [fsel]
  have fsel1 : ∀ {α : Type} (a : α) (f g : ℕ → α) (j : ℕ), fsel a f g (odd + 2 * j + 1) = g j :=
    fun a f g j => by
      simp [fsel, show ¬ odd + 2 * j + 1 < odd by omega, show (odd + 2 * j + 1 - odd) % 2 = 1 by omega,
        show (odd + 2 * j + 1 - odd) / 2 = j by omega]
  have fselM : ∀ {α : Type} (a : α) (f g : ℕ → α), odd = 1 → fsel a f g 0 = a :=
    fun a f g h => by simp [fsel, h]
  set D0 : ℕ → E := fun j => τ j (.n (oqDot s 11)) with hD0
  set D1 : ℕ → E := fun j => τ j (.n (oqDot s (oqE1 s + 1))) with hD1
  set B0 : ℕ → E := fun j => τ j (.n 10) with hB0
  set B1 : ℕ → E := fun j => τ j (.n (oqE1 s)) with hB1
  set ds := fsel (σ (.n (oqDot s 13))) D0 D1 with hds
  set ws := oqsOf s odd loop N rd σ V with hws
  have hwsM : odd = 1 → ws.getD 0 default = oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V := by
    intro h1; subst h1; simp [hws, oqsOf]
  have hwsI : ∀ j < N, ∀ e < 2, ws.getD (odd + (2 * j + e)) default =
      (oqIterOf s rd (τ j) V).getD e default := by
    intro j hj e he
    have hl : (if odd = 1 then [oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V] else []).length = odd := by
      split_ifs with h <;> simp <;> omega
    simp only [hws, oqsOf]
    rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]
    exact oqGetD_flatMap_range _ 2 (fun j => by simp [oqIterOf, hb1]) default N j e hj he
  -- the chain
  have hchain : ∀ i ≤ N, LoadHolds rd (σ (.n 11)) i (oqChain odd s.base (σ (.n 2))⁻¹ ds i) := by
    intro i hi
    induction i with
    | zero =>
      by_cases h1 : odd = 1
      · have := (hM h1).2.2
        simp only [oqChain, h1, ↓reduceIte]
        rw [hds, fselM (α := E) (σ (.n (oqDot s 13))) D0 D1 h1, ← hmuinv]
        exact this
      · simp only [oqChain, h1, ↓reduceIte]
        exact h0even h1
    | succ i ih =>
      obtain ⟨-, -, -, -, hv, hv1⟩ := hit i (by omega)
      have e := loadHolds_unique hv (ih (by omega))
      rw [e] at hv1
      have q0 : ds (odd + 2 * i) = τ i (.n (oqDot s 11)) := fsel0 (α := E) _ D0 D1 i
      have q1 : ds (odd + 2 * i + 1) = τ i (.n (oqDot s (oqE1 s + 1))) := fsel1 (α := E) _ D0 D1 i
      rw [oqChain_succ_one hb1, q0, q1]
      rw [hmuinv] at hv1
      exact hv1
  have hlast := e4
  rw [e3, hN, loadHolds_mul_gen_pow, Nat.add_zero] at hlast
  have hv := loadHolds_unique hlast (hchain N le_rfl)
  refine ⟨N, hNo, hN, hlam, by rw [hws, oqsOf_length_one hb1 hodd, hb1]; simp [oqCount],
    fsel (σ (.n 12)) B0 B1, ds, fun k hk => ?_,
    σ (.n 11), hchain, ?_⟩
  · simp only [oqCount, hb1, ↓reduceIte] at hk
    by_cases hk0 : k < odd
    · have h1 : odd = 1 := by omega
      obtain rfl : k = 0 := by omega
      obtain ⟨a1, a2, -⟩ := hM h1
      rw [fselM (α := E) (σ (.n 12)) B0 B1 h1, hds, fselM (α := E) (σ (.n (oqDot s 13))) D0 D1 h1,
        hwsM h1]
      exact ⟨a1, a2⟩
    · obtain ⟨j, hj, hk'⟩ : ∃ j < N, k = odd + 2 * j ∨ k = odd + 2 * j + 1 :=
        ⟨(k - odd) / 2, by omega, by omega⟩
      obtain ⟨a1, a2, a3, a4, -⟩ := hit j hj
      rcases hk' with rfl | rfl
      · rw [fsel0 (α := E) (σ (.n 12)) B0 B1 j, hds, fsel0 (α := E) (σ (.n (oqDot s 13))) D0 D1 j,
          show odd + 2 * j = odd + (2 * j + 0) by omega, hwsI j hj 0 (by omega)]
        rw [show oqIterOf s rd (τ j) V = [oqQueryW s rd (τ j (.n 10)) (τ j (.n 3)) (τ j (.n 4)) 11 true (τ j) V,
          oqQueryW s rd (τ j (.n (oqE1 s))) (τ j (.n 3)) (τ j (.n 4)) (oqE1 s + 1) false (τ j) V] by simp [oqIterOf, hb1],
          List.getD_cons_zero, show odd + (2 * j + 0) = 2 * j + odd by omega]
        exact ⟨a1, a2⟩
      · rw [fsel1 (α := E) (σ (.n 12)) B0 B1 j, hds, fsel1 (α := E) (σ (.n (oqDot s 13))) D0 D1 j,
          show odd + 2 * j + 1 = odd + (2 * j + 1) by omega, hwsI j hj 1 (by omega)]
        rw [show oqIterOf s rd (τ j) V = [oqQueryW s rd (τ j (.n 10)) (τ j (.n 3)) (τ j (.n 4)) 11 true (τ j) V,
          oqQueryW s rd (τ j (.n (oqE1 s))) (τ j (.n 3)) (τ j (.n 4)) (oqE1 s + 1) false (τ j) V] by simp [oqIterOf, hb1],
          List.getD_cons_succ, List.getD_cons_zero, show odd + (2 * j + 1) = 2 * j + odd + 1 by omega]
        exact ⟨a3, a4⟩
  · rw [← hret, e5, hv]

theorem oqsOf_length_zero {s : Oq} (hb0 : s.base = 0) (loop : String) (N : ℕ) (rd : Reader)
    (σ : Val) (V : FrameMap) : (oqsOf s 0 loop N rd σ V).length = N := by
  unfold oqsOf
  rw [List.length_append, oqLength_flatMap_range _ 1 (fun j => by simp [oqIterOf, hb0])]
  simp

/-- **`opening_queries` deeper is sound with its queries named.** -/
theorem oqMain0_sound_w {s : Oq} (hs : s.RowShape) (hb0 : s.base = 0) (hpd : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {name loop : String}
    (hW : WalkFn (oqWalkOf s) s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s 0 (oqWalkOf s) loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s (oqWalkOf s) loop) :
    opening_queries_sound_w_Spec name loop s 0 := by
  intro rd C V hU _ fm' σ args rets N hfm' hp hh hN hNo hbits
  rw [hfm] at hfm'
  cases hfm'
  rw [hpm] at hp
  simp only [List.map_cons, List.map_nil] at hp
  subst hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hN hbits
  rw [hbm, oqMainT, holdsList_append, holdsList_flatC (oqMainA_flatC s 0 (oqWalkOf s))] at hh
  obtain ⟨hA, h⟩ := hh
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨-, hcall, e3, e4, e5, hret⟩ := h
  obtain ⟨hmu, hg, hst, h0even⟩ := oqMainA_basic hA
  have hlam : σ (.n 2) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hmu; exact zero_ne_one hmu
  have hmuinv : σ (.n 8) = (σ (.n 2))⁻¹ := eq_inv_of_mul_eq_one_left hmu
  rw [hb0] at hbits
  simp only [oqCount, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at hbits
  have hfr := loopV_frames (rd := rd) hU hfl (by rw [hbl]; rfl) (oqLoop0A_flatC s (oqWalkOf s))
    (Nv := σ (.n 6)) (rest := [σ (.n 4), σ (.n 0), σ (.n 1), σ (.n 5), σ (.n 11), σ (.n 8)])
    (fun τ x hp hA => oqLoop0_hc hpl τ x hp hA) hN hNo (fun hN0 => by
      have hne : σ (.n (oqMK s 0 + 1)) ≠ 0 := by
        rw [hg, hN]
        intro h0
        have := (gen_pow_eq_one_iff hNo).mp (e_add_eq_zero_iff.mp h0).symm
        omega
      have := hcall hne
      rwa [hst] at this)
  set τ : ℕ → Val := fun j =>
    V loop (gen ^ j :: oqLoopArgs σ) [] with hτ
  have hit : ∀ j < N, ∃ v : E,
      LoadHolds rd (σ (.n 4)) j (τ j (.n 9)) ∧
      QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (τ j (.n 9))
        (oqQueryW s rd (τ j (.n 9)) (τ j (.n 3)) (τ j (.n 4)) 10 true (τ j) V) (τ j (.n (oqDot s 10))) ∧
      LoadHolds rd (σ (.n 11)) j v ∧
      LoadHolds rd (σ (.n 11)) (j + 1) ((v + τ j (.n (oqDot s 10))) * σ (.n 8)) := by
    intro j hj
    obtain ⟨hp, hA⟩ := hfr j hj
    obtain ⟨t0, hps⟩ := loop_params hpl hp
    simp only [List.cons.injEq] at hps
    obtain ⟨-, t2, t3, t4, t5, t6, t7, -⟩ := hps
    have := oqIter0_sound_w hU hs hpd hcd hcd8 hW (i := j) hA t0 (fun bp hbp => by
      rw [← t2] at hbp
      exact hbits j hj bp hbp)
    rw [← t2, ← t5, ← t6, ← t7] at this
    obtain ⟨v, a1, a2, a3, a4⟩ := this
    exact ⟨v, a1, by convert a2 using 2 <;> rfl, a3, a4⟩
  choose! v hit using hit
  set ds := fun j => τ j (.n (oqDot s 10)) with hds
  set ws := oqsOf s 0 loop N rd σ V with hws
  have hwsI : ∀ j < N, ws.getD j default = oqQueryW s rd (τ j (.n 9)) (τ j (.n 3)) (τ j (.n 4)) 10 true (τ j) V := by
    intro j hj
    simp only [hws, oqsOf, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.nil_append]
    have := oqGetD_flatMap_range (fun j => oqIterOf s rd (V loop (gen ^ j :: oqLoopArgs σ) []) V) 1
      (fun j => by simp [oqIterOf, hb0]) default N j 0 hj (by omega)
    rw [Nat.one_mul, Nat.add_zero] at this
    rw [this]
    simp [oqIterOf, hb0, hτ]
  have hchain : ∀ i ≤ N, LoadHolds rd (σ (.n 11)) i (oqChain 0 s.base (σ (.n 2))⁻¹ ds i) := by
    intro i hi
    induction i with
    | zero =>
      simp only [oqChain, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
      exact h0even (by decide)
    | succ i ih =>
      obtain ⟨-, -, hv, hv1⟩ := hit i (by omega)
      have e := loadHolds_unique hv (ih (by omega))
      rw [e] at hv1
      rw [oqChain_succ_zero hb0]
      rw [hmuinv] at hv1
      exact hv1
  have hlast := e4
  rw [e3, hN, loadHolds_mul_gen_pow, Nat.add_zero] at hlast
  have hv := loadHolds_unique hlast (hchain N le_rfl)
  refine ⟨N, hNo, hN, hlam, by rw [hws, oqsOf_length_zero hb0, hb0]; simp [oqCount],
    fun j => τ j (.n 9), ds, fun k hk => ?_, σ (.n 11), hchain, ?_⟩
  · simp only [oqCount, hb0, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at hk
    obtain ⟨a1, a2, -⟩ := hit k hk
    rw [hwsI k hk]
    exact ⟨a1, a2⟩
  · rw [← hret, e5, hv]

end
end LeanVM.Guest.B1
