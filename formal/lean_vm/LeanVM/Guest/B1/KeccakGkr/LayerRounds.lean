/-
  LeanVM.Guest.B1.KeccakGkr.LayerRounds

  B1 of `layer_rounds`: its specializations `layer_rounds__L0` to `__L16` run that many
  equality-mode rounds of a layer's pack and segment on the carried capacity.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackRound
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.B1.Tables.Basic
import LeanVM.Guest.CoreRef

/-!
# `layer_rounds`

`layer_rounds(fs0..fs4, cursor, run, prev_point, point, tabs, n)` (G) copies the capacity, runs `n`
rounds and returns the last capacity, the cursor `·g^(2n)` and the normalized claim. Round `q`
(`lrRound q`, the template `packRoundT`): the coordinate `prev_point[q]`, `g₁`, `g₂` at the cursor's
words `2q`, `2q + 1`, the squeeze from the capacity with four zero rate cells (set in round `0`), the
challenge stored at `point[q]`, the claim `claim + (r + c)·g₁ + (r + c²)·g₂` (`eqRound`). Every grind
is of `0` bits (`ROUND3_GRIND_BITS`): `tabs` is never read. `layer_rounds__L{n}`'s body is `lrBody n`
by kernel evaluation (`stmtsEqb_sound`), and computes `packRunF` of the coordinates and the
messages (`MeaningLayerRounds`, `lr_sound`, `layer_rounds_sound`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The meaning -/

/-- **`layer_rounds(fs0..fs4, cursor, run, prev_point, point, tabs, n)`**: the `n` coordinates `rs`
at `prev_point` and the `2n` stream words at the cursor, the rounds' `(g₁, g₂)`, run `packRunF`
from the claim `run` (`v`) on the capacity; the challenges are at `point`, and the function returns the
final capacity, the cursor `·g^(2n)` and the final claim. -/
def MeaningLayerRounds (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, v, pp, pt, _tabs], rets =>
      ∃ (rs : List E) (ms : List (E × E)), rs.length = n ∧ ms.length = n ∧ ReadsAt rd pp rs ∧
        ReadsAt rd cur (ms.flatMap fun m ↦ [m.1, m.2]) ∧
        ReadsAt rd pt (packRunF rs ms v ⟨[f0, f1, f2, f3, f4], []⟩).1.2 ∧
        (packRunF rs ms v ⟨[f0, f1, f2, f3, f4], []⟩).2.pend = [] ∧
        rets = (packRunF rs ms v ⟨[f0, f1, f2, f3, f4], []⟩).2.cap ++
          [cur * gen ^ (2 * n), (packRunF rs ms v ⟨[f0, f1, f2, f3, f4], []⟩).1.1]
  | _, _ => False

/-! ## The template -/

/-- Round `q`'s permutation outputs (the challenge first). -/
def lrC (q : ℕ) : ℕ := 35 + 27 * q

/-- Round `q`'s first value, its coordinate. -/
def lrB (q : ℕ) : ℕ := if q = 0 then 23 else 28 + 27 * q

/-- The capacity cells round `q` reads. -/
def lrCap (q : ℕ) : List V := if q = 0 then cap5 18 else cap5 (lrC (q - 1) + 8)

/-- The claim round `q` reads. -/
def lrCl (q : ℕ) : V := if q = 0 then .n 6 else .n (lrC (q - 1) + 19)

/-- The four zero rate cells. -/
def lrZs : List V := [.n 31, .n 32, .n 33, .n 34]

/-- The constants round `0` sets: a one, and the zero rate cells. -/
def lrPre (q : ℕ) : List Stmt :=
  if q = 0 then
    [.atom (.const (.n 30) (word 1 0)), .atom (.const (.n 31) (word 0 0)),
      .atom (.const (.n 32) (word 0 0)), .atom (.const (.n 33) (word 0 0)),
      .atom (.const (.n 34) (word 0 0))]
  else []

/-- Round `q`. -/
def lrRound (q : ℕ) : List Stmt :=
  packRoundT (.n 7) (.n 5) (.n 8) q (lrB q) (lrC q) (lrPre q) lrZs (lrCap q) (lrCl q)

/-- The head: the rate buffer's eight zeros, the capacity copied. -/
def lrHead : List Stmt :=
  ((List.range 8).map fun k ↦ .atom (.const (.n (10 + k)) (word 0 0))) ++
    ((List.range 5).map fun k ↦ .atom (.copy (.n (18 + k)) (.n k)))

/-- The tail: the capacity, the cursor and the claim copied for the return. -/
def lrTail (n : ℕ) : List Stmt :=
  if n = 0 then
    ((List.range 5).map fun k ↦ .atom (.copy (.n (23 + k)) (.n (18 + k)))) ++
      [.atom (.copy (.n 28) (.n 5)), .atom (.copy (.n 29) (.n 6))]
  else
    ((List.range 5).map fun k ↦ .atom (.copy (.n (lrC (n - 1) + 20 + k)) (.n (lrC (n - 1) + 8 + k)))) ++
      [.atom (.const (.n (lrC (n - 1) + 25)) (word (2 ^ (2 * n)) 0)),
        .atom (.mul (.n (lrC (n - 1) + 26)) (.n 5) (.n (lrC (n - 1) + 25))),
        .atom (.copy (.n (lrC (n - 1) + 27)) (.n (lrC (n - 1) + 26))),
        .atom (.copy (.n (lrC (n - 1) + 28)) (.n (lrC (n - 1) + 19)))]

/-- The values returned. -/
def lrRets (n : ℕ) : List V :=
  if n = 0 then [.n 23, .n 24, .n 25, .n 26, .n 27, .n 28, .n 29]
  else ((List.range 5).map fun k ↦ .n (lrC (n - 1) + 20 + k)) ++
    [.n (lrC (n - 1) + 27), .n (lrC (n - 1) + 28)]

/-- The statements before the `ret`. -/
def lrPreBody (n : ℕ) : List Stmt :=
  lrHead ++ ((List.range n).map lrRound).flatten ++ lrTail n

/-- `layer_rounds__L{n}`'s body. -/
def lrBody (n : ℕ) : List Stmt := lrPreBody n ++ [.ret (lrRets n)]

/-- Its parameters. -/
def lrParams : List V := (List.range 10).map V.n

/-! ## Atoms -/

theorem allAtoms_map_range {n : ℕ} (f : ℕ → Atom) : AllAtoms ((List.range n).map fun k ↦ .atom (f k)) := by
  intro s hs
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hs
  exact ⟨_, rfl⟩

theorem allAtoms_list {l : List Atom} : AllAtoms (l.map Stmt.atom) := by
  intro s hs
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs
  exact ⟨a, rfl⟩

theorem packRoundT_atoms (pp cu pt : V) (q b c : ℕ) (pre : List Stmt) (hpre : AllAtoms pre)
    (zs cap : List V) (cl : V) : AllAtoms (packRoundT pp cu pt q b c pre zs cap cl) := by
  unfold packRoundT
  refine allAtoms_append (allAtoms_append (allAtoms_append (allAtoms_append (allAtoms_append
    ?_ (fsNextT_atoms _ _ _)) (fsNextT_atoms _ _ _)) hpre) ?_) ?_ <;>
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem lrPre_atoms (q : ℕ) : AllAtoms (lrPre q) := by
  unfold lrPre
  split
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · exact allAtoms_nil

theorem lrRound_atoms (q : ℕ) : AllAtoms (lrRound q) :=
  packRoundT_atoms _ _ _ _ _ _ _ (lrPre_atoms q) _ _ _

theorem lrTail_atoms (n : ℕ) : AllAtoms (lrTail n) := by
  unfold lrTail
  split
  · refine allAtoms_append (allAtoms_map_range _) ?_
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact ⟨_, rfl⟩
  · refine allAtoms_append (allAtoms_map_range _) ?_
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem lrPreBody_atoms (n : ℕ) : AllAtoms (lrPreBody n) :=
  allAtoms_append (allAtoms_append (allAtoms_append (allAtoms_map_range _) (allAtoms_map_range _))
    (allAtoms_map_flatten fun q _ ↦ lrRound_atoms q)) (lrTail_atoms n)

/-! ## Memory runs -/

theorem readsAt_map_range {rd : Reader} {p : E} {n : ℕ} {f : ℕ → E}
    (h : ∀ q < n, LoadHolds rd p q (f q)) : ReadsAt rd p ((List.range n).map f) := by
  intro k hk
  simp only [List.length_map, List.length_range] at hk
  simpa using h k hk

theorem length_flatMap_pairs (ms : List (E × E)) :
    (ms.flatMap fun m ↦ [m.1, m.2]).length = 2 * ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    simp
    omega

theorem readsAt_pairs {rd : Reader} {p : E} {f : ℕ → E × E} : ∀ n : ℕ,
    (∀ q < n, LoadHolds rd p (2 * q) (f q).1 ∧ LoadHolds rd p (2 * q + 1) (f q).2) →
    ReadsAt rd p (((List.range n).map f).flatMap fun m ↦ [m.1, m.2])
  | 0, _ => readsAt_nil _ _
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.flatMap_append, readsAt_append]
    refine ⟨readsAt_pairs n fun q hq ↦ h q (by omega), ?_⟩
    rw [length_flatMap_pairs, List.length_map, List.length_range, readsAt_gen_pow_mul]
    intro k hk
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_cons, List.length_nil] at hk ⊢
    interval_cases k
    · exact (h n (by omega)).1
    · exact (h n (by omega)).2

/-! ## The rounds chained -/

section Chain

variable {rd : Reader} {σ : Val}

theorem lrCap_succ (q : ℕ) : lrCap (q + 1) = cap5 (lrC q + 8) := by simp [lrCap]

theorem lrCl_succ (q : ℕ) : lrCl (q + 1) = .n (lrC q + 19) := by simp [lrCl]

/-- The rounds `k ..< k + m` chain from round `k`'s claim and capacity to round `k + m`'s. -/
theorem lr_chain {N : ℕ} (hz : lrZs.map σ = [0, 0, 0, 0])
    (H : ∀ q < N, ∀ a, Stmt.atom a ∈ lrRound q → a.Holds rd σ) : ∀ m k : ℕ, k + m ≤ N →
    EqChain ((List.range' k m).map fun q ↦ σ (.n (lrB q)))
      ((List.range' k m).map fun q ↦ (σ (.n (lrB q + 1)), σ (.n (lrB q + 4))))
      (σ (lrCl k)) ((lrCap k).map σ) ((List.range' k m).map fun q ↦ σ (.n (lrC q)))
      (σ (lrCl (k + m))) ((lrCap (k + m)).map σ)
  | 0, k, _ => ⟨rfl, rfl, rfl⟩
  | m + 1, k, hle => by
    have hf := packRound_facts (H k (by omega)) hz
    simp only [List.range'_succ, List.map_cons]
    refine ⟨_, _, _, _, hf.2.2.2.2, rfl, ?_⟩
    have := lr_chain hz H m (k + 1) (by omega)
    rw [lrCap_succ, lrCl_succ, show k + 1 + m = k + (m + 1) by omega] at this
    exact this

end Chain

/-! ## Soundness -/

theorem gen_pow_two_mul_word {n : ℕ} (hn : n ≤ 16) : word (2 ^ (2 * n)) 0 = gen ^ (2 * n) :=
  Tables.tb_word_two_pow (by omega)

/-- **`layer_rounds` is sound**, for a body that is the template. -/
theorem lr_sound {P : Program} {name : String} {fn : Fn} (hf : P.find? name = some fn)
    (hp : fn.params = lrParams) {n : ℕ} (hn : n ≤ 16) (hb : fn.body = lrBody n) {rd : Reader}
    {args rets : List E} (h : P.Rel rd name args rets) : MeaningLayerRounds n rd args rets := by
  rw [rel_iff_sem hf, hb, hp, lrBody] at h
  obtain ⟨σ, rfl, h⟩ := h
  rw [holdsList_append, holdsList_atoms (lrPreBody_atoms n)] at h
  obtain ⟨H, hret⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds] at hret
  have Hm : ∀ l : List Stmt, (∀ s ∈ l, s ∈ lrPreBody n) → ∀ a, Stmt.atom a ∈ l → a.Holds rd σ :=
    fun l hl a ha ↦ H a (hl _ ha)
  have Hhead : ∀ a, Stmt.atom a ∈ lrHead → a.Holds rd σ :=
    Hm _ (fun s hs ↦ by simp only [lrPreBody, List.mem_append]; exact Or.inl (Or.inl hs))
  have Htail : ∀ a, Stmt.atom a ∈ lrTail n → a.Holds rd σ :=
    Hm _ (fun s hs ↦ by simp only [lrPreBody, List.mem_append]; exact Or.inr hs)
  have Hr : ∀ q < n, ∀ a, Stmt.atom a ∈ lrRound q → a.Holds rd σ := fun q hq ↦
    Hm _ (fun s hs ↦ by
      simp only [lrPreBody, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨_, ⟨q, hq, rfl⟩, hs⟩))
  have hcopy : ∀ k < 5, σ (.n (18 + k)) = σ (.n k) := fun k hk ↦
    Hhead (.copy (.n (18 + k)) (.n k)) (by
      simp only [lrHead, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨k, hk, rfl⟩)
  have hcap0 : (lrCap 0).map σ = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
    simp only [lrCap, ↓reduceIte, cap5, List.map_cons, List.map_nil]
    rw [hcopy 0 (by omega), hcopy 1 (by omega), hcopy 2 (by omega), hcopy 3 (by omega),
      hcopy 4 (by omega)]
  simp only [lrParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · -- No round.
    simp only [lrTail, ↓reduceIte, List.mem_append, List.mem_map, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false] at Htail
    have t : ∀ k < 5, σ (.n (23 + k)) = σ (.n (18 + k)) := fun k hk ↦
      Htail (.copy (.n (23 + k)) (.n (18 + k))) (Or.inl ⟨k, hk, rfl⟩)
    have t5 : σ (.n 28) = σ (.n 5) := Htail (.copy (.n 28) (.n 5)) (Or.inr (Or.inl rfl))
    have t6 : σ (.n 29) = σ (.n 6) := Htail (.copy (.n 29) (.n 6)) (Or.inr (Or.inr rfl))
    refine ⟨[], [], rfl, rfl, readsAt_nil _ _, readsAt_nil _ _, readsAt_nil _ _, rfl, ?_⟩
    rw [← hret]
    simp only [lrRets, ↓reduceIte, List.map_cons, List.map_nil, packRunF, mul_zero, pow_zero,
      mul_one, List.cons_append, List.nil_append]
    have e : ∀ k < 5, σ (.n (23 + k)) = σ (.n k) := fun k hk ↦ (t k hk).trans (hcopy k hk)
    have e0 := e 0 (by omega)
    have e1 := e 1 (by omega)
    have e2 := e 2 (by omega)
    have e3 := e 3 (by omega)
    have e4 := e 4 (by omega)
    simp only [Nat.reduceAdd] at e0 e1 e2 e3 e4
    simp only [e0, e1, e2, e3, e4, t5, t6]
  · -- `n` rounds.
    have hz : lrZs.map σ = [0, 0, 0, 0] := by
      have Z : ∀ k, 31 ≤ k → k < 35 → σ (.n k) = 0 := fun k h1 h2 ↦ by
        have := Hr 0 hpos (.const (.n k) (word 0 0)) (by
          simp only [lrRound, packRoundT, lrPre, ↓reduceIte, List.mem_append, List.mem_cons]
          interval_cases k <;> simp)
        simpa [Atom.Holds, Tables.tb_word_zero] using this
      simp only [lrZs, List.map_cons, List.map_nil]
      rw [Z 31 (by omega) (by omega), Z 32 (by omega) (by omega), Z 33 (by omega) (by omega),
        Z 34 (by omega) (by omega)]
    have pf : ∀ q < n, _ := fun q hq ↦ packRound_facts (Hr q hq) hz
    have hch := lr_chain hz Hr n 0 (by omega)
    have hrun := packRunF_of_chain _ _ _ _ _ _ _ hch
    simp only [Nat.zero_add] at hrun
    rw [show lrCl 0 = .n 6 by simp [lrCl], hcap0] at hrun
    refine ⟨(List.range' 0 n).map fun q ↦ σ (.n (lrB q)),
      (List.range' 0 n).map fun q ↦ (σ (.n (lrB q + 1)), σ (.n (lrB q + 4))), by simp, by simp,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [← List.range_eq_range']
      exact readsAt_map_range fun q hq ↦ (pf q hq).1
    · rw [← List.range_eq_range']
      exact readsAt_pairs n fun q hq ↦ ⟨(pf q hq).2.1, (pf q hq).2.2.1⟩
    · rw [hrun, ← List.range_eq_range']
      exact readsAt_map_range fun q hq ↦ (pf q hq).2.2.2.1
    · rw [hrun]
    · rw [hrun, ← hret]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [lrTail, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.mem_append,
        List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at Htail
      have t : ∀ k < 5, σ (.n (lrC n' + 20 + k)) = σ (.n (lrC n' + 8 + k)) := fun k hk ↦
        Htail (.copy (.n (lrC n' + 20 + k)) (.n (lrC n' + 8 + k))) (Or.inl ⟨k, hk, rfl⟩)
      have c25 : σ (.n (lrC n' + 25)) = word (2 ^ (2 * (n' + 1))) 0 :=
        Htail (.const (.n (lrC n' + 25)) (word (2 ^ (2 * (n' + 1))) 0)) (Or.inr (Or.inl rfl))
      have m26 : σ (.n (lrC n' + 26)) = σ (.n 5) * σ (.n (lrC n' + 25)) :=
        Htail (.mul (.n (lrC n' + 26)) (.n 5) (.n (lrC n' + 25))) (Or.inr (Or.inr (Or.inl rfl)))
      have c27 : σ (.n (lrC n' + 27)) = σ (.n (lrC n' + 26)) :=
        Htail (.copy (.n (lrC n' + 27)) (.n (lrC n' + 26))) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      have c28 : σ (.n (lrC n' + 28)) = σ (.n (lrC n' + 19)) :=
        Htail (.copy (.n (lrC n' + 28)) (.n (lrC n' + 19))) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      simp only [lrRets, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, lrCap_succ, lrCl_succ,
        cap5, List.map_cons, List.map_nil, List.range_succ,
        List.range_zero, List.nil_append, List.cons_append]
      rw [c28, c27, m26, c25, gen_pow_two_mul_word hn, t 0 (by omega), t 1 (by omega),
        t 2 (by omega), t 3 (by omega), t 4 (by omega)]

/-! ## The specializations -/

/-- `layer_rounds__L{n}`, `n ≤ 16`. -/
def lrNames : List String := ["layer_rounds__L0", "layer_rounds__L1", "layer_rounds__L2", "layer_rounds__L3", "layer_rounds__L4", "layer_rounds__L5", "layer_rounds__L6", "layer_rounds__L7", "layer_rounds__L8", "layer_rounds__L9", "layer_rounds__L10", "layer_rounds__L11", "layer_rounds__L12", "layer_rounds__L13", "layer_rounds__L14", "layer_rounds__L15", "layer_rounds__L16"]

set_option maxRecDepth 100000 in
theorem layer_rounds_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 0 "") args rets → MeaningLayerRounds 0 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L0») (coreProgram_find?_at (j := idx% «layer_rounds__L0») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L1_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 1 "") args rets → MeaningLayerRounds 1 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L1») (coreProgram_find?_at (j := idx% «layer_rounds__L1») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L2_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 2 "") args rets → MeaningLayerRounds 2 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L2») (coreProgram_find?_at (j := idx% «layer_rounds__L2») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L3_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 3 "") args rets → MeaningLayerRounds 3 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L3») (coreProgram_find?_at (j := idx% «layer_rounds__L3») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L4_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 4 "") args rets → MeaningLayerRounds 4 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L4») (coreProgram_find?_at (j := idx% «layer_rounds__L4») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L5_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 5 "") args rets → MeaningLayerRounds 5 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L5») (coreProgram_find?_at (j := idx% «layer_rounds__L5») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L6_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 6 "") args rets → MeaningLayerRounds 6 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L6») (coreProgram_find?_at (j := idx% «layer_rounds__L6») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L7_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 7 "") args rets → MeaningLayerRounds 7 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L7») (coreProgram_find?_at (j := idx% «layer_rounds__L7») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L8_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 8 "") args rets → MeaningLayerRounds 8 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L8») (coreProgram_find?_at (j := idx% «layer_rounds__L8») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L9_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 9 "") args rets → MeaningLayerRounds 9 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L9») (coreProgram_find?_at (j := idx% «layer_rounds__L9») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L10_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 10 "") args rets → MeaningLayerRounds 10 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L10») (coreProgram_find?_at (j := idx% «layer_rounds__L10») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L11_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 11 "") args rets → MeaningLayerRounds 11 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L11») (coreProgram_find?_at (j := idx% «layer_rounds__L11») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L12_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 12 "") args rets → MeaningLayerRounds 12 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L12») (coreProgram_find?_at (j := idx% «layer_rounds__L12») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L13_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 13 "") args rets → MeaningLayerRounds 13 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L13») (coreProgram_find?_at (j := idx% «layer_rounds__L13») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L14_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 14 "") args rets → MeaningLayerRounds 14 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L14») (coreProgram_find?_at (j := idx% «layer_rounds__L14») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L15_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 15 "") args rets → MeaningLayerRounds 15 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L15») (coreProgram_find?_at (j := idx% «layer_rounds__L15») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
theorem layer_rounds_L16_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD 16 "") args rets → MeaningLayerRounds 16 rd args rets :=
  lr_sound (fn := fn% «layer_rounds__L16») (coreProgram_find?_at (j := idx% «layer_rounds__L16») rfl) rfl
    (by decide) (stmtsEqb_sound (by decide +kernel))

/-- **`layer_rounds` is sound**: every specialization computes its meaning. -/
theorem layer_rounds_sound (n : ℕ) (hn : n ≤ 16) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (lrNames.getD n "") args rets → MeaningLayerRounds n rd args rets := by
  interval_cases n
  exacts [layer_rounds_L0_sound rd args rets, layer_rounds_L1_sound rd args rets, layer_rounds_L2_sound rd args rets, layer_rounds_L3_sound rd args rets, layer_rounds_L4_sound rd args rets, layer_rounds_L5_sound rd args rets, layer_rounds_L6_sound rd args rets, layer_rounds_L7_sound rd args rets, layer_rounds_L8_sound rd args rets, layer_rounds_L9_sound rd args rets, layer_rounds_L10_sound rd args rets, layer_rounds_L11_sound rd args rets, layer_rounds_L12_sound rd args rets, layer_rounds_L13_sound rd args rets, layer_rounds_L14_sound rd args rets, layer_rounds_L15_sound rd args rets, layer_rounds_L16_sound rd args rets]

end
end LeanVM.Guest.B1.VerifySub

