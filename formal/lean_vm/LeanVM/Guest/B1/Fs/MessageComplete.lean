/-
  LeanVM.Guest.B1.Fs.MessageComplete

  The completeness of `opening_message`'s template, and the proof that every deployed
  specialization's core IR is its meaning.
-/

module

public import LeanVM.Guest.B1.Fs.MessageSound

/-!
# `opening_message`: completeness

The honest valuation (`omVals`): the arguments, the capacity copied in, the words and their packed
cells, each full group's permutation's cells (`stF`), the tail's values (`omTailVal`: the pad
run's constants, the nonce, the last permutation's cells), the returned cells and cursor
(`omFinVal`). `om_complete` checks every atom of `omAtoms`; `opening_message_holds` joins both
directions over the deployed messages.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The tail's values, by offset from `omE n`; `S0` the last group's permutation, `S1` the
nonce's. -/
def omTailVal (n nonce : ℕ) (S0 S1 : KeccakState) (nn : E) (d : ℕ) : E :=
  if nonce = 0 then
    if n - 4 * omK n = 4 then cellsOfState S0 false (fin13 d)
    else if d = 0 then word 1 0 else if d < 5 then 0 else cellsOfState S0 false (fin13 (d - 5))
  else if n - 4 * omK n = 4 then
    (if d < 13 then cellsOfState S0 false (fin13 d) else if d < 15 then nn
      else if d = 15 then word 0 dsPowNonce else if d = 16 then word 1 0 else if d < 21 then 0
      else cellsOfState S1 false (fin13 (d - 21)))
  else if n - 4 * omK n = 2 then
    (if d < 2 then nn else if d = 2 then word 0 dsPowNonce else if d < 5 then 0
      else cellsOfState S1 false (fin13 (d - 5)))
  else if d < 2 then nn else if d = 2 then word 0 dsPowNonce else if d = 3 then word 1 0
    else if d < 8 then 0 else cellsOfState S1 false (fin13 (d - 8))

/-- The returned values, by offset from the copies' start. -/
def omFinVal (n nonce : ℕ) (S : KeccakState) (cur : E) (u : ℕ) : E :=
  if u = 0 then cellsOfState S false 0 else if u = 1 then cellsOfState S false 1
  else if u < 7 then cellsOfState S false (fin13 (u + 6))
  else if u = 7 then word (2 ^ (n + nonce)) 0 else cur * word (2 ^ (n + nonce)) 0

/-- **The honest valuation of `opening_message__L{n}_L{nonce}`** on the arguments `as`, the words
`xs` and the nonce `nn`. -/
def omVals (as xs : List E) (nn : E) (n nonce k : ℕ) : E :=
  if k < 7 then as.getD k 0
  else if k < 12 then as.getD (k - 7) 0
  else if k < omE n then
    (if (k - 12) % 25 < 12 then
      (if (k - 12) % 25 % 3 = 2 then word 0 dsObserve
        else xs.getD (4 * ((k - 12) / 25) + (k - 12) % 25 / 3) 0)
    else cellsOfState (stF (as.take 5) xs ((k - 12) / 25)).perm false (fin13 ((k - 12) % 25 - 12)))
  else if k < (omTail n nonce).2.2 then
    omTailVal n nonce (stF (as.take 5) xs (omK n)).perm
      ((stF (as.take 5) xs (omK n)).absorb nn dsPowNonce).perm nn (k - omE n)
  else omFinVal n nonce
    (if nonce = 1 then ((stF (as.take 5) xs (omK n)).absorb nn dsPowNonce).perm
      else (stF (as.take 5) xs (omK n)).perm) (as.getD 5 0) (k - (omTail n nonce).2.2)

/-- Decide the next `if` of an unfolded index function by `omega`. -/
macro "om_if" : tactic => `(tactic| first
  | (rw [ite_eq_right_of_eq_false]; rotate_left; exact eq_false (by omega))
  | (rw [ite_eq_left_of_eq_true]; rotate_left; exact eq_true (by omega)))

theorem omW_lt_omE {n p : ℕ} (hp : p < n) : omW p + 2 < omE n := by
  simp only [omW, omE, omK]
  have : p / 4 ≤ (n - 1) / 4 := Nat.div_le_div_right (by omega)
  omega

theorem omW_mod {p u : ℕ} (hu : u < 3) :
    (omW p + u - 12) / 25 = p / 4 ∧ (omW p + u - 12) % 25 = 3 * (p % 4) + u := by
  simp only [omW]
  omega

theorem omTail_f_gt (n nonce : ℕ) : omE n < (omTail n nonce).2.2 := by
  simp only [omTail]
  split_ifs <;> dsimp only <;> omega

/-- A permutation's honest outputs, on its inputs the cells of a carried sponge. -/
theorem keccak_of_fs {rd : Reader} {σ : Val} {ins : List V} {O : ℕ} {s : Fs}
    (hs : s.pend.length ≤ 4) (hcap : s.cap.length = 5)
    (hins : ins.map σ = pendCells s.pend ++ List.replicate (8 - 2 * s.pend.length) 0 ++ s.cap)
    (hO : ∀ c : Fin 13, σ (.n (O + c.val)) = cellsOfState s.perm false c) :
    (Atom.keccak ins (run13 O) false false).Holds rd σ := by
  have hlen : ins.length = 13 := by
    have h := congrArg List.length hins
    have hp : (pendCells s.pend).length = 2 * s.pend.length := by
      simp only [pendCells, List.length_flatMap, List.length_cons, List.length_nil]
      induction s.pend <;> simp_all; omega
    simp only [List.length_map, List.length_append, List.length_replicate, hp, hcap] at h
    omega
  refine keccakA_of hlen (by simp [run13]) (funext fun c ↦ ?_)
  rw [cells13_run13, hO c, hins, perm_eq_cells _ hs]


/-! ## Evaluating the honest valuation -/

section Eval

variable (as xs : List E) (nn : E) (n nonce : ℕ)

theorem omV_head {k : ℕ} (hk : k < 12) :
    omVals as xs nn n nonce k = if k < 7 then as.getD k 0 else as.getD (k - 7) 0 := by
  unfold omVals
  by_cases h : k < 7
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_left hk]

theorem omV_word {p u : ℕ} (hp : p < n) (hu : u < 3) :
    omVals as xs nn n nonce (omW p + u) = if u = 2 then word 0 dsObserve else xs.getD p 0 := by
  have hl := omW_lt_omE hp
  obtain ⟨h1, h2⟩ := omW_mod (p := p) hu
  have h12 : 12 ≤ omW p := by simp only [omW]; omega
  unfold omVals
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), h1, h2,
    ite_eq_left (by omega)]
  by_cases hu2 : u = 2
  · rw [ite_eq_left (by omega), ite_eq_left hu2]
  · rw [ite_eq_right (by omega), ite_eq_right hu2]
    congr 1
    omega

theorem omV_mid {g : ℕ} (hg : g < omK n) (c : Fin 13) :
    omVals as xs nn n nonce (omO g + c.val) =
      cellsOfState (stF (as.take 5) xs g).perm false c := by
  have hc := c.isLt
  have hl : omO g + c.val < omE n := by simp only [omO, omE, omK] at hg ⊢; omega
  unfold omVals
  rw [ite_eq_right (by simp only [omO]; omega), ite_eq_right (by simp only [omO]; omega),
    ite_eq_left hl, show (omO g + c.val - 12) / 25 = g by simp only [omO]; omega,
    show (omO g + c.val - 12) % 25 = 12 + c.val by simp only [omO]; omega,
    ite_eq_right (by omega)]
  congr 1
  apply fin13_eq
  omega

theorem omV_tail {d : ℕ} (hd : omE n + d < (omTail n nonce).2.2) :
    omVals as xs nn n nonce (omE n + d) =
      omTailVal n nonce (stF (as.take 5) xs (omK n)).perm
        ((stF (as.take 5) xs (omK n)).absorb nn dsPowNonce).perm nn d := by
  have h12 : 12 ≤ omE n := by simp only [omE]; omega
  unfold omVals
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hd,
    Nat.add_sub_cancel_left]

theorem omV_fin (u : ℕ) :
    omVals as xs nn n nonce ((omTail n nonce).2.2 + u) =
      omFinVal n nonce (if nonce = 1 then ((stF (as.take 5) xs (omK n)).absorb nn dsPowNonce).perm
        else (stF (as.take 5) xs (omK n)).perm) (as.getD 5 0) u := by
  have hf := omTail_f_gt n nonce
  have h12 : 12 ≤ omE n := by simp only [omE]; omega
  unfold omVals
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), Nat.add_sub_cancel_left]

end Eval

/-- A full group of words. -/
theorem grp_getD {xs : List E} {g : ℕ} (h : 4 * g + 4 ≤ xs.length) :
    grp xs g = [xs.getD (4 * g) 0, xs.getD (4 * g + 1) 0, xs.getD (4 * g + 2) 0,
      xs.getD (4 * g + 3) 0] := by
  have e : ∀ j (hj : j < xs.length), xs.getD j 0 = xs[j] := fun j hj ↦ List.getD_eq_getElem _ _ hj
  apply List.ext_getElem
  · simp [grp]; omega
  · intro i h1 h2
    simp only [grp, List.getElem_take, List.getElem_drop]
    simp only [List.length_cons, List.length_nil] at h2
    interval_cases i
    · exact (e _ (by omega)).symm
    · exact (e _ (by omega)).symm
    · exact (e _ (by omega)).symm
    · exact (e _ (by omega)).symm

/-- The last group of two words. -/
theorem grp_getD2 {xs : List E} {g : ℕ} (h : xs.length = 4 * g + 2) :
    grp xs g = [xs.getD (4 * g) 0, xs.getD (4 * g + 1) 0] := by
  have e : ∀ j (hj : j < xs.length), xs.getD j 0 = xs[j] := fun j hj ↦ List.getD_eq_getElem _ _ hj
  apply List.ext_getElem
  · simp [grp]; omega
  · intro i h1 h2
    simp only [grp, List.getElem_take, List.getElem_drop]
    simp only [List.length_cons, List.length_nil] at h2
    interval_cases i
    · exact (e _ (by omega)).symm
    · exact (e _ (by omega)).symm

/-- The last group of one word. -/
theorem grp_getD1 {xs : List E} {g : ℕ} (h : xs.length = 4 * g + 1) :
    grp xs g = [xs.getD (4 * g) 0] := by
  have e : ∀ j (hj : j < xs.length), xs.getD j 0 = xs[j] := fun j hj ↦ List.getD_eq_getElem _ _ hj
  apply List.ext_getElem
  · simp [grp]; omega
  · intro i h1 h2
    simp only [grp, List.getElem_take, List.getElem_drop]
    simp only [List.length_cons, List.length_nil] at h2
    interval_cases i
    exact (e _ (by omega)).symm


theorem stCap_length (cap xs : List E) (hc : cap.length = 5) : ∀ g, (stCap cap xs g).length = 5
  | 0 => hc
  | _ + 1 => rfl

/-- **`opening_message` is complete.** -/
theorem om_complete {name : String} {f : Fn} (n nonce : ℕ) (hcase : OmCase n nonce) (hn : 1 ≤ n)
    (h64 : n + nonce < 64) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbody : f.body = omBody n nonce) (rd : Reader) (args rets : List E)
    (h : MeaningOpeningMessage n nonce rd args rets) : coreProgram.Rel rd name args rets := by
  obtain ⟨f0, f1, f2, f3, f4, cur, out, rfl⟩ : ∃ f0 f1 f2 f3 f4 cur out,
      args = [f0, f1, f2, f3, f4, cur, out] := by
    match args, h with
    | [a, b, c, d, e, g, k], _ => exact ⟨a, b, c, d, e, g, k, rfl⟩
  obtain ⟨xs, hlen, hcur, hout, nn, hnn, hret⟩ := h
  let as : List E := [f0, f1, f2, f3, f4, cur, out]
  let cap : List E := [f0, f1, f2, f3, f4]
  have htake : as.take 5 = cap := rfl
  let σ : Val := fun v ↦ omVals as xs nn n nonce v.idx
  have ev : ∀ k, σ (.n k) = omVals as xs nn n nonce k := fun _ ↦ rfl
  let S0 := (stF cap xs (omK n)).perm
  let S1 := ((stF cap xs (omK n)).absorb nn dsPowNonce).perm
  have hx : ∀ p < n, LoadHolds rd cur p (xs.getD p 0) ∧ LoadHolds rd out p (xs.getD p 0) :=
    fun p hp ↦ by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact ⟨hcur p (by omega), hout p (by omega)⟩
  have e5 : σ (.n 5) = cur := by rw [ev, omV_head _ _ _ _ _ (by omega)]; rfl
  have e6 : σ (.n 6) = out := by rw [ev, omV_head _ _ _ _ _ (by omega)]; rfl
  have vW : ∀ p < n, ∀ u < 3,
      σ (.n (omW p + u)) = if u = 2 then word 0 dsObserve else xs.getD p 0 :=
    fun p hp u hu ↦ omV_word as xs nn n nonce hp hu
  have vM : ∀ g < omK n, ∀ c : Fin 13,
      σ (.n (omO g + c.val)) = cellsOfState (stF cap xs g).perm false c :=
    fun g hg c ↦ omV_mid as xs nn n nonce hg c
  have vT : ∀ d, omE n + d < (omTail n nonce).2.2 →
      σ (.n (omE n + d)) = omTailVal n nonce S0 S1 nn d :=
    fun d hd ↦ omV_tail as xs nn n nonce hd
  have vF : ∀ u, σ (.n ((omTail n nonce).2.2 + u)) =
      omFinVal n nonce (if nonce = 1 then S1 else S0) cur u :=
    fun u ↦ omV_fin as xs nn n nonce u
  have capK : ∀ g ≤ omK n, (run5 (omCap g)).map σ = stCap cap xs g := by
    intro g hg
    cases g with
    | zero =>
      simp only [run5, omCap, List.map_cons, List.map_nil, stCap]
      rw [ev, ev, ev, ev, ev, omV_head _ _ _ _ _ (by omega), omV_head _ _ _ _ _ (by omega),
        omV_head _ _ _ _ _ (by omega), omV_head _ _ _ _ _ (by omega),
        omV_head _ _ _ _ _ (by omega)]
      rfl
    | succ g =>
      rw [stCap_succ, ← run5_cellsO (vM g (by omega))]
      rfl
  have rateF : ∀ g, 4 * g + 4 ≤ n →
      (omRate g).map σ = pendCells ((grp xs g).map (·, dsObserve)) := by
    intro g hg
    rw [grp_getD (by omega)]
    simp only [omRate, List.map_cons, List.map_nil]
    rw [vW _ (by omega) 1 (by omega), vW _ (by omega) 2 (by omega),
      vW (4 * g + 1) (by omega) 1 (by omega), vW (4 * g + 1) (by omega) 2 (by omega),
      vW (4 * g + 2) (by omega) 1 (by omega), vW (4 * g + 2) (by omega) 2 (by omega),
      vW (4 * g + 3) (by omega) 1 (by omega), vW (4 * g + 3) (by omega) 2 (by omega)]
    rfl
  have keccakG : ∀ g, 4 * g + 4 ≤ n → (run5 (omCap g)).map σ = stCap cap xs g →
      (∀ c : Fin 13, σ (.n (omO g + c.val)) = cellsOfState (stF cap xs g).perm false c) →
      (omKeccak g).Holds rd σ := by
    intro g hg hc hO
    have hl : (grp xs g).length = 4 := by rw [length_grp]; omega
    exact keccak_of_fs (s := stF cap xs g) (by simp [stF, hl])
      (stCap_length cap xs rfl g) (by
        rw [List.map_append, rateF g hg, hc]
        simp [stF, hl])
      hO
  -- the last permutation's cells
  have hOS : ∀ c : Fin 13, σ (.n ((omTail n nonce).2.1 + c.val)) =
      cellsOfState (if nonce = 1 then S1 else S0) false c := by
    intro c
    have hc := c.isLt
    rcases hcase with ⟨rfl, h4⟩ | ⟨rfl, h2⟩ | ⟨rfl, h4⟩ | ⟨rfl, h2⟩ | ⟨rfl, h1⟩
    · have he : omO (omK n) = omE n := by simp only [omE, omO, omK] at h4 ⊢; omega
      simp only [omTail, h4, ↓reduceIte]
      rw [he, vT c.val (by simp only [omTail, h4, ↓reduceIte]; omega)]
      simp only [omTailVal, h4, ↓reduceIte, show (0 : ℕ) ≠ 1 by decide]
      exact congrArg _ (fin13_eq (by omega))
    · simp only [omTail, h2, ↓reduceIte, show (2 : ℕ) ≠ 4 by decide]
      rw [show omE n + 5 + c.val = omE n + (5 + c.val) by ring,
        vT (5 + c.val) (by simp only [omTail, h2, ↓reduceIte, show (2 : ℕ) ≠ 4 by decide]; omega)]
      simp only [omTailVal, h2, ↓reduceIte, show (2 : ℕ) ≠ 4 by decide, show (0 : ℕ) ≠ 1 by decide,
        show 5 + c.val ≠ 0 by omega, show ¬ (5 + c.val < 5) by omega]
      exact congrArg _ (fin13_eq (by omega))
    · simp only [omTail, h4, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
      rw [show omE n + 21 + c.val = omE n + (21 + c.val) by ring,
        vT (21 + c.val) (by simp only [omTail, h4, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide]; omega)]
      simp only [omTailVal, h4, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
        show ¬ (21 + c.val < 13) by omega, show ¬ (21 + c.val < 15) by omega,
        show 21 + c.val ≠ 15 by omega, show 21 + c.val ≠ 16 by omega,
        show ¬ (21 + c.val < 21) by omega]
      exact congrArg _ (fin13_eq (by omega))
    · simp only [omTail, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 4 by decide]
      rw [show omE n + 5 + c.val = omE n + (5 + c.val) by ring,
        vT (5 + c.val) (by simp only [omTail, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
          show (2 : ℕ) ≠ 4 by decide]; omega)]
      simp only [omTailVal, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 4 by decide,
        show ¬ (5 + c.val < 2) by omega, show 5 + c.val ≠ 2 by omega, show ¬ (5 + c.val < 5) by omega]
      exact congrArg _ (fin13_eq (by omega))
    · simp only [omTail, h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) ≠ 4 by decide,
        show (1 : ℕ) ≠ 2 by decide]
      rw [show omE n + 8 + c.val = omE n + (8 + c.val) by ring,
        vT (8 + c.val) (by simp only [omTail, h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
          show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 2 by decide]; omega)]
      simp only [omTailVal, h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) ≠ 4 by decide,
        show (1 : ℕ) ≠ 2 by decide,
        show ¬ (8 + c.val < 2) by omega, show 8 + c.val ≠ 2 by omega, show 8 + c.val ≠ 3 by omega,
        show ¬ (8 + c.val < 8) by omega]
      exact congrArg _ (fin13_eq (by omega))
  -- the tail's atoms
  have htail : ∀ a ∈ (omTail n nonce).1, a.Holds rd σ := by
    have hpad : ∀ b d, omE n + d < (omTail n nonce).2.2 → b = omE n + d →
        omTailVal n nonce S0 S1 nn d = 0 → σ (.n b) = word 0 0 := by
      intro b d hd hb hv
      rw [hb, vT d hd, hv, word_zero]
    have hKn : omK n ≤ omK n := le_rfl
    rcases hcase with ⟨rfl, h4⟩ | ⟨rfl, h2⟩ | ⟨rfl, h4⟩ | ⟨rfl, h2⟩ | ⟨rfl, h1⟩
    · intro a ha
      simp only [omTail, h4, ↓reduceIte, List.mem_singleton] at ha
      subst ha
      have he : omO (omK n) = omE n := by simp only [omE, omO, omK] at h4 ⊢; omega
      refine keccakG _ (by simp only [omK] at h4 ⊢; omega) (capK _ hKn) fun c ↦ ?_
      have := hOS c
      simp only [omTail, h4, ↓reduceIte, show (0 : ℕ) ≠ 1 by decide] at this
      exact this
    · have hf : (omTail n 0).2.2 = omE n + 18 := by
        simp only [omTail, h2, ↓reduceIte, show (2 : ℕ) ≠ 4 by decide]
      intro a ha
      simp only [omTail, h2, ↓reduceIte, show (2 : ℕ) ≠ 4 by decide, padAs, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (rfl | rfl | rfl | rfl | rfl) | rfl
      · show σ (.n (omE n)) = word 1 0
        rw [show omE n = omE n + 0 by ring, vT 0 (by omega)]
        simp [omTailVal, h2]
      · exact hpad _ 1 (by omega) rfl (by simp [omTailVal, h2])
      · exact hpad _ 2 (by omega) rfl (by simp [omTailVal, h2])
      · exact hpad _ 3 (by omega) rfl (by simp [omTailVal, h2])
      · exact hpad _ 4 (by omega) rfl (by simp [omTailVal, h2])
      · have hg := grp_getD2 (xs := xs) (g := omK n) (by omega)
        have hl : (grp xs (omK n)).length = 2 := by rw [hg]; rfl
        refine keccak_of_fs (s := stF cap xs (omK n)) (by simp [stF, hl])
          (stCap_length cap xs rfl _) ?_ fun c ↦ ?_
        · rw [List.map_append, capK _ hKn]
          simp only [List.map_cons, List.map_nil, stF, hg]
          rw [vW _ (by omega) 1 (by omega), vW _ (by omega) 2 (by omega),
            vW (4 * omK n + 1) (by omega) 1 (by omega), vW (4 * omK n + 1) (by omega) 2 (by omega),
            hpad _ 1 (by omega) rfl (by simp [omTailVal, h2]),
            hpad _ 2 (by omega) rfl (by simp [omTailVal, h2]),
            hpad _ 3 (by omega) rfl (by simp [omTailVal, h2]),
            hpad _ 4 (by omega) rfl (by simp [omTailVal, h2]), word_zero]
          rfl
        · have := hOS c
          simp only [omTail, h2, ↓reduceIte, show (2 : ℕ) ≠ 4 by decide,
            show (0 : ℕ) ≠ 1 by decide] at this
          exact this
    · have hf : (omTail n 1).2.2 = omE n + 34 := by
        simp only [omTail, h4, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
      have he : omO (omK n) = omE n := by simp only [omE, omO, omK] at h4 ⊢; omega
      have hB : ∀ c : Fin 13, σ (.n (omO (omK n) + c.val)) = cellsOfState S0 false c := by
        intro c
        have hc := c.isLt
        rw [he, vT c.val (by omega)]
        simp only [omTailVal, h4, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, hc]
        exact congrArg _ (fin13_eq (by omega))
      have vnn : ∀ d, 13 ≤ d → d < 15 → σ (.n (omE n + d)) = nn := fun d h1 h2 ↦ by
        rw [vT d (by omega)]
        simp only [omTailVal, h4, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
          show ¬ (d < 13) by omega, h2]
      have v15 : σ (.n (omE n + 15)) = word 0 dsPowNonce := by
        rw [vT 15 (by omega)]; simp [omTailVal, h4]
      intro a ha
      simp only [omTail, h4, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, padAs, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)) | rfl
      · exact keccakG _ (by simp only [omK] at h4 ⊢; omega) (capK _ hKn) hB
      · show LoadHolds rd (σ (.n 5)) n (σ (.n (omE n + 13)))
        rw [e5, vnn 13 (by omega) (by omega)]; exact hnn rfl
      · show σ (.n (omE n + 14)) = σ (.n (omE n + 13))
        rw [vnn 14 (by omega) (by omega), vnn 13 (by omega) (by omega)]
      · exact v15
      · show σ (.n (omE n + 16)) = word 1 0
        rw [vT 16 (by omega)]; simp [omTailVal, h4]
      · exact hpad _ 17 (by omega) (by ring) (by simp [omTailVal, h4])
      · exact hpad _ 18 (by omega) (by ring) (by simp [omTailVal, h4])
      · exact hpad _ 19 (by omega) (by ring) (by simp [omTailVal, h4])
      · exact hpad _ 20 (by omega) (by ring) (by simp [omTailVal, h4])
      · have hl : (grp xs (omK n)).length = 4 := by rw [length_grp]; omega
        have habs : (stF cap xs (omK n)).absorb nn dsPowNonce =
            ⟨capOf S0, [(nn, dsPowNonce)]⟩ := by
          simp [Fs.absorb, stF, hl, rateScalars, S0]
        refine keccak_of_fs (s := ⟨capOf S0, [(nn, dsPowNonce)]⟩) (by simp) rfl ?_ fun c ↦ ?_
        · rw [List.map_append, show omE n + 8 = omO (omK n) + 8 by rw [he], run5_cellsO hB]
          simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
          rw [vnn 14 (by omega) (by omega), v15,
            hpad _ 17 (by omega) (by ring) (by simp [omTailVal, h4]),
            hpad _ 18 (by omega) (by ring) (by simp [omTailVal, h4]),
            hpad _ 19 (by omega) (by ring) (by simp [omTailVal, h4]),
            hpad _ 20 (by omega) (by ring) (by simp [omTailVal, h4]), word_zero]
          rfl
        · have := hOS c
          simp only [omTail, h4, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide] at this
          rw [this, ← habs]
    · have hf : (omTail n 1).2.2 = omE n + 18 := by
        simp only [omTail, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 4 by decide]
      have vnn : ∀ d, d < 2 → σ (.n (omE n + d)) = nn := fun d hd ↦ by
        rw [vT d (by omega)]
        simp only [omTailVal, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
          show (2 : ℕ) ≠ 4 by decide, hd]
      have v2 : σ (.n (omE n + 2)) = word 0 dsPowNonce := by
        rw [vT 2 (by omega)]; simp [omTailVal, h2]
      intro a ha
      simp only [omTail, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 4 by decide,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (rfl | rfl | rfl | rfl | rfl) | rfl
      · show LoadHolds rd (σ (.n 5)) n (σ (.n (omE n)))
        rw [e5, show omE n = omE n + 0 by ring, vnn 0 (by omega)]; exact hnn rfl
      · show σ (.n (omE n + 1)) = σ (.n (omE n))
        rw [vnn 1 (by omega), show omE n = omE n + 0 by ring, vnn 0 (by omega)]
      · exact v2
      · exact hpad _ 3 (by omega) (by ring) (by simp [omTailVal, h2])
      · exact hpad _ 4 (by omega) (by ring) (by simp [omTailVal, h2])
      · have hg := grp_getD2 (xs := xs) (g := omK n) (by omega)
        have habs : (stF cap xs (omK n)).absorb nn dsPowNonce =
            ⟨stCap cap xs (omK n), [(xs.getD (4 * omK n) 0, dsObserve),
              (xs.getD (4 * omK n + 1) 0, dsObserve), (nn, dsPowNonce)]⟩ := by
          simp [Fs.absorb, stF, hg, rateScalars]
        refine keccak_of_fs (s := ⟨stCap cap xs (omK n), [(xs.getD (4 * omK n) 0, dsObserve),
          (xs.getD (4 * omK n + 1) 0, dsObserve), (nn, dsPowNonce)]⟩) (by simp)
          (stCap_length cap xs rfl _) ?_ fun c ↦ ?_
        · rw [List.map_append, capK _ hKn]
          simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
          rw [vW _ (by omega) 1 (by omega), vW _ (by omega) 2 (by omega),
            vW (4 * omK n + 1) (by omega) 1 (by omega), vW (4 * omK n + 1) (by omega) 2 (by omega),
            vnn 1 (by omega), v2,
            hpad _ 3 (by omega) (by ring) (by simp [omTailVal, h2]),
            hpad _ 4 (by omega) (by ring) (by simp [omTailVal, h2]), word_zero]
          rfl
        · have := hOS c
          simp only [omTail, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
            show (2 : ℕ) ≠ 4 by decide] at this
          rw [this, ← habs]
    · have hf : (omTail n 1).2.2 = omE n + 21 := by
        simp only [omTail, h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) ≠ 4 by decide,
          show (1 : ℕ) ≠ 2 by decide]
      have vnn : ∀ d, d < 2 → σ (.n (omE n + d)) = nn := fun d h2 ↦ by
        rw [vT d (by omega)]
        simp only [omTailVal, h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
          show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 2 by decide, h2]
      have v2 : σ (.n (omE n + 2)) = word 0 dsPowNonce := by
        rw [vT 2 (by omega)]; simp [omTailVal, h1]
      intro a ha
      simp only [omTail, h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (1 : ℕ) ≠ 4 by decide,
        show (1 : ℕ) ≠ 2 by decide,
        padAs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ((rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)) | rfl
      · show LoadHolds rd (σ (.n 5)) n (σ (.n (omE n)))
        rw [e5, show omE n = omE n + 0 by ring, vnn 0 (by omega)]; exact hnn rfl
      · show σ (.n (omE n + 1)) = σ (.n (omE n))
        rw [vnn 1 (by omega), show omE n = omE n + 0 by ring, vnn 0 (by omega)]
      · exact v2
      · show σ (.n (omE n + 3)) = word 1 0
        rw [vT 3 (by omega)]; simp [omTailVal, h1]
      · exact hpad _ 4 (by omega) (by ring) (by simp [omTailVal, h1])
      · exact hpad _ 5 (by omega) (by ring) (by simp [omTailVal, h1])
      · exact hpad _ 6 (by omega) (by ring) (by simp [omTailVal, h1])
      · exact hpad _ 7 (by omega) (by ring) (by simp [omTailVal, h1])
      · have hg := grp_getD1 (xs := xs) (g := omK n) (by omega)
        have habs : (stF cap xs (omK n)).absorb nn dsPowNonce =
            ⟨stCap cap xs (omK n), [(xs.getD (4 * omK n) 0, dsObserve), (nn, dsPowNonce)]⟩ := by
          simp [Fs.absorb, stF, hg, rateScalars]
        refine keccak_of_fs (s := ⟨stCap cap xs (omK n), [(xs.getD (4 * omK n) 0, dsObserve),
          (nn, dsPowNonce)]⟩) (by simp) (stCap_length cap xs rfl _) ?_ fun c ↦ ?_
        · rw [List.map_append, capK _ hKn]
          simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
          rw [vW _ (by omega) 1 (by omega), vW _ (by omega) 2 (by omega), vnn 1 (by omega), v2,
            hpad _ 4 (by omega) (by ring) (by simp [omTailVal, h1]),
            hpad _ 5 (by omega) (by ring) (by simp [omTailVal, h1]),
            hpad _ 6 (by omega) (by ring) (by simp [omTailVal, h1]),
            hpad _ 7 (by omega) (by ring) (by simp [omTailVal, h1]), word_zero]
          rfl
        · have := hOS c
          simp only [omTail, h1, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
            show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 2 by decide] at this
          rw [this, ← habs]
  -- the copies out and the cursor
  have hfin : ∀ a ∈ omFinal n nonce (omTail n nonce).2.1 (omTail n nonce).2.2, a.Holds rd σ := by
    intro a ha
    have o0 := hOS 0
    have o1 := hOS 1
    have o8 := hOS 8
    have o9 := hOS 9
    have o10 := hOS 10
    have o11 := hOS 11
    have o12 := hOS 12
    simp only [Fin.val_zero, Nat.add_zero] at o0
    simp only [omFinal, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show σ (.n (omTail n nonce).2.2) = σ (.n (omTail n nonce).2.1)
      rw [show (omTail n nonce).2.2 = (omTail n nonce).2.2 + 0 by ring, vF 0, o0]; rfl
    · show σ (.n ((omTail n nonce).2.2 + 1)) = σ (.n ((omTail n nonce).2.1 + 1))
      rw [vF 1, show (omTail n nonce).2.1 + 1 = (omTail n nonce).2.1 + (1 : Fin 13).val by rfl, o1]
      rfl
    · show σ (.n ((omTail n nonce).2.2 + 2)) = σ (.n ((omTail n nonce).2.1 + 8))
      rw [vF 2, show (omTail n nonce).2.1 + 8 = (omTail n nonce).2.1 + (8 : Fin 13).val by rfl, o8]
      rfl
    · show σ (.n ((omTail n nonce).2.2 + 3)) = σ (.n ((omTail n nonce).2.1 + 9))
      rw [vF 3, show (omTail n nonce).2.1 + 9 = (omTail n nonce).2.1 + (9 : Fin 13).val by rfl, o9]
      rfl
    · show σ (.n ((omTail n nonce).2.2 + 4)) = σ (.n ((omTail n nonce).2.1 + 10))
      rw [vF 4, show (omTail n nonce).2.1 + 10 = (omTail n nonce).2.1 + (10 : Fin 13).val by rfl,
        o10]
      rfl
    · show σ (.n ((omTail n nonce).2.2 + 5)) = σ (.n ((omTail n nonce).2.1 + 11))
      rw [vF 5, show (omTail n nonce).2.1 + 11 = (omTail n nonce).2.1 + (11 : Fin 13).val by rfl,
        o11]
      rfl
    · show σ (.n ((omTail n nonce).2.2 + 6)) = σ (.n ((omTail n nonce).2.1 + 12))
      rw [vF 6, show (omTail n nonce).2.1 + 12 = (omTail n nonce).2.1 + (12 : Fin 13).val by rfl,
        o12]
      rfl
    · show σ (.n ((omTail n nonce).2.2 + 7)) = word (2 ^ (n + nonce)) 0
      rw [vF 7]; rfl
    · show σ (.n ((omTail n nonce).2.2 + 8)) = σ (.n 5) * σ (.n ((omTail n nonce).2.2 + 7))
      rw [vF 8, vF 7, e5]; rfl
    · show σ (.n ((omTail n nonce).2.2 + 9)) = σ (.n ((omTail n nonce).2.2 + 8))
      rw [vF 9, vF 8]; rfl
  have hS : omState cap xs (if nonce = 1 then some nn else none) =
      if nonce = 1 then S1 else S0 := by
    by_cases h1 : nonce = 1
    · rw [ite_eq_left h1, ite_eq_left h1, omState_some _ _ (by omega), hlen]
    · rw [ite_eq_right h1, ite_eq_right h1, omState_none _ _ (by omega), hlen]
  rw [rel_iff_sem hfind, hbody, hparams, omBody]
  refine ⟨σ, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [ev, ev, ev, ev, ev, ev, ev, omV_head _ _ _ _ _ (by omega), omV_head _ _ _ _ _ (by omega),
      omV_head _ _ _ _ _ (by omega), omV_head _ _ _ _ _ (by omega), omV_head _ _ _ _ _ (by omega),
      omV_head _ _ _ _ _ (by omega), omV_head _ _ _ _ _ (by omega)]
    rfl
  rw [holdsList_atomsRet]
  refine ⟨fun a ha ↦ ?_, ?_⟩
  · simp only [omAtoms, List.mem_append] at ha
    rcases ha with ((hh | hw) | ht) | hf
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl <;>
      · show σ _ = σ _
        rw [ev, ev, omV_head _ _ _ _ _ (by omega), omV_head _ _ _ _ _ (by omega)]
        rfl
    · simp only [omWords, List.mem_flatMap, List.mem_range, List.mem_append] at hw
      obtain ⟨p, hp, hwa | hk⟩ := hw
      · simp only [omWordAs, List.mem_cons, List.not_mem_nil, or_false] at hwa
        have w0 : σ (.n (omW p)) = xs.getD p 0 := by
          rw [show omW p = omW p + 0 by ring, vW p hp 0 (by omega)]; rfl
        rcases hwa with rfl | rfl | rfl | rfl
        · show LoadHolds rd (σ (.n 5)) p (σ (.n (omW p)))
          rw [e5, w0]; exact (hx p hp).1
        · show σ (.n (omW p + 1)) = σ (.n (omW p))
          rw [vW p hp 1 (by omega), w0]; rfl
        · show σ (.n (omW p + 2)) = word 0 dsObserve
          rw [vW p hp 2 (by omega)]; rfl
        · show LoadHolds rd (σ (.n 6)) p (σ (.n (omW p)))
          rw [e6, w0]; exact (hx p hp).2
      · split_ifs at hk with hc
        · simp only [List.mem_singleton] at hk
          subst hk
          have hg : p / 4 < omK n := by simp only [omK]; omega
          exact keccakG _ (by omega) (capK _ (by omega)) (vM _ hg)
        · simp at hk
    · exact htail a ht
    · exact hfin a hf
  · simp only [omRets, List.map_cons, List.map_nil]
    rw [hret, hS, vF 1, vF 2, vF 3, vF 4, vF 5, vF 6, vF 9,
      show (omTail n nonce).2.2 = (omTail n nonce).2.2 + 0 by ring, vF 0, ← word_two_pow h64]
    rfl

/-- `opening_message__L{n}_L{nonce}`'s core IR is its meaning, for every deployed message. -/
def opening_message_Spec : Prop := opening_message_SpecP coreProgram

/-- **`opening_message`'s core IR is its meaning**, for every deployed message. -/
theorem opening_message_holds : opening_message_Spec := by
  intro p hp rd args rets
  obtain ⟨hc, hn, h64⟩ := omCase_deployed p hp
  have go : ∀ {fn : Fn}, (coreProgram.find? (omName p) = some fn ∧
      fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧ fn.body = omBody p.1 p.2) →
      (coreProgram.Rel rd (omName p) args rets ↔ MeaningOpeningMessage p.1 p.2 rd args rets) :=
    fun ⟨h1, h2, h3⟩ ↦ ⟨om_sound _ _ hc hn h64 h1 h2 h3 rd args rets,
      om_complete _ _ hc hn h64 h1 h2 h3 rd args rets⟩
  simp only [omDeployed, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact go om_found_1_1
  · exact go om_found_6_1
  · exact go om_found_8_1
  · exact go om_found_12_1
  · exact go om_found_20_1
  · exact go om_found_36_1

end
end LeanVM.Guest.B1
