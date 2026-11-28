/-
  LeanVM.Guest.B1.KeccakGkr.PackChain

  A layer's pack and segment rounds: `keccak_layer`'s two dispatches to `layer_rounds` chain into
  `packRunF` of the claim's point.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerRounds
public import LeanVM.Guest.B1.KeccakGkr.LayerT

/-!
# The pack rounds (`keccak_layer`)

`keccak_layer` runs the claim's `y = 16·⌊y/16⌋ + y % 16` pack and segment rounds as a dispatch on
`step_g = g^⌊y/16⌋` to `layer_rounds__L0` or `__L16` (`stepNames`), then one on `rem_g = g^(y % 16)`
to `layer_rounds__L{y % 16}` (`remNames`) on the coordinates and challenges `16·⌊y/16⌋` on.
`pack_rounds`: the two runs chain (`packRunF_append`) into `packRunF` of the claim's point, the
messages read from the cursor and the challenges stored at `point`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-! ## `packRunF` -/

/-- `packRunF` past its last round. -/
theorem packRunF_nil (v : E) (s : Fs) : packRunF [] [] v s = ((v, []), s) := rfl

/-- `packRunF` over a prefix of rounds, then the rest. -/
theorem packRunF_append :
    ∀ (A rest : List E) (MA restM : List (E × E)) (v : E) (s : Fs), MA.length = A.length →
      packRunF (A ++ rest) (MA ++ restM) v s =
        (((packRunF rest restM (packRunF A MA v s).1.1 (packRunF A MA v s).2).1.1,
          (packRunF A MA v s).1.2 ++
            (packRunF rest restM (packRunF A MA v s).1.1 (packRunF A MA v s).2).1.2),
          (packRunF rest restM (packRunF A MA v s).1.1 (packRunF A MA v s).2).2)
  | [], rest, [], restM, v, s, _ => by simp [packRunF_nil]
  | r :: A, rest, (g1, g2) :: MA, restM, v, s, h => by
    have h' : MA.length = A.length := by simpa using h
    rw [List.cons_append, List.cons_append, packRunF_cons, packRunF_cons,
      packRunF_append A rest MA restM _ _ h']
    simp only [List.cons_append]
  | [], _, _ :: _, _, _, _, h | _ :: _, _, [], _, _, _, h => by simp at h

/-- The challenges are as many as the rounds. -/
theorem packRunF_chs_length : ∀ (rs : List E) (ms : List (E × E)) (v : E) (s : Fs),
    ms.length = rs.length → (packRunF rs ms v s).1.2.length = rs.length
  | [], [], _, _, _ => rfl
  | r :: rs, (g1, g2) :: ms, v, s, h => by
    rw [packRunF_cons]
    simp only [List.length_cons]
    rw [packRunF_chs_length rs ms _ _ (by simpa using h)]
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp at h

/-- The capacity stays five cells. -/
theorem packRunF_cap_length : ∀ (rs : List E) (ms : List (E × E)) (v : E) (s : Fs),
    s.cap.length = 5 → (packRunF rs ms v s).2.cap.length = 5
  | [], _, _, _, h => h
  | _ :: _, [], _, _, h => h
  | r :: rs, (g1, g2) :: ms, v, s, _ => by
    simp only [packRunF]
    exact packRunF_cap_length rs ms _ _ rfl

/-! ## Words -/

theorem word_16 : word 16 0 = gen ^ 4 := by
  rw [show (16 : ℕ) = 2 ^ 4 from rfl]; exact word_two_pow (by decide)

theorem gen_pow_ne_one {h : ℕ} (h0 : 0 < h) (hlt : h < ordG) : 1 + gen ^ h ≠ 0 := by
  intro e
  have : gen ^ h = gen ^ 0 := by rw [pow_zero]; exact (e_add_eq_zero_iff.mp e).symm
  have := gen_pow_inj (by unfold ordG at hlt; omega) (by decide) this
  omega

/-! ## Memory runs -/

theorem readsAt_unique' {p : E} {l1 l2 : List E} (h1 : ReadsAt rd p l1) (h2 : ReadsAt rd p l2)
    (hl : l1.length = l2.length) : l1 = l2 :=
  List.ext_getElem hl fun k hk1 hk2 ↦ loadHolds_unique (h1 k hk1) (h2 k hk2)

theorem readsAt_take {p : E} {l : List E} (h : ReadsAt rd p l) (n : ℕ) : ReadsAt rd p (l.take n) :=
  fun k hk ↦ by
    simp only [List.length_take] at hk
    rw [List.getElem_take]
    exact h k (by omega)

theorem readsAt_drop {p : E} {l : List E} (h : ReadsAt rd p l) (n : ℕ) :
    ReadsAt rd (p * gen ^ n) (l.drop n) := by
  rw [readsAt_gen_pow_mul]
  intro k hk
  simp only [List.length_drop] at hk
  rw [List.getElem_drop]
  exact h (n + k) (by omega)

/-! ## The dispatches' names -/

theorem stepNames_getD {j : ℕ} (hj : j < 2) : stepNames.getD j "" = lrNames.getD (krStep * j) "" := by
  interval_cases j <;> rfl

theorem remNames_getD {j : ℕ} (hj : j < 16) : remNames.getD j "" = lrNames.getD j "" := by
  interval_cases j <;> rfl

/-! ## The pack rounds -/

/-- **The pack rounds**: the two dispatches' runs, on the coordinates `pts` at `prev_point`, chain
into `packRunF` of `pts`, the messages read from the cursor `cur` and the challenges stored at
`point`; the second dispatch returns its result, the cursor `2y` words on. -/
theorem pack_rounds {pp pt sg rg cur hv tb : E} {capS pts r1 r2 : List E} {y j1 j2 : ℕ}
    (hsg : sg = gen ^ (y / krStep)) (hrg : rg = gen ^ (y % krStep)) (hy32 : y < 32)
    (hcapS : capS.length = 5) (hpts : pts.length = y) (hpp : ReadsAt rd pp pts)
    (hj1 : j1 < 2) (hsgj : sg = gen ^ j1)
    (hr1 : coreProgram.Rel rd (stepNames.getD j1 "") (capS ++ [cur, hv, pp, pt, tb]) r1)
    (hj2 : j2 < 16) (hrgj : rg = gen ^ j2)
    (hr2 : coreProgram.Rel rd (remNames.getD j2 "") (r1 ++ [pp * sg ^ krStep, pt * sg ^ krStep, tb])
      r2) :
    ∃ (msgs : List (E × E)) (chs capL : List E) (curL vL : E), r2 = capL ++ [curL, vL] ∧
      capL.length = 5 ∧ msgs.length = y ∧ ReadsAt rd cur (msgs.flatMap fun m ↦ [m.1, m.2]) ∧
      ReadsAt rd pt chs ∧ chs.length = y ∧ curL = cur * gen ^ (2 * y) ∧
      (packRunF pts msgs hv ⟨capS, []⟩).1 = (vL, chs) ∧
      (packRunF pts msgs hv ⟨capS, []⟩).2 = ⟨capL, []⟩ := by
  have hlt : ∀ m, m < 32 → m < 2 ^ 64 - 1 := fun m hm ↦ by omega
  have e1 : j1 = y / krStep := gen_pow_inj (hlt _ (by omega)) (hlt _ (by simp [krStep]; omega))
    (hsgj.symm.trans hsg)
  have e2 : j2 = y % krStep := gen_pow_inj (hlt _ (by omega)) (hlt _ (by simp [krStep]; omega))
    (hrgj.symm.trans hrg)
  subst e1 e2
  rw [stepNames_getD hj1] at hr1
  rw [remNames_getD hj2] at hr2
  have M1 := layer_rounds_sound _ (by simp [krStep] at hj1 ⊢; omega) rd _ _ hr1
  obtain ⟨c0, c1, c2, c3, c4, rfl⟩ : ∃ c0 c1 c2 c3 c4, capS = [c0, c1, c2, c3, c4] := by
    match capS, hcapS with
    | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩
  simp only [List.cons_append, List.nil_append, MeaningLayerRounds] at M1
  obtain ⟨rs1, ms1, hrs1, hms1, hpp1, hcur1, hpt1, hpend1, hret1⟩ := M1
  set P1 := packRunF rs1 ms1 hv ⟨[c0, c1, c2, c3, c4], []⟩ with hP1
  have hcap1 : P1.2.cap.length = 5 := packRunF_cap_length _ _ _ _ rfl
  obtain ⟨d0, d1, d2, d3, d4, hd⟩ : ∃ d0 d1 d2 d3 d4, P1.2.cap = [d0, d1, d2, d3, d4] := by
    match P1.2.cap, hcap1 with
    | [d0, d1, d2, d3, d4], _ => exact ⟨d0, d1, d2, d3, d4, rfl⟩
  have M2 := layer_rounds_sound _ (by simp [krStep] at hj2 ⊢; omega) rd _ _ hr2
  rw [hret1, hd] at M2
  simp only [List.cons_append, List.nil_append, MeaningLayerRounds] at M2
  obtain ⟨rs2, ms2, hrs2, hms2, hpp2, hcur2, hpt2, hpend2, hret2⟩ := M2
  have hs1 : P1.2 = ⟨[d0, d1, d2, d3, d4], []⟩ := by
    rw [← hd, ← hpend1]
  set P2 := packRunF rs2 ms2 P1.1.1 ⟨[d0, d1, d2, d3, d4], []⟩ with hP2
  have hsgk : sg ^ krStep = gen ^ (krStep * (y / krStep)) := by rw [hsgj, ← pow_mul, mul_comm]
  -- The coordinates.
  have hpts' : pts = rs1 ++ rs2 := by
    have hy : krStep * (y / krStep) + y % krStep = y := Nat.div_add_mod y krStep
    have ht := readsAt_unique' (readsAt_take hpp (krStep * (y / krStep))) hpp1
      (by simp [hrs1, hpts]; omega)
    have hd' := readsAt_unique' (readsAt_drop hpp (krStep * (y / krStep))) (by rw [← hsgk]; exact hpp2)
      (by simp [hrs2, hpts]; omega)
    rw [← List.take_append_drop (krStep * (y / krStep)) pts, ht, hd']
  have hchs1 : P1.1.2.length = krStep * (y / krStep) := by
    rw [packRunF_chs_length _ _ _ _ (by rw [hms1, hrs1])]; exact hrs1
  have hrun : packRunF pts (ms1 ++ ms2) hv ⟨[c0, c1, c2, c3, c4], []⟩ =
      ((P2.1.1, P1.1.2 ++ P2.1.2), P2.2) := by
    rw [hpts', packRunF_append _ _ _ _ _ _ (by rw [hms1, hrs1]), ← hP1, hs1]
  refine ⟨ms1 ++ ms2, P1.1.2 ++ P2.1.2, P2.2.cap,
    cur * gen ^ (2 * (krStep * (y / krStep))) * gen ^ (2 * (y % krStep)), P2.1.1, hret2,
    packRunF_cap_length _ _ _ _ rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append, hms1, hms2]
    exact Nat.div_add_mod y krStep
  · rw [List.flatMap_append, readsAt_append, length_flatMap_pairs, hms1]
    exact ⟨hcur1, hcur2⟩
  · rw [readsAt_append, hchs1, ← hsgk]
    exact ⟨hpt1, hpt2⟩
  · rw [List.length_append, hchs1, packRunF_chs_length _ _ _ _ (by rw [hms2, hrs2]), hrs2]
    exact Nat.div_add_mod y krStep
  · rw [mul_assoc, ← pow_add, ← mul_add, Nat.div_add_mod]
  · rw [hrun]
  · rw [hrun, ← hpend2]

end
end LeanVM.Guest.B1.VerifySub
