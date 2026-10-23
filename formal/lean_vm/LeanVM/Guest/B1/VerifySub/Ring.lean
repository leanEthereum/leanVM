/-
  LeanVM.Guest.B1.VerifySub.Ring

  `verify_sub`'s ring-switching front: the map's challenges, the coefficient table `c_table`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Challenges

/-!
# The ring switch's map (G:2170-2193)

* `vs_mapChallenges`: the six challenges squeezed into `map_challenges` after Flock;
* `vs_ctable`: `c_table` holds the drawn map's Frobenius coefficients `ringCoefficients`
  (V:2019). The guest expands the composition of the six two-term maps stage by stage: before
  shift `d`, the entries at multiples of `2d` are set, and the new branch fills the `d`-offset
  entries, `c[s·2d + d] = f_d · c[s·2d]^(2^d)` (`ctTab`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The challenges -/

/-- **The ring map's challenges** (G:2176-2178), squeezed from Flock's final state. -/
theorem vs_mapChallenges (h : VsHolds rd σ) {cv : Digest}
    (h0 : (σ (.n 730), σ (.n 731)) = digestScalars cv) :
    ReadsAt rd (σ (.n 732)) (sqAll 6 cv).1 ∧ (σ (.n 810), σ (.n 811)) = digestScalars (sqAll 6 cv).2 := by
  obtain ⟨hl, hc⟩ := squeezes (h := h) (m := 6) (s0 := 730) (nk := fun k ↦ 825 + 15 * k)
    (st := fun k ↦ 735 + 14 * k) (out := .n 732) (by decide +kernel) (by decide +kernel) h0
  rw [sqAll_eq]
  refine ⟨fun k hk => ?_, hc 5 (by omega)⟩
  simp only [List.length_map, List.length_range] at hk
  simpa using hl k hk

/-! ## Squaring chains -/

/-- The `d` squarings from value `u`. -/
def sqChain (u d : ℕ) : List Stmt :=
  ((List.range d).map fun i ↦ [.atom (.mul (.n (u + 1 + i)) (.n (u + i)) (.n (u + i)))]).flatten

theorem holds_sqChain {C : CallRel} {k : List E → Prop} (u d : ℕ)
    (h : Stmt.HoldsList C rd σ (sqChain u d) True k) : σ (.n (u + d)) = σ (.n u) ^ 2 ^ d := by
  rw [sqChain, holdsList_range_flatten d _ (fun _ => rfl)] at h
  have hs : ∀ i < d, σ (.n (u + 1 + i)) = σ (.n (u + i)) * σ (.n (u + i)) := fun i hi => by
    simpa [Stmt.HoldsList, Stmt.Holds, Atom.Holds] using h.1 i hi
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show u + (d + 1) = u + 1 + d by omega, hs d (by omega), ih fun i hi => hs i (by omega),
      ← pow_two, ← pow_mul, pow_succ]

/-! ## `c_table` -/

/-- Stage `st`'s shift `d = 32 >> st`. -/
abbrev ctD (st : ℕ) : ℕ := 32 >>> st

/-- Stage `st`'s first value (its challenge's) and first statement. -/
def ctV : ℕ → ℕ
  | 0 => 820
  | st + 1 => ctV st + 1 + 2 ^ st * (ctD st + 2)

def ctN : ℕ → ℕ
  | 0 => 917
  | st + 1 => ctN st + 1 + 2 ^ st * (ctD st + 3)

/-- Slot `sl` of stage `st`: read `c[sl·2d]`, square `d` times, multiply by the stage's challenge,
store at `sl·2d + d`. -/
def ctSlot (st sl : ℕ) : List Stmt :=
  let d := ctD st
  let u := ctV st + 1 + sl * (d + 2)
  [.atom (.load (.n u) (.n 733) (sl * (2 * d)))] ++ sqChain u d ++
    [.atom (.mul (.n (u + d + 1)) (.n (ctV st)) (.n (u + d))),
      .atom (.load (.n (u + d + 1)) (.n 733) (sl * (2 * d) + d))]

theorem vs_ct_loads : ∀ st < 6,
    stmtsEqb [.atom (.load (.n (ctV st)) (.n 732) st)] ((vsPre.drop (ctN st)).take 1) = true := by
  decide +kernel

theorem vs_ct_slots : ∀ st < 6, ∀ sl < 2 ^ st, stmtsEqb (ctSlot st sl)
    ((vsPre.drop (ctN st + 1 + sl * (ctD st + 3))).take (ctD st + 3)) = true := by
  decide +kernel

theorem sqChain_length (u d : ℕ) : (sqChain u d).length = d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [sqChain, List.range_succ, List.map_append, List.flatten_append, List.length_append]
    simp only [sqChain] at ih
    simp [ih]

theorem ctSlot_length (st sl : ℕ) : (ctSlot st sl).length = ctD st + 3 := by
  simp only [ctSlot, List.length_append, sqChain_length, List.length_cons, List.length_nil]
  omega

/-- The table after stage `st`. -/
def ctTab (mcs : List E) : ℕ → ℕ → E
  | 0, k => if k = 0 then 1 else 0
  | st + 1, k =>
    if k % (2 * ctD st) = ctD st then mcs.getD st 0 * ctTab mcs st (k - ctD st) ^ 2 ^ ctD st
    else ctTab mcs st k

theorem sqChain_noRet (u d : ℕ) : Stmt.noRetList (sqChain u d) = true := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [sqChain, List.range_succ, List.map_append, List.flatten_append, noRetList_append]
    simp only [sqChain] at ih
    simp [ih, Stmt.noRetList, Stmt.noRet]

theorem holds_ctSlot {k : List E → Prop} (st sl : ℕ)
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (ctSlot st sl) True k) :
    LoadHolds rd (σ (.n 733)) (sl * (2 * ctD st)) (σ (.n (ctV st + 1 + sl * (ctD st + 2)))) ∧
      LoadHolds rd (σ (.n 733)) (sl * (2 * ctD st) + ctD st)
        (σ (.n (ctV st)) * σ (.n (ctV st + 1 + sl * (ctD st + 2))) ^ 2 ^ ctD st) := by
  simp only [ctSlot, holdsList_append] at h
  rw [holdsList_noRet _ (by rfl), holdsList_noRet _ (sqChain_noRet _ _)] at h
  obtain ⟨hl, hc, hr⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hl hr
  rw [← holds_sqChain _ _ hc]
  exact ⟨hl, by rw [← hr.1]; exact hr.2⟩

theorem ctD_facts : ∀ st < 6, 0 < ctD st ∧ 64 >>> st = 2 * ctD st ∧ 64 >>> (st + 1) = ctD st ∧
    2 ^ st * (2 * ctD st) = 64 := by decide

theorem ctTab_six (mcs : List E) (hl : mcs.length = 6) (k : ℕ) (hk : k < 64) :
    ctTab mcs 6 k = (ringCoefficients mcs).getD k 0 := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ : ∃ a b c d e f, mcs = [a, b, c, d, e, f] := by
    match mcs, hl with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  simp only [ringCoefficients, ringMapShifts, Flock.ringShifts, kBits, List.getD_eq_getElem?_getD,
    List.getElem?_map, Vector.toList_mk, List.zip_cons_cons, List.zip_nil_right,
    List.getElem?_range hk, Option.map_some, Option.getD_some, List.filter_cons, List.filter_nil]
  interval_cases k <;> simp [ctTab, ctD] <;> ring

/-- **`c_table`** (G:2179-2189): the drawn map's coefficients. -/
theorem vs_ctable (h : VsHolds rd σ) {mcs : List E} (hl : mcs.length = 6)
    (hm : ReadsAt rd (σ (.n 732)) mcs) :
    ∀ k < 64, LoadHolds rd (σ (.n 733)) k ((ringCoefficients mcs).getD k 0) := by
  have h0 := h.slice 915 [.atom (.const (.n 819) (word 1 0 0)), .atom (.load (.n 819) (.n 733) 0)]
    (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h0
  have hmc : ∀ st < 6, σ (.n (ctV st)) = mcs.getD st 0 := fun st hst => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique (h.atom _ _ (vs_ct_loads st hst)) (hm st (by omega))
  have hP : ∀ st ≤ 6, ∀ k < 64, k % (64 >>> st) = 0 → LoadHolds rd (σ (.n 733)) k (ctTab mcs st k) := by
    intro st hst
    induction st with
    | zero =>
      intro k hk hk0
      rw [show k = 0 by simp at hk0; omega]
      simp only [ctTab, ↓reduceIte]
      rw [← h0.1]; exact h0.2
    | succ st ih =>
      intro k hk hkd
      obtain ⟨hd0, hd1, hd2, hd3⟩ := ctD_facts st (by omega)
      rw [hd2] at hkd
      simp only [ctTab]
      by_cases hodd : k % (2 * ctD st) = ctD st
      · simp only [hodd, ↓reduceIte]
        set sl := k / (2 * ctD st) with hsl_def
        have hsl : sl < 2 ^ st := by
          rw [hsl_def, Nat.div_lt_iff_lt_mul (by omega), hd3]; exact hk
        have hk' : k = sl * (2 * ctD st) + ctD st := by
          have := Nat.div_add_mod k (2 * ctD st); rw [hodd] at this; rw [hsl_def]; linarith
        have hs := holds_ctSlot st sl (h.slice _ _ (by
          rw [ctSlot_length]; exact vs_ct_slots st (by omega) _ hsl))
        have hread := ih (by omega) (sl * (2 * ctD st)) (by omega)
          (by rw [hd1]; exact Nat.mul_mod_left _ _)
        rw [show k - ctD st = sl * (2 * ctD st) by omega, ← loadHolds_unique hs.1 hread,
          ← hmc st (by omega), hk']
        exact hs.2
      · simp only [hodd, ↓reduceIte]
        refine ih (by omega) k hk ?_
        rw [hd1]
        have hr : k % (2 * ctD st) % ctD st = 0 := by rw [Nat.mod_mod_of_dvd _ ⟨2, by ring⟩]; exact hkd
        have hlt := Nat.mod_lt k (show 0 < 2 * ctD st by omega)
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hr
        rw [hq] at hlt hodd ⊢
        have hq2 : q < 2 := by
          by_contra hq2; exact absurd hlt (not_lt.mpr (by nlinarith))
        interval_cases q
        · simp
        · exact absurd (by ring) hodd
  intro k hk
  rw [← ctTab_six mcs hl k hk]
  exact hP 6 le_rfl k hk (by rw [show 64 >>> 6 = 1 from rfl, Nat.mod_one])

end
end LeanVM.Guest.B1.VerifySub
