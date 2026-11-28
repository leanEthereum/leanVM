module

public import LeanVM.Guest.Complete.Claims.KidDigest
public import LeanVM.Guest.Complete.Claims.Field

/-!
# A child's claim list, at every position

`kidList_atEvery`: `child_claim_list_digest` on a child's claims at the slots `os` of the table at
`g^eP` (claim `j`'s four cells at `4 os[j]`), its coverage marks at `g^(rg + os[j])` (`g^b` along
strictly increasing slots, else `g^(b + j)`), the slots below `L`: at every frame and cursor past
its block, its end within `2^40` of its cursor, popping `Prover.childSlotPushes os`, every node
exact. The walk is the one the prover's hint picks: the gap walk (`mono_callAtA`) when the slots
increase, else the walk by hinted indices (`any_callAtA`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## Lists -/

theorem getD_flatMap_four {α : Type} {f : α → List E} (hf : ∀ a, (f a).length = 4) :
    ∀ (L : List α) (j : ℕ) (hj : j < L.length) (c : ℕ), c < 4 →
      (L.flatMap f).getD (4 * j + c) 0 = (f L[j]).getD c 0
  | [], _, hj, _, _ => absurd hj (by simp)
  | a :: L, 0, _, c, hc => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hf]; omega)]
    simp [List.getD_eq_getElem?_getD]
  | a :: L, j + 1, hj, c, hc => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hf]; omega), hf,
      show 4 * (j + 1) + c - 4 = 4 * j + c by omega, ← List.getD_eq_getElem?_getD,
      getD_flatMap_four hf L j (by simpa using hj) c hc]
    simp

theorem increasing_lt : ∀ (os : List ℕ), Prover.increasing os = true →
    ∀ i (hi : i + 1 < os.length), os[i] < os[i + 1]
  | [], _, _, hi => absurd hi (by simp)
  | [_], _, _, hi => absurd hi (by simp)
  | a :: b :: l, h, i, hi => by
    simp only [Prover.increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := increasing_lt (b :: l) h.2 i (by simpa using hi)
      simpa using this

theorem slotGaps_eq : ∀ (os : List ℕ) (next : ℕ), Prover.slotGaps next os =
    (List.range os.length).map fun i => os.getD i 0 - (if i = 0 then next else os.getD (i - 1) 0 + 1)
  | [], _ => rfl
  | o :: os, next => by
    rw [Prover.slotGaps, slotGaps_eq os (o + 1), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    cases i <;> simp

/-! ## A child's list -/

theorem allocBase_ccd (al : String → Bool) (F : String) (cur : ℕ) :
    allocBase (al F) (allocBase (al "list_split") cur + B2C.fs "list_split") + B2C.fs F ≤ cur + 2 ^ 32 := by
  have a0 := allocBase_le (al "list_split") cur
  have a1 := allocBase_le (al F) (allocBase (al "list_split") cur + B2C.fs "list_split")
  have f0 := B2C.fs_lt "list_split"
  have f1 := B2C.fs_lt F
  omega

set_option maxHeartbeats 4000000 in
/-- **A child's claim list, at every position.** -/
theorem kidList_atEvery {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {α : Type} {f : α → List E}
    (hf : ∀ a, (f a).length = 4) {cx : List α} {os : List ℕ} (hlen : os.length = cx.length)
    (hn : cx.length < 2 ^ 19) {eP rg L b : ℕ} (hL : L < 2 ^ 19) (hos : ∀ j (hj : j < os.length), os[j] < L)
    {R : ℕ → Prop} (hR2 : ∀ j (hj : j < os.length), R (rg + os[j]))
    (hR3 : ∀ j (hj : j < os.length), ∀ c < 4, R (eP + 4 * os[j] + c)) {Pre : Reader → Prop}
    (hmark : ∀ rd, LowDef k rd → Pre rd → ∀ j (hj : j < os.length),
      LoadHolds rd (gen ^ (rg + os[j])) 0 (if Prover.increasing os then gen ^ b else gen ^ (b + j)))
    (hcell : ∀ rd, LowDef k rd → Pre rd → ∀ j (hj : j < os.length), ∀ c < 4,
      LoadHolds rd (gen ^ eP) (4 * os[j] + c) ((f (cx[j]'(hlen ▸ hj))).getD c 0))
    (hbd : ∀ rd, LowDef k rd → Pre rd → BoundMem rd (L + 1))
    {d : Digest} (hd : keccak256 (cellsBytes (cx.flatMap f)) = d) (lo : ℕ) :
    AtEveryE al k "child_claim_list_digest" [gen ^ eP, gen ^ rg, gen ^ b, gen ^ L, gen ^ cx.length]
      (Prover.digestCells d) R Pre (PopsPost (Prover.childSlotPushes os)) (B2C.fs "child_claim_list_digest") lo := by
  intro fp cur _ hfc
  set n := cx.length with hnd
  set o : ℕ → ℕ := fun j => os.getD j 0 with ho
  set cells := cx.flatMap f with hcells
  have hl : cells.length = 4 * n := flatMap_length_const fun c _ => hf c
  have hoj : ∀ j (hj : j < n), o j = os[j]'(by omega) := fun j hj => List.getD_eq_getElem _ _ _
  have hexact : ∀ rd (t : Memory.Tree) (args rets : List E), t.name = "child_claim_list_digest" →
      t.Valid coreProgram rd args rets → t.Every (ExactAt coreProgram rd) := fun rd t _ _ hn' hv =>
    every_exact_of_free child_claim_list_digest_exact hv hn' rd
  rcases Nat.eq_zero_or_pos n with h0 | hn0
  · -- the empty list
    have hcx : cx = [] := List.eq_nil_of_length_eq_zero h0
    have hos0 : os = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hcx hos0
    refine ⟨cur, fun _ => by omega, ?_⟩
    have h := ccd0_callAtA (fs := B2C.fs) (al := al) (cert := B2C.cert) (k := k) (eP := eP) (rg := rg) (L := L)
      (base := gen ^ b) (R := R) (Pre := Pre) hfc
    rw [← hd]
    refine h.withValid fun rd t _ _ hn' hv _ hp => ⟨SameStreams.of_eq ?_, hexact rd t _ _ hn' hv⟩
    rw [hp]; simp [Prover.childSlotPushes]
  have hn0' : n ≠ 0 := by omega
  have hR2' : ∀ j < n, R (rg + o j) := fun j hj => by rw [hoj j hj]; exact hR2 j (by omega)
  have hR3' : ∀ j < n, ∀ c < 4, R (eP + 4 * o j + c) := fun j hj c hc => by rw [hoj j hj]; exact hR3 j (by omega) c hc
  have hcellj : ∀ rd, LowDef k rd → Pre rd → ∀ j < n, ∀ c < 4,
      LoadHolds rd (gen ^ eP) (4 * o j + c) (cells.getD (4 * j + c) 0) := fun rd hl' hp j hj c hc => by
    rw [hoj j hj, hcells, getD_flatMap_four hf cx j hj c hc]
    exact hcell rd hl' hp j (by omega) c hc
  have hmarkj : ∀ rd, LowDef k rd → Pre rd → ∀ j < n, LoadHolds rd (gen ^ rg * gen ^ o j) 0
      (if Prover.increasing os then gen ^ b else gen ^ b * gen ^ j) := fun rd hl' hp j hj => by
    rw [← pow_add, hoj j hj, ← pow_add]
    exact hmark rd hl' hp j (by omega)
  have hsplit : ∀ P : List Pop, ∀ mono : Bool, (Prover.increasing os = mono) →
      ((if mono then (Prover.slotGaps 0 os).map fun x => ("child_claim_gap", [Prover.count x])
        else os.map fun x => ("child_claim_index", [Prover.count x])) = P) →
      ccPops mono n P = Prover.childSlotPushes os := by
    intro P mono hm hP
    have hne : os ≠ [] := fun h => by rw [h] at hlen; simp at hlen; omega
    have h17 : n % Prover.claimBig % Prover.claimGroup = n % 17 := Nat.mod_mod_of_dvd _ (by decide)
    rw [Prover.childSlotPushes, ← hP, hm, ccPops, hlen]
    cases mono
    · simp only [hne, Bool.false_eq_true, ↓reduceIte, ccHint, Prover.listSplit, h17, Prover.count,
        LeanVM.Protocol.Verifier.gpow]
      rfl
    · simp only [hne, ↓reduceIte, ccHint, Prover.listSplit, h17, Prover.count, LeanVM.Protocol.Verifier.gpow]
      rfl
  cases hinc : Prover.increasing os
  · -- the walk by hinted indices
    have hrec : ∀ rd, LowDef k rd → Pre rd →
        RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) (gen ^ b) n o cells ∧ BoundMem rd L := by
      intro rd hl' hp
      refine ⟨fun j hj => ⟨⟨by have := hos j (by omega); rw [hoj j hj]; omega,
        L - o j - 1, by omega, by rw [hoj j hj]; have := hos j (by omega); congr 1; omega⟩, ?_,
        hcellj rd hl' hp j hj⟩, fun i hi => hbd rd hl' hp i (by omega)⟩
      have := hmarkj rd hl' hp j hj
      rwa [hinc] at this
    have h := ccdNe_callAtA (fs := B2C.fs) (al := al) (cert := B2C.cert) coreProgram_wf hk false
      (eP := eP) (rg := rg) (L := L) (base := gen ^ b) (D := keccak256 (cellsBytes cells)) hn0' hn
      (R := R) (Pre := Pre) (P := idxPops o 0 n) (armE := anyEnd B2C.fs al n)
      (fun fpA cA hA => (any_callAtA (fs := B2C.fs) (al := al) (cert := B2C.cert) hk (o := o) hn hl
        (by omega) hR2' hR3' hrec hA).mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h)
        fun _ _ _ h => h.2) hfc
    refine ⟨anyEnd B2C.fs al n (allocBase (al (ccF false)) (allocBase (al "list_split") cur + B2C.fs "list_split") +
      B2C.fs (ccF false)), fun _ => ?_, ?_⟩
    · have := anyEnd_le al hn (c := allocBase (al (ccF false)) (allocBase (al "list_split") cur +
        B2C.fs "list_split") + B2C.fs (ccF false))
      have := allocBase_ccd al (ccF false) cur
      omega
    rw [← hd]
    refine h.withValid fun rd t _ _ hn' hv _ hp => ⟨SameStreams.of_eq ?_, hexact rd t _ _ hn' hv⟩
    rw [hp]
    refine hsplit _ false hinc ?_
    simp only [Bool.false_eq_true, ↓reduceIte, idxPops, Prover.count, LeanVM.Protocol.Verifier.gpow]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
    rw [hoj i (by simpa using h2)]
  · -- the gap walk
    have hlt := increasing_lt os hinc
    have hinc' : ∀ i < n, mStart o i ≤ o i := by
      intro i hi
      unfold mStart
      split
      · omega
      · have := hlt (i - 1) (by omega)
        rw [hoj i hi, hoj (i - 1) (by omega)]
        simp only [show i - 1 + 1 = i by omega] at this
        omega
    have hend' : mStart o n ≤ L := by
      unfold mStart
      simp only [hn0', ↓reduceIte]
      rw [hoj (n - 1) (by omega)]
      have := hos (n - 1) (by omega)
      omega
    have hrec : ∀ rd, LowDef k rd → Pre rd → MRec rd (gen ^ rg) L (gen ^ eP) (gen ^ b) n o cells ∧
        BoundMem rd (L + 1) := by
      intro rd hl' hp
      refine ⟨fun j hj => ⟨by rw [hoj j hj]; exact hos j (by omega), ?_, hcellj rd hl' hp j hj⟩, hbd rd hl' hp⟩
      have := hmarkj rd hl' hp j hj
      rw [hinc] at this
      exact this
    have h := ccdNe_callAtA (fs := B2C.fs) (al := al) (cert := B2C.cert) coreProgram_wf hk true
      (eP := eP) (rg := rg) (L := L) (base := gen ^ b) (D := keccak256 (cellsBytes cells)) hn0' hn
      (R := R) (Pre := Pre) (P := gapPops o 0 n) (armE := monoEnd B2C.fs al n)
      (fun fpA cA hA => (mono_callAtA (fs := B2C.fs) (al := al) (cert := B2C.cert) hk (o := o) hn hl
        hinc' hend' hR2' hR3' hrec hA).mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h)
        fun _ _ _ h => h.2) hfc
    refine ⟨monoEnd B2C.fs al n (allocBase (al (ccF true)) (allocBase (al "list_split") cur + B2C.fs "list_split") +
      B2C.fs (ccF true)), fun _ => ?_, ?_⟩
    · have := monoEnd_le al hn (c := allocBase (al (ccF true)) (allocBase (al "list_split") cur +
        B2C.fs "list_split") + B2C.fs (ccF true))
      have := allocBase_ccd al (ccF true) cur
      omega
    rw [← hd]
    refine h.withValid fun rd t _ _ hn' hv _ hp => ⟨SameStreams.of_eq ?_, hexact rd t _ _ hn' hv⟩
    rw [hp]
    refine hsplit _ true hinc ?_
    simp only [↓reduceIte, gapPops, Prover.count, LeanVM.Protocol.Verifier.gpow, slotGaps_eq, List.map_map]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add, Function.comp_apply, mGap, mStart]
    rfl

end
end LeanVM.Guest.Complete
