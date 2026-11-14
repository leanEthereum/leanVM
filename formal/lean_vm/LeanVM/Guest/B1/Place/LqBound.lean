/-
  LeanVM.Guest.B1.Place.LqBound

  `level_queries` by a tree of exactly `lqN` words, within every words bound of its trees.
-/

module

public import LeanVM.Guest.B1.Place.LqProof
public import LeanVM.Guest.B1.Place.LpBound

/-!
# `level_queries` within a words bound

`lqN`: `level_queries`' words, its frame, its cap and flags, `verify_merkle_cap`'s frame and
`opening_queries`' `oqBound`. `LqAtE`: `LqAtD` by a tree of exactly `lqN` words. `lq_bound`: frames
below `2^32`, placed after a fresh copy of an instance's words (the rounds, the high part, the
positions, the window pointers and the windows), `level_queries` holds on a fresh memory, so a
words bound of its trees is at least `lqN`. `lqAtO_of_E`: `LqAtE` gives `LqAtO` at every words
bound of its trees.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- `level_queries`' words: its frame, its cap and flags, `verify_merkle_cap`'s frame and
`opening_queries`' words. -/
def lqN (fs : String → ℕ) (name : String) (q base folds leaf d cd mu nhs hbits fin : ℕ) : ℕ :=
  fs name + 5 * 2 ^ cd + fs ("verify_merkle_cap__L" ++ natStr cd) +
    oqBound fs (lqOqN q base folds leaf d cd mu nhs hbits fin)
      (oqLoopOf (lqOqN q base folds leaf d cd mu nhs hbits fin)) (lqIters q base)

/-- **`LqAtD` by a tree of exactly `lqN` words.** -/
def LqAtE (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String)
    (q base folds leaf d cd mu nhs hbits fin : ℕ) : Prop :=
  let s := lqOqS q base folds leaf d cd mu nhs hbits fin
  ∀ (Lin : Layout) (lam lamInv : E) (ecoefs ehs epos eqp : ℕ) (rounds : List FoldRound)
    (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest)
    (capW flW : List E) (r0 r1 : E),
    rounds.length = s.folds → (s.final = 1 → hsv.length = s.nHs) →
    OqStatic s rounds hsv qs rows sibs q →
    LqCaps s q capW flW r0 r1 qs rows sibs →
    LqReg (RegionL Lin) s q ecoefs ehs epos eqp eb →
    (∀ rd, LowDef κ rd → MemL rd Lin → LqMem rd s q ecoefs ehs epos eqp rounds hsv eb qs) →
    CompleteAtE fs cert κ name Lin
      [lam, lamInv, ofK (addressOfIndex ecoefs), ofK (addressOfIndex ehs),
        ofK (addressOfIndex epos), ofK (addressOfIndex eqp)]
      (Returns [r0, r1, lqSum s (lqOdd q base folds leaf d cd mu nhs hbits fin) (lqIters q base)
        lamInv rounds qs rows, lam ^ q]) (lqN fs name q base folds leaf d cd mu nhs hbits fin)

/-- An entry's sizes the bound's fresh instance takes. -/
def LqSmall (q base folds leaf d cd mu nhs hbits fin : ℕ) : Prop :=
  q ≤ 1024 ∧ cd ≤ 8 ∧ (lqOqS q base folds leaf d cd mu nhs hbits fin).folds ≤ 64 ∧
    (lqOqS q base folds leaf d cd mu nhs hbits fin).nHs ≤ 1024 ∧
    qwN ((lqOqS q base folds leaf d cd mu nhs hbits fin).pd +
      (lqOqS q base folds leaf d cd mu nhs hbits fin).cd)
      (lqOqS q base folds leaf d cd mu nhs hbits fin).cd ≤ 64 ∧
    oqWalkCount (lqOqN q base folds leaf d cd mu nhs hbits fin) (lqIters q base) ≤ 4096

instance (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    Decidable (LqSmall q base folds leaf d cd mu nhs hbits fin) := by
  unfold LqSmall; infer_instance

set_option maxRecDepth 100000 in
/-- **Every entry of `lqTable` is small**, by the kernel. -/
theorem lqTable_small : ∀ e ∈ lqTable,
    LqSmall e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 := by
  decide +kernel

theorem lqN_lt {fs : String → ℕ} {name : String} {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (hfs : ∀ f, fs f < 2 ^ 32) (hS : LqSmall q base folds leaf d cd mu nhs hbits fin) :
    lqN fs name q base folds leaf d cd mu nhs hbits fin < 2 ^ 50 := by
  obtain ⟨hq, hcd, -, -, -, hw⟩ := hS
  unfold lqN oqBound
  have hN : lqIters q base ≤ 1024 := by unfold lqIters; split <;> omega
  have h2 : 2 ^ cd ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) hcd
  have e1 := hfs name
  have e2 := hfs ("verify_merkle_cap__L" ++ natStr cd)
  have e3 := hfs (lqOqN q base folds leaf d cd mu nhs hbits fin)
  have e4 : (lqIters q base + 1) * fs (oqLoopOf (lqOqN q base folds leaf d cd mu nhs hbits fin)) ≤
      1025 * 2 ^ 32 := Nat.mul_le_mul (by omega) (hfs _).le
  have e5 : oqWalkCount (lqOqN q base folds leaf d cd mu nhs hbits fin) (lqIters q base) *
      fs (oqWalkOfName (lqOqN q base folds leaf d cd mu nhs hbits fin)) ≤ 4096 * 2 ^ 32 :=
    Nat.mul_le_mul hw (hfs _).le
  omega

set_option maxHeartbeats 800000 in
/-- **A fresh copy of a queries' words**: the rounds, the high part, the positions, the window
pointers and the windows, below `top ≤ 2^20`, where `level_queries` reads them. -/
theorem lq_fresh {s : Oq} {q : ℕ} {rounds : List FoldRound} {hsv : List E} {qs : ℕ → ℕ}
    (κ : ℕ) (hrl : rounds.length = s.folds) (hhs : s.final = 1 → hsv.length = s.nHs)
    (hq : q ≤ 1024) (hfo : s.folds ≤ 64) (hnh : s.nHs ≤ 1024) (hwn : qwN (s.pd + s.cd) s.cd ≤ 64) :
    ∃ (Lin0 : Layout) (e2 e3 e4 top : ℕ) (eb : ℕ → ℕ), Within Lin0 0 top ∧ DisjL Lin0 ∧
      top ≤ 2 ^ 20 ∧ LqReg (RegionL Lin0) s q 0 e2 e3 e4 eb ∧
      ∀ rd, LowDef κ rd → MemL rd Lin0 → LqMem rd s q 0 e2 e3 e4 rounds hsv eb qs := by
  obtain ⟨Wn, hWn⟩ : ∃ w, w = qwN (s.pd + s.cd) s.cd := ⟨_, rfl⟩
  obtain ⟨hsW, hhsW⟩ : ∃ l : List E, l = if s.final = 1 then hsv else [] := ⟨_, rfl⟩
  have hHle : hsW.length ≤ 1024 := by
    rw [hhsW]; split
    · next h => rw [hhs h]; exact hnh
    · simp
  have hW0 : 0 < Wn := by rw [hWn]; unfold qwN; omega
  obtain ⟨coefsW, hcoefsW⟩ : ∃ l : List E, l = (List.range (2 * rounds.length)).map fun t ↦
      if t % 2 = 0 then (rounds.getD (t / 2) ⟨0, 0⟩).alpha else (rounds.getD (t / 2) ⟨0, 0⟩).beta :=
    ⟨_, rfl⟩
  obtain ⟨posW, hposW⟩ : ∃ l : List E, l = (List.range q).map fun k ↦ eOfNat (qs k) := ⟨_, rfl⟩
  obtain ⟨e5, he5⟩ : ∃ e, e = 2 * rounds.length + hsW.length + q + q := ⟨_, rfl⟩
  obtain ⟨ptrW, hptrW⟩ : ∃ l : List E, l = (List.range q).map fun k ↦
      ofK (addressOfIndex (e5 + k * Wn)) := ⟨_, rfl⟩
  obtain ⟨winW, hwinW⟩ : ∃ l : List E, l = (List.range (q * Wn)).map fun t ↦
      gen ^ qwVal (s.pd + s.cd) s.cd (qs (t / Wn)) (t % Wn) := ⟨_, rfl⟩
  have lC : coefsW.length = 2 * rounds.length := by rw [hcoefsW]; simp
  have lP : posW.length = q := by rw [hposW]; simp
  have lR : ptrW.length = q := by rw [hptrW]; simp
  have lW : winW.length = q * Wn := by rw [hwinW]; simp
  have hWn64 : q * Wn ≤ 1024 * 64 := Nat.mul_le_mul hq (hWn ▸ hwn)
  have hkW : ∀ k < q, ∀ i < Wn, k * Wn + i < q * Wn := fun k hk i hi ↦ by
    have := Nat.mul_le_mul_right Wn (show k + 1 ≤ q by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hdm : ∀ k < q, ∀ i < Wn, (k * Wn + i) / Wn = k ∧ (k * Wn + i) % Wn = i := fun k _ i hi ↦ by
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW0, Nat.div_eq_of_lt hi, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  set e2 := 2 * rounds.length with he2
  set e3 := e2 + hsW.length with he3
  set e4 := e3 + q with he4
  refine ⟨[(0, coefsW), (e2, hsW), (e3, posW), (e4, ptrW), (e5, winW)], e2, e3, e4, e5 + q * Wn,
    fun k ↦ e5 + k * Wn, ?_, ?_, by rw [hrl] at he2; omega, ⟨fun l hl ↦ ?_, fun hf l hl ↦ ?_,
      fun k hk ↦ ⟨?_, ?_, fun i hi ↦ ?_⟩⟩, fun rd _ hm ↦ ?_⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · simp only [lC]; omega
    · simp only; omega
    · simp only [lP]; omega
    · simp only [lR]; omega
    · simp only [lW]; omega
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.Pairwise.cons ?_ (List.Pairwise.cons (fun _ h ↦ absurd h List.not_mem_nil) .nil))))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> left <;> simp only [lC] <;> omega
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> left <;> simp only <;> omega
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> left <;> simp only [lP] <;> omega
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      left; simp only [lR]; omega
  · exact ⟨(0, coefsW), by simp, Nat.zero_le _, by simp only [lC]; rw [he2, hrl]; omega⟩
  · refine ⟨(e2, hsW), by simp, Nat.le_add_right _ _, ?_⟩
    have : hsW.length = s.nHs := by rw [hhsW]; simp only [hf, ↓reduceIte]; exact hhs hf
    simp only [this]; omega
  · exact ⟨(e3, posW), by simp, Nat.le_add_right _ _, by simp only [lP]; omega⟩
  · exact ⟨(e4, ptrW), by simp, Nat.le_add_right _ _, by simp only [lR]; omega⟩
  · refine ⟨(e5, winW), by simp, by simp only; omega, ?_⟩
    have := hkW k hk i (by rw [hWn]; exact hi)
    simp only [lW]; omega
  · have hC := hm (0, coefsW) (by simp)
    have hH2 := hm (e2, hsW) (by simp)
    have hP := hm (e3, posW) (by simp)
    have hR := hm (e4, ptrW) (by simp)
    have hWi := hm (e5, winW) (by simp)
    refine ⟨fun j hj ↦ ⟨?_, ?_⟩, fun hf c hc ↦ ?_, fun k hk ↦ ⟨?_, ?_, fun i hi ↦ ?_⟩⟩
    · have := hC (2 * j) (by simp only [lC]; omega)
      simpa [hcoefsW, show 2 * j / 2 = j by omega] using this
    · have := hC (2 * j + 1) (by simp only [lC]; omega)
      simpa [hcoefsW, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1) % 2 = 1 by omega]
        using this
    · have e : hsW = hsv := by rw [hhsW]; simp only [hf, ↓reduceIte]
      subst e
      have := hH2 c hc
      rwa [List.getD_eq_getElem _ _ hc]
    · have := hP k (by rw [lP]; exact hk); simpa [hposW] using this
    · have := hR k (by rw [lR]; exact hk); simpa [hptrW] using this
    · rw [← hWn] at hi
      have := hWi (k * Wn + i) (by rw [lW]; exact hkW k hk i hi)
      simp only [hwinW, List.getElem_map, List.getElem_range, (hdm k hk i hi).1,
        (hdm k hk i hi).2] at this
      rw [← loadHolds_mul_gen_pow, ofK_addr_mul_gen_pow] at this
      exact this

set_option maxHeartbeats 800000 in
/-- **A words bound of `level_queries`' trees is at least `lqN`**, frames below `2^32`, from an
instance's words. -/
theorem lq_bound {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {name : String}
    {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (hE : LqAtE fs cert κ name q base folds leaf d cd mu nhs hbits fin)
    (hfs : ∀ f, fs f < 2 ^ 32) (hS : LqSmall q base folds leaf d cd mu nhs hbits fin)
    {rounds : List FoldRound} {hsv : List E} {qs : ℕ → ℕ} {rows : ℕ → List K}
    {sibs : ℕ → List Digest} {capW flW : List E} {r0 r1 : E}
    (hrl : rounds.length = (lqOqS q base folds leaf d cd mu nhs hbits fin).folds)
    (hhs : (lqOqS q base folds leaf d cd mu nhs hbits fin).final = 1 →
      hsv.length = (lqOqS q base folds leaf d cd mu nhs hbits fin).nHs)
    (hst : OqStatic (lqOqS q base folds leaf d cd mu nhs hbits fin) rounds hsv qs rows sibs q)
    (hcaps : LqCaps (lqOqS q base folds leaf d cd mu nhs hbits fin) q capW flW r0 r1 qs rows sibs)
    {B : ℕ} (hT : TotalLe coreProgram fs name (fun _ ↦ B)) :
    lqN fs name q base folds leaf d cd mu nhs hbits fin ≤ B := by
  obtain ⟨hq, -, hfo, hnh, hwn, -⟩ := id hS
  obtain ⟨Lin0, e2, e3, e4, top, eb, hLW, hLD, htop, hreg, hmem⟩ :=
    lq_fresh (qs := qs) κ hrl hhs hq hfo hnh hwn
  obtain ⟨Lown, rets, Lout, hout, hW, hD, hR⟩ := hE Lin0 0 0 0 e2 e3 e4 rounds hsv eb qs rows
    sibs capW flW r0 r1 hrl hhs hst hcaps hreg hmem top
  have hlt := lqN_lt (fs := fs) (name := name) hfs hS
  obtain ⟨rd, hlow, hmm⟩ := fresh_pair κ hD hW hLD hLW (by omega)
  exact relAtIn_le (hR rd hlow hmm) hT

/-- **`LqAtE` gives `LqAtO` within every words bound of its trees**, frames below `2^32`. -/
theorem lqAtO_of_E {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {name : String}
    {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (hE : LqAtE fs cert κ name q base folds leaf d cd mu nhs hbits fin)
    (hfs : ∀ f, fs f < 2 ^ 32) (hS : LqSmall q base folds leaf d cd mu nhs hbits fin) {B : ℕ}
    (hT : TotalLe coreProgram fs name (fun _ ↦ B)) :
    Arm.LqAtO fs cert κ name q base folds leaf d cd mu nhs hbits fin (some B) := by
  intro Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs hst
    hcaps hreg hmem
  exact ((hE Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs
    hst hcaps hreg hmem).toB (lq_bound hE hfs hS hrl hhs hst hcaps hT)).toO

end
end LeanVM.Guest.B1
