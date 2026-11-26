/-
  LeanVM.Guest.B1.Digest.ChildListCRec

  A child claim record, completely: on an evaluated valuation, its atoms hold at honest slots; a
  block of records with the state's loads and stores around them holds.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk
public import LeanVM.Guest.B1.Digest.ClaimListCLast

/-!
# A claim record, completely

On a valuation evaluated (`Fwd.Good`), a record evaluated by `recW` on its own atoms holds once
its slot is `g^e` (the oracle `slotW`), its mark, cells and the coverage region's slot are the
honest ones (`RecMem`), and the words the range check reads are defined (`g^i`, `i` below the log
`L` of the bound `last · g`): `wit_val`, `markC_val`, `cellLd_val` give the values,
`sideW_holds` the side atoms. A read through a pointer no mark's is no store (`notS_of_ptr`, from
`edgeOk`'s `storesOk`). `blockW_holds`: a block's atoms are before its records, a record's, or
after them (`mem_parts`), so all hold given the records' side atoms, the state's loads and the
next state's stores.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader} {A S W F : List Atom} {w : ℕ → E} {σ : Val} {P : ClaimVs} {o0 K : ℕ}

/-- The claim of a slot value's number (`ccOV o0 j ↦ j`). -/
def slotOf (o0 i : ℕ) : ℕ := if i = o0 then 0 else (i - o0 - 12) / 14 + 1

theorem slotOf_ccOV (o0 j : ℕ) : slotOf o0 (ccOV o0 j) = j := by
  unfold slotOf ccOV
  split_ifs <;> omega

/-- The oracle of the slots `os`: `g^(os j)` at claim `j`'s slot value. -/
noncomputable def slotW (o0 : ℕ) (os : ℕ → ℕ) (i : ℕ) : E := gen ^ os (slotOf o0 i)

theorem w_slot (o0 : ℕ) (os : ℕ → ℕ) (j : ℕ) : slotW o0 os (ccOV o0 j) = gen ^ os j := by
  rw [slotW, slotOf_ccOV]

/-- **The honest records**: claim `j < K`'s slot `os j` below the bound's log, its mark
`marks · g^j` at the coverage region's slot `region · g^(os j)`, its four cells at the table. -/
def RecMem (rd : Reader) (region limit entries marks : E) (K : ℕ) (os : ℕ → ℕ)
    (cells : List E) : Prop :=
  ∀ j < K, BelowLog limit (os j) ∧ LoadHolds rd (region * gen ^ os j) 0 (marks * gen ^ j) ∧
    ∀ c < 4, LoadHolds rd entries (4 * os j + c) (cells.getD (4 * j + c) 0)

/-- The words a range check against `g^L` reads are defined. -/
def BoundMem (rd : Reader) (L : ℕ) : Prop := ∀ i < L, ∃ t, LoadHolds rd (gen ^ i) 0 t

/-! ## A record's values -/

theorem isWitO_eq {o : V} {a : Atom} (h : isWitO o a = true) :
    ∃ s, a = .hint (.witness s (.stack [o])) := by
  unfold isWitO at h
  split at h
  · rename_i s v
    simp only [decide_eq_true_eq] at h
    exact ⟨s, by rw [h]⟩
  · exact absurd h (by simp)

theorem wit_val {o : V} (h : W.any (isWitO o) = true) (hg : ∀ a ∈ W, Good rd S w σ a) :
    σ o = w o.idx := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  obtain ⟨s, rfl⟩ := isWitO_eq hp
  exact hg _ ha o (by simp)

theorem markC_val {j : ℕ} (hj : j ≠ 0) (h : markC F P o0 j = true)
    (hF : ∀ a ∈ F, a.Holds rd σ) :
    σ (ccMark o0 P.marks j) = σ (ccMark o0 P.marks (j - 1)) * gen := by
  unfold markC at h
  rw [ite_neg' hj] at h
  split at h
  · rename_i m c hmc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hc⟩ := h
    rw [mulOf_sound hmc hF, const_sound hc hF, word_gen]
  · exact absurd h (by simp)

theorem cells_ptr {p o : V} {e : ℕ}
    (hperm : (monoOf F 40 p).isPerm (P.entries :: List.replicate 4 o) = true)
    (hF : ∀ a ∈ F, a.Holds rd σ) (ho : σ o = gen ^ e) :
    σ p = σ P.entries * gen ^ (4 * e) := by
  rw [monoPerm_sound hperm hF]
  simp only [List.map_cons, List.map_replicate, List.prod_cons, List.prod_replicate]
  rw [ho, ← pow_mul, mul_comm e 4]

/-- A store goes through a mark's pointer or the state's from offset `13`. -/
theorem notS_of_ptr {stp : ℕ} (hS : ∀ a ∈ S, storesOk o0 stp a = true) {d p : V} {off : ℕ}
    (hp : markPtrB o0 p.idx = false) (hoff : off < 13) : Atom.load d p off ∉ S := by
  intro hm
  have := hS _ hm
  simp only [storesOk, hp, Bool.or_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  omega

theorem cellLd_val {stp j c e : ℕ} {v : E} (hS : ∀ a ∈ S, storesOk o0 stp a = true)
    (h : W.any (isCellLd F P o0 j c) = true) (hF : ∀ a ∈ F, a.Holds rd σ)
    (hg : ∀ a ∈ W, Good rd S w σ a) (hc : c < 4)
    (ho : σ (.n (ccOV o0 j)) = gen ^ e) (hv : LoadHolds rd (σ P.entries) (4 * e + c) v) :
    σ (.n (ccCell o0 j c)) = v := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a <;> simp only [isCellLd, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Bool.not_eq_true'] at hp
  rename_i d p off
  obtain ⟨⟨⟨hd, hoff⟩, hmp⟩, hperm⟩ := hp
  have hnS : Atom.load d p off ∉ S := notS_of_ptr hS hmp (by omega)
  subst hd hoff
  rcases hg _ ha with h' | h'
  · exact absurd h' hnS
  · rw [h', cells_ptr hperm hF ho, rdAt_of_load ((loadHolds_mul_gen_pow rd _ _ _ _).mpr hv)]

/-- **A record's side atom holds**: the range check of its slot, its mark's store, a cell's
read. -/
theorem sideW_holds {stp j : ℕ} {os : ℕ → ℕ} {cells : List E} {L : ℕ}
    (hS : ∀ a ∈ S, storesOk o0 stp a = true) (hF : ∀ a ∈ F, a.Holds rd σ)
    (hwit : σ (.n (ccOV o0 j)) = gen ^ os j)
    (hmark : σ (ccMark o0 P.marks j) = σ P.marks * gen ^ j)
    (hrec : RecMem rd (σ P.region) (gen ^ L) (σ P.entries) (σ P.marks) K os cells) (hj : j < K)
    (hlast : σ P.last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L)
    {a : Atom} (hg : Good rd S w σ a) (hs : sideW F P o0 j a = true) : a.Holds rd σ := by
  cases a with
  | rangeCheck x y t1 t2 k =>
    simp only [sideW, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨hky, rfl⟩, rfl⟩ := hs
    obtain ⟨he32, e', he', hlim⟩ := (hrec j hj).1
    have hLe : L = os j + e' + 1 := gen_pow_inj' (by omega) (by omega) hlim
    simp only [Good] at hg
    rw [ite_pos' hky] at hg
    obtain ⟨h1, h2, h3⟩ := hg
    have hgen : gen ^ os j ≠ 0 := pow_ne_zero _ gen_ne_zero
    have hkv : σ P.last = gen ^ os j * gen ^ e' := by
      apply mul_right_cancel₀ gen_ne_zero
      rw [hlast, hLe, pow_succ, ← pow_add]
    have hyv : σ y = gen ^ e' := by
      rw [h3, hkv, hwit, mul_comm (gen ^ os j), mul_assoc, mul_inv_cancel₀ hgen, mul_one]
    obtain ⟨t1', ht1⟩ := hdef (os j) (by omega)
    obtain ⟨t2', ht2⟩ := hdef e' (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, hwit, rdAt_of_load ht1]; exact ht1
    · rw [hkv, hwit, hyv]
    · rw [h2, hyv, rdAt_of_load ht2]; exact ht2
  | load d p off =>
    simp only [sideW, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    rcases hs with ⟨⟨rfl, rfl⟩, hperm⟩ | ⟨hoff, hc⟩
    · show LoadHolds rd (σ p) 0 (σ (ccMark o0 P.marks j))
      rw [monoPerm_sound hperm hF, hmark]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [hwit]
      exact (hrec j hj).2.1
    · simp only [isCellLd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨-, -⟩, hmp⟩, hperm⟩ := hc
      have hnS : Atom.load d p off ∉ S := notS_of_ptr hS hmp (by omega)
      have hv := (loadHolds_mul_gen_pow rd _ _ _ _).mpr ((hrec j hj).2.2 off hoff)
      rw [← cells_ptr hperm hF hwit] at hv
      exact load_holds_of hnS hg hv
  | _ => simp [sideW] at hs

/-! ## The records' layout -/

theorem ccPos_zero (p0 : ℕ) : ccPos p0 0 = p0 := by simp [ccPos]

theorem ccPos_succ (p0 j : ℕ) : ccPos p0 (j + 1) = p0 + 11 + 13 * j := by simp [ccPos]

theorem ccPos_mono (p0 : ℕ) {a b : ℕ} (h : a ≤ b) : ccPos p0 a ≤ ccPos p0 b := by
  rcases a with _ | a
  · rw [ccPos_zero]
    rcases b with _ | b
    · rw [ccPos_zero]
    · rw [ccPos_succ]; omega
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [ccPos_succ, ccPos_succ]; omega

theorem ccPos_find {p0 i : ℕ} (h : p0 ≤ i) : ∃ j, ccPos p0 j ≤ i ∧ i < ccPos p0 (j + 1) := by
  by_cases hi : i < p0 + 11
  · exact ⟨0, by rw [ccPos_zero]; exact h, by rw [ccPos_succ]; omega⟩
  · obtain ⟨q, hq1, hq2⟩ : ∃ q, 13 * q ≤ i - p0 - 11 ∧ i - p0 - 11 < 13 * q + 13 :=
      ⟨(i - p0 - 11) / 13, by omega, by omega⟩
    exact ⟨q + 1, by rw [ccPos_succ]; omega, by rw [ccPos_succ]; omega⟩

theorem mem_ccOwn {A : List Atom} {p0 j : ℕ} {a : Atom} (h : a ∈ ccOwn A p0 j) : a ∈ A :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- **A block's atoms**: before its records, a record's own, or after them. -/
theorem mem_parts {A : List Atom} {p0 K : ℕ} {a : Atom} (ha : a ∈ A) :
    a ∈ A.take p0 ∨ (∃ j < K, a ∈ ccOwn A p0 j) ∨ a ∈ A.drop (ccPos p0 K) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  rcases Nat.lt_or_ge i p0 with h1 | h1
  · exact Or.inl (List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩)
  rcases Nat.lt_or_ge i (ccPos p0 K) with h2 | h2
  · obtain ⟨j, hj1, hj2⟩ := ccPos_find h1
    have hjK : j < K := by
      by_contra hc
      have := ccPos_mono p0 (show K ≤ j by omega)
      omega
    refine Or.inr (Or.inl ⟨j, hjK, List.mem_iff_getElem.mpr ⟨i - ccPos p0 j, ?_, ?_⟩⟩)
    · simp only [ccOwn, List.length_take, List.length_drop]; omega
    · simp only [ccOwn, List.getElem_take, List.getElem_drop]
      congr 1; omega
  · exact Or.inr (Or.inr (List.mem_iff_getElem.mpr ⟨i - ccPos p0 K, by simp; omega,
      by simp only [List.getElem_drop]; congr 1; omega⟩))

/-- **The records from windows** of `w` records covering the `K`. -/
theorem recs_of_wins {A : List Atom} {P : ClaimVs} {o0 p0 K w W : ℕ} (hn : K ≤ w * W)
    (h : ∀ i < W, recsWin A P o0 p0 K (w * i) w = true) :
    ∀ j < K, recW (ccOwn A p0 j) P o0 j = true := by
  intro k hk
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hi : k / w < W := by
    rw [Nat.div_lt_iff_lt_mul hw]; rw [Nat.mul_comm] at hn; omega
  have := h (k / w) hi
  simp only [recsWin, List.all_eq_true, List.mem_range', Bool.or_eq_true,
    decide_eq_true_eq] at this
  rcases this k ⟨k % w, Nat.mod_lt _ hw, by rw [Nat.one_mul]; exact (Nat.div_add_mod k w).symm⟩
    with h' | h'
  · omega
  · exact h'

theorem recW_parts {W : List Atom} {P : ClaimVs} {o0 j : ℕ} (h : recW W P o0 j = true) :
    W.any (isWitO (.n (ccOV o0 j))) = true ∧ markC (W.filter pureB) P o0 j = true ∧
      (∀ c < 4, W.any (isCellLd (W.filter pureB) P o0 j c) = true) ∧
      ∀ a ∈ W, needsSide a = true → sideW (W.filter pureB) P o0 j a = true := by
  simp only [recW, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun a ha hn => (h4 a ha).resolve_left (by simp [hn])⟩

/-- **The records of a block, evaluated, hold**: their slots the oracle's, their marks
`marks · g^j`, their cells the honest ones, their side atoms. -/
theorem recsW_holds {p0 stp L : ℕ} {os : ℕ → ℕ} {cells : List E}
    (hrecs : ∀ j < K, recW (ccOwn A p0 j) P o0 j = true)
    (hg : ∀ a ∈ A, Good rd S (slotW o0 os) σ a) (hS : ∀ a ∈ S, storesOk o0 stp a = true)
    (hrec : RecMem rd (σ P.region) (gen ^ L) (σ P.entries) (σ P.marks) K os cells)
    (hlast : σ P.last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L) :
    (∀ j < K, σ (.n (ccOV o0 j)) = gen ^ os j) ∧
      (∀ j < K, σ (ccMark o0 P.marks j) = σ P.marks * gen ^ j) ∧
      (∀ j < K, ∀ c < 4, σ (.n (ccCell o0 j c)) = cells.getD (4 * j + c) 0) ∧
      ∀ j < K, ∀ a ∈ ccOwn A p0 j, needsSide a = true → a.Holds rd σ := by
  have hgW : ∀ j, ∀ a ∈ ccOwn A p0 j, Good rd S (slotW o0 os) σ a :=
    fun j a ha => hg a (mem_ccOwn ha)
  have hFW : ∀ j, ∀ a ∈ (ccOwn A p0 j).filter pureB, a.Holds rd σ :=
    fun j => pure_holds (hgW j)
  have hwit : ∀ j < K, σ (.n (ccOV o0 j)) = gen ^ os j := fun j hj =>
    (wit_val (recW_parts (hrecs j hj)).1 (hgW j)).trans (w_slot o0 os j)
  have hmark : ∀ j < K, σ (ccMark o0 P.marks j) = σ P.marks * gen ^ j := by
    intro j
    induction j with
    | zero => intro _; simp [ccMark]
    | succ j ih =>
      intro hj
      rw [markC_val (by omega) (recW_parts (hrecs (j + 1) hj)).2.1 (hFW (j + 1)),
        Nat.add_sub_cancel, ih (by omega), pow_succ, mul_assoc]
  refine ⟨hwit, hmark, fun j hj c hc => ?_, fun j hj a ha hn => ?_⟩
  · exact cellLd_val hS ((recW_parts (hrecs j hj)).2.2.1 c hc) (hFW j) (hgW j) hc (hwit j hj)
      ((hrec j hj).2.2 c hc)
  · exact sideW_holds hS (hFW j) (hwit j hj) (hmark j hj) hrec hj hlast hL33 hdef (hgW j a ha)
      ((recW_parts (hrecs j hj)).2.2.2 a ha hn)

theorem storesOf_load : ∀ {c : ℕ} {ss : List Stmt} {a : Atom}, a ∈ storesOf c ss →
    ∃ d p o, a = .load d p o
  | _, [], _, h => by simp [storesOf] at h
  | c, s :: ss, a, h => by
    simp only [storesOf, List.mem_append] at h
    rcases h with h | h
    · unfold storeHd at h
      split at h
      · split at h
        · rename_i d p o _
          exact ⟨d, p, o, List.mem_singleton.mp h⟩
        · simp at h
      · simp at h
    · exact storesOf_load h

/-- **A block of records holds**: the records' side atoms, the state's
loads and the next state's stores (those a store given the rest), by `edgeOk`. -/
theorem blockW_holds {c : ℕ} {ss : List Stmt} {p0 stp : ℕ} {outs : List V}
    (hg : ∀ a ∈ A, Good rd (storesOf c ss) w σ a)
    (hedge : edgeOk A (storesOf c ss) o0 p0 K stp outs = true)
    (hside : ∀ j < K, ∀ a ∈ ccOwn A p0 j, needsSide a = true → a.Holds rd σ)
    (hstl : ∀ a ∈ A, isStLd stp a = true → a ∉ storesOf c ss → a.Holds rd σ)
    (hstN : ∀ a ∈ A, isStSt outs stp a = true → a ∉ storesOf c ss → a.Holds rd σ)
    (hstS : (∀ a ∈ A, a ∉ storesOf c ss → a.Holds rd σ) →
      ∀ a ∈ A, isStSt outs stp a = true → a ∈ storesOf c ss → a.Holds rd σ) :
    ∀ a ∈ A, a.Holds rd σ := by
  simp only [edgeOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true]
    at hedge
  obtain ⟨⟨⟨hSt, hstp⟩, hhd⟩, htl⟩ := hedge
  have hnS : ∀ a ∈ A, isStLd stp a = true → a ∉ storesOf c ss := by
    intro a _ h
    cases a <;> simp only [isStLd, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    obtain ⟨hp, ho⟩ := h
    exact notS_of_ptr hSt (by rw [hp]; exact hstp) ho
  refine atoms_holds_stores hg
    (fun a ha haS hns => Or.inl ?_) (fun h1 a ha haS => ?_)
  · rcases mem_parts (p0 := p0) (K := K) ha with h | ⟨j, hj, h⟩ | h
    · rw [hhd a h] at hns; exact absurd hns (by simp)
    · exact hside j hj a h hns
    · rcases htl a h with (h' | h') | h'
      · rw [h'] at hns; exact absurd hns (by simp)
      · exact hstl a ha h' haS
      · exact hstN a ha h' haS
  · obtain ⟨d, p, o, rfl⟩ := storesOf_load haS
    rcases mem_parts (p0 := p0) (K := K) ha with h | ⟨j, hj, h⟩ | h
    · exact absurd (hhd _ h) (by simp [needsSide])
    · exact hside j hj _ h rfl
    · rcases htl _ h with (h' | h') | h'
      · exact absurd h' (by simp [needsSide])
      · exact absurd haS (hnS _ ha h')
      · exact hstS h1 _ ha h' haS

end
end LeanVM.Guest.B1.Digest
