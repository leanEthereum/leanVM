/-
  LeanVM.Guest.B1.VsC.TableSizeC

  `table_size__L{h}` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.B1.Link.TableSize
import LeanVM.Guest.CoreRef

/-!
# `table_size`, complete

`table_size(rows, bits, h)` reads at `bits` the hinted bits of `rows + (2^h - 1)`: the complements
of the row count `R`'s bits below `h`, then its bit `h` (`tsBitsW R h`). `tsBits_exact`: for
`R ≤ 2^h` these are what the executor writes (the hint's words of `eOfNat R + eOfNat (2^h - 1)`).

`table_size_complete`: for every `h ≤ 24` and `R ≤ 2^h`, on every memory holding `tsBitsW R h` at
`bits`, the call on `[eOfNat R, bits]` returns `[g^R, tsLeadW R h, tsRestW R h]` by a tree that
pops nothing, exact. Its valuation is the body's forward evaluation (`fwdVal`); per specialization
the kernel checks the template's shape (`tsChecks`: every value defined in order, the stores the
bits squared back, every load through `bits` below `h + 1`, the only other side conditions the two
checks). `tsLeadRest_iff`: the least-height terms pass exactly when `h = 0` or `2^(h-1) < R`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (wordNat bitWord)

@[expose] public section

/-! ## Words and bits -/

theorem wordNat_eOfNat {n : ℕ} (hn : n < 2 ^ 64) : wordNat (eOfNat n) = n := by
  have h0 : (0 : K).toBitVec.toNat = 0 := by
    rw [← K.ofBits_zero, K.toNat_ofBits (by norm_num)]
  simp only [wordNat, eOfNat, limb_ofK, Fin.isValue, Fin.val_zero, ↓reduceIte, Fin.val_one,
    one_ne_zero]
  show (K.ofBits n).toBitVec.toNat + 2 ^ 64 * (0 : K).toBitVec.toNat = n
  rw [K.toNat_ofBits hn, h0]
  simp

theorem bitWord_testBit (n k : ℕ) : bitWord (n.testBit k) = Link.bitE n k := by
  rw [bitE_eq, Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  unfold bitWord
  by_cases hb : (n >>> k) % 2 = 1 <;> simp [hb]

theorem bitWord_not (b : Bool) : bitWord (!b) = 1 + bitWord b := by
  cases b <;> simp [bitWord, add_self_E]

theorem bitE_mul_self (n k : ℕ) : Link.bitE n k * Link.bitE n k = Link.bitE n k := by
  rw [bitE_eq]; split <;> simp

theorem cbitE_mul_self (n k : ℕ) : cbitE n k * cbitE n k = cbitE n k :=
  one_add_bit (bitE_mul_self n k)

/-- A run of memory words, read by a heap destination. -/
theorem heap_words {rd : Reader} {σ : Val} {p : V} {ws : List E} (h : ReadsAt rd (σ p) ws) :
    (Dest.heap p 0 ws.length).words rd σ = ws := by
  refine List.ext_getElem (by simp [Dest.words]) fun i h1 h2 => ?_
  simp only [Dest.words, List.getElem_map, List.getElem_range, Nat.zero_add]
  rw [(h i h2).2]
  rfl

theorem bitE_inj {m n k : ℕ} (h : Link.bitE m k = Link.bitE n k) : m.testBit k = n.testBit k := by
  rw [← bitWord_testBit, ← bitWord_testBit] at h
  cases hm : m.testBit k <;> cases hn : n.testBit k <;> simp_all [bitWord]

/-- Two numbers below `2^(h+1)` with the same bits up to `h` are equal. -/
theorem eq_of_bitE {m n h : ℕ} (hm : m < 2 ^ (h + 1)) (hn : n < 2 ^ (h + 1))
    (hb : ∀ k ≤ h, Link.bitE m k = Link.bitE n k) : m = n := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i ≤ h
  · exact bitE_inj (hb i hi)
  · have h2 : 2 ^ (h + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

/-! ## The honest bits -/

/-- The words `table_size` reads at `bits`: the complement bits of `R` below `h`, then bit `h`. -/
def tsBitsW (R h : ℕ) : List E := cbitsE R h ++ [Link.bitE R h]

/-- Word `k ≤ h` of `tsBitsW R h`. -/
def tsW (R h k : ℕ) : E := if k < h then cbitE R k else Link.bitE R h

theorem tsBitsW_length (R h : ℕ) : (tsBitsW R h).length = h + 1 := by simp [tsBitsW, cbitsE_length]

theorem tsBitsW_getElem {R h k : ℕ} (hk : k < (tsBitsW R h).length) : (tsBitsW R h)[k] = tsW R h k := by
  have hk' := hk
  rw [tsBitsW_length] at hk'
  simp only [tsBitsW, List.getElem_append, cbitsE_length, tsW]
  by_cases h1 : k < h
  · simp [h1, cbitsE]
  · simp [h1, show k - h = 0 by omega]

theorem tsW_mul_self (R h k : ℕ) : tsW R h k * tsW R h k = tsW R h k := by
  unfold tsW; split
  · exact cbitE_mul_self R k
  · exact bitE_mul_self R h

theorem readsAt_tsW {rd : Reader} {bits : E} {R h : ℕ} (hm : ReadsAt rd bits (tsBitsW R h)) {k : ℕ}
    (hk : k ≤ h) : LoadHolds rd bits k (tsW R h k) := by
  have hk' : k < (tsBitsW R h).length := by rw [tsBitsW_length]; omega
  have := hm k hk'
  rwa [tsBitsW_getElem] at this

/-- **The hint's words are the honest bits**: those of `R + (2^h - 1)`, `R ≤ 2^h`. -/
theorem tsBits_exact {R h : ℕ} (hR : R ≤ 2 ^ h) (hh : h ≤ 24) :
    tsBitsW R h = (List.range (h + 1)).map fun j =>
      bitWord ((wordNat (eOfNat R + eOfNat (2 ^ h - 1))).testBit (0 + j)) := by
  have h25 : 2 ^ h ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hh
  rw [← LeanVM.Guest.Value.eOfNat_xor,
    wordNat_eOfNat (Nat.xor_lt_two_pow (n := 64) (by omega) (by omega))]
  refine List.ext_getElem (by simp [tsBitsW_length]) fun j h1 h2 => ?_
  rw [tsBitsW_getElem h1]
  simp only [List.getElem_map, List.getElem_range, Nat.zero_add, Nat.testBit_xor,
    Nat.testBit_two_pow_sub_one]
  simp only [List.length_map, List.length_range] at h2
  unfold tsW
  split
  · next hj => simp only [hj, decide_true, Bool.xor_true]; rw [bitWord_not, bitWord_testBit]; rfl
  · next hj =>
    simp only [hj, decide_false, Bool.xor_false]
    rw [bitWord_testBit, show j = h by omega]

/-! ## The template's shape, checked per specialization -/

/-- The stores of `table_size__L{h}`, `h ≥ 1`: each bit squared back in place. -/
def tsStores (h : ℕ) : List Atom :=
  .load (.n 5) (.n 1) 0 :: (List.range h).map fun k => .load (.n (4 + 9 * (k + 1))) (.n 1) (k + 1)

/-- A load is through `bits`, at an offset at most `h`. -/
def tsLoadOk (h : ℕ) : Atom → Bool
  | .load _ p k => p == .n 1 && decide (k ≤ h)
  | _ => true

/-- An atom needing a side condition is a load or one of the checks `A1`, `A2`. -/
def tsSideOk (A1 A2 : Atom) : Atom → Bool
  | .load .. => true
  | a => !needsSide a || a == A1 || a == A2

/-- The two checks of `table_size__L{h}`, `h ≥ 2`. -/
def tsA1 (h : ℕ) : Atom := .assertEq (.n (13 * h + 16)) (.n 3)
def tsA2 (h : ℕ) : Atom := .assertEq (.n (13 * h + 19)) (.n (13 * h + 20))

/-- A hint is the head's bits of `rows + (2^h - 1)`. -/
def tsHintOk (h : ℕ) : Atom → Bool
  | .hint hh => hh == .bits (.n 3) 0 (h + 1) (.heap (.n 1) 0 (h + 1))
  | _ => true

/-- What the kernel checks of a `table_size` body `B` at height `h`, its two checks `A1`, `A2`: every
value defined in order, the stores the bits squared back, every load through `bits` at an offset at
most `h`, the other side conditions the checks, no witness hint, the head without the checks, the
one hint the head's. -/
def tsChecksB (h : ℕ) (B : List Stmt) (A1 A2 : Atom) : Bool :=
  (chk 2 B).isSome && storesOf 2 B == tsStores h && (atomsOf B).all (tsLoadOk h) &&
    (atomsOf B).all (tsSideOk A1 A2) && (atomsOf B).all atomQuiet &&
    (atomsOf (tsHead h)).all (fun a => !(a == A1) && !(a == A2)) && (atomsOf B).all (tsHintOk h)

/-- What the kernel checks of `tsBody h`. -/
def tsChecks (h : ℕ) : Bool := tsChecksB h (tsBody h) (tsA1 h) (tsA2 h)

theorem mem_atomsOf {a : Atom} : ∀ {ss : List Stmt}, Stmt.atom a ∈ ss → a ∈ atomsOf ss
  | [], h => by simp at h
  | s :: ss, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · simp [atomsOf]
    · have ih := mem_atomsOf h'
      cases s with
      | atom b => exact List.mem_cons_of_mem _ ih
      | _ => exact ih

theorem sideOk_cases {A1 A2 a : Atom} (h : tsSideOk A1 A2 a = true) (hn : needsSide a = true) :
    (∃ d p k, a = .load d p k) ∨ a = A1 ∨ a = A2 := by
  cases a with
  | load d p k => exact Or.inl ⟨d, p, k, rfl⟩
  | _ =>
    simp only [tsSideOk, hn, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h
    exact Or.inr h

/-! ## The least-height terms -/

/-- `table_size`'s `lead`: `top + 1 + c_{h-1}`. -/
def tsLeadW (R h : ℕ) : E := if h = 0 then 1 else Link.bitE R h + 1 + cbitE R (h - 1)

/-- `table_size`'s `rest`: `top + below + (2^(h-1) - 1)`. -/
def tsRestW (R h : ℕ) : E :=
  if h = 0 then 1 else Link.bitE R h + polyE ((List.range (h - 1)).map (cbitE R)) + eOfNat (2 ^ (h - 1) - 1)

/-- The row count the loaded bits stand for is `R`. -/
theorem tsR_eq {σ : Val} {R h : ℕ} (hh : h ≤ 24) (hR : R ≤ 2 ^ h)
    (hcv : ∀ k < h, tsCv σ k = cbitE R k) (htop : σ (.n (3 + 9 * h)) = Link.bitE R h) : tsR σ h = R := by
  have hb : ∀ k < h, tsCv σ k * tsCv σ k = tsCv σ k := fun k hk => by rw [hcv k hk]; exact cbitE_mul_self R k
  have ht : σ (.n (3 + 9 * h)) * σ (.n (3 + 9 * h)) = σ (.n (3 + 9 * h)) := by rw [htop]; exact bitE_mul_self R h
  obtain ⟨-, hcb, htb, hR', hlt⟩ := tsR_facts hh hb ht
  have hbv : bv (σ (.n (3 + 9 * h))) ≤ 1 := bv_le _
  have hlt2 : tsR σ h < 2 ^ (h + 1) := by rw [hR', pow_succ]; nlinarith
  refine eq_of_bitE hlt2 (by rw [pow_succ]; omega) fun k hk => ?_
  rcases Nat.lt_or_ge k h with hk' | hk'
  · have e := congrArg (fun l => l.getD k 0) hcb
    simp only [cbitsE, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk',
      Option.map_some, Option.getD_some] at e
    rw [hcv k hk'] at e
    unfold cbitE at e
    exact add_left_cancel e
  · rw [show k = h by omega, htb, htop]

/-- A valuation whose loaded bits are `R`'s. -/
def tsSyn (R h : ℕ) : Val := fun v =>
  if v.idx = 3 + 9 * h then Link.bitE R h else if v.idx = 4 then cbitE R 0 else cbitE R ((v.idx - 3) / 9)

theorem tsSyn_cv {R h k : ℕ} (hk : k < h) : tsCv (tsSyn R h) k = cbitE R k := by
  unfold tsCv tsSyn
  split
  · next hk0 => subst hk0; simp; omega
  · next hk0 =>
    simp only [show ¬ 3 + 9 * k = 3 + 9 * h by omega, show ¬ 3 + 9 * k = 4 by omega, ↓reduceIte]
    congr 1; omega

/-- **The least-height terms pass exactly when `h = 0` or `2^(h-1) < R`**, for `R ≤ 2^h`. -/
theorem tsLeadRest_iff {R h : ℕ} (hh : h ≤ 24) (hR : R ≤ 2 ^ h) :
    (tsLeadW R h = 1 ∧ tsRestW R h ≠ 0) ↔ (h = 0 ∨ 2 ^ (h - 1) < R) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh1
  · simp [tsLeadW, tsRestW]
  have hcv : ∀ k < h, tsCv (tsSyn R h) k = cbitE R k := fun k hk => tsSyn_cv hk
  have htop : tsSyn R h (.n (3 + 9 * h)) = Link.bitE R h := by simp [tsSyn]
  have hb : ∀ k < h, tsCv (tsSyn R h) k * tsCv (tsSyn R h) k = tsCv (tsSyn R h) k :=
    fun k hk => by rw [hcv k hk]; exact cbitE_mul_self R k
  have ht : tsSyn R h (.n (3 + 9 * h)) * tsSyn R h (.n (3 + 9 * h)) = tsSyn R h (.n (3 + 9 * h)) := by
    rw [htop]; exact bitE_mul_self R h
  have hReq := tsR_eq hh hR hcv htop
  have hall : tsSyn R h (.n (3 + 9 * h)) = 1 → natOfBits ((List.range h).map (tsD (tsSyn R h))) = 0 := by
    intro h1
    obtain ⟨-, -, -, hR', hlt⟩ := tsR_facts hh hb ht
    rw [hReq, h1, show bv (1 : E) = 1 by simp [bv]] at hR'
    omega
  have hlr := ts_lead_rest hh1 hh hb ht hall
  rw [hReq, htop, hcv (h - 1) (by omega)] at hlr
  have hm : (List.range (h - 1)).map (tsCv (tsSyn R h)) = (List.range (h - 1)).map (cbitE R) :=
    List.map_congr_left fun k hk => hcv k (by have := List.mem_range.mp hk; omega)
  rw [hm] at hlr
  simp only [tsLeadW, tsRestW, show h ≠ 0 by omega, ↓reduceIte, false_or]
  exact hlr

/-! ## Completeness, `2 ≤ h ≤ 24` -/

section Main

theorem n_idx (i : ℕ) : (V.n i).idx = i := rfl

theorem load_inj_idx {i j o o' : ℕ} {p p' : V} (he : Atom.load (.n i) p o = Atom.load (.n j) p' o') :
    i = j ∧ o = o' := ⟨congrArg V.idx (Atom.load.inj he).1, (Atom.load.inj he).2.2⟩

end Main

/-- The index of bit `k`'s load in the factor blocks. -/
def tsLd (k : ℕ) : ℕ := if k = 0 then 4 else 3 + 9 * k

/-- The index of bit `k`'s square, stored back. -/
def tsSt (k : ℕ) : ℕ := if k = 0 then 5 else 4 + 9 * k

/-- The second check: `top · (low + (2^h - 1)) = 0` on the honest bits. -/
theorem ts_top_low {R h : ℕ} (hR : R ≤ 2 ^ h) (hh : h ≤ 63) :
    Link.bitE R h * (polyE ((List.range h).map (cbitE R)) + eOfNat (2 ^ h - 1)) = 0 := by
  rcases Nat.lt_or_ge R (2 ^ h) with hRl | hRe'
  · have : Link.bitE R h = 0 := by
      rw [bitE_eq, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hRl]; simp
    rw [this, zero_mul]
  · have hR2 : R = 2 ^ h := by omega
    subst hR2
    have hones : (List.range h).map (cbitE (2 ^ h)) = List.replicate h 1 := by
      refine List.ext_getElem (by simp) fun k h1 h2 => ?_
      simp only [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, cbitE, bitE_eq,
        Nat.shiftRight_eq_div_pow]
      obtain ⟨m, hm⟩ : ∃ m, h - k = m + 1 := ⟨h - k - 1, by omega⟩
      rw [Nat.pow_div (by omega) (by norm_num), hm]
      simp [pow_succ]
    rw [hones, polyE_replicate_one hh, add_self_E, mul_zero]

theorem tsBody_mem_head {h : ℕ} {a : Atom} (ha : Stmt.atom a ∈ tsHead h) : Stmt.atom a ∈ tsBody h :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha))

/-- Bit `k`'s load and square lie in the head. -/
theorem tsHead_mem_blk {h k : ℕ} (hk : k ≤ h) :
    Stmt.atom (.load (.n (tsLd k)) (.n 1) k) ∈ tsHead h ∧
      Stmt.atom (.mul (.n (tsSt k)) (.n (tsLd k)) (.n (tsLd k))) ∈ tsHead h := by
  unfold tsLd tsSt
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [↓reduceIte]
    constructor <;> refine List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ ?_)) <;> simp [tsBlk0]
  · simp only [show k ≠ 0 by omega, ↓reduceIte]
    rcases Nat.lt_or_ge k h with hkh | hkh
    · have hk1 : k - 1 ∈ List.range (h - 1) := List.mem_range.mpr (by omega)
      have hm : ∀ a, Stmt.atom a ∈ tsBlk k → Stmt.atom a ∈ tsHead h := fun a hs => List.mem_append_left _
        (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨k - 1, hk1,
          by rw [Nat.sub_add_cancel hk0]⟩, hs⟩))
      exact ⟨hm _ (by simp [tsBlk]), hm _ (by simp [tsBlk])⟩
    · rw [show k = h by omega]
      exact ⟨List.mem_append_right _ (by simp [tsTop]), List.mem_append_right _ (by simp [tsTop])⟩

theorem tsStores_mem {h : ℕ} {a : Atom} (ha : a ∈ tsStores h) :
    ∃ k ≤ h, a = .load (.n (tsSt k)) (.n 1) k := by
  simp only [tsStores, List.mem_cons, List.mem_map, List.mem_range] at ha
  rcases ha with rfl | ⟨k, hk, rfl⟩
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨k + 1, by omega, by simp [tsSt]⟩

theorem tsStores_not_ld {h k : ℕ} : Atom.load (.n (tsLd k)) (.n 1) k ∉ tsStores h := by
  intro hm
  obtain ⟨j, -, he⟩ := tsStores_mem hm
  obtain ⟨h1, h2⟩ := load_inj_idx he
  subst h2
  unfold tsLd tsSt at h1
  split at h1 <;> omega

/-- A load beyond the factor blocks is no store. -/
theorem tsStores_not_hi {h i k : ℕ} (hi : 6 + 9 * h ≤ i) : Atom.load (.n i) (.n 1) k ∉ tsStores h := by
  intro hst
  obtain ⟨j, hj, he⟩ := tsStores_mem hst
  obtain ⟨e1, e2⟩ := load_inj_idx he
  unfold tsSt at e1; split at e1 <;> omega

/-- **What the head establishes** on the forward valuation `σ` of a `table_size` body `B`. -/
structure TsHead (rd : Reader) (R h : ℕ) (bits : E) (B : List Stmt) (A1 A2 : Atom) (σ : Val) : Prop where
  good : ∀ a, Stmt.atom a ∈ B → Good rd (tsStores h) (fun _ ↦ 0) σ a
  s0 : σ (.n 0) = eOfNat R
  s1 : σ (.n 1) = bits
  load : ∀ d k, Stmt.atom (.load d (.n 1) k) ∈ B → Atom.load d (.n 1) k ∉ tsStores h → σ d = tsW R h k
  holds : ∀ a, Stmt.atom a ∈ B → a ≠ A1 → a ≠ A2 → a.Holds rd σ
  exact : ∀ a, Stmt.atom a ∈ B → a.Exact rd σ
  s3 : σ (.n 3) = eOfNat R + eOfNat (2 ^ h - 1)
  top : σ (.n (3 + 9 * h)) = Link.bitE R h
  grows : σ (.n (9 + 9 * h)) = gen ^ R
  eR : eOfNat R = polyE ((List.range h).map (cbitE R)) + eOfNat (2 ^ h - 1) + Link.bitE R h * gen ^ h

/-- **The head of a `table_size` body**, `1 ≤ h ≤ 24`, on a memory holding the honest bits. -/
theorem ts_head {h : ℕ} (hh : 1 ≤ h) (hh' : h ≤ 24) {B : List Stmt} {A1 A2 : Atom}
    (hB : ∀ a, Stmt.atom a ∈ tsHead h → Stmt.atom a ∈ B) (hck : tsChecksB h B A1 A2 = true)
    {R : ℕ} {bits : E} (hR : R ≤ 2 ^ h) {rd : Reader} (hmem : ReadsAt rd bits (tsBitsW R h)) :
    TsHead rd R h bits B A1 A2 (fwdVal rd (fun _ ↦ 0) [eOfNat R, bits] B) := by
  simp only [tsChecksB, Bool.and_eq_true, beq_iff_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨hc, hS⟩, hLd⟩, hSd⟩, -⟩, hHd⟩, hHt⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  set σ := fwdVal rd (fun _ ↦ 0) [eOfNat R, bits] B with hσ
  have G : ∀ a, Stmt.atom a ∈ B → Good rd (storesOf 2 B) (fun _ ↦ 0) σ a :=
    fwd_good (args := [eOfNat R, bits]) hc
  rw [hS] at G
  have hs0 : σ (.n 0) = eOfNat R := fwd_param (args := [eOfNat R, bits]) hc (by simp)
  have hs1 : σ (.n 1) = bits := fwd_param (args := [eOfNat R, bits]) hc (by simp)
  have hld : ∀ d p k, Stmt.atom (.load d p k) ∈ B → p = .n 1 ∧ k ≤ h := by
    intro d p k hm
    have := List.all_eq_true.mp hLd _ (mem_atomsOf hm)
    simp only [tsLoadOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this
  have hL : ∀ d k, Stmt.atom (.load d (.n 1) k) ∈ B → Atom.load d (.n 1) k ∉ tsStores h →
      σ d = tsW R h k := by
    intro d k hm hns
    have hk := (hld _ _ _ hm).2
    exact good_load_eq (by rw [hs1]; exact readsAt_tsW hmem hk) (G _ hm) hns
  have hcv : ∀ k ≤ h, σ (.n (tsLd k)) = tsW R h k := fun k hk =>
    hL _ _ (hB _ (tsHead_mem_blk hk).1) tsStores_not_ld
  have hsq : ∀ k ≤ h, σ (.n (tsSt k)) = tsW R h k := by
    intro k hk
    have hm := G _ (hB _ (tsHead_mem_blk hk).2)
    rw [good_mul_eq hm (by simp only [tsLd, tsSt]; split <;> omega)
      (by simp only [tsLd, tsSt]; split <;> omega), hcv k hk, tsW_mul_self]
  have hside : ∀ a, Stmt.atom a ∈ B → a ≠ A1 → a ≠ A2 → needsSide a = true →
      a.Holds rd σ ∨ Side rd (tsStores h) σ a := by
    intro a hm h1 h2 hn
    rcases sideOk_cases (List.all_eq_true.mp hSd a (mem_atomsOf hm)) hn with ⟨d, p, k, rfl⟩ | rfl | rfl
    · obtain ⟨rfl, hk⟩ := hld _ _ _ hm
      by_cases hst : Atom.load d (.n 1) k ∈ tsStores h
      · obtain ⟨j, hj, he⟩ := tsStores_mem hst
        have hd : d = .n (tsSt j) := (Atom.load.inj he).1
        have hkj : k = j := (Atom.load.inj he).2.2
        rw [hd, hkj] at hst ⊢
        right
        simp only [Side, hst, ↓reduceIte]
        rw [hsq j hj, hs1]
        exact readsAt_tsW hmem hj
      · left
        show LoadHolds rd (σ (.n 1)) k (σ d)
        rw [hL d k hm hst, hs1]
        exact readsAt_tsW hmem hk
    · exact absurd rfl h1
    · exact absurd rfl h2
  have hholds : ∀ a, Stmt.atom a ∈ B → a ≠ A1 → a ≠ A2 → a.Holds rd σ := by
    intro a hm h1 h2
    have hb := atoms_holds (rd := rd) (S := tsStores h) (w := fun _ ↦ 0) (σ := σ) (atoms := [a])
      (fun b hb => by rw [List.mem_singleton] at hb; subst hb; exact G b hm)
      (fun b hb hn => by rw [List.mem_singleton] at hb; subst hb; exact hside b hm h1 h2 hn)
    exact hb a List.mem_cons_self
  have hheadA : ∀ a, Stmt.atom a ∈ tsHead h → a.Holds rd σ := by
    intro a ha
    have hc := List.all_eq_true.mp hHd a (mem_atomsOf ha)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hc
    exact hholds a (hB a ha) hc.1 hc.2
  obtain ⟨h3, hbits, -, htopb, hg⟩ := tsHead_facts hh hh' hheadA
  have hcvk : ∀ k < h, tsCv σ k = cbitE R k := fun k hk => by
    rw [show tsCv σ k = σ (.n (tsLd k)) from rfl, hcv k (by omega)]
    simp [tsW, hk]
  have htop : σ (.n (3 + 9 * h)) = Link.bitE R h := by
    rw [show 3 + 9 * h = tsLd h by simp [tsLd, show h ≠ 0 by omega], hcv h le_rfl]
    simp [tsW]
  have hReq := tsR_eq hh' hR hcvk htop
  have hcvm : (List.range h).map (tsCv σ) = (List.range h).map (cbitE R) :=
    List.map_congr_left fun k hk => hcvk k (List.mem_range.mp hk)
  obtain ⟨hRe, -, -, -, -⟩ := tsR_facts hh' (fun k hk => (hbits k hk).2) htopb
  rw [hReq, hcvm, htop] at hRe
  have h3' : σ (.n 3) = eOfNat R + eOfNat (2 ^ h - 1) := by rw [h3, hs0]
  refine ⟨G, hs0, hs1, hL, hholds, fun a ha => ?_, h3', htop, by rw [hg, hReq], hRe⟩
  have ht := List.all_eq_true.mp hHt a (mem_atomsOf ha)
  cases a with
  | hint ht' =>
    simp only [tsHintOk, beq_iff_eq] at ht
    subst ht
    show Dest.words rd σ (.heap (.n 1) 0 (h + 1)) = _
    rw [h3', ← tsBits_exact hR hh', ← tsBitsW_length R h]
    exact heap_words (by rw [hs1]; exact hmem)
  | _ => trivial

/-- **`table_size__L{h}`'s template completes**, `2 ≤ h ≤ 24`. -/
theorem ts_complete {kd h : ℕ} (hh : 2 ≤ h) (hh' : h ≤ 24) {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = tsBody h)
    (hck : tsChecks h = true) (R : ℕ) (bits : E) (hR : R ≤ 2 ^ h) :
    CallCompletes0 kd name [eOfNat R, bits] [gen ^ R, tsLeadW R h, tsRestW R h]
      (fun rd ↦ ReadsAt rd bits (tsBitsW R h)) PostQuiet := by
  have hck' := hck
  simp only [tsChecks, tsChecksB, Bool.and_eq_true] at hck'
  have hQ := hck'.1.1.2
  have hbody' : f.body = (tsHead h ++ tsBelow h ++ tsTail h) ++ [.ret [.n (13 * h + 21), .n (13 * h + 22),
      .n (13 * h + 23)]] := hbody
  have hat : AllAtoms (tsHead h ++ tsBelow h ++ tsTail h) :=
    allAtoms_append (allAtoms_append (tsHead_atoms h) (allAtoms_cons (allAtoms_map_flatten fun _ _ ↦
      allAtoms_of_isAtomsB rfl))) (allAtoms_of_isAtomsB rfl)
  have hq : (atomsOf (tsHead h ++ tsBelow h ++ tsTail h)).all atomQuiet = true := by
    refine List.all_eq_true.mpr fun a ha => List.all_eq_true.mp hQ a ?_
    exact mem_atomsOf (List.mem_append_left _ (mem_of_mem_atomsOf ha))
  have h24 : 2 ^ h ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hh'
  refine callCompletes0_straightRd (fun rd ↦ fwdVal rd (fun _ ↦ 0) [eOfNat R, bits] (tsBody h)) hfind hbody'
    hat hq fun rd _ hmem ↦ ?_
  have H := ts_head (B := tsBody h) (by omega) hh' (fun a ha => tsBody_mem_head ha) hck hR hmem
  set σ := fwdVal rd (fun _ ↦ 0) [eOfNat R, bits] (tsBody h) with hσ
  obtain ⟨G, hs0, hs1, hL, hholds, hex, h3, htop, hg, hRe⟩ := H
  have mem : ∀ a, Stmt.atom a ∈ tsTail h → Stmt.atom a ∈ tsBody h :=
    fun a ha => List.mem_append_left _ (List.mem_append_right _ ha)
  -- below, by its Horner walk from the top
  have hbel : ∀ j ≤ h - 2, σ (.n (10 + 9 * h + 4 * j)) =
      polyE ((List.range (j + 1)).map fun m ↦ cbitE R (h - 2 - j + m)) := by
    intro j hj
    induction j with
    | zero =>
      have hm : Stmt.atom (.load (.n (10 + 9 * h)) (.n 1) (h - 2)) ∈ tsBody h :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
      rw [show 10 + 9 * h + 4 * 0 = 10 + 9 * h by ring, hL _ _ hm (tsStores_not_hi (by omega))]
      simp [polyE, tsW, show h - 2 < h by omega]
    | succ j ih =>
      have mB : ∀ a, Stmt.atom a ∈ tsBelowStep h j → Stmt.atom a ∈ tsBody h := fun a ha ↦
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _
          (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, ha⟩))))
      have c1 := G (.const (.n (11 + 9 * h + 4 * j)) (word 2 0)) (mB _ (by simp [tsBelowStep]))
      have m2 := good_mul_eq (G (.mul (.n (12 + 9 * h + 4 * j)) (.n (10 + 9 * h + 4 * j))
        (.n (11 + 9 * h + 4 * j))) (mB _ (by simp [tsBelowStep]))) (by simp only; omega) (by simp only; omega)
      have hm3 := mB (.load (.n (13 + 9 * h + 4 * j)) (.n 1) (h - 3 - j)) (by simp [tsBelowStep])
      have l3 := hL _ _ hm3 (tsStores_not_hi (by omega))
      have a4 := G (.add (.n (14 + 9 * h + 4 * j)) (.n (12 + 9 * h + 4 * j)) (.n (13 + 9 * h + 4 * j)))
        (mB _ (by simp [tsBelowStep]))
      simp only [Good] at c1 a4
      have hm : ((List.range (j + 1)).map ((fun m ↦ cbitE R (h - 2 - (j + 1) + m)) ∘ Nat.succ)) =
          (List.range (j + 1)).map fun m ↦ cbitE R (h - 2 - j + m) :=
        List.map_congr_left fun m _ ↦ by simp only [Function.comp]; congr 1; omega
      have e : polyE ((List.range (j + 1 + 1)).map fun m ↦ cbitE R (h - 2 - (j + 1) + m)) =
          cbitE R (h - 3 - j) + gen * polyE ((List.range (j + 1)).map fun m ↦ cbitE R (h - 2 - j + m)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, polyE, hm,
          show h - 2 - (j + 1) + 0 = h - 3 - j by omega]
      rw [show 10 + 9 * h + 4 * (j + 1) = 14 + 9 * h + 4 * j by ring, a4, m2, c1, word_gen, ih (by omega),
        l3, e]
      simp only [tsW, show h - 3 - j < h by omega, ↓reduceIte]
      ring
  have hbelow := hbel (h - 2) le_rfl
  rw [show 10 + 9 * h + 4 * (h - 2) = 13 * h + 2 by omega, show h - 2 - (h - 2) = 0 by omega,
    show h - 2 + 1 = h - 1 by omega] at hbelow
  simp only [Nat.zero_add] at hbelow
  -- the tail
  have l3 := hL (.n (13 * h + 3)) (h - 1) (mem _ (by simp [tsTail])) (tsStores_not_hi (by omega))
  have l9 := hL (.n (13 * h + 9)) (h - 1) (mem _ (by simp [tsTail])) (tsStores_not_hi (by omega))
  have c4 := G (.const (.n (13 * h + 4)) (word (2 ^ (h - 1)) 0)) (mem _ (by simp [tsTail]))
  have m5 := good_mul_eq (G (.mul (.n (13 * h + 5)) (.n (13 * h + 3)) (.n (13 * h + 4)))
    (mem _ (by simp [tsTail]))) (by simp only; omega) (by simp only; omega)
  have a6 := G (.add (.n (13 * h + 6)) (.n (13 * h + 2)) (.n (13 * h + 5))) (mem _ (by simp [tsTail]))
  have c7 := G (.const (.n (13 * h + 7)) (word 1 0)) (mem _ (by simp [tsTail]))
  have a8 := G (.add (.n (13 * h + 8)) (.n (3 + 9 * h)) (.n (13 * h + 7))) (mem _ (by simp [tsTail]))
  have a10 := G (.add (.n (13 * h + 10)) (.n (13 * h + 8)) (.n (13 * h + 9))) (mem _ (by simp [tsTail]))
  have a11 := G (.add (.n (13 * h + 11)) (.n (3 + 9 * h)) (.n (13 * h + 2))) (mem _ (by simp [tsTail]))
  have c12 := G (.const (.n (13 * h + 12)) (word (2 ^ (h - 1) - 1) 0)) (mem _ (by simp [tsTail]))
  have a13 := G (.add (.n (13 * h + 13)) (.n (13 * h + 11)) (.n (13 * h + 12))) (mem _ (by simp [tsTail]))
  have c14 := G (.const (.n (13 * h + 14)) (word (2 ^ h) 0)) (mem _ (by simp [tsTail]))
  have m15 := good_mul_eq (G (.mul (.n (13 * h + 15)) (.n (3 + 9 * h)) (.n (13 * h + 14)))
    (mem _ (by simp [tsTail]))) (by simp only; omega) (by simp only; omega)
  have a16 := G (.add (.n (13 * h + 16)) (.n (13 * h + 6)) (.n (13 * h + 15))) (mem _ (by simp [tsTail]))
  have c17 := G (.const (.n (13 * h + 17)) (word (2 ^ h - 1) 0)) (mem _ (by simp [tsTail]))
  have a18 := G (.add (.n (13 * h + 18)) (.n (13 * h + 6)) (.n (13 * h + 17))) (mem _ (by simp [tsTail]))
  have m19 := good_mul_eq (G (.mul (.n (13 * h + 19)) (.n (3 + 9 * h)) (.n (13 * h + 18)))
    (mem _ (by simp [tsTail]))) (by simp only; omega) (by simp only; omega)
  have c20 := G (.const (.n (13 * h + 20)) (word 0 0)) (mem _ (by simp [tsTail]))
  have k21 := G (.copy (.n (13 * h + 21)) (.n (9 + 9 * h))) (mem _ (by simp [tsTail]))
  have k22 := G (.copy (.n (13 * h + 22)) (.n (13 * h + 10))) (mem _ (by simp [tsTail]))
  have k23 := G (.copy (.n (13 * h + 23)) (.n (13 * h + 13))) (mem _ (by simp [tsTail]))
  simp only [Good] at c4 a6 c7 a8 a10 a11 c12 a13 c14 a16 c17 a18 c20 k21 k22 k23
  simp only [tsW, show h - 1 < h by omega, ↓reduceIte] at l3 l9
  have hlow : σ (.n (13 * h + 6)) = polyE ((List.range h).map (cbitE R)) := by
    rw [a6, m5, c4, l3, hbelow, word_two_pow (by omega)]
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    rw [polyE_range_succ, Nat.add_sub_cancel]
  refine ⟨?_, ?_, fun a ha => ⟨?_, hex a (List.mem_append_left _ ha)⟩⟩
  · rw [hparams]
    simp only [List.map_cons, List.map_nil, hs0, hs1]
  · simp only [List.map_cons, List.map_nil]
    rw [k21, hg, k22, a10, a8, c7, word_one, l9, k23, a13, a11, c12, hbelow, htop, word_eOfNat]
    simp [tsLeadW, tsRestW, show h ≠ 0 by omega]
  · have hm : Stmt.atom a ∈ tsBody h := List.mem_append_left _ ha
    by_cases h1 : a = tsA1 h
    · subst h1
      show σ (.n (13 * h + 16)) + σ (.n 3) = 0
      rw [a16, m15, c14, word_two_pow (by omega), hlow, h3, htop, hRe]
      linear_combination (polyE ((List.range h).map (cbitE R)) + Link.bitE R h * gen ^ h +
        eOfNat (2 ^ h - 1)) * two_eq_zero_E
    by_cases h2 : a = tsA2 h
    · subst h2
      show σ (.n (13 * h + 19)) + σ (.n (13 * h + 20)) = 0
      rw [m19, c20, word_zero, add_zero, a18, c17, hlow, htop, word_eOfNat]
      exact ts_top_low hR (by omega)
    exact hholds a hm h1 h2

/-- The two checks of `table_size__L1`. -/
def tsChecks1 : Bool := tsChecksB 1 tsBody1 (.assertEq (.n 26) (.n 3)) (.assertEq (.n 29) (.n 30))

/-- **`table_size__L1`'s template completes.** -/
theorem ts1_complete {kd : ℕ} {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = tsBody1)
    (hck : tsChecks1 = true) (R : ℕ) (bits : E) (hR : R ≤ 2 ^ 1) :
    CallCompletes0 kd name [eOfNat R, bits] [gen ^ R, tsLeadW R 1, tsRestW R 1]
      (fun rd ↦ ReadsAt rd bits (tsBitsW R 1)) PostQuiet := by
  have hck' := hck
  simp only [tsChecks1, tsChecksB, Bool.and_eq_true] at hck'
  have hQ := hck'.1.1.2
  have hbody' : f.body = (tsHead 1 ++ tsTail1) ++ [.ret [.n 31, .n 32, .n 33]] := hbody
  have hat : AllAtoms (tsHead 1 ++ tsTail1) := allAtoms_append (tsHead_atoms 1) (allAtoms_of_isAtomsB rfl)
  have hq : (atomsOf (tsHead 1 ++ tsTail1)).all atomQuiet = true := by
    refine List.all_eq_true.mpr fun a ha => List.all_eq_true.mp hQ a ?_
    exact mem_atomsOf (List.mem_append_left _ (mem_of_mem_atomsOf ha))
  refine callCompletes0_straightRd (fun rd ↦ fwdVal rd (fun _ ↦ 0) [eOfNat R, bits] tsBody1) hfind hbody'
    hat hq fun rd _ hmem ↦ ?_
  have H := ts_head (B := tsBody1) le_rfl (by norm_num)
    (fun a ha => List.mem_append_left _ (List.mem_append_left _ ha)) hck hR hmem
  set σ := fwdVal rd (fun _ ↦ 0) [eOfNat R, bits] tsBody1 with hσ
  obtain ⟨G, hs0, hs1, hL, hholds, hex, h3, htop, hg, hRe⟩ := H
  have mem : ∀ a, Stmt.atom a ∈ tsTail1 → Stmt.atom a ∈ tsBody1 :=
    fun a ha => List.mem_append_left _ (List.mem_append_right _ ha)
  have htop' : σ (.n 12) = Link.bitE R 1 := htop
  have hg' : σ (.n 18) = gen ^ R := hg
  have l19 := hL (.n 19) 0 (mem _ (by simp [tsTail1])) (tsStores_not_hi (by omega))
  have l22 := hL (.n 22) 0 (mem _ (by simp [tsTail1])) (tsStores_not_hi (by omega))
  have c20 := G (.const (.n 20) (word 1 0)) (mem _ (by simp [tsTail1]))
  have a21 := G (.add (.n 21) (.n 12) (.n 20)) (mem _ (by simp [tsTail1]))
  have a23 := G (.add (.n 23) (.n 21) (.n 22)) (mem _ (by simp [tsTail1]))
  have c24 := G (.const (.n 24) (word 2 0)) (mem _ (by simp [tsTail1]))
  have m25 := good_mul_eq (G (.mul (.n 25) (.n 12) (.n 24)) (mem _ (by simp [tsTail1]))) (by decide) (by decide)
  have a26 := G (.add (.n 26) (.n 19) (.n 25)) (mem _ (by simp [tsTail1]))
  have c27 := G (.const (.n 27) (word 1 0)) (mem _ (by simp [tsTail1]))
  have a28 := G (.add (.n 28) (.n 19) (.n 27)) (mem _ (by simp [tsTail1]))
  have m29 := good_mul_eq (G (.mul (.n 29) (.n 12) (.n 28)) (mem _ (by simp [tsTail1]))) (by decide) (by decide)
  have c30 := G (.const (.n 30) (word 0 0)) (mem _ (by simp [tsTail1]))
  have k31 := G (.copy (.n 31) (.n 18)) (mem _ (by simp [tsTail1]))
  have k32 := G (.copy (.n 32) (.n 23)) (mem _ (by simp [tsTail1]))
  have k33 := G (.copy (.n 33) (.n 12)) (mem _ (by simp [tsTail1]))
  simp only [Good] at c20 a21 a23 c24 a26 c27 a28 c30 k31 k32 k33
  simp only [tsW, zero_lt_one, ↓reduceIte] at l19 l22
  have hlow : polyE ((List.range 1).map (cbitE R)) = cbitE R 0 := by simp [polyE]
  rw [hlow] at hRe
  refine ⟨?_, ?_, fun a ha => ⟨?_, hex a (List.mem_append_left _ ha)⟩⟩
  · rw [hparams]
    simp only [List.map_cons, List.map_nil, hs0, hs1]
  · simp only [List.map_cons, List.map_nil]
    rw [k31, hg', k32, a23, a21, c20, word_one, l22, k33, htop']
    simp [tsLeadW, tsRestW, polyE, LeanVM.Guest.Value.eOfNat_zero]
  · have hm : Stmt.atom a ∈ tsBody1 := List.mem_append_left _ ha
    by_cases h1 : a = .assertEq (.n 26) (.n 3)
    · subst h1
      show σ (.n 26) + σ (.n 3) = 0
      rw [a26, m25, c24, word_gen, l19, htop', h3, hRe]
      linear_combination (cbitE R 0 + Link.bitE R 1 * gen + eOfNat (2 ^ 1 - 1)) * two_eq_zero_E
    by_cases h2 : a = .assertEq (.n 29) (.n 30)
    · subst h2
      show σ (.n 29) + σ (.n 30) = 0
      rw [m29, c30, word_zero, add_zero, a28, c27, l19, htop']
      have := ts_top_low hR (by norm_num)
      rw [hlow, show (2 : ℕ) ^ 1 - 1 = 1 by norm_num, LeanVM.Guest.Value.eOfNat_one] at this
      rw [word_one]; exact this
    exact hholds a hm h1 h2

/-- `table_size__L0`'s atoms. -/
def tsAtoms0 : List Stmt :=
  [.atom (.hint (.bits (.n 0) 0 1 (.heap (.n 1) 0 1))), .atom (.load (.n 2) (.n 1) 0),
    .atom (.mul (.n 3) (.n 2) (.n 2)), .atom (.load (.n 3) (.n 1) 0), .atom (.const (.n 4) (word 1 0)),
    .atom (.const (.n 5) (word 3 0)), .atom (.mul (.n 6) (.n 2) (.n 5)), .atom (.add (.n 7) (.n 4) (.n 6)),
    .atom (.assertEq (.n 2) (.n 0)), .atom (.const (.n 8) (word 0 0)), .atom (.mul (.n 9) (.n 2) (.n 8)),
    .atom (.const (.n 10) (word 0 0)), .atom (.assertEq (.n 9) (.n 10)), .atom (.copy (.n 11) (.n 7)),
    .atom (.const (.n 12) (word 1 0)), .atom (.const (.n 13) (word 1 0))]

/-- What the kernel checks of `tsBody0`: its values in order, its one store. -/
def tsChecks0 : Bool :=
  (chk 2 tsBody0).isSome && storesOf 2 tsBody0 == [.load (.n 3) (.n 1) 0]

/-- **`table_size__L0`'s template completes.** -/
theorem ts0_complete {kd : ℕ} {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = tsBody0)
    (hck : tsChecks0 = true) (R : ℕ) (bits : E) (hR : R ≤ 2 ^ 0) :
    CallCompletes0 kd name [eOfNat R, bits] [gen ^ R, tsLeadW R 0, tsRestW R 0]
      (fun rd ↦ ReadsAt rd bits (tsBitsW R 0)) PostQuiet := by
  simp only [tsChecks0, Bool.and_eq_true, beq_iff_eq] at hck
  obtain ⟨hc, hS⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  have hbody' : f.body = tsAtoms0 ++ [.ret [.n 11, .n 12, .n 13]] := hbody
  refine callCompletes0_straightRd (fun rd ↦ fwdVal rd (fun _ ↦ 0) [eOfNat R, bits] tsBody0) hfind hbody'
    (allAtoms_of_isAtomsB rfl) (by decide) fun rd _ hmem ↦ ?_
  set σ := fwdVal rd (fun _ ↦ 0) [eOfNat R, bits] tsBody0 with hσ
  have G : ∀ a, Stmt.atom a ∈ tsBody0 → Good rd (storesOf 2 tsBody0) (fun _ ↦ 0) σ a :=
    fwd_good (args := [eOfNat R, bits]) hc
  rw [hS] at G
  have hs0 : σ (.n 0) = eOfNat R := fwd_param (args := [eOfNat R, bits]) hc (by simp)
  have hs1 : σ (.n 1) = bits := fwd_param (args := [eOfNat R, bits]) hc (by simp)
  have hb0 : LoadHolds rd bits 0 (Link.bitE R 0) := readsAt_tsW (h := 0) hmem le_rfl
  have l2 : σ (.n 2) = Link.bitE R 0 :=
    good_load_eq (by rw [hs1]; exact hb0) (G _ (by simp [tsBody0])) (by decide)
  have m3 := good_mul_eq (G (.mul (.n 3) (.n 2) (.n 2)) (by simp [tsBody0])) (by decide) (by decide)
  have m6 := good_mul_eq (G (.mul (.n 6) (.n 2) (.n 5)) (by simp [tsBody0])) (by decide) (by decide)
  have m9 := good_mul_eq (G (.mul (.n 9) (.n 2) (.n 8)) (by simp [tsBody0])) (by decide) (by decide)
  have c4 := G (.const (.n 4) (word 1 0)) (by simp [tsBody0])
  have c5 := G (.const (.n 5) (word 3 0)) (by simp [tsBody0])
  have a7 := G (.add (.n 7) (.n 4) (.n 6)) (by simp [tsBody0])
  have c8 := G (.const (.n 8) (word 0 0)) (by simp [tsBody0])
  have c10 := G (.const (.n 10) (word 0 0)) (by simp [tsBody0])
  have k11 := G (.copy (.n 11) (.n 7)) (by simp [tsBody0])
  have c12 := G (.const (.n 12) (word 1 0)) (by simp [tsBody0])
  have c13 := G (.const (.n 13) (word 1 0)) (by simp [tsBody0])
  simp only [Good] at c4 c5 a7 c8 c10 k11 c12 c13
  have hR' : eOfNat R = Link.bitE R 0 := by
    interval_cases R <;> simp [bitE_eq, LeanVM.Guest.Value.eOfNat_zero, LeanVM.Guest.Value.eOfNat_one]
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  refine ⟨?_, ?_, fun a ha => ?_⟩
  · rw [hparams]; simp only [List.map_cons, List.map_nil, hs0, hs1]
  · simp only [List.map_cons, List.map_nil]
    rw [k11, a7, m6, c4, c5, c12, c13, word_one, w3, l2]
    interval_cases R
    · simp [bitE_eq, tsLeadW, tsRestW]
    · simp [bitE_eq, tsLeadW, tsRestW]; linear_combination two_eq_zero_E
  · simp only [tsAtoms0, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨trivial, ?_⟩
      show Dest.words rd σ (.heap (.n 1) 0 1) = _
      have e := tsBits_exact (R := R) (h := 0) hR (by norm_num)
      simp only [pow_zero, Nat.sub_self, LeanVM.Guest.Value.eOfNat_zero, add_zero] at e
      rw [hs0, ← e]
      have := heap_words (σ := σ) (p := .n 1) (rd := rd) (ws := tsBitsW R 0) (by rw [hs1]; exact hmem)
      rwa [tsBitsW_length] at this
    · exact ⟨by show LoadHolds rd (σ (.n 1)) 0 (σ (.n 2)); rw [hs1, l2]; exact hb0, trivial⟩
    · exact ⟨m3, trivial⟩
    · refine ⟨?_, trivial⟩
      show LoadHolds rd (σ (.n 1)) 0 (σ (.n 3))
      rw [hs1, m3, l2, bitE_mul_self]; exact hb0
    · exact ⟨c4, trivial⟩
    · exact ⟨c5, trivial⟩
    · exact ⟨m6, trivial⟩
    · exact ⟨a7, trivial⟩
    · refine ⟨?_, trivial⟩
      show σ (.n 2) + σ (.n 0) = 0
      rw [l2, hs0, hR', add_self_E]
    · exact ⟨c8, trivial⟩
    · exact ⟨m9, trivial⟩
    · exact ⟨c10, trivial⟩
    · refine ⟨?_, trivial⟩
      show σ (.n 9) + σ (.n 10) = 0
      rw [m9, c8, c10, word_zero, mul_zero, add_zero]
    · exact ⟨k11, trivial⟩
    · exact ⟨c12, trivial⟩
    · exact ⟨c13, trivial⟩

/-! ## The specializations -/

/-- What `table_size__L{h}`'s completeness gives: on `R ≤ 2^h` rows, its arguments and memory. -/
def TableSizeComplete (kd h : ℕ) (name : String) : Prop :=
  ∀ (R : ℕ) (bits : E), R ≤ 2 ^ h →
    CallCompletes0 kd name [eOfNat R, bits] [gen ^ R, tsLeadW R h, tsRestW R h]
      (fun rd ↦ ReadsAt rd bits (tsBitsW R h)) PostQuiet

theorem table_size_L0_complete (kd : ℕ) : TableSizeComplete kd 0 "table_size__L0" :=
  fun R bits hR ↦ ts0_complete (kd := kd) (f := fn% «table_size__L0»)
    (coreProgram_find?_at (j := idx% «table_size__L0») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

theorem table_size_L1_complete (kd : ℕ) : TableSizeComplete kd 1 "table_size__L1" :=
  fun R bits hR ↦ ts1_complete (kd := kd) (f := fn% «table_size__L1»)
    (coreProgram_find?_at (j := idx% «table_size__L1») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L2_complete (kd : ℕ) : TableSizeComplete kd 2 "table_size__L2" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 2) (by norm_num) (by norm_num) (f := fn% «table_size__L2»)
    (coreProgram_find?_at (j := idx% «table_size__L2») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L3_complete (kd : ℕ) : TableSizeComplete kd 3 "table_size__L3" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 3) (by norm_num) (by norm_num) (f := fn% «table_size__L3»)
    (coreProgram_find?_at (j := idx% «table_size__L3») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L4_complete (kd : ℕ) : TableSizeComplete kd 4 "table_size__L4" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 4) (by norm_num) (by norm_num) (f := fn% «table_size__L4»)
    (coreProgram_find?_at (j := idx% «table_size__L4») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L5_complete (kd : ℕ) : TableSizeComplete kd 5 "table_size__L5" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 5) (by norm_num) (by norm_num) (f := fn% «table_size__L5»)
    (coreProgram_find?_at (j := idx% «table_size__L5») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L6_complete (kd : ℕ) : TableSizeComplete kd 6 "table_size__L6" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 6) (by norm_num) (by norm_num) (f := fn% «table_size__L6»)
    (coreProgram_find?_at (j := idx% «table_size__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L7_complete (kd : ℕ) : TableSizeComplete kd 7 "table_size__L7" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 7) (by norm_num) (by norm_num) (f := fn% «table_size__L7»)
    (coreProgram_find?_at (j := idx% «table_size__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L8_complete (kd : ℕ) : TableSizeComplete kd 8 "table_size__L8" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 8) (by norm_num) (by norm_num) (f := fn% «table_size__L8»)
    (coreProgram_find?_at (j := idx% «table_size__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L9_complete (kd : ℕ) : TableSizeComplete kd 9 "table_size__L9" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 9) (by norm_num) (by norm_num) (f := fn% «table_size__L9»)
    (coreProgram_find?_at (j := idx% «table_size__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L10_complete (kd : ℕ) : TableSizeComplete kd 10 "table_size__L10" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 10) (by norm_num) (by norm_num) (f := fn% «table_size__L10»)
    (coreProgram_find?_at (j := idx% «table_size__L10») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L11_complete (kd : ℕ) : TableSizeComplete kd 11 "table_size__L11" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 11) (by norm_num) (by norm_num) (f := fn% «table_size__L11»)
    (coreProgram_find?_at (j := idx% «table_size__L11») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L12_complete (kd : ℕ) : TableSizeComplete kd 12 "table_size__L12" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 12) (by norm_num) (by norm_num) (f := fn% «table_size__L12»)
    (coreProgram_find?_at (j := idx% «table_size__L12») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L13_complete (kd : ℕ) : TableSizeComplete kd 13 "table_size__L13" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 13) (by norm_num) (by norm_num) (f := fn% «table_size__L13»)
    (coreProgram_find?_at (j := idx% «table_size__L13») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L14_complete (kd : ℕ) : TableSizeComplete kd 14 "table_size__L14" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 14) (by norm_num) (by norm_num) (f := fn% «table_size__L14»)
    (coreProgram_find?_at (j := idx% «table_size__L14») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L15_complete (kd : ℕ) : TableSizeComplete kd 15 "table_size__L15" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 15) (by norm_num) (by norm_num) (f := fn% «table_size__L15»)
    (coreProgram_find?_at (j := idx% «table_size__L15») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L16_complete (kd : ℕ) : TableSizeComplete kd 16 "table_size__L16" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 16) (by norm_num) (by norm_num) (f := fn% «table_size__L16»)
    (coreProgram_find?_at (j := idx% «table_size__L16») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L17_complete (kd : ℕ) : TableSizeComplete kd 17 "table_size__L17" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 17) (by norm_num) (by norm_num) (f := fn% «table_size__L17»)
    (coreProgram_find?_at (j := idx% «table_size__L17») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L18_complete (kd : ℕ) : TableSizeComplete kd 18 "table_size__L18" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 18) (by norm_num) (by norm_num) (f := fn% «table_size__L18»)
    (coreProgram_find?_at (j := idx% «table_size__L18») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L19_complete (kd : ℕ) : TableSizeComplete kd 19 "table_size__L19" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 19) (by norm_num) (by norm_num) (f := fn% «table_size__L19»)
    (coreProgram_find?_at (j := idx% «table_size__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L20_complete (kd : ℕ) : TableSizeComplete kd 20 "table_size__L20" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 20) (by norm_num) (by norm_num) (f := fn% «table_size__L20»)
    (coreProgram_find?_at (j := idx% «table_size__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L21_complete (kd : ℕ) : TableSizeComplete kd 21 "table_size__L21" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 21) (by norm_num) (by norm_num) (f := fn% «table_size__L21»)
    (coreProgram_find?_at (j := idx% «table_size__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L22_complete (kd : ℕ) : TableSizeComplete kd 22 "table_size__L22" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 22) (by norm_num) (by norm_num) (f := fn% «table_size__L22»)
    (coreProgram_find?_at (j := idx% «table_size__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L23_complete (kd : ℕ) : TableSizeComplete kd 23 "table_size__L23" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 23) (by norm_num) (by norm_num) (f := fn% «table_size__L23»)
    (coreProgram_find?_at (j := idx% «table_size__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

set_option maxRecDepth 100000 in
theorem table_size_L24_complete (kd : ℕ) : TableSizeComplete kd 24 "table_size__L24" :=
  fun R bits hR ↦ ts_complete (kd := kd) (h := 24) (by norm_num) (by norm_num) (f := fn% «table_size__L24»)
    (coreProgram_find?_at (j := idx% «table_size__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) (by decide +kernel) R bits hR

/-- **Every `table_size__L{h}` completes**, `h ≤ 24` (`N_ROW_LOGS`). -/
theorem table_size_complete (kd : ℕ) : ∀ h ≤ 24, TableSizeComplete kd h (tsNames.getD h "") := by
  intro h hh
  interval_cases h
  exacts [table_size_L0_complete kd, table_size_L1_complete kd, table_size_L2_complete kd,
    table_size_L3_complete kd, table_size_L4_complete kd, table_size_L5_complete kd, table_size_L6_complete kd,
    table_size_L7_complete kd, table_size_L8_complete kd, table_size_L9_complete kd, table_size_L10_complete kd,
    table_size_L11_complete kd, table_size_L12_complete kd, table_size_L13_complete kd,
    table_size_L14_complete kd, table_size_L15_complete kd, table_size_L16_complete kd,
    table_size_L17_complete kd, table_size_L18_complete kd, table_size_L19_complete kd,
    table_size_L20_complete kd, table_size_L21_complete kd, table_size_L22_complete kd,
    table_size_L23_complete kd, table_size_L24_complete kd]

end
end LeanVM.Guest.B1.VsC
