/-
  LeanVM.Guest.B1.Terminal.SelComplete

  `column_selector`, placed, on `selector_tables`' buffer, the point and the nibble shares: complete
  on its honest valuation (B1-c's `cskVal`), its tables from `selector_tables`' soundness on a
  memory holding its honest buffer.
-/

module

public import LeanVM.Guest.B1.Selectors.SelectorTablesAt
public import LeanVM.Guest.B1.Selectors.ColumnSelectorComplete
public import LeanVM.Guest.B1.Tables.VtC.Kids
public import LeanVM.Guest.B1.Terminal.Template

/-!
# The column selectors, placed

`selector_tables` returns its buffer `stOwn` (B1-c's `selector_tables_completeAt`). On a memory
holding it and the point's words `stLin`, `selector_tables`' statements hold (`st_holds`), so its
soundness puts the opening point's eq tables there (`selTabs_of_memL`). The nibble shares
`exponent_tables` wrote (`GTabsAt`) are the run `gTabW` (`gTabs_of_reads`, `reads_of_gTabs`).

`column_selector__L{κ}` range-checks its digits (the memory defined below `2^4`) and loads through
pointers it computes, so it is complete on its honest valuation, whose loads lie in the eq buffer
and the shares: `csk_holdsPre` (B1-c's `csk_rel`, on the valuation) and `csk_ret` (its return,
`column_selector_complete_holds`'s), then `cs_completeAtDTB` (`completeAt_flatOutDTB`, no buffer,
no callee: within its frame).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-! ## The honest valuation (B1-c's `csk_rel` and `column_selector_complete_holds`, on it) -/

/-- **`column_selector__L{κ}`'s statements hold on its honest valuation `cskVal`.** -/
theorem csk_holdsPre {κ : ℕ} (hκ : κ < 31) {rd : Reader} {o : ℕ} {se sg : E} {p p1 : List E}
    (ho : o < 2 ^ 32) (hd : 2 ^ κ ∣ o) (hlow : ∀ i < 16, (rd (addressOfIndex i)).isSome)
    (hE : EqTabsAt rd se p p1) (hG : GTabsAt rd sg) {kret : List E → Prop} :
    Stmt.HoldsList (coreProgram.Rel rd) rd (fun x ↦ cskVal κ o se sg p p1 rd x.idx) (csPre κ) True
      kret := by
  set F := cskVal κ o se sg p p1 rd with hF
  have f0 : F 0 = gen ^ o := by simp [hF, cskVal]
  have f1 : F 1 = se := by simp [hF, cskVal]
  have f2 : F 2 = sg := by simp [hF, cskVal]
  by_cases h32 : κ = 32
  · subst h32
    have ho0 : o = 0 := by
      obtain ⟨q, rfl⟩ := hd
      have : q = 0 := by
        by_contra hq
        have : 2 ^ 32 * 1 ≤ 2 ^ 32 * q := Nat.mul_le_mul_left _ (by omega)
        omega
      simp [this]
    subst ho0
    simp only [csPre, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
      true_and]
    have e3 : F 3 = word 1 0 := by simp [hF, cskVal]
    have e4 : F 4 = word 1 0 := by simp [hF, cskVal]
    rw [e3, e4, f0, tb_word_one, pow_zero]
    exact ⟨rfl, e_add_self 1, rfl⟩
  have hκ' : κ < 32 := by omega
  have hdig := cs_digits hκ' ho (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd)
  have hu : ∀ k < csN κ, cskU κ o k < 16 := fun k _ => Nat.mod_lt _ (by norm_num)
  simp only [csPre, h32, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  rw [tb_holdsList_append_noRet (tb_noRetList_flatten_range _ _ (csNibT_noRet κ)),
    tb_holdsList_flatten_range _ _ (csNibT_noRet κ)]
  have hN1 : 1 ≤ csN κ := by unfold csN; omega
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · -- nibble `k`
    obtain ⟨hw1, hw4⟩ := csW_bounds κ k
    have hj : κ / 4 + k < 8 := by simp only [csN] at hk; omega
    have hdk := cs_dvd hu (by rw [show 16 ^ (κ / 4) * csDig (cskU κ o) (csN κ) = o from hdig.symm]; exact hd) k hk
    have hxe : LoadHolds rd (se * gen ^ cskU κ o k) (64 * (κ / 4 + k) + 16 * (csW κ k - 1))
        (cskXE κ o p p1 k) := by
      rw [tb_loadHolds_mul_gen_pow, show cskU κ o k + (64 * (κ / 4 + k) + 16 * (csW κ k - 1)) =
        64 * (κ / 4 + k) + 16 * (csW κ k - 1) + cskU κ o k by omega]
      exact hE _ hj _ (by omega) _ (hu k hk) hdk
    have hxg : LoadHolds rd (sg * gen ^ cskU κ o k) (16 * (κ / 4 + k)) (cskXG κ o k) := by
      rw [tb_loadHolds_mul_gen_pow, show cskU κ o k + 16 * (κ / 4 + k) =
        16 * (κ / 4 + k) + cskU κ o k by omega]
      exact hG _ hj _ (hu k hk)
    have hrc : LoadHolds rd (gen ^ cskU κ o k) 0 (cskRd rd (cskU κ o k)) ∧
        w15 = gen ^ cskU κ o k * gen ^ (15 - cskU κ o k) ∧
        LoadHolds rd (gen ^ (15 - cskU κ o k)) 0 (cskRd rd (15 - cskU κ o k)) :=
      ⟨csk_load hlow (hu k hk), by
        rw [← pow_add, Nat.add_sub_cancel' (by have := hu k hk; omega), word_g15, gen_pow_eq_ofK],
        csk_load hlow (by omega)⟩
    have e : ∀ s, s < (if k = 0 then 8 else 10) →
        F (csC κ k + s) = cskRole κ o se sg p p1 rd k s := fun s hs => cskVal_at hκ' hk hs
    have ed : F (3 + k) = gen ^ cskU κ o k := cskVal_digit hκ' hk
    unfold csNibT
    by_cases hk0 : k = 0
    · subst hk0
      have e' : ∀ s, s < 8 → F (csC κ 0 + s) = cskRole κ o se sg p p1 rd 0 s :=
        fun s hs => e s (by simpa using hs)
      simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.cons_append,
        List.nil_append]
      have e0 := e' 0 (by norm_num)
      rw [Nat.add_zero] at e0 ed
      rw [e0, e' 1 (by norm_num), e' 2 (by norm_num), e' 3 (by norm_num), e' 4 (by norm_num),
        e' 5 (by norm_num), e' 6 (by norm_num), e' 7 (by norm_num), ed, f1, f2]
      simp only [cskRole, Nat.add_zero, OfNat.ofNat_ne_zero, one_ne_zero, ↓reduceIte,
        show (2 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
        show (4 : ℕ) ≠ 1 by omega, show (4 : ℕ) ≠ 2 by omega, show (4 : ℕ) ≠ 3 by omega,
        show (5 : ℕ) ≠ 1 by omega, show (5 : ℕ) ≠ 2 by omega, show (5 : ℕ) ≠ 3 by omega,
        show (5 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 1 by omega, show (6 : ℕ) ≠ 2 by omega,
        show (6 : ℕ) ≠ 3 by omega, show (6 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 5 by omega,
        show (7 : ℕ) ≠ 1 by omega, show (7 : ℕ) ≠ 2 by omega, show (7 : ℕ) ≠ 3 by omega,
        show (7 : ℕ) ≠ 4 by omega, show (7 : ℕ) ≠ 5 by omega, show (7 : ℕ) ≠ 6 by omega]
      exact ⟨trivial, hrc, trivial, hxe, trivial, hxg⟩
    · have e' : ∀ s, s < 10 → F (csC κ k + s) = cskRole κ o se sg p p1 rd k s :=
        fun s hs => e s (by simpa [hk0] using hs)
      have eS : F (csSel κ (k - 1)) = cskS κ o p p1 (k - 1) := cskVal_sel hκ' (by omega)
      have eR : F (csRb κ (k - 1)) = cskR κ o (k - 1) := cskVal_rb hκ' (by omega)
      simp only [hk0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
        List.cons_append, List.nil_append]
      have e0 := e' 0 (by norm_num)
      rw [Nat.add_zero] at e0
      rw [e0, e' 1 (by norm_num), e' 2 (by norm_num), e' 3 (by norm_num), e' 4 (by norm_num),
        e' 5 (by norm_num), e' 6 (by norm_num), e' 7 (by norm_num), e' 8 (by norm_num),
        e' 9 (by norm_num), ed, f1, f2, eS, eR]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [cskRole, hk0, ↓reduceIte, Nat.add_sub_cancel, cskS, cskR, prod_range_succ _ (k' + 1),
        OfNat.ofNat_ne_zero, one_ne_zero,
        show (2 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
        show (4 : ℕ) ≠ 1 by omega, show (4 : ℕ) ≠ 2 by omega, show (4 : ℕ) ≠ 3 by omega,
        show (5 : ℕ) ≠ 1 by omega, show (5 : ℕ) ≠ 2 by omega, show (5 : ℕ) ≠ 3 by omega,
        show (5 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 1 by omega, show (6 : ℕ) ≠ 2 by omega,
        show (6 : ℕ) ≠ 3 by omega, show (6 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 5 by omega,
        show (7 : ℕ) ≠ 1 by omega, show (7 : ℕ) ≠ 2 by omega, show (7 : ℕ) ≠ 3 by omega,
        show (7 : ℕ) ≠ 4 by omega, show (7 : ℕ) ≠ 5 by omega, show (7 : ℕ) ≠ 6 by omega,
        show (8 : ℕ) ≠ 1 by omega, show (8 : ℕ) ≠ 2 by omega, show (8 : ℕ) ≠ 3 by omega,
        show (8 : ℕ) ≠ 4 by omega, show (8 : ℕ) ≠ 5 by omega, show (8 : ℕ) ≠ 6 by omega,
        show (8 : ℕ) ≠ 7 by omega, show (9 : ℕ) ≠ 1 by omega, show (9 : ℕ) ≠ 2 by omega,
        show (9 : ℕ) ≠ 3 by omega, show (9 : ℕ) ≠ 4 by omega, show (9 : ℕ) ≠ 5 by omega,
        show (9 : ℕ) ≠ 6 by omega, show (9 : ℕ) ≠ 7 by omega, show (9 : ℕ) ≠ 8 by omega]
      exact ⟨trivial, hrc, trivial, hxe, trivial, trivial, hxg, trivial⟩
  · -- the assertion and the copy
    have eS : F (csSel κ (csN κ - 1)) = cskS κ o p p1 (csN κ - 1) := cskVal_sel hκ' (by omega)
    have eR : F (csRb κ (csN κ - 1)) = cskR κ o (csN κ - 1) := cskVal_rb hκ' (by omega)
    have hC := csC_ge κ (csN κ)
    have eC : F (csC κ (csN κ)) = cskS κ o p p1 (csN κ - 1) := cskVal_last hκ'
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    rw [eS, eR, eC, f0]
    refine ⟨?_, rfl⟩
    rw [cskR, show csN κ - 1 + 1 = csN κ by omega,
      prod_congr rfl (fun m _ => show cskXG κ o m = gen ^ (cskU κ o m * 16 ^ (κ / 4 + m)) from rfl),
      prod_gen_pow_csDig, show 16 ^ (κ / 4) * csDig (cskU κ o) (csN κ) = o from hdig.symm]
    exact e_add_self _

/-- **`column_selector__L{κ}`'s honest return** is the selector. -/
theorem csk_ret {κ : ℕ} (hκ : κ < 31) {rd : Reader} {o : ℕ} {se sg : E} {p p1 : List E}
    (ho : o < 2 ^ 32) (hd : 2 ^ κ ∣ o) (hp : p.length = 32) (hp1 : p1.length = 32) :
    cskVal κ o se sg p p1 rd (csRet κ) =
      bitsEq ((List.range (32 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ) (p1.drop κ) := by
  by_cases h32 : κ = 32
  · subst h32
    have ho0 : o = 0 := by
      obtain ⟨q, rfl⟩ := hd
      have : q = 0 := by
        by_contra hq
        have : 2 ^ 32 * 1 ≤ 2 ^ 32 * q := Nat.mul_le_mul_left _ (by omega)
        omega
      simp [this]
    subst ho0
    have : cskVal 32 0 se sg p p1 rd (csRet 32) = 1 := by simp [cskVal, csRet, tb_word_one]
    rw [this]
    simp [bitsEq]
  have hκ' : κ < 32 := by omega
  have hdig := cs_digits hκ' ho (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd)
  have hret : cskVal κ o se sg p p1 rd (csRet κ) = cskS κ o p p1 (csN κ - 1) := by
    simp only [csRet, h32, ↓reduceIte]; exact cskVal_last hκ'
  rw [hret, cskS, show csN κ - 1 + 1 = csN κ by unfold csN; omega]
  have hsel := cs_sel_prod hκ' (u := cskU κ o) (fun k _ => Nat.mod_lt _ (by norm_num)) hp hp1
  rw [show (fun m ↦ cskXE κ o p p1 m) = fun k ↦ selEqEntry p p1 (κ / 4 + k) (csW κ k - 1)
    (cskU κ o k) from rfl]
  rw [hsel, show 16 ^ (κ / 4) * csDig (cskU κ o) (csN κ) = o from hdig.symm]

/-! ## The body, checked by the kernel -/

/-- An atom. -/
def isAtomS : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- `column_selector__L{κ}`'s loads, nibble by nibble: the eq weight through value `csC κ k + 4`,
the share through `csC κ k + 6` (the first nibble) or `+ 7`. -/
def csLoads (κ : ℕ) : List (V × ℕ) :=
  (List.range (csN κ)).flatMap fun k ↦
    [(.n (csC κ k + 4), 64 * (κ / 4 + k) + 16 * (csW κ k - 1)),
      (.n (csC κ k + if k = 0 then 6 else 7), 16 * (κ / 4 + k))]

/-- The facts of `column_selector__L{κ}`'s body the placed completeness uses. -/
noncomputable def csBodyOk (κ : ℕ) : Bool :=
  (csPre κ).all isAtomS && (csPre κ).all Stmt.flat && (csPre κ).all noLoadIte &&
    ((csPre κ).filterMap Main.Stmt.addrS).isEmpty &&
    ((csPre κ).filterMap Main.Stmt.allocSz).isEmpty &&
    decide ((csPre κ).filterMap Stmt.loadS = csLoads κ) &&
    !coreProgram.loop (lName "column_selector" κ)

theorem csBodyOk_all : (List.range 31).all csBodyOk = true := by decide +kernel

theorem cs_body {κ : ℕ} (hκ : κ < 31) :
    (csPre κ).all isAtomS = true ∧ (csPre κ).all Stmt.flat = true ∧
      (csPre κ).all noLoadIte = true ∧ (csPre κ).filterMap Main.Stmt.addrS = [] ∧
      (csPre κ).filterMap Main.Stmt.allocSz = [] ∧ (csPre κ).filterMap Stmt.loadS = csLoads κ ∧
      coreProgram.loop (lName "column_selector" κ) = false := by
  have h := List.all_eq_true.mp csBodyOk_all κ (List.mem_range.mpr hκ)
  simp only [csBodyOk, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end
end LeanVM.Guest.B1.Tables

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

theorem cs_addr_mul (b c k : ℕ) : (ofK (addressOfIndex b) * gen ^ c).limb 0 * addressOfIndex k =
    addressOfIndex (b + c + k) := by
  have e : ofK (addressOfIndex b) * gen ^ c = ofK (addressOfIndex (b + c)) := by
    rw [gen_pow_eq_ofK, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]
  rw [e, Main.addr_ofK]

/-! ## The nibble shares -/

/-- **The nibble shares' words** (`exponent_tables`): `g^(u·16^j)` at `16j + u`, `j < 8`. -/
def gTabW : List E := (List.range 128).map fun i ↦ gen ^ (i % 16 * 16 ^ (i / 16))

theorem gTabW_length : gTabW.length = 128 := by simp [gTabW]

theorem gTabs_of_reads {rd : Reader} {b : ℕ} (h : ReadsAt rd (ofK (addressOfIndex b)) gTabW) :
    Tables.GTabsAt rd (ofK (addressOfIndex b)) := fun j hj u hu ↦ by
  change j < 8 at hj
  have := h (16 * j + u) (by rw [gTabW_length]; omega)
  simp only [gTabW, List.getElem_map, List.getElem_range] at this
  rwa [show (16 * j + u) % 16 = u by omega, show (16 * j + u) / 16 = j by omega] at this

theorem reads_of_gTabs {rd : Reader} {b : ℕ} (h : Tables.GTabsAt rd (ofK (addressOfIndex b))) :
    ReadsAt rd (ofK (addressOfIndex b)) gTabW := fun k hk ↦ by
  rw [gTabW_length] at hk
  have := h (k / 16) (show k / 16 < 8 by omega) (k % 16) (by omega)
  simp only [gTabW, List.getElem_map, List.getElem_range]
  rwa [show 16 * (k / 16) + k % 16 = k by omega] at this

/-! ## The eq tables -/

/-- **`selector_tables`' honest buffer holds the opening point's tables**, on every memory holding
it and the point. -/
theorem selTabs_of_memL {ept ept1 ese : ℕ} {p p1 : List E} (hl : p.length = 32)
    (hl1 : p1.length = 32) {rd : Reader}
    (hm : MemL rd (Tables.stOwn ept ept1 ese p p1 ++ Tables.stLin ept ept1 p p1)) :
    Tables.EqTabsAt rd (ofK (addressOfIndex ese)) p p1 :=
  Tables.selector_tables_holds rd _ _ (Tables.st_holds ept ept1 ese p p1 hl hl1 rd hm) p p1 hl hl1
    (hm (ept, p) (by simp [Tables.stLin])) (hm (ept1, p1) (by simp [Tables.stLin]))

/-- The words `column_selector__L{κ}` reads: `selector_tables`' buffer, the point's runs and the
shares at `g^bg`. -/
noncomputable def csLin (ept ept1 ese bg : ℕ) (p p1 : List E) : Main.Layout :=
  Tables.stOwn ept ept1 ese p p1 ++ Tables.stLin ept ept1 p p1 ++ [(bg, gTabW)]

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxRecDepth 10000 in
/-- **`column_selector__L{κ}` is complete, placed, within its frame**, on `selector_tables`'
buffer, the point and the shares, the memory defined below `2^4`: it returns the eq weight of the
offset's bits above `κ`. -/
theorem cs_completeAtDTB (k : ℕ) (hk : 4 ≤ k) {κ : ℕ} (hκ : κ < 31) {o : ℕ} (ho : o < 2 ^ 32)
    (hd : 2 ^ κ ∣ o) {ept ept1 ese bg : ℕ} {p p1 : List E} (hl : p.length = 32)
    (hl1 : p1.length = 32) :
    CompleteAtDTB fs cert k (Tables.lName "column_selector" κ) (csLin ept ept1 ese bg p p1)
      [gen ^ o, ofK (addressOfIndex ese), ofK (addressOfIndex bg)]
      (Returns [Tables.bitsEq ((List.range (32 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ)
        (p1.drop κ)]) (fun _ ↦ True) (fs (Tables.lName "column_selector" κ)) := by
  obtain ⟨fn, hf, hp, hb⟩ := Tables.csFound hκ
  obtain ⟨hat, hfl, hnl, haddr, halloc, hld, hloop⟩ := Tables.cs_body hκ
  set f := Tables.lName "column_selector" κ
  set sel := Tables.bitsEq ((List.range (32 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ)
    (p1.drop κ)
  refine (completeAt_flatOutDTB (fs := fs) (cert := cert) hf hloop k (csLin ept ept1 ese bg p p1) _
    (fun _ ↦ [sel]) _ hb hfl haddr [] (fun _ ↦ []) (fun _ ↦ .nil) (fun _ ↦ ⟨rfl, rfl⟩)
    (fun _ ↦ []) (fun _ ↦ True) [] [] 0 (fun _ ↦ trivial) (fun _ ↦ le_rfl)
    (fun _ ↦ le_rfl) (fun _ _ h ↦ absurd h (by simp)) (fun _ _ _ _ _ h ↦ absurd h (by simp))
    ?_).mono (by simp) fun _ _ ↦ trivial
  intro fp outs ho' rd hlow _ hLin
  have hlow16 : ∀ i < 16, (rd (addressOfIndex i)).isSome := fun i hi ↦
    hlow i (lt_of_lt_of_le hi (by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk))
  have hE : Tables.EqTabsAt rd (ofK (addressOfIndex ese)) p p1 :=
    selTabs_of_memL hl hl1 fun q hq ↦ hLin q (List.mem_append_left _ hq)
  have hG : Tables.GTabsAt rd (ofK (addressOfIndex bg)) :=
    gTabs_of_reads (hLin (bg, gTabW) (by simp [csLin]))
  set σ : Val := fun x ↦ Tables.cskVal κ o (ofK (addressOfIndex ese)) (ofK (addressOfIndex bg)) p
    p1 rd x.idx with hσ
  have hcall : (Tables.csPre κ).filterMap (Stmt.callSF σ) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro s hs
    have := List.all_eq_true.mp hat s hs
    cases s with
    | atom a => rfl
    | _ => simp [Tables.isAtomS] at this
  refine ⟨σ, ?_, fun s hs ↦ ?_, ?_, by rw [halloc]; rfl, by rw [halloc]; rfl, ?_, ?_, trivial⟩
  · rw [hp]; simp [hσ, Tables.cskVal]
  · have := List.all_eq_true.mp hat s hs
    cases s <;> simp_all [Tables.isAtomS, DispOk]
  · rw [hb, holdsList_append, holdsList_noRet _ (Tables.csPre_noRet κ)]
    refine ⟨Tables.csk_holdsPre hκ ho hd hlow16 hE hG, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
    rw [hσ]
    simp only [Tables.csk_ret hκ ho hd hl hl1, sel]
  · rw [flatCalls, hcall]
    match outs, ho' with
    | [], _ => exact True.intro
  · rw [flatMap_loadsEv _ _ hnl, hld]
    intro q hq
    simp only [Tables.csLoads, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    obtain ⟨j, hj, hq⟩ := hq
    have hκ' : κ < 32 := by
      by_contra h; simp only [Tables.csN] at hj; omega
    have hu : Tables.cskU κ o j < 16 := Nat.mod_lt _ (by norm_num)
    have hjn : κ / 4 + j < 8 := by simp only [Tables.csN] at hj; omega
    obtain ⟨hw1, hw4⟩ := Tables.csW_bounds κ j
    rcases hq with rfl | rfl
    · have e : σ (.n (Tables.csC κ j + 4)) = ofK (addressOfIndex ese) * gen ^ Tables.cskU κ o j := by
        show Tables.cskVal _ _ _ _ _ _ _ (Tables.csC κ j + 4) = _
        rw [Tables.cskVal_at hκ' hj (by split <;> omega)]
        simp [Tables.cskRole]
      refine ⟨ese + Tables.cskU κ o j + (64 * (κ / 4 + j) + 16 * (Tables.csW κ j - 1)), ?_,
        Or.inl ⟨(ese, Tables.stEqWords (Tables.stVal ept ept1 ese p p1)), by simp [csLin, Tables.stOwn],
          by omega, by simp [Tables.stEqWords]; omega⟩⟩
      rw [e]; exact cs_addr_mul _ _ _
    · have e : σ (.n (Tables.csC κ j + if j = 0 then 6 else 7)) =
          ofK (addressOfIndex bg) * gen ^ Tables.cskU κ o j := by
        show Tables.cskVal _ _ _ _ _ _ _ (Tables.csC κ j + if j = 0 then 6 else 7) = _
        by_cases hj0 : j = 0
        · subst hj0
          rw [ite_pos' rfl, Tables.cskVal_at hκ' hj (by simp)]
          simp [Tables.cskRole]
        · rw [ite_neg' hj0, Tables.cskVal_at hκ' hj (by simp [hj0])]
          simp [Tables.cskRole, hj0]
      refine ⟨bg + Tables.cskU κ o j + 16 * (κ / 4 + j), ?_,
        Or.inl ⟨(bg, gTabW), by simp [csLin], by omega, by rw [gTabW_length]; omega⟩⟩
      rw [e]; exact cs_addr_mul _ _ _

/-- **`column_selector__L{κ}` is complete, placed, within its frame** (`cs_completeAtDTB`). -/
theorem cs_completeAtB (k : ℕ) (hk : 4 ≤ k) {κ : ℕ} (hκ : κ < 31) {o : ℕ} (ho : o < 2 ^ 32)
    (hd : 2 ^ κ ∣ o) {ept ept1 ese bg : ℕ} {p p1 : List E} (hl : p.length = 32)
    (hl1 : p1.length = 32) :
    CompleteAtB fs cert k (Tables.lName "column_selector" κ) (csLin ept ept1 ese bg p p1)
      [gen ^ o, ofK (addressOfIndex ese), ofK (addressOfIndex bg)]
      (Returns [Tables.bitsEq ((List.range (32 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ)
        (p1.drop κ)]) (fs (Tables.lName "column_selector" κ)) := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho', hw, hd', hr⟩ :=
    cs_completeAtDTB (fs := fs) (cert := cert) (ept := ept) (ept1 := ept1) (ese := ese) (bg := bg)
      k hk hκ ho hd hl hl1 fp
  ⟨n, Lown, rets, Lout, ho', hw, hd', hn, fun rd hl' hm => (hr rd hl' hm).relAtIn⟩

/-- **`column_selector__L{κ}` is complete, placed** (`cs_completeAtDTB`). -/
theorem cs_completeAt (k : ℕ) (hk : 4 ≤ k) {κ : ℕ} (hκ : κ < 31) {o : ℕ} (ho : o < 2 ^ 32)
    (hd : 2 ^ κ ∣ o) {ept ept1 ese bg : ℕ} {p p1 : List E} (hl : p.length = 32)
    (hl1 : p1.length = 32) :
    CompleteAtD fs cert k (Tables.lName "column_selector" κ) (csLin ept ept1 ese bg p p1)
      [gen ^ o, ofK (addressOfIndex ese), ofK (addressOfIndex bg)]
      (Returns [Tables.bitsEq ((List.range (32 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ)
        (p1.drop κ)]) :=
  (cs_completeAtB (ept := ept) (ept1 := ept1) k hk hκ ho hd hl hl1).toCompleteAtD

end
end LeanVM.Guest.B1.VerifySub
