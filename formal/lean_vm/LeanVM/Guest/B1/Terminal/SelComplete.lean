/-
  LeanVM.Guest.B1.Terminal.SelComplete

  `column_selector`, placed, on `selector_tables`' buffer, the point and the nibble shares: complete
  on its honest valuation (`cskVal`), its tables from `selector_tables`' soundness on a
  memory holding its honest buffer.
-/

module

public import LeanVM.Guest.B1.Selectors.SelectorTablesAt
public import LeanVM.Guest.B1.Selectors.ColumnSelectorComplete
public import LeanVM.Guest.B1.Tables.VtC.Kids
public import LeanVM.Guest.B1.Terminal.Template

/-!
# The column selectors, placed

`selector_tables` returns its buffer `stOwn`. On a memory
holding it and the point's words `stLin`, `selector_tables`' statements hold (`st_holds`), so its
soundness puts the opening point's eq tables there (`selTabs_of_memL`). The nibble shares
`exponent_tables` wrote (`GTabsAt`) are the run `gTabW` (`gTabs_of_reads`, `reads_of_gTabs`).

`column_selector__L{κ}` range-checks its digits (the memory defined below `2^4`) and loads through
pointers it computes, so it is complete on its honest valuation, whose loads lie in the eq buffer
and the shares: `csk_holdsPre` and `csk_ret`, then `cs_completeAtDTB` (`completeAt_flatOutDTB`, no buffer,
no callee: within its frame).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-! ## The body, checked by the kernel -/

/-- An atom. -/
def isAtomS : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- `column_selector__L{κ}`'s loads, nibble by nibble: the eq weight through value `csC κ k + 4`,
the share through `csC κ k + 6` (the first nibble) or `+ 7`. -/
def csLoads (κ : ℕ) : List (V × ℕ) :=
  (List.range (csN κ)).flatMap fun k ↦
    [(.n (csC κ k + 4), 32 * (κ / 4 + k) + Tables.selEqOff (csW κ k - 1)),
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
    have hso : Tables.selEqOff (Tables.csW κ j - 1) ≤ 16 := by
      unfold Tables.selEqOff
      generalize Tables.csW κ j - 1 = w
      rcases w with _ | _ | _ | _ | w <;> simp
    rcases hq with rfl | rfl
    · have e : σ (.n (Tables.csC κ j + 4)) = ofK (addressOfIndex ese) * gen ^ Tables.cskU κ o j := by
        show Tables.cskVal _ _ _ _ _ _ _ (Tables.csC κ j + 4) = _
        rw [Tables.cskVal_at hκ' hj (by split <;> omega)]
        simp [Tables.cskRole]
      refine ⟨ese + Tables.cskU κ o j + (32 * (κ / 4 + j) + Tables.selEqOff (Tables.csW κ j - 1)), ?_,
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

end
end LeanVM.Guest.B1.VerifySub
