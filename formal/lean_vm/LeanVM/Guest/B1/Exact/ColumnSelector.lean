/-
  LeanVM.Guest.B1.Exact.ColumnSelector

  `column_selector__L{κ}`, placed within its frame, by a tree exact on the memory: its digits are its honest
  valuation's.
-/

module

public import LeanVM.Guest.B1.Terminal.SelComplete
public import LeanVM.Guest.Exact.Kids

/-!
# `column_selector`, exact

`cs_completeAtDTBRH`: `cs_completeAtDTB` by a node of honest shape whose valuation is `cskVal`. Its one computed hint,
the digits of its offset's exponent, is exact there (`csHint_exact`: `cskVal`'s digits are the exponent's nibbles), every
other is pinned by the next atom (none is: `cs_sites`), so `cs_completeAtDTBRE`: by a tree exact on the memory.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- `column_selector__L{κ}`'s computed hint: the digits of its offset's exponent. -/
def csHintA (κ : ℕ) : Atom :=
  .hint (.digitsExp (.n 0) 32 (Tables.csN κ) 4 (4 * (κ / 4)) none
    (.stack ((List.range (Tables.csN κ)).map fun k ↦ .n (3 + k))))

theorem cs_sites_all : (List.range 31).all (fun κ => Stmt.blockNextOk
    (fun a => isComputed a && !decide (a ∈ [csHintA κ])) pinsInverse
    (Tables.csPre κ ++ [.ret [.n (Tables.csRet κ)]])) = true := by
  decide +kernel

theorem cs_sites {κ : ℕ} (hκ : κ < 31) : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ [csHintA κ]))
    pinsInverse (Tables.csPre κ ++ [.ret [.n (Tables.csRet κ)]]) = true :=
  List.all_eq_true.mp cs_sites_all κ (List.mem_range.mpr hκ)

/-- **The digits hint is exact** at the honest valuation. -/
theorem csHint_exact {κ o : ℕ} (hκ : κ < 31) (ho : o < 2 ^ 32) {se sg : E} {p p1 : List E} {rd : Reader} :
    (csHintA κ).Exact rd (fun x ↦ Tables.cskVal κ o se sg p p1 rd x.idx) := by
  refine ⟨o, 4 * (κ / 4), ho, ?_, rfl, ?_⟩
  · show Tables.cskVal κ o se sg p p1 rd 0 = _
    rw [Tables.cskVal, ite_eq_left rfl, gen_pow_eq_ofK]
  · show ((List.range (Tables.csN κ)).map fun k ↦ V.n (3 + k)).map _ = _
    rw [List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj : j < Tables.csN κ := List.mem_range.mp hj
    have hj8 : κ / 4 + j < 8 := by simp only [Tables.csN] at hj; omega
    show Tables.cskVal κ o se sg p p1 rd (3 + j) = _
    rw [Tables.cskVal_digit (by omega) hj, gen_pow_eq_ofK, ite_eq_right (by omega), Tables.cskU,
      Nat.shiftRight_eq_div_pow, ← Nat.mul_add, pow_mul]
    rfl

theorem cs_completeAtDTBRH (k : ℕ) (hk : 4 ≤ k) {κ : ℕ} (hκ : κ < 31) {o : ℕ} (ho : o < 2 ^ 32)
    (hd : 2 ^ κ ∣ o) {ept ept1 ese bg : ℕ} {p p1 : List E} (hl : p.length = 32)
    (hl1 : p1.length = 32) :
    CompleteAtDTBR fs cert k (Tables.lName "column_selector" κ) (csLin ept ept1 ese bg p p1)
      [gen ^ o, ofK (addressOfIndex ese), ofK (addressOfIndex bg)]
      (Returns [Tables.bitsEq ((List.range (32 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ)
        (p1.drop κ)])
      (fun rd ↦ Budget.NodeHonest coreProgram (Tables.lName "column_selector" κ)
        (fun σ ↦ σ = fun x ↦ Tables.cskVal κ o (ofK (addressOfIndex ese)) (ofK (addressOfIndex bg)) p p1 rd x.idx)
        (flatCalls (Tables.csPre κ)) (fun _ ↦ []) []) (fs (Tables.lName "column_selector" κ)) := by
  obtain ⟨fn, hf, hp, hb⟩ := Tables.csFound hκ
  obtain ⟨hat, hfl, hnl, haddr, halloc, hld, hloop⟩ := Tables.cs_body hκ
  set f := Tables.lName "column_selector" κ
  set sel := Tables.bitsEq ((List.range (32 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ)
    (p1.drop κ)
  refine (completeAt_flatOutDTBR (fs := fs) (cert := cert) hf hloop k (csLin ept ept1 ese bg p p1) _
    (fun _ ↦ [sel]) _ hb hfl haddr [] (fun _ ↦ []) (fun _ ↦ .nil) (fun _ ↦ ⟨rfl, rfl⟩)
    (fun _ ↦ []) (fun rd σ ↦ σ = fun x ↦ Tables.cskVal κ o (ofK (addressOfIndex ese)) (ofK (addressOfIndex bg)) p
      p1 rd x.idx) [] [] 0 (fun _ ↦ trivial) (fun _ ↦ le_rfl)
    (fun _ ↦ le_rfl) (fun _ _ h ↦ absurd h (by simp)) (fun _ _ _ _ _ h ↦ absurd h (by simp))
    ?_).mono (by simp) fun _ _ h ↦ h
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
  refine ⟨σ, ?_, fun s hs ↦ ?_, ?_, by rw [halloc]; rfl, by rw [halloc]; rfl, ?_, ?_, rfl⟩
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


/-- **`column_selector__L{κ}`, placed within its frame, exact at every node.** -/
theorem cs_completeAtDTBRE (k : ℕ) (hk : 4 ≤ k) {κ : ℕ} (hκ : κ < 31) {o : ℕ} (ho : o < 2 ^ 32)
    (hd : 2 ^ κ ∣ o) {ept ept1 ese bg : ℕ} {p p1 : List E} (hl : p.length = 32)
    (hl1 : p1.length = 32) :
    CompleteAtDTBR fs cert k (Tables.lName "column_selector" κ) (csLin ept ept1 ese bg p p1)
      [gen ^ o, ofK (addressOfIndex ese), ofK (addressOfIndex bg)]
      (Returns [Tables.bitsEq ((List.range (32 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ)
        (p1.drop κ)]) (fun rd t ↦ t.Every (ExactAt coreProgram rd)) (fs (Tables.lName "column_selector" κ)) := by
  refine (cs_completeAtDTBRH (fs := fs) (cert := cert) (ept := ept) (ept1 := ept1) k hk hκ ho hd hl hl1).monoV
    le_rfl fun rd t rets hv hT => ?_
  obtain ⟨σ, ks, rfl, hQ, hc, hlen, hTk⟩ := hT
  obtain ⟨fn, hf, -, hb⟩ := Tables.csFound hκ
  have hv' := hv
  obtain ⟨fn', hf', -, es, vs, hw, -, hes, hkv⟩ := hv'
  rw [hf] at hf'
  cases hf'
  rw [hc fn es vs hf hw] at hkv
  refine Tree.every_node.mpr ⟨exactAt_of_walk hf hw (exact_of_sites (by rw [hb]; exact cs_sites hκ) hw hes
    fun a ha _ => ?_), everyKids_of_kidsT hkv hlen hTk fun _ _ hm => by simp at hm⟩
  rw [List.mem_singleton.mp ha, hQ]
  exact csHint_exact hκ ho

end
end LeanVM.Guest.B1.VerifySub
