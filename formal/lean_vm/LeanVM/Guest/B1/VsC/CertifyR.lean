/-
  LeanVM.Guest.B1.VsC.CertifyR

  `certify_stack`'s body under forward evaluation on an honest memory: every atom holds.
-/

module

public import LeanVM.Guest.B1.VsC.CertifyW

/-!
# `certify_stack`'s run

`cs_run`: on a valuation satisfying the body's equations (`Good`), its fresh loads no stores, its
parameters `qk`, `qt`, its buffers at the cursor `c`, on a memory defined below `2^k`, `11 ≤ k`,
with the exponent tables at `qt`, the kappa sources at `qk` and the node's own words (`csWords`),
every atom of `certify_stack`'s body holds, the total it hands `log2` is `g^T`, and every load reads
the node's buffers, the tables or the kappa sources. The segments by `csKey_fwd`, `csRank0_fwd`,
`csRank_fwd` (by induction on the rank: the previous key and total), `csOut_fwd`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Whir LeanVM.Guest.B1.Fwd LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The segments' places -/

theorem csKey_ge (gi s : ℕ) : s ≤ (csKey gi s).2 := by
  unfold csKey
  rcases csKappa_shape (csG gi) s with ⟨-, -, -, h3⟩ | ⟨-, -, -, h3⟩ <;>
    by_cases hb : (csG gi).b0 = 0 <;> simp only [hb, ↓reduceIte, h3] <;> omega

theorem csOut_ge (gi s : ℕ) : s ≤ (csOut 303 164 gi s).2 := by
  unfold csOut
  rcases csKappa_shape (csG gi) s with ⟨-, -, -, h3⟩ | ⟨-, -, -, h3⟩ <;> simp only [h3] <;> omega

theorem mem_csKeys {a : Stmt} : ∀ (n gi s : ℕ), a ∈ (csKeys gi n s).1 →
    ∃ j < n, ∃ s', s ≤ s' ∧ a ∈ (csKey (gi + j) s').1 ∧ ∀ st ∈ (csKey (gi + j) s').1, st ∈ (csKeys gi n s).1
  | 0, _, _, h => absurd h List.not_mem_nil
  | n + 1, gi, s, h => by
    rw [csKeys] at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨0, by omega, s, le_rfl, h, fun st hst => by rw [csKeys]; exact List.mem_append_left _ hst⟩
    · obtain ⟨j, hj, s', hs', ha, hsub⟩ := mem_csKeys n (gi + 1) _ h
      refine ⟨j + 1, by omega, s', le_trans (csKey_ge gi s) hs', by rw [show gi + (j + 1) = gi + 1 + j by omega]; exact ha,
        fun st hst => ?_⟩
      rw [csKeys]
      exact List.mem_append_right _ (hsub st (by rw [show gi + 1 + j = gi + (j + 1) by omega]; exact hst))

theorem mem_csOuts {a : Stmt} : ∀ (n gi s : ℕ), a ∈ (csOuts 303 164 gi n s).1 →
    ∃ j < n, ∃ s', s ≤ s' ∧ a ∈ (csOut 303 164 (gi + j) s').1 ∧
      ∀ st ∈ (csOut 303 164 (gi + j) s').1, st ∈ (csOuts 303 164 gi n s).1
  | 0, _, _, h => absurd h List.not_mem_nil
  | n + 1, gi, s, h => by
    rw [csOuts] at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨0, by omega, s, le_rfl, h, fun st hst => by rw [csOuts]; exact List.mem_append_left _ hst⟩
    · obtain ⟨j, hj, s', hs', ha, hsub⟩ := mem_csOuts n (gi + 1) _ h
      refine ⟨j + 1, by omega, s', le_trans (csOut_ge gi s) hs', by rw [show gi + (j + 1) = gi + 1 + j by omega]; exact ha,
        fun st hst => ?_⟩
      rw [csOuts]
      exact List.mem_append_right _ (hsub st (by rw [show gi + 1 + j = gi + (j + 1) by omega]; exact hst))

/-- `certify_stack`'s body before its return, by its parts. -/
theorem csBodyA_eq : csBodyA = csLoads ++ (csKeys 0 8 12).1 ++
    [.atom (.hint (.alloc (.n 163) 8)), .atom (.hint (.witness "stk_group_order" (.heap (.n 163) 0 8))),
      .atom (.hint (.alloc (.n 164) 8))] ++ csRanks 163 164 165 ++
    [.call "log2_ceil_in_the_exponent__L16_L34" [.n 301, .n 1] [.n 302], .atom (.hint (.alloc (.n 303) 104))] ++
    (csOuts 303 164 0 8 304).1 ++
    [.atom (.copy (.n 374) (.n 302)), .atom (.copy (.n 375) (.n 303)), osCst 376 (csW 52), osMul 377 303 376] := by
  simp only [csBodyA, csKeys_end, Nat.reduceAdd, Nat.reduceMul, csOuts_end]

/-! ## The keys' order -/

theorem csKeyW_shift {kv : ℕ → ℕ} {gi : ℕ} (hgi : gi < 8) : csKeyW kv gi * gen ^ 52 = gen ^ csN kv gi := by
  apply csKey_shift hgi
  unfold csKeyW
  by_cases hb : (csG gi).b0 = 0
  · rw [ite_pos' hb, hb, pow_zero, mul_one, ← pow_mul]; congr 1; unfold csKap; ring
  · rw [ite_neg' hb, mul_assoc, csInv_eq gi hgi hb, mul_one, ← pow_mul]; congr 1; unfold csKap; ring

/-! ## The run -/

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- Where `certify_stack`'s loads read: its buffers `[c, c + 136)`, the exponent table's squares at
`qt`, the kappa sources at `qk`. -/
def CsLoadIn (c qt qk i : ℕ) : Prop := (c ≤ i ∧ i < c + 136) ∨ (qt ≤ i ∧ i < qt + 34) ∨ (qk ≤ i ∧ i < qk + 8)

/-- Rank `r`'s key value and total value. -/
def csPk (r : ℕ) : ℕ := if r = 0 then 165 + 6 else 165 + 11 + 18 * (r - 1) + 6

def csTt (r : ℕ) : ℕ := if r = 0 then 165 + 10 else 165 + 11 + 18 * (r - 1) + 17

/-- Rank `r`'s statements. -/
def csRankSeg (r : ℕ) : List Stmt :=
  if r = 0 then csRank0L 165 else csRank 163 164 (165 + 11 + 18 * (r - 1)) (csPk (r - 1)) (csTt (r - 1)) r

theorem mem_csRanks {a : Stmt} (h : a ∈ csRanks 163 164 165) : ∃ r < 8, a ∈ csRankSeg r := by
  rw [csRanks_eq] at h
  rcases List.mem_append.mp h with h | h
  · exact ⟨0, by omega, by simpa [csRankSeg] using h⟩
  · obtain ⟨l, hl, ha⟩ := List.mem_flatten.mp h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    refine ⟨r + 1, by simp at hr; omega, ?_⟩
    simp only [csRankSeg, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact ha

theorem csRankSeg_sub {r : ℕ} (hr : r < 8) : ∀ st ∈ csRankSeg r, st ∈ csRanks 163 164 165 := by
  intro st hst
  rw [csRanks_eq]
  rcases r with _ | r
  · exact List.mem_append_left _ (by simpa [csRankSeg] using hst)
  · refine List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨r, List.mem_range.mpr (by omega), rfl⟩, ?_⟩)
    simp only [csRankSeg, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hst
    exact hst

theorem limb_gpow_addr' (p : E) (e o : ℕ) :
    (p * gen ^ e).limb 0 * addressOfIndex o = p.limb 0 * addressOfIndex (e + o) := by
  rw [gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]

theorem ptrAtV_addr (a t : ℕ) : (ptrAtV a).limb 0 * addressOfIndex t = addressOfIndex (a + t) := by
  simp [ptrAtV, addressOfIndex, pow_add]

/-- **`certify_stack`'s body holds** on an honest memory, under its equations. -/
theorem cs_run {k : ℕ} (hk : 11 ≤ k) (hl : LowDef k rd) {bytecode : List K} {lm : ℕ} {rows : List ℕ}
    {layout : Layout} (hbl : buildLayout bytecode lm rows = some layout) (hL : layout.stackLog ≤ 30)
    (hG : ∀ a, Stmt.atom a ∈ csBodyA → Good rd S w σ a) (hF : FreshOk S csBodyA) {c qt qk : ℕ}
    (hp0 : σ (.n 0) = ptrAtV qk) (hp1 : σ (.n 1) = ptrAtV qt) (h10 : σ (.n 10) = ptrAtV c)
    (h11 : σ (.n 11) = ptrAtV (c + 8)) (h163 : σ (.n 163) = ptrAtV (c + 16)) (h164 : σ (.n 164) = ptrAtV (c + 24))
    (h303 : σ (.n 303) = ptrAtV (c + 32)) (ht : ExpTables rd (ptrAtV qt))
    (hks : ReadsAt rd (ptrAtV qk) (kappaSources layout.logMemory layout.tableLogHeights))
    (hW : HoldsWords rd (csWords layout c)) :
    (∀ a, Stmt.atom a ∈ csBodyA → a.Holds rd σ) ∧
      σ (.n 301) = gen ^ csTot (csKv layout) (csρ layout) 8 ∧
      ∀ d p off, Stmt.atom (.load d p off) ∈ csBodyA →
        ∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧ CsLoadIn c qt qk i := by
  obtain ⟨hk30, -, -⟩ := cs_layout hbl hL
  obtain ⟨hperm, hR, hstep⟩ := csOrd_facts layout fun g hg => by have := hk30 g hg; omega
  obtain ⟨hrk1, hrk2⟩ := csRk_facts hperm
  set kv := csKv layout with hkv
  set ρ := csρ layout with hρ
  have hρ8 : ∀ r < 8, ρ r < 8 := hR.lt
  -- the memory's words
  have wK : ReadsAt rd (ptrAtV c) ((List.range 8).map (csKeyW kv)) := hW _ List.mem_cons_self
  have wS : ReadsAt rd (ptrAtV (c + 8)) ((List.range 8).map fun gi => gen ^ csSize kv gi) :=
    hW _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have wO : ReadsAt rd (ptrAtV (c + 16)) ((csOrd (stackKappas layout)).map Prover.count) :=
    hW _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have wA : ReadsAt rd (ptrAtV (c + 24)) ((List.range 8).map (csAtW layout)) :=
    hW _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have wU : ReadsAt rd (ptrAtV (c + 32)) (csOutsW layout) :=
    hW _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))))
  have hlen8 : (csOrd (stackKappas layout)).length = 8 := by rw [hperm.length_eq, List.length_range]
  have lK : ∀ gi < 8, LoadHolds rd (σ (.n 10)) gi (csKeyW kv gi) := fun gi hgi => by
    have := wK gi (by simp; omega); simpa [h10] using this
  have lS : ∀ gi < 8, LoadHolds rd (σ (.n 11)) gi (gen ^ csSize kv gi) := fun gi hgi => by
    have := wS gi (by simp; omega); simpa [h11] using this
  have lO : ∀ r < 8, LoadHolds rd (σ (.n 163)) r (gen ^ ρ r) := fun r hr => by
    have := wO r (by simp; omega)
    simp only [List.getElem_map, Prover.count, gpow] at this
    rw [h163]; convert this using 2
    show csRho _ r = _; unfold csRho; rw [List.getD_eq_getElem _ _ (by omega)]
  have lA : ∀ r < 8, LoadHolds rd (σ (.n 164)) (ρ r) (gen ^ csTot kv ρ r) := fun r hr => by
    have := wA (ρ r) (by simp; exact hρ8 r hr)
    simp only [List.getElem_map, List.getElem_range, csAtW] at this
    rw [h164]; convert this using 3; exact (hrk2 r hr).symm
  have lAg : ∀ gi < 8, LoadHolds rd (σ (.n 164)) gi (gen ^ csTot kv ρ (csRk (stackKappas layout) gi)) :=
    fun gi hgi => by
      have := wA gi (by simp; omega)
      simpa [h164, csAtW] using this
  have lU : ∀ b < 104, LoadHolds rd (σ (.n 303)) b ((csOutsW layout).getD b 0) := fun b hb => by
    have := wU b (by rw [csOutsW_length]; omega)
    rw [h303, List.getD_eq_getElem _ _ (by rw [csOutsW_length]; omega)]; exact this
  have hkb : ∀ i < 8, σ (.n (2 + i)) = gen ^ kv i := fun i hi => by
    have hm : Stmt.atom (.load (.n (2 + i)) (.n 0) i) ∈ csBodyA := by
      rw [csBodyA_eq]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))))))
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    exact (good_fresh (hG _ hm) (hF _ _ _ hm (by simp [freshShape]))
      (by rw [hp0]; exact kappaSources_get hks i hi)).1
  have ht' : ExpTables rd (σ (.n 1)) := by rw [hp1]; exact ht
  -- the parts' places
  have inK : ∀ st ∈ (csKeys 0 8 12).1, st ∈ csBodyA := fun st h => by
    rw [csBodyA_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ h)))))
  have inR : ∀ st ∈ csRanks 163 164 165, st ∈ csBodyA := fun st h => by
    rw [csBodyA_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))
  have inO : ∀ st ∈ (csOuts 303 164 0 8 304).1, st ∈ csBodyA := fun st h => by
    rw [csBodyA_eq]
    exact List.mem_append_left _ (List.mem_append_right _ h)
  have ofT : gen ^ csTot kv ρ 0 = (1 : E) := by simp [csTot]
  -- the ranks, in order
  have hranks : ∀ r < 8, σ (.n (csPk r)) = csKeyW kv (ρ r) ∧ σ (.n (csTt r)) = gen ^ csTot kv ρ (r + 1) ∧
      (∀ a, Stmt.atom a ∈ csRankSeg r → a.Holds rd σ) ∧
      ∀ d p off, Stmt.atom (.load d p off) ∈ csRankSeg r →
        ∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧ CsLoadIn c qt qk i := by
    intro r
    induction r with
    | zero =>
      intro _
      have hseg : ∀ st ∈ csRank0L 165, st ∈ csBodyA := fun st h => inR st (csRankSeg_sub (r := 0) (by omega) st
        (by simpa [csRankSeg] using h))
      obtain ⟨hA, v6, v10, hld⟩ := csRank0_fwd (S := S) (w := w) (show 3 ≤ k by omega) hl (s0 := 165) le_rfl
        (hρ8 0 (by omega)) (fun a ha => hG a (hseg _ ha)) (hF.sub hseg) (lO 0 (by omega)) (lK _ (hρ8 0 (by omega)))
        (by have := lA 0 (by omega); rwa [ofT] at this) (lS _ (hρ8 0 (by omega)))
      refine ⟨v6, ?_, fun a ha => hA a (by simpa [csRankSeg] using ha), fun d p off ha => ?_⟩
      · show σ (.n (165 + 10)) = _; rw [v10, csTot_succ]; simp [csTot]
      · rcases hld d p off (by simpa [csRankSeg] using ha) with ⟨rfl, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩
        · exact ⟨c + 16, by rw [h163, ptrAtV_addr], Or.inl ⟨by omega, by omega⟩⟩
        · exact ⟨c + ρ 0, by rw [hp, h10]; simp only [limb_gpow_addr', ptrAtV_addr, Nat.add_zero],
            Or.inl ⟨by omega, by have := hρ8 0 (by omega); omega⟩⟩
        · exact ⟨c + 24 + ρ 0, by rw [hp, h164]; simp only [limb_gpow_addr', ptrAtV_addr, Nat.add_zero],
            Or.inl ⟨by omega, by have := hρ8 0 (by omega); omega⟩⟩
        · exact ⟨c + 8 + ρ 0, by rw [hp, h11]; simp only [limb_gpow_addr', ptrAtV_addr, Nat.add_zero],
            Or.inl ⟨by omega, by have := hρ8 0 (by omega); omega⟩⟩
    | succ r ih =>
      intro hr
      obtain ⟨ipk, itt, -, -⟩ := ih (by omega)
      have hseg : ∀ st ∈ csRankSeg (r + 1), st ∈ csBodyA := fun st h => inR st (csRankSeg_sub hr st h)
      have hseg' : csRankSeg (r + 1) = csRank 163 164 (165 + 11 + 18 * r) (csPk r) (csTt r) (r + 1) := by
        simp [csRankSeg]
      rw [hseg'] at hseg
      have hpk : csPk r < 165 + 11 + 18 * r := by unfold csPk; split <;> omega
      have htt : csTt r < 165 + 11 + 18 * r := by unfold csTt; split <;> omega
      obtain ⟨hA, v6, v17, hld⟩ := csRank_fwd (S := S) (w := w) hk hl (s := 165 + 11 + 18 * r) (by omega) hpk htt
        (hρ8 (r + 1) hr) (fun a ha => hG a (hseg _ ha)) (hF.sub hseg) (lO (r + 1) hr) (lK _ (hρ8 (r + 1) hr))
        (csKeyW_shift (hρ8 (r + 1) hr)) (by rw [ipk]; exact csKeyW_shift (hρ8 r (by omega)))
        (hR.desc r (by omega)) (hstep r (by omega)) itt (lA (r + 1) hr) (lS _ (hρ8 (r + 1) hr))
      refine ⟨by simp only [csPk, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; exact v6, ?_,
        fun a ha => hA a (by rw [hseg'] at ha; exact ha), fun d p off ha => ?_⟩
      · simp only [csTt, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [v17, csTot_succ kv ρ (r + 1), pow_add]
      · rw [hseg'] at ha
        have h8 := hρ8 (r + 1) hr
        rcases hld d p off ha with ⟨rfl, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩
        · exact ⟨c + 16 + (r + 1), by rw [h163, ptrAtV_addr], Or.inl ⟨by omega, by omega⟩⟩
        · exact ⟨c + ρ (r + 1), by rw [hp, h10]; simp only [limb_gpow_addr', ptrAtV_addr, Nat.add_zero],
            Or.inl ⟨by omega, by omega⟩⟩
        · exact ⟨c + 24 + ρ (r + 1), by rw [hp, h164]; simp only [limb_gpow_addr', ptrAtV_addr, Nat.add_zero],
            Or.inl ⟨by omega, by omega⟩⟩
        · exact ⟨c + 8 + ρ (r + 1), by rw [hp, h11]; simp only [limb_gpow_addr', ptrAtV_addr, Nat.add_zero],
            Or.inl ⟨by omega, by omega⟩⟩
  have h301 : σ (.n 301) = gen ^ csTot kv ρ 8 := (hranks 7 (by omega)).2.1
  -- the outputs' words
  have lOut : ∀ gi < 8, ∀ j < (csG gi).len,
      LoadHolds rd (σ (.n 303)) ((csG gi).b0 + j) (gen ^ (csTot kv ρ (csRk (stackKappas layout) gi) +
        j * 2 ^ csKap kv gi)) ∧ LoadHolds rd (σ (.n 303)) (52 + (csG gi).b0 + j) (gen ^ csKap kv gi) := by
    intro gi hgi j hj
    have hbl : ∀ gi < 8, (csG gi).b0 + (csG gi).len ≤ 52 := by decide
    have hb : (csG gi).b0 + j < 52 := by have := hbl gi hgi; omega
    have hgo : grpOf ((csG gi).b0 + j) = gi := grpOf_block gi hgi j hj
    constructor
    · have := lU ((csG gi).b0 + j) (by omega)
      rw [List.getD_eq_getElem _ _ (by rw [csOutsW_length]; omega), csOutsW_off layout hb, csOffW, hgo,
        show (csG gi).b0 + j - (csG gi).b0 = j by omega] at this
      exact this
    · have := lU (52 + ((csG gi).b0 + j)) (by omega)
      rw [List.getD_eq_getElem _ _ (by rw [csOutsW_length]; omega), csOutsW_kap layout hb, hgo,
        show 52 + ((csG gi).b0 + j) = 52 + (csG gi).b0 + j by omega] at this
      exact this
  have keyF : ∀ a, Stmt.atom a ∈ (csKeys 0 8 12).1 → a.Holds rd σ ∧ ∀ d p off, a = .load d p off →
      ∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧ CsLoadIn c qt qk i := by
    intro a ha
    obtain ⟨gi, hgi, s', hs', ham, hsub⟩ := mem_csKeys 8 0 12 ha
    rw [Nat.zero_add] at ham hsub
    have hseg : ∀ st ∈ (csKey gi s').1, st ∈ csBodyA := fun st h => inK st (hsub st h)
    obtain ⟨hA, hld⟩ := csKey_fwd (S := S) (w := w) (show 6 ≤ k by omega) hl hkb ht' hgi
      (by have := hk30 gi hgi; omega) (by omega) (fun b hb => hG b (hseg _ hb)) (hF.sub hseg) (lK gi hgi) (lS gi hgi)
    refine ⟨hA a ham, fun d p off he => ?_⟩
    subst he
    rcases hld d p off ham with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hp, rfl⟩
    · exact ⟨c + off, by rw [h10, ptrAtV_addr], Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨c + 8 + off, by rw [h11, ptrAtV_addr], Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨qt + csKap kv gi, by rw [hp, hp1]; simp only [limb_gpow_addr', ptrAtV_addr, Nat.add_zero],
        Or.inr (Or.inl ⟨by omega, by have := hk30 gi hgi; omega⟩)⟩
  have outF : ∀ a, Stmt.atom a ∈ (csOuts 303 164 0 8 304).1 → a.Holds rd σ ∧ ∀ d p off, a = .load d p off →
      ∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧ CsLoadIn c qt qk i := by
    intro a ha
    obtain ⟨gi, hgi, s', hs', ham, hsub⟩ := mem_csOuts 8 0 304 ha
    rw [Nat.zero_add] at ham hsub
    have hseg : ∀ st ∈ (csOut 303 164 gi s').1, st ∈ csBodyA := fun st h => inO st (hsub st h)
    obtain ⟨hA, hld⟩ := csOut_fwd (S := S) (w := w) hkb ht' hgi (by have := hk30 gi hgi; omega) (by omega)
      (fun b hb => hG b (hseg _ hb)) (hF.sub hseg) (lAg gi hgi) (lOut gi hgi)
    refine ⟨hA a ham, fun d p off he => ?_⟩
    subst he
    rcases hld d p off ham with ⟨rfl, hoff⟩ | ⟨rfl, rfl⟩ | ⟨hp, rfl⟩
    · exact ⟨c + 32 + off, by rw [h303, ptrAtV_addr], Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨c + 24 + off, by rw [h164, ptrAtV_addr], Or.inl ⟨by omega, by omega⟩⟩
    · exact ⟨qt + csKap kv gi, by rw [hp, hp1]; simp only [limb_gpow_addr', ptrAtV_addr, Nat.add_zero],
        Or.inr (Or.inl ⟨by omega, by have := hk30 gi hgi; omega⟩)⟩
  have loadF : ∀ a, Stmt.atom a ∈ csLoads → a.Holds rd σ ∧ ∀ d p off, a = .load d p off →
      ∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧ CsLoadIn c qt qk i := by
    intro a ha
    simp only [csLoads, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false, Stmt.atom.injEq] at ha
    rcases ha with ⟨i, hi, he⟩ | rfl | rfl
    · cases he
      have hm : Stmt.atom (.load (.n (2 + i)) (.n 0) i) ∈ csBodyA := by
        rw [csBodyA_eq]
        refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))))))
        exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
      refine ⟨(good_fresh (hG _ hm) (hF _ _ _ hm (by simp [freshShape]))
        (by rw [hp0]; exact kappaSources_get hks i hi)).2, fun d p off he => ?_⟩
      cases he
      exact ⟨qk + i, by rw [hp0, ptrAtV_addr], Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
    · exact ⟨trivial, fun d p off he => by cases he⟩
    · exact ⟨trivial, fun d p off he => by cases he⟩
  have rankF : ∀ a, Stmt.atom a ∈ csRanks 163 164 165 → a.Holds rd σ ∧ ∀ d p off, a = .load d p off →
      ∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧ CsLoadIn c qt qk i := by
    intro a ha
    obtain ⟨r, hr, hm⟩ := mem_csRanks ha
    obtain ⟨-, -, hA, hld⟩ := hranks r hr
    exact ⟨hA a hm, fun d p off he => by subst he; exact hld d p off hm⟩
  have allF : ∀ a, Stmt.atom a ∈ csBodyA → a.Holds rd σ ∧ ∀ d p off, a = .load d p off →
      ∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧ CsLoadIn c qt qk i := by
    intro a ha
    have hg := hG a ha
    rw [csBodyA_eq] at ha
    simp only [List.mem_append] at ha
    rcases ha with (((((((ha | ha) | ha) | ha) | ha) | ha) | ha))
    · exact loadF a ha
    · exact keyF a ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl <;> exact ⟨trivial, fun d p off he => by cases he⟩
    · exact rankF a ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq, reduceCtorEq, false_or] at ha
      subst ha; exact ⟨trivial, fun d p off he => by cases he⟩
    · exact outF a ha
    · simp only [osCst, osMul, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact ⟨hg, fun d p off he => by cases he⟩
      · exact ⟨hg, fun d p off he => by cases he⟩
      · exact ⟨hg, fun d p off he => by cases he⟩
      · exact ⟨good_mul hg (by omega) (by omega), fun d p off he => by cases he⟩
  exact ⟨fun a ha => (allF a ha).1, h301, fun d p off ha => (allF _ ha).2 d p off rfl⟩

end
end LeanVM.Guest.B1.VsC
