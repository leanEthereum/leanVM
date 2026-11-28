/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.StreamQ

  `VsStreamQ` from `OsCurSpec`: at an honest instance of `verify_sub`, the positions past `stream` of its cursors and
  of its end, and each stream read and run the family places, under its branch conditions, before the end.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_sub.StreamEnd
public import LeanVM.Guest.CoreMode.Fn.verify_sub.StreamVk

/-!
# The stream's reads, by position

`VsPos σ E`: `stream ≠ 0`; `[108] = g^a`, `[460] = g^b`, `[115]·[412] = g^n`; `link_row_side`'s arm `j`
(`σ1070 = g^j`) and `open_stacked`'s `m` (`σ489 = g^m`); `cursor@3 = stream·g^p3`,
`p3 = 16 + 2(a + b) + n·S + 6·S'` (`rowStrides j`); `kb[7] = g^h`, `9 ≤ h ≤ 24`; `cursor@4 = stream·g^p4`,
`p4 = p3 + 144 + 24(h - 3) + 1106` (`verify_keccak`'s words, `vs_c2920x`); the end
`E = p4 + 1 + K`, `osRoom[m] ≤ K`. `vsPos_of`: at every honest instance, given `OsCurSpec`. `streamQ_of_pos`: then
every read and run of `streamCell`, `streamRun` is `stream·g^i`, `i < E`. `vsStreamQ_of : OsCurSpec → VsStreamQ al D`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub LeanVM.Protocol.Verifier
open LeanVM.Guest.CoreMode (CCond CRes CRun CCell prodW vw rep rep_of capE idxC)
open LeanVM.Guest.CoreMode.Own.verify_sub (osRoom lrsRoom armOf streamCell streamRun)

@[expose] public section

/-- **The stream's positions** at a valuation of `verify_sub`, its end at `E`. -/
def VsPos (σ : Val) (E : ℕ) : Prop :=
  ∃ a b n j m K p3 p4 h : ℕ, σ (.n 55) ≠ 0 ∧ σ (.n 108) = gen ^ a ∧ a ≤ 32 ∧ σ (.n 460) = gen ^ b ∧ b ≤ 24 ∧
    σ (.n 115) * σ (.n 412) = gen ^ n ∧ n < 64 ∧ j < 4 ∧ σ (.n 1070) = ofK (addressOfIndex j) ∧ m < 15 ∧
    σ (.n 489) = ofK (addressOfIndex m) ∧
    p3 = 16 + 2 * (a + b) + n * (rowStrides.getD j (0, 0)).1 + 6 * (rowStrides.getD j (0, 0)).2 ∧
    σ (.n 1076) = σ (.n 55) * gen ^ p3 ∧ σ (.n 2920) = σ (.n 55) * gen ^ p4 ∧ σ (.n 120) = gen ^ h ∧ 9 ≤ h ∧
    h ≤ 24 ∧ p4 = p3 + 144 + (24 * (h - 3) + 1106) ∧ osRoom.getD m 0 ≤ K ∧ E = p4 + 1 + K

/-- `verify_sub`'s atoms the positions read. -/
def vsPosAtoms : List Atom :=
  [.rangeCheck (.n 108) (.n 109) (.n 110) (.n 111) (.n 106), .const (.n 106) (word (2 ^ 32) 0),
    .rangeCheck (.n 460) (.n 461) (.n 462) (.n 463) (.n 459), .const (.n 459) (word (2 ^ 24) 0),
    .const (.n 107) (word 2 0), .mul (.n 101) (.n 108) (.n 107), .mul (.n 409) (.n 460) (.n 101),
    .mul (.n 408) (.n 412) (.n 115), .load (.n 57) (.n 55) 0, .mul (.n 3996) (.n 4009) (.n 55)]

end

public section

theorem vs_pos_atoms : vsPosAtoms.all (fun a ↦ (Res.topAtoms (fn% «verify_sub»).body).contains a) = true := by
  decide +kernel

theorem ofK_aoi_inj {a b : ℕ} (ha : a < 64) (hb : b < 64)
    (h : ofK (addressOfIndex a) = ofK (addressOfIndex b)) : a = b :=
  Digest.gen_pow_inj' (by omega) (by omega) (by rw [Value.gen_pow_eq_ofK, Value.gen_pow_eq_ofK]; exact h)

/-- The selector of an arm among the branch conditions. -/
theorem armOf_holds {g : List CCond} {σ : Val} {x j : ℕ} (hg : ∀ y ∈ g, y.Holds σ) (h : armOf g x = some j) :
    σ (.n x) = ofK (addressOfIndex j) := by
  obtain ⟨c, hc, hf⟩ := List.exists_of_findSome?_eq_some h
  cases c with
  | arm y j' =>
    simp only at hf
    split_ifs at hf with hy
    cases hf
    subst hy
    exact hg _ hc
  | zero _ => simp at hf
  | nonzero _ => simp at hf

theorem cellW {w : ℕ → E} {bs : List (ℕ × ℕ)} {o : ℕ} :
    CCell.valW w ⟨bs, o⟩ = prodW w bs * gen ^ o := by
  simp only [CCell.valW]; rw [Value.gen_pow_eq_ofK]

theorem rep_gen {x : E} {z : ℕ} (hx : x = gen ^ z) (hz : z < 2 ^ 34) : rep x = some z := by
  rw [hx, Value.gen_pow_eq_ofK, rep_of (by unfold capE; omega)]

/-- `open_stacked`'s reads past `cursor@4`: at least `103`. -/
theorem osRoom_ge : ∀ m < 15, 103 ≤ osRoom.getD m 0 := by decide

/-- The row side's reads past its rows lie before its end, its strides the contract's. -/
theorem lrsRoom_ok : ∀ j < 4, (lrsRoom.getD j (0, 0)).1 = (rowStrides.getD j (0, 0)).1 ∧
    (lrsRoom.getD j (0, 0)).2 < 16 + 6 * (rowStrides.getD j (0, 0)).2 := by decide

/-- **Every stream read and run of the family lies before the end**, at its positions. -/
theorem streamQ_of_pos {σ : Val} {E : ℕ} (P : VsPos σ E) (g : List CCond) (hg : ∀ x ∈ g, x.Holds σ) :
    (∀ c, streamCell g c = true → ∃ i < E, c.addrW (vw σ) = (σ (.n 55) * gen ^ i).limb 0) ∧
      ∀ q, streamRun g q = true → ∀ x, q.Set (vw σ) x → ∃ i < E, x = (σ (.n 55) * gen ^ i).limb 0 := by
  obtain ⟨a, b, n, j, m, K, p3, p4, hh, -, h108, ha, h460, hb, hn, hn64, hj, h1070, hm, h489, hp3, h1076, h2920,
    h120, hh9, hh24, h34, hK, rfl⟩ := P
  have hK103 : 103 ≤ K := le_trans (osRoom_ge m hm) hK
  set s := σ (.n 55)
  have hS := lrsRoom_ok j hj
  -- the row side's arm among the conditions is `j`
  have arm1070 : ∀ a', armOf g 1070 = some a' → a' < 4 → a' = j := fun a' h h4 ↦
    ofK_aoi_inj (by omega) (by omega) ((armOf_holds hg h).symm.trans h1070)
  have arm489 : ∀ m', armOf g 489 = some m' → m' < 15 → m' = m := fun m' h h15 ↦
    ofK_aoi_inj (by omega) (by omega) ((armOf_holds hg h).symm.trans h489)
  have w2 : prodW (vw σ) [(55, 1), (108, 2), (460, 2)] = s * gen ^ (2 * a + 2 * b) := by
    simp only [prodW, vw, h108, h460, pow_one, mul_one]; ring
  have wrow : ∀ S, prodW (vw σ) [(55, 1), (108, 2), (115, S), (412, S), (460, 2)] =
      s * gen ^ (2 * a + 2 * b + n * S) := by
    intro S
    simp only [prodW, vw, h108, h460, pow_one, mul_one]
    rw [show s * ((gen ^ a) ^ 2 * (σ (.n 115) ^ S * (σ (.n 412) ^ S * (gen ^ b) ^ 2))) =
      s * ((gen ^ a) ^ 2 * ((σ (.n 115) * σ (.n 412)) ^ S * (gen ^ b) ^ 2)) by ring, hn]
    ring
  obtain ⟨hL1, hL2⟩ := hS
  set S := (rowStrides.getD j (0, 0)).1
  set S' := (rowStrides.getD j (0, 0)).2
  refine ⟨fun ⟨bs, o⟩ hc ↦ ?_, fun ⟨⟨bs, o⟩, St, lo, hi⟩ hq x hx ↦ ?_⟩
  · have key : ∀ p, prodW (vw σ) bs * gen ^ o = s * gen ^ p → p < p4 + 1 + K →
        ∃ i < p4 + 1 + K, CCell.addrW (vw σ) ⟨bs, o⟩ = (s * gen ^ i).limb 0 :=
      fun p hp hpE ↦ ⟨p, hpE, by rw [CCell.addrW, cellW, hp]⟩
    simp only [streamCell, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ((⟨rfl, ho⟩ | ⟨rfl, ho⟩) | hc) | hc
    · -- the link's sent values and slices, at `cursor@3`
      simp only [Nat.blt_eq] at ho
      exact key (p3 + o) (by simp only [prodW, vw, pow_one, mul_one, h1076]; ring) (by omega)
    · rcases ho with ho | ho
      · -- the ring switch's nonce, at `cursor@4`
        simp only [Nat.beq_eq] at ho
        subst ho
        exact key p4 (by simp only [prodW, vw, pow_one, mul_one, pow_zero, h2920]) (by omega)
      · -- `open_stacked`'s words
        cases hA : armOf g 489 with
        | none => simp [hA] at ho
        | some m' =>
          simp only [hA, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ho
          obtain ⟨⟨h1, h2⟩, h3⟩ := ho
          obtain rfl := arm489 m' hA h3
          exact key (p4 + o) (by simp only [prodW, vw, pow_one, mul_one, h2920]; ring) (by omega)
    · -- `link_rounds`' returned cursor
      simp only [CCell.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact key (2 * a + 2 * b + 15) (by rw [w2]; ring) (by omega)
    · -- the words past the row side's rows
      cases hB : armOf g 1070 with
      | none => simp [hB] at hc
      | some a' =>
        simp only [hB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨h4, rfl⟩, h16⟩, hK'⟩ := hc
        obtain rfl := arm1070 a' hB h4
        refine key (2 * a + 2 * b + n * (lrsRoom.getD a' (0, 0)).1 + o) (by rw [wrow]; ring) ?_
        rw [hL1]
        generalize n * S = N at *
        omega
  · simp only [CRun.Set, CoreMode.RunSet] at hx
    obtain ⟨ylo, yhi, i, -, hhi, -, hiy, rfl⟩ := hx
    simp only [streamRun, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hq
    rcases hq with (⟨⟨⟨⟨rfl, ho⟩, rfl⟩, rfl⟩, rfl⟩ | hq) | hq
    swap
    · -- `verify_keccak`'s words, its residue runs at `cursor@3·g^144`
      simp only [Nat.ble_eq, Nat.blt_eq] at hq
      obtain ⟨⟨⟨⟨⟨rfl, ho1⟩, ho2⟩, rfl⟩, rfl⟩, rfl⟩ := hq
      have e : (idxC (.mono ⟨[(120, 1)], 44⟩)).valW (vw σ) = gen ^ (hh + 44) := by
        show CCell.valW (vw σ) ⟨[(120, 1)], 44⟩ = _
        rw [cellW]; simp only [prodW, vw, pow_one, mul_one, h120]; ring
      rw [e, rep_gen rfl (by omega), Option.some.injEq] at hhi
      subst hhi
      refine ⟨p3 + o + 24 * i, by omega, ?_⟩
      rw [cellW, ← Value.gen_pow_eq_ofK]
      simp only [prodW, vw, pow_one, mul_one, h1076]
      refine congrArg (fun z : E ↦ z.limb 0) ?_
      ring
    · -- `link_rounds`' words
      have e : (idxC (.mono ⟨[(108, 1), (460, 1)], 1⟩)).valW (vw σ) = gen ^ (a + b + 1) := by
        show CCell.valW (vw σ) ⟨[(108, 1), (460, 1)], 1⟩ = _
        rw [cellW]; simp only [prodW, vw, pow_one, mul_one, h108, h460]; ring
      rw [e, rep_gen rfl (by omega), Option.some.injEq] at hhi
      subst hhi
      refine ⟨o + 2 * i, by omega, ?_⟩
      rw [cellW, ← Value.gen_pow_eq_ofK]
      simp only [prodW, vw, pow_one, mul_one]
      rw [mul_assoc, ← pow_add]
    · -- the row side's rows
      cases hB : armOf g 1070 with
      | none => simp [hB] at hq
      | some a' =>
        simp only [hB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, decide_eq_true_eq, Nat.beq_eq] at hq
        obtain ⟨⟨⟨⟨⟨⟨h4, rfl⟩, rfl⟩, h16⟩, hlt⟩, rfl⟩, rfl⟩ := hq
        obtain rfl := arm1070 a' hB h4
        rw [hL1] at hlt ⊢
        have e : (idxC (.mono ⟨[(115, 1), (412, 1)], 0⟩)).valW (vw σ) = gen ^ n := by
          show CCell.valW (vw σ) ⟨[(115, 1), (412, 1)], 0⟩ = _
          rw [cellW]; simp only [prodW, vw, pow_one, mul_one, pow_zero, hn]
        rw [e, rep_gen rfl (by omega), Option.some.injEq] at hhi
        subst hhi
        refine ⟨2 * a + 2 * b + o + S * i, ?_, ?_⟩
        · have hSi : S * (i + 1) ≤ S * n := Nat.mul_le_mul_left S (by omega)
          rw [Nat.mul_add, mul_comm S n] at hSi
          generalize n * S = N at *
          generalize S * i = M at *
          omega
        · rw [cellW, ← Value.gen_pow_eq_ofK, w2]
          rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
          ring_nf

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

theorem rowStrides_le : ∀ j < 4, (rowStrides.getD j (0, 0)).1 ≤ 12 ∧ (rowStrides.getD j (0, 0)).2 ≤ 11 := by
  decide

/-- **The positions at an honest instance**, its end `4009 = g^E0`. -/
theorem vsPos_of (hOs : OsCurSpec) (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r)
    {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «verify_sub» σ bufs kids) :
    ∃ E0 < 2 ^ 34, VsPos σ E0 ∧ σ (.n 4009) = gen ^ E0 := by
  obtain ⟨rets, R⟩ := vsRun_honest hR hr hI ht
  have hm := ref_memOkA hR hr
  obtain ⟨args, rets', hv⟩ := inst_validA hR hI ht
  obtain ⟨fn', hf', -, es, vs, hw, -, hh, -⟩ := hv
  obtain rfl : fn% «verify_sub» = fn' := Option.some.inj (find_vs.symm.trans hf')
  have hall : ∀ a ∈ Res.topAtoms (fn% «verify_sub»).body, a.Holds r.img.read σ :=
    fun a ha ↦ hh _ (topAtoms_on_path hw ha)
  have H : ∀ a ∈ vsPosAtoms, a.Holds r.img.read σ := fun a ha ↦
    hall a (List.contains_iff_mem.mp (List.all_eq_true.mp vs_pos_atoms a ha))
  have a0 := H (.rangeCheck (.n 108) (.n 109) (.n 110) (.n 111) (.n 106)) (by simp [vsPosAtoms])
  have a1 := H (.const (.n 106) (word (2 ^ 32) 0)) (by simp [vsPosAtoms])
  have a2 := H (.rangeCheck (.n 460) (.n 461) (.n 462) (.n 463) (.n 459)) (by simp [vsPosAtoms])
  have a3 := H (.const (.n 459) (word (2 ^ 24) 0)) (by simp [vsPosAtoms])
  have a4 := H (.const (.n 107) (word 2 0)) (by simp [vsPosAtoms])
  have a5 := H (.mul (.n 101) (.n 108) (.n 107)) (by simp [vsPosAtoms])
  have a6 := H (.mul (.n 409) (.n 460) (.n 101)) (by simp [vsPosAtoms])
  have a7 := H (.mul (.n 408) (.n 412) (.n 115)) (by simp [vsPosAtoms])
  have a8 := H (.load (.n 57) (.n 55) 0) (by simp [vsPosAtoms])
  have a9 := H (.mul (.n 3996) (.n 4009) (.n 55)) (by simp [vsPosAtoms])
  simp only [Atom.Holds] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  obtain ⟨a, ha, h108⟩ := Digest.rc_const hm (c := 32) (by norm_num)
    (a1.trans (word_two_pow (a := 32) (by norm_num))) a0
  obtain ⟨b, hb, h460⟩ := Digest.rc_const hm (c := 24) (by norm_num)
    (a3.trans (word_two_pow (a := 24) (by norm_num))) a2
  have hs : σ (.n 55) ≠ 0 := ne_zero_of_load (by have := hr.log; omega) r.img a8
  have c580 := vs_c580 R
  obtain ⟨w, hw64, h409, c772⟩ := vs_c772 R
  have hwab : w = a + b + 1 := by
    refine Digest.gen_pow_inj' (by omega) (by omega) ?_
    rw [← h409, a6, a5, a4, h460, h108, word_gen]; ring
  obtain ⟨j, hj, n, hn64, h1070, h408, c1076⟩ := vs_c1076 R
  have hn : σ (.n 115) * σ (.n 412) = gen ^ n := by rw [mul_comm, ← a7, h408]
  obtain ⟨hh, hh9, hh24, h120, c2920⟩ := vs_c2920x R
  obtain ⟨m, hm15, h489, K, hK, hroom, c3996⟩ := vs_cEnd hOs R
  obtain ⟨hS1, hS2⟩ := rowStrides_le j hj
  set S := (rowStrides.getD j (0, 0)).1
  set S' := (rowStrides.getD j (0, 0)).2
  have h1076 : σ (.n 1076) = σ (.n 55) * gen ^ (16 + 2 * (a + b) + n * S + 6 * S') := by
    rw [c1076, c772, c580, hwab]; ring
  have h2920 : σ (.n 2920) = σ (.n 55) * gen ^ (16 + 2 * (a + b) + n * S + 6 * S' + 144 + (24 * (hh - 3) + 1106)) :=
    by rw [c2920, h1076]; ring
  have hnS : n * S ≤ 64 * 12 := Nat.mul_le_mul (by omega) hS1
  refine ⟨16 + 2 * (a + b) + n * S + 6 * S' + 144 + (24 * (hh - 3) + 1106) + 1 + K,
    by rw [show (2 : ℕ) ^ 34 = 17179869184 by norm_num]; omega,
    ⟨a, b, n, j, m, K, _, _, hh, hs, h108, ha, h460, hb, hn, hn64, hj, h1070, hm15, h489, rfl, h1076, h2920, h120,
      hh9, hh24, rfl, hroom, rfl⟩, ?_⟩
  have e : σ (.n 4009) * σ (.n 55) =
      gen ^ (16 + 2 * (a + b) + n * S + 6 * S' + 144 + (24 * (hh - 3) + 1106) + 1 + K) * σ (.n 55) := by
    rw [← a9, c3996, h2920]; ring
  exact mul_right_cancel₀ hs e

/-- **`VsStreamQ` from `open_stacked`'s cursor.** -/
theorem vsStreamQ_of (hOs : OsCurSpec) : VsStreamQ al D := by
  intro r hR hr I hI σ bufs kids ht E hE g hg
  obtain ⟨E0, hE0b, P, hE0⟩ := vsPos_of hOs hR hr hI ht
  have hle : E0 ≤ E := by
    by_contra hlt
    exact hlt (le_of_eq (Digest.gen_pow_inj' hE0b (by omega) (hE0.symm.trans hE)))
  obtain ⟨h1, h2⟩ := streamQ_of_pos P g hg
  refine ⟨fun c hc ↦ ?_, fun q hq x hx ↦ ?_⟩
  · obtain ⟨i, hi, e⟩ := h1 c hc
    exact ⟨i, by omega, e⟩
  · obtain ⟨i, hi, e⟩ := h2 q hq x hx
    exact ⟨i, by omega, e⟩

end

end LeanVM.Guest.EndExec
