/-
  LeanVM.Guest.B1.KeccakGkr.VkIn

  `verify_keccak`'s inputs' opening up to the slices (G:3000-3019).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkOut
public import LeanVM.Guest.B1.KeccakGkr.VkSlices
public import LeanVM.Guest.B1.KeccakGkr.VkOpenMath

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {rd : Reader} {σ : Val}

theorem word_2p39 : word 549755813888 0 = gen ^ 39 := by
  rw [show (549755813888 : ℕ) = 2 ^ 39 from rfl]; exact word_two_pow (by decide)

/-- **The inputs' opening up to the slices** (G:3000-3019). -/
theorem vkInT_holds {τ : ℕ} (h6 : σ (.n 6) = gen ^ τ)
    {c : KeccakClaim} (hc : ClaimRec rd ((0 : ℕ) = 1) (σ (.n 161) * gen ^ (22 * 12)) c (τ - 3))
    (hw : FsPackOk σ (.n 931) (931 + 1) dsObserve)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vkInT next kret) :
    ∃ (mI mS : List (E × E)) (low slotI : List E), mI.length = 4 ∧
      ReadsAt rd (σ (.n 929) * gen) (mI.flatMap fun c ↦ [c.1, c.2]) ∧
      plainRun mI c.value
        ((⟨[σ (.n 924), σ (.n 925), σ (.n 926), σ (.n 927), σ (.n 928)], []⟩ : Fs).absorb
          (σ (.n 931)) dsObserve) =
        (low, σ (.n 1209), ⟨[σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207)], []⟩) ∧
      ReadsAt rd (σ (.n 9) * gen ^ 39) low ∧ σ (.n 1208) = σ (.n 929) * gen * gen ^ 8 ∧
      σ (.n 1327) = multilinearEval c.mu low ∧
      mS.length = 6 ∧ ReadsAt rd (σ (.n 1208)) (mS.flatMap fun c ↦ [c.1, c.2]) ∧
      plainRun mS (σ (.n 1209))
        ⟨[σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207)], []⟩ =
        (slotI, σ (.n 1339),
          ⟨[σ (.n 1333), σ (.n 1334), σ (.n 1335), σ (.n 1336), σ (.n 1337)], []⟩) ∧
      ReadsAt rd (σ (.n 1330)) slotI ∧ σ (.n 1330) = σ (.n 9) * gen ^ 39 * gen ^ τ ∧
      σ (.n 1338) = σ (.n 1208) * gen ^ 12 ∧
      ReadsAt rd (σ (.n 1338)) ((List.range 64).map fun z ↦ σ (.n (slB 1345 z))) ∧
      (∀ z < 64, LoadHolds rd (σ (.n 10)) z (σ (.n (slB 1345 z)))) ∧
      ((⟨[σ (.n 1333), σ (.n 1334), σ (.n 1335), σ (.n 1336), σ (.n 1337)], []⟩ : Fs).absorbAll
        ((List.range 64).map fun z ↦ σ (.n (slB 1345 z))) dsObserve).pend.length = rateScalars ∧
      capOf ((⟨[σ (.n 1333), σ (.n 1334), σ (.n 1335), σ (.n 1336), σ (.n 1337)], []⟩ : Fs).absorbAll
        ((List.range 64).map fun z ↦ σ (.n (slB 1345 z))) dsObserve).perm =
        [σ (.n 1740), σ (.n 1741), σ (.n 1742), σ (.n 1743), σ (.n 1744)] ∧
      σ (.n 1202) = σ (.n 9) * gen ^ 39 ∧ next := by
  obtain ⟨hmuL, hptL, hval, -, hmus, -⟩ := hc
  rw [vkInT] at h
  generalize hEQ : eqtreeT (.n 9) (.n 1210) 39 1211 4 = EQ at h
  generalize hPD : pairsDotT (.n 1210) (.n 161) (consecOffs 14 270 16) 1265 = PD at h
  generalize hSL : slicesT (.n 1338) 1340 1345 = SL at h
  generalize hCP : (List.range 5).map (fun j ↦ Stmt.atom (.copy (.n (1340 + j)) (.n (1333 + j)))) = CP at h
  simp only [holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil] at h
  obtain ⟨e75, e76, l77, e78, e79, hcall1, -, h⟩ := h
  -- the pack's rounds
  obtain ⟨mI, hmL, hmR, hrun⟩ := plain_call (k0 := 1) (n := 4) (by omega) rfl
    (cap := [σ (.n 924), σ (.n 925), σ (.n 926), σ (.n 927), σ (.n 928)]) rfl
    (by simpa [List.range_succ, plainName] using hcall1)
  obtain ⟨hpt1, hrets1⟩ := hrun (σ (.n 931)) (fun _ ↦ fsPackT_cells hw)
  simp only [plainStart, ↓reduceIte] at hpt1 hrets1
  have hval' : σ (.n 1200) = c.value := by
    have := (loadHolds_mul_gen_pow rd _ _ _ _).1 hval
    exact loadHolds_unique l77 (by simpa using this)
  rw [hval'] at hpt1 hrets1
  have hpend1 := plainRun_pend mI c.value
    ⟨[σ (.n 924), σ (.n 925), σ (.n 926), σ (.n 927), σ (.n 928)], [(σ (.n 931), dsObserve)]⟩
    (by rintro rfl; simp at hmL)
  set R1 := plainRun mI c.value
    ⟨[σ (.n 924), σ (.n 925), σ (.n 926), σ (.n 927), σ (.n 928)], [(σ (.n 931), dsObserve)]⟩
    with hR1
  rw [show [σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207), σ (.n 1208),
      σ (.n 1209)] = [σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207)] ++
      [σ (.n 1208), σ (.n 1209)] from rfl] at hrets1
  obtain ⟨hcap1, hlast1⟩ := List.append_inj' hrets1 rfl
  simp only [List.cons.injEq, and_true] at hlast1
  obtain ⟨h3985, h3986⟩ := hlast1
  have hR1s : R1 = (R1.1, σ (.n 1209),
      ⟨[σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207)], []⟩) := by
    rw [h3986, hcap1, ← hpend1]
  have hlowL : R1.1.length = 4 := by rw [hR1, plainRun_length, hmL]
  have h3979 : σ (.n 1202) = σ (.n 9) * gen ^ 39 := by rw [e79, e78, word_2p39]
  -- the low tree and μ at the low point
  rw [← hEQ] at h
  obtain ⟨hlt, h⟩ := eqtreeT_last (rs := R1.1) (n := 4) (by omega) hlowL (fun t ht ↦ by
    have := hpt1 t (by omega)
    rw [h3979, loadHolds_mul_gen_pow] at this
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact this) h
  rw [← hPD] at h
  obtain ⟨hmu, h⟩ := pairsDotT_holds (P := fun i ↦ (eqKernel R1.1).getD i 0)
    (Q := fun i ↦ c.mu.getD i 0) (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some] at hv
      have := hlt k (by norm_num; omega)
      simp only [show 2 ^ 4 - 2 = 14 from rfl] at this
      exact loadHolds_unique hv (by simpa [List.getD_eq_getElem?_getD] using this))
    (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some] at hv
      have := (loadHolds_mul_gen_pow rd _ _ _ _).1 (hmus k (by simp [pack]; omega))
      exact loadHolds_unique hv (by
        rw [List.getD_eq_getElem?_getD] at this ⊢
        simpa [show 22 * 12 + (6 + k) = 270 + k by omega] using this))
    (by simp [consecOffs]) h
  simp only [consecOffs, List.length_map, List.length_range, pairsDotV] at hmu
  have hmle : σ (.n 1327) = multilinearEval c.mu R1.1 := by
    rw [show (1327 : ℕ) = 1265 + 4 * (16 - 1) + 2 from rfl, hmu,
      multilinearEval_eqAt c.mu R1.1 (by simpa [pack] using hmuL) hlowL]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < 16 := Finset.mem_range.1 hi
    rw [eqKernel_getD]
    simp [hlowL, hi']
  -- the slot's rounds
  obtain ⟨e05, e06, e07, -, -, hcall2, h⟩ := h
  obtain ⟨mS, hsL, hsR, hrun2⟩ := plain_call (k0 := 0) (n := 6) (by omega) rfl
    (cap := [σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207)]) rfl
    (by simpa [List.range_succ, plainName] using hcall2)
  obtain ⟨hpt2, hrets2⟩ := hrun2 0 (fun h ↦ absurd h (by decide))
  simp only [plainStart, show ¬ ((0 : ℕ) = 1) by decide, ↓reduceIte] at hpt2 hrets2
  have hpend2 := plainRun_pend mS (σ (.n 1209))
    ⟨[σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207)], []⟩
    (by rintro rfl; simp at hsL)
  set R2 := plainRun mS (σ (.n 1209))
    ⟨[σ (.n 1203), σ (.n 1204), σ (.n 1205), σ (.n 1206), σ (.n 1207)], []⟩ with hR2
  rw [show [σ (.n 1333), σ (.n 1334), σ (.n 1335), σ (.n 1336), σ (.n 1337), σ (.n 1338),
      σ (.n 1339)] = [σ (.n 1333), σ (.n 1334), σ (.n 1335), σ (.n 1336), σ (.n 1337)] ++
      [σ (.n 1338), σ (.n 1339)] from rfl] at hrets2
  obtain ⟨hcap2, hlast2⟩ := List.append_inj' hrets2 rfl
  simp only [List.cons.injEq, and_true] at hlast2
  obtain ⟨h4115, h4116⟩ := hlast2
  have hR2s : R2 = (R2.1, σ (.n 1339),
      ⟨[σ (.n 1333), σ (.n 1334), σ (.n 1335), σ (.n 1336), σ (.n 1337)], []⟩) := by
    rw [h4116, hcap2, ← hpend2]
  -- the copies and the slices
  rw [← hCP, holdsList_map_atoms] at h
  obtain ⟨hcp, h⟩ := h
  simp only [Atom.Holds] at hcp
  rw [← hSL] at h
  obtain ⟨hrs, hst, hpl, hsc, hn⟩ := slicesT_holds h
  have hc5 : (cap5 1340).map σ = [σ (.n 1333), σ (.n 1334), σ (.n 1335), σ (.n 1336), σ (.n 1337)] := by
    simp only [cap5, List.map_cons, List.map_nil]
    rw [hcp 0 (by omega), hcp 1 (by omega), hcp 2 (by omega), hcp 3 (by omega), hcp 4 (by omega)]
  rw [hc5] at hpl hsc
  refine ⟨mI, mS, R1.1, R2.1, hmL, ?_, ?_, ?_, ?_, hmle, hsL, ?_, hR2s, hpt2, ?_, h4115.trans
    (by norm_num), hrs, hst, hpl, by simpa [cap5, slP] using hsc, h3979, hn⟩
  · rw [e76, e75, word_gen] at hmR; exact hmR
  · rw [show (⟨[σ (.n 924), σ (.n 925), σ (.n 926), σ (.n 927), σ (.n 928)], []⟩ : Fs).absorb
      (σ (.n 931)) dsObserve = ⟨[σ (.n 924), σ (.n 925), σ (.n 926), σ (.n 927), σ (.n 928)],
        [(σ (.n 931), dsObserve)]⟩ from rfl]
    exact hR1s
  · rw [← h3979]; exact hpt1
  · rw [h3985, e76, e75, word_gen]
  · exact hsR
  · rw [e07, e06, e05, word_2p39, h6]

end
end LeanVM.Guest.B1.VerifySub
