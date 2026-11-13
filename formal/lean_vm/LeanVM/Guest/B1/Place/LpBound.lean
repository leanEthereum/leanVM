/-
  LeanVM.Guest.B1.Place.LpBound

  A words bound of `level_positions`' trees bounds its placed words, frames below `2^32`.
-/

module

public import LeanVM.Guest.B1.Place.LpProof
public import LeanVM.Guest.B1.Place.Fresh
public import LeanVM.Guest.B1.Place.ArmKids
public import LeanVM.Guest.B1.Whir.DataSpec
public import LeanVM.Guest.B1.Whir.HelperAll

/-!
# `level_positions` within a words bound

`relAtIn_le`: a placed tree on some memory is a valid tree, so a words bound of the function's
trees (`TotalLe`) bounds its words. `lp_bound`: with every frame below `2^32`, `level_positions`
placed after a fresh window table, positions and window pointers holds on a fresh memory
(`fresh_exists`), so `lpN ≤ B`. `level_positions_completeAtB`: every entry is `LpAtO` at `some B`
for every such `B`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A words bound of a function's trees bounds a placed tree's words.** -/
theorem relAtIn_le {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtIn coreProgram fs cert rd R D fp n f args rets) {B : ℕ}
    (hT : TotalLe coreProgram fs f (fun _ ↦ B)) : n ≤ B := by
  obtain ⟨t, hn, hv, hb, -, ht, -⟩ := h
  rw [← ht]
  exact hT rd t args rets hn hv hb

/-- Two layouts, one below `b` and one within `[b, b + n)`, disjoint and below the order of `g`. -/
theorem fresh_pair (κ : ℕ) {L Lin : Layout} {b n : ℕ} (hd : DisjL L) (hw : Within L b n)
    (hd' : DisjL Lin) (hw' : Within Lin 0 b) (hlt : b + n < 2 ^ 64 - 1) :
    ∃ rd, LowDef κ rd ∧ MemL rd (L ++ Lin) := by
  refine fresh_exists κ ?_ fun q hq ↦ ?_
  · refine List.pairwise_append.mpr ⟨hd, hd', fun a ha c hc ↦ Or.inr ?_⟩
    have := hw a ha
    have := hw' c hc
    omega
  · rcases List.mem_append.mp hq with hq | hq
    · have := hw q hq; omega
    · have := hw' q hq; omega

theorem lpN_lt {name loop : String} {S d cd : ℕ} (hfs : ∀ f, fs f < 2 ^ 32) (hS : S ≤ 64) :
    lpN fs name loop S d cd < 2 ^ 40 := by
  unfold lpN sqTot
  have h1 := hfs name
  have h2 := hfs (dqwName d cd)
  have h3 := hfs loop
  have h4 := hfs (sqDecName (lpLvP d cd))
  have e1 : (S - 1 - 0 + 1) * fs loop ≤ 64 * 2 ^ 32 := Nat.mul_le_mul (by omega) h3.le
  have e2 : (S - 1 - 0) * fs (sqDecName (lpLvP d cd)) ≤ 64 * 2 ^ 32 := Nat.mul_le_mul (by omega) h4.le
  omega

set_option maxHeartbeats 800000 in
/-- **A words bound of `level_positions`' trees bounds `lpN`**, frames below `2^32`. -/
theorem lp_bound (κ : ℕ) {name loop : String} {S d cd : ℕ}
    (hlp : FnIs name (osParams 9) (lpBody S d cd loop))
    (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop)) (hS : 0 < S) (hSo : S < ordG) (hSB : S ≤ 64)
    (hpw : digitsVal (osPowDigits (128 / d)) 1 = 128 / d)
    (hdec : QwDecodeAtD fs cert κ d cd (dqwName d cd)) (hfs : ∀ f, fs f < 2 ^ 32) {B : ℕ}
    (hT : TotalLe coreProgram fs name (fun _ ↦ B)) : lpN fs name loop S d cd ≤ B := by
  set Q := 128 / d with hQ
  set M := S * Q with hM
  have hQle : Q ≤ 128 := Nat.div_le_self _ _
  have hMle : M ≤ 64 * 128 := Nat.mul_le_mul hSB hQle
  set cap : List E := [0, 0, 0, 0, 0] with hcap
  set fp0 := 2048 + 2 * M with hfp0
  set tabW : List E := (List.range 2048).map eOfNat with htabW
  set posW : List E := (List.range M).map fun k ↦ eOfNat (qwPosOf d (sqSample 0 cap (k / Q)) (k % Q))
    with hposW
  set ptrW : List E := (List.range M).map fun k ↦
    qwPtrAt cert (dqwName d cd) (lpDecPos fs name loop S d cd fp0 (k / Q)) d cd (k % Q) with hptrW
  set Lin0 : Layout := [(0, tabW), (2048, posW), (2048 + M, ptrW)] with hLin0
  have hLW : Within Lin0 0 fp0 := by
    intro q hq
    simp only [hLin0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp [htabW, hposW, hptrW] <;> omega
  have hlT : tabW.length = 2048 := by simp [htabW]
  have hlP : posW.length = M := by simp [hposW]
  have hlR : ptrW.length = M := by simp [hptrW]
  have hLD : DisjL Lin0 := by
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons
      (fun _ h ↦ absurd h List.not_mem_nil) .nil))
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · left; simp only [hlT]; omega
      · left; simp only [hlT]; omega
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      left; simp only [hlP]; omega
  have hmemQ : ∀ j < S, ∀ i < Q, j * Q + i < M := fun j hj i hi ↦ by
    have := Nat.mul_le_mul_right Q (show j + 1 ≤ S by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hdm : ∀ j < S, ∀ i < Q, (j * Q + i) / Q = j ∧ (j * Q + i) % Q = i := fun j _ i hi ↦ by
    have hQ0 : 0 < Q := by omega
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ0, Nat.div_eq_of_lt hi, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  obtain ⟨Lown, hW, hD, hR⟩ := lp_placed fs cert κ hlp hl hS hSo hSB hpw hdec
    (w0 := 0) (cap := cap) (ep := 2048) (ew := 2048 + M) (tabs := ofK (addressOfIndex 0))
    (Lin := Lin0) rfl fp0
    (fun k hk ↦ ⟨⟨(2048, posW), by simp [hLin0], Nat.le_add_right _ _, by rw [hlP]; exact Nat.add_lt_add_left hk _⟩,
      ⟨(2048 + M, ptrW), by simp [hLin0], Nat.le_add_right _ _, by rw [hlR]; exact Nat.add_lt_add_left hk _⟩⟩)
    (fun t ht ↦ ⟨t, by rw [Main.addr_ofK, Nat.zero_add],
      ⟨(0, tabW), by simp [hLin0], by omega, by rw [hlT]; omega⟩⟩)
    (fun rd _ hm ↦ by
      have hT0 := hm (0, tabW) (by simp [hLin0])
      have hP0 := hm (2048, posW) (by simp [hLin0])
      have hW0 := hm (2048 + M, ptrW) (by simp [hLin0])
      refine ⟨fun n hn ↦ ?_, fun j hj i hi ↦ ⟨?_, ?_⟩⟩
      · have h := hT0 n (by simp [htabW]; norm_num [winTabBits] at hn; omega)
        simpa [htabW] using h
      · have h := hP0 (j * Q + i) (by simp [hposW]; exact hmemQ j hj i hi)
        simp only [hposW, List.getElem_map, List.getElem_range, (hdm j hj i hi).1,
          (hdm j hj i hi).2] at h
        exact h
      · have h := hW0 (j * Q + i) (by simp [hptrW]; exact hmemQ j hj i hi)
        simp only [hptrW, List.getElem_map, List.getElem_range, (hdm j hj i hi).1,
          (hdm j hj i hi).2] at h
        exact h)
  have hlt := lpN_lt (name := name) (loop := loop) (d := d) (cd := cd) hfs hSB
  obtain ⟨rd, hlow, hm⟩ := fresh_pair κ hD hW hLD hLW (by omega)
  exact relAtIn_le (hR rd hlow hm) hT

/-- **`level_positions` within every words bound of its trees**, frames below `2^32`. -/
theorem level_positions_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (hfit : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 7 ≤ κ)
    (hfs : ∀ f, fs f < 2 ^ 32) :
    ∀ e ∈ lpTable, ∀ B, TotalLe coreProgram fs e.1 (fun _ ↦ B) →
      Arm.LpAtO fs cert κ e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2 (some B) := by
  intro e he B hT
  obtain ⟨hlp, hl⟩ := lpTable_ok e he
  obtain ⟨hS, hSo, hSB, hpw, hmem⟩ := lpTable_facts e he
  have hdec := qwDecodeAtD_holds hfit hcons hκ _ hmem
  have hb := lp_bound κ hlp hl hS hSo hSB hpw hdec hfs hT
  intro w0 cap ep ew tabs Lin hcl hreg hregt hmemL fp
  obtain ⟨Lown, hW, hD, hR⟩ := lp_placed fs cert κ hlp hl hS hSo hSB hpw hdec hcl fp
    (fun k hk ↦ hreg fp k hk) (hregt fp) (fun rd hlow hm ↦ hmemL fp rd hlow hm)
  exact ⟨lpN fs e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2, Lown, hW, hD,
    fun B' hB' ↦ by cases hB'; exact hb, hR⟩

end
end LeanVM.Guest.B1
