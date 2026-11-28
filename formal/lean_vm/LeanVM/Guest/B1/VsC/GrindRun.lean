/-
  LeanVM.Guest.B1.VsC.GrindRun

  `grind_check` inlined with folded tables, as atoms of a run window: what `RunHyp` asks of them.
-/

module

public import LeanVM.Guest.B1.VsC.WinGen
public import LeanVM.Guest.B1.VsC.RoundsC1

/-!
# The inlined grind in a run window

`gcInlineOT b o off w tabs` (`GrindFwd.lean`), at any deployed `b`: on a valuation satisfying its statements'
equations (`GoodS`), the oracle's windows the honest ones (`gcWin`), no store into its values, the bit-window table at
`tabs·g^off` on the evaluation memory (defined on its first `2^k` words, `11 ≤ k`) and the word passing the proof of
work, each atom meets what a run window asks (`gcO_atoms`, `GcAtomOk`): its `PureF` (the windows' range checks low,
the final split in `K`), its `MemF` on every memory holding the table, and each load a table word `tabs·g^e`,
`e < 2^11`, at offset `off`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- A range check's complement: `wBound T = g^e·y` with `e < 2^T` makes `y = g^(2^T - 1 - e)`. -/
theorem rc_compl {T e : ℕ} {y : E} (hT : T ≤ 11) (he : e < 2 ^ T) (h : wBound T = gen ^ e * y) :
    y = gen ^ (2 ^ T - 1 - e) := by
  rw [wBound_eq hT, show 2 ^ T - 1 = e + (2 ^ T - 1 - e) by omega, pow_add] at h
  exact (mul_left_cancel₀ (pow_ne_zero _ Value.gen_ne_zero) h).symm

/-- A forward product asks nothing. -/
theorem pureF_mul_fwd {k : ℕ} {σ : Val} {d x y : V} (h : x.idx < d.idx ∧ y.idx < d.idx) :
    PureF k σ (.mul d x y) := by
  show (if x.idx < d.idx ∧ y.idx < d.idx then True else σ y ≠ 0)
  split
  · trivial
  · contradiction

/-- **What a run window asks of an atom of the inlined grind**: its pure side condition, its word on every memory
holding the bit-window table at `t·g^off`, and a load's pointer a table word `t·g^e`, `e < 2^11`, at `off`. -/
def GcAtomOk (k : ℕ) (σ : Val) (t : E) (off : ℕ) (a : Atom) : Prop :=
  PureF k σ a ∧ (∀ rd, WinTabs rd (t * gen ^ off) → MemF rd σ a) ∧
    ∀ d p off', a = .load d p off' → off' = off ∧ ∃ e < 2 ^ 11, σ p = t * gen ^ e

theorem gcAtomOk_of_quiet {k : ℕ} {σ : Val} {t : E} {off : ℕ} {a : Atom} (hp : PureF k σ a)
    (hm : ∀ rd, MemF rd σ a) (hl : ∀ d p off', a ≠ .load d p off') : GcAtomOk k σ t off a :=
  ⟨hp, fun rd _ => hm rd, fun d p off' h => absurd h (hl d p off')⟩

section
variable {rd0 : Reader} {S : List Atom} {wo : ℕ → E} {σ : Val}

/-- **The inlined grind's atoms meet a run window's asks**, at any deployed `b`. -/
theorem gcO_atoms {k b o off : ℕ} (hk : 11 ≤ k) (hb : b ∈ grindBitsDeployed) {wv tabs : V}
    (hwo : wv.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineOT b o off wv tabs, GoodS rd0 S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false) (hl0 : LowDef k rd0)
    (ht : WinTabs rd0 (σ tabs * gen ^ off)) (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ wv) j)
    (hlow : ((σ wv).limb 0).lane.toNat % 2 ^ b = 0) :
    ∀ a ∈ atomsOf (gcInlineOT b o off wv tabs), GcAtomOk k σ (σ tabs) off a := by
  have hrc := hrc_of_lowDef hl0 hk
  have hv := gcInlineO_vals_of_good hb hwo hto hg hS hrc ht hwin
  obtain ⟨hT1, hT, hsum⟩ := gc_shape b hb
  have hW1 := gcW_pos b hb
  have hlen : gcLen b = 10 * gcW b + 16 := rfl
  have hR : ∀ j, 2 ≤ j → j < gcLen b → σ (gcRen o wv tabs (.n j)) = gcVals rd0 b (σ wv) (σ tabs) j :=
    fun j h2 hj ↦ by rw [gcRen_own o wv tabs h2]; exact hv j h2 hj
  have rlt : ∀ x d, x < d → 2 ≤ d → (gcRen o wv tabs (.n x)).idx < (gcRen o wv tabs (.n d)).idx := by
    intro x d hx hd
    rw [gcRen_own o wv tabs hd]
    rcases Nat.lt_or_ge x 2 with h2 | h2
    · rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
      · rw [gcRen_word]; show wv.idx < o + d - 2; omega
      · rw [gcRen_tabs]; show tabs.idx < o + d - 2; omega
    · rw [gcRen_own o wv tabs h2]; show o + x - 2 < o + d - 2; omega
  have fwd : ∀ d x y, x < d → y < d → 2 ≤ d →
      PureF k σ (.mul (gcRen o wv tabs (.n d)) (gcRen o wv tabs (.n x)) (gcRen o wv tabs (.n y))) :=
    fun d x y hx hy hd ↦ pureF_mul_fwd ⟨rlt x d hx hd, rlt y d hy hd⟩
  have low : ∀ m, m < 2 ^ 11 → LowW k (gen ^ m) := fun m hm ↦
    ⟨m, lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hk), rfl⟩
  have hV0 := gcV_zero_lt hsum (σ wv)
  have hV0' : gcV b (σ wv) 0 < 2 ^ 11 := lt_of_lt_of_le hV0 (Nat.pow_le_pow_right (by decide) hT)
  -- the tail's split
  have hlow' : kToNat ((σ wv).limb 0) % 2 ^ b = 0 := hlow
  have hVW : 2 ^ b * gcV b (σ wv) (gcW b) = kToNat ((σ wv).limb 0) := by
    unfold gcV
    rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow')
  have hL : eOfNat (gcV b (σ wv) (gcW b)) * word (2 ^ b) 0 = ofK ((σ wv).limb 0) := by
    rw [word_eOfNat, mul_comm, eOfNat_two_pow_mul (by rw [hVW]; exact kToNat_lt _), hVW, eOfNat, ofBits_kToNat]
  have hsp := (split_iff (σ wv) (ofK ((σ wv).limb 0))).mpr rfl
  intro a ha
  obtain ⟨s0, hs0, e0⟩ := renameList_mem_inv (mem_of_mem_atomsOf ha)
  simp only [gcPreO, gcHeadO, gcTailPre, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_range] at hs0
  rcases hs0 with (hs0 | ⟨l, ⟨i, hi, rfl⟩, hs0⟩) | hs0
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Stmt.rename, Stmt.atom.injEq] at e0 <;> subst e0
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
    · -- the top window's range check
      refine gcAtomOk_of_quiet ?_ (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
      obtain ⟨y, t1, t2, r1, r2, r3⟩ := hrc _ hT _ hV0
      have c := rcWit_spec (rd := rd0) ⟨y, t1, t2, r1, r2, r3⟩
      have e4 : gcVals rd0 b (σ wv) (σ tabs) (gcW b + 4) =
          (rcWit rd0 (gen ^ gcV b (σ wv) 0) (wBound (gcTop b))).1 := by
        unfold gcVals
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left rfl]
      show LowW k (σ (gcRen o wv tabs (.n (gcW b + 2)))) ∧ LowW k (σ (gcRen o wv tabs (.n (gcW b + 4))))
      rw [hR (gcW b + 2) (by omega) (by rw [hlen]; omega), hR (gcW b + 4) (by omega) (by rw [hlen]; omega), gv_top, e4,
        rc_compl hT hV0 c.2.1]
      have p1 := Nat.one_le_two_pow (n := gcTop b)
      have p2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hT
      exact ⟨low _ hV0', low _ (by omega)⟩
    · exact gcAtomOk_of_quiet (fwd _ _ _ (by omega) (by omega) (by omega)) (fun _ => trivial)
        (fun _ _ _ h => by simp [Atom.rename] at h)
    · -- the top window's table read
      have ep : σ (gcRen o wv tabs (.n (gcW b + 7))) = σ tabs * gen ^ gcV b (σ wv) 0 := by
        rw [hR (gcW b + 7) (by omega) (by rw [hlen]; omega), gv_top_ptr]
      have ed : σ (gcRen o wv tabs (.n (gcW b + 8))) = eOfNat (gcV b (σ wv) 0) := by
        rw [hR (gcW b + 8) (by omega) (by rw [hlen]; omega), show gcW b + 8 = gcW b + 9 * 0 + 8 by ring]
        exact gv_acc (i := 0) (by omega)
      refine ⟨trivial, fun rd hrd => ?_, fun d p off' h => ?_⟩
      · show LoadHolds rd (σ (gcRen o wv tabs (.n (gcW b + 7)))) off (σ (gcRen o wv tabs (.n (gcW b + 8))))
        rw [ep, ed]; exact winTab_loadO hrd hV0'
      · simp only [Atom.rename, Atom.load.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact ⟨rfl, _, hV0', ep⟩
  · -- step `i + 1`
    have h1 : 1 ≤ i + 1 := by omega
    have h2 : i + 1 ≤ gcW b := by omega
    have hwin' : gcV b (σ wv) (i + 1) % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by positivity)
    simp only [gcIterAtO, List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Stmt.rename, Stmt.atom.injEq] at e0 <;> subst e0
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
    · -- the window's range check
      refine gcAtomOk_of_quiet ?_ (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
      obtain ⟨y, t1, t2, r1, r2, r3⟩ := hrc 11 le_rfl _ hwin'
      have c := rcWit_spec (rd := rd0) ⟨y, t1, t2, r1, r2, r3⟩
      show LowW k (σ (gcRen o wv tabs (.n (gcW b + 2 - (i + 1))))) ∧
        LowW k (σ (gcRen o wv tabs (.n (gcW b + 9 * (i + 1) + 1))))
      rw [hR (gcW b + 2 - (i + 1)) (by omega) (by rw [hlen]; omega), hR (gcW b + 9 * (i + 1) + 1) (by omega) (by rw [hlen]; omega), gv_win h1 h2,
        gv_iter h1 h2 (by omega)]
      show _ ∧ LowW k (rcWit rd0 (gen ^ (gcV b (σ wv) (i + 1) % 2 ^ 11)) (wBound 11)).1
      rw [rc_compl le_rfl hwin' c.2.1]
      exact ⟨low _ hwin', low _ (by omega)⟩
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet (fwd _ _ _ (by omega) (by omega) (by omega)) (fun _ => trivial)
        (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet (fwd _ _ _ (by omega) (by omega) (by omega)) (fun _ => trivial)
        (fun _ _ _ h => by simp [Atom.rename] at h)
    · -- the window's table read
      have ep : σ (gcRen o wv tabs (.n (gcW b + 9 * (i + 1) + 6))) =
          σ tabs * gen ^ (gcV b (σ wv) (i + 1) % 2 ^ 11) := by
        rw [hR (gcW b + 9 * (i + 1) + 6) (by omega) (by rw [hlen]; omega), gv_iter h1 h2 (by omega)]; rfl
      have ed : σ (gcRen o wv tabs (.n (gcW b + 9 * (i + 1) + 7))) = eOfNat (gcV b (σ wv) (i + 1) % 2 ^ 11) := by
        rw [hR (gcW b + 9 * (i + 1) + 7) (by omega) (by rw [hlen]; omega), gv_iter h1 h2 (by omega)]; rfl
      refine ⟨trivial, fun rd hrd => ?_, fun d p off' h => ?_⟩
      · show LoadHolds rd (σ (gcRen o wv tabs (.n (gcW b + 9 * (i + 1) + 6)))) off
          (σ (gcRen o wv tabs (.n (gcW b + 9 * (i + 1) + 7))))
        rw [ep, ed]; exact winTab_loadO hrd hwin'
      · simp only [Atom.rename, Atom.load.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact ⟨rfl, _, hwin', ep⟩
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Stmt.rename, Stmt.atom.injEq] at e0 <;> subst e0
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet (fwd _ _ _ (by omega) (by omega) (by omega)) (fun _ => trivial)
        (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet (fwd _ _ _ (by omega) (by omega) (by omega)) (fun _ => trivial)
        (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet trivial (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
    · exact gcAtomOk_of_quiet (fwd _ _ _ (by omega) (by omega) (by omega)) (fun _ => trivial)
        (fun _ _ _ h => by simp [Atom.rename] at h)
    · -- the final split
      refine gcAtomOk_of_quiet ?_ (fun _ => trivial) (fun _ _ _ h => by simp [Atom.rename] at h)
      show IsInK (σ (gcRen o wv tabs (.n (10 * gcW b + 13)))) ∧ IsInK (σ (gcRen o wv tabs (.n (10 * gcW b + 15))))
      rw [hR (10 * gcW b + 13) (by omega) (by rw [hlen]; omega), hR (10 * gcW b + 15) (by omega) (by rw [hlen]; omega),
        show 10 * gcW b + 13 = 10 * gcW b + 9 + 4 by omega, show 10 * gcW b + 15 = 10 * gcW b + 9 + 6 by omega,
        gv_tail, gv_tail]
      show IsInK ((σ wv + eOfNat (gcV b (σ wv) (gcW b)) * word (2 ^ b) 0) * word 2 1) ∧
        IsInK (eOfNat (gcV b (σ wv) (gcW b)) * word (2 ^ b) 0)
      rw [hL, word_y_inv]
      exact ⟨hsp.2, hsp.1⟩

end

end
end LeanVM.Guest.B1.VsC
