/-
  LeanVM.Guest.B1.VsC.ColSelA

  `column_selector` completes placed, its loads in the tables its caller hands it.
-/

module

public import LeanVM.Guest.B1.VsC.ColSelCAll
public import LeanVM.Guest.B1.VsC.LeafA
public import LeanVM.Guest.Memory.Straight

/-!
# `column_selector`, placed

`column_selector__L{n}_L{κ}` has no words of its own; placed at frame `fp` and cursor `c` it ends at
`c`. On its forward evaluation (`csel_fwd`) each digit's two loads read the selector tables at
`se` below `32 n` and the nibble shares at `sg` below `144` (`csel_loads`: the pointers are
`se·g^e` and `sg·g^e`, `e` the digit), so they lie in any region holding those words
(`column_selector_placed`). Its range checks read the low words, which `LowDef` covers and
`LoadsInA` does not count.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Stack
open LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem selOff_le (w : ℕ) : selOff w ≤ 16 := by
  unfold selOff; rcases w with _ | _ | _ | _ | w <;> simp

/-- What the kernel checks of `column_selector`'s template for its placed form. -/
def cselOkA (n κ : ℕ) : Bool :=
  (atomsOf (cselBody n κ)).all leafAtomOk && (atomsOf (cselBody n κ)).all (fun a => !atomAllocB a)

theorem cselOkA_all : ∀ n, 4 ≤ n → n ≤ 8 → ∀ κ, κ ≤ 30 → cselOkA n κ = true := by
  have h : ((List.range 5).all fun n => (List.range 31).all fun κ => cselOkA (n + 4) κ) = true := by
    decide +kernel
  intro n h4 h8 κ hκ
  have := List.all_eq_true.mp (List.all_eq_true.mp h (n - 4) (List.mem_range.mpr (by omega))) κ
    (List.mem_range.mpr (by omega))
  rwa [Nat.sub_add_cancel h4] at this

/-- `(p·g^e)·g^o` is `p·g^(e + o)`. -/
theorem limb_gpow_addr (p : E) (e o : ℕ) :
    (p * gen ^ e).limb 0 * addressOfIndex o = p.limb 0 * addressOfIndex (e + o) := by
  rw [gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]

/-- **The loads of `column_selector`'s forward evaluation** read the selector tables at `se` below
`32 n` and the nibble shares at `sg` below `144`. -/
theorem csel_loads {rd : Reader} {n κ idx : ℕ} (hn : n ≤ 8) (hok : cselOk n κ = true) {se sg : E}
    {A : K} (hA : A ∈ loadAddrs (fwdVal rd (cselW idx (κ / 4)) [gen ^ idx, se, sg] (cselBody n κ))
      ((atomsOf (cselBody n κ)).map Ev.atom)) :
    (∃ t < 32 * n, A = se.limb 0 * addressOfIndex t) ∨ ∃ t < 144, A = sg.limb 0 * addressOfIndex t := by
  simp only [cselOk, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨⟨⟨-, -⟩, hc⟩, hS⟩ := hok
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hc
  set j0 := κ / 4 with hj0
  set args : List E := [gen ^ idx, se, sg] with hargs
  set σ := fwdVal rd (cselW idx j0) args (cselBody n κ) with hσ
  have hg : ∀ a, Stmt.atom a ∈ cselBody n κ → Good rd [] (cselW idx j0) σ a := by
    intro a ha; have := fwd_good (rd := rd) (w := cselW idx j0) (args := args) hc' a ha
    rwa [show args.length = 3 from rfl, hS] at this
  have p1' : σ (.n 1) = se := fwd_param (args := args) hc' (i := 1) (by rw [hargs]; simp)
  have p2 : σ (.n 2) = sg := fwd_param (args := args) hc' (i := 2) (by rw [hargs]; simp)
  obtain ⟨d, q, off, hm, rfl⟩ := mem_loadAddrs hA
  have hm := mem_of_mem_atomsOf hm
  by_cases hnk : n ≤ j0
  · have hb : cselBody n κ = [.atom (.hint (.digitsExp (.n 0) (4 * n) 0 4 (4 * (κ / 4)) none (.stack []))),
        osCst 3 (word 1 0), .atom (.assertEq (.n 3) (.n 0)), osCst 4 (word 1 0), .ret [.n 4]] := by
      simp [cselBody, cselBodyA, hnk, ← hj0]
    rw [hb] at hm
    simp at hm
  set c := n - j0 with hc
  have hnk' : ¬ n ≤ j0 := hnk
  have hbA : (cselBodyA n κ).1 = [.atom (.hint (.digitsExp (.n 0) (4 * n) c 4 (4 * j0) none
      (.stack ((List.range c).map fun i => .n (3 + i)))))] ++
      ((List.range c).map (cselDigit j0 κ c)).flatten ++
      [.atom (.assertEq (.n (cselReb c (c - 1))) (.n 0)),
        .atom (.copy (.n (cselB c c)) (.n (cselSel c (c - 1))))] := by
    simp [cselBodyA, hnk', ← hj0, ← hc]
  have hmemA : ∀ s, s ∈ (cselBodyA n κ).1 → s ∈ cselBody n κ := fun s hs => by
    rw [cselBody]; exact List.mem_append_left _ hs
  have hdig : ∀ i < c, ∀ a, Stmt.atom a ∈ cselDigit j0 κ c i → Stmt.atom a ∈ cselBody n κ :=
    fun i hi a ha => hmemA _ (by
      rw [hbA]; refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ha⟩)))
  have hd : ∀ i < c, σ (.n (3 + i)) = gen ^ nibOf idx (j0 + i) := by
    intro i hi
    have := hg (.hint (.digitsExp (.n 0) (4 * n) c 4 (4 * j0) none
      (.stack ((List.range c).map fun i => .n (3 + i))))) (hmemA _ (by rw [hbA]; simp)) (.n (3 + i))
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rw [this]; simp [cselW]
  have hne : ∀ i, nibOf idx (j0 + i) < 16 := fun i => Nat.mod_lt _ (by decide)
  -- the load is a digit's
  obtain ⟨i, hi, hmd⟩ : ∃ i < c, Stmt.atom (.load d q off) ∈ cselDigit j0 κ c i := by
    rw [cselBody, List.mem_append, hbA] at hm
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatten, List.mem_map,
      List.mem_range, Stmt.atom.injEq, reduceCtorEq, false_or, or_false] at hm
    obtain ⟨_, ⟨i, hi, rfl⟩, h⟩ := hm
    exact ⟨i, hi, h⟩
  have hmul : ∀ x y z, Stmt.atom (.mul (.n x) (.n y) (.n z)) ∈ cselDigit j0 κ c i → y < x → z < x →
      σ (.n x) = σ (.n y) * σ (.n z) := fun x y z h hy hz =>
    good_mul_eq (hg _ (hdig i hi _ h)) hy hz
  have hb3 : 3 + i < cselB c i + 4 := by unfold cselB; split_ifs <;> omega
  have hdi := hd i hi
  have hjn : j0 + i < n := by omega
  unfold cselDigit at hmd hmul
  split_ifs at hmd hmul with hi0
  · subst hi0
    simp only [List.mem_cons, List.mem_nil_iff, or_false, osCst, osMul, csRc, Stmt.atom.injEq, reduceCtorEq,
      false_or, Atom.load.injEq] at hmd
    rcases hmd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · left
      rw [hmul _ 1 (3 + 0) (by simp) (by omega) hb3, p1', hdi, limb_gpow_addr]
      exact ⟨_, by have := selOff_le (4 * j0 + 3 - κ); have := hne 0; simp only [Nat.add_zero] at *; omega, rfl⟩
    · right
      rw [hmul _ 2 (3 + 0) (by simp) (by omega) (by omega), p2, hdi, limb_gpow_addr]
      exact ⟨_, by have := hne 0; simp only [Nat.add_zero] at *; omega, rfl⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false, osCst, osMul, csRc, Stmt.atom.injEq, reduceCtorEq,
      false_or, Atom.load.injEq] at hmd
    rcases hmd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · left
      rw [hmul _ 1 (3 + i) (by simp) (by omega) hb3, p1', hdi, limb_gpow_addr]
      exact ⟨_, by have := hne i; omega, rfl⟩
    · right
      rw [hmul _ 2 (3 + i) (by simp) (by omega) (by omega), p2, hdi, limb_gpow_addr]
      exact ⟨_, by have := hne i; omega, rfl⟩

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **`column_selector__L{n}_L{κ}` completes placed**, with no words of its own, its loads in any
region holding the selector tables' `32 n` words at `se` and the `144` nibble shares at `sg`. -/
theorem column_selector_placed {k : ℕ} (hk : 4 ≤ k) (n κ : ℕ) (h4 : 4 ≤ n) (h8 : n ≤ 8)
    (h30 : κ ≤ 30) {idx : ℕ} (hidx : idx < 2 ^ (4 * n)) (hal : 2 ^ κ ∣ idx) (p p1 : ℕ → E) (se sg : E)
    {R : ℕ → Prop} (hR : (∀ t < 32 * n, ∃ m, se.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
      ∀ t < 144, ∃ m, sg.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) (fp c : ℕ) :
    CallAtA fs al cert k (cselName n κ) [gen ^ idx, se, sg] [∏ t ∈ Finset.Ico κ (4 * n), selBit p p1 idx t]
      R (fun _ => False) (fun _ => True) (CselPre n p p1 se sg) PostQuiet (fs (cselName n κ)) fp c c := by
  obtain ⟨f, hfind, hparams, hbody⟩ := csel_spec n κ h4 h8 h30
  have hok := cselOk_all n h4 h8 κ h30
  have hokA := cselOkA_all n h4 h8 κ h30
  simp only [cselOkA, Bool.and_eq_true] at hokA
  have hok' := hok
  simp only [cselOk, Bool.and_eq_true] at hok'
  have hlp : coreProgram.loop (cselName n κ) = false := by
    rw [Program.loop_of_find? hfind, Fn.loop, hbody, cselBody]; simp
  have e := callAtA_straight (fs := fs) (al := al) (cert := cert) (k := k) (R := R) (D := fun _ => False)
    (Out := fun _ => True) (Pre := CselPre n p p1 se sg) (fp := fp) (c := c)
    (args := [gen ^ idx, se, sg]) (rets := [∏ t ∈ Finset.Ico κ (4 * n), selBit p p1 idx t])
    (fun rd => fwdVal rd (cselW idx (κ / 4)) [gen ^ idx, se, sg] (cselBody n κ)) [] [] hfind hlp
    (by rw [hbody, hok'.1.1.1, hokA.1]; rfl) ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial)
    (fun _ h => h.elim) fun rd hl _ hpre => ?_
  · simpa using e
  obtain ⟨hpar, hret, hA⟩ := csel_fwd hk h8 hparams hbody hok hidx hal p p1 se sg rd hl hpre
  refine ⟨hpar, hret, hA, ?_, ?_, fun A hA' => ?_⟩
  · rw [hbody]; exact allocs_atoms _ hokA.2
  · rw [hbody, allocDsts_atoms hokA.2]; rfl
  · rw [hbody] at hA'
    rcases csel_loads h8 hok hA' with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · obtain ⟨m, hm, hRm⟩ := hR.1 t ht; exact ⟨m, hm, Or.inr hRm⟩
    · obtain ⟨m, hm, hRm⟩ := hR.2 t ht; exact ⟨m, hm, Or.inr hRm⟩

end
end LeanVM.Guest.B1.VsC
