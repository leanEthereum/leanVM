/-
  LeanVM.Guest.CoreMode.Fn.column_selector.SoundA

  `column_selector`'s own family, sound at the honest instances of b2c's aligned tree (`OwnOkA`): its
  lowest digit's read lies in its strided table.
-/

module

public import LeanVM.Guest.EndExecCoreResA
public import LeanVM.Guest.CoreMode.Fn.column_selector.CsChain
public import LeanVM.Guest.CoreMode.Fn.column_selector.Fam

/-!
`cs_digit`: on `column_selector__L{n}_L{κ}`'s template (`B1.Stack.cselBody`), at an offset `g^idx`,
`idx < 2^32` a multiple of `2^κ`, with the nibble shares at `sel_g`, the range-checked digits rebuild
the offset, so they are its nibbles from `κ / 4` on (`B1.Stack.nibSum_digit`), and the lowest one,
`g^u`, has `2^(κ % 4) ∣ u` (the bus era's `cs_digit`, on `B1.Stack.csel_sound`'s steps). `cs_holdsA`:
at an honest instance, its arguments as its callers hand them (`csQ_allA`), the read
`[sel_eq]·[digit₀]·g^off` is the `k`-th cell of the run `csSub κ` names.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir LeanVM.Guest.B1.Stack
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.CoreMode (CRes csSub)

public section

/-- **The lowest digit**: `g^(2^(κ % 4)·k)`, `k < 2^(4 - κ % 4)`, once the offset is aligned. -/
theorem cs_digit {m : ℕ} (hm : m ≤ 32) (hm6 : 6 ≤ m) (L : MemoryImage m) {C : CallRel} {σ : Val} {n κ : ℕ}
    (hn : n ≤ 8) (hnk : κ / 4 < n) (hA : AllOk C L.read σ (cselBodyA n κ).1) (hsh : SharesAt L.read (σ (.n 2)))
    {idx : ℕ} (hidx : idx < 2 ^ 32) (hal : 2 ^ κ ∣ idx) (hoff : σ (.n 0) = gen ^ idx) :
    ∃ k < 2 ^ (4 - κ % 4), σ (.n 3) = gen ^ (2 ^ (κ % 4) * k) := by
  have hnk' : ¬ n ≤ κ / 4 := by omega
  set j0 := κ / 4 with hj0
  set c := n - j0 with hc
  have hc1 : 1 ≤ c := by omega
  simp only [cselBodyA, hnk', ↓reduceIte, ← hj0, ← hc, allOk_append, allOk_cons, allOk_nil, and_true,
    allOk_flatten, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hA
  obtain ⟨⟨-, hdig⟩, hassert, -⟩ := hA
  simp only [StmtOk, Atom.Holds] at hassert
  -- the digits
  have hex : ∀ i < c, ∃ e < 16, σ (.n (3 + i)) = gen ^ e := fun i hi ↦ by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; obtain ⟨e, he, hd, -⟩ := cselDigit0_ok hm hm6 L (hdig 0 hi); exact ⟨e, he, hd⟩
    · obtain ⟨e, he, hd, -⟩ := cselDigitS_ok hm hm6 L (by omega) (hdig i hi); exact ⟨e, he, hd⟩
  choose! e he hd using hex
  have hj9 : ∀ i < c, j0 + i < 9 := fun i hi ↦ by omega
  -- the rebuilt offset
  have hreb : ∀ i < c, σ (.n (cselReb c i)) = gen ^ nibSum e j0 (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro h0
      obtain ⟨e', he', hd', -, hl⟩ := cselDigit0_ok hm hm6 L (hdig 0 h0)
      have : e' = e 0 := Value.gen_pow_inj (by omega) (by have := he 0 h0; omega)
        (by rw [← hd', hd 0 h0])
      subst this
      rw [Nat.add_comm, Nat.add_comm] at hl
      rw [loadHolds_unique hl (by rw [Nat.add_comm]; exact hsh j0 (hj9 0 h0) (e 0) (he 0 h0))]
      simp [nibSum]
    | succ i ih =>
      intro hi
      obtain ⟨e', he', hd', -, u, hl, hr⟩ := cselDigitS_ok hm hm6 L (by omega) (hdig (i + 1) hi)
      have : e' = e (i + 1) := Value.gen_pow_inj (by omega) (by have := he (i + 1) hi; omega)
        (by rw [← hd', hd (i + 1) hi])
      subst this
      rw [hr, Nat.add_sub_cancel, ih (by omega),
        loadHolds_unique hl (by rw [Nat.add_comm]; exact hsh _ (hj9 _ hi) _ (he _ hi)), ← pow_add]
      rfl
  -- the offset is the rebuilt one
  have hidx' : idx = nibSum e j0 c := by
    have hrb := hreb (c - 1) (by omega)
    rw [Nat.sub_add_cancel hc1] at hrb
    have hlt := nibSum_lt e j0 c (fun i hi ↦ he i hi)
    have h16 : 16 ^ (j0 + c) ≤ 2 ^ 32 := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
    refine Value.gen_pow_inj (by omega) (by omega) ?_
    rw [← hoff, ← hrb]
    exact (Value.e_add_eq_zero_iff.mp hassert).symm
  have hnib : ∀ i < c, nibOf idx (j0 + i) = e i := fun i hi ↦ by
    rw [hidx']; exact nibSum_digit e j0 c (fun i hi ↦ he i hi) i hi
  -- the lowest digit, aligned
  set lo := κ - 4 * j0 with hlo
  have hlo' : lo = κ % 4 := by omega
  have hdv : 2 ^ lo ∣ e 0 := by
    rw [← hnib 0 (by omega), Nat.add_zero, nibOf, Nat.shiftRight_eq_div_pow]
    obtain ⟨q, hq⟩ := hal
    rw [hq, show κ = 4 * j0 + lo by omega, pow_add, mul_assoc,
      Nat.mul_div_cancel_left _ (by positivity),
      show (16 : ℕ) = 2 ^ lo * 2 ^ (4 - lo) by rw [← pow_add, show lo + (4 - lo) = 4 by omega]; rfl,
      Nat.mul_mod_mul_left]
    exact dvd_mul_right _ _
  obtain ⟨k, hk⟩ := hdv
  have hk16 : k < 2 ^ (4 - lo) := by
    have := he 0 (by omega); rw [hk] at this
    have h2 : 2 ^ lo * k < 2 ^ lo * 2 ^ (4 - lo) := by
      rw [← pow_add, show lo + (4 - lo) = 4 by omega]; exact this
    exact Nat.lt_of_mul_lt_mul_left h2
  refine ⟨k, by rw [← hlo']; exact hk16, ?_⟩
  rw [hd 0 (by omega), hk, hlo']

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- **`column_selector`'s lowest digit at an honest instance**: the read lies in its strided table. -/
theorem cs_holdsA (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} {n κ : ℕ} (h4 : 4 ≤ n) (h8 : n ≤ 8) (hκn : κ < 4 * n) (hκ : κ < 31)
    (ht : I.t = .node (cselName n κ) σ bufs kids) : (csSub κ).Holds σ := by
  have hκ28 : r.κ ≤ 28 := hr.log
  have hκ23 : 23 ≤ r.κ := by rw [hR.κ]; exact twentyThree_le_logMem _
  obtain ⟨idx, hidx, hal, h0, hsh⟩ := (csQ_allA hR hr I hI _ σ bufs kids ht).2.2.2.2 n κ h4 h8 hκn hκ rfl
  obtain ⟨fn, hf, -, hbody⟩ := cs_found n κ h4 h8 hκn hκ
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hf
  rw [hbody, cselBody, holdsList_flat_ret _ (cselBodyA_flat n κ)] at hb
  obtain ⟨k, hk, hd⟩ := cs_digit (m := r.κ) (by omega) (by omega) r.img h8 (by omega) hb.1 hsh hidx hal h0
  have hcap : 2 ^ (4 - κ % 4) < CoreMode.capE := by
    have : 2 ^ (4 - κ % 4) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold CoreMode.capE; omega
  have hcap0 : 0 < CoreMode.capE := by unfold CoreMode.capE; omega
  rw [csSub]
  show CoreMode.RunSet (CoreMode.vw σ) _ _ _ _ _
  refine ⟨0, 2 ^ (4 - κ % 4), k, CoreMode.rep_const hcap0, CoreMode.rep_const hcap, Nat.zero_le _, hk, ?_⟩
  unfold CoreMode.CCell.addrW
  refine congrArg (fun x : E ↦ x.limb 0) ?_
  simp only [CoreMode.CCell.valW, CoreMode.prodW, CoreMode.vw, hd, Value.gen_pow_eq_ofK, pow_one, mul_one]
  ring

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.column_selector

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

public section

/-- Each specialization listed is `column_selector__L{n}_L{κ}`, `κ < 4n`. -/
theorem csNames_ok : ∀ p ∈ csNames, 4 ≤ p.2.1 ∧ p.2.1 ≤ 8 ∧ p.2.2 < 4 * p.2.1 ∧ p.2.2 < 31 ∧
    p.1 = B1.Stack.cselName p.2.1 p.2.2 := by
  decide +kernel

/-- **Its family** (`cs_holdsA`), aligned. -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  intro r hR hr I hI σ bufs kids ht fn hf x hx
  obtain rfl : x = CoreMode.csSub p.2.2 := of_decide_eq_true hx
  obtain ⟨h4, h8, hκn, hκ, hname⟩ := csNames_ok p hp
  rw [hname] at ht
  exact cs_holdsA hR hr hI h4 h8 hκn hκ ht

end

end LeanVM.Guest.CoreMode.Own.column_selector
