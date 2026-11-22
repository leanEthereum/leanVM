/-
  LeanVM.Guest.CoreMode.Fn.column_selector.ResCs

  `column_selector`'s lowest digit, sound at the honest frames given its offset's alignment
  and the nibble shares at `sel_g` (`CsQ`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.check_opening_terminal.ResE
public import LeanVM.Guest.CoreMode.Fam.MonoChain
public import LeanVM.Guest.CoreMode.Fam.RefAll
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«column_selector__L»

/-!
# `column_selector`'s lowest digit

`csRes κ s d`: `column_selector__L{κ}`'s read of its lowest digit `[d]`'s eq weight at
`[s]·[d]·g^(64(κ/4) + 16(w - 1))`, inside the strided level-`w` table, `w` the digit's width; `csB j`
names it at function `j`.

`CsQ r J`: at an instance of `column_selector__L{κ}`, its offset is `g^o`, `o < 2^32` a multiple of
`2^κ`, and `sel_g` holds the nibble shares (`GTabsAt`), as `check_opening_terminal`'s dispatch hands
them.

`cs_digit`: on such arguments, the digits' range checks and `rebuilt = offset` make the offset's
exponent `16^(κ/4)` times the digits' number (`csDig`), so the lowest digit `g^u`, `u < 16`, is a
multiple of `2^(4 - w)` (`B1.Tables.cs_dvd`), `w` its width (`csW_sub`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B2C (cellJ)

@[expose] public section

/-- **`column_selector__L{κ}`'s read of its lowest digit's eq weight**: `[s]·[d]·g^off` inside
`[s]·g^(2^(4 - w)·i + off)`, `i < 2^w`, `w` the digit's width, `off = 64(κ/4) + 16(w - 1)`. -/
def csRes (κ s d : ℕ) : Mode.Res :=
  let w := Tables.csW κ 0
  let off := 64 * (κ / 4) + 16 * (w - 1)
  .sub ⟨⟨0, off, Mode.insertBs (.fr d, 1) [(.fr s, 1)]⟩, .num 0, .num 1, 1, 0⟩
    [⟨⟨0, 0, [(.fr s, 1)]⟩, .num 0, .num (2 ^ w), 2 ^ (4 - w), off⟩]

/-- The `κ` whose `csRes` reads at offset `k`. -/
def csKappa (k : ℕ) : ℕ := 4 * (k / 64) + 3 - k % 64 / 16

/-- **The lowest digit's read at function `j`**: `j` is `column_selector__L{κ}`, its `sel_eq` and
digit cells `s`, `d`, the digit's inside the frame. -/
noncomputable def csB (j : ℕ) : Mode.Res → Bool
  | .sub a [b] =>
    decide (csKappa a.q.k < 31) && (coreOf j).name == Tables.lName "column_selector" (csKappa a.q.k) &&
      inFr j (cellJ j (.n (valf% «column_selector» "digits[0]"))) &&
      decide (Mode.Res.sub a [b] = csRes (csKappa a.q.k) (cellJ j (.n (valf% «column_selector» "sel_eq")))
        (cellJ j (.n (valf% «column_selector» "digits[0]"))))
  | _ => false

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (csRes csKappa csB inFr topAtoms)
open LeanVM.Guest.B1.Tables (csPre csNibT csN csW csC csRb csHint csDig holds_csNib cs_dvd csDig_lt
  prod_gen_pow_csDig csNibT_noRet csPre_noRet csFound csRet csW_bounds GTabsAt lName)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- `column_selector__L{κ}`'s arguments as its caller hands them: the offset `g^o`, `o < 2^32` a
multiple of `2^κ`, and the nibble shares at `sel_g`. -/
def CsH (rd : Reader) (κ : ℕ) : List E → Prop
  | [off, _se, sg] => ∃ o < 2 ^ 32, 2 ^ κ ∣ o ∧ off = gen ^ o ∧ GTabsAt rd sg
  | _ => False

/-- **`column_selector`'s arguments at its instances.** -/
def CsQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ κ < 31, f = lName "column_selector" κ → ∀ fn,
    coreProgram.find? f = some fn → CsH r.img.read κ (fn.params.map σ)

end

public section

/-- **The lowest digit**: `g^u`, `u < 16`, a multiple of `2^(3 - (w - 1))`, once the offset is
aligned. -/
theorem cs_digit {κ : ℕ} (hκ : κ < 31) {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {C : CallRel}
    {σ : Core.Val} {kret : List E → Prop} (hpre : Stmt.HoldsList C Lm.read σ (csPre κ) True kret)
    (hG : GTabsAt Lm.read (σ (.n (valf% «column_selector» "sel_g")))) {o : ℕ} (ho : o < 2 ^ 32) (hal : 2 ^ κ ∣ o)
    (h0 : σ (.n (valf% «column_selector» "offset")) = gen ^ o) : ∃ u < 16, σ (.n (valf% «column_selector» "digits[0]")) = gen ^ u ∧ 2 ^ (3 - (csW κ 0 - 1)) ∣ u := by
  have h32 : κ ≠ 32 := by omega
  simp only [csPre, h32, ↓reduceIte, csHint, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at hpre
  rw [holdsList_append, holdsList_flatten _ (fun b hb => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hb; exact csNibT_noRet κ t)] at hpre
  obtain ⟨hnibs, htail⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at htail
  obtain ⟨hassert, -⟩ := htail
  set N := csN κ with hNdef
  set b := κ / 4 with hbdef
  have hN1 : 1 ≤ N := by simp only [hNdef, csN]; omega
  have hNb : b + N = 8 := by simp only [hNdef, hbdef, csN]; omega
  have hNib : ∀ k < N, _ := fun k hk => holds_csNib hμ Lm (C := C) (σ := σ) (kret := kret) (κ := κ) (k := k)
    (hnibs _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
  choose u hu hd xe xg hxe hxg hsel hrb using hNib
  let u' : ℕ → ℕ := fun k ↦ if hk : k < N then u k hk else 0
  have hu' : ∀ k < N, u' k < 16 := fun k hk => by simp only [u', hk, ↓reduceDIte]; exact hu k hk
  let xg' : ℕ → E := fun k ↦ if hk : k < N then xg k hk else 1
  have hR : ∀ k < N, σ (.n (csRb κ k)) = ∏ m ∈ Finset.range (k + 1), xg' m := by
    intro k hk
    induction k with
    | zero => rw [hrb 0 hk]; simp [xg', hk]
    | succ k ih =>
      rw [hrb (k + 1) hk, Finset.prod_range_succ]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega)]; simp [xg', hk]
  have hxg' : ∀ k < N, xg' k = gen ^ (u' k * 16 ^ (b + k)) := by
    intro k hk
    have h1 := hG (b + k) (show b + k < 8 by omega) (u k hk) (hu k hk)
    have h2 := hxg k hk
    rw [show u k hk + 16 * (b + k) = 16 * (b + k) + u k hk by omega] at h2
    simp only [xg', u', hk, ↓reduceDIte]
    exact B1.Tables.tb_loadHolds_unique h2 h1
  have hreb : σ (.n (valf% «column_selector» "offset")) = gen ^ (16 ^ b * csDig u' N) := by
    have e0 := Value.e_add_eq_zero_iff.mp hassert
    rw [← e0, hR (N - 1) (by omega), show N - 1 + 1 = N by omega,
      Finset.prod_congr rfl (fun k hk => hxg' k (Finset.mem_range.mp hk)), prod_gen_pow_csDig]
  have hlt : 16 ^ b * csDig u' N < 2 ^ 32 := by
    have := csDig_lt hu'
    rw [show 16 ^ b = 2 ^ (4 * b) by rw [pow_mul]; norm_num]
    calc 2 ^ (4 * b) * csDig u' N < 2 ^ (4 * b) * 2 ^ (4 * N) :=
          Nat.mul_lt_mul_of_pos_left this (Nat.two_pow_pos _)
      _ = 2 ^ 32 := by rw [← pow_add, show 4 * b + 4 * N = 32 by omega]
  have hoe : o = 16 ^ b * csDig u' N :=
    Value.gen_pow_inj (by omega) (by omega) (h0.symm.trans hreb)
  have hdv := cs_dvd hu' (hoe ▸ hal) 0 (by omega)
  refine ⟨u 0 (by omega), hu 0 _, by simpa using hd 0 (by omega), ?_⟩
  simpa [u', show 0 < N by omega] using hdv

theorem csW_sub {κ : ℕ} : 3 - (csW κ 0 - 1) = 4 - csW κ 0 := by
  have := csW_bounds κ 0; omega

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

end

end

end LeanVM.Guest.EndExec
