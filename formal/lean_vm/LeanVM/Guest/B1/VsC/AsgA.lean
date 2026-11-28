/-
  LeanVM.Guest.B1.VsC.AsgA

  `assert_small_g_power` completes placed, its loads in the exponent table's nibble shares.
-/

module

public import LeanVM.Guest.B1.VsC.AsgC
public import LeanVM.Guest.B1.VsC.LeafA
public import LeanVM.Guest.B1.VsC.ColSelA
import LeanVM.Guest.CoreRef

/-!
# `assert_small_g_power`, placed

`assert_small_g_power(x, g_squares)` has no words of its own; placed at frame `fp` and cursor `c` it
ends at `c` (`callAtA_straight`). On `x = g^e`, `e < 2^36`, its valuation on a memory is the guest
stream's honest one (`asg_holds_ofD`, chosen per memory), each share load through `q·g^d` at
`34 + 16 j`, `d < 16` the digit, so in any region holding the nibble shares `[34, 178)` of the
table at `q` (`asg_placed`). The template's facts are one kernel decision (`asgOkA`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Every load of `assert_small_g_power`: digit `j`'s share, through `asgPtr j` at `34 + 16 j`. -/
def asgLoadOk : Atom → Bool
  | .load _ p off => (List.range 9).any fun j => p == .n (asgPtr j) && off == 34 + 16 * j
  | _ => true

/-- What the kernel checks of `assert_small_g_power` for its placed form. -/
def asgOkA : Bool :=
  (retOf asgBody).isSome && (atomsOf asgBody).all leafAtomOk && (atomsOf asgBody).all asgLoadOk &&
    (atomsOf asgBody).all (fun a => !atomAllocB a)

theorem asgOkA_ok : asgOkA = true := by decide +kernel

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- What the honest valuation satisfies on a memory. -/
def AsgHonest (e : ℕ) (q : E) (rd : Reader) (σ : Val) : Prop :=
  σ (.n 0) = gen ^ e ∧ σ (.n 1) = q ∧ (∀ j < 9, σ (.n (asgPtr j)) = q * gen ^ (e / 16 ^ j % 16)) ∧
    (∀ j < 9, σ (.n (j + 2)) = gen ^ (e / 16 ^ j % 16)) ∧
    Stmt.HoldsList (coreProgram.Rel rd) rd σ asgBody False (fun rs ↦ rs = [])

/-- The honest valuation on a memory, where the range checks and the shares allow one. -/
noncomputable def asgVal (e : ℕ) (q : E) (rd : Reader) : Val := Classical.epsilon (AsgHonest e q rd)

/-- **`assert_small_g_power` completes placed** on `g^e`, `e < 2^36`, its loads in `R`. -/
theorem asg_placed {k : ℕ} (hk : 4 ≤ k) {e : ℕ} (he : e < 2 ^ 36) {q : E} {R : ℕ → Prop}
    (hR : ∀ t < 144, ∃ m, q.limb 0 * addressOfIndex (34 + t) = addressOfIndex m ∧ R m) (fp c : ℕ) :
    CallAtA fs al cert k "assert_small_g_power" [gen ^ e, q] [] R (fun _ => False) (fun _ => True)
      (fun rd => ExpTables rd q) PostQuiet (fs "assert_small_g_power") fp c c := by
  have hok := asgOkA_ok
  simp only [asgOkA, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hr, hleaf⟩, hld⟩, hna⟩ := hok
  have hlp : coreProgram.loop "assert_small_g_power" = false := by
    rw [Program.loop_of_find? find_assert_small_g_power, Fn.loop, assert_small_g_power_body, asgBody]; simp
  have e' := callAtA_straight (fs := fs) (al := al) (cert := cert) (k := k) (R := R) (D := fun _ => False)
    (Out := fun _ => True) (Pre := fun rd => ExpTables rd q) (fp := fp) (c := c) (args := [gen ^ e, q])
    (rets := []) (asgVal e q) [] [] find_assert_small_g_power hlp
    (by rw [assert_small_g_power_body]; simp [hr, hleaf]) ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial)
    (fun _ h => h.elim) fun rd hl _ ht => ?_
  · simpa using e'
  have hex := asg_holds_ofD (C := coreProgram.Rel rd) (rd := rd) (q := q) (by simpa using he)
    (fun j => asg_rc_low hk hl (Nat.mod_lt _ (by decide))) (asg_shares ht e)
  obtain ⟨e0, e1, ep, ed, hh⟩ : AsgHonest e q rd (asgVal e q rd) := Classical.epsilon_spec hex
  set σ := asgVal e q rd with hσdef
  have hr' : retOf (fn% «assert_small_g_power»).body = some [] := by rw [assert_small_g_power_body]; decide +kernel
  rw [← assert_small_g_power_body] at hh
  have hA := atoms_of_holdsList hr' hh
  refine ⟨?_, fun vs hvs => by rw [hr'] at hvs; cases hvs; rfl, fun a ha => ⟨hA a ha, ?_⟩, ?_, ?_, fun A hA' => ?_⟩
  · show [σ (.n 0), σ (.n 1)] = _
    rw [e0, e1]
  · have hsplit : (fn% «assert_small_g_power»).body =
        .atom (.hint (.digitsExp (.n 0) 36 9 4 0 none (.stack [.n 2, .n 3, .n 4, .n 5, .n 6, .n 7,
          .n 8, .n 9, .n 10]))) :: (fn% «assert_small_g_power»).body.tail := rfl
    rw [hsplit] at ha
    rcases List.mem_cons.mp ha with he' | ha
    · cases he'
      exact asgHint_exact he e0 fun j hj => ed j hj
    · have hnc : (atomsOf (fn% «assert_small_g_power»).body.tail).all (fun a => !isComputed a) = true := by
        decide +kernel
      exact exact_of_not_computed (by simpa using List.all_eq_true.mp hnc a (mem_atomsOf' ha))
  · rw [assert_small_g_power_body]; exact allocs_atoms _ hna
  · rw [assert_small_g_power_body, allocDsts_atoms hna]; rfl
  · rw [assert_small_g_power_body] at hA'
    obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA'
    have h := List.all_eq_true.mp hld _ hm
    simp only [asgLoadOk, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨j, hj, rfl, rfl⟩ := h
    have hd : e / 16 ^ j % 16 < 16 := Nat.mod_lt _ (by decide)
    obtain ⟨m, hm', hRm⟩ := hR (e / 16 ^ j % 16 + 16 * j) (by omega)
    refine ⟨m, ?_, Or.inr hRm⟩
    rw [ep j hj, limb_gpow_addr, ← hm']
    congr 2; omega

end
end LeanVM.Guest.B1.VsC
