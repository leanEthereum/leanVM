/-
  LeanVM.Guest.CoreMode.Fn.certify_placement.ResCp

  `certify_placement`'s residuals at its honest frames: a rank's key nonzero, and the hinted group
  order onto the nine groups, so its ranks write every cell of `group_base`.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.CoreMode.Fam.ResA
public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.MonoReplay
public import LeanVM.Guest.B1.Placement.Certify
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«certify_placement»

/-!
# `certify_placement`'s residuals

At an honest frame (`TopAt`) the frame's function is `certify_placement`, an instance whose body
holds at its valuation (`Res.holds_of_valid`) and whose `g_squares` is the exponent tables
(`(certify_placement, 1, .tab)` in `Res.carried`, `carryQ_all`). B1's decomposition of the body
(`holds_cpGroup`, `CpFacts`) then gives (`cp_keys`): each group's key word, `g^(κ·247)` over
`INV_GEN^c₀`, nonzero, stored at `group_key[g^gi]`; each rank's group `g^(π r)`, `π r < 9`, read
from `group_order[g^r]`, and its key the word at `group_key[g^(π r)]`, each key `g^(e+1)` times
the next.

The keys strictly descend (`cp_desc`), so the ranks' keys are distinct, and the keys being the
words of their groups' cells, the ranks' groups are (`Value.cover_of_writeOnce`): nine ranks into
nine groups, onto (`cp_onto`), which the core route's `cpPerm` family reads (`EndExec.cpPerm_inst`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (alignA)
open LeanVM.Guest.B1.Tables
open LeanVM.Guest.Value (gen_pow_ne_zero)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-! ## The body's facts -/

/-- **What `certify_placement`'s body gives** on a memory of at most `2^32` words with the
exponent tables at `g_squares`: each group's key word nonzero at `group_key[g^gi]`, each rank's
facts, and each rank's group read from `group_order[g^r]`. -/
theorem cp_keys {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {C : CallRel} {σ : Core.Val} {kret : List E → Prop}
    (hpre : Stmt.HoldsList C Lm.read σ cpPre True kret) (ht : B1.ExpTables Lm.read (σ (.n (val% «certify_placement» "g_squares")))) :
    (∀ gi < 9, ∃ K, K ≠ 0 ∧ LoadHolds Lm.read (σ (.n (val% «certify_placement» "group_key"))) gi K) ∧ (∀ r < 9, CpFacts Lm.read σ r) ∧
      ∀ r < 9, LoadHolds Lm.read (σ (.n (val% «certify_placement» "group_order"))) r (σ (.n (cpRB r))) := by
  simp only [cpPre, holdsList_append,
    tb_holdsList_range_flatten 8 (fun i ↦ [Stmt.atom (.load (.n (2 + i)) (.n (val% «certify_placement» "kappa_base")) i)]) (fun _ ↦ rfl),
    tb_holdsList_range_flatten 9 cpGroup cpGroup_noRet,
    tb_holdsList_range_flatten 8 (fun r ↦ cpRank (r + 1)) (fun _ ↦ rfl),
    tb_holdsList_range_flatten 9 cpCols cpCols_noRet, holds_cpRank, cpRank0,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and] at hpre
  obtain ⟨-, hgroups, l138, c139, rc138, m143, l144, c145, m146, l145, m147, l148, hranks, -⟩ := hpre
  have hrk : ∀ k < 34, LoadHolds Lm.read (σ (.n (val% «certify_placement» "g_squares"))) (178 + k) (gen ^ (k * 247)) := fun k hk ↦ by
    have := ht.2.2.1 k hk
    simpa only [B1.rankKeysAt, B1.rankStride] using this
  refine ⟨fun gi hgi ↦ ?_, fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · obtain ⟨-, hq, hrc, hload, hkey, hkeyL, -⟩ := holds_cpGroup hgi (hgroups gi hgi)
    obtain ⟨x, hx, ex⟩ := cp_rc34 hμ Lm hq hrc
    rw [ex, tb_loadHolds_mul_gen_pow] at hload
    have e5 := tb_loadHolds_unique hload (by rw [add_comm]; exact hrk x hx)
    refine ⟨_, ?_, hkeyL⟩
    rw [hkey, e5]
    intro h0
    have h1 := congrArg (· * gen ^ cpC0 gi) h0
    simp only [zero_mul] at h1
    rw [mul_assoc, cpInvWord_mul hgi, mul_one] at h1
    exact gen_pow_ne_zero _ h1
  · rcases Nat.eq_zero_or_pos r with rfl | hr0
    · unfold CpFacts
      simp only [cpRB, cpRK, cpRP, cpRT, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      refine ⟨cp_rc9 hμ Lm c139 rc138, by rw [← m143]; exact l144, by rw [← m146]; exact l145,
        ⟨_, by rw [← m147]; exact l148, by rw [c145, tb_word_one, one_mul]⟩,
        fun _ ↦ by rw [c145, tb_word_one], fun h ↦ absurd h (by omega),
        fun h ↦ absurd h (by omega)⟩
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      exact cpFacts_succ hμ Lm (hranks r' (by omega))
  · rcases Nat.eq_zero_or_pos r with rfl | hr0
    · exact l138
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have h := (hranks r' (by omega)).1
      simp only [cpRB, Nat.add_one_ne_zero, ↓reduceIte]
      exact h

/-! ## The order -/

/-- **Strictly descending keys**: each key `g^(e+1)` times the next, `e < 8398`, so an earlier
key is `g^D` times a later one, `1 ≤ D`. -/
theorem cp_desc {k : ℕ → E} (hd : ∀ r, r + 1 < 9 → ∃ e < 8398, k r = gen ^ (e + 1) * k (r + 1)) :
    ∀ r s, r < s → s < 9 → ∃ D, 1 ≤ D ∧ D ≤ 8398 * s ∧ k r = gen ^ D * k s := by
  intro r s hrs hs
  induction s with
  | zero => omega
  | succ s ih =>
    obtain ⟨e, he, hk⟩ := hd s hs
    rcases Nat.lt_or_ge r s with h | h
    · obtain ⟨D, hD1, hD2, hD⟩ := ih h (by omega)
      exact ⟨D + (e + 1), by omega, by omega, by rw [hD, hk, ← mul_assoc, ← pow_add]⟩
    · obtain rfl : r = s := by omega
      exact ⟨e + 1, by omega, by omega, hk⟩

/-- **The keys are distinct**: nonzero and strictly descending. -/
theorem cp_distinct {k : ℕ → E} (hnz : ∀ r < 9, k r ≠ 0)
    (hd : ∀ r, r + 1 < 9 → ∃ e < 8398, k r = gen ^ (e + 1) * k (r + 1)) :
    ∀ r < 9, ∀ s < 9, k r = k s → r = s := by
  have key : ∀ r s, r < s → s < 9 → k r ≠ k s := fun r s hrs hs he ↦ by
    obtain ⟨D, hD1, hD2, hD⟩ := cp_desc hd r s hrs hs
    rw [he] at hD
    have h1 : (gen ^ D - 1) * k s = 0 := by rw [sub_mul, ← hD, one_mul, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · have h2 : gen ^ D = gen ^ 0 := by rw [pow_zero]; exact sub_eq_zero.mp h
      have := tb_gen_pow_inj' (by omega) (by omega) h2
      omega
    · exact hnz s hs h
  intro r hr s hs he
  rcases Nat.lt_trichotomy r s with h | h | h
  · exact absurd he (key r s h hs)
  · exact h
  · exact absurd he.symm (key s r h hr)

/-- **The ranks' groups are onto**: from distinct keys, each the word of its group's cell. -/
theorem cp_onto {rd : Reader} {σ : Core.Val}
    (hK : ∀ gi < 9, ∃ K, K ≠ 0 ∧ LoadHolds rd (σ (.n (val% «certify_placement» "group_key"))) gi K) (hf : ∀ r < 9, CpFacts rd σ r) :
    ∃ π : ℕ → ℕ, (∀ r < 9, σ (.n (cpRB r)) = gen ^ π r) ∧ ∀ g < 9, ∃ r < 9, π r = g := by
  obtain ⟨π, hπ⟩ := tb_exists_fun_of_forall (n := 9) fun r hr ↦ (hf r hr).1
  obtain ⟨Kf, hKf⟩ := tb_exists_fun_of_forall (n := 9) hK
  have hkey : ∀ r < 9, σ (.n (cpRK r)) = Kf (π r) := fun r hr ↦ by
    have := (hf r hr).2.1
    rw [(hπ r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero] at this
    exact tb_loadHolds_unique this (hKf _ (hπ r hr).1).2
  have hdist := cp_distinct (k := fun r ↦ σ (.n (cpRK r)))
    (fun r hr ↦ by rw [hkey r hr]; exact (hKf _ (hπ r hr).1).1)
    (fun r hr ↦ by
      obtain ⟨e, he, h⟩ := (hf (r + 1) hr).2.2.2.2.2.2 (by omega)
      rw [Nat.add_sub_cancel] at h
      exact ⟨e, he, h⟩)
  refine ⟨π, fun r hr ↦ (hπ r hr).2, fun g hg ↦ ?_⟩
  obtain ⟨r, ⟨hr, hrg⟩, -⟩ := Value.cover_of_writeOnce (N := 9) (M := 9) (slot := π)
    (mark := fun r ↦ σ (.n (cpRK r))) (mem := Kf) (fun r hr ↦ (hπ r hr).1) hdist
    (fun r hr ↦ (hkey r hr).symm) le_rfl g hg
  exact ⟨r, hr, hrg⟩


/-- **Rank `1`'s key is nonzero** at every honest instance: the word at its group's cell (`cp_keys`). -/
theorem nzVal_cp155 : NzVal "certify_placement" (.n (val% «certify_placement» "key@2")) := by
  intro r hr I hI σ bufs kids hIt
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨args0, rets0, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨fn, hfn, hps, hbody⟩ := cpFound
  obtain ⟨-, hb⟩ := LeanVM.Guest.Res.holds_of_valid LeanVM.Guest.Res.fs_pos hv hfn
  rw [hbody, holdsList_append, holdsList_noRet _ cpPre_noRet] at hb
  have htab : B1.ExpTables r.img.read (σ (.n (val% «certify_placement» "g_squares"))) :=
    (carryQ_all hr I hI _ σ bufs kids hIt fn hfn ("certify_placement", 1, .tab) (by decide) rfl (.n (val% «certify_placement» "g_squares"))
      (by rw [hps]; rfl)).1
  obtain ⟨hK, hf, -⟩ := cp_keys (by omega) r.img hb.1 htab
  obtain ⟨⟨gi, hgi, hg⟩, hld, -⟩ := hf 1 (by omega)
  have eK : cpRK 1 = 155 := rfl
  rw [eK, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at hld
  obtain ⟨K, hK0, hKl⟩ := hK gi hgi
  rw [tb_loadHolds_unique hld hKl]
  exact hK0

end

end LeanVM.Guest.EndExec
