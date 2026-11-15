/-
  LeanVM.Guest.EndExecRCp

  `certify_placement`'s residuals at its honest frames: rank `1`'s key nonzero, and the hinted
  group order onto the nine groups, so its ranks write every cell of `group_base`.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.EndExecRA
public import LeanVM.Guest.Res.CpChk
public import LeanVM.Guest.Res.MonoReplay
public import LeanVM.Guest.B1.Placement.Certify

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
nine groups, onto. The divisor at offset `152` is rank `1`'s key; the run at offset `275` is
`group_base[0 .. 9)`, each cell `g^k` that of the rank `r` with `π r = k`.
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

/-! ## The block's leading atoms -/

/-- The leading atoms of a block. -/
def leadAtoms : List Stmt → List Atom
  | .atom a :: ss => a :: leadAtoms ss
  | _ => []

/-- The block past its leading atoms. -/
def leadRest : List Stmt → List Stmt
  | .atom _ :: ss => leadRest ss
  | ss => ss

theorem lead_split : ∀ ss : List Stmt, ss = (leadAtoms ss).map Stmt.atom ++ leadRest ss
  | [] => rfl
  | .atom a :: ss => by
    simp only [leadAtoms, leadRest, List.map_cons, List.cons_append]
    exact congrArg _ (lead_split ss)
  | .ite .. :: _ | .match_ .. :: _ | .call .. :: _ | .callIf .. :: _ | .dispatch .. :: _
  | .ret _ :: _ => rfl

/-- **A leading atom is on every returning path.** -/
theorem lead_on_path {σ : Core.Val} {ss : List Stmt} {es : List Ev} {vs : List V} (hw : walk σ ss = .ret es vs)
    {a : Atom} (ha : a ∈ leadAtoms ss) : Ev.atom a ∈ es :=
  Bridge.atoms_on_path (by rw [← lead_split]; exact hw) a ha

/-! ## The body's facts -/

/-- **What `certify_placement`'s body gives** on a memory of at most `2^32` words with the
exponent tables at `g_squares`: each group's key word nonzero at `group_key[g^gi]`, each rank's
facts, and each rank's group read from `group_order[g^r]`. -/
theorem cp_keys {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {C : CallRel} {σ : Core.Val} {kret : List E → Prop}
    (hpre : Stmt.HoldsList C Lm.read σ cpPre True kret) (ht : B1.ExpTables Lm.read (σ (.n 1))) :
    (∀ gi < 9, ∃ K, K ≠ 0 ∧ LoadHolds Lm.read (σ (.n 10)) gi K) ∧ (∀ r < 9, CpFacts Lm.read σ r) ∧
      ∀ r < 9, LoadHolds Lm.read (σ (.n 136)) r (σ (.n (cpRB r))) := by
  simp only [cpPre, holdsList_append,
    tb_holdsList_range_flatten 8 (fun i ↦ [Stmt.atom (.load (.n (2 + i)) (.n 0) i)]) (fun _ ↦ rfl),
    tb_holdsList_range_flatten 9 cpGroup cpGroup_noRet,
    tb_holdsList_range_flatten 8 (fun r ↦ cpRank (r + 1)) (fun _ ↦ rfl),
    tb_holdsList_range_flatten 9 cpCols cpCols_noRet, holds_cpRank, cpRank0,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and] at hpre
  obtain ⟨-, hgroups, l138, c139, rc138, m143, l144, c145, m146, l145, m147, l148, hranks, -⟩ := hpre
  have hrk : ∀ k < 34, LoadHolds Lm.read (σ (.n 1)) (178 + k) (gen ^ (k * 247)) := fun k hk ↦ by
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
    (hK : ∀ gi < 9, ∃ K, K ≠ 0 ∧ LoadHolds rd (σ (.n 10)) gi K) (hf : ∀ r < 9, CpFacts rd σ r) :
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

/-! ## The residuals -/

/-- **`certify_placement`'s residuals at its honest frames.** -/
theorem resCp_alignA : ResCert alignA Fn.«certify_placement».modeCert := by
  intro r hr i hi e j t x hx hin
  have hres := LeanVM.Guest.Res.cp_res i hi x hx
  obtain ⟨hj0, hent0⟩ := LeanVM.Guest.Res.cp_idx
  obtain ⟨c155, c136, c137, hfs⟩ := LeanVM.Guest.Res.cp_cells
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  -- the frame's function
  obtain ⟨ia, rfl, hia, hna, hfa, hca, -, -, h1a, hlta⟩ := fn_of_idx t.idx
  obtain ⟨ib, hib, hib', hnb, hfb, hcb, -, -, h1b, hltb⟩ := fn_of_idx hj0
  have hjj : ia + 1 = fn_idx% «certify_placement» := by
    refine fnOf_entry_inj hlta hltb ?_
    have := t.entry
    simp only [entryOf, t.idx] at this
    rw [this, hent0]
  obtain rfl : ia = ib := by omega
  have hname : e.I.t.name = "certify_placement" := by rw [← hna, hnb]
  rw [← hjj] at c155 c136 c137 hfs
  -- the instance's body at its valuation, and its exponent tables
  obtain ⟨f0, bufs, kids, hnode⟩ := t.node
  have hf0 : f0 = "certify_placement" := by rw [← hname, hnode]; rfl
  subst hf0
  obtain ⟨args0, rets0, hv⟩ := inst_valid' hr t.inst hnode
  obtain ⟨fn, hfn, hps, hbody⟩ := cpFound
  obtain ⟨-, hb⟩ := LeanVM.Guest.Res.holds_of_valid LeanVM.Guest.Res.fs_pos hv hfn
  rw [hbody, holdsList_append, holdsList_noRet _ cpPre_noRet] at hb
  have htab : B1.ExpTables r.img.read (e.σ (.n 1)) :=
    carryQ_all hr e.I t.inst _ e.σ bufs kids hnode fn hfn ("certify_placement", 1, .tab) (by decide) rfl (.n 1) (by rw [hps]; rfl)
  obtain ⟨hK, hf, hord⟩ := cp_keys (by omega) r.img hb.1 htab
  -- the path's atoms name their values, which the frame holds
  obtain ⟨vs, hw, hF, -⟩ := t.events hr
  have hfnj : coreOf (ia + 1) = fn := by
    rw [hca]; exact Option.some.inj (hfa.symm.trans (hname ▸ hfn))
  rw [hfnj, hbody] at hw
  have hcell : ∀ a ∈ leadAtoms (cpPre ++ [.ret [.n 406, .n 407]]), ∀ v ∈ atomUses a,
      2 ≤ cellJ (ia + 1) v → cellJ (ia + 1) v < fsN (ia + 1) →
      refMem r.img (e.I.fp + cellJ (ia + 1) v) = e.σ v := fun a ha v hv h2 hlt ↦
    t.cell hr hF (namedOf_atom (lead_on_path hw ha) hv) h2 hlt
  rcases hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- rank `1`'s key, the word at its group's cell
    show refMem r.img (e.I.fp + 141) ≠ 0
    rw [← c155, hcell (.load (.n 155) (.n 154) 0) (by decide +kernel) (.n 155) (by decide) (by omega)
      (by omega)]
    obtain ⟨⟨gi, hgi, hg⟩, hld, -⟩ := hf 1 (by omega)
    rw [show cpRB 1 = 149 from rfl, show cpRK 1 = 155 from rfl] at *
    rw [hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at hld
    obtain ⟨K, hK0, hKl⟩ := hK gi hgi
    rw [tb_loadHolds_unique hld hKl]
    exact hK0
  · -- `group_base[0 .. 9)`: cell `g^k` the rank's whose group is `k`
    obtain ⟨π, hπ, hon⟩ := cp_onto hK hf
    have e136 := hcell (.load (.n 138) (.n 136) 0) (by decide +kernel) (.n 136) (by decide) (by omega)
      (by omega)
    rw [c136] at e136
    refine ⟨0, 9, rfl, rfl, fun vq hvq k _ hk ↦ ?_⟩
    obtain ⟨r0, hr0, hπr⟩ := hon k hk
    refine ⟨_, List.mem_map.mpr ⟨r0, List.mem_range.mpr hr0, rfl⟩,
      fun vb ylo yhi hvb hlo hhi ↦ ⟨0, by simp only [RIdx] at hlo; omega,
        by simp only [RIdx] at hhi; omega, ?_⟩⟩
    obtain ⟨w, ⟨u, w1, hu, hw1, rfl⟩, rfl⟩ := hvq
    obtain ⟨wb, ⟨u', wb1, hu', ⟨u2, wb2, hu2, hwb2, rfl⟩, rfl⟩, rfl⟩ := hvb
    simp only [RBs] at hw1 hwb2
    subst hw1 hwb2
    simp only [RBase] at hu hu'
    obtain ⟨y, ⟨hy, hylt⟩, rfl⟩ := hu2
    rw [e136, Mode.limb_mul_ofK] at hy
    obtain ⟨-, hrd⟩ := hord r0 hr0
    have hrd' : r.img.read (Parameters.g ^ y) = some (e.σ (.n (cpRB r0))) := by rw [← hy]; exact hrd
    rw [((refRd_img hκ r.img) _ _ (by unfold maxCells at hylt; omega) hrd').2, hπ r0 hr0, hπr,
      ← hu, ← hu', ← ofK_gpow]
    dsimp only
    simp only [pow_zero, pow_one, mul_one, one_mul, Nat.add_zero,
      show ofK (1 : K) = 1 from map_one (algebraMap K E)]

end

end LeanVM.Guest.EndExec
