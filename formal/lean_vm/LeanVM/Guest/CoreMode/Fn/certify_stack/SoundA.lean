/-
  LeanVM.Guest.CoreMode.Fn.certify_stack.SoundA

  `certify_stack`'s own family, sound at the honest instances of b2c's aligned tree (`OwnOkA`): the
  hinted group order onto the eight groups, so its ranks write every cell of `group_at`.
-/

module

public import LeanVM.Guest.EndExecCoreResA
public import LeanVM.Guest.EndExecResNz
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Stack.CertifyS
public import LeanVM.Guest.CoreMode.Fam.MonoChain
public import LeanVM.Guest.CoreMode.Fn.certify_stack.Fam
import LeanVM.Guest.Value.Pigeonhole

/-!
The bus era's `certify_placement` family (`cpPerm`) on `certify_stack`'s template (`B1.Stack.csBody`).
`csKey_nz`: each group's key at `group_key[gi]` is nonzero (its kappa range checked, so a power of `g`,
the key its `53`-rd power times `g^(-b0)`). `cs_onto`: each rank's group `g^(π r)`, `π r < 8`, is read
from the hinted order, its key the word at `group_key[g^(π r)]`, each key `g^(e+1)` times the next
(`B1.Stack.csRank0_sound`, `csRank_sound`); the keys strictly descend, so they are distinct, and being
their groups' cells' words, the ranks' groups are distinct (`Value.cover_of_writeOnce`): onto.
`csPerm_instA`: at an honest instance the residual `[group_at]·g^k` is the cell of the rank whose group is `k`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir LeanVM.Guest.B1.Stack LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

public section

variable {C : CallRel} {σ : Val}

/-- **Group `gi`'s key is nonzero**: its kappa is range checked, so a power of `g`. -/
theorem csKey_nz {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ) {gi : ℕ} (hgi : gi < 8) (s : ℕ)
    (h : AllOk C L.read σ (csKey gi s).1) : ∃ key, LoadHolds L.read (σ (.n 10)) gi key ∧ key ≠ 0 := by
  unfold csKey at h
  simp only [allOk_append, allOk_cons, allOk_nil, and_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hc33, hrc⟩, hch⟩, hkey⟩, hstk, -, -⟩, -⟩, -⟩ := h
  set kp := csKappa (csG gi) s with hkp_def
  simp only [StmtOk, Atom.Holds] at hc33
  simp only [csRc, StmtOk, Atom.Holds] at hrc
  obtain ⟨r1, r2, r3⟩ := hrc
  obtain ⟨e, -, hve⟩ := (rangeCheck_gen_iff hκ L _ (K := 34) (by decide)
    (le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6)) (by decide)).1
    ⟨_, _, _, r1, by rw [← r2, hc33]; rfl, r3⟩
  have hc := osPowSteps_val (C := C) (rd := L.read) (σ := σ) kp.2.1 (osPowDigits 53) kp.2.1
    (kp.2.2 + 4) 1 (by rw [pow_one]) hch
  rw [digits53, hve, ← pow_mul] at hc
  have hc0 : σ (.n (osPowSteps kp.2.1 (osPowDigits 53) kp.2.1 (kp.2.2 + 4)).2) ≠ 0 := by
    rw [hc]; exact gen_pow_ne_zero _
  simp only [StmtOk, Atom.Holds] at hstk
  by_cases hb0 : (csG gi).b0 = 0
  · simp only [hb0, ↓reduceIte] at hstk
    exact ⟨_, hstk, hc0⟩
  · simp only [hb0, ↓reduceIte, osCst, osMul, allOk_cons, allOk_nil, and_true, StmtOk,
      Atom.Holds] at hstk hkey
    obtain ⟨k0, k1⟩ := hkey
    refine ⟨_, hstk, ?_⟩
    rw [k1, k0]
    refine mul_ne_zero hc0 fun h0 ↦ ?_
    have h1 := csInv_eq gi hgi hb0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1

/-- **Strictly descending keys**: each key `g^(e+1)` times the next, `e < 1802`, so an earlier key is `g^D`
times a later one, `1 ≤ D`. -/
theorem cs_desc {k : ℕ → E} (hd : ∀ r, r + 1 < 8 → ∃ e < 1802, k r = gen ^ (e + 1) * k (r + 1)) :
    ∀ r s, r < s → s < 8 → ∃ D, 1 ≤ D ∧ D ≤ 1802 * s ∧ k r = gen ^ D * k s := by
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
theorem cs_distinct {k : ℕ → E} (hnz : ∀ r < 8, k r ≠ 0)
    (hd : ∀ r, r + 1 < 8 → ∃ e < 1802, k r = gen ^ (e + 1) * k (r + 1)) :
    ∀ r < 8, ∀ s < 8, k r = k s → r = s := by
  have key : ∀ r s, r < s → s < 8 → k r ≠ k s := fun r s hrs hs he ↦ by
    obtain ⟨D, hD1, hD2, hD⟩ := cs_desc hd r s hrs hs
    rw [he] at hD
    have h1 : (gen ^ D - 1) * k s = 0 := by rw [sub_mul, ← hD, one_mul, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · have h2 : gen ^ D = gen ^ 0 := by rw [pow_zero]; exact sub_eq_zero.mp h
      have := gen_pow_inj (lt_of_le_of_lt (show D ≤ 12614 by omega) (by norm_num)) (by norm_num) h2
      omega
    · exact hnz s hs h
  intro r hr s hs he
  rcases Nat.lt_trichotomy r s with h | h | h
  · exact absurd he (key r s h hs)
  · exact h
  · exact absurd he.symm (key s r h hr)

/-- **The ranks' groups are onto**: on `certify_stack`'s statements before its return, every group `j < 8` is
some rank's, the rank's slot `csSlot`'s word `g^j`. -/
theorem cs_onto {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ) (hA : AllOk C L.read σ csBodyA) :
    ∀ j < 8, ∃ r < 8, σ (.n (CoreMode.csSlot r)) = gen ^ j := by
  simp only [csBodyA, csKeys_end, allOk_append] at hA
  obtain ⟨⟨⟨⟨⟨⟨-, hK⟩, -⟩, hR⟩, -⟩, -⟩, -⟩ := hA
  simp only [Nat.reduceAdd] at hR
  simp only [csRanks, allOk_append, allOk_flatten, List.mem_map, List.mem_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hR
  obtain ⟨hR0, hRr⟩ := hR
  -- the groups' keys, nonzero
  have hK' : ∀ gi < 8, ∃ K, LoadHolds L.read (σ (.n 10)) gi K ∧ K ≠ 0 := fun gi hgi ↦ by
    obtain ⟨s', hs'⟩ := csKeys_each 8 0 12 hK gi hgi
    rw [Nat.zero_add] at hs'
    exact csKey_nz hκ (by omega) L hgi s' hs'
  choose! Kf hKf using hK'
  -- the ranks
  have hs0 : LoadHolds L.read (σ (.n 163)) 0 (σ (.n 165)) := by
    have := hR0 _ (List.mem_cons_self ..)
    simpa only [StmtOk, Atom.Holds] using this
  obtain ⟨ρ0, hρ0, hord0, hk0, -, -⟩ := csRank0_sound hκ (by omega) L 163 164 165 hR0
  have hsr : ∀ r < 7, LoadHolds L.read (σ (.n 163)) (r + 1) (σ (.n (165 + 11 + 18 * r))) := fun r hr ↦ by
    have := hRr r hr _ (by unfold csRank; exact List.mem_cons_self ..)
    simpa only [StmtOk, Atom.Holds] using this
  have hRr' := fun r (hr : r < 7) ↦ csRank_sound hκ hκ11 L 163 164 (165 + 11 + 18 * r)
    (if r = 0 then 165 + 6 else 165 + 11 + 18 * (r - 1) + 6)
    (if r = 0 then 165 + 10 else 165 + 11 + 18 * (r - 1) + 17) (r + 1) (hRr r hr)
  choose! ρs hρs hords hks hdesc _hats _hszs _htots using hRr'
  set π : ℕ → ℕ := fun r ↦ if r = 0 then ρ0 else ρs (r - 1) with hπdef
  have hπlt : ∀ r < 8, π r < 8 := fun r hr ↦ by
    rcases r with _ | r
    · exact hρ0
    · exact hρs r (by omega)
  have hslot : ∀ r < 8, σ (.n (if r = 0 then 165 else 165 + 11 + 18 * (r - 1))) = gen ^ π r := fun r hr ↦ by
    rcases r with _ | r
    · exact loadHolds_unique hs0 hord0
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hπdef]
      exact loadHolds_unique (hsr r (by omega)) (hords r (by omega))
  -- each rank's key is its group's
  set kr : ℕ → E := fun r ↦ σ (.n (if r = 0 then 165 + 6 else 165 + 11 + 18 * (r - 1) + 6)) with hkrdef
  have hkeyR : ∀ r < 8, kr r = Kf (π r) := fun r hr ↦ by
    rcases r with _ | r
    · exact loadHolds_unique hk0 (hKf ρ0 hρ0).1
    · simp only [hkrdef, hπdef, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact loadHolds_unique (hks r (by omega)) (hKf _ (hρs r (by omega))).1
  have hdist := cs_distinct (k := kr)
    (fun r hr ↦ by rw [hkeyR r hr]; exact (hKf _ (hπlt r hr)).2)
    (fun r hr ↦ by
      obtain ⟨e, he, h⟩ := hdesc r (by omega)
      refine ⟨e, he, ?_⟩
      simp only [hkrdef, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact h)
  intro j hj
  obtain ⟨r, ⟨hr, hrj⟩, -⟩ := Value.cover_of_writeOnce (N := 8) (M := 8) (slot := π) (mark := kr) (mem := Kf)
    hπlt hdist (fun r hr ↦ (hkeyR r hr).symm) le_rfl j hj
  exact ⟨r, hr, (hslot r hr).trans (by rw [hrj])⟩

/-- **Rank `1`'s key is nonzero** (the frame walk's divisor, value `182`): the word at its group's cell (`csKey_nz`). -/
theorem cs_key1_nz {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ) (hA : AllOk C L.read σ csBodyA) :
    σ (.n 182) ≠ 0 := by
  simp only [csBodyA, csKeys_end, allOk_append] at hA
  obtain ⟨⟨⟨⟨⟨⟨-, hK⟩, -⟩, hR⟩, -⟩, -⟩, -⟩ := hA
  simp only [Nat.reduceAdd] at hR
  simp only [csRanks, allOk_append, allOk_flatten, List.mem_map, List.mem_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hR
  obtain ⟨-, hRr⟩ := hR
  obtain ⟨ρ, hρ, -, hk, -⟩ := csRank_sound hκ hκ11 L _ _ _ _ _ _ (hRr 0 (by decide))
  obtain ⟨s', hs'⟩ := csKeys_each 8 0 12 hK ρ hρ
  rw [Nat.zero_add] at hs'
  obtain ⟨K, hKl, hK0⟩ := csKey_nz hκ (by omega) L hρ s' hs'
  have e := loadHolds_unique hk hKl
  intro h0
  apply hK0
  rw [← e]
  exact h0

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- **`certify_stack`'s cell `[group_at]·g^k`, `k < 8`, is one of `[group_at]·[v]` over its ranks' groups**
(`csPerm`), at an honest instance: the ranks' groups are onto (`cs_onto`). -/
theorem csPerm_instA (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node "certify_stack" σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? "certify_stack" = some fn) {x : CoreMode.CRes} (hx : CoreMode.csPerm x = true) :
    x.Holds σ := by
  match x, hx with
  | .subP ⟨cb, k⟩ cs, h =>
    simp only [CoreMode.csPerm, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hcb, hk⟩, rfl⟩ := h
    subst hcb
    have hκ28 : r.κ ≤ 28 := hr.log
    have hκ23 : 23 ≤ r.κ := by rw [hR.κ]; exact twentyThree_le_logMem _
    obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
    obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hf
    rw [find_certify_stack] at hf
    obtain rfl := Option.some.inj hf
    rw [certify_stack_body, csBody_split, holdsList_flat_ret _ csBodyA_flat] at hb
    obtain ⟨r0, hr0, hs⟩ := cs_onto (κ := r.κ) (by omega) (by omega) r.img hb.1 k hk
    have hvals : CoreMode.csRankVals = (List.range 8).map CoreMode.csSlot := by decide
    refine ⟨⟨[(CoreMode.csAt, 1), (CoreMode.csSlot r0, 1)], 0⟩, ?_, ?_⟩
    · rw [hvals, List.map_map]
      exact List.mem_map.mpr ⟨r0, List.mem_range.mpr hr0, rfl⟩
    · simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, CoreMode.vw, pow_one, mul_one, hs,
        Value.gen_pow_eq_ofK, addressOfIndex, pow_zero,
        show ofK (1 : Parameters.K) = 1 from map_one (algebraMap Parameters.K Parameters.E)]
  | .lt _ _, h | .nz _, h | .sub _ _, h | .subR _ _, h | .under _ _, h => simp [CoreMode.csPerm] at h

/-- **`certify_stack`'s divisor at every honest instance** is nonzero (`cs_key1_nz`). -/
theorem nzValA_cs182 : NzValA al D name% «certify_stack» (.n 182) := by
  intro r hR hr I hI σ bufs kids ht
  have hκ28 : r.κ ≤ 28 := hr.log
  have hκ23 : 23 ≤ r.κ := by rw [hR.κ]; exact twentyThree_le_logMem _
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_certify_stack
  rw [certify_stack_body, csBody_split, holdsList_flat_ret _ csBodyA_flat] at hb
  exact cs_key1_nz (κ := r.κ) (by omega) (by omega) r.img hb.1

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.certify_stack

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

public section

/-- **Its family** (`csPerm_instA`), aligned. -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  intro r hR hr I hI σ bufs kids ht fn hf x h
  exact csPerm_instA hR hr hI ht hf h

end

end LeanVM.Guest.CoreMode.Own.certify_stack
