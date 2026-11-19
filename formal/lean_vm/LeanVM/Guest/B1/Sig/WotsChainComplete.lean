/-
  LeanVM.Guest.B1.Sig.WotsChainComplete

  A chained dispatch's arms (`armsM`), for completeness: an arm below `4^n` is `armT`'s, a dispatch
  completes by the arm of its honest digits, and its values are numbered below its end.
-/

module

public import LeanVM.Guest.B1.Sig.CodewordComplete
public import LeanVM.Guest.B1.Sig.WotsSound

/-!
# A chained dispatch, complete

Both signature verifiers dispatch their digit groups back to back over tables that may be wider
than a group's digits (`armsM`, `WotsT`): leanXMSS's in `main_loop2`, leanSPHINCS's in `sp_wots`.

* `armM_eq`, `armsM_eq`, `armBaseM_eq`: arm `k < 4^n` of a group is `armT`'s, from `armBase`'s base;
* `armsM_append`: the arms of a table split at an arm;
* `matchArm_complete`: a dispatch on `d` whose arm `k` is `armT`'s from `armB … k`, its chains'
  starts `vals` loaded: the arm's atoms and its starts kept, the step's reads (`good`) kept;
* `armM_snd_ge`, `armsM_snd_ge`, `armsM_numBelow`, `groupArmsT_numBelow`: the arms' bases grow and
  their values are numbered below their end (the arms `≥ 4^n` are `armT`'s values or fewer).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The arms -/

theorem armM_eq (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) {k : Nat} (b : Nat) (hk : k < 4 ^ n) :
    armM W slots first n fold prodIn encIn prodOut encOut k b =
      armT W slots first n fold prodIn encIn prodOut encOut k b := by
  simp only [armM, armT, Nat.mod_eq_of_lt hk]

theorem armsM_eq (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ (m k b : Nat), k + m ≤ 4 ^ n →
    armsM W slots first n fold prodIn encIn prodOut encOut m k b =
      armsT W slots first n fold prodIn encIn prodOut encOut m k b
  | 0, _, _, _ => rfl
  | m + 1, k, b, h => by
      simp only [armsM, armsT, armM_eq W slots first n fold prodIn encIn prodOut encOut b
        (show k < 4 ^ n by omega)]
      rw [armsM_eq W slots first n fold prodIn encIn prodOut encOut m (k + 1) _ (by omega)]

theorem armsM_append (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (m : Nat) : ∀ (j k b : Nat),
    armsM W slots first n fold prodIn encIn prodOut encOut (j + m) k b =
      ((armsM W slots first n fold prodIn encIn prodOut encOut j k b).1 ++
        (armsM W slots first n fold prodIn encIn prodOut encOut m (k + j)
          (armsM W slots first n fold prodIn encIn prodOut encOut j k b).2).1,
        (armsM W slots first n fold prodIn encIn prodOut encOut m (k + j)
          (armsM W slots first n fold prodIn encIn prodOut encOut j k b).2).2)
  | 0, k, b => by simp [armsM]
  | j + 1, k, b => by
      rw [show j + 1 + m = (j + m) + 1 by omega]
      simp only [armsM]
      rw [armsM_append W slots first n fold prodIn encIn prodOut encOut m j (k + 1),
        show k + 1 + j = k + (j + 1) by omega]
      rfl

/-! ## A group's dispatch -/

/-- **A group's dispatch completes** by arm `k`, `armT`'s from `armB … k`, its starts `vals`
loaded, the dispatch's end `Ee` past the arms. -/
theorem matchArm_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : GoodStable B good) (hWa : StepAtoms W) {first n : Nat} {fold : Bool} {prodIn encIn : V}
    {b k d Ee : Nat} {arms : List (List Stmt)} (hk : k < 4 ^ n) (hB : B ≤ b + 6) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hpw : NBv B (W.power (digitSum k n))) (hkl : k < arms.length)
    (harm : arms[k] = (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
      (encT W fold n b) k (armB W first n fold prodIn encIn b k)).1)
    (hE : armB W first n fold prodIn encIn b (4 ^ n) ≤ Ee) (hd : d < b + 6) (vals : Nat → E)
    (σ : Val) (hg : good σ)
    (hx : σ (.n d) = ofK (addressOfIndex k)) :
    Completes C rd (b + 6) Ee [.match_ (.n d) arms] σ
      (fun σ' => good σ' ∧ (∀ t < n, σ' (grpPos W first n fold prodIn encIn b k t) = vals t) ∧
        AtomsHold rd σ' (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
          (encT W fold n b) k (armB W first n fold prodIn encIn b k)).1) := by
  set σr := sLoad (grpPos W first n fold prodIn encIn b k) vals σ n with hσr
  have hpos : ∀ t < n, ∃ j, grpPos W first n fold prodIn encIn b k t = .n j ∧ b + 6 ≤ j ∧
      j < armB W first n fold prodIn encIn b (4 ^ n) := fun t ht => by
    obtain ⟨j, e, h1, h2, -⟩ := grpPos_spec W first n fold prodIn encIn b k t hk ht
    exact ⟨j, e, h1, h2⟩
  have hext : Ext (b + 6) (armB W first n fold prodIn encIn b (4 ^ n)) σ σr := fun v hv =>
    sLoad_other _ _ σ n fun t ht e => by
      obtain ⟨j, ej, h1, h2⟩ := hpos t ht
      rw [ej] at e
      exact hv j h1 h2 e
  have hat : ∀ t < n, σr (grpPos W first n fold prodIn encIn b k t) = vals t :=
    sLoad_at _ vals σ n (fun a c h1 h2 => grpPos_ne hk h1 h2)
  have hgr : good σr := hc _ _ (fun j hj => (hext.apply (Or.inl (by omega))).symm) hg
  have hxr : σr (.n d) = ofK (addressOfIndex k) := by rw [hext.apply (Or.inl hd)]; exact hx
  refine Completes.reload (hext.mono le_rfl hE) (match_complete hkl ⟨d, hd, rfl⟩ hxr ?_)
  rw [harm]
  obtain ⟨σ', he', hp', hh'⟩ := groupArm_complete (C := C) (rd := rd) (first := first) (n := n)
    (fold := fold) (prodIn := prodIn) (encIn := encIn) (b := b) (k := k) hW hk hB hpi hei hpw σr
  refine ⟨σ', he'.mono le_rfl hE, ⟨hc _ _ (fun j hj => (he'.apply (Or.inl (by omega))).symm) hgr,
    fun t ht => ?_, atomsHold_of_holdsList (armT_atoms hWa ..)
      (hh' True (fun _ => True) trivial)⟩, hh'⟩
  obtain ⟨j, ej, -⟩ := hpos t ht
  rw [hp'.1, ej, fwd_hint_keep _ σr hp'.2
    (armStart_mem W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) k
      (armB W first n fold prodIn encIn b k) ht) (.n j) (by rw [← ej]; exact List.mem_singleton_self _),
    ← ej, hat t ht]

/-! ## The arms' bases -/

theorem armM_snd_ge (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) :
    b ≤ (armM W slots first n fold prodIn encIn prodOut encOut k b).2 := by
  have hw : ∀ st, b ≤ (walksT W slots first k st n 0 b).2 := fun st => by
    rw [walksT_snd, walkBase_eq]; omega
  have h := hw (if k = 0 then W.size + 1 else W.size)
  unfold armM
  cases fold <;> by_cases hk : k % 4 ^ n = 0 <;> simp only [hk, ↓reduceIte, Bool.false_eq_true] <;> omega

theorem armsM_snd_ge (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) :
    ∀ m k b, b ≤ (armsM W slots first n fold prodIn encIn prodOut encOut m k b).2
  | 0, _, _ => le_rfl
  | m + 1, k, b => by
      simp only [armsM]
      refine le_trans ?_ (armsM_snd_ge W slots first n fold prodIn encIn prodOut encOut m (k + 1) _)
      have h1 := armM_snd_ge W slots first n fold prodIn encIn prodOut encOut k b
      split <;> omega

theorem armBaseM_eq (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ k j b, k + j ≤ 4 ^ n →
    armBaseM W slots first n fold prodIn encIn prodOut encOut k j b =
      armBase W slots first n fold prodIn encIn prodOut encOut k j b
  | _, 0, _, _ => rfl
  | k, j + 1, b, h => by
      simp only [armBaseM, armBase]
      rw [armM_eq W slots first n fold prodIn encIn prodOut encOut b (show k < 4 ^ n by omega),
        armBaseM_eq W slots first n fold prodIn encIn prodOut encOut (k + 1) j _ (by omega)]

/-! ## A dispatch's values, numbered below its end -/

/-- The arms of a group's dispatch are numbered below its end. -/
theorem groupArmsT_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {first n : Nat} {fold : Bool}
    {prodIn encIn : V} {b : Nat} (hB : B ≤ b + 6) (hpi : NBv (b + 6) prodIn) (hei : NBv (b + 6) encIn)
    (hpw : ∀ k, NBv (b + 6) (W.power (digitSum k n))) :
    NumBelow (armB W first n fold prodIn encIn b (4 ^ n))
      (Stmt.valsArms (groupArmsT W first n fold prodIn encIn b).1) := by
  have h := groupD_numBelow (pre := []) (d := b) (first := first) (n := n) (fold := fold) hW hB le_rfl
    (.nil _) hpi hei (fun k _ => hpw k)
  have hend : (groupD W first n fold prodIn encIn b [] b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
    simp only [groupD, groupArmsT]; rw [armsT_snd]; rfl
  rw [hend] at h
  intro v hv
  refine h v (mem_valsList_of_mem (s := .match_ (.n b) (groupArmsT W first n fold prodIn encIn b).1)
    (by simp [groupD]) (List.mem_cons_of_mem _ hv))

theorem armM_snd_pos (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat)
    (prodIn encIn prodOut encOut : V) {k : Nat} (hk : k ≠ 0) (a : Nat) :
    (armM W slots first n false prodIn encIn prodOut encOut k a).2 =
      if k % 4 ^ n = 0 then walkBase W.size k 0 n a else walkBase W.size k 0 n a + 1 := by
  unfold armM
  by_cases h : k % 4 ^ n = 0 <;> simp [h, hk, walksT_snd]

theorem armM_snd_gt (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat)
    (prodIn encIn prodOut encOut : V) {k : Nat} (hk : k ≠ 0) (hn : 1 ≤ n) (a : Nat) :
    a + 1 ≤ (armM W slots first n false prodIn encIn prodOut encOut k a).2 := by
  rw [armM_snd_pos W slots first n prodIn encIn prodOut encOut hk a, walkBase_eq]
  split
  · rename_i h0
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h4 : k % 4 = 0 := by
      have : k % 4 ^ (n' + 1) % 4 = k % 4 :=
        Nat.mod_mod_of_dvd k (Dvd.intro_left (4 ^ n') (by rw [pow_succ]))
      rw [← this, h0]
    have hw : walkSum W.size k 0 (n' + 1) = walkSize W.size (dig k 0) + walkSum W.size k 1 n' := rfl
    have hd : dig k 0 = 0 := by simp [dig, h4]
    rw [hw, hd, walkSize]
    simp only [show ¬ (0 = 3) from by omega, ↓reduceIte]
    omega
  · omega

theorem armM_vals_sub (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) {k : Nat} (hk : k ≠ 0) (a : Nat) {x : V}
    (hx : x ∈ Stmt.valsList (armM W slots first n fold prodIn encIn prodOut encOut k a).1) :
    x ∈ Stmt.valsList (armT W slots first n fold prodIn encIn prodOut encOut k a).1 := by
  unfold armM at hx
  unfold armT
  cases fold <;> simp only [hk, ↓reduceIte, Bool.false_eq_true] at hx ⊢
  · split at hx <;>
      simp only [valsList_append, List.mem_append, valsList_cons, valsList_nil, List.append_nil, copyS, cst,
        addS, mulS, Stmt.vals, Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢ <;> tauto
  · simp only [valsList_append, List.mem_append, valsList_cons, valsList_nil, List.append_nil, copyS,
      Stmt.vals, Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto

/-- **A later arm's values**, `fold = false`, are numbered below any bound past its walks. -/
theorem armT_numBelow_pos {W : WotsT} {B : Nat} (hW : StepShape W B) {first n : Nat} {prodIn encIn : V}
    {vb k a E : Nat} (hB : B ≤ vb + 6) (hk : k ≠ 0)
    (ha : groupStart false vb + chainStride W * n + 2 ≤ a) (hE : walkBase W.size k 0 n a + 1 ≤ E)
    (hpi : NBv (vb + 6) prodIn) (hei : NBv (vb + 6) encIn) (hpw : NBv (vb + 6) (W.power (digitSum k n))) :
    NumBelow E (Stmt.valsList (armT W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
      (encT W false n vb) k a).1) := by
  have hW' := StepShape.mono hW hB
  have hgs : vb + 6 ≤ groupStart false vb := by simp [groupStart]
  have hwb := walkBase_le W.size k a (Nat.zero_le n)
  simp only [walkBase] at hwb
  obtain ⟨l1, l2, l3⟩ := armPos_lay W false (B := vb + 6) (n := n) (k := k) (a := a) le_rfl ha
  have hP1 : ∀ x, NBv (vb + 6) x → ∃ j < E, x = .n j := by
    rintro x ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩
  refine armT_vals hW' (by simpa [hk] using l1) (by simpa [hk] using l2) hP1 (fun x hx => ?_)
    ⟨?_, ?_, hP1 _ hpi, hP1 _ hei, hP1 _ hpw, fun _ => ?_⟩
  · obtain ⟨j, rfl, h⟩ := l3 x (by simpa [hk] using hx)
    rcases h with h | h
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨j, by omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩
  · rw [walksT_snd]
    exact ⟨_, by simpa using hE, rfl⟩

/-- **The arms `k ..< k + m` of a dispatch, `fold = false`, past arm `0`**, ending at a multiple of
`4^n`, are numbered below their end. -/
theorem armsM_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {first n : Nat} {prodIn encIn : V}
    {vb : Nat} (hn : 1 ≤ n) (hB : B ≤ vb + 6) (hpi : NBv (vb + 6) prodIn) (hei : NBv (vb + 6) encIn)
    (hpw : ∀ k, NBv (vb + 6) (W.power (digitSum k n))) : ∀ m k a, k ≠ 0 → (k + m) % 4 ^ n = 0 →
    groupStart false vb + chainStride W * n + 2 ≤ a →
    NumBelow (armsM W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb) (encT W false n vb)
      m k a).2 (Stmt.valsArms (armsM W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
        (encT W false n vb) m k a).1)
  | 0, _, _, _, _, _ => NumBelow.nil _
  | m + 1, k, a, hk, hm, ha => by
      have hN : 2 ≤ 4 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
      simp only [armsM, hk, ↓reduceIte, Stmt.valsArms]
      set a' := (armM W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb) (encT W false n vb)
        k a).2 with ha'
      have hge := armM_snd_ge W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
        (encT W false n vb) k a
      have hrest := armsM_snd_ge W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
        (encT W false n vb) m (k + 1) a'
      have hsnd := armM_snd_pos W (slotsT W false vb) first n prodIn encIn (prodT W false n vb)
        (encT W false n vb) hk a
      -- arm `k`'s walks end below the rest's end
      have hE : walkBase W.size k 0 n a + 1 ≤ (armsM W (slotsT W false vb) first n false prodIn encIn
          (prodT W false n vb) (encT W false n vb) m (k + 1) a').2 := by
        by_cases h0 : k % 4 ^ n = 0
        · simp only [h0, ↓reduceIte] at hsnd
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
            refine ⟨m - 1, ?_⟩
            rcases Nat.eq_zero_or_pos m with h | h
            · subst h
              exfalso
              rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)] at hm
              omega
            · omega
          simp only [armsM]
          have h1 := armM_snd_gt W (slotsT W false vb) first n prodIn encIn (prodT W false n vb)
            (encT W false n vb) (show k + 1 ≠ 0 by omega) hn a'
          have h2 := armsM_snd_ge W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
            (encT W false n vb) m' (k + 1 + 1)
            (if k + 1 = 0 then (armM W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
              (encT W false n vb) (k + 1) a').2 + 2 else (armM W (slotsT W false vb) first n false prodIn encIn
                (prodT W false n vb) (encT W false n vb) (k + 1) a').2)
          simp only [show k + 1 ≠ 0 by omega, ↓reduceIte] at h2 ⊢
          omega
        · simp only [h0, ↓reduceIte] at hsnd
          omega
      refine NumBelow.append ?_ (armsM_numBelow hW hn hB hpi hei hpw m (k + 1) a' (by omega)
        (by rw [show k + 1 + m = k + (m + 1) by omega]; exact hm) (by omega))
      intro x hx
      exact armT_numBelow_pos hW hB hk ha hE hpi hei (hpw _) x
        (armM_vals_sub _ _ _ _ _ _ _ _ _ hk a hx)

theorem valsArms_append : ∀ (xs ys : List (List Stmt)),
    Stmt.valsArms (xs ++ ys) = Stmt.valsArms xs ++ Stmt.valsArms ys
  | [], _ => rfl
  | x :: xs, ys => by simp only [List.cons_append, Stmt.valsArms, valsArms_append xs ys, List.append_assoc]

end
end LeanVM.Guest.B1.Sig
