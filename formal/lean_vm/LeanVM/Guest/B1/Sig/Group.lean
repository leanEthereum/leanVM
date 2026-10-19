/-
  LeanVM.Guest.B1.Sig.Group

  A digit group of a WOTS+C codeword (G:2421-2429): the hinted digits in the exponent, their range
  check and the dispatch over their values, each arm walking the group's chains.
-/

module

public import LeanVM.Guest.B1.Sig.Arm

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Values below a bound -/

/-- `v` is numbered below `hi`. -/
abbrev NB (hi : Nat) (v : V) : Prop := ∃ k < hi, v = .n k

theorem NB.mono {hi hi' : Nat} {v : V} (h : NB hi v) (hle : hi ≤ hi') : NB hi' v :=
  let ⟨k, hk, e⟩ := h; ⟨k, by omega, e⟩

theorem cArm_below {w : Wots} {tips : Nat → V × V} {power : Nat → V} {prodIn encIn prodOut encOut : V}
    {first n k : Nat} {fold fresh : Bool} {b hi : Nat} (hw : w.Below hi)
    (ht : ∀ r < n, NB hi (tips r).1 ∧ NB hi (tips r).2)
    (hio : NB hi prodIn ∧ NB hi encIn ∧ NB hi prodOut ∧ NB hi encOut ∧ NB hi (power (digitSum k n)))
    (hb : (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).2 ≤ hi) :
    NumBelow hi (Stmt.valsList (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).1) := by
  have hsnd := cArm_snd w tips power prodIn encIn prodOut encOut first n k fold fresh b
  have he0 := armWalksEnd_ge w tips first n k fold fresh b
  have hab : b ≤ armStart fold b := by unfold armStart; split <;> omega
  have hpe : (cWalks w tips first k fresh n 0 (armStart fold b)).2 = armWalksEnd w tips first n k fold fresh b := rfl
  rw [cArm_fst, valsList_append, valsList_append]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hio
  refine (NumBelow.append ?_ ?_).append ?_
  · cases fold
    · exact NumBelow.nil _
    · simp only [↓reduceIte, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
      exact NumBelow.cons ⟨b, by simp only [armStart, ↓reduceIte] at he0; omega, rfl⟩ (NumBelow.nil _)
  · exact cWalks_below hw _ _ _ (fun r' _ h => by simpa using ht r' (by omega)) (by omega)
  · unfold armTail
    by_cases hk : k = 0
    · subst hk
      cases fold <;>
        simp only [↓reduceIte, Bool.false_eq_true, mulS, valsList_cons, valsList_nil,
          Stmt.vals, Atom.vals, List.cons_append, List.nil_append, List.append_nil]
      · exact .cons h3 (.cons h1 (.cons h5 (.cons h4 (.cons h2 (.nil _)))))
      · exact .cons h3 (.cons h5 (.cons h4 (.cons ⟨b, by simp only [armStart, ↓reduceIte] at he0; omega, rfl⟩
          (.nil _))))
    · simp only [hk, ↓reduceIte] at hsnd
      cases fold <;>
        simp only [hk, ↓reduceIte, Bool.false_eq_true, mulS, cst, addS, valsList_cons, valsList_nil,
          Stmt.vals, Atom.vals, List.cons_append, List.nil_append, List.append_nil]
      · exact .cons h3 (.cons h1 (.cons h5 (.cons ⟨_, by omega, rfl⟩ (.cons h4 (.cons h2
          (.cons ⟨_, by omega, rfl⟩ (.nil _)))))))
      · exact .cons h3 (.cons h5 (.cons ⟨_, by omega, rfl⟩ (.cons h4 (.cons ⟨b, by
          simp only [armStart, ↓reduceIte] at he0; omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))))

/-! ## The arms -/

theorem cArm_snd_ge (w : Wots) (tips : Nat → V × V) (power : Nat → V) (prodIn encIn prodOut encOut : V)
    (first n k : Nat) (fold fresh : Bool) (b : Nat) :
    b ≤ (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).2 := by
  have h1 := cArm_snd w tips power prodIn encIn prodOut encOut first n k fold fresh b
  have h2 := armWalksEnd_ge w tips first n k fold fresh b
  have h3 : b ≤ armStart fold b := by unfold armStart; split <;> omega
  omega

section Arms

variable (w : Wots) (tips : Nat → V × V) (power : Nat → V) (prodIn encIn prodOut encOut : V)
  (first n : Nat) (fold : Bool)

theorem cArms_snd_ge : ∀ (m k b : Nat), b ≤ (cArms w tips power prodIn encIn prodOut encOut first n fold m k b).2
  | 0, _, _ => le_rfl
  | m + 1, k, b => by
      simp only [cArms]
      exact le_trans (cArm_snd_ge ..) (cArms_snd_ge m (k + 1) _)

theorem cArms_length : ∀ (m k b : Nat), (cArms w tips power prodIn encIn prodOut encOut first n fold m k b).1.length = m
  | 0, _, _ => rfl
  | m + 1, k, b => by simp only [cArms, List.length_cons, cArms_length m (k + 1)]

theorem cArms_get : ∀ (m k b j : Nat), j < m → ∃ bj,
    (cArms w tips power prodIn encIn prodOut encOut first n fold m k b).1[j]? =
      some (cArm w tips power prodIn encIn prodOut encOut first n (k + j) fold ((k + j) == 0) bj).1 ∧
    b ≤ bj ∧ (cArm w tips power prodIn encIn prodOut encOut first n (k + j) fold ((k + j) == 0) bj).2 ≤
      (cArms w tips power prodIn encIn prodOut encOut first n fold m k b).2 ∧
    (0 < j → (cArm w tips power prodIn encIn prodOut encOut first n k fold (k == 0) b).2 ≤ bj) ∧
    (j = 0 → bj = b)
  | 0, _, _, _, h => absurd h (by omega)
  | m + 1, k, b, 0, _ => ⟨b, by simp [cArms], le_rfl, by simp only [cArms, Nat.add_zero]; exact cArms_snd_ge ..,
      fun h => absurd h (by omega), fun _ => rfl⟩
  | m + 1, k, b, j + 1, h => by
      obtain ⟨bj, h1, h2, h3, _⟩ := cArms_get m (k + 1) _ j (by omega)
      refine ⟨bj, ?_, le_trans (cArm_snd_ge ..) h2, ?_, fun _ => h2, fun h => absurd h (by omega)⟩
      · simp only [cArms, List.getElem?_cons_succ]; rw [h1, show k + 1 + j = k + (j + 1) by omega]
      · simp only [cArms]; rw [show k + (j + 1) = k + 1 + j by omega]; exact h3

theorem cArms_below {hi : Nat} : ∀ (m k b : Nat),
    (∀ k' b', k ≤ k' → k' < k + m → b ≤ b' →
      (cArm w tips power prodIn encIn prodOut encOut first n k' fold (k' == 0) b').2 ≤ hi →
      NumBelow hi (Stmt.valsList (cArm w tips power prodIn encIn prodOut encOut first n k' fold (k' == 0) b').1)) →
    (cArms w tips power prodIn encIn prodOut encOut first n fold m k b).2 ≤ hi →
    NumBelow hi (Stmt.valsArms (cArms w tips power prodIn encIn prodOut encOut first n fold m k b).1)
  | 0, _, _, _, _ => NumBelow.nil hi
  | m + 1, k, b, h, hb => by
      simp only [cArms] at hb ⊢
      simp only [Stmt.valsArms]
      have h2 := cArms_snd_ge w tips power prodIn encIn prodOut encOut first n fold m (k + 1)
        (cArm w tips power prodIn encIn prodOut encOut first n k fold (k == 0) b).2
      exact (h k b le_rfl (by omega) le_rfl (by omega)).append
        (cArms_below m (k + 1) _ (fun k' b' h1 h2' h3 h4 => h k' b' (by omega) (by omega)
          (le_trans (cArm_snd_ge ..) h3) h4) hb)

end Arms

/-! ## A group -/

theorem holdsList_match_single (x : V) (arms : List (List Stmt)) (next : Prop) (kret : List E → Prop)
    (σ : Val) :
    Stmt.HoldsList C rd σ [.match_ x arms] next kret ↔
      ∃ (j : Nat) (h : j < arms.length), σ x = ofK (gpow j) ∧ Stmt.HoldsList C rd σ arms[j] next kret := by
  simp only [Stmt.HoldsList]
  exact holds_match_iff x arms next kret

theorem cGroup_sound {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} {prodIn encIn : V} {first n : Nat} {fold : Bool} {b : Nat} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (cGroup w power prodIn encIn first n fold b).1 next kret) :
    (∃ k < 4 ^ n, σ (.n b) = ofK (gpow k) ∧ ArmOK w σ (groupTips w.lx fold b) first n k ∧
      ArmFold σ power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n k fold) ∧
      next := by
  simp only [cGroup, hintW, rangeS, cst, List.cons_append, List.nil_append, holdsList_cons_atom,
    Atom.Holds, true_and] at h
  obtain ⟨_, _, h⟩ := h
  obtain ⟨j, hj, hx, ha⟩ := (holdsList_match_single _ _ _ _ _).mp h
  rw [cArms_length] at hj
  obtain ⟨bj, hget, -, -, -, -⟩ := cArms_get w (groupTips w.lx fold b) power prodIn encIn (groupProd w.lx fold n b)
    (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5) j hj
  rw [List.getElem?_eq_getElem (by rw [cArms_length]; exact hj), Option.some.injEq, Nat.zero_add] at hget
  rw [hget] at ha
  obtain ⟨h1, h2, hn⟩ := cArm_sound hmd ha
  exact ⟨⟨j, hj, hx, h1, h2⟩, hn⟩

/-! ## Completeness of a group -/

/-- The reader is defined at the first `K` powers of `g`, where the range checks read. -/
def MemOK (rd : Reader) (K : Nat) : Prop := ∀ i < K, (rd (gpow i)).isSome

theorem MemOK.mono {rd : Reader} {K K' : Nat} (h : MemOK rd K) (hle : K' ≤ K) : MemOK rd K' :=
  fun i hi => h i (lt_of_lt_of_le hi hle)

theorem digitSum_le (k : Nat) : ∀ n, digitSum k n ≤ 3 * n
  | 0 => le_rfl
  | n + 1 => by
      have := Nat.mod_lt (k / 4 ^ n) (show 4 > 0 by norm_num)
      have := digitSum_le k n
      simp only [digitSum]; omega

theorem digitSum_lt_ten (k : Nat) {n : Nat} (hn : n ≤ 3) : digitSum k n < 10 := by
  have := digitSum_le k n; omega

theorem word_two_pow {a : Nat} (h : a < 64) : word (2 ^ a) 0 0 = ofK (gpow a) := by
  rw [word_eq_eOfNat, eOfNat, Parameters.gpow, g_pow_eq_ofBits h]

theorem loadHolds_memOK {rd : Reader} {K : Nat} (hrd : MemOK rd K) {i : Nat} (hi : i < K) :
    LoadHolds rd (ofK (gpow i)) 0 ((rd (gpow i)).getD 0) := by
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  have e : (ofK (Parameters.gpow i)).limb 0 * Parameters.gpow 0 = Parameters.gpow i := by
    simp [Parameters.gpow]
  rw [e]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hrd i hi)
  rw [hv]; rfl

/-- **The range check is complete**: on a memory defined at the first `K` powers, `x = g^e`,
`e < K`, passes it with its complement and the words it reads. -/
theorem rangeCheck_witness {rd : Reader} {K : Nat} (hrd : MemOK rd K) (_hK : 1 ≤ K) {e : Nat} (he : e < K) :
    ∃ y t1 t2 : E, LoadHolds rd (ofK (gpow e)) 0 t1 ∧ ofK (gpow (K - 1)) = ofK (gpow e) * y ∧
      LoadHolds rd y 0 t2 := by
  refine ⟨_, _, _, loadHolds_memOK hrd he, ?_, loadHolds_memOK hrd (i := K - 1 - e) (by omega)⟩
  rw [← ofK_mul]
  congr 1
  simp only [Parameters.gpow, ← pow_add]
  congr 1
  omega

/-- `σ` with the values numbered `lo ..< hi` taken from `g`. -/
def patch (σ : Val) (lo hi : Nat) (g : Nat → E) : Val := fun v =>
  if v.path = [] ∧ v.tag = 0 ∧ lo ≤ v.idx ∧ v.idx < hi then g v.idx else σ v

theorem patch_ext (σ : Val) (lo hi : Nat) (g : Nat → E) : Ext lo hi σ (patch σ lo hi g) := by
  intro v hv
  unfold patch
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := h
    exact absurd (by cases v; simp_all) (hv v.idx h3 h4)
  · rfl

theorem patch_at (σ : Val) {lo hi j : Nat} (g : Nat → E) (h1 : lo ≤ j) (h2 : j < hi) :
    patch σ lo hi g (.n j) = g j := by
  simp [patch, h1, h2]

theorem stride_div {s r c : Nat} (hc : c < s) : (s * r + c) / s = r := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem stride_mod {s r c : Nat} (hc : c < s) : (s * r + c) % s = c := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem patch_out (σ : Val) {lo hi j : Nat} (g : Nat → E) (h : j < lo ∨ hi ≤ j) :
    patch σ lo hi g (.n j) = σ (.n j) := (patch_ext σ lo hi g).apply h

theorem patch_other (σ : Val) {lo hi : Nat} (g : Nat → E) {v : V} (h : Out lo hi v) :
    patch σ lo hi g v = σ v := (patch_ext σ lo hi g).out h

theorem groupStart_ge (fold : Bool) (b : Nat) : b + 5 ≤ groupStart fold b := by
  unfold groupStart; omega

theorem groupStart_eq (fold : Bool) (b : Nat) : groupStart fold b = armStart fold (b + 5) := by
  unfold groupStart armStart; cases fold <;> simp

theorem ws_lt_stride (lx : Bool) : walkSize lx 0 + 1 < chainStride lx := by unfold chainStride; omega

/-- The tips' values on the chains' range: offset `ws` of chain `q` its end, `ws + 1` the other
half. -/
def tipsPre (lx : Bool) (s0 : Nat) (tp : Nat → E × E) (σ : Val) (j : Nat) : E :=
  if (j - s0) % chainStride lx = walkSize lx 0 then (tp ((j - s0) / chainStride lx)).1
  else if (j - s0) % chainStride lx = walkSize lx 0 + 1 then (tp ((j - s0) / chainStride lx)).2
  else σ (.n j)

theorem tipsPre_tip (lx : Bool) (s0 : Nat) (tp : Nat → E × E) (σ : Val) (r : Nat) :
    tipsPre lx s0 tp σ (s0 + chainStride lx * r + walkSize lx 0) = (tp r).1 ∧
      tipsPre lx s0 tp σ (s0 + chainStride lx * r + walkSize lx 0 + 1) = (tp r).2 := by
  have hst := ws_lt_stride lx
  have e1 : s0 + chainStride lx * r + walkSize lx 0 - s0 = chainStride lx * r + walkSize lx 0 := by omega
  have e2 : s0 + chainStride lx * r + walkSize lx 0 + 1 - s0 = chainStride lx * r + (walkSize lx 0 + 1) := by
    omega
  constructor
  · unfold tipsPre
    rw [e1, stride_div (by omega), stride_mod (by omega)]
    simp
  · unfold tipsPre
    rw [e2, stride_div (by omega), stride_mod (by omega)]
    simp

/-- A group's presets: the digit, its bound and the range check's values, then the tips, then the
product and the encoding. -/
def groupPreset (w : Wots) (σ : Val) (power : Nat → V) (prodIn encIn : V) (first n : Nat) (fold : Bool)
    (b k : Nat) (y t1 t2 : E) (xs : Nat → E) : Val :=
  let s0 := groupStart fold b
  let st := chainStride w.lx
  let tp := fun r => tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) (first + r) (armDigit k r) (xs r)
  let σa := patch σ b (b + 5) fun j =>
    if j = b then ofK (gpow k) else if j = b + 1 then word (2 ^ (4 ^ n - 1)) 0 0
    else if j = b + 2 then y else if j = b + 3 then t1 else t2
  let σb := patch σa s0 (s0 + st * n) (tipsPre w.lx s0 tp σa)
  patch σb (s0 + st * n) (s0 + st * n + 2) fun j =>
    if j = s0 + st * n then (if fold then 1 else σ prodIn) * σ (power (digitSum k n))
    else (if fold then 0 else σ encIn) + lit (k * 4 ^ first)

section Pre

variable (w : Wots) (σ : Val) (power : Nat → V) (prodIn encIn : V) (first n : Nat) (fold : Bool)
  (b k : Nat) (y t1 t2 : E) (xs : Nat → E)

theorem groupPreset_ext :
    Ext b (groupStart fold b + chainStride w.lx * n + 2) σ
      (groupPreset w σ power prodIn encIn first n fold b k y t1 t2 xs) := by
  have h5 := groupStart_ge fold b
  unfold groupPreset
  exact ((patch_ext _ _ _ _).mono le_rfl (by omega)).comp
    (((patch_ext _ _ _ _).mono (by omega) (by omega)).comp ((patch_ext _ _ _ _).mono (by omega) le_rfl))

theorem groupPreset_low {j : Nat} (h1 : b ≤ j) (h2 : j < b + 5) :
    groupPreset w σ power prodIn encIn first n fold b k y t1 t2 xs (.n j) =
      if j = b then ofK (gpow k) else if j = b + 1 then word (2 ^ (4 ^ n - 1)) 0 0
      else if j = b + 2 then y else if j = b + 3 then t1 else t2 := by
  have h5 := groupStart_ge fold b
  unfold groupPreset
  rw [patch_out _ _ (by omega), patch_out _ _ (by omega), patch_at _ _ h1 h2]

theorem groupPreset_tip {r : Nat} (hr : r < n) :
    groupPreset w σ power prodIn encIn first n fold b k y t1 t2 xs
        (.n (groupStart fold b + chainStride w.lx * r + walkSize w.lx 0)) =
      (tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) (first + r) (armDigit k r) (xs r)).1 ∧
    groupPreset w σ power prodIn encIn first n fold b k y t1 t2 xs
        (.n (groupStart fold b + chainStride w.lx * r + walkSize w.lx 0 + 1)) =
      (tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) (first + r) (armDigit k r) (xs r)).2 := by
  have hst := ws_lt_stride w.lx
  have hm : chainStride w.lx * r + chainStride w.lx ≤ chainStride w.lx * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  have ht := tipsPre_tip w.lx (groupStart fold b) (fun r => tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ)
    (first + r) (armDigit k r) (xs r)) (patch σ b (b + 5) fun j =>
    if j = b then ofK (gpow k) else if j = b + 1 then word (2 ^ (4 ^ n - 1)) 0 0
    else if j = b + 2 then y else if j = b + 3 then t1 else t2) r
  unfold groupPreset
  constructor
  · rw [patch_out _ _ (by omega), patch_at _ _ (by omega) (by omega)]; exact ht.1
  · rw [patch_out _ _ (by omega), patch_at _ _ (by omega) (by omega)]; exact ht.2

theorem groupPreset_out :
    groupPreset w σ power prodIn encIn first n fold b k y t1 t2 xs (.n (groupStart fold b + chainStride w.lx * n)) =
      (if fold then 1 else σ prodIn) * σ (power (digitSum k n)) ∧
    groupPreset w σ power prodIn encIn first n fold b k y t1 t2 xs
        (.n (groupStart fold b + chainStride w.lx * n + 1)) =
      (if fold then 0 else σ encIn) + lit (k * 4 ^ first) := by
  unfold groupPreset
  constructor
  · rw [patch_at _ _ le_rfl (by omega)]; simp
  · rw [patch_at _ _ (by omega) (by omega)]; simp

end Pre

/-- **A group is complete**: for a digit value `k` in range and the chains' values `xs`, a
valuation under which the group holds, its chains' tips, product and encoding those of arm `k`. -/
theorem cGroup_complete {w : Wots} {power : Nat → V} {prodIn encIn : V} {first n : Nat} {fold : Bool}
    {b : Nat} {σ : Val} (hrd : MemOK rd (4 ^ n)) (hn : n ≤ 3) (hw : w.Below b)
    (hin : NB b prodIn ∧ NB b encIn ∧ ∀ s < 10, NB b (power s)) (hmd : σ w.md = mdw (stepCount w.lx) true)
    (hc : w.Canon σ) {k : Nat} (hk : k < 4 ^ n) {xs : Nat → E} (hx : ∀ r < n, IsCanonical128 (xs r)) :
    Completes C rd b (cGroup w power prodIn encIn first n fold b).2 (cGroup w power prodIn encIn first n fold b).1 σ
      (fun σ' => σ' (.n b) = ofK (gpow k) ∧
        (∀ r < n, TipSet w σ' (first + r) (armDigit k r) (xs r) (groupTips w.lx fold b r)) ∧
        ArmFold σ' power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n k fold) := by
  have h4 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have h64 : 4 ^ n ≤ 64 := le_trans (Nat.pow_le_pow_right (by norm_num) hn) (by norm_num)
  obtain ⟨y, t1, t2, hl1, hl2, hl3⟩ := rangeCheck_witness hrd h4 hk
  have h5 := groupStart_ge fold b
  have hst := ws_lt_stride w.lx
  set tips := groupTips w.lx fold b with htips_def
  set A := cArms w tips power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n fold
    (4 ^ n) 0 (b + 5) with hA
  have ha0 : (cArm w tips power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n 0 fold
      true (b + 5)).2 = groupStart fold b + chainStride w.lx * n + 2 := by
    rw [cArm_snd, armWalksEnd, cWalks_snd_fresh, groupStart_eq]; simp
  obtain ⟨b0, -, -, h0le, -, hb0⟩ := cArms_get w tips power prodIn encIn (groupProd w.lx fold n b)
    (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5) 0 (by omega)
  rw [hb0 rfl, Nat.zero_add] at h0le
  simp only [beq_self_eq_true] at h0le
  rw [ha0] at h0le
  obtain ⟨bk, hgk, hbk, hkle, h0k, hk0⟩ := cArms_get w tips power prodIn encIn (groupProd w.lx fold n b)
    (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5) k hk
  simp only [Nat.zero_add] at hgk hkle h0k
  simp only [beq_self_eq_true] at h0k
  rw [ha0] at h0k
  set σ1 := groupPreset w σ power prodIn encIn first n fold b k y t1 t2 xs with hσ1
  have he1 := groupPreset_ext w σ power prodIn encIn first n fold b k y t1 t2 xs
  rw [← hσ1] at he1
  have hk1 := hw.keep he1
  have hlow := fun {j : Nat} (h1 : b ≤ j) (h2 : j < b + 5) =>
    groupPreset_low w σ power prodIn encIn first n fold b k y t1 t2 xs h1 h2
  have htip := fun {r : Nat} (hr : r < n) => groupPreset_tip w σ power prodIn encIn first n fold b k y t1 t2 xs hr
  have hout := groupPreset_out w σ power prodIn encIn first n fold b k y t1 t2 xs
  rw [← hσ1] at hlow htip hout
  have hmid : ∀ r < n, chainStride w.lx * r + walkSize w.lx 0 + 2 ≤ chainStride w.lx * n := fun r hr => by
    have : chainStride w.lx * r + chainStride w.lx ≤ chainStride w.lx * n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
    unfold chainStride at this ⊢; omega
  have hcomp := cArm_complete (C := C) (rd := rd) (σ := σ1) (b := bk) (xs := xs)
    (tips := tips) (power := power) (prodIn := prodIn) (encIn := encIn) (prodOut := groupProd w.lx fold n b)
    (encOut := groupEnc w.lx fold n b) (first := first) (n := n) (k := k) (fold := fold) (fresh := k == 0)
    (hw.mono (by omega)) ?_ ?_ ?_ (by rw [hk1.2.2.2, hmd]) (hc.congr hk1) ?_ ?_
  rotate_left
  · -- the tips' positions
    by_cases hk' : k = 0
    · subst hk'
      simp only [beq_self_eq_true, ↓reduceIte, TipsPos]
      refine ⟨trivial, fun r' _ _ => ?_⟩
      rw [hk0 rfl, htips_def, groupTips, groupStart_eq, Nat.sub_zero]
    · simp only [hk', beq_iff_eq, ↓reduceIte, TipsPos]
      intro r' _ hr'
      have := h0k (by omega)
      have := hmid r' (by omega)
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩
  · -- the outputs' positions
    by_cases hk' : k = 0
    · subst hk'
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [hk0 rfl, armWalksEnd, cWalks_snd_fresh, ← groupStart_eq]
      exact ⟨rfl, rfl⟩
    · simp only [hk', beq_iff_eq, ↓reduceIte]
      have := h0k (by omega)
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩
  · exact ⟨hin.1.mono (by omega), hin.2.1.mono (by omega), (hin.2.2 _ (digitSum_lt_ten _ hn)).mono (by omega)⟩
  · intro r hr
    refine ⟨hx r hr, ?_⟩
    rw [TipSet, hk1.1, hk1.2.1, hk1.2.2.1]
    exact ⟨(htip hr).1, fun _ => (htip hr).2⟩
  · rw [ArmFold, groupProd, groupEnc, hout.1, hout.2, he1.below hin.1, he1.below hin.2.1, he1.below (hin.2.2 _ (digitSum_lt_ten _ hn))]
    exact ⟨rfl, rfl⟩
  obtain ⟨σ', he', hpost, hh⟩ := hcomp
  have heT : Ext b A.2 σ σ' := (he1.mono le_rfl (by omega)).comp (he'.mono (by omega) hkle)
  have hk2 := hw.keep heT
  have hb : ∀ j, b ≤ j → j < b + 5 → σ' (.n j) = σ1 (.n j) := fun j _ h2 => he'.apply (Or.inl (by omega))
  refine ⟨σ', heT, ⟨?_, fun r hr => ?_, ?_⟩, fun next kret hn => ?_⟩
  · rw [hb b le_rfl (by omega), hlow le_rfl (by omega)]; simp
  · rw [TipSet, hk2.1, hk2.2.1, hk2.2.2.1, (hpost.1 r hr).1, (hpost.1 r hr).2]
    exact ⟨(htip hr).1, fun _ => (htip hr).2⟩
  · rw [ArmFold, hpost.2.1, hpost.2.2, groupProd, groupEnc, hout.1, hout.2, heT.below hin.1,
      heT.below hin.2.1, heT.below (hin.2.2 _ (digitSum_lt_ten _ hn))]
    exact ⟨rfl, rfl⟩
  · simp only [cGroup, hintW, rangeS, cst, List.cons_append, List.nil_append, holdsList_cons_atom,
      Atom.Holds, true_and]
    rw [hb (b + 1) (by omega) (by omega), hb b le_rfl (by omega), hb (b + 2) (by omega) (by omega),
      hb (b + 3) (by omega) (by omega), hb (b + 4) (by omega) (by omega), hlow le_rfl (by omega),
      hlow (by omega) (by omega), hlow (by omega) (by omega), hlow (by omega) (by omega),
      hlow (by omega) (by omega)]
    simp only [show b + 1 ≠ b by omega, show b + 2 ≠ b by omega, show b + 2 ≠ b + 1 by omega,
      show b + 3 ≠ b by omega, show b + 3 ≠ b + 1 by omega, show b + 3 ≠ b + 2 by omega,
      show b + 4 ≠ b by omega, show b + 4 ≠ b + 1 by omega, show b + 4 ≠ b + 2 by omega,
      show b + 4 ≠ b + 3 by omega, ↓reduceIte]
    refine ⟨trivial, ⟨hl1, by rw [word_two_pow (by omega)]; exact hl2, hl3⟩,
      (holdsList_match_single _ _ _ _ _).mpr ⟨k, by rw [cArms_length]; exact hk, ?_, ?_⟩⟩
    · rw [hb b le_rfl (by omega), hlow le_rfl (by omega)]; simp
    · rw [List.getElem?_eq_getElem (by rw [cArms_length]; exact hk), Option.some.injEq] at hgk
      rw [hgk]
      exact hh next kret hn

theorem cGroup_snd_ge (w : Wots) (power : Nat → V) (prodIn encIn : V) (first n : Nat) (fold : Bool) (b : Nat) :
    groupStart fold b + chainStride w.lx * n + 2 ≤ (cGroup w power prodIn encIn first n fold b).2 := by
  have ha0 : (cArm w (groupTips w.lx fold b) power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b)
      first n 0 fold true (b + 5)).2 = groupStart fold b + chainStride w.lx * n + 2 := by
    rw [cArm_snd, armWalksEnd, cWalks_snd_fresh, groupStart_eq]; simp
  have hn : 0 < 4 ^ n := by positivity
  obtain ⟨b0, -, -, h0le, -, hb0⟩ := cArms_get w (groupTips w.lx fold b) power prodIn encIn
    (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5) 0 hn
  rw [hb0 rfl, Nat.zero_add] at h0le
  simp only [beq_self_eq_true] at h0le
  rw [ha0] at h0le
  exact h0le

theorem cGroup_below {w : Wots} {power : Nat → V} {prodIn encIn : V} {first n : Nat} {fold : Bool} {b : Nat}
    (hn : n ≤ 3) (hw : w.Below b) (hin : NB b prodIn ∧ NB b encIn ∧ ∀ s < 10, NB b (power s)) :
    NumBelow (cGroup w power prodIn encIn first n fold b).2
      (Stmt.valsList (cGroup w power prodIn encIn first n fold b).1) := by
  have hG := cGroup_snd_ge w power prodIn encIn first n fold b
  have h5 := groupStart_ge fold b
  have hst := ws_lt_stride w.lx
  set G := (cGroup w power prodIn encIn first n fold b).2
  have hmid : ∀ r < n, chainStride w.lx * r + walkSize w.lx 0 + 2 ≤ chainStride w.lx * n := fun r hr => by
    have : chainStride w.lx * r + chainStride w.lx ≤ chainStride w.lx * n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
    unfold chainStride at this ⊢; omega
  have hA : NumBelow G (Stmt.valsArms (cArms w (groupTips w.lx fold b) power prodIn encIn (groupProd w.lx fold n b)
      (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5)).1) :=
    cArms_below (hi := G) _ _ _ _ _ _ _ _ _ _ (4 ^ n) 0 (b + 5) (fun k' b' _ _ hb' hle => cArm_below (hw.mono (by omega))
      (fun r hr => ⟨⟨_, by have := hmid r hr; omega, rfl⟩, ⟨_, by have := hmid r hr; omega, rfl⟩⟩)
      ⟨hin.1.mono (by omega), hin.2.1.mono (by omega), ⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩,
        (hin.2.2 _ (digitSum_lt_ten _ hn)).mono (by omega)⟩ hle) le_rfl
  simp only [cGroup, hintW, rangeS, cst, List.cons_append, List.nil_append, valsList_cons, valsList_nil,
    Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.append_nil, List.cons_append, List.nil_append]
  exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩
    (.cons ⟨b + 2, by omega, rfl⟩ (.cons ⟨b + 3, by omega, rfl⟩ (.cons ⟨b + 4, by omega, rfl⟩
    (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩ hA)))))))

end
end LeanVM.Guest.B1.Sig
