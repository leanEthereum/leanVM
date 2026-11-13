/-
  LeanVM.Guest.B1.Sig.WotsCongr

  The codeword template depends on a chain step only through the chains, steps and powers it
  uses: two steps agreeing there give the same codeword.
-/

module

public import LeanVM.Guest.B1.Sig.CodewordComplete

/-!
# The codeword, by the steps it uses

`WEq W W' I`: the steps agree on the chains `i < I`, the steps `s < 3` and the powers `j < 10`.
Then the walks, arms, groups and codewords of both are the same (`codewordT_weq`), and so are their
states, tips, starts and arm positions. `cwStart_eq_cwPos`: a codeword's start, read off a
valuation holding the digits `K`, is the start of the arms of `K`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Two chain steps agreeing on the chains `i < I`, the steps `s < 3` and the powers `j < 10`. -/
structure WEq (W W' : WotsT) (I : Nat) : Prop where
  size : W.size = W'.size
  step : ∀ i < I, ∀ s < 3, W.step i s = W'.step i s
  power : ∀ j < 10, W.power j = W'.power j

variable {W W' : WotsT} {I : Nat}

theorem walkT_weq (h : WEq W W' I) {i : Nat} (hi : i < I) (slot : Nat → Nat) (stride d b : Nat) :
    walkT W i slot stride d b = walkT W' i slot stride d b := by
  unfold walkT
  split
  · rfl
  · congr 1
    exact List.flatMap_congr fun j hj => by
      rw [List.mem_range] at hj
      rw [h.step i hi (d + j) (by omega)]

theorem walksT_weq (h : WEq W W' I) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ m r b, first + r + m ≤ I →
      walksT W slots first k stride m r b = walksT W' slots first k stride m r b
  | 0, _, _, _ => rfl
  | m + 1, r, b, hm => by
      simp only [walksT]
      rw [walkT_weq h (i := first + r) (by omega), walksT_weq h slots first k stride m (r + 1) _ (by omega)]

theorem digitSum_le (k : Nat) : ∀ n, digitSum k n ≤ 3 * n
  | 0 => le_rfl
  | n + 1 => by
      simp only [digitSum]
      have := digitSum_le k n
      have : k / 4 ^ n % 4 < 4 := Nat.mod_lt _ (by norm_num)
      omega

theorem armT_weq (h : WEq W W' I) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) (hn : first + n ≤ I) (hd : n ≤ 3)
    (he : W.enc = W'.enc := by rfl) :
    armT W slots first n fold prodIn encIn prodOut encOut k b =
      armT W' slots first n fold prodIn encIn prodOut encOut k b := by
  have hp := h.power (digitSum k n) (by have := digitSum_le k n; omega)
  simp only [armT, h.size, hp, he]
  rw [walksT_weq h slots first k _ n 0 _ (by omega)]

/-- An arm's next base: its walks' and its outputs', whatever its encoding. -/
theorem armT_snd_weq (h : WEq W W' I) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) (hn : first + n ≤ I) :
    (armT W slots first n fold prodIn encIn prodOut encOut k b).2 =
      (armT W' slots first n fold prodIn encIn prodOut encOut k b).2 := by
  unfold armT
  rw [h.size, walksT_weq h slots first k _ n 0 _ (by omega)]
  split <;> rfl

theorem armsT_weq (h : WEq W W' I) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (hn : first + n ≤ I) (hd : n ≤ 3) (he : W.enc = W'.enc := by rfl) :
    ∀ m k b, armsT W slots first n fold prodIn encIn prodOut encOut m k b =
      armsT W' slots first n fold prodIn encIn prodOut encOut m k b
  | 0, _, _ => rfl
  | m + 1, k, b => by
      simp only [armsT]
      rw [armT_weq h slots first n fold prodIn encIn prodOut encOut k b hn hd he,
        armsT_weq h slots first n fold prodIn encIn prodOut encOut hn hd he m (k + 1)]

theorem armsT_snd_weq (h : WEq W W' I) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (hn : first + n ≤ I) :
    ∀ m k b, (armsT W slots first n fold prodIn encIn prodOut encOut m k b).2 =
      (armsT W' slots first n fold prodIn encIn prodOut encOut m k b).2
  | 0, _, _ => rfl
  | m + 1, k, b => by
      simp only [armsT]
      rw [armT_snd_weq h slots first n fold prodIn encIn prodOut encOut k b hn,
        armsT_snd_weq h slots first n fold prodIn encIn prodOut encOut hn m (k + 1)]

theorem armBase_weq (h : WEq W W' I) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (hn : first + n ≤ I) (hd : n ≤ 3) :
    ∀ k j b, armBase W slots first n fold prodIn encIn prodOut encOut k j b =
      armBase W' slots first n fold prodIn encIn prodOut encOut k j b
  | _, 0, _ => rfl
  | k, j + 1, b => by
      simp only [armBase]
      rw [armT_snd_weq h slots first n fold prodIn encIn prodOut encOut k b hn,
        armBase_weq h slots first n fold prodIn encIn prodOut encOut hn hd (k + 1) j]

theorem slotsT_weq (h : WEq W W' I) : slotsT W = slotsT W' := by
  funext fold b r s
  simp only [slotsT, chainStride, h.size]

theorem prodT_weq (h : WEq W W' I) : prodT W = prodT W' := by
  funext fold n b
  simp only [prodT, chainStride, h.size]

theorem encT_weq (h : WEq W W' I) : encT W = encT W' := by
  funext fold n b
  simp only [encT, chainStride, h.size]

theorem armStart_weq (h : WEq W W' I) : armStart W = armStart W' := by
  funext slots fold k b r
  simp only [armStart, h.size]

theorem groupT_weq (h : WEq W W' I) {first n : Nat} (fold : Bool) (prodIn encIn : V) (b : Nat)
    (hn : first + n ≤ I) (hd : n ≤ 3) (he : W.enc = W'.enc := by rfl) :
    groupT W first n fold prodIn encIn b = groupT W' first n fold prodIn encIn b := by
  unfold groupT groupD groupArmsT
  rw [slotsT_weq h, prodT_weq h, encT_weq h, armsT_weq h _ first n fold _ _ _ _ hn hd he]

theorem groupT_snd_weq (h : WEq W W' I) {first n : Nat} (fold : Bool) (prodIn encIn : V) (b : Nat)
    (hn : first + n ≤ I) :
    (groupT W first n fold prodIn encIn b).2 = (groupT W' first n fold prodIn encIn b).2 := by
  unfold groupT groupD groupArmsT
  rw [slotsT_weq h, prodT_weq h, encT_weq h, armsT_snd_weq h _ first n fold _ _ _ _ hn]

theorem armB_weq (h : WEq W W' I) {first n : Nat} (fold : Bool) (prodIn encIn : V) (b k : Nat)
    (hn : first + n ≤ I) (hd : n ≤ 3) :
    armB W first n fold prodIn encIn b k = armB W' first n fold prodIn encIn b k := by
  unfold armB
  rw [slotsT_weq h, prodT_weq h, encT_weq h, armBase_weq h _ first n fold _ _ _ _ hn hd]

theorem grpPos_weq (h : WEq W W' I) {first n : Nat} (fold : Bool) (prodIn encIn : V) (b k t : Nat)
    (hn : first + n ≤ I) (hd : n ≤ 3) :
    grpPos W first n fold prodIn encIn b k t = grpPos W' first n fold prodIn encIn b k t := by
  unfold grpPos
  rw [armStart_weq h, slotsT_weq h, armB_weq h fold prodIn encIn b k hn hd]

theorem groupsT_weq (h : WEq W W' I) (he : W.enc = W'.enc := by rfl) :
    ∀ m p prod enc b, 3 * (p + m) ≤ I → groupsT W m p prod enc b = groupsT W' m p prod enc b
  | 0, _, _, _, _, _ => rfl
  | m + 1, p, prod, enc, b, hm => by
      simp only [groupsT]
      rw [groupT_weq h _ prod enc b (by omega) (le_refl 3) he, prodT_weq h, encT_weq h, slotsT_weq h,
        groupsT_weq h he m (p + 1) _ _ _ (by omega)]

theorem codewordT_weq (h : WEq W W' I) {G : Nat} (target : E) (d0 : V) (b : Nat) (hG : 3 * G + 1 ≤ I)
    (he : W.enc = W'.enc := by rfl) :
    codewordT W G target d0 b = codewordT W' G target d0 b := by
  simp only [codewordT]
  rw [groupsT_weq h he G 0 _ _ b (by omega), groupT_weq h _ _ _ _ (by omega) (by norm_num) he, prodT_weq h,
    encT_weq h, slotsT_weq h]

theorem cwState_weq (h : WEq W W' I) (b : Nat) : ∀ p, 3 * p ≤ I → cwState W b p = cwState W' b p
  | 0, _ => rfl
  | p + 1, hp => by
      simp only [cwState]
      rw [cwState_weq h b p (by omega), prodT_weq h, encT_weq h, groupT_snd_weq h _ _ _ _ (by omega)]

theorem cwPos_weq (h : WEq W W' I) (G b : Nat) (K : Nat → Nat) (i : Nat) (hi : i < 3 * G + 1)
    (hG : 3 * G + 1 ≤ I) : cwPos W G b K i = cwPos W' G b K i := by
  have hn : cwN G (i / 3) ≤ 3 := by unfold cwN; split <;> norm_num
  have hn' : 3 * (i / 3) + cwN G (i / 3) ≤ I := by unfold cwN; split <;> omega
  unfold cwPos
  rw [cwState_weq h b _ (by omega), grpPos_weq h _ _ _ _ _ _ hn' hn]

/-- **A codeword's start**, read off a valuation holding the digits `K`, is the start of the arms
of `K`. -/
theorem cwStart_eq_cwPos {W : WotsT} {G b : Nat} {K : Nat → Nat} {σ : Val}
    (hK : ∀ q ≤ G, K q < 4 ^ cwN G q) (hx : ∀ q ≤ G, σ (.n (cwState W b q).2.2) = ofK
        (addressOfIndex (K q)))
    {i : Nat} (hi : i < 3 * G + 1) : cwStart W G b σ i = cwPos W G b K i := by
  have hb : 4 ^ cwN G (i / 3) ≤ 2 ^ 64 - 1 := by unfold cwN; split <;> norm_num
  have e : cwK W G b σ (i / 3) = K (i / 3) := logG_eq (hK _ (by omega)) hb (hx _ (by omega))
  unfold cwStart cwPos grpPos armB
  rw [e]

end
end LeanVM.Guest.B1.Sig
