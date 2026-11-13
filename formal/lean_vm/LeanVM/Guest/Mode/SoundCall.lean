module

public import LeanVM.Guest.Mode.SoundJoin

/-!
# Translating a callee's bases

A callee's frame `sE` (its frame pointer the word of the caller's product `mq`) and its caller's
`sC` share one memory. `trFr_iff`, `trBase_iff`: a callee base's word is the word of the product
`trBase` gives it in the caller, both ways.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

theorem MonoVal.single {s : St} {b : Base} {v : E} : MonoVal s ⟨0, 0, [(b, 1)]⟩ v ↔ BaseVal s b v := by
  constructor
  · rintro ⟨w, ⟨u, w', hu, hw', rfl⟩, rfl⟩
    rw [show w' = 1 from hw']; simpa using hu
  · intro h
    exact ⟨v, ⟨v, 1, h, rfl, by simp⟩, by simp⟩

theorem MonoVal.unshift {s : St} {m : Mono} {o : ℕ} {v : E} (h : MonoVal s (m.shift o) v) :
    ∃ u, MonoVal s m u ∧ v = u * ofK (g ^ o) := by
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨_, ⟨w, hw, rfl⟩, by simp only [Mono.shift, pow_add, ofK_mul]; ring⟩

theorem Mono.rootCell_eq {m : Mono} {q : ℕ} (h : m.rootCell = some q) : m = .root q := by
  unfold Mono.rootCell at h
  split at h
  · cases h; rfl
  · cases h

theorem pow_val' {s : St} {fp k : ℕ} {u : E} (h : MonoVal s ⟨fp, k, []⟩ u) :
    u = ofK (g ^ (s.fp * fp + k)) := by
  obtain ⟨w, hw, rfl⟩ := h
  rw [show w = 1 from hw, mul_one, ← ofK_pow, ← pow_mul, ← ofK_mul, ← pow_add]

/-- The callee's frame and its caller's. -/
structure Frames (sC sE : St) (mq : Mono) : Prop where
  mem : sE.mem = sC.mem
  mq : MonoVal sC mq (ofK (g ^ sE.fp))
  fpE : sE.fp < maxCells
  fpC : sC.fp < maxCells
  wf : sC.mem.WF
  used : sC.mem.used ≤ maxCells

/-- A cell is the callee's cell `o`: the cell `mq·g^o` names. -/
theorem Frames.names {sC sE : St} {mq : Mono} (F : Frames sC sE mq) {o : ℕ} (ho : o < 2 ^ 30)
    {v : E} (hv : MonoVal sC (mq.shift o) v) {c : ℕ} (hc : Names v c) : c = sE.fp + o := by
  have := hv.unique (F.mq.shift o)
  rw [this, ← ofK_mul, ← pow_add] at hc
  exact names_ofK (by have := F.fpE; unfold maxCells at this; omega) hc

theorem Frames.get_lt {sC sE : St} {mq : Mono} (F : Frames sC sE mq) {c : ℕ} {v : E}
    (h : sE.mem.get c = some v) : c < maxCells := by
  rw [F.mem] at h
  exact lt_of_lt_of_le (F.wf.get_lt h) F.used

/-- The word of a heap cell the walk knows the word of, as a callee's cell `o`. -/
theorem hvGet_cell {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A)
    {o : ℕ} (ho : o < 2 ^ 30) {x : Mono} (h : A.hvGet (mq.shift o) = some (.m x)) :
    ∃ w, sE.mem.get (sE.fp + o) = some w ∧ MonoVal sC x w := by
  rw [F.mem]
  unfold Abs.hvGet at h
  split at h
  · rename_i d hd
    obtain ⟨he, hd'⟩ := Mono.ownCell_eq hd
    split_ifs at h with hw
    have hfp : mq = ⟨1, mq.k, []⟩ ∧ mq.k + o = d := by
      obtain ⟨a, b, c⟩ := mq
      simp only [Mono.shift, Mono.own, Mono.mk.injEq] at he
      exact ⟨by rw [he.1, he.2.2], he.2.1⟩
    have h1 := F.mq
    rw [hfp.1] at h1
    have h2 := pow_val' h1
    rw [Nat.mul_one] at h2
    have h3 := ofK_gpow_inj
      (by have := F.fpE; have := F.fpC; have := hfp.2; unfold maxCells at *; omega)
      (by have := F.fpE; have := F.fpC; have := hfp.2; unfold maxCells at *; omega) h2.symm
    rw [show sE.fp + o = sC.fp + d by omega]
    obtain ⟨u, hu⟩ := Mem.get_of_written (hA.written hw)
    refine ⟨u, hu, ?_⟩
    cases hv : A.v.get d with
    | none => rw [hv] at h; cases h; exact MonoVal.root hu
    | some y =>
      rw [hv] at h
      cases h
      obtain ⟨u', h4, h5⟩ := hA.v d _ hv
      rw [hu] at h4; cases h4; exact h5
  · obtain ⟨p, hp, hpx⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v0, c, w, h1, h2, h3, h4⟩ := hA.hv p (List.mem_of_find?_eq_some hp)
    have hb := List.find?_some hp
    rw [Mono.beq_eq hb] at h1
    rw [hpx] at h4
    obtain rfl := F.names ho h1 h2
    exact ⟨w, h3, h4⟩

/-- **A callee's frame cell, translated.** -/
theorem trFr_iff {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A) {o : ℕ}
    {m : Mono} (h : trFr A mq o = some m) (v : E) : BaseVal sE (.fr o) v ↔ MonoVal sC m v := by
  unfold trFr at h
  split_ifs at h with ho
  have ho : o < 2 ^ 30 := by omega
  split at h
  · rename_i x hx
    cases h
    obtain ⟨w, hw, hxw⟩ := hvGet_cell F hA ho hx
    show sE.mem.get (sE.fp + o) = some v ↔ _
    rw [hw]
    exact ⟨fun h ↦ (Option.some.inj h) ▸ hxw, fun h ↦ congrArg some (hxw.unique h)⟩
  · cases h
  · rename_i hn
    split at h
    · rename_i q hq
      cases h
      rw [MonoVal.single]
      have hmq := F.mq
      rw [Mono.rootCell_eq hq] at hmq
      obtain ⟨w, ⟨u, w', hu, hw', rfl⟩, h1⟩ := hmq
      have h1' : u = ofK (g ^ sE.fp) := by
        rw [h1, show w' = 1 from hw']
        simp [Mono.root, show ofK (1 : K) = 1 from map_one (algebraMap K E)]
      show sE.mem.get (sE.fp + o) = some v ↔ ∃ p x, sC.mem.get (sC.fp + q) = some p ∧ _
      constructor
      · intro hv
        refine ⟨u, sE.fp + o, hu, ⟨?_, F.get_lt hv⟩, F.mem ▸ hv⟩
        rw [h1', limb_mul_ofK]; simp [pow_add]
      · rintro ⟨p, c, hp, hc, hv⟩
        rw [hu] at hp; cases hp
        rw [h1', ← ofK_mul, ← pow_add] at hc
        rw [names_ofK (by have := F.fpE; unfold maxCells at this; omega) hc] at hv
        rw [F.mem]; exact hv
    · cases h

/-- A heap cell the walk knows the word of: its cell exists, holds it, and is the only one. -/
theorem hvGet_gen {s : St} {A : Abs} (hA : Holds s A) (hfp : s.fp < maxCells) (hwf : s.mem.WF)
    (hu : s.mem.used ≤ maxCells) {k x : Mono} (h : A.hvGet k = some (.m x)) :
    (∃ vk X w, MonoVal s k vk ∧ Names vk X ∧ s.mem.get X = some w ∧ MonoVal s x w) ∧
      ∀ vk X, MonoVal s k vk → Names vk X → ∃ w, s.mem.get X = some w ∧ MonoVal s x w := by
  unfold Abs.hvGet at h
  split at h
  · rename_i d hd
    obtain ⟨rfl, hd'⟩ := Mono.ownCell_eq hd
    split_ifs at h with hw
    obtain ⟨u, hu'⟩ := Mem.get_of_written (hA.written hw)
    have hx : MonoVal s x u := by
      cases hv : A.v.get d with
      | none => rw [hv] at h; cases h; exact MonoVal.root hu'
      | some y =>
        rw [hv] at h; cases h
        obtain ⟨u', h4, h5⟩ := hA.v d _ hv
        rw [hu'] at h4; cases h4; exact h5
    have hlt := hwf.get_lt hu'
    refine ⟨⟨_, s.fp + d, u, MonoVal.own d, ⟨by simp, by omega⟩, hu', hx⟩, fun vk X hk hX ↦ ?_⟩
    rw [own_names hfp hd hk hX]
    exact ⟨u, hu', hx⟩
  · obtain ⟨p, hp, hpx⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v0, c, w, h1, h2, h3, h4⟩ := hA.hv p (List.mem_of_find?_eq_some hp)
    have hb := List.find?_some hp
    rw [Mono.beq_eq hb] at h1
    rw [hpx] at h4
    refine ⟨⟨v0, c, w, h1, h2, h3, h4⟩, fun vk X hk hX ↦ ?_⟩
    obtain rfl := hk.unique h1
    obtain rfl := names_inj hX h2
    exact ⟨w, h3, h4⟩

theorem MonoVal.ptr {s : St} {k q : ℕ} {u : E} :
    MonoVal s ⟨0, k, [(.fr q, 1)]⟩ u ↔ ∃ p, s.mem.get (s.fp + q) = some p ∧ u = ofK (g ^ k) * p := by
  constructor
  · rintro ⟨w, ⟨p, w', hp, hw', rfl⟩, rfl⟩
    exact ⟨p, hp, by rw [show w' = 1 from hw']; simp⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, ⟨p, 1, hp, rfl, by simp⟩, by simp⟩

/-- **A callee's base, translated.** -/
theorem trBase_iff {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A)
    {b : Base} {m : Mono} (h : trBase A mq b = some m) (v : E) : BaseVal sE b v ↔ MonoVal sC m v := by
  cases b with
  | fr o => exact trFr_iff F hA h v
  | hp p d =>
    simp only [trBase] at h
    split at h
    · cases h
    rename_i mp hmp
    have hP := trFr_iff F hA hmp
    split_ifs at h with hd
    show (∃ pp X, sE.mem.get (sE.fp + p) = some pp ∧ Names (pp * ofK (g ^ d)) X ∧
      sE.mem.get X = some v) ↔ _
    rw [F.mem]
    split at h
    · rename_i x hx
      cases h
      obtain ⟨⟨vk, X, w, hk, hX, hw, hxw⟩, huniq⟩ := hvGet_gen hA F.fpC F.wf F.used hx
      constructor
      · rintro ⟨pp, Y, hpp, hY, hv⟩
        have h1 := (hP pp).mp (by rw [← F.mem] at hpp; exact hpp)
        obtain ⟨w', hw', hxw'⟩ := huniq _ Y (h1.shift d) hY
        rw [hv] at hw'; cases hw'; exact hxw'
      · intro hv
        obtain ⟨u, hu, rfl⟩ := hk.unshift
        have : sC.mem.get (sE.fp + p) = some u := by rw [← F.mem]; exact (hP u).mpr hu
        obtain rfl := hv.unique hxw
        exact ⟨u, X, this, hX, hw⟩
    · cases h
    · split at h
      · rename_i k q _
        cases h
        rw [MonoVal.single]
        show _ ↔ ∃ p' X, sC.mem.get (sC.fp + q) = some p' ∧ Names (p' * ofK (g ^ (k + d))) X ∧
          sC.mem.get X = some v
        have e1 : ∀ p', ofK (g ^ k) * p' * ofK (g ^ d) = p' * ofK (g ^ (k + d)) := fun p' ↦ by
          rw [pow_add, ofK_mul]; ring
        constructor
        · rintro ⟨pp, X, hpp, hX, hv⟩
          obtain ⟨p', hp', rfl⟩ := MonoVal.ptr.mp ((hP _).mp (by rw [← F.mem] at hpp; exact hpp))
          exact ⟨p', X, hp', by rw [← e1]; exact hX, hv⟩
        · rintro ⟨p', X, hp', hX, hv⟩
          have : sC.mem.get (sE.fp + p) = some (ofK (g ^ k) * p') := by
            rw [← F.mem]; exact (hP _).mpr (MonoVal.ptr.mpr ⟨p', hp', rfl⟩)
          exact ⟨_, X, this, by rw [e1]; exact hX, hv⟩
      · cases h

/-! ## Products, taken apart -/

theorem BsVal.insert_inv {s : St} {b : Base} {e : ℕ} :
    ∀ {l : List (Base × ℕ)} {w : E}, BsVal s (insertBs (b, e) l) w →
      ∃ u wl, BaseVal s b u ∧ BsVal s l wl ∧ w = u ^ e * wl
  | [], w, ⟨u, w', hu, hw', h⟩ => ⟨u, 1, hu, rfl, by rw [h, show w' = 1 from hw']⟩
  | (b', e') :: l, w, h => by
    unfold insertBs at h
    dsimp only at h
    split_ifs at h with hq hl
    · obtain rfl := Base.beq_eq hq
      obtain ⟨u, w', hu, hw', rfl⟩ := h
      exact ⟨u, u ^ e' * w', hu, ⟨u, w', hu, hw', rfl⟩, by rw [pow_add, mul_assoc]⟩
    · obtain ⟨u, w', hu, hw', rfl⟩ := h
      exact ⟨u, w', hu, hw', rfl⟩
    · obtain ⟨u', w', hu', hw', rfl⟩ := h
      obtain ⟨u, wl, hu, hwl, rfl⟩ := BsVal.insert_inv hw'
      exact ⟨u, u' ^ e' * wl, hu, ⟨u', wl, hu', hwl, rfl⟩, by ring⟩

theorem BsVal.mul_inv {s : St} : ∀ {a b : List (Base × ℕ)} {w : E}, BsVal s (mulBs a b) w →
    ∃ wa wb, BsVal s a wa ∧ BsVal s b wb ∧ w = wa * wb
  | [], _, w, h => ⟨1, w, rfl, h, by rw [one_mul]⟩
  | (x, e) :: a, b, w, h => by
    obtain ⟨u, wl, hu, hwl, rfl⟩ := BsVal.insert_inv h
    obtain ⟨wa, wb, ha, hb, rfl⟩ := BsVal.mul_inv hwl
    exact ⟨u ^ e * wa, wb, ⟨u, wa, hu, ha, rfl⟩, hb, by ring⟩

theorem MonoVal.mul_inv {s : St} {a b : Mono} {v : E} (h : MonoVal s (a.mul b) v) :
    ∃ va vb, MonoVal s a va ∧ MonoVal s b vb ∧ v = va * vb := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨wa, wb, ha, hb, rfl⟩ := BsVal.mul_inv hw
  refine ⟨_, _, ⟨wa, ha, rfl⟩, ⟨wb, hb, rfl⟩, ?_⟩
  simp only [Mono.mul, pow_add, ofK_mul]
  ring

theorem MonoVal.one_iff {s : St} {v : E} : MonoVal s .one v ↔ v = 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩; rw [show w = 1 from hw]; simp [Mono.one, show ofK (1 : K) = 1 from map_one (algebraMap K E)]
  · rintro rfl; exact MonoVal.one'

theorem MonoVal.npow {s : St} {x : Mono} {u : E} (h : MonoVal s x u) :
    ∀ e, MonoVal s (x.npow e) (u ^ e)
  | 0 => by rw [pow_zero]; exact MonoVal.one'
  | e + 1 => by rw [pow_succ]; exact (MonoVal.npow h e).mul h

theorem MonoVal.npow_inv {s : St} {x : Mono} (e : ℕ) : ∀ {v : E}, 0 < e →
    MonoVal s (x.npow e) v → ∃ u, MonoVal s x u ∧ v = u ^ e := by
  induction e with
  | zero => intro v h; omega
  | succ e ih =>
    intro v _ h
    obtain ⟨va, u, ha, hu, rfl⟩ := MonoVal.mul_inv h
    refine ⟨u, hu, ?_⟩
    rcases Nat.eq_zero_or_pos e with rfl | he
    · rw [(MonoVal.one_iff.mp ha), one_mul, pow_one]
    · obtain ⟨u', hu', rfl⟩ := ih he ha
      obtain rfl := hu'.unique hu
      ring

theorem foldl_none {α β : Type} (f : Option β → α → Option β) (hf : ∀ a, f none a = none) :
    ∀ l : List α, l.foldl f none = none
  | [] => rfl
  | a :: l => by rw [List.foldl_cons, hf]; exact foldl_none f hf l

/-- **A callee's product, translated.** -/
theorem trMono_iff {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A)
    {m m' : Mono} (h : trMono A mq m = some m') (v : E) : MonoVal sE m v ↔ MonoVal sC m' v := by
  have key : ∀ (bs : List (Base × ℕ)) (acc m' : Mono),
      bs.foldl (fun acc p ↦ acc.bind fun acc ↦
        if p.2 == 0 then none else (trBase A mq p.1).map fun x ↦ acc.mul (x.npow p.2)) (some acc) =
        some m' → ∀ w, MonoVal sC m' w ↔ ∃ wa wb, MonoVal sC acc wa ∧ BsVal sE bs wb ∧ w = wa * wb := by
    intro bs
    induction bs with
    | nil =>
      intro acc m' h w
      cases h
      exact ⟨fun h ↦ ⟨w, 1, h, rfl, by rw [mul_one]⟩, fun ⟨wa, wb, h1, h2, h3⟩ ↦ by
        rw [h3, show wb = 1 from h2, mul_one]; exact h1⟩
    | cons p bs ih =>
      intro acc m' h w
      obtain ⟨b, e⟩ := p
      rw [List.foldl_cons] at h
      dsimp only [Option.bind_some] at h
      by_cases he : (e == 0) = true
      · rw [ite_eq_left he, foldl_none _ (fun _ ↦ rfl)] at h; cases h
      rw [ite_eq_right he] at h
      have he' : 0 < e := by simp only [beq_iff_eq] at he; omega
      cases hx : trBase A mq b with
      | none => rw [hx, Option.map_none, foldl_none _ (fun _ ↦ rfl)] at h; cases h
      | some x =>
        rw [hx, Option.map_some] at h
        have hb := trBase_iff F hA hx
        rw [ih _ _ h]
        constructor
        · rintro ⟨wa', wb, h1, h2, rfl⟩
          obtain ⟨wa, ux, h3, h4, rfl⟩ := MonoVal.mul_inv h1
          obtain ⟨u, h5, rfl⟩ := MonoVal.npow_inv e he' h4
          exact ⟨wa, u ^ e * wb, h3, ⟨u, wb, (hb u).mpr h5, h2, rfl⟩, by ring⟩
        · rintro ⟨wa, wb', h1, ⟨u, wb, hu, h2, rfl⟩, rfl⟩
          exact ⟨wa * u ^ e, wb, h1.mul (MonoVal.npow ((hb u).mp hu) e), h2, by ring⟩
  rw [key _ _ _ h]
  have hacc : ∀ wa, MonoVal sC ((mq.npow m.fp).mul (.gp m.k)) wa ↔
      wa = ofK (g ^ sE.fp) ^ m.fp * ofK (g ^ m.k) := fun wa ↦ by
    constructor
    · intro h1
      obtain ⟨va, vb, h2, h3, rfl⟩ := MonoVal.mul_inv h1
      rw [h2.unique (F.mq.npow m.fp), h3.unique (MonoVal.gp m.k)]
    · rintro rfl; exact (F.mq.npow m.fp).mul (MonoVal.gp m.k)
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, w, (hacc _).mpr rfl, hw, rfl⟩
  · rintro ⟨wa, wb, h1, h2, rfl⟩
    rw [(hacc wa).mp h1]
    exact ⟨wb, h2, rfl⟩

/-! ## Exponents and runs, translated -/

theorem MonoVal.base1 {s : St} {k : ℕ} {b : Base} {u : E} :
    MonoVal s ⟨0, k, [(b, 1)]⟩ u ↔ ∃ p, BaseVal s b p ∧ u = ofK (g ^ k) * p := by
  constructor
  · rintro ⟨w, ⟨p, w', hp, hw', rfl⟩, rfl⟩
    exact ⟨p, hp, by rw [show w' = 1 from hw']; simp⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, ⟨p, 1, hp, rfl, by simp⟩, by simp⟩

theorem trIdxK_ex {A : Abs} {mq : Mono} {x : Base} {c : ℕ} {j : Idx} {k : ℕ}
    (h : trIdxK A mq (.ex x c) = some (j, k)) :
    (k = 0 ∧ ∃ k', k' < 2 ^ 62 ∧ trBase A mq x = some ⟨0, k', []⟩ ∧ j = .num (c + k')) ∨
      (k < 2 ^ 62 ∧ ∃ y, trBase A mq x = some ⟨0, k, [(y, 1)]⟩ ∧ j = .ex y (c + k)) := by
  simp only [trIdxK] at h
  split at h
  · rename_i k' hk
    split_ifs at h with h1
    cases h
    exact Or.inl ⟨rfl, k', h1, hk, rfl⟩
  · rename_i k' y hk
    split_ifs at h with h1
    cases h
    exact Or.inr ⟨h1, y, hk, rfl⟩
  · cases h

theorem trIdxK_num {A : Abs} {mq : Mono} {n : ℕ} {j : Idx} {k : ℕ}
    (h : trIdxK A mq (.num n) = some (j, k)) : j = .num n ∧ k = 0 := by
  simp only [trIdxK, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- **A callee's exponent, moved in**: the caller's value is the callee's, when it is below `2^62`
or the base is not shifted. -/
theorem trIdx_down {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A)
    {i j : Idx} {k : ℕ} (h : trIdxK A mq i = some (j, k)) {y : ℕ} (hy : IdxVal sC j y)
    (hs : k = 0 ∨ y < 2 ^ 62) : IdxVal sE i y := by
  cases i with
  | num n =>
    obtain ⟨rfl, -⟩ := trIdxK_num h
    exact hy
  | ex x c =>
    rcases trIdxK_ex h with ⟨rfl, k', hk', hb, rfl⟩ | ⟨hk, y', hb, rfl⟩
    · have hy' : y = c + k' := hy
      exact ⟨_, k', (trBase_iff F hA hb _).mpr (MonoVal.gp k'), rfl, hk', by omega⟩
    · obtain ⟨v, e, hv, rfl, he, rfl⟩ := hy
      refine ⟨ofK (g ^ (k + e)), k + e,
        (trBase_iff F hA hb _).mpr (MonoVal.base1.mpr ⟨_, hv, by rw [pow_add, ofK_mul]⟩), rfl, ?_,
        by omega⟩
      rcases hs with rfl | hs <;> omega

/-- **A callee's exponent, moved out**: the callee's value is the caller's, when the caller's base has
an exponent or the base is not shifted. -/
theorem trIdx_up {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A)
    {i j : Idx} {k : ℕ} (h : trIdxK A mq i = some (j, k)) {x : ℕ} (hx : IdxVal sE i x)
    (hs : k = 0 ∨ ∃ y, IdxVal sC j y) : IdxVal sC j x := by
  cases i with
  | num n =>
    obtain ⟨rfl, -⟩ := trIdxK_num h
    exact hx
  | ex x0 c =>
    rcases trIdxK_ex h with ⟨rfl, k', hk', hb, rfl⟩ | ⟨hk, y', hb, rfl⟩
    · obtain ⟨v, e, hv, rfl, he, rfl⟩ := hx
      have := ofK_gpow_inj (by omega) (by omega) (pow_val ((trBase_iff F hA hb _).mp hv))
      show e + c = c + k'
      omega
    · obtain ⟨v, e, hv, rfl, he, rfl⟩ := hx
      obtain ⟨p, hp, hpe⟩ := MonoVal.base1.mp ((trBase_iff F hA hb _).mp hv)
      have key : ∃ e', p = ofK (g ^ e') ∧ e' < 2 ^ 62 ∧ e = e' + k := by
        rcases hs with rfl | ⟨y0, v', e', hv', rfl, he', -⟩
        · rw [pow_zero, show ofK (1 : K) = 1 from map_one (algebraMap K E), one_mul] at hpe
          exact ⟨e, hpe.symm, he, by omega⟩
        · obtain rfl := hp.unique hv'
          rw [← ofK_mul, ← pow_add] at hpe
          exact ⟨e', rfl, he', by have := ofK_gpow_inj (by omega) (by omega) hpe; omega⟩
      obtain ⟨e', rfl, he', rfl⟩ := key
      exact ⟨_, e', hp, rfl, he', by omega⟩

theorem Idx.small_sound {s : St} {i : Idx} (h : i.small = true) {y : ℕ} (hy : IdxVal s i y) :
    y < 2 ^ 62 := by
  cases i with
  | num n =>
    simp only [Idx.small, decide_eq_true_eq] at h
    rw [show y = n from hy]; exact h
  | ex b c =>
    simp only [Idx.small, beq_iff_eq] at h
    subst h
    obtain ⟨v, e, -, -, he, rfl⟩ := hy
    omega

theorem Abs.small_sound {s : St} {A : Abs} (hA : Holds s A) {j : Idx} (h : A.small j = true) {y : ℕ}
    (hy : IdxVal s j y) : y < 2 ^ 62 := by
  unfold Abs.small at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Idx.small_sound h hy
  · obtain ⟨p, hm, hh⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true] at hh
    obtain ⟨xa, xb, -, hb, -⟩ := hA.lt p hm
    obtain ⟨xa', ha', hle⟩ := Abs.le_sound hA hh.2 hb
    rw [hy.unique ha']
    have := Idx.small_sound hh.1 hb
    omega

theorem idxUp_some {A : Abs} {mq : Mono} {i j : Idx} (h : idxUp A mq i = some j) :
    ∃ k, trIdxK A mq i = some (j, k) ∧ (k = 0 ∨ A.hasIdx j = true) := by
  unfold idxUp at h
  split at h
  · rename_i j' k hk
    split_ifs at h with h1
    cases h
    exact ⟨k, hk, by simpa using h1⟩
  · cases h

theorem idxDown_some {A : Abs} {mq : Mono} {i j : Idx} (h : idxDown A mq i = some j) :
    ∃ k, trIdxK A mq i = some (j, k) ∧ (k = 0 ∨ A.small j = true) := by
  unfold idxDown at h
  split at h
  · rename_i j' k hk
    split_ifs at h with h1
    cases h
    exact ⟨k, hk, by simpa using h1⟩
  · cases h

theorem idxUp_val {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A)
    {i j : Idx} (h : idxUp A mq i = some j) {x : ℕ} (hx : IdxVal sE i x) : IdxVal sC j x := by
  obtain ⟨k, hk, hs⟩ := idxUp_some h
  exact trIdx_up F hA hk hx (hs.imp id (Abs.hasIdx_sound hA))

theorem idxDown_val {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A)
    {i j : Idx} (h : idxDown A mq i = some j) {y : ℕ} (hy : IdxVal sC j y) : IdxVal sE i y := by
  obtain ⟨k, hk, hs⟩ := idxDown_some h
  exact trIdx_down F hA hk hy (hs.imp id fun h ↦ Abs.small_sound hA h hy)

theorem trRngBy_some {A : Abs} {mq : Mono} {tr : Idx → Option Idx} {r r' : Rng}
    (h : trRngBy A mq tr r = some r') : ∃ q lo hi, trMono A mq r.q = some q ∧ tr r.lo = some lo ∧
      tr r.hi = some hi ∧ r' = ⟨q, lo, hi, r.S, r.d⟩ := by
  unfold trRngBy at h
  split at h
  · rename_i q lo hi h1 h2 h3
    cases h
    exact ⟨q, lo, hi, h1, h2, h3, rfl⟩
  · cases h

/-- **A callee's run, moved out.** -/
theorem RW.trUp {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A) {r r' : Rng}
    (h : trRngUp A mq r = some r') (hr : RW sE r) : RW sC r' := by
  obtain ⟨q, lo, hi, hq, hlo, hhi, rfl⟩ := trRngBy_some h
  obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := hr
  exact ⟨vq, xlo, xhi, (trMono_iff F hA hq vq).mp h1, idxUp_val F hA hlo h2, idxUp_val F hA hhi h3,
    fun j a b ↦ F.mem ▸ h4 j a b⟩

/-- **A callee's run, moved in.** -/
theorem RW.trDown {sC sE : St} {A : Abs} {mq : Mono} (F : Frames sC sE mq) (hA : Holds sC A)
    {r r' : Rng} (h : trRngDown A mq r = some r') (hr : RW sC r') : RW sE r := by
  obtain ⟨q, lo, hi, hq, hlo, hhi, rfl⟩ := trRngBy_some h
  obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := hr
  exact ⟨vq, xlo, xhi, (trMono_iff F hA hq vq).mpr h1, idxDown_val F hA hlo h2,
    idxDown_val F hA hhi h3, fun j a b ↦ F.mem ▸ h4 j a b⟩

/-- The own frame, as a callee's. -/
theorem Frames.own {s : St} (hfp : s.fp < maxCells) (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells)
    {e : ℕ} {sE : St} (hm : sE.mem = s.mem) (hE : sE.fp = s.fp + e) (hEfp : sE.fp < maxCells) :
    Frames s sE (.own e) :=
  ⟨hm, by rw [hE]; exact MonoVal.own e, hEfp, hfp, hwf, hu⟩

end

end LeanVM.Guest.Mode
