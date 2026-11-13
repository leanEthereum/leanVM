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

end

end LeanVM.Guest.Mode
