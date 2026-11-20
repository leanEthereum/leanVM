module

public import LeanVM.Guest.Mode.SoundStep

/-!
# Words an instruction's immediates name

`pow_val`, `immNz_ne`, `ofBits_ne_zero_of`: the powers of `g` and the nonzero words an instruction's
immediates name; `Holds.quotC`: a quotient the domain records.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

theorem PowTree.find_ok' {t : Exec.PowTree} (ht : t.Ok) {k e : ℕ} (h : t.find k = some e) :
    K.ofBits k = addressOfIndex e := by
  induction t with
  | leaf => exact absurd h (by simp [Exec.PowTree.find])
  | node k' e' l r ihl ihr =>
    have hf : (Exec.PowTree.node k' e' l r).find k =
        (bif k == k' then some e' else bif Nat.blt k k' then l.find k else r.find k) := rfl
    rw [hf] at h
    simp only [Bool.cond_eq_ite, beq_iff_eq] at h
    split_ifs at h with h1 h2
    · subst h1
      obtain rfl := Option.some.inj h
      exact ht.1
    · exact ihl ht.2.1 h
    · exact ihr ht.2.2 h

theorem imm_of_ofBits' {k : ℕ} {a : K} (h : K.ofBits k = a) :
    OffsetInstruction.immediateWord k 0 = ofK a := by
  rw [OffsetInstruction.immediateWord, h, ofK_eq_ofLimbs]
  rfl

theorem pow_val {s : St} {e : ℕ} {u : E} (h : MonoVal s ⟨0, e, []⟩ u) : u = ofK (g ^ e) := by
  obtain ⟨w, hw, rfl⟩ := h
  rw [show w = 1 from hw]; simp

theorem ofK_gpow_ne_zero (e : ℕ) : ofK (g ^ e) ≠ 0 :=
  (map_ne_zero (algebraMap K E)).mpr (pow_ne_zero _ g_ne_zero)

theorem Abs.zImp_sound {s : St} {A : Abs} (hH : Holds s A) {b x : ℕ} (h : A.zImp b x = true) {u w : E}
    (hb : s.mem.get (s.fp + b) = some u) (hx : s.mem.get (s.fp + x) = some w) (hu : u = 0) : w = 0 := by
  unfold Abs.zImp at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain rfl := beq_iff_eq.mp h
    obtain rfl := Option.some.inj (hb.symm.trans hx)
    exact hu
  · obtain ⟨⟨p, q, r⟩, hm, hc⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨vx, vy, h1, h2, h3⟩ := hH.pr _ hm
    obtain ⟨rfl, hc⟩ := hc
    obtain rfl := Option.some.inj (hb.symm.trans h3)
    rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hp⟩
    · obtain ⟨u', hu', hne⟩ := hH.nzAt hq
      obtain rfl := Option.some.inj (h2.symm.trans hu')
      obtain rfl := Option.some.inj (h1.symm.trans hx)
      exact (mul_eq_zero.mp hu).resolve_right hne
    · obtain ⟨u', hu', hne⟩ := hH.nzAt hp
      obtain rfl := Option.some.inj (h1.symm.trans hu')
      obtain rfl := Option.some.inj (h2.symm.trans hx)
      exact (mul_eq_zero.mp hu).resolve_left hne

/-- A back-solved `MUL`'s divisor is nonzero after it. -/
theorem ZNz.ne {s : St} {m' : Mem} {x c : ℕ} (hz : ZNz s x c) (hle : s.mem ≤ m') {vx vy : E}
    (hx : m'.get (s.fp + x) = some vx) (hc : m'.get (s.fp + c) = some (vx * vy)) : vx ≠ 0 := by
  obtain ⟨u, v, hu, hv, huv⟩ := hz
  obtain rfl := Option.some.inj ((hle.get _ _ hu).symm.trans hx)
  obtain rfl := Option.some.inj ((hle.get _ _ hv).symm.trans hc)
  exact fun h0 ↦ huv h0 (by rw [h0, zero_mul])

theorem ofBits_ne_zero_of {n : ℕ} (h0 : n ≠ 0) (hn : n < 2 ^ 64) : K.ofBits n ≠ 0 := fun h ↦ by
  have h' : K.ofBits n = K.ofBits 0 := h.trans (by decide +kernel)
  have := congrArg (fun z : K ↦ z.toBitVec.toNat) h'
  simp only [K.ofBits, BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt hn] at this
  exact h0 (by simpa using this)

theorem immNz_ne {k0 k1 : ℕ} (h : immNz k0 k1 = true) : OffsetInstruction.immediateWord k0 k1 ≠ 0 := by
  intro hz
  have h0 := congrArg (fun x : E ↦ x.limb 0) hz
  have h1 := congrArg (fun x : E ↦ x.limb 1) hz
  simp only [OffsetInstruction.immediateWord, limb_ofLimbs, limb_zero] at h0 h1
  simp only [immNz, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · exact ofBits_ne_zero_of a b (by simpa using h0)
  · exact ofBits_ne_zero_of a b (by simpa using h1)

/-- **A quotient's exponent**: `[u]` with `[c] = [k]·[u]` and `[c] = g^C`, under `k`'s exponent `j`, has
exponent `C - j`. -/
theorem Holds.quotC {s : St} {A : Abs} (hA : Holds s A) {k u c : ℕ} {vk vu : E}
    (hk : s.mem.get (s.fp + k) = some vk) (hu : s.mem.get (s.fp + u) = some vu)
    (hc : s.mem.get (s.fp + c) = some (vk * vu)) : Holds s (A.quotC k u c) := by
  unfold Abs.quotC
  split
  · rename_i C b hv hb
    split_ifs with hcb
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcb
      obtain ⟨hC, hbC⟩ := hcb
      unfold qMax at hC
      obtain ⟨w, hw, hwv⟩ := hA.v c _ hv
      rw [hc] at hw
      cases hw
      have hw' : vk * vu = ofK (g ^ C) := pow_val hwv
      exact { hA with
        c := fun q hq ↦ by
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨j, hj, hq⟩ := List.mem_filterMap.mp hq
            split_ifs at hq
            cases hq
            refine ⟨⟨vk, hk⟩, fun hix ↦ ?_⟩
            obtain ⟨v, e, hv1, rfl, he, hje⟩ := hix
            have hvk : vk = ofK (g ^ e) := Option.some.inj (hk.symm.trans hv1)
            have hjb : j ≤ C := by have := List.mem_range.mp hj; omega
            have hvu : vu = ofK (g ^ (C - j)) := by
              refine mul_left_cancel₀ (ofK_gpow_ne_zero j) ?_
              rw [← ofK_mul, ← pow_add, show j + (C - j) = C by omega, ← hw', hvk]
              simp only [Nat.add_zero] at hje
              rw [hje]
            have hi0 : IdxVal s (.ex (.fr u) 0) (C - j) := ⟨vu, C - j, hu, hvu, by omega, rfl⟩
            have hi1 : IdxVal s (.ex (.fr u) 1) (C - j + 1) := ⟨vu, C - j, hu, hvu, by omega, rfl⟩
            refine ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h, fun _ h ↦ by simp at h, fun p hp ↦ ?_,
              fun _ h ↦ by simp at h⟩
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨C - j, C - j + 1, hi0, rfl, by omega⟩
            · rcases List.mem_singleton.mp hp with rfl
              exact ⟨C - j, C - j + 1, rfl, hi1, by omega⟩
          · exact hA.c q hq }
    · exact hA
  · exact hA

end

end LeanVM.Guest.Mode
