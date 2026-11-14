module

public import LeanVM.Guest.Mode.SoundOp

/-!
# A `DEREF` of the walk is sound

`stepOp_sound_deref`: through a pointer cell the walk knows written, whose word it knows as a
product `m`, a `DEREF` stores (frame side known written), loads (heap side known written: its
word from `loadVal`, and, through a run of pointers, the cells past it the run promises,
`ptrLoad_sound`), or links; the pointer is nonzero and a power below `maxCells` after it, and
the range-check gadget's bound follows (`rangeFact_sound`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

theorem names_ofK {n X : ℕ} (hn : n < 2 ^ 63) (h : Names (ofK (g ^ n)) X) : X = n :=
  gpow_inj (by have := h.2; unfold maxCells at this; omega) hn (by simpa using h.1.symm)

/-- The frame cell an own product names. -/
theorem own_names {s : St} (hfp : s.fp < maxCells) {k : Mono} {d : ℕ} (hd : k.ownCell = some d)
    {v : E} (hk : MonoVal s k v) {X : ℕ} (hX : Names v X) : X = s.fp + d := by
  obtain ⟨rfl, hd'⟩ := Mono.ownCell_eq hd
  obtain rfl := hk.unique (MonoVal.own d)
  exact names_ofK (by unfold maxCells at hfp; omega) hX

theorem Holds.foldl {s : St} {α : Type} (f : Abs → α → Abs) :
    ∀ (l : List α) {A : Abs}, Holds s A → (∀ A a, a ∈ l → Holds s A → Holds s (f A a)) →
      Holds s (l.foldl f A)
  | [], _, h, _ => h
  | a :: l, A, h, hf => Holds.foldl f l (hf A a (List.mem_cons_self ..) h)
      fun A' a' hm h' ↦ hf A' a' (List.mem_cons_of_mem _ hm) h'

theorem Holds.foldlA {s : St} {α : Type} (f : Abs → α → Abs) (l : List α) {A : Abs} (h : Holds s A)
    (hf : ∀ A a, a ∈ l → Holds s A → Holds s (f A a)) : Holds s (Mode.foldlA f A l) := by
  rw [foldlA_eq]
  exact Holds.foldl f l h hf

theorem Holds.addH_cell {s : St} {A : Abs} (h : Holds s A) (hfp : s.fp < maxCells) {k : Mono} {v : E}
    {x : ℕ} (hk : MonoVal s k v) (hx : Names v x) (hw : s.mem.written x = true) : Holds s (A.addH k) :=
  h.addH ⟨v, x, hk, hx, hw⟩ fun _ hd ↦ by rw [← own_names hfp hd hk hx]; exact hw

/-- The cells `os` past a product's word, each written. -/
theorem Holds.addH_offs {s : St} {B : Abs} (hB : Holds s B) (hfp : s.fp < maxCells) {m : Mono}
    {p : E} (hm : MonoVal s m p) {os : List ℕ}
    (hos : ∀ o ∈ os, ∃ y, Names (p * ofK (g ^ o)) y ∧ s.mem.written y = true) :
    Holds s (Mode.foldlA (fun B o ↦ B.addH (m.shift o)) B os) :=
  Holds.foldlA _ _ hB fun _ o ho hB' ↦ (hos o ho).elim fun _ hy ↦
    hB'.addH_cell hfp (hm.shift o) hy.1 hy.2

/-- **A load from a run of pointers**: the loaded word's cells the run promises are written. -/
theorem ptrLoad_sound {s s' : St} {A B : Abs} {k : Mono} {c : ℕ} (hA : Holds s A)
    (hB : Holds s' B) (hle : s.mem ≤ s'.mem) (hfp : s'.fp < maxCells) {vk : E}
    (hk : MonoVal s k vk) {X : ℕ} (hX : Names vk X) {vX : E}
    (hc : s'.mem.get (s'.fp + c) = some vX) (hget : s.mem.get X = some vX) :
    Holds s' (ptrLoad A k c B) := by
  unfold ptrLoad
  refine Holds.foldlA _ _ hB fun B q hq hB ↦ ?_
  split
  · rename_i hin
    split
    · rename_i m hm
      obtain ⟨x, hx, p, hp, hos⟩ := Abs.inRng_ptr hA (hA.p q hq) hin hk
      obtain rfl := names_inj hx hX
      obtain rfl : p = vX := Option.some.inj (hp.symm.trans hget)
      obtain ⟨u, hu, hmu⟩ := hB.mono_val hm (written_of_get hc)
      rw [hc] at hu; cases hu
      exact hB.addH_offs hfp hmu fun o ho ↦ (hos o ho).elim fun y hy ↦
        ⟨y, hy.1, written_le hle hy.2⟩
    · exact hB
  · exact hB

theorem loadVal_sound {En : Env} {s : St} {A : Abs} (hH : Holds s A) (hE : EnvOk s En)
    (hfp : s.fp < maxCells) {k : Mono} {x : Val} (hl : loadVal En A k = some x) {vk : E}
    (hk : MonoVal s k vk) {X : ℕ} (hX : Names vk X) {vX : E} (hv : s.mem.get X = some vX) :
    ValOk s x vX := by
  unfold loadVal at hl
  split at hl
  · rename_i x' hx
    cases hl
    unfold Abs.hvGet at hx
    split at hx
    · rename_i d hd
      obtain rfl := own_names hfp hd hk hX
      split_ifs at hx with hw
      cases hx
      cases hvd : A.v.get d with
      | none => simp only [Option.getD_none]; exact MonoVal.root hv
      | some y =>
        simp only [Option.getD_some]
        obtain ⟨u, hu, hok⟩ := hH.v d y hvd
        rw [hv] at hu; cases hu; exact hok
    · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hx
      have hm := List.mem_of_find?_eq_some hp
      have hb := List.find?_some hp
      obtain ⟨v', c', w, h1, h2, h3, h4⟩ := hH.hv p hm
      rw [Mono.beq_eq hb] at h1
      obtain rfl := h1.unique hk
      obtain rfl := names_inj h2 hX
      rw [hv] at h3; cases h3; exact h4
  · split at hl
    · rename_i d _
      split_ifs at hl with hj
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hl
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      have hval := hE.2.2 d e hj.1 hj.2 he
      have hjt := hE.2.1
      have : vk = ofK (g ^ d) := pow_val hk
      rw [this] at hX
      obtain rfl := names_ofK (by unfold maxCells at hjt; omega) hX
      rw [hv] at hval; cases hval
      exact MonoVal.gp e
    · rename_i d b _
      split_ifs at hl
      · cases hl
        exact ⟨vk, X, hk, hX, hv⟩
      · split at hl
        · cases hl
          obtain ⟨w, ⟨u, w', hu, hw', rfl⟩, rfl⟩ := hk
          rw [show w' = 1 from hw'] at hX
          refine ⟨vX, ⟨vX, 1, ⟨u, X, hu, ?_, hv⟩, rfl, by simp⟩, by simp⟩
          convert hX using 1
          simp; ring
        · cases hl
    · cases hl

/-- The range check's bound. -/
theorem rangeFact_sound {s : St} {A : Abs} (hH : Holds s A) {y : ℕ} {base : ℕ}
    (hy : s.mem.get (s.fp + y) = some (ofK (g ^ base))) (hb : base < maxCells) :
    Holds s (rangeFact A y) := by
  unfold rangeFact
  split
  · rename_i x y' z l hpr
    have hp := hH.pr _ (by rw [hpr]; exact List.mem_cons_self ..)
    simp only at hp
    obtain ⟨vx, vy, hx, hy', hz⟩ := hp
    split_ifs with hc
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hlt⟩ := hc
      rw [hy] at hy'; cases hy'
      obtain ⟨ex, hex, hexlt⟩ := Abs.ltI_sound hH hlt (show IdxVal s (.num maxCells) maxCells from rfl)
      obtain ⟨u, e', hu, hu', he', hxe⟩ := hex
      have hu2 : s.mem.get (s.fp + x) = some u := hu
      have hvx : vx = ofK (g ^ e') := by rw [hx] at hu2; rw [← hu']; exact Option.some.inj hu2
      have hzm : ∀ m, A.mono z = some m → MonoVal s m (vx * ofK (g ^ base)) := fun m hm ↦ by
        obtain ⟨u2, hu2, hok⟩ := hH.mono_val hm (written_of_get hz)
        rw [hz] at hu2; cases hu2; exact hok
      have h1 : ofK (1 : K) = 1 := map_one (algebraMap K E)
      split
      · rename_i k hz'
        split_ifs with hk
        · refine hH.addLtC ⟨e', k + 1, ⟨_, e', hx, hvx, he', rfl⟩, rfl, ?_⟩
          have := pow_val (hzm _ hz')
          rw [hvx, ← ofK_mul, ← pow_add] at this
          have := ofK_gpow_inj (by unfold maxCells at hexlt hb; omega) (by omega) this
          omega
        · exact hH
      · rename_i k b hz'
        have hok := hzm _ hz'
        obtain ⟨w, ⟨u3, w3, h3, hw3, rfl⟩, h4⟩ := hok
        rw [show w3 = 1 from hw3] at h4
        simp only [pow_zero, one_mul, pow_one, mul_one] at h4
        split_ifs with hk hg
        · rcases Bool.or_eq_true_iff.mp hk with hk | hk
          · obtain rfl := beq_iff_eq.mp hk
            rw [pow_zero, h1, one_mul] at h4
            have hu3 : u3 = ofK (g ^ (e' + base)) := by rw [← h4, hvx, ← ofK_mul, ← pow_add]
            exact hH.addLtC ⟨e', e' + base + (0 + 1), ⟨_, e', hx, hvx, he', rfl⟩,
              ⟨u3, e' + base, h3, hu3, by unfold maxCells at hexlt hb; omega, rfl⟩, by omega⟩
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
            obtain ⟨eb, ⟨ub, eb', hub, hub', heb', hbe⟩, heblt⟩ :=
              Abs.ltI_sound hH hk.2 (show IdxVal s (.num maxCells) maxCells from rfl)
            refine hH.addLtC ⟨e', eb' + (k + 1), ⟨_, e', hx, hvx, he', rfl⟩,
              ⟨ub, eb', hub, hub', heb', rfl⟩, ?_⟩
            obtain rfl := h3.unique hub
            rw [hub'] at h4
            rw [hvx, ← ofK_mul, ← pow_add, ← ofK_mul, ← pow_add] at h4
            have := ofK_gpow_inj (by unfold maxCells at hexlt hb; omega)
              (by unfold maxCells at heblt; omega) h4
            omega
        · obtain rfl := beq_iff_eq.mp hg
          have hu3 : u3 = ofK (g ^ (e' + base + 1)) := by
            have h5 : u3 = vx * ofK (g ^ base) * ofK g := by
              rw [h4, mul_comm (ofK _) u3, mul_assoc, ← ofK_mul, gpow_ginv_mul, h1, mul_one]
            rw [h5, hvx, ← ofK_mul, ← ofK_mul, ← pow_add, ← pow_succ]
          refine hH.addLtC ⟨e', e' + base + 1, ⟨_, e', hx, hvx, he', rfl⟩,
            ⟨u3, e' + base + 1, h3, hu3, by unfold maxCells at hexlt hb; omega, rfl⟩, by omega⟩
        · exact hH
      · exact hH
    · exact hH
  · exact hH

/-- **A `DEREF` the walk accepts.** -/
theorem stepOp_sound_deref {En : Env} {C : Ctx} {s s' : St} {A A' : Abs} {a o c : ℕ}
    {mode : DerefMode} (hs : s.Good) (hfp : s.fp < maxCells) (hpc : s.pc < C.ops.size)
    (hu : s.mem.used ≤ maxCells) (hE : EnvOk s En) (hH : Holds s A)
    (h : stepOp En s.pc A (.deref a o c mode) = some A') :
    s.mem.written (s.fp + a) = true ∧
      (runOp C s (.deref a o c mode) = .ok s' → Holds s' A') := by
  simp only [stepOp] at h
  by_cases ha : A.hasW a = true
  swap
  · rw [ite_eq_right ha] at h; cases h
  rw [ite_eq_left ha] at h
  refine ⟨hH.written ha, fun e ↦ ?_⟩
  split at h
  · cases h
  rename_i m hm
  obtain ⟨g1, g2, g3⟩ := runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
  obtain ⟨p, base, hp, hpb, hbo, hpc', hfp', hcell⟩ := deref_vals hs e
  have hmv : MonoVal s m p := by
    obtain ⟨u, h1, h2⟩ := hH.mono_val hm (hH.written ha)
    rw [hp] at h1; cases h1; exact h2
  have hkv : MonoVal s (m.shift o) (p * ofK (g ^ o)) := hmv.shift o
  have hX : Names (p * ofK (g ^ o)) (base + o) := names_shift (by rw [hpb]; simp) hbo
  have hm' := hH.mono g3 g2
  -- the pointer: nonzero, a power below `maxCells`
  have hp' : s'.mem.get (s'.fp + a) = some p := by rw [g2]; exact g3.get _ _ hp
  have hA0 : Holds s' ((A.addNz a).addLt (.ex (.fr a) 0) (.num maxCells)) :=
    (hm'.addNz ⟨p, hp', by rw [hpb]; exact ofK_gpow_ne_zero _⟩).addLt
      ⟨base, maxCells, ⟨p, base, hp', hpb, by unfold maxCells at hbo; omega, rfl⟩, rfl,
        by omega⟩
  have hA1 : Holds s' (if (o == 0) = true then rangeFact ((A.addNz a).addLt (.ex (.fr a) 0)
      (.num maxCells)) a else (A.addNz a).addLt (.ex (.fr a) 0) (.num maxCells)) := by
    split_ifs
    · exact rangeFact_sound hA0 (by rw [hp', hpb]) (by omega)
    · exact hA0
  have hA2 := Holds.setPr hA1 (l := A.pr) (fun q hq ↦ hm'.pr q hq)
  have hkv' : MonoVal s' (m.shift o) (p * ofK (g ^ o)) := hkv.mono g3 g2
  have hown : ∀ d, (m.shift o).ownCell = some d → base + o = s'.fp + d := fun d hd ↦ by
    rw [g2]; exact own_names hfp hd hkv hX
  cases mode with
  | pc =>
    cases h
    have hw := hpc' rfl
    refine Holds.setPr ?_ (fun _ h ↦ nomatch h)
    refine (hA2.addH ⟨_, base + o, hkv', hX, written_of_get hw⟩ fun d hd ↦ ?_).addHv
      ⟨_, base + o, _, hkv', hX, hw, MonoVal.gp _⟩ fun d hd ↦ ⟨_, by rw [← hown d hd]; exact hw,
        MonoVal.gp _⟩
    rw [← hown d hd]; exact written_of_get hw
  | fp =>
    cases h
    have hw := hfp' rfl
    have hval : ValOk s' (.m (.own 0)) (ofK (g ^ s.fp)) := by
      have := MonoVal.own (s := s') 0
      rw [g2, Nat.add_zero] at this; exact this
    refine Holds.setPr ?_ (fun _ h ↦ nomatch h)
    refine (hA2.addH ⟨_, base + o, hkv', hX, written_of_get hw⟩ fun d hd ↦ ?_).addHv
      ⟨_, base + o, _, hkv', hX, hw, hval⟩ fun d hd ↦ ⟨_, by rw [← hown d hd]; exact hw, hval⟩
    rw [← hown d hd]; exact written_of_get hw
  | cell =>
    obtain ⟨hld, hst⟩ := hcell rfl
    by_cases hc : A.hasW c = true
    · rw [ite_eq_left hc] at h
      cases h
      obtain ⟨vc, hvc⟩ := Mem.get_of_written (hH.written hc)
      have hw := hst vc hvc
      have hval : ValOk s' ((A.v.get c).getD (.m (.root c))) vc := by
        cases hx : A.v.get c with
        | none =>
          simp only [Option.getD_none]
          exact MonoVal.root (by rw [g2]; exact g3.get _ _ hvc)
        | some y =>
          simp only [Option.getD_some]
          obtain ⟨u, h1, h2⟩ := hH.v c y hx
          rw [hvc] at h1; cases h1; exact h2.mono g3 g2
      refine Holds.setPr ?_ (fun q hq ↦ hm'.pr q hq)
      refine (hA2.addH ⟨_, base + o, hkv', hX, written_of_get hw⟩ fun d hd ↦ ?_).addHv
        ⟨_, base + o, _, hkv', hX, hw, hval⟩ fun d hd ↦ ⟨_, by rw [← hown d hd]; exact hw, hval⟩
      rw [← hown d hd]; exact written_of_get hw
    rw [ite_eq_right hc] at h
    by_cases hcov : A.covered (m.shift o) = true
    · rw [ite_eq_left hcov] at h
      cases h
      have hwX := Abs.covered_sound hH hs.wf hu hcov hkv hX
      obtain ⟨vX, hvX⟩ := Mem.get_of_written hwX
      have hw := hld vX hvX
      refine Holds.setPr ?_ (fun q hq ↦ hm'.pr q hq)
      have hA3 := hA2.addW (o := c) (by rw [g2]; exact written_of_get hw)
      refine ptrLoad_sound hH ?_ g3 (by rw [g2]; exact hfp) hkv hX (by rw [g2]; exact hw) hvX
      split
      · rename_i x hx
        exact hA3.addV ⟨vX, by rw [g2]; exact hw, (loadVal_sound hH hE hfp hx hkv hX hvX).mono g3 g2⟩
      · exact hA3
    · rw [ite_eq_right hcov] at h
      cases h
      exact hA2

end

end LeanVM.Guest.Mode
