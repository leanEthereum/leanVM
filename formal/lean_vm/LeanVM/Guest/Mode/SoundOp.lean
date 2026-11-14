module

public import LeanVM.Guest.Mode.SoundStep

/-!
# One instruction of the walk is sound

`stepOp_sound`: from a state where the walk's set `A` holds, an instruction the walk accepts reads
written cells (`Reads`: with the reference's part, `OpModed`), and, unless it is a `JUMP`, leaves a
state where the walk's next set holds.
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

theorem gpow_ginv_mul : g ^ (2 ^ 64 - 2) * g = 1 := by
  rw [← pow_succ, show 2 ^ 64 - 2 + 1 = 2 ^ 64 - 1 by norm_num, g_pow_card_sub_one]

theorem ofBits_ginv : K.ofBits ginvBits = g ^ (2 ^ 64 - 2) :=
  mul_right_cancel₀ g_ne_zero ((show K.ofBits ginvBits * g = 1 by decide +kernel).trans gpow_ginv_mul.symm)

/-- A `SET` immediate's known word holds of it; a product among them is a power, nonzero. -/
theorem valOfImm_ok {s : St} {En : Env} (hp : En.pows.Ok) (k0 k1 : ℕ) :
    ValOk s (valOfImm En k0 k1) (OffsetInstruction.immediateWord k0 k1) ∧
      ((∃ x, valOfImm En k0 k1 = .m x) → OffsetInstruction.immediateWord k0 k1 ≠ 0) := by
  unfold valOfImm
  by_cases h1 : (k1 == 0) = true
  · rw [ite_eq_left h1]
    obtain rfl := beq_iff_eq.mp h1
    by_cases h0 : (k0 == 1) = true
    · rw [ite_eq_left h0]
      obtain rfl := beq_iff_eq.mp h0
      have hw : OffsetInstruction.immediateWord 1 0 = 1 := by
        rw [imm_of_ofBits' (a := 1) rfl]; exact map_one (algebraMap K E)
      refine ⟨by rw [hw]; exact MonoVal.one', fun _ ↦ by rw [hw]; exact one_ne_zero⟩
    · rw [ite_eq_right h0]
      by_cases hg : (k0 == ginvBits) = true
      · rw [ite_eq_left hg]
        obtain rfl := beq_iff_eq.mp hg
        have hw := imm_of_ofBits' ofBits_ginv
        exact ⟨by rw [hw]; exact MonoVal.gp _, fun _ ↦ by
          rw [hw]; exact (map_ne_zero (algebraMap K E)).mpr (pow_ne_zero _ g_ne_zero)⟩
      rw [ite_eq_right hg]
      split
      · rename_i e he
        have hw := imm_of_ofBits' (PowTree.find_ok' hp he)
        refine ⟨by rw [hw]; exact MonoVal.gp e, fun _ ↦ by
          rw [hw]; exact (map_ne_zero (algebraMap K E)).mpr (pow_ne_zero _ g_ne_zero)⟩
      · exact ⟨rfl, fun ⟨_, h⟩ ↦ Val.noConfusion h⟩
  · rw [ite_eq_right h1]
    exact ⟨rfl, fun ⟨_, h⟩ ↦ Val.noConfusion h⟩

theorem mono_get {s : St} {A : Abs} (hH : Holds s A) {o : ℕ} {x : Mono} (h : A.mono o = some x)
    (hw : A.hasW o = true) {s' : St} (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) {u : E}
    (hu : s'.mem.get (s'.fp + o) = some u) : MonoVal s' x u := by
  obtain ⟨u', h1, h2⟩ := hH.mono_val h (hH.written hw)
  rw [hfp] at hu
  obtain rfl := Option.some.inj ((hle.get _ _ h1).symm.trans hu)
  exact h2.mono hle hfp

theorem pow_val {s : St} {e : ℕ} {u : E} (h : MonoVal s ⟨0, e, []⟩ u) : u = ofK (g ^ e) := by
  obtain ⟨w, hw, rfl⟩ := h
  rw [show w = 1 from hw]; simp

theorem ofK_gpow_ne_zero (e : ℕ) : ofK (g ^ e) ≠ 0 :=
  (map_ne_zero (algebraMap K E)).mpr (pow_ne_zero _ g_ne_zero)

theorem Abs.isOne_sound {s : St} {A : Abs} (hH : Holds s A) {o : ℕ} (h : A.isOne o = true) :
    s.mem.get (s.fp + o) = some 1 := by
  unfold Abs.isOne at h
  split at h
  · rename_i hv
    obtain ⟨u, hu, hok⟩ := hH.v o _ hv
    rw [pow_val hok, pow_zero, show ofK (1 : K) = 1 from map_one (algebraMap K E)] at hu
    exact hu
  · cases h

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

/-- **A back-solve's divisor**: where the walk's `zNz` holds, the divisor zero makes the product
nonzero. -/
theorem Abs.zNz_sound {s : St} {A : Abs} (hH : Holds s A) {b c : ℕ} (hb : s.mem.written (s.fp + b) = true)
    (hc : s.mem.written (s.fp + c) = true) (h : A.zNz b c = true) : ZNz s b c := by
  obtain ⟨u, hu⟩ := Mem.get_of_written hb
  obtain ⟨v, hv⟩ := Mem.get_of_written hc
  refine ⟨u, v, hu, hv, fun hu0 ↦ ?_⟩
  unfold Abs.zNz at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain ⟨u', hu', hne⟩ := hH.nzAt h
      obtain rfl := Option.some.inj (hu.symm.trans hu')
      exact absurd hu0 hne
    · obtain ⟨v', hv', hne⟩ := hH.nzAt h
      obtain rfl := Option.some.inj (hv.symm.trans hv')
      exact hne
  · split at h
    · rename_i o x hx
      obtain ⟨vo, vx, ho, hx', hc'⟩ := hH.xs c o x hx
      obtain rfl := Option.some.inj (hv.symm.trans hc')
      rcases Bool.or_eq_true_iff.mp h with h | h
      · simp only [Bool.and_eq_true] at h
        obtain rfl := Option.some.inj (ho.symm.trans (Abs.isOne_sound hH h.1))
        rw [Abs.zImp_sound hH h.2 hu hx' hu0, add_zero]
        exact one_ne_zero
      · simp only [Bool.and_eq_true] at h
        obtain rfl := Option.some.inj (hx'.symm.trans (Abs.isOne_sound hH h.1))
        rw [Abs.zImp_sound hH h.2 hu ho hu0, zero_add]
        exact one_ne_zero
    · cases h

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

/-- **An `XOR`, `MUL`, `SET` or `KECCAK` the walk accepts.** -/
theorem stepOp_sound_nj {En : Env} {C : Ctx} {s s' : St} {A A' : Abs} {ins : OffsetInstruction}
    (hs : s.Good) (hfp : s.fp < maxCells) (hpc : s.pc < C.ops.size) (hE : EnvOk s En)
    (hH : Holds s A) (h : stepOp En s.pc A ins = some A')
    (hk : ∀ a o c mode, ins ≠ .deref a o c mode) (hj : ∀ c d f, ins ≠ .jump c d f) :
    Reads s (opOfOff ins) ∧ (runOp C s (opOfOff ins) = .ok s' → Holds s' A') := by
  cases ins with
  | xor a b c =>
    simp only [stepOp, Bool.and_eq_true] at h
    split_ifs at h with hc
    cases h
    refine ⟨⟨hH.written hc.1, hH.written hc.2⟩, fun e ↦ ?_⟩
    obtain ⟨h1, h2, h3⟩ := runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    have hm := hH.mono h3 h2
    have hW := hm.addW (o := c) (by rw [h2]; exact runOp_writes (k := 0) hs (Or.inl rfl) e)
    have hX : ∀ c' a' b', (addSum A.xs c a b).get c' = some (a', b') → XorF s' a' b' c' := by
      intro c' a' b' hc'
      unfold addSum at hc'
      split at hc'
      · exact hm.xs c' a' b' hc'
      · rcases Exec.Trie.get_set hc' with ⟨rfl, he⟩ | hc'
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          obtain ⟨va, vb, ha, hb, hc'⟩ := xor_vals hs e
          exact ⟨va, vb, by rw [h2]; exact h3.get _ _ ha, by rw [h2]; exact h3.get _ _ hb,
            by rw [h2]; exact hc'⟩
        · exact hm.xs c' a' b' hc'
    refine Holds.setPrXs (l := []) ?_ (fun _ h ↦ nomatch h) hX
    split
    · rename_i x y hx hy
      split_ifs with hxy
      · simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] at hxy
        refine hW.addNz ?_
        obtain ⟨va, vb, ha, hb, hc'⟩ := xor_vals hs e
        have hva := pow_val ((hH.mono_val hx (hH.written hc.1)).elim fun u ⟨h4, h5⟩ ↦ by
          rw [ha] at h4; cases h4; exact h5)
        have hvb := pow_val ((hH.mono_val hy (hH.written hc.2)).elim fun u ⟨h4, h5⟩ ↦ by
          rw [hb] at h4; cases h4; exact h5)
        refine ⟨va + vb, by rw [h2]; exact hc', fun hz ↦ hxy.1.1 ?_⟩
        have : va = vb := by rw [← sub_eq_zero, CharTwo.sub_eq_add]; exact hz
        rw [hva, hvb] at this
        exact ofK_gpow_inj (by have := hxy.1.2; omega) (by have := hxy.2; omega) this
      · exact hW
    · exact hW
  | mul a b c =>
    simp only [stepOp] at h
    by_cases h1 : (A.hasW a && A.hasW b) = true
    · rw [ite_eq_left h1] at h
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true] at h1
      refine ⟨Or.inl ⟨hH.written h1.1, hH.written h1.2⟩, fun e ↦ ?_⟩
      obtain ⟨g1, g2, g3⟩ := runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
      obtain ⟨va, vb, ha, hb, hc⟩ := mul_vals hs e
      rw [← g2] at ha hb hc
      have hm := hH.mono g3 g2
      have hW := hm.addW (o := c) (written_of_get hc)
      refine Holds.setPr ?_ (fun p hp ↦ by
        rcases List.mem_singleton.mp hp with rfl
        exact ⟨va, vb, ha, hb, hc⟩)
      have hV : Holds s' (match A.mono a, A.mono b with
          | some x, some y => (A.addW c).addV c (.m (x.mul y))
          | _, _ => A.addW c) := by
        split
        · rename_i x y hx hy
          exact hW.addV ⟨_, hc, MonoVal.mul (mono_get hH hx h1.1 g3 g2 ha)
            (mono_get hH hy h1.2 g3 g2 hb)⟩
        · exact hW
      by_cases hn : (A.hasNz a && A.hasNz b) = true
      · rw [ite_eq_left hn]
        simp only [Bool.and_eq_true] at hn
        refine hV.addNz ⟨_, hc, mul_ne_zero ?_ ?_⟩
        · obtain ⟨u, hu, hne⟩ := hH.nzAt hn.1
          rw [g2] at ha
          rw [g3.get _ _ hu] at ha; cases ha; exact hne
        · obtain ⟨u, hu, hne⟩ := hH.nzAt hn.2
          rw [g2] at hb
          rw [g3.get _ _ hu] at hb; cases hb; exact hne
      · rw [ite_eq_right hn]; exact hV
    rw [ite_eq_right h1] at h
    by_cases h2 : (A.hasW c && A.hasW a && A.zNz a c) = true
    · rw [ite_eq_left h2] at h
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true] at h2
      have hz := Abs.zNz_sound hH (hH.written h2.1.2) (hH.written h2.1.1) h2.2
      refine ⟨Or.inr (Or.inl ⟨hH.written h2.1.1, hH.written h2.1.2, hz⟩), fun e ↦ ?_⟩
      obtain ⟨g1, g2, g3⟩ := runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
      obtain ⟨va, vb, ha, hb, hc⟩ := mul_vals hs e
      have hva := hz.ne g3 ha hc
      rw [← g2] at ha hb hc
      have hm := hH.mono g3 g2
      have hW := (hm.addW (o := b) (written_of_get hb)).addNz ⟨va, ha, hva⟩
      refine Holds.setPr ?_ (fun p hp ↦ by
        rcases List.mem_singleton.mp hp with rfl
        exact ⟨va, vb, ha, hb, hc⟩)
      by_cases hn : A.hasNz c = true
      · rw [ite_eq_left hn]
        refine hW.addNz ⟨vb, hb, fun hz ↦ ?_⟩
        obtain ⟨u, hu, hne⟩ := hH.nzAt hn
        rw [g2] at hc
        rw [g3.get _ _ hu, hz, mul_zero] at hc; cases hc; exact hne rfl
      · rw [ite_eq_right hn]; exact hW
    rw [ite_eq_right h2] at h
    by_cases h3 : (A.hasW c && A.hasW b && A.zNz b c) = true
    · rw [ite_eq_left h3] at h
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true] at h3
      have hz := Abs.zNz_sound hH (hH.written h3.1.2) (hH.written h3.1.1) h3.2
      refine ⟨Or.inr (Or.inr ⟨hH.written h3.1.1, hH.written h3.1.2, hz⟩), fun e ↦ ?_⟩
      obtain ⟨g1, g2, g3⟩ := runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
      obtain ⟨va, vb, ha, hb, hc⟩ := mul_vals hs e
      have hvb := hz.ne g3 hb (by rw [mul_comm]; exact hc)
      rw [← g2] at ha hb hc
      have hm := hH.mono g3 g2
      have hW := (hm.addW (o := a) (written_of_get ha)).addNz ⟨vb, hb, hvb⟩
      refine Holds.setPr ?_ (fun p hp ↦ by
        rcases List.mem_singleton.mp hp with rfl
        exact ⟨va, vb, ha, hb, hc⟩)
      by_cases hn : A.hasNz c = true
      · rw [ite_eq_left hn]
        refine hW.addNz ⟨va, ha, fun hz ↦ ?_⟩
        obtain ⟨u, hu, hne⟩ := hH.nzAt hn
        rw [g2] at hc
        rw [g3.get _ _ hu, hz, zero_mul] at hc; cases hc; exact hne rfl
      · rw [ite_eq_right hn]; exact hW
    rw [ite_eq_right h3] at h
    cases h
  | set o k0 k1 =>
    simp only [stepOp] at h
    cases h
    refine ⟨trivial, fun e ↦ ?_⟩
    obtain ⟨g1, g2, g3⟩ := runOp_next hs hfp hpc e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    have hv := set_vals hs e
    rw [← g2] at hv
    obtain ⟨hok, hnz⟩ := valOfImm_ok (s := s') hE.1 k0 k1
    have hm := hH.mono g3 g2
    have hA := (hm.addW (written_of_get hv)).addV (o := o) ⟨_, hv, hok⟩
    have hB : Holds s' (match valOfImm En k0 k1 with
        | .m _ => ((A.addW o).addV o (valOfImm En k0 k1)).addNz o
        | _ => if immNz k0 k1 then ((A.addW o).addV o (valOfImm En k0 k1)).addNz o
          else (A.addW o).addV o (valOfImm En k0 k1)) := by
      split
      · rename_i x hx
        exact hA.addNz ⟨_, hv, hnz ⟨x, hx⟩⟩
      · split_ifs with hi
        · exact hA.addNz ⟨_, hv, immNz_ne hi⟩
        · exact hA
    refine Holds.setPr ?_ (fun _ h ↦ nomatch h)
    split
    · rename_i x i p l hpr
      by_cases hc : (p == o && k0 == 1 && k1 == 0) = true
      · rw [ite_eq_left hc]
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
        obtain ⟨vx, vi, hx, hi, hp⟩ := hH.pr _ (by rw [hpr]; exact List.mem_cons_self ..)
        simp only at hx hi hp
        have hone : OffsetInstruction.immediateWord 1 0 = 1 := by
          rw [imm_of_ofBits' (a := 1) rfl]; exact map_one (algebraMap K E)
        rw [g2] at hv
        rw [g3.get _ _ hp, hone] at hv
        have h1 : vx * vi = 1 := Option.some.inj hv
        exact (hB.addNz ⟨vx, by rw [g2]; exact g3.get _ _ hx, left_ne_zero_of_mul_eq_one h1⟩).addNz
          ⟨vi, by rw [g2]; exact g3.get _ _ hi, right_ne_zero_of_mul_eq_one h1⟩
      · rw [ite_eq_right hc]; exact hB
    · exact hB
  | deref a o c mode => exact absurd rfl (hk a o c mode)
  | jump c d f => exact absurd rfl (hj c d f)
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    simp only [stepOp] at h
    split_ifs at h with hall
    cases h
    refine ⟨fun i hi ↦ ?_, fun e ↦ ?_⟩
    · have hi' : i ∈ keccakIns m0 m1 m2 m3 tail b8 cap := by simpa using hi
      exact hH.written (List.all_eq_true.mp hall i hi')
    · obtain ⟨g3, g2, -, hw⟩ := keccak_writes hs e
      have hm := hH.mono g3 g2
      refine Holds.setPr ?_ (fun _ h ↦ nomatch h)
      have : ∀ (n : ℕ) (B : Abs), Holds s' B → (∀ j < n, j < outCells.cellCount) →
          Holds s' ((List.range n).foldl (fun A j ↦ A.addW (out + j)) B) := by
        intro n
        induction n with
        | zero => exact fun B hB _ ↦ hB
        | succ n ih =>
          intro B hB hn
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact (ih B hB fun j hj ↦ hn j (by omega)).addW (by rw [g2]; exact hw n (hn n (by omega)))
      rw [foldlA_eq]
      exact this _ A hm fun j hj ↦ hj

end

end LeanVM.Guest.Mode
