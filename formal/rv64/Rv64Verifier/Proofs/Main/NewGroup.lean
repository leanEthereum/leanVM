import Rv64Verifier.Proofs.Main.NewProbe3

/-!
# `group`'s loop

One position (`group_pos`, from `0x800005b4`): its word loaded, a zero word skipped, a nonzero one
probed (`probe_first`) and its group stored to `group_of` (`group_store`, `0x80000594`); then on
(`group_adv`, `0x800005a8`) to the next position or out of the loop at `0x8000064c`. Every prefix
of `groupRust`'s fold is `some` (`gfold_some`, as in `Model.groupRust_spec`), so the probe is.
`group_loop`: from `GH` at `0` to the loop's exit with `gfold` over the whole block.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

theorem groupFold_spec (block : List (BitVec 64)) (hb : block.length ≤ 2 ^ 14)
    (slots : List (Option (BitVec 16))) (hs : slots.length = 2 ^ 15) (groupOf : List (BitVec 16))
    (hg : block.length ≤ groupOf.length) : ∀ q ≤ block.length, ∃ st,
      (List.range q).foldl (Model.groupStepRust block) (some (slots.map fun _ ↦ none, groupOf, [])) =
        some st ∧ Model.GroupInv block groupOf.length q st := by
  intro q hq
  induction q with
  | zero =>
    refine ⟨_, rfl, ⟨by rw [List.length_map, hs], ?_, rfl, Nat.zero_le _,
      fun p hp ↦ absurd hp (Nat.not_lt_zero _)⟩⟩
    rw [Model.occupied, List.countP_eq_zero.mpr (fun a ha ↦ ?_)]
    · rfl
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
      simp
  | succ q ih =>
    obtain ⟨st, hst, hinv⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, hst, List.foldl_cons, List.foldl_nil,
      Model.groupStepRust, Option.bind_some]
    by_cases hz : block.getD q 0 = 0
    · rw [ite_eq_left hz]
      refine ⟨st, rfl, ⟨hinv.slots_len, hinv.occupied_eq, hinv.groupOf_len, by
        have := hinv.distinct_le; omega, fun p hp hp0 ↦ ?_⟩⟩
      rcases (show p < q ∨ p = q by omega) with hp' | rfl
      · exact hinv.group p hp' hp0
      · exact absurd hz hp0
    · rw [ite_eq_right hz]
      have hL : 0 < st.1.length := by rw [hinv.slots_len]; norm_num
      have hslot : Model.slotOfRust (block.getD q 0) < st.1.length := by
        rw [hinv.slots_len]; exact Model.slotOfRust_lt _
      have hqg : q < st.2.1.length := by rw [hinv.groupOf_len]; omega
      cases hpr : Model.probeRust (block.getD q 0) st.2.2 st.1 st.1.length
          (Model.slotOfRust (block.getD q 0)) with
      | none =>
        exfalso
        have hall := Model.all_occupied st.1 _ hslot
          (Model.probe_none _ _ _ hL _ _ hslot hpr)
        rw [hinv.occupied_eq, hinv.slots_len] at hall
        have := hinv.distinct_le
        omega
      | some r =>
        refine ⟨_, rfl, ?_⟩
        show Model.GroupInv block groupOf.length (q + 1) (r.1, st.2.1.set q r.2.2, r.2.1)
        rcases Model.probe_some _ hz _ _ hL _ _ r hslot hpr with
          ⟨h1, h2, h3, h4⟩ | ⟨t, ht, htn, h1, h2, h3⟩
        · refine ⟨by rw [h1]; exact hinv.slots_len, by rw [h1, h2]; exact hinv.occupied_eq,
            by rw [List.length_set]; exact hinv.groupOf_len, by
              rw [h2]; dsimp only; have := hinv.distinct_le; omega, fun p hp hp0 ↦ ?_⟩
          rw [h2, Model.getD_set_eq]
          rcases (show p < q ∨ p = q by omega) with hp' | rfl
          · rw [ite_eq_right (fun h ↦ by omega)]
            exact hinv.group p hp' hp0
          · rw [ite_eq_left ⟨rfl, hqg⟩]
            exact ⟨h3, h4⟩
        · have hd := hinv.distinct_le
          have hdl : st.2.2.length < 2 ^ 14 := by omega
          refine ⟨by rw [h1, List.length_set]; exact hinv.slots_len, ?_,
            by rw [List.length_set]; exact hinv.groupOf_len, by rw [h2]; simp; omega,
            fun p hp hp0 ↦ ?_⟩
          · have htn' : st.1[t] = none := by rwa [List.getD_eq_getElem _ _ ht] at htn
            rw [h1, h2, Model.occupied, List.countP_set ht, htn', ← Model.occupied,
              hinv.occupied_eq]
            simp
          · rw [h2, Model.getD_set_eq]
            rcases (show p < q ∨ p = q by omega) with hp' | rfl
            · rw [ite_eq_right (fun h ↦ by omega)]
              obtain ⟨g1, g2⟩ := hinv.group p hp' hp0
              refine ⟨by rw [List.length_append, List.length_singleton]; omega, ?_⟩
              rw [List.getD_append _ _ _ _ g1, g2]
            · rw [ite_eq_left ⟨rfl, hqg⟩, h3, Model.toNat_newGroup hdl]
              simp

theorem gfold_succ (words : List Word) (i : Nat) (st : Model.NewState) (q : Nat) :
    gfold words i st (q + 1) = Model.groupStepRust (blk words i) (gfold words i st q) q := by
  simp only [gfold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem blk_length {words : List Word} {i : Nat} (hlen : (words.getD 0 0).toNat + 1 ≤ words.length) :
    (blk words i).length = min ((words.getD 0 0).toNat - 2 ^ 14 * i) (2 ^ 14) := by
  simp only [blk, tbl, List.length_take, List.length_drop]
  omega

theorem blk_getD {words : List Word} {i q : Nat} (hq : q < 2 ^ 14)
    (hn : 2 ^ 14 * i + q < (words.getD 0 0).toNat) (hlen : (words.getD 0 0).toNat + 1 ≤ words.length) :
    (blk words i).getD q 0 = words[1 + 2 ^ 14 * i + q]'(by omega) := by
  rw [List.getD_eq_getElem?_getD]
  simp only [blk, tbl, List.getElem?_take, List.getElem?_drop, hq, ↓reduceIte,
    show i * 2 ^ 14 + q < (words.getD 0 0).toNat by omega]
  rw [List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  congr 1
  omega

/-- A halfword store at `P + 2 p` sets entry `p` of the halfwords from `P`. -/
theorem halvesAt_set {t t' : MachineState} {P : Word} {n p : Nat} {v : BitVec 16}
    (hP : P.toNat % 2 = 0) (hn : P.toNat + 2 * n < 2 ^ 64) (hp : p < n)
    (hf : BFrame t t' (Within · (P + BitVec.ofNat 64 (2 * p)) 2))
    (hv : t'.getHalfword (P + BitVec.ofNat 64 (2 * p)) = v) :
    halvesAt t' P n = (halvesAt t P n).set p v := by
  apply List.ext_getElem (by simp [halvesAt])
  intro k h1 _
  simp only [halvesAt, List.length_map, List.length_range] at h1
  rw [List.getElem_set]
  simp only [halvesAt, List.getElem_map, List.getElem_range]
  split
  · rename_i e; subst e; exact hv
  · rename_i e
    exact getHalfword_eq_of_bytes (by addr_omega [hP, hn, h1])
      (hf _ fun hw ↦ by addr_omega [hw, hn, h1, hp, e])
      (hf _ fun hw ↦ by addr_omega [hw, hn, h1, hp, e])

theorem shr14_eq_zero {q : Nat} (hq : q < 2 ^ 14) : BitVec.ofNat 64 q >>> 14 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0]
  apply Nat.div_eq_of_lt
  omega

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb q : Nat} {st : Model.NewState}
  {g : GrpSt}

theorem GS.L_le (h : GS s words u₀ i L Hb st q g t) : L ≤ 2 ^ 14 := by
  have := h.k.hL; omega

theorem GS.blk_len (h : GS s words u₀ i L Hb st q g t) : (blk words i).length = L := by
  rw [blk_length h.k.a.len, h.k.hL]

/-- `0x800005a8`'s step: on to position `q'`, nothing else changed. -/
theorem GS.adv (h : GS s words u₀ i L Hb st q g t) (hm : ∀ a, t'.getMem a = t.getMem a)
    (hr : ∀ r, r ≠ .x9 → r ≠ .x24 → t'.getReg r = t.getReg r) {q' : Nat} (hq : q' ≤ L)
    (h9 : t'.getReg .x9 = BitVec.ofNat 64 q')
    (h24 : t'.getReg .x24 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i + q'))) :
    GS s words u₀ i L Hb st q' g t' := by
  have hn : heapNext t' = heapNext t := by simp only [heapNext, hm]
  have hsp : t'.getReg .x2 = msp := (hr .x2 (by decide) (by decide)).trans h.k.ng.sp
  have hf : BFrame t t' (fun _ ↦ False) := BFrame.of_same hm _
  obtain ⟨vecs, bufs⟩ := VecsAt.frame h.vecs h.bufs hf (fun _ h ↦ h.elim) (by
    have := h.k.hb; have := h.k.ng.heap.hi; simp only [heapNext] at *; omega)
  have m := h.mem
  refine ⟨h.k.frame hf (fun _ h ↦ h.elim) hsp ⟨by rw [hn]; exact h.k.ng.heap.lo,
    by rw [hn]; exact h.k.ng.heap.hi⟩ (le_of_eq hn.symm), vecs, bufs,
    ⟨fun j hj ↦ ?_, by rw [halvesAt_same hm]; exact m.groupOf, by rw [hm]; exact m.len,
      by rw [hm]; exact m.cap, by rw [hm]; exact m.al, by rw [hm, hm, hn]; exact m.buf,
      by rw [hm, rwords_same hm]; exact m.dist⟩, hq, ?_, h9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h24,
    ?_, ?_, ?_⟩
  · simp only [getHalfword_same hm]; exact m.slots j hj
  all_goals first
    | (rw [hr _ (by decide) (by decide)]; first
        | exact h.x8 | exact h.x15 | exact h.x16 | exact h.x18 | exact h.x20
        | exact h.x21 | exact h.x22 | exact h.x23 | exact h.x25 | exact h.x26
        | exact h.x27 | (rw [hm]; exact h.x10))

/-- A step that writes only the halfword `group_of[p]`. -/
theorem GS.goWrite (h : GS s words u₀ i L Hb st q g t) {p : Nat} (hp : p < 2 ^ 14)
    (hf : BFrame t t' (Within · (u₀.getReg .x9 + BitVec.ofNat 64 (2 * p)) 2))
    (hr : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x19 → t'.getReg r = t.getReg r)
    {go : List (BitVec 16)} (hg : halvesAt t' (u₀.getReg .x9) 0x4000 = go) :
    GS s words u₀ i L Hb st q (g.1, go, g.2.2) t' := by
  have hSL := h.k.a.slots
  have hGO := h.k.a.groupOf
  have hH0 := h.k.hb0
  have hhb := h.k.hb
  have hhi := h.k.ng.heap.hi
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hH0 hhb hhi
  have hlow : ∀ a : Word, (u₀.getReg .x9).toNat + 0x8000 ≤ a.toNat ∨
      a.toNat < (u₀.getReg .x9).toNat → byteAt t' a = byteAt t a :=
    fun a ha ↦ hf a fun hw ↦ by rcases ha with ha | ha <;> addr_omega [hw, ha, hp, hGO, hhi, hH0, hhb]
  have hmsp : ∀ c : Nat, c % 8 = 0 → c + 8 ≤ 4096 →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := fun c h8 hc ↦
    hf.getMem (by addr_omega [h8, hc]) fun k hk hw ↦ by addr_omega [hw, hk, hc, hp, hSL, hGO, hH0, hhb, hhi]
  have hn : heapNext t' = heapNext t := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf.getMem (a := nextAddr) (by decide) fun k hk hw ↦ by
      addr_omega [hw, hk, hp, hSL, hGO, hH0, hhb, hhi])
  have hsp : t'.getReg .x2 = msp := (hr .x2 (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans h.k.ng.sp
  have hW : ∀ a, Within a (u₀.getReg .x9 + BitVec.ofNat 64 (2 * p)) 2 → WB (heapNext u₀) Hb a :=
    fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by
      simp only [heapStart]; addr_omega [ha, hSL, hGO, hp], by
      simp only [heapNext]; addr_omega [ha, hSL, hGO, hp]⟩))))))
  have hHb : Hb ≤ heapEnd := by simp only [heapEnd]; omega
  obtain ⟨vecs, bufs⟩ := VecsAt.frame h.vecs h.bufs hf (fun a ha ↦ WB.vec h.k.hb0 hHb (hW a ha))
    hHb
  have m := h.mem
  have v104 : t'.getMem (msp + 104) = t.getMem (msp + 104) := hmsp 104 (by decide) (by decide)
  have v112 : t'.getMem (msp + 112) = t.getMem (msp + 112) := hmsp 112 (by decide) (by decide)
  have v120 : t'.getMem (msp + 120) = t.getMem (msp + 120) := hmsp 120 (by decide) (by decide)
  have hD : ∀ k < g.2.2.length, t'.getMem (t.getMem (msp + 112) + BitVec.ofNat 64 (8 * k)) =
      t.getMem (t.getMem (msp + 112) + BitVec.ofNat 64 (8 * k)) := by
    intro k hk
    have hc := m.cap
    have hal := m.al
    rcases m.buf with h0 | ⟨h1, h2⟩
    · omega
    · exact getMem_eq_of_bytes (by addr_omega [hal, hk, h1, h2, hhi, hc])
        (by addr_omega [hal, hk, h1, h2, hhi, hc]) fun x hx ↦ hlow _ (Or.inl (by
          addr_omega [h1, h2, hk, hx, hhi, hH0, hGO, hSL, hc]))
  refine ⟨h.k.frame hf hW hsp ⟨by rw [hn]; exact h.k.ng.heap.lo, by rw [hn]; exact h.k.ng.heap.hi⟩
    (le_of_eq hn.symm), vecs, bufs, ⟨fun j hj ↦ ?_, hg, by rw [v120]; exact m.len,
    by rw [v104]; exact m.cap, by rw [v112]; exact m.al, by rw [v112, v104, hn]; exact m.buf, ?_⟩,
    h.hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have k0 : t'.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j)) =
        t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j)) :=
      getHalfword_eq_of_bytes (by addr_omega [hSL, hj, hGO, hhi])
        (hlow _ (Or.inr (by addr_omega [hSL, hj, hGO, hhi])))
        (hlow _ (Or.inr (by addr_omega [hSL, hj, hGO, hhi])))
    have k2 : t'.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) + 2) =
        t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) + 2) :=
      getHalfword_eq_of_bytes (by addr_omega [hSL, hj, hGO, hhi])
        (hlow _ (Or.inr (by addr_omega [hSL, hj, hGO, hhi])))
        (hlow _ (Or.inr (by addr_omega [hSL, hj, hGO, hhi])))
    rw [k0, k2]
    exact m.slots j hj
  · show t'.readWords _ g.2.2.length = g.2.2
    have e := m.dist
    rw [v112, readWords_eq_map]
    rw [readWords_eq_map] at e
    exact (List.map_congr_left fun k hk ↦ hD k (List.mem_range.mp hk)).trans e
  all_goals first
    | (rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; first
        | exact h.x8 | exact h.x9 | exact h.x15 | exact h.x16 | exact h.x18 | exact h.x20
        | exact h.x21 | exact h.x22 | exact h.x23 | exact h.x24 | exact h.x25 | exact h.x26
        | exact h.x27 | (rw [v112]; exact h.x10))

/-- `0x800005a8`: past position `q`, to the next or out of the loop. -/
theorem group_adv (h : GS s words u₀ i L Hb st q g t) (hpc : t.pc = 0x800005a8) (hq : q < L)
    (hf : gfold words i st (q + 1) = some g) :
    ∃ v, Reaches Image.code t v ∧ (GH s words u₀ i L Hb st (q + 1) g v ∨
      (q + 1 = L ∧ GS s words u₀ i L Hb st L g v ∧ v.pc = 0x8000064c)) := by
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b800005a8_spec hpc trivial
  have kv := b800005a8_keeps hv
  have hfit := h.k.a.inv.fits
  simp only [inputWords] at hfit
  have hlen := h.k.a.len
  have hlt := h.k.lt
  have hL := h.k.hL
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hr : ∀ r, r ≠ .x9 → r ≠ .x24 → v.getReg r = t.getReg r := by
    intro r h9 h24
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact kv _ (by decide) | rfl
  have h9 : v.getReg .x9 = BitVec.ofNat 64 (q + 1) := by
    rw [b800005a8_x9 hv, h.x9, BitVec.ofNat_add]; rfl
  have h24 : v.getReg .x24 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i + (q + 1))) := by
    rw [b800005a8_x24 hv, h.x24]
    apply BitVec.eq_of_toNat_eq
    addr_omega [hib, hfit, hlen, hlt, hL, hq]
  have gs := h.adv (fun a ↦ b800005a8_mem_same hv a) hr (q' := q + 1) (by omega) h9 h24
  by_cases e : q + 1 = L
  · subst e
    refine ⟨v, rv, Or.inr ⟨rfl, gs, b800005a8_pc_taken hv ?_⟩⟩
    rw [h.x24, h.x15]
    apply BitVec.eq_of_toNat_eq
    addr_omega [hib, hfit, hlen, hlt, hL, hq]
  · refine ⟨v, rv, Or.inl ⟨gs, b800005a8_pc_not_taken hv fun he ↦ e ?_, hf, by omega⟩⟩
    rw [h.x24, h.x15] at he
    have := congrArg BitVec.toNat he
    addr_omega [this, hib, hfit, hlen, hlt, hL, hq]

/-- `0x80000594`: `group_of[q]` set to the word's group, on to `0x800005a8`. -/
theorem group_store {r : List (Option (BitVec 16)) × List (BitVec 64) × BitVec 16}
    (h : GP s words u₀ i L Hb st q g r t) (hq : q < L) :
    ∃ v, Reaches Image.code t v ∧ v.pc = 0x800005a8 ∧
      GS s words u₀ i L Hb st q (r.1, g.2.1.set q r.2.2, r.2.1) v := by
  have gs := h.gs
  have hL := gs.L_le
  have hGO := gs.k.a.groupOf
  have hSL := gs.k.a.slots
  have hhi := gs.k.ng.heap.hi
  have hH0 := gs.k.ng.mono
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hhi hH0
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000594_spec h.pc trivial
  have k₁ := b80000594_keeps h₁
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches NB.g8000059c_spec
    (b80000594_pc_not_taken h₁ (by rw [gs.x9]; exact shr14_eq_zero (by omega))) trivial
  have k₂ := NB.g8000059c_keeps h₂
  have x12₂ : t₂.getReg .x12 = u₀.getReg .x9 + BitVec.ofNat 64 (2 * q) := by
    rw [NB.g8000059c_x12 h₂, k₁ .x16 (by decide), k₁ .x9 (by decide), gs.x16, gs.x9,
      show (2 : Word) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]
  have x11₂ : t₂.getReg .x11 = t.getReg .x11 := by
    rw [k₂ .x11 (by decide), k₁ .x11 (by decide)]
  have hm₂ : ∀ a, t₂.getMem a = t.getMem a := fun a ↦ by
    rw [NB.g8000059c_mem_same h₂, b80000594_mem_same h₁]
  obtain ⟨t₃, r₃, hpc₃, hr₃, hh₃, hf₃⟩ := step_sh (code := Image.code) (s := t₂) (rs1 := .x12)
    (rs2 := .x11) (off := 0) (by rw [NB.g8000059c_pc h₂]; exact fetch_of (by decide +kernel))
    (by
      rw [off0, x12₂]
      exact valid2_of (by addr_omega [hSL, hGO, hq, hL]) (by addr_omega [hGO, hq, hL, hhi, hH0])
        (by addr_omega [hGO, hq, hL]))
  rw [off0, x12₂] at hh₃ hf₃
  have hf : BFrame t t₃ (Within · (u₀.getReg .x9 + BitVec.ofNat 64 (2 * q)) 2) := fun a ha ↦ by
    rw [hf₃.byte a fun h' ↦ ha ?_, byteAt_eq, byteAt_eq, hm₂]
    rcases h' with h' | h' <;> rw [h'] <;> addr_omega [hGO, hq, hL, hhi, hH0]
  have hr : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x19 →
      t₃.getReg r = t.getReg r := by
    intro r h11 h12 h13 h14 h19
    rw [hr₃ r]
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact (k₂ _ (by decide)).trans (k₁ _ (by decide)) | rfl
  have hv : t₃.getHalfword (u₀.getReg .x9 + BitVec.ofNat 64 (2 * q)) = r.2.2 := by
    rw [hh₃, x11₂, ← h.x11]
  have hgo := gs.mem.groupOf
  have hgo' : halvesAt t₃ (u₀.getReg .x9) 0x4000 = g.2.1.set q r.2.2 := by
    rw [halvesAt_set hGO.1 (by addr_omega [hGO, hhi, hH0]) (by omega) hf hv, hgo]
  have gs₃ := gs.goWrite (p := q) (by omega) hf hr hgo'
  exact ⟨t₃, r₁.trans (r₂.trans ⟨1, r₃⟩), by rw [hpc₃, NB.g8000059c_pc h₂]; rfl, gs₃⟩

theorem gfold_len (words : List Word) (i : Nat) (st : Model.NewState) :
    ∀ q g, gfold words i st q = some g → g.2.1.length = st.groupOf.length := by
  intro q
  induction q with
  | zero => intro g hg; cases hg; rfl
  | succ q ih =>
    intro g hg
    rw [gfold_succ] at hg
    cases e : gfold words i st q with
    | none => rw [e] at hg; cases hg
    | some g₀ =>
      rw [e, Model.groupStepRust, Option.bind_some] at hg
      split at hg
      · cases hg; exact ih _ e
      · obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp hg
        rw [List.length_set]; exact ih _ e

/-- One position of `group`'s loop, from its head. -/
theorem group_pos (h : GH s words u₀ i L Hb st q g t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ g', gfold words i st (q + 1) = some g' ∧
      (GH s words u₀ i L Hb st (q + 1) g' v ∨
        (q + 1 = L ∧ GS s words u₀ i L Hb st L g' v ∧ v.pc = 0x8000064c))) := by
  have gs := h.gs
  have hq := h.lt
  have hfit := gs.k.a.inv.fits
  simp only [inputWords] at hfit
  have hlen := gs.k.a.len
  have hlt := gs.k.lt
  have hL := gs.k.hL
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hbl := gs.blk_len
  have hgl : st.groupOf.length = 0x4000 := by
    rw [← gfold_len words i st q g h.fold, ← gs.mem.groupOf]; simp [halvesAt]
  obtain ⟨g₁, hg₁, -⟩ := groupFold_spec (blk words i) (by rw [hbl]; exact gs.L_le) st.slots
    gs.k.slotsLen st.groupOf (by rw [hbl, hgl]; exact gs.L_le) (q + 1) (by omega)
  have hg₁' : gfold words i st (q + 1) = some g₁ := hg₁
  rw [gfold_succ, h.fold] at hg₁'
  have hw : t.getMem (t.getReg .x24) = (blk words i).getD q 0 := by
    rw [gs.x24, blk_getD (by omega) (by omega) hlen, ← (gs.k.ng.minv gs.k.a).input _ (by omega)]
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b800005b4_spec h.pc (by
    rv_eval []
    rw [gs.x24]
    exact (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by addr_omega [hib, hfit, hlen, hlt, hL, hq],
      by addr_omega [hib, hfit, hlen, hlt, hL, hq]⟩, by addr_omega [hib, hfit, hlen, hlt, hL, hq]⟩)
  have k₁ := b800005b4_keeps h₁
  have gs₁ := gs.same (fun a ↦ b800005b4_mem_same h₁ a) fun r _ _ _ _ h19 ↦ by
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact k₁ _ (by decide) | rfl
  by_cases hz : (blk words i).getD q 0 = 0
  · rw [Model.groupStepRust, Option.bind_some, ite_eq_left hz] at hg₁'
    cases hg₁'
    have hf : gfold words i st (q + 1) = some g := by
      rw [gfold_succ, h.fold, Model.groupStepRust, Option.bind_some, ite_eq_left hz]
    obtain ⟨v, rv, hv⟩ := group_adv gs₁ (b800005b4_pc_taken h₁ (by rw [hw, hz])) hq hf
    exact ⟨v, r₁.trans rv, Or.inr ⟨g, hf, hv⟩⟩
  · rw [Model.groupStepRust, Option.bind_some, ite_eq_right hz] at hg₁'
    obtain ⟨r, hr, hrg⟩ := Option.map_eq_some_iff.mp hg₁'
    have x19₁ : t₁.getReg .x19 = (blk words i).getD q 0 := by rw [b800005b4_x19 h₁, hw]
    have hglen : g.1.length = 2 ^ 15 := by
      obtain ⟨g₀, hg₀, hinv⟩ := groupFold_spec (blk words i) (by rw [hbl]; exact gs.L_le) st.slots
        gs.k.slotsLen st.groupOf (by rw [hbl, hgl]; exact gs.L_le) q (by omega)
      have : gfold words i st q = some g₀ := hg₀
      rw [h.fold] at this
      cases this
      exact hinv.slots_len
    obtain ⟨t₂, r₂, hd | hgp⟩ := probe_first gs₁ (b800005b4_pc_not_taken h₁ (by rw [hw]; exact hz))
      hglen (r := r) (by rw [x19₁]; exact hr)
    · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
    obtain ⟨t₃, r₃, hpc₃, gs₃⟩ := group_store hgp hq
    have hf : gfold words i st (q + 1) = some (r.1, g.2.1.set q r.2.2, r.2.1) := by
      rw [gfold_succ, h.fold, Model.groupStepRust, Option.bind_some, ite_eq_right hz, hr]; rfl
    obtain ⟨v, rv, hv⟩ := group_adv gs₃ hpc₃ hq hf
    exact ⟨v, r₁.trans (r₂.trans (r₃.trans rv)), Or.inr ⟨_, hf, hv⟩⟩

/-- `group`'s loop, from position `q` to its exit at `0x8000064c`. -/
theorem group_loop : ∀ m q g t, L - q = m → GH s words u₀ i L Hb st q g t →
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ g', gfold words i st L = some g' ∧
      GS s words u₀ i L Hb st L g' v ∧ v.pc = 0x8000064c) := by
  intro m
  induction m with
  | zero => intro q g t hm h; have := h.lt; omega
  | succ m ih =>
    intro q g t hm h
    obtain ⟨v, rv, hd | ⟨g', hf, hgh | ⟨he, gs, hpc⟩⟩⟩ := group_pos h
    · exact ⟨v, rv, Or.inl hd⟩
    · obtain ⟨w, rw', hw⟩ := ih (q + 1) g' v (by omega) hgh
      exact ⟨w, rv.trans rw', hw⟩
    · subst he
      exact ⟨v, rv, Or.inr ⟨g', hf, gs, hpc⟩⟩

end

end Rv64Verifier.Proofs.Main
