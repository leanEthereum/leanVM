module

public import NativeRustcX64.Sym.Mem

/-!
# Whole loads and stores are sound

A load or store the executor places at a constant offset in a region (`NativeRustcX64.Sym.Mem`),
at an index in a region no write overlaps, or over the slots of an index with a bound: a symbolic
load's value is the integer Kraken loads (`Match.loadAt`); a symbolic store's state matches the
machine after Kraken's store, whose bytes are all mapped (`Match.storeAt`).

An access at `o + s * x` (`SState.slots`: `x` with a bound `B`, `n ≤ s`) is at one of the slots
`o + s * k`, `k < B`, which do not overlap: a store writes each slot (`slotWrite`), the stored value
at slot `x` and the bytes already there at the others (`Match.storeSlots`); a load is the
conditional over the slots (`Match.loadSlots`).
-/

namespace NativeRustcX64.Sym

public section

/-! ## Writes before others -/

theorem natOfBytes_div (bs : List UInt8) (t : Nat) (ht : t < bs.length) :
    Nat.ofBytes bs / 2 ^ (8 * t) % 256 = (bs[t]'ht).toNat := by
  induction bs generalizing t with
  | nil => cases ht
  | cons b bs ih =>
    have hb := b.toNat_lt
    show (Nat.ofBytes bs * 256 + b.toNat) / 2 ^ (8 * t) % 256 = _
    cases t with
    | zero =>
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]
      omega
    | succ t =>
      rw [show 8 * (t + 1) = 8 + 8 * t by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
        show (Nat.ofBytes bs * 256 + b.toNat) / 2 ^ 8 = Nat.ofBytes bs by omega]
      exact ih t (by simp at ht; omega)

theorem findWrite_append (r i : Nat) (L ws : List Write) :
    findWrite r i (L ++ ws) = (findWrite r i L).or (findWrite r i ws) := by
  induction L with
  | nil => rfl
  | cons w L ih =>
    rw [List.cons_append, findWrite_cons, findWrite_cons]
    split
    · rfl
    · exact ih

/-! ## Slots -/

/-- Slots of a scale at least the access's size do not overlap. -/
theorem slot_unique {o s n i k k' : Nat} (hns : n ≤ s) (h : o + s * k ≤ i ∧ i < o + s * k + n)
    (h' : o + s * k' ≤ i ∧ i < o + s * k' + n) : k = k' := by
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      omega
    · exact hs
  have e : ∀ j, o + s * j ≤ i ∧ i < o + s * j + n → (i - o) / s = j := by
    intro j hj
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]
      omega
    · rw [Nat.succ_mul, Nat.mul_comm]
      omega
  rw [← e k h, ← e k' h']

theorem findWrite_slots_none {ws : List Write} {r' r o s n i : Nat} {x v : Sym} :
    ∀ {B : Nat}, (∀ k < B, ¬(r = r' ∧ o + s * k ≤ i ∧ i < o + s * k + n)) →
      findWrite r' i ((List.range B).map (slotWrite ws r o s n x v)) = none
  | 0, _ => rfl
  | B + 1, h => by
    rw [List.range_succ, List.map_append, findWrite_append,
      findWrite_slots_none (fun k hk => h k (by omega))]
    show findWrite r' i [slotWrite ws r o s n x v B] = none
    simp only [findWrite_cons, slotWrite]
    rw [ite_neg (h B (by omega))]
    rfl

theorem findWrite_slots_some {ws : List Write} {r o s n i k : Nat} {x v : Sym} (hns : n ≤ s)
    (hi : o + s * k ≤ i ∧ i < o + s * k + n) :
    ∀ {B : Nat}, k < B → findWrite r i ((List.range B).map (slotWrite ws r o s n x v)) =
      some ((slotWrite ws r o s n x v k).v, i - (o + s * k))
  | 0, hk => absurd hk (Nat.not_lt_zero _)
  | B + 1, hk => by
    rw [List.range_succ, List.map_append, findWrite_append]
    by_cases hkB : k < B
    · rw [findWrite_slots_some hns hi hkB]
      rfl
    · have hk' : k = B := by omega
      subst hk'
      rw [findWrite_slots_none fun k' hk' hc => absurd (slot_unique hns hi hc.2) (by omega)]
      show findWrite r i [slotWrite ws r o s n x v k] = _
      simp only [findWrite_cons, slotWrite, hi.1, hi.2, and_self, ↓reduceIte]

theorem ofNat_beq {X k : Nat} (hX : X < 2 ^ 64) (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 X == BitVec.ofNat 64 k) = decide (X = k) := by
  by_cases h : X = k
  · subst h
    simp
  · have hne : BitVec.ofNat 64 X ≠ BitVec.ofNat 64 k := fun e => h (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hk] at this)
    simp [h, hne]

theorem shiftCount_lit : ∀ (w : Width) (j : Nat), j < w.bits →
    shiftCount w (BitVec.ofNat 64 j) = j := by
  intro w
  cases w <;> decide +kernel

variable [Labels] {env : Env} {S : SState} {m : MachineData}

theorem memByte_append_none {L ws : List Write} {r i : Nat} {b : BitVec 64}
    (h : findWrite r i L = none) : memByte env (L ++ ws) r b i = memByte env ws r b i := by
  unfold memByte
  rw [findWrite_append, h]
  rfl

theorem memByte_append_some {L ws : List Write} {r i : Nat} {b : BitVec 64} {v : Sym} {t : Nat}
    (h : findWrite r i L = some (v, t)) :
    memByte env (L ++ ws) r b i = some (byteOf (v.eval env) t) := by
  unfold memByte
  rw [findWrite_append, h]
  rfl

theorem idxScale_spec {i x : Sym} {s B : Nat} (h : idxScale i = (x, s))
    (hx : (x.eval env).toNat < B) (hB : s * (B - 1) < 2 ^ 64) :
    (i.eval env).toNat = s * (x.eval env).toNat := by
  unfold idxScale at h
  split at h
  · rename_i x' s'
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rcases Nat.eq_zero_or_pos (x'.eval env).toNat with h0 | h0
    · rw [h0]
      simp
    · have h1 : s' ≤ s' * (B - 1) := Nat.le_mul_of_pos_right _ (by omega)
      have h2 : s' * (x'.eval env).toNat ≤ s' * (B - 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mod_eq_of_lt (show s' < 2 ^ 64 by omega), Nat.mul_comm,
        Nat.mod_eq_of_lt (by omega)]
  · rename_i x' j
    split at h
    · rename_i hj
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hX : 2 ^ j * (x'.eval env).toNat ≤ 2 ^ j * (B - 1) := Nat.mul_le_mul_left _ (by omega)
      have hc : shiftCount .W64 (BitVec.ofNat 64 j) = j := shiftCount_lit .W64 j hj
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hc, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; omega), Nat.mul_comm]
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Nat.one_mul]
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Nat.one_mul]

theorem Match.slotsAt (hm : Match env S m) (hwf : env.WFRo) {p i x : Sym} {d : Int}
    {n r o s B : Nat} (h : S.slotsAt p i d n = some (r, o, x, s, B)) :
    ∃ b sz, env.regions[r]? = some (b, sz) ∧ n ≤ s ∧ 0 < n ∧ o + s * (B - 1) + n ≤ sz ∧
      (x.eval env).toNat < B ∧
      p.eval env + BitVec.ofInt 64 d + i.eval env =
        b + BitVec.ofNat 64 (o + s * (x.eval env).toNat) := by
  unfold SState.slotsAt at h
  cases hp : S.toPtr p with
  | none => simp [hp] at h
  | some ro =>
    obtain ⟨r', o'⟩ := ro
    cases hB : S.bounds.lookup (idxScale i).1 with
    | none => simp [hp, hB] at h
    | some B' =>
      simp only [hp, hB] at h
      cases hr : S.regions[r']? with
      | none => simp [hr] at h
      | some sz =>
        simp only [hr] at h
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          obtain ⟨b, hb⟩ := hm.regions r' sz hr
          have hx := hm.bounds _ B' (mem_of_lookup hB)
          have hnw := hwf.noWrap r' b sz hb
          obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := hc
          have hsB : (idxScale i).2 * (B' - 1) < 2 ^ 64 := by omega
          have hi := idxScale_spec (env := env) (x := (idxScale i).1) (s := (idxScale i).2) (B := B')
            (rfl : idxScale i = ((idxScale i).1, (idxScale i).2)) hx hsB
          have hsX : (idxScale i).2 * ((idxScale i).1.eval env).toNat ≤ (idxScale i).2 * (B' - 1) :=
            Nat.mul_le_mul_left _ (by omega)
          refine ⟨b, sz, hb, hc2, hc3, by omega, hx, ?_⟩
          rw [hm.toPtr hp, Env.base_eq hb]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat, hi]
          generalize (idxScale i).2 * ((idxScale i).1.eval env).toNat = Y at *
          generalize (idxScale i).2 * (B' - 1) = Z at *
          omega
        · cases h

theorem Match.slots2 (hm : Match env S m) (hwf : env.WFRo) {p q x : Sym} {d : Int}
    {n r o s B : Nat} (h : S.slots2 p q d n = some (r, o, x, s, B)) :
    ∃ b sz, env.regions[r]? = some (b, sz) ∧ n ≤ s ∧ 0 < n ∧ o + s * (B - 1) + n ≤ sz ∧
      (x.eval env).toNat < B ∧
      p.eval env + q.eval env + BitVec.ofInt 64 d =
        b + BitVec.ofNat 64 (o + s * (x.eval env).toNat) := by
  unfold SState.slots2 at h
  split at h
  · rename_i res hres
    cases h
    obtain ⟨b, sz, hb, h1, h2, h3, h4, he⟩ := hm.slotsAt hwf hres
    refine ⟨b, sz, hb, h1, h2, h3, h4, ?_⟩
    rw [← he, BitVec.add_assoc, BitVec.add_comm (q.eval env), ← BitVec.add_assoc]
  · obtain ⟨b, sz, hb, h1, h2, h3, h4, he⟩ := hm.slotsAt hwf h
    refine ⟨b, sz, hb, h1, h2, h3, h4, ?_⟩
    rw [← he, BitVec.add_comm (p.eval env), BitVec.add_assoc, BitVec.add_comm (p.eval env),
      ← BitVec.add_assoc]

/-- An indexed access the executor places as slots: its region, and its address for the bounded
value's value. -/
theorem Match.slots (hm : Match env S m) (hwf : env.WFRo) {a x : Sym} {n r o s B : Nat}
    (h : S.slots a n = some (r, o, x, s, B)) :
    ∃ b sz, env.regions[r]? = some (b, sz) ∧ n ≤ s ∧ 0 < n ∧ o + s * (B - 1) + n ≤ sz ∧
      (x.eval env).toNat < B ∧ a.eval env = b + BitVec.ofNat 64 (o + s * (x.eval env).toNat) := by
  unfold SState.slots at h
  split at h
  · rename_i p q c
    obtain ⟨b, sz, hb, h1, h2, h3, h4, he⟩ := hm.slots2 hwf h
    refine ⟨b, sz, hb, h1, h2, h3, h4, ?_⟩
    rw [← he]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, ofInt_litInt]
  · rename_i p q _
    obtain ⟨b, sz, hb, h1, h2, h3, h4, he⟩ := hm.slots2 hwf h
    refine ⟨b, sz, hb, h1, h2, h3, h4, ?_⟩
    rw [← he]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  · cases h

/-- Byte `t` of a symbolic load is the byte of memory there. -/
theorem Match.byteOf_loadSym (hm : Match env S m) (hwf : env.WFRo) {r o n : Nat} {b : BitVec 64}
    {sz : Nat} (hb : env.regions[r]? = some (b, sz)) (hle : o + n ≤ sz) (hn : n ≤ 8) {t : Nat}
    (ht : t < n) : byteOf ((NativeRustcX64.Sym.loadSym S.mem r o n).eval env) t = memByteD env S.mem r b (o + t) := by
  obtain ⟨hl, -⟩ := hm.loadSym_ro hwf hb hle hn
  rw [loadInt_of_get? _ _ n (fun i => memByteD env S.mem r b (o + i)) (fun i hi => by
    rw [addr_add, hm.mem r b sz hb (o + i) (by omega), memByte_eq_ro hwf hb (by omega)]),
    ofBytes_natCast, Option.some.injEq, Int.natCast_inj] at hl
  rw [byteOf_mod, ← hl, natOfBytes_div _ t (by simp; omega)]
  simp

theorem eval_pickEq {x : Sym} {k : Nat} (hx : x.eval env = BitVec.ofNat 64 k) (v : Sym) :
    (pickEq x k v).eval env = v.eval env := by
  unfold pickEq
  split
  · rename_i y j a b
    split
    · rename_i hc
      obtain ⟨rfl, hj, hk⟩ := hc
      have hcond : (SBool.cmp .eq .W64 y (.lit j)).eval env = decide (k = j) := by
        simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, hx]
        exact ofNat_beq hk hj
      by_cases hjk : j = k
      · subst hjk
        simp only [Sym.eval, hcond, decide_true, ite_true]
      · have hkj : ¬k = j := fun e => hjk e.symm
        simp only [Sym.eval, hcond, hjk, hkj, decide_false, Bool.false_eq_true, ite_false]
    · rfl
  · rfl

theorem eval_underEq {x : Sym} {k : Nat} (hx : x.eval env = BitVec.ofNat 64 k) (v : Sym) :
    (underEq x k v).eval env = v.eval env := by
  unfold underEq
  split
  · simp only [Sym.eval, eval_pickEq hx]
  · exact eval_pickEq hx _

theorem eval_slotLoad {ws : List Write} {r o s n : Nat} {x : Sym} {X : Nat}
    (hx : x.eval env = BitVec.ofNat 64 X) (hX : X < 2 ^ 64) :
    ∀ c k, k ≤ X → X ≤ k + c →
      (slotLoad ws r o s n x k c).eval env = (loadSym ws r (o + s * X) n).eval env
  | 0, k, h1, h2 => by
    obtain rfl : X = k := by omega
    exact eval_underEq hx _
  | c + 1, k, h1, h2 => by
    rw [slotLoad, eval_mkIte, eval_mkCmp]
    simp only [CmpOp.apply, low_W64, Sym.eval, hx, ofNat_beq hX (by omega : k < 2 ^ 64)]
    by_cases hk : X = k
    · subst hk
      simp only [decide_true, ite_true]
      exact eval_underEq hx _
    · simp only [hk, decide_false, Bool.false_eq_true, ite_false]
      exact eval_slotLoad hx hX c (k + 1) (by omega) (by omega)

/-- **A load over slots is Kraken's.** -/
theorem Match.loadSlots (hm : Match env S m) (hwf : env.WFRo) {a v : Sym} {n : Nat}
    (h : S.loadSlots a n = some v) (hn : n ≤ 8) :
    Mem.loadInt m.dmem (a.eval env) n = some ((v.eval env).toNat : Int) ∧
      (v.eval env).toNat < 2 ^ (8 * n) := by
  unfold SState.loadSlots at h
  cases hs : S.slots a n with
  | none => rw [hs] at h; cases h
  | some q =>
    obtain ⟨r, o, x, s, B⟩ := q
    rw [hs] at h
    cases h
    obtain ⟨b, sz, hb, hns, hn0, hle, hX, ha⟩ := hm.slots hwf hs
    have hsX : s * (x.eval env).toNat ≤ s * (B - 1) := Nat.mul_le_mul_left _ (by omega)
    have hxe : x.eval env = BitVec.ofNat 64 (x.eval env).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [ha, eval_slotLoad hxe (BitVec.isLt _) (B - 1) 0 (Nat.zero_le _) (by omega)]
    exact hm.loadSym_ro hwf hb (by omega) hn

/-- **A store over slots is Kraken's**: the bytes it stores are mapped, and the state after it
matches the machine after Kraken's store at the bounded value's slot. -/
theorem Match.storeSlots (hm : Match env S m) (hwf : env.WFRo) {a u x : Sym} {n r o s B : Nat}
    (h : S.slots a n = some (r, o, x, s, B)) (hro : r ∉ S.roRegions) (hn : n ≤ 8) (val : Int)
    (hval : ∀ t < n, (Int.toBytes n val)[t]? = some (byteOf (u.eval env) t)) :
    (Mem.loadInt m.dmem (a.eval env) n).isSome ∧
      Match env (S.storeSlots r o s n x u B)
        { m with dmem := Mem.storeInt m.dmem (a.eval env) n val } := by
  obtain ⟨b, sz, hb, hns, hn0, hle, hX, ha⟩ := hm.slots hwf h
  have hsX : s * (x.eval env).toNat ≤ s * (B - 1) := Nat.mul_le_mul_left _ (by omega)
  have hBs : B - 1 ≤ s * (B - 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hxe : x.eval env = BitVec.ofNat 64 (x.eval env).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hXlt : (x.eval env).toNat < 2 ^ 64 := BitVec.isLt _
  generalize (x.eval env).toNat = X at hX hsX ha hxe hXlt
  rw [ha]
  have hbsz := hwf.noWrap r b sz hb
  have hA : (b + BitVec.ofNat 64 (o + s * X)).toNat = b.toNat + (o + s * X) :=
    toNat_add_ofNat b _ (by omega)
  have hcond : ∀ k, k < B → (mkCmp .eq .W64 x (.lit k)).eval env = decide (X = k) := by
    intro k hk
    rw [eval_mkCmp]
    simp only [CmpOp.apply, low_W64, Sym.eval, hxe]
    exact ofNat_beq hXlt (by omega)
  refine ⟨loadInt_isSome_of_get? _ _ _ fun i hi => ?_, ?_⟩
  · rw [addr_add]
    exact hm.get?_some_ro hwf hb (by omega)
  -- the bytes outside the store are unchanged
  have hout : ∀ k : BitVec 64,
      (k.toNat < b.toNat + (o + s * X) ∨ b.toNat + (o + s * X) + n ≤ k.toNat) →
      (Mem.storeInt m.dmem (b + BitVec.ofNat 64 (o + s * X)) n val).get? k = m.dmem.get? k := by
    intro k hk
    rw [get?_storeInt _ _ _ _ _ hn, ite_neg]
    have := le_toNat_sub k (b + BitVec.ofNat 64 (o + s * X)) n (by omega) (by omega)
    omega
  refine ⟨hm.regs, hm.flags, hm.regions, fun r' b' sz' hb' i hi => ?_, hm.labels,
    hm.bounds, hm.aliases, fun k hk => ?_, hm.known, hm.roRegions⟩
  · have hK : (b' + BitVec.ofNat 64 i).toNat = b'.toNat + i :=
      toNat_add_ofNat b' i (by have := hwf.noWrap r' b' sz' hb'; omega)
    show _ = memByte env ((List.range B).map (slotWrite S.mem r o s n x u) ++ S.mem) r' b' i
    by_cases hin : r = r' ∧ o + s * X ≤ i ∧ i < o + s * X + n
    · -- the stored slot
      obtain ⟨rfl, hi1, hi2⟩ := hin
      rw [hb] at hb'
      cases hb'
      rw [memByte_append_some (findWrite_slots_some hns ⟨hi1, hi2⟩ (by omega : X < B)),
        get?_storeInt _ _ _ _ _ hn, ite_pos (by rw [toNat_sub_of_le _ _ (by omega)]; omega),
        toNat_sub_of_le _ _ (by omega), hK, hA,
        show b.toNat + i - (b.toNat + (o + s * X)) = i - (o + s * X) by omega, hval _ (by omega)]
      simp only [slotWrite, eval_mkIte, hcond X (by omega), decide_true, ite_true]
    · by_cases hsl : r = r' ∧ ∃ k < B, o + s * k ≤ i ∧ i < o + s * k + n
      · -- another slot: the bytes already there
        obtain ⟨rfl, k, hk, hk1, hk2⟩ := hsl
        rw [hb] at hb'
        cases hb'
        have hkX : ¬X = k := fun e => hin ⟨rfl, e ▸ hk1, e ▸ hk2⟩
        have hni : ¬(o + s * X ≤ i ∧ i < o + s * X + n) := fun hc =>
          hkX (slot_unique hns hc ⟨hk1, hk2⟩)
        have hsk : s * k ≤ s * (B - 1) := Nat.mul_le_mul_left _ (by omega)
        rw [memByte_append_some (findWrite_slots_some hns ⟨hk1, hk2⟩ hk),
          hout _ (by rw [hK]; omega), hm.mem r b sz hb i hi, memByte_eq_ro hwf hb hi]
        simp only [slotWrite, eval_mkIte, hcond k hk, hkX, decide_false, Bool.false_eq_true,
          ite_false]
        rw [hm.byteOf_loadSym hwf hb (by omega) hn (by omega : i - (o + s * k) < n),
          show o + s * k + (i - (o + s * k)) = i by omega]
      · -- no slot
        rw [memByte_append_none (findWrite_slots_none fun k hk hc => hsl ⟨hc.1, k, hk, hc.2⟩)]
        rw [hout _ (by
          rw [hK]
          by_cases hr : r = r'
          · subst hr
            rw [hb] at hb'
            cases hb'
            have : ¬(o + s * X ≤ i ∧ i < o + s * X + n) := fun hc => hin ⟨rfl, hc⟩
            omega
          · rcases hwf.disjointOf r r' b b' sz sz' (hm.roRegions ▸ hro) hr hb hb' with h1 | h1 <;> omega),
          hm.mem r' b' sz' hb' i hi]
  · show (Mem.storeInt m.dmem (b + BitVec.ofNat 64 (o + s * X)) n val).get? k = _
    rw [hout k (by
      have := hk r b sz hb
      omega)]
    exact hm.outside k hk

/-! ## Loads and stores -/

/-- Initial-memory descriptions can be appended behind actual writes when interpreting a load. -/
theorem Match.withKnownMemory (hm : Match env S m) :
    Match env { S with mem := S.mem ++ S.known } m := by
  refine { hm with mem := ?_ }
  intro r b sz hb i hi
  rw [hm.mem r b sz hb i hi]
  change memByte env S.mem r b i = memByte env (S.mem ++ S.known) r b i
  unfold memByte
  rw [findWrite_append]
  cases findWrite r i S.mem with
  | none => exact (memByte_known hm.known hb i).symm
  | some vt => rfl

/-- A symbolic load at an unconditional address is Kraken's. -/
theorem Match.loadOne (hm : Match env S m) (hwf : env.WFRo) {a v : Sym} {n : Nat}
    (h : S.loadOne a n = some v) (hn : n ≤ 8) :
    Mem.loadInt m.dmem (a.eval env) n = some ((v.eval env).toNat : Int) ∧
      (v.eval env).toNat < 2 ^ (8 * n) := by
  unfold SState.loadOne at h
  cases hacc : S.access a n with
  | some ro =>
    obtain ⟨r, o⟩ := ro
    rw [hacc] at h
    cases h
    obtain ⟨b, sz, hb, hle, ha⟩ := hm.access hacc
    rw [ha]
    exact hm.withKnownMemory.loadSym_ro hwf hb hle hn
  | none =>
    rw [hacc] at h
    cases hidx : S.accessIdx a n with
    | none =>
      rw [hidx] at h
      exact hm.loadSlots hwf h hn
    | some roi =>
      obtain ⟨r, o, i, M⟩ := roi
      rw [hidx] at h
      change (if S.mem.all (fun w => w.r != r || w.off + w.n ≤ o || o + M + n ≤ w.off) then
        some (Sym.loadx r o i n) else S.loadSlots a n) = some v at h
      split at h
      · rename_i hall
        cases h
        obtain ⟨b, sz, hb, hM, hle, ha⟩ := hm.accessIdx hidx
        rw [ha]
        exact hm.load_mem0_ro hwf hb hle hn fun j hj1 hj2 =>
          findWrite_none_of_apart hall (by omega) (by omega)
      · exact hm.loadSlots hwf h hn

/-- **A symbolic load is Kraken's.** -/
theorem Match.loadAt (hm : Match env S m) (hwf : env.WFRo) {a v : Sym} {n : Nat}
    (h : S.loadAt a n = some v) (hn : n ≤ 8) :
    Mem.loadInt m.dmem (a.eval env) n = some ((v.eval env).toNat : Int) ∧
      (v.eval env).toNat < 2 ^ (8 * n) := by
  unfold SState.loadAt at h
  cases ha : a.asIte with
  | none =>
    rw [ha] at h
    exact hm.loadOne hwf h hn
  | some cxy =>
    obtain ⟨c, x, y⟩ := cxy
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨vx, hx, vy, hy, rfl⟩ := h
    rw [asIte_eq ha, eval_mkIte]
    simp only [Sym.eval]
    split
    · exact hm.loadOne hwf hx hn
    · exact hm.loadOne hwf hy hn

/-! ## Stores -/

/-- **A symbolic store is Kraken's**: the bytes it stores are mapped, and the state after it
matches the machine after Kraken's store of bytes that are those of the stored value. -/
theorem Match.storeAt (hm : Match env S m) (hwf : env.WFRo) {a u : Sym} {n : Nat} {S' : SState}
    (h : S.storeAt a n u = some S') (hn0 : 0 < n) (hn : n ≤ 8) (val : Int)
    (hval : ∀ t < n, (Int.toBytes n val)[t]? = some (byteOf (u.eval env) t)) :
    (Mem.loadInt m.dmem (a.eval env) n).isSome ∧
      Match env S' { m with dmem := Mem.storeInt m.dmem (a.eval env) n val } := by
  unfold SState.storeAt at h
  cases hacc : S.access a n with
  | none =>
    rw [hacc] at h
    cases hs : S.slots a n with
    | none => rw [hs] at h; cases h
    | some q =>
      obtain ⟨r, o, x, s, B⟩ := q
      rw [hs] at h
      by_cases hro : r ∈ S.roRegions
      · simp [hro] at h
      · simp only [hro, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact hm.storeSlots hwf hs hro hn val hval
  | some ro =>
    obtain ⟨r, o⟩ := ro
    rw [hacc] at h
    by_cases hro : r ∈ S.roRegions
    · simp [hro] at h
    · simp only [hro, ↓reduceIte, Option.some.injEq] at h
      subst h
      obtain ⟨b, sz, hb, hle, ha⟩ := hm.access hacc
      rw [ha]
      have hbsz := hwf.noWrap r b sz hb
      have hA : (b + BitVec.ofNat 64 o).toNat = b.toNat + o := toNat_add_ofNat b o (by omega)
      refine ⟨loadInt_isSome_of_get? _ _ _ fun i hi => ?_, ?_⟩
      · rw [addr_add]
        exact hm.get?_some_ro hwf hb (by omega)
      have hout : ∀ k : BitVec 64, (k.toNat < b.toNat + o ∨ b.toNat + o + n ≤ k.toNat) →
          (Mem.storeInt m.dmem (b + BitVec.ofNat 64 o) n val).get? k = m.dmem.get? k := by
        intro k hk
        rw [get?_storeInt _ _ _ _ _ hn, ite_neg]
        have := le_toNat_sub k (b + BitVec.ofNat 64 o) n (by omega) (by omega)
        omega
      refine ⟨hm.regs, hm.flags, hm.regions, fun r' b' sz' hb' i hi => ?_, hm.labels,
        hm.bounds, hm.aliases, fun k hk => ?_, hm.known, hm.roRegions⟩
      · have hK : (b' + BitVec.ofNat 64 i).toNat = b'.toNat + i :=
          toNat_add_ofNat b' i (by have := hwf.noWrap r' b' sz' hb'; omega)
        by_cases hin : r' = r ∧ o ≤ i ∧ i < o + n
        · obtain ⟨rfl, hi1, hi2⟩ := hin
          rw [hb] at hb'
          cases hb'
          show _ = memByte env (⟨r', o, n, u⟩ :: _) r' b i
          rw [get?_storeInt _ _ _ _ _ hn, ite_pos (by
            rw [toNat_sub_of_le _ _ (by omega)]
            omega), toNat_sub_of_le _ _ (by omega), hK, hA,
            show b.toNat + i - (b.toNat + o) = i - o by omega, hval (i - o) (by omega)]
          unfold memByte
          rw [findWrite_cons, ite_pos ⟨rfl, hi1, hi2⟩]
        · rw [hout _ (by
            by_cases hr : r' = r
            · subst hr
              rw [hb] at hb'
              cases hb'
              omega
            · rcases hwf.disjointOf r r' b b' sz sz' (hm.roRegions ▸ hro) (Ne.symm hr) hb hb' with h1 | h1 <;> omega),
            hm.mem r' b' sz' hb' i hi]
          show _ = memByte env (⟨r, o, n, u⟩ :: _) r' b' i
          unfold memByte
          have hf : findWrite r' i (⟨r, o, n, u⟩ :: S.mem.filter fun w =>
              !decide (w.r = r ∧ o ≤ w.off ∧ w.off + w.n ≤ o + n)) = findWrite r' i S.mem := by
            rw [findWrite_cons, ite_neg (by
              intro hc
              exact hin ⟨hc.1.symm, hc.2⟩)]
            apply findWrite_filter
            intro w _ hpw hc
            simp only [Bool.not_eq_false', decide_eq_true_eq] at hpw
            exact hin ⟨hc.1.symm.trans hpw.1, by omega⟩
          rw [hf]
      · show (Mem.storeInt m.dmem (b + BitVec.ofNat 64 o) n val).get? k = _
        rw [hout k (by
          have := hk r b sz hb
          omega)]
        exact hm.outside k hk

end

end NativeRustcX64.Sym
