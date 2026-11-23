module

public import NativeRustcVmArm.Layout.Body
public import NativeRustcVmArm.Layout.Frame
public import NativeRustcVmArm.Layout.BuildLayout.Exec
public import NativeVm.Math.Layout

/-!
# `build_layout`'s proof: its tests, words in memory, calls in a body

- The power-of-two test (`x ^ (x - 1) > x - 1`, `pow2_test`) is the model's `log2Strict` check
  (`pow2_iff`); the size checks of `b2` and `b8` as the executor states them (`cond2`, `cond8`).
- Words at offsets of a region (`Ws`), kept by a block whose writes miss them (`Ws.keep`, by
  `decide` on the block's writes, `Misses`) and by a change outside the region (`Ws.of_same`).
- A call that changes bytes inside the outputs or the stack but off the prologue's slots keeps a
  body (`Body.of_call_stack`).
-/

namespace NativeRustcVmArm.Layout.BuildLayout

open NativeRustcArm NativeRustcArm.Sym
open NativeRustcVmArm.Arrays (Body)

public section

/-! ## The power-of-two test -/

theorem pow2_iff : ∀ n, 0 < n → (n &&& (n - 1) = 0 ↔ n - 1 < n ^^^ (n - 1))
  | n, hn => by
    have hX : n ^^^ (n - 1) = 2 * (n / 2 ^^^ (n - 1) / 2) + 1 := by
      have h1 : (n ^^^ (n - 1)) % 2 = 1 := by
        rw [Nat.xor_mod_two_eq_one]; omega
      have h2 := Nat.xor_div_two (a := n) (b := n - 1)
      omega
    have hA : n &&& (n - 1) = 2 * (n / 2 &&& (n - 1) / 2) := by
      have h1 : (n &&& (n - 1)) % 2 = 0 := by
        have := (Nat.and_mod_two_eq_one (a := n) (b := n - 1)).not
        omega
      have h2 := Nat.and_div_two (a := n) (b := n - 1)
      omega
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hm : 0 < m := by omega
      have ih := pow2_iff m hm
      rw [hA, hX, show 2 * m / 2 = m by omega, show (2 * m - 1) / 2 = m - 1 by omega]
      omega
    · rw [hA, hX, show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 - 1) / 2 = m by omega,
        Nat.and_self, Nat.xor_self]
      omega
  termination_by n => n
  decreasing_by omega

/-- **`b0`'s test**: `x ^ (x - 1) ≤ x - 1`, the length not a power of two. -/
theorem pow2_test (x : BitVec 64) :
    ((x ^^^ x - 1#64).ult (x - 1#64) || x ^^^ x - 1#64 == x - 1#64) = true ↔
      ¬(0 < x.toNat ∧ x.toNat &&& (x.toNat - 1) = 0) := by
  by_cases h0 : x.toNat = 0
  · have : x = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h0)
    subst this
    simp
  · have hs : (x - 1#64).toNat = x.toNat - 1 :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)
    have hp := pow2_iff x.toNat (by omega)
    simp only [Bool.or_eq_true, BitVec.ult, decide_eq_true_eq, beq_iff_eq, ← BitVec.toNat_inj,
      BitVec.toNat_xor, hs]
    omega

/-- **`b2`'s test**: the bytecode's bit length below `5`, or the memory's log-size outside
`1 … 30`. -/
theorem cond2 (x y : BitVec 64) (bl : Nat) (hx : x.toNat = bl) (h1 : 1 ≤ bl) :
    ((if (!BitVec.unsigned (x - 5#64 + 5#64) != BitVec.unsigned (x - 5#64) + (5#64).unsigned ||
          x - 5#64 + 5#64 == 0#64) = true then !BitVec.ult (y - 1#64) 29#64 else true) &&
      !if (!BitVec.unsigned (x - 5#64 + 5#64) != BitVec.unsigned (x - 5#64) + (5#64).unsigned ||
          x - 5#64 + 5#64 == 0#64) = true then y - 1#64 == 29#64 else false) = true ↔
      ¬(5 ≤ bl ∧ 1 ≤ y.toNat ∧ y.toNat ≤ 30) := by
  have hbl := x.isLt
  rw [BitVec.sub_add_cancel]
  have hz : (x == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; rw [h] at hx; simp at hx; omega
  have hu : (!BitVec.unsigned x != BitVec.unsigned (x - 5#64) + (5#64).unsigned) =
      decide (5 ≤ bl) := by
    simp only [bne, Bool.not_not, BitVec.unsigned, BitVec.toNat_sub, hx, BitVec.toNat_ofNat]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    by_cases h5 : 5 ≤ bl
    · rw [show (2 ^ 64 - 5 % 2 ^ 64 + bl) % 2 ^ 64 = bl - 5 by omega]; omega
    · rw [show (2 ^ 64 - 5 % 2 ^ 64 + bl) % 2 ^ 64 = 2 ^ 64 - 5 + bl by omega]; omega
  rw [hu, hz, Bool.or_false]
  have hy := y.isLt
  by_cases h5 : 5 ≤ bl
  · simp only [h5, decide_true, ↓reduceIte, true_and, Bool.and_eq_true, Bool.not_eq_true',
      BitVec.ult, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq, ← BitVec.toNat_inj,
      BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · simp [h5]

/-- **`b8`'s test**: the bytecode's log-size past `30`, or the last row count past `2 ^ 30`. -/
theorem cond8 (x r : BitVec 64) (bl : Nat) (hx : x.toNat = bl) (h5 : 5 ≤ bl) :
    (if (BitVec.ult (x - 5#64) 30#64 || x - 5#64 == 30#64) = true then
        !r.ult 1073741825#64 else true) = true ↔ ¬(bl - 5 ≤ 30 ∧ r.toNat ≤ 2 ^ 30) := by
  have hs : (x - 5#64).toNat = bl - 5 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega) |>.trans (by rw [hx]; rfl)
  by_cases hb : bl - 5 ≤ 30
  · have : (BitVec.ult (x - 5#64) 30#64 || x - 5#64 == 30#64) = true := by
      simp only [Bool.or_eq_true, BitVec.ult, decide_eq_true_eq, beq_iff_eq, ← BitVec.toNat_inj,
        hs]
      simp; omega
    rw [Arrays.ite_bool, this, Bool.cond_true]
    simp only [Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not]
    simp; omega
  · have : (BitVec.ult (x - 5#64) 30#64 || x - 5#64 == 30#64) = false := by
      simp only [Bool.or_eq_false_iff, BitVec.ult, decide_eq_false_iff_not, beq_eq_false_iff_ne,
        ne_eq, ← BitVec.toNat_inj, hs]
      simp; omega
    rw [Arrays.ite_bool, this, Bool.cond_false]
    simp; omega

/-- `b3`'s test: the first row count past `2 ^ 30`. -/
theorem cond3 (r : BitVec 64) :
    (!r.ult 1073741824#64 && !(r == 1073741824#64)) = true ↔ ¬r.toNat ≤ 2 ^ 30 := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
    beq_eq_false_iff_ne, ne_eq, ← BitVec.toNat_inj]
  simp; omega

/-! ## Words at offsets of a region -/

/-- The words `ws` (offset, value) from `b`. -/
@[expose] def Ws (d : Mem 64) (b : BitVec 64) (ws : List (Nat × UInt64)) : Prop :=
  ∀ p ∈ ws, NativeRustcVm.WordAt d (b + BitVec.ofNat 64 p.1) p.2

theorem Ws.nil (d : Mem 64) (b : BitVec 64) : Ws d b [] := nofun

theorem Ws.cons {d : Mem 64} {b : BitVec 64} {o : Nat} {v : UInt64} {ws : List (Nat × UInt64)}
    (h : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) v) (hs : Ws d b ws) :
    Ws d b ((o, v) :: ws) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h
  · exact hs p hp

theorem Ws.get {d : Mem 64} {b : BitVec 64} {ws : List (Nat × UInt64)} (h : Ws d b ws)
    {o : Nat} {v : UInt64} (hp : (o, v) ∈ ws) : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) v :=
  h (o, v) hp

/-- **Words a block missed**: those of region 0 at offsets its writes miss. -/
theorem Ws.keep [Labels] {st m : MachineData} {b : BitVec 64} {n : Nat}
    {rs : List (BitVec 64 × Nat)} {S : SState} (hm : Match (Env.ofMachine st ((b, n) :: rs)) S m)
    (hwf : (Env.ofMachine st ((b, n) :: rs)).WF) {ws : List (Nat × UInt64)}
    (hin : ∀ p ∈ ws, p.1 + 8 ≤ n) (h : Ws st.dmem b ws) (hmiss : Misses S (ws.map (·.1)) = true) :
    Ws m.dmem b ws := by
  intro p hp
  have hle := hin p hp
  have hnw := hwf.noWrap 0 b n rfl
  refine NativeRustcVm.Layout.BytesAt.of_same (h p hp) (n := 8) (fun j hj ↦ ?_)
    (by rw [NativeRustcVm.length_wordBytes])
  rw [NativeRustcVm.addr_add_add]
  refine hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ ?_
  simp only [Misses, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmiss
  obtain ⟨hr, hos⟩ := hmiss w hw
  have ho := hos p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  rw [hr] at hb'
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at h1 h2
  omega

/-- Words kept where memory did not change. -/
theorem Ws.of_same {d d' : Mem 64} {b : BitVec 64} {ws : List (Nat × UInt64)} (h : Ws d b ws)
    (hs : ∀ p ∈ ws, ∀ j < 8, d'.get? (b + BitVec.ofNat 64 (p.1 + j)) =
      d.get? (b + BitVec.ofNat 64 (p.1 + j))) : Ws d' b ws := fun p hp ↦
  NativeRustcVm.Layout.BytesAt.of_same (h p hp) (n := 8)
    (fun j hj ↦ by rw [NativeRustcVm.addr_add_add]; exact hs p hp j hj)
    (by rw [NativeRustcVm.length_wordBytes])

/-! ## Calls in a body -/

/-- **A call that changes only bytes of the outputs or the stack** off the top `G` bytes of the
frame, which hold the slots, keeps a body. -/
theorem Body.of_call_stack {m0 st st' : MachineData} {F S G : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} (hb : Body m0 F S slots oa on st) {R : BitVec 64 → Prop}
    (hsame : NativeRustcVm.SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → (InRange oa on p ∨ InRange (stackBelow m0 S) S p) ∧
      ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 G) G p)
    (hsaved : Saved st st') (hslots : ∀ p ∈ slots, F - G ≤ p.1 ∧ p.1 + 8 ≤ F) (hGF : G ≤ F)
    (hF : F ≤ m0.regs.SP.toNat) : Body m0 F S slots oa on st' := by
  refine ⟨hsaved.2.1 ▸ hb.sp, fun p hp i hi ↦ ?_, fun r hr hn ↦ (hsaved.1 r hr).trans
    (hb.regs r hr hn), fun p hp ↦ ?_, fun p hp ↦ hsaved.2.2 p (hb.kept p hp)⟩
  · rw [hsame _ fun h ↦ (hR _ h).2 ?_]
    · exact hb.frame p hp i hi
    · simp only [List.length_map, List.length_range] at hi
      have := hslots p hp
      have hsp := m0.regs.SP.toNat_lt
      have hF' : F ≤ m0.regs.SP.toBitVec.toNat := hF
      unfold InRange
      rw [show m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i -
          (m0.regs.SP.toBitVec - BitVec.ofNat 64 G) = BitVec.ofNat 64 (p.1 + i - (F - G)) by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
        omega, BitVec.toNat_ofNat]
      omega
  · rw [hsame p fun h ↦ hp (hR p h).1]
    exact hb.same p hp

/-- **The callee's stack** at SP the frame's base, inside a body's stack. -/
theorem stackOk_body {m0 st : MachineData} {F S n' : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} (hS : StackOk m0 S) (hb : Body m0 F S slots oa on st)
    (hF16 : F % 16 = 0) (hle : F + n' ≤ S) : StackOk st n' := by
  obtain ⟨hal, hSle, hmap⟩ := hS
  have hsp : st.regs.SP.toNat = m0.regs.SP.toNat - F := by
    rw [← UInt64.toNat_toBitVec, hb.sp, Arrays.toNat_sub_ofNat (by simp at hSle ⊢; omega)]
    rfl
  refine ⟨by rw [hsp]; omega, by rw [hsp]; omega, fun i hi ↦ ?_⟩
  have := hb.kept _ (hmap (S - F - n' + i) (by omega))
  have hS' : S ≤ m0.regs.SP.toBitVec.toNat := hSle
  have e : st.regs.SP.toBitVec - BitVec.ofNat 64 n' + BitVec.ofNat 64 i =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - F - n' + i) := by
    rw [hb.sp]
    bv_omega
  rw [e]
  exact this

/-! ## Numbers in memory -/

theorem toNat_toUInt64' {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toNat = x := by
  rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- **Numbers read back**: the words of `xs` at `a` are `xs`. -/
theorem natsOf_of_words {m : MachineData} {a : UInt64} {xs : Array Nat} {n : Nat}
    (h : NativeRustcVm.WordsAt m.dmem a.toBitVec (natWords xs)) (hlt : ∀ x ∈ xs, x < 2 ^ 64)
    (hn : xs.size = n) :
    natsOf m a n = xs := by
  have hw := NativeRustcVm.wordsOf_of_wordsAt h
  have hl : (natWords xs).length = n := by simp [natWords, hn]
  rw [hl] at hw
  unfold natsOf
  rw [hw]
  apply Array.ext (by simp [natWords, hn]) fun i h1 h2 ↦ ?_
  simp only [natWords, List.getElem_toArray, List.getElem_map, Array.getElem_toList]
  exact toNat_toUInt64' (hlt _ (Array.getElem_mem _))

/-- Numbers from words at `a + 8 t`. -/
theorem wordsAt_natWords {d : Mem 64} {a : BitVec 64} {xs : Array Nat}
    (h : ∀ t (ht : t < xs.size), NativeRustcVm.WordAt d (a + BitVec.ofNat 64 (8 * t)) xs[t].toUInt64) :
    NativeRustcVm.WordsAt d a (natWords xs) :=
  NativeRustcVm.wordsAt_iff.mpr fun i hi ↦ by
    simp only [natWords, List.length_map, Array.length_toList] at hi
    simpa [natWords] using h i hi

/-! ## The model -/

open NativeVm.Math.Layout in
theorem kapF_le {lm lb : Nat} {hs : Array Nat} (hlm : lm ≤ 30) (hlb : lb ≤ 30)
    (hh : ∀ t < 6, hs.getD t 0 ≤ 30) (c : Nat) : kapF lm lb hs c ≤ 36 := by
  have := hh 0 (by omega); have := hh 1 (by omega); have := hh 2 (by omega)
  have := hh 3 (by omega); have := hh 4 (by omega); have := hh 5 (by omega)
  unfold kapF
  split_ifs <;> omega

open NativeVm.Math.Layout in
theorem heights_le {rows : Array Nat} (hs : rows.size = 6) (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30)
    {t : Nat} (ht : t < 6) : (heightsF rows).getD t 0 ≤ 30 := by
  rw [heightsF_getD hs ht]
  have := log2Ceil_le (hr t ht)
  unfold floorF
  split_ifs <;> omega

open NativeVm.Math.Layout in
theorem layoutF_placements (bc : Array UInt64) (lm lb : Nat) (rows : Array Nat) :
    (layoutF bc lm lb rows).placements =
      (NativeVm.Model.placementsOf (NativeVm.Model.columnKappas lm lb (heightsF rows))).1 ∧
    (layoutF bc lm lb rows).stackLog =
      (NativeVm.Model.placementsOf (NativeVm.Model.columnKappas lm lb (heightsF rows))).2 :=
  ⟨rfl, rfl⟩

/-! ## Where calls write -/

theorem sp_toNat_sub {m0 : MachineData} {n : Nat} (h : n ≤ m0.regs.SP.toNat) :
    (m0.regs.SP.toBitVec - BitVec.ofNat 64 n).toNat = m0.regs.SP.toNat - n :=
  Arrays.toNat_sub_ofNat h

/-- Bytes below SP less `G`, or at SP and above, are not among the top `G` bytes of the stack. -/
theorem not_top {m0 : MachineData} {G : Nat} {p : BitVec 64} (hG : G ≤ m0.regs.SP.toNat)
    (h : p.toNat < m0.regs.SP.toNat - G ∨ m0.regs.SP.toNat ≤ p.toNat) :
    ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 G) G p := by
  have e := sp_toNat_sub hG
  have hnw : NoWrap (m0.regs.SP.toBitVec - BitVec.ofNat 64 G) G := by
    unfold NoWrap; rw [e]; have := m0.regs.SP.toNat_lt; omega
  rw [inRange_iff hnw, e]
  omega

/-- A byte of a range apart from the stack is off the stack's top `G` bytes. -/
theorem not_top_of_apart {m0 : MachineData} {S G n : Nat} {a p : BitVec 64} (hS : StackOk m0 S)
    (hG : G ≤ S) (hap : Apart a n (stackBelow m0 S) S) (hnw : NoWrap a n) (hp : InRange a n p) :
    ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 G) G p := by
  have hSle : S ≤ m0.regs.SP.toNat := hS.2.1
  have e : (stackBelow m0 S).toNat = m0.regs.SP.toNat - S := sp_toNat_sub hSle
  rw [inRange_iff hnw] at hp
  unfold Apart at hap
  rw [e] at hap
  exact not_top (by omega) (by omega)

/-- A byte below the frame of `F ≥ G` bytes is off the stack's top `G` bytes. -/
theorem not_top_of_low {m0 : MachineData} {G n : Nat} {a p : BitVec 64}
    (hG : G ≤ m0.regs.SP.toNat) (hnw : NoWrap a n) (hle : a.toNat + n ≤ m0.regs.SP.toNat - G)
    (hp : InRange a n p) : ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 G) G p := by
  rw [inRange_iff hnw] at hp
  exact not_top hG (by omega)

/-- **The read-only data for a callee** using `n'` bytes below a body's frame. -/
theorem rodataAt_body [Labels] {m0 st : MachineData} {F S n' : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} (hS : StackOk m0 S) (h : RodataAt m0 S)
    (hb : Body m0 F S slots oa on st) (hra : RodataApart oa on) (hnw : NoWrap oa on)
    (hle : F + n' ≤ S) : RodataAt st n' :=
  rodataAt_callee hS h hb.same (fun q hq t ↦ by
    rcases hq with hq | hq
    · exact (hra t).not_inRange hnw (h.noWrap t) hq
    · exact (h.apart t).symm.not_inRange (Arrays.stack_noWrap hS) (h.noWrap t) hq) hb.sp hle

/-- The kappas (the frame's low `K` bytes) are off the stack's top `G` bytes and in the stack. -/
theorem kap_in {m0 : MachineData} {F S K G : Nat} {p : BitVec 64} (hS : StackOk m0 S) (hF : F ≤ S)
    (hKG : K + G ≤ F) (hp : InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) K p) :
    InRange (stackBelow m0 S) S p ∧ ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 G) G p := by
  have hFs : F ≤ m0.regs.SP.toNat := Nat.le_trans hF hS.2.1
  have e := sp_toNat_sub hFs
  have hnw : NoWrap (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) K := by
    unfold NoWrap; rw [e]; have := m0.regs.SP.toNat_lt; omega
  have hnwF : NoWrap (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) F := by
    unfold NoWrap; rw [e]; have := m0.regs.SP.toNat_lt; omega
  refine ⟨frame_in_stack hS hF (NativeRustcVm.InRange.mono hp hnw hnwF
    (Nat.le_refl _) (Nat.add_le_add_left (by omega) _)), not_top_of_low (by omega) hnw (by rw [e]; omega) hp⟩

end

end NativeRustcVmArm.Layout.BuildLayout
