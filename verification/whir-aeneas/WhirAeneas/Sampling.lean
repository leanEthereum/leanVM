import WhirAeneas.Replay

/-! The generated `sample_queries` is the model's `deriveQueries` on the squeezed elements it
reads, read as 192-bit numbers. -/
namespace WhirAeneas.Sampling
open Aeneas Aeneas.Std ReplaySource Whir Whir.Concrete WhirAeneas.Fold WhirAeneas.Replay

/-! ## Scalar operations -/

theorem shr_val {ty : UScalarTy} (x : UScalar ty) (n : Usize) (h : n.val < ty.numBits) :
    (UScalar.wrapping_shr_rhs x n).val = x.val / 2 ^ n.val := by
  simp only [UScalar.wrapping_shr_rhs, WrappingShiftRhs.amount_unsigned]
  rw [Nat.mod_eq_of_lt h]
  show (x.bv >>> n.val).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

theorem shl_val {ty : UScalarTy} (x : UScalar ty) (n : Usize) (h : n.val < ty.numBits) :
    (UScalar.wrapping_shl_rhs x n).val = (x.val * 2 ^ n.val) % 2 ^ ty.numBits := by
  simp only [UScalar.wrapping_shl_rhs, WrappingShiftRhs.amount_unsigned]
  rw [Nat.mod_eq_of_lt h]
  show (x.bv <<< n.val).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rfl

/-! ## One chunk of a squeezed element -/

theorem mod_add_pow_mul (x y k d : Nat) (h : d ≤ k) : (x + 2 ^ k * y) % 2 ^ d = x % 2 ^ d := by
  rw [show 2 ^ k * y = 2 ^ d * (2 ^ (k - d) * y) by rw [← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega]
  exact Nat.add_mul_mod_self_left x (2 ^ d) _

theorem div_split (L0 R sh : Nat) (hsh : sh ≤ 64) :
    (L0 + 2 ^ 64 * R) / 2 ^ sh = L0 / 2 ^ sh + 2 ^ (64 - sh) * R := by
  rw [show 2 ^ 64 * R = 2 ^ sh * (2 ^ (64 - sh) * R) by rw [← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega]
  exact Nat.add_mul_div_left _ _ (Nat.two_pow_pos sh)

/-- A chunk at bit offset `sh` of limb `L0`, completed from the next limb `L1` when it
crosses the limb boundary, is the `d` bits at `sh` of the number. -/
theorem chunk_core (L0 L1 L2 sh d : Nat) (h0 : L0 < 2 ^ 64) (hsh : sh < 64) (hd : d ≤ 64) :
    (if 64 < sh + d then L0 / 2 ^ sh ||| (L1 * 2 ^ (64 - sh)) % 2 ^ 64 else L0 / 2 ^ sh) % 2 ^ d =
      ((L0 + 2 ^ 64 * (L1 + 2 ^ 64 * L2)) / 2 ^ sh) % 2 ^ d := by
  rw [div_split _ _ _ hsh.le]
  split
  · rename_i hc
    have hlo : L0 / 2 ^ sh < 2 ^ (64 - sh) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos sh), ← Nat.pow_add]
      rw [show 64 - sh + sh = 64 by omega]; exact h0
    have hm : (L1 * 2 ^ (64 - sh)) % 2 ^ 64 = 2 ^ (64 - sh) * (L1 % 2 ^ sh) := by
      rw [show (2 : Nat) ^ 64 = 2 ^ (64 - sh) * 2 ^ sh by rw [← Nat.pow_add]; congr 1; omega,
        Nat.mul_comm L1, Nat.mul_mod_mul_left]
    rw [hm, Nat.lor_comm, ← Nat.two_pow_add_eq_or_of_lt hlo]
    have hsplit : 2 ^ (64 - sh) * (L1 + 2 ^ 64 * L2) =
        2 ^ (64 - sh) * (L1 % 2 ^ sh) + 2 ^ 64 * (L1 / 2 ^ sh + 2 ^ (64 - sh) * L2) := by
      have := Nat.mod_add_div L1 (2 ^ sh)
      have hp : (2 : Nat) ^ 64 = 2 ^ (64 - sh) * 2 ^ sh := by rw [← Nat.pow_add]; congr 1; omega
      conv_lhs => rw [← this]
      rw [hp]; ring
    rw [hsplit, ← Nat.add_assoc, Nat.add_comm (L0 / 2 ^ sh), mod_add_pow_mul _ _ _ _ hd]
  · rename_i hc
    exact (mod_add_pow_mul _ _ _ _ (by omega)).symm

/-- The number a squeezed element's three limbs denote. -/
def limbsNat (x0 x1 x2 : U64) : Nat := x0.val + 2 ^ 64 * (x1.val + 2 ^ 64 * x2.val)

theorem rem_ok {ty : UScalarTy} (x y : UScalar ty) (h : y.val ≠ 0) :
    ∃ z : UScalar ty, x % y = Result.ok z ∧ z.val = x.val % y.val := by
  refine ⟨⟨x.bv % y.bv⟩, ?_, ?_⟩
  · conv => lhs; simp [HMod.hMod]
    simp [h, UScalar.rem]
  · show (x.bv % y.bv).toNat = x.bv.toNat % y.bv.toNat
    exact BitVec.toNat_umod

/-- One iteration of `push_chunks` pushes chunk `j`: the `d` bits at offset `j * d`. -/
theorem push_chunks_body (hw : System.Platform.numBits = 64) (limbs : Array U64 3#usize) (x0 x1 x2 : U64)
    (hl : limbs.val = [x0, x1, x2]) (d take : Usize) (hd0 : 0 < d.val) (hd : d.val < 64)
    (out : alloc.vec.Vec Usize) (j : Usize) (hj : j.val < take.val)
    (hoff : j.val * d.val + d.val ≤ 192) (hcap : out.val.length < Usize.max) :
    ∃ out', whir.query.push_chunks_loop.body limbs d take out j =
        .ok (.cont (out', Std.Usize.wrapping_add j 1#usize)) ∧
      out'.val.map (·.val) = out.val.map (·.val) ++ [(limbsNat x0 x1 x2 / 2 ^ (j.val * d.val)) % 2 ^ d.val] := by
  have hU : UScalarTy.Usize.numBits = 64 := by simp [hw]
  have hoffv : (Std.Usize.wrapping_mul j d).val = j.val * d.val := by
    rw [Std.Usize.wrapping_mul_val_eq, UScalar.size_def, hU]; apply Nat.mod_eq_of_lt; omega
  obtain ⟨li, hli, eli⟩ := UScalar.div_spec (Std.Usize.wrapping_mul j d) (y := 64#usize) (by simp)
  obtain ⟨sh, hsh, esh⟩ := rem_ok (Std.Usize.wrapping_mul j d) 64#usize (by simp)
  have h64 : (64#usize : Usize).val = 64 := by simp
  rw [hoffv, h64] at eli esh
  have hli3 : li.val < 3 := by rw [eli]; omega
  have hsh64 : sh.val < 64 := by rw [esh]; omega
  have hoffs : j.val * d.val = 64 * li.val + sh.val := by rw [eli, esh]; omega
  have hidx : ∀ i : Usize, (hi : i.val < 3) → Array.index_usize limbs i = .ok ([x0, x1, x2][i.val]'(by simpa using hi)) := by
    intro i hi
    simp [Array.index_usize, hl]
    rw [List.getElem?_eq_getElem (by simpa using hi)]
  have hjt : j < take := by simpa [UScalar.lt_equiv] using hj
  set L0 := [x0, x1, x2][li.val]'(by simpa using hli3) with hL0
  have hc : (Std.U64.wrapping_shr L0 sh).val = L0.val / 2 ^ sh.val := shr_val L0 sh (by simp; omega)
  have hsd : (Std.Usize.wrapping_add sh d).val = sh.val + d.val := by
    rw [Std.Usize.wrapping_add_val_eq, UScalar.size_def, hU]; apply Nat.mod_eq_of_lt; omega
  have hbm : (Std.Usize.wrapping_sub (Std.Usize.wrapping_shl 1#usize d) 1#usize).val = 2 ^ d.val - 1 := by
    rw [Fold.sub_val _ _ (by rw [Replay.shl_one_val hw d hd]; exact Nat.one_le_two_pow),
      Replay.shl_one_val hw d hd]; simp
  have hcast : ∀ x : U64, (UScalar.cast .Usize x).val = x.val := by
    intro x; rw [UScalar.cast_val_eq, hU]; exact Nat.mod_eq_of_lt (by have := x.hBounds; simpa using this)
  have b0 := x0.hBounds; have b1 := x1.hBounds
  simp only [UScalar.size_def, UScalarTy.U64_numBits_eq] at b0 b1
  have hA : limbsNat x0 x1 x2 / 2 ^ 64 = x1.val + 2 ^ 64 * x2.val := by
    unfold limbsNat; rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt b0, Nat.zero_add]
  have hB : (x1.val + 2 ^ 64 * x2.val) / 2 ^ 64 = x2.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt b1, Nat.zero_add]
  obtain ⟨L1, L2, hNL, hcross⟩ : ∃ L1 L2 : Nat,
      limbsNat x0 x1 x2 / 2 ^ (64 * li.val) = L0.val + 2 ^ 64 * (L1 + 2 ^ 64 * L2) ∧
      (64 < sh.val + d.val → ∃ h : li.val + 1 < 3, L1 = ([x0, x1, x2][li.val + 1]'(by simpa using h)).val) := by
    rcases (show li.val = 0 ∨ li.val = 1 ∨ li.val = 2 by omega) with h | h | h
    · refine ⟨x1.val, x2.val, ?_, fun _ => ⟨by omega, by simp [h]⟩⟩
      simp only [hL0, h, Nat.mul_zero, Nat.pow_zero, Nat.div_one, limbsNat]; rfl
    · refine ⟨x2.val, 0, ?_, fun _ => ⟨by omega, by simp [h]⟩⟩
      rw [h, Nat.mul_one, hA]; simp [hL0, h]
    · refine ⟨0, 0, ?_, fun hc => absurd hc (by omega)⟩
      rw [h, show 64 * 2 = 64 + 64 from rfl, Nat.pow_add, ← Nat.div_div_eq_div_mul, hA, hB]; simp [hL0, h]
  have hN : limbsNat x0 x1 x2 / 2 ^ (j.val * d.val) = (L0.val + 2 ^ 64 * (L1 + 2 ^ 64 * L2)) / 2 ^ sh.val := by
    rw [hoffs, Nat.pow_add, ← Nat.div_div_eq_div_mul, hNL]
  have hcore := chunk_core L0.val L1 L2 sh.val d.val L0.hBounds hsh64 (by omega)
  rw [← hN] at hcore
  have hmask : ∀ x : Usize, (x &&& Std.Usize.wrapping_sub (Std.Usize.wrapping_shl 1#usize d) 1#usize).val =
      x.val % 2 ^ d.val := by
    intro x; rw [UScalar.val_and, hbm, Nat.and_two_pow_sub_one_eq_mod]
  by_cases hx : 64 < sh.val + d.val
  · obtain ⟨hl1, eL1⟩ := hcross hx
    set L1v := [x0, x1, x2][li.val + 1]'(by simpa using hl1) with hL1v
    have hli1 : (Std.Usize.wrapping_add li 1#usize).val = li.val + 1 := by
      rw [Std.Usize.wrapping_add_val_eq, UScalar.size_def, hU]; simp; omega
    have h64s : (Std.Usize.wrapping_sub 64#usize sh).val = 64 - sh.val := by
      rw [Fold.sub_val _ _ (by simp; omega)]; simp
    have hshl : (Std.U64.wrapping_shl L1v (Std.Usize.wrapping_sub 64#usize sh)).val =
        (L1v.val * 2 ^ (64 - sh.val)) % 2 ^ 64 := by
      rw [show Std.U64.wrapping_shl L1v (Std.Usize.wrapping_sub 64#usize sh) =
        UScalar.wrapping_shl_rhs L1v (Std.Usize.wrapping_sub 64#usize sh) from rfl,
        shl_val _ _ (by rw [h64s, UScalarTy.U64_numBits_eq]; omega)]
      simp [h64s]
    obtain ⟨v, hv⟩ : ∃ v, (UScalar.cast .Usize (Std.U64.wrapping_shr L0 sh |||
        Std.U64.wrapping_shl L1v (Std.Usize.wrapping_sub 64#usize sh)) &&&
        Std.Usize.wrapping_sub (Std.Usize.wrapping_shl 1#usize d) 1#usize) = v := ⟨_, rfl⟩
    have ev : v.val = (limbsNat x0 x1 x2 / 2 ^ (j.val * d.val)) % 2 ^ d.val := by
      rw [← hv, hmask, hcast, UScalar.val_or, hc, hshl, ← eL1, ← hcore, if_pos hx]
    obtain ⟨out', hpush, eout⟩ := Query.push_ok out v hcap
    refine ⟨out', ?_, by rw [eout]; simp [ev]⟩
    have hgt : Std.Usize.wrapping_add sh d > 64#usize := by simp only [gt_iff_lt, UScalar.lt_equiv, hsd]; simpa using hx
    have hidx1 := hidx (Std.Usize.wrapping_add li 1#usize) (by rw [hli1]; exact hl1)
    simp only [hli1] at hidx1
    simp only [whir.query.push_chunks_loop.body, hjt, ↓reduceIte, lift, Std.bind_ok, hli, hsh, hidx li hli3, hgt,
      hidx1, ← hL0, ← hL1v, hv, hpush]
  · obtain ⟨v, hv⟩ : ∃ v, (UScalar.cast .Usize (Std.U64.wrapping_shr L0 sh) &&&
        Std.Usize.wrapping_sub (Std.Usize.wrapping_shl 1#usize d) 1#usize) = v := ⟨_, rfl⟩
    have ev : v.val = (limbsNat x0 x1 x2 / 2 ^ (j.val * d.val)) % 2 ^ d.val := by
      rw [← hv, hmask, hcast, hc, ← hcore, if_neg hx]
    obtain ⟨out', hpush, eout⟩ := Query.push_ok out v hcap
    refine ⟨out', ?_, by rw [eout]; simp [ev]⟩
    have hgt : ¬ (Std.Usize.wrapping_add sh d > 64#usize) := by
      simp only [gt_iff_lt, UScalar.lt_equiv, hsd]; simpa using hx
    simp only [whir.query.push_chunks_loop.body, hjt, ↓reduceIte, lift, Std.bind_ok, hli, hsh, hidx li hli3, hgt,
      ← hL0, hv, hpush]

/-- `push_chunks` pushes the first `take` chunks of the limbs' number, in order. -/
theorem push_chunks_eq (hw : System.Platform.numBits = 64) (limbs : Array U64 3#usize) (x0 x1 x2 : U64)
    (hl : limbs.val = [x0, x1, x2]) (d take : Usize) (hd0 : 0 < d.val) (hd : d.val < 64)
    (htake : take.val * d.val ≤ 192) :
    ∀ (m : Nat) (j : Usize) (out : alloc.vec.Vec Usize), take.val - j.val = m → j.val ≤ take.val →
      out.val.length + (take.val - j.val) ≤ Usize.max →
      ∃ out', whir.query.push_chunks_loop out limbs d take j = .ok out' ∧
        out'.val.map (·.val) = out.val.map (·.val) ++
          (List.range' j.val (take.val - j.val)).map fun k => (limbsNat x0 x1 x2 / 2 ^ (k * d.val)) % 2 ^ d.val := by
  intro m
  induction m with
  | zero =>
    intro j out hm hj hcap
    refine ⟨out, ?_, by rw [show take.val - j.val = 0 by omega]; simp⟩
    unfold whir.query.push_chunks_loop
    apply loop_done
    have : ¬ (j < take) := by simp only [UScalar.lt_equiv]; omega
    simp [whir.query.push_chunks_loop.body, this]
  | succ m ih =>
    intro j out hm hj hcap
    have hjt : j.val < take.val := by omega
    obtain ⟨out1, hbody, e1⟩ := push_chunks_body hw limbs x0 x1 x2 hl d take hd0 hd out j hjt
      (by have : (j.val + 1) * d.val ≤ take.val * d.val := Nat.mul_le_mul_right _ hjt; rw [Nat.add_mul] at this; omega)
      (by omega)
    have hsucc := succ_val j take.val hjt (by have := take.hBounds; scalar_tac)
    have hl1 : out1.val.length = out.val.length + 1 := by simpa using congrArg List.length e1
    obtain ⟨out', hloop, e'⟩ := ih (Std.Usize.wrapping_add j 1#usize) out1 (by omega) (by omega)
      (by rw [hl1, hsucc]; omega)
    refine ⟨out', ?_, ?_⟩
    · unfold whir.query.push_chunks_loop
      rw [loop_cont hbody]
      unfold whir.query.push_chunks_loop at hloop
      exact hloop
    · rw [e', e1, hsucc, show take.val - j.val = (take.val - (j.val + 1)) + 1 by omega, List.range'_succ]
      simp

/-! ## The squeeze loop -/

/-- The challenger's squeezes: `tape ch xs` says the next `F192` verifier messages drawn from
the duplex in state `ch` are `xs`. -/
structure SqueezeTape {T0 : Type} (Ch : fiat_shamir.Challenger T0)
    (tape : T0 → List primitives.field.gf2_64x3.F192 → Prop) : Prop where
  sample : ∀ ch x rest, tape ch (x :: rest) → ∃ ch', Ch.verifier_message
    primitives.field.gf2_64x3.F192.Insts.Fiat_shamirCodecFromUniformArrayU824 ch = .ok (x, ch') ∧ tape ch' rest

/-- A squeezed element as the model's extension element. -/
def toE (x : primitives.field.gf2_64x3.F192) : Concrete.E :=
  ⟨UInt64.ofNat x.c0.val, UInt64.ofNat x.c1.val, UInt64.ofNat x.c2.val⟩

theorem toE_toNat (x : primitives.field.gf2_64x3.F192) : (toE x).toNat = limbsNat x.c0 x.c1 x.c2 := by
  have b0 := x.c0.hBounds; have b1 := x.c1.hBounds; have b2 := x.c2.hBounds
  simp only [UScalarTy.U64_numBits_eq] at b0 b1 b2
  simp [toE, E.toNat, limbsNat, Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2]
  ring

/-- The number a squeezed element denotes. -/
def sqNat (x : primitives.field.gf2_64x3.F192) : Nat := limbsNat x.c0 x.c1 x.c2

/-- Query `i`'s raw position before stratification: chunk `i mod per` of squeeze `i / per`. -/
def rawAt (ns : List Nat) (d per i : Nat) : Nat :=
  (ns.getD (i / per) 0 / 2 ^ ((i % per) * d)) % 2 ^ d

theorem sample_loop_eq (hw : System.Platform.numBits = 64) {T0 : Type} (Ch : fiat_shamir.Challenger T0)
    (tape : T0 → List primitives.field.gf2_64x3.F192 → Prop) (ht : SqueezeTape Ch tape)
    (count d per : Usize) (hd0 : 0 < d.val) (hd : d.val < 64)
    (hper : per.val = 192 / d.val) (sq : List primitives.field.gf2_64x3.F192)
    (hsq : sq.length = (count.val + per.val - 1) / per.val) (rest : List primitives.field.gf2_64x3.F192) :
    ∀ (m k : Nat) (ch : T0) (out : alloc.vec.Vec Usize), sq.length - k = m → k ≤ sq.length →
      tape ch (sq.drop k ++ rest) → out.val.length = min (k * per.val) count.val →
      out.val.map (·.val) = (List.range out.val.length).map (rawAt (sq.map sqNat) d.val per.val) →
      ∃ ch' out', whir.query.sample_queries_loop0 Ch ch d count per out = .ok (ch', out') ∧
        tape ch' rest ∧ out'.val.map (·.val) = (List.range count.val).map (rawAt (sq.map sqNat) d.val per.val) := by
  have hp0 : 0 < per.val := by rw [hper]; exact Nat.div_pos (by omega) hd0
  have hpd : per.val * d.val ≤ 192 := by rw [hper]; exact Nat.div_mul_le_self 192 d.val
  have hceil : ∀ k, k < sq.length ↔ k * per.val < count.val := by
    intro k
    rw [hsq, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hp0, Nat.add_mul]; omega
  intro m
  induction m with
  | zero =>
    intro k ch out hm hk hch hlen hout
    have hk' : k = sq.length := by omega
    have hge : count.val ≤ k * per.val := by have := (hceil k).not.mp (by omega); omega
    have hlc : out.val.length = count.val := by rw [hlen]; omega
    refine ⟨ch, out, ?_, by rw [hk', List.drop_length] at hch; exact hch, by rw [hout, hlc]⟩
    unfold whir.query.sample_queries_loop0
    apply loop_done
    have : ¬ (alloc.vec.Vec.len out < count) := by
      rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simp only [alloc.vec.Vec.length]; omega
    simp [whir.query.sample_queries_loop0.body, this]
  | succ m ih =>
    intro k ch out hm hk hch hlen hout
    have hkl : k < sq.length := by omega
    have hkc : k * per.val < count.val := (hceil k).mp hkl
    have hlo : out.val.length = k * per.val := by rw [hlen]; omega
    obtain ⟨ch1, hsample, hch1⟩ := ht.sample ch sq[k] (sq.drop (k + 1) ++ rest)
      (by rw [List.drop_eq_getElem_cons hkl] at hch; exact hch)
    have hcm : count.val ≤ Usize.max := by clear * - count; scalar_tac
    have hU : UScalarTy.Usize.numBits = 64 := by simp [hw]
    have hsub : (Std.Usize.wrapping_sub count (alloc.vec.Vec.len out)).val = count.val - k * per.val := by
      rw [Fold.sub_val _ _ (by simp; omega)]; simp [hlo]
    obtain ⟨take, htk, etk⟩ : ∃ take, core.cmp.impls.OrdUsize.min per
        (Std.Usize.wrapping_sub count (alloc.vec.Vec.len out)) = take ∧
        take.val = min per.val (count.val - k * per.val) := ⟨_, rfl, by simp [core.cmp.impls.OrdUsize.min_val, hsub]⟩
    have hz0 : (0#usize : Usize).val = 0 := by simp
    let limbs := Array.make 3#usize [sq[k].c0, sq[k].c1, sq[k].c2]
    obtain ⟨out1, hloop1, e1⟩ := push_chunks_eq hw limbs sq[k].c0 sq[k].c1 sq[k].c2 rfl d take hd0 hd
      (by rw [etk]; exact le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) hpd) _ 0#usize out rfl (by simp)
      (by rw [hz0, etk, hlo, Nat.sub_zero]; omega)
    have hlt : alloc.vec.Vec.len out < count := by
      rw [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simp only [alloc.vec.Vec.length]; omega
    have hbody : whir.query.sample_queries_loop0.body Ch d count per ch out = .ok (.cont (ch1, out1)) := by
      simp only [whir.query.sample_queries_loop0.body, hlt, ↓reduceIte, Std.bind_ok, hsample, lift, htk]
      simp [whir.query.push_chunks, limbs] at hloop1 ⊢
      rw [hloop1]; simp only [Std.bind_ok]
    have hl1 : out1.val.length = min ((k + 1) * per.val) count.val := by
      have := congrArg List.length e1; simp at this; rw [this, hlo, etk, Nat.add_mul]; omega
    obtain ⟨ch', out', hloop, hch', hout'⟩ := ih (k + 1) ch1 out1 (by omega) (by omega)
      hch1 hl1 (by
        rw [e1, hout, hlo, hl1]
        rw [show min ((k + 1) * per.val) count.val = k * per.val + min per.val (count.val - k * per.val) by
          rw [Nat.add_mul]; omega, List.range_add, List.map_append]
        congr 1
        simp only [hz0, Nat.sub_zero, etk, List.range'_eq_map_range, List.map_map]
        apply List.map_congr_left
        intro j hj
        simp only [List.mem_range] at hj
        have hjp : j < per.val := lt_of_lt_of_le hj (Nat.min_le_left _ _)
        simp only [Function.comp, rawAt, Nat.zero_add]
        rw [show (k * per.val + j) / per.val = k by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hjp, Nat.zero_add],
          show (k * per.val + j) % per.val = j by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjp]]
        simp [List.getD_eq_getElem?_getD, hkl, sqNat])
    refine ⟨ch', out', ?_, hch', hout'⟩
    unfold whir.query.sample_queries_loop0
    rw [loop_cont hbody]
    unfold whir.query.sample_queries_loop0 at hloop
    exact hloop

/-! ## Strata -/

/-- A group of `2^g` queries fixing their top `min g depth` bits to the query index. -/
def groupList (g depth : Nat) : List (Nat × Nat) :=
  (List.range (2 ^ g)).map fun j => (min g depth, j % 2 ^ (min g depth))

/-- The strata over groups `gs`, highest first, of the set bits of `count`. -/
def strataList (count depth : Nat) (gs : List Nat) : List (Nat × Nat) :=
  gs.flatMap fun g => if count.testBit g then groupList g depth else []

theorem forIn_append_flatMap (p : Nat → Bool) (f : Nat → List (Nat × Nat)) (gs : List Nat)
    (acc : Array (Nat × Nat)) :
    (forIn (m := Id) gs acc fun g s =>
        if p g = true then pure (ForInStep.yield (s ++ (f g).toArray)) else pure (ForInStep.yield s)).run.toList =
      acc.toList ++ gs.flatMap fun g => if p g = true then f g else [] := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    by_cases hp : p g = true
    · simp only [List.forIn_cons, hp, ↓reduceIte, List.flatMap_cons]
      erw [ih]; simp
    · simp only [List.forIn_cons, hp, ↓reduceIte, List.flatMap_cons, Bool.false_eq_true]
      erw [ih]; simp

theorem strata_model (count depth : Nat) :
    (Concrete.strata count depth).toList = strataList count depth (List.range (count.log2 + 1)).reverse := by
  simp [Concrete.strata, strataList, groupList]
  rw [forIn_append_flatMap (fun g => count.testBit g) (fun g => (List.range' 0 (2 ^ g)).map
    fun x => (min g depth, x % 2 ^ min g depth))]
  simp [List.range_eq_range']

/-- A stratum as the model's pair. -/
def pr (st : whir.query.Stratum) : Nat × Nat := (st.bits.val, st.index.val)

theorem push_group_eq (hw : System.Platform.numBits = 64) (g bits : Usize) (hg : g.val < 64) (hb : bits.val < 64) :
    ∀ (m : Nat) (j : Usize) (out : alloc.vec.Vec whir.query.Stratum), 2 ^ g.val - j.val = m → j.val ≤ 2 ^ g.val →
      out.val.length + (2 ^ g.val - j.val) ≤ Usize.max →
      ∃ out', whir.query.Stratum.push_group_loop out g bits j = .ok out' ∧
        out'.val.map pr = out.val.map pr ++
          (List.range' j.val (2 ^ g.val - j.val)).map fun k => (bits.val, k % 2 ^ bits.val) := by
  have hg1 := shl_one_val hw g hg
  have hb1 := shl_one_val hw bits hb
  have hU : UScalarTy.Usize.numBits = 64 := by simp [hw]
  intro m
  induction m with
  | zero =>
    intro j out hm hj hcap
    refine ⟨out, ?_, by rw [show 2 ^ g.val - j.val = 0 by omega]; simp⟩
    unfold whir.query.Stratum.push_group_loop
    apply loop_done
    have : ¬ (j.val < (Std.Usize.wrapping_shl 1#usize g).val) := by rw [hg1]; omega
    simp [whir.query.Stratum.push_group_loop.body, lift, this]
  | succ m ih =>
    intro j out hm hj hcap
    have hjt : j.val < 2 ^ g.val := by omega
    have hlt : j < Std.Usize.wrapping_shl 1#usize g := by simp only [UScalar.lt_equiv, hg1]; omega
    have hsucc := succ_val j (2 ^ g.val) hjt (by have := Usize.max_def; scalar_tac)
    obtain ⟨st, hst⟩ : ∃ st : whir.query.Stratum,
        ({ bits := bits, index := j &&& Std.Usize.wrapping_sub (Std.Usize.wrapping_shl 1#usize bits) 1#usize } :
          whir.query.Stratum) = st := ⟨_, rfl⟩
    have est : pr st = (bits.val, j.val % 2 ^ bits.val) := by
      rw [← hst, pr]
      simp only [UScalar.val_and]
      rw [Fold.sub_val _ _ (by rw [hb1]; exact Nat.one_le_two_pow), hb1]
      simp [Nat.and_two_pow_sub_one_eq_mod]
    obtain ⟨out1, hpush, e1⟩ := Query.push_ok out st (by omega)
    have hbody : whir.query.Stratum.push_group_loop.body g bits out j =
        .ok (.cont (out1, Std.Usize.wrapping_add j 1#usize)) := by
      simp only [whir.query.Stratum.push_group_loop.body, lift, Std.bind_ok, hlt, ↓reduceIte, hst, hpush]
    obtain ⟨out', hloop, e'⟩ := ih (Std.Usize.wrapping_add j 1#usize) out1 (by omega) (by omega)
      (by rw [e1, hsucc]; simp; omega)
    refine ⟨out', ?_, ?_⟩
    · unfold whir.query.Stratum.push_group_loop
      rw [loop_cont hbody]
      unfold whir.query.Stratum.push_group_loop at hloop
      exact hloop
    · rw [e', e1, hsucc, show 2 ^ g.val - j.val = (2 ^ g.val - (j.val + 1)) + 1 by omega, List.range'_succ]
      simp [est]

theorem strataList_length (count depth g : Nat) :
    (strataList count depth (List.range g).reverse).length = count % 2 ^ g := by
  induction g with
  | zero => simp [strataList, Nat.mod_one]
  | succ g ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [strataList, List.reverse_cons, List.reverse_nil, List.nil_append] at ih ⊢
    rw [List.flatMap_append, List.length_append, ih, Nat.mod_pow_succ, List.flatMap_singleton,
      Nat.testBit_eq_decide_div_mod_eq]
    have h2 : count / 2 ^ g % 2 = 0 ∨ count / 2 ^ g % 2 = 1 := Nat.mod_two_eq_zero_or_one _
    rcases h2 with h | h <;> simp [h, groupList] <;> ring

theorem strata_loop_eq (hw : System.Platform.numBits = 64) (count depth : Usize) (hdep : depth.val < 64) :
    ∀ (m : Nat) (g : Usize) (out : alloc.vec.Vec whir.query.Stratum), g.val = m → g.val ≤ 64 →
      out.val.length + count.val % 2 ^ g.val ≤ Usize.max →
      ∃ out', whir.query.Stratum.batch_loop count depth out g = .ok out' ∧
        out'.val.map pr = out.val.map pr ++ strataList count.val depth.val (List.range g.val).reverse := by
  have hU : UScalarTy.Usize.numBits = 64 := by simp [hw]
  intro m
  induction m with
  | zero =>
    intro g out hm hg hcap
    refine ⟨out, ?_, by rw [hm]; simp [strataList]⟩
    unfold whir.query.Stratum.batch_loop
    apply loop_done
    have : ¬ (g.val > 0) := by omega
    simp [whir.query.Stratum.batch_loop.body, this]
  | succ m ih =>
    intro g out hm hg hcap
    have hgp : g > 0#usize := by simp only [gt_iff_lt, UScalar.lt_equiv]; simp; omega
    have hg1 : (Std.Usize.wrapping_sub g 1#usize).val = m := by rw [Fold.sub_val _ _ (by simp; omega)]; simp; omega
    have hsh : (Std.Usize.wrapping_shr count (Std.Usize.wrapping_sub g 1#usize)).val = count.val / 2 ^ m := by
      rw [show Std.Usize.wrapping_shr count (Std.Usize.wrapping_sub g 1#usize) =
        UScalar.wrapping_shr_rhs count (Std.Usize.wrapping_sub g 1#usize) from rfl, shr_val _ _ (by rw [hg1, hU]; omega),
        hg1]
    have hbit : (Std.Usize.wrapping_shr count (Std.Usize.wrapping_sub g 1#usize) &&& 1#usize).val =
        count.val / 2 ^ m % 2 := by
      rw [UScalar.val_and, hsh]; simp [Nat.and_one_is_mod]
    have hsplit : strataList count.val depth.val (List.range g.val).reverse =
        (if count.val.testBit m = true then groupList m depth.val else []) ++
          strataList count.val depth.val (List.range m).reverse := by
      rw [hm, List.range_succ, List.reverse_append]; simp [strataList]
    have hmod := Nat.mod_pow_succ (b := 2) (x := count.val) (k := m)
    rw [← hm] at hmod
    by_cases ht : count.val.testBit m = true
    · have h1 : count.val / 2 ^ m % 2 = 1 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at ht; simpa using ht
      have heq : (Std.Usize.wrapping_shr count (Std.Usize.wrapping_sub g 1#usize) &&& 1#usize) = 1#usize :=
        UScalar.eq_of_val_eq (by rw [hbit, h1]; simp)
      have hmin : (core.cmp.impls.OrdUsize.min (Std.Usize.wrapping_sub g 1#usize) depth).val = min m depth.val := by
        simp [core.cmp.impls.OrdUsize.min_val, hg1]
      have hz0 : (0#usize : Usize).val = 0 := by simp
      obtain ⟨out1, hpg, e1⟩ := push_group_eq hw (Std.Usize.wrapping_sub g 1#usize)
        (core.cmp.impls.OrdUsize.min (Std.Usize.wrapping_sub g 1#usize) depth) (by omega) (by rw [hmin]; omega)
        _ 0#usize out rfl (by rw [hz0]; positivity) (by rw [hz0, hg1]; rw [h1] at hmod; omega)
      have hbody : whir.query.Stratum.batch_loop.body count depth out g =
          .ok (.cont (out1, Std.Usize.wrapping_sub g 1#usize)) := by
        simp only [whir.query.Stratum.batch_loop.body, hgp, ↓reduceIte, lift, Std.bind_ok, heq,
          whir.query.Stratum.push_group, hpg]
      have hl1 : out1.val.length = out.val.length + 2 ^ m := by
        have := congrArg List.length e1; simp [hz0, hg1] at this; omega
      obtain ⟨out', hloop, e'⟩ := ih (Std.Usize.wrapping_sub g 1#usize) out1 hg1 (by omega)
        (by rw [hl1, hg1]; rw [h1] at hmod; omega)
      refine ⟨out', ?_, ?_⟩
      · unfold whir.query.Stratum.batch_loop
        rw [loop_cont hbody]
        unfold whir.query.Stratum.batch_loop at hloop
        exact hloop
      · rw [e', e1, hsplit, hg1, if_pos ht, hz0, hmin]
        simp [groupList, List.range_eq_range']
    · have h0 : count.val / 2 ^ m % 2 = 0 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at ht; simp at ht; omega
      have heq : ¬ (Std.Usize.wrapping_shr count (Std.Usize.wrapping_sub g 1#usize) &&& 1#usize) = 1#usize := by
        intro he; have := congrArg UScalar.val he; rw [hbit, h0] at this; simp at this
      have hbody : whir.query.Stratum.batch_loop.body count depth out g =
          .ok (.cont (out, Std.Usize.wrapping_sub g 1#usize)) := by
        simp only [whir.query.Stratum.batch_loop.body, hgp, ↓reduceIte, lift, Std.bind_ok, heq]
      obtain ⟨out', hloop, e'⟩ := ih (Std.Usize.wrapping_sub g 1#usize) out hg1 (by omega)
        (by rw [hg1]; rw [h0] at hmod; omega)
      refine ⟨out', ?_, ?_⟩
      · unfold whir.query.Stratum.batch_loop
        rw [loop_cont hbody]
        unfold whir.query.Stratum.batch_loop at hloop
        exact hloop
      · rw [e', hsplit, hg1, if_neg ht]; simp

theorem strataList_trim (count depth : Nat) (h : count < 2 ^ 64) :
    strataList count depth (List.range 64).reverse = strataList count depth (List.range (count.log2 + 1)).reverse := by
  have hL : count.log2 + 1 ≤ 64 := by
    by_cases h0 : count = 0
    · subst h0; simp
    · have := (Nat.log2_lt h0).mpr h; omega
  have hlt : count < 2 ^ (count.log2 + 1) := by
    by_cases h0 : count = 0
    · subst h0; simp
    · exact (Nat.log2_lt h0).mp (by omega)
  rw [show 64 = (count.log2 + 1) + (64 - (count.log2 + 1)) by omega, List.range_add, List.reverse_append]
  simp only [strataList, List.flatMap_append]
  rw [List.flatMap_eq_nil_iff.mpr, List.nil_append]
  intro g hg
  simp only [List.mem_reverse, List.mem_map, List.mem_range] at hg
  obtain ⟨k, _, rfl⟩ := hg
  have : count.testBit (count.log2 + 1 + k) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp [this]

theorem strata_eq (hw : System.Platform.numBits = 64) (count depth : Usize) (hdep : depth.val < 64) :
    ∃ out, whir.query.Stratum.batch count depth = .ok out ∧
      out.val.map pr = (Concrete.strata count.val depth.val).toList := by
  have hb := Replay.bits_val hw
  have hc : count.val < 2 ^ 64 := by have := count.hBounds; simpa [hw] using this
  obtain ⟨out, hloop, e⟩ := strata_loop_eq hw count depth hdep 64 _ (alloc.vec.Vec.with_capacity _ count) hb
    (by rw [hb]) (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, hb]; have := Usize.max_def; scalar_tac)
  refine ⟨out, ?_, ?_⟩
  · simp only [whir.query.Stratum.batch, lift, Std.bind_ok]; exact hloop
  · rw [e, strata_model, hb, strataList_trim _ _ hc]; simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]

theorem strataList_mem (count depth : Nat) (gs : List Nat) (p : Nat × Nat) (hp : p ∈ strataList count depth gs) :
    p.1 ≤ depth ∧ p.2 < 2 ^ p.1 := by
  simp only [strataList, List.mem_flatMap] at hp
  obtain ⟨g, _, hg⟩ := hp
  split at hg
  · simp only [groupList, List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    exact ⟨Nat.min_le_right _ _, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  · simp at hg

/-! ## Stratum replacement -/

/-- A raw position with its top `bits` bits replaced by `index`. -/
def place (d raw : Nat) (p : Nat × Nat) : Nat := raw % 2 ^ (d - p.1) + p.2 * 2 ^ (d - p.1)

theorem place_loop_eq (hw : System.Platform.numBits = 64) (d : Usize) (hd : d.val < 64)
    (strata : alloc.vec.Vec whir.query.Stratum) (raws : List Nat) (hlen : strata.val.length = raws.length)
    (hs : ∀ p ∈ strata.val.map pr, p.1 ≤ d.val ∧ p.2 < 2 ^ p.1) :
    ∀ (m : Nat) (i : Usize) (out : alloc.vec.Vec Usize), raws.length - i.val = m → i.val ≤ raws.length →
      out.val.map (·.val) = (List.range raws.length).map (fun k =>
        if k < i.val then place d.val raws[k]! (strata.val.map pr)[k]! else raws[k]!) →
      ∃ out', whir.query.sample_queries_loop1 d out strata i = .ok out' ∧
        out'.val.map (·.val) = (List.range raws.length).map fun k => place d.val raws[k]! (strata.val.map pr)[k]! := by
  have hU : UScalarTy.Usize.numBits = 64 := by simp [hw]
  intro m
  induction m with
  | zero =>
    intro i out hm hi hout
    have hol : out.val.length = raws.length := by simpa using congrArg List.length hout
    refine ⟨out, ?_, ?_⟩
    · unfold whir.query.sample_queries_loop1
      apply loop_done
      have : ¬ (i.val < out.val.length) := by omega
      simp [whir.query.sample_queries_loop1.body, lift, this]
    · rw [hout]; apply List.map_congr_left; intro k hk; simp at hk; simp [show k < i.val by omega]
  | succ m ih =>
    intro i out hm hi hout
    have hol : out.val.length = raws.length := by simpa using congrArg List.length hout
    have hil : i.val < raws.length := by omega
    have hsucc := succ_val i raws.length hil (by have := out.property; omega)
    have hmin : i.val < (core.cmp.impls.OrdUsize.min (alloc.vec.Vec.len out) (alloc.vec.Vec.len strata)).val := by
      simp [core.cmp.impls.OrdUsize.min_val, hol, hlen]; omega
    set st := strata.val[i.val]'(by omega) with hst
    set r := out.val[i.val]'(by omega) with hr
    have hrv : r.val = raws[i.val]! := by
      have := congrArg (fun l => l[i.val]!) hout
      rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by simp; omega)] at this
      simp [show ¬ (i.val < i.val) from lt_irrefl _] at this
      rw [hr, this, getElem!_pos raws i.val hil]; simp [hil]
    have hpr : pr st = (strata.val.map pr)[i.val]! := by
      rw [getElem!_pos _ _ (by simp; omega)]; simp [hst]
    obtain ⟨hbd, hix⟩ := hs (pr st) (by rw [hpr, getElem!_pos _ _ (by simp; omega)]; exact List.getElem_mem _)
    simp only [pr] at hbd hix
    have hlow : (Std.Usize.wrapping_sub d st.bits).val = d.val - st.bits.val := Fold.sub_val _ _ hbd
    have hm1 : (Std.Usize.wrapping_sub (Std.Usize.wrapping_shl 1#usize (Std.Usize.wrapping_sub d st.bits)) 1#usize).val =
        2 ^ (d.val - st.bits.val) - 1 := by
      rw [Fold.sub_val _ _ (by rw [shl_one_val hw _ (by omega), hlow]; exact Nat.one_le_two_pow),
        shl_one_val hw _ (by omega), hlow]; simp
    have hix2 : st.index.val * 2 ^ (d.val - st.bits.val) < 2 ^ d.val := by
      calc st.index.val * 2 ^ (d.val - st.bits.val) < 2 ^ st.bits.val * 2 ^ (d.val - st.bits.val) :=
            Nat.mul_lt_mul_of_pos_right hix (Nat.two_pow_pos _)
        _ = 2 ^ d.val := by rw [← Nat.pow_add]; congr 1; omega
    have hidxsh : (Std.Usize.wrapping_shl st.index (Std.Usize.wrapping_sub d st.bits)).val =
        st.index.val * 2 ^ (d.val - st.bits.val) := by
      rw [show Std.Usize.wrapping_shl st.index (Std.Usize.wrapping_sub d st.bits) =
        UScalar.wrapping_shl_rhs st.index (Std.Usize.wrapping_sub d st.bits) from rfl,
        shl_val _ _ (by rw [hlow, hU]; omega), hlow, hU]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le hix2 (Nat.pow_le_pow_right (by norm_num) (by omega)))
    obtain ⟨x, hx⟩ : ∃ x, ((r &&& Std.Usize.wrapping_sub (Std.Usize.wrapping_shl 1#usize
        (Std.Usize.wrapping_sub d st.bits)) 1#usize) ||| Std.Usize.wrapping_shl st.index
        (Std.Usize.wrapping_sub d st.bits)) = x := ⟨_, rfl⟩
    have ex : x.val = place d.val raws[i.val]! (pr st) := by
      rw [← hx, UScalar.val_or, UScalar.val_and, hm1, Nat.and_two_pow_sub_one_eq_mod, hidxsh, place, ← hrv]
      simp only [pr]
      rw [Nat.lor_comm, Nat.mul_comm st.index.val, ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)),
        Nat.add_comm]
    have hbody : whir.query.sample_queries_loop1.body d strata out i =
        .ok (.cont (alloc.vec.Vec.set out i x, Std.Usize.wrapping_add i 1#usize)) := by
      have hlt : i < core.cmp.impls.OrdUsize.min (alloc.vec.Vec.len out) (alloc.vec.Vec.len strata) := by
        simpa [UScalar.lt_equiv] using hmin
      simp only [whir.query.sample_queries_loop1.body, lift, Std.bind_ok, hlt, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize,
        vec_index_usize strata i (by omega), vec_index_usize out i (by omega), ← hst, ← hr, hx]
      simp
    obtain ⟨out', hloop, e'⟩ := ih (Std.Usize.wrapping_add i 1#usize) (alloc.vec.Vec.set out i x) (by omega)
      (by omega) (by
        rw [hsucc, alloc.vec.Vec.set_val_eq, List.map_set, hout, ex, hpr]
        apply List.ext_getElem (by simp)
        intro k h1 h2
        simp only [List.getElem_set, List.getElem_map, List.getElem_range]
        by_cases hk : k = i.val
        · subst hk; simp
        · rw [if_neg (Ne.symm hk)]
          by_cases hk2 : k < i.val
          · simp [hk2, show k < i.val + 1 by omega]
          · simp [hk2, show ¬ (k < i.val + 1) by omega])
    refine ⟨out', ?_, e'⟩
    unfold whir.query.sample_queries_loop1
    rw [loop_cont hbody]
    unfold whir.query.sample_queries_loop1 at hloop
    exact hloop

/-! ## The composed sampler -/

/-- The generated `sample_queries`, reading the squeezes `sq` from its challenger, returns
exactly the model's `deriveQueries` of those squeezes read as extension elements, for a depth
`0 < depth < 64`. -/
theorem sample_queries_eq (hw : System.Platform.numBits = 64) {T0 : Type}
    (Ch : fiat_shamir.Challenger T0) (tape : T0 → List primitives.field.gf2_64x3.F192 → Prop)
    (ht : SqueezeTape Ch tape) (ch : T0) (depth count : Usize) (hd0 : 0 < depth.val) (hd : depth.val < 64)
    (sq : List primitives.field.gf2_64x3.F192)
    (hsq : sq.length = (count.val + 192 / depth.val - 1) / (192 / depth.val))
    (rest : List primitives.field.gf2_64x3.F192) (hch : tape ch (sq ++ rest)) :
    ∃ out ch', whir.query.sample_queries Ch ch depth count = .ok (out, ch') ∧ tape ch' rest ∧
      deriveQueries depth.val count.val (sq.map toE).toArray = some (out.val.map (·.val)).toArray := by
  set d := depth.val with hd_def
  have edU : depth.val = d := hd_def.symm
  obtain ⟨per, hdiv, eper⟩ := UScalar.div_spec 192#usize (y := depth) (by omega)
  have hper : per.val = 192 / d := by rw [eper, edU]; simp
  have hp0 : 0 < 192 / d := Nat.div_pos (by omega) hd0
  obtain ⟨ch', out1, hl0, hch', e1⟩ := sample_loop_eq hw Ch tape ht count depth per (by omega) (by omega)
    (by rw [hper, edU]) sq (by rw [hper]; exact hsq) rest sq.length 0 ch
    (alloc.vec.Vec.with_capacity Usize count) (by simp) (by simp) (by simpa using hch)
    (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]) (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
  obtain ⟨strataV, hstr, estr⟩ := strata_eq hw count depth (by omega)
  have hcnt : count.val < 2 ^ 64 := by have := count.hBounds; simpa [hw] using this
  have hslen : (Concrete.strata count.val d).toList.length = count.val := by
    rw [strata_model, ← strataList_trim _ _ hcnt, strataList_length]; exact Nat.mod_eq_of_lt hcnt
  set raws := (List.range count.val).map (rawAt (sq.map sqNat) depth.val per.val) with hraws
  have hlenS : strataV.val.length = raws.length := by
    have := congrArg List.length estr; simp only [List.length_map] at this; rw [this, edU, hslen]; simp [hraws]
  obtain ⟨out', hl1, e'⟩ := place_loop_eq hw depth (by omega) strataV raws hlenS (by
      intro p hp
      rw [estr, strata_model] at hp
      exact strataList_mem _ _ _ p hp) _ 0#usize out1 rfl (by simp) (by
      rw [e1]
      apply List.ext_getElem (by simp [hraws])
      intro k h1 h2
      have hk : k < count.val := by simpa [hraws] using h1
      simp [hraws, hk])
  refine ⟨out', ch', ?_, hch', ?_⟩
  · simp [whir.query.sample_queries, lift, hdiv, hl0, hstr, hl1]
  · rw [e']
    unfold deriveQueries
    have hd' : ¬ (d == 0 || decide (d > 64)) = true := by simp; omega
    simp only [hd', Bool.false_eq_true, ↓reduceIte, List.size_toArray, List.length_map, hsq, bne_self_eq_false]
    simp only [Concrete.tab, Option.pure_def, Option.some.injEq]
    rw [List.map_toArray, show raws.length = count.val by simp [hraws]]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi : i < count.val := List.mem_range.mp hi
    have hq : i / (192 / d) < sq.length := by
      rw [hsq, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hp0, Nat.add_mul]
      have := Nat.div_mul_le_self i (192 / d); omega
    have hs : (List.map pr strataV.val)[i]! = (Concrete.strata count.val d)[i]! := by
      rw [estr, edU, getElem!_pos _ _ (by rw [hslen]; exact hi), getElem!_pos _ _ (by
        rw [← Array.length_toList, hslen]; exact hi)]
      simp
    have hr : raws[i]! = (sqNat sq[i / (192 / d)] / 2 ^ (i % (192 / d) * d)) % 2 ^ d := by
      rw [getElem!_pos _ _ (by simp [hraws, hi])]
      simp [hraws, rawAt, hper, edU, hq]
    have hl : ((sq.map toE).toArray[i / (192 / d)]!).toNat = sqNat sq[i / (192 / d)] := by
      rw [getElem!_pos _ _ (by simp [hq])]; simp [toE_toNat, sqNat]
    rw [hs, hr, hl, place, edU]

end WhirAeneas.Sampling
