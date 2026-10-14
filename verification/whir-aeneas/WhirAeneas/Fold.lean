import WhirAeneas.Generated.Replay.Funs
import Whir.SuccinctRingWeight
import Whir.InducedTerminalRefinement
import Whir.AccumulatedTerminalAlgebra

/-! The actual generated round quadratic evaluation and folding, the ring map's
linearized closure, an out-of-domain claim's terminal term, and one query's
basis product compute the proof model's operations. The single field premise is
`ArithModel`: every arithmetic dictionary operation the replay calls succeeds,
leaves the verifier state unchanged, and returns the model field operation on the
interpreted operands. Index and length premises are stated where the source would
otherwise panic or wrap. -/
namespace WhirAeneas.Fold
open Aeneas Aeneas.Std ReplaySource Whir Whir.Concrete

/-- The arithmetic dictionary computes the model's field operations on interpreted
elements, from any state, and leaves the state unchanged. `const` interprets the
source's `F192` constants. The table, power and multilinear operations are the
dictionary's provided methods; each is stated where the source does not panic. -/
structure ArithModel {S E : Type} (inst : fiat_shamir.arith.Arith S E) (encode : E → Concrete.E)
    (const : primitives.field.gf2_64x3.F192 → Concrete.E) : Prop where
  mul_add : ∀ s a b c, ∃ y, inst.mul_add s a b c = .ok (y, s) ∧
    encode y = encode a * encode b + encode c
  add : ∀ s a b, ∃ y, inst.add s a b = .ok (y, s) ∧ encode y = encode a + encode b
  mul : ∀ s a b, ∃ y, inst.mul s a b = .ok (y, s) ∧ encode y = encode a * encode b
  zero : ∀ s, ∃ y, inst.zero s = .ok (y, s) ∧ encode y = 0
  one : ∀ s, ∃ y, inst.one s = .ok (y, s) ∧ encode y = 1
  mul_const : ∀ s a c, ∃ y, inst.mul_const s a c = .ok (y, s) ∧ encode y = encode a * const c
  add_const : ∀ s a c, ∃ y, inst.add_const s a c = .ok (y, s) ∧ encode y = encode a + const c
  times_one_plus : ∀ s a b, ∃ y, inst.times_one_plus s a b = .ok (y, s) ∧
    encode y = encode a * (1 + encode b)
  eq_table_prefix : ∀ s (point : Slice E) (len : Usize), point.val.length < 64 →
    len.val ≤ 2 ^ point.val.length → ∃ t, inst.eq_table_prefix s point len = .ok (t, s) ∧
      t.val.map encode = ((Concrete.eqTable (point.val.map encode).toArray).toList.take len.val)
  powers : ∀ s x (n : Usize), ∃ p, inst.powers s x n = .ok (p, s) ∧
    p.val.map encode = (Concrete.powers (encode x) n.val).toList
  mle : ∀ s (values point : Slice E), point.val.length < 64 →
    values.val.length = 2 ^ point.val.length → ∃ y, inst.mle s values point = .ok (y, s) ∧
      encode y = Concrete.mle (values.val.map encode).toArray (point.val.map encode).toArray

theorem loop_cont {α β : Type} {body : α → Result (ControlFlow α β)} {x x' : α}
    (h : body x = .ok (.cont x')) : loop body x = loop body x' := by
  rw [loop]; simp [h]

theorem loop_done {α β : Type} {body : α → Result (ControlFlow α β)} {x : α} {y : β}
    (h : body x = .ok (.done y)) : loop body x = .ok y := by
  rw [loop]; simp [h]

theorem usize_lt_size (i : Usize) : i.val < UScalar.size .Usize := by
  have := Usize.max_def
  simp only [UScalar.size] at *
  scalar_tac

theorem pred_val (i : Usize) (h : 0 < i.val) :
    (Std.Usize.wrapping_sub i 1#usize).val = i.val - 1 := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have h1 : (1#usize).val = 1 := by simp
  have hs := usize_lt_size i
  rw [h1, show i.val + (UScalar.size .Usize - 1) = (i.val - 1) + UScalar.size .Usize by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem succ_val (i : Usize) (n : Nat) (hi : i.val < n) (hn : n ≤ Usize.max) :
    (Std.Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have : i.val + 1 < UScalar.size .Usize := by
    have := Usize.max_def; simp only [UScalar.size] at *; scalar_tac
  have h1 : (1#usize).val = 1 := by simp
  rw [h1]
  exact Nat.mod_eq_of_lt this

theorem slice_index {α : Type} (s : Slice α) (i : Usize) (hi : i.val < s.val.length) :
    Slice.index_usize s i = .ok s.val[i.val] := by
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, hi]

theorem vec_index {α : Type} (v : alloc.vec.Vec α) (i : Usize) (hi : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = .ok v.val[i.val] := by
  rw [alloc.vec.Vec.index_slice_index]
  simp [alloc.vec.Vec.index_usize, hi]

/-! ## Round quadratic -/

section Quad
variable {E V R K Q : Type} (copy : core.marker.Copy E) (inst : verifier.OpeningVerifier V R K Q E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)

/-- `RoundQuad::eval` is the model's message evaluation `Message.eval`, with the source's
stored linear coefficient interpreted as `claim + u2`. -/
theorem quad_eval (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (q : whir.sumcheck.RoundQuad E) (v : V) (x : E) (claim : Concrete.E)
    (hb : encode q.b = claim + encode q.a) :
    ∃ y, whir.sumcheck.RoundQuad.eval copy inst.fiat_shamirarithVerifierInst.ArithInst q v x = .ok (y, v) ∧
      encode y = Protocol.Message.eval ⟨encode q.c, encode q.a⟩ claim (encode x) := by
  obtain ⟨u, hu, eu⟩ := h.mul_add v q.a x q.b
  obtain ⟨y, hy, ey⟩ := h.mul_add v u x q.c
  refine ⟨y, ?_, ?_⟩
  · simp [whir.sumcheck.RoundQuad.eval, hu, hy]
  · rw [ey, eu, hb]
    simp only [Protocol.Message.eval]
    ring

/-- `RoundQuad::fold` is the model's `Message.glue` on the transmitted coefficients, and keeps
the linear coefficient equal to the batched claim `claim + s * value` plus the new `u2`. -/
theorem quad_fold (h : ArithModel inst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (q other : whir.sumcheck.RoundQuad E) (v : V) (s : E) (claim value : Concrete.E)
    (hb : encode q.b = claim + encode q.a) (hob : encode other.b = value + encode other.a) :
    ∃ r, whir.sumcheck.RoundQuad.fold copy inst.fiat_shamirarithVerifierInst.ArithInst q v other s = .ok (r, v) ∧
      (⟨encode r.c, encode r.a⟩ : Protocol.Message Concrete.E) =
        Protocol.Message.glue ⟨encode q.c, encode q.a⟩ ⟨encode other.c, encode other.a⟩ (encode s) ∧
      encode r.b = claim + encode s * value + encode r.a := by
  obtain ⟨c, hc, ec⟩ := h.mul_add v s other.c q.c
  obtain ⟨b, hb', eb⟩ := h.mul_add v s other.b q.b
  obtain ⟨a, ha, ea⟩ := h.mul_add v s other.a q.a
  refine ⟨{ c := c, b := b, a := a }, ?_, ?_, ?_⟩
  · simp [whir.sumcheck.RoundQuad.fold, hc, hb', ha]
  · simp only [Protocol.Message.glue, ec, ea]
    congr 1 <;> ring
  · simp only [eb, ea, hb, hob]
    ring

end Quad

/-! ## Linearized closure -/

section Close
variable {E S : Type} (copy : core.marker.Copy E) (inst : fiat_shamir.arith.Arith S E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)

theorem close_loop_eq (h : ArithModel inst encode const) (terms : Slice E) :
    ∀ (n : Nat) (i : Usize) (acc : E) (a : S), i.val = n → i.val < terms.val.length →
      encode acc = SuccinctRingWeight.close ((terms.val.drop i.val).map encode) →
      ∃ y, ring_switch.RingMap.close_loop inst a terms i acc = .ok (y, a) ∧
        encode y = SuccinctRingWeight.close (terms.val.map encode) := by
  intro n
  induction n with
  | zero =>
    intro i acc a hn _ hacc
    refine ⟨acc, ?_, ?_⟩
    · unfold ring_switch.RingMap.close_loop
      apply loop_done
      have : ¬ (0#usize < i) := by scalar_tac
      simp [ring_switch.RingMap.close_loop.body, this]
    · simpa [hn] using hacc
  | succ k ih =>
    intro i acc a hn hlt hacc
    have hpos : 0 < i.val := by omega
    have hpred := pred_val i hpos
    have hk : (Std.Usize.wrapping_sub i 1#usize).val < terms.val.length := by omega
    obtain ⟨acc1, hm, em⟩ := h.mul_add a acc acc terms.val[(Std.Usize.wrapping_sub i 1#usize).val]
    have hbody : ring_switch.RingMap.close_loop.body inst terms a i acc =
        .ok (.cont (a, Std.Usize.wrapping_sub i 1#usize, acc1)) := by
      have : 0#usize < i := by scalar_tac
      simp only [ring_switch.RingMap.close_loop.body, gt_iff_lt, this, ↓reduceIte, lift, Std.bind_ok,
        bind_tc_ok, slice_index terms _ hk, hm]
      rfl
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_sub i 1#usize) acc1 a (by omega) hk (by
      rw [em, hacc]
      have hd : terms.val.drop (Std.Usize.wrapping_sub i 1#usize).val =
          terms.val[(Std.Usize.wrapping_sub i 1#usize).val] :: terms.val.drop i.val := by
        rw [List.drop_eq_getElem_cons hk, show (Std.Usize.wrapping_sub i 1#usize).val + 1 = i.val by omega]
      rw [hd]
      simp only [List.map_cons, SuccinctRingWeight.close, RingPCSGame.squareIter]
      ring)
    refine ⟨y, ?_, ey⟩
    unfold ring_switch.RingMap.close_loop
    rw [loop_cont hbody]
    unfold ring_switch.RingMap.close_loop at hy
    exact hy

/-- On nonempty terms, `RingMap::close` is the model's linearized Horner closure
`SuccinctRingWeight.close`, that is `sum_k terms[k]^(2^k)`. -/
theorem close_eq (h : ArithModel inst encode const) (a : S) (terms : Slice E)
    (hne : terms.val ≠ []) :
    ∃ y, ring_switch.RingMap.close copy inst a terms = .ok (y, a) ∧
      encode y = SuccinctRingWeight.close (terms.val.map encode) := by
  have hlen : 0 < terms.val.length := List.length_pos_of_ne_nil hne
  have hspec := Usize.checked_sub_bv_spec (Slice.len terms) 1#usize
  cases hcs : Usize.checked_sub (Slice.len terms) 1#usize with
  | none =>
    simp only [hcs] at hspec
    have h1 : (1#usize).val = 1 := by simp
    have h2 : (Slice.len terms).val = terms.val.length := by simp
    omega
  | some z =>
    simp only [hcs] at hspec
    obtain ⟨_, hz, _⟩ := hspec
    have hz' : z.val = terms.val.length - 1 := by simpa [Slice.len_val] using hz
    have hzl : z.val < terms.val.length := by omega
    obtain ⟨y, hy, ey⟩ := close_loop_eq inst encode const h terms z.val z terms.val[z.val] a rfl hzl (by
      have hd : terms.val.drop z.val = [terms.val[z.val]] := by
        rw [List.drop_eq_getElem_cons hzl, List.drop_eq_nil_of_le (by omega)]
      simp [hd, SuccinctRingWeight.close, RingPCSGame.squareIter])
    refine ⟨y, ?_, ey⟩
    simp [ring_switch.RingMap.close, hcs, lift, core.option.Option.expect, Result.ofOption,
      slice_index terms z hzl, hy]

end Close

/-! ## Out-of-domain terminal term -/

section Ood
variable {E S : Type} (copy : core.marker.Copy E) (inst : fiat_shamir.arith.Arith S E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)

theorem sub_val (j k : Usize) (hle : k.val ≤ j.val) :
    (Std.Usize.wrapping_sub j k).val = j.val - k.val := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hs := usize_lt_size j
  have hs2 := usize_lt_size k
  rw [show j.val + (UScalar.size .Usize - k.val) = (j.val - k.val) + UScalar.size .Usize by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem term_loop_eq (h : ArithModel inst encode const) (z : alloc.vec.Vec E) (head tail : Slice E)
    (n : Usize) (hn : n.val = min z.val.length (head.val.length + tail.val.length)) :
    ∀ (m : Nat) (j : Usize) (scalar : E) (a : S), n.val - j.val = m → j.val ≤ n.val →
      ∃ y, whir.verify.OodCtx.term_loop inst z a head tail n scalar j = .ok (y, a) ∧
        encode y = encode scalar * ((((z.val.map encode).drop j.val).zip
          (((head.val ++ tail.val).map encode).drop j.val)).map fun (a, b) => 1 + a + b).prod := by
  intro m
  induction m with
  | zero =>
    intro j scalar a hm hj
    refine ⟨scalar, ?_, ?_⟩
    · unfold whir.verify.OodCtx.term_loop
      apply loop_done
      have : ¬ (j.val < n.val) := by omega
      simp only [whir.verify.OodCtx.term_loop.body, UScalar.lt_equiv, this, ↓reduceIte]
    · have hnil : ((z.val.map encode).drop j.val).zip (((head.val ++ tail.val).map encode).drop j.val) = [] := by
        simp only [List.zip_eq_nil_iff, List.drop_eq_nil_iff, List.length_map, List.length_append]
        omega
      rw [hnil]
      simp
  | succ k ih =>
    intro j scalar a hm hj
    have hjn : j.val < n.val := by omega
    have hjz : j.val < z.val.length := by omega
    have hjx : j.val < (head.val ++ tail.val).length := by simp; omega
    have hsucc := succ_val j n.val hjn (by scalar_tac)
    -- The source picks `x_j` from `head`, then from `tail`; either way it is `(head ++ tail)[j]`.
    have hpick : ∃ x, (head.val ++ tail.val)[j.val] = x ∧
        ∀ (scalar1 sum : E),
          inst.add a z.val[j.val] x = .ok (sum, a) →
          inst.times_one_plus a scalar sum = .ok (scalar1, a) →
          whir.verify.OodCtx.term_loop.body inst z head tail n a scalar j =
            .ok (.cont (a, scalar1, Std.Usize.wrapping_add j 1#usize)) := by
      by_cases hh : j.val < head.val.length
      · refine ⟨head.val[j.val], List.getElem_append_left hh, ?_⟩
        intro scalar1 sum hadd htop
        simp only [whir.verify.OodCtx.term_loop.body, UScalar.lt_equiv, Slice.len_val, Slice.length,
          hjn, hh, ↓reduceIte, slice_index head j hh, vec_index z j hjz, Std.bind_ok, bind_tc_ok,
          lift, hadd, htop]
        simp [htop]
      · have hle : (Slice.len head).val ≤ j.val := by simp; omega
        have hsub := sub_val j (Slice.len head) hle
        have hi2 : (Std.Usize.wrapping_sub j (Slice.len head)).val < tail.val.length := by
          rw [hsub]; simp at hjx ⊢; omega
        refine ⟨tail.val[(Std.Usize.wrapping_sub j (Slice.len head)).val], ?_, ?_⟩
        · rw [List.getElem_append_right (by omega)]
          congr 1
          rw [hsub]; simp
        · intro scalar1 sum hadd htop
          simp only [whir.verify.OodCtx.term_loop.body, UScalar.lt_equiv, Slice.len_val, Slice.length,
            hjn, hh, ↓reduceIte, slice_index tail _ hi2, vec_index z j hjz, Std.bind_ok, bind_tc_ok,
            lift, hadd, htop]
          simp [htop]
    obtain ⟨x, hx, hbody⟩ := hpick
    obtain ⟨sum, hadd, esum⟩ := h.add a z.val[j.val] x
    obtain ⟨scalar1, htop, etop⟩ := h.times_one_plus a scalar sum
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add j 1#usize) scalar1 a (by omega) (by omega)
    refine ⟨y, ?_, ?_⟩
    · unfold whir.verify.OodCtx.term_loop
      rw [loop_cont (hbody scalar1 sum hadd htop)]
      unfold whir.verify.OodCtx.term_loop at hy
      exact hy
    · rw [ey, etop, esum, hsucc]
      have hz : (z.val.map encode).drop j.val = encode z.val[j.val] :: (z.val.map encode).drop (j.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega), List.getElem_map]
      have hxs : ((head.val ++ tail.val).map encode).drop j.val =
          encode x :: ((head.val ++ tail.val).map encode).drop (j.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega), List.getElem_map, hx]
      rw [hz, hxs]
      simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]
      ring

/-- An OOD claim's terminal term is the model's `beta * equalityProduct z (head ++ tail)`,
whose `zip` keeps the source's truncation to the shorter side. -/
theorem term_eq (h : ArithModel inst encode const) (ctx : whir.verify.OodCtx E) (a : S)
    (head tail : Slice E) (hfit : head.val.length + tail.val.length ≤ Usize.max) :
    ∃ y, whir.verify.OodCtx.term copy inst ctx a head tail = .ok (y, a) ∧
      encode y = encode ctx.beta * AccumulatedTerminalAlgebra.equalityProduct (ctx.z.val.map encode)
        ((head.val ++ tail.val).map encode) := by
  have hadd : (Std.Usize.wrapping_add (Slice.len head) (Slice.len tail)).val =
      head.val.length + tail.val.length := by
    rw [Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    have := Usize.max_def
    simp only [UScalar.size, Slice.len_val] at *
    scalar_tac
  have hn : (core.cmp.impls.OrdUsize.min (alloc.vec.Vec.len ctx.z)
      (Std.Usize.wrapping_add (Slice.len head) (Slice.len tail))).val =
      min ctx.z.val.length (head.val.length + tail.val.length) := by
    simp only [core.cmp.impls.OrdUsize.min_val, hadd, alloc.vec.Vec.len_val]
  obtain ⟨y, hy, ey⟩ := term_loop_eq inst encode const h ctx.z head tail _ hn _ 0#usize ctx.beta a rfl
    (by simp)
  refine ⟨y, ?_, ?_⟩
  · simp only [whir.verify.OodCtx.term, lift, Std.bind_ok, bind_tc_ok]
    exact hy
  · rw [ey]
    simp [AccumulatedTerminalAlgebra.equalityProduct]

end Ood

/-! ## One query's basis product -/

section Basis
variable {E S : Type} (copy : core.marker.Copy E) (inst : fiat_shamir.arith.Arith S E)
  (encode : E → Concrete.E) (const : primitives.field.gf2_64x3.F192 → Concrete.E)

/-- The model's affine factors, interpreted from the source's pairs. -/
def factors (lin : Slice (E × E)) : Array (Concrete.E × Concrete.E) :=
  (lin.val.map fun p => (encode p.1, encode p.2)).toArray

theorem basis_loop_eq (h : ArithModel inst encode const) (lin : Slice (E × E))
    (basis : ntt.basis.NovelBasis) (roots : Array Concrete.K) (s0 : E)
    (hsks : lin.val.length ≤ basis.normalizers.val.length + 1)
    (hroots : ∀ i (hi : i < basis.normalizers.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from basis.normalizers.val[i] = .ok f →
        const f = Concrete.E.ofK roots[i]!) :
    ∀ (m : Nat) (k : Usize) (st product : E) (a : S), lin.val.length - k.val = m →
      k.val ≤ lin.val.length →
      (encode st, encode product) = (List.range k.val).foldl
        (InducedTerminalRefinement.nativeStep roots (factors encode lin)) (encode s0, 1) →
      ∃ y, whir.verify.basis_product_loop inst a lin basis st product k = .ok (y, a) ∧
        encode y = ((List.range lin.val.length).foldl
          (InducedTerminalRefinement.nativeStep roots (factors encode lin)) (encode s0, 1)).2 := by
  intro m
  induction m with
  | zero =>
    intro k st product a hm hk hst
    have hkl : k.val = lin.val.length := by omega
    refine ⟨product, ?_, ?_⟩
    · unfold whir.verify.basis_product_loop
      apply loop_done
      have : ¬ (k.val < lin.val.length) := by omega
      simp only [whir.verify.basis_product_loop.body, UScalar.lt_equiv, Slice.len_val, Slice.length,
        this, ↓reduceIte]
    · rw [← hkl, ← hst]
  | succ n ih =>
    intro k st product a hm hk hst
    have hkl : k.val < lin.val.length := by omega
    have hsucc := succ_val k lin.val.length hkl (by scalar_tac)
    obtain ⟨p1, p2, hp12⟩ : ∃ p1 p2, lin.val[k.val] = (p1, p2) := ⟨_, _, rfl⟩
    have hix : Slice.index_usize lin k = .ok (p1, p2) := by
      rw [slice_index lin k hkl]; exact congrArg Result.ok hp12
    have hL : (factors encode lin)[k.val]! = (encode p1, encode p2) := by
      simp [factors, getElem!_pos, hkl, hp12]
    have hkl' : (k.val < (Slice.len lin).val) := by simpa using hkl
    -- The recurrence's new `s`, then the factor and the product.
    have hstep : ∃ s1 product1,
        whir.verify.basis_product_loop.body inst lin basis a st product k =
          .ok (.cont (a, s1, product1, Std.Usize.wrapping_add k 1#usize)) ∧
        encode s1 = (if k.val = 0 then encode st else
          encode st * encode st + encode st * Concrete.E.ofK roots[k.val - 1]!) ∧
        encode product1 = encode product * (encode p2 * encode s1 + encode p1) := by
      by_cases hk0 : k.val = 0
      · have h0 : ¬ ((0#usize).val < k.val) := by simp; omega
        obtain ⟨f, hf, ef⟩ := h.mul_add a p2 st p1
        obtain ⟨product1, hp, ep⟩ := h.mul a product f
        refine ⟨st, product1, ?_, by simp [hk0], by rw [ep, ef]⟩
        simp only [whir.verify.basis_product_loop.body, UScalar.lt_equiv, gt_iff_lt, hkl', h0,
          ↓reduceIte, hix, Std.bind_ok, bind_tc_ok, hf, hp, lift]
        simp [hf, hp]
      · have h0 : (0#usize).val < k.val := by simp; omega
        have hpred := pred_val k (by omega)
        have hi : (Std.Usize.wrapping_sub k 1#usize).val < basis.normalizers.val.length := by omega
        obtain ⟨u, hu, eu⟩ := h.mul_const a st
          { c0 := basis.normalizers.val[(Std.Usize.wrapping_sub k 1#usize).val], c1 := 0#u64, c2 := 0#u64 }
        obtain ⟨s2, hs2, es2⟩ := h.mul_add a st st u
        obtain ⟨f, hf, ef⟩ := h.mul_add a p2 s2 p1
        obtain ⟨product1, hp, ep⟩ := h.mul a product f
        refine ⟨s2, product1, ?_, ?_, by rw [ep, ef]⟩
        · simp only [whir.verify.basis_product_loop.body, UScalar.lt_equiv, gt_iff_lt, hkl', h0,
            ↓reduceIte, hix, ntt.basis.NovelBasis.next, vec_index basis.normalizers _ hi, alloc.vec.Vec.index_usize, hi,
            Std.bind_ok, bind_tc_ok, lift,
            primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from, hu, hs2, hf, hp]
          simp [hs2, hf, hp]
        · simp only [hk0, ↓reduceIte]
          rw [es2, eu, hroots _ hi _ rfl, hpred]
    obtain ⟨s1, product1, hbody, es1, ep⟩ := hstep
    obtain ⟨y, hy, ey⟩ := ih (Std.Usize.wrapping_add k 1#usize) s1 product1 a (by omega) (by omega) (by
      rw [hsucc, List.range_succ, List.foldl_append, ← hst]
      simp only [List.foldl_cons, List.foldl_nil, InducedTerminalRefinement.nativeStep, hL, es1, ep]
      try rfl)
    refine ⟨y, ?_, ey⟩
    unfold whir.verify.basis_product_loop
    rw [loop_cont hbody]
    unfold whir.verify.basis_product_loop at hy
    exact hy

/-- `basis_product` is the model's per-query fold of `nativeStep`, the inner product of
`nativeBasisAt`, given the source's normalizers interpret as the model's subspace roots. -/
theorem basis_product_eq (h : ArithModel inst encode const) (a : S) (lin : Slice (E × E))
    (basis : ntt.basis.NovelBasis) (roots : Array Concrete.K) (s : E)
    (hsks : lin.val.length ≤ basis.normalizers.val.length + 1)
    (hroots : ∀ i (hi : i < basis.normalizers.val.length) f,
      primitives.field.gf2_64x3.F192.Insts.CoreConvertFromF64.from basis.normalizers.val[i] = .ok f →
        const f = Concrete.E.ofK roots[i]!) :
    ∃ y, whir.verify.basis_product copy inst a lin basis s = .ok (y, a) ∧
      encode y = ((List.range lin.val.length).foldl
        (InducedTerminalRefinement.nativeStep roots (factors encode lin)) (encode s, 1)).2 := by
  obtain ⟨one, hone, eone⟩ := h.one a
  obtain ⟨y, hy, ey⟩ := basis_loop_eq inst encode const h lin basis roots s hsks hroots _ 0#usize s one a
    rfl (by simp) (by simp [eone])
  exact ⟨y, by simp only [whir.verify.basis_product, hone, Std.bind_ok, bind_tc_ok]; exact hy, ey⟩

end Basis

end WhirAeneas.Fold
