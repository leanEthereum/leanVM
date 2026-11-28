module

public import NativeRustcX64.Sym
public import NativeRustc.Bytes
import Native.Xmss.ModelSpec

/-!
# Memory facts for the layer parser and verifier proofs

Addresses of non-wrapping ranges (`toNat_addr`), sub-ranges of mapped, non-wrapping and apart
ranges (`Mapped.sub`, `NoWrap.sub`, `Apart.sub`), what is kept (`SameOutside.trans`,
`Mapped.kept`, `BytesAt.sameOutside`), bytes assembled from pieces (`BytesAt.append`,
`BytesAt.bytesOf`), the bytes of a 64-bit value (`regBytes`, `regBytes_eq_wordBytes`), a stored
load after a block (`Match.get?_load`) and addresses outside an environment's regions
(`Env.outside_of`).
-/

namespace NativeRustcX64

public section

/-! ## Addresses -/

theorem toNat_addr {a : BitVec 64} {i n : Nat} (h : a.toNat + n ≤ 2 ^ 64) (hi : i < n) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i :=
  Sym.toNat_add_ofNat a i (by omega)

theorem addr_add_addr (a : BitVec 64) (i j : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem NoWrap.sub {a : BitVec 64} {n i k : Nat} (h : NoWrap a n) (hk : i + k ≤ n) :
    NoWrap (a + BitVec.ofNat 64 i) k := by
  unfold NoWrap at *
  by_cases hk0 : k = 0
  · subst hk0
    have := (a + BitVec.ofNat 64 i).isLt
    omega
  · rw [toNat_addr h (by omega)]
    omega

theorem Mapped.sub {d : DataMem} {a : BitVec 64} {n i k : Nat} (h : Mapped d a n)
    (hk : i + k ≤ n) : Mapped d (a + BitVec.ofNat 64 i) k := fun j hj => by
  rw [addr_add_addr]
  exact h (i + j) (by omega)

theorem Mapped.kept {d d' : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n)
    (hk : Kept d d') : Mapped d' a n := fun j hj => hk _ (h j hj)

/-- Sub-ranges of apart ranges are apart. -/
theorem Apart.sub {a a' : BitVec 64} {n n' i k i' k' : Nat} (h : Apart a n a' n')
    (hw : NoWrap a n) (hw' : NoWrap a' n') (hk : i + k ≤ n) (hk' : i' + k' ≤ n')
    (h0 : 0 < k) (h0' : 0 < k') :
    Apart (a + BitVec.ofNat 64 i) k (a' + BitVec.ofNat 64 i') k' := by
  unfold Apart NoWrap at *
  rw [toNat_addr hw (by omega), toNat_addr hw' (by omega)]
  omega

theorem Apart.sub_right {a a' : BitVec 64} {n n' i' k' : Nat} (h : Apart a n a' n')
    (hw' : NoWrap a' n') (hk' : i' + k' ≤ n') (h0' : 0 < k') :
    Apart a n (a' + BitVec.ofNat 64 i') k' := by
  unfold Apart NoWrap at *
  rw [toNat_addr hw' (by omega)]
  omega

theorem Apart.sub_left {a a' : BitVec 64} {n n' i k : Nat} (h : Apart a n a' n')
    (hw : NoWrap a n) (hk : i + k ≤ n) (h0 : 0 < k) :
    Apart (a + BitVec.ofNat 64 i) k a' n' := by
  unfold Apart NoWrap at *
  rw [toNat_addr hw (by omega)]
  omega

/-- Two ranges at offsets `o`, `o'` of a non-wrapping range that do not overlap are apart. -/
theorem apart_offsets {f : BitVec 64} {N o s o' s' : Nat} (hf : NoWrap f N)
    (h : o + s ≤ o' ∨ o' + s' ≤ o) (ho : o + s ≤ N) (ho' : o' + s' ≤ N) (hs : 0 < s)
    (hs' : 0 < s') : Apart (f + BitVec.ofNat 64 o) s (f + BitVec.ofNat 64 o') s' := by
  unfold Apart NoWrap at *
  rw [toNat_addr hf (by omega), toNat_addr hf (by omega)]
  omega

/-- An address in a sub-range is in the range. -/
theorem inRange_sub {f p : BitVec 64} {N o s : Nat} (hf : NoWrap f N) (ho : o + s ≤ N)
    (h : InRange (f + BitVec.ofNat 64 o) s p) : InRange f N p := by
  by_cases hs : s = 0
  · subst hs
    unfold InRange at h
    omega
  have hf' : (f + BitVec.ofNat 64 o).toNat + s ≤ 2 ^ 64 := by
    unfold NoWrap at hf
    rw [toNat_addr hf (by omega)]
    omega
  rw [Sym.inRange_iff hf'] at h
  rw [Sym.inRange_iff hf]
  unfold NoWrap at hf
  rw [toNat_addr hf (by omega)] at h
  omega

/-- An address apart from a range is not in it. -/
theorem not_inRange_of_apart {a p : BitVec 64} {n : Nat} (hw : NoWrap a n) (h : Apart a n p 1) :
    ¬InRange a n p := by
  rw [Sym.inRange_iff hw]
  unfold Apart at h
  omega

theorem bytesAt_add_zero {d : DataMem} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d (a + BitVec.ofNat 64 0) bs) : BytesAt d a bs := by
  simpa using h

/-! ## What is kept -/

theorem SameOutside.refl (d : DataMem) (R : BitVec 64 → Prop) : SameOutside d d R :=
  fun _ _ => rfl

theorem SameOutside.trans {d₁ d₂ d₃ : DataMem} {R R' : BitVec 64 → Prop}
    (h₁ : SameOutside d₁ d₂ R) (h₂ : SameOutside d₂ d₃ R') :
    SameOutside d₁ d₃ (fun p => R p ∨ R' p) := fun p hp =>
  (h₂ p fun h => hp (Or.inr h)).trans (h₁ p fun h => hp (Or.inl h))

theorem SameOutside.mono {d d' : DataMem} {R R' : BitVec 64 → Prop} (h : SameOutside d d' R)
    (hR : ∀ p, R p → R' p) : SameOutside d d' R' := fun p hp => h p fun h' => hp (hR p h')

theorem Kept.refl (d : DataMem) : Kept d d := fun _ h => h

theorem Kept.trans {d₁ d₂ d₃ : DataMem} (h₁ : Kept d₁ d₂) (h₂ : Kept d₂ d₃) : Kept d₁ d₃ :=
  fun p hp => h₂ p (h₁ p hp)

/-! ## Bytes -/

theorem BytesAt.sameOutside {d d' : DataMem} {a : BitVec 64} {bs : List UInt8}
    {R : BitVec 64 → Prop} (h : BytesAt d a bs) (hs : SameOutside d d' R)
    (hR : ∀ i < bs.length, ¬R (a + BitVec.ofNat 64 i)) : BytesAt d' a bs := fun i hi => by
  rw [hs _ (hR i hi)]
  exact h i hi

theorem BytesAt.append {d : DataMem} {a : BitVec 64} {xs ys : List UInt8} (h₁ : BytesAt d a xs)
    (h₂ : BytesAt d (a + BitVec.ofNat 64 xs.length) ys) : BytesAt d a (xs ++ ys) := by
  intro i hi
  by_cases hx : i < xs.length
  · rw [List.getElem_append_left hx]
    exact h₁ i hx
  · rw [List.getElem_append_right (by omega)]
    have := h₂ (i - xs.length) (by simp at hi; omega)
    rwa [addr_add_addr, show xs.length + (i - xs.length) = i by omega] at this

theorem BytesAt.mapped {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    Mapped d a bs.length := fun i hi => by rw [h i hi]; rfl

theorem BytesAt.bytesOf {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    NativeRustcX64.bytesOf d a bs.length = bs := by
  apply List.ext_getElem (by simp [NativeRustcX64.bytesOf])
  intro i h1 h2
  simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range]
  rw [h i h2]
  rfl

theorem bytesAt_bytesOf {d : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n) :
    BytesAt d a (bytesOf d a n) := by
  intro i hi
  simp only [bytesOf, List.length_map, List.length_range] at hi
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  have := h i hi
  revert this
  cases d.get? (a + BitVec.ofNat 64 i) <;> simp

theorem getElem_bytesOf {d : DataMem} {a : BitVec 64} {n i : Nat}
    (hi : i < (bytesOf d a n).length) :
    (bytesOf d a n)[i] = (d.get? (a + BitVec.ofNat 64 i)).getD 0 := by
  simp [bytesOf]

theorem length_bytesOf (d : DataMem) (a : BitVec 64) (n : Nat) : (bytesOf d a n).length = n := by
  simp [bytesOf]

/-- The `n` bytes from `a` are those of `bytesOf d₀ b N` from `k`. -/
theorem bytesAt_slice {d d₀ : DataMem} {a b : BitVec 64} {N k n : Nat} (hk : k + n ≤ N)
    (h : ∀ t < n, d.get? (a + BitVec.ofNat 64 t) =
      some ((d₀.get? (b + BitVec.ofNat 64 (k + t))).getD 0)) :
    BytesAt d a (NativeRustc.slice (bytesOf d₀ b N) k n) := by
  intro t ht
  have hl : (NativeRustc.slice (bytesOf d₀ b N) k n).length = n := by
    simp [NativeRustc.slice, bytesOf]; omega
  rw [h t (by omega)]
  simp [NativeRustc.slice, bytesOf]

/-- The little-endian number of bytes is `Nat.ofBytes`'s. -/
theorem leNat_eq_ofBytes (bs : List UInt8) : NativeRustc.leNat bs = Nat.ofBytes bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show b.toNat + 256 * NativeRustc.leNat bs = Nat.ofBytes bs * 256 + b.toNat
    rw [ih]
    omega

/-- A 64-bit value's 8 bytes, little-endian, as a block stores them. -/
@[expose] def regBytes (x : BitVec 64) : List UInt8 := (List.range 8).map (Sym.byteOf x)

theorem length_regBytes (x : BitVec 64) : (regBytes x).length = 8 := by simp [regBytes]

theorem regBytes_eq_wordBytes (x : BitVec 64) :
    regBytes x = LeanVM.Protocol.KeccakHash.wordBytes (UInt64.ofBitVec x) := by
  rw [Native.XmssVerifier.wordBytes_eq_bytes]
  apply List.ext_getElem (by simp [regBytes, Native.XmssVerifier.bytes])
  intro i h1 h2
  simp only [regBytes, Native.XmssVerifier.bytes, List.getElem_map, List.getElem_range, Sym.byteOf]
  rw [show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]
  rfl

/-- The value a block loads back from a value's bytes. -/
theorem ofBytes_regBytes (x : BitVec 64) : BitVec.ofInt 64 (Int.ofBytes (regBytes x)) = x := by
  unfold regBytes
  have := Sym.ofBytes_byteOf x 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  rw [this, BitVec.ofInt_natCast, Nat.mod_eq_of_lt x.isLt]
  exact BitVec.eq_of_toNat_eq (by simp)

theorem ofBytes_eq_leNat (bs : List UInt8) :
    BitVec.ofInt 64 (Int.ofBytes bs) = BitVec.ofNat 64 (NativeRustc.leNat bs) := by
  rw [Sym.ofBytes_natCast, BitVec.ofInt_natCast, leNat_eq_ofBytes]

/-- An address at an offset of a non-wrapping range is in a sub-range by its offset. -/
theorem inRange_offsets {f : BitVec 64} {N o s x : Nat} (hf : NoWrap f N) (ho : o + s ≤ N)
    (hx : x < N) :
    InRange (f + BitVec.ofNat 64 o) s (f + BitVec.ofNat 64 x) ↔ o ≤ x ∧ x < o + s := by
  unfold InRange
  unfold NoWrap at hf
  rw [BitVec.toNat_sub, toNat_addr hf hx]
  by_cases hs : s = 0
  · subst hs
    omega
  rw [toNat_addr hf (by omega)]
  have := f.isLt
  constructor
  · intro h
    by_cases hle : o ≤ x
    · rw [show 2 ^ 64 - (f.toNat + o) + (f.toNat + x) = (x - o) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
  · intro ⟨h1, h2⟩
    rw [show 2 ^ 64 - (f.toNat + o) + (f.toNat + x) = (x - o) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Equal-sized pieces at consecutive offsets make their concatenation. -/
theorem bytesAt_flatten {d : DataMem} {a : BitVec 64} {f : Nat → List UInt8} {s : Nat} :
    ∀ n, (∀ j < n, (f j).length = s) → (∀ j < n, BytesAt d (a + BitVec.ofNat 64 (s * j)) (f j)) →
      BytesAt d a ((List.range n).map f).flatten
  | 0, _, _ => fun i hi => by simp at hi
  | n + 1, hf, h => by
    rw [List.range_succ, List.map_append, List.flatten_append]
    refine BytesAt.append (bytesAt_flatten n (fun j hj => hf j (by omega))
      fun j hj => h j (by omega)) ?_
    have hl : (((List.range n).map f).flatten).length = s * n := by
      rw [List.length_flatten, List.map_map]
      clear h
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append, ih (fun j hj => hf j (by omega))]
        simp [hf n (by omega), Nat.mul_succ]
    rw [hl]
    simpa using h n (by omega)

/-! ## After a block -/

variable [Labels] {env : Sym.Env} {S : Sym.SState} {m : MachineData}

/-- A byte a block stored from a load: the environment's byte the load read. -/
theorem Sym.Match.get?_load (hm : Sym.Match env S m) {r j : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hj : j < sz) {r' off k u : Nat}
    (hf : Sym.findWrite r j S.mem = some (.load r' off k, u)) (hu : u < k) (hk : k ≤ 8) :
    m.dmem.get? (b + BitVec.ofNat 64 j) =
      some ((env.mem0.get? (env.base r' + BitVec.ofNat 64 (off + u))).getD 0) := by
  rw [hm.mem r b sz hb j hj]
  unfold Sym.memByte
  rw [hf]
  simp only [Sym.eval]
  rw [Sym.byteOf_load hu hk]

omit [Labels] in
theorem pairwise3 {α : Type} {R : α → α → Prop} {a b c : α} (hab : R a b) (hac : R a c)
    (hbc : R b c) : [a, b, c].Pairwise R := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
  exact ⟨⟨hab, hac⟩, hbc⟩

omit [Labels] in
theorem pairwise4 {α : Type} {R : α → α → Prop} {a b c d : α} (hab : R a b) (hac : R a c)
    (had : R a d) (hbc : R b c) (hbd : R b d) (hcd : R c d) : [a, b, c, d].Pairwise R := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
  exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩

omit [Labels] in
theorem Apart.symm {a a' : BitVec 64} {n n' : Nat} (h : Apart a n a' n') : Apart a' n' a n :=
  Or.symm h

/-- Bytes in a region that no write of the block overlaps are the environment's. -/
theorem Sym.Match.bytesAt_keep (hm : Sym.Match env S m) {r o sz : Nat} {b : BitVec 64}
    {bs : List UInt8} (hb : env.regions[r]? = some (b, sz)) (hle : o + bs.length ≤ sz)
    (hc : Sym.firstOverlap r o bs.length S.mem = none)
    (h0 : BytesAt env.mem0 (b + BitVec.ofNat 64 o) bs) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) bs := fun i hi => by
  rw [addr_add_addr, hm.mem r b sz hb (o + i) (by omega)]
  unfold Sym.memByte
  rw [Sym.findWrite_none hc (by omega) (by omega), ← addr_add_addr]
  exact h0 i hi

/-- Bytes outside the regions are the environment's. -/
theorem Sym.Match.bytesAt_outside (hm : Sym.Match env S m) {a : BitVec 64} {bs : List UInt8}
    (h : ∀ i < bs.length, env.Outside (a + BitVec.ofNat 64 i)) (h0 : BytesAt env.mem0 a bs) :
    BytesAt m.dmem a bs := fun i hi => by
  rw [hm.outside _ (h i hi)]
  exact h0 i hi

/-- Bytes of a region the block wrote, each the byte of the newest write covering it. -/
theorem Sym.Match.bytesAt_of (hm : Sym.Match env S m) {r o sz : Nat} {b : BitVec 64}
    {bs : List UInt8} (hb : env.regions[r]? = some (b, sz)) (hle : o + bs.length ≤ sz)
    (h : ∀ i (hi : i < bs.length), ∃ v t, Sym.findWrite r (o + i) S.mem = some (v, t) ∧
      Sym.byteOf (v.eval env) t = bs[i]) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) bs := fun i hi => by
  obtain ⟨v, t, hf, hv⟩ := h i hi
  rw [addr_add_addr, hm.mem r b sz hb (o + i) (by omega)]
  unfold Sym.memByte
  rw [hf]
  exact congrArg some hv

/-- Each write of `S` is to one of the regions `rs` and within it. -/
@[expose] def writesIn (S : Sym.SState) (rs : List Nat) : Bool :=
  S.mem.all fun w => rs.contains w.r &&
    match S.regions[w.r]? with
    | some sz => decide (w.off + w.n ≤ sz)
    | none => false

/-- The address `p` is in region `r` of the environment. -/
@[expose] def InRegion (env : Sym.Env) (r : Nat) (p : BitVec 64) : Prop :=
  ∃ b sz, env.regions[r]? = some (b, sz) ∧ InRange b sz p

/-- **Memory after a block** is the environment's but in the regions the block writes. -/
theorem Sym.Match.sameOutside_in (hm : Sym.Match env S m) (hwf : env.WF) {rs : List Nat}
    (hc : writesIn S rs = true) :
    SameOutside env.mem0 m.dmem (fun p => ∃ r ∈ rs, InRegion env r p) := by
  refine (hm.sameOutside hwf).mono fun p ⟨w, hw, b, sz, hb, h1, h2⟩ => ?_
  have := List.all_eq_true.mp hc w hw
  simp only [Bool.and_eq_true, List.contains_iff_mem] at this
  obtain ⟨hr, hsz⟩ := this
  cases hS : S.regions[w.r]? with
  | none => rw [hS] at hsz; cases hsz
  | some sz' =>
    rw [hS] at hsz
    simp only [decide_eq_true_eq] at hsz
    obtain ⟨b', hb'⟩ := hm.regions w.r sz' hS
    rw [hb] at hb'
    cases hb'
    have hnw := hwf.noWrap w.r b sz hb
    exact ⟨w.r, hr, b, sz, hb, (Sym.inRange_iff hnw).mpr ⟨by omega, by omega⟩⟩

/-- Each write of `S` is within the first `B` bytes of a region `r` with `(r, B)` in `rs`. -/
@[expose] def writesBelow (S : Sym.SState) (rs : List (Nat × Nat)) : Bool :=
  S.mem.all fun w => rs.any fun rb => w.r == rb.1 && decide (w.off + w.n ≤ rb.2)

/-- **Memory after a block** is the environment's but in the first `B` bytes of the regions `r`
with `(r, B)` in `rs` the block writes. -/
theorem Sym.Match.sameOutside_below (hm : Sym.Match env S m) (hwf : env.WF)
    {rs : List (Nat × Nat)} (hc : writesBelow S rs = true) :
    SameOutside env.mem0 m.dmem (fun p => ∃ rb ∈ rs, ∃ b sz, env.regions[rb.1]? = some (b, sz) ∧
      InRange b rb.2 p) := by
  refine (hm.sameOutside hwf).mono fun p ⟨w, hw, b, sz, hb, h1, h2⟩ => ?_
  have := List.all_eq_true.mp hc w hw
  obtain ⟨rb, hrb, h⟩ := List.any_eq_true.mp this
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hr, hB⟩ := h
  refine ⟨rb, hrb, b, sz, hr ▸ hb, ?_⟩
  unfold InRange
  rw [BitVec.toNat_sub]
  have := p.isLt
  have := b.isLt
  rw [show 2 ^ 64 - b.toNat + p.toNat = (p.toNat - b.toNat) + 2 ^ 64 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

omit [Labels] in
/-- An address apart from every region is outside them. -/
theorem Sym.Env.outside_of {p : BitVec 64}
    (h : Sym.AllOf (fun e : BitVec 64 × Nat => e.1.toNat + e.2 ≤ p.toNat ∨ p.toNat < e.1.toNat)
      env.regions) : env.Outside p := by
  intro r b n hb hc
  have := Sym.mem_of_allOf h (List.mem_of_getElem? hb)
  simp only at this
  omega

omit [Labels] in
/-- An address apart from every region is outside them. -/
theorem Sym.Env.outside_of_apart {p : BitVec 64}
    (h : Sym.AllOf (fun e : BitVec 64 × Nat => Apart e.1 e.2 p 1) env.regions) : env.Outside p := by
  intro r b n hb hc
  have := Sym.mem_of_allOf h (List.mem_of_getElem? hb)
  unfold Apart at this
  simp only at this
  omega

omit [Labels] in
theorem allOf_map_range {α : Type} {P : α → Prop} {f : Nat → α} :
    ∀ {n : Nat}, (∀ j < n, P (f j)) → Sym.AllOf P ((List.range n).map f)
  | 0, _ => trivial
  | n + 1, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    exact ⟨h 0 (by omega), allOf_map_range (f := f ∘ Nat.succ) fun j hj => h (j + 1) (by omega)⟩

end

/-! ## Steps -/

public section
variable [Host] {env : Sym.Env}

open NativeRustcX64.Sym in
/-- A block ending in a conditional branch that is not taken. -/
theorem cond_step {ds : List Directive} {k : Nat} {S S' : SState} {c : SBool} {l : Label}
    {st : MachineState} {R : MachineState → Prop} (hk : ds.IsInfixAt Host.prog k)
    (hx : exec ds S = some (S', .cond c l)) (hwf : env.WF) (hpc : st.pc = Host.addrOf k)
    (hm : Match env S st.data) (hc : c.eval env = false)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + ds.length) →
      Match env ((exec ds S).getD (S, .fall)).1 st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at hk hx hwf (fun _ h => nomatch h) hpc hm fun st' hm' hpc' => cont st'
    (by simpa only [PcOk, hc, Bool.false_eq_true, ite_false] using hpc') (by rw [hx]; exact hm')

open NativeRustcX64.Sym in
/-- A block falling through. -/
theorem fall_step {ds : List Directive} {k : Nat} {S S' : SState}
    {st : MachineState} {R : MachineState → Prop} (hk : ds.IsInfixAt Host.prog k)
    (hx : exec ds S = some (S', .fall)) (hwf : env.WF) (hpc : st.pc = Host.addrOf k)
    (hm : Match env S st.data)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + ds.length) →
      Match env ((exec ds S).getD (S, .fall)).1 st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at hk hx hwf (fun _ h => nomatch h) hpc hm fun st' hm' hpc' =>
    cont st' hpc' (by rw [hx]; exact hm')

open NativeRustcX64.Sym in
/-- A block ending in a call, its return address the environment's. -/
theorem call_step {ds : List Directive} {k : Nat} {S S' : SState} {l : Label}
    {st : MachineState} {R : MachineState → Prop} (hk : ds.IsInfixAt Host.prog k)
    (hx : exec ds S = some (S', .call l)) (hwf : env.WF)
    (hret : env.ret = (Host.addrOf (k + ds.length)).toBitVec) (hpc : st.pc = Host.addrOf k)
    (hm : Match env S st.data)
    (cont : ∀ st' : MachineState, PcOk env (.call l) (Host.addrOf (k + ds.length)) st' →
      Match env ((exec ds S).getD (S, .fall)).1 st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at hk hx hwf (fun _ _ => hret) hpc hm fun st' hm' hpc' =>
    cont st' hpc' (by rw [hx]; exact hm')

end

end NativeRustcX64
