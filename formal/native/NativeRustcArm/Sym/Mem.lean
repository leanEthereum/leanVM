module

public import NativeRustcArm.Sym.Smart
public import NativeRustcArm.Sym.Bytes

/-!
# Symbolic memory accesses are sound

Where the symbolic executor places an access at a constant offset (`SState.access`) or at a
bounded index (`SState.accessIdx`), Kraken's machine accesses the same bytes of the same region:
the symbolic load's value is the integer Kraken loads (`Match.loadSym`, `Match.load_mem0`);
`NativeRustcArm.Sym.Slots` assembles the loads and stores (`Match.loadAt`, `Match.storeAt`). Address operands (`Match.addr`, `Match.uaddr`) and the check of SP's alignment
(`Match.checkSp`, `Match.checkSpU`) are Kraken's.
-/

namespace NativeRustcArm.Sym

public section

/-! ## The newest write of a byte -/

theorem findWrite_cons (r i : Nat) (w : Write) (ws : List Write) :
    findWrite r i (w :: ws) =
      if w.r = r ∧ w.off ≤ i ∧ i < w.off + w.n then some (w.v, i - w.off) else findWrite r i ws :=
  (rfl)

theorem firstOverlap_cons (r o n : Nat) (w : Write) (ws : List Write) :
    firstOverlap r o n (w :: ws) =
      if w.r = r ∧ w.off < o + n ∧ o < w.off + w.n then some w else firstOverlap r o n ws :=
  (rfl)

theorem findWrite_none {r o n i : Nat} {ws : List Write} (h : firstOverlap r o n ws = none)
    (hi : o ≤ i) (hi' : i < o + n) : findWrite r i ws = none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [firstOverlap_cons] at h
    split at h
    · cases h
    · rename_i hw
      rw [findWrite_cons, ite_neg (by omega)]
      exact ih h

theorem findWrite_some {r o n i : Nat} {ws : List Write} {w : Write}
    (h : firstOverlap r o n ws = some w) (hc : w.off ≤ o ∧ o + n ≤ w.off + w.n) (hi : o ≤ i)
    (hi' : i < o + n) : findWrite r i ws = some (w.v, i - w.off) := by
  induction ws with
  | nil => cases h
  | cons w' ws ih =>
    rw [firstOverlap_cons] at h
    split at h
    · rename_i hw
      cases h
      rw [findWrite_cons, ite_pos (by omega)]
    · rename_i hw
      rw [findWrite_cons, ite_neg (by omega)]
      exact ih h

theorem findWrite_filter {r i : Nat} (p : Write → Bool) (ws : List Write)
    (hp : ∀ w ∈ ws, p w = false → ¬(w.r = r ∧ w.off ≤ i ∧ i < w.off + w.n)) :
    findWrite r i (ws.filter p) = findWrite r i ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have ih' := ih (fun w' hw' => hp w' (List.mem_cons_of_mem _ hw'))
    rw [List.filter_cons]
    by_cases hpw : p w = true
    · rw [ite_pos hpw, findWrite_cons, findWrite_cons]
      split
      · rfl
      · exact ih'
    · rw [ite_neg hpw]
      have := hp w List.mem_cons_self (by simpa using hpw)
      rw [findWrite_cons, ite_neg this]
      exact ih'

/-! ## Regions -/

variable [Labels] {env : Env} {S : SState} {m : MachineData}

omit [Labels] in
theorem Env.base_eq {r : Nat} {b : BitVec 64} {n : Nat} (h : env.regions[r]? = some (b, n)) :
    env.base r = b := by
  simp [Env.base, h]

omit [Labels] in
theorem access_spec {a : Sym} {n r o : Nat} (h : S.access a n = some (r, o)) :
    ∃ o' sz al, S.toPtr a = some (r, o') ∧ (o' : Int) = o ∧ S.regions[r]? = some (sz, al) ∧
      o + n ≤ sz := by
  unfold SState.access at h
  split at h
  · rename_i r' o' hp
    split at h
    · rename_i sz al hr
      split at h
      · rename_i hc
        cases h
        exact ⟨o', sz, al, hp, by omega, hr, by omega⟩
      · cases h
    · cases h
  · cases h

theorem Match.basePtr (hm : Match env S m) {a : Sym} {r : Nat} {o : Int}
    (h : S.basePtr a = some (r, o)) : a.eval env = env.base r + BitVec.ofInt 64 o := by
  unfold SState.basePtr at h
  cases ha : S.aliases.lookup a with
  | some ro =>
    rw [ha] at h
    cases h
    exact hm.aliases a r o ha
  | none =>
    rw [ha] at h
    cases a with
    | ptr r' o' =>
      cases h
      rfl
    | label l =>
      cases hl : S.labels.lookup l with
      | none => simp [hl] at h
      | some r' =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Sym.eval, hm.labels l r' hl, BitVec.ofInt_ofNat, BitVec.add_zero]
    | _ => cases h

theorem Match.toPtr (hm : Match env S m) {a : Sym} {r : Nat} {o : Int} (h : S.toPtr a = some (r, o)) :
    a.eval env = env.base r + BitVec.ofInt 64 o := by
  unfold SState.toPtr at h
  cases hb : S.basePtr a with
  | some ro =>
    rw [hb] at h
    cases h
    exact hm.basePtr hb
  | none =>
    rw [hb] at h
    cases hx : a.asAddLit with
    | none => simp [hx] at h
    | some xc =>
      obtain ⟨x, c⟩ := xc
      cases hbx : S.basePtr x with
      | none => simp [hx, hbx] at h
      | some ro =>
        simp only [hx, hbx, Option.map_some, Option.some.injEq] at h
        cases h
        rw [asAddLit_eq hx]
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hm.basePtr hbx, BitVec.ofInt_add,
          ofInt_litInt, BitVec.add_assoc]

/-- An access the executor places: its region in `env`, its address. -/
theorem Match.access (hm : Match env S m) {a : Sym} {n r o : Nat} (h : S.access a n = some (r, o)) :
    ∃ b sz, env.regions[r]? = some (b, sz) ∧ o + n ≤ sz ∧ a.eval env = b + BitVec.ofNat 64 o := by
  obtain ⟨o', sz, al, hp, ho, hr, hle⟩ := access_spec h
  obtain ⟨b, hb, -⟩ := hm.regions r sz al hr
  refine ⟨b, sz, hb, hle, ?_⟩
  rw [hm.toPtr hp, Env.base_eq hb, ho, BitVec.ofInt_natCast]

omit [Labels] in
theorem addr_add (b : BitVec 64) (o i : Nat) :
    b + BitVec.ofNat 64 o + BitVec.ofNat 64 i = b + BitVec.ofNat 64 (o + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem Match.get?_some (hm : Match env S m) (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz i : Nat}
    (hr : env.regions[r]? = some (b, sz)) (hi : i < sz) :
    (m.dmem.get? (b + BitVec.ofNat 64 i)).isSome := by
  rw [hm.mem r b sz hr i hi]
  unfold memByte
  split
  · rfl
  · exact hwf.mapped r b sz hr i hi

/-! ## Loads -/

omit [Labels] in
theorem toNat_ofInt_ofBytes (bs : List UInt8) (hn : bs.length ≤ 8) :
    ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int) = Int.ofBytes bs := by
  obtain ⟨h0, h1⟩ := ofBytes_nonneg_lt bs
  have : (2 : Int) ^ (8 * bs.length) ≤ 2 ^ 64 :=
    (show ∀ k, k ≤ 8 → (2 : Int) ^ (8 * k) ≤ 2 ^ 64 by decide) _ hn
  rw [BitVec.toNat_ofInt]
  omega

/-- The byte the writes `ws` over `env.mem0` give at `j` in region `r` (base `b`). -/
def memByteD (env : Env) (ws : List Write) (r : Nat) (b : BitVec 64) (j : Nat) : UInt8 :=
  match findWrite r j ws with
  | some (v, t) => byteOf (v.eval env) t
  | none => (env.mem0.get? (b + BitVec.ofNat 64 j)).getD 0

theorem memByte_eq (hwf : env.WF) {ws : List Write} {r : Nat} {b : BitVec 64} {sz j : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hj : j < sz) :
    memByte env ws r b j = some (memByteD env ws r b j) := by
  unfold memByte memByteD
  cases findWrite r j ws with
  | some vt => rfl
  | none =>
    have := hwf.mapped r b sz hb j hj
    revert this
    cases env.mem0.get? (b + BitVec.ofNat 64 j) <;> simp

omit [Labels] in
theorem natOfBytes_lt (bs : List UInt8) : Nat.ofBytes bs < 2 ^ (8 * bs.length) := by
  have := (ofBytes_nonneg_lt bs).2
  rw [ofBytes_natCast] at this
  exact_mod_cast this

theorem eval_byteSym {ws : List Write} {r : Nat} {b : BitVec 64} (hb : env.base r = b) (j : Nat) :
    (byteSym ws r j).eval env = BitVec.ofNat 64 (memByteD env ws r b j).toNat := by
  unfold byteSym memByteD
  cases findWrite r j ws with
  | some vt =>
    obtain ⟨v, t⟩ := vt
    show (mkBytes v t 1).eval env = BitVec.ofNat 64 (byteOf (v.eval env) t).toNat
    rw [eval_mkBytes, byteOf_mod, UInt8.toNat_ofNat']
    unfold bytesOf
    congr 1
    omega
  | none =>
    show Env.load env r j 1 = _
    unfold Env.load
    rw [hb]
    show BitVec.ofInt 64 (Int.ofBytes [_]) = _
    rw [ofBytes_natCast, BitVec.ofInt_natCast]
    simp [Nat.ofBytes]

theorem eval_assemble {ws : List Write} {r : Nat} {b : BitVec 64} (hb : env.base r = b) :
    ∀ n o, (assemble ws r o n).eval env =
      BitVec.ofNat 64 (Nat.ofBytes ((List.range n).map fun i => memByteD env ws r b (o + i)))
  | 0, _ => rfl
  | n + 1, o => by
    rw [assemble, eval_mkBin, eval_mkUn, eval_assemble hb n (o + 1), eval_byteSym hb,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    have hf : ((fun i => memByteD env ws r b (o + i)) ∘ Nat.succ) =
        fun i => memByteD env ws r b (o + 1 + i) := by
      funext i
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1
      omega
    rw [hf]
    show _ = BitVec.ofNat 64 (Nat.ofBytes _ * 256 + (memByteD env ws r b (o + 0)).toNat)
    simp only [BinOp.apply, UnOp.apply, shiftW, low_W64, ext_W64, Nat.add_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      MemWidth.bits]
    omega

/-- A load of bytes no write covers is `env.mem0`'s. -/
theorem Match.load_mem0 (hm : Match env S m) (hwf : env.WF) {r o n : Nat} {b : BitVec 64}
    {sz : Nat} (hb : env.regions[r]? = some (b, sz)) (hle : o + n ≤ sz) (hn : n ≤ 8)
    (hno : ∀ j, o ≤ j → j < o + n → findWrite r j S.mem = none) :
    Mem.loadInt m.dmem (b + BitVec.ofNat 64 o) n = some ((env.load r o n).toNat : Int) ∧
      (env.load r o n).toNat < 2 ^ (8 * n) := by
  have h64 : 2 ^ (8 * n) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hget : ∀ i < n, m.dmem.get? (b + BitVec.ofNat 64 o + BitVec.ofNat 64 i) =
      some ((env.mem0.get? (env.base r + BitVec.ofNat 64 (o + i))).getD 0) := by
    intro i hi
    rw [addr_add, hm.mem r b sz hb (o + i) (by omega), Env.base_eq hb]
    unfold memByte
    rw [hno (o + i) (by omega) (by omega)]
    have := hwf.mapped r b sz hb (o + i) (by omega)
    revert this
    cases env.mem0.get? (b + BitVec.ofNat 64 (o + i)) <;> simp
  rw [loadInt_of_get? _ _ n _ hget]
  have hlen : ((List.range n).map fun i =>
      (env.mem0.get? (env.base r + BitVec.ofNat 64 (o + i))).getD 0).length = n := by simp
  have h2 := (ofBytes_nonneg_lt ((List.range n).map fun i =>
    (env.mem0.get? (env.base r + BitVec.ofNat 64 (o + i))).getD 0)).2
  rw [hlen] at h2
  refine ⟨?_, ?_⟩
  · unfold Env.load
    rw [toNat_ofInt_ofBytes _ (by omega)]
  · unfold Env.load
    have := toNat_ofInt_ofBytes ((List.range n).map fun i =>
      (env.mem0.get? (env.base r + BitVec.ofNat 64 (o + i))).getD 0) (by omega)
    have h3 : ((2 ^ (8 * n) : Nat) : Int) = 2 ^ (8 * n) := by rw [Int.natCast_pow]; rfl
    omega

omit [Labels] in
theorem findWrite_none_of_all {r j : Nat} {ws : List Write} (h : ws.all (·.r != r) = true) :
    findWrite r j ws = none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rw [findWrite_cons, ite_neg (fun hc => h.1 hc.1)]
    exact ih (by simpa using h.2)

omit [Labels] in
theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨a', b'⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i ha
      cases h
      rw [beq_iff_eq] at ha
      subst ha
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem Match.idxMax (hm : Match env S m) {i : Sym} {M : Nat} (h : S.idxMax i = some M) :
    (i.eval env).toNat ≤ M := by
  unfold SState.idxMax at h
  split at h
  · rename_i k x
    cases hl : S.bounds.lookup x with
    | none => rw [hl] at h; cases h
    | some B =>
      rw [hl] at h
      cases h
      have hx := hm.bounds x B (mem_of_lookup hl)
      show (BitVec.ofInt 64 ((x.eval env).apply_mem_extend ⟨.UXTX, k⟩)).toNat ≤ _
      cases k <;> simp only [BitVec.apply_mem_extend, BitVec.unsigned, BitVec.toNat_ofInt,
        Int.shiftLeft_eq] <;> omega
  · rename_i k x
    cases hl : S.bounds.lookup x with
    | none => rw [hl] at h; cases h
    | some B =>
      rw [hl] at h
      cases h
      have hx := hm.bounds x B (mem_of_lookup hl)
      show (ext .W64 (shiftW .LSL (low .W64 (x.eval env)) k)).toNat ≤ _
      simp only [ext_W64, low_W64, shiftW, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.mul_le_mul_right _ (by omega))
  · cases hl : S.bounds.lookup i with
    | none => rw [hl] at h; cases h
    | some B =>
      rw [hl] at h
      cases h
      have := hm.bounds i B (mem_of_lookup hl)
      show (i.eval env).toNat ≤ B - 1
      omega

theorem Match.accessIdxAt (hm : Match env S m) {p i' i : Sym} {d : Int} {n r o M : Nat}
    (h : S.accessIdxAt p i' d n = some (r, o, i, M)) :
    i' = i ∧ ∃ b sz, env.regions[r]? = some (b, sz) ∧ (i.eval env).toNat ≤ M ∧
      o + (i.eval env).toNat + n ≤ sz ∧
      p.eval env + BitVec.ofInt 64 d + i.eval env = b + BitVec.ofNat 64 (o + (i.eval env).toNat) := by
  unfold SState.accessIdxAt at h
  cases hp : S.toPtr p with
  | none => simp [hp] at h
  | some ro =>
    obtain ⟨r', o'⟩ := ro
    cases hM : S.idxMax i' with
    | none => simp [hp, hM] at h
    | some M' =>
      simp only [hp, hM] at h
      cases hr : S.regions[r']? with
      | none => simp [hr] at h
      | some szal =>
        obtain ⟨sz, al⟩ := szal
        simp only [hr] at h
        split at h
        · rename_i hc
          cases h
          obtain ⟨b, hb, -⟩ := hm.regions r sz al hr
          have hle := hm.idxMax hM
          refine ⟨rfl, b, sz, hb, hle, by omega, ?_⟩
          rw [hm.toPtr hp, Env.base_eq hb]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
          omega
        · cases h

/-- An indexed access the executor places: its region, and its address for the index's value. -/
theorem Match.accessIdx (hm : Match env S m) {a i : Sym} {n r o M : Nat}
    (h : S.accessIdx a n = some (r, o, i, M)) :
    ∃ b sz, env.regions[r]? = some (b, sz) ∧ (i.eval env).toNat ≤ M ∧
      o + (i.eval env).toNat + n ≤ sz ∧
      a.eval env = b + BitVec.ofNat 64 (o + (i.eval env).toNat) := by
  unfold SState.accessIdx at h
  split at h
  · rename_i p i' c ha
    obtain ⟨rfl, b, sz, hb, hM, hle, he⟩ := hm.accessIdxAt h
    refine ⟨b, sz, hb, hM, hle, ?_⟩
    rw [asAddLit_eq ha, ← he]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, ofInt_litInt]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, MemWidth.bits]
    omega
  · split at h
    · rename_i p i'
      obtain ⟨rfl, b, sz, hb, hM, hle, he⟩ := hm.accessIdxAt h
      refine ⟨b, sz, hb, hM, hle, ?_⟩
      rw [← he]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    · cases h

/-- The value of the symbolic load of `n` bytes at `o` in region `r` is the integer Kraken loads
there. -/
theorem Match.loadSym (hm : Match env S m) (hwf : env.WF) {r o n : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + n ≤ sz) (hn : n ≤ 8) :
    Mem.loadInt m.dmem (b + BitVec.ofNat 64 o) n =
        some (((loadSym S.mem r o n).eval env).toNat : Int) ∧
      ((loadSym S.mem r o n).eval env).toNat < 2 ^ (8 * n) := by
  have h64 : 2 ^ (8 * n) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  -- the bytes of the general case
  have hgen : Mem.loadInt m.dmem (b + BitVec.ofNat 64 o) n = some ((Nat.ofBytes
      ((List.range n).map fun i => memByteD env S.mem r b (o + i)) : Nat) : Int) := by
    rw [loadInt_of_get? _ _ n (fun i => memByteD env S.mem r b (o + i)) (fun i hi => by
      rw [addr_add, hm.mem r b sz hb (o + i) (by omega), memByte_eq hwf hb (by omega)]),
      ofBytes_natCast]
  have hlt := natOfBytes_lt ((List.range n).map fun i => memByteD env S.mem r b (o + i))
  rw [List.length_map, List.length_range] at hlt
  cases hf : firstOverlap r o n S.mem with
  | none =>
    simp only [NativeRustcArm.Sym.loadSym, hf]
    exact hm.load_mem0 hwf hb hle hn fun j hj hj' => findWrite_none hf hj hj'
  | some w =>
    by_cases hc : w.off ≤ o ∧ o + n ≤ w.off + w.n
    · simp only [NativeRustcArm.Sym.loadSym, hf, hc, and_self, ite_true]
      have hget : ∀ i < n, m.dmem.get? (b + BitVec.ofNat 64 o + BitVec.ofNat 64 i) =
          some (byteOf (w.v.eval env) (o - w.off + i)) := by
        intro i hi
        rw [addr_add, hm.mem r b sz hb (o + i) (by omega)]
        unfold memByte
        rw [findWrite_some hf hc (by omega) (by omega),
          show o + i - w.off = o - w.off + i by have := hc.1; omega]
      rw [loadInt_of_get? _ _ n _ hget, ofBytes_byteOf, eval_mkBytes]
      have hlt' : (w.v.eval env).toNat / 2 ^ (8 * (o - w.off)) % 2 ^ (8 * n) < 2 ^ (8 * n) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have heq : (bytesOf (w.v.eval env) (o - w.off) n).toNat =
          (w.v.eval env).toNat / 2 ^ (8 * (o - w.off)) % 2 ^ (8 * n) := by
        unfold bytesOf
        rw [BitVec.toNat_ofNat]
        omega
      rw [heq]
      exact ⟨rfl, hlt'⟩
    · simp only [NativeRustcArm.Sym.loadSym, hf, hc, ite_false]
      rw [eval_assemble (Env.base_eq hb), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact ⟨hgen, hlt⟩

omit [Labels] in
theorem findWrite_none_of_apart {r j o M n : Nat} {ws : List Write}
    (h : ws.all (fun w => w.r != r || w.off + w.n ≤ o || o + M + n ≤ w.off) = true)
    (hj1 : o ≤ j) (hj2 : j < o + M + n) : findWrite r j ws = none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at h
    rw [findWrite_cons, ite_neg (by omega)]
    exact ih (by simpa using h.2)

/-! ## Addresses -/

omit [Labels] in
theorem ofInt_signed_add (x : BitVec 64) (off : Int) :
    BitVec.ofInt 64 (x.signed + off) = x + BitVec.ofInt 64 off := by
  rw [BitVec.ofInt_add, BitVec.signed, BitVec.ofInt_toInt]

theorem constInt_spec {c : ConstExpr} {off : Int} (h : constInt c = some off) (p : Std.Rco Int64) :
    (c.interp p).toInt = off := by
  cases c <;> cases h
  rfl

theorem eval_addImm (b : Sym) (off : Int) :
    (mkBin .add .W64 b (.lit (BitVec.ofInt 64 off).toNat)).eval env = b.eval env + BitVec.ofInt 64 off := by
  rw [eval_mkBin, eval_lit_toNat]
  simp only [BinOp.apply, low_W64, ext_W64]

/-- **An address operand is Kraken's**: the address, and the state after the base's writeback. -/
theorem Match.addr (hm : Match env S m) {ae : AddrExpr} {a : Sym} {S₁ : SState}
    (h : S.addr ae = some (a, S₁)) (p : Std.Rco Int64) :
    (ae.eval m p).1 = a.eval env ∧ Match env S₁ (ae.eval m p).2 ∧ (ae.eval m p).2.dmem = m.dmem := by
  obtain ⟨base, off⟩ := ae
  unfold SState.addr at h
  cases hb : S.getSp base with
  | none => rw [hb] at h; cases h
  | some bs =>
    rw [hb] at h
    have hbase : m.regs.getRegOrSp base = bs.eval env := by rw [hm.getSp hb, low_W64]
    cases off with
    | reg e =>
      cases hi : S.getZr64 e.reg.reg.base with
      | none => simp [hi] at h
      | some is =>
        simp only [hi] at h
        cases h
        refine ⟨?_, hm, rfl⟩
        simp only [AddrExpr.eval, MemExtRegExpr.interp, hbase, hm.getZr64 hi, ofInt_signed_add,
          eval_mkBin, eval_mkUn, BinOp.apply, UnOp.apply, low_W64, ext_W64]
    | imm i =>
      obtain ⟨c, idx⟩ := i
      cases hc : constInt c with
      | none => simp [hc] at h
      | some o =>
        simp only [hc] at h
        have hoff := constInt_spec hc p
        cases idx with
        | none =>
          cases h
          refine ⟨?_, hm, rfl⟩
          simp only [AddrExpr.eval, hbase, hoff, ofInt_signed_add, eval_addImm]
        | some ix =>
          cases ix <;> cases h <;>
          refine ⟨?_, ?_, rfl⟩
          · simp only [AddrExpr.eval, hbase, hoff, ofInt_signed_add, eval_addImm]
          · simp only [AddrExpr.eval, hbase, hoff, ofInt_signed_add]
            exact hm.setSp base (eval_addImm _ _)
          · simp only [AddrExpr.eval, hbase, BitVec.signed, BitVec.ofInt_toInt]
          · simp only [AddrExpr.eval, hbase, hoff, ofInt_signed_add]
            exact hm.setSp base (eval_addImm _ _)

/-- An unscaled address operand is Kraken's. -/
theorem Match.uaddr (hm : Match env S m) {ua : UnscaledAddrExpr} {a : Sym}
    (h : S.uaddr ua = some a) (p : Std.Rco Int64) : ua.eval m p = a.eval env := by
  obtain ⟨base, c⟩ := ua
  unfold SState.uaddr at h
  cases hb : S.getSp base with
  | none => rw [hb] at h; cases h
  | some bs =>
    cases hc : constInt c with
    | none => simp [hb, hc] at h
    | some o =>
      simp only [hb, hc] at h
      cases h
      simp only [UnscaledAddrExpr.eval, hm.getSp hb, low_W64, constInt_spec hc p,
        ofInt_signed_add, eval_addImm]

theorem Match.spAligned (hm : Match env S m) (h : S.spAligned = true) :
    (m.regs.getRegOrSp RegOrSp.SP % 16#64 != 0#64) = false := by
  have hsp : m.regs.getRegOrSp RegOrSp.SP = S.sp.eval env := by
    show (m.regs.SP.toBitVec).take 64 = _
    rw [← low_W64 (S.sp.eval env), hm.sp]
    rfl
  rw [hsp]
  unfold SState.spAligned at h
  split at h
  · rename_i r o hsp'
    split at h
    · rename_i sz al hr
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨b, hb, hal⟩ := hm.regions r sz al hr
      have hb16 := hal h.1
      rw [hsp']
      simp only [Sym.eval, Env.base_eq hb, bne_eq_false_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_ofInt]
      show (b.toNat + (o % 18446744073709551616).toNat) % 18446744073709551616 % 16 = 0
      omega
    · cases h
  · cases h

theorem Match.checkSp (hm : Match env S m) {ae : AddrExpr} (h : S.checkSp ae.base = true)
    (ok : Unit → Effects) : ae.checkSPAlignment m ok = ok () := by
  obtain ⟨⟨b, w⟩, off⟩ := ae
  cases b with
  | SP =>
    show (if _ then _ else ok ()) = ok ()
    rw [hm.spAligned h]
    rfl
  | reg x => rfl

theorem Match.checkSpU (hm : Match env S m) {ua : UnscaledAddrExpr} (h : S.checkSp ua.base = true)
    (ok : Unit → Effects) : ua.checkSPAlignment m ok = ok () := by
  obtain ⟨⟨b, w⟩, off⟩ := ua
  cases b with
  | SP =>
    show (if _ then _ else ok ()) = ok ()
    rw [hm.spAligned h]
    rfl
  | reg x => rfl

end

end NativeRustcArm.Sym
