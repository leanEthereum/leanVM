module

public import NativeRustcX64.Sym.Smart
public import NativeRustcX64.Sym.Bytes

/-!
# Symbolic memory accesses are sound

Where the symbolic executor places an access at a constant offset (`SState.access`) or at a
bounded index (`SState.accessIdx`), Kraken's machine accesses the same bytes of the same region:
the symbolic load's value is the integer Kraken loads (`Match.loadSym`, `Match.load_mem0`);
`NativeRustcX64.Sym.Slots` assembles the loads and stores (`Match.loadAt`, `Match.storeAt`). Address operands are Kraken's (`Match.addr`).
-/

namespace NativeRustcX64.Sym

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
    ∃ o' sz, S.toPtr a = some (r, o') ∧ (o' : Int) = o ∧ S.regions[r]? = some sz ∧
      o + n ≤ sz := by
  unfold SState.access at h
  split at h
  · rename_i r' o' hp
    split at h
    · rename_i sz hr
      split at h
      · rename_i hc
        cases h
        exact ⟨o', sz, hp, by omega, hr, by omega⟩
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

theorem Match.toPtr (hm : Match env S m) {a : Sym} {r : Nat} {o : Int}
    (h : S.toPtr a = some (r, o)) :
    a.eval env = env.base r + BitVec.ofInt 64 o := by
  unfold SState.toPtr at h
  cases hb : S.basePtr a with
  | some ro =>
    rw [hb] at h
    cases h
    exact hm.basePtr hb
  | none =>
    rw [hb] at h
    dsimp only at h
    cases a with
    | bin op w x y =>
      cases op <;> try cases h
      cases w <;> try cases h
      cases y <;> try cases h
      rename_i c
      cases hbx : S.basePtr x with
      | none => simp [hbx] at h
      | some ro =>
        simp only [hbx, Option.map_some, Option.some.injEq] at h
        cases h
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hm.basePtr hbx, BitVec.ofInt_add,
          ofInt_litInt, BitVec.add_assoc]
    | _ => cases h

/-- An access the executor places: its region in `env`, its address. -/
theorem Match.access (hm : Match env S m) {a : Sym} {n r o : Nat} (h : S.access a n = some (r, o)) :
    ∃ b sz, env.regions[r]? = some (b, sz) ∧ o + n ≤ sz ∧ a.eval env = b + BitVec.ofNat 64 o := by
  obtain ⟨o', sz, hp, ho, hr, hle⟩ := access_spec h
  obtain ⟨b, hb⟩ := hm.regions r sz hr
  refine ⟨b, sz, hb, hle, ?_⟩
  rw [hm.toPtr hp, Env.base_eq hb, ho, BitVec.ofInt_natCast]

omit [Labels] in
theorem addr_add (b : BitVec 64) (o i : Nat) :
    b + BitVec.ofNat 64 o + BitVec.ofNat 64 i = b + BitVec.ofNat 64 (o + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem Match.get?_some_ro (hm : Match env S m) (hwf : env.WFRo) {r : Nat} {b : BitVec 64} {sz i : Nat}
    (hr : env.regions[r]? = some (b, sz)) (hi : i < sz) :
    (m.dmem.get? (b + BitVec.ofNat 64 i)).isSome := by
  rw [hm.mem r b sz hr i hi]
  unfold memByte
  split
  · rfl
  · exact hwf.mapped r b sz hr i hi

theorem Match.get?_some (hm : Match env S m) (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz i : Nat}
    (hr : env.regions[r]? = some (b, sz)) (hi : i < sz) :
    (m.dmem.get? (b + BitVec.ofNat 64 i)).isSome :=
  hm.get?_some_ro hwf.toWFRo hr hi

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

theorem memByte_eq_ro (hwf : env.WFRo) {ws : List Write} {r : Nat} {b : BitVec 64} {sz j : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hj : j < sz) :
    memByte env ws r b j = some (memByteD env ws r b j) := by
  unfold memByte memByteD
  cases findWrite r j ws with
  | some vt => rfl
  | none =>
    have := hwf.mapped r b sz hb j hj
    revert this
    cases env.mem0.get? (b + BitVec.ofNat 64 j) <;> simp

theorem memByte_eq (hwf : env.WF) {ws : List Write} {r : Nat} {b : BitVec 64} {sz j : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hj : j < sz) :
    memByte env ws r b j = some (memByteD env ws r b j) :=
  memByte_eq_ro hwf.toWFRo hb hj

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

omit [Labels] in
theorem shiftCount_8 : shiftCount .W64 (BitVec.ofNat 64 8) = 8 := by decide

theorem eval_assemble {ws : List Write} {r : Nat} {b : BitVec 64} (hb : env.base r = b) :
    ∀ n o, (assemble ws r o n).eval env =
      BitVec.ofNat 64 (Nat.ofBytes ((List.range n).map fun i => memByteD env ws r b (o + i)))
  | 0, _ => rfl
  | n + 1, o => by
    rw [assemble, eval_mkBin, eval_mkBin, eval_assemble hb n (o + 1), eval_byteSym hb,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    have hf : ((fun i => memByteD env ws r b (o + i)) ∘ Nat.succ) =
        fun i => memByteD env ws r b (o + 1 + i) := by
      funext i
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1
      omega
    rw [hf]
    show _ = BitVec.ofNat 64 (Nat.ofBytes _ * 256 + (memByteD env ws r b (o + 0)).toNat)
    simp only [BinOp.apply, low_W64, ext_W64, Sym.eval, shiftCount_8, Nat.add_zero, Width.bits]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Width.bits]
    omega

/-- A load of bytes no write covers is `env.mem0`'s. -/
theorem Match.load_mem0_ro (hm : Match env S m) (hwf : env.WFRo) {r o n : Nat} {b : BitVec 64}
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

theorem Match.load_mem0 (hm : Match env S m) (hwf : env.WF) {r o n : Nat} {b : BitVec 64}
    {sz : Nat} (hb : env.regions[r]? = some (b, sz)) (hle : o + n ≤ sz) (hn : n ≤ 8)
    (hno : ∀ j, o ≤ j → j < o + n → findWrite r j S.mem = none) :
    Mem.loadInt m.dmem (b + BitVec.ofNat 64 o) n = some ((env.load r o n).toNat : Int) ∧
      (env.load r o n).toNat < 2 ^ (8 * n) :=
  hm.load_mem0_ro hwf.toWFRo hb hle hn hno

/-- The value of the symbolic load of `n` bytes at `o` in region `r` is the integer Kraken loads
there. -/
theorem Match.loadSym_ro (hm : Match env S m) (hwf : env.WFRo) {r o n : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + n ≤ sz) (hn : n ≤ 8) :
    Mem.loadInt m.dmem (b + BitVec.ofNat 64 o) n =
        some (((loadSym S.mem r o n).eval env).toNat : Int) ∧
      ((loadSym S.mem r o n).eval env).toNat < 2 ^ (8 * n) := by
  have h64 : 2 ^ (8 * n) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hgen : Mem.loadInt m.dmem (b + BitVec.ofNat 64 o) n = some ((Nat.ofBytes
      ((List.range n).map fun i => memByteD env S.mem r b (o + i)) : Nat) : Int) := by
    rw [loadInt_of_get? _ _ n (fun i => memByteD env S.mem r b (o + i)) (fun i hi => by
      rw [addr_add, hm.mem r b sz hb (o + i) (by omega), memByte_eq_ro hwf hb (by omega)]),
      ofBytes_natCast]
  have hlt := natOfBytes_lt ((List.range n).map fun i => memByteD env S.mem r b (o + i))
  rw [List.length_map, List.length_range] at hlt
  cases hf : firstOverlap r o n S.mem with
  | none =>
    simp only [NativeRustcX64.Sym.loadSym, hf]
    exact hm.load_mem0_ro hwf hb hle hn fun j hj hj' => findWrite_none hf hj hj'
  | some w =>
    by_cases hc : w.off ≤ o ∧ o + n ≤ w.off + w.n
    · simp only [NativeRustcX64.Sym.loadSym, hf, hc, and_self, ite_true]
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
    · simp only [NativeRustcX64.Sym.loadSym, hf, hc, ite_false]
      rw [eval_assemble (Env.base_eq hb), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact ⟨hgen, hlt⟩

theorem Match.loadSym (hm : Match env S m) (hwf : env.WF) {r o n : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + n ≤ sz) (hn : n ≤ 8) :
    Mem.loadInt m.dmem (b + BitVec.ofNat 64 o) n =
        some (((loadSym S.mem r o n).eval env).toNat : Int) ∧
      ((loadSym S.mem r o n).eval env).toNat < 2 ^ (8 * n) :=
  hm.loadSym_ro hwf.toWFRo hb hle hn

/-! ## Indexed loads -/

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
  · rename_i x s
    cases hl : S.bounds.lookup x with
    | none => rw [hl] at h; cases h
    | some B =>
      rw [hl] at h
      cases h
      have hx := hm.bounds x B (mem_of_lookup hl)
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat]
      have : (x.eval env).toNat * (s % 2 ^ 64) ≤ (B - 1) * s :=
        Nat.mul_le_mul (by omega) (Nat.mod_le _ _)
      exact Nat.le_trans (Nat.mod_le _ _) this
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
      p.eval env + BitVec.ofInt 64 d + i.eval env =
        b + BitVec.ofNat 64 (o + (i.eval env).toNat) := by
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
      | some sz =>
        simp only [hr] at h
        split at h
        · rename_i hc
          cases h
          obtain ⟨b, hb⟩ := hm.regions r sz hr
          have hle := hm.idxMax hM
          refine ⟨rfl, b, sz, hb, hle, by omega, ?_⟩
          rw [hm.toPtr hp, Env.base_eq hb]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
          omega
        · cases h

theorem Match.accessIdx2 (hm : Match env S m) {x y i : Sym} {d : Int} {n r o M : Nat}
    (h : S.accessIdx2 x y d n = some (r, o, i, M)) :
    ∃ b sz, env.regions[r]? = some (b, sz) ∧ (i.eval env).toNat ≤ M ∧
      o + (i.eval env).toNat + n ≤ sz ∧
      x.eval env + y.eval env + BitVec.ofInt 64 d =
        b + BitVec.ofNat 64 (o + (i.eval env).toNat) := by
  unfold SState.accessIdx2 at h
  split at h
  · rename_i res hres
    cases h
    obtain ⟨rfl, b, sz, hb, hM, hle, he⟩ := hm.accessIdxAt hres
    refine ⟨b, sz, hb, hM, hle, ?_⟩
    rw [← he, BitVec.add_assoc, BitVec.add_comm (y.eval env), ← BitVec.add_assoc]
  · obtain ⟨rfl, b, sz, hb, hM, hle, he⟩ := hm.accessIdxAt h
    refine ⟨b, sz, hb, hM, hle, ?_⟩
    rw [← he, BitVec.add_comm (x.eval env), BitVec.add_assoc, BitVec.add_comm (x.eval env),
      ← BitVec.add_assoc]

/-- An indexed access the executor places: its region, and its address for the index's value. -/
theorem Match.accessIdx (hm : Match env S m) {a i : Sym} {n r o M : Nat}
    (h : S.accessIdx a n = some (r, o, i, M)) :
    ∃ b sz, env.regions[r]? = some (b, sz) ∧ (i.eval env).toNat ≤ M ∧
      o + (i.eval env).toNat + n ≤ sz ∧
      a.eval env = b + BitVec.ofNat 64 (o + (i.eval env).toNat) := by
  unfold SState.accessIdx at h
  split at h
  · rename_i x y c
    obtain ⟨b, sz, hb, hM, hle, he⟩ := hm.accessIdx2 h
    refine ⟨b, sz, hb, hM, hle, ?_⟩
    rw [← he]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, ofInt_litInt]
  · rename_i x y _
    obtain ⟨b, sz, hb, hM, hle, he⟩ := hm.accessIdx2 h
    refine ⟨b, sz, hb, hM, hle, ?_⟩
    rw [← he]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  · cases h

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
theorem ofInt_toInt_int64 (a : Int64) : BitVec.ofInt 64 a.toInt = a.toBitVec := by
  rw [Int64.toInt, BitVec.ofInt_toInt]

theorem eval_mul_lit (v : Sym) (c : Nat) :
    (mkBin .mul .W64 v (.lit c)).eval env = v.eval env * BitVec.ofNat 64 c := by
  rw [eval_mkBin]
  simp only [BinOp.apply, low_W64, ext_W64, Sym.eval]

omit [Labels] in
theorem ofInt_rip (U L : Int64) :
    (BitVec.ofInt 64 (U.toInt + 0 + (L - U).toInt)).zeroExtend 64 = L.toBitVec := by
  rw [Int.add_zero, BitVec.ofInt_add, ofInt_toInt_int64, ofInt_toInt_int64, Int64.toBitVec_sub,
    BitVec.add_comm, BitVec.sub_add_cancel]
  exact BitVec.setWidth_eq _

omit [Labels] in
theorem ofInt_addr (B I : Int) (k : Int64) (b i : BitVec 64) (hB : BitVec.ofInt 64 B = b)
    (hI : BitVec.ofInt 64 I = i) :
    (BitVec.ofInt 64 (B + I + k.toInt)).zeroExtend 64 = b + i + k.toBitVec := by
  rw [BitVec.ofInt_add, BitVec.ofInt_add, hB, hI, ofInt_toInt_int64]
  exact BitVec.setWidth_eq _

omit [Labels] in
theorem ofInt_base (x : BitVec 64) : BitVec.ofInt 64 (x.take 64).toInt = x := by
  rw [BitVec.ofInt_toInt]
  simp [BitVec.take]

omit [Labels] in
theorem ofInt_index (x : BitVec 64) (n : Nat) :
    BitVec.ofInt 64 ((x.take 64).toInt * (n : Int)) = x * BitVec.ofNat 64 n := by
  rw [BitVec.ofInt_mul, ofInt_base, BitVec.ofInt_natCast]

/-- Symbolic constants denote exactly Kraken's constants, including symbolic GOT addresses. -/
theorem eval_constSym {c : ConstExpr} {x : Sym} (h : constSym c = some x)
    (p : Std.Rco Int64) : x.eval env = (c.interp p).toBitVec := by
  cases c <;> cases h
  all_goals first | exact eval_lit_toNat env _ | rfl

/-- **An address operand is Kraken's** (64-bit addresses). -/
theorem Match.addr (hm : Match env S m) {a : AddrExpr} {x : Sym} (h : S.addr a = some x)
    (p : Std.Rco Int64) :
    (a.interp (address_size := ⟨.W64⟩) m.regs p).zeroExtend 64 = x.eval env := by
  obtain ⟨base, idx, disp⟩ := a
  unfold SState.addr at h
  dsimp only at h
  split at h
  · rename_i l
    split at h
    · cases h
      exact ofInt_rip p.upper (Labels.label l)
    · cases h
  · rename_i l
    split at h
    · cases h
      exact ofInt_rip p.upper (Labels.gotSlot l)
    · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨d, hd, b, hb, i, hi, rfl⟩ := h
    rw [eval_mkAdd64, eval_mkAdd64, eval_constSym hd p]
    have hI : ∀ I : Int, (∀ r sc, idx = some ⟨r, sc⟩ →
        I = ((m.regs.get64 r).take 64).toInt * (sc.bytes : Int)) → (idx = none → I = 0) →
        BitVec.ofInt 64 I = i.eval env := by
      intro I h1 h2
      cases idx with
      | none =>
        cases hi
        rw [h2 rfl]
        rfl
      | some ix =>
        obtain ⟨r, sc⟩ := ix
        cases hr : S.reg r with
        | none => simp [SState.indexSym, hr] at hi
        | some v =>
          simp only [SState.indexSym, hr, Option.map_some, Option.some.injEq] at hi
          subst hi
          rw [h1 r sc rfl, ofInt_index, eval_mul_lit, ← hm.regs r v hr]
    cases base with
    | none =>
      cases hb
      cases idx with
      | none => exact ofInt_addr _ _ (disp.interp p) _ _ rfl (hI _ nofun fun _ => rfl)
      | some ix =>
        exact ofInt_addr _ _ (disp.interp p) _ _ rfl (hI _ (fun _ _ h => by cases h; rfl) nofun)
    | some br =>
      cases br with
      | rip => cases hb
      | reg r =>
        have hB := (ofInt_base (m.regs.get64 r)).trans (hm.regs r b hb)
        cases idx with
        | none => exact ofInt_addr _ _ (disp.interp p) _ _ hB (hI _ nofun fun _ => rfl)
        | some ix =>
          exact ofInt_addr _ _ (disp.interp p) _ _ hB (hI _ (fun _ _ h => by cases h; rfl) nofun)

/-- Add a symbolic description of initial bytes without changing the actual write footprint.
For a GOT slot use `v := .label target` and an alias `(.gotSlot target, r, off)`. -/
theorem Match.withKnownBytes (hm : Match env S m) {r off n : Nat} {v : Sym}
    (hbytes : ∀ i < n, env.mem0.get? (env.base r + BitVec.ofNat 64 (off + i)) =
      some (byteOf (v.eval env) i)) :
    Match env (S.withKnownBytes r off n v) m := by
  refine { hm with known := ?_ }
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hbytes
  · exact hm.known w hw

/-- Descriptions of initial memory evaluate to that memory, byte by byte. -/
theorem memByte_known {known : List Write}
    (hknown : ∀ w ∈ known, ∀ i < w.n,
      env.mem0.get? (env.base w.r + BitVec.ofNat 64 (w.off + i)) =
        some (byteOf (w.v.eval env) i))
    {r : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz)) (i : Nat) :
    memByte env known r b i = env.mem0.get? (b + BitVec.ofNat 64 i) := by
  induction known with
  | nil => rfl
  | cons w ws ih =>
    unfold memByte
    rw [findWrite_cons]
    by_cases hw : w.r = r ∧ w.off ≤ i ∧ i < w.off + w.n
    · rw [ite_pos hw]
      have he := hknown w List.mem_cons_self (i - w.off) (by omega)
      have hbase : env.base w.r = b := Env.base_eq (hw.1 ▸ hb)
      have hoff : w.off + (i - w.off) = i := by omega
      simpa only [hbase, hoff] using he.symm
    · rw [ite_neg hw]
      exact ih (fun w' hw' => hknown w' (List.mem_cons_of_mem _ hw'))

end

end NativeRustcX64.Sym
