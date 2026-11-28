module

public import NativeRustcX64.Sym.Flags
public import NativeRustcX64.Sym.Slots

/-!
# Operands of instructions

`OpOk env op`: from any state the symbolic step of `op` describes, Kraken's semantics of `op`
(64-bit addresses) ends where the step says. The operands the executor reads and writes are
Kraken's: register writes of each width (`Match.setR`), register or memory operands
(`Match.readRM`, `Match.readOp`, `Match.writeDst`), loads and stores at an address (`load_All`,
`store_All`), shift counts (`Match.count`).
-/

namespace NativeRustcX64.Sym

public section

/-- **An instruction is sound**: from a state `S` describes, Kraken's semantics of `op` (64-bit
addresses) ends in a state the symbolic step's `S'` describes, at the pc its exit says; a call
pushes `env.ret`, which must be the address after it. -/
@[expose] def OpOk [Labels] (env : Env) {w : Width} (op : Operation w) : Prop :=
  ∀ (S S' : SState) (x : Exit) (m : MachineData) (p : Std.Rco Int64), env.WF → Match env S m →
    stepOp op S = some (S', x) → (∀ l, x = .call l → env.ret = p.upper.toBitVec) →
    (op.interp p m (fun m' => .done ⟨m', p.upper⟩)
      (fun a m' => .done ⟨m', a⟩)).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st)

/-- A step that falls through to a state matching `m'`. -/
theorem done_fall [Labels] {env : Env} {S' : SState} {m' : MachineData} {p : Std.Rco Int64}
    (h : Match env S' m') :
    (Effects.done ⟨m', p.upper⟩).All (fun st => Match env S' st.data ∧ PcOk env .fall p.upper st) :=
  ⟨h, rfl⟩

/-- A choice Kraken leaves undefined unless `c`: whatever is chosen, the continuation holds. -/
theorem all_choice {c : Prop} [Decidable c] {b : Bool} {k : Bool → Effects}
    {post : MachineState → Prop} (h : ∀ v, (k v).All post) :
    (if c then k b else undefined k).All post := by
  split
  · exact h b
  · exact h

theorem ofInt_toNat_low (w : Width) (x : BitVec 64) :
    BitVec.ofInt w.bits (x.toNat : Int) = low w x := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  rfl

theorem ext_low_of_lt (w : Width) {x : BitVec 64} (h : x.toNat < 2 ^ (8 * w.bytes)) :
    ext w (low w x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ext, toNat_low, bits_eq]
  exact Nat.mod_eq_of_lt h

/-- The bytes Kraken stores for a value of width `w`. -/
theorem store_bytes (w : Width) (y : BitVec 64) :
    ∀ t < w.bytes, (Int.toBytes w.bytes (low w y).toInt)[t]? = some (byteOf y t) := by
  intro t ht
  cases w <;> exact toBytes_setWidth y _ t ht

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-! ## Registers -/

/-- **A register write of width `w` is Kraken's**, of a value already zero-extended. -/
theorem Match.setR (hm : Match env S m) {w : Width} {r : Reg w} {u : Sym} {S' : SState}
    (h : S.setR r u = some S') {x : w.type} (hu : u.eval env = ext w x) :
    Match env S' (m.setReg r x) := by
  cases r with
  | low r w =>
    cases w with
    | W64 =>
      cases h
      exact hm.set64 r fun _ h' => by cases h'; rw [hu, ext_W64]
    | W32 =>
      cases h
      exact hm.set64 r fun _ h' => by cases h'; exact hu
    | W8 =>
      cases h
      refine hm.set64 r fun u' h' => ?_
      obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp h'
      rw [eval_mkBin]
      simp only [BinOp.apply]
      rw [← hm.regs r old hold, hu, low_ext]
    | W16 =>
      cases h
      refine hm.set64 r fun u' h' => ?_
      obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp h'
      rw [eval_mkBin]
      simp only [BinOp.apply]
      rw [← hm.regs r old hold, hu, low_ext]
  | _ => cases h

/-! ## Memory -/

/-- A load Kraken performs where the symbolic executor loads `v`. -/
theorem load_All (hm : Match env S m) (hwf : env.WF) {w : Width} {A : BitVec 64} {a v : Sym}
    (hA : a.eval env = A) (hv : S.loadAt a w.bytes = some v)
    {ret : w.type → MachineData → Effects} {post : MachineState → Prop}
    (hret : (v.eval env).toNat < 2 ^ (8 * w.bytes) → (ret (low w (v.eval env)) m).All post) :
    (m.load A w ret).All post := by
  obtain ⟨hl, hlt⟩ := hm.loadAt hwf hv (bytes_le w)
  rw [hA] at hl
  unfold MachineData.load
  rw [Effects.All_require_read_access, hl]
  show (ret (BitVec.ofInt w.bits ((v.eval env).toNat : Int)) m).All post
  rw [ofInt_toNat_low]
  exact hret hlt

/-- A store Kraken performs where the symbolic executor stores `u`. -/
theorem store_All (hm : Match env S m) (hwf : env.WF) {w : Width} {A : BitVec 64} {a u : Sym}
    {S' : SState} (hA : a.eval env = A) (hs : S.storeAt a w.bytes u = some S') {x : w.type}
    (hx : low w (u.eval env) = x) {ret : MachineData → Effects} {post : MachineState → Prop}
    (hret : ∀ m', Match env S' m' → (ret m').All post) :
    (m.store A x ret).All post := by
  obtain ⟨hl, hm'⟩ := hm.storeAt hwf hs (bytes_pos w) (bytes_le w) x.toInt
    (hx ▸ store_bytes w (u.eval env))
  rw [hA] at hl hm'
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hl
  unfold MachineData.store
  rw [Effects.All_require_write_access, hy]
  exact hret _ hm'

omit [Labels] in
/-- After a store at a constant offset, a load of the same bytes reads the stored value. -/
theorem SState.storeAt_loadOne {S S' : SState} {a u : Sym} {n : Nat}
    (h : S.storeAt a n u = some S') (hs : S.slots a n = none) (hn : 0 < n) :
    S'.loadOne a n = some (mkBytes u 0 n) := by
  unfold SState.storeAt at h
  cases hacc : S.access a n with
  | none => rw [hacc, hs] at h; cases h
  | some ro =>
    obtain ⟨r, o⟩ := ro
    rw [hacc] at h
    cases h
    have : (S.store r o n u).access a n = some (r, o) := hacc
    unfold SState.loadOne
    rw [this]
    show some (loadSym (⟨r, o, n, u⟩ :: _) r o n) = _
    unfold loadSym
    rw [firstOverlap_cons, ite_pos ⟨rfl, by dsimp only; omega, by dsimp only; omega⟩]
    simp

/-! ## Operands -/

/-- **A register or memory operand is Kraken's**: its value is the low `w` bits of the symbolic
value read. -/
theorem Match.readRM (hm : Match env S m) (hwf : env.WF) {w : Width} {o : RegOrMem w} {v : Sym}
    (h : S.readRM o = some v) (p : Std.Rco Int64) {ret : w.type → MachineData → Effects}
    {post : MachineState → Prop} (hret : (ret (low w (v.eval env)) m).All post) :
    (o.interp m p ret).All post := by
  cases o with
  | reg r =>
    show (ret (m.regs.get r) m).All post
    rw [hm.getR h]
    exact hret
  | mem a =>
    simp only [SState.readRM, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨xa, hxa, hv⟩ := h
    exact load_All hm hwf (hm.addr hxa p).symm hv fun _ => hret

/-- **An operand is Kraken's**: its value is the low `w` bits of the symbolic value read. -/
theorem Match.readOp (hm : Match env S m) (hwf : env.WF) {w : Width} {o : Operand w} {v : Sym}
    (h : S.readOp o = some v) (p : Std.Rco Int64) {ret : w.type → MachineData → Effects}
    {post : MachineState → Prop} (hret : (ret (low w (v.eval env)) m).All post) :
    (o.interp m p ret).All post := by
  cases o with
  | regOrMem o => exact hm.readRM hwf h p hret
  | imm c =>
    have hc := eval_constSym (env := env) h p
    show (ret ((c.interp p).toBitVec.truncate _) m).All post
    rw [← hc]
    exact hret

/-- **A write to a destination is Kraken's**, of a value already zero-extended. -/
theorem Match.writeDst (hm : Match env S m) (hwf : env.WF) {w : Width} {d : Dst w} {u : Sym}
    {S' : SState} (h : S.writeDst d u = some S') {x : w.type} (hu : u.eval env = ext w x)
    (p : Std.Rco Int64) {next : MachineData → Effects} {post : MachineState → Prop}
    (hnext : ∀ m', Match env S' m' → (next m').All post) :
    (m.set d x p next).All post := by
  cases d with
  | reg r => exact hnext _ (hm.setR h hu)
  | mem a =>
    simp only [SState.writeDst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨xa, hxa, hs⟩ := h
    exact store_All hm hwf (hm.addr hxa p).symm hs (by rw [hu, low_ext]) hnext

/-- **A shift count is Kraken's.** -/
theorem Match.count (hm : Match env S m) {c : ShiftCountExpr} {n : Sym} (h : S.count c = some n)
    (p : Std.Rco Int64) (w : Width) : c.interpMasked m p w = shiftCount w (n.eval env) := by
  have hv : c.interp m p = low .W8 (n.eval env) := by
    cases c with
    | cl =>
      rw [← hm.regs .rcx n h]
      exact take_eq_low .W8 _
    | imm8 v =>
      simp only [SState.count, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨k, hk, rfl⟩ := h
      cases v <;> cases hk
      rw [eval_lit_toNat]
      exact take_eq_low .W8 _
  show (c.interp m p).toNat &&& _ = _
  rw [hv]
  cases w <;> rfl

/-- Bit offsets have Kraken's modulo-width semantics, including low-byte immediates. -/
theorem Match.bitOffset (hm : Match env S m) {w : Width} {o : BitOffset w} {v : Sym}
    (h : S.bitOffset o = some v) (p : Std.Rco Int64)
    {ret : Nat → Effects} {post : MachineState → Prop}
    (hret : (ret ((low w (v.eval env)).toNat % w.bits)).All post) :
    (o.interp m p ret).All post := by
  cases o with
  | reg r =>
    show (ret ((m.regs.get r).toNat % w.bits)).All post
    rw [hm.getR h]
    exact hret
  | imm c =>
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    have he : (low w ((truncTo .W8 u).eval env)).toNat =
        ((c.interp p).toBitVec.take 8).toNat := by
      rw [eval_truncTo, eval_constSym hu p, take_eq_low .W8]
      cases w <;> simp only [toNat_low, toNat_ext, Width.bits] <;> omega
    rw [he] at hret
    exact hret

end

end NativeRustcX64.Sym
