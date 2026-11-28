module

public import NativeRustcArm.Sym.Operand

/-!
# Loads and stores are sound

`OpOk` for `LDR`/`STR`, their byte and halfword forms, the unscaled forms (`LDUR`, ...) and the
pairs `LDP`/`STP`: one lemma per symbolic step (`Step.load`, `Step.store`, ...) from the value
Kraken loads or stores, then one per `Operation` constructor.
-/

namespace NativeRustcArm.Sym

public section

variable [Labels] {env : Env} {S S' : SState} {x : Exit} {m : MachineData} {w : RegWidth}

/-- A load Kraken performs where the symbolic executor loads `v`. -/
theorem load_All {m₁ : MachineData} {A : BitVec 64} (mw : MemWidth) {S₁ : SState} {a v : Sym}
    (hm₁ : Match env S₁ m₁) (hwf : env.WF) (hA : a.eval env = A) (hv : S₁.loadAt a mw.bytes = some v)
    (hmw : mw.bytes ≤ 8) {ret : mw.type → MachineData → Effects} {post : MachineState → Prop}
    (hret : ∀ y : BitVec 64, y = v.eval env → y.toNat < 2 ^ (8 * mw.bytes) →
      (ret (BitVec.ofInt mw.bits (y.toNat : Int)) m₁).All post) :
    (m₁.load A mw ret).All post := by
  obtain ⟨hl, hlt⟩ := hm₁.loadAt hwf hv hmw
  rw [hA] at hl
  show (Effects.require_read_access A mw fun _ => match Mem.loadInt m₁.dmem A mw.bytes with
    | some i => ret (.ofInt _ i) m₁
    | none => _).All post
  simp only [Effects.All]
  rw [hl]
  exact hret _ rfl hlt

/-- A store Kraken performs where the symbolic executor stores `u`. -/
theorem store_All {m₁ : MachineData} {A : BitVec 64} (mw : MemWidth) {S₁ S₂ : SState} {a u : Sym}
    (hm₁ : Match env S₁ m₁) (hwf : env.WF) (hA : a.eval env = A)
    (hs : S₁.storeAt a mw.bytes u = some S₂) (hmw0 : 0 < mw.bytes) (hmw : mw.bytes ≤ 8)
    (val : mw.type) (hval : ∀ t < mw.bytes, (Int.toBytes mw.bytes val.toInt)[t]? =
      some (byteOf (u.eval env) t))
    {ret : MachineData → Effects} {post : MachineState → Prop}
    (hret : ∀ m₂, Match env S₂ m₂ → (ret m₂).All post) :
    (m₁.store A val ret).All post := by
  obtain ⟨hl, hm₂⟩ := hm₁.storeAt hwf hs hmw0 hmw val.toInt hval
  rw [hA] at hl hm₂
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hl
  show (Effects.require_write_access A mw fun _ => match Mem.loadInt m₁.dmem A mw.bytes with
    | some _ => ret { m₁ with dmem := Mem.storeInt m₁.dmem A mw.bytes val.toInt }
    | none => _).All post
  simp only [Effects.All]
  rw [hy]
  exact hret _ hm₂

/-! ## Step families -/

theorem load_ok (mw : MemWidth) (hmw : mw.bytes ≤ 8) (conv : mw.type → w.type)
    (hconv : ∀ y : BitVec 64, y.toNat < 2 ^ (8 * mw.bytes) →
      ext w (conv (BitVec.ofInt mw.bits (y.toNat : Int))) = y)
    {dst : RegOrZr w} {ae : AddrExpr} (hwf : env.WF) (hm : Match env S m)
    (h : Step.load mw dst ae S = some (S', x)) (p : Std.Rco Int64) :
    (ae.interpLoad (w := mw) m p (fun val s => s.setRegOrZr dst (conv val)
      (fun m' => .done ⟨m', p.upper⟩))).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  unfold Step.load at h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨a, S₁⟩, hA, v, hv, rfl, rfl⟩ := h
    unfold AddrExpr.interpLoad
    rw [hm.checkSp hc]
    obtain ⟨haddr, hm₁, -⟩ := hm.addr hA p
    cases he : ae.eval m p with
    | mk A m₁ =>
      rw [he] at haddr hm₁
      exact load_All mw hm₁ hwf haddr.symm hv hmw fun y hy hlt =>
        done_fall (hm₁.setZr dst (by rw [hconv y hlt, hy]))
  · cases h

theorem uload_ok (mw : MemWidth) (hmw : mw.bytes ≤ 8) (conv : mw.type → w.type)
    (hconv : ∀ y : BitVec 64, y.toNat < 2 ^ (8 * mw.bytes) →
      ext w (conv (BitVec.ofInt mw.bits (y.toNat : Int))) = y)
    {dst : RegOrZr w} {ua : UnscaledAddrExpr} (hwf : env.WF) (hm : Match env S m)
    (h : Step.uload mw dst ua S = some (S', x)) (p : Std.Rco Int64) :
    (ua.interpLoad (w := mw) m p (fun val s => s.setRegOrZr dst (conv val)
      (fun m' => .done ⟨m', p.upper⟩))).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  unfold Step.uload at h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨a, hA, v, hv, rfl, rfl⟩ := h
    unfold UnscaledAddrExpr.interpLoad
    rw [hm.checkSpU hc]
    exact load_All mw hm hwf (hm.uaddr hA p).symm hv hmw fun y hy hlt =>
      done_fall (hm.setZr dst (by rw [hconv y hlt, hy]))
  · cases h

theorem store_ok (mw : MemWidth) (hmw0 : 0 < mw.bytes) (hmw : mw.bytes ≤ 8) (conv : w.type → mw.type)
    (hconv : ∀ y : BitVec 64, ∀ t < mw.bytes,
      (Int.toBytes mw.bytes (conv (low w y)).toInt)[t]? = some (byteOf y t))
    {src : RegOrZr w} {ae : AddrExpr} (hwf : env.WF) (hm : Match env S m)
    (h : Step.store mw src ae S = some (S', x)) (p : Std.Rco Int64) :
    (ae.interpStore (w := mw) m p (conv (m.regs.getRegOrZr src))
      (fun m' => .done ⟨m', p.upper⟩)).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  unfold Step.store at h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨u, hu, ⟨a, S₁⟩, hA, S₂, hs, rfl, rfl⟩ := h
    unfold AddrExpr.interpStore
    rw [hm.checkSp hc]
    obtain ⟨haddr, hm₁, -⟩ := hm.addr hA p
    cases he : ae.eval m p with
    | mk A m₁ =>
      rw [he] at haddr hm₁
      rw [hm.getZr hu]
      exact store_All mw hm₁ hwf haddr.symm hs hmw0 hmw _ (hconv _) fun m₂ hm₂ =>
        done_fall hm₂
  · cases h

theorem ustore_ok (mw : MemWidth) (hmw0 : 0 < mw.bytes) (hmw : mw.bytes ≤ 8)
    (conv : w.type → mw.type)
    (hconv : ∀ y : BitVec 64, ∀ t < mw.bytes,
      (Int.toBytes mw.bytes (conv (low w y)).toInt)[t]? = some (byteOf y t))
    {src : RegOrZr w} {ua : UnscaledAddrExpr} (hwf : env.WF) (hm : Match env S m)
    (h : Step.ustore mw src ua S = some (S', x)) (p : Std.Rco Int64) :
    (ua.interpStore (w := mw) m p (conv (m.regs.getRegOrZr src))
      (fun m' => .done ⟨m', p.upper⟩)).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  unfold Step.ustore at h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨u, hu, a, hA, S₂, hs, rfl, rfl⟩ := h
    unfold UnscaledAddrExpr.interpStore
    rw [hm.checkSpU hc, hm.getZr hu]
    exact store_All mw hm hwf (hm.uaddr hA p).symm hs hmw0 hmw _ (hconv _) fun m₂ hm₂ =>
      done_fall hm₂
  · cases h

theorem eval_addBytes (a : Sym) (n : Nat) :
    (mkBin .add .W64 a (.lit n)).eval env = a.eval env + BitVec.ofNat 64 n := by
  rw [eval_mkBin]
  simp only [BinOp.apply, Sym.eval, low_W64, ext_W64]

theorem ldp_ok {dst1 dst2 : RegOrZr w} {ae : AddrExpr} (hwf : env.WF) (hm : Match env S m)
    (h : Step.ldp dst1 dst2 ae S = some (S', x)) (p : Std.Rco Int64) :
    (ae.checkSPAlignment m (fun _ =>
      let (addr, s') := ae.eval m p
      s'.load addr w (fun val1 s'' =>
        s''.load (addr + w.bytesv) w (fun val2 s''' =>
          s'''.setRegOrZr dst1 val1 (fun s'''' =>
            s''''.setRegOrZr dst2 val2 (fun m' => .done ⟨m', p.upper⟩)))))).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  unfold Step.ldp at h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨a, S₁⟩, hA, v₁, hv₁, v₂, hv₂, rfl, rfl⟩ := h
    rw [hm.checkSp hc]
    obtain ⟨haddr, hm₁, -⟩ := hm.addr hA p
    cases he : ae.eval m p with
    | mk A m₁ =>
      rw [he] at haddr hm₁
      have hmw : (w : MemWidth).bytes ≤ 8 := by cases w <;> decide
      refine load_All (w : MemWidth) hm₁ hwf haddr.symm hv₁ hmw fun y₁ hy₁ hlt₁ => ?_
      refine load_All (w : MemWidth) hm₁ hwf (by rw [eval_addBytes, show (a, S₁).1.eval env = A from haddr.symm]) hv₂ hmw
        fun y₂ hy₂ hlt₂ => ?_
      exact done_fall ((hm₁.setZr dst1 (by rw [ext_ofInt_toNat w y₁ hlt₁, hy₁])).setZr dst2
        (by rw [ext_ofInt_toNat w y₂ hlt₂, hy₂]))
  · cases h

theorem stp_ok {src1 src2 : RegOrZr w} {ae : AddrExpr} (hwf : env.WF) (hm : Match env S m)
    (h : Step.stp src1 src2 ae S = some (S', x)) (p : Std.Rco Int64) :
    (ae.checkSPAlignment m (fun _ =>
      let val1 := m.regs.getRegOrZr src1
      let val2 := m.regs.getRegOrZr src2
      let (addr, s') := ae.eval m p
      s'.store addr val1 (fun s'' =>
        s''.store (addr + w.bytesv) val2 (fun m' => .done ⟨m', p.upper⟩)))).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  unfold Step.stp at h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨u₁, hu₁, u₂, hu₂, ⟨a, S₁⟩, hA, S₂, hs₂, S₃, hs₃, rfl, rfl⟩ := h
    rw [hm.checkSp hc]
    obtain ⟨haddr, hm₁, -⟩ := hm.addr hA p
    cases he : ae.eval m p with
    | mk A m₁ =>
      rw [he] at haddr hm₁
      have hmw0 : 0 < (w : MemWidth).bytes := by cases w <;> decide
      have hmw : (w : MemWidth).bytes ≤ 8 := by cases w <;> decide
      rw [hm.getZr hu₁, hm.getZr hu₂]
      refine store_All (w : MemWidth) hm₁ hwf haddr.symm hs₂ hmw0 hmw _ (store_bytes w _)
        fun m₂ hm₂ => ?_
      exact store_All (w : MemWidth) hm₂ hwf (by rw [eval_addBytes, show (a, S₁).1.eval env = A from haddr.symm]) hs₃ hmw0 hmw _
        (store_bytes w _) fun m₃ hm₃ => done_fall hm₃
  · cases h

/-! ## Instructions -/

theorem ok_LDR (dst : RegOrZr w) (ae : AddrExpr) : OpOk env (.LDR dst (.addr ae)) :=
  fun _ _ _ _ p hwf hm h => load_ok (w : MemWidth) (by cases w <;> decide) id
    (fun y hy => ext_ofInt_toNat w y hy) hwf hm h p

theorem ok_LDRB (dst : RegOrZr .W32) (ae : AddrExpr) : OpOk env (.LDRB dst ae) :=
  fun _ _ _ _ p hwf hm h => load_ok .W8 (by decide) (·.zeroExtend 32)
    (fun y hy => ext_ofInt_toNat_narrow 8 (by decide) y hy) hwf hm h p

theorem ok_LDRH (dst : RegOrZr .W32) (ae : AddrExpr) : OpOk env (.LDRH dst ae) :=
  fun _ _ _ _ p hwf hm h => load_ok .W16 (by decide) (·.zeroExtend 32)
    (fun y hy => ext_ofInt_toNat_narrow 16 (by decide) y hy) hwf hm h p

theorem ok_LDUR (dst : RegOrZr w) (ua : UnscaledAddrExpr) : OpOk env (.LDUR dst ua) :=
  fun _ _ _ _ p hwf hm h => uload_ok (w : MemWidth) (by cases w <;> decide) id
    (fun y hy => ext_ofInt_toNat w y hy) hwf hm h p

theorem ok_LDURB (dst : RegOrZr .W32) (ua : UnscaledAddrExpr) : OpOk env (.LDURB dst ua) :=
  fun _ _ _ _ p hwf hm h => uload_ok .W8 (by decide) (·.zeroExtend 32)
    (fun y hy => ext_ofInt_toNat_narrow 8 (by decide) y hy) hwf hm h p

theorem ok_LDURH (dst : RegOrZr .W32) (ua : UnscaledAddrExpr) : OpOk env (.LDURH dst ua) :=
  fun _ _ _ _ p hwf hm h => uload_ok .W16 (by decide) (·.zeroExtend 32)
    (fun y hy => ext_ofInt_toNat_narrow 16 (by decide) y hy) hwf hm h p

theorem ok_STR (src : RegOrZr w) (ae : AddrExpr) : OpOk env (.STR src ae) :=
  fun _ _ _ _ p hwf hm h => store_ok (w : MemWidth) (by cases w <;> decide) (by cases w <;> decide)
    id (fun y => store_bytes w y) hwf hm h p

theorem ok_STRB (src : RegOrZr .W32) (ae : AddrExpr) : OpOk env (.STRB src ae) :=
  fun _ _ _ _ p hwf hm h => store_ok .W8 (by decide) (by decide) (·.take 8)
    (fun y => store_bytes_narrow 1 (by decide) y) hwf hm h p

theorem ok_STRH (src : RegOrZr .W32) (ae : AddrExpr) : OpOk env (.STRH src ae) :=
  fun _ _ _ _ p hwf hm h => store_ok .W16 (by decide) (by decide) (·.take 16)
    (fun y => store_bytes_narrow 2 (by decide) y) hwf hm h p

theorem ok_STUR (src : RegOrZr w) (ua : UnscaledAddrExpr) : OpOk env (.STUR src ua) :=
  fun _ _ _ _ p hwf hm h => ustore_ok (w : MemWidth) (by cases w <;> decide)
    (by cases w <;> decide) id (fun y => store_bytes w y) hwf hm h p

theorem ok_STURB (src : RegOrZr .W32) (ua : UnscaledAddrExpr) : OpOk env (.STURB src ua) :=
  fun _ _ _ _ p hwf hm h => ustore_ok .W8 (by decide) (by decide) (·.take 8)
    (fun y => store_bytes_narrow 1 (by decide) y) hwf hm h p

theorem ok_STURH (src : RegOrZr .W32) (ua : UnscaledAddrExpr) : OpOk env (.STURH src ua) :=
  fun _ _ _ _ p hwf hm h => ustore_ok .W16 (by decide) (by decide) (·.take 16)
    (fun y => store_bytes_narrow 2 (by decide) y) hwf hm h p

theorem ok_LDP (dst1 dst2 : RegOrZr w) (ae : AddrExpr) : OpOk env (.LDP dst1 dst2 ae) :=
  fun _ _ _ _ p hwf hm h => ldp_ok hwf hm h p

theorem ok_STP (src1 src2 : RegOrZr w) (ae : AddrExpr) : OpOk env (.STP src1 src2 ae) :=
  fun _ _ _ _ p hwf hm h => stp_ok hwf hm h p

end

end NativeRustcArm.Sym
