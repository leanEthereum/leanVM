module

public import NativeRustcVmArm.Bus.BytecodeShare.Common

/-!
# `bytecode_share`: the point's copy and the result

From `b12` on, the check passed: `bytecode_low` goes to the point's first slots, two elements a
turn (`b18`, the head `.LBytecodeShare_12`), then the odd one (`b21`), the slot point after them
and the result to the output (`b22`), then the epilogue. `Cp j`: the first `j` elements copied,
nothing else changed since `b12` but the point.

- `copied_word`: a word a block copied from one region to another.
- `finish`: `b22` and the epilogue.
- `pair`: a turn of the pair loop.
- `copy_spec`: from `b12` to the return.
-/

namespace NativeRustcVmArm.Bus.BytecodeShare

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BytecodeShare
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr

public section

/-- **A word a block copied**: region `rd`'s eight bytes at `od` are region `rs`'s at `os`. -/
theorem copied_word [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m rs) S m') {rd rr od os : Nat} {bd bs : BitVec 64}
    {szd szs : Nat} (hbd : rs[rd]? = some (bd, szd)) (hbs : rs[rr]? = some (bs, szs))
    (hd : od + 8 ≤ szd) (hmap : NativeRustcVm.Mapped m.dmem (bs + BitVec.ofNat 64 os) 8)
    (hw : ∀ i < 8, findWrite rd (od + i) S.mem = some (.load rr os 8, i)) :
    ∀ i < 8, m'.dmem.get? (bd + BitVec.ofNat 64 (od + i)) =
      m.dmem.get? (bs + BitVec.ofNat 64 (os + i)) := by
  have h1 := Bus.wordAt_write hm hbd hd hw
  have he : (Sym.load rr os 8).eval (Env.ofMachine m rs) =
      (NativeRustcVm.wordOf m.dmem (bs + BitVec.ofNat 64 os)).toBitVec := by
    show (Env.ofMachine m rs).load rr os 8 = _
    rw [load_eq_wordOf, Env.base_ofMachine m rs _ hbs]
    rfl
  rw [he, UInt64.ofBitVec_toBitVec] at h1
  have h2 := NativeRustcVm.wordAt_of_mapped hmap
  intro i hi
  have hi' : i < (NativeRustcVm.wordBytes (NativeRustcVm.wordOf m.dmem
      (bs + BitVec.ofNat 64 os))).length := by rw [NativeRustcVm.length_wordBytes]; exact hi
  rw [← NativeRustcVm.addr_add_add, ← NativeRustcVm.addr_add_add, h1 i hi', h2 i hi']

/-- Bytes moved from `a` to `b` carry the elements there. -/
theorem ewsAt_transfer {d d' : Mem 64} {a b : BitVec 64} {xs : List EW}
    (htr : ∀ i < 16 * xs.length, d'.get? (b + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i))
    (h : NativeRustcVm.EWsAt d a xs) : NativeRustcVm.EWsAt d' b xs := fun i hi ↦ by
  have := hi
  rw [NativeRustcVm.length_ewsBytes] at this
  rw [htr i this]
  exact h i hi

/-- An address inside `n` bytes from `a` that do not wrap. -/
theorem toNat_in {a : BitVec 64} {n o : Nat} (h : NoWrap a n) (ho : o < n) :
    (a + BitVec.ofNat 64 o).toNat = a.toNat + o :=
  NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at h; omega)

theorem kept_trans {d1 d2 d3 : DataMem} (h1 : Kept d1 d2) (h2 : Kept d2 d3) : Kept d1 d3 :=
  fun p hp ↦ h2 p (h1 p hp)

/-- `len & 62` for a length below `64`. -/
theorem and62 (x : UInt64) (h : x.toNat < 64) : (x.toBitVec &&& 62#64).toNat = x.toNat - x.toNat % 2 := by
  have : ∀ y : Fin 64, ((BitVec.ofNat 64 y.val) &&& 62#64).toNat = y.val - y.val % 2 := by
    decide +kernel
  have e := this ⟨x.toNat, h⟩
  simp only at e
  rw [show BitVec.ofNat 64 x.toNat = x.toBitVec from by simp] at e
  exact e

/-- `8 | (j << 4)` for `j` below `64`. -/
theorem orr8 (x : BitVec 64) (h : x.toNat < 64) :
    (8#64 ||| (x <<< 4)) = BitVec.ofNat 64 (16 * x.toNat + 8) := by
  have : ∀ y : Fin 64, (8#64 ||| (BitVec.ofNat 64 y.val <<< 4)) = BitVec.ofNat 64 (16 * y.val + 8) := by
    decide +kernel
  have e := this ⟨x.toNat, h⟩
  simp only at e
  rw [show BitVec.ofNat 64 x.toNat = x from by simp] at e
  exact e

/-- The registers the copy keeps. -/
structure Regs (m0 : MachineData) (sh v : EW) (st : MachineData) : Prop where
  x19 : st.regs.getXReg .X19 = m0.regs.X0
  x20 : st.regs.getXReg .X20 = sh.c0
  x21 : st.regs.getXReg .X21 = sh.c1
  x22 : st.regs.getXReg .X22 = m0.regs.X4
  x23 : st.regs.getXReg .X23 = m0.regs.X5
  x24 : st.regs.getXReg .X24 = m0.regs.X3
  x25 : st.regs.getXReg .X25 = v.c0
  x26 : st.regs.getXReg .X26 = v.c1

/-- The registers through a block that leaves them alone. -/
theorem Regs.block [Labels] {m0 m m' : MachineData} {sh v : EW} {rs : List (BitVec 64 × Nat)}
    {S : SState} (h : Regs m0 sh v m) (hm : Match (Env.ofMachine m rs) S m')
    (hk : ([.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26] : List XReg).all
      (fun r ↦ S.reg r == some (.reg r)) = true) : Regs m0 sh v m' := by
  have k := fun r (hr : r ∈ ([.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26] : List XReg)) ↦
    mov_reg hm (beq_iff_eq.mp (List.all_eq_true.mp hk r hr))
  exact ⟨(k .X19 (by simp)).trans h.x19, (k .X20 (by simp)).trans h.x20,
    (k .X21 (by simp)).trans h.x21, (k .X22 (by simp)).trans h.x22,
    (k .X23 (by simp)).trans h.x23, (k .X24 (by simp)).trans h.x24,
    (k .X25 (by simp)).trans h.x25, (k .X26 (by simp)).trans h.x26⟩

/-- **`j` elements copied**, since the state `m` at `b12`. -/
structure Cp (m0 m : MachineData) (sh v : EW) (j : Nat) (st : MachineData) : Prop where
  fr : Fr m0 432 bytecodeShareStack slots keep (outsP m0) st
  regs : Regs m0 sh v st
  x8 : st.regs.getXReg .X8 = m0.regs.X4 + 4
  x9 : (st.regs.getXReg .X9).toBitVec =
    m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * m0.regs.X4.toNat)
  le : j ≤ m0.regs.X4.toNat
  cpy : ∀ i < 16 * j, st.dmem.get? (m0.regs.X5.toBitVec + BitVec.ofNat 64 i) =
    m0.dmem.get? (m0.regs.X3.toBitVec + BitVec.ofNat 64 i)
  same : SameOutside m.dmem st.dmem (InRange m0.regs.X5.toBitVec (16 * j))
  kept : Kept m.dmem st.dmem

variable {a : DecArea} {s0 s3 : TState} {m0 m : MachineData} {k : Nat} {sh v : EW}
  {sp : Array EW}

/-- The precondition's address facts the copy uses. -/
structure Addr (m0 : MachineData) : Prop where
  len : m0.regs.X4.toNat ≤ 63
  pnw : NoWrap m0.regs.X5.toBitVec ptBytes
  bnw : NoWrap m0.regs.X3.toBitVec (16 * m0.regs.X4.toNat)
  onw : NoWrap m0.regs.X0.toBitVec 48
  pst : Apart m0.regs.X5.toBitVec ptBytes (stackBelow m0 bytecodeShareStack) bytecodeShareStack
  bst : Apart m0.regs.X3.toBitVec (16 * m0.regs.X4.toNat) (stackBelow m0 bytecodeShareStack)
    bytecodeShareStack
  ost : Apart m0.regs.X0.toBitVec 48 (stackBelow m0 bytecodeShareStack) bytecodeShareStack
  pb : Apart m0.regs.X5.toBitVec ptBytes m0.regs.X3.toBitVec (16 * m0.regs.X4.toNat)
  op : Apart m0.regs.X0.toBitVec 48 m0.regs.X5.toBitVec ptBytes
  bt : Apart m0.regs.X3.toBitVec (16 * m0.regs.X4.toNat) m0.regs.X1.toBitVec tstateBytes
  sp : bytecodeShareStack ≤ m0.regs.SP.toNat

theorem addr_of [Labels] (h : BytecodeSharePre a s0 m0) : Addr m0 := by
  obtain ⟨hS, -, -, -, -, hlen, hbl, hoo, hpo, hop, hpb, -, hbt⟩ := pre_parts h
  exact ⟨hlen, hpo.2.1, hbl.1.2, hoo.2.1, hpo.2.2.2.2.1, hbl.2, hoo.2.2.2.2.1, hpb, hop, hbt,
    hS.2.1⟩

/-- A byte of `bytecode_low` is no output of the copy. -/
theorem b_not_outsP [Labels] (h : BytecodeSharePre a s0 m0) :
    ∀ j < 16 * m0.regs.X4.toNat, ¬outsP m0 (m0.regs.X3.toBitVec + BitVec.ofNat 64 j) := by
  intro j hj ho
  have A := addr_of h
  obtain ⟨-, -, htok, fp⟩ : _ ∧ _ ∧ TStateAt m0.dmem m0.regs.X1.toBitVec a s0 ∧ _ :=
    ⟨(pre_parts h).1, (pre_parts h).2.1, (pre_parts h).2.2.1, (pre_parts h).2.2.2.1⟩
  have hin : InRange m0.regs.X3.toBitVec (16 * m0.regs.X4.toNat)
      (m0.regs.X3.toBitVec + BitVec.ofNat 64 j) :=
    NativeRustcVm.inRange_add hj (by have := A.bnw; unfold NoWrap at this; omega)
  rcases ho with ho | ho
  · exact NativeRustcVm.Apart.not_inRange A.bt A.bnw htok.footprint.1.2 hin ho
  · exact NativeRustcVm.Apart.not_inRange A.pb.symm A.bnw A.pnw hin ho

/-- **Words a block copied**: region `rd`'s `8 nw` bytes at `od` are region `rr`'s at `os`. -/
theorem copy_words [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m rs) S m') {rd rr od os nw : Nat} {bd bs : BitVec 64}
    {szd szs : Nat} (hbd : rs[rd]? = some (bd, szd)) (hbs : rs[rr]? = some (bs, szs))
    (hd : od + 8 * nw ≤ szd) (hmap : NativeRustcVm.Mapped m.dmem (bs + BitVec.ofNat 64 os) (8 * nw))
    (hw : ∀ w < nw, ∀ i < 8, findWrite rd (od + 8 * w + i) S.mem =
      some (.load rr (os + 8 * w) 8, i)) :
    ∀ i < 8 * nw, m'.dmem.get? (bd + BitVec.ofNat 64 (od + i)) =
      m.dmem.get? (bs + BitVec.ofNat 64 (os + i)) := by
  intro i hi
  have hw8 : i / 8 < nw := by omega
  have e := copied_word hm (od := od + 8 * (i / 8)) (os := os + 8 * (i / 8)) hbd hbs (by omega)
    (fun j hj ↦ by
      have := hmap (8 * (i / 8) + j) (by omega)
      rw [NativeRustcVm.addr_add_add]
      rwa [NativeRustcVm.addr_add_add, ← Nat.add_assoc] at this) (hw _ hw8)
    (i % 8) (Nat.mod_lt _ (by omega))
  rw [show od + 8 * (i / 8) + i % 8 = od + i by omega,
    show os + 8 * (i / 8) + i % 8 = os + i by omega] at e
  exact e

/-- Where a block wrote: in a region other than the frame. -/
theorem written_out {env : Env} {S : SState} (hwf : env.WF)
    (hS : ∀ w ∈ S.mem, w.r ≠ 0 ∧ ∀ b sz, env.regions[w.r]? = some (b, sz) → w.off + w.n ≤ sz)
    {q : BitVec 64} (hq : Written env S q) :
    ∃ r b sz, r ≠ 0 ∧ env.regions[r]? = some (b, sz) ∧ InRange b sz q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
  obtain ⟨hr, hle⟩ := hS w hw
  have := hle b sz hb
  exact ⟨w.r, b, sz, hr, hb, by rw [Sym.inRange_iff (hwf.noWrap _ _ _ hb)]; omega⟩

/-- The writes of a block in a three-region environment, in regions 1 and 2, inside the
outputs. -/
theorem writeOk3 {m : MachineData} {vars : Nat → BitVec 64} {F : Nat}
    {slots : List (Nat × XReg)} {outs : BitVec 64 → Prop} {b0 b1 b2 : BitVec 64} {n1 n2 : Nat}
    (hout1 : ∀ i < n1, outs (b1 + BitVec.ofNat 64 i))
    (hout2 : ∀ i < n2, outs (b2 + BitVec.ofNat 64 i)) {w : Write}
    (h : (w.r = 1 ∧ w.off + w.n ≤ n1) ∨ (w.r = 2 ∧ w.off + w.n ≤ n2)) :
    WriteOk (Env.ofMachine m [(b0, F), (b1, n1), (b2, n2)] vars) F slots outs w := by
  refine .inr ⟨by omega, fun b sz hb ↦ ?_⟩
  change [(b0, F), (b1, n1), (b2, n2)][w.r]? = some (b, sz) at hb
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0] at hb <;>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb <;> obtain ⟨rfl, rfl⟩ := hb
  · exact ⟨h1, hout1⟩
  · exact ⟨h1, hout2⟩

/-- The writes of a three-region block, in regions 1 and 2. -/
theorem out3 {m : MachineData} {vars : Nat → BitVec 64} {F : Nat} {b0 b1 b2 : BitVec 64}
    {n1 n2 : Nat} {w : Write} (h : (w.r = 1 ∧ w.off + w.n ≤ n1) ∨ (w.r = 2 ∧ w.off + w.n ≤ n2)) :
    w.r ≠ 0 ∧ ∀ b sz, (Env.ofMachine m [(b0, F), (b1, n1), (b2, n2)] vars).regions[w.r]? =
      some (b, sz) → w.off + w.n ≤ sz := by
  refine ⟨by omega, fun b sz hb ↦ ?_⟩
  change [(b0, F), (b1, n1), (b2, n2)][w.r]? = some (b, sz) at hb
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0] at hb <;>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb <;> obtain ⟨rfl, rfl⟩ := hb <;> exact h1

/-- What a three-region block, writing regions 1 and 2, changed. -/
theorem same3 [Labels] {m m' : MachineData} {b0 b1 b2 : BitVec 64} {F n1 n2 : Nat}
    {S : SState} (hm : Match (Env.ofMachine m [(b0, F), (b1, n1), (b2, n2)]) S m')
    (hwf : (Env.ofMachine m [(b0, F), (b1, n1), (b2, n2)]).WF)
    (h : ∀ w ∈ S.mem, (w.r = 1 ∧ w.off + w.n ≤ n1) ∨ (w.r = 2 ∧ w.off + w.n ≤ n2)) :
    SameOutside m.dmem m'.dmem (fun q ↦ InRange b1 n1 q ∨ InRange b2 n2 q) :=
  NativeRustcVm.SameOutside.mono (hm.sameOutside hwf) fun q hq ↦ by
    obtain ⟨r, b, sz, hr, hb, hin⟩ := written_out hwf (fun w hw ↦ out3 (h w hw)) hq
    change [(b0, F), (b1, n1), (b2, n2)][r]? = some (b, sz) at hb
    match r, hb with
    | 1, hb =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact .inl hin
    | 2, hb =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact .inr hin
    | r + 3, hb => simp at hb

/-- `n` bytes inside `N` bytes from `a`. -/
theorem sub_range {d : DataMem} {a : BitVec 64} {N o n : Nat} (hm : NativeRustcVm.Mapped d a N)
    (hnw : NoWrap a N) (hon : o + n ≤ N) :
    NativeRustcVm.Mapped d (a + BitVec.ofNat 64 o) n ∧ NoWrap (a + BitVec.ofNat 64 o) n ∧
      (o < N → (a + BitVec.ofNat 64 o).toNat = a.toNat + o) := by
  refine ⟨fun i hi ↦ by rw [NativeRustcVm.addr_add_add]; exact hm _ (by omega), ?_,
    fun ho ↦ toNat_in hnw ho⟩
  unfold NoWrap at hnw ⊢
  rcases Nat.lt_or_ge o N with ho | ho
  · rw [toNat_in hnw ho]; omega
  · have : n = 0 := by omega
    subst this
    have := (a + BitVec.ofNat 64 o).isLt
    omega

theorem toUInt64_add4 (x : UInt64) : (x.toNat + 4).toUInt64 = x + 4 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  have : (4 : UInt64).toNat = 4 := rfl
  omega

variable [Host]

/-- **`b22` and the epilogue**: the slot point after the copied elements, the result. -/
theorem finish (hp : Placed code k) (h : BytecodeSharePre a s0 m0) {st : MachineData}
    (hcp : Cp m0 m sh v m0.regs.X4.toNat st)
    (hsp : NativeRustcVm.EWsAt m.dmem (base m0 432 + BitVec.ofNat 64 16) sp.toList)
    (hsz : sp.size = 4) (hts : TStateAt m.dmem m0.regs.X1.toBitVec a s3)
    (hr : res s0 m0 = some ((sh, slice m0 m0.regs.X3 m0.regs.X4 ++ sp, v), s3)) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b22Offset)⟩ := by
  obtain ⟨hS, -, hts0, -, -, -, hbl, hoo, hpo, -⟩ := pre_parts h
  have A := addr_of h
  have hlen := A.len
  have hN := A.sp
  have hpnw : m0.regs.X5.toBitVec.toNat + 1072 ≤ 2 ^ 64 := A.pnw
  have hpnwA : NoWrap m0.regs.X5.toBitVec 1072 := A.pnw
  have hP16 : (m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * m0.regs.X4.toNat)).toNat = m0.regs.X5.toBitVec.toNat + 16 * m0.regs.X4.toNat := toNat_in hpnwA (by omega)
  obtain ⟨hmP, hnwP, -⟩ := sub_range (d := st.dmem) (o := 16 * m0.regs.X4.toNat) (n := 64)
    (fun i hi ↦ hcp.fr.kept _ (hpo.1 i hi)) hpnwA (by show _ ≤ 1072; omega)
  have hwf : (Env.ofMachine st [(base m0 432, 432), (m0.regs.X0.toBitVec, 48),
      (m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * m0.regs.X4.toNat), 64)]).WF :=
    wf_frame3 hS N_ge hcp.fr.kept (fun i hi ↦ hcp.fr.kept _ (hoo.1 i hi)) A.onw hmP hnwP A.ost
      (by have := A.pst; rw [ptBytes_eq] at this; unfold Apart at this ⊢; rw [hP16]; omega)
      (by have := A.op; rw [ptBytes_eq] at this; unfold Apart at this ⊢; rw [hP16]; omega)
  have hm := match_frame3 (n1 := 48) (n2 := 64) (c1 := 0) (c2 := 0) hS N_ge rfl hcp.fr.sp
    (r1 := .X19) (r2 := .X9) (x1 := m0.regs.X0.toBitVec) (x2 := m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * m0.regs.X4.toNat))
    (by rw [hcp.regs.x19, NativeRustcVm.addr_add_zero]) (by rw [hcp.x9, NativeRustcVm.addr_add_zero])
  refine exec_then (b22_in_code.trans hp.1 (by simp [b22])) run_b22 hwf hm fun st' hm' hpc ↦ ?_
  have hW : ∀ w ∈ (after b22 frEnd).mem, (w.r = 1 ∧ w.off + w.n ≤ 48) ∨
      (w.r = 2 ∧ w.off + w.n ≤ 64) := by
    rw [Bus.after_eq run_b22]; decide
  rw [Bus.after_eq run_b22] at hW
  have hfr : Fr m0 432 bytecodeShareStack slots keep (outs m0) st'.data :=
    Fr.ofBlockW (Bus.Fr.mono hcp.fr outsP_all) hm hm' hwf rfl rfl (fun r hr ↦ absurd hr List.not_mem_nil)
      rfl N_ge hN slots_le fun w hw ↦ writeOk3
        (fun i hi ↦ .inl (NativeRustcVm.inRange_add hi (by have := A.onw; unfold NoWrap at this; omega)))
        (fun i hi ↦ .inr (.inr (by
          rw [NativeRustcVm.addr_add_add]
          exact NativeRustcVm.inRange_add (by unfold ptBytes sharePointSlots busPointCap; omega)
            (by unfold ptBytes sharePointSlots busPointCap; omega)))) (hW w hw)
  have hs22 := same3 hm' hwf hW
  -- the output's words
  have w0 := Bus.wordAt_write hm' (r := 1) (o := 0) rfl (by omega) (v := .lit 1) (by decide)
  have w8 := Bus.wordAt_write hm' (r := 1) (o := 8) rfl (by omega) (v := .reg .X20) (by decide)
  have w16 := Bus.wordAt_write hm' (r := 1) (o := 16) rfl (by omega) (v := .reg .X21) (by decide)
  have w24 := Bus.wordAt_write hm' (r := 1) (o := 24) rfl (by omega) (v := .reg .X8) (by decide)
  have w32 := Bus.wordAt_write hm' (r := 1) (o := 32) rfl (by omega) (v := .reg .X25) (by decide)
  have w40 := Bus.wordAt_write hm' (r := 1) (o := 40) rfl (by omega) (v := .reg .X26) (by decide)
  simp only [Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec, hcp.regs.x20, hcp.regs.x21,
    hcp.x8, hcp.regs.x25, hcp.regs.x26, NativeRustcVm.addr_add_zero] at w0 w8 w16 w24 w32 w40
  -- the slot point's copy
  have hcpy := copy_words hm' (rd := 2) (rr := 0) (od := 0) (os := 16) (nw := 8) rfl rfl
    (by omega) (fun i hi ↦ by
      rw [NativeRustcVm.addr_add_add]
      exact hcp.fr.kept _ ((Bus.frame_mapped hS N_ge).1 _ (by omega))) (by decide)
  have hblL : (slice m0 m0.regs.X3 m0.regs.X4).toList.length = m0.regs.X4.toNat := by simp [slice]
  have hk : Kept m.dmem st'.data.dmem := kept_trans hcp.kept (hm'.kept hwf)
  simp only [PcOk] at hpc
  refine at_pc (hpc.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b16Offset) NativeRustcVmArm.Vm.BytecodeShare.label_10_at)) (exit16 hp h hfr ⟨?_, fun x s' hx ↦ ?_⟩)
  · rw [hr]
    simp only [Option.map_some, OptShareAt, off]
    refine ⟨w0, NativeRustcVm.ewAt_iff.mpr ⟨w8, ?_⟩, ?_, NativeRustcVm.ewAt_iff.mpr ⟨w32, ?_⟩⟩
    · rw [NativeRustcVm.addr_add_add]; exact w16
    · rw [Array.size_append, hsz, show (slice m0 m0.regs.X3 m0.regs.X4).size = m0.regs.X4.toNat by
        simp [slice]]
      rw [toUInt64_add4]
      exact w24
    · rw [NativeRustcVm.addr_add_add]; exact w40
  · rw [hr] at hx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · simp only [Array.toList_append]
      refine NativeRustcVm.ewsAt_append.mpr ⟨?_, ?_⟩
      · refine ewsAt_transfer (a := m0.regs.X3.toBitVec) (fun i hi ↦ ?_)
          (NativeRustcVm.ewsAt_of_mapped (d := m0.dmem) hbl.1.1)
        rw [hblL] at hi
        rw [hs22 _ fun hq ↦ ?_, hcp.cpy i hi]
        beta_reduce at hq
        rw [Sym.inRange_iff A.onw, Sym.inRange_iff hnwP, hP16, toNat_in hpnwA (by omega)] at hq
        have := A.op
        rw [ptBytes_eq] at this
        unfold Apart at this
        omega
      · simp only [hblL]
        refine ewsAt_transfer (a := base m0 432 + BitVec.ofNat 64 16) (fun i hi ↦ ?_) hsp
        rw [Array.length_toList, hsz] at hi
        have e := hcpy i (by omega)
        rw [Nat.zero_add] at e
        rw [e, ← NativeRustcVm.addr_add_add]
        refine hcp.same _ fun hq ↦ ?_
        have hb := base_toNat (m0 := m0) (F := 432) (by have := N_ge; omega)
        have hst := A.pst
        unfold Apart at hst
        have hsb : (stackBelow m0 bytecodeShareStack).toNat = m0.regs.SP.toNat - bytecodeShareStack :=
          base_toNat hN
        rw [NativeRustcVm.addr_add_add, Sym.inRange_iff (by omega),
          toNat_in (base_noWrap (m0 := m0) (F := 432) (by have := N_ge; omega)) (by omega)] at hq
        have := N_ge
        have := m0.regs.SP.toNat_lt
        unfold ptBytes sharePointSlots busPointCap at hst
        omega
    · refine hts.frame (R := fun q ↦ InRange m0.regs.X5.toBitVec ptBytes q ∨ InRange m0.regs.X0.toBitVec 48 q) hk ?_ ?_
      · intro q hq
        rcases hq with hq | hq
        · exact ⟨NativeRustcVm.Apart.not_inRange hpo.2.2.1 hpo.2.1 hts0.footprint.1.2 hq,
            NativeRustcVm.Apart.not_inRange hpo.2.2.2.1 hpo.2.1 hts0.footprint.2.1.2 hq⟩
        · exact ⟨NativeRustcVm.Apart.not_inRange hoo.2.2.1 hoo.2.1 hts0.footprint.1.2 hq,
            NativeRustcVm.Apart.not_inRange hoo.2.2.2.1 hoo.2.1 hts0.footprint.2.1.2 hq⟩
      · intro q hq
        rw [hs22 q fun h' ↦ hq ?_, hcp.same q fun h' ↦ hq (.inl ?_)]
        · rw [Sym.inRange_iff (by omega)] at h'
          rw [ptBytes_eq, Sym.inRange_iff hpnw]
          omega
        · rcases h' with h' | h'
          · exact .inr h'
          · left
            rw [Sym.inRange_iff hnwP, hP16] at h'
            rw [ptBytes_eq, Sym.inRange_iff hpnw]
            omega

end

end NativeRustcVmArm.Bus.BytecodeShare
