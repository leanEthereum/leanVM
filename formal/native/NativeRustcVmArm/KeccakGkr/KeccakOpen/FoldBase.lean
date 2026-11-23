module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Known
public import NativeRustcVmArm.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s fold: tools

Elements kept or changed where memory changed in a range given as numbers (`ElemsAt.keepN`,
`ElemsAt.setN`); `Mid` kept by a block that writes nothing (`Mid.of_dmem`); a callee's stack below
the frame (`MulR`); the environment of an inner loop's loads (`bufR`, `wf_buf`); a counted loop
(`loopN`); a fold's entry as the code computes it (`foldE_eq`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays

@[expose] public section

/-- The two elements an inner loop loads: entry `j` of the buffers at the frame's `80`, `1104`. -/
def bufR (m0 : MachineData) (j : Nat) : List (BitVec 64 × Nat) :=
  [(fbA m0 + BitVec.ofNat 64 (80 + 16 * j), 16), (fbA m0 + BitVec.ofNat 64 (1104 + 16 * j), 16)]

/-- The bytes of `EW::mul`'s stack, below the frame. -/
def MulR (m0 : MachineData) (q : BitVec 64) : Prop :=
  spN m0 - 2816 ≤ q.toNat ∧ q.toNat < spN m0 - 2224

end

public section

variable {c : Cx} {m0 st st' : MachineData}

/-- **Elements kept** where memory changed only outside them. -/
theorem ElemsAt.keepN {d d' : DataMem} {a : BitVec 64} {f : Nat → EW} {N : Nat}
    {R : BitVec 64 → Prop} (h : ElemsAt d a f N) (hs : SameOutside d d' R)
    (hnw : a.toNat + 16 * N ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 16 * N ≤ q.toNat) : ElemsAt d' a f N :=
  ElemsAt.keep h hs (fun p hp hRp ↦ by
    rw [inRange_nat hnw] at hp
    have := hR p hRp
    omega) hnw

/-- **An element changed**: element `m` is `v`, memory changed only there. -/
theorem ElemsAt.setN {d d' : DataMem} {a : BitVec 64} {g : Nat → EW} {N m : Nat} {v : EW}
    {R : BitVec 64 → Prop} (h : ElemsAt d a g N) (hnw : a.toNat + 16 * N ≤ 2 ^ 64) (hm : m < N)
    (hs : SameOutside d d' R)
    (hR : ∀ q, R q → a.toNat + 16 * m ≤ q.toNat ∧ q.toNat < a.toNat + 16 * m + 16)
    (hv : NativeRustcVm.EWAt d' (a + BitVec.ofNat 64 (16 * m)) v) :
    ElemsAt d' a (fun n ↦ if n = m then v else g n) N := by
  intro i hi
  by_cases him : i = m
  · subst him
    have e : (if i = i then v else g i) = v := ite_eq_left_iff.mpr fun h ↦ absurd rfl h
    show NativeRustcVm.EWAt d' _ (if i = i then v else g i)
    rw [e]
    exact hv
  · have e : (if i = m then v else g i) = g i := ite_eq_right_iff.mpr fun h ↦ absurd h him
    show NativeRustcVm.EWAt d' _ (if i = m then v else g i)
    rw [e]
    refine NativeRustcVm.BytesAt.of_sameOutside (h i hi) hs fun t ht hRt ↦ ?_
    rw [NativeRustcVm.length_ewBytes] at ht
    have := hR _ hRt
    rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at this
    omega

theorem fbA_toNat (hn : Nums c.a m0) : (fbA m0).toNat = spN m0 - 2224 :=
  fb_toNat (by have := hn.hN; omega)

theorem fbA_add (hn : Nums c.a m0) {o : Nat} (ho : o ≤ 2224) :
    (fbA m0 + BitVec.ofNat 64 o).toNat = spN m0 - 2224 + o :=
  fb_add (by have := hn.hN; omega) ho

theorem spN_lt (m0 : MachineData) : spN m0 < 2 ^ 64 := m0.regs.SP.toBitVec.isLt

theorem mulR_safe (hn : Nums c.a m0) {q : BitVec 64} (h : MulR m0 q) : Safe m0 q := by
  unfold MulR at h
  unfold Safe
  have := hn.hN
  omega

/-- The rows' region is one `keccak_open` writes. -/
theorem rows_mem : (⟨rwA m0, NativeRustcVm.KeccakGkr.rowsBytes⟩ : NativeRustcVm.Region) ∈ wsOf m0 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

section
variable [Labels]

/-- **`Mid` kept** by a change of the registers alone. -/
theorem Mid.of_dmem (hm : Mid c m0 st) (hb : Body m0 st') (hd : st'.dmem = st.dmem) :
    Mid c m0 st' := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hm
  rw [← hd] at h1 h2 h3 h4 h5 h7 h8
  exact ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- `EW::mul`'s stack is `MulR`. -/
theorem mulR_of (hn : Nums c.a m0) (hb : Body m0 st) {q : BitVec 64}
    (h : InRange (stackBelow st ewMulStack) ewMulStack q) : MulR m0 q := by
  have hN := hn.hN
  have h1 : st.regs.SP.toBitVec = fbA m0 := hb.sp
  have e : (stackBelow st ewMulStack).toNat = spN m0 - 2816 := by
    unfold stackBelow
    rw [h1, show ewMulStack = 592 from rfl, toNat_sub_ofNat (by rw [fbA_toNat hn]; omega),
      fbA_toNat hn]
    omega
  rw [inRange_nat (by rw [e]; have := spN_lt m0; rw [show ewMulStack = 592 from rfl]; omega),
    e] at h
  unfold MulR
  rw [show ewMulStack = 592 from rfl] at h
  omega

/-- **The loads' environment** is well formed. -/
theorem wf_buf (ok : Ok c.a m0) (hb : Body m0 st) {j : Nat} (hj : j < 64) :
    (Env.ofMachine st (bufR m0 j)).WF := by
  obtain ⟨hfm, hfw, -⟩ := frame_ok ok.stack (show 2224 ≤ keccakOpenStack by decide)
  have hok : NativeRustcVm.Region.Ok st.dmem ⟨fbA m0, 2224⟩ := ⟨Mapped.kept' hfm hb.kept, hfw⟩
  obtain ⟨h1m, h1w⟩ := sub_ok hok (o := 80 + 16 * j) (n := 16) (by omega)
  obtain ⟨h2m, h2w⟩ := sub_ok hok (o := 1104 + 16 * j) (n := 16) (by omega)
  refine Env.wf_of ⟨⟨h1m, h1w⟩, ⟨h2m, h2w⟩, trivial⟩
    (List.pairwise_cons.mpr ⟨fun e he ↦ ?_, List.pairwise_singleton _ _⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  exact apart_in hfw (by omega) (by omega)

/-- A part of the rows is data memory and does not wrap. -/
theorem rows_ok (ok : Ok c.a m0) (hb : Body m0 st) {o n : Nat} (h : o + n ≤ 65536) :
    Mapped st.dmem (rwA m0 + BitVec.ofNat 64 o) n ∧ NoWrap (rwA m0 + BitVec.ofNat 64 o) n :=
  sub_ok (show NativeRustcVm.Region.Ok st.dmem ⟨rwA m0, 65536⟩ from
    ⟨Mapped.kept' ok.rowsM hb.kept, ok.nums.rW⟩) h

/-- A byte of the rows is in a region `keccak_open` writes. -/
theorem rows_inAny (ok : Ok c.a m0) {q : BitVec 64}
    (h : (rwA m0).toNat ≤ q.toNat ∧ q.toNat < (rwA m0).toNat + 65536) :
    NativeRustcVm.InAny (wsOf m0) q :=
  ⟨_, rows_mem, (inRange_nat ok.nums.rW).mpr h⟩

end

/-- The value of the alias form of an index register. -/
theorem memExtend_uxtx0 (x : BitVec 64) :
    UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64 x = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned, BitVec.toNat_ofInt]
  have := x.isLt
  omega

/-- **A fold's entry** as the code computes it: the product of the challenge and the sum of the
two entries, plus the first. -/
theorem foldE_eq {cc : EW} {fa fb : Nat → EW} {j : Nat} {x0 x1 l0 l1 : UInt64}
    (hx : (⟨x0, x1⟩ : EW) = cc * (fb j + fa j)) (h0 : l0 = (fa j).c0) (h1 : l1 = (fa j).c1) :
    (⟨x0 ^^^ l0, x1 ^^^ l1⟩ : EW) = foldE cc fa fb j := by
  have e : fb j + fa j = fa j + fb j := by
    show (⟨_, _⟩ : EW) = ⟨_, _⟩
    rw [UInt64.xor_comm (fb j).c0, UInt64.xor_comm (fb j).c1]
  rw [e] at hx
  have e0 := congrArg EW.c0 hx
  have e1 := congrArg EW.c1 hx
  simp only at e0 e1
  unfold foldE
  show _ = (⟨_, _⟩ : EW)
  rw [e0, e1, h0, h1, UInt64.xor_comm, UInt64.xor_comm (cc * (fa j + fb j)).c1]

/-- **A counted loop**: `P j` at `a` for `j < n` reaches `P (j + 1)`, at `a` while `j + 1 < n`,
at `b` once `j + 1 = n`. -/
theorem loopN [NativeRustcArm.Host] {k ka kb n : Nat} {P : Nat → MachineData → Prop}
    (step : ∀ j (s : MachineState), j < n → s.pc = Host.addrOf (k + ka) → P j s.data →
      Eventually (step1 Host.exe) (fun s' ↦
        (j + 1 < n ∧ s'.pc = Host.addrOf (k + ka) ∧ P (j + 1) s'.data) ∨
          (j + 1 = n ∧ s'.pc = Host.addrOf (k + kb) ∧ P (j + 1) s'.data)) s)
    {j : Nat} (hj : j < n) {s : MachineState} (hpc : s.pc = Host.addrOf (k + ka))
    (h : P j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + kb) ∧ P n s'.data) s :=
  Sym.loop (fun m s ↦ ∃ j, m = n - j ∧ j < n ∧ s.pc = Host.addrOf (k + ka) ∧ P j s.data)
    (fun _ s ⟨j, hm, hj, hpc, h⟩ ↦ (step j s hj hpc h).mono fun s' h' ↦ by
      rcases h' with ⟨hj', hpc', h'⟩ | ⟨hj', hpc', h'⟩
      · exact Or.inr ⟨n - (j + 1), by omega, j + 1, rfl, hj', hpc', h'⟩
      · exact Or.inl ⟨hpc', hj' ▸ h'⟩)
    ⟨j, rfl, hj, hpc, h⟩

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
