module

public import NativeRustcArm.Code.Xmss.XmssVerify.Names

public import NativeRustcArm.XmssVerify.Head
meta import NativeRustcArm.Code.Xmss.XmssVerify

/-!
# `xmss_verify`: the loop copying the signature's words

Block 2, turn `i < 75`: input words `9 + 4 i` to `12 + 4 i` to the frame at `48 + 32 i`. A fresh
environment per turn: region 0 the 32 input bytes read, 1 the 32 frame bytes written.
X13 and X12 point 24 and 16 bytes into these regions; X14 counts remaining words.
`copy` reaches block 3 after 75 turns.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash

set_option Elab.async false

/-- The symbolic state at the loop's head. -/
def stC : SState := init [(32, false), (32, false)] .sp
  [(.X12, .ptr 1 16), (.X13, .ptr 0 24)]

sym_block b2_exec := exec b2 stC

/-- The symbolic state after block 2. -/
def stC' : SState := ((exec b2 stC).getD (stC, .fall)).1

theorem stC'_facts : stC'.sp = .sp ∧ writesIn stC' [1] = true ∧
    (∀ r ∈ [XReg.X8, .X9, .X10, .X11, .X19, .X20, .X21, .X23, .X24, .X29],
      stC'.reg r = some (.reg r)) ∧
    stC'.reg .X12 = some (.ptr 1 48) ∧ stC'.reg .X13 = some (.ptr 0 56) ∧
    stC'.reg .X14 = some (.bin .sub .W64 (.reg .X14) (.lit 4)) := by decide +kernel

theorem stC'_copy : ∀ j < 4, ∀ t < 8,
    findWrite 1 (8 * j + t) stC'.mem = some (.load 0 (8 * j) 8, t) := by decide +kernel

theorem b2_exec' : exec b2 stC = some (stC', .cond
    (.not (.cmp .eq .W64 (.reg .X14) (.lit 4))) NativeRustcArm.Xmss.XmssVerify.label_1) := by
  rw [b2_exec]
  rfl

section
variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData} {i : Nat}

/-- The regions of turn `i`. -/
def regsC (m₀ : MachineData) (i : Nat) : List (BitVec 64 × Nat) :=
  [(inp m₀ + BitVec.ofNat 64 (72 + 32 * i), 32), (ad m₀ (fb + 48 + 32 * i), 32)]

theorem regsC_wf (P : Pre w m₀) (hi : i < 75) (hk : Kept m₀.dmem m.dmem) :
    (Env.ofMachine m (regsC m₀ i)).WF :=
  Env.wf_of ⟨⟨(P.inpMapped.sub (by omega)).kept hk, NoWrap.sub P.inpNW (by omega)⟩,
    ⟨(P.mapped.sub (by fbo)).kept hk, P.ad_nw (by fbo)⟩, trivial⟩
    (List.pairwise_pair.mpr (P.inp_apart (by omega) (by fbo) (by omega) (by omega)))

omit [Labels] in
theorem sub_lit (a : BitVec 64) (x c : Nat) :
    a + BitVec.ofNat 64 (x + c) - BitVec.ofNat 64 c = a + BitVec.ofNat 64 x := by
  rw [← addr_add_addr, BitVec.add_sub_cancel]

omit [Labels] in
theorem ad_sub {x y c : Nat} (m₀ : MachineData) (h : x = y + c) :
    ad m₀ x - BitVec.ofNat 64 c = ad m₀ y := by
  subst h
  unfold ad
  exact sub_lit _ _ _

theorem match_C (h : LoopAt w m₀ m i) : Match (Env.ofMachine m (regsC m₀ i)) stC m := by
  unfold stC
  apply match_ofMachine
  · exact And.intro rfl (And.intro (by simp) (And.intro rfl (And.intro (by simp) trivial)))
  · rfl
  · refine ⟨?_, ?_, trivial⟩
    · change (m.regs.getXReg .X12).toBitVec = _
      rw [h.x12]
      simp only [Sym.eval, Env.base_ofMachine_eq, regsC, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some, BitVec.ofInt_ofNat, ad_add]
      congr 1
      omega
    · change (m.regs.getXReg .X13).toBitVec = _
      rw [h.x13]
      simp only [Sym.eval, Env.base_ofMachine_eq, regsC, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some, BitVec.ofInt_ofNat, addr_add_addr]
      congr 2
      omega
  · exact trivial
  · exact trivial
  · exact trivial

/-- A byte of the stack outside turn `i`'s frame bytes is outside its regions. -/
theorem outsideC (P : Pre w m₀) (hi : i < 75) {x : Nat} (hx : x < 9200)
    (hd : x < fb + 48 + 32 * i ∨ fb + 80 + 32 * i ≤ x) :
    (Env.ofMachine m (regsC m₀ i)).Outside (ad m₀ x) :=
  Env.outside_of_apart ⟨P.inp_apart (by omega) (by omega) (by omega) (by omega),
    P.apart_ad (by omega) (by fbo) (by omega) (by omega) (by omega), trivial⟩

/-- Bytes of the stack outside turn `i`'s frame bytes are kept. -/
theorem keepC (P : Pre w m₀) (hi : i < 75) {S : SState} {m' : MachineData}
    (hm : Match (Env.ofMachine m (regsC m₀ i)) S m') {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 9200) (hd : o + bs.length ≤ fb + 48 + 32 * i ∨ fb + 80 + 32 * i ≤ o)
    (h : BytesAt m.dmem (ad m₀ o) bs) : BytesAt m'.dmem (ad m₀ o) bs :=
  hm.bytesAt_outside (fun t ht => by rw [ad_add]; exact outsideC P hi (by omega) (by omega)) h

/-- What a turn leaves. -/
theorem afterC (P : Pre w m₀) (hi : i < 75) (h : LoopAt w m₀ m i) {m' : MachineData}
    (hm : Match (Env.ofMachine m (regsC m₀ i)) stC' m') : LoopAt w m₀ m' (i + 1) := by
  have C := h.common
  have hwf := regsC_wf P hi (m := m) C.kept
  obtain ⟨hsp, hw, hregs, h12, h13, h14⟩ := stC'_facts
  have hreg : ∀ r ∈ [XReg.X8, .X9, .X10, .X11, .X19, .X20, .X21, .X23, .X24, .X29],
      m'.regs.getXReg r = m.regs.getXReg r := fun r hr =>
    UInt64.toBitVec_inj.mp (hm.regs r _ (hregs r hr))
  refine ⟨⟨?_, ?_, fun j hj => ?_, ?_, C.kept.trans (hm.kept hwf)⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, fun k hk => ?_, ?_, fun k hk => ?_, ?_, ?_, ?_⟩
  · rw [hm.sp, hsp]
    exact C.sp
  · rw [hreg .X29 (by simp)]
    exact C.x29
  · exact keepC P hi hm (by rw [length_regBytes]; fbo) (by rw [length_regBytes]; omega)
      (C.save j hj)
  · refine (C.same.trans (hm.sameOutside_in hwf hw)).mono fun p hp => hp.elim id ?_
    rintro ⟨r, hr, b, sz, hb, hin⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp only [Env.ofMachine_regions, regsC, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact P.inRange_lo (by fbo) hin
  · rw [hreg .X19 (by simp)]; exact h.x19
  · rw [hreg .X20 (by simp)]; exact h.x20
  · rw [hm.regs .X12 _ h12]
    simp only [Sym.eval, Env.base_ofMachine_eq, regsC, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some, BitVec.ofInt_ofNat, ad_add]
    congr 1
    omega
  · rw [hreg .X8 (by simp)]; exact h.x8
  · rw [hreg .X9 (by simp)]; exact h.x9
  · rw [hreg .X10 (by simp)]; exact h.x10
  · rw [hreg .X11 (by simp)]; exact h.x11
  · rw [hreg .X24 (by simp)]; exact h.x24
  · rw [hreg .X23 (by simp)]; exact h.x23
  · exact keepC P hi hm (by rw [NativeRustc.length_wordBytes]; fbo)
      (by rw [NativeRustc.length_wordBytes]; omega) (h.msg k hk)
  · exact keepC P hi hm (by simp; fbo) (by simp; omega) h.li
  · by_cases hki : k < 4 * i
    · exact keepC P hi hm (by rw [NativeRustc.length_wordBytes]; fbo)
        (by rw [NativeRustc.length_wordBytes]; omega) (h.sig k hki)
    · obtain ⟨j, hj, rfl⟩ : ∃ j < 4, k = 4 * i + j := ⟨k - 4 * i, by omega, by omega⟩
      have := copy_word P hm (rd := 1) (od := 8 * j) rfl (by omega) (i := 9 + (4 * i + j))
        (by omega) (rs := 0) (os := 8 * j) (fun t _ => by
          simp only [Env.base_ofMachine_eq, regsC, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some, addr_add_addr]
          congr 2
          omega) C.same (stC'_copy j hj)
      rw [ad_add] at this
      rwa [show fb + 48 + 8 * (4 * i + j) = fb + 48 + 32 * i + 8 * j by omega]
  · rw [hreg .X21 (by simp)]; exact h.x21
  · rw [hm.regs .X13 _ h13]
    simp only [Sym.eval, Env.base_ofMachine_eq, regsC, List.getElem?_cons_zero,
      Option.map_some, Option.getD_some, BitVec.ofInt_ofNat, addr_add_addr]
    congr 2
    omega
  · rw [hm.regs .X14 _ h14]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h.x14]
    rw [show 300 - 4 * i = (300 - 4 * (i + 1)) + 4 by omega, BitVec.ofNat_add,
      BitVec.add_sub_cancel]

end

variable {w : Nat → UInt64} {m₀ : MachineData} {i : Nat}

/-- **A turn of the copy**: from the head before turn `i`, the head before turn `i + 1`, or
block 3 after the last turn. -/
theorem turnC [Host] {k : Nat} (hp : Placed code k) (P : Pre w m₀) (hi : i < 75)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b2Offset)) (h : LoopAt w m₀ st.data i) :
    Eventually (step1 Host.exe) (fun st' => (i + 1 = 75 ∧ st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b3Offset) ∧
      LoopAt w m₀ st'.data 75) ∨
      (i + 1 < 75 ∧ st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b2Offset) ∧ LoopAt w m₀ st'.data (i + 1))) st := by
  have hwf := regsC_wf P hi (m := st.data) h.common.kept
  refine exec_at (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) b2_exec' hwf hpc (match_C h)
    fun st' hm hpc' => .done _ ?_
  have A := afterC P hi h hm
  have hc : (SBool.not (.cmp .eq .W64 (.reg .X14) (.lit 4))).eval
      (Env.ofMachine st.data (regsC m₀ i)) = decide (i + 1 < 75) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs, h.x14]
    by_cases hlt : i + 1 < 75
    · simp only [hlt, decide_true, Bool.not_eq_true']
      simp [BitVec.toNat_eq]
      omega
    · simp only [hlt, decide_false, Bool.not_eq_false']
      simp [BitVec.toNat_eq]
      omega
  simp only [PcOk, hc] at hpc'
  by_cases hlt : i + 1 < 75
  · simp only [hlt, decide_true, ite_true] at hpc'
    exact Or.inr ⟨hlt, hpc'.trans ((hp.label NativeRustcArm.Xmss.XmssVerify.label_1_at)), A⟩
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false] at hpc'
    have hi' : i + 1 = 75 := by omega
    exact Or.inl ⟨hi', hpc'.trans rfl, hi' ▸ A⟩

/-- **The copy of the signature's words.** -/
public theorem copy [Host] {k : Nat} (hp : Placed code k) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b2Offset)) (h : LoopAt w m₀ st.data 0) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b3Offset) ∧
      LoopAt w m₀ st'.data 75) st :=
  Sym.loop (I := fun n s => ∃ i, i + n = 75 ∧ 0 < n ∧ s.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b2Offset) ∧
      LoopAt w m₀ s.data i)
    (fun n s ⟨i, hn, hn0, hpc, h⟩ => NativeRustcArm.Eventually.mono (turnC hp P (by omega) hpc h)
      fun s' h' => by
        rcases h' with ⟨-, h'⟩ | ⟨hlt, hpc', h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨n - 1, by omega, i + 1, by omega, by omega, hpc', h'⟩)
    (n := 75) ⟨0, rfl, by decide, hpc, h⟩

end NativeRustcArm.Xmss.XmssVerify
