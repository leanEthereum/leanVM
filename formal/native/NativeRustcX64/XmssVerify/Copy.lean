module

public import NativeRustcX64.Code.Xmss.XmssVerify.Names

public import NativeRustcX64.XmssVerify.Head

/-!
# `xmss_verify`: the loop copying the signature's words (x86-64)

Block 2, turn `t < 50`: input words `9 + 6 t` to `14 + 6 t` to the frame region at
`956 + 48 t`. A fresh environment per turn: region 0 the 48 input bytes read, 1 the 48 frame
bytes written; the indexed address sums `R14 + 8 R15` and `RSP + 8 R15` are aliases of them
(`stC`). `copy`: from `LoopAt 0` to `LoopAt 50` at block 3.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

set_option Elab.async false

public section

theorem stC'_facts : writesIn (after b2 stC) [1] = true ∧
    (∀ r ∈ [Reg64.r14, .rsp, .rax, .rcx, .rdx, .rsi, .r13, .rbx, .rbp], (after b2 stC).reg r = some (.reg r)) ∧
    (after b2 stC).reg .r15 = some (.bin .add .W64 (.lit 6) (.reg .r15)) := by decide +kernel

theorem stC'_copy : ∀ j < 6, ∀ u < 8,
    findWrite 1 (8 * j + u) (after b2 stC).mem = some (.load 0 (8 * j) 8, u) := by decide +kernel

theorem run_b2' : exec b2 stC = some (after b2 stC, .cond
    (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 6) (.reg .r15)) (.lit 300))) NativeRustcX64.Xmss.XmssVerify.label_1) := by
  rw [run_b2]
  rfl

section
variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData} {t : Nat}

/-- The regions of turn `t`. -/
def regsC (m₀ : MachineData) (t : Nat) : List (BitVec 64 × Nat) :=
  [(inp m₀ + BitVec.ofNat 64 (72 + 48 * t), 48), (ad m₀ (fr + 956 + 48 * t), 48)]

theorem regsC_wf (P : Pre w m₀) (ht : t < 50) (hk : Kept m₀.dmem m.dmem) :
    (Env.ofMachine m (regsC m₀ t)).WF :=
  Env.wf_of ⟨⟨(P.inpMapped.sub (by omega)).kept hk, NoWrap.sub P.inpNW (by omega)⟩,
    ⟨(P.mapped.sub (by fro)).kept hk, P.ad_nw (by fro)⟩, trivial⟩
    (List.pairwise_pair.mpr (P.inp_apart (by omega) (by fro) (by omega) (by omega)))

theorem idx8_eval (r : Reg64) {env : Env} :
    (idx8 r).eval env = env.regs r + env.regs .r15 * 8#64 := by
  simp only [idx8, eval_mkAdd64, eval_mkBin, Sym.eval, BinOp.apply, low_W64, ext_W64]

omit [Labels] in
theorem alias_context (ctx : BitVec 64) (t : Nat) :
    ctx + BitVec.ofNat 64 (6 * t) * 8#64 =
      ctx + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (72 + 48 * t) + BitVec.ofInt 64 (-1096) := by
  have e : BitVec.ofInt 64 (-1096) = 0#64 - 1096#64 := by decide
  rw [e]
  bv_omega

omit [Labels] in
theorem alias_rsp (l : BitVec 64) (t : Nat) :
    l + BitVec.ofNat 64 (fr + 24) + BitVec.ofNat 64 (6 * t) * 8#64 =
      l + BitVec.ofNat 64 (fr + 956 + 48 * t) + BitVec.ofInt 64 (-932) := by
  have e : BitVec.ofInt 64 (-932) = 0#64 - 932#64 := by decide
  rw [e, fr_eq]
  bv_omega

theorem match_C (h : LoopAt w m₀ m t) : Match (Env.ofMachine m (regsC m₀ t)) stC m := by
  unfold stC
  refine match_ofMachine (sregions := [48, 48]) ⟨rfl, rfl, trivial⟩ trivial trivial trivial
    ⟨?_, ?_, trivial⟩
  · show (idx8 .r14).eval _ = _
    rw [idx8_eval]
    show reg m .r14 + reg m .r15 * 8#64 = inp m₀ + BitVec.ofNat 64 (72 + 48 * t) + _
    rw [h.r14, h.r15]
    exact alias_context _ t
  · show (idx8 .rsp).eval _ = _
    rw [idx8_eval]
    show rspOf m + reg m .r15 * 8#64 = ad m₀ (fr + 956 + 48 * t) + _
    rw [h.rsp, h.r15]
    exact alias_rsp _ t

/-- A byte of the stack outside turn `t`'s frame bytes is outside its regions. -/
theorem outsideC (P : Pre w m₀) (ht : t < 50) {x : Nat} (hx : x < 9256)
    (hd : x < fr + 956 + 48 * t ∨ fr + 1004 + 48 * t ≤ x) :
    (Env.ofMachine m (regsC m₀ t)).Outside (ad m₀ x) :=
  Env.outside_of_apart ⟨P.inp_apart (by omega) (by omega) (by omega) (by omega),
    P.apart_ad (by omega) (by fro) (by omega) (by omega) (by omega), trivial⟩

/-- Bytes of the stack outside turn `t`'s frame bytes are kept. -/
theorem keepC (P : Pre w m₀) (ht : t < 50) {S : SState} {m' : MachineData}
    (hm : Match (Env.ofMachine m (regsC m₀ t)) S m') {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 9256)
    (hd : o + bs.length ≤ fr + 956 + 48 * t ∨ fr + 1004 + 48 * t ≤ o)
    (h : BytesAt m.dmem (ad m₀ o) bs) : BytesAt m'.dmem (ad m₀ o) bs :=
  hm.bytesAt_outside (fun u hu => by rw [ad_add]; exact outsideC P ht (by omega) (by omega)) h

set_option linter.unusedSimpArgs false in
/-- What a turn leaves. -/
theorem afterC (P : Pre w m₀) (ht : t < 50) (h : LoopAt w m₀ m t) {m' : MachineData}
    (hm : Match (Env.ofMachine m (regsC m₀ t)) (after b2 stC) m') : LoopAt w m₀ m' (t + 1) := by
  have C := h.common
  have hwf := regsC_wf P ht (m := m) C.kept
  obtain ⟨hw, hregs, h15⟩ := stC'_facts
  have hreg : ∀ r ∈ [Reg64.r14, .rsp, .rax, .rcx, .rdx, .rsi, .r13, .rbx, .rbp], reg m' r = reg m r :=
    fun r hr => hm.regs r _ (hregs r hr)
  refine ⟨⟨fun j hj => ?_, ?_, C.kept.trans (hm.kept hwf)⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun k hk => ?_, ?_, ?_, fun k hk => ?_⟩
  · exact keepC P ht hm (by rw [length_regBytes]; fro) (by rw [length_regBytes]; omega)
      (C.save j hj)
  · refine (C.same.trans (hm.sameOutside_in hwf hw)).mono fun p hp => hp.elim id ?_
    rintro ⟨r, hr, b, sz, hb, hin⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp only [Env.ofMachine_regions, regsC, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact P.inRange_lo (by fro) hin
  · exact (hreg .rsp (by simp)).trans h.rsp
  · exact (hreg .r14 (by simp)).trans h.r14
  · rw [show reg m' .r15 = _ from hm.regs .r15 _ h15]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show m.regs.get64 .r15 = reg m .r15 from rfl, h.r15, BitVec.ofNat_add_ofNat]
    congr 1
    omega
  · exact (hreg .rax (by simp)).trans h.rax
  · exact (hreg .rcx (by simp)).trans h.rcx
  · exact (hreg .rdx (by simp)).trans h.rdx
  · exact (hreg .rsi (by simp)).trans h.rsi
  · exact (hreg .r13 (by simp)).trans h.r13
  · exact (hreg .rbx (by simp)).trans h.rbx
  · exact keepC P ht hm (by rw [NativeRustc.length_wordBytes]; fro)
      (by rw [NativeRustc.length_wordBytes]; omega) (h.msg k hk)
  · exact (hreg .rbp (by simp)).trans h.rbp
  · exact keepC P ht hm (by simp; fro) (by simp; omega) h.li
  · by_cases hkt : k < 6 * t
    · exact keepC P ht hm (by rw [NativeRustc.length_wordBytes]; fro)
        (by rw [NativeRustc.length_wordBytes]; omega) (h.sig k hkt)
    · obtain ⟨j, hj, rfl⟩ : ∃ j < 6, k = 6 * t + j := ⟨k - 6 * t, by omega, by omega⟩
      have := copy_word P hm (rd := 1) (od := 8 * j) rfl (by omega) (i := 9 + (6 * t + j))
        (by omega) (rs := 0) (os := 8 * j) (fun u _ => by
          simp only [Env.base_ofMachine_eq, regsC, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some, addr_add_addr]
          congr 2
          omega) C.same (stC'_copy j hj)
      rw [ad_add] at this
      rwa [show fr + 956 + 8 * (6 * t + j) = fr + 956 + 48 * t + 8 * j by omega]

end

variable {w : Nat → UInt64} {m₀ : MachineData} {t : Nat}

set_option linter.unusedSimpArgs false in
/-- **A turn of the copy**: from the head before turn `t`, the head before turn `t + 1`, or
block 3 after the last turn. -/
theorem turnC [Host] {k : Nat} (hp : Placed code k) (P : Pre w m₀) (ht : t < 50)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b2Offset)) (h : LoopAt w m₀ st.data t) :
    Eventually (step1 Host.exe) (fun st' => (t + 1 = 50 ∧ st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b3Offset) ∧
      LoopAt w m₀ st'.data 50) ∨
      (t + 1 < 50 ∧ st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b2Offset) ∧ LoopAt w m₀ st'.data (t + 1))) st := by
  have hwf := regsC_wf P ht (m := st.data) h.common.kept
  refine exec_at (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b2' hwf
    (fun _ h => nomatch h) hpc (match_C h) fun st' hm hpc' => .done _ ?_
  have A := afterC P ht h hm
  have hc : (SBool.not (.cmp .eq .W64 (.bin .add .W64 (.lit 6) (.reg .r15)) (.lit 300))).eval
      (Env.ofMachine st.data (regsC m₀ t)) = decide (t + 1 < 50) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs]
    rw [show st.data.regs.get64 .r15 = reg st.data .r15 from rfl, h.r15, BitVec.ofNat_add_ofNat]
    by_cases hlt : t + 1 < 50
    · simp only [hlt, decide_true, Bool.not_eq_true']
      simp [BitVec.toNat_eq]
      omega
    · simp only [hlt, decide_false, Bool.not_eq_false']
      simp [BitVec.toNat_eq]
      omega
  simp only [PcOk, hc] at hpc'
  by_cases hlt : t + 1 < 50
  · simp only [hlt, decide_true, ite_true] at hpc'
    exact Or.inr ⟨hlt, hpc'.trans ((hp.label NativeRustcX64.Xmss.XmssVerify.label_1_at)), A⟩
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false] at hpc'
    have ht' : t + 1 = 50 := by omega
    exact Or.inl ⟨ht', hpc'.trans rfl, ht' ▸ A⟩

/-- **The copy of the signature's words.** -/
theorem copy [Host] {k : Nat} (hp : Placed code k) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b2Offset)) (h : LoopAt w m₀ st.data 0) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b3Offset) ∧
      LoopAt w m₀ st'.data 50) st :=
  Sym.loop (I := fun n s => ∃ t, t + n = 50 ∧ 0 < n ∧ s.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b2Offset) ∧
      LoopAt w m₀ s.data t)
    (fun n s ⟨t, hn, hn0, hpc, h⟩ => NativeRustcX64.Eventually.mono (turnC hp P (by omega) hpc h)
      fun s' h' => by
        rcases h' with ⟨-, h'⟩ | ⟨hlt, hpc', h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨n - 1, by omega, t + 1, by omega, by omega, hpc', h'⟩)
    (n := 50) ⟨0, rfl, by decide, hpc, h⟩

end

end NativeRustcX64.Xmss.XmssVerify
