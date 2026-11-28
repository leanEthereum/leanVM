module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names
public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.XmssVerify.Tree1

/-!
# `xmss_verify`: the loop over the top layer's path (x86-64)

`turn1`: blocks 19 to 25 with the calls between them (`NativeRustcX64.XmssVerify.Tree1`), from
`TreeAt1` at level `z < 16` to `TreeAt1` at `z + 1`, back at block 19 or, at `z + 1 = 16`, on at
block 26. `loop1`: the 16 turns.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

set_option linter.unusedSimpArgs false in
/-- **A turn over the top layer's path**: from `TreeAt1` at level `z < 16` at block 19 to
`TreeAt1` at `z + 1`, at block 19 again or, at `z + 1 = 16`, at block 26. -/
public theorem turn1 {k : Nat} (hp : Placed code k)
    (hset : Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost)
    (hupd : Spec (label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost)
    (hcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hfin : Spec (label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre FinalizePost) (P : Pre w m₀)
    {leaf : List UInt8} (hleaf : leaf.length = 16) {z : Nat} (hz : z < 16)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b19Offset)) (h : TreeAt1 w m₀ leaf st.data z)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState,
      st'.pc = (if z + 1 = 16 then Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b26Offset) else Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b19Offset)) →
      TreeAt1 w m₀ leaf st'.data (z + 1) → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have hc : 1204 + 1200 ≤ (sigB w).length := by simp [length_sigB]
  have hpath : BytesAt st.data.dmem (ad m₀ (fr + (4556 + 16 * z))) ((topL w).path.getD z []) := by
    have := layer_path (bs := sigB w) (c := 1204) hc h.top hz
    rwa [ad_add, Nat.add_assoc] at this
  have hsibL : ((topL w).path.getD z []).length = 16 := path_len hc hz
  have hcurL := length_pf (pp w) 1 (li1 w).toNat (topL w).path hleaf z
  have hlen1 : (topL w).memBytes.length = 1200 := length_memBytes hc
  -- Block 19.
  let env := Env.ofMachine st.data (nodeR m₀ (4556 + 16 * z)) (fun _ => 0)
    (Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b19Offset + b19.length)).toBitVec
  have hwf : env.WF := node_wf P C.kept (by omega) (by omega)
  have hm : Match env st19 st.data :=
    match_stN P C.same ⟨h.rsp.trans (eval_ptr0 24).symm,
      h.r14.trans ((congrArg (ad m₀) (by omega)).trans (eval_ptr1 0).symm),
      h.r13.trans (eval_ptr0 120).symm, h.rbp.trans (eval_ptr0 608).symm,
      h.r15.trans (eval_ptr0 184).symm, trivial⟩
  obtain ⟨f0, f1, f2, fsp, fbp, f13, f14, f15, gbx, g12, fw, flow⟩ := st19_regs
  obtain ⟨c0, c1, c2, c3⟩ := st19_children
  obtain ⟨a1, a2, a3, a4, a5⟩ := st19_addr
  refine call_step (b19_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b19 hwf rfl hpc hm
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ (after b19 st19) st₁.data at hm₁
  have C₁ := Common.block P C hwf hm₁ fw
  have hx : ∀ {r : Reg64} {o : Nat}, (after b19 st19).reg r = some (.ptr 0 o) →
      reg st₁.data r = ad m₀ (fr + o) := fun hr => (hm₁.regs _ _ hr).trans (eval_ptr0 _)
  have hrsp₁ : rspOf st₁.data = ad m₀ (fr + 16) := hx fsp
  have hr12 : (Sym.reg .r12).eval env = BitVec.ofNat 64 (z + 1) := h.r12
  have hrbx : env.regs .rbx = BitVec.ofNat 64 (li1 w).toNat := h.rbx
  have hli1 : (li1 w).toNat < 2 ^ 32 := (li1 w).toNat_lt
  have hlo : ((loW (.reg .r12)).eval env).toNat = (li1 w).toNat >>> (z + 1) :=
    loW_toNat hr12 (by omega) hrbx hli1
  have hhi := hi1_eval (env := env) hz hr12
  have hA₁ := addrAt hm₁ (by omega) a1 a2 a3 a4 a5 hlo hhi
  have hsib := halves hpath
  have l3 : (((topL w).path.getD z []).take 8).length = 8 := by
    rw [List.length_take, hsibL]; rfl
  have l4 : ((((topL w).path.getD z []).drop 8).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hsibL]; rfl
  have r2 : regBytes ((Sym.load 1 0 8).eval env) = ((topL w).path.getD z []).take 8 :=
    regBytes_node l3 (by rw [Nat.add_zero]; exact hsib.1)
  have r3 : regBytes ((Sym.load 1 8 8).eval env) = (((topL w).path.getD z []).drop 8).take 8 :=
    regBytes_node l4 hsib.2
  have hCh₁ := childrenAt hm₁ (by omega) c0 c1 c2 c3
    (cur := pf (pp w) 1 (li1 w).toNat (topL w).path leaf z)
    (sib := (topL w).path.getD z []) h.cur
    (by rw [r2, r3, List.take_of_length_le (l := List.drop 8 _) (by rw [List.length_drop, hsibL]),
      List.take_append_drop])
  rw [bitC_eval (r12m1_eval h.r12) (by omega) hrbx hli1] at hCh₁
  simp only [decide_eq_true_eq] at hCh₁
  have hChL : (if (li1 w).toNat >>> z &&& 1 = 0 then
      pf (pp w) 1 (li1 w).toNat (topL w).path leaf z ++ (topL w).path.getD z []
      else (topL w).path.getD z [] ++ pf (pp w) 1 (li1 w).toNat (topL w).path leaf z).length =
      32 := by
    split <;> rw [List.length_append, hcurL, hsibL]
  have hpk₁ : BytesAt st₁.data.dmem (ad m₀ (fr + 40)) (pkB w) :=
    frame_keep2 P hwf hm₁ flow h.pk le_rfl (by simp [length_pkB]) (by simp [length_pkB])
  have htop₁ := frame_keep P hwf hm₁ fw h.top (by omega) (by simp [hlen1])
  -- `memset` of the hasher.
  refine memsetCall hset P hpc₁ C₁ hrsp₁ (dst := 184) (n := 344) (hx f0)
    (toNat_lit (hm₁.regs _ _ f2) (by decide)) (by omega) (by omega) (by omega)
    fun st₂ hpc₂ hrsp₂ C₂ hs₂ hb₂ hsm₂ => ?_
  have hk₂ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₁.data.dmem (ad m₀ (fr + x)) bs →
      x + bs.length ≤ 5816 → 16 ≤ x → (x + bs.length ≤ 184 ∨ 528 ≤ x) →
      BytesAt st₂.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb hle hq h1 => keep_callR P hrsp₁ (by decide) (by decide) hsm₂ hb hle hq h1
  have hh₂ : Keccak.HasherHolds (bytesOf st₂.data.dmem (ad m₀ (fr + 184)) 344) [] := by
    have hr : reg st₁.data .rsi = BitVec.ofNat 64 0 := hm₁.regs _ _ f1
    have := hb₂.bytesOf
    rw [List.length_replicate, hr] at this
    rw [this]
    exact Keccak.holds_new
  have hr15₂ : reg st₂.data .r15 = ad m₀ (fr + 184) := (hs₂.1 .r15 rfl).trans (hx f15)
  have hrbp₂ : reg st₂.data .rbp = ad m₀ (fr + 608) := (hs₂.1 .rbp rfl).trans (hx fbp)
  have hpk₂ := hk₂ hpk₁ (by simp [length_pkB]) (by omega) (by simp [length_pkB])
  -- Blocks 20 to 24: the node's hash.
  refine hashNode hupd hcpy hfin P (X := .rax) (H := .rbp) (j := k + NativeRustcX64.Xmss.XmssVerify.b20Offset)
    (k12 := [(.r15, .ptr 0 184), (.rbp, .ptr 0 608)])
    (b20_in_code.trans hp.1 (List.cons_ne_nil _ _)) (b21_in_code.trans hp.1 (List.cons_ne_nil _ _))
    (b22_in_code.trans hp.1 (List.cons_ne_nil _ _)) (b23_in_code.trans hp.1 (List.cons_ne_nil _ _))
    (b24_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b20' f20 run_b21' f21 run_b22' f22
    run_b23' f23 run_b24' f24 rfl (by decide) (hpc₂.trans rfl) C₂ hrsp₂ hr15₂
    (fun _ _ hs => ⟨((hs .r15 rfl (by decide)).trans hr15₂).trans (eval_ptr0 184).symm,
      ((hs .rbp rfl (by decide)).trans hrbp₂).trans (eval_ptr0 608).symm, trivial⟩)
    (length_pp w) (length_address _) hChL hh₂ (pp_at hpk₂)
    (hk₂ hA₁ (by simp [length_address]) (by omega) (by simp [length_address]))
    (hk₂ hCh₁ (by rw [hChL]; omega) (by omega) (by rw [hChL]; omega))
    fun st₃ hpc₃ hrsp₃ C₃ hs₃ hhash₃ K₃ => ?_
  -- Block 25.
  have hr12₃ : reg st₃.data .r12 = BitVec.ofNat 64 (z + 1) :=
    (hs₃ .r12 rfl (by decide)).trans ((hs₂.1 .r12 rfl).trans ((hm₁.regs _ _ g12).trans h.r12))
  have hr14₃ : reg st₃.data .r14 = ad m₀ (fr + 4556 + 16 * z) :=
    (hs₃ .r14 rfl (by decide)).trans ((hs₂.1 .r14 rfl).trans ((hm₁.regs _ _ f14).trans
      ((eval_ptr1 0).trans (congrArg (ad m₀) (by omega)))))
  have hrbx₃ : reg st₃.data .rbx = BitVec.ofNat 64 (li1 w).toNat :=
    (hs₃ .rbx rfl (by decide)).trans ((hs₂.1 .rbx rfl).trans ((hm₁.regs _ _ gbx).trans h.rbx))
  have hr13₃ : reg st₃.data .r13 = ad m₀ (fr + 120) :=
    (hs₃ .r13 rfl (by decide)).trans ((hs₂.1 .r13 rfl).trans (hx f13))
  have hrbp₃ : reg st₃.data .rbp = ad m₀ (fr + 608) := (hs₃ .rbp rfl (by decide)).trans hrbp₂
  have hr15₃ : reg st₃.data .r15 = ad m₀ (fr + 184) := (hs₃ .r15 rfl (by decide)).trans hr15₂
  let env₃ := Env.ofMachine st₃.data (frameRs m₀) (fun _ => 0) 0
  have hwf₃ : env₃.WF := frameG_wf P C₃.kept
  have hm₃ : Match env₃ (stF []) st₃.data := match_stG P C₃.same hrsp₃ trivial
  obtain ⟨esp, ecx, edx, e12, e14, ekeep, emem⟩ := st25_facts
  refine exec_at (b25_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b25' hwf₃
    (fun _ h => nomatch h) (hpc₃.trans rfl) hm₃ fun st₄ hm₄ hpc₄ => ?_
  have hv12 : (Sym.bin .add .W64 (.reg .r12) (.lit 1)).eval env₃ = BitVec.ofNat 64 (z + 1 + 1) :=
    add1_eval hr12₃
  have hc : (SBool.not (.cmp .eq .W64 (.bin .add .W64 (.reg .r12) (.lit 1)) (.lit 17))).eval
      env₃ = !decide (z + 1 = 16) := by
    simp only [SBool.eval, CmpOp.apply]
    rw [hv12]
    exact congrArg (!·) (beq17 hz)
  simp only [PcOk, hc] at hpc₄
  refine cont st₄ ?_ ?_
  · rw [hpc₄]
    by_cases h16 : z + 1 = 16
    · simp only [h16, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      rfl
    · simp only [h16, decide_false, Bool.not_false, ite_true, ite_false]
      exact hp.label NativeRustcX64.Xmss.XmssVerify.label_7_at
  have hd₄ : st₄.data.dmem = st₃.data.dmem := hm₄.dmem_eq hwf₃ emem
  have hreg : ∀ r ∈ [Reg64.rbx, .rbp, .r13, .r15], reg st₄.data r = reg st₃.data r :=
    fun r hr => hm₄.regs _ _ (ekeep r hr)
  have hhash : (Keccak.hashBytes (pp w ++ address (tweak 3 (layerHi 1 (z + 1).toUInt32)
      ((li1 w).toNat >>> (z + 1)).toUInt32) ++ (if (li1 w).toNat >>> z &&& 1 = 0 then
      pf (pp w) 1 (li1 w).toNat (topL w).path leaf z ++ (topL w).path.getD z []
      else (topL w).path.getD z [] ++ pf (pp w) 1 (li1 w).toNat (topL w).path leaf z))).take 16
      = pf (pp w) 1 (li1 w).toNat (topL w).path leaf (z + 1) := by
    rw [pf_succ]
    rfl
  have hl32 := length_hashBytes (pp w ++ address (tweak 3 (layerHi 1 (z + 1).toUInt32)
      ((li1 w).toNat >>> (z + 1)).toUInt32) ++ (if (li1 w).toNat >>> z &&& 1 = 0 then
      pf (pp w) 1 (li1 w).toNat (topL w).path leaf z ++ (topL w).path.getD z []
      else (topL w).path.getD z [] ++ pf (pp w) 1 (li1 w).toNat (topL w).path leaf z))
  refine ⟨C₃.congr hd₄, (hm₄.regs _ _ esp).trans (eval_ptr0 24),
    (hm₄.regs _ _ e12).trans hv12, (hreg .rbx (by simp)).trans hrbx₃,
    (hreg .r13 (by simp)).trans hr13₃, ?_, (hreg .rbp (by simp)).trans hrbp₃,
    (hreg .r15 (by simp)).trans hr15₃,
    hd₄ ▸ K₃ _ _ (by omega) (by simp [length_pkB]) (by simp [length_pkB]) hpk₂,
    hd₄ ▸ K₃ _ _ (by omega) (by simp [hlen1]) (by omega)
      (hk₂ htop₁ (by simp [hlen1]) (by omega) (by omega)), ?_⟩
  · rw [show reg st₄.data .r14 = _ from hm₄.regs _ _ e14]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 16) (reg st₃.data .r14) = _
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [hr14₃, BitVec.add_comm, ad_add]
    exact congrArg (ad m₀) (by omega)
  · rw [show reg st₄.data .rcx = _ from hm₄.regs _ _ ecx,
      show reg st₄.data .rdx = _ from hm₄.regs _ _ edx]
    exact (regs16 hl32 hhash₃).trans hhash

/-- **The loop over the top layer's path**: its 16 turns, from `TreeAt1` at level `0` at block 19
to `TreeAt1` at level `16` at block 26. -/
public theorem loop1 {k : Nat} (hp : Placed code k)
    (hset : Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost)
    (hupd : Spec (label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost)
    (hcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hfin : Spec (label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre FinalizePost) (P : Pre w m₀)
    {leaf : List UInt8} (hleaf : leaf.length = 16) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b19Offset)) (h : TreeAt1 w m₀ leaf st.data 0) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b26Offset) ∧
      TreeAt1 w m₀ leaf st'.data 16) st :=
  Sym.loop (I := fun n s => ∃ z, z + n = 16 ∧ 0 < n ∧ s.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b19Offset) ∧
      TreeAt1 w m₀ leaf s.data z)
    (fun n _ ⟨z, hn, hn0, hpc, h⟩ => turn1 hp hset hupd hcpy hfin P hleaf (by omega) hpc h
      fun st' hpc' h' => .done _ (by
        by_cases h16 : z + 1 = 16
        · simp only [h16, ↓reduceIte] at hpc'
          exact Or.inl ⟨hpc', h16 ▸ h'⟩
        · simp only [h16, ↓reduceIte] at hpc'
          exact Or.inr ⟨n - 1, by omega, z + 1, by omega, by omega, hpc', h'⟩))
    (n := 16) ⟨0, rfl, by decide, hpc, h⟩

end NativeRustcX64.Xmss.XmssVerify
