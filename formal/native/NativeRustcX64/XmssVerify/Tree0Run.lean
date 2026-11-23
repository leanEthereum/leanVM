module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names
public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.XmssVerify.Tree0

/-!
# `xmss_verify`: the loop over the bottom layer's path (x86-64)

`turn0`: blocks 9 to 15 with the calls between them (`NativeRustcX64.XmssVerify.Tree0`), from
`TreeAt0` at level `z < 16` to `TreeAt0` at `z + 1`, back at block 9 or, at `z + 1 = 16`, on at
block 16. `loop0`: the 16 turns.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

public section

theorem u32W_eq (x : UInt64) : u32W x = BitVec.ofNat 64 (x.toNat % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [u32W, BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt64.toNat]

theorem li_toNat (w : Nat → UInt64) : (li w).toNat = (w 8).toNat % 2 ^ 32 := by
  rw [li, UInt64.toNat_toUInt32]

theorem li_lt (w : Nat → UInt64) : (li w).toNat < 2 ^ 32 := (li w).toNat_lt

/-- A layer's path node `j`: 16 bytes. -/
theorem path_len {bs : List UInt8} {c : Nat} (hc : c + 1200 ≤ bs.length) {j : Nat} (hj : j < 16) :
    ((takeLayer bs c).1.path.getD j []).length = 16 := by
  simp only [takeLayer, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]
  exact length_slice (by omega)

theorem pp_at {w : Nat → UInt64} {m₀ : MachineData} {d : DataMem}
    (h : BytesAt d (ad m₀ (fr + 40)) (pkB w)) : BytesAt d (ad m₀ (fr + 56)) (pp w) := by
  have := bytes_drop h 16
  rwa [show fr + 40 + 16 = fr + 56 by omega] at this

theorem length_pp (w : Nat → UInt64) : (pp w).length = 16 := by
  rw [pp, List.length_drop, length_pkB]

theorem length_address (tw : Tweak) : (address tw).length = 16 := by
  simp [address, length_u32Bytes]

theorem beq16 {z : Nat} (hz : z < 16) :
    (BitVec.ofNat 64 (z + 1) == BitVec.ofNat 64 16) = decide (z + 1 = 16) := by
  by_cases h : z + 1 = 16
  · rw [h]; rfl
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h'
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    omega

variable [Labels] {env : Env}

/-- The high field's bytes of a bottom node's address. -/
theorem hi0_eval {z : Nat} (hz : z < 16) (h : rbp1.eval env = BitVec.ofNat 64 (z + 1)) :
    [UInt8.ofNat ((Sym.un .trunc .W16 rbp1).eval env).toNat,
      UInt8.ofNat (((Sym.un .trunc .W16 rbp1).eval env).toNat / 256),
      UInt8.ofNat ((Sym.un .trunc .W8 (.bin .shr .W32 (.un .trunc .W32 rbp1) (.lit 16))).eval
        env).toNat] = (u32Bytes (layerHi 0 (z + 1).toUInt32)).take 3 := by
  have e1 : ((Sym.un .trunc .W16 rbp1).eval env).toNat = (z + 1) % 2 ^ 16 := by
    show (UnOp.apply .trunc .W16 (rbp1.eval env)).toNat = _
    rw [trunc_toNat, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show z + 1 < 2 ^ 64 by omega)]
  have e2 : ((Sym.un .trunc .W8 (.bin .shr .W32 (.un .trunc .W32 rbp1) (.lit 16))).eval
      env).toNat = (z + 1) % 2 ^ 32 / 2 ^ 16 % 2 ^ 8 := by
    show (UnOp.apply .trunc .W8 (BinOp.apply .shr .W32 (UnOp.apply .trunc .W32 (rbp1.eval env))
      (BitVec.ofNat 64 16))).toNat = _
    rw [trunc_toNat, shr16_toNat, trunc_toNat, h, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show z + 1 < 2 ^ 64 by omega)]
    show (z + 1) % 2 ^ 32 % 2 ^ 32 / 2 ^ 16 % 2 ^ 8 = _
    rw [Nat.mod_mod]
  rw [e1, e2]
  exact hiBytes_bottom z hz

end

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

set_option linter.unusedSimpArgs false in
/-- **A turn over the bottom layer's path**: from `TreeAt0` at level `z < 16` at block 9 to
`TreeAt0` at `z + 1`, at block 9 again or, at `z + 1 = 16`, at block 16. -/
public theorem turn0 {k : Nat} (hp : Placed code k)
    (hset : Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost)
    (hupd : Spec (label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost)
    (hcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hfin : Spec (label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre FinalizePost) (P : Pre w m₀)
    {leaf : List UInt8} (hleaf : leaf.length = 16) {z : Nat} (hz : z < 16)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b9Offset)) (h : TreeAt0 w m₀ leaf st.data z)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState,
      st'.pc = (if z + 1 = 16 then Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b16Offset) else Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b9Offset)) →
      TreeAt0 w m₀ leaf st'.data (z + 1) → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have C := h.common
  have hc4 : 4 + 1200 ≤ (sigB w).length := by rw [length_sigB]; omega
  have hpath : BytesAt st.data.dmem (ad m₀ (fr + (3356 + 16 * z)))
      ((bottomL w).path.getD z []) := by
    have := layer_path (bs := sigB w) (c := 4) hc4 h.bottom hz
    rwa [ad_add, Nat.add_assoc] at this
  have hsibL : ((bottomL w).path.getD z []).length = 16 := path_len hc4 hz
  have hcurL := length_pf (pp w) 0 (li w).toNat (bottomL w).path hleaf z
  have hlen0 : (bottomL w).memBytes.length = 1200 := length_memBytes hc4
  have hlen1 : (topL w).memBytes.length = 1200 := length_memBytes (by simp [length_sigB])
  -- Block 9.
  let env := Env.ofMachine st.data (nodeR m₀ (3356 + 16 * z)) (fun _ => 0)
    (Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b9Offset + b9.length)).toBitVec
  have hwf : env.WF := node_wf P C.kept (by omega) (by omega)
  have hm : Match env st9 st.data :=
    match_stN P C.same ⟨h.rsp.trans (eval_ptr0 24).symm,
      h.r12.trans ((congrArg (ad m₀) (by omega)).trans (eval_ptr1 0).symm),
      h.r15.trans (eval_ptr0 184).symm, trivial⟩
  obtain ⟨f0, f1, f2, fsp, fbp, g14, g12, g15, gbx, fw, flow⟩ := st9_regs
  obtain ⟨c0, c1, c2, c3⟩ := st9_children
  obtain ⟨a1, a2, a3, a4, a5⟩ := st9_addr
  refine call_step (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b9 hwf rfl hpc hm
    fun st₁ hpc₁ hm₁ => ?_
  change Match _ (after b9 st9) st₁.data at hm₁
  have C₁ := Common.block P C hwf hm₁ fw
  have hx : ∀ {r : Reg64} {o : Nat}, (after b9 st9).reg r = some (.ptr 0 o) →
      reg st₁.data r = ad m₀ (fr + o) := fun hr => (hm₁.regs _ _ hr).trans (eval_ptr0 _)
  have hrsp₁ : rspOf st₁.data = ad m₀ (fr + 16) := hx fsp
  have hrbp : (Sym.reg .rbp).eval env = BitVec.ofNat 64 z := h.rbp
  have hrbx : env.regs .rbx = BitVec.ofNat 64 (li w).toNat := by
    rw [li_toNat]; exact h.rbx.trans (u32W_eq _)
  have hv1 : rbp1.eval env = BitVec.ofNat 64 (z + 1) := add1_eval hrbp
  have hrbp₁ : reg st₁.data .rbp = BitVec.ofNat 64 (z + 1) := (hm₁.regs _ _ fbp).trans hv1
  have hlo : ((loW rbp1).eval env).toNat = (li w).toNat >>> (z + 1) :=
    loW_toNat hv1 (by omega) hrbx (li_lt w)
  have hhi := hi0_eval (env := env) hz hv1
  have hA₁ := addrAt hm₁ (by omega) a1 a2 a3 a4 a5 hlo hhi
  have hcur := halves h.cur
  have hsib := halves hpath
  have l1 : ((pf (pp w) 0 (li w).toNat (bottomL w).path leaf z).take 8).length = 8 := by
    rw [List.length_take, hcurL]; rfl
  have l2 : (((pf (pp w) 0 (li w).toNat (bottomL w).path leaf z).drop 8).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hcurL]; rfl
  have l3 : (((bottomL w).path.getD z []).take 8).length = 8 := by
    rw [List.length_take, hsibL]; rfl
  have l4 : ((((bottomL w).path.getD z []).drop 8).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hsibL]; rfl
  have r0 : regBytes ((Sym.load 0 592 8).eval env) =
      (pf (pp w) 0 (li w).toNat (bottomL w).path leaf z).take 8 := regBytes_frame l1 hcur.1
  have r1 : regBytes ((Sym.load 0 600 8).eval env) =
      ((pf (pp w) 0 (li w).toNat (bottomL w).path leaf z).drop 8).take 8 :=
    regBytes_frame l2 hcur.2
  have r2 : regBytes ((Sym.load 1 0 8).eval env) = ((bottomL w).path.getD z []).take 8 :=
    regBytes_node l3 (by rw [Nat.add_zero]; exact hsib.1)
  have r3 : regBytes ((Sym.load 1 8 8).eval env) =
      (((bottomL w).path.getD z []).drop 8).take 8 := regBytes_node l4 hsib.2
  have hCh₁ := childrenAt hm₁ (by omega) c0 c1 c2 c3
    (cur := pf (pp w) 0 (li w).toNat (bottomL w).path leaf z)
    (sib := (bottomL w).path.getD z [])
    (by rw [r0, r1, List.take_of_length_le (l := List.drop 8 _) (by rw [List.length_drop, hcurL]),
      List.take_append_drop])
    (by rw [r2, r3, List.take_of_length_le (l := List.drop 8 _) (by rw [List.length_drop, hsibL]),
      List.take_append_drop])
  rw [bitC_eval hrbp (by omega) hrbx (li_lt w)] at hCh₁
  simp only [decide_eq_true_eq] at hCh₁
  have hChL : (if (li w).toNat >>> z &&& 1 = 0 then
      pf (pp w) 0 (li w).toNat (bottomL w).path leaf z ++ (bottomL w).path.getD z []
      else (bottomL w).path.getD z [] ++ pf (pp w) 0 (li w).toNat (bottomL w).path leaf z).length =
      32 := by
    split <;> rw [List.length_append, hcurL, hsibL]
  have hk₁ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st.data.dmem (ad m₀ (fr + x)) bs →
      40 ≤ x → x + bs.length ≤ 88 → BytesAt st₁.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb hx hle => frame_keep2 P hwf hm₁ flow hb hx hle (by omega)
  have hpk₁ := hk₁ h.pk le_rfl (by simp [length_pkB])
  have hw8₁ := hk₁ h.w8 (by omega) (by simp [length_regBytes])
  have hbot₁ := frame_keep P hwf hm₁ fw h.bottom (by omega) (by simp [hlen0])
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
  have hr15₂ : reg st₂.data .r15 = ad m₀ (fr + 184) := (hs₂.1 .r15 rfl).trans (hx g15)
  -- Blocks 10 to 14: the node's hash.
  refine hashNode hupd hcpy hfin P (X := .r13) (H := .r13) (j := k + NativeRustcX64.Xmss.XmssVerify.b10Offset)
    (b10_in_code.trans hp.1 (List.cons_ne_nil _ _)) (b11_in_code.trans hp.1 (List.cons_ne_nil _ _))
    (b12_in_code.trans hp.1 (List.cons_ne_nil _ _)) (b13_in_code.trans hp.1 (List.cons_ne_nil _ _))
    (b14_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b10' f10 run_b11' f11 run_b12' f12
    run_b13' f13 run_b14' f14 rfl (by decide) (hpc₂.trans rfl) C₂ hrsp₂ hr15₂
    (fun _ _ hs => ⟨((hs .r15 rfl (by decide)).trans hr15₂).trans (eval_ptr0 184).symm, trivial⟩)
    (length_pp w) (length_address _) hChL
    hh₂ (pp_at (hk₂ hpk₁ (by simp [length_pkB]) (by omega) (by simp [length_pkB])))
    (hk₂ hA₁ (by simp [length_address]) (by omega) (by simp [length_address]))
    (hk₂ hCh₁ (by rw [hChL]; omega) (by omega) (by rw [hChL]; omega))
    fun st₃ hpc₃ hrsp₃ C₃ hs₃ hhash₃ K₃ => ?_
  -- Block 15.
  have hr14₃ : reg st₃.data .r14 = ad m₀ (fr + 592) :=
    (hs₃ .r14 rfl (by decide)).trans ((hs₂.1 .r14 rfl).trans (hx g14))
  have hr12₃ : reg st₃.data .r12 = ad m₀ (fr + (3356 + 16 * z) + 0) :=
    (hs₃ .r12 rfl (by decide)).trans ((hs₂.1 .r12 rfl).trans
      ((hm₁.regs _ _ g12).trans (eval_ptr1 0)))
  have hrbp₃ : reg st₃.data .rbp = BitVec.ofNat 64 (z + 1) :=
    (hs₃ .rbp rfl (by decide)).trans ((hs₂.1 .rbp rfl).trans hrbp₁)
  have hrbx₃ : reg st₃.data .rbx = u32W (w 8) :=
    (hs₃ .rbx rfl (by decide)).trans ((hs₂.1 .rbx rfl).trans ((hm₁.regs _ _ gbx).trans h.rbx))
  have hr15₃ : reg st₃.data .r15 = ad m₀ (fr + 184) := (hs₃ .r15 rfl (by decide)).trans hr15₂
  let env₃ := Env.ofMachine st₃.data (nodeR m₀ (3356 + 16 * z)) (fun _ => 0) 0
  have hwf₃ : env₃.WF := node_wf P C₃.kept (by omega) (by omega)
  have hm₃ : Match env₃ st15 st₃.data :=
    match_stN P C₃.same ⟨hrsp₃.trans (eval_ptr0 24).symm,
      hr14₃.trans (eval_ptr0 592).symm, hr12₃.trans (eval_ptr1 0).symm, trivial⟩
  obtain ⟨esp, e12, ekeep, ew, elow, e592, e600⟩ := st15_facts
  refine exec_at (b15_in_code.trans hp.1 (List.cons_ne_nil _ _)) run_b15' hwf₃
    (fun _ h => nomatch h) (hpc₃.trans rfl) hm₃ fun st₄ hm₄ hpc₄ => ?_
  have hc : (SBool.not (.cmp .eq .W64 (.reg .rbp) (.lit 16))).eval env₃ = !decide (z + 1 = 16) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval]
    rw [show env₃.regs .rbp = BitVec.ofNat 64 (z + 1) from hrbp₃]
    exact congrArg (!·) (beq16 hz)
  simp only [PcOk, hc] at hpc₄
  refine cont st₄ ?_ ?_
  · rw [hpc₄]
    by_cases h16 : z + 1 = 16
    · simp only [h16, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      rfl
    · simp only [h16, decide_false, Bool.not_false, ite_true, ite_false]
      exact hp.label NativeRustcX64.Xmss.XmssVerify.label_4_at
  have hreg : ∀ r ∈ [Reg64.rbx, .rbp, .r15], reg st₄.data r = reg st₃.data r :=
    fun r hr => hm₄.regs _ _ (ekeep r hr)
  have hk₄ : ∀ {x : Nat} {bs : List UInt8}, BytesAt st₃.data.dmem (ad m₀ (fr + x)) bs →
      24 ≤ x → x + bs.length ≤ 592 → BytesAt st₄.data.dmem (ad m₀ (fr + x)) bs :=
    fun hb hx hle => frame_keep2 P hwf₃ hm₄ elow hb hx hle (by omega)
  have hhash : (Keccak.hashBytes (pp w ++ address (tweak 3 (layerHi 0 (z + 1).toUInt32)
      ((li w).toNat >>> (z + 1)).toUInt32) ++ (if (li w).toNat >>> z &&& 1 = 0 then
      pf (pp w) 0 (li w).toNat (bottomL w).path leaf z ++ (bottomL w).path.getD z []
      else (bottomL w).path.getD z [] ++ pf (pp w) 0 (li w).toNat (bottomL w).path leaf z))).take 16
      = pf (pp w) 0 (li w).toNat (bottomL w).path leaf (z + 1) := by
    rw [pf_succ]
    rfl
  have hl32 := length_hashBytes (pp w ++ address (tweak 3 (layerHi 0 (z + 1).toUInt32)
      ((li w).toNat >>> (z + 1)).toUInt32) ++ (if (li w).toNat >>> z &&& 1 = 0 then
      pf (pp w) 0 (li w).toNat (bottomL w).path leaf z ++ (bottomL w).path.getD z []
      else (bottomL w).path.getD z [] ++ pf (pp w) 0 (li w).toNat (bottomL w).path leaf z))
  refine ⟨Common.block P C₃ hwf₃ hm₄ ew, (hm₄.regs _ _ esp).trans (eval_ptr0 24),
    (hreg .rbp (by simp)).trans hrbp₃, (hreg .rbx (by simp)).trans hrbx₃,
    (hm₄.regs _ _ e12).trans ((eval_ptr1 16).trans (congrArg (ad m₀) (by omega))),
    (hreg .r15 (by simp)).trans hr15₃,
    hk₄ (K₃ _ _ (by omega) (by simp [length_pkB]) (by simp [length_pkB])
      (hk₂ hpk₁ (by simp [length_pkB]) (by omega) (by simp [length_pkB])))
      (by omega) (by simp [length_pkB]),
    hk₄ (K₃ _ _ (by omega) (by simp [length_regBytes]) (by simp [length_regBytes])
      (hk₂ hw8₁ (by simp [length_regBytes]) (by omega) (by simp [length_regBytes])))
      (by omega) (by simp [length_regBytes]),
    frame_keep P hwf₃ hm₄ ew (K₃ _ _ (by omega) (by simp [hlen0]) (by omega)
      (hk₂ hbot₁ (by simp [hlen0]) (by omega) (by omega))) (by omega) (by simp [hlen0]),
    frame_keep P hwf₃ hm₄ ew (K₃ _ _ (by omega) (by simp [hlen1]) (by omega)
      (hk₂ htop₁ (by simp [hlen1]) (by omega) (by omega))) (by omega) (by simp [hlen1]), ?_⟩
  rw [← hhash]
  exact copy16 hm₄ (by omega) e592 e600 hl32 hhash₃

/-- **The loop over the bottom layer's path**: its 16 turns, from `TreeAt0` at level `0` at
block 9 to `TreeAt0` at level `16` at block 16. -/
public theorem loop0 {k : Nat} (hp : Placed code k)
    (hset : Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost)
    (hupd : Spec (label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost)
    (hcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hfin : Spec (label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre FinalizePost) (P : Pre w m₀)
    {leaf : List UInt8} (hleaf : leaf.length = 16) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b9Offset)) (h : TreeAt0 w m₀ leaf st.data 0) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b16Offset) ∧
      TreeAt0 w m₀ leaf st'.data 16) st :=
  Sym.loop (I := fun n s => ∃ z, z + n = 16 ∧ 0 < n ∧ s.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b9Offset) ∧
      TreeAt0 w m₀ leaf s.data z)
    (fun n _ ⟨z, hn, hn0, hpc, h⟩ => turn0 hp hset hupd hcpy hfin P hleaf (by omega) hpc h
      fun st' hpc' h' => .done _ (by
        by_cases h16 : z + 1 = 16
        · simp only [h16, ↓reduceIte] at hpc'
          exact Or.inl ⟨hpc', h16 ▸ h'⟩
        · simp only [h16, ↓reduceIte] at hpc'
          exact Or.inr ⟨n - 1, by omega, z + 1, by omega, by omega, hpc', h'⟩))
    (n := 16) ⟨0, rfl, by decide, hpc, h⟩

end NativeRustcX64.Xmss.XmssVerify
