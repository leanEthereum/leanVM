module

public import NativeRustcX64.SphincsVerify.Tree.Glue

/-!
# The one-time leaf's `th` (x86-64)

From layer `l`'s chain ends `e` at `28280` (`b151` .. `b157`, each ending in a call): the address
of type `WOTS_PK` at `8320`, hasher A (`4096`) zeroed, updated with `PK.seed` and the address,
cloned into hasher B (`576`), B updated with the ends and finalized into `10368`; the hash's first
16 bytes copied to `2112` and on to `9408` (the `memcpy` of 80 bytes from `2048` to `9344`). What
the stretch keeps (`LeafC`: `Base`, the leaf's spills `LeafX`, R12, R13, the ends) through a block
and its call (`LeafC.step`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcX64.Sphincs.SphincsVerify

public section

section
variable (r : Run) [Labels]

/-- The leaf's spills: the layer's word (`104`), the key pair's (`60`), the layer (`96`). -/
@[expose] def LeafX (l : Nat) (m : MachineData) : Prop :=
  BytesAt m.dmem (r.off 104) (be32 l.toUInt32) ∧ BytesAt m.dmem (r.off 60) (be32 (r.key l).leaf) ∧
    r.WordAt m 96 l.toUInt64

/-- **What the leaf's stretch keeps**: `Base`, `LeafX`, R12 hasher A, R13 `base + 2048`, the
ends. -/
@[expose] def LeafC (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  Base r l m ∧ LeafX r l m ∧ Run.RegIs m .r12 (r.off 4096) ∧ Run.RegIs m .r13 (r.off 2048) ∧
    BytesAt m.dmem (r.off 28280) e.flatten ∧ e.flatten.length = 1024 ∧
    Run.RegIs m .rbx (Labels.label "memset").toBitVec

end

/-- No write of a block reaches the leaf's spills or the ends. -/
@[expose] def leafW (S : SState) : Bool :=
  Run.noWriteIn S 60 4 && Run.noWriteIn S 96 12 && Run.noWriteIn S 28280 1024

section
variable {r : Run} [Labels]

/-- The state at a block's call: at a call, `Keep`, `LeafX`, the registers, the ends. -/
@[expose] def LeafAt (r : Run) (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  r.AtCall m ∧ Keep r l m ∧ LeafX r l m ∧ Run.RegIs m .rbp (r.off 576) ∧
    Run.RegIs m .r12 (r.off 4096) ∧ Run.RegIs m .r13 (r.off 2048) ∧
    BytesAt m.dmem (r.off 28280) e.flatten ∧
    Run.RegIs m .rbx (Labels.label "memset").toBitVec ∧ Run.RegIs m .r14 (Labels.label "memcpy").toBitVec

/-- **A block of the leaf's stretch**, ending in a call. -/
theorem LeafC.block (hpre : r.Pre) {l : Nat} {e : List (List UInt8)} {m m' : MachineData}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (h : LeafC r l e m)
    (hm : Match (r.env m vars ret) S m') (hwf : (r.env m vars ret).WF)
    (hsp : S.reg .rsp = some (.ptr 0 (-8))) (hw : Run.frameWrites S = true) (hk : keepW S = true)
    (hl : leafW S = true) (hbp : S.reg .rbp = some (.ptr 0 576))
    (h12 : S.reg .r12 = some (.ptr 0 4096)) (h13 : S.reg .r13 = some (.ptr 0 2048))
    (hbx : S.reg .rbx = some (.label "memset") := by rfl)
    (h14 : S.reg .r14 = some (.label "memcpy") := by rfl) :
    LeafAt r l e m' := by
  obtain ⟨hB, ⟨h104, h60, h96⟩, -, -, hE, hEl, -⟩ := h
  simp only [leafW, Bool.and_eq_true] at hl
  obtain ⟨⟨n60, n96⟩, nE⟩ := hl
  have k := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (h : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn S o bs.length = true) ↦
    r.bytesAt_kept hpre hm hwf ho h hn
  have n96' : ∀ o, 96 ≤ o → o + 4 ≤ 108 → ∀ k, o + k ≤ 108 → Run.noWriteIn S o k = true := by
    intro o h1 h2 k' hk'
    simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at n96 ⊢
    intro w hw'
    rcases n96 w hw' with ⟨h0, h | h⟩ | h
    · exact Or.inl ⟨h0, Or.inl (by omega)⟩
    · exact Or.inl ⟨h0, Or.inr (by omega)⟩
    · exact Or.inr h
  refine ⟨hB.atCall hpre hm hwf hsp hw, hB.2.2.1.of_match hpre hm hwf hk,
    ⟨k (by simp [be32]) h104 (n96' 104 (by decide) (by decide) _ (by simp [be32])),
     k (by simp [be32]) h60 (by simpa [be32] using n60),
     k (by rw [length_wordBytes]; decide) h96
      (n96' 96 (by decide) (by decide) _ (by rw [length_wordBytes]; decide))⟩,
    (hm.regs _ _ hbp).trans (eval_ptr 576), (hm.regs _ _ h12).trans (eval_ptr 4096),
    (hm.regs _ _ h13).trans (eval_ptr 2048), k (by omega) hE (by rw [hEl]; exact nE),
    hm.regs .rbx _ hbx, hm.regs .r14 _ h14⟩

/-- **After the call** that changed the frame's bytes `a .. a + n` above the spills. -/
theorem LeafAt.post (hpre : r.Pre) {l : Nat} {e : List (List UInt8)} {m m' : MachineData}
    (hl : l < 3) (hEl : e.flatten.length = 1024) (h : LeafAt r l e m) (hS : Saved m m')
    (hsp : rspOf m' = rspOf m + 8#64) {a n N : Nat} (ha : 576 ≤ a) (han : a + n ≤ 20540)
    (hN : N ≤ finalizeStack) (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) :
    LeafC r l e m' := by
  obtain ⟨hc, hK, ⟨h104, h60, h96⟩, hbp, h12, h13, hE, hbx, h14⟩ := h
  have k := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hd : o + bs.length ≤ a ∨ a + n ≤ o) (h : BytesAt m.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hc (by omega) hN hout ho hd h
  exact ⟨Base.of_call hpre hl hc hK hbp h14 hS hsp ha han hN hout,
    ⟨k (by simp [be32]) (by simp [be32]; omega) h104, k (by simp [be32]) (by simp [be32]; omega) h60,
     k (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; omega) h96⟩,
    regIs_of_saved rfl h12 hS, regIs_of_saved rfl h13 hS,
    k (by omega) (by omega) hE, hEl, regIs_of_saved rfl hbx hS⟩

end

/-! ## The stages -/

variable [Host] {r : Run}

theorem frame_wf' (hpre : r.Pre) {l : Nat} {m : MachineData} (hB : Base r l m) (ret : BitVec 64) :
    (r.env m (fun _ ↦ 0) ret).WF :=
  r.frame_wf hpre hB.2.1.2.2.2 _ _

/-- A fresh state of the leaf's stretch. -/
theorem match_leaf (hpre : r.Pre) {l : Nat} {e : List (List UInt8)} {m : MachineData}
    (h : LeafC r l e m) (ret : BitVec 64) : Match (r.env m (fun _ ↦ 0) ret) wotsS m :=
  r.match_frame hpre h.1.2.1
    (show AllOf _ [(Reg64.r14, Sym.label "memcpy"), (.r12, .ptr 0 4096),
      (.rbp, .ptr 0 576), (.r13, .ptr 0 2048), (.rbx, .label "memset")] from
      ⟨h.1.2.2.2.2, h.2.2.1.trans (eval_ptr 4096).symm,
        h.1.2.2.2.1.trans (eval_ptr 576).symm,
        h.2.2.2.1.trans (eval_ptr 2048).symm, h.2.2.2.2.2.2, trivial⟩) trivial trivial trivial

/-- **`b151` and `memset`**: the address at `8320`, hasher A zero. -/
theorem stage1 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : r.AtWotsPk l e m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b152Offset ∧ LeafC r l e st.data ∧
      BytesAt st.data.dmem (r.off 8320) ((r.key l).adrs 1) ∧
      BytesAt st.data.dmem (r.off 4096) Keccak.new) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b151Offset⟩ := by
  obtain ⟨hl, hEl, hF, hIn, hSp, h12, hbp, h13, hE, hbx, h14⟩ := h
  obtain ⟨h96, h200, h208, h160, h216, h104, h88, h60, h568, -⟩ := hSp
  have hC : LeafC r l e m := ⟨⟨hl, hF, ⟨hIn, h88, h160, h200, h208, h216, h568⟩, hbp, h14⟩,
    ⟨h104, h60, h96⟩, h12, h13, hE, hEl, hbx⟩
  have hwf := frame_wf' hpre hC.1 (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b151Offset + b151.length)).toBitVec
  refine exec_then (hb151 hp) run_b151 hwf (fun _ _ ↦ rfl) (match_leaf hpre hC _) fun st hm hpc ↦ ?_
  have hA := hC.block hpre hm hwf rfl (by decide) (by decide) (by decide) rfl rfl rfl
  have h0 : Run.RegIs st.data .rdi (r.off 4096) := (hm.regs .rdi _ rfl).trans (eval_ptr 4096)
  have h1 : reg st.data .rsi = 0 := hm.regs .rsi _ rfl
  have h2 : (reg st.data .rdx).toNat = 344 := regIs_toNat (hm.regs .rdx _ rfl) (by decide)
  have hadr : BytesAt st.data.dmem (r.off 8320) ((r.key l).adrs 1) := by
    rw [keyAdrs_one, show (r.key l).layer = l from rfl]
    refine bytesAt_cat rfl (write_eval hm (o := 8320) (n := 4) (v := .load 0 104 4) (by decide)
      (by decide) rfl (bytes_load h104 rfl (by decide))) ?_
    refine bytesAt_cat rfl (write_eval hm (o := 8324) (n := 4) (v := .lit 0) (by decide)
      (by decide) rfl (by simp only [Sym.eval]; decide)) ?_
    refine bytesAt_cat rfl (write_eval hm (o := 8328) (n := 8) (v := .load 0 88 8) (by decide)
      (by decide) rfl (bytes_load h88 rfl (by decide))) ?_
    refine bytesAt_cat rfl (write_eval hm (o := 8336) (n := 4) (v := .lit 16777216) (by decide)
      (by decide) rfl (by simp only [Sym.eval]; decide)) ?_
    refine bytesAt_cat rfl (write_eval hm (o := 8340) (n := 4) (v := .load 0 60 4) (by decide)
      (by decide) rfl (bytes_load h60 rfl (by decide))) ?_
    exact write_eval hm (o := 8344) (n := 8) (v := .lit 0) (by decide) (by decide) rfl
      (by simp only [Sym.eval]; decide)
  refine call_then hpc hc.2.1 (r.memset_pre hpre hA.1 h0 h2 (by decide))
    fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hz, hout, hS⟩ := r.memset_out h0 h2 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b151_next),
    hA.post hpre hl hEl hS hsp (by decide) (by decide) (by decide) hout, ?_, ?_⟩
  · exact r.bytesAt_of_call hpre hA.1 (by decide) (by decide) hout (by rw [length_adrs]; decide)
      (by rw [length_adrs]; omega) hadr
  · rw [h1] at hz
    exact hz

/-- **`b152`**: `update` of hasher A with `PK.seed`. -/
theorem stage2 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : LeafC r l e m)
    (hA : BytesAt m.dmem (r.off 8320) ((r.key l).adrs 1))
    (hH : BytesAt m.dmem (r.off 4096) Keccak.new) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b153Offset ∧ LeafC r l e st.data ∧
      BytesAt st.data.dmem (r.off 8320) ((r.key l).adrs 1) ∧
      HasherHolds (bytesOf st.data.dmem (r.off 4096) 344) r.seed) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b152Offset⟩ := by
  have hwf := frame_wf' hpre h.1 (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b152Offset + b152.length)).toBitVec
  refine exec_then (hb152 hp) run_b152 hwf (fun _ _ ↦ rfl) (match_leaf hpre h _) fun st hm hpc ↦ ?_
  have hL := h.block hpre hm hwf rfl (by decide) (by decide) (by decide) rfl rfl rfl
  have h0 : Run.RegIs st.data .rdi (r.off 4096) := (hm.regs .rdi _ rfl).trans (eval_ptr 4096)
  have h1 : Run.RegIs st.data .rsi (r.off 112) := (hm.regs .rsi _ rfl).trans (eval_ptr 112)
  have h2 : (reg st.data .rdx).toNat = 16 := regIs_toNat (hm.regs .rdx _ rfl) (by decide)
  have k := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hb : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm hwf ho hb hn
  have hl : Keccak.new.length = 344 := List.length_replicate
  have hH1 : HasherHolds (bytesOf st.data.dmem (r.off 4096) 344) [] := by
    have := bytesOf_of_bytesAt (k (by rw [hl]; decide) hH (by rw [hl]; decide))
    rw [hl] at this
    rw [this]
    exact holds_new
  have hA1 := k (by rw [length_adrs]; decide) hA (by rw [length_adrs]; decide)
  have hseed : bytesOf st.data.dmem (r.off 112) 16 = r.seed := by
    have h1 := hL.2.1.1.1
    rw [← List.take_append_drop 16 (pkBytes r.w)] at h1
    have := bytesOf_of_bytesAt (bytesAt_append_left h1)
    rwa [List.length_take, length_pkBytes] at this
  refine call_then hpc hc.2.2.1 (r.update_pre hpre hL.1 h0 h1 h2 (by decide) (by decide)
    (by decide) ⟨_, hH1⟩) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hh, hout, hS⟩ := r.update_out h0 h1 h2 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b152_next),
    hL.post hpre h.1.1 h.2.2.2.2.2.1 hS hsp (by decide) (by decide) (by decide) hout,
    r.bytesAt_of_call hpre hL.1 (by decide) (by decide) hout (by rw [length_adrs]; decide)
      (by rw [length_adrs]; omega) hA1, ?_⟩
  have := hh [] hH1
  rwa [List.nil_append, hseed] at this

/-- **`b153`**: `update` of hasher A with the address. -/
theorem stage3 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : LeafC r l e m)
    (hA : BytesAt m.dmem (r.off 8320) ((r.key l).adrs 1))
    (hH : HasherHolds (bytesOf m.dmem (r.off 4096) 344) r.seed) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b154Offset ∧ LeafC r l e st.data ∧
      HasherHolds (bytesOf st.data.dmem (r.off 4096) 344) (r.seed ++ (r.key l).adrs 1))
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b153Offset⟩ := by
  have hwf := frame_wf' hpre h.1 (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b153Offset + b153.length)).toBitVec
  refine exec_then (hb153 hp) run_b153 hwf (fun _ _ ↦ rfl) (match_leaf hpre h _) fun st hm hpc ↦ ?_
  have hL := h.block hpre hm hwf rfl (by decide) (by decide) (by decide) rfl rfl rfl
  have h0 : Run.RegIs st.data .rdi (r.off 4096) := (hm.regs .rdi _ rfl).trans (eval_ptr 4096)
  have h1 : Run.RegIs st.data .rsi (r.off 8320) := (hm.regs .rsi _ rfl).trans (eval_ptr 8320)
  have h2 : (reg st.data .rdx).toNat = 32 := regIs_toNat (hm.regs .rdx _ rfl) (by decide)
  have hbo : ∀ {o n : Nat}, o + n ≤ 29384 → Run.noWriteIn _ o n = true →
      bytesOf st.data.dmem (r.off o) n = bytesOf m.dmem (r.off o) n := fun {o n} ho hn ↦ by
    have hmap := (r.frame_mapped hpre h.1.2.1.2.2.2 (a := o) (n := n) (by omega)).1
    have := r.bytesAt_kept hpre hm hwf (by rw [Hasher.length_bytesOf]; exact ho)
      (Hasher.bytesAt_bytesOf hmap) (by rw [Hasher.length_bytesOf]; exact hn)
    have := bytesOf_of_bytesAt this
    rwa [Hasher.length_bytesOf] at this
  have hH1 : HasherHolds (bytesOf st.data.dmem (r.off 4096) 344) r.seed := by
    rw [hbo (by decide) (by decide)]; exact hH
  have hadr : bytesOf st.data.dmem (r.off 8320) 32 = (r.key l).adrs 1 := by
    rw [hbo (by decide) (by decide)]
    have := bytesOf_of_bytesAt hA
    rwa [length_adrs] at this
  refine call_then hpc hc.2.2.1 (r.update_pre hpre hL.1 h0 h1 h2 (by decide) (by decide)
    (by decide) ⟨_, hH1⟩) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hh, hout, hS⟩ := r.update_out h0 h1 h2 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b153_next),
    hL.post hpre h.1.1 h.2.2.2.2.2.1 hS hsp (by decide) (by decide) (by decide) hout, ?_⟩
  have := hh _ hH1
  rwa [hadr] at this

/-- **`b154`**: hasher A cloned into hasher B. -/
theorem stage4 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : LeafC r l e m)
    (hH : HasherHolds (bytesOf m.dmem (r.off 4096) 344) (r.seed ++ (r.key l).adrs 1)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b155Offset ∧ LeafC r l e st.data ∧
      HasherHolds (bytesOf st.data.dmem (r.off 576) 344) (r.seed ++ (r.key l).adrs 1))
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b154Offset⟩ := by
  have hwf := frame_wf' hpre h.1 (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b154Offset + b154.length)).toBitVec
  refine exec_then (hb154 hp) run_b154 hwf (fun _ _ ↦ rfl) (match_leaf hpre h _) fun st hm hpc ↦ ?_
  have hL := h.block hpre hm hwf rfl (by decide) (by decide) (by decide) rfl rfl rfl
  have h0 : Run.RegIs st.data .rdi (r.off 576) := (hm.regs .rdi _ rfl).trans (eval_ptr 576)
  have h1 : Run.RegIs st.data .rsi (r.off 4096) := (hm.regs .rsi _ rfl).trans (eval_ptr 4096)
  have h2 : (reg st.data .rdx).toNat = 344 := regIs_toNat (hm.regs .rdx _ rfl) (by decide)
  have hmap := (r.frame_mapped hpre h.1.2.1.2.2.2 (a := 4096) (n := 344) (by decide)).1
  have hkp := r.bytesAt_kept hpre hm hwf (by rw [Hasher.length_bytesOf]; decide)
      (Hasher.bytesAt_bytesOf hmap) (by rw [Hasher.length_bytesOf]; decide)
  refine call_then hpc hc.1 (r.memcpy_pre hpre hL.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b154_next),
    hL.post hpre h.1.1 h.2.2.2.2.2.1 hS hsp (by decide) (by decide) (by decide) hout, ?_⟩
  have e1 := bytesOf_of_bytesAt hcp
  rw [Hasher.length_bytesOf] at e1
  have e2 := bytesOf_of_bytesAt hkp
  rw [Hasher.length_bytesOf] at e2
  rw [e1, e2]
  exact hH

/-- **`b155`**: `update` of hasher B with the chain ends. -/
theorem stage5 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : LeafC r l e m)
    (hH : HasherHolds (bytesOf m.dmem (r.off 576) 344) (r.seed ++ (r.key l).adrs 1)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b156Offset ∧ LeafC r l e st.data ∧
      HasherHolds (bytesOf st.data.dmem (r.off 576) 344) (r.seed ++ (r.key l).adrs 1 ++ e.flatten))
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b155Offset⟩ := by
  have hwf := frame_wf' hpre h.1 (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b155Offset + b155.length)).toBitVec
  refine exec_then (hb155 hp) run_b155 hwf (fun _ _ ↦ rfl) (match_leaf hpre h _) fun st hm hpc ↦ ?_
  have hL := h.block hpre hm hwf rfl (by decide) (by decide) (by decide) rfl rfl rfl
  have h0 : Run.RegIs st.data .rdi (r.off 576) := (hm.regs .rdi _ rfl).trans (eval_ptr 576)
  have h1 : Run.RegIs st.data .rsi (r.off 28280) := (hm.regs .rsi _ rfl).trans (eval_ptr 28280)
  have h2 : (reg st.data .rdx).toNat = 1024 := regIs_toNat (hm.regs .rdx _ rfl) (by decide)
  have hbo : ∀ {o n : Nat}, o + n ≤ 29384 → Run.noWriteIn _ o n = true →
      bytesOf st.data.dmem (r.off o) n = bytesOf m.dmem (r.off o) n := fun {o n} ho hn ↦ by
    have hmap := (r.frame_mapped hpre h.1.2.1.2.2.2 (a := o) (n := n) (by omega)).1
    have := r.bytesAt_kept hpre hm hwf (by rw [Hasher.length_bytesOf]; exact ho)
      (Hasher.bytesAt_bytesOf hmap) (by rw [Hasher.length_bytesOf]; exact hn)
    have := bytesOf_of_bytesAt this
    rwa [Hasher.length_bytesOf] at this
  have hH1 : HasherHolds (bytesOf st.data.dmem (r.off 576) 344) (r.seed ++ (r.key l).adrs 1) := by
    rw [hbo (by decide) (by decide)]; exact hH
  have hends : bytesOf st.data.dmem (r.off 28280) 1024 = e.flatten := by
    rw [hbo (by decide) (by decide), ← h.2.2.2.2.2.1]
    exact bytesOf_of_bytesAt h.2.2.2.2.1
  refine call_then hpc hc.2.2.1 (r.update_pre hpre hL.1 h0 h1 h2 (by decide) (by decide)
    (by decide) ⟨_, hH1⟩) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hh, hout, hS⟩ := r.update_out h0 h1 h2 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b155_next),
    hL.post hpre h.1.1 h.2.2.2.2.2.1 hS hsp (by decide) (by decide) (by decide) hout, ?_⟩
  have := hh _ hH1
  rwa [hends] at this

/-- **`b156`**: `finalize` of hasher B into `10368`. -/
theorem stage6 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : LeafC r l e m)
    (hH : HasherHolds (bytesOf m.dmem (r.off 576) 344) (r.seed ++ (r.key l).adrs 1 ++ e.flatten)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b157Offset ∧ LeafC r l e st.data ∧
      BytesAt st.data.dmem (r.off 10368) (hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten)))
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b156Offset⟩ := by
  have hwf := frame_wf' hpre h.1 (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b156Offset + b156.length)).toBitVec
  refine exec_then (hb156 hp) run_b156 hwf (fun _ _ ↦ rfl) (match_leaf hpre h _) fun st hm hpc ↦ ?_
  have hL := h.block hpre hm hwf rfl (by decide) (by decide) (by decide) rfl rfl rfl
  have h0 : Run.RegIs st.data .rdi (r.off 10368) := (hm.regs .rdi _ rfl).trans (eval_ptr 10368)
  have h1 : Run.RegIs st.data .rsi (r.off 576) := (hm.regs .rsi _ rfl).trans (eval_ptr 576)
  have hmap := (r.frame_mapped hpre h.1.2.1.2.2.2 (a := 576) (n := 344) (by decide)).1
  have hkp := r.bytesAt_kept hpre hm hwf (by rw [Hasher.length_bytesOf]; decide)
      (Hasher.bytesAt_bytesOf hmap) (by rw [Hasher.length_bytesOf]; decide)
  have e2 := bytesOf_of_bytesAt hkp
  rw [Hasher.length_bytesOf] at e2
  have hH1 : HasherHolds (bytesOf st.data.dmem (r.off 576) 344)
      (r.seed ++ (r.key l).adrs 1 ++ e.flatten) := by rw [e2]; exact hH
  refine call_then hpc hc.2.2.2.1 (r.finalize_pre hpre hL.1 h0 h1 (by decide) (by decide)
    (by decide) ⟨_, hH1⟩) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hf, hout, hS⟩ := r.finalize_out h0 h1 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b156_next),
    hL.post hpre h.1.1 h.2.2.2.2.2.1 hS hsp (by decide) (by decide) (by decide) hout, ?_⟩
  rw [finalize_eq hH1] at hf
  exact hf

/-- **`b157` and `memcpy`**: the hash's first 16 bytes to `2112` and on to `9408`. -/
theorem stage7 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : LeafC r l e m)
    (hH : BytesAt m.dmem (r.off 10368) (hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten))) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b158Offset ∧ LeafC r l e st.data ∧
      BytesAt st.data.dmem (r.off 9408) (wotsLeafHash r.seed (r.key l) e))
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b157Offset⟩ := by
  have hwf := frame_wf' hpre h.1 (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b157Offset + b157.length)).toBitVec
  refine exec_then (hb157 hp) run_b157 hwf (fun _ _ ↦ rfl) (match_leaf hpre h _) fun st hm hpc ↦ ?_
  have hL := h.block hpre hm hwf rfl (by decide) (by decide) (by decide) rfl rfl rfl
  have h0 : Run.RegIs st.data .rdi (r.off 9344) := (hm.regs .rdi _ rfl).trans (eval_ptr 9344)
  have h1 : Run.RegIs st.data .rsi (r.off 2048) := (hm.regs .rsi _ rfl).trans (eval_ptr 2048)
  have h2 : (reg st.data .rdx).toNat = 80 := regIs_toNat (hm.regs .rdx _ rfl) (by decide)
  have hlen : (hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten)).length = 32 :=
    NativeRustc.Sphincs.length_hashBytes _
  have hV : BytesAt st.data.dmem (r.off 2112) (wotsLeafHash r.seed (r.key l) e) := by
    show BytesAt _ _ ((hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten)).take 16)
    generalize hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten) = V at hH hlen ⊢
    have lo := bytes_load (vars := fun _ ↦ 0) (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b157Offset + b157.length)).toBitVec)
      (n := 8) (bytesAt_sub hH 0 8) (by simp [hlen]) (by decide)
    have hi := bytes_load (vars := fun _ ↦ 0) (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b157Offset + b157.length)).toBitVec)
      (n := 8) (bytesAt_sub hH 8 8) (by simp [hlen]) (by decide)
    rw [List.drop_zero] at lo
    rw [List.take_add (l := V) (i := 8) (j := 8)]
    refine bytesAt_cat (n := 8) (by simp [hlen]) (write_eval hm (o := 2112)
      (v := .load 0 10368 8) (by decide) (by decide) rfl lo) ?_
    exact write_eval hm (o := 2120) (v := .load 0 10376 8) (by decide) (by decide) rfl hi
  refine call_then hpc hc.1 (r.memcpy_pre hpre hL.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b157_next),
    hL.post hpre h.1.1 h.2.2.2.2.2.1 hS hsp (by decide) (by decide) (by decide) hout, ?_⟩
  have hs := bytesAt_sub hcp 64 16
  have hl16 : (wotsLeafHash r.seed (r.key l) e).length = 16 := length_th _ _ _
  rw [← Hasher.bytesOf_add _ _ (by decide : 64 + 16 ≤ 80), Run.off_add, ← hl16,
    bytesOf_of_bytesAt hV] at hs
  exact hs

end

end NativeRustcX64.SphincsVerifyProof.Tree
