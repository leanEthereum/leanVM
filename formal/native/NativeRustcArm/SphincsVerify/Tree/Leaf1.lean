module

public import NativeRustcArm.SphincsVerify.Tree.Glue

/-!
# The one-time leaf's `th`, first calls

From layer `l`'s chain ends `e` at `28208` (`b143`): the address of type `WOTS_PK` at `21648`
(`(r.key l).adrs 1`), hasher A (`16400`) zeroed by `memset` (`stage1`), then updated with
`PK.seed` (`b144`, `stage2`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

/-! ## Helpers -/

section
variable {r : Run}

/-- The pc after a block, from generated adjacency evidence. -/
theorem pc_after [Host] {k j j' : Nat} {ds : List Directive} (h : j + ds.length = j') :
    Host.addrOf (k + j + ds.length) = Host.addrOf (k + j') := by
  rw [Nat.add_assoc, h]

/-- **A write's bytes** in the frame. -/
theorem write_bytes [Labels] {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o n : Nat} {v : Sym} (hle : o + n ≤ 29376)
    (hw : ∀ i < n, findWrite 0 (o + i) S.mem = some (v, i)) {bs : List UInt8}
    (hbs : (List.range n).map (byteOf (v.eval (r.env m vars))) = bs) :
    BytesAt m'.dmem (r.off o) bs :=
  hbs ▸ hm.bytesAt_write rfl hle hw

/-- Two adjacent byte ranges of the frame. -/
theorem bytesAt_cat {d : DataMem} {o n : Nat} {p q : List UInt8} (hn : p.length = n)
    (hp : BytesAt d (r.off o) p) (hq : BytesAt d (r.off (o + n)) q) : BytesAt d (r.off o) (p ++ q) :=
  bytesAt_append hp (by rw [hn, r.off_add]; exact hq)

/-- `PK.seed`: the key's first 16 bytes. -/
theorem seed_bytes {m : MachineData} (h : r.Inputs m) : bytesOf m.dmem (r.off 8208) 16 = r.seed := by
  have h1 := h.1
  rw [← List.take_append_drop 16 (pkBytes r.w)] at h1
  have := bytesOf_of_bytesAt (bytesAt_append_left h1)
  rwa [List.length_take, length_pkBytes] at this

theorem regIs_toNat {m : MachineData} {x : XReg} {n : Nat} (h : (m.regs.getXReg x).toBitVec =
    BitVec.ofNat 64 n) (hn : n < 2 ^ 64) : (m.regs.getXReg x).toNat = n := by
  show (m.regs.getXReg x).toBitVec.toNat = n
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

end

theorem length_adrs (key : OtsKey) (t : UInt32) : (key.adrs t).length = 32 := rfl

variable [Host] (r : Run)

/-! ## The states -/

/-- At `b144`: the ends, the address, hasher A zero. -/
@[expose] def AtL1 (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  Base r l m ∧ BytesAt m.dmem (r.off 28208) e.flatten ∧ e.flatten.length = 1024 ∧
    BytesAt m.dmem (r.off 21648) ((r.key l).adrs 1) ∧ BytesAt m.dmem (r.off 16400) Keccak.new

/-- At `b145`: hasher A has absorbed `PK.seed`. -/
@[expose] def AtL2 (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  Base r l m ∧ BytesAt m.dmem (r.off 28208) e.flatten ∧ e.flatten.length = 1024 ∧
    BytesAt m.dmem (r.off 21648) ((r.key l).adrs 1) ∧
    HasherHolds (bytesOf m.dmem (r.off 16400) 344) r.seed

variable {r}

/-- **`b143` and `memset`.** -/
theorem stage1 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : r.AtWotsPk l e m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b144Offset ∧ AtL1 r l e st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b143Offset⟩ := by
  obtain ⟨hl, hF, hIn, hSp, h21, h25, h26, hE, hElen⟩ := h
  have hB : Base r l m := ⟨hl, hF, ⟨hIn, hSp⟩, h21, h25, h26⟩
  have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
  refine exec_then (hb143 hp) run_b143 hwf (match_base hpre hB) fun st hm hpc ↦ ?_
  have hB1 := Base.of_match hpre hB hm hwf rfl rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st.data .X0 (r.off 16400) := (hm.regs .X0 _ rfl).trans (eval_ptr 16400)
  have h1 : st.data.regs.X1 = 0 := UInt64.toBitVec_inj.mp (hm.regs .X1 _ rfl)
  have h2 : st.data.regs.X2.toNat = 344 := regIs_toNat (hm.regs .X2 _ rfl) (by decide)
  have hE1 : BytesAt st.data.dmem (r.off 28208) e.flatten :=
    r.bytesAt_kept hpre hm hwf (by omega) hE (by rw [hElen]; rfl)
  obtain ⟨-, -, -, -, -, -, -, -, h408, h416, h424⟩ := hSp
  have hA : BytesAt st.data.dmem (r.off 21648) ((r.key l).adrs 1) := by
    have hlay : (r.key l).layer = l := rfl
    rw [keyAdrs_one, hlay]
    refine bytesAt_cat rfl (write_bytes hm (o := 21648) (n := 4) (v := .load 0 416 4) (by decide)
      (by decide) (bytes_load h416 rfl (by decide))) ?_
    refine bytesAt_cat rfl (write_bytes hm (o := 21652) (n := 4) (v := .lit 0) (by decide)
      (by decide) (by simp only [Sym.eval]; decide)) ?_
    refine bytesAt_cat rfl (write_bytes hm (o := 21656) (n := 8) (v := .load 0 424 8) (by decide)
      (by decide) (bytes_load h424 rfl (by decide))) ?_
    refine bytesAt_cat rfl (write_bytes hm (o := 21664) (n := 4) (v := .lit 16777216) (by decide)
      (by decide) (by simp only [Sym.eval]; decide)) ?_
    refine bytesAt_cat rfl (write_bytes hm (o := 21668) (n := 4) (v := .load 0 408 4) (by decide)
      (by decide) (bytes_load h408 rfl (by decide))) ?_
    exact write_bytes hm (o := 21672) (n := 8) (v := .lit 0) (by decide) (by decide)
      (by simp only [Sym.eval]; decide)
  refine call_then hpc hc.2.1 (r.memset_pre hpre hB1.2.1 h0 h2 (by decide)) fun st' hpc' hpost ↦ ?_
  obtain ⟨hz, hout, hS⟩ := r.memset_out h0 h2 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b143_next), hB1.of_call hpre hS (by decide) (by decide)
    (by decide) hout, ?_, hElen, ?_, ?_⟩
  · exact r.bytesAt_of_call hpre hB1.2.1 (by decide) (by decide) hout (by omega)
      (by omega) hE1
  · exact r.bytesAt_of_call hpre hB1.2.1 (by decide) (by decide) hout (by rw [length_adrs]; omega)
      (by rw [length_adrs]; omega) hA
  · rw [h1] at hz
    exact hz

/-- **`b144`**: `update` of hasher A with `PK.seed`. -/
theorem stage2 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : AtL1 r l e m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b145Offset ∧ AtL2 r l e st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b144Offset⟩ := by
  obtain ⟨hB, hE, hElen, hA, hH⟩ := h
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  refine exec_then (hb144 hp) run_b144 hwf (match_base hpre hB) fun st hm hpc ↦ ?_
  have hB1 := Base.of_match hpre hB hm hwf rfl rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st.data .X0 (r.off 16400) := (hm.regs .X0 _ rfl).trans (eval_ptr 16400)
  have h1 : Run.RegIs st.data .X1 (r.off 8208) := (hm.regs .X1 _ rfl).trans (eval_ptr 8208)
  have h2 : st.data.regs.X2.toNat = 16 := regIs_toNat (hm.regs .X2 _ rfl) (by decide)
  have hd : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 29376 → BytesAt m.dmem (r.off o) bs →
      BytesAt st.data.dmem (r.off o) bs := fun ho h ↦ by
    rw [hm.dmem_eq hwf rfl]
    exact h
  have hH1 : HasherHolds (bytesOf st.data.dmem (r.off 16400) 344) [] := by
    have hl : Keccak.new.length = 344 := List.length_replicate
    have := bytesOf_of_bytesAt (hd (by rw [hl]; decide) hH)
    rw [hl] at this
    rw [this]
    exact holds_new
  refine call_then hpc hc.2.2.1 (r.update_pre hpre hB1.2.1 h0 h1 h2 (a := 16400) (b := 8208)
    (by decide) (by decide) (by decide) ⟨_, hH1⟩) fun st' hpc' hpost ↦ ?_
  obtain ⟨hh, hout, hS⟩ := r.update_out h0 h1 h2 hpost
  have hseed := seed_bytes hB1.2.2.1.1
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b144_next), hB1.of_call hpre hS (by decide) (by decide)
    (by decide) hout, ?_, hElen, ?_, ?_⟩
  · exact r.bytesAt_of_call hpre hB1.2.1 (by decide) (by decide) hout (by omega)
      (by omega) (hd (by omega) hE)
  · exact r.bytesAt_of_call hpre hB1.2.1 (by decide) (by decide) hout (by rw [length_adrs]; omega)
      (by rw [length_adrs]; omega) (hd (by rw [length_adrs]; omega) hA)
  · have := hh [] hH1
    rwa [List.nil_append, hseed] at this

end

end NativeRustcArm.SphincsVerifyProof.Tree
