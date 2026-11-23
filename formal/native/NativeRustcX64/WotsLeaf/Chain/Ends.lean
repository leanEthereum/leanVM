module

public import NativeRustcX64.WotsLeaf.Chain.Steps

/-!
# A chain's end stored

`b14` (`.LWotsLeaf_23`, directive 168) stores chain `i`'s end, the 16 bytes at `80`, at
`1080 + 16 i` (the address RSP plus `456(%rsp)`, `16 i`, plus 1080) and goes on with chain `i + 1`
at `b15` (directive 177) or, after chain 57, to `b51` (directive 525) (`seg_b14`). Its symbolic
state `s14`: region 0 the frame's first 96 bytes, region 1 the call's return slot, region 2 the
word at `456`, region 3 the end's 16 bytes.
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Chain

public section

theorem off_add_ofInt {r : Run} (a : Nat) {c : Int} {b : Nat} (h : (a : Int) + c = b) :
    r.off a + BitVec.ofInt 64 c = r.off b := by
  unfold Run.off
  have ha : BitVec.ofNat 64 a = BitVec.ofInt 64 (a : Int) := by simp
  have hb : BitVec.ofNat 64 b = BitVec.ofInt 64 (b : Int) := by simp
  rw [BitVec.add_assoc, ha, hb, ← BitVec.ofInt_add, h]

/-- A word's bytes read back. -/
theorem ofInt_regBytes (v : BitVec 64) : BitVec.ofInt 64 (Int.ofBytes (regBytes v)) = v := by
  have hb := Sym.ofBytes_byteOf v 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at hb
  rw [regBytes, hb, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have := v.isLt
  omega

theorem beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he ↦ h (by
      have := congrArg BitVec.toNat he
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
        at this)
    simp [h, this]

/-- The slots all end by `a₀`. -/
@[expose] def slotsBelow (L : List Slot) (a₀ : Nat) : Bool := L.all fun s ↦ decide (s.1 + s.2.1 ≤ a₀)

section
variable [Labels] {r : Run}

/-- **A block writing only region `k`** changes only its bytes. -/
theorem sameOutside_region {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
    (hwf : env.WF) {k : Nat} {a : BitVec 64} {n : Nat} (hk : env.regions[k]? = some (a, n))
    (hall : S.mem.all (fun w ↦ w.r == k && decide (w.off + w.n ≤ n)) = true) :
    SameOutside env.mem0 m'.dmem (InRange a n) := by
  refine SameOutside.mono (hm.sameOutside hwf) fun p ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ ?_
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
  obtain ⟨hr, hn⟩ := hall w hw
  rw [hr, hk] at hb
  cases hb
  have := hwf.noWrap k a n hk
  rw [Sym.inRange_iff this]
  omega

/-- **Slots ending by `a₀` stay** through a change of the frame's bytes from `a ≥ a₀`. -/
theorem SlotsAt.of_above (hpre : r.Pre) {m m' : MachineData} {L : List Slot} (h : SlotsAt r m L)
    {a n a₀ : Nat} (hout : SameOutside m.dmem m'.dmem (InRange (r.off a) n)) (ha : a + n ≤ 2768)
    (ha₀ : a₀ ≤ a) (hL : slotsBelow L a₀ = true) : SlotsAt r m' L :=
  allOf_imp (fun s hs ⟨hl, ho, hb⟩ ↦ ⟨hl, ho, bytesAt_of_sameOutside hb hout fun i hi ↦ by
    have := List.all_eq_true.mp hL s hs
    simp only [decide_eq_true_eq] at this
    rw [Run.off_add]
    exact r.not_inRange_off hpre ha (by omega) (by omega)⟩) h

end

variable [Host] {r : Run}

/-- At `b14`: the regions. -/
@[expose] def Run.regions14 (r : Run) (i : Nat) : List (BitVec 64 × Nat) :=
  [(r.off 0, 96), (r.base - 8#64, 8), (r.off 456, 8), (r.off (1080 + 16 * i), 16)]

/-- **`b14`**: chain `i`'s end stored after the ends so far; on to chain `i + 1`, or `b51` after
chain 57. -/
theorem seg_b14 (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) {i : Nat} (hi : i < 58)
    {e : List UInt8} (he : e.length = 16) {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r (r.endSlots i) m) (h80 : BytesAt m.dmem (r.off 80) e)
    (hdx : Run.RegIs m .rdx (BitVec.ofNat 64 i)) (h12 : Run.RegIs m .r12 (r.off 112))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec)
    (hbx : Run.RegIs m .rbx (Labels.label "memset").toBitVec)
    (cont : ∀ m', Keep r (r.chainSlots ++ [(1080, 16 * (i + 1), r.endsPre i ++ e)]) m' →
      Run.RegIs m' .rdx (BitVec.ofNat 64 (i + 1)) → Run.RegIs m' .r12 (r.off 112) →
      Run.RegIs m' .r13 (Labels.label "memcpy").toBitVec →
      Run.RegIs m' .rbx (Labels.label "memset").toBitVec →
      Eventually (step1 Host.exe) R ⟨m', if i + 1 = 58 then r.pc NativeRustcX64.Xmss.WotsLeaf.b51Offset else r.pc NativeRustcX64.Xmss.WotsLeaf.b15Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b14Offset⟩ := by
  have hF := hK.1
  obtain ⟨⟨hEl0, -, hE⟩, -⟩ := allOf_right (allOf_left hK.2)
  have hEl : (r.endsPre i).length = 16 * i := hEl0
  obtain ⟨⟨-, -, h456⟩, -⟩ := allOf_right hK.2
  have hb := r.base_toNat hpre
  have hc8 := r.callSp_toNat hpre
  have o0 := r.off_toNat hpre (a := 0) (by decide)
  have o456 := r.off_toNat hpre (a := 456) (by decide)
  have oE := r.off_toNat hpre (a := 1080 + 16 * i) (by omega)
  obtain ⟨m0, w0⟩ := r.frame_mapped hpre hF (a := 0) (n := 96) (by decide)
  obtain ⟨m2, w2⟩ := r.frame_mapped hpre hF (a := 456) (n := 8) (by decide)
  obtain ⟨m3, w3⟩ := r.frame_mapped hpre hF (a := 1080 + 16 * i) (n := 16) (by omega)
  obtain ⟨m1, w1⟩ := r.slot_mapped hpre hF.2.2.2
  have hwf : (Env.ofMachine m (r.regions14 i) (fun _ ↦ 0)
      (r.pc (NativeRustcX64.Xmss.WotsLeaf.b14Offset + b14.length)).toBitVec).WF := by
    refine Env.wf_of ⟨⟨m0, w0⟩, ⟨m1, w1⟩, ⟨m2, w2⟩, ⟨m3, w3⟩, trivial⟩ ?_
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
      (List.pairwise_singleton _ _)))
    all_goals
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> (unfold Apart; dsimp only; omega)
  have hm : Match (Env.ofMachine m (r.regions14 i) (fun _ ↦ 0) (r.pc (NativeRustcX64.Xmss.WotsLeaf.b14Offset + b14.length)).toBitVec)
      s14 m := by
    refine match_ofMachine ⟨rfl, rfl, rfl, rfl, trivial⟩ ⟨?_, trivial⟩ trivial trivial
      ⟨?_, ?_, trivial⟩
    · show m.regs.get64 .rsp = r.off 0 + BitVec.ofInt 64 0
      rw [off_add_ofInt 0 (b := 0) (by simp), Run.off_zero]
      exact hF.1
    · show r.off 0 + BitVec.ofInt 64 456 = r.off 456 + BitVec.ofInt 64 0
      rw [off_add_ofInt 0 (b := 456) (by simp), off_add_ofInt 456 (b := 456) (by simp)]
    · show BinOp.apply .add .W64 (r.off 0 + BitVec.ofInt 64 0)
        ((Env.ofMachine m (r.regions14 i) (fun _ ↦ 0)
          (r.pc (NativeRustcX64.Xmss.WotsLeaf.b14Offset + b14.length)).toBitVec).load 2 0 8) =
          r.off (1080 + 16 * i) + BitVec.ofInt 64 (-1080)
      rw [Env.load_of_bytesAt (length_regBytes _) (by rw [BitVec.add_zero]; exact h456),
        ofInt_regBytes, off_add_ofInt 0 (b := 0) (by simp),
        off_add_ofInt (1080 + 16 * i) (b := 16 * i) (by omega)]
      simp only [BinOp.apply, low_W64, ext_W64]
      rw [Run.off_add, Nat.zero_add]
  refine blk r hp b14_in_code (List.cons_ne_nil _ _) run_b14 hwf rfl hm fun st hm1 hpc ↦ ?_
  have hslot : BytesAt st.data.dmem (r.off (1080 + 16 * i)) e :=
    BytesAt.zero (copy16 hm1 (k := 3) (b := r.off (1080 + 16 * i)) (sz := 16) rfl (o := 0)
      (by decide) (k' := 0) (o' := 80) (by decide +kernel) (by decide +kernel) he (by
        show BytesAt m.dmem (r.off 0 + BitVec.ofNat 64 80) e
        rw [Run.off_add]
        exact h80))
  have hout : SameOutside m.dmem st.data.dmem (InRange (r.off (1080 + 16 * i)) 16) :=
    sameOutside_region hm1 hwf (k := 3) rfl (by decide +kernel)
  have hsp : reg st.data .rsp = r.base := by
    unfold reg
    rw [hm1.regs .rsp _ rfl]
    show r.off 0 + BitVec.ofInt 64 0 = r.base
    rw [off_add_ofInt 0 (b := 0) (by simp), Run.off_zero]
  have hF1 : r.Frame st.data :=
    (r.frame_iff _).2 (Run.FrameAt.of_block ((r.frame_iff m).1 hF) hsp hout
      (fun _ hp ↦ r.inRange_off hpre (a := 1080 + 16 * i) (n := 16) (by omega) hp) (hm1.kept hwf))
  have hC : SlotsAt r st.data r.chainSlots :=
    SlotsAt.of_above hpre (allOf_left (allOf_left hK.2)) hout (by omega) (a₀ := 672) (by omega) rfl
  have hE1 : BytesAt st.data.dmem (r.off 1080) (r.endsPre i) :=
    bytesAt_of_sameOutside hE hout fun j hj ↦ by
      rw [Run.off_add]
      exact r.not_inRange_off hpre (by omega) (by omega) (by omega)
  have hE' : BytesAt st.data.dmem (r.off 1080) (r.endsPre i ++ e) :=
    BytesAt.cat hE1 hslot (by rw [hEl])
  have hdx' : Run.RegIs st.data .rdx (BitVec.ofNat 64 (i + 1)) := by
    unfold Run.RegIs reg
    rw [hm1.regs .rdx _ rfl]
    show BinOp.apply .add .W64 (m.regs.get64 .rdx) (BitVec.ofNat 64 1) = _
    rw [show m.regs.get64 .rdx = BitVec.ofNat 64 i from hdx]
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [BitVec.ofNat_add]
  have hc : (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .rdx) (.lit 1)) (.lit 58)).eval
      (Env.ofMachine m (r.regions14 i) (fun _ ↦ 0) (r.pc (NativeRustcX64.Xmss.WotsLeaf.b14Offset + b14.length)).toBitVec) =
        decide (i + 1 = 58) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (m.regs.get64 .rdx) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 58) = _
    rw [show m.regs.get64 .rdx = BitVec.ofNat 64 i from hdx]
    simp only [CmpOp.apply, BinOp.apply, low_W64, ext_W64]
    rw [← BitVec.ofNat_add, beq_ofNat (by omega) (by omega)]
  refine pc_at ?_ (cont _ ⟨hF1, allOf_append hC ⟨⟨by simp only [List.length_append, hEl, he]; omega,
    by show 1080 + 16 * (i + 1) ≤ 2712; omega, hE'⟩, trivial⟩⟩ hdx' (regIs_reg hm1 rfl h12)
      (regIs_reg hm1 rfl h13) (regIs_reg hm1 rfl hbx))
  rw [pc_cond hpc hc, Run.label_of_block r hp b51_in_code rfl]
  by_cases h : i + 1 = 58
  · rw [ite_pos h, decide_eq_true h]
    rfl
  · rw [ite_neg h, decide_eq_false h]
    rfl

end

end NativeRustcX64.WotsLeafProof
