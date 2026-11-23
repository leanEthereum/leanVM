module

public import NativeRustcX64.WotsLeaf.Chain.StepC

/-!
# A chain step, part B: the clone and the payload absorbed

From `b31` (directive 359) with hasher A's zero state at `112`, its 32 buffered bytes `SA` at
`312` and its `buf_len` 32 at `448`, the payload `P` at `672`: A cloned into B at `704` (`b31`),
B's `buf_len` loaded (`b32`), the inlined `update`'s loop (`b35`, `b36`) copying `P` into B's
buffer after `SA` (`b37`), `buf_len` 64 (`b38`), the loop's end (`b34`); then `b42`
(`seg_b31`, `seg_b37`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Chain
open LeanVM.Protocol.KeccakHash

public section

variable [Host] {r : Run}

/-- **`b37`, `b38`, `b34`**: `P` copied into B's buffer after `SA`, B's `buf_len` 64; then
`b42`. -/
theorem seg_b37 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {SA P : List UInt8} (hSA : SA.length = 32) (hP : P.length = 32)
    {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))), (672, 32, P),
      (704, 200, List.replicate 200 0), (904, 32, SA), (1040, 8, regBytes (BitVec.ofNat 64 32))]) m)
    (h15 : Run.RegIs m .r15 (BitVec.ofNat 64 32)) (h14 : Run.RegIs m .r14 (BitVec.ofNat 64 32))
    (hbx : Run.RegIs m .rbx (r.off 672)) (h12 : Run.RegIs m .r12 (BitVec.ofNat 64 32))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r i p (SA ++ P) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b37Offset⟩ := by
  -- `b37`: `memcpy` of `P`.
  refine frameCall r hp hpre b37_in_code (List.cons_ne_nil _ _) run_b37 (by decide) rfl hK
    trivial extraOK_nil ⟨known_lit h15, known_lit h14, known_ptr hbx, h13, trivial⟩ trivial trivial
    hc.1 fun m₁ hm₁ hK₁ _ ↦ ?_
  obtain ⟨-, ⟨-, -, hP₁⟩, -⟩ := allOf_right hK₁.2
  obtain ⟨hpre₁, hpost₁⟩ := memcpyFrame hpre hK₁ (regIs_ptr hm₁ rfl) (regIs_ptr hm₁ rfl)
    (toNat_of_lit hm₁ rfl (by decide)) (by decide) (by decide) (by decide) rfl hP hP₁
  refine ⟨hpre₁, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hK₂, hS₂, -, hB⟩ := hpost₁ m₂ hsp hQ
  obtain ⟨t56, -, t704, ⟨-, -, hSA₂⟩, ⟨-, -, h1040⟩, -⟩ := allOf_right hK₂.2
  have h14₂ : Run.RegIs m₂ .r14 (BitVec.ofNat 64 32) := RegIs.of_saved hS₂ rfl (regIs_lit hm₁ rfl)
  have hbx₂ : Run.RegIs m₂ .rbx (r.off 672) := RegIs.of_saved hS₂ rfl (regIs_ptr hm₁ rfl)
  have h12₂ : Run.RegIs m₂ .r12 (BitVec.ofNat 64 32) :=
    RegIs.of_saved hS₂ rfl (regIs_reg hm₁ rfl h12)
  have h13₂ : Run.RegIs m₂ .r13 (Labels.label "memcpy").toBitVec :=
    RegIs.of_saved hS₂ rfl (hm₁.regs .r13 _ rfl)
  have hK₂' : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))),
      (704, 200, List.replicate 200 0), (904, 64, SA ++ P)]) m₂ :=
    hK₂.left.add ⟨t56, t704, ⟨by simp only [List.length_append, hSA, hP], by norm_num,
      BytesAt.cat hSA₂ hB (by rw [hSA])⟩, trivial⟩
  -- `b38`: B's `buf_len` 64.
  have hm₀ := match_seeded (match_frameS
    (fun _ hl _ hi => r.got_byte hpre hK₂'.1.2.2.1 hl hi) hK₂'.1.1 (sextra := []) (extra := [])
    (ret := (r.pc (NativeRustcX64.Xmss.WotsLeaf.b38Offset + b38.length)).toBitVec) (k := [(.r14, .lit 32)]) (bounds := [])
    (aliases := []) trivial ⟨known_lit h14₂, trivial⟩ trivial trivial)
    h1040
  refine frameStepS r hp hpre b38_in_code (List.cons_ne_nil _ _) run_b38 (by decide) rfl hK₂'
    extraOK_nil hm₀ fun st3 hm3 hK3 _ hpc3 ↦ ?_
  refine pc_at ((pc_true hpc3).trans (Run.label_of_block r hp b34_in_code rfl)) ?_
  -- `b34`: the loop's end.
  refine frameStep r hp hpre b34_in_code (List.cons_ne_nil _ _) run_b34 (by decide) rfl hK3
    trivial extraOK_nil ⟨known_lit (regIs_reg hm3 rfl h12₂), known_lit (regIs_lit hm3 rfl),
      known_ptr (regIs_reg hm3 rfl hbx₂), trivial⟩ trivial trivial fun st4 hm4 hK4 _ hpc4 ↦ ?_
  refine pc_at ((pc_true hpc4).trans (Run.label_of_block r hp b42_in_code rfl)) ?_
  exact seg_b42 hp hc hpre hp3 (by simp only [List.length_append, hSA, hP]) hK4
    (regIs_reg hm4 rfl (regIs_lit hm3 rfl))
    (regIs_reg hm4 rfl (regIs_reg hm3 rfl h13₂)) cont

/-- **`b31 .. b36`**: A cloned into B, B's `buf_len` loaded, the loop's first bounds; then
`b37`. -/
theorem seg_b31 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {SA P : List UInt8} (hSA : SA.length = 32) (hP : P.length = 32)
    {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))), (672, 32, P),
      (112, 200, List.replicate 200 0), (312, 32, SA), (448, 8, regBytes (BitVec.ofNat 64 32))]) m)
    (h12 : Run.RegIs m .r12 (r.off 112))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec) (cont : StepCont r i p (SA ++ P) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b31Offset⟩ := by
  -- `b31`: `memcpy` of A into B.
  refine frameCall r hp hpre b31_in_code (List.cons_ne_nil _ _) run_b31 (by decide) rfl hK
    trivial extraOK_nil ⟨known_ptr h12, h13, trivial⟩ trivial trivial hc.1 fun m₁ hm₁ hK₁ _ ↦ ?_
  obtain ⟨-, -, ⟨-, -, hA0⟩, ⟨-, -, hSA₁⟩, ⟨-, -, h448⟩, -⟩ := allOf_right hK₁.2
  obtain ⟨hpre₁, hpost₁⟩ := memcpyFrame' hpre hK₁ (regIs_ptr hm₁ rfl) (regIs_ptr hm₁ rfl)
    (toNat_of_lit hm₁ rfl (by decide)) (by decide) (by decide) (by decide) rfl
  refine ⟨hpre₁, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hK₂, hS₂, hB⟩ := hpost₁ m₂ hsp hQ
  have h13₂ : Run.RegIs m₂ .r13 (Labels.label "memcpy").toBitVec :=
    RegIs.of_saved hS₂ rfl (hm₁.regs .r13 _ rfl)
  obtain ⟨t56, t672, -⟩ := allOf_right hK₂.2
  have hB0 : BytesAt m₂.dmem (r.off 704) (List.replicate 200 0) :=
    copy_slice (c := 0) (bs := List.replicate 200 0) hB
      (by simp only [List.length_replicate]; omega) hA0
  have hBsa : BytesAt m₂.dmem (r.off 904) SA :=
    copy_slice (c := 200) (bs := SA) hB (by omega) hSA₁
  have hB32 : BytesAt m₂.dmem (r.off 1040) (regBytes (BitVec.ofNat 64 32)) :=
    copy_slice (c := 336) (bs := regBytes (BitVec.ofNat 64 32)) hB
      (by simp only [length_regBytes]; omega) h448
  -- `b32`: B's `buf_len` loaded, the loop's registers.
  have hK₂' : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))), (672, 32, P),
      (704, 200, List.replicate 200 0), (904, 32, SA)]) m₂ :=
    hK₂.left.add ⟨t56, t672, ⟨by simp only [List.length_replicate], by norm_num, hB0⟩,
      ⟨hSA, by norm_num, hBsa⟩, trivial⟩
  have hm₀ := match_seeded (match_frameS
    (fun _ hl _ hi => r.got_byte hpre hK₂'.1.2.2.1 hl hi) hK₂'.1.1 (sextra := []) (extra := [])
    (ret := (r.pc (NativeRustcX64.Xmss.WotsLeaf.b32Offset + b32.length)).toBitVec) (k := []) (bounds := []) (aliases := []) trivial
    trivial trivial trivial) hB32
  refine frameStepS r hp hpre b32_in_code (List.cons_ne_nil _ _) run_b32 (by decide) rfl hK₂'
    extraOK_nil hm₀ fun st3 hm3 hK3 _ hpc3 ↦ ?_
  have h1040 : BytesAt st3.data.dmem (r.off 1040) (regBytes (BitVec.ofNat 64 32)) :=
    frame_covers hm3 (o := 1040) (n := 8) (v := .lit 32) (by decide) (by decide +kernel)
  refine pc_at (hpc3.trans (Run.label_of_block r hp b35_in_code rfl)) ?_
  obtain ⟨u56, u672, u704, u904, -⟩ := allOf_right hK3.2
  have hK3' : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))), (672, 32, P),
      (704, 200, List.replicate 200 0), (904, 32, SA), (1040, 8, regBytes (BitVec.ofNat 64 32))])
      st3.data :=
    hK3.left.add ⟨u56, u672, u704, u904, ⟨length_regBytes _, by norm_num, h1040⟩, trivial⟩
  -- `b35`, `b36`: the loop's bounds.
  refine frameStep r hp hpre b35_in_code (List.cons_ne_nil _ _) run_b35 (by decide) rfl hK3'
    trivial extraOK_nil ⟨known_lit (regIs_lit hm3 rfl), known_lit (regIs_lit hm3 rfl),
      known_ptr (regIs_ptr hm3 rfl), trivial⟩ trivial trivial fun st4 hm4 hK4 _ hpc4 ↦ ?_
  refine pc_at (pc_false hpc4) ?_
  refine frameStep r hp hpre b36_in_code (List.cons_ne_nil _ _) run_b36 (by decide) rfl hK4
    trivial extraOK_nil ⟨known_lit (regIs_lit hm4 rfl), trivial⟩ trivial trivial
    fun st5 hm5 hK5 _ hpc5 ↦ ?_
  refine pc_at (pc_false hpc5) ?_
  exact seg_b37 hp hc hpre hp3 hSA hP hK5 (regIs_reg hm5 rfl (regIs_lit hm4 rfl))
    (regIs_reg hm5 rfl (regIs_lit hm4 rfl)) (regIs_reg hm5 rfl (regIs_ptr hm4 rfl))
    (regIs_reg hm5 rfl (regIs_lit hm4 rfl))
    (regIs_reg hm5 rfl (regIs_reg hm4 rfl (regIs_reg hm3 rfl h13₂))) cont

end

end NativeRustcX64.WotsLeafProof
