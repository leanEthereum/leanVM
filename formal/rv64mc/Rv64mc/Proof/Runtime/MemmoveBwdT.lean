/-
  Rv64mc.Proof.Runtime.MemmoveBwdT

  `compiler_builtins`' `memmove`'s backward copy, from its program counter 8 (`bwd_ok`): taken when `dst - src`
  (wrapping) is below `n`, so the destination starts inside the source and each source byte is read before any
  destination byte after it is written (`MoveT.FxB`). From 16 bytes on, it copies the bytes after the destination's
  last 8-byte boundary one at a time (the prefix, `nt` of them, from the end), then the destination's doublewords
  from the end, then the bytes before them (the suffix). A source as aligned as the destination is copied a
  doubleword at a time; another is read a source doubleword at a time from the end and each destination doubleword
  reassembled from two (`extractByte_shr_or_shl`), the partial source doublewords at either end read through the
  scratch doubleword (`load_aligned_partial`, `load_aligned_end_partial`).

  The proof is cut at the loops' heads and the partial loads' joins, with the bytes copied so far as `MoveT.BInv`.
  Every loop is `Total.loop` with the bytes left as the measure.

  ## Main results

  * `bwd_ok`
-/

import Rv64mc.Proof.Runtime.MoveT

namespace Rv64mc.Proof.Runtime.MemmoveBwdT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime.CopyT Rv64mc.Proof.Runtime.MoveT
open Rv64mc.Proof.Runtime.MemsetT (InWin Kept)
open Rv64mc.Gen.CompilerBuiltins.Mem.Memmove (Link tmpl)

/-- A side goal about numbers with literals' `toNat` computed. -/
local macro "tlit" : tactic => `(tactic| ((try tnorm) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow,
  Nat.reduceMod, show ((UnOp.sext .b4).eval 6#64 : Word) = 6#64 by decide,
  show ((UnOp.sext .b4).eval 2#64 : Word) = 2#64 by decide, show ((UnOp.sext .b4).eval 3#64 : Word) = 3#64 by decide])
  <;> omega))

/-- `Regs` through the body's writes of scratch registers. -/
local macro "regs_ok " h:term : tactic => `(tactic| ((repeat (apply Regs.upd _ (by decide))) <;> exact $h))

set_option hygiene false in
/-- The entry's windows (`hsw`, `hdw`, `hW`) and the code's bytes (`hcode`) as hypotheses. -/
local macro "fx_facts " F:term:max hI:term:max : tactic => `(tactic| (
  have hsw := inWindow_iff.1 ($F).swin; have hdw := ($F).dwin; unfold InWin at hdw; have hW := ($F).win
  have hroom := ($F).room; have hal := ($F).al; have hcode := ($hI).1.1.2.2))

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} {Q : State rvIsa → Prop} {ret top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState}

theorem bat_eq {M : MachineState} {a b : Nat} (h : a = b) : bat M a = bat M b := h ▸ rfl

/-! ## The suffix -/

/-- The suffix's loop at its head, `c` bytes left: `x17` one past the next destination byte, `x14` the next source
    byte, `x11` the destination. -/
def SInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (c : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  Regs ret top regs r ∧ BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M c ∧
    (r .x17).toNat = (regs .x10).toNat + c ∧ (r .x14).toNat + 1 = (regs .x11).toNat + c ∧
    (r .x11).toNat = (regs .x10).toNat ∧ 0 < c ∧ c ≤ (regs .x12).toNat

/-- The suffix, a byte at a time from its end. -/
theorem loopS_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) :
    ∀ c r M, SInv env ret top regs m c r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 438, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (SInv env ret top regs m) fun c r M ⟨hR, hI, h17, h14, h11, hc0, hcn⟩ ih => ?_
  fx_facts F hI
  have hx2 := hR.2.1
  have hv : extractByte ((M.getByte (r .x14)).zeroExtend 64) 0 = bat m ((regs .x11).toNat + (c - 1)) := by
    rw [extractByte_zext_getByte, show (r .x14).toNat = (regs .x11).toNat + (c - 1) by omega]
    exact F.src hI (by omega) (by omega) (by omega)
  have h17' : (r .x17 + 0xffffffffffffffff#64).toNat = (regs .x10).toNat + (c - 1) := by
    rw [toNat_dec (by omega)]; omega
  have h14' : (r .x14 + 0xffffffffffffffff#64).toNat = (r .x14).toNat - 1 := toNat_dec (by omega)
  have hI0 : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (c - 1 + 1) := by
    rwa [Nat.sub_add_cancel hc0]
  have hI' := hI0.byte F.toFx h17' (by omega) hv
  rv_symT hp stop [450] with [hx2]
  · have hc' := BitVec.lt_def.1 hc
    rw [h17'] at hc'
    refine ih (c - 1) _ _ (by omega) ⟨by regs_ok hR, hI', ?_, ?_, ?_, by omega, by omega⟩ <;> tnorm <;> omega
  · have hc' := BitVec.le_def.1 hc
    rw [h17'] at hc'
    refine ret_ok hp F.toFx hk hsp (by regs_ok hR) (BInv.toF ?_)
    rwa [show c - 1 = 0 by omega] at hI'

/-- The suffix, `c` bytes, from its end: `x17` and `x14` one past the destination's and the source's. -/
theorem sfx_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {c : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M c)
    (h17 : (r .x17).toNat = (regs .x10).toNat + c) (h14 : (r .x14).toNat = (regs .x11).toNat + c)
    (h12 : (r .x12).toNat = c) (hcn : c ≤ (regs .x12).toNat) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 432, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have h11 : (r .x17 - r .x12).toNat = (regs .x10).toNat := by rw [BitVec.toNat_sub]; omega
  rv_symT hp stop [438, 450] with [hx2]
  · have hc' := BitVec.le_def.1 hc
    rw [h11] at hc'
    refine ret_ok hp F.toFx hk hsp (by regs_ok hR) (BInv.toF ?_)
    rwa [show c = 0 by omega] at hI
  · have hc' := BitVec.lt_def.1 hc
    rw [h11] at hc'
    refine loopS_ok hp F hk hsp c _ _ ⟨by regs_ok hR, hI, ?_, ?_, ?_, by omega, hcn⟩
    · tnorm; omega
    · tnorm; rw [toNat_dec (by omega)]; omega
    · tnorm; omega

/-! ## The doublewords -/

theorem toNat_add_neg {a b : Word} (h : b.toNat ≤ a.toNat) : (a + (0#64 - b)).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega

/-- What the doublewords' parts keep, `jw` bytes before the prefix: `x13` and `x14` one past the destination's and
    the source's `jw` bytes, `x15 = jw`, `x16` minus its doublewords' bytes. -/
def Mid (regs r : Reg → Word) (jw : Nat) : Prop :=
  (r .x13).toNat = (regs .x10).toNat + jw ∧ (r .x14).toNat = (regs .x11).toNat + jw ∧ (r .x15).toNat = jw ∧
    r .x16 = 0#64 - BitVec.ofNat 64 (jw - jw % 8) ∧ ((regs .x10).toNat + jw) % 8 = 0 ∧ 8 ≤ jw ∧
    jw ≤ (regs .x12).toNat

theorem Mid.upd {regs r : Reg → Word} {jw : Nat} (h : Mid regs r jw) {d : Reg}
    (hd : d ∈ [.x5, .x6, .x7, .x8, .x11, .x12, .x17, .x28, .x29, .x30, .x31]) (v : Word) :
    Mid regs (updReg r d v) jw := by
  obtain ⟨h13, h14, h15, h16, h1, h2, h3⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  have hne : d ≠ .x13 ∧ d ≠ .x14 ∧ d ≠ .x15 ∧ d ≠ .x16 := by
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_, ?_, ?_, h1, h2, h3⟩ <;>
    simp [updReg_apply, Ne.symm hne.1, Ne.symm hne.2.1, Ne.symm hne.2.2.1, Ne.symm hne.2.2.2, h13, h14, h15, h16]

/-- `Mid` through the body's writes of scratch registers. -/
local macro "mid_ok " hm:term : tactic => `(tactic| ((repeat (apply Mid.upd _ (by decide))) <;> exact $hm))

/-- After the doublewords: the suffix, `jw % 8` bytes. -/
theorem after_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (jw % 8)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 426, ret, top⟩ :: rest, r, M⟩ := by
  obtain ⟨h13, h14, h15, h16, hd8, hj8, hjn⟩ := hM
  have hdn := F.dn
  have hsw := inWindow_iff.1 F.swin
  have hx2 := hR.2.1
  have hw : (BitVec.ofNat 64 (jw - jw % 8)).toNat = jw - jw % 8 := by rw [BitVec.toNat_ofNat]; omega
  have hA : (r .x13 + r .x16).toNat = (regs .x10).toNat + jw % 8 := by rw [h16, toNat_add_neg (by omega)]; omega
  have hB : (r .x14 + r .x16).toNat = (regs .x11).toNat + jw % 8 := by rw [h16, toNat_add_neg (by omega)]; omega
  have hC := Proof.Runtime.Alloc.and7 (r .x15)
  rv_symT hp stop [432] with [hx2]
  refine sfx_ok hp F hk hsp (c := jw % 8) (by regs_ok hR) hI ?_ ?_ ?_ (by omega) <;> tnorm <;> omega

/-- The aligned doublewords' loop at its head, the bytes from `j` on copied: `x12` and `x11 + 8` the destination's
    and the source's `j`-th byte, `x7` the destination's first doubleword. -/
def GInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (jw j : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  Regs ret top regs r ∧ Mid regs r jw ∧ BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M j ∧
    (r .x12).toNat = (regs .x10).toNat + j ∧ (r .x11).toNat + 8 = (regs .x11).toNat + j ∧
    (r .x7).toNat = (regs .x10).toNat + jw % 8 ∧ jw % 8 + 8 ≤ j ∧ j ≤ jw ∧ (jw - j) % 8 = 0 ∧
    ((regs .x11).toNat + jw) % 8 = 0

/-- The doublewords of a source as aligned as the destination, from the end. -/
theorem loopG_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) (jw : Nat) :
    ∀ j r M, GInv env ret top regs m jw j r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 296, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (GInv env ret top regs m jw)
    fun j r M ⟨hR, hM, hI, h12, h11, h7, hj0, hjw, hj8, hs8⟩ ih => ?_
  fx_facts F hI
  have hx2 := hR.2.1
  have hM' := hM
  obtain ⟨h13, h14, h15, h16, hd8, hjw8, hjn⟩ := hM'
  have ha11 : (r .x11).toNat % 8 = 0 := by omega
  have hv : ∀ t, t < 8 → extractByte (M.getMem (r .x11)) t = bat m ((regs .x11).toNat + (j - 8) + t) := by
    intro t ht
    rw [extractByte_getMem ha11 ht, show (r .x11).toNat + t = (regs .x11).toNat + (j - 8) + t by omega]
    exact F.src hI (by omega) (by omega) (by omega)
  have h12' : (r .x12 + 0xfffffffffffffff8#64).toNat = (regs .x10).toNat + (j - 8) := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have h11' : (r .x11 + 0xfffffffffffffff8#64).toNat = (r .x11).toNat - 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hI0 : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (j - 8 + 8) := by
    rwa [Nat.sub_add_cancel (by omega)]
  have hI' := hI0.word F.toFx h12' (by omega) (by omega) hv
  rv_symT hp stop [426] with [hx2]
  · have hc' := BitVec.lt_def.1 hc
    rw [h12', h7] at hc'
    clear hc
    refine ih (j - 8) _ _ (by omega) ⟨by regs_ok hR, by mid_ok hM, hI', ?_, ?_, ?_, by omega, by omega, by omega,
      hs8⟩ <;> tnorm <;> omega
  · have hc' := BitVec.le_def.1 hc
    rw [h12', h7] at hc'
    clear hc
    have e : j - 8 = jw % 8 := by clear * - hc' hj0; omega
    rw [e] at hI'
    exact after_ok hp F hk hsp (jw := jw) (by regs_ok hR) (by mid_ok hM) hI'

/-- The doublewords of a source as aligned as the destination. -/
theorem alB_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M jw)
    (h7 : (r .x7).toNat = (regs .x10).toNat + jw % 8) (h11 : (r .x11).toNat = (regs .x11).toNat)
    (hs8 : ((regs .x11).toNat + jw) % 8 = 0) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 288, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have hM' := hM
  obtain ⟨h13, h14, h15, h16, hd8, hjw8, hjn⟩ := hM'
  have hA : (r .x15 + r .x11).toNat = (regs .x11).toNat + jw := by rw [BitVec.toNat_add]; omega
  rv_symT hp stop [296, 426] with [hx2]
  · have hc' := BitVec.le_def.1 hc
    omega
  · refine loopG_ok hp F hk hsp jw jw _ _ ⟨by regs_ok hR, by mid_ok hM, hI, ?_, ?_, ?_, by omega, le_rfl,
      by simp, hs8⟩
    · tnorm; omega
    · tnorm; rw [BitVec.toNat_add, hA]; simp only [BitVec.toNat_ofNat]; omega
    · tnorm; omega

/-! ## A misaligned source's last doubleword -/

theorem slot_addr {top : Word} {r : Reg → Word} (hx2 : r .x2 = top + 0xfffffffffffffff0#64)
    (hroom : 16 ≤ top.toNat) : (r .x2).toNat = top.toNat - 16 := by
  rw [hx2, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

/-- The destination's first doubleword, from the scratch doubleword (the bytes from `o` on, the source's from
    `jw % 8`) and `x28` (the first `o` bytes of the source doubleword after them). -/
theorem lastB_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw o : Nat} {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (jw % 8 + 8))
    (ho1 : 0 < o) (ho8 : o < 8) (h11 : (r .x11).toNat = (regs .x10).toNat + jw % 8 + 8)
    (h7 : (r .x7).toNat = 8 * o)
    (hP : ∀ t, t < o → extractByte (r .x28) t = bat m ((regs .x11).toNat + jw % 8 + 8 - o + t))
    (hS : ∀ t, o ≤ t → t < 8 → bat M (top.toNat - 16 + t) = bat m ((regs .x11).toNat + jw % 8 - o + t)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 412, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have hs16 := slot_addr hx2 (by omega)
  have hM' := hM
  obtain ⟨h13, h14, h15, h16, hd8, hjw8, hjn⟩ := hM'
  obtain ⟨s1, s2⟩ := shamt h7 ho1 ho8
  have hv : ∀ t, t < 8 → extractByte (M.getMem (r .x2) >>> (r .x7 &&& 63#64).toNat |||
      r .x28 <<< (0#64 - r .x7 &&& 56#64 &&& 63#64).toNat) t = bat m ((regs .x11).toNat + jw % 8 + t) := by
    intro t ht
    rw [s1, s2, extractByte_shr_or_shl _ _ o t ho1 ho8 ht]
    split
    · rw [extractByte_getMem (by rw [hs16]; omega) (by omega), hs16, hS _ (by omega) (by omega)]; congr 1; omega
    · rw [hP _ (by omega)]; congr 1; omega
  have h11' : (r .x11 + 0xfffffffffffffff8#64).toNat = (regs .x10).toNat + jw % 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hI' := hI.word F.toFx h11' (by omega) (by omega) hv
  rv_symT hp stop [426] with [hx2]
  exact after_ok hp F hk hsp (jw := jw) (by regs_ok hR) (by mid_ok hM) hI'

-- `rv_symT` over the word's load and store into the scratch doubleword runs past the default budget.
set_option maxHeartbeats 400000 in
/-- `load_aligned_end_partial`'s word: the last four bytes into the scratch doubleword, `c` copied before them. -/
theorem endWordB_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw o c : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (jw % 8 + 8))
    (ho1 : 0 < o) (ho8 : o < 8) (hso : ((regs .x11).toNat + jw) % 8 = o)
    (h11 : (r .x11).toNat = (regs .x10).toNat + jw % 8 + 8) (h7 : (r .x7).toNat = 8 * o)
    (hP : ∀ t, t < o → extractByte (r .x28) t = bat m ((regs .x11).toNat + jw % 8 + 8 - o + t))
    (h6 : (r .x6).toNat = (regs .x11).toNat + jw % 8) (h12 : (r .x12).toNat = c)
    (h17 : (r .x17).toNat = top.toNat - 16 + o)
    (hS : ∀ t, o ≤ t → t < o + c → bat M (top.toNat - 16 + t) = bat m ((regs .x11).toNat + jw % 8 - o + t))
    (hc4 : o + c + 4 = 8) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 404, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have hM' := hM
  obtain ⟨h13, h14, h15, h16, hd8, hjw8, hjn⟩ := hM'
  have hb4 : Width.b4.bytes = 4 := rfl
  have hA : (r .x6 + r .x12).toNat = (regs .x11).toNat + jw % 8 + c := by rw [BitVec.toNat_add]; omega
  have hX : (r .x17 + r .x12).toNat = top.toNat - 16 + (o + c) := by rw [BitVec.toNat_add]; omega
  clear hdw h13 h14 h15 h16 hd8
  rv_symT hp stop [412] with [hx2]
  obtain ⟨hI', hS'⟩ := slot_copy16 (m := m) (w := .b4) (lo := o) (i := o + c) (B := (regs .x11).toNat + jw % 8 - o)
    (P := fun M' => BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' (jw % 8 + 8))
    (X := r .x17 + r .x12) (v := (UnOp.sext .b4).eval (Tactic.loadVal .b4 M (r .x6 + r .x12)))
    (fun _ h => h.slot F.toFx (by omega) (by rw [hb4]; omega) (by rw [hX, hb4]; omega)) hI (by omega) hS hX
    (by rw [hX, hb4]; omega) (by rw [hb4]; omega) (fun u hu => by
      have := extractByte_load (M := M) (x := r .x6 + r .x12) (u := u) true (by rw [hA, hb4]; omega) hu
      simp only [↓reduceIte] at this
      rw [this, hA]
      exact (F.src hI (by omega) (by omega) (by omega)).trans (by congr 1; omega))
  refine lastB_ok hp F hk hsp (jw := jw) (o := o) (by regs_ok hR) (by mid_ok hM) hI' ho1 ho8 ?_ ?_ ?_ ?_
  any_goals (tnorm; assumption)
  · intro t ht1 ht2; exact hS' t ht1 (by rw [hb4]; omega)

/-- `load_aligned_end_partial` at its word: `x5 = 8 - o`, its bits below 4 copied. -/
theorem endBit2B_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw o c : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (jw % 8 + 8))
    (ho1 : 0 < o) (ho8 : o < 8) (hso : ((regs .x11).toNat + jw) % 8 = o)
    (h11 : (r .x11).toNat = (regs .x10).toNat + jw % 8 + 8) (h7 : (r .x7).toNat = 8 * o)
    (hP : ∀ t, t < o → extractByte (r .x28) t = bat m ((regs .x11).toNat + jw % 8 + 8 - o + t))
    (h6 : (r .x6).toNat = (regs .x11).toNat + jw % 8) (h12 : (r .x12).toNat = c)
    (h17 : (r .x17).toNat = top.toNat - 16 + o)
    (hS : ∀ t, o ≤ t → t < o + c → bat M (top.toNat - 16 + t) = bat m ((regs .x11).toNat + jw % 8 - o + t))
    (h5 : (r .x5).toNat = 8 - o) (hcv : c = (8 - o) % 4) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 400, ret, top⟩ :: rest, r, M⟩ := by
  have hx2 := hR.2.1
  rv_symT hp stop [404, 412] with [hx2]
  · have := (and4_zero _).1 hc
    refine lastB_ok hp F hk hsp (jw := jw) (o := o) (by regs_ok hR) (by mid_ok hM) hI ho1 ho8 ?_ ?_ ?_ ?_
    any_goals (tnorm; assumption)
    · intro t ht1 ht2; exact hS t ht1 (by omega)
  · have : ¬ (r .x5).toNat % 8 < 4 := mt (and4_zero _).2 hc
    refine endWordB_ok hp F hk hsp (jw := jw) (o := o) (c := c) (by regs_ok hR) (by mid_ok hM) hI ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ hS (by omega)
    all_goals (tnorm; assumption)

-- `rv_symT` over the ten paths of the three partial loads runs past the default budget.
set_option maxHeartbeats 1000000 in
/-- `load_aligned_end_partial`: the source's bytes from `jw % 8` up to the next source doubleword into the scratch
    doubleword from byte `o` on, a byte, a halfword and a word as the bits of `8 - o` say. -/
theorem endB_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw o : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (jw % 8 + 8))
    (ho1 : 0 < o) (ho8 : o < 8) (hso : ((regs .x11).toNat + jw) % 8 = o)
    (h11 : (r .x11).toNat = (regs .x10).toNat + jw % 8 + 8) (h7 : (r .x7).toNat = 8 * o)
    (hP : ∀ t, t < o → extractByte (r .x28) t = bat m ((regs .x11).toNat + jw % 8 + 8 - o + t))
    (h29 : (r .x29).toNat + o = (regs .x11).toNat + jw % 8 + 8) (h6 : (r .x6).toNat = o) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 376, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have hs16 := slot_addr hx2 (by omega)
  have hM' := hM
  obtain ⟨h13, h14, h15, h16, hd8, hjw8, hjn⟩ := hM'
  have hb1 : Width.b1.bytes = 1 := rfl
  have hb2 : Width.b2.bytes = 2 := rfl
  have hb8 : Width.b8.bytes = 8 := rfl
  clear hdw h13 h14 h15 h16 hd8
  have hX6 : r .x2 ||| r .x6 = BitVec.ofNat 64 (top.toNat - 16 + o) := by
    rw [or_eq_add (by rw [hs16]; omega) (by omega)]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hs16, BitVec.toNat_ofNat]; omega
  have hX : (BitVec.ofNat 64 (top.toNat - 16 + o)).toNat = top.toNat - 16 + o := by
    rw [BitVec.toNat_ofNat]; omega
  have h5 : (8#64 - r .x6).toNat = 8 - o := by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hY : (r .x29 + r .x6 + 0xfffffffffffffff8#64).toNat = (regs .x11).toNat + jw % 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hI1 := hI.slot (w := .b8) (x := r .x2) (v := 0#64) F.toFx (by omega) (by rw [hb8]; omega)
    (by rw [hs16]; show _ % 8 = 0; omega)
  have src : ∀ M', BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' (jw % 8 + 8) →
      ∀ u, u < 8 - o → bat M' ((regs .x11).toNat + jw % 8 + u) = bat m ((regs .x11).toNat + jw % 8 + u) :=
    fun M' hI' u hu => F.src hI' (by omega) (by omega) (by omega)
  have hY1 : (r .x29 + r .x6 + 0xfffffffffffffff9#64).toNat = (regs .x11).toNat + jw % 8 + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hPs : ∀ (w : Width) (X v : Word) M', top.toNat - 16 ≤ X.toNat → X.toNat + w.bytes ≤ top.toNat - 8 →
      X.toNat % w.bytes = 0 →
      BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' (jw % 8 + 8) →
      BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m (Tactic.storeMem w M' X v) (jw % 8 + 8) :=
    fun w X v M' h1 h2 h3 h => h.slot F.toFx h1 h2 h3
  -- a byte at `o`, or a halfword at `o + c`
  have cpB := slot_copy16 (m := m) (w := .b1) (lo := o) (i := o) (B := (regs .x11).toNat + jw % 8 - o)
    (P := fun M' => BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' (jw % 8 + 8))
    (X := BitVec.ofNat 64 (top.toNat - 16 + o))
    (v := Tactic.loadVal .b1 (Tactic.storeMem .b8 M (r .x2) 0#64) (r .x29 + r .x6 + 0xfffffffffffffff8#64))
    (fun M' h => hPs .b1 _ _ M' (by rw [hX]; omega) (by rw [hX, hb1]; omega) (by rw [hb1]; omega) h) hI1
    (by omega) (fun t h1 h2 => absurd h2 (by omega)) hX (by rw [hb1]; omega) (by rw [hb1]; omega) (fun u hu => by
      have := extractByte_load (M := Tactic.storeMem .b8 M (r .x2) 0#64)
        (x := r .x29 + r .x6 + 0xfffffffffffffff8#64) (u := u) false (by rw [hb1]; omega) hu
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      have hu1 : u < 8 - o := by rw [hb1] at hu; omega
      rw [this, hY, src _ hI1 u hu1, show (regs .x11).toNat + jw % 8 - o + o + u = (regs .x11).toNat + jw % 8 + u
        by omega])
  have cpH := fun (c : Nat) (X Y : Word) {M' : MachineState}
      (hI' : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' (jw % 8 + 8))
      (hS' : ∀ t, o ≤ t → t < o + c → bat M' (top.toNat - 16 + t) = bat m ((regs .x11).toNat + jw % 8 - o + t))
      (hXc : X.toNat = top.toNat - 16 + (o + c)) (hYc : Y.toNat = (regs .x11).toNat + jw % 8 + c)
      (hal : (o + c) % 2 = 0) (hc2 : o + c + 2 ≤ 8) =>
    slot_copy16 (m := m) (w := .b2) (lo := o) (i := o + c) (B := (regs .x11).toNat + jw % 8 - o) (X := X)
      (P := fun M' => BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' (jw % 8 + 8))
      (v := (UnOp.sext .b2).eval (Tactic.loadVal .b2 M' Y))
      (fun M'' h => hPs .b2 _ _ M'' (by rw [hXc]; omega) (by rw [hXc, hb2]; omega) (by rw [hXc, hb2]; omega) h) hI'
      (by omega) hS' hXc (by rw [hXc, hb2]; omega) (by rw [hb2]; omega) (fun u hu => by
        have := extractByte_load (M := M') (x := Y) (u := u) true (by rw [hYc, hb2]; omega) hu
        simp only [↓reduceIte] at this
        have hu1 : c + u < 8 - o := by rw [hb2] at hu; omega
        rw [this, hYc, show (regs .x11).toNat + jw % 8 + c + u = (regs .x11).toNat + jw % 8 + (c + u) by omega,
          src _ hI' (c + u) hu1, show (regs .x11).toNat + jw % 8 - o + (o + c) + u =
            (regs .x11).toNat + jw % 8 + (c + u) by omega])
  rv_symT hp stop [400, 404, 412] with [hx2]
  all_goals try rw [hX6]
  rv_closeT
  -- `8 - o` odd, no halfword: the byte
  · rw [and2_zero, h5] at hc
    rw [and1_zero, h5] at hc_1
    obtain ⟨hI2, hS2⟩ := cpB
    refine endBit2B_ok hp F hk hsp (jw := jw) (o := o) (c := 1) (by regs_ok hR) (by mid_ok hM) hI2 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ ?hS ?_ (by omega)
    case hS => intro t ht1 ht2; exact hS2 t ht1 (by rw [hb1]; omega)
    all_goals tnorm
    exacts [h11, h7, hP, hY, rfl, hX, h5]
  -- the halfword after the byte: its alignments
  · rw [and1_zero, h5] at hc_1
    rw [hY1]; omega
  · rw [and1_zero, h5] at hc_1
    rw [toNat_add_ofNat (by rw [hX]; omega), hX]; omega
  -- `8 - o` is 7: the byte, the halfword, the word
  · rw [and1_zero, h5] at hc_1
    rw [and2_zero, h5] at hc_2
    rw [and4_zero, h5] at hc
    obtain ⟨hI2, hS2⟩ := cpB
    obtain ⟨hI3, hS3⟩ := cpH 1 (BitVec.ofNat 64 (top.toNat - 16 + o) + 1#64)
      (r .x29 + r .x6 + 0xfffffffffffffff9#64) hI2 hS2 (by rw [toNat_add_ofNat (by rw [hX]; omega), hX]; omega)
      hY1 (by omega) (by omega)
    refine endWordB_ok hp F hk hsp (jw := jw) (o := o) (c := 3) (by regs_ok hR) (by mid_ok hM) hI3 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ ?hS (by omega)
    case hS => intro t ht1 ht2; exact hS3 t ht1 (by rw [hb2]; omega)
    all_goals tnorm
    exacts [h11, h7, hP, hY, by decide, hX]
  -- `8 - o` is 3: the byte and the halfword
  · rw [and1_zero, h5] at hc_1
    rw [and2_zero, h5] at hc_2
    rw [and4_zero, h5] at hc
    obtain ⟨hI2, hS2⟩ := cpB
    obtain ⟨hI3, hS3⟩ := cpH 1 (BitVec.ofNat 64 (top.toNat - 16 + o) + 1#64)
      (r .x29 + r .x6 + 0xfffffffffffffff9#64) hI2 hS2 (by rw [toNat_add_ofNat (by rw [hX]; omega), hX]; omega)
      hY1 (by omega) (by omega)
    refine lastB_ok hp F hk hsp (jw := jw) (o := o) (by regs_ok hR) (by mid_ok hM) hI3 ho1 ho8 ?_ ?_ ?_ ?hS
    case hS => intro t ht1 ht2; exact hS3 t ht1 (by rw [hb2]; omega)
    all_goals tnorm
    exacts [h11, h7, hP]
  -- the halfword alone: its alignments
  · rw [and1_zero, h5] at hc_1
    rw [hY]; omega
  · rw [and1_zero, h5] at hc_1
    rw [hX]; omega
  -- `8 - o` is 6: the halfword and the word
  · rw [and1_zero, h5] at hc_1
    rw [and2_zero, h5] at hc_2
    rw [and4_zero, h5] at hc
    obtain ⟨hI3, hS3⟩ := cpH 0 (BitVec.ofNat 64 (top.toNat - 16 + o)) (r .x29 + r .x6 + 0xfffffffffffffff8#64) hI1
      (fun t h1 h2 => absurd h2 (by omega)) (by rw [hX, Nat.add_zero]) (by rw [hY, Nat.add_zero]) (by omega)
      (by omega)
    refine endWordB_ok hp F hk hsp (jw := jw) (o := o) (c := 2) (by regs_ok hR) (by mid_ok hM) hI3 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ ?hS (by omega)
    case hS => intro t ht1 ht2; exact hS3 t ht1 (by rw [hb2]; omega)
    all_goals tnorm
    exacts [h11, h7, hP, hY, by decide, hX]
  -- `8 - o` is 2: the halfword
  · rw [and1_zero, h5] at hc_1
    rw [and2_zero, h5] at hc_2
    rw [and4_zero, h5] at hc
    obtain ⟨hI3, hS3⟩ := cpH 0 (BitVec.ofNat 64 (top.toNat - 16 + o)) (r .x29 + r .x6 + 0xfffffffffffffff8#64) hI1
      (fun t h1 h2 => absurd h2 (by omega)) (by rw [hX, Nat.add_zero]) (by rw [hY, Nat.add_zero]) (by omega)
      (by omega)
    refine lastB_ok hp F hk hsp (jw := jw) (o := o) (by regs_ok hR) (by mid_ok hM) hI3 ho1 ho8 ?_ ?_ ?_ ?hS
    case hS => intro t ht1 ht2; exact hS3 t ht1 (by rw [hb2]; omega)
    all_goals tnorm
    exacts [h11, h7, hP]
  -- `8 - o` is 4: the word alone
  · rw [and1_zero, h5] at hc_1
    rw [and2_zero, h5] at hc
    refine endBit2B_ok hp F hk hsp (jw := jw) (o := o) (c := 0) (by regs_ok hR) (by mid_ok hM) hI1 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ ?hS ?_ (by omega)
    case hS => intro t ht1 ht2; omega
    all_goals tnorm
    exacts [h11, h7, hP, hY, rfl, hX, h5]

/-- The misaligned doublewords' loop at its head, the bytes from `j` on copied: `x29 + x5` the source doubleword
    `x28` was loaded from, `o` bytes below the source's `j`-th byte, `x17 + x5` the destination's `j`-th byte, `x5`
    minus the prefix's `nt` bytes. -/
def HInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (jw o nt j : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  Regs ret top regs r ∧ Mid regs r jw ∧ BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M j ∧
    (r .x29).toNat + o = (regs .x11).toNat + j + nt ∧ (r .x17).toNat = (regs .x10).toNat + j + nt ∧
    r .x5 = 0#64 - BitVec.ofNat 64 nt ∧ nt < 8 ∧
    (∀ t, t < o → extractByte (r .x28) t = bat m ((regs .x11).toNat + j - o + t)) ∧
    (r .x30).toNat = (regs .x10).toNat + jw % 8 + 8 ∧ (r .x7).toNat = 8 * o ∧
    (r .x12 &&& 63#64).toNat = 64 - 8 * o ∧ (r .x6).toNat = o ∧ jw % 8 + 16 ≤ j ∧ j ≤ jw ∧ (jw - j) % 8 = 0

-- `rv_symT` over the loop's body runs past the default budget.
set_option maxHeartbeats 1000000 in
/-- The doublewords of a misaligned source, from the end, each reassembled from two source doublewords. -/
theorem loopH_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw o nt : Nat} (ho1 : 0 < o) (ho8 : o < 8)
    (hso : ((regs .x11).toNat + jw) % 8 = o) :
    ∀ j r M, HInv env ret top regs m jw o nt j r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 100, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (HInv env ret top regs m jw o nt)
    fun j r M hH ih => ?_
  obtain ⟨hR, hM, hI, h29, h17, -, hnt, hP, h30, h7, h12, h6, hj0, hjw, hj8⟩ := id hH
  fx_facts F hI
  have hx2 := hR.2.1
  have hM' := hM
  obtain ⟨h13, h14, h15, h16, hd8, hjw8, hjn⟩ := hM'
  have hnt' : (BitVec.ofNat 64 nt).toNat = nt := by rw [BitVec.toNat_ofNat]; omega
  have hA : (r .x29 + r .x5 + 0xfffffffffffffff8#64).toNat = (regs .x11).toNat + j - o - 8 := by
    rw [BitVec.toNat_add, hH.2.2.2.2.2.1, toNat_add_neg (by omega), hnt']; simp only [BitVec.toNat_ofNat]; omega
  have hD : (r .x17 + r .x5 + 0xfffffffffffffff8#64).toNat = (regs .x10).toNat + (j - 8) := by
    rw [BitVec.toNat_add, hH.2.2.2.2.2.1, toNat_add_neg (by omega), hnt']; simp only [BitVec.toNat_ofNat]; omega
  have hD' : (r .x17 + 0xfffffffffffffff8#64 + r .x5).toNat = (regs .x10).toNat + (j - 8) := by
    rw [BitVec.add_assoc, BitVec.add_comm 0xfffffffffffffff8#64, ← BitVec.add_assoc, hD]
  have hS' : (r .x29 + 0xfffffffffffffff8#64 + r .x5).toNat = (regs .x11).toNat + j - o - 8 := by
    rw [BitVec.add_assoc, BitVec.add_comm 0xfffffffffffffff8#64, ← BitVec.add_assoc, hA]
  have hA8 : (r .x29 + r .x5 + 0xfffffffffffffff8#64).toNat % 8 = 0 := by rw [hA]; omega
  clear h13 h14 h15 h16
  have s1 := (shamt h7 ho1 ho8).1
  have hcur : ∀ t, t < 8 → extractByte (M.getMem (r .x29 + r .x5 + 0xfffffffffffffff8#64)) t =
      bat m ((regs .x11).toNat + (j - 8) - o + t) := by
    intro t ht
    rw [extractByte_getMem hA8 ht, hA, show (regs .x11).toNat + j - o - 8 + t = (regs .x11).toNat + (j - 8) - o + t
      by omega]
    exact F.src hI (by omega) (by omega) (by omega)
  have hv : ∀ t, t < 8 → extractByte (M.getMem (r .x29 + r .x5 + 0xfffffffffffffff8#64) >>> (r .x7 &&& 63#64).toNat |||
      r .x28 <<< (r .x12 &&& 63#64).toNat) t = bat m ((regs .x11).toNat + (j - 8) + t) := by
    intro t ht
    rw [s1, h12, extractByte_shr_or_shl _ _ o t ho1 ho8 ht]
    split
    · rw [hcur _ (by omega)]; exact bat_eq (by omega)
    · rw [hP _ (by omega)]; exact bat_eq (by omega)
  have hI0 : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (j - 8 + 8) := by
    rwa [Nat.sub_add_cancel (by omega)]
  have hI' := hI0.word F.toFx hD (by omega) (by omega) hv
  have h5 : True → r .x5 = 0#64 - BitVec.ofNat 64 nt := fun _ => hH.2.2.2.2.2.1
  have hcur' : True → _ := fun _ => hcur
  clear hI0 hH hv hcur
  have hR' : True → Regs ret top regs r := fun _ => hR
  have hM'' : True → Mid regs r jw := fun _ => hM
  clear hR hM
  have hwA : inWindow (r .x29 + r .x5 + 0xfffffffffffffff8#64) 8 = true := by
    rw [inWindow_iff, hA]; omega
  have hwD : inWindow (r .x17 + r .x5 + 0xfffffffffffffff8#64) 8 = true := by
    rcases hdw with hd | hd
    · exact hW.heapObj (by rw [hD]; omega) (by rw [hD]; omega)
    · exact hW.stackObj (by rw [hD]; omega) (by rw [hD]; omega)
  rv_symT hp stop [104, 376] with [hx2]
  refine TotalRv.label hp rfl ?_
  refine TotalRv.ld8 hp rfl (by tnorm; exact hwA) (by tnorm; exact hA8) ?_
  tnorm
  rv_symT hp stop [376]
  · have hc' := BitVec.lt_def.1 hc
    rw [hD'] at hc'
    clear hc
    have hR := hR' trivial
    have hM := hM'' trivial
    refine ih (j - 8) _ _ (by omega) ⟨by regs_ok hR, by mid_ok hM, hI', ?_, ?_, ?_, hnt, ?_, ?_, ?_, ?_, ?_,
      by omega, by omega, by omega⟩
    · tnorm; rw [toNat_top8 (by omega)]; omega
    · tnorm; rw [toNat_top8 (by omega)]; omega
    · tnorm; exact h5 trivial
    · tnorm; intro t ht; rw [hcur' trivial t (by omega)]
    all_goals tnorm
    exacts [h30, h7, h12, h6]
  · have hc' := BitVec.le_def.1 hc
    rw [hD'] at hc'
    clear hc
    have hR := hR' trivial
    have hM := hM'' trivial
    have e : j - 8 = jw % 8 + 8 := by clear * - hc' h30 hj0 hj8 hjw; omega
    rw [e] at hI'
    refine endB_ok hp F hk hsp (jw := jw) (o := o) (by regs_ok hR) (by mid_ok hM) hI' ho1 ho8 hso ?_ ?_ ?_ ?_ ?_
    · tnorm; rw [hD']; omega
    · tnorm; exact h7
    · tnorm; intro t ht; rw [hcur' trivial t (by omega)]; exact bat_eq (by omega)
    · tnorm; rw [hS']; omega
    · tnorm; exact h6

/-- After `load_aligned_partial`: the scratch doubleword holds the source's `o` bytes up to its `jw`-th; to the
    loop over the destination's doublewords, or with one doubleword only, to its last. -/
theorem prevB_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw o nt : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M jw)
    (ho1 : 0 < o) (ho8 : o < 8) (hso : ((regs .x11).toNat + jw) % 8 = o)
    (h7 : (r .x7).toNat = (regs .x10).toNat + jw % 8) (h6 : (r .x6).toNat = o)
    (h11 : (r .x11).toNat = (regs .x11).toNat) (h12 : (r .x12).toNat = (regs .x12).toNat)
    (h17 : (r .x17).toNat = (regs .x10).toNat + jw + nt) (h5 : r .x5 = 0#64 - BitVec.ofNat 64 nt) (hnt : nt < 8)
    (hn : jw + nt = (regs .x12).toNat) (h29 : (r .x29).toNat + o = (regs .x11).toNat + jw)
    (hS : ∀ t, t < o → bat M (top.toNat - 16 + t) = bat m ((regs .x11).toNat + jw - o + t)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 84, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have hs16 := slot_addr hx2 (by omega)
  have hM' := hM
  obtain ⟨h13, h14, h15, h16, hd8, hjw8, hjn⟩ := hM'
  have h8o := toNat_shl3 (x := r .x6) (by omega)
  rw [h6] at h8o
  have s2 := (shamt h8o ho1 ho8).2
  have h30 : (r .x7 + 8#64).toNat = (regs .x10).toNat + jw % 8 + 8 := by rw [BitVec.toNat_add]; simp; omega
  have h29' : (r .x11 + (r .x12 - r .x6)).toNat + o = (regs .x11).toNat + jw + nt := by
    rw [BitVec.toNat_add, BitVec.toNat_sub]; omega
  have hP : ∀ t, t < o → extractByte (M.getMem (r .x2)) t = bat m ((regs .x11).toNat + jw - o + t) := by
    intro t ht
    rw [extractByte_getMem (by rw [hs16]; omega) (by omega), hs16]; exact hS t ht
  have hR' : True → Regs ret top regs r := fun _ => hR
  have hM'' : True → Mid regs r jw := fun _ => hM
  clear hR hM h16 h14 h15
  rv_symT hp stop [100, 376] with [hx2]
  · have hc' := BitVec.le_def.1 hc
    rw [h30] at hc'
    clear hc
    have e : jw = jw % 8 + 8 := by clear * - hc' h13 hjw8; omega
    rw [e] at hI
    have hR := hR' trivial
    have hM := hM'' trivial
    refine endB_ok hp F hk hsp (jw := jw) (o := o) (by regs_ok hR) (by mid_ok hM) hI ho1 ho8 hso ?_ ?_ ?_ ?_ ?_
    · tnorm; omega
    · tnorm; exact h8o
    · tnorm; intro t ht; rw [hP t ht]; exact bat_eq (by omega)
    · tnorm; omega
    · tnorm; exact h6
  · have hc' := BitVec.lt_def.1 hc
    rw [h30] at hc'
    clear hc
    have hR := hR' trivial
    have hM := hM'' trivial
    refine loopH_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) ho1 ho8 hso jw _ _ ⟨by regs_ok hR, by mid_ok hM, hI,
      ?_, ?_, ?_, hnt, ?_, ?_, ?_, ?_, ?_, by omega, le_rfl, by simp⟩
    · tnorm; exact h29'
    · tnorm; exact h17
    · tnorm; exact h5
    · tnorm; exact hP
    · tnorm; exact h30
    · tnorm; exact h8o
    · tnorm; exact s2
    · tnorm; exact h6

/-- The last byte of `load_aligned_partial`, at `x28 = o - 1`. -/
theorem lastByteB_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw o nt : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M jw)
    (ho1 : 0 < o) (ho8 : o < 8) (hso : ((regs .x11).toNat + jw) % 8 = o)
    (h7 : (r .x7).toNat = (regs .x10).toNat + jw % 8) (h6 : (r .x6).toNat = o)
    (h11 : (r .x11).toNat = (regs .x11).toNat) (h12 : (r .x12).toNat = (regs .x12).toNat)
    (h17 : (r .x17).toNat = (regs .x10).toNat + jw + nt) (h5 : r .x5 = 0#64 - BitVec.ofNat 64 nt) (hnt : nt < 8)
    (hn : jw + nt = (regs .x12).toNat) (h29 : (r .x29).toNat + o = (regs .x11).toNat + jw)
    (h28 : (r .x28).toNat + 1 = o)
    (hS : ∀ t, t < o - 1 → bat M (top.toNat - 16 + t) = bat m ((regs .x11).toNat + jw - o + t)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 74, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have hs16 := slot_addr hx2 (by omega)
  have hb1 : Width.b1.bytes = 1 := rfl
  have hjn := hM.2.2.2.2.2.2
  have hjw8 := hM.2.2.2.2.2.1
  have hX : r .x2 ||| r .x28 = BitVec.ofNat 64 (top.toNat - 16 + (o - 1)) := by
    rw [or_eq_add (by rw [hs16]; omega) (by omega)]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hs16, BitVec.toNat_ofNat]; omega
  have hY : (r .x29 + r .x28).toNat = (regs .x11).toNat + jw - o + (o - 1) := by rw [BitVec.toNat_add]; omega
  obtain ⟨hI', hS'⟩ := slot_copy16 (m := m) (w := .b1) (lo := 0) (i := o - 1) (B := (regs .x11).toNat + jw - o)
    (P := fun M' => BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' jw)
    (X := r .x2 ||| r .x28) (v := Tactic.loadVal .b1 M (r .x29 + r .x28))
    (fun _ h => h.slot F.toFx (by rw [hX, BitVec.toNat_ofNat]; omega) (by rw [hX, BitVec.toNat_ofNat, hb1]; omega)
      (Nat.mod_one _)) hI (by omega) (fun t _ ht => hS t ht) (by rw [hX, BitVec.toNat_ofNat]; omega) (Nat.mod_one _)
    (by rw [hb1]; omega) (fun u hu => by
      have := extractByte_load (M := M) (x := r .x29 + r .x28) (u := u) false (Nat.mod_one _) hu
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [this, hY]
      have hu0 : u = 0 := by rw [hb1] at hu; omega
      subst hu0
      have hoS : o ≤ (regs .x11).toNat + jw := by omega
      exact (F.src (a := (regs .x11).toNat + jw - o + (o - 1) + 0) hI hjn (by omega)
        (by omega)).trans (bat_eq (by omega)))
  have hwX : inWindow (r .x2 ||| r .x28) 1 = true := by
    rw [hX]; exact hW.stack (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega)
  have hR' : True → Regs ret top regs r := fun _ => hR
  have hM'' : True → Mid regs r jw := fun _ => hM
  clear hR hM
  rv_symT hp stop [84] with [hx2]
  · exact hwX
  have hR := hR' trivial
  have hM := hM'' trivial
  refine prevB_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) (by regs_ok hR) (by mid_ok hM) hI' ho1 ho8 hso
    ?_ ?_ ?_ ?_ ?_ ?_ hnt hn ?_ ?hS
  case hS => intro t ht; exact hS' t (Nat.zero_le _) (by rw [hb1]; omega)
  all_goals tnorm
  exacts [h7, h6, h11, h12, h17, h5, h29]

/-- `load_aligned_partial` at its last chunk: a byte if `o` is odd, the bytes below `o`'s low bit copied. -/
theorem bit0B_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw o nt : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M jw)
    (ho1 : 0 < o) (ho8 : o < 8) (hso : ((regs .x11).toNat + jw) % 8 = o)
    (h7 : (r .x7).toNat = (regs .x10).toNat + jw % 8) (h6 : (r .x6).toNat = o)
    (h11 : (r .x11).toNat = (regs .x11).toNat) (h12 : (r .x12).toNat = (regs .x12).toNat)
    (h17 : (r .x17).toNat = (regs .x10).toNat + jw + nt) (h5 : r .x5 = 0#64 - BitVec.ofNat 64 nt) (hnt : nt < 8)
    (hn : jw + nt = (regs .x12).toNat) (h29 : (r .x29).toNat + o = (regs .x11).toNat + jw)
    (h28 : (r .x28).toNat = o / 2 * 2)
    (hS : ∀ t, t < o / 2 * 2 → bat M (top.toNat - 16 + t) = bat m ((regs .x11).toNat + jw - o + t)) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 70, ret, top⟩ :: rest, r, M⟩ := by
  have hx2 := hR.2.1
  have h14 := hM.2.1
  rv_symT hp stop [74, 84] with [hx2]
  · have := (and1_zero _).1 hc
    refine prevB_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) (by regs_ok hR) (by mid_ok hM) hI ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ hnt hn ?_ ?hS
    case hS => intro t ht; exact hS t (by omega)
    all_goals tnorm
    exacts [h7, h6, h11, h12, h17, h5, h29]
  · have : ¬ (r .x14).toNat % 2 = 0 := mt (and1_zero _).2 hc
    refine lastByteB_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) (by regs_ok hR) (by mid_ok hM) hI ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ hnt hn ?_ ?_ ?hS
    case hS => intro t ht; exact hS t (by omega)
    all_goals tnorm
    exacts [h7, h6, h11, h12, h17, h5, h29, by omega]

-- `rv_symT` over the six paths of the partial load runs past the default budget.
set_option maxHeartbeats 1000000 in
/-- `load_aligned_partial`: the source's `o` bytes up to its `jw`-th into the scratch doubleword, a word, a halfword
    and a byte as `o`'s bits say. -/
theorem misB_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw o nt : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r) (hM : Mid regs r jw)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M jw)
    (ho1 : 0 < o) (ho8 : o < 8) (hso : ((regs .x11).toNat + jw) % 8 = o)
    (h7 : (r .x7).toNat = (regs .x10).toNat + jw % 8) (h6 : (r .x6).toNat = o)
    (h11 : (r .x11).toNat = (regs .x11).toNat) (h12 : (r .x12).toNat = (regs .x12).toNat)
    (h17 : (r .x17).toNat = (regs .x10).toNat + jw + nt) (h5 : r .x5 = 0#64 - BitVec.ofNat 64 nt) (hnt : nt < 8)
    (hn : jw + nt = (regs .x12).toNat) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 56, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have hs16 := slot_addr hx2 (by omega)
  have hjn := hM.2.2.2.2.2.2
  have hjw8 := hM.2.2.2.2.2.1
  have h14 := hM.2.1
  have hb2 : Width.b2.bytes = 2 := rfl
  have hb4 : Width.b4.bytes = 4 := rfl
  have hb8 : Width.b8.bytes = 8 := rfl
  have hY : (r .x14 - r .x6).toNat = (regs .x11).toNat + jw - o := by rw [BitVec.toNat_sub]; omega
  have hY4 : (r .x14 - r .x6 + 4#64).toNat = (regs .x11).toNat + jw - o + 4 := by
    rw [BitVec.toNat_add, hY, show (4#64 : Word).toNat = 4 from rfl]; omega
  have hX4 : r .x2 ||| 4#64 = BitVec.ofNat 64 (top.toNat - 12) := by
    rw [or_eq_add (by rw [hs16]; omega) (by decide)]
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hs16, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]
    omega
  have h12' : (BitVec.ofNat 64 (top.toNat - 12)).toNat = top.toNat - 12 := by rw [BitVec.toNat_ofNat]; omega
  have hPs : ∀ (w : Width) (X v : Word) M', top.toNat - 16 ≤ X.toNat → X.toNat + w.bytes ≤ top.toNat - 8 →
      X.toNat % w.bytes = 0 →
      BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' jw →
      BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m (Tactic.storeMem w M' X v) jw :=
    fun w X v M' h1 h2 h3 h => h.slot F.toFx h1 h2 h3
  have src : ∀ M', BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' jw → ∀ u, u < o →
      bat M' ((regs .x11).toNat + jw - o + u) = bat m ((regs .x11).toNat + jw - o + u) :=
    fun M' hI' u hu => F.src hI' hjn (by omega) (by omega)
  have hI1 := hPs .b8 (r .x2) 0#64 M (by omega) (by rw [hb8]; omega) (by rw [hs16, hb8]; omega) hI
  -- the halfword or the word at the slot's start
  have cp0 := fun (w : Width) (hw : w = .b2 ∨ w = .b4) (hwo : w.bytes ≤ o) =>
    slot_copy16 (m := m) (M := Tactic.storeMem .b8 M (r .x2) 0#64) (top := top) (w := w) (X := r .x2) (i := 0)
      (lo := 0) (B := (regs .x11).toNat + jw - o)
      (P := fun M' => BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' jw)
      (v := (UnOp.sext w).eval (Tactic.loadVal w (Tactic.storeMem .b8 M (r .x2) 0#64) (r .x14 - r .x6)))
      (fun M' h => hPs w (r .x2) _ M' (by omega)
        (by rcases hw with rfl | rfl <;> (rw [hs16]; simp only [Width.bytes]; omega))
        (by rcases hw with rfl | rfl <;> (rw [hs16]; simp only [Width.bytes]; omega)) h) hI1 (by omega)
      (fun _ _ h => absurd h (Nat.not_lt_zero _)) (by rw [hs16]; rfl)
      (by rcases hw with rfl | rfl <;> (rw [hs16]; simp only [Width.bytes]; omega))
      (by rcases hw with rfl | rfl <;> decide) (fun u hu => by
        have := extractByte_load (M := Tactic.storeMem .b8 M (r .x2) 0#64) (x := r .x14 - r .x6) (u := u) true
          (by rcases hw with rfl | rfl <;> (rw [hY]; simp only [Width.bytes]; omega)) hu
        simp only [↓reduceIte] at this
        rw [this, hY, src _ hI1 u (by omega), Nat.add_zero])
  -- the halfword at byte 4, after the word
  have cp4 := fun {M2 : MachineState}
      (hI2 : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M2 jw)
      (hS2 : ∀ t, 0 ≤ t → t < 0 + Width.b4.bytes → bat M2 (top.toNat - 16 + t) =
        bat m ((regs .x11).toNat + jw - o + t)) (ho6 : 6 ≤ o) =>
    slot_copy16 (m := m) (w := .b2) (X := BitVec.ofNat 64 (top.toNat - 12)) (i := 4) (lo := 0)
      (B := (regs .x11).toNat + jw - o)
      (P := fun M' => BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M' jw)
      (v := (UnOp.sext .b2).eval (Tactic.loadVal .b2 M2 (r .x14 - r .x6 + 4#64)))
      (fun M' h => hPs .b2 (BitVec.ofNat 64 (top.toNat - 12)) _ M' (by rw [h12']; omega) (by rw [h12', hb2]; omega)
        (by rw [h12', hb2]; omega) h) hI2
      (by omega) (fun t h1 ht => hS2 t h1 (by rw [hb4]; omega)) (by rw [h12']; omega) (by rw [h12', hb2]; omega)
      (by decide) (fun u hu => by
        have := extractByte_load (M := M2) (x := r .x14 - r .x6 + 4#64) (u := u) true (by rw [hY4, hb2]; omega) hu
        simp only [↓reduceIte] at this
        rw [this, hY4, show (regs .x11).toNat + jw - o + 4 + u = (regs .x11).toNat + jw - o + (u + 4) by omega,
          src _ hI2 _ (by rw [hb2] at hu; omega)])
  have hR' : True → Regs ret top regs r := fun _ => hR
  have hM'' : True → Mid regs r jw := fun _ => hM
  clear hR hM
  have hX0 : r .x2 ||| 0#64 = r .x2 := BitVec.or_zero
  have ho : (r .x14).toNat % 8 = o := by omega
  rv_symT hp stop [70, 74, 84] with [hx2]
  all_goals try rw [hX4]
  all_goals try rw [hX0]
  rv_closeT
  -- `o` is 4 or 5: a word
  · have ho4 : 4 ≤ o := by have := BitVec.le_def.1 hc_1; rw [h6] at this; exact this
    have ho2 := (and2_zero _).1 hc
    obtain ⟨hI2, hS2⟩ := cp0 .b4 (.inr rfl) (by rw [hb4]; omega)
    have hR := hR' trivial
    have hM := hM'' trivial
    refine bit0B_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) (by regs_ok hR) (by mid_ok hM) hI2 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ hnt hn ?_ ?_ ?hS
    case hS => intro t ht; exact hS2 t (Nat.zero_le _) (by rw [hb4]; omega)
    all_goals tnorm
    exacts [h7, h6, h11, h12, h17, h5, by omega, by tlit]
  -- `o` is 7: a word, a halfword, then the last byte
  · have ho4 : 4 ≤ o := by have := BitVec.le_def.1 hc_1; rw [h6] at this; exact this
    have ho2 : ¬ (r .x14).toNat % 4 < 2 := mt (and2_zero _).2 hc_2
    have ho0 : ¬ (r .x14).toNat % 2 = 0 := mt (and1_zero _).2 hc
    obtain ⟨hI2, hS2⟩ := cp0 .b4 (.inr rfl) (by rw [hb4]; omega)
    obtain ⟨hI3, hS3⟩ := cp4 hI2 hS2 (by omega)
    have hR := hR' trivial
    have hM := hM'' trivial
    refine lastByteB_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) (by regs_ok hR) (by mid_ok hM) hI3 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ hnt hn ?_ ?_ ?hS
    case hS => intro t ht; exact hS3 t (Nat.zero_le _) (by rw [hb2]; omega)
    all_goals tnorm
    exacts [h7, h6, h11, h12, h17, h5, by omega, by tlit]
  -- `o` is 6: a word and a halfword
  · have ho4 : 4 ≤ o := by have := BitVec.le_def.1 hc_1; rw [h6] at this; exact this
    have ho2 : ¬ (r .x14).toNat % 4 < 2 := mt (and2_zero _).2 hc_2
    have ho0 := (and1_zero _).1 hc
    obtain ⟨hI2, hS2⟩ := cp0 .b4 (.inr rfl) (by rw [hb4]; omega)
    obtain ⟨hI3, hS3⟩ := cp4 hI2 hS2 (by omega)
    have hR := hR' trivial
    have hM := hM'' trivial
    refine prevB_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) (by regs_ok hR) (by mid_ok hM) hI3 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ hnt hn ?_ ?hS
    case hS => intro t ht; exact hS3 t (Nat.zero_le _) (by rw [hb2]; omega)
    all_goals tnorm
    exacts [h7, h6, h11, h12, h17, h5, by omega]
  -- `o` is 3: a halfword, then the last byte
  · have ho4 : o < 4 := by have := BitVec.lt_def.1 hc_1; rw [h6] at this; exact this
    have ho2 : ¬ (r .x14).toNat % 4 < 2 := mt (and2_zero _).2 hc_2
    have ho0 : ¬ (r .x14).toNat % 2 = 0 := mt (and1_zero _).2 hc
    obtain ⟨hI2, hS2⟩ := cp0 .b2 (.inl rfl) (by rw [hb2]; omega)
    have hR := hR' trivial
    have hM := hM'' trivial
    refine lastByteB_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) (by regs_ok hR) (by mid_ok hM) hI2 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ hnt hn ?_ ?_ ?hS
    case hS => intro t ht; exact hS2 t (Nat.zero_le _) (by rw [hb2]; omega)
    all_goals tnorm
    exacts [h7, h6, h11, h12, h17, h5, by omega, by tlit]
  -- `o` is 2: a halfword
  · have ho4 : o < 4 := by have := BitVec.lt_def.1 hc_1; rw [h6] at this; exact this
    have ho2 : ¬ (r .x14).toNat % 4 < 2 := mt (and2_zero _).2 hc_2
    have ho0 := (and1_zero _).1 hc
    obtain ⟨hI2, hS2⟩ := cp0 .b2 (.inl rfl) (by rw [hb2]; omega)
    have hR := hR' trivial
    have hM := hM'' trivial
    refine prevB_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) (by regs_ok hR) (by mid_ok hM) hI2 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ hnt hn ?_ ?hS
    case hS => intro t ht; exact hS2 t (Nat.zero_le _) (by rw [hb2]; omega)
    all_goals tnorm
    exacts [h7, h6, h11, h12, h17, h5, by omega]
  -- `o` is 1: the byte alone
  · have ho4 : o < 4 := by have := BitVec.lt_def.1 hc_1; rw [h6] at this; exact this
    have ho2 := (and2_zero _).1 hc
    have hR := hR' trivial
    have hM := hM'' trivial
    refine bit0B_ok hp F hk hsp (jw := jw) (o := o) (nt := nt) (by regs_ok hR) (by mid_ok hM) hI1 ho1 ho8 hso
      ?_ ?_ ?_ ?_ ?_ ?_ hnt hn ?_ ?_ ?hS
    case hS => intro t ht; omega
    all_goals tnorm
    exacts [h7, h6, h11, h12, h17, h5, by omega, by tlit]

/-! ## The prefix and the entry -/

/-- After the prefix, the bytes from `jw = n - nt` on copied, the destination's end `jw` 8-byte aligned: the
    doublewords, by the source's alignment. -/
theorem mid_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {jw nt : Nat} {r : Reg → Word}
    {M : MachineState} (hR : Regs ret top regs r)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M jw)
    (hn : jw + nt = (regs .x12).toNat) (hnt : nt < 8) (h16n : 16 ≤ (regs .x12).toNat)
    (hd8 : ((regs .x10).toNat + jw) % 8 = 0) (h13 : (r .x13).toNat = (regs .x10).toNat + jw)
    (h14 : (r .x14).toNat = (regs .x11).toNat + (regs .x12).toNat) (h15 : (r .x15).toNat = nt)
    (h5 : r .x5 = 0#64 - BitVec.ofNat 64 nt) (h11 : (r .x11).toNat = (regs .x11).toNat)
    (h12 : (r .x12).toNat = (regs .x12).toNat) (h17 : (r .x17).toNat = (regs .x10).toNat + (regs .x12).toNat) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 42, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have hnt' : (BitVec.ofNat 64 nt).toNat = nt := by rw [BitVec.toNat_ofNat]; omega
  have hA : (r .x14 + r .x5).toNat = (regs .x11).toNat + jw := by
    rw [h5, toNat_add_neg (by omega), hnt']; omega
  have hB : (r .x12 - r .x15).toNat = jw := by rw [BitVec.toNat_sub]; omega
  have hW8 := toNat_and_not7 (r .x12 - r .x15)
  rw [hB] at hW8
  have hW8' : (r .x12 - r .x15 &&& 18446744073709551608#64) = BitVec.ofNat 64 (jw - jw % 8) :=
    BitVec.eq_of_toNat_eq (by rw [hW8, BitVec.toNat_ofNat]; omega)
  have hC : (r .x13 - (r .x12 - r .x15 &&& 18446744073709551608#64)).toNat = (regs .x10).toNat + jw % 8 := by
    rw [BitVec.toNat_sub, hW8]; omega
  have ho := Proof.Runtime.Alloc.and7 (r .x14 + r .x5)
  rw [hA] at ho
  have hM : Mid regs (updReg (updReg (updReg (updReg (updReg (updReg r .x14 (r .x14 + r .x5)) .x15
      (r .x12 - r .x15)) .x7 (r .x12 - r .x15 &&& 18446744073709551608#64)) .x6 (r .x14 + r .x5 &&& 7#64)) .x16
      (0#64 - (r .x12 - r .x15 &&& 18446744073709551608#64))) .x7
      (r .x13 - (r .x12 - r .x15 &&& 18446744073709551608#64))) jw := by
    refine ⟨?_, ?_, ?_, ?_, hd8, by omega, by omega⟩ <;> tnorm
    · exact h13
    · exact hA
    · exact hB
    · rw [hW8']
  have hR' : True → Regs ret top regs r := fun _ => hR
  have hM' : True → _ := fun _ => hM
  clear hR hM
  rv_symT hp stop [56, 288] with [hx2]
  · have hc' : ((regs .x11).toNat + jw) % 8 = 0 := by rw [← ho, hc]; rfl
    have hR := hR' trivial
    refine alB_ok hp F hk hsp (jw := jw) (by regs_ok hR) (hM' trivial) hI ?_ ?_ hc'
    all_goals tnorm
    exacts [hC, h11]
  · have hc' : ¬ ((regs .x11).toNat + jw) % 8 = 0 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [ho, h]; rfl))
    have hR := hR' trivial
    refine misB_ok hp F hk hsp (jw := jw) (o := ((regs .x11).toNat + jw) % 8) (nt := nt) (by regs_ok hR)
      (hM' trivial) hI (by omega) (by omega) rfl ?_ ?_ ?_ ?_ ?_ h5 hnt hn
    all_goals tnorm
    exacts [hC, ho, h11, h12, by omega]

/-- The prefix's loop at its head, the bytes from `j` on copied: `x6` one past the next destination byte, `x16` the
    next source byte, `x13` the destination's last 8-byte boundary, `jw` bytes on. -/
def EInv (env : Env) (ret top : Word) (regs : Reg → Word) (m : MachineState) (jw nt j : Nat) (r : Reg → Word)
    (M : MachineState) : Prop :=
  Regs ret top regs r ∧ BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M j ∧
    (r .x6).toNat = (regs .x10).toNat + j ∧ (r .x16).toNat + 1 = (regs .x11).toNat + j ∧
    (r .x13).toNat = (regs .x10).toNat + jw ∧ jw < j ∧ j ≤ (regs .x12).toNat ∧
    jw + nt = (regs .x12).toNat ∧ nt < 8 ∧ 16 ≤ (regs .x12).toNat ∧ ((regs .x10).toNat + jw) % 8 = 0 ∧
    (r .x14).toNat = (regs .x11).toNat + (regs .x12).toNat ∧ (r .x15).toNat = nt ∧
    r .x5 = 0#64 - BitVec.ofNat 64 nt ∧ (r .x11).toNat = (regs .x11).toNat ∧ (r .x12).toNat = (regs .x12).toNat ∧
    (r .x17).toNat = (regs .x10).toNat + (regs .x12).toNat

/-- The prefix, a byte at a time from its end. -/
theorem loopE_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) (jw nt : Nat) :
    ∀ j r M, EInv env ret top regs m jw nt j r M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 30, ret, top⟩ :: rest, r, M⟩ := by
  refine Total.loop (I := rvIsa) (EInv env ret top regs m jw nt) fun j r M hE ih => ?_
  obtain ⟨hR, hI, h6, h16, h13, hjw, hjn, hn, hnt, h16n, hd8, h14, h15, -, h11, h12, h17⟩ := id hE
  fx_facts F hI
  have hx2 := hR.2.1
  have hv : extractByte ((M.getByte (r .x16)).zeroExtend 64) 0 = bat m ((regs .x11).toNat + (j - 1)) := by
    rw [extractByte_zext_getByte, show (r .x16).toNat = (regs .x11).toNat + (j - 1) by omega]
    exact F.src hI (by omega) (by omega) (by omega)
  have h6' : (r .x6 + 0xffffffffffffffff#64).toNat = (regs .x10).toNat + (j - 1) := by
    rw [toNat_dec (by omega)]; omega
  have hI0 : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (j - 1 + 1) := by
    rwa [Nat.sub_add_cancel (by omega)]
  have hI' := hI0.byte F.toFx h6' (by omega) hv
  have h5 := hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h5' : True → _ := fun _ => h5
  have hR' : True → Regs ret top regs r := fun _ => hR
  clear hE hI0 hR h5
  rv_symT hp stop [42] with [hx2]
  · have hc' := BitVec.lt_def.1 hc
    rw [h6'] at hc'
    clear hc
    have hR := hR' trivial
    refine ih (j - 1) _ _ (by omega) ⟨by regs_ok hR, hI', ?_, ?_, ?_, by omega, by omega, hn, hnt, h16n, hd8,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals tnorm
    · exact h6'
    · rw [toNat_dec (by omega)]; omega
    · exact h13
    · exact h14
    · exact h15
    · exact h5' trivial
    · exact h11
    · exact h12
    · exact h17
  · have hc' := BitVec.le_def.1 hc
    rw [h6'] at hc'
    clear hc
    have hR := hR' trivial
    have e : j - 1 = jw := by clear * - hc' h13 hjw; omega
    rw [e] at hI'
    refine mid_ok hp F hk hsp (jw := jw) (nt := nt) (by regs_ok hR) hI' hn hnt h16n hd8 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals tnorm
    exacts [h13, h14, h15, h5' trivial, h11, h12, h17]

/-- **The backward copy**, from its first instruction after `memmove`'s choice of direction, nothing copied yet. -/
theorem bwd_ok (hp : p[i]? = some (tmpl L)) (F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m)
    (hk : Cont env p Q ret top rest regs m) (hsp : regs .x2 = top) {r : Reg → Word} {M : MachineState}
    (hR : Regs ret top regs r)
    (hI : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M (regs .x12).toNat)
    (h11 : r .x11 = regs .x11) (h12 : r .x12 = regs .x12) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 8, ret, top⟩ :: rest, r, M⟩ := by
  fx_facts F hI
  have hx2 := hR.2.1
  have h10 := hR.2.2.2
  have e10 := congrArg BitVec.toNat h10
  have e11 := congrArg BitVec.toNat h11
  have e12 := congrArg BitVec.toNat h12
  have hdn := F.dn
  have hD : (r .x10 + r .x12).toNat = (regs .x10).toNat + (regs .x12).toNat := by rw [BitVec.toNat_add]; omega
  have hS : (r .x11 + r .x12).toNat = (regs .x11).toNat + (regs .x12).toNat := by rw [BitVec.toNat_add]; omega
  have hN7 := Proof.Runtime.Alloc.and7 (r .x10 + r .x12)
  have hNw := toNat_and_not7 (r .x10 + r .x12)
  rw [hD] at hN7 hNw
  have h16 : (16#64 : Word).toNat = 16 := rfl
  have hR' : True → Regs ret top regs r := fun _ => hR
  clear hR
  rv_symT hp stop [30, 42, 432] with [hx2]
  · have hc' := BitVec.lt_def.1 hc
    clear hc
    have hR := hR' trivial
    refine sfx_ok hp F hk hsp (c := (regs .x12).toNat) (by regs_ok hR) hI ?_ ?_ ?_ le_rfl
    all_goals tnorm
    exacts [hD, hS, e12]
  · have hc' := BitVec.le_def.1 hc
    have hc1 := BitVec.le_def.1 hc_1
    rw [hNw, hD] at hc'
    clear hc hc_1
    have hR := hR' trivial
    have h0 : ((regs .x10).toNat + (regs .x12).toNat) % 8 = 0 := by omega
    have hx15 : (r .x10 + r .x12 &&& 7#64) = BitVec.ofNat 64 0 :=
      BitVec.eq_of_toNat_eq (by rw [hN7, h0]; rfl)
    refine mid_ok hp F hk hsp (jw := (regs .x12).toNat) (nt := 0) (by regs_ok hR) hI (by omega) (by omega)
      (by rw [e12] at hc1; exact hc1) h0 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals tnorm
    · rw [hNw]; omega
    · exact hS
    · rw [hN7]; omega
    · rw [hx15]
    · exact e11
    · exact e12
    · exact hD
  · have hc' := BitVec.lt_def.1 hc
    have hc1 := BitVec.le_def.1 hc_1
    rw [hNw, hD] at hc'
    clear hc hc_1
    have hR := hR' trivial
    have hI0 : BInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m M
        ((regs .x12).toNat - ((regs .x10).toNat + (regs .x12).toNat) % 8 + ((regs .x10).toNat +
          (regs .x12).toNat) % 8) := by rwa [Nat.sub_add_cancel (by omega)]
    refine loopE_ok hp F hk hsp ((regs .x12).toNat - ((regs .x10).toNat + (regs .x12).toNat) % 8)
      (((regs .x10).toNat + (regs .x12).toNat) % 8) (regs .x12).toNat _ _ ⟨by regs_ok hR, hI, ?_, ?_, ?_,
      by omega, le_rfl, by omega, by omega, by rw [e12] at hc1; exact hc1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals tnorm
    · exact hD
    · rw [toNat_dec (by omega), hS]; omega
    · rw [hNw]; omega
    · exact hS
    · exact hN7
    · rw [show (r .x10 + r .x12 &&& 7#64) = BitVec.ofNat 64 (((regs .x10).toNat + (regs .x12).toNat) % 8) from
        BitVec.eq_of_toNat_eq (by rw [hN7, BitVec.toNat_ofNat]; omega)]
    · exact e11
    · exact e12
    · exact hD

end Rv64mc.Proof.Runtime.MemmoveBwdT
