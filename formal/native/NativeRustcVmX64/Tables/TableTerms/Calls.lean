module

public import NativeRustcVmX64.Tables.TableTerms.Iter

/-!
# `table_terms`: blocks and calls of the body (x86-64)

`block`: a body block from a literal start state, its result and the body after it. `callO`: a
call changing outputs; `callL`: `constraints_w`'s, changing the frame's constraints (offsets `144`
to `176`). The frame's words across them (`fw_block`, `fw_callO`, `fw_callL`); a callee's
`OutOk` of a part of an output (`outOk_sub`); `test %al, %al` of an `Option<()>` (`cAl_eval`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck
open NativeRustcVm (wordOf ewsOf)

public section

/-- A part of an output. -/
theorem outOk_sub [Labels] {m : MachineData} {t : BitVec 64} {a : DecArea} {x : BitVec 64}
    {n N o k : Nat} (h : OutOk m t a x n N) (hk : o + k ≤ n) :
    OutOk m t a (x + BitVec.ofNat 64 o) k N :=
  ⟨NativeRustcVm.Mapped.sub h.1 hk, NativeRustcVm.NoWrap.sub h.2.1 hk, apart_sub h.2.1 h.2.2.1 hk,
    apart_sub h.2.1 h.2.2.2.1 hk, apart_sub h.2.1 h.2.2.2.2.1 hk, apart_sub h.2.1 h.2.2.2.2.2 hk⟩

theorem okWord_toNat' (b : Bool) : (okWord b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

/-- `test %al, %al` of an `Option<()>` in AL: zero exactly when it is `None`. -/
theorem cAl_eval [Labels] {env : Env} {b : Bool}
    (h : (env.regs .rax).toNat % 256 = (okWord b).toNat) :
    cAl.eval env = !b := by
  show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (env.regs .rax) (env.regs .rax))
    (BitVec.ofNat 64 0) = !b
  rw [testAl_eq, h, okWord_toNat']
  cases b <;> rfl

theorem frame_wd {L : List (Nat × UInt64)} {p : Nat × UInt64} (hp : p ∈ L)
    (hL : ∀ p ∈ L, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280) : 8 ≤ p.1 ∧ p.1 + 8 ≤ 280 := hL p hp

variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- **A block of the body**, its writes in the frame and the regions `outs` of outputs. -/
theorem blockB (h : TableTermsPre a s heights forms m0) {d d' : MachineData} {o o' : Nat}
    (hb : Bd m0 272 N slots (outs m0) o d) {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {Sy : SState} (hwf : (E m0 d rest ret).WF) (hm : Match (E m0 d rest ret) Sy d')
    (hmid : MidOk 272 o' slots Sy = true) {os : List Nat} (hW : WrOk Sy os = true)
    (hR : ∀ r ∈ os, ∀ x, rest[r - 1]? = some x → ∀ q, NativeRustcVm.InRange x.1 x.2 q → outs m0 q) :
    Bd m0 272 N slots (outs m0) o' d' ∧
      NativeRustcVm.SameOutside d.dmem d'.dmem
        (fun q ↦ NativeRustcVm.InRange (stackBelow m0 N) N q ∨
          ∃ r ∈ os, ∃ x, rest[r - 1]? = some x ∧ NativeRustcVm.InRange x.1 x.2 q) := by
  refine ⟨hb.step (Pre.stack h) (by rw [N_eq]; omega) hwf hm hmid (fun p hp ↦ (slots_le p hp).2)
    hW hR, ?_⟩
  refine NativeRustcVm.SameOutside.mono (same_block hwf hm (writesIn_of_mid hmid)
    (belowRet_of_mid hmid) hW (X := fun q ↦ ∃ r ∈ os, ∃ x, rest[r - 1]? = some x ∧
      NativeRustcVm.InRange x.1 x.2 q) fun r hr x hx q hq ↦ ⟨r, hr, x, hx, hq⟩) fun q hq ↦ ?_
  rcases hq with hq | hq
  · exact .inl (fr_stack h hq)
  · exact .inr hq

/-- The frame's words a block left alone (`missO`). -/
theorem fw_block {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {Sy : SState} (hwf : (E m0 d rest ret).WF) (hm : Match (E m0 d rest ret) Sy d')
    (hin : writesIn Sy = true) {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, p.1 + 8 ≤ 280)
    (hmiss : missO Sy (L.map Prod.fst) = true) (hfw : FW m0 d L) : FW m0 d' L :=
  FW.block hwf hm hin hL hmiss hfw

/-- The frame's words a block left alone, by its `missO` over `UW ex`. -/
theorem fw_blockU {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {Sy : SState} (hwf : (E m0 d rest ret).WF) (hm : Match (E m0 d rest ret) Sy d')
    (hin : writesIn Sy = true) {ex : List Nat} (hmiss : missO Sy (UW ex) = true)
    {L : List (Nat × UInt64)} (hL : (L.map Prod.fst).all (fun o ↦ (UW ex).contains o) = true)
    (hle : ∀ p ∈ L, p.1 + 8 ≤ 280) (hfw : FW m0 d L) : FW m0 d' L :=
  FW.block hwf hm hin hle (missO_sub hmiss fun o ho ↦ by
    have := List.all_eq_true.mp hL o ho
    simpa using this) hfw

/-- A word a block wrote, at its offset in the frame. -/
theorem fw_wrote {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {Sy : SState} (hm : Match (E m0 d rest ret) Sy d') {o : Nat} (hle : o + 8 ≤ 280) {v : Sym}
    (hw : WordW 0 o v Sy) {w : UInt64} (hv : v.eval (E m0 d rest ret) = w.toBitVec) :
    FW m0 d' [(o, w)] := fun p hp ↦ by
  rw [List.mem_singleton] at hp; subst hp; exact wroteW hm hle hw hv

omit [Labels] in
theorem FW.append {d : MachineData} {L L' : List (Nat × UInt64)} (h : FW m0 d L)
    (h' : FW m0 d L') : FW m0 d (L ++ L') := fun p hp ↦ by
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

omit [Labels] in
theorem FW.left {d : MachineData} {L L' : List (Nat × UInt64)} (h : FW m0 d (L ++ L')) :
    FW m0 d L := fun p hp ↦ h p (List.mem_append_left _ hp)

omit [Labels] in
theorem FW.right {d : MachineData} {L L' : List (Nat × UInt64)} (h : FW m0 d (L ++ L')) :
    FW m0 d L' := fun p hp ↦ h p (List.mem_append_right _ hp)

omit [Labels] in
theorem FW.of_dmem {d d' : MachineData} {L : List (Nat × UInt64)} (hd : d'.dmem = d.dmem)
    (h : FW m0 d L) : FW m0 d' L := fun p hp ↦ by rw [hd]; exact h p hp

/-- **A call changing outputs** keeps the frame's words. -/
theorem fw_callO (h : TableTermsPre a s heights forms m0) {d d' : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 0 d) {Nc : Nat} (hle : 272 + Nc ≤ N)
    {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    (hRo : ∀ q, Ro q → outs m0 q) {L : List (Nat × UInt64)}
    (hL : ∀ p ∈ L, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280) (hfw : FW m0 d L) : FW m0 d' L :=
  FW.call hb (Pre.stack h) hle hso hL (fun p hp i hi hq ↦ outs_not_frame h (hRo _ hq)
    (frame_in_280 h (by have := hL p hp; omega))) hfw
where
  frame_in_280 (h : TableTermsPre a s heights forms m0) {j : Nat} (hj : j < 280) :
      NativeRustcVm.InRange (fb m0) 280 (off (fb m0) j) :=
    inRange_off_self hj (by norm_num)

/-- The frame's bytes `144` to `176`, the constraints. -/
@[expose] def loc (m0 : MachineData) (q : BitVec 64) : Prop := NativeRustcVm.InRange (off (fb m0) 144) 32 q

/-- **`constraints_w`'s call**, changing the frame's constraints, keeps the body. -/
theorem callL (h : TableTermsPre a s heights forms m0) {d d' : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 0 d) {Nc : Nat} (hle : 272 + Nc ≤ N) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ loc m0 q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q)) :
    Bd m0 272 N slots (outs m0) 8 d' := by
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (272 + 8) ≤ 2 ^ 64 := frame_noWrap (F := 272) hS (by rw [N_eq]; omega)
  have hloc : ∀ j, j < 144 ∨ 176 ≤ j → j < 280 → ¬ loc m0 (off (fb m0) j) := fun j hj hj' hq ↦ by
    unfold loc at hq
    rw [inRange_off_iff (by omega) (by omega)] at hq
    omega
  have hcal : ∀ j, 8 ≤ j → j < 280 →
      ¬ NativeRustcVm.InRange (stackBelow d Nc) Nc (off (fb m0) j) := fun j hj hj' hq ↦ by
    have := (hb.callee_in hS (Nat.zero_le _) (by simpa using hle) hq).2
    exact this (by
      rw [off_zero]; exact inRange_off_self (by omega) (by omega))
  refine hb.call_at hs hrsp hso (fun q hq ↦ ?_) (fun p hp i hi hq ↦ ?_) (fun j hj hq ↦ ?_)
  · rcases hq with hq | hq
    · right
      refine fr_stack h ?_
      unfold loc at hq
      have hnw' : NativeRustcVm.NoWrap (off (fb m0) 144) 32 := by
        unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega
      rw [inRange_iff' hnw', toNat_off (by omega)] at hq
      show NativeRustcVm.InRange (fb m0) 272 q
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
      omega
    · exact .inr (callee_stack h hb hle hq)
  · have hp' := slots_le p hp
    rcases hq with hq | hq
    · exact hloc _ (.inr (by omega)) (by omega) hq
    · exact hcal _ (by omega) (by omega) hq
  · rcases hq with hq | hq
    · exact hloc _ (.inr (by omega)) (by omega) hq
    · exact hcal _ (by omega) (by omega) hq

/-- **`constraints_w`'s call** keeps the frame's words outside the constraints. -/
theorem fw_callL (h : TableTermsPre a s heights forms m0) {d d' : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 0 d) {Nc : Nat} (hle : 272 + Nc ≤ N)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ loc m0 q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280 ∧ (p.1 + 8 ≤ 144 ∨ 176 ≤ p.1))
    (hfw : FW m0 d L) : FW m0 d' L := by
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (272 + 8) ≤ 2 ^ 64 := frame_noWrap (F := 272) hS (by rw [N_eq]; omega)
  refine FW.call hb hS hle hso (fun p hp ↦ ⟨(hL p hp).1, (hL p hp).2.1⟩) (fun p hp i hi hq ↦ ?_) hfw
  have hp' := hL p hp
  unfold loc at hq
  rw [inRange_off_iff (by omega) (by omega)] at hq
  omega

end

end NativeRustcVmX64.Tables.TableTerms
