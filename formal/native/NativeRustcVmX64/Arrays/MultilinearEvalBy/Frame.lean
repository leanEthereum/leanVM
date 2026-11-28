module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVm.Arrays.Mle

/-!
# `multilinear_eval_by`'s frame (x86-64)

Both instances of `multilinear_eval_by` push RBP, R15, R14, R13, R12, RBX and reserve 1160
bytes: their frame (`Arrays.Body` with `F = 1216`) is the 1216 bytes below the entry's RSP, its
base `fbOf`. They keep `i` at `fb + 16`, their arguments from `fb + 24` (`argVals`), a product at
`fb + 64`, the `full` flags at `fb + 80 + k` and the pending entries at `fb + 144 + 16 k`
(`k < 64`), the pushed registers from `fb + 1168` (`mleSlots`).

- Words at offsets of the frame (`ValsAt`), loaded (`val_load`), kept (`vals_congr`).
- The pending entries the frame holds (`pendOf`, the flags `0` or `1`: `FlagsOk`); a flag cleared
  (`pendOf_clear`), an entry pushed (`pendOf_set`), bytes kept (`pendOf_congr`).
- A block writing only between offsets `16` and `1168` keeps the body (`body_of_local`).
- The loops' invariants: the frame (`Fr`), the outer loop's head (`Outer`: `i` entries streamed)
  and the inner loop's (`Inner`: entry `i` carried to level `k`), over the entries `es` and the
  registers each instance keeps the flag's address, the level's offset `16 k` and the carried
  value in.
-/

namespace NativeRustcVmX64.Arrays.MleFrame

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (setP stream cont)

@[expose] public section

/-- The frame's base: `1216` bytes below the entry's RSP. -/
abbrev fbOf (m0 : MachineData) : BitVec 64 := stackBelow m0 1216

/-! ## The blocks' symbolic states -/

/-- A turn of the zeroing loop: the 64 bytes at `RSP + 136 + RAX`. -/
def zS : SState := init [64] (aliases := [(.bin .add .W64 (.reg .rsp) (.reg .rax), 0, -136)])
/-- `full[k]` at `rf`. -/
def flagS (rf : Reg64) : SState := init [1] [(rf, .ptr 0 0)]
/-- A pairing's loads: the frame's first 80 bytes (RSP at `8`), `full[k]` (`rf`), `pending[k]`
(`RSP + 136 + ri`), `point[k]` (`point + ri`, `point` the frame's word at `56`). -/
def pairS (rf ri : Reg64) : SState :=
  init [80, 1, 16, 16] [(.rsp, .ptr 0 8), (rf, .ptr 1 0)]
    (aliases := [(.bin .add .W64 (.ptr 0 8) (.reg ri), 2, -136),
      (.bin .add .W64 (.load 0 56 8) (.reg ri), 3, 0)])
/-- A pending entry's store: the frame's first 80 bytes, `full[k]` (`rf`), `pending[k]`. -/
def pushS (rf ri : Reg64) : SState :=
  init [80, 1, 16] [(.rsp, .ptr 0 8), (rf, .ptr 1 0)]
    (aliases := [(.bin .add .W64 (.ptr 0 8) (.reg ri), 2, -136)])
/-- Registers only. -/
def regsS : SState := init []

/-- The pushed registers' slots. -/
def mleSlots : List (Nat × Reg64) :=
  [(1168, .rbx), (1176, .r12), (1184, .r13), (1192, .r14), (1200, .r15), (1208, .rbp)]

/-- Level `k`'s pending entry: `full[k]` (the byte at `fb + 80 + k`) is `1`, the entry the one at
`fb + 144 + 16 k`. -/
def pendOf (d : DataMem) (fb : BitVec 64) (k : Nat) : Option EW :=
  if k < 64 ∧ d.get? (fb + BitVec.ofNat 64 (80 + k)) = some 1 then
    some (ewOf d (fb + BitVec.ofNat 64 (144 + 16 * k)))
  else none

/-- Every flag is `0` or `1`. -/
def FlagsOk (d : DataMem) (fb : BitVec 64) : Prop :=
  ∀ k < 64, d.get? (fb + BitVec.ofNat 64 (80 + k)) = some 0 ∨
    d.get? (fb + BitVec.ofNat 64 (80 + k)) = some 1

/-- The words `v` at the offsets `o` from `fb`, for each `(o, v)`. -/
def ValsAt (d : DataMem) (fb : BitVec 64) (l : List (Nat × BitVec 64)) : Prop :=
  ∀ p ∈ l, BytesAt d (fb + BitVec.ofNat 64 p.1) ((List.range 8).map (byteOf p.2))

/-- The point. -/
abbrev pts (m0 : MachineData) : List EW := ewsOf m0.dmem (reg m0 .rcx) (reg m0 .r8).toNat
/-- `|mle|` (`= n`). -/
abbrev nn (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
/-- `|point|`. -/
abbrev mm (m0 : MachineData) : Nat := (reg m0 .r8).toNat

/-- The arguments' words in the frame: `mle`, `n`, `|mle|`, `16 |point|`, `point`. -/
def argVals (m0 : MachineData) : List (Nat × BitVec 64) :=
  [(24, reg m0 .rsi), (32, reg m0 .rdi), (40, reg m0 .rdx), (48, BitVec.ofNat 64 (16 * mm m0)),
    (56, reg m0 .rcx)]

end

public section

/-! ## Words in the frame -/

/-- **A word read back.** -/
theorem val_load {env : Env} {r : Nat} {l : List (Nat × BitVec 64)}
    (h : ValsAt env.mem0 (env.base r) l) {o : Nat} {v : BitVec 64} (hp : (o, v) ∈ l) :
    env.load r o 8 = v := by
  rw [Env.load_of_bytesAt (by simp) (h _ hp), ofInt_ofBytes_byteOf]

/-- Words kept where memory is. -/
theorem vals_congr {d d' : DataMem} {fb : BitVec 64} {l : List (Nat × BitVec 64)}
    (h : ValsAt d fb l)
    (he : ∀ p ∈ l, ∀ j < 8, d'.get? (fb + BitVec.ofNat 64 (p.1 + j)) =
      d.get? (fb + BitVec.ofNat 64 (p.1 + j))) : ValsAt d' fb l := fun p hp i hi ↦ by
  simp only [List.length_map, List.length_range] at hi
  rw [addr_add, he p hp i hi, ← addr_add]
  exact h p hp i (by simpa using hi)

theorem vals_nil (d : DataMem) (fb : BitVec 64) : ValsAt d fb [] := fun _ h ↦ by cases h

theorem vals_cons {d : DataMem} {fb : BitVec 64} {o : Nat} {v : BitVec 64}
    {l : List (Nat × BitVec 64)} :
    ValsAt d fb ((o, v) :: l) ↔
      BytesAt d (fb + BitVec.ofNat 64 o) ((List.range 8).map (byteOf v)) ∧ ValsAt d fb l := by
  unfold ValsAt
  simp

/-- A word a block stored. -/
theorem val_of_write [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz)
    {v : Sym} (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) :
    ValsAt m.dmem b [(o, v.eval env)] := by
  rw [vals_cons]
  exact ⟨hm.bytesAt_write hb hle hw, vals_nil _ _⟩

/-! ## Addresses -/

theorem ofNat_add_inj {a : BitVec 64} {i j : Nat} (h : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 j)
    (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) : i = j := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  have := a.isLt
  omega

theorem mleStack_eq : mleStack = 1360 := rfl

theorem fb_toNat {m0 : MachineData} (hS : StackOk m0 mleStack) :
    (fbOf m0).toNat = (rspOf m0).toNat - 1216 ∧ 1360 ≤ (rspOf m0).toNat ∧
      (rspOf m0).toNat + 8 ≤ 2 ^ 64 :=
  ⟨stackBelow_toNat (by have := hS.1; rw [mleStack_eq] at this; omega),
    by have := hS.1; rw [mleStack_eq] at this; omega, hS.2.1⟩

theorem fb_add_toNat {m0 : MachineData} (hS : StackOk m0 mleStack) {o : Nat} (ho : o < 1224) :
    (fbOf m0 + BitVec.ofNat 64 o).toNat = (fbOf m0).toNat + o := by
  obtain ⟨h1, h2, h3⟩ := fb_toNat hS
  exact toNat_add_ofNat _ _ (by omega)

/-- A piece of the frame is in the stack. -/
theorem frame_inStack {m0 : MachineData} (hS : StackOk m0 mleStack) {j : Nat} (hj : j < 1216) :
    InRange (stackBelow m0 mleStack) mleStack (fbOf m0 + BitVec.ofNat 64 j) := by
  obtain ⟨h1, h2, h3⟩ := fb_toNat hS
  have hsb : (stackBelow m0 mleStack).toNat = (rspOf m0).toNat - 1360 :=
    stackBelow_toNat (by rw [mleStack_eq]; omega)
  rw [Sym.inRange_iff (by rw [hsb, mleStack_eq]; omega), hsb, fb_add_toNat hS (by omega), h1,
    mleStack_eq]
  omega

/-- The `n` bytes at `o` of the frame, `o + n ≤ 1224`: mapped while the entry's bytes are. -/
theorem frame_piece {m0 st : MachineData} (hS : StackOk m0 mleStack) (hk : Kept m0.dmem st.dmem)
    {o n : Nat} (h : o + n ≤ 1224) :
    Readable st (fbOf m0 + BitVec.ofNat 64 o) n := by
  obtain ⟨h1, h2, h3⟩ := fb_toNat hS
  have hS' := stackOk_mono hS (show 1216 ≤ mleStack by decide)
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [addr_add]; exact hk _ (hS'.2.2 _ (by omega))
  · unfold NoWrap
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := (fbOf m0 + BitVec.ofNat 64 o).isLt; omega
    · rw [fb_add_toNat hS (by omega)]; omega

/-- Two pieces of the frame, the first below the second. -/
theorem frame_apart {m0 : MachineData} (hS : StackOk m0 mleStack) {o n o' n' : Nat}
    (h : o + n ≤ o') (h' : o' + n' ≤ 1224) (hn : 0 < n') :
    Apart (fbOf m0 + BitVec.ofNat 64 o) n (fbOf m0 + BitVec.ofNat 64 o') n' := by
  unfold Apart
  rw [fb_add_toNat hS (by omega), fb_add_toNat hS (by omega)]
  omega

/-- A piece of a region apart from the stack is apart from a piece of the frame. -/
theorem piece_offStack {m0 : MachineData} (hS : StackOk m0 mleStack) {a : BitVec 64} {len : Nat}
    (h : OffStack m0 a len mleStack) (hnw : NoWrap a len) {j w o n : Nat} (hj : j + w ≤ len)
    (hw : 0 < w) (ho : o + n ≤ 1224) (hn : 0 < n) :
    Apart (a + BitVec.ofNat 64 j) w (fbOf m0 + BitVec.ofNat 64 o) n := by
  obtain ⟨h1, h2, h3⟩ := fb_toNat hS
  have hsb : (stackBelow m0 mleStack).toNat = (rspOf m0).toNat - 1360 :=
    stackBelow_toNat (by rw [mleStack_eq]; omega)
  unfold OffStack Apart at h
  unfold NoWrap at hnw
  unfold Apart
  rw [hsb, mleStack_eq] at h
  rw [fb_add_toNat hS (by omega), toNat_add_ofNat _ _ (by omega)]
  omega

/-- An address between offsets `lo` and `hi` of the frame. -/
theorem frame_addr {m0 : MachineData} (hS : StackOk m0 mleStack) {p : BitVec 64} {lo hi : Nat}
    (h1 : (fbOf m0).toNat + lo ≤ p.toNat) (h2 : p.toNat < (fbOf m0).toNat + hi) (hhi : hi ≤ 1224) :
    ∃ j, lo ≤ j ∧ j < hi ∧ p = fbOf m0 + BitVec.ofNat 64 j :=
  ⟨p.toNat - (fbOf m0).toNat, by omega, by omega, by
    apply BitVec.eq_of_toNat_eq; rw [fb_add_toNat hS (by omega)]; omega⟩

/-- Two regions, readable, apart: a well-formed environment. -/
theorem wf2 {st : MachineData} {a b : BitVec 64} {n n' : Nat} (ha : Readable st a n)
    (hb : Readable st b n') (hab : Apart a n b n') (vars : Nat → BitVec 64 := fun _ ↦ 0)
    (ret : BitVec 64 := 0) : (Env.ofMachine st [(a, n), (b, n')] vars ret).WF :=
  Env.wf_of ⟨⟨ha.1, ha.2⟩, ⟨hb.1, hb.2⟩, trivial⟩ (List.pairwise_pair.mpr hab)

/-- One region, readable: a well-formed environment. -/
theorem wf1 {st : MachineData} {a : BitVec 64} {n : Nat} (ha : Readable st a n)
    (vars : Nat → BitVec 64 := fun _ ↦ 0) (ret : BitVec 64 := 0) :
    (Env.ofMachine st [(a, n)] vars ret).WF :=
  Env.wf_of ⟨⟨ha.1, ha.2⟩, trivial⟩ (List.pairwise_singleton _ _)

/-- Three regions, readable, pairwise apart: a well-formed environment. -/
theorem wf3 {st : MachineData} {a b c : BitVec 64} {n n' n'' : Nat}
    (ha : Readable st a n) (hb : Readable st b n') (hc : Readable st c n'')
    (hab : Apart a n b n') (hac : Apart a n c n'') (hbc : Apart b n' c n'')
    (vars : Nat → BitVec 64 := fun _ ↦ 0) (ret : BitVec 64 := 0) :
    (Env.ofMachine st [(a, n), (b, n'), (c, n'')] vars ret).WF :=
  Env.wf_of ⟨⟨ha.1, ha.2⟩, ⟨hb.1, hb.2⟩, ⟨hc.1, hc.2⟩, trivial⟩
    (List.pairwise_cons.mpr ⟨by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact hab
      · exact hac, List.pairwise_pair.mpr hbc⟩)

/-- Four regions, readable, pairwise apart: a well-formed environment. -/
theorem wf4 {st : MachineData} {a b c e : BitVec 64} {n n' n'' n''' : Nat}
    (ha : Readable st a n) (hb : Readable st b n') (hc : Readable st c n'')
    (he : Readable st e n''')
    (hab : Apart a n b n') (hac : Apart a n c n'') (hae : Apart a n e n''')
    (hbc : Apart b n' c n'') (hbe : Apart b n' e n''') (hce : Apart c n'' e n''')
    (vars : Nat → BitVec 64 := fun _ ↦ 0) (ret : BitVec 64 := 0) :
    (Env.ofMachine st [(a, n), (b, n'), (c, n''), (e, n''')] vars ret).WF :=
  Env.wf_of ⟨⟨ha.1, ha.2⟩, ⟨hb.1, hb.2⟩, ⟨hc.1, hc.2⟩, ⟨he.1, he.2⟩, trivial⟩
    (List.pairwise_cons.mpr ⟨by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hab
      · exact hac
      · exact hae,
     List.pairwise_cons.mpr ⟨by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hbc
      · exact hbe, List.pairwise_pair.mpr hce⟩⟩)

/-! ## Bodies -/

theorem freeRegs_mleSlots : freeRegs mleSlots = [] := by decide

theorem mleSlots_ok : ∀ p ∈ mleSlots, 1168 ≤ p.1 ∧ p.1 + 8 ≤ 1216 := by decide

/-- **A block writing only between offsets `16` and `1168` of the frame**, keeping RSP, keeps a
body. -/
theorem body_of_local [Labels] {m0 st st' : MachineData} {env : Env} {S₁ : SState}
    (hb : Body m0 1216 mleStack mleSlots 0 0 st) (hS : StackOk m0 mleStack)
    (hm : Match env S₁ st') (hwf : env.WF) (hd : env.mem0 = st.dmem)
    (hrsp : reg st' .rsp = reg st .rsp)
    (hw : ∀ p, Written env S₁ p → ∃ j, 16 ≤ j ∧ j < 1168 ∧ p = fbOf m0 + BitVec.ofNat 64 j) :
    Body m0 1216 mleStack mleSlots 0 0 st' := by
  have hsame : ∀ p, ¬Written env S₁ p → st'.dmem.get? p = st.dmem.get? p := fun p hp ↦ by
    rw [hm.get?_mem0 hwf hp, hd]
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_, ?_⟩
  · show reg st' .rsp = _
    rw [hrsp]; exact hb.rsp
  · simp only [List.length_map, List.length_range] at hi
    have hs := mleSlots_ok p hp
    rw [addr_add, hsame _ fun hW ↦ ?_]
    · rw [← addr_add]; exact hb.frame p hp i (by simpa using hi)
    · obtain ⟨j, hj1, hj2, he⟩ := hw _ hW
      have := ofNat_add_inj he (by omega) (by omega)
      omega
  · have := free_mem hr hn
    rw [freeRegs_mleSlots] at this
    cases this
  · by_cases hW : Written env S₁ p
    · obtain ⟨j, -, hj2, rfl⟩ := hw _ hW
      exact absurd (Or.inr (frame_inStack hS (by omega))) hp
    · rw [hsame p hW]; exact hb.same p hp
  · intro p hp
    have := hm.kept hwf p
    rw [hd] at this
    exact this (hb.kept p hp)

/-! ## Pending entries -/

theorem pendOf_congr {d d' : DataMem} {fb : BitVec 64}
    (h : ∀ j, 80 ≤ j → j < 1168 → d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    pendOf d' fb = pendOf d fb := by
  funext k
  unfold pendOf
  by_cases hk : k < 64
  · rw [h (80 + k) (by omega) (by omega), NativeRustcVm.ewOf_congr (d := d) fun i hi ↦ by
      rw [NativeRustcVm.addr_add]; exact h _ (by omega) (by omega)]
  · simp [hk]

theorem flagsOk_congr {d d' : DataMem} {fb : BitVec 64} (hf : FlagsOk d fb)
    (h : ∀ j, 80 ≤ j → j < 144 → d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    FlagsOk d' fb := fun k hk ↦ by
  rw [h (80 + k) (by omega) (by omega)]; exact hf k hk

/-- Every flag `0`: nothing pending. -/
theorem pendOf_zero {d : DataMem} {fb : BitVec 64}
    (h : ∀ k < 64, d.get? (fb + BitVec.ofNat 64 (80 + k)) = some 0) :
    pendOf d fb = fun _ ↦ none := by
  funext k
  unfold pendOf
  by_cases hk : k < 64
  · rw [h k hk]; simp
  · simp [hk]

/-- **A flag cleared**: level `k`'s entry gone. -/
theorem pendOf_clear {d d' : DataMem} {fb : BitVec 64} {k : Nat} (hk : k < 64)
    (hf : d'.get? (fb + BitVec.ofNat 64 (80 + k)) = some 0)
    (h : ∀ j, 80 ≤ j → j < 1168 → j ≠ 80 + k →
      d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    pendOf d' fb = setP (pendOf d fb) k none := by
  funext j
  unfold setP
  by_cases hj : j = k
  · subst hj
    rw [ite_eq_left rfl]
    unfold pendOf
    rw [hf]
    simp
  · rw [ite_eq_right hj]
    unfold pendOf
    by_cases hj' : j < 64
    · rw [h (80 + j) (by omega) (by omega) (by omega), NativeRustcVm.ewOf_congr (d := d) fun i hi ↦ by
        rw [NativeRustcVm.addr_add]; exact h _ (by omega) (by omega) (by omega)]
    · simp [hj']

theorem flagsOk_clear {d d' : DataMem} {fb : BitVec 64} {k : Nat} (hfl : FlagsOk d fb)
    (hf : d'.get? (fb + BitVec.ofNat 64 (80 + k)) = some 0)
    (h : ∀ j, 80 ≤ j → j < 144 → j ≠ 80 + k →
      d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    FlagsOk d' fb := fun j hj ↦ by
  by_cases hjk : j = k
  · subst hjk; exact Or.inl hf
  · rw [h (80 + j) (by omega) (by omega) (by omega)]; exact hfl j hj

/-- **An entry pushed** at level `k`. -/
theorem pendOf_set {d d' : DataMem} {fb : BitVec 64} {k : Nat} {v : EW} (hk : k < 64)
    (hf : d'.get? (fb + BitVec.ofNat 64 (80 + k)) = some 1)
    (hv : ewOf d' (fb + BitVec.ofNat 64 (144 + 16 * k)) = v)
    (h : ∀ j, 80 ≤ j → j < 1168 → j ≠ 80 + k → (j < 144 + 16 * k ∨ 160 + 16 * k ≤ j) →
      d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    pendOf d' fb = setP (pendOf d fb) k (some v) := by
  funext j
  unfold setP
  by_cases hj : j = k
  · subst hj
    rw [ite_eq_left rfl]
    unfold pendOf
    rw [hf, hv]
    simp [hk]
  · rw [ite_eq_right hj]
    unfold pendOf
    by_cases hj' : j < 64
    · rw [h (80 + j) (by omega) (by omega) (by omega) (by omega),
        NativeRustcVm.ewOf_congr (d := d) fun i hi ↦ by
          rw [NativeRustcVm.addr_add]
          exact h _ (by omega) (by omega) (by omega) (by
            rcases Nat.lt_or_gt_of_ne hj with hl | hl <;> omega)]
    · simp [hj']

theorem flagsOk_set {d d' : DataMem} {fb : BitVec 64} {k : Nat} (hfl : FlagsOk d fb)
    (hf : d'.get? (fb + BitVec.ofNat 64 (80 + k)) = some 1)
    (h : ∀ j, 80 ≤ j → j < 144 → j ≠ 80 + k →
      d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    FlagsOk d' fb := fun j hj ↦ by
  by_cases hjk : j = k
  · subst hjk; exact Or.inr hf
  · rw [h (80 + j) (by omega) (by omega) (by omega)]; exact hfl j hj

/-- A flag's byte, `0` (nothing pending) or `1` (the entry pending). -/
theorem flag_cases {d : DataMem} {fb : BitVec 64} {k : Nat} (hk : k < 64) (hfl : FlagsOk d fb) :
    (d.get? (fb + BitVec.ofNat 64 (80 + k)) = some 0 ∧ pendOf d fb k = none) ∨
      (d.get? (fb + BitVec.ofNat 64 (80 + k)) = some 1 ∧
        pendOf d fb k = some (ewOf d (fb + BitVec.ofNat 64 (144 + 16 * k)))) := by
  rcases hfl k hk with h | h
  · refine .inl ⟨h, ?_⟩
    unfold pendOf
    rw [h, ite_eq_right (fun hc ↦ absurd hc.2 (by decide))]
  · refine .inr ⟨h, ?_⟩
    unfold pendOf
    rw [h, ite_eq_left ⟨hk, rfl⟩]

/-- A byte at an address, as the executor loads it. -/
theorem load_byte {env : Env} {r : Nat} {b : UInt8}
    (h : env.mem0.get? (env.base r) = some b) :
    env.load r 0 1 = BitVec.ofInt 64 (Int.ofBytes [b]) :=
  Env.load_of_bytesAt rfl fun i hi ↦ by
    obtain rfl : i = 0 := by simp at hi; omega
    rw [add_ofNat_zero, add_ofNat_zero]
    exact h

/-! ## Slices -/

/-- A word of an argument slice, read in a body. -/
theorem word_of_apart {m0 st : MachineData} {S : Nat} {a : BitVec 64} {n i : Nat}
    (hc : Changes m0 st S 0 0) (hS : StackOk m0 S) (hna : NoWrap a (8 * n))
    (hst : OffStack m0 a (8 * n) S) (hi : i < n) :
    wordOf st.dmem (a + BitVec.ofNat 64 (8 * i)) =
      (NativeRustcVm.wordsOf m0.dmem a n)[i]'(by simp; exact hi) := by
  rw [NativeRustcVm.getElem_wordsOf]
  exact NativeRustcVm.wordOf_congr fun j hj ↦ by
    rw [NativeRustcVm.addr_add]
    exact same_of_apart hc hS hna hst (apart_zero _ _) noWrap_zero _ (by omega)

/-- The `8` bytes of word `i < n` of a readable slice are readable in a state that kept them. -/
theorem word_mapped {m0 st : MachineData} {a : BitVec 64} {n i : Nat} (h : Readable m0 a (8 * n))
    (hk : Kept m0.dmem st.dmem) (hi : i < n) : Readable st (a + BitVec.ofNat 64 (8 * i)) 8 := by
  obtain ⟨hm, hn⟩ := h
  unfold NoWrap at *
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [addr_add]; exact hk _ (hm _ (by omega))
  · show (a + BitVec.ofNat 64 (8 * i)).toNat + 8 ≤ 2 ^ 64
    rw [toNat_add_ofNat _ _ (by omega)]; omega

end

/-! ## The loops' invariants -/

@[expose] public section

/-- The registers an instance keeps its loop state in: `full[k]`'s address (`rf`), `16 k`
(`ri`), the carried value (`vlo`, `vhi`), `point[k]` across the calls (`plo`, `phi`). -/
structure Regs where
  rf : Reg64
  ri : Reg64
  vlo : Reg64
  vhi : Reg64
  plo : Reg64
  phi : Reg64

/-- The registers are callee-saved. -/
def Regs.Saved (R : Regs) : Prop :=
  calleeSaved R.rf = true ∧ calleeSaved R.ri = true ∧ calleeSaved R.vlo = true ∧
    calleeSaved R.vhi = true ∧ calleeSaved R.plo = true ∧ calleeSaved R.phi = true

/-- **The frame in the loops**: the body, the arguments' words, the flags `0` or `1`. -/
structure Fr (m0 s : MachineData) : Prop where
  body : Body m0 1216 mleStack mleSlots 0 0 s
  args : ValsAt s.dmem (fbOf m0) (argVals m0)
  flags : FlagsOk s.dmem (fbOf m0)

/-- **The outer loop's head**, `i` of the entries `es` streamed. -/
structure Outer (es : List EW) (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  fr : Fr m0 s
  hi : i < nn m0
  pos : 0 < mm m0
  lt : mm m0 < 64
  wi : ValsAt s.dmem (fbOf m0) [(16, BitVec.ofNat 64 i)]
  val : stream (pts m0) (es.drop i) (pendOf s.dmem (fbOf m0)) = stream (pts m0) es fun _ ↦ none

/-- **The inner loop's head**: entry `i` carried to level `kk`. -/
structure Inner (es : List EW) (R : Regs) (m0 : MachineData) (i kk : Nat) (s : MachineData) :
    Prop where
  fr : Fr m0 s
  hi : i < nn m0
  hk : kk < mm m0
  lt : mm m0 < 64
  wi : ValsAt s.dmem (fbOf m0) [(16, BitVec.ofNat 64 (i + 1))]
  rf : reg s R.rf = fbOf m0 + BitVec.ofNat 64 (80 + kk)
  ri : reg s R.ri = BitVec.ofNat 64 (16 * kk)
  val : cont (pts m0) (es.drop (i + 1)) (pendOf s.dmem (fbOf m0)) kk
    (ewArg (reg s R.vlo) (reg s R.vhi)) = stream (pts m0) es fun _ ↦ none

/-- **At the epilogue**: the body, the result in `vlo`, `vhi`. -/
structure AtEnd (es : List EW) (R : Regs) (m0 : MachineData) (s : MachineData) : Prop where
  body : Body m0 1216 mleStack mleSlots 0 0 s
  val : ewArg (reg s R.vlo) (reg s R.vhi) = stream (pts m0) es fun _ ↦ none

end

public section

/-! ## Frame bytes kept -/

theorem args_congr {m0 st st' : MachineData} (h : ValsAt st.dmem (fbOf m0) (argVals m0))
    (he : ∀ j, 24 ≤ j → j < 64 → st'.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
      st.dmem.get? (fbOf m0 + BitVec.ofNat 64 j)) : ValsAt st'.dmem (fbOf m0) (argVals m0) :=
  vals_congr h fun p hp j hj ↦ he _ (by
    simp only [argVals, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by
    simp only [argVals, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega)

theorem wi_congr {m0 st st' : MachineData} {v : BitVec 64}
    (h : ValsAt st.dmem (fbOf m0) [(16, v)])
    (he : ∀ j, 16 ≤ j → j < 24 → st'.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) =
      st.dmem.get? (fbOf m0 + BitVec.ofNat 64 j)) : ValsAt st'.dmem (fbOf m0) [(16, v)] :=
  vals_congr h fun p hp j hj ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact he _ (by simp) (by simp; omega)

/-- **The bytes a block wrote**, by the writes' regions and offsets: an address a write covers
is between the write's bounds. -/
theorem written_bounds {env : Env} {S : SState} {p : BitVec 64} (h : Written env S p) :
    ∃ w ∈ S.mem, ∃ (b : BitVec 64) (sz : Nat), env.regions[w.r]? = some (b, sz) ∧
      b.toNat + w.off ≤ p.toNat ∧ p.toNat < b.toNat + w.off + w.n := h

/-- Where a block writes nothing, `Written` is empty. -/
theorem not_written_nil {env : Env} {S : SState} (h : S.mem = []) (p : BitVec 64) :
    ¬Written env S p := fun ⟨w, hw, _⟩ ↦ by rw [h] at hw; cases hw

/-- **A block that writes nothing**, keeps RSP and the registers `rs`, keeps a body, memory and
the registers. -/
theorem body_of_keeps [Labels] {m0 st st' : MachineData} {env : Env} {S₀ S₁ : SState}
    {rs : List Reg64} (hb : Body m0 1216 mleStack mleSlots 0 0 st) (hS : StackOk m0 mleStack)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : env.mem0 = st.dmem)
    (hk : keepsAll S₀ S₁ rs = true) :
    Body m0 1216 mleStack mleSlots 0 0 st' ∧ st'.dmem = st.dmem ∧ ∀ r ∈ rs, reg st' r = reg st r := by
  unfold keepsAll at hk
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk
  obtain ⟨hr, hmem⟩ := hk
  have he := regs_eq_of hm₀ hm hr
  refine ⟨body_of_local hb hS hm hwf hd (he .rsp (by simp))
    (fun p hp ↦ absurd hp (not_written_nil hmem p)),
    (hm.dmem_eq hwf hmem).trans hd, fun r hr' ↦ he r (List.mem_cons_of_mem _ hr')⟩

theorem ofInt_neg136 : (BitVec.ofInt 64 (-136)).toNat = 2 ^ 64 - 136 := by
  rw [BitVec.toNat_ofInt]; rfl

theorem ofInt_8 : BitVec.ofInt 64 8 = BitVec.ofNat 64 8 := by decide

theorem ofInt_0 : BitVec.ofInt 64 0 = 0#64 := by decide

/-- A pending entry's address: RSP (`fb + 8`) plus `x` plus `136`. -/
theorem pend_alias (fb : BitVec 64) (x : Nat) :
    fb + BitVec.ofInt 64 8 + BitVec.ofNat 64 x =
      fb + BitVec.ofNat 64 (144 + x) + BitVec.ofInt 64 (-136) := by
  rw [ofInt_8]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, ofInt_neg136,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := fb.isLt
  omega

/-- A region pointer at offset `0` is the region's base. -/
theorem eval_ptr0 [Labels] {env : Env} {r : Nat} {b : BitVec 64} {n : Nat}
    (h : env.regions[r]? = some (b, n)) : (Sym.ptr r 0).eval env = b := by
  show env.base r + BitVec.ofInt 64 0 = b
  rw [Env.base_eq h, ofInt_0, BitVec.add_zero]

/-- `16 + 16 k`. -/
theorem ofNat_16_add (k : Nat) :
    BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * k) = BitVec.ofNat 64 (16 * (k + 1)) := by
  rw [← BitVec.ofNat_add, show 16 + 16 * k = 16 * (k + 1) by omega]

end

end NativeRustcVmX64.Arrays.MleFrame
