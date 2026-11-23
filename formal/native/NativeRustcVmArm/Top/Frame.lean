module

public import NativeRustcArm.Sym
public import NativeRustcVm.MemLemmas
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# Frames of the top functions

What the proofs of `seed`, `verify`, `verify_execution` and `leanvm_verify` share: a function's
body after its prologue (`Body m0 F slots R st`: SP `F` bytes below the entry's, the prologue's
slots holding the entry's registers, the other callee-saved registers the entry's, memory as at
the entry but in the addresses `R`, every mapped byte kept); kept across a call whose writes stay
in `R` and off the slots (`Body.call`), across a block (`Body.block`, its writes in the frame off
the slots); the epilogue restores the entry's registers (`Body.ret`). Addresses as numbers
(`written_sub`, `bv_toNat`), bytes kept across a change (`bytesAt_keep`).
-/

namespace NativeRustcVmArm.Top

open NativeRustcArm NativeRustcArm.Sym
open NativeRustcVm (WordAt WordsAt wordBytes wordOf wordOf_of_wordAt)

public section

/-! ## Runs -/

/-- The state `exec ds S` ends in (`S` where it fails). -/
@[expose] def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-! ## Addresses -/

theorem toNat_addr {a : BitVec 64} {i : Nat} (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i :=
  NativeRustcVm.toNat_add_ofNat h

theorem toNat_subAddr {a : BitVec 64} {i : Nat} (h : i ≤ a.toNat) :
    (a - BitVec.ofNat 64 i).toNat = a.toNat - i :=
  NativeRustcVm.toNat_sub_ofNat h

/-- `InRange` of bytes that do not wrap, as numbers. -/
theorem inRange_nat {x p : BitVec 64} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64) :
    InRange x n p ↔ x.toNat ≤ p.toNat ∧ p.toNat < x.toNat + n :=
  NativeRustcVm.inRange_iff hx

/-- Two addresses equal as numbers. -/
theorem addr_eq {a b : BitVec 64} {i j : Nat} (ha : a.toNat + i < 2 ^ 64) (hb : b.toNat + j < 2 ^ 64)
    (h : a.toNat + i = b.toNat + j) : a + BitVec.ofNat 64 i = b + BitVec.ofNat 64 j :=
  BitVec.eq_of_toNat_eq (by rw [toNat_addr ha, toNat_addr hb, h])

/-- Bytes mapped inside mapped bytes. -/
theorem Mapped.within {d : DataMem} {a a' : BitVec 64} {n n' : Nat} (h : Mapped d a n)
    (hnw : a.toNat + n ≤ 2 ^ 64) (h1 : a.toNat ≤ a'.toNat) (h2 : a'.toNat + n' ≤ a.toNat + n) :
    Mapped d a' n' := fun i hi ↦ by
  rw [addr_eq (b := a) (j := a'.toNat - a.toNat + i) (by omega) (by omega) (by omega)]
  exact h _ (by omega)

/-- The addresses a block's writes into region `r` (between offsets `lo` and `hi`) cover. -/
theorem written_sub [Labels] {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {sz lo hi : Nat}
    (hb : env.regions[r]? = some (b, sz))
    (hall : ∀ w ∈ S.mem, w.r = r ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) {a : BitVec 64}
    (h : Written env S a) : b.toNat + lo ≤ a.toNat ∧ a.toNat < b.toNat + hi := by
  obtain ⟨w, hw, b', sz', hb', h1, h2⟩ := h
  obtain ⟨hr, hlo, hhi⟩ := hall w hw
  rw [hr, hb] at hb'
  cases hb'
  omega

/-- **Bytes kept** across a change whose addresses are outside them. -/
theorem bytesAt_keep {d d' : DataMem} {R : BitVec 64 → Prop} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d a bs) (hs : SameOutside d d' R) (hnw : a.toNat + bs.length ≤ 2 ^ 64)
    (hR : ∀ p, R p → p.toNat < a.toNat ∨ a.toNat + bs.length ≤ p.toNat) : BytesAt d' a bs :=
  fun i hi ↦ by
    rw [hs _ fun hr ↦ by
      have := hR _ hr
      rw [toNat_addr (by omega)] at this
      omega]
    exact h i hi

/-- **Words kept** across a change whose addresses are outside them. -/
theorem wordsAt_keep {d d' : DataMem} {R : BitVec 64 → Prop} {a : BitVec 64} {ws : List UInt64}
    (h : WordsAt d a ws) (hs : SameOutside d d' R) (hnw : a.toNat + 8 * ws.length ≤ 2 ^ 64)
    (hR : ∀ p, R p → p.toNat < a.toNat ∨ a.toNat + 8 * ws.length ≤ p.toNat) : WordsAt d' a ws :=
  bytesAt_keep (bs := ws.flatMap wordBytes) h hs
    (by rw [NativeRustcVm.length_wordsBytes]; exact hnw)
    (by rw [NativeRustcVm.length_wordsBytes]; exact hR)

/-- Mapped bytes stay mapped. -/
theorem Mapped.kept {d d' : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n)
    (hk : Kept d d') : Mapped d' a n := fun i hi ↦ hk _ (h i hi)

/-- Five regions pairwise apart. -/
theorem disjoint_five {r₁ r₂ r₃ r₄ r₅ : NativeRustcVm.Region}
    (h12 : NativeRustcVm.Apart r₁.addr r₁.size r₂.addr r₂.size)
    (h13 : NativeRustcVm.Apart r₁.addr r₁.size r₃.addr r₃.size)
    (h14 : NativeRustcVm.Apart r₁.addr r₁.size r₄.addr r₄.size)
    (h15 : NativeRustcVm.Apart r₁.addr r₁.size r₅.addr r₅.size)
    (h23 : NativeRustcVm.Apart r₂.addr r₂.size r₃.addr r₃.size)
    (h24 : NativeRustcVm.Apart r₂.addr r₂.size r₄.addr r₄.size)
    (h25 : NativeRustcVm.Apart r₂.addr r₂.size r₅.addr r₅.size)
    (h34 : NativeRustcVm.Apart r₃.addr r₃.size r₄.addr r₄.size)
    (h35 : NativeRustcVm.Apart r₃.addr r₃.size r₅.addr r₅.size)
    (h45 : NativeRustcVm.Apart r₄.addr r₄.size r₅.addr r₅.size) :
    NativeRustcVm.Disjoint [r₁, r₂, r₃, r₄, r₅] := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))) <;> intro r hr <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  · rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rcases hr with rfl | rfl | rfl <;> assumption
  · rcases hr with rfl | rfl <;> assumption
  · subst hr; assumption

/-- Four regions pairwise apart. -/
theorem disjoint_four {r₁ r₂ r₃ r₄ : NativeRustcVm.Region}
    (h12 : NativeRustcVm.Apart r₁.addr r₁.size r₂.addr r₂.size)
    (h13 : NativeRustcVm.Apart r₁.addr r₁.size r₃.addr r₃.size)
    (h14 : NativeRustcVm.Apart r₁.addr r₁.size r₄.addr r₄.size)
    (h23 : NativeRustcVm.Apart r₂.addr r₂.size r₃.addr r₃.size)
    (h24 : NativeRustcVm.Apart r₂.addr r₂.size r₄.addr r₄.size)
    (h34 : NativeRustcVm.Apart r₃.addr r₃.size r₄.addr r₄.size) :
    NativeRustcVm.Disjoint [r₁, r₂, r₃, r₄] := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))) <;> intro r hr <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  · rcases hr with rfl | rfl | rfl <;> assumption
  · rcases hr with rfl | rfl <;> assumption
  · subst hr; assumption

/-! ## The frame -/

/-- The prologue's slots: register `r`'s entry value at `fb + o` for each `(o, r)`. -/
@[expose] def SlotsAt (d : DataMem) (fb : BitVec 64) (m0 : MachineData)
    (slots : List (Nat × XReg)) : Prop :=
  ∀ p ∈ slots, BytesAt d (fb + BitVec.ofNat 64 p.1)
    ((List.range 8).map (byteOf (m0.regs.getXReg p.2).toBitVec))

theorem ofInt_ofBytes_byteOf (x : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map (byteOf x))) = x := by
  have := ofBytes_byteOf x 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  rw [this, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- **A slot read back** is the entry's register. -/
theorem slot_load [Labels] {env : Env} {m0 : MachineData} {slots : List (Nat × XReg)} {r : Nat}
    (h : SlotsAt env.mem0 (env.base r) m0 slots) {o : Nat} {x : XReg} (hp : (o, x) ∈ slots) :
    env.load r o 8 = (m0.regs.getXReg x).toBitVec := by
  rw [Env.load_of_bytesAt (by simp) (h _ hp), ofInt_ofBytes_byteOf]

/-- **A function's body**: `F` bytes of frame below the entry's SP, the prologue's slots there,
the other callee-saved registers the entry's, memory as at the entry but in `R`, every mapped
byte kept. -/
structure Body (m0 : MachineData) (F : Nat) (slots : List (Nat × XReg)) (R : BitVec 64 → Prop)
    (st : MachineData) : Prop where
  sp : st.regs.SP.toBitVec = m0.regs.SP.toBitVec - BitVec.ofNat 64 F
  frame : SlotsAt st.dmem (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) m0 slots
  regs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → st.regs.getXReg r = m0.regs.getXReg r
  same : SameOutside m0.dmem st.dmem R
  kept : Kept m0.dmem st.dmem

/-- The `N` bytes below the entry's SP, as numbers. -/
@[expose] def InStack (m0 : MachineData) (N : Nat) (q : BitVec 64) : Prop :=
  m0.regs.SP.toBitVec.toNat - N ≤ q.toNat ∧ q.toNat < m0.regs.SP.toBitVec.toNat

/-- A body changing fewer addresses. -/
theorem Body.mono {m0 st : MachineData} {F : Nat} {slots : List (Nat × XReg)}
    {R R' : BitVec 64 → Prop} (hb : Body m0 F slots R st) (h : ∀ p, R p → R' p) :
    Body m0 F slots R' st :=
  ⟨hb.sp, hb.frame, hb.regs, fun p hp ↦ hb.same p fun hr ↦ hp (h p hr), hb.kept⟩

/-- The bytes `BytesAt` gives. -/
theorem bytesOf_of_bytesAt {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    NativeRustcArm.bytesOf d a bs.length = bs := by
  apply List.ext_getElem (by simp [NativeRustcArm.bytesOf])
  intro i h1 h2
  simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range]
  rw [h i h2]
  rfl

/-- The `N` bytes below `sp`, as numbers. -/
theorem inRange_below {sp p : BitVec 64} {N : Nat} (h : N ≤ sp.toNat) :
    InRange (sp - BitVec.ofNat 64 N) N p ↔ sp.toNat - N ≤ p.toNat ∧ p.toNat < sp.toNat := by
  rw [inRange_nat (by rw [toNat_subAddr h]; have := sp.isLt; omega), toNat_subAddr h]
  omega

/-- A word's bytes are `byteOf` of its value. -/
theorem wordBytes_byteOf (w : UInt64) : wordBytes w = (List.range 8).map (byteOf w.toBitVec) := by
  rw [NativeRustcVm.wordBytes_eq]
  rfl

/-- An environment's eight bytes holding a word are its value. -/
theorem load_wordAt [Labels] {env : Env} {r off : Nat} {w : UInt64}
    (h : WordAt env.mem0 (env.base r + BitVec.ofNat 64 off) w) : env.load r off 8 = w.toBitVec := by
  unfold WordAt at h
  rw [wordBytes_byteOf] at h
  rw [Env.load_of_bytesAt (by simp) h, ofInt_ofBytes_byteOf]

/-- Zero bytes are zero words. -/
theorem wordsAt_zeros {d : DataMem} {a : BitVec 64} (k : Nat)
    (h : BytesAt d a (List.replicate (8 * k) 0)) : WordsAt d a (List.replicate k 0) := by
  have e : ∀ k, (List.replicate k (0 : UInt64)).flatMap wordBytes = List.replicate (8 * k) 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih, show 8 * (k + 1) = 8 + 8 * k by omega,
        ← List.replicate_append_replicate]
      rfl
  unfold WordsAt
  rw [e]
  exact h

/-- Mapped bytes hold the word `wordOf` reads. -/
theorem wordAt_wordOf {d : DataMem} {a : BitVec 64} (h : Mapped d a 8) : WordAt d a (wordOf d a) := by
  have hl : (NativeRustcVm.bytesFrom d a 8).length = 8 := by simp [NativeRustcVm.bytesFrom]
  unfold WordAt wordOf
  rw [NativeRustcVm.wordBytes_ofNat_leNat hl]
  intro i hi
  simp only [NativeRustcVm.bytesFrom, List.getElem_map, List.getElem_range]
  have := h i (by rw [hl] at hi; exact hi)
  revert this
  cases d.get? (a + BitVec.ofNat 64 i) <;> simp

/-- Mapped bytes hold the words `wordsOf` reads. -/
theorem wordsAt_wordsOf {d : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a (8 * n)) :
    WordsAt d a (NativeRustcVm.wordsOf d a n) := by
  refine NativeRustcVm.wordsAt_iff.mpr fun i hi ↦ ?_
  simp only [NativeRustcVm.wordsOf, List.length_map, List.length_range] at hi
  simp only [NativeRustcVm.wordsOf, List.getElem_map, List.getElem_range]
  exact wordAt_wordOf (NativeRustcVm.Mapped.sub h (by omega))

/-- The slots' bytes: offsets `lo` to `F` of the frame. -/
@[expose] def SlotsIn (slots : List (Nat × XReg)) (lo F : Nat) : Prop :=
  ∀ p ∈ slots, lo ≤ p.1 ∧ p.1 + 8 ≤ F

/-- **A step** keeps a body: SP and the callee-saved registers but the slots' kept, every mapped
byte kept, its writes `W` in `R` and below the slots or above the frame. -/
theorem Body.step {m0 st st' : MachineData} {F lo : Nat} {slots : List (Nat × XReg)}
    {R W : BitVec 64 → Prop} (hb : Body m0 F slots R st) (hsl : SlotsIn slots lo F)
    (hF : F ≤ m0.regs.SP.toBitVec.toNat) (hsame : SameOutside st.dmem st'.dmem W)
    (hsp : st'.regs.SP = st.regs.SP)
    (hregs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) →
      st'.regs.getXReg r = st.regs.getXReg r)
    (hkept : Kept st.dmem st'.dmem)
    (hW : ∀ p, W p → R p ∧
      (p.toNat < m0.regs.SP.toBitVec.toNat - F + lo ∨ m0.regs.SP.toBitVec.toNat ≤ p.toNat)) :
    Body m0 F slots R st' := by
  have hfb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 F).toNat = m0.regs.SP.toBitVec.toNat - F :=
    toNat_subAddr hF
  refine ⟨hsp ▸ hb.sp, fun p hp ↦ ?_, fun r hr hn ↦ (hregs r hr hn).trans (hb.regs r hr hn),
    fun p hp ↦ ?_, fun p hp ↦ hkept p (hb.kept p hp)⟩
  · have := hsl p hp
    have hlt := m0.regs.SP.toBitVec.isLt
    refine bytesAt_keep (hb.frame p hp) hsame ?_ fun q hq ↦ ?_
    · simp only [List.length_map, List.length_range]
      rw [toNat_addr (by rw [hfb]; omega), hfb]
      omega
    · simp only [List.length_map, List.length_range]
      rw [toNat_addr (by rw [hfb]; omega), hfb]
      have := (hW q hq).2
      omega
  · rw [hsame p fun h ↦ hp (hW p h).1]
    exact hb.same p hp

/-- **A call** keeps a body: its writes `W` in `R` and below the slots or above the frame. -/
theorem Body.call {m0 st st' : MachineData} {F lo : Nat} {slots : List (Nat × XReg)}
    {R W : BitVec 64 → Prop} (hb : Body m0 F slots R st) (hsl : SlotsIn slots lo F)
    (hF : F ≤ m0.regs.SP.toBitVec.toNat) (hsame : SameOutside st.dmem st'.dmem W)
    (hsaved : Saved st st')
    (hW : ∀ p, W p → R p ∧
      (p.toNat < m0.regs.SP.toBitVec.toNat - F + lo ∨ m0.regs.SP.toBitVec.toNat ≤ p.toNat)) :
    Body m0 F slots R st' :=
  hb.step hsl hF hsame hsaved.2.1 (fun r hr _ ↦ hsaved.1 r hr) hsaved.2.2 hW

/-- The callee-saved registers. -/
@[expose] def calleeRegs : List XReg :=
  [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

theorem mem_calleeRegs {r : XReg} (h : calleeSaved r = true) : r ∈ calleeRegs := by
  cases r <;> simp_all [calleeSaved, calleeRegs]

/-- `S` keeps `S₀`'s SP and every register of `rs`. -/
@[expose] def keepsRegs (S₀ S : SState) (rs : List XReg) : Bool :=
  rs.all (fun r ↦ (S₀.reg r).isSome && S.reg r == S₀.reg r) && S.sp == S₀.sp

/-- **A block** keeps a body: it keeps SP and the callee-saved registers but the slots' (those of
`rs`), its writes in `R` and off the slots. -/
theorem Body.block' [Labels] {m0 st st' : MachineData} {F lo : Nat} {slots : List (Nat × XReg)}
    {R : BitVec 64 → Prop} {env : Env} {S₀ S₁ : SState} {rs : List XReg}
    (hb : Body m0 F slots R st)
    (hsl : SlotsIn slots lo F) (hF : F ≤ m0.regs.SP.toBitVec.toNat)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsRegs S₀ S₁ rs = true)
    (hrs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → r ∈ rs)
    (hW : ∀ p, Written env S₁ p → R p ∧
      (p.toNat < m0.regs.SP.toBitVec.toNat - F + lo ∨ m0.regs.SP.toBitVec.toNat ≤ p.toNat)) :
    Body m0 F slots R st' := by
  simp only [keepsRegs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk
  obtain ⟨hr, hsp⟩ := hk
  have hsame : SameOutside st.dmem st'.dmem (Written env S₁) := hd ▸ hm.sameOutside hwf
  refine hb.step hsl hF hsame (Match.sp_eq hm₀ hm hsp) (fun r hr' hn ↦ ?_) (hd ▸ hm.kept hwf) hW
  obtain ⟨hs, he⟩ := hr r (hrs r hr' hn)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact Match.reg_eq hm₀ hm hv (he.trans hv)

/-- **A block** keeps a body: it keeps the callee-saved registers and SP, its writes in `R` and
off the slots. -/
theorem Body.block [Labels] {m0 st st' : MachineData} {F lo : Nat} {slots : List (Nat × XReg)}
    {R : BitVec 64 → Prop} {env : Env} {S₀ S₁ : SState} (hb : Body m0 F slots R st)
    (hsl : SlotsIn slots lo F) (hF : F ≤ m0.regs.SP.toBitVec.toNat)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsRegs S₀ S₁ calleeRegs = true)
    (hW : ∀ p, Written env S₁ p → R p ∧
      (p.toNat < m0.regs.SP.toBitVec.toNat - F + lo ∨ m0.regs.SP.toBitVec.toNat ≤ p.toNat)) :
    Body m0 F slots R st' :=
  hb.block' hsl hF hm₀ hm hwf hd hk (fun _ hr _ ↦ mem_calleeRegs hr) hW

/-- The callee-saved registers and X30. -/
@[expose] def savedRegs : List XReg :=
  [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29, .X30]

theorem mem_savedRegs {r : XReg} (h : calleeSaved r = true) : r ∈ savedRegs := by
  cases r <;> simp_all [calleeSaved, savedRegs]

/-- The epilogue's registers: each slot's register its load from the frame (region 0), the other
callee-saved registers and X30 kept, SP the frame's top. -/
@[expose] def restores (slots : List (Nat × XReg)) (F : Nat) (S : SState) : Bool :=
  savedRegs.all (fun r ↦ S.reg r == some (match slots.find? (·.2 == r) with
    | some p => .load 0 p.1 8
    | none => .reg r)) && S.sp == .ptr 0 (F : Int)

theorem find?_mem {slots : List (Nat × XReg)} {r : XReg} {p : Nat × XReg}
    (h : slots.find? (·.2 == r) = some p) : p ∈ slots ∧ p.2 = r := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, XReg.eq_of_beq this⟩

theorem find?_none {slots : List (Nat × XReg)} {r : XReg}
    (h : slots.find? (·.2 == r) = none) : r ∉ slots.map (·.2) := by
  intro hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  have := List.find?_eq_none.mp h p hp
  exact absurd this (by cases p.2 <;> decide)

/-- **The epilogue**: run from a body with the frame as region 0, it restores the entry's
callee-saved registers, X30 and SP, and writes nothing. -/
theorem Body.ret [Labels] {m0 st st' : MachineData} {F : Nat} {slots : List (Nat × XReg)}
    {R : BitVec 64 → Prop} {S₁ : SState} (hb : Body m0 F slots R st)
    (hm : Match (Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]) S₁ st')
    (hwf : (Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]).WF)
    (hx30 : (XReg.X30) ∈ slots.map (·.2))
    (hr : restores slots F S₁ = true) (hmem : S₁.mem = []) :
    Saved m0 st' ∧ retOf st' = retOf m0 ∧ st'.dmem = st.dmem := by
  simp only [restores, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hr
  obtain ⟨hr, hsp⟩ := hr
  have hbase : (Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]).base 0 =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 F := rfl
  have hreg : ∀ r ∈ savedRegs, st'.regs.getXReg r = m0.regs.getXReg r := by
    intro r hrs
    have h := hm.regs r _ (hr r hrs)
    cases hf : slots.find? (·.2 == r) with
    | some p =>
      obtain ⟨hp, rfl⟩ := find?_mem hf
      rw [hf] at h
      apply UInt64.toBitVec_inj.mp
      rw [h]
      exact slot_load (r := 0) (by rw [hbase]; exact hb.frame) hp
    | none =>
      rw [hf] at h
      apply UInt64.toBitVec_inj.mp
      rw [h]
      show (st.regs.getXReg r).toBitVec = _
      by_cases hc : calleeSaved r = true
      · rw [hb.regs r hc (find?_none hf)]
      · have : r = .X30 := by
          cases r <;> simp_all [calleeSaved, savedRegs]
        subst this
        exact absurd hx30 (find?_none hf)
  have hdm : st'.dmem = st.dmem := hm.dmem_eq hwf hmem
  refine ⟨⟨fun r hc ↦ hreg r (mem_savedRegs hc), ?_, ?_⟩, ?_, hdm⟩
  · apply UInt64.toBitVec_inj.mp
    rw [hm.sp, hsp]
    simp only [Sym.eval, hbase]
    rw [show BitVec.ofInt 64 (F : Int) = BitVec.ofNat 64 F from rfl, BitVec.sub_add_cancel]
  · rw [hdm]; exact hb.kept
  · unfold retOf
    rw [show st'.regs.X30 = m0.regs.X30 from hreg .X30 (by simp [savedRegs])]

end

end NativeRustcVmArm.Top
