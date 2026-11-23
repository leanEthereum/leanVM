module

public import NativeRustcVmX64.Bus.BusLayout.Exec
public import NativeRustcVmX64.Bus.BusLayout.Model
public import NativeRustcVmX64.Bus.Common
public import NativeRustcX64.Got

/-!
# `bus_layout`'s proof: what its parts share (x86-64)

The frame (`fb`, 1808 bytes below the entry's RSP): the layout under construction at `8` (its
depth, the framework's count at `16` and placements from `24`, the tables' count at `72` and
placements from `80`), the sizes at `896`, the offsets at `1328`, the pushes from `1760`. The
sizes `S` (the framework's, then each block's owner's log-height), the offsets and depth `O`,
placement `j` `P j` (`Model`). A block writing a range of the frame below the pushes keeps the
function's body (`Body.of_sub`). Words read where memory changed only in the stack: the blocks'
owners (`owner_word`), the layout's heights (`height_word`). The layout built in the frame, moved
to the output (`built`, `busLayoutWAt_transfer`).
-/

namespace NativeRustcVmX64.Bus.BusLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open LeanVM.Protocol.Verifier (Placement)

@[expose] public section

/-- The framework's count. -/
abbrev nf (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
/-- The framework's sizes. -/
abbrev fws (m0 : MachineData) : Array Nat := natsOf m0 (reg m0 .rsi) (nf m0)
/-- The sizes. -/
abbrev S (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) : List Nat :=
  szs (fws m0) L.tableLogHeights bl
/-- The offsets and the depth. -/
abbrev O (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) :
    Array Nat × Nat :=
  so (fws m0) L.tableLogHeights bl
/-- Placement `j`. -/
abbrev P (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) (j : Nat) :
    Placement :=
  pl (fws m0) L.tableLogHeights bl j
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 1808

/-- The sizes' first `k` words. -/
def SizesAt (d : DataMem) (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (k : Nat) : Prop :=
  ∀ j < k, NativeRustcVm.WordAt d (off (fb m0) (896 + 8 * j)) ((S L bl m0).getD j 0).toUInt64

/-- The offsets' words. -/
def OffsAt (d : DataMem) (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) :
    Prop :=
  ∀ j < nf m0 + bl.length,
    NativeRustcVm.WordAt d (off (fb m0) (1328 + 8 * j)) ((O L bl m0).1.getD j 0).toUInt64

/-- **The layout under construction** after `i` placements. -/
structure Part (d : DataMem) (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (i : Nat) : Prop where
  depth : NativeRustcVm.WordAt d (off (fb m0) 8) (O L bl m0).2.toUInt64
  tlen : NativeRustcVm.WordAt d (off (fb m0) 72) (i - nf m0).toUInt64
  fw : ∀ j < min i (nf m0), PlacementAt d (off (fb m0) (24 + 16 * j)) (P L bl m0 j)
  tb : ∀ j < i - nf m0, PlacementAt d (off (fb m0) (80 + 16 * j)) (P L bl m0 (nf m0 + j))

end

public section

theorem fws_size (m0 : MachineData) : (fws m0).size = nf m0 := by simp [natsOf]

theorem S_length (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) :
    (S L bl m0).length = nf m0 + bl.length := by
  rw [length_szs, fws_size]

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1808 := by decide

theorem slots_lo : ∀ p ∈ slots, 1760 ≤ p.1 := by decide

theorem slots_all : ∀ r, calleeSaved r = true → slots.any (·.2 == r) = true := by
  intro r hr
  cases r <;> first | exact absurd hr (by decide) | decide

theorem S_getD_fw {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData} {j : Nat}
    (hj : j < nf m0) :
    (S L bl m0).getD j 0 = (NativeRustcVm.wordOf m0.dmem
      (reg m0 .rsi + BitVec.ofNat 64 (8 * j))).toNat := by
  simp only [S, szs, List.getD_eq_getElem?_getD, List.getElem?_append_left
    (show j < (fws m0).toList.length by simpa [fws_size] using hj)]
  simp only [fws, natsOf, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by rw [NativeRustcVm.length_wordsOf]; exact hj)]
  simp

theorem S_getD_bl {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData} {i : Nat}
    (hi : i < bl.length) :
    (S L bl m0).getD (nf m0 + i) 0 = L.tableLogHeights.getD bl[i].owner 0 := by
  simp only [S, szs, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [fws_size])]
  simp [fws_size, List.getElem?_eq_getElem hi]

section
variable [Labels] {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}

/-- The two loader slots used by the layout and its offsets callee. -/
theorem pre_got (h : BusLayoutPre L bl m0) :
    GotAt m0 busLayoutStack
      ([(reg m0 .rdi, optBusLayoutBytes), (reg m0 .rcx, 16 * bl.length),
        (reg m0 .r9, layoutBytes)] ++
        (if 8 * nf m0 = 0 then [] else [(reg m0 .rsi, 8 * nf m0)])) ["memcpy", "memset"] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Only stack bytes change before the final layout copy. -/
theorem got_byte (h : BusLayoutPre L bl m0) {d : MachineData}
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem
      (NativeRustcVm.InRange (stackBelow m0 busLayoutStack) busLayoutStack))
    {l : Label} (hl : l ∈ ["memcpy", "memset"]) {i : Nat} (hi : i < 8) :
    d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      some (byteOf (Labels.label l).toBitVec i) := by
  rw [get_keep h.1 hs ((pre_got h).1 l hl).2.2.1 ((pre_got h).1 l hl).2.1 hi]
  exact (pre_got h).byte hl hi

/-- The ordinary frame plus the particular slot read by this block. -/
theorem wf_got (h : BusLayoutPre L bl m0) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {l : Label} (hl : l ∈ ["memcpy", "memset"])
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 d 1808 [(gotAddr l, 8)] vars ret).WF :=
  wf1 h.1 (by decide) hk ⟨(pre_got h).mapped hl, ((pre_got h).1 l hl).2.1⟩
    ((pre_got h).1 l hl).2.2.1

/-- Seed a GOT call from its actual loader bytes. -/
theorem match_got (h : BusLayoutPre L bl m0) {d : MachineData}
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem
      (NativeRustcVm.InRange (stackBelow m0 busLayoutStack) busLayoutStack))
    {l : Label} (hl : l ∈ ["memcpy", "memset"]) {o : Nat}
    (hsp : reg d .rsp = off (fb m0) o)
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    Match (frameEnv m0 d 1808 [(gotAddr l, 8)] vars ret) (gotS o l) d := by
  have hm := match_ofMachine (m := d)
    (regions := [(fb m0, 1816), (gotAddr l, 8)]) (vars := vars) (ret := ret)
    (sregions := [1816, 8]) (known := [(.rsp, .ptr 0 o)])
    (labels := []) (bounds := []) (aliases := [(.gotSlot l, 1, 0)])
    ⟨rfl, rfl, trivial⟩ ⟨hsp, trivial⟩ trivial trivial
    ⟨(BitVec.add_zero _).symm, trivial⟩
  apply hm.withKnownBytes (r := 1) (off := 0) (n := 8) (v := .label l)
  intro i hi
  simpa only [Env.ofMachine_mem0, Env.base_ofMachine_eq, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.map_some, Option.getD_some, Nat.zero_add, Sym.eval]
    using got_byte h hs hl hi

theorem pre_S_le (hpre : BusLayoutPre L bl m0) : ∀ s ∈ S L bl m0, s ≤ 30 :=
  szs_le hpre.2.2.1 hpre.2.2.2.2.2.2.2.2.2.2.1.heights_le

theorem pre_n (hpre : BusLayoutPre L bl m0) : nf m0 + bl.length ≤ 54 := by
  have h1 : nf m0 ≤ 3 := hpre.2.1
  have h2 := hpre.2.2.2.2.2.1
  unfold maxBlocks at h2
  omega

theorem pre_O_lt (hpre : BusLayoutPre L bl m0) (j : Nat) :
    (O L bl m0).1.getD j 0 < 2 ^ 64 := by
  show (stackOffsets (S L bl m0).toArray).1.getD j 0 < 2 ^ 64
  have h1 := offset_le (l := S L bl m0) j
  have h2 := sum_pow_le (pre_S_le hpre)
  have h3 : (S L bl m0).length * 2 ^ 30 ≤ 54 * 2 ^ 30 :=
    Nat.mul_le_mul_right _ (by rw [S_length]; exact pre_n hpre)
  omega

theorem pre_depth_lt (hpre : BusLayoutPre L bl m0) : (O L bl m0).2 < 2 ^ 64 := by
  show (stackOffsets (S L bl m0).toArray).2 < 2 ^ 64
  have := depth_le (pre_S_le hpre) (by rw [S_length]; exact pre_n hpre)
  omega

theorem pre_S_getD_le (hpre : BusLayoutPre L bl m0) (j : Nat) :
    (S L bl m0).getD j 0 ≤ 30 := by
  rw [List.getD_eq_getElem?_getD]
  cases e : (S L bl m0)[j]? with
  | none => simp
  | some x => exact pre_S_le hpre x (List.mem_of_getElem? e)

theorem pre_P_ok (hpre : BusLayoutPre L bl m0) (j : Nat) :
    (P L bl m0 j).variableCount < 2 ^ 64 ∧ (P L bl m0 j).index < 2 ^ 64 :=
  ⟨by have := pre_S_getD_le hpre j; show (S L bl m0).getD j 0 < 2 ^ 64; omega, pre_O_lt hpre j⟩

/-- Block `i`'s owner, where memory changed only in the stack. -/
theorem owner_word (hpre : BusLayoutPre L bl m0) {d : MachineData}
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem
      (NativeRustcVm.InRange (stackBelow m0 busLayoutStack) busLayoutStack))
    {i : Nat} (hi : i < bl.length) :
    NativeRustcVm.wordOf d.dmem (reg m0 .rcx + BitVec.ofNat 64 (16 * i)) = bl[i].owner.toUInt64 := by
  obtain ⟨hst, -, -, -, -, -, -, -, hB, hBok, -⟩ := hpre
  have hb := hB.flatMap_getElem (k := 16)
    (fun x ↦ by simp [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes,
      NativeRustcVm.length_wordBytes]) hi
  simp only [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes] at hb
  rw [← NativeRustcVm.wordOf_of_wordAt hb.left]
  apply NativeRustcVm.wordOf_congr
  intro t ht
  rw [NativeRustcVm.addr_add_add]
  exact get_keep hst hs hBok.2 hBok.1.2 (by omega)

/-- Height `o` of the layout, where memory changed only in the stack. -/
theorem height_word (hpre : BusLayoutPre L bl m0) {d : MachineData}
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem
      (NativeRustcVm.InRange (stackBelow m0 busLayoutStack) busLayoutStack))
    {o : Nat} (ho : o < 6) :
    NativeRustcVm.wordOf d.dmem (reg m0 .r9 + BitVec.ofNat 64 (24 + 8 * o)) =
      (L.tableLogHeights.getD o 0).toUInt64 := by
  obtain ⟨hst, -, -, -, -, -, -, -, -, -, hL, hLok, -⟩ := hpre
  have hsz : L.tableLogHeights.size = 6 := hL.heights_size
  have hw := NativeRustcVm.WordsAt.getElem hL.heights (i := o) (by simp [hsz, ho])
  simp only [List.getElem_map, Array.getElem_toList] at hw
  rw [show off (reg m0 .r9) 24 + BitVec.ofNat 64 (8 * o) = reg m0 .r9 + BitVec.ofNat 64 (24 + 8 * o)
    from NativeRustcVm.addr_add_add _ _ _] at hw
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some,
    ← NativeRustcVm.wordOf_of_wordAt hw]
  apply NativeRustcVm.wordOf_congr
  intro t ht
  rw [NativeRustcVm.addr_add_add]
  exact get_keep hst hs hLok.2 hLok.1.2
    (by unfold layoutBytes NativeRustcVm.Layout.placementBytes columnCountW; omega)

end

/-! ## The body, through blocks writing below the pushes -/

/-- **A block writing a range of the frame below the slots** keeps the body. -/
theorem Body.of_sub {m0 st st' : MachineData} {F N o : Nat} {sl : Slots} (hst : StackOk m0 N)
    (hF : F ≤ N) (hb : Body m0 F N sl o st) {a n : Nat} (han : a + n ≤ F)
    (hslot : ∀ p ∈ sl, a + n ≤ p.1) (hsle : ∀ p ∈ sl, p.1 + 8 ≤ F)
    (hs : NativeRustcVm.SameOutside st.dmem st'.dmem
      (NativeRustcVm.InRange (off (stackBelow m0 F) a) n))
    (hsp : rspOf st' = rspOf st) (hk : Kept st.dmem st'.dmem)
    (hregs : ∀ r, calleeSaved r = true → sl.any (·.2 == r) = false → reg st' r = reg st r) :
    Body m0 F N sl o st' := by
  have hrsp := hst.1
  have htop := hst.2.1
  have hnw : NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8) := frame_noWrap hst hF
  have hbase : (stackBelow m0 F).toNat = (rspOf m0).toNat - F := stackBelow_toNat (by omega)
  have hout : ∀ j, a + n ≤ j → j < F + 8 →
      ¬NativeRustcVm.InRange (off (stackBelow m0 F) a) n (off (stackBelow m0 F) j) := by
    intro j h1 h2 h
    rw [inRange_off_iff (by omega) (by unfold NativeRustcVm.NoWrap at hnw; omega)] at h
    omega
  refine ⟨⟨hsp.trans hb.fr.sp, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hb.fr.kept hk,
    fun r hr hsl ↦ (hregs r hr hsl).trans (hb.fr.regs r hr hsl)⟩, fun q hq ↦ ?_⟩
  · refine bytesAt_congr (hb.fr.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    exact hs _ (hout _ (by have := hslot p hp; omega) (by have := hsle p hp; omega))
  · rw [hs _ (hout _ (by omega) (by omega))]
    exact hb.fr.ret j hj
  · refine (hs q fun h ↦ hq ?_).trans (hb.same q hq)
    exact inRange_frame_stack htop hrsp hF (inRange_of_off (N := F) (by
      unfold NativeRustcVm.NoWrap at hnw ⊢; omega) han h)

end

end NativeRustcVmX64.Bus.BusLayout
