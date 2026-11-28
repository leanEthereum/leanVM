module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Grind
public import NativeRustcVmX64.Code.Vm.BusLayout.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `verify_bus_balance`'s head: what it shares (x86-64)

- `wordAt_transfer`, `placementAt_transfer`, `busLayoutWAt_transfer`: a side's layout moved.
- `get_of_copy`, `blw_copy`: bytes, a side's layout copied (its depth stored apart).
- `blocks_bytes_length`: a list of blocks' bytes.
- `fw_nats`: the framework sizes at `328`.
- `bl_call`: `bus_layout` from the frame, its output at `672`.
- `mc_call`: `memcpy` within the frame.
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout
open LeanVM.Protocol.Verifier (Placement)

public section

theorem wordAt_transfer {d d' : DataMem} {a b : BitVec 64} {n o : Nat} {w : UInt64}
    (htr : ∀ i < n, ∀ x, d.get? (off a i) = some x → d'.get? (off b i) = some x)
    (ho : o + 8 ≤ n) (h : NativeRustcVm.WordAt d (off a o) w) :
    NativeRustcVm.WordAt d' (off b o) w := fun i hi ↦ by
  have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
  rw [off_add]
  exact htr (o + i) (by omega) _ (by rw [← off_add]; exact h i hi)

theorem placementAt_transfer {d d' : DataMem} {a b : BitVec 64} {n o : Nat} {p : Placement}
    (htr : ∀ i < n, ∀ x, d.get? (off a i) = some x → d'.get? (off b i) = some x)
    (ho : o + 16 ≤ n) (h : PlacementAt d (off a o) p) : PlacementAt d' (off b o) p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, wordAt_transfer htr (by omega) h3, ?_⟩
  rw [off_off] at h4 ⊢
  exact wordAt_transfer htr (by omega) h4

/-- **A side's layout moved** with its 888 bytes. -/
theorem busLayoutWAt_transfer {d d' : DataMem} {a b : BitVec 64} {BL : BusLayoutW}
    (htr : ∀ i < 888, ∀ x, d.get? (off a i) = some x → d'.get? (off b i) = some x)
    (h : BusLayoutWAt d a BL) : BusLayoutWAt d' b BL := by
  obtain ⟨hdl, hd, ⟨hfs, hfl, hfi⟩, ⟨hts, htl, hti⟩⟩ := h
  refine ⟨hdl, ?_, ⟨hfs, wordAt_transfer htr (by omega) hfl, fun i hi ↦ ?_⟩,
    ⟨hts, wordAt_transfer htr (by omega) htl, fun i hi ↦ ?_⟩⟩
  · have := wordAt_transfer (o := 0) htr (by omega) (by rw [off_zero]; exact hd)
    rwa [off_zero] at this
  · have := hfi i hi
    rw [off_off] at this ⊢
    exact placementAt_transfer htr (by unfold NativeRustcVm.Bus.placementBytes; omega) this
  · have := hti i hi
    unfold maxBlocks at hts
    rw [off_off] at this ⊢
    exact placementAt_transfer htr (by unfold NativeRustcVm.Bus.placementBytes; omega) this

/-- A byte copied: where `d'` at `b` holds `bytesOf d a n`. -/
theorem get_of_copy {d d' : DataMem} {a b : BitVec 64} {n : Nat}
    (hb : NativeRustcX64.BytesAt d' b (bytesOf d a n)) :
    ∀ i < n, ∀ x, d.get? (off a i) = some x → d'.get? (off b i) = some x := fun i hi x hx ↦ by
  have := hb i (by simp [NativeRustcX64.bytesOf]; exact hi)
  rw [show off b i = b + BitVec.ofNat 64 i from rfl, this]
  simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range]
  rw [show a + BitVec.ofNat 64 i = off a i from rfl, hx, Option.getD_some]

/-- Bytes copied, then kept. -/
theorem copy_keep {d d' d'' : DataMem} {a b : BitVec 64} {n : Nat}
    (hb : NativeRustcX64.BytesAt d' b (bytesOf d a n)) (hs : Same d' d'' b n) :
    ∀ i < n, ∀ x, d.get? (off a i) = some x → d''.get? (off b i) = some x := fun i hi x hx ↦ by
  rw [show off b i = b + BitVec.ofNat 64 i from rfl, hs i hi]
  exact get_of_copy hb i hi x hx

/-- **A side's layout copied**: its depth word stored at `b`, its other `880` bytes copied. -/
theorem blw_copy {d d' : DataMem} {a b : BitVec 64} {BL : BusLayoutW} (h : BusLayoutWAt d a BL)
    (hw : NativeRustcVm.WordAt d' b BL.depth.toUInt64)
    (hc : ∀ i < 880, ∀ x, d.get? (off (off a 8) i) = some x → d'.get? (off (off b 8) i) = some x) :
    BusLayoutWAt d' b BL := by
  refine busLayoutWAt_transfer (fun i hi x hx ↦ ?_) h
  rcases Nat.lt_or_ge i 8 with h8 | h8
  · have e1 := h.depth i (by rw [NativeRustcVm.length_wordBytes]; exact h8)
    obtain rfl := Option.some.inj (e1.symm.trans hx)
    exact hw i (by rw [NativeRustcVm.length_wordBytes]; exact h8)
  · have e : 8 + (i - 8) = i := by omega
    have := hc (i - 8) (by omega) x (by rw [off_off, e]; exact hx)
    rwa [off_off, e] at this

/-- A list of blocks' bytes: `16` each. -/
theorem blocks_bytes_length (l : List NativeRustcVm.Data.Block) :
    (l.flatMap NativeRustcVm.Data.Block.bytes).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes, List.length_append,
      NativeRustcVm.length_wordBytes]
    omega

/-! ## The sides' blocks -/

theorem side0_len : (sideBlocks 0).length = 51 := by decide +kernel
theorem side1_len : (sideBlocks 1).length = 51 := by decide +kernel
theorem side2_len : (sideBlocks 2).length = 45 := by decide +kernel
theorem maxBlocks_eq : maxBlocks = 51 := by decide +kernel

theorem side0_own : ∀ x ∈ sideBlocks 0, x.owner < nTables := by decide +kernel
theorem side1_own : ∀ x ∈ sideBlocks 1, x.owner < nTables := by decide +kernel
theorem side2_own : ∀ x ∈ sideBlocks 2, x.owner < nTables := by decide +kernel

theorem side0_bytes : NativeRustcVm.Data.Item.pushBlocks.bytes =
    (sideBlocks 0).flatMap NativeRustcVm.Data.Block.bytes := by decide +kernel
theorem side1_bytes : NativeRustcVm.Data.Item.pullBlocks.bytes =
    (sideBlocks 1).flatMap NativeRustcVm.Data.Block.bytes := by decide +kernel
theorem side2_bytes : NativeRustcVm.Data.Item.countBlocks.bytes =
    (sideBlocks 2).flatMap NativeRustcVm.Data.Block.bytes := by decide +kernel

/-- The push and pull sides' framework sizes. -/
theorem fw_nats {m0 : MachineData} {m : MachineData} {L : LayoutW} {x1 x2 : BitVec 64}
    (h1 : x1 = loc m0 328) (h2 : x2.toNat = 3)
    (w0 : NativeRustcVm.WordAt m.dmem (loc m0 328) 0)
    (w1 : NativeRustcVm.WordAt m.dmem (loc m0 336) L.logMemory.toUInt64)
    (w2 : NativeRustcVm.WordAt m.dmem (loc m0 344) L.logBytecode.toUInt64)
    (hm : L.logMemory ≤ 30) (hb : L.logBytecode ≤ 30) : natsOf m x1 x2.toNat = fwRows L := by
  have hw : NativeRustcVm.WordsAt m.dmem (loc m0 328)
      [0, L.logMemory.toUInt64, L.logBytecode.toUInt64] :=
    NativeRustcVm.wordsAt_cons_iff.mpr ⟨w0, NativeRustcVm.wordsAt_cons_iff.mpr
      ⟨by rw [NativeRustcVm.addr_add_add]; exact w1, NativeRustcVm.wordsAt_cons_iff.mpr
        ⟨by rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]; exact w2,
          NativeRustcVm.wordsAt_nil _ _⟩⟩⟩
  have e : NativeRustcVm.wordsOf m.dmem (loc m0 328) 3 =
      [0, L.logMemory.toUInt64, L.logBytecode.toUInt64] := NativeRustcVm.wordsOf_of_wordsAt hw
  have e1 : L.logMemory.toUInt64.toNat = L.logMemory :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have e2 : L.logBytecode.toUInt64.toNat = L.logBytecode :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  unfold natsOf
  rw [h1, h2, e]
  simp only [List.map_cons, List.map_nil, e1, e2, fwRows]
  rfl

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **`bus_layout(672, fw, n, blocks, len, layout)`** from the frame: the side's layout, of the
framework sizes `fw`. -/
theorem bl_call (h : VerifyBusBalancePre a s0 L m0)
    (hbl : ∀ L bl, Spec (Labels.label NativeRustcVmX64.Vm.BusLayout.entryLabel) (BusLayoutPre L bl) (BusLayoutPost L bl))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (fr : St m0 96 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.BusLayout.entryLabel ∧ retOf st.data = next)
    {side : Nat} {it : NativeRustcVm.Data.Item}
    (hit : it.bytes = (sideBlocks side).flatMap NativeRustcVm.Data.Block.bytes)
    (hitgot : it ∈ [.pushBlocks, .pullBlocks, .countBlocks])
    (hl1 : 2 ≤ (sideBlocks side).length) (hl2 : (sideBlocks side).length ≤ maxBlocks)
    (hown : ∀ x ∈ sideBlocks side, x.owner < nTables)
    {rows : Array Nat} (hrows : busBlocks L.tableLogHeights rows = (L.push, L.pull, L.count))
    {fw : Array Nat} (hfw : natsOf st.data (reg st.data .rsi) (reg st.data .rdx).toNat = fw)
    (hfw3 : (reg st.data .rdx).toNat ≤ 3) (hfw30 : ∀ s ∈ fw, s ≤ 30)
    (hfok : InOk st.data (reg st.data .rsi) (8 * (reg st.data .rdx).toNat) busLayoutStack)
    (hfap : NativeRustcVm.Apart (loc m0 672) optBusLayoutBytes (reg st.data .rsi)
      (8 * (reg st.data .rdx).toNat))
    (hfgot : ∀ l ∈ ["memcpy", "memset"], 0 < (reg st.data .rdx).toNat →
      Apart (gotAddr l) 8 (reg st.data .rsi) (8 * (reg st.data .rdx).toNat))
    (xdi : reg st.data .rdi = loc m0 672) (xcx : reg st.data .rcx = rodataAddr it)
    (x8 : (reg st.data .r8).toNat = (sideBlocks side).length) (x9 : reg st.data .r9 = reg m0 .rsi)
    (cont : ∀ m2, St m0 104 m2 →
      OptBusLayoutWAt m2.dmem (loc m0 672) (some (busLayout fw (sideOf L side))) →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.get64 r = st.data.regs.get64 r) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow st.data busLayoutStack) busLayoutStack q ∨
          NativeRustcVm.InRange (loc m0 672) optBusLayoutBytes q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have hob : optBusLayoutBytes = 896 := rfl
  have hle : 5520 - 96 + busLayoutStack ≤ NN := le_bl
  have hlen : it.bytes.length = 16 * (sideBlocks side).length := by
    rw [hit, blocks_bytes_length]
  have hro := cal_ro h fr (by omega) hle it
  refine callF h (c := 96) (Nc := busLayoutStack) (lo := 672) (len := optBusLayoutBytes)
    (X := NativeRustcVm.InRange (loc m0 672) optBusLayoutBytes) (by omega) hle (by omega)
    (fun q hq ↦ .inr hq) (hbl L (sideBlocks side)) fr hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ by
      rcases hq' with hq' | hq'
      · rw [xdi] at hq'; exact .inr hq'
      · exact .inl hq', hq.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · dsimp only [BusLayoutPre]
    rw [xdi, xcx, x8, x9]
    refine ⟨cal_stack h fr (by omega) hle, hfw3, by rw [hfw]; exact hfw30, hfok, hl1, hl2, rfl,
      hown, by rw [← hit]; exact hro.1, ?_, lay_at h fr, cal_in h fr (by omega) hle (pre_layOk h),
      cal_localIn h fr (by omega) hle (by omega) (by omega), hfap, ?_,
      (apart_loc hS (pre_layOk h).2 (j := 672) (l := optBusLayoutBytes) (by omega)).symm,
      cal_got h fr (by omega) hle (by rfl) ?_⟩
    · rw [← hlen]
      exact ⟨⟨NativeRustcVm.BytesAt.mapped hro.1, hro.2.1⟩, hro.2.2⟩
    · rw [← hlen]
      exact (apart_loc hS ((pre_ro h) it).2.2 (j := 672) (l := optBusLayoutBytes) (by omega)).symm
    · intro l hl b hb
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with (rfl | rfl | rfl) | hb
      · exact got_apart_frame (pre_got h) hS hl N_ge (by omega)
      · rw [← hlen]
        apply ((pre_got h).1 l hl).2.2.2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hitgot
        rcases hitgot with rfl | rfl | rfl <;> simp
      · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
      · by_cases hn : 8 * (reg st.data .rdx).toNat = 0
        · simp only [hn, ↓reduceIte, List.not_mem_nil] at hb
        · simp only [hn, ↓reduceIte, List.mem_singleton] at hb
          subst b
          exact hfgot l hl (by omega)
  · obtain ⟨ho, -, hsv⟩ := hq2
    have ho' := ho rows
    rw [xdi, hfw, sideOf_eq hrows side] at ho'
    exact cont m2 fr2 ho' hsv.2 hcs2 hs2

/-- **`memcpy(dst, src, n)`** within the frame. -/
theorem mc_call (h : VerifyBusBalancePre a s0 L m0)
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (fr : St m0 96 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel ∧ retOf st.data = next)
    {dst src n : Nat} (hd1 : 104 ≤ dst) (hd : dst + n ≤ 5472) (hs1 : 104 ≤ src)
    (hs : src + n ≤ 5472) (hap : dst + n ≤ src ∨ src + n ≤ dst)
    (xdi : reg st.data .rdi = loc m0 dst) (xsi : reg st.data .rsi = loc m0 src)
    (xdx : (reg st.data .rdx).toNat = n)
    (cont : ∀ m2, St m0 104 m2 →
      NativeRustcX64.BytesAt m2.dmem (loc m0 dst) (bytesOf st.data.dmem (loc m0 src) n) →
      Kept st.data.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.get64 r = st.data.regs.get64 r) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        NativeRustcVm.InRange (stackBelow st.data 0) 0 q ∨ NativeRustcVm.InRange (loc m0 dst) n q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have hle : 5520 - 96 + 0 ≤ NN := le_mem
  refine callF h (c := 96) (Nc := 0) (lo := dst) (len := n)
    (X := NativeRustcVm.InRange (loc m0 dst) n) (by omega) hle hd
    (fun q hq ↦ .inr hq) hmc fr hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [xdi, xdx] at hq'; exact .inr hq', hq.2.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · unfold MemcpyPre
    rw [xdi, xsi, xdx]
    have hd' := cal_local h fr (by omega) hle (j := dst) (n := n) (by omega) (by omega)
    have hs' := cal_local h fr (by omega) hle (j := src) (n := n) (by omega) (by omega)
    have e : stackBelow st.data 0 = rspOf st.data := by
      unfold stackBelow
      simp
    have hap' := hd'.2.2.2.2.1
    rw [e] at hap'
    exact ⟨cal_stack h fr (by omega) hle, hd'.1, hs'.1, hd'.2.1, hs'.2.1,
      loc_apart hS (by omega) (by omega) hap, hap'⟩
  · obtain ⟨-, hb, -, hsv⟩ := hq2
    rw [xdi, xsi, xdx] at hb
    exact cont m2 fr2 hb hsv.2 hcs2 hs2

end

end NativeRustcVmX64.Bus.VerifyBusBalance
