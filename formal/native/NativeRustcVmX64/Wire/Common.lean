module

public import NativeRustcX64.Sym
public import NativeRustcX64.Mem.Common
public import NativeRustcX64.KeccakF.Inv
public import NativeRustcArm.Code.Infix
public import NativeRustc.Bytes
public import NativeRustcVm.MemLemmas
public import NativeRustcVm.Wire.Rep
public import NativeRustcX64.Hasher.Bytes
import NativeVm.Wire.Read

/-!
# Helpers of the wire decoder's proofs (x86-64)

What the executor loads (`load_word`, `load_byte`, `load_le`: bytes as `leNat`), `or`s and
shifts of disjoint bits as sums (`toNat_or_add`, `toNat_shl`), a block of a placed function in
the program (`infix_of`), the final `retq` of a leaf keeping every register its block keeps
(`ret_keep`), and memory changed only in one window of a region (`Match.sameOutside_in`).
-/

namespace NativeRustcVmX64.Wire

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem LeanVM.Protocol.KeccakHash NativeVm.Wire

public section

/-- A word's bytes loaded: the word. -/
theorem ofInt_ofBytes_wordBytes (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes (wordBytes v)) = v.toBitVec := by
  have hw := Hasher.wordBytes_ofBitVec v.toBitVec
  have hb := Sym.ofBytes_byteOf v.toBitVec 0 8
  simp only [Nat.zero_add] at hb
  rw [show UInt64.ofBitVec v.toBitVec = v from rfl] at hw
  rw [hw, hb, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := v.toBitVec.isLt
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

/-- The bytes of a 64-bit value: the word's. -/
theorem byteOf_range (x : BitVec 64) :
    (List.range 8).map (byteOf x) = wordBytes (UInt64.ofBitVec x) :=
  (Hasher.wordBytes_ofBitVec x).symm

/-- **A word at a region's offset** is what the environment loads there. -/
theorem load_word {env : Env} {r off : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 off) v) :
    env.load r off 8 = v.toBitVec := by
  rw [Env.load_of_bytesAt (NativeRustcVm.length_wordBytes v) h, ofInt_ofBytes_wordBytes]

/-- A byte at a region's offset, loaded. -/
theorem load_byte {env : Env} {r off : Nat} {b : UInt8}
    (h : env.mem0.get? (env.base r + BitVec.ofNat 64 off) = some b) :
    (env.load r off 1).toNat = b.toNat := by
  have hl := Env.load_of_bytesAt (env := env) (r := r) (off := off) (bs := [b]) (n := 1) rfl
    (fun i hi ↦ by
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi
      simpa using h)
  rw [hl, ofBytes_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  show (0 * 256 + b.toNat) % 2 ^ 64 = b.toNat
  have := b.toNat_lt
  omega

/-- `leNat` by Horner's rule, from the lowest byte. -/
theorem leNat_cons (B : List UInt8) (p n : Nat) :
    leNat B p (n + 1) = (B.getD p 0).toNat + 256 * leNat B (p + 1) n := by
  unfold leNat
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.add_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ ↦ by
    rw [show p + (k + 1) = p + 1 + k by omega, pow_succ]
    ring

theorem leNat_zero (B : List UInt8) (p : Nat) : leNat B p 0 = 0 := by
  simp [leNat]

/-- `Nat.ofBytes` of the `n` bytes of `B` from `p` is `leNat`. -/
theorem ofBytes_range (B : List UInt8) (p : Nat) : ∀ n,
    Nat.ofBytes ((List.range n).map fun i ↦ B.getD (p + i) 0) = leNat B p n
  | 0 => by rw [leNat_zero]; rfl
  | n + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, leNat_cons]
    have ih := ofBytes_range B (p + 1) n
    have e : ((fun i ↦ B.getD (p + i) 0) ∘ Nat.succ) = fun i ↦ B.getD (p + 1 + i) 0 :=
      funext fun i ↦ by
        show B.getD (p + (i + 1)) 0 = B.getD (p + 1 + i) 0
        rw [show p + (i + 1) = p + 1 + i by omega]
    rw [e]
    show Nat.ofBytes _ * 256 + (B.getD (p + 0) 0).toNat = _
    rw [ih, Nat.add_zero p]
    omega

/-- **`n` bytes loaded** from a region where `B`'s bytes from `p` are: `leNat`. -/
theorem load_le {env : Env} {r off n : Nat} {B : List UInt8} {p : Nat} (hn : n ≤ 8)
    (h : ∀ i < n, env.mem0.get? (env.base r + BitVec.ofNat 64 (off + i)) = some (B.getD (p + i) 0)) :
    (env.load r off n).toNat = leNat B p n := by
  unfold Env.load
  rw [List.map_congr_left (fun i hi ↦ by rw [h i (List.mem_range.mp hi), Option.getD_some]),
    ofBytes_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat, ofBytes_range]
  have := leNat_lt B p n
  have : 256 ^ n ≤ 2 ^ 64 :=
    (Nat.pow_le_pow_right (by omega) hn).trans (by norm_num)
  omega

/-- An `or` of a small value and a multiple of `2 ^ k` is their sum. -/
theorem toNat_or_add {a b : BitVec 64} {k : Nat} (ha : a.toNat < 2 ^ k) (hb : 2 ^ k ∣ b.toNat) :
    (a ||| b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_or, NativeRustc.lor_eq_add ha hb]

/-- A shift without overflow is a product. -/
theorem toNat_shl {x : BitVec 64} {k : Nat} (h : x.toNat * 2 ^ k < 2 ^ 64) :
    (x <<< k).toNat = x.toNat * 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-- **The writes of a block** all within bytes `o` to `o + n` of region `r0`: memory changed only
there. -/
theorem Match.sameOutside_in [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) (hwf : env.WF) {r0 : Nat} {b : BitVec 64} {sz o n : Nat}
    (hb : env.regions[r0]? = some (b, sz)) (hon : o + n ≤ sz)
    (hw : ∀ w ∈ S.mem, w.r = r0 ∧ o ≤ w.off ∧ w.off + w.n ≤ o + n) :
    SameOutside env.mem0 m.dmem (InRange (b + BitVec.ofNat 64 o) n) := by
  intro p hp
  refine hm.get?_mem0 hwf fun ⟨w, hwS, b', sz', hb', h1, h2⟩ ↦ hp ?_
  obtain ⟨hr, ho, hn⟩ := hw w hwS
  rw [hr, hb] at hb'
  cases hb'
  have hnw := hwf.noWrap r0 b sz hb
  have ho' : (b + BitVec.ofNat 64 o).toNat = b.toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [inRange_iff (by omega), ho']
  omega

/-! ## Values and branches -/

theorem ult64 (a b : BitVec 64) : CmpOp.apply .ult .W64 a b = decide (a.toNat < b.toNat) := by
  simp only [CmpOp.apply, low_W64]; rfl

theorem eq64 (a b : BitVec 64) : CmpOp.apply .eq .W64 a b = decide (a.toNat = b.toNat) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]

theorem eq32_zero (a : BitVec 64) (h : a.toNat < 2 ^ 32) :
    CmpOp.apply .eq .W32 a (BitVec.ofNat 64 0) = decide (a.toNat = 0) := by
  simp only [CmpOp.apply, low]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Width.bits]
  omega

theorem toNat_add64 (a b : BitVec 64) :
    (BinOp.apply .add .W64 a b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add]

theorem toNat_sub64 {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (BinOp.apply .sub .W64 a b).toNat = a.toNat - b.toNat := by
  have := a.isLt
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub]
  omega

theorem eval_reg [Labels] (env : Env) (r : Reg64) : (Sym.reg r).eval env = env.regs r := rfl

theorem eval_lit [Labels] (env : Env) (n : Nat) : (Sym.lit n).eval env = BitVec.ofNat 64 n := rfl

theorem eval_load [Labels] (env : Env) (r o n : Nat) : (Sym.load r o n).eval env = env.load r o n :=
  rfl

/-- A conditional exit's successor, the condition decided. -/
theorem pc_cond [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) {P : Prop} [Decidable P] (hc : c.eval env = decide P) :
    st.pc = if P then Labels.label l else next := by
  simp only [PcOk, hc] at h
  rw [h]
  by_cases hP : P <;> simp [hP]

theorem ite_t {α : Type} {P : Prop} [Decidable P] {a b : α} (h : P) :
    (if P then a else b) = a := by simp [h]

theorem ite_f {α : Type} {P : Prop} [Decidable P] {a b : α} (h : ¬P) :
    (if P then a else b) = b := by simp [h]

variable [Host]

/-- A block of a placed function is in the program. -/
theorem infix_of {F b : List Directive} {k j : Nat} (hb : b.IsInfixAt F j) (hne : b ≠ [])
    (hp : Placed F k) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- **A leaf's final `retq`**, from a state with RSP at the entry's and the return address's
bytes as at entry: back at the return address, RSP 8 above, memory kept, each register the
block's value for it. -/
theorem ret_keep {ds : List Directive} {k : Nat} {S' : SState} (hk : ds.IsInfixAt Host.prog k)
    (hx : exec ds sRet = some (S', .ret (.load 0 0 8))) (hrsp : S'.reg .rsp = some (.ptr 0 8))
    (hmem : S'.mem = []) (hkeeps : keeps sRet S' = true)
    {m : MachineData} {st : MachineState} (hpc : st.pc = Host.addrOf k) (hstk : StackOk m 0)
    (hsp : st.data.regs.get64 .rsp = rspOf m)
    (hslot : ∀ i < 8, st.data.dmem.get? (rspOf m + BitVec.ofNat 64 i) =
      m.dmem.get? (rspOf m + BitVec.ofNat 64 i)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m ∧
      rspOf st'.data = rspOf m + 8#64 ∧ st'.data.dmem = st.data.dmem ∧
      (∀ r v, S'.reg r = some v →
        reg st'.data r = v.eval (Env.ofMachine st.data [(rspOf m, 8)])) ∧
      Saved st.data st'.data) st := by
  obtain ⟨-, hnw, hmap⟩ := hstk
  rw [show rspOf m - BitVec.ofNat 64 0 = rspOf m from BitVec.sub_zero _] at hmap
  let env := Env.ofMachine st.data [(rspOf m, 8)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨fun i hi ↦ by
        show (st.data.dmem.get? (rspOf m + _)).isSome = true
        rw [hslot i hi]
        exact hmap i (by omega), by unfold NoWrap; exact hnw⟩,
      trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env sRet st.data := match_ofMachine ⟨rfl, trivial⟩
    ⟨show st.data.regs.get64 .rsp = (Sym.ptr 0 0).eval env by
      simp [Sym.eval, env, hsp], trivial⟩ trivial trivial trivial
  have hread := hm.read hwf (r := 0) (o := 0) (n := 8) rfl (by decide) (by decide)
  refine exec_at hk hx hwf (fun _ h ↦ nomatch h) hpc hm fun st' hm' hpc' ↦
    .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    have hb : env.base 0 + BitVec.ofNat 64 0 = rspOf m := by simp [env]
    rw [hb] at hread
    rw [loadInt_congr hslot] at hread
    exact (retOf_of_loadInt hread).symm
  · have h := hm'.regs .rsp _ hrsp
    simp only [Sym.eval, env, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some] at h
    exact h
  · exact (hm'.dmem_eq hwf hmem)
  · exact fun r v hr ↦ hm'.regs r v hr
  · exact Match.saved hm hm' hwf rfl hkeeps

/-- **A final block ending in `retq`**, run from a state `S0` without writes whose region 0 is
the return address (8 bytes at RSP, as at entry), the others `rest`: back at the return address,
RSP 8 above, the block's result. -/
theorem ret_with {ds : List Directive} {k : Nat} {S0 S' : SState} (hk : ds.IsInfixAt Host.prog k)
    (hx : exec ds S0 = some (S', .ret (.load 0 0 8))) (hrsp : S'.reg .rsp = some (.ptr 0 8))
    (h0 : S0.mem = []) (hS0 : S0.regions[0]? = some 8) {m : MachineData} {st : MachineState}
    {rest : List (BitVec 64 × Nat)} (hwf : (Env.ofMachine st.data ((rspOf m, 8) :: rest)).WF)
    (hm : Match (Env.ofMachine st.data ((rspOf m, 8) :: rest)) S0 st.data)
    (hpc : st.pc = Host.addrOf k)
    (hslot : ∀ i < 8, st.data.dmem.get? (rspOf m + BitVec.ofNat 64 i) =
      m.dmem.get? (rspOf m + BitVec.ofNat 64 i)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m ∧
      rspOf st'.data = rspOf m + 8#64 ∧
      Match (Env.ofMachine st.data ((rspOf m, 8) :: rest)) S' st'.data) st := by
  have hread := hm.read hwf (r := 0) (o := 0) (n := 8) hS0 (by decide) (by decide)
  rw [h0] at hread
  refine exec_at hk hx hwf (fun _ h ↦ nomatch h) hpc hm fun st' hm' hpc' ↦
    .done _ ⟨?_, ?_, hm'⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    have hb : (Env.ofMachine st.data ((rspOf m, 8) :: rest)).base 0 + BitVec.ofNat 64 0 =
        rspOf m := by simp
    rw [hb, loadInt_congr hslot] at hread
    exact (retOf_of_loadInt hread).symm
  · have h := hm'.regs .rsp _ hrsp
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some] at h
    exact h

end

end NativeRustcVmX64.Wire
