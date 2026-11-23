module

public import NativeRustcVmX64.Wire.InsD.Exec
public import NativeRustcVmX64.Wire.Common
public import NativeRustcVmX64.Spec.Wire
public import NativeRustcVm.Wire.InsD
public import NativeRustcVm.Wire.WordsFacts

/-!
# `ins_d`'s states (x86-64)

The words `L` (the list `l = L.map toNat`) at `a` (RDI), `n = L.length` (RSI), `x` (RDX). The
array's words as `L` with a hole at `q` holding `g` (`hl L q g`, the elements from `q` moved up
one); a change of a window of the array (`wordsAt_update`, `same_window`); what every state keeps
(`Kp`); the elements' addresses (`eval_elem`, `elem_alias`); the result (`post_of`,
`insD_words`).
-/

namespace NativeRustcVmX64.Wire.InsD

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmX64.Vm.InsD

@[expose] public section

/-- `L` with the elements from `q` moved up one and `g` at `q`. -/
def hl (L : List UInt64) (q : Nat) (g : UInt64) : List UInt64 := L.take q ++ g :: L.drop q

/-- The array's address. -/
abbrev arr (m : MachineData) : BitVec 64 := reg m .rdi

/-- Element `p`'s address. -/
abbrev pos (m : MachineData) (p : Nat) : BitVec 64 := arr m + BitVec.ofNat 64 (8 * p)

/-- What every state of `ins_d` keeps of its entry state `m`. -/
structure Kp (m s : MachineData) : Prop where
  rdi : reg s .rdi = reg m .rdi
  rdx : reg s .rdx = reg m .rdx
  rsp : reg s .rsp = rspOf m
  sv : Saved m s
  so : NativeRustcVm.SameOutside m.dmem s.dmem (NativeRustcVm.InRange (arr m) 2048)

end

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem length_hl (L : List UInt64) {q : Nat} (hq : q ≤ L.length) (g : UInt64) :
    (hl L q g).length = L.length + 1 := by
  simp [hl]; omega

theorem getD_hl {L : List UInt64} {q : Nat} (hq : q ≤ L.length) (g : UInt64) (i : Nat) :
    (hl L q g).getD i 0 =
      if i < q then L.getD i 0 else if i = q then g else L.getD (i - 1) 0 := by
  simp only [hl, List.getD_eq_getElem?_getD]
  by_cases h1 : i < q
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt h1]
    simp only [h1, ↓reduceIte]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [h1, ↓reduceIte, List.length_take, Nat.min_eq_left hq]
    by_cases h2 : i = q
    · subst h2; simp
    · rw [show i - q = (i - q - 1) + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_drop, show q + (i - q - 1) = i - 1 by omega]
      simp only [h2, ↓reduceIte]

theorem wordsAt_getD {d : Mem 64} {a : BitVec 64} {ws : List UInt64} :
    WordsAt d a ws ↔ ∀ i < ws.length, WordAt d (a + BitVec.ofNat 64 (8 * i)) (ws.getD i 0) := by
  rw [NativeRustcVm.wordsAt_iff]
  refine ⟨fun h i hi ↦ ?_, fun h i hi ↦ ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]; exact h i hi
  · have := h i hi
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

/-- **A window changed**: words `lo` to `hi` as `C'`'s, the others kept from `C`. -/
theorem wordsAt_update {d d' : Mem 64} {a : BitVec 64} {C C' : List UInt64}
    (hl : C'.length = C.length) (h : WordsAt d a C) (hnw : NativeRustcVm.NoWrap a (8 * C.length))
    {lo hi : Nat} (hlo : lo < hi) (hhi : hi ≤ C.length)
    (hs : NativeRustcVm.SameOutside d d'
      (NativeRustcVm.InRange (a + BitVec.ofNat 64 (8 * lo)) (8 * (hi - lo))))
    (hin : ∀ i, lo ≤ i → i < hi → WordAt d' (a + BitVec.ofNat 64 (8 * i)) (C'.getD i 0))
    (hout : ∀ i < C.length, i < lo ∨ hi ≤ i → C'.getD i 0 = C.getD i 0) : WordsAt d' a C' := by
  unfold NativeRustcVm.NoWrap at hnw
  rw [wordsAt_getD] at h ⊢
  intro i hi'
  rw [hl] at hi'
  by_cases hw : lo ≤ i ∧ i < hi
  · exact hin i hw.1 hw.2
  · rw [hout i hi' (by omega)]
    refine NativeRustcVm.BytesAt.of_sameOutside (h i hi') hs fun t ht hq ↦ ?_
    simp only [NativeRustcVm.length_wordBytes] at ht
    rw [NativeRustcVm.addr_add_add] at hq
    have h1 : (a + BitVec.ofNat 64 (8 * lo)).toNat = a.toNat + 8 * lo :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [h1]; omega), h1,
      NativeRustcVm.toNat_add_ofNat (by omega)] at hq
    omega

/-- **The writes of a block** within the bytes `b` to `b + N`: memory changed only there. -/
theorem same_window [Labels] {env : Env} {S : SState} {d' : MachineData} (hm : Match env S d')
    (hwf : env.WF) {b : BitVec 64} {N : Nat} (hN : b.toNat + N ≤ 2 ^ 64)
    (hw : ∀ w ∈ S.mem, ∀ b' sz, env.regions[w.r]? = some (b', sz) →
      b.toNat ≤ b'.toNat + w.off ∧ b'.toNat + w.off + w.n ≤ b.toNat + N) :
    NativeRustcVm.SameOutside env.mem0 d'.dmem (NativeRustcVm.InRange b N) := by
  intro q hq
  refine hm.get?_mem0 hwf fun ⟨w, hw', b', sz, hb, h1, h2⟩ ↦ hq ?_
  have := hw w hw' b' sz hb
  rw [NativeRustcVm.inRange_iff hN]
  omega

theorem Kp.refl (m : MachineData) : Kp m m :=
  ⟨rfl, rfl, rfl, ⟨fun _ _ ↦ rfl, fun _ h ↦ h⟩, fun _ _ ↦ rfl⟩

theorem saved_trans {a b c : MachineData} (h1 : Saved a b) (h2 : Saved b c) : Saved a c :=
  ⟨fun r hr ↦ (h2.1 r hr).trans (h1.1 r hr), fun p h ↦ h2.2 p (h1.2 p h)⟩

variable {m : MachineData}

/-- A block run from a state that keeps `m`'s, keeping RDI, RDX, RSP, the callee-saved registers,
and changing at most the array. -/
theorem Kp.block [Labels] {s s' : MachineData} {env : Env} {S S' : SState} (hk : Kp m s)
    (hm : Match env S s) (hm' : Match env S' s') (hwf : env.WF) (hd : s.dmem = env.mem0)
    (hkeep : keeps S S' = true)
    (hregs : ∀ r ∈ [Reg64.rdi, .rdx, .rsp], S.reg r = some (.reg r) ∧ S'.reg r = some (.reg r))
    (hso : NativeRustcVm.SameOutside s.dmem s'.dmem (NativeRustcVm.InRange (arr m) 2048)) :
    Kp m s' where
  rdi := (Match.reg_eq hm hm' (hregs .rdi (by simp)).1 (hregs .rdi (by simp)).2).trans hk.rdi
  rdx := (Match.reg_eq hm hm' (hregs .rdx (by simp)).1 (hregs .rdx (by simp)).2).trans hk.rdx
  rsp := (Match.reg_eq hm hm' (hregs .rsp (by simp)).1 (hregs .rsp (by simp)).2).trans hk.rsp
  sv := saved_trans hk.sv (Match.saved hm hm' hwf hd hkeep)
  so := fun p hp ↦ (hso p hp).trans (hk.so p hp)

/-- The element's address: index `zext8 y`, eight bytes each. -/
theorem eval_elem [Labels] (env : Env) (y : Sym) :
    (elem y).eval env = env.regs .rdi + BitVec.ofNat 64 (8 * ((y.eval env).toNat % 256)) := by
  simp only [elem, Sym.eval, BinOp.apply, UnOp.apply, low_W64, ext_W64]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, ext, low, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Width.bits]
  omega

section Geo

variable (hok : NativeRustcVm.Region.Ok m.dmem ⟨arr m, 2048⟩)
include hok

theorem arr_noWrap : (arr m).toNat + 2048 ≤ 2 ^ 64 := hok.2

theorem pos_toNat {p : Nat} (hp : p < 256) : (pos m p).toNat = (arr m).toNat + 8 * p :=
  NativeRustcVm.toNat_add_ofNat (by have := arr_noWrap hok; omega)

theorem pos_noWrap {p : Nat} (hp : p < 256) : NativeRustcVm.NoWrap (pos m p) 8 :=
  NativeRustcVm.NoWrap.sub (n := 2048) hok.2 (by omega)

theorem pos_mapped {s : MachineData} (hk : Kp m s) {p : Nat} (hp : p < 256) :
    NativeRustcVm.Mapped s.dmem (pos m p) 8 :=
  fun i hi ↦ hk.sv.2 _ (NativeRustcVm.Mapped.sub (n := 2048) hok.1 (o := 8 * p) (m := 8)
    (by omega) i hi)

theorem pos_ok {s : MachineData} (hk : Kp m s) {p : Nat} (hp : p < 256) :
    NativeRustcVm.Mapped s.dmem (pos m p) 8 ∧ NativeRustcVm.NoWrap (pos m p) 8 :=
  ⟨pos_mapped hok hk hp, pos_noWrap hok hp⟩

theorem pos_apart {p q : Nat} (hp : p < 256) (hq : q < 256) (hpq : p ≠ q) :
    NativeRustcVm.Apart (pos m p) 8 (pos m q) 8 := by
  unfold NativeRustcVm.Apart
  rw [pos_toNat hok hp, pos_toNat hok hq]
  omega

/-- A change of positions `lo` to `hi` changes only the array. -/
theorem window_sub {lo hi : Nat} (hlo : lo ≤ hi) (hhi : hi ≤ 256) {d d' : Mem 64}
    (h : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (pos m lo) (8 * (hi - lo)))) :
    NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (arr m) 2048) :=
  NativeRustcVm.SameOutside.mono h fun _ hq ↦
    NativeRustcVm.InRange.of_sub (n := 2048) hq hok.2 (by omega)

/-- The array's words `C`, `C.length ≤ 256`, kept by a change of the array's positions. -/
theorem noWrap_words {C : List UInt64} (hC : C.length ≤ 256) :
    NativeRustcVm.NoWrap (arr m) (8 * C.length) := by
  have := arr_noWrap hok; unfold NativeRustcVm.NoWrap; omega

end Geo

theorem elem_alias [Labels] {s : MachineData} (hk : Kp m s) {regions : List (BitVec 64 × Nat)}
    {r p : Nat} (hb : regions[r]? = some (pos m p, 8)) {y : Sym}
    (hy : (y.eval (Env.ofMachine s regions)).toNat % 256 = p) :
    (elem y).eval (Env.ofMachine s regions) = (Env.ofMachine s regions).base r + BitVec.ofInt 64 0 := by
  rw [eval_elem, Env.base_ofMachine _ _ _ _ hb, hy, Env.ofMachine_regs,
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  exact congrArg (· + _) hk.rdi

theorem load_pos [Labels] {s : MachineData} {regions : List (BitVec 64 × Nat)} {r p : Nat}
    (hb : regions[r]? = some (pos m p, 8)) {w : UInt64} (h : WordAt s.dmem (pos m p) w) :
    (Env.ofMachine s regions).load r 0 8 = w.toBitVec :=
  Wire.load_word (by
    rw [Env.base_ofMachine _ _ _ _ hb, NativeRustcVm.addr_add_zero]; exact h)

/-! ## The model -/

/-- The model's list. -/
abbrev lst (L : List UInt64) : List Nat := L.map UInt64.toNat

/-- `x`. -/
abbrev xv (m : MachineData) : Nat := (reg m .rdx).toNat

/-- The elements before `i` are below `x`. -/
@[expose] def Below (m : MachineData) (L : List UInt64) (i : Nat) : Prop :=
  ∀ j (hj : j < i) (hjn : j < L.length), L[j].toNat < xv m

/-- Element `i`, if there is one, is above `x`. -/
@[expose] def Above (m : MachineData) (L : List UInt64) (i : Nat) : Prop :=
  ∀ (h : i < L.length), xv m < L[i].toNat

/-- **The postcondition** from the words `L` the array held, and the result for their list. -/
theorem post_of {L : List UInt64} (hL : L.length = (reg m .rsi).toNat)
    (hW : WordsAt m.dmem (arr m) L) {m' : MachineData} (hsv : Saved m m')
    (hso : NativeRustcVm.SameOutside m.dmem m'.dmem (NativeRustcVm.InRange (arr m) 2048))
    (h0 : (reg m' .rax).toNat = (insD (lst L) (xv m)).length)
    (hw : WordsAt m'.dmem (arr m) ((insD (lst L) (xv m)).map Nat.toUInt64)) : InsDPost m m' := by
  refine ⟨fun l hl hb hwl ↦ ?_, hso, hsv⟩
  have he : l.map Nat.toUInt64 = L := wordsAt_unique hwl hW (by simp only [List.length_map]; omega)
  have : l = lst L := by rw [eq_map_toNat hb, he]
  subst this
  exact ⟨h0, hw⟩

/-- `insD` where `x` goes in at `i`, as words. -/
theorem insD_words {L : List UInt64} {i : Nat} (hle : i ≤ L.length) (hb : Below m L i)
    (ha : Above m L i) :
    insD (lst L) (xv m) = (lst L).take i ++ xv m :: (lst L).drop i ∧
      ((lst L).take i ++ xv m :: (lst L).drop i).map Nat.toUInt64 =
        hl L i (UInt64.ofBitVec (reg m .rdx)) := by
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_eq_of_le hle with hi | rfl
    · exact insD_at _ _ i (by simpa using hi) (fun j hj ↦ by simpa using hb j hj (by omega))
        (by simpa using ha hi)
    · have hall : ∀ y ∈ lst L, y < xv m := fun y hy ↦ by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
        simpa using hb j (by simpa using hj) (by simpa using hj)
      rw [insD_end _ _ hall, List.take_of_length_le (by simp), List.drop_of_length_le (by simp)]
  · simp only [List.map_append, List.map_cons, List.map_take, List.map_drop, map_toUInt64_toNat,
      hl]
    congr 2
    apply UInt64.toBitVec_inj.mp
    simp [xv]

end

end NativeRustcVmX64.Wire.InsD
