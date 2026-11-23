module

public import NativeRustcVmArm.Wire.RdRows.ZeroA

/-!
# `rd_rows`' calls of `Reader::words`

The call's precondition from the places (`Geo.words_pre`), what it changes (`Geo.call_same`), the
leaves so far, the zeros before the row and the frame's words surviving it (`call_leaves`,
`call_zeros`, `call_frame`), a padded leaf completed (`leaves_snoc`), the result's flag
(`flag_snoc`).
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8}

theorem inRange_prefix {a p : BitVec 64} {m n : Nat} (h : InRange a m p) (hn : NoWrap a n)
    (hm : m ≤ n) : InRange a n p :=
  NativeRustcVm.InRange.of_sub (o := 0) (by rwa [NativeRustcVm.addr_add_zero]) hn (by omega)

/-- **`Reader::words`' precondition** for `sz / 8` words at byte `o` of leaf `i`. -/
theorem Geo.words_pre (G : Geo m0 bp B) {i o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    {s : MachineData} (hfr : Frm m0 s) (hx0 : s.regs.X0.toBitVec = rdr m0)
    (hx1 : s.regs.X1.toBitVec = leaf m0 i + BitVec.ofNat 64 o) (hx2 : 8 * s.regs.X2.toNat = sz)
    {ci : Nat} (hR : ReaderAt s.dmem (rdr m0) bp B ci) : ReaderWordsPre s := by
  have hst := G.g.st
  have hN := hst.2.1
  have := G.lvNw
  have hle : 512 * i + o + sz ≤ 512 * nr m0 := by omega
  refine ⟨hfr.stackOk hst (by decide) (by decide), ⟨fun j hj ↦ ?_, ?_⟩, bp, B, ci,
    by rw [hx0]; exact hR, ?_⟩
  · have hj' : j < sz := by rw [← hx2]; exact hj
    show (s.dmem.get? (s.regs.X1.toBitVec + BitVec.ofNat 64 j)).isSome
    rw [hx1, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
    exact hfr.kept _ (G.lvMap _ (by omega))
  · show NoWrap s.regs.X1.toBitVec (8 * s.regs.X2.toNat)
    rw [hx1, hx2, NativeRustcVm.addr_add_add]
    unfold NoWrap
    rcases NativeRustcVm.toNat_add_ofNat_le (a := lv m0) (i := 512 * i + o) (by omega) with
      h1 | ⟨h1, -⟩ <;> rw [h1] <;> omega
  · have aS := G.sub_apart hle G.aS
    have aR := G.sub_apart hle G.aR
    have aB := G.sub_apart hle G.aB
    rw [← hx1, ← hx2] at aS aR aB
    rw [hx0]
    simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨(hfr.apart hN G.g.sr.symm (by decide)).symm, (hfr.apart hN G.g.sb.symm (by decide)).symm,
      (hfr.apart hN aS (by decide)).symm⟩, ⟨G.g.rb, aR.symm⟩, aB.symm, fun _ h ↦ h.elim⟩

/-- **What a call of `Reader::words` changes**: its words at byte `o` of leaf `i`, the reader's
cursor, its stack. -/
theorem Geo.call_same (G : Geo m0 bp B) {i o sz : Nat} {s m2 : MachineData} (hfr : Frm m0 s)
    (hs : SameOutside s.dmem m2.dmem (InAny [⟨leaf m0 i + BitVec.ofNat 64 o, sz⟩,
      curRegion (rdr m0), stackR s readerWordsStack])) :
    SameOutside s.dmem m2.dmem fun q ↦ InRange (leaf m0 i + BitVec.ofNat 64 o) sz q ∨
      InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨ InRange (base m0 144) 32 q := by
  refine NativeRustcVm.SameOutside.mono hs fun q ⟨r, hr, h⟩ ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ?_)
    have := Ring.stackBelow_eq (m0 := m0) (F := 112) hfr.sp (N' := readerWordsStack)
      (by have := G.g.st.2.1; unfold readerWordsStack readerLeStack; omega)
    exact this ▸ h

/-- A byte of the leaves outside the call's words is kept by the call. -/
theorem Geo.call_keep_W (G : Geo m0 bp B) {i o sz : Nat} {q : BitVec 64} (hW : W m0 q)
    (hq : ¬InRange (leaf m0 i + BitVec.ofNat 64 o) sz q) :
    ¬(InRange (leaf m0 i + BitVec.ofNat 64 o) sz q ∨
      InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨ InRange (base m0 144) 32 q) := by
  rintro (h | h | h)
  · exact hq h
  · exact G.g.wR q hW (NativeRustcVm.InRange.of_sub (o := 16) (m := 8) h G.g.rNw (by omega))
  · exact G.g.wS q hW (inRange_prefix h (Ring.base_noWrap G.g.st.2.1) (by omega))

/-- A word of the frame is kept by a call of `Reader::words`. -/
theorem Geo.call_frame (G : Geo m0 bp B) {i o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    (hsz : 0 < sz) {d d' : Mem 64}
    (hs : SameOutside d d' fun q ↦ InRange (leaf m0 i + BitVec.ofNat 64 o) sz q ∨
      InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨ InRange (base m0 144) 32 q)
    {f : Nat} (hf : f + 8 ≤ 112) {w : UInt64} (h : WordAt d (base m0 112 + BitVec.ofNat 64 f) w) :
    WordAt d' (base m0 112 + BitVec.ofNat 64 f) w :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun j hj hq ↦ by
    rw [NativeRustcVm.length_wordBytes] at hj
    rw [NativeRustcVm.addr_add_add (base m0 112)] at hq
    have hst := G.g.st
    have hfs := frame_in_stack hst (o := f + j) (by omega)
    rcases hq with h | h | h
    · exact G.not_frame hi ho hsz (by omega) h
    · exact NativeRustcVm.Apart.not_inRange G.g.sr (Ring.base_noWrap hst.2.1) G.g.rNw hfs
        (NativeRustcVm.InRange.of_sub (o := 16) (m := 8) h G.g.rNw (by omega))
    · have hb := Ring.base_noWrap (m0 := m0) (F := 144) hst.2.1
      have hb' : (base m0 144).toNat + 32 ≤ 2 ^ 64 := by unfold NoWrap at hb; omega
      have hSP := hst.2.1
      have hlt := m0.regs.SP.toNat_lt
      rw [Sym.inRange_iff hb', Ring.base_toNat hst.2.1] at h
      rw [← Ring.base_add (F := 112) (N := 144) (by omega) hst.2.1, NativeRustcVm.addr_add_add,
        NativeRustcVm.toNat_add_ofNat (by rw [Ring.base_toNat hst.2.1]; omega),
        Ring.base_toNat hst.2.1] at h
      omega

/-- The leaves before leaf `i` are kept by a call of `Reader::words` into leaf `i`. -/
theorem Geo.call_leaves (G : Geo m0 bp B) {i o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    {d d' : Mem 64}
    (hs : SameOutside d d' fun q ↦ InRange (leaf m0 i + BitVec.ofNat 64 o) sz q ∨
      InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨ InRange (base m0 144) 32 q)
    {L : List (List K)} (hL : L.length = i) (hl : ∀ x ∈ L, x.length = lw m0)
    (h : LeavesAt d (lv m0) L) : LeavesAt d' (lv m0) L := by
  intro j hj
  have hx := h j hj
  have hlen := hl _ (List.getElem_mem hj)
  have := G.lvNw
  have h64 := G.lw64
  refine NativeRustcVm.BytesAt.of_sameOutside hx hs fun t ht hq ↦ ?_
  rw [NativeRustcVm.length_wordsBytes, List.length_map, hlen] at ht
  have hW : W m0 (lv m0 + BitVec.ofNat 64 (512 * j) + BitVec.ofNat 64 t) := by
    rw [NativeRustcVm.addr_add_add (lv m0) (512 * j) t]
    exact NativeRustcVm.inRange_add (by omega) (by omega)
  refine G.call_keep_W hW ?_ hq
  intro h
  rcases Nat.eq_zero_or_pos sz with rfl | hsz
  · exact absurd h (by unfold InRange; omega)
  have hlt := G.leaf_toNat (i := i) (o := o) (by omega)
  rw [NativeRustcVm.addr_add_add (lv m0) (512 * j) t,
    Sym.inRange_iff (show (leaf m0 i + BitVec.ofNat 64 o).toNat + sz ≤ 2 ^ 64 by rw [hlt]; omega),
    hlt, NativeRustcVm.toNat_add_ofNat (by omega)] at h
  omega

/-- The zeros before byte `o` of leaf `i` are kept by a call of `Reader::words` there. -/
theorem Geo.call_zeros (G : Geo m0 bp B) {i o sz t : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    (hto : 8 * t ≤ o) {d d' : Mem 64}
    (hs : SameOutside d d' fun q ↦ InRange (leaf m0 i + BitVec.ofNat 64 o) sz q ∨
      InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨ InRange (base m0 144) 32 q)
    (h : WordsAt d (leaf m0 i) (List.replicate t 0)) : WordsAt d' (leaf m0 i) (List.replicate t 0) :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun j hj ↦ by
    rw [NativeRustcVm.length_wordsBytes, List.length_replicate] at hj
    have := G.lvNw
    have hW : W m0 (leaf m0 i + BitVec.ofNat 64 j) := by
      rw [NativeRustcVm.addr_add_add]
      exact NativeRustcVm.inRange_add (by omega) (by omega)
    exact G.call_keep_W hW
      (NativeRustcVm.not_inRange_sub (G.leaf_noWrap hi) ho (by omega) (.inl (by omega)))

/-- **A padded leaf more.** -/
theorem leaves_snoc {d : Mem 64} {a : BitVec 64} {L : List (List K)} {x : List K}
    (h : LeavesAt d a L) (hx : WordsAt d (a + BitVec.ofNat 64 (512 * L.length)) (x.map K.lane)) :
    LeavesAt d a (L ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]; exact h j hj
  · rw [List.getElem_append_right (le_refl _)]; simpa using hx

theorem lane_eq_zero {x : K} : x.lane = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hx : x = K.ofLane x.lane := rfl
    rw [hx, h]
    rfl
  · intro h
    rw [h]
    exact lane_zero

/-- The flag after one more row. -/
theorem flag_snoc (rows : List (List K)) (x : List K) :
    flag (rows ++ [x]) = if x.getD 0 0 = 0 then flag rows else 0 := by
  have e : (∀ y ∈ rows ++ [x], y.getD 0 0 = 0) ↔ (∀ y ∈ rows, y.getD 0 0 = 0) ∧ x.getD 0 0 = 0 :=
    ⟨fun h ↦ ⟨fun y hy ↦ h y (List.mem_append_left _ hy), h x (List.mem_append_right _
      (List.mem_singleton_self x))⟩, fun ⟨h1, h2⟩ y hy ↦ by
      rcases List.mem_append.mp hy with hy | hy
      · exact h1 y hy
      · rw [List.mem_singleton.mp hy]; exact h2⟩
  unfold flag
  by_cases h : ∀ y ∈ rows, y.getD 0 0 = 0 <;> by_cases hx : x.getD 0 0 = 0
  · simp only [eq_true (e.mpr ⟨h, hx⟩), eq_true hx, eq_true h, ite_true]
  · simp only [eq_false fun h' ↦ hx (e.mp h').2, eq_false hx, ite_false]
  · simp only [eq_false fun h' ↦ h (e.mp h').1, eq_true hx, eq_false h, ite_true, ite_false]
  · simp only [eq_false fun h' ↦ hx (e.mp h').2, eq_false hx, ite_false]

end

end NativeRustcVmArm.Wire.RdRows
