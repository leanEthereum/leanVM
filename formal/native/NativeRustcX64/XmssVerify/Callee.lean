module

public import NativeRustcX64.XmssVerify.Inv

/-!
# `xmss_verify`: its callees' preconditions and what their postconditions keep (x86-64)

At a callee's entry RSP is the frame region's offset `q` (`16` for the calls from RSP `24`, `0`
for `wots_leaf`, its two stack arguments pushed): the stack below it (`stackBelow_at`) is the
stack's from `fr + q - n`; from `Common`, the callees' stack facts (`stackOk_at`, `rcAt_at`) and
a buffer of the frame's apart from a callee's stack (`apart_at`). `gotAt_at` transports the
unchanged loader slots to the callee's stack and buffers, retaining pairwise slot separation
and restricting the symbols to those the callee reads. The callees' preconditions
(`memsetPre`, `memcpyPre`, `updatePre`, `finalizePre`, `fromBytesPre`). `Common.call`: a call
that keeps the callee-saved registers and changes only bytes of the stack other than the pushed
registers keeps `Common`.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

/-- What a call with `n` bytes of output at the frame offset `a` and `s` bytes of stack below its
entry RSP may change. -/
@[expose] public def CallR (m₀ m : MachineData) (a n s : Nat) (p : BitVec 64) : Prop :=
  InRange (ad m₀ (fr + a)) n p ∨ InRange (stackBelow m s) s p

public section

variable [Labels] {w : Nat → UInt64} {m₀ m m' : MachineData}

theorem Common.mapped (P : Pre w m₀) (C : Common m₀ m) {o s : Nat} (h : o + s ≤ 9256) :
    Mapped m.dmem (ad m₀ o) s :=
  (P.mapped.sub h).kept C.kept

omit [Labels] in
/-- The stack below RSP at the frame region's offset `q`. -/
theorem stackBelow_at {q n : Nat} (h : rspOf m = ad m₀ (fr + q)) (hn : n ≤ fr + q) :
    stackBelow m n = ad m₀ (fr + q - n) := by
  have e : BitVec.ofNat 64 (fr + q) = BitVec.ofNat 64 (fr + q - n) + BitVec.ofNat 64 n := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hn]
  unfold stackBelow
  rw [h, ad, ad, e, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem rsp_toNat (P : Pre w m₀) {q : Nat} (h : rspOf m = ad m₀ (fr + q)) (hq : q < 5816) :
    (rspOf m).toNat = (lo m₀).toNat + fr + q := by
  rw [h, P.ad_toNat (by fro)]
  omega

theorem stackOk_at (P : Pre w m₀) (C : Common m₀ m) {q n : Nat} (h : rspOf m = ad m₀ (fr + q))
    (hq : q + 8 ≤ 5816) (hn : n ≤ fr + q) : StackOk m n := by
  have hr := rsp_toNat P h (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · rw [hr]
    have := P.loNW
    unfold NoWrap at this
    fro
  · rw [show rspOf m - BitVec.ofNat 64 n = stackBelow m n from rfl, stackBelow_at h hn]
    exact C.mapped P (by fro)

theorem apart_at (P : Pre w m₀) {q n o s : Nat} (h : rspOf m = ad m₀ (fr + q))
    (hn : n ≤ fr + q) (hk : fr + q + 8 ≤ 9256) (ho : fr + q + 8 ≤ o) (hs : o + s ≤ 9256)
    (hs0 : 0 < s) : Apart (ad m₀ o) s (stackBelow m n) (n + 8) := by
  rw [stackBelow_at h hn]
  exact P.apart_ad (by omega) hs (by omega) hs0 (by omega)

omit [Labels] in
theorem rcBytes_length : rcBytes.length = 192 := by
  rw [show rcBytes = Native.Keccak.wordsBytes LeanVM.Parameters.keccakRC from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  rfl

theorem rcAt_at (P : Pre w m₀) (C : Common m₀ m) {q n : Nat} (h : rspOf m = ad m₀ (fr + q))
    (hq : q + 8 ≤ 5816) (hn : n ≤ fr + q) : RcAt m n := by
  refine ⟨fun i hi => ?_, P.rcNW, ?_⟩
  · rw [rcBytes_length] at hi
    rw [C.same _ fun h' => P.rc_not_lo hi (P.lo_mono h')]
    exact P.rc i (by rw [rcBytes_length]; exact hi)
  · rw [stackBelow_at h hn]
    exact P.rc_apart (by fro) (by omega)

/-- GOT slots remain outside every frame slice. -/
theorem got_apart (P : Pre w m₀) {l : Label} (hl : l ∈ ["memcpy", "memset"])
    {o s : Nat} (ho : o + s ≤ 9256) (hs : 0 < s) :
    Apart (gotAddr l) 8 (ad m₀ o) s :=
  (P.got.1 l hl).2.2.1.sub_right P.loNW ho hs

/-- Calls read the entry's GOT bytes, which the frame invariant preserves. -/
theorem gotAt_at (P : Pre w m₀) (C : Common m₀ m) {q n : Nat}
    (h : rspOf m = ad m₀ (fr + q)) (hq : q + 8 ≤ 5816) (hn : n ≤ fr + q)
    {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (hl : symbols.Sublist ["memcpy", "memset"])
    (ha : ∀ l ∈ symbols, ∀ a ∈ areas, Apart (gotAddr l) 8 a.1 a.2) :
    GotAt m n areas symbols := by
  apply (P.got.symbols hl).transport
  · intro l hl' i hi
    have hg := P.got.1 l (hl.subset hl')
    apply C.same
    intro hin
    exact not_inRange_of_apart P.loNW
      ((hg.2.2.1.sub_left hg.2.1 (by omega) (by omega)).symm) (P.lo_mono hin)
  · intro l hl'
    change Apart (gotAddr l) 8 (stackBelow m n) (n + 8)
    rw [stackBelow_at h hn]
    exact got_apart P (hl.subset hl') (by fro) (by omega)
  · exact ha

/-! ## Preconditions -/

theorem memsetPre (P : Pre w m₀) (C : Common m₀ m) {q o n : Nat} (h : rspOf m = ad m₀ (fr + q))
    (hq : q + 8 ≤ 5816) (h0 : reg m .rdi = ad m₀ o) (h2 : (reg m .rdx).toNat = n)
    (ho : fr + q + 8 ≤ o) (h : o + n ≤ 9256) (hn : 0 < n) : MemsetPre m := by
  unfold MemsetPre
  rw [h0, h2]
  refine ⟨stackOk_at P C ‹_› hq (by omega), C.mapped P h, P.ad_nw h, ?_⟩
  rw [‹rspOf m = _›]
  exact P.apart_ad (by omega) h (by fro) hn (by omega)

theorem memcpyPre (P : Pre w m₀) (C : Common m₀ m) {q o o' n : Nat}
    (h : rspOf m = ad m₀ (fr + q)) (hq : q + 8 ≤ 5816) (h0 : reg m .rdi = ad m₀ o)
    (h1 : reg m .rsi = ad m₀ o') (h2 : (reg m .rdx).toNat = n) (ho : fr + q + 8 ≤ o)
    (hb : o + n ≤ 9256) (hb' : o' + n ≤ 9256) (hd : o + n ≤ o' ∨ o' + n ≤ o) (hn : 0 < n) :
    MemcpyPre m := by
  unfold MemcpyPre
  rw [h0, h1, h2]
  refine ⟨stackOk_at P C h hq (by omega), C.mapped P hb, C.mapped P hb', P.ad_nw hb,
    P.ad_nw hb', P.apart_ad hd hb hb' hn hn, ?_⟩
  rw [h]
  exact P.apart_ad (by omega) hb (by fro) hn (by omega)

/-! ## What a call keeps -/

omit [Labels] in
/-- **A call keeps `Common`** when it keeps the callee-saved registers and changes only bytes of
the stack outside the pushed registers. -/
theorem Common.call (C : Common m₀ m) (hs : Saved m m') {R : BitVec 64 → Prop}
    (hsame : SameOutside m.dmem m'.dmem R) (hR : ∀ p, R p → InRange (lo m₀) 9248 p)
    (hsave : ∀ x, fr + 5760 ≤ x → x < fr + 5808 → ¬R (ad m₀ x)) : Common m₀ m' where
  save j hj := (C.save j hj).sameOutside hsame fun t ht => by
    rw [ad_add]
    rw [length_regBytes] at ht
    exact hsave _ (by omega) (by omega)
  same := (C.same.trans hsame).mono fun p hp => hp.elim id (hR p)
  kept := C.kept.trans hs.2

omit [Labels] in
/-- Bytes of the stack a call does not change are kept. -/
theorem keep_ad {d d' : DataMem} {R : BitVec 64 → Prop} (hsame : SameOutside d d' R) {o : Nat}
    {bs : List UInt8} (h : BytesAt d (ad m₀ o) bs)
    (hR : ∀ t < bs.length, ¬R (ad m₀ (o + t))) : BytesAt d' (ad m₀ o) bs :=
  h.sameOutside hsame fun t ht => by rw [ad_add]; exact hR t ht

theorem not_callR (P : Pre w m₀) {q a n s x : Nat} (hrsp : rspOf m = ad m₀ (fr + q))
    (hs : s ≤ fr + q) (ha : a + n ≤ 5816) (hx : x < 5816) (hq : q ≤ x) (h : x < a ∨ a + n ≤ x) :
    ¬CallR m₀ m a n s (ad m₀ (fr + x)) := by
  rintro (hp | hp)
  · exact P.not_inRange_ad (by fro) (by fro) (by omega) hp
  · rw [stackBelow_at hrsp hs] at hp
    exact P.not_inRange_ad (by fro) (by fro) (by omega) hp

/-- **The frame's bytes a call keeps**: those from its entry RSP apart from its output. -/
theorem keep_callR (P : Pre w m₀) {q a n s : Nat} (hrsp : rspOf m = ad m₀ (fr + q))
    (hs : s ≤ fr + q) (ha : a + n ≤ 5816) {d d' : DataMem}
    (hsame : SameOutside d d' (CallR m₀ m a n s)) {x : Nat} {bs : List UInt8}
    (h : BytesAt d (ad m₀ (fr + x)) bs) (hx : x + bs.length ≤ 5816) (hq : q ≤ x)
    (h1 : x + bs.length ≤ a ∨ a + n ≤ x) : BytesAt d' (ad m₀ (fr + x)) bs :=
  keep_ad hsame h fun t ht => by
    rw [Nat.add_assoc]
    exact not_callR P hrsp hs ha (by omega) (by omega) (by omega)

/-- **`Common` after a call** with its output in the frame below the pushed registers. -/
theorem Common.callR (P : Pre w m₀) (C : Common m₀ m) (hs : Saved m m') {q a n s : Nat}
    (hrsp : rspOf m = ad m₀ (fr + q)) (hsq : s ≤ fr + q) (hq : q ≤ 5760) (ha : a + n ≤ 5760)
    (hsame : SameOutside m.dmem m'.dmem (CallR m₀ m a n s)) : Common m₀ m' :=
  C.call hs hsame
    (fun p hp => by
      rcases hp with hp | hp
      · exact P.inRange_lo (by fro) hp
      · rw [stackBelow_at hrsp hsq] at hp
        exact P.inRange_lo (by fro) hp)
    fun x hx hx' => by
      have := not_callR P (m := m) (a := a) (n := n) (s := s) (x := x - fr) hrsp hsq (by omega)
        (by fro) (by fro) (by fro)
      rwa [show fr + (x - fr) = x by omega] at this

end

end NativeRustcX64.Xmss.XmssVerify
