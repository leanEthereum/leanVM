module

public import NativeRustcX64.XmssVerify.Callee
public import NativeRustcX64.XmssVerify.Exec
public import NativeRustcX64.Got

/-!
# `xmss_verify`: the prologue (x86-64)

Block 0 from the entry: the callee-saved registers pushed, the frame allocated (with a stack
probe), `memset(frame + 932, 0, 2400)`; block 1: the input's words 0 to 3 into registers, words 4
to 7 (the message) to the frame at `152`, word 8 into R13 and its `u32` to RBP and `952`; to the
head of the loop copying the signature's words (`LoopAt` before its first turn). One environment
per block: block 0 uses region 0 for the frame and regions 1 and 2 for the ordinary-memory
`memcpy` and `memset` GOT slots; block 1 uses region 0 for the frame and region 1 for the input.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

set_option Elab.async false

@[expose] public section

/-- A word's `u32` zero-extended. -/
def u32W (x : UInt64) : BitVec 64 := (x.toBitVec.setWidth 32).setWidth 64

/-- At the head of the loop copying the signature's words, before turn `t` (R15 `6 t`). -/
structure LoopAt (w : Nat → UInt64) (m₀ m : MachineData) (t : Nat) : Prop where
  common : Common m₀ m
  rsp : rspOf m = ad m₀ (fr + 24)
  r14 : reg m .r14 = reg m₀ .rdi
  r15 : reg m .r15 = BitVec.ofNat 64 (6 * t)
  rax : reg m .rax = (w 0).toBitVec
  rcx : reg m .rcx = (w 1).toBitVec
  rdx : reg m .rdx = (w 2).toBitVec
  rsi : reg m .rsi = (w 3).toBitVec
  r13 : reg m .r13 = (w 8).toBitVec
  rbx : reg m .rbx = ad m₀ (fr + 956)
  msg : ∀ k < 4, BytesAt m.dmem (ad m₀ (fr + 152 + 8 * k)) (wordBytes (w (4 + k)))
  rbp : reg m .rbp = u32W (w 8)
  li : BytesAt m.dmem (ad m₀ (fr + 952)) ((wordBytes (w 8)).take 4)
  sig : ∀ k < 6 * t, BytesAt m.dmem (ad m₀ (fr + 956 + 8 * k)) (wordBytes (w (9 + k)))

end

public section

/-! ## The blocks' results -/

theorem st0'_facts : (after b0 st0).reg .rdi = some (.ptr 0 956) ∧
    (after b0 st0).reg .rdx = some (.lit 2400) ∧ (after b0 st0).reg .rsp = some (.ptr 0 16) ∧
    (after b0 st0).reg .r14 = some (.reg .rdi) ∧ (after b0 st0).reg .r15 = some (.lit 0) ∧
    (after b0 st0).reg .rbx = some (.ptr 0 956) ∧
    writesBelow (after b0 st0) [(0, 5808)] = true := by decide +kernel

theorem st0'_save : ∀ j < 6, ∀ t < 8,
    findWrite 0 (5760 + 8 * j + t) (after b0 st0).mem = some (.reg (saveRegs.getD j .rax), t) := by
  decide +kernel

theorem st1'_facts : (after b1 st1).reg .rax = some (.load 1 0 8) ∧
    (after b1 st1).reg .rcx = some (.load 1 8 8) ∧ (after b1 st1).reg .rdx = some (.load 1 16 8) ∧
    (after b1 st1).reg .rsi = some (.load 1 24 8) ∧ (after b1 st1).reg .r13 = some (.load 1 64 8) ∧
    (after b1 st1).reg .rsp = some (.ptr 0 24) ∧ (after b1 st1).reg .r14 = some (.ptr 1 (-1024)) ∧
    (after b1 st1).reg .r15 = some (.reg .r15) ∧
    (after b1 st1).reg .rbx = some (.reg .rbx) ∧
    writesBelow (after b1 st1) [(0, 5760)] = true := by decide +kernel

theorem st1'_msg : ∀ k < 4, ∀ t < 8,
    findWrite 0 (152 + 8 * k + t) (after b1 st1).mem = some (.load 1 (8 * (4 + k)) 8, t) := by
  decide +kernel

theorem st1'_rbp :
    (after b1 st1).reg .rbp = some (.un .trunc .W32 (.load 1 64 8)) := by decide +kernel

theorem st1'_li : ∀ t < 4,
    findWrite 0 (952 + t) (after b1 st1).mem = some (.un .trunc .W32 (.load 1 64 8), t) := by
  decide +kernel

/-! ## Environments -/

variable [Labels] {w : Nat → UInt64} {m₀ : MachineData}

/-- The frame region as an environment's region. -/
abbrev frR (m₀ : MachineData) : BitVec 64 × Nat := (ad m₀ fr, 5816)

theorem frame_wf (P : Pre w m₀) {m : MachineData} (hk : Kept m₀.dmem m.dmem)
    {vs : Nat → BitVec 64} {ret : BitVec 64} : (Env.ofMachine m [frR m₀] vs ret).WF :=
  Env.wf_of ⟨⟨(P.mapped.sub (i := fr) (k := 5816) (by fro)).kept hk, P.ad_nw (by fro)⟩, trivial⟩
    (List.pairwise_singleton _ _)

/-- The frame region and the input words as an environment's regions. -/
abbrev inR (m₀ : MachineData) : List (BitVec 64 × Nat) := [frR m₀, (inp m₀, 2472)]

theorem in_wf (P : Pre w m₀) {m : MachineData} (hk : Kept m₀.dmem m.dmem)
    {vs : Nat → BitVec 64} {ret : BitVec 64} : (Env.ofMachine m (inR m₀) vs ret).WF :=
  Env.wf_of ⟨⟨(P.mapped.sub (i := fr) (k := 5816) (by fro)).kept hk, P.ad_nw (by fro)⟩,
      ⟨P.inpMapped.kept hk, P.inpNW⟩, trivial⟩
    (List.pairwise_pair.mpr (by
      have := P.inp_apart (i := 0) (n := 2472) (o := fr) (s := 5816) (by omega) (by fro)
        (by omega) (by omega)
      simpa using this.symm))

omit [Labels] in
theorem inp_eq (m₀ : MachineData) : inp m₀ + BitVec.ofInt 64 (-1024) = reg m₀ .rdi := by
  unfold inp xmssInput
  rw [BitVec.add_assoc, show BitVec.ofNat 64 1024 + BitVec.ofInt 64 (-1024) = 0 by decide]
  exact BitVec.add_zero _

omit [Labels] in
theorem ad_int (m₀ : MachineData) (q : Nat) :
    ad m₀ fr + BitVec.ofInt 64 (q : Int) = ad m₀ (fr + q) := by
  rw [BitVec.ofInt_natCast, ad_add]

/-- One environment includes the frame and both loader-provided slots. -/
abbrev frameRs (m₀ : MachineData) : List (BitVec 64 × Nat) :=
  [frR m₀, (gotAddr "memcpy", 8), (gotAddr "memset", 8)]

theorem frameG_wf (P : Pre w m₀) {m : MachineData} (hk : Kept m₀.dmem m.dmem)
    {vs : Nat → BitVec 64} {ret : BitVec 64} : (Env.ofMachine m (frameRs m₀) vs ret).WF := by
  have hc := P.got.1 "memcpy" (by simp)
  have hs := P.got.1 "memset" (by simp)
  exact Env.wf_of
    ⟨⟨(P.mapped.sub (i := fr) (k := 5816) (by fro)).kept hk, P.ad_nw (by fro)⟩,
      ⟨(P.got.mapped (by simp)).kept hk, hc.2.1⟩,
      ⟨(P.got.mapped (by simp)).kept hk, hs.2.1⟩, trivial⟩
    (pairwise3 (got_apart P (by simp) (by fro) (by change 0 < 5816; decide)).symm
      (got_apart P (by simp) (by fro) (by change 0 < 5816; decide)).symm
      (by simpa using P.got.2))

theorem got_byte (P : Pre w m₀) {m : MachineData}
    (hs : SameOutside m₀.dmem m.dmem (InRange (lo m₀) 9248))
    {l : Label} (hl : l ∈ ["memcpy", "memset"]) {i : Nat} (hi : i < 8) :
    m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      some (byteOf (Labels.label l).toBitVec i) := by
  have hg := P.got.1 l hl
  rw [hs _ (fun hin => not_inRange_of_apart P.loNW
    ((hg.2.2.1.sub_left hg.2.1 (by omega) (by omega)).symm) (P.lo_mono hin))]
  exact P.got.byte hl hi

theorem match_stG (P : Pre w m₀) {m : MachineData}
    (hs : SameOutside m₀.dmem m.dmem (InRange (lo m₀) 9248))
    {ret : BitVec 64} {sp : Nat} {known : List (Reg64 × Sym)}
    (hsp : rspOf m = ad m₀ (fr + sp))
    (hk : AllOf (fun p => reg m p.1 =
      p.2.eval (Env.ofMachine m (frameRs m₀) (fun _ => 0) ret)) known) :
    Match (Env.ofMachine m (frameRs m₀) (fun _ => 0) ret) (stG sp known) m := by
  apply Match.withKnownBytes
  · apply Match.withKnownBytes
    · apply match_ofMachine
      · exact ⟨rfl, rfl, rfl, trivial⟩
      · exact ⟨hsp.trans (ad_int m₀ sp).symm, hk⟩
      · exact trivial
      · exact trivial
      · exact ⟨by simp [Sym.eval, Env.base, frameRs, gotAddr],
          by simp [Sym.eval, Env.base, frameRs, gotAddr], trivial⟩
    · intro i hi
      simpa [Sym.eval, Env.base, frameRs] using got_byte P hs (by simp : "memcpy" ∈ _) hi
  · intro i hi
    simpa [Sym.eval, Env.base, frameRs] using got_byte P hs (by simp : "memset" ∈ _) hi

omit [Labels] in
theorem sp_eq (m₀ : MachineData) : ad m₀ (fr + 5808) = rspOf m₀ := by
  unfold ad lo stackBelow
  rw [show BitVec.ofNat 64 (fr + 5808) = BitVec.ofNat 64 xmssVerifyStack from rfl,
    BitVec.sub_add_cancel]

omit [Labels] in
/-- Byte `t < 4` of a word's `u32` is the word's. -/
theorem byteOf_u32 (x : UInt64) {t : Nat} (ht : t < 4) :
    byteOf (BitVec.setWidth 64 (BitVec.setWidth Width.W32.bits x.toBitVec)) t =
      (wordBytes x).getD t 0 := by
  rw [← regBytes_eq_wordBytes]
  simp only [regBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show t < 8 by omega), Option.map_some, Option.getD_some]
  apply UInt8.toNat_inj.mp
  simp only [byteOf, UInt8.toNat_ofNat', BitVec.toNat_setWidth,
    show Width.W32.bits = 32 from rfl]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · simp [hj, show j + 8 * t < 32 by omega, show j + 8 * t < 64 by omega]
  · simp [hj]

/-- A register a block loaded from an input word is the word. -/
theorem load_word (P : Pre w m₀) {env : Env}
    (hmem : SameOutside m₀.dmem env.mem0 (InRange (lo m₀) 9248)) {rs os i : Nat} (hi : i < 309)
    (hbs : env.base rs + BitVec.ofNat 64 os = inp m₀ + BitVec.ofNat 64 (8 * i)) :
    env.load rs os 8 = (w i).toBitVec := by
  rw [Env.load_of_bytesAt (bs := wordBytes (w i)) (NativeRustc.length_wordBytes _)
    (by rw [hbs]; exact P.words_at hmem hi), ← UInt64.toBitVec_ofBitVec (w i).toBitVec,
    show UInt64.ofBitVec (w i).toBitVec = w i from rfl, ← regBytes_eq_wordBytes, ofBytes_regBytes]

/-- A word of the input copied by a block: the input word's bytes. -/
theorem copy_word (P : Pre w m₀) {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {rd od rs os : Nat} {bd : BitVec 64} {szd : Nat}
    (hbd : env.regions[rd]? = some (bd, szd)) (hle : od + 8 ≤ szd) {i : Nat} (hi : i < 309)
    (hbs : ∀ t < 8, env.base rs + BitVec.ofNat 64 (os + t) =
      inp m₀ + BitVec.ofNat 64 (8 * i + t))
    (hmem : SameOutside m₀.dmem env.mem0 (InRange (lo m₀) 9248))
    (hf : ∀ t < 8, findWrite rd (od + t) S.mem = some (.load rs os 8, t)) :
    BytesAt m.dmem (bd + BitVec.ofNat 64 od) (wordBytes (w i)) := by
  intro t ht
  rw [NativeRustc.length_wordBytes] at ht
  rw [addr_add_addr, hm.get?_load hbd (by omega) (hf t ht) ht (le_refl 8), hbs t ht,
    ← addr_add_addr, P.words_at hmem hi t (by rw [NativeRustc.length_wordBytes]; exact ht)]
  rfl

/-- Bytes of the frame region from `B` on are kept by a block writing the frame region only
below `B`. -/
theorem frame_keep (P : Pre w m₀) {m m' : MachineData} {N : Nat} {rest : List (BitVec 64 × Nat)}
    {vs : Nat → BitVec 64} {ret : BitVec 64} {S' : SState}
    (hwf : (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret).WF)
    (hm : Match (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) S' m') {B : Nat}
    (hw : writesBelow S' [(0, B)] = true) {x : Nat} {bs : List UInt8}
    (hb : BytesAt m.dmem (ad m₀ (fr + x)) bs) (hx : B ≤ x) (hle : x + bs.length ≤ 5816) :
    BytesAt m'.dmem (ad m₀ (fr + x)) bs := by
  refine hb.sameOutside (hm.sameOutside_below hwf hw) fun t ht => ?_
  rintro ⟨rb, hrb, b, sz, hb', hin⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
  subst hrb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  rw [ad_add, Nat.add_assoc] at hin
  exact P.not_inRange_ad (by fro) (by fro) (by omega) hin

/-- Bytes of the frame region in `[L, H)` are kept by a block writing the frame region only
below `L` or from `H`. -/
theorem frame_keep2 (P : Pre w m₀) {m m' : MachineData} {vs : Nat → BitVec 64} {ret : BitVec 64}
    {N : Nat} {rest : List (BitVec 64 × Nat)} {S' : SState}
    (hwf : (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret).WF)
    (hm : Match (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) S' m') {L H : Nat}
    (hw : ∀ w ∈ S'.mem, w.r = 0 ∧ (w.off + w.n ≤ L ∨ H ≤ w.off)) {x : Nat} {bs : List UInt8}
    (hb : BytesAt m.dmem (ad m₀ (fr + x)) bs) (hx : L ≤ x) (hxe : x + bs.length ≤ H)
    (hle : x + bs.length ≤ 5816) : BytesAt m'.dmem (ad m₀ (fr + x)) bs := by
  intro t ht
  rw [hm.get?_mem0 hwf ?_]
  · exact hb t ht
  rintro ⟨w', hw', b, sz, hb', h1, h2⟩
  obtain ⟨hr, hoff⟩ := hw w' hw'
  rw [hr] at hb'
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  rw [ad_add, P.ad_toNat (by fro), P.ad_toNat (by fro)] at h1 h2
  omega

/-- **A block keeps `Common`** when it writes only the frame region below the pushed
registers. -/
theorem Common.block (P : Pre w m₀) {m m' : MachineData} (C : Common m₀ m) {N : Nat}
    {rest : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {ret : BitVec 64} {S' : SState}
    (hwf : (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret).WF)
    (hm : Match (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) S' m') {B : Nat}
    (hw : writesBelow S' [(0, B)] = true) (hB : B ≤ 5760 := by decide) : Common m₀ m' where
  save j hj := by
    refine (C.save j hj).sameOutside (hm.sameOutside_below hwf hw) fun t ht => ?_
    rintro ⟨rb, hrb, b, sz, hb, hin⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
    subst hrb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [length_regBytes] at ht
    rw [ad_add] at hin
    exact P.not_inRange_ad (by fro) (by fro) (by omega) hin
  same := (C.same.trans (hm.sameOutside_below hwf hw)).mono fun p hp =>
    hp.elim id fun ⟨rb, hrb, b, sz, hb, hin⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
      subst hrb
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact P.inRange_lo (by fro) hin
  kept := C.kept.trans (hm.kept hwf)

/-- The frame region's offset `q` as a symbolic pointer. -/
theorem eval_ptr0 {m : MachineData} {vs : Nat → BitVec 64} {ret : BitVec 64} {N : Nat}
    {rest : List (BitVec 64 × Nat)} (q : Nat) :
    (Sym.ptr 0 q).eval (Env.ofMachine m ((ad m₀ fr, N) :: rest) vs ret) = ad m₀ (fr + q) :=
  ad_int m₀ q

end

end NativeRustcX64.Xmss.XmssVerify
