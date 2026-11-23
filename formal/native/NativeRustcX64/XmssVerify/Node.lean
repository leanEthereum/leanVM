module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.XmssVerify.Calls

/-!
# `xmss_verify`: a Merkle node's hash (x86-64)

The calls of the inlined `node`/`th` of a path step, the same on both layers (blocks 10 to 14 on
the bottom layer, 20 to 24 on the top): from a new hasher at `184` (the frame's offsets),
`update` with the public parameter at `56`, `update` with the address at `24`, `memcpy` of the
hasher to `608`, `update` of the copy with the children at `88`, `finalize` of the copy to `184`
(`hashNode`). The blocks are arguments: those of the two layers keep the copy's pointer in
different registers (`H`) and set it in different blocks.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc

public section

variable [Labels] {w : Nat → UInt64} {m₀ : MachineData}

/-- The frame's bytes from `24` outside the hashers at `184 .. 952` are the same. -/
@[expose] def FrKeep (m₀ : MachineData) (d d' : DataMem) : Prop :=
  ∀ (x : Nat) (bs : List UInt8), 24 ≤ x → x + bs.length ≤ 5816 → (x + bs.length ≤ 184 ∨ 952 ≤ x) →
    BytesAt d (ad m₀ (fr + x)) bs → BytesAt d' (ad m₀ (fr + x)) bs

omit [Labels] in
theorem FrKeep.trans {d₁ d₂ d₃ : DataMem} (h₁ : FrKeep m₀ d₁ d₂) (h₂ : FrKeep m₀ d₂ d₃) :
    FrKeep m₀ d₁ d₃ := fun x bs hx hle hd hb => h₂ x bs hx hle hd (h₁ x bs hx hle hd hb)

omit [Labels] in
theorem FrKeep.of_all {d d' : DataMem}
    (h : ∀ {x : Nat} {bs : List UInt8}, 24 ≤ x → x + bs.length ≤ 5816 →
      BytesAt d (ad m₀ (fr + x)) bs → BytesAt d' (ad m₀ (fr + x)) bs) : FrKeep m₀ d d' :=
  fun _ _ hx hle _ hb => h hx hle hb

theorem FrKeep.of_call (P : Pre w m₀) {m : MachineData} {d d' : DataMem} {a n s : Nat}
    (hrsp : rspOf m = ad m₀ (fr + 16)) (hs : s ≤ fr + 16) (ha : 184 ≤ a) (ha' : a + n ≤ 952)
    (hsame : SameOutside d d' (CallR m₀ m a n s)) : FrKeep m₀ d d' :=
  fun _ _ hx hle hd hb => keep_callR P hrsp hs (by omega) hsame hb hle (by omega) (by omega)

omit [Labels] in
/-- A hasher's bytes kept. -/
theorem holds_keep {d d' : DataMem} {a : BitVec 64} {xs : List UInt8}
    (hh : Keccak.HasherHolds (bytesOf d a 344) xs) (hmap : Mapped d a 344)
    (hk : BytesAt d a (bytesOf d a 344) → BytesAt d' a (bytesOf d a 344)) :
    Keccak.HasherHolds (bytesOf d' a 344) xs := by
  have := (hk (bytesAt_bytesOf hmap)).bytesOf
  rw [length_bytesOf] at this
  rwa [this]

end

public section

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- A register a block set to a literal. -/
theorem toNat_lit {m : MachineData} {env : Env} {r : Reg64} {n : Nat}
    (h : reg m r = (Sym.lit n).eval env) (hn : n < 2 ^ 64) : (reg m r).toNat = n := by
  rw [h]
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- **A Merkle node's hash**: from blocks like blocks 10 to 14 from `j`, the hash of the public
parameter `pp` at `56`, the address `A` at `24` and the children `Ch` at `88`, at `184`; the
frame's bytes from `24` outside the hashers kept. -/
theorem hashNode (hupd : Spec (label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost)
    (hcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hfin : Spec (label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre FinalizePost) (P : Pre w m₀)
    {d10 d11 d12 d13 d14 : List Directive} {j : Nat} {k12 : List (Reg64 × Sym)} {H X : Reg64}
    {S10 S11 S12 S13 S14 : SState}
    (p10 : d10.IsInfixAt Host.prog j) (p11 : d11.IsInfixAt Host.prog (j + d10.length))
    (p12 : d12.IsInfixAt Host.prog (j + d10.length + d11.length))
    (p13 : d13.IsInfixAt Host.prog (j + d10.length + d11.length + d12.length))
    (p14 : d14.IsInfixAt Host.prog (j + d10.length + d11.length + d12.length + d13.length))
    (x10 : exec d10 (stF [(.r15, .ptr 0 184)]) = some (S10, .call NativeRustcX64.Common.Update.entryLabel))
    (f10 : (writesBelow S10 [(0, 24)] = true ∧ keepsBut X (stF [(.r15, .ptr 0 184)]) S10 = true ∧
      S10.reg .rsp = some (.ptr 0 16)) ∧ S10.reg .rdi = some (.ptr 0 184) ∧
      S10.reg .rsi = some (.ptr 0 56) ∧ S10.reg .rdx = some (.lit 16))
    (x11 : exec d11 (stF [(.r15, .ptr 0 184)]) = some (S11, .call NativeRustcX64.Common.Update.entryLabel))
    (f11 : (writesBelow S11 [(0, 24)] = true ∧ keepsBut X (stF [(.r15, .ptr 0 184)]) S11 = true ∧
      S11.reg .rsp = some (.ptr 0 16)) ∧ S11.reg .rdi = some (.ptr 0 184) ∧
      S11.reg .rsi = some (.ptr 0 24) ∧ S11.reg .rdx = some (.lit 16))
    (x12 : exec d12 (stF k12) = some (S12, .call NativeRustcX64.Common.Memcpy.entryLabel))
    (f12 : (writesBelow S12 [(0, 24)] = true ∧ keepsBut X (stF k12) S12 = true ∧
      S12.reg .rsp = some (.ptr 0 16)) ∧ S12.reg .rdi = some (.ptr 0 608) ∧
      S12.reg .rsi = some (.ptr 0 184) ∧ S12.reg .rdx = some (.lit 344) ∧
      S12.reg .r15 = some (.ptr 0 184) ∧ S12.reg H = some (.ptr 0 608))
    (x13 : exec d13 (stF [(.r15, .ptr 0 184), (H, .ptr 0 608)]) = some (S13, .call NativeRustcX64.Common.Update.entryLabel))
    (f13 : (writesBelow S13 [(0, 24)] = true ∧
      keepsBut X (stF [(.r15, .ptr 0 184), (H, .ptr 0 608)]) S13 = true ∧
      S13.reg .rsp = some (.ptr 0 16)) ∧ S13.reg .rdi = some (.ptr 0 608) ∧
      S13.reg .rsi = some (.ptr 0 88) ∧ S13.reg .rdx = some (.lit 32) ∧
      S13.reg H = some (.ptr 0 608))
    (x14 : exec d14 (stF [(.r15, .ptr 0 184), (H, .ptr 0 608)]) =
      some (S14, .call NativeRustcX64.Common.Finalize.entryLabel))
    (f14 : (writesBelow S14 [(0, 24)] = true ∧
      keepsBut X (stF [(.r15, .ptr 0 184), (H, .ptr 0 608)]) S14 = true ∧
      S14.reg .rsp = some (.ptr 0 16)) ∧ S14.reg .rdi = some (.ptr 0 184) ∧
      S14.reg .rsi = some (.ptr 0 608))
    (hH : calleeSaved H = true) (hX : X ≠ .r15) {st : MachineState} (hpc : st.pc = Host.addrOf j)
    (C : Common m₀ st.data) (hrsp : rspOf st.data = ad m₀ (fr + 24))
    (hr15 : reg st.data .r15 = ad m₀ (fr + 184))
    (hk12 : ∀ (m : MachineData) (ret : BitVec 64), SavedBut X st.data m →
      AllOf (fun p => reg m p.1 = p.2.eval (Env.ofMachine m (frameRs m₀) (fun _ => 0) ret)) k12)
    {pp A Ch : List UInt8} (hlp : pp.length = 16) (hlA : A.length = 16) (hlC : Ch.length = 32)
    (hh : Keccak.HasherHolds (bytesOf st.data.dmem (ad m₀ (fr + 184)) 344) [])
    (hpp : BytesAt st.data.dmem (ad m₀ (fr + 56)) pp)
    (hA : BytesAt st.data.dmem (ad m₀ (fr + 24)) A)
    (hC : BytesAt st.data.dmem (ad m₀ (fr + 88)) Ch) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState,
      st'.pc = Host.addrOf (j + d10.length + d11.length + d12.length + d13.length + d14.length) →
      rspOf st'.data = ad m₀ (fr + 24) → Common m₀ st'.data → SavedBut X st.data st'.data →
      BytesAt st'.data.dmem (ad m₀ (fr + 184)) (Keccak.hashBytes (pp ++ A ++ Ch)) →
      FrKeep m₀ st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨g10, a0, a1, a2⟩ := f10
  obtain ⟨g11, b0, b1, b2⟩ := f11
  obtain ⟨g12, c0, c1, c2, c15, cH⟩ := f12
  obtain ⟨g13, e0, e1, e2, eH⟩ := f13
  obtain ⟨g14, i0, i1⟩ := f14
  have hmap : ∀ {m : MachineData} {o : Nat}, Common m₀ m → o + 344 ≤ 5816 →
      Mapped m.dmem (ad m₀ (fr + o)) 344 := fun C' ho => C'.mapped P (by fro)
  -- Block 10 and `update` with the public parameter.
  refine callBlock P p10 x10 g10 hpc C hrsp ⟨hr15.trans (eval_ptr0 184).symm, trivial⟩
    fun s1 hpc1 hrsp1 C1 hs1 hk1 hr1 => ?_
  have hh1 := holds_keep hh (hmap C (by omega)) fun hb => hk1 (by omega) (by rw [length_bytesOf]; omega) hb
  refine updateCall hupd P hpc1 C1 hrsp1 (h := 184) (d := 56) ((hr1 _ _ a0).trans (eval_ptr0 _))
    ((hr1 _ _ a1).trans (eval_ptr0 _)) (by rw [hlp]; exact toNat_lit (hr1 _ _ a2) (by decide))
    hh1 (hk1 (by omega) (by omega) hpp) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) fun s2 hpc2 hrsp2 C2 hs2 hh2 hsm2 => ?_
  have K2 : FrKeep m₀ st.data.dmem s2.data.dmem :=
    (FrKeep.of_all hk1).trans (FrKeep.of_call P hrsp1 (by decide) le_rfl (by omega) hsm2)
  have S2 := hs1.trans (Saved.savedBut hs2)
  -- Block 11 and `update` with the address.
  refine callBlock P p11 x11 g11 hpc2 C2 hrsp2
    ⟨((S2 .r15 rfl hX.symm).trans hr15).trans (eval_ptr0 184).symm, trivial⟩
    fun s3 hpc3 hrsp3 C3 hs3 hk3 hr3 => ?_
  have hh3 := holds_keep hh2 (hmap C2 (by omega)) fun hb => hk3 (by omega) (by rw [length_bytesOf]; omega) hb
  refine updateCall hupd P hpc3 C3 hrsp3 (h := 184) (d := 24) ((hr3 _ _ b0).trans (eval_ptr0 _))
    ((hr3 _ _ b1).trans (eval_ptr0 _)) (by rw [hlA]; exact toNat_lit (hr3 _ _ b2) (by decide))
    hh3 (hk3 le_rfl (by omega) (K2 _ _ le_rfl (by omega) (by omega) hA))
    (by omega) (by omega) le_rfl (by omega) (by omega) (by omega)
    fun s4 hpc4 hrsp4 C4 hs4 hh4 hsm4 => ?_
  have K4 : FrKeep m₀ st.data.dmem s4.data.dmem :=
    K2.trans ((FrKeep.of_all hk3).trans (FrKeep.of_call P hrsp3 (by decide) le_rfl (by omega)
      hsm4))
  have S4 := S2.trans (hs3.trans (Saved.savedBut hs4))
  -- Block 12 and `memcpy` of the hasher.
  refine callBlock P p12 x12 g12 hpc4 C4 hrsp4 (hk12 _ _ S4)
    fun s5 hpc5 hrsp5 C5 hs5 hk5 hr5 => ?_
  have hh5 := holds_keep hh4 (hmap C4 (by omega)) fun hb => hk5 (by omega) (by rw [length_bytesOf]; omega) hb
  refine memcpyCall hcpy P hpc5 C5 hrsp5 (dst := 608) (src := 184)
    ((hr5 _ _ c0).trans (eval_ptr0 _)) ((hr5 _ _ c1).trans (eval_ptr0 _))
    (toNat_lit (hr5 _ _ c2) (by decide)) (by omega) (by omega) (by omega) (by omega) (by omega)
    fun s6 hpc6 hrsp6 C6 hs6 hb6 hsm6 => ?_
  have hh6 : Keccak.HasherHolds (bytesOf s6.data.dmem (ad m₀ (fr + 608)) 344) (pp ++ A) := by
    have := hb6.bytesOf
    rw [length_bytesOf] at this
    rwa [this]
  have K6 : FrKeep m₀ st.data.dmem s6.data.dmem :=
    K4.trans ((FrKeep.of_all hk5).trans (FrKeep.of_call P hrsp5 (by decide) (by omega)
      (by omega) hsm6))
  have r15₆ : reg s6.data .r15 = ad m₀ (fr + 184) :=
    (hs6.1 .r15 rfl).trans ((hr5 _ _ c15).trans (eval_ptr0 _))
  have H₆ : reg s6.data H = ad m₀ (fr + 608) :=
    (hs6.1 H hH).trans ((hr5 _ _ cH).trans (eval_ptr0 _))
  -- Block 13 and `update` of the copy with the children.
  refine callBlock P p13 x13 g13 hpc6 C6 hrsp6
    ⟨r15₆.trans (eval_ptr0 184).symm, H₆.trans (eval_ptr0 608).symm, trivial⟩
    fun s7 hpc7 hrsp7 C7 hs7 hk7 hr7 => ?_
  have hh7 := holds_keep hh6 (hmap C6 (by omega)) fun hb => hk7 (by omega) (by rw [length_bytesOf]; omega) hb
  refine updateCall hupd P hpc7 C7 hrsp7 (h := 608) (d := 88) ((hr7 _ _ e0).trans (eval_ptr0 _))
    ((hr7 _ _ e1).trans (eval_ptr0 _)) (by rw [hlC]; exact toNat_lit (hr7 _ _ e2) (by decide))
    hh7 (hk7 (by omega) (by omega) (K6 _ _ (by omega) (by omega) (by omega) hC))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    fun s8 hpc8 hrsp8 C8 hs8 hh8 hsm8 => ?_
  have K8 : FrKeep m₀ st.data.dmem s8.data.dmem :=
    K6.trans ((FrKeep.of_all hk7).trans (FrKeep.of_call P hrsp7 (by decide) (by omega)
      (by omega) hsm8))
  have S8 := hs7.trans (Saved.savedBut hs8)
  have r15₈ : reg s8.data .r15 = ad m₀ (fr + 184) := (S8 .r15 rfl hX.symm).trans r15₆
  have H₈ : reg s8.data H = ad m₀ (fr + 608) :=
    (hs8.1 H hH).trans ((hr7 _ _ eH).trans (eval_ptr0 _))
  -- Block 14 and `finalize` of the copy.
  refine callBlock P p14 x14 g14 hpc8 C8 hrsp8
    ⟨r15₈.trans (eval_ptr0 184).symm, H₈.trans (eval_ptr0 608).symm, trivial⟩
    fun s9 hpc9 hrsp9 C9 hs9 hk9 hr9 => ?_
  have hh9 := holds_keep hh8 (hmap C8 (by omega)) fun hb => hk9 (by omega) (by rw [length_bytesOf]; omega) hb
  refine finalizeCall hfin P hpc9 C9 hrsp9 (o := 184) (h := 608)
    ((hr9 _ _ i0).trans (eval_ptr0 _)) ((hr9 _ _ i1).trans (eval_ptr0 _)) hh9 (by omega)
    (by omega) (by omega) (by omega) (by omega) fun s10 hpc10 hrsp10 C10 hs10 hb10 hsm10 => ?_
  refine cont s10 hpc10 hrsp10 C10
    (S4.trans (hs5.trans ((Saved.savedBut hs6).trans (S8.trans (hs9.trans (Saved.savedBut hs10))))))
    (by simpa only [List.append_assoc] using hb10) ?_
  exact K8.trans ((FrKeep.of_all hk9).trans (FrKeep.of_call P hrsp9 (by decide) le_rfl
    (by omega) hsm10))

end

end NativeRustcX64.Xmss.XmssVerify
