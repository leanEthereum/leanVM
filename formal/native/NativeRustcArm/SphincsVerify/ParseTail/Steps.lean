module

public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names

public import NativeRustcArm.SphincsVerify.ParseTail.Loop

/-!
# The parse's tail: a block, then its call, on `Facts`

`step_memcpy`: a straight block from `fs known` ending in `bl memcpy` between frame offsets takes
`Facts r m L K` to the facts the block adds (`Lnew`, `Knew`), the ones it keeps, and the bytes
`memcpy` copies. `step_fall`: a straight block falling through.
-/

namespace NativeRustcArm.SphincsVerifyProof.ParseTail

open NativeRustc NativeRustcArm.Sym

public section

theorem bytesOf_eq {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    bytesOf d a bs.length = bs := by
  apply List.ext_getElem (by simp [bytesOf])
  intro i h1 h2
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  rw [h i h2]
  rfl

theorem BytesL.append {r : Run} {d : DataMem} {L L' : List (Nat × Nat × List UInt8)}
    (h : BytesL r d L) (h' : BytesL r d L') : BytesL r d (L ++ L') :=
  allOf_append.mpr ⟨h, h'⟩

theorem RegsL.append {m : MachineData} {K K' : List (XReg × BitVec 64)} (h : RegsL m K)
    (h' : RegsL m K') : RegsL m (K ++ K') :=
  allOf_append.mpr ⟨h, h'⟩

theorem BytesL.mem {r : Run} {d : DataMem} {L : List (Nat × Nat × List UInt8)} (h : BytesL r d L)
    {o n : Nat} {bs : List UInt8} (hm : (o, n, bs) ∈ L) : bs.length = n ∧ BytesAt d (r.off o) bs :=
  allOf_iff.mp h _ hm

/-- **Forgetting facts.** -/
theorem Facts.weaken {r : Run} {m : MachineData} {L L' : List (Nat × Nat × List UInt8)}
    {K K' : List (XReg × BitVec 64)} (h : Facts r m L K) (hL : ∀ x ∈ L', x ∈ L)
    (hK : ∀ x ∈ K', x ∈ K) : Facts r m L' K' :=
  ⟨h.1, allOf_iff.mpr fun x hx ↦ allOf_iff.mp h.2.1 x (hL x hx),
    allOf_iff.mpr fun x hx ↦ allOf_iff.mp h.2.2 x (hK x hx)⟩

/-- No bytes at `a`. -/
theorem Facts.nil {r : Run} {m : MachineData} {L : List (Nat × Nat × List UInt8)}
    {K : List (XReg × BitVec 64)} (h : Facts r m L K) (a : Nat) : Facts r m ((a, 0, []) :: L) K :=
  ⟨h.1, ⟨⟨rfl, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩, h.2.1⟩, h.2.2⟩

/-- Forgetting the second bytes. -/
theorem Facts.drop1 {r : Run} {m : MachineData} {a b : Nat × Nat × List UInt8}
    {L : List (Nat × Nat × List UInt8)} {K : List (XReg × BitVec 64)}
    (h : Facts r m (a :: b :: L) K) : Facts r m (a :: L) K :=
  ⟨h.1, ⟨h.2.1.1, h.2.1.2.2⟩, h.2.2⟩

/-- Forgetting the third bytes. -/
theorem Facts.drop2 {r : Run} {m : MachineData} {a b c : Nat × Nat × List UInt8}
    {L : List (Nat × Nat × List UInt8)} {K : List (XReg × BitVec 64)}
    (h : Facts r m (a :: b :: c :: L) K) : Facts r m (a :: b :: L) K :=
  ⟨h.1, ⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.2⟩, h.2.2⟩

/-- Forgetting the first register. -/
theorem Facts.dropK {r : Run} {m : MachineData} {L : List (Nat × Nat × List UInt8)}
    {x : XReg × BitVec 64} {K : List (XReg × BitVec 64)} (h : Facts r m L (x :: K)) :
    Facts r m L K :=
  ⟨h.1, h.2.1, h.2.2.2⟩

/-- **Adjacent known bytes**, together. -/
theorem Facts.concat {r : Run} {m : MachineData} {L : List (Nat × Nat × List UInt8)}
    {K : List (XReg × BitVec 64)} (h : Facts r m L K) {o n n' : Nat} {xs ys : List UInt8}
    (hx : (o, n, xs) ∈ L) (hy : (o + n, n', ys) ∈ L) :
    Facts r m ((o, n + n', xs ++ ys) :: L) K := by
  obtain ⟨hxl, hxb⟩ := h.2.1.mem hx
  obtain ⟨hyl, hyb⟩ := h.2.1.mem hy
  refine ⟨h.1, ⟨⟨by simp [hxl, hyl], bytesAt_append hxb ?_⟩, h.2.1⟩, h.2.2⟩
  rw [hxl, Parse.off_add]
  exact hyb

/-- The first directive of a block placed at `j` is the function's `j`th. -/
theorem getElem?_of_infix {ds F : List Directive} {j : Nat} (h : ds.IsInfixAt F j) {d : Directive}
    (hd : ds[0]? = some d) : F[j]? = some d := by
  obtain ⟨t, ht⟩ := h
  have h1 : (F.drop j)[0]? = some d := by
    rw [← ht, List.getElem?_append_left (by
      cases ds with
      | nil => simp at hd
      | cons _ _ => simp)]
    exact hd
  simpa using h1

variable (r : Run) [ElfHost]

/-- **A block, then `memset`**, on facts. -/
theorem step_memset (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {known : List (XReg × Sym)} {S' : SState} (hx : exec ds (fs known) = some (S', .call NativeRustcArm.Common.Memset.entryLabel))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0)
    (h29 : S'.reg .X29 = some (.ptr 0 21520))
    {a n : Nat} (h0 : S'.reg .X0 = some (.ptr 0 a)) (h2 : S'.reg .X2 = some (.lit n))
    (ha : a + n ≤ 21520)
    {m : MachineData} {L : List (Nat × Nat × List UInt8)} {K : List (XReg × BitVec 64)}
    (h : Facts r m L K)
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (envSig r m)) known)
    (hLb : noW S' L = true) (hKb : keptK (fs known) S' K = true)
    {Knew : List (XReg × BitVec 64)} (hKn : ∀ m', Match (envSig r m) S' m' → RegsL m' Knew)
    (hLc : disj L a n = true) (hKc : savedK (Knew ++ K) = true) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc (j + ds.length) ∧
      Facts r st.data L (Knew ++ K)) ⟨m, r.pc j⟩ := by
  refine block_memset r hp hc hpre hk hx hw hsp h29 h0 h2 (by omega) ha h.1 hkn
    fun m' st' hm' hpc hF hS hout ↦ .done _ ⟨hpc, hF, ?_, ?_⟩
  · have hwf := envSig_wf r hpre h.1 (fun _ ↦ 0)
    exact BytesL.keep r hpre hout (by omega) hLc (BytesL.keep_block r hpre hm' hwf hw hLb h.2.1)
  · have hm0 := match_fs r hpre h.1 hkn
    exact RegsL.keep_call hS hKc ((hKn m' hm').append (RegsL.keep_block hm0 hm' hKb h.2.2))

/-- **A block, then `memcpy`**, on facts. -/
theorem step_memcpy (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j)
    {known : List (XReg × Sym)} {S' : SState} (hx : exec ds (fs known) = some (S', .call NativeRustcArm.Common.Memcpy.entryLabel))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0)
    (h29 : S'.reg .X29 = some (.ptr 0 21520))
    {a b n : Nat} (h0 : S'.reg .X0 = some (.ptr 0 a)) (h1 : S'.reg .X1 = some (.ptr 0 b))
    (h2 : S'.reg .X2 = some (.lit n)) (ha : a + n ≤ 21520) (hb : b + n ≤ 21616)
    (hab : a + n ≤ b ∨ b + n ≤ a)
    {m : MachineData} {L : List (Nat × Nat × List UInt8)} {K : List (XReg × BitVec 64)}
    (h : Facts r m L K)
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (envSig r m)) known)
    (hLb : noW S' L = true) (hKb : keptK (fs known) S' K = true)
    {Lnew : List (Nat × Nat × List UInt8)} (hLn : ∀ m', Match (envSig r m) S' m' → BytesL r m'.dmem Lnew)
    {Knew : List (XReg × BitVec 64)} (hKn : ∀ m', Match (envSig r m) S' m' → RegsL m' Knew)
    (hLc : disj (Lnew ++ L) a n = true) (hKc : savedK (Knew ++ K) = true)
    {bs : List UInt8} (hsrc : (b, n, bs) ∈ Lnew ++ L) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc (j + ds.length) ∧
      Facts r st.data ((a, n, bs) :: (Lnew ++ L)) (Knew ++ K)) ⟨m, r.pc j⟩ := by
  refine block_memcpy r hp hc hpre hk hx hw hsp h29 h0 h1 h2 (by omega) ha hb hab h.1 hkn
    fun m' st' hm' hpc hF hS hbytes hout ↦ .done _ ⟨hpc, hF, ?_, ?_⟩
  · have hwf := envSig_wf r hpre h.1 (fun _ ↦ 0)
    have hL' : BytesL r m'.dmem (Lnew ++ L) :=
      (hLn m' hm').append (BytesL.keep_block r hpre hm' hwf hw hLb h.2.1)
    obtain ⟨hl, hsb⟩ := hL'.mem hsrc
    rw [← hl, bytesOf_eq hsb] at hbytes
    exact ⟨⟨hl, hbytes⟩, BytesL.keep r hpre hout (by omega) hLc hL'⟩
  · have hm0 := match_fs r hpre h.1 hkn
    exact RegsL.keep_call hS hKc ((hKn m' hm').append (RegsL.keep_block hm0 hm' hKb h.2.2))

/-- **A block falling through**, on facts. -/
theorem step_fall (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hk : ds.IsInfixAt Sphincs.SphincsVerify.code j) (hne : ds ≠ [])
    {known : List (XReg × Sym)} {S' : SState} (hx : exec ds (fs known) = some (S', .fall))
    (hw : Run.frameWrites S' = true) (hsp : S'.sp = .ptr 0 0)
    (h29 : S'.reg .X29 = some (.ptr 0 21520))
    {m : MachineData} {L : List (Nat × Nat × List UInt8)} {K : List (XReg × BitVec 64)}
    (h : Facts r m L K)
    (hkn : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (envSig r m)) known)
    (hLb : noW S' L = true) (hKb : keptK (fs known) S' K = true)
    {Lnew : List (Nat × Nat × List UInt8)} (hLn : ∀ m', Match (envSig r m) S' m' → BytesL r m'.dmem Lnew)
    {Knew : List (XReg × BitVec 64)} (hKn : ∀ m', Match (envSig r m) S' m' → RegsL m' Knew) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc (j + ds.length) ∧
      Facts r st.data (Lnew ++ L) (Knew ++ K)) ⟨m, r.pc j⟩ := by
  refine block_fall r hp hpre hk hne hx hw hsp h29 h.1 hkn fun st hm' hpc hF ↦ .done _ ⟨hpc, hF, ?_, ?_⟩
  · have hwf := envSig_wf r hpre h.1 (fun _ ↦ 0)
    exact (hLn _ hm').append (BytesL.keep_block r hpre hm' hwf hw hLb h.2.1)
  · exact (hKn _ hm').append (RegsL.keep_block (match_fs r hpre h.1 hkn) hm' hKb h.2.2)

end

/-- **A segment of the tail**: from a state with `P` at the function's directive `j`, the machine
inevitably reaches directive `j'` in a state with `Q`. -/
@[expose] public def Seg [ElfHost] (r : Run) (j : Nat) (P : MachineData → Prop) (j' : Nat)
    (Q : MachineData → Prop) : Prop :=
  ∀ m, P m → Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc j' ∧ Q st.data) ⟨m, r.pc j⟩

/-- Segments one after the other. -/
public theorem Seg.trans [ElfHost] {r : Run} {j j' j'' : Nat} {P Q R : MachineData → Prop}
    (h1 : Seg r j P j' Q) (h2 : Seg r j' Q j'' R) : Seg r j P j'' R := fun m hm ↦
  Eventually.bind_elf (h1 m hm) fun st ⟨hpc, hq⟩ ↦ by
    obtain ⟨m', pc⟩ := st
    simp only at hpc
    subst hpc
    exact h2 m' hq

/-- Known bytes. -/
public theorem Facts.get {r : Run} {m : MachineData} {L : List (Nat × Nat × List UInt8)}
    {K : List (XReg × BitVec 64)} (h : Facts r m L K) {o n : Nat} {bs : List UInt8}
    (hm : (o, n, bs) ∈ L) : BytesAt m.dmem (r.off o) bs :=
  (h.2.1.mem hm).2

/-- A known register. -/
public theorem Facts.reg {r : Run} {m : MachineData} {L : List (Nat × Nat × List UInt8)}
    {K : List (XReg × BitVec 64)} (h : Facts r m L K) {x : XReg} {v : BitVec 64}
    (hx : (x, v) ∈ K) : (m.regs.getXReg x).toBitVec = v :=
  allOf_iff.mp h.2.2 _ hx

/-- **Forgetting or reordering registers.** -/
public theorem Facts.weakenK {r : Run} {m : MachineData} {L : List (Nat × Nat × List UInt8)}
    {K K' : List (XReg × BitVec 64)} (h : Facts r m L K) (hK : ∀ x ∈ K', x ∈ K) : Facts r m L K' :=
  h.weaken (fun _ hx ↦ hx) hK

end NativeRustcArm.SphincsVerifyProof.ParseTail
