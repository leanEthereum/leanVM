import Rv64Verifier.Proofs.Pcs.VsoTailB510

/-!
# `verify_stacked_opening`'s level tail: the next level's head

After the glue (`GlueOut`) and the branch (`b510`), the back edge (`BackOut`: the next root
written over the root, the head's registers loaded) reaches the next level's head
(`nextHead`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- At `0x8000a190`, from `z` at `0x8000b51c`: the next root `d` written. -/
structure BackOut (s z u : MachineState) (d : Digest) : Prop where
  pc : u.pc = 0x8000a190
  dig : digestAt u (s.getReg .x11) = d
  fr : DFrame z u fun a ↦ Within a (s.getReg .x11) 32 ∨ Within a (s.getReg .x2 - 784) 8 ∨
    Within a (s.getReg .x2 - 824) 8
  regs : ∀ q ∈ [Reg.x1, .x2, .x9, .x25, .x26], u.getReg q = z.getReg q
  x5 : u.getReg .x5 = z.getMem (s.getReg .x2 - 1008)
  x8 : u.getReg .x8 = 0xffffffffffffffff
  x10 : u.getReg .x10 = z.getMem (s.getReg .x2 - 864)
  x17 : u.getReg .x17 = 8
  x22 : u.getReg .x22 = z.getMem (s.getReg .x2 - 896)
  x23 : u.getReg .x23 = z.getMem (s.getReg .x2 - 808)
  x27 : u.getReg .x27 = z.getMem (s.getReg .x2 - 816)

/-- The fold rounds' folds and quadratic, the head's glued claims: where they lie. -/
structure Regions (s : MachineState) (x : LCtx) (h t : MachineState) : Prop where
  fb : (vecCap t (s.getReg .x2 - 688)).toNat * 24 = 0 ∨
    x.L ≤ (vecPtr t (s.getReg .x2 - 688)).toNat ∧
    (vecPtr t (s.getReg .x2 - 688)).toNat + (vecCap t (s.getReg .x2 - 688)).toNat * 24 ≤ heapNext t
  qb : (t.getReg .x23).toNat = 0 ∨ x.L ≤ (t.getReg .x22).toNat ∧
    (t.getReg .x22).toNat + 24 * (t.getReg .x23).toNat ≤ heapNext t
  gb : (vecCap h (s.getReg .x2 - 664)).toNat * 88 = 0 ∨
    x.L ≤ (vecPtr h (s.getReg .x2 - 664)).toNat ∧
    (vecPtr h (s.getReg .x2 - 664)).toNat + (vecCap h (s.getReg .x2 - 664)).toNat * 88 ≤ heapNext h
  fq : Apart (vecPtr t (s.getReg .x2 - 688)) ((vecCap t (s.getReg .x2 - 688)).toNat * 24)
    (t.getReg .x22) (24 * (t.getReg .x23).toNat)
  fg : Apart (vecPtr t (s.getReg .x2 - 688)) ((vecCap t (s.getReg .x2 - 688)).toNat * 24)
    (vecPtr h (s.getReg .x2 - 664)) ((vecCap h (s.getReg .x2 - 664)).toNat * 88)
  gq : Apart (vecPtr h (s.getReg .x2 - 664)) ((vecCap h (s.getReg .x2 - 664)).toNat * 88)
    (t.getReg .x22) (24 * (t.getReg .x23).toNat)
  old : ∀ i < (vecLen h (s.getReg .x2 - 664)).toNat, ∀ y, InBufs h (gAddr h s i) y →
    x.L ≤ y.toNat ∧ y.toNat < heapNext h ∧
    ¬ Within y (vecPtr t (s.getReg .x2 - 688)) ((vecCap t (s.getReg .x2 - 688)).toNat * 24) ∧
    ¬ Within y (vecPtr h (s.getReg .x2 - 664)) ((vecCap h (s.getReg .x2 - 664)).toNat * 88) ∧
    ¬ Within y (t.getReg .x22) (24 * (t.getReg .x23).toNat)

theorem Folded.regions {s : MachineState} {x : LCtx} {h t : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} (hf : Folded s x h t ℓ Wl lf q) :
    Regions s x h t := by
  have hh := hf.head
  have hF := hh.facts
  have hmo := hf.mono
  obtain ⟨hfv, -, hFF⟩ := hf.F
  have hfraw := hfv.raw
  simp only [RawVecOk, Buf] at hfraw
  obtain ⟨-, -, hQ⟩ := hf.Q
  have hhq := hh.quad.2.2
  obtain ⟨hgv, -, hglo⟩ := hh.glued
  have hgraw := hgv.raw
  simp only [RawVecOk, Buf] at hgraw
  have hap := hh.apart
  simp only [Apart] at hap
  have gb : (vecCap h (s.getReg .x2 - 664)).toNat * 88 = 0 ∨
      x.L ≤ (vecPtr h (s.getReg .x2 - 664)).toNat ∧
      (vecPtr h (s.getReg .x2 - 664)).toNat + (vecCap h (s.getReg .x2 - 664)).toNat * 88 ≤
        heapNext h := by
    rcases hgraw.2 with h0 | h0
    · exact Or.inl h0
    · rcases hglo with h1 | h1
      · exact Or.inl (by rw [h1]; rfl)
      · exact Or.inr ⟨h1, h0.2⟩
  have hfb := hF.F
  refine ⟨?_, ?_, gb, by have := hf.ap.2.1; exact this, ?_, ?_, fun i hi y hy ↦ ?_⟩
  · rcases hFF with ⟨e1, e2⟩ | hn
    · rw [e1, e2]; rcases hfb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by omega⟩
    · simp only [NewBuf] at hn
      rcases hn.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by have := hF.hL; omega, h0.2⟩
  · rcases hQ with ⟨e1, e2⟩ | h0 | h0
    · rw [e1, e2]; rcases hhq with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by omega⟩
    · exact Or.inl h0
    · exact Or.inr ⟨by have := hF.hL; omega, h0.2⟩
  · rcases hFF with ⟨e1, e2⟩ | hn
    · rw [e1, e2]; simp only [Apart]; omega
    · simp only [NewBuf] at hn; simp only [Apart]
      rcases hn.2 with h0 | h0
      · omega
      · rcases gb with h1 | h1 <;> omega
  · simp only [Apart]
    rcases hQ with ⟨e1, e2⟩ | h0 | h0
    · rw [e1, e2]; omega
    · omega
    · rcases gb with h1 | h1 <;> omega
  · obtain ⟨f1, f2, f3, f4, f5⟩ := hh.frozen i hi y hy
    refine ⟨f1, f2, ?_, f4, ?_⟩
    · rcases hFF with ⟨e1, e2⟩ | hn
      · rw [e1, e2]; exact f3
      · simp only [NewBuf] at hn; simp only [Within]
        rcases hn.2 with h0 | h0 <;> omega
    · rcases hQ with ⟨e1, e2⟩ | h0 | h0
      · rw [e1, e2]; exact f5
      · simp only [Within]; omega
      · simp only [Within]; omega

/-- The quadratic's buffer at the glue's entry, the fold rounds'. -/
theorem AtR.g896 {s : MachineState} {x : LCtx} {h t u w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (ha : AtR s x h t u w r ℓ Wl lf qq res pend d qs) (hf : Fronted s r g q) :
    g.getMem (s.getReg .x2 - 896) = t.getReg .x22 := by
  have hb := bounds hpre
  have hP := ha.pnd
  have hpraw := hP.vec.raw
  simp only [RawVecOk, Buf] at hpraw
  have hhr := ha.heap.hi
  simp only [heapEnd] at hhr
  rw [← ha.quad.1]
  exact hf.fr _ fun i hi hw ↦ by
    rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
    all_goals first
      | addr_omega [hw, hi, hb]
      | (have hI := hpre.self; have hS := Region.bounds hI.ok.self; have hIs := hI.stack
         rw [stackLo_vso, vso_stack] at hIs; addr_omega [hw, hi, hb, hS, hIs])
      | (obtain ⟨hnx, -⟩ := sfacts hpre; addr_omega [hw, hi, hb, hnx])
      | (rcases hpraw.2 with h0 | h0
         · simp only [Within] at hw; omega
         · addr_omega [hw, hi, hb, h0, hhr])
      | (simp only [Fresh] at hw; have := hf.heap.hi; simp only [heapEnd] at this
         addr_omega [hw.2, hi, hb, this])

/-- What the tail writes from the rows' end to the back edge's end, in the loop's `LM`. -/
theorem tailLM {s : MachineState} {x : LCtx} {h t u w r g z z' v : MachineState} {ℓ : ℕ}
    {Wl Wl' : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (ha : AtR s x h t u w r ℓ Wl lf qq res pend d qs) (hf : Fronted s r g q)
    (hgo : GlueOut s g z Wl') (hz : ∀ a, z'.getMem a = z.getMem a)
    (hX : DFrame z' v fun a ↦ Within a (s.getReg .x11) 32 ∨ Within a (s.getReg .x2 - 784) 8 ∨
      Within a (s.getReg .x2 - 824) 8)
    (hnv : heapNext z ≤ heapNext v) :
    DFrame x.c v (LM s x.L (v.getMem nextAddr)) := by
  have hb := bounds hpre
  have hF := ha.head.facts
  have hrt : heapNext h ≤ heapNext r := le_trans ha.ht (le_trans ha.tu (le_trans ha.uw ha.wr))
  have hmo := hf.mono
  have hmz := hgo.mono
  have hP := ha.pnd
  obtain ⟨gc, ep, -, -, -⟩ := gluedG hpre ha hf
  obtain ⟨-, q23, -, -⟩ := ha.quad
  have rg := ha.fo.regions
  have htv : heapNext t ≤ heapNext v := by
    have := ha.tu; have := ha.uw; have := ha.wr; omega
  have hL : x.L ≤ heapNext h := hF.hL
  have lm (a : Word) (h1 : x.L ≤ a.toNat) (h2 : a.toNat < heapNext v) :
      LM s x.L (v.getMem nextAddr) a :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))
  refine ((((ha.fr.mono fun a ha' ↦ LM.mono (by
        show heapNext r ≤ heapNext v; omega) ha').trans (hf.fr.mono fun a ha' ↦ ?_)
      fun _ h ↦ h).trans (hgo.fr.mono fun a ha' ↦ ?_) fun _ h ↦ h).trans
      (DFrame.of_same hz _) fun _ h ↦ h).trans (hX.mono fun a ha' ↦ ?_) fun _ h ↦ h
  · rcases ha' with ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha'
    · exact Or.inl (by addr_omega [ha', hb])
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (by simp only [W]; addr_omega [ha'])))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha'))))))
    · have := hP.fresh a (Or.inl ha')
      exact lm a (by have := ha.ht; omega) (by omega)
    · simp only [Fresh] at ha'; exact lm a (by omega) (by omega)
  · rcases ha' with ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha'
    · rw [ha.g896 hpre hf, hf.regs .x23 (by decide), q23] at ha'
      simp only [Within] at ha'
      rcases rg.qb with h0 | h0
      · omega
      · exact lm a (by omega) (by omega)
    · rw [ep, gc] at ha'
      simp only [Within] at ha'
      rcases rg.gb with h0 | h0
      · omega
      · exact lm a (by omega) (by have := ha.ht; omega)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha'))))))
    · simp only [Fresh] at ha'; exact lm a (by omega) (by omega)
  · rcases ha' with ha' | ha' | ha'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ha'))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb]))))
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb])))

/-- From the rows' end through the glue and the back edge. -/
structure TailEnd (s : MachineState) (x : LCtx) (h t u w r g z z' v : MachineState) (ℓ : ℕ)
    (Wl Wl' : Model.Pcs.WhirLocals) (lf qq res q : List E)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (d : Digest) (qs : List Word) : Prop where
  ha : AtR s x h t u w r ℓ Wl lf qq res pend d qs
  hf : Fronted s r g q
  hgo : GlueOut s g z Wl'
  zm : ∀ a, z'.getMem a = z.getMem a
  zr : ∀ q ∈ calleeSaved, z'.getReg q = z.getReg q
  bfr : DFrame z' v fun a ↦ Within a (s.getReg .x11) 32 ∨ Within a (s.getReg .x2 - 784) 8 ∨
    Within a (s.getReg .x2 - 824) 8
  vn : heapNext v = heapNext z
  wf : Wl'.folds = Wl.folds ++ lf

/-- A heap byte from the configured mark on, below `v`'s `NEXT`, outside the quadratic, the glued
claims' buffer at `g` and the old pending buffer, is the rows' end's. -/
theorem TailEnd.keepHeap {s : MachineState} {x : LCtx} {h t u w r g z z' v : MachineState}
    {ℓ : ℕ} {Wl Wl' : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (he : TailEnd s x h t u w r g z z' v ℓ Wl Wl' lf qq res q pend d qs)
    (y : Word) (h1 : x.L ≤ y.toNat) (h2 : y.toNat + 8 ≤ heapNext r)
    (h3 : ∀ i < 8, ¬ Within (y + BitVec.ofNat 64 i) (g.getMem (s.getReg .x2 - 896))
      (24 * (g.getReg .x23).toNat))
    (h4 : ∀ i < 8, ¬ Within (y + BitVec.ofNat 64 i) (vecPtr g (s.getReg .x2 - 664))
      ((vecCap g (s.getReg .x2 - 664)).toNat * 88))
    (h5 : ∀ i < 8, ¬ Within (y + BitVec.ofNat 64 i) (vecPtr r (s.getReg .x2 - 616))
      ((vecCap r (s.getReg .x2 - 616)).toNat * 80)) :
    v.getMem y = r.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIf := hI.free
  simp only [Outside] at hIf
  have hrs := hpre.root.free
  simp only [Outside] at hrs
  have hF := he.ha.head.facts
  have hhr := he.ha.heap.hi
  simp only [heapEnd] at hhr
  have hsL := hF.hs
  refine ((he.bfr y fun i hi hw ↦ ?_).trans (he.zm y)).trans ((he.hgo.fr y fun i hi hw ↦ ?_).trans
    (he.hf.fr y fun i hi hw ↦ ?_))
  · rcases hw with hw | hw | hw
    · rcases hrs.1 with h0 | h0
      · addr_omega [hw, hi, h0, h1, hsL, h2, hhr]
      · addr_omega [hw, hi, h0, h2, hhr]
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
  · rcases hw with hw | hw | hw | hw | hw | hw | hw | hw
    · exact h3 i hi hw
    · exact h4 i hi hw
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hnx]
    · simp only [Fresh] at hw; have hm := he.hf.mono; addr_omega [hw.1, hi, h2, hhr, hm]
  · rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
    · addr_omega [hw, hi, h2, hhr, hb]
    · rcases hIf.1 with h0 | h0
      · addr_omega [hw, hi, h0, h1, hsL, hS, h2, hhr]
      · addr_omega [hw, hi, h0, h2, hhr, hS]
    · addr_omega [hw, hi, h2, hhr, hnx]
    · exact h5 i hi hw
    · simp only [Fresh] at hw; addr_omega [hw.1, hi, h2, hhr]

/-- The stack slots the tail keeps, from the rows' end to the back edge's end. -/
theorem TailEnd.keepSlot {s : MachineState} {x : LCtx} {h t u w r g z z' v : MachineState}
    {ℓ : ℕ} {Wl Wl' : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (he : TailEnd s x h t u w r g z z' v ℓ Wl Wl' lf qq res q pend d qs)
    (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 904).toNat ∨ (s.getReg .x2 - 896).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 832).toNat ∨ (s.getReg .x2 - 816).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 784).toNat ∨ (s.getReg .x2 - 776).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 664).toNat ∨ (s.getReg .x2 - 592).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 512).toNat) :
    v.getMem y = r.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hhr := he.ha.heap.hi
  have hhg := he.hf.heap.hi
  have hhz := he.hgo.heap.hi
  have hP := he.ha.pnd
  have hraw := hP.vec.raw
  simp only [RawVecOk, Buf] at hraw
  obtain ⟨hgv, -⟩ := he.hf.vec
  have hgr := hgv.raw
  simp only [RawVecOk, Buf] at hgr
  have hgo := he.hgo
  obtain ⟨gc, ep, -, -, -⟩ := gluedG hpre he.ha he.hf
  obtain ⟨-, q23, -, -⟩ := he.ha.quad
  have rg := he.ha.fo.regions
  have hrt : heapNext t ≤ heapNext r := by
    have := he.ha.tu; have := he.ha.uw; have := he.ha.wr; omega
  have hhe := he.ha.head.facts.hend
  refine ((he.bfr y fun i hi hw ↦ ?_).trans (he.zm y)).trans ((hgo.fr y fun i hi hw ↦ ?_).trans
    (he.hf.fr y fun i hi hw ↦ ?_))
  · rcases hw with hw | hw | hw <;> rcases hy with hy | hy | hy | hy | hy <;>
      addr_omega [hw, hi, hy, hb, hrst]
  · rcases hw with hw | hw | hw | hw | hw | hw | hw | hw
    · rw [he.ha.g896 hpre he.hf, he.hf.regs .x23 (by decide), q23] at hw
      rcases rg.qb with h0 | h0
      · simp only [Within] at hw; omega
      · rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, h0, hhr, hrt]
    · rw [ep, gc] at hw
      rcases rg.gb with h0 | h0
      · simp only [Within] at hw; omega
      · rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, h0, hhe]
    all_goals first
      | (rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hnx])
      | (simp only [Fresh] at hw; rcases hy with hy | hy | hy | hy | hy <;>
          addr_omega [hw.2, hi, hy, hb, hhz])
  · rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
    all_goals first
      | (rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hnx])
      | (rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hS, hIs])
      | (rcases hraw.2 with h0 | h0
         · simp only [Within] at hw; omega
         · rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hi, hy, hb, h0, hhr])
      | (simp only [Fresh] at hw; rcases hy with hy | hy | hy | hy | hy <;>
          addr_omega [hw.2, hi, hy, hb, hhg])

/-- Glued claims kept through a frame that misses their header, buffer and weights' buffers. -/
theorem gluedFrame {s z v : MachineState} {X : Word → Prop} (hpre : VsoPre s) (hD : DFrame z v X)
    (hhdr : ∀ y : Word, (s.getReg .x2 - 664).toNat ≤ y.toNat → y.toNat < (s.getReg .x2 - 640).toNat →
      ¬ X y)
    (hv : VecOk z (s.getReg .x2 - 664) 88 8) (hhe : heapNext z ≤ heapEnd)
    (hbuf : ∀ y, Within y (vecPtr z (s.getReg .x2 - 664))
      ((vecCap z (s.getReg .x2 - 664)).toNat * 88) → ¬ X y)
    (hib : ∀ i < (vecLen z (s.getReg .x2 - 664)).toNat, ∀ y, InBufs z (gAddr z s i) y →
      ¬ X y ∧ y.toNat < heapEnd) :
    vecCap v (s.getReg .x2 - 664) = vecCap z (s.getReg .x2 - 664) ∧
    vecPtr v (s.getReg .x2 - 664) = vecPtr z (s.getReg .x2 - 664) ∧
    vecLen v (s.getReg .x2 - 664) = vecLen z (s.getReg .x2 - 664) ∧
    gluedListAt v (vecPtr v (s.getReg .x2 - 664)) (vecLen v (s.getReg .x2 - 664)).toNat =
      gluedListAt z (vecPtr z (s.getReg .x2 - 664)) (vecLen z (s.getReg .x2 - 664)).toNat ∧
    ∀ i < (vecLen z (s.getReg .x2 - 664)).toNat,
      (∀ y, InBufs v (gAddr v s i) y ↔ InBufs z (gAddr z s i) y) ∧
      (WeightAligned v (gAddr v s i) ↔ WeightAligned z (gAddr z s i)) := by
  have hb := bounds hpre
  have hraw := hv.raw
  simp only [RawVecOk, Buf] at hraw
  have hlc := hv.len
  have hdr (o : ℕ) (ho : o + 8 ≤ 24) :
      v.getMem (s.getReg .x2 - 664 + BitVec.ofNat 64 o) =
        z.getMem (s.getReg .x2 - 664 + BitVec.ofNat 64 o) :=
    hD _ fun i hi hx ↦ hhdr _ (by addr_omega [hb, hi, ho]) (by addr_omega [hb, hi, ho]) hx
  have ec : vecCap v (s.getReg .x2 - 664) = vecCap z (s.getReg .x2 - 664) := by
    simpa only [vecCap, add_ofNat_zero] using hdr 0 (by decide)
  have ep : vecPtr v (s.getReg .x2 - 664) = vecPtr z (s.getReg .x2 - 664) := hdr 8 (by decide)
  have el : vecLen v (s.getReg .x2 - 664) = vecLen z (s.getReg .x2 - 664) := hdr 16 (by decide)
  have hWE (i : ℕ) (hi : i < (vecLen z (s.getReg .x2 - 664)).toNat) :
      WordsEq v (gAddr v s i) z (gAddr z s i) 11 := fun k hk ↦ by
    simp only [gAddr, ep]
    refine hD _ fun j hj hx ↦ hbuf _ ?_ hx
    rcases hraw.2 with h0 | h0
    · omega
    · simp only [heapEnd] at hhe; addr_omega [h0, hj, hk, hi, hlc, hhe]
  have hWB (i : ℕ) (hi : i < (vecLen z (s.getReg .x2 - 664)).toNat) : WBufs v z (gAddr z s i) :=
    WBufs.of_frame hD fun y hy ↦ hib i hi y hy
  refine ⟨ec, ep, el, ?_, fun i hi ↦ ⟨fun y ↦ InBufs_congr ((hWE i hi).ptrs (by omega)) y, ?_⟩⟩
  · rw [ep, el]
    simp only [gluedListAt]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have h1 := hWE i hi
    have h2 := hWB i hi
    simp only [gAddr, ep] at h1 h2
    exact gluedAt_congr h1 h2
  · have hp := (hWE i hi).ptrs (by omega)
    unfold WeightAligned
    rw [hp.w0, hp.p0, hp.p8, hp.p24]

theorem endFacts {s : MachineState} {x : LCtx} {h t u w r g z z' v : MachineState} {ℓ : ℕ}
    {Wl Wl' : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (he : TailEnd s x h t u w r g z z' v ℓ Wl Wl' lf qq res q pend d qs) :
    VecEAt v (s.getReg .x2 - 688) x.L Wl'.folds ∧
    (VecOk v (s.getReg .x2 - 664) 88 8 ∧
      gluedListAt v (vecPtr v (s.getReg .x2 - 664)) (vecLen v (s.getReg .x2 - 664)).toNat = Wl'.glued ∧
      (vecCap v (s.getReg .x2 - 664) = 0 ∨ x.L ≤ (vecPtr v (s.getReg .x2 - 664)).toNat)) ∧
    (eListAt v (t.getReg .x22) (t.getReg .x23).toNat = Wl'.runningQuad ∧
      (t.getReg .x22).toNat % 8 = 0 ∧ ((t.getReg .x23).toNat = 0 ∨
      x.L ≤ (t.getReg .x22).toNat ∧ (t.getReg .x22).toNat + 24 * (t.getReg .x23).toNat ≤ heapNext v)) ∧
    (Apart (vecPtr v (s.getReg .x2 - 688)) ((vecCap v (s.getReg .x2 - 688)).toNat * 24)
      (vecPtr v (s.getReg .x2 - 664)) ((vecCap v (s.getReg .x2 - 664)).toNat * 88) ∧
    Apart (vecPtr v (s.getReg .x2 - 688)) ((vecCap v (s.getReg .x2 - 688)).toNat * 24)
      (t.getReg .x22) (24 * (t.getReg .x23).toNat) ∧
    Apart (vecPtr v (s.getReg .x2 - 664)) ((vecCap v (s.getReg .x2 - 664)).toNat * 88)
      (t.getReg .x22) (24 * (t.getReg .x23).toNat)) ∧
    (∀ i < (vecLen v (s.getReg .x2 - 664)).toNat, ∀ y, InBufs v (gAddr v s i) y →
      x.L ≤ y.toNat ∧ y.toNat < heapNext v ∧
      ¬ Within y (vecPtr v (s.getReg .x2 - 688)) ((vecCap v (s.getReg .x2 - 688)).toNat * 24) ∧
      ¬ Within y (vecPtr v (s.getReg .x2 - 664)) ((vecCap v (s.getReg .x2 - 664)).toNat * 88) ∧
      ¬ Within y (t.getReg .x22) (24 * (t.getReg .x23).toNat)) ∧
    (∀ i < (vecLen v (s.getReg .x2 - 664)).toNat, WeightAligned v (gAddr v s i)) := by
  have hb := bounds hpre
  have ha := he.ha
  have hhd := ha.head
  have hF := hhd.facts
  have hfo := ha.fo
  have hgo := he.hgo
  have hf := he.hf
  have hK := K0_lt s
  have hlt := hhd.lvl
  have kS := he.keepSlot hpre
  have hzn : heapNext v = heapNext z := he.vn
  have hmz := hgo.mono
  have hmg := hf.mono
  have hrt : heapNext t ≤ heapNext r := le_trans ha.tu (le_trans ha.uw ha.wr)
  obtain ⟨q896, q23, q808, -⟩ := ha.quad
  have hfQ := hfo.Q
  have hhq := hhd.quad
  have hhap := hhd.apart
  obtain ⟨hgv, -, -⟩ := hhd.glued
  have hhraw := hgv.raw
  simp only [RawVecOk, Buf] at hhraw
  have hFF := hfo.F
  have hap := hfo.ap
  obtain ⟨hfv, hfe, hfp, hfc⟩ := ha.folds
  have hfraw := hfv.raw
  simp only [RawVecOk, Buf] at hfraw
  have hfl := hfv.len
  obtain ⟨hzv, hzl, hzn'⟩ := hgo.glued
  have hzraw := hzv.raw
  simp only [RawVecOk, Buf] at hzraw
  obtain ⟨gc, gp, gl, -, -⟩ := gluedG hpre ha hf
  have rg := hfo.regions
  have hP := ha.pnd
  have hpraw := hP.vec.raw
  simp only [RawVecOk, Buf] at hpraw
  have hpend : (vecCap r (s.getReg .x2 - 616)).toNat * 80 = 0 ∨
      heapNext t ≤ (vecPtr r (s.getReg .x2 - 616)).toNat := by
    by_cases hc : (vecCap r (s.getReg .x2 - 616)).toNat * 80 = 0
    · exact Or.inl hc
    · rcases hpraw.2 with h0 | h0
      · exact absurd h0 hc
      · refine Or.inr (hP.fresh _ (Or.inl ?_)).1
        simp only [Within]; omega
  have hhr := ha.heap.hi
  simp only [heapEnd] at hhr
  have hrv : heapNext r ≤ heapNext v := by rw [hzn]; omega
  -- the slots at `z'`, as at `r`
  have kz (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 904).toNat ∨ (s.getReg .x2 - 896).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 832).toNat ∨ (s.getReg .x2 - 816).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 784).toNat ∨ (s.getReg .x2 - 776).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 664).toNat ∨ (s.getReg .x2 - 592).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 512).toNat) : z'.getMem y = r.getMem y := by
    have hrst := hpre.root.stack
    rw [stackLo_vso, vso_stack] at hrst
    rw [← kS y hy]
    exact (he.bfr y fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> rcases hy with hy | hy | hy | hy | hy <;>
        addr_omega [hw, hi, hy, hb, hrst]).symm
  -- the quadratic at `g` is the fold rounds'
  have g896 : g.getMem (s.getReg .x2 - 896) = t.getReg .x22 := by
    rw [← q896]
    exact hf.fr _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
      all_goals first
        | addr_omega [hw, hi, hb]
        | (have hI := hpre.self; have hS := Region.bounds hI.ok.self; have hIs := hI.stack
           rw [stackLo_vso, vso_stack] at hIs; addr_omega [hw, hi, hb, hS, hIs])
        | (obtain ⟨hnx, -⟩ := sfacts hpre; addr_omega [hw, hi, hb, hnx])
        | (rcases hpraw.2 with h0 | h0
           · simp only [Within] at hw; omega
           · addr_omega [hw, hi, hb, h0, hhr])
        | (simp only [Fresh] at hw; have := hf.heap.hi; simp only [heapEnd] at this
           addr_omega [hw.2, hi, hb, this])
  have g23 : g.getReg .x23 = t.getReg .x23 := (hf.regs .x23 (by decide)).trans q23
  have hlf : Wl'.folds = Wl.folds ++ lf := he.wf
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hrf := hpre.root.free
  simp only [Outside] at hrf
  have hsL := hF.hs
  have hgv := hgo.heap.hi
  have hgz : heapNext g ≤ heapNext z := hmz
  have hrg : heapNext r ≤ heapNext g := hmg
  have hDz : DFrame z v fun a ↦ Within a (s.getReg .x11) 32 ∨ Within a (s.getReg .x2 - 784) 8 ∨
      Within a (s.getReg .x2 - 824) 8 := (DFrame.of_same he.zm _).trans he.bfr fun _ h ↦ h
  -- the glued claims' buffer at `z`: the head's, or new since `g`
  have hzb : (vecCap z (s.getReg .x2 - 664)).toNat * 88 = 0 ∨
      ((vecPtr z (s.getReg .x2 - 664)).toNat + (vecCap z (s.getReg .x2 - 664)).toNat * 88 ≤
        heapNext h ∧ x.L ≤ (vecPtr z (s.getReg .x2 - 664)).toNat ∧
        vecPtr z (s.getReg .x2 - 664) = vecPtr h (s.getReg .x2 - 664) ∧
        vecCap z (s.getReg .x2 - 664) = vecCap h (s.getReg .x2 - 664)) ∨
      (heapNext g ≤ (vecPtr z (s.getReg .x2 - 664)).toNat ∧
        (vecPtr z (s.getReg .x2 - 664)).toNat + (vecCap z (s.getReg .x2 - 664)).toNat * 88 ≤
          heapNext z) := by
    rcases hzn' with ⟨e1, e2⟩ | hn
    · rw [e1, e2, gp, gc]
      rcases rg.gb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inl ⟨h0.2, h0.1, rfl, rfl⟩)
    · simp only [NewBuf] at hn
      rcases hn.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inr h0)
  have hcls (i : ℕ) (hi : i < (vecLen z (s.getReg .x2 - 664)).toNat) (y : Word)
      (hy : InBufs z (gAddr z s i) y) :
      (heapNext t ≤ y.toNat ∧ y.toNat < heapNext g) ∨
        ∃ j < (vecLen h (s.getReg .x2 - 664)).toNat, InBufs h (gAddr h s j) y :=
    readsClass hpre ha hf y (hgo.bufs i hi y hy)
  have hib (i : ℕ) (hi : i < (vecLen z (s.getReg .x2 - 664)).toNat) (y : Word)
      (hy : InBufs z (gAddr z s i) y) : x.L ≤ y.toNat ∧ y.toNat < heapNext g := by
    rcases hcls i hi y hy with h0 | ⟨j, hj, hjb⟩
    · exact ⟨by have := hF.hL; have := ha.ht; omega, h0.2⟩
    · have := rg.old j hj y hjb; exact ⟨this.1, by have := ha.ht; omega⟩
  obtain ⟨vc, vp, vl, vgl, vib⟩ := gluedFrame (X := fun a ↦ Within a (s.getReg .x11) 32 ∨
      Within a (s.getReg .x2 - 784) 8 ∨ Within a (s.getReg .x2 - 824) 8) hpre hDz
    (fun y h1 h2 hx ↦ by rcases hx with hx | hx | hx <;> addr_omega [hx, h1, h2, hb, hrst])
    hzv hgv
    (fun y hy hx ↦ by
      rcases hzb with h0 | h0 | h0
      · simp only [Within] at hy; omega
      · rcases hx with hx | hx | hx
        · rcases hrf.1 with h1 | h1
          · addr_omega [hy, hx, h1, h0.2.1, hsL]
          · addr_omega [hy, hx, h1, h0.1, hF.hend]
        · addr_omega [hy, hx, h0.1, hF.hend, hb]
        · addr_omega [hy, hx, h0.1, hF.hend, hb]
      · rcases hx with hx | hx | hx
        · rcases hrf.1 with h1 | h1
          · have := hF.hL; have := ha.ht; addr_omega [hy, hx, h1, h0.1, hsL, hrt, hrg, hF.hL, ha.ht]
          · have := hgo.heap.hi; addr_omega [hy, hx, h1, h0.2, this]
        · have := hgo.heap.hi; addr_omega [hy, hx, h0.2, this, hb]
        · have := hgo.heap.hi; addr_omega [hy, hx, h0.2, this, hb])
    (fun i hi y hy ↦ by
      obtain ⟨h1, h2⟩ := hib i hi y hy
      have := hf.heap.hi
      refine ⟨fun hx ↦ ?_, by omega⟩
      rcases hx with hx | hx | hx
      · rcases hrf.1 with h3 | h3
        · addr_omega [hx, h1, h3, hsL]
        · addr_omega [hx, h2, h3, this]
      · addr_omega [hx, h2, this, hb]
      · addr_omega [hx, h2, this, hb])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have eh (o : ℕ) (ho : o + 8 ≤ 24) :
        v.getMem (s.getReg .x2 - 688 + BitVec.ofNat 64 o) =
          r.getMem (s.getReg .x2 - 688 + BitVec.ofNat 64 o) :=
      kS _ (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hb, ho])))))
    have fc : vecCap v (s.getReg .x2 - 688) = vecCap t (s.getReg .x2 - 688) := by
      rw [← hfc]; simpa only [vecCap, add_ofNat_zero] using eh 0 (by decide)
    have fpr : vecPtr v (s.getReg .x2 - 688) = vecPtr r (s.getReg .x2 - 688) := eh 8 (by decide)
    have fl : vecLen v (s.getReg .x2 - 688) = vecLen r (s.getReg .x2 - 688) := eh 16 (by decide)
    have fp : vecPtr v (s.getReg .x2 - 688) = vecPtr t (s.getReg .x2 - 688) := fpr.trans hfp
    rw [hfp, hfc] at hfraw
    rw [hfc] at hfl
    have hsl := hpre.heap.lo
    have hsL := hF.hs
    refine ⟨⟨?_, by rw [fl, fc]; exact hfl⟩, ?_, ?_⟩
    · simp only [RawVecOk, Buf]
      rw [fp, fc]
      refine ⟨hfraw.1, ?_⟩
      rcases rg.fb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by simp only [heapStart] at hsl ⊢; omega, by omega⟩
    · rw [hlf, ← hfe]
      simp only [vecEs]
      rw [fpr, fl]
      unfold Rv64Verifier.eListAt
      apply List.map_congr_left
      intro k hk
      simp only [List.mem_range] at hk
      have hq := rg.fq
      have hg' := rg.fg
      simp only [Apart] at hq hg'
      rw [hfp]
      rcases rg.fb with h0 | h0
      · omega
      have kw (m : ℕ) (hm : m < 3) :
          v.getMem (vecPtr t (s.getReg .x2 - 688) + BitVec.ofNat 64 (24 * k) + BitVec.ofNat 64 (8 * m)) =
            r.getMem (vecPtr t (s.getReg .x2 - 688) + BitVec.ofNat 64 (24 * k) +
              BitVec.ofNat 64 (8 * m)) :=
        he.keepHeap hpre _ (by addr_omega [h0, hk, hfl, hm]) (by addr_omega [h0, hk, hfl, hm, hhr, hrt])
          (fun i hi hw ↦ by rw [g896, g23] at hw; addr_omega [h0, hk, hfl, hm, hhr, hw, hi, hq])
          (fun i hi hw ↦ by rw [gp, gc] at hw; addr_omega [h0, hk, hfl, hm, hhr, hw, hi, hg'])
          (fun i hi hw ↦ by
            rcases hpend with h1 | h1
            · simp only [Within] at hw; omega
            · addr_omega [h0, hk, hfl, hm, hhr, hw, hi, h1])
      refine eAt_congr ?_ ?_ ?_
      · simpa using kw 0 (by decide)
      · simpa [BitVec.add_assoc] using kw 1 (by decide)
      · simpa [BitVec.add_assoc] using kw 2 (by decide)
    · rw [fc, fp]
      rcases rg.fb with h0 | h0
      · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [show (0 : Word).toNat = 0 from rfl]; omega))
      · exact Or.inr h0.1
  · refine ⟨⟨?_, by rw [vl, vc]; exact hzv.len⟩, by rw [vgl]; exact hzl, ?_⟩
    · simp only [RawVecOk, Buf]; rw [vc, vp]
      exact ⟨hzraw.1, hzraw.2.imp id fun h ↦ ⟨h.1, by rw [hzn]; exact h.2⟩⟩
    · rw [vc, vp]
      rcases hzb with h0 | h0 | h0
      · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [show (0 : Word).toNat = 0 from rfl]; omega))
      · exact Or.inr h0.2.1
      · exact Or.inr (by have := hF.hL; have := ha.ht; omega)
  · refine ⟨?_, hfQ.2.1, ?_⟩
    · rw [← hgo.quad, g896, g23]
      refine hDz.eListAt fun i hi hx ↦ ?_
      rcases rg.qb with h0 | h0
      · omega
      · rcases hx with hx | hx | hx
        · rcases hrf.1 with h1 | h1
          · addr_omega [hx, hi, h0, h1, hsL]
          · addr_omega [hx, hi, h0, h1, hhr, hrt]
        · addr_omega [hx, hi, h0, hhr, hrt, hb]
        · addr_omega [hx, hi, h0, hhr, hrt, hb]
    · rcases rg.qb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by rw [hzn]; omega⟩
  · have fp : vecPtr v (s.getReg .x2 - 688) = vecPtr t (s.getReg .x2 - 688) :=
      (kS _ (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))))).trans hfp
    have fc : vecCap v (s.getReg .x2 - 688) = vecCap t (s.getReg .x2 - 688) :=
      (kS _ (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))))).trans hfc
    rw [fp, fc, vp, vc]
    have hq := rg.fq
    have hg' := rg.fg
    have hgq := rg.gq
    simp only [Apart] at hq hg' hgq ⊢
    have hfb := rg.fb
    have hqb := rg.qb
    refine ⟨?_, hq, ?_⟩
    · rcases hzb with h0 | ⟨h1, h2, e1, e2⟩ | h0
      · omega
      · rw [e1, e2]; exact hg'
      · rcases hfb with h3 | h3 <;> omega
    · rcases hzb with h0 | ⟨h1, h2, e1, e2⟩ | h0
      · omega
      · rw [e1, e2]; exact hgq
      · rcases hqb with h3 | h3 <;> omega
  · exact fun i hi y hy ↦ by
      rw [vl] at hi
      rw [(vib i hi).1 y] at hy
      have fp : vecPtr v (s.getReg .x2 - 688) = vecPtr t (s.getReg .x2 - 688) :=
        (kS _ (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))))).trans hfp
      have fc : vecCap v (s.getReg .x2 - 688) = vecCap t (s.getReg .x2 - 688) :=
        (kS _ (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))))).trans hfc
      rw [fp, fc, vp, vc, hzn]
      have hfb := rg.fb
      have hqb := rg.qb
      rcases hcls i hi y hy with ⟨h1, h2⟩ | ⟨j, hj, hjb⟩
      · refine ⟨by have := hF.hL; have := ha.ht; omega, by omega, ?_, ?_, ?_⟩
        · simp only [Within]; rcases hfb with h3 | h3 <;> omega
        · have := ha.ht; simp only [Within]; rcases hzb with h3 | h3 | h3 <;> omega
        · simp only [Within]; rcases hqb with h3 | h3 <;> omega
      · obtain ⟨o1, o2, o3, o4, o5⟩ := rg.old j hj y hjb
        refine ⟨o1, by have := ha.ht; omega, o3, ?_, o5⟩
        rcases hzb with h3 | ⟨-, -, e1, e2⟩ | h3
        · simp only [Within]; omega
        · rw [e1, e2]; exact o4
        · simp only [Within]; have := ha.ht; omega
  · exact fun i hi ↦ by
      rw [vl] at hi
      exact ((vib i hi).2).mpr (hgo.aligned i hi)

/-- **The next level's head.** -/
theorem nextHead {s : MachineState} {x : LCtx} {h t u w r g z z' v : MachineState} {ℓ : ℕ}
    {Wl Wl' : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (hl : ℓ ≠ K0 s + 1)
    (he : TailEnd s x h t u w r g z z' v ℓ Wl Wl' lf qq res q pend d qs)
    (hbo : BackOut s z' v d) (hx1 : z'.getReg .x1 = BitVec.ofNat 64 (K0 s + 1))
    (hV : Runs s v (ℓ + 1) (levelsFrom s x (ℓ + 1) Wl')) :
    Head s x v (ℓ + 1) Wl' := by
  have hb := bounds hpre
  have ha := he.ha
  have hhd := ha.head
  have hK := K0_lt s
  have hlt := hhd.lvl
  have kS := he.keepSlot hpre
  have hzn : heapNext v = heapNext z := he.vn
  have hgo := he.hgo
  have hf := he.hf
  obtain ⟨q896, q23, q808, -⟩ := ha.quad
  obtain ⟨Ff, Fg, Fq, Fa, Fz, Fal⟩ := endFacts hpre he
  -- the slots at `z'`, as at `r`
  have kz (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 904).toNat ∨ (s.getReg .x2 - 896).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 832).toNat ∨ (s.getReg .x2 - 816).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 784).toNat ∨ (s.getReg .x2 - 776).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 664).toNat ∨ (s.getReg .x2 - 592).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 512).toNat) : z'.getMem y = r.getMem y := by
    have hrst := hpre.root.stack
    rw [stackLo_vso, vso_stack] at hrst
    rw [← kS y hy]
    exact (he.bfr y fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> rcases hy with hy | hy | hy | hy | hy <;>
        addr_omega [hw, hi, hy, hb, hrst]).symm
  have v22 : v.getReg .x22 = t.getReg .x22 := by
    rw [hbo.x22, kz _ (Or.inr (Or.inl (by addr_omega [hb]))), q896]
  have v23 : v.getReg .x23 = t.getReg .x23 := by
    rw [hbo.x23, kz _ (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))), q808]
  refine {
    cfg := hhd.cfg
    mark := hhd.mark
    fr := tailLM hpre ha hf hgo he.zm he.bfr (by rw [hzn])
    heap := ⟨by rw [hzn]; exact hgo.heap.lo, by rw [hzn]; exact hgo.heap.hi⟩
    mono := by
      rw [hzn]; have := hhd.mono; have := ha.ht; have := ha.tu; have := ha.uw; have := ha.wr
      have := hf.mono; have := hgo.mono; omega
    pc := hbo.pc
    sp := by rw [hbo.regs .x2 (by decide), he.zr .x2 (by decide), hgo.sp]; rfl
    x1 := by rw [hbo.regs .x1 (by decide), hx1]
    x5 := by
      rw [hbo.x5, kz _ (Or.inl (by addr_omega [hb])), ha.m32]
      apply BitVec.eq_of_toNat_eq; simp
    x8 := hbo.x8
    x9 := by
      rw [hbo.regs .x9 (by decide), he.zr .x9 (by decide), hgo.regs .x9 (by decide),
        hf.regs .x9 (by decide), ha.x9]
    x10 := by rw [hbo.x10, kz _ (Or.inr (Or.inl (by addr_omega [hb]))), ha.m176]
    x17 := hbo.x17
    x25 := by
      rw [hbo.regs .x25 (by decide), he.zr .x25 (by decide), hgo.regs .x25 (by decide), hf.x25,
        ha.m248]
    x26 := by
      rw [hbo.regs .x26 (by decide), he.zr .x26 (by decide), hgo.regs .x26 (by decide), hf.x26,
        ha.m128]
    x27 := by rw [hbo.x27, kz _ (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))), ha.m816]
    lvl := by omega
    m152 := by rw [kS _ (Or.inr (Or.inl (by addr_omega [hb]))), ha.m152]
    m160 := by rw [kS _ (Or.inr (Or.inl (by addr_omega [hb]))), ha.m160]
    m224 := by rw [kS _ (Or.inr (Or.inr (Or.inl (by addr_omega [hb])))), ha.m816]
    folds := Ff
    glued := Fg
    quad := by rw [v22, v23]; exact Fq
    apart := by rw [v22, v23]; exact Fa
    frozen := by rw [v22, v23]; exact Fz
    aligned := Fal
    value := hV }

end Rv64Verifier.Proofs.Pcs.Vso
