import Rv64Verifier.Proofs.Multilinear.MleEvalWin
import Rv64Verifier.Proofs.Multilinear.EqKernelInv

/-!
# `verifier::multilinear::multilinear_eval`: the invariants

```rust
pub fn multilinear_eval<T: Copy + Into<E>>(mle: &[T], point: &[E]) -> Result<E, VerifierError> {
    require(point.len() < 64 && mle.len() == 1 << point.len(), VerifierError::MultilinearSize)?;
    let mut cur: Vec<E> = mle.iter().map(|&value| value.into()).collect();
    for &r in point {
        let scale = Scaler::new(r, cur.len() / 2);
        for i in 0..cur.len() / 2 {
            cur[i] = cur[2 * i] + scale.mul(cur[2 * i] + cur[2 * i + 1]);
        }
        cur.truncate(cur.len() / 2);
    }
    Ok(cur[0])
}
```

compiled at `0x8000d28c` (`Blocks/F56.lean`) for `T = E`, with `S` the entry's `sp`, `n` the point's
length and `L` the table's: `0x8000d28c` saves `ra`, `s0`..`s11` in a 208-byte frame and checks the
sizes (`Err` at `0x8000d5b4`); `0x8000d2f0` calls `try_allocate_in(S - 128, L, 0, 8, 24)`,
`0x8000d318` keeps the result's address at `S - 208` and calls `reserve` on the new `Vec` (room
enough), `0x8000d340` calls `memcpy` (`s5` = the buffer `P`); `0x8000d378` keeps the point's end at
`S - 200`. The outer loop at `0x8000d3b8` (`s0` = the length, `a1` = `&point[k]`, kept at
`S - 192`) calls `Scaler::new(S - 160, &point[k], len / 2)`; `0x8000d3d4` sets up the inner loop
at `0x8000d478` (`s7` = `i`, `s3` = `len / 2`, `s1` = `(len + 1) / 2`, the `Scaler`'s tag in `t3`,
its table in `s10`, `s11`). `0x8000d47c` reads `cur[2i]` into `t5`, `t6`, `s0` and the sum into
`a5`, `a4`, `a1` and `S - 128`; the product goes to `a0`, `a2`, `a3` by `mul` (`0x8000d3f0`) or the
table (`MleEvalWin.table_mul`); `0x8000d448` writes `cur[i]`. `0x8000d3a4` moves to the next
coordinate; `0x8000d5c4` writes `Ok(cur[0])`, `0x8000d5e4` the tag, restores and returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.MleEval
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords
  Rv64Verifier.Blocks.F56 Rv64Verifier.Proofs.Multilinear.ScalerFill
  Rv64Verifier.Proofs.Multilinear.EqKernelWin Rv64Verifier.Proofs.Multilinear.MleEvalWin
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The values -/

/-- The point's length. -/
@[rv_addr] def nn (s : MachineState) : Nat := (s.getReg .x14).toNat

/-- The table's length. -/
@[rv_addr] def ll (s : MachineState) : Nat := (s.getReg .x12).toNat

def mle (s : MachineState) : List E := eListAt s (s.getReg .x11) (ll s)

def pt (s : MachineState) : List E := eListAt s (s.getReg .x13) (nn s)

/-- The table after `k` passes. -/
def cur (s : MachineState) (k : Nat) : List E := ((pt s).take k).foldl Model.mlePass (mle s)

/-- The sizes the check accepts. -/
structure Sized (s : MachineState) : Prop where
  lt : nn s < 64
  len : ll s = 2 ^ nn s

theorem cur_succ (s : MachineState) {k : Nat} (hk : k < nn s) :
    cur s (k + 1) = Model.mlePass (cur s k) ((pt s).getD k 0) := by
  have hk' : k < (pt s).length := by rw [pt, eListAt_length]; exact hk
  rw [cur, cur, List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem _ _ hk']

theorem mlePass_length (c : List E) (r : E) : (Model.mlePass c r).length = c.length / 2 := by
  rw [Model.mlePass_eq, Model.foldPairs_length]

theorem cur_length {s : MachineState} (hs : Sized s) :
    ∀ k, k ≤ nn s → (cur s k).length = 2 ^ (nn s - k)
  | 0, _ => by simp [cur, mle, eListAt_length, hs.len]
  | k + 1, hk => by
    rw [cur_succ s (by omega), mlePass_length, cur_length hs k (by omega),
      show nn s - k = nn s - (k + 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem eListAt_take (u : MachineState) (p : Word) {m N : Nat} (h : m ≤ N) :
    (eListAt u p N).take m = eListAt u p m := by
  apply List.ext_getElem (by simp [eListAt_length]; omega)
  intro i h1 h2
  rw [List.getElem_take, eListAt_getElem, eListAt_getElem]

/-- One pass of the inner loop, done: the next coordinate's table. -/
theorem pass_done {s u : MachineState} (hs : Sized s) {P : Word} {k : Nat} (hk : k < nn s)
    (h : eListAt u P (2 ^ (nn s - k)) = (List.range (2 ^ (nn s - k - 1))).foldl
      (Model.mleStep ((pt s).getD k 0)) (cur s k)) :
    eListAt u P (2 ^ (nn s - (k + 1))) = cur s (k + 1) := by
  have hl := cur_length hs k (by omega)
  have e : 2 ^ (nn s - k) / 2 = 2 ^ (nn s - k - 1) := by
    rw [show nn s - k = nn s - k - 1 + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rfl
  rw [cur_succ s hk, Model.mlePass, hl, e, ← h,
    eListAt_take _ _ (Nat.pow_le_pow_right (by norm_num) (by omega)),
    show nn s - (k + 1) = nn s - k - 1 by omega]

/-- The `Ok` value: `cur[0]` after every pass. -/
theorem value_eq {s : MachineState} (hs : Sized s) :
    Model.multilinearEvalRust (mle s) (pt s) = some ((cur s (nn s)).getD 0 0) := by
  have h1 : (pt s).length = nn s := by rw [pt, eListAt_length]
  have h2 : (mle s).length = ll s := by rw [mle, eListAt_length]
  rw [Model.multilinearEvalRust, ite_eq_left ⟨by rw [h1]; exact hs.lt, by rw [h1, h2]; exact hs.len⟩,
    cur, ← h1, List.take_length]

/-! ## The frame -/

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19),
  (48, .x20), (56, .x21), (64, .x22), (72, .x23), (80, .x24), (88, .x25), (96, .x26), (104, .x27)]

theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 ≤ 104 := by decide

/-- What the run may have written, while `NEXT` reached `nx`: the stack, `NEXT`, the heap
allocated since the entry. The result is written last. -/
@[rv_addr] def LW (s : MachineState) (nx a : Word) : Prop :=
  Within a (stackLo s mleEvalStack) mleEvalStack ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)

/-- `LW` and the result. -/
@[rv_addr] def PW (s : MachineState) (nx a : Word) : Prop :=
  Within a (s.getReg .x10) 32 ∨ LW s nx a

structure Inv (s u : MachineState) (nx : Word) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 208
  slots : ∀ p ∈ slots, u.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2
  dw : DwFrame s u (PW s nx)
  next : u.getMem nextAddr = nx
  mono : heapNext s ≤ nx.toNat
  fits : nx.toNat ≤ heapEnd

theorem outValid {s : MachineState} (h : MleEvalPre s) : ValidMemRange (s.getReg .x10) 4 := by
  intro i hi
  have ho := h.out
  exact Transcript.Region.valid ho (by addr_omega [ho, hi]) (by addr_omega [ho, hi])
    (by addr_omega [ho, hi])

theorem pointValid {s : MachineState} (h : MleEvalPre s) (hn : 0 < nn s) :
    ValidMemRange (s.getReg .x13) (3 * nn s) := by
  intro i hi
  have ho := h.point.resolve_left (by simp only [nn] at hn; omega)
  simp only [nn] at hi
  exact Transcript.Region.valid ho (by addr_omega [ho, hi]) (by addr_omega [ho, hi])
    (by addr_omega [ho, hi])

theorem bounds {s : MachineState} (h : MleEvalPre s) :
    0x78000000 + 1232 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 32 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds (outValid h) (by decide)
  simp only [mleEvalStack, mulStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop} (hpre : MleEvalPre s)
    (h : Inv s u nx) (hX : DwFrame u v X) (hsub : ∀ a, X a → PW s nx' a)
    (hslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - 104) 104)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) : Inv s v nx' := by
  have hb := bounds hpre
  have mono (a : Word) (ha : PW s nx a) : PW s nx' a := by
    simp only [PW, LW] at ha ⊢
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨ha.1, by omega⟩))
  refine ⟨hsp.trans h.sp, fun p hp ↦ ?_, ?_, hnx, Nat.le_trans h.mono hle, hend⟩
  · obtain ⟨h1, h2⟩ := slots_ok p hp
    rw [← h.slots p hp]
    exact hX _ (fun hx ↦ hslot _ hx (by addr_omega [hb, h1, h2]))
      (Or.inr fun i hi hx ↦ hslot _ hx (by addr_omega [hb, h1, h2, hi]))
  · intro a ha hb'
    rw [hX a (fun hx ↦ ha (hsub a hx)) (by
        rcases hb' with hb' | hb'
        · exact Or.inl hb'
        · exact Or.inr fun i hi hx ↦ hb' i hi (hsub _ hx))]
    exact h.dw a (fun hx ↦ ha (mono a hx)) (by
      rcases hb' with hb' | hb'
      · exact Or.inl hb'
      · exact Or.inr fun i hi hx ↦ hb' i hi (mono _ hx))

theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : MleEvalPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = u.getReg .x2) : Inv s v nx :=
  h.step hpre (DwFrame.same hm fun _ ↦ False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
    ((hm _).trans h.next) (Nat.le_refl _) h.fits hsp

theorem Inv.keep {s u : MachineState} {nx : Word} (h : Inv s u nx) {a : Word}
    (ha : ∀ i < 8, ¬ PW s nx (a + BitVec.ofNat 64 i)) : u.getMem a = s.getMem a :=
  h.dw a (by simpa using ha 0 (by decide)) (Or.inr ha)

theorem Inv.rodataOk {s u : MachineState} {nx : Word} (hpre : MleEvalPre s) (h : Inv s u nx) :
    RodataOk u := by
  have hb := bounds hpre
  have hro := hpre.stack.rodata
  have hor := hpre.outRodata
  have hfit := h.fits
  have miss (a : Word) (ha : Within a rodataBase Rv64Verifier.rodataSize) : ¬ PW s nx a := by
    simp only [PW, LW]
    rintro (hw | hw | hw | hw)
    · addr_omega [hw, ha, hor]
    · addr_omega [hw, ha, hro, hb]
    · addr_omega [hw, ha]
    · addr_omega [hw, ha, hfit]
  intro p hp
  have hin := within_of_mem_rodataWords hp
  rw [h.dw p.1 (miss _ (by addr_omega [hin])) (by
    by_cases h8 : p.1.toNat % 8 = 0
    · exact Or.inr fun i hi ↦ miss _ (by addr_omega [hin, hi, h8])
    · exact Or.inl h8)]
  exact hpre.rodata p hp

/-- An input slice is never written. -/
theorem Inv.slice {s u : MachineState} {nx : Word} (hpre : MleEvalPre s) (h : Inv s u nx)
    {p : Word} {N : Nat} (hfree : Outside s p (24 * N))
    (hst : Apart p (24 * N) (stackLo s mleEvalStack) mleEvalStack)
    (hout : Apart p (24 * N) (s.getReg .x10) 32) (hp : p.toNat + 24 * N ≤ 2 ^ 64) :
    eListAt u p N = eListAt s p N := by
  have hb := bounds hpre
  have hfit := h.fits
  have hmono := h.mono
  simp only [Outside] at hfree
  refine EqKernel.eListAt_dw h.dw (fun a ha hw ↦ ?_) hp
  simp only [PW, LW] at hw
  rcases hw with hw | hw | hw | hw
  · addr_omega [hw, ha, hout]
  · addr_omega [hw, ha, hst]
  · addr_omega [hw, ha, hfree.2]
  · rcases hfree.1 with h1 | h1
    · addr_omega [hw, ha, h1]
    · addr_omega [hw, ha, h1, hfit]

theorem Inv.point {s u : MachineState} {nx : Word} (hpre : MleEvalPre s) (h : Inv s u nx)
    (hn : 0 < nn s) : eListAt u (s.getReg .x13) (nn s) = pt s := by
  have he := ValidMemRange.bounds (pointValid hpre hn) (by omega)
  exact h.slice hpre (hpre.pointFree.resolve_left (by simp only [nn] at hn; omega))
    hpre.pointStack hpre.pointOut (by simp only [nn] at he ⊢; omega)

/-! ## From the allocation on -/

/-- The buffer `P`, room for `L` elements below `nx`, and the result's address at `S - 208`. -/
structure Res (s u : MachineState) (P nx : Word) : Prop where
  inv : Inv s u nx
  outp : u.getMem (s.getReg .x2 - 208) = s.getReg .x10
  align : P.toNat % 8 = 0
  lo : heapNext s ≤ P.toNat
  top : P.toNat + 24 * ll s ≤ nx.toNat

theorem Res.step {s u v : MachineState} {P nx nx' : Word} {X : Word → Prop}
    (hpre : MleEvalPre s) (h : Res s u P nx) (hX : DwFrame u v X) (hsub : ∀ a, X a → LW s nx' a)
    (hslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - 104) 104 ∧ ¬ Within a (s.getReg .x2 - 208) 8)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) : Res s v P nx' := by
  have hb := bounds hpre
  have e := EqKernel.DwFrame.keep hX (a := s.getReg .x2 - 208) fun i hi hx ↦
    (hslot _ hx).2 (by addr_omega [hb, hi])
  exact ⟨h.inv.step hpre hX (fun a ha ↦ Or.inr (hsub a ha)) (fun a ha ↦ (hslot a ha).1) hnx hle
    hend hsp, e.trans h.outp,
    h.align, h.lo, Nat.le_trans h.top hle⟩

theorem Res.same {s u v : MachineState} {P nx : Word} (hpre : MleEvalPre s) (h : Res s u P nx)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = u.getReg .x2) : Res s v P nx :=
  h.step hpre (DwFrame.same hm fun _ ↦ False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
    ((hm _).trans h.inv.next) (Nat.le_refl _) h.inv.fits hsp

/-- The loop's constants: the buffer in `s5`, the windows' ends in `s4`, `s6`, `s8`, the point's
end at `S - 200`. -/
structure Mid (s u : MachineState) (P nx : Word) : Prop extends Res s u P nx where
  x20 : u.getReg .x20 = 704
  x21 : u.getReg .x21 = P
  x22 : u.getReg .x22 = 1408
  x24 : u.getReg .x24 = 2112
  stop : u.getMem (s.getReg .x2 - 200) = s.getReg .x13 + BitVec.ofNat 64 (24 * nn s)

def midRegs : List Reg := [.x2, .x20, .x21, .x22, .x24]

theorem Mid.step {s u v : MachineState} {P nx nx' : Word} {X : Word → Prop}
    (hpre : MleEvalPre s) (h : Mid s u P nx) (hX : DwFrame u v X) (hsub : ∀ a, X a → LW s nx' a)
    (hslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - 104) 104 ∧ ¬ Within a (s.getReg .x2 - 208) 16)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ midRegs, v.getReg r = u.getReg r) : Mid s v P nx' := by
  have hb := bounds hpre
  have e := EqKernel.DwFrame.keep hX (a := s.getReg .x2 - 200) fun i hi hx ↦
    (hslot _ hx).2 (by addr_omega [hb, hi])
  exact { toRes := h.toRes.step hpre hX hsub
            (fun a ha ↦ ⟨(hslot a ha).1, fun h' ↦ (hslot a ha).2 (by addr_omega [h'])⟩) hnx hle
            hend (hr _ (by decide))
          x20 := (hr _ (by decide)).trans h.x20
          x21 := (hr _ (by decide)).trans h.x21
          x22 := (hr _ (by decide)).trans h.x22
          x24 := (hr _ (by decide)).trans h.x24
          stop := e.trans h.stop }

theorem Mid.same {s u v : MachineState} {P nx : Word} (hpre : MleEvalPre s)
    (h : Mid s u P nx) (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ midRegs, v.getReg r = u.getReg r) : Mid s v P nx :=
  h.step hpre (DwFrame.same hm fun _ ↦ False) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim)
    ((hm _).trans h.inv.next) (Nat.le_refl _) h.inv.fits hr

theorem shr1 {m : Nat} (h1 : 1 ≤ m) (h2 : m < 64) :
    BitVec.ofNat 64 (2 ^ m) >>> 1 = BitVec.ofNat 64 (2 ^ (m - 1)) := by
  have hp : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) h2
  have he : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  omega

theorem shr1' {m : Nat} (h1 : 1 ≤ m) (h2 : m < 64) :
    (BitVec.ofNat 64 (2 ^ m) + 1) >>> 1 = BitVec.ofNat 64 (2 ^ (m - 1)) := by
  have hp : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) h2
  have he : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hp, Nat.shiftRight_eq_div_pow]
  simp only [Sym.wordToNatLit]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The sizes: `24 · 2^n` bytes fit in the heap, so `n < 27`. -/
theorem Res.small {s u : MachineState} {P nx : Word} (hs : Sized s) (h : Res s u P nx) :
    P.toNat + 24 * 2 ^ nn s ≤ heapEnd ∧ nn s < 27 := by
  have h1 := h.top
  have h3 := h.inv.fits
  rw [hs.len] at h1
  have hP : P.toNat + 24 * 2 ^ nn s ≤ heapEnd := by omega
  refine ⟨hP, Nat.lt_of_not_le fun h27 ↦ ?_⟩
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h27
  simp only [heapEnd] at hP
  norm_num at this
  omega

/-- At `0x8000d3b8`, the first `k` passes done. -/
structure OInv (s u : MachineState) (P nx : Word) (k : Nat) : Prop extends Mid s u P nx where
  pc : u.pc = 0x8000d3b8
  lt : k < nn s
  x11 : u.getReg .x11 = s.getReg .x13 + BitVec.ofNat 64 (24 * k)
  x8 : u.getReg .x8 = BitVec.ofNat 64 (2 ^ (nn s - k))
  buf : eListAt u P (2 ^ (nn s - k)) = cur s k

/-- The `Scaler` for `r` at `S - 160`, as the inner loop reads it: the tag in `t3`, the table `T`
in `s10`, its length in `s11`. -/
structure Sc (s u : MachineState) (P T nx : Word) (r : E) : Prop where
  x26 : u.getReg .x26 = T
  plain : u.getReg .x28 ≠ 0 → eAt u (s.getReg .x2 - 152) = r
  table : u.getReg .x28 = 0 → u.getReg .x27 = 2112 ∧ BufP T ∧ P.toNat + 24 * ll s ≤ T.toNat ∧
    T.toNat + tabBytes ≤ nx.toNat ∧ tab u T = Model.scaledTable (Model.limbs r)

/-- The `Scaler` survives a step writing the stack below it, the sum and the buffer. -/
theorem Sc.step {s u v : MachineState} {P T nx : Word} {r : E} {X : Word → Prop}
    (hpre : MleEvalPre s) (hm : Mid s u P nx) (h : Sc s u P T nx r) (hX : DwFrame u v X)
    (hsub : ∀ a, X a → Within a (s.getReg .x2 - 1232) 1072 ∨ Within a (s.getReg .x2 - 128) 24 ∨
      Within a P (24 * ll s))
    (hr : ∀ r ∈ [Reg.x26, .x27, .x28], v.getReg r = u.getReg r) : Sc s v P T nx r := by
  have hb := bounds hpre
  have hab := hpre.stack.above
  have htop := hm.top
  have hfit := hm.inv.fits
  refine ⟨(hr _ (by decide)).trans h.x26, fun hne ↦ ?_, fun he ↦ ?_⟩
  · rw [hr _ (by decide)] at hne
    rw [← h.plain hne]
    have w (c : Nat) (hc : c = 0 ∨ c = 8 ∨ c = 16) :
        v.getMem (s.getReg .x2 - 152 + BitVec.ofNat 64 c) =
          u.getMem (s.getReg .x2 - 152 + BitVec.ofNat 64 c) :=
      EqKernel.DwFrame.keep hX fun i hi hx ↦ by
        rcases hsub _ hx with hx | hx | hx
        · addr_omega [hx, hi, hc, hb]
        · addr_omega [hx, hi, hc, hb]
        · addr_omega [hx, hi, hc, hb, hab, htop, hfit]
    have e0 := w 0 (Or.inl rfl)
    have e1 := w 8 (Or.inr (Or.inl rfl))
    have e2 := w 16 (Or.inr (Or.inr rfl))
    simp only [BitVec.add_zero] at e0 e1 e2
    exact eAt_congr e0 e1 e2
  · rw [hr _ (by decide)] at he
    obtain ⟨h27, hB, hPT, hTt, htab⟩ := h.table he
    have hTh := hB.hi
    refine ⟨(hr _ (by decide)).trans h27, hB, hPT, hTt, ?_⟩
    rw [EqKernel.tab_dw hX (fun a ha hx ↦ by
        rcases hsub _ hx with hx | hx | hx
        · addr_omega [hx, ha, hb, hab, hTh]
        · addr_omega [hx, ha, hb, hab, hTh]
        · addr_omega [hx, ha, hPT])
      (by simp only [tabBytes, heapEnd] at hTh ⊢; omega), htab]

/-- At `0x8000d478`, pass `k` at `i`. -/
structure IInv (s u : MachineState) (P T nx : Word) (k i : Nat) : Prop extends Mid s u P nx where
  pc : u.pc = 0x8000d478
  lt : k < nn s
  ilt : i < 2 ^ (nn s - k - 1)
  m192 : u.getMem (s.getReg .x2 - 192) = s.getReg .x13 + BitVec.ofNat 64 (24 * k)
  x19 : u.getReg .x19 = BitVec.ofNat 64 (2 ^ (nn s - k - 1))
  x9 : u.getReg .x9 = BitVec.ofNat 64 (2 ^ (nn s - k - 1))
  x23 : u.getReg .x23 = BitVec.ofNat 64 i
  sc : Sc s u P T nx ((pt s).getD k 0)
  buf : eListAt u P (2 ^ (nn s - k)) =
    (List.range i).foldl (Model.mleStep ((pt s).getD k 0)) (cur s k)

/-- At `0x8000d448`, `cur[2i]` in `t5`, `t6`, `s0` and the product in `a0`, `a2`, `a3`. -/
structure Pre (s u : MachineState) (P T nx : Word) (k i : Nat) : Prop extends Mid s u P nx where
  pc : u.pc = 0x8000d448
  lt : k < nn s
  ilt : i < 2 ^ (nn s - k - 1)
  m192 : u.getMem (s.getReg .x2 - 192) = s.getReg .x13 + BitVec.ofNat 64 (24 * k)
  x19 : u.getReg .x19 = BitVec.ofNat 64 (2 ^ (nn s - k - 1))
  x9 : u.getReg .x9 = BitVec.ofNat 64 (2 ^ (nn s - k - 1))
  x23 : u.getReg .x23 = BitVec.ofNat 64 i
  x25 : u.getReg .x25 = BitVec.ofNat 64 (16 * i)
  sc : Sc s u P T nx ((pt s).getD k 0)
  buf : eListAt u P (2 ^ (nn s - k)) =
    (List.range i).foldl (Model.mleStep ((pt s).getD k 0)) (cur s k)
  even : (u.getReg .x30, u.getReg .x31, u.getReg .x8) =
    Model.limbs (eAt u (P + BitVec.ofNat 64 (24 * (2 * i))))
  prod : (u.getReg .x10, u.getReg .x12, u.getReg .x13) =
    Model.limbs ((eAt u (P + BitVec.ofNat 64 (24 * (2 * i))) +
      eAt u (P + BitVec.ofNat 64 (24 * (2 * i + 1)))) * (pt s).getD k 0)

/-- At `0x8000d3a4`, pass `k` done. -/
structure Done (s u : MachineState) (P nx : Word) (k : Nat) : Prop extends Mid s u P nx where
  pc : u.pc = 0x8000d3a4
  lt : k < nn s
  m192 : u.getMem (s.getReg .x2 - 192) = s.getReg .x13 + BitVec.ofNat 64 (24 * k)
  x19 : u.getReg .x19 = BitVec.ofNat 64 (2 ^ (nn s - k - 1))
  buf : eListAt u P (2 ^ (nn s - (k + 1))) = cur s (k + 1)

/-- At `0x8000d5c0`, every pass done. -/
structure Last (s u : MachineState) (P nx : Word) : Prop extends Res s u P nx where
  pc : u.pc = 0x8000d5c0
  x19 : u.getReg .x19 ≠ 0
  x21 : u.getReg .x21 = P
  val : eAt u P = (cur s (nn s)).getD 0 0

end Rv64Verifier.Proofs.Multilinear.MleEval
