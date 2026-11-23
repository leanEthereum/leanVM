module

public import NativeRustcVmX64.Wire.PhaseM.Checks

/-!
# `phase_m`: what holds from the rows on (x86-64)

`Mid`: the model's phase now `climbFin` of the rows read, the sizes, the frame's words (the leaf
width at `16`, the height at `32`, the query count at `40`, the leaves' address at `56`), the
queries, the positions and the leaves in the working area. `Wr`: what a later step may change (the
stack below the frame's word `16`, its words `24` and `64` to `112`, the reader's cursor, the
phase, the working area between the positions and the leaves); `Mid.keep`: `Mid` kept by such a
change. Nodes, leaves and levels of siblings kept by changes missing them, by numbers.
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- What a step from the rows on may change. -/
def Wr (m0 : MachineData) (q : BitVec 64) : Prop :=
  (SP0 m0 - 1216 ≤ q.toNat ∧ q.toNat < SP0 m0 - 144) ∨
    (SP0 m0 - 136 ≤ q.toNat ∧ q.toNat < SP0 m0 - 128) ∨
    (SP0 m0 - 96 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) ∨
    ((RD m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (RD m0).toNat + 24) ∨
    ((OUT m0).toNat ≤ q.toNat ∧ q.toNat < (OUT m0).toNat + 395288) ∨
    ((WK m0).toNat + 4096 ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 352512)

/-- **What holds from the rows on.** -/
structure Mid (m0 : MachineData) (B : List UInt8) (c : Nat) (count : Nat)
    (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 : Nat) (d : Mem 64) : Prop where
  model : phaseM B c = climbFin B qs height lw rows c6
  len : qs.length = count
  cnt0 : 0 < count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  h32 : height ≤ 32
  lw64 : lw ≤ 64
  ps0 : 0 < (sortD qs).length
  ps256 : (sortD qs).length ≤ 256
  rlen : rows.length = (sortD qs).length
  rw : ∀ r ∈ rows, r.length ≤ lw
  f16 : FW m0 d 16 lw.toUInt64
  f32 : FW m0 d 32 height.toUInt64
  f40 : FW m0 d 40 count.toUInt64
  f56 : FW m0 d 56 (UInt64.ofBitVec (wa m0 352512))
  qsW : NativeRustcVm.WordsAt d (wa m0 0) (qs.map Nat.toUInt64)
  psW : NativeRustcVm.WordsAt d (wa m0 2048) ((sortD qs).map Nat.toUInt64)
  lvW : LeavesAt d (wa m0 352512) (leavesOf lw rows)

end

public section

theorem add_off (a : BitVec 64) (j : Nat) :
    BinOp.apply .add .W64 a (BitVec.ofNat 64 j) = off a j := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem add_off' (a : BitVec 64) (j : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 j) a = off a j := by
  simp only [BinOp.apply, low_W64, ext_W64]; rw [BitVec.add_comm]

theorem length_digest (x : Digest) : x.toList.length = 4 := by simp

/-- **Leaves kept** by a change missing them. -/
theorem leaves_keep {d d' : Mem 64} {a : BitVec 64} {l : List (List K)} {R : BitVec 64 → Prop}
    (h : LeavesAt d a l) (hs : NativeRustcVm.SameOutside d d' R) (hw : ∀ x ∈ l, x.length ≤ 64)
    (hnw : a.toNat + 512 * l.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 512 * l.length ≤ q.toNat) :
    LeavesAt d' a l := fun i hi ↦ by
  have hx := hw _ (List.getElem_mem hi)
  have ho : (off a (512 * i)).toNat = a.toNat + 512 * i := toNat_off (by omega)
  refine wordsAt_keep (h i hi) hs (by rw [List.length_map, ho]; omega) fun q hq ↦ ?_
  rw [List.length_map, ho]
  have := hR q hq
  omega

/-- **A node kept** by a change missing it. -/
theorem node_keep {d d' : Mem 64} {a : BitVec 64} {x : Nat × Digest} {R : BitVec 64 → Prop}
    (h : NodeAt d a x) (hs : NativeRustcVm.SameOutside d d' R) (hnw : a.toNat + 40 ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 40 ≤ q.toNat) : NodeAt d' a x := by
  obtain ⟨h1, h2, h3⟩ := h
  have ho : (off a 8).toNat = a.toNat + 8 := toNat_off (by omega)
  refine ⟨h1, wordAt_keep h2 hs (by omega) fun q hq ↦ by have := hR q hq; omega,
    wordsAt_keep h3 hs (by rw [ho, length_digest]; omega) fun q hq ↦ ?_⟩
  rw [ho, length_digest]
  have := hR q hq
  omega

/-- **Nodes kept** by a change missing them. -/
theorem nodes_keep {d d' : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)}
    {R : BitVec 64 → Prop} (h : NodesAt d a l) (hs : NativeRustcVm.SameOutside d d' R)
    (hnw : a.toNat + 40 * l.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 40 * l.length ≤ q.toNat) :
    NodesAt d' a l := fun i hi ↦ by
  have ho : (off a (40 * i)).toNat = a.toNat + 40 * i := toNat_off (by omega)
  refine node_keep (h i hi) hs (by rw [ho]; omega) fun q hq ↦ ?_
  rw [ho]
  have := hR q hq
  omega

/-- **One node more.** -/
theorem nodes_snoc {d : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)} {x : Nat × Digest}
    (h : NodesAt d a l) (hx : NodeAt d (off a (40 * l.length)) x) : NodesAt d a (l ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]; exact h j hj
  · rw [List.getElem_append_right (le_refl _)]
    simpa using hx

/-- **Levels of siblings kept** by a change missing them. -/
theorem sibs_keep {d d' : Mem 64} {a cnt : BitVec 64} {l : List (List (Nat × Digest))}
    {R : BitVec 64 → Prop} (h : SibsAt d a cnt l) (hs : NativeRustcVm.SameOutside d d' R)
    (hnw : a.toNat + 10240 * l.length ≤ 2 ^ 64) (hcw : cnt.toNat + 8 * l.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < a.toNat ∨ a.toNat + 10240 * l.length ≤ q.toNat)
    (hC : ∀ q, R q → q.toNat < cnt.toNat ∨ cnt.toNat + 8 * l.length ≤ q.toNat) :
    SibsAt d' a cnt l := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h j hj
  have hc : (off cnt (8 * j)).toNat = cnt.toNat + 8 * j := toNat_off (by omega)
  have ha : (off a (nodesBytes * j)).toNat = a.toNat + 10240 * j := toNat_off (by
    unfold nodesBytes; omega)
  refine ⟨h1, wordAt_keep h2 hs (by rw [hc]; omega) fun q hq ↦ ?_,
    nodes_keep h3 hs (by rw [ha]; omega) fun q hq ↦ ?_⟩
  · rw [hc]; have := hC q hq; omega
  · rw [ha]; have := hR q hq; omega

/-- **One level more** of siblings. -/
theorem sibs_snoc {d : Mem 64} {a cnt : BitVec 64} {l : List (List (Nat × Digest))}
    {x : List (Nat × Digest)} (h : SibsAt d a cnt l) (hx : x.length ≤ 256)
    (hc : NativeRustcVm.WordAt d (off cnt (8 * l.length)) x.length.toUInt64)
    (hn : NodesAt d (off a (nodesBytes * l.length)) x) : SibsAt d a cnt (l ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]; exact h j hj
  · rw [List.getElem_append_right (le_refl _)]
    simpa using ⟨hx, hc, hn⟩

variable {m0 : MachineData} {bp : BitVec 64} {L : Nat}

section
variable [Labels]

theorem Wr.chg (G : Geo m0 bp L) {q : BitVec 64} (h : Wr m0 q) : Chg m0 q := by
  have := G.sp
  unfold Wr at h
  unfold Chg
  omega


/-- **What holds is kept** by a change of what a later step may change. -/
theorem Mid.keep (G : Geo m0 bp L) {B : List UInt8} {c count : Nat} {qs : List Nat}
    {height lw : Nat} {rows : List (List K)} {c6 : Nat} {d d' : Mem 64}
    (h : Mid m0 B c count qs height lw rows c6 d) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) (hR : ∀ q, R q → Wr m0 q) :
    Mid m0 B c count qs height lw rows c6 d' := by
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsR := G.sR
  have hsO := G.sO
  have hsW := G.sW
  have hrW := G.rW
  have hoW := G.oW
  have hrn := G.rNw
  have hon := G.oNw
  have hql := h.len
  have hps := h.ps256
  have hrl := h.rlen
  have hcnt := h.cnt
  have hR' : ∀ q, R q → (SP0 m0 - 1216 ≤ q.toNat ∧ q.toNat < SP0 m0 - 144) ∨
      (SP0 m0 - 136 ≤ q.toNat ∧ q.toNat < SP0 m0 - 128) ∨
      (SP0 m0 - 96 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) ∨
      ((RD m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (RD m0).toNat + 24) ∨
      ((OUT m0).toNat ≤ q.toNat ∧ q.toNat < (OUT m0).toNat + 395288) ∨
      ((WK m0).toNat + 4096 ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 352512) := hR
  have hf : ∀ o v, o = 16 ∨ o = 32 ∨ o = 40 ∨ o = 56 → FW m0 d o v → FW m0 d' o v :=
    fun o v ho hf ↦ hf.keep G (by omega) hs fun q hq ↦ by
      have := hR' q hq
      omega
  have hw0 := G.wa (o := 0) (by omega)
  have hw2 := G.wa (o := 2048) (by omega)
  have hw3 := G.wa (o := 352512) (by omega)
  refine ⟨h.model, hql, h.cnt0, hcnt, h.qlt, h.h32, h.lw64, h.ps0, hps, hrl, h.rw,
    hf _ _ (by omega) h.f16, hf _ _ (by omega) h.f32, hf _ _ (by omega) h.f40,
    hf _ _ (by omega) h.f56, ?_, ?_, ?_⟩
  · refine wordsAt_keep h.qsW hs (by rw [List.length_map, hw0]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw0]
    have := hR' q hq
    omega
  · refine wordsAt_keep h.psW hs (by rw [List.length_map, hw2]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw2]
    have := hR' q hq
    omega
  · have hl : (leavesOf lw rows).length = (sortD qs).length := by simp [hrl]
    refine leaves_keep h.lvW hs (fun x hx ↦ ?_) (by rw [hl, hw3]; omega) fun q hq ↦ ?_
    · simp only [leavesOf, List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [length_paddedLeaf (h.rw r hr)]; exact h.lw64
    · rw [hl, hw3]
      have := hR' q hq
      omega

end

end

end NativeRustcVmX64.Wire.PhaseM
