/-
  LeanVM.Guest.B1.VerifySub.Ood

  `verify_sub`'s out-of-domain sample: the grind, the point, the value and the bus
  grind's nonce.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.GrindOff
public import LeanVM.Guest.B1.Fs.SqueezePoint
public import LeanVM.Guest.B1.Fs.MessageComplete
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The out-of-domain sample

`vsOodT_holds`: the nonce at stream offset `10` absorbed after the root's two words and permuted
(`Fs.nonceState`), its proof of work checked by the inlined `grind_check` (`gcInlineO_sound`), the point `z` of the stack's
`m` variables (the ground challenge, then `squeeze_point_from__L{m}`), the value `v` read by
`opening_message__L1_L1` with the bus grind's nonce `nn`: `readOod m` runs on `[nonce, v]`, and
the message's returns are the cells and capacity of the value's nonce permutation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## Squeezes and samples -/

theorem vs_squeezeN_length : ∀ (k : ℕ) (s : Fs), (s.squeezeN k).1.length = k
  | 0, _ => rfl
  | k + 1, s => by simp [Fs.squeezeN, vs_squeezeN_length k]

theorem vs_squeezeN_pend : ∀ (k : ℕ) (s : Fs), s.pend = [] → (s.squeezeN k).2.pend = []
  | 0, _, h => h
  | k + 1, s, _ => vs_squeezeN_pend k s.squeeze.2 rfl

/-- **`k + 1` samples from a ground challenge** `c` at the capacity `cap`: `c`, then `k` squeezed
from `cap`. -/
theorem runsFromG_sampleN_succ (k : ℕ) (cap : List E) (c : E) :
    RunsFromG (VerifierProgram.sampleChallenges (k + 1)) cap c []
      (c :: ((⟨cap, []⟩ : Fs).squeezeN k).1) ((⟨cap, []⟩ : Fs).squeezeN k).2 := by
  have h := (runsFromG_sample cap c).bind
    (f := fun x ↦ do let xs ← VerifierProgram.sampleChallenges k; return x :: xs)
    ((runsTo_sampleN k ⟨cap, []⟩).bind
      (f := fun xs ↦ (pure (c :: xs) : VerifierProgram (List E))) (runsTo_ret _ _))
  simpa [VerifierProgram.sampleChallenges] using h

/-! ## The nonce's permutation -/

/-- The nonce's permutation after the root's two words. -/
abbrev vsAtom288 : Atom :=
  .keccak [.n (val% «verify_sub» "rate[0]@3"), .n (val% «verify_sub» "rate[1]@3"), .n (val% «verify_sub» "rate[2]@3"), .n (val% «verify_sub» "rate[3]@3"), .n (val% «verify_sub» "rate[4]@3"), .n (val% «verify_sub» "rate[5]@3"), .n (val% «verify_sub» "rate[6]@3"), .n (val% «verify_sub» "rate[7]@3"), .n (val% «verify_sub» "nxt[8]@2"), .n (val% «verify_sub» "nxt[9]@2"),
    .n (val% «verify_sub» "nxt[10]@2"), .n (val% «verify_sub» "nxt[11]@2"), .n (val% «verify_sub» "nxt[12]@2")] (vsRun 288 13) false false

theorem vs_oodPerm (w268 : WordAt rd σ 8 268) (w271 : WordAt rd σ 9 271)
    (hn : FsPackOk σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0")) 284 dsPowNonce) (h286 : σ (.n (val% «verify_sub» "rate[6]@3")) = 0) (h287 : σ (.n (val% «verify_sub» "rate[7]@3")) = 0)
    (hk : vsAtom288.Holds rd σ) :
    cells13 ((vsRun 288 13).map σ) =
      cellsOfState ((⟨[σ (.n (val% «verify_sub» "nxt[8]@2")), σ (.n (val% «verify_sub» "nxt[9]@2")), σ (.n (val% «verify_sub» "nxt[10]@2")), σ (.n (val% «verify_sub» "nxt[11]@2")), σ (.n (val% «verify_sub» "nxt[12]@2"))],
        [(σ (.n (val% «verify_sub» "x@9")), dsObserve), (σ (.n (val% «verify_sub» "x@10")), dsObserve)]⟩ : Fs).nonceState (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0")))) false := by
  obtain ⟨-, -, hc⟩ := keccakA_perm hk
  have c0 := wordAt_cells w268
  have c1 := wordAt_cells w271
  have c2 := fsPackT_cells hn
  have e : (⟨[σ (.n (val% «verify_sub» "nxt[8]@2")), σ (.n (val% «verify_sub» "nxt[9]@2")), σ (.n (val% «verify_sub» "nxt[10]@2")), σ (.n (val% «verify_sub» "nxt[11]@2")), σ (.n (val% «verify_sub» "nxt[12]@2"))],
      [(σ (.n (val% «verify_sub» "x@9")), dsObserve), (σ (.n (val% «verify_sub» "x@10")), dsObserve)]⟩ : Fs).nonceState (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0"))) =
      permOf (rateOf [(σ (.n (val% «verify_sub» "x@9")), dsObserve), (σ (.n (val% «verify_sub» "x@10")), dsObserve), (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0")), dsPowNonce)] ++
        [σ (.n (val% «verify_sub» "nxt[8]@2")), σ (.n (val% «verify_sub» "nxt[9]@2")), σ (.n (val% «verify_sub» "nxt[10]@2")), σ (.n (val% «verify_sub» "nxt[11]@2")), σ (.n (val% «verify_sub» "nxt[12]@2"))]) := by
    simp [Fs.nonceState, Fs.absorb, Fs.perm, rateScalars]
  have hl : rateOf [(σ (.n (val% «verify_sub» "x@9")), dsObserve), (σ (.n (val% «verify_sub» "x@10")), dsObserve), (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0")), dsPowNonce)] ++
      [σ (.n (val% «verify_sub» "nxt[8]@2")), σ (.n (val% «verify_sub» "nxt[9]@2")), σ (.n (val% «verify_sub» "nxt[10]@2")), σ (.n (val% «verify_sub» "nxt[11]@2")), σ (.n (val% «verify_sub» "nxt[12]@2"))] =
      List.map σ [.n (val% «verify_sub» "rate[0]@3"), .n (val% «verify_sub» "rate[1]@3"), .n (val% «verify_sub» "rate[2]@3"), .n (val% «verify_sub» "rate[3]@3"), .n (val% «verify_sub» "rate[4]@3"), .n (val% «verify_sub» "rate[5]@3"), .n (val% «verify_sub» "rate[6]@3"), .n (val% «verify_sub» "rate[7]@3"), .n (val% «verify_sub» "nxt[8]@2"), .n (val% «verify_sub» "nxt[9]@2"),
        .n (val% «verify_sub» "nxt[10]@2"), .n (val% «verify_sub» "nxt[11]@2"), .n (val% «verify_sub» "nxt[12]@2")] := by
    rw [rateOf_three, ← c0, ← c1, ← c2]
    simp only [List.map_cons, List.map_nil, h286, h287]
    rfl
  rw [hc, e, hl]

/-! ## The section -/

/-- The sponge with the root's two words waiting. -/
abbrev vsRootFs (σ : Val) : Fs :=
  ⟨[σ (.n (val% «verify_sub» "nxt[8]@2")), σ (.n (val% «verify_sub» "nxt[9]@2")), σ (.n (val% «verify_sub» "nxt[10]@2")), σ (.n (val% «verify_sub» "nxt[11]@2")), σ (.n (val% «verify_sub» "nxt[12]@2"))],
    [(σ (.n (val% «verify_sub» "x@9")), dsObserve), (σ (.n (val% «verify_sub» "x@10")), dsObserve)]⟩


theorem vsRun356 : (vsRun 356 5).map σ =
    [σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")), σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")), σ (.n (val% «verify_sub» "fs4@1"))] := rfl

theorem spfName_eq {m : ℕ} (h1 : 20 ≤ m) (h2 : m ≤ 30) (h : m - 20 < vsSqpNames.length) :
    vsSqpNames[m - 20] = spfName m := by
  interval_cases m <;> rfl

theorem spf_mem {m : ℕ} (h1 : 20 ≤ m) (h2 : m ≤ 30) : m ∈ spfDeployed :=
  List.mem_map.2 ⟨m - 6, List.mem_range.2 (by omega), by omega⟩

theorem word_g11 : word 2048 0 = gen ^ 11 := by
  rw [show (2048 : ℕ) = 2 ^ 11 from rfl]; exact word_two_pow (by norm_num)

/-- **The out-of-domain sample**. -/
theorem vsOodT_holds {κ : ℕ} (hκ : κ ≤ 32) (hκw : winTabBits ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (hwin : ExpWinTab L.read (σ (.n (val% «verify_sub» "g_squares"))))
    {m : ℕ} (hm20 : 20 ≤ m) (hm30 : m ≤ 30) (h278 : σ (.n (val% «verify_sub» "size_sel")) = gen ^ (m - 20))
    (w268 : WordAt L.read σ 8 268) (w271 : WordAt L.read σ 9 271)
    (h : Stmt.HoldsList C L.read σ vsOodT next kret) :
    ∃ (z : List E) (v nn : E),
      RunsTo (readOod m) ⟨[σ (.n (val% «verify_sub» "nxt[8]@2")), σ (.n (val% «verify_sub» "nxt[9]@2")), σ (.n (val% «verify_sub» "nxt[10]@2")), σ (.n (val% «verify_sub» "nxt[11]@2")), σ (.n (val% «verify_sub» "nxt[12]@2"))],
          [(σ (.n (val% «verify_sub» "x@9")), dsObserve), (σ (.n (val% «verify_sub» "x@10")), dsObserve)]⟩
        [σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0")), v] (fun x ↦ eqEval z x, v)
        ⟨[σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")), σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")), σ (.n (val% «verify_sub» "fs4@1"))], [(v, dsObserve)]⟩ ∧
      z.length = m ∧ ReadsAt L.read (σ (.n (val% «verify_sub» "ood_z"))) z ∧ ReadsAt L.read (σ (.n (val% «verify_sub» "ood_value"))) [v] ∧
      LoadHolds L.read (σ (.n (val% «verify_sub» "stream"))) 10 (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0"))) ∧ σ (.n (val% «verify_sub» "word0~9")) = σ (.n (val% «verify_sub» "stream")) * gen ^ 11 ∧
      LoadHolds L.read (σ (.n (val% «verify_sub» "word0~9"))) 0 v ∧ LoadHolds L.read (σ (.n (val% «verify_sub» "word0~9"))) 1 nn ∧
      [σ (.n (val% «verify_sub» "word0")), σ (.n (val% «verify_sub» "pow_word")), σ (.n (val% «verify_sub» "fs0@2")), σ (.n (val% «verify_sub» "fs1@2")), σ (.n (val% «verify_sub» "fs2@2")), σ (.n (val% «verify_sub» "fs3@2")), σ (.n (val% «verify_sub» "fs4@2")),
          σ (.n (val% «verify_sub» "cursor@1"))] =
        [cellsOfState ((⟨[σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")), σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")), σ (.n (val% «verify_sub» "fs4@1"))],
            [(v, dsObserve)]⟩ : Fs).nonceState nn) false 0,
          cellsOfState ((⟨[σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")), σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")), σ (.n (val% «verify_sub» "fs4@1"))],
            [(v, dsObserve)]⟩ : Fs).nonceState nn) false 1] ++
          capOf ((⟨[σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")), σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")), σ (.n (val% «verify_sub» "fs4@1"))],
            [(v, dsObserve)]⟩ : Fs).nonceState nn) ++ [σ (.n (val% «verify_sub» "word0~9")) * gen ^ 2] ∧ next := by
  rw [vsOodT] at h
  simp only [holdsList_append] at h
  obtain ⟨⟨l283, hn⟩, h⟩ := (holds_fsNonceT _ _ _ _ _).1 h
  obtain ⟨⟨h286, h287⟩, h⟩ := (holds_zero2T _ _ _).1 h
  obtain ⟨hk, h⟩ := holds_atom1.1 h
  obtain ⟨hpow, h⟩ := gcInlineO_sound hκ hκw L (by decide) (winTabs_of_expWinTab hwin) h
  simp only [Stmt.HoldsList, Stmt.Holds, vsAlloc, vsConst, vsMul, vsCall,
    Atom.Holds, List.map_cons, List.map_nil, range8] at h
  obtain ⟨-, ⟨j, hj, hj278, hsp⟩, -, e311, m312, hom, hn'⟩ := h
  -- the nonce's permutation
  have hc := vs_oodPerm w268 w271 hn h286 h287 hk
  obtain ⟨S, hS⟩ : ∃ S, (vsRootFs σ).nonceState (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0"))) = S := ⟨_, rfl⟩
  rw [hS] at hc
  have e288 : σ (.n (val% «verify_sub» "nxt[0]@3")) = cellsOfState S false 0 := congrFun hc 0
  have e289 : σ (.n (val% «verify_sub» "nxt[1]@3")) = cellsOfState S false 1 := congrFun hc 1
  have e296 : σ (.n (val% «verify_sub» "nxt[8]@3")) = cellsOfState S false 8 := congrFun hc 8
  have e297 : σ (.n (val% «verify_sub» "nxt[9]@3")) = cellsOfState S false 9 := congrFun hc 9
  have e298 : σ (.n (val% «verify_sub» "nxt[10]@3")) = cellsOfState S false 10 := congrFun hc 10
  have e299 : σ (.n (val% «verify_sub» "nxt[11]@3")) = cellsOfState S false 11 := congrFun hc 11
  have e300 : σ (.n (val% «verify_sub» "nxt[12]@3")) = cellsOfState S false 12 := congrFun hc 12
  have hcapS : [σ (.n (val% «verify_sub» "nxt[8]@3")), σ (.n (val% «verify_sub» "nxt[9]@3")), σ (.n (val% «verify_sub» "nxt[10]@3")), σ (.n (val% «verify_sub» "nxt[11]@3")), σ (.n (val% «verify_sub» "nxt[12]@3"))] = capOf S := by
    rw [capOf, e296, e297, e298, e299, e300]
  -- the grind
  have hok : powOk 15 (Keccak.lane ((vsRootFs σ).nonceState (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0")))) 2) = true := by
    refine ((grindOk_iff (s := vsRootFs σ) (bits := 15) (by decide) (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0")))).2 ?_).resolve_left
      (by decide)
    rw [hS, ← e289]
    exact hpow
  have hG := runsToG_grind (bits := Whir.oodGrindingBits) (by decide) (vsRootFs σ) (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0"))) hok
  rw [hS] at hG
  have h303 : σ (.n (val% «verify_sub» "nxt[0]@3")) = challengeOf S := by rw [e288, Keccak.challengeOf_cells]
  -- the point
  have hj7 : j < 11 := by simpa [vsSqpNames] using hj
  have hjm : j = m - 20 := by
    rw [h278, gen_pow_eq_ofK] at hj278
    exact (gen_pow_inj (by omega) (by omega)
      (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK]; exact hj278)).symm
  subst hjm
  rw [spfName_eq hm20 hm30 hj, vsRun356] at hsp
  obtain ⟨hz, hret⟩ := (squeeze_point_from_holds m (spf_mem hm20 hm30) L.read _ _).1 (hC _ _ _ hsp)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hz hret
  rw [h303, hcapS] at hz
  rw [hcapS] at hret
  have hT : ((⟨capOf S, []⟩ : Fs).squeezeN k).2 =
      ⟨[σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")), σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")), σ (.n (val% «verify_sub» "fs4@1"))], []⟩ := by
    have hp := vs_squeezeN_pend k ⟨capOf S, []⟩ rfl
    revert hp hret
    generalize ((⟨capOf S, []⟩ : Fs).squeezeN k).2 = T
    obtain ⟨c, p⟩ := T
    rintro hp hret
    simp only at hp hret
    rw [hp, hret]
  -- the value and the bus grind's nonce
  obtain ⟨xs, hxl, hxc, hxo, nn, hnn, hrets⟩ :=
    (opening_message_holds (1, 1) (by decide) L.read _ _).1 (hC _ _ _ hom)
  dsimp only at hxl hnn hrets
  obtain ⟨v, rfl⟩ : ∃ v, xs = [v] := by
    match xs, hxl with
    | [v], _ => exact ⟨v, rfl⟩
  have e312 : σ (.n (val% «verify_sub» "word0~9")) = σ (.n (val% «verify_sub» "stream")) * gen ^ 11 := by rw [m312, e311, word_g11]
  refine ⟨challengeOf S :: ((⟨capOf S, []⟩ : Fs).squeezeN k).1, v, nn, ?_,
    by simp [vs_squeezeN_length], hz, hxo, l283, e312, hxc 0 (by simp), hnn rfl, ?_, hn'⟩
  · -- the run
    have h3 := (runsTo_readE ((⟨capOf S, []⟩ : Fs).squeezeN k).2 v).bind
      (f := fun value ↦ (pure (fun x ↦ eqEval (challengeOf S :: ((⟨capOf S, []⟩ : Fs).squeezeN k).1)
        x, value) : VerifierProgram StackClaim)) (runsTo_ret _ _)
    have h2 := (runsFromG_sampleN_succ k (capOf S) (challengeOf S)).bind
      (f := fun z ↦ do
        let value ← VerifierProgram.readScalar
        return ((fun x ↦ eqEval z x, value) : StackClaim)) h3
    have h1 := hG.bindFrom
      (f := fun _ ↦ do
        let z ← VerifierProgram.sampleChallenges (k + 1)
        let value ← VerifierProgram.readScalar
        return ((fun x ↦ eqEval z x, value) : StackClaim)) h2
    refine h1.of_eq rfl (by simp) rfl ?_
    rw [hT]
    simp [Fs.absorb, rateScalars]
  · rw [hrets]
    rfl

end
end LeanVM.Guest.B1.VerifySub
