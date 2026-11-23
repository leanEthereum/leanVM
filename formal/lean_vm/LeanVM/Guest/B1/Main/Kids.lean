/-
  LeanVM.Guest.B1.Main.Kids

  What each child of `main` establishes, its records named: the digest family's statements
  applied to the calls of `main_loop4`.
-/

module

public import LeanVM.Guest.B1.Main.Cover
public import LeanVM.Guest.B1.Digest.Statement
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main»

/-!
# The children's records

`KidStepC` (`main_loop4`'s iteration) names the calls; with the digest family's statements
(`child_claim_list_digest_sound`, `statement_digest_sound`) each child's records are values
(`KidRec`) with their facts (`KidOk`): its leanXMSS and leanSPHINCS claims' slots and cells, its
lists' digests, its DA digest's cells at `da_digests · g^(2c)`, its statement's digest at
`child_pi`, its proof's check, and the running counts.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

/-- A child's records. -/
structure KidRec where
  base : E
  cx0 : E
  cx1 : E
  cs0 : E
  cs1 : E
  d0 : E
  d1 : E
  p0 : E
  p1 : E
  ex : ℕ
  es : ℕ
  ox : ℕ → ℕ
  cellsx : List E
  os : ℕ → ℕ
  cellss : List E
  defer : List E
  /-- The leanXMSS list is gap-walked (`child_claim_list_mono`): one mark, increasing slots. -/
  mx : Bool
  /-- The leanSPHINCS list is gap-walked. -/
  ms : Bool

/-- **What child `c` establishes.** -/
structure KidOk (C : CallRel) (rd : Reader) (σ : Val) (c : ℕ) (k : KidRec) : Prop where
  base : LoadHolds rd (σ (.n (val% «main» "written"))) c k.base
  next : LoadHolds rd (σ (.n (val% «main» "written"))) (c + 1) (k.base * (gen ^ k.ex * gen ^ k.es))
  bounds : k.ex < 2 ^ 32 ∧ k.es < 2 ^ 32
  xlen : k.cellsx.length = 4 * k.ex
  xrec : ∀ j < k.ex, SlotBelow (σ (.n (val% «main» "lx_slots_g"))) (k.ox j) ∧
    LoadHolds rd (σ (.n (val% «main» "cover"))) (k.ox j) (k.base * gen ^ (if k.mx then 0 else j)) ∧
    ∀ i < 4, LoadHolds rd (σ (.n (val% «main» "lx_table"))) (4 * k.ox j + i) (k.cellsx.getD (4 * j + i) 0)
  xmono : k.mx = true → ∀ i j, i < j → j < k.ex → k.ox i < k.ox j
  xdig : [k.cx0, k.cx1] = digestCells (keccak256 (cellsBytes k.cellsx))
  slen : k.cellss.length = 4 * k.es
  srec : ∀ j < k.es, SlotBelow (σ (.n (val% «main» "lean_sphincs_slots_g"))) (k.os j) ∧
    LoadHolds rd (σ (.n (val% «main» "sp_cover"))) (k.os j) (k.base * gen ^ k.ex * gen ^ (if k.ms then 0 else j)) ∧
    ∀ i < 4, LoadHolds rd (σ (.n (val% «main» "lean_sphincs_table"))) (4 * k.os j + i) (k.cellss.getD (4 * j + i) 0)
  smono : k.ms = true → ∀ i j, i < j → j < k.es → k.os i < k.os j
  sdig : [k.cs0, k.cs1] = digestCells (keccak256 (cellsBytes k.cellss))
  da0 : LoadHolds rd (σ (.n (val% «main» "da_digests"))) (2 * c) k.d0
  da1 : LoadHolds rd (σ (.n (val% «main» "da_digests"))) (2 * c + 1) k.d1
  deflen : k.defer.length = 24
  defreads : ReadsAt rd (σ (.n (val% «main» "child_carried")) * gen ^ (24 * c)) k.defer
  pdig : [k.p0, k.p1] = digestCells (keccak256
    (stmtBytes [σ (.n (val% «main» "fs_seed[0]")), σ (.n (val% «main» "fs_seed[1]")), k.cx0, k.cx1, k.cs0, k.cs1, k.d0, k.d1] k.defer))
  pi0 : LoadHolds rd (σ (.n (val% «main» "child_pi"))) (2 * c) k.p0
  pi1 : LoadHolds rd (σ (.n (val% «main» "child_pi"))) (2 * c + 1) k.p1
  sub : C "verify_sub"
    [k.p0, k.p1, σ (.n (val% «main» "fs_seed[0]")), σ (.n (val% «main» "fs_seed[1]")), σ (.n (val% «main» "g_squares")), σ (.n (val% «main» "child_fresh")) * gen ^ (24 * c)] []

theorem loadHolds_gen_pow_iff {rd : Reader} {p : E} {c k : ℕ} {w : E} :
    LoadHolds rd (p * gen ^ c) k w ↔ LoadHolds rd p (c + k) w :=
  loadHolds_mul_gen_pow rd p c k w

/-- **Each child's records.** -/
theorem kid_rec {rd : Reader} (hm : MemOk rd) {σ : Val} (MF : MainFacts C rd σ) :
    ∀ c < lg σ 6, ∃ k : KidRec, KidOk C rd σ c k := by
  intro c hc
  obtain ⟨base, cx0, cx1, cs0, cs1, d0, d1, p0, p1, ex, es, hb, hex, hes, hcx, hcs, hd0, hd1, hsd,
    hp0, hp1, hsub, hnext⟩ := MF.children c hc
  -- the leanXMSS records
  obtain ⟨mx, ox, cellsx, hlx, hmonox, hrecx, hdigx⟩ :=
    child_claim_list_digest_sound rd hm _ _ hcx ex (by omega) rfl
  -- the leanSPHINCS records
  obtain ⟨ms, os, cellss, hls, hmonos, hrecs, hdigs⟩ :=
    child_claim_list_digest_sound rd hm _ _ hcs es (by omega) rfl
  -- the statement's digest
  obtain ⟨defer, hdlen, hdefr, hpdig⟩ := statement_digest_sound rd _ _ hsd
  refine ⟨⟨base, cx0, cx1, cs0, cs1, d0, d1, p0, p1, ex, es, ox, cellsx, os, cellss, defer, mx, ms⟩,
    ?_⟩
  refine ⟨?_, ?_, ⟨hex, hes⟩, hlx, hrecx, hmonox, hdigx, hls, hrecs, hmonos, hdigs,
    ?_, ?_, hdlen, ?_, hpdig, ?_, ?_, ?_⟩
  · have := loadHolds_gen_pow_iff.mp hb; simpa using this
  · have := loadHolds_gen_pow_iff.mp hnext; exact this
  · rw [gen_pow_pow] at hd0
    have := loadHolds_gen_pow_iff.mp hd0
    simpa using this
  · rw [gen_pow_pow] at hd1
    exact loadHolds_gen_pow_iff.mp hd1
  · rwa [gen_pow_pow] at hdefr
  · rw [gen_pow_pow] at hp0
    have := loadHolds_gen_pow_iff.mp hp0
    simpa using this
  · rw [gen_pow_pow] at hp1
    exact loadHolds_gen_pow_iff.mp hp1
  · rwa [gen_pow_pow] at hsub

end
end LeanVM.Guest.B1.Main
