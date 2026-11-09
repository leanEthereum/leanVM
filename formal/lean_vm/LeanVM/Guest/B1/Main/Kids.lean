/-
  LeanVM.Guest.B1.Main.Kids

  What each child of `main` establishes, its records named: the digest family's statements
  applied to the calls of `__loop4`.
-/

module

public import LeanVM.Guest.B1.Main.Cover
public import LeanVM.Guest.B1.Digest.Statement

/-!
# The children's records

`KidStepC` (`__loop4`'s iteration) names the calls; with the digest family's statements
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
  base : LoadHolds rd (σ (.n 420)) c k.base
  next : LoadHolds rd (σ (.n 420)) (c + 1) (k.base * (gen ^ k.ex * gen ^ k.es))
  bounds : k.ex ≤ 65535 ∧ k.es ≤ 65535
  xlen : k.cellsx.length = 4 * k.ex
  xcan : AllCanonical k.cellsx
  xrec : ∀ j < k.ex, SlotBelow (σ (.n 40)) (k.ox j) ∧
    LoadHolds rd (σ (.n 66)) (k.ox j) (k.base * gen ^ (if k.mx then 0 else j)) ∧
    ∀ i < 4, LoadHolds rd (σ (.n 52)) (4 * k.ox j + i) (k.cellsx.getD (4 * j + i) 0)
  xmono : k.mx = true → ∀ i j, i < j → j < k.ex → k.ox i < k.ox j
  xdig : [k.cx0, k.cx1] = digestCells (keccak256 (cellsBytes k.cellsx))
  slen : k.cellss.length = 4 * k.es
  scan : AllCanonical k.cellss
  srec : ∀ j < k.es, SlotBelow (σ (.n 41)) (k.os j) ∧
    LoadHolds rd (σ (.n 67)) (k.os j) (k.base * gen ^ k.ex * gen ^ (if k.ms then 0 else j)) ∧
    ∀ i < 4, LoadHolds rd (σ (.n 55)) (4 * k.os j + i) (k.cellss.getD (4 * j + i) 0)
  smono : k.ms = true → ∀ i j, i < j → j < k.es → k.os i < k.os j
  sdig : [k.cs0, k.cs1] = digestCells (keccak256 (cellsBytes k.cellss))
  da0 : LoadHolds rd (σ (.n 385)) (2 * c) k.d0
  da1 : LoadHolds rd (σ (.n 385)) (2 * c + 1) k.d1
  deflen : k.defer.length = 24
  defreads : ReadsAt rd (σ (.n 417) * gen ^ (24 * c)) k.defer
  hdrcan : AllCanonical [σ (.n 47), σ (.n 48), k.cx0, k.cx1, k.cs0, k.cs1, k.d0, k.d1]
  pdig : [k.p0, k.p1] = digestCells (keccak256
    (stmtBytes [σ (.n 47), σ (.n 48), k.cx0, k.cx1, k.cs0, k.cs1, k.d0, k.d1] k.defer))
  pi0 : LoadHolds rd (σ (.n 405)) (2 * c) k.p0
  pi1 : LoadHolds rd (σ (.n 405)) (2 * c + 1) k.p1
  sub : C "verify_sub"
    [k.p0, k.p1, σ (.n 47), σ (.n 48), σ (.n 49), σ (.n 411) * gen ^ (24 * c)] []

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
  obtain ⟨nx, hnx, hgx, mx, ox, cellsx, hlx, hcanx, hmonox, hrecx, hdigx⟩ :=
    child_claim_list_digest_sound rd hm _ _ hcx
  have hnx' : nx < 8912896 := hnx
  have hexn := gen_pow_inj34 (by omega) (by omega) hgx
  subst hexn
  -- the leanSPHINCS records
  obtain ⟨ns, hns, hgs, ms, os, cellss, hls, hcans, hmonos, hrecs, hdigs⟩ :=
    child_claim_list_digest_sound rd hm _ _ hcs
  have hns' : ns < 8912896 := hns
  have hesn := gen_pow_inj34 (by omega) (by omega) hgs
  subst hesn
  -- the statement's digest
  obtain ⟨defer, hdlen, hdefr, hhdr, hpdig⟩ := statement_digest_sound rd _ _ hsd
  refine ⟨⟨base, cx0, cx1, cs0, cs1, d0, d1, p0, p1, ex, es, ox, cellsx, os, cellss, defer, mx, ms⟩,
    ?_⟩
  refine ⟨?_, ?_, ⟨hex, hes⟩, hlx, hcanx, hrecx, hmonox, hdigx, hls, hcans, hrecs, hmonos, hdigs,
    ?_, ?_, hdlen, ?_, hhdr, hpdig, ?_, ?_, ?_⟩
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
