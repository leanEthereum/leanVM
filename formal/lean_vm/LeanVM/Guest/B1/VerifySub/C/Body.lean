/-
  LeanVM.Guest.B1.VerifySub.C.Body

  `verify_sub`'s statements hold on its honest valuation, from the sections' data: the body
  reduced to the memory's words and the values' facts each section needs.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Tail

/-!
# The body, honestly

`VsSecData rd w args`: what the thirteen sections take — the memory's words (the stream, the own
buffers' and the caller's), the values' facts (constants, canonical cells, the callees' returns
as the oracle gives them), with `C` the trivial call relation (`completeAt_flatDep`'s body holds
under any call relation: the callees come from their placement). `vsCPre_complete`: every
statement of `verify_sub` but its `ret` holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

/-- An atom. -/
def atomB : Stmt → Bool
  | .atom _ => true
  | _ => false

theorem vsHeadT_atoms : vsHeadT.all atomB = true := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- The head, as a block holding under any call relation. -/
theorem vsHeadT_completeH (hl : args.length = 6) (hc : ∀ i < 4, IsCanonical128 (args.getD i 0))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList C rd (vsσ rd w args) vsHeadT next kret := by
  refine holdsList_straightN vsHeadT (by decide +kernel) (fun s hs ↦ ?_) hn
  have h := vsHeadT_complete (rd := rd) (w := w) hl hc s hs
  have ha := List.all_eq_true.mp vsHeadT_atoms s hs
  cases s with
  | atom a => exact h
  | _ => simp [atomB] at ha

/-- **What the sections take.** -/
structure VsSecData (rd : Reader) (w : ℕ → E) (args : List E) : Type where
  hl : args.length = 6
  -- the head
  hc4 : ∀ i < 4, IsCanonical128 (args.getD i 0)
  -- the announced words
  ws : List E
  hws : ∀ i < 8, LoadHolds rd (vsσ rd w args (.n 25)) i (ws.getD i 0)
  hrows : ∀ i < 6, LoadHolds rd (vsσ rd w args (.n 26)) i (ws.getD (i + 1) 0)
  hcap22 : ∀ i ∈ [20, 21, 22, 23, 24], IsCanonical128 (vsσ rd w args (.n i))
  -- the sizes
  κ : ℕ
  hκ6 : 6 ≤ κ
  hlow : LowDef κ rd
  lir : ℕ
  logMem : ℕ
  hl1 : 1 ≤ lir
  hl4 : lir ≤ 4
  hlm1 : 1 ≤ logMem
  hm30 : logMem ≤ 30
  e112 : vsσ rd w args (.n 110) = eOfNat lir
  e29 : vsσ rd w args (.n 27) = eOfNat logMem
  e122 : vsσ rd w args (.n 120) = gen ^ lir
  e130 : vsσ rd w args (.n 128) = gen ^ logMem
  hs : List ℕ
  hsl : hs.length = 6
  hh : ∀ x ∈ hs, x < 33
  hdims : ReadsAt rd (vsσ rd w args (.n 127)) (gen ^ logMem :: hs.map Hints.count)
  hkb : ReadsAt rd (vsσ rd w args (.n 139)) (1 :: gen ^ logMem :: hs.map Hints.count)
  hcount : hs.map Hints.count = hs.map (gen ^ ·)
  hexp : B1.ExpTables rd (vsσ rd w args (.n 4))
  -- the root
  hin : ∀ i ∈ [87, 89, 97, 99, 107, 109, 117, 119, 75, 76, 77, 78, 79],
    IsCanonical128 (vsσ rd w args (.n i))
  x0 : E
  x1 : E
  hw8 : LoadHolds rd (vsσ rd w args (.n 25)) 8 x0
  hw9 : LoadHolds rd (vsσ rd w args (.n 25)) 9 x1
  -- the bus challenges and their weights
  hz : ∀ i ∈ [8, 9, 10, 11], vsσ rd w args (.n i) = 0
  hcap532 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (319 + i)))
  hA : ∀ k (hk : k < 4), LoadHolds rd (vsσ rd w args (.n 346)) k
    (vsσ rd w args (.n ([366, 386, 406, 426][k]'(by simp; omega))))
  a0 : E
  a1 : E
  a2 : E
  a3 : E
  ha : ReadsAt rd (vsσ rd w args (.n 346)) [a0, a1, a2, a3]
  hfp : ReadsAt rd (vsσ rd w args (.n 427)) (eqKernel [a0, a1, a2, a3])
  hcap628 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (415 + i)))
  -- the three calls
  τg : E
  hd6 : LoadHolds rd (vsσ rd w args (.n 127)) 6 τg
  -- the ring map
  hcap871 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (659 + i)))
  hM : ∀ k (hk : k < 6), LoadHolds rd (vsσ rd w args (.n 664)) k
    (vsσ rd w args (.n ([658, 685, 705, 725, 745, 765][k]'(by simp; omega))))
  chs : List E
  hcl : chs.length = 6
  hchs : ReadsAt rd (vsσ rd w args (.n 664)) chs
  hct : ReadsAt rd (vsσ rd w args (.n 665)) (ringCoefficients chs)
  -- the batching
  hcap966 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (754 + i)))
  vals : ℕ → E
  hpool : ∀ i < 142, LoadHolds rd (vsσ rd w args (.n (vsClaimAt (vsKept i)).1))
    (vsClaimAt (vsKept i)).2 (vals i)
  -- the tail
  m : ℕ
  r : ℕ
  hmu20 : B1.Whir.minOpenLog ≤ m
  hmu30 : m ≤ 30
  hr1 : 1 ≤ r
  hr4 : r ≤ 4
  e1684 : vsσ rd w args (.n 1684) = gen ^ m
  e124 : vsσ rd w args (.n 122) = gen ^ (r - 1)
  zs : ℕ → E
  al : ℕ → E
  hzeta : ∀ k < 19, LoadHolds rd (vsσ rd w args (.n 310)) k (zs k)
  halpha : ∀ k < 4, LoadHolds rd (vsσ rd w args (.n 346)) k (al k)
  hout : ∀ k < 19, LoadHolds rd (vsσ rd w args (.n 5)) k (zs k)
  hout' : ∀ k < 4, LoadHolds rd (vsσ rd w args (.n 5)) (19 + k) (al k)
  hout23 : LoadHolds rd (vsσ rd w args (.n 5)) 23 (vsσ rd w args (.n 643))

/-- **`verify_sub`'s statements hold on its honest valuation**, from the sections' data, under the
trivial call relation. -/
theorem vsCPre_complete (D : VsSecData rd w args) {next : Prop} {kret : List E → Prop}
    (hn : next) : Stmt.HoldsList (fun _ _ _ ↦ True) rd (vsσ rd w args) vsCPre next kret := by
  have hl := D.hl
  rw [vsCPre_tail]
  simp only [holdsList_append]
  refine vsHeadT_completeH hl D.hc4 ?_
  refine (vsReadsT_complete hl D.hws D.hrows D.hcap22 ?_).2
  have hS := (vsSizesT_complete (C := fun _ _ _ ↦ True) (kret := kret) hl D.hκ6 D.hlow D.hl1 D.hl4
    D.hlm1 D.hm30 D.e112 D.e29 D.e122 D.e130 D.hsl D.hdims D.hkb trivial trivial trivial).1
  have hkbv : ∀ s < 8, vsσ rd w args (.n (140 + s)) = gen ^ (([0, D.logMem] ++ D.hs).getD s 0) :=
    fun s hs8 ↦ by rw [hS s hs8, D.hcount, kbase_getD D.hsl hs8]
  refine (vsSizesT_complete hl D.hκ6 D.hlow D.hl1 D.hl4 D.hlm1 D.hm30 D.e112 D.e29 D.e122 D.e130
    D.hsl D.hdims D.hkb trivial trivial ?_).2
  refine (vsPushT_complete hl D.hh (by have := D.hm30; omega) hkbv D.hexp (fun _ _ ↦ trivial) ?_).2
  have R := vsRootsT_complete (rd := rd) (w := w) (C := fun _ _ _ ↦ True) (next := True)
    (kret := kret) hl D.hin D.hw8 D.hw9 trivial trivial trivial
  refine (vsRootsT_complete hl D.hin D.hw8 D.hw9 trivial trivial ?_).2.2.2
  refine vsAlphasT_complete hl D.hz R.2.2.1 D.hcap532 D.hA ?_
  refine vsFpwT_complete hl D.ha D.hfp D.hz D.hcap628 ?_
  refine (vsCallsT_complete hl D.hd6 trivial trivial trivial ?_).2.2.2.2
  refine vsMapsT_complete hl D.hz D.hcap871 D.hM ?_
  refine vsCtabT_complete hl D.hcl D.hchs D.hct trivial ?_
  refine (vsLamT_complete hl D.hz D.hcap966 D.hpool ?_).2.2
  exact (vsTailPre_complete hl D.hκ6 D.hlow D.hmu20 D.hmu30 D.e1684 D.hzeta
    D.halpha D.hout D.hout' D.hout23 trivial trivial trivial trivial hn).2

end
end LeanVM.Guest.B1.VerifySub
