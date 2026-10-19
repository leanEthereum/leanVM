/-
  LeanVM.Guest.B1.Tables.VtPlDec

  `verify_tables`' hints' sizes and pointers, and the padding weights' loads, by evaluation.
-/

module

public import LeanVM.Guest.B1.Tables.VtPlCalls

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The hints' sizes before the sum-check's: constants or a value. -/
def vtSzSrcA : List (ℕ ⊕ V) :=
  [.inl 102, .inl 102, .inl 102, .inl 34, .inl 102, .inr (.n 1866),
    .inl 42, .inl 42, .inr (.n 1904), .inl 42, .inl 42, .inl 42,
    .inr (.n 2008), .inl 42, .inl 42, .inl 42, .inr (.n 2088), .inl 42,
    .inl 42, .inr (.n 2117), .inl 42, .inl 42, .inr (.n 2146), .inl 42,
    .inl 42, .inr (.n 2175), .inl 42, .inl 42, .inr (.n 2204), .inl 42,
    .inl 42, .inr (.n 2233), .inl 42, .inl 42, .inr (.n 2262), .inl 42,
    .inl 42, .inr (.n 2291), .inl 42, .inl 42, .inr (.n 2320), .inl 42,
    .inl 42, .inr (.n 2349), .inl 42, .inl 42, .inr (.n 2378), .inl 42,
    .inl 42, .inr (.n 2407), .inl 42, .inl 42, .inr (.n 2436), .inl 42,
    .inl 42, .inr (.n 2465), .inl 42, .inl 42, .inr (.n 2494), .inl 42,
    .inl 42, .inr (.n 2523), .inl 42, .inl 42, .inr (.n 2552), .inl 42,
    .inl 42, .inr (.n 2581), .inl 42, .inl 42, .inr (.n 2610), .inl 42,
    .inl 42, .inr (.n 2639), .inl 42, .inl 42, .inr (.n 2668), .inl 42,
    .inl 42, .inr (.n 2697), .inl 42, .inl 42, .inr (.n 2726), .inl 42,
    .inl 42, .inr (.n 2755), .inl 42, .inl 42, .inr (.n 2784), .inl 42,
    .inl 42, .inr (.n 2813), .inl 42, .inl 42, .inr (.n 2842), .inl 42,
    .inl 42, .inr (.n 2871), .inl 42, .inl 42, .inr (.n 2900), .inl 42,
    .inl 42, .inr (.n 2929), .inl 42, .inl 42, .inr (.n 2958), .inl 42,
    .inl 42, .inr (.n 2987), .inl 42, .inl 42, .inr (.n 3016), .inl 42,
    .inl 42, .inr (.n 3045), .inl 42, .inl 42, .inr (.n 3717), .inl 42,
    .inl 42, .inr (.n 3745), .inl 42, .inl 42, .inr (.n 3774), .inl 42,
    .inl 42, .inr (.n 3803), .inl 42, .inl 42, .inr (.n 3832), .inl 42,
    .inl 42, .inr (.n 3861), .inl 42, .inl 42, .inr (.n 3890), .inl 42,
    .inl 42, .inr (.n 3919), .inl 42, .inl 42, .inr (.n 3948), .inl 42,
    .inl 42, .inr (.n 3977), .inl 42, .inl 42, .inr (.n 4006), .inl 42,
    .inl 42, .inr (.n 4035), .inl 42, .inl 42, .inr (.n 4064), .inl 42,
    .inl 42, .inr (.n 4093), .inl 42, .inl 42, .inr (.n 4122), .inl 42,
    .inl 42, .inr (.n 4151), .inl 42, .inl 42, .inr (.n 4180), .inl 42,
    .inl 42, .inr (.n 4209), .inl 42, .inl 42, .inr (.n 4238), .inl 42,
    .inl 42, .inr (.n 4267), .inl 42, .inl 42, .inr (.n 4296), .inl 42,
    .inl 42, .inr (.n 4325), .inl 42, .inl 42, .inr (.n 4354), .inl 42,
    .inl 42, .inr (.n 4383), .inl 42, .inl 42, .inr (.n 4412), .inl 42,
    .inl 42, .inr (.n 4441), .inl 42, .inl 42, .inr (.n 4470), .inl 42,
    .inl 42, .inr (.n 4499), .inl 42, .inl 42]

set_option maxRecDepth 100000 in
theorem vt_allocs : (vtPre.filterMap Main.Stmt.allocSz).map Prod.snd =
    vtSzSrcA ++ [.inr (.n 4635), .inr (.n 4638), .inr (.n 4654)] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vt_allocs_fst : (vtPre.filterMap Main.Stmt.allocSz).map Prod.fst = vtAllocVar.map V.n := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vtSzSrcA_cells : vtSzSrcA.all (fun x => match x with
    | .inl _ => true
    | .inr v => (List.range 65).any fun i => v == .n (selVal.getD i 0 + 11)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtSzSrcA_sizes : vtSzSrcA.map (fun x => x.elim id fun _ => 34) = vtSzPre := by decide +kernel

set_option maxRecDepth 100000 in
theorem vt_pad_load : ∀ t < 6, stmtsEqb [.atom (.load (.n (1733 + 14 * t)) (.n 7) (t + 1))]
    ((vtPre.drop (1439 + 11 * t)).take 1) = true := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
