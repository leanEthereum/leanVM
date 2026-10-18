/-
  LeanVM.Guest.B1.Tables.FlockBody

  `verify_flock`'s body and its two loops as generators, equal to the compiled core bodies by
  kernel evaluation, and its relation as the conjunction of its segments.
-/

module

public import LeanVM.Guest.B1.Lag64
public import LeanVM.Guest.B1.Tables.Common

/-!
# `verify_flock`'s body (TRIAGE #40)

`verify_flock` (G:1827-1963, `Data.core12`, 4210 statements) is straight-line but for two
guarded loop calls: the prelude stores the seven fixed challenges and calls `__loop81` for the
sampled ones (`flP0`); 64 words of round 1 (`rd1Blk`); the skip challenge (`squeezeT`); the
numerators over the upper nodes (`lag64T`) and the interpolation (`ipBlk`, `flP5`); the seven
fixed rounds (`frBlk`); the sampled rounds by `__loop82` (`flP7`); the final evaluations; the
numerators over the lower nodes; the lincheck's `alpha` and claim; its eight rounds (`lcBlk`);
the 64 slices (`zpBlk`); the pin term (`flP13`); the equality of the two points (`cpeBlk`); the
slices' Lagrange sum (`csBlk`); the check and the returns (`flPEnd`). `core12_body` checks the
generator against the data, `core140_body` and `core141_body` the loops'.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The irregular segments -/

/-- The prelude (G:1843-1858): the fixed challenges stored, the sampled ones by `__loop81`, the
state after them. -/
def flP0 : List Stmt :=
  [.atom (.copy (.n 7) (.n 0)),
    .atom (.copy (.n 8) (.n 1)),
    .atom (.const (.n 9) (word 16384 0 0)),
    .atom (.mul (.n 10) (.n 3) (.n 9)),
    .atom (.hint (.allocDyn (.n 11) (.n 10))),
    .atom (.const (.n 12) (word 5772811086190238293 0 0)),
    .atom (.load (.n 12) (.n 11) 6),
    .atom (.const (.n 13) (word 18376177690117868746 0 0)),
    .atom (.load (.n 13) (.n 11) 7),
    .atom (.const (.n 14) (word 1537792354547671042 0 0)),
    .atom (.load (.n 14) (.n 11) 8),
    .atom (.const (.n 15) (word 3877548338577296374 1367482035892397521 13373126565067795492)),
    .atom (.load (.n 15) (.n 11) 9),
    .atom (.const (.n 16) (word 7200243516802924451 16251485319816311889 13522021764491415548)),
    .atom (.load (.n 16) (.n 11) 10),
    .atom (.const (.n 17) (word 14498505783250251438 16564499533431716054 16770611540025040673)),
    .atom (.load (.n 17) (.n 11) 11),
    .atom (.const (.n 18) (word 3934799921294095118 853327055063395975 1309330797735322834)),
    .atom (.load (.n 18) (.n 11) 12),
    .atom (.const (.n 19) (word 16384 0 0)),
    .atom (.mul (.n 20) (.n 3) (.n 19)),
    .atom (.const (.n 21) (word 4 0 0)),
    .atom (.mul (.n 22) (.n 20) (.n 21)),
    .atom (.mul (.n 23) (.n 22) (.n 22)),
    .atom (.hint (.allocDyn (.n 24) (.n 23))),
    .atom (.const (.n 25) (word 67108864 0 0)),
    .atom (.mul (.n 26) (.n 24) (.n 25)),
    .atom (.load (.n 7) (.n 26) 0),
    .atom (.load (.n 8) (.n 26) 1),
    .atom (.const (.n 27) (word 8192 0 0)),
    .atom (.const (.n 28) (word 16384 0 0)),
    .atom (.mul (.n 29) (.n 3) (.n 28)),
    .atom (.add (.n 30) (.n 27) (.n 29)),
    .atom (.const (.n 31) (word 8192 0 0)),
    .atom (.const (.n 32) (word 16384 0 0)),
    .atom (.mul (.n 33) (.n 3) (.n 32)),
    .callIf (.n 30) "__loop81" [.n 31, .n 33, .n 24, .n 11],
    .atom (.const (.n 34) (word 16384 0 0)),
    .atom (.mul (.n 35) (.n 3) (.n 34)),
    .atom (.mul (.n 36) (.n 35) (.n 35)),
    .atom (.mul (.n 37) (.n 24) (.n 36)),
    .atom (.load (.n 38) (.n 37) 0),
    .atom (.load (.n 39) (.n 37) 1),
    .atom (.hint (.alloc (.n 40) 64))]

/-- The interpolation scaled by `LAGRANGE_INV_COMBINED`, and `m - 6` (G:1876-1877). -/
def flP5 : List Stmt :=
  [.atom (.const (.n 1845) (word 233317187178767959 0 0)),
    .atom (.mul (.n 1846) (.n 1841) (.n 1845)),
    .atom (.mul (.n 1847) (.n 1844) (.n 1846)),
    .atom (.const (.n 1848) (word 16384 0 0)),
    .atom (.mul (.n 1849) (.n 3) (.n 1848)),
    .atom (.const (.n 1850) (word 2017612633061982209 0 0)),
    .atom (.mul (.n 1851) (.n 1849) (.n 1850))]

/-- The sampled rounds by `__loop82`, and their last row (G:1888-1910). -/
def flP7 : List Stmt :=
  [.atom (.const (.n 2216) (word 4 0 0)),
    .atom (.mul (.n 2217) (.n 1851) (.n 2216)),
    .atom (.mul (.n 2218) (.n 2217) (.n 2217)),
    .atom (.mul (.n 2219) (.n 2218) (.n 2218)),
    .atom (.hint (.allocDyn (.n 2220) (.n 2219))),
    .atom (.const (.n 2221) (word 268435456 0 0)),
    .atom (.mul (.n 2222) (.n 2220) (.n 2221)),
    .atom (.load (.n 2203) (.n 2222) 0),
    .atom (.load (.n 2204) (.n 2222) 1),
    .atom (.const (.n 2223) (word 442368 0 0)),
    .atom (.mul (.n 2224) (.n 2) (.n 2223)),
    .atom (.load (.n 2224) (.n 2222) 2),
    .atom (.load (.n 2215) (.n 2222) 3),
    .atom (.const (.n 2225) (word 128 0 0)),
    .atom (.const (.n 2226) (word 256 0 0)),
    .atom (.mul (.n 2227) (.n 3) (.n 2226)),
    .atom (.add (.n 2228) (.n 2225) (.n 2227)),
    .atom (.const (.n 2229) (word 128 0 0)),
    .atom (.const (.n 2230) (word 256 0 0)),
    .atom (.mul (.n 2231) (.n 3) (.n 2230)),
    .callIf (.n 2228) "__loop82" [.n 2229, .n 2231, .n 2220, .n 11, .n 4],
    .atom (.const (.n 2232) (word 256 0 0)),
    .atom (.mul (.n 2233) (.n 3) (.n 2232)),
    .atom (.mul (.n 2234) (.n 2233) (.n 2233)),
    .atom (.mul (.n 2235) (.n 2234) (.n 2234)),
    .atom (.mul (.n 2236) (.n 2220) (.n 2235)),
    .atom (.load (.n 2237) (.n 2236) 0),
    .atom (.load (.n 2238) (.n 2236) 1),
    .atom (.load (.n 2239) (.n 2236) 3),
    .atom (.load (.n 2240) (.n 2236) 2)]

/-- The pin column's weight (`eq_weight`, inline), and the pin term (G:1945-1946). -/
def flP13 : List Stmt :=
  [.atom (.load (.n 4093) (.n 5) 0),
    .atom (.const (.n 4094) (word 1 0 0)),
    .atom (.add (.n 4095) (.n 4094) (.n 4093)),
    .atom (.load (.n 4096) (.n 5) 1),
    .atom (.const (.n 4097) (word 1 0 0)),
    .atom (.add (.n 4098) (.n 4097) (.n 4096)),
    .atom (.mul (.n 4099) (.n 4095) (.n 4098)),
    .atom (.load (.n 4100) (.n 5) 2),
    .atom (.const (.n 4101) (word 1 0 0)),
    .atom (.add (.n 4102) (.n 4101) (.n 4100)),
    .atom (.mul (.n 4103) (.n 4099) (.n 4102)),
    .atom (.load (.n 4104) (.n 5) 3),
    .atom (.const (.n 4105) (word 1 0 0)),
    .atom (.add (.n 4106) (.n 4105) (.n 4104)),
    .atom (.mul (.n 4107) (.n 4103) (.n 4106)),
    .atom (.load (.n 4108) (.n 5) 4),
    .atom (.mul (.n 4109) (.n 4107) (.n 4108)),
    .atom (.load (.n 4110) (.n 5) 5),
    .atom (.const (.n 4111) (word 1 0 0)),
    .atom (.add (.n 4112) (.n 4111) (.n 4110)),
    .atom (.mul (.n 4113) (.n 4109) (.n 4112)),
    .atom (.load (.n 4114) (.n 5) 6),
    .atom (.const (.n 4115) (word 1 0 0)),
    .atom (.add (.n 4116) (.n 4115) (.n 4114)),
    .atom (.mul (.n 4117) (.n 4113) (.n 4116)),
    .atom (.load (.n 4118) (.n 5) 7),
    .atom (.const (.n 4119) (word 1 0 0)),
    .atom (.add (.n 4120) (.n 4119) (.n 4118)),
    .atom (.mul (.n 4121) (.n 4117) (.n 4120)),
    .atom (.mul (.n 4122) (.n 2735) (.n 4121)),
    .atom (.load (.n 4123) (.n 6) 0),
    .atom (.mul (.n 4124) (.n 4122) (.n 4123))]

/-- The slices' Lagrange sum scaled, the final check and the returns (G:1955-1963). -/
def flPEnd : List Stmt :=
  [.atom (.const (.n 4363) (word 11666641484232641359 0 0)),
    .atom (.mul (.n 4364) (.n 4362) (.n 4363)),
    .atom (.add (.n 4365) (.n 2719) (.n 4124)),
    .atom (.mul (.n 4366) (.n 2734) (.n 4171)),
    .atom (.mul (.n 4367) (.n 4366) (.n 4364)),
    .atom (.add (.n 4368) (.n 4365) (.n 4367)),
    .atom (.assertEq (.n 3132) (.n 4368)),
    .atom (.copy (.n 4369) (.n 4091)),
    .atom (.copy (.n 4370) (.n 4092)),
    .atom (.const (.n 4371) (word 7077888 0 0)),
    .atom (.mul (.n 4372) (.n 2240) (.n 4371)),
    .atom (.copy (.n 4373) (.n 4372)),
    .atom (.copy (.n 4374) (.n 1014)),
    .atom (.copy (.n 4375) (.n 2733)),
    .atom (.copy (.n 4376) (.n 2719))]

/-! ## The repeated blocks -/

/-- Round 1's word `i`'s state cells. -/
def rd1S (i : ℕ) : ℕ := if i = 0 then 38 else 39 + 15 * i

/-- Round 1's word `i` (G:1864-1866): read at offset `i`, absorbed, stored. -/
def rd1Blk (i : ℕ) : List Stmt :=
  fsNextT (.n (rd1S i)) (.n (rd1S i + 1)) (.n 2) i (41 + 15 * i) ++
    [.atom (.load (.n (41 + 15 * i)) (.n 40) i)]

/-- Term `i` of the interpolation (G:1873-1875): the lower half's product and the sum. -/
def ipBlk (i : ℕ) : List Stmt :=
  if i = 0 then [.atom (.load (.n 1465) (.n 40) 0), .atom (.mul (.n 1466) (.n 1401) (.n 1465))]
  else
    [.atom (.const (.n (1461 + 6 * i)) (word (phi8Words.getD i 0) 0 0)),
      .atom (.add (.n (1462 + 6 * i)) (.n 1014) (.n (1461 + 6 * i))),
      .atom (.mul (.n (1463 + 6 * i)) (.n (if i = 1 then 1014 else 1457 + 6 * i))
        (.n (1462 + 6 * i))),
      .atom (.load (.n (1464 + 6 * i)) (.n 40) i),
      .atom (.mul (.n (1465 + 6 * i)) (.n (1401 + i)) (.n (1464 + 6 * i))),
      .atom (.add (.n (1466 + 6 * i)) (.n (if i = 1 then 1466 else 1460 + 6 * i))
        (.n (1465 + 6 * i)))]

/-- Fixed round `i`'s base value. -/
def frB (i : ℕ) : ℕ := 1852 + 52 * i

/-- Fixed round `i`'s state cells. -/
def frS (i : ℕ) : ℕ := if i = 0 then 1006 else frB i - 13

/-- Fixed round `i`'s running claim. -/
def frC (i : ℕ) : ℕ := if i = 0 then 1847 else frB i - 1

/-- Fixed round `i` (G:1879-1886): the equality challenge, the two coefficients, the constant one
the split fixes, the challenge stored, the next claim. -/
def frBlk (i : ℕ) : List Stmt :=
  let B := frB i
  .atom (.load (.n B) (.n 11) (6 + i)) ::
    fsNextT (.n (frS i)) (.n (frS i + 1)) (.n 2) (64 + 2 * i) (B + 1) ++
    fsNextT (.n (B + 14)) (.n (B + 15)) (.n 2) (65 + 2 * i) (B + 16) ++
    [.atom (.add (.n (B + 31)) (.n (B + 1)) (.n (B + 16))),
      .atom (.mul (.n (B + 32)) (.n B) (.n (B + 31))),
      .atom (.add (.n (B + 33)) (.n (frC i)) (.n (B + 32)))] ++
    squeezeT (.n (B + 29)) (.n (B + 30)) (B + 34) ++
    [.atom (.load (.n (B + 47)) (.n 4) i),
      .atom (.mul (.n (B + 48)) (.n (B + 47)) (.n (B + 16))),
      .atom (.add (.n (B + 49)) (.n (B + 1)) (.n (B + 48))),
      .atom (.mul (.n (B + 50)) (.n (B + 47)) (.n (B + 49))),
      .atom (.add (.n (B + 51)) (.n (B + 33)) (.n (B + 50)))]

/-- The final evaluations `a`, `b` and `c = claim + a·b` (G:1914-1916). -/
def flS8 : List Stmt :=
  fsNextT (.n 2237) (.n 2238) (.n 2240) 0 2241 ++ fsNextT (.n 2254) (.n 2255) (.n 2240) 1 2256 ++
    [.atom (.mul (.n 2271) (.n 2241) (.n 2256)), .atom (.add (.n 2272) (.n 2239) (.n 2271))]

/-- The deferred matrix value, `alpha` and the lincheck's claim (G:1926-1930). -/
def flS10 : List Stmt :=
  .atom (.hint (.witness "matpart" (.stack [.n 2719]))) :: squeezeT (.n 2269) (.n 2270) 2720 ++
    [.atom (.mul (.n 2734) (.n 2733) (.n 2733)), .atom (.mul (.n 2735) (.n 2734) (.n 2733)),
      .atom (.mul (.n 2736) (.n 2733) (.n 2256)), .atom (.add (.n 2737) (.n 2241) (.n 2736)),
      .atom (.mul (.n 2738) (.n 2734) (.n 2272)), .atom (.add (.n 2739) (.n 2737) (.n 2738)),
      .atom (.add (.n 2740) (.n 2739) (.n 2735))]

/-- Lincheck round `i`'s base value. -/
def lcB (i : ℕ) : ℕ := 2741 + 49 * i

/-- Lincheck round `i`'s state cells. -/
def lcS (i : ℕ) : ℕ := if i = 0 then 2725 else lcB i - 13

/-- Lincheck round `i`'s running claim. -/
def lcC (i : ℕ) : ℕ := if i = 0 then 2740 else lcB i - 1

/-- Lincheck round `i` (G:1931-1937): the two coefficients, the linear one the split fixes, the
challenge stored, the next claim. -/
def lcBlk (i : ℕ) : List Stmt :=
  let B := lcB i
  fsNextT (.n (lcS i)) (.n (lcS i + 1)) (.n 2240) (2 + 2 * i) B ++
    fsNextT (.n (B + 13)) (.n (B + 14)) (.n 2240) (3 + 2 * i) (B + 15) ++
    [.atom (.add (.n (B + 30)) (.n (lcC i)) (.n (B + 15)))] ++
    squeezeT (.n (B + 28)) (.n (B + 29)) (B + 31) ++
    [.atom (.load (.n (B + 44)) (.n 5) i),
      .atom (.mul (.n (B + 45)) (.n (B + 44)) (.n (B + 15))),
      .atom (.add (.n (B + 46)) (.n (B + 30)) (.n (B + 45))),
      .atom (.mul (.n (B + 47)) (.n (B + 44)) (.n (B + 46))),
      .atom (.add (.n (B + 48)) (.n B) (.n (B + 47)))]

/-- Slice `i`'s state cells. -/
def zpS (i : ℕ) : ℕ := if i = 0 then 3120 else 3131 + 15 * i

/-- Slice `i` (G:1939-1941): read, absorbed, stored. -/
def zpBlk (i : ℕ) : List Stmt :=
  fsNextT (.n (zpS i)) (.n (zpS i + 1)) (.n 2240) (18 + i) (3133 + 15 * i) ++
    [.atom (.load (.n (3133 + 15 * i)) (.n 6) i)]

/-- Factor `t` of the points' equality (G:1951-1952). -/
def cpeBlk (t : ℕ) : List Stmt :=
  if t = 0 then
    [.atom (.const (.n 4125) (word 1 0 0)), .atom (.load (.n 4126) (.n 4) 0),
      .atom (.add (.n 4127) (.n 4125) (.n 4126)), .atom (.load (.n 4128) (.n 5) 7),
      .atom (.add (.n 4129) (.n 4127) (.n 4128))]
  else
    [.atom (.const (.n (4124 + 6 * t)) (word 1 0 0)), .atom (.load (.n (4125 + 6 * t)) (.n 4) t),
      .atom (.add (.n (4126 + 6 * t)) (.n (4124 + 6 * t)) (.n (4125 + 6 * t))),
      .atom (.load (.n (4127 + 6 * t)) (.n 5) (7 - t)),
      .atom (.add (.n (4128 + 6 * t)) (.n (4126 + 6 * t)) (.n (4127 + 6 * t))),
      .atom (.mul (.n (4129 + 6 * t)) (.n (if t = 1 then 4129 else 4123 + 6 * t))
        (.n (4128 + 6 * t)))]

/-- Term `i` of the slices' Lagrange sum (G:1953-1954). -/
def csBlk (i : ℕ) : List Stmt :=
  if i = 0 then [.atom (.load (.n 4172) (.n 6) 0), .atom (.mul (.n 4173) (.n 2655) (.n 4172))]
  else
    [.atom (.load (.n (4171 + 3 * i)) (.n 6) i),
      .atom (.mul (.n (4172 + 3 * i)) (.n (2655 + i)) (.n (4171 + 3 * i))),
      .atom (.add (.n (4173 + 3 * i)) (.n (if i = 1 then 4173 else 4170 + 3 * i))
        (.n (4172 + 3 * i)))]

/-! ## The body -/

/-- The segments of `verify_flock`'s body before its `ret`. -/
def flSegs : List (List Stmt) :=
  [flP0, ((List.range 64).map rd1Blk).flatten, squeezeT (.n 999) (.n 1000) 1001,
    lag64T (.n 1014) (phi8From 64) 1015, ((List.range 64).map ipBlk).flatten, flP5,
    ((List.range 7).map frBlk).flatten, flP7, flS8, lag64T (.n 1014) (phi8From 0) 2273, flS10,
    ((List.range 8).map lcBlk).flatten, ((List.range 64).map zpBlk).flatten, flP13,
    ((List.range 8).map cpeBlk).flatten, ((List.range 64).map csBlk).flatten, flPEnd]

/-- `verify_flock`'s return. -/
def flRet : Stmt := .ret [.n 4369, .n 4370, .n 4373, .n 4374, .n 4375, .n 4376]

set_option maxRecDepth 100000 in
theorem core12_body : Fn.body Data.core12 = flSegs.flatten ++ [flRet] :=
  stmtsEqb_sound (by decide +kernel)

theorem flSegs_noRet : ∀ s ∈ flSegs, Stmt.noRetList s = true := by decide +kernel

theorem find_verify_flock : coreProgram.find? "verify_flock" = some Data.core12 :=
  Program.find?_of_indexOf? (j := 12) (by decide +kernel) rfl

theorem core12_params : Fn.params Data.core12 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] := rfl

section
variable {C : CallRel} {rd : Reader} {σ : Val}

theorem holdsList_flatten_noRet : ∀ (ss : List (List Stmt)), (∀ s ∈ ss, Stmt.noRetList s = true) →
    ∀ (next : Prop) (kret : List E → Prop),
    Stmt.HoldsList C rd σ ss.flatten next kret ↔
      (∀ s ∈ ss, Stmt.HoldsList C rd σ s True kret) ∧ next
  | [], _, _, _ => by simp [Stmt.HoldsList]
  | s :: ss, h, next, kret => by
    rw [List.flatten_cons, holdsList_append, holdsList_noRet s (h s (by simp)),
      holdsList_flatten_noRet ss (fun t ht => h t (by simp [ht]))]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

end

/-- **`verify_flock`'s relation**: a valuation taking the parameters to the arguments, every
segment holding, and the returns. -/
theorem verify_flock_holds {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd "verify_flock" args rets) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] = args ∧
      (∀ s ∈ flSegs, Stmt.HoldsList (coreProgram.Rel rd) rd σ s True fun rs => rs = rets) ∧
      [σ (.n 4369), σ (.n 4370), σ (.n 4373), σ (.n 4374), σ (.n 4375), σ (.n 4376)] = rets := by
  rw [rel_iff_sem find_verify_flock, core12_body, core12_params] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [holdsList_append, holdsList_flatten_noRet _ flSegs_noRet] at hb
  exact ⟨σ, hp, hb.1, by simpa [flRet, Stmt.HoldsList, Stmt.Holds] using hb.2⟩

/-! ## The loops -/

/-- `__loop81`'s body (G:1855-1861): row `x` of `flock_pts` squeezed, the challenge stored at
`zerocheck_r[x]`, the state on to row `x·g`. -/
def l81Body : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 2) (.n 4)),
    .atom (.load (.n 6) (.n 5) 0), .atom (.load (.n 7) (.n 5) 1)] ++
    squeezeT (.n 6) (.n 7) 8 ++
    [.atom (.mul (.n 22) (.n 3) (.n 0)), .atom (.load (.n 21) (.n 22) 0),
      .atom (.load (.n 13) (.n 5) 2), .atom (.load (.n 14) (.n 5) 3),
      .atom (.const (.n 23) (word 2 0 0)), .atom (.mul (.n 24) (.n 0) (.n 23)),
      .atom (.add (.n 25) (.n 24) (.n 1)), .atom (.const (.n 26) (word 2 0 0)),
      .atom (.mul (.n 27) (.n 0) (.n 26)),
      .callIf (.n 25) "__loop81" [.n 27, .n 1, .n 2, .n 3], .ret []]

theorem core140_body : Fn.body Data.core140 = l81Body := stmtsEqb_sound (by decide +kernel)

/-- `__loop82`'s body (G:1893-1907): row `x` of `flock_rounds` holds the state, the cursor and
the claim; round `x` reads its two coefficients, stores its challenge at `zerocheck_chis[x]` and
writes row `x·g`. -/
def l82Body : List Stmt :=
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 5) (.n 5)),
    .atom (.mul (.n 7) (.n 2) (.n 6)), .atom (.load (.n 8) (.n 7) 0),
    .atom (.load (.n 9) (.n 7) 1), .atom (.mul (.n 10) (.n 3) (.n 0)),
    .atom (.load (.n 11) (.n 10) 6), .atom (.load (.n 12) (.n 7) 2)] ++
    fsNextT (.n 8) (.n 9) (.n 12) 0 13 ++ fsNextT (.n 26) (.n 27) (.n 12) 1 28 ++
    [.atom (.load (.n 43) (.n 7) 3), .atom (.add (.n 44) (.n 13) (.n 28)),
      .atom (.mul (.n 45) (.n 11) (.n 44)), .atom (.add (.n 46) (.n 43) (.n 45))] ++
    squeezeT (.n 41) (.n 42) 47 ++
    [.atom (.mul (.n 61) (.n 4) (.n 0)), .atom (.load (.n 60) (.n 61) 0),
      .atom (.load (.n 52) (.n 7) 4), .atom (.load (.n 53) (.n 7) 5),
      .atom (.const (.n 62) (word 4 0 0)), .atom (.mul (.n 63) (.n 12) (.n 62)),
      .atom (.load (.n 63) (.n 7) 6), .atom (.mul (.n 64) (.n 60) (.n 28)),
      .atom (.add (.n 65) (.n 13) (.n 64)), .atom (.mul (.n 66) (.n 60) (.n 65)),
      .atom (.add (.n 67) (.n 46) (.n 66)), .atom (.load (.n 67) (.n 7) 7),
      .atom (.const (.n 68) (word 2 0 0)), .atom (.mul (.n 69) (.n 0) (.n 68)),
      .atom (.add (.n 70) (.n 69) (.n 1)), .atom (.const (.n 71) (word 2 0 0)),
      .atom (.mul (.n 72) (.n 0) (.n 71)),
      .callIf (.n 70) "__loop82" [.n 72, .n 1, .n 2, .n 3, .n 4], .ret []]

theorem core141_body : Fn.body Data.core141 = l82Body := stmtsEqb_sound (by decide +kernel)

theorem find_loop81 : coreProgram.find? "__loop81" = some Data.core140 :=
  Program.find?_of_indexOf? (j := 140) (by decide +kernel) rfl

theorem find_loop82 : coreProgram.find? "__loop82" = some Data.core141 :=
  Program.find?_of_indexOf? (j := 141) (by decide +kernel) rfl

end
end LeanVM.Guest.B1
