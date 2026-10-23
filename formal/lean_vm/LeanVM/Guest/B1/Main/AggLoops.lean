/-
  LeanVM.Guest.B1.Main.AggLoops

  The five loops of `aggregate_claims` (`__loop95` to `__loop99`, G:3341-3480) as templates.
-/

module

public import LeanVM.Guest.B1.Main.AggTemplate

/-!
# The batching loops

Each loop runs one child at `x = g^c`:

* `__loop95` (`l95Body`): the transcript row: the child's public input, its 106 fresh cells and
  its 53 carried cells absorbed (`obsChainT`, a chain of `fs_next`), the pointers stored in
  `fresh_row`, `carried_row`;
* `__loop96` (`l96Body`), `__loop98` (`l98Body`): two and three squeezes, the lambdas stored, the
  running claim accumulated;
* `__loop97` (`l97Body`): the bytecode weight, two products of 22 factors (`l97Coord`);
* `__loop99` (`l99Body`): the matrix weights: the 64 Lagrange numerators at the skip challenge
  over the nodes `phiWords` (prefix and suffix products), the row and column sums against the
  `eqtree`s, the eq factors, and the carried claim's product of 28 factors.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## The absorb chain -/

/-- The state's first cell before block `k` of an absorb chain from `B`. -/
def chainS0 (s0 : V) (B : ℕ) : ℕ → V
  | 0 => s0
  | k + 1 => .n (B + 15 * k + 13)

/-- The state's second cell before block `k`. -/
def chainS1 (s1 : V) (B : ℕ) : ℕ → V
  | 0 => s1
  | k + 1 => .n (B + 15 * k + 14)

/-- `n` words at `cur`, read and absorbed in turn from the state `s0, s1`, block `k` from
`B + 15k`. -/
def obsChainT (s0 s1 cur : V) (B n : ℕ) : List Stmt :=
  ((List.range n).map fun k => fsNextT (chainS0 s0 B k) (chainS1 s1 B k) cur k (B + 15 * k)).flatten

/-! ## `__loop95` -/

/-- `__loop95`'s body. -/
def l95Body : List Stmt :=
  [.atom (.mul (.n 8) (.n 0) (.n 0)), .atom (.mul (.n 9) (.n 2) (.n 8)),
    .atom (.load (.n 10) (.n 9) 0), .atom (.load (.n 11) (.n 9) 1),
    .atom (.mul (.n 12) (.n 0) (.n 0)), .atom (.mul (.n 13) (.n 3) (.n 12))] ++
  fsNextT (.n 10) (.n 11) (.n 13) 0 14 ++ [.atom (.mul (.n 29) (.n 3) (.n 12))] ++
  fsNextT (.n 27) (.n 28) (.n 29) 1 30 ++
  [.atom (.mul (.n 45) (.n 0) (.n 0)), .atom (.mul (.n 46) (.n 45) (.n 0)),
    .atom (.mul (.n 47) (.n 46) (.n 46)), .atom (.mul (.n 48) (.n 47) (.n 47)),
    .atom (.mul (.n 49) (.n 48) (.n 0)), .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 50) (.n 50)), .atom (.mul (.n 52) (.n 51) (.n 0)),
    .atom (.mul (.n 53) (.n 52) (.n 52)), .atom (.mul (.n 54) (.n 4) (.n 53)),
    .atom (.mul (.n 55) (.n 5) (.n 0)), .atom (.load (.n 54) (.n 55) 0)] ++
  obsChainT (.n 43) (.n 44) (.n 54) 56 106 ++
  [.atom (.mul (.n 1646) (.n 0) (.n 0)), .atom (.mul (.n 1647) (.n 1646) (.n 0)),
    .atom (.mul (.n 1648) (.n 1647) (.n 1647)), .atom (.mul (.n 1649) (.n 1648) (.n 1648)),
    .atom (.mul (.n 1650) (.n 1649) (.n 0)), .atom (.mul (.n 1651) (.n 1650) (.n 1650)),
    .atom (.mul (.n 1652) (.n 1651) (.n 1651)), .atom (.mul (.n 1653) (.n 1652) (.n 0)),
    .atom (.mul (.n 1654) (.n 6) (.n 1653)), .atom (.mul (.n 1655) (.n 7) (.n 0)),
    .atom (.load (.n 1654) (.n 1655) 0)] ++
  obsChainT (.n 1644) (.n 1645) (.n 1654) 1656 53 ++
  [.atom (.load (.n 2449) (.n 9) 2), .atom (.load (.n 2450) (.n 9) 3),
    .atom (.const (.n 2451) (word 2 0 0)), .atom (.mul (.n 2452) (.n 0) (.n 2451)),
    .atom (.add (.n 2453) (.n 2452) (.n 1)), .atom (.const (.n 2454) (word 2 0 0)),
    .atom (.mul (.n 2455) (.n 0) (.n 2454)),
    .callIf (.n 2453) "__loop95" [.n 2455, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], .ret []]

/-! ## `__loop96`, `__loop98` -/

/-- `__loop96`'s body. -/
def l96Body : List Stmt :=
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 0)),
    .atom (.mul (.n 8) (.n 2) (.n 7)), .atom (.load (.n 9) (.n 8) 0),
    .atom (.load (.n 10) (.n 8) 1)] ++ squeezeT (.n 9) (.n 10) 11 ++ squeezeT (.n 16) (.n 17) 25 ++
  [.atom (.mul (.n 39) (.n 0) (.n 0)), .atom (.mul (.n 40) (.n 3) (.n 39)),
    .atom (.load (.n 24) (.n 40) 0), .atom (.mul (.n 41) (.n 3) (.n 39)),
    .atom (.load (.n 38) (.n 41) 1), .atom (.mul (.n 42) (.n 4) (.n 0)),
    .atom (.load (.n 43) (.n 42) 0), .atom (.mul (.n 44) (.n 5) (.n 0)),
    .atom (.load (.n 45) (.n 44) 0), .atom (.load (.n 30) (.n 8) 3), .atom (.load (.n 31) (.n 8) 4),
    .atom (.load (.n 46) (.n 8) 2), .atom (.load (.n 47) (.n 43) 22),
    .atom (.mul (.n 48) (.n 24) (.n 47)), .atom (.add (.n 49) (.n 46) (.n 48)),
    .atom (.load (.n 50) (.n 45) 22), .atom (.mul (.n 51) (.n 38) (.n 50)),
    .atom (.add (.n 52) (.n 49) (.n 51)), .atom (.load (.n 52) (.n 8) 5),
    .atom (.const (.n 53) (word 2 0 0)), .atom (.mul (.n 54) (.n 0) (.n 53)),
    .atom (.add (.n 55) (.n 54) (.n 1)), .atom (.const (.n 56) (word 2 0 0)),
    .atom (.mul (.n 57) (.n 0) (.n 56)),
    .callIf (.n 55) "__loop96" [.n 57, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []]

/-- `__loop98`'s body. -/
def l98Body : List Stmt :=
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 0)),
    .atom (.mul (.n 8) (.n 2) (.n 7)), .atom (.load (.n 9) (.n 8) 0),
    .atom (.load (.n 10) (.n 8) 1)] ++ squeezeT (.n 9) (.n 10) 11 ++ squeezeT (.n 16) (.n 17) 25 ++
  squeezeT (.n 30) (.n 31) 39 ++
  [.atom (.mul (.n 53) (.n 0) (.n 0)), .atom (.mul (.n 54) (.n 53) (.n 0)),
    .atom (.mul (.n 55) (.n 3) (.n 54)), .atom (.load (.n 24) (.n 55) 0),
    .atom (.mul (.n 56) (.n 3) (.n 54)), .atom (.load (.n 38) (.n 56) 1),
    .atom (.mul (.n 57) (.n 3) (.n 54)), .atom (.load (.n 52) (.n 57) 2),
    .atom (.mul (.n 58) (.n 4) (.n 0)), .atom (.load (.n 59) (.n 58) 0),
    .atom (.mul (.n 60) (.n 5) (.n 0)), .atom (.load (.n 61) (.n 60) 0),
    .atom (.load (.n 44) (.n 8) 3), .atom (.load (.n 45) (.n 8) 4), .atom (.load (.n 62) (.n 8) 2),
    .atom (.load (.n 63) (.n 59) 105), .atom (.mul (.n 64) (.n 24) (.n 63)),
    .atom (.add (.n 65) (.n 62) (.n 64)), .atom (.load (.n 66) (.n 61) 51),
    .atom (.mul (.n 67) (.n 38) (.n 66)), .atom (.add (.n 68) (.n 65) (.n 67)),
    .atom (.load (.n 69) (.n 61) 52), .atom (.mul (.n 70) (.n 52) (.n 69)),
    .atom (.add (.n 71) (.n 68) (.n 70)), .atom (.load (.n 71) (.n 8) 5),
    .atom (.const (.n 72) (word 2 0 0)), .atom (.mul (.n 73) (.n 0) (.n 72)),
    .atom (.add (.n 74) (.n 73) (.n 1)), .atom (.const (.n 75) (word 2 0 0)),
    .atom (.mul (.n 76) (.n 0) (.n 75)),
    .callIf (.n 74) "__loop98" [.n 76, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []]

/-! ## `__loop97` -/

/-- Coordinate `k ≥ 1` of the two bytecode eq products, from `b = 20 + 11(k - 1)`. -/
def l97Coord (k : ℕ) : List Stmt :=
  let b := 20 + 11 * (k - 1)
  let pf := if k = 1 then 15 else b - 6
  let pc := if k = 1 then 19 else b - 1
  [.atom (.load (.n b) (.n 4) k), .atom (.const (.n (b + 1)) (word 1 0 0)),
    .atom (.load (.n (b + 2)) (.n 8) k), .atom (.add (.n (b + 3)) (.n (b + 1)) (.n (b + 2))),
    .atom (.add (.n (b + 4)) (.n (b + 3)) (.n b)), .atom (.mul (.n (b + 5)) (.n pf) (.n (b + 4))),
    .atom (.const (.n (b + 6)) (word 1 0 0)), .atom (.load (.n (b + 7)) (.n 10) k),
    .atom (.add (.n (b + 8)) (.n (b + 6)) (.n (b + 7))), .atom (.add (.n (b + 9)) (.n (b + 8)) (.n b)),
    .atom (.mul (.n (b + 10)) (.n pc) (.n (b + 9)))]

/-- `__loop97`'s body. -/
def l97Body : List Stmt :=
  [.atom (.mul (.n 7) (.n 2) (.n 0)), .atom (.load (.n 8) (.n 7) 0),
    .atom (.mul (.n 9) (.n 3) (.n 0)), .atom (.load (.n 10) (.n 9) 0),
    .atom (.load (.n 11) (.n 4) 0), .atom (.const (.n 12) (word 1 0 0)),
    .atom (.load (.n 13) (.n 8) 0), .atom (.add (.n 14) (.n 12) (.n 13)),
    .atom (.add (.n 15) (.n 14) (.n 11)), .atom (.const (.n 16) (word 1 0 0)),
    .atom (.load (.n 17) (.n 10) 0), .atom (.add (.n 18) (.n 16) (.n 17)),
    .atom (.add (.n 19) (.n 18) (.n 11))] ++
  ((List.range 21).map fun k => l97Coord (k + 1)).flatten ++
  [.atom (.mul (.n 251) (.n 0) (.n 0)), .atom (.mul (.n 252) (.n 5) (.n 0)),
    .atom (.load (.n 253) (.n 252) 0), .atom (.mul (.n 254) (.n 6) (.n 251)),
    .atom (.load (.n 255) (.n 254) 0), .atom (.mul (.n 256) (.n 255) (.n 245)),
    .atom (.add (.n 257) (.n 253) (.n 256)), .atom (.mul (.n 258) (.n 6) (.n 251)),
    .atom (.load (.n 259) (.n 258) 1), .atom (.mul (.n 260) (.n 259) (.n 250)),
    .atom (.add (.n 261) (.n 257) (.n 260)), .atom (.mul (.n 262) (.n 5) (.n 0)),
    .atom (.load (.n 261) (.n 262) 1), .atom (.const (.n 263) (word 2 0 0)),
    .atom (.mul (.n 264) (.n 0) (.n 263)), .atom (.add (.n 265) (.n 264) (.n 1)),
    .atom (.const (.n 266) (word 2 0 0)), .atom (.mul (.n 267) (.n 0) (.n 266)),
    .callIf (.n 265) "__loop97" [.n 267, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], .ret []]

/-! ## `__loop99` -/

/-- The 64 nodes of the skip domain as the data's words (`0,1,233317187178767958,233317187178767959,5847396588373319944,5847396588373319945,5916261553440163678,5916261553440163679,909273441170553857,909273441170553856,1126616643693337175,1126616643693337174,6753221685647269129,6753221685647269128,6810757554037128031,6810757554037128030,13425015913296524956,13425015913296524957,13363258058013790410,13363258058013790411,16963121286284040084,16963121286284040085,16741555821419917762,16741555821419917763,13173415632012282525,13173415632012282524,13109335328444067019,13109335328444067018,16714968798032636821,16714968798032636820,16486437098630516163,16486437098630516162,13413663147086793287,13413663147086793286,13337989939188722705,13337989939188722704,16933754119322725199,16933754119322725198,16734302103207496985,16734302103207496984,13166419680609547846,13166419680609547847,13079698300183580688,13079698300183580689,16689958445912364878,16689958445912364879,16474814470949679384,16474814470949679385,29795976497216731,29795976497216730,240155289994828429,240155289994828428,5859178164118920659,5859178164118920658,5941114056868903813,5941114056868903812,934417933708345562,934417933708345563,1138091936817112716,1138091936817112717,6760351777467556306,6760351777467556307,6840247247740520324,68402472477405203258_NODES`). -/
def phiWords : List ℕ := [0,1,233317187178767958,233317187178767959,5847396588373319944,5847396588373319945,5916261553440163678,5916261553440163679,909273441170553857,909273441170553856,1126616643693337175,1126616643693337174,6753221685647269129,6753221685647269128,6810757554037128031,6810757554037128030,13425015913296524956,13425015913296524957,13363258058013790410,13363258058013790411,16963121286284040084,16963121286284040085,16741555821419917762,16741555821419917763,13173415632012282525,13173415632012282524,13109335328444067019,13109335328444067018,16714968798032636821,16714968798032636820,16486437098630516163,16486437098630516162,13413663147086793287,13413663147086793286,13337989939188722705,13337989939188722704,16933754119322725199,16933754119322725198,16734302103207496985,16734302103207496984,13166419680609547846,13166419680609547847,13079698300183580688,13079698300183580689,16689958445912364878,16689958445912364879,16474814470949679384,16474814470949679385,29795976497216731,29795976497216730,240155289994828429,240155289994828428,5859178164118920659,5859178164118920658,5941114056868903813,5941114056868903812,934417933708345562,934417933708345563,1138091936817112716,1138091936817112717,6760351777467556306,6760351777467556307,6840247247740520324,6840247247740520325]

/-- The prefix product's value before node `i ≥ 1`: `pre[i]`. -/
def preV (i : ℕ) : ℕ := if i = 1 then 13 else 16 + 3 * (i - 2)

/-- Node `i ≥ 1` of the prefix products. -/
def l99Pre (i : ℕ) : List Stmt :=
  [.atom (.const (.n (14 + 3 * (i - 1))) (word (phiWords.getD i 0) 0 0)),
    .atom (.add (.n (15 + 3 * (i - 1))) (.n 11) (.n (14 + 3 * (i - 1)))),
    .atom (.mul (.n (16 + 3 * (i - 1))) (.n (preV i)) (.n (15 + 3 * (i - 1))))]

/-- Step `i < 63` of the suffix products, node `63 - i`. -/
def l99Suf (i : ℕ) : List Stmt :=
  [.atom (.const (.n (204 + 3 * i)) (word (phiWords.getD (63 - i) 0) 0 0)),
    .atom (.add (.n (205 + 3 * i)) (.n 11) (.n (204 + 3 * i))),
    .atom (.mul (.n (206 + 3 * i)) (.n (if i = 0 then 203 else 203 + 3 * i)) (.n (205 + 3 * i)))]

/-- `pre[i]`'s value. -/
def preAt (i : ℕ) : ℕ := if i = 0 then 12 else 3 * i + 10

/-- `suf[j]`'s value, `1 ≤ j ≤ 64`. -/
def sufAt (j : ℕ) : ℕ := if j = 64 then 203 else 395 - 3 * j

/-- Term `i ≥ 1` of the row sum. -/
def l99Row (i : ℕ) : List Stmt :=
  [.atom (.load (.n (460 + 3 * (i - 1))) (.n 3) (62 + i)),
    .atom (.mul (.n (461 + 3 * (i - 1))) (.n (394 + i)) (.n (460 + 3 * (i - 1)))),
    .atom (.add (.n (462 + 3 * (i - 1))) (.n (if i = 1 then 459 else 459 + 3 * (i - 1)))
      (.n (461 + 3 * (i - 1))))]

/-- Factor `k < 8` of the row eq product. -/
def l99RowEq (k : ℕ) : List Stmt :=
  [.atom (.const (.n (651 + 6 * k)) (word 1 0 0)), .atom (.load (.n (652 + 6 * k)) (.n 10) (25 + k)),
    .atom (.add (.n (653 + 6 * k)) (.n (651 + 6 * k)) (.n (652 + 6 * k))),
    .atom (.load (.n (654 + 6 * k)) (.n 4) (6 + k)),
    .atom (.add (.n (655 + 6 * k)) (.n (653 + 6 * k)) (.n (654 + 6 * k))),
    .atom (.mul (.n (656 + 6 * k)) (.n (650 + 6 * k)) (.n (655 + 6 * k)))]

/-- Term `i ≥ 1` of the column sum. -/
def l99Col (i : ℕ) : List Stmt :=
  [.atom (.load (.n (702 + 4 * (i - 1))) (.n 10) (41 + i)),
    .atom (.load (.n (703 + 4 * (i - 1))) (.n 5) (62 + i)),
    .atom (.mul (.n (704 + 4 * (i - 1))) (.n (702 + 4 * (i - 1))) (.n (703 + 4 * (i - 1)))),
    .atom (.add (.n (705 + 4 * (i - 1))) (.n (701 + 4 * (i - 1))) (.n (704 + 4 * (i - 1))))]

/-- Factor `j < 8` of the column eq product. -/
def l99ColEq (j : ℕ) : List Stmt :=
  [.atom (.const (.n (954 + 6 * j)) (word 1 0 0)), .atom (.load (.n (955 + 6 * j)) (.n 10) (33 + j)),
    .atom (.add (.n (956 + 6 * j)) (.n (954 + 6 * j)) (.n (955 + 6 * j))),
    .atom (.load (.n (957 + 6 * j)) (.n 4) (27 - j)),
    .atom (.add (.n (958 + 6 * j)) (.n (956 + 6 * j)) (.n (957 + 6 * j))),
    .atom (.mul (.n (959 + 6 * j)) (.n (953 + 6 * j)) (.n (958 + 6 * j)))]

/-- Factor `k ≥ 1` of the carried claim's eq product. -/
def l99Car (k : ℕ) : List Stmt :=
  [.atom (.const (.n (1010 + 6 * (k - 1))) (word 1 0 0)),
    .atom (.load (.n (1011 + 6 * (k - 1))) (.n 1004) (23 + k)),
    .atom (.add (.n (1012 + 6 * (k - 1))) (.n (1010 + 6 * (k - 1))) (.n (1011 + 6 * (k - 1)))),
    .atom (.load (.n (1013 + 6 * (k - 1))) (.n 4) k),
    .atom (.add (.n (1014 + 6 * (k - 1))) (.n (1012 + 6 * (k - 1))) (.n (1013 + 6 * (k - 1)))),
    .atom (.mul (.n (1015 + 6 * (k - 1))) (.n (1009 + 6 * (k - 1))) (.n (1014 + 6 * (k - 1))))]

/-- `__loop99`'s body. -/
def l99Body : List Stmt :=
  [.atom (.mul (.n 9) (.n 2) (.n 0)), .atom (.load (.n 10) (.n 9) 0),
    .atom (.load (.n 11) (.n 10) 24), .atom (.const (.n 12) (word 1 0 0)),
    .atom (.mul (.n 13) (.n 12) (.n 11))] ++
  ((List.range 63).map fun i => l99Pre (i + 1)).flatten ++
  [.atom (.const (.n 203) (word 1 0 0))] ++ ((List.range 63).map l99Suf).flatten ++
  [.atom (.mul (.n 393) (.n 392) (.n 11))] ++
  ((List.range 64).map fun i => [.atom (.mul (.n (394 + i)) (.n (preAt i)) (.n (sufAt (i + 1))))]).flatten ++
  [.atom (.load (.n 458) (.n 3) 62), .atom (.mul (.n 459) (.n 394) (.n 458))] ++
  ((List.range 63).map fun i => l99Row (i + 1)).flatten ++
  [.atom (.const (.n 649) (word 11666641484232641359 0 0)), .atom (.mul (.n 650) (.n 648) (.n 649))] ++
  ((List.range 8).map l99RowEq).flatten ++
  [.atom (.load (.n 699) (.n 10) 41), .atom (.load (.n 700) (.n 5) 62),
    .atom (.mul (.n 701) (.n 699) (.n 700))] ++
  ((List.range 63).map fun i => l99Col (i + 1)).flatten ++
  ((List.range 8).map l99ColEq).flatten ++
  [.atom (.mul (.n 1002) (.n 698) (.n 1001)), .atom (.mul (.n 1003) (.n 6) (.n 0)),
    .atom (.load (.n 1004) (.n 1003) 0), .atom (.const (.n 1005) (word 1 0 0)),
    .atom (.load (.n 1006) (.n 1004) 23), .atom (.add (.n 1007) (.n 1005) (.n 1006)),
    .atom (.load (.n 1008) (.n 4) 0), .atom (.add (.n 1009) (.n 1007) (.n 1008))] ++
  ((List.range 27).map fun k => l99Car (k + 1)).flatten ++
  [.atom (.mul (.n 1172) (.n 0) (.n 0)), .atom (.mul (.n 1173) (.n 1172) (.n 0)),
    .atom (.mul (.n 1174) (.n 7) (.n 1173)), .atom (.load (.n 1175) (.n 1174) 0),
    .atom (.mul (.n 1176) (.n 0) (.n 0)), .atom (.mul (.n 1177) (.n 8) (.n 1176)),
    .atom (.load (.n 1178) (.n 1177) 0), .atom (.mul (.n 1179) (.n 1175) (.n 1002)),
    .atom (.add (.n 1180) (.n 1178) (.n 1179)), .atom (.mul (.n 1181) (.n 7) (.n 1173)),
    .atom (.load (.n 1182) (.n 1181) 1), .atom (.mul (.n 1183) (.n 1182) (.n 1171)),
    .atom (.add (.n 1184) (.n 1180) (.n 1183)), .atom (.load (.n 1184) (.n 1177) 2),
    .atom (.load (.n 1185) (.n 1177) 1), .atom (.load (.n 1186) (.n 10) 23),
    .atom (.mul (.n 1187) (.n 1175) (.n 1186)), .atom (.mul (.n 1188) (.n 1187) (.n 1002)),
    .atom (.add (.n 1189) (.n 1185) (.n 1188)), .atom (.mul (.n 1190) (.n 7) (.n 1173)),
    .atom (.load (.n 1191) (.n 1190) 2), .atom (.mul (.n 1192) (.n 1191) (.n 1171)),
    .atom (.add (.n 1193) (.n 1189) (.n 1192)), .atom (.load (.n 1193) (.n 1177) 3),
    .atom (.const (.n 1194) (word 2 0 0)), .atom (.mul (.n 1195) (.n 0) (.n 1194)),
    .atom (.add (.n 1196) (.n 1195) (.n 1)), .atom (.const (.n 1197) (word 2 0 0)),
    .atom (.mul (.n 1198) (.n 0) (.n 1197)),
    .callIf (.n 1196) "__loop99" [.n 1198, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8],
    .ret []]

set_option maxRecDepth 100000 in
theorem core566_body : Fn.body Data.core566 = l95Body := stmtsEqb_sound (by decide +kernel)

theorem core567_body : Fn.body Data.core567 = l96Body := stmtsEqb_sound (by decide +kernel)

theorem core569_body : Fn.body Data.core569 = l97Body := stmtsEqb_sound (by decide +kernel)

theorem core570_body : Fn.body Data.core570 = l98Body := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem core572_body : Fn.body Data.core572 = l99Body := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Main
