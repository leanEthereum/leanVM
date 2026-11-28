module

public import NativeRustcVmX64.Arrays.Dot
public import NativeRustcVmX64.Arrays.EqEval
public import NativeRustcVmX64.Arrays.Powers
public import NativeRustcVmX64.Arrays.PolyEval
public import NativeRustcVmX64.Arrays.IndexMleFrom
public import NativeRustcVmX64.Arrays.PaddingWeight
public import NativeRustcVmX64.Arrays.EqEvalFn
public import NativeRustcVmX64.Arrays.ProdE
public import NativeRustcVmX64.Arrays.EqKernel
public import NativeRustcVmX64.Arrays.SumE
public import NativeRustcVmX64.Arrays.SelectorPoint
public import NativeRustcVmX64.Arrays.BufEW30Extend
public import NativeRustcVmX64.Arrays.BufEW36Extend
public import NativeRustcVmX64.Arrays.BufEW63Extend
public import NativeRustcVmX64.Arrays.BufEW230Extend
public import NativeRustcVmX64.Arrays.BufU64x230Extend

/-!
# `field.rs`'s array functions on x86-64

The contracts (`NativeRustcVmX64.Spec.Arrays`) of rustc's array functions, met given `EW::mul`'s:
`Arrays.Dot.dot_spec`, `Arrays.EqEval.eqEval_spec`, `Arrays.Powers.powers_spec`,
`Arrays.PolyEval.polyEval_spec`, `Arrays.IndexMleFrom.indexMleFrom_spec`,
`Arrays.PaddingWeight.paddingWeight_spec`, `Arrays.EqEvalFn.eqEvalFn_spec`,
`Arrays.ProdE.prodE_spec`, `Arrays.EqKernel.eqKernel_spec`; without callees
`Arrays.SumE.sumE_spec`, `Arrays.SelectorPoint.selectorPoint_spec`, the `Buf::extend`s
`Arrays.BufEW{30,36,63,230}Extend.bufEW{30,36,63,230}Extend_spec`,
`Arrays.BufU64x230Extend.bufU64x230Extend_spec`. The build fails if an axiom footprint grows
beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmX64.Arrays.Dot.dot_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.Dot.dot_spec

/-- info: 'NativeRustcVmX64.Arrays.EqEval.eqEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.EqEval.eqEval_spec

/-- info: 'NativeRustcVmX64.Arrays.Powers.powers_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.Powers.powers_spec

/-- info: 'NativeRustcVmX64.Arrays.PolyEval.polyEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.PolyEval.polyEval_spec

/-- info: 'NativeRustcVmX64.Arrays.IndexMleFrom.indexMleFrom_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.IndexMleFrom.indexMleFrom_spec

/-- info: 'NativeRustcVmX64.Arrays.PaddingWeight.paddingWeight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.PaddingWeight.paddingWeight_spec

/-- info: 'NativeRustcVmX64.Arrays.EqEvalFn.eqEvalFn_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.EqEvalFn.eqEvalFn_spec

/-- info: 'NativeRustcVmX64.Arrays.ProdE.prodE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.ProdE.prodE_spec

/-- info: 'NativeRustcVmX64.Arrays.SumE.sumE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.SumE.sumE_spec

/-- info: 'NativeRustcVmX64.Arrays.BufEW30Extend.bufEW30Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.BufEW30Extend.bufEW30Extend_spec

/-- info: 'NativeRustcVmX64.Arrays.BufEW36Extend.bufEW36Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.BufEW36Extend.bufEW36Extend_spec

/-- info: 'NativeRustcVmX64.Arrays.BufEW63Extend.bufEW63Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.BufEW63Extend.bufEW63Extend_spec

/-- info: 'NativeRustcVmX64.Arrays.BufEW230Extend.bufEW230Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.BufEW230Extend.bufEW230Extend_spec

/-- info: 'NativeRustcVmX64.Arrays.BufU64x230Extend.bufU64x230Extend_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.BufU64x230Extend.bufU64x230Extend_spec

/-- info: 'NativeRustcVmX64.Arrays.SelectorPoint.selectorPoint_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.SelectorPoint.selectorPoint_spec

/-- info: 'NativeRustcVmX64.Arrays.EqKernel.eqKernel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Arrays.EqKernel.eqKernel_spec
