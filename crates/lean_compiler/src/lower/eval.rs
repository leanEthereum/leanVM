//! Compile-time evaluation: what an expression is worth before anything runs.
//!
//! Queries emit no instructions and leave compiler state unchanged.
//!
//! There are two answers and the POSITION of a use picks one:
//! [`FnLower::try_const_int`] for a size, an index, a bound or an exponent,
//! [`FnLower::try_field_const`] for a value, where `+` is XOR. They disagree on
//! a sum of overlapping integers, and `const(...)` is how an author says which
//! was meant.

use super::*;

/// The readings of one expression: as many as its shape has. Produced by
/// [`FnLower::eval`], which is the only walk that computes them.
#[derive(Clone, Copy, Default)]
pub(super) struct Known {
    /// The compile-time INTEGER, wanted by a size, an index, a bound, an exponent.
    pub(super) int: Option<u128>,
    /// The FIELD element a value position sees, where `+` is XOR.
    pub(super) field: Option<F192>,
    /// The ADDRESS the compiler tracks: a base cell times `g^exp`.
    pub(super) addr: Option<GAddr>,
}

impl Known {
    /// The integer and field readings when both exist and disagree.
    pub(super) fn diverging_readings(self) -> Option<(u128, F192)> {
        let (n, f) = (self.int?, self.field?);
        (f != lit_field(n)).then_some((n, f))
    }
}

/// `a·b` in the [`GAddr`] representation: exponents add, and at most one factor
/// may carry a runtime base (two pointers can't be multiplied symbolically).
fn gmul(a: GAddr, b: GAddr) -> Option<GAddr> {
    let base = match (a.base, b.base) {
        (None, x) | (x, None) => x,
        (Some(_), Some(_)) => return None,
    };
    Some(GAddr {
        base,
        exp: a.exp.checked_add(b.exp)?,
        // Only a based address carries a run, and at most one side is based, so
        // the shift keeps its origin: `addr(sb) * GEN ** k` stays bounded by `sb`.
        run: a.run.or(b.run),
    })
}

/// `b^k` by square-and-multiply, in logarithmically many field operations.
pub(super) fn field_pow(b: F192, mut k: u32) -> F192 {
    let (mut acc, mut sq) = (F192::ONE, b);
    while k > 0 {
        if k & 1 == 1 {
            acc *= sq;
        }
        k >>= 1;
        if k > 0 {
            sq *= sq;
        }
    }
    acc
}

impl FnLower<'_> {
    /// Everything `e` is worth before anything runs, from ONE walk.
    ///
    /// An expression genuinely has more than one reading, and which is wanted
    /// depends on the POSITION of the use: `x = 2` names the integer 2, the field
    /// element 2, and the address `g^1`, all three at once. So the evaluator
    /// computes every reading a shape has and the caller takes the one its
    /// position means.
    ///
    /// Keeping the readings together lets each use reject an ambiguous value
    /// by comparing them, without evaluating the expression again.
    pub(super) fn eval(&self, e: &Expr) -> Known {
        // Deliberately NO address: only a LITERAL reads as one, and only under the
        // guard below. Attaching it here gave `const(2^k)` and `len(A)` an address
        // that `Expr::Lit` alone used to have, which slipped them past
        // `heap_addr`'s ambiguity guard: `buf[const(8)]` on a `HeapBuf(4)`
        // compiled and aliased cell 3, while the bare `buf[8]` it means was
        // rejected. One spelling naming two different cells is exactly what that
        // guard exists to stop.
        let int = |n: u128| Known {
            int: Some(n),
            field: Some(lit_field(n)),
            addr: None,
        };
        let gpow = |exp: u128| Known {
            int: None,
            field: Some(g_pow_u128(exp).into()),
            addr: Some(GAddr {
                base: None,
                exp,
                run: None,
            }),
        };
        match e {
            // `g = x`, so the literal `2^k` IS `g^k`, but ONLY while `k < 64`: at
            // and above it the modulus folds the monomial back into the low limb
            // while the literal's bit `k` lands in the next limb, the tower
            // coefficient of `y`. Without the guard the guest's own `Y_TOWER =
            // 2^64` would read as `g^64` in a pointer position.
            Expr::Lit(n) => Known {
                addr: (n.is_power_of_two() && *n < (1 << 64)).then(|| GAddr {
                    base: None,
                    exp: n.trailing_zeros() as u128,
                    run: None,
                }),
                ..int(*n)
            },
            Expr::Gen => gpow(1),
            Expr::GPow(k) => gpow(*k),
            Expr::GenPow(x) => match self.eval(x).int.and_then(|n| u32::try_from(n).ok()) {
                Some(k) => gpow(u128::from(k)),
                None => Known::default(),
            },
            Expr::Var(v) => {
                let Some(b) = self.scope.bound(v) else {
                    return Known::default();
                };
                let int = b.int;
                match b.val {
                    Binding::FConst(c) => Known {
                        int,
                        field: Some(c),
                        addr: None,
                    },
                    Binding::Gaddr(ga) => Known {
                        int,
                        // A constant g-power also reads as that field element.
                        field: (ga.base.is_none()).then(|| g_pow_u128(ga.exp).into()),
                        addr: Some(ga),
                    },
                    // A plain scalar is its own base, unshifted.
                    Binding::Scalar(c) => Known {
                        int,
                        field: None,
                        addr: Some(GAddr {
                            base: Some(c),
                            exp: 0,
                            run: None,
                        }),
                    },
                    Binding::Stack(..) => Known {
                        int,
                        ..Known::default()
                    },
                }
            }
            // Each operand is evaluated ONCE: a reading per arm would re-walk the
            // subtree, which is exponential in the nesting depth.
            //
            // `+` is integer addition in an index and XOR in a value, so it has
            // both; `-`, `//` and `%` have no field meaning, so only the integer.
            Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Mod(a, b) => {
                let (x, y) = (self.eval(a), self.eval(b));
                if matches!(e, Expr::Div(..) | Expr::Mod(..)) && y.int == Some(0) {
                    self.fail(match e {
                        Expr::Div(..) => "compile-time division by zero",
                        _ => "compile-time modulo by zero",
                    })
                };
                let int = || {
                    let (n, m) = (x.int?, y.int?);
                    match e {
                        Expr::Add(..) => n.checked_add(m),
                        Expr::Sub(..) => n.checked_sub(m),
                        Expr::Mul(..) => n.checked_mul(m),
                        Expr::Div(..) => Some(n / m),
                        _ => Some(n % m),
                    }
                };
                Known {
                    int: int(),
                    field: match e {
                        Expr::Add(..) => x.field.and_then(|f| Some(f + y.field?)),
                        Expr::Mul(..) => x.field.and_then(|f| Some(f * y.field?)),
                        _ => None,
                    },
                    addr: match e {
                        Expr::Mul(..) => x.addr.and_then(|p| gmul(p, y.addr?)),
                        _ => None,
                    },
                }
            }
            Expr::Pow(b, x) => {
                let (base, exp) = (self.eval(b), self.eval(x).int.and_then(|n| u32::try_from(n).ok()));
                Known {
                    int: base.int.and_then(|n| n.checked_pow(exp?)),
                    field: base.field.and_then(|f| Some(field_pow(f, exp?))),
                    addr: None,
                }
            }
            // A constant-array element, as a field value or as the integer those
            // bits spell.
            Expr::Index(..) => match self.const_array_elem(e) {
                Some(v) => Known {
                    int: (v.c2 == 0).then_some(v.c0 as u128 | ((v.c1 as u128) << 64)),
                    field: Some(v),
                    addr: None,
                },
                None => Known::default(),
            },
            Expr::Call(f, args) if f == "f192" && args.len() == 3 => {
                let limb = |i: usize| match &args[i] {
                    Expr::Lit(n) => u64::try_from(*n).ok(),
                    _ => None,
                };
                Known {
                    field: (|| Some(F192::new(limb(0)?, limb(1)?, limb(2)?)))(),
                    ..Known::default()
                }
            }
            // `const(e)`: the one construct that asks for the INTEGER reading in a
            // position that would otherwise take the field one. It reinterprets the
            // OPERATORS, so its leaves must mean the same thing either way.
            Expr::Call(f, args) if f == "const" && args.len() == 1 => {
                self.check_const_leaves(&args[0]);
                match self.eval(&args[0]).int {
                    Some(n) => int(n),
                    None => Known::default(),
                }
            }
            Expr::Call(..) => match self.const_len(e) {
                Some(n) => int(n as u128),
                None => Known::default(),
            },
            _ => Known::default(),
        }
    }

    /// A compile-time integer. `None` means a runtime value, or arithmetic outside
    /// the source language's `u128` literal domain.
    pub(super) fn try_const_int(&self, e: &Expr) -> Option<u128> {
        self.eval(e).int
    }

    /// The address the compiler tracks for `e`: a base cell times `g^exp`.
    pub(super) fn gaddr_of(&self, e: &Expr) -> Option<GAddr> {
        self.eval(e).addr
    }

    /// `e` as a compile-time FIELD constant, where `+` is XOR. `None` for a
    /// runtime value or for arithmetic the field has no meaning for (`-`, `//`,
    /// `%`).
    pub(super) fn try_field_const(&self, e: &Expr) -> Option<F192> {
        self.eval(e).field
    }

    /// A compile-time integer index. The general integer evaluator is narrowed
    /// here so stack offsets, bounds, and immediate exponents remain `u32`.
    pub(super) fn try_const_index(&self, idx: &Expr) -> Option<u32> {
        u32::try_from(self.try_const_int(idx)?).ok()
    }

    /// A stack index or compile-time slice bound: [`Self::try_const_index`],
    /// required to succeed.
    pub(super) fn const_index(&self, idx: &Expr) -> u32 {
        let k = self.try_const_int(idx).unwrap_or_else(|| {
            self.fail(format!(
                "a StackBuf index must be a compile-time integer, got `{idx:?}`"
            ))
        });
        u32::try_from(k).unwrap_or_else(|_| self.fail(format!("stack index {k} does not fit in u32")))
    }

    /// The exponent of `GEN ** e`: a compile-time integer, required to succeed.
    pub(super) fn gpow_exp(&self, e: &Expr) -> u128 {
        self.try_const_index(e)
            .unwrap_or_else(|| self.fail(format!("`GEN ** e` needs a compile-time integer exponent, got `{e:?}`")))
            as u128
    }

    /// If `e` is `NAME[i]` for a top-level constant array `NAME` with a
    /// compile-time index `i`, its element (a raw `u128`).
    fn const_array_elem(&self, e: &Expr) -> Option<F192> {
        if let Expr::Index(arr, idx) = e
            && let Expr::Var(v) = arr.as_ref()
            && let Some(a) = self.const_arrays.get(v)
        {
            let i = self.try_const_index(idx)? as usize;
            return Some(
                *a.get(i).unwrap_or_else(|| {
                    self.fail(format!("const array `{v}` index {i} out of bounds (len {})", a.len()))
                }),
            );
        }
        None
    }

    /// If `e` is `len(NAME)` for a top-level constant array `NAME`, its length.
    fn const_len(&self, e: &Expr) -> Option<usize> {
        if let Expr::Call(f, args) = e
            && f == "len"
            && args.len() == 1
            && let Expr::Var(v) = &args[0]
        {
            return self.const_arrays.get(v).map(|a| a.len());
        }
        None
    }

    /// The surviving operand of `a + b` when the other is a compile-time zero,
    /// which contributes nothing and (being a constant) has no side effect to
    /// preserve. So `x + 0` lowers to just `x`: no cell, no XOR. Kills the
    /// `acc = 0; acc = acc + t` accumulator seed and similar.
    pub(super) fn add_identity<'e>(&self, a: &'e Expr, b: &'e Expr) -> Option<&'e Expr> {
        if self.try_field_const(a) == Some(F192::ZERO) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F192::ZERO)).then_some(a)
    }

    /// The surviving operand of `a * b` when the other is a compile-time one, a
    /// no-op multiply. Kills the `acc = GEN ** 0` (= 1) accumulator seed's first
    /// `1 * f` in every product loop.
    pub(super) fn mul_identity<'e>(&self, a: &'e Expr, b: &'e Expr) -> Option<&'e Expr> {
        if self.try_field_const(a) == Some(F192::ONE) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F192::ONE)).then_some(a)
    }

    /// The field value of `e` when it is a trivial compile-time constant (a
    /// literal, a literal-bound name, or `GEN ** 0`), for the `x*1`/`x+0`
    /// arithmetic identities and the `== 0` test of [`Self::lower_if`].
    pub(super) fn try_lit(&self, e: &Expr) -> Option<u64> {
        match e {
            Expr::Lit(n) => u64::try_from(*n).ok(),
            Expr::Var(v) => self.scope.int(v).and_then(|n| u64::try_from(n).ok()),
            Expr::GPow(0) => Some(1),
            _ => None,
        }
    }

    /// Check the LEAVES of a `const(...)`. The wrapper reinterprets the
    /// OPERATORS as integer arithmetic, which is its whole purpose, so their two
    /// readings are expected to diverge (`3 + 1` is the integer 4 and the value
    /// 2). A LEAF is different: `const(...)` cannot change what a name already
    /// stands for, so a leaf whose own two readings disagree would have the
    /// wrapper hand back a value that leaf never had.
    ///
    /// `n = 2 + 3` is the case. The cell holds `2 XOR 3` = 1 while the name's
    /// integer reading is 5, so `assert n == 1` and `assert const(n) == 5` both
    /// passed, in one program. This is the ambiguity `if const(...)` already
    /// rejects per side, one level up, and the rule is the same one.
    fn check_const_leaves(&self, e: &Expr) {
        match e {
            Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::Mod(a, b)
            | Expr::Pow(a, b) => {
                self.check_const_leaves(a);
                self.check_const_leaves(b);
            }
            Expr::Call(f, args) if f == "const" && args.len() == 1 => self.check_const_leaves(&args[0]),
            leaf => {
                if let Some((n, f)) = self.eval(leaf).diverging_readings() {
                    self.fail(format!(
                        "const(...) reads its operators as integer arithmetic, but it cannot reinterpret \
                         `{leaf:?}`, which is the integer {n} and the value {:#x}:{:#x}: two different \
                         numbers. Bind it in one regime and name that one",
                        f.c1, f.c0
                    ))
                }
            }
        }
    }

    /// The exponent of `e` when it is a *constant* g-power small enough to ride a
    /// `DEREF` `β` immediate, for the constant factor of a product index.
    ///
    /// Folds `e` only where the readings agree: either the compiler tracks it as an
    /// address, or `e` is the integer `2^j` AND its field value is `g^j`, in
    /// which case both readings name cell `j` and folding decides nothing.
    pub(super) fn const_gpow(&self, e: &Expr) -> Option<u32> {
        let k = self.eval(e);
        if let Some(GAddr { base: None, exp, .. }) = k.addr
            && exp <= FOLD_MAX
        {
            return Some(exp as u32);
        }
        // `g = x`, so the integer `2^j` reads as `g^j`, but ONLY for `j < 64`:
        // at and above that the modulus folds the monomial back into the low
        // limb while the literal's bit lands in the tower coefficient of `y`.
        let n = k.int?;
        if !n.is_power_of_two() || n >= (1 << 64) {
            return None;
        }
        let j = n.trailing_zeros();
        (u128::from(j) <= FOLD_MAX && k.field? == g_pow_u128(u128::from(j)).into()).then_some(j)
    }
}
