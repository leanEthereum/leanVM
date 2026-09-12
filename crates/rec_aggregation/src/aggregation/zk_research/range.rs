//! Research-only replacement of exponent range probes by local arithmetic.

use std::collections::BTreeSet;

use lean_compiler::{Ast, Expr, LtBound, Stmt, StmtKind};

fn helpers(bits: u32) -> String {
    let bind = if bits == 0 {
        "    assert value == 1\n".to_string()
    } else {
        format!(
            r#"    bits = StackBuf({bits})
    hint_decompose_bits_exponent(bits, value, {bits})
    product = 1
    for j in unroll(0, {bits}):
        bit = bits[j]
        bits[j] = bit * bit
        product = product * (1 + bit * (GEN ** (2 ** j) + 1))
    assert product == value
"#
        )
    };
    let inline = if bits <= 4 { "@inline\n" } else { "" };
    format!(
        r#"
@inline
def zk_exp_core_{bits}(value):
{bind}    return

{inline}def zk_bind_exp_{bits}(value):
    zk_exp_core_{bits}(value)
    return

{inline}def zk_range_{bits}(value, bound):
    zk_exp_core_{bits}(value)
    complement = (bound / GEN) / value
    zk_exp_core_{bits}(complement)
    return
"#
    )
}

fn rewrite(body: &mut [Stmt], widths: &mut BTreeSet<u32>) -> usize {
    let mut count = 0;
    for statement in body {
        match &mut statement.kind {
            StmtKind::AssertLt(value, bound) => {
                let (bits, name, args) = match bound {
                    LtBound::Const(bound) => {
                        assert!((1..=1 << lean_vm::cpu::MIN_LOG_MEM).contains(bound));
                        let bits = u64::BITS - (*bound - 1).leading_zeros();
                        if bound.is_power_of_two() {
                            (bits, format!("zk_bind_exp_{bits}"), vec![value.clone()])
                        } else {
                            (
                                bits,
                                format!("zk_range_{bits}"),
                                vec![value.clone(), Expr::GPow(*bound as u128)],
                            )
                        }
                    }
                    LtBound::Runtime(bound) => {
                        let bits = lean_vm::cpu::MIN_LOG_MEM as u32;
                        (bits, format!("zk_range_{bits}"), vec![value.clone(), bound.clone()])
                    }
                };
                widths.insert(bits);
                statement.kind = StmtKind::Call(name, args);
                count += 1;
            }
            StmtKind::If { then, els, .. } => {
                count += rewrite(then, widths) + rewrite(els, widths);
            }
            StmtKind::For { body, .. } | StmtKind::Unroll { body, .. } => count += rewrite(body, widths),
            _ => {}
        }
    }
    count
}

/// Runtime bounds retain the compiler's precondition: their exponents are at most 2^MIN_LOG_MEM.
pub(super) fn eliminate_probes(ast: &mut Ast) -> usize {
    assert!(ast.funcs.iter().all(|f| !f.name.starts_with("zk_bind_exp_")
        && !f.name.starts_with("zk_range_")
        && !f.name.starts_with("zk_exp_core_")));
    let mut widths = BTreeSet::new();
    let count = ast.funcs.iter_mut().map(|f| rewrite(&mut f.body, &mut widths)).sum();
    for bits in widths {
        ast.funcs.extend(
            lean_compiler::parse(&helpers(bits))
                .expect("local exponent helpers")
                .funcs,
        );
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;
    use lean_compiler::compile;
    use primitives::field::{F192, G, g_pow};

    #[test]
    fn local_ranges_bind_untrusted_bits_and_complements() {
        for width in [1u32, 3, 16] {
            let source = helpers(width).replace(
                &format!("hint_decompose_bits_exponent(bits, value, {width})"),
                "hint_witness(bits, \"bits\")",
            ) + &format!(
                "\ndef main():\n    value = hint_witness(\"value\")\n    bound = hint_witness(\"bound\")\n    zk_range_{width}(value, bound)\n    return\n"
            );
            let mut program = compile(&lean_compiler::parse(&source).unwrap());
            let capacity = 1usize << width;
            let encode = |n: usize| {
                (0..width)
                    .map(|j| F192::new(((n >> j) & 1) as u64, 0, 0))
                    .collect::<Vec<_>>()
            };
            let cases = [
                (0, 1),
                (0, capacity),
                (capacity - 1, capacity),
                (capacity / 2 - 1, capacity / 2),
            ];
            for (value, bound) in cases {
                program.set_witness("value", vec![vec![F192::from(g_pow(value))]]);
                program.set_witness("bound", vec![vec![F192::from(g_pow(bound))]]);
                program.set_witness("bits", vec![encode(value), encode(bound - 1 - value)]);
                let execution = program.execute([F192::ZERO; 2]);
                assert!(execution.unconstrained_reads.is_empty());
                for (pc, _) in execution.instruction_sites() {
                    if program.fn_at(pc).starts_with("zk_") || width <= 4 {
                        assert!(!matches!(program.prog[pc as usize], lean_vm::cpu::Op::Deref { .. }));
                    }
                }
            }
            let invalid = [
                (F192::ZERO, F192::from(g_pow(capacity)), encode(0), encode(0)),
                (
                    F192::from(g_pow(capacity)),
                    F192::from(g_pow(capacity)),
                    encode(0),
                    encode(0),
                ),
                (F192::from(G.inv()), F192::from(g_pow(capacity)), encode(0), encode(0)),
                (F192::ONE, F192::ONE, encode(0), encode(0)),
                (F192::from(g_pow(1)), F192::from(g_pow(1)), encode(1), encode(0)),
            ];
            for (value, bound, first, second) in invalid {
                program.set_witness("value", vec![vec![value]]);
                program.set_witness("bound", vec![vec![bound]]);
                program.set_witness("bits", vec![first, second]);
                assert!(std::panic::catch_unwind(|| program.execute([F192::ZERO; 2])).is_err());
            }
            for forged in [F192::new(2, 0, 0), F192::new(0, 1, 0)] {
                let value = F192::ONE + forged * (F192::from(G) + F192::ONE);
                let mut bits = encode(0);
                bits[0] = forged;
                program.set_witness("value", vec![vec![value]]);
                program.set_witness("bound", vec![vec![F192::from(G) * value]]);
                program.set_witness("bits", vec![bits, encode(0)]);
                assert!(std::panic::catch_unwind(|| program.execute([F192::ZERO; 2])).is_err());
            }
        }
    }
}
