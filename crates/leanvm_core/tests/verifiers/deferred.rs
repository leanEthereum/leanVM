//! The claims `verify_core` leaves on the program and the circuits: they bind what
//! `verify` checks whole, they merge across proofs, and Python leaves the same ones.

use super::python_verifier::PythonStatement;
use leanvm_core::cpu::{CpuError, DeferredClaims, Program};
use leanvm_core::pcs::Rate;
use leanvm_core::rv::Region;
use leanvm_core::rv::asm::*;
use primitives::field::F192;

/// A program that reads its RAM image, so that the image's share of the program claim
/// is not zero.
fn image_program(image: Vec<u64>) -> Program {
    let text = Asm::new()
        .li(Reg::T0, Region::RAM.base())
        .load(Ld, Reg::A0, 0, Reg::T0)
        .load(Ld, Reg::A1, 8, Reg::T0)
        .r(Add, Reg::A0, Reg::A0, Reg::A1)
        .li(Reg::A1, 0)
        .exit()
        .finish();
    Program::new(&text, Region::TEXT.base(), image, 3, 0).expect("valid instruction program")
}

fn claims_of(program: &Program, rate: Rate) -> DeferredClaims {
    let (proof, output, _) = program.prove(&[], rate).expect("the run halts");
    assert_eq!(output, [16, 0, 0, 0]);
    program
        .verify_core(&output, &proof)
        .expect("the proof's own checks pass")
}

fn assert_refused_by_the_program(claims: &DeferredClaims, program: &Program, what: &str) {
    assert_eq!(
        program.check_deferred(claims),
        Err(CpuError::Constraint(leanvm_core::constraints::Error::FinalMismatch)),
        "{what}"
    );
}

/// Every part of a claim is bound: a value, a point, a weight, or the program it is
/// checked against.
#[test]
fn a_tampered_deferred_claim_is_refused() {
    let program = image_program(vec![7, 9]);
    let honest = claims_of(&program, Rate::MIN);
    program.check_deferred(&honest).expect("the honest claims hold");

    let mut claims = honest.clone();
    claims.program.value += F192::ONE;
    assert_refused_by_the_program(&claims, &program, "a program value");
    let mut claims = honest.clone();
    claims.program.terms[0].1.twist[0] += F192::ONE;
    assert_refused_by_the_program(&claims, &program, "a multiplicity bit's weight");
    let mut claims = honest.clone();
    claims.program.terms[0].1.bytecode[0] += F192::ONE;
    assert_refused_by_the_program(&claims, &program, "the bytecode point");
    let mut claims = honest.clone();
    claims.program.terms[0].1.image_weight += F192::ONE;
    assert_refused_by_the_program(&claims, &program, "the image's weight");
    assert_refused_by_the_program(&honest, &image_program(vec![7, 10]), "another image");

    for f in 0..honest.circuits.len() {
        let mut claims = honest.clone();
        claims.circuits[f].value += F192::ONE;
        assert!(
            matches!(program.check_deferred(&claims), Err(CpuError::Flock { .. })),
            "circuit {f}'s value"
        );
        let mut claims = honest.clone();
        claims.circuits[f].terms[0].1.s_hat_v[1] += F192::ONE;
        assert!(
            matches!(program.check_deferred(&claims), Err(CpuError::Flock { .. })),
            "circuit {f}'s slices"
        );
    }
}

/// Two proofs' claims merge into one under a challenge, which holds exactly when both do.
#[test]
fn merged_claims_hold_when_all_of_theirs_do() {
    let program = image_program(vec![7, 9]);
    let proofs = [Rate::MIN, Rate::new(2).expect("a supported rate")].map(|rate| claims_of(&program, rate));
    assert_ne!(proofs[0], proofs[1], "two transcripts, two sets of claims");
    let gamma = F192::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x5eed);
    program
        .check_deferred(&DeferredClaims::merge(&proofs, gamma))
        .expect("the merged claims hold");

    let mut forged = proofs.clone();
    forged[1].program.value += F192::ONE;
    assert_refused_by_the_program(
        &DeferredClaims::merge(&forged, gamma),
        &program,
        "a false program claim among them",
    );
    let mut forged = proofs;
    forged[0].circuits[3].value += F192::ONE;
    assert!(matches!(
        program.check_deferred(&DeferredClaims::merge(&forged, gamma)),
        Err(CpuError::Flock { .. })
    ));
}

/// The claims as Python renders them: one line per field, every element as its three
/// limbs in hexadecimal, high first.
fn render(claims: &DeferredClaims) -> String {
    fn line(name: &str, values: &[F192]) -> String {
        std::iter::once(name.to_owned())
            .chain(
                values
                    .iter()
                    .map(|v| format!("{:016x}{:016x}{:016x}", v.c2, v.c1, v.c0)),
            )
            .collect::<Vec<_>>()
            .join(" ")
    }
    let [(weight, point)] = &claims.program.terms[..] else {
        panic!("one proof's claim has one point")
    };
    assert_eq!(*weight, F192::ONE);
    let mut lines = vec![
        line("program value", &[claims.program.value]),
        line("program bytecode", &point.bytecode),
        line("program twist", &point.twist),
        line("program image_weight", &[point.image_weight]),
        line("program image_point", &point.image_point),
    ];
    for (f, claim) in claims.circuits.iter().enumerate() {
        let [(_, form)] = &claim.terms[..] else {
            panic!("one proof's claim has one point")
        };
        lines.extend([
            line(&format!("circuit {f} value"), &[claim.value]),
            line(&format!("circuit {f} alpha"), &[form.alpha]),
            line(
                &format!("circuit {f} row"),
                &[&[form.z_skip][..], &form.x_inner_rest].concat(),
            ),
            line(&format!("circuit {f} column"), &form.r_inner_rest),
            line(&format!("circuit {f} slices"), &form.s_hat_v),
        ]);
    }
    lines.join("\n")
}

/// The two verifiers leave the same claims on the same proof.
#[test]
fn python_leaves_the_same_deferred_claims() {
    let program = image_program(vec![7, 9]);
    let (proof, output, _) = program.prove(&[], Rate::MIN).expect("the run halts");
    let claims = program
        .verify_core(&output, &proof)
        .expect("the proof's own checks pass");
    let raw = program.verify_to_raw(&output, &proof).expect("the proof verifies");
    let python = PythonStatement::new("deferred", &program, &output).deferred(&raw);
    assert_eq!(python, render(&claims));
}
