//! Targets that fail on purpose, one way each, so a new machine can check that the supervisor catches every kind of
//! failure: `LEANVM_FUZZ_SELFTEST=1 cargo leanvm-fuzz run --targets selftest --duration 3m --mem-limit-mb 4096`, then
//! `report` should list each. Registered only when `LEANVM_FUZZ_SELFTEST` is set.

use crate::{Cost, Ctx, Finding, Outcome, Source, Target};

fn rare(src: &mut Source) -> bool {
    src.chance(1, 50)
}

fn finding(src: &mut Source, _: &Ctx) -> Outcome {
    if rare(src) {
        return Err(Finding::critical("selftest: a finding", "returned on purpose"));
    }
    Ok(())
}

fn panic(src: &mut Source, _: &Ctx) -> Outcome {
    if rare(src) {
        let v: Vec<u8> = Vec::new();
        let _ = v[src.below(10) + 1];
    }
    Ok(())
}

fn abort(src: &mut Source, _: &Ctx) -> Outcome {
    if rare(src) {
        std::process::abort();
    }
    Ok(())
}

#[allow(unconditional_recursion)]
fn deep(n: u64) -> u64 {
    std::hint::black_box([0u8; 4096]);
    deep(std::hint::black_box(n + 1)) + 1
}

fn stack_overflow(src: &mut Source, _: &Ctx) -> Outcome {
    if rare(src) {
        deep(0);
    }
    Ok(())
}

fn hang(src: &mut Source, _: &Ctx) -> Outcome {
    if rare(src) {
        loop {
            std::thread::sleep(std::time::Duration::from_secs(1));
        }
    }
    Ok(())
}

fn memory(src: &mut Source, _: &Ctx) -> Outcome {
    if rare(src) {
        let mut hog: Vec<Vec<u8>> = Vec::new();
        let mut rng = crate::Rng::new(1);
        loop {
            // Incompressible, or a compressing kernel keeps it out of the resident set.
            let mut block = vec![0u8; 1 << 26];
            rng.fill(&mut block);
            hog.push(block);
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
    Ok(())
}

fn pool_panic(src: &mut Source, _: &Ctx) -> Outcome {
    if rare(src) {
        parallel::for_each(64, |i| assert!(i != 37, "a panic inside a pool job"));
    }
    Ok(())
}

pub static TARGETS: &[&Target] = &[
    &Target {
        name: "selftest-finding",
        about: "returns a finding now and then",
        cost: Cost::Cheap,
        run: finding,
    },
    &Target {
        name: "selftest-panic",
        about: "panics now and then",
        cost: Cost::Cheap,
        run: panic,
    },
    &Target {
        name: "selftest-abort",
        about: "aborts the process now and then",
        cost: Cost::Cheap,
        run: abort,
    },
    &Target {
        name: "selftest-stack-overflow",
        about: "overflows its stack now and then",
        cost: Cost::Cheap,
        run: stack_overflow,
    },
    &Target {
        name: "selftest-hang",
        about: "never returns now and then",
        cost: Cost::Cheap,
        run: hang,
    },
    &Target {
        name: "selftest-memory",
        about: "allocates without bound now and then",
        cost: Cost::Cheap,
        run: memory,
    },
    &Target {
        name: "selftest-pool-panic",
        about: "panics inside a thread-pool job now and then",
        cost: Cost::Cheap,
        run: pool_panic,
    },
];
