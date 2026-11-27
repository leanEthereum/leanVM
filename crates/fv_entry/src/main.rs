//! `fv_entry INPUT OUTPUT`: [`fv_entry::prove`] from one file to another, the binary the x86 proofs are about.

use std::process::ExitCode;

/// Room for the output: the proof is far smaller.
const OUT_CAP: usize = 1 << 26;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let [_, input, output] = args.as_slice() else {
        eprintln!("usage: fv_entry INPUT OUTPUT");
        return ExitCode::FAILURE;
    };
    let input = std::fs::read(input).expect("read the input");
    let mut out = vec![0; OUT_CAP];
    // SAFETY: both buffers are live for their whole lengths, and distinct.
    let written = unsafe { fv_entry::leanvm_fv_prove(input.as_ptr(), input.len(), out.as_mut_ptr(), out.len()) };
    let Ok(written) = usize::try_from(written) else {
        eprintln!("fv_entry: error {written}");
        return ExitCode::FAILURE;
    };
    std::fs::write(output, &out[..written]).expect("write the output");
    ExitCode::SUCCESS
}
