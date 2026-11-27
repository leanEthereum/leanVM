//! `fv_entry GUEST INPUT OUTPUT`: [`fv_entry::prove`] from files to a file, the binary the x86 proofs are about.

use std::process::ExitCode;

/// Room for the output: the proof is far smaller.
const OUT_CAP: usize = 1 << 26;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let [_, guest, input, output] = args.as_slice() else {
        eprintln!("usage: fv_entry GUEST INPUT OUTPUT");
        return ExitCode::FAILURE;
    };
    let guest = std::fs::read(guest).expect("read the guest");
    let input = std::fs::read(input).expect("read the input");
    let mut out = vec![0; OUT_CAP];
    // SAFETY: the buffers are live for their whole lengths, and distinct.
    let written = unsafe {
        fv_entry::leanvm_fv_prove(
            guest.as_ptr(),
            guest.len(),
            input.as_ptr(),
            input.len(),
            out.as_mut_ptr(),
            out.len(),
        )
    };
    let Ok(written) = usize::try_from(written) else {
        eprintln!("fv_entry: error {written}");
        return ExitCode::FAILURE;
    };
    std::fs::write(output, &out[..written]).expect("write the output");
    ExitCode::SUCCESS
}
