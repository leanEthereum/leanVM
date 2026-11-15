//! `guest-export <lean_vm dir> [--check]`: write the guest's Lean data under `<lean_vm dir>`
//! (paths relative to `lean_vm/`), or with `--check` fail when any file differs from what is
//! there. Stale `Bytecode*.lean` modules are removed on write and reported on check.

use leanvm_guest_export::lean_export;
use std::collections::BTreeSet;
use std::path::Path;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    let root = args.iter().find(|a| !a.starts_with("--")).expect("usage: guest-export <lean_vm dir> [--check]");
    let root = Path::new(root);

    let t = std::time::Instant::now();
    let guest = lean_export::guest();
    eprintln!(
        "guest: 2^{} slots, {} instructions of code, {} functions ({:.1?})",
        guest.prog.len().trailing_zeros(),
        guest.code_len(),
        guest.fn_ranges.len(),
        t.elapsed()
    );
    let files = lean_export::all_files();

    let data = root.join(lean_export::bytecode::DATA);
    let bytecode_modules = |dir: &Path| -> BTreeSet<String> {
        std::fs::read_dir(dir)
            .map(|es| {
                es.filter_map(|e| e.ok()?.file_name().into_string().ok())
                    .filter(|n| n.starts_with("Bytecode") && n.ends_with(".lean"))
                    .collect()
            })
            .unwrap_or_default()
    };
    let ours: BTreeSet<String> = files
        .iter()
        .filter_map(|f| f.path.strip_prefix(&format!("{}/", lean_export::bytecode::DATA)).map(str::to_string))
        .filter(|n| n.starts_with("Bytecode"))
        .collect();
    let mut stale = Vec::new();
    for extra in bytecode_modules(&data).difference(&ours) {
        if check {
            stale.push(format!("{}/{extra} (not generated)", lean_export::bytecode::DATA));
        } else {
            std::fs::remove_file(data.join(extra)).unwrap();
        }
    }
    for f in &files {
        let path = root.join(&f.path);
        let same = std::fs::read_to_string(&path).ok().as_deref() == Some(f.text.as_str());
        if check {
            if !same {
                stale.push(f.path.clone());
            }
        } else if !same {
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(&path, &f.text).unwrap();
        }
        eprintln!("{} {} ({} bytes)", if same { "=" } else if check { "!" } else { "w" }, f.path, f.text.len());
    }
    if !stale.is_empty() {
        eprintln!("stale; rerun guest-export without --check:");
        for s in &stale {
            eprintln!("  {s}");
        }
        std::process::exit(1);
    }
}
