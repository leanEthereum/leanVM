//! The sidecar binary end to end, through the Rust client: a leaf with every kind of input, a narrowed node over
//! it from a second connection, verifying, refusals that leave the connection usable, an unknown operation sent as
//! another language's client would, the connection cap, and the socket's life across a second sidecar and a restart.

use aggregation::signers_cache;
use lean_vm::{AggregateClaims, OutputClaims, lean_da};
use sidecar::{Client, Rejection, SidecarError};
use stable_lean_vm_core::StableProver;
use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::time::{Duration, Instant};

struct Sidecar(Child);

impl Drop for Sidecar {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// The socket's path, and its lock's, removed at the end whatever happens.
struct Socket(PathBuf);

impl Drop for Socket {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
        let _ = std::fs::remove_file(self.0.with_extension("sock.lock"));
    }
}

fn command(socket: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_leanvm-sidecar"));
    command.arg("--socket").arg(socket);
    command
}

/// Starts a sidecar and waits until it serves.
fn start(socket: &Path) -> (Sidecar, Client) {
    let mut sidecar = Sidecar(command(socket).spawn().unwrap());
    let start = Instant::now();
    loop {
        if let Ok(client) = Client::connect(socket) {
            return (sidecar, client);
        }
        assert!(sidecar.0.try_wait().unwrap().is_none(), "the sidecar exited");
        assert!(start.elapsed() < Duration::from_secs(300), "the sidecar never served");
        std::thread::sleep(Duration::from_millis(50));
    }
}

fn read_frame(stream: &mut UnixStream) -> Vec<u8> {
    let mut len = [0; 8];
    stream.read_exact(&mut len).unwrap();
    let mut body = vec![0; u64::from_le_bytes(len) as usize];
    stream.read_exact(&mut body).unwrap();
    body
}

#[test]
fn sidecar_end_to_end() {
    let guard = Socket(PathBuf::from(format!(
        "/tmp/leanvm-sidecar-test-{}.sock",
        std::process::id()
    )));
    let socket = &guard.0;
    let (first, mut client) = start(socket);
    assert_eq!(
        client.prover(),
        if cfg!(feature = "experimental_prover") {
            "experimental"
        } else {
            "stable"
        }
    );

    let xmss = signers_cache::get_signers::<StableProver>(3);
    let sphincs = signers_cache::get_lean_sphincs_signers::<StableProver>(1);
    let blobs: Vec<lean_da::Blob> = vec![std::array::from_fn(|i| i as u128)];
    let leaf = client
        .aggregate(&[], &xmss[..2], &sphincs, &blobs, OutputClaims::All, 2)
        .unwrap();
    assert!(client.verify(&leaf.0, &leaf.1).unwrap());
    assert_eq!(leaf.0.num_signature_claims(), 3);
    assert_eq!(
        leaf.0.da_commitment,
        Some(lean_da::BlobMatrix::build(&blobs).unwrap().commitment())
    );

    // A second connection while the first stays open: the leaf and one more signature, keeping only one leanXMSS
    // claim of each.
    let mut other = Client::connect(socket).unwrap();
    let mut kept: Vec<_> = [&xmss[0], &xmss[2]].iter().map(|(pk, m, _)| (*pk, *m)).collect();
    kept.sort();
    let only = AggregateClaims {
        lean_xmss: kept,
        ..AggregateClaims::default()
    };
    let node = other
        .aggregate(&[leaf], &xmss[2..], &[], &[], OutputClaims::Only(&only), 1)
        .unwrap();
    assert_eq!(node.0, only);
    assert!(client.verify(&only, &node.1).unwrap());
    // Not against other claims.
    assert!(!other.verify(&AggregateClaims::default(), &node.1).unwrap());

    // Refusals leave the connection in step: two in a row.
    for rate in [0, 300] {
        match client.aggregate(&[], &xmss[..1], &[], &[], OutputClaims::All, rate) {
            Err(SidecarError::Rejected(Rejection::InvalidInput, message)) => assert!(message.contains("log_inv_rate")),
            other => panic!("rate {rate}: {other:?}"),
        }
    }

    // A client in another language sends an operation this version does not have, twice: a refusal keeps the
    // connection usable.
    let mut raw = UnixStream::connect(socket).unwrap();
    assert!(read_frame(&mut raw).starts_with(b"leanvmsc"));
    for _ in 0..2 {
        raw.write_all(&[&1u64.to_le_bytes()[..], &[7]].concat()).unwrap();
        assert_eq!(read_frame(&mut raw)[0], Rejection::Malformed as u8);
    }

    // Three connections are open: a 17th fails at once, and one more connects once another closes.
    let mut open: Vec<_> = (3..16).map(|_| Client::connect(socket).unwrap()).collect();
    match Client::connect(socket) {
        Err(SidecarError::Io(e)) => assert_eq!(e.kind(), std::io::ErrorKind::ConnectionRefused),
        other => panic!("a 17th connection: {other:?}"),
    }
    open.pop();
    let closed = Instant::now();
    while Client::connect(socket).is_err() {
        assert!(
            closed.elapsed() < Duration::from_secs(10),
            "a freed connection never reopened"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    drop(open);

    // A second sidecar leaves a live one's socket alone; a restart replaces the stale socket a killed one leaves.
    let refused = command(socket).output().unwrap();
    assert!(!refused.status.success());
    drop(first);
    assert!(socket.exists());
    let (_sidecar, _client) = start(socket);
}
