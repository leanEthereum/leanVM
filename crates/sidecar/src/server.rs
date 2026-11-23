//! The server: a thread per connection reads and decodes requests and verifies proofs, and the thread that calls
//! [`serve`], the one that started the prover's pool, proves them one at a time. Also the server's half of the
//! protocol: requests in, the hello and responses out.

use crate::wire::{
    self, Cursor, Frame, Hello, Incoming, OK, OP_AGGREGATE, OP_VERIFY, Outcome, Proven, RawLeanSphincs, RawLeanXmss,
};
use crate::{Blob, Rejection};
use aggregation::{AggregateError, AggregateProof};
use claims::{AggregateClaims, OutputClaims};
use isa::Prover;
use lean_sphincs::{LeanSphincsPublicKey, LeanSphincsSignature};
use lean_xmss::{LeanXmssPublicKey, LeanXmssSignature};
use std::convert::Infallible;
use std::fs::{File, TryLockError};
use std::io::{self, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{FileTypeExt, OpenOptionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// The longest request body taken, in bytes: room for every blob and child a request may have and thousands of
/// signatures, while bounding the memory a connection holds.
const MAX_REQUEST: u64 = 64 << 20;

/// The most connections served at once; another is closed before its hello, so its client fails rather than wait.
/// With [`MAX_REQUEST`], it bounds the memory requests hold, queued ones included: each connection has at most one.
const MAX_CONNECTIONS: usize = 16;

/// A request, its client's connection, and where its outcome goes.
type Job = (Request, UnixStream, Sender<Outcome>);

/// Writes a status line to stderr, ignoring I/O errors so a closed or full stderr never panics the server.
fn log(args: std::fmt::Arguments<'_>) {
    let _ = writeln!(io::stderr(), "{args}");
}

/// Starts prover `P` on `threads` threads (0: one per core), builds the aggregation program and warms up, then listens
/// on `socket`, replacing a stale one a sidecar that stopped left, and serves until the process ends, proving on the
/// calling thread. The socket appears once the sidecar is ready to prove. Returns only on an error before serving,
/// which a second sidecar on the same socket gets before it starts anything.
///
/// Call it from the main thread: a panic while proving, a bug, then ends the process.
pub fn serve<P: Prover>(socket: &Path, threads: usize) -> io::Result<Infallible> {
    std::os::unix::net::SocketAddr::from_pathname(socket)?;
    let _lock = lock(socket)?;
    remove_stale(socket)?;
    P::set_num_threads(threads);
    P::init();
    warm_up::<P>();
    let listener = UnixListener::bind(socket)?;
    let hello = encode_hello(&Hello {
        max_request: MAX_REQUEST,
        tag: verifier::TAG.to_vec(),
        prover: P::NAME.into(),
    });
    let (jobs, queue) = mpsc::channel();
    thread::Builder::new()
        .name("accept".into())
        .spawn(move || accept(&listener, &jobs, hello.into()))?;
    log(format_args!("serving {} with the {} prover", socket.display(), P::NAME));
    prove_forever::<P>(&queue)
}

/// A fresh process's first proofs are slower, touching memory the allocator then keeps: this pays for it before the
/// first request, with a discarded leaf and a full recursion over it, at rate 1/4, the one used in practice (a lower
/// rate, a larger `log_inv_rate`, still pays for its extra memory on its first proof). A blob is the one input that
/// needs no key.
fn warm_up<P: Prover>() {
    let blobs = lean_da::BlobMatrix::build(&[[0; lean_da::BLOB_SYMBOLS]]).expect("one blob");
    let rate = 2;
    let leaf = aggregation::aggregate::<P>(&[], vec![], vec![], Some(&blobs), OutputClaims::All, rate)
        .expect("the warm-up's leaf proves");
    let children = vec![(leaf.0, leaf.1); aggregation::MAX_RECURSIONS];
    aggregation::aggregate::<P>(&children, vec![], vec![], None, OutputClaims::All, rate)
        .expect("the warm-up's recursion proves");
}

/// Locks `<socket>.lock`, which the process holds until it ends, so that one sidecar at a time owns the socket. A
/// symlink or a FIFO there is refused rather than followed or waited on.
fn lock(socket: &Path) -> io::Result<File> {
    let mut path = socket.as_os_str().to_owned();
    path.push(".lock");
    let file = File::options()
        .create(true)
        .truncate(false)
        .write(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(&path)?;
    match file.try_lock() {
        Ok(()) => Ok(file),
        Err(TryLockError::WouldBlock) => Err(io::Error::new(
            io::ErrorKind::AddrInUse,
            format!("another sidecar serves {}", socket.display()),
        )),
        Err(TryLockError::Error(e)) => Err(e),
    }
}

/// Removes the socket a sidecar that stopped left, and nothing else: not another file, nor a socket something listens
/// on. Holding the lock, no other sidecar binds meanwhile.
fn remove_stale(socket: &Path) -> io::Result<()> {
    let metadata = match std::fs::symlink_metadata(socket) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        metadata => metadata?,
    };
    if !metadata.file_type().is_socket() {
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!("{} is not a socket", socket.display()),
        ));
    }
    // Only a refused connection says nothing listens: one we may not open can be another program's.
    match UnixStream::connect(socket) {
        Err(e) if e.kind() == io::ErrorKind::ConnectionRefused => std::fs::remove_file(socket),
        Ok(_) => Err(io::Error::new(
            io::ErrorKind::AddrInUse,
            format!("something else listens on {}", socket.display()),
        )),
        Err(e) => Err(e),
    }
}

fn prove_forever<P: Prover>(queue: &Receiver<Job>) -> ! {
    loop {
        let (request, client, reply) = queue.recv().expect("the accept thread never ends");
        let summary = format!(
            "{} children, {} leanXMSS, {} leanSPHINCS, {} blobs, rate {}",
            request.children.len(),
            request.raw_lean_xmss.len(),
            request.raw_lean_sphincs.len(),
            request.blobs.len(),
            request.log_inv_rate,
        );
        if hung_up(&client) {
            log(format_args!("{summary}: dropped, its client hung up"));
            continue;
        }
        let outcome = aggregate::<P>(request);
        match &outcome {
            Ok(_) => log(format_args!("{summary}: proven")),
            Err((rejection, message)) => log(format_args!("{summary}: refused ({rejection:?}): {message}")),
        }
        // The connection may have closed meanwhile.
        let _ = reply.send(outcome);
    }
}

/// Whether the client closed its connection, so no longer waits for the request it sent: one that timed out, say. A
/// client that only shut down its writing half reads the same, as the protocol says. Nothing else reads the stream
/// meanwhile, its connection thread waiting on the outcome.
fn hung_up(client: &UnixStream) -> bool {
    let mut byte = 0u8;
    // SAFETY: a one-byte buffer of ours, on an open socket; peeking leaves the stream as it is.
    let n = unsafe {
        libc::recv(
            client.as_raw_fd(),
            (&raw mut byte).cast(),
            1,
            libc::MSG_PEEK | libc::MSG_DONTWAIT,
        )
    };
    match n {
        0 => true,
        1.. => false,
        _ => !matches!(
            io::Error::last_os_error().kind(),
            io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
        ),
    }
}

fn aggregate<P: Prover>(request: Request) -> Outcome {
    let children = request
        .children
        .into_iter()
        .enumerate()
        .map(|(i, (claims, proof))| match AggregateProof::from_bytes(&proof) {
            Some(proof) => Ok((claims, proof)),
            None => Err((Rejection::InvalidChild, format!("child {i}'s proof does not decode"))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let blobs = match request.blobs.len() {
        0 => None,
        _ => Some(lean_da::BlobMatrix::build(&request.blobs).map_err(|e| (Rejection::InvalidInput, e.to_string()))?),
    };
    drop(request.blobs);
    let output = request.output.as_ref().map_or(OutputClaims::All, OutputClaims::Only);
    aggregation::aggregate::<P>(
        &children,
        request.raw_lean_xmss,
        request.raw_lean_sphincs,
        blobs.as_ref(),
        output,
        request.log_inv_rate,
    )
    .map(|(claims, proof, _)| (claims, proof.to_bytes()))
    .map_err(|e| match e {
        AggregateError::InvalidInput(reason) => (Rejection::InvalidInput, reason.into()),
        AggregateError::InvalidSignature => (Rejection::InvalidSignature, e.to_string()),
        AggregateError::InvalidChild => (Rejection::InvalidChild, e.to_string()),
        AggregateError::ProvingFailed => (Rejection::ProvingFailed, e.to_string()),
    })
}

fn accept(listener: &UnixListener, jobs: &Sender<Job>, hello: Arc<[u8]>) {
    let open = Arc::new(Mutex::new(0));
    loop {
        match listener.accept() {
            Ok((stream, _)) => {
                let Some(slot) = Slot::take(&open) else {
                    log(format_args!("a connection refused: {MAX_CONNECTIONS} open"));
                    continue;
                };
                let (jobs, hello) = (jobs.clone(), hello.clone());
                let spawned = thread::Builder::new().name("connection".into()).spawn(move || {
                    let _slot = slot;
                    connection(stream, &jobs, &hello);
                });
                if let Err(e) = spawned {
                    log(format_args!("a connection dropped: {e}"));
                }
            }
            Err(e) => {
                // Out of file descriptors, say: wait for some to close rather than spin.
                log(format_args!("accept: {e}"));
                thread::sleep(Duration::from_millis(100));
            }
        }
    }
}

/// One of the [`MAX_CONNECTIONS`], freed when dropped, even by a connection's thread that panics.
struct Slot(Arc<Mutex<usize>>);

impl Slot {
    /// Takes a free slot, if any.
    fn take(open: &Arc<Mutex<usize>>) -> Option<Self> {
        let mut count = open.lock().unwrap();
        (*count < MAX_CONNECTIONS).then(|| {
            *count += 1;
            Self(open.clone())
        })
    }
}

impl Drop for Slot {
    fn drop(&mut self) {
        *self.0.lock().unwrap() -= 1;
    }
}

/// Serves one connection: its hello, then each request in turn, until the client closes it.
fn connection(mut stream: UnixStream, jobs: &Sender<Job>, hello: &[u8]) {
    if stream.write_all(hello).is_err() {
        return;
    }
    loop {
        let body = match wire::read_frame(&mut stream, MAX_REQUEST) {
            Ok(Incoming::Body(body)) => body,
            // The body is left unread, so the stream is lost: say why, and close.
            Ok(Incoming::TooLarge(len)) => {
                let message = format!("a request of {len} bytes, the sidecar takes at most {MAX_REQUEST}");
                log(format_args!("a request refused (Malformed): {message}"));
                let _ = stream.write_all(&encode_response(&Err((Rejection::Malformed, message))));
                return;
            }
            Ok(Incoming::End) | Err(_) => return,
        };
        let response = match decode_request(&body) {
            Ok(Call::Aggregate(request)) => {
                drop(body);
                let Ok(client) = stream.try_clone() else { return };
                let (reply, outcome) = mpsc::channel();
                jobs.send((request, client, reply))
                    .expect("the prover outlives every connection");
                // No outcome: the prover dropped the request, its client having hung up.
                let Ok(outcome) = outcome.recv() else { return };
                encode_response(&outcome)
            }
            // Here rather than behind the proofs: it is fast, and on one thread.
            Ok(Call::Verify(claims, proof)) => {
                encode_verdict(AggregateProof::from_bytes(&proof).is_some_and(|proof| proof.verify(&claims)))
            }
            Err((rejection, message)) => {
                log(format_args!("a request refused ({rejection:?}): {message}"));
                encode_response(&Err((rejection, message)))
            }
        };
        if stream.write_all(&response).is_err() {
            return;
        }
    }
}

const XMSS_RECORD: usize = lean_xmss::PUB_KEY_SIZE + lean_xmss::MESSAGE_LEN + lean_xmss::SIG_SIZE;
const SPHINCS_RECORD: usize = lean_sphincs::PUB_KEY_SIZE + lean_sphincs::MESSAGE_LEN + lean_sphincs::SIG_SIZE;
const BLOB_BYTES: usize = size_of::<Blob>();

fn encode_hello(hello: &Hello) -> Vec<u8> {
    let mut f = Frame::new();
    f.raw(&wire::MAGIC);
    f.raw(&wire::VERSION.to_le_bytes());
    f.u64(hello.max_request);
    f.bytes(&hello.tag);
    f.bytes(hello.prover.as_bytes());
    f.finish()
}

/// A request, as the server decodes it.
enum Call {
    Aggregate(Request),
    /// Claims, and their proof's bytes.
    Verify(AggregateClaims, Vec<u8>),
}

/// An `aggregate` call, its children's proofs still bytes.
struct Request {
    children: Vec<Proven>,
    raw_lean_xmss: Vec<RawLeanXmss>,
    raw_lean_sphincs: Vec<RawLeanSphincs>,
    blobs: Vec<Blob>,
    /// `None` for [`OutputClaims::All`].
    output: Option<AggregateClaims>,
    log_inv_rate: usize,
}

fn decode_request(body: &[u8]) -> Result<Call, (Rejection, String)> {
    let malformed = |what: &str| (Rejection::Malformed, format!("malformed request: {what}"));
    let mut c = Cursor(body);
    let call = match c.u8() {
        Some(OP_AGGREGATE) => Call::Aggregate(decode_aggregate(&mut c, malformed)?),
        Some(OP_VERIFY) => {
            let claims = c.claims().ok_or_else(|| malformed("claims"))?;
            let proof = c.bytes().ok_or_else(|| malformed("proof"))?;
            Call::Verify(claims, proof.to_vec())
        }
        Some(op) => return Err((Rejection::Malformed, format!("unknown operation {op}"))),
        None => return Err(malformed("empty")),
    };
    if !c.is_empty() {
        return Err(malformed("trailing bytes"));
    }
    Ok(call)
}

/// A count of records of `size` bytes each, all of which must follow: a forged count allocates nothing.
fn count(c: &mut Cursor, size: usize) -> Option<usize> {
    let n = usize::try_from(c.u64()?).ok()?;
    (n.checked_mul(size)? <= c.0.len()).then_some(n)
}

fn decode_aggregate(
    c: &mut Cursor,
    malformed: impl Fn(&str) -> (Rejection, String),
) -> Result<Request, (Rejection, String)> {
    let log_inv_rate = c.u8().ok_or_else(|| malformed("no rate"))?.into();

    // Each child is at least its two lengths.
    let n = count(c, 16).ok_or_else(|| malformed("children"))?;
    // `aggregate`'s bound, checked before decoding: a decoded child takes more memory than its bytes.
    if n > aggregation::MAX_RECURSIONS {
        return Err((Rejection::InvalidInput, "more than MAX_RECURSIONS children".into()));
    }
    let mut children = Vec::with_capacity(n);
    for i in 0..n {
        let claims = c.claims().ok_or_else(|| malformed(&format!("child {i}'s claims")))?;
        let proof = c.bytes().ok_or_else(|| malformed(&format!("child {i}'s proof")))?;
        children.push((claims, proof.to_vec()));
    }

    let n = count(c, XMSS_RECORD).ok_or_else(|| malformed("leanXMSS signatures"))?;
    let raw_lean_xmss = (0..n)
        .map(|_| {
            (
                LeanXmssPublicKey::from_bytes(c.array().unwrap()),
                *c.array().unwrap(),
                LeanXmssSignature::from_bytes(c.array().unwrap()),
            )
        })
        .collect();
    let n = count(c, SPHINCS_RECORD).ok_or_else(|| malformed("leanSPHINCS signatures"))?;
    let raw_lean_sphincs = (0..n)
        .map(|_| {
            (
                LeanSphincsPublicKey::from_bytes(c.array().unwrap()),
                *c.array().unwrap(),
                LeanSphincsSignature::from_bytes(c.array().unwrap()),
            )
        })
        .collect();

    let n = count(c, BLOB_BYTES).ok_or_else(|| malformed("blobs"))?;
    // `BlobMatrix::build`'s bound, checked before allocating and queueing blobs that will be refused.
    if n > lean_da::DA_MAX_ROWS {
        return Err((
            Rejection::InvalidInput,
            format!("{n} blobs: expected 1 to {}", lean_da::DA_MAX_ROWS),
        ));
    }
    let blobs = (0..n)
        .map(|_| {
            let symbols = c.take(BLOB_BYTES).unwrap().as_chunks::<16>().0;
            std::array::from_fn(|i| u128::from_le_bytes(symbols[i]))
        })
        .collect();

    let output = match c.u8() {
        Some(0) => None,
        Some(1) => Some(c.claims().ok_or_else(|| malformed("output claims"))?),
        _ => return Err(malformed("output")),
    };
    Ok(Request {
        children,
        raw_lean_xmss,
        raw_lean_sphincs,
        blobs,
        output,
        log_inv_rate,
    })
}

fn encode_response(result: &Outcome) -> Vec<u8> {
    let mut f = Frame::new();
    match result {
        Ok((claims, proof)) => {
            f.u8(OK);
            f.bytes(&claims.to_bytes());
            f.bytes(proof);
        }
        Err((rejection, message)) => {
            f.u8(*rejection as u8);
            f.bytes(message.as_bytes());
        }
    }
    f.finish()
}

/// A verify request's response: whether the proof is valid.
fn encode_verdict(valid: bool) -> Vec<u8> {
    let mut f = Frame::new();
    f.u8(OK);
    f.u8(valid.into());
    f.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::{decode_hello, decode_response, encode_request, hello_version};

    fn body(frame: Vec<u8>) -> Vec<u8> {
        assert_eq!(
            u64::from_le_bytes(frame[..8].try_into().unwrap()),
            frame.len() as u64 - 8
        );
        frame[8..].to_vec()
    }

    #[test]
    fn hello_round_trips() {
        let hello = Hello {
            max_request: 1 << 30,
            tag: verifier::TAG.to_vec(),
            prover: "stable".into(),
        };
        let bytes = body(encode_hello(&hello));
        assert_eq!(hello_version(&bytes), Some(wire::VERSION));
        assert_eq!(decode_hello(&bytes), Some(hello));
        assert_eq!(decode_hello(&bytes[..bytes.len() - 1]), None);
        assert_eq!(decode_hello(&[&bytes[..], &[0]].concat()), None);
        let mut other = bytes.clone();
        other[0] ^= 1;
        assert_eq!(hello_version(&other), None);
    }

    /// A request decodes to what was encoded; every truncation, and a trailing byte, is refused, never a panic.
    #[test]
    fn requests_round_trip_and_truncations_are_refused() {
        let xmss = (
            LeanXmssPublicKey::from_bytes(&[1; 32]),
            [2; 32],
            LeanXmssSignature::from_bytes(&std::array::from_fn(|i| i as u8)),
        );
        let sphincs = (
            LeanSphincsPublicKey::from_bytes(&[3; 32]),
            [4; 32],
            LeanSphincsSignature::from_bytes(&std::array::from_fn(|i| (i * 7) as u8)),
        );
        let blob: Blob = std::array::from_fn(|i| ((i as u128) << 100) | i as u128);
        let only = AggregateClaims {
            lean_xmss: vec![(xmss.0, xmss.1)],
            lean_sphincs: vec![(sphincs.0, sphincs.1)],
            da_commitment: Some([5; 32]),
        };
        let child = (only.clone(), vec![6, 7, 8]);
        let frame = encode_request(
            std::slice::from_ref(&child),
            std::slice::from_ref(&xmss),
            std::slice::from_ref(&sphincs),
            &[blob],
            OutputClaims::Only(&only),
            3,
        );
        let bytes = body(frame);
        let Ok(Call::Aggregate(request)) = decode_request(&bytes) else {
            panic!("not an aggregate request")
        };
        assert_eq!(request.children, vec![child]);
        assert_eq!(request.raw_lean_xmss, vec![xmss]);
        assert_eq!(request.raw_lean_sphincs, vec![sphincs]);
        assert_eq!(request.blobs, vec![blob]);
        assert_eq!(request.output, Some(only));
        assert_eq!(request.log_inv_rate, 3);
        for len in 0..bytes.len() {
            assert!(
                decode_request(&bytes[..len]).is_err(),
                "a prefix of {len} bytes decoded"
            );
        }
        assert!(decode_request(&[&bytes[..], &[0]].concat()).is_err());
        // A count no body could hold.
        let mut huge = vec![OP_AGGREGATE, 1];
        huge.extend(u64::MAX.to_le_bytes());
        assert!(decode_request(&huge).is_err());
        let many = vec![(AggregateClaims::default(), Vec::new()); aggregation::MAX_RECURSIONS + 1];
        let frame = encode_request(&many, &[], &[], &[], OutputClaims::All, 1);
        assert!(matches!(
            decode_request(&body(frame)),
            Err((Rejection::InvalidInput, _))
        ));
        let many_blobs = vec![[0; lean_da::BLOB_SYMBOLS]; lean_da::DA_MAX_ROWS + 1];
        let frame = encode_request(&[], &[], &[], &many_blobs, OutputClaims::All, 1);
        assert!(matches!(
            decode_request(&body(frame)),
            Err((Rejection::InvalidInput, _))
        ));
    }

    #[test]
    fn responses_round_trip() {
        let proven = (AggregateClaims::default(), vec![1, 2, 3]);
        assert_eq!(
            decode_response(&body(encode_response(&Ok(proven.clone())))),
            Some(Ok(proven))
        );
        let rejection = (Rejection::InvalidInput, "log_inv_rate out of range".to_string());
        let bytes = body(encode_response(&Err(rejection.clone())));
        assert_eq!(decode_response(&bytes).unwrap().unwrap_err(), rejection);
        assert!(decode_response(&[42, 0, 0, 0, 0, 0, 0, 0, 0]).is_none());
    }
}
