//! The server: a thread per connection reads and decodes requests and verifies proofs, and the thread that calls
//! [`serve`], the one that started the prover's pool, proves them one at a time.

use crate::Rejection;
use crate::wire::{self, Call, Hello, Incoming, Outcome, Request};
use aggregation::{AggregateError, OutputClaims};
use isa::Prover;
use std::convert::Infallible;
use std::fs::{File, TryLockError};
use std::io::{self, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::FileTypeExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;
use std::time::Duration;

/// How a sidecar serves.
#[derive(Clone, Debug)]
pub struct Config {
    /// The socket to listen on. A stale one, left by a sidecar that stopped, is replaced.
    pub socket: PathBuf,
    /// The longest request body taken, in bytes.
    pub max_request: u64,
    /// The prover's thread count (0: one per core).
    pub threads: usize,
}

/// A request, its client's connection, and where its outcome goes.
type Job = (Request, UnixStream, Sender<Outcome>);

/// Starts prover `P` and builds the aggregation program, then listens on `config.socket` and serves until the
/// process ends, proving on the calling thread. The socket appears once the sidecar is ready to prove. Returns only
/// if it cannot listen, which a second sidecar on the same socket learns before it starts anything.
///
/// Call it from the main thread: a panic while proving, a bug, then ends the process.
pub fn serve<P: Prover>(config: &Config) -> io::Result<Infallible> {
    std::os::unix::net::SocketAddr::from_pathname(&config.socket)?;
    let _lock = lock(&config.socket)?;
    remove_stale(&config.socket)?;
    if config.threads > 0 {
        P::set_num_threads(config.threads);
    }
    P::init();
    let program = aggregation::unified_guest().bytecode().fiat_shamir_iv();
    let listener = UnixListener::bind(&config.socket)?;
    let hello = wire::encode_hello(&Hello {
        max_request: config.max_request,
        tag: verifier::TAG.to_vec(),
        program,
        prover: P::NAME.into(),
    });
    let (jobs, queue) = mpsc::channel();
    let max_request = config.max_request;
    thread::Builder::new()
        .name("accept".into())
        .spawn(move || accept(&listener, &jobs, hello.into(), max_request))?;
    eprintln!(
        "leanvm-sidecar: serving {} with the {} prover",
        config.socket.display(),
        P::NAME
    );
    prove_forever::<P>(&queue)
}

/// Locks `<socket>.lock`, which the process holds until it ends, so that one sidecar at a time owns the socket.
fn lock(socket: &Path) -> io::Result<File> {
    let mut path = socket.as_os_str().to_owned();
    path.push(".lock");
    let file = File::options().create(true).truncate(false).write(true).open(&path)?;
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
            eprintln!("{summary}: dropped, its client hung up");
            continue;
        }
        let outcome = aggregate::<P>(request);
        match &outcome {
            Ok(_) => eprintln!("{summary}: proven"),
            Err((rejection, message)) => eprintln!("{summary}: refused ({rejection:?}): {message}"),
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
    let blobs = match request.blobs.len() {
        0 => None,
        _ => Some(lean_da::BlobMatrix::build(&request.blobs).map_err(|e| (Rejection::InvalidInput, e.to_string()))?),
    };
    drop(request.blobs);
    let output = request.output.as_ref().map_or(OutputClaims::All, OutputClaims::Only);
    aggregation::aggregate::<P>(
        &request.children,
        request.raw_lean_xmss,
        request.raw_lean_sphincs,
        blobs.as_ref(),
        output,
        request.log_inv_rate,
    )
    .map(|(claims, proof, _)| (claims, proof))
    .map_err(|e| match e {
        AggregateError::InvalidInput(reason) => (Rejection::InvalidInput, reason.into()),
        AggregateError::InvalidSignature => (Rejection::InvalidSignature, e.to_string()),
        AggregateError::InvalidChild => (Rejection::InvalidChild, e.to_string()),
        AggregateError::ProvingFailed => (Rejection::ProvingFailed, e.to_string()),
    })
}

fn accept(listener: &UnixListener, jobs: &Sender<Job>, hello: Arc<[u8]>, max_request: u64) {
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                let (jobs, hello) = (jobs.clone(), hello.clone());
                let spawned = thread::Builder::new()
                    .name("connection".into())
                    .spawn(move || connection(stream, &jobs, &hello, max_request));
                if let Err(e) = spawned {
                    eprintln!("leanvm-sidecar: a connection dropped: {e}");
                }
            }
            Err(e) => {
                // Out of file descriptors, say: wait for some to close rather than spin.
                eprintln!("leanvm-sidecar: accept: {e}");
                thread::sleep(Duration::from_millis(100));
            }
        }
    }
}

/// Serves one connection: its hello, then each request in turn, until the client closes it.
fn connection(mut stream: UnixStream, jobs: &Sender<Job>, hello: &[u8], max_request: u64) {
    if stream.write_all(hello).is_err() {
        return;
    }
    loop {
        let body = match wire::read_frame(&mut stream, max_request) {
            Ok(Incoming::Body(body)) => body,
            // The body is left unread, so the stream is lost: say why, and close.
            Ok(Incoming::TooLarge(len)) => {
                let message = format!("a request of {len} bytes, the sidecar takes at most {max_request}");
                eprintln!("a request refused (Malformed): {message}");
                let _ = stream.write_all(&wire::encode_response(&Err((Rejection::Malformed, message))));
                return;
            }
            Ok(Incoming::End) | Err(_) => return,
        };
        let response = match wire::decode_request(&body) {
            Ok(Call::Aggregate(request)) => {
                drop(body);
                let Ok(client) = stream.try_clone() else { return };
                let (reply, outcome) = mpsc::channel();
                jobs.send((request, client, reply))
                    .expect("the prover outlives every connection");
                // No outcome: the prover dropped the request, its client having hung up.
                let Ok(outcome) = outcome.recv() else { return };
                wire::encode_response(&outcome)
            }
            // Here rather than behind the proofs: it is fast, and on one thread.
            Ok(Call::Verify(claims, proof)) => wire::encode_verdict(proof.is_some_and(|proof| proof.verify(&claims))),
            Err((rejection, message)) => {
                eprintln!("a request refused ({rejection:?}): {message}");
                wire::encode_response(&Err((rejection, message)))
            }
        };
        if stream.write_all(&response).is_err() {
            return;
        }
    }
}
