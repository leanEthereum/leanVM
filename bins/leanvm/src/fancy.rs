//! `recursion --fancy`: the benchmark drawn live on the terminal. The subnets' attestations are
//! aggregated into leaf proofs, all subnets side by side, and the leaf proofs then flow into the
//! root, which recurses them into one.
//!
//! The leaves are proven one after another, but drawn as if in parallel ([`fill`]): the leaves'
//! process reports each leaf it starts and finishes ([`PROTOCOL`]), and the subnets complete
//! together when the last one is proven. The recursion step reports each pass. Off a terminal it
//! prints the final frame alone, without colors.

use std::io::{IsTerminal, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// Prefix of the lines the leaves' process reports its progress with, on its stdout.
pub const PROTOCOL: &str = "\u{1e}leanvm-leaf";

const FRAME: Duration = Duration::from_millis(50);
/// How long the subnets' counts take to run up to full once the last leaf is proven.
const RUSH: Duration = Duration::from_millis(400);
const SPINNER: [char; 10] = ['⠋', '⠙', '⠹', '⠸', '⠼', '⠴', '⠦', '⠧', '⠇', '⠏'];

type Rgb = (u8, u8, u8);
/// A box's inner width and height in cells, and the dots it shows.
type Layout = (usize, usize, usize);
const DIM: Rgb = (68, 76, 98);
const FAINT: Rgb = (110, 118, 140);
const TEXT: Rgb = (200, 206, 220);
const AMBER: Rgb = (255, 150, 60);
const GOLD: Rgb = (255, 210, 100);
const WHITE: Rgb = (255, 248, 230);
const TEAL: Rgb = (70, 220, 190);
const TEAL_DIM: Rgb = (40, 120, 110);
const VIOLET: Rgb = (150, 110, 255);
const PINK: Rgb = (255, 100, 200);

#[derive(Clone, Copy)]
enum Root {
    Waiting,
    Pass { index: usize, started: Instant },
    Between,
    Verifying,
    Done { at: Instant, kib: f64, secs: f64 },
}

#[derive(Clone, Copy, Default)]
struct Leaf {
    started: Option<Instant>,
    done: Option<(Instant, f64)>,
}

struct State {
    per_leaf: usize,
    noun: &'static str,
    passes: usize,
    status: String,
    leaves: Vec<Leaf>,
    root: Root,
    began: Instant,
    /// The child's output that is not progress, printed under the final frame.
    postscript: String,
    /// Each subnet's dots in the order they aggregate, for the layout they were placed in.
    dots: Option<(Layout, Vec<Vec<usize>>)>,
}

/// The animation, or nothing when `--fancy` is off: every method is then a no-op.
pub struct Show(Option<Inner>);

struct Inner {
    state: Arc<Mutex<State>>,
    stop: Arc<AtomicBool>,
    painter: Option<JoinHandle<usize>>,
    tty: bool,
    closed: bool,
}

impl Show {
    /// `n` subnets of `per_leaf` `noun` each, and a recursion step of a warmup plus `repeat` passes.
    pub fn new(enabled: bool, n: usize, per_leaf: usize, noun: &'static str, repeat: usize) -> Self {
        if !enabled {
            return Self(None);
        }
        bench::quiet_progress();
        let state = Arc::new(Mutex::new(State {
            per_leaf: per_leaf.max(1),
            noun,
            passes: repeat + 1,
            status: String::new(),
            leaves: vec![Leaf::default(); n],
            root: Root::Waiting,
            began: Instant::now(),
            postscript: String::new(),
            dots: None,
        }));
        let stop = Arc::new(AtomicBool::new(false));
        let tty = std::io::stdout().is_terminal();
        let painter = tty.then(|| {
            on_interrupt_restore_cursor();
            // A panic's message goes under the frame: stop drawing before it is printed, or the
            // next frame paints over it.
            let (previous, halt) = (std::panic::take_hook(), stop.clone());
            std::panic::set_hook(Box::new(move |info| {
                if !halt.swap(true, Ordering::Relaxed) {
                    std::thread::sleep(2 * FRAME);
                    eprint!("\x1b[?25h");
                }
                previous(info);
            }));
            print!("\x1b[?25l");
            let (state, stop) = (state.clone(), stop.clone());
            std::thread::spawn(move || {
                let mut height = 0;
                while !stop.load(Ordering::Relaxed) {
                    let frame = render(&mut lock(&state), Instant::now(), terminal_width(), true);
                    height = paint(&frame, height, true);
                    std::thread::sleep(FRAME);
                }
                height
            })
        });
        Self(Some(Inner {
            state,
            stop,
            painter,
            tty,
            closed: false,
        }))
    }

    pub fn is_on(&self) -> bool {
        self.0.is_some()
    }

    fn with(&self, f: impl FnOnce(&mut State)) {
        if let Some(inner) = &self.0 {
            f(&mut inner.lock());
        }
    }

    /// What the run is doing before the first subnet starts.
    pub fn status(&self, status: &str) {
        self.with(|s| s.status = status.into());
    }

    /// Follow the leaves' process through its stdout until it closes. Its lines that are not
    /// progress are kept for under the final frame, but for the signers cache's transient status.
    pub fn follow(&self, mut out: impl std::io::Read) {
        let (mut pending, mut chunk) = (Vec::new(), [0u8; 4096]);
        while let Ok(read @ 1..) = out.read(&mut chunk) {
            pending.extend_from_slice(&chunk[..read]);
            // The signers cache redraws its status with `\r`, so a line ends at either.
            while let Some(end) = pending.iter().position(|&b| b == b'\n' || b == b'\r') {
                self.feed(&String::from_utf8_lossy(&pending[..end]));
                pending.drain(..=end);
            }
        }
        self.feed(&String::from_utf8_lossy(&pending));
    }

    fn feed(&self, part: &str) {
        let part = part.trim();
        if part.is_empty() {
            return;
        }
        self.with(|s| {
            let now = Instant::now();
            let mut words = part.strip_prefix(PROTOCOL).map(str::split_whitespace);
            match words
                .as_mut()
                .map(|w| (w.next(), w.next().and_then(|k| k.parse::<usize>().ok())))
            {
                Some((Some("start"), Some(k))) if k < s.leaves.len() => s.leaves[k].started = Some(now),
                Some((Some("done"), Some(k))) if k < s.leaves.len() => {
                    let began = s.leaves[k].started.unwrap_or(now);
                    s.leaves[k].done = Some((now, (now - began).as_secs_f64()));
                }
                Some(_) => {}
                None if part.starts_with("generating") => s.status = part.into(),
                None => {
                    s.postscript.push_str(part);
                    s.postscript.push('\n');
                }
            }
        });
    }

    /// Text to print under the final frame.
    pub fn postscript(&self, text: &str) {
        self.with(|s| s.postscript.push_str(text));
    }

    pub fn pass_started(&self, index: usize) {
        self.with(|s| {
            s.root = Root::Pass {
                index,
                started: Instant::now(),
            }
        });
    }

    pub fn pass_ended(&self) {
        self.with(|s| s.root = Root::Between);
    }

    pub fn verifying(&self) {
        self.with(|s| s.root = Root::Verifying);
    }

    /// Celebrate the root proof for a moment, then leave its final frame on the terminal.
    pub fn finish(&mut self, kib: f64, secs: f64) {
        let Some(inner) = &mut self.0 else { return };
        inner.lock().root = Root::Done {
            at: Instant::now(),
            kib,
            secs,
        };
        if inner.tty {
            std::thread::sleep(Duration::from_millis(1500));
        }
        inner.close();
    }

    /// Stop drawing, leaving the frame as it is and the child's output under it, before an error
    /// is reported.
    pub fn close(&mut self) {
        if let Some(inner) = &mut self.0 {
            inner.close();
        }
    }
}

impl Inner {
    fn lock(&self) -> MutexGuard<'_, State> {
        lock(&self.state)
    }

    fn close(&mut self) {
        if std::mem::replace(&mut self.closed, true) {
            return;
        }
        self.stop.store(true, Ordering::Relaxed);
        let height = self.painter.take().map_or(0, |p| p.join().unwrap_or(0));
        let mut state = self.lock();
        // Unwinding, the panic's message is under the frame: leave both as they are.
        if !std::thread::panicking() {
            let now = match state.root {
                // Long after any sparkle has faded.
                Root::Done { at, .. } => at + Duration::from_secs(60),
                _ => Instant::now(),
            };
            let frame = render(&mut state, now, terminal_width(), self.tty);
            paint(&frame, height, self.tty);
        }
        if self.tty {
            print!("\x1b[?25h");
        }
        println!();
        print!("{}", state.postscript);
        let _ = std::io::stdout().flush();
    }
}

impl Drop for Inner {
    fn drop(&mut self) {
        self.close();
    }
}

fn lock(state: &Mutex<State>) -> MutexGuard<'_, State> {
    state.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Redraw `frame` over the `height` lines drawn last, returning its own height. Off a terminal,
/// just print it.
fn paint(frame: &[String], height: usize, tty: bool) -> usize {
    let mut out = String::new();
    if height > 0 {
        out.push_str(&format!("\x1b[{height}A\r"));
    }
    for line in frame {
        out.push_str(line);
        out.push_str(if tty { "\x1b[K\n" } else { "\n" });
    }
    if tty {
        out.push_str("\x1b[J");
    }
    let mut stdout = std::io::stdout().lock();
    let _ = stdout.write_all(out.as_bytes());
    let _ = stdout.flush();
    frame.len()
}

fn terminal_width() -> usize {
    // SAFETY: `TIOCGWINSZ` only writes the `winsize` it is handed.
    let mut size: libc::winsize = unsafe { std::mem::zeroed() };
    let ok = unsafe { libc::ioctl(libc::STDOUT_FILENO, libc::TIOCGWINSZ, &raw mut size) } == 0;
    if ok && size.ws_col > 0 {
        usize::from(size.ws_col)
    } else {
        100
    }
}

/// Ctrl-C would otherwise leave the terminal without a cursor.
fn on_interrupt_restore_cursor() {
    extern "C" fn restore(_: libc::c_int) {
        let reset = b"\x1b[0m\x1b[?25h\n";
        // SAFETY: `write` and `_exit` are async-signal-safe.
        unsafe {
            libc::write(libc::STDOUT_FILENO, reset.as_ptr().cast(), reset.len());
            libc::_exit(130);
        }
    }
    // SAFETY: the handler only calls async-signal-safe functions.
    unsafe {
        libc::signal(
            libc::SIGINT,
            restore as extern "C" fn(libc::c_int) as libc::sighandler_t,
        )
    };
}

/// A grid of colored characters, with a braille layer of 2×4 dots per cell beneath them.
struct Canvas {
    w: usize,
    cells: Vec<Vec<(char, u8, Rgb)>>,
}

impl Canvas {
    fn new(w: usize, h: usize) -> Self {
        Self {
            w,
            cells: vec![vec![(' ', 0, TEXT); w]; h],
        }
    }

    fn put(&mut self, x: usize, y: usize, ch: char, color: Rgb) {
        if let Some(cell) = self.cells.get_mut(y).and_then(|row| row.get_mut(x)) {
            *cell = (ch, 0, color);
        }
    }

    fn text(&mut self, x: usize, y: usize, text: &str, color: Rgb) {
        for (k, ch) in text.chars().enumerate() {
            self.put(x + k, y, ch, color);
        }
    }

    /// `text` centered on `[x, x + w)`, cut to fit.
    fn centered(&mut self, x: usize, w: usize, y: usize, text: &str, color: Rgb) {
        let text: String = text.chars().take(w).collect();
        self.text(x + (w - text.chars().count()) / 2, y, &text, color);
    }

    /// The braille dot at pixel `(px, py)`, and the color of its cell.
    fn dot(&mut self, px: usize, py: usize, color: Option<Rgb>) {
        const BITS: [[u8; 4]; 2] = [[0x01, 0x02, 0x04, 0x40], [0x08, 0x10, 0x20, 0x80]];
        if let Some(cell) = self.cells.get_mut(py / 4).and_then(|row| row.get_mut(px / 2)) {
            cell.1 |= BITS[px % 2][py % 4];
            if let Some(color) = color {
                cell.2 = color;
            }
        }
    }

    fn tint(&mut self, x: usize, y: usize, color: Rgb) {
        if let Some(cell) = self.cells.get_mut(y).and_then(|row| row.get_mut(x)) {
            cell.2 = color;
        }
    }

    /// A rounded box of outer size `w × h` at `(x, y)`.
    fn frame(&mut self, x: usize, y: usize, w: usize, h: usize, color: Rgb) {
        for k in 1..w - 1 {
            self.put(x + k, y, '─', color);
            self.put(x + k, y + h - 1, '─', color);
        }
        for k in 1..h - 1 {
            self.put(x, y + k, '│', color);
            self.put(x + w - 1, y + k, '│', color);
        }
        self.put(x, y, '╭', color);
        self.put(x + w - 1, y, '╮', color);
        self.put(x, y + h - 1, '╰', color);
        self.put(x + w - 1, y + h - 1, '╯', color);
    }

    fn lines(&self, color: bool) -> Vec<String> {
        self.cells
            .iter()
            .map(|row| {
                let mut line = String::new();
                let mut last = None;
                for &(ch, bits, rgb) in &row[..self.w] {
                    let ch = if ch == ' ' && bits != 0 {
                        char::from_u32(0x2800 + u32::from(bits)).unwrap()
                    } else {
                        ch
                    };
                    if color && ch != ' ' && last != Some(rgb) {
                        line.push_str(&format!("\x1b[38;2;{};{};{}m", rgb.0, rgb.1, rgb.2));
                        last = Some(rgb);
                    }
                    line.push(ch);
                }
                let line = line.trim_end().to_string();
                if color { line + "\x1b[0m" } else { line }
            })
            .collect()
    }
}

fn mix(a: Rgb, b: Rgb, t: f64) -> Rgb {
    let t = t.clamp(0.0, 1.0);
    let m = |a: u8, b: u8| (f64::from(a) + (f64::from(b) - f64::from(a)) * t).round() as u8;
    (m(a.0, b.0), m(a.1, b.1), m(a.2, b.2))
}

fn hash(a: u64, b: u64) -> u64 {
    let mut z = a.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ b.wrapping_add(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// `1234` as `1.2k`.
fn short(n: usize) -> String {
    match n {
        0..1_000 => n.to_string(),
        1_000..1_000_000 => format!("{:.1}k", n as f64 / 1e3).replace(".0k", "k"),
        _ => format!("{:.1}M", n as f64 / 1e6).replace(".0M", "M"),
    }
}

fn spinner(t: f64) -> char {
    SPINNER[(t * 12.0) as usize % SPINNER.len()]
}

/// How full every subnet is drawn, once the first leaf has started: an easing guess until it is
/// proven, then a straight run to the time `n` leaves of its proving time take. Short of full,
/// since the subnets complete only when the last leaf is proven.
fn fill(s: &State, now: Instant) -> Option<f64> {
    let first = s.leaves[0];
    let elapsed = now.saturating_duration_since(first.started?).as_secs_f64();
    let guess = |elapsed: f64| 0.3 * (1.0 - (-elapsed / 4.0).exp());
    let fill = match first.done {
        None => guess(elapsed),
        Some((_, secs)) => {
            let (from, rest) = (guess(secs), (s.leaves.len() - 1) as f64 * secs);
            from + (1.0 - from) * ((elapsed - secs) / rest.max(1e-9)).clamp(0.0, 1.0)
        }
    };
    Some(fill.min(0.97))
}

/// The curve from a subnet down to the root: `(x, y)` at `f` in `[0, 1]`, easing sideways.
fn curve(from: (f64, f64), to: (f64, f64), f: f64) -> (usize, usize) {
    let ease = f * f * (3.0 - 2.0 * f);
    (
        (from.0 + (to.0 - from.0) * ease).round() as usize,
        (from.1 + (to.1 - from.1) * f).round() as usize,
    )
}

fn render(s: &mut State, now: Instant, width: usize, color: bool) -> Vec<String> {
    let n = s.leaves.len();
    let t = now.saturating_duration_since(s.began).as_secs_f64();
    let w = width.saturating_sub(1).clamp(40, 120);

    // The subnets side by side, as wide as the terminal allows, right of a leaf's mean time.
    let reserved = 6;
    let room = w - reserved;
    let gap = if n * 6 + 2 * (n - 1) + 2 <= room { 2 } else { 1 };
    let bw = ((room - 2 - gap * (n - 1)) / n).clamp(3, 22);
    let left = reserved + room.saturating_sub(n * bw + gap * (n - 1)) / 2;
    // A dot for every `per_dot` attestations, filling about half the box.
    let (iw, ih) = (bw - 2, (2 * s.per_leaf).div_ceil((bw - 2) * 8).clamp(2, 5));
    let slots = iw * 2 * ih * 4;
    let per_dot = s.per_leaf.div_ceil(slots / 2);
    let shown = s.per_leaf.div_ceil(per_dot);

    let (name_y, box_y) = (3, 4);
    let label_y = box_y + ih + 2;
    let fan_y = label_y + 1;
    let fan_h = 5;
    let root_y = fan_y + fan_h;
    let mut c = Canvas::new(w, root_y + 4);

    // The attestations, scattered over each box and aggregated from its far corners in.
    if s.dots.as_ref().is_none_or(|(layout, _)| *layout != (iw, ih, shown)) {
        let order = |i: usize| {
            let (ox, oy) = (iw as f64, ih as f64 * 4.0);
            let dist = |d: usize| {
                let (dx, dy) = ((d % (iw * 2)) as f64 - ox, (d / (iw * 2)) as f64 - oy);
                -(dx * dx + 4.0 * dy * dy) - (hash(d as u64, 7) % 9) as f64
            };
            let mut dots: Vec<usize> = (0..slots).collect();
            dots.sort_by_key(|&d| hash(i as u64, d as u64));
            dots.truncate(shown);
            dots.sort_by(|&a, &b| dist(a).total_cmp(&dist(b)));
            dots
        };
        s.dots = Some(((iw, ih, shown), (0..n).map(order).collect()));
    }
    let s = &*s;

    let shared = fill(s, now);
    // When the last leaf is proven, every subnet's count runs up to full, and then they are done.
    let last_done = s
        .leaves
        .iter()
        .map(|l| l.done.map(|d| d.0))
        .collect::<Option<Vec<_>>>()
        .and_then(|done| done.into_iter().max());
    let finished = last_done.map(|at| at + RUSH).filter(|&at| at <= now);
    let active = shared.is_some() && finished.is_none();
    let status = match (s.root, active) {
        (Root::Done { .. }, _) => format!(
            "{} {} in {} subnets, proven by one proof",
            short(n * s.per_leaf),
            s.noun,
            n
        ),
        (Root::Verifying, _) => "verifying the root proof".into(),
        (Root::Pass { .. } | Root::Between, _) => format!("recursing {n} subnet proofs into one"),
        (Root::Waiting, true) => format!("aggregating {n} subnets, {} {} each", short(s.per_leaf), s.noun),
        (Root::Waiting, false) if finished.is_some() => format!("{n} subnet proofs ready for the recursion"),
        (Root::Waiting, false) => s.status.clone(),
    };
    c.text(1, 0, "◆ leanVM", GOLD);
    c.text(
        10,
        0,
        &format!("recursion {n}→1 · {n} subnets × {} {}", short(s.per_leaf), s.noun),
        TEXT,
    );
    c.text(3, 1, &status, FAINT);

    let rw = (w - 4).min(38);
    let rx = (w - rw) / 2;
    for i in 0..n {
        let x = left + i * (bw + gap);
        let since = |at: Instant| now.saturating_duration_since(at).as_secs_f64();
        // Each subnet a little ahead of or behind the shared fill, never at either end.
        let own_at = |at: Instant| {
            fill(s, at).map(|f| (f + 0.08 * (i as f64 * 2.4 + 1.0).sin() * f * (1.0 - f)).clamp(0.0, 0.97))
        };
        let own = match last_done {
            Some(at) => {
                let from = own_at(at).unwrap_or(0.0);
                Some(from + (1.0 - from) * (since(at) / RUSH.as_secs_f64()).min(1.0))
            }
            None => own_at(now),
        };
        let (lit, border, name_color) = match (finished, own) {
            (Some(_), _) => (shown, TEAL, TEAL),
            (None, Some(own)) => {
                let pulse = 0.5 + 0.5 * (t * 5.0 + i as f64).sin();
                ((own * shown as f64) as usize, mix(AMBER, GOLD, pulse), GOLD)
            }
            (None, None) => (0, DIM, FAINT),
        };
        let name = if bw >= 10 { format!("subnet {i}") } else { i.to_string() };
        c.centered(x, bw, name_y, &name, name_color);
        c.frame(x, box_y, bw, ih + 2, border);

        let dots = &s.dots.as_ref().expect("placed above").1[i];
        let front = (shown / 10).max(1);
        let mut cells = vec![(0usize, 0usize, false); iw * ih];
        for (rank, &d) in dots.iter().enumerate() {
            let (px, py) = (d % (iw * 2), d / (iw * 2));
            c.dot((x + 1) * 2 + px, (box_y + 1) * 4 + py, None);
            let cell = &mut cells[(py / 4) * iw + px / 2];
            cell.0 += 1;
            if rank < lit {
                cell.1 += 1;
                cell.2 |= rank + front >= lit && finished.is_none();
            }
        }
        for (k, &(total, lit, front)) in cells.iter().enumerate() {
            let (cx, cy) = (x + 1 + k % iw, box_y + 1 + k / iw);
            let rgb = match finished {
                Some(at) => mix(WHITE, TEAL, since(at) / 0.8),
                None if front => mix(GOLD, WHITE, 0.5 + 0.5 * (t * 9.0 + k as f64).sin()),
                None if lit > 0 => mix(DIM, AMBER, 0.4 + 0.6 * lit as f64 / total as f64),
                None if hash(hash(i as u64, k as u64), (t * 4.0) as u64).is_multiple_of(31) => FAINT,
                None => DIM,
            };
            c.tint(cx, cy, rgb);
        }

        // The longest label that fits the box, never one cut short.
        let total = short(s.per_leaf);
        let (labels, color) = match own {
            Some(own) => {
                let aggregated = short((own * s.per_leaf as f64).round() as usize);
                let labels = match finished {
                    Some(_) => vec![format!("{aggregated}/{total}"), aggregated],
                    None => {
                        let spin = spinner(t + i as f64 * 0.05);
                        vec![
                            format!("{spin} {aggregated}/{total}"),
                            format!("{spin} {aggregated}"),
                            aggregated,
                        ]
                    }
                };
                (labels, if finished.is_some() { TEAL } else { GOLD })
            }
            None => (vec![format!("{total} {}", s.noun), total], DIM),
        };
        let label = labels.into_iter().find(|l| l.chars().count() <= bw).unwrap_or_default();
        c.centered(x, bw, label_y, &label, color);

        // Its proof's way down to the root: dotted until the proof exists, then lit, with packets
        // flowing along it while the root recurses.
        let from = ((x * 2 + bw) as f64 - 0.5, (fan_y * 4) as f64);
        let to = (
            (rx * 2 + 2) as f64 + (i as f64 + 0.5) / n as f64 * (rw * 2 - 4) as f64,
            (root_y * 4 - 1) as f64,
        );
        let steps = ((to.0 - from.0).abs() + (to.1 - from.1)) as usize * 2;
        let packets: Vec<f64> = match (finished, s.root) {
            (Some(_), Root::Pass { .. }) => (0..3)
                .map(|j| (t * 0.6 + j as f64 / 3.0 + i as f64 * 0.17).fract())
                .collect(),
            (Some(at), Root::Waiting) if since(at) < 1.0 => vec![since(at)],
            _ => Vec::new(),
        };
        let path = match s.root {
            Root::Done { .. } => mix(TEAL_DIM, GOLD, 0.35),
            _ if finished.is_some() => TEAL_DIM,
            _ => DIM,
        };
        for k in 0..=steps {
            let f = k as f64 / steps as f64;
            if finished.is_none() && k % 4 != 0 {
                continue;
            }
            let (px, py) = curve(from, to, f);
            c.dot(px, py, Some(path));
        }
        for k in 0..=steps {
            let f = k as f64 / steps as f64;
            if let Some(p) = packets.iter().find(|&&p| (f - p).abs() < 0.05) {
                let (px, py) = curve(from, to, f);
                c.dot(px, py, Some(mix(TEAL, WHITE, 1.0 - (f - p).abs() / 0.05)));
            }
        }
    }

    // A leaf's mean proving time.
    if finished.is_some() {
        let mean = s.leaves.iter().filter_map(|l| l.done.map(|d| d.1)).sum::<f64>() / n as f64;
        c.text(0, label_y, &format!("{mean:.1}s"), TEAL);
    }

    // The root.
    let (border, content, label) = match s.root {
        Root::Waiting => (
            mix(
                DIM,
                TEAL_DIM,
                if finished.is_some() { 1.0 } else { shared.unwrap_or(0.0) },
            ),
            (
                if finished.is_some() {
                    format!("root · {n} subnet proofs")
                } else {
                    format!("root · awaiting {n} subnet proofs")
                },
                FAINT,
            ),
            (String::new(), DIM),
        ),
        Root::Pass { index, started } => (
            mix(VIOLET, PINK, 0.5 + 0.5 * (t * 4.0).sin()),
            (format!("{} recursing {n}→1", spinner(t)), TEXT),
            (
                match index {
                    0 => format!(
                        "warm-up pass · {:.1}s",
                        now.saturating_duration_since(started).as_secs_f64()
                    ),
                    k => format!(
                        "measured pass {k}/{} · {:.1}s",
                        s.passes - 1,
                        now.saturating_duration_since(started).as_secs_f64()
                    ),
                },
                FAINT,
            ),
        ),
        Root::Between => (
            VIOLET,
            (format!("{} recursing {n}→1", spinner(t)), TEXT),
            ("cooling down".into(), DIM),
        ),
        Root::Verifying => (
            VIOLET,
            (format!("{} verifying", spinner(t)), TEXT),
            (String::new(), DIM),
        ),
        Root::Done { at, kib, secs } => {
            let age = now.saturating_duration_since(at).as_secs_f64();
            // A burst of sparkles around the root, fading.
            if age < 1.5 {
                for k in 0..24u64 {
                    let h = hash(k, (age * 6.0) as u64);
                    let (sx, sy) = (
                        rx.saturating_sub(3) + (h % (rw as u64 + 6)) as usize,
                        root_y - 1 + (h >> 20) as usize % 5,
                    );
                    if (sy < root_y || sy > root_y + 2 || sx < rx || sx >= rx + rw) && sy < root_y + 4 {
                        let ch = ['✦', '✧', '·', '*'][(h >> 40) as usize % 4];
                        c.put(sx, sy, ch, mix(WHITE, GOLD, age / 1.5));
                    }
                }
            }
            (
                mix(WHITE, GOLD, age / 0.6),
                (format!("◆ root proof · {kib:.1} KiB"), GOLD),
                (format!("✓ verified · recursed {n}→1 in {secs:.2}s"), TEAL),
            )
        }
    };
    c.frame(rx, root_y, rw, 3, border);
    c.centered(rx + 1, rw - 2, root_y + 1, &content.0, content.1);
    c.centered(0, w, root_y + 3, &label.0, label.1);
    c.lines(color)
}
